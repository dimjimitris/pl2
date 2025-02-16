use crate::{bytecode, heap};
use std::{
    io::{self, Read as _, Write as _},
    ops, time,
};

pub const STACK_SIZE: usize = 1 << 14;
pub const HEAP_SIZE: usize = 1 << 20;

/// The VM struct
pub struct VM<H: heap::Heap> {
    pub bytecode: bytecode::Bytecode,
    stack: [heap::Word; STACK_SIZE], // fixed-size stack of words
    sp: usize,                       // stack pointer
    heap: H,
}

impl<H: heap::Heap> VM<H> {
    /// Create a new `VM` with the given bytecode
    pub fn new(bytecode: bytecode::Bytecode) -> Self {
        Self {
            bytecode,
            stack: [heap::Word::from_int(0); STACK_SIZE],
            sp: 0,
            heap: H::new(HEAP_SIZE),
        }
    }

    #[allow(dead_code)]
    #[cfg(debug_assertions)]
    fn print_state(&self, ip: usize) {
        print!("Stack: ");
        for i in 0..self.sp {
            print!("| {:?} ", self.stack[i]);
        }
        println!("|");

        let opcode: Option<bytecode::Opcode> =
            bytecode::Opcode::from_u8(self.bytecode.instructions[ip]);

        println!("IP {:#04x}: {:?}", ip, opcode);
    }

    #[allow(dead_code)]
    #[cfg(not(debug_assertions))]
    fn print_state(&self) {}

    pub fn run(&mut self) {
        use bytecode::Opcode;
        use heap::Word;

        let t0 = time::Instant::now();

        loop {
            // might be useful for debugging
            let _ip = self.bytecode.ip() as usize;

            let instr: [u8; 1] = self.bytecode.next_bytes();
            let opcode = Opcode::from_u8(instr[0])
                .unwrap_or_else(|| panic!("invalid opcode {:#04x}", instr[0]));

            match opcode {
                Opcode::Halt => break,

                Opcode::Jump => {
                    let instr: [u8; 2] = self.bytecode.next_bytes();
                    let addr = <u16>::from_le_bytes(instr);
                    self.bytecode.jump(addr);
                }

                Opcode::Jnz => {
                    let instr: [u8; 2] = self.bytecode.next_bytes();
                    let addr = <u16>::from_le_bytes(instr);

                    let num = self.pop_from_stack().to_int();
                    if num != 0 {
                        self.bytecode.jump(addr);
                    }
                }

                Opcode::Jumpi => {
                    let num = self.pop_from_stack().to_int();
                    let addr = <u16>::try_from(num).expect("jump address out of bounds");
                    self.bytecode.jump(addr);
                }

                Opcode::Dup => {
                    let instr: [u8; 1] = self.bytecode.next_bytes();
                    let depth = <u8>::from_le_bytes(instr) as usize;

                    let w = self.peek_in_stack(depth);
                    self.push_to_stack(w);
                }

                Opcode::Swap => {
                    let instr: [u8; 1] = self.bytecode.next_bytes();
                    let depth = <u8>::from_le_bytes(instr) as usize;

                    let w_top = self.peek_in_stack(0);
                    let w_bot = self.replace_in_stack(w_top, depth);
                    self.replace_in_stack(w_bot, 0);
                }

                Opcode::Drop => drop(self.pop_from_stack()),

                Opcode::Push4 => {
                    let instr: [u8; 4] = self.bytecode.next_bytes();
                    let num = <i32>::from_le_bytes(instr);
                    self.push_to_stack(Word::from_int(num));
                }

                Opcode::Push2 => {
                    let instr: [u8; 2] = self.bytecode.next_bytes();
                    let num = <i16>::from_le_bytes(instr) as i32;
                    self.push_to_stack(Word::from_int(num));
                }

                Opcode::Push1 => {
                    let instr: [u8; 1] = self.bytecode.next_bytes();
                    let num = <i8>::from_le_bytes(instr) as i32;
                    self.push_to_stack(Word::from_int(num));

                    // note:
                    // suppose byte = 255u8
                    // casting it to i32 turns it into 255i32 (makes sense)
                    // however, the specification of push1 asserts that
                    // the byte should be read as a signed integer,
                    // meaning that 255u8 should be turned to -1i32
                    // the solution is to cast it to i8 first and then to i32
                }

                Opcode::Add => self.arithmetic_bop_aux(i32::wrapping_add),
                Opcode::Sub => self.arithmetic_bop_aux(i32::wrapping_sub),
                Opcode::Mul => self.arithmetic_bop_aux(i32::wrapping_mul),
                Opcode::Div => self.arithmetic_bop_aux(i32::wrapping_div),
                Opcode::Mod => self.arithmetic_bop_aux(i32::wrapping_rem),
                Opcode::Eq => self.logical_bop_aux(PartialEq::eq),
                Opcode::Ne => self.logical_bop_aux(PartialEq::ne),
                Opcode::Lt => self.logical_bop_aux(PartialOrd::lt),
                Opcode::Gt => self.logical_bop_aux(PartialOrd::gt),
                Opcode::Le => self.logical_bop_aux(PartialOrd::le),
                Opcode::Ge => self.logical_bop_aux(PartialOrd::ge),

                Opcode::Not => {
                    let num = self.pop_from_stack().to_int();
                    self.push_to_stack(Word::from_int(if num == 0 { 1 } else { 0 }));
                }

                Opcode::And => self.arithmetic_bop_aux(ops::BitAnd::bitand),
                Opcode::Or => self.arithmetic_bop_aux(ops::BitOr::bitor),

                Opcode::Input => {
                    let mut buf = [0; 1];
                    io::stdin().read_exact(&mut buf).unwrap();
                    self.push_to_stack(Word::from_int(buf[0] as i32));
                }

                Opcode::Output => {
                    let char = self.pop_from_stack().to_int();
                    io::stdout().write_all(&[char as u8]).unwrap();
                }

                Opcode::Alloc => {
                    let tag = self.pop_from_stack().to_int();
                    let size = self.pop_from_stack().to_int();

                    loop {
                        let mut words = (0..size).fold(
                            Vec::<Word>::with_capacity(size as usize),
                            |mut v, _| {
                                v.push(self.pop_from_stack());
                                v
                            },
                        );

                        words.reverse();

                        if let Some(addr) = self.heap.alloc(size as usize, tag as u8, &words) {
                            self.push_to_stack(Word::from_pointer(addr));
                            break;
                        }

                        // before running garbage collection the words about to be
                        // allocated must be pushed back into the stack,
                        // as they might contain pointers that will need to be updated
                        // [this unironically took me around 15 hours of debugging to figure out]
                        for w in words {
                            self.push_to_stack(w);
                        }

                        // run_gc() panics if the heap does not have enough space
                        // so the loop {} will terminate after at most two iterations
                        self.heap.run_gc(&mut self.stack);
                    }
                }

                Opcode::Load => {
                    let instr: [u8; 4] = self.bytecode.next_bytes();
                    let offset = <u32>::from_le_bytes(instr) as usize;

                    let addr = self.pop_from_stack().to_pointer();

                    let w = self.heap.load(addr, offset);
                    self.push_to_stack(w);
                }

                Opcode::Clock => {
                    let dt = t0.elapsed().as_secs_f64();
                    let string = format!("{:.4}", dt);
                    io::stdout().write_all(string.as_bytes()).unwrap();
                }
            }
        }
    }

    fn peek_in_stack(&self, depth: usize) -> heap::Word {
        self.stack[(self.sp - 1) - depth]
    }

    fn push_to_stack(&mut self, w: heap::Word) {
        if self.sp >= STACK_SIZE {
            panic!("stack overflow!")
        }

        self.stack[self.sp] = w;
        self.sp += 1;
    }

    fn pop_from_stack(&mut self) -> heap::Word {
        if self.sp == 0 {
            panic!("stack underflow!")
        }

        self.sp -= 1;
        self.stack[self.sp]
    }

    fn replace_in_stack(&mut self, w: heap::Word, depth: usize) -> heap::Word {
        let w_old = self.stack[(self.sp - 1) - depth];
        self.stack[(self.sp - 1) - depth] = w;
        w_old
    }

    fn arithmetic_bop_aux(&mut self, op: impl FnOnce(i32, i32) -> i32) {
        let b = self.pop_from_stack().to_int();
        let a = self.pop_from_stack().to_int();
        let res = op(a, b);
        self.push_to_stack(heap::Word::from_int(res));
    }

    fn logical_bop_aux(&mut self, op: impl FnOnce(&i32, &i32) -> bool) {
        let b = self.pop_from_stack().to_int();
        let a = self.pop_from_stack().to_int();
        let res = if op(&a, &b) { 1 } else { 0 };
        self.push_to_stack(heap::Word::from_int(res));
    }
}
