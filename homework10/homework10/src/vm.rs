use crate::bytecode::{Bytecode, Opcode};
use crate::heap::{Heap, Word};
use std::time::Instant;
use std::io::{self, Read, Write};

pub const STACK_SIZE: usize = 1 << 14;
pub const HEAP_SIZE: usize = 1 << 20;

/// The VM struct
pub struct VM {
    pub bytecode: Bytecode,
    stack: [Word; STACK_SIZE],  // Fixed-size stack of words
    sp: usize,                  // Stack pointer. Points to the next free slot in the stack.
    ip: usize,                  // Instruction pointer
    heap: Heap,                 // The heap
}

impl VM {
    /// Create a new `VM` with the given bytecode
    pub fn new(bytecode: Bytecode) -> Self {
        VM {
            bytecode,
            stack: [Word::from_int(0); STACK_SIZE], // Initialize stack with zeroes
            sp: 0,
            ip: 0,
            heap: Heap::new(HEAP_SIZE), // The heap
        }
    }

    #[cfg(debug_assertions)]
    fn print_state(&self) {
        print!("Stack: ");
        for i in 0..self.sp {
            print!("| {:?} ", self.stack[i]);
        }
        println!("|");

        let opcode: Option<Opcode> = Opcode::from_u8(self.bytecode.instructions[self.ip]);

        println!("IP 0x{:X}: {:?}", self.ip, opcode);
    }

    #[cfg(not(debug_assertions))]
    fn print_state(&self) {}

    pub fn run(&mut self) {
        let ts = Instant::now();

        loop {
            let i_opcode = self.pop_bytecode::<1>();
            let opcode = Opcode::from_u8(i_opcode[0])
                .unwrap_or_else(|| panic!("Invalid opcode {} at i_addr {}", i_opcode[0], self.ip));

            match opcode {
                Opcode::Halt => {
                    break;
                }
                Opcode::Jump => {
                    let i_addr = <u16>::from_le_bytes(self.pop_bytecode::<2>());
                    self.jump(i_addr);
                }
                Opcode::Jnz => {
                    let i_addr: u16 = <u16>::from_le_bytes(self.pop_bytecode::<2>());
                    let val = self.pop_stack().to_int();
                    if val != 0 {
                        self.jump(i_addr);
                    }
                }
                Opcode::Jumpi => {
                    let val = self.pop_stack().to_int();
                    let i_addr = <u16>::try_from(val)
                        .expect("Jump address out of bounds");
                    self.jump(i_addr);
                }
                Opcode::Dup => {
                    let depth_bytes = self.pop_bytecode::<1>();
                    let depth = <u8>::from_le_bytes(depth_bytes) as usize;

                    let word = self.peek_stack(depth);
                    self.push_stack(word);
                }
                Opcode::Swap => {
                    let depth_bytes = self.pop_bytecode::<1>();
                    let depth = <u8>::from_le_bytes(depth_bytes) as usize;

                    let word_bot = self.peek_stack(depth);
                    let word_top = self.peek_stack(0);

                    self.put_stack(depth, word_top);
                    self.put_stack(0, word_bot);
                }
                Opcode::Drop => {
                    self.pop_stack();
                }
                Opcode::Push4 => {
                    let val = <i32>::from_le_bytes(self.pop_bytecode::<4>());
                    self.push_stack(Word::from_int(val));
                }
                Opcode::Push2 => {
                    let val = <i16>::from_le_bytes(self.pop_bytecode::<2>());
                    self.push_stack(Word::from_int(val as i32));
                }
                Opcode::Push1 => {
                    let val = <i8>::from_le_bytes(self.pop_bytecode::<1>());
                    self.push_stack(Word::from_int(val as i32));
                }
                Opcode::Add => {
                    self.bop(|a, b| a + b);
                }
                Opcode::Sub => {
                    self.bop(|a, b| a - b);
                }
                Opcode::Mul => {
                    self.bop(|a, b| a * b);
                }
                Opcode::Div => {
                    self.bop(|a, b| a / b);
                }
                Opcode::Mod => {
                    self.bop(|a, b| a % b);
                }
                Opcode::Eq => {
                    self.bop(|a, b| (a == b) as i32);
                }
                Opcode::Ne => {
                    self.bop(|a, b| (a != b) as i32);
                }
                Opcode::Lt => {
                    self.bop(|a, b| (a < b) as i32);
                }
                Opcode::Gt => {
                    self.bop(|a, b| (a > b) as i32);
                }
                Opcode::Le => {
                    self.bop(|a, b| (a <= b) as i32);
                }
                Opcode::Ge => {
                    self.bop(|a, b| (a >= b) as i32);
                }
                Opcode::Not => {
                    let a = self.pop_stack().to_int();
                    self.push_stack(Word::from_int((a == 0) as i32));
                }
                Opcode::And => {
                    self.bop(|a, b| a & b);
                }
                Opcode::Or => {
                    self.bop(|a, b| a | b);
                }
                Opcode::Input => {
                    let mut buffer: [u8; 1] = [0; 1];
                    io::stdin()
                        .read_exact(&mut buffer)
                        .expect("Failed to read input");
                    // source is unsigned, so cast will 0 extend
                    self.push_stack(Word::from_int(buffer[0] as i32));
                }
                Opcode::Output => {
                    let val = self.pop_stack().to_int();
                    io::stdout()
                        .write_all(&[val as u8])
                        .expect("Failed to write output");
                }
                Opcode::Alloc => {
                    let tag = self.pop_stack().to_int();
                    let size = self.pop_stack().to_int();

                    for error_idx in 0..3 {
                        if error_idx >= 2 {
                            panic!("Run out of heap memory");
                        }
                        
                        let mut words = Vec::<Word>::with_capacity(size as usize);
                        for _ in 0..size {
                            words.push(self.pop_stack());
                        }
                        words.reverse();

                        match self.heap.alloc(size as usize, tag as u8, &words) {
                            // success
                            Some(h_addr) => {
                                self.push_stack(Word::from_pointer(h_addr));
                                break;
                            }
                            //failure
                            None => {
                                // return stack to its original state
                                for word in words {
                                    self.push_stack(word);
                                }
    
                                // run garbage collection and try again
                                self.heap.gc(&mut self.stack[..self.sp]);
                            }
                        }
                    }

                }
                Opcode::Load => {
                    let h_addr = self.pop_stack().to_pointer();
                    let offset = <u32>::from_le_bytes(self.pop_bytecode::<4>());
                    let offset = offset as usize;
                    let word = self.heap.load(h_addr, offset);
                    self.push_stack(word);
                }
                Opcode::Clock => {
                    let elapsed = ts.elapsed().as_secs_f64();
                    io::stdout()
                        .write_all(format!("{:.4}", elapsed).as_bytes())
                        .expect("Failed to write output");
                }
            }

        }
    }

    // Pop the next N bytes from the bytecode and move instruction pointer
    fn pop_bytecode<const N: usize>(&mut self) -> [u8; N] {
        if self.ip + N > self.bytecode.instructions.len() {
            panic!("Unexpected end of bytecode")
        }
        let mut bytes = [0; N];
        bytes.copy_from_slice(&self.bytecode.instructions[self.ip..self.ip + N]);
        self.ip += N;

        // pop is done, return bytes
        bytes
    }

    // jump to a given instruction address
    fn jump(&mut self, i_addr: u16) {
        let i_addr = i_addr as usize;
        if i_addr >= self.bytecode.instructions.len() {
            panic!("Invalid jump instruction address")
        }
        self.ip = i_addr;
    }

    fn pop_stack(&mut self) -> Word {
        if self.sp < 1 {
            panic!("Stack underflow (pop)")
        }
        self.sp -= 1;
        self.stack[self.sp]
    }

    fn peek_stack(&self, depth : usize) -> Word {
        if self.sp < depth + 1 {
            panic!("Stack underflow (peek)")
        }
        self.stack[self.sp - depth - 1]
    }

    fn push_stack(&mut self, word: Word) -> () {
        if self.sp >= STACK_SIZE {
            panic!("Stack overflow")
        }
        self.stack[self.sp] = word;
        self.sp += 1;
    }

    fn put_stack(&mut self, depth : usize, word: Word) -> () {
        if self.sp < depth + 1 {
            panic!("Stack underflow (put)")
        }
        self.stack[self.sp - depth - 1] = word; 
    }

    fn bop(&mut self, op: fn(i32, i32) -> i32) -> () {
        let b = self.pop_stack().to_int();
        let a = self.pop_stack().to_int();
        self.push_stack(Word::from_int(op(a, b)));
    }
}
