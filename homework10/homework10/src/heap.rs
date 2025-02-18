use std::{
    fmt::{self, Debug},
    mem, vec,
};

#[derive(Clone, Copy)]
pub struct Word {
    w: i32,
}

impl Word {
    pub fn from_pointer(ptr: usize) -> Word {
        Word {
            w: (ptr as i32) << 1 | 0,
        }
    }

    pub fn from_int(int: i32) -> Word {
        Word { w: int << 1 | 1 }
    }

    pub fn to_pointer(self) -> usize {
        (self.w >> 1) as usize
    }

    pub fn to_int(self) -> i32 {
        self.w >> 1
    }

    fn is_pointer(self) -> bool {
        (self.w & 1) == 0
    }
}

impl Debug for Word {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_pointer() {
            write!(f, "Ptr({})", self.to_pointer())
        } else {
            write!(f, "Int({})", self.to_int())
        }
    }
}

pub struct Heap {
    pub heap: Box<[Word]>,
    size: usize, // The size of the heap
    from_start_addr: usize,
    to_start_addr: usize,
    from_next_addr: usize, // The heap pointer to the next free slot in the from space
}

impl Heap {
    pub fn new(total_words: usize) -> Self {
        let vec = vec![Word { w: 0 }; total_words];
        let memory = vec.into_boxed_slice();
        Heap {
            heap: memory,
            size: total_words,
            from_start_addr: 0,
            to_start_addr: total_words / 2,
            from_next_addr: 0,
        }
    }

    // attempts to allocate _words in the heap
    pub fn alloc(&mut self, size: usize, tag: u8, words: &[Word]) -> Option<usize> {
        let header = self.header_compose(size, tag);
        let word_cnt = 1 + size;

        if self.from_next_addr + word_cnt > self.from_start_addr + self.size / 2 {
            None
        } else {
            let from_curr_addr = self.from_next_addr;

            self.heap[from_curr_addr] = header;
            for i in 0..size {
                self.heap[from_curr_addr + i + 1] = words[i];
            }
            self.from_next_addr += word_cnt;

            Some(from_curr_addr)
        }
    }

    pub fn load(&self, h_addr: usize, offset: usize) -> Word {
        if h_addr >= self.from_start_addr
            && h_addr < self.from_next_addr
            && h_addr + offset >= self.from_start_addr
            && h_addr + offset < self.from_next_addr
        {
            self.heap[h_addr + offset]
        } else {
            panic!("Invalid heap address: {}", h_addr + offset);
        }
    }

    pub fn gc(&mut self, stack: &mut [Word]) -> () {
        let mut to_next_addr = self.to_start_addr;
        let mut root_curr_addr;

        for idx in 0..2 {
            if idx == 0 {
                to_next_addr = self.to_start_addr;
                root_curr_addr = 0;
            } else {
                to_next_addr = to_next_addr;
                root_curr_addr = self.to_start_addr;
            }

            loop {
                if (idx == 0 && root_curr_addr >= stack.len())
                    || (idx == 1 && root_curr_addr >= to_next_addr)
                {
                    break;
                }

                let root_word = if idx == 0 {
                    stack[root_curr_addr]
                } else {
                    self.heap[root_curr_addr]
                };

                if root_word.is_pointer() {
                    let from_curr_addr = root_word.to_pointer();
                    // rword points to fword
                    let from_word = self.heap[from_curr_addr];

                    if !from_word.is_pointer() {
                        // Case 1
                        // fword is not a pointer, fword is a header
                        // rword points to the header of a block in the from-space
                        let (size, _) = self.header_decompose(from_word);
                        let word_cnt = 1 + size;

                        let from_addrs = from_curr_addr..from_curr_addr + word_cnt;
                        self.heap.copy_within(from_addrs, to_next_addr);

                        // the pointer from the root set, rword, is updated to hold the new
                        // address of the block in the to-space
                        if idx == 0 {
                            stack[root_curr_addr] = Word::from_pointer(to_next_addr);
                        } else {
                            self.heap[root_curr_addr] = Word::from_pointer(to_next_addr);
                        }

                        // the old memory location becomes a forwarding pointer
                        self.heap[from_curr_addr] = Word::from_pointer(to_next_addr);

                        to_next_addr += word_cnt;
                    } else {
                        // check if rword points to the to-space
                        if from_curr_addr >= self.to_start_addr
                            && from_curr_addr < self.to_start_addr + self.size / 2
                        {
                            //Case 2
                            // no action is needed
                        } else {
                            // Case 3
                            // fword is a pointer
                            if idx == 0 {
                                stack[root_curr_addr] = from_word;
                            } else {
                                self.heap[root_curr_addr] = from_word;
                            }
                        }
                    }
                }
                root_curr_addr += 1;
            }
        }
        // update to, from, and free_from_hp
        mem::swap(&mut self.from_start_addr, &mut self.to_start_addr);
        self.from_next_addr = to_next_addr;
    }

    fn header_compose(&self, size: usize, tag: u8) -> Word {
        let size = (size << 8) & 0x7F_FF_FF_00;
        let tag = (tag as usize) & 0x00_00_00_FF;

        // everything will be shifted by 1 bit to the left
        // lsb of the word will be 1
        Word::from_int((size | tag) as i32)
    }

    fn header_decompose(&self, header: Word) -> (usize, u8) {
        let header = header.to_int() as usize;
        let size = (header >> 8) & 0x00_7F_FF_FF;
        let tag = header & 0x00_00_00_FF;

        (size, tag as u8)
    }
}
