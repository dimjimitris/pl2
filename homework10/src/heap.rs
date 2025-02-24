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
            w: (ptr as i32) << 1,
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
        let vec = vec![Word::from_int(0); total_words];
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
        let header = Heap::header_compose(size, tag);
        let word_cnt = 1 + size;

        if self.from_next_addr + word_cnt > self.from_start_addr + self.size / 2 {
            None
        } else {
            let from_curr_addr = self.from_next_addr;

            self.heap[from_curr_addr] = header;
            for (i, word) in words.iter().enumerate().take(size) {
                self.heap[from_curr_addr + i + 1] = *word;
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
        // the next address in the to-space where we can write
        let mut to_next_addr = self.to_start_addr;
        // the current address in the root space where we read from
        let mut root_curr_addr;

        // garbage collection happens in 2 passes
        // first pass: idx == 0 and root-space === stack
        // second pass: idx == 1 and root-space === to-space
        for idx in 0..2 {
            // initialize to_next_addr and root_curr_addr variables
            // properly for each pass
            #[allow(clippy::self_assignment)]
            if idx == 0 {
                to_next_addr = self.to_start_addr;
                root_curr_addr = 0;
            } else {
                to_next_addr = to_next_addr;
                root_curr_addr = self.to_start_addr;
            }

            // first pass: idx == 0, will go through all of the stack slice we
            // supply. So root_curr_addr in [0, stack.len())
            // second pass: idx == 1, will go through all of the to-space, considering
            // to-space memory entries added as the algorithm moves forward. So
            // root_curr_addr in [self.to_start_addr, to_next_addr), where to_next_addr
            // will dynamically change
            while root_curr_addr < if idx == 0 { stack.len() } else { to_next_addr } {
                // get the root word we will be examining
                let root_word = if idx == 0 {
                    // root word is in the stack
                    stack[root_curr_addr]
                } else {
                    // root word is in the heap
                    self.heap[root_curr_addr]
                };

                // if the root word is not a pointer, there is nothing to do...
                if root_word.is_pointer() {
                    // root word is a pointer
                    let from_curr_addr = root_word.to_pointer();
                    // root word is a pointer that points to from word
                    let from_word = self.heap[from_curr_addr];

                    if !from_word.is_pointer() {
                        // Case 1
                        // from word is not a pointer
                        // it is a header of a block in the from-space
                        let (size, _) = Heap::header_decompose(from_word);
                        let word_cnt = 1 + size;

                        // we copy this block to the to-space
                        let from_addrs = from_curr_addr..from_curr_addr + word_cnt;
                        self.heap.copy_within(from_addrs, to_next_addr);

                        // the root word is a pointer and needs to be updated to hold the new
                        // address of the block in the to-space
                        if idx == 0 {
                            // root word is in the stack
                            stack[root_curr_addr] = Word::from_pointer(to_next_addr);
                        } else {
                            // root word is in the heap
                            self.heap[root_curr_addr] = Word::from_pointer(to_next_addr);
                        }

                        // the memory location of the from word is updated to point to
                        // the new address of the block in the to-space
                        // from word is now a forwarding pointer
                        self.heap[from_curr_addr] = Word::from_pointer(to_next_addr);

                        // get the next available address, where we can write
                        to_next_addr += word_cnt;
                    } else {
                        // from word is a pointer
                        if from_curr_addr >= self.to_start_addr
                            && from_curr_addr < self.to_start_addr + self.size / 2
                        {
                            // Case 2
                            // root word is a pointer that points to from_curr_addr
                            // from_curr_addr is in to-space
                            // we do not need to do anything
                        } else {
                            // Case 3
                            // root word is a pointer that points to from_curr_addr
                            // from_curr_addr is in from-space, this means that is is
                            // a forwarding pointer
                            // we update root word to point to the same address
                            // Thus we set root word equal to from word
                            if idx == 0 {
                                // root word is in the stack
                                stack[root_curr_addr] = from_word;
                            } else {
                                // root word is in the heap
                                self.heap[root_curr_addr] = from_word;
                            }
                        }
                    }
                }
                // move to the next address in the root-space
                root_curr_addr += 1;
            }
        }
        // update from_start_addr, to_start_addr, and from_next_addr
        mem::swap(&mut self.from_start_addr, &mut self.to_start_addr);
        self.from_next_addr = to_next_addr;
    }

    fn header_compose(size: usize, tag: u8) -> Word {
        let size = (size << 8) & 0x7F_FF_FF_00;
        let tag = (tag as usize) & 0x00_00_00_FF;

        // everything will be shifted by 1 bit to the left
        // lsb of the word will be 1
        Word::from_int((size | tag) as i32)
    }

    fn header_decompose(header: Word) -> (usize, u8) {
        let header = header.to_int() as usize;
        let size = (header >> 8) & 0x00_7F_FF_FF;
        let tag = header & 0x00_00_00_FF;

        (size, tag as u8)
    }
}
