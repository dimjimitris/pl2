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
    size: usize,         // The size of the heap
    from: usize,         // The index of the from-space
    to: usize,           // The index of the to-space
    free_from_hp: usize, // The heap pointer to the next free slot in the from space
}

impl Heap {
    pub fn new(total_words: usize) -> Self {
        let vec = vec![Word { w: 0 }; total_words];
        let memory = vec.into_boxed_slice();
        Heap {
            heap: memory,
            size: total_words,
            from: 0,
            to: total_words / 2,
            free_from_hp: 0,
        }
    }

    // attempts to allocate _words in the heap
    pub fn alloc(&mut self, size: usize, tag: u8, words: &[Word]) -> Option<usize> {
        let header = self.header_compose(size, tag);
        let word_cnt = 1 + size;

        if self.free_from_hp + word_cnt > self.from + self.size / 2 {
            None
        } else {
            let hp_start = self.free_from_hp;

            self.heap[hp_start] = header;
            for i in 0..size {
                self.heap[hp_start + i + 1] = words[i];
            }
            self.free_from_hp += word_cnt;

            Some(hp_start)
        }
    }

    pub fn load(&self, h_addr: usize, offset: usize) -> Word {
        if h_addr + offset >= self.size {
            panic!("Invalid heap address: {}", h_addr + offset);
        }

        self.heap[h_addr + offset]
    }

    pub fn gc2(&mut self, words: &mut [Word]) -> () {
        let (a_free_to_hp0, a_free_to_hp) = self.gc_aux_1(self.to, self.to, words);
        let (_, b_free_to_hp) = self.gc_aux_2(self.to, a_free_to_hp, a_free_to_hp0);
        // update to, from, and free_from_hp
        mem::swap(&mut self.from, &mut self.to);
        self.free_from_hp = b_free_to_hp;
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

    fn gc_aux_1(&mut self, to: usize, mut free_to_hp: usize, words: &mut [Word]) -> (usize, usize) {
        let free_to_hp0 = free_to_hp;

        for rword in words.iter_mut().filter(|w| w.is_pointer()) {
            // rword belongs to the root set.

            let used_from_hp = rword.to_pointer();
            // rword points to fword
            let fword = self.heap[used_from_hp];

            if !fword.is_pointer() {
                // Case 1
                // fword is not a pointer, fword is a header
                // rword points to the header of ablock in the from-space
                let (size, _) = self.header_decompose(fword);
                let word_cnt = 1 + size;

                let faddresses = used_from_hp..used_from_hp + word_cnt;
                self.heap.copy_within(faddresses, free_to_hp);

                // the pointer from the root set, rword, is updated to hold the new
                // address of the block in the to-space
                *rword = Word::from_pointer(free_to_hp);
                // the old memory location becomes a forwarding pointer
                self.heap[used_from_hp] = Word::from_pointer(free_to_hp);

                free_to_hp += word_cnt;
            } else {
                // check if rword points to the to-space
                if used_from_hp >= to && used_from_hp < to + self.size / 2 {
                    //Case 2
                    // no action is needed
                } else {
                    // Case 3
                    // fword is a pointer
                    *rword = fword;
                }
            }
        }
        (free_to_hp0, free_to_hp)
    }

    pub fn gc(&mut self, words: &mut [Word]) -> () {
        let mut free_to_hp = self.to;
        let mut used_root_address;

        for idx in 0..2 {
            if idx == 0 {
                free_to_hp = self.to;
                used_root_address = 0;
            } else {
                free_to_hp = free_to_hp;
                used_root_address = self.to;
            }

            loop {
                if (idx == 0 && used_root_address >= words.len())
                    || (idx == 1 && used_root_address >= free_to_hp)
                {
                    break;
                }

                let rword = if idx == 0 { words[used_root_address] } else { self.heap[used_root_address] };

                if rword.is_pointer() {
                    let used_from_hp = rword.to_pointer();
                    // rword points to fword
                    let fword = self.heap[used_from_hp];

                    if !fword.is_pointer() {
                        // Case 1
                        // fword is not a pointer, fword is a header
                        // rword points to the header of a block in the from-space
                        let (size, _) = self.header_decompose(fword);
                        let word_cnt = 1 + size;

                        let faddresses = used_from_hp..used_from_hp + word_cnt;
                        self.heap.copy_within(faddresses, free_to_hp);

                        // the pointer from the root set, rword, is updated to hold the new
                        // address of the block in the to-space
                        if idx == 0 {
                            words[used_root_address] = Word::from_pointer(free_to_hp);
                        } else {
                            self.heap[used_root_address] = Word::from_pointer(free_to_hp);
                        }

                        // the old memory location becomes a forwarding pointer
                        self.heap[used_from_hp] = Word::from_pointer(free_to_hp);

                        free_to_hp += word_cnt;
                    } else {
                        // check if rword points to the to-space
                        if used_from_hp >= self.to && used_from_hp < self.to + self.size / 2 {
                            //Case 2
                            // no action is needed
                        } else {
                            // Case 3
                            // fword is a pointer
                            if idx == 0 {
                                words[used_root_address] = fword;
                            } else {
                                self.heap[used_root_address] = fword;
                            }
                        }
                    }
                }
                used_root_address += 1;
            }
        }
        // update to, from, and free_from_hp
        mem::swap(&mut self.from, &mut self.to);
        self.free_from_hp = free_to_hp;
    }

    fn gc_aux_2(
        &mut self,
        to: usize,
        mut free_to_hp: usize,
        mut used_root_address: usize,
    ) -> (usize, usize) {
        let free_to_hp0 = free_to_hp;

        while used_root_address < free_to_hp {
            let rword = self.heap[used_root_address];
            if rword.is_pointer() {
                let used_from_hp = rword.to_pointer();
                // rword points to fword
                let fword = self.heap[used_from_hp];

                if !fword.is_pointer() {
                    // Case 1
                    // fword is not a pointer, fword is a header
                    // rword points to the header of ablock in the from-space
                    let (size, _) = self.header_decompose(fword);
                    let word_cnt = 1 + size;

                    let faddresses = used_from_hp..used_from_hp + word_cnt;
                    self.heap.copy_within(faddresses, free_to_hp);

                    // the pointer from the root set, rword, is updated to hold the new
                    // address of the block in the to-space
                    self.heap[used_root_address] = Word::from_pointer(free_to_hp);
                    // the old memory location becomes a forwarding pointer
                    self.heap[used_from_hp] = Word::from_pointer(free_to_hp);

                    free_to_hp += word_cnt;
                } else {
                    // check if rword points to the to-space
                    if used_from_hp >= to && used_from_hp < to + self.size / 2 {
                        //Case 2
                        // no action is needed
                    } else {
                        // Case 3
                        // fword is a pointer
                        self.heap[used_root_address] = fword;
                    }
                }
            }
            used_root_address += 1;
        }
        (free_to_hp0, used_root_address)
    }
}
