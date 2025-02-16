use std::{cmp, fmt, mem};

#[derive(Clone, Copy)]
pub struct Word {
    w: i32,
}

impl Word {
    pub fn from_int(int: i32) -> Self {
        Self { w: int << 1 | 1 }
    }

    pub fn from_pointer(ptr: usize) -> Self {
        Self {
            w: (ptr as i32) << 1,
        }
    }

    pub fn to_int(self) -> i32 {
        self.w >> 1
    }

    pub fn to_pointer(self) -> usize {
        (self.w >> 1) as usize
    }

    pub fn is_pointer(self) -> bool {
        (self.w & 1) == 0
    }
}

impl fmt::Debug for Word {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_pointer() {
            write!(f, "Ptr({})", self.to_pointer())
        } else {
            write!(f, "Int({})", self.to_int())
        }
    }
}

pub trait Heap {
    fn new(capacity: usize) -> Self;
    fn alloc(&mut self, size: usize, tag: u8, words: &[Word]) -> Option<usize>;
    fn load(&self, addr: usize, offset: usize) -> Word;
    fn run_gc(&mut self, stack: &mut [Word]);
}

pub struct CheneyHeap {
    data: Box<[Word]>,
    capacity: usize,
    fs_start: usize,
    ts_start: usize,
    next_fs_addr: usize,
}

impl Heap for CheneyHeap {
    fn new(capacity: usize) -> Self {
        Self {
            data: vec![Word::from_int(0); capacity].into_boxed_slice(),
            capacity,
            fs_start: 0,
            ts_start: capacity / 2,
            next_fs_addr: 0,
        }
    }

    fn alloc(&mut self, size: usize, tag: u8, words: &[Word]) -> Option<usize> {
        debug_assert_eq!(size, words.len(), "size does not match word count");

        let total_words = 1 + words.len();
        let header = construct_header(size, tag);

        if self.next_fs_addr + total_words > self.fs_start + self.capacity / 2 {
            return None;
        }

        let fs_addr = self.next_fs_addr;
        self.data[fs_addr] = header;
        self.data[(fs_addr + 1)..(fs_addr + total_words)].copy_from_slice(words);

        self.next_fs_addr += total_words;
        Some(fs_addr)
    }

    fn load(&self, addr: usize, offset: usize) -> Word {
        if addr + offset >= self.capacity {
            panic!("address out of bounds");
        }

        self.data[addr + offset]
    }

    fn run_gc(&mut self, stack: &mut [Word]) {
        // * INVARIANT: [from-space -> to-space] pointers don't exist
        debug_assert!(self.data[self.fs_start..self.next_fs_addr]
            .iter()
            .all(|w| { !w.is_pointer() || is_pointer_to_fspace(self, w.to_pointer()) }));

        // next free slot of the to-space
        let mut next_ts_addr = self.ts_start;

        // * STEP 1: find every (from-space) object reachable
        // * from the stack and move it to the to-space

        // A. a stack word can be:
        // 1. a pointer to the heap
        // 2. an integer (case eliminated by filter iterator)
        for stack_word in stack.iter_mut().filter(|w| w.is_pointer()) {
            // * INVARIANT: [stack -> to-space] pointers don't exist
            debug_assert!(is_pointer_to_fspace(self, stack_word.to_pointer()));

            let curr_fs_addr = stack_word.to_pointer();

            // * CASE A1: the stack word is a pointer to the heap

            // B. a from-space word can be:
            // 1. an object header
            // 2. a forwarding pointer to the new address
            //    of an already moved object
            let fs_word = self.data[curr_fs_addr];
            if fs_word.is_pointer() {
                // * CASE B2: the heap word is a forwarding pointer

                // * INVARIANT: forwarding pointers point to the to-space
                debug_assert!(is_pointer_to_tspace(self, fs_word.to_pointer()));

                *stack_word = fs_word;
                continue;
            }

            // * CASE B1: the from-space word is the header of an object

            // the object must be copied to the to-space
            let (size, _) = destruct_header(fs_word);
            let total_size = 1 + size; // account for the header

            // ensure there is enough space for the object
            if next_ts_addr + total_size > self.ts_start + self.capacity / 2 {
                panic!("insufficient space on the heap");
            }

            // * INVARIANT: the new and old addresses of the object don't overlap
            debug_assert!(
                // old address: [fspace_addr_start, fspace_addr_end)
                // new address: [tspace_addr_start, tspace_addr_end)

                // non-overlap test:
                // fspace_addr_end <= tspace_addr_start
                //  || fspace_addr_start >= tspace_addr_end
                curr_fs_addr + total_size <= next_ts_addr
                    || curr_fs_addr >= next_ts_addr + total_size
            );

            // copy the object
            let curr_fs_addr_range = curr_fs_addr..(curr_fs_addr + total_size);
            self.data.copy_within(curr_fs_addr_range, next_ts_addr);

            // replace the old address on the stack with the new one
            // replace the old header with a forwarding pointer
            *stack_word = Word::from_pointer(next_ts_addr);
            self.data[curr_fs_addr] = Word::from_pointer(next_ts_addr);

            // calculate the next free slot of the to-space
            next_ts_addr += total_size;
        }

        // * IVARIANT: [to-space -> to-space] pointers don't exist
        debug_assert!(self.data[self.ts_start..next_ts_addr]
            .iter()
            .all(|w| { !w.is_pointer() || is_pointer_to_fspace(self, w.to_pointer()) }));

        // * STEP 2: find every (from-space) object reachable
        // * from the to-space and move it to the to-space

        // address of the word to start iterating from
        let mut curr_ts_addr = self.ts_start;

        // stop when every allocated word in the to-space has been checked
        while curr_ts_addr < next_ts_addr {
            // C. a to-space word can be
            // 1. an object header
            // 2. a non-pointer object field
            // 3. a pointer to an object header in the to-space
            // 4. a pointer to an object header in the from-space
            // 5. a pointer to a forwarding pointer in the from-space
            let ts_word = self.data[curr_ts_addr];
            if !ts_word.is_pointer() {
                // * CASES C1, C2: the to-space word is either
                // * an object header or a non-pointer object field

                curr_ts_addr += 1;
                continue;
            }

            if is_pointer_to_tspace(self, ts_word.to_pointer()) {
                // * CASE C3: the to-space word is a pointer
                // * to an object header in the to-space

                // * INVARIANT: [to-space -> to-space] pointers only point to headers
                debug_assert!(!self.data[ts_word.to_pointer()].is_pointer());

                curr_ts_addr += 1;
                continue;
            }

            // * CASES C4, C5: the to-space word is a pointer to a from-space word

            let curr_fs_addr = ts_word.to_pointer();
            let fs_word = self.data[curr_fs_addr];
            if fs_word.is_pointer() {
                // * CASE C5: the from-space word is a forwarding pointer

                // * INVARIANT: from-space forwarding pointers point to the to-space
                debug_assert!(is_pointer_to_tspace(self, fs_word.to_pointer()));

                self.data[curr_ts_addr] = fs_word;
                curr_ts_addr += 1;
                continue;
            }

            // * CASE C4: the from-space word is an object header
            let (size, _tag) = destruct_header(fs_word);
            let total_size = 1 + size;

            // ensure there is enough space for the object
            if next_ts_addr + total_size > next_ts_addr + self.capacity / 2 {
                panic!("insufficient space on the heap");
            }

            // * INVARIANT: the new and old addresses of the object don't overlap
            debug_assert!(
                // see previous loop for an explanation of the following check
                curr_fs_addr + total_size <= next_ts_addr
                    || curr_fs_addr >= next_ts_addr + total_size
            );

            // copy the object
            let curr_fs_addr_range = curr_fs_addr..(curr_fs_addr + total_size);
            self.data.copy_within(curr_fs_addr_range, next_ts_addr);

            // replace the old address on the to-space with the new one
            // and replace the old header with a forwarding pointer
            self.data[curr_ts_addr] = Word::from_pointer(next_ts_addr);
            self.data[curr_fs_addr] = Word::from_pointer(next_ts_addr);

            // calculate the next free slot of the to-space
            next_ts_addr += total_size;

            curr_ts_addr += 1;
        }

        // * INVARIANT: [to-space -> from-space] pointers don't exist
        debug_assert!(self.data[self.ts_start..next_ts_addr]
            .iter()
            .all(|w| { !w.is_pointer() || is_pointer_to_tspace(self, w.to_pointer()) }));

        // swap from-space and to-space
        // [ from-space | to-space ] <-> [ to-space | from-space ]
        mem::swap(&mut self.fs_start, &mut self.ts_start);
        self.next_fs_addr = next_ts_addr;
    }
}

/**
 The first word is the header that contains metadata about the block:
  - The 23 higher-order bits represent the number of fields, `n`, in the block.
  - The next 8 bits store the tag, which provides additional information about the type of the block.
  - The lowest-order bit is always `1`.
 */
#[rustfmt::skip]
fn construct_header(size: usize, tag: u8) -> Word {
    let size = (size) << 8    & 0b0111_1111_1111_1111_1111_1111_0000_0000;
    let tag  = (tag as usize) & 0b0000_0000_0000_0000_0000_0000_1111_1111;
    Word::from_int((size | tag) as i32) // ints have lowest-order bit 1
}

/// Returns the pair (size, tag)
#[rustfmt::skip]
fn destruct_header(header: Word) -> (usize, u8) {
    let header = header.to_int();
    let size = (header >> 8) & 0b0000_0000_0111_1111_1111_1111_1111_1111;
    let tag  = header        & 0b0000_0000_0000_0000_0000_0000_1111_1111;
    (size as usize, tag as u8)
}

fn is_pointer_to_fspace(heap: &CheneyHeap, ptr: usize) -> bool {
    // * INVARIANT: this function is always called with a valid pointer
    debug_assert!(
        ptr >= cmp::min(heap.fs_start, heap.ts_start) && ptr < heap.capacity,
        "pointer out of bounds"
    );

    // [ from-space          | to-space                   ]
    // [ 0 .. (capacity / 2) | (capacity / 2) .. capacity ]
    if heap.fs_start < heap.ts_start {
        ptr < heap.ts_start
    }
    // [ to-space            | from-space                 ]
    // [ 0 .. (capacity / 2) | (capacity / 2) .. capacity ]
    else {
        ptr >= heap.fs_start
    }
}

fn is_pointer_to_tspace(heap: &CheneyHeap, ptr: usize) -> bool {
    // * INVARIANT: this function is always called with a valid pointer
    debug_assert!(
        ptr >= cmp::min(heap.fs_start, heap.ts_start) && ptr < heap.capacity,
        "pointer out of bounds"
    );

    !is_pointer_to_fspace(heap, ptr)
}

// --------------------------------------------------

pub struct SimpleHeap {
    data: Box<[Word]>,
    capacity: usize,
    next_addr: usize,
}

impl Heap for SimpleHeap {
    fn new(capacity: usize) -> Self {
        Self {
            data: vec![Word::from_int(0); capacity].into_boxed_slice(),
            capacity,
            next_addr: 0,
        }
    }

    fn alloc(&mut self, size: usize, tag: u8, words: &[Word]) -> Option<usize> {
        debug_assert_eq!(size, words.len(), "size does not match word count");

        let header = construct_header(size, tag);
        let total_words = 1 + words.len();

        if self.next_addr + total_words > self.capacity {
            return None;
        }

        let addr = self.next_addr;
        self.data[addr] = header;
        self.data[(addr + 1)..(addr + total_words)].copy_from_slice(words);

        self.next_addr += total_words;
        Some(addr)
    }

    fn load(&self, addr: usize, offset: usize) -> Word {
        if addr + offset >= self.capacity {
            panic!("address out of bounds");
        }

        self.data[addr + offset]
    }

    fn run_gc(&mut self, _stack: &mut [Word]) {
        panic!("this heap does not support garbage collection!")
    }
}
