use std::{env, fs};

mod bytecode;
mod heap;
mod vm;

fn main() {
    let args: Vec<String> = env::args().collect();

    let file_path = &args[1];

    let raw_bytes = fs::read(file_path).expect("Unable to read the file.");

    let bytecode = bytecode::Bytecode::from_raw_bytes(&raw_bytes);

    //let mut vm = VM::<heap::SimpleHeap>::new(bytecode);
    let mut vm = vm::VM::<heap::CheneyHeap>::new(bytecode);

    vm.run();
}
