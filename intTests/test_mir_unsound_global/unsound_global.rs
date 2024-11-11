// unsound_global.rs
//
// (this is essentially the same as unsound_global.c from
// test_llvm_unsound_global)

static mut TEST: u32 = 1;

// the C version uses an array, but that currently causes extra
// complications here (you can't successfully assign GLOBAL[1] without
// initializing GLOBAL[0], and that requires also initializing
// GLOBAL[1], and that changes the meaning of the test, so for now
// just use a scalar.
//static mut GLOBAL: [u32; 2] = [0, 0];
static mut GLOBAL: u32 = 0;

pub fn foo(x: u32) -> u32 {
   //unsafe { GLOBAL[1] = x };
   unsafe { GLOBAL = x };
   x + 1
}

pub fn bar() -> u32 {
   unsafe { TEST = 42 };
   //unsafe { GLOBAL[1] = 0 };
   unsafe { GLOBAL = 0 };
   let val: u32 = foo(1);
   // this does not go, not entirely sure why
   //println!("{}", unsafe { TEST } );
   // unsafe { GLOBAL[1] = 0 };
   // unsafe { GLOBAL = 0 };
   //val + unsafe { GLOBAL[1] }
   val + unsafe { GLOBAL }
}
