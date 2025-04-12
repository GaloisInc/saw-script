use std::collections::{HashMap};
use std::fmt;
use std::convert::{Infallible};

/*
/* A function that immediately panics */
pub fn get_out () -> ! {
    panic!("Uh oh!")
}
*/

/* The logical and operation as a function on bool */
pub fn bool_and (x:bool, y:bool) -> bool {
    x & y
}

/* The logical and operation as a function on bools in a pair */
pub fn bool_and_pair (xy:(bool,bool)) -> bool {
    xy.0 & xy.1
}

/* Read two integers from references and return their sum */
pub fn ref_sum <'a,'b> (x:&'a u64, y:&'a u64) -> u64 {
    return *x + *y;
}

/* Double the integer pointed to by a reference by duplicating the reference and
 * passing it to ref_sum */
pub fn double_dup_ref <'a> (x:&'a u64) -> u64 {
    return ref_sum (x, x);
}

#[repr(C)]
pub struct BoolStruct { fst_bool:bool,snd_bool:bool }

/* The logical and operation as a function on bools in a struct */
pub fn bool_and_struct (xy:BoolStruct) -> bool {
    xy.fst_bool & xy.snd_bool
}

/* A struct containing 2 32-bit values, to test how structs that fit into 1
 * 64-bit value are represented */
#[repr(C)]
pub struct TwoValues(u32,u32);

pub fn mk_two_values (x1:u32,x2:u32) -> TwoValues {
    TwoValues(x1,x2)
}

pub extern fn mk_two_values_extern (x1:u32,x2:u32) -> TwoValues {
    TwoValues(x1,x2)
}

pub fn mk_two_values_opt (x1:u32,x2:u32) -> Option<TwoValues> {
    Some(TwoValues(x1,x2))
}

pub fn two_values_proj1 (x:TwoValues) -> u32 {
    match x {
        TwoValues(x1,_) => x1
    }
}

pub fn two_values_proj1_ref <'a> (x:&'a mut TwoValues) -> &'a mut u32 {
    &mut x.1
}

pub extern fn two_values_proj1_extern (x:TwoValues) -> u32 {
    match x {
        TwoValues(x1,_) => x1
    }
}

/* A struct containing 3 32-bit values, to test how structs that fit but don't
 * fill up 2 64-bit values are represented */
#[repr(C)]
pub struct ThreeValues(u32,u32,u32);

pub fn mk_three_values (x1:u32,x2:u32,x3:u32) -> ThreeValues {
    ThreeValues(x1,x2,x3)
}

pub extern fn mk_three_values_extern (x1:u32,x2:u32,x3:u32) -> ThreeValues {
    ThreeValues(x1,x2,x3)
}

pub fn three_values_proj1 (x:ThreeValues) -> u32 {
    match x {
        ThreeValues(x1,_,_) => x1
    }
}

pub extern fn three_values_proj1_extern (x:ThreeValues) -> u32 {
    match x {
        ThreeValues(x1,_,_) => x1
    }
}


/* A struct containing 4 32-bit values, to test how structs that fit into 2
 * 64-bit values are represented */
#[repr(C)]
pub struct FourValues(u32,u32,u32,u32);

pub fn mk_four_values (x1:u32,x2:u32,x3:u32,x4:u32) -> FourValues {
    FourValues(x1,x2,x3,x4)
}

pub extern fn mk_four_values_extern (x1:u32,x2:u32,x3:u32,x4:u32) -> FourValues {
    FourValues(x1,x2,x3,x4)
}

pub fn four_values_proj1 (x:FourValues) -> u32 {
    match x {
        FourValues(x1,_,_,_) => x1
    }
}

pub extern fn four_values_proj1_extern (x:FourValues) -> u32 {
    match x {
        FourValues(x1,_,_,_) => x1
    }
}


/* A struct containing 5 32-bit values, to test how structs that do not quite
 * fit into 2 64-bit values are represented */
#[repr(C)]
pub struct FiveValues(u32,u32,u32,u32,u32);

pub fn mk_five_values (x1:u32,x2:u32,x3:u32,x4:u32,x5:u32) -> FiveValues {
    FiveValues(x1,x2,x3,x4,x5)
}

pub extern fn mk_five_values_extern (x1:u32,x2:u32,x3:u32,x4:u32,x5:u32)
                                     -> FiveValues {
    FiveValues(x1,x2,x3,x4,x5)
}

pub fn mk_five_values_opt (x1:u32,x2:u32,x3:u32,x4:u32,x5:u32) -> Option<FiveValues> {
    Some(FiveValues(x1,x2,x3,x4,x5))
}

pub fn proj_five_values (i:u64, fvs:FiveValues) -> u32 {
    match fvs {
        FiveValues(x0,x1,x2,x3,x4) =>
            match i {
                0 => x0,
                1 => x1,
                2 => x2,
                3 => x3,
                _ => x4
            }
    }
}

pub fn mk_proj0_five_values (x1:u32,x2:u32,x3:u32,x4:u32,x5:u32) -> u32 {
    proj_five_values (0, mk_five_values (x1,x2,x3,x4,x5))
}


/* Test if a Result is Ok or Err */
pub fn test_result <'a> (r:&'a Result<u64,u64>) -> bool {
    match r {
        Ok(_) => true,
        Err(_) => false
    }
}

/* Make a Result whose other branch is uninhabited */
pub fn mk_result_infallible (x:u64) -> Result<Infallible,u64> {
  Err(x)
}

/* Extract a value from a Result whose other branch is uninhabited */
pub fn extract_from_result_infallible <'a> (r:&'a Result<Infallible,u64>) -> u64 {
    match r {
        Ok(i) => match *i { },
        Err(x) => *x,
    }
}

/* Sum of two types; yes, this is like Result, but defined locally so we can
 * make an impl block on it */
#[derive(Clone, Debug, PartialEq)]
#[repr(C,u64)]
pub enum Sum<X,Y> {
    Left (X),
    Right (Y)
}


/***
 *** Some tests for how Rust compiles functions on enums
 ***/

impl Sum<u64,u64> {
    pub fn test_sum_impl (&self) -> bool {
        match self {
            Sum::Left(_) => true,
            Sum::Right(_) => false
        }
    }

    pub fn mk_u64_sum_left (x:u64) -> Self {
        Sum::Left (x)
    }

    pub extern fn mk_u64_sum_left_extern (x:u64) -> Self {
        Sum::Left (x)
    }

    pub fn mk_u64_sum_left_add3 (x:&u64, y:u64, z:u64) -> Self {
        Sum::Left (*x+y+z)
    }
}

pub fn mk_sum_left_asym (x:u32) -> Sum<u32,u64> {
    Sum::Left (x)
}

pub fn mk_string_sum_left (x:&str) -> Sum<String,u64> {
    Sum::Left (x.to_string())
}

pub fn mk_sum_sum_left (x:Sum<u64,u64>) -> Sum<Sum<u64,u64>,u64> {
    Sum::Left (x)
}

pub extern fn mk_sum_sum_left_extern (x:Sum<u64,u64>) -> Sum<Sum<u64,u64>,u64> {
    Sum::Left (x)
}

pub fn mk_sum_sum_left_asym (x:Sum<u32,u64>) -> Sum<Sum<u32,u64>,u64> {
    Sum::Left (x)
}

pub extern fn mk_sum_sum_left_asym_extern (x:Sum<u32,u64>) -> Sum<Sum<u32,u64>,u64> {
    Sum::Left (x)
}


pub fn elim_sum_u64_u64 (x:Sum<u64,u64>) -> u64 {
    match x {
        Sum::Left (x) => x,
        Sum::Right (x) => x,
    }
}


/* A struct containing a string */
#[repr(C)]
pub struct StrStruct(String);

impl StrStruct {
    /* Constructor for StrStruct */
    pub fn new(name: &str) -> StrStruct {
        StrStruct(name.to_string())
    }

    // &str not considered FFI safe, so Rust doesn't like extern here
    /*
    pub extern fn new_extern(name: &str) -> StrStruct {
        StrStruct(name.to_string())
    }
    */

    /* Accessor for StrStruct */
    pub fn name(&self) -> String {
        match self {
            StrStruct(s) => s.to_string(),
        }
    }

    // String not considered FFI safe, so Rust doesn't like extern here
    /*
    pub extern fn name_extern(&self) -> String {
        match self {
            StrStruct(s) => s.to_string(),
        }
    }
     */

    /* Version of name that maps to &str */
    pub fn name_str (&self) -> &str {
        match self {
            StrStruct(s) => s.as_str(),
        }
    }

    // &str not considered FFI safe, so Rust doesn't like extern here
    /*
    pub extern fn name_str_extern (&self) -> &str {
        match self {
            StrStruct(s) => s.as_str(),
        }
    }
     */
}

/* A struct with a mix of different field types */
#[derive(Clone, Debug, PartialEq)]
#[repr(C)]
pub struct MixedStruct {
    pub s: String,
    pub i1: u64,
    pub i2: u64,
}

impl MixedStruct {
    pub fn get_s(&self) -> String {
        self.s.clone()
    }

    pub fn get_i1(&self) -> u64 {
        self.i1
    }

    pub fn get_i2(&self) -> u64 {
        self.i2
    }
}

impl fmt::Display for MixedStruct {
    fn fmt<'a, 'b>(&'a self, f: &'b mut fmt::Formatter) -> fmt::Result {
        write!(f, "s = {}, i1 = {}, i2 = {}", self.s, self.i1, self.i2)
    }
}

/* A 'true' enum */
#[derive(Clone, Debug, PartialEq)]
#[repr(u64)]
pub enum TrueEnum {
    Foo,
    Bar,
    Baz,
}

pub fn cycle_true_enum (te: &TrueEnum) -> TrueEnum {
    match te {
        TrueEnum::Foo => TrueEnum::Bar,
        TrueEnum::Bar => TrueEnum::Baz,
        TrueEnum::Baz => TrueEnum::Foo,
    }
}

impl fmt::Display for TrueEnum {
    fn fmt<'a, 'b>(&'a self, f: &'b mut fmt::Formatter) -> fmt::Result {
        match self {
            TrueEnum::Foo => f.write_str ("Foo"),
            TrueEnum::Bar => f.write_str ("Bar"),
            TrueEnum::Baz => f.write_str ("Baz"),
            /*
            TrueEnum::Foo => write!(f,"Foo"),
            TrueEnum::Bar => write!(f,"Bar"),
            TrueEnum::Baz => write!(f,"Baz"),
             */
        }
    }
}


/***
 *** Pointers and References
 ***/

pub fn box_read (p:Box<u64>) -> u64 {
    *p
}


/***
 *** Slices and Arrays
 ***/

pub fn index_one_array (x:[u64; 1]) -> u64 {
    x[0]
}

pub fn index_two_array (x:[u64; 2]) -> u64 {
    x[0]
}

pub fn index_three_array (x:[u64; 3]) -> u64 {
    x[0]
}


/***
 *** Linked Lists
 ***/

/* A linked list */
#[derive(Clone, Debug, PartialEq)]
#[repr(C,u64)]
pub enum LList<X> {
    Nil,
    Cons (X,Box<LList<X>>)
}

/* Test if a list is empty */
pub fn list_is_empty (l: &LList<u64>) -> bool {
    match l {
        LList::Nil => true,
        LList::Cons (_,_) => false
    }
}

/* Get the head of a linked list or return an error */
pub fn list_head (l: &LList<u64>) -> Box<Sum<u64,()>> {
    match l {
        LList::Nil => Box::new(Sum::Right (())),
        LList::Cons (x,_) => Box::new(Sum::Left (*x))
    }
}

/* Get the head of a linked list or return an error, in an impl block */
impl LList<u64> {
    pub fn list_head_impl (&self) -> Result<u64,()> {
        match self {
            LList::Nil => Err (()),
            LList::Cons (x,_) => Ok (*x)
        }
    }
}

/* A linked list specialized to 64-bit elements */
#[derive(Clone, Debug, PartialEq)]
#[repr(C,u64)]
pub enum List64 {
    Nil64,
    Cons64 (u64,Box<List64>)
}

pub fn box_list64_clone<'a>(x:&'a Box<List64>) -> Box<List64> {
    return x.clone();
}

pub fn list64_clone<'a>(x:&'a List64) -> List64 {
    match &x {
        List64::Nil64 => List64::Nil64,
        List64::Cons64(h,t) => List64::Cons64(*h,box_list64_clone(t)),
    }
}

/* Test if a List64 is empty */
pub fn list64_is_empty (l: &List64) -> bool {
    match l {
        List64::Nil64 => true,
        List64::Cons64 (_,_) => false
    }
}

/* Return the tail of a List64, or None if it is the empty list */
pub fn list64_tail (l: List64) -> Option<List64> {
    match l {
        List64::Nil64 => None,
        List64::Cons64 (_,tl) => Some (*tl)
    }
}

/* Sum the elements of a List64 */
pub fn list64_sum(l:&List64) -> u64 {
    match l {
        List64::Nil64 => 0,
        List64::Cons64 (x,rest) => x + list64_sum (rest),
    }
}

/* Return a mutable reference to the head of a list, or None if it is empty */
pub fn list64_head_mut <'a> (l:&'a mut List64) -> Option<&'a mut u64> {
    match l {
        List64::Nil64 => None,
        List64::Cons64 (h,_) => Some (h),
    }
}

/* Return a mutable reference to the tail of a list, or None if it is empty */
pub fn list64_tail_mut <'a> (l:&'a mut List64) -> Option<&'a mut List64> {
    match l {
        List64::Nil64 => None,
        List64::Cons64 (_,t) => Some (t),
    }
}

/* Truncate a List64 to just one element */
pub fn list64_truncate <'a> (l:&'a mut List64) {
    match list64_tail_mut(l) {
        Some (tl) => *tl = List64::Nil64,
        None => ()
    }
}

/* Find an element in a List64 and return a mutable reference to it */
pub fn list64_find_mut <'a> (x:u64, l:&'a mut List64) -> Option<&'a mut u64> {
    match l {
        List64::Nil64 => None,
        List64::Cons64 (y,rest) =>
            if x == *y { Some (y) } else { list64_find_mut (x,rest) }
    }
}

/* Build a HashMap with a String key already mapped to a list */
pub fn hash_map_for_string_and_list64 (str:String,
                                       l:List64) -> HashMap<String,List64> {
    let mut map = HashMap::new();
    map.insert (str, l);
    return map;
}

pub fn opt_hash_map_for_string_and_list64 (str:String,
                                           l:List64) -> Option<HashMap<String,List64>> {
    Some(hash_map_for_string_and_list64 (str,l))
}


/* Sum the List64s in a HashMap */
pub fn sum_hash_map_string_list64 (map:&HashMap<String,List64>) -> u64 {
    let mut ret:u64 = 0;
    for (_,l) in map.iter() {
        ret += list64_sum (l);
    }
    return ret;
}

/* Insert a mapping into m from the greatest of x and y to the other */
pub fn hash_map_insert_gt_to_le (m: &mut HashMap<u64,u64>, x:u64, y:u64) -> () {
    if x > y {
        m.insert (x, y);
    } else {
        m.insert (y, x);
    }
}

/* A binary tree */
pub enum BinTree<X> {
    BinLeaf (X),
    BinNode (Box<BinTree<X>>,Box<BinTree<X>>)
}

pub fn bintree_is_leaf (t: &BinTree<u64>) -> bool {
    match *t {
        BinTree::BinLeaf (_) => true,
        BinTree::BinNode (_,_) => false
    }
}


/* A tree whose internal nodes contain vectors of children */
pub enum Tree<X> {
    Leaf (X),
    Node (Vec<Tree<X>>)
}

pub fn tree_is_leaf (t: &Tree<u64>) -> bool {
    match *t {
        Tree::Leaf (_) => true,
        Tree::Node (_) => false
    }
}

/* Sum all leaves in a tree */
/*
pub fn tree_sum (t: &Tree<u64>) -> u64 {
    let mut acc = 0;
    match *t {
        Tree::Leaf (x) => x,
        Tree::Node (children) =>
            for u in children {
                acc += tree_sum (u);
            }
            acc;
    }
}
*/

/* A 20-element enum that just wraps around type X */
#[repr(u64)]
pub enum Enum20<X> {
  Enum20_0(X),
  Enum20_1(X),
  Enum20_2(X),
  Enum20_3(X),
  Enum20_4(X),
  Enum20_5(X),
  Enum20_6(X),
  Enum20_7(X),
  Enum20_8(X),
  Enum20_9(X),
  Enum20_10(X),
  Enum20_11(X),
  Enum20_12(X),
  Enum20_13(X),
  Enum20_14(X),
  Enum20_15(X),
  Enum20_16(X),
  Enum20_17(X),
  Enum20_18(X),
  Enum20_19(X),
}

pub fn enum20_list_proj<'a> (x:&'a Enum20<LList<u64>>) -> &'a LList<u64> {
  match x {
      Enum20::Enum20_0(l) => l,
      Enum20::Enum20_1(l) => l,
      Enum20::Enum20_2(l) => l,
      Enum20::Enum20_3(l) => l,
      Enum20::Enum20_4(l) => l,
      Enum20::Enum20_5(l) => l,
      Enum20::Enum20_6(l) => l,
      Enum20::Enum20_7(l) => l,
      Enum20::Enum20_8(l) => l,
      Enum20::Enum20_9(l) => l,
      Enum20::Enum20_10(l) => l,
      Enum20::Enum20_11(l) => l,
      Enum20::Enum20_12(l) => l,
      Enum20::Enum20_13(l) => l,
      Enum20::Enum20_14(l) => l,
      Enum20::Enum20_15(l) => l,
      Enum20::Enum20_16(l) => l,
      Enum20::Enum20_17(l) => l,
      Enum20::Enum20_18(l) => l,
      Enum20::Enum20_19(l) => l,
  }
}

/* A non-empty list type with 20 separate constructors */
#[repr(u64)]
pub enum List10<X> {
  List10Head(X),
  List10_0(X,Box<List10<X>>),
  List10_1(X,Box<List10<X>>),
  List10_2(X,Box<List10<X>>),
  List10_3(X,Box<List10<X>>),
  List10_4(X,Box<List10<X>>),
  List10_5(X,Box<List10<X>>),
  List10_6(X,Box<List10<X>>),
  List10_7(X,Box<List10<X>>),
  List10_8(X,Box<List10<X>>),
  List10_9(X,Box<List10<X>>),
}

pub fn list10_head<'a> (x:&'a List10<LList<u64>>) -> &'a LList<u64> {
  match x {
      List10::List10Head(l) => l,
      List10::List10_0(l,_) => l,
      List10::List10_1(l,_) => l,
      List10::List10_2(l,_) => l,
      List10::List10_3(l,_) => l,
      List10::List10_4(l,_) => l,
      List10::List10_5(l,_) => l,
      List10::List10_6(l,_) => l,
      List10::List10_7(l,_) => l,
      List10::List10_8(l,_) => l,
      List10::List10_9(l,_) => l,
  }
}


/* A non-empty list type with 20 separate constructors */
#[repr(u64)]
pub enum List20<X> {
  List20Head(X),
  List20_0(X,Box<List20<X>>),
  List20_1(X,Box<List20<X>>),
  List20_2(X,Box<List20<X>>),
  List20_3(X,Box<List20<X>>),
  List20_4(X,Box<List20<X>>),
  List20_5(X,Box<List20<X>>),
  List20_6(X,Box<List20<X>>),
  List20_7(X,Box<List20<X>>),
  List20_8(X,Box<List20<X>>),
  List20_9(X,Box<List20<X>>),
  List20_10(X,Box<List20<X>>),
  List20_11(X,Box<List20<X>>),
  List20_12(X,Box<List20<X>>),
  List20_13(X,Box<List20<X>>),
  List20_14(X,Box<List20<X>>),
  List20_15(X,Box<List20<X>>),
  List20_16(X,Box<List20<X>>),
  List20_17(X,Box<List20<X>>),
  List20_18(X,Box<List20<X>>),
  List20_19(X,Box<List20<X>>),
}

pub fn list20_head<'a> (x:&'a List20<LList<u64>>) -> &'a LList<u64> {
  match x {
      List20::List20Head(l) => l,
      List20::List20_0(l,_) => l,
      List20::List20_1(l,_) => l,
      List20::List20_2(l,_) => l,
      List20::List20_3(l,_) => l,
      List20::List20_4(l,_) => l,
      List20::List20_5(l,_) => l,
      List20::List20_6(l,_) => l,
      List20::List20_7(l,_) => l,
      List20::List20_8(l,_) => l,
      List20::List20_9(l,_) => l,
      List20::List20_10(l,_) => l,
      List20::List20_11(l,_) => l,
      List20::List20_12(l,_) => l,
      List20::List20_13(l,_) => l,
      List20::List20_14(l,_) => l,
      List20::List20_15(l,_) => l,
      List20::List20_16(l,_) => l,
      List20::List20_17(l,_) => l,
      List20::List20_18(l,_) => l,
      List20::List20_19(l,_) => l,
  }
}

impl Clone for List20<u64> {
    fn clone<'a>(&'a self) -> Self {
        match &self {
            List20::List20Head(b) => List20::List20Head(*b),
            List20::List20_0(h,t) => List20::List20_0(*h,t.clone()),
            List20::List20_1(h,t) => List20::List20_1(*h,t.clone()),
            List20::List20_2(h,t) => List20::List20_2(*h,t.clone()),
            List20::List20_3(h,t) => List20::List20_3(*h,t.clone()),
            List20::List20_4(h,t) => List20::List20_4(*h,t.clone()),
            List20::List20_5(h,t) => List20::List20_5(*h,t.clone()),
            List20::List20_6(h,t) => List20::List20_6(*h,t.clone()),
            List20::List20_7(h,t) => List20::List20_7(*h,t.clone()),
            List20::List20_8(h,t) => List20::List20_8(*h,t.clone()),
            List20::List20_9(h,t) => List20::List20_9(*h,t.clone()),
            List20::List20_10(h,t) => List20::List20_10(*h,t.clone()),
            List20::List20_11(h,t) => List20::List20_11(*h,t.clone()),
            List20::List20_12(h,t) => List20::List20_12(*h,t.clone()),
            List20::List20_13(h,t) => List20::List20_13(*h,t.clone()),
            List20::List20_14(h,t) => List20::List20_14(*h,t.clone()),
            List20::List20_15(h,t) => List20::List20_15(*h,t.clone()),
            List20::List20_16(h,t) => List20::List20_16(*h,t.clone()),
            List20::List20_17(h,t) => List20::List20_17(*h,t.clone()),
            List20::List20_18(h,t) => List20::List20_18(*h,t.clone()),
            List20::List20_19(h,t) => List20::List20_19(*h,t.clone()),
        }
    }
}
