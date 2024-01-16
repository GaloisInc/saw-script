static ANSWER: u32 = 42;

pub fn answer_to_the_ultimate_question() -> u32 {
    ANSWER
}

pub fn answer_in_ref_form() -> &'static u32 {
    &ANSWER
}

static mut MUT_ANSWER: u32 = 42;

pub fn mut_answer_to_the_ultimate_question() -> u32 {
    unsafe { MUT_ANSWER }
}

pub fn alternate_universe() -> u32 {
    unsafe {
        MUT_ANSWER = 27;
    }
    mut_answer_to_the_ultimate_question()
}
