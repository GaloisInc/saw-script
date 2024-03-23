pub enum Error {
    Overflow,
}

pub fn increment(count: u32) -> Result<u32, Error> {
    if count < u32::MAX {
        Ok(count+1)
    } else {
        Err(Error::Overflow)
    }
}

pub fn f() -> Result<u32, Error> {
    increment(0)
}

pub fn g() -> Result<u32, Error> {
    increment(u32::MAX)
}
