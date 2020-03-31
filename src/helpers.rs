use std::io::{self, Error, Read, Write};
use std::result::Result;

pub trait ReadUninterrupted {
    fn read_uninterrupted(&mut self, buf: &mut [u8]) -> Result<usize, Error>;
}

impl<T: Read> ReadUninterrupted for T {
    fn read_uninterrupted(&mut self, buf: &mut [u8]) -> Result<usize, Error> {
        loop {
            match self.read(buf) {
                Ok(n) => break Ok(n),
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => continue,
                err => break err,
            }
        }
    }
}

pub trait WriteUninterrupted {
    fn write_uninterrupted(&mut self, buf: &[u8]) -> Result<usize, Error>;
}

impl<T: Write> WriteUninterrupted for T {
    fn write_uninterrupted(&mut self, buf: &[u8]) -> Result<usize, Error> {
        loop {
            match self.write(buf) {
                Ok(n) => break Ok(n),
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => continue,
                err => break err,
            }
        }
    }
}
