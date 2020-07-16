#[derive(Copy, Clone, Debug)]
pub struct MemRange {
    start: u64,
    len: usize,
}

impl MemRange {
    pub fn new(start: u64) -> Self {
        MemRange { start, len: 0 }
    }

    pub fn with_len(start: u64, len: usize) -> Self {
        MemRange { start, len }
    }

    pub fn next(&self) -> u64 {
        self.start + self.len as u64
    }

    pub fn expand(&mut self, len: usize) {
        self.len += len;
    }

    pub fn start(&self) -> u64 {
        self.start
    }
}
