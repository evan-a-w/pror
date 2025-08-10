/// s(n): Luby sequence term, 1-based (1,1,2,1,1,2,4,...)
pub fn luby_term(n: u64) -> u64 {
    let mut k = 1u64;
    while (1u64 << k) - 1 < n {
        k += 1;
    }
    if n == (1u64 << k) - 1 {
        1u64 << (k - 1)
    } else {
        let prev_block = (1u64 << (k - 1)) - 1;
        luby_term(n - prev_block)
    }
}

/// Multiply Luby terms by a "unit run" `u` (e.g., conflicts per run)
#[derive(Clone, Debug)]
pub struct Luby {
    u: u64,
    i: u64, // number of terms produced so far
}

impl Luby {
    pub fn new(unit_run: u64) -> Self {
        Self { u: unit_run, i: 1 }
    }
    pub fn value(&self) -> u64 {
        self.u * luby_term(self.i)
    }
}

impl Iterator for Luby {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        self.i += 1; // terms are 1-based
        Some(self.value())
    }
}
