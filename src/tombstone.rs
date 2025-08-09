pub type Generation = usize;

#[derive(Debug)]
pub enum TombStone<T> {
    T(Generation, T),
    TombStone(Generation, Option<usize>),
}

impl<T> TombStone<T> {
    pub fn new(gen: Generation, t: T) -> Self {
        TombStone::T(gen, t)
    }

    pub fn generation(&self) -> &usize {
        match self {
            TombStone::T(gen, _) => gen,
            TombStone::TombStone(gen, _) => gen,
        }
    }

    pub fn generation_mut(&mut self) -> &mut usize {
        match self {
            TombStone::T(gen, _) => gen,
            TombStone::TombStone(gen, _) => gen,
        }
    }

    pub fn tombstone_idx_exn(&self) -> Option<usize> {
        match self {
            TombStone::TombStone(_, idx) => *idx,
            TombStone::T(_, _) => panic!("expected tombstone"),
        }
    }

    pub fn value(&self) -> Option<&T> {
        match self {
            TombStone::T(_, t) => Some(t),
            TombStone::TombStone(_, _) => None,
        }
    }

    pub fn value_mut(&mut self) -> Option<&mut T> {
        match self {
            TombStone::T(_, t) => Some(t),
            TombStone::TombStone(_, _) => None,
        }
    }

    pub fn value_exn(&self) -> &T {
        self.value().unwrap()
    }

    pub fn value_mut_exn(&mut self) -> &mut T {
        self.value_mut().unwrap()
    }
}
