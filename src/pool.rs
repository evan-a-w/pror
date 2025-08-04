#[derive(Clone)]
pub struct Pool<T> {
    free: Vec<T>,
}

impl<T> Pool<T> {
    pub fn new() -> Self {
        Pool { free: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Pool {
            free: Vec::with_capacity(capacity),
        }
    }

    pub fn acquire<F>(&mut self, factory: F) -> T
    where
        F: FnOnce() -> T,
    {
        self.free.pop().unwrap_or_else(factory)
    }

    pub fn release(&mut self, item: T) {
        self.free.push(item);
    }

    pub fn len(&self) -> usize {
        self.free.len()
    }

    pub fn is_empty(&self) -> bool {
        self.free.is_empty()
    }
}

impl<T> Default for Pool<T> {
    fn default() -> Self {
        Pool::new()
    }
}
