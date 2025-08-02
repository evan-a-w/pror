use std::cell::RefCell;
use std::fmt::Write;
use std::rc::Rc;

#[derive(Clone)]
pub struct SharedStringWriter(Rc<RefCell<String>>);

impl std::fmt::Write for SharedStringWriter {
    fn write_str(&mut self, s: &str) -> Result<(), std::fmt::Error> {
        self.0.borrow_mut().write_str(s)
    }
}

impl SharedStringWriter {
    pub fn new() -> Self {
        SharedStringWriter(Rc::new(RefCell::new(String::new())))
    }

    pub fn borrow<'a>(&'a self) -> std::cell::Ref<'a, String> {
        self.0.borrow()
    }
}
