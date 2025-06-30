pub mod scanner;
pub mod tokens;
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceLocation {
    pub start_line: u32,
    pub end_line: u32,
}
impl SourceLocation {
    pub fn one_line(line: u32) -> Self {
        Self {
            start_line: line,
            end_line: line,
        }
    }
    pub fn new(start: u32, end: u32) -> Self {
        Self {
            start_line: start,
            end_line: end,
        }
    }
}
