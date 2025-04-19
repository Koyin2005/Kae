pub mod backend;
pub mod frontend;
mod data_structures;
mod identifiers;
pub use identifiers::SymbolInterner as SymbolInterner;
pub use identifiers::GlobalSymbols as GlobalSymbols;

