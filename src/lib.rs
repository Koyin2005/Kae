pub mod backend;
pub mod frontend;
pub mod middle;
pub mod thir_lowering;
mod data_structures;
mod identifiers;
pub use identifiers::SymbolInterner as SymbolInterner;
pub use identifiers::GlobalSymbols as GlobalSymbols;
mod errors;
