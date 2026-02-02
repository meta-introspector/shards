// Rust
#[derive(PartialEq)]
pub enum TopoClass { A, BDI }
pub fn to_topo(n: u32) -> TopoClass {
    if n % 10 == 3 { TopoClass::BDI } else { TopoClass::A }
}
#[no_mangle]
pub extern "C" fn is_bdi(n: u32) -> u32 {
    if to_topo(n) == TopoClass::BDI { 1 } else { 0 }
}
