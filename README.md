# Installation
Install `cargo` (rust tool for package managing and compiling).
Run `cargo run` with `--debug` or `--release` flag (default is `--debug`).

# How to compute?
    * `use typenum::U8 as N;` -- all the computation is done over Z8 in that case
    * `type Int = u16;` -- 16 bit Int for efficiency, if you find some errors for large groups try changing to `u32`, `u64` or even `u128`
    * `type R = C<N>; type I = CIdeal<N>;` -- parameters for the code, do not change
