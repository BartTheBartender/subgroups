#![feature(specialization)]
#![feature(generic_const_exprs)]
#![feature(let_chains)]
#![feature(btree_extract_if)]
#![feature(iterator_try_collect)]
#![feature(trait_alias)]
/* this feature is necessary to constrain matrices,
however, a bug inside it prevents using type aliases for other types
*/
// #![feature(lazy_type_alias)]
// visual separator
#![allow(incomplete_features, reason = "we need nightly features")]
#![allow(dead_code, reason = "to be removed later")] // REMOVE THIS LATER

// - - -
/* clippy begin */
#![warn(
    // regular groups
    clippy::all, // just in case
    clippy::nursery,
    clippy::pedantic,
    clippy::style,
    clippy::complexity,
    clippy::perf,

    // debugging remnants
    clippy::dbg_macro,
    //clippy::expect_used,
    //clippy::panic,
    clippy::print_stderr,
    //clippy::print_stdout,
    clippy::todo,
    clippy::unimplemented,
    clippy::unreachable,
    clippy::use_debug,
    //clippy::unwrap_used,

    // restricions
    clippy::arithmetic_side_effects,
    clippy::clone_on_ref_ptr,
    clippy::else_if_without_else,
    clippy::float_cmp_const,
    clippy::fn_to_numeric_cast_any,
    clippy::if_then_some_else_none,
    clippy::let_underscore_must_use,
    clippy::map_err_ignore,
    clippy::missing_assert_message,
    clippy::multiple_inherent_impl,
    clippy::multiple_unsafe_ops_per_block,
    clippy::mutex_atomic,
    clippy::pattern_type_mismatch,
    clippy::rc_buffer,
    clippy::rc_mutex,
    clippy::same_name_method,
    clippy::shadow_reuse,
    clippy::shadow_same,
    clippy::shadow_unrelated,
    clippy::single_char_lifetime_names,
    clippy::str_to_string,
    clippy::string_slice,
    clippy::string_to_string,
    clippy::verbose_file_reads,

    // style
    clippy::decimal_literal_representation,
    clippy::format_push_string,
    clippy::tests_outside_test_module,
)]
#![deny(
    clippy::correctness,

    // restrictions
    clippy::as_conversions,
    clippy::allow_attributes_without_reason,
    clippy::default_numeric_fallback,
    clippy::exit,
    clippy::indexing_slicing,
    clippy::lossy_float_literal,
    clippy::mem_forget,
    clippy::string_add,
    clippy::try_err,

    // style
    clippy::empty_structs_with_brackets,
    clippy::impl_trait_in_params,
    clippy::rest_pat_in_fully_bound_structs,
    clippy::self_named_module_files,
    clippy::semicolon_inside_block,
    clippy::unnecessary_self_imports,
    clippy::unneeded_field_pattern,
    clippy::unseparated_literal_suffix,
)]
#![allow(clippy::module_name_repetitions, reason = "this is a dumb rule")]
/* clippy end */

mod category;
mod ralg;

// - - -

use crate::{
    category::{morphism::Morphism, object::Concrete},
    ralg::{
        cgroup::{ideal::CIdeal, C},
        module::canon::object::Object as Module,
    },
};
// parameters for the code
use typenum::U8 as N;
type Int = u16;
type R = C<N>;
type I = CIdeal<N>;

use std::time::Instant;

fn main() {
    let group = [8,8,8].into_iter().collect::<Module<R, I>>();
    print!("{group} ");

    let start = Instant::now();
    let subgroups = group.submodules();
    let duration = start.elapsed();
    
    /*
    println!("\nSubgroups: ");
    for subgroup in subgroups.iter() {
        println!("{subgroup)\n----------------------------")
    }
    */


    println!("{} {:.3?}",subgroups.len(), duration.as_secs_f64()); // formatted time output
}
