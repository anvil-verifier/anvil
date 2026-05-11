// Shared atom-building macros for spec predicates.
//
// These macros expand into Verus spec code at the call site, but their
// definitions are plain Rust so they live outside any `verus!{}` block
// to keep rustc's macro-usage tracking working normally.

/// `and!(pred1, pred2, ...)` — pointwise conjunction over a state.
#[macro_export]
macro_rules! and {
    ($($tokens:tt)+) => {
        closure_to_fn_spec(|s| {
            $crate::and_internal!(s, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! and_internal {
    ($s:expr, $head:expr) => {
        $head($s)
    };

    ($s:expr, $head:expr, $($tail:tt)+) => {
        $crate::and_internal!($s, $head) && $crate::and_internal!($s, $($tail)+)
    };
}

/// `or!(pred1, pred2, ...)` — pointwise disjunction over a state.
#[macro_export]
macro_rules! or {
    ($($tokens:tt)+) => {
        closure_to_fn_spec(|s| {
            $crate::or_internal!(s, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! or_internal {
    ($s:expr, $head:expr) => {
        $head($s)
    };

    ($s:expr, $head:expr, $($tail:tt)+) => {
        $crate::or_internal!($s, $head) || $crate::or_internal!($s, $($tail)+)
    };
}

/// `not!(pred)` — pointwise negation over a state.
#[macro_export]
macro_rules! not {
    ( $pred:expr ) => {
        closure_to_fn_spec(|s| {
            ! $pred(s)
        })
    };
}

// Hacky workaround for type conversion bug:
//   error[E0605]: non-primitive cast: `{integer}` as `builtin::nat`
#[macro_export]
macro_rules! nat0 {
    () => { spec_literal_nat("0") };
}

#[macro_export]
macro_rules! nat1 {
    () => { spec_literal_nat("1") };
}

#[macro_export]
macro_rules! int0 {
    () => { spec_literal_int("0") };
}

#[macro_export]
macro_rules! int1 {
    () => { spec_literal_int("1") };
}

pub use and;
pub use and_internal;
pub use or;
pub use or_internal;
pub use not;
pub use nat0;
pub use nat1;
pub use int0;
pub use int1;
