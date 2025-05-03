/// This macro evaluates to its contents if the `v1_24` feature is enabled, otherwise it evaluates to nothing.
///
/// # Examples
///
/// ```rust
/// # #[macro_use] extern crate k8s_openapi;
/// k8s_if_1_24! {
///     use k8s_openapi::api::core::v1 as api;
/// }
/// ```
#[macro_export] macro_rules! k8s_if_1_24 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_24` or higher feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_ge_1_24 { ($($tt:tt)*) => { $($tt)* }; }

/// This macro evaluates to its contents if the `v1_24` or lower feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_le_1_24 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_25` feature is enabled, otherwise it evaluates to nothing.
///
/// # Examples
///
/// ```rust
/// # #[macro_use] extern crate k8s_openapi;
/// k8s_if_1_25! {
///     use k8s_openapi::api::core::v1 as api;
/// }
/// ```
#[macro_export] macro_rules! k8s_if_1_25 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_25` or higher feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_ge_1_25 { ($($tt:tt)*) => { $($tt)* }; }

/// This macro evaluates to its contents if the `v1_25` or lower feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_le_1_25 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_26` feature is enabled, otherwise it evaluates to nothing.
///
/// # Examples
///
/// ```rust
/// # #[macro_use] extern crate k8s_openapi;
/// k8s_if_1_26! {
///     use k8s_openapi::api::core::v1 as api;
/// }
/// ```
#[macro_export] macro_rules! k8s_if_1_26 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_26` or higher feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_ge_1_26 { ($($tt:tt)*) => { $($tt)* }; }

/// This macro evaluates to its contents if the `v1_26` or lower feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_le_1_26 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_27` feature is enabled, otherwise it evaluates to nothing.
///
/// # Examples
///
/// ```rust
/// # #[macro_use] extern crate k8s_openapi;
/// k8s_if_1_27! {
///     use k8s_openapi::api::core::v1 as api;
/// }
/// ```
#[macro_export] macro_rules! k8s_if_1_27 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_27` or higher feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_ge_1_27 { ($($tt:tt)*) => { $($tt)* }; }

/// This macro evaluates to its contents if the `v1_27` or lower feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_le_1_27 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_28` feature is enabled, otherwise it evaluates to nothing.
///
/// # Examples
///
/// ```rust
/// # #[macro_use] extern crate k8s_openapi;
/// k8s_if_1_28! {
///     use k8s_openapi::api::core::v1 as api;
/// }
/// ```
#[macro_export] macro_rules! k8s_if_1_28 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_28` or higher feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_ge_1_28 { ($($tt:tt)*) => { $($tt)* }; }

/// This macro evaluates to its contents if the `v1_28` or lower feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_le_1_28 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_29` feature is enabled, otherwise it evaluates to nothing.
///
/// # Examples
///
/// ```rust
/// # #[macro_use] extern crate k8s_openapi;
/// k8s_if_1_29! {
///     use k8s_openapi::api::core::v1 as api;
/// }
/// ```
#[macro_export] macro_rules! k8s_if_1_29 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_29` or higher feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_ge_1_29 { ($($tt:tt)*) => { $($tt)* }; }

/// This macro evaluates to its contents if the `v1_29` or lower feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_le_1_29 { ($($tt:tt)*) => { }; }

/// This macro evaluates to its contents if the `v1_30` feature is enabled, otherwise it evaluates to nothing.
///
/// # Examples
///
/// ```rust
/// # #[macro_use] extern crate k8s_openapi;
/// k8s_if_1_30! {
///     use k8s_openapi::api::core::v1 as api;
/// }
/// ```
#[macro_export] macro_rules! k8s_if_1_30 { ($($tt:tt)*) => { $($tt)* }; }

/// This macro evaluates to its contents if the `v1_30` or higher feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_ge_1_30 { ($($tt:tt)*) => { $($tt)* }; }

/// This macro evaluates to its contents if the `v1_30` or lower feature is enabled, otherwise it evaluates to nothing.
#[macro_export] macro_rules! k8s_if_le_1_30 { ($($tt:tt)*) => { $($tt)* }; }

/// A macro that emits a `match` expr with the given test expression and arms.
/// The match arms can be annotated with the other conditional compilation macros in this crate so that they're only emitted
/// if the predicate is true.
#[macro_export] macro_rules! k8s_match {
    (@inner { $test:expr } { $($arms:tt)* } { }) => {
        match $test { $($arms)* }
    };

    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_1_24!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_ge_1_24!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($arm)*, $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_le_1_24!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };

    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_1_25!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_ge_1_25!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($arm)*, $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_le_1_25!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };

    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_1_26!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_ge_1_26!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($arm)*, $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_le_1_26!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };

    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_1_27!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_ge_1_27!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($arm)*, $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_le_1_27!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };

    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_1_28!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_ge_1_28!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($arm)*, $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_le_1_28!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };

    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_1_29!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_ge_1_29!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($arm)*, $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_le_1_29!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($rest)* })
    };

    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_1_30!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($arm)*, $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_ge_1_30!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($arm)*, $($rest)* })
    };
    (@inner { $test:expr } { $($arms:tt)* } { k8s_if_le_1_30!($($arm:tt)*), $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* } { $($arm)*, $($rest)* })
    };

    (@inner { $test:expr } { $($arms:tt)* } { $next_pat:pat $(if $cond:expr)? => $next_expr:expr, $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { $($arms)* $next_pat $(if $cond)? => $next_expr, } { $($rest)* })
    };

    ($test:expr, { $($rest:tt)* }) => {
        k8s_match!(@inner { $test } { } { $($rest)* })
    };
}
