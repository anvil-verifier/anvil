// Native checks for the decimal string conversions in `vstd_ext::string_view`.
//
// `i32_to_string` and `usize_to_string` stay `external_body` (vstd leaves `ToString::to_string`
// on integers uninterpreted); their contracts say the result is `int_to_string_view`, the
// canonical base-10 representation. These tests compare them against an independent reference
// implementation of that definition, and check the verified `parse_usize`,
// `is_canonical_decimal_nat` and `cmp_ordinal_suffix_desc` on the edges their contracts name.
use std::cmp::Ordering;
use verifiable_controllers::vstatefulset_controller::trusted::reconciler::{
    cmp_ordinal_suffix_desc, get_ordinal_suffix,
};
use verifiable_controllers::vstd_ext::string_view::{
    i32_to_string, is_canonical_decimal_nat, parse_usize, usize_to_string,
};

// The spec's `nat_to_string_view` / `int_to_string_view`, digit by digit.
fn reference_nat(n: u128) -> String {
    if n < 10 {
        ((b'0' + n as u8) as char).to_string()
    } else {
        let mut s = reference_nat(n / 10);
        s.push((b'0' + (n % 10) as u8) as char);
        s
    }
}

fn reference_int(i: i128) -> String {
    if i >= 0 {
        reference_nat(i as u128)
    } else {
        format!("-{}", reference_nat((-i) as u128))
    }
}

#[test]
fn test_to_string_matches_int_to_string_view() {
    let i32s = [0, 1, 9, 10, 99, 100, 12345, i32::MAX, -1, -9, -10, -12345, i32::MIN];
    for i in i32s {
        assert_eq!(i32_to_string(i), reference_int(i as i128), "i32 {}", i);
    }
    let usizes = [0, 1, 9, 10, 11, 100, 1000000, usize::MAX - 1, usize::MAX];
    for u in usizes {
        assert_eq!(usize_to_string(u), reference_nat(u as u128), "usize {}", u);
    }
}

#[test]
fn test_parse_usize_accepts_exactly_canonical_usize_decimals() {
    for u in [0usize, 7, 10, 42, 1000, usize::MAX] {
        assert_eq!(parse_usize(&reference_nat(u as u128)), Some(u));
    }
    let above_max = reference_nat(usize::MAX as u128 + 1);
    for s in ["", "-1", "+1", "00", "007", "1a", "a1", " 1", "1 ", "١", above_max.as_str(), "99999999999999999999999"] {
        assert_eq!(parse_usize(s), None, "{:?}", s);
    }
}

#[test]
fn test_is_canonical_decimal_nat() {
    let above_max = reference_nat(usize::MAX as u128 + 1);
    for s in ["0", "1", "10", "907", above_max.as_str(), "100000000000000000000000000000"] {
        assert!(is_canonical_decimal_nat(s), "{:?}", s);
    }
    for s in ["", "-0", "-1", "+1", "00", "01", "1.0", "1e3", "x", "١٢"] {
        assert!(!is_canonical_decimal_nat(s), "{:?}", s);
    }
}

#[test]
fn test_ordinal_suffixes_compare_by_value_descending() {
    let cases = [
        ("2", "10", Ordering::Greater),
        ("10", "2", Ordering::Less),
        ("18446744073709551616", "18446744073709551615", Ordering::Less),
        ("100000000000000000000", "18446744073709551616", Ordering::Less),
        ("123", "123", Ordering::Equal),
        ("0", "0", Ordering::Equal),
        ("19", "91", Ordering::Greater),
    ];
    for (a, b, expected) in cases {
        assert_eq!(cmp_ordinal_suffix_desc(a, b), expected, "{} vs {}", a, b);
    }
}

#[test]
fn test_get_ordinal_suffix() {
    let parent = "web".to_string();
    let some = |n: &str| get_ordinal_suffix(&parent, &n.to_string()).map(|s| s.to_string());
    assert_eq!(some("vstatefulset-web-0"), Some("0".to_string()));
    assert_eq!(some("vstatefulset-web-18446744073709551616"), Some("18446744073709551616".to_string()));
    for n in ["vstatefulset-web-", "vstatefulset-web-01", "vstatefulset-web-+1", "vstatefulset-web2-1", "vstatefulset-we-1", "web-1", "vstatefulset-web-1-0"] {
        assert_eq!(some(n), None, "{:?}", n);
    }
}
