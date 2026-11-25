// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

use vstd::{prelude::*, utf8::*};
use crate::vstd_ext::seq_lib::*;

verus! {

pub type StringView = Seq<char>;

// helper function to circumvent the lack of support for String in spec
pub fn string_equal(s1: &String, s2: &str) -> (res: bool)
    ensures
        s1@ == s2@ <==> res,
{
    s1.as_str() == s2
}

// `ToString::to_string` on integers is only specified by vstd through the uninterpreted
// `to_string_from_display_ensures`, so the two conversions below stay trusted. Their contracts
// are stated against the concrete decimal definition `int_to_string_view` below and are tested
// natively in `tests/string_view_decimal.rs`.
#[verifier(external_body)]
pub fn i32_to_string(i: i32) -> (s: String)
    ensures s@ == int_to_string_view(i as int),
{
    i.to_string()
}

#[verifier(external_body)]
pub fn usize_to_string(i: usize) -> (s: String)
    ensures s@ == int_to_string_view(i as int)
{
    i.to_string()
}

// The inverse of usize_to_string: Some(i) iff s is the canonical decimal representation of a
// usize value i; None iff no usize value has canonical decimal representation s (including when s
// is a canonical decimal integer above usize::MAX).
//
// It reads the digits itself instead of calling `str::parse`, so that the contract is proved
// rather than trusted: `str::parse` also accepts non-canonical forms such as "+1" and "007",
// which `usize_to_string` never produces.
pub fn parse_usize(s: &str) -> (res: Option<usize>)
    ensures
        res is Some ==> s@ == int_to_string_view(res->0 as int),
        res is None ==> forall |i: usize| s@ != #[trigger] int_to_string_view(i as int),
{
    broadcast use vstd::string::is_ascii_spec_bytes;
    if !s.is_ascii() {
        proof {
            assert forall |i: usize| s@ != #[trigger] int_to_string_view(i as int) by {
                lemma_nat_to_string_view_props(i as nat);
            }
        }
        return None;
    }
    let bytes = s.as_bytes();
    let ghost b = bytes@;
    assert(b =~= Seq::new(s@.len(), |i: int| s@[i] as u8));
    if bytes.len() == 0 || (bytes.len() > 1 && bytes[0] == b'0') {
        proof {
            assert forall |i: usize| s@ != #[trigger] int_to_string_view(i as int) by {
                if s@ == int_to_string_view(i as int) {
                    lemma_nat_str_to_canonical_bytes(i as nat);
                }
            }
        }
        return None;
    }
    let mut acc: usize = 0;
    let mut idx: usize = 0;
    assert(b.take(0) =~= Seq::<u8>::empty());
    while idx < bytes.len()
        invariant
            b == bytes@,
            b =~= Seq::new(s@.len(), |i: int| s@[i] as u8),
            b.len() >= 1,
            b.len() > 1 ==> b[0] != 48u8,
            0 <= idx <= b.len(),
            forall |j: int| 0 <= j < idx ==> 48u8 <= #[trigger] b[j] <= 57u8,
            acc as nat == decimal_bytes_val(b.take(idx as int)),
        decreases b.len() - idx,
    {
        let c = bytes[idx];
        if c < b'0' || c > b'9' {
            proof {
                assert forall |i: usize| s@ != #[trigger] int_to_string_view(i as int) by {
                    if s@ == int_to_string_view(i as int) {
                        lemma_nat_str_to_canonical_bytes(i as nat);
                        assert(48u8 <= b[idx as int] <= 57u8);
                    }
                }
            }
            return None;
        }
        let digit = (c - b'0') as usize;
        assert(b.take(idx + 1).drop_last() =~= b.take(idx as int));
        assert(decimal_bytes_val(b.take(idx + 1)) == decimal_bytes_val(b.take(idx as int)) * 10 + digit);
        if acc > (usize::MAX - digit) / 10 {
            proof {
                assert(acc * 10 + digit > usize::MAX) by (nonlinear_arith)
                    requires acc > (usize::MAX - digit) / 10, digit <= 9;
                assert forall |i: usize| s@ != #[trigger] int_to_string_view(i as int) by {
                    if s@ == int_to_string_view(i as int) {
                        lemma_nat_str_to_canonical_bytes(i as nat);
                        lemma_decimal_bytes_val_take_le(b, idx + 1);
                    }
                }
            }
            return None;
        }
        acc = acc * 10 + digit;
        idx += 1;
    }
    proof {
        assert(b.take(b.len() as int) =~= b);
        lemma_canonical_bytes_to_nat_str(s@, b);
    }
    Some(acc)
}

pub fn is_canonical_decimal_nat(s: &str) -> (res: bool)
    ensures
        res == (exists |i: nat| s@ == #[trigger] int_to_string_view(i as int)),
{
    broadcast use vstd::string::is_ascii_spec_bytes;
    if !s.is_ascii() {
        proof {
            assert forall |i: nat| s@ != #[trigger] int_to_string_view(i as int) by {
                lemma_nat_to_string_view_props(i);
            }
        }
        return false;
    }
    let bytes = s.as_bytes();
    let ghost b = bytes@;
    assert(b =~= Seq::new(s@.len(), |i: int| s@[i] as u8));
    if bytes.len() == 0 || (bytes.len() > 1 && bytes[0] == b'0') {
        proof {
            assert forall |i: nat| s@ != #[trigger] int_to_string_view(i as int) by {
                if s@ == int_to_string_view(i as int) {
                    lemma_nat_str_to_canonical_bytes(i);
                }
            }
        }
        return false;
    }
    let mut idx: usize = 0;
    while idx < bytes.len()
        invariant
            b == bytes@,
            b =~= Seq::new(s@.len(), |i: int| s@[i] as u8),
            0 <= idx <= b.len(),
            forall |j: int| 0 <= j < idx ==> 48u8 <= #[trigger] b[j] <= 57u8,
        decreases b.len() - idx,
    {
        if bytes[idx] < b'0' || bytes[idx] > b'9' {
            proof {
                assert forall |i: nat| s@ != #[trigger] int_to_string_view(i as int) by {
                    if s@ == int_to_string_view(i as int) {
                        lemma_nat_str_to_canonical_bytes(i);
                        assert(48u8 <= b[idx as int] <= 57u8);
                    }
                }
            }
            return false;
        }
        idx += 1;
    }
    proof {
        lemma_canonical_bytes_to_nat_str(s@, b);
        let n = decimal_bytes_val(b);
        assert(s@ == int_to_string_view(n as int));
    }
    true
}

#[verifier(external_body)]
pub fn starts_with(s: &String, prefix: &str) -> (res: bool)
    ensures res == starts_with_spec(s@, prefix@),
{
    s.starts_with(prefix)
}

// The canonical base-10 representation of an integer, as produced by `ToString::to_string` on
// Rust's integer types: no leading zeros, and a leading '-' for negative values.
pub open spec fn int_to_string_view(i: int) -> StringView {
    if i >= 0 {
        nat_to_string_view(i as nat)
    } else {
        seq!['-'] + nat_to_string_view((-i) as nat)
    }
}

pub open spec fn nat_to_string_view(n: nat) -> StringView
    decreases n,
{
    if n < 10 {
        seq![digit_to_char(n as int)]
    } else {
        nat_to_string_view((n / 10) as nat) + seq![digit_to_char((n % 10) as int)]
    }
}

pub open spec fn digit_to_char(d: int) -> char {
    if d == 0 { '0' }
    else if d == 1 { '1' }
    else if d == 2 { '2' }
    else if d == 3 { '3' }
    else if d == 4 { '4' }
    else if d == 5 { '5' }
    else if d == 6 { '6' }
    else if d == 7 { '7' }
    else if d == 8 { '8' }
    else { '9' }
}

// The value of a sequence of ASCII digit bytes, read in base 10.
pub open spec fn decimal_bytes_val(b: Seq<u8>) -> nat
    decreases b.len(),
{
    if b.len() == 0 {
        0
    } else {
        decimal_bytes_val(b.drop_last()) * 10 + ((b.last() - 48) as nat)
    }
}

// A nonempty sequence of ASCII digit bytes without a leading zero (unless it is "0").
pub open spec fn is_canonical_decimal_bytes(b: Seq<u8>) -> bool {
    &&& b.len() >= 1
    &&& (b.len() == 1 || b[0] != 48u8)
    &&& forall |i: int| 0 <= i < b.len() ==> 48u8 <= (#[trigger] b[i]) <= 57u8
}

pub proof fn int_to_string_view_injectivity()
    ensures forall |i: int, j: int| int_to_string_view(i) == int_to_string_view(j) ==> i == j,
{
    assert forall |i: int, j: int| int_to_string_view(i) == int_to_string_view(j) implies i == j by {
        lemma_int_to_string_view_injective(i, j);
    }
}

pub proof fn int_to_string_view_ascii()
    ensures forall |i: int| is_ascii_chars(#[trigger] int_to_string_view(i)),
{
    assert forall |i: int| is_ascii_chars(#[trigger] int_to_string_view(i)) by {
        if i >= 0 {
            lemma_nat_to_string_view_props(i as nat);
        } else {
            let digits = nat_to_string_view((-i) as nat);
            lemma_nat_to_string_view_props((-i) as nat);
            assert forall |k: int| 0 <= k < int_to_string_view(i).len()
                implies '\0' <= #[trigger] int_to_string_view(i)[k] <= '\u{7f}' by {
                if k > 0 {
                    assert(int_to_string_view(i)[k] == digits[k - 1]);
                }
            }
        }
    }
}

// Only the representation of a nonnegative integer is free of dashes: a negative one starts
// with '-'.
pub proof fn int_to_string_view_dash_free()
    ensures forall |i: int| i >= 0 ==> dash_free(#[trigger] int_to_string_view(i)),
{
    assert forall |i: int| i >= 0 implies dash_free(#[trigger] int_to_string_view(i)) by {
        lemma_nat_to_string_view_props(i as nat);
        reveal_strlit("-");
        assert forall |k: int| 0 <= k < int_to_string_view(i).len()
            implies int_to_string_view(i)[k] != '-'@ by {
            assert(48u8 <= (int_to_string_view(i)[k] as u8) <= 57u8);
        }
    }
}

pub proof fn lemma_digit_to_char_props(d: int)
    requires
        0 <= d < 10,
    ensures
        (digit_to_char(d) as u8) == (48 + d) as u8,
        '\0' <= digit_to_char(d) <= '\u{7f}',
        (digit_to_char(d) == '0') <==> (d == 0),
{}

pub proof fn lemma_digit_to_char_injective(d1: int, d2: int)
    requires
        0 <= d1 < 10,
        0 <= d2 < 10,
        digit_to_char(d1) == digit_to_char(d2),
    ensures
        d1 == d2,
{}

pub proof fn lemma_nat_to_string_view_props(n: nat)
    ensures
        nat_to_string_view(n).len() >= 1,
        n >= 10 ==> nat_to_string_view(n).len() >= 2,
        is_ascii_chars(nat_to_string_view(n)),
        forall |i: int| 0 <= i < nat_to_string_view(n).len()
            ==> 48u8 <= (#[trigger] nat_to_string_view(n)[i] as u8) <= 57u8,
        nat_to_string_view(n).len() > 1 ==> nat_to_string_view(n)[0] != '0',
    decreases n,
{
    if n < 10 {
        lemma_digit_to_char_props(n as int);
    } else {
        let q = (n / 10) as nat;
        let r = (n % 10) as int;
        lemma_nat_to_string_view_props(q);
        lemma_digit_to_char_props(r);
        let sq = nat_to_string_view(q);
        let sr = seq![digit_to_char(r)];
        assert((sq + sr)[0] == sq[0]);
        if sq.len() == 1 {
            assert(q >= 1 && q < 10);
            lemma_digit_to_char_props(q as int);
        }
        assert forall |i: int| 0 <= i < (sq + sr).len()
            implies '\0' <= #[trigger] (sq + sr)[i] <= '\u{7f}'
                && 48u8 <= ((sq + sr)[i] as u8) <= 57u8 by {
            if i < sq.len() {
                assert((sq + sr)[i] == sq[i]);
            } else {
                assert((sq + sr)[i] == sr[0]);
            }
        };
    }
}

pub proof fn lemma_nat_to_string_view_injective(a: nat, b: nat)
    requires
        nat_to_string_view(a) == nat_to_string_view(b),
    ensures
        a == b,
    decreases a + b,
{
    lemma_nat_to_string_view_props(a);
    lemma_nat_to_string_view_props(b);
    if a < 10 && b < 10 {
        assert(nat_to_string_view(a)[0] == nat_to_string_view(b)[0]);
        lemma_digit_to_char_injective(a as int, b as int);
    } else if a >= 10 && b >= 10 {
        let sa = nat_to_string_view((a / 10) as nat);
        let sb = nat_to_string_view((b / 10) as nat);
        assert(nat_to_string_view(a).last() == digit_to_char((a % 10) as int));
        assert(nat_to_string_view(b).last() == digit_to_char((b % 10) as int));
        lemma_digit_to_char_injective((a % 10) as int, (b % 10) as int);
        assert(nat_to_string_view(a).drop_last() =~= sa);
        assert(nat_to_string_view(b).drop_last() =~= sb);
        lemma_nat_to_string_view_injective((a / 10) as nat, (b / 10) as nat);
    }
}

pub proof fn lemma_int_to_string_view_injective(i: int, j: int)
    requires
        int_to_string_view(i) == int_to_string_view(j),
    ensures
        i == j,
{
    if i >= 0 && j >= 0 {
        lemma_nat_to_string_view_injective(i as nat, j as nat);
    } else if i < 0 && j < 0 {
        let si = nat_to_string_view((-i) as nat);
        let sj = nat_to_string_view((-j) as nat);
        assert(int_to_string_view(i).drop_first() =~= si);
        assert(int_to_string_view(j).drop_first() =~= sj);
        lemma_nat_to_string_view_injective((-i) as nat, (-j) as nat);
    } else if i >= 0 {
        lemma_nat_to_string_view_props(i as nat);
        assert(int_to_string_view(j)[0] == '-');
        assert(48u8 <= (int_to_string_view(i)[0] as u8) <= 57u8);
    } else {
        lemma_nat_to_string_view_props(j as nat);
        assert(int_to_string_view(i)[0] == '-');
        assert(48u8 <= (int_to_string_view(j)[0] as u8) <= 57u8);
    }
}

pub proof fn lemma_decimal_bytes_positive(b: Seq<u8>)
    requires
        is_canonical_decimal_bytes(b),
        b.len() >= 2,
    ensures
        decimal_bytes_val(b) >= 10,
    decreases b.len(),
{
    if b.len() == 2 {
        assert(b.drop_last() =~= seq![b[0]]);
        assert(b.drop_last().drop_last() =~= Seq::<u8>::empty());
        assert(49u8 <= b[0] <= 57u8);
        assert(48u8 <= b[1] <= 57u8);
        reveal_with_fuel(decimal_bytes_val, 2);
        assert(decimal_bytes_val(b.drop_last()) == (b[0] - 48) as nat);
    } else {
        assert(is_canonical_decimal_bytes(b.drop_last())) by {
            assert(b.drop_last()[0] == b[0]);
            assert forall |i: int| 0 <= i < b.drop_last().len()
                implies 48u8 <= (#[trigger] b.drop_last()[i]) <= 57u8 by {
                assert(b.drop_last()[i] == b[i]);
            };
        };
        lemma_decimal_bytes_positive(b.drop_last());
        assert(48u8 <= b[b.len() - 1] <= 57u8);
    }
}

// The value of a prefix of a sequence of digits is at most the value of the whole sequence.
pub proof fn lemma_decimal_bytes_val_take_le(b: Seq<u8>, k: int)
    requires
        0 <= k <= b.len(),
        forall |i: int| 0 <= i < b.len() ==> 48u8 <= (#[trigger] b[i]) <= 57u8,
    ensures
        decimal_bytes_val(b.take(k)) <= decimal_bytes_val(b),
    decreases b.len(),
{
    if k == b.len() {
        assert(b.take(k) =~= b);
    } else {
        assert(b.drop_last().take(k) =~= b.take(k));
        assert forall |i: int| 0 <= i < b.drop_last().len()
            implies 48u8 <= (#[trigger] b.drop_last()[i]) <= 57u8 by {
            assert(b.drop_last()[i] == b[i]);
        };
        lemma_decimal_bytes_val_take_le(b.drop_last(), k);
        assert(48u8 <= b.last() <= 57u8);
    }
}

// A sequence of ASCII characters whose bytes are a canonical decimal is the representation of
// the value of those bytes.
pub proof fn lemma_canonical_bytes_to_nat_str(s: Seq<char>, b: Seq<u8>)
    requires
        is_ascii_chars(s),
        b =~= Seq::new(s.len(), |i: int| s[i] as u8),
        is_canonical_decimal_bytes(b),
    ensures
        s =~= nat_to_string_view(decimal_bytes_val(b)),
    decreases b.len(),
{
    let v = decimal_bytes_val(b);
    assert(48u8 <= b[b.len() - 1] <= 57u8);
    let d = (b.last() - 48) as int;
    lemma_digit_to_char_props(d);
    assert('\0' <= s.last() <= '\u{7f}');
    assert((digit_to_char(d) as u32) == (s.last() as u32));
    if b.len() == 1 {
        assert(b.drop_last() =~= Seq::<u8>::empty());
        reveal_with_fuel(decimal_bytes_val, 2);
        assert(v == d as nat);
        assert(s =~= seq![s.last()]);
    } else {
        assert(is_canonical_decimal_bytes(b.drop_last())) by {
            assert(b.drop_last()[0] == b[0]);
            assert forall |i: int| 0 <= i < b.drop_last().len()
                implies 48u8 <= (#[trigger] b.drop_last()[i]) <= 57u8 by {
                assert(b.drop_last()[i] == b[i]);
            };
        };
        assert(is_ascii_chars(s.drop_last())) by {
            assert forall |i: int| 0 <= i < s.drop_last().len()
                implies '\0' <= #[trigger] s.drop_last()[i] <= '\u{7f}' by {
                assert(s.drop_last()[i] == s[i]);
            };
        };
        lemma_decimal_bytes_positive(b);
        let q = decimal_bytes_val(b.drop_last());
        assert((v / 10) as nat == q);
        assert((v % 10) as int == d);
        lemma_canonical_bytes_to_nat_str(s.drop_last(), b.drop_last());
        assert(s.drop_last().push(s.last()) =~= s);
    }
}

// The bytes of the representation of n are a canonical decimal of value n.
pub proof fn lemma_nat_str_to_canonical_bytes(n: nat)
    ensures ({
        let s = nat_to_string_view(n);
        let b = Seq::new(s.len(), |i: int| s[i] as u8);
        &&& is_canonical_decimal_bytes(b)
        &&& decimal_bytes_val(b) == n
    }),
    decreases n,
{
    lemma_nat_to_string_view_props(n);
    let s = nat_to_string_view(n);
    let b = Seq::new(s.len(), |i: int| s[i] as u8);
    if n < 10 {
        lemma_digit_to_char_props(n as int);
        assert(b.drop_last() =~= Seq::<u8>::empty());
        reveal_with_fuel(decimal_bytes_val, 2);
        assert(b.last() == (48 + n) as u8);
    } else {
        let q = (n / 10) as nat;
        let r = (n % 10) as int;
        lemma_nat_str_to_canonical_bytes(q);
        lemma_digit_to_char_props(r);
        let sq = nat_to_string_view(q);
        let bq = Seq::new(sq.len(), |i: int| sq[i] as u8);
        assert(b.drop_last() =~= bq);
        assert(b.last() == (48 + r) as u8);
        assert(b[0] == (s[0] as u8));
        assert(s[0] != '0');
        assert('\0' <= s[0] <= '\u{7f}');
        assert(b[0] != 48u8);
        assert forall |i: int| 0 <= i < b.len() implies 48u8 <= (#[trigger] b[i]) <= 57u8 by {
            assert(b[i] == (s[i] as u8));
        };
    }
}

// A canonical decimal of fewer digits has a smaller value.
pub proof fn lemma_decimal_bytes_len_lt(b1: Seq<u8>, b2: Seq<u8>)
    requires
        is_canonical_decimal_bytes(b1),
        is_canonical_decimal_bytes(b2),
        b1.len() < b2.len(),
    ensures
        decimal_bytes_val(b1) < decimal_bytes_val(b2),
    decreases b1.len() + b2.len(),
{
    if b1.len() == 1 {
        assert(b1.drop_last() =~= Seq::<u8>::empty());
        assert(48u8 <= b1[0] <= 57u8);
        reveal_with_fuel(decimal_bytes_val, 2);
        assert(decimal_bytes_val(b1) < 10);
        lemma_decimal_bytes_positive(b2);
    } else {
        assert(is_canonical_decimal_bytes(b1.drop_last())) by {
            assert(b1.drop_last()[0] == b1[0]);
            assert forall |i: int| 0 <= i < b1.drop_last().len()
                implies 48u8 <= (#[trigger] b1.drop_last()[i]) <= 57u8 by {
                assert(b1.drop_last()[i] == b1[i]);
            };
        };
        assert(is_canonical_decimal_bytes(b2.drop_last())) by {
            assert(b2.drop_last()[0] == b2[0]);
            assert forall |i: int| 0 <= i < b2.drop_last().len()
                implies 48u8 <= (#[trigger] b2.drop_last()[i]) <= 57u8 by {
                assert(b2.drop_last()[i] == b2[i]);
            };
        };
        lemma_decimal_bytes_len_lt(b1.drop_last(), b2.drop_last());
        assert(48u8 <= b1.last() <= 57u8);
        assert(48u8 <= b2.last() <= 57u8);
    }
}

// Of two decimals of the same length, the one with the smaller first differing digit is smaller.
pub proof fn lemma_decimal_bytes_same_len_lt(b1: Seq<u8>, b2: Seq<u8>, k: int)
    requires
        b1.len() == b2.len(),
        0 <= k < b1.len(),
        forall |i: int| 0 <= i < b1.len() ==> 48u8 <= (#[trigger] b1[i]) <= 57u8,
        forall |i: int| 0 <= i < b2.len() ==> 48u8 <= (#[trigger] b2[i]) <= 57u8,
        forall |i: int| 0 <= i < k ==> b1[i] == b2[i],
        b1[k] < b2[k],
    ensures
        decimal_bytes_val(b1) < decimal_bytes_val(b2),
    decreases b1.len(),
{
    assert(48u8 <= b1.last() <= 57u8);
    assert(48u8 <= b2.last() <= 57u8);
    if k == b1.len() - 1 {
        assert(b1.drop_last() =~= b2.drop_last());
    } else {
        assert forall |i: int| 0 <= i < b1.drop_last().len()
            implies 48u8 <= (#[trigger] b1.drop_last()[i]) <= 57u8 by {
            assert(b1.drop_last()[i] == b1[i]);
        };
        assert forall |i: int| 0 <= i < b2.drop_last().len()
            implies 48u8 <= (#[trigger] b2.drop_last()[i]) <= 57u8 by {
            assert(b2.drop_last()[i] == b2[i]);
        };
        assert forall |i: int| 0 <= i < k implies b1.drop_last()[i] == b2.drop_last()[i] by {
            assert(b1.drop_last()[i] == b1[i]);
            assert(b2.drop_last()[i] == b2[i]);
        };
        assert(b1.drop_last()[k] == b1[k]);
        assert(b2.drop_last()[k] == b2[k]);
        lemma_decimal_bytes_same_len_lt(b1.drop_last(), b2.drop_last(), k);
    }
}

#[verifier(external_body)]
pub fn bool_to_string(b: bool) -> (s: String)
    ensures s@ == bool_to_string_view(b),
{
    b.to_string()
}

pub open spec fn bool_to_string_view(b: bool) -> StringView {
    if b { "true"@ } else { "false"@ }
}

pub proof fn bool_to_string_view_injectivity()
    ensures forall |i: bool, j: bool| bool_to_string_view(i) == bool_to_string_view(j) ==> i == j,
{
    reveal_strlit("true");
    reveal_strlit("false");
    assert("true"@.len() != "false"@.len());
}

pub open spec fn opt_string_to_view(s: &Option<String>) -> Option<StringView> {
    match s {
        Some(s1) => Some(s1@),
        None => None,
    }
}

pub open spec fn starts_with_spec(s: StringView, prefix: StringView) -> bool {
    exists |suffix: StringView| s == prefix + suffix
}

pub open spec fn dash_free(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> s[i] != '-'@
}

#[verifier(external_body)]
pub fn dash_free_exec(s: &String) -> (res: bool)
    ensures res == dash_free(s@)
{
    !s.as_str().contains("-")
}

pub proof fn dash_char_view_eq_str_view()
    ensures "-"@ == seq!['-'@],
{
    reveal_strlit("-");
    assert("-"@ =~= seq!['-'@]);
}

pub proof fn lemma_dash_free_prefix_preserves_suffix_inequality(
    a1: Seq<char>, a2: Seq<char>, b1: Seq<char>, b2: Seq<char>,
)
requires
    dash_free(a1),
    dash_free(a2),
    b1 != b2,
ensures
    a1 + "-"@ + b1 != a2 + "-"@ + b2
{
    let lhs = a1 + "-"@ + b1;
    let rhs = a2 + "-"@ + b2;
    dash_char_view_eq_str_view();
    if a1 != a2 {
        if a1.len() == a2.len() {
            if forall |i: int| 0 <= i < a1.len() ==> a1[i] == a2[i] {
                assert(a1 == a2);
                assert(false);
            }
            let witness_idx = choose |i: int| 0 <= i < a1.len() && a1[i] != a2[i];
            assert(lhs[witness_idx] != rhs[witness_idx]);
        } else if a1.len() < a2.len() {
            let witness_idx = a1.len() as int;
            assert(lhs[witness_idx] == '-'@);
            assert(rhs[witness_idx] != '-'@);
        } else {
            let witness_idx = a2.len() as int;
            assert(lhs[witness_idx] != '-'@);
            assert(rhs[witness_idx] == '-'@);
        }
    } else {
        seq_equal_preserved_by_add(a1, a2, "-"@);
        seq_unequal_preserved_by_add_prefix(a1 + "-"@, b1, b2);
    }
}

pub proof fn lemma_dash_free_suffix_preserves_prefix_inequality(
    a1: Seq<char>, a2: Seq<char>, b1: Seq<char>, b2: Seq<char>,
)
requires
    dash_free(b1),
    dash_free(b2),
    a1 != a2,
ensures
    a1 + "-"@ + b1 != a2 + "-"@ + b2
{
    let lhs = a1 + "-"@ + b1;
    let rhs = a2 + "-"@ + b2;
    dash_char_view_eq_str_view();
    if lhs == rhs {
        assert(lhs.len() == rhs.len());
        assert(a1.len() + b1.len() + 1 == a2.len() + b2.len() + 1);
        if a1.len() == a2.len() {
            if forall |i: int| 0 <= i < a1.len() ==> a1[i] == a2[i] {
                assert(a1 == a2);
                assert(false);
            }
            let witness_idx = choose |i: int| 0 <= i < a1.len() && a1[i] != a2[i];
            assert(lhs[witness_idx] != rhs[witness_idx]);
        } else if a1.len() < a2.len() {
            let witness_idx = a2.len() as int;
            assert(rhs[witness_idx] == '-'@);
            assert(lhs[witness_idx] == b1[witness_idx - a1.len() - 1]);
            assert(lhs[witness_idx] != '-'@);
        } else {
            let witness_idx = a1.len() as int;
            assert(lhs[witness_idx] == '-'@);
            assert(rhs[witness_idx] == b2[witness_idx - a2.len() - 1]);
            assert(rhs[witness_idx] != '-'@);
        }
    }
}

// const string assumptions

pub proof fn vrs_prefix_equality()
    ensures "vreplicaset-"@ == "vreplicaset"@ + "-"@
{
    reveal_strlit("vreplicaset-");
    reveal_strlit("vreplicaset");
    reveal_strlit("-");
    assert("vreplicaset-"@ =~= "vreplicaset"@ + "-"@);
}

pub proof fn vrs_vsts_str_neq()
    ensures
        "vreplicaset"@.len() < "vstatefulset"@.len(),
        "vstatefulset"@.take("vreplicaset"@.len() as int) != "vreplicaset"@,
{
    reveal_strlit("vreplicaset");
    reveal_strlit("vstatefulset");
    assert("vstatefulset"@.take("vreplicaset"@.len() as int)[1] != "vreplicaset"@[1]);
}

}