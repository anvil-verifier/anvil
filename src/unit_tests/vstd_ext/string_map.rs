// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[test]
#[verifier(external)]
pub fn test_extend() {
    let mut m = StringMap::empty();
    m.insert(new_strlit("key1").to_string(), new_strlit("val1").to_string());
    m.insert(new_strlit("key2").to_string(), new_strlit("val2").to_string());

    let mut m2 = StringMap::empty();
    m2.insert(new_strlit("key1").to_string(), new_strlit("new_val1").to_string());
    m2.insert(new_strlit("key3").to_string(), new_strlit("val3").to_string());

    m.extend(m2);

    let rust_map = m.into_rust_map();
    assert_eq!(rust_map.get(&"key1".to_string()), Some(&"new_val1".to_string()));
    assert_eq!(rust_map.get(&"key2".to_string()), Some(&"val2".to_string()));
    assert_eq!(rust_map.get(&"key3".to_string()), Some(&"val3".to_string()));
}

}
