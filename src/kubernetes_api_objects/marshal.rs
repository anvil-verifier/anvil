// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

/// Value is used to "serialize" whatever Kubernetes resource object to a DynamicObject.
/// It looks similar to serde_json::Value but there are two major differences:
/// - Value::Object carries a Map<nat, Value>, while serde_json::Value::Object carries a Map<String, Value>
/// - Value has more variants for map structures like StringStringMap
///
/// All these differences are intended to make it easy (trivial) to prove a Kubernetes object
/// remains unchanged after "serialization" and "deserialization".
/// For example:
///     forall |o: ConfigMapView| o == ConfigMapView::from_dynamic_object(o.to_dynamic_object())
///
/// To do so, we try to avoid using StringView (Seq<Char>) as the key of Object Map because
/// Verus cannot easily tell two StringViews are different unless we reveal them.

#[is_variant]
pub enum Value {
    Null,
    Bool(bool),
    Nat(nat),
    Int(int),
    String(StringView),
    Array(Seq<Value>),
    StringStringMap(Map<StringView, StringView>),
    Object(Map<nat, Value>),
}

}
