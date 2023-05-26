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
/// All these differences are intended to make it easy to prove a Kubernetes object
/// remains unchanged after "marshaling" and "unmarshaling".
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

/// This trait is used to marshal ghost Kubernetes object types to Value, and unmarshal them back
pub trait Marshalable: Sized {
    /// Marshal the object to a Value

    open spec fn marshal(self) -> Value;

    /// Unmarshal the object back from a Value

    open spec fn unmarshal(value: Value) -> Self;

    /// Check if the data integrity is preserved after marshaling and unmarshaling

    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal());
}

}
