// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::pervasive::{*, option::Option};
#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::apis::*;
#[allow(unused_imports)]
use crate::distributed_system::*;
#[allow(unused_imports)]
use crate::custom_controller_logic::*;

#[allow(unused_imports)]
use crate::kubernetes;
#[allow(unused_imports)]
use crate::controller;
#[allow(unused_imports)]
use crate::custom_controller_workload;

verus! {

spec fn safety(v: DSVariables) -> bool {
    v.kubernetes_variables.cluster_state.contains(configmap_2_key()) ==> v.kubernetes_variables.cluster_state.contains(configmap_1_key())
}

spec fn apiop_is_deletion(api_op: APIOp) -> bool {
    matches!(api_op, APIOp::Delete{..})
}

// XXX: Strong assumption
spec fn no_deletion_i1(v: DSVariables) -> bool {
    forall |packet: Packet| is_sent(v, packet) ==>
        match packet.message {
            Message::APIOpRequest(api_op_request) => !apiop_is_deletion(api_op_request.api_op),
            _ => true,
        }
}

// GCU = get/create/update message. That is, anything that isn't a delete
spec fn matches_valid_gcu_response(packet: Packet, key: ObjectKey) -> bool {
    match packet.message {
        Message::APIOpResponse(api_op_response) =>
            match api_op_response.api_op_request.api_op {
                APIOp::Get{object_key} => equal(object_key, key) && api_op_response.success,
                APIOp::Create{object_key, ..} => equal(object_key, key) && api_op_response.success,
                APIOp::Update{object_key, ..} => equal(object_key, key) && api_op_response.success,
                _ => false,
            },
        _ => false,
    }
}

// XXX: Not yet clear why this needs to be inline for the proof to go through.
#[verifier(inline)]
spec fn is_create_request_with_key(packet: Packet, key: ObjectKey) -> bool {
    matches!(packet.message,
        Message::APIOpRequest(APIOpRequest{api_op: APIOp::Create{object_key, ..}}) if equal(object_key, key))
}

// XXX: Not sure why we preclude the need for Create messages when it comes to CR types
spec fn object_exists_implies_creation_sent_i2(v: DSVariables) -> bool {
    forall |key :ObjectKey|
        (#[trigger] v.kubernetes_variables.cluster_state.contains(key))
        ==> exists |packet: Packet| #[trigger] is_sent(v, packet) && is_create_request_with_key(packet, key)
}

spec fn object_in_cache_implies_corresponding_response_received_i3(v: DSVariables) -> bool {
    forall |key: ObjectKey| v.controller_variables.state_cache.contains(key)
        ==> exists |packet: Packet| #[trigger] is_sent(v, packet) && matches_valid_gcu_response(packet, key)
}

spec fn gcu_response_implies_object_in_cluster_state_i4(v: DSVariables) -> bool {
    forall |key: ObjectKey|
        (exists |packet: Packet| #[trigger] is_sent(v, packet) && matches_valid_gcu_response(packet, key))
        ==> v.kubernetes_variables.cluster_state.contains(key)
}

spec fn cm2_creation_implies_cm1_existence_i5(v: DSVariables) -> bool {
    (exists |packet: Packet|
        is_sent(v, packet) && is_create_request_with_key(packet, configmap_2_key()))
    ==> v.kubernetes_variables.cluster_state.contains(configmap_1_key())
}

proof fn kubernetes_state_monotonicity(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        next(c, v, v_prime) && no_deletion_i1(v)
    ensures
       forall |key: ObjectKey| v.kubernetes_variables.cluster_state.contains(key)
        ==> v_prime.kubernetes_variables.cluster_state.contains(key) {
}

proof fn network_monotonicity(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        next(c, v, v_prime)
    ensures
        forall |packet: Packet| is_sent(v, packet) ==> is_sent(v_prime, packet) {
}

proof fn controller_cache_monotonicity(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        next(c, v, v_prime) && no_deletion_i1(v)
    ensures
        forall |key: ObjectKey| v.kubernetes_variables.cluster_state.contains(key)
            ==> v_prime.kubernetes_variables.cluster_state.contains(key) {
}

spec fn inv(c: DSConstants, v: DSVariables) -> bool {
    &&& c.well_formed()
    &&& v.well_formed(c)
    &&& no_deletion_i1(v)
    &&& object_exists_implies_creation_sent_i2(v)
    &&& object_in_cache_implies_corresponding_response_received_i3(v)
    &&& gcu_response_implies_object_in_cluster_state_i4(v)
    &&& cm2_creation_implies_cm1_existence_i5(v)
    &&& safety(v)
}

proof fn init_implies_inv(c: DSConstants, v: DSVariables)
    requires
        init(c, v)
    ensures
        inv(c, v) {
}

// XXX: This is actually a proof assumption that there are no deletes being issued ever
proof fn inv_preserves_i1(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v) && next(c, v, v_prime)
    ensures
        no_deletion_i1(v_prime) {
}

proof fn inv_preserves_i2(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v) && next(c, v, v_prime)
    ensures
        object_exists_implies_creation_sent_i2(v_prime) {
    assert
        forall |any_object_key: ObjectKey|
            (#[trigger] v_prime.kubernetes_variables.cluster_state.contains(any_object_key))
            ==> exists |packet: Packet|
                #[trigger] is_sent(v_prime, packet) && is_create_request_with_key(packet, any_object_key)
    by {
        network_monotonicity(c, v, v_prime);
        let bool = v.kubernetes_variables.cluster_state.contains(any_object_key);
    }
}

// This is a statement about the controller cache's monotonicity
proof fn inv_preserves_i3(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v) && next(c, v, v_prime)
    ensures
        object_in_cache_implies_corresponding_response_received_i3(v_prime) {
    assert
        // XXX: this is the body of object_in_cache_implies_corresponding_response_received_i3
        forall |any_object_key: ObjectKey| v_prime.controller_variables.state_cache.contains(any_object_key)
            ==> exists |packet: Packet|
                #[trigger] is_sent(v_prime, packet) && matches_valid_gcu_response(packet, any_object_key)
    by {
        network_monotonicity(c, v, v_prime);
        // XXX: not sure why adding the below statement makes the proof go through
        let bool = v.controller_variables.state_cache.contains(any_object_key);
    };
}

// gcu = get/create/update
proof fn inv_preserves_i4(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v) && next(c, v, v_prime)
    ensures
        gcu_response_implies_object_in_cluster_state_i4(v_prime) {
    kubernetes_state_monotonicity(c, v, v_prime);
}

proof fn inv_preserves_i5(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v) && next(c, v, v_prime)
    ensures
        cm2_creation_implies_cm1_existence_i5(v_prime) {
}

proof fn inv_preserves_safety(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v) && next(c, v, v_prime)
    ensures
        safety(v_prime) {
}

proof fn inv_inductive(c: DSConstants, v: DSVariables, v_prime: DSVariables) {
    requires(inv(c, v) && next(c, v, v_prime));
    ensures(inv(c, v_prime));
    inv_preserves_i1(c, v, v_prime);
    inv_preserves_i2(c, v, v_prime);
    inv_preserves_i3(c, v, v_prime);
    inv_preserves_i4(c, v, v_prime);
    inv_preserves_i5(c, v, v_prime);
    inv_preserves_safety(c, v, v_prime);
}

proof fn inv_implies_safety(c: DSConstants, v: DSVariables)
    requires
        inv(c, v)
    ensures
        safety(v) {
}

}