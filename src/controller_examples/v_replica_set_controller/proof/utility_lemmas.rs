// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, prelude::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::proof::controller_runtime::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::defs::*;
use crate::v_replica_set_controller::model::{reconciler::*};
use crate::v_replica_set_controller::trusted::{
    liveness_theorem::*, spec_types::*, step::*,
};
use crate::v_replica_set_controller::proof::{
    predicate::*,
};
use vstd::{prelude::*, math::abs};

verus! {

#[verifier(external_body)]
pub proof fn lemma_filtered_pods_set_equals_matching_pods(
    s: VRSCluster, vrs: VReplicaSetView, resp_msg: VRSMessage
)
    ensures
        ({
            let objs = resp_msg.content.get_list_response().res.unwrap();
            let pods_or_none = objects_to_pods(objs);
            let pods = pods_or_none.unwrap();
            let filtered_pods = filter_pods(pods, vrs);
            &&& filtered_pods.no_duplicates()
            &&& filtered_pods.len() == matching_pod_entries(vrs, s.resources()).len()
            &&& filtered_pods.map_values(|p: PodView| p.marshal()).to_set() == matching_pod_entries(vrs, s.resources()).values()
        }),
{}
//
// TODO: Prove this.
//
// filter_pods filters pods in a very similar way to matching_pods, but the former
// works on a sequence of PodViews, while the latter works on the key-value store directly.
// I need to do some manual effort to make the two representations work together.
//
// Once proven, this will supplant the earlier lemma
// lemma_filtered_pods_len_equals_matching_pods_len.
//

}
