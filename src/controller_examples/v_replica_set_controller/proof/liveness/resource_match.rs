// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use crate::v_replica_set_controller::{
    model::{reconciler::*},
    proof::{helper_invariants, predicate::*},
    trusted::{spec_types::*, step::*, liveness_theorem::*},
};
use vstd::{prelude::*, string::*, math::abs};

verus! {

pub proof fn lemma_from_diff_and_init_to_current_state_matches(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int,
)
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(lift_state(current_state_matches(vrs)))
        )
{
    // Deal with transition from init to pod listings.
    lemma_from_init_step_to_send_list_pods_req(spec, vrs, diff);
    lemma_from_after_send_list_pods_req_to_recieve_list_pods_resp(spec, vrs, diff);

    // TODO: Would an invariant be a better way of showing 
    // num_diff_pods_is is maintained across this introductory step?
    leads_to_trans_n!(
        spec, 
        lift_state(
            |s: VRSCluster| {
                &&& at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
                &&& num_diff_pods_is(vrs, diff)(s)
            }
        ),
        lift_state(
            |s: VRSCluster| {
                &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
                &&& num_diff_pods_is(vrs, diff)(s)
            }
        ),
        lift_state(
            |s: VRSCluster| {
                &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
                &&& num_diff_pods_is(vrs, diff)(s)
            }
        )
    );

    let list_resp_msg = |resp_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
            &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, resp_msg)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_resp = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Dispatch by difference.
    if diff < 0 {
        // // Predicates specific to creating pods.
        // let create_req_msg = |req_msg: VRSMessage, diff: int| lift_state(|s: VRSCluster| {
        //     &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, req_msg, (abs(diff) - 1) as nat)(s)
        //     &&& num_diff_pods_is(vrs, diff)(s)
        // });
        // let create_req = |diff: int| lift_state(
        //     |s: VRSCluster| {
        //         &&& pending_req_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
        //         &&& num_diff_pods_is(vrs, diff)(s)
        //     }
        // );
        // let create_resp_msg = |resp_msg: VRSMessage, diff: int| lift_state(
        //     |s: VRSCluster| {
        //         &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, resp_msg, abs(diff))(s)
        //         &&& num_diff_pods_is(vrs, diff)(s)
        //     }
        // );
        // let create_resp = |diff: int| lift_state(
        //     |s: VRSCluster| {
        //         &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, abs(diff))(s)
        //         &&& num_diff_pods_is(vrs, diff)(s)
        //     }
        // )

        // // Try creating a pod starting in the AfterListPods step.
        // assert forall |resp_msg: VRSMessage| 
        //             #[trigger] spec.entails(
        // // lemma_from_after_recieve_list_pods_resp_to_send_create_pod_req(
        // //     spec, vrs, resp_msg, diff
        // // );
        // // lemma_from_after_send_create_pod_req_to_recieve_ok_resp(
        // //     spec, vrs, resp_msg, diff
        // // );
        // //leads_to_trans_n!(spec, )

        assume(false);
    } else if diff > 0 {
        assume(false);
    } else {
        // diff = 0
        // Use p ~> q, weakening of q => q'.
        leads_to_weaken_temp(
            spec,
            lift_state(
                |s: VRSCluster| {
                    &&& at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ),
            lift_state(
                |s: VRSCluster| {
                    &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ),
            lift_state(
                |s: VRSCluster| {
                    &&& at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ),
            lift_state(current_state_matches(vrs))
        );
    }
}

#[verifier(external_body)]
pub proof fn lemma_from_init_step_to_send_list_pods_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        )
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_send_list_pods_req_to_recieve_list_pods_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        )
{
}

// If there are too few pods, these lemmas apply.
#[verifier(external_body)]
pub proof fn lemma_from_after_recieve_list_pods_resp_to_send_create_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, resp_msg)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& pending_req_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_send_create_pod_req_to_recieve_ok_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, req_msg: VRSMessage, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, req_msg, (abs(diff) - 1) as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff + 1)(s)
                    }
                )
            )
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_recieve_ok_resp_to_send_create_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, resp_msg, abs(diff))(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
}

// If there are too many pods, this lemma applies.
#[verifier(external_body)]
pub proof fn lemma_from_after_recieve_list_pods_resp_to_send_delete_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, resp_msg)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_send_delete_pod_req_to_recieve_ok_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, req_msg: VRSMessage, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, req_msg, (abs(diff) - 1) as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff - 1)(s)
                    }
                )
            )
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_recieve_ok_resp_to_send_delete_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, resp_msg, abs(diff))(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
}

}
