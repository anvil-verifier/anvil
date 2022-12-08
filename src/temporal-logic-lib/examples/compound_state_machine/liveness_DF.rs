// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::{
    common::*,
    controller, distributed_system,
    distributed_system::{message_sent, next, resource_exists, sm_spec, State},
    kubernetes_api_liveness,
    safety::*,
};
use crate::pervasive::option::*;
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn liveness_property(cr: ResourceObj) -> TempPred<State>
    recommends
        cr.key.kind.is_CustomResourceKind(),
{
    let cr_name = cr.key.name;
    let sts_name = cr_name + sts_suffix();
    let pod_name = sts_name + pod_suffix();
    let vol_name = sts_name + vol_suffix();

    always(lift_state(resource_exists(cr.key)))
    .leads_to(always(lift_state(
        |s: State| {
            &&& resource_exists(ResourceKey{name: pod_name, kind: ResourceKind::PodKind})(s)
            &&& resource_exists(ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind})(s)
        }
    )))
}

proof fn liveness_proof_for_all_cr()
    ensures
        forall |cr: ResourceObj| cr.key.kind.is_CustomResourceKind()
          ==> sm_spec().entails(#[trigger] liveness_property(cr)),
{
    assert forall |cr: ResourceObj| cr.key.kind.is_CustomResourceKind()
    implies sm_spec().entails(#[trigger] liveness_property(cr)) by {
        liveness_proof(cr);
    };
}

proof fn liveness_proof(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(liveness_property(cr)),
{
    let cr_name = cr.key.name;
    let sts_name = cr_name + sts_suffix();
    let pod_name = sts_name + pod_suffix();
    let vol_name = sts_name + vol_suffix();
    let assumption = |s| {
        &&& !message_sent(delete_req_msg(ResourceKey{name: pod_name, kind: ResourceKind::PodKind}))(s)
        &&& !message_sent(delete_req_msg(ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind}))(s)
    };
    let cr_exists = resource_exists(cr.key);
    let pod_exists = resource_exists(ResourceKey{name: pod_name, kind: ResourceKind::PodKind});
    let vol_exists = resource_exists(ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind});

    // F:
    assert(forall |s, s_prime: State| pod_exists(s) && #[trigger] action_pred_call(next(), s, s_prime) && assumption(s) ==> pod_exists(s_prime));
    assert(forall |s, s_prime: State| vol_exists(s) && #[trigger] action_pred_call(next(), s, s_prime) && assumption(s) ==> vol_exists(s_prime));
    lemma_cr_exists_leads_to_pod_exists_and_vol_exists(cr);
    lemma_always_cr_always_exists_implies_sub_resources_never_deleted(cr);

    // temporal:
    leads_to_weaken_auto::<State>(sm_spec());
    leads_to_stable_assume_p_combine::<State>(sm_spec(), next(), assumption, resource_exists(cr.key), pod_exists, vol_exists);
    implies_preserved_by_always_temp::<State>(
        lift_state(resource_exists(ResourceKey{name: pod_name, kind: ResourceKind::PodKind}))
            .and(lift_state(resource_exists(ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind}))),
        lift_state(
            |s: State| {
                &&& resource_exists(ResourceKey{name: pod_name, kind: ResourceKind::PodKind})(s)
                &&& resource_exists(ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind})(s)
            }
        )
    );
}

proof fn lemma_cr_exists_leads_to_pod_exists_and_vol_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(resource_exists(cr.key))
                .leads_to(lift_state(resource_exists(ResourceKey{name: cr.key.name + sts_suffix() + pod_suffix(), kind: ResourceKind::PodKind})))
        ),
        sm_spec().entails(
            lift_state(resource_exists(cr.key))
                .leads_to(lift_state(resource_exists(ResourceKey{name: cr.key.name + sts_suffix() + vol_suffix(), kind: ResourceKind::VolumeKind})))
        ),
{
    let cr_name = cr.key.name;
    let sts_name = cr_name + sts_suffix();


    lemma_always_res_exists_implies_create_req_sent(cr);

    kubernetes_api_liveness::lemma_create_req_leads_to_create_resp(create_req_msg(cr.key));
    lemma_controller_create_cr_resp_leads_to_create_sts_req(create_resp_msg(cr.key));
    kubernetes_api_liveness::lemma_create_sts_req_sent_leads_to_pod_exists_and_vol_exists(create_req_msg(ResourceKey{name: sts_name, kind: ResourceKind::StatefulSetKind}));

    // temporal:
    leads_to_trans_auto::<State>(sm_spec());
    leads_to_weaken_auto::<State>(sm_spec());
}

proof fn lemma_always_cr_always_exists_implies_sub_resources_never_deleted(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            always(
                always(lift_state(resource_exists(cr.key)))
                .implies(always(lift_state(|s| {
                    &&& !message_sent(delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + pod_suffix(), kind: ResourceKind::PodKind}))(s)
                    &&& !message_sent(delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + vol_suffix(), kind: ResourceKind::VolumeKind}))(s)
                })))
            )
        ),
{
    kubernetes_api_liveness::lemma_delete_req_leads_to_res_not_exists(delete_req_msg(cr.key));
    lemma_always_delete_cr_req_never_sent_implies_sub_resources_never_deleted(cr);

    // temporal:
    leads_to_contraposition::<State>(sm_spec(),
        message_sent(delete_req_msg(cr.key)),
        |s| !resource_exists(cr.key)(s),
    );
    always_implies_preserved_by_always::<State>(sm_spec(),
        |s| !message_sent(delete_req_msg(cr.key))(s),
        |s| {
            &&& !message_sent(delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + pod_suffix(), kind: ResourceKind::PodKind}))(s)
            &&& !message_sent(delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + vol_suffix(), kind: ResourceKind::VolumeKind}))(s)
        }
    );

    implies_preserved_by_always_auto::<State>();
    always_implies_weaken_auto::<State>(sm_spec());
}

proof fn lemma_always_delete_cr_req_never_sent_implies_sub_resources_never_deleted(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(always(
            lift_state(|s| !message_sent(delete_req_msg(cr.key))(s))
                .implies(lift_state(|s| {
                    &&& !message_sent(delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + pod_suffix(), kind: ResourceKind::PodKind}))(s)
                    &&& !message_sent(delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + vol_suffix(), kind: ResourceKind::VolumeKind}))(s)
                }))
        )),
{
    let delete_cr_req_msg = delete_req_msg(cr.key);
    let delete_cr_resp_msg = delete_resp_msg(cr.key);
    let delete_sts_req_msg = delete_req_msg(ResourceKey{
        name: cr.key.name + sts_suffix(),
        kind: ResourceKind::StatefulSetKind,
    });
    lemma_always_delete_req_not_sent_implies_delete_resp_not_sent(delete_cr_req_msg);
    lemma_always_delete_cr_resp_not_sent_implies_delete_sts_req_not_sent(delete_cr_resp_msg);
    lemma_always_delete_sts_req_not_sent_implies_delete_pod_and_vol_req_not_sent(delete_sts_req_msg);

    // temporal:
    always_implies_trans_auto::<State>(sm_spec());
}

proof fn lemma_controller_create_cr_resp_leads_to_create_sts_req(msg: Message)
    requires
        msg.is_CreateResponse(),
        msg.get_CreateResponse_0().obj.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(lift_state(message_sent(msg)).leads_to(lift_state(message_sent(create_req_msg(ResourceKey{
            name: msg.get_CreateResponse_0().obj.key.name + sts_suffix(),
            kind: ResourceKind::StatefulSetKind,
        }))))),
{
    let recv = Option::Some(msg);
    let pre = distributed_system::controller_action_pre(controller::send_create_sts(), recv);
    let post = message_sent(create_req_msg(ResourceKey{
        name: msg.get_CreateResponse_0().obj.key.name + sts_suffix(),
        kind: ResourceKind::StatefulSetKind
    }));

    // F:
    assert(forall |s, s_prime: State| distributed_system::controller_next().pre(recv)(s) && action_pred_call(next(), s, s_prime) ==> distributed_system::controller_next().pre(recv)(s_prime) || post(s_prime));
    assert(forall |s, s_prime: State| distributed_system::controller_next().pre(recv)(s) && action_pred_call(next(), s, s_prime) && distributed_system::controller_next().forward(recv)(s, s_prime) ==> post(s_prime));
    distributed_system::controller_action_pre_implies_next_pre(controller::send_create_sts(), recv);

    // temporal:
    leads_to_weaken_auto::<State>(sm_spec());
    use_tla_forall::<State, Option<Message>>(sm_spec(), |r| distributed_system::controller_next().weak_fairness(r), recv);
    distributed_system::controller_next().wf1(recv, sm_spec(), next(), post);
    assert(sm_spec().entails(lift_state(pre).leads_to(lift_state(post))));
}

}
