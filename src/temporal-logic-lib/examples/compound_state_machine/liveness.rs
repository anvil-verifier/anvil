// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::common::*;
use crate::examples::compound_state_machine::compound_state_machine::*;
use crate::examples::compound_state_machine::safety::*;
use crate::pervasive::{option::*, seq::*, set::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn liveness_property(cr: ResourceObj) -> TempPred<CompoundState>
    recommends
        cr.key.kind.is_CustomResourceKind(),
{
    let cr_name = cr.key.name;
    let sts_name = cr_name + sts_suffix();
    let pod_name = sts_name + pod_suffix();
    let vol_name = sts_name + vol_suffix();

    always(lift_state(resource_exists(cr.key)))
    .leads_to(always(lift_state(
        |s: CompoundState| {
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

    leads_to_weaken_auto::<CompoundState>(sm_spec());

    lemma_cr_exists_leads_to_pod_exists_and_vol_exists(cr);
    lemma_always_cr_always_exists_implies_sub_resources_never_deleted(cr);
    leads_to_stable_assume_p_combine::<CompoundState>(sm_spec(),
        next(),
        |s| {
            &&& !message_sent(delete_req_msg(ResourceKey{name: pod_name, kind: ResourceKind::PodKind}))(s)
            &&& !message_sent(delete_req_msg(ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind}))(s)
        },
        resource_exists(cr.key),
        resource_exists(ResourceKey{name: pod_name, kind: ResourceKind::PodKind}),
        resource_exists(ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind})
    );

    // We can also use the auto version, which takes more time in smt-run
    implies_preserved_by_always_temp::<CompoundState>(
        lift_state(resource_exists(ResourceKey{name: pod_name, kind: ResourceKind::PodKind}))
            .and(lift_state(resource_exists(ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind}))),
        lift_state(
            |s: CompoundState| {
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

    leads_to_trans_auto::<CompoundState>(sm_spec());
    leads_to_weaken_auto::<CompoundState>(sm_spec());

    lemma_always_res_exists_implies_create_req_sent(cr);

    lemma_k8s_create_cr_req_leads_to_create_cr_resp(create_req_msg(cr.key));
    lemma_controller_create_cr_resp_leads_to_create_sts_req(create_resp_msg(cr.key));
    lemma_k8s_create_sts_req_sent_leads_to_pod_exists_and_vol_exists(create_req_msg(ResourceKey{name: sts_name, kind: ResourceKind::StatefulSetKind}));
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
    lemma_k8s_delete_cr_req_leads_to_cr_not_exists(delete_req_msg(cr.key));
    leads_to_contradiction::<CompoundState>(sm_spec(),
        message_sent(delete_req_msg(cr.key)),
        |s| !resource_exists(cr.key)(s),
    );

    lemma_always_delete_cr_req_never_sent_implies_sub_resources_never_deleted(cr);
    always_implies_preserved_by_always::<CompoundState>(sm_spec(),
        |s| !message_sent(delete_req_msg(cr.key))(s),
        |s| {
            &&& !message_sent(delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + pod_suffix(), kind: ResourceKind::PodKind}))(s)
            &&& !message_sent(delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + vol_suffix(), kind: ResourceKind::VolumeKind}))(s)
        }
    );

    implies_preserved_by_always_auto::<CompoundState>();
    always_implies_weaken_auto::<CompoundState>(sm_spec());
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

    always_implies_trans_auto::<CompoundState>(sm_spec());
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
    let create_sts_req_msg = create_req_msg(ResourceKey{
        name: msg.get_CreateResponse_0().obj.key.name + sts_suffix(),
        kind: ResourceKind::StatefulSetKind
    });

    leads_to_eq_auto::<CompoundState>(sm_spec());
    use_tla_forall::<CompoundState, Option<Message>>(sm_spec(), |recv| weak_fairness(controller_action(recv)), Option::Some(msg));

    controller_action_send_create_sts_enabled(Option::Some(msg));

    wf1::<CompoundState>(sm_spec(),
        next(),
        controller_action(Option::Some(msg)),
        controller_action_send_create_sts_pre(Option::Some(msg)),
        message_sent(create_sts_req_msg),
    );
}

proof fn lemma_k8s_create_cr_req_leads_to_create_cr_resp(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().obj.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(message_sent(msg)).leads_to(lift_state(message_sent(create_resp_msg(msg.get_CreateRequest_0().obj.key))))
        ),
{
    let create_cr_resp_msg = create_resp_msg(msg.get_CreateRequest_0().obj.key);

    leads_to_eq_auto::<CompoundState>(sm_spec());
    use_tla_forall::<CompoundState, Option<Message>>(sm_spec(), |recv| weak_fairness(kubernetes_api_action(recv)), Option::Some(msg));

    kubernetes_api_action_handle_request_enabled(Option::Some(msg));
    wf1::<CompoundState>(sm_spec(),
        next(),
        kubernetes_api_action(Option::Some(msg)),
        kubernetes_api_action_handle_request_pre(Option::Some(msg)),
        message_sent(create_cr_resp_msg),
    );
}

proof fn lemma_k8s_delete_cr_req_leads_to_cr_not_exists(msg: Message)
    requires
        msg.is_DeleteRequest(),
        msg.get_DeleteRequest_0().key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(message_sent(msg)).leads_to(lift_state(|s| !resource_exists(msg.get_DeleteRequest_0().key)(s)))
        ),
{
    leads_to_eq_auto::<CompoundState>(sm_spec());
    use_tla_forall::<CompoundState, Option<Message>>(sm_spec(), |recv| weak_fairness(kubernetes_api_action(recv)), Option::Some(msg));

    kubernetes_api_action_handle_request_enabled(Option::Some(msg));
    wf1::<CompoundState>(sm_spec(),
        next(),
        kubernetes_api_action(Option::Some(msg)),
        kubernetes_api_action_handle_request_pre(Option::Some(msg)),
        |s| !resource_exists(msg.get_DeleteRequest_0().key)(s)
    );
}

proof fn lemma_k8s_create_sts_req_sent_leads_to_pod_exists_and_vol_exists(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().obj.key.kind.is_StatefulSetKind(),
    ensures
        sm_spec()
            .entails(lift_state(message_sent(msg))
                .leads_to(lift_state(resource_exists(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind})))),
        sm_spec()
            .entails(lift_state(message_sent(msg))
                .leads_to(lift_state(resource_exists(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind})))),
{
    lemma_k8s_create_sts_req_sent_leads_to(msg, create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind}));
    lemma_k8s_create_sts_req_sent_leads_to(msg, create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind}));
}

proof fn lemma_k8s_create_sts_req_sent_leads_to(msg: Message, sub_res_msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().obj.key.kind.is_StatefulSetKind(),
        sub_res_msg.is_CreateRequest(),
        sub_res_msg.get_CreateRequest_0().obj.key === (ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind})
        || sub_res_msg.get_CreateRequest_0().obj.key === (ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind}),
    ensures
        sm_spec()
            .entails(lift_state(message_sent(msg))
                .leads_to(lift_state(resource_exists(sub_res_msg.get_CreateRequest_0().obj.key)))),
{
    let sub_res_key = sub_res_msg.get_CreateRequest_0().obj.key;

    leads_to_eq_auto::<CompoundState>(sm_spec());
    use_tla_forall::<CompoundState, Option<Message>>(sm_spec(), |recv| weak_fairness(kubernetes_api_action(recv)), Option::Some(msg));
    use_tla_forall::<CompoundState, Option<Message>>(sm_spec(), |recv| weak_fairness(kubernetes_api_action(recv)), Option::Some(sub_res_msg));

    kubernetes_api_action_handle_request_enabled(Option::Some(msg));
    wf1::<CompoundState>(sm_spec(),
        next(),
        kubernetes_api_action(Option::Some(msg)),
        kubernetes_api_action_handle_request_pre(Option::Some(msg)),
        message_sent(sub_res_msg)
    );

    kubernetes_api_action_handle_request_enabled(Option::Some(sub_res_msg));
    wf1::<CompoundState>(sm_spec(),
        next(),
        kubernetes_api_action(Option::Some(sub_res_msg)),
        kubernetes_api_action_handle_request_pre(Option::Some(sub_res_msg)),
        resource_exists(sub_res_key)
    );

    leads_to_trans::<CompoundState>(sm_spec(),
        message_sent(msg),
        message_sent(sub_res_msg),
        resource_exists(sub_res_key)
    );
}

}
