// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::predicate::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, error::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::{predicate::*, resource::*},
    spec::types::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

spec fn make_owner_references_with_name_and_uid(name: StringView, uid: Uid) -> OwnerReferenceView {
    OwnerReferenceView {
        block_owner_deletion: None,
        controller: Some(true),
        kind: RabbitmqClusterView::kind(),
        name: name,
        uid: uid,
    }
}

// pub proof fn lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
//     requires
//         spec.entails(lift_state(RMQCluster::init())),
//         spec.entails(always(lift_action(RMQCluster::next()))),
//     ensures
//         spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
// {
//     let inv = resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq);
//     lemma_always_resource_object_create_request_msg_is_valid(spec, rabbitmq.object_ref());
//     lemma_always_resource_object_update_request_msg_is_valid(spec, rabbitmq.object_ref());
//     let stronger_next = |s, s_prime| {
//         &&& RMQCluster::next()(s, s_prime)
//         &&& resource_object_update_request_msg_is_valid(rabbitmq.object_ref())(s)
//         &&& resource_object_create_request_msg_is_valid(rabbitmq.object_ref())(s)
//     };
//     combine_spec_entails_always_n!(
//         spec, lift_action(stronger_next),
//         lift_action(RMQCluster::next()),
//         lift_state(resource_object_update_request_msg_is_valid(rabbitmq.object_ref())),
//         lift_state(resource_object_create_request_msg_is_valid(rabbitmq.object_ref()))
//     );
//     init_invariant(spec, RMQCluster::init(), stronger_next, inv);
// }

// proof fn lemma_always_resource_object_create_request_msg_is_valid(spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
//     requires
//         key.kind.is_CustomResourceKind(),
//         spec.entails(lift_state(RMQCluster::init())),
//         spec.entails(always(lift_action(RMQCluster::next()))),
//     ensures
//         spec.entails(always(lift_state(resource_object_create_request_msg_is_valid(key)))),
// {
//     let stronger_next = |s, s_prime| {
//         &&& RMQCluster::next()(s, s_prime)
//         &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
//     };
//     RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
//     combine_spec_entails_always_n!(
//         spec, lift_action(stronger_next),
//         lift_action(RMQCluster::next()),
//         lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
//     );
//     assert forall |s, s_prime| resource_object_create_request_msg_is_valid(sub_resource, rabbitmq)(s) && #[trigger] stronger_next(s, s_prime) implies
//     resource_object_create_request_msg_is_valid(sub_resource, rabbitmq)(s_prime) by {
//         assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && resource_object_create_request_msg(key)(msg) implies
//         msg.content.get_create_request().obj.metadata.finalizers.is_None()
//         && exists |uid: Uid| #![auto] msg.content.get_create_request().obj.metadata.owner_references
//             == Some(seq![make_owner_references_with_name_and_uid(key.name, uid)]) by {
//             if !s.in_flight().contains(msg) {
//                 let step = choose |step| RMQCluster::next_step(s, s_prime, step);
//                 lemma_resource_object_create_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
//                 let cr = s.ongoing_reconciles()[key].triggering_cr;
//                 assert(cr.metadata.uid.is_Some());
//                 assert(msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
//                     make_owner_references_with_name_and_uid(key.name, cr.metadata.uid.get_Some_0())
//                 ]));
//             }
//         }
//     }
//     init_invariant(spec, RMQCluster::init(), stronger_next, resource_object_create_request_msg_is_valid(key));
// }

spec fn resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        forall |msg: RMQMessage| {
            #[trigger] s.in_flight().contains(msg) ==> {
                &&& resource_update_request_msg(resource_key)(msg)
                    ==> msg.content.get_update_request().obj.metadata.finalizers.is_None()
                        && exists |uid: Uid| #![auto]
                            msg.content.get_update_request().obj.metadata.owner_references == Some(seq![
                                make_owner_references_with_name_and_uid(key.name, uid)
                            ])
                &&& resource_create_request_msg(resource_key)(msg)
                    ==> msg.content.get_create_request().obj.metadata.finalizers.is_None()
                        && exists |uid: Uid| #![auto]
                            msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                                make_owner_references_with_name_and_uid(key.name, uid)
                            ])
            }
        }
    }
}

proof fn lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
        sub_resource == SubResource::StatefulSet,
    ensures
        spec.entails(always(lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, rabbitmq)))),
{
    let inv = resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, rabbitmq);
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    let create_msg_pred = |msg: RMQMessage| {
        resource_create_request_msg(resource_key)(msg)
        ==> msg.content.get_create_request().obj.metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
                msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(key.name, uid)
                ])
    };
    let update_msg_pred = |msg: RMQMessage| {
        resource_update_request_msg(resource_key)(msg)
        ==> msg.content.get_update_request().obj.metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
                msg.content.get_update_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(key.name, uid)
                ])
    };
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies update_msg_pred(msg) && create_msg_pred(msg) by {
            if !s.in_flight().contains(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, rabbitmq, s, s_prime, msg, step);
                let cr = s.ongoing_reconciles()[key].triggering_cr;
                if resource_create_request_msg(resource_key)(msg) {
                    assert(msg.content.get_create_request().obj == make(sub_resource, cr, s.ongoing_reconciles()[key].local_state).get_Ok_0());
                    assert(msg.content.get_create_request().obj.metadata.finalizers.is_None());
                    assert(msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                        make_owner_references_with_name_and_uid(key.name, cr.metadata.uid.get_Some_0())
                    ]));
                }
                if resource_update_request_msg(resource_key)(msg) {
                    assert(step.get_ControllerStep_0().0.get_Some_0().content.is_get_response());
                    assert(step.get_ControllerStep_0().0.get_Some_0().content.get_get_response().res.is_Ok());
                    assert(update(
                        sub_resource, cr, s.ongoing_reconciles()[key].local_state, step.get_ControllerStep_0().0.get_Some_0().content.get_get_response().res.get_Ok_0()
                    ).is_Ok());
                    assert(msg.content.get_update_request().obj == update(
                        sub_resource, cr, s.ongoing_reconciles()[key].local_state, step.get_ControllerStep_0().0.get_Some_0().content.get_get_response().res.get_Ok_0()
                    ).get_Ok_0());
                    assert(msg.content.get_update_request().obj.metadata.owner_references == Some(seq![
                        make_owner_references_with_name_and_uid(key.name, cr.metadata.uid.get_Some_0())
                    ]));
                }

            }
        }
    }
    init_invariant(spec, RMQCluster::init(), stronger_next, inv);
}

/// This lemma is used to show that if an action (which transfers the state from s to s_prime) creates a sub resource object
/// create/update request message (with key as key), it must be a controller action, and the triggering cr is s.ongoing_reconciles()[key].triggering_cr.
///
/// After the action, the controller stays at After(Create/Update, SubResource) step.
/// 
/// Talking about both s and s_prime give more information to those using this lemma and also makes the verification faster.
proof fn lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster, msg: RMQMessage, step: RMQStep
)
    requires
        rabbitmq.well_formed(),
        !s.in_flight().contains(msg), s_prime.in_flight().contains(msg),
        RMQCluster::next_step(s, s_prime, step),
        RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
    ensures
        resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == rabbitmq.object_ref()
            && at_rabbitmq_step(rabbitmq.object_ref(), RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
            && at_rabbitmq_step(rabbitmq.object_ref(), RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s_prime),
        resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == rabbitmq.object_ref()
            && at_rabbitmq_step(rabbitmq.object_ref(), RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
            && at_rabbitmq_step(rabbitmq.object_ref(), RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s_prime),
{
    // Since we know that this step creates a create server config map message, it is easy to see that it's a controller action.
    // This action creates a config map, and there are two kinds of config maps, we have to show that only server config map
    // is possible by extra reasoning about the strings.
    let cr_key = step.get_ControllerStep_0().1.get_Some_0();
    let key = rabbitmq.object_ref();
    let cr = s.ongoing_reconciles()[key].triggering_cr;
    let resource_key = get_request(sub_resource, rabbitmq).key;
    // It's easy for the verifier to know that cr_key has the same kind and namespace as key.
    match sub_resource {
        SubResource::ServerConfigMap => {
            // resource_create_request_msg(key)(msg) requires the msg has a key with name key.name "-server-conf". So we
            // first show that in this action, cr_key is only possible to add "-server-conf" rather than "-plugins-conf" to reach
            // such a post state.
            assert_by(
                cr_key.name + new_strlit("-plugins-conf")@ != key.name + new_strlit("-server-conf")@,
                {
                    let str1 = cr_key.name + new_strlit("-plugins-conf")@;
                    let str2 = key.name + new_strlit("-server-conf")@;
                    reveal_strlit("-server-conf");
                    reveal_strlit("-plugins-conf");
                    if str1.len() == str2.len() {
                        assert(str1[str1.len() - 6] == 's');
                        assert(str2[str1.len() - 6] == 'r');
                    }
                }
            );
            // Then we show that only if cr_key.name equals key.name, can this message be created in this step.
            seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-server-conf")@);
        },
        SubResource::PluginsConfigMap => {
            assert_by(
                key.name + new_strlit("-plugins-conf")@ != cr_key.name + new_strlit("-server-conf")@,
                {
                    let str1 = key.name + new_strlit("-plugins-conf")@;
                    let str2 = cr_key.name + new_strlit("-server-conf")@;
                    reveal_strlit("-server-conf");
                    reveal_strlit("-plugins-conf");
                    if str1.len() == str2.len() {
                        assert(str1[str1.len() - 6] == 's');
                        assert(str2[str1.len() - 6] == 'r');
                    }
                }
            );
            seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-plugins-conf")@);
        },
        SubResource::ErlangCookieSecret => {
            assert_by(
                cr_key.name + new_strlit("-default-user")@ != key.name + new_strlit("-erlang-cookie")@,
                {
                    let str1 = cr_key.name + new_strlit("-default-user")@;
                    let str2 = key.name + new_strlit("-erlang-cookie")@;
                    reveal_strlit("-erlang-cookie");
                    reveal_strlit("-default-user");
                    if str1.len() == str2.len() {
                        assert(str1[str1.len() - 1] == 'r');
                        assert(str2[str1.len() - 1] == 'e');
                    }
                }
            );
            // Then we show that only if cr_key.name equals key.name, can this message be created in this step.
            seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-erlang-cookie")@);
        },
        SubResource::DefaultUserSecret => {
            assert_by(
                key.name + new_strlit("-default-user")@ != cr_key.name + new_strlit("-erlang-cookie")@,
                {
                    let str1 = key.name + new_strlit("-default-user")@;
                    let str2 = cr_key.name + new_strlit("-erlang-cookie")@;
                    reveal_strlit("-erlang-cookie");
                    reveal_strlit("-default-user");
                    if str1.len() == str2.len() {
                        assert(str1[str1.len() - 1] == 'r');
                        assert(str2[str1.len() - 1] == 'e');
                    }
                }
            );
            seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-default-user")@);
        },
        SubResource::HeadlessService => {
            assert_by(
                key.name + new_strlit("-nodes")@ != cr_key.name + new_strlit("-client")@,
                {
                    let str1 = key.name + new_strlit("-nodes")@;
                    let str2 = cr_key.name + new_strlit("-client")@;
                    reveal_strlit("-client");
                    reveal_strlit("-nodes");
                    if str1.len() == str2.len() {
                        assert(str1[str1.len() - 1] == 's');
                        assert(str2[str1.len() - 1] == 't');
                    }
                }
            );
            seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-nodes")@);
        },
        SubResource::Service => {
            assert_by(
                cr_key.name + new_strlit("-nodes")@ != key.name + new_strlit("-client")@,
                {
                    let str1 = cr_key.name + new_strlit("-nodes")@;
                    let str2 = key.name + new_strlit("-client")@;
                    reveal_strlit("-client");
                    reveal_strlit("-nodes");
                    if str1.len() == str2.len() {
                        assert(str1[str1.len() - 1] == 's');
                        assert(str2[str1.len() - 1] == 't');
                    }
                }
            );
            seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-client")@);
        },
        SubResource::RoleBinding | SubResource::ServiceAccount | SubResource::StatefulSet => {
            seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-server")@);
        },
        SubResource::Role => {
            seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-peer-discovery")@);
        },
    }
}

}
