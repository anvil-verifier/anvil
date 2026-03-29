#![allow(unused_imports)]
use super::predicate::*;
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*,
    label_selector::LabelSelectorView, volume_resource_requirements::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    message::*,
    api_server::state_machine::*,
};
use crate::rabbitmq_controller::{
    model::resource::*,
    proof::{predicate::*, resource::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::vstatefulset_controller::trusted::spec_types::{VStatefulSetView, StatefulSetPodNameLabel, StatefulSetOrdinalLabel};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

#[verifier(external_body)]
pub proof fn rmq_with_different_key_implies_request_with_different_key(rmq: RabbitmqClusterView, other_rmq: RabbitmqClusterView, sub_resource: SubResource)
requires
    rmq.object_ref() != other_rmq.object_ref()
ensures
    get_request(sub_resource, other_rmq).key != get_request(sub_resource, rmq).key,
{}

pub proof fn make_sts_pass_state_validation(rmq: RabbitmqClusterView, cm_rv: StringView) -> (sts: VStatefulSetView)
requires
    rmq.state_validation(),
ensures
    sts == make_stateful_set(rmq, cm_rv),
    sts.state_validation(),
{
    let sts = make_stateful_set(rmq, cm_rv);
    let name = rmq.metadata.name->0;
    let labels = Map::empty().insert("app"@, name);

    // selector.match_labels is Some and non-empty
    assert(labels.len() > 0) by {
        assert(labels.contains_key("app"@));
    };

    // selector matches template labels
    let template_labels = make_labels(rmq);
    assert forall |k: StringView, v: StringView| labels.contains_pair(k, v) implies template_labels.contains_pair(k, v) by {
    };

    // template labels don't contain StatefulSetPodNameLabel or StatefulSetOrdinalLabel
    // make_labels(rmq) = rmq.spec.labels.insert("app"@, name)
    reveal_strlit("app");
    reveal_strlit("statefulset.kubernetes.io/pod-name");
    reveal_strlit("apps.kubernetes.io/pod-index");
    assert(StatefulSetPodNameLabel == "statefulset.kubernetes.io/pod-name"@);
    assert(StatefulSetOrdinalLabel == "apps.kubernetes.io/pod-index"@);
    // From rmq.state_validation()
    assert(!rmq.spec.labels.contains_key(StatefulSetPodNameLabel));
    assert(!rmq.spec.labels.contains_key(StatefulSetOrdinalLabel));
    // "app" != StatefulSetPodNameLabel/StatefulSetOrdinalLabel (different lengths)
    assert("app"@.len() == 3);
    assert("statefulset.kubernetes.io/pod-name"@.len() > 3);
    assert("apps.kubernetes.io/pod-index"@.len() > 3);
    assert("app"@ != StatefulSetPodNameLabel);
    assert("app"@ != StatefulSetOrdinalLabel);
    // So insert("app", name) doesn't introduce those keys
    assert(!rmq.spec.labels.insert("app"@, name).contains_key(StatefulSetPodNameLabel));
    assert(!rmq.spec.labels.insert("app"@, name).contains_key(StatefulSetOrdinalLabel));

    // Volume claim templates validation
    if rmq.spec.persistence.storage != "0Gi"@ {
        reveal_strlit("persistence");
        assert(dash_free("persistence"@));
    }

    return sts;
}

#[verifier(external_body)]
pub proof fn update_sts_pass_state_validation(rmq: RabbitmqClusterView, found_sts: VStatefulSetView, cm_rv: StringView) -> (sts: VStatefulSetView)
requires
    rmq.state_validation(),
    found_sts.state_validation(),
    found_sts.metadata.owner_references_only_contains(rmq.controller_owner_ref()),
    found_sts.spec.selector == LabelSelectorView::default().with_match_labels(Map::empty().insert("app"@, rmq.metadata.name->0)),
ensures
    sts == update_stateful_set(rmq, found_sts, cm_rv),
    sts.state_validation(),
{
    return update_stateful_set(rmq, found_sts, cm_rv);
}

// shield_lemma
#[verifier(external_body)]
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
    s: ClusterState, s_prime: ClusterState, rmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rmq, sub_resource)(s),
    no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s),
    rmq_rely_conditions(cluster, controller_id)(s),
    msg.src != HostId::Controller(controller_id, rmq.object_ref()),
ensures
    s.resources().contains_key(get_request(sub_resource, rmq).key) == s_prime.resources().contains_key(get_request(sub_resource, rmq).key),
    s.resources()[get_request(sub_resource, rmq).key] == s_prime.resources()[get_request(sub_resource, rmq).key],
    // cm is not updated
    s.resources().contains_key(make_server_config_map_key(rmq)) == s_prime.resources().contains_key(make_server_config_map_key(rmq)),
    s.resources()[make_server_config_map_key(rmq)] == s_prime.resources()[make_server_config_map_key(rmq)],
{}

pub proof fn lemma_create_sub_resource_request_returns_ok(
    s: ClusterState, s_prime: ClusterState, rmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rmq, sub_resource)(s),
    req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rmq, controller_id, msg)(s),
ensures
    resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, rmq, controller_id, resp_msg)(s_prime),
    resource_state_matches(sub_resource, rmq)(s_prime),
{
    RabbitmqReconcileState::marshal_preserves_integrity();

    match sub_resource {
        SubResource::HeadlessService => {
            ServiceView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            ServiceView::marshal_preserves_integrity();
            ServiceView::marshal_status_preserves_integrity(); // marshalled default status can pass state validation
        },
        SubResource::Service => {
            ServiceView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            ServiceView::marshal_preserves_integrity();
            ServiceView::marshal_status_preserves_integrity();
        },
        SubResource::ErlangCookieSecret => {
            SecretView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            SecretView::marshal_preserves_integrity();
            SecretView::marshal_status_preserves_integrity();
        },
        SubResource::DefaultUserSecret => {
            SecretView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            SecretView::marshal_preserves_integrity();
            SecretView::marshal_status_preserves_integrity();
        },
        SubResource::PluginsConfigMap => {
            ConfigMapView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            ConfigMapView::marshal_preserves_integrity();
            ConfigMapView::marshal_status_preserves_integrity();
        },
        SubResource::ServerConfigMap => {
            ConfigMapView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            ConfigMapView::marshal_preserves_integrity();
            ConfigMapView::marshal_status_preserves_integrity();
        },
        SubResource::ServiceAccount => {
            ServiceAccountView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            ServiceAccountView::marshal_preserves_integrity();
            ServiceAccountView::marshal_status_preserves_integrity();
        },
        SubResource::Role => {
            RoleView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            RoleView::marshal_preserves_integrity();
            RoleView::marshal_status_preserves_integrity();
        },
        SubResource::RoleBinding => {
            RoleBindingView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            RoleBindingView::marshal_preserves_integrity();
            RoleBindingView::marshal_status_preserves_integrity();
        },
        SubResource::VStatefulSetView => {
            VStatefulSetView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            VStatefulSetView::marshal_preserves_integrity();
            VStatefulSetView::marshal_status_preserves_integrity();
        },
    }
    let resp_msg = handle_create_request_msg(cluster.installed_types, msg, s.api_server).1;
    assert(resp_msg.content.get_create_response().res is Ok);
    let local_state = s_prime.ongoing_reconciles(controller_id)[rmq.object_ref()].local_state;
    let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
    assert(state_after_create(sub_resource, rmq, resp_msg.content.get_create_response().res->Ok_0, unmarshalled_state) is Ok);

    return resp_msg;
}

pub proof fn lemma_update_sub_resource_request_returns_ok(
    s: ClusterState, s_prime: ClusterState, rmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rmq, sub_resource)(s),
    req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rmq, controller_id, msg)(s),
ensures
    resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, rmq, controller_id, resp_msg)(s_prime),
    resource_state_matches(sub_resource, rmq)(s_prime),
{
    let resp_msg = handle_update_request_msg(cluster.installed_types, msg, s.api_server).1;
    let local_state = s_prime.ongoing_reconciles(controller_id)[rmq.object_ref()].local_state;
    let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
    assert(state_after_update(sub_resource, rmq, resp_msg.content.get_update_response().res->Ok_0, unmarshalled_state) is Ok);

    return resp_msg;
}

}