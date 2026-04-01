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
    proof::{predicate::*, resource::*, guarantee::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::rabbitmq_controller::proof::helper_invariants::no_interfering_request_between_rmq_forall_rmq;
use crate::vstatefulset_controller::trusted::spec_types::{VStatefulSetView, StatefulSetPodNameLabel, StatefulSetOrdinalLabel};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib::*, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

#[verifier(external_body)]
pub proof fn rmq_with_different_key_implies_request_with_different_key(rmq: RabbitmqClusterView, other_rmq: RabbitmqClusterView, sub_resource: SubResource)
requires
    rmq.object_ref() != other_rmq.object_ref()
ensures
    get_request(sub_resource, other_rmq).key != get_request(sub_resource, rmq).key,
{}

pub proof fn lemma_cr_name_neq_implies_resource_key_name_neq(
    cr_name_a: StringView, cr_name_b: StringView, suffix: StringView,
)
    requires cr_name_a != cr_name_b,
    ensures
        RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + cr_name_a + suffix
        != RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + cr_name_b + suffix,
{
    let prefix_dash = RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@;
    // prefix_dash + cr_name_a != prefix_dash + cr_name_b  (since cr_name_a != cr_name_b)
    seq_unequal_preserved_by_add_prefix(prefix_dash, cr_name_a, cr_name_b);
    // (prefix_dash + cr_name_a) + suffix != (prefix_dash + cr_name_b) + suffix
    seq_unequal_preserved_by_add(prefix_dash + cr_name_a, prefix_dash + cr_name_b, suffix);
}

pub proof fn lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key(
    cr_key_a: ObjectRef, cr_key_b: ObjectRef, sub_resource_a: SubResource, sub_resource_b: SubResource
)
requires
    sub_resource_a != sub_resource_b,
ensures
    make_resource_key(cr_key_a, sub_resource_a) != make_resource_key(cr_key_b, sub_resource_b),
{
    let key_a = make_resource_key(cr_key_a, sub_resource_a);
    let key_b = make_resource_key(cr_key_b, sub_resource_b);
    // If the kinds differ, the keys trivially differ.
    if key_a.kind == key_b.kind {
        // Same Kind => one of three pairs (Service, Secret, ConfigMap).
        // We show key_a.name != key_b.name by examining a character near the end
        // that differs between the two suffixes.
        match key_a.kind {
            Kind::ServiceKind => {
                // HeadlessService: suffix "-nodes" (last char 's')
                // Service: suffix "-client" (last char 't')
                reveal_strlit("-nodes");
                reveal_strlit("-client");
                if sub_resource_a == SubResource::HeadlessService {
                    assert(key_a.name[key_a.name.len() - 1] == 's');
                    assert(key_b.name[key_b.name.len() - 1] == 't');
                } else {
                    assert(key_a.name[key_a.name.len() - 1] == 't');
                    assert(key_b.name[key_b.name.len() - 1] == 's');
                }
            },
            Kind::SecretKind => {
                // ErlangCookieSecret: suffix "-erlang-cookie" (last char 'e')
                // DefaultUserSecret: suffix "-default-user" (last char 'r')
                reveal_strlit("-erlang-cookie");
                reveal_strlit("-default-user");
                if sub_resource_a == SubResource::ErlangCookieSecret {
                    assert(key_a.name[key_a.name.len() - 1] == 'e');
                    assert(key_b.name[key_b.name.len() - 1] == 'r');
                } else {
                    assert(key_a.name[key_a.name.len() - 1] == 'r');
                    assert(key_b.name[key_b.name.len() - 1] == 'e');
                }
            },
            Kind::ConfigMapKind => {
                // PluginsConfigMap: suffix "-plugins-conf" (char at len-6 is 's')
                // ServerConfigMap: suffix "-server-conf" (char at len-6 is 'r')
                reveal_strlit("-plugins-conf");
                reveal_strlit("-server-conf");
                if sub_resource_a == SubResource::PluginsConfigMap {
                    assert(key_a.name[key_a.name.len() - 6] == 's');
                    assert(key_b.name[key_b.name.len() - 6] == 'r');
                } else {
                    assert(key_a.name[key_a.name.len() - 6] == 'r');
                    assert(key_b.name[key_b.name.len() - 6] == 's');
                }
            },
            _ => {
                // No other Kind has two different sub-resources mapping to it.
                assert(false);
            }
        }
    }
}

pub proof fn lemma_sub_resource_neq_implies_resource_key_neq(
    rabbitmq: RabbitmqClusterView, sub_resource_a: SubResource, sub_resource_b: SubResource
)
    requires
        sub_resource_a != sub_resource_b,
    ensures
        get_request(sub_resource_a, rabbitmq).key != get_request(sub_resource_b, rabbitmq).key,
{
    let res_key_a = get_request(sub_resource_a, rabbitmq).key;
    let res_key_b = get_request(sub_resource_b, rabbitmq).key;
    if res_key_a.kind == res_key_b.kind {
        // When two different sub-resources share the same Kind, they must have different name suffixes.
        // We prove name inequality by showing the suffixes differ (via reveal_strlit + character comparison),
        // then use seq_unequal_preserved_by_add_prefix to lift that to the full names.
        let prefix = RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.object_ref().name;
        match res_key_a.kind {
            Kind::ServiceKind => {
                // HeadlessService: prefix + "-nodes", Service: prefix + "-client"
                assert_by("-nodes"@ != "-client"@, {
                    reveal_strlit("-nodes");
                    reveal_strlit("-client");
                    if "-nodes"@.len() == "-client"@.len() {
                        assert("-nodes"@[1] != "-client"@[1]);
                    }
                });
                seq_unequal_preserved_by_add_prefix(prefix, "-nodes"@, "-client"@);
                if sub_resource_a == SubResource::HeadlessService {
                    assert(sub_resource_b == SubResource::Service);
                } else {
                    assert(sub_resource_b == SubResource::HeadlessService);
                }
            },
            Kind::SecretKind => {
                // ErlangCookieSecret: prefix + "-erlang-cookie", DefaultUserSecret: prefix + "-default-user"
                assert_by("-erlang-cookie"@ != "-default-user"@, {
                    reveal_strlit("-erlang-cookie");
                    reveal_strlit("-default-user");
                    if "-erlang-cookie"@.len() == "-default-user"@.len() {
                        assert("-erlang-cookie"@[1] != "-default-user"@[1]);
                    }
                });
                seq_unequal_preserved_by_add_prefix(prefix, "-erlang-cookie"@, "-default-user"@);
                if sub_resource_a == SubResource::ErlangCookieSecret {
                    assert(sub_resource_b == SubResource::DefaultUserSecret);
                } else {
                    assert(sub_resource_b == SubResource::ErlangCookieSecret);
                }
            },
            Kind::ConfigMapKind => {
                // PluginsConfigMap: prefix + "-plugins-conf", ServerConfigMap: prefix + "-server-conf"
                assert_by("-plugins-conf"@ != "-server-conf"@, {
                    reveal_strlit("-plugins-conf");
                    reveal_strlit("-server-conf");
                    if "-plugins-conf"@.len() == "-server-conf"@.len() {
                        assert("-plugins-conf"@[1] != "-server-conf"@[1]);
                    }
                });
                seq_unequal_preserved_by_add_prefix(prefix, "-plugins-conf"@, "-server-conf"@);
                if sub_resource_a == SubResource::PluginsConfigMap {
                    assert(sub_resource_b == SubResource::ServerConfigMap);
                } else {
                    assert(sub_resource_b == SubResource::PluginsConfigMap);
                }
            },
            _ => {
                assert(false);
            }
        }
    }
}

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
    let sts = update_stateful_set(rmq, found_sts, cm_rv);
    let name = rmq.metadata.name->0;

    // The updated sts keeps found_sts.spec.selector, which already passes validation
    // The updated sts keeps found_sts.spec.volume_claim_templates, update_strategy, ordinals, min_ready_seconds
    // All of these pass validation from found_sts.state_validation()

    // template comes from make_stateful_set - need to prove labels don't contain reserved keys
    // and selector matches template labels
    let template_labels = make_labels(rmq);
    let labels = Map::empty().insert("app"@, name);

    // selector matches template labels (selector is preserved from found_sts)
    assert forall |k: StringView, v: StringView| labels.contains_pair(k, v) implies template_labels.contains_pair(k, v) by {
    };

    // template labels don't contain StatefulSetPodNameLabel or StatefulSetOrdinalLabel
    reveal_strlit("app");
    reveal_strlit("statefulset.kubernetes.io/pod-name");
    reveal_strlit("apps.kubernetes.io/pod-index");
    assert(StatefulSetPodNameLabel == "statefulset.kubernetes.io/pod-name"@);
    assert(StatefulSetOrdinalLabel == "apps.kubernetes.io/pod-index"@);
    assert(!rmq.spec.labels.contains_key(StatefulSetPodNameLabel));
    assert(!rmq.spec.labels.contains_key(StatefulSetOrdinalLabel));
    assert("app"@.len() == 3);
    assert("statefulset.kubernetes.io/pod-name"@.len() > 3);
    assert("apps.kubernetes.io/pod-index"@.len() > 3);
    assert("app"@ != StatefulSetPodNameLabel);
    assert("app"@ != StatefulSetOrdinalLabel);
    assert(!rmq.spec.labels.insert("app"@, name).contains_key(StatefulSetPodNameLabel));
    assert(!rmq.spec.labels.insert("app"@, name).contains_key(StatefulSetOrdinalLabel));

    return sts;
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

pub proof fn lemma_get_sub_resource_request_returns_ok_or_not_found(
    s: ClusterState, s_prime: ClusterState, rmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rmq, sub_resource)(s),
    req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rmq, controller_id, msg)(s),
ensures
    s.resources().contains_key(get_request(sub_resource, rmq).key) == s_prime.resources().contains_key(get_request(sub_resource, rmq).key),
    s.resources().contains_key(get_request(sub_resource, rmq).key) ==>
        resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rmq, controller_id, resp_msg)(s_prime),
    !s.resources().contains_key(get_request(sub_resource, rmq).key) ==>
        resp_msg_is_the_in_flight_not_found_resp_at_after_get_resource_step(sub_resource, rmq, controller_id, resp_msg)(s_prime),
{
    RabbitmqReconcileState::marshal_preserves_integrity();

    let resp_msg = handle_get_request_msg(msg, s.api_server).1;
    return resp_msg;
}

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

#[verifier(external_body)]
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

/// When an API server step processes a request whose key is different from `resource_key`,
/// the resource at `resource_key` is unchanged. This is needed because compound operations
/// like GetThenUpdate/GetThenUpdateStatus have complex specs that the verifier can't
/// automatically reason through.
#[verifier(spinoff_prover)]
pub proof fn lemma_api_request_not_made_by_field_matches_maintains_resource(
    s: ClusterState, s_prime: ClusterState, cluster: Cluster, msg: Message, resource_key: ObjectRef,
)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    msg.content is APIRequest,
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(_) => true,
        APIRequest::ListRequest(_) => true,
        APIRequest::CreateRequest(req) => s.resources().contains_key(resource_key),
        APIRequest::DeleteRequest(req) => req.key != resource_key,
        APIRequest::UpdateRequest(req) => req.key() != resource_key,
        APIRequest::UpdateStatusRequest(req) => req.key() != resource_key,
        APIRequest::GetThenDeleteRequest(req) => req.key() != resource_key,
        APIRequest::GetThenUpdateRequest(req) => req.key() != resource_key,
        APIRequest::GetThenUpdateStatusRequest(req) => req.key() != resource_key,
    },
ensures
    s.resources().contains_key(resource_key) == s_prime.resources().contains_key(resource_key),
    s.resources().contains_key(resource_key) ==> s.resources()[resource_key] == s_prime.resources()[resource_key],
{
    let (etcd_state, _) = transition_by_etcd(cluster.installed_types, msg, s.api_server);
    assert(s_prime.api_server == etcd_state);
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(_) => {},
        APIRequest::ListRequest(_) => {},
        APIRequest::CreateRequest(req) => {
            // resource_key already exists in s.resources().
            // If create admission fails, state unchanged.
            // If the created object's key already exists, ObjectAlreadyExists — state unchanged.
            // If it succeeds, insert at created_obj.object_ref() which can't be resource_key
            // because resource_key already exists but created_obj.object_ref() doesn't.
            if create_request_admission_check(cluster.installed_types, req, s.api_server) is None {
                let created_obj = DynamicObjectView {
                    kind: req.obj.kind,
                    metadata: ObjectMetaView {
                        name: if req.obj.metadata.name is Some {
                            req.obj.metadata.name
                        } else {
                            Some(generated_name(s.api_server, req.obj.metadata.generate_name.unwrap()))
                        },
                        namespace: Some(req.namespace),
                        resource_version: Some(s.api_server.resource_version_counter),
                        uid: Some(s.api_server.uid_counter),
                        deletion_timestamp: None,
                        ..req.obj.metadata
                    },
                    spec: req.obj.spec,
                    status: marshalled_default_status(req.obj.kind, cluster.installed_types),
                };
                if s.api_server.resources.contains_key(created_obj.object_ref()) {
                } else if created_object_validity_check(created_obj, cluster.installed_types) is Some {
                } else {
                    // created_obj.object_ref() doesn't exist yet, resource_key does, so they differ
                    assert(!s.api_server.resources.contains_key(created_obj.object_ref()));
                    assert(s.api_server.resources.contains_key(resource_key));
                    assert(created_obj.object_ref() != resource_key);
                }
            }
        },
        APIRequest::DeleteRequest(req) => {},
        APIRequest::UpdateRequest(req) => {},
        APIRequest::UpdateStatusRequest(req) => {},
        APIRequest::GetThenDeleteRequest(req) => {
            let gd_req = msg.content.get_get_then_delete_request();
            if gd_req.well_formed() && s.api_server.resources.contains_key(gd_req.key())
            && s.api_server.resources[gd_req.key()].metadata.owner_references_contains(gd_req.owner_ref) {
                // Delete at gd_req.key() != resource_key
            }
        },
        APIRequest::GetThenUpdateRequest(req) => {
            let gu_req = msg.content.get_get_then_update_request();
            if gu_req.well_formed() && s.api_server.resources.contains_key(gu_req.key())
            && s.api_server.resources[gu_req.key()].metadata.owner_references_contains(gu_req.owner_ref) {
                let current_obj = s.api_server.resources[gu_req.key()];
                let new_obj = DynamicObjectView {
                    metadata: ObjectMetaView {
                        resource_version: current_obj.metadata.resource_version,
                        uid: current_obj.metadata.uid,
                        ..gu_req.obj.metadata
                    },
                    ..gu_req.obj
                };
                let update_req = UpdateRequest {
                    name: gu_req.name,
                    namespace: gu_req.namespace,
                    obj: new_obj,
                };
                assert(update_req.key() == gu_req.key());
                assert(update_req.key() != resource_key);
            }
        },
        APIRequest::GetThenUpdateStatusRequest(req) => {
            let gus_req = msg.content.get_get_then_update_status_request();
            if gus_req.well_formed() && s.api_server.resources.contains_key(gus_req.key())
            && s.api_server.resources[gus_req.key()].metadata.owner_references_contains(gus_req.owner_ref) {
                let current_obj = s.api_server.resources[gus_req.key()];
                // From each_object_in_etcd_is_weakly_well_formed:
                //   current_obj.object_ref() == gus_req.key()
                // So current_obj.kind == gus_req.key().kind == gus_req.obj.kind
                assert(Cluster::etcd_object_is_weakly_well_formed(gus_req.key())(s));
                assert(current_obj.object_ref() == gus_req.key());
                let new_obj = DynamicObjectView {
                    metadata: current_obj.metadata,
                    spec: current_obj.spec,
                    status: gus_req.obj.status,
                    ..current_obj
                };
                let update_status_req = UpdateStatusRequest {
                    name: gus_req.name,
                    namespace: gus_req.namespace,
                    obj: new_obj,
                };
                assert(update_status_req.key() == gus_req.key());
                assert(update_status_req.key() != resource_key);
            }
        },
    }
}

}