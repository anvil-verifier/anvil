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
use crate::kubernetes_cluster::proof::api_server::generated_name_reflects_prefix;
use crate::rabbitmq_controller::{
    model::resource::*,
    proof::{predicate::*, resource::*, guarantee::*, helper_invariants::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::vstatefulset_controller::trusted::spec_types::{VStatefulSetView, STATEFULSET_POD_NAME_LABEL, STATEFULSET_ORDINAL_LABEL};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib::*, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub proof fn rmq_with_different_key_implies_request_with_different_key(rabbitmq: RabbitmqClusterView, other_rmq: RabbitmqClusterView, sub_resource: SubResource)
requires
    rabbitmq.object_ref() != other_rmq.object_ref()
ensures
    get_request(sub_resource, other_rmq).key != get_request(sub_resource, rabbitmq).key,
{
    let key_a = get_request(sub_resource, rabbitmq).key;
    let key_b = get_request(sub_resource, other_rmq).key;
    if rabbitmq.metadata.namespace->0 != other_rmq.metadata.namespace->0 {
    } else {
        assert(rabbitmq.metadata.name->0 != other_rmq.metadata.name->0);
        let prefix = RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@;
        let cr_name_a = rabbitmq.metadata.name->0;
        let cr_name_b = other_rmq.metadata.name->0;
        seq_unequal_preserved_by_add_prefix(prefix, cr_name_a, cr_name_b);
        match sub_resource {
            SubResource::HeadlessService => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-nodes"@);
            },
            SubResource::Service => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-client"@);
            },
            SubResource::ErlangCookieSecret => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-erlang-cookie"@);
            },
            SubResource::DefaultUserSecret => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-default-user"@);
            },
            SubResource::PluginsConfigMap => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-plugins-conf"@);
            },
            SubResource::ServerConfigMap => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-server-conf"@);
            },
            SubResource::ServiceAccount => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-server"@);
            },
            SubResource::Role => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-peer-discovery"@);
            },
            SubResource::RoleBinding => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-server"@);
            },
            SubResource::VStatefulSetView => {
                seq_unequal_preserved_by_add(prefix + cr_name_a, prefix + cr_name_b, "-server"@);
            },
        }
    }
}

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

// Sub-resource keys produced from two different RMQ cr_keys are disjoint.
// Both cr_keys must have the RabbitmqClusterView kind (which is the case for
// any cr_key managed by the rabbitmq controller).
pub proof fn lemma_diff_cr_key_implies_resource_key_neq(
    cr_key_a: ObjectRef, cr_key_b: ObjectRef, sub_a: SubResource, sub_b: SubResource,
)
    requires
        cr_key_a != cr_key_b,
        cr_key_a.kind == RabbitmqClusterView::kind(),
        cr_key_b.kind == RabbitmqClusterView::kind(),
    ensures
        make_resource_key(cr_key_a, sub_a) != make_resource_key(cr_key_b, sub_b),
{
    if sub_a != sub_b {
        // Different sub-resources: existing lemma handles both cross- and same-cr_key cases.
        lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key(cr_key_a, cr_key_b, sub_a, sub_b);
    } else {
        // Same sub_resource ⇒ same key.kind. Difference must come from cr_key.name or .namespace.
        let key_a = make_resource_key(cr_key_a, sub_a);
        let key_b = make_resource_key(cr_key_b, sub_b);
        if cr_key_a.namespace != cr_key_b.namespace {
            // namespaces differ ⇒ key namespaces differ.
            assert(key_a.namespace != key_b.namespace);
        } else {
            // Same namespace, same kind ⇒ cr_keys differ in name.
            assert(cr_key_a.name != cr_key_b.name);
            match sub_a {
                SubResource::HeadlessService => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-nodes"@);
                },
                SubResource::Service => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-client"@);
                },
                SubResource::ErlangCookieSecret => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-erlang-cookie"@);
                },
                SubResource::DefaultUserSecret => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-default-user"@);
                },
                SubResource::PluginsConfigMap => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-plugins-conf"@);
                },
                SubResource::ServerConfigMap => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-server-conf"@);
                },
                SubResource::ServiceAccount => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-server"@);
                },
                SubResource::Role => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-peer-discovery"@);
                },
                SubResource::RoleBinding => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-server"@);
                },
                SubResource::VStatefulSetView => {
                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key_a.name, cr_key_b.name, "-server"@);
                },
            }
        }
    }
}

pub proof fn lemma_resource_key_has_rmq_prefix(sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
ensures
    has_rmq_prefix(get_request(sub_resource, rabbitmq).key.name),
{
    let key_name = get_request(sub_resource, rabbitmq).key.name;
    let prefix = RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@;
    let rmq_name = rabbitmq.metadata.name->0;
    match sub_resource {
        SubResource::HeadlessService => {
            let suffix = rmq_name + "-nodes"@;
            assert(key_name =~= prefix + suffix);
        },
        SubResource::Service => {
            let suffix = rmq_name + "-client"@;
            assert(key_name =~= prefix + suffix);
        },
        SubResource::ErlangCookieSecret => {
            let suffix = rmq_name + "-erlang-cookie"@;
            assert(key_name =~= prefix + suffix);
        },
        SubResource::DefaultUserSecret => {
            let suffix = rmq_name + "-default-user"@;
            assert(key_name =~= prefix + suffix);
        },
        SubResource::PluginsConfigMap => {
            let suffix = rmq_name + "-plugins-conf"@;
            assert(key_name =~= prefix + suffix);
        },
        SubResource::ServerConfigMap => {
            let suffix = rmq_name + "-server-conf"@;
            assert(key_name =~= prefix + suffix);
        },
        SubResource::ServiceAccount => {
            let suffix = rmq_name + "-server"@;
            assert(key_name =~= prefix + suffix);
        },
        SubResource::Role => {
            let suffix = rmq_name + "-peer-discovery"@;
            assert(key_name =~= prefix + suffix);
        },
        SubResource::RoleBinding => {
            let suffix = rmq_name + "-server"@;
            assert(key_name =~= prefix + suffix);
        },
        SubResource::VStatefulSetView => {
            let suffix = rmq_name + "-server"@;
            assert(key_name =~= prefix + suffix);
        },
    }
    assert(has_rmq_prefix(key_name));
}

pub proof fn make_sts_pass_state_validation(rabbitmq: RabbitmqClusterView, cm_rv: StringView) -> (sts: VStatefulSetView)
requires
    rabbitmq.state_validation(),
ensures
    sts == make_stateful_set(rabbitmq, cm_rv),
    sts.state_validation(),
{
    let sts = make_stateful_set(rabbitmq, cm_rv);
    let name = rabbitmq.metadata.name->0;
    let labels = Map::empty().insert("app"@, name);

    // selector.match_labels is Some and non-empty
    assert(labels.len() > 0) by {
        assert(labels.contains_key("app"@));
    };

    // selector matches template labels
    let template_labels = make_labels(rabbitmq);
    assert forall |k: StringView, v: StringView| labels.contains_pair(k, v) implies template_labels.contains_pair(k, v) by {
    };

    // template labels don't contain STATEFULSET_POD_NAME_LABEL or STATEFULSET_ORDINAL_LABEL
    // make_labels(rabbitmq) = rabbitmq.spec.labels.insert("app"@, name)
    reveal_strlit("app");
    reveal_strlit("statefulset.kubernetes.io/pod-name");
    reveal_strlit("apps.kubernetes.io/pod-index");
    assert(STATEFULSET_POD_NAME_LABEL == "statefulset.kubernetes.io/pod-name"@);
    assert(STATEFULSET_ORDINAL_LABEL == "apps.kubernetes.io/pod-index"@);
    // From rabbitmq.state_validation()
    assert(!rabbitmq.spec.labels.contains_key(STATEFULSET_POD_NAME_LABEL));
    assert(!rabbitmq.spec.labels.contains_key(STATEFULSET_ORDINAL_LABEL));
    // "app" != STATEFULSET_POD_NAME_LABEL/STATEFULSET_ORDINAL_LABEL (different lengths)
    assert("app"@.len() == 3);
    assert("statefulset.kubernetes.io/pod-name"@.len() > 3);
    assert("apps.kubernetes.io/pod-index"@.len() > 3);
    assert("app"@ != STATEFULSET_POD_NAME_LABEL);
    assert("app"@ != STATEFULSET_ORDINAL_LABEL);
    // So insert("app", name) doesn't introduce those keys
    assert(!rabbitmq.spec.labels.insert("app"@, name).contains_key(STATEFULSET_POD_NAME_LABEL));
    assert(!rabbitmq.spec.labels.insert("app"@, name).contains_key(STATEFULSET_ORDINAL_LABEL));

    // Volume claim templates validation
    if rabbitmq.spec.persistence.storage != "0Gi"@ {
        reveal_strlit("persistence");
        assert(dash_free("persistence"@));
    }

    return sts;
}

pub proof fn update_sts_pass_state_validation(rabbitmq: RabbitmqClusterView, found_sts: VStatefulSetView, cm_rv: StringView) -> (sts: VStatefulSetView)
requires
    rabbitmq.state_validation(),
    found_sts.state_validation(),
    found_sts.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref()),
    found_sts.spec.selector == LabelSelectorView::default().with_match_labels(Map::empty().insert("app"@, rabbitmq.metadata.name->0)),
ensures
    sts == update_stateful_set(rabbitmq, found_sts, cm_rv),
    sts.state_validation(),
{
    let sts = update_stateful_set(rabbitmq, found_sts, cm_rv);
    let name = rabbitmq.metadata.name->0;

    // The updated sts keeps found_sts.spec.selector, which already passes validation
    // The updated sts keeps found_sts.spec.volume_claim_templates, update_strategy, ordinals, min_ready_seconds
    // All of these pass validation from found_sts.state_validation()

    // template comes from make_stateful_set - need to prove labels don't contain reserved keys
    // and selector matches template labels
    let template_labels = make_labels(rabbitmq);
    let labels = Map::empty().insert("app"@, name);

    // selector matches template labels (selector is preserved from found_sts)
    assert forall |k: StringView, v: StringView| labels.contains_pair(k, v) implies template_labels.contains_pair(k, v) by {
    };

    // template labels don't contain STATEFULSET_POD_NAME_LABEL or STATEFULSET_ORDINAL_LABEL
    reveal_strlit("app");
    reveal_strlit("statefulset.kubernetes.io/pod-name");
    reveal_strlit("apps.kubernetes.io/pod-index");
    assert(STATEFULSET_POD_NAME_LABEL == "statefulset.kubernetes.io/pod-name"@);
    assert(STATEFULSET_ORDINAL_LABEL == "apps.kubernetes.io/pod-index"@);
    assert(!rabbitmq.spec.labels.contains_key(STATEFULSET_POD_NAME_LABEL));
    assert(!rabbitmq.spec.labels.contains_key(STATEFULSET_ORDINAL_LABEL));
    assert("app"@.len() == 3);
    assert("statefulset.kubernetes.io/pod-name"@.len() > 3);
    assert("apps.kubernetes.io/pod-index"@.len() > 3);
    assert("app"@ != STATEFULSET_POD_NAME_LABEL);
    assert("app"@ != STATEFULSET_ORDINAL_LABEL);
    assert(!rabbitmq.spec.labels.insert("app"@, name).contains_key(STATEFULSET_POD_NAME_LABEL));
    assert(!rabbitmq.spec.labels.insert("app"@, name).contains_key(STATEFULSET_ORDINAL_LABEL));

    return sts;
}

// shield_lemma
#[verifier(spinoff_prover)]
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
    s: ClusterState, s_prime: ClusterState, rabbitmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s),
    cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime),
    cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
    Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s),
    // Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
    Cluster::no_pending_request_to_api_server_from_non_controllers()(s),
    Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s),
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)(s),
    resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)(s),
    no_delete_resource_request_msg_from_gc_in_flight(sub_resource, rabbitmq)(s),
    rmq_self_rely_guarantee(controller_id, rabbitmq.object_ref())(s),
    rmq_guarantee(controller_id)(s),
    rmq_rely_conditions(cluster, controller_id)(s),
    msg.src != HostId::Controller(controller_id, rabbitmq.object_ref()),
ensures
    s.resources().contains_key(get_request(sub_resource, rabbitmq).key) == s_prime.resources().contains_key(get_request(sub_resource, rabbitmq).key),
    s.resources().contains_key(get_request(sub_resource, rabbitmq).key) ==> match sub_resource {
        // to prove cm resource version does not change, rely conditions prevent status update request to this kind
        SubResource::ServerConfigMap | SubResource::PluginsConfigMap => s.resources()[get_request(sub_resource, rabbitmq).key] == s_prime.resources()[get_request(sub_resource, rabbitmq).key],
        _ => s.resources()[get_request(sub_resource, rabbitmq).key].spec == s_prime.resources()[get_request(sub_resource, rabbitmq).key].spec
            && s.resources()[get_request(sub_resource, rabbitmq).key].metadata.without_resource_version() == s_prime.resources()[get_request(sub_resource, rabbitmq).key].metadata.without_resource_version(),
    },
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    assert(s.in_flight().contains(msg));
    if !(msg.content is APIRequest && msg.dst is APIServer) {
        return;
    }

    if s.resources().contains_key(resource_key) {
        let etcd_obj = s.resources()[resource_key];
        let owner_ref = choose |owner_reference: OwnerReferenceView| {
            &&& etcd_obj.metadata.owner_references == Some(seq![owner_reference])
            &&& #[trigger] owner_reference_eq_without_uid(owner_reference, rabbitmq.controller_owner_ref())
        };
        let some_rmq = RabbitmqClusterView {
            metadata: ObjectMetaView {
                name: Some(rabbitmq.metadata.name->0),
                uid: Some(owner_ref.uid),
                ..rabbitmq.metadata
            },
            ..rabbitmq
        };
        assert(etcd_obj.metadata.owner_references->0[0] == some_rmq.controller_owner_ref());
        assert(etcd_obj.metadata.owner_references->0.contains(etcd_obj.metadata.owner_references->0[0]));
        assert(etcd_obj.metadata.owner_references_contains(some_rmq.controller_owner_ref()));
        assert(exists |rabbitmq: RabbitmqClusterView| #[trigger] etcd_obj.metadata.owner_references_contains(rabbitmq.controller_owner_ref()));
    }
    lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);

    // Establish a concrete formula for s_prime.api_server.
    let api_state_prime = transition_by_etcd(cluster.installed_types, msg, s.api_server).0;
    assert(s_prime.api_server == api_state_prime);

    match msg.src {
        HostId::Controller(id, cr_key) => {
            if id != controller_id {
                assert(cluster.controller_models.remove(controller_id).contains_key(id));
                assert(rmq_rely(id)(s));
            }
            match msg.content->APIRequest_0 {
                APIRequest::GetRequest(_) | APIRequest::ListRequest(_) => {
                    // Read-only: api server does not modify resources.
                    assert(s_prime.resources() == s.resources());
                    assert(s.resources().contains_key(resource_key) ==> s_prime.resources().contains_key(resource_key));
                },
                APIRequest::CreateRequest(req) => {
                    if id == controller_id {
                        // rmq_guarantee_create_req: req.obj.metadata.name is Some.
                        assert(rmq_guarantee_create_req(req));
                        // self-rely: cr_key != rabbitmq.object_ref() ⇒ req.key() != resource_key.
                        assert(cr_key != rabbitmq.object_ref());
                        assert(req.key() != make_resource_key(rabbitmq.object_ref(), sub_resource));
                        assert(req.key() != resource_key);
                    } else if is_rmq_managed_kind(req.obj.kind) {
                        // id != controller_id: use rely.
                        if req.obj.metadata.name is Some {
                            if req.key() == resource_key {
                                assert(false);
                            }
                        } else if req.obj.metadata.generate_name is Some {
                            let name = generated_name(s.api_server, req.obj.metadata.generate_name->0);
                            if has_rmq_prefix(name) {
                                generated_name_spec(s.api_server, req.obj.metadata.generate_name->0);
                                let generated_suffix = choose |suffix: StringView| #[trigger] dash_free(suffix) &&
                                    name == req.obj.metadata.generate_name->0 + suffix;
                                generated_name_reflects_prefix(s.api_server, req.obj.metadata.generate_name->0, RabbitmqClusterView::kind()->CustomResourceKind_0);
                                assert(false);
                            }
                            assert(name != resource_key.name);
                        }
                    }
                    // Create only inserts at most one key, never removes; if rk in s, rk in s_prime.
                    assert(s.resources().contains_key(resource_key) ==> s_prime.resources().contains_key(resource_key));
                },
                APIRequest::UpdateRequest(req) => {
                    if id == controller_id {
                        // rmq_guarantee returns false for UpdateRequest from rabbitmq controller.
                        assert(false);
                    } else {
                        if s.resources().contains_key(resource_key) {
                            if req.key() == resource_key {
                                assert(update_request_admission_check(cluster.installed_types, req, s.api_server) is Some);
                                assert(s_prime.resources() == s.resources());
                            } else {
                                // req.key() != resource_key. handle_update_request only ever modifies
                                // s_prime.resources() at req.key(), so dom is preserved at rk.
                                assert(req.key() != resource_key);
                                assert(s_prime.resources().contains_key(resource_key));
                            }
                        }
                        assert(s.resources().contains_key(resource_key) ==> s_prime.resources().contains_key(resource_key));
                    }
                },
                APIRequest::DeleteRequest(req) => {
                    if id == controller_id {
                        assert(false);
                    } else if s.resources().contains_key(resource_key) && req.key() == resource_key {
                        assert(delete_request_admission_check(req, s.api_server) is Some);
                        assert(s_prime.resources() == s.resources());
                    }
                },
                APIRequest::UpdateStatusRequest(req) => {
                    if id == controller_id {
                        // rmq_guarantee returns false for UpdateStatusRequest from rabbitmq controller.
                        assert(false);
                    } else {
                        if s.resources().contains_key(resource_key) {
                            if req.key() == resource_key {
                                if req.obj.kind == Kind::ConfigMapKind {
                                    // For CM: rmq_rely_update_status_req triggers and gives rv mismatch.
                                    assert(update_status_request_admission_check(cluster.installed_types, req, s.api_server) is Some);
                                    assert(s_prime.resources() == s.resources());
                                }
                                // For non-CM: status_updated_object preserves spec; contains_key preserved.
                            } else {
                                assert(req.key() != resource_key);
                            }
                        }
                        assert(s.resources().contains_key(resource_key) ==> s_prime.resources().contains_key(resource_key));
                    }
                },
                APIRequest::GetThenUpdateRequest(req) => {
                    if id == controller_id {
                        // self-rely: cr_key != rabbitmq.object_ref() ⇒ req.key() != resource_key.
                        assert(cr_key != rabbitmq.object_ref());
                        assert(req.key() != make_resource_key(rabbitmq.object_ref(), sub_resource));
                        assert(req.key() != resource_key);
                    } else if req.key() == resource_key && s.resources().contains_key(resource_key) {
                        // id != controller_id: rely says effective get_then_update on rabbitmq-managed
                        // key with rabbitmq prefix has owner_ref.kind != RmqCR::kind. The etcd owner_ref
                        // (a singleton) does have kind == RmqCR::kind, so owner_refs.contains(req.owner_ref)
                        // would force a contradiction; hence the API server's owner check fails and
                        // s_prime.resources() == s.resources().
                        let etcd_obj = s.resources()[resource_key];
                        let owner_refs = etcd_obj.metadata.owner_references->0;
                        if owner_refs.contains(req.owner_ref) {
                            lemma_singleton_contains_at_most_one_element(owner_refs, req.owner_ref, owner_refs[0]);
                        }
                        assert(s_prime.resources() == s.resources());
                    }
                    assert(s.resources().contains_key(resource_key) ==> s_prime.resources().contains_key(resource_key));
                },
                APIRequest::GetThenDeleteRequest(req) => {
                    if id == controller_id {
                        assert(false);
                    } else {
                        if req.key == resource_key && s.resources().contains_key(resource_key) {
                            let etcd_obj = s.resources()[resource_key];
                            let owner_refs = etcd_obj.metadata.owner_references->0;
                            if owner_refs.contains(req.owner_ref) {
                                lemma_singleton_contains_at_most_one_element(owner_refs, req.owner_ref, owner_refs[0]);
                            }
                            assert(s_prime.resources() == s.resources());
                        }
                        assert(s.resources().contains_key(resource_key) ==> s_prime.resources().contains_key(resource_key));
                    }
                },
                APIRequest::GetThenUpdateStatusRequest(req) => {
                    if id == controller_id {
                        // rmq_guarantee returns false for GetThenUpdateStatusRequest from rabbitmq controller.
                        assert(false);
                    } else {
                        if s.resources().contains_key(resource_key) {
                            if req.key() == resource_key {
                                if req.obj.kind == Kind::ConfigMapKind {
                                    // For CM: rmq_rely_get_then_update_status_req gives owner_ref.kind != RabbitmqClusterView.
                                    // The owner_references_contains check fails, so handle returns TransactionAbort.
                                    let etcd_obj = s.resources()[resource_key];
                                    let owner_refs = etcd_obj.metadata.owner_references->0;
                                    if owner_refs.contains(req.owner_ref) {
                                        lemma_singleton_contains_at_most_one_element(owner_refs, req.owner_ref, owner_refs[0]);
                                    }
                                    assert(s_prime.resources() == s.resources());
                                }
                                // For non-CM: status-only change preserves spec; contains_key preserved.
                            } else {
                                assert(req.key() != resource_key);
                            }
                        }
                        assert(s.resources().contains_key(resource_key) ==> s_prime.resources().contains_key(resource_key));
                    }
                },
            }
        },
        HostId::BuiltinController => {
            // all_requests_from_builtin_controllers_are_api_delete_requests forces msg to be a delete.
            assert(msg.content.is_delete_request());
            assert(!resource_delete_request_msg(resource_key)(msg));
            let req = msg.content.get_delete_request();
            assert(req.key != resource_key);
            assert(s.resources().contains_key(resource_key) ==> s_prime.resources().contains_key(resource_key));
        },
        _ => {
            // no_pending_request_to_api_server_from_non_controllers excludes other sources.
            assert(false);
        },
    }
}

pub proof fn lemma_get_sub_resource_request_returns_ok_or_not_found(
    s: ClusterState, s_prime: ClusterState, rabbitmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, msg)(s),
ensures
    s.resources().contains_key(get_request(sub_resource, rabbitmq).key) == s_prime.resources().contains_key(get_request(sub_resource, rabbitmq).key),
    s.resources().contains_key(get_request(sub_resource, rabbitmq).key) ==>
        resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s_prime),
    !s.resources().contains_key(get_request(sub_resource, rabbitmq).key) ==>
        resp_msg_is_the_in_flight_not_found_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s_prime),
{
    RabbitmqReconcileState::marshal_preserves_integrity();

    let resp_msg = handle_get_request_msg(msg, s.api_server).1;
    return resp_msg;
}

pub proof fn lemma_create_sub_resource_request_returns_ok(
    s: ClusterState, s_prime: ClusterState, rabbitmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, msg)(s),
ensures
    resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s_prime),
    resource_state_matches(sub_resource, rabbitmq)(s_prime),
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
    let local_state = s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state;
    let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
    assert(state_after_create(sub_resource, rabbitmq, resp_msg.content.get_create_response().res->Ok_0, unmarshalled_state) is Ok);

    return resp_msg;
}

pub proof fn lemma_get_then_update_sub_resource_request_returns_ok(
    s: ClusterState, s_prime: ClusterState, rabbitmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, msg)(s),
ensures
    resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s_prime),
    resource_state_matches(sub_resource, rabbitmq)(s_prime),
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

    let resp_msg = handle_get_then_update_request_msg(cluster.installed_types, msg, s.api_server).1;
    let local_state = s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state;
    let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();

    let step = after_update_k_request_step(sub_resource);
    let key = get_request(sub_resource, rabbitmq).key;
    let req = msg.content.get_get_then_update_request();
    assert(msg.content.is_get_then_update_request());
    assert(resp_msg.content.get_get_then_update_response().res is Ok) by {
        assert(req.well_formed());
        // resource_object_only_has_owner_reference_pointing_to_current_cr gives
        // etcd.owner_references == seq![rabbitmq.controller_owner_ref()] exactly (with uid).
        // req.owner_ref == rabbitmq.controller_owner_ref() from the pending-req predicate.
        // Combining: etcd.owner_references_contains(req.owner_ref).
        let etcd_refs = s.resources()[key].metadata.owner_references->0;
        assert(s.resources()[key].metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()]));
        assert(etcd_refs[0] == rabbitmq.controller_owner_ref());
        assert(req.owner_ref == rabbitmq.controller_owner_ref());
        assert(etcd_refs.contains(req.owner_ref)) by {
            assert(etcd_refs[0] == req.owner_ref);
        }
    }
    assert(state_after_update(sub_resource, rabbitmq, resp_msg.content.get_get_then_update_response().res->Ok_0, unmarshalled_state) is Ok);

    return resp_msg;
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
pub proof fn lemma_resource_get_then_update_request_msg_implies_key_in_reconcile_equals(controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message, step: Step)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s_prime),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        cluster.next_step(s, s_prime, step),
        resource_get_then_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg),
        (msg.content.get_get_then_update_request().owner_ref.kind == RabbitmqClusterView::kind() && msg.content.get_get_then_update_request().owner_ref.controller == Some(true))
            || msg.src == HostId::Controller(controller_id, rabbitmq.object_ref()),
    ensures
        step is ControllerStep,
        step->ControllerStep_0.0 == controller_id,
        step->ControllerStep_0.2->0 == rabbitmq.object_ref(),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s_prime),
        Cluster::pending_req_msg_is(controller_id, s_prime, rabbitmq.object_ref(), msg),
        // since init
        msg.content.get_get_then_update_request().obj.metadata.finalizers is None,
        msg.content.get_get_then_update_request().obj.metadata.deletion_timestamp is None,
        exists |owner_reference: OwnerReferenceView| {
            &&& msg.content.get_get_then_update_request().obj.metadata.owner_references == Some(seq![owner_reference])
            &&& #[trigger] owner_reference_eq_without_uid(owner_reference, rabbitmq.controller_owner_ref())
        },
        // holds later
        Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s)
            ==> msg.content.get_get_then_update_request().owner_ref == rabbitmq.controller_owner_ref(),
{
    assert(step is ControllerStep);
    let (id, _, cr_key_opt) = step->ControllerStep_0;
    if msg.content.get_get_then_update_request().owner_ref.kind == RabbitmqClusterView::kind()
        && msg.content.get_get_then_update_request().owner_ref.controller == Some(true)    
        && id != controller_id { // other controller, call rely condition to derive contradiction
        assert(cluster.controller_models.remove(controller_id).contains_key(id));
        assert(rmq_rely(id)(s_prime));
        lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);
        assert(false);
    }
    let cr_key = cr_key_opt->0;
    let cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr)->Ok_0;
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
    let local_step = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    let local_step_prime = RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    assert(local_step is AfterKRequestStep && local_step->AfterKRequestStep_0 == ActionKind::Get);
    assert(local_step_prime is AfterKRequestStep && local_step_prime->AfterKRequestStep_0 == ActionKind::Update);
    assert(msg.content.get_get_then_update_request().obj.metadata.owner_references == Some(seq![cr.controller_owner_ref()]));
    // 1. lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key: eliminates the "wrong sub-resource"
    //    case for sub-resources sharing the same Kind (e.g., PluginsConfigMap vs ServerConfigMap).
    // 2. lemma_cr_name_neq_implies_resource_key_name_neq (contrapositive): if the resource key names
    //    are equal, then cr_key.name == key.name.
    let local_step_sub_resource = local_step->AfterKRequestStep_1;
    // Eliminate the case where the controller creates a different sub-resource type.
    if local_step_sub_resource != sub_resource {
        lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key(cr_key, key, local_step_sub_resource, sub_resource);
    }
    // Now local_step_sub_resource == sub_resource. Prove cr_key.name == key.name by contrapositive.
    if cr_key.name != key.name {
        match sub_resource {
            SubResource::ServerConfigMap => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server-conf"@),
            SubResource::PluginsConfigMap => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-plugins-conf"@),
            SubResource::ErlangCookieSecret => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-erlang-cookie"@),
            SubResource::DefaultUserSecret => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-default-user"@),
            SubResource::HeadlessService => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-nodes"@),
            SubResource::Service => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-client"@),
            SubResource::RoleBinding | SubResource::ServiceAccount | SubResource::VStatefulSetView => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server"@),
            SubResource::Role => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-peer-discovery"@),
        }
    }
    assert(cr_key == rabbitmq.object_ref());
    assert(owner_reference_eq_without_uid(cr.controller_owner_ref(), rabbitmq.controller_owner_ref()));
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
pub proof fn lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message, step: Step)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s_prime),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        cluster.next_step(s, s_prime, step),
        resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg),
    ensures
        step is ControllerStep,
        step->ControllerStep_0.0 == controller_id,
        step->ControllerStep_0.2->0 == rabbitmq.object_ref(),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s_prime),
        Cluster::pending_req_msg_is(controller_id, s_prime, rabbitmq.object_ref(), msg),
        msg.content.get_create_request().obj.metadata.finalizers is None,
        exists |owner_reference: OwnerReferenceView| {
            &&& msg.content.get_create_request().obj.metadata.owner_references == Some(seq![owner_reference])
            &&& #[trigger] owner_reference_eq_without_uid(owner_reference, rabbitmq.controller_owner_ref())
        },
{
    // Since we know that this step creates a sub resource create request message, it is easy to see that it's a controller action.
    // This action creates a resource, and there may be sub-resources sharing the same Kind, so we have to show that only the correct sub-resource
    // is possible by extra reasoning about the strings.
    assert(step is ControllerStep);
    let (id, _, cr_key_opt) = step->ControllerStep_0;

    if id != controller_id { // other controller, call rely condition to derive contradiction
        assert(cluster.controller_models.remove(controller_id).contains_key(id));
        // rmq_rely(other_id)(s_prime): msg IS in s_prime.in_flight(), so rely applies
        assert(rmq_rely(id)(s_prime));
        // resource_create_request_msg gives us: req.obj.metadata.name is Some, name == resource_key.name.
        // resource_key.name has rabbitmq prefix; req.obj.kind == resource_key.kind is rabbitmq-managed.
        // rmq_rely_create_req: is_rmq_managed_kind(req.obj.kind) ==> name has no rabbitmq prefix. Contradiction.
        lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);
        assert(false);
    }
    let cr_key = cr_key_opt->0;
    let cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr)->Ok_0;
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let local_step = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    let local_step_prime = RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
    assert(local_step is AfterKRequestStep && local_step->AfterKRequestStep_0 == ActionKind::Get);
    assert(local_step_prime is AfterKRequestStep && local_step_prime->AfterKRequestStep_0 == ActionKind::Create);
    assert(msg.content.get_create_request().obj.metadata.owner_references == Some(seq![cr.controller_owner_ref()]));
    // It's easy for the verifier to know that cr_key has the same kind and namespace as key.
    // We use two helper lemmas:
    // 1. lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key: eliminates the "wrong sub-resource"
    //    case for sub-resources sharing the same Kind (e.g., PluginsConfigMap vs ServerConfigMap).
    // 2. lemma_cr_name_neq_implies_resource_key_name_neq (contrapositive): if the resource key names
    //    are equal, then cr_key.name == key.name.
    let local_step_sub_resource = local_step->AfterKRequestStep_1;
    // Eliminate the case where the controller creates a different sub-resource type.
    if local_step_sub_resource != sub_resource {
        lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key(cr_key, key, local_step_sub_resource, sub_resource);
    }
    // Now local_step_sub_resource == sub_resource. Prove cr_key.name == key.name by contrapositive.
    if cr_key.name != key.name {
        match sub_resource {
            SubResource::ServerConfigMap => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server-conf"@),
            SubResource::PluginsConfigMap => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-plugins-conf"@),
            SubResource::ErlangCookieSecret => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-erlang-cookie"@),
            SubResource::DefaultUserSecret => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-default-user"@),
            SubResource::HeadlessService => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-nodes"@),
            SubResource::Service => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-client"@),
            SubResource::RoleBinding | SubResource::ServiceAccount | SubResource::VStatefulSetView => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server"@),
            SubResource::Role => lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-peer-discovery"@),
        }
    }
    assert(cr_key == rabbitmq.object_ref());
    assert(owner_reference_eq_without_uid(cr.controller_owner_ref(), rabbitmq.controller_owner_ref()));
}

pub proof fn rmq_rely_condition_equivalent_to_lifted_rmq_rely_condition(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] rmq_rely(other_id)))))
        <==>
            spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
{
    let lhs =
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] rmq_rely(other_id)))));
    let rhs = spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id))));

    assert_by(
        lhs ==> rhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                lhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies rmq_rely(other_id)(ex.suffix(n).head()) by {
                assert(valid(spec.implies(always(lift_state(rmq_rely(other_id))))));
                assert(spec.implies(always(lift_state(rmq_rely(other_id)))).satisfied_by(ex));
                assert(always(lift_state(rmq_rely(other_id))).satisfied_by(ex));
                assert(lift_state(rmq_rely(other_id)).satisfied_by(ex.suffix(n)));
            }
        }
    );

    assert_by(
        rhs ==> lhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                rhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies rmq_rely(other_id)(ex.suffix(n).head()) by {
                assert(valid(spec.implies(always(lift_state(rmq_rely_conditions(cluster, controller_id))))));
                assert(spec.implies(always(lift_state(rmq_rely_conditions(cluster, controller_id)))).satisfied_by(ex));
                assert(always(lift_state(rmq_rely_conditions(cluster, controller_id))).satisfied_by(ex));
                assert(lift_state(rmq_rely_conditions(cluster, controller_id)).satisfied_by(ex.suffix(n)));
            }
        }
    );
}

}