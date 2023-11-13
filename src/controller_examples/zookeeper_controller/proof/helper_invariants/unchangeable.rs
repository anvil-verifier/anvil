// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, error::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::{reconciler::*, resource_builder::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib::*, string_view::*};
use crate::zookeeper_controller::{
    common::*,
    proof::{
        helper_invariants::{owner_ref::*, predicate::*, proof::*, validation::*},
        predicate::*,
        resource::*,
    },
    spec::{reconciler::*, resource::*, types::*, zookeeper_api::validate_config_map_data},
};
use vstd::{multiset::*, prelude::*, seq_lib::*, string::*};

verus! {

// This module is to prove that for every subresource object, it satisfies some properties as long as it exists in etcd
// regardless of when it was created or how many times it has been updated or what its owner references point to.
// Right now only the `unchangeable` spec functions are proved by this. But actually things like
// `resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref` can also use the following lemmas.
// And the following lemmas are more powerful because it considers the cases when the objects in update request messages
// and etcd rely on each other to show they satisfy those properties.

/// Objects in create request messages satisfying the properties can be proved along because it doesn't have to do with
/// how the objects in etcd look like now.
pub open spec fn object_in_every_create_request_msg_satisfies_unchangeable(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    let resource_key = get_request(sub_resource, zookeeper).key;
    |s: ZKCluster| {
        forall |msg: ZKMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_create_request_msg(get_request(sub_resource, zookeeper).key)(msg)
            ==> unchangeable(sub_resource, msg.content.get_create_request().obj, zookeeper)
    }
}

/// On the contrary, we should combine the proof of update request message and etcd because they rely on each other.
pub open spec fn object_in_every_update_request_msg_satisfies_unchangeable(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    let resource_key = get_request(sub_resource, zookeeper).key;
    |s: ZKCluster| {
        forall |msg: ZKMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(get_request(sub_resource, zookeeper).key)(msg)
            && s.resources().contains_key(resource_key)
            && s.resources()[resource_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
            ==> unchangeable(sub_resource, msg.content.get_update_request().obj, zookeeper)
    }
}

proof fn lemma_always_object_in_every_create_request_msg_satisfies_unchangeable(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures
        spec.entails(always(lift_state(object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper)))),
{
    let inv = object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper);
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())(s)
    };
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    lemma_always_the_object_in_reconcile_satisfies_state_validation(spec, zookeeper.object_ref());
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref()))
    );
    let resource_key = get_request(sub_resource, zookeeper).key;
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: ZKMessage| s_prime.in_flight().contains(msg) && #[trigger] resource_create_request_msg(resource_key)(msg)
        implies unchangeable(sub_resource, msg.content.get_create_request().obj, zookeeper) by {
            if !s.in_flight().contains(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, zookeeper, s, s_prime, msg, step);
                match sub_resource {
                    SubResource::ConfigMap => {
                        ConfigMapView::marshal_preserves_integrity();
                        ConfigMapView::marshal_spec_preserves_integrity();
                        made_config_map_data_satisfies_validation(s.ongoing_reconciles()[zookeeper.object_ref()].triggering_cr);
                    },
                    SubResource::StatefulSet => {
                        StatefulSetView::marshal_preserves_integrity();
                        StatefulSetView::marshal_spec_preserves_integrity();
                    },
                    _ => {},
                }
            }
        }
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
}

pub proof fn lemma_always_object_in_etcd_satisfies_unchangeable(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures
        spec.entails(always(lift_state(object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)))),
{
    let inv = |s: ZKCluster| {
        &&& object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s)
        &&& object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s)
    };
    let resource_key = get_request(sub_resource, zookeeper).key;
    let next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(resource_key)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper)(s)
        &&& object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s)
        &&& response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)(s)
        &&& the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())(s)
    };
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    ZKCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, resource_key);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec, sub_resource, zookeeper);
    lemma_always_object_in_every_create_request_msg_satisfies_unchangeable(spec, sub_resource, zookeeper);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, zookeeper);
    lemma_always_the_object_in_reconcile_satisfies_state_validation(spec, zookeeper.object_ref());
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(resource_key)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper)),
        lift_state(object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)),
        lift_state(the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref()))
    );
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        object_in_etcd_satisfies_unchangeable_induction(sub_resource, zookeeper, s, s_prime);
        object_in_every_update_request_msg_satisfies_unchangeable_induction(sub_resource, zookeeper, s, s_prime);
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
    always_weaken_temp(spec, lift_state(inv), lift_state(object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)));
}

pub proof fn object_in_etcd_satisfies_unchangeable_induction(
    sub_resource: SubResource, zookeeper: ZookeeperClusterView, s: ZKCluster, s_prime: ZKCluster
)
    requires
        object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s),
        object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s),
        ZKCluster::next()(s, s_prime),
        ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        ZKCluster::each_object_in_etcd_is_well_formed()(s),
        ZKCluster::each_object_in_etcd_is_well_formed()(s_prime),
        object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper)(s),
        object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s),
    ensures
        object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s_prime),
{
    let resource_key = get_request(sub_resource, zookeeper).key;
    let step = choose |step| ZKCluster::next_step(s, s_prime, step);
    if s_prime.resources().contains_key(resource_key) {
        match sub_resource {
            SubResource::ConfigMap => {
                ConfigMapView::marshal_preserves_integrity();
                ConfigMapView::marshal_spec_preserves_integrity();
            },
            SubResource::StatefulSet => {
                StatefulSetView::marshal_preserves_integrity();
                StatefulSetView::marshal_spec_preserves_integrity();
            },
            _ => {},
        }
        match step {
            Step::KubernetesAPIStep(input) => {
                let req = input.get_Some_0();
                if resource_create_request_msg(resource_key)(req) {} else {}
                if resource_update_request_msg(resource_key)(req) {} else {}
            },
            _ => {}
        }
    }
}

pub proof fn object_in_every_update_request_msg_satisfies_unchangeable_induction(
    sub_resource: SubResource, zookeeper: ZookeeperClusterView, s: ZKCluster, s_prime: ZKCluster
)
    requires
        object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s),
        ZKCluster::next()(s, s_prime),
        ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        ZKCluster::each_object_in_etcd_is_well_formed()(s),
        ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, zookeeper).key)(s),
        response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)(s),
        object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper)(s),
        object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s),
        the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())(s),
    ensures
        object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s_prime),
{
    let resource_key = get_request(sub_resource, zookeeper).key;
    assert forall |msg: ZKMessage| s_prime.in_flight().contains(msg) && #[trigger] resource_update_request_msg(resource_key)(msg)
    && s_prime.resources().contains_key(resource_key) && s_prime.resources()[resource_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
    implies unchangeable(sub_resource, msg.content.get_update_request().obj, zookeeper) by {
        if s.in_flight().contains(msg) {
            if s.resources().contains_key(resource_key) {
                if s.resources()[resource_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version {
                    assert(unchangeable(sub_resource, msg.content.get_update_request().obj, zookeeper));
                } else {
                    assert(s_prime.resources()[resource_key].metadata.resource_version.get_Some_0() == s.kubernetes_api_state.resource_version_counter);
                }
            } else {
                assert(s_prime.resources()[resource_key].metadata.resource_version.get_Some_0() == s.kubernetes_api_state.resource_version_counter);
            }
            assert(unchangeable(sub_resource, msg.content.get_update_request().obj, zookeeper));
        } else {
            let step = choose |step| ZKCluster::next_step(s, s_prime, step);
            lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, zookeeper, s, s_prime, msg, step);
            match sub_resource {
                SubResource::ConfigMap => {
                    ConfigMapView::marshal_preserves_integrity();
                    ConfigMapView::marshal_spec_preserves_integrity();
                    made_config_map_data_satisfies_validation(s.ongoing_reconciles()[zookeeper.object_ref()].triggering_cr);
                },
                SubResource::StatefulSet => {
                    StatefulSetView::marshal_preserves_integrity();
                    StatefulSetView::marshal_spec_preserves_integrity();
                },
                _ => {},
            }
        }
    }
}

proof fn int_to_string_view_ensures_inequal(n: int)
    ensures
        forall |i| #![trigger int_to_string_view(n)[i]]
            0 <= i < int_to_string_view(n).len() ==> {
                &&& int_to_string_view(n)[i] != 'm'
                &&& int_to_string_view(n)[i] != 'i'
                &&& int_to_string_view(n)[i] != 'n'
                &&& int_to_string_view(n)[i] != '\n'
            },
{
    int_to_string_view_ensures_for(n);
}

#[verifier(external_body)]
proof fn made_config_map_data_satisfies_validation(zookeeper: ZookeeperClusterView)
    requires
        zookeeper.state_validation(),
    ensures
        make_config_map(zookeeper).data.is_Some(),
        validate_config_map_data(make_config_map(zookeeper).data.get_Some_0()),
{
    let data = make_config_map(zookeeper).data.get_Some_0();
    reveal_strlit("zoo.cfg");
    reveal_strlit("log4j.properties");
    reveal_strlit("log4j-quiet.properties");
    reveal_strlit("env.sh");
    assert(new_strlit("zoo.cfg")@.len() == 7);
    assert(data.contains_key(new_strlit("zoo.cfg")@));
    let zk_config = make_zk_config(zookeeper);
    assert(data[new_strlit("zoo.cfg")@] == zk_config);
    let prefix = new_strlit("4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n\
    dataDir=/data\n\
    standaloneEnabled=false\n\
    reconfigEnabled=true\n\
    skipACL=yes\n\
    metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n\
    metricsProvider.httpPort=")@;
    reveal_strlit("4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n\
    dataDir=/data\n\
    standaloneEnabled=false\n\
    reconfigEnabled=true\n\
    skipACL=yes\n\
    metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n\
    metricsProvider.httpPort=");
    reveal_strlit("\nmetricsProvider.exportJvmInfo=true\ninitLimit=");
    reveal_strlit("\nsyncLimit=");
    reveal_strlit("\ntickTime=");
    reveal_strlit("\nglobalOutstandingLimit=");
    reveal_strlit("\npreAllocSize=");
    reveal_strlit("\nsnapCount=");
    reveal_strlit("\ncommitLogCount=");
    reveal_strlit("\nsnapSizeLimitInKb=");
    reveal_strlit("\nmaxCnxns=");
    reveal_strlit("\nmaxClientCnxns=");
    reveal_strlit("\nminSessionTimeout=");
    reveal_strlit("\nmaxSessionTimeout=");
    reveal_strlit("\nautopurge.snapRetainCount=");
    reveal_strlit("\nautopurge.purgeInterval=");
    reveal_strlit("\nquorumListenOnAllIPs=");
    reveal_strlit("\nadmin.serverPort=");
    reveal_strlit("\ndynamicConfigFile=/data/zoo.cfg.dynamic\n");
    reveal_strlit("true");
    reveal_strlit("false");
    int_to_string_view_ensures_inequal(zookeeper.spec.ports.metrics);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.init_limit);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.sync_limit);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.tick_time);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.global_outstanding_limit);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.pre_alloc_size);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.snap_count);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.commit_log_count);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.snap_size_limit_in_kb);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.max_cnxns);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.max_client_cnxns);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.min_session_timeout);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.max_session_timeout);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.auto_purge_snap_retain_count);
    int_to_string_view_ensures_inequal(zookeeper.spec.conf.auto_purge_purge_interval);
    bool_to_string_view_ensures_for(zookeeper.spec.conf.quorum_listen_on_all_ips);
    int_to_string_view_ensures_inequal(zookeeper.spec.ports.admin_server);
    assert forall |min| #![trigger int_to_string_view(min)] (exists |min_i, min_j| zk_config.len() >= min_j > min_i >= 0 &&
    (#[trigger] zk_config.subrange(min_i,min_j)) == new_strlit("minSessionTimeout=")@ + int_to_string_view(min) + new_strlit("\n")@)
    implies min == zookeeper.spec.conf.min_session_timeout by {
        let (min_i, min_j) = choose |min_i, min_j| zk_config.len() >= min_j > min_i >= 0 &&
        (#[trigger] zk_config.subrange(min_i,min_j)) == new_strlit("minSessionTimeout=")@ + int_to_string_view(min) + new_strlit("\n")@;
        let len = zk_config.subrange(min_i,min_j).len();
        reveal_strlit("minSessionTimeout=");
        // assert_seqs_equal!(zk_config.subrange(min_i, min_j).subrange(0, 18), new_strlit("minSessionTimeout=")@);
        // assert_seqs_equal!(zk_config.subrange(min_i, min_i + 18), new_strlit("minSessionTimeout=")@);
        // assert(zk_config.subrange(min_i, min_j).len() == min_j - min_i);
        // assert(len >= 18);
        // assert(zk_config.subrange(min_i, min_j).subrange(0, 18) == new_strlit("minSessionTimeout=")@);
        // assert(zk_config.subrange(min_i, min_i + 18) == new_strlit("minSessionTimeout=")@);
        assert(zk_config.subrange(min_i, min_j)[0] == 'm');
        assert(zk_config[min_i] == 'm');
        assert(zk_config.subrange(min_i, min_j)[1] == 'i');
        assert(zk_config[min_i + 1] == 'i');
        assert(zk_config.subrange(min_i, min_j)[2] == 'n');
        assert(zk_config[min_i + 2] == 'n');
        assert(zk_config.subrange(min_i, min_j)[3] == 'S');
        assert(zk_config[min_i + 3] == 'S');
        assert(min_i == (prefix + int_to_string_view(zookeeper.spec.ports.metrics) + new_strlit("\n\
        metricsProvider.exportJvmInfo=true\n\
        initLimit=")@ + int_to_string_view(zookeeper.spec.conf.init_limit)
        + new_strlit("\nsyncLimit=")@ + int_to_string_view(zookeeper.spec.conf.sync_limit)
        + new_strlit("\ntickTime=")@ + int_to_string_view(zookeeper.spec.conf.tick_time)
        + new_strlit("\nglobalOutstandingLimit=")@ + int_to_string_view(zookeeper.spec.conf.global_outstanding_limit)
        + new_strlit("\npreAllocSize=")@ + int_to_string_view(zookeeper.spec.conf.pre_alloc_size)
        + new_strlit("\nsnapCount=")@ + int_to_string_view(zookeeper.spec.conf.snap_count)
        + new_strlit("\ncommitLogCount=")@ + int_to_string_view(zookeeper.spec.conf.commit_log_count)
        + new_strlit("\nsnapSizeLimitInKb=")@ + int_to_string_view(zookeeper.spec.conf.snap_size_limit_in_kb)
        + new_strlit("\nmaxCnxns=")@ + int_to_string_view(zookeeper.spec.conf.max_cnxns)
        + new_strlit("\nmaxClientCnxns=")@ + int_to_string_view(zookeeper.spec.conf.max_client_cnxns)
        ).len() + 1);
        assert(len == new_strlit("minSessionTimeout=")@.len() + int_to_string_view(min).len() + new_strlit("\n")@.len());
        assert_seqs_equal!(
            new_strlit("minSessionTimeout=")@ + int_to_string_view(min) + new_strlit("\n")@,
            zk_config.subrange(min_i, min_i+18) + zk_config.subrange(min_i+18,min_j)
        );
        assume(new_strlit("minSessionTimeout=")@ + (int_to_string_view(min) + new_strlit("\n")@) == new_strlit("minSessionTimeout=")@ + zk_config.subrange(min_i+18,min_j));
        seq_equal_preserved_by_add_prefix(new_strlit("minSessionTimeout=")@, int_to_string_view(min) + new_strlit("\n")@, zk_config.subrange(min_i+18,min_j));
        reveal_strlit("\n");
        assert(int_to_string_view(min) + new_strlit("\n")@ == zk_config.subrange(min_i+18,min_j));
        assert((int_to_string_view(min) + new_strlit("\n")@)[int_to_string_view(min).len() as int] == '\n');
        assert(zk_config.subrange(min_i+18,min_j)[int_to_string_view(min).len() as int] == '\n');
        assert(zk_config.subrange(min_i+18,min_j).len() == int_to_string_view(min).len() + 1);
        int_to_string_view_ensures_for(min);
        let min_session_timeout_string = int_to_string_view(zookeeper.spec.conf.min_session_timeout);
        let min_string = int_to_string_view(min);
        if min_string.len() < min_session_timeout_string.len() {
            // assert_seqs_equal!(min_string, zk_config.subrange(min_i+18,min_j))
            let min_string_len = min_string.len() as int;
            assert_seqs_equal!(zk_config.subrange(min_i+18,min_j).subrange(0,min_string_len),min_session_timeout_string.subrange(0,min_string_len));
            assert_seqs_equal!(zk_config.subrange(min_i+18,min_j).subrange(0,min_string_len+1),min_session_timeout_string.subrange(0,min_string_len+1));
            assert(zk_config.subrange(min_i+18,min_j).subrange(0,min_string_len+1)[min_string_len] == min_session_timeout_string.subrange(0,min_string_len+1)[min_string_len]);
            assert(min_session_timeout_string[min_string_len] == '\n');
        } else if min_string.len() > min_session_timeout_string.len() {
            let min_session_timeout_string_len = min_session_timeout_string.len() as int;
            assert_seqs_equal!(zk_config.subrange(min_i+18,min_j).subrange(0,min_session_timeout_string_len),min_string.subrange(0,min_session_timeout_string_len));
            assert_seqs_equal!(zk_config.subrange(min_i+18,min_j).subrange(0,min_session_timeout_string_len+1),min_string.subrange(0,min_session_timeout_string_len+1));
            assert(zk_config.subrange(min_i+18,min_j).subrange(0,min_session_timeout_string_len+1)[min_session_timeout_string_len] == '\n');
            assert(min_string[min_session_timeout_string_len] == '\n');
        }
        assert(min_session_timeout_string.len() == min_string.len());
        assert_seqs_equal!(new_strlit("minSessionTimeout=")@ + int_to_string_view(min) + new_strlit("\n")@
        , new_strlit("minSessionTimeout=")@ + int_to_string_view(zookeeper.spec.conf.min_session_timeout) + new_strlit("\n")@);
        assert_by(
            new_strlit("minSessionTimeout=")@ + int_to_string_view(min) == new_strlit("minSessionTimeout=")@ + int_to_string_view(zookeeper.spec.conf.min_session_timeout),
            {
                seq_equal_preserved_by_add(new_strlit("minSessionTimeout=")@ + int_to_string_view(min), new_strlit("minSessionTimeout=")@ + int_to_string_view(zookeeper.spec.conf.min_session_timeout), new_strlit("\n")@);
            }
        );
        assert_by(
            int_to_string_view(min) == int_to_string_view(zookeeper.spec.conf.min_session_timeout),
            {
                seq_equal_preserved_by_add_prefix(new_strlit("minSessionTimeout=")@, int_to_string_view(min), int_to_string_view(zookeeper.spec.conf.min_session_timeout));
            }
        );
        int_to_string_view_injectivity_for(min, zookeeper.spec.conf.min_session_timeout);
    }
    // assert forall |max_i, max_j, max| #![trigger zk_config.subrange(max_i,max_j), int_to_string_view(max)]
    // zk_config.subrange(max_i,max_j) == new_strlit("maxSessionTimeout=")@ + int_to_string_view(max) + new_strlit("\n")@
    // implies max == zookeeper.spec.conf.max_session_timeout by {
    //     let len = zk_config.subrange(max_i,max_j).len();
    //     reveal_strlit("maxSessionTimeout=");
    //     assert_seqs_equal!(zk_config.subrange(max_i, max_j).subrange(0, 18), new_strlit("maxSessionTimeout=")@);
    //     assert(zk_config.subrange(max_i, max_j).subrange(0, 18) == new_strlit("maxSessionTimeout=")@);
    //     let max_session_timeout_string = int_to_string_view(zookeeper.spec.conf.max_session_timeout);
    //     let max_string = int_to_string_view(max);
    //     if max_string.len() > max_session_timeout_string.len() {
    //         assert(max_string[max_session_timeout_string.len() as int] == '\n');
    //     } else if max_string.len() < max_session_timeout_string.len(){
    //         assert(max_session_timeout_string[max_string.len() as int] == '\n');
    //     }
    //     assert_seqs_equal!(max_string, max_session_timeout_string);
    // }
    // assert forall |limit_i, limit_j, limit| #![trigger zk_config.subrange(limit_i,limit_j), int_to_string_view(limit)]
    // zk_config.subrange(limit_i,limit_j) == new_strlit("syncLimit=")@ + int_to_string_view(limit) + new_strlit("\n")@
    // implies limit == zookeeper.spec.conf.sync_limit by {
    //     let len = zk_config.subrange(limit_i,limit_j).len();
    //     reveal_strlit("syncLimit=");
    //     assert_seqs_equal!(zk_config.subrange(limit_i, limit_j).subrange(0, 10), new_strlit("syncLimit=")@);
    //     assert(zk_config.subrange(limit_i, limit_j).subrange(0, 10) == new_strlit("syncLimit=")@);
    //     let sync_limit_string = int_to_string_view(zookeeper.spec.conf.sync_limit);
    //     let limit_string = int_to_string_view(limit);
    //     if limit_string.len() > sync_limit_string.len() {
    //         assert(limit_string[sync_limit_string.len() as int] == '\n');
    //     } else if limit_string.len() < sync_limit_string.len(){
    //         assert(sync_limit_string[limit_string.len() as int] == '\n');
    //     }
    //     assert_seqs_equal!(limit_string, sync_limit_string);
    // }
}

}
