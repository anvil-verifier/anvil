// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    affinity::*, api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError,
    marshal::*, object_meta::*, owner_reference::*, resource::*, resource_requirements::*,
    toleration::*,
};
use crate::pervasive_ext::{string_map::*, string_view::*};
use crate::zookeeper_controller::spec::types::*;
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct ZookeeperCluster {
    inner: deps_hack::ZookeeperCluster
}

impl ZookeeperCluster {
    pub spec fn view(&self) -> ZookeeperClusterView;

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: ZookeeperClusterSpec)
        ensures
            spec@ == self@.spec,
    {
        ZookeeperClusterSpec::from_kube(self.inner.spec.clone())
    }

    #[verifier(external_body)]
    pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
        ensures
            owner_reference@ == self@.controller_owner_ref(),
    {
        OwnerReference::from_kube(
            // We can safely unwrap here because the trait method implementation always returns a Some(...)
            self.inner.controller_owner_ref(&()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == ZookeeperClusterView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::ZookeeperCluster>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.marshal(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<ZookeeperCluster, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ZookeeperClusterView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ZookeeperClusterView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::ZookeeperCluster>();
        if parse_result.is_ok() {
            let res = ZookeeperCluster { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::ZookeeperCluster> for ZookeeperCluster {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::ZookeeperCluster) -> ZookeeperCluster {
        ZookeeperCluster {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::ZookeeperCluster {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ZookeeperClusterSpec {
    inner: deps_hack::ZookeeperClusterSpec,
}

impl ZookeeperClusterSpec {
    pub spec fn view(&self) -> ZookeeperClusterSpecView;

    #[verifier(external_body)]
    pub fn replicas(&self) -> (replicas: i32)
        ensures
            replicas as int == self@.replicas,
    {
        self.inner.replicas
    }

    #[verifier(external_body)]
    pub fn image(&self) -> (image: String)
        ensures
            image@ == self@.image,
    {
        String::from_rust_string(self.inner.image.to_string())
    }

    #[verifier(external_body)]
    pub fn ports(&self) -> (ports: ZookeeperPorts)
        ensures
            ports@ == self@.ports,
    {
        ZookeeperPorts::from_kube(self.inner.ports.clone())
    }

    #[verifier(external_body)]
    pub fn conf(&self) -> (conf: ZookeeperConfig)
        ensures
            conf@ == self@.conf,
    {
        ZookeeperConfig::from_kube(self.inner.conf.clone())
    }

    #[verifier(external_body)]
    pub fn persistence(&self) -> (persistence: ZookeeperPersistence)
        ensures
            persistence@ == self@.persistence,
    {
        ZookeeperPersistence::from_kube(self.inner.persistence.clone())
    }

    #[verifier(external_body)]
    pub fn resources(&self) -> (resources: Option<ResourceRequirements>)
        ensures
            self@.resources.is_Some() == resources.is_Some(),
            resources.is_Some() ==> resources.get_Some_0()@ == self@.resources.get_Some_0(),
    {
        match &self.inner.resources {
            Some(r) => Some(ResourceRequirements::from_kube(r.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn affinity(&self) -> (affinity: Option<Affinity>)
        ensures
            self@.affinity.is_Some() == affinity.is_Some(),
            affinity.is_Some() ==> affinity.get_Some_0()@ == self@.affinity.get_Some_0(),
    {
        match &self.inner.affinity {
            Some(a) => Some(Affinity::from_kube(a.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn tolerations(&self) -> (tolerations: Option<Vec<Toleration>>)
        ensures
            self@.tolerations.is_Some() == tolerations.is_Some(),
            tolerations.is_Some() ==> tolerations.get_Some_0()@.map_values(|t: Toleration| t@) == self@.tolerations.get_Some_0(),
    {
        match &self.inner.tolerations {
            Some(tols) => Some(tols.clone().into_iter().map(|t: deps_hack::k8s_openapi::api::core::v1::Toleration| Toleration::from_kube(t)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn node_selector(&self) -> (node_selector: StringMap)
        ensures
            node_selector@ == self@.node_selector,
    {
        StringMap::from_rust_map(self.inner.node_selector.clone())
    }

    #[verifier(external_body)]
    pub fn labels(&self) -> (labels: StringMap)
        ensures
            labels@ == self@.labels,
    {
        StringMap::from_rust_map(self.inner.labels.clone())
    }

    #[verifier(external_body)]
    pub fn annotations(&self) -> (annotations: StringMap)
        ensures
            annotations@ == self@.annotations,
    {
        StringMap::from_rust_map(self.inner.annotations.clone())
    }
}

impl ResourceWrapper<deps_hack::ZookeeperClusterSpec> for ZookeeperClusterSpec {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::ZookeeperClusterSpec) -> ZookeeperClusterSpec {
        ZookeeperClusterSpec {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::ZookeeperClusterSpec {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ZookeeperPorts {
    inner: deps_hack::ZookeeperPorts,
}

impl ZookeeperPorts {
    pub spec fn view(&self) -> ZookeeperPortsView;

    #[verifier(external_body)]
    pub fn client(&self) -> (client: i32)
        ensures
            client as int == self@.client,
    {
        self.inner.client
    }

    #[verifier(external_body)]
    pub fn quorum(&self) -> (quorum: i32)
        ensures
            quorum as int == self@.quorum,
    {
        self.inner.quorum
    }

    #[verifier(external_body)]
    pub fn leader_election(&self) -> (leader_election: i32)
        ensures
            leader_election as int == self@.leader_election,
    {
        self.inner.leader_election
    }

    #[verifier(external_body)]
    pub fn metrics(&self) -> (metrics: i32)
        ensures
            metrics as int == self@.metrics,
    {
        self.inner.metrics
    }

    #[verifier(external_body)]
    pub fn admin_server(&self) -> (admin_server: i32)
        ensures
            admin_server as int == self@.admin_server,
    {
        self.inner.admin_server
    }
}

impl ResourceWrapper<deps_hack::ZookeeperPorts> for ZookeeperPorts {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::ZookeeperPorts) -> ZookeeperPorts {
        ZookeeperPorts {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::ZookeeperPorts {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ZookeeperConfig {
    inner: deps_hack::ZookeeperConfig,
}

impl ZookeeperConfig {
    pub spec fn view(&self) -> ZookeeperConfigView;

    #[verifier(external_body)]
    pub fn init_limit(&self) -> (init_limit: i32)
        ensures
            init_limit as int == self@.init_limit,
    {
        self.inner.init_limit
    }

    #[verifier(external_body)]
    pub fn tick_time(&self) -> (tick_time: i32)
        ensures
            tick_time as int == self@.tick_time,
    {
        self.inner.tick_time
    }

    #[verifier(external_body)]
    pub fn sync_limit(&self) -> (sync_limit: i32)
        ensures
            sync_limit as int == self@.sync_limit,
    {
        self.inner.sync_limit
    }

    #[verifier(external_body)]
    pub fn global_outstanding_limit(&self) -> (global_outstanding_limit: i32)
        ensures
            global_outstanding_limit as int == self@.global_outstanding_limit,
    {
        self.inner.global_outstanding_limit
    }

    #[verifier(external_body)]
    pub fn pre_alloc_size(&self) -> (pre_alloc_size: i32)
        ensures
            pre_alloc_size as int == self@.pre_alloc_size,
    {
        self.inner.pre_alloc_size
    }

    #[verifier(external_body)]
    pub fn snap_count(&self) -> (snap_count: i32)
        ensures
            snap_count as int == self@.snap_count,
    {
        self.inner.snap_count
    }

    #[verifier(external_body)]
    pub fn commit_log_count(&self) -> (commit_log_count: i32)
        ensures
            commit_log_count as int == self@.commit_log_count,
    {
        self.inner.commit_log_count
    }

    #[verifier(external_body)]
    pub fn snap_size_limit_in_kb(&self) -> (snap_size_limit_in_kb: i32)
        ensures
            snap_size_limit_in_kb as int == self@.snap_size_limit_in_kb,
    {
        self.inner.snap_size_limit_in_kb
    }

    #[verifier(external_body)]
    pub fn max_cnxns(&self) -> (max_cnxns: i32)
        ensures
            max_cnxns as int == self@.max_cnxns,
    {
        self.inner.max_cnxns
    }

    #[verifier(external_body)]
    pub fn max_client_cnxns(&self) -> (max_client_cnxns: i32)
        ensures
            max_client_cnxns as int == self@.max_client_cnxns,
    {
        self.inner.max_client_cnxns
    }

    #[verifier(external_body)]
    pub fn min_session_timeout(&self) -> (min_session_timeout: i32)
        ensures
            min_session_timeout as int == self@.min_session_timeout,
    {
        self.inner.min_session_timeout
    }

    #[verifier(external_body)]
    pub fn max_session_timeout(&self) -> (max_session_timeout: i32)
        ensures
            max_session_timeout as int == self@.max_session_timeout,
    {
        self.inner.max_session_timeout
    }

    #[verifier(external_body)]
    pub fn auto_purge_snap_retain_count(&self) -> (auto_purge_snap_retain_count: i32)
        ensures
            auto_purge_snap_retain_count as int == self@.auto_purge_snap_retain_count,
    {
        self.inner.auto_purge_snap_retain_count
    }

    #[verifier(external_body)]
    pub fn auto_purge_purge_interval(&self) -> (auto_purge_purge_interval: i32)
        ensures
            auto_purge_purge_interval as int == self@.auto_purge_purge_interval,
    {
        self.inner.auto_purge_purge_interval
    }

    #[verifier(external_body)]
    pub fn quorum_listen_on_all_ips(&self) -> (quorum_listen_on_all_ips: bool)
        ensures
            quorum_listen_on_all_ips == self@.quorum_listen_on_all_ips,
    {
        self.inner.quorum_listen_on_all_ips
    }
}

impl ResourceWrapper<deps_hack::ZookeeperConfig> for ZookeeperConfig {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::ZookeeperConfig) -> ZookeeperConfig {
        ZookeeperConfig {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::ZookeeperConfig {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ZookeeperPersistence {
    inner: deps_hack::ZookeeperPersistence,
}

impl ZookeeperPersistence {
    pub spec fn view(&self) -> ZookeeperPersistenceView;

    #[verifier(external_body)]
    pub fn enabled(&self) -> (enabled: bool)
        ensures
            enabled == self@.enabled,
    {
        self.inner.enabled
    }

    #[verifier(external_body)]
    pub fn storage_size(&self) -> (storage_size: String)
        ensures
            storage_size@ == self@.storage_size,
    {
        String::from_rust_string(self.inner.storage_size.clone().0)
    }

    #[verifier(external_body)]
    pub fn storage_class_name(&self) -> (storage_class_name: Option<String>)
        ensures
            self@.storage_class_name.is_Some() == storage_class_name.is_Some(),
            storage_class_name.is_Some() ==> storage_class_name.get_Some_0()@ == self@.storage_class_name.get_Some_0(),
    {
        match &self.inner.storage_class_name {
            Some(s) => Some(String::from_rust_string(s.clone())),
            None => None,
        }
    }
}

impl ResourceWrapper<deps_hack::ZookeeperPersistence> for ZookeeperPersistence {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::ZookeeperPersistence) -> ZookeeperPersistence {
        ZookeeperPersistence {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::ZookeeperPersistence {
        self.inner
    }
}

}
