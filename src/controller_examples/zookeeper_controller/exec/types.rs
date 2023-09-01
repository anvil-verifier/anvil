// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, resource::*,
};
use crate::pervasive_ext::string_view::*;
use crate::zookeeper_controller::spec::types::*;
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
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == ZookeeperClusterView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::ZookeeperCluster>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<ZookeeperCluster, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ZookeeperClusterView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ZookeeperClusterView::from_dynamic_object(obj@).get_Ok_0(),
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
    pub fn conf(&self) -> (conf: ZookeeperConfig)
        ensures
            conf@ == self@.conf,
    {
        ZookeeperConfig::from_kube(self.inner.conf.clone())
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

}
