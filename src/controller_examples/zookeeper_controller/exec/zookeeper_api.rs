// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::exec::*;
use crate::pervasive_ext::to_view::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::zookeeper_api::{
    ZKAPIInputView, ZKAPIOutputView, ZKAPIResultView,
};
use core::time::Duration;
use deps_hack::zookeeper::{Acl, CreateMode, WatchedEvent, Watcher, ZkError, ZooKeeper};
use vstd::{prelude::*, string::*};

verus! {

pub type ZKAPIResult = Result<(), Error>;

impl ToView for ZKAPIResult {
    type V = ZKAPIResultView;
    spec fn to_view(&self) -> ZKAPIResultView {
        match self {
            Ok(_) => Ok(()),
            Err(_) => Err(Error::ClusterSizeZKNodeSetFailed),
        }
    }
}

#[is_variant]
pub enum ZKAPIInput {
    SetZKNode(String, String, String),
}

#[is_variant]
pub enum ZKAPIOutput {
    SetZKNode(ZKAPIResult),
}

impl ToView for ZKAPIInput {
    type V = ZKAPIInputView;
    spec fn to_view(&self) -> ZKAPIInputView {
        match self {
            ZKAPIInput::SetZKNode(zk_name, zk_namespace, replicas)
                => ZKAPIInputView::SetZKNode(zk_name@, zk_namespace@, replicas@),
        }
    }
}

pub proof fn zk_api_input_to_view_match(zk_name: String, zk_namespace: String, replicas: String)
    ensures
        ZKAPIInput::SetZKNode(zk_name, zk_namespace, replicas).to_view()
            == ZKAPIInputView::SetZKNode(zk_name@, zk_namespace@, replicas@) {}

impl ToView for ZKAPIOutput {
    type V = ZKAPIOutputView;
    spec fn to_view(&self) -> ZKAPIOutputView {
        match self {
            ZKAPIOutput::SetZKNode(result) => ZKAPIOutputView::SetZKNode(result.to_view()),
        }
    }
}

pub proof fn zk_api_output_to_view_match(result: ZKAPIResult)
    ensures
        ZKAPIOutput::SetZKNode(result).to_view() == ZKAPIOutputView::SetZKNode(result.to_view()) {}

impl ZKAPIOutput {
    pub fn is_reconcile_zk_node(&self) -> (res: bool)
        ensures res <==> self.is_SetZKNode(),
    {
        match self {
            ZKAPIOutput::SetZKNode(_) => true,
        }
    }

    pub fn into_zk_api_result(self) -> (result: ZKAPIResult)
        requires
            self.is_SetZKNode(),
        ensures
            result == self.get_SetZKNode_0(),
            result.is_Ok() <==> self.get_SetZKNode_0().is_Ok(),
    {
        match self {
            ZKAPIOutput::SetZKNode(result) => result,
        }
    }
}

pub struct ZKAPI {}

impl ExternalAPI<ZKAPIInput, ZKAPIOutput> for ZKAPI {
    #[verifier(external)]
    fn transition(input: ZKAPIInput) -> Option<ZKAPIOutput> {
        match input {
            ZKAPIInput::SetZKNode(zk_name, zk_namespace, replicas)
                => Some(ZKAPIOutput::SetZKNode(reconcile_zk_node(zk_name, zk_namespace, replicas))),
        }
    }
}

struct LoggingWatcher;
impl Watcher for LoggingWatcher {
    #[verifier(external)]
    fn handle(&self, e: WatchedEvent) {}
}

#[verifier(external)]
pub fn reconcile_zk_node(zk_name: String, zk_namespace: String, replicas: String) -> ZKAPIResult {
    let uri = &format!(
        "{}-client.{}.svc.cluster.local:2181",
        zk_name.as_rust_string_ref(),
        zk_namespace.as_rust_string_ref()
    );
    let zk_client = ZooKeeper::connect(uri, Duration::from_secs(10), LoggingWatcher)
        .map_err(|e| Error::ClusterSizeZKNodeSetFailed)?;

    let parent_node_path = "/zookeeper-operator";
    ensure_parent_node_exists(parent_node_path, &zk_client)?;

    let node_path = &format!("{}/{}", parent_node_path, zk_name.as_rust_string_ref());
    let data = format!("CLUSTER_SIZE={}", replicas.as_rust_string_ref()).as_bytes().to_vec();
    let acl = Acl::open_unsafe().to_vec();
    match zk_client.exists(node_path, false) {
        Err(_) => Err(Error::ClusterSizeZKNodeSetFailed),
        Ok(stat_opt) => match stat_opt {
            Some(stat) => {
                match zk_client.set_data(node_path, data, Some(stat.version)) {
                    Err(_) => Err(Error::ClusterSizeZKNodeSetFailed),
                    Ok(_) => Ok(()),
                }
            }
            None => {
                match zk_client.create(node_path, data, acl, CreateMode::Persistent) {
                    Err(_) => Err(Error::ClusterSizeZKNodeSetFailed),
                    Ok(_) => Ok(()),
                }
            }
        }
    }
}

#[verifier(external)]
pub fn ensure_parent_node_exists(parent_node_path: &str, zk_client: &ZooKeeper) -> ZKAPIResult {
    let data = Vec::new();
    let acl = Acl::open_unsafe().to_vec();
    match zk_client.exists(parent_node_path, false) {
        Err(_) => Err(Error::ClusterSizeZKNodeSetFailed),
        Ok(stat_opt) => match stat_opt {
            Some(_) => Ok(()),
            None => {
                match zk_client.create(parent_node_path, data, acl, CreateMode::Persistent) {
                    Err(_) => Err(Error::ClusterSizeZKNodeSetFailed),
                    Ok(_) => Ok(()),
                }
            }
        }
    }
}

}
