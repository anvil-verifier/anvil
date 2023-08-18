// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::exec::*;
use crate::pervasive_ext::to_view::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::exec::zookeepercluster::*;
use crate::zookeeper_controller::spec::zookeeper_api::{
    ZKAPIInputView, ZKAPIOutputView, ZKNodeResultView,
};
use core::time::Duration;
use deps_hack::zookeeper::{Acl, CreateMode, WatchedEvent, Watcher, ZkError, ZooKeeper};
use vstd::{prelude::*, string::*};

verus! {

pub type ZKNodeResult = Result<(), Error>;

impl ToView for ZKNodeResult {
    type V = ZKNodeResultView;
    spec fn to_view(&self) -> ZKNodeResultView {
        match self {
            Ok(_) => Ok(()),
            Err(_) => Err(Error::ClusterSizeZKNodeCreationFailed),
        }
    }
}

#[is_variant]
pub enum ZKAPIInput {
    ReconcileZKNode(String, String, String),
}

#[is_variant]
pub enum ZKAPIOutput {
    ReconcileZKNode(ZKNodeResult),
}

impl ToView for ZKAPIInput {
    type V = ZKAPIInputView;
    spec fn to_view(&self) -> ZKAPIInputView {
        match self {
            ZKAPIInput::ReconcileZKNode(zk_name, zk_namespace, replicas)
                => ZKAPIInputView::ReconcileZKNode(zk_name@, zk_namespace@, replicas@),
        }
    }
}

pub proof fn zk_support_input_to_view_match(zk_name: String, zk_namespace: String, replicas: String)
    ensures
        ZKAPIInput::ReconcileZKNode(zk_name, zk_namespace, replicas).to_view()
            == ZKAPIInputView::ReconcileZKNode(zk_name@, zk_namespace@, replicas@) {}

impl ToView for ZKAPIOutput {
    type V = ZKAPIOutputView;
    spec fn to_view(&self) -> ZKAPIOutputView {
        match self {
            ZKAPIOutput::ReconcileZKNode(result) => ZKAPIOutputView::ReconcileZKNode(result.to_view()),
        }
    }
}

pub proof fn zk_support_output_to_view_match(result: ZKNodeResult)
    ensures
        ZKAPIOutput::ReconcileZKNode(result).to_view() == ZKAPIOutputView::ReconcileZKNode(result.to_view()) {}

impl ZKAPIOutput {
    pub fn is_reconcile_zk_node(&self) -> (res: bool)
        ensures res <==> self.is_ReconcileZKNode(),
    {
        match self {
            ZKAPIOutput::ReconcileZKNode(_) => true,
        }
    }

    pub fn into_reconcile_zk_node(self) -> (result: ZKNodeResult)
        requires
            self.is_ReconcileZKNode(),
        ensures
            result == self.get_ReconcileZKNode_0(),
            result.is_Ok() <==> self.get_ReconcileZKNode_0().is_Ok(),
    {
        match self {
            ZKAPIOutput::ReconcileZKNode(result) => result,
        }
    }
}

pub struct ZKAPI {}

impl ExternalAPI<ZKAPIInput, ZKAPIOutput> for ZKAPI {
    #[verifier(external)]
    fn transition(input: ZKAPIInput) -> Option<ZKAPIOutput> {
        match input {
            ZKAPIInput::ReconcileZKNode(zk_name, zk_namespace, replicas)
                => Some(ZKAPIOutput::ReconcileZKNode(reconcile_zk_node(zk_name, zk_namespace, replicas))),
        }
    }
}

struct LoggingWatcher;
impl Watcher for LoggingWatcher {
    #[verifier(external)]
    fn handle(&self, e: WatchedEvent) {}
}

#[verifier(external)]
pub fn reconcile_zk_node(zk_name: String, zk_namespace: String, replicas: String) -> ZKNodeResult {
    let uri = &format!(
        "{}-client.{}.svc.cluster.local:2181",
        zk_name.as_rust_string_ref(),
        zk_namespace.as_rust_string_ref()
    );
    let zk_client = ZooKeeper::connect(uri, Duration::from_secs(10), LoggingWatcher);
    if zk_client.is_err() {
        return Err(Error::ClusterSizeZKNodeCreationFailed);
    }
    let zk_client = zk_client.unwrap();

    let parent_node_path = "/zookeeper-operator";
    ensure_parent_node_exists(parent_node_path, &zk_client)?;

    let node_path = &format!("{}/{}", parent_node_path, zk_name.as_rust_string_ref());
    let data = format!("CLUSTER_SIZE={}", replicas.as_rust_string_ref()).as_bytes().to_vec();
    match zk_client.exists(node_path, false) {
        Err(_) => Err(Error::ClusterSizeZKNodeCreationFailed),
        Ok(stat_opt) => match stat_opt {
            Some(stat) => {
                match zk_client.set_data(node_path, data, Some(stat.version)) {
                    Err(_) => Err(Error::ClusterSizeZKNodeCreationFailed),
                    Ok(_) => Ok(()),
                }
            }
            None => {
                match zk_client.create(node_path, data, Acl::open_unsafe().clone(), CreateMode::Persistent) {
                    Err(_) => Err(Error::ClusterSizeZKNodeCreationFailed),
                    Ok(_) => Ok(()),
                }
            }
        }
    }
}

#[verifier(external)]
pub fn ensure_parent_node_exists(parent_node_path: &str, zk_client: &ZooKeeper) -> ZKNodeResult {
    let data = Vec::new();
    match zk_client.exists(parent_node_path, false) {
        Err(_) => Err(Error::ClusterSizeZKNodeCreationFailed),
        Ok(stat_opt) => match stat_opt {
            Some(_) => Ok(()),
            None => {
                match zk_client.create(parent_node_path, data, Acl::open_unsafe().clone(), CreateMode::Persistent) {
                    Err(_) => Err(Error::ClusterSizeZKNodeCreationFailed),
                    Ok(_) => Ok(()),
                }
            }
        }
    }
}

}
