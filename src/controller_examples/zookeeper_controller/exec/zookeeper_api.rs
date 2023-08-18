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

pub struct ZKAPIResult {
    pub res: Result<(), Error>,
}

#[is_variant]
pub enum ZKAPIInput {
    SetZKNodeRequest(String, String, String),
}

#[is_variant]
pub enum ZKAPIOutput {
    SetZKNodeResponse(ZKAPIResult),
}

impl ToView for ZKAPIInput {
    type V = ZKAPIInputView;
    open spec fn to_view(&self) -> ZKAPIInputView {
        match self {
            ZKAPIInput::SetZKNodeRequest(zk_name, zk_namespace, replicas)
                => ZKAPIInputView::SetZKNodeRequest(zk_name@, zk_namespace@, replicas@),
        }
    }
}

impl ToView for ZKAPIOutput {
    type V = ZKAPIOutputView;
    open spec fn to_view(&self) -> ZKAPIOutputView {
        match self {
            ZKAPIOutput::SetZKNodeResponse(result) => ZKAPIOutputView::SetZKNodeResponse(ZKAPIResultView {res: result.res}),
        }
    }
}

impl ZKAPIOutput {
    pub fn is_set_zk_node_response(&self) -> (res: bool)
        ensures
            res == self.is_SetZKNodeResponse(),
    {
        match self {
            ZKAPIOutput::SetZKNodeResponse(_) => true,
        }
    }

    pub fn into_set_zk_node_response(self) -> (result: ZKAPIResult)
        requires
            self.is_SetZKNodeResponse(),
        ensures
            result == self.get_SetZKNodeResponse_0(),
    {
        match self {
            ZKAPIOutput::SetZKNodeResponse(result) => result,
        }
    }
}

pub struct ZKAPI {}

impl ExternalAPI<ZKAPIInput, ZKAPIOutput> for ZKAPI {
    #[verifier(external)]
    fn transition(input: ZKAPIInput) -> Option<ZKAPIOutput> {
        match input {
            ZKAPIInput::SetZKNodeRequest(zk_name, zk_namespace, replicas)
                => Some(ZKAPIOutput::SetZKNodeResponse(set_zk_node(zk_name, zk_namespace, replicas))),
        }
    }
}

struct LoggingWatcher;
impl Watcher for LoggingWatcher {
    #[verifier(external)]
    fn handle(&self, e: WatchedEvent) {}
}

#[verifier(external)]
pub fn set_zk_node(zk_name: String, zk_namespace: String, replicas: String) -> ZKAPIResult {
    ZKAPIResult {res: set_zk_node_internal(zk_name, zk_namespace, replicas)}
}

#[verifier(external)]
pub fn set_zk_node_internal(zk_name: String, zk_namespace: String, replicas: String) -> Result<(), Error> {
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
pub fn ensure_parent_node_exists(parent_node_path: &str, zk_client: &ZooKeeper) -> Result<(), Error> {
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
