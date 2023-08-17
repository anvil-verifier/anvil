// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::string_view::*;
use crate::pervasive_ext::to_view::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::exec::{common::*, zookeeper_api::*, zookeepercluster::*};
use crate::zookeeper_controller::spec::zookeeper_api::{
    ZKAPIInputView, ZKAPIOutputView, ZKNodeResultView,
};
use deps_hack::tokio::time::Duration;
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

struct LoggingWatcher;
impl Watcher for LoggingWatcher {
    #[verifier(external)]
    fn handle(&self, e: WatchedEvent) {}
}

#[verifier(external)]
pub fn reconcile_zk_node(zk_name: String, uri: String, replicas: String) -> ZKNodeResult {
    let zk_client = ZooKeeper::connect(
        uri.as_str().into_rust_str(),
        Duration::from_secs(10),
        LoggingWatcher,
    );
    if zk_client.is_err() {
        return Err(Error::ClusterSizeZKNodeCreationFailed);
    }
    let zk_client = zk_client.unwrap();
    let parent_node_path = "/zookeeper-operator";
    ensure_parent_node_exists(parent_node_path, &zk_client)?;

    let node_path = &format!("{}/{}", parent_node_path, zk_name.as_rust_string_ref());
    let data = format!("CLUSTER_SIZE={}", replicas.as_rust_string_ref()).as_bytes().to_vec();
    // let data = new_strlit("CLUSTER_SIZE=").to_string().concat(replicas.as_str()).as_str().into_rust_str().as_bytes().to_vec();

    match zk_client.exists(node_path, false) {
        Err(_) => Err(Error::ClusterSizeZKNodeCreationFailed),
        Ok(stat_opt) => match stat_opt {
            Some(stat) => {
                match zk_client.set_data(node_path, data, Some(stat.version)) {
                    Err(_) => Err(Error::ClusterSizeZKNodeCreationFailed),
                    Ok(_) => Ok(()),
                }
            },
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
    // let data = "".as_bytes().to_vec();
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
