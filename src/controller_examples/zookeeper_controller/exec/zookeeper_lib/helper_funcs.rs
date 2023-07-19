// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::string_view::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::exec::{common::*, zookeeper_lib::*, zookeepercluster::*};
use deps_hack::tokio::time::Duration;
use deps_hack::zookeeper::{Acl, CreateMode, WatchedEvent, Watcher, ZkError, ZooKeeper};
use vstd::{prelude::*, string::*};

verus! {

struct LoggingWatcher;
impl Watcher for LoggingWatcher {
    #[verifier(external)]
    fn handle(&self, e: WatchedEvent) {}
}

#[verifier(external)]
pub fn reconcile_zk_node(zk: &ZookeeperCluster) -> Result<(), Error>
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
{
    let path = cluster_size_zk_node_path(&zk);
    let zk_client = ZooKeeper::connect(
        zk_service_uri(&zk).as_str().into_rust_str(),
        Duration::from_secs(10),
        LoggingWatcher,
    );
    if zk_client.is_err() {
        return Result::Err(Error::ClusterSizeZKNodeCreationFailed);
    }
    let zk_client = zk_client.unwrap();
    let path_look_up = zk_client.exists(path.as_rust_string_ref(), false);
    if path_look_up.is_err() {
        return Result::Err(Error::ClusterSizeZKNodeCreationFailed);
    }
    let path_look_up = path_look_up.unwrap();
    match path_look_up {
        Some(_) => Ok(()),
        None => {
            // First create the parent node
            if zk_client
                .create(
                    "/zookeeper-operator",
                    new_strlit("CLUSTER_SIZE=").to_string().concat(i32_to_string(zk.spec().replicas()).as_str())
                        .as_str()
                        .as_bytes()
                        .to_vec(),
                    Acl::open_unsafe().clone(),
                    CreateMode::Persistent,
                ).is_err() {
                return Result::Err(Error::ClusterSizeZKNodeCreationFailed);
            }
            if zk_client
                .create(
                    path.as_rust_string_ref(),
                    new_strlit("CLUSTER_SIZE=").to_string().concat(i32_to_string(zk.spec().replicas()).as_str())
                        .as_str()
                        .as_bytes()
                        .to_vec(),
                    Acl::open_unsafe().clone(),
                    CreateMode::Persistent,
                ).is_err() {
                return Result::Err(Error::ClusterSizeZKNodeCreationFailed);
            }
            return Ok(());
        }
    }
}

}
