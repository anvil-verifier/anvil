use crate::zookeepercluster_types::*;

pub fn headless_service_name(zk: &ZookeeperCluster) -> String {
    zk.metadata.name.as_ref().unwrap().clone() + "-headless"
}

pub fn client_service_name(zk: &ZookeeperCluster) -> String {
    zk.metadata.name.as_ref().unwrap().clone() + "-client"
}

pub fn admin_server_service_name(zk: &ZookeeperCluster) -> String {
    zk.metadata.name.as_ref().unwrap().clone() + "-admin-server"
}

pub fn config_map_name(zk: &ZookeeperCluster) -> String {
    zk.metadata.name.as_ref().unwrap().clone() + "-configmap"
}

pub fn stateful_set_name(zk: &ZookeeperCluster) -> String {
    zk.metadata.name.as_ref().unwrap().clone()
}

pub fn zk_service_uri(zk: &ZookeeperCluster) -> String {
    format!(
        "{}.{}.svc.cluster.local:2181",
        client_service_name(zk),
        zk.metadata.namespace.as_ref().unwrap()
    )
}

pub fn cluster_size_zk_node_path(zk: &ZookeeperCluster) -> String {
    format!("/zookeeper-operator/{}", zk.metadata.name.as_ref().unwrap())
}
