// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::exec::*;
use crate::zookeeper_controller::trusted::{
    step::*,
    zookeeper_api_spec::{
        ZKAPICreateResultView, ZKAPIExistsResultView, ZKAPIInputView, ZKAPIOutputView,
        ZKAPISetDataResultView,
    },
};
use core::time::Duration;
use deps_hack::zookeeper::{Acl, CreateMode, WatchedEvent, Watcher, ZkError, ZkResult, ZooKeeper};
use vstd::{prelude::*, string::*, view::*};

use vstd::pervasive::unreached;

verus! {

pub struct ZKAPIExistsResult {
    pub res: Result<Option<i32>, ZKAPIError>,
}

impl View for ZKAPIExistsResult {
    type V = ZKAPIExistsResultView;
    open spec fn view(&self) -> ZKAPIExistsResultView {
        match self.res {
            Ok(o) => match o {
                Some(i) => ZKAPIExistsResultView { res: Ok(Some(i as int)) },
                None => ZKAPIExistsResultView { res: Ok(None) },
            }
            Err(e) => ZKAPIExistsResultView { res: Err(e) },
        }
    }
}

pub struct ZKAPICreateResult {
    pub res: Result<(), ZKAPIError>,
}

impl View for ZKAPICreateResult {
    type V = ZKAPICreateResultView;
    open spec fn view(&self) -> ZKAPICreateResultView { ZKAPICreateResultView {res: self.res} }
}

pub struct ZKAPISetDataResult {
    pub res: Result<(), ZKAPIError>,
}

impl View for ZKAPISetDataResult {
    type V = ZKAPISetDataResultView;
    open spec fn view(&self) -> ZKAPISetDataResultView { ZKAPISetDataResultView {res: self.res} }
}

#[is_variant]
pub enum ZKAPIInput {
    ExistsRequest(String, String, i32, Vec<String>),
    CreateRequest(String, String, i32, Vec<String>, String),
    SetDataRequest(String, String, i32, Vec<String>, String, i32),
}

#[is_variant]
pub enum ZKAPIOutput {
    ExistsResponse(ZKAPIExistsResult),
    CreateResponse(ZKAPICreateResult),
    SetDataResponse(ZKAPISetDataResult),
}

impl View for ZKAPIInput {
    type V = ZKAPIInputView;
    open spec fn view(&self) -> ZKAPIInputView {
        match self {
            ZKAPIInput::ExistsRequest(name, namespace, port, path)
                => ZKAPIInputView::ExistsRequest(name@, namespace@, *port as int, path@.map_values(|s: String| s@)),
            ZKAPIInput::CreateRequest(name, namespace, port, path, data)
                => ZKAPIInputView::CreateRequest(name@, namespace@, *port as int, path@.map_values(|s: String| s@), data@),
            ZKAPIInput::SetDataRequest(name, namespace, port, path, data, version)
                => ZKAPIInputView::SetDataRequest(name@, namespace@, *port as int, path@.map_values(|s: String| s@), data@, *version as int),
        }
    }
}

impl View for ZKAPIOutput {
    type V = ZKAPIOutputView;
    open spec fn view(&self) -> ZKAPIOutputView {
        match self {
            ZKAPIOutput::ExistsResponse(result) => ZKAPIOutputView::ExistsResponse(result@),
            ZKAPIOutput::CreateResponse(result) => ZKAPIOutputView::CreateResponse(result@),
            ZKAPIOutput::SetDataResponse(result) => ZKAPIOutputView::SetDataResponse(result@),
        }
    }
}

pub struct ZKAPIShimLayer {}

#[verifier(external)]
impl ExternalAPIShimLayer for ZKAPIShimLayer {
    type Input = ZKAPIInput;
    type Output = ZKAPIOutput;
    fn call_external_api(input: ZKAPIInput) -> ZKAPIOutput {
        match input {
            ZKAPIInput::ExistsRequest(zk_name, zk_namespace, port, path)
                => ZKAPIOutput::ExistsResponse(zk_exists(zk_name, zk_namespace, port, path)),
            ZKAPIInput::CreateRequest(zk_name, zk_namespace, port, path, data)
                => ZKAPIOutput::CreateResponse(zk_create(zk_name, zk_namespace, port, path, data)),
            ZKAPIInput::SetDataRequest(zk_name, zk_namespace, port, path, data, version)
                => ZKAPIOutput::SetDataResponse(zk_set_data(zk_name, zk_namespace, port, path, data, version)),
        }
    }
}

struct NoopWatcher;

#[verifier(external)]
impl Watcher for NoopWatcher {
    fn handle(&self, _e: WatchedEvent) {}
}

#[verifier(external)]
pub fn set_up_zk_client(name: &String, namespace: &String, port: i32) -> ZkResult<ZooKeeper> {
    let uri = &format!("{}-client.{}.svc.cluster.local:{}", name.as_rust_string_ref(), namespace.as_rust_string_ref(), port);
    println!("Connecting to zk uri {} ...", uri);
    ZooKeeper::connect(uri, Duration::from_secs(10), NoopWatcher)
}

#[verifier(external)]
pub fn zk_exists(name: String, namespace: String, port: i32, path: Vec<String>) -> ZKAPIExistsResult {
    let result = ZKAPIExistsResult {res: zk_exists_internal(name, namespace, port, path)};
    match result.res {
        Err(_) => println!("Checking existence of zk node failed"),
        Ok(o) => {
            println!("Checking existence of zk node successfully");
            match o {
                Some(version) => println!("The zk node exists and version is {}", version),
                None => println!("The zk node does not exist"),
            }
        },
    }
    result
}

#[verifier(external)]
pub fn zk_exists_internal(name: String, namespace: String, port: i32, path: Vec<String>) -> Result<Option<i32>, ZKAPIError> {
    let zk_client = set_up_zk_client(&name, &namespace, port).map_err(|_e| ZKAPIError::ZKNodeExistsFailed)?;
    let path_as_string = format!("/{}", path.into_iter().map(|s: String| s.into_rust_string()).collect::<Vec<_>>().join("/"));
    println!("Checking existence of {} ...", &path_as_string);
    let exist_result = zk_client.exists(path_as_string.as_str(), false);
    let _ = zk_client.close();
    match exist_result {
        Err(e) => Err(ZKAPIError::ZKNodeExistsFailed),
        Ok(o) => match o {
            Some(stat) => Ok(Some(stat.version)),
            None => Ok(None),
        },
    }
}

#[verifier(external)]
pub fn zk_create(name: String, namespace: String, port: i32, path: Vec<String>, data: String) -> ZKAPICreateResult {
    let result = ZKAPICreateResult {res: zk_create_internal(name, namespace, port, path, data)};
    match result.res {
        Err(_) => println!("Create zk node failed"),
        Ok(_) => println!("Create zk node successfully"),
    }
    result
}

#[verifier(external)]
pub fn zk_create_internal(name: String, namespace: String, port: i32, path: Vec<String>, data: String) -> Result<(), ZKAPIError> {
    let zk_client = set_up_zk_client(&name, &namespace, port).map_err(|_e| ZKAPIError::ZKNodeCreateFailed)?;
    let path_as_string = format!("/{}", path.into_iter().map(|s: String| s.into_rust_string()).collect::<Vec<_>>().join("/"));
    let data_as_string = data.into_rust_string();
    println!("Creating {} {} ...", &path_as_string, &data_as_string);
    let create_result = zk_client.create(path_as_string.as_str(), data_as_string.as_str().as_bytes().to_vec(), Acl::open_unsafe().to_vec(), CreateMode::Persistent);
    let _ = zk_client.close();
    match create_result {
        Err(e) => match e {
            ZkError::NodeExists => Err(ZKAPIError::ZKNodeCreateAlreadyExists),
            _ => Err(ZKAPIError::ZKNodeCreateFailed),
        },
        Ok(_) => Ok(()),
    }
}

#[verifier(external)]
pub fn zk_set_data(name: String, namespace: String, port: i32, path: Vec<String>, data: String, version: i32) -> ZKAPISetDataResult {
    let result = ZKAPISetDataResult {res: zk_set_data_internal(name, namespace, port, path, data, version)};
    match result.res {
        Err(_) => println!("Set zk node failed"),
        Ok(_) => println!("Set zk node successfully"),
    }
    result
}

#[verifier(external)]
pub fn zk_set_data_internal(name: String, namespace: String, port: i32, path: Vec<String>, data: String, version: i32) -> Result<(), ZKAPIError> {
    let zk_client = set_up_zk_client(&name, &namespace, port).map_err(|_e| ZKAPIError::ZKNodeSetDataFailed)?;
    let path_as_string = format!("/{}", path.into_iter().map(|s: String| s.into_rust_string()).collect::<Vec<_>>().join("/"));
    let data_as_string = data.into_rust_string();
    println!("Setting {} {} {} ...", &path_as_string, &data_as_string, version);
    let set_result = zk_client.set_data(path_as_string.as_str(), data_as_string.as_str().as_bytes().to_vec(), Some(version));
    let _ = zk_client.close();
    match set_result {
        Err(_) => Err(ZKAPIError::ZKNodeSetDataFailed),
        Ok(_) => Ok(()),
    }
}

}
