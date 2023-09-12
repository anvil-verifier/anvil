// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::exec::*;
use crate::pervasive_ext::to_view::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::zookeeper_api::{
    ZKAPICreateResultView, ZKAPIExistsResultView, ZKAPIInputView, ZKAPIOutputView,
    ZKAPISetDataResultView,
};
use core::time::Duration;
use deps_hack::zookeeper::{Acl, CreateMode, WatchedEvent, Watcher, ZkError, ZkResult, ZooKeeper};
use vstd::{prelude::*, string::*};

use vstd::pervasive::unreached;

verus! {

pub struct ZKAPIExistsResult {
    pub res: Result<Option<i32>, Error>,
}

impl ToView for ZKAPIExistsResult {
    type V = ZKAPIExistsResultView;
    open spec fn to_view(&self) -> ZKAPIExistsResultView {
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
    pub res: Result<(), Error>,
}

impl ToView for ZKAPICreateResult {
    type V = ZKAPICreateResultView;
    open spec fn to_view(&self) -> ZKAPICreateResultView {
        ZKAPICreateResultView {res: self.res}
    }
}

pub struct ZKAPISetDataResult {
    pub res: Result<(), Error>,
}

impl ToView for ZKAPISetDataResult {
    type V = ZKAPISetDataResultView;
    open spec fn to_view(&self) -> ZKAPISetDataResultView {
        ZKAPISetDataResultView {res: self.res}
    }
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

impl ToView for ZKAPIInput {
    type V = ZKAPIInputView;
    open spec fn to_view(&self) -> ZKAPIInputView {
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

impl ToView for ZKAPIOutput {
    type V = ZKAPIOutputView;
    open spec fn to_view(&self) -> ZKAPIOutputView {
        match self {
            ZKAPIOutput::ExistsResponse(result) => ZKAPIOutputView::ExistsResponse(result.to_view()),
            ZKAPIOutput::CreateResponse(result) => ZKAPIOutputView::CreateResponse(result.to_view()),
            ZKAPIOutput::SetDataResponse(result) => ZKAPIOutputView::SetDataResponse(result.to_view()),
        }
    }
}

impl ZKAPIOutput {
    pub fn is_exists_response(&self) -> (res: bool)
        ensures
            res == self.is_ExistsResponse(),
    {
        match self {
            ZKAPIOutput::ExistsResponse(_) => true,
            _ => false,
        }
    }

    pub fn unwrap_exists_response(self) -> (result: ZKAPIExistsResult)
        requires
            self.is_ExistsResponse(),
        ensures
            result == self.get_ExistsResponse_0(),
    {
        match self {
            ZKAPIOutput::ExistsResponse(result) => result,
            _ => unreached(),
        }
    }

    pub fn is_create_response(&self) -> (res: bool)
        ensures
            res == self.is_CreateResponse(),
    {
        match self {
            ZKAPIOutput::CreateResponse(_) => true,
            _ => false,
        }
    }

    pub fn unwrap_create_response(self) -> (result: ZKAPICreateResult)
        requires
            self.is_CreateResponse(),
        ensures
            result == self.get_CreateResponse_0(),
    {
        match self {
            ZKAPIOutput::CreateResponse(result) => result,
            _ => unreached(),
        }
    }

    pub fn is_set_data_response(&self) -> (res: bool)
        ensures
            res == self.is_SetDataResponse(),
    {
        match self {
            ZKAPIOutput::SetDataResponse(_) => true,
            _ => false,
        }
    }

    pub fn unwrap_set_data_response(self) -> (result: ZKAPISetDataResult)
        requires
            self.is_SetDataResponse(),
        ensures
            result == self.get_SetDataResponse_0(),
    {
        match self {
            ZKAPIOutput::SetDataResponse(result) => result,
            _ => unreached(),
        }
    }
}

pub struct ZKAPIShimLayer {}

impl ExternalAPIShimLayer<ZKAPIInput, ZKAPIOutput> for ZKAPIShimLayer {
    #[verifier(external)]
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

struct LoggingWatcher;
impl Watcher for LoggingWatcher {
    #[verifier(external)]
    fn handle(&self, e: WatchedEvent) {}
}

#[verifier(external)]
pub fn set_up_zk_client(name: &String, namespace: &String, port: i32) -> ZkResult<ZooKeeper> {
    let uri = &format!("{}-client.{}.svc.cluster.local:{}", name.as_rust_string_ref(), namespace.as_rust_string_ref(), port);
    println!("Connecting to zk uri {} ...", uri);
    ZooKeeper::connect(uri, Duration::from_secs(10), LoggingWatcher)
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
pub fn zk_exists_internal(name: String, namespace: String, port: i32, path: Vec<String>) -> Result<Option<i32>, Error> {
    let zk_client = set_up_zk_client(&name, &namespace, port).map_err(|e| Error::ZKNodeExistsFailed)?;
    let path_as_string = format!("/{}", path.into_iter().map(|s: String| s.into_rust_string()).collect::<Vec<_>>().join("/"));
    println!("Checking existence of {} ...", &path_as_string);
    match zk_client.exists(path_as_string.as_str(), false) {
        Err(e) => Err(Error::ZKNodeExistsFailed),
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
pub fn zk_create_internal(name: String, namespace: String, port: i32, path: Vec<String>, data: String) -> Result<(), Error> {
    let zk_client = set_up_zk_client(&name, &namespace, port).map_err(|e| Error::ZKNodeCreateFailed)?;
    let path_as_string = format!("/{}", path.into_iter().map(|s: String| s.into_rust_string()).collect::<Vec<_>>().join("/"));
    let data_as_string = data.into_rust_string();
    println!("Creating {} {} ...", &path_as_string, &data_as_string);
    match zk_client.create(path_as_string.as_str(), data_as_string.as_str().as_bytes().to_vec(), Acl::open_unsafe().to_vec(), CreateMode::Persistent) {
        Err(e) => match e {
            ZkError::NodeExists => Err(Error::ZKNodeCreateAlreadyExists),
            _ => Err(Error::ZKNodeCreateFailed),
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
pub fn zk_set_data_internal(name: String, namespace: String, port: i32, path: Vec<String>, data: String, version: i32) -> Result<(), Error> {
    let zk_client = set_up_zk_client(&name, &namespace, port).map_err(|e| Error::ZKNodeSetDataFailed)?;
    let path_as_string = format!("/{}", path.into_iter().map(|s: String| s.into_rust_string()).collect::<Vec<_>>().join("/"));
    let data_as_string = data.into_rust_string();
    println!("Setting {} {} {} ...", &path_as_string, &data_as_string, version);
    match zk_client.set_data(path_as_string.as_str(), data_as_string.as_str().as_bytes().to_vec(), Some(version)) {
        Err(_) => Err(Error::ZKNodeSetDataFailed),
        Ok(_) => Ok(()),
    }
}

}
