// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

use std::collections::{BTreeMap, HashMap};

#[derive(PartialEq, Debug)]
pub enum ControllerState {
    Init,
    S1,
    S2,
    Retry,
    Done,
}

pub enum APIOp {
    Noop,
    GetConfigMap{name:String, namespace:String},
    CreateConfigMap{name:String, namespace:String, configmapl:ConfigMapL}
}

pub struct APIOpResponse {
    pub success: bool
}

pub struct APIOpRequest {
    pub api_op: APIOp
}

pub struct ClusterState {
    pub configmaps: HashMap<String, Option<ConfigMapL>>,
}

pub struct ConfigMapL {
    pub name: Option<String>,

    pub namespace: Option<String>,
    
    pub data: Option<BTreeMap<String, String>>,
}

pub enum StringL {
    Configmap1,
    Configmap2,
    Default,
    DefaultConfigmap1,
}

// #[verifier(external_body)]
pub fn translate_stringl_to_string(stringl:StringL) -> String {
    match stringl {
        StringL::Configmap1 => "configmap-1".to_string(),
        StringL::Configmap2 => "configmap-2".to_string(),
        StringL::Default => "default".to_string(),
        StringL::DefaultConfigmap1 => "default/configmap-1".to_string(),
    }
}

pub fn controller_logic(controller_state: &ControllerState, cluster_state: &ClusterState, api_result: &APIOpResponse) -> (ControllerState, APIOpRequest) {
    if !api_result.success {
        (ControllerState::Retry, APIOpRequest{api_op:APIOp::Noop})
    } else {
        match controller_state {
            ControllerState::Init => (
                ControllerState::S1, APIOpRequest{
                    api_op:APIOp::GetConfigMap{
                        name:translate_stringl_to_string(StringL::Configmap1),
                        namespace:translate_stringl_to_string(StringL::Default),
                    }
                }
            ),
            ControllerState::S1 => {
                match cluster_state.configmaps.get(&translate_stringl_to_string(StringL::DefaultConfigmap1)) {
                    Some(o) => {
                        match o {
                            Some(_) => (ControllerState::Done, APIOpRequest{api_op:APIOp::Noop}),
                            None => (
                                ControllerState::S2, APIOpRequest{
                                    api_op:APIOp::CreateConfigMap{
                                        name:translate_stringl_to_string(StringL::Configmap1), 
                                        namespace:translate_stringl_to_string(StringL::Default), 
                                        configmapl:ConfigMapL{
                                            name: Some(translate_stringl_to_string(StringL::Configmap1)),
                                            namespace: Some(translate_stringl_to_string(StringL::Default)),
                                            data: Some(BTreeMap::new()),
                                        },
                                    }
                                }
                            ),
                        }
                    },
                    None => panic!("should never get here"),
                }
            },
            ControllerState::S2 => (
                ControllerState::Done, APIOpRequest{
                    api_op:APIOp::CreateConfigMap{
                        name:translate_stringl_to_string(StringL::Configmap2), 
                        namespace:translate_stringl_to_string(StringL::Default), 
                        configmapl:ConfigMapL{
                            name: Some(translate_stringl_to_string(StringL::Configmap2)),
                            namespace: Some(translate_stringl_to_string(StringL::Default)),
                            data: Some(BTreeMap::new()),
                        },
                    }
                }
            ),
            ControllerState::Retry => panic!("should never get here"),
            ControllerState::Done => panic!("should never get here"),
        }
    }
}

