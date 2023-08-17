// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::exec::*;
use crate::pervasive_ext::to_view::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::exec::zookeeper_api::helper_funcs::*;
use crate::zookeeper_controller::exec::zookeepercluster::*;
use crate::zookeeper_controller::spec::zookeeper_api::{
    ZKAPIInputView, ZKAPIOutputView, ZKNodeResultView,
};
use vstd::{prelude::*, string::*};

verus! {

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
            ZKAPIInput::ReconcileZKNode(zk_name, uri, replicas)
                => ZKAPIInputView::ReconcileZKNode(zk_name@, uri@, replicas@),
        }
    }
}

pub proof fn zk_support_input_to_view_match(zk_name: String, uri: String, replicas: String)
    ensures
        ZKAPIInput::ReconcileZKNode(zk_name, uri, replicas).to_view()
            == ZKAPIInputView::ReconcileZKNode(zk_name@, uri@, replicas@) {}


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
            ZKAPIInput::ReconcileZKNode(zk_name, uri, replicas)
                => Some(ZKAPIOutput::ReconcileZKNode(reconcile_zk_node(zk_name, uri, replicas))),
        }
    }
}

}
