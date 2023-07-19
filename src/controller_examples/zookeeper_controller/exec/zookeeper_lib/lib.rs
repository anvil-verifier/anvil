// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::to_view::*;
use crate::reconciler::exec::external::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::exec::zookeeper_lib::helper_funcs::*;
use crate::zookeeper_controller::exec::zookeepercluster::*;
use crate::zookeeper_controller::spec::zookeeper_lib::*;
use vstd::{prelude::*, string::*};

verus! {

#[is_variant]
pub enum ZKSupportInput {
    ReconcileZKNode(String,String,String),
}

#[is_variant]
pub enum ZKSupportOutput {
    ReconcileZKNode(ZKNodeResult),
}

impl ToView for ZKSupportInput {
    type V = ZKSupportInputView;
    spec fn to_view(&self) -> ZKSupportInputView {
        match self {
            ZKSupportInput::ReconcileZKNode(s1,s2,s3) => ZKSupportInputView::ReconcileZKNode(s1@,s2@,s3@),
        }
    }
}

pub proof fn to_view_is_other(s1: String, s2: String, s3: String)
    ensures 
        ZKSupportInput::ReconcileZKNode(s1,s2,s3).to_view() == ZKSupportInputView::ReconcileZKNode(s1@, s2@, s3@) {}


impl ToView for ZKSupportOutput {
    type V = ZKSupportOutputView;
    spec fn to_view(&self) -> ZKSupportOutputView {
        match self {
            ZKSupportOutput::ReconcileZKNode(result) => ZKSupportOutputView::ReconcileZKNode(ZKNodeResultView{res: result.res}),
        }
    }
}

pub proof fn same_result(result: ZKNodeResult)
    ensures 
        ZKSupportOutput::ReconcileZKNode(result).to_view() == ZKSupportOutputView::ReconcileZKNode(ZKNodeResultView{res: result.res}) {}

impl ZKSupportOutput {
    pub fn is_reconcile_zk_node(&self) -> (res: bool)
        ensures res <==> self.is_ReconcileZKNode(),
    {
        match self {
            ZKSupportOutput::ReconcileZKNode(_) => true,
        }
    }

    pub fn into_reconcile_zk_node(self) -> (result: ZKNodeResult)
        requires
            self.is_ReconcileZKNode(),
        ensures
            result == self.get_ReconcileZKNode_0(),
            result.res.is_Ok() <==> self.get_ReconcileZKNode_0().res.is_Ok(),
    {
        match self {
            ZKSupportOutput::ReconcileZKNode(result) => result,
        }
    }
}

pub struct ZKSupport {}

impl ExternalLibrary<ZKSupportInput, ZKSupportOutput> for ZKSupport {
    #[verifier(external)]
    fn process(input: ZKSupportInput) -> Option<ZKSupportOutput> {
        match input {
            ZKSupportInput::ReconcileZKNode(s1,s2,s3)
                => Option::Some(ZKSupportOutput::ReconcileZKNode(reconcile_zk_node(s1,s2,s3))),
        }
    }
}

}
