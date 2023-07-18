// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::reconciler::exec::external::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::exec::zookeeper_lib::helper_funcs;
use crate::zookeeper_controller::exec::zookeepercluster::*;
use crate::zookeeper_controller::spec::zookeeper_lib::*;
use vstd::{prelude::*, string::*};

verus! {

pub enum ZKSupportInput {
    ReconcileZKNode(ZookeeperCluster),
}

pub enum ZKSupportOutput {
    ReconcileZKNode(Result<(), Error>),
}

impl View for ZKSupportInput {
    type V = ZKSupportInputView;
    spec fn view(&self) -> ZKSupportInputView {
        match self {
            ZKSupportInput::ReconcileZKNode(zk) => ZKSupportInputView::ReconcileZKNode(zk@),
        }
    }
}

impl View for ZKSupportOutput {
    type V = ZKSupportOutputView;
    spec fn view(&self) -> ZKSupportOutputView {
        match self {
            ZKSupportOutput::ReconcileZKNode(res) => ZKSupportOutputView::ReconcileZKNode(*res),
        }
    }
}

// pub open spec fn

pub struct ZKSupport {}

impl ExternalLibrary<ZKSupportInput, ZKSupportOutput> for ZKSupport {
    #[verifier(external)]
    fn process(input: ZKSupportInput) -> Option<ZKSupportOutput> {
        match input {
            ZKSupportInput::ReconcileZKNode(zk)
                => Option::Some(ZKSupportOutput::ReconcileZKNode(helper_funcs::reconcile_zk_node(&zk))),
        }
    }
}

}
