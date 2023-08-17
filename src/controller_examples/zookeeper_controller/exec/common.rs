// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::string_view::*;
use crate::zookeeper_controller::exec::zookeepercluster::*;
use crate::zookeeper_controller::spec::reconciler as zk_spec;
use vstd::{prelude::*, string::*};

verus! {

pub fn client_service_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
    ensures
        name@ == zk_spec::make_client_service_name(zk@),
{
    zk.metadata().name().unwrap().concat(new_strlit("-client"))
}

pub fn zk_service_uri(zk: &ZookeeperCluster) -> (uri: String)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
    ensures
        uri@ == zk_spec::zk_service_uri(zk@),
{
    client_service_name(zk)
    .concat(new_strlit("."))
    .concat(zk.metadata().namespace().unwrap().as_str())
    .concat(new_strlit(".svc.cluster.local:2181"))
}

}
