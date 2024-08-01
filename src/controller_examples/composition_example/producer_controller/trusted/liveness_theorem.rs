// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{container::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::Step, message::*};
use crate::producer_controller::trusted::{spec_types::*, step::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub open spec fn liveness_theorem() -> bool { cluster_spec().entails(tla_forall(|producer: ProducerView| liveness(producer))) }

pub open spec fn cluster_spec() -> TempPred<PCluster> { PCluster::sm_spec() }

pub open spec fn liveness(producer: ProducerView) -> TempPred<PCluster> {
    always(lift_state(PCluster::desired_state_is(producer))).leads_to(always(lift_state(current_state_matches(producer))))
}

pub open spec fn current_state_matches(producer: ProducerView) -> StatePred<PCluster> {
    |s: PCluster| {
        let obj = s.resources()[pod_key(producer)];
        let pod = PodView::unmarshal(obj).get_Ok_0();
        &&& s.resources().contains_key(pod_key(producer))
        &&& PodView::unmarshal(obj).is_Ok()
        &&& pod.metadata.owner_references.get_Some_0().contains(producer.controller_owner_ref())
        &&& pod.metadata.labels.get_Some_0().contains_pair("producer_message"@, producer.spec.message)
        &&& pod.spec == Some(PodSpecView {
                containers: seq![ContainerView {
                    name: "nginx"@,
                    image: Some("nginx:1.14.2"@),
                    ports: Some(seq![ContainerPortView {
                        container_port: 80,
                        ..ContainerPortView::default()
                    }]),
                    ..ContainerView::default()
                }],
                ..PodSpecView::default()
            })
    }
}

pub open spec fn pod_key(producer: ProducerView) -> ObjectRef {
    ObjectRef {
        name: producer.metadata.name.get_Some_0(),
        namespace: producer.metadata.namespace.get_Some_0(),
        kind: Kind::PodKind,
    }
}

}
