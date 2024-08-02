// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::consumer_controller::trusted::{spec_types::*, step::*};
use crate::kubernetes_api_objects::spec::{container::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::Step, message::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub open spec fn liveness_theorem() -> bool { cluster_spec().entails(tla_forall(|consumer: ConsumerView| liveness(consumer))) }

pub open spec fn cluster_spec() -> TempPred<CCluster> { CCluster::sm_spec() }

pub open spec fn liveness(consumer: ConsumerView) -> TempPred<CCluster> {
    always(lift_state(CCluster::desired_state_is(consumer))).leads_to(always(lift_state(current_state_matches(consumer))))
}

pub open spec fn current_state_matches(consumer: ConsumerView) -> StatePred<CCluster> {
    |s: CCluster| {
        let obj = s.resources()[pod_key(consumer)];
        let pod = PodView::unmarshal(obj).get_Ok_0();
        &&& s.resources().contains_key(pod_key(consumer))
        &&& PodView::unmarshal(obj).is_Ok()
        &&& pod.metadata.labels.get_Some_0().contains_pair("consumer_message"@, consumer.spec.message)
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

pub open spec fn pod_key(consumer: ConsumerView) -> ObjectRef {
    ObjectRef {
        name: consumer.metadata.name.get_Some_0(),
        namespace: consumer.metadata.namespace.get_Some_0(),
        kind: Kind::PodKind,
    }
}

}
