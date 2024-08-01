// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{container::*, prelude::*};
use crate::producer_controller::trusted::{spec_types::*, step::*};
use crate::reconciler::spec::{io::*, reconciler::*};
use vstd::{prelude::*, string::*};

verus! {

impl Reconciler<ProducerView, EmptyAPI> for ProducerReconciler {
    type T = ProducerReconcileState;

    open spec fn reconcile_init_state() -> ProducerReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(fb: ProducerView, resp_o: Option<ResponseView<EmptyTypeView>>, state: ProducerReconcileState)
    -> (ProducerReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fb, resp_o, state)
    }

    open spec fn reconcile_done(state: ProducerReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: ProducerReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool { false /* expect nothing */ }
}

pub open spec fn reconcile_init_state() -> ProducerReconcileState {
    ProducerReconcileState {
        reconcile_step: ProducerReconcileStepView::Init,
    }
}

pub open spec fn reconcile_done(state: ProducerReconcileState) -> bool {
    match state.reconcile_step {
        ProducerReconcileStepView::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: ProducerReconcileState) -> bool {
    match state.reconcile_step {
        ProducerReconcileStepView::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    producer: ProducerView, resp_o: Option<ResponseView<EmptyTypeView>>, state: ProducerReconcileState
) -> (ProducerReconcileState, Option<RequestView<EmptyTypeView>>) {
    let namespace = producer.metadata.namespace.unwrap();
    match &state.reconcile_step {
        ProducerReconcileStepView::Init => {
            let pod = make_pod(producer);
            let req = APIRequest::CreateRequest(CreateRequest {
                namespace: namespace,
                obj: pod.marshal(),
            });
            let state_prime = ProducerReconcileState {
                reconcile_step: ProducerReconcileStepView::Done,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req)))
        },
        _ => {
            (state, None)
        }
    }
}

pub open spec fn make_pod(producer: ProducerView) -> (pod: PodView) {
    let pod = PodView {
        metadata: ObjectMetaView {
            name: Some(producer.metadata.name.unwrap()),
            owner_references: Some(seq![producer.controller_owner_ref()]),
            labels: Some(map!["producer_message"@ => producer.spec.message]),
            ..ObjectMetaView::default()
        },
        spec: Some(PodSpecView {
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
        }),
        ..PodView::default()
    };
    pod
}

}
