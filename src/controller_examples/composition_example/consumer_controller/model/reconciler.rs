// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::consumer_controller::trusted::{spec_types::*, step::*};
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{container::*, prelude::*};
use crate::reconciler::spec::{io::*, reconciler::*};
use vstd::{prelude::*, string::*};

verus! {

impl Reconciler<ConsumerView, EmptyAPI> for ConsumerReconciler {
    type T = ConsumerReconcileState;

    open spec fn reconcile_init_state() -> ConsumerReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(fb: ConsumerView, resp_o: Option<ResponseView<EmptyTypeView>>, state: ConsumerReconcileState)
    -> (ConsumerReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fb, resp_o, state)
    }

    open spec fn reconcile_done(state: ConsumerReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: ConsumerReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool { false /* expect nothing */ }
}

pub open spec fn reconcile_init_state() -> ConsumerReconcileState {
    ConsumerReconcileState {
        reconcile_step: ConsumerReconcileStepView::Init,
    }
}

pub open spec fn reconcile_done(state: ConsumerReconcileState) -> bool {
    match state.reconcile_step {
        ConsumerReconcileStepView::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: ConsumerReconcileState) -> bool {
    match state.reconcile_step {
        ConsumerReconcileStepView::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    consumer: ConsumerView, resp_o: Option<ResponseView<EmptyTypeView>>, state: ConsumerReconcileState
) -> (ConsumerReconcileState, Option<RequestView<EmptyTypeView>>) {
    let namespace = consumer.metadata.namespace.unwrap();
    match &state.reconcile_step {
        ConsumerReconcileStepView::Init => {
            let pod = make_pod(consumer);
            let req = APIRequest::CreateRequest(CreateRequest {
                namespace: namespace,
                obj: pod.marshal(),
            });
            let state_prime = ConsumerReconcileState {
                reconcile_step: ConsumerReconcileStepView::Done,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req)))
        },
        _ => {
            (state, None)
        }
    }
}

pub open spec fn make_pod(consumer: ConsumerView) -> (pod: PodView) {
    let pod = PodView {
        metadata: ObjectMetaView {
            name: Some(consumer.metadata.name.unwrap()),
            owner_references: Some(make_owner_references(consumer)),
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

pub open spec fn make_owner_references(consumer: ConsumerView) -> Seq<OwnerReferenceView> { seq![consumer.controller_owner_ref()] }

}
