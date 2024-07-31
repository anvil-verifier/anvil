// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::consumer_controller::trusted::{spec_types::*, step::*};
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{container::*, prelude::*};
use crate::producer_controller::trusted::spec_types::*;
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
            let req = APIRequest::GetRequest(GetRequest {
                key: ObjectRef {
                    kind: ProducerView::kind(),
                    name: consumer.metadata.name->Some_0,
                    namespace: consumer.metadata.namespace->Some_0,
                }
            });
            let state_prime = ConsumerReconcileState {
                reconcile_step: ConsumerReconcileStepView::AfterGetProducer,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req)))
        },
        ConsumerReconcileStepView::AfterGetProducer => {
            if is_some_k_get_resp!(resp_o) {
                let res = extract_some_k_get_resp!(resp_o);
                if res is Ok {
                    let req = APIRequest::GetRequest(GetRequest {
                        key: ObjectRef {
                            kind: PodView::kind(),
                            name: consumer.metadata.name->Some_0,
                            namespace: consumer.metadata.namespace->Some_0,
                        }
                    });
                    let state_prime = ConsumerReconcileState {
                        reconcile_step: ConsumerReconcileStepView::AfterGetPod,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req)))
                } else if res.get_Err_0() is ObjectNotFound {
                    let producer = make_producer(consumer);
                    let req = APIRequest::CreateRequest(CreateRequest {
                        namespace: consumer.metadata.namespace->Some_0,
                        obj: producer.marshal(),
                    });
                    let state_prime = ConsumerReconcileState {
                        reconcile_step: ConsumerReconcileStepView::AfterCreateProducer,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req)))
                } else {
                    (error_state(state), None)
                }
            } else {
                (error_state(state), None)
            }
        },
        ConsumerReconcileStepView::AfterCreateProducer => {
            if is_some_k_create_resp!(resp_o) {
                let res = extract_some_k_create_resp!(resp_o);
                if res is Ok {
                    let req = APIRequest::GetRequest(GetRequest {
                        key: ObjectRef {
                            kind: PodView::kind(),
                            name: consumer.metadata.name->Some_0,
                            namespace: consumer.metadata.namespace->Some_0,
                        }
                    });
                    let state_prime = ConsumerReconcileState {
                        reconcile_step: ConsumerReconcileStepView::AfterGetPod,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req)))
                } else {
                    (error_state(state), None)
                }
            } else {
                (error_state(state), None)
            }
        },
        ConsumerReconcileStepView::AfterGetPod => {
            if is_some_k_get_resp!(resp_o) {
                let res = extract_some_k_get_resp!(resp_o);
                if res is Ok {
                    let old_pod_unmarshal_res = PodView::unmarshal(res.get_Ok_0());
                    if old_pod_unmarshal_res is Ok {
                        let old_pod = old_pod_unmarshal_res.get_Ok_0();
                        let new_pod = update_pod(consumer, old_pod);
                        let req = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: consumer.metadata.namespace->Some_0,
                            name: consumer.metadata.name->Some_0,
                            obj: new_pod.marshal(),
                        });
                        let state_prime = ConsumerReconcileState {
                            reconcile_step: ConsumerReconcileStepView::AfterUpdatePod,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req)))
                    } else {
                        (error_state(state), None)
                    }
                } else {
                    (error_state(state), None)
                }
            } else {
                (error_state(state), None)
            }
        },
        ConsumerReconcileStepView::AfterUpdatePod => {
            if is_some_k_update_resp!(resp_o) {
                let res = extract_some_k_update_resp!(resp_o);
                if res is Ok {
                    let state_prime = ConsumerReconcileState {
                        reconcile_step: ConsumerReconcileStepView::Done,
                        ..state
                    };
                    (state_prime, None)
                } else {
                    (error_state(state), None)
                }
            } else {
                (error_state(state), None)
            }
        }
        _ => {
            (state, None)
        }
    }
}

pub open spec fn error_state(state: ConsumerReconcileState) -> (state_prime: ConsumerReconcileState) {
    ConsumerReconcileState {
        reconcile_step: ConsumerReconcileStepView::Error,
        ..state
    }
}

pub open spec fn update_pod(consumer: ConsumerView, pod: PodView) -> PodView {
    PodView {
        metadata: ObjectMetaView {
            labels: Some(if pod.metadata.labels.is_None() {
                map!["consumer_message"@ => consumer.spec.message]
            } else {
                pod.metadata.labels.get_Some_0().insert("consumer_message"@, consumer.spec.message)
            }),
            ..pod.metadata
        },
        ..pod
    }
}

pub open spec fn make_producer(consumer: ConsumerView) -> ProducerView {
    ProducerView {
        metadata: ObjectMetaView {
            name: Some(consumer.metadata.name.unwrap()),
            owner_references: Some(seq![consumer.controller_owner_ref()]),
            ..ObjectMetaView::default()
        },
        spec: ProducerSpecView {
            message: consumer.spec.message,
        },
        ..ProducerView::default()
    }
}

}
