// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::v_replica_set_controller::trusted::{spec_types::*, step::*};
use vstd::{prelude::*, string::*};

verus! {

impl Reconciler<VReplicaSetView, EmptyAPI> for VReplicaSetReconciler {
    type T = VReplicaSetReconcileState;

    open spec fn reconcile_init_state() -> VReplicaSetReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(fb: VReplicaSetView, resp_o: Option<ResponseView<EmptyTypeView>>, state: VReplicaSetReconcileState)
    -> (VReplicaSetReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fb, resp_o, state)
    }

    open spec fn reconcile_done(state: VReplicaSetReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: VReplicaSetReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool { false /* expect nothing */ }
}

pub open spec fn reconcile_init_state() -> VReplicaSetReconcileState {
    VReplicaSetReconcileState {
        reconcile_step: VReplicaSetReconcileStep::Init,
        filtered_pods: None,
    }
}

pub open spec fn reconcile_done(state: VReplicaSetReconcileState) -> bool {
    match state.reconcile_step {
        VReplicaSetReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: VReplicaSetReconcileState) -> bool {
    match state.reconcile_step {
        VReplicaSetReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    v_replica_set: VReplicaSetView, resp_o: Option<ResponseView<EmptyTypeView>>, state: VReplicaSetReconcileState
) -> (VReplicaSetReconcileState, Option<RequestView<EmptyTypeView>>) {
    let namespace = v_replica_set.metadata.namespace.unwrap();
    match &state.reconcile_step {
        VReplicaSetReconcileStep::Init => {
            let req = APIRequest::ListRequest(ListRequest {
                kind: PodView::kind(),
                namespace: namespace,
            });
            let state_prime = VReplicaSetReconcileState {
                reconcile_step: VReplicaSetReconcileStep::AfterListPods,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req)))
        },
        VReplicaSetReconcileStep::AfterListPods => {
            if !(resp_o.is_Some() && resp_o.get_Some_0().is_KResponse()
            && resp_o.get_Some_0().get_KResponse_0().is_ListResponse()
            && resp_o.get_Some_0().get_KResponse_0().get_ListResponse_0().res.is_ok()) {
                (error_state(state), None)
            } else {
                let objs = resp_o.unwrap().get_KResponse_0().get_ListResponse_0().res.unwrap();
                let pods_or_none = objects_to_pods(objs);
                if pods_or_none.is_none() {
                    (error_state(state), None)
                } else {
                    let pods = pods_or_none.unwrap();
                    let filtered_pods = filter_pods(pods, v_replica_set);
                    let replicas = v_replica_set.spec.replicas.unwrap_or(0);
                    if replicas < 0 {
                        (error_state(state), None)
                    } else {
                        let desired_replicas: usize = replicas as usize;
                        if filtered_pods.len() == desired_replicas {
                            let state_prime = VReplicaSetReconcileState {
                                reconcile_step: VReplicaSetReconcileStep::Done,
                                ..state
                            };
                            (state_prime, None)
                        } else if filtered_pods.len() < desired_replicas {
                            let diff =  desired_replicas - filtered_pods.len();
                            let pod = make_pod(v_replica_set);
                            let req = APIRequest::CreateRequest(CreateRequest {
                                namespace: namespace,
                                obj: pod.marshal(),
                            });
                            let state_prime = VReplicaSetReconcileState {
                                reconcile_step: VReplicaSetReconcileStep::AfterCreatePod((diff - 1) as usize),
                                ..state
                            };
                            (state_prime, Some(RequestView::KRequest(req)))
                        } else {
                            let diff = filtered_pods.len() - desired_replicas;
                            let pod_name_or_none = filtered_pods[diff - 1].metadata.name;
                            if pod_name_or_none.is_none() {
                                (error_state(state), None)
                            } else {
                                let req = APIRequest::DeleteRequest(DeleteRequest {
                                    key: ObjectRef {
                                        kind: PodView::kind(),
                                        name: pod_name_or_none.unwrap(),
                                        namespace: namespace,
                                    }
                                });
                                let state_prime = VReplicaSetReconcileState {
                                    reconcile_step: VReplicaSetReconcileStep::AfterDeletePod((diff - 1) as usize),
                                    filtered_pods: Some(filtered_pods),
                                    ..state
                                };
                                (state_prime, Some(RequestView::KRequest(req)))
                            }
                        }
                    }
                }
            }
        },
        VReplicaSetReconcileStep::AfterCreatePod(diff) => {
            let diff = *diff;
            if !(resp_o.is_Some() && resp_o.get_Some_0().is_KResponse()
            && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res.is_ok()) {
                (error_state(state), None)
            } else if diff == 0 {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let pod = make_pod(v_replica_set);
                let req = APIRequest::CreateRequest(CreateRequest {
                    namespace: namespace,
                    obj: pod.marshal(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterCreatePod((diff - 1) as usize),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req)))
            }
        },
        VReplicaSetReconcileStep::AfterDeletePod(diff) => {
            let diff = *diff;
            if !(resp_o.is_Some() && resp_o.get_Some_0().is_KResponse()
            && resp_o.get_Some_0().get_KResponse_0().is_DeleteResponse()
            && resp_o.get_Some_0().get_KResponse_0().get_DeleteResponse_0().res.is_ok()) {
                (error_state(state), None)
            } else if diff == 0 {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                if state.filtered_pods.is_none() {
                    (error_state(state), None)
                } else if diff > state.filtered_pods.unwrap().len() {
                    (error_state(state), None)
                } else {
                    let pod_name_or_none = state.filtered_pods.unwrap()[diff - 1].metadata.name;
                    if pod_name_or_none.is_none() {
                        (error_state(state), None)
                    } else {
                        let req = APIRequest::DeleteRequest(DeleteRequest {
                            key: ObjectRef {
                                kind: PodView::kind(),
                                name: pod_name_or_none.unwrap(),
                                namespace: namespace,
                            }
                        });
                        let state_prime = VReplicaSetReconcileState {
                            reconcile_step: VReplicaSetReconcileStep::AfterDeletePod((diff - 1) as usize),
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req)))
                    }
                }
            }
        },
        _ => {
            (state, None)
        }
    }
}

pub open spec fn error_state(state: VReplicaSetReconcileState) -> (state_prime: VReplicaSetReconcileState)
{
    VReplicaSetReconcileState {
        reconcile_step: VReplicaSetReconcileStep::Error,
        ..state
    }
}

pub open spec fn objects_to_pods(objs: Seq<DynamicObjectView>) -> (pods_or_none: Option<Seq<PodView>>) {
    if objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() != 0 {
        None
    } else {
        Some(objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()))
    }
}

pub open spec fn filter_pods(pods: Seq<PodView>, v_replica_set: VReplicaSetView) -> (filtered_pods: Seq<PodView>) {
    pods.filter(|pod: PodView|
        pod.metadata.owner_references_contains(v_replica_set.controller_owner_ref())
        && v_replica_set.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        && pod.metadata.deletion_timestamp.is_None())
}

pub open spec fn make_pod(v_replica_set: VReplicaSetView) -> (pod: PodView) {
    let template = v_replica_set.spec.template.unwrap();
    let pod = PodView::default();
    let pod = PodView {
        spec: template.spec,
        metadata: {
            let tm = template.metadata.unwrap();
            let metadata = ObjectMetaView::default();
            let metadata = ObjectMetaView {
                labels: tm.labels,
                annotations: tm.annotations,
                finalizers: tm.finalizers,
                ..metadata
            };
            let metadata = metadata.set_generate_name(
                v_replica_set.metadata.name.unwrap() + "-"@
            );
            let metadata = metadata.set_owner_references(
                make_owner_references(v_replica_set)
            );
            metadata
        },
        ..pod
    };
    pod
}

pub open spec fn make_owner_references(v_replica_set: VReplicaSetView) -> Seq<OwnerReferenceView> { seq![v_replica_set.controller_owner_ref()] }

}
