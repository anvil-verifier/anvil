// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*, error::*, resource::*};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllersState,
    client::types::ClientState,
    controller::common::{ControllerState, OngoingReconcile},
    external_api::types::ExternalAPIState,
    kubernetes_api::common::KubernetesAPIState,
    message::*,
    network::types::NetworkState,
};
use crate::reconciler::spec::reconciler::Reconciler;
use vstd::{multiset::*, prelude::*};

verus! {

/// The Cluster struct is an abstraction of the compound state machine of the kubernetes cluster. It contains a number of
/// fields for describing the state of those components as well as all the methods of the specifications and lemmas of the
/// system.
///
/// It takes three generics, which should be essentially one: R is the type of Reconciler and K and E are the two generics
/// fed to R.
///
/// By using such a struct, we don't have to let all the functions carry the generics; and therefore we don't need to
/// specify the generics whenever calling those spec or proof functions.
pub struct Cluster<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> {
    pub kubernetes_api_state: KubernetesAPIState,
    pub builtin_controllers_state: BuiltinControllersState,
    pub controller_state: ControllerState<K, E, R>,
    pub client_state: ClientState,
    pub network_state: NetworkState<E::Input, E::Output>,
    pub external_api_state: ExternalAPIState<E>,
    pub rest_id_allocator: RestIdAllocator,
    pub crash_enabled: bool,
    pub transient_failure_enabled: bool,
}

impl<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {
    #[verifier(inline)]
    pub open spec fn in_flight(self) -> Multiset<MsgType<E>> {
        self.network_state.in_flight
    }

    #[verifier(inline)]
    pub open spec fn resources(self) -> StoredState {
        self.kubernetes_api_state.resources
    }

    #[verifier(inline)]
    pub open spec fn ongoing_reconciles(self) -> Map<ObjectRef, OngoingReconcile<K, E, R>> {
        self.controller_state.ongoing_reconciles
    }

    #[verifier(inline)]
    pub open spec fn scheduled_reconciles(self) -> Map<ObjectRef, K> {
        self.controller_state.scheduled_reconciles
    }

    pub open spec fn has_rest_id_counter_no_smaller_than(self, rest_id: nat) -> bool {
        self.rest_id_allocator.rest_id_counter >= rest_id
    }
}

}
