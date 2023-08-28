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
    pub busy_enabled: bool,
}

impl<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {
    #[verifier(inline)]
    pub open spec fn message_in_flight(self, msg: MsgType<E>) -> bool {
        self.network_state.in_flight.contains(msg)
    }

    pub open spec fn resource_key_exists(self, key: ObjectRef) -> bool {
        self.kubernetes_api_state.resources.dom().contains(key)
    }

    pub open spec fn resource_obj_exists(self, obj: DynamicObjectView) -> bool {
        &&& self.kubernetes_api_state.resources.dom().contains(obj.object_ref())
        &&& self.kubernetes_api_state.resources[obj.object_ref()] == obj
    }

    pub open spec fn resource_obj_of(self, key: ObjectRef) -> DynamicObjectView
        recommends self.resource_key_exists(key)
    {
        self.kubernetes_api_state.resources[key]
    }

    #[verifier(inline)]
    pub open spec fn reconcile_state_contains(self, key: ObjectRef) -> bool {
        self.controller_state.ongoing_reconciles.dom().contains(key)
    }

    pub open spec fn reconcile_state_of(self, key: ObjectRef) -> OngoingReconcile<K, E, R>
        recommends
            self.reconcile_state_contains(key),
    {
        self.controller_state.ongoing_reconciles[key]
    }

    pub open spec fn triggering_cr_of(self, key: ObjectRef) -> K
        recommends
            self.reconcile_state_contains(key),
    {
        self.controller_state.ongoing_reconciles[key].triggering_cr
    }

    #[verifier(inline)]
    pub open spec fn pending_req_of(self, key: ObjectRef) -> MsgType<E>
        recommends
            self.reconcile_state_contains(key),
            self.reconcile_state_of(key).pending_req_msg.is_Some(),
    {
        self.controller_state.ongoing_reconciles[key].pending_req_msg.get_Some_0()
    }

    pub open spec fn reconcile_scheduled_for(self, key: ObjectRef) -> bool {
        self.controller_state.scheduled_reconciles.contains_key(key)
    }

    pub open spec fn reconcile_scheduled_obj_of(self, key: ObjectRef) -> K
        recommends
            self.reconcile_scheduled_for(key),
    {
        self.controller_state.scheduled_reconciles[key]
    }

    pub open spec fn has_rest_id_counter_no_smaller_than(self, rest_id: nat) -> bool {
        self.rest_id_allocator.rest_id_counter >= rest_id
    }
}

}
