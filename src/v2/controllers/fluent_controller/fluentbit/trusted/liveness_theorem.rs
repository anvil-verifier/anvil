// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::fluent_controller::fluentbit::trusted::{maker::*, spec_types::*, step::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::Step, message::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::int_to_string_view;
use vstd::prelude::*;

verus! {

pub open spec fn liveness_theorem<M: Maker>() -> bool { cluster_spec().entails(tla_forall(|fb: FluentBitView| liveness::<M>(fb))) }

pub open spec fn cluster_spec() -> TempPred<FBCluster> { FBCluster::sm_spec() }

pub open spec fn liveness<M: Maker>(fb:FluentBitView) -> TempPred<FBCluster> {
    always(lift_state(desired_state_is(fb))).leads_to(always(lift_state(current_state_matches::<M>(fb))))
}

pub open spec fn desired_secret_key(fb: FluentBitView) -> ObjectRef {
    ObjectRef {
        kind: SecretView::kind(),
        namespace: fb.metadata.namespace.get_Some_0(),
        name: fb.spec.fluentbit_config_name,
    }
}

pub open spec fn desired_state_is(fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        &&& FBCluster::desired_state_is(fb)(s)
        &&& s.resources().contains_key(desired_secret_key(fb))
    }
}

pub open spec fn current_state_matches<M: Maker>(fb:FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        forall |sub_resource: SubResource| #[trigger] resource_state_matches::<M>(sub_resource, fb, s.resources())
    }
}

pub open spec fn resource_state_matches<M: Maker>(sub_resource: SubResource, fb:FluentBitView, resources: StoredState) -> bool {
    match sub_resource {
        SubResource::ServiceAccount => {
            let key = M::make_service_account_key(fb);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& ServiceAccountView::unmarshal(obj).is_Ok()
            &&& ServiceAccountView::unmarshal(obj).get_Ok_0().automount_service_account_token == M::make_service_account(fb).automount_service_account_token
            &&& obj.metadata.labels == M::make_service_account(fb).metadata.labels
            &&& obj.metadata.annotations == M::make_service_account(fb).metadata.annotations
        },
        SubResource::Role => {
            let key = M::make_role_key(fb);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& RoleView::unmarshal(obj).is_Ok()
            &&& RoleView::unmarshal(obj).get_Ok_0().policy_rules == M::make_role(fb).policy_rules
            &&& obj.metadata.labels == M::make_role(fb).metadata.labels
            &&& obj.metadata.annotations == M::make_role(fb).metadata.annotations
        },
        SubResource::RoleBinding => {
            let key = M::make_role_binding_key(fb);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& RoleBindingView::unmarshal(obj).is_Ok()
            &&& RoleBindingView::unmarshal(obj).get_Ok_0().role_ref == M::make_role_binding(fb).role_ref
            &&& RoleBindingView::unmarshal(obj).get_Ok_0().subjects == M::make_role_binding(fb).subjects
            &&& obj.metadata.labels == M::make_role_binding(fb).metadata.labels
            &&& obj.metadata.annotations == M::make_role_binding(fb).metadata.annotations
        },
        SubResource::Service => {
            let key = M::make_service_key(fb);
            let obj = resources[key];
            let made_spec = M::make_service(fb).spec.get_Some_0();
            let spec = ServiceView::unmarshal(obj).get_Ok_0().spec.get_Some_0();
            &&& resources.contains_key(key)
            &&& ServiceView::unmarshal(obj).is_Ok()
            &&& ServiceView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& made_spec == ServiceSpecView {
                cluster_ip: made_spec.cluster_ip,
                ..spec
            }
            &&& obj.metadata.labels == M::make_service(fb).metadata.labels
            &&& obj.metadata.annotations == M::make_service(fb).metadata.annotations
        },
        SubResource::DaemonSet => {
            let key = M::make_daemon_set_key(fb);
            let obj = resources[key];
            let made_ds = M::make_daemon_set(fb);
            &&& resources.contains_key(key)
            &&& DaemonSetView::unmarshal(obj).is_Ok()
            &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec == made_ds.spec
            &&& obj.metadata.labels == made_ds.metadata.labels
            &&& obj.metadata.annotations == made_ds.metadata.annotations
        },
    }
}

}
