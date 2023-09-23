// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::exec::types::*;
use crate::fluent_controller::fluentbit::spec::reconciler as fb_spec;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, container::*, daemon_set::*, label_selector::*,
    object_meta::*, owner_reference::*, persistent_volume_claim::*, pod::*, pod_template_spec::*,
    resource::*, resource_requirements::*, role::*, role_binding::*, secret::*, service::*,
    service_account::*, toleration::*, volume::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

// TODO:
// + Use Role after Anvil supports cluster-scoped resources
//
// + Add more features
//
// + Split the management logic into two reconciliation loops

pub struct FluentBitReconcileState {
    pub reconcile_step: FluentBitReconcileStep,
}

impl FluentBitReconcileState {
    pub open spec fn to_view(&self) -> fb_spec::FluentBitReconcileState {
        fb_spec::FluentBitReconcileState {
            reconcile_step: self.reconcile_step,
        }
    }
}

pub struct FluentBitReconciler {}

#[verifier(external)]
impl Reconciler<FluentBit, FluentBitReconcileState, EmptyType, EmptyType, EmptyAPIShimLayer> for FluentBitReconciler {
    fn reconcile_init_state(&self) -> FluentBitReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, fb: &FluentBit, resp_o: Option<Response<EmptyType>>, state: FluentBitReconcileState) -> (FluentBitReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(fb, resp_o, state)
    }

    fn reconcile_done(&self, state: &FluentBitReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &FluentBitReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for FluentBitReconciler {
    fn default() -> FluentBitReconciler { FluentBitReconciler{} }
}

pub fn reconcile_init_state() -> (state: FluentBitReconcileState)
    ensures
        state.to_view() == fb_spec::reconcile_init_state(),
{
    FluentBitReconcileState {
        reconcile_step: FluentBitReconcileStep::Init,
    }
}

pub fn reconcile_done(state: &FluentBitReconcileState) -> (res: bool)
    ensures
        res == fb_spec::reconcile_done(state.to_view()),
{
    match state.reconcile_step {
        FluentBitReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &FluentBitReconcileState) -> (res: bool)
    ensures
        res == fb_spec::reconcile_error(state.to_view()),
{
    match state.reconcile_step {
        FluentBitReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(fb: &FluentBit, resp_o: Option<Response<EmptyType>>, state: FluentBitReconcileState) -> (res: (FluentBitReconcileState, Option<Request<EmptyType>>))
    requires
        fb@.well_formed(),
    ensures
        (res.0.to_view(), opt_request_to_view(&res.1)) == fb_spec::reconcile_core(fb@, opt_response_to_view(&resp_o), state.to_view()),
{
    let step = state.reconcile_step;
    match step{
        FluentBitReconcileStep::Init => {
            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: Secret::api_resource(),
                name: fb.spec().fluentbit_config_name(),
                namespace: fb.metadata().namespace().unwrap(),
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterGetSecret,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        FluentBitReconcileStep::AfterGetSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_sts_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_sts_resp.is_ok() {
                    let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                        api_resource: Role::api_resource(),
                        name: make_role_name(fb),
                        namespace: fb.metadata().namespace().unwrap(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterGetRole,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterGetRole => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_role_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_role_resp.is_ok() {
                    let unmarshal_role_result = Role::unmarshal(get_role_resp.unwrap());
                    if unmarshal_role_result.is_ok() {
                        let found_role = unmarshal_role_result.unwrap();
                        let new_role = update_role(fb, &found_role);
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: Role::api_resource(),
                            name: make_role_name(fb),
                            namespace: fb.metadata().namespace().unwrap(),
                            obj: new_role.marshal(),
                        });
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::AfterUpdateRole,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_role_resp.unwrap_err().is_object_not_found() {
                    let role = make_role(fb);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Role::api_resource(),
                        namespace: fb.metadata().namespace().unwrap(),
                        obj: role.marshal(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterCreateRole,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterCreateRole => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.unwrap().into_k_response().into_create_response().res.is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: ServiceAccount::api_resource(),
                    name: make_service_account_name(fb),
                    namespace: fb.metadata().namespace().unwrap(),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetServiceAccount,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterUpdateRole => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.unwrap().into_k_response().into_update_response().res.is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: ServiceAccount::api_resource(),
                    name: make_service_account_name(fb),
                    namespace: fb.metadata().namespace().unwrap(),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetServiceAccount,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterGetServiceAccount => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_service_account_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_service_account_resp.is_ok() {
                    let unmarshal_service_account_result = ServiceAccount::unmarshal(get_service_account_resp.unwrap());
                    if unmarshal_service_account_result.is_ok() {
                        let found_service_account = unmarshal_service_account_result.unwrap();
                        let new_service_account = update_service_account(fb, &found_service_account);
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: ServiceAccount::api_resource(),
                            name: make_service_account_name(fb),
                            namespace: fb.metadata().namespace().unwrap(),
                            obj: new_service_account.marshal(),
                        });
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::AfterUpdateServiceAccount,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_service_account_resp.unwrap_err().is_object_not_found() {
                    let service_account = make_service_account(fb);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: ServiceAccount::api_resource(),
                        namespace: fb.metadata().namespace().unwrap(),
                        obj: service_account.marshal(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterCreateServiceAccount,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterCreateServiceAccount => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.unwrap().into_k_response().into_create_response().res.is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: RoleBinding::api_resource(),
                    name: make_role_binding_name(fb),
                    namespace: fb.metadata().namespace().unwrap(),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetRoleBinding,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterUpdateServiceAccount => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.unwrap().into_k_response().into_update_response().res.is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: RoleBinding::api_resource(),
                    name: make_role_binding_name(fb),
                    namespace: fb.metadata().namespace().unwrap(),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetRoleBinding,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterGetRoleBinding => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_role_binding_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_role_binding_resp.is_ok() {
                    let unmarshal_role_binding_result = RoleBinding::unmarshal(get_role_binding_resp.unwrap());
                    if unmarshal_role_binding_result.is_ok() {
                        let found_role_binding = unmarshal_role_binding_result.unwrap();
                        let new_role_binding = update_role_binding(fb, &found_role_binding);
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: RoleBinding::api_resource(),
                            name: make_role_binding_name(fb),
                            namespace: fb.metadata().namespace().unwrap(),
                            obj: new_role_binding.marshal(),
                        });
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::AfterUpdateRoleBinding,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_role_binding_resp.unwrap_err().is_object_not_found() {
                    let role_binding = make_role_binding(fb);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: RoleBinding::api_resource(),
                        namespace: fb.metadata().namespace().unwrap(),
                        obj: role_binding.marshal(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterCreateRoleBinding,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterCreateRoleBinding => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.unwrap().into_k_response().into_create_response().res.is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: DaemonSet::api_resource(),
                    name: make_daemon_set_name(fb),
                    namespace: fb.metadata().namespace().unwrap(),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetDaemonSet,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterUpdateRoleBinding => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.unwrap().into_k_response().into_update_response().res.is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: DaemonSet::api_resource(),
                    name: make_daemon_set_name(fb),
                    namespace: fb.metadata().namespace().unwrap(),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetDaemonSet,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterGetDaemonSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_daemon_set_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_daemon_set_resp.is_ok() {
                    let unmarshal_daemon_set_result = DaemonSet::unmarshal(get_daemon_set_resp.unwrap());
                    if unmarshal_daemon_set_result.is_ok() {
                        let found_daemon_set = unmarshal_daemon_set_result.unwrap();
                        if found_daemon_set.spec().is_some() {
                            let new_daemon_set = update_daemon_set(fb, &found_daemon_set);
                            let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                api_resource: DaemonSet::api_resource(),
                                name: make_daemon_set_name(fb),
                                namespace: fb.metadata().namespace().unwrap(),
                                obj: new_daemon_set.marshal(),
                            });
                            let state_prime = FluentBitReconcileState {
                                reconcile_step: FluentBitReconcileStep::AfterUpdateDaemonSet,
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                } else if get_daemon_set_resp.unwrap_err().is_object_not_found() {
                    let daemon_set = make_daemon_set(fb);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: DaemonSet::api_resource(),
                        namespace: fb.metadata().namespace().unwrap(),
                        obj: daemon_set.marshal(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterCreateDaemonSet,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterCreateDaemonSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.unwrap().into_k_response().into_create_response().res.is_ok() {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterUpdateDaemonSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.unwrap().into_k_response().into_update_response().res.is_ok() {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            }
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        _ => {
            let state_prime = FluentBitReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = None;
            (state_prime, req_o)
        }
    }
}

fn make_base_labels(fb: &FluentBit) -> (labels: StringMap)
    requires
        fb@.well_formed(),
    ensures
        labels@ == fb_spec::make_base_labels(fb@),
{
    let mut labels = StringMap::empty();
    labels.insert(new_strlit("app").to_string(), fb.metadata().name().unwrap());
    labels
}

fn make_labels(fb: &FluentBit) -> (labels: StringMap)
    requires
        fb@.well_formed(),
    ensures
        labels@ == fb_spec::make_labels(fb@),
{
    let mut labels = fb.spec().labels();
    labels.extend(make_base_labels(fb));
    labels
}

fn make_role_name(fb: &FluentBit) -> (name: String)
    requires
        fb@.well_formed(),
    ensures
        name@ == fb_spec::make_role_name(fb@.metadata.name.get_Some_0()),
{
    fb.metadata().name().unwrap().concat(new_strlit("-role"))
}

fn update_role(fb: &FluentBit, found_role: &Role) -> (role: Role)
    requires
        fb@.well_formed(),
    ensures
        role@ == fb_spec::update_role(fb@, found_role@),
{
    let mut role = found_role.clone();
    let made_role = make_role(fb);
    role.set_metadata({
        let mut metadata = found_role.metadata();
        metadata.set_labels(made_role.metadata().labels().unwrap());
        metadata.set_annotations(made_role.metadata().annotations().unwrap());
        metadata
    });
    role
}

fn make_role(fb: &FluentBit) -> (role: Role)
    requires
        fb@.well_formed(),
    ensures
        role@ == fb_spec::make_role(fb@),
{
    let mut role = Role::default();
    role.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_role_name(fb));
        metadata.set_labels(make_labels(fb));
        metadata.set_annotations(fb.spec().annotations());
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(fb.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    fb_spec::make_role(fb@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    role.set_policy_rules({
        let mut rules = Vec::new();
        rules.push({
            let mut rule = PolicyRule::default();
            rule.set_api_groups({
                let mut api_groups = Vec::new();
                api_groups.push(new_strlit("").to_string());
                proof{
                    assert_seqs_equal!(
                        api_groups@.map_values(|p: String| p@),
                        fb_spec::make_role(fb@).policy_rules.get_Some_0()[0].api_groups.get_Some_0()
                    );
                }
                api_groups
            });
            rule.set_resources({
                let mut resources = Vec::new();
                resources.push(new_strlit("pods").to_string());
                proof{
                    assert_seqs_equal!(
                        resources@.map_values(|p: String| p@),
                        fb_spec::make_role(fb@).policy_rules.get_Some_0()[0].resources.get_Some_0()
                    );
                }
                resources
            });
            rule.set_verbs({
                let mut verbs = Vec::new();
                verbs.push(new_strlit("get").to_string());
                proof{
                    assert_seqs_equal!(
                        verbs@.map_values(|p: String| p@),
                        fb_spec::make_role(fb@).policy_rules.get_Some_0()[0].verbs
                    );
                }
                verbs
            });
            rule
        });
        proof{
            assert_seqs_equal!(
                rules@.map_values(|p: PolicyRule| p@),
                fb_spec::make_role(fb@).policy_rules.get_Some_0()
            );
        }
        rules
    });
    role
}

fn make_service_account_name(fb: &FluentBit) -> (name: String)
    requires
        fb@.well_formed(),
    ensures
        name@ == fb_spec::make_service_account_name(fb@.metadata.name.get_Some_0()),
{
    fb.metadata().name().unwrap()
}

fn update_service_account(fb: &FluentBit, found_service_account: &ServiceAccount) -> (service_account: ServiceAccount)
    requires
        fb@.well_formed(),
    ensures
        service_account@ == fb_spec::update_service_account(fb@, found_service_account@),
{
    let mut service_account = found_service_account.clone();
    let made_service_account = make_service_account(fb);
    service_account.set_metadata({
        let mut metadata = found_service_account.metadata();
        metadata.set_labels(made_service_account.metadata().labels().unwrap());
        metadata.set_annotations(made_service_account.metadata().annotations().unwrap());
        metadata
    });
    service_account
}

fn make_service_account(fb: &FluentBit) -> (service_account: ServiceAccount)
    requires
        fb@.well_formed(),
    ensures
        service_account@ == fb_spec::make_service_account(fb@),
{
    let mut service_account = ServiceAccount::default();
    service_account.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_service_account_name(fb));
        metadata.set_labels(make_labels(fb));
        metadata.set_annotations(fb.spec().annotations());
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(fb.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    fb_spec::make_service_account(fb@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    service_account
}

fn make_role_binding_name(fb: &FluentBit) -> (name: String)
    requires
        fb@.well_formed(),
    ensures
        name@ == fb_spec::make_role_binding_name(fb@.metadata.name.get_Some_0()),
{
    fb.metadata().name().unwrap().concat(new_strlit("-role-binding"))
}

fn update_role_binding(fb: &FluentBit, found_role_binding: &RoleBinding) -> (role_binding: RoleBinding)
    requires
        fb@.well_formed(),
    ensures
        role_binding@ == fb_spec::update_role_binding(fb@, found_role_binding@),
{
    let mut role_binding = found_role_binding.clone();
    let made_role_binding = make_role_binding(fb);
    role_binding.set_metadata({
        let mut metadata = found_role_binding.metadata();
        metadata.set_labels(made_role_binding.metadata().labels().unwrap());
        metadata.set_annotations(made_role_binding.metadata().annotations().unwrap());
        metadata
    });
    role_binding
}

fn make_role_binding(fb: &FluentBit) -> (role_binding: RoleBinding)
    requires
        fb@.well_formed(),
    ensures
        role_binding@ == fb_spec::make_role_binding(fb@),
{
    let mut role_binding = RoleBinding::default();
    role_binding.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_role_binding_name(fb));
        metadata.set_labels(make_labels(fb));
        metadata.set_annotations(fb.spec().annotations());
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(fb.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    fb_spec::make_role_binding(fb@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    role_binding.set_role_ref({
        let mut role_ref = RoleRef::default();
        role_ref.set_api_group(new_strlit("rbac.authorization.k8s.io").to_string());
        role_ref.set_kind(new_strlit("Role").to_string());
        role_ref.set_name(fb.metadata().name().unwrap().concat(new_strlit("-role")));
        role_ref
    });
    role_binding.set_subjects({
        let mut subjects = Vec::new();
        subjects.push({
            let mut subject = Subject::default();
            subject.set_kind(new_strlit("ServiceAccount").to_string());
            subject.set_name(fb.metadata().name().unwrap());
            subject.set_namespace(fb.metadata().namespace().unwrap());
            subject
        });
        proof{
            assert_seqs_equal!(
                subjects@.map_values(|p: Subject| p@),
                fb_spec::make_role_binding(fb@).subjects.get_Some_0()
            );
        }
        subjects
    });

    role_binding
}

fn make_daemon_set_name(fb: &FluentBit) -> (name: String)
    requires
        fb@.well_formed(),
    ensures
        name@ == fb_spec::make_daemon_set_name(fb@.metadata.name.get_Some_0()),
{
    fb.metadata().name().unwrap()
}

fn update_daemon_set(fb: &FluentBit, found_daemon_set: &DaemonSet) -> (daemon_set: DaemonSet)
    requires
        fb@.well_formed(),
        found_daemon_set@.spec.is_Some(),
    ensures
        daemon_set@ == fb_spec::update_daemon_set(fb@, found_daemon_set@),
{
    let mut daemon_set = found_daemon_set.clone();
    let made_daemon_set = make_daemon_set(fb);
    daemon_set.set_metadata({
        let mut metadata = found_daemon_set.metadata();
        metadata.set_labels(made_daemon_set.metadata().labels().unwrap());
        metadata.set_annotations(made_daemon_set.metadata().annotations().unwrap());
        metadata
    });
    daemon_set.set_spec({
        let mut spec = found_daemon_set.spec().unwrap();
        spec.set_template(made_daemon_set.spec().unwrap().template());
        spec
    });
    daemon_set
}

fn make_daemon_set(fb: &FluentBit) -> (daemon_set: DaemonSet)
    requires
        fb@.well_formed(),
    ensures
        daemon_set@ == fb_spec::make_daemon_set(fb@),
{
    let mut daemon_set = DaemonSet::default();
    daemon_set.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_daemon_set_name(fb));
        metadata.set_labels(make_labels(fb));
        metadata.set_annotations(fb.spec().annotations());
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(fb.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    fb_spec::make_daemon_set(fb@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    daemon_set.set_spec({
        let mut daemon_set_spec = DaemonSetSpec::default();
        // Set the selector used for querying pods of this daemon set
        daemon_set_spec.set_selector({
            let mut selector = LabelSelector::default();
            selector.set_match_labels(make_base_labels(fb));
            selector
        });
        // Set the template used for creating pods
        daemon_set_spec.set_template({
            let mut pod_template_spec = PodTemplateSpec::default();
            pod_template_spec.set_metadata({
                let mut metadata = ObjectMeta::default();
                metadata.set_labels(make_labels(fb));
                metadata.set_annotations(fb.spec().annotations());
                metadata
            });
            pod_template_spec.set_spec(make_fluentbit_pod_spec(fb));
            pod_template_spec
        });
        daemon_set_spec
    });
    daemon_set
}

fn make_fluentbit_pod_spec(fb: &FluentBit) -> (pod_spec: PodSpec)
    requires
        fb@.well_formed(),
    ensures
        pod_spec@ == fb_spec::make_fluentbit_pod_spec(fb@),
{
    let mut pod_spec = PodSpec::default();
    pod_spec.set_service_account_name(fb.metadata().name().unwrap());
    pod_spec.set_containers({
        let mut containers = Vec::new();
        containers.push({
            let mut fb_container = Container::default();
            fb_container.set_name(new_strlit("fluent-bit").to_string());
            fb_container.set_image(new_strlit("kubesphere/fluent-bit:v2.1.7").to_string());
            fb_container.set_env(make_env(&fb));
            fb_container.set_volume_mounts({
                let mut volume_mounts = Vec::new();
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("varlibcontainers").to_string());
                    volume_mount.set_read_only(true);
                    volume_mount.set_mount_path(new_strlit("/containers").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("config").to_string());
                    volume_mount.set_read_only(true);
                    volume_mount.set_mount_path(new_strlit("/fluent-bit/config").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("varlogs").to_string());
                    volume_mount.set_read_only(true);
                    volume_mount.set_mount_path(new_strlit("/var/log/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("systemd").to_string());
                    volume_mount.set_read_only(true);
                    volume_mount.set_mount_path(new_strlit("/var/log/journal").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("positions").to_string());
                    volume_mount.set_mount_path(new_strlit("/fluent-bit/tail").to_string());
                    volume_mount
                });
                proof {
                    assert_seqs_equal!(
                        volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
                        fb_spec::make_fluentbit_pod_spec(fb@).containers[0].volume_mounts.get_Some_0()
                    );
                }
                volume_mounts
            });
            fb_container.set_ports({
                let mut ports = Vec::new();
                ports.push(ContainerPort::new_with(new_strlit("metrics").to_string(), 2020));
                proof {
                    assert_seqs_equal!(
                        ports@.map_values(|port: ContainerPort| port@),
                        fb_spec::make_fluentbit_pod_spec(fb@).containers[0].ports.get_Some_0()
                    );
                }
                ports
            });
            fb_container.overwrite_resources(fb.spec().resources());
            fb_container
        });
        proof {
            assert_seqs_equal!(
                containers@.map_values(|container: Container| container@),
                fb_spec::make_fluentbit_pod_spec(fb@).containers
            );
        }
        containers
    });
    pod_spec.set_volumes({
        let mut volumes = Vec::new();
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("varlibcontainers").to_string());
            volume.set_host_path({
                let mut host_path = HostPathVolumeSource::default();
                host_path.set_path(new_strlit("/containers").to_string());
                host_path
            });
            volume
        });
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("config").to_string());
            volume.set_secret({
                let mut secret = SecretVolumeSource::default();
                secret.set_secret_name(fb.spec().fluentbit_config_name());
                secret
            });
            volume
        });
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("varlogs").to_string());
            volume.set_host_path({
                let mut host_path = HostPathVolumeSource::default();
                host_path.set_path(new_strlit("/var/log").to_string());
                host_path
            });
            volume
        });
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("systemd").to_string());
            volume.set_host_path({
                let mut host_path = HostPathVolumeSource::default();
                host_path.set_path(new_strlit("/var/log/journal").to_string());
                host_path
            });
            volume
        });
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("positions").to_string());
            volume.set_host_path({
                let mut host_path = HostPathVolumeSource::default();
                host_path.set_path(new_strlit("/var/lib/fluent-bit/").to_string());
                host_path
            });
            volume
        });
        proof {
            assert_seqs_equal!(
                volumes@.map_values(|vol: Volume| vol@),
                fb_spec::make_fluentbit_pod_spec(fb@).volumes.get_Some_0()
            );
        }
        volumes
    });
    pod_spec.overwrite_tolerations(fb.spec().tolerations());
    pod_spec
}

fn make_env(fb: &FluentBit) -> (env_vars: Vec<EnvVar>)
    ensures
        env_vars@.map_values(|v: EnvVar| v@) == fb_spec::make_env(fb@),
{
    let mut env_vars = Vec::new();
    env_vars.push(EnvVar::new_with(
        new_strlit("NODE_NAME").to_string(), None, Some(EnvVarSource::new_with_field_ref({
            let mut selector = ObjectFieldSelector::default();
            selector.set_field_path(new_strlit("spec.nodeName").to_string());
            selector
        }))
    ));
    env_vars.push(EnvVar::new_with(
        new_strlit("HOST_IP").to_string(), None, Some(EnvVarSource::new_with_field_ref({
            let mut selector = ObjectFieldSelector::default();
            selector.set_field_path(new_strlit("status.hostIP").to_string());
            selector
        }))
    ));
    proof {
        assert_seqs_equal!(
            env_vars@.map_values(|v: EnvVar| v@),
            fb_spec::make_env(fb@),
        );
    }
    env_vars
}

}
