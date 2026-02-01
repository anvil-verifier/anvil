// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    affinity::*, common::*, container::*, dynamic::*, object_meta::*, resource::*, toleration::*,
    volume::*,
};
use crate::vstd_ext::string_view::*;
use deps_hack::k8s_openapi::api::core::v1::PodSpec;
use vstd::prelude::*;

verus! {

// PodView is the ghost type of Pod.

pub struct PodView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PodSpecView>,
    pub status: Option<PodStatusView>,
}

pub type PodStatusView = EmptyStatusView;

impl PodView {
    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> PodView {
        PodView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_spec(self, spec: PodSpecView) -> PodView {
        PodView {
            spec: Some(spec),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: PodView) -> bool { true }
}

implement_resource_view_trait!(PodView, Option<PodSpecView>, None, Option<PodStatusView>, None,
    Kind::PodKind, _state_validation, _transition_validation);

pub struct PodSpecView {
    pub affinity: Option<AffinityView>,
    pub containers: Seq<ContainerView>,
    pub volumes: Option<Seq<VolumeView>>,
    pub init_containers: Option<Seq<ContainerView>>,
    pub service_account_name: Option<StringView>,
    pub tolerations: Option<Seq<TolerationView>>,
    pub node_selector: Option<Map<StringView, StringView>>,
    pub runtime_class_name: Option<StringView>,
    pub dns_policy: Option<StringView>,
    pub priority_class_name: Option<StringView>,
    pub scheduler_name: Option<StringView>,
    pub security_context: Option<PodSecurityContextView>,
    pub host_network: Option<bool>,
    pub termination_grace_period_seconds: Option<int>,
    pub image_pull_secrets: Option<Seq<LocalObjectReferenceView>>,
    pub hostname: Option<StringView>,
    pub subdomain: Option<StringView>,
}

impl PodSpecView {
    pub open spec fn default() -> PodSpecView {
        PodSpecView {
            affinity: None,
            containers: Seq::empty(),
            volumes: None,
            init_containers: None,
            service_account_name: None,
            tolerations: None,
            node_selector: None,
            runtime_class_name: None,
            dns_policy: None,
            priority_class_name: None,
            scheduler_name: None,
            security_context: None,
            host_network: None,
            termination_grace_period_seconds: None,
            image_pull_secrets: None,
            hostname: None,
            subdomain: None,
        }
    }

    pub open spec fn with_affinity(self, affinity: AffinityView) -> PodSpecView {
        PodSpecView {
            affinity: Some(affinity),
            ..self
        }
    }

    pub open spec fn without_affinity(self) -> PodSpecView {
        PodSpecView {
            affinity: None,
            ..self
        }
    }

    pub open spec fn with_containers(self, containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            containers: containers,
            ..self
        }
    }

    pub open spec fn with_volumes(self, volumes: Seq<VolumeView>) -> PodSpecView {
        PodSpecView {
            volumes: Some(volumes),
            ..self
        }
    }

    pub open spec fn without_volumes(self) -> PodSpecView {
        PodSpecView {
            volumes: None,
            ..self
        }
    }

    pub open spec fn with_init_containers(self, init_containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            init_containers: Some(init_containers),
            ..self
        }
    }

    pub open spec fn with_service_account_name(self, service_account_name: StringView) -> PodSpecView {
        PodSpecView {
            service_account_name: Some(service_account_name),
            ..self
        }
    }

    pub open spec fn with_tolerations(self, tolerations: Seq<TolerationView>) -> PodSpecView {
        PodSpecView {
            tolerations: Some(tolerations),
            ..self
        }
    }

    pub open spec fn without_tolerations(self) -> PodSpecView {
        PodSpecView {
            tolerations: None,
            ..self
        }
    }

    pub open spec fn with_node_selector(self, node_selector: Map<StringView, StringView>) -> PodSpecView {
        PodSpecView {
            node_selector: Some(node_selector),
            ..self
        }
    }

    pub open spec fn with_runtime_class_name(self, runtime_class_name: StringView) -> PodSpecView {
        PodSpecView {
            runtime_class_name: Some(runtime_class_name),
            ..self
        }
    }

    pub open spec fn with_dns_policy(self, dns_policy: StringView) -> PodSpecView {
        PodSpecView {
            dns_policy: Some(dns_policy),
            ..self
        }
    }

    pub open spec fn with_scheduler_name(self, scheduler_name: StringView) -> PodSpecView {
        PodSpecView {
            scheduler_name: Some(scheduler_name),
            ..self
        }
    }

    pub open spec fn with_priority_class_name(self, priority_class_name: StringView) -> PodSpecView {
        PodSpecView {
            priority_class_name: Some(priority_class_name),
            ..self
        }
    }

    pub open spec fn with_security_context(self, security_context: PodSecurityContextView) -> PodSpecView {
        PodSpecView {
            security_context: Some(security_context),
            ..self
        }
    }

    pub open spec fn with_host_network(self, host_network: bool) -> PodSpecView {
        PodSpecView {
            host_network: Some(host_network),
            ..self
        }
    }

    pub open spec fn with_termination_grace_period_seconds(self, termination_grace_period_seconds: int) -> PodSpecView {
        PodSpecView {
            termination_grace_period_seconds: Some(termination_grace_period_seconds),
            ..self
        }
    }

    pub open spec fn with_image_pull_secrets(self, image_pull_secrets: Seq<LocalObjectReferenceView>) -> PodSpecView {
        PodSpecView {
            image_pull_secrets: Some(image_pull_secrets),
            ..self
        }
    }

    pub open spec fn with_hostname(self, hostname: StringView) -> PodSpecView {
        PodSpecView {
            hostname: Some(hostname),
            ..self
        }
    }

    pub open spec fn without_hostname(self) -> PodSpecView {
        PodSpecView {
            hostname: None,
            ..self
        }
    }

    pub open spec fn with_subdomain(self, subdomain: StringView) -> PodSpecView {
        PodSpecView {
            subdomain: Some(subdomain),
            ..self
        }
    }

    pub open spec fn without_subdomain(self) -> PodSpecView {
        PodSpecView {
            subdomain: None,
            ..self
        }
    }
}

pub struct PodSecurityContextView {}

impl PodSecurityContextView {
    pub open spec fn default() -> PodSecurityContextView {
        PodSecurityContextView {}
    }
}

pub struct LocalObjectReferenceView {}

impl LocalObjectReferenceView {
    pub open spec fn default() -> LocalObjectReferenceView {
        LocalObjectReferenceView {}
    }
}

}
