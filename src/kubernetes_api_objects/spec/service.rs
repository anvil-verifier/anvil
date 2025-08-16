// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*, object_meta::*, resource::*};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;

verus! {

// ServiceView is the ghost type of Service.


pub struct ServiceView {
    pub metadata: ObjectMetaView,
    pub spec: Option<ServiceSpecView>,
    pub status: Option<ServiceStatusView>,
}

pub type ServiceStatusView = EmptyStatusView;

impl ServiceView {
    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> ServiceView {
        ServiceView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_spec(self, spec: ServiceSpecView) -> ServiceView {
        ServiceView {
            spec: Some(spec),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: ServiceView) -> bool { true }
}

implement_resource_view_trait!(ServiceView, Option<ServiceSpecView>, None, Option<ServiceStatusView>, None,
    Kind::ServiceKind, _state_validation, _transition_validation);

pub struct ServiceSpecView {
    pub cluster_ip: Option<StringView>,
    pub ports: Option<Seq<ServicePortView>>,
    pub selector: Option<Map<StringView, StringView>>,
    pub publish_not_ready_addresses: Option<bool>,
}

impl ServiceSpecView {
    pub open spec fn default() -> ServiceSpecView {
        ServiceSpecView {
            cluster_ip: None,
            ports: None,
            selector: None,
            publish_not_ready_addresses: None,
        }
    }

    pub open spec fn with_cluster_ip(self, cluster_ip: StringView) -> ServiceSpecView {
        ServiceSpecView {
            cluster_ip: Some(cluster_ip),
            ..self
        }
    }

    pub open spec fn with_ports(self, ports: Seq<ServicePortView>) -> ServiceSpecView {
        ServiceSpecView {
            ports: Some(ports),
            ..self
        }
    }

    pub open spec fn with_selector(self, selector: Map<StringView, StringView>) -> ServiceSpecView {
        ServiceSpecView {
            selector: Some(selector),
            ..self
        }
    }

    pub open spec fn with_publish_not_ready_addresses(self, publish_not_ready_addresses: bool) -> ServiceSpecView {
        ServiceSpecView {
            publish_not_ready_addresses: Some(publish_not_ready_addresses),
            ..self
        }
    }

    pub open spec fn without_publish_not_ready_addresses(self) -> ServiceSpecView {
        ServiceSpecView {
            publish_not_ready_addresses: None,
            ..self
        }
    }
}

pub struct ServicePortView {
    pub name: Option<StringView>,
    pub port: int,
    pub app_protocol: Option<StringView>,
    pub protocol: Option<StringView>,
}

impl ServicePortView {
    pub open spec fn default() -> ServicePortView {
        ServicePortView {
            name: None,
            port: 0, // TODO: is this the correct default value?
            app_protocol: None,
            protocol: None,
        }
    }

    pub open spec fn with_name(self, name: StringView) -> ServicePortView {
        ServicePortView {
            name: Some(name),
            ..self
        }
    }

    pub open spec fn with_port(self, port: int) -> ServicePortView {
        ServicePortView {
            port: port,
            ..self
        }
    }

    pub open spec fn with_app_protocol(self, app_protocol: StringView) -> ServicePortView {
        ServicePortView {
            app_protocol: Some(app_protocol),
            ..self
        }
    }

    pub open spec fn with_protocol(self, protocol: StringView) -> ServicePortView {
        ServicePortView {
            protocol: Some(protocol),
            ..self
        }
    }
}

}
