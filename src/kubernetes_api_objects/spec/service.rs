// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, marshal::*, object_meta::*, resource::*,
};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

/// ServiceView is the ghost type of Service.
/// It is supposed to be used in spec and proof code.

pub struct ServiceView {
    pub metadata: ObjectMetaView,
    pub spec: Option<ServiceSpecView>,
    pub status: Option<ServiceStatusView>,
}

pub type ServiceStatusView = EmptyStatusView;

impl ServiceView {
    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> ServiceView {
        ServiceView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: ServiceSpecView) -> ServiceView {
        ServiceView {
            spec: Some(spec),
            ..self
        }
    }
}

impl ResourceView for ServiceView {
    type Spec = Option<ServiceSpecView>;
    type Status = Option<ServiceStatusView>;

    open spec fn default() -> ServiceView {
        ServiceView {
            metadata: ObjectMetaView::default(),
            spec: None,
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::ServiceKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<ServiceSpecView> {
        self.spec
    }

    open spec fn status(self) -> Option<ServiceStatusView> {
        self.status
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ServiceView::marshal_spec(self.spec),
            status: ServiceView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<ServiceView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ServiceView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ServiceView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(ServiceView {
                metadata: obj.metadata,
                spec: ServiceView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: ServiceView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        ServiceView::marshal_spec_preserves_integrity();
        ServiceView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: Option<ServiceSpecView>) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Option<ServiceSpecView>, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<ServiceStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<ServiceStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        &&& self.spec.is_Some()
    }

    open spec fn transition_validation(self, old_obj: ServiceView) -> bool {
        true
    }
}

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

    pub open spec fn set_cluster_ip(self, cluster_ip: StringView) -> ServiceSpecView {
        ServiceSpecView {
            cluster_ip: Some(cluster_ip),
            ..self
        }
    }

    pub open spec fn set_ports(self, ports: Seq<ServicePortView>) -> ServiceSpecView {
        ServiceSpecView {
            ports: Some(ports),
            ..self
        }
    }

    pub open spec fn set_selector(self, selector: Map<StringView, StringView>) -> ServiceSpecView {
        ServiceSpecView {
            selector: Some(selector),
            ..self
        }
    }

    pub open spec fn set_publish_not_ready_addresses(self, publish_not_ready_addresses: bool) -> ServiceSpecView {
        ServiceSpecView {
            publish_not_ready_addresses: Some(publish_not_ready_addresses),
            ..self
        }
    }

    pub open spec fn unset_publish_not_ready_addresses(self) -> ServiceSpecView {
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

    pub open spec fn set_name(self, name: StringView) -> ServicePortView {
        ServicePortView {
            name: Some(name),
            ..self
        }
    }

    pub open spec fn set_port(self, port: int) -> ServicePortView {
        ServicePortView {
            port: port,
            ..self
        }
    }

    pub open spec fn set_app_protocol(self, app_protocol: StringView) -> ServicePortView {
        ServicePortView {
            app_protocol: Some(app_protocol),
            ..self
        }
    }

    pub open spec fn set_protocol(self, protocol: StringView) -> ServicePortView {
        ServicePortView {
            protocol: Some(protocol),
            ..self
        }
    }
}

}
