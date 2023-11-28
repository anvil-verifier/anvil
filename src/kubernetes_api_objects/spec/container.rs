// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, marshal::*, resource::*, resource_requirements::*, volume::*,
};
use crate::vstd_ext::string_view::*;
use vstd::{prelude::*, string::*};

verus! {

pub struct ContainerView {
    pub env: Option<Seq<EnvVarView>>,
    pub image: Option<StringView>,
    pub name: StringView,
    pub ports: Option<Seq<ContainerPortView>>,
    pub volume_mounts: Option<Seq<VolumeMountView>>,
    pub lifecycle: Option<LifecycleView>,
    pub resources: Option<ResourceRequirementsView>,
    pub readiness_probe: Option<ProbeView>,
    pub liveness_probe: Option<ProbeView>,
    pub command: Option<Seq<StringView>>,
    pub image_pull_policy: Option<StringView>,
    pub args: Option<Seq<StringView>>,
    pub security_context: Option<SecurityContextView>,
}

impl ContainerView {
    pub open spec fn default() -> ContainerView {
        ContainerView {
            env: None,
            image: None,
            name: new_strlit("")@,
            ports: None,
            volume_mounts: None,
            lifecycle: None,
            resources: None,
            readiness_probe: None,
            liveness_probe: None,
            command: None,
            image_pull_policy: None,
            args: None,
            security_context: None,
        }
    }

    pub open spec fn set_env(self, env: Seq<EnvVarView>) -> ContainerView {
        ContainerView {
            env: Some(env),
            ..self
        }
    }

    pub open spec fn set_image(self, image: StringView) -> ContainerView {
        ContainerView {
            image: Some(image),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ContainerView {
        ContainerView {
            name: name,
            ..self
        }
    }

    pub open spec fn set_ports(self, ports: Seq<ContainerPortView>) -> ContainerView {
        ContainerView {
            ports: Some(ports),
            ..self
        }
    }

    pub open spec fn set_volume_mounts(self, volume_mounts: Seq<VolumeMountView>) -> ContainerView {
        ContainerView {
            volume_mounts: Some(volume_mounts),
            ..self
        }
    }

    pub open spec fn set_lifecycle(self, lifecycle: LifecycleView) -> ContainerView {
        ContainerView {
            lifecycle: Some(lifecycle),
            ..self
        }
    }

    pub open spec fn set_resources(self, resources: ResourceRequirementsView) -> ContainerView {
        ContainerView {
            resources: Some(resources),
            ..self
        }
    }

    pub open spec fn unset_resources(self) -> ContainerView {
        ContainerView {
            resources: None,
            ..self
        }
    }

    pub open spec fn set_readiness_probe(self, readiness_probe: ProbeView) -> ContainerView {
        ContainerView {
            readiness_probe: Some(readiness_probe),
            ..self
        }
    }

    pub open spec fn set_liveness_probe(self, liveness_probe: ProbeView) -> ContainerView {
        ContainerView {
            liveness_probe: Some(liveness_probe),
            ..self
        }
    }

    pub open spec fn set_command(self, command: Seq<StringView>) -> ContainerView {
        ContainerView {
            command: Some(command),
            ..self
        }
    }

    pub open spec fn set_image_pull_policy(self, image_pull_policy: StringView) -> ContainerView {
        ContainerView {
            image_pull_policy: Some(image_pull_policy),
            ..self
        }
    }

    pub open spec fn set_args(self, args: Seq<StringView>) -> ContainerView {
        ContainerView {
            args: Some(args),
            ..self
        }
    }

    pub open spec fn set_security_context(self, security_context: SecurityContextView) -> ContainerView {
        ContainerView {
            security_context: Some(security_context),
            ..self
        }
    }
}

pub struct LifecycleView {
    pub pre_stop: Option<LifecycleHandlerView>,
}

impl LifecycleView {
    pub open spec fn default() -> LifecycleView {
        LifecycleView {
            pre_stop: None,
        }
    }

    pub open spec fn set_pre_stop(self, pre_stop: LifecycleHandlerView) -> LifecycleView {
        LifecycleView {
            pre_stop: Some(pre_stop),
            ..self
        }
    }
}

pub struct LifecycleHandlerView {
    pub exec_: Option<ExecActionView>,
}

impl LifecycleHandlerView {
    pub open spec fn default() -> LifecycleHandlerView {
        LifecycleHandlerView {
            exec_: None,
        }
    }

    pub open spec fn set_exec(self, exec: ExecActionView) -> LifecycleHandlerView {
        LifecycleHandlerView {
            exec_: Some(exec),
            ..self
        }
    }
}

pub struct ContainerPortView {
    pub container_port: int,
    pub name: Option<StringView>,
    pub protocol: Option<StringView>,
}

impl ContainerPortView {
    pub open spec fn default() -> ContainerPortView {
        ContainerPortView {
            container_port: 0, // TODO: is this the correct default value?
            name: None,
            protocol: None,
        }
    }

    pub open spec fn set_container_port(self, container_port: int) -> ContainerPortView {
        ContainerPortView {
            container_port: container_port,
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ContainerPortView {
        ContainerPortView {
            name: Some(name),
            ..self
        }
    }

    pub open spec fn set_protocol(self, protocol: StringView) -> ContainerPortView {
        ContainerPortView {
            protocol: Some(protocol),
            ..self
        }
    }
}

pub struct VolumeMountView {
    pub mount_path: StringView,
    pub name: StringView,
    pub read_only: Option<bool>,
    pub sub_path: Option<StringView>,
    pub mount_propagation: Option<StringView>,
}

impl VolumeMountView {
    pub open spec fn default() -> VolumeMountView {
        VolumeMountView {
            mount_path: new_strlit("")@,
            name: new_strlit("")@,
            read_only: Some(false),
            sub_path: None,
            mount_propagation: None,
        }
    }

    pub open spec fn set_mount_path(self, mount_path: StringView) -> VolumeMountView {
        VolumeMountView {
            mount_path: mount_path,
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> VolumeMountView {
        VolumeMountView {
            name: name,
            ..self
        }
    }

    pub open spec fn set_read_only(self, read_only: bool) -> VolumeMountView {
        VolumeMountView {
            read_only: Some(read_only),
            ..self
        }
    }

    pub open spec fn set_sub_path(self, sub_path: StringView) -> VolumeMountView {
        VolumeMountView {
            sub_path: Some(sub_path),
            ..self
        }
    }

    pub open spec fn overwrite_mount_propagation(self, mount_propagation: Option<StringView>) -> VolumeMountView {
        VolumeMountView {
            mount_propagation: mount_propagation,
            ..self
        }
    }
}

pub struct ProbeView {
    pub exec_: Option<ExecActionView>,
    pub failure_threshold: Option<int>,
    pub initial_delay_seconds: Option<int>,
    pub period_seconds: Option<int>,
    pub success_threshold: Option<int>,
    pub tcp_socket: Option<TCPSocketActionView>,
    pub timeout_seconds: Option<int>,
}

impl ProbeView {
    pub open spec fn default() -> ProbeView {
        ProbeView {
            exec_: None,
            failure_threshold: None,
            initial_delay_seconds: None,
            period_seconds: None,
            success_threshold: None,
            tcp_socket: None,
            timeout_seconds: None,
        }
    }

    pub open spec fn set_exec(self, exec: ExecActionView) -> ProbeView {
        ProbeView {
            exec_: Some(exec),
            ..self
        }
    }

    pub open spec fn set_failure_threshold(self, failure_threshold: int) -> ProbeView {
        ProbeView {
            failure_threshold: Some(failure_threshold),
            ..self
        }
    }

    pub open spec fn set_initial_delay_seconds(self, initial_delay_seconds: int) -> ProbeView {
        ProbeView {
            initial_delay_seconds: Some(initial_delay_seconds),
            ..self
        }
    }

    pub open spec fn set_period_seconds(self, period_seconds: int) -> ProbeView {
        ProbeView {
            period_seconds: Some(period_seconds),
            ..self
        }
    }

    pub open spec fn set_success_threshold(self, success_threshold: int) -> ProbeView {
        ProbeView {
            success_threshold: Some(success_threshold),
            ..self
        }
    }

    pub open spec fn set_tcp_socket(self, tcp_socket: TCPSocketActionView) -> ProbeView {
        ProbeView {
            tcp_socket: Some(tcp_socket),
            ..self
        }
    }

    pub open spec fn set_timeout_seconds(self, timeout_seconds: int) -> ProbeView {
        ProbeView {
            timeout_seconds: Some(timeout_seconds),
            ..self
        }
    }
}

pub struct ExecActionView {
    pub command: Option<Seq<StringView>>,
}

impl ExecActionView {
    pub open spec fn default() -> ExecActionView {
        ExecActionView {
            command: None,
        }
    }

    pub open spec fn set_command(self, command: Seq<StringView>) -> ExecActionView {
        ExecActionView {
            command: Some(command),
            ..self
        }
    }
}

pub struct TCPSocketActionView {
    pub host: Option<StringView>,
    pub port: int,
}

impl TCPSocketActionView {
    pub open spec fn default() -> TCPSocketActionView {
        TCPSocketActionView {
            host: None,
            port: 0,
        }
    }

    pub open spec fn set_host(self, host: StringView) -> TCPSocketActionView {
        TCPSocketActionView {
            host: Some(host),
            ..self
        }
    }

    pub open spec fn set_port(self, port: int) -> TCPSocketActionView {
        TCPSocketActionView {
            port: port,
            ..self
        }
    }
}

pub struct EnvVarView {
    pub name: StringView,
    pub value: Option<StringView>,
    pub value_from: Option<EnvVarSourceView>,
}

impl EnvVarView {
    pub open spec fn default() -> EnvVarView {
        EnvVarView {
            name: new_strlit("")@,
            value: None,
            value_from: None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> EnvVarView {
        EnvVarView {
            name: name,
            ..self
        }
    }

    pub open spec fn overwrite_value(self, value: Option<StringView>) -> EnvVarView {
        EnvVarView {
            value: value,
            ..self
        }
    }

    pub open spec fn overwrite_value_from(self, value_from: Option<EnvVarSourceView>) -> EnvVarView {
        EnvVarView {
            value_from: value_from,
            ..self
        }
    }
}

pub struct EnvVarSourceView {
    pub field_ref: Option<ObjectFieldSelectorView>,
}

impl EnvVarSourceView {
    pub open spec fn default() -> EnvVarSourceView {
        EnvVarSourceView {
            field_ref: None,
        }
    }

    pub open spec fn set_field_ref(self, field_ref: ObjectFieldSelectorView) -> EnvVarSourceView {
        EnvVarSourceView {
            field_ref: Some(field_ref),
            ..self
        }
    }
}

pub struct SecurityContextView {}

}
