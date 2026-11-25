// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::common::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// OwnerReferenceView is the ghost type of OwnerReference.


pub struct OwnerReferenceView {
    pub block_owner_deletion: Option<bool>,
    pub controller: Option<bool>,
    pub kind: Kind,
    pub name: StringView,
    pub uid: Uid,
}

impl OwnerReferenceView {
    // default() isn't needed; this is just to make the macro implement_field_wrapper_type happy
    pub uninterp spec fn default() -> OwnerReferenceView;
}

// The kind of the object an owner reference names, given by the reference's apiVersion and kind
// strings. Each kind the model knows gets its own Kind; any other pair gets a custom-resource kind
// that encodes the pair (its first character, '\0', never starts a kind above, and the length of
// apiVersion separates the two strings), so two references with different apiVersion or kind
// strings never get the same kind.
pub open spec fn owner_reference_kind_view(api_version: StringView, kind: StringView) -> Kind {
    if api_version == "v1"@ && kind == "ConfigMap"@ {
        Kind::ConfigMapKind
    } else if api_version == "apps/v1"@ && kind == "DaemonSet"@ {
        Kind::DaemonSetKind
    } else if api_version == "v1"@ && kind == "PersistentVolumeClaim"@ {
        Kind::PersistentVolumeClaimKind
    } else if api_version == "v1"@ && kind == "Pod"@ {
        Kind::PodKind
    } else if api_version == "rbac.authorization.k8s.io/v1"@ && kind == "Role"@ {
        Kind::RoleKind
    } else if api_version == "rbac.authorization.k8s.io/v1"@ && kind == "RoleBinding"@ {
        Kind::RoleBindingKind
    } else if api_version == "apps/v1"@ && kind == "StatefulSet"@ {
        Kind::StatefulSetKind
    } else if api_version == "v1"@ && kind == "Service"@ {
        Kind::ServiceKind
    } else if api_version == "v1"@ && kind == "ServiceAccount"@ {
        Kind::ServiceAccountKind
    } else if api_version == "v1"@ && kind == "Secret"@ {
        Kind::SecretKind
    } else if api_version == "anvil.dev/v1"@ && kind == "VReplicaSet"@ {
        Kind::CustomResourceKind("vreplicaset"@)
    } else if api_version == "anvil.dev/v1"@ && kind == "VDeployment"@ {
        Kind::CustomResourceKind("vdeployment"@)
    } else if api_version == "anvil.dev/v1"@ && kind == "VStatefulSet"@ {
        Kind::CustomResourceKind("vstatefulset"@)
    } else if api_version == "anvil.dev/v1"@ && kind == "RabbitmqCluster"@ {
        Kind::CustomResourceKind("rabbitmq"@)
    } else {
        Kind::CustomResourceKind(owner_reference_kind_view_fallback(api_version, kind))
    }
}

pub proof fn lemma_owner_reference_kind_view_of_crds()
    ensures
        owner_reference_kind_view("anvil.dev/v1"@, "VReplicaSet"@) == Kind::CustomResourceKind("vreplicaset"@),
        owner_reference_kind_view("anvil.dev/v1"@, "VDeployment"@) == Kind::CustomResourceKind("vdeployment"@),
        owner_reference_kind_view("anvil.dev/v1"@, "VStatefulSet"@) == Kind::CustomResourceKind("vstatefulset"@),
        owner_reference_kind_view("anvil.dev/v1"@, "RabbitmqCluster"@) == Kind::CustomResourceKind("rabbitmq"@),
{
    reveal_strlit("v1");
    reveal_strlit("apps/v1");
    reveal_strlit("rbac.authorization.k8s.io/v1");
    reveal_strlit("anvil.dev/v1");
    reveal_strlit("ConfigMap");
    reveal_strlit("DaemonSet");
    reveal_strlit("PersistentVolumeClaim");
    reveal_strlit("Pod");
    reveal_strlit("Role");
    reveal_strlit("RoleBinding");
    reveal_strlit("StatefulSet");
    reveal_strlit("Service");
    reveal_strlit("ServiceAccount");
    reveal_strlit("Secret");
    reveal_strlit("VReplicaSet");
    reveal_strlit("VDeployment");
    reveal_strlit("VStatefulSet");
    reveal_strlit("RabbitmqCluster");
}

pub open spec fn owner_reference_kind_view_fallback(api_version: StringView, kind: StringView) -> StringView {
    seq!['\0'] + nat_to_string_view(api_version.len()) + seq![':'] + api_version + kind
}

proof fn lemma_owner_reference_kind_view_fallback_injective(
    a1: StringView, k1: StringView, a2: StringView, k2: StringView,
)
    requires
        owner_reference_kind_view_fallback(a1, k1) == owner_reference_kind_view_fallback(a2, k2),
    ensures
        a1 == a2 && k1 == k2,
{
    let l1 = nat_to_string_view(a1.len());
    let l2 = nat_to_string_view(a2.len());
    lemma_nat_to_string_view_props(a1.len());
    lemma_nat_to_string_view_props(a2.len());
    let s1 = owner_reference_kind_view_fallback(a1, k1);
    let s2 = owner_reference_kind_view_fallback(a2, k2);
    assert(forall |i: int| 0 <= i < l1.len() ==> (#[trigger] l1[i]) != ':') by {
        assert forall |i: int| 0 <= i < l1.len() implies (#[trigger] l1[i]) != ':' by {
            assert(48u8 <= (l1[i] as u8) <= 57u8);
        }
    }
    assert(forall |i: int| 0 <= i < l2.len() ==> (#[trigger] l2[i]) != ':') by {
        assert forall |i: int| 0 <= i < l2.len() implies (#[trigger] l2[i]) != ':' by {
            assert(48u8 <= (l2[i] as u8) <= 57u8);
        }
    }
    if l1.len() < l2.len() {
        assert(s1[1 + l1.len() as int] == ':');
        assert(s2[1 + l1.len() as int] == l2[l1.len() as int]);
        assert(false);
    }
    if l2.len() < l1.len() {
        assert(s2[1 + l2.len() as int] == ':');
        assert(s1[1 + l2.len() as int] == l1[l2.len() as int]);
        assert(false);
    }
    assert(l1 =~= s1.subrange(1, 1 + l1.len() as int));
    assert(l2 =~= s2.subrange(1, 1 + l2.len() as int));
    lemma_nat_to_string_view_injective(a1.len(), a2.len());
    assert(a1 =~= s1.subrange(2 + l1.len() as int, 2 + l1.len() as int + a1.len() as int));
    assert(a2 =~= s2.subrange(2 + l2.len() as int, 2 + l2.len() as int + a2.len() as int));
    assert(k1 =~= s1.subrange(2 + l1.len() as int + a1.len() as int, s1.len() as int));
    assert(k2 =~= s2.subrange(2 + l2.len() as int + a2.len() as int, s2.len() as int));
}

// Owner references with different apiVersion or kind strings have different kinds, so that an
// owner reference's view determines its strings (which ObjectMeta::owner_references_contains
// relies on, as it compares the k8s-openapi structs).
pub proof fn lemma_owner_reference_kind_view_injective(
    a1: StringView, k1: StringView, a2: StringView, k2: StringView,
)
    requires
        owner_reference_kind_view(a1, k1) == owner_reference_kind_view(a2, k2),
    ensures
        a1 == a2 && k1 == k2,
{
    reveal_strlit("vreplicaset");
    reveal_strlit("vdeployment");
    reveal_strlit("vstatefulset");
    reveal_strlit("rabbitmq");
    let f1 = owner_reference_kind_view_fallback(a1, k1);
    let f2 = owner_reference_kind_view_fallback(a2, k2);
    assert(f1[0] == '\0' && f2[0] == '\0');
    assert("vreplicaset"@[0] != '\0' && "vdeployment"@[0] != '\0' && "vstatefulset"@[0] != '\0' && "rabbitmq"@[0] != '\0');
    assert("vreplicaset"@ != "vdeployment"@ && "vreplicaset"@ != "vstatefulset"@ && "vdeployment"@ != "vstatefulset"@) by {
        assert("vreplicaset"@[1] != "vdeployment"@[1]);
        assert("vreplicaset"@[1] != "vstatefulset"@[1]);
        assert("vdeployment"@[1] != "vstatefulset"@[1]);
    }
    assert("rabbitmq"@[0] != "vreplicaset"@[0]);
    if owner_reference_kind_view(a1, k1) == Kind::CustomResourceKind(f1)
        && owner_reference_kind_view(a2, k2) == Kind::CustomResourceKind(f2) {
        lemma_owner_reference_kind_view_fallback_injective(a1, k1, a2, k2);
    }
}

pub open spec fn owner_reference_to_object_reference(owner_reference: OwnerReferenceView, namespace: StringView) -> ObjectRef {
    ObjectRef {
        kind: owner_reference.kind,
        namespace: namespace,
        name: owner_reference.name,
    }
}

pub open spec fn controller_owner_filter() -> spec_fn(OwnerReferenceView) -> bool {
    |o: OwnerReferenceView| o.controller is Some && o.controller->0
}

pub open spec fn owner_reference_eq_without_uid(r1: OwnerReferenceView, r2: OwnerReferenceView) -> bool {
    &&& r1.controller == r2.controller
    &&& r1.block_owner_deletion == r2.block_owner_deletion
    &&& r1.kind == r2.kind
    &&& r1.name == r2.name
}

}
