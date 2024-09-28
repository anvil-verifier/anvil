## Unconditional update

### Description

Many types of Kubernetes objects allow one to update the objects without providing a resource version, which is called [unconditional update](https://github.com/kubernetes/kubernetes/blob/v1.30.0/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L623-L631). During conditional update, API server will not perform resource version checking.

Objects that allow unconditional update include:
- [ConfigMap](https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/core/configmap/strategy.go#L96-L98)
- [Secret](https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/core/secret/strategy.go#L100-L102)
- [Service](https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/core/service/strategy.go#L112-L114)
- [Pod](https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/core/pod/strategy.go#L161-L164)
- [ReplicaSet](https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/apps/replicaset/strategy.go#L179-L181)
- [Deployment](https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/apps/deployment/strategy.go#L167-L169)
- [DaemonSet](https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/apps/daemonset/strategy.go#L183-L186)
- [StatefulSet](https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/apps/statefulset/strategy.go#L189-L192)

Objects that do not allow unconditional update include:
- [CustomResource](https://github.com/kubernetes/kubernetes/blob/v1.30.0/staging/src/k8s.io/apiextensions-apiserver/pkg/registry/customresource/strategy.go#L271-L274)
