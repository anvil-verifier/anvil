## Finalizers

### Description

Finalizers, as a field in metadata, is used to tell Kubernetes to wait until certain conditions are met before it actually deletes resources. There are standard finalizers such as `foregroundDeletion` and `orphan` used by the garbage collector, and users can also create their own finalizers which are handled by their custom controllers.

When sending a deletion request to an object, the API server performs several checks to decide whether to immediately remove the object from the backend key-value store (i.e., etcd). It first checks whether the object has at least one finalizer (see [this](https://github.com/kubernetes/kubernetes/tree/v1.26.3/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1058)), or `foregroundDeletion` and `orphan` should be added to the object's finalizers because of the deletion option (see [this](https://github.com/kubernetes/kubernetes/tree/v1.26.3/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1065)). It takes different actions depending on the results:
- If so, the API server sets the deletion timestamp and returns, instead of deleting the object (see [this](https://github.com/kubernetes/kubernetes/tree/v1.26.3/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L997) and [this](https://github.com/kubernetes/kubernetes/tree/v1.26.3/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1081)).
- If not, the API server immediately deletes the object from the key-value store (see [this](https://github.com/kubernetes/kubernetes/tree/v1.26.3/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1100)).

For the first case (finalizers exist), the actual deletion is completed by a later update that removes the finalizer from the object. When handling the update request, if the API server finds that the object has no finalizers and has a deletion timestamp, it will delete the object from the key-value store after updating the object in the key-value store (see [this](https://github.com/kubernetes/kubernetes/tree/v1.26.3/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L691)). Such update requests are usually sent by controllers that manage different finalizers (e.g., garbage collector).

Note that besides the finalizers, deletion might also get deferred due to graceful period (`deletionGracePeriodSeconds`), which is called graceful deletion. Graceful deletion is usually only applied to pods.

### References
Documentation:
- https://kubernetes.io/docs/concepts/overview/working-with-objects/finalizers/

Source code:
- https://github.com/kubernetes/kubernetes/tree/v1.26.3/staging/src/k8s.io/apiserver/pkg/registry/generic/registry
