## Garbage collector

### Description

Garbage collector is a Kubernetes built-in controller designed for cleaning up cluster resources. Its major functionality is [cascading deletion](https://kubernetes.io/docs/concepts/architecture/garbage-collection/#cascading-deletion) with three modes:
- Background cascading deletion: The default mode. The Kubernetes API server deletes the owner object immediately and the garbage collector cleans up the dependent objects in the background. The dependent object is cleaned up only after all the owners are deleted.
- Foreground cascading deletion: The Kubernetes API server sets the object's `metdata.finalizers` to `foregroundDeletion` and doesn't delete the object immediately (see [this](https://github.com/kubernetes/kubernetes/blob/v1.26.3/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L869)). The garbage collector initiates deletion to the dependents of the object. Once all the blocking dependents (those have `ownerReference.blockOwnerDeletion=true`) are deleted, the garbage collector will remove the `foregroundDeletion` finalizer (see [this](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/controller/garbagecollector/garbagecollector.go#L534)), which allows the object to be finally deleted.
- Orphan dependents: The Kubernetes API server sets the object's `metdata.finalizers` to `orphan` and doesn't delete the object immediately (see [this](https://github.com/kubernetes/kubernetes/blob/v1.26.3/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L869)). The garbage collector removes the owner reference pointing this object from all its dependents, and then removes the `orphan` finalizer from the object. In this way, after the object gets deleted, the previous dependents will not be deleted (because they no long have the owner reference).

The garbage collector internally builds a in-memory graph to track the ownership dependency between objects. it sets up informers to watch delete and update events from the API server. Once the graph has any change, it starts to check whether the affected objects should be deleted. For example, if an object is deleted, it pushes its dependents into a `attemptToDelete` queue (see [this](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/controller/garbagecollector/graph_builder.go#L771)). Each object inside the `attemptToDelete` queue will be popped out and processed by [`attemptToDeleteItem`](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/controller/garbagecollector/garbagecollector.go#L500), which checks whether the object should be deleted. For example, if all its owners are deleted, the garbage collector will delete the object.

### References
Documentation:
- https://kubernetes.io/docs/concepts/architecture/garbage-collection/
- https://kubernetes.io/docs/tasks/administer-cluster/use-cascading-deletion/

Source code:
- https://github.com/kubernetes/kubernetes/tree/v1.26.3/pkg/controller/garbagecollector
