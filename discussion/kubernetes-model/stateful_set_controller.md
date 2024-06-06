## Stateful set controller

### Description

Stateful set controller is a Kubernetes built-in controller designed for managing stateful sets, i.e., a collection of pods (running the same image) with persistent volumes. The stateful set controller does two things on high level:
- Scaling: Make the number of running pods match `.spec.replicas`. If there are more running pods than `.spec.replicas`, the stateful set controller will delete some, and if there are less it will create more. The number of existing pods belonging to the stateful set is shown in `.status.replicas` (and the ready ones are shown in `.status.ready_replicas`). 
- Rolling update: Make the spec of the running pods match `.spec.template`. If some pod has outdated spec, the stateful set controller will delete and recreate that pod (causing the containerized application to restart). When performing update, the number of existing pods that use the old (resp. new) spec is shown in `.status.current_replicas` (resp. `.status.update_replicas`).

The stateful set controller follows the state-reconciliation principle: it looks at the current stateful set object to perform scaling and rolling update in the [`sync`](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/controller/statefulset/stateful_set.go#L437) function.

However, to correctly set the `.status` fields that talk about pods with new/old spec, the stateful set controller needs to know (a little bit) *history* of this stateful set object (e.g., what is the previous spec for its pod?). To obtain the history without breaking the state-reconciliation principle, the stateful set controller uses a list of [controller revision](https://github.com/kubernetes/kubernetes/blob/v1.26.3/staging/src/k8s.io/api/apps/v1/types.go#L925) objects to record the historical pod specs for each stateful set object.

The concrete reconciliation logic can be found in [`UpdateStatefulSet`](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/controller/statefulset/stateful_set_control.go#L78), which consists of three parts:
- Record the new spec: The controller will create a new controller revision object to record the new pod spec (`.spec.template`) in [`getStatefulSetRevisions`](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/controller/statefulset/stateful_set_control.go#L101), unless the same pod spec has been used before (so the corresponding controller revision object already exists). The list of controller revision objects form the history of the pod specs used by this stateful set object (by default only the latest 10 are kept in etcd).
- Manage pods based on the new and the last spec: The controller only needs the new spec and the last spec to decide which pod to create/delete in [`updateStatefulSet`](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/controller/statefulset/stateful_set_control.go#L107). For scaling, the number of pods that exist (shown in `.status.replicas`) eventually matches the desired number (`.spec.replicas`). For rolling update, all pods with the old spec will be eventually be replaced by pods with the new spec one by one. That is, `.status.current_replicas` (pods with old spec) gradually drops to 0, meanwhile `.status.update_replicas` (pods with new spec) gradually climbs to `.status.replicas`.
- Update status: The controller updates `.status` of the stateful set object after each round of reconciliation to reflect the progress of scaling and rolling update in [`updateStatefulSetStatus`](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/controller/statefulset/stateful_set_control.go#L113). When the rolling update completes (`.status.update_replicas == .status.replicas`) the controller sets the value of `.status.current_replicas` to `.status.update_replicas` (see [`completeRollingUpdate`](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/controller/statefulset/stateful_set_utils.go#L587)).

### References
Documentation:
- https://kubernetes.io/docs/concepts/workloads/controllers/statefulset/
- https://kubernetes.io/docs/reference/kubernetes-api/workload-resources/controller-revision-v1/

Source code:
- https://github.com/kubernetes/kubernetes/tree/v1.26.3/pkg/controller/statefulset
