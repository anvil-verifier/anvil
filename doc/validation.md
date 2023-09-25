## Validation

### Description

Kubernetes employs rich semantic validation for all types of state objects. Such validation happens after the API server accepts the requests and before the objects get created/updated to the back-end key-value store (etcd). If the validation fails, the request will fail with typically an error code returned to the client.

In general, there are two types of validation rules: validation for single object and validation for transition. The former checks whether a single object is valid, and the latter checks whether a transition (a new object and an old object) is valid. A few representative examples of such validation rules are:
- Object validation: There cannot be more than one controller owner reference. See https://github.com/kubernetes/kubernetes/blob/v1.26.3/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L92
- Transition validation: There cannot be new finalizers added to the object if the object is set to be deleted. See https://github.com/kubernetes/kubernetes/blob/v1.26.3/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L121

We do not have a complete list of validation rules here, but the common ones can be found at:
- [staging/src/k8s.io/apimachinery/pkg/api/validation](https://github.com/kubernetes/kubernetes/blob/v1.26.3/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go)
- [pkg/registry/apps/statefulset/strategy.go](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/registry/apps/statefulset/strategy.go) (replace `apps` with other groups and `statefulset` with other types)
- [pkg/apis/apps/validation/validation.go](https://github.com/kubernetes/kubernetes/blob/v1.26.3/pkg/apis/apps/validation/validation.go) (replace `apps` with other groups)
