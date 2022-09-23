## Assumptions on environments

We start from simple.

Things we include in the current version:
- controller crash

Things we do NOT include yet:
- network message loss
- network partition
- staleness at the k8s side (this will be implemented by adding API server hosts into distributed system part)
- ...

## Abstraction

The abstract state includes:
- a map where the key is the object key (i.e., combination of resource type, namespace, name) and the value is the kubernetes object
- a clock for each controller

We have predicates on the abstract state that should always be true:
- if the clock is C, cm1 and cm2 both exist in the map
- if cm2 exists in the map, cm1 exists in the map
- ...

## Distributed System
The distributed system composite includes the following:
- controller host
- database host
- network

We start from having just one controller host.
We also need a few client events to trigger the distributed system,
like sending a message to the database host to create the custom resource.

### Controller Host
The controller host can take the following actions:
- receive a state update message from the database host and push it to a queue
- pop out a message from the queue and start a reconcile
- run one step of the reconcile logic that ends with one state object update or query -- this is the controller logic function
- receive an OK and the object from the database and unblock the next step
- end a reconcile (this only happens when all the reconcile logic steps are done)

We start from assuming controller has no local indexer for caching states across reconciles.
We do not allow concurrent reconcile logic.
That is, once starting a reconcile, the controller host has to finish all the steps and ends the reconcile before start another one.
After each step, the controller has to wait for the reply from the database to continue to next step.

### Database Host
We start from assuming there is only the etcd hosting the entire cluster state and ignoring API servers for now.
The database host can take the following actions:
- receive a state query message and send an OK and the object back
- receive a state update message from the controller, updates the object state, send an OK and the object back and marks the object as fresh
- send a message for one object marked as fresh to the controller and mark it as unfresh

Note that we are assuming (1) only the single controller cares about the object and (2) the single controller cares about every object. These two might not be true but we can stay with them for now.

### Network
The network can take the following actions:
- deliver a message to the dest if the message has been sent to the network

Note that this implicitly means we are considering network message duplicate and reordering.

