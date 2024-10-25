When verifying interactions between controllers, we find it hard to specify the fairness assumptions that allow controllers to make progress while there are races on the resource version number of the same object (stored in etcd).

## Background
Kubernetes controllers often employ a pattern that it reads an object from etcd and then writes the updated object back to etcd. 
Note that:
- etcd uses version based concurrency control for each object, and the version numbers behave like logical timestamps
- each object in etcd has its own version number
- each write to the object in etcd will increment its version number
- each write must carry a version number `v`, and the write succeeds only if `v` equals to the current version number of that object

## Problem
Now suppose our controller $C$ runs:
```
for {
    ... // do something
    obj, v = read(name);
    if P(obj) {
        obj' = modify1(obj);
        if write(name, obj', v) != ok {
            continue
        }
    }
    ... // do something
}
```

And there is a set of other controllers $S$ ($S$ won't grow) that each of them runs:
```
for {
    ... // do something
    obj, v = read(name);
    obj' = modify2(obj);
    ... // do something
    write(name, obj', v);
    ... // do something
}
```

Assume that initially `P` holds true for the object in etcd and only $C$'s `write` invalidates `P`.
That is, $C$ will retry its `write` until it succeeds.

The pseudocode above turns into state machine actions: in each (atomic) action, a controller receives the response from the last request it sent (if any), performs internal computation, and then sends one request (`read` or `write`) to the network. We do NOT assume the entire block is atomic.

The network and etcd are also modeled as state machine actions. The network connects controllers to etcd has delay and can reorder messages. In each (atomic) action, etcd handles on request sent by some controller and sends a reply to the network.

We currently assume fairness on controller's actions and etcd's actions.

The problem is how to prove that $C$ eventually successfully writes the object (for at least once).
Since $C$ races with every controller in $S$ on the version number, we need to prove that $C$ eventually wins the race (for at least once).

*However, we find that neither weak fairness nor strong fairness can solve the problem.* To see why, consider the following execution:
```
C                       S
v1 = read()
                        v1 = read()
                        write(..., v1) // ok, v1 -> v2 in etcd
write(..., v1) // err
v2 = read()
                        v2 = read()
                        write(..., v2) // ok, v2 -> v3 in etcd
write(..., v2) // err
...                     ...
```
where every time between $C$'s `read` and `write`, some controller from $S$ successfully writes the object, making the version number read by $C$ no longer fresh. In this execution, $C$ runs fairly but it will never successfully writes the object.

Note that this example is realistic. In practice, Kubernetes controllers share objects in this way --- they update different parts of the object while racing with each other. This usually doesn't block any controller's progress indefinitely, because (1) there is usually a long time window between each controller's successful `write` and its next `write`, (2) if a controller's `write` fails, it can aggressively retry `read; if P { write; }`, and (3) there aren't too many controllers sharing the same object at the same time.