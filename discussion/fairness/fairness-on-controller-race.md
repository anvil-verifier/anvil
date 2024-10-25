When verifying interactions between controllers, we find it hard to specify the fairness assumptions that allow controllers to make progress while there are races on the resource version number of the same object (stored in etcd).

## Background
Kubernetes controllers often employ a pattern that it reads an object from etcd (which uses version control for stored objects) and then writes the updated object back to etcd.
Note that:
- each object in etcd has its own version number
- each write to the object in etcd will increment its version number
- each write must carry a version number, and the write succeeds only if the carried number equals to the current version number of that object

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
and there is a set of other controllers $S$ ($S$ won't grow) that each of them runs:
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
And `modify1` and `modify2` modifies different parts of the object.

The problem is how to prove that $C$ eventually successfully writes the object (for at least once) with some fairness assumption.
Since $C$ races with every controller in $S$ on the version number, the fairness assumption needs to imply that $C$ eventually wins the race (for at least once).

We find that even strong fairness is not sufficient to prove liveness here. To see why, consider the following execution:
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