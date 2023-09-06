#!/usr/bin/env bash

set -xeu

instance=$1
username=$(kubectl get secret ${instance}-default-user -o jsonpath="{.data.username}" | base64 --decode)
password=$(kubectl get secret ${instance}-default-user -o jsonpath="{.data.password}" | base64 --decode)
service=${instance}
kubectl run perf-test --image=pivotalrabbitmq/perf-test -- --uri "amqp://${username}:${password}@${service}"
