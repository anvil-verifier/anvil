#!/usr/bin/env bash

## Verify the controller alone without verifying the Anvil framework.

set -xeu

YELLOW='\033[1;33m'
GREEN='\033[1;32m'
RED='\033[0;31m'
NC='\033[0m'

app=$1

if [ "$app" = "fluent" ]; then
    ./build.sh fluent_controller.rs --emit=dep-info --time --time-expanded --output-json --rlimit 50 --num-threads 1 \
        --verify-module fluent_controller \
        --verify-module fluent_controller::fluentbit \
        --verify-module fluent_controller::fluentbit::common \
        --verify-module fluent_controller::fluentbit::exec \
        --verify-module fluent_controller::fluentbit::exec::reconciler \
        --verify-module fluent_controller::fluentbit::exec::resource \
        --verify-module fluent_controller::fluentbit::exec::resource::common \
        --verify-module fluent_controller::fluentbit::exec::resource::daemon_set \
        --verify-module fluent_controller::fluentbit::exec::resource::role \
        --verify-module fluent_controller::fluentbit::exec::resource::role_binding \
        --verify-module fluent_controller::fluentbit::exec::resource::service_account \
        --verify-module fluent_controller::fluentbit::exec::types \
        --verify-module fluent_controller::fluentbit::proof \
        --verify-module fluent_controller::fluentbit::proof::helper_invariants \
        --verify-module fluent_controller::fluentbit::proof::helper_invariants::owner_ref \
        --verify-module fluent_controller::fluentbit::proof::helper_invariants::predicate \
        --verify-module fluent_controller::fluentbit::proof::helper_invariants::proof \
        --verify-module fluent_controller::fluentbit::proof::helper_invariants::unchangeable \
        --verify-module fluent_controller::fluentbit::proof::helper_invariants::validation \
        --verify-module fluent_controller::fluentbit::proof::liveness \
        --verify-module fluent_controller::fluentbit::proof::liveness::daemon_set_match \
        --verify-module fluent_controller::fluentbit::proof::liveness::proof \
        --verify-module fluent_controller::fluentbit::proof::liveness::resource_match \
        --verify-module fluent_controller::fluentbit::proof::liveness::spec \
        --verify-module fluent_controller::fluentbit::proof::liveness::terminate \
        --verify-module fluent_controller::fluentbit::proof::liveness_theorem \
        --verify-module fluent_controller::fluentbit::proof::predicate \
        --verify-module fluent_controller::fluentbit::proof::resource \
        --verify-module fluent_controller::fluentbit::spec \
        --verify-module fluent_controller::fluentbit::spec::reconciler \
        --verify-module fluent_controller::fluentbit::spec::resource \
        --verify-module fluent_controller::fluentbit::spec::resource::common \
        --verify-module fluent_controller::fluentbit::spec::resource::daemon_set \
        --verify-module fluent_controller::fluentbit::spec::resource::role \
        --verify-module fluent_controller::fluentbit::spec::resource::role_binding \
        --verify-module fluent_controller::fluentbit::spec::resource::service_account \
        --verify-module fluent_controller::fluentbit::spec::types \
        --verify-module fluent_controller::fluentbit_config \
        --verify-module fluent_controller::fluentbit_config::common \
        --verify-module fluent_controller::fluentbit_config::exec \
        --verify-module fluent_controller::fluentbit_config::exec::reconciler \
        --verify-module fluent_controller::fluentbit_config::exec::resource \
        --verify-module fluent_controller::fluentbit_config::exec::resource::common \
        --verify-module fluent_controller::fluentbit_config::exec::resource::secret \
        --verify-module fluent_controller::fluentbit_config::exec::types \
        --verify-module fluent_controller::fluentbit_config::proof \
        --verify-module fluent_controller::fluentbit_config::proof::helper_invariants \
        --verify-module fluent_controller::fluentbit_config::proof::helper_invariants::owner_ref \
        --verify-module fluent_controller::fluentbit_config::proof::helper_invariants::predicate \
        --verify-module fluent_controller::fluentbit_config::proof::helper_invariants::proof \
        --verify-module fluent_controller::fluentbit_config::proof::liveness \
        --verify-module fluent_controller::fluentbit_config::proof::liveness::proof \
        --verify-module fluent_controller::fluentbit_config::proof::liveness::resource_match \
        --verify-module fluent_controller::fluentbit_config::proof::liveness::spec \
        --verify-module fluent_controller::fluentbit_config::proof::liveness::terminate \
        --verify-module fluent_controller::fluentbit_config::proof::liveness_theorem \
        --verify-module fluent_controller::fluentbit_config::proof::predicate \
        --verify-module fluent_controller::fluentbit_config::proof::resource \
        --verify-module fluent_controller::fluentbit_config::spec \
        --verify-module fluent_controller::fluentbit_config::spec::reconciler \
        --verify-module fluent_controller::fluentbit_config::spec::resource \
        --verify-module fluent_controller::fluentbit_config::spec::resource::common \
        --verify-module fluent_controller::fluentbit_config::spec::resource::secret \
        --verify-module fluent_controller::fluentbit_config::spec::types \
        > fluent.json
elif [ "$app" = "rabbitmq" ]; then
    ./build.sh rabbitmq_controller.rs --emit=dep-info --time --time-expanded --output-json --rlimit 50 --num-threads 1 \
        --verify-module rabbitmq_controller \
        --verify-module rabbitmq_controller::common \
        --verify-module rabbitmq_controller::exec \
        --verify-module rabbitmq_controller::exec::reconciler \
        --verify-module rabbitmq_controller::exec::resource \
        --verify-module rabbitmq_controller::exec::resource::common \
        --verify-module rabbitmq_controller::exec::resource::config_map \
        --verify-module rabbitmq_controller::exec::resource::default_user_secret \
        --verify-module rabbitmq_controller::exec::resource::erlang_cookie \
        --verify-module rabbitmq_controller::exec::resource::headless_service \
        --verify-module rabbitmq_controller::exec::resource::rabbitmq_plugins \
        --verify-module rabbitmq_controller::exec::resource::role \
        --verify-module rabbitmq_controller::exec::resource::role_binding \
        --verify-module rabbitmq_controller::exec::resource::service \
        --verify-module rabbitmq_controller::exec::resource::service_account \
        --verify-module rabbitmq_controller::exec::resource::stateful_set \
        --verify-module rabbitmq_controller::exec::types \
        --verify-module rabbitmq_controller::proof \
        --verify-module rabbitmq_controller::proof::helper_invariants \
        --verify-module rabbitmq_controller::proof::helper_invariants::owner_ref \
        --verify-module rabbitmq_controller::proof::helper_invariants::predicate \
        --verify-module rabbitmq_controller::proof::helper_invariants::proof \
        --verify-module rabbitmq_controller::proof::helper_invariants::unchangeable \
        --verify-module rabbitmq_controller::proof::helper_invariants::validation \
        --verify-module rabbitmq_controller::proof::liveness \
        --verify-module rabbitmq_controller::proof::liveness::proof \
        --verify-module rabbitmq_controller::proof::liveness::resource_match \
        --verify-module rabbitmq_controller::proof::liveness::spec \
        --verify-module rabbitmq_controller::proof::liveness::stateful_set_match \
        --verify-module rabbitmq_controller::proof::liveness::terminate \
        --verify-module rabbitmq_controller::proof::liveness_theorem \
        --verify-module rabbitmq_controller::proof::predicate \
        --verify-module rabbitmq_controller::proof::resource \
        --verify-module rabbitmq_controller::proof::safety \
        --verify-module rabbitmq_controller::proof::safety::proof \
        --verify-module rabbitmq_controller::proof::safety_theorem \
        --verify-module rabbitmq_controller::spec \
        --verify-module rabbitmq_controller::spec::reconciler \
        --verify-module rabbitmq_controller::spec::resource \
        --verify-module rabbitmq_controller::spec::resource::common \
        --verify-module rabbitmq_controller::spec::resource::config_map \
        --verify-module rabbitmq_controller::spec::resource::default_user_secret \
        --verify-module rabbitmq_controller::spec::resource::erlang_cookie \
        --verify-module rabbitmq_controller::spec::resource::headless_service \
        --verify-module rabbitmq_controller::spec::resource::rabbitmq_plugins \
        --verify-module rabbitmq_controller::spec::resource::role \
        --verify-module rabbitmq_controller::spec::resource::role_binding \
        --verify-module rabbitmq_controller::spec::resource::service \
        --verify-module rabbitmq_controller::spec::resource::service_account \
        --verify-module rabbitmq_controller::spec::resource::stateful_set \
        --verify-module rabbitmq_controller::spec::types \
        > rabbitmq.json
elif [ "$app" = "zookeeper" ]; then
    ./build.sh zookeeper_controller.rs --emit=dep-info --time --time-expanded --output-json --rlimit 50 --num-threads 1 \
        --verify-module zookeeper_controller \
        --verify-module zookeeper_controller::common \
        --verify-module zookeeper_controller::exec \
        --verify-module zookeeper_controller::exec::reconciler \
        --verify-module zookeeper_controller::exec::resource \
        --verify-module zookeeper_controller::exec::resource::admin_server_service \
        --verify-module zookeeper_controller::exec::resource::client_service \
        --verify-module zookeeper_controller::exec::resource::common \
        --verify-module zookeeper_controller::exec::resource::config_map \
        --verify-module zookeeper_controller::exec::resource::headless_service \
        --verify-module zookeeper_controller::exec::resource::stateful_set \
        --verify-module zookeeper_controller::exec::types \
        --verify-module zookeeper_controller::exec::zookeeper_api \
        --verify-module zookeeper_controller::proof \
        --verify-module zookeeper_controller::proof::helper_invariants \
        --verify-module zookeeper_controller::proof::helper_invariants::owner_ref \
        --verify-module zookeeper_controller::proof::helper_invariants::predicate \
        --verify-module zookeeper_controller::proof::helper_invariants::proof \
        --verify-module zookeeper_controller::proof::helper_invariants::unchangeable \
        --verify-module zookeeper_controller::proof::helper_invariants::validation \
        --verify-module zookeeper_controller::proof::helper_invariants::zookeeper_api \
        --verify-module zookeeper_controller::proof::liveness \
        --verify-module zookeeper_controller::proof::liveness::proof \
        --verify-module zookeeper_controller::proof::liveness::resource_match \
        --verify-module zookeeper_controller::proof::liveness::spec \
        --verify-module zookeeper_controller::proof::liveness::stateful_set_match \
        --verify-module zookeeper_controller::proof::liveness::terminate \
        --verify-module zookeeper_controller::proof::liveness::zookeeper_api \
        --verify-module zookeeper_controller::proof::liveness_theorem \
        --verify-module zookeeper_controller::proof::predicate \
        --verify-module zookeeper_controller::proof::resource \
        --verify-module zookeeper_controller::spec \
        --verify-module zookeeper_controller::spec::reconciler \
        --verify-module zookeeper_controller::spec::resource \
        --verify-module zookeeper_controller::spec::resource::admin_server_service \
        --verify-module zookeeper_controller::spec::resource::client_service \
        --verify-module zookeeper_controller::spec::resource::common \
        --verify-module zookeeper_controller::spec::resource::config_map \
        --verify-module zookeeper_controller::spec::resource::headless_service \
        --verify-module zookeeper_controller::spec::resource::stateful_set \
        --verify-module zookeeper_controller::spec::types \
        --verify-module zookeeper_controller::spec::zookeeper_api \
        > zookeeper.json
else
    echo -e "${RED}Wrong controller name: please use fluent, rabbitmq or zookeeper."
fi

