#!/usr/bin/env bash

## Verify the controller alone without verifying the Anvil framework.

set -xeu

YELLOW='\033[1;33m'
GREEN='\033[1;32m'
RED='\033[0;31m'
NC='\033[0m'

app=$1

if [ "$app" = "fluent" ]; then
    ./build.sh fluent_controller.rs --emit=dep-info --time --time-expanded --output-json --rlimit 50 \
        --verify-module fluent_controller \
        --verify-module fluent_controller::fluentbit \
        --verify-module fluent_controller::fluentbit::exec \
        --verify-module fluent_controller::fluentbit::exec::reconciler \
        --verify-module fluent_controller::fluentbit::exec::resource \
        --verify-module fluent_controller::fluentbit::exec::resource::common \
        --verify-module fluent_controller::fluentbit::exec::resource::daemon_set \
        --verify-module fluent_controller::fluentbit::exec::resource::role \
        --verify-module fluent_controller::fluentbit::exec::resource::role_binding \
        --verify-module fluent_controller::fluentbit::exec::resource::service \
        --verify-module fluent_controller::fluentbit::exec::resource::service_account \
        --verify-module fluent_controller::fluentbit::model \
        --verify-module fluent_controller::fluentbit::model::reconciler \
        --verify-module fluent_controller::fluentbit::model::resource \
        --verify-module fluent_controller::fluentbit::model::resource::common \
        --verify-module fluent_controller::fluentbit::model::resource::daemon_set \
        --verify-module fluent_controller::fluentbit::model::resource::role \
        --verify-module fluent_controller::fluentbit::model::resource::role_binding \
        --verify-module fluent_controller::fluentbit::model::resource::service \
        --verify-module fluent_controller::fluentbit::model::resource::service_account \
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
        --verify-module fluent_controller::fluentbit::proof::predicate \
        --verify-module fluent_controller::fluentbit::proof::resource \
        --verify-module fluent_controller::fluentbit::trusted \
        --verify-module fluent_controller::fluentbit::trusted::exec_types \
        --verify-module fluent_controller::fluentbit::trusted::liveness_theorem \
        --verify-module fluent_controller::fluentbit::trusted::maker \
        --verify-module fluent_controller::fluentbit::trusted::spec_types \
        --verify-module fluent_controller::fluentbit::trusted::step \
        --verify-module fluent_controller::fluentbit_config \
        --verify-module fluent_controller::fluentbit_config::exec \
        --verify-module fluent_controller::fluentbit_config::exec::reconciler \
        --verify-module fluent_controller::fluentbit_config::exec::resource \
        --verify-module fluent_controller::fluentbit_config::exec::resource::common \
        --verify-module fluent_controller::fluentbit_config::exec::resource::secret \
        --verify-module fluent_controller::fluentbit_config::model \
        --verify-module fluent_controller::fluentbit_config::model::reconciler \
        --verify-module fluent_controller::fluentbit_config::model::resource \
        --verify-module fluent_controller::fluentbit_config::model::resource::common \
        --verify-module fluent_controller::fluentbit_config::model::resource::secret \
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
        --verify-module fluent_controller::fluentbit_config::proof::predicate \
        --verify-module fluent_controller::fluentbit_config::proof::resource \
        --verify-module fluent_controller::fluentbit_config::trusted \
        --verify-module fluent_controller::fluentbit_config::trusted::exec_types \
        --verify-module fluent_controller::fluentbit_config::trusted::liveness_theorem \
        --verify-module fluent_controller::fluentbit_config::trusted::maker \
        --verify-module fluent_controller::fluentbit_config::trusted::spec_types \
        --verify-module fluent_controller::fluentbit_config::trusted::step \
        > fluent.json
elif [ "$app" = "rabbitmq" ]; then
    ./build.sh rabbitmq_controller.rs --emit=dep-info --time --time-expanded --output-json --rlimit 50 \
        --verify-module rabbitmq_controller \
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
        --verify-module rabbitmq_controller::model \
        --verify-module rabbitmq_controller::model::reconciler \
        --verify-module rabbitmq_controller::model::resource \
        --verify-module rabbitmq_controller::model::resource::common \
        --verify-module rabbitmq_controller::model::resource::config_map \
        --verify-module rabbitmq_controller::model::resource::default_user_secret \
        --verify-module rabbitmq_controller::model::resource::erlang_cookie \
        --verify-module rabbitmq_controller::model::resource::headless_service \
        --verify-module rabbitmq_controller::model::resource::rabbitmq_plugins \
        --verify-module rabbitmq_controller::model::resource::role \
        --verify-module rabbitmq_controller::model::resource::role_binding \
        --verify-module rabbitmq_controller::model::resource::service \
        --verify-module rabbitmq_controller::model::resource::service_account \
        --verify-module rabbitmq_controller::model::resource::stateful_set \
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
        --verify-module rabbitmq_controller::proof::predicate \
        --verify-module rabbitmq_controller::proof::resource \
        --verify-module rabbitmq_controller::proof::safety \
        --verify-module rabbitmq_controller::proof::safety::proof \
        --verify-module rabbitmq_controller::trusted \
        --verify-module rabbitmq_controller::trusted::exec_types \
        --verify-module rabbitmq_controller::trusted::liveness_theorem \
        --verify-module rabbitmq_controller::trusted::maker \
        --verify-module rabbitmq_controller::trusted::safety_theorem \
        --verify-module rabbitmq_controller::trusted::spec_types \
        --verify-module rabbitmq_controller::trusted::step \
        > rabbitmq.json
elif [ "$app" = "zookeeper" ]; then
    ./build.sh zookeeper_controller.rs --emit=dep-info --time --time-expanded --output-json --rlimit 50 \
        --verify-module zookeeper_controller \
        --verify-module zookeeper_controller::exec \
        --verify-module zookeeper_controller::exec::reconciler \
        --verify-module zookeeper_controller::exec::resource \
        --verify-module zookeeper_controller::exec::resource::admin_server_service \
        --verify-module zookeeper_controller::exec::resource::client_service \
        --verify-module zookeeper_controller::exec::resource::common \
        --verify-module zookeeper_controller::exec::resource::config_map \
        --verify-module zookeeper_controller::exec::resource::headless_service \
        --verify-module zookeeper_controller::exec::resource::stateful_set \
        --verify-module zookeeper_controller::model \
        --verify-module zookeeper_controller::model::reconciler \
        --verify-module zookeeper_controller::model::resource \
        --verify-module zookeeper_controller::model::resource::admin_server_service \
        --verify-module zookeeper_controller::model::resource::client_service \
        --verify-module zookeeper_controller::model::resource::common \
        --verify-module zookeeper_controller::model::resource::config_map \
        --verify-module zookeeper_controller::model::resource::headless_service \
        --verify-module zookeeper_controller::model::resource::stateful_set \
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
        --verify-module zookeeper_controller::proof::predicate \
        --verify-module zookeeper_controller::proof::resource \
        --verify-module zookeeper_controller::trusted \
        --verify-module zookeeper_controller::trusted::config_map \
        --verify-module zookeeper_controller::trusted::exec_types \
        --verify-module zookeeper_controller::trusted::liveness_theorem \
        --verify-module zookeeper_controller::trusted::maker \
        --verify-module zookeeper_controller::trusted::spec_types \
        --verify-module zookeeper_controller::trusted::step \
        --verify-module zookeeper_controller::trusted::zookeeper_api_exec \
        --verify-module zookeeper_controller::trusted::zookeeper_api_spec \
        > zookeeper.json
else
    echo -e "${RED}Wrong controller name: please use fluent, rabbitmq or zookeeper."
fi

