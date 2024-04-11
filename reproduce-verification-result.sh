#!/usr/bin/env bash

## Reproduce the verification result of the three controllers,
## also generate the Table 1 in the paper including:
## (1) the time spent on verifying each controller
## (2) the code size breakdown of each controller

set -xeu

YELLOW='\033[1;33m'
GREEN='\033[1;32m'
RED='\033[0;31m'
NC='\033[0m'

prefix="${GREEN}[Artifact Evaluation]"

echo -e "${prefix} Verifying Anvil framework...${NC}"
./build.sh anvil.rs --crate-type=lib --emit=dep-info --time --time-expanded --output-json --rlimit 50 > anvil.json

echo -e "${prefix} Verifying Fluent controller...${NC}"
./verify-controller-only.sh fluent

echo -e "${prefix} Verifying RabbitMQ controller...${NC}"
./verify-controller-only.sh rabbitmq

echo -e "${prefix} Verifying ZooKeeper controller...${NC}"
./verify-controller-only.sh zookeeper

echo -e "${prefix} Calling Verus line counting tool...${NC}"
pushd $VERUS_DIR/source/tools/line_count
cargo run --release -- /Users/xudongsun/workspace/verifiable-controllers/src/anvil.d > anvil_loc_table
cargo run --release -- /Users/xudongsun/workspace/verifiable-controllers/src/fluent_controller.d > fluent_loc_table
cargo run --release -- /Users/xudongsun/workspace/verifiable-controllers/src/rabbitmq_controller.d > rabbitmq_loc_table
cargo run --release -- /Users/xudongsun/workspace/verifiable-controllers/src/zookeeper_controller.d > zookeeper_loc_table
popd

echo -e "${prefix} Generating verification time result...${NC}"
cp anvil.json tools/anvil.json
cp fluent.json tools/fluent.json
cp rabbitmq.json tools/rabbitmq.json
cp zookeeper.json tools/zookeeper.json
pushd tools
python3 gen-t1-t2-time.py
popd

echo -e "${prefix} Generating code size result...${NC}"
pushd tools
python3 gen-t1-t2-lines.py
popd

echo -e "${prefix} Presenting verification result...${NC}"
cat anvil.json | grep "errors"
cat fluent.json | grep "errors"
cat rabbitmq.json | grep "errors"
cat zookeeper.json | grep "errors"
