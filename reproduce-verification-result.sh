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

PREFIX="${GREEN}"

CUR_DIR=$(pwd)

echo -e "${PREFIX}Verifying Anvil framework...${NC}"
./build.sh anvil.rs --crate-type=lib --emit=dep-info --time --time-expanded --output-json --rlimit 50 > anvil.json

echo -e "${PREFIX}Verifying Fluent controller...${NC}"
./verify-controller-only.sh fluent

echo -e "${PREFIX}Verifying RabbitMQ controller...${NC}"
./verify-controller-only.sh rabbitmq

echo -e "${PREFIX}Verifying ZooKeeper controller...${NC}"
./verify-controller-only.sh zookeeper

echo -e "${PREFIX}Calling Verus line counting tool...${NC}"
pushd $VERUS_DIR/source/tools/line_count
cargo run --release -- $CUR_DIR/src/anvil.d > anvil_loc_table
cargo run --release -- $CUR_DIR/src/fluent_controller.d > fluent_loc_table
cargo run --release -- $CUR_DIR/src/rabbitmq_controller.d > rabbitmq_loc_table
cargo run --release -- $CUR_DIR/src/zookeeper_controller.d > zookeeper_loc_table
popd

echo -e "${PREFIX}Generating Table 1 to tools/t1.txt${NC}"
cp anvil.json tools/anvil.json
cp fluent.json tools/fluent.json
cp rabbitmq.json tools/rabbitmq.json
cp zookeeper.json tools/zookeeper.json
pushd tools
python3 gen-t1.py > t1.txt
popd

echo -e "${PREFIX}Presenting verification results from Verus. You should see 0 errors for Anvil and the three controllers, which means everything is verified.${NC}"
cat anvil.json | grep "errors"
cat fluent.json | grep "errors"
cat rabbitmq.json | grep "errors"
cat zookeeper.json | grep "errors"

# echo -e "${PREFIX}To check the verification time and code size results, just run cat tools/t1-time.txt and cat tools/t1-loc.txt.${NC}"
