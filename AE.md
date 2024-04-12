# Artifact Evaluation Instructions for "Anvil: Verifying Liveness of Cluster Management Controllers"

This document is for OSDI'2024 artifact evaluation.

## Artifact goal
In the paper, we make the claim that
>  We use Anvil to verify three Kubernetes controllers for managing ZooKeeper, RabbitMQ, and FluentBit, which can readily be deployed in Kubernetes platforms and are comparable in terms of features and performance to widely used unverified controllers.

The goal is to reproduce the key results to support the claim. Specifically, the key results are (1) verification results in Figure 1 in Section 7 and (2) performance results in Figure 3 in Section 7.

The entire artifact evaluation process can take about X hours.

1. [Kick-the-tires Instructions](#kick-the-tires-instructions-5-minutes)
2. [Full Evaluation Instructions](#full-evaluation-instructions-X-hours)

## Kick-the-tires Instructions (~5 minutes)

Following kick-the-tires instructions, you will download a container image prepared by us with all the dependencies installed, and reproduce the verification result for one controller we built.

Before following the instructions, please ensure you have [Docker](https://docs.docker.com/engine/install/) installed on your machine.

**Step 1: download the container image (about 3.56GB)**
```bash
docker pull docker pull ghcr.io/vmware-research/verifiable-controllers/anvil-ae:latest
```
Note: If you cannot download the image, try to [authenticate to the container registry](https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry#authenticating-to-the-container-registry) and pull again.

</details>

**Step 2: run the container**
```bash
docker run -it ghcr.io/vmware-research/verifiable-controllers/anvil-ae:latest bash
```
Now you should be in the path `/anvil` inside the container.

**Step 3: verify the ZooKeeper controller in the container**
```bash
VERUS_DIR=/verus ./verify-controller-only.sh zookeeper
```
It takes about 4 minutes to finish on a MacBook Pro 2019.

**Step 4: check the verification result**
```bash
cat zookeeper.json | grep "errors"
```
The result should be `"errors": 0,`, meaning that all the proofs are verified. If you do not see the expected output, please let us know.

## Full Evaluation Instructions (~X hours)

### Reproducing Verification Results in Table 1

Following the instructions, you will reproduce the key results that (1) the Anvil framework and the three controllers are verified, and (2) the code size the time to verify are consistent with Table 1 in the paper.

You will reuse the container from [Kick-the-tires Instructions](#kick-the-tires-instructions-5-minutes). Run the container with bash as you did before. Then in the path `/anvil` inside the container, run
```bash
VERUS_DIR=/verus ./reproduce-verification-result.sh
```
This commands run Verus to verify the Anvil framework and the three controllers, and collect statistics including code sizes and time to verify. It takes about 12 minutes to finish on a MacBook Pro 2019. After it's done, you should see
```
Presenting verification results from Verus. You are expected to see 0 errors for Anvil and the three controllers, which means everything is verified.
+ cat anvil.json
+ grep errors
    "errors": 0,
+ cat fluent.json
+ grep errors
    "errors": 0,
+ grep errors
+ cat rabbitmq.json
    "errors": 0,
+ cat zookeeper.json
+ grep errors
    "errors": 0,
```
All the `"errors": 0,` mean that the Anvil framework and the three controllers are verified.

To see the generated Table 1, run
```bash
cat tools/t1.txt
```
and you should see
```
|                           | Trusted (LoC)   | Exec (LoC)   | Proof (LoC)   | Time to Verify (seconds)   |
|---------------------------|-----------------|--------------|---------------|----------------------------|
| ZooKeeper controller      |                 |              |               |                            |
| |---Liveness              | 94              | --           | 7245          | 463.172                    |
| |---Conformance           | 5               | --           | 172           | 10.579                     |
| |---Controller model      | --              | --           | 935           | --                         |
| |---Controller impl       | --              | 1134         | --            | --                         |
| |---Trusted wrapper       | 515             | --           | --            | --                         |
| |---Trusted ZooKeeper API | 318             | --           | --            | --                         |
| |---Trusted entry point   | 19              | --           | --            | --                         |
| |---Total                 | 951             | 1134         | 8352          | 473.751 (108.276)          |
| RabbitMQ controller       |                 |              |               |                            |
| |---Liveness              | 144             | --           | 5211          | 312.898                    |
| |---Safety                | 22              | --           | 358           | 34.936                     |
| |---Conformance           | 5               | --           | 290           | 27.051                     |
| |---Controller model      | --              | --           | 1369          | --                         |
| |---Controller impl       | --              | 1598         | --            | --                         |
| |---Trusted wrapper       | 359             | --           | --            | --                         |
| |---Trusted entry point   | 19              | --           | --            | --                         |
| |---Total                 | 549             | 1598         | 7228          | 374.885 (129.054)          |
| Fluent controller         |                 |              |               |                            |
| |---Liveness              | 115             | --           | 7079          | 397.297                    |
| |---Conformance           | 10              | --           | 201           | 14.496                     |
| |---Controller model      | --              | --           | 1115          | --                         |
| |---Controller impl       | --              | 1208         | --            | --                         |
| |---Trusted wrapper       | 681             | --           | --            | --                         |
| |---Trusted entry point   | 24              | --           | --            | --                         |
| |---Total                 | 830             | 1208         | 8395          | 411.793 (103.509)          |
| Total(all)                | 2330            | 3940         | 23975         | 1260.429 (340.839)         |
```

### Reproducing Performance Results in Table 3

Following the instructions, you will reproduce the key results that the verified controllers achieve comparable performance to the unverified reference controllers as shown in Table 3.


