# Artifact Evaluation Instructions for "Compositional Verification of Cluster Control Planes"

This document is for SOSP'2026 artifact evaluation

## Artifact goal

The paper claims that Welder enables compositional verification of Kubernetes controllers, and the verified controllers achieve competitive performance compared to unverified references. The key results to reproduce are:

1. **Verification results (Table 1).** Welder's framework, four controllers (VReplicaSet, VDeployment, VStatefulSet, VRabbitMQ), and their composition proof are fully verified by Verus (0 errors), with the code size table.
2. **Performance results (Table 2).** The verified controllers' `reconcile` and end-to-end reconciliation times are comparable to the unverified reference controllers (end-to-end differences within one standard deviation).

We require a Linux X86-64 machine to reproduce the result. You are welcome to use Cloudlab machine for reproduction.

## Kick-the-tires instructions (~1 compute-hour + ~6 human-minutes)

### Use CloudLab machine (recommended)

The paper's experiments were run on CloudLab Clemson c6420 machines (dual Xeon Gold 6142, 384 GB DRAM, Ubuntu 22.04 LTS). We highly suggest you use the CloudLab machines with the profiles we prepared, as all the environment setup work will be a matter of running one script. If you are a first timer of CloudLab, you can read the CloudLab doc for an overview of how [artifact evaluation is generally conducted on CloudLab](https://docs.cloudlab.us/repeatable-research.html#%28part._aec-members%29). If you do not already have a CloudLab account, please apply for one following this [link](https://www.cloudlab.us/signup.php), and ask the SOSP AEC chairs to add you to the SOSP AEC project.

To make the evaluation process smooth, we have prepared CloudLab profiles for setting up the environment for three hardware types: Clemson c6420, Wisconsin c220g5, and Wisconsin c220g2. Please note that these machines may not be available all the time. You can [submit a resource reservation](https://docs.cloudlab.us/reservations.html) to guarantee the availability of the machine.

**Please let us know if you have trouble accessing CloudLab. We can help set up the experiment and give you access.**

Click **one** of the following three links: [profile `welder-ae-c6420`](https://www.cloudlab.us/p/Sieve-Acto/welder-ae-cloudlab?refspec=refs/heads/c220g2), [profile `welder-ae-c220g5`](https://www.cloudlab.us/p/Sieve-Acto/welder-ae-cloudlab?refspec=refs/heads/c220g2), or [profile `welder-ae-c220g2`](https://www.cloudlab.us/p/Sieve-Acto/welder-ae-cloudlab?refspec=refs/heads/c220g2), and keep hitting `next` to create the experiment. You should see that CloudLab starts to provision the machine, which typically takes ~5 minutes. Please patiently wait for "Status" to become `Ready`. After the machine is ready, log into the machine using `ssh` (with the key provided to CloudLab) or using the `shell` provided by the CloudLab Web UI, and then run

```bash
bash /local/repository/scripts/cloudlab_startup_run_by_creator.sh
```

This command will take ~5 minutes to finish, and it will set up the environment for you, installing Acto at `~/workdir/acto` and Welder (anvil) at `~/anvil`.

Please note that by default, you **only have access to the machine for 16 hours**. Although it is definitely enough to finish the kick-the-tires instructions, we suggest you extend your access (just click the green `Extend` button) to ensure you can finish the full evaluation with the same machine smoothly.

<details><summary>No available machine?</summary>

You can try to reserve one machine of Clemson c6420, Wisconsin c220g5 or Wisconsin c220g2. If you still cannot get a machine, please contact us on HotCRP.
</details>

<details><summary>The script fails in the middle?</summary>

Sometimes the script might fail due to transient network issues. The script is supposed to be idempotent and you can just rerun it. If it persistently fails, please contact us on HotCRP.
</details>

### Or, use your own machine

You need a Linux system with [Docker](https://docs.docker.com/engine/install/), [Go](https://go.dev/doc/install), [kubectl](https://kubernetes.io/docs/tasks/tools/install-kubectl-linux/), [Python](https://www.python.org/downloads/) and [uv](https://docs.astral.sh/uv/#installation) installed (any well-provisioned machine works, but absolute performance numbers depend on the platform). Clone both repositories and run the setup script:

```bash
# Download source code
git clone --recursive --branch v-dev https://github.com/xlab-uiuc/acto.git
git clone --branch sosp26 https://github.com/anvil-verifier/anvil.git

# Set up Rust, Verus, and the LOC tooling (idempotent, no sudo)
./anvil/tools/setup-welder-env.sh
export PATH="$PATH:$HOME/verus"

# Install Python libraries
cd acto
uv venv --clear --python 3.12 venv-welder
uv pip install -p venv-welder/bin/python -r requirements-dev.txt
cd ~
```

### Reproducing full verification results (~10 compute-minutes + ~1 human-minutes)

```bash
cd ~/anvil
. "$HOME/.cargo/env"
export PATH="$PATH:$HOME/verus"
cargo verus verify --lib
```

This verifies the Anvil/Welder framework, all four controllers, and the composition proofs. You are expected to see

```bash
verification results:: 1858 verified, 0 errors
    Checking verus_temporal_logic v0.1.0 (https://github.com/anvil-verifier/verus-tla?rev=91dcde63d45c4980e9d4555b7e9f6861cfb95705#91dcde63)
verification results:: 139 verified, 0 errors
    Checking verifiable-controllers v0.1.0 (/users/cat/anvil)
verification results:: 911 verified, 0 errors
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 8m 03s
```

### Collecting the lines-of-code statistics (~1 compute-minute + ~1 human-minute)

```bash
VERUS_DIR=~/verus-source ./tools/gen-loc-table.sh
```

The **expected output** looks like:

```
|                         |   Trusted Spec |   Trusted Unverified |   Exec | Conformance Proof   | Model   |   Core | ESR   |
|-------------------------|----------------|----------------------|--------|---------------------|---------|--------|-------|
| VReplicaSet controller  |            205 |                  257 |    300 | 119                 | 418     |   7726 | 7305  |
| VDeployment controller  |            254 |                  387 |    365 | 190                 | 563     |  10327 | 10201 |
| VStatefulSet controller |            194 |                  380 |    896 | 366                 | 1274    |  12085 | 11937 |
| RabbitMQ controller     |            247 |                  298 |   1619 | 175                 | 1660    |   6920 | 6772  |
| Composition proofs      |            181 |                    0 |      0 | --                  | 0       |    429 | --    |
| Total(all)              |           1081 |                 1322 |   3180 | 850                 | --      |  41402 | --    |
```

**Minor differences are expected** because the controllers' proofs have been optimized and updated to follow updates from upstream.

### Running workloads of one controller (~70 compute-minutes + ~2 human-minutes)

To quickly check that the environment works end-to-end, run a 5% sample of the performance workloads for the VDeployment controller and its unverified reference. We suggest you use `tmux` when running on remote machines as the command can take a while.

```bash
cd ~/workdir/acto
source venv-welder/bin/activate # only on your own machine
bash welder-ae-one-controller.sh 0.05
cat welder-table-2.txt
```

If you set up your own machine, replace `~/workdir/acto` with the path to the cloned acto repo on your machine instead. You should see a table like this:

```
| Controller   |   reconcile Verified |   reconcile Ref. | reconcile Diff   |   End-to-end Verified |   End-to-end Ref. | End-to-end Diff   |
|--------------|----------------------|------------------|------------------|-----------------------|-------------------|-------------------|
| ReplicaSet   |                 0.66 |             0.07 | 0.59±0.04        |                  5.82 |              5.53 | 0.29±0.13         |
| Deployment   |                 0.1  |             0.06 | 0.03±0.01        |                  5.82 |              5.53 | 0.29±0.13         |
```

**Expected result:** The absolute numbers depend on the platform, but you should observe that end-to-end differences are negligible.

---
## Full Evaluation Instructions (~2 compute-hours + ~2 human-minutes)

You will reproduce the performance results in Table 2. These are the key results that support the claim in the paper. The absolute number of time-related results heavily depends on the platform, but we will highlight the key pattern you should be able to observe. You will reuse the environments from kick-the-tire instructions.
The entire testing process takes about 2 machine-hours with the default 5% sample.

We suggest you use `tmux` when running on remote machines, as the command can take hours. In the `acto` checkout, run:

```bash
bash welder-ae-sampled.sh 0.05
cat welder-table-2.txt
```

This runs 5% of the workloads for both campaigns (VDeployment + VReplicaSet vs. the native Deployment/ReplicaSet controllers, and VRabbitMQ + VStatefulSet vs. the official RabbitMQ operator) and processes the results into `welder-table-2.txt`. You should see a table like this (times in seconds):

```
| Controller   |   reconcile Verified |   reconcile Ref. | reconcile Diff   |   End-to-end Verified |   End-to-end Ref. | End-to-end Diff   |
|--------------|----------------------|------------------|------------------|-----------------------|-------------------|-------------------|
| ReplicaSet   |                 0.73 |             0.1  | 0.63±0.11        |                  5.59 |              5.61 | -0.02±0.13        |
| Deployment   |                 0.11 |             0.06 | 0.05±0.00        |                  5.59 |              5.61 | -0.02±0.13        |
| StatefulSet  |                 0.45 |             0.28 | 0.17±0.08        |                103.6  |            101.54 | 2.06±4.72         |
| RabbitMQ     |                 0.47 |             0.73 | -0.26±0.10       |                103.6  |            101.54 | 2.06±4.72         |
```

**Expected result:** The absolute numbers depend on the platform, but you should observe that the end-to-end differences are negligible.

<details><summary>I want to run all the workloads?</summary>

Note that running all the workloads takes about 22 machine-hours. If you really want to do that, run
```bash
bash welder-ae-sampled.sh 1
```
</details>
