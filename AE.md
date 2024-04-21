# Artifact Evaluation Instructions for "Anvil: Verifying Liveness of Cluster Management Controllers"

This document is for OSDI'2024 artifact evaluation.

## Artifact goal
In the paper, we make the claim that
>  We use Anvil to verify three Kubernetes controllers for managing ZooKeeper, RabbitMQ, and FluentBit, which can readily be deployed in Kubernetes platforms and are comparable in terms of features and performance to widely used unverified controllers.

The goal is to reproduce the key results to support the claim. Specifically, the key results are (1) verification results in Figure 1 in Section 7 and (2) performance results in Figure 3 in Section 7.

The entire artifact evaluation process can take about X hours.

1. [Kick-the-tires Instructions](#kick-the-tires-instructions-3-compute-hours--6-human-minutes)
2. [Full Evaluation Instructions](#full-evaluation-instructions-10-compute-hours--6-human-minutes)

## Kick-the-tires Instructions (~3 compute-hours + ~6 human-minutes)

Following kick-the-tires instructions, you will (1) verify one controller using the container image we prepared, and (2) run a small subset of the workloads used for evaluating the controller's performance.

### Verifying one controller (~4 compute-minutes + ~1 human-minute)

Before following the instructions, please ensure you have [Docker](https://docs.docker.com/engine/install/) installed on your machine.

**Step 1: download the container image (~3.56GB)**
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

### Running workloads of one controller (~3 compute-hours + ~5 human-minutes)

The following instructions require some environment setup to run (part of) the performance evaluation. We highly suggest you use the CloudLab machine with the image we prepared, as all the environment setup work will be a matter of running one script. If you are a first timer of CloudLab, we encourage you to read the CloudLab doc for an overview of how [artifact evaluation is generally conducted on CloudLab]((https://docs.cloudlab.us/repeatable-research.html#%28part._aec-members%29)). If you do not already have a CloudLab account, please apply for one following this [link](https://www.cloudlab.us/signup.php), and ask the OSDI AEC chair to add you to the OSDI AEC project.

To make the evaluation process smooth, we have prepared CloudLab profiles for setting up the environment for three hardware types: c6420, c220g5 and c220g2. Please note these machines may not be available all the time. You can [submit a resource reservation](https://docs.cloudlab.us/reservations.html) to guarantee the availability of the machine.

**Please let us know if you have trouble accessing CloudLab, we can help set up the experiment and give you access.**

**Step 1: setup environment**

Click the [link](https://www.cloudlab.us/instantiate.php?project=anvil&profile=anvil-ae-c6420&refspec=refs/heads/main) (which instantiates a CloudLab machine with the profile `anvil-ae-c6420`) and keep hitting `next` to create the experiment. You should see that CloudLab starts to provision the machine, which typically takes ~5 minutes. Please patiently wait for "Status" to become `Ready`. After the machine is ready, log into the machine using `ssh` (with the key provided to CloudLab) or using the `shell` provided by the CloudLab Web UI, and then run
```bash
bash /local/repository/scripts/cloudlab_startup_run_by_creator.sh
```
This command will take ~5 minutes to finish and it will set up the environment for you and install Acto at the `workdir/acto` directory under your `$HOME` directory.

Please note that by default you **only have access to the machine for 16 hours**. Although it is definitely enough to finish the kick-the-tires instructions, we suggest you extend your access (just click the green `Extend` button) to ensure you can finish the full evaluation with the same machine smoothly.

<details><summary>No available machine?</summary>

You can also try [profile `anvil-ae-c220g5`](https://www.cloudlab.us/instantiate.php?project=anvil&profile=anvil-ae-c220g5&refspec=refs/heads/main) or [profile `anvil-ae-c220g2`](https://www.cloudlab.us/instantiate.php?project=anvil&profile=anvil-ae-c220g2&refspec=refs/heads/main). If you still cannot get a machine, please contact us on HotCRP.
</details>

<details><summary>The script fails in the middle?</summary>

Sometimes the script might fail due to transient network issues. The script is supposed to be idempotent and you can just rerun it. If it persistently fails, please contact us on HotCRP.
</details>

<details><summary>Still want to set up local environment instead of using CloudLab?</summary>

* A Linux system with Docker support
* Python 3.10 or newer
* Install `pip3` by running `sudo apt install python3-pip`
* Install [Golang](https://go.dev/doc/install)
* Clone the repo recursively by running `git clone --recursive --branch anvil-dev https://github.com/xlab-uiuc/acto.git`
* Install Python dependencies by running `pip3 install -r requirements-dev.txt` in the project
* Install `Kind` by running `go install sigs.k8s.io/kind@v0.20.0`
* Install `Kubectl` by running `curl -LO https://dl.k8s.io/release/v1.22.9/bin/linux/amd64/kubectl` and `sudo install -o root -g root -m 0755 kubectl /usr/local/bin/kubectl`

Run all the instructions below inside the cloned `acto` repo.

If you encounter any problem, please contact us on HotCRP.
</details>


**Step 2: run the workload**

From now we suggest you use `tmux` as the command will take hours.
```bash
cd ~/workdir/acto/
bash anvil-ae-one-controller.sh
```
It takes approximately 3 hours to finish.

<details><summary>Seeing urllib3.exceptions.SSLError: [SSL: WRONG_VERSION_NUMBER] wrong version number (_ssl.c:2578)?</summary>

This is benign and will not affect the result. You can ignore it.
</details>

**Step 3: check the performance result**
```bash
cat anvil-table-3.txt
```
You should see a table like this:
```
| Controller                         |   Verified (Anvil) Mean |   Verified (Anvil) Max |   Reference (unverified) Mean |   Reference (unverified) Max |
|------------------------------------|-------------------------|------------------------|-------------------------------|------------------------------|
| testrun-anvil-zk-performance       |                 151.655 |                160.793 |                       145.006 |                      160.501 |
```
Note that the absolute numbers depends on the platform, but you should observe that the verified ZooKeeper controller is not significantly slower than the unverified one. In most cases, they have similar execution time.

## Full Evaluation Instructions (~10 compute-hours + ~6 human-minutes)

Following full evaluation instructions, you will reproduce the verification results in Table 1 and the performance results in Table 3. These are the key results that support the claim in the paper. The absolute number of the time-related results heavily depend on the platform, but we will **highlight** the key pattern you should be able to observe from such numbers.

### Reproducing Verification Results in Table 1 (~12 compute-minutes + ~3 human-minutes)

Following the instructions, you will reproduce the key results that (1) the Anvil framework and the three controllers are verified, and (2) the code size the time to verify are consistent with Table 1 in the paper.

You will reuse the container from [Kick-the-tires Instructions](#verifying-one-controller-4-compute-minutes--1-human-minute). Run the container with bash as you did before. Then in the path `/anvil` inside the container, run
```bash
VERUS_DIR=/verus ./reproduce-verification-result.sh
```
This command runs Verus to verify the Anvil framework and the three controllers and collects statistics including code sizes and time to verify. It takes about 12 minutes to finish on a MacBook Pro 2019. After it's done, you should see
```
Presenting verification results from Verus. You should see 0 errors for Anvil and the three controllers, which means everything is verified.
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
and you should see a generated table like this:
```
|                           | Trusted (LoC)   | Exec (LoC)   | Proof (LoC)   | Time to Verify (seconds)   |
|---------------------------|-----------------|--------------|---------------|----------------------------|
| ZooKeeper controller      |                 |              |               |                            |
| |---Liveness              | 94              | --           | 7245          | 297.872                    |
| |---Conformance           | 5               | --           | 172           | 5.891                      |
| |---Controller model      | --              | --           | 935           | --                         |
| |---Controller impl       | --              | 1134         | --            | --                         |
| |---Trusted wrapper       | 515             | --           | --            | --                         |
| |---Trusted ZooKeeper API | 318             | --           | --            | --                         |
| |---Trusted entry point   | 19              | --           | --            | --                         |
| |---Total                 | 951             | 1134         | 8352          | 303.763 (172.959)          |
| RabbitMQ controller       |                 |              |               |                            |
| |---Liveness              | 144             | --           | 5211          | 163.285                    |
| |---Safety                | 22              | --           | 358           | 14.561                     |
| |---Conformance           | 5               | --           | 290           | 10.48                      |
| |---Controller model      | --              | --           | 1369          | --                         |
| |---Controller impl       | --              | 1598         | --            | --                         |
| |---Trusted wrapper       | 359             | --           | --            | --                         |
| |---Trusted entry point   | 19              | --           | --            | --                         |
| |---Total                 | 549             | 1598         | 7228          | 188.326 (209.879)          |
| Fluent controller         |                 |              |               |                            |
| |---Liveness              | 115             | --           | 7079          | 216.977                    |
| |---Conformance           | 10              | --           | 201           | 6.741                      |
| |---Controller model      | --              | --           | 1115          | --                         |
| |---Controller impl       | --              | 1208         | --            | --                         |
| |---Trusted wrapper       | 681             | --           | --            | --                         |
| |---Trusted entry point   | 24              | --           | --            | --                         |
| |---Total                 | 830             | 1208         | 8395          | 223.718 (168.815)          |
| Total(all)                | 2330            | 3940         | 23975         | 715.807 (551.653)          |
```
When comparing this generated table to the original Table 1 in the paper, please note that:
- The numbers in the "Time to verify" column heavily depend on the platform. The numbers we show above are different from those in the paper because the platform configuration and the solver version have changed since the submission. You might find the absolute numbers generated on your platform are different from the numbers shown above, which is expected. **Regardless of the platform, you should still be able to observe that most of the time is expected to be spent on the "Liveness" row.**
- The numbers in the "Trusted", "Exec" and "Proof" should be deterministic. You might notice some minor difference when comparing them to the numbers reported in the paper. This is because we have slightly updated the controllers' implementations and proofs since the submission.

### Reproducing Performance Results in Table 3 (~10 compute-hours + ~3 human-minutes)

Following the instructions, you will reproduce the key results that the verified controllers achieve comparable performance to the unverified reference controllers as shown in Table 3.

You will reuse the CloudLab machine as in the [Kick-the-tires Instructions](#running-workloads-of-one-controller-3-compute-hours--5-human-minutes).

We suggest you use `tmux` as the command will take hours.

In the path `~/workdir/acto/` inside your CloudLab machine, run
```bash
bash anvil-ae-sampled.sh
```
This command runs 10% of the workloads for the three controllers and their unverified references. It takes approximately 10 hours to finish on CloudLab c6420. After it's done, to see the generated Table 3, run
```bash
cat anvil-table-3.txt
```
and you should see a generated table like this:
```
| Controller                         |   Verified (Anvil) Mean |   Verified (Anvil) Max |   Reference (unverified) Mean |   Reference (unverified) Max |
|------------------------------------|-------------------------|------------------------|-------------------------------|------------------------------|
| testrun-anvil-zk-performance       |                 151.655 |                160.793 |                       145.006 |                      160.501 |
| testrun-anvil-rabbitmq-performance |                 217.23  |                360.532 |                       214.493 |                      357.244 |
| testrun-anvil-fluent-performance   |                  37.989 |                 40.339 |                        29.188 |                       35.648 |
```
The absolute numbers heavily depend on the platform and it's totally expected that they are not exactly the same as the Table 3 in the paper. **Regardless of the platform, you should still be able to observe that the verified controllers are not significantly slower than their unverified references.** In fact, in most cases the difference is even negligible.
