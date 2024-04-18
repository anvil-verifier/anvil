# Artifact Evaluation Instructions for "Anvil: Verifying Liveness of Cluster Management Controllers"

This document is for OSDI'2024 artifact evaluation.

## Artifact goal
In the paper, we make the claim that
>  We use Anvil to verify three Kubernetes controllers for managing ZooKeeper, RabbitMQ, and FluentBit, which can readily be deployed in Kubernetes platforms and are comparable in terms of features and performance to widely used unverified controllers.

The goal is to reproduce the key results to support the claim. Specifically, the key results are (1) verification results in Figure 1 in Section 7 and (2) performance results in Figure 3 in Section 7.

The entire artifact evaluation process can take about X hours.

1. [Kick-the-tires Instructions](#kick-the-tires-instructions-5-minutes)
2. [Full Evaluation Instructions](#full-evaluation-instructions-X-hours)

## Kick-the-tires Instructions (~X compute-minutes + ~Y human-minute)

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

### Running workloads of one controller (~X compute-minutes + ~Y human-minute)

**Step 1: setup environment**

If you are a first timer of CloudLab, we encourage you to read the CloudLab doc for an overview of how Artifact Evaluation is generally conducted on CloudLab.

[CloudLab For Artifact Evaluation](https://docs.cloudlab.us/repeatable-research.html#%28part._aec-members%29)

If you do not already have a CloudLab account, please apply for one following this [link](https://www.cloudlab.us/signup.php),
  and ask the SOSP AEC chair to add you to the SOSP AEC project. Please let us know if you have trouble accessing cloudlab, we can help set up the experiment and give you access.

We recommend you to use the machine type, [c6420](https://www.cloudlab.us/instantiate.php?project=Sieve-Acto&profile=acto-cloudlab&refspec=refs/heads/main) (CloudLab profile), which was used by the evaluation. Note that the machine may not be available all the time. You would need to submit a resource reservation to guarantee the availability of the resource.

We provide CloudLab profile to automatically select the c6420 as the machine type and set up
  all the environment.

To use the profile, follow the [link](https://www.cloudlab.us/instantiate.php?project=Sieve-Acto&profile=acto-cloudlab&refspec=refs/heads/main)
and keep hitting `next` to create the experiment.
You should see that CloudLab starts to provision the machine and our profile will run a StartUp
  script to set the environment up.

The start up would take around 15 minutes.
Please patiently wait for "Status" to become `Ready` and "Startup" to become `Finished`.
After that, Acto is installed at the `workdir/acto` directory under your `$HOME` directory.

Access the machine using `ssh` or through the `shell` provided by the CloudLab Web UI.

<details><summary>Seeing `Exited (2)` in the "Startup" column?</summary>

There could sometimes be transient network issues within the CloudLab cluster, which prevent e.g. `pip install` in the startup scripts from functioning as expected.

To circumvent the problem, either

1. Recreate the experiment using the same profile, or
2. SSH into the machine and manually rerun the startup:

    ```sh
    sudo su - geniuser
    bash /local/repository/scripts/cloudlab_startup_run_by_geniuser.sh
    exit
    ```

</details>

<details><summary>Setting up local environment (skip this if using the CloudLab profile)</summary>
 
* A Linux system with Docker support
* Python 3.10 or newer
* Install `pip3` by running `sudo apt install python3-pip`
* Install [Golang](https://go.dev/doc/install)
* Clone the repo recursively by running `git clone --recursive --branch anvil-dev https://github.com/xlab-uiuc/acto.git`
* Install Python dependencies by running `pip3 install -r requirements-dev.txt` in the project
* Install `Kind` by running `go install sigs.k8s.io/kind@v0.20.0`
* Install `Kubectl` by running `curl -LO https://dl.k8s.io/release/v1.22.9/bin/linux/amd64/kubectl` and `sudo install -o root -g root -m 0755 kubectl /usr/local/bin/kubectl`

</details>

**Step 2: run workload**

First witch into the `acto` repository cloned from the Step 1, and run the following command to start running the workload.
```bash
bash anvil-ae-one-controller.sh
```
It runs 10% of the workloads for the ZooKeeper controller, and prints the table to the file `anvil-table-3.txt`.
It takes approximately 3 hours to finish.

**Step 3: check the performance result**
```bash
cat anvil-table-3.txt
```

and you should see a generated table like this:
| Controller                         |   Verified (Anvil) Mean |   Verified (Anvil) Max |   Reference (unverified) Mean |   Reference (unverified) Max |
|------------------------------------|-------------------------|------------------------|-------------------------------|------------------------------|
| testrun-anvil-zk-performance       |                 151.655 |                160.793 |                       145.006 |                      160.501 |

#### 

## Full Evaluation Instructions (~X compute-hours + ~Y human-minutes)

Following full evaluation instructions, you will reproduce the verification results in Table 1 and the performance results in Table 3. These are the key results that support the claim in the paper. The absolute number of the time-related results heavily depend on the platform, but we will **highlight** the key pattern you should be able to observe from such numbers.

### Reproducing Verification Results in Table 1 (~12 compute-minutes + ~3 human-minutes)

Following the instructions, you will reproduce the key results that (1) the Anvil framework and the three controllers are verified, and (2) the code size the time to verify are consistent with Table 1 in the paper.

You will reuse the container from [Kick-the-tires Instructions](#kick-the-tires-instructions-5-minutes). Run the container with bash as you did before. Then in the path `/anvil` inside the container, run
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
- The numbers in the "Time to verify" column heavily depend on the platform. The numbers we show above are different from those in the paper because the platform configuration and the solver version have changed since the submission. You might find the absolute numbers generated on your platform are different from the numbers shown above, which is expected. **Regardless of the platform, you should still be able to observe that most of the time is expected to be spent on the "Liveness" row**.
- The numbers in the "Trusted", "Exec" and "Proof" should be deterministic. You might notice some minor difference when comparing them to the numbers reported in the paper. This is because we have slightly updated the controllers' implementations and proofs since the submission.

### Reproducing Performance Results in Table 3 (~X compute-minutes + ~Y human-minutes)

Following the instructions, you will reproduce the key results that the verified controllers achieve comparable performance to the unverified reference controllers as shown in Table 3.

**Step 1: setup environment**
Same as the Kick-the-tires Instructions.

**Step 2: run workload**

```bash
bash anvil-ae-sampled.sh
```
It runs 10% of the workloads for the three controllers, and prints the table to the file `anvil-table-3.txt`.
It takes approximately 10 hours to finish.

**Step 3: check the performance result**
```bash
cat anvil-table-3.txt
```

and you should see a generated table like this:
| Controller                         |   Verified (Anvil) Mean |   Verified (Anvil) Max |   Reference (unverified) Mean |   Reference (unverified) Max |
|------------------------------------|-------------------------|------------------------|-------------------------------|------------------------------|
| testrun-anvil-zk-performance       |                 151.655 |                160.793 |                       145.006 |                      160.501 |
| testrun-anvil-rabbitmq-performance |                 217.23  |                360.532 |                       214.493 |                      357.244 |
| testrun-anvil-fluent-performance   |                  37.989 |                 40.339 |                        29.188 |                       35.648 |
