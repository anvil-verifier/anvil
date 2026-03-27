import os
import json
from tabulate import tabulate

indent = "|---"

print_anvil = False

cap_controllers = {
    "vdeployment": "VDeployment controller",
    "vreplicaset": "VReplicaSet controller",
    "vstatefulset": "VStatefulSet controller",
    "rabbitmq": "RabbitMQ controller",
}


def gen_for_anvil():
    table = []
    verus_lc_dir = os.path.join(os.environ["VERUS_DIR"], "source/tools/line_count")
    os.system(
        "python3 count-anvil-loc.py {}/anvil_loc_table".format(verus_lc_dir)
    )
    anvil_loc_data = json.load(open("anvil-loc.json"))
    anvil_raw_data = json.load(open("{}/anvil.json".format(verus_lc_dir)))

    table.append(["Anvil", "", "", "", ""])
    table.append(
        [
            indent + "Lemmas",
            "--",
            "--",
            str(
                anvil_loc_data["k8s_lemma_lines"]["Proof"]
                + anvil_loc_data["tla_lemma_lines"]["Proof"]
            ),
            "{} ({})".format(
                anvil_raw_data["times-ms"]["total-verify"] / 1000,
                anvil_raw_data["times-ms"]["total"] / 1000,
            ),
        ]
    )
    table.append(
        [
            indent + "TLA embedding",
            str(anvil_loc_data["tla_embedding_lines"]["Trusted"]),
            "--",
            "--",
            "--",
        ]
    )
    table.append(
        [
            indent + "Model",
            str(anvil_loc_data["other_lines"]["Trusted"]),
            "--",
            "--",
            "--",
        ]
    )
    table.append(
        [
            indent + "Object view",
            str(anvil_loc_data["object_model_lines"]["Trusted"]),
            "--",
            "--",
            "--",
        ]
    )
    table.append(
        [
            indent + "Object wrapper",
            str(anvil_loc_data["object_wrapper_lines"]["Trusted"]),
            "--",
            "--",
            "--",
        ]
    )
    table.append(
        [
            indent + "Shim layer",
            str(anvil_loc_data["other_lines"]["Exec"]),
            "--",
            "--",
            "--",
        ]
    )
    return table


def gen_for_controller(controller):
    table = []
    verus_lc_dir = os.path.join(os.environ["VERUS_DIR"], "source/tools/line_count")
    os.system(
        "python3 count-loc.py {}/{}_loc_table {}".format(
            verus_lc_dir, controller, controller
        )
    )
    os.system("python3 count-time.py {}/{}.json {}".format(verus_lc_dir, controller, controller))
    loc_data = json.load(open("{}-loc.json".format(controller)))
    time_data = json.load(open("{}-time.json".format(controller)))
    raw_data = json.load(open("{}/{}.json".format(verus_lc_dir, controller)))

    total = {"Trusted": 0, "Exec": 0, "Proof": 0, "Time": 0, "TimeParallel": 0}

    table.append([cap_controllers[controller], "", "", "", ""])
    table.append(
        [
            indent + "Liveness",
            str(loc_data["liveness_theorem"]["Trusted"]),
            "--",
            str(loc_data["liveness_proof"]["Proof"]),
            str(time_data["Liveness"] / 1000),
        ]
    )
    total["Trusted"] += loc_data["liveness_theorem"]["Trusted"]
    total["Proof"] += loc_data["liveness_proof"]["Proof"]

    if controller == "rabbitmq":
        table.append(
            [
                indent + "Safety",
                str(loc_data["safety_theorem"]["Trusted"]),
                "--",
                str(loc_data["safety_proof"]["Proof"]),
                str(time_data["Safety"] / 1000),
            ]
        )
        total["Trusted"] += loc_data["safety_theorem"]["Trusted"]
        total["Proof"] += loc_data["safety_proof"]["Proof"]

    table.append(
        [
            indent + "Conformance",
            str(5),
            "--",
            str(loc_data["reconcile_impl"]["Proof"] - 5),
            str(time_data["Impl"] / 1000),
        ]
    )
    total["Trusted"] += 5
    total["Proof"] += loc_data["reconcile_impl"]["Proof"] - 5

    table.append(
        [
            indent + "Controller model",
            "--",
            "--",
            str(loc_data["reconcile_model"]["Proof"]),
            "--",
        ]
    )
    total["Proof"] += loc_data["reconcile_model"]["Proof"]

    table.append(
        [
            indent + "Controller impl",
            "--",
            str(
                loc_data["reconcile_model"]["Exec"] + loc_data["reconcile_impl"]["Exec"]
            ),
            "--",
            "--",
        ]
    )
    total["Exec"] += (
        loc_data["reconcile_model"]["Exec"] + loc_data["reconcile_impl"]["Exec"]
    )

    table.append(
        [
            indent + "Trusted wrapper",
            str(loc_data["wrapper"]["Trusted"]),
            "--",
            "--",
            "--",
        ]
    )
    total["Trusted"] += loc_data["wrapper"]["Trusted"]



    table.append(
        [
            indent + "Trusted entry point",
            str(loc_data["entry"]["Trusted"]),
            "--",
            "--",
            "--",
        ]
    )
    total["Trusted"] += loc_data["entry"]["Trusted"]

    total["Time"] = time_data["Total"]
    total["TimeParallel"] = raw_data["times-ms"]["total"]

    table.append(
        [
            indent + "Total",
            str(total["Trusted"]),
            str(total["Exec"]),
            str(total["Proof"]),
            "{} ({})".format(total["Time"] / 1000, total["TimeParallel"] / 1000),
        ]
    )
    return total, table


def gen_for_composition(base_controller):
    """Generate composition proof stats using any controller's loc table that includes composition files."""
    table = []
    verus_lc_dir = os.path.join(os.environ["VERUS_DIR"], "source/tools/line_count")
    # Use the base_controller's loc table to extract composition lines
    os.system(
        "python3 count-loc.py {}/{}_loc_table composition".format(
            verus_lc_dir, base_controller
        )
    )
    os.system("python3 count-time.py {}/{}.json composition".format(verus_lc_dir, base_controller))
    loc_data = json.load(open("composition-loc.json"))
    time_data = json.load(open("composition-time.json"))
    raw_data = json.load(open("{}/{}.json".format(verus_lc_dir, base_controller)))

    total = {"Trusted": 0, "Exec": 0, "Proof": 0, "Time": 0, "TimeParallel": 0}

    table.append(["Composition proofs", "", "", "", ""])
    table.append(
        [
            indent + "Composition proof",
            "--",
            str(loc_data["composition_proof"]["Exec"]),
            str(loc_data["composition_proof"]["Proof"]),
            str(time_data["Composition"] / 1000),
        ]
    )
    total["Proof"] += loc_data["composition_proof"]["Proof"]
    total["Exec"] += loc_data["composition_proof"]["Exec"]
    total["Time"] = time_data["Composition"]
    total["TimeParallel"] = raw_data["times-ms"]["total"]

    table.append(
        [
            indent + "Total",
            str(total["Trusted"]),
            str(total["Exec"]),
            str(total["Proof"]),
            "{} ({})".format(total["Time"] / 1000, total["TimeParallel"] / 1000),
        ]
    )
    return total, table


def main():
    table = []
    controllers = ["vdeployment", "vreplicaset", "vstatefulset", "rabbitmq"]
    totals = {}
    for controller in controllers:
        totals[controller], controller_table = gen_for_controller(controller)
        table += controller_table
    # Use esr_composition's loc table which includes all composition files
    totals["composition"], composition_table = gen_for_composition("esr_composition")
    table += composition_table
    all_keys = controllers + ["composition"]
    table.append(
        [
            "Total(all)",
            str(sum(totals[c]["Trusted"] for c in all_keys)),
            str(sum(totals[c]["Exec"] for c in all_keys)),
            str(sum(totals[c]["Proof"] for c in all_keys)),
            "{} ({})".format(
                sum(totals[c]["Time"] for c in all_keys) / 1000,
                sum(totals[c]["TimeParallel"] for c in all_keys) / 1000,
            ),
        ]
    )
    if print_anvil:
        table += gen_for_anvil()
    headers = [
        "",
        "Trusted (LoC)",
        "Exec (LoC)",
        "Proof (LoC)",
        "Time to Verify (seconds)",
    ]
    print(tabulate(table, headers, tablefmt="github"))


if __name__ == "__main__":
    main()
