import os
import json
from tabulate import tabulate

indent = "|---"

print_anvil = False

cap_controllers = {
    "zookeeper": "ZooKeeper controller",
    "rabbitmq": "RabbitMQ controller",
    "fluent": "Fluent controller",
}


def gen_for_anvil():
    table = []
    os.system(
        "python3 count-anvil-loc.py $VERUS_DIR/source/tools/line_count/anvil_loc_table"
    )
    anvil_loc_data = json.load(open("anvil-loc.json"))
    anvil_raw_data = json.load(open("anvil.json"))

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
    os.system(
        "python3 count-loc.py $VERUS_DIR/source/tools/line_count/{}_loc_table {}".format(
            controller, controller
        )
    )
    os.system("python3 count-time.py {}.json {}".format(controller, controller))
    loc_data = json.load(open("{}-loc.json".format(controller)))
    time_data = json.load(open("{}-time.json".format(controller)))
    raw_data = json.load(open("{}.json".format(controller)))

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

    if controller == "fluent":
        table.append(
            [
                indent + "Conformance",
                str(10),
                "--",
                str(loc_data["reconcile_impl"]["Proof"] - 10),
                str(time_data["Impl"] / 1000),
            ]
        )
        total["Trusted"] += 10
        total["Proof"] += loc_data["reconcile_impl"]["Proof"] - 10
    else:
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

    if controller == "zookeeper":
        table.append(
            [
                indent + "Trusted ZooKeeper API",
                str(loc_data["external_model"]["Trusted"]),
                "--",
                "--",
                "--",
            ]
        )
        total["Trusted"] += loc_data["external_model"]["Trusted"]

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


def main():
    table = []
    zookeeper_total, zookeeper_table = gen_for_controller("zookeeper")
    rabbitmq_total, rabbitmq_table = gen_for_controller("rabbitmq")
    fluent_total, fluent_table = gen_for_controller("fluent")
    table += zookeeper_table
    table += rabbitmq_table
    table += fluent_table
    table.append(
        [
            "Total(all)",
            str(
                zookeeper_total["Trusted"]
                + rabbitmq_total["Trusted"]
                + fluent_total["Trusted"]
            ),
            str(
                zookeeper_total["Exec"] + rabbitmq_total["Exec"] + fluent_total["Exec"]
            ),
            str(
                zookeeper_total["Proof"]
                + rabbitmq_total["Proof"]
                + fluent_total["Proof"]
            ),
            "{} ({})".format(
                (
                    zookeeper_total["Time"]
                    + rabbitmq_total["Time"]
                    + fluent_total["Time"]
                )
                / 1000,
                (
                    zookeeper_total["TimeParallel"]
                    + rabbitmq_total["TimeParallel"]
                    + fluent_total["TimeParallel"]
                )
                / 1000,
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
