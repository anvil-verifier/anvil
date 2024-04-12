import os
import json

indent = "    "

debug = False

cap_controllers = {
    "zookeeper": "ZooKeeper controller",
    "rabbitmq": "RabbitMQ controller",
    "fluent": "Fluent controller",
}


def count_total_lines(data):
    lines = 0
    for key in data:
        for inner_key in data[key]:
            lines += data[key][inner_key]
    return lines


def gen_for_controller(controller):
    os.system(
        "python3 count-loc.py $VERUS_DIR/source/tools/line_count/{}_loc_table {}".format(
            controller, controller
        )
    )
    data = json.load(open("{}-loc.json".format(controller)))

    total = {
        "Trusted": 0,
        "Exec": 0,
        "Proof": 0,
    }
    if debug:
        missed_lines = count_total_lines(data)
        missed_lines -= data["liveness_inv"]["Proof"]

    print("{}:".format(cap_controllers[controller]))

    # Count LoC for liveness proof
    print(
        indent
        + "Liveness\t\t\t& {}\t& --\t& {}".format(
            data["liveness_theorem"]["Trusted"],
            data["liveness_proof"]["Proof"],
        )
    )
    total["Trusted"] += data["liveness_theorem"]["Trusted"]
    total["Proof"] += data["liveness_proof"]["Proof"]
    if debug:
        missed_lines -= data["liveness_theorem"]["Trusted"]
        missed_lines -= data["liveness_proof"]["Proof"]

    if controller == "rabbitmq":
        # Count LoC for safety proof for RabbitMQ controller only
        print(
            indent
            + "Safety\t\t\t& {}\t& --\t& {}".format(
                data["safety_theorem"]["Trusted"],
                data["safety_proof"]["Proof"],
            )
        )
        total["Trusted"] += data["safety_theorem"]["Trusted"]
        total["Proof"] += data["safety_proof"]["Proof"]
        if debug:
            missed_lines -= data["safety_theorem"]["Trusted"]
            missed_lines -= data["safety_proof"]["Proof"]

    if controller == "fluent":
        # Count LoC for conformance proof
        # for Fluent controller only because its conformance theorem takes 10 lines (it has two reconcile loops)
        print(
            indent
            + "Conformance\t\t\t& 10\t& --\t& {}".format(
                data["reconcile_impl"]["Proof"] - 10,
            )
        )
        total["Trusted"] += 10
        total["Proof"] += data["reconcile_impl"]["Proof"] - 10
    else:
        # Count LoC for conformance proof for the other two controllers whose conformance theorem takes only 5 lines
        print(
            indent
            + "Conformance\t\t\t& 5\t& --\t& {}".format(
                data["reconcile_impl"]["Proof"] - 5,
            )
        )
        total["Trusted"] += 5
        total["Proof"] += data["reconcile_impl"]["Proof"] - 5
    if debug:
        missed_lines -= data["reconcile_impl"]["Proof"]

    # Count LoC for controller model
    print(
        indent
        + "Controller model\t\t& --\t& --\t& {}".format(
            data["reconcile_model"]["Proof"],
        )
    )
    total["Proof"] += data["reconcile_model"]["Proof"]
    if debug:
        missed_lines -= data["reconcile_model"]["Proof"]

    # Count LoC for controller implementation
    print(
        indent
        + "Controller impl\t\t& --\t& {}\t& --".format(
            data["reconcile_model"]["Exec"] + data["reconcile_impl"]["Exec"],
        )
    )
    total["Exec"] += data["reconcile_model"]["Exec"] + data["reconcile_impl"]["Exec"]
    if debug:
        missed_lines -= data["reconcile_model"]["Exec"] + data["reconcile_impl"]["Exec"]

    # Count LoC for trusted wrapper
    print(
        indent
        + "Trusted wrapper\t\t& {}\t& --\t& --".format(
            data["wrapper"]["Trusted"],
        )
    )
    total["Trusted"] += data["wrapper"]["Trusted"]
    if debug:
        missed_lines -= data["wrapper"]["Trusted"]

    if controller == "zookeeper":
        # Count LoC for trusted ZooKeeper API for ZooKeeper controller only
        print(
            indent
            + "Trusted ZooKeeper API\t& {}\t& --\t& --".format(
                data["external_model"]["Trusted"],
            )
        )
        total["Trusted"] += data["external_model"]["Trusted"]
        if debug:
            missed_lines -= data["external_model"]["Trusted"]

    # Count LoC for trusted entry point
    print(
        indent
        + "Trusted entry point\t\t& {}\t& --\t& --".format(
            data["entry"]["Trusted"],
        )
    )
    total["Trusted"] += data["entry"]["Trusted"]
    if debug:
        missed_lines -= data["entry"]["Trusted"]

    # Count total LoC
    print(
        indent
        + "Total\t\t\t& {}\t& {}\t& {}".format(
            total["Trusted"],
            total["Exec"],
            total["Proof"],
        )
    )
    if debug:
        print("{} lines are not included".format(missed_lines))
    return total


def gen_for_anvil():
    os.system(
        "python3 count-anvil-loc.py $VERUS_DIR/source/tools/line_count/anvil_loc_table"
    )
    anvil_data = json.load(open("anvil-loc.json"))
    if debug:
        missed_lines = count_total_lines(anvil_data)
        missed_lines -= anvil_data["test_lines"]["Exec"]
    print("Anvil:")
    print(
        indent
        + "Lemmas\t\t\t& --\t& --\t& {}".format(
            anvil_data["k8s_lemma_lines"]["Proof"]
            + anvil_data["tla_lemma_lines"]["Proof"]
        )
    )
    if debug:
        missed_lines -= (
            anvil_data["k8s_lemma_lines"]["Proof"]
            + anvil_data["tla_lemma_lines"]["Proof"]
        )
    print(
        indent
        + "TLA embedding\t\t& {}\t& --\t& --".format(
            anvil_data["tla_embedding_lines"]["Trusted"]
        )
    )
    if debug:
        missed_lines -= anvil_data["tla_embedding_lines"]["Trusted"]
    print(
        indent
        + "Model\t\t\t& {}\t& --\t& --".format(anvil_data["other_lines"]["Trusted"])
    )
    if debug:
        missed_lines -= anvil_data["other_lines"]["Trusted"]
    print(
        indent
        + "Object view\t\t\t& {}\t& --\t& --".format(
            anvil_data["object_model_lines"]["Trusted"]
        )
    )
    if debug:
        missed_lines -= anvil_data["object_model_lines"]["Trusted"]
    print(
        indent
        + "Object wrapper\t\t& {}\t& --\t& --".format(
            anvil_data["object_wrapper_lines"]["Trusted"]
        )
    )
    if debug:
        missed_lines -= anvil_data["object_wrapper_lines"]["Trusted"]
    print(
        indent
        + "Shim layer\t\t\t& {}\t& --\t& --".format(anvil_data["other_lines"]["Exec"])
    )
    if debug:
        missed_lines -= anvil_data["other_lines"]["Exec"]
    if debug:
        print("{} lines are not included".format(missed_lines))


def main():
    zookeeper_total = gen_for_controller("zookeeper")
    rabbitmq_total = gen_for_controller("rabbitmq")
    fluent_total = gen_for_controller("fluent")
    print(
        "Total(all)\t\t\t& {}\t& {}\t& {}".format(
            zookeeper_total["Trusted"]
            + rabbitmq_total["Trusted"]
            + fluent_total["Trusted"],
            zookeeper_total["Exec"] + rabbitmq_total["Exec"] + fluent_total["Exec"],
            zookeeper_total["Proof"] + rabbitmq_total["Proof"] + fluent_total["Proof"],
        )
    )
    # gen_for_anvil()


if __name__ == "__main__":
    main()
