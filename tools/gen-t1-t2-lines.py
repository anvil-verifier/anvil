import os
import json


def count_total_lines(data):
    lines = 0
    for key in data:
        for inner_key in data[key]:
            lines += data[key][inner_key]
    return lines


def gen_for_controller(controller):
    os.system(
        "python3 count-lines.py $VERUS_DIR/source/tools/line_count/{}_table {}".format(
            controller, controller
        )
    )
    data = json.load(open("{}-lines.json".format(controller)))

    total_lines = count_total_lines(data)
    total_lines -= data["liveness_inv"]["Proof"]

    print("{}:".format(controller))
    print(
        "Liveness & {} & -- & {}".format(
            data["liveness_theorem"]["Trusted"],
            data["liveness_proof"]["Proof"],
        )
    )
    total_lines -= data["liveness_theorem"]["Trusted"]
    total_lines -= data["liveness_proof"]["Proof"]

    if controller == "rabbitmq":
        print(
            "Safety & {} & -- & {}".format(
                data["safety_theorem"]["Trusted"],
                data["safety_proof"]["Proof"],
            )
        )
        total_lines -= data["safety_theorem"]["Trusted"]
        total_lines -= data["safety_proof"]["Proof"]

    if controller == "fluent":
        print(
            "Conformance & 10 & -- & {}".format(
                data["reconcile_impl"]["Proof"] - 10,
            )
        )
    else:
        print(
            "Conformance & 5 & -- & {}".format(
                data["reconcile_impl"]["Proof"] - 5,
            )
        )
    total_lines -= data["reconcile_impl"]["Proof"]
    print(
        "Controller model & -- & -- & {}".format(
            data["reconcile_model"]["Proof"],
        )
    )
    total_lines -= data["reconcile_model"]["Proof"]
    print(
        "Controller impl & -- & {} & --".format(
            data["reconcile_model"]["Exec"] + data["reconcile_impl"]["Exec"],
        )
    )
    total_lines -= data["reconcile_model"]["Exec"] + data["reconcile_impl"]["Exec"]
    print(
        "Trusted wrapper & {} & -- & --".format(
            data["wrapper"]["Trusted"],
        )
    )
    total_lines -= data["wrapper"]["Trusted"]
    if controller == "zookeeper":
        print(
            "Trusted ZooKeeper API & {} & -- & --".format(
                data["external_model"]["Trusted"],
            )
        )
        total_lines -= data["external_model"]["Trusted"]
    print(
        "Trusted entry point & {} & -- & --".format(
            data["entry"]["Trusted"],
        )
    )
    total_lines -= data["entry"]["Trusted"]
    print("{} lines are not included".format(total_lines))


def main():
    gen_for_controller("zookeeper")
    gen_for_controller("rabbitmq")
    gen_for_controller("fluent")

    os.system(
        "python3 count-anvil-lines.py $VERUS_DIR/source/tools/line_count/lib_table"
    )
    anvil_data = json.load(open("anvil-lines.json"))
    total_lines = count_total_lines(anvil_data)
    total_lines -= anvil_data["test_lines"]["Exec"]
    print("Anvil:")
    print(
        "Lemmas & -- & -- & {}".format(
            anvil_data["k8s_lemma_lines"]["Proof"]
            + anvil_data["tla_lemma_lines"]["Proof"]
        )
    )
    total_lines -= (
        anvil_data["k8s_lemma_lines"]["Proof"] + anvil_data["tla_lemma_lines"]["Proof"]
    )
    print(
        "TLA embedding & {} & -- & --".format(
            anvil_data["tla_embedding_lines"]["Trusted"]
        )
    )
    total_lines -= anvil_data["tla_embedding_lines"]["Trusted"]
    print("Model & {} & -- & --".format(anvil_data["other_lines"]["Trusted"]))
    total_lines -= anvil_data["other_lines"]["Trusted"]
    print(
        "Object view & {} & -- & --".format(anvil_data["object_model_lines"]["Trusted"])
    )
    total_lines -= anvil_data["object_model_lines"]["Trusted"]
    print(
        "Object wrapper & {} & -- & --".format(
            anvil_data["object_wrapper_lines"]["Trusted"]
        )
    )
    total_lines -= anvil_data["object_wrapper_lines"]["Trusted"]
    print("Shim layer & {} & -- & --".format(anvil_data["other_lines"]["Exec"]))
    total_lines -= anvil_data["other_lines"]["Exec"]
    print("{} lines are not included".format(total_lines))


if __name__ == "__main__":
    main()
