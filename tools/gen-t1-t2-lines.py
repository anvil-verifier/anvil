import os
import json


def main():
    os.system(
        "python3 count-lines.py $VERUS_DIR/source/tools/line_count/zookeeper_table zookeeper"
    )
    os.system(
        "python3 count-lines.py $VERUS_DIR/source/tools/line_count/rabbitmq_table rabbitmq"
    )
    os.system(
        "python3 count-lines.py $VERUS_DIR/source/tools/line_count/fluent_table fluent"
    )
    os.system(
        "python3 count-anvil-lines.py $VERUS_DIR/source/tools/line_count/lib_table"
    )
    zk_data = json.load(open("zookeeper-lines.json"))
    rmq_data = json.load(open("rabbitmq-lines.json"))
    fb_data = json.load(open("fluent-lines.json"))
    anvil_data = json.load(open("anvil-lines.json"))
    print("ZooKeeper:")
    print(
        "Liveness & {} & -- & {}".format(
            zk_data["liveness_theorem"]["Trusted"],
            zk_data["liveness_proof"]["Proof"],
        )
    )
    print(
        "Conformance & 5 & -- & {}".format(
            zk_data["reconcile_impl"]["Proof"] - 5,
        )
    )
    print(
        "Controller model & -- & -- & {}".format(
            zk_data["reconcile_model"]["Proof"],
        )
    )
    print(
        "Controller impl & -- & {} & --".format(
            zk_data["reconcile_model"]["Exec"] + zk_data["reconcile_impl"]["Exec"],
        )
    )
    print(
        "Trusted wrapper & {} & -- & --".format(
            zk_data["wrapper"]["Trusted"],
        )
    )
    print(
        "Trusted ZooKeeper API & {} & -- & --".format(
            zk_data["external_model"]["Trusted"],
        )
    )
    print(
        "Trusted entry point & {} & -- & --".format(
            zk_data["entry"]["Trusted"],
        )
    )

    print("RabbitMQ:")
    print(
        "Liveness & {} & -- & {}".format(
            rmq_data["liveness_theorem"]["Trusted"],
            rmq_data["liveness_proof"]["Proof"],
        )
    )
    print(
        "Safety & {} & -- & {}".format(
            rmq_data["safety_theorem"]["Trusted"],
            rmq_data["safety_proof"]["Proof"],
        )
    )
    print(
        "Conformance & 5 & -- & {}".format(
            rmq_data["reconcile_impl"]["Proof"] - 5,
        )
    )
    print(
        "Controller model & -- & -- & {}".format(
            rmq_data["reconcile_model"]["Proof"],
        )
    )
    print(
        "Controller impl & -- & {} & --".format(
            rmq_data["reconcile_model"]["Exec"] + rmq_data["reconcile_impl"]["Exec"],
        )
    )
    print(
        "Trusted wrapper & {} & -- & --".format(
            rmq_data["wrapper"]["Trusted"],
        )
    )
    print(
        "Trusted entry point & {} & -- & --".format(
            rmq_data["entry"]["Trusted"],
        )
    )

    print("Fluent:")
    print(
        "Liveness & {} & -- & {}".format(
            fb_data["liveness_theorem"]["Trusted"],
            fb_data["liveness_proof"]["Proof"],
        )
    )
    print(
        "Conformance & 10 & -- & {}".format(
            fb_data["reconcile_impl"]["Proof"] - 10,
        )
    )
    print(
        "Controller model & -- & -- & {}".format(
            fb_data["reconcile_model"]["Proof"],
        )
    )
    print(
        "Controller impl & -- & {} & --".format(
            fb_data["reconcile_model"]["Exec"] + fb_data["reconcile_impl"]["Exec"],
        )
    )
    print(
        "Trusted wrapper & {} & -- & --".format(
            fb_data["wrapper"]["Trusted"],
        )
    )
    print(
        "Trusted entry point & {} & -- & --".format(
            fb_data["entry"]["Trusted"],
        )
    )
    print("Anvil:")
    print(
        "TLA embedding & {} & -- & --".format(
            anvil_data["tla_embedding_lines"]["Trusted"]
        )
    )
    print(
        "Model & {} & -- & --".format(
            anvil_data["other_lines"]["Trusted"]
            + anvil_data["object_model_lines"]["Trusted"]
        )
    )
    print(
        "Lemmas & -- & -- & {}".format(
            anvil_data["k8s_lemma_lines"]["Proof"]
            + anvil_data["tla_lemma_lines"]["Proof"]
        )
    )
    print(
        "Shim layer & {} & -- & --".format(
            anvil_data["object_wrapper_lines"]["Trusted"]
            + anvil_data["other_lines"]["Exec"]
        )
    )


if __name__ == "__main__":
    main()
