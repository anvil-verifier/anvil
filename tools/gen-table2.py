import sys
import json


def main():
    zk_data = json.load(open("zookeeper-lines.json"))
    rmq_data = json.load(open("rabbitmq-lines.json"))
    fb_data = json.load(open("fluent-lines.json"))
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
        "Reconciliation model & -- & -- & {}".format(
            zk_data["reconcile_model"]["Proof"],
        )
    )
    print(
        "Reconciliation impl & -- & {} & --".format(
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
        "Reconciliation model & -- & -- & {}".format(
            rmq_data["reconcile_model"]["Proof"],
        )
    )
    print(
        "Reconciliation impl & -- & {} & --".format(
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
        "Reconciliation model & -- & -- & {}".format(
            fb_data["reconcile_model"]["Proof"],
        )
    )
    print(
        "Reconciliation impl & -- & {} & --".format(
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


if __name__ == "__main__":
    main()
