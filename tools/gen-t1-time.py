import os
import json

indent = "    "


def main():
    os.system("python3 count-time.py zookeeper.json zookeeper")
    os.system("python3 count-time.py rabbitmq.json rabbitmq")
    os.system("python3 count-time.py fluent.json fluent")
    zk_data = json.load(open("zookeeper-time.json"))
    rmq_data = json.load(open("rabbitmq-time.json"))
    fb_data = json.load(open("fluent-time.json"))
    zk_raw_data = json.load(open("zookeeper.json"))
    rmq_raw_data = json.load(open("rabbitmq.json"))
    fb_raw_data = json.load(open("fluent.json"))
    anvil_raw_data = json.load(open("anvil.json"))
    print("ZooKeeper controller:")
    print(indent + "Liveness & {}".format(zk_data["Liveness"] / 1000))
    print(indent + "Safety & {}".format(zk_data["Safety"] / 1000))
    print(indent + "Conformance & {}".format(zk_data["Impl"] / 1000))
    print(
        indent
        + "Total & {} ({})".format(
            zk_data["Total"] / 1000, zk_raw_data["times-ms"]["total"] / 1000
        )
    )
    print("RabbitMQ controller:")
    print(indent + "Liveness & {}".format(rmq_data["Liveness"] / 1000))
    print(indent + "Safety & {}".format(rmq_data["Safety"] / 1000))
    print(indent + "Conformance & {}".format(rmq_data["Impl"] / 1000))
    print(
        indent
        + "Total & {} ({})".format(
            rmq_data["Total"] / 1000, rmq_raw_data["times-ms"]["total"] / 1000
        )
    )
    print("Fluent controller:")
    print(indent + "Liveness & {}".format(fb_data["Liveness"] / 1000))
    print(indent + "Safety & {}".format(fb_data["Safety"] / 1000))
    print(indent + "Conformance & {}".format(fb_data["Impl"] / 1000))
    print(
        indent
        + "Total & {} ({})".format(
            fb_data["Total"] / 1000, fb_raw_data["times-ms"]["total"] / 1000
        )
    )
    print(
        "Total(all) & {} ({})".format(
            (zk_data["Total"] + rmq_data["Total"] + fb_data["Total"]) / 1000,
            (
                zk_raw_data["times-ms"]["total"]
                + rmq_raw_data["times-ms"]["total"]
                + fb_raw_data["times-ms"]["total"]
            )
            / 1000,
        )
    )
    # print("Anvil:")
    # print(
    #     "Reusable lemmas & {} ({})".format(
    #         anvil_raw_data["times-ms"]["total-verify"] / 1000,
    #         anvil_raw_data["times-ms"]["total"] / 1000,
    #     )
    # )


if __name__ == "__main__":
    main()
