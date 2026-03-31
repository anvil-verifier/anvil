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

LOC_COLUMNS = [
    "trusted_spec",
    "trusted_unverified",
    "exec",
    "proof_conformance",
    "proof_guarantee",
    "proof_esr",
]


def gen_for_anvil():
    table = []
    verus_lc_dir = os.path.join(os.environ["VERUS_DIR"], "source/tools/line_count")
    os.system(
        "python3 count-anvil-loc.py {}/anvil_loc_table".format(verus_lc_dir)
    )
    anvil_loc_data = json.load(open("anvil-loc.json"))
    anvil_raw_data = json.load(open("{}/anvil.json".format(verus_lc_dir)))

    table.append(["Anvil", "", "", "", "", "", ""])
    table.append(
        [
            indent + "Lemmas",
            "--",
            "--",
            "--",
            "--",
            "--",
            str(
                anvil_loc_data["k8s_lemma_lines"]["Proof"]
                + anvil_loc_data["tla_lemma_lines"]["Proof"]
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
            "--",
            "--",
        ]
    )
    table.append(
        [
            indent + "Shim layer",
            "--",
            "--",
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
    loc_data = json.load(open("{}-loc.json".format(controller)))

    total = sum(loc_data[col] for col in LOC_COLUMNS)

    row = [cap_controllers[controller]]
    for col in LOC_COLUMNS:
        row.append(str(loc_data[col]))
    row.append(str(total))
    table.append(row)

    return loc_data, table


def gen_for_composition(base_controller):
    """Generate composition proof stats using any controller's loc table that includes composition files."""
    table = []
    verus_lc_dir = os.path.join(os.environ["VERUS_DIR"], "source/tools/line_count")
    os.system(
        "python3 count-loc.py {}/{}_loc_table composition".format(
            verus_lc_dir, base_controller
        )
    )
    loc_data = json.load(open("composition-loc.json"))

    total = sum(loc_data[col] for col in LOC_COLUMNS)

    row = ["Composition proofs"]
    for col in LOC_COLUMNS:
        row.append(str(loc_data[col]))
    row.append(str(total))
    table.append(row)

    return loc_data, table


def main():
    table = []
    controllers = ["vreplicaset", "vdeployment", "vstatefulset", "rabbitmq"]
    totals = {}
    for controller in controllers:
        totals[controller], controller_table = gen_for_controller(controller)
        table += controller_table
    # Use esr_composition's loc table which includes all composition files
    totals["composition"], composition_table = gen_for_composition("esr_composition")
    table += composition_table

    # Grand totals row
    all_keys = controllers + ["composition"]
    grand_row = ["Total(all)"]
    grand_total = 0
    for col in LOC_COLUMNS:
        col_sum = sum(totals[c][col] for c in all_keys)
        grand_row.append(str(col_sum))
        grand_total += col_sum
    grand_row.append(str(grand_total))
    table.append(grand_row)

    if print_anvil:
        table += gen_for_anvil()
    headers = [
        "",
        "Trusted Spec",
        "Trusted Unverified",
        "Exec",
        "Proof Conformance",
        "Proof Guarantee",
        "Proof ESR",
        "Total",
    ]
    print(tabulate(table, headers, tablefmt="github"))


if __name__ == "__main__":
    main()

