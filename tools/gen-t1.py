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
    "model",
    "proof_guarantee",
    "core_esr",
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


DISPLAY_COLUMNS = ["trusted_spec", "trusted_unverified", "exec", "model"]


def make_display_row(label, loc_data):
    """Build a display row: 4 base columns + Core (guarantee + core_esr) + ESR (core_esr)."""
    row = [label]
    for col in DISPLAY_COLUMNS:
        row.append(str(loc_data[col]))
    row.append(str(loc_data["proof_guarantee"] + loc_data["core_esr"]))
    row.append(str(loc_data["core_esr"]))
    return row


def gen_for_controller(controller):
    table = []
    verus_lc_dir = os.path.join(os.environ["VERUS_DIR"], "source/tools/line_count")
    os.system(
        "python3 count-loc.py {}/{}_loc_table {}".format(
            verus_lc_dir, controller, controller
        )
    )
    loc_data = json.load(open("{}-loc.json".format(controller)))
    table.append(make_display_row(cap_controllers[controller], loc_data))
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
    table.append(make_display_row("Composition proofs", loc_data))
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
    grand = {col: sum(totals[c][col] for c in all_keys) for col in LOC_COLUMNS}
    grand = make_display_row("Total(all)", grand)
    # remove grand ESR and grand/total = model + core proof
    total_cnt = int(grand[4]) + int(grand[5])
    grand[5] = str(total_cnt)
    grand[6] = "--"
    table.append(grand)

    if print_anvil:
        table += gen_for_anvil()
    headers = [
        "",
        "Trusted Spec",
        "Trusted Unverified",
        "Exec",
        "Model",
        "Core",
        "ESR",
    ]
    print(tabulate(table, headers, tablefmt="github"))


if __name__ == "__main__":
    main()
