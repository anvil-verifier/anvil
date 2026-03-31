import sys
import json

FILE_COL = 1
TRUSTED_COL = 2
SPEC_COL = 3
PROOF_COL = 4
EXEC_COL = 5
PROOF_AND_EXEC_COL = 6

# Map from short name to directory name fragment
CONTROLLER_DIR = {
    "vreplicaset": "vreplicaset_controller",
    "vdeployment": "vdeployment_controller",
    "vstatefulset": "vstatefulset_controller",
    "rabbitmq": "rabbitmq_controller",
    "composition": "composition",
}


def empty_row():
    """6-column row: trusted_spec, trusted_unverified, exec, proof_conformance, proof_guarantee, proof_esr."""
    return {
        "trusted_spec": 0,
        "trusted_unverified": 0,
        "exec": 0,
        "proof_conformance": 0,
        "proof_guarantee": 0,
        "proof_esr": 0,
    }


def all_lines(cols):
    """Sum all code-line columns (Trusted + Spec + Proof + Exec + Proof+Exec)."""
    return (
        int(cols[TRUSTED_COL])
        + int(cols[SPEC_COL])
        + int(cols[PROOF_COL])
        + int(cols[EXEC_COL])
        + int(cols[PROOF_AND_EXEC_COL])
    )


def exec_lines(cols):
    """Executable lines: Exec + Proof+Exec."""
    return int(cols[EXEC_COL]) + int(cols[PROOF_AND_EXEC_COL])


def proof_lines(cols):
    """Proof/spec lines: Spec + Proof + Proof+Exec."""
    return int(cols[SPEC_COL]) + int(cols[PROOF_COL]) + int(cols[PROOF_AND_EXEC_COL])


def is_exec_reconciler_file(fname, controller_name):
    """Check if a file belongs to the exec/reconciler category for a controller.

    For rabbitmq: exec/reconciler.rs and exec/resource/*.rs
    For others: all files under exec/ (reconciler.rs, validation.rs, mod.rs, etc.)
    """
    if "/exec/" not in fname:
        return False
    if controller_name == "rabbitmq":
        # Include exec/reconciler and exec/resource/
        return "/exec/reconciler" in fname or "/exec/resource/" in fname
    else:
        # Include exec/reconciler
        return "/exec/reconciler" in fname


def parse_table_and_collect_lines(file_path, controller_name):
    row = empty_row()

    with open(file_path, "r") as file:
        lines = file.readlines()
        line_num = 0
        line_len = len(lines)
        for line in lines:
            line_num += 1
            cols = line.strip().split("|")
            stripped_cols = [col.strip() for col in cols]

            if line_num == 1:
                # Sanity check the schema of the table
                assert stripped_cols[FILE_COL] == "file", stripped_cols[FILE_COL]
                assert stripped_cols[TRUSTED_COL] == "Trusted", stripped_cols[TRUSTED_COL]
                assert stripped_cols[SPEC_COL] == "Spec", stripped_cols[SPEC_COL]
                assert stripped_cols[PROOF_COL] == "Proof", stripped_cols[PROOF_COL]
                assert stripped_cols[EXEC_COL] == "Exec", stripped_cols[EXEC_COL]
                assert stripped_cols[PROOF_AND_EXEC_COL] == "Proof+Exec", stripped_cols[PROOF_AND_EXEC_COL]
            elif line_num == line_len - 1:
                assert "----------------" in stripped_cols[FILE_COL], stripped_cols[FILE_COL]
            elif line_num == line_len:
                assert "total" in stripped_cols[FILE_COL], stripped_cols[FILE_COL]

            if line_num <= 2 or line_num >= line_len - 1:
                continue

            fname = stripped_cols[FILE_COL]

            # --- Composition ---
            # Composition has trusted_spec (spec functions) and proof_esr;
            # no guarantee, conformance, trusted_unverified, or exec.
            if controller_name == "composition":
                if "controllers/composition/" not in fname:
                    continue
                row["trusted_spec"] += int(stripped_cols[SPEC_COL])
                row["proof_esr"] += int(stripped_cols[PROOF_COL])
                continue

            if CONTROLLER_DIR[controller_name] not in fname:
                continue
            if "controllers/composition/" in fname:
                continue

            # --- trusted_spec: trusted/{rely_guarantee|liveness_theorem} ---
            if (
                "/trusted/rely_guarantee.rs" in fname
                or "/trusted/liveness_theorem.rs" in fname
            ):
                row["trusted_spec"] += all_lines(stripped_cols)

            # --- trusted_unverified: trusted/{spec_types|exec_types|step|reconciler} ---
            elif (
                "/trusted/spec_types.rs" in fname
                or "/trusted/exec_types.rs" in fname
                or "/trusted/step.rs" in fname
                or "/trusted/reconciler.rs" in fname
            ):
                row["trusted_unverified"] += all_lines(stripped_cols)

            # --- exec + proof_conformance: exec/reconciler (+ resource/*.rs for rabbitmq) ---
            elif is_exec_reconciler_file(fname, controller_name):
                row["exec"] += exec_lines(stripped_cols)
                row["proof_conformance"] += proof_lines(stripped_cols)

            # --- proof_guarantee: proof/guarantee ---
            elif "/proof/guarantee.rs" in fname:
                row["proof_guarantee"] += proof_lines(stripped_cols)
                row["proof_guarantee"] += exec_lines(stripped_cols)

            # --- proof_esr: all other proofs in controller path ---
            elif "/proof/" in fname or "/model/" in fname:
                row["proof_esr"] += proof_lines(stripped_cols)

            # else: uncategorized (e.g. trusted/safety_theorem.rs, trusted/mod.rs,
            # trusted/util.rs, trusted/reconciler.rs, controller root mod.rs) - skip

    json.dump(row, open(controller_name + "-loc.json", "w"), indent=4)

    # Print summary
    total = sum(row.values())
    print(f"[{controller_name}] LOC breakdown:")
    for k, v in row.items():
        print(f"  {k:>20}: {v}")
    print(f"  {'total':>20}: {total}")
    print()


def main():
    file_path = sys.argv[1]
    controller_name = sys.argv[2]
    parse_table_and_collect_lines(file_path, controller_name)


if __name__ == "__main__":
    main()
