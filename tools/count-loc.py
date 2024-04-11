import sys
import json

FILE_COL = 1
TRUSTED_COL = 2
SPEC_COL = 3
PROOF_COL = 4
EXEC_COL = 5
PROOF_AND_EXEC_COL = 6


def empty_counting_map():
    return {
        "Trusted": 0,
        "Exec": 0,
        "Proof": 0,
    }


def parse_table_and_collect_lines(file_path, controller_name):
    liveness_theorem_lines = empty_counting_map()
    model_lines = empty_counting_map()
    impl_lines = empty_counting_map()
    liveness_proof_lines = empty_counting_map()
    liveness_inv_lines = empty_counting_map()
    safety_theorem_lines = empty_counting_map()
    safety_proof_lines = empty_counting_map()
    external_model_lines = empty_counting_map()
    wrapper_lines = empty_counting_map()
    entry_lines = empty_counting_map()
    other_lines = empty_counting_map()
    # total_lines = empty_counting_map()

    with open(file_path, "r") as file:
        lines = file.readlines()
        line_num = 0
        line_len = len(lines)
        for line in lines:
            # print(line)
            line_num = line_num + 1  # We start from 1
            cols = line.strip().split("|")
            # print(cols)
            stripped_cols = [col.strip() for col in cols]
            # print(stripped_cols)
            if line_num == 1:
                # Sanity check the schema of the table
                assert stripped_cols[FILE_COL] == "file", print(stripped_cols[FILE_COL])
                assert stripped_cols[TRUSTED_COL] == "Trusted", print(
                    stripped_cols[TRUSTED_COL]
                )
                assert stripped_cols[SPEC_COL] == "Spec", print(stripped_cols[SPEC_COL])
                assert stripped_cols[PROOF_COL] == "Proof", print(
                    stripped_cols[PROOF_COL]
                )
                assert stripped_cols[EXEC_COL] == "Exec", print(stripped_cols[EXEC_COL])
                assert stripped_cols[PROOF_AND_EXEC_COL] == "Proof+Exec", print(
                    stripped_cols[PROOF_AND_EXEC_COL]
                )
            elif line_num == line_len - 1:
                assert "----------------" in stripped_cols[FILE_COL], print(
                    stripped_cols[FILE_COL]
                )
            elif line_num == line_len:
                assert "total" in stripped_cols[FILE_COL], print(
                    stripped_cols[FILE_COL]
                )
            if line_num <= 2 or line_num >= line_len - 1:
                # Skip the first two lines and the last two lines
                continue
            if controller_name + "_controller" not in stripped_cols[FILE_COL]:
                # Skip the files that don't belong to this controller
                continue
            if controller_name + "_controller.rs" == stripped_cols[FILE_COL]:
                entry_lines["Trusted"] += int(stripped_cols[EXEC_COL])
                entry_lines["Trusted"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                entry_lines["Trusted"] += int(stripped_cols[PROOF_COL])
                entry_lines["Trusted"] += int(stripped_cols[SPEC_COL])
            elif (
                controller_name == "rabbitmq"
                and "/proof/safety/" in stripped_cols[FILE_COL]
            ):
                safety_proof_lines["Exec"] += int(stripped_cols[EXEC_COL])
                safety_proof_lines["Exec"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                safety_proof_lines["Proof"] += int(stripped_cols[PROOF_COL])
                safety_proof_lines["Proof"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                safety_proof_lines["Proof"] += int(stripped_cols[SPEC_COL])
            elif controller_name == "zookeeper" and (
                "/trusted/zookeeper_api_spec.rs" in stripped_cols[FILE_COL]
                or "/trusted/zookeeper_api_exec.rs" in stripped_cols[FILE_COL]
                or "/trusted/config_map.rs" in stripped_cols[FILE_COL]
            ):
                external_model_lines["Trusted"] += int(stripped_cols[EXEC_COL])
                external_model_lines["Trusted"] += int(stripped_cols[PROOF_COL])
                external_model_lines["Trusted"] += int(
                    stripped_cols[PROOF_AND_EXEC_COL]
                )
                external_model_lines["Trusted"] += int(stripped_cols[SPEC_COL])
            elif (
                "/trusted/spec_types.rs" in stripped_cols[FILE_COL]
                or "/trusted/exec_types.rs" in stripped_cols[FILE_COL]
                or "/trusted/step.rs" in stripped_cols[FILE_COL]
            ):
                wrapper_lines["Trusted"] += int(stripped_cols[EXEC_COL])
                wrapper_lines["Trusted"] += int(stripped_cols[PROOF_COL])
                wrapper_lines["Trusted"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                wrapper_lines["Trusted"] += int(stripped_cols[SPEC_COL])
            elif "/exec/" in stripped_cols[FILE_COL]:
                impl_lines["Exec"] += int(stripped_cols[EXEC_COL])
                impl_lines["Exec"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                impl_lines["Proof"] += int(stripped_cols[PROOF_COL])
                impl_lines["Proof"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                impl_lines["Proof"] += int(stripped_cols[SPEC_COL])
            elif "/model/" in stripped_cols[FILE_COL]:
                model_lines["Exec"] += int(stripped_cols[EXEC_COL])
                model_lines["Exec"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                model_lines["Proof"] += int(stripped_cols[PROOF_COL])
                model_lines["Proof"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                model_lines["Proof"] += int(stripped_cols[SPEC_COL])
            elif (
                "/trusted/liveness_theorem.rs" in stripped_cols[FILE_COL]
                or "trusted/maker.rs" in stripped_cols[FILE_COL]
            ):
                liveness_theorem_lines["Trusted"] += int(stripped_cols[EXEC_COL])
                liveness_theorem_lines["Trusted"] += int(stripped_cols[PROOF_COL])
                liveness_theorem_lines["Trusted"] += int(
                    stripped_cols[PROOF_AND_EXEC_COL]
                )
                liveness_theorem_lines["Trusted"] += int(stripped_cols[SPEC_COL])
            elif "/trusted/safety_theorem.rs" in stripped_cols[FILE_COL]:
                safety_theorem_lines["Trusted"] += int(stripped_cols[EXEC_COL])
                safety_theorem_lines["Trusted"] += int(stripped_cols[PROOF_COL])
                safety_theorem_lines["Trusted"] += int(
                    stripped_cols[PROOF_AND_EXEC_COL]
                )
                safety_theorem_lines["Trusted"] += int(stripped_cols[SPEC_COL])
            elif "/proof/" in stripped_cols[FILE_COL]:
                if "/proof/helper_invariants" in stripped_cols[FILE_COL]:
                    liveness_inv_lines["Exec"] += int(stripped_cols[EXEC_COL])
                    liveness_inv_lines["Exec"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                    liveness_inv_lines["Proof"] += int(stripped_cols[PROOF_COL])
                    liveness_inv_lines["Proof"] += int(
                        stripped_cols[PROOF_AND_EXEC_COL]
                    )
                    liveness_inv_lines["Proof"] += int(stripped_cols[SPEC_COL])
                liveness_proof_lines["Exec"] += int(stripped_cols[EXEC_COL])
                liveness_proof_lines["Exec"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                liveness_proof_lines["Proof"] += int(stripped_cols[PROOF_COL])
                liveness_proof_lines["Proof"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                liveness_proof_lines["Proof"] += int(stripped_cols[SPEC_COL])
            else:
                # print(line)  # Print out the lines that are hard to classify
                other_lines["Exec"] += int(stripped_cols[EXEC_COL])
                other_lines["Proof"] += int(stripped_cols[PROOF_COL])
                other_lines["Proof"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                other_lines["Proof"] += int(stripped_cols[SPEC_COL])
    all_lines = {
        "liveness_theorem": liveness_theorem_lines,
        "reconcile_model": model_lines,
        "reconcile_impl": impl_lines,
        "liveness_proof": liveness_proof_lines,
        "liveness_inv": liveness_inv_lines,
        "safety_theorem": safety_theorem_lines,
        "safety_proof": safety_proof_lines,
        "external_model": external_model_lines,
        "wrapper": wrapper_lines,
        "entry": entry_lines,
        "other": other_lines,
    }
    json.dump(all_lines, open(controller_name + "-loc.json", "w"), indent=4)


def main():
    file_path = sys.argv[1]
    controller_name = sys.argv[2]
    parse_table_and_collect_lines(file_path, controller_name)


if __name__ == "__main__":
    main()
