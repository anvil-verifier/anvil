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


def parse_table_and_collect_lines(file_path):
    test_lines = empty_counting_map()
    tla_embedding_lines = empty_counting_map()
    k8s_lemma_lines = empty_counting_map()
    tla_lemma_lines = empty_counting_map()
    object_model_lines = empty_counting_map()
    object_wrapper_lines = empty_counting_map()
    other_lines = empty_counting_map()

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
            elif "unit_tests/" in stripped_cols[FILE_COL]:
                test_lines["Exec"] += int(stripped_cols[EXEC_COL])
                test_lines["Exec"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                test_lines["Proof"] += int(stripped_cols[PROOF_COL])
                test_lines["Proof"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                test_lines["Proof"] += int(stripped_cols[SPEC_COL])
            elif stripped_cols[FILE_COL] == "temporal_logic/rules.rs":
                tla_lemma_lines["Exec"] += int(stripped_cols[EXEC_COL])
                tla_lemma_lines["Exec"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                tla_lemma_lines["Proof"] += int(stripped_cols[PROOF_COL])
                tla_lemma_lines["Proof"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                tla_lemma_lines["Proof"] += int(stripped_cols[SPEC_COL])
            elif stripped_cols[FILE_COL] == "temporal_logic/defs.rs":
                tla_embedding_lines["Trusted"] += int(stripped_cols[EXEC_COL])
                tla_embedding_lines["Trusted"] += int(stripped_cols[PROOF_COL])
                tla_embedding_lines["Trusted"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                tla_embedding_lines["Trusted"] += int(stripped_cols[SPEC_COL])
            elif (
                "/proof/" in stripped_cols[FILE_COL]
                or stripped_cols[FILE_COL] == "vstd_ext/multiset_lib.rs"
                or stripped_cols[FILE_COL] == "vstd_ext/seq_lib.rs"
            ):
                k8s_lemma_lines["Exec"] += int(stripped_cols[EXEC_COL])
                k8s_lemma_lines["Exec"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                k8s_lemma_lines["Proof"] += int(stripped_cols[PROOF_COL])
                k8s_lemma_lines["Proof"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                k8s_lemma_lines["Proof"] += int(stripped_cols[SPEC_COL])
            elif "kubernetes_api_objects/spec" in stripped_cols[FILE_COL]:
                object_model_lines["Trusted"] += int(stripped_cols[EXEC_COL])
                object_model_lines["Trusted"] += int(stripped_cols[PROOF_COL])
                object_model_lines["Trusted"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                object_model_lines["Trusted"] += int(stripped_cols[SPEC_COL])
            elif "kubernetes_api_objects/exec" in stripped_cols[FILE_COL]:
                object_wrapper_lines["Trusted"] += int(stripped_cols[EXEC_COL])
                object_wrapper_lines["Trusted"] += int(stripped_cols[PROOF_COL])
                object_wrapper_lines["Trusted"] += int(
                    stripped_cols[PROOF_AND_EXEC_COL]
                )
                object_wrapper_lines["Trusted"] += int(stripped_cols[SPEC_COL])
            else:
                other_lines["Exec"] += int(stripped_cols[EXEC_COL])
                other_lines["Exec"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                other_lines["Trusted"] += int(stripped_cols[PROOF_COL])
                other_lines["Trusted"] += int(stripped_cols[PROOF_AND_EXEC_COL])
                other_lines["Trusted"] += int(stripped_cols[SPEC_COL])
    all_lines = {
        "test_lines": test_lines,
        "tla_embedding_lines": tla_embedding_lines,
        "tla_lemma_lines": tla_lemma_lines,
        "k8s_lemma_lines": k8s_lemma_lines,
        "object_model_lines": object_model_lines,
        "object_wrapper_lines": object_wrapper_lines,
        "other_lines": other_lines,
    }
    json.dump(all_lines, open("anvil-loc.json", "w"), indent=4)


def main():
    file_path = sys.argv[1]
    parse_table_and_collect_lines(file_path)


if __name__ == "__main__":
    main()
