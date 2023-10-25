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
        "Impl": 0,
        "Liveness": 0,
        "Safety": 0,
        "Total": 0,
    }


def parse_json_and_collect_time(file_path, controller_name):
    verify_time = empty_counting_map()

    json_data = json.load(open(file_path, "r"))
    module_times = json_data["times-ms"]["total-verify-module-times"]
    for module_time in module_times:
        verify_time["Total"] += module_time["time"]
        if "::exec::" in module_time["module"]:
            verify_time["Impl"] += module_time["time"]
        elif "::proof::safety::" in module_time["module"]:
            verify_time["Safety"] += module_time["time"]
        else:
            verify_time["Liveness"] += module_time["time"]
    json.dump(verify_time, open(controller_name + "-time.json", "w"), indent=4)


def main():
    file_path = sys.argv[1]
    controller_name = sys.argv[2]
    parse_json_and_collect_time(file_path, controller_name)


if __name__ == "__main__":
    main()
