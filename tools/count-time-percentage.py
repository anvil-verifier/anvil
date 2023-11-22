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


def parse_json_and_collect_time():
    all_times = []
    for app in ["zookeeper", "rabbitmq", "fluent"]:
        file_path = "{}.json".format(app)
        json_data = json.load(open(file_path, "r"))
        module_times = json_data["times-ms"]["smt"]["smt-run-module-times"]
        for module in module_times:
            function_times = module["function-breakdown"]
            for function in function_times:
                time = function["time"]
                all_times.append(time)
    print(len(all_times))
    all_times.sort()
    for idx, time in enumerate(all_times):
        if time > 10000:
            print(idx)
            break
    print(all_times[-1])


def main():
    parse_json_and_collect_time()


if __name__ == "__main__":
    main()
