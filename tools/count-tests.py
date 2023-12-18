import re
import os

def count_functions(file_path):
    # Regular expression patterns
    pattern_external_body = re.compile(r'#\[verifier\(external_body\)]\s*pub\s+fn')
    pattern_external_pub_fn = re.compile(r'#\[verifier\(external\)]\s*pub\s+fn')
    pattern_external_fn = re.compile(r'#\[verifier\(external\)]\s*fn')
    view_struct_pattern = re.compile(r'struct\s+View\b')

    # Reading the file
    with open(file_path, 'r') as file:
        file_contents = file.read()

    # Finding the position of the first 'View' struct
    view_struct_match = view_struct_pattern.search(file_contents)
    if view_struct_match:
        content_up_to_view_struct = file_contents[:view_struct_match.start()]
    else:
        content_up_to_view_struct = file_contents

    # Counting the occurrences
    count_external_body = len(pattern_external_body.findall(content_up_to_view_struct))
    count_external_pub_fn = len(pattern_external_pub_fn.findall(content_up_to_view_struct))
    count_external_fn = len(pattern_external_fn.findall(content_up_to_view_struct))

    # Returning the counts
    return count_external_body, count_external_pub_fn, count_external_fn

def count_test_functions(test_filename, test_directory_path='src/unit_tests/kubernetes_api_objects'):
    """Count test functions in the given file."""
    test_file_path = os.path.join(test_directory_path, test_filename)
    count = 0
    test_function_pattern = re.compile(r"pub fn test_")
    special_functions = {"test_marshal", "test_kube"}
    if os.path.isfile(test_file_path):
        with open(test_file_path, 'r') as file:
            content = file.read()
            matches = test_function_pattern.findall(content)
            count = len(matches)
            for special_function in special_functions:
                if special_function in content:
                    count += 1
    return count

def find_structs(file_path):
    """Find all struct names in the given file."""
    with open(file_path, 'r') as file:
        file_contents = file.read()

    struct_pattern = re.compile(r'pub struct\s+(\w+)\b')
    enum_pattern = re.compile(r'pub enum\s+(\w+)\b')
    all_structs = struct_pattern.findall(file_contents) + enum_pattern.findall(file_contents)

    # Exclude structs containing 'View' in their name
    return [s for s in all_structs if 'View' not in s]

def camel_to_snake(name):
    """Convert CamelCase to snake_case."""
    s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()

def main():
    api_directory_path = 'src/kubernetes_api_objects/exec'  # Update this path if needed
    test_directory_path = 'src/unit_tests/kubernetes_api_objects'
    flag = True
    for filename in sorted(os.listdir(api_directory_path)): # loop through all files in api_directory_path
        if filename.endswith('.rs'):
            file_path = os.path.join(api_directory_path, filename)
            structs = find_structs(file_path)
            if filename == 'api_method.rs':
                structs = ['ApiMethod']
            if filename == 'error.rs':
                structs = ['Error']
            test_count = 0
            struct_count = {}
            for struct_name in structs: # count every struct's test functions
                test_filename = f"{camel_to_snake(struct_name)}.rs"
                test_file_path = os.path.join(test_directory_path, test_filename)
                temp = count_test_functions(test_filename)
                test_count += temp
                struct_count[struct_name] = temp
            count_external_body, count_external_pub_fn, count_external_fn = count_functions(file_path)
            total_count = count_external_body + count_external_pub_fn + count_external_fn
            
            
            if total_count != test_count:
                flag = False
                print(f"{filename}: Total Count = {total_count}")
                print("Test Count = ", test_count)
                print("ERROR: Test Count != Total Count")
                print(struct_count)
                print("-------------------------------------------")
    if flag:
        print("All functions are covered!")
if __name__ == "__main__":
    main()
