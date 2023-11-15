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

def count_test_functions(file_path):
    """Count test functions in the given file."""
    with open(file_path, 'r') as file:
        file_contents = file.read()

    test_function_pattern = re.compile(r'fn test\w*\(')
    return len(test_function_pattern.findall(file_contents))

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
    api_directory_path = 'src/kubernetes_api_objects'  # Update this path if needed
    test_directory_path = 'src/unit_tests/kubernetes_api_objects'
    for filename in sorted(os.listdir(api_directory_path)):
        if filename.endswith('.rs'):
            file_path = os.path.join(api_directory_path, filename)
            structs = find_structs(file_path)
            if filename == 'api_method.rs':
                structs = ['ApiMethod']
            if filename == 'error.rs':
                structs = ['Error']
            # print(f"\n{filename}: {structs}")
            for struct_name in structs:
                test_filename = f"{camel_to_snake(struct_name)}.rs"
                test_file_path = os.path.join(test_directory_path, test_filename)
            count_external_body, count_external_pub_fn, count_external_fn = count_functions(file_path)
            total_count = count_external_body + count_external_pub_fn + count_external_fn
            if not os.path.exists(test_file_path) and total_count > 0:
                # test_count = count_test_functions(test_file_path)
                print(f"\nThis file can not be found:{test_filename}\n")

            # print(f"{filename}: Total Count = {total_count}")

if __name__ == "__main__":
    main()
