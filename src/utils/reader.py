import os

from pathlib import Path


def read_code_from_file(data_path: Path) -> str:
    code = ""
    # Get the absolute path to the directory of the current script
    script_dir = os.path.dirname(os.path.realpath(__file__))

    # Join the script directory with the relative path to the file
    root_dir = os.path.join(script_dir, "../../")
    file_path = os.path.join(root_dir, data_path)

    # Open the file using the absolute path
    with open(file_path, "r", encoding="utf-8") as file:
        code = file.read()

    return code
