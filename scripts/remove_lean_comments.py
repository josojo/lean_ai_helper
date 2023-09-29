import re


def remove_comments(filename):
    with open(filename, "r", encoding="utf-8") as file:
        lines = file.readlines()

    with open(filename, "w", encoding="utf-8") as file:
        for line in lines:
            stripped_line = line.lstrip()
            if not stripped_line.startswith("--"):
                file.write(line)


if __name__ == "__main__":
    remove_comments("tests/data/Mathlib.LinearAlgebra.EigenSpaces.Basic.lean")
