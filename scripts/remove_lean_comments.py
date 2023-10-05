def remove_comments(filename):
    with open(filename, "r", encoding="utf-8") as file:
        lines = file.readlines()

    is_comment = False
    with open(filename, "w", encoding="utf-8") as file:
        for line in lines:
            stripped_line = line.lstrip()
            if stripped_line.startswith("/--"):
                is_comment = True
            if not stripped_line.startswith("--") and not is_comment:
                file.write(line)
            if is_comment and stripped_line.find("-/") != -1:
                is_comment = False


if __name__ == "__main__":
    remove_comments("tests/data/Mathlib.LinearAlgebra.EigenSpaces.Basic.lean")
