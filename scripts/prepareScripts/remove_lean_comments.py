from src.utils.lean_code_modifier import remove_comments_from_lean_file

if __name__ == "__main__":
    remove_comments_from_lean_file(
        "tests/data/Mathlib.LinearAlgebra.EigenSpaces.Basic.lean"
    )
