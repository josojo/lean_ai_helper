import os

from src.utils.lean_code_modifier import rewrite_all_proofs_in_tactic_style


if __name__ == "__main__":
    script_dir = os.path.dirname(os.path.realpath(__file__))
    file_path = os.path.join(
        script_dir,
        "../../tests/data/anomalie.2.lean",
    )
    file_path_new = os.path.join(
        script_dir,
        "../../tests/data/anomalie.2_rewrite.lean",
    )
    rewrite_all_proofs_in_tactic_style(file_path, file_path_new)
