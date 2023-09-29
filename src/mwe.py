import re
from typing import List


def parse_code(code: str, name: str) -> List[int]:
    """
    This function parses the code to find the start and end positions of the theorem and its proof.

    Args:
        code (str): The code to be parsed.
        name (str): The name of the theorem.

    Returns:
        list: A list containing the start position of the theorem,
        the start position of the proof, and the end position of the proof.
    """

    theorem_pattern = re.compile(r"\n.*theorem " + re.escape(name))
    match = theorem_pattern.search(code)
    if match is None:
        raise ValueError(f"Theorem {name} not found in code.")
    theorem_start = match.start()
    proof_start = code.find(":=", theorem_start) + 2
    lines = code[proof_start:].split("\n")
    proof_end = len(code)
    proof_code = ""
    for i, line in enumerate(lines):
        if i != 0 and not line.startswith(" "):
            proof_end = proof_start + len(proof_code)
            break
        proof_code += line + "\n"
    return [theorem_start, proof_start, proof_end]


class Mwe:
    ### Mwe class that defines the code which should be parsed or interacted with.
    ### Mwe stands for https://leanprover-community.github.io/mwe.html
    code: str
    name: str
    theorem_start: int
    proof_start: int
    proof_end: int

    def __init__(
        self,
        code: str,
        name: str,
    ):
        self.code = code
        self.name = name
        [self.theorem_start, self.proof_start, self.proof_end] = parse_code(code, name)

    def rewrite_to_tactic_style(self) -> None:
        """Rewrite the code to tactic style."""
        code = self.code
        # Rewrite the code in tactic style
        tactic_style_code = (
            code[: self.proof_start]
            + " by exact ("
            + code[self.proof_start : self.proof_end]
            + ")"
            + code[self.proof_end :]
        )
        self.proof_end += len(" by exact ()")
        self.code = tactic_style_code
