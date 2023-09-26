import re
from typing import List
from loguru import logger


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
    logger.debug(f"lines: {lines[1:]}")
    proof_end = len(code)
    for i, line in enumerate(lines):
        # Skip the first line
        if i == 0:
            continue
        if not line.startswith(" "):
            proof_end = proof_start + i
            break
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
