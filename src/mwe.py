import re
from typing import List


def all_brackets_closed(code: str) -> bool:
    opening_parenthesis = ["(", "{", "[", "\u27e8"]
    closing_parenthesis = [")", "}", "]", "\u27e9"]
    # iterate over the index of the commands
    for opening, closing in zip(opening_parenthesis, closing_parenthesis):
        # count the number of opening and closing parenthesis
        num_opening = code.count(opening)
        num_closing = code.count(closing)
        if num_opening > num_closing:
            return False
    return True


class UnusualTheoremFormatError(Exception):
    pass


def get_theorem_positions(code: str, name: str, thm_iteration: int = 0) -> List[int]:
    """
    This function parses the code to find the start and end positions of the theorem and its proof.
    Since the name is not a unique identifier, one can also hand in an thm_iteration
    to specify which theorem with the same name should be parsed.

    Args:
        code (str): The code to be parsed.
        name (str): The name of the theorem.
        thm_iteration (int, optional): The iteration of the theorem. Defaults to 0.

    Returns:
        list: A list containing the start position of the theorem,
        the start position of the proof, and the end position of the proof.
    """
    theorem_pattern = re.compile(
        r"\n(?:protected |private |nonrec )?theorem " + re.escape(name)
    )
    match = theorem_pattern.search(code)
    for _ in range(thm_iteration):
        if match is None:
            raise ValueError(
                f"Theorem {name} iteration {thm_iteration} not found in code."
            )
        match = theorem_pattern.search(code, match.end())

    if match is None:
        raise ValueError(f"Theorem {name} not found in code.")
    theorem_start = match.start() + 1
    proof_start = code.find(":=", theorem_start) + 2
    theorem_code = code[theorem_start:proof_start].split("\n")
    for i, line in enumerate(theorem_code):
        if i == 0:
            continue
        if len(line.lstrip()) + 2 >= len(line):
            raise UnusualTheoremFormatError(
                f"Theorem {name} is not according to the standard format with =:"
            )
    while not all_brackets_closed(code[theorem_start:proof_start]):
        proof_start = code.find(":=", proof_start) + 2
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
        thm_iteration: int = 0,
    ):
        self.code = code
        self.name = name
        [self.theorem_start, self.proof_start, self.proof_end] = get_theorem_positions(
            code, name, thm_iteration
        )

    def rewrite_to_tactic_style(self) -> None:
        """Rewrite the code to tactic style."""
        code = self.code
        if code[self.proof_start : self.proof_end].strip().startswith("by"):
            return
        if code[self.proof_start : self.proof_end].strip().startswith("|"):
            return
        # Rewrite the code in tactic style
        tactic_style_code = (
            code[: self.proof_start]
            + " by exact ("
            + code[self.proof_start : self.proof_end - 1]
            + ")\n"
            + code[self.proof_end :]
        )
        self.proof_end += len(" by exact ()")
        self.code = tactic_style_code

    def rewrite_expand_rw(self) -> None:
        """expands all rw commands in the proof of the theorem."""
        code = self.code

        rw_code = code[self.proof_start : self.proof_end]
        initial_length = len(rw_code)
        print(initial_length)
        rw_code = rewrite_code_with_expanded_rw(rw_code)
        final_length = len(rw_code)
        print(final_length)
        self.proof_end += final_length - initial_length
        self.code = code[: self.proof_start] + rw_code + code[self.proof_end :]


def rewrite_code_with_expanded_rw(input_string: str) -> str:
    # Define the regular expression pattern to match the content inside the square brackets
    pattern = r"rw\s*\[([^]]*)\]"

    # Use findall to extract the content within the brackets
    matches = re.findall(pattern, input_string)

    print(matches)
    reformatted_string = ""

    # If matches were found, process them
    for match in matches:
        # Split the matches by comma and strip any surrounding whitespace
        elements = [elem.strip() for elem in match.split(",")]

        # Format the new string
        reformatted_string = "; ".join(f"rw [{elem}]" for elem in elements)
        input_string = input_string.replace(f"rw [{match}]", reformatted_string)
    print(input_string)
    return input_string
