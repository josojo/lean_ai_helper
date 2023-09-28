from typing import List


def format_tatic_for_repl(proof: str) -> List[str]:
    if proof.startswith(" by\n"):
        proof = proof[5:]
    elif proof.startswith(" by"):
        proof = proof[3:]
    elif proof.startswith("by\n"):
        proof = proof[4:]
    elif proof.startswith("by"):
        proof = proof[2:]
    else:
        proof = "exact (" + proof + ")"
        return [proof]
    proof = proof.replace(";", "\n")
    proof_array = proof.split("\n")
    proof_array = [line for line in proof_array if line.strip() != ""]
    proof_array = undo_line_splits_for_unclosed_parenthesis(proof_array)
    proof_array = undo_line_splits_for_dot_notation(proof_array)
    return proof_array


def undo_line_splits_for_dot_notation(commands: List[str]) -> List[str]:
    """Undo line splits for unclosed parenthesis."""
    # iterate over the index of the commands
    i = 0
    while i <= len(commands) - 2:
        # check if the leading character after spaces is a dot
        if commands[i].strip().startswith("\u00b7"):
            # count the leading spaces
            num_spaces = len(commands[i]) - len(commands[i].lstrip())
            # check if the next line has more leading spaces
            if len(commands[i + 1]) - len(commands[i + 1].lstrip()) > num_spaces:
                # undo the line split
                commands[i] = commands[i] + "\n"
                commands[i] = commands[i] + commands[i + 1]
                commands.pop(i + 1)
                i -= 1
        i += 1

    return commands


def undo_line_splits_for_unclosed_parenthesis(commands: List[str]) -> List[str]:
    """Undo line splits for unclosed parenthesis."""
    opening_parenthesis = ["(", "{", "[", "\u27e8"]
    closing_parenthesis = [")", "}", "]", "\u27e9"]
    # iterate over the index of the commands
    i = 0
    while i <= len(commands) - 2:
        for opening, closing in zip(opening_parenthesis, closing_parenthesis):
            # count the number of opening and closing parenthesis
            num_opening = commands[i].count(opening)
            num_closing = commands[i].count(closing)
            if num_opening > num_closing:
                # undo the line split
                commands[i] = commands[i] + "\n"
                commands[i] = commands[i] + commands[i + 1]
                commands.pop(i + 1)
                i -= 1
        i += 1
    return commands
