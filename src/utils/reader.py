import os

from pathlib import Path
from typing import List, Tuple
from src.mwe import Mwe
from src.trace.trace import TracedTacticState, Tracer


def get_objects_for_theorem(
    theorem_name: str, code: str, tracing_res_path: Path, iteration: int = 0
) -> Tuple[Mwe, List[TracedTacticState]]:
    mwe = Mwe(
        code,
        theorem_name,
        iteration,
    )
    tracer = Tracer(mwe)
    tracer.load_trace_result(tracing_res_path)
    # Get tactics
    assert tracer.tracing_result is not None
    tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)
    return mwe, tactics


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
