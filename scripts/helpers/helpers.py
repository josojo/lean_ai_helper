from ast import Tuple
from pathlib import Path
from typing import List
from src.mwe import Mwe
from src.trace.trace import TracedTacticState, Tracer


def get_objects_for_theorem(
    theorem_name: str, code: str, tracing_res_path: Path, iteration: int = 0
) -> Tuple(Mwe, List[TracedTacticState]):
    mwe = Mwe(
        code,
        theorem_name,
        thm_iteration=iteration,
    )
    tracer = Tracer(mwe)
    tracer.load_trace_result(tracing_res_path)
    # Get tactics
    tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)
    return mwe, tactics
