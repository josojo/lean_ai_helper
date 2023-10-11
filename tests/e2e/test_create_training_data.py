import json
import os
from typing import List
from pathlib import Path
import ray
import pytest

from src.generate.training_data import (
    close_array_in_output_file,
    generate_training_data,
    initate_array_in_output_file,
)
from src.lean_env.setup import ParallelExecutor


@pytest.fixture(scope="module")
def ray_fix():
    ray.init(num_cpus=1)
    yield None
    ray.shutdown()


def test_extracted_theorem_interaction_in_gym() -> None:

    executor = ParallelExecutor(1)

    references_to_test_data = [
        "../../tests/data/Mathlib.Data.Set.Finite.lean",
    ]
    script_dir = os.path.dirname(os.path.realpath(__file__))

    files_to_investigate: List[Path] = []
    for file_path in references_to_test_data:
        files_to_investigate.append(
            Path(
                os.path.normpath(
                    os.path.join(
                        script_dir,
                        file_path,
                    )
                )
            )
        )
    output_file = Path(
        os.path.join(
            script_dir,
            "../../output.json",
        )
    )
    initate_array_in_output_file(output_file)
    executor.run(generate_training_data, files_to_investigate)
    close_array_in_output_file(output_file)

    # read the output file as json
    with open(output_file, "r", encoding="utf-8") as file:
        output = json.load(file)

    assert output[0]["theorem_name"] == "Finite.exists_finset"
    assert json.dumps(output[0]["tactics"], sort_keys=True) == json.dumps(
        json.loads(
            '[ \
                {"syntax": "  cases h", "premises": []}, \
                {"syntax": "  exact \u27e8s.toFinset, fun _ => mem_toFinset\u27e9",\
                "premises": ["Exists.intro", "Set.toFinset", "Set.mem_toFinset"]}]'
        ),
        sort_keys=True,
    )
    assert output[0]["defintions"] == [
        "Set",
        "Set.Finite",
        "Exists",
        "Finset",
        "Iff",
        "Membership.mem",
        "Set.Finite.exists_finset",
    ]
    #     json.loads(
    #         '{"theorem_name":, \
    #         "file_path": \
    #             "/tests/data/Mathlib.Data.Set.Finite.lean", \
    #         "tactics":  \
    #         "defintions": ["Set", "Set.Finite", "Exists", \
    #         "Finset", "Iff", "Membership.mem", "Set.Finite.exists_finset"]}'
    #     ),
    #     sort_keys=True,
    # )
    assert len(output) == 25
