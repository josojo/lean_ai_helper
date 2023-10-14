from collections import deque
import os
from pathlib import Path
from typing import Any, Dict, List, Protocol
import ray
from loguru import logger


class RayRemoteProtocol(Protocol):
    def remote(self, *args: Any, **kwargs: Any) -> Any:
        ...


class ParallelExecutor:
    def __init__(self, num_cpus: int) -> None:
        ray.init(num_cpus=num_cpus)
        self.execution_envs = [Path(f"execution_env_{i}") for i in range(num_cpus)]
        for folder in self.execution_envs:
            os.makedirs(folder, exist_ok=True)
        # Create a queue for folders
        self.execution_envs_queue = deque(self.execution_envs)
        self.output_dir = Path(__file__).parent.parent.parent.absolute() / "output.json"

    def run(self, exec_function: RayRemoteProtocol, args: List[Any]) -> List[Any]:
        results = []
        futures: Dict[Any, Path] = {}
        length_of_files = len(args)
        for cnt, argument in enumerate(args):
            logger.info(f"Running the function with the file: {argument}")
            logger.info(f"Progress: {cnt}/{length_of_files}")
            # Wait for an available folder
            while not self.execution_envs_queue:
                # Check for completed tasks
                ready_ids, _ = ray.wait(list(futures.keys()), num_returns=1, timeout=0)

                for done_id in ready_ids:
                    # Retrieve the result, free up the folder, and remove from tracking dict
                    try:
                        result = ray.get(done_id)
                        results.append(result)
                    except Exception as e:  # pylint: disable=broad-except
                        logger.error(
                            f"Exception: {e} for running the function with the file: {argument}"
                        )
                    self.execution_envs_queue.append(futures.pop(done_id))

            # Start a task with an available folder
            env = self.execution_envs_queue.popleft()
            future = exec_function.remote(argument, env, self.output_dir)
            futures[future] = env

        # Wait for all remaining tasks to finish
        results.extend(ray.get(list(futures.keys())))
        return results

    def __exit__(self, exc_type: None, exc_val: None, exc_tb: None) -> None:
        ray.shutdown()
