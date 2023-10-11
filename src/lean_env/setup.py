from collections import deque
import os
from pathlib import Path
from typing import Any, Dict, List, Protocol
import ray
from src.logger_config import logger


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
        for argument in args:
            logger.debug(f"argument: {argument}")
            logger.debug(f"execution_envs_queue: {self.execution_envs_queue}")
            logger.debug(f"futures: {self.execution_envs}")
            # Wait for an available folder
            while not self.execution_envs_queue:
                # Check for completed tasks
                ready_ids, _ = ray.wait(list(futures.keys()), num_returns=1, timeout=0)

                for done_id in ready_ids:
                    # Retrieve the result, free up the folder, and remove from tracking dict
                    result = ray.get(done_id)
                    results.append(result)
                    self.execution_envs_queue.append(futures.pop(done_id))

            # Start a task with an available folder
            env = self.execution_envs_queue.popleft()
            logger.debug(f"env: {env}")
            logger.debug(f"argument: {argument}")
            future = exec_function.remote(argument, env, self.output_dir)
            futures[future] = env

        # Wait for all remaining tasks to finish
        results.extend(ray.get(list(futures.keys())))
        return results

    def __exit__(self, exc_type: None, exc_val: None, exc_tb: None) -> None:
        ray.shutdown()
