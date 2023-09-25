import os
import shutil
import subprocess
from typing import Optional
from pathlib import Path
from loguru import logger


class ExecutionEnv:
    def __init__(self, tmp_dir: Optional[Path] = None) -> None:
        if tmp_dir is None:
            self.tmp_dir = Path(__file__).parent.parent.absolute() / "execution_env"
            logger.debug(f"Using default tmp_dir: {self.tmp_dir}")
        else:
            self.tmp_dir = tmp_dir

    def create_env(self) -> None:
        """Create a test environment for the proof."""

        # copy the content from common repl dir into the tmp dir
        if not os.path.exists(self.tmp_dir):
            logger.debug("Copying the content from submodule repl dir into the tmp dir")
            shutil.copytree(
                str(Path(__file__).parent.parent.parent.absolute() / "Lean4Repl"),
                str(self.tmp_dir) + "/",
                dirs_exist_ok=True,
            )
            os.chdir(self.tmp_dir)
            command = "lake exe cache get"
            subprocess.run(command.split(), check=True)
            command = "lake build Lean4Repl"
            subprocess.run(command.split(), check=True)
        else:
            logger.debug("Test environment exists. Skipping creation.")

    def write_main_file(self, code: str) -> None:
        # Interaction through tactics.
        repl_file = "Main.lean"
        repl_dst = self.tmp_dir / repl_file
        with repl_dst.open("wt") as oup:
            oup.write(code)
