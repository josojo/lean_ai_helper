from pathlib import Path
from typing import Tuple


def get_folder_and_path_from_path(path: Path) -> Tuple[Path, str]:
    foldername = path.parts[-1]
    path = Path("/".join(path.parts[:-1]))
    return path, foldername
