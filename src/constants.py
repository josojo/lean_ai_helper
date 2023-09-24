import os
import sys
from loguru import logger
from dotenv import load_dotenv

load_dotenv()

logger.remove()
if "VERBOSE" in os.environ or "DEBUG" in os.environ:
    logger.add(sys.stderr, level="DEBUG")
else:
    logger.add(sys.stderr, level="INFO")
