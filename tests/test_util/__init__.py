import sys

from io import StringIO
from typing import Generator
from contextlib import contextmanager


@contextmanager
def CaptureStdout() -> Generator[StringIO, None, None]:
    save_stdout = sys.stdout
    out = StringIO()
    sys.stdout = out
    yield out
    sys.stdout = save_stdout
