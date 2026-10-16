"""ANSI colors for the messages on a terminal; PLAIN leaves the text unchanged."""

import os
import sys
from typing import TextIO


class Palette:
    def __init__(self, enabled: bool):
        self.enabled = enabled

    def _paint(self, code: str, text: str) -> str:
        return f"\033[{code}m{text}\033[0m" if self.enabled and text else text

    def bold(self, text: str) -> str:
        return self._paint("1", text)

    def dim(self, text: str) -> str:
        return self._paint("2", text)

    def green(self, text: str) -> str:
        return self._paint("1;32", text)

    def red(self, text: str) -> str:
        return self._paint("1;31", text)

    def yellow(self, text: str) -> str:
        return self._paint("33", text)

    def magenta(self, text: str) -> str:
        return self._paint("1;35", text)

    def cyan(self, text: str) -> str:
        return self._paint("36", text)

    def status(self, status: str, text: str = "") -> str:
        """`text` (default: `status`) in the color of a verdict."""
        paint = {"valid": self.green, "invalid": self.red,
                 "error": self.magenta}.get(status, self.yellow)
        return paint(text or status)

    def groundtruth(self, check: str) -> str:
        """The comparison with the ground truth (Outcome.groundtruth_check)."""
        if check == "OK":
            return self.green(check)
        if check == "NOT OK":
            return self.red(check)
        if check.startswith("OK-"):
            return self.yellow(check)
        return self.dim(check)


PLAIN = Palette(False)


def palette(choice: str, stream: TextIO = sys.stdout) -> Palette:
    """choice: always, never, or auto (colors on a terminal, unless $NO_COLOR is set)."""
    if choice == "auto":
        return Palette(stream.isatty() and not os.environ.get("NO_COLOR")
                       and os.environ.get("TERM") != "dumb")
    return Palette(choice == "always")
