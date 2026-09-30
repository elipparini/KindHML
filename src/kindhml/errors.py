"""Errors reported to the user (syntax and type errors)."""

from typing import Optional


class KindHMLError(Exception):
    def __init__(self, message: str, pos: Optional[object] = None):
        self.message = message
        self.pos = pos
        super().__init__(f"{message} ({pos})" if pos else message)
