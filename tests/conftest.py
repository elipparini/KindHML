import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "src"))


def pytest_addoption(parser):
    parser.addoption("--users", default="any",
                     help="the number of users of the regression tests (test_regressions.py): "
                          "any (every number of users, the default of the tool) or a number")
