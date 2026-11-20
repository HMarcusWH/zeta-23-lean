"""Replay finite examples against their committed receipts and source generator."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
from types import ModuleType

HERE = Path(__file__).resolve().parent
GENERATOR = HERE.parents[1] / "cone_parity.py"
GENERATOR_SHA256 = "d2927aa38f97ee77229c7d8e9b782d549975bba6fd1a7acb9c895d0da709cec7"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def native():
    source = GENERATOR.read_bytes()
    require(sha256(source).hexdigest() == GENERATOR_SHA256, "Native cone generator differs")
    module = ModuleType("native_cone")
    module.__file__ = str(GENERATOR)
    exec(compile(source, str(GENERATOR), "exec"), module.__dict__)
    return module


def replay(filename, calculate, *, sort_keys=True):
    parser = argparse.ArgumentParser(description=calculate.__doc__)
    dest = parser.add_mutually_exclusive_group()
    dest.add_argument("--write", action="store_true", help="regenerate the committed result")
    dest.add_argument("--output", type=Path, help="export the verified calculation to this file")
    args = parser.parse_args()
    data = (json.dumps(calculate(), indent=2, sort_keys=sort_keys) + "\n").encode("utf-8")
    expected = HERE / filename
    if args.write:
        expected.write_bytes(data)
    require(expected.read_bytes() == data, "Finite replay differs from " + filename)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(data)
    print("Verified " + filename)
