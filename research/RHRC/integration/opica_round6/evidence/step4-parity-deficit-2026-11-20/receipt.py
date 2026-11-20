"""Compare a finite replay with its committed result before exporting fresh bytes."""

import argparse
import json
from pathlib import Path


def replay(filename, calculate):
    parser = argparse.ArgumentParser(description=calculate.__doc__)
    outputs = parser.add_mutually_exclusive_group()
    outputs.add_argument("--write", action="store_true", help="regenerate the committed result")
    outputs.add_argument("--output", type=Path, help="export the verified calculation to this file")
    args = parser.parse_args()
    expected = Path(__file__).with_name(filename)
    data = (json.dumps(calculate(), indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    if args.write:
        expected.write_bytes(data)
    if expected.read_bytes() != data:
        raise SystemExit(f"Finite replay differs from {expected.name}")
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(data)
    print(f"Verified {filename}")
