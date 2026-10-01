from __future__ import annotations

from pathlib import Path

from feature_registry import load_registry

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]


def lint() -> None:
    registry = load_registry()
    for relation in registry["relations"]:
        if relation["authority"] != "PROVED_LEAN":
            continue
        source = REPO / relation["source_path"]
        if not source.is_file():
            raise SystemExit(f"missing Lean source for {relation['id']}: {source}")
        text = source.read_text(encoding="utf-8")
        declaration = relation["declaration"]
        if declaration not in text:
            raise SystemExit(
                f"declared Lean authority {declaration!r} not found for {relation['id']}"
            )
        if (
            relation["scope"] == "CANONICAL_ONLY"
            and "Source" not in relation["source_path"]
            and "Moment" not in relation["source_path"]
        ):
            raise SystemExit(
                f"canonical-only relation lacks source/moment provenance path: {relation['id']}"
            )

    for relation in registry.get("paper_relations", []):
        if relation["authority"] != "PAPER_DERIVED_NOT_LEAN":
            raise SystemExit("paper relation authority drift")

    print("contact quotient source-authority lint: PASS")


if __name__ == "__main__":
    lint()
