from __future__ import annotations

from pathlib import Path

from control_v2.retro.git_history import reachable_commits
from control_v2.retro.schemas import RetroSearchReceipt
from control_v2.retro.search import search_concept


class HistoricalLeakageError(RuntimeError):
    pass


def assert_receipt_as_of(repo_root: Path, receipt: RetroSearchReceipt) -> None:
    if receipt.as_of_ref is None:
        return
    allowed = reachable_commits(repo_root, receipt.as_of_ref)
    allowed.add(receipt.as_of_ref)
    for hit in receipt.hits:
        if hit.source_commit is not None and hit.source_commit not in allowed:
            raise HistoricalLeakageError(
                f"retro replay leaked future commit {hit.source_commit} for {hit.source_path}"
            )


def replay_concept(*, repo_root: Path, concept_id: str, as_of_ref: str,
                   archive_root: Path | None = None) -> RetroSearchReceipt:
    receipt = search_concept(
        repo_root=repo_root,
        concept_id=concept_id,
        as_of_ref=as_of_ref,
        archive_root=archive_root,
        mode="COUNTERFACTUAL_REPLAY",
    )
    assert_receipt_as_of(repo_root, receipt)
    return receipt
