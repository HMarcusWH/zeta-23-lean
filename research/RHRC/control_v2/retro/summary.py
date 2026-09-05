from __future__ import annotations

from collections import Counter

from control_v2.retro.schemas import RetroSearchReceipt


def summarize_receipt(receipt: RetroSearchReceipt, *, top_k: int = 8) -> dict:
    term_counts = Counter(hit.term for hit in receipt.hits)
    path_counts = Counter(hit.source_path for hit in receipt.hits)
    family_counts = Counter(hit.source_family for hit in receipt.hits)
    unique_lines = {
        (hit.source_family, hit.source_path, hit.excerpt.casefold())
        for hit in receipt.hits
    }
    return {
        "receipt_id": receipt.receipt_id,
        "hit_count": len(receipt.hits),
        "unique_clue_lines": len(unique_lines),
        "search_scope": receipt.search_scope,
        "search_complete": receipt.search_complete,
        "top_terms": term_counts.most_common(top_k),
        "top_paths": path_counts.most_common(top_k),
        "source_families": sorted(family_counts.items()),
    }
