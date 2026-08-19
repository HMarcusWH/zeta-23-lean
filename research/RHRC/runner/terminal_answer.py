from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class FinalAnswer:
    terminal_question: str
    answer_code: str
    answer: str
    mathematical_status: str
    certificate_status: str
    research_signal: str
    legal_claim: str
    blockers: tuple[str, ...]
    evidence_receipts: tuple[str, ...]
    theorem_authority: str = "Lean/comparator"


def load_json(path: Path) -> Any:
    return json.loads(path.read_text())


def derive_answer(claim_registry: Path, receipts: list[Path]) -> FinalAnswer:
    registry = load_json(claim_registry)
    claims = {c['id']: c for c in registry['claims']}
    terminal = claims['C_RH']
    receipt_rows = []
    valid_diagnostic_pass = False
    invalid_receipt = False
    for p in receipts:
        if not p.exists():
            continue
        r = load_json(p)
        receipt_rows.append(str(p))
        bounded = r.get('bounded_claim') or r.get('bounded_discovery_claim') or {}
        cert = bounded.get('certificate_status')
        result = bounded.get('result')
        if cert == 'INVALID':
            invalid_receipt = True
        if cert == 'VALID' and result == 'PASS':
            valid_diagnostic_pass = True

    blockers = tuple(d for d in terminal.get('dependencies', []) if claims.get(d, {}).get('status') != 'PROVED_UNCONDITIONAL')

    if invalid_receipt:
        return FinalAnswer(
            terminal_question=terminal['statement'], answer_code='INVALID_EVIDENCE',
            answer='No mathematical answer may be issued because a claim-bearing evidence receipt is INVALID.',
            mathematical_status=terminal['status'], certificate_status='INVALID', research_signal='BLOCKED',
            legal_claim='INVALID evidence cannot support promotion.', blockers=blockers, evidence_receipts=tuple(receipt_rows))

    if terminal['status'] == 'PROVED_UNCONDITIONAL' and not blockers:
        return FinalAnswer(
            terminal_question=terminal['statement'], answer_code='RH_PROVED_TRUE', answer='TRUE',
            mathematical_status='PROVED_UNCONDITIONAL', certificate_status='VALID', research_signal='CLOSED',
            legal_claim='RH is proved within the audited unconditional theorem chain.', blockers=(), evidence_receipts=tuple(receipt_rows))

    if terminal['status'] == 'REFUTED':
        return FinalAnswer(
            terminal_question=terminal['statement'], answer_code='RH_REFUTED', answer='FALSE',
            mathematical_status='REFUTED', certificate_status='VALID', research_signal='CLOSED',
            legal_claim='RH is refuted by an audited mathematical counterexample/proof.', blockers=(), evidence_receipts=tuple(receipt_rows))

    signal = 'FINITE_DIAGNOSTIC_PASS' if valid_diagnostic_pass else 'NO_PROMOTABLE_SIGNAL'
    return FinalAnswer(
        terminal_question=terminal['statement'], answer_code='RH_OPEN', answer='OPEN / NOT ESTABLISHED',
        mathematical_status=terminal['status'], certificate_status='VALID' if valid_diagnostic_pass else 'INCOMPLETE',
        research_signal=signal,
        legal_claim='No proof or refutation of RH. Finite numerical/synthetic diagnostics may guide proof search but cannot promote the theorem.',
        blockers=blockers, evidence_receipts=tuple(receipt_rows))


def render_text(ans: FinalAnswer) -> str:
    lines = [
        '===== RHRC FINISHED ANSWER =====',
        f'QUESTION: {ans.terminal_question}',
        f'ANSWER: {ans.answer}',
        f'ANSWER_CODE: {ans.answer_code}',
        f'MATHEMATICAL_STATUS: {ans.mathematical_status}',
        f'CERTIFICATE_STATUS: {ans.certificate_status}',
        f'RESEARCH_SIGNAL: {ans.research_signal}',
        f'THEOREM_AUTHORITY: {ans.theorem_authority}',
        f'LEGAL_CLAIM: {ans.legal_claim}',
        'BLOCKERS: ' + (', '.join(ans.blockers) if ans.blockers else 'NONE'),
        '===============================',
    ]
    return '\n'.join(lines) + '\n'


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--claim-registry', type=Path, default=ROOT/'CLAIM_REGISTRY.json')
    ap.add_argument('--receipt', type=Path, action='append', default=[])
    ap.add_argument('--output-dir', type=Path, required=True)
    args = ap.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    ans = derive_answer(args.claim_registry, args.receipt)
    (args.output_dir/'FINAL_ANSWER.json').write_text(json.dumps(asdict(ans), indent=2))
    txt = render_text(ans)
    (args.output_dir/'FINAL_ANSWER.txt').write_text(txt)
    print(txt, end='')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
