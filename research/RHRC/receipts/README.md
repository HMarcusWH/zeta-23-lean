# Evidence receipts

RHRC receipts follow the domain-neutral operational semantics transplanted from **OoL-MVS Kernel v2.7.6**.

The evidence path is intentionally layered:

```text
raw EvidenceReceipt
  -> authorized leaf/relation evaluation
  -> claim evaluation (PASS / FAIL / NA)
  -> evidence bundle bound to exact support
  -> ClaimCertificate (VALID / INCOMPLETE / INVALID)
```

`ClaimResult` and certificate integrity are separate. A well-supported negative result may therefore be `FAIL + VALID`. Missing or unresolved evidence remains `NA`; it is not silently converted to `FAIL`. Unknown provenance is not admitted provenance, and an absence/clean-ancestry result requires a sufficiently complete declared search domain.

Each confirmatory research result must record source hashes, config, seed(s), split, null family, ablations, transfer tests, commutation check, claim cap, exact code revision, route specification digest, boundary digest, evidence/support references, and evaluation mode. Claim-bearing changes after result/lockbox exposure require a new route digest and fresh confirmatory execution.

Receipts certify what was run and how the research claim was evaluated. They do **not** certify a mathematical theorem; theorem authority remains Lean/comparator.

Schemas:

- `../schemas/evidence_receipt.schema.json`
- `../schemas/claim_certificate.schema.json`
