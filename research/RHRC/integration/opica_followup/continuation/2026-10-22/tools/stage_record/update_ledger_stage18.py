# Worked example from Stage 18 (copy into your scratch directory and adapt; see README.md here).
# Paths come from OPICA_REPO (repository root) and OPICA_SCRATCH (scratch directory).
import hashlib, json
from pathlib import Path
import os
REPO = Path(os.environ.get('OPICA_REPO', '/home/user/zeta-23-lean'))
C = REPO/'research/RHRC/integration/opica_followup/continuation/2026-10-22'
p = C/'ROOT_LEDGER_100.json'
d = json.loads(p.read_bytes())
sha = lambda q: hashlib.sha256(q.read_bytes()).hexdigest()
path = 'Zeta23/OPICAFollowup/CoPoissonJets.lean'
src = sha(REPO/path)
ev = 'evidence/current-codex/stage18/STATUS.json'
cons = 'consumers/ExpectedCoPoissonJets.lean'
info = {
 'copoisson_zero_jets_measures': (
   'PASS_ACTUAL_ZERO_ORDER_ZERO_JET_IS_CP1_MEASURE_K0_CHAIN_IS_FORCED_EULER_REFLECTION_SAME_NODE',
   'zeroJetOrder rho := analyticOrderNatAt riemannZeta rho; normalizedZeroMeasureJet rho k := the CP1 zeroMeasure at '
   'k = 0, and the canonical-Jordan density measure of (1/k!) d^k/dkappa^k g_kappa(|x|) at kappa0 = rho(1 - rho) for '
   'k >= 1, with g_kappa the entire kappa-family kappa sum_(1 <= k <= |y|) (e^(-u/2)/k) Sh(1/4 - kappa, u) of the '
   'actual finite sums (equal to S_rho(|y|)/b_rho for every strip rho != 1/2). For an actual zero with 0 < Re rho < 1 '
   'and every k < m: m >= 1 is the analytic order; the local inverse rho(kappa) is holomorphic at kappa0 with '
   'derivative -1/(2rho - 1) and zeta o rho(.) has order m; on Schwartz tests nu_k is (1/k!) d^k/dkappa^k of the actual '
   'construction (CP1.7)/b along rho(kappa), explicitly int g_k phi - [k = 0] sum_(n != 0) phi(n) (H1.1); exact open '
   'unit gap, zero origin atom, even Jordan parts, linear variation growth; jet densities [k = 0] - ([k = 0] kappa0 + '
   '[k = 1]) B2({|x|})/(2x^2) + O(|x|^-3); Fourier self-duality on Schwartz tests and as tempered distributions, also '
   'for the real part; the differentiated forced chain (H1.2) (L - kappa0) h0 = kappa0 G, (L - kappa0) h1 = h0 + G, '
   '(L - kappa0) hk = h(k-1) on positive-axis tests; 1 - rho has the same multiplicity, node and jets; conj rho has '
   'the same multiplicity and nu_k(conj rho)(phi) = conj(nu_k(rho)(conj phi)). Recorded choice: the measure is defined '
   'from the kappa-jet of the density and identified with the parameter jets of the actual construction by theorem.'),
}
for r in d['roots']:
    if r['path'] != path:
        continue
    name = r['full_name'].split('.')[-1]
    dom, text = info[name]
    r['current_status'] = 'PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING'
    r['gates'] = {
        'implementation': 'IMPLEMENTED_FULL_FROZEN_CONTRACT_REVIEWED_NARROW',
        'module_compilation': 'PASS_EXACT_COMMITTED_SOURCE_PINNED_LINUX',
        'expected_type_consumer': 'PASS_INDEPENDENT_FULL_TYPE_AND_DEFINITION_AUDITS',
        'actual_domain_consumer': dom,
        'axiom_check': 'STANDARD_ONLY_TRANSITIVE_PRINTED_CLOSURES',
        'aggregate_current_source_export': 'OPEN',
        'full_release_acceptance': 'OPEN'}
    r['source_file_present'] = True
    r['declaration_lexically_present'] = True
    r['source_sha256'] = src
    r['evidence'] = [ev]
    r['independent_consumer'] = {'path': cons, 'sha256': sha(C/cons)}
    r['statement_formalization'] = text
counts = {}
for r in d['roots']:
    counts[r['current_status']] = counts.get(r['current_status'], 0) + 1
d['status_counts'] = dict(sorted(counts.items()))
vs = d['verification_summary']
narrow = counts['PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING']
absent = counts['OPEN_NO_COMPLETE_CANDIDATE']
assert narrow == 49 and absent == 10, (narrow, absent)
vs['independently_verified_narrow_roots'] = narrow
vs['open_no_complete_candidate_roots'] = absent
vs['receipt'] = 'STAGE18_HANDOVER.md'
vs['meaning'] = ('41 historical plus 49 narrow local results is not aggregate 90-root acceptance. 10 absent '
    'implementations plus all remaining domain/integration gates remain OPEN; original100/28 scope unchanged.')
vs['receipt_scope'] = ('Index of one Stage18, two Stage17, four Stage16, three Stage15, two Stage14, three Stage13, two Stage12, two Stage11, two Stage10, two Stage9, one Stage8, three Stage7, three Stage6, two Stage5, two '
    'Stage4 and fifteen retained narrow original-root results, not an aggregate receipt')
vs['additional_stage18_primary_roots'] = ['copoisson_zero_jets_measures']
out = json.dumps(d, indent=2, ensure_ascii=True) + '\n'
p.write_bytes(out.replace('\n', '\r\n').encode())
print(d['status_counts'])
