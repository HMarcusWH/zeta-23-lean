# Worked example from Stage 18 (copy into your scratch directory and adapt; see README.md here).
# Paths come from OPICA_REPO (repository root) and OPICA_SCRATCH (scratch directory).
import hashlib, json, sys
from pathlib import Path
import os
REPO = Path(os.environ.get('OPICA_REPO', '/home/user/zeta-23-lean'))
C = REPO/'research/RHRC/integration/opica_followup/continuation/2026-10-22'
E = C/'evidence/current-codex/stage18'
S = Path(os.environ.get('OPICA_SCRATCH', '/tmp/opica-scratch'))/'stage18-final'
sha = lambda q: hashlib.sha256(Path(q).read_bytes()).hexdigest()
head, tree = (S/'head.txt').read_text().split()
res = json.loads((E/'runner/CHECK_RESULT.json').read_text())
assert res['status'] == 'PASS_NARROW_ONLY' and res['head'] == head and res['dirty_status'] == ''
assert res['source_unchanged'] is True and len(res['consumers']) == 25
srcs = ['Zeta23/OPICAFollowup/CoPoissonJets.lean',
        str((C/'consumers/ExpectedCoPoissonJets.lean').relative_to(REPO)),
        str((C/'run_candidate_checks.py').relative_to(REPO)),
        '.github/workflows/rhrc_opica_followup.yml', 'lean-toolchain', 'lake-manifest.json']
neg = ('REJECTED (10 errors, exit 1): jets claimed at k <= m; the order-zero jet without the punctured lattice; the B2 tail '
       'with a plus sign; the tail rate |y|^(-4); the first differentiated equation without its source G; the branch derivative '
       '+1/(2rho - 1); the reflected zero as a separate node; the reflected multiplicity m + 1; the conjugate relation without '
       'conjugating the test; the root without the strip condition 0 < Re rho')
status = {
 'schema': 'OPICA_STAGE18_NARROW_GATE_V1',
 'status': 'PASS_NARROW_LOCAL_GATES_ONLY_AGGREGATE_AND_FULL_RELEASE_OPEN',
 'checked_commit': head, 'checked_tree': tree, 'dirty_status_during_checks': '',
 'compiler': 'Lean 4.33.0-rc2 commit d8b18978322de05a8f3dba51ef03cf5461676c17 (Linux x86_64), Lake 5.0.0-src+d8b1897',
 'mathlib': '51e6992efd06126df61a496bebf8f49482a4e129 (pins unchanged; no lake update)',
 'new_module': {
   'module': 'Zeta23.OPICAFollowup.CoPoissonJets',
   'project_imports': ['Zeta23.OPICAFollowup.ZeroProfiles'],
   'mathlib_imports': ['Mathlib.Analysis.SpecialFunctions.Trigonometric.Series'],
   'authority': 'BUILD_MANIFEST direct_project_imports of this module is exactly [ZeroProfiles]',
   'required_definitions': ['normalizedZeroMeasureJet', 'zeroJetOrder'],
   'new_definitions': ['shKernel', 'zeroFamilyDensity', 'zeroLocalInverse', 'localRadicand', 'localJetDomain',
                       'zeroJetOrder', 'zetaFunctionalFactor', 'zeroJetDensity', 'boundaryMellinPairing',
                       'zeroFamilyFunctional', 'jetPowerTerms', 'jetTailRemainder', 'jetDensityMeasure',
                       'normalizedZeroMeasureJet', 'zeroJetProfile'],
   'reproduced_identity': ('the Stage 11 forced Euler identity is reproduced under the CoPoissonJets namespace from the same '
                           'ZeroProfiles cell lemmas, because the module may import only ZeroProfiles'),
   'supporting_results': ['coPoissonComplexDensity_eq_family', 'norm_zeroFamilyDensity_le_of_norm_le',
                          'iteratedDeriv_integral_entire', 'hasDerivAt_integral_of_closedBall',
                          'spectralKappa_zeroLocalInverse', 'deriv_zeroLocalInverse_center',
                          'analyticOrderAt_riemannZeta_comp_inverse', 'zeroJetOrder_one_sub', 'zeroJetOrder_conj',
                          'zeroFamilyDensity_pairing_jet', 'zeroFamilyFunctional_eq', 'zeroFamilyFunctional_fourier',
                          'zeroFamilyFunctional_jet', 'zeroJetDensity_tail', 'zeroJetDensity_bounded',
                          'normalizedZeroMeasureJet_integral', 'zeroJetProfile_chain', 'zeroJetProfile_forced_chain',
                          'normalizedZeroMeasureJet_one_sub', 'normalizedZeroMeasureJet_conj']},
 'existing_lean_sources_changed': False,
 'cache_owner': ('single local process; the module was built from this exact source in the session '
                 '(lake rebuilds on source hash change), and the runner build re-validated it'),
 'sources': [{'path': q, 'sha256': sha(REPO/q), 'bytes': (REPO/q).stat().st_size} for q in srcs],
 'roots': {
  'Zeta23.OPICAFollowup.copoisson_zero_jets_measures': {
    'paper': 'R2-H1', 'expected_type_consumer': 'consumers/ExpectedCoPoissonJets.lean (9 receipts)',
    'actual_domain': ('at every actual strip zero the order-zero jet is the CP1 zero measure and its parameter limit is the '
                      'construction; the k = 0 chain is the ForcedEuler identity; at multiplicity >= 2 the first jet is a pure '
                      'density measure with tail -B2/(2x^2) + O(x^-3); 1 - rho gives the same node and jets; conjugate jets on '
                      'real tests'),
    'premises': 'zeta(rho) = 0, 0 < Re rho < 1, k < zeroJetOrder rho (rho != 1/2 is derived)',
    'axioms': 'propext, Classical.choice, Quot.sound'}},
 'gates': [
  {'label': 'narrow runner (20 modules, 25 consumer files)', 'log': 'runner/CHECK_RESULT.json',
   'sha256': sha(E/'runner/CHECK_RESULT.json'), 'exit_code': 0, 'runner_status': 'PASS_NARROW_ONLY',
   'consumer_receipts': {c['name']: len(c['axioms']) for c in res['consumers']}},
  {'label': 'W04/W07 workflow consumer (unchanged heredoc)', 'log': 'consumers/opica-w04-w07-expected.log',
   'sha256': sha(E/'consumers/opica-w04-w07-expected.log'), 'exit_code': 0, 'standard_axiom_receipts': 52},
  {'label': 'W06 workflow consumer (unchanged heredoc)', 'log': 'consumers/opica-w06-expected.log',
   'sha256': sha(E/'consumers/opica-w06-expected.log'), 'exit_code': 0, 'standard_axiom_receipts': 14},
  {'label': 'W01 consumers and exact-source subset',
   'note': 'not re-run locally: no existing Lean source changed and no W01 or subset module imports the new module; green in CI at the Stage 16 record head c6ce649d (stage17/ci-harvest-c6ce649d-partial.json)'},
  {'label': 'child suite and parent contract tests', 'result': sys.argv[1]},
  {'label': 'frozen control replay', 'result': sys.argv[2]},
  {'label': 'numerical falsification (mpmath 1.3.0, not interval certified)',
   'script': 'numerical-falsification.py', 'script_sha256': sha(E/'numerical-falsification.py'),
   'log': 'numerical-falsification.log', 'log_sha256': sha(E/'numerical-falsification.log'),
   'result': ('first zero rho0 (simple, m = 1): the kappa-family equals S_rho/b_rho to 2e-30 at a generic parameter; the '
              'order-zero tail residual times y^3 stays bounded (1.6 to 3.3) up to y = 900; beyond the multiplicity the first '
              'kappa-jet of the density is of size y^(-1/2) (the predicted power-term derivative; residual times y^3 bounded), '
              'so the O(y^-2) tail fails at k = m, and the first construction jet on a gap test is A\'(kappa0) H(rho0) = '
              '7.8e-4 != 0 (gap lost at k = m); the chain for h1 holds on cells to 3e-30 and x^2 h1\' jumps by -1.000001 at '
              'n = 2 and 5; the branches through rho0 and 1 - rho0 are reflections')}],
 'negative_controls': [{'file': 'negative-controls/negative-copoisson-jets.lean', 'expected': 'REJECTED',
   'observed': neg, 'log_sha256': sha(E/'negative-controls/negative-copoisson-jets.log')}],
 'ci_harvest': {'file': '../stage17/ci-harvest-c6ce649d-partial.json', 'sha256': sha(C/'evidence/current-codex/stage17/ci-harvest-c6ce649d-partial.json'), 'scope': 'no new harvest: the latest harvest is the Stage 17 partial harvest of c6ce649d; CI on 02c0ce8f was superseded by the push of ff7b7c70, and CI on ff7b7c70 was in progress at publication'},
 'not_established': ['aggregate current-source export', 'full100 compiler receipt production/replay',
   'facade and registration', 'parent-extension acceptance',
   'canonical regeneration (rhkg-compiler-receipt remains red)', 'CI on the published head (pending at publication)'],
 'RH': 'OPEN', 'Step4': 'OPEN', 'independent_closing_inequalities': 'OPEN'}
(E/'STATUS.json').write_text(json.dumps(status, indent=1)+'\n')
print('ok', head)
