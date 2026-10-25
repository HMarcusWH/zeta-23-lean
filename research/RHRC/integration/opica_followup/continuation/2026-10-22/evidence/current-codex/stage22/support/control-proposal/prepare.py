"""Preserve21 historical controls and prepare10 exact Stage22 mutations."""
from pathlib import Path
import hashlib, importlib.util, json, re, subprocess
HERE=Path(__file__).resolve().parent;WORK=HERE.parent;REPO=WORK/'opica-followup-repo'
HEAD='2440dcde7607baa7bcff2ce9626effa1ae9f3f07';TREE='dee5bc2fa3148ad42e3ef1fef17c4acf6a408f99'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok:raise ValueError(msg)
def git(*args):return subprocess.check_output(['git','-C',str(REPO),*args],text=True).strip()
require(git('rev-parse','HEAD')==HEAD and git('rev-parse','HEAD^{tree}')==TREE and not git('status','--porcelain'),'exact clean Stage22 pin required')
dest=HERE/'sources';require(not dest.exists(),'fresh proposal sources required');dest.mkdir()
prior_folder=WORK/'opica-stage21/clean-controls';prior=json.loads((prior_folder/'CHECK_RESULT.json').read_bytes())
require(prior['status']=='PASS_CONTROLS_ONLY' and len(prior['controls'])==21,'complete21 prior controls required')
anchors={
 'homogeneous-eigenproblem':['eulerImage','PositiveAxisTest'],
 'missing-conjugation':['native_sample_stieltjes_identity','starRingEnd'],
 'missing-lattice-atoms':['nativeLogForce','sawtooth_integrable_force_identity'],
 'synthetic-spectral-measure':['arithmeticSpectralMeasure','not definitionally equal'],
 'wrong-fourier-2pi':['logFourier','logFourier_eq_fourier'],
 'wrong-reflection-kappa':['unsolved goals','starRingEnd'],
 'NegativeMissingQuiet':['Invalid projection','quiet_balanced_observation_implies_native_cut'],
 'NegativeMissingSlow':['native_slow_source_window_rate','Tendsto'],
 'NegativeSyntheticQuiet':['nativeRawHigh','Application type mismatch'],
 'NegativeWindowBoundary':['unsolved goals','False'],
 'NegativeZeroDamping':['nativeZeroDisplacementSup','False'],
 'NegativeConfluentProfilesDistinctness':['distinctSpectralNodes','LinearIndependent'],
 'NegativeConfluentProfilesDeterminantSign':['profile_jet_confluent_determinant','profileJetMatrix'],
 'NegativeConfluentProfilesUnnormalized':['iteratedDeriv','profile_jet_confluent_determinant'],
 'NegativeParameterFactorial':['oddJetCoefficient','-1 / 6','-1 / 3'],
 'NegativeFullFiniteSpanFinal':['OffLatticeNonnegative','finite_zero_span_positive_only_zero'],
 'NegativeBudgetIndependenceFinal':['Invalid field `choose`','LinearIndependent'],
}
rows=[]
def add(filename,data,positive,scope,origin,needles=()):
    target=dest/filename;require(not target.exists(),'duplicate source filename')
    target.write_bytes(data)
    rows.append({'name':target.stem,'file':filename,'source_sha256':sha(target),
      'expected':'PASS' if positive else 'REJECTED','scope':scope,'origin':origin,'required_diagnostic_regex':list(needles)})
for row in prior['controls']:
    path=prior_folder/row['file'];require(sha(path)==row['source_sha256'],'prior source mismatch:'+path.name)
    add(path.name,path.read_bytes(),row['expected']=='PASS',row['scope'],
        {'kind':'EXACT_STAGE21_BYTES','path':str(path),'sha256':sha(path),
         'receipt':str(prior_folder/'CHECK_RESULT.json'),'receipt_sha256':sha(prior_folder/'CHECK_RESULT.json')},anchors.get(row['name'],[]))
canonical_receipt=WORK/'audit-release/stage22-type-control-receipt.json'
canonical=json.loads(canonical_receipt.read_text())
for name,needles,scope in [
 ('NegativeCanonicalRecoveryWrongCost',['orthogonalRecovery_norm_eq_optimalRecoveryCost','sSup'],'Canonical exact recovery cost cannot acquire an unproved +1.'),
 ('NegativeCanonicalEulerWrongMultiplier',['finiteEulerFilter_laplace','finiteEulerMultiplier'],'Actual Euler action cannot acquire an unproved +1 multiplier.'),
 ('NegativeCanonicalResidualWrongPower',['truncatedInverseResidual_laplace','r \\+ 1'],'Actual real-cutoff residual cannot change power r to r+1.')]:
    path=WORK/'audit-release'/(name+'.lean')
    evidence=next(r for r in canonical['commands'] if r.get('source')==path.name)
    require(sha(path)==evidence['source_sha256'] and evidence['expected_disposition_observed'],'canonical sealed source mismatch')
    add(path.name,path.read_bytes(),False,scope,{'kind':'EXACT_SEALED_CANONICAL_MUTATION','path':str(path),
      'sha256':sha(path),'receipt':str(canonical_receipt),'receipt_sha256':sha(canonical_receipt)},needles)
square_folder=WORK/'audit-square-physical/SEALED_SQUARE_PHYSICAL_2026-10-24'
square=square_folder/'NegativeSquarePhysicalFinal.lean';square_manifest=json.loads((square_folder/'FILE_MANIFEST_SHA256.json').read_text())
require(sha(square)==square_manifest[square.name],'sealed square source mismatch')
text=square.read_text(encoding='utf-8').replace('import SquareDefectPhysicalFullCandidate','import Zeta23.OPICAFollowup.SquareDefect',1)
positions=[m.start() for m in re.finditer(r'(?m)^example\b',text)];require(len(positions)==3,'three actual square mutations required')
prefix=text[:positions[0]];ending='\nend Zeta23.OPICAFollowup.SquarePhysicalNegative\n'
for i,(name,needles,scope) in enumerate([
 ('NegativeSquareMissingPlateau',['squareGapJordan_gap','h x = A'],'Actual square unit gap needs the genuine plateau condition.'),
 ('NegativeSquareMissingLatticeSupport',['square_actual_no_tempered_measure_repair','totalVariation'],'Actual all-temperate-measure no-repair needs actual lattice support.'),
 ('NegativeSquareMissingTemperedGrowth',['failed to synthesize','HasTemperateGrowth'],'The canonical Schwartz embedding needs actual temperate variation growth.')]):
    stop=positions[i+1] if i+1<len(positions) else text.index('\nend Zeta23.OPICAFollowup.SquarePhysicalNegative',positions[i])
    add(name+'.lean',(prefix+text[positions[i]:stop]+ending).encode(),False,scope,
      {'kind':'SEALED_SQUARE_EXAMPLE_SPLIT_IMPORT_ONLY','path':str(square),'sha256':sha(square),
       'example_index':i,'adaptation':'Split the three original example bodies into separate files; change only standalone module import.'},needles)
compat=WORK/'audit-tempered-lattice/SEALED_TEMPERED_LATTICE_2026-10-24/NegativeOmitsCompactCompatibility.lean'
require(sha(compat)=='a45273eb9bf5e980dc7c5a1e900493773cd8fcd606c07dd886644b0fdb0a46f2','sealed compact-compatibility source mismatch')
add(compat.name,compat.read_bytes().replace(b'import TemperedLatticeNoRepair',b'import Zeta23.OPICAFollowup.SquareDefect',1),False,
 'Support of an unrelated measure does not constrain an arbitrary tempered distribution without compact compatibility.',
 {'kind':'SEALED_COMPACT_COMPATIBILITY_IMPORT_ONLY','path':str(compat),'sha256':sha(compat)},
 ['extension_annihilates_lattice_zero','ExtendsCompactPairing'])
ct_folder=WORK/'audit-ct13';ct=json.loads((ct_folder/'negative-controls.json').read_text())
for name,needles in [('WrongFactorControl',['sinc_identity_original','Real.exp L - 1']),
                     ('WrongSlopeControl',['positive_sinc_mass_slope','Tendsto'])]:
    path=ct_folder/(name+'.lean');evidence=next(r for r in ct['controls'] if r['name']==name)
    require(sha(path)==evidence['source_sha256'] and evidence['expected_disposition_observed'],'sealed CT mutation mismatch')
    add(path.name,path.read_bytes().replace(b'import CT13Limits',b'import Zeta23.OPICAFollowup.NearGapLimits',1),False,
      'Original CT1.3 normalization/first-order cost is indispensable.',
      {'kind':'SEALED_CT13_IMPORT_ONLY','path':str(path),'sha256':sha(path),
       'receipt':str(ct_folder/'negative-controls.json'),'receipt_sha256':sha(ct_folder/'negative-controls.json')},needles)
cc_folder=WORK/'audit-independent-expected-types';cc=cc_folder/'NegativeNoCommonBudget.lean'
cc_receipt=json.loads((cc_folder/'HT2_COMPACT_CONTINUOUS_EXTRACTION_RECEIPT.json').read_text())
evidence=next(r for r in cc_receipt['files'] if Path(r['path']).name==cc.name)
require(sha(cc)==evidence['sha256'],'sealed common TV omission source mismatch')
add(cc.name,cc.read_bytes().replace(b'import CompactContinuousExtraction',b'import Zeta23.OPICAFollowup.NearGapLimits',1),False,
 'Per-member linear growth does not replace one common TV bound in Schwartz-to-continuous-compact extraction.',
 {'kind':'SEALED_CC_COMMON_TV_IMPORT_ONLY','path':str(cc),'sha256':sha(cc),
  'receipt':str(cc_folder/'HT2_COMPACT_CONTINUOUS_EXTRACTION_RECEIPT.json'),'receipt_sha256':sha(cc_folder/'HT2_COMPACT_CONTINUOUS_EXTRACTION_RECEIPT.json')},
 ['unsolved goals','CommonLinearMassBound'])
require(len(rows)==31 and sum(r['expected']=='PASS' for r in rows)==4,'exact31 source inventory required')
spec=importlib.util.spec_from_file_location('unchanged_source_snapshot_reader',REPO/'research/RHRC/integration/opica_followup/build_receipt.py')
builder=importlib.util.module_from_spec(spec);spec.loader.exec_module(builder)
snapshot=builder.full_source_manifest(REPO)
require(git('rev-parse','HEAD')==HEAD and not git('status','--porcelain'),'owner changed during plan')
(HERE/'planned-source-manifest.json').write_text(json.dumps(snapshot,indent=2)+'\n',encoding='utf-8')
manifest={'schema':'OPICA_STAGE22_31_CONTROL_PLAN_V1','status':'PREPARED_NOT_RUN_AT_STAGE22_PIN',
 'checked_commit':HEAD,'checked_tree':TREE,'original21_preserved_byte_exact':True,
 'source_count':31,'negative_source_count':27,'positive_source_count':4,
 'new_groups':{'canonical':3,'square_physical':3,'compact_compatibility':1,'CT13':2,'continuous_compact_common_TV':1},
 'planned_owner_source_manifest':'planned-source-manifest.json','planned_owner_source_manifest_sha256':sha(HERE/'planned-source-manifest.json'),
 'source_reader_sha256':sha(REPO/'research/RHRC/integration/opica_followup/build_receipt.py'),
 'controls':rows,'runtime_policy':'No owner source/cache writers; owner authorized overlap with read-only44 consumer replay after broad build. No build command; all Lean outputs external.',
 'source_pin_drift':'FAIL_CLOSED; regenerate proposal after explicitly reviewed source/pin change.',
 'release_ready':False,'aggregate_accepted':False,'RH':'OPEN','Step4':'OPEN'}
(HERE/'CONTROL_PLAN.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print('PREPARED31 controls:27negative+4positive; preservedall21 priorbytes; boundclean'+HEAD)
