"""Portable orchestration guards; native proof lanes remain independently required.

Only the failing source-report tests replace a lightweight source inspector.
Their heavy checkers are tripwires and never return a simulated proof success.
The positive support-receipt test executes the real authored49-test runner.
"""
from collections import Counter
from pathlib import Path
import json
import copy
import hashlib
import subprocess
import sys
import os
import stat
from contextlib import contextmanager
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

from research.RHRC.integration.opica_composition import cli, executor, qualification, snapshot
from research.RHRC.integration.opica_composition.contracts import WorkerConfig, SearchBudget
from research.RHRC.integration.opica_round4 import math_gate
from research.RHRC.integration.opica_composition.accept import ROUND4_LANES
from research.RHRC.integration.opica_composition.canonical import ContractError, canonical_bytes, load_bytes
from research.RHRC.integration.opica_composition.descendant import BASE, BASE_TREE
from research.RHRC.integration.opica_composition.provider import configuration
from research.RHRC.integration.opica_composition.testing import discover_methods

REPO = Path(__file__).resolve().parents[5]
R4 = REPO / "research/RHRC/integration/opica_round4"
SUPPORT = REPO / "research/RHRC/integration/opica_round4_support"
REQUIRED_LANES = (
    "CONTRACT", "PARENT_REGRESSION", "CURRENT_COMPATIBILITY", "COMPOSITION_FORMAL",
    "SEMANTIC_NEGATIVES", "REPLAY_CAMPAIGN", "FRAMEWORK_ADAPTERS", "PROVIDER_SELECTED",
    "GENERATED_STATE", "MATHEMATICAL_SUPPORT", "SOURCE_NUMERICS",
)


class CliOrchestrationTests(unittest.TestCase):
    def test_native_evidence_copy_preserves_complete_inventory(self):
        # Actual filesystem bytes only; this does not manufacture native proof.
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);native=root/'native';native.mkdir();(native/'empty').mkdir()
            payloads={'bootstrap/result.json':b'{}\n','attempt/OpicaAttempt.olean':b'object bytes',
                      'attempt/OpicaAttempt.olean.server':b'server bytes','journal.db':b'database bytes',
                      'unfiltered.bin':b'\0\xffcomplete bytes'}
            for name,raw in payloads.items():
                path=native/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
            sealed=snapshot.seal_evidence_tree(native);output=root/'lane';output.mkdir()
            manifest=cli._publish_native_evidence(native,output)
            self.assertEqual(manifest,sealed[0])
            self.assertEqual({r['path'] for r in manifest['files']},set(payloads))
            self.assertEqual(manifest['total_bytes'],sum(map(len,payloads.values())))
            self.assertIn('empty',manifest['directories'])
            self.assertEqual(load_bytes((output/'native-evidence-inventory.json').read_bytes()),manifest)
            for name,raw in payloads.items():self.assertEqual((output/'native-evidence'/name).read_bytes(),raw)
            self.assertTrue(snapshot.verify_evidence_tree(output/'native-evidence',manifest))
            with self.assertRaisesRegex(ContractError,'logical bytes'):
                snapshot.seal_evidence_tree(native,maximum_bytes=1)
            # Missing, extra and changed files and empty directories all matter.
            for change in ('missing','extra','changed','empty-directory'):
                destination=root/change;snapshot.copy_evidence_tree(native,destination,sealed)
                if change=='missing':(destination/'unfiltered.bin').unlink()
                elif change=='extra':(destination/'extra.bin').write_bytes(b'extra')
                elif change=='changed':(destination/'unfiltered.bin').write_bytes(b'changed')
                else:(destination/'empty').rmdir()
                with self.subTest(change=change),self.assertRaises(ContractError):
                    snapshot.verify_evidence_tree(destination,manifest)
            for name,row in (('results.json',{}),('source.json',{'fixture':'not proof'}),
                             ('source-after.json',{'fixture':'not proof'})):
                (output/name).write_bytes(canonical_bytes(row))
            (output/'native-evidence/unfiltered.bin').unlink()
            files={name:output/name for name in ('results.json','source.json','source-after.json','native-evidence-inventory.json')}
            with patch.object(cli,'validate_descendant',return_value={'fixture':'not proof'}), \
                    patch('research.RHRC.integration.opica_composition.testing.checked_inventory',
                          side_effect=AssertionError('heavy replay must not run')) as replay:
                with self.assertRaisesRegex(ContractError,'inventory/content'):
                    cli.verify_lane_raw({'id':'MATHEMATICAL_SUPPORT'},{},files,REPO,root/'independent')
                replay.assert_not_called()
            self.assertFalse((root/'independent').exists())

    def test_native_evidence_rejects_links_and_nonregular_entries(self):
        @contextmanager
        def bad_entry(path,kind,outside):
            if os.name!='nt':
                if kind=='fifo':os.mkfifo(path)
                else:path.symlink_to(outside if kind!='dangling' else outside/'absent',target_is_directory=kind=='directory')
                yield
            else:
                # Windows needs no symlink privilege: only the exact leaf's
                # metadata changes; outside bytes and all parent reads are real.
                path.write_bytes(b'placeholder')
                original=os.lstat
                def lstat(candidate,*args,**kwargs):
                    info=original(candidate,*args,**kwargs)
                    if Path(os.path.abspath(candidate))==path:
                        fields={name:getattr(info,name) for name in dir(info) if name.startswith('st_')}
                        fields['st_mode']=(stat.S_IFIFO if kind=='fifo' else stat.S_IFLNK)|0o600
                        fields['st_file_attributes']=1024 if kind=='reparse' else 0
                        return SimpleNamespace(**fields)
                    return info
                with patch.object(os,'lstat',side_effect=lstat):yield
        for kind in ('file','directory','dangling','reparse','fifo'):
            with self.subTest(kind=kind),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);native=root/'native';native.mkdir();outside=root/'outside';outside.mkdir()
                secret=b'EXTERNAL_BYTES_MUST_NEVER_BE_COPIED';(outside/'secret.log').write_bytes(secret)
                path=native/'alias.log';target=outside if kind=='directory' else outside/'secret.log'
                with bad_entry(path,kind,target),patch.dict(os.environ,{'OPICA_NATIVE_OUTPUT':str(native)}), \
                        patch.object(cli,'validate_descendant',return_value={'fixture':'not proof'}), \
                        patch('research.RHRC.integration.opica_composition.testing.checked_inventory',
                              return_value={'tests':[{'lane':'COMPOSITION_FORMAL','method':'boundary fixture only'}]}), \
                        patch('research.RHRC.integration.opica_composition.testing.run_modes',return_value=[]), \
                        patch.object(cli,'_collect_failed_native_diagnostics'):
                    with self.assertRaises((ContractError,OSError)):
                        cli.run_lane('COMPOSITION_FORMAL',REPO,root/'lane',{})
                self.assertFalse((root/'lane/lane.json').exists())
                self.assertFalse((root/'lane/native-evidence-inventory.json').exists())
                self.assertFalse(any(p.is_file() and p.read_bytes()==secret for p in (root/'lane').rglob('*')))
                self.assertEqual((outside/'secret.log').read_bytes(),secret)
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);native=root/'native';native.mkdir();(native/'ok').write_bytes(b'original')
            if os.name!='nt':
                alias=root/'root-alias';alias.symlink_to(native,target_is_directory=True)
                with self.assertRaises(ContractError):snapshot.seal_evidence_tree(alias)
                repo_alias=root/'repo-alias';repo_alias.symlink_to(REPO,target_is_directory=True)
                with self.assertRaises(ContractError):cli.run_lane('CONTRACT',repo_alias,root/'aliased-output',{})
            else:
                with bad_entry(root/'root-alias','reparse',native),self.assertRaises(ContractError):
                    snapshot.seal_evidence_tree(root/'root-alias')
                with bad_entry(root/'repo-alias','reparse',REPO),self.assertRaises(ContractError):
                    cli.run_lane('CONTRACT',root/'repo-alias',root/'aliased-output',{})
            self.assertFalse((root/'aliased-output').exists())

    def test_native_evidence_copy_races_never_publish_success(self):
        # Inject changes after sealing, at the actual copy boundary. No native
        # checker or successful lane receipt is substituted or accepted here.
        for kind in ('content','file-to-directory','directory-to-link','dangling-link','root-swap','during-copy',
                     'open-boundary-link','open-boundary-directory'):
            with self.subTest(kind=kind),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);native=root/'native';(native/'parent').mkdir(parents=True)
                source=native/'parent/evidence.log';source.write_bytes(b'original')
                outside=root/'outside';outside.mkdir();secret=b'EXTERNAL_RACE_BYTES';(outside/'evidence.log').write_bytes(secret)
                output=root/'lane';original=cli.copy_evidence_tree
                def changed(tree,destination,sealed):
                    if kind.startswith('open-boundary-'):
                        original_file=snapshot._evidence_file;calls=0
                        @contextmanager
                        def swap_before_open(base,relative,identities=None):
                            nonlocal calls
                            if Path(base)==tree and relative=='parent/evidence.log':
                                calls+=1
                                # First read is copy's pre-seal; second is the
                                # actual source open after the destination exists.
                                if calls==2:
                                    if kind=='open-boundary-link':
                                        source.unlink()
                                        if os.name!='nt':source.symlink_to(outside/'evidence.log')
                                        else:source.write_bytes(secret)
                                    else:
                                        (tree/'parent').rename(tree/'old-parent')
                                        if os.name!='nt':(tree/'parent').symlink_to(outside,target_is_directory=True)
                                        else:(tree/'parent').mkdir();(tree/'parent/evidence.log').write_bytes(secret)
                            with original_file(base,relative,identities) as value:yield value
                        with patch.object(snapshot,'_evidence_file',side_effect=swap_before_open):
                            return original(tree,destination,sealed)
                    if kind=='during-copy':
                        original_directory=snapshot._evidence_directory
                        @contextmanager
                        def mutate_after_open(base,relative='',identities=None):
                            with original_directory(base,relative,identities) as value:
                                if Path(base)==destination and relative=='parent':source.write_bytes(b'changed during copy')
                                yield value
                        with patch.object(snapshot,'_evidence_directory',side_effect=mutate_after_open):
                            return original(tree,destination,sealed)
                    if kind=='content':source.write_bytes(b'changed')
                    elif kind=='file-to-directory':source.unlink();source.mkdir()
                    elif kind=='root-swap':
                        tree.rename(root/'old-root');tree.mkdir();(tree/'parent').mkdir();(tree/'parent/evidence.log').write_bytes(b'original')
                    elif os.name!='nt':
                        source.unlink();(tree/'parent').rmdir()
                        (tree/'parent').symlink_to(outside if kind=='directory-to-link' else root/'absent',target_is_directory=True)
                    else:
                        # Real replacement-directory identity guards remain
                        # active without requiring Windows symlink privileges.
                        (tree/'parent').rename(tree/'old-parent');(tree/'parent').mkdir()
                        (tree/'parent/evidence.log').write_bytes(b'original')
                    return original(tree,destination,sealed)
                with patch.object(cli,'copy_evidence_tree',side_effect=changed), \
                        patch.dict(os.environ,{'OPICA_NATIVE_OUTPUT':str(native)}), \
                        patch.object(cli,'validate_descendant',return_value={'fixture':'not proof'}), \
                        patch('research.RHRC.integration.opica_composition.testing.checked_inventory',
                              return_value={'tests':[{'lane':'COMPOSITION_FORMAL','method':'boundary fixture only'}]}), \
                        patch('research.RHRC.integration.opica_composition.testing.run_modes',return_value=[]), \
                        patch.object(cli,'_collect_failed_native_diagnostics'):
                    with self.assertRaises((ContractError,OSError)):cli.run_lane('COMPOSITION_FORMAL',REPO,output,{})
                self.assertFalse((output/'lane.json').exists())
                self.assertFalse((output/'native-evidence-inventory.json').exists())
                self.assertFalse(any(p.is_file() and p.read_bytes()==secret for p in output.rglob('*')))
                self.assertEqual((outside/'evidence.log').read_bytes(),secret)

    def test_mathematical_support_uses_closed_worker_recipe_and_bounded_caps(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            worker = WorkerConfig(str(root / 'toolchain/bin/lean'), str(root / 'toolchain'),
                                  [str(root / 'imports')], production=True,
                                  budget={'wall_seconds': 900, 'memory_bytes': 8589934592, 'disk_bytes': 8589934592})
            budget = math_gate.mathematical_budget(worker, 900)
            self.assertEqual(budget.heartbeats, 1200000)
            self.assertEqual((budget.wall_seconds, budget.memory_bytes, budget.disk_bytes),
                             (600, 4294967296, 4294967296))
            short = math_gate.mathematical_budget(worker, 10)
            self.assertEqual((short.wall_seconds, short.cpu_seconds), (10, 10))
            source = 'Zeta23/OPICARound4/Validation.lean'
            command, env = executor._recipe(worker, root / 'output', source, source[:-5] + '.olean',
                                            budget, mathematical_support=True)
            self.assertEqual(env, {})
            self.assertIn('--unshare-all', command)
            self.assertIn('--clearenv', command)
            self.assertIn('--nproc=64', command)
            self.assertIs(type(executor.LEAN_ADDRESS_SPACE_BYTES), int)
            self.assertEqual(executor.LEAN_ADDRESS_SPACE_BYTES, 68719476736)
            self.assertEqual([arg for arg in command if arg.startswith('--as=')], ['--as=68719476736'])
            self.assertEqual(command[command.index('--bind') + 1:command.index('--bind') + 3],
                             [str(root / 'output'), '/out'])
            self.assertEqual(command[-1], '/out/' + source)
            self.assertEqual(command[command.index('-i') + 1], '/out/' + source[:-5] + '.ilean')
            self.assertIn('-DrelaxedAutoImplicit=false', command)
            self.assertIn('-j2', command)
            lean_path = command[command.index('LEAN_PATH') + 1]
            self.assertEqual(lean_path, str(root / 'imports'))
            self.assertNotIn('/out', lean_path.split(':'))
            default, _ = executor._recipe(worker, root / 'output', 'OpicaAttempt.lean', 'OpicaAttempt.olean', SearchBudget())
            self.assertNotIn('-i', default)
            self.assertNotIn('-DrelaxedAutoImplicit=false', default)
            config = root / 'worker-config.json'; config.write_bytes(worker.to_bytes() + b'\n')
            parsed, config_hash = math_gate.load_worker_config(config)
            self.assertEqual(parsed, worker)
            self.assertEqual(config_hash, hashlib.sha256(config.read_bytes()).hexdigest())
            # Exercise direct-script package loading, stopping at the missing
            # compiler before any native work or successful proof is possible.
            entry = subprocess.run([sys.executable, '-B', str(Path(math_gate.__file__)), '--repo', str(REPO),
                                    '--output-dir', str(root / 'unused'), '--lean', worker.lean,
                                    '--lean-paths', worker.lean_paths[0], '--worker-config', str(config)],
                                   capture_output=True, text=True, timeout=30)
            self.assertNotEqual(entry.returncode, 0)
            self.assertIn('Missing checkout or native compiler', entry.stderr)
            config.write_bytes(canonical_bytes({**worker.to_dict(), 'extra': 'forbidden'}))
            with self.assertRaises(ContractError):
                math_gate.load_worker_config(config)
            for name, obj, selector in (('../Escape.lean', '../Escape.olean', True),
                                       ('Source.lean', 'Source.olean', True),
                                       (source, 'Other.olean', True), (source, source[:-5] + '.olean', 'yes')):
                with self.subTest(source=name, object=obj, selector=selector), self.assertRaises(ContractError):
                    executor._recipe(worker, root / 'output', name, obj, budget, mathematical_support=selector)

    def test_mathematical_support_copies_exact_module_before_dispatch(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); lib = root / 'lib'; lib.mkdir()
            source = root / 'original.lean'; raw = b'import Init\n-- exact input bytes\r\n'
            source.write_bytes(raw)
            worker = WorkerConfig(str(root / 'lean'), str(root / 'toolchain'), [str(root / 'imports')], production=False)
            relative = 'Zeta23/OPICARound4/Validation.lean'; output = root / 'worker'
            def tripwire(config, folder, source_name, obj_name, budget, **options):
                self.assertEqual((source_name, obj_name), (relative, relative[:-5] + '.olean'))
                self.assertEqual((folder / relative).read_bytes(), raw)
                self.assertEqual(config.lean_paths, [str(lib), *worker.lean_paths])
                self.assertEqual(options, {'mathematical_support': True})
                raise RuntimeError('dispatch tripwire; no proof executed')
            with patch.object(executor, 'run_worker', side_effect=tripwire) as dispatch, \
                    patch.object(math_gate.subprocess, 'run', side_effect=AssertionError('direct compiler forbidden')):
                with self.assertRaisesRegex(RuntimeError, 'dispatch tripwire'):
                    math_gate._isolated_compile(worker, output, lib, source, relative, SearchBudget())
                dispatch.assert_called_once()
            self.assertEqual(source.read_bytes(), raw)
            self.assertEqual(list(lib.iterdir()), [])
            def coordinator_tripwire(command, repo, env, folder, label, seconds):
                self.assertEqual(seconds, 7200)
                self.assertEqual(command[command.index('--timeout') + 1], '600')
                config = Path(command[command.index('--worker-config') + 1])
                self.assertEqual(math_gate.load_worker_config(config)[0], worker)
                raise RuntimeError('bounded coordinator tripwire; no proof executed')
            with patch.object(qualification, '_worker_version', return_value={}), \
                    patch.object(qualification, '_command', side_effect=coordinator_tripwire) as coordinator:
                with self.assertRaisesRegex(RuntimeError, 'bounded coordinator tripwire'):
                    qualification.check_mathematical_support(REPO, root / 'coordinator', worker)
                coordinator.assert_called_once()
            self.assertEqual(load_bytes((root / 'coordinator/result.json').read_bytes())['status'], 'ENVIRONMENT_ERROR')

    def test_mathematical_support_rejects_unisolated_and_forged_worker_receipts(self):
        # These records only exercise rejection paths; none can authorize proof.
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp); worker = WorkerConfig(str(output / 'lean'), str(output / 'toolchain'),
                                                     [str(output / 'imports')], production=True)
            with self.assertRaisesRegex(ContractError, 'execution authority'):
                qualification._validate_mathematical_worker_receipts({'execution_mode': 'DEVELOPMENT_ONLY'}, output, worker)
            module = math_gate.MODULES[0]; source = math_gate.relative(module).as_posix()
            folder = output / 'workers' / module; (folder / source).parent.mkdir(parents=True)
            (folder / source).write_bytes(b'fixture, not a theorem')
            log = output / (module + '.log'); log.write_bytes(b'fixture, not compiler evidence')
            (folder / (source + '.log')).write_bytes(log.read_bytes())
            sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
            budget = math_gate.mathematical_budget(worker, 600)
            isolated = WorkerConfig(worker.lean, worker.toolchain_root, [str(output / 'lib'), *worker.lean_paths])
            command, _ = executor._recipe(isolated, folder, source, source[:-5] + '.olean', budget, mathematical_support=True)
            native = {'recipe': executor.MATH_SUPPORT_RECIPE, 'capability': 'LINUX_ISOLATED', 'exit_code': 0,
                      'resource_status': None, 'command': command, 'log_sha256': sha(log),
                      'resource_scope': {'mode': 'LINUX_CGROUP_V2_TMPFS', 'memory_bytes': 4294967296,
                                         'address_space_bytes': 68719476736,
                                         'processes': 64, 'disk_bytes': 4294967296, 'cgroup': '/fixture'}}
            native.update(resource_reason=None,failure_reason=None,
              resource_caps={'wall_seconds':budget.wall_seconds,'cpu_seconds_soft':budget.cpu_seconds,
                'cpu_seconds_hard':budget.cpu_seconds,'log_bytes':budget.log_bytes,'max_file_bytes':budget.max_file_bytes,
                'memory_bytes':budget.memory_bytes,'disk_bytes':budget.disk_bytes,
                'address_space_bytes':executor.LEAN_ADDRESS_SPACE_BYTES,'os_limits_enforced':True},
              child_status={'schema':'OPICA_WORKER_WAIT_STATUS_V1','return_code':0,'signal':None,
                'observation':'PYTHON_SUBPROCESS_WAIT','scope':'COMMAND_PROCESS_ONLY_WRAPPED_CHILD_UNKNOWN'})
            first = {'module': module, 'worker_output': str(folder), 'argv': command, 'native': native,
                     'exit_code': 0, 'source_sha256': sha(folder / source), 'log_sha256': sha(log)}
            base = {'execution_mode': 'PRODUCTION_ISOLATED', 'authority': 'CURRENT_SOURCE_ISOLATED_NATIVE_SUPPORT',
                    'worker': worker.to_dict(), 'worker_budget': budget.to_dict(),
                    'module_records': [first] + [{'module': m} for m in math_gate.MODULES[1:]]}
            for patch_value, message in (
                    ({'resource_caps': {}}, 'resource caps differ'),
                    ({'resource_caps': {**native['resource_caps'], 'os_limits_enforced': 1}}, 'resource caps differ'),
                    ({'resource_caps': {**native['resource_caps'], 'max_file_bytes': 1}}, 'resource caps differ'),
                    ({'child_status': {}}, 'wait status differs'),
                    ({'child_status': {**native['child_status'], 'return_code': False}}, 'wait status differs'),
                    ({'failure_reason': 'UNCLASSIFIED_WORKER_FAILURE'}, 'failure reason differs'),
                    ({'failure_reason': 'KILLED_UNATTRIBUTED'}, 'receipt missing or invalid'),
                    ({'resource_reason': 'CPU_TIME'}, 'receipt missing or invalid')):
                with self.subTest(resource_evidence=patch_value):
                    forged = copy.deepcopy(base); forged['module_records'][0]['native'].update(patch_value)
                    with self.assertRaisesRegex(ContractError, message):
                        qualification._validate_mathematical_worker_receipts(forged, output, worker)
            # Correct resource fields must pass their guard and reach the
            # deliberately incomplete products, never qualify this fixture.
            with self.assertRaisesRegex(ContractError, 'Mathematical module product binding differs'):
                qualification._validate_mathematical_worker_receipts(base, output, worker)
            absent = object()
            for virtual in (absent, True, '68719476736', 68719476736.0, 0, 4294967296, 68719476735, 68719476737):
                with self.subTest(address_space=virtual):
                    forged = copy.deepcopy(base)
                    scope = forged['module_records'][0]['native']['resource_scope']
                    if virtual is absent:
                        scope.pop('address_space_bytes')
                    else:
                        scope['address_space_bytes'] = virtual
                    with self.assertRaisesRegex(ContractError, 'Mathematical isolated worker resource scope differs'):
                        qualification._validate_mathematical_worker_receipts(forged, output, worker)
            forged = copy.deepcopy(base)
            forged['module_records'][0]['native']['resource_scope']['memory_bytes'] = 4294967297
            with self.assertRaisesRegex(ContractError, 'Mathematical isolated worker resource scope differs'):
                qualification._validate_mathematical_worker_receipts(forged, output, worker)
            for update in ({'recipe': 'OPICA_LEAN_ISOLATED_V1'}, {'capability': 'NATIVE_DEVELOPMENT_ONLY'},
                           {'command': command + ['--extra']}, {'resource_status': 'RESOURCE_EXHAUSTED'},
                           {'exit_code': 1}, {'log_sha256': '0' * 64},
                           {'resource_scope': {'mode': 'NATIVE_DEVELOPMENT_ONLY'}}):
                with self.subTest(update=update):
                    forged = copy.deepcopy(base); forged['module_records'][0]['native'].update(update)
                    forged['module_records'][0]['argv'] = forged['module_records'][0]['native']['command']
                    with self.assertRaises(ContractError):
                        qualification._validate_mathematical_worker_receipts(forged, output, worker)

    def test_original_acceptance_census_has_every_numbered_method_once(self):
        original = load_bytes((R4 / "BASELINE_ACCEPTANCE_MATRIX.json").read_bytes())["tests"]
        methods = [row for row in discover_methods() if row["case"] is not None]
        self.assertEqual(len(original), 117)
        self.assertEqual(len(methods), 117)
        self.assertEqual(Counter(row["case"] for row in methods), Counter(row["id"] for row in original))
        self.assertEqual(len({row["method"] for row in methods}), 117)

    def test_all_thirteen_work_packages_remain_explicit(self):
        packages = load_bytes((R4 / "WORK_PACKAGES.json").read_bytes())["packages"]
        self.assertEqual([row["id"] for row in packages], ["R4-" + str(i).zfill(2) for i in range(13)])
        self.assertTrue(all(row.get("name") and row.get("implementation") and row.get("acceptance_authority")
                            for row in packages))

    def test_every_lane_uses_its_own_source_identity(self):
        profile = load_bytes(cli.PROFILE.read_bytes())
        self.assertEqual(set(ROUND4_LANES), set(REQUIRED_LANES))
        self.assertEqual(len(ROUND4_LANES), 11)
        self.assertEqual(profile["required_input_lanes"], list(ROUND4_LANES))
        requested = {"requested_commit": "a" * 40, "requested_tree": "b" * 40}
        provider = configuration()
        for lane in REQUIRED_LANES:
            with self.subTest(lane=lane):
                row = cli.lane_expected(lane, requested)
                self.assertEqual(row["id"], lane)
                if lane == "PARENT_REGRESSION":
                    self.assertEqual(row, {"id": lane, "scope": "FROZEN_BASELINE",
                                           "checked": {"commit": BASE, "tree": BASE_TREE}})
                elif lane == "PROVIDER_SELECTED":
                    self.assertEqual(row, {"id": lane, "scope": "SELECTED_PROVIDER", "checked": {
                        "repository": provider["repository"], "commit": provider["commit"],
                        "toolchain": provider["toolchain"]}})
                else:
                    self.assertEqual(row, {"id": lane, "scope": "CURRENT_HOST", "checked": {
                        "commit": requested["requested_commit"], "tree": requested["requested_tree"]}})
        with self.assertRaises(ContractError):
            cli.lane_expected("ACCEPTANCE", requested)

    def test_source_report_mismatch_stops_before_any_heavy_checker(self):
        current = {"schema": "SOURCE_IDENTITY_FIXTURE_ONLY_NOT_PROOF", "commit": "c" * 40}
        changed = {**current, "commit": "d" * 40}
        for source, after in ((current, changed), (changed, changed)):
            with self.subTest(source=source, after=after), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                files = {}
                for name, row in (("results.json", {}), ("source.json", source), ("source-after.json", after)):
                    path = root / name
                    path.write_bytes(canonical_bytes(row))
                    files[name] = path
                with patch.object(cli, "validate_descendant", return_value=current) as inspector, \
                     patch.object(cli, "worker_from_environment", side_effect=AssertionError("native worker must not run")) as worker, \
                     patch("research.RHRC.integration.opica_composition.qualification.check_current_compatibility",
                           side_effect=AssertionError("heavy native checker must not run")) as heavy:
                    with self.assertRaisesRegex(ContractError, "Lane source differs"):
                        cli.verify_lane_raw({"id": "CURRENT_COMPATIBILITY"}, {}, files, REPO, root / "independent")
                    inspector.assert_called_once_with(REPO, require_clean=True)
                    worker.assert_not_called()
                    heavy.assert_not_called()
                    self.assertFalse((root / "independent").exists())

    def test_real_support_runner_yields_all_forty_nine_tests_in_both_modes(self):
        expected = load_bytes((SUPPORT / "EXPECTED_TEST_IDS.json").read_bytes())
        self.assertEqual(len(expected), 49)
        with tempfile.TemporaryDirectory() as tmp:
            rows = cli.support_regressions(REPO, Path(tmp))
            self.assertEqual(len(rows), 2)
            for row, optimized in zip(rows, (False, True)):
                receipt = row["receipt"]
                self.assertEqual(row["command"]["exit_code"], 0)
                self.assertEqual(receipt["test_ids"], sorted(expected))
                self.assertEqual(receipt["executed"], 49)
                self.assertIs(receipt["optimized"], optimized)

    def test_support_receipt_rejects_empty_skipped_or_wrong_mode_wrappers(self):
        # Synthetic failures test parsing only; no synthetic success is accepted.
        base = {"status": "PASS", "executed": 49, "expected": 49, "skips": 0, "errors": 0,
                "failures": 0, "expected_failures": 0, "unexpected_successes": 0, "optimized": False}
        for update in ({"executed": 0}, {"skips": 1}, {"optimized": True}):
            with self.subTest(update=update), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                def rejected_wrapper(repo, argv, output, label):
                    path = output / (label + ".log")
                    path.write_text(json.dumps({**base, **update}) + "\n", encoding="utf-8")
                    return {"log": path.name, "exit_code": 0}
                with patch.object(cli, "run_command", side_effect=rejected_wrapper):
                    with self.assertRaises(ContractError):
                        cli.support_regressions(REPO, root)


if __name__ == "__main__":
    unittest.main()
