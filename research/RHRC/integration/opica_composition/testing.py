"""Exact, non-skipping unittest receipts for the reviewed lane inventory."""
from __future__ import annotations
import ast
import json
from pathlib import Path
import re
import subprocess
import sys
import unittest
from .canonical import require, canonical_bytes, load_bytes
from .snapshot import file_hash, _evidence_file

PACKAGE = 'research.RHRC.integration.opica_composition.tests'
TEST_ROOT = Path(__file__).parent/'tests'
INVENTORY = Path(__file__).parent/'EXPECTED_TESTS.json'
FAILURE_TAIL_BYTES = 8192


def _emit_failed_test_diagnostics(output,mode):
    """Fixed-path, no-follow, bounded tails; never interpret receipt log paths."""
    require(mode in {'normal','optimized'},'Known test mode required')
    for suffix in ('.json','.log','.driver.log'):
        name=mode+suffix
        try:
            with _evidence_file(output,name) as (stream,info):
                stream.seek(max(0,info.st_size-FAILURE_TAIL_BYTES))
                raw=stream.read(FAILURE_TAIL_BYTES)
            row={'authority':'DIAGNOSTIC_ONLY_NOT_ACCEPTANCE','file':name,
                 'bytes':info.st_size,'tail_bytes':len(raw),'truncated':info.st_size>len(raw),
                 'tail':raw.decode('utf-8',errors='replace')}
            # One escaped line cannot introduce workflow commands or control
            # characters from child output into the parent job log.
            sys.stderr.write('OPICA_TEST_DIAGNOSTIC_ONLY '+json.dumps(row,ensure_ascii=True)+'\n')
        except FileNotFoundError:continue
        except Exception as error:
            try:sys.stderr.write('OPICA_TEST_DIAGNOSTIC_ONLY_UNAVAILABLE '+name+' '+type(error).__name__+'\n')
            except (OSError,ValueError,AttributeError):pass

def discover_methods():
    result=[]
    for path in sorted(TEST_ROOT.glob('test_*.py')):
        tree=ast.parse(path.read_text(encoding='utf-8'))
        for cls in tree.body:
            if not isinstance(cls,ast.ClassDef): continue
            for method in cls.body:
                if isinstance(method,ast.FunctionDef) and method.name.startswith('test_'):
                    name=PACKAGE+'.'+path.stem+'.'+cls.name+'.'+method.name
                    match=re.fullmatch(r'test_t(\d+)',method.name)
                    result.append({'method':name,'case':('T'+match[1].zfill(2)) if match else None,
                                   'source_sha256':file_hash(path)})
    return result

def checked_inventory():
    expected=load_bytes(INVENTORY.read_bytes())
    actual=discover_methods()
    require(sorted(r['method'] for r in expected['tests'])==sorted(r['method'] for r in actual),
            'Exact complete test-method inventory differs')
    cases=[r['case'] for r in actual if r['case']]
    require(sorted(cases)==sorted('T'+str(i).zfill(2) for i in range(1,118)),
            'Required117 acceptance cases missing or duplicated')
    return expected

class ReceiptResult(unittest.TextTestResult):
    def startTest(self,test):
        super().startTest(test);self.executed_ids.append(test.id())

def run_tests(methods,output):
    require(methods and len(methods)==len(set(methods)),'Exact nonempty selected test methods required')
    output=Path(output);output.parent.mkdir(parents=True,exist_ok=True)
    suite=unittest.TestLoader().loadTestsFromNames(methods)
    with output.with_suffix('.log').open('w',encoding='utf-8') as stream:
        class Result(ReceiptResult):
            executed_ids=[]
        result=unittest.TextTestRunner(stream=stream,verbosity=2,resultclass=Result).run(suite)
    row={'schema':'OPICA_EXACT_TEST_RECEIPT_V1','status':'PASS' if result.wasSuccessful() and not result.skipped and
         not result.expectedFailures and not result.unexpectedSuccesses else 'FAIL',
         'optimized':not __debug__,'test_ids':sorted(result.executed_ids),'executed':result.testsRun,
         'expected':len(methods),'skips':len(result.skipped),'failures':len(result.failures),'errors':len(result.errors),
         'expected_failures':len(result.expectedFailures),'unexpected_successes':len(result.unexpectedSuccesses),
         'log_sha256':file_hash(output.with_suffix('.log'))}
    output.write_bytes(canonical_bytes(row)+b'\n')
    require(row['status']=='PASS' and row['test_ids']==sorted(methods),'Test lane failed: '+str(output))
    return row

def run_modes(lane,output,repo):
    expected=checked_inventory();methods=sorted(r['method'] for r in expected['tests'] if r['lane']==lane)
    require(methods,'Lane has no declared methods')
    output=Path(output);output.mkdir(parents=True,exist_ok=True);rows=[]
    for optimized in (False,True):
        mode='optimized' if optimized else 'normal'
        receipt=output/(mode+'.json')
        argv=[sys.executable,*(['-O'] if optimized else []),'-B','-m',__name__,
              '--lane',lane,'--receipt',str(receipt)]
        try:
            with receipt.with_suffix('.driver.log').open('wb') as stream:
                process=subprocess.run(argv,cwd=repo,stdout=stream,stderr=subprocess.STDOUT,timeout=30000)
            require(process.returncode==0,'Normal/optimized test process failed: '+str(receipt))
            rows.append(load_bytes(receipt.read_bytes()))
        except BaseException:
            try:_emit_failed_test_diagnostics(output,mode)
            except Exception:pass
            raise
    return rows

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--lane',required=True);p.add_argument('--receipt',required=True,type=Path)
    args=p.parse_args();inventory=checked_inventory()
    run_tests(sorted(r['method'] for r in inventory['tests'] if r['lane']==args.lane),args.receipt)
