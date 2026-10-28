"""Real untemplated search terms and independent native expected-type checks."""
import unittest
from pathlib import Path
from research.RHRC.integration.opica_composition.canonical import require,load_bytes
from research.RHRC.integration.opica_composition.contracts import StatementInventory,GrammarProfile,SearchBudget
from research.RHRC.integration.opica_composition.executor import run_worker
from research.RHRC.integration.opica_composition.composition_search import retrieve
from research.RHRC.integration.opica_composition.tests.test_executor import (
    native_context,target_spec,fresh,attempt,independently_verify,local)

MODULE='Zeta23.RHRC.OpicaComposition.SearchExamples'


def candidates(name):
    target=target_spec(name,MODULE)
    worker,snapshot,_=native_context()
    output=fresh('search-type');output.mkdir()
    (output/'SearchType.lean').write_text('import '+MODULE+'\nimport Zeta23.RHRC.OpicaComposition.Export\nrun_cmd Zeta23.RHRC.OpicaComposition.exportTarget `'+MODULE+'.'+name+' "value"\n',encoding='utf8')
    result=run_worker(worker,output,'SearchType.lean','SearchType.olean',SearchBudget())
    require(result['exit_code']==0 and result['resource_status'] is None,'independent search target export failed')
    rows=[line.split(b'\t',1)[1] for line in (output/'SearchType.lean.log').read_bytes().splitlines() if line.startswith(b'OPICA_TARGET\t')]
    require(len(rows)==1,'missing independent target expression')
    expected=load_bytes(rows[0])
    inventory=StatementInventory(snapshot.generation,[],'a'*64)
    plans,complete,provenance=retrieve(inventory,target,GrammarProfile([],[]),SearchBudget(),expected)
    return target,plans,complete,provenance


class NativeCompositionSearchTests(unittest.TestCase):
    def prove(self,name):
        target,plans,_,record=candidates(name)
        self.assertTrue(plans,'general search found no candidate for '+name)
        self.assertFalse(record['kernel_acceptance'])
        result=attempt(target,plans[0]['term_plan'])
        self.assertEqual(result.status,'PROVED_CONDITIONAL',result.reason)
        self.assertEqual(independently_verify(result,target).status,'PROVED_CONDITIONAL')

    def test_native_untemplated_chain(self):
        self.prove('ChainTarget')

    def test_native_dependent_witness_chain(self):
        self.prove('DependentChainTarget')

    def test_native_existential_elimination(self):
        self.prove('ExistentialChainTarget')

    def test_native_complete_disjunction(self):
        self.prove('DisjunctiveChainTarget')

    def test_native_changed_witness_is_rejected(self):
        target,plans,complete,_=candidates('MismatchedWitnessTarget')
        self.assertEqual(plans,[])
        self.assertTrue(complete)
        wrong={'tag':'app','function':local(6),'arguments':[local(3),local(5)]}
        self.assertEqual(attempt(target,wrong).status,'TYPE_REJECTED_THIS_APPLICATION')


if __name__=='__main__':unittest.main()
