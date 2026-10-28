"""Behavioral controls for scope, dependent arguments and bounded search."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest
from dataclasses import replace
from research.RHRC.integration.opica_composition.canonical import ContractError
from research.RHRC.integration.opica_composition.contracts import StatementInventory, TargetSpec, GrammarProfile, SearchBudget, PER_ATTEMPT_GATES
from research.RHRC.integration.opica_composition.inventory import expression_hash
from research.RHRC.integration.opica_composition.composition_search import retrieve
from research.RHRC.integration.opica_composition.proposals import used_constant_ids


def name(text):
    value = ['anonymous']
    for part in text.split('.'):
        value = ['str',value,part]
    return value


def c(text): return ('const',text)
def b(index): return ('bvar',index)
def app(f,*args):
    for arg in args: f=('app',f,arg)
    return f
def arrow(domain,body,info='default'): return ('forall',info,domain,body)
def lam(domain,body): return ('lam','default',domain,body)


def dag(expr):
    rows, cache = [], {}
    def add(t):
        if t in cache: return str(cache[t])
        if t[0]=='const': row=['const',name(t[1]),[]]
        elif t[0]=='bvar': row=['bvar',str(t[1])]
        elif t[0]=='app': row=['app',add(t[1]),add(t[2])]
        elif t[0] in ('forall','lam'): row=[t[0],name('_'),t[1],add(t[2]),add(t[3])]
        else: raise ValueError(t)
        index=len(rows); rows.append(row); cache[t]=index
        return str(index)
    root=add(expr)
    return {'format':'LEAN_EXPR_DAG_V1','nodes':rows,'root':root}


def setup(target_expr, constants=(), budget=None, forbidden=()):
    target_dag=dag(target_expr)
    ids={n:hashlib.sha256(n.encode()).hexdigest() for n,_ in constants}
    rows=[{'declaration':n,'module':'SearchFixtures','type_expression':dag(t),'type_sha256':expression_hash(dag(t))} for n,t in constants]
    inventory=StatementInventory('a'*64,rows,'b'*64)
    target=TargetSpec('test','SearchFixtures.Target','SearchFixtures',expression_hash(target_dag),
        {ids[n]:n for n,_ in constants},['propext','Classical.choice','Quot.sound'],['SearchFixtures'],list(PER_ATTEMPT_GATES),forbidden_constants=list(forbidden))
    candidates,complete,provenance=retrieve(inventory,target,GrammarProfile([],[]),budget or SearchBudget(),target_dag)
    return candidates,complete,provenance,ids


class CompositionSearchTests(unittest.TestCase):
    def test_untemplated_two_step_chain(self):
        p,q,r=map(c,['P','Q','R'])
        rows,complete,proof,ids=setup(arrow(p,r),[('step1',arrow(p,q)),('step2',arrow(q,r))])
        expected={'tag':'app','function':{'tag':'const','constant_id':ids['step2']},'arguments':[
            {'tag':'app','function':{'tag':'const','constant_id':ids['step1']},'arguments':[{'tag':'local','binder_slot':0}]}]}
        self.assertIn(expected,[r['term_plan'] for r in rows])
        self.assertTrue(complete)
        self.assertFalse(proof['kernel_acceptance'])

    def test_dependent_witness_is_preserved(self):
        alpha,p,q=map(c,['Alpha','P','Q'])
        step=arrow(alpha,arrow(app(p,b(0)),app(q,b(1))))
        goal=arrow(alpha,arrow(app(p,b(0)),app(q,b(1))))
        rows,_,_,ids=setup(goal,[('step',step)])
        expected={'tag':'app','function':{'tag':'const','constant_id':ids['step']},'arguments':[
            {'tag':'local','binder_slot':0},{'tag':'local','binder_slot':1}]}
        self.assertIn(expected,[r['term_plan'] for r in rows])

    def test_other_witness_does_not_supply_property(self):
        alpha,p,q=map(c,['Alpha','P','Q'])
        step=arrow(alpha,arrow(app(p,b(0)),app(q,b(1))))
        # x y hx : P x, goal Q y. No equality/transport was supplied.
        goal=arrow(alpha,arrow(alpha,arrow(app(p,b(1)),app(q,b(1)))))
        rows,complete,_,_=setup(goal,[('step',step)])
        self.assertEqual(rows,[])
        self.assertTrue(complete)

    def test_existential_packet_is_eliminated_in_scope(self):
        alpha,p,r=map(c,['Alpha','P','R'])
        packet=app(c('Exists'),alpha,lam(alpha,app(p,b(0))))
        step=arrow(alpha,arrow(app(p,b(0)),r))
        rows,_,_,_=setup(arrow(packet,r),[('step',step)])
        self.assertTrue(any(x['term_plan']['tag']=='cases' for x in rows))

    def test_supplied_context_packet_precedes_backward_consumer(self):
        alpha,p,q,seed,result=map(c,['Carrier','FirstProperty','SecondProperty','Seed','Result'])
        packet=app(c('Exists'),alpha,lam(alpha,app(c('And'),app(p,b(0)),app(q,b(0)))))
        cap=arrow(alpha,arrow(app(p,b(0)),arrow(app(q,b(1)),c('False'))))
        # Both approved links are generic: produce a witness packet from the
        # supplied seed, then finish from the local cap at that same witness.
        constants=[('generic_packet',arrow(seed,packet)),('generic_finish',arrow(c('False'),result))]
        rows,_,record,ids=setup(arrow(seed,arrow(cap,result)),constants,
            SearchBudget(candidates=1,term_nodes=96,term_depth=32))
        expected={'tag':'let','value':{'tag':'app',
            'function':{'tag':'const','constant_id':ids['generic_packet']},
            'arguments':[{'tag':'local','binder_slot':0}]},
            'body':{'tag':'cases','value':{'tag':'local','binder_slot':2},'branches':[
                {'tag':'cases','value':{'tag':'local','binder_slot':4},'branches':[
                    {'tag':'app','function':{'tag':'const','constant_id':ids['generic_finish']},
                     'arguments':[{'tag':'app','function':{'tag':'local','binder_slot':1},
                         'arguments':[{'tag':'local','binder_slot':3},
                                      {'tag':'local','binder_slot':5},
                                      {'tag':'local','binder_slot':6}]}]}]}]}}
        self.assertIn(expected,[row['term_plan'] for row in rows])
        self.assertEqual(used_constant_ids(expected),set(ids.values()))
        self.assertLessEqual(record['states'],96)
        self.assertFalse(record['kernel_acceptance'])

    def test_conjunction_packet(self):
        p,q=map(c,['P','Q'])
        rows,_,_,_=setup(arrow(app(c('And'),p,q),q))
        self.assertTrue(any(x['term_plan']['tag']=='cases' for x in rows))

    def test_disjunction_requires_both_branches(self):
        p,q,r=map(c,['P','Q','R'])
        packet=app(c('Or'),p,q)
        rows,_,_,_=setup(arrow(packet,r),[('left',arrow(p,r))])
        self.assertEqual(rows,[])
        good,_,_,_=setup(arrow(packet,r),[('left',arrow(p,r)),('right',arrow(q,r))])
        self.assertTrue(any(x['term_plan']['tag']=='cases' and len(x['term_plan']['branches'])==2 for x in good))

    def test_budget_stop_is_not_unprovability(self):
        p,q,r=map(c,['P','Q','R'])
        rows,complete,record,_=setup(arrow(p,r),[('a',arrow(p,q)),('b',arrow(q,r))],SearchBudget(term_nodes=2))
        self.assertFalse(complete)
        self.assertEqual(record['stopping_reason'],'RESOURCE_EXHAUSTED')
        self.assertLessEqual(record['states'],record['maximum_states'])
        self.assertFalse(record['mathematical_exhaustiveness'])

    def test_forbidden_answer_is_not_retrieved(self):
        p= c('P')
        rows,_,_,ids=setup(p,[('answer',p)],forbidden=['answer'])
        self.assertEqual(rows,[])

    def test_cycles_terminate(self):
        p,q=map(c,['P','Q'])
        rows,complete,_,_=setup(arrow(p,q),[('loop',arrow(q,q))])
        self.assertEqual(rows,[])
        self.assertTrue(complete)

    def test_target_digest_cannot_be_replaced(self):
        p,q=map(c,['P','Q'])
        inventory=StatementInventory('a'*64,[],'b'*64)
        target=TargetSpec('test','T','M',expression_hash(dag(p)),{},[],['M'],list(PER_ATTEMPT_GATES))
        with self.assertRaises(ContractError):
            retrieve(inventory,target,GrammarProfile([],[]),SearchBudget(),dag(q))

    def test_shared_dag_retrieval_preserves_linear_work(self):
        # A shared app DAG of depth64 has65nodes, but its unfolded tree has
        # exponentially many nodes. A subprocess bounds a tuple-equality
        # regression without hanging the whole portable test runner.
        program=textwrap.dedent('''
            import hashlib,json
            from research.RHRC.integration.opica_composition.composition_search import retrieve
            from research.RHRC.integration.opica_composition.contracts import StatementInventory,TargetSpec,GrammarProfile,SearchBudget,PER_ATTEMPT_GATES
            from research.RHRC.integration.opica_composition.inventory import expression_hash
            nodes=[['const',['str',['anonymous'],'P'],[]]]
            for i in range(1,65):nodes.append(['app',str(i-1),str(i-1)])
            expr={'format':'LEAN_EXPR_DAG_V1','nodes':nodes,'root':'64'}
            sha=expression_hash(expr);cid=hashlib.sha256(b'provider').hexdigest()
            row={'declaration':'provider','module':'SearchFixtures','type_expression':expr,'type_sha256':sha}
            inv=StatementInventory('a'*64,[row],'b'*64)
            target=TargetSpec('shared','SearchFixtures.Target','SearchFixtures',sha,{cid:'provider'},[],['SearchFixtures'],list(PER_ATTEMPT_GATES))
            plans,complete,record=retrieve(inv,target,GrammarProfile([],[]),SearchBudget(term_nodes=128,wall_seconds=10),expr)
            print(json.dumps({'plans':len(plans),'complete':complete,'record':record}))
        ''')
        command=[sys.executable,'-B']
        if sys.flags.optimize:command.append('-O')
        completed=subprocess.run([*command,'-c',program],cwd=Path(__file__).resolve().parents[5],
            capture_output=True,text=True,timeout=15,check=True)
        result=json.loads(completed.stdout)
        self.assertEqual(result['plans'],1)
        self.assertTrue(result['complete'])
        self.assertLess(result['record']['type_work_units'],10000)
        self.assertLessEqual(result['record']['type_work_units'],result['record']['maximum_type_work_units'])
        self.assertFalse(result['record']['kernel_acceptance'])

    def test_deep_valid_dag_reports_resource_exhaustion(self):
        # This is a strict-valid closed expression DAG, not a proof claim.
        # Type processing must be bounded even before any proof candidate exists.
        nodes=[['const',name('F'),[]]]
        for i in range(1,1201):nodes.append(['app',str(i-1),'0'])
        expression={'format':'LEAN_EXPR_DAG_V1','nodes':nodes,'root':'1200'}
        sha=expression_hash(expression)
        target=TargetSpec('deep','SearchFixtures.Target','SearchFixtures',sha,{},[],
            ['SearchFixtures'],list(PER_ATTEMPT_GATES))
        rows,complete,record=retrieve(StatementInventory('a'*64,[],'b'*64),target,
            GrammarProfile([],[]),SearchBudget(term_nodes=1),expression)
        self.assertEqual(rows,[])
        self.assertFalse(complete)
        self.assertEqual(record['stopping_reason'],'RESOURCE_EXHAUSTED')
        self.assertFalse(record['mathematical_exhaustiveness'])
        self.assertFalse(record['kernel_acceptance'])
        self.assertLessEqual(record['type_work_units'],record['maximum_type_work_units']+1)


if __name__=='__main__': unittest.main()
