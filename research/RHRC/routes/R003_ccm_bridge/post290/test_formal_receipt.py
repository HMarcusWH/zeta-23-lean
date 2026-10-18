#!/usr/bin/env python3
"""Compiler log mutations; synthetic logs supply no Lean theorem authority."""
import hashlib
import json
import unittest
from lean_expr_dag import validate_expression
from build_formal_receipt import (compiler_records, audit_roots,
    compiler_type_expressions, full_expression_record, validate_full_type_fields)


def synthetic_name(name):
    result = ['anonymous']
    for segment in name.split('.'):
        result = ['str', result, segment]
    return result


def synthetic_type_expression(name):
    """A fabricated closed protocol fixture, never a Lean type certificate."""
    return json.dumps({'format': 'LEAN_EXPR_DAG_V1', 'root': '0',
                       'nodes': [['const', synthetic_name(name), []]]},
                      ensure_ascii=False, separators=(',', ':'))


def synthetic_dag(nodes):
    """Fabricated graph for parser controls; no kernel typing is asserted."""
    return json.dumps({'format': 'LEAN_EXPR_DAG_V1', 'root': str(len(nodes) - 1),
                       'nodes': nodes}, ensure_ascii=False, separators=(',', ':'))


class CompilerLogMutations(unittest.TestCase):
    head='a'*40;tree='b'*40;roots={'Mock.theorem':'Mock.Module'}
    def fixture(self):
        return '\n'.join(['POST290_COMPILER_CONTEXT\t'+self.head+'\t'+self.tree,
            'RHRC_CANDIDATE_RESULT\tMock.theorem\tRESOLVED_UNIQUE\t1\tMock.theorem\tMock.Module\tTHEOREM\t0\tVALIDATOR_CONTROL_TYPE\tcontrol',
            'POST290_AXIOMS\tMock.theorem\tpropext,Classical.choice,Quot.sound'])
    def test_unique_current_complete_control(self):
        types,axioms=compiler_records(self.fixture(),self.roots,self.head,self.tree)
        self.assertEqual(list(types),['Mock.theorem']);self.assertEqual(len(axioms['Mock.theorem']),3)
    def test_stale_head_or_tree_rejected(self):
        for old,new in ((self.head,'c'*40),(self.tree,'d'*40)):
            with self.assertRaisesRegex(ValueError,'compiler head/tree context'):
                compiler_records(self.fixture().replace(old,new),self.roots,self.head,self.tree)
    def test_missing_or_duplicate_context_rejected(self):
        log=self.fixture()
        for altered in ('\n'.join(log.splitlines()[1:]),log+'\n'+log.splitlines()[0]):
            with self.assertRaises(ValueError):compiler_records(altered,self.roots,self.head,self.tree)
    def test_late_compiler_failure_rejected(self):
        with self.assertRaisesRegex(ValueError,'failed check'):
            compiler_records(self.fixture()+'\nZeta23/RHRC/Step123OutputBindings.lean:99:0: error: broken proof',self.roots,self.head,self.tree)
    def test_missing_or_duplicate_axiom_rejected(self):
        log=self.fixture()
        for altered in ('\n'.join(log.splitlines()[:-1]),log+'\n'+log.splitlines()[-1]):
            with self.assertRaises(ValueError):compiler_records(altered,self.roots,self.head,self.tree)
    def test_wrong_binding_or_axiom_rejected(self):
        log=self.fixture()
        for altered in (log.replace('Mock.Module','Other.Module'),log.replace('Quot.sound','sorryAx'),log.replace('THEOREM\t0','THEOREM\t1')):
            with self.assertRaises(ValueError):compiler_records(altered,self.roots,self.head,self.tree)
    def test_empty_scope_rejected(self):
        with self.assertRaisesRegex(ValueError,'empty compiler root scope'):
            compiler_records(self.fixture().splitlines()[0],{},self.head,self.tree)
    def test_constructor_requires_explicit_definition_kind(self):
        log=self.fixture().replace('THEOREM\t0','DEFINITION\t0')
        with self.assertRaisesRegex(ValueError,'identity/kind mismatch'):
            compiler_records(log,self.roots,self.head,self.tree)
        compiler_records(log,self.roots,self.head,self.tree,{'Mock.theorem':'DEFINITION'})
        with self.assertRaisesRegex(ValueError,'identity/kind mismatch'):
            compiler_records(self.fixture(),self.roots,self.head,self.tree,{'Mock.theorem':'DEFINITION'})
    def test_multiline_source_inventory_keeps_exact_kinds(self):
        source='''(``Mock.theorem, "Mock.Module", "THEOREM"),
        (``Mock.constructor,
          "Mock.Module", "DEF")'''
        roots,kinds=audit_roots(source)
        self.assertEqual(roots,{'Mock.theorem':'Mock.Module','Mock.constructor':'Mock.Module'})
        self.assertEqual(kinds,{'Mock.theorem':'THEOREM','Mock.constructor':'DEFINITION'})
    def test_real_binding_inventory_accepts_all_exact_kinds(self):
        from build_formal_receipt import AUDIT
        roots,kinds=audit_roots(AUDIT.read_text(encoding='utf-8'))
        self.assertGreaterEqual(len(roots),1248)
        names=[n for n in roots if n.startswith('Zeta23.RHRC.mc')]
        self.assertEqual(len(names),16)
        self.assertEqual(sum(kinds[n]=='DEFINITION' for n in names),8)
        self.assertEqual(sum(kinds[n]=='THEOREM' for n in names),8)

    def test_m07_05_exact_origin_is_defining_geometry_module(self):
        from build_formal_receipt import AUDIT
        roots,kinds=audit_roots(AUDIT.read_text(encoding='utf-8'))
        name='Zeta23.CCM.poleNeutralIndexEquiv'
        self.assertEqual(roots[name],'Zeta23.CCM.CanonicalPoleNeutralGeometry')
        self.assertEqual(kinds[name],'DEFINITION')
        self.assertNotEqual(roots[name],'Zeta23.CCM.CanonicalPoleNeutralCarrier')

    def test_m07_05_wrong_importing_module_rejected_by_compiler_receipt(self):
        name='Zeta23.CCM.poleNeutralIndexEquiv'
        module='Zeta23.CCM.CanonicalPoleNeutralGeometry'
        testlog='\n'.join([
            'POST290_COMPILER_CONTEXT\t'+self.head+'\t'+self.tree,
            'RHRC_CANDIDATE_RESULT\t'+name+'\tRESOLVED_UNIQUE\t1\t'+
            name+'\t'+module+'\tDEFINITION\t0\tEXACT_INDEX_EQUIV_TYPE\t-',
            'POST290_AXIOMS\t'+name+'\tpropext,Classical.choice,Quot.sound'
        ])
        roots={name:module}; kinds={name:'DEFINITION'}
        types,axioms=compiler_records(testlog,roots,self.head,self.tree,kinds)
        self.assertEqual(types[name],'EXACT_INDEX_EQUIV_TYPE')
        self.assertEqual(len(axioms[name]),3)
        importing='Zeta23.CCM.CanonicalPoleNeutralCarrier'
        with self.assertRaisesRegex(ValueError,'identity/kind mismatch'):
            compiler_records(testlog.replace(module,importing),roots,
                             self.head,self.tree,kinds)

    def test_source_kind_canonical_spelling(self):
        roots,kinds=audit_roots('''(``Mock.a, "Mock", "DEFINITION"),
            (``Mock.b, "Mock", "STRUCTURE")''')
        self.assertEqual(kinds,{'Mock.a':'DEFINITION','Mock.b':'INDUCTIVE'})

    def test_missing_duplicate_or_unknown_source_kind_rejected(self):
        for source in ['(``Mock.root, "Mock.Module")',
            '(``Mock.root, "Mock.Module", "UNREVIEWED")',
            '(``Mock.root, "Mock.Module", "DEF"), (``Mock.root, "Mock.Module", "DEF")']:
            with self.assertRaises(ValueError):audit_roots(source)


class FullTypeExpressionMutations(unittest.TestCase):
    """Synthetic protocol controls; these strings carry no Lean authority."""
    roots = {'Mock.witness': 'Mock.Module', 'Mock.data': 'Mock.Module',
             'Mock.Structure': 'Mock.Module'}
    kinds = {'Mock.witness': 'THEOREM', 'Mock.data': 'DEFINITION',
             'Mock.Structure': 'INDUCTIVE'}
    witness_expression = synthetic_dag([
        ['const', synthetic_name('ExistsUnique'), []],
        ['const', synthetic_name('Zeta23.CCM.NativeCompactPoleH2'), []],
        ['const', synthetic_name('True'), []],
        ['lam', synthetic_name('u'), 'default', '1', '2'],
        ['app', '0', '1'], ['app', '4', '3']])
    constructor_expression = synthetic_dag([
        ['const', synthetic_name('Nat'), []],
        ['const', synthetic_name('Mock.Structure'), []],
        ['forall', synthetic_name('value'), 'default', '0', '1']])

    def fixture(self):
        return '\n'.join([
            'POST290_TYPE_EXPR\tMock.witness\t' + self.witness_expression,
            'POST290_TYPE_EXPR\tMock.data\t' + synthetic_dag([['sort', ['zero']]]),
            'POST290_TYPE_EXPR\tMock.Structure\t' + synthetic_dag([['sort', ['succ', ['zero']]]]),
            'POST290_CONSTRUCTOR_TYPE_EXPR\tMock.Structure\tMock.Structure.mk\t'
            + self.constructor_expression])

    def parse(self, log):
        return compiler_type_expressions(log, self.roots, self.kinds)

    def test_full_witness_and_constructor_types_retained(self):
        expressions, constructors = self.parse(self.fixture())
        self.assertEqual(set(expressions), set(self.roots))
        self.assertEqual(expressions['Mock.witness'], self.witness_expression)
        self.assertIn('NativeCompactPoleH2', expressions['Mock.witness'])
        self.assertEqual(set(constructors), {'Mock.Structure'})
        self.assertIn('"forall"', constructors['Mock.Structure']['Mock.Structure.mk'])
        self.assertIn('"value"', constructors['Mock.Structure']['Mock.Structure.mk'])
        record = full_expression_record(expressions['Mock.witness'])
        self.assertEqual(record['full_type_expr_format'], 'LEAN_EXPR_DAG_V1')
        self.assertEqual(record['full_type_expr_sha256'], hashlib.sha256(self.witness_expression.encode()).hexdigest())

    def test_additive_expression_protocol_keeps_historical_type_and_hash(self):
        original = CompilerLogMutations().fixture().replace('VALIDATOR_CONTROL_TYPE', '∃! u, True')
        roots = CompilerLogMutations.roots
        kinds = {'Mock.theorem': 'THEOREM'}
        supplemented = original + '\nPOST290_TYPE_EXPR\tMock.theorem\t' + self.witness_expression
        old_types, old_axioms = compiler_records(original, roots, 'a' * 40, 'b' * 40)
        new_types, new_axioms = compiler_records(supplemented, roots, 'a' * 40, 'b' * 40)
        expressions, constructors = compiler_type_expressions(supplemented, roots, kinds)
        self.assertEqual((old_types, old_axioms), (new_types, new_axioms))
        self.assertEqual(hashlib.sha256(old_types['Mock.theorem'].encode()).hexdigest(),
                         hashlib.sha256(new_types['Mock.theorem'].encode()).hexdigest())
        self.assertIn('NativeCompactPoleH2', expressions['Mock.theorem'])
        self.assertEqual(constructors, {})

    def test_missing_duplicate_unexpected_or_empty_root_expression_rejected(self):
        log = self.fixture()
        first = log.splitlines()[0]
        mutants = ['\n'.join(log.splitlines()[1:]), log + '\n' + first,
                   log + '\nPOST290_TYPE_EXPR\tMock.unknown\tSYNTHETIC_EXPR',
                   log.replace(self.witness_expression, ''),
                   log.replace(self.witness_expression, '   ')]
        for altered in mutants:
            with self.subTest(log=altered), self.assertRaises(ValueError):
                self.parse(altered)

    def test_missing_duplicate_unexpected_or_empty_constructor_rejected(self):
        log = self.fixture()
        constructor = log.splitlines()[-1]
        mutants = ['\n'.join(log.splitlines()[:-1]), log + '\n' + constructor,
                   log.replace('POST290_CONSTRUCTOR_TYPE_EXPR\tMock.Structure\t',
                               'POST290_CONSTRUCTOR_TYPE_EXPR\tMock.unknown\t'),
                   log.replace('POST290_CONSTRUCTOR_TYPE_EXPR\tMock.Structure\t',
                               'POST290_CONSTRUCTOR_TYPE_EXPR\tMock.data\t'),
                   log.replace('Mock.Structure.mk\t', '\t'),
                   log[:log.rfind('\t') + 1]]
        for altered in mutants:
            with self.subTest(log=altered), self.assertRaises(ValueError):
                self.parse(altered)

    def test_multiple_real_constructor_names_allowed(self):
        log = self.fixture() + '\nPOST290_CONSTRUCTOR_TYPE_EXPR\tMock.Structure\tMock.Structure.other\t' + synthetic_type_expression('Mock.OtherCtor')
        _, constructors = self.parse(log)
        self.assertEqual(len(constructors['Mock.Structure']), 2)

    def test_same_constructor_cannot_be_claimed_by_two_owners(self):
        roots = dict(self.roots, **{'Mock.Other': 'Mock.Module'})
        kinds = dict(self.kinds, **{'Mock.Other': 'INDUCTIVE'})
        log = (self.fixture() + '\nPOST290_TYPE_EXPR\tMock.Other\tSYNTHETIC_OTHER_TYPE'
               '\nPOST290_CONSTRUCTOR_TYPE_EXPR\tMock.Other\tMock.Structure.mk\tSYNTHETIC_OTHER_CTOR')
        with self.assertRaisesRegex(ValueError, 'duplicate constructor'):
            compiler_type_expressions(log, roots, kinds)

    def test_malformed_protocol_fields_rejected(self):
        for suffix in ['POST290_TYPE_EXPR\tMock.witness',
                       'POST290_TYPE_EXPR\tMock.witness\tEXPR\tUNEXPECTED',
                       'POST290_CONSTRUCTOR_TYPE_EXPR\tMock.Structure\tMock.Structure.mk',
                       'POST290_CONSTRUCTOR_TYPE_EXPR\tMock.Structure\tMock.Structure.mk\tEXPR\tUNEXPECTED']:
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                self.parse(self.fixture() + '\n' + suffix)

    def test_empty_or_mismatched_scope_rejected(self):
        for roots, kinds in [({}, {}), (self.roots, {}),
                             (self.roots, dict(self.kinds, **{'Mock.witness': 'AXIOM'}))]:
            with self.subTest(kinds=kinds), self.assertRaises(ValueError):
                compiler_type_expressions(self.fixture(), roots, kinds)

    def test_full_type_consumer_fields_accept_exact_ast(self):
        for kind, constructors in [('THEOREM', []), ('DEFINITION', []),
                                   ('INDUCTIVE', [dict(constructor='Mock.Structure.mk',
                                        **full_expression_record(synthetic_type_expression('Mock.Ctor')))])]:
            row = dict(declaration_kind=kind, structure_constructor_types=constructors,
                       **full_expression_record(self.witness_expression))
            self.assertIsNone(validate_full_type_fields(row))

    def test_full_type_consumer_fields_reject_missing_or_tampered_data(self):
        from copy import deepcopy
        original = dict(declaration_kind='THEOREM', structure_constructor_types=[],
                        **full_expression_record(self.witness_expression))
        mutations = [lambda r: r.pop('full_type_expr'),
                     lambda r: r.update(full_type_expr=''),
                     lambda r: r.update(full_type_expr_sha256='0' * 64),
                     lambda r: r.update(full_type_expr_format='PRETTY_TYPE'),
                     lambda r: r.update(declaration_kind='AXIOM'),
                     lambda r: r.pop('structure_constructor_types'),
                     lambda r: r.update(structure_constructor_types={}),
                     lambda r: r.update(structure_constructor_types=[dict(
                         constructor='Mock.Structure.mk', **full_expression_record(synthetic_type_expression('Mock.Ctor')))])]
        for mutate in mutations:
            row = deepcopy(original)
            mutate(row)
            with self.subTest(row=row), self.assertRaises(ValueError):
                validate_full_type_fields(row)

    def test_full_type_consumer_fields_reject_bad_constructor_inventory(self):
        from copy import deepcopy
        original = dict(declaration_kind='INDUCTIVE', structure_constructor_types=[
            dict(constructor='Mock.Structure.mk', **full_expression_record(synthetic_type_expression('Mock.Ctor')))],
            **full_expression_record(synthetic_type_expression('Mock.Structure')))
        mutations = [lambda r: r.update(structure_constructor_types=[]),
                     lambda r: r['structure_constructor_types'].append(deepcopy(r['structure_constructor_types'][0])),
                     lambda r: r['structure_constructor_types'][0].update(constructor=''),
                     lambda r: r['structure_constructor_types'][0].update(full_type_expr=''),
                     lambda r: r['structure_constructor_types'][0].update(full_type_expr_sha256='0' * 64),
                     lambda r: r['structure_constructor_types'][0].update(full_type_expr_format='PRETTY_TYPE'),
                     lambda r: r['structure_constructor_types'].append(dict(
                         constructor='Mock.Structure.aa', **full_expression_record(synthetic_type_expression('Mock.Ctor'))))]
        for mutate in mutations:
            row = deepcopy(original)
            mutate(row)
            with self.subTest(row=row), self.assertRaises(ValueError):
                validate_full_type_fields(row)


class LeanTypeDAGControls(unittest.TestCase):
    """Protocol and resource controls; synthetic graphs are not Lean proofs."""

    def test_sharing_does_not_expand_exponential_expression(self):
        nodes = [['const', synthetic_name('Mock.leaf'), []]]
        for _ in range(10000):
            previous = str(len(nodes) - 1)
            nodes.append(['app', previous, previous])
        result = validate_expression(synthetic_dag(nodes))
        self.assertEqual(result['unique_nodes'], 10001)
        self.assertIs(result['closed'], True)

    def test_binder_scope_is_checked_without_expanding_sharing(self):
        for binder in ('default', 'implicit', 'strictImplicit', 'instImplicit'):
            nodes = [['sort', ['zero']], ['bvar', '0'],
                     ['forall', synthetic_name('x'), binder, '0', '1']]
            self.assertTrue(validate_expression(synthetic_dag(nodes))['closed'])
            nodes[1][1] = '1'
            with self.assertRaisesRegex(ValueError, 'loose bound'):
                validate_expression(synthetic_dag(nodes))
        # A binder does not bind occurrences in its own domain.
        with self.assertRaisesRegex(ValueError, 'loose bound'):
            validate_expression(synthetic_dag([
                ['bvar', '0'], ['forall', synthetic_name('x'), 'default', '0', '0']]))

    def test_all_payload_kinds_and_metadata_are_retained(self):
        name = ['num', synthetic_name('Mock'), '123456789012345678901234567890']
        substring = ['substring', '\tβ\n', '0', '4']
        source = ['original', substring, '2', substring, '4']
        syntaxes = [
            ['missing'], ['atom', ['none'], '\tβ\n'],
            ['node', ['synthetic', '0', '9', True], name, [['missing']]],
            ['ident', source, substring, name,
             [['namespace', name], ['decl', name, ['field1', 'field2']]]]]
        values = [['string', '\tβ\n'], ['bool', False], ['name', name],
                  ['nat', '123456789012345678901234567890'], ['int', '-42']]
        values.extend(['syntax', syntax] for syntax in syntaxes)
        metadata = [[synthetic_name('Mock.key' + str(i)), value]
                    for i, value in enumerate(values)]
        nodes = [
            ['const', name, [['max', ['succ', ['zero']],
                              ['imax', ['param', name], ['zero']]]]],
            ['nat', '123456789012345678901234567890'], ['app', '0', '1'],
            ['string', '\tβ\n'], ['app', '2', '3'], ['bvar', '0'],
            ['let', name, '0', '4', '5', False],
            ['lam', name, 'instImplicit', '0', '6'],
            ['proj', name, '123456789012345678901234567890', '7'],
            ['mdata', metadata, '8']]
        self.assertEqual(validate_expression(synthetic_dag(nodes))['unique_nodes'], 10)

    def test_bad_topology_closedness_and_node_shapes_rejected(self):
        const = ['const', synthetic_name('Mock.c'), []]
        bad_nodes = [[], [['bvar', '0']], [['fvar', synthetic_name('x')]],
                     [['mvar', synthetic_name('x')]],
                     [const, ['app', '0', '1']], [const, ['app', '0', '99']],
                     [const, ['app', '0', '-1']], [const, ['app', '0', '00']],
                     [const, ['app', '0', 0]], [const, ['app', '0']],
                     [const, const], [const, const, ['app', '0', '1']],
                     [['nat', 2]], [['nat', '01']],
                     [['sort', ['mvar', synthetic_name('u')]]],
                     [['const', ['num', ['anonymous'], '-1'], []]],
                     [const, ['forall', synthetic_name('x'), 'unknown', '0', '0']],
                     [const, ['let', synthetic_name('x'), '0', '0', '0', 1]],
                     [const, ['proj', synthetic_name('S'), '-1', '0']],
                     [const, ['mdata', [[synthetic_name('k'), ['int', '-0']]], '0']],
                     [const, ['mdata', [[synthetic_name('k'), ['bool', 1]]], '0']],
                     [const, ['mdata', [[synthetic_name('k'), ['syntax',
                         ['ident', ['none'], ['substring', '', '0', '0'],
                          synthetic_name('x'), [['unknown', synthetic_name('x')]]]]]], '0']]]
        for nodes in bad_nodes:
            with self.subTest(nodes=nodes), self.assertRaises(ValueError):
                validate_expression(synthetic_dag(nodes))

    def test_malformed_json_format_root_and_duplicate_keys_rejected(self):
        good = json.loads(synthetic_type_expression('Mock.c'))
        from copy import deepcopy
        for mutate in (lambda d: d.update(format='LEAN_EXPR_REPR_V1'),
                       lambda d: d.update(root=0), lambda d: d.update(root='00'),
                       lambda d: d.update(root='2'), lambda d: d.update(extra=True)):
            data = deepcopy(good)
            mutate(data)
            with self.assertRaises(ValueError):
                validate_expression(json.dumps(data))
        for expression in ('SYNTHETIC_REPR_NOT_A_DAG', '{}', '[]', 'null',
                           '{"format":"LEAN_EXPR_DAG_V1","root":"0","root":"0","nodes":[]}',
                           '{"format":NaN,"root":"0","nodes":[]}', '{'):
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                validate_expression(expression)

    def test_malformed_graph_rejected_even_with_recomputed_hash(self):
        expression = synthetic_dag([['bvar', '0']])
        row = dict(declaration_kind='THEOREM', structure_constructor_types=[],
                   full_type_expr=expression,
                   full_type_expr_sha256=hashlib.sha256(expression.encode()).hexdigest(),
                   full_type_expr_format='LEAN_EXPR_DAG_V1')
        with self.assertRaises(ValueError):
            validate_full_type_fields(row)


if __name__=='__main__':unittest.main()
