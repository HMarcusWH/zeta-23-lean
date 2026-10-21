from __future__ import annotations
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest
import tempfile

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('opica_receipt', HERE/'build_receipt.py')
receipt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(receipt)


class ReceiptMutations(unittest.TestCase):
    def setUp(self):
        self.name = 'Zeta23.OPICA.fixture'
        self.module = 'Zeta23.OPICA.LocalObstruction'
        self.expression = json.dumps({'format':'LEAN_EXPR_DAG_V1','root':'0',
            'nodes':[['const',['str',['anonymous'],'True'],[]]]},separators=(',',':'))
        self.root = {'id':'X','full_name':self.name,'module':self.module,'kind':'THEOREM',
            'expected_type_sha256':hashlib.sha256(self.expression.encode()).hexdigest()}
        self.lines = [f'RHRC_CANDIDATE_RESULT\tX\tRESOLVED_UNIQUE\t1\t{self.name}\t{self.module}\tTHEOREM\t0\tTrue\t-',
            f'OPICA_DECL\t{self.name}\t{self.module}\tTHEOREM\t{self.expression}\t',
            'OPICA_PUBLIC_COUNT\t1',f'RHKG_DEP_DECL\t{self.name}\t{self.module}\tTHEOREM\t0',
            *[f'RHKG_DEP_CHANNEL\t{self.name}\t{channel}' for channel in ('TYPE','VALUE','STRUCTURE')], 'OPICA_COMPLETE\t1']

    def parse(self):
        return receipt.parse_compiler_output('\n'.join(self.lines),[self.root])

    def test_complete_fixture(self):
        self.assertEqual(len(self.parse()['declarations']),1)

    def test_missing_root(self):
        self.lines.pop(1)
        with self.assertRaises(ValueError): self.parse()

    def test_duplicate_root(self):
        self.lines.append(self.lines[1])
        with self.assertRaises(ValueError): self.parse()

    def test_wrong_kind(self):
        self.lines[1] = self.lines[1].replace('\tTHEOREM\t','\tDEFINITION\t')
        with self.assertRaisesRegex(ValueError,'kind mismatch'): self.parse()

    def test_wrong_module(self):
        self.lines[1] = self.lines[1].replace(self.module,'Zeta23.OPICA.EnergyRate')
        with self.assertRaisesRegex(ValueError,'module/kind mismatch'): self.parse()

    def add_public(self, name, module=None, kind='THEOREM'):
        module = self.module if module is None else module
        self.lines[2] = 'OPICA_PUBLIC_COUNT\t2'
        extra = [f'OPICA_DECL\t{name}\t{module}\t{kind}\t{self.expression}\t',
            f'RHKG_DEP_DECL\t{name}\t{module}\t{kind}\t0',
            *[f'RHKG_DEP_CHANNEL\t{name}\t{channel}' for channel in ('TYPE','VALUE','STRUCTURE')]]
        self.lines[-1:-1] = extra
        self.lines[-1] = 'OPICA_COMPLETE\t2'

    def test_generated_constructor_congruence_is_enumerated_and_audited(self):
        name = 'ContDiffBump.mk.congr_simp'
        module = 'Zeta23.OPICA.SignedHeatSeparator'
        self.add_public(name, module)
        result = self.parse()
        helper = next(item for item in result['declarations'] if item['name'] == name)
        self.assertEqual(helper['module'], module)
        self.assertEqual(helper['kind'], 'THEOREM')
        self.assertEqual(helper['type_expression'], json.loads(self.expression))
        self.assertEqual(helper['axioms'], [])
        self.assertEqual(len(result['dependencies']), 6)

    def test_generated_congruence_cannot_bypass_axiom_audit(self):
        name = 'ContDiffBump.mk.congr_simp'
        self.add_public(name)
        index = next(i for i, line in enumerate(self.lines) if line.startswith('OPICA_DECL\t'+name+'\t'))
        self.lines[index] += 'sorryAx'
        with self.assertRaisesRegex(ValueError, 'unadmitted'): self.parse()

    def test_generated_congruence_requires_theorem_kind(self):
        for kind in ('DEFINITION', 'OPAQUE', 'CONSTRUCTOR', 'RECURSOR'):
            with self.subTest(kind=kind):
                self.setUp()
                self.add_public('ContDiffBump.mk.congr_simp', kind=kind)
                with self.assertRaisesRegex(ValueError, 'foreign declaration namespace'): self.parse()

    def test_generated_congruence_suffix_is_exact(self):
        for name in ('ContDiffBump.mk.other', 'ContDiffBump.mk.congr_simp_extra',
                'ContDiffBump.mk.not_congr_simp', 'ContDiffBump.mk.congr_simp.recursor'):
            with self.subTest(name=name):
                self.setUp()
                self.add_public(name)
                with self.assertRaisesRegex(ValueError, 'foreign declaration namespace'): self.parse()

    def test_generated_congruence_requires_exact_mathematical_module_ownership(self):
        for module in ('Mathlib.Analysis.Calculus.BumpFunction.Basic',
                'Zeta23.OPICA.Other', 'Zeta23.OPICA.Validation', 'Zeta23.RHRC.OpicaBindings'):
            with self.subTest(module=module):
                self.setUp()
                self.add_public('ContDiffBump.mk.congr_simp', module)
                with self.assertRaisesRegex(ValueError, 'foreign defining module'): self.parse()

    def test_unknown_public_module_is_rejected_even_in_opica_namespace(self):
        self.add_public('Zeta23.OPICA.extra', 'Zeta23.OPICA.Other')
        with self.assertRaisesRegex(ValueError, 'foreign defining module'): self.parse()

    def test_generated_congruence_cannot_replace_primary_namespace(self):
        name = 'ContDiffBump.mk.congr_simp'
        self.root['full_name'] = name
        self.lines = [line.replace(self.name, name) for line in self.lines]
        with self.assertRaisesRegex(ValueError, 'foreign primary root namespace'): self.parse()

    def test_generated_congruence_public_metadata_stays_source_bound(self):
        name = 'ContDiffBump.mk.congr_simp'
        self.add_public(name)
        index = next(i for i, line in enumerate(self.lines) if line.startswith('RHKG_DEP_DECL\t'+name+'\t'))
        self.lines[index] = self.lines[index].replace(self.module, 'Zeta23.OPICA.EnergyRate')
        with self.assertRaisesRegex(ValueError, 'metadata mismatch'): self.parse()

    def test_generated_foreign_name_still_requires_all_project_channels(self):
        name = 'ContDiffBump.mk.congr_simp'
        self.add_public(name)
        self.lines.remove(f'RHKG_DEP_CHANNEL\t{name}\tVALUE')
        with self.assertRaisesRegex(ValueError, 'incomplete project dependency channels'): self.parse()

    def test_extra_axiom(self):
        self.lines[1] += 'sorryAx'
        with self.assertRaisesRegex(ValueError,'unadmitted'): self.parse()

    def test_native_evaluation_trust_extension(self):
        self.lines[1] += 'Lean.ofReduceBool'
        with self.assertRaisesRegex(ValueError,'unadmitted'): self.parse()

    def test_truncated_dag(self):
        self.lines[1] = self.lines[1].replace(self.expression,self.expression[:-1])
        with self.assertRaises(ValueError): self.parse()

    def test_hidden_typeclass_premise_changes_reviewed_type(self):
        changed = json.dumps({'format':'LEAN_EXPR_DAG_V1','root':'1',
            'nodes':[['const',['str',['anonymous'],'True'],[]],
                ['forall',['str',['anonymous'],'inst'],'instImplicit','0','0']]},separators=(',',':'))
        self.lines[1] = self.lines[1].replace(self.expression,changed)
        with self.assertRaisesRegex(ValueError,'expected type changed'): self.parse()

    def test_missing_structure_channel(self):
        self.lines.pop(-2)
        with self.assertRaisesRegex(ValueError,'channel'): self.parse()

    def test_fake_public_count(self):
        self.lines[2] = 'OPICA_PUBLIC_COUNT\t2'
        with self.assertRaisesRegex(ValueError,'enumeration'): self.parse()

    def test_missing_terminating_record(self):
        self.lines.pop()
        with self.assertRaisesRegex(ValueError,'completeness'):
            self.parse()

    def test_record_after_termination(self):
        self.lines.append('OPICA_PUBLIC_COUNT\t1')
        with self.assertRaisesRegex(ValueError,'after the terminating'):
            self.parse()

    def test_ambiguous_candidate(self):
        self.lines[0] = self.lines[0].replace('RESOLVED_UNIQUE','AMBIGUOUS_COMPILER_MATCH')
        with self.assertRaisesRegex(ValueError,'ambiguous'): self.parse()

    def add_dependency(self, name, module, *, expand=False):
        self.lines[4] += '\t'+name
        extra = [f'RHKG_DEP_DECL\t{name}\t{module}\tDEFINITION\t1']
        if expand:
            extra += [f'RHKG_DEP_CHANNEL\t{name}\t{c}' for c in ('TYPE','VALUE','STRUCTURE')]
        self.lines[-1:-1] = extra

    def test_reachable_project_helper_cannot_omit_entire_expansion(self):
        self.add_dependency('helper','Zeta23.OPICA.LocalObstruction')
        with self.assertRaisesRegex(ValueError,'incomplete project dependency channels'): self.parse()

    def test_reachable_private_project_helper_has_all_channels(self):
        self.add_dependency('helper','Zeta23.OPICA.LocalObstruction',expand=True)
        result = self.parse()
        self.assertEqual(len(result['dependencies']),6)
        self.assertEqual(len(result['dependency_declarations']),2)

    def test_one_missing_project_helper_channel_rejected(self):
        self.add_dependency('helper','Zeta23.OPICA.LocalObstruction',expand=True)
        self.lines.pop(-2)
        with self.assertRaisesRegex(ValueError,'incomplete project dependency channels'): self.parse()

    def test_external_constant_is_unexpanded_boundary(self):
        self.add_dependency('external','Mathlib.External')
        self.assertEqual(len(self.parse()['dependencies']),3)

    def test_external_boundary_cannot_be_expanded(self):
        self.add_dependency('external','Mathlib.External',expand=True)
        with self.assertRaisesRegex(ValueError,'external dependency boundary'): self.parse()

    def test_unreachable_helper_is_not_part_of_root_closure(self):
        self.add_dependency('helper','Zeta23.OPICA.LocalObstruction',expand=True)
        self.lines[4] = self.lines[4].removesuffix('\thelper')
        with self.assertRaisesRegex(ValueError,'unreachable'): self.parse()

    def test_public_dependency_metadata_is_source_bound(self):
        self.lines[3] = self.lines[3].replace(self.module,'Zeta23.OPICA.Other')
        with self.assertRaisesRegex(ValueError,'metadata mismatch'): self.parse()

    def test_malformed_protocol_marker_rejected(self):
        self.lines.insert(-1,'OPICA_UNKNOWN\t1')
        with self.assertRaisesRegex(ValueError,'malformed compiler protocol'): self.parse()

    def test_duplicate_dependency_metadata_rejected(self):
        self.lines.insert(-1,self.lines[3])
        with self.assertRaisesRegex(ValueError,'duplicate dependency declaration'): self.parse()

    def test_constructor_family_is_bound_to_structural_provenance(self):
        family,other,ctor = ['Zeta23.OPICA.'+n for n in ('Family','Other','Family.mk')]
        self.lines[2] = 'OPICA_PUBLIC_COUNT\t4'
        self.lines[-1] = 'OPICA_COMPLETE\t4'
        extra = []
        for name,kind in [(family,'INDUCTIVE'),(other,'INDUCTIVE'),(ctor,'CONSTRUCTOR')]:
            extra += [f'OPICA_DECL\t{name}\t{self.module}\t{kind}\t{self.expression}\t',
                f'RHKG_DEP_DECL\t{name}\t{self.module}\t{kind}\t0']
            for channel in ('TYPE','VALUE','STRUCTURE'):
                targets = '\t'+(other if name==ctor else ctor) if channel=='STRUCTURE' else ''
                extra.append(f'RHKG_DEP_CHANNEL\t{name}\t{channel}'+targets)
        extra.append(f'OPICA_CONSTRUCTOR\t{family}\t{ctor}\t{self.expression}')
        self.lines[-1:-1] = extra
        with self.assertRaisesRegex(ValueError,'constructor structural family mismatch'): self.parse()


class SharedReceiptMutations(unittest.TestCase):
    def setUp(self):
        fixture = ReceiptMutations()
        fixture.setUp()
        self.root = fixture.root
        self.payload = fixture.parse()
        self.manifest = json.loads((HERE/'BUILD_MANIFEST.json').read_text(encoding='utf-8'))
        targets = self.manifest['no_root_api_pollution']['required_build_targets']
        commands = [{'argv':argv,'log':log,'log_sha256':hashlib.sha256(log.encode()).hexdigest(),
            'exit_code':0,'seconds':0.1} for argv,log in [
                (['lake','env','lean','--version'],'lean-version.log'),
                (['lake','build',*targets],'build.log'),
                (['lake','env','lean','Zeta23/RHRC/OpicaBindings.lean'],'bindings.log')]]
        self.payload.update(schema='OPICA_COMPILER_RECEIPT_V1',status='COMPILER_VERIFIED',
            checked_commit='a'*40,checked_tree='b'*40,requested_head='a'*40,checkout_kind='PR_HEAD',
            requested_base=self.manifest['base_commit'],mathlib_commit=self.manifest['mathlib_commit'],
            lean='Lean (version 4.33.0-rc2, test)',commands=commands)

    def validate(self):
        receipt.validate_compiler_receipt(self.payload,self.manifest,[self.root])

    def add_public(self,name,kind,expression=None):
        expression = copy.deepcopy(expression or self.payload['declarations'][0]['type_expression'])
        encoded = json.dumps(expression,ensure_ascii=False,separators=(',',':'))
        record = {'name':name,'module':self.root['module'],'kind':kind,'axioms':[],
            'type_expression':expression,'type_sha256':hashlib.sha256(encoded.encode()).hexdigest(),
            'type_metrics':receipt.validate_expression(encoded)}
        self.payload['declarations'].append(record)
        self.payload['dependency_declarations'].append({'name':name,'module':self.root['module'],
            'kind':kind,'internal':False})
        self.payload['dependencies'] += [{'source':name,'channel':channel,'targets':[]}
            for channel in ('TYPE','VALUE','STRUCTURE')]
        return record

    def channel(self,name,channel):
        return next(item for item in self.payload['dependencies'] if item['source']==name and item['channel']==channel)

    def add_constructor(self):
        family,ctor = 'Zeta23.OPICA.Family','Zeta23.OPICA.Family.mk'
        self.add_public(family,'INDUCTIVE',{'format':'LEAN_EXPR_DAG_V1','root':'0','nodes':[['sort',['zero']]]})
        self.add_public(ctor,'CONSTRUCTOR',{'format':'LEAN_EXPR_DAG_V1','root':'0','nodes':[
            ['const',['str',['str',['str',['anonymous'],'Zeta23'],'OPICA'],'Family'],[]]]})
        self.payload['constructors'][ctor] = {'family':family,
            'type_expression':copy.deepcopy(self.payload['declarations'][-1]['type_expression'])}
        self.channel(family,'STRUCTURE')['targets'] = [ctor]
        self.channel(ctor,'TYPE')['targets'] = [family]
        self.channel(ctor,'STRUCTURE')['targets'] = [family]
        return family,ctor

    def test_full_valid_receipt_passes_shared_validation(self):
        self.validate()
        receipt.validate_checkout_identity(self.payload,'a'*40,'b'*40,[])

    def test_missing_public_dag_cannot_hide_behind_reviewed_digest(self):
        del self.payload['declarations'][0]['type_expression']
        with self.assertRaisesRegex(ValueError,'missing public declaration evidence'): self.validate()

    def test_changed_hidden_premise_cannot_reuse_old_digest(self):
        self.payload['declarations'][0]['type_expression'] = {'format':'LEAN_EXPR_DAG_V1','root':'1',
            'nodes':[['const',['str',['anonymous'],'True'],[]],
                ['forall',['str',['anonymous'],'inst'],'instImplicit','0','0']]}
        with self.assertRaisesRegex(ValueError,'DAG digest mismatch'): self.validate()

    def test_every_public_helper_digest_is_recomputed(self):
        record = self.add_public('Zeta23.OPICA.helper','DEFINITION')
        record['type_expression']['nodes'][0][1][-1] = 'False'
        with self.assertRaisesRegex(ValueError,'DAG digest mismatch'): self.validate()

    def test_malformed_dag_rejected_even_with_recomputed_digest(self):
        record = self.payload['declarations'][0]
        record['type_expression']['root'] = '99'
        record['type_sha256'] = hashlib.sha256(json.dumps(record['type_expression'],ensure_ascii=False,
            separators=(',',':')).encode()).hexdigest()
        with self.assertRaisesRegex(ValueError,'invalid Lean type DAG'): self.validate()

    def test_dag_metrics_cannot_be_edited_independently(self):
        self.payload['declarations'][0]['type_metrics']['unique_nodes'] = 42
        with self.assertRaisesRegex(ValueError,'DAG metrics mismatch'): self.validate()

    def test_unicode_type_hash_uses_utf8_without_ascii_escaping(self):
        expression = {'format':'LEAN_EXPR_DAG_V1','root':'1','nodes':[
            ['const',['str',['anonymous'],'True'],[]],
            ['forall',['str',['anonymous'],'α'],'default','0','0']]}
        record = self.add_public('Zeta23.OPICA.unicodeHelper','DEFINITION',expression)
        self.validate()
        record['type_sha256'] = hashlib.sha256(json.dumps(expression,ensure_ascii=True,
            separators=(',',':')).encode()).hexdigest()
        with self.assertRaisesRegex(ValueError,'DAG digest mismatch'): self.validate()

    def test_valid_constructor_inventory_passes(self):
        self.add_constructor()
        self.validate()

    def test_missing_constructor_inventory_or_member_rejected(self):
        _,ctor = self.add_constructor()
        del self.payload['constructors'][ctor]
        with self.assertRaisesRegex(ValueError,'constructor inventory differs'): self.validate()
        del self.payload['constructors']
        with self.assertRaisesRegex(ValueError,'constructor inventory'): self.validate()

    def test_foreign_constructor_entry_cannot_be_invented(self):
        self.payload['constructors']['Zeta23.OPICA.fake'] = {'family':'Zeta23.OPICA.Fake','type_expression':{}}
        with self.assertRaisesRegex(ValueError,'constructor inventory differs'): self.validate()

    def test_constructor_dag_must_match_public_full_type(self):
        _,ctor = self.add_constructor()
        self.payload['constructors'][ctor]['type_expression'] = copy.deepcopy(self.payload['declarations'][0]['type_expression'])
        with self.assertRaisesRegex(ValueError,'constructor full type mismatch'): self.validate()

    def test_constructor_family_must_be_inductive(self):
        _,ctor = self.add_constructor()
        self.payload['constructors'][ctor]['family'] = self.root['full_name']
        with self.assertRaisesRegex(ValueError,'constructor family mismatch'): self.validate()

    def test_constructor_structural_family_links_are_required(self):
        family,ctor = self.add_constructor()
        self.channel(ctor,'STRUCTURE')['targets'] = []
        with self.assertRaisesRegex(ValueError,'constructor structural family mismatch'): self.validate()
        self.channel(ctor,'STRUCTURE')['targets'] = [family]
        self.channel(family,'STRUCTURE')['targets'] = []
        with self.assertRaisesRegex(ValueError,'missing from inductive structural family'): self.validate()

    def test_public_helpers_remain_namespace_module_kind_and_axiom_checked(self):
        for key,value,message in [('name','Foreign.helper','foreign declaration namespace'),
                ('module','Zeta23.OPICA.Validation','foreign defining module'),
                ('kind','AXIOM','unadmitted public declaration kind'),
                ('axioms',['sorryAx'],'unadmitted mathematical axiom')]:
            with self.subTest(key=key):
                self.setUp()
                record = self.add_public('Zeta23.OPICA.helper','THEOREM')
                record[key] = value
                with self.assertRaisesRegex(ValueError,message): self.validate()

    def test_deleting_public_record_cannot_hide_existing_public_metadata(self):
        self.add_public('Zeta23.OPICA.helper','THEOREM')
        self.channel(self.root['full_name'],'VALUE')['targets'] = ['Zeta23.OPICA.helper']
        self.payload['declarations'].pop()
        with self.assertRaisesRegex(ValueError,'escaped enumeration'): self.validate()

    def test_exact_build_targets_and_fresh_export_commands_are_required(self):
        for index,argv in [(1,['lake','build','Zeta23.OPICA']),
                (2,['echo','cached success']),(0,['lake','--version'])]:
            with self.subTest(index=index):
                self.setUp()
                self.payload['commands'][index]['argv'] = argv
                with self.assertRaisesRegex(ValueError,'command identity'): self.validate()

    def test_command_inventory_log_identity_and_digest_are_required(self):
        for key,value,message in [('log','cached.log','command identity'),
                ('log_sha256','wrong','log digest'),('exit_code',True,'command identity')]:
            with self.subTest(key=key):
                self.setUp()
                self.payload['commands'][0][key] = value
                with self.assertRaisesRegex(ValueError,message): self.validate()
        self.payload['commands'].pop()
        with self.assertRaisesRegex(ValueError,'command inventory'): self.validate()

    def test_nonfinite_negative_or_nonnumeric_timing_is_rejected(self):
        for value in [-1,float('inf'),float('nan'),'1',True]:
            with self.subTest(value=value):
                self.payload['commands'][0]['seconds'] = value
                with self.assertRaisesRegex(ValueError,'command timing'): self.validate()

    def test_wrong_runtime_pin_is_rejected(self):
        self.payload['lean'] = 'Lean (version 4.32.0, test)'
        with self.assertRaisesRegex(ValueError,'runtime pin'): self.validate()

    def test_requested_head_is_actual_checked_head_or_direct_parent(self):
        self.payload.update(requested_head='c'*40,checkout_kind='SYNTHETIC_MERGE')
        receipt.validate_checkout_identity(self.payload,'a'*40,'b'*40,['c'*40,'d'*40])
        with self.assertRaisesRegex(ValueError,'foreign compiler requested head'):
            receipt.validate_checkout_identity(self.payload,'a'*40,'b'*40,['d'*40])

    def test_normal_parent_commit_cannot_be_labeled_synthetic_merge(self):
        self.payload.update(requested_head='c'*40,checkout_kind='SYNTHETIC_MERGE')
        with self.assertRaisesRegex(ValueError,'exactly two actual parents'):
            receipt.validate_checkout_identity(self.payload,'a'*40,'b'*40,['c'*40])

    def test_repaired_primary_dag_hash_still_must_match_reviewed_type(self):
        record = self.payload['declarations'][0]
        record['type_expression']['nodes'][0][1][-1] = 'False'
        encoded = json.dumps(record['type_expression'],ensure_ascii=False,separators=(',',':'))
        record['type_sha256'] = hashlib.sha256(encoded.encode()).hexdigest()
        record['type_metrics'] = receipt.validate_expression(encoded)
        with self.assertRaisesRegex(ValueError,'reviewed expected type changed'): self.validate()

    def test_requested_head_syntax_and_checkout_label_are_required(self):
        for requested,kind in [(None,'PR_HEAD'),('A'*40,'SYNTHETIC_MERGE'),('a'*40,'SYNTHETIC_MERGE')]:
            with self.subTest(requested=requested,kind=kind):
                self.payload.update(requested_head=requested,checkout_kind=kind)
                with self.assertRaises(ValueError):
                    receipt.validate_checkout_identity(self.payload,'a'*40,'b'*40,[])


class CompilerLogBytes(unittest.TestCase):
    def test_physical_utf8_log_bytes_match_recorded_digest_on_every_platform(self):
        captured = 'Lean proof α\nOPICA_COMPLETE\t76\n'
        expected = captured.encode('utf-8')
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)/'compiler.log'
            target.write_bytes(b'older CRLF log\r\nwith trailing bytes to replace\r\n')
            digest = receipt.write_compiler_log(target,captured)
            physical = target.read_bytes()
        self.assertEqual(physical,expected)
        self.assertNotIn(b'\r\n',physical)
        self.assertEqual(digest,hashlib.sha256(physical).hexdigest())


class RegisteredDependencyMapping(unittest.TestCase):
    def setUp(self):
        self.a,self.b,self.old,self.unrelated = ['Zeta23.OPICA.a','Zeta23.OPICA.b',
            'Zeta23.CCM.old','Zeta23.OPICA.unrelated']
        self.bindings = [{'id':identity,'theorem':name} for identity,name in
            [('NEW_A',self.a),('NEW_B',self.b),('OLD',self.old),('UNRELATED',self.unrelated)]]
        uses = {self.a:{'TYPE':['helperP'],'VALUE':[self.b]},
            'helperP':{'STRUCTURE':['helperQ']},'helperQ':{'VALUE':[self.old]},
            self.b:{'VALUE':['external']},self.old:{},self.unrelated:{'VALUE':[self.old]}}
        self.dependencies = [{'source':source,'channel':channel,'targets':channels.get(channel,[])}
            for source,channels in uses.items() for channel in ('TYPE','VALUE','STRUCTURE')]

    def mapped(self):
        return receipt.mapped_registered_dependencies([self.a,self.b],self.bindings,self.dependencies)

    def test_maps_new_and_old_registered_roots_through_all_channels(self):
        self.assertEqual(self.mapped(),{self.a:['NEW_B','OLD'],self.b:[]})

    def test_unrelated_registered_root_is_not_inferred_from_shared_uses(self):
        self.assertNotIn('UNRELATED',self.mapped()[self.a])
        self.assertEqual(self.mapped()[self.b],[])

    def test_cycles_never_create_a_self_dependency(self):
        next(row for row in self.dependencies if row['source']=='helperQ' and row['channel']=='STRUCTURE')['targets'] = [self.a]
        self.assertEqual(self.mapped()[self.a],['NEW_B','OLD'])

    def test_missing_provenance_channel_is_rejected(self):
        self.dependencies.pop()
        with self.assertRaisesRegex(ValueError,'incomplete mapped dependency provenance'): self.mapped()

    def test_reachable_registered_root_cannot_be_an_unexpanded_boundary(self):
        self.dependencies = [row for row in self.dependencies if row['source']!=self.old]
        with self.assertRaisesRegex(ValueError,'registered root lacks compiler expansion'): self.mapped()

    def test_duplicate_registered_identity_cannot_change_mapping(self):
        self.bindings.append({'id':'NEW_A','theorem':'Zeta23.OPICA.other'})
        with self.assertRaisesRegex(ValueError,'duplicate registered binding identity'): self.mapped()


if __name__ == '__main__':
    unittest.main()
