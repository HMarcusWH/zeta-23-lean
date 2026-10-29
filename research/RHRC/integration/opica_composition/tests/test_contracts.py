import unittest
from research.RHRC.integration.opica_composition.canonical import (
    ContractError, digest_text, relative_path, validate_path_inventory, load_bytes)
from research.RHRC.integration.opica_composition.contracts import CompositionProposal, SearchBudget

LANES=("CONTRACT","PARENT_REGRESSION","CURRENT_COMPATIBILITY","COMPOSITION_FORMAL",
       "SEMANTIC_NEGATIVES","FRAMEWORK_ADAPTERS","PROVIDER_SELECTED","REPLAY_CAMPAIGN","GENERATED_STATE","ACCEPTANCE")

class ContractCases(unittest.TestCase):
    def test_t104(self):
        # IDs are exact identities, not presentation aliases.
        from research.RHRC.integration.opica_composition.contracts import validate_lane_id
        self.assertEqual(validate_lane_id("PARENT_REGRESSION"),"PARENT_REGRESSION")
        for alias in ("parent_regression","PARENT","PARENT-REGRESSION"," PARENT_REGRESSION"):
            with self.assertRaises(ContractError): validate_lane_id(alias)

    def test_t109(self):
        self.assertEqual(digest_text("a"*64),"a"*64)
        for value in ("a"*64+"\n","a"*64+"\r","a"*64+" ","a"*63,"a"*65,"A"*64,"а"*64):
            with self.assertRaises(ContractError): digest_text(value)
            with self.assertRaises(ContractError): CompositionProposal("p","t",value,{"tag":"local","binder_slot":0})

    def test_t110(self):
        self.assertEqual(relative_path("Evidence/actual-result.json"),"Evidence/actual-result.json")
        for value in ("CON","foo/NUL.txt","COM1.out","a.","a ","foo~1/x","a:b","a\\b","../x"):
            with self.assertRaises(ContractError): relative_path(value)

    def test_t111(self):
        self.assertEqual(validate_path_inventory(["A/x","B/y"]),("A/x","B/y"))
        for paths in (["A/x","a/y"],["A/x","A/X"],["A","A/x"],["a/x","a/x"]):
            with self.assertRaises(ContractError): validate_path_inventory(paths)

    def test_closed_mutable_fields(self):
        plan={"tag":"local","binder_slot":0}; p=CompositionProposal("p","t","a"*64,plan)
        plan["binder_slot"]=99
        self.assertEqual(p.plan["binder_slot"],0)
        p.plan["binder_slot"]=99
        with self.assertRaises(ContractError): _=p.digest
        with self.assertRaises(ContractError): SearchBudget(term_nodes=True)
        with self.assertRaises(ContractError): load_bytes(b'{"x":1,"x":2}')

    def _transport_fixture(self,root):
        import hashlib
        from research.RHRC.integration.opica_composition import snapshot
        from research.RHRC.integration.opica_composition.canonical import canonical_bytes
        native=root/'native';(native/'temp/nested-empty').mkdir(parents=True)
        (native/'.hidden-dir/.empty').mkdir(parents=True)
        (native/'result.log').write_bytes(b'actual fixture bytes, not compiler proof\x00\xff')
        (native/'.hidden-file').write_bytes(b'dot bytes\r\n')
        bundle=root/'lane';bundle.mkdir()
        sealed=snapshot.seal_evidence_tree(native)
        snapshot.copy_evidence_tree(native,bundle/'native-evidence',sealed)
        (bundle/'native-evidence-inventory.json').write_bytes(canonical_bytes(sealed[0]))
        for name,value in (('source.json',{'fixture':'transport only'}),('source-after.json',{'fixture':'transport only'}),
                           ('results.json',{'fixture_value':17,'authority':'NO_THEOREM_AUTHORITY'})):
            (bundle/name).write_bytes(canonical_bytes(value))
        exp={'run_id':'12345','attempt':2,'requested_commit':'a'*40,'requested_tree':'b'*40,'profile_digest':'c'*64}
        identity={'lane_id':'CONTRACT','experiment':exp}
        files=sorted(p for p in bundle.rglob('*') if p.is_file())
        record={'schema':'OPICA4_LANE_BUNDLE_V1','lane_id':'CONTRACT','scope':'CURRENT_HOST','experiment':exp,
                'checked':{'commit':exp['requested_commit'],'tree':exp['requested_tree']},'conclusion':'success',
                'artifacts':[{'path':p.relative_to(bundle).as_posix(),'bytes':p.stat().st_size,
                              'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files],
                'records':['results.json','source.json','source-after.json']}
        (bundle/'lane.json').write_bytes(canonical_bytes(record))
        return bundle,identity

    def _transport_rewrite(self,staging,mutator):
        import hashlib,zipfile,warnings
        from research.RHRC.integration.opica_composition.canonical import canonical_bytes
        path=staging/'bundle.zip'
        with zipfile.ZipFile(path) as archive:rows=[(info,archive.read(info.filename)) for info in archive.infolist()]
        with warnings.catch_warnings():
            warnings.simplefilter('ignore',UserWarning)
            with zipfile.ZipFile(path,'w') as archive:
                for info,data in mutator(rows):archive.writestr(info,data)
        envelope=load_bytes((staging/'transport.json').read_bytes())
        envelope['container']={'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        (staging/'transport.json').write_bytes(canonical_bytes(envelope))

    def test_transport_roundtrip_preserves_exact_native_namespace(self):
        import tempfile,zipfile
        from pathlib import Path
        from research.RHRC.integration.opica_composition import snapshot
        from research.RHRC.integration.opica_composition.accept import verify_lane_bundle
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,identity=self._transport_fixture(root);staging=root/'transport'
            before=snapshot.seal_evidence_tree(bundle)[0]
            snapshot.pack_evidence_bundle(bundle,staging,identity)
            # Emulate the service's file-only outer ZIP: every inner directory
            # and dot entry must survive solely through the container's bytes.
            outer=root/'artifact.zip'
            with zipfile.ZipFile(outer,'w',compression=zipfile.ZIP_DEFLATED) as archive:
                for name in ('bundle.zip','transport.json'):archive.write(staging/name,name)
            downloaded=root/'download';downloaded.mkdir()
            with zipfile.ZipFile(outer) as archive:
                for name in ('bundle.zip','transport.json'):(downloaded/name).write_bytes(archive.read(name))
            destination=root/'reconstructed';snapshot.unpack_evidence_bundle(downloaded,destination,identity)
            self.assertTrue(snapshot.verify_evidence_tree(destination,before))
            self.assertEqual(snapshot.seal_evidence_tree(destination)[0],before)
            self.assertEqual(list((destination/'native-evidence/temp/nested-empty').iterdir()),[])
            self.assertEqual(list((destination/'native-evidence/.hidden-dir/.empty').iterdir()),[])
            self.assertEqual((destination/'native-evidence/.hidden-file').read_bytes(),b'dot bytes\r\n')
            replayed=[]
            def fixture_reconstruction(expected,record,files):
                self.assertEqual(load_bytes(files['results.json'].read_bytes())['fixture_value'],17)
                manifest=load_bytes(files['native-evidence-inventory.json'].read_bytes())
                snapshot.verify_evidence_tree(destination/'native-evidence',manifest)
                replayed.append(True);return True
            expected={'id':'CONTRACT','scope':'CURRENT_HOST','checked':load_bytes((destination/'lane.json').read_bytes())['checked']}
            verify_lane_bundle(expected,destination,experiment=identity['experiment'],replay=fixture_reconstruction)
            self.assertEqual(replayed,[True])
            self.assertEqual({p.name for p in staging.iterdir()},{'bundle.zip','transport.json'})

    def test_transport_rejects_corrupt_truncated_or_extra_container_bytes(self):
        import tempfile
        from pathlib import Path
        from research.RHRC.integration.opica_composition import snapshot
        for change in ('alter','truncate','append'):
            with self.subTest(change=change),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);bundle,identity=self._transport_fixture(root);staging=root/'transport'
                snapshot.pack_evidence_bundle(bundle,staging,identity);path=staging/'bundle.zip';raw=path.read_bytes()
                path.write_bytes((bytes([raw[0]^1])+raw[1:]) if change=='alter' else raw[:-1] if change=='truncate' else raw+b'X')
                with self.assertRaises(ContractError):snapshot.unpack_evidence_bundle(staging,root/'out',identity)
                self.assertFalse((root/'out').exists())

    def test_transport_rejects_wrong_identity_and_open_envelope(self):
        import copy,tempfile
        from pathlib import Path
        from research.RHRC.integration.opica_composition import snapshot
        from research.RHRC.integration.opica_composition.canonical import canonical_bytes
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,identity=self._transport_fixture(root);staging=root/'transport'
            snapshot.pack_evidence_bundle(bundle,staging,identity)
            for field,value in (('lane_id','MATHEMATICAL_SUPPORT'),('run_id','999'),('attempt',1),
                                ('requested_commit','d'*40),('requested_tree','e'*40),('profile_digest','f'*64)):
                expected=copy.deepcopy(identity)
                if field=='lane_id':expected[field]=value
                else:expected['experiment'][field]=value
                with self.subTest(field=field),self.assertRaises(ContractError):
                    snapshot.unpack_evidence_bundle(staging,root/'out',expected)
                self.assertFalse((root/'out').exists())
            envelope=load_bytes((staging/'transport.json').read_bytes());envelope['callback']='forbidden'
            (staging/'transport.json').write_bytes(canonical_bytes(envelope))
            with self.assertRaises(ContractError):snapshot.unpack_evidence_bundle(staging,root/'out',identity)

    def test_transport_rejects_missing_added_duplicate_and_altered_members(self):
        import copy,tempfile,zipfile,struct,hashlib
        from contextlib import nullcontext
        from pathlib import Path
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import snapshot
        from research.RHRC.integration.opica_composition.canonical import canonical_bytes
        for mode in ('missing','added','duplicate','altered','underreported-count'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);bundle,identity=self._transport_fixture(root);staging=root/'transport'
                snapshot.pack_evidence_bundle(bundle,staging,identity)
                def mutate(rows):
                    if mode=='missing':return rows[:-1]
                    if mode=='duplicate':return rows+[copy.copy(rows[-1])]
                    if mode in {'added','underreported-count'}:return rows+[(zipfile.ZipInfo('unlisted'),b'extra')]
                    return [(info,(b'X'+data[1:]) if info.filename=='native-evidence/result.log' else data) for info,data in rows]
                self._transport_rewrite(staging,mutate)
                allocation_tripwire=nullcontext()
                if mode=='underreported-count':
                    path=staging/'bundle.zip';raw=bytearray(path.read_bytes());position=len(raw)-22
                    count=struct.unpack_from('<H',raw,position+10)[0]-1
                    struct.pack_into('<2H',raw,position+8,count,count);path.write_bytes(raw)
                    envelope=load_bytes((staging/'transport.json').read_bytes())
                    envelope['container']={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
                    (staging/'transport.json').write_bytes(canonical_bytes(envelope))
                    allocation_tripwire=patch.object(snapshot.zipfile,'ZipFile',side_effect=AssertionError('unbounded member allocation'))
                with allocation_tripwire,self.assertRaises((ContractError,zipfile.BadZipFile)):
                    snapshot.unpack_evidence_bundle(staging,root/'out',identity)
                if mode!='altered':self.assertFalse((root/'out').exists())

    def test_transport_rejects_path_alias_and_traversal_members(self):
        import copy,tempfile
        from pathlib import Path
        from research.RHRC.integration.opica_composition import snapshot
        for name in ('/absolute','../escape','a\\b','C:/escape','NUL.log','a.','native-evidence/RESULT.log'):
            with self.subTest(name=name),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);bundle,identity=self._transport_fixture(root);staging=root/'transport'
                snapshot.pack_evidence_bundle(bundle,staging,identity)
                def mutate(rows):
                    info=copy.copy(rows[-1][0]);info.filename=name;return rows[:-1]+[(info,rows[-1][1])]
                self._transport_rewrite(staging,mutate)
                with self.assertRaises(ContractError):snapshot.unpack_evidence_bundle(staging,root/'out',identity)
                self.assertFalse((root/'out').exists());self.assertFalse((root/'escape').exists())

    def test_transport_rejects_compression_bombs_and_unsupported_metadata(self):
        import copy,stat,tempfile,zipfile,struct,hashlib
        from pathlib import Path
        from research.RHRC.integration.opica_composition import snapshot
        from research.RHRC.integration.opica_composition.canonical import canonical_bytes
        for mode in ('compressed','symlink','device','permissions','extra','comment','encrypted','local-name'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);bundle,identity=self._transport_fixture(root);staging=root/'transport'
                snapshot.pack_evidence_bundle(bundle,staging,identity)
                def mutate(rows):
                    changed=[]
                    for original,data in rows:
                        info=copy.copy(original)
                        if not info.is_dir():
                            if mode=='compressed':info.compress_type=zipfile.ZIP_DEFLATED;data=b'\0'*(1024*1024)
                            elif mode=='symlink':info.external_attr=(stat.S_IFLNK|0o600)<<16
                            elif mode=='device':info.external_attr=(stat.S_IFCHR|0o600)<<16
                            elif mode=='permissions':info.external_attr=(stat.S_IFREG|0o4755)<<16
                            elif mode=='extra':info.extra=struct.pack('<HH',2,0)
                            elif mode=='comment':info.comment=b'unsupported'*100
                        changed.append((info,data))
                    return changed
                self._transport_rewrite(staging,mutate)
                if mode in {'encrypted','local-name'}:
                    path=staging/'bundle.zip';raw=bytearray(path.read_bytes())
                    if mode=='encrypted':
                        central=raw.index(b'PK\x01\x02');raw[central+8]|=1
                    else:raw[30]^=1
                    path.write_bytes(raw)
                    envelope=load_bytes((staging/'transport.json').read_bytes())
                    envelope['container']={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
                    (staging/'transport.json').write_bytes(canonical_bytes(envelope))
                with self.assertRaises(ContractError):snapshot.unpack_evidence_bundle(staging,root/'out',identity)
                self.assertFalse((root/'out').exists())

    def test_transport_finite_limits_reject_before_destination_creation(self):
        import copy,tempfile
        from pathlib import Path
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import snapshot
        from research.RHRC.integration.opica_composition.canonical import canonical_bytes
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,identity=self._transport_fixture(root);staging=root/'transport'
            snapshot.pack_evidence_bundle(bundle,staging,identity)
            original=load_bytes((staging/'transport.json').read_bytes())
            for bound in ('TRANSPORT_MAX_ENTRIES','TRANSPORT_MAX_DEPTH','TRANSPORT_MAX_FILE_BYTES','TRANSPORT_MAX_BYTES','TRANSPORT_MAX_CONTAINER_BYTES'):
                with self.subTest(bound=bound),patch.object(snapshot,bound,1),self.assertRaises(ContractError):
                    snapshot.unpack_evidence_bundle(staging,root/'out',identity)
                self.assertFalse((root/'out').exists())
            for mode in ('total','member','count','depth'):
                envelope=copy.deepcopy(original);manifest=envelope['manifest']
                if mode=='total':manifest['total_bytes']=snapshot.TRANSPORT_MAX_BYTES+1
                elif mode=='member':manifest['files'][0]['bytes']=snapshot.TRANSPORT_MAX_FILE_BYTES+1
                elif mode=='count':manifest['directories']=['d'+str(i) for i in range(snapshot.TRANSPORT_MAX_ENTRIES+1)]
                else:manifest['directories']=['/'.join(['x']*i) for i in range(1,66)]
                (staging/'transport.json').write_bytes(canonical_bytes(envelope))
                with self.subTest(mode=mode),self.assertRaises(ContractError):snapshot.unpack_evidence_bundle(staging,root/'out',identity)
                self.assertFalse((root/'out').exists())

    def test_transport_refuses_links_reparse_and_nonregular_sources(self):
        import os,stat,tempfile
        from pathlib import Path
        from types import SimpleNamespace
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import snapshot
        for kind in ('file-link','directory-link','reparse','fifo'):
            with self.subTest(kind=kind),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);bundle,identity=self._transport_fixture(root);outside=root/'outside';outside.mkdir()
                (outside/'secret').write_bytes(b'NEVER_TRANSPORT_SECRET');leaf=bundle/'alias'
                if os.name!='nt':
                    if kind=='fifo':os.mkfifo(leaf)
                    elif kind=='reparse':leaf.symlink_to(outside,target_is_directory=True)
                    else:leaf.symlink_to(outside if kind=='directory-link' else outside/'secret',target_is_directory=kind=='directory-link')
                else:leaf.write_bytes(b'placeholder')
                original=os.lstat
                def metadata(candidate,*args,**kwargs):
                    info=original(candidate,*args,**kwargs)
                    if os.name=='nt' and Path(os.path.abspath(candidate))==leaf:
                        fields={key:getattr(info,key) for key in dir(info) if key.startswith('st_')}
                        fields['st_mode']=(stat.S_IFIFO if kind=='fifo' else stat.S_IFLNK)|0o600
                        fields['st_file_attributes']=1024 if kind=='reparse' else 0
                        return SimpleNamespace(**fields)
                    return info
                with patch.object(os,'lstat',side_effect=metadata),self.assertRaises((ContractError,OSError)):
                    snapshot.pack_evidence_bundle(bundle,root/'transport',identity)
                self.assertFalse((root/'transport/transport.json').exists())
                self.assertEqual((outside/'secret').read_bytes(),b'NEVER_TRANSPORT_SECRET')

    def test_transport_pack_rejects_growth_replacement_and_link_substitution(self):
        import os,tempfile
        from pathlib import Path
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import snapshot
        for mode in ('growth','same-bytes-replacement','file-link','directory-link'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);bundle,identity=self._transport_fixture(root);original=snapshot._transport_new_directory
                outside=root/'outside';outside.mkdir();(outside/'result.log').write_bytes(b'NEVER_READ_EXTERNAL_SECRET')
                def at_pack_boundary(path):
                    owned=original(path);leaf=bundle/'native-evidence/result.log'
                    if mode=='growth':
                        with leaf.open('ab') as stream:stream.write(b'grew')
                    elif mode=='same-bytes-replacement':
                        raw=leaf.read_bytes();leaf.rename(leaf.with_name('old.log'));leaf.write_bytes(raw)
                    elif mode=='file-link':
                        leaf.unlink()
                        if os.name!='nt':leaf.symlink_to(outside/'result.log')
                        else:leaf.write_bytes(b'NEVER_READ_EXTERNAL_SECRET')
                    else:
                        (bundle/'native-evidence').rename(bundle/'old-native')
                        if os.name!='nt':(bundle/'native-evidence').symlink_to(outside,target_is_directory=True)
                        else:(bundle/'native-evidence').mkdir();(bundle/'native-evidence/result.log').write_bytes(b'NEVER_READ_EXTERNAL_SECRET')
                    return owned
                with patch.object(snapshot,'_transport_new_directory',side_effect=at_pack_boundary),self.assertRaises((ContractError,OSError)):
                    snapshot.pack_evidence_bundle(bundle,root/'transport',identity)
                self.assertFalse((root/'transport/transport.json').exists())
                self.assertEqual((outside/'result.log').read_bytes(),b'NEVER_READ_EXTERNAL_SECRET')

    def test_transport_pack_detects_mutation_during_streaming(self):
        import tempfile
        from contextlib import contextmanager
        from pathlib import Path
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import snapshot
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,identity=self._transport_fixture(root);original=snapshot._evidence_file;reads=0
            @contextmanager
            def grow_after_open(base,relative,identities=None):
                nonlocal reads
                with original(base,relative,identities) as (stream,info):
                    if Path(base)==bundle and relative=='native-evidence/result.log':
                        reads+=1
                        if reads==2:
                            class ChangingReader:
                                def read(self,amount):
                                    data=stream.read(amount)
                                    # Windows's retained no-write handle refuses
                                    # this real mutation; Linux detects growth.
                                    with (bundle/relative).open('ab') as target:target.write(b'grew in stream')
                                    return data
                            yield ChangingReader(),info;return
                    yield stream,info
            with patch.object(snapshot,'_evidence_file',side_effect=grow_after_open),self.assertRaises((ContractError,OSError)):
                snapshot.pack_evidence_bundle(bundle,root/'transport',identity)
            self.assertFalse((root/'transport/transport.json').exists())

    def test_transport_extraction_refuses_nonfresh_and_substituted_destination(self):
        import tempfile
        from pathlib import Path
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import snapshot
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,identity=self._transport_fixture(root);staging=root/'transport'
            snapshot.pack_evidence_bundle(bundle,staging,identity);destination=root/'out';destination.mkdir()
            with self.assertRaises(ContractError):snapshot.unpack_evidence_bundle(staging,destination,identity)
            destination.rmdir();original=snapshot._transport_new_directory
            def substituted(path):
                owned=original(path);path.rename(root/'stolen');path.mkdir();return owned
            with patch.object(snapshot,'_transport_new_directory',side_effect=substituted),self.assertRaises((ContractError,OSError)):
                snapshot.unpack_evidence_bundle(staging,destination,identity)
            self.assertEqual(list(destination.iterdir()),[])

    def test_transport_exact_attempt_lane_inventory_is_closed(self):
        import tempfile
        from pathlib import Path
        from research.RHRC.integration.opica_composition import cli
        from research.RHRC.integration.opica_composition.accept import ROUND4_LANES
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);_,identity=self._transport_fixture(root);inputs=root/'inputs';inputs.mkdir()
            for lane in ROUND4_LANES:(inputs/('opica4-12345-1-lane-'+lane)).mkdir()
            with self.assertRaisesRegex(ContractError,'eleven-lane'):
                cli.unpack_lane_bundles(Path(__file__).resolve().parents[5],inputs,root/'out',identity['experiment'])
            self.assertFalse((root/'out').exists())

    def test_transport_keeps_existing_lane_verifier_identity_checks(self):
        import tempfile
        from pathlib import Path
        from research.RHRC.integration.opica_composition import snapshot
        from research.RHRC.integration.opica_composition.accept import verify_lane_bundle
        from research.RHRC.integration.opica_composition.canonical import canonical_bytes
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,identity=self._transport_fixture(root)
            row=load_bytes((bundle/'lane.json').read_bytes());row['experiment']['attempt']=1
            (bundle/'lane.json').write_bytes(canonical_bytes(row))
            snapshot.pack_evidence_bundle(bundle,root/'transport',identity)
            snapshot.unpack_evidence_bundle(root/'transport',root/'out',identity)
            def forbidden_replay(*args):raise AssertionError('stale lane must fail before independent replay')
            with self.assertRaisesRegex(ContractError,'cross-run/attempt'):
                verify_lane_bundle({'id':'CONTRACT','scope':'CURRENT_HOST','checked':row['checked']},root/'out',
                                   experiment=identity['experiment'],replay=forbidden_replay)

    def test_transport_producer_checks_complete_lane_with_no_follow_reads(self):
        import os,tempfile
        from contextlib import nullcontext
        from pathlib import Path
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import cli
        from research.RHRC.integration.opica_composition.canonical import canonical_bytes
        from research.RHRC.integration.opica_composition.tests.test_native_environment import leaf_links
        for mode in ('valid','wrong-attempt','linked-lane'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);bundle,identity=self._transport_fixture(root);context=nullcontext()
                if mode=='wrong-attempt':
                    row=load_bytes((bundle/'lane.json').read_bytes());row['experiment']['attempt']=1
                    (bundle/'lane.json').write_bytes(canonical_bytes(row))
                elif mode=='linked-lane':
                    secret=root/'secret';secret.write_bytes(b'NEVER_READ_LINKED_LANE')
                    if os.name!='nt':(bundle/'lane.json').unlink();(bundle/'lane.json').symlink_to(secret)
                    else:context=leaf_links({bundle/'lane.json':str(secret)})
                read_tripwire=(patch.object(Path,'read_bytes',side_effect=AssertionError('path-based lane read forbidden'))
                               if mode=='linked-lane' else nullcontext())
                with context,read_tripwire,patch.object(cli,'validate_descendant',return_value={'fixture':'transport only'}):
                    if mode=='valid':
                        cli.pack_lane_bundle(cli.REPO,bundle,root/'transport','CONTRACT',identity['experiment'])
                        self.assertTrue((root/'transport/transport.json').is_file())
                    else:
                        with self.assertRaises(ContractError):
                            cli.pack_lane_bundle(cli.REPO,bundle,root/'transport','CONTRACT',identity['experiment'])
                        self.assertFalse((root/'transport/transport.json').exists())

    def test_transport_zip64_offset_is_checked_without_allocating_gigabytes(self):
        import io,struct,tempfile
        from pathlib import Path
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import snapshot
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,_=self._transport_fixture(root);manifest=snapshot.seal_evidence_tree(bundle)[0]
            names=[name+'/' for name in manifest['directories']]+[row['path'] for row in manifest['files']]
            records=[]
            for name in names:
                header=bytearray(46);header[:4]=b'PK\x01\x02';struct.pack_into('<3H',header,28,len(name),0,0)
                records.append(bytes(header)+name.encode('ascii'))
            central=b''.join(records);count=len(names);offset=0x100000000+100;central_bytes=len(central)
            size=offset+central_bytes+98;zip_offset=size-98
            tail=struct.pack('<4sQ2H2L4Q',b'PK\x06\x06',44,45,45,0,0,count,count,central_bytes,offset)
            tail+=struct.pack('<4sLQL',b'PK\x06\x07',0,zip_offset,1)
            tail+=struct.pack('<4s4H2LH',b'PK\x05\x06',0,0,count,count,central_bytes,0xffffffff,0)
            class FooterOnlyStream(io.BytesIO):
                def seek(self,value,whence=0):self.position=value;return value
                def read(self,amount=-1):
                    start=self.position-zip_offset;central_start=self.position-offset;self.position+=amount
                    if 0<=central_start<len(central):return central[central_start:central_start+amount]
                    return tail[start:start+amount] if 0<=start<len(tail) else b''
            # The constructor tripwire must only be reached after the bounded
            # preflight has authenticated and adopted the 64-bit offset.
            with patch.object(snapshot.zipfile,'ZipFile',side_effect=RuntimeError('bounded preflight passed')) as constructor:
                with self.assertRaisesRegex(RuntimeError,'bounded preflight passed'):
                    snapshot._transport_zip_inventory(FooterOnlyStream(),manifest,size)
                constructor.assert_called_once()
