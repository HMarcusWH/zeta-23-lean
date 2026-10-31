import unittest
from io import BytesIO
from pathlib import Path
import sys
import tempfile
from zipfile import ZipFile
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from source_lock import compare_locked_sources,git_blob,safe_archive_name,ARCHIVE_ROOT

class LockTest(unittest.TestCase):
    def test_git_blob_constant(self):
        self.assertEqual(git_blob(b'hello\n'),'ce013625030ba8dba906f756967f9e9ca394464a')
    def test_archive_path_rejects_traversal(self):
        for p in ('../x','a/../x','/abs','a\\b','a//b','C:/x','a/./b'):
            with self.subTest(p=p), self.assertRaises(ValueError):safe_archive_name(p)
    def test_source_archive_verification(self):
        data=b'content\n'; expected=git_blob(data)
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'input.zip'
            with ZipFile(path,'w') as z:z.writestr(ARCHIVE_ROOT+'A.lean',data)
            result=compare_locked_sources(path,{'A.lean':expected})
            self.assertEqual(result['verified_git_blobs']['A.lean'],expected)
    def test_wrong_blob_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'input.zip'
            with ZipFile(path,'w') as z:z.writestr(ARCHIVE_ROOT+'A.lean',b'x')
            with self.assertRaises(ValueError):compare_locked_sources(path,{'A.lean':'0'*40})
    def test_duplicate_members_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'input.zip'
            import warnings
            with warnings.catch_warnings():
                warnings.simplefilter('ignore')
                with ZipFile(path,'w') as z:
                    z.writestr(ARCHIVE_ROOT+'A.lean',b'x')
                    z.writestr(ARCHIVE_ROOT+'A.lean',b'x')
            with self.assertRaises(ValueError):compare_locked_sources(path,{'A.lean':git_blob(b'x')})
