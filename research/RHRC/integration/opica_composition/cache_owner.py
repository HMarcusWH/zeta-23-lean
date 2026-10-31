"""One trusted writer per native build directory; workers only mount it read-only."""
from pathlib import Path
import os,uuid
from .canonical import require
from .snapshot import unlinked

class CacheWriterLease:
    def __init__(self,cache):
        self.cache=unlinked(cache).absolute();self.path=self.cache/'.opica-cache-writer.lock';self.owner=uuid.uuid4().hex
    def __enter__(self):
        self.cache.mkdir(parents=True,exist_ok=True)
        try:fd=os.open(self.path,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
        except FileExistsError as exc:raise ValueError('native build cache already has a writer') from exc
        with os.fdopen(fd,'w',encoding='ascii') as f:f.write(self.owner);f.flush();os.fsync(f.fileno())
        return self
    def __exit__(self,*_):
        require(self.path.read_text(encoding='ascii')==self.owner,'cache lease owner changed')
        self.path.unlink()
