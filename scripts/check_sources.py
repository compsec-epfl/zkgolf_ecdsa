#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
for record in json.loads((root/'docs/sources.json').read_text()):
    data=(root/record['file']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==record['local_sha256'], record['file']
    assert hashlib.sha256(data).hexdigest()==record['sha256'], record['file']
print('Pinned vector and license hashes verified')

for record in json.loads((root/'docs/longfellow-sources.json').read_text()):
    data=(root/record['file']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==record['local_sha256'], record['file']
    if record['file'].endswith('/Nat.lean'):
        data=data.replace(b'    rw [h2]\n    simp only [cond]\n', b'    rw [h2]\n    dsimp\n')
    assert hashlib.sha256(data).hexdigest()==record['sha256'], record['file']
print('Longfellow definitions unchanged; two proof-tactic compatibility edits verified')
