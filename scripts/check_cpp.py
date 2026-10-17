#!/usr/bin/env python3
"""Check generated witnesses with the actual pinned C++ circuit evaluator.
Usage: python3 scripts/check_cpp.py /path/to/longfellow-zk
Requires clang++ and the upstream checkout at the exact challenge commit.
No GoogleTest, OpenSSL or full Longfellow build is needed.
"""
import json, subprocess, sys, tempfile
from pathlib import Path
root=Path(__file__).resolve().parents[1]
up=Path(sys.argv[1]).resolve()
rev='4fe092be7e8e9634cd3b27daf55695a3a416043e'
assert subprocess.check_output(['git','-C',str(up),'rev-parse','HEAD'],text=True).strip()==rev
assert not subprocess.check_output(['git','-C',str(up),'diff','HEAD','--','lib'],text=True), 'Modified upstream C++'
cases=json.loads((root/'vectors/cases.json').read_text())
p=0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
n=0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
eligible=[]
for c in cases:
    pk=bytes.fromhex(c['pk']); digest=bytes.fromhex(c['digest']); sig=bytes.fromhex(c['signature'])
    if len(pk)!=64 or len(digest)!=32 or len(sig)!=64:
        assert not c['expected']; continue
    nums=[int.from_bytes(x,'big') for x in [pk[:32],pk[32:],digest,sig[:32],sig[32:]]]
    x,y,e,r,s=nums
    if not (x<p and y<p and 0<r<n and 0<s<n):
        assert not c['expected']; continue
    eligible.append((c,nums))
with tempfile.TemporaryDirectory(prefix='ecdsa-cpp-') as tmp:
    tmp=Path(tmp); src=tmp/'probe.cc';exe=tmp/'probe'
    text='#include "probe.h"\nint main() {\n'
    for c,nums in eligible:
        text+='  { const ecdsa_testvec v[] = {{'+','.join('StaticString("'+hex(x)+'")' for x in nums)+'}};\n'
        text+='    std::cout << test_signature3(v, 1, p256, p256_scalar, n256_order) << "\\n"; }\n'
    src.write_text(text+'}\n')
    subprocess.run(['clang++','-std=c++17','-O2','-I'+str(up/'lib'),'-I'+str(root/'reference/cpp'),str(src),str(up/'lib/ec/p256.cc'),str(up/'lib/algebra/nat.cc'),'-o',str(exe)],check=True)
    output=subprocess.check_output([str(exe)],text=True).splitlines()
    assert len(output)==len(eligible)
    for (c,_),actual in zip(eligible,output):
        assert (actual=='1')==c['expected'], (c['id'],actual,c['expected'])
report={'commit':rev,'total_cases':len(cases),'cpp_evaluated':len(eligible),
        'byte_envelope_rejections':len(cases)-len(eligible),'passed':True,
        'scope':'actual circuit evaluator on generated witnesses; not an exhaustive existential equivalence proof'}
(root/'docs/cpp-validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
