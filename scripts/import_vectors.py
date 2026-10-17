#!/usr/bin/env python3
import argparse, hashlib, json
from pathlib import Path
from p256_reference import direct_x_for_valid_case, circuit_for_valid_case, mul, G
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
source=json.loads((root/'vectors/wycheproof.json').read_text())
cases=[]
for group in source['testGroups']:
    assert group['sha']=='SHA-256' and group['publicKey']['curve']=='secp256r1'
    key=group['publicKey']['uncompressed'];assert key.startswith('04') and len(key)==130
    for t in group['tests']:
        assert t['result'] in ['valid','invalid'], t
        cases.append(dict(id=f"wycheproof-{t['tcId']}",pk=key[2:],digest=hashlib.sha256(bytes.fromhex(t['msg'])).hexdigest(),signature=t['sig'],message=t['msg'],expected=t['result']=='valid',comment=t['comment']))
assert len(cases)==source['numberOfTests']
# Additional fixed-interface key and digest rejection checks; upstream cases unchanged.
seed=next(t for t in cases if t['expected'])
p256=0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
mutations={'off-curve':dict(pk='00'*64),'x-equals-p':dict(pk=f'{p256:064x}'+seed['pk'][64:]),'y-equals-p':dict(pk=seed['pk'][:64]+f'{p256:064x}'),'short-key':dict(pk=seed['pk'][:-2]),'short-digest':dict(digest=seed['digest'][:-2]),'long-digest':dict(digest=seed['digest']+'00')}
for name,fields in mutations.items():cases.append(dict(seed,**{'id':'local-'+name,'expected':False,'comment':'Locally constructed rejection test',**fields}))
for c in cases: c['standard_expected'] = c['expected']
generator_pk = ('6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296'
                '4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5')
r = 0x7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978
n = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
s = ((1+r)*pow(2,-1,n)) % n
for name, digest, scalar, valid in [('generator', 1, s, True),
                                    ('generator-other-s', 1, n-s, True),
                                    ('generator-bad-digest', 2, s, False)]:
    cases.append(dict(id='local-'+name, pk=generator_pk, digest=f'{digest:064x}',
        signature=f'{r:064x}{scalar:064x}', message='', expected=valid,
        standard_expected=valid, comment='Generator public key; d=1, e=1, k=2 regression'))
for c in json.loads((root/'vectors/longfellow-overflow.json').read_text()):
    cases.append(dict(c, standard_expected=True, expected=False))
for name,d,k in [('pk-minus-g',n-1,2), ('r-minus-g',2,n-1),
                 ('r-minus-pk',2,n-2), ('g-r-pk-infinity',2,n-3)]:
    Q=mul(d,G); R=mul(k,G); r=R[0]%n; s=(1+r*d)*pow(k,-1,n)%n
    assert r and s
    cases.append(dict(id='local-'+name,pk=''.join(f'{v:064x}' for v in Q),
        digest=f'{1:064x}',signature=f'{r:064x}{s:064x}',message='',
        standard_expected=True,comment='Longfellow affine precomputation exception'))
for c in cases:
    c['direct_x_expected'] = c['standard_expected'] and direct_x_for_valid_case(c)
    c['expected'] = c['standard_expected'] and circuit_for_valid_case(c)
text=json.dumps(cases,indent=2)+'\n';path=root/'vectors/cases.json'
if args.check:assert path.read_text()==text, 'Corpus drift'
else:path.write_text(text)
print(f'{len(cases)} cases ({sum(c["expected"] for c in cases)} valid), {source["numberOfTests"]} upstream, {len(cases)-source["numberOfTests"]} local')
