#!/usr/bin/env python3
"""Construct an ECDSA verifier edge case; no private key or hash preimage is known.
This is a diagnostic, not the trusted specification or an issued credential.
"""
import json, math
from pathlib import Path
p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
n = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
G = (0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
     0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)
def add(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P;u,v=Q
    if x==u and (y+v)%p==0:return None
    slope=((3*x*x-3)*pow(2*y,-1,p) if P==Q else (v-y)*pow(u-x,-1,p))%p
    X=(slope*slope-x-u)%p
    return X,(slope*(x-X)-y)%p
def mul(k,P):
    out=None
    while k:
        if k&1:out=add(out,P)
        P=add(P,P);k>>=1
    return out
def oncurve(P):
    x,y=P
    return (y*y-(x*x*x-3*x+b))%p==0
x=n+1
while True:
    rhs=(x*x*x-3*x+b)%p;y=pow(rhs,(p+1)//4,p)
    if y*y%p==rhs:break
    x+=1
R=(x,y);r=x%n;e=s=1
Q=mul(pow(r,-1,n),add(R,(G[0],(-G[1])%p)))
assert oncurve(Q) and add(G,mul(r,Q))==R
assert x%n==r and x!=r
# Released witness generator uses r as rx and the reconstructed R.y as ry.
assert not oncurve((r,y))
case=dict(id='local-longfellow-overflow',pk=''.join(f'{v:064x}' for v in Q),
    digest=f'{e:064x}',signature=f'{r:064x}{s:064x}',message='',expected=True,
    comment='Constructed verifier-only case: R.x >= n; no known signing key or message preimage')
root=Path(__file__).resolve().parents[1]
(root/'vectors/longfellow-overflow.json').write_text(json.dumps([case],indent=2)+'\n')
print(f'R.x = n + {r}; ordinary ECDSA accepts, direct-x equality fails')
print('Longfellow-generated (r, R.y) fails its on-curve constraint')
print(f'(p-n)/p = {(p-n)/p:.4e}, about 2^({math.log2((p-n)/p):.2f}); interval ratio, not an exact nonce probability')
