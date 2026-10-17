"""Small affine model used only to derive direct-x vector expectations.
RustCrypto and the Lean upstream-arithmetic oracle independently check them.
"""
p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
n = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
G = (0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
     0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)
def add(P, Q):
    if P is None: return Q
    if Q is None: return P
    x,y=P; u,v=Q
    if x==u and (y+v)%p==0: return None
    slope=((3*x*x-3)*pow(2*y,-1,p) if P==Q else (v-y)*pow(u-x,-1,p))%p
    X=(slope*slope-x-u)%p
    return X,(slope*(x-X)-y)%p

def mul(k, P):
    result=None
    while k:
        if k&1: result=add(result,P)
        P=add(P,P); k>>=1
    return result

def direct_x_for_valid_case(c):
    """Precondition: valid canonical ordinary-ECDSA input."""
    pk=c['pk']; sig=c['signature']
    Q=(int(pk[:64],16),int(pk[64:],16)); r=int(sig[:64],16); s=int(sig[64:],16)
    w=pow(s,-1,n)
    R=add(mul(int(c['digest'],16)*w%n,G),mul(r*w%n,Q))
    assert R is not None and R[0]%n==r
    return R[0]==r


def circuit_for_valid_case(c):
    """Expected generated-witness result for valid ordinary ECDSA cases."""
    pk=c['pk']; sig=c['signature']
    Q=(int(pk[:64],16),int(pk[64:],16)); r=int(sig[:64],16); s=int(sig[64:],16)
    R=add(mul(int(c['digest'],16)*pow(s,-1,n)%n,G),mul(r*pow(s,-1,n)%n,Q))
    assert R is not None and R[0]%n==r
    return (R[0]==r and Q[0]!=0 and add(G,Q) is not None and
            add(G,R) is not None and add(Q,R) is not None and
            add(G,add(Q,R)) is not None)
