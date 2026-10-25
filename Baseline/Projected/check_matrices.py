#!/usr/bin/env python3
"""Independent sparse R1CS count and witness check (Python standard library only)."""
import hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1] if len(sys.argv)>1 else pathlib.Path(__file__).parent/'generated')
raw=(root/'matrices.json').read_bytes()
m=json.loads(raw); p=int(m['field_prime']); z=[int(x) for x in json.loads((root/'sample-witness.json').read_text())]
assert z[0]==1 and len(z)==m['columns']
assert m['columns']==m['additional_allocations']+m['fixed_inputs']+1
assert m['rows']==len(m['constraints'])
assert m['score']==m['rows']+m['additional_allocations']

def value(lc,wires):
    result=0
    for column,coefficient in lc:
        assert 0<=column<len(wires)
        result+=int(coefficient)*wires[column]
    return result%p

def failures(wires):
    return [i for i,(a,b,c) in enumerate(m['constraints']) if (value(a,wires)*value(b,wires)-value(c,wires))%p]
assert not failures(z),'exported witness violates matrices'
# Vary each external statement input while keeping auxiliary witness fixed.
for i in range(1,6):
    corrupt=z.copy(); corrupt[i]=(corrupt[i]+1)%p
    assert failures(corrupt),f'input column {i} is not bound'
# Report which auxiliary-wire changes are detected for this sample.
# This is a local corruption test, not a proof of global soundness.
uses=[set() for _ in z]
for i,(a,b,c) in enumerate(m['constraints']):
    for column,_ in a+b+c: uses[column].add(i)
rejected_aux=0
free_in_sample=[]
for column in range(6,len(z)):
    old=z[column]; z[column]=(old+1)%p
    rejected=any((value(m['constraints'][i][0],z)*value(m['constraints'][i][1],z)-value(m['constraints'][i][2],z))%p for i in uses[column])
    z[column]=old
    if rejected: rejected_aux+=1
    else: free_in_sample.append(column)
print(json.dumps({'field_prime':str(p),'additional_allocations':m['additional_allocations'],'rows':m['rows'],'score':m['score'],'matrix_sha256':hashlib.sha256(raw).hexdigest(),'sample_satisfies':True,'input_mutations_rejected':5,'auxiliary_mutations_rejected':rejected_aux,'sample_free_auxiliary_columns':free_in_sample},indent=2))
