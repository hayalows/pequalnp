from itertools import combinations_with_replacement
n=10
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
mask=(1<<(1<<n))-1
inputs=[sum(1<<v for v in range(1<<n) if v>>i&1) for i in range(n)]
target=0
for u,v in edges: target |= inputs[u]&inputs[v]
assert (0,2) not in {tuple(sorted(p)) for p in edges}
first=inputs[0]&inputs[2]
wires=inputs+[first,0]
candidates=[('not',i,i,mask^a) for i,a in enumerate(wires)]
for i,j in combinations_with_replacement(range(len(wires)),2):
 candidates.extend([('and',i,j,wires[i]&wires[j]),('or',i,j,wires[i]|wires[j])])
matching=[g[:3] for g in candidates if g[3]==target]
assert not matching
best=min((g[3]^target).bit_count() for g in candidates)
print('First gate AND(0,2), a non-edge. Second gate choices:',len(candidates))
print('Target output matched in two gates:',len(matching))
print('Best truth-table Hamming distance after second gate:',best)
print('Output may also directly select an input or first gate; none equals target:',all(w!=target for w in wires))

edge_set={frozenset(e) for e in edges}
def extend(mapping, unused):
 if len(mapping)==n:
  yield tuple(mapping)
  return
 i=len(mapping)
 for v in unused:
  if all((frozenset((i,j)) in edge_set)==(frozenset((v,mapping[j])) in edge_set) for j in range(i)):
   yield from extend(mapping+[v], unused-{v})
automorphisms=list(extend([],set(range(n))))
orbit={frozenset((p[0],p[2])) for p in automorphisms}
nonedges={frozenset((a,b)) for a,b in combinations_with_replacement(range(n),2) if a!=b and frozenset((a,b)) not in edge_set}
assert orbit==nonedges
print('Graph automorphisms:',len(automorphisms),'non-edge orbit size:',len(orbit))
