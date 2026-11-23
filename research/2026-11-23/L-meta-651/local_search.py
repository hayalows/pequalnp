from itertools import product,combinations_with_replacement
n=10
mask=(1<<1024)-1
xs=[sum(((k>>i)&1)<<k for k in range(1024)) for i in range(10)]
gates=[('o',7,3),('o',1,5),('o',1,9),('o',3,6),('o',1,10),('o',5,9),('o',13,5),('a',11,0),('o',9,0),('o',18,3),('a',12,6),('a',2,14),('a',15,7),('a',8,16),('o',22,20),('a',4,19),('o',23,17),('o',21,26),('o',25,27),('o',24,28)]
def ev(gs):
 w=xs[:]
 for op,a,b in gs:w.append((w[a]&w[b]) if op=='a' else (w[a]|w[b]) if op=='o' else (~w[a]&mask))
 return w[-1]
target=ev(gates)
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
assert target==sum(1<<k for k in range(1024) if any((k>>a)&1 and (k>>b)&1 for a,b in edges))
# Remove one gate, repair every subsequent reference to it using a different preceding wire.
for deleted in range(20):
 for repl in range(10+deleted):
  gs=[]
  for j,(op,a,b) in enumerate(gates):
   if j==deleted:continue
   def remap(v):
    if v==10+deleted:v=repl
    return v-(v>10+deleted)
   gs.append((op,remap(a),remap(b)))
  if ev(gs)==target: print('FOUND',deleted,repl,gs);quit()
print('No single deletion with uniform earlier-wire replacement')
def live(gs):
 todo=[29]; seen=set()
 while todo:
  i=todo.pop()
  if i<10 or i in seen:continue
  seen.add(i);op,a,b=gs[i-10];todo.append(a)
  if op!='n':todo.append(b)
 return len(seen)
for j in range(20):
 for op in ('a','o','n'):
  for a,b in combinations_with_replacement(range(10+j),2) if op!='n' else ((k,k) for k in range(10+j)):
   v=gates.copy();v[j]=(op,a,b)
   if ev(v)==target and live(v)<20:
    print('FOUND changed gate',j,'to',op,a,b,'live',live(v),v);quit()
print('No single gate replacement yields redundant gate')
