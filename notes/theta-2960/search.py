"""Exhaustive signed AIG search with exact functional-dependence and induced-graph cuts."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from itertools import groupby, permutations, product

def canonical(edges):
    deg={}
    for i,j in edges:deg[i]=deg.get(i,0)+1;deg[j]=deg.get(j,0)+1
    if not deg:return (),()
    classes=[list(g) for _,g in groupby(sorted(deg,key=deg.get),key=deg.get)]
    best=None
    for p in product(*(permutations(cls) for cls in classes)):
        order=sum(p,()); inv={old:new for new,old in enumerate(order)}
        transformed=tuple(sorted(tuple(sorted((inv[i],inv[j]))) for i,j in edges))
        if best is None or transformed<best[0]:best=(transformed,order)
    return best
@lru_cache(None)
def graph_key(edges):
 return canonical(edges)
class Scan:
 def __init__(self,edges,budget,minor_bounds):
  self.e=edges;self.n=1+max(max(e) for e in edges);self.m=(1<<(1<<self.n))-1;self.b=budget
  self.v=tuple(sum((x>>i&1)<<x for x in range(1<<self.n)) for i in range(self.n))
  self.y=0
  for i,j in edges:self.y |= self.v[i]&self.v[j]
  self.hits={};self.levels={};self.memo=set();self.limit=30000;self.expanded={}
  pos=[x for x in range(1<<self.n) if self.y>>x&1];neg=[x for x in range(1<<self.n) if not self.y>>x&1]
  self.p=pos; self.nrows=neg
  self.allsep=(1<<(len(pos)*len(neg)))-1
  self.minors=[]
  for kept in range(1,1<<self.n):
   if kept+1==1<<self.n:continue
   ee=tuple((i,j) for i,j in edges if kept>>i & kept>>j &1)
   if not ee:continue
   canon,order=graph_key(ee)
   if sum(1<<i for i in order)!=kept:continue
   lo=minor_bounds[canon];face=sum(1<<x for x in range(1<<self.n) if not x&~kept)
   if lo+self.n-len(order)<budget-2:continue
   self.minors.append((face,lo))
 @lru_cache(None)
 def sep(self,w):
  neg=sum(((w>>x)&1)<<i for i,x in enumerate(self.nrows));mask=(1<<len(self.nrows))-1
  return sum((neg ^ (mask if w>>x&1 else 0)) << (k*len(self.nrows)) for k,x in enumerate(self.p))
 def go(self,v,b,paid,trail):
  if self.y in v:raise ValueError(trail)
  if len(v)>b+1:return
  key=(v,b,paid)
  if key in self.memo:return
  self.memo.add(key);self.levels[b]=self.levels.get(b,0)+1
  if len(self.memo)>self.limit:raise TimeoutError
  cuts=[]
  for i,(face,L) in enumerate(self.minors):
   wp={u&face for u in v};cf=sum((u&face) in (0,face) for u in v)
   if paid[i]+b < L+cf:return
   cuts.append((face,wp|{face^u for u in wp}|{0,face}|{q&face for q in self.v}|{face^(q&face) for q in self.v},paid[i]))
  self.expanded[b]=1+self.expanded.get(b,0)
  if b==0:return
  for i,a in enumerate(v):
   for j in range(i):
    c=v[j];rem=v[:j]+v[j+1:i]+v[i+1:]
    for ka,kb in ((0,0),(1,0),(0,1),(1,1)):
     pool=rem+((a,) if ka else ())+((c,) if kb else ())
     if len(pool)>=b:continue
     miss=self.allsep
     for x in pool:miss &= ~self.sep(x)
     for p,q in ((0,0),(0,1),(1,0),(1,1)):
      z=(a^(self.m*p)) & (c^(self.m*q))
      if z&1:z^=self.m
      if not z or z in v:continue
      if miss & ~self.sep(z):continue
      cost=tuple(s+int(z&f not in wp) for f,wp,s in cuts)
      self.go(tuple(sorted(pool+(z,))),b-1,cost,trail+[(a,c,p,q,z)])
def run():
 edges=((0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(3,6))
 minors={}
 for mask in range(1,128):
  ee=tuple(e for e in edges if (mask>>e[0])&(mask>>e[1])&1)
  if ee:minors[graph_key(ee)[0]]=0
 for i,e in enumerate(sorted(minors,key=lambda e:(max(max(p) for p in e),len(e),e))):
  n=1+max(max(p) for p in e)
  vc=min(bin(x).count('1') for x in range(1<<n) if all(x>>a&1 or x>>b&1 for a,b in e))
  target=len(e)+vc-1
  r=Scan(e,target-1,minors)
  try:
   r.go(tuple(sorted(r.v)),r.b,tuple(0 for _ in r.minors),[])
   minors[e]=target
   print(i,n,target,e,sorted(r.levels.items()),'closed',sorted(r.expanded.items()),flush=True)
  except TimeoutError:
   print(i,n,target,e,sorted(r.levels.items()),'exceeded',flush=True)
   minors[e]=n-1
  except ValueError as ex:
   print(i,'WITNESS',e,ex,flush=True);minors[e]=n-1
if __name__=='__main__':run()
