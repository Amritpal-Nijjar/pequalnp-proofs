"""Enumerate projected two-AND schedules on representative four-edge residual forests."""
from itertools import combinations, combinations_with_replacement, product
import json

SHAPES = {
    'star4': [(0,1),(0,2),(0,3),(0,4)],
    'path4': [(0,1),(1,2),(2,3),(3,4)],
    'fork': [(0,1),(0,2),(0,3),(3,4)],
    'star3_edge': [(0,1),(0,2),(0,3),(4,5)],
    'star2_star2': [(0,1),(0,2),(3,4),(3,5)],
}

def fourcycle(edges, n):
    adj = [{y for x,y in edges if x==v} | {x for x,y in edges if y==v} for v in range(n)]
    return any(len(adj[x] & adj[y]) > 1 for x,y in combinations(range(n),2))

def graphs(U):
    n = max(max(edge) for edge in U)+1
    seen=set()
    for color in product((0,1), repeat=n):
        if color[0] or any(color[x]==color[y] for x,y in U):continue
        rest=[(x,y) for x,y in combinations(range(n),2) if color[x]!=color[y] and (x,y) not in U]
        for mask in range(1<<len(rest)):
            G=sorted(U+[e for i,e in enumerate(rest) if mask>>i&1])
            if fourcycle(G,n):continue
            key=(tuple(color),tuple(G))
            if key not in seen:
                seen.add(key);yield n,color,G

def test(U,n,color,G,guard=True,least=False):
    points=[(i,j) for i in range(n) for j in range(i,n)]
    bits=[sum(1<<r for r,p in enumerate(points) if i in p) for i in range(n)]
    pos=[1<<points.index(e) for e in U]
    safe=sum(1<<points.index(e) for e in G)
    adj=[{y for x,y in G if x==v} | {x for x,y in G if y==v} for v in range(n)]
    forbidden=set()
    for u,v in U:
        for x,z in ((u,v),(v,u)):
            for y in adj[z]-{x}:forbidden.add((1<<x)|(1<<y))
    rawvals={}
    for m in range(1<<n):
        verts=[v for v in range(n) if m>>v&1]
        if len({color[v] for v in verts})>1:continue
        if guard and any(m&k==k for k in forbidden):continue
        row=0
        for v in verts:row|=bits[v]
        rawvals[row]=m
    first={x&y:(rawvals[x],rawvals[y]) for x,y in combinations_with_replacement(rawvals,2)}
    models=visits=0; witness=None
    for d0,ab in first.items():
        ports={x:(m,False) for x,m in rawvals.items()}
        for x,m in rawvals.items():ports.setdefault(x|d0,(m,True))
        second={x&y:(ports[x],ports[y]) for x,y in combinations_with_replacement(ports,2)}
        for d1,cd in second.items():
            visits+=1
            if least and any((d >> points.index((v,v))) & 1 and not any(d & p and not bits[v] & p for p in pos)
                             for d in (d0,d1) for v in range(n)):
                continue
            terms=[d0&d1]+[d&r for d in (d0,d1) for r in bits]
            cover=0
            for t in terms:
                if not t&~safe:cover|=t
            if all(cover&p for p in pos):
                models+=1
                if witness is None:witness=[ab,cd]
    return visits,models,witness

if __name__=='__main__':
    out={}
    for name,U in SHAPES.items():
        results=[]
        for n,color,G in graphs(U):
            count,models,witness=test(U,n,color,G)
            results.append({'color':color,'G':G,'count':count,'models':models,'witness':witness})
        out[name]=results
        print(name,len(results),sum(x['count'] for x in results),sum(x['models'] for x in results),flush=True)
    from pathlib import Path
    (Path(__file__).parent/'four-shapes.json').write_text(json.dumps(out),encoding='utf8')
