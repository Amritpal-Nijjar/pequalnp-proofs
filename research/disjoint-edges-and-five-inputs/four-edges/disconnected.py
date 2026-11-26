"""Independent finite relaxation for four residual edges, assuming both exceptional ORs are visible."""
from itertools import combinations, product
import json
from shapes import SHAPES, graphs


def run(edges, n, color, graph):
    pairs = [(i,j) for i in range(n) for j in range(i,n)]
    row = {p:1 << i for i,p in enumerate(pairs)}
    bits = [sum(r for p,r in row.items() if i in p) for i in range(n)]
    pos = [row[e] for e in edges]
    safe = sum(row[e] for e in graph)
    vertices = list(range(n))
    forbidden = set()
    for u,v in edges:
        for x,z in ((u,v),(v,u)):
            for i,j in graph:
                if z in (i,j):
                    other = i+j-z
                    if other != x:
                        forbidden.add((1 << x) | (1 << other))
    menu = []
    for mask in range(1 << n):
        supp = [i for i in vertices if mask >> i & 1]
        if len({color[i] for i in supp}) <= 1 and not any(mask & f == f for f in forbidden):
            menu.append((mask,sum(r for p,r in row.items() if any(t in supp for t in p))))
    cache = {}
    clean = needed = charged = total = 0
    witness = None
    for (ma,va),(mb,vb),(mc,vc),(md,vd) in product(menu, repeat=4):
        d0 = va & vb
        for a,b in product((0,1), repeat=2):
            total += 1
            d1 = (vc | (d0 if a else 0)) & (vd | (d0 if b else 0))
            key = d0,d1
            if key not in cache:
                terms = [d0 & d1] + [d & bv for d in (d0,d1) for bv in bits]
                covered = 0
                for t in terms:
                    if not t & ~safe:
                        covered |= t
                wins = all(covered & r for r in pos)
                req = all(not (d & row[(i,i)]) or any(d & r and not bits[i] & r for r in pos)
                          for d in (d0,d1) for i in vertices) if wins else False
                counts = [max((sum(i in e and not (other & r) for e,r in zip(edges,pos))
                               for i in vertices if d & row[(i,i)]),default=0)
                          for d,other in ((d0,d1),(d1,d0))] if req else [0,0]
                cache[key] = wins,req,counts
            wins,req,counts = cache[key]
            if not wins:
                continue
            clean += 1
            if not req:
                continue
            needed += 1
            # A raw-bearing operand firing on a pair with neither endpoint raw
            # guarantees a prior exception by BranchCharge.earlier.
            before = any(mask and d1 & r and not raw & r for mask,raw in ((mc,vc),(md,vd)) for r in pos)
            if counts[0] > 2 or counts[1] + int(before) > 2:
                continue
            charged += 1
            if witness is None:
                witness = [ma,mb,mc,md,a,b]
    return dict(encodings=total,clean=clean,essential=needed,charged=charged,survivor=witness)


if __name__ == '__main__':
    recs = []
    for shape in ('star3_edge','star2_star2'):
        edges = SHAPES[shape]
        for n,color,graph in graphs(edges):
            recs.append(dict(shape=shape,color=color,graph=graph,**run(edges,n,color,graph)))
    print(json.dumps(recs,indent=2))
