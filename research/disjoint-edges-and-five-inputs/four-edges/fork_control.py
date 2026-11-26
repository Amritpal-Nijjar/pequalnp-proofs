"""Check every ordered raw-mask and lift-flag assignment for the fork chart."""
from itertools import product
import json

def replay(monochromatic=True, full=False):
    U=[(0,1),(0,2),(0,3),(3,4)]
    rows=[i for i in range(32) if full or i.bit_count()<=2]
    bit=[sum(1<<j for j,r in enumerate(rows) if r&(1<<v)) for v in range(5)]
    row=lambda x: 1<<rows.index(x)
    yes=[row((1<<u)|(1<<v)) for u,v in U]
    safe=sum(1<<i for i,r in enumerate(rows) if any(r&(1<<u) and r&(1<<v) for u,v in U))
    singles=[row(1<<i) for i in range(5)]
    menu=[i for i in range(32) if (not monochromatic or i.bit_count()<=1)
          and not any(i&pair==pair for pair in [6,10,12,17])]
    val={m:sum(1<<i for i,r in enumerate(rows) if r&m) for m in menu}
    checked=cover=minimal=guarded=0; example=None
    cache={}
    for ma,mb,mc,md in product(menu,repeat=4):
        d0=val[ma]&val[mb]
        for a,b in product((0,1),repeat=2):
            checked+=1
            d1=(val[mc]|(d0 if a else 0)) & (val[md]|(d0 if b else 0))
            key=d0,d1
            if key not in cache:
                t=[d0&d1]+[z&r for z in (d0,d1) for r in bit]
                union=0
                for term in t:
                    if not term&~safe:union|=term
                wins=all(union&r for r in yes)
                needed=all(not (z&s) or any(z&r and not r&bit[i] for r in yes) for z in (d0,d1) for i,s in enumerate(singles))
                cache[key]=wins,needed
            wins,needed=cache[key]
            if not wins:continue
            cover+=1
            if not needed:continue
            minimal+=1
            bad=(d1&singles[0] and not d0&yes[0] and not d0&yes[1] and d1&yes[3] and mc&1 and not mc&24)
            if not bad:
                guarded+=1
                if example is None:example=[ma,mb,mc,md,a,b]
    return dict(mono=monochromatic,all_rows=full,encodings=checked,clean=cover,essential=minimal,with_charge=guarded,example=example)
if __name__=='__main__':
    print(json.dumps([replay(m,f) for m in (True,False) for f in (False,True)],indent=2))
