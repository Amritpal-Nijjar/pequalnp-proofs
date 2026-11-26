"""Test the one-visible-OR relaxation on two disjoint two-edge stars."""
from itertools import combinations_with_replacement
from functools import lru_cache
import json
import sys

EDGES = [(0,1),(0,2),(3,4),(3,5)]
LEFT = {0,3}
BITS = [sum(1 << r for r in range(64) if r & (1 << i)) for i in range(6)]
POS = [1 << ((1 << i) | (1 << j)) for i,j in EDGES]
SINGLE = [1 << (1 << i) for i in range(6)]
ROWS = (1 << 64)-1
TARGET = (BITS[0] & (BITS[1] | BITS[2])) | (BITS[3] & (BITS[4] | BITS[5]))
TESTED = sum(1 << r for r in range(64) if '--pairs' not in sys.argv or r.bit_count() <= 2)
FORBIDDEN = (BITS[0] | BITS[3]) & (~TARGET & TESTED)
VALS = [sum(1 << r for r in range(64) if r & m) for m in range(64)]
GOOD = [m for m in range(64)
        if not (m & 9 and m & 54) and m & 6 != 6 and m & 48 != 48]


@lru_cache(None)
def test(d0,d1):
    signal = any(not y & FORBIDDEN and all(y & r for r in POS) for y in (d0,d1,d0|d1))
    clean = [d & b for d in (d0,d1) for b in BITS] + [d0&d1]
    covered = 0
    for t in clean:
        if not t & ~TARGET & TESTED:
            covered |= t
    if not all(covered & r for r in POS):
        return (0,0,0,int(signal))
    needed = all(not (d & SINGLE[i]) or any(d&r and not BITS[i]&r for r in POS)
                 for d in (d0,d1) for i in range(6))
    return 1,int(needed),int(needed and signal),int(signal)


def enumerate_menus(menus):
    counts=[0,0,0,0,0]
    found=None
    for menu in menus:
        first = {VALS[a]&VALS[b]:(a,b) for a,b in combinations_with_replacement(menu,2)}
        for d0,ab in first.items():
            ports = {VALS[m]:(m,False) for m in menu}
            for m in menu:
                ports.setdefault(VALS[m]|d0,(m,True))
            second = {a&b:(ports[a],ports[b]) for a,b in combinations_with_replacement(ports,2)}
            for d1,cd in second.items():
                counts[0]+=1
                wins,needed,guarded,signal=test(d0,d1)
                counts[1]+=wins; counts[2]+=needed; counts[3]+=guarded; counts[4]+=signal
                if found is None and guarded:
                    found=[ab,cd]
    return dict(table_pairs_summed_over_menus=counts[0],clean=counts[1],essential=counts[2],
                single_visible_signal=counts[3],signal_alone=counts[4],example=found)


if __name__=='__main__':
    bad=sorted(set(range(64))-set(GOOD))
    bad_pairs=[6,48]
    print(json.dumps(dict(tested_inputs=TESTED.bit_count(),good=GOOD,one_allowed_bad=enumerate_menus([GOOD+[m] for m in bad]),
                          two_bad_control=enumerate_menus([GOOD+bad_pairs])),indent=2))
