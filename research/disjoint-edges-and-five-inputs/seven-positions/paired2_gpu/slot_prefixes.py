"""Canonical four-gate prefixes with the unique inversion in slot 1 (zero-based)."""
from functools import cache
from itertools import combinations, permutations
from collections import Counter
from run_search import INPUTS, TARGET, MASK, apply_gate, physical
from run_live import prefix_debt


def inverse_map(p):
    return tuple(sum(((row >> i) & 1) << p[i] for i in range(5)) for row in range(32))


PERMUTATIONS = [inverse_map(p) for p in permutations(range(5))]
SYMMETRIES = [q for q in PERMUTATIONS if all((TARGET>>i & 1) == (TARGET>>q[i] & 1) for i in range(32))]


@cache
def rename(table, mapping):
    return sum(((table >> i) & 1) << mapping[i] for i in range(32))


def extend(prefix):
    bank = physical(prefix); old = {0,MASK,*bank,*(v^MASK for v in bank)}
    for a,b in combinations(range(len(bank)),2):
        for op in (0,1):
            if apply_gate(op,bank[a],bank[b]) not in old:
                yield prefix+[(op,[a,b])]


def key(prefix):
    bank=physical(prefix); assert len(set(bank)) == len(bank)
    debt=prefix_debt(prefix)
    return min(tuple(sorted((rename(v,p), int(bool(debt & 1<<i))) for i,v in enumerate(bank)))
            for p in SYMMETRIES)


def groups(position=1):
    if position not in (1,2,3):
        raise ValueError('The four-gate prefix must include the internal NOT')
    classes = {}; generated=0

    def expand(prefix):
        nonlocal generated
        if len(prefix)==4:
            generated+=1; tag=key(prefix)
            if tag not in classes: classes[tag]=prefix
            return
        if len(prefix)!=position:
            for one_more in extend(prefix): expand(one_more)
            return
        # A second NOT pin is ignored by evaluation, but it can give one
        # otherwise unused earlier gate its only syntactic read. Other second
        # pin choices have the same effect as omitting that pin.
        debt = prefix_debt(prefix)
        for head in range(5,5+position):
            expand(prefix+[(2,[head])])
            for other in range(5,5+position):
                if other!=head and debt & (1<<other): expand(prefix+[(2,[head,other])])

    expand([])
    return classes,generated


if __name__=='__main__':
    prefix,gen=groups()
    print('permutations preserving target:',len(SYMMETRIES),'raw fresh prefixes:',gen,'canonical states:',len(prefix))
    print(Counter((v[0][0],tuple(v[0][1])) for v in prefix.values()))
