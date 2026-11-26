"""Exact row tests after fixing the signal feeding the only NOT gate."""
from collections import Counter
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
TARGET=0xfee8eaa8
MASK=(1<<32)-1
le=lambda x,y: x & y == x


def monotone_tables(arity):
    tables=[0,1]
    for level in range(arity):
        half=1<<level
        tables=[low|(high<<half) for low in tables for high in tables if le(low,high)]
    return tables


def rows(source):
    result=[]
    for bit in (0,1):
        positives=[r for r in range(32) if (source>>r)&1==bit and TARGET>>r&1]
        negatives=[r for r in range(32) if (source>>r)&1==bit and not TARGET>>r&1]
        minimal=[r for r in positives if not any(q!=r and le(q,r) for q in positives)]
        maximal=[r for r in negatives if not any(q!=r and le(r,q) for q in negatives)]
        assert all(any(le(q,r) for q in minimal) for r in positives)
        assert all(any(le(r,q) for q in maximal) for r in negatives)
        result.extend(minimal+maximal)
    assert len(result)==len(set(result))
    return sorted(result)


def main():
    all_tables=monotone_tables(5)
    assert len(all_tables)==7581 and TARGET in all_tables
    sources=[s for s in all_tables if not le(s,TARGET) and not le(TARGET,s)]
    counts=Counter()
    examples={}
    for s in sources:
        needed=rows(s)
        counts[len(needed)]+=1
        examples.setdefault(len(needed),{'source':s,'rows':needed})
    result={'target':TARGET,'all_monotone_tables':len(all_tables),'incomparable_sources':len(sources),
            'histogram':dict(sorted(counts.items())),'examples':examples}
    (HERE/'source_rows.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print({k:v for k,v in result.items() if k!='examples'})


if __name__=='__main__':
    main()
