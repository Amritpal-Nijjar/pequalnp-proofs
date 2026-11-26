"""Independently search circuit wirings on CPU, with Lean-proved restriction bounds."""
import argparse
from collections import Counter
import concurrent.futures as futures
import ctypes as ct
from datetime import datetime,timezone
import itertools
import json
import os
from pathlib import Path
import random
import sys
import threading
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'paired2_gpu'))
from run_live import independent_witness,no_dead,prefix_debt
from run_search import TARGET, physical, write_status
from wide_positions import unpack_prefix
from sweep import code,prefix8,STRIDES

U,Q=ct.c_uint32,ct.c_uint64
P=ct.POINTER
gate_reps=[code(0,0,1),code(0,1,2),code(0,1,4),code(1,0,1),code(1,1,2),code(1,1,4),code(1,0,4)]


def load_dll():
    dll=ct.CDLL(str(HERE/'native.dll'))
    dll.search.argtypes=[U,U,U,U,U,P(U),P(Q),P(U)]
    dll.search.restype=U
    dll.endcheck.argtypes=[P(U),U,U,P(U)]
    dll.endcheck.restype=U
    return dll


def checks(dll,codes,stop):
    rng=random.Random(18096)
    positive=negative=0
    for i in range(320):
        k=rng.randrange(len(codes)//15)
        root=unpack_prefix(codes[15*k:15*(k+1)])
        pos=6+i%2
        gates=prefix8(root,pos,rng.randrange(STRIDES[pos]))
        wires=physical(gates)
        # Alternate planted truth tables and the actual target.
        if i%3:
            v=wires[rng.randrange(13)]|wires[rng.randrange(13)]
            target=v&wires[rng.randrange(13)]
        else:
            target=TARGET
        direct=independent_witness(gates,0,0,target)
        out=(U*6)()
        got=dll.endcheck((U*13)(*wires),prefix_debt(gates),target,out)
        assert bool(got)==(direct is not None)
        if got:
            made=gates+[(out[j],[out[j+1],out[j+2]]) for j in (0,3)]
            assert no_dead(made) and physical(made)[-1]==target
            positive+=1
        else: negative+=1
    # A deliberately live chain plants solutions across all seven inverter positions.
    for pos in range(1,8):
        gates=[(0,[0,1])]
        for j in range(1,10):
            gates.append((2,[4+j]) if j==pos else (j%2,[j%5,4+j]))
        target=physical(gates)[-1]
        j=2 if pos==1 else 1
        second=code(gates[j][0],*gates[j][1])
        if stop.value: raise TimeoutError('CPU controls reached the cap')
        seen=(Q*10)(); wire=(U*30)()
        assert dll.search(pos,gate_reps[0],second,target,0,ct.byref(stop),seen,wire)
        winning=[(wire[3*j],[wire[3*j+1]] if wire[3*j]==2 else [wire[3*j+1],wire[3*j+2]]) for j in range(10)]
        assert no_dead(winning) and physical(winning)[-1]==target
    return {'direct_positive':positive,'direct_negative':negative,'whole_search_positives':7}


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--deadline',required=True)
    p.add_argument('--workers',type=int,default=min(12,max(2,(os.cpu_count() or 4)//2)))
    args=p.parse_args()
    deadline=datetime.fromisoformat(args.deadline.replace('Z','+00:00')).timestamp()
    dll=load_dll()
    stop=U(0)
    timer=threading.Timer(max(0,deadline-time.time()-3),lambda:setattr(stop,'value',1))
    timer.daemon=True
    timer.start()
    tasks=[]
    for pos in (7,6,5,4,3,2,1):
        n=7 if pos==1 else 6
        for first in gate_reps:
            for a,b in itertools.combinations(range(n),2):
                for op in (0,1):
                    tasks.append((pos,first,code(op,a,b)))
    counts=Counter(t[0] for t in tasks)
    result={'target':TARGET,'workers':args.workers,'positions':{str(k):{'shards':v,'finished':0,'visits':[0]*10} for k,v in counts.items()},'witnesses':[]}
    path=HERE/'native_results.json'
    def run(job):
        pos,a,b=job
        seen=(Q*10)()
        solution=(U*30)()
        found=dll.search(pos,a,b,TARGET,1,ct.byref(stop),seen,solution)
        return pos,list(seen),list(solution) if found else None
    result['controls']=checks(dll,(HERE/'roots_codes.bin').read_bytes(),stop)
    print('CPU controls',result['controls'],flush=True)
    started=time.monotonic()
    for pos,obj in result['positions'].items():
        obj['shard_total']=obj['shards']
    with futures.ThreadPoolExecutor(args.workers) as pool:
        jobs=iter(tasks)
        pending={pool.submit(run,j) for j in itertools.islice(jobs,args.workers)}
        last=0
        while pending and not stop.value:
            if time.time()>=deadline-3:
                stop.value=1
                break
            done,pending=futures.wait(pending,timeout=.3,return_when=futures.FIRST_COMPLETED)
            for f in done:
                pos,seen,out=f.result()
                row=result['positions'][str(pos)]
                row['finished']+=1
                row['visits']=[a+b for a,b in zip(row['visits'],seen)]
                if out is not None:
                    gates=[(out[3*j],[out[3*j+1]] if out[3*j]==2 else [out[3*j+1],out[3*j+2]]) for j in range(10)]
                    assert no_dead(gates) and physical(gates)[-1]==TARGET
                    result['witnesses'].append(gates)
                    stop.value=1
                    break
                new=next(jobs,None)
                if new is not None:pending.add(pool.submit(run,new))
            if time.monotonic()-last>2:
                result['elapsed_s']=round(time.monotonic()-started,2)
                write_status(path,result)
                last=time.monotonic()
    result['complete']=all(v['shards']==v['finished'] for v in result['positions'].values())
    result['finished_utc']=datetime.now(timezone.utc).isoformat(timespec='seconds')
    result['elapsed_s']=round(time.monotonic()-started,2)
    write_status(path,result)
    print('Native result:',result['complete'],[(p,v['finished']) for p,v in result['positions'].items()],flush=True)
    timer.cancel()


if __name__=='__main__':
    main()
