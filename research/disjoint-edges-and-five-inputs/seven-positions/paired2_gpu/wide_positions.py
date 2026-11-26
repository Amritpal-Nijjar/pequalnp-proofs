"""Merge semantically interchangeable prefixes before the NOT, then check their suffixes."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import struct
import time

from opencl_replay import ReplayDevice
from run_search import TARGET, physical, write_status
from run_live import factors, encode, independent_witness, no_dead, prefix_debt
from slot_prefixes import SYMMETRIES, extend, rename


def pack_prefix(gates):
    return bytes(i for op,pins in gates for i in (op,pins[0],pins[1] if len(pins)>1 else 255))


def unpack_prefix(data):
    return [(data[i],[data[i+1]] if data[i+2]==255 else [data[i+1],data[i+2]]) for i in range(0,len(data),3)]


def state_key(gates):
    bank=physical(gates);debt=prefix_debt(gates)
    assert len(bank)==len(set(bank))
    # Raw inputs, paid gates and unpaid gates receive separate tags. Before the
    # NOT, this preserves its possible head and the liveness role of an ignored pin.
    tags=[0 if i<5 else 1+int(bool(debt & (1<<i))) for i in range(len(bank))]
    best=min(tuple(sorted(rename(v,m)*4+tag for v,tag in zip(bank,tags))) for m in SYMMETRIES)
    return struct.pack('<'+'Q'*len(best),*best)


def add_nots(gates):
    debt=prefix_debt(gates)
    for head in range(5,5+len(gates)):
        yield gates+[(2,[head])]
        for extra in range(5,5+len(gates)):
            if head!=extra and debt&(1<<extra): yield gates+[(2,[head,extra])]


def prepare(position, path, meta, limit):
    old={state_key([]):b''};stages=[]
    for depth in range(position+1):
        new={};tries=0;begin=time.perf_counter()
        for idx,packed in enumerate(old.values()):
            if idx%32==0 and time.time()>limit-3: raise TimeoutError('Prefix preparation reached the time cap')
            prefix=unpack_prefix(packed)
            for candidate in (add_nots(prefix) if depth==position else extend(prefix)):
                tries+=1;tag=state_key(candidate)
                if tag not in new: new[tag]=pack_prefix(candidate)
        stages.append({'gates':depth+1,'transitions':tries,'states':len(new),'sec':round(time.perf_counter()-begin,2)})
        print('Prepared',stages[-1],flush=True);old=new
    # Sorting the compact serializations makes the coverage order reproducible.
    all_bytes=b''.join(sorted(old.values()));path.write_bytes(all_bytes)
    write_status(meta,{'position':position,'length':3*(position+1),'states':len(old),'stages':stages,
                      'sha256':hashlib.sha256(all_bytes).hexdigest()})


def planted(position):
    if position==4:
        return [(0,[0,1]),(1,[2,3]),(0,[4,6]),(1,[7,1]),(2,[5,8]),(0,[9,2]),
                (1,[10,0]),(0,[11,3]),(1,[12,4]),(0,[13,1])]
    assert position==5
    return [(0,[0,1]),(1,[2,3]),(0,[4,6]),(1,[7,1]),(0,[8,0]),(2,[5,9]),
            (0,[10,2]),(1,[11,0]),(0,[12,3]),(1,[13,4])]


def scan(position, path, meta, outfile, limit):
    code=path.read_bytes();m=json.loads(meta.read_text());assert hashlib.sha256(code).hexdigest()==m['sha256']
    width=m['length'];n=5+position+1;early=10-position-1-2;s,low,domain=factors(n,early)
    assert s==early and low==domain and domain < 2**28
    dev=ReplayDevice(131072);start=time.perf_counter();done=0;hits=0
    example=planted(position);prefix=example[:position+1];near=physical(example)[-1]
    assert no_dead(example);ix=encode(example[position+1:-2],n);dev.set_bank(physical(prefix))
    assert dev.count_live(early,ix,0,s,prefix_debt(prefix),1,near)==(1,0)
    assert independent_witness(prefix,early,ix,near) is not None
    report={'target':TARGET,'not_slot_zero_based':position,'device':dev.name,'total_prefixes':m['states'],
            'prefix_metadata':m,'prefixes_completed':0,'states_per_prefix':domain,'tested_states':0,
            'hits':0,'witnesses':[],'positive_control':{'table':near,'early_index':ix,'ignored_pin':example[position][1][1]},'complete':False}
    write_status(outfile,report);last=start
    try:
        for off in range(0,len(code),width):
            if time.time()>=limit-2:return
            prefix=unpack_prefix(code[off:off+width]);bank=physical(prefix);debt=prefix_debt(prefix)
            dev.set_bank(bank);found,index=dev.count_live(early,0,0,s,debt,domain,TARGET)
            hits+=found;done+=1
            if found:
                witness=independent_witness(prefix,early,index,TARGET);assert witness is not None
                report['witnesses'].append({'gates':witness,'output':14});print('QUALIFYING WITNESS',witness,flush=True);return
            now=time.perf_counter()
            if now-last>=2:
                report.update(prefixes_completed=done,tested_states=done*domain,hits=hits,elapsed_s=round(now-start,2))
                write_status(outfile,report);last=now
        report['complete']=True
    finally:
        report.update(prefixes_completed=done,tested_states=done*domain,hits=hits,elapsed_s=round(time.perf_counter()-start,2),kernel_s=round(dev.gpu_ms/1000,3),finished_utc=datetime.now(timezone.utc).isoformat(timespec='seconds'))
        write_status(outfile,report);dev.close()


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('mode', choices=('prepare','scan'));p.add_argument('folder',type=Path)
    p.add_argument('--deadline',required=True);p.add_argument('--position',type=int,choices=(4,5),default=4)
    o=p.parse_args();end=datetime.fromisoformat(o.deadline.replace('Z','+00:00')).timestamp()
    binpath=o.folder/f'slot{o.position}_prefixes.bin';metadata=o.folder/f'slot{o.position}_prefixes.json'
    if o.mode=='prepare':prepare(o.position,binpath,metadata,end)
    else:scan(o.position,binpath,metadata,o.folder/f'slot_{o.position}_results.json',end)
