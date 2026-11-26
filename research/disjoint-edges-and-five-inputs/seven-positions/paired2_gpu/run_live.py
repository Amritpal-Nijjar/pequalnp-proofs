"""Check rewired suffixes including the posted use of every non-output gate."""
import argparse
from collections import defaultdict
import ctypes as ct
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import random
import statistics
import time

from opencl_replay import ReplayDevice
from run_search import INPUTS, PAIRS, PAIR_BYTES, ROOT, TARGET, apply_gate, decode, physical, write_status


def no_dead(gates):
    read = {p for _, pins in gates for p in pins}
    return all(5+i in read for i in range(len(gates)-1))


def prefix_debt(gates):
    read = {p for _, pins in gates for p in pins}
    return sum(1 << (5+i) for i in range(len(gates)) if 5+i not in read)


def encode(gates, n):
    result = 0; stride = 1
    for op, pins in gates:
        a, b = sorted(pins)
        assert op in (0,1) and b < n
        result += stride*(b*(b+1)+2*a+op)
        stride *= n*(n+1); n += 1
    return result


def all_prefixes(data, suffix):
    groups = defaultdict(list)
    for key, entry in data.items():
        gates = entry['gates']; prefix = gates[:10-suffix]
        if sum(t == 2 for t,_ in prefix) != 1:
            continue
        assert physical(gates)[-1] == TARGET ^ (1 << int(key)) and no_dead(gates)
        assert all(t in (0,1) for t,_ in gates[len(prefix):])
        groups[tuple((t,tuple(p)) for t,p in prefix)].append((int(key),gates))
    return groups


def factors(n, early):
    s = 0; low = 1; total = 1
    for i in range(early):
        radix = (n+i)*(n+i+1); total *= radix
        if s == i and low*radix <= 2**32-1:
            low *= radix; s += 1
    assert total//low < 2**32
    return s, low, total


def independent_witness(prefix, early, index, target):
    wires, steps = decode(physical(prefix),early,index)
    fixed = list(prefix) + steps
    n = len(wires)
    for b in range(n):
        for a in range(b+1):
            for op in (0,1):
                v = apply_gate(op,wires[a],wires[b])
                for j in range(n+1):
                    other = wires[j] if j < n else v
                    for last in (0,1):
                        if apply_gate(last,v,other) != target:
                            continue
                        circuit = fixed + [(op,[a,b]),(last,[n,j])]
                        if no_dead(circuit):
                            assert all(p < 5+k for k,(_,pins) in enumerate(circuit) for p in pins)
                            assert sum(t==2 for t,_ in circuit)==1 and physical(circuit)[-1]==target
                            return circuit
    return None


def gpu_piece(device,prefix,early,begin,count,target):
    n = 5+len(prefix); s, low, total = factors(n,early)
    upper, off = divmod(begin,low)
    assert count <= low-off and begin+count <= total
    return device.run_live(early,off,upper,s,prefix_debt(prefix),count,target)


def native_function():
    fn = ct.CDLL(str(ROOT/'cpu_library.dll')).live_batch
    uint, byte = ct.c_uint32, ct.c_ubyte
    fn.argtypes = [ct.POINTER(uint),uint,ct.POINTER(byte),uint,uint,uint,uint,uint,uint,uint,ct.POINTER(byte)]
    fn.restype = None
    return fn


def audit(device, data, capacity):
    rng = random.Random(8177)
    fn = native_function(); pairs = (ct.c_ubyte*len(PAIR_BYTES)).from_buffer_copy(PAIR_BYTES)
    yes = no = 0; controls = []; measured = []
    for suffix in (5,6,7):
        for prefix, layouts in all_prefixes(data,suffix).items():
            bank = physical(prefix); n = len(bank); early = suffix-2; device.set_bank(bank)
            split,low,total = factors(n,early)
            for key,gates in layouts:
                idx = encode(gates[len(prefix):-2],n); table = TARGET^(1<<key)
                assert gpu_piece(device,prefix,early,idx,1,table) == b'\x01'
                assert independent_witness(prefix,early,idx,table) is not None
                yes += 1; controls.append([suffix,key])
            # Include indices beyond 2^32 when the seven-gate domain exceeds it.
            for _ in range(5):
                idx = rng.randrange(total); target = rng.choice([TARGET,rng.getrandbits(32),layouts[0][1] and TARGET^(1<<layouts[0][0])])
                found = independent_witness(prefix,early,idx,target) is not None
                assert gpu_piece(device,prefix,early,idx,1,target)[0] == found
                yes += found; no += not found
            if suffix == 7 and len(measured) < 3:
                count = min(capacity,262144); off = min(1234,low-count); upper = total//low-1
                b = (ct.c_uint32*n)(*bank); dst = (ct.c_ubyte*count)()
                start = time.perf_counter(); fn(b,n,pairs,early,off,upper,split,prefix_debt(prefix),count,TARGET,dst)
                native_ms = 1000*(time.perf_counter()-start)
                start = time.perf_counter(); flags = device.run_live(early,off,upper,split,prefix_debt(prefix),count,TARGET)
                gpu_ms = 1000*(time.perf_counter()-start)
                assert bytes(dst) == flags
                measured.append({'states':count,'native_one_core_ms':round(native_ms,3),'gpu_with_readback_ms':round(gpu_ms,3)})
    assert yes >= 21 and no > 0
    return {'control_rows':controls,'independent_yes':yes,'independent_no':no,'native_bytewise_controls':measured}


def crosscheck_relaxed_hits(device, near, report_path, capacity):
    old = json.loads(report_path.read_text()); details = []
    for item in old['groups']:
        if not item['target_hits']: continue
        suffix = item['suffix_gates']; early=suffix-2; row=item['rows'][0]
        prefix = near[str(row)]['gates'][:10-suffix]; physical_bank = physical(prefix)
        bank = item['bank']; assert len(set(physical_bank))==len(physical_bank)==len(bank)
        device.set_bank(bank); seen=0; valid=[]
        for at in range(0,item['total'],capacity):
            flags = device.run(early,at,min(capacity,item['total']-at),TARGET)
            k = flags.find(b'\x01')
            while k >= 0:
                seen += 1; _, steps = decode(bank,early,at+k)
                m = [physical_bank.index(v) for v in bank]; restored=[]
                for op,pins in steps:
                    restored.append((op,[m[i] for i in pins])); m.append(len(m))
                ix = encode(restored,len(bank)); witness=independent_witness(prefix,early,ix,TARGET)
                if witness: valid.append({'row':row,'gates':witness})
                k = flags.find(b'\x01',k+1)
        assert seen == item['target_hits']
        details.append({'prefix_rows':item['rows'],'relaxed_matches':seen,'fully_live':valid})
    return details


def run():
    args = argparse.ArgumentParser();args.add_argument('near',type=Path);args.add_argument('output',type=Path)
    args.add_argument('--deadline',required=True);args.add_argument('--batch',type=int,default=524288)
    args.add_argument('--suffixes',type=int,nargs='+',default=[5,6,7]);args.add_argument('--relaxed',type=Path)
    opt=args.parse_args();limit=datetime.fromisoformat(opt.deadline.replace('Z','+00:00')).timestamp()
    data=json.loads(opt.near.read_text(encoding='utf-8-sig')); dev=ReplayDevice(opt.batch)
    start=time.perf_counter();report={'device':dev.name,'target':TARGET,'complete':False,'groups':[],'found':[]}
    try:
        report['audit']=audit(dev,data,opt.batch)
        if opt.relaxed:
            report['relaxed_audit']=crosscheck_relaxed_hits(dev,data,opt.relaxed,opt.batch)
            for audit_row in report['relaxed_audit']:
                report['found'].extend(audit_row['fully_live'])
        write_status(opt.output,report);print('Validation passed',report.get('relaxed_audit'),flush=True)
        for suffix in opt.suffixes:
            groups=all_prefixes(data,suffix)
            for prefix, layouts in groups.items():
                bank=physical(prefix);n=len(bank);early=suffix-2;dev.set_bank(bank)
                split,low,total=factors(n,early); at=0; begun=time.perf_counter();lastsave=begun
                group={'suffix_gates':suffix,'prefix_rows':[x[0] for x in layouts], 'total':total,'tested':0,'hits':0}
                report['groups'].append(group)
                for key,gates in layouts:
                    ix=encode(gates[len(prefix):-2],n)
                    assert gpu_piece(dev,prefix,early,ix,1,TARGET^(1<<key))==b'\x01'
                while at<total:
                    if time.time() >= limit-2:
                        report['stopped_at_cap']=True;return
                    upper,off=divmod(at,low);count=min(opt.batch,low-off,total-at)
                    flags=dev.run_live(early,off,upper,split,prefix_debt(prefix),count,TARGET)
                    hits=flags.count(1)
                    if hits:
                        index=at+flags.index(1); witness=independent_witness(prefix,early,index,TARGET)
                        assert witness, (suffix,index)
                        report['found'].append({'row':layouts[0][0],'index':index,'gates':witness,'output':14})
                        print('EXACT CANDIDATE',json.dumps(report['found'][-1]),flush=True)
                    at+=count;group['tested']=at;group['hits']+=hits
                    now=time.perf_counter()
                    if now-lastsave>=3 or hits:
                        group['elapsed_s']=round(now-begun,3);write_status(opt.output,report);lastsave=now
                    if hits: return
                group['elapsed_s']=round(time.perf_counter()-begun,3);write_status(opt.output,report)
                print('Complete',suffix,group['prefix_rows'],total,'states',group['hits'],'qualifying matches',group['elapsed_s'],'s',flush=True)
        report['complete']=True
    finally:
        report['kernel_s']=round(dev.gpu_ms/1000,3);report['elapsed_s']=round(time.perf_counter()-start,3)
        report['finish_utc']=datetime.now(timezone.utc).isoformat(timespec='seconds')
        write_status(opt.output,report);dev.close()


if __name__=='__main__': run()
