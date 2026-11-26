"""Independent computational exclusion attempt for a NOT immediately after the first gate."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time

from opencl_replay import ReplayDevice
from run_search import TARGET, physical, write_status
from run_live import encode, independent_witness, prefix_debt
from slot_prefixes import groups, SYMMETRIES, key


def family(prefix):
    op,pins = prefix[0]
    return ('OR' if op else 'AND')+'('+','.join(map(str,pins))+')'


def validate(device, data, position, classes):
    checks=[]
    examples = [(int(row),v['gates'],TARGET^(1<<int(row))) for row,v in data.items() if v['gates'][position][0]==2]
    if position==3:
        specimen=[(0,[0,1]),(1,[2,3]),(0,[4,6]),(2,[5,7]),(0,[8,2]),(1,[9,0]),
                  (0,[10,3]),(1,[11,4]),(0,[12,1]),(1,[13,5])]
        examples.append(('syntactic second NOT pin',specimen,physical(specimen)[-1]))
    assert examples
    for row,gates,near in examples:
        prefix=gates[:4]; assert gates[position][0]==2 and key(prefix) in classes
        bank=physical(prefix);device.set_bank(bank);debt=prefix_debt(prefix)
        known=encode(gates[4:-2],len(bank))
        assert device.count_live(4,known,0,4,debt,1,near)==(1,0)
        assert independent_witness(prefix,4,known,near) is not None
        for at,count,table in [(known,256,near),(max(0,known-23),256,near),(100000,65536,TARGET)]:
            flags=device.run_live(4,at,0,4,debt,count,table)
            number,first=device.count_live(4,at,0,4,debt,count,table)
            assert number==flags.count(1) and first==(flags.index(1) if number else 0xffffffff)
            checks.append([row,table,count,number])
    return checks


def main():
    parser=argparse.ArgumentParser();parser.add_argument('near',type=Path);parser.add_argument('status',type=Path)
    parser.add_argument('--deadline',required=True);parser.add_argument('--batch',type=int,default=16777216)
    parser.add_argument('--position',type=int,choices=(1,2,3),default=1)
    opt=parser.parse_args();end=datetime.fromisoformat(opt.deadline.replace('Z','+00:00')).timestamp()
    data=json.loads(opt.near.read_text(encoding='utf-8-sig')); begun=time.perf_counter();device=ReplayDevice(65536)
    classes,generated=groups(opt.position);representatives=list(classes.values())
    # The separate proof worker covers AND(0,4), NOT independently. Give all other families priority.
    representatives.sort(key=lambda p:(family(p)=='AND(0,4)',family(p),repr(p)))
    counts=Counter(family(p) for p in representatives)
    summary={k:{'total':v,'complete':0,'states':0,'hits':0} for k,v in counts.items()}
    ordered_digest=hashlib.sha256(json.dumps(representatives,separators=(',',':')).encode()).hexdigest()
    report={'device':device.name,'target':TARGET,'not_slot_zero_based':opt.position,'input_renamings':len(SYMMETRIES),
            'four_gate_prefixes_before_deduplication':generated,'canonical_prefixes':len(representatives),
            'ordered_prefix_sha256':ordered_digest,'families':summary,'complete':False,'candidates':[]}
    try:
        report['checks']=validate(device,data,opt.position,classes)
        assert all(p[opt.position][0]==2 for p in representatives)
        total=9*10*10*11*11*12*12*13
        assert total==203860800
        write_status(opt.status,report)
        current=''; last=time.perf_counter()
        for number,prefix in enumerate(representatives):
            label=family(prefix); row=summary[label]
            if label!=current:
                print('Starting',label,'with',row['total'],'prefix classes',flush=True);current=label
            bank=physical(prefix);assert len(bank)==9
            device.set_bank(bank);debt=prefix_debt(prefix);at=0
            while at<total:
                if time.time()>=end-2:
                    report['stopped_at_cap']=True;return
                qty=min(total-at,opt.batch)
                hits,first=device.count_live(4,at,0,4,debt,qty,TARGET)
                row['states']+=qty;row['hits']+=hits
                if hits:
                    ix=at+first;w=independent_witness(prefix,4,ix,TARGET)
                    assert w is not None
                    report['candidates'].append({'family':label,'prefix':prefix,'index':ix,'gates':w,'output':14})
                    print('QUALIFYING CANDIDATE',json.dumps(report['candidates'][-1]),flush=True)
                    return
                at+=qty
            row['complete']+=1
            if time.perf_counter()-last>2 or row['complete']==row['total']:
                report['current_prefix_number']=number; report['elapsed_s']=round(time.perf_counter()-begun,2)
                write_status(opt.status,report);last=time.perf_counter()
            if row['complete']==row['total']:
                print('Completed',label,row['states'],'states',row['hits'],'matches',flush=True)
        report['complete']=True
    finally:
        report['elapsed_s']=round(time.perf_counter()-begun,3);report['gpu_kernel_s']=round(device.gpu_ms/1000,3)
        report['finished_utc']=datetime.now(timezone.utc).isoformat(timespec='seconds');write_status(opt.status,report);device.close()


if __name__=='__main__':main()
