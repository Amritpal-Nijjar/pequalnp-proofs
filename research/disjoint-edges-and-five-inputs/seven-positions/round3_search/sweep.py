"""Search both final NOT placements, checking the GPU against a direct CPU enumerator."""
import argparse
from array import array
import ctypes as ct
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import random
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'paired2_gpu'))
from opencl_replay import ReplayDevice, checked, i32, ptr, ref, u32
from run_live import independent_witness, no_dead, prefix_debt
from run_search import PAIRS, TARGET, physical, write_status
from wide_positions import unpack_prefix

STRIDES={6:102960, 7:101640}


def gate(code):
    return (code%2,list(PAIRS[code//2]))


def code(op,a,b):
    a,b=sorted((a,b))
    return b*(b+1)+2*a+op


def prefix8(root,position,index):
    if position==6:
        first,rem=divmod(index,936)
        inv,second=divmod(rem,156)
        return root+[gate(first),(2,[5+inv]),gate(second)]
    first,rem=divmod(index,924)
    second,inv=divmod(rem,7)
    return root+[gate(first),gate(second),(2,[5+inv])]


class GPU:
    def __init__(self,capacity):
        self.dev=ReplayDevice(64)
        d=self.dev
        err=i32()
        src=ct.c_char_p((HERE/'tail.cl').read_bytes())
        self.prog=ptr(d.cl.clCreateProgramWithSource(d.context,1,ref(src),None,ref(err)))
        checked(err.value,'placement program')
        result=d.cl.clBuildProgram(self.prog,1,ref(d.device),b'-cl-std=CL1.2',None,None)
        if result:
            log=ct.create_string_buffer(16384)
            d.cl.clGetProgramBuildInfo(self.prog,d.device,0x1183,len(log),log,None)
            raise RuntimeError(log.value.decode())
        self.kernel=ptr(d.cl.clCreateKernel(self.prog,b'search_placement',ref(err)))
        checked(err.value,'placement kernel')
        self.buf=ptr(d.cl.clCreateBuffer(d.context,4,capacity*44,None,ref(err)))
        checked(err.value,'root buffer')
        self.capacity=capacity

    def upload(self,payload):
        assert len(payload)%44==0 and len(payload)<=self.capacity*44
        self.count=len(payload)//44
        data=ct.create_string_buffer(payload)
        d=self.dev
        checked(d.cl.clEnqueueWriteBuffer(d.queue,self.buf,1,0,len(payload),data,0,None,None),'upload roots')

    def run(self,position,begin,count,goal):
        assert 0<count and begin+count<=self.count*STRIDES[position]<2**32
        result=(u32*2)(0,0xffffffff)
        d=self.dev
        checked(d.cl.clEnqueueWriteBuffer(d.queue,d.summary,1,0,8,result,0,None,None),'reset counts')
        args=[self.buf,d.pairs,u32(position),u32(begin),u32(count),u32(goal),d.summary]
        d.execute(self.kernel,args,count,d.summary,result)
        return result[0],result[1]

    def close(self):
        d=self.dev
        d.cl.clReleaseMemObject(self.buf)
        d.cl.clReleaseKernel(self.kernel)
        d.cl.clReleaseProgram(self.prog)
        d.close()


def validate(device, codes):
    chain=[(0,[0,1]),(1,[2,5]),(0,[3,6]),(1,[4,7]),(0,[0,8])]
    roots=[unpack_prefix(codes[:15]),chain,unpack_prefix(codes[-15:])]
    records=array('I')
    for gates in roots:
        records.extend(physical(gates)+[prefix_debt(gates)])
    device.upload(records.tobytes())
    samples=[]
    for pos in (6,7):
        first=code(1,9,1)
        if pos==6: index=(first*6+5)*156+code(0,11,2)
        else: index=(first*132+code(0,10,3))*7+6
        base=prefix8(chain,pos,index)
        circuit=base+[(1,[12,1]),(0,[13,4])]
        assert no_dead(circuit)
        target=physical(circuit)[-1]
        stride=STRIDES[pos]
        assert device.run(pos,stride+index,1,target)==(1,0)
        rng=random.Random(17625+pos)
        for start,n,goal in [(stride+index-3,10,target),(stride-2,5,TARGET),(stride*2-3,5,target),
                              *[(rng.randrange(3*stride-4),4,rng.choice([target,TARGET,0xffffffff,0])) for _ in range(12)]]:
            expected=[]
            for i in range(n):
                j,k=divmod(start+i,stride)
                if independent_witness(prefix8(roots[j],pos,k),0,0,goal) is not None:
                    expected.append(i)
            result=device.run(pos,start,n,goal)
            assert result==(len(expected),expected[0] if expected else 0xffffffff), (pos,start,result,expected)
            samples.append({'position':pos,'tested':n,'hits':len(expected),'target':goal})
    return samples


def main():
    args=argparse.ArgumentParser()
    args.add_argument('--deadline',required=True)
    args.add_argument('--batch',type=int,default=128)
    args.add_argument('--folder',type=Path,default=HERE)
    opt=args.parse_args()
    end=datetime.fromisoformat(opt.deadline.replace('Z','+00:00')).timestamp()
    root=opt.folder
    meta=json.loads((root/'roots.json').read_text())
    codes=(root/'roots_codes.bin').read_bytes()
    banks=(root/'roots_banks.bin').read_bytes()
    total=meta['roots']
    assert sha256(codes).hexdigest()==meta['codes_sha256'] and sha256(banks).hexdigest()==meta['banks_sha256']
    assert len(codes)==15*total and len(banks)==44*total
    device=GPU(opt.batch)
    path=root/'sweep.json'
    result={'target':TARGET,'device':device.dev.name,'root_metadata':meta,'witnesses':[],
            'positions':{str(p):{'roots_complete':0,'candidate_prefixes':0,'complete':False} for p in (6,7)}}
    try:
        result['cpu_crosschecks']=validate(device,codes)
        print('Validated GPU with direct CPU completion on both placements',flush=True)
        write_status(path,result)
        started=time.monotonic()
        last=started
        for start in range(0,total,opt.batch):
            count=min(opt.batch,total-start)
            device.upload(banks[44*start:44*(start+count)])
            for pos in (6,7):
                if time.time()>=end-3:
                    return
                stride=STRIDES[pos]
                hits,index=device.run(pos,0,stride*count,TARGET)
                if hits:
                    relative,slot=divmod(index,stride)
                    k=start+relative
                    pref=prefix8(unpack_prefix(codes[15*k:15*(k+1)]),pos,slot)
                    proof=independent_witness(pref,0,0,TARGET)
                    assert proof is not None and no_dead(proof) and physical(proof)[-1]==TARGET
                    result['witnesses'].append({'position':pos,'root':k,'index':slot,'gates':proof,'output':14})
                    print('QUALIFYING CIRCUIT',result['witnesses'][-1],flush=True)
                    return
                stage=result['positions'][str(pos)]
                stage.update(roots_complete=start+count,candidate_prefixes=(start+count)*stride,complete=start+count==total)
            if time.monotonic()-last>=2:
                result['elapsed_s']=round(time.monotonic()-started,2)
                write_status(path,result)
                last=time.monotonic()
        result['complete']=True
    finally:
        result['finished_utc']=datetime.now(timezone.utc).isoformat(timespec='seconds')
        result['gpu_seconds']=round(device.dev.gpu_ms/1000,3)
        write_status(path,result)
        print(result['positions'],flush=True)
        device.close()


if __name__=='__main__':
    main()
