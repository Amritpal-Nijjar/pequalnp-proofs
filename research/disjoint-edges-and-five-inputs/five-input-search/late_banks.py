"""Batch distinct sixth-gate NOT prefixes in reverse order on the GPU."""
from array import array
import argparse
import ctypes as ct
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time

from opencl_replay import ReplayDevice, checked, i32, ptr, ref, u32
from run_live import independent_witness, prefix_debt
from run_search import TARGET, physical, write_status
from wide_positions import pack_prefix, planted, unpack_prefix


class Batch:
    def __init__(self):
        self.dev = ReplayDevice(64)
        d, err = self.dev, i32()
        self.kernel = ptr(d.cl.clCreateKernel(d.program, b'late_banks', ref(err)))
        checked(err.value, 'create late kernel')
        self.bank = ptr(d.cl.clCreateBuffer(d.context, 4, 512*12*4, None, ref(err)))
        checked(err.value, 'allocate packed banks')

    def evaluate(self, prefixes, target):
        data = array('I')
        for gates in prefixes:
            data.extend(physical(gates))
            data.append(prefix_debt(gates))
        assert data.itemsize == 4 and 0 < len(prefixes) <= 512
        assert len(data) == 12*len(prefixes)
        buf = (u32*len(data)).from_buffer(data)
        dev = self.dev
        checked(dev.cl.clEnqueueWriteBuffer(dev.queue,self.bank,1,0,ct.sizeof(buf),buf,0,None,None), 'transfer banks')
        result = (u32*2)(0,0xffffffff)
        checked(dev.cl.clEnqueueWriteBuffer(dev.queue,dev.summary,1,0,8,result,0,None,None), 'reset')
        count = len(prefixes)*20592
        dev.execute(self.kernel,[self.bank,dev.pairs,u32(count),u32(target),dev.summary],count,dev.summary,result)
        return result[0],result[1]

    def close(self):
        self.dev.cl.clReleaseMemObject(self.bank)
        self.dev.cl.clReleaseKernel(self.kernel)
        self.dev.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('folder', type=Path)
    parser.add_argument('--deadline', required=True)
    parser.add_argument('--front', type=Path, help='optional increasing-order search checkpoint')
    opt = parser.parse_args()
    end = datetime.fromisoformat(opt.deadline.replace('Z','+00:00')).timestamp()
    root = opt.folder
    code = (root/'slot5_prefixes.bin').read_bytes()
    meta = json.loads((root/'slot5_prefixes.json').read_text())
    assert len(code) == meta['states']*18 and hashlib.sha256(code).hexdigest() == meta['sha256']
    out = root/'slot_5_reverse.json'
    top = meta['states']
    report = {'not_slot_zero_based':5,'total_prefixes':top,'sha256':meta['sha256'],'suffix_lower':top,
              'prefix_boundary':0,'witnesses':[],'complete':False}
    worker = Batch()
    try:
        example = planted(5)
        table = physical(example)[-1]
        controls = [unpack_prefix(code[:18]),example[:6],unpack_prefix(code[-18:])]
        assert pack_prefix(controls[0]) == code[:18]
        for goal in (table,TARGET):
            parts = []
            for prefix in controls:
                worker.dev.set_bank(physical(prefix))
                parts.append(worker.dev.count_live(2,0,0,2,prefix_debt(prefix),20592,goal))
            count, index = worker.evaluate(controls,goal)
            assert sum(h for h,_ in parts) == count
            assert index == next((i*20592+v for i,(h,v) in enumerate(parts) if h),0xffffffff)
            if goal == table: assert parts[1][0] > 0
        report['positive_control'] = table
        last = 0
        while time.time() < end-2:
            front = 0
            if opt.front and opt.front.is_file():
                front = json.loads(opt.front.read_text())['prefixes_completed']
            report['prefix_boundary'] = front
            if top <= front:
                report['complete'] = True
                break
            start = max(front,top-512)
            prefixes = [unpack_prefix(code[i*18:(i+1)*18]) for i in range(start,top)]
            count, index = worker.evaluate(prefixes,TARGET)
            if count:
                i, suffix = divmod(index,20592)
                witness = independent_witness(prefixes[i],2,suffix,TARGET)
                assert witness is not None
                report['witnesses'].append({'gates':witness,'index':start+i,'output':14})
                break
            top = start
            report['suffix_lower'] = top
            if time.monotonic()-last > 2:
                write_status(out,report)
                last = time.monotonic()
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat(timespec='seconds')
        write_status(out,report)
        worker.close()
        print(report,flush=True)


if __name__ == '__main__':
    main()
