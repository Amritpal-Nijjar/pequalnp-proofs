"""Search all remaining binary AND/OR wirings for saved five-input prefixes."""
import argparse
from collections import defaultdict
import ctypes as ct
from datetime import datetime, timezone
import itertools
import json
import math
from pathlib import Path
import random
import statistics
import time

from opencl_replay import ReplayDevice


ROOT = Path(__file__).resolve().parent
TARGET = 4276677288
MASK = 2**32 - 1
INPUTS = [sum(((row >> i) & 1) << row for row in range(32)) for i in range(5)]
PAIRS = [(a, b) for b in range(20) for a in range(b+1)]
PAIR_BYTES = bytes(x for pair in PAIRS for x in pair)


def apply_gate(op, a, b=0):
    return a & b if op == 0 else a | b if op == 1 else MASK ^ a


def physical(gates):
    wires = INPUTS.copy()
    for op, idx in gates:
        wires.append(apply_gate(op, *(wires[x] for x in idx)))
    return wires


def decode(bank, early, index):
    wires = list(bank)
    gates = []
    for _ in range(early):
        n = len(wires)
        index, code = divmod(index, n * (n+1))
        a, b = PAIRS[code//2]
        gates.append((code%2, [a,b]))
        wires.append(apply_gate(code%2, wires[a], wires[b]))
    assert index == 0
    return wires, gates


def independent_finish(wires, target):
    # Return a witness using at most two gates. The last gate can read the
    # one new wire and an old one, or just old wires. A repeated pin adds no value.
    for k, a in enumerate(wires):
        if a == target:
            return [], k
    for b in range(len(wires)):
        for a in range(b+1):
            for op, v in enumerate((wires[a] & wires[b], wires[a] | wires[b])):
                first = (op, [a, b])
                if v == target:
                    return [first], len(wires)
                for k, w in enumerate(wires):
                    if (v & w) == target:
                        return [first, (0, [len(wires), k])], len(wires)+1
                    if (v | w) == target:
                        return [first, (1, [len(wires), k])], len(wires)+1
    return None


def control_index(gates, prefix):
    root = physical(gates[:prefix]); wires = sorted(set(root))
    index = 0; stride = 1
    for op, pair in gates[prefix:-2]:
        assert op in (0,1)
        a, b = sorted(wires.index(root[i]) for i in pair)
        index += stride * (b*(b+1) + 2*a + op)
        stride *= len(wires) * (len(wires)+1)
        value = apply_gate(op, wires[a], wires[b])
        root.append(value); wires.append(value)
    return index


def group_prefixes(layouts, prefix):
    groups = defaultdict(list)
    for key, row in layouts.items():
        gates = row['gates']
        assert len(gates) == 10 and sum(op == 2 for op, _ in gates[:prefix]) == 1
        assert all(op in (0,1) for op,_ in gates[prefix:])
        group = tuple(sorted(set(physical(gates[:prefix]))))
        actual = sum(v << i for i, v in enumerate(row['actual']))
        assert actual == TARGET ^ (1 << int(key)) and physical(gates)[-1] == actual
        groups[group].append((int(key), gates, actual))
    return groups


class NativeControl:
    def __init__(self):
        dll = ct.CDLL(str(ROOT/'cpu_library.dll'))
        self.replay = dll.replay_batch
        self.u32, self.byte = ct.c_uint32, ct.c_ubyte
        self.replay.argtypes = [ct.POINTER(self.u32), self.u32, ct.POINTER(self.byte), self.u32,
                                self.u32, self.u32, self.u32, ct.POINTER(self.byte)]
        self.replay.restype = None
        self.pairs = (self.byte * len(PAIR_BYTES)).from_buffer_copy(PAIR_BYTES)

    def run(self, bank, early, begin, count, target):
        inputs = (self.u32 * len(bank))(*bank)
        result = (self.byte * count)()
        self.replay(inputs, len(bank), self.pairs, early, begin, count, target, result)
        return bytes(result)


def audit(device, bank, controls, batch, cpu):
    early = 3
    device.set_bank(bank)
    size = math.prod(n*(n+1) for n in range(len(bank),len(bank)+early))
    rng = random.Random(18096)
    checks = positives = negatives = 0
    for _ in range(80):
        at = rng.randrange(size)
        wires, _ = decode(bank, early, at)
        a,b,c = rng.choices(wires,k=3)
        table = rng.choice([TARGET,controls[0][2],rng.getrandbits(32),(a & b)|c,(a | b)&c])
        expected = independent_finish(wires,table) is not None
        actual = device.run(early,at,1,table)[0]
        assert actual == expected, (at,table,expected,actual)
        checks += 1; positives += expected; negatives += not expected
    assert positives > 0 and negatives > 0
    timings = []
    for target in (TARGET, (bank[0] & bank[3]) | bank[5]):
        for _ in range(3):
            start = time.perf_counter(); ref = cpu.run(bank,early,139,batch,target); cpu_ms = (time.perf_counter()-start)*1000
            start = time.perf_counter(); got = device.run(early,139,batch,target); gpu_ms = (time.perf_counter()-start)*1000
            assert got == ref
            timings.append({'table':target,'states':batch,'cpu_ms':round(cpu_ms,3),
                            'gpu_batch_ms':round(gpu_ms,3),'hits':got.count(1)})
    primary = [t for t in timings if t['table'] == TARGET]
    return {'independent_truth_checks':checks,'positive':positives,'negative':negatives,
            'native_comparisons':timings,'cpu_target_median_ms':statistics.median(t['cpu_ms'] for t in primary),
            'gpu_target_median_ms':statistics.median(t['gpu_batch_ms'] for t in primary)}


def write_status(path, obj):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8')
    for attempt in range(12):
        try:
            temporary.replace(path)
            return
        except PermissionError:
            if attempt == 11:
                raise
            time.sleep(0.015 * (attempt + 1))


def materialize(prefix_gates, bank, early, hit):
    wires, early_gates = decode(bank,early,hit)
    tail, out = independent_finish(wires,TARGET)
    original = physical(prefix_gates)
    mapping = [original.index(v) for v in bank]
    gates = list(prefix_gates)
    for op, pins in early_gates + tail:
        gates.append((op,[mapping[i] for i in pins])); mapping.append(5+len(gates)-1)
    assert physical(gates)[mapping[out]] == TARGET
    return {'gates':gates,'output':mapping[out], 'checked_table':TARGET}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('near_rows',type=Path); parser.add_argument('status',type=Path)
    parser.add_argument('--deadline',required=True); parser.add_argument('--batch',type=int,default=65536)
    parser.add_argument('--suffixes',nargs='+',type=int,default=[5,6])
    args = parser.parse_args()
    deadline = datetime.fromisoformat(args.deadline.replace('Z','+00:00')).timestamp()
    layouts = json.loads(args.near_rows.read_text(encoding='utf-8-sig'))
    started = time.perf_counter(); device = ReplayDevice(args.batch)
    first_bank, first_controls = next(iter(group_prefixes(layouts,5).items()))
    report = {'device':device.name, 'target':TARGET, 'groups':[], 'found':[], 'complete':False}
    try:
        report['audit'] = audit(device, first_bank, first_controls, min(args.batch,65536), NativeControl())
        write_status(args.status, report)
        print('Controls passed on',device.name,report['audit']['cpu_target_median_ms'],report['audit']['gpu_target_median_ms'],flush=True)
        for suffix in args.suffixes:
            if suffix not in (4,5,6): raise ValueError('This index layout handles four to six replacement gates')
            prefix = 10 - suffix; early = suffix - 2
            for bank, items in group_prefixes(layouts,prefix).items():
                device.set_bank(bank)
                group = {'suffix_gates':suffix,'rows':[k for k,_,_ in items], 'bank':list(bank),
                         'tested':0,'total':math.prod(n*(n+1) for n in range(len(bank),len(bank)+early)),
                         'target_hits':0,'positive_controls':[]}
                assert group['total'] <= 2**32
                report['groups'].append(group)
                for key,gates,table in items:
                    ix = control_index(gates,prefix)
                    assert device.run(early,ix,1,table) == b'\x01'
                    assert independent_finish(decode(bank,early,ix)[0],table) is not None
                    group['positive_controls'].append(key)
                began = time.perf_counter(); last_save = began
                while group['tested'] < group['total']:
                    if time.time() > deadline-2:
                        report['stopped_at_cap'] = True
                        return
                    at = group['tested']; count = min(args.batch,group['total']-at)
                    flags = device.run(early,at,count,TARGET)
                    hits = flags.count(1)
                    if hits and not report['found']:
                        ix = at+flags.index(1)
                        report['found'].append({'row':items[0][0],'index':ix,**materialize(items[0][1][:prefix],bank,early,ix)})
                        print('TARGET CANDIDATE',json.dumps(report['found'][0]),flush=True)
                    group['target_hits'] += hits; group['tested'] += count
                    now = time.perf_counter()
                    if now - last_save >= 2 or hits:
                        group['wall_s'] = round(now-began,3); write_status(args.status,report); last_save = now
                group['wall_s'] = round(time.perf_counter()-began,3)
                print('completed',suffix,group['rows'],group['tested'],'states,',group['target_hits'],'hits,',group['wall_s'],'s',flush=True)
                write_status(args.status,report)
        report['complete'] = True
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat(timespec='seconds')
        report['elapsed_s'] = round(time.perf_counter()-started,3); report['gpu_kernel_s'] = round(device.gpu_ms/1000,3)
        write_status(args.status,report); device.close()


if __name__ == '__main__':
    main()
