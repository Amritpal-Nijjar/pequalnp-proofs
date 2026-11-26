"""Small OpenCL 1.2 driver for the grid of independent Boolean circuit suffixes."""
import ctypes as ct
from pathlib import Path


ptr, u32, i32, u64, size = ct.c_void_p, ct.c_uint32, ct.c_int32, ct.c_uint64, ct.c_size_t
ref = ct.byref
P = ct.POINTER


def checked(code, operation):
    if code != 0:
        raise RuntimeError(f'{operation} returned OpenCL status {code}')


class ReplayDevice:
    def __init__(self, capacity):
        cl = ct.WinDLL('OpenCL.dll')
        self.cl = cl
        definitions = {
            'clGetPlatformIDs': (i32, [u32, P(ptr), P(u32)]),
            'clGetDeviceIDs': (i32, [ptr, u64, u32, P(ptr), P(u32)]),
            'clGetDeviceInfo': (i32, [ptr, u32, size, ptr, P(size)]),
            'clCreateContext': (ptr, [ptr, u32, P(ptr), ptr, ptr, P(i32)]),
            'clCreateCommandQueue': (ptr, [ptr, ptr, u64, P(i32)]),
            'clCreateProgramWithSource': (ptr, [ptr, u32, P(ct.c_char_p), P(size), P(i32)]),
            'clBuildProgram': (i32, [ptr, u32, P(ptr), ct.c_char_p, ptr, ptr]),
            'clGetProgramBuildInfo': (i32, [ptr, ptr, u32, size, ptr, P(size)]),
            'clCreateKernel': (ptr, [ptr, ct.c_char_p, P(i32)]),
            'clCreateBuffer': (ptr, [ptr, u64, size, ptr, P(i32)]),
            'clEnqueueWriteBuffer': (i32, [ptr, ptr, u32, size, size, ptr, u32, ptr, ptr]),
            'clSetKernelArg': (i32, [ptr, u32, size, ptr]),
            'clEnqueueNDRangeKernel': (i32, [ptr, ptr, u32, P(size), P(size), P(size), u32, ptr, P(ptr)]),
            'clEnqueueReadBuffer': (i32, [ptr, ptr, u32, size, size, ptr, u32, ptr, ptr]),
            'clGetEventProfilingInfo': (i32, [ptr, u32, size, ptr, P(size)]),
        }
        for typ in ['Event', 'MemObject', 'Kernel', 'Program', 'CommandQueue', 'Context']:
            definitions['clRelease' + typ] = (i32, [ptr])
        for name, (out, args) in definitions.items():
            function = getattr(cl, name)
            function.restype, function.argtypes = out, args

        count = u32()
        checked(cl.clGetPlatformIDs(0, None, ref(count)), 'count platforms')
        platforms = (ptr * count.value)()
        checked(cl.clGetPlatformIDs(count, platforms, None), 'read platforms')
        self.device = ptr()
        for platform in platforms:
            if cl.clGetDeviceIDs(platform, 4, 1, ref(self.device), None) == 0:
                break
        if not self.device:
            raise RuntimeError('The system OpenCL driver exposes no GPU')
        name = ct.create_string_buffer(512)
        checked(cl.clGetDeviceInfo(self.device, 0x102B, len(name), name, None), 'device name')
        self.name = name.value.decode()
        code = i32()
        self.context = ptr(cl.clCreateContext(None, 1, ref(self.device), None, None, ref(code)))
        checked(code.value, 'context')
        self.queue = ptr(cl.clCreateCommandQueue(self.context, self.device, 2, ref(code)))
        checked(code.value, 'profiling queue')
        source = ct.c_char_p(Path(__file__).with_name('suffix.cl').read_bytes())
        self.program = ptr(cl.clCreateProgramWithSource(self.context, 1, ref(source), None, ref(code)))
        checked(code.value, 'program')
        result = cl.clBuildProgram(self.program, 1, ref(self.device), b'-cl-std=CL1.2', None, None)
        if result:
            log = ct.create_string_buffer(16384)
            cl.clGetProgramBuildInfo(self.program, self.device, 0x1183, len(log), log, None)
            raise RuntimeError(log.value.decode(errors='replace'))
        self.kernel = ptr(cl.clCreateKernel(self.program, b'replay', ref(code)))
        checked(code.value, 'kernel')
        self.live_kernel = ptr(cl.clCreateKernel(self.program, b'replay_live', ref(code)))
        checked(code.value, 'liveness kernel')
        self.count_kernel = ptr(cl.clCreateKernel(self.program, b'count_live', ref(code)))
        checked(code.value, 'counting kernel')
        pairs = bytes(x for b in range(20) for a in range(b+1) for x in (a, b))
        pair_data = ct.create_string_buffer(pairs)
        self.pairs = ptr(cl.clCreateBuffer(self.context, 4 | 32, len(pairs), pair_data, ref(code)))
        checked(code.value, 'pair buffer')
        self.bank = ptr(cl.clCreateBuffer(self.context, 4, 4*20, None, ref(code)))
        checked(code.value, 'bank buffer')
        self.out = ptr(cl.clCreateBuffer(self.context, 2, capacity, None, ref(code)))
        checked(code.value, 'result buffer')
        self.summary = ptr(cl.clCreateBuffer(self.context, 1, 8, None, ref(code)))
        checked(code.value, 'count buffer')
        self.capacity = capacity
        self.n = 0
        self.gpu_ms = 0.0

    def set_bank(self, bank):
        self.n = len(bank)
        wires = (u32 * self.n)(*bank)
        checked(self.cl.clEnqueueWriteBuffer(self.queue, self.bank, 1, 0, ct.sizeof(wires), wires, 0, None, None), 'upload bank')

    def run(self, early, begin, count, target):
        if not (self.n and 0 < count <= self.capacity and self.n + early < 20 and begin+count <= 2**32):
            raise ValueError('Batch bounds exceed the tested kernel representation')
        values = [self.bank, u32(self.n), self.pairs, u32(early), u32(begin), u32(count), u32(target), self.out]
        return self.dispatch(self.kernel,values,count)

    def run_live(self, early, begin, upper, split, unpaid, count, target):
        if not (0 < count <= self.capacity and 0 <= begin <= 2**32-count and upper < 2**32 and self.n+early < 20):
            raise ValueError('Invalid liveness batch')
        values = [self.bank, u32(self.n), self.pairs, u32(early), u32(begin), u32(upper), u32(split),
                  u32(unpaid), u32(count), u32(target), self.out]
        return self.dispatch(self.live_kernel,values,count)

    def dispatch(self, kernel, values, count):
        result = (ct.c_ubyte * count)()
        self.execute(kernel,values,count,self.out,result)
        return bytes(result)

    def count_live(self, early, begin, upper, split, unpaid, count, target):
        if not(0<count<=2**28 and begin+count<=2**32 and self.n+early<20):
            raise ValueError('Invalid count batch')
        result = (u32*2)(0,0xffffffff)
        checked(self.cl.clEnqueueWriteBuffer(self.queue,self.summary,1,0,8,result,0,None,None),'reset counts')
        args=[self.bank,u32(self.n),self.pairs,u32(early),u32(begin),u32(upper),u32(split),
              u32(unpaid),u32(count),u32(target),self.summary]
        self.execute(self.count_kernel,args,count,self.summary,result)
        return result[0],result[1]

    def execute(self, kernel, values, count, output, result):
        for i, value in enumerate(values):
            checked(self.cl.clSetKernelArg(kernel, i, ct.sizeof(value), ref(value)), 'set argument')
        threads = size(((count+63)//64)*64)
        event = ptr()
        checked(self.cl.clEnqueueNDRangeKernel(self.queue, kernel, 1, None, ref(threads), None, 0, None, ref(event)), 'launch')
        checked(self.cl.clEnqueueReadBuffer(self.queue, output, 1, 0, ct.sizeof(result), result, 0, None, None), 'read flags')
        start, end = u64(), u64()
        checked(self.cl.clGetEventProfilingInfo(event, 0x1282, 8, ref(start), None), 'profile start')
        checked(self.cl.clGetEventProfilingInfo(event, 0x1283, 8, ref(end), None), 'profile end')
        self.gpu_ms += (end.value - start.value) / 1e6
        checked(self.cl.clReleaseEvent(event), 'release event')

    def close(self):
        self.cl.clReleaseKernel(self.count_kernel)
        self.cl.clReleaseKernel(self.live_kernel)
        for item in (self.summary, self.out, self.pairs, self.bank):
            self.cl.clReleaseMemObject(item)
        for name in ('kernel','program','queue','context'):
            command = {'kernel':'Kernel','program':'Program','queue':'CommandQueue','context':'Context'}[name]
            getattr(self.cl, 'clRelease' + command)(getattr(self, name))
