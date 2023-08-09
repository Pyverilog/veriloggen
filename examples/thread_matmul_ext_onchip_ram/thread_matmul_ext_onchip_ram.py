from __future__ import absolute_import
from __future__ import print_function
import sys
import os
import numpy as np
import math

# the next line can be removed after installation
sys.path.insert(0, os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))))

from veriloggen import *
import veriloggen.thread as vthread
import veriloggen.types.axi as axi

mem_datawidth = 8
datawidth = 16
addrwidth = 8

matrix_size = 10

num_pack = math.ceil(datawidth / mem_datawidth)
addr_pack = math.ceil((addrwidth + math.ceil(np.log2(datawidth / mem_datawidth)))
                       / mem_datawidth)

matrix_size_addr = 0
a_offset_addr = 4
b_offset_addr = 8
c_offset_addr = 12
a_offset = 16
b_offset = a_offset + matrix_size * matrix_size * num_pack
c_offset = b_offset + matrix_size * matrix_size * num_pack


def mkLed():
    m = Module('user_module')
    clk = m.Input('clk')
    rst = m.Input('rst')
    start = m.Input('start')
    busy = m.OutputReg('busy', initval=0)

    ram = vthread.ExtRAM(m, 'ram', clk, rst, mem_datawidth, 
                         addrwidth + math.ceil(np.log2(datawidth / mem_datawidth)))

    def matmul():
        while True:
            wait()
            matrix_size = read_matrix_size()
            offset_a = read_matrix_a_offset()
            offset_b = read_matrix_b_offset()
            offset_c = read_matrix_c_offset()
            comp(matrix_size, offset_a, offset_b, offset_c)
            done()

    def wait():
        while not start:
            pass
        busy.value = 1

    def read_matrix_size():
        size = 0
        for i in range(addr_pack):
            size |= ((ram.read(matrix_size_addr + i) & ((1 << mem_datawidth) - 1))
                     << (mem_datawidth * i))
        return size

    def read_matrix_a_offset():
        offset = 0
        for i in range(addr_pack):
            offset |= ((ram.read(a_offset_addr + i) & ((1 << mem_datawidth) - 1))
                       << (mem_datawidth * i))
        return offset

    def read_matrix_b_offset():
        offset = 0
        for i in range(addr_pack):
            offset |= ((ram.read(b_offset_addr + i) & ((1 << mem_datawidth) - 1))
                       << (mem_datawidth * i))
        return offset

    def read_matrix_c_offset():
        offset = 0
        for i in range(addr_pack):
            offset |= ((ram.read(c_offset_addr + i) & ((1 << mem_datawidth) - 1))
                       << (mem_datawidth * i))
        return offset

    def comp(matrix_size, a_offset, b_offset, c_offset):
        a_addr, c_addr = a_offset, c_offset

        for i in range(matrix_size):
            b_addr = b_offset
            for j in range(matrix_size):
                sum = 0
                for k in range(matrix_size):
                    x = int(0, base=2)
                    y = 0
                    for l in range(num_pack):
                        x |= ((ram.read(a_addr + k * num_pack + l) 
                               & ((1 << mem_datawidth) - 1))
                              << (mem_datawidth * l))
                        y |= ((ram.read(b_addr + k * num_pack + l) 
                               & ((1 << mem_datawidth) - 1)) 
                              << (mem_datawidth * l))
                    sum += x * y
                for l in range(num_pack):
                    ram.write(c_addr + j * num_pack + l,
                              (sum >> (mem_datawidth * l)) & (1<<mem_datawidth)-1)

                b_addr += matrix_size * num_pack

            a_addr += matrix_size * num_pack
            c_addr += matrix_size * num_pack

    def done():
        busy.value = 0

    th = vthread.Thread(m, 'th_matmul', clk, rst, matmul, datawidth=16)
    fsm = th.start()

    return m


def mkTest(memimg_name=None):

    a_shape = (matrix_size, matrix_size)
    b_shape = (matrix_size, matrix_size)
    c_shape = (a_shape[0], b_shape[0])

    n_raw_a = axi.shape_to_length(a_shape)
    n_raw_b = axi.shape_to_length(b_shape)

    n_a = axi.shape_to_memory_size(a_shape, datawidth)
    n_b = axi.shape_to_memory_size(b_shape, datawidth)

    a = np.zeros(a_shape, dtype=np.int64)
    b = np.zeros(b_shape, dtype=np.int64)

    value = 1
    for y in range(a_shape[0]):
        for x in range(a_shape[1]):
            if x == y:
                a[y][x] = value
                value += 1
            else:
                a[y][x] = 0

    for y in range(b_shape[0]):
        for x in range(b_shape[1]):
            if x == y:
                b[y][x] = 2
            else:
                b[y][x] = 0

    a_addr = a_offset
    b_addr = b_offset

    mem = np.zeros([(2 ** addrwidth) * num_pack], dtype=np.int64)
    axi.set_memory(mem, a, mem_datawidth, datawidth, a_addr)
    axi.set_memory(mem, b, mem_datawidth, datawidth, b_addr)

    led = mkLed()

    m = Module('test')
    params = m.copy_params(led)
    ports = m.copy_sim_ports(led)
    clk = ports['clk']
    rst = ports['rst']

    start = ports['start']
    busy = ports['busy']

    start.initval = 0

    memory = vthread.RAM(m, 'memory', clk, rst, mem_datawidth, 
                         addrwidth + math.ceil(np.log2(datawidth / mem_datawidth)),
                         numports=2, initvals=mem.tolist())
    memory.connect_rtl(0, ports['ram_0_addr'], ports['ram_0_wdata'],
                       ports['ram_0_wenable'], ports['ram_0_rdata'],
                       ports['ram_0_enable'])

    # Timer
    counter = m.Reg('counter', 32, initval=0)
    seq = Seq(m, 'seq', clk, rst)
    seq(
        counter.inc()
    )

    def ctrl():
        for i in range(100):
            pass

        for i in range(addr_pack):
            awaddr = matrix_size_addr + i
            v = (matrix_size >> (mem_datawidth * i)) & ((1 << mem_datawidth) - 1)
            print('# matrix_size[%d:%d] = %d' % 
                  (mem_datawidth * (i+1) - 1, mem_datawidth * i, v))
            memory.write(awaddr, v, port=1)

        for i in range(addr_pack):
            awaddr = a_offset_addr + i
            v = (a_offset >> (mem_datawidth * i)) & ((1 << mem_datawidth) - 1)
            print('# a_offset[%d:%d] = %d' % 
                  (mem_datawidth * (i+1) - 1, mem_datawidth * i, v))
            memory.write(awaddr, v, port=1)

        for i in range(addr_pack):
            awaddr = b_offset_addr + i
            v = (b_offset >> (mem_datawidth * i)) & ((1 << mem_datawidth) - 1)
            print('# b_offset[%d:%d] = %d' % 
                  (mem_datawidth * (i+1) - 1, mem_datawidth * i, v))
            memory.write(awaddr, v, port=1)

        for i in range(addr_pack):
            awaddr = c_offset_addr + i
            v = (c_offset >> (mem_datawidth * i)) & ((1 << mem_datawidth) - 1)
            print('# c_offset[%d:%d] = %d' % 
                  (mem_datawidth * (i+1) - 1, mem_datawidth * i, v))
            memory.write(awaddr, v, port=1)

        start_time = counter
        print('# start time = %d' % start_time)
        start.value = 1

        for _ in range(10):
            pass

        start.value = 0

        while True:
            if not busy:
                break

        end_time = counter
        print('# end time = %d' % end_time)
        time = end_time - start_time
        print('# exec time = %d' % time)

        all_ok = True
        for y in range(matrix_size):
            for x in range(matrix_size):
                v = 0
                v_addr = c_offset + (y * matrix_size + x) * num_pack
                for l in range(num_pack):
                    v |= memory.read(v_addr + l, port=1) << (mem_datawidth * l)
                    v |= ((memory.read(v_addr + l, port=1) 
                           & ((1 << mem_datawidth) - 1))
                          << (mem_datawidth * l))
                if y == x and vthread.verilog.NotEql(v, (y + 1) * 2):
                    all_ok = False
                    print("NG [%d,%d] = %d (expected: %d)" % (y, x, v, (y + 1) * 2))
                if y != x and vthread.verilog.NotEql(v, 0):
                    all_ok = False
                    print("NG [%d,%d] = %d (expected: %d)" % (y, x, v, 0))

        if all_ok:
            print('# verify: PASSED')
        else:
            print('# verify: FAILED')

        vthread.finish()

    th = vthread.Thread(m, 'th_ctrl', clk, rst, ctrl)
    fsm = th.start()

    uut = m.Instance(led, 'uut',
                     params=m.connect_params(led),
                     ports=m.connect_ports(led))

    # vcd_name = os.path.splitext(os.path.basename(__file__))[0] + '.vcd'
    # simulation.setup_waveform(m, uut, dumpfile=vcd_name)
    simulation.setup_clock(m, clk, hperiod=5)
    init = simulation.setup_reset(m, rst, m.make_reset(), period=100)

    init.add(
        Delay(1000000),
        Systask('finish'),
    )

    # return m

    # for VCD dump
    top = Module('top')
    uut = Submodule(top, m, name='test')

    vcd_name = os.path.splitext(os.path.basename(__file__))[0] + '.vcd'
    simulation.setup_waveform(top, uut, dumpfile=vcd_name)

    return top


def run(filename='tmp.v', simtype='iverilog', outputfile=None):

    if outputfile is None:
        outputfile = os.path.splitext(os.path.basename(__file__))[0] + '.out'

    memimg_name = 'memimg_' + outputfile

    test = mkTest(memimg_name=memimg_name)

    if filename is not None:
        test.to_verilog(filename)

    sim = simulation.Simulator(test, sim=simtype)
    rslt = sim.run(outputfile=outputfile)

    return rslt


if __name__ == '__main__':
    rslt = run(filename='tmp.v')
    print(rslt)
