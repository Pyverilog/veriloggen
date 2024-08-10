from __future__ import absolute_import
from __future__ import print_function

from . import stream

__intrinsics__ = {'copy': 'copy',
                  'copy_pattern': 'copy_pattern'}

copy_stream_cache = {}
copy_pattern_stream_cache = {}


def copy(fsm, src_ram, dst_ram, src_addr, dst_addr, size,
         src_stride=1, dst_stride=1,
         src_port=0, dst_port=0):

    name = '_'.join(['copy', src_ram.name, dst_ram.name])

    if name in copy_stream_cache:
        strm = copy_stream_cache[name]

    else:
        m = src_ram.m
        clk = src_ram.clk
        rst = src_ram.rst
        strm = stream.Stream(m, name, clk, rst)
        src = strm.source('src')
        dst = src
        strm.sink(dst, 'dst')
        copy_stream_cache[name] = strm

    strm.set_source(fsm, 'src', src_ram, src_addr, size,
                    stride=src_stride, port=src_port)
    strm.set_sink(fsm, 'dst', dst_ram, dst_addr, size,
                  stride=dst_stride, port=dst_port)
    strm.run(fsm)
    strm.join(fsm)


def copy_pattern(fsm, src_ram, dst_ram, src_addr, dst_addr,
                 src_pattern, dst_pattern,
                 src_port=0, dst_port=0):

    name = '_'.join(['copy', src_ram.name, dst_ram.name])

    if name in copy_pattern_stream_cache:
        strm = copy_pattern_stream_cache[name]

    else:
        m = src_ram.m
        clk = src_ram.clk
        rst = src_ram.rst
        strm = stream.Stream(m, name, clk, rst)
        src = strm.source('src')
        dst = src
        strm.sink(dst, 'dst')
        copy_pattern_stream_cache[name] = strm

    strm.set_source_pattern(fsm, 'src', src_ram, src_addr, src_pattern,
                            port=src_port)
    strm.set_sink_pattern(fsm, 'dst', dst_ram, dst_addr, dst_pattern,
                          port=dst_port)
    strm.run(fsm)
    strm.join(fsm)
