from __future__ import absolute_import
from __future__ import print_function

import math
import functools
import ast
import inspect
import textwrap
from collections import OrderedDict

import veriloggen.core.vtypes as vtypes
import veriloggen.types.fixed as fxd
import veriloggen.types.util as util
from veriloggen.seq.seq import make_condition
from veriloggen.fsm.fsm import FSM
from veriloggen.seq.seq import Seq
from veriloggen.stream.stream import Stream as BaseStream
from veriloggen.stream.stypes import Substream as BaseSubstream
from veriloggen.stream.stypes import SubstreamMultiCycle as BaseSubstreamMultiCycle
from veriloggen.stream.stypes import _and_vars

from . import compiler
from . import thread

mode_width = 5
mode_idle = vtypes.Int(0, mode_width, base=2)
mode_ram_normal = vtypes.Int(1 << 0, mode_width, base=2)
mode_ram_pattern = vtypes.Int(1 << 1, mode_width, base=2)
mode_ram_multipattern = vtypes.Int(1 << 2, mode_width, base=2)
mode_ram_generator = vtypes.Int(1 << 3, mode_width, base=2)
mode_fifo = vtypes.Int(1 << 4, mode_width, base=2)

generator_id_width = 16

reduce_reset_name = '_reduce_reset'
terminate_prefix = '_terminate_%d'


def TmpStream(m, clk, rst,
              datawidth=32, addrwidth=32,
              max_pattern_length=4, ram_sel_width=8,
              fsm_as_module=False):
    name = compiler._tmp_name('_tmp_stream')
    return Stream(m, name, clk, rst,
                  datawidth, addrwidth,
                  max_pattern_length, ram_sel_width,
                  fsm_as_module=False)


class Stream(BaseStream):
    __intrinsics__ = {'set_source': 'set_source',
                      'set_source_pattern': 'set_source_pattern',
                      'set_source_multidim': 'set_source_multidim',
                      'set_source_multipattern': 'set_source_multipattern',
                      'set_source_generator': 'set_source_generator',
                      'set_source_fifo': 'set_source_fifo',
                      'set_source_empty': 'set_source_empty',
                      'set_sink': 'set_sink',
                      'set_sink_pattern': 'set_sink_pattern',
                      'set_sink_multidim': 'set_sink_multidim',
                      'set_sink_multipattern': 'set_sink_multipattern',
                      'set_sink_generator': 'set_sink_generator',
                      'set_sink_fifo': 'set_sink_fifo',
                      'set_sink_immediate': 'set_sink_immediate',
                      'set_sink_empty': 'set_sink_empty',
                      'set_parameter': 'set_parameter',
                      'set_read_RAM': 'set_read_RAM',
                      'set_write_RAM': 'set_write_RAM',
                      'set_read_modify_write_RAM': 'set_read_modify_write_RAM',
                      'set_read_fifo': 'set_read_fifo',
                      'set_write_fifo': 'set_write_fifo',
                      'read_sink': 'read_sink',
                      'run': 'run',
                      'join': 'join',
                      'done': 'done',
                      'source_join': 'source_join',
                      'source_done': 'source_done',
                      'sink_join': 'sink_join',
                      'sink_done': 'sink_done',
                      'source_join_and_run': 'source_join_and_run',
                      'enable_dump': 'enable_dump',
                      'disable_dump': 'disable_dump'}

    ram_delay = 0

    def __init__(self, m, name, clk, rst,
                 infinite=False,
                 datawidth=32, addrwidth=32,
                 max_pattern_length=4, max_multipattern_length=2,
                 ram_sel_width=8, fsm_as_module=False,
                 dump=False, dump_base=10, dump_mode='all'):

        # pipeline control
        ivalid = m.Reg('_'.join(['', name, 'stream_ivalid']), initval=0)

        oready = m.Wire('_'.join(['', name, 'stream_oready']))
        self.internal_oready = m.Wire('_'.join(['', name, 'stream_internal_oready']))
        self.internal_oready.assign(1)
        oready.assign(self.internal_oready)

        BaseStream.__init__(self, module=m, clock=clk, reset=rst,
                            ivalid=ivalid,
                            oready=oready,
                            no_hook=True,
                            dump=dump, dump_base=dump_base, dump_mode=dump_mode)

        self.name = name
        self.datawidth = datawidth
        self.addrwidth = addrwidth

        self.infinite = infinite

        self.max_pattern_length = max_pattern_length
        self.max_multipattern_length = max_multipattern_length
        self.ram_sel_width = ram_sel_width
        self.fsm_as_module = fsm_as_module

        self.stream_synthesized = False
        self.fsm_synthesized = False

        self.fsm = FSM(self.module, '_%s_fsm' %
                       self.name, self.clock, self.reset,
                       as_module=self.fsm_as_module)

        self.run_flag = self.module.Wire(
            '_'.join(['', self.name, 'run_flag']))
        self.run_flag.assign(0)

        self.source_start = self.module.Reg(
            '_'.join(['', self.name, 'source_start']), initval=0)
        self.source_stop = self.module.Wire(
            '_'.join(['', self.name, 'source_stop']))
        self.source_busy = self.module.Reg(
            '_'.join(['', self.name, 'source_busy']), initval=0)

        self.sink_start = self.module.Wire(
            '_'.join(['', self.name, 'sink_start']))
        self.sink_stop = self.module.Wire(
            '_'.join(['', self.name, 'sink_stop']))
        self.sink_busy = self.module.Wire(
            '_'.join(['', self.name, 'sink_busy']))

        self.busy = self.module.Wire(
            '_'.join(['', self.name, 'busy']))
        self.busy_reg = self.module.Reg(
            '_'.join(['', self.name, 'busy_reg']), initval=0)

        self.is_root = self.module.Wire('_'.join(['', self.name, 'is_root']))
        self.is_root.assign(1)

        self.sources = OrderedDict()
        self.sinks = OrderedDict()
        self.parameters = OrderedDict()
        self.substreams = []
        self.read_rams = OrderedDict()
        self.write_rams = OrderedDict()
        self.read_modify_write_rams = OrderedDict()
        self.read_fifos = OrderedDict()
        self.write_fifos = OrderedDict()

        self.var_name_map = OrderedDict()
        self.var_id_map = OrderedDict()
        self.var_id_name_map = OrderedDict()
        self.var_name_id_map = OrderedDict()
        self.var_id_count = 0

        self.source_idle_map = OrderedDict()
        self.sink_when_map = OrderedDict()

        self.reduce_reset = None
        self.terminates = []

        self.buf_id_count = 1  # '0' is reserved for idle
        self.buf_id_map = OrderedDict()  # key: buf._id(), value: count

        self.fsm_id_count = 0

    def source(self, name=None, datawidth=None, point=0, signed=True, no_ctrl=False):
        if self.stream_synthesized:
            raise ValueError(
                'cannot modify the stream because already synthesized')

        _id = self.var_id_count
        if name is None:
            name = 'source_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        prefix = self._prefix(name)

        self.var_id_count += 1

        if datawidth is None:
            datawidth = self.datawidth

        var = self.Variable(self._dataname(name), datawidth, point, signed)

        if no_ctrl:
            return var

        self.sources[name] = var
        self.var_id_map[_id] = var
        self.var_name_map[name] = var
        self.var_id_name_map[_id] = name
        self.var_name_id_map[name] = _id

        var.source_fsm = None
        var.source_pat_fsm = None
        var.source_multipat_fsm = None
        var.source_generator_fsms = []

        var.source_idle = self.module.Reg('_%s_idle' % prefix, initval=1)
        self.source_idle_map[name] = var.source_idle

        var.source_count = self.module.Reg('_%s_source_count' % prefix,
                                           self.addrwidth + 1, initval=0)

        # 5'b00000: set_source_empty, 5'b00001: set_source,
        # 5'b00010: set_source_pattern, 5'b00100: set_source_multipattern,
        # 5'b01000: set_source_generator,
        # 5'b10000: set_source_fifo
        var.source_mode = self.module.Reg('_%s_source_mode' % prefix, mode_width,
                                          initval=mode_idle)

        var.source_generator_id = self.module.Reg('_%s_source_generator_id' % prefix, generator_id_width,
                                                  initval=0)

        # set_source
        var.source_offset = self.module.Reg('_%s_source_offset' % prefix,
                                            self.addrwidth, initval=0)
        var.source_size = self.module.Reg('_%s_source_size' % prefix,
                                          self.addrwidth + 1, initval=0)
        var.source_stride = self.module.Reg('_%s_source_stride' % prefix,
                                            self.addrwidth, initval=0)

        var.source_offset_buf = self.module.Reg('_%s_source_offset_buf' % prefix,
                                                self.addrwidth, initval=0)
        var.source_size_buf = self.module.Reg('_%s_source_size_buf' % prefix,
                                              self.addrwidth + 1, initval=0)
        var.source_stride_buf = self.module.Reg('_%s_source_stride_buf' % prefix,
                                                self.addrwidth, initval=0)

        # set_source_pattern
        var.source_pat_cur_offsets = None
        var.source_pat_sizes = None
        var.source_pat_strides = None
        var.source_pat_counts = None

        var.source_pat_size_bufs = None
        var.source_pat_stride_bufs = None

        # set_source_multipattern
        var.source_multipat_num_patterns = None
        var.source_multipat_offsets = None
        var.source_multipat_cur_offsets = None
        var.source_multipat_sizes = None
        var.source_multipat_strides = None

        var.source_multipat_offset_bufs = None
        var.source_multipat_size_bufs = None
        var.source_multipat_stride_bufs = None

        # RAM, FIFO
        var.source_id_map = OrderedDict()
        var.source_sel = self.module.Reg('_%s_source_sel' % prefix,
                                         self.ram_sel_width, initval=0)

        # RAM
        var.source_ram_raddr = self.module.Reg('_%s_source_ram_raddr' % prefix,
                                               self.addrwidth, initval=0)
        var.source_ram_renable = self.module.Reg('_%s_source_ram_renable' % prefix,
                                                 initval=0)
        var.source_ram_rdata = self.module.Wire('_%s_source_ram_rdata' % prefix,
                                                datawidth)

        # FIFO
        var.source_fifo_deq = self.module.Reg('_%s_source_fifo_deq' % prefix,
                                              initval=0)
        var.source_fifo_rdata = self.module.Wire('_%s_source_fifo_rdata' % prefix,
                                                 datawidth)

        # empty
        var.has_source_empty = False
        var.source_empty_data = self.module.Reg('_%s_source_empty_data' % prefix,
                                                datawidth, initval=0)

        # default value
        self.seq.If(self.oready)(
            var.source_ram_renable(0),
            var.source_fifo_deq(0)
        )

        self.seq(
            var.source_idle(var.source_idle)
        )

        return var

    def sink(self, data, name=None, when=None, when_name=None):
        if self.stream_synthesized:
            raise ValueError(
                'cannot modify the stream because already synthesized')

        _id = self.var_id_count
        if name is None:
            name = 'sink_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        elif data.output_data is not None:
            # implicit Alias
            alias = self.Alias(data)
            return self.sink(alias, name, when, when_name)

        else:
            data.output(self._dataname(name))

        prefix = self._prefix(name)

        self.var_id_count += 1

        self.sinks[name] = data
        self.var_id_map[_id] = data
        self.var_name_map[name] = data
        self.var_id_name_map[_id] = name
        self.var_name_id_map[name] = _id

        data.sink_fsm = None
        data.sink_pat_fsm = None
        data.sink_multipat_fsm = None
        data.sink_generator_fsms = []

        data.sink_count = self.module.Reg('_%s_sink_count' % prefix,
                                          self.addrwidth + 1, initval=0)

        # 5'b00000: set_sink_empty, 5'b00001: set_sink,
        # 5'b00010: set_sink_pattern, 5'b00100: set_sink_multipattern,
        # 5'b01000: set_sink_generator,
        # 5'b10000: set_sink_fifo
        data.sink_mode = self.module.Reg('_%s_sink_mode' % prefix, mode_width,
                                         initval=mode_idle)

        data.sink_generator_id = self.module.Reg('_%s_sink_generator_id' % prefix, generator_id_width,
                                                 initval=0)

        # set_sink
        data.sink_offset = self.module.Reg('_%s_sink_offset' % prefix,
                                           self.addrwidth, initval=0)
        data.sink_size = self.module.Reg('_%s_sink_size' % prefix,
                                         self.addrwidth + 1, initval=0)
        data.sink_stride = self.module.Reg('_%s_sink_stride' % prefix,
                                           self.addrwidth, initval=0)

        data.sink_offset_buf = self.module.Reg('_%s_sink_offset_buf' % prefix,
                                               self.addrwidth, initval=0)
        data.sink_size_buf = self.module.Reg('_%s_sink_size_buf' % prefix,
                                             self.addrwidth + 1, initval=0)
        data.sink_stride_buf = self.module.Reg('_%s_sink_stride_buf' % prefix,
                                               self.addrwidth, initval=0)

        # set_sink_pattern
        data.sink_pat_cur_offsets = None
        data.sink_pat_sizes = None
        data.sink_pat_strides = None
        data.sink_pat_counts = None

        data.sink_pat_size_bufs = None
        data.sink_pat_stride_bufs = None

        # set_sink_multipattern
        data.sink_multipat_num_patterns = None
        data.sink_multipat_offsets = None
        data.sink_multipat_cur_offsets = None
        data.sink_multipat_sizes = None
        data.sink_multipat_strides = None

        data.sink_multipat_offset_bufs = None
        data.sink_multipat_size_bufs = None
        data.sink_multipat_stride_bufs = None

        # RAM, FIFO
        data.sink_id_map = OrderedDict()
        data.sink_sel = self.module.Reg('_%s_sink_sel' % prefix,
                                        self.ram_sel_width, initval=0)

        # RAM
        data.sink_ram_waddr = self.module.Reg('_%s_sink_waddr' % prefix,
                                              self.addrwidth, initval=0)
        data.sink_ram_wenable = self.module.Reg('_%s_sink_wenable' % prefix,
                                                initval=0)
        data.sink_ram_wdata = self.module.Reg('_%s_sink_wdata' % prefix,
                                              data.width, initval=0)

        # FIFO
        data.sink_fifo_enq = self.module.Reg('_%s_sink_fifo_enq' % prefix,
                                             initval=0)
        data.sink_fifo_wdata = self.module.Reg('_%s_sink_fifo_wdata' % prefix,
                                               data.width, initval=0)

        # immediate
        data.sink_immediate = self.module.Reg('_%s_sink_immediate' % prefix,
                                              data.width, initval=0)

        # default value
        self.seq.If(self.oready)(
            data.sink_ram_wenable(0),
            data.sink_fifo_enq(0)
        )

        if when is not None:
            self.sink(when, when_name)
            self.sink_when_map[name] = when

    def terminate(self, data):
        _id = self.var_id_count
        name = terminate_prefix % _id
        self.terminates.append(data)
        self.sink(data, name)
        return data

    def parameter(self, name=None, datawidth=None, point=0, signed=True):
        if self.stream_synthesized:
            raise ValueError(
                'cannot modify the stream because already synthesized')

        _id = self.var_id_count
        if name is None:
            name = 'parameter_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        prefix = self._prefix(name)

        self.var_id_count += 1

        if datawidth is None:
            datawidth = self.datawidth

        var = self.Variable(self._dataname(name), datawidth, point, signed)

        self.parameters[name] = var
        self.var_id_map[_id] = var
        self.var_name_map[name] = var
        self.var_id_name_map[_id] = name
        self.var_name_id_map[name] = _id

        var.next_parameter_data = self.module.Reg('_%s_next_parameter_data' % prefix,
                                                  datawidth, initval=0)
        var.next_parameter_data.no_write_check = True
        var.has_parameter_data = False

        return var

    def substream(self, child):
        _id = self.var_id_count
        name = 'substream_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        prefix = self._prefix(name)
        self.var_id_count += 1

        sub = Substream(self.module, self.clock, self.reset, child, self)
        self.substreams.append(sub)

        if child.reduce_reset is not None:
            if self.reduce_reset is None:
                self._make_reduce_reset()

            sub.to_source(reduce_reset_name, self.reduce_reset)

        return sub

    def substream_multicycle(self, child):
        _id = self.var_id_count
        name = 'substream_multicycle_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        prefix = self._prefix(name)
        self.var_id_count += 1

        sub = SubstreamMultiCycle(self.module, self.clock, self.reset, child, self)
        self.substreams.append(sub)

        if child.reduce_reset is not None:
            if self.reduce_reset is None:
                self._make_reduce_reset()

            sub.to_source(reduce_reset_name, self.reduce_reset)

        return sub

    def read_RAM(self, name, addr, when=None,
                 datawidth=None, point=0, signed=True):

        if self.stream_synthesized:
            raise ValueError(
                'cannot modify the stream because already synthesized')

        _id = self.var_id_count
        if name is None:
            name = 'read_ram_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        prefix = self._prefix(name)

        self.var_id_count += 1

        if datawidth is None:
            datawidth = self.datawidth

        var = self.ReadRAM(addr, when=when,
                           width=datawidth, point=point, signed=signed, ram_name=name)

        self.read_rams[name] = var
        self.var_id_map[_id] = var
        self.var_name_map[name] = var
        self.var_id_name_map[_id] = name
        self.var_name_id_map[name] = _id

        var.read_ram_id_map = OrderedDict()
        var.read_ram_sel = self.module.Reg('_%s_read_ram_sel' % prefix,
                                           self.ram_sel_width, initval=0)

        return var

    def write_RAM(self, name, addr, data, when=None):

        if self.stream_synthesized:
            raise ValueError(
                'cannot modify the stream because already synthesized')

        _id = self.var_id_count
        if name is None:
            name = 'write_ram_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        prefix = self._prefix(name)

        self.var_id_count += 1

        var = self.WriteRAM(addr, data, when=when, ram_name=name)

        self.write_rams[name] = var
        self.var_id_map[_id] = var
        self.var_name_map[name] = var
        self.var_id_name_map[_id] = name
        self.var_name_id_map[name] = _id

        var.write_ram_id_map = OrderedDict()
        var.write_ram_sel = self.module.Reg('_%s_write_ram_sel' % prefix,
                                            self.ram_sel_width, initval=0)

        return var

    def read_modify_write_RAM(self, name, raddrs, waddr, op, op_args, when=None,
                              datawidth_list=None, point_list=None, signed_list=None):

        if self.stream_synthesized:
            raise ValueError(
                'cannot modify the stream because already synthesized')

        _id = self.var_id_count
        if name is None:
            name = 'read_modify_write_ram_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        self.var_id_count += 1

        if datawidth_list is None:
            datawidth_list = [None for raddr in raddrs]
            point_list = [None for raddr in raddrs]
            signed_list = [True for raddr in raddrs]

        if len(raddrs) > 1:
            raddrs = self.Sync(*raddrs)

        read_vars = []
        read_rams = []

        for i, (raddr, datawidth, point, signed) in enumerate(
                zip(raddrs, datawidth_list, point_list, signed_list)):

            read_name = '_'.join([name, 'read', '%d' % i])
            read_var = self.read_RAM(read_name, raddr, when=None,
                                     datawidth=datawidth, point=point, signed=signed)
            read_var.latency = 1
            read_vars.append(read_var)
            read_rams.append(read_name)

        read_vars = [self.ForwardDest(read_var, raddr)
                     for read_var, raddr in zip(read_vars, raddrs)]

        args = []
        args.extend(read_vars)
        args.extend(op_args)
        write_var = op(*args)

        for read_var in read_vars:
            self.ForwardSource(write_var, waddr, read_var)

        write_name = '_'.join([name, 'write'])
        write_var = self.write_RAM(write_name, waddr, write_var, when=when)
        write_ram = write_name

        read_rams = tuple(read_rams)

        self.read_modify_write_rams[name] = (read_rams, write_ram)
        self.var_id_map[_id] = (read_rams, write_ram)
        self.var_name_map[name] = (read_rams, write_ram)
        self.var_id_name_map[_id] = name
        self.var_name_id_map[name] = _id

        return write_var

    def read_fifo(self, name, when=None,
                  datawidth=None, point=0, signed=True):

        if self.stream_synthesized:
            raise ValueError(
                'cannot modify the stream because already synthesized')

        _id = self.var_id_count
        if name is None:
            name = 'read_fifo_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        prefix = self._prefix(name)

        self.var_id_count += 1

        if datawidth is None:
            datawidth = self.datawidth

        var = self.ReadFIFO(when=when,
                            width=datawidth, point=point, signed=signed, fifo_name=name)

        self.read_fifos[name] = var
        self.var_id_map[_id] = var
        self.var_name_map[name] = var
        self.var_id_name_map[_id] = name
        self.var_name_id_map[name] = _id

        var.read_fifo_id_map = OrderedDict()
        var.read_fifo_sel = self.module.Reg('_%s_read_fifo_sel' % prefix,
                                            self.ram_sel_width, initval=0)

        return var

    def write_fifo(self, name, data, when=None):

        if self.stream_synthesized:
            raise ValueError(
                'cannot modify the stream because already synthesized')

        _id = self.var_id_count
        if name is None:
            name = 'write_fifo_%d' % _id

        if name in self.var_name_map:
            raise ValueError("'%s' is already defined in stream '%s'" %
                             (name, self.name))

        prefix = self._prefix(name)

        self.var_id_count += 1

        var = self.WriteFIFO(data, when=when, fifo_name=name)

        self.write_fifos[name] = var
        self.var_id_map[_id] = var
        self.var_name_map[name] = var
        self.var_id_name_map[_id] = name
        self.var_name_id_map[name] = _id

        var.write_fifo_id_map = OrderedDict()
        var.write_fifo_sel = self.module.Reg('_%s_write_fifo_sel' % prefix,
                                             self.ram_sel_width, initval=0)

        return var

    def set_source(self, fsm, name, ram, offset, size, stride=1, port=0):
        """ intrinsic method to assign RAM property to a source stream """
        self._set_source(fsm, name, ram, offset, size, stride, port)
        fsm.goto_next()

    def _set_source(self, fsm, name, ram, offset, size, stride=1, port=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sources:
            raise NameError("No such stream '%s'" % name)

        set_cond = self._set_flag(fsm)

        self.seq.If(set_cond)(
            var.source_mode(mode_ram_normal),
            var.source_offset(offset),
            var.source_size(size),
            var.source_stride(stride)
        )

        port = vtypes.to_int(port)
        self._setup_source_ram(ram, var, port, set_cond)
        self._synthesize_set_source(var, name)

    def set_source_pattern(self, fsm, name, ram, offset, pattern, port=0):
        """ intrinsic method to assign RAM property to a source stream """
        self._set_source_pattern(fsm, name, ram, offset, pattern, port)
        fsm.goto_next()

    def _set_source_pattern(self, fsm, name, ram, offset, pattern, port=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sources:
            raise NameError("No such stream '%s'" % name)

        if not isinstance(pattern, (tuple, list)):
            raise TypeError('pattern must be list or tuple.')

        if not pattern:
            raise ValueError(
                'pattern must have one (size, stride) pair at least.')

        if not isinstance(pattern[0], (tuple, list)):
            pattern = (pattern,)

        pattern = tuple(pattern)

        if len(pattern) > self.max_pattern_length:
            raise ValueError(
                "'pattern' length exceeds maximum pattern length.")

        self._make_source_pattern_vars(var, name)

        set_cond = self._set_flag(fsm)

        self.seq.If(set_cond)(
            var.source_mode(mode_ram_pattern),
            var.source_offset(offset)
        )

        pad = tuple([(1, 0)
                     for _ in range(self.max_pattern_length - len(pattern))])

        for (source_pat_size, source_pat_stride,
             (size, stride)) in zip(var.source_pat_sizes, var.source_pat_strides,
                                    pattern + pad):
            self.seq.If(set_cond)(
                source_pat_size(size),
                source_pat_stride(stride)
            )

        port = vtypes.to_int(port)
        self._setup_source_ram(ram, var, port, set_cond)
        self._synthesize_set_source_pattern(var, name)

    def set_source_multidim(self, fsm, name, ram, offset, shape, order=None, port=0):
        """ intrinsic method to assign RAM property to a source stream """
        self._set_source_multidim(fsm, name, ram, offset, shape, order, port)
        fsm.goto_next()

    def _set_source_multidim(self, fsm, name, ram, offset, shape, order=None, port=0):
        if order is None:
            order = list(reversed(range(len(shape))))

        pattern = self._to_pattern(shape, order)
        self._set_source_pattern(fsm, name, ram, offset, pattern, port)

    def set_source_multipattern(self, fsm, name, ram, offsets, patterns, port=0):
        """ intrinsic method to assign multiple patterns to a RAM """
        self._set_source_multipattern(fsm, name, ram, offsets, patterns, port)
        fsm.goto_next()

    def _set_source_multipattern(self, fsm, name, ram, offsets, patterns, port=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sources:
            raise NameError("No such stream '%s'" % name)

        if not isinstance(patterns, (tuple, list)):
            raise TypeError('patterns must be list or tuple.')

        if not patterns:
            raise ValueError(
                'patterns must have one [(size, stride)] list at least.')

        if not isinstance(offsets, (tuple, list)):
            offsets = [offsets] * len(patterns)

        if not offsets:
            raise ValueError('offsets must have one offset value at least.')

        offsets = tuple(offsets)
        patterns = tuple(patterns)

        if len(offsets) != len(patterns):
            raise ValueError(
                "number of offsets must be 1 or equal to the number of patterns.")

        if len(offsets) > self.max_multipattern_length:
            raise ValueError(
                "'offsets' length exceeds maximum multipattern length.")

        if len(patterns) > self.max_multipattern_length:
            raise ValueError(
                "'patterns' length exceeds maximum multipattern length.")

        for pattern in patterns:
            if len(pattern) > self.max_pattern_length:
                raise ValueError(
                    "'pattern' length exceeds maximum pattern length.")

        self._make_source_multipattern_vars(var, name)

        set_cond = self._set_flag(fsm)

        self.seq.If(set_cond)(
            var.source_mode(mode_ram_multipattern),
            var.source_multipat_num_patterns(len(patterns))
        )

        offsets_pad = tuple(
            [0 for _ in range(self.max_multipattern_length - len(patterns))])

        for offset, multipat_offset in zip(offsets + offsets_pad,
                                           var.source_multipat_offsets):
            self.seq.If(set_cond)(
                multipat_offset(offset)
            )

        for multipat_sizes, multipat_strides, pattern in zip(
                var.source_multipat_sizes, var.source_multipat_strides, patterns):
            pad = tuple([(1, 0)
                         for _ in range(self.max_pattern_length - len(pattern))])

            for (multipat_size, multipat_stride,
                 (size, stride)) in zip(multipat_sizes, multipat_strides,
                                        pattern + pad):
                self.seq.If(set_cond)(
                    multipat_size(size),
                    multipat_stride(stride)
                )

        port = vtypes.to_int(port)
        self._setup_source_ram(ram, var, port, set_cond)
        self._synthesize_set_source_multipattern(var, name)

    def set_source_generator(self, fsm, name, ram, func, initvals, args=(), port=0):
        """ intrinsic method to assign address generator function to a source stream """
        self._set_source_generator(fsm, name, ram, func, initvals, args, port)
        fsm.goto_next()

    def _set_source_generator(self, fsm, name, ram, func, initvals, args=(), port=0):
        if not isinstance(initvals, (tuple, list)):
            raise TypeError('initvals be 1 tuple or list.')

        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sources:
            raise NameError("No such stream '%s'" % name)

        set_cond = self._set_flag(fsm)
        generator_id = len(var.source_generator_fsms)

        self.seq.If(set_cond)(
            var.source_mode(mode_ram_generator),
            var.source_generator_id(generator_id)
        )

        port = vtypes.to_int(port)
        self._setup_source_ram(ram, var, port, set_cond)
        self._synthesize_set_source_generator(var, name, func, initvals, args)

    def set_source_fifo(self, fsm, name, fifo, size):
        """ intrinsic method to assign FIFO property to a source stream """
        self._set_source_fifo(fsm, name, fifo, size)
        fsm.goto_next()

    def _set_source_fifo(self, fsm, name, fifo, size):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sources:
            raise NameError("No such stream '%s'" % name)

        set_cond = self._set_flag(fsm)

        self.seq.If(set_cond)(
            var.source_mode(mode_fifo),
            var.source_size(size),
        )

        self._setup_source_fifo(fifo, var, set_cond)
        self._synthesize_set_source_fifo(var, name)

    def set_source_empty(self, fsm, name, value=0):
        self._set_source_empty(fsm, name, value)
        fsm.goto_next()

    def _set_source_empty(self, fsm, name, value=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sources:
            raise NameError("No such stream '%s'" % name)

        set_cond = self._set_flag(fsm)

        self.seq.If(set_cond)(
            var.source_mode(mode_idle),
            var.source_empty_data(value)
        )

        if var.has_source_empty:
            fsm.goto_next()
            return

        source_start = vtypes.Ands(self.source_start, self.oready,
                                   vtypes.Not(vtypes.Uor(vtypes.And(var.source_mode, mode_idle))))

        self.seq.If(source_start)(
            var.source_idle(1)
        )

        wdata = var.source_empty_data
        wenable = vtypes.Ands(source_start, self.is_root)
        var.write(wdata, wenable)

        var.has_source_empty = True

    def set_sink(self, fsm, name, ram, offset, size, stride=1, port=0):
        """ intrinsic method to assign RAM property to a sink stream """
        self._set_sink(fsm, name, ram, offset, size, stride, port)
        fsm.If(self.oready).goto_next()

    def _set_sink(self, fsm, name, ram, offset, size, stride=1, port=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sinks:
            raise NameError("No such stream '%s'" % name)

        set_cond_base = self._set_flag(fsm)
        set_cond = self._delay_from_start_to_sink(set_cond_base)
        sink_offset = self._delay_from_start_to_sink(offset)
        sink_size = self._delay_from_start_to_sink(size)
        sink_stride = self._delay_from_start_to_sink(stride)

        self.seq.If(set_cond)(
            var.sink_mode(mode_ram_normal),
            var.sink_offset(sink_offset),
            var.sink_size(sink_size),
            var.sink_stride(sink_stride)
        )

        port = vtypes.to_int(port)
        self._setup_sink_ram(ram, var, port, set_cond)
        self._synthesize_set_sink(var, name)

    def set_sink_pattern(self, fsm, name, ram, offset, pattern, port=0):
        """ intrinsic method to assign RAM property to a sink stream """
        self._set_sink_pattern(fsm, name, ram, offset, pattern, port)
        fsm.If(self.oready).goto_next()

    def _set_sink_pattern(self, fsm, name, ram, offset, pattern, port=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sinks:
            raise NameError("No such stream '%s'" % name)

        if not isinstance(pattern, (tuple, list)):
            raise TypeError('pattern must be list or tuple.')

        if not pattern:
            raise ValueError(
                'pattern must have one (size, stride) pair at least.')

        if not isinstance(pattern[0], (tuple, list)):
            pattern = (pattern,)

        pattern = tuple(pattern)

        if len(pattern) > self.max_pattern_length:
            raise ValueError(
                "'pattern' length exceeds maximum pattern length.")

        self._make_sink_pattern_vars(var, name)

        set_cond_base = self._set_flag(fsm)
        set_cond = self._delay_from_start_to_sink(set_cond_base)
        sink_offset = self._delay_from_start_to_sink(offset)

        self.seq.If(set_cond)(
            var.sink_mode(mode_ram_pattern),
            var.sink_offset(sink_offset)
        )

        pad = tuple([(1, 0)
                     for _ in range(self.max_pattern_length - len(pattern))])

        for (sink_pat_size, sink_pat_stride,
             (size, stride)) in zip(var.sink_pat_sizes, var.sink_pat_strides,
                                    pattern + pad):

            sink_size = self._delay_from_start_to_sink(size)
            sink_stride = self._delay_from_start_to_sink(stride)

            self.seq.If(set_cond)(
                sink_pat_size(sink_size),
                sink_pat_stride(sink_stride)
            )

        port = vtypes.to_int(port)
        self._setup_sink_ram(ram, var, port, set_cond)
        self._synthesize_set_sink_pattern(var, name)

    def set_sink_multidim(self, fsm, name, ram, offset, shape, order=None, port=0):
        """ intrinsic method to assign RAM property to a sink stream """
        self._set_sink_multidim(fsm, name, ram, offset, shape, order, port)
        fsm.If(self.oready).goto_next()

    def _set_sink_multidim(self, fsm, name, ram, offset, shape, order=None, port=0):
        if order is None:
            order = list(reversed(range(len(shape))))

        pattern = self._to_pattern(shape, order)
        self._set_sink_pattern(fsm, name, ram, offset, pattern, port)

    def set_sink_multipattern(self, fsm, name, ram, offsets, patterns, port=0):
        """ intrinsic method to assign multiple patterns to a RAM """
        self._set_sink_multipattern(fsm, name, ram, offsets, patterns, port)
        fsm.If(self.oready).goto_next()

    def _set_sink_multipattern(self, fsm, name, ram, offsets, patterns, port=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sinks:
            raise NameError("No such stream '%s'" % name)

        if not isinstance(patterns, (tuple, list)):
            raise TypeError('patterns must be list or tuple.')

        if not patterns:
            raise ValueError(
                'patterns must have one [(size, stride)] list at least.')

        if not isinstance(offsets, (tuple, list)):
            offsets = [offsets] * len(patterns)

        if not offsets:
            raise ValueError('offsets must have one offset value at least.')

        offsets = tuple(offsets)
        patterns = tuple(patterns)

        if len(offsets) != len(patterns):
            raise ValueError(
                "number of offsets must be 1 or equal to the number of patterns.")

        if len(offsets) > self.max_multipattern_length:
            raise ValueError(
                "'offsets' length exceeds maximum multipattern length.")

        if len(patterns) > self.max_multipattern_length:
            raise ValueError(
                "'patterns' length exceeds maximum multipattern length.")

        for pattern in patterns:
            if len(pattern) > self.max_pattern_length:
                raise ValueError(
                    "'pattern' length exceeds maximum pattern length.")

        self._make_sink_multipattern_vars(var, name)

        set_cond_base = self._set_flag(fsm)
        set_cond = self._delay_from_start_to_sink(set_cond_base)

        self.seq.If(set_cond)(
            var.sink_mode(mode_ram_multipattern),
            var.sink_multipat_num_patterns(len(patterns))
        )

        offsets_pad = tuple(
            [0 for _ in range(self.max_multipattern_length - len(patterns))])

        for offset, multipat_offset in zip(offsets + offsets_pad,
                                           var.sink_multipat_offsets):

            sink_offset = self._delay_from_start_to_sink(offset)

            self.seq.If(set_cond)(
                multipat_offset(sink_offset)
            )

        for multipat_sizes, multipat_strides, pattern in zip(
                var.sink_multipat_sizes, var.sink_multipat_strides, patterns):
            pad = tuple([(1, 0)
                         for _ in range(self.max_pattern_length - len(pattern))])

            for (multipat_size, multipat_stride,
                 (size, stride)) in zip(multipat_sizes, multipat_strides,
                                        pattern + pad):

                sink_size = self._delay_from_start_to_sink(size)
                sink_stride = self._delay_from_start_to_sink(stride)

                self.seq.If(set_cond)(
                    multipat_size(sink_size),
                    multipat_stride(sink_stride)
                )

        port = vtypes.to_int(port)
        self._setup_sink_ram(ram, var, port, set_cond)
        self._synthesize_set_sink_multipattern(var, name)

    def set_sink_generator(self, fsm, name, ram, func, initvals, args=(), port=0):
        """ intrinsic method to assign address generator function to a sink stream """
        self._set_sink_generator(fsm, name, ram, func, initvals, args, port)
        fsm.If(self.oready).goto_next()

    def _set_sink_generator(self, fsm, name, ram, func, initvals, args=(), port=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sinks:
            raise NameError("No such stream '%s'" % name)

        set_cond_base = self._set_flag(fsm)
        set_cond = self._delay_from_start_to_sink(set_cond_base)

        initvals = [self._delay_from_start_to_sink(initval) for initval in initvals]
        args = [self._delay_from_start_to_sink(arg) for arg in args]

        generator_id = len(var.sink_generator_fsms)

        self.seq.If(set_cond)(
            var.sink_mode(mode_ram_generator),
            var.sink_generator_id(generator_id)
        )

        port = vtypes.to_int(port)
        self._setup_sink_ram(ram, var, port, set_cond)
        self._synthesize_set_sink_generator(var, name, func, initvals, args)

    def set_sink_fifo(self, fsm, name, fifo, size):
        """ intrinsic method to assign FIFO property to a sink stream """
        self._set_sink_fifo(fsm, name, fifo, size)
        fsm.If(self.oready).goto_next()

    def _set_sink_fifo(self, fsm, name, fifo, size):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sinks:
            raise NameError("No such stream '%s'" % name)

        set_cond_base = self._set_flag(fsm)
        set_cond = self._delay_from_start_to_sink(set_cond_base)
        sink_size = self._delay_from_start_to_sink(size)

        self.seq.If(set_cond)(
            var.sink_mode(mode_fifo),
            var.sink_size(sink_size),
        )

        self._setup_sink_fifo(fifo, var, set_cond)
        self._synthesize_set_sink_fifo(var, name)

    def set_sink_immediate(self, fsm, name, size):
        """ intrinsic method to set a sink stream as an immediate variable """
        self._set_sink_immediate(fsm, name, size)
        fsm.If(self.oready).goto_next()

    def _set_sink_immediate(self, fsm, name, size):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sinks:
            raise NameError("No such stream '%s'" % name)

        set_cond_base = self._set_flag(fsm)
        set_cond = self._delay_from_start_to_sink(set_cond_base)
        sink_mode = mode_ram_normal
        sink_size = self._delay_from_start_to_sink(size)

        self.seq.If(set_cond)(
            var.sink_mode(sink_mode),
            var.sink_size(sink_size)
        )

        ram_sel = var.sink_sel
        self.seq.If(set_cond)(
            ram_sel(0)  # '0' is reserved for empty
        )

        self._synthesize_set_sink_immediate(var, name)

    def set_sink_empty(self, fsm, name):
        """ intrinsic method to assign RAM property to a sink stream """
        self._set_sink_empty(fsm, name)
        fsm.If(self.oready).goto_next()

    def _set_sink_empty(self, fsm, name):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sinks:
            raise NameError("No such stream '%s'" % name)

        set_cond_base = self._set_flag(fsm)
        set_cond = self._delay_from_start_to_sink(set_cond_base)

        ram_sel = var.sink_sel
        self.seq.If(set_cond)(
            ram_sel(0)  # '0' is reserved for empty
        )

    def set_parameter(self, fsm, name, value, raw=False):
        """ intrinsic method to assign parameter value to a parameter stream """
        self._set_parameter(fsm, name, value, raw)
        fsm.goto_next()

    def _set_parameter(self, fsm, name, value, raw=False):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.parameters:
            raise NameError("No such stream '%s'" % name)

        set_cond = self._set_flag(fsm)

        if not raw:
            value = fxd.write_adjust(value, var.point)

        self.seq.If(set_cond)(
            var.next_parameter_data(value)
        )

        if not var.has_parameter_data:
            var.write(var.next_parameter_data, self.source_start)
            var.has_parameter_data = True

    def set_read_RAM(self, fsm, name, ram, port=0):
        """ intrinsic method to assign RAM property to a read_RAM interface """
        self._set_read_RAM(fsm, name, ram, port)
        fsm.goto_next()

    def _set_read_RAM(self, fsm, name, ram, port=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.read_rams:
            raise NameError("No such stream '%s'" % name)

        set_cond = self._set_flag(fsm)

        port = vtypes.to_int(port)
        self._setup_read_ram(ram, var, port, set_cond)

    def set_write_RAM(self, fsm, name, ram, port=0):
        """ intrinsic method to assign RAM property to a write_RAM interface """
        self._set_write_RAM(fsm, name, ram, port)
        fsm.goto_next()

    def _set_write_RAM(self, fsm, name, ram, port=0):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.write_rams:
            raise NameError("No such stream '%s'" % name)

        set_cond = self._set_flag(fsm)

        port = vtypes.to_int(port)
        self._setup_write_ram(ram, var, port, set_cond)

    def set_read_modify_write_RAM(self, fsm, name, ram, read_ports=None, write_port=None):
        self._set_read_modify_write_RAM(fsm, name, ram, read_ports, write_port)
        fsm.goto_next()

    def _set_read_modify_write_RAM(self, fsm, name, ram, read_ports=None, write_port=None):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.read_modify_write_rams:
            raise NameError("No such stream '%s'" % name)

        read_rams, write_ram = var

        if read_ports is None:
            read_ports = [i for i, read_ram in enumerate(read_ram)]

        if write_port is None:
            write_port = read_ports[-1] + 1

        for i, (read_ram, read_port) in enumerate(zip(read_rams, read_ports)):
            read_name = read_ram
            self._set_read_RAM(fsm, read_name, ram, port=read_port)

        write_name = write_ram
        self._set_write_RAM(fsm, write_name, ram, port=write_port)

    def set_read_fifo(self, fsm, name, fifo):
        """ intrinsic method to assign FIFO property to a read_fifo interface """
        self._set_read_fifo(fsm, name, fifo)
        fsm.goto_next()

    def _set_read_fifo(self, fsm, name, fifo):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.read_fifos:
            raise NameError("No such stream '%s'" % name)

        set_cond = self._set_flag(fsm)

        self._setup_read_fifo(fifo, var, set_cond)

    def set_write_fifo(self, fsm, name, fifo):
        """ intrinsic method to assign FIFO property to a write_fifo interface """
        self._set_write_fifo(fsm, name, fifo)
        fsm.goto_next()

    def _set_write_fifo(self, fsm, name, fifo):
        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.write_fifos:
            raise NameError("No such stream '%s'" % name)

        set_cond = self._set_flag(fsm)

        self._setup_write_fifo(fifo, var, set_cond)

    def read_sink(self, fsm, name):
        """ intrinsic method to read the last output of a sink stream """

        if not self.stream_synthesized:
            self._implement_stream()

        if isinstance(name, str):
            var = self.var_name_map[name]
        elif isinstance(name, vtypes.Str):
            name = name.value
            var = self.var_name_map[name]
        elif isinstance(name, int):
            var = self.var_id_map[name]
        elif isinstance(name, vtypes.Int):
            name = name.value
            var = self.var_id_map[name]
        else:
            raise TypeError('Unsupported index name')

        if name not in self.sinks:
            raise NameError("No such stream '%s'" % name)

        fsm.goto_next()

        return var.sink_immediate

    def run(self, fsm):
        cond = self._set_flag(fsm)

        self._run(cond)
        fsm.goto_next()

        fsm.If(self.busy).goto_next()

        return 0

    def _run(self, cond):
        util.add_enable_cond(self.run_flag, cond, 1)

        if not self.fsm_synthesized:
            substreams = self._collect_substreams()
            for sub in substreams:
                if not sub.child.fsm_synthesized:
                    sub.child._synthesize_run()
                    sub.child.fsm_synthesized = True

            self._synthesize_run()
            self.fsm_synthesized = True

        return 0

    def _synthesize_run(self):
        # entry point
        self.fsm._set_index(0)

        # start
        self.fsm.If(self.run_flag)(
            self.source_start(1)
        )
        self.fsm.If(self.run_flag).goto_next()

        # restart state
        fsm_restart_state = self.fsm.current

        start_cond = self.source_start

        self.fsm.If(start_cond, self.oready)(
            self.source_start(0),
            self.source_busy(1)
        )

        self.fsm.seq.If(self.oready,
                        self._delay_from_start_to_ivalid_on(start_cond))(
            self.ivalid(1)
        )

        if self.reduce_reset is not None:
            cond = vtypes.Ands(self.oready,
                               self._delay_from_start_to_reduce_reset_on_before_off(start_cond))
            self.reduce_reset.write(1, cond=cond)

            cond = vtypes.Ands(self.oready,
                               self._delay_from_start_to_reduce_reset_off(start_cond))
            self.reduce_reset.write(0, cond=cond)

        if self.dump:
            self.seq.If(self.oready,
                        self._delay_from_start_to_ivalid_on(start_cond))(
                self.dump_enable(1)
            )

        self.fsm.If(start_cond, self.oready).goto_next()

        # compute (at this cycle, source_idle <- 0)
        self.fsm.If(self.oready).goto_next()

        # compute and join
        done_cond = None
        for key, source_idle in sorted(self.source_idle_map.items(),
                                       key=lambda x: x[0]):
            done_cond = make_condition(done_cond, source_idle)

        source_end_cond = make_condition(done_cond, self.fsm.here)

        # infinite execution (stream does stop even if all sources are halted.)
        if self.infinite:
            source_end_cond = vtypes.Int(0, width=1)

        # terminate
        source_term_cond = None
        for term in self.terminates:
            stage = term.end_stage
            v = make_condition(term.raw_data, self.valid_list[stage])

            # force flush
            for valid in self.valid_list[:stage + 1]:
                self.seq.If(self.oready, v)(
                    valid(0)
                )

            if source_term_cond is None:
                source_term_cond = v
            else:
                source_term_cond = vtypes.Ors(source_term_cond, v)

        if source_term_cond is not None:
            source_end_cond = vtypes.Ors(source_end_cond, source_term_cond)

        sink_term_cond = None
        for term in self.terminates:
            v = term.read()
            if sink_term_cond is None:
                sink_term_cond = v
            else:
                sink_term_cond = vtypes.Ors(sink_term_cond, v)

        if sink_term_cond is not None:
            sink_term_cond = make_condition(sink_term_cond, self.valid_list[-1])

        # source_stop and source_busy
        self.source_stop.assign(vtypes.Ands(self.oready, source_end_cond))

        self.fsm.If(self.oready, source_end_cond)(
            self.source_busy(0)
        )

        self.fsm.If(self.oready, source_end_cond).goto_init()

        # restart
        self.fsm.If(self.oready, source_end_cond, self.run_flag)(
            self.source_start(1)
        )
        self.fsm.If(self.oready, source_end_cond, self.run_flag).goto(fsm_restart_state)

        # deassert
        self.fsm.seq.If(self.oready, self._delay_from_start_to_ivalid_off(source_end_cond))(
            self.ivalid(0)
        )

        # reset accumulate pipelines
        if self.reduce_reset is not None:
            cond = vtypes.Ands(self.oready,
                               self._delay_from_start_to_reduce_reset_on(source_end_cond))
            self.reduce_reset.write(1, cond=cond)

        if self.dump:
            dump_delay = self.ram_delay
            self.seq.If(self.oready,
                        self._delay_from_start_to_ivalid_off(source_end_cond))(
                self.dump_enable(0)
            )

        self.sink_start.assign(self._delay_from_start_to_sink(self.source_start))

        # force flush
        if sink_term_cond is not None:
            not_sink_term_cond = vtypes.Not(sink_term_cond)
            masked_source_stop = vtypes.Ands(self.source_stop, not_sink_term_cond)
            sink_stop_value = vtypes.Ors(sink_term_cond,
                                         self._delay_from_start_to_sink_stop(masked_source_stop))
            self.sink_stop.assign(sink_stop_value)
            self.sink_busy.assign(
                self._delay_from_start_to_sink_busy(self.source_busy,
                                                    self.seq.Prev(sink_term_cond, 1, cond=self.oready)))
        else:
            sink_stop_value = self._delay_from_start_to_sink_stop(self.source_stop)
            self.sink_stop.assign(sink_stop_value)
            self.sink_busy.assign(self._delay_from_start_to_sink_busy(self.source_busy))

        # negative edge
        self.seq.If(vtypes.Not(self.sink_busy), self.seq.Prev(self.sink_busy, 1, cond=self.oready))(
            self.busy_reg(0)
        )
        self.seq.If(self.source_busy)(
            self.busy_reg(1)
        )

        if sink_term_cond is not None:
            self.seq.If(self.oready, sink_term_cond)(
                self.busy_reg(0)
            )

        self.busy.assign(vtypes.Ors(self.source_busy, self.sink_busy, self.busy_reg))

        return 0

    def join(self, fsm):
        fsm.If(vtypes.Not(self.busy)).goto_next()
        return 0

    def done(self, fsm):
        return vtypes.Not(self.busy)

    def source_join(self, fsm):
        fsm.If(vtypes.Not(self.source_busy)).goto_next()
        return 0

    def source_done(self, fsm):
        return vtypes.Not(self.source_busy)

    def sink_join(self, fsm):
        fsm.If(vtypes.Not(self.sink_busy)).goto_next()
        return 0

    def sink_done(self, fsm):
        return vtypes.Not(self.sink_busy)

    def source_join_and_run(self, fsm):
        cond = self._set_flag(fsm)

        self._run(cond)
        fsm.If(vtypes.Not(self.source_busy)).goto_next()

        fsm.If(self.busy).goto_next()

        return 0

    def enable_dump(self, fsm):
        if not self.dump:
            raise TypeError('dump mode is disabled.')

        self.seq.If(fsm.here)(
            self.dump_mask(0)
        )

        fsm.goto_next()
        return self.dump_mask

    def disable_dump(self, fsm):
        if not self.dump:
            raise TypeError('dump mode is disabled.')

        self.seq.If(fsm.here)(
            self.dump_mask(1)
        )

        fsm.goto_next()
        return self.dump_mask

    def _delay_from_start_to_sink(self, v):
        delay = self._write_delay()
        start_value = v
        first_renable = self.seq.Prev(start_value, 1, cond=self.oready)
        first_rvalid = self.seq.Prev(first_renable, 1, cond=self.oready)
        sink_value = self.seq.Prev(first_rvalid, delay, cond=self.oready)
        return sink_value

    def _delay_from_start_to_sink_stop(self, v):
        delay = self._write_delay()
        start_value = v
        first_renable = self.seq.Prev(start_value, 1, cond=self.oready)
        first_rvalid = self.seq.Prev(first_renable, 1, cond=self.oready)
        sink_value = self.seq.Prev(first_rvalid, delay, cond=self.oready)
        return sink_value

    def _delay_from_start_to_sink_busy(self, v, term=None):
        delay = self._write_delay()
        # start_value = v
        # first_renable = self.seq.Prev(start_value, 1, cond=self.oready)
        # first_rvalid = self.seq.Prev(first_renable, 1, cond=self.oready)
        # sink_value = self.seq.Prev(first_rvalid, delay, cond=self.oready)
        # return sink_value
        for i in range(delay + 2):
            n = self.module.TmpReg(initval=0)
            self.seq.If(self.oready)(
                n(v)
            )
            if term is not None:
                self.seq.If(self.oready, term)(
                    n(0)
                )
            v = n
        return v

    def _delay_from_start_to_ivalid_on(self, v):
        start_value = self.seq.Prev(v, 1, cond=self.oready)
        first_renable = self.seq.Prev(start_value, 1, cond=self.oready)
        first_rvalid = self.seq.Prev(first_renable, 1, cond=self.oready)
        return first_rvalid

    def _delay_from_start_to_reduce_reset_off(self, v):
        initial_reset = self.seq.Prev(v, 1, cond=self.oready)
        start_value = self.seq.Prev(initial_reset, 1, cond=self.oready)
        first_renable = self.seq.Prev(start_value, 1, cond=self.oready)
        first_rvalid = self.seq.Prev(first_renable, 1, cond=self.oready)
        return first_rvalid

    def _delay_from_start_to_reduce_reset_on_before_off(self, v):
        initial_reset = self.seq.Prev(v, 1, cond=self.oready)
        start_value = self.seq.Prev(initial_reset, 1, cond=self.oready)
        first_renable = self.seq.Prev(start_value, 1, cond=self.oready)
        return first_renable

    def _delay_from_start_to_ivalid_off(self, v):
        start_value = self.seq.Prev(v, 1, cond=self.oready)
        return start_value

    def _delay_from_start_to_reduce_reset_on(self, v):
        start_value = self.seq.Prev(v, 1, cond=self.oready)
        return start_value

    def _setup_source_ram(self, ram, var, port, set_cond):
        if ram._id() in var.source_id_map:
            ram_id = var.source_id_map[ram._id()]
            self.seq.If(set_cond)(
                var.source_sel(ram_id)
            )
            return

        if ram._id() not in self.buf_id_map:
            ram_id = self.buf_id_count
            self.buf_id_count += 1
            self.buf_id_map[ram._id()] = ram_id
        else:
            ram_id = self.buf_id_map[ram._id()]

        var.source_id_map[ram._id()] = ram_id

        self.seq.If(set_cond)(
            var.source_sel(ram_id)
        )

        ram_cond = (var.source_sel == ram_id)
        renable = vtypes.Ands(self.oready, var.source_ram_renable, ram_cond)

        d, v = ram.read_rtl(var.source_ram_raddr, port=port, cond=renable)

        d_out = d
        util.add_mux(var.source_ram_rdata, ram_cond, d_out)

        if (self.dump and
            (self.dump_mode == 'all' or
             self.dump_mode == 'ram' or
             (self.dump_mode == 'selective' and
                 hasattr(ram, 'dump') and ram.dump))):
            self._setup_source_ram_dump(ram, var, renable, d)

    def _setup_source_ram_dump(self, ram, var, read_enable, read_data):
        pipeline_depth = self.pipeline_depth()
        log_pipeline_depth = max(
            int(math.ceil(math.log(max(pipeline_depth, 10), 10))), 1)

        addr_base = (ram.dump_addr_base if hasattr(ram, 'dump_addr_base') else
                     self.dump_base)
        addr_base_char = ('b' if addr_base == 2 else
                          'o' if addr_base == 8 else
                          'd' if addr_base == 10 else
                          'x')
        addr_prefix = ('0b' if addr_base == 2 else
                       '0o' if addr_base == 8 else
                       '  ' if addr_base == 10 else
                       '0x')
        addr_vfmt = ''.join([addr_prefix, '%', addr_base_char])

        data_base = (ram.dump_data_base if hasattr(ram, 'dump_data_base') else
                     self.dump_base)
        data_base_char = ('b' if data_base == 2 else
                          'o' if data_base == 8 else
                          'd' if (data_base == 10 and
                                  (not hasattr(ram, 'point') or ram.point <= 0)) else
                          # 'f' if (data_base == 10 and
                          #        hasattr(ram, 'point') and ram.point > 0) else
                          'g' if (data_base == 10 and
                                  hasattr(ram, 'point') and ram.point > 0) else
                          'x')
        data_prefix = ('0b' if data_base == 2 else
                       '0o' if data_base == 8 else
                       '  ' if data_base == 10 else
                       '0x')
        # if data_base_char == 'f':
        #    point_len = int(math.ceil(ram.point / math.log(10, 2)))
        #    point_len = max(point_len, 8)
        #    total_len = int(math.ceil(ram.datawidth / math.log(10, 2)))
        #    total_len = max(total_len, point_len)
        #    data_vfmt = ''.join([data_prefix, '%',
        #                         '%d.%d' % (total_len + 1, point_len),
        #                         data_base_char])
        # else:
        #    data_vfmt = ''.join([data_prefix, '%', data_base_char])
        data_vfmt = ''.join([data_prefix, '%', data_base_char])

        name = ram.name
        fmt = ''.join(['(', self.name, ' step:%d, ',
                       'read, ', ' ' * (log_pipeline_depth + 2),
                       'age:%d) ', name,
                       '[', addr_vfmt, '] = ', data_vfmt])

        dump_ram_step_name = ('_stream_dump_ram_step_%d_%s' %
                              (self.object_id, name))
        dump_ram_step = self.module.Reg(dump_ram_step_name, 32, initval=0)

        enable = self.seq.Prev(read_enable, 1, cond=self.oready)
        age = dump_ram_step
        addr = self.seq.Prev(var.source_ram_raddr, 1, cond=self.oready)
        if hasattr(ram, 'point') and ram.point > 0:
            data = vtypes.Div(vtypes.SystemTask('itor', read_data),
                              1.0 * (2 ** ram.point))
        elif hasattr(ram, 'point') and ram.point < 0:
            data = vtypes.Times(read_data, 2 ** -ram.point)
        else:
            data = read_data

        self.seq(
            dump_ram_step(0)
        )
        self.seq.If(enable)(
            dump_ram_step.inc()
        )
        self.seq.If(self.dump_enable)(
            dump_ram_step.inc()
        )

        self.seq.If(enable, vtypes.Not(self.dump_mask))(
            vtypes.Display(fmt, dump_ram_step, age, addr, data)
        )

    def _synthesize_set_source(self, var, name):
        if var.source_fsm is not None:
            return

        source_start = vtypes.Ands(self.source_start,
                                   vtypes.And(var.source_mode, mode_ram_normal))

        self.seq.If(source_start, self.oready)(
            # var.source_idle(0),
            var.source_offset_buf(var.source_offset),
            var.source_size_buf(var.source_size),
            var.source_stride_buf(var.source_stride)
        )

        wdata = var.source_ram_rdata
        wenable = vtypes.Ands(self.oready, self.source_busy, self.is_root)
        var.write(wdata, wenable)

        fsm_id = self.fsm_id_count
        self.fsm_id_count += 1

        prefix = self._prefix(name)

        fsm_name = '_%s_source_fsm_%d' % (prefix, fsm_id)
        var.source_fsm = FSM(self.module, fsm_name, self.clock, self.reset,
                             as_module=self.fsm_as_module)

        var.source_fsm.If(source_start, self.oready).goto_next()

        self.seq.If(var.source_fsm.here, self.oready)(
            var.source_idle(0),
            var.source_ram_raddr(var.source_offset_buf),
            var.source_ram_renable(1),
            var.source_count(var.source_size_buf)
        )

        var.source_fsm.If(self.oready).goto_next()

        self.seq.If(var.source_fsm.here, self.oready)(
            var.source_ram_raddr.add(var.source_stride_buf),
            var.source_ram_renable(1),
            var.source_count.dec()
        )
        self.seq.If(var.source_fsm.here, var.source_count == 1, self.oready)(
            var.source_ram_renable(0),
            var.source_idle(1)
        )

        var.source_fsm.If(var.source_count == 1, self.oready).goto_init()

        # force flush
        self.seq.If(var.source_fsm.here, self.source_stop, self.oready)(
            var.source_ram_renable(0),
            var.source_idle(1)
        )
        var.source_fsm.If(self.source_stop, self.oready).goto_init()

    def _make_source_pattern_vars(self, var, name):
        if var.source_pat_cur_offsets is not None:
            return

        prefix = self._prefix(name)

        var.source_pat_cur_offsets = [
            self.module.Reg('_source_%s_pat_cur_offset_%d' % (prefix, i),
                            self.addrwidth, initval=0)
            for i in range(self.max_pattern_length)]
        var.source_pat_sizes = [self.module.Reg('_source_%s_pat_size_%d' % (prefix, i),
                                                self.addrwidth + 1, initval=0)
                                for i in range(self.max_pattern_length)]
        var.source_pat_strides = [self.module.Reg('_source_%s_pat_stride_%d' % (prefix, i),
                                                  self.addrwidth, initval=0)
                                  for i in range(self.max_pattern_length)]
        var.source_pat_counts = [self.module.Reg('_source_%s_pat_count_%d' % (prefix, i),
                                                 self.addrwidth + 1, initval=0)
                                 for i in range(self.max_pattern_length)]

        var.source_pat_size_bufs = [self.module.Reg('_source_%s_pat_size_buf_%d' % (prefix, i),
                                                    self.addrwidth + 1, initval=0)
                                    for i in range(self.max_pattern_length)]
        var.source_pat_stride_bufs = [self.module.Reg('_source_%s_pat_stride_buf_%d' % (prefix, i),
                                                      self.addrwidth, initval=0)
                                      for i in range(self.max_pattern_length)]

    def _synthesize_set_source_pattern(self, var, name):
        if var.source_pat_fsm is not None:
            return

        source_start = vtypes.Ands(self.source_start,
                                   vtypes.And(var.source_mode, mode_ram_pattern))

        self.seq.If(source_start, self.oready)(
            # var.source_idle(0),
            var.source_offset_buf(var.source_offset)
        )

        for source_pat_cur_offset in var.source_pat_cur_offsets:
            self.seq.If(source_start, self.oready)(
                source_pat_cur_offset(0)
            )

        for (source_pat_size, source_pat_count) in zip(
                var.source_pat_sizes, var.source_pat_counts):
            self.seq.If(source_start, self.oready)(
                source_pat_count(source_pat_size - 1)
            )

        for (source_pat_size_buf, source_pat_size) in zip(
                var.source_pat_size_bufs, var.source_pat_sizes):
            self.seq.If(source_start, self.oready)(
                source_pat_size_buf(source_pat_size)
            )

        for (source_pat_stride_buf, source_pat_stride) in zip(
                var.source_pat_stride_bufs, var.source_pat_strides):
            self.seq.If(source_start, self.oready)(
                source_pat_stride_buf(source_pat_stride)
            )

        wdata = var.source_ram_rdata
        wenable = vtypes.Ands(self.oready, self.source_busy, self.is_root)
        var.write(wdata, wenable)

        fsm_id = self.fsm_id_count
        self.fsm_id_count += 1

        prefix = self._prefix(name)

        fsm_name = '_%s_source_pat_fsm_%d' % (prefix, fsm_id)
        var.source_pat_fsm = FSM(self.module, fsm_name,
                                 self.clock, self.reset,
                                 as_module=self.fsm_as_module)

        var.source_pat_fsm.If(source_start, self.oready).goto_next()

        source_all_offset = self.module.Wire('_%s_source_pat_all_offset' % prefix,
                                             self.addrwidth)
        source_all_offset_val = var.source_offset_buf
        for source_pat_cur_offset in var.source_pat_cur_offsets:
            source_all_offset_val += source_pat_cur_offset
        source_all_offset.assign(source_all_offset_val)

        self.seq.If(var.source_pat_fsm.here, self.oready)(
            var.source_idle(0),
            var.source_ram_raddr(source_all_offset),
            var.source_ram_renable(1)
        )

        upcond = None

        for (source_pat_cur_offset, source_pat_size_buf,
             source_pat_stride_buf, source_pat_count) in zip(
                 var.source_pat_cur_offsets, var.source_pat_size_bufs,
                 var.source_pat_stride_bufs, var.source_pat_counts):

            self.seq.If(var.source_pat_fsm.here, upcond, self.oready)(
                source_pat_cur_offset.add(source_pat_stride_buf),
                source_pat_count.dec()
            )

            reset_cond = source_pat_count == 0
            self.seq.If(var.source_pat_fsm.here, upcond, reset_cond, self.oready)(
                source_pat_cur_offset(0),
                source_pat_count(source_pat_size_buf - 1)
            )
            upcond = make_condition(upcond, reset_cond)

        fin_cond = upcond

        # force flush
        self.seq.If(var.source_pat_fsm.here, self.source_stop, self.oready)(
            var.source_ram_renable(0),
            var.source_idle(1)
        )
        var.source_pat_fsm.If(self.source_stop, self.oready).goto_init()

        # finalize
        var.source_pat_fsm.If(fin_cond, self.oready).goto_next()

        self.seq.If(var.source_pat_fsm.here, self.oready)(
            var.source_ram_renable(0),
            var.source_idle(1)
        )

        var.source_pat_fsm.If(self.oready).goto_init()

    def _make_source_multipattern_vars(self, var, name):
        if var.source_multipat_cur_offsets is not None:
            return

        prefix = self._prefix(name)

        var.source_multipat_num_patterns = self.module.Reg(
            '_source_%s_multipat_num_patterns' % prefix,
            int(math.ceil(math.log(max(self.max_multipattern_length, 2), 2))), initval=0)
        var.source_multipat_offsets = [
            self.module.Reg('_source_%s_multipat_%d_offset' % (prefix, j),
                            self.addrwidth, initval=0)
            for j in range(self.max_multipattern_length)]
        var.source_multipat_cur_offsets = [
            self.module.Reg('_source_%s_multipat_%d_cur_offset' % (prefix, i),
                            self.addrwidth, initval=0)
            for i in range(self.max_pattern_length)]
        var.source_multipat_sizes = [[self.module.Reg('_source_%s_multipat_%d_size_%d' %
                                                      (prefix, j, i),
                                                      self.addrwidth + 1, initval=0)
                                      for i in range(self.max_pattern_length)]
                                     for j in range(self.max_multipattern_length)]
        var.source_multipat_strides = [[self.module.Reg('_source_%s_multipat_%d_stride_%d' %
                                                        (prefix, j, i),
                                                        self.addrwidth, initval=0)
                                        for i in range(self.max_pattern_length)]
                                       for j in range(self.max_multipattern_length)]
        var.source_multipat_counts = [[self.module.Reg('_source_%s_multipat_%d_count_%d' %
                                                       (prefix, j, i),
                                                       self.addrwidth + 1, initval=0)
                                       for i in range(self.max_pattern_length)]
                                      for j in range(self.max_multipattern_length)]

        var.source_multipat_offset_bufs = [
            self.module.Reg('_source_%s_multipat_%d_offset_buf' % (prefix, j),
                            self.addrwidth, initval=0)
            for j in range(self.max_multipattern_length)]
        var.source_multipat_size_bufs = [[self.module.Reg('_source_%s_multipat_%d_size_buf_%d' %
                                                          (prefix, j, i),
                                                          self.addrwidth, initval=0)
                                          for i in range(self.max_pattern_length)]
                                         for j in range(self.max_multipattern_length)]
        var.source_multipat_stride_bufs = [[self.module.Reg('_source_%s_multipat_%d_stride_buf_%d' %
                                                            (prefix, j, i),
                                                            self.addrwidth, initval=0)
                                            for i in range(self.max_pattern_length)]
                                           for j in range(self.max_multipattern_length)]

    def _synthesize_set_source_multipattern(self, var, name):
        if var.source_pat_fsm is not None:
            return

        source_start = vtypes.Ands(self.source_start,
                                   vtypes.And(var.source_mode, mode_ram_multipattern))

        # self.seq.If(source_start, self.oready)(
        #     # var.source_idle(0)
        # )

        for source_multipat_cur_offset in var.source_multipat_cur_offsets:
            self.seq.If(source_start, self.oready)(
                source_multipat_cur_offset(0)
            )

        self.seq.If(source_start, self.oready)(
            var.source_multipat_num_patterns.dec()
        )

        for (source_multipat_size, source_multipat_count) in zip(
                var.source_multipat_sizes[0], var.source_multipat_counts[0]):
            self.seq.If(source_start, self.oready)(
                source_multipat_count(source_multipat_size - 1)
            )

        for (source_multipat_offset_buf,
             source_multipat_offset) in zip(var.source_multipat_offset_bufs,
                                            var.source_multipat_offsets):
            self.seq.If(source_start, self.oready)(
                source_multipat_offset_buf(source_multipat_offset)
            )

        for (source_multipat_size_buf_line,
             source_multipat_size_line) in zip(var.source_multipat_size_bufs,
                                               var.source_multipat_sizes):
            for (source_multipat_size_buf,
                 source_multipat_size) in zip(source_multipat_size_buf_line,
                                              source_multipat_size_line):
                self.seq.If(source_start, self.oready)(
                    source_multipat_size_buf(source_multipat_size)
                )

        for (source_multipat_stride_buf_line,
             source_multipat_stride_line) in zip(var.source_multipat_stride_bufs,
                                                 var.source_multipat_strides):
            for (source_multipat_stride_buf,
                 source_multipat_stride) in zip(source_multipat_stride_buf_line,
                                                source_multipat_stride_line):
                self.seq.If(source_start, self.oready)(
                    source_multipat_stride_buf(source_multipat_stride)
                )

        wdata = var.source_ram_rdata
        wenable = vtypes.Ands(self.oready, self.source_busy, self.is_root)
        var.write(wdata, wenable)

        fsm_id = self.fsm_id_count
        self.fsm_id_count += 1

        prefix = self._prefix(name)

        fsm_name = '_%s_source_multipat_fsm_%d' % (prefix, fsm_id)
        var.source_multipat_fsm = FSM(self.module, fsm_name,
                                      self.clock, self.reset,
                                      as_module=self.fsm_as_module)

        var.source_multipat_fsm.If(source_start, self.oready).goto_next()

        source_all_offset = self.module.Wire('_%s_source_multipat_all_offset' % prefix,
                                             self.addrwidth)
        source_all_offset_val = var.source_multipat_offset_bufs[0]
        for source_multipat_cur_offset in var.source_multipat_cur_offsets:
            source_all_offset_val += source_multipat_cur_offset
        source_all_offset.assign(source_all_offset_val)

        self.seq.If(var.source_multipat_fsm.here, self.oready)(
            var.source_idle(0),
            var.source_ram_raddr(source_all_offset),
            var.source_ram_renable(1)
        )

        upcond = None

        for (source_multipat_cur_offset, source_multipat_size_buf,
             source_multipat_stride_buf, source_multipat_count) in zip(
                 var.source_multipat_cur_offsets, var.source_multipat_size_bufs[0],
                 var.source_multipat_stride_bufs[0], var.source_multipat_counts[0]):

            self.seq.If(var.source_multipat_fsm.here, upcond, self.oready)(
                source_multipat_cur_offset.add(source_multipat_stride_buf),
                source_multipat_count.dec()
            )

            reset_cond = source_multipat_count == 0
            self.seq.If(var.source_multipat_fsm.here, upcond, reset_cond, self.oready)(
                source_multipat_cur_offset(0),
                source_multipat_count(source_multipat_size_buf - 1)
            )
            upcond = make_condition(upcond, reset_cond)

        fin_cond = upcond

        prev_offset = var.source_multipat_offset_bufs[0]
        for multipat_offset_buf in var.source_multipat_offset_bufs[1:]:
            self.seq.If(fin_cond, var.source_multipat_fsm.here, self.oready)(
                prev_offset(multipat_offset_buf)
            )
            prev_offset = multipat_offset_buf

        prev_sizes = var.source_multipat_size_bufs[0]
        for multipat_sizes in var.source_multipat_size_bufs[1:]:
            for prev_size, size in zip(prev_sizes, multipat_sizes):
                self.seq.If(fin_cond, var.source_multipat_fsm.here, self.oready)(
                    prev_size(size)
                )
            prev_sizes = multipat_sizes

        prev_strides = var.source_multipat_stride_bufs[0]
        for multipat_strides in var.source_multipat_stride_bufs[1:]:
            for prev_stride, stride in zip(prev_strides, multipat_strides):
                self.seq.If(fin_cond, var.source_multipat_fsm.here, self.oready)(
                    prev_stride(stride)
                )
            prev_strides = multipat_strides

        self.seq.If(fin_cond, var.source_multipat_fsm.here, self.oready)(
            var.source_multipat_num_patterns.dec()
        )

        # force flush
        self.seq.If(var.source_multipat_fsm.here, self.source_stop, self.oready)(
            var.source_ram_renable(0),
            var.source_idle(1)
        )
        var.source_multipat_fsm.If(self.source_stop, self.oready).goto_init()

        # finalize
        var.source_multipat_fsm.If(fin_cond,
                                   var.source_multipat_num_patterns == 0,
                                   self.oready).goto_next()

        self.seq.If(var.source_multipat_fsm.here, self.oready)(
            var.source_ram_renable(0),
            var.source_idle(1)
        )

        var.source_multipat_fsm.If(self.oready).goto_init()

    def _synthesize_set_source_generator(self, var, name, func, initvals, args):

        num_generator_vars = len(initvals)

        if num_generator_vars < 1:
            raise ValueError('initvals must not be empty.')

        generator_id = len(var.source_generator_fsms)

        source_start = vtypes.Ands(self.source_start,
                                   vtypes.And(var.source_mode, mode_ram_generator),
                                   var.source_generator_id == generator_id)

        prefix = self._prefix(name)

        generator_vars = [self.module.Reg('%s_generator_%d_var_%d' % (prefix, generator_id, i),
                                          self.addrwidth, initval=0)
                          for i in range(num_generator_vars)]

        for generator_var, initval in zip(generator_vars, initvals):
            self.seq.If(source_start, self.oready)(
                generator_var(initval)
            )

        wdata = var.source_ram_rdata
        wenable = vtypes.Ands(self.oready, self.source_busy, self.is_root)
        var.write(wdata, wenable)

        fsm_name = '_%s_source_generator_fsm_%d' % (prefix, generator_id)
        fsm = FSM(self.module, fsm_name, self.clock, self.reset,
                  as_module=self.fsm_as_module)
        var.source_generator_fsms.append(fsm)

        fsm.If(source_start, self.oready).goto_next()

        current_addr = generator_vars[0]

        self.seq.If(fsm.here, self.oready)(
            var.source_idle(0),
            var.source_ram_raddr(current_addr),
            var.source_ram_renable(1),
        )

        func_args = generator_vars + list(args)
        ret = func(*func_args)

        last_name = '%s_generator_%d_last' % (prefix, generator_id)
        last = self.module.Wire(last_name)
        last.assign(ret[0])
        next_values = ret[1:]

        for generator_var, next_value in zip(generator_vars, next_values):
            self.seq.If(fsm.here, self.oready)(
                generator_var(next_value)
            )

        # force flush
        self.seq.If(fsm.here, self.source_stop, self.oready)(
            var.source_ram_renable(0),
            var.source_idle(1)
        )
        fsm.If(self.source_stop, self.oready).goto_init()

        # finalize
        fsm.If(last, self.oready).goto_next()

        self.seq.If(fsm.here, self.oready)(
            var.source_ram_renable(0),
            var.source_idle(1)
        )

        fsm.If(self.oready).goto_init()

    def _setup_source_fifo(self, fifo, var, set_cond):
        if fifo._id() in var.source_id_map:
            fifo_id = var.source_id_map[fifo._id()]
            self.seq.If(set_cond)(
                var.source_sel(fifo_id)
            )
            return

        if fifo._id() not in self.buf_id_map:
            fifo_id = self.buf_id_count
            self.buf_id_count += 1
            self.buf_id_map[fifo._id()] = fifo_id
        else:
            fifo_id = self.buf_id_map[fifo._id()]

        var.source_id_map[fifo._id()] = fifo_id

        self.seq.If(set_cond)(
            var.source_sel(fifo_id)
        )

        fifo_cond = (var.source_sel == fifo_id)
        deq = vtypes.Ands(self.oready, var.source_fifo_deq, fifo_cond)

        d, v, ready = fifo.deq_rtl(cond=deq)

        d_out = d
        util.add_mux(var.source_fifo_rdata, fifo_cond, d_out)

        # stall control
        cond = vtypes.Ands(self.source_busy, fifo_cond)
        fifo_oready = vtypes.Ors(ready, var.source_idle)
        util.add_disable_cond(self.oready, cond, fifo_oready)

        if (self.dump and
            (self.dump_mode == 'all' or
             self.dump_mode == 'fifo' or
             (self.dump_mode == 'selective' and
                 hasattr(fifo, 'dump') and fifo.dump))):
            self._setup_source_fifo_dump(fifo, var, deq, d)

    def _setup_source_fifo_dump(self, fifo, var, deq, read_data):
        pipeline_depth = self.pipeline_depth()
        log_pipeline_depth = max(
            int(math.ceil(math.log(max(pipeline_depth, 10), 10))), 1)

        data_base = (fifo.dump_data_base if hasattr(fifo, 'dump_data_base') else
                     self.dump_base)
        data_base_char = ('b' if data_base == 2 else
                          'o' if data_base == 8 else
                          'd' if (data_base == 10 and
                                  (not hasattr(fifo, 'point') or fifo.point <= 0)) else
                          # 'f' if (data_base == 10 and
                          #        hasattr(fifo, 'point') and fifo.point > 0) else
                          'g' if (data_base == 10 and
                                  hasattr(fifo, 'point') and fifo.point > 0) else
                          'x')
        data_prefix = ('0b' if data_base == 2 else
                       '0o' if data_base == 8 else
                       '  ' if data_base == 10 else
                       '0x')
        # if data_base_char == 'f':
        #    point_len = int(math.ceil(fifo.point / math.log(10, 2)))
        #    point_len = max(point_len, 8)
        #    total_len = int(math.ceil(fifo.datawidth / math.log(10, 2)))
        #    total_len = max(total_len, point_len)
        #    data_vfmt = ''.join([data_prefix, '%',
        #                         '%d.%d' % (total_len + 1, point_len),
        #                         data_base_char])
        # else:
        #    data_vfmt = ''.join([data_prefix, '%', data_base_char])
        data_vfmt = ''.join([data_prefix, '%', data_base_char])

        name = fifo.name
        fmt = ''.join(['(', self.name, ' step:%d, ',
                       'read, ', ' ' * (log_pipeline_depth + 2),
                       'age:%d) ', name,
                       ' = ', data_vfmt])

        dump_fifo_step_name = ('_stream_dump_fifo_step_%d_%s' %
                               (self.object_id, name))
        dump_fifo_step = self.module.Reg(dump_fifo_step_name, 32, initval=0)

        enable = self.seq.Prev(deq, 1, cond=self.oready)
        age = dump_fifo_step
        if hasattr(fifo, 'point') and fifo.point > 0:
            data = vtypes.Div(vtypes.SystemTask('itor', read_data),
                              1.0 * (2 ** fifo.point))
        elif hasattr(fifo, 'point') and fifo.point < 0:
            data = vtypes.Times(read_data, 2 ** -fifo.point)
        else:
            data = read_data

        self.seq(
            dump_fifo_step(0)
        )
        self.seq.If(enable)(
            dump_fifo_step.inc()
        )
        self.seq.If(self.dump_enable)(
            dump_fifo_step.inc()
        )

        self.seq.If(enable, vtypes.Not(self.dump_mask))(
            vtypes.Display(fmt, dump_fifo_step, age, data)
        )

    def _synthesize_set_source_fifo(self, var, name):
        if var.source_fsm is not None:
            return

        source_start = vtypes.Ands(self.source_start,
                                   vtypes.And(var.source_mode, mode_fifo))

        self.seq.If(source_start, self.oready)(
            var.source_idle(0),
            var.source_size_buf(var.source_size),
        )

        wdata = var.source_fifo_rdata
        wenable = vtypes.Ands(self.oready, self.source_busy, self.is_root)
        var.write(wdata, wenable)

        fsm_id = self.fsm_id_count
        self.fsm_id_count += 1

        prefix = self._prefix(name)

        fsm_name = '_%s_source_fsm_%d' % (prefix, fsm_id)
        var.source_fsm = FSM(self.module, fsm_name, self.clock, self.reset,
                             as_module=self.fsm_as_module)

        var.source_fsm.If(source_start, self.oready).goto_next()

        self.seq.If(var.source_fsm.here, self.oready)(
            var.source_fifo_deq(1),
            var.source_count(var.source_size_buf)
        )

        var.source_fsm.If(self.oready).goto_next()

        self.seq.If(var.source_fsm.here, self.oready)(
            var.source_fifo_deq(1),
            var.source_count.dec()
        )
        self.seq.If(var.source_fsm.here, var.source_count == 1, self.oready)(
            var.source_fifo_deq(0),
            var.source_idle(1)
        )
        var.source_fsm.If(var.source_count == 1, self.oready).goto_init()

        # force flush
        self.seq.If(var.source_fsm.here, self.source_stop, self.oready)(
            var.source_fifo_deq(0),
            var.source_idle(1)
        )
        var.source_fsm.If(self.source_stop, self.oready).goto_init()

    def _setup_sink_ram(self, ram, var, port, set_cond):
        if ram._id() in var.sink_id_map:
            ram_id = var.sink_id_map[ram._id()]
            self.seq.If(set_cond)(
                var.sink_sel(ram_id)
            )
            return

        if ram._id() not in self.buf_id_map:
            ram_id = self.buf_id_count
            self.buf_id_count += 1
            self.buf_id_map[ram._id()] = ram_id
        else:
            ram_id = self.buf_id_map[ram._id()]

        var.sink_id_map[ram._id()] = ram_id

        self.seq.If(set_cond)(
            var.sink_sel(ram_id)
        )

        ram_cond = (var.sink_sel == ram_id)
        wenable = vtypes.Ands(self.oready, var.sink_ram_wenable, ram_cond)
        ram.write_rtl(var.sink_ram_waddr, var.sink_ram_wdata,
                      port=port, cond=wenable)

        if (self.dump and
            (self.dump_mode == 'all' or
             self.dump_mode == 'ram' or
             (self.dump_mode == 'selective' and
                 hasattr(ram, 'dump') and ram.dump))):
            self._setup_sink_ram_dump(ram, var, wenable)

    def _setup_sink_ram_dump(self, ram, var, write_enable):
        pipeline_depth = self.pipeline_depth()
        log_pipeline_depth = max(
            int(math.ceil(math.log(max(pipeline_depth, 10), 10))), 1)

        addr_base = (ram.dump_addr_base if hasattr(ram, 'dump_addr_base') else
                     self.dump_base)
        addr_base_char = ('b' if addr_base == 2 else
                          'o' if addr_base == 8 else
                          'd' if addr_base == 10 else
                          'x')
        addr_prefix = ('0b' if addr_base == 2 else
                       '0o' if addr_base == 8 else
                       '  ' if addr_base == 10 else
                       '0x')
        addr_vfmt = ''.join([addr_prefix, '%', addr_base_char])

        data_base = (ram.dump_data_base if hasattr(ram, 'dump_data_base') else
                     self.dump_base)
        data_base_char = ('b' if data_base == 2 else
                          'o' if data_base == 8 else
                          'd' if (data_base == 10 and
                                  (not hasattr(ram, 'point') or ram.point <= 0)) else
                          # 'f' if (data_base == 10 and
                          #        hasattr(ram, 'point') and ram.point > 0) else
                          'g' if (data_base == 10 and
                                  hasattr(ram, 'point') and ram.point > 0) else
                          'x')
        data_prefix = ('0b' if data_base == 2 else
                       '0o' if data_base == 8 else
                       '  ' if data_base == 10 else
                       '0x')
        # if data_base_char == 'f':
        #    point_len = int(math.ceil(ram.point / math.log(10, 2)))
        #    point_len = max(point_len, 8)
        #    total_len = int(math.ceil(ram.datawidth / math.log(10, 2)))
        #    total_len = max(total_len, point_len)
        #    data_vfmt = ''.join([data_prefix, '%',
        #                         '%d.%d' % (total_len + 1, point_len),
        #                         data_base_char])
        # else:
        #    data_vfmt = ''.join([data_prefix, '%', data_base_char])
        data_vfmt = ''.join([data_prefix, '%', data_base_char])

        name = ram.name
        fmt = ''.join(['(', self.name, ' step:%d, ',
                       'write, ', ' ' * (log_pipeline_depth + 1),
                       'age:%d) ', name,
                       '[', addr_vfmt, '] = ', data_vfmt])

        enable = var.sink_ram_wenable
        age = self.seq.Prev(self.dump_step, pipeline_depth + 1, cond=self.oready) - 1
        addr = var.sink_ram_waddr
        if hasattr(ram, 'point') and ram.point > 0:
            data = vtypes.Div(vtypes.SystemTask('itor', var.sink_ram_wdata),
                              1.0 * (2 ** ram.point))
        elif hasattr(ram, 'point') and ram.point < 0:
            data = vtypes.Times(var.sink_ram_wdata, 2 ** -ram.point)
        else:
            data = var.sink_ram_wdata

        self.seq.If(enable, vtypes.Not(self.dump_mask))(
            vtypes.Display(fmt, self.dump_step, age, addr, data)
        )

    def _synthesize_set_sink(self, var, name):
        if var.sink_fsm is not None:
            return

        sink_start = vtypes.Ands(self.sink_start,
                                 vtypes.And(var.sink_mode, mode_ram_normal))

        self.seq.If(sink_start, self.oready)(
            var.sink_offset_buf(var.sink_offset),
            var.sink_size_buf(var.sink_size),
            var.sink_stride_buf(var.sink_stride)
        )

        fsm_id = self.fsm_id_count
        self.fsm_id_count += 1

        prefix = self._prefix(name)

        fsm_name = '_%s_sink_fsm_%d' % (prefix, fsm_id)
        var.sink_fsm = FSM(self.module, fsm_name, self.clock, self.reset,
                           as_module=self.fsm_as_module)

        var.sink_fsm.If(sink_start, self.oready).goto_next()
        self.seq.If(var.sink_fsm.here, self.oready)(
            var.sink_ram_waddr(var.sink_offset_buf - var.sink_stride_buf),
            var.sink_count(var.sink_size_buf),
        )
        var.sink_fsm.If(self.oready).goto_next()

        if name in self.sink_when_map:
            when = self.sink_when_map[name]
            wcond = when.read()
        else:
            wcond = None

        rdata = var.read()

        self.seq.If(var.sink_fsm.here, wcond, self.oready)(
            var.sink_ram_waddr.add(var.sink_stride_buf),
            var.sink_ram_wdata(rdata),
            var.sink_ram_wenable(1),
            var.sink_count.dec()
        )

        var.sink_fsm.If(wcond, var.sink_count == 1, self.oready).goto_init()
        var.sink_fsm.If(self.sink_stop, self.oready).goto_init()

    def _make_sink_pattern_vars(self, var, name):
        if var.sink_pat_cur_offsets is not None:
            return

        prefix = self._prefix(name)

        var.sink_pat_cur_offsets = [self.module.Reg('_sink_%s_pat_cur_offset_%d' % (prefix, i),
                                                    self.addrwidth, initval=0)
                                    for i in range(self.max_pattern_length)]
        var.sink_pat_sizes = [self.module.Reg('_sink_%s_pat_size_%d' % (prefix, i),
                                              self.addrwidth + 1, initval=0)
                              for i in range(self.max_pattern_length)]
        var.sink_pat_strides = [self.module.Reg('_sink_%s_pat_stride_%d' % (prefix, i),
                                                self.addrwidth, initval=0)
                                for i in range(self.max_pattern_length)]
        var.sink_pat_counts = [self.module.Reg('_sink_%s_pat_count_%d' % (prefix, i),
                                               self.addrwidth + 1, initval=0)
                               for i in range(self.max_pattern_length)]

        var.sink_pat_size_bufs = [self.module.Reg('_sink_%s_pat_size_buf_%d' % (prefix, i),
                                                  self.addrwidth + 1, initval=0)
                                  for i in range(self.max_pattern_length)]
        var.sink_pat_stride_bufs = [self.module.Reg('_sink_%s_pat_stride_buf_%d' % (prefix, i),
                                                    self.addrwidth, initval=0)
                                    for i in range(self.max_pattern_length)]

    def _synthesize_set_sink_pattern(self, var, name):
        if var.sink_pat_fsm is not None:
            return

        sink_start = vtypes.Ands(self.sink_start,
                                 vtypes.And(var.sink_mode, mode_ram_pattern))

        self.seq.If(sink_start, self.oready)(
            var.sink_offset_buf(var.sink_offset)
        )

        for (sink_pat_size_buf, sink_pat_size) in zip(
                var.sink_pat_size_bufs, var.sink_pat_sizes):
            self.seq.If(sink_start, self.oready)(
                sink_pat_size_buf(sink_pat_size)
            )

        for (sink_pat_stride_buf, sink_pat_stride) in zip(
                var.sink_pat_stride_bufs, var.sink_pat_strides):
            self.seq.If(sink_start, self.oready)(
                sink_pat_stride_buf(sink_pat_stride)
            )

        fsm_id = self.fsm_id_count
        self.fsm_id_count += 1

        prefix = self._prefix(name)

        fsm_name = '_%s_sink_pat_fsm_%d' % (prefix, fsm_id)
        var.sink_pat_fsm = FSM(self.module, fsm_name,
                               self.clock, self.reset,
                               as_module=self.fsm_as_module)

        var.sink_pat_fsm.If(sink_start, self.oready).goto_next()

        for sink_pat_cur_offset in var.sink_pat_cur_offsets:
            self.seq.If(var.sink_pat_fsm.here, self.oready)(
                sink_pat_cur_offset(0)
            )

        for (sink_pat_size_buf, sink_pat_count) in zip(
                var.sink_pat_size_bufs, var.sink_pat_counts):
            self.seq.If(var.sink_pat_fsm.here, self.oready)(
                sink_pat_count(sink_pat_size_buf - 1)
            )

        var.sink_pat_fsm.If(self.oready).goto_next()

        if name in self.sink_when_map:
            when = self.sink_when_map[name]
            wcond = when.read()
        else:
            wcond = None

        rdata = var.read()

        sink_all_offset = self.module.Wire('_%s_sink_pat_all_offset' % prefix,
                                           self.addrwidth)
        sink_all_offset_val = var.sink_offset_buf
        for sink_pat_cur_offset in var.sink_pat_cur_offsets:
            sink_all_offset_val += sink_pat_cur_offset
        sink_all_offset.assign(sink_all_offset_val)

        self.seq.If(var.sink_pat_fsm.here, wcond, self.oready)(
            var.sink_ram_waddr(sink_all_offset),
            var.sink_ram_wdata(rdata),
            var.sink_ram_wenable(1)
        )

        upcond = None

        for (sink_pat_cur_offset, sink_pat_size_buf,
             sink_pat_stride_buf, sink_pat_count) in zip(
                 var.sink_pat_cur_offsets, var.sink_pat_size_bufs,
                 var.sink_pat_stride_bufs, var.sink_pat_counts):

            self.seq.If(var.sink_pat_fsm.here, wcond, upcond, self.oready)(
                sink_pat_cur_offset.add(sink_pat_stride_buf),
                sink_pat_count.dec()
            )

            reset_cond = sink_pat_count == 0
            self.seq.If(var.sink_pat_fsm.here, wcond, upcond, reset_cond, self.oready)(
                sink_pat_cur_offset(0),
                sink_pat_count(sink_pat_size_buf - 1)
            )
            upcond = make_condition(upcond, reset_cond)

        fin_cond = upcond

        var.sink_pat_fsm.If(wcond, fin_cond, self.oready).goto_init()
        var.sink_pat_fsm.If(self.sink_stop, self.oready).goto_init()

    def _make_sink_multipattern_vars(self, var, name):
        if var.sink_multipat_cur_offsets is not None:
            return

        prefix = self._prefix(name)

        var.sink_multipat_num_patterns = self.module.Reg(
            '_sink_%s_multipat_num_patterns' % prefix,
            int(math.ceil(math.log(max(self.max_multipattern_length, 2), 2))), initval=0)
        var.sink_multipat_offsets = [
            self.module.Reg('_sink_%s_multipat_%d_offset' % (prefix, j),
                            self.addrwidth, initval=0)
            for j in range(self.max_multipattern_length)]
        var.sink_multipat_cur_offsets = [
            self.module.Reg('_sink_%s_multipat_%d_cur_offset' % (prefix, i),
                            self.addrwidth, initval=0)
            for i in range(self.max_pattern_length)]
        var.sink_multipat_sizes = [[self.module.Reg('_sink_%s_multipat_%d_size_%d' %
                                                    (prefix, j, i),
                                                    self.addrwidth + 1, initval=0)
                                    for i in range(self.max_pattern_length)]
                                   for j in range(self.max_multipattern_length)]
        var.sink_multipat_strides = [[self.module.Reg('_sink_%s_multipat_%d_stride_%d' %
                                                      (prefix, j, i),
                                                      self.addrwidth, initval=0)
                                      for i in range(self.max_pattern_length)]
                                     for j in range(self.max_multipattern_length)]
        var.sink_multipat_counts = [[self.module.Reg('_sink_%s_multipat_%d_count_%d' %
                                                     (prefix, j, i),
                                                     self.addrwidth + 1, initval=0)
                                     for i in range(self.max_pattern_length)]
                                    for j in range(self.max_multipattern_length)]

        var.sink_multipat_offset_bufs = [
            self.module.Reg('_sink_%s_multipat_%d_offset_buf' % (prefix, j),
                            self.addrwidth, initval=0)
            for j in range(self.max_multipattern_length)]
        var.sink_multipat_size_bufs = [[self.module.Reg('_sink_%s_multipat_%d_size_buf_%d' %
                                                        (prefix, j, i),
                                                        self.addrwidth, initval=0)
                                        for i in range(self.max_pattern_length)]
                                       for j in range(self.max_multipattern_length)]
        var.sink_multipat_stride_bufs = [[self.module.Reg('_sink_%s_multipat_%d_stride_buf_%d' %
                                                          (prefix, j, i),
                                                          self.addrwidth, initval=0)
                                          for i in range(self.max_pattern_length)]
                                         for j in range(self.max_multipattern_length)]

    def _synthesize_set_sink_multipattern(self, var, name):
        if var.sink_multipat_fsm is not None:
            return

        sink_start = vtypes.Ands(self.sink_start,
                                 vtypes.And(var.sink_mode, mode_ram_multipattern))

        self.seq.If(sink_start, self.oready)(
            var.sink_multipat_num_patterns.dec()
        )

        for (sink_multipat_offset_buf,
             sink_multipat_offset) in zip(var.sink_multipat_offset_bufs,
                                          var.sink_multipat_offsets):
            self.seq.If(sink_start, self.oready)(
                sink_multipat_offset_buf(sink_multipat_offset)
            )

        for (sink_multipat_size_buf_line,
             sink_multipat_size_line) in zip(var.sink_multipat_size_bufs,
                                             var.sink_multipat_sizes):
            for (sink_multipat_size_buf,
                 sink_multipat_size) in zip(sink_multipat_size_buf_line,
                                            sink_multipat_size_line):
                self.seq.If(sink_start, self.oready)(
                    sink_multipat_size_buf(sink_multipat_size)
                )

        for (sink_multipat_stride_buf_line,
             sink_multipat_stride_line) in zip(var.sink_multipat_stride_bufs,
                                               var.sink_multipat_strides):
            for (sink_multipat_stride_buf,
                 sink_multipat_stride) in zip(sink_multipat_stride_buf_line,
                                              sink_multipat_stride_line):
                self.seq.If(sink_start, self.oready)(
                    sink_multipat_stride_buf(sink_multipat_stride)
                )

        fsm_id = self.fsm_id_count
        self.fsm_id_count += 1

        prefix = self._prefix(name)

        fsm_name = '_%s_sink_multipat_fsm_%d' % (prefix, fsm_id)
        var.sink_multipat_fsm = FSM(self.module, fsm_name,
                                    self.clock, self.reset,
                                    as_module=self.fsm_as_module)

        var.sink_multipat_fsm.If(sink_start, self.oready).goto_next()

        for sink_multipat_cur_offset in var.sink_multipat_cur_offsets:
            self.seq.If(var.sink_multipat_fsm.here, self.oready)(
                sink_multipat_cur_offset(0)
            )

        for (sink_multipat_size, sink_multipat_count) in zip(
                var.sink_multipat_size_bufs[0], var.sink_multipat_counts[0]):
            self.seq.If(var.sink_multipat_fsm.here, self.oready)(
                sink_multipat_count(sink_multipat_size - 1)
            )

        var.sink_multipat_fsm.If(self.oready).goto_next()

        if name in self.sink_when_map:
            when = self.sink_when_map[name]
            wcond = when.read()
        else:
            wcond = None

        rdata = var.read()

        sink_all_offset = self.module.Wire('_%s_sink_multipat_all_offset' % prefix,
                                           self.addrwidth)
        sink_all_offset_val = var.sink_multipat_offset_bufs[0]
        for sink_multipat_cur_offset in var.sink_multipat_cur_offsets:
            sink_all_offset_val += sink_multipat_cur_offset
        sink_all_offset.assign(sink_all_offset_val)

        self.seq.If(var.sink_multipat_fsm.here, self.oready)(
            var.sink_ram_wenable(0)
        )
        self.seq.If(var.sink_multipat_fsm.here, wcond, self.oready)(
            var.sink_ram_waddr(sink_all_offset),
            var.sink_ram_wdata(rdata),
            var.sink_ram_wenable(1)
        )

        upcond = None

        for (sink_multipat_cur_offset, sink_multipat_size_buf,
             sink_multipat_stride_buf, sink_multipat_count) in zip(
                 var.sink_multipat_cur_offsets, var.sink_multipat_size_bufs[0],
                 var.sink_multipat_stride_bufs[0], var.sink_multipat_counts[0]):

            self.seq.If(var.sink_multipat_fsm.here, upcond, self.oready)(
                sink_multipat_cur_offset.add(sink_multipat_stride_buf),
                sink_multipat_count.dec()
            )

            reset_cond = sink_multipat_count == 0
            self.seq.If(var.sink_multipat_fsm.here, upcond, reset_cond, self.oready)(
                sink_multipat_cur_offset(0),
                sink_multipat_count(sink_multipat_size_buf - 1)
            )
            upcond = make_condition(upcond, reset_cond)

        fin_cond = upcond

        prev_offset = var.sink_multipat_offset_bufs[0]
        for multipat_offset_buf in var.sink_multipat_offset_bufs[1:]:
            self.seq.If(fin_cond, var.sink_multipat_fsm.here, self.oready)(
                prev_offset(multipat_offset_buf)
            )
            prev_offset = multipat_offset_buf

        prev_sizes = var.sink_multipat_size_bufs[0]
        for multipat_sizes in var.sink_multipat_size_bufs[1:]:
            for prev_size, size in zip(prev_sizes, multipat_sizes):
                self.seq.If(fin_cond, var.sink_multipat_fsm.here, self.oready)(
                    prev_size(size)
                )
            prev_sizes = multipat_sizes

        prev_strides = var.sink_multipat_stride_bufs[0]
        for multipat_strides in var.sink_multipat_stride_bufs[1:]:
            for prev_stride, stride in zip(prev_strides, multipat_strides):
                self.seq.If(fin_cond, var.sink_multipat_fsm.here, self.oready)(
                    prev_stride(stride)
                )
            prev_strides = multipat_strides

        self.seq.If(fin_cond, var.sink_multipat_fsm.here, self.oready)(
            var.sink_multipat_num_patterns.dec()
        )

        var.sink_multipat_fsm.If(fin_cond,
                                 var.sink_multipat_num_patterns == 0,
                                 self.oready).goto_init()
        var.sink_multipat_fsm.If(self.sink_stop, self.oready).goto_init()

    def _synthesize_set_sink_generator(self, var, name, func, initvals, args):

        num_generator_vars = len(initvals)

        if num_generator_vars < 1:
            raise ValueError('initvals must not be empty.')

        generator_id = len(var.sink_generator_fsms)

        sink_start = vtypes.Ands(self.sink_start,
                                 vtypes.And(var.sink_mode, mode_ram_generator),
                                 var.sink_generator_id == generator_id)

        initvals = [self.seq.Prev(initval, 1, cond=vtypes.Ands(sink_start, self.oready))
                    for initval in initvals]
        args = [self.seq.Prev(arg, 1, cond=vtypes.Ands(sink_start, self.oready))
                for arg in args]

        prefix = self._prefix(name)

        fsm_name = '_%s_sink_generator_fsm_%d' % (prefix, generator_id)
        fsm = FSM(self.module, fsm_name, self.clock, self.reset,
                  as_module=self.fsm_as_module)
        var.sink_generator_fsms.append(fsm)

        fsm.If(sink_start, self.oready).goto_next()

        generator_vars = [self.module.Reg('%s_generator_%d_var_%d' % (prefix, generator_id, i),
                                          self.addrwidth, initval=0)
                          for i in range(num_generator_vars)]

        for generator_var, initval in zip(generator_vars, initvals):
            self.seq.If(sink_start, self.oready)(
                generator_var(initval)
            )

        fsm.If(self.oready).goto_next()

        current_addr = generator_vars[0]

        if name in self.sink_when_map:
            when = self.sink_when_map[name]
            wcond = when.read()
        else:
            wcond = None

        rdata = var.read()

        self.seq.If(fsm.here, wcond, self.oready)(
            var.sink_ram_waddr(current_addr),
            var.sink_ram_wdata(rdata),
            var.sink_ram_wenable(1)
        )

        func_args = generator_vars + list(args)
        ret = func(*func_args)

        last_name = '%s_generator_%d_last' % (prefix, generator_id)
        last = self.module.Wire(last_name)
        last.assign(ret[0])
        next_values = ret[1:]

        for generator_var, next_value in zip(generator_vars, next_values):
            self.seq.If(fsm.here, self.oready, wcond)(
                generator_var(next_value)
            )

        fsm.If(last, wcond, self.oready).goto_init()
        fsm.If(self.sink_stop, self.oready).goto_init()

    def _setup_sink_fifo(self, fifo, var, set_cond):
        if fifo._id() in var.sink_id_map:
            fifo_id = var.sink_id_map[fifo._id()]
            self.seq.If(set_cond)(
                var.sink_sel(fifo_id)
            )
            return

        if fifo._id() not in self.buf_id_map:
            fifo_id = self.buf_id_count
            self.buf_id_count += 1
            self.buf_id_map[fifo._id()] = fifo_id
        else:
            fifo_id = self.buf_id_map[fifo._id()]

        var.sink_id_map[fifo._id()] = fifo_id

        self.seq.If(set_cond)(
            var.sink_sel(fifo_id)
        )

        fifo_cond = (var.sink_sel == fifo_id)
        enq = vtypes.Ands(self.oready, var.sink_fifo_enq, fifo_cond)
        ack, ready = fifo.enq_rtl(var.sink_fifo_wdata, cond=enq)

        # stall control
        cond = vtypes.Ands(self.sink_busy, fifo_cond)
        fifo_oready = ready
        util.add_disable_cond(self.oready, cond, fifo_oready)

        if (self.dump and
            (self.dump_mode == 'all' or
             self.dump_mode == 'fifo' or
             (self.dump_mode == 'selective' and
                 hasattr(fifo, 'dump') and fifo.dump))):
            self._setup_sink_fifo_dump(fifo, var, enq)

    def _setup_sink_fifo_dump(self, fifo, var, enq):
        pipeline_depth = self.pipeline_depth()
        log_pipeline_depth = max(
            int(math.ceil(math.log(max(pipeline_depth, 10), 10))), 1)

        data_base = (fifo.dump_data_base if hasattr(fifo, 'dump_data_base') else
                     self.dump_base)
        data_base_char = ('b' if data_base == 2 else
                          'o' if data_base == 8 else
                          'd' if (data_base == 10 and
                                  (not hasattr(fifo, 'point') or fifo.point <= 0)) else
                          # 'f' if (data_base == 10 and
                          #        hasattr(fifo, 'point') and fifo.point > 0) else
                          'g' if (data_base == 10 and
                                  hasattr(fifo, 'point') and fifo.point > 0) else
                          'x')
        data_prefix = ('0b' if data_base == 2 else
                       '0o' if data_base == 8 else
                       '  ' if data_base == 10 else
                       '0x')
        # if data_base_char == 'f':
        #    point_len = int(math.ceil(fifo.point / math.log(10, 2)))
        #    point_len = max(point_len, 8)
        #    total_len = int(math.ceil(fifo.datawidth / math.log(10, 2)))
        #    total_len = max(total_len, point_len)
        #    data_vfmt = ''.join([data_prefix, '%',
        #                         '%d.%d' % (total_len + 1, point_len),
        #                         data_base_char])
        # else:
        #    data_vfmt = ''.join([data_prefix, '%', data_base_char])
        data_vfmt = ''.join([data_prefix, '%', data_base_char])

        name = fifo.name
        fmt = ''.join(['(', self.name, ' step:%d, ',
                       'write, ', ' ' * (log_pipeline_depth + 1),
                       'age:%d) ', name,
                       ' = ', data_vfmt])

        enable = var.sink_fifo_enq
        age = self.seq.Prev(self.dump_step, pipeline_depth + 1, cond=self.oready) - 1
        if hasattr(fifo, 'point') and fifo.point > 0:
            data = vtypes.Div(vtypes.SystemTask('itor', var.sink_fifo_wdata),
                              1.0 * (2 ** fifo.point))
        elif hasattr(fifo, 'point') and fifo.point < 0:
            data = vtypes.Times(var.sink_fifo_wdata, 2 ** -fifo.point)
        else:
            data = var.sink_fifo_wdata

        self.seq.If(enable, vtypes.Not(self.dump_mask))(
            vtypes.Display(fmt, self.dump_step, age, data)
        )

    def _synthesize_set_sink_fifo(self, var, name):
        if var.sink_fsm is not None:
            return

        sink_start = vtypes.Ands(self.sink_start,
                                 vtypes.And(var.sink_mode, mode_fifo))

        self.seq.If(sink_start, self.oready)(
            var.sink_size_buf(var.sink_size),
        )

        fsm_id = self.fsm_id_count
        self.fsm_id_count += 1

        prefix = self._prefix(name)

        fsm_name = '_%s_sink_fsm_%d' % (prefix, fsm_id)
        var.sink_fsm = FSM(self.module, fsm_name, self.clock, self.reset,
                           as_module=self.fsm_as_module)

        var.sink_fsm.If(sink_start, self.oready).goto_next()

        self.seq.If(var.sink_fsm.here, self.oready)(
            var.sink_count(var.sink_size),
            var.sink_size_buf(var.sink_size),
        )
        var.sink_fsm.If(self.oready).goto_next()

        if name in self.sink_when_map:
            when = self.sink_when_map[name]
            wcond = when.read()
        else:
            wcond = None

        rdata = var.read()

        self.seq.If(var.sink_fsm.here, wcond, self.oready)(
            var.sink_fifo_wdata(rdata),
            var.sink_fifo_enq(1),
            var.sink_count.dec()
        )

        var.sink_fsm.If(wcond, var.sink_count == 1, self.oready).goto_init()
        var.sink_fsm.If(self.sink_stop, self.oready).goto_init()

    def _synthesize_set_sink_immediate(self, var, name):
        if var.sink_fsm is not None:
            return

        sink_start = vtypes.Ands(self.sink_start,
                                 vtypes.And(var.sink_mode, mode_ram_normal))

        self.seq.If(sink_start, self.oready)(
            var.sink_size_buf(var.sink_size)
        )

        fsm_id = self.fsm_id_count
        self.fsm_id_count += 1

        prefix = self._prefix(name)

        fsm_name = '_%s_sink_fsm_%d' % (prefix, fsm_id)
        var.sink_fsm = FSM(self.module, fsm_name, self.clock, self.reset,
                           as_module=self.fsm_as_module)

        var.sink_fsm.If(sink_start, self.oready).goto_next()

        self.seq.If(var.sink_fsm.here, self.oready)(
            var.sink_count(var.sink_size_buf)
        )
        var.sink_fsm.If(self.oready).goto_next()

        if name in self.sink_when_map:
            when = self.sink_when_map[name]
            wcond = when.read()
        else:
            wcond = None

        rdata = var.read()

        self.seq.If(var.sink_fsm.here, wcond, self.oready)(
            var.sink_immediate(rdata),
            var.sink_count.dec()
        )

        var.sink_fsm.If(wcond, var.sink_count == 1, self.oready).goto_init()
        var.sink_fsm.If(self.sink_stop, self.oready).goto_init()

    def _setup_read_ram(self, ram, var, port, set_cond):
        if ram._id() in var.read_ram_id_map:
            ram_id = var.read_ram_id_map[ram._id()]
            self.seq.If(set_cond)(
                var.read_ram_sel(ram_id)
            )
            return

        if ram._id() not in self.buf_id_map:
            ram_id = self.buf_id_count
            self.buf_id_count += 1
            self.buf_id_map[ram._id()] = ram_id
        else:
            ram_id = self.buf_id_map[ram._id()]

        var.read_ram_id_map[ram._id()] = ram_id

        self.seq.If(set_cond)(
            var.read_ram_sel(ram_id)
        )

        ram_cond = (var.read_ram_sel == ram_id)
        renable = vtypes.Ands(self.oready, var.enable, ram_cond)

        d, v = ram.read_rtl(var.addr, port=port, cond=renable)

        d_out = d
        util.add_mux(var.read_data, ram_cond, d_out)

        if (self.dump and
            (self.dump_mode == 'all' or
             self.dump_mode == 'ram' or
             (self.dump_mode == 'selective' and
                 hasattr(ram, 'dump') and ram.dump))):
            self._setup_read_ram_dump(ram, var, renable, d)

    def _setup_read_ram_dump(self, ram, var, read_enable, read_data):
        pipeline_depth = self.pipeline_depth()
        log_pipeline_depth = max(
            int(math.ceil(math.log(max(pipeline_depth, 10), 10))), 1)

        addr_base = (ram.dump_addr_base if hasattr(ram, 'dump_addr_base') else
                     self.dump_base)
        addr_base_char = ('b' if addr_base == 2 else
                          'o' if addr_base == 8 else
                          'd' if addr_base == 10 else
                          'x')
        addr_prefix = ('0b' if addr_base == 2 else
                       '0o' if addr_base == 8 else
                       '  ' if addr_base == 10 else
                       '0x')
        addr_vfmt = ''.join([addr_prefix, '%', addr_base_char])

        data_base = (ram.dump_data_base if hasattr(ram, 'dump_data_base') else
                     self.dump_base)
        data_base_char = ('b' if data_base == 2 else
                          'o' if data_base == 8 else
                          'd' if (data_base == 10 and
                                  (not hasattr(ram, 'point') or ram.point <= 0)) else
                          # 'f' if (data_base == 10 and
                          #        hasattr(ram, 'point') and ram.point > 0) else
                          'g' if (data_base == 10 and
                                  hasattr(ram, 'point') and ram.point > 0) else
                          'x')
        data_prefix = ('0b' if data_base == 2 else
                       '0o' if data_base == 8 else
                       '  ' if data_base == 10 else
                       '0x')
        # if data_base_char == 'f':
        #    point_len = int(math.ceil(ram.point / math.log(10, 2)))
        #    point_len = max(point_len, 8)
        #    total_len = int(math.ceil(ram.datawidth / math.log(10, 2)))
        #    total_len = max(total_len, point_len)
        #    data_vfmt = ''.join([data_prefix, '%',
        #                         '%d.%d' % (total_len + 1, point_len),
        #                         data_base_char])
        # else:
        #    data_vfmt = ''.join([data_prefix, '%', data_base_char])
        data_vfmt = ''.join([data_prefix, '%', data_base_char])

        name = ram.name
        fmt = ''.join(['(', self.name, ' step:%d, ',
                       'read, ', ' ' * (log_pipeline_depth + 2),
                       'age:%d) ', name,
                       '[', addr_vfmt, '] = ', data_vfmt])

        dump_ram_step_name = ('_stream_dump_ram_step_%d_%s' %
                              (self.object_id, name))
        dump_ram_step = self.module.Reg(dump_ram_step_name, 32, initval=0)

        enable = self.seq.Prev(read_enable, 1, cond=self.oready)
        age = dump_ram_step
        addr = self.seq.Prev(var.addr, 1, cond=self.oready)
        if hasattr(ram, 'point') and ram.point > 0:
            data = vtypes.Div(vtypes.SystemTask('itor', read_data),
                              1.0 * (2 ** ram.point))
        elif hasattr(ram, 'point') and ram.point < 0:
            data = vtypes.Times(read_data, 2 ** -ram.point)
        else:
            data = read_data

        self.seq(
            dump_ram_step(0)
        )
        self.seq.If(enable)(
            dump_ram_step.inc()
        )
        self.seq.If(self.dump_enable)(
            dump_ram_step.inc()
        )

        self.seq.If(enable, vtypes.Not(self.dump_mask))(
            vtypes.Display(fmt, dump_ram_step, age, addr, data)
        )

    def _setup_write_ram(self, ram, var, port, set_cond):
        if ram._id() in var.write_ram_id_map:
            ram_id = var.write_ram_id_map[ram._id()]
            self.seq.If(set_cond)(
                var.write_ram_sel(ram_id)
            )
            return

        if ram._id() not in self.buf_id_map:
            ram_id = self.buf_id_count
            self.buf_id_count += 1
            self.buf_id_map[ram._id()] = ram_id
        else:
            ram_id = self.buf_id_map[ram._id()]

        var.write_ram_id_map[ram._id()] = ram_id

        self.seq.If(set_cond)(
            var.write_ram_sel(ram_id)
        )

        ram_cond = (var.write_ram_sel == ram_id)
        wenable = vtypes.Ands(self.oready, var.enable, ram_cond)

        ram.write_rtl(var.addr, var.write_data, port=port, cond=wenable)

        if (self.dump and
            (self.dump_mode == 'all' or
             self.dump_mode == 'ram' or
             (self.dump_mode == 'selective' and
                 hasattr(ram, 'dump') and ram.dump))):
            self._setup_write_ram_dump(ram, var, wenable)

    def _setup_write_ram_dump(self, ram, var, write_enable):
        pipeline_depth = self.pipeline_depth()
        log_pipeline_depth = max(
            int(math.ceil(math.log(max(pipeline_depth, 10), 10))), 1)

        addr_base = (ram.dump_addr_base if hasattr(ram, 'dump_addr_base') else
                     self.dump_base)
        addr_base_char = ('b' if addr_base == 2 else
                          'o' if addr_base == 8 else
                          'd' if addr_base == 10 else
                          'x')
        addr_prefix = ('0b' if addr_base == 2 else
                       '0o' if addr_base == 8 else
                       '  ' if addr_base == 10 else
                       '0x')
        addr_vfmt = ''.join([addr_prefix, '%', addr_base_char])

        data_base = (ram.dump_data_base if hasattr(ram, 'dump_data_base') else
                     self.dump_base)
        data_base_char = ('b' if data_base == 2 else
                          'o' if data_base == 8 else
                          'd' if (data_base == 10 and
                                  (not hasattr(ram, 'point') or ram.point <= 0)) else
                          # 'f' if (data_base == 10 and
                          #        hasattr(ram, 'point') and ram.point > 0) else
                          'g' if (data_base == 10 and
                                  hasattr(ram, 'point') and ram.point > 0) else
                          'x')
        data_prefix = ('0b' if data_base == 2 else
                       '0o' if data_base == 8 else
                       '  ' if data_base == 10 else
                       '0x')
        # if data_base_char == 'f':
        #    point_len = int(math.ceil(ram.point / math.log(10, 2)))
        #    point_len = max(point_len, 8)
        #    total_len = int(math.ceil(ram.datawidth / math.log(10, 2)))
        #    total_len = max(total_len, point_len)
        #    data_vfmt = ''.join([data_prefix, '%',
        #                         '%d.%d' % (total_len + 1, point_len),
        #                         data_base_char])
        # else:
        #    data_vfmt = ''.join([data_prefix, '%', data_base_char])
        data_vfmt = ''.join([data_prefix, '%', data_base_char])

        name = ram.name
        fmt = ''.join(['(', self.name, ' step:%d, ',
                       'write, ', ' ' * (log_pipeline_depth + 1),
                       'age:%d) ', name,
                       '[', addr_vfmt, '] = ', data_vfmt])

        enable = write_enable
        age = self.seq.Prev(self.dump_step, pipeline_depth + 1, cond=self.oready) - 1
        addr = var.addr
        if hasattr(ram, 'point') and ram.point > 0:
            data = vtypes.Div(vtypes.SystemTask('itor', var.write_data),
                              1.0 * (2 ** ram.point))
        elif hasattr(ram, 'point') and ram.point < 0:
            data = vtypes.Times(var.write_data, 2 ** -ram.point)
        else:
            data = var.write_data

        self.seq.If(enable, vtypes.Not(self.dump_mask))(
            vtypes.Display(fmt, self.dump_step, age, addr, data)
        )

    def _setup_read_fifo(self, fifo, var, set_cond):
        if fifo._id() in var.read_fifo_id_map:
            fifo_id = var.read_fifo_id_map[fifo._id()]
            self.seq.If(set_cond)(
                var.read_fifo_sel(fifo_id)
            )
            return

        if fifo._id() not in self.buf_id_map:
            fifo_id = self.buf_id_count
            self.buf_id_count += 1
            self.buf_id_map[fifo._id()] = fifo_id
        else:
            fifo_id = self.buf_id_map[fifo._id()]

        var.read_fifo_id_map[fifo._id()] = fifo_id

        self.seq.If(set_cond)(
            var.read_fifo_sel(fifo_id)
        )

        fifo_cond = (var.read_fifo_sel == fifo_id)
        renable = vtypes.Ands(self.oready, var.enable, fifo_cond)

        d, v, ready = fifo.deq_rtl(cond=renable)

        d_out = d
        util.add_mux(var.read_data, fifo_cond, d_out)
        util.add_disable_cond(var.read_ready, fifo_cond, ready)

        if (self.dump and
            (self.dump_mode == 'all' or
             self.dump_mode == 'fifo' or
             (self.dump_mode == 'selective' and
                 hasattr(fifo, 'dump') and fifo.dump))):
            self._setup_read_fifo_dump(fifo, var, renable, d)

    def _setup_read_fifo_dump(self, fifo, var, deq, read_data):
        pipeline_depth = self.pipeline_depth()
        log_pipeline_depth = max(
            int(math.ceil(math.log(max(pipeline_depth, 10), 10))), 1)

        data_base = (fifo.dump_data_base if hasattr(fifo, 'dump_data_base') else
                     self.dump_base)
        data_base_char = ('b' if data_base == 2 else
                          'o' if data_base == 8 else
                          'd' if (data_base == 10 and
                                  (not hasattr(fifo, 'point') or fifo.point <= 0)) else
                          # 'f' if (data_base == 10 and
                          #        hasattr(fifo, 'point') and fifo.point > 0) else
                          'g' if (data_base == 10 and
                                  hasattr(fifo, 'point') and fifo.point > 0) else
                          'x')
        data_prefix = ('0b' if data_base == 2 else
                       '0o' if data_base == 8 else
                       '  ' if data_base == 10 else
                       '0x')
        # if data_base_char == 'f':
        #    point_len = int(math.ceil(fifo.point / math.log(10, 2)))
        #    point_len = max(point_len, 8)
        #    total_len = int(math.ceil(fifo.datawidth / math.log(10, 2)))
        #    total_len = max(total_len, point_len)
        #    data_vfmt = ''.join([data_prefix, '%',
        #                         '%d.%d' % (total_len + 1, point_len),
        #                         data_base_char])
        # else:
        #    data_vfmt = ''.join([data_prefix, '%', data_base_char])
        data_vfmt = ''.join([data_prefix, '%', data_base_char])

        name = fifo.name
        fmt = ''.join(['(', self.name, ' step:%d, ',
                       'read, ', ' ' * (log_pipeline_depth + 2),
                       'age:%d) ', name,
                       ' = ', data_vfmt])

        dump_fifo_step_name = ('_stream_dump_fifo_step_%d_%s' %
                               (self.object_id, name))
        dump_fifo_step = self.module.Reg(dump_fifo_step_name, 32, initval=0)

        enable = self.seq.Prev(deq, 1, cond=self.oready)
        age = dump_fifo_step
        if hasattr(fifo, 'point') and fifo.point > 0:
            data = vtypes.Div(vtypes.SystemTask('itor', read_data),
                              1.0 * (2 ** fifo.point))
        elif hasattr(fifo, 'point') and fifo.point < 0:
            data = vtypes.Times(read_data, 2 ** -fifo.point)
        else:
            data = read_data

        self.seq(
            dump_fifo_step(0)
        )
        self.seq.If(enable)(
            dump_fifo_step.inc()
        )
        self.seq.If(self.dump_enable)(
            dump_fifo_step.inc()
        )

        self.seq.If(enable, vtypes.Not(self.dump_mask))(
            vtypes.Display(fmt, dump_fifo_step, age, data)
        )

    def _setup_write_fifo(self, fifo, var, set_cond):
        if fifo._id() in var.write_fifo_id_map:
            fifo_id = var.write_fifo_id_map[fifo._id()]
            self.seq.If(set_cond)(
                var.write_fifo_sel(fifo_id)
            )
            return

        if fifo._id() not in self.buf_id_map:
            fifo_id = self.buf_id_count
            self.buf_id_count += 1
            self.buf_id_map[fifo._id()] = fifo_id
        else:
            fifo_id = self.buf_id_map[fifo._id()]

        var.write_fifo_id_map[fifo._id()] = fifo_id

        self.seq.If(set_cond)(
            var.write_fifo_sel(fifo_id)
        )

        fifo_cond = (var.write_fifo_sel == fifo_id)
        wenable = vtypes.Ands(self.oready, var.enable, fifo_cond)
        ack, ready = fifo.enq_rtl(var.write_data, cond=wenable)

        util.add_disable_cond(var.write_ready, fifo_cond, ready)

        if (self.dump and
            (self.dump_mode == 'all' or
             self.dump_mode == 'fifo' or
             (self.dump_mode == 'selective' and
                 hasattr(fifo, 'dump') and fifo.dump))):
            self._setup_write_fifo_dump(fifo, var, wenable)

    def _setup_write_fifo_dump(self, fifo, var, enq):
        pipeline_depth = self.pipeline_depth()
        log_pipeline_depth = max(
            int(math.ceil(math.log(max(pipeline_depth, 10), 10))), 1)

        data_base = (fifo.dump_data_base if hasattr(fifo, 'dump_data_base') else
                     self.dump_base)
        data_base_char = ('b' if data_base == 2 else
                          'o' if data_base == 8 else
                          'd' if (data_base == 10 and
                                  (not hasattr(fifo, 'point') or fifo.point <= 0)) else
                          # 'f' if (data_base == 10 and
                          #        hasattr(fifo, 'point') and fifo.point > 0) else
                          'g' if (data_base == 10 and
                                  hasattr(fifo, 'point') and fifo.point > 0) else
                          'x')
        data_prefix = ('0b' if data_base == 2 else
                       '0o' if data_base == 8 else
                       '  ' if data_base == 10 else
                       '0x')
        # if data_base_char == 'f':
        #    point_len = int(math.ceil(fifo.point / math.log(10, 2)))
        #    point_len = max(point_len, 8)
        #    total_len = int(math.ceil(fifo.datawidth / math.log(10, 2)))
        #    total_len = max(total_len, point_len)
        #    data_vfmt = ''.join([data_prefix, '%',
        #                         '%d.%d' % (total_len + 1, point_len),
        #                         data_base_char])
        # else:
        #    data_vfmt = ''.join([data_prefix, '%', data_base_char])
        data_vfmt = ''.join([data_prefix, '%', data_base_char])

        name = fifo.name
        fmt = ''.join(['(', self.name, ' step:%d, ',
                       'write, ', ' ' * (log_pipeline_depth + 1),
                       'age:%d) ', name,
                       ' = ', data_vfmt])

        enable = var.sink_fifo_enq
        age = self.seq.Prev(self.dump_step, pipeline_depth + 1, cond=self.oready) - 1
        if hasattr(fifo, 'point') and fifo.point > 0:
            data = vtypes.Div(vtypes.SystemTask('itor', var.sink_fifo_wdata),
                              1.0 * (2 ** fifo.point))
        elif hasattr(fifo, 'point') and fifo.point < 0:
            data = vtypes.Times(var.sink_fifo_wdata, 2 ** -fifo.point)
        else:
            data = var.sink_fifo_wdata

        self.seq.If(enable, vtypes.Not(self.dump_mask))(
            vtypes.Display(fmt, self.dump_step, age, data)
        )

    def _make_reduce_reset(self):
        self.reduce_reset = self.source(reduce_reset_name,
                                        datawidth=1, signed=False, no_ctrl=True)

    def _set_flag(self, fsm, prefix='_set_flag'):
        flag = self.module.TmpWire(prefix=prefix)
        flag.assign(fsm.here)
        return flag

    def _implement_stream(self):
        self.implement()
        self.stream_synthesized = True

    def _write_delay(self):
        depth = self.pipeline_depth()
        return depth + self.ram_delay

    def _to_pattern(self, shape, order):
        pattern = []
        for p in order:
            if not isinstance(p, int):
                raise TypeError(
                    "Values of 'order' must be 'int', not %s" % str(type(p)))
            size = shape[p]
            basevalue = 1 if isinstance(size, int) else vtypes.Int(1)
            stride = functools.reduce(lambda x, y: x * y,
                                      shape[p + 1:], basevalue)
            pattern.append((size, stride))
        return tuple(pattern)

    def _prefix(self, name):
        return '%s_%s' % (self.name, name)

    def _dataname(self, name):
        return '%s_data' % self._prefix(name)

    def _collect_substreams(self):
        ret = []

        for sub in self.substreams:
            ret.extend(sub._collect_substreams())

        return ret

    def __getattr__(self, attr):
        f = BaseStream.__getattr__(self, attr)

        if (callable(f) and
            (f.__name__.startswith('Reduce') or
             f.__name__.startswith('Counter') or
             f.__name__.startswith('Pulse') or
             f.__name__.startswith('Producer') or
             f.__name__.startswith('CustomCounter'))):

            if self.reduce_reset is None:
                self._make_reduce_reset()

            @functools.wraps(f)
            def func(*args, **kwargs):
                if 'reset' in kwargs:
                    reset = self.Lor(self.reduce_reset, kwargs['reset'])
                    reset.latency = 0
                else:
                    reset = self.reduce_reset

                kwargs['reset'] = reset
                return f(*args, **kwargs)

            return func

        return f


class Substream(BaseSubstream):

    def __init__(self, module, clock, reset, child, strm):
        self.module = module
        self.clock = clock
        self.reset = reset
        self.reset_delay = 0

        BaseSubstream.__init__(self, child, strm)

    def _implement(self, m, seq, svalid=None, senable=None):
        BaseSubstream._implement(self, m, seq, svalid, senable)

        cond_delay = self.reset_delay - 1
        child_source_busy = seq.Prev(self.strm.source_busy, cond_delay, cond=self.strm.oready)
        cond = _and_vars(senable, self.strm.busy)
        self.child.fsm.seq(self.child.source_busy(child_source_busy), cond=cond)

        # parent to child
        util.add_disable_cond(self.child.is_root, self.strm.busy, 0)
        util.add_disable_cond(self.child.oready, self.strm.busy, self.strm.oready)

        # child to parent
        util.add_disable_cond(self.strm.internal_oready, self.strm.busy,
                              self.child.internal_oready)

    def to_source(self, name, data):
        source_name = self.child._dataname(name)
        BaseSubstream.write(self, source_name, data)

    def to_parameter(self, name, data):
        parameter_name = self.child._dataname(name)
        BaseSubstream.write(self, parameter_name, data)

    def from_sink(self, name):
        sink_name = self.child._dataname(name)
        return BaseSubstream.read(self, sink_name)

    def _collect_substreams(self):
        ret = []
        self.reset_delay = 0
        ret.append(self)
        ret.extend(self.child._collect_substreams())
        for s in ret:
            s.reset_delay += 1 + self.start_stage
        return ret


class SubstreamMultiCycle(BaseSubstreamMultiCycle, Substream):

    def __init__(self, module, clock, reset, child, strm):
        self.module = module
        self.clock = clock
        self.reset = reset
        self.reset_delay = 0

        BaseSubstreamMultiCycle.__init__(self, child, strm)

    def _implement(self, m, seq, svalid=None, senable=None):
        BaseSubstreamMultiCycle._implement(self, m, seq, svalid, senable)

        cond_delay = self.reset_delay - 1
        child_source_busy = seq.Prev(self.strm.source_busy, cond_delay, cond=self.strm.oready)
        cond = _and_vars(senable, self.strm.busy)
        self.child.fsm.seq(self.child.source_busy(child_source_busy), cond=cond)

        # parent to child
        util.add_disable_cond(self.child.is_root, self.strm.busy, 0)
