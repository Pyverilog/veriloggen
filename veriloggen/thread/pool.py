from __future__ import absolute_import
from __future__ import print_function
import os
import sys

import veriloggen.core.vtypes as vtypes
from veriloggen.fsm.fsm import FSM

from .thread import Thread


def to_thread_pool(*threads):
    if not threads:
        raise ValueError('no thread specified.')

    if len(threads) == 1 and isinstance(threads[0], (tuple, list)):
        threads = threads[0]

    return ThreadPool(threads=threads)


class ThreadPool(vtypes.VeriloggenNode):
    __intrinsics__ = {'run': 'run',
                      'join': 'join',
                      'done': 'done',
                      'reset': 'reset',
                      'ret': 'ret'}

    def __init__(self, m=None, name=None, clk=None, rst=None,
                 targ=None, numthreads=None, datawidth=32,
                 threads=None, fsm_as_module=False):

        if threads is not None:
            if not isinstance(threads, (tuple, list)):
                threads = [threads]

            clk = threads[0].clk
            rst = threads[0].rst
            name = threads[0].name
            self.m = threads[0].m
            self.numthreads = len(threads)
            self.threads = list(threads)
            for i, thread in enumerate(self.threads):
                thread.tid = i

        elif (m is not None and name is not None and
              clk is not None and rst is not None and
              targ is not None and numthreads is not None):

            self.m = m
            self.numthreads = numthreads
            self.threads = [Thread(m, '_'.join([name, str(i)]), clk, rst, targ,
                                   datawidth=datawidth, tid=i,
                                   fsm_as_module=fsm_as_module)
                            for i in range(numthreads)]

        else:
            raise ValueError('threads or other options must be specified.')

        self.start = self.m.Reg(
            '_'.join(['', name, 'start']), self.numthreads, initval=0)

    def start(self, tid, *args, **kwargs):
        return self.threads[tid].start(*args, **kwargs)

    def extend(self, tid, fsm, *args, **kwargs):
        return self.threads[tid].extend(fsm, *args, **kwargs)

    def run(self, fsm, tid, *args, **kwargs):
        """ start as a child thread """

        fsm(
            self.start[tid](1)
        )
        fsm.goto_next()

        for thread in self.threads:
            start_cond = self.start[thread.tid]

            if not thread.is_child and thread.end_state is not None:
                raise ValueError('thread %d already started' % thread.tid)

            if thread.fsm is None:
                thread.fsm = FSM(thread.m, thread.name, thread.clk, thread.rst,
                                 as_module=thread.fsm_as_module)

            thread.is_child = True

            if thread.start_state is not None:
                thread.fsm._set_index(thread.start_state)
            else:
                thread.start_state = thread.fsm.current

        fsm_start = fsm.current

        for thread in self.threads:
            start_cond = self.start[thread.tid]

            fsm._set_index(fsm_start)

            thread._synthesize_run_fsm(fsm, args, kwargs, cond=start_cond)

            if thread.end_state is None:
                thread.end_state = thread.fsm.current

        fsm(
            self.start[tid](0)
        )
        fsm.goto_next()

        return 0

    def join(self, fsm, tid):
        """ wait for the completion """

        patterns = []
        for thread in self.threads:
            if thread.end_state is None:
                raise ValueError('thread %d not started' % thread.tid)
            end_flag = (thread.fsm.state == thread.end_state)
            patterns.append(((tid == thread.tid), end_flag))

        patterns.append((None, 0))
        cond = vtypes.PatternMux(*patterns)
        fsm.If(cond).goto_next()

        return 0

    def done(self, fsm, tid):
        """ check whethe the thread is running """

        patterns = []
        for thread in self.threads:
            if thread.end_state is None:
                raise ValueError('thread %d not started' % thread.tid)
            end_flag = (thread.fsm.state == thread.end_state)
            patterns.append(((tid == thread.tid), end_flag))

        patterns.append((None, 0))
        cond = vtypes.PatternMux(*patterns)

        return cond

    def reset(self, fsm, tid):
        """ reset the FSM counter to the initial state """

        for thread in self.threads:
            if thread.end_state is None:
                raise ValueError('thread %d not started' % thread.tid)

        for thread in self.threads:
            reset_flag = vtypes.Land(
                (fsm.state == fsm.current), (tid == thread.tid))

            thread.fsm._set_index(thread.end_state)

            if thread.called is not None:
                thread.fsm.If(reset_flag)(
                    thread.called(0)
                )

            thread.fsm.goto_from(
                thread.end_state, thread.start_state, reset_flag)
            thread.fsm._set_index(thread.start_state)

        return 0

    def ret(self, fsm, tid):
        """ return value """

        patterns = []
        for thread in self.threads:
            if thread.end_state is None:
                raise ValueError('thread %d not started' % thread.tid)
            patterns.append(((tid == thread.tid), thread.return_value))

        patterns.append((None, vtypes.IntX()))
        ret = vtypes.PatternMux(*patterns)

        return ret
