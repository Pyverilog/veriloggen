from __future__ import absolute_import
from __future__ import print_function

import functools
import inspect
from collections import OrderedDict

import veriloggen.core.vtypes as vtypes
import veriloggen.types.util as util
from veriloggen.seq.seq import Seq


__intrinsics__ = {'intrinsic': 'intrinsic_intrinsic',
                  'statement': 'intrinsic_statement',
                  'subst': 'intrinsic_subst',
                  'display': 'intrinsic_display',
                  'write': 'intrinsic_write',
                  'finish': 'intrinsic_finish',
                  'signed': 'intrinsic_signed',
                  'embedded_code': 'intrinsic_embedded_code',
                  'embedded_numeric': 'intrinsic_embedded_numeric',
                  'set_parallel': 'intrinsic_set_parallel',
                  'unset_parallel': 'intrinsic_unset_parallel'}


def intrinsic_intrinsic(fsm, func, *args, **kwargs):
    """ function call as an intrinsic """
    return func(fsm, *args, **kwargs)


def intrinsic(func, *args, **kwargs):
    return func(*args, **kwargs)


class _verilog_meta(type):
    """ metaclass for verilog operator intrinsics """

    __verilog_classes__ = dict(inspect.getmembers(vtypes))
    __intrinsics__ = dict([(key, key) for key in __verilog_classes__.keys()])

    def __getattr__(self, key):
        if key in self.__verilog_classes__:
            cls = self.__verilog_classes__[key]

            @functools.wraps(cls)
            def wrapper(fsm, *args, **kwargs):
                return cls(*args, **kwargs)
            return wrapper

        raise NameError("name '%s' is not defined" % key)


_verilog = _verilog_meta('verilog', (object,),
                         {'__doc__': _verilog_meta.__doc__})


class verilog(_verilog):
    """ verilog operator intrinsics """
    pass


# for SingleStatement and EmbeddedCode
def intrinsic_statement(fsm, *values):
    for value in values:
        fsm(
            value
        )
    fsm.goto_next()


def statement(*values):
    for value in values:
        eval(value)


def intrinsic_subst(fsm, dst, src):
    intrinsic_statement(fsm, vtypes.Subst(dst, src))


def subst(dst, src):
    raise NotImplementedError("Only the intrinsic function 'intrinsic_subst' is supported.")


def intrinsic_display(fsm, *args):
    intrinsic_statement(fsm, vtypes.Display(*args))


def display(*args):
    print(*args)


def intrinsic_write(fsm, *args):
    intrinsic_statement(fsm, vtypes.Write(*args))


def write(*args):
    raise NotImplementedError("Only the intrinsic function 'intrinsic_write' is supported.")


def intrinsic_finish(fsm):
    intrinsic_statement(fsm, vtypes.Finish())


def finish():
    exit()


def intrinsic_signed(fsm, value):
    return vtypes.Signed(value)


def signed(value):
    return value


def intrinsic_embedded_code(fsm, *codes):
    codes = [code.value if isinstance(code, vtypes.Str) else code
             for code in codes]
    code = '\n'.join(codes)
    intrinsic_statement(fsm, vtypes.EmbeddedCode(code))


def embedded_code(*codes):
    raise NotImplementedError("Only the intrinsic function 'intrinsic_embedded_code' is supported.")


def intrinsic_embedded_numeric(fsm, code):
    return vtypes.EmbeddedNumeric(code)


def embedded_numeric(code):
    return vtypes.EmbeddedNumeric(code)


# parallel subst
def intrinsic_set_parallel(fsm):
    fsm.parallel = True


def set_parallel():
    raise NotImplementedError("Only the intrinsic function 'intrinsic_set_parallel' is supported.")


def intrinsic_unset_parallel(fsm):
    fsm.parallel = False
    fsm.goto_next()


def unset_parallel():
    raise NotImplementedError("Only the intrinsic function 'intrinsic_unset_parallel' is supported.")


def Lock(m, name, clk, rst, width=32):
    """ alias of Mutex class """
    return Mutex(m, name, clk, rst, width)


class Mutex(object):
    __intrinsics__ = {'lock': '_intrinsic_lock',
                      'try_lock': '_intrinsic_try_lock',
                      'unlock': '_intrinsic_unlock',
                      'acquire': '_intrinsic_acquire',
                      'release': '_intrinsic_release'}

    def __init__(self, m, name, clk, rst, width=32):

        self.m = m
        self.name = name
        self.clk = clk
        self.rst = rst
        self.width = width

        self.seq = Seq(self.m, self.name, self.clk, self.rst)

        self.lock_reg = self.m.Reg(
            '_'.join(['', self.name, 'lock_reg']), initval=0)
        self.lock_id = self.m.Reg(
            '_'.join(['', self.name, 'lock_id']), self.width, initval=0)

        self.id_map = OrderedDict()
        self.id_map_count = 0

    def _intrinsic_lock(self, fsm):
        name = fsm.name
        new_lock_id = self._get_id(name)

        if new_lock_id > 2 ** self.width - 1:
            raise ValueError('too many lock IDs')

        # try
        try_state = fsm.current

        state_cond = fsm.state == fsm.current
        try_cond = vtypes.Not(self.lock_reg)
        fsm_cond = vtypes.Ors(try_cond, self.lock_id == new_lock_id)

        self.seq.If(state_cond, try_cond)(
            self.lock_reg(1),
            self.lock_id(new_lock_id)
        )

        fsm.If(fsm_cond).goto_next()

        # verify
        cond = vtypes.Ands(self.lock_reg, self.lock_id == new_lock_id)
        fsm.If(vtypes.Not(cond)).goto(try_state)  # try again
        fsm.If(cond).goto_next()  # OK

        return 1

    def lock(self):
        raise NotImplementedError()

    def _intrinsic_try_lock(self, fsm):
        name = fsm.name
        new_lock_id = self._get_id(name)

        if new_lock_id > 2 ** self.width - 1:
            raise ValueError('too many lock IDs')

        # try
        try_state = fsm.current

        state_cond = fsm.state == fsm.current
        try_cond = vtypes.Not(self.lock_reg)

        self.seq.If(state_cond, try_cond)(
            self.lock_reg(1),
            self.lock_id(new_lock_id)
        )

        fsm.goto_next()

        # verify
        cond = vtypes.And(self.lock_reg, self.lock_id == new_lock_id)
        result = self.m.TmpReg(initval=0)
        fsm(
            result(cond)
        )
        fsm.goto_next()

        return result

    def try_lock(self):
        raise NotImplementedError()

    def _intrinsic_unlock(self, fsm):
        name = fsm.name
        new_lock_id = self._get_id(name)

        if new_lock_id > 2 ** self.width - 1:
            raise ValueError('too many lock IDs')

        state_cond = fsm.state == fsm.current

        self.seq.If(state_cond, self.lock_id == new_lock_id)(
            self.lock_reg(0)
        )

        fsm.goto_next()

        return 0

    def unlock(self):
        raise NotImplementedError()

    def _get_id(self, name):
        if name not in self.id_map:
            self.id_map[name] = self.id_map_count
            self.id_map_count += 1

        return self.id_map[name]

    def _intrinsic_acquire(self, fsm, blocking=True):
        """ alias of lock() """

        if not isinstance(blocking, (bool, int)):
            raise TypeError('blocking argument must be bool')

        if blocking:
            return self._intrinsic_lock(fsm)

        return self._intrinsic_try_lock(fsm)

    def acquire(self):
        raise NotImplementedError()

    def _intrinsic_release(self, fsm):
        """ alias of unlock() """

        return self._intrinsic_unlock(fsm)

    def release(self):
        raise NotImplementedError()


class _MutexFunction(object):
    __intrinsics__ = {'lock': '_intrinsic_lock',
                      'try_lock': '_intrinsic_try_lock',
                      'unlock': '_intrinsic_unlock'}

    def _check_mutex(self, fsm):
        if self.mutex is None:
            self.mutex = Mutex(self.m, '_'.join(
                ['', self.name, 'mutex']), self.clk, self.rst)

    def _intrinsic_lock(self, fsm):
        self._check_mutex(fsm)
        return self.mutex._intrinsic_lock(fsm)

    def lock(self):
        raise NotImplementedError()

    def _intrinsic_try_lock(self, fsm):
        self._check_mutex(fsm)
        return self.mutex._intrinsic_try_lock(fsm)

    def try_lock(self):
        raise NotImplementedError()

    def _intrinsic_unlock(self, fsm):
        self._check_mutex(fsm)
        return self.mutex._intrinsic_unlock(fsm)

    def unlock(self):
        raise NotImplementedError()


class Barrier(object):
    __intrinsics__ = {'wait': '_intrinsic_wait'}

    def __init__(self, m, name, clk, rst, numparties):

        self.m = m
        self.name = name
        self.clk = clk
        self.rst = rst
        self.numparties = numparties
        self.width = util.log2(self.numparties) + 1

        self.seq = Seq(self.m, self.name, self.clk, self.rst)

        self.count = self.m.Reg(
            '_'.join(['', self.name, 'barrier_count']), self.width, initval=0)
        self.done = self.m.Reg(
            '_'.join(['', self.name, 'barrier_done']), initval=0)
        self.mutex = Mutex(self.m, '_'.join(
            ['', self.name, 'barrier_mutex']), self.clk, self.rst)

        # reset condition
        self.seq(
            self.done(0)
        )
        self.seq.If(self.count == self.numparties)(
            self.count(0),
            self.done(1)
        )

    def _intrinsic_wait(self, fsm):

        self.mutex._intrinsic_lock(fsm)

        state_cond = fsm.state == fsm.current
        self.seq.If(state_cond)(
            self.count.inc()
        )
        fsm.goto_next()

        self.mutex._intrinsic_unlock(fsm)

        fsm.If(self.done).goto_next()

        return 0

    def wait(self):
        raise NotImplementedError()


class Shared(_MutexFunction):
    __intrinsics__ = {'read': '_intrinsic_read',
                      'write': '_intrinsic_write'} | _MutexFunction.__intrinsics__

    def __init__(self, value):
        self._value = value
        self.seq = None
        self.mutex = None

    @property
    def value(self):
        return self._value

    def _intrinsic_read(self, fsm):
        return self._value

    def read(self):
        raise NotImplementedError()

    def _intrinsic_write(self, fsm, value, *part):
        if self.seq is None:
            m = fsm.m
            clk = fsm.clk
            rst = fsm.rst
            name = self._value.name
            self.seq = Seq(m, '_'.join(['seq', name]), clk, rst)

        cond = fsm.state == fsm.current

        def getval(v, p):
            if isinstance(p, (tuple, list)):
                return v[p[0], p[1]]
            return v[p]

        if len(part) == 0:
            targ = self._value
        elif len(part) == 1:
            targ = getval(self._value, part[0])
        elif len(part) == 2:
            targ = getval(getval(self._value, part[0]), part[1])
        else:
            raise TypeError('unsupported type')

        self.seq.If(cond)(
            targ(value)
        )

        fsm.goto_next()
        return 0

    def write(self, value, *part):
        raise NotImplementedError()

    def _check_mutex(self, fsm):
        if self.mutex is None:
            m = fsm.m
            clk = fsm.clk
            rst = fsm.rst
            name = self._value.name
            self.mutex = Mutex(m, '_'.join(['', name, 'mutex']), clk, rst)
