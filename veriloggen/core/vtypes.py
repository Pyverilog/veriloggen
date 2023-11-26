from __future__ import absolute_import
from __future__ import print_function
import re

# Object ID counter for object sorting key
global_object_counter = 0

operator_dict = {
    'Uminus': '-', 'Ulnot': '!', 'Unot': '~', 'Uand': '&', 'Unand': '~&',
    'Uor': '|', 'Unor': '~|', 'Uxor': '^', 'Uxnor': '~^',
    'Power': '**', 'Times': '*', 'Divide': '/', 'Mod': '%',
    'Plus': '+', 'Minus': '-',
    'Sll': '<<', 'Srl': '>>', 'Sra': '>>>',
    'LessThan': '<', 'GreaterThan': '>', 'LessEq': '<=', 'GreaterEq': '>=',
    'Eq': '==', 'NotEq': '!=', 'Eql': '===', 'NotEql': '!==',
    'And': '&', 'Xor': '^', 'Xnor': '~^',
    'Or': '|', 'Land': '&&', 'Lor': '||'
}


def op2mark(op):
    if op in operator_dict:
        return operator_dict[op]
    return op


def str_to_signed(s):
    targ = s.replace('_', '')
    match = re.search(r's(.+)', targ)
    if match is not None:
        return True
    return False


def check_int_hex(v):
    if not re.search(r'^[0-9a-fA-FxzXZ]+$', v):
        raise ValueError("Illegal value format '%s' for hex" % v)


def check_int_dec(v):
    if not re.search(r'^[0-9xzXZ]+$', v):
        raise ValueError("Illegal value format '%s' for dec" % v)


def check_int_dec_pure(v):
    if not re.search(r'^[0-9]+$', v):
        raise ValueError("Illegal value format '%s' for dec" % v)


def check_int_oct(v):
    if not re.search(r'^[0-7xzXZ]+$', v):
        raise ValueError("Illegal value format '%s' for oct" % v)


def check_int_bin(v):
    if not re.search(r'^[01xzXZ]+$', v):
        raise ValueError("Illegal value format '%s' for bin" % v)


def str_to_value(s):
    targ = s.replace('_', '')

    match = re.search(r'h(.+)', targ)
    if match is not None:
        try:
            v = int(match.group(1), 16)
        except:
            v = match.group(1)
            check_int_hex(v)
        return v, 16

    match = re.search(r'd(.+)', targ)
    if match is not None:
        try:
            v = int(match.group(1), 10)
        except:
            v = match.group(1)
            check_int_dec(v)
        return v, 10

    match = re.search(r'o(.+)', targ)
    if match is not None:
        try:
            v = int(match.group(1), 8)
        except:
            v = match.group(1)
            check_int_oct(v)
        return v, 8

    match = re.search(r'b(.+)', targ)
    if match is not None:
        try:
            v = int(match.group(1), 2)
        except:
            v = match.group(1)
            check_int_bin(v)
        return v, 2

    try:
        v = int(targ, 10)
    except:
        v = targ
        check_int_dec_pure(v)
    return v, None


def str_to_width(s):
    targ = s.replace('_', '')
    match = re.search(r'(.+)\'h.+', targ)
    if match is not None:
        return int(match.group(1), 10)
    match = re.search(r'(.+)\'d.+', targ)
    if match is not None:
        return int(match.group(1), 10)
    match = re.search(r'(.+)\'o.+', targ)
    if match is not None:
        return int(match.group(1), 10)
    match = re.search(r'(.+)\'b.+', targ)
    if match is not None:
        return int(match.group(1), 10)
    return None


def get_width(v):
    if hasattr(v, 'get_width'):
        return v.get_width()

    w = v.bit_length()
    if isinstance(v, int):
        w += 1

    return w


def get_signed(obj):
    if hasattr(obj, 'get_signed'):
        return obj.get_signed()
    if isinstance(obj, (int, float)):
        return True
    return False


def get_dims(obj):
    if hasattr(obj, 'dims'):
        return obj.dims
    return None


def get_value(obj):
    if hasattr(obj, 'value'):
        return obj.value
    return None


def get_initval(obj):
    if hasattr(obj, 'initval'):
        return obj.initval
    return None


def max_width(left, right):
    if left is None and right is None:
        return None
    if left is None:
        return right
    if right is None:
        return left
    return Mux(left >= right, left, right)


def raw_value(v):
    if isinstance(v, Int):
        return v.value
    if isinstance(v, Float):
        return v.value
    if isinstance(v, Str):
        return v.value
    return v


def to_int(v):
    if isinstance(v, int):
        return v
    if isinstance(v, (bool, float)):
        return int(v)
    if isinstance(v, Int):
        v = v.value
        if isinstance(v, int):
            return v
    raise TypeError('can not convert to int')


def equals(a, b):
    if type(a) != type(b):
        return False

    if isinstance(a, (tuple, list)) and isinstance(b, (tuple, list)):
        for aa, bb in zip(a, b):
            v = equals(aa, bb)
            if not v:
                return False
        return True

    if not isinstance(a, _Numeric) and not isinstance(b, _Numeric):
        return a == b

    if hasattr(a, 'equals'):
        return a.equals(b)

    if hasattr(b, 'equals'):
        return b.equals(a)

    raise False


def _write_subst(obj, value, blk=False, ldelay=None, rdelay=None):
    if ((not hasattr(obj, 'no_write_check') or not obj.no_write_check) and
            hasattr(value, 'to_int')):
        value = value.to_int()
    return Subst(obj, value, blk=blk, ldelay=ldelay, rdelay=rdelay)


class VeriloggenNode(object):
    """ Base class of Veriloggen AST object """
    attr_names = ('object_id',)

    def __init__(self):
        global global_object_counter
        self.object_id = global_object_counter
        global_object_counter += 1

    def equals(self, other):
        if type(self) != type(other):
            return False

        for attr in self.attr_names:
            v = equals(getattr(self, attr), getattr(other, attr))
            if not v:
                return False

        return True

    def __hash__(self):
        return hash((id(self), self.object_id))

    def __eq__(self, other):
        return (id(self), self.object_id) == (id(other), other.object_id)

    def __lt__(self, r):
        raise TypeError('Not allowed operation.')

    def __le__(self, r):
        raise TypeError('Not allowed operation.')

    # def __eq__(self, r):
    #    raise TypeError('Not allowed operation.')

    # def __ne__(self, r):
    #    raise TypeError('Not allowed operation.')

    def __ge__(self, r):
        raise TypeError('Not allowed operation.')

    def __gt__(self, r):
        raise TypeError('Not allowed operation.')

    def __add__(self, r):
        raise TypeError('Not allowed operation.')

    def __sub__(self, r):
        raise TypeError('Not allowed operation.')

    def __pow__(self, r):
        raise TypeError('Not allowed operation.')

    def __mul__(self, r):
        raise TypeError('Not allowed operation.')

    def __div__(self, r):
        raise TypeError('Not allowed operation.')

    def __truediv__(self, r):
        raise TypeError('Not allowed operation.')

    def __floordiv__(self, r):
        raise TypeError('Not allowed operation.')

    def __mod__(self, r):
        raise TypeError('Not allowed operation.')

    def __and__(self, r):
        raise TypeError('Not allowed operation.')

    def __or__(self, r):
        raise TypeError('Not allowed operation.')

    def __xor__(self, r):
        raise TypeError('Not allowed operation.')

    def __lshift__(self, r):
        raise TypeError('Not allowed operation.')

    def __rshift__(self, r):
        raise TypeError('Not allowed operation.')

    def __neg__(self):
        raise TypeError('Not allowed operation.')

    def __pos__(self):
        raise TypeError('Not allowed operation.')

    def __invert__(self):
        raise TypeError('Not allowed operation.')

    def __abs__(self):
        raise TypeError('Not allowed operation.')

    def __getitem__(self, r):
        raise TypeError('Not allowed operation.')


class _Numeric(VeriloggenNode):

    def __init__(self):
        VeriloggenNode.__init__(self)
        self._value = None

    def __hash__(self):
        return hash((id(self), self.object_id))

    def __lt__(self, r):
        return LessThan(self, r)

    def __le__(self, r):
        return LessEq(self, r)

    def __eq__(self, r):
        return Eq(self, r)

    def __ne__(self, r):
        return NotEq(self, r)

    def __ge__(self, r):
        return GreaterEq(self, r)

    def __gt__(self, r):
        return GreaterThan(self, r)

    def __add__(self, r):
        return Plus(self, r)

    def __sub__(self, r):
        return Minus(self, r)

    def __pow__(self, r):
        return Power(self, r)

    def __mul__(self, r):
        return Times(self, r)

    def __div__(self, r):
        return Divide(self, r)

    def __truediv__(self, r):
        return Divide(self, r)

    def __floordiv__(self, r):
        return Divide(self, r)

    def __mod__(self, r):
        return Mod(self, r)

    def __and__(self, r):
        return And(self, r)

    def __or__(self, r):
        return Or(self, r)

    def __xor__(self, r):
        return Xor(self, r)

    def __lshift__(self, r):
        return Sll(self, r)

    def __rshift__(self, r):
        return Srl(self, r)

    def __radd__(self, l):
        return Plus(l, self)

    def __rsub__(self, l):
        return Minus(l, self)

    def __rpow__(self, l):
        return Power(l, self)

    def __rmul__(self, l):
        return Times(l, self)

    def __rdiv__(self, l):
        return Divide(l, self)

    def __rtruediv__(self, l):
        return Divide(l, self)

    def __rfloordiv__(self, l):
        return Divide(l, self)

    def __rmod__(self, l):
        return Mod(l, self)

    def __rand__(self, l):
        return And(l, self)

    def __ror__(self, l):
        return Or(l, self)

    def __rxor__(self, l):
        return Xor(l, self)

    def __rlshift__(self, l):
        return Sll(l, self)

    def __rrshift__(self, l):
        return Srl(l, self)

    def __neg__(self):
        return Uminus(self)

    def __pos__(self):
        return Uplus(self)

    def __invert__(self):
        return Unot(self)

    def __abs__(self):
        return Abs(self)

    def __getitem__(self, r):
        if isinstance(r, slice):
            size = self._len()

            right = r.start
            left = r.stop
            step = r.step

            if isinstance(left, Int):
                left = left.value
            if isinstance(right, Int):
                right = right.value
            if isinstance(step, Int):
                step = step.value

            if right is None:
                right = 0
            elif isinstance(right, int) and right < 0:
                right = size - abs(right)

            if left is None:
                left = size
            elif isinstance(left, int) and left < 0:
                left = size - abs(left)
            left -= 1

            if isinstance(left, int) and left < 0:
                raise ValueError("Illegal slice index: left = %d" % left)

            if step is None:
                return Slice(self, left, right)
            else:
                if not (isinstance(left, int) and
                        isinstance(right, int) and
                        isinstance(step, int)):
                    raise ValueError(
                        "Slice with step is not supported in Verilog Slice.")

                if step == 0:
                    raise ValueError("Illegal slice step: step = %d" % step)

                values = [Pointer(self, i)
                          for i in range(right, left + 1, step)]
                values.reverse()
                return Cat(*values)

        if isinstance(r, int) and r < 0:
            r = self.get_width() - abs(r)

        return Pointer(self, r)

    def sra(self, r):  # shift right arithmetically
        return Sra(self, r)

    def repeat(self, times):
        return Repeat(self, times)

    def slice(self, msb, lsb):
        return Slice(self, msb, lsb)

    def bit_length(self):
        return self.get_width()

    def get_width(self):
        raise TypeError("get_width() is not supported.")

    def get_signed(self):
        if hasattr(self, 'signed') and getattr(self, 'signed'):
            return True
        return False

    def __iter__(self):
        self.iter_size = len(self)
        self.iter_count = 0
        return self

    def __next__(self):
        if self.iter_count >= self.iter_size:
            raise StopIteration()

        ret = Pointer(self, self.iter_count)
        self.iter_count += 1
        return ret

    # for Python2
    def next(self):
        return self.__next__()

    def _len(self):
        return self.get_width()

    def __len__(self):
        ret = self._len()
        if not isinstance(ret, int):
            raise TypeError("Non int length.")
        return ret

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, value):
        self._value = value


class _Variable(_Numeric):

    def __init__(self, width=1, dims=None, signed=False, value=None, initval=None, name=None,
                 raw_width=None, raw_dims=None, module=None):
        _Numeric.__init__(self)
        self.name = name
        self.width = width
        if dims is not None and not isinstance(dims, (tuple, list)):
            dims = tuple([dims])
        self.dims = dims
        self.signed = signed
        self._value = value
        self.initval = initval

        self.raw_width = raw_width  # (MSB, LSB)
        if raw_dims is not None:
            for raw_dim in raw_dims:
                if not isinstance(raw_dim, tuple):
                    raise TypeError('dim must be tuple.')
                if len(raw_dim) != 2:
                    raise TypeError('len of dim must be 2.')
            self.raw_dims = tuple(raw_dims)  # [(L, R), ...]
        else:
            self.raw_dims = None

        self.module = module
        self.subst = []
        self.assign_value = None

    @property
    def shape(self):
        return self.dims

    def write(self, value, blk=False, ldelay=None, rdelay=None):
        return _write_subst(self, value, blk, ldelay, rdelay)

    def read(self):
        return self

    def assign(self, value):
        if self.module is None:
            raise ValueError(
                "Variable '%s' has no parent module information" % self.name)
        return self.module.Assign(self.write(value))

    def connect(self, value):
        if self.module is None:
            raise ValueError(
                "Variable '%s' has no parent module information" % self.name)
        if isinstance(self, Reg):
            wire_self = self.module.TmpWireLike(self)
            wire_self.assign(value)
            self.module.Always()(self(wire_self, blk=True))
        elif isinstance(self, (Wire, Output)):
            self.assign(value)
        else:
            raise TypeError('connect() is not supported')

    def comb(self, value):
        return self.assign(value)

    def reset(self):
        return None

    def get_width(self):
        return self.width

    def get_signed(self):
        return self.signed

    def _add_assign(self, s):
        if self.assign_value is not None:
            raise ValueError('already assigned')
        self.assign_value = s

    def _get_assign(self):
        return self.assign_value

    def _add_subst(self, s):
        self.subst.append(s)

    def _get_subst(self):
        return self.subst

    def _get_module(self):
        return self.module

    def __setattr__(self, attr, value):
        if attr == 'width':
            object.__setattr__(self, 'raw_width', None)
        if attr == 'dims':
            object.__setattr__(self, 'raw_dims', None)
        object.__setattr__(self, attr, value)

    def __str__(self):
        return self.name

    def __call__(self, value, blk=False, ldelay=None, rdelay=None):
        return self.write(value, blk=blk, ldelay=ldelay, rdelay=rdelay)

    def _len(self):
        if self.dims is not None:
            return self.dims[0]

        return self.get_width()


class Input(_Variable):
    pass


class Output(_Variable):
    pass


class Inout(_Variable):
    pass


class Tri(_Variable):
    pass


class Reg(_Variable):

    def assign(self, value):
        raise TypeError("Reg object accept no combinational assignment.")

    def reset(self):
        if self.initval is None:
            return None
        return self.write(self.initval)

    def add(self, r):
        return self.write(self + r)

    def sub(self, r):
        return self.write(self - r)

    def inc(self):
        return self.add(1)

    def dec(self):
        return self.sub(1)


class Wire(_Variable):

    def _add_subst(self, s):
        if len(self.subst) > 0:
            raise ValueError('Wire %s is already assigned.' % self.name)
        self.subst.append(s)


class Integer(_Variable):

    def reset(self):
        if self.initval is None:
            return None
        return self.write(self.initval)

    def add(self, r):
        return self.write(self + r)

    def sub(self, r):
        return self.write(self - r)

    def inc(self):
        return self.add(1)

    def dec(self):
        return self.sub(1)


class Real(_Variable):

    def reset(self):
        if self.initval is None:
            return None
        return self.write(self.initval)

    def add(self, r):
        return self.write(self + r)

    def sub(self, r):
        return self.write(self - r)

    def inc(self):
        return self.add(1)

    def dec(self):
        return self.sub(1)


class Genvar(_Variable):

    def add(self, r):
        return self.write(self + r)

    def sub(self, r):
        return self.write(self - r)

    def inc(self):
        return self.add(1)

    def dec(self):
        return self.sub(1)


# for undetermined identifier
class AnyType(_Variable):
    pass


class _ParameterVariable(_Variable):

    def __init__(self, value, width=None, signed=False, name=None,
                 raw_width=None, module=None):
        if isinstance(value, _ParameterVariable):
            value = value.value
        if value is None:
            raise ValueError('value must not be None.')
        _Variable.__init__(self, width=width, signed=signed, value=value, name=name,
                           raw_width=raw_width, module=module)

    def get_width(self):
        if self.width is None:
            return 32
        return self.width


class Parameter(_ParameterVariable):
    pass


class Localparam(_ParameterVariable):
    pass


class Supply(_ParameterVariable):
    pass


class _Constant(_Numeric):
    attr_names = ('value',)

    def __init__(self, value, width=None, base=None):
        _Numeric.__init__(self)
        self._value = value
        self.width = width
        self.base = base
        self._type_check_value(value)
        self._type_check_width(width)
        self._type_check_base(base)

    def _type_check_value(self, value): pass

    def _type_check_width(self, width): pass

    def _type_check_base(self, base): pass

    def __str__(self):
        return str(self.value)

    def get_width(self):
        if self.width is None:
            return 32
        return self.width

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, value):
        raise ValueError('setter is not supported.')


class Int(_Constant):

    def __init__(self, value, width=None, base=None, signed=False, is_raw_value=False):
        _Constant.__init__(self, value, width, base)
        if is_raw_value:
            if width is None:
                raise ValueError(
                    'width is required when is_raw_value is enabled.')
            if base is None:
                raise ValueError(
                    'base is required when is_raw_value is enabled.')
            self._value = value
            self.width = width
            self.base = base
            self.signed = signed
        elif isinstance(value, int):
            self._value = value
            self.width = width
            self.base = base
            self.signed = signed if value >= 0 else value < 0
        else:
            self._value, self.base = str_to_value(value)
            if base is not None:
                self.base = base
            if not isinstance(self.value, int):
                if self.base is None:
                    check_int_dec_pure(self.value)
                elif self.base == 16:
                    check_int_hex(self.value)
                elif self.base == 10:
                    check_int_dec(self.value)
                elif self.base == 8:
                    check_int_oct(self.value)
                elif self.base == 2:
                    check_int_bin(self.value)
                else:
                    raise ValueError(
                        "Illegal base number %d for Int." % self.base)
            self.width = str_to_width(value) if width is None else width
            self.signed = str_to_signed(value) if signed == False else signed

    def _type_check_value(self, value):
        if not isinstance(value, (int, str)):
            raise TypeError(
                'value of Int must be int or str, not %s.' % str(type(value)))

    def _type_check_width(self, width):
        if width is None:
            return
        if not isinstance(width, int):
            raise TypeError('width of Int must be int, not %s.' %
                            str(type(width)))

    def _type_check_base(self, base):
        if base is None:
            return
        if not isinstance(base, int):
            raise TypeError('base of Int must be int, not %s.' %
                            str(type(base)))

    def __str__(self):
        value_list = []
        if self.width:
            value_list.append(str(self.width))

        if self.base is None:
            if self.signed:
                value_list.append("'sd")
            elif self.width:
                value_list.append("'d")
            if isinstance(self.value, str):
                value_list.append(self.value)
            else:
                value_list.append(str(self.value))
        elif self.base == 2:
            if self.signed:
                value_list.append("'sb")
            else:
                value_list.append("'b")
            if isinstance(self.value, str):
                value_list.append(self.value)
            else:
                value_list.append(bin(self .value).replace('0b', ''))
        elif self.base == 8:
            if self.signed:
                value_list.append("'so")
            else:
                value_list.append("'o")
            if isinstance(self.value, str):
                value_list.append(self.value)
            else:
                value_list.append(oct(self.value).replace('0o', ''))
        elif self.base == 10:
            if self.signed:
                value_list.append("'sd")
            else:
                value_list.append("'d")
            if isinstance(self.value, str):
                value_list.append(self.value)
            else:
                value_list.append(str(self.value))
        elif self.base == 16:
            if self.signed:
                value_list.append("'sh")
            else:
                value_list.append("'h")
            if isinstance(self.value, str):
                value_list.append(self.value)
            else:
                value_list.append(hex(self.value).replace('0x', ''))
        else:
            raise ValueError("Int.base must be 2, 8, 10, or 16")

        return ''.join(value_list)

    def get_signed(self):
        return self.signed


def IntX(width=None, base=None, signed=False):
    return Int("'hx", width, base, signed)


def IntZ(width=None, base=None, signed=False):
    return Int("'hz", width, base, signed)


class Float(_Constant):

    def __init__(self, value):
        _Constant.__init__(self, value, None, None)
        self._value = value
        self.width = 32

    def _type_check_value(self, value):
        if not isinstance(value, (float, int)):
            raise TypeError(
                'value of Float must be float, not %s.' % str(type(value)))

    def __str__(self):
        return str(self.value)

    def get_signed(self):
        return True


class Str(_Constant):

    def __init__(self, value):
        _Constant.__init__(self, value, None, None)
        self._value = value

    def _type_check_value(self, value):
        if not isinstance(value, str):
            raise TypeError('value of Str must be str, not %s.' %
                            str(type(value)))

    def __str__(self):
        return str(self.value)


class _Operator(_Numeric):

    def __init__(self):
        _Numeric.__init__(self)
        self.signed = False

    def get_signed(self):
        return self.signed


class _BinaryOperator(_Operator):
    attr_names = ('left', 'right')

    def __init__(self, left, right):
        _Operator.__init__(self)
        self._type_check(left, right)
        self.left = left
        self.right = right
        self.signed = get_signed(self.left) and get_signed(self.right)

    def _type_check(self, left, right):
        if not isinstance(left, (_Numeric, bool, int, float, str)):
            raise TypeError(
                'BinaryOperator does not support Type %s' % str(type(left)))
        if not isinstance(right, (_Numeric, bool, int, float, str)):
            raise TypeError(
                'BinaryOperator does not support Type %s' % str(type(right)))

    def _get_module(self):
        if hasattr(self.left, '_get_module'):
            return self.left._get_module()
        if hasattr(self.right, '_get_module'):
            return self.right._get_module()
        return None

    def __str__(self):
        return ''.join(['(', str(self.left), ' ', op2mark(self.__class__.__name__), ' ',
                        str(self.right), ')'])

    def get_width(self):
        left = get_width(self.left)
        right = get_width(self.right)
        return max_width(left, right) + 1

    def get_signed(self):
        return self.signed


class _UnaryOperator(_Operator):
    attr_names = ('right',)

    def __init__(self, right):
        _Operator.__init__(self)
        self._type_check(right)
        self.right = right
        self.signed = get_signed(self.right)

    def _type_check(self, right):
        if not isinstance(right, (_Numeric, bool, int, float, str)):
            raise TypeError(
                'BinaryOperator does not support Type %s' % str(type(right)))

    def _get_module(self):
        if hasattr(self.right, '_get_module'):
            return self.right._get_module()
        return None

    def __str__(self):
        return ''.join(['(', op2mark(self.__class__.__name__), str(self.right), ')'])

    def get_width(self):
        return get_width(self.right)


# for FixedPoint
class _SkipUnaryOperator(_UnaryOperator):
    pass


# class names must be same the ones in pyverilog.vparser.ast
class Power(_BinaryOperator):

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left ** right


class Times(_BinaryOperator):

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left * right

    def get_width(self):
        left = get_width(self.left)
        right = get_width(self.right)
        return left + right


class Divide(_BinaryOperator):

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left // right

    def get_width(self):
        left = get_width(self.left)
        right = get_width(self.right)
        return max_width(left, right)


class Mod(_BinaryOperator):

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left % right

    def get_width(self):
        left = get_width(self.left)
        right = get_width(self.right)
        return max_width(left, right)


class Plus(_BinaryOperator):

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left + right


class Minus(_BinaryOperator):

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left - right


# general name alias
def Add(left, right):
    return Plus(left, right)


def Sub(left, right):
    return Minus(left, right)


def Mul(left, right):
    return Times(left, right)


def Div(left, right):
    return Divide(left, right)


class Sll(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = get_signed(self.left)

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left << right

    def get_width(self):
        left = get_width(self.left)
        right = get_width(self.right)
        return Int(2) ** right + left


class Srl(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left >> right

    def get_width(self):
        left = get_width(self.left)
        return left


class Sra(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = get_signed(self.left)

    @staticmethod
    def op(left, right, lwidth, rwidth):
        sign = left >= 0
        left = abs(left)
        ret = left >> right
        if not sign:
            return -1 * ret
        return ret

    def get_width(self):
        left = get_width(self.left)
        return left


class LessThan(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left < right

    def get_width(self):
        return 1


class GreaterThan(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left > right

    def get_width(self):
        return 1


class LessEq(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left <= right

    def get_width(self):
        return 1


class GreaterEq(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left >= right

    def get_width(self):
        return 1


class Eq(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left == right

    def get_width(self):
        return 1


class NotEq(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left != right

    def get_width(self):
        return 1


class Eql(_BinaryOperator):  # ===

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left == right

    def get_width(self):
        return 1


class NotEql(_BinaryOperator):  # !==

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left != right

    def get_width(self):
        return 1


class And(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left & right

    def get_width(self):
        left = get_width(self.left)
        right = get_width(self.right)
        return max_width(left, right)


class Xor(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left ^ right

    def get_width(self):
        left = get_width(self.left)
        right = get_width(self.right)
        return max_width(left, right)


class Xnor(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        width = max(lwidth, rwidth)
        value = ~(left ^ right)
        mask = 0
        for i in range(width):
            mask = (0x1 << i) | mask
        return mask & value

    def get_width(self):
        left = get_width(self.left)
        right = get_width(self.right)
        return max_width(left, right)


class Or(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        return left | right

    def get_width(self):
        left = get_width(self.left)
        right = get_width(self.right)
        return max_width(left, right)


class Land(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        if left and right:
            return True
        return False

    def get_width(self):
        return 1


class Lor(_BinaryOperator):

    def __init__(self, left, right):
        _BinaryOperator.__init__(self, left, right)
        self.signed = False

    @staticmethod
    def op(left, right, lwidth, rwidth):
        if left or right:
            return True
        return False

    def get_width(self):
        return 1


class Uplus(_UnaryOperator):

    @staticmethod
    def op(right, rwidth):
        return right


class Uminus(_UnaryOperator):

    @staticmethod
    def op(right, rwidth):
        return -right


class Ulnot(_UnaryOperator):

    def __init__(self, right):
        _UnaryOperator.__init__(self, right)
        self.signed = False

    @staticmethod
    def op(right, rwidth):
        return not right

    def get_width(self):
        return 1


class Unot(_UnaryOperator):

    def __init__(self, right):
        _UnaryOperator.__init__(self, right)
        self.signed = False

    @staticmethod
    def op(right, rwidth):
        return ~right


class Uand(_UnaryOperator):

    def __init__(self, right):
        _UnaryOperator.__init__(self, right)
        self.signed = False

    @staticmethod
    def op(right, rwidth):
        for i in range(rwidth):
            v = (right >> i) & 0x1
            if not v:
                return False
        return True

    def get_width(self):
        return 1


class Unand(_UnaryOperator):

    def __init__(self, right):
        _UnaryOperator.__init__(self, right)
        self.signed = False

    @staticmethod
    def op(right, rwidth):
        for i in range(rwidth):
            v = (right >> i) & 0x1
            if not v:
                return True
        return False

    def get_width(self):
        return 1


class Uor(_UnaryOperator):

    def __init__(self, right):
        _UnaryOperator.__init__(self, right)
        self.signed = False

    @staticmethod
    def op(right, rwidth):
        for i in range(rwidth):
            v = (right >> i) & 0x1
            if v:
                return True
        return False

    def get_width(self):
        return 1


class Unor(_UnaryOperator):

    def __init__(self, right):
        _UnaryOperator.__init__(self, right)
        self.signed = False

    @staticmethod
    def op(right, rwidth):
        for i in range(rwidth):
            v = (right >> i) & 0x1
            if v:
                return False
        return True

    def get_width(self):
        return 1


class Uxor(_UnaryOperator):

    def __init__(self, right):
        _UnaryOperator.__init__(self, right)
        self.signed = False

    @staticmethod
    def op(right, rwidth):
        ret = False
        for i in range(rwidth):
            v = (right >> i) & 0x1
            ret = ret ^ v
        return ret

    def get_width(self):
        return 1


class Uxnor(_UnaryOperator):

    def __init__(self, right):
        _UnaryOperator.__init__(self, right)
        self.signed = False

    @staticmethod
    def op(right, rwidth):
        ret = True
        for i in range(rwidth):
            v = (right >> i) & 0x1
            ret = ret ^ v
        return ret

    def get_width(self):
        return 1


# alias
def Not(*args):
    return Ulnot(*args)


def AndList(*args):
    if len(args) == 0:
        raise ValueError("LandList requires at least one argument.")
    if len(args) == 1:
        return args[0]
    left = args[0]
    for right in args[1:]:
        left = Land(left, right)
    return left


def OrList(*args):
    if len(args) == 0:
        raise ValueError("LorList requires at least one argument.")
    if len(args) == 1:
        return args[0]
    left = args[0]
    for right in args[1:]:
        left = Lor(left, right)
    return left


Ands = AndList
Ors = OrList


class _SpecialOperator(_Operator):
    attr_names = ('args', 'kwargs')

    def __init__(self, *args, **kwargs):
        _Operator.__init__(self)
        self.args = args
        self.kwargs = kwargs
        self.signed = False

    def _get_module(self):
        return None


class Pointer(_SpecialOperator):
    attr_names = ('var', 'pos')

    def __init__(self, var, pos):
        _SpecialOperator.__init__(self)
        self.var = var
        self.pos = pos
        self.subst = []
        self.assign_value = None
        self._type_check_var(var)

    def write(self, value, blk=False, ldelay=None, rdelay=None):
        return _write_subst(self, value, blk, ldelay, rdelay)

    def read(self):
        return self

    def get_width(self):
        if isinstance(self.var, _Variable) and self.var.dims is not None:
            return get_width(self.var)

        if isinstance(self.var, Pointer):
            root = self.var
            depth = 1
            while True:
                if not isinstance(root, Pointer):
                    break
                root = root.var
                depth += 1

            if not hasattr(root, 'dims'):
                return 1

            if len(root.dims) >= depth:
                return get_width(root)

            return 1

        return 1

    def assign(self, value):
        module = self._get_module()
        if module is None:
            raise ValueError("This Pointer has no parent module information")
        return module.Assign(self.write(value))

    def _type_check_var(self, var):
        if not isinstance(var, (_Variable, Scope, Pointer)):
            raise TypeError(
                'var of Pointer must be Variable, not %s' % str(type(var)))

    def _add_assign(self, s):
        if self.assign_value is not None:
            raise ValueError('already assigned')
        self.assign_value = s

    def _get_assign(self):
        return self.assign_value

    def _add_subst(self, s):
        self.subst.append(s)

    def _get_subst(self):
        return self.subst

    def _get_module(self):
        if not hasattr(self.var, '_get_module'):
            return None
        return self.var._get_module()

    def __str__(self):
        return ''.join([str(self.var), '[', str(self.pos), ']'])

    def __call__(self, value, blk=False, ldelay=None, rdelay=None):
        return self.write(value, blk=blk, ldelay=ldelay, rdelay=rdelay)

    def _len(self):
        root = self.var
        depth = 1
        while True:
            if not isinstance(root, Pointer):
                break
            root = root.var
            depth += 1

        if not hasattr(root, 'dims'):
            return 1

        if len(root.dims) > depth:
            return root.dims[depth - 1]

        return self.get_width()

    @staticmethod
    def op(var, pos):
        return (var >> pos) & 0x1


class Slice(_SpecialOperator):
    attr_names = ('var', 'msb', 'lsb')

    def __init__(self, var, msb, lsb):
        _SpecialOperator.__init__(self)
        self.var = var
        self.msb = msb
        self.lsb = lsb
        self.subst = []
        self.assign_value = None
        self._type_check_var(var)

    def write(self, value, blk=False, ldelay=None, rdelay=None):
        return _write_subst(self, value, blk, ldelay, rdelay)

    def read(self):
        return self

    def get_width(self):
        return self.msb - self.lsb + 1

    def assign(self, value):
        module = self._get_module()
        if module is None:
            raise ValueError("This Slice has no parent module information")
        return module.Assign(self.write(value))

    def _type_check_var(self, var):
        if not isinstance(var, (_Variable, Scope)):
            raise TypeError(
                'var of Slice must be Variable, not %s' % str(type(var)))

    def _add_assign(self, s):
        if self.assign_value is not None:
            raise ValueError('already assigned')
        self.assign_value = s

    def _get_assign(self):
        return self.assign_value

    def _add_subst(self, s):
        self.subst.append(s)

    def _get_subst(self):
        return self.subst

    def _get_module(self):
        if not hasattr(self.var, '_get_module'):
            return None
        return self.var._get_module()

    def __str__(self):
        return ''.join([str(self.var), '[', str(self.msb), ':', str(self.lsb), ']'])

    def __call__(self, value, blk=False, ldelay=None, rdelay=None):
        return self.write(value, blk=blk, ldelay=ldelay, rdelay=rdelay)

    @staticmethod
    def op(var, msb, lsb):
        mask = 0
        for i in range(msb - lsb + 1):
            mask = (mask << 1) | 0x1
        return (var >> lsb) & mask


class Cat(_SpecialOperator):
    attr_names = ('vars',)

    def __init__(self, *vars):
        _SpecialOperator.__init__(self)
        self.vars = tuple(vars)
        self.assign_value = None
        self.subst = []

    def write(self, value, blk=False, ldelay=None, rdelay=None):
        return _write_subst(self, value, blk, ldelay, rdelay)

    def read(self):
        return self

    def get_width(self):
        values = [get_width(v) for v in self.vars]
        ret = values[0]
        for v in values[1:]:
            ret = ret + v
        return ret

    def assign(self, value):
        module = self._get_module()
        if module is None:
            raise ValueError("This Cat has no parent module information")
        return module.Assign(self.write(value))

    def _add_assign(self, s):
        if self.assign_value is not None:
            raise ValueError('already assigned')
        self.assign_value = s

    def _get_assign(self):
        return self.assign_value

    def _add_subst(self, s):
        self.subst.append(s)

    def _get_subst(self):
        return self.subst

    def _get_module(self):
        for var in self.vars:
            if hasattr(var, '_get_module'):
                return var._get_module()
        return None

    def __str__(self):
        ret = []
        ret.append('{')
        for v in self.vars:
            ret.append(str(v))
            ret.append(', ')
        ret.pop()
        ret.append('}')
        return ''.join(ret)

    def __call__(self, value, blk=False, ldelay=None, rdelay=None):
        return self.write(value, blk=blk, ldelay=ldelay, rdelay=rdelay)

    @staticmethod
    def op(vars, widths):
        ret = 0
        for var, width in zip(vars, widths):
            ret = (ret << width) | var
        return ret


class Repeat(_SpecialOperator):
    attr_names = ('var', 'times')

    def __init__(self, var, times):
        _SpecialOperator.__init__(self)
        self.var = var
        self.times = times

    def get_width(self):
        return get_width(self.var) * self.times

    def __str__(self):
        return ''.join(['{', str(self.times), '{', str(self.var), '}}'])

    @staticmethod
    def op(var, width, times):
        ret = 0
        for i in range(times):
            ret = (ret << width) | var
        return ret


class Cond(_SpecialOperator):

    def __init__(self, condition, true_value, false_value):
        _SpecialOperator.__init__(self)
        self.condition = condition
        self.true_value = true_value
        self.false_value = false_value
        self.signed = get_signed(
            self.true_value) or get_signed(self.false_value)

    def get_width(self):
        t = get_width(self.true_value)
        f = get_width(self.false_value)
        return max_width(t, f)

    def __str__(self):
        return ''.join(['(', str(self.condition), ')?',
                        str(self.true_value), ' : ', str(self.false_value)])

    @staticmethod
    def op(condition, true_value, false_value):
        if condition:
            return true_value
        else:
            return false_value


def Mux(condition, true_value, false_value):
    # return the result immediately if the condition can be resolved now
    if isinstance(condition, (bool, int, float, str, list, tuple)):
        return true_value if condition else false_value
    return Cond(condition, true_value, false_value)


def Complement2(var):
    if isinstance(var, (int, bool, float)):
        return abs(var)

    return Unot(var) + Int(1)


def Abs(var):
    return Mux(Sign(var), Complement2(var), var)


def Sign(var):
    if isinstance(var, (int, bool, float)):
        return var < 0

    return var < Int(0, signed=True)


class Sensitive(VeriloggenNode):

    def __init__(self, name):
        VeriloggenNode.__init__(self)
        self.name = name


class Posedge(Sensitive):
    pass


class Negedge(Sensitive):
    pass


class SensitiveAll(Sensitive):

    def __init__(self):
        Sensitive.__init__(self, 'all')


class Subst(VeriloggenNode):

    def __init__(self, left, right, blk=False, ldelay=None, rdelay=None):
        VeriloggenNode.__init__(self)
        self._type_check_left(left)
        self._type_check_right(right)
        self.left = left
        self.right = right
        self.blk = blk
        self.ldelay = ldelay
        self.rdelay = rdelay
        self.left._add_subst(self)

    def _type_check_left(self, left):
        if not isinstance(left, VeriloggenNode):
            raise TypeError(
                "left must be VeriloggenNode, not '%s'" % str(type(left)))

    def _type_check_right(self, right):
        if not isinstance(right, (VeriloggenNode, int, float, bool, str)):
            raise TypeError(
                "right must be VeriloggenNode, not '%s'" % str(type(right)))

    def overwrite_right(self, right):
        self.right = right

    def __str__(self):
        return ''.join([str(self.left), ' <- ', str(self.right)])


class Always(VeriloggenNode):

    def __init__(self, *sensitivity):
        VeriloggenNode.__init__(self)
        self.sensitivity = tuple(sensitivity)
        self.statement = None

    def set_statement(self, *statement):
        if self.statement is not None:
            raise ValueError("Statement is already assigned.")
        self.statement = tuple(statement)
        return self

    def __call__(self, *statement):
        return self.set_statement(*statement)


class Assign(VeriloggenNode):

    def __init__(self, statement):
        VeriloggenNode.__init__(self)
        self.statement = statement
        statement.left._add_assign(self)

    def overwrite_right(self, v):
        self.statement.overwrite_right(v)


class Initial(VeriloggenNode):

    def __init__(self, *statement):
        VeriloggenNode.__init__(self)
        self.statement = tuple(statement)

    def add(self, *statement):
        if self.statement is None:
            return self.set_statement(*statement)
        self.statement = tuple(self.statement + statement)
        return self


class If(VeriloggenNode):

    def __init__(self, condition):
        VeriloggenNode.__init__(self)
        self.condition = condition
        self.true_statement = None
        self.false_statement = None

        self.root = self
        self.next_call = None

    def set_true_statement(self, *statement):
        self.true_statement = tuple(statement)
        return self.root

    def set_false_statement(self, *statement):
        self.false_statement = tuple(statement)
        return self.root

    def Else(self, *statement):
        if self.next_call is not None:
            return self.next_call.Else(*statement)
        if self.false_statement is None:
            return self.set_false_statement(*statement)
        raise ValueError("False statement is already assigned.")

    def Elif(self, condition):
        next_If = If(condition)
        next_If.root = self.root
        self.Else(next_If)
        self.next_call = next_If
        return self

    def __call__(self, *args):
        if self.next_call is not None:
            return self.next_call(*args)
        if self.true_statement is None:
            return self.set_true_statement(*args)
        if self.false_statement is None:
            return self.set_false_statement(*args)
        raise ValueError(
            "True statement and False statement are already assigned.")


class For(VeriloggenNode):

    def __init__(self, pre, condition, post):
        VeriloggenNode.__init__(self)
        self.pre = pre
        self.condition = condition
        self.post = post
        self.statement = None

    def set_statement(self, *statement):
        self.statement = tuple(statement)
        return self

    def add(self, *statement):
        if self.statement is None:
            return self.set_statement(*statement)
        self.statement = tuple(self.statement + statement)
        return self

    def __call__(self, *args):
        if self.statement is None:
            return self.set_statement(*args)
        raise ValueError("Statement body is already assigned.")


class While(VeriloggenNode):

    def __init__(self, condition):
        VeriloggenNode.__init__(self)
        self.condition = condition
        self.statement = None

    def set_statement(self, *statement):
        self.statement = tuple(statement)
        return self

    def add(self, *statement):
        if self.statement is None:
            return self.set_statement(*statement)
        self.statement = tuple(self.statement + statement)
        return self

    def __call__(self, *args):
        if self.statement is None:
            return self.set_statement(*args)
        raise ValueError("Statement body is already assigned.")


class Case(VeriloggenNode):

    def __init__(self, comp):
        VeriloggenNode.__init__(self)
        self.comp = comp
        self.statement = None
        self.last = False

    def _type_check_statement(self, *statement):
        for s in statement:
            if not isinstance(s, When):
                raise TypeError(
                    "Case statement requires When() object as statement list.")
            if self.last:
                raise ValueError("When() with None condition must be last.")
            if s.condition is None:
                self.last = True

    def set_statement(self, *statement):
        self._type_check_statement(*statement)
        self.statement = tuple(statement)
        return self

    def add(self, *statement):
        if self.statement is None:
            return self.set_statement(*statement)
        self._type_check_statement(*statement)
        self.statement = tuple(self.statement + statement)
        return self

    def __call__(self, *args):
        if self.statement is None:
            return self.set_statement(*args)
        raise ValueError("Case statement list is already assigned.")


class Casex(Case):
    pass


class When(VeriloggenNode):

    def __init__(self, *condition):
        VeriloggenNode.__init__(self)
        self._type_check_condition(*condition)
        self.condition = None if len(condition) == 0 or condition[
            0] is None else tuple(condition)
        self.statement = None

    def _type_check_condition(self, *args):
        if len(args) == 0:
            return
        if len(args) == 1 and args[0] is None:
            return
        for i, a in enumerate(args):
            if a is None:
                raise ValueError(
                    "None condition must not mixed in When() statement.")
            if isinstance(a, (_Numeric, bool, int, float, str)):
                continue
            raise TypeError(
                "Condition must be _Numeric object, not '%s'" % str(type(a)))

    def _type_check_statement(self, *args):
        pass

    def set_statement(self, *statement):
        self._type_check_statement(*statement)
        self.statement = tuple(statement)
        return self

    def add(self, *statement):
        if self.statement is None:
            return self.set_statement(*statement)
        self._type_check_statement(*statement)
        self.statement = tuple(self.statement + statement)
        return self

    def __call__(self, *args):
        if self.statement is None:
            return self.set_statement(*args)
        raise ValueError("Statement body is already assigned.")


def PatternIf(*patterns):
    root = None
    prev = None
    length = len(patterns)

    if len(patterns) == 1 and isinstance(patterns, (tuple, list)):
        patterns = patterns[0]

    for i, (cond, stmt) in enumerate(patterns):
        if not isinstance(stmt, (tuple, list)):
            stmt = tuple([stmt])

        body = If(cond)(stmt) if cond is not None else stmt

        if root is None:
            root = body
        else:
            prev.Else(body)

        prev = body

        if cond is None:
            if i < length - 1:
                raise ValueError("Too many patterns after None condition.")
            break

    return root


def PatternMux(*patterns):
    prev = None

    if len(patterns) == 1 and isinstance(patterns, (tuple, list)):
        patterns = patterns[0]

    for i, (cond, stmt) in enumerate(reversed(patterns)):
        if prev is None and cond is not None:
            raise ValueError('Last pattern requires a None condition.')
        if prev is not None and cond is None:
            raise ValueError('Non-last pattern requires a condition.')
        prev = Mux(cond, stmt, prev) if cond is not None else stmt

    return prev


class ScopeIndex(VeriloggenNode):

    def __init__(self, name, index):
        VeriloggenNode.__init__(self)
        self.name = name
        self.index = index


class Scope(_Numeric):

    def __init__(self, *args):
        _Numeric.__init__(self)
        self.args = tuple(args)
        if not args:
            raise ValueError("Scope requires at least one argument.")

    def get_width(self):
        try:
            w = get_width(self.args[-1])
            return w
        except:
            raise ValueError('could not identify get_width.')


class SystemTask(_Numeric):

    def __init__(self, cmd, *args):
        _Numeric.__init__(self)
        cmd = raw_value(cmd)
        self.cmd = cmd
        self.args = tuple(args)

    def get_width(self):
        if self.cmd == 'signed':
            return get_width(self.args[0])
        raise TypeError("get_width() is not supported.")


def Systask(cmd, *args):
    return SingleStatement(SystemTask(cmd, *args))


# frequently-used system task
def Display(*args):
    return Systask('display', *args)


def Write(*args):
    return Systask('write', *args)


def Finish():
    return Systask('finish')


def Signed(value):
    return SystemTask('signed', value)


class Event(VeriloggenNode):

    def __init__(self, *sensitivity):
        VeriloggenNode.__init__(self)
        self.sensitivity = sensitivity


class Wait(VeriloggenNode):

    def __init__(self, condition):
        VeriloggenNode.__init__(self)
        self.condition = condition
        self.statement = None

    def set_statement(self, *statement):
        if self.statement is not None:
            raise ValueError("Statement is already assigned.")
        self.statement = tuple(statement)
        return self

    def __call__(self, *statement):
        return self.set_statement(*statement)


class Forever(VeriloggenNode):

    def __init__(self, *statement):
        VeriloggenNode.__init__(self)
        self.statement = tuple(statement)


class Delay(VeriloggenNode):

    def __init__(self, value):
        VeriloggenNode.__init__(self)
        self._value = value

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, value):
        raise ValueError('setter is not supported.')


class SingleStatement(VeriloggenNode):

    def __init__(self, statement):
        VeriloggenNode.__init__(self)
        self.statement = statement


class EmbeddedCode(VeriloggenNode):

    def __init__(self, code):
        VeriloggenNode.__init__(self)
        code = raw_value(code)
        self.code = code


class EmbeddedNumeric(EmbeddedCode, _Numeric):

    def __init__(self, code):
        EmbeddedCode.__init__(self, code)


numerical_types = (_Numeric, int, bool, float, str)
