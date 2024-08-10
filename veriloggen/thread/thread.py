from __future__ import absolute_import
from __future__ import print_function

import ast
import inspect
import textwrap
from collections import OrderedDict

import veriloggen.core.vtypes as vtypes
from veriloggen.fsm.fsm import FSM

from . import compiler


def reset():
    compiler._tmp_count = 0


def TmpThread(m, clk, rst, targ, datawidth=32, tid=None,
              fsm_as_module=False):
    name = compiler._tmp_name()
    return Thread(m, name, clk, rst, targ, datawidth, tid, fsm_as_module)


def embed_thread(fsm, func, *args, **kwargs):
    m = fsm.m
    clk = fsm.clk
    rst = fsm.rst
    th = TmpThread(m, clk, rst, func)
    return th._embed_thread(fsm, *args, **kwargs)


class Thread(vtypes.VeriloggenNode):
    __intrinsics__ = {'run': '_intrinsic_run',
                      'join': '_intrinsic_join',
                      'done': '_intrinsic_done',
                      'reset': '_intrinsic_reset',
                      'ret': '_intrinsic_ret'}

    def __init__(self, m, name, clk, rst, targ,
                 datawidth=32, point=16, tid=None, fsm_as_module=False):

        self.m = m
        self.name = name
        self.clk = clk
        self.rst = rst
        self.targ = targ
        self.datawidth = datawidth
        self.point = point
        self.tid = tid
        self.fsm_as_module = fsm_as_module

        self.function_lib = OrderedDict()
        self.intrinsic_functions = OrderedDict()
        self.intrinsic_methods = OrderedDict()

        self.fsm = None
        self.is_child = False
        self.start_state = None
        self.end_state = None
        self.return_value = None
        self.start_frame = None
        self.args_dict = OrderedDict()
        self.vararg_regs = []
        self.vararg_set = False
        self.called = None

    def start(self, *args, **kwargs):
        """ build up a new FSM based on the arguments """

        if self.is_child:
            raise ValueError('already started as a child thread')

        if self.end_state is not None:
            raise ValueError('already started')

        frame = inspect.currentframe()
        self.start_frame = frame.f_back

        self.fsm = FSM(self.m, self.name, self.clk, self.rst,
                       as_module=self.fsm_as_module)

        self.start_state = self.fsm.current
        self._synthesize_start_fsm(args, kwargs)
        self.end_state = self.fsm.current

        return self.fsm

    def extend(self, fsm, *args, **kwargs):
        """ extend a given thread FSM """

        frame = inspect.currentframe()
        self.start_frame = frame.f_back

        self._synthesize_start_fsm(args, kwargs, fsm)

        return fsm

    def _embed_thread(self, fsm, *args, **kwargs):
        """ extend a given thread FSM (for embed_thread func) """

        frame = inspect.currentframe()
        self.start_frame = frame.f_back.f_back

        self._synthesize_start_fsm(args, kwargs, fsm)

        return fsm

    def _intrinsic_run(self, fsm, *args, **kwargs):
        """ start as a child thread """

        if not self.is_child and self.end_state is not None:
            raise ValueError('already started')

        if self.fsm is None:
            self.fsm = FSM(self.m, self.name, self.clk, self.rst,
                           as_module=self.fsm_as_module)

        self.is_child = True

        if self.start_state is not None:
            self.fsm._set_index(self.start_state)
        else:
            self.start_state = self.fsm.current

        self._synthesize_run_fsm(fsm, args, kwargs)

        if self.end_state is None:
            self.end_state = self.fsm.current

        start_flag = (self.fsm.state == self.start_state)

        return start_flag

    def run(self, *args, **kwargs):
        """ start as a child thread """
        raise NotImplementedError()

    def _intrinsic_join(self, fsm):
        """ wait for the completion """

        if self.end_state is None:
            raise ValueError('not started')

        end_flag = (self.fsm.state == self.end_state)
        fsm.If(end_flag).goto_next()

        return 0

    def join(self):
        """ wait for the completion """
        raise NotImplementedError()

    def _intrinsic_done(self, fsm):
        """ check whethe the thread is running """

        if self.end_state is None:
            raise ValueError('not started')

        end_flag = (self.fsm.state == self.end_state)

        return end_flag

    def done(self):
        """ check whethe the thread is running """
        raise NotImplementedError()

    def _intrinsic_reset(self, fsm):
        """ reset the FSM counter to the initial state """

        if self.end_state is None:
            raise ValueError('not started')

        reset_flag = (fsm.state == fsm.current)
        self.fsm._set_index(self.end_state)

        if self.called is not None:

            self.fsm.If(reset_flag)(
                self.called(0)
            )

        self.fsm.goto_from(self.end_state, self.start_state, reset_flag)
        self.fsm._set_index(self.start_state)

        return 0

    def reset(self):
        """ reset the FSM counter to the initial state """
        raise NotImplementedError()

    def _intrinsic_ret(self, fsm):
        """ return value """

        return self.return_value

    def ret(self):
        """ return value """
        raise NotImplementedError()

    # --------------------------------------------------------------------------
    def add_function(self, func):
        name = func.__name__
        if name in self.function_lib:
            raise ValueError(
                'Function {} is already defined'.format(name))
        self.function_lib[name] = func
        return func

    def add_intrinsic_method_prefix(self, obj, prefix):
        funcs = [(name, method) for name, method in inspect.getmembers(obj, inspect.ismethod)
                 if name.startswith(prefix)]
        for name, func in funcs:
            self.add_intrinsic(func, name)

    def add_intrinsic(self, func, name=None):
        if inspect.isfunction(func):
            return self._add_intrinsic_function(func, name)
        if inspect.ismethod(func):
            return self._add_intrinsic_method(func, name)
        raise TypeError("'%s' object is not supported" % str(type(func)))

    def _add_intrinsic_function(self, func, name):
        if name is None:
            name = func.__name__
        if name in self.intrinsic_functions:
            raise ValueError(
                'Intrinsic function {} is already defined'.format(name))
        self.intrinsic_functions[name] = func
        return func

    def _add_intrinsic_method(self, func, name):
        if name is None:
            raise ValueError("'name' must not be None.")
        if name in self.intrinsic_methods:
            raise ValueError(
                'Intrinsic method {} is already defined'.format(name))
        self.intrinsic_methods[name] = func
        return func

    def _synthesize_start_fsm(self, args, kwargs, fsm=None):
        if fsm is None:
            fsm = self.fsm

        functions = self._get_functions()

        cvisitor = compiler.CompileVisitor(self.m, self.name, self.clk, self.rst, fsm,
                                           functions, self.intrinsic_functions,
                                           self.intrinsic_methods,
                                           self.start_frame,
                                           datawidth=self.datawidth, point=self.point)

        text = textwrap.dedent(inspect.getsource(self.targ))
        tree = ast.parse(text).body[0]

        # stack a new scope frame
        cvisitor.pushScope(ftype='call')

        # args -> scope variable (pass by reference)
        args_code = []
        rest_args = []
        for pos, arg in enumerate(args):
            baseobj = tree.args.args[pos]
            argname = (baseobj.id
                       if isinstance(baseobj, ast.Name)  # python 2
                       else baseobj.arg)  # python 3
            cvisitor.scope.addVariable(argname, arg)
            args_code.append(argname)

        # kwargs -> scope variable (pass by reference)
        kwargs_code = []
        for key, val in sorted(kwargs.items(), key=lambda x: x[0]):
            cvisitor.scope.addVariable(key, val)
            kwargs_code.append('{}={}'.format(key, key))

        # call AST
        args_text = ', '.join(args_code + kwargs_code)
        call_code = ''.join([self.targ.__name__, '(', args_text, ')'])
        _call_ast = ast.parse(call_code)

        # start visit
        self.return_value = cvisitor.visit(_call_ast.body[0].value)

        # clean-up jump conditions
        cvisitor.clearBreak()
        cvisitor.clearContinue()
        cvisitor.clearReturn()
        cvisitor.clearReturnVariable()

        # return to the previous scope frame
        cvisitor.popScope()

        return self.return_value

    def _synthesize_run_fsm(self, parent_fsm, args, kwargs, cond=None):
        start_flag = (parent_fsm.state == parent_fsm.current)

        if self.called is None:
            self.called = self.m.Reg(
                '_'.join(['', self.name, 'called']), initval=0)

        if cond is not None:
            self.fsm.If(cond)

        self.fsm.If(start_flag)(
            self.called(1)
        )

        functions = self._get_functions()

        cvisitor = compiler.CompileVisitor(self.m, self.name, self.clk, self.rst, self.fsm,
                                           functions, self.intrinsic_functions,
                                           self.intrinsic_methods,
                                           self.start_frame,
                                           datawidth=self.datawidth)

        text = textwrap.dedent(inspect.getsource(self.targ))
        tree = ast.parse(text).body[0]

        # stack a new scope frame
        cvisitor.pushScope(ftype='call')

        used_args = []

        # args
        args_code = []
        for pos, arginfo in enumerate(tree.args.args):
            argname = (arginfo.id
                       if isinstance(arginfo, ast.Name)  # python 2
                       else arginfo.arg)  # python 3

            # actual values can be assigned later in default value section
            args_code.append(argname)

            # regular args
            if pos < len(args):
                arg = args[pos]
                used_args.append(argname)

                if isinstance(arg, vtypes.numerical_types):  # pass by value
                    if argname not in self.args_dict:
                        name = compiler._tmp_name(
                            '_'.join(['', self.name, argname]))
                        v = self.m.Reg(name, self.datawidth,
                                       initval=0, signed=True)
                        cvisitor.scope.addVariable(argname, v)
                        self.args_dict[argname] = v
                    else:
                        v = self.args_dict[argname]

                    # binding
                    if cond is not None:
                        self.fsm.If(cond)

                    self.fsm.If(start_flag)(
                        v(arg)
                    )

                else:  # pass by reference
                    if argname not in self.args_dict:
                        cvisitor.scope.addVariable(argname, arg)
                        self.args_dict[argname] = arg
                    elif id(self.args_dict[argname]) == id(arg):
                        pass
                    else:
                        raise ValueError(
                            'same object must be passed for non-numeric argument')

        # variable length args
        if tree.args.vararg is None and len(args) > len(tree.args.args):
            raise TypeError('takes %d positional arguments but %d were given' %
                            (len(tree.args.args), len(args)))

        if tree.args.vararg is not None and not self.vararg_set:
            baseobj = tree.args.vararg
            varargname = (baseobj.id
                          if isinstance(baseobj, ast.Name)  # python 2
                          else baseobj.arg)  # python 3
            cvisitor.scope.addVariable(varargname, self.vararg_regs)

        if len(args) > len(tree.args.args):
            used_args.append(varargname)
            raise ValueError(
                'variable length argument is not supported in dynamic thread execution')

            #num_vararg_vars = len(args) - len(tree.args.args)
            # if num_vararg_vars > len(self.vararg_regs):
            #    for i in range(num_vararg_vars - len(self.vararg_regs)):
            #        name = compiler._tmp_name('_'.join(['', self.name, varargname]))
            #        v = self.m.Reg(name, self.datawidth, initval=0, signed=True)
            #        self.vararg_regs.append(v)
            #        args_code.append(varargname)
            # for i, arg in enumerate(args[-num_vararg_vars:]):
            #    if not isinstance(arg, vtypes.numerical_types):
            #        raise TypeError('variable length argument support no non-numeric values')
            #    v = self.vararg_regs[i]
            #    # binding
            #    if cond is not None:
            #        self.fsm.If(cond)
            #    self.fsm.If(start_flag)(
            #        v(arg)
            #    )

        # kwargs
        kwargs_code = []
        for argname, arg in sorted(kwargs.items(), key=lambda x: x[0]):
            if argname in used_args:
                raise TypeError(
                    "got multiple values for argument '%s'" % argname)

            used_args.append(argname)

            if isinstance(arg, vtypes.numerical_types):  # pass by value
                if argname not in self.args_dict:
                    name = compiler._tmp_name(
                        '_'.join(['', self.name, argname]))
                    v = self.m.Reg(name, self.datawidth,
                                   initval=0, signed=True)
                    cvisitor.scope.addVariable(argname, v)
                    self.args_dict[argname] = v
                else:
                    v = self.args_dict[argname]

                # binding
                if cond is not None:
                    self.fsm.If(cond)

                self.fsm.If(start_flag)(
                    v(arg)
                )

            else:  # pass by reference
                if argname not in self.args_dict:
                    cvisitor.scope.addVariable(argname, arg)
                    self.args_dict[argname] = arg
                elif id(self.args_dict[argname]) == id(arg):
                    pass
                else:
                    raise ValueError(
                        'same object must be passed for non-numeric argument')

            kwargs_code.append('{}={}'.format(key, key))

        # defaults
        defaults_size = len(tree.args.defaults)
        if defaults_size > 0:
            for arg, val in zip(tree.args.args[-defaults_size:], tree.args.defaults):
                argname = (arg.id if isinstance(arg, ast.Name)  # python 2
                           else arg.arg)  # python 3

                if argname not in self.args_dict:
                    name = compiler._tmp_name(
                        '_'.join(['', self.name, argname]))
                    v = self.m.Reg(name, self.datawidth,
                                   initval=0, signed=True)
                    cvisitor.scope.addVariable(argname, v)
                    self.args_dict[argname] = v
                else:
                    v = self.args_dict[argname]

                if argname not in used_args:
                    right = cvisitor.visit(val)

                    # binding
                    if cond is not None:
                        self.fsm.If(cond)

                    self.fsm.If(start_flag)(
                        v(right)
                    )

        c = start_flag
        if cond is not None:
            c = vtypes.Land(c, cond)

        self.fsm.goto_from(self.start_state, self.start_state + 1, c)
        self.fsm._set_index(self.start_state + 1)

        parent_fsm.goto_next()

        # if already synthesized
        if self.end_state is not None:
            return self.return_value

        # call AST
        args_text = ', '.join(args_code + kwargs_code)
        call_code = ''.join([self.targ.__name__, '(', args_text, ')'])
        _call_ast = ast.parse(call_code)

        # start visit
        self.return_value = cvisitor.visit(_call_ast.body[0].value)

        # clean-up jump conditions
        cvisitor.clearBreak()
        cvisitor.clearContinue()
        cvisitor.clearReturn()
        cvisitor.clearReturnVariable()

        # return to the previous scope frame
        cvisitor.popScope()

        return self.return_value

    def _get_functions(self):
        codes = []

        for func_name, func in self.function_lib.items():
            codes.append(textwrap.dedent(inspect.getsource(func)))

        if self.targ.__name__ not in self.function_lib:
            codes.append(textwrap.dedent(inspect.getsource(self.targ)))

        text = '\n'.join(codes)
        _ast = ast.parse(text)

        functionvisitor = compiler.FunctionVisitor()
        functionvisitor.visit(_ast)
        functions = functionvisitor.getFunctions()

        return functions
