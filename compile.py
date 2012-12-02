# Copyright (C) 2009 Corrado Zoccolo

# This file is part of py_llvm_compile.

# py_llvm_compile is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# py_llvm_compile is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with py_llvm_compile.  If not, see <http://www.gnu.org/licenses/>.

from llvm_w import *
from ast import *

class ast2llvm_type_visitor(type_visitor):
    def integer(self,bits): return Type.int(bits)
    def real(self,bits):
        if not bits in (32,64): raise TypeError('no real type with '+str(bits)+' bits')
        return Type.float() if bits==32 else Type.double()
    def pointer(self, type): return Type.pointer(type._accept(self))
    def array(self, type, l): return Type.array(type._accept(self),l)
    def struct(self, types): return Type.struct([t._accept(self) for t in types])

ast2llvm_tv=ast2llvm_type_visitor()

def ast2llvm_type(ast_type):
    return ast_type._accept(ast2llvm_tv)

def type_1_op(op,llvm_t):
    return llvm_t

def type_2_op(op,llvm_t1,llvm_t2):
    if llvm_t1==None:
        return llvm_t2
    if llvm_t2==None:
        return llvm_t1
    if op in ('eq','ge','gt','le','lt','ne'):
        return Type.int(1)
    if op=='getitem':
        return llvm_type_elem(llvm_t1)
    if op=='displ':
        return llvm_t1
    if op in ('truediv','pow'):
        return Type.double()
    return llvm_type_promote(llvm_t1,llvm_t2)

class type_deduction_visitor(visitor):
    def __init__(self,vars):
        self.vars=vars

    def new_scope(self,assignments):
        nv=type_deduction_visitor(self.vars.copy())
        for (name,val) in assignments:
            nv.vars[name]=val
        return nv

    def visitC(self,v):
        return llvm_type(v.__class__,v)
    def visitN(self,name):
        return self.vars[name]
    def visit1(self,op,l):
        return type_1_op(op,l._accept(self))
    def visit2(self,op,l,r):
        return type_2_op(op,l._accept(self),r._accept(self))
    def visitIf(self,cond,left,right):
        return llvm_type_promote(left._accept(self),right._accept(self))
    def visitExtern(self,name,rt,types):
        ty=[ast2llvm_type(t) for t in types]
        return Type.pointer(Type.function(ast2llvm_type(rt),ty))
    def visitFunc(self,name,vars,types,expr):
        return self.visitLambda(vars,types,expr)
    def visitFix(self,varName,expr):
        ns = self.new_scope([(varName,None)])
        return expr._accept(ns)
    def visitLambda(self,vars,types,expr,fixVarName=None):
        ty=[ast2llvm_type(t) for t in types]
        nv=self.new_scope(zip((v.name() for v in vars),ty))
        return Type.pointer(Type.function(expr._accept(nv),ty))
    def visitCall(self,fun,args):
        ty=fun._accept(self)
        if ty==None:
            return ty
        return llvm_type_apply(ty,*(i._accept(self) for i in args))

def _ra(f): lambda x,y,*o:f(y,x,*o)
def _ni(*o): raise NotImplementedError()

def _llvm_compile(name,expr,type_v,args,types,
                  rt=None,
                  fixVarName=None,
                  internal=False,
                  parent=None):
    if fixVarName!=None:
        type_v = type_v.new_scope([(fixVarName,None)])
    if rt==None:
        rt=expr._accept(type_v)
    fsig=Type.function(rt,types)
    my_fun=llvm_function(fsig,name,str(expr)+' '+str(args)+':'+str([str(t) for t in types]), internal)
    if(my_fun.basic_block_count!=0):
        return my_fun
    for (i,n) in enumerate(args):
        my_fun.args[i]=n
    bb=my_fun.append_basic_block('entry')
    builder=enhanced_builder.new(bb)
    inh_vars=None
    if isinstance(parent,compile_visitor):
        inh_vars=parent.vars
    cv=compile_visitor(my_fun,args,type_v,builder,inherited_vars=inh_vars)
    if fixVarName!=None:
        cv.type_v.vars[fixVarName]=Type.pointer(fsig)
        cv.vars[fixVarName]=my_fun
    res=expr._accept(cv)
    builder.ret(res)
    llvm_opt_function(my_fun)
    return my_fun

class compile_visitor(visitor):
    def __init__(self,fun,arg_order,type_v,builder,inherited_vars=None):
        self.fun=fun
        self.vars=dict() if inherited_vars==None else inherited_vars.copy()
        self.vars.update( ((n,fun.args[i]) for (i,n) in enumerate(arg_order)) )
        self.type_v=type_v
        self.builder=builder
        self.unops={'abs':builder.abs,
                    'invert':builder.not_,
                    'neg':builder.neg,
                    'pos':lambda v,n:v}

        self.binops={'add':builder.add,
                     'and':builder.and_,
                     'div':builder.div,
                     'divmod':builder.divmod,
                     'floordiv':_ni,
                     'lshift':builder.shl,
                     'mod':builder.mod,
                     'mul':builder.mul,
                     'or':builder.or_,
                     'pow':builder.pow,
                     'radd':builder.add,
                     'rand':builder.and_,
                     'rdiv':_ra(builder.div),
                     'rdivmod':_ra(builder.divmod),
                     'rfloordiv':_ni,
                     'rlshift':_ra(builder.shl),
                     'rmod':_ra(builder.mod),
                     'rmul':builder.mul,
                     'ror':builder.or_,
                     'rpow':_ra(builder.pow),
                     'rrshift':_ra(builder.ashr),
                     'rshift':builder.ashr,
                     'rsub':_ra(builder.sub),
                     'rtruediv':_ra(builder.fdiv),
                     'rxor':builder.xor,
                     'sub':builder.sub,
                     'truediv':builder.fdiv,
                     'xor':builder.xor}
        
        for i in ('eq','ge','gt','le','lt','ne'):
            self.binops[i]=lambda x,y,n,ii=i:builder.cmp(ii,x,y,n)

    def visitC(self,v):
        return llvm_rt_value(self.type_v.visitC(v),v)

    def visitN(self,name):
        return self.vars[name]

    def visit1(self,op,l):
        val=l._accept(self)
        return self.unops[op](val,'$'+op)

    def visit2(self,op,l,r):
        if not op in ('getitem','displ'):
            tv=self.type_v
            if op in ('eq','ge','gt','le','lt','ne'):
                dest_type=llvm_type_promote(l._accept(tv),r._accept(tv))
            else:
                dest_type=type_2_op(op,l._accept(tv),r._accept(tv))
            l_=l._accept(self)
            l_=self.builder.coerce(dest_type,l_,'('+str(dest_type)+')'+l_.name)
            r_=r._accept(self)
            r_=self.builder.coerce(dest_type,r_,'('+str(dest_type)+')'+r_.name)
            return self.binops[op](l_,r_,'$'+op)
        if op in ('getitem','displ'):
            tv=self.type_v
            dest_type=type_2_op(op,l._accept(tv),r._accept(tv))
            l_=l._accept(self)
            r_=r._accept(self)
            r_=self.builder.coerce(Type.int(),r_,'(int)'+r_.name)
            a_=self.builder.gep(l_,(r_,),'address')
            return self.builder.load(a_,'value') if op=='getitem' else a_
        raise NotImplementedError()

    def visitIf(self,cond,left,right):
        dest_type=llvm_type_promote(left._accept(self.type_v),right._accept(self.type_v))
        res=cond._accept(self)
        res=self.builder.coerce(Type.int(1),res,'(bool)'+res.name)
        then_br = self.fun.append_basic_block('cond_true')
        else_br = self.fun.append_basic_block('cond_false')
        merge_bl = self.fun.append_basic_block('merge')
        self.builder.cbranch(res, then_br, else_br)
        self.builder.position_at_end(then_br)
        l_=left._accept(self)
        l_=self.builder.coerce(dest_type,l_,'('+str(dest_type)+')'+l_.name)
        self.builder.branch(merge_bl)
        then_br=self.builder.block

        self.builder.position_at_end(else_br)
        r_=right._accept(self)
        r_=self.builder.coerce(dest_type,r_,'('+str(dest_type)+')'+r_.name)
        self.builder.branch(merge_bl)
        else_br=self.builder.block

        self.builder.position_at_end(merge_bl)
        ph=self.builder.phi(dest_type,'$if')
        ph.add_incoming(l_,then_br)
        ph.add_incoming(r_,else_br)
        return ph

    def visitFix(self,varName,expr):
        return expr._accept(self,fixVarName=varName)

    def visitExtern(self,name,rt,types):
        ty=[ast2llvm_type(t) for t in types]
        fsig=Type.function(ast2llvm_type(rt),ty)
        return llvm_get_or_insert_function(fsig,name)
        
    def visitFunc(self,name,vars,types,expr):
        ty=[ast2llvm_type(t) for t in types]
        vars=[n.name() for n in vars]
        return _llvm_compile(name,expr,self.type_v.new_scope(zip(vars,ty)),vars,ty,
                             fixVarName=name)
        
    def visitLambda(self,vars,types,expr,fixVarName=None):
        name='lambda_$'
        ty=[ast2llvm_type(t) for t in types]
        vars=[n.name() for n in vars]
        return _llvm_compile(name,expr,self.type_v.new_scope(zip(vars,ty)),vars,ty,
                             fixVarName=fixVarName, internal=True, parent=self)

    def visitCall(self,fun,args):
        llvm_fun=fun._accept(self)
        a=[self.builder.coerce(form,act._accept(self),'(argcast)') for (form,act) in zip(llvm_type_fun(llvm_fun.type).args,args)]
        return self.builder.call(llvm_fun,a)

def llvm_compile(expr, var_types):
    vt=[i for i in var_types.iteritems()]
    arg_pack_t=[ast2llvm_type(t) for (n,t) in vt]
    arg_order=[n for (n,t) in vt]
    tv=type_deduction_visitor( dict( zip(arg_order,arg_pack_t) ) )
    rt=expr._accept(tv)
    fun_name='fun_$'
    my_fun=_llvm_compile(fun_name, expr, tv, arg_order, arg_pack_t, internal=True)
    return llvm_compiled_fun(my_fun, zip(arg_pack_t,arg_order), rt)

def llvm_compile_ordered(expr, var_types):
    arg_pack_t=[ast2llvm_type(t) for (n,t) in var_types]
    arg_order=[n for (n,t) in var_types]
    tv=type_deduction_visitor( dict( zip(arg_order,arg_pack_t) ) )
    rt=expr._accept(tv)
    fun_name='fun_$'
    my_fun=_llvm_compile(fun_name, expr, tv, arg_order, arg_pack_t, internal=True)
    return llvm_compiled_ordered_fun(my_fun, arg_pack_t, rt)

def llvm_compile_closed(expr,name='fun_$'):
    tv=type_deduction_visitor(dict())
    rt=expr._accept(tv)
    my_fun=_llvm_compile(name, expr, tv, [], [], internal=True)
    return llvm_compiled_funptr(my_fun)

def _test0():
    x=variable('x')
    e=condition(x,1+x,x**2)
    print e
    v={'x':int32_t}
    compiled=llvm_compile(e,v)
    llvm_dump_module()
    print compiled(x=2)

def _test0_1():
    x=variable('x')
    e=condition(x,1+x,x**2)
    compiled=llvm_compile_ordered(e,[('x',int32_t)])
    llvm_dump_module()
    print compiled(2)

def _test1():
    x=variable('x')
    f=variable('f')
    fact=extern('fact',int32_t,[int32_t])
    print fact
    fact=function('fact',[x],[int32_t],condition(x>0,x*fact(x-1),1))
    print fact
    compiled=llvm_compile(fact(10),{})
    llvm_dump_module()
    print compiled()

def _test1_0():
    x=variable('x')
    f=variable('f')
    fact=extern('fact',int32_t,[int32_t])
    print fact
    fact=function('fact',[x],[int32_t],condition(x>0,x*fact(x-1),1))
    print fact
    compiled=llvm_compile_closed(fact(10),"z10")
    llvm_dump_module()
    print compiled
    print compiled()

def _test1_1():
    x=variable('x')
    f=variable('f')
    fact=fix(f,lamb([x],[int32_t],condition(x>0,x*f(x-1),1)))
    print fact
    compiled=llvm_compile(fact(10),{})
    llvm_dump_module()
    print compiled()

def _test1_2():
    x=variable('x')
    f=variable('f')
    fact=fix(f,lamb([x],[int32_t],condition(x>0,x*f(x-1),1)))
    print fact
    compiled=llvm_compile_ordered(fact(x),[('x',int32_t)])
    llvm_dump_module()
    print compiled(10)

def _test2():
    x=variable('x')
    y=variable('y')
    f=variable('f')
    cos=extern('cos',double_t,[double_t])
    sin=extern('sin',double_t,[double_t])
    compiled=llvm_compile(cos(x)**2+sin(x)**2,{'x':double_t})
    llvm_dump_module()
    print compiled(x=0.5)

def _test2_1():
    x=variable('x')
    y=variable('y')
    f=variable('f')
    cos=extern('cos',double_t,[double_t])
    sin=extern('sin',double_t,[double_t])
    compiled=llvm_compile_ordered(cos(x)**2+sin(x)**2,[('x',double_t)])
    llvm_dump_module()
    print compiled(0.5)
    
def _test3():
    system=extern('system',int32_t,[cstring])
    x=variable('x')
    do_system=llvm_compile(system('echo 1'),{})
    llvm_dump_module()
    do_system()

def _test3_0():
    system=extern('system',int32_t,[cstring])
    x=variable('x')
    do_system=llvm_compile_closed(system('echo 1'),'invk_system')
    llvm_dump_module()
    do_system()

def _test4():
    system=extern('system',int32_t,[cstring])
    x=variable('x')
    do_system=llvm_compile(system(x),{'x':cstring})
    llvm_dump_module()
    do_system(x='echo 1')

def _test4_1():
    system=extern('system',int32_t,[cstring])
    x=variable('x')
    do_system=llvm_compile_ordered(system(x),[('x',cstring)])
    llvm_dump_module()
    do_system('echo 1')

def _test5():
    strchr=extern('strchr',cstring,[cstring,int32_t])
    x=variable('x')
    y=variable('y')
    call=llvm_compile(strchr(x,y),{'x':cstring,'y':int32_t})
    llvm_dump_module()
    print call(x='echo 1',y=ord('1'))

def _test5_1():
    strchr=extern('strchr',cstring,[cstring,int32_t])
    x=variable('x')
    y=variable('y')
    call=llvm_compile_ordered(strchr(x,y),[('x',cstring),('y',int32_t)])
    llvm_dump_module()
    print call('echo 1',ord('1'))

def _test6():
    system=extern('system',int32_t,[cstring])
    do_system=llvm_compile(system,{})()
    do_system('echo 1')
    llvm_dump_module()

def _test7():
    one=function('one',
                 [],
                 [],
                 box(1))
    t=llvm_compile(one(),{})
    print t() # generates code
    t=llvm_compile(one,{})
    z=t()
    llvm_dump_module()
    return z()

def _test8():
    ssp=extern('sparse_scal_prod', double_t, [double_t,
                                              int32_t,pointer(int32_t),pointer(double_t),
                                              int32_t,pointer(int32_t),pointer(double_t)])
    acc=variable('acc')
    n0=variable('n0')
    idx0=variable('idx0')
    val0=variable('val0')
    n1=variable('n1')
    idx1=variable('idx1')
    val1=variable('val1')
    
    ssp=function('sparse_scal_prod',
                 [acc,
                  n0,idx0,val0,
                  n1,idx1,val1],
                 [double_t,
                  int32_t,pointer(int32_t),pointer(double_t),
                  int32_t,pointer(int32_t),pointer(double_t)],
                 condition((n0>0) & (n1>0),
                           on_true=(condition
                                    (idx0[0]<idx1[0],ssp(acc,
                                                         n0-1,idx0.displ(1),val0.displ(1),
                                                         n1,idx1,val1),
                                     condition
                                     (idx0[0]>idx1[0],ssp(acc,
                                                          n0,idx0,val0,
                                                          n1-1,idx1.displ(1),val1.displ(1)),
                                      ssp(val0[0]*val1[0],
                                          n0-1,idx0.displ(1),val0.displ(1),
                                          n1-1,idx1.displ(1),val1.displ(1))))
                                    ),
                           on_false=acc))

    z=llvm_compile(ssp,{})()
    llvm_dump_module()
    import ctypes
    v0=(ctypes.ARRAY(ctypes.c_int32,16)(),ctypes.ARRAY(ctypes.c_double,16)())
    v1=(ctypes.ARRAY(ctypes.c_int32,16)(),ctypes.ARRAY(ctypes.c_double,16)())
    print v0,v1
    return z(0.,1,v0[0],v0[1],1,v1[0],v1[1])

def _test8_0():
    ssp=extern('sparse_scal_prod', double_t, [double_t,
                                              int32_t,pointer(int32_t),pointer(double_t),
                                              int32_t,pointer(int32_t),pointer(double_t)])
    acc=variable('acc')
    n0=variable('n0')
    idx0=variable('idx0')
    val0=variable('val0')
    n1=variable('n1')
    idx1=variable('idx1')
    val1=variable('val1')
    
    ssp=function('sparse_scal_prod',
                 [acc,
                  n0,idx0,val0,
                  n1,idx1,val1],
                 [double_t,
                  int32_t,pointer(int32_t),pointer(double_t),
                  int32_t,pointer(int32_t),pointer(double_t)],
                 condition((n0>0) & (n1>0),
                           on_true=(condition
                                    (idx0[0]<idx1[0],ssp(acc,
                                                         n0-1,idx0.displ(1),val0.displ(1),
                                                         n1,idx1,val1),
                                     condition
                                     (idx0[0]>idx1[0],ssp(acc,
                                                          n0,idx0,val0,
                                                          n1-1,idx1.displ(1),val1.displ(1)),
                                      ssp(val0[0]*val1[0],
                                          n0-1,idx0.displ(1),val0.displ(1),
                                          n1-1,idx1.displ(1),val1.displ(1))))
                                    ),
                           on_false=acc))

    t=llvm_compile_closed(ssp,"test")
    z=t()
    llvm_dump_module()

    import ctypes
    v0=[ctypes.ARRAY(ctypes.c_int32,16)(0,1),
        ctypes.ARRAY(ctypes.c_double,16)(0.5,0.5)]
    v1=[ctypes.ARRAY(ctypes.c_int32,16)(1,2),
        ctypes.ARRAY(ctypes.c_double,16)(0.1,1.0)]

    print z(0.,
            2, ctypes.pointer(v0[0]),ctypes.pointer(v0[1]),
            2, ctypes.pointer(v1[0]),ctypes.pointer(v1[1]))

def _test():
    for i in (_test0,_test0_1,
              _test1,_test1_0,_test1_1,_test1_2,
              _test2,_test2_1,
              _test3,_test3_0,
              _test4,_test4_1,
              _test5,_test5_1,
              _test6,_test7,
              _test8,_test8_0):
        print "Starting test:", i
        i()
