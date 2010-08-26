from __future__ import division

class expression(object):
    @staticmethod
    def _loadbinops():
        binops=('add','and','div','divmod','floordiv','lshift','mod','mul','or','pow','radd','rand','rdiv','rdivmod','rfloordiv','rlshift','rmod','rmul','ror','rpow','rrshift','rshift','rsub','rtruediv','rxor','sub','truediv','xor','getitem')
        cmpops=('eq','ge','gt','le','lt','ne')
        for i in binops+cmpops:
            setattr(expression,'__'+i+'__',lambda s,o,ii=i:binop(ii,s,box(o)))
    @staticmethod
    def _loadunops():
        unops=('abs','invert','neg','pos')
        for i in unops:
            setattr(expression,'__'+i+'__',lambda s,ii=i:unaryop(ii,s))
    def __coerce__(self,other):
        return (self,box(other))
    def __call__(self,*arg):
        return callexpr(self,arg)
    def __str__(self):
        pass
    def __repr__(self):return str(self)
    def _accept(self,v):
        pass
    def displ(self,v):
        return binop('displ',self,box(v))

expression._loadbinops()
expression._loadunops()

# not overloaded:
# __cmp__
# __class__
# __delattr__
# __new__ 
# __doc__
# __getattribute__
# __getnewargs__
# __setattr__
# __hash__
# __str__
# __init__
# __index__
# basic type constructors (int, float, long)
# hex, oct
# nonzero

class callexpr(expression):
    def __init__(self, fun, args):
        self.__fun=fun
        self.__args=[box(i) for i in args]
    def __str__(self):
        return str(self.__fun)+str(self.__args)
    def _accept(self,v):
        return v.visitCall(self.__fun,self.__args)

class binop(expression):
    def __init__(self, op, left, right):
        self.__op=op
        self.__left=left
        self.__right=right
    def __str__(self):
        return self.__op+'('+str(self.__left)+','+str(self.__right)+')'
    def _accept(self,v):
        return v.visit2(self.__op,self.__left,self.__right)

class unaryop(expression):
    def __init__(self, op, left):
        self.__op=op
        self.__left=left
    def __str__(self):
        return self.__op+'('+str(self.__left)+')'
    def _accept(self,v):
        return v.visit1(self.__op,self.__left)

class variable(expression):
    def __init__(self, n=None):
        self.__name=n if not n is None else '_var_$'+str(id(self))
    def __str__(self):
        return self.__name
    def _accept(self,v):
        return v.visitN(self.__name)
    def name(self):
        return self.__name

class const(expression):
    def __init__(self, v):
        self.__value=v
    def __str__(self):
        return str(self.__value)
    def _accept(self,v):
        return v.visitC(self.__value)

class condition(expression):
    def __init__(self, cond, on_true, on_false):
        self.__cond=box(cond)
        self.__left=box(on_true)
        self.__right=box(on_false)
    def __str__(self):
        return str(self.__cond)+'?'+str(self.__left)+':'+str(self.__right)
    def _accept(self,v):
        return v.visitIf(self.__cond,self.__left,self.__right)

class extern(expression):
    def __init__(self, name, return_type, types):
        self.__name      = name
        self.__return_ty = return_type
        self.__types     = types
    def __str__(self):
        return 'extern '+str(self.__return_ty)+' '+self.__name+'('+str(self.__types)+')'
    def _accept(self,v):
        return v.visitExtern(self.__name,self.__return_ty,self.__types)

class function(expression):
    def __init__(self, name, vars, types, expr):
        self.__name      = name
        self.__var_types = zip(vars,types)
        self.__vars      = vars
        self.__types     = types
        self.__expr      = expr
    def __str__(self):
        return 'function '+self.__name+'('+str(self.__var_types)+','+str(self.__expr)+')'
    def _accept(self,v):
        return v.visitFunc(self.__name,self.__vars,self.__types,self.__expr)

class lamb(expression):
    def __init__(self, vars, types, expr):
        self.__var_types = zip(vars,types)
        self.__vars      = vars
        self.__types     = types
        self.__expr      = expr
    def __str__(self):
        return 'lamb('+str(self.__var_types)+','+str(self.__expr)+')'
    def _accept(self,v,fixVarName=None):
        return v.visitLambda(self.__vars,self.__types,self.__expr,fixVarName=fixVarName)
    def lamb_int(self):
        return (self.__var_types,self.__expr)

class fix(expression):
    def __init__(self, var, expr):
        self.__var=var.name()
        self.__expr=expr
    def __str__(self):
        return 'fix('+str(self.__var)+','+str(self.__expr)+')'
    def _accept(self,v):
        return v.visitFix(self.__var,self.__expr)

def box(expr):
    if isinstance(expr,expression):
        return expr
    else:
        return const(expr)

class visitor(object):
    def visitC(self,v):
        pass
    def visitN(self,name):
        pass
    def visit1(self,op,l):
        pass
    def visit2(self,op,l,r):
        pass
    def visitIf(self,cond,left,right):
        pass
    def visitFix(self,varName,expr):
        pass
    def visitExtern(self,name,rt,types):
        pass
    def visitFunc(self,name,vars,types,expr):
        pass
    def visitLambda(self,vars,types,expr):
        pass
    def visitCall(self,fun,args):
        pass

class eval_visitor(visitor):
    def __init__(self,vars,ops):
        self.vars=vars
        self.ops=ops
    def new_scope(self,assignments):
        nv=eval_visitor(self.vars.copy(),self.ops)
        for (name,val) in assignments:
            nv.vars[name]=val
        return nv
    def __str__(self):
        return 'scope('+str(self.vars)+','+str(self.ops)+')'
    def visitC(self,v):
        return v
    def visitN(self,name):
        return self.vars[name]
    def visit1(self,op,l):
        return self.ops[op](l._accept(self))
    def visit2(self,op,l,r):
        return self.ops[op](l._accept(self),r._accept(self))
    def visitIf(self,cond,left,right):
        return left._accept(self) if cond._accept(self) else right._accept(self)
    def visitLambda(self,vars,types,expr):
        vars=[v.name() for v in vars]
        return (lambda ev=self,v=vars,ty=types,ex=expr:lambda *args: ex._accept(ev.new_scope(zip(v,(t(a) for (t,a) in zip(ty,args))))))()
    def visitExtern(self,name,rt,types):
        return self.ops['$ext.'+name]
    def visitFunc(self,name,vars,types,expr):
        #imperfect emulation: cannot export function definition
        fun=self.visitLambda(vars,types,expr)
        self.ops['$ext.'+name]=fun
        return fun
    def visitFix(self,varName,expr):
        revisitor=eval_visitor(self.vars.copy(),self.ops)
        revisitor.vars[varName]=lambda *args: expr._accept(revisitor)(*args)
        return revisitor.vars[varName]
    def visitCall(self,fun,args):
        return self.ops['call'](fun._accept(self),(i._accept(self) for i in args))

def __ni(x,y):raise(NotImplementedError())

python_ops={'add':lambda x,y:x + y,
            'and':lambda x,y:x and y,
            'div':lambda x,y:x / y,
            'divmod':lambda x,y:divmod(x, y),
            'floordiv':lambda x,y:x // y,
            'lshift':lambda x,y:x << y,
            'mod':lambda x,y:x % y,
            'mul':lambda x,y:x * y,
            'or':lambda x,y:x or y,
            'pow':lambda x,y:x ** y,
            'rshift':lambda x,y:x >> y,
            'sub':lambda x,y:x - y,
            'truediv':lambda x,y:x / y,
            'xor':lambda x,y:x ^ y,
            
            'radd':lambda y,x:x + y,
            'rand':lambda y,x:x and y,
            'rdiv':lambda y,x:x / y,
            'rdivmod':lambda y,x:divmod(x, y),
            'rfloordiv':lambda y,x:x // y,
            'rlshift':lambda y,x:x << y,
            'rmod':lambda y,x:x % y,
            'rmul':lambda y,x:x * y,
            'ror':lambda y,x:x or y,
            'rpow':lambda y,x:x ** y,
            'rrshift':lambda y,x:x >> y,
            'rsub':lambda y,x:x - y,
            'rtruediv':lambda y,x:x / y,
            'rxor':lambda y,x:x ^ y,

            'getitem':lambda x,y:x[y],
            'call':lambda x,y:x(*y),
            
            'eq':lambda x,y: x == y,
            'ge':lambda x,y: x >= y,
            'gt':lambda x,y: x >  y,
            'le':lambda x,y: x <= y,
            'lt':lambda x,y: x <  y,
            'ne':lambda x,y: x != y,

            'invert':lambda x: ~x,
            'abs':lambda x: abs(x),
            'neg':lambda x: -x,
            'pos':lambda x: +x
            }

def eval(expression, vars, ops=python_ops):
    return expression._accept(eval_visitor(vars,ops))

class type_visitor(object):
    def integer(self,bits): pass
    def real(self,bits): pass
    def pointer(self, type): pass
    def array(self, type, l): pass
    def struct(self, types): pass

class type(object):
    def __call__(self,x):
        return x
    def __str__(self):return 'type'
    def __repr__(self):return str(self)
    def _accept(self,v):
        pass

class integer(type):
    def __init__(self,bits=32):
        self.bits=bits
    def __call__(self,x):
        if self.bits==1: return 1 if x else 0
        return int(x) & ((1 << self.bits) - 1)
    def __str__(self):
        return 'bool_t' if self.bits==1 else 'int'+str(self.bits)+'_t'
    def _accept(self,v):
        return v.integer(self.bits)

class real(type):
    def __init__(self,bits=64):
        self.bits=bits
    def __call__(self,x):
        return float(x)
    def __str__(self):
        return 'float_t' if self.bits==32 else 'double_t' if self.bits==64 else 'real_'+str(self.bits)+'_t'
    def _accept(self,v):
        return v.real(self.bits)

class pointer(type):
    def __init__(self,pointee):
        self.element=pointee
    def __str__(self):
        return str(self.element)+'*'
    def _accept(self,v):
        return v.pointer(self.element)

class array(type):
    def __init__(self,element,l):
        self.element=element
        self.len=l
    def __str__(self):
        return str(self.element)+'['+str(self.len)+'+'
    def _accept(self,v):
        return v.array(self.element,self.len)

class struct(type):
    def __init__(self,types):
        self.types=types
    def __call__(self,xs):
        return [t(x) for (x,t) in zip(xs,self.types)]
    def __str__(self):
        return str(self.types)
    def _accept(self,v):
        return v.struct(self.types)

bool_t  = integer(1)
int8_t  = integer(8)
int32_t = integer(32)
int64_t = integer(64)
float_t = real(32)
double_t = real(64)
cstring = pointer(int8_t)

def _test():
    x=variable('x')
    y=variable('y')
    f=variable('f')
    e=condition(x,on_true=1+x,on_false=x+2)
    print e
    v={'x':0}
    print eval(e,v)
    print eval(f(x,y),{'f':lambda z,w:z+w,'x':1,'y':2})
    
    e=fix(f,lamb([x],[int32_t],condition(x>0,x*f(x-1),1)))
    print e(y)
    e=function('z',[x,y],[int32_t,int32_t],x+y)
    print e(1,2)+extern('z',int32_t,[int32_t,int32_t])(2,3)
    print eval(e(1,2)+extern('z',int32_t,[int32_t,int32_t])(2,3),{'y':7})
