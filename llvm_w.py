import ctypes
import llvm._core as _core  # C wrappers
from llvm import *
from llvm.core import *
from llvm.ee import *
from llvm.passes import *

if not globals().has_key('__loaded'):
    __llvm_module=Module.new('llvm_module')
    __fopt = FunctionPassManager.new(__llvm_module)
    __ee = ExecutionEngine.new(__llvm_module)
    __fopt.add(__ee.target_data)

    __constant_cache={}
    __function_cache={}
    __ctypes_string_cache={}

    for i in (
        PASS_SIMPLIFY_LIB_CALLS,
        PASS_REASSOCIATE,
        PASS_GVN,
        PASS_CFG_SIMPLIFICATION,
        PASS_TAIL_CALL_ELIMINATION,
        PASS_INSTRUCTION_COMBINING,
        ):
        __fopt.add(i)
    __fopt.initialize()
    __loaded=1

def llvm_intrinsic(which,*types): return Function.intrinsic(__llvm_module, which, types)
def llvm_create_global_constant(llvm_v):
    n=str(llvm_v)
    if(__constant_cache.has_key(n)):
        return __constant_cache[n]
    v=__llvm_module.add_global_variable(llvm_v.type,'const_$')
    v.initializer=llvm_v
    v.global_constant=True
    __constant_cache[n]=v
    return v

def llvm_add_function(sig,name): return __llvm_module.add_function(sig,name)
def llvm_get_function(sig,name):
    try: fun=__llvm_module.get_function_named(name)
    except: return None
    if sig!=llvm_type_fun(fun.type): raise TypeError('Wrong signature for function '+name)
    return fun

def llvm_get_or_insert_function(sig,name):
    fun=__llvm_module.get_or_insert_function(sig,name)
    if sig!=llvm_type_fun(fun.type): raise TypeError('Wrong signature for function '+name)
    return fun

def llvm_function(sig, name, key, internal):
    if(__function_cache.has_key(key)):
        return __function_cache[key]
    if internal:
        f=llvm_add_function(sig,name)
        f.linkage=LINKAGE_INTERNAL
    else:
        f=llvm_get_function(sig,name)
        if not f:
            f=llvm_add_function(sig,name)
    __function_cache[key]=f
    return f

def llvm_opt_function(f): return __fopt.run(f)
def llvm_run_function(f,a): return __ee.run_function(f,a)
def llvm_dump_module(): print __llvm_module

def llvm_type(py_t, py_v=None):
    if issubclass(py_t,int):
        return Type.int(32)
    if issubclass(py_t,long):
        return Type.int(64)
    if issubclass(py_t,float):
        return Type.double()
    if issubclass(py_t,str):
        return Type.array(Type.int(8),len(py_v)+1)
    return Type.void()

def llvm_is_int(llvm_t):
    return llvm_t.kind in (TYPE_INTEGER,)

def llvm_is_number(llvm_t):
    return llvm_t.kind in (TYPE_INTEGER,TYPE_FLOAT,TYPE_DOUBLE)

def llvm_is_array(llvm_t):
    return llvm_t.kind in (TYPE_ARRAY,)

def llvm_is_pointer(llvm_t):
    return llvm_t.kind in (TYPE_ARRAY,TYPE_POINTER)

def llvm_type_fun(llvm_t):
    if(llvm_t.kind==TYPE_POINTER):
        llvm_t=llvm_t.pointee
    if(llvm_t.kind!=TYPE_FUNCTION):
        raise TypeError('Not a function')
    return llvm_t

def llvm_type_elem(llvm_st):
    if(llvm_st.kind==TYPE_ARRAY):
        return llvm_st.element
    if(llvm_st.kind==TYPE_POINTER):
        return llvm_st.pointee
    return Type.void()

def llvm_type_promote(llvm_t1,llvm_t2):
    if(llvm_t1==llvm_t2):
        return llvm_t1
    if(llvm_is_int(llvm_t1) and llvm_is_int(llvm_t2)):
        return llvm_t1 if llvm_t1.width>=llvm_t2.width else llvm_t2
    if(llvm_is_number(llvm_t1) and llvm_is_number(llvm_t2)):
        return Type.double()
    if(llvm_is_array(llvm_t1) and llvm_is_array(llvm_t2) and llvm_t1.count==llvm_t2.count):
        return Type.array(llvm_type_promote(llvm_t1.element,llvm_t2.element),llvm_t1.count)
    if(llvm_is_pointer(llvm_t1) and llvm_is_pointer(llvm_t2)):
        return Type.pointer(llvm_type_promote(llvm_type_elem(llvm_t1),llvm_type_elem(llvm_t2)))
    return Type.void()

def llvm_type_apply(llvm_t, *llvm_ts):
    llvm_t=llvm_type_fun(llvm_t)
    if len(llvm_ts)!=llvm_t.arg_count:
        raise TypeError('Wrong number of argument in function call')
    return llvm_t.return_type

def ctypes_type(llvm_t):
    if(llvm_is_int(llvm_t)):
        if llvm_t.width <=32:
            return ctypes.c_int32
        else:
            return ctypes.c_int64
    if(llvm_is_number(llvm_t)):
        return ctypes.c_double
    if(llvm_is_pointer(llvm_t)):
        if(llvm_type_elem(llvm_t)==Type.int(8)):
            return ctypes.c_char_p
        return ctypes.c_void_p
    if(llvm_t==Type.void()):
        return None
    raise TypeError('Cannot convert llvm type '+str(llvm_t)+' to ctypes')

def ctypes_ptr_to_int(ctypes_ptr): return ctypes.cast(ctypes_ptr,ctypes.c_voidp).value

def llvm_string_argument(llvm_t,py_v):
    n=str(py_v)
    if(not __ctypes_string_cache.has_key(n)):
        __ctypes_string_cache[n]=ctypes.c_char_p(n)
    return GenericValue.pointer(llvm_t,ctypes_ptr_to_int(__ctypes_string_cache[n]))
                                        
def llvm_arg_value(llvm_t,py_v):
    if(llvm_is_int(llvm_t)):
        return GenericValue.int_signed(llvm_t,py_v)
    if(llvm_is_number(llvm_t)):
        return GenericValue.real(llvm_t,py_v)
    if(llvm_t==Type.pointer(Type.int(8))):
        return llvm_string_argument(llvm_t,py_v)
    raise NotImplementedError()

def llvm_rt_value(llvm_t,py_v):
    if(llvm_is_int(llvm_t)):
        return Constant.int_signextend(llvm_t,py_v)
    if(llvm_is_number(llvm_t)):
        return Constant.real(llvm_t,py_v)
    if(llvm_t.kind==TYPE_ARRAY and llvm_t.element==Type.int(8)):
        return Constant.stringz(py_v)
    raise NotImplementedError()

def python_value(llvm_t,llvm_v):
    if(llvm_is_int(llvm_t)):
        return llvm_v.as_int_signed()
    if(llvm_is_number(llvm_t)):
        return llvm_v.as_real(llvm_t)
    if(llvm_t==Type.pointer(Type.int(8))):
        p=llvm_v.as_pointer()
        return str(ctypes.string_at(llvm_v.as_pointer())) if p else None
    try:
        ft=llvm_type_fun(llvm_t)
        cproto=ctypes.CFUNCTYPE(ctypes_type(ft.return_type),*(ctypes_type(t) for t in ft.args))
        return cproto(llvm_v.as_pointer())
    except: pass
    raise NotImplementedError()

class enhanced_builder(Builder):
    def __init__(self, ptr):
        return Builder.__init__(self,ptr)

    @staticmethod
    def new(basic_block):
        import llvm._core
        check_is_basic_block(basic_block)
        b = enhanced_builder(llvm._core.LLVMCreateBuilder())
        b.position_at_end(basic_block)
        return b

    def coerce(self,llvm_t,llvm_v,nm):
        if(llvm_t==llvm_v.type):
            return llvm_v
        if(llvm_is_int(llvm_t) and llvm_t.width==1):
            return self.cmp('ne',llvm_v,llvm_rt_value(llvm_v.type,0),nm)
        if(llvm_is_int(llvm_t)):
            if(llvm_is_int(llvm_v.type)):
                if(llvm_v.type.width<=llvm_t.width):
                    return self.sext(llvm_v,llvm_t,nm)
                else:
                    return self.trunc(llvm_v,llvm_t,nm)
            if(llvm_is_number(llvm_v.type)):
                return self.fptosi(llvm_v,llvm_t,nm)
            return llvm_v
        if(llvm_is_number(llvm_t)):
            if(llvm_is_int(llvm_v.type)):
                return self.sitofp(llvm_v,llvm_t,nm)
            if(llvm_is_number(llvm_v.type)):
                return self.fpext(llvm_v,llvm_t,nm)
            return llvm_v
        if(llvm_t.kind==TYPE_POINTER and llvm_v.type.kind==TYPE_ARRAY):
            if isinstance(llvm_v,Constant):
                llvm_v=llvm_create_global_constant(llvm_v)
            zero=llvm_rt_value(Type.int(32),0)
            return self.gep(llvm_v,(zero,zero),nm)
        raise TypeError('Cannot convert '+str(llvm_v.type)+' to '+str(llvm_t))
    
    def abs(self,llvm_v,nm):
        if(llvm_is_int(llvm_v.type)):
            neg_v = self.neg(llvm_v)
            pos = self.icmp(llvm_v,Constant.int(llvm_v.type,0))
            return self.select(pos,llvm_t,neg_v)
        if(llvm_is_number(llvm_v.type)):
            neg_v = self.neg(llvm_v)
            pos = self.icmp(llvm_v,Constant.real(llvm_v.type,0))
            return self.select(pos,llvm_t,neg_v,nm)
        raise NotImplementedError()

    def div(self,llvm_v1,llvm_v2,nm):
        ty=llvm_v1.type
        if(llvm_is_int(ty)):
            return self.sdiv(llvm_v1,llvm_v2)
        if(llvm_is_real(ty)):
            return self.fdiv(llvm_v1,llvm_v2)
        raise NotImplementedError()

    def mod(self,llvm_v1,llvm_v2,nm):
        ty=llvm_v1.type
        if(llvm_is_int(ty)):
            return self.smod(llvm_v1,llvm_v2)
        if(llvm_is_real(ty)):
            return self.fmod(llvm_v1,llvm_v2)
        raise NotImplementedError()
    
    def divmod(self,llvm_v1,llvm_v2,nm):
        ty=llvm_v1.type
        if(llvm_is_int(ty)):
            q=self.sdiv(llvm_v1,llvm_v2,'quot')
            r=self.smod(llvm_v1,llvm_v2,'rem')
            return None
        if(llvm_is_real(ty)):
            q=self.fdiv(llvm_v1,llvm_v2,'quot')
            r=self.fmod(llvm_v1,llvm_v2,'rem')
            return None
        raise NotImplementedError()
    
    def cmp(self,op,llvm_v1,llvm_v2,nm):
        if(llvm_is_int(llvm_v1.type)):
            return self.icmp({'eq':IPRED_EQ,
                              'ge':IPRED_SGE,
                              'gt':IPRED_SGT,
                              'le':IPRED_SLE,
                              'lt':IPRED_SLT,
                              'ne':IPRED_NE}[op],llvm_v1,llvm_v2,nm)

        if(llvm_is_number(llvm_v1.type)):
            return self.fcmp({'eq':RPRED_OEQ,
                              'ge':RPRED_OGE,
                              'gt':RPRED_OGT,
                              'le':RPRED_OLE,
                              'lt':RPRED_OLT,
                              'ne':RPRED_ONE}[op],llvm_v1,llvm_v2,nm)
        raise NotImplementedError()

    def pow(self,llvm_v1,llvm_v2,nm):
        pow_intr = llvm_intrinsic(INTR_POW, llvm_v1.type, llvm_v2.type)
        return self.call(pow_intr, (llvm_v1,llvm_v2),nm)
        
class llvm_compiled_fun(object):
    def __init__(self, llvm_fun, arg_t, return_t):
        self.llvm_fun=llvm_fun
        self.arg_t=arg_t
        self.return_t=return_t
    def __call__(self,**args):
        arg=[llvm_arg_value(t,args[v]) for (t,v) in self.arg_t]
        return python_value(self.return_t,llvm_run_function(self.llvm_fun,arg))
