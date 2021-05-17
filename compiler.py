from collections import defaultdict
from typing import List, Set, Dict, Tuple, DefaultDict
import itertools
import textwrap
import sys
from cs202_support.base_ast import print_ast

import cs202_support.x86exp as x86
import cfun
import constants

from rlam_parser import *
from typed_rlam import *

gensym_num = 0


def gensym(x):
    
    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'

def unzip2(ls):
    """
    Unzip a list of 2-tuples.
    :param ls: A list of 2-tuples.
    :return: A single 2-tuple. The first element of the tuple is a list of the 
    first elements of the pairs in ls. The second element of the tuple is a list
    of the second elements of the pairs in ls.
    """

    if ls == []:
        return [], []
    else:
        xs, ys = zip(*ls)
        return list(xs), list(ys)

##################################################
# typecheck
##################################################

TEnv = Dict[str, RlamType]

def uncover_closure_args(e, args):
        
    all_args = set([a[0] for a in args])
    closure_args = []

    def _uncover_closure_args(e):

        if isinstance(e, (IntTE, BoolTE, VoidTE, FunRefTE)):
            return
        elif isinstance(e, VarTE):
            if e.var not in all_args:
                closure_args.append((e.var, e.typ))
        elif isinstance(e, FunRefTE):
            if e.name not in all_args:
                closure_args.append((e.name, e.typ))
        elif isinstance(e, PrimTE):
            [_uncover_closure_args(a) for a in e.args]
        elif isinstance(e, IfTE):
            _uncover_closure_args(e.e1)
            _uncover_closure_args(e.e2)
            _uncover_closure_args(e.e3)
        elif isinstance(e, FuncallTE):
            [_uncover_closure_args(a) for a in e.args]
            _uncover_closure_args(e.fun)
        elif isinstance(e, DynamTE):
            _uncover_closure_args(e.body)
        elif isinstance(e, LambdaTE):
            _uncover_closure_args(e.body)
        elif isinstance(e, LetTE):
            
            # Call recursively on e.e1
            _uncover_closure_args(e.e1)

            # Then on body
            _uncover_closure_args(e.body)

            # But then remove e.x as if is added
            just_names = [n[0] for n in closure_args]
            if e.x in just_names:
                del closure_args[just_names.index(e.x)]

        else:
            raise Exception('_uncover_closure_args', e)

    _uncover_closure_args(e)
    return closure_args

def typecheck(p: RlamProgram) -> RlamProgramT:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param e: The Rlam program to typecheck
    :return: The program, if it is well-typed
    """

    prim_arg_types = {
        '+':   [IntT(), IntT()],
        'not': [BoolT()],
        '||':  [BoolT(), BoolT()],
        '&&':  [BoolT(), BoolT()],
        '>':   [IntT(), IntT()],
        '>=':  [IntT(), IntT()],
        '<':   [IntT(), IntT()],
        '<=':  [IntT(), IntT()],
        'neg': [IntT()]
    }

    prim_output_types = {
        '+':   IntT(),
        'not': BoolT(),
        '||':  BoolT(),
        '&&':  BoolT(),
        '>':   BoolT(),
        '>=':  BoolT(),
        '<':   BoolT(),
        '<=':  BoolT(),
        'neg': IntT()
    }

    def _vec_first_args_check(e, env, dynam_env):

        e1, e2 = e.args[0], e.args[1]

        # Make sure first arg is vector
        t1, new_e1 = tc_exp(e1, env, dynam_env)
        assert isinstance(t1, VectorT)
        ts = t1.types

        # Make sure 2nd arg is literal integer idx
        assert isinstance(e2, Int)
        idx = e2.val
        new_e2 = IntTE(idx)
        
        # Throw error if index doesn't exist
        t = ts[idx]

        return new_e1, new_e2, t

    def tc_dynam_func_call(e, env, dynam_env):

        # First index of tuple is Dynam
        dynam = dynam_env[e.fun.var][0]
        
        # Run tc_exp with the current scope - the initial
        # environment being the dynams args
        init_env = {a[0]: a[1] for a in dynam.args}
        new_env = {**env, **init_env}

        dynam_body_t, new_dynam_body = tc_exp(dynam.body, new_env, dynam_env)

        # Check to see if this dynam has already been checked
        # if so, make sure it has the same type
        if e.fun.var in env:
            if env[e.fun.var] != dynam_body_t:
                raise RuntimeError('If dynam function used multiple times, must have same type.')

        # Other case is if first time checked, save type
        else:
            env[e.fun.var] = dynam_body_t

        # Given the body of the Dynam get the closure args as a List[Tuple[str, RlamType]]
        closure_args = uncover_closure_args(new_dynam_body, dynam.args)

        # Replace spot in dynam_env with new tuple
        dynam_env[e.fun.var] = (dynam, DynamTE(args=dynam.args,
                                               body=new_dynam_body,
                                               closure_args=closure_args,
                                               output_type=dynam_body_t))

        # Gen new FuncallTE
        arg_types, new_args = unzip2([tc_exp(a, env, dynam_env) for a in e.args])
        
        # New fun is variable w/ has dynam type is of DynamT, to keep track of closure args
        dynam_t = DynamT(arg_types=arg_types,
                         return_type=dynam_body_t,
                         closure_args=closure_args)
        new_fun = VarTE(e.fun.var, typ=dynam_t)

        # New func call has the dynam_body type
        new_fun_call = FuncallTE(fun=new_fun,
                                 args=new_args,
                                 typ=dynam_body_t)

        # Return FuncallTE, w/ body of the dynams type as return type
        return dynam_body_t, new_fun_call

    def tc_exp(e, env, dynam_env) -> Tuple[RlamType, RlamExpT]:
        
        if isinstance(e, Var):
            return env[e.var], VarTE(e.var, env[e.var])

        elif isinstance(e, Int):
            return IntT(), IntTE(e.val)

        elif isinstance(e, Bool):
            return BoolT(), BoolTE(e.val)

        elif isinstance(e, Prim):

            if e.op == '==':
                
                e1, e2 = e.args

                t1, new_e1 = tc_exp(e1, env, dynam_env)
                t2, new_e2 = tc_exp(e2, env, dynam_env)
                assert t1 == t2

                new_e = PrimTE(op=e.op, args=[new_e1, new_e2], typ=BoolT())
                return BoolT(), new_e

            elif e.op == 'vectorRef':
                
                # Check vec first two args
                new_e1, new_e2, t = _vec_first_args_check(e, env, dynam_env)

                # Gen new prim
                new_e = PrimTE(op=e.op, args=[new_e1, new_e2], typ=t)

                # Return type of indexed element and new expression
                return t, new_e

            elif e.op == 'vectorSet':

                # Check vec first two args
                new_e1, new_e2, t = _vec_first_args_check(e, env, dynam_env)
                
                # Get third arg, check to make sure
                # type is valid
                e3 = e.args[2]
                t3, new_e3 = tc_exp(e3, env, dynam_env)
                assert t == t3

                # Make new prim
                new_e = PrimTE(op=e.op, args=[new_e1, new_e2, new_e3], typ=VoidT())

                # Return
                return VoidT(), new_e

            elif e.op == 'vector':

                types, new_args = [], []
                for a in e.args:
                    t, new_a = tc_exp(a, env, dynam_env)
                    types.append(t)
                    new_args.append(new_a)
                
                # Generate vector of types
                vt = VectorT(types)

                # Gen new expression
                new_e = PrimTE(op=e.op, args=new_args, typ=vt)
                return vt, new_e
            
            else:
                
                type_args = [tc_exp(a, env, dynam_env) for a in e.args]
                arg_types = [ta[0] for ta in type_args]
                new_args = [ta[1] for ta in type_args]
        
                assert arg_types == prim_arg_types[e.op], e
                
                new_typ = prim_output_types[e.op]
                new_exp = PrimTE(op=e.op, args=new_args, typ=new_typ)
                return new_typ, new_exp

        elif isinstance(e, Let):
            
            # For Let, non-dynamic case
            if not isinstance(e.e1, Dynam):

                t1, new_e1 = tc_exp(e.e1, env, dynam_env)
                new_env = {**env, e.x: t1}

                typ, new_body = tc_exp(e.body, new_env, dynam_env)
                new_exp = LetTE(x=e.x, e1=new_e1, body=new_body)

                return typ, new_exp

            # Special dynamic case
            new_dynam_env = {**dynam_env, e.x: (e.e1, None)}
            typ, new_body = tc_exp(e.body, env, new_dynam_env)

            if new_dynam_env[e.x][1] is None:
                raise RuntimeError('dynam expression was never used.')
            
            # Set new e_e1 with type checked DynamTE
            new_e1 = new_dynam_env[e.x][1]
            new_exp = LetTE(x=e.x, e1=new_e1, body=new_body)

            return typ, new_exp

        elif isinstance(e, If):

            t1, new_e1 = tc_exp(e.e1, env, dynam_env)
            t2, new_e2 = tc_exp(e.e2, env, dynam_env)
            t3, new_e3 = tc_exp(e.e3, env, dynam_env)

            assert t1 == BoolT()
            assert t2 == t3
             
            # Type of if is t2 or t2's type
            return t2, IfTE(new_e1, new_e2, new_e3, typ=t2)

        elif isinstance(e, Funcall):
            
            # Special dynam case - i.e., calling a dynamic function
            if isinstance(e.fun, Var) and e.fun.var in dynam_env:
                return tc_dynam_func_call(e, env, dynam_env)

            # Otherwise, base behavior for function call
            t_fun, new_fun = tc_exp(e.fun, env, dynam_env)
            assert isinstance(t_fun, FunT)
            
            arg_types, new_args = unzip2([tc_exp(a, env, dynam_env) for a in e.args])
            for at, tf_t in zip(t_fun.arg_types, arg_types):
                assert at == tf_t

            return t_fun.return_type, FuncallTE(fun=new_fun,
                                                args=new_args,
                                                typ=t_fun.return_type)

        elif isinstance(e, Dynam):
            raise RuntimeError('Dynam should only be used with Let. '
                               'This is a restriction made to make the current implementation easier.')

        elif isinstance(e, Lambda):
            
            ext_env = {**env, **{a[0]: a[1] for a in e.args}}
            new_body_typ, new_body = tc_exp(e.body, ext_env, dynam_env)
            
            new_e = LambdaTE(args=e.args, output_type=new_body_typ, body=new_body)

            # Return as type FunT
            lam_t = FunT(arg_types=[a[1] for a in e.args], return_type=new_body_typ)
            
            return lam_t, new_e

        else:
            raise Exception('tc_exp', e)

    def tc_def(defn, env, dynam_env) -> RlamDefT:

        init_env = {a[0]: a[1] for a in defn.args}
        new_env = {**env, **init_env}

        t_body, new_body = tc_exp(defn.body, new_env, dynam_env)

        assert t_body == defn.output_type
    
        return RlamDefT(defn.name,
                        defn.args,
                        defn.output_type,
                        new_body)
 
    env = {d.name: FunT(arg_types=[a[1] for a in d.args],
                        return_type=d.output_type) for d in p.defs}

    new_defs = [tc_def(d, env, {}) for d in p.defs]
    _, typ_body = tc_exp(p.body, env, {})

    return RlamProgramT(new_defs, typ_body)


##################################################
# shrink
##################################################

def shrink(p: RlamProgramT) -> RlamProgramT:
    """
    Eliminates some operators from Rlam
    :param e: The Rlam program to shrink
    :return: A shrunken Rlam program
    """

    def shrink_def(defn: RlamDefT) -> RlamDefT:
        
        new_body = shrink_exp(defn.body)
        return RlamDefT(defn.name,
                        defn.args,
                        defn.output_type,
                        new_body)

    def shrink_exp(e: RlamExpT) -> RlamExpT:

        if isinstance(e, (IntTE, BoolTE, VarTE, FuncallTE)):
            return e
                
        elif isinstance(e, LetTE):
            new_e1 = shrink_exp(e.e1)
            new_body = shrink_exp(e.body)
            return LetTE(e.x, new_e1, new_body)
        
        elif isinstance(e, PrimTE):
            new_args = [shrink_exp(arg) for arg in e.args]

            if e.op == '+':
                return PrimTE(e.op, new_args, typ=IntT())
            elif e.op in ['not', '==', '<']:
                return PrimTE(e.op, new_args, typ=BoolT())
            elif e.op in ['vector', 'vectorRef', 'vectorSet']:
                return PrimTE(e.op, new_args, typ=e.typ)
            elif e.op == '>':
                return PrimTE('<', [new_args[1], new_args[0]], typ=BoolT())
            elif e.op == '<=':
                return PrimTE('not', [PrimTE('<', [new_args[1], new_args[0]])], typ=BoolT())
            elif e.op == '>=':
                return PrimTE('not', [PrimTE('<', new_args)], typ=BoolT())
            elif e.op == '&&':
                e1, e2 = new_args
                return IfTE(e1, e2, Bool(False), typ=BoolT())
            elif e.op == '||':
                e1, e2 = new_args
                return IfTE(e1, Bool(True), e2, typ=BoolT())
            else:
                raise Exception('shrink unknown prim:', e)

        elif isinstance(e, DynamTE):
            new_body = shrink_exp(e.body)
            return DynamTE(e.args, new_body,
                           e.closure_args, e.output_type)

        elif isinstance(e, LambdaTE):
            return LambdaTE(e.args, e.output_type, shrink_exp(e.body))

        elif isinstance(e, IfTE):
            return IfTE(shrink_exp(e.e1),
                        shrink_exp(e.e2),
                        shrink_exp(e.e3),
                        typ=e.typ)

        else:
            raise Exception('shrink_exp', e)
    
    new_body = shrink_exp(p.body)
    new_defns = [shrink_def(d) for d in p.defs]

    return RlamProgramT(new_defns, new_body)

##################################################
# uniquify
##################################################

def uniquify(p: RlamProgramT) -> RlamProgramT:
    """
    Makes the program's variable names unique
    :param e: The Rlam program to uniquify
    :return: An Rlam program with unique names
    """

    def uniquify_def(defn: RlamDefT) -> RlamDefT:

        new_args, env = [], {}
        for arg in defn.args:
            new_name = gensym(arg[0])
            new_args.append((new_name, arg[1]))
            env[arg[0]] = new_name
        
        new_body = uniquify_exp(defn.body, env)
        return RlamDefT(defn.name,
                        new_args,
                        defn.output_type,
                        new_body)

    def u_args(e, env):

        # If DynamTE or LambdaTE, then make argument unique
        new_args, new_env = [], {}
        for arg in e.args:
            new_name = gensym(arg[0])
            new_args.append((new_name, arg[1]))
            new_env[arg[0]] = new_name

        # Update with current env
        new_env.update(env)

        return new_args, new_env

    def uniquify_exp(e: RlamExpT, env: Dict[str, str]) -> RlamExpT:

        if isinstance(e, (IntTE, BoolTE)):
            return e

        elif isinstance(e, FuncallTE):
            new_args = [uniquify_exp(a, env) for a in e.args]
            return FuncallTE(uniquify_exp(e.fun, env), new_args, e.typ)

        elif isinstance(e, VarTE):
            
            # Special nested case for uniquify args
            if isinstance(e.typ, DynamT):
                e.typ.closure_args =\
                    [(env[a], t) if a in env else (a, t) for a, t in e.typ.closure_args]

            if e.var in env:
                return VarTE(env[e.var], typ=e.typ)
            else:
                return e

        elif isinstance(e, LetTE):
            new_e1 = uniquify_exp(e.e1, env)
            new_x = gensym(e.x)
            new_env = {**env, e.x: new_x}
            new_body = uniquify_exp(e.body, new_env)
            return LetTE(new_x, new_e1, new_body)

        elif isinstance(e, PrimTE):
            new_args = [uniquify_exp(arg, env) for arg in e.args]
            return PrimTE(e.op, new_args, e.typ)

        elif isinstance(e, IfTE):
            return IfTE(uniquify_exp(e.e1, env),
                        uniquify_exp(e.e2, env),
                        uniquify_exp(e.e3, env),
                        typ=e.typ)
        
        elif isinstance(e, DynamTE):

            # Make arguments unique
            new_args, new_env = u_args(e, env)

            # Want to call uniquify on body,
            # but with the special property that
            # all of the closure variables in the body of the dynam
            # map to unique temp closure variables.

            # So first we make them, and add them to new_env
            new_closure_vars = [gensym('closure_var') for _ in e.closure_args]
            for cv_typ, new_cv in zip(e.closure_args, new_closure_vars):
                new_env[cv_typ[0]] = new_cv

            # Then we can generate the new body
            new_body = uniquify_exp(e.body, new_env)

            # We want to keep track of these new closure args + their order
            # and pass them to the return DynamTE
            new_closure_args = list(zip(new_closure_vars, [a[1] for a in e.closure_args]))

            # Return new w/ new args, body and closure args
            return DynamTE(args=new_args,
                           body=new_body,
                           closure_args=new_closure_args,
                           output_type=e.output_type)

        elif isinstance(e, LambdaTE):

            # Make arguments unique
            new_args, new_env = u_args(e, env)
            
            # Call recursively on body
            new_body = uniquify_exp(e.body, new_env)

            return LambdaTE(args=new_args,
                            output_type=e.output_type,
                            body=new_body)

        else:
            raise Exception('uniquify', e)
    
    new_defns = [uniquify_def(d) for d in p.defs]
    new_body = uniquify_exp(p.body, {})
    

    return RlamProgramT(new_defns, new_body)


def flatten_lambda(p: RlamProgramT) -> RlamProgramT:

    def flatten_lambda_def(defn):

        new_body = flatten_lambda_exp(defn.body)
        return RlamDefT(defn.name,
                        defn.args,
                        defn.output_type,
                        new_body)

    def flatten_lambda_exp(e: RlamExpT, env: Dict[str, str]) -> RlamExpT:

        if isinstance(e, (IntTE, BoolTE, VarTE, FunRefTE)):
            return e

        elif isinstance(e, FuncallTE):
            new_args = [flatten_lambda_exp(a, env) for a in e.args]
            return FuncallTE(flatten_lambda_exp(e.fun, env), new_args, e.typ)

        elif isinstance(e, LetTE):

            new_e1 = flatten_lambda_exp(e.e1, env)
            new_body = flatten_lambda_exp(e.body, env)
            
            # If body of the Let is a Lambda, need to re-arrange
            if isinstance(new_body, LambdaTE):

                # Move the let statement inside the body of the lambda
                new_expr_body = LetTE(e.x, new_e1, new_body.body)
                
                # Then return new expr
                new_expr = LambdaTE(args=new_body.args,
                                    output_type=new_body.output_type,
                                    body=new_expr_body)

                return new_expr
            
            return LetTE(e.x, new_e1, new_body)

        elif isinstance(e, PrimTE):
            new_args = [flatten_lambda_exp(arg, env) for arg in e.args]
            return PrimTE(e.op, new_args, e.typ)

        elif isinstance(e, IfTE):
            return IfTE(flatten_lambda_exp(e.e1, env),
                        flatten_lambda_exp(e.e2, env),
                        flatten_lambda_exp(e.e3, env),
                        typ=e.typ)
        
        elif isinstance(e, LambdaTE):

            new_body = flatten_lambda_exp(e.body, env)
            return LambdaTE(args=e.args,
                            output_type=e.output_type,
                            body=new_body)
    
        elif isinstance(e, DynamTE):
            new_body = flatten_lambda_exp(e.body, env)
            return DynamTE(args=e.args,
                           body=new_body,
                           closure_args=e.closure_args,
                           output_type=e.output_type)

        else:
            raise Exception('flatten_lambda_exp', e)
    
    new_defns = [flatten_lambda_def(d) for d in p.defs]
    new_body = flatten_lambda_exp(p.body, {})

    return RlamProgramT(new_defns, new_body)

##################################################
# reveal_functions
##################################################

def reveal_functions(p: RlamProgramT) -> RlamProgramT:
    """
    Transform references to top-level functions from variable references to
    function references.
    :param e: An Rlam program
    :return: An Rlam program in which all references to top-level functions
    are in the form of FunRef objects.
    """

    def reveal_function_def(defn: RlamDefT,  env: Set[str]) -> RlamDefT:

        new_body = reveal_function_exp(defn.body, env)
        return RlamDefT(defn.name,
                        defn.args,
                        defn.output_type,
                        new_body)

    def reveal_function_exp(e: RlamExpT, env: Set[str]) -> RlamExpT:

        if isinstance(e, (IntTE, BoolTE)):
            return e

        elif isinstance(e, FuncallTE):
            new_args = [reveal_function_exp(a, env) for a in e.args]

            return FuncallTE(fun=reveal_function_exp(e.fun, env),
                             args=new_args, typ=e.typ)

        elif isinstance(e, VarTE):

            if e.var in env:
                return FunRefTE(e.var, e.typ)
            elif isinstance(e.typ, FunT):
                return FunRefTE(e.var, e.typ)
            else:
                return e

        elif isinstance(e, LetTE):
            new_e1 = reveal_function_exp(e.e1, env)
            new_env = env.copy()

            # Special Dynam / Lambda case, if the new expression
            # is a lambda expression, then we want to add
            # the name of the variable to the environment
            # as a valid function name to call
            if isinstance(new_e1, (DynamTE, LambdaTE)):
                new_env.add(e.x)

            new_body = reveal_function_exp(e.body, new_env)
            return LetTE(e.x, new_e1, new_body)

        elif isinstance(e, PrimTE):
            new_args = [reveal_function_exp(arg, env) for arg in e.args]
            return PrimTE(e.op, new_args, e.typ)

        elif isinstance(e, IfTE):
            return IfTE(reveal_function_exp(e.e1, env),
                        reveal_function_exp(e.e2, env),
                        reveal_function_exp(e.e3, env),
                        typ=e.typ)

        elif isinstance(e, DynamTE):
            new_body = reveal_function_exp(e.body, env)
            return DynamTE(e.args, new_body, e.closure_args, e.output_type)

        elif isinstance(e, LambdaTE):
            new_body = reveal_function_exp(e.body, env)
            return LambdaTE(e.args, e.output_type, new_body)

        else:
            raise Exception('reveal_functions', e)

    func_names = set([d.name for d in p.defs])

    new_body = reveal_function_exp(p.body, func_names)
    new_defns = [reveal_function_def(d, func_names) for d in p.defs]

    return RlamProgramT(new_defns, new_body)


##################################################
# convert-to-closure
##################################################

def convert_to_closure(p: RlamProgramT) -> RlamProgramT:
    
    # Store any created dynam defs
    dynam_defs = []

    def convert_to_closure_def(defn: RlamDefT) -> RlamDefT:

        new_body = convert_to_closure_exp(defn.body, {})
        return RlamDefT(defn.name,
                        defn.args,
                        defn.output_type,
                        new_body)

    def get_new_defn(e, env):

        # Gen new function name
        func_name = gensym('lambda')

        # Call recursively on body
        new_body = convert_to_closure_exp(e.body, env)

        # Get the closure args
        if hasattr(e, 'closure_args'):
            closure_args = e.closure_args
        else:
            closure_args = uncover_closure_args(new_body, e.args)

        vec_type = VectorT([a[1] for a in closure_args])
        vec_var = VarTE('closure', vec_type)
        func_args = e.args + [('closure', vec_type)]

        # Unpack body
        for i, c_var_typ in enumerate(closure_args):
            new_body = LetTE(c_var_typ[0],
                             PrimTE('vectorRef', [vec_var, IntTE(i)],
                             c_var_typ[1]),
                             new_body)

        new_defn = RlamDefT(func_name, func_args, e.output_type, new_body)

        # Save new definition to definitions
        dynam_defs.append(new_defn)
        
        # Generate and return new FunRef
        fun_ref = FunRefTE(name=func_name,
                           typ=FunT(arg_types=[a[1] for a in func_args],
                                    return_type=e.output_type))

        return fun_ref, closure_args

    def convert_dynam_body_closure(e, env):

        # If here, assumes e is DynamTE
        fun_ref, _ = get_new_defn(e, env)

        # Return just the new name of this function
        return fun_ref.name

    def gen_new_funcall(e, new_fun_ref, closure, env):

        # The new arguments are recursive call on the args
        # then adding the closure vector with rest of args
        new_args = [convert_to_closure_exp(a, env) for a in e.args] + [closure]
                    
        # Then return as new funcall - where typ is the same
        return FuncallTE(fun=new_fun_ref, args=new_args, typ=e.typ)

    def convert_to_closure_exp(e, env) -> RlamExpT:

        if isinstance(e, (IntTE, BoolTE, VarTE)):
            return e

        elif isinstance(e, FuncallTE):
            
            # If contains a  call to FunRef
            if isinstance(e.fun, FunRefTE):

                # If call to Dynam
                if isinstance(e.fun.typ, DynamT):
            
                    # Get reference to new function call name.
                    new_fun_name = env[e.fun.name]

                    # Generate the closure vector type
                    closure_type = VectorT([ca[1] for ca in e.fun.typ.closure_args])

                    # Generate the closure vector from the closure args
                    closure_args = [VarTE(var=ca[0], typ=ca[1]) for ca in e.fun.typ.closure_args]
                    closure = PrimTE(op='vector', args=closure_args, typ=closure_type)
                
                    # Create new argument types as current types plus closure type
                    new_arg_types = e.fun.typ.arg_types + [closure_type]

                    # Then generate new FunT, for new FunRefTE
                    new_fun_typ = FunT(new_arg_types, e.fun.typ.return_type)
                    new_fun_ref = FunRefTE(name=new_fun_name, typ=new_fun_typ)

                    # Gen new fun call
                    return gen_new_funcall(e, new_fun_ref, closure, env)
                
                # Call to FunT - for call to lambda
                elif isinstance(e.fun.typ, FunT):

                    # If simple case, the saved type should be
                    # a closure in the env
                    context = env[e.fun.name]
                    if isinstance(context, PrimTE) and context.op == 'vector' and len(context.args) == 2:
                    
                        # Get the correct type of the reference
                        # vector storing the function and arguments
                        typ = context.typ

                        # Put it in a variable
                        vec_var = VarTE(e.fun.name, typ)

                        # First arg is the reference to the function
                        new_fun_ref = PrimTE('vectorRef', args=[vec_var, IntTE(0)], typ=typ.types[0])

                        # Second arg is the stored arguments
                        closure = PrimTE('vectorRef', args=[vec_var, IntTE(1)], typ=typ.types[1])
                        
                        # Gen new fun call
                        return gen_new_funcall(e, new_fun_ref, closure, env)

                    else:
                        raise RuntimeError('context for function is not closure')

                else:
                    raise Exception('convert_to_closure_exp FunRefTE', e)
            
            # If the function is a lambda
            elif isinstance(e.fun, LambdaTE):

                # In this case, lambda isn't saved to a variable
                # just called directly - first recursive call
                closure_vec = convert_to_closure_exp(e.fun, env)

                # Can just grab new_fun_ref directly from closure_vec
                # as well as the closure arg vector
                # (instead of creating a vectorRef to them)
                new_fun_ref = closure_vec.args[0]
                closure = closure_vec.args[1]

                # Then same gen new fun call
                return gen_new_funcall(e, new_fun_ref, closure, env)

            # Otherwise, just call recursively
            new_args = [convert_to_closure_exp(a, env) for a in e.args]
            return FuncallTE(convert_to_closure_exp(e.fun, env), new_args, e.typ)

        elif isinstance(e, LetTE):

            # If e1, the expression of the let is a DynamTE
            if isinstance(e.e1, DynamTE):
                
                # Create and add a new function based on the body
                # of this function
                dynam_func_name = convert_dynam_body_closure(e.e1, env)

                # Store in new environment, mapping from
                # assigned name to the name of the
                # created dynam function
                new_env = {**env, e.x: dynam_func_name}

                # Now call recursively on the new body
                # with the new environment
                new_body = convert_to_closure_exp(e.body, new_env)

                # Return the new body here instead of the let statement
                return new_body

            # Otherwise, just normal recursive calls
            new_e1 = convert_to_closure_exp(e.e1, env)
            
            # Passing a new environment with current variables in scope
            new_env = {**env, e.x: new_e1}
            new_body = convert_to_closure_exp(e.body, new_env)

            return LetTE(e.x, new_e1, new_body)

        elif isinstance(e, PrimTE):
            new_args = [convert_to_closure_exp(arg, env) for arg in e.args]
            return PrimTE(e.op, new_args, e.typ)

        elif isinstance(e, IfTE):
            return IfTE(convert_to_closure_exp(e.e1, env),
                        convert_to_closure_exp(e.e2, env),
                        convert_to_closure_exp(e.e3, env),
                        typ=e.typ)

        elif isinstance(e, LambdaTE):

            # Get function ref and closure args
            fun_ref, closure_args = get_new_defn(e, env)

            # Get the vector of current in scope arguments
            closure_vars = [env[a[0]] for a in closure_args]
            closure_var_types = VectorT([a[1] for a in closure_args])
            args_vec = PrimTE('vector', args=closure_vars, typ=closure_var_types)
            
            # Return a vector with func + args_cv
            return PrimTE('vector', args=[fun_ref, args_vec], typ=VectorT([fun_ref.typ, args_vec.typ]))

        elif isinstance(e, FunRefTE):
            raise RuntimeError('Not Implemented FunRefTE case')

        elif isinstance(e, DynamTE):
            raise RuntimeError('If Dynam should be in body of Let.')

        else:
            raise Exception('convert_to_closure_exp', e)

    new_body = convert_to_closure_exp(p.body, {})
    new_defns = [convert_to_closure_def(d) for d in p.defs] + dynam_defs

    return RlamProgramT(new_defns, new_body)




##################################################
# limit-functions
##################################################


def limit_functions(p: RlamProgramT) -> RlamProgramT:
    """
    Limit functions to have at most 6 arguments.
    :param e: An Rlam program to reveal_functions
    :return: An Rlam program, in which each function has at most 6 arguments
    """

    def limit_functions_def(defn):

        if len(defn.args) > 6:

            # replace the 6th argument with a single vector to hold the rest of the arguments
            # replace references the 6+ references with vectorref
            # expressions that return the correct thing

            # Map variable names to the correct / new vector ref expressions
            # variables in the environment are the argument names for
            # the extra variables to be mapped
            env = {} 
            extra_args = defn.args[5:]
            args_vec_name = gensym('args_vec')

            extra_arg_types = [a[1] for a in extra_args]
            vec_var = VarTE(args_vec_name, VectorT(extra_arg_types))
            
            for i, arg in enumerate(extra_args):
                env[arg[0]] = PrimTE('vectorRef', [vec_var, IntTE(i)], arg[1])

            new_body = limit_functions_exp(defn.body, env)
            new_args = defn.args[:5] + [(vec_var.var, vec_var.typ)]

            return RlamDefT(defn.name,
                            new_args,
                            defn.output_type,
                            new_body)

        else:

            new_body = limit_functions_exp(defn.body, {})

            return RlamDefT(defn.name,
                            defn.args,
                            defn.output_type,
                            new_body)

    def limit_functions_exp(e, env):

        if isinstance(e, (IntTE, BoolTE, FunRefTE)):
            return e

        if isinstance(e, VarTE):
            if e.var in env:
                return env[e.var]
            return e

        elif isinstance(e, FuncallTE):

            new_args = [limit_functions_exp(a, env) for a in e.args]
            new_fun = limit_functions_exp(e.fun, env)

            if len(e.args) > 6:
                vec_exp = PrimTE('vector', new_args[5:], VectorT(new_fun.typ.arg_types[5:]))
                return FuncallTE(new_fun, new_args[:5] + [vec_exp], e.typ)

            return FuncallTE(new_fun, new_args, e.typ)

        elif isinstance(e, LetTE):
            new_e1 = limit_functions_exp(e.e1, env)
            new_body = limit_functions_exp(e.body, env)
            return LetTE(e.x, new_e1, new_body)

        elif isinstance(e, PrimTE):
            new_args = [limit_functions_exp(arg, env) for arg in e.args]
            return PrimTE(e.op, new_args, e.typ)
        
        elif isinstance(e, IfTE):
            return IfTE(limit_functions_exp(e.e1, env),
                        limit_functions_exp(e.e2, env),
                        limit_functions_exp(e.e3, env),
                        typ=e.typ)
        else:
            raise Exception('limit_functions_exp', e)

    new_body = limit_functions_exp(p.body, {})
    new_defns = [limit_functions_def(d) for d in p.defs]
    
    return RlamProgramT(new_defns, new_body)


##################################################
# expose-alloc
##################################################

def mk_let(bindings: Dict[str, RlamExpT], body: RlamExpT):
    """
    Builds a Let expression from a list of bindings and a body.
    :param bindings: A list of bindings from variables (str) to their 
    expressions (RlamExp)
    :param body: The body of the innermost Let expression
    :return: A Let expression implementing the bindings in "bindings"
    """
    result = body
    for var, rhs in reversed(list(bindings.items())):
        result = LetTE(var, rhs, result)

    return result


def get_type(e: RlamExpT) -> RlamType:
    """
    Helper to return type, esp for classes w/o type
    """
    if hasattr(e, 'typ'):
        return e.typ
    elif isinstance(e, IntTE):
        return IntT()
    elif isinstance(e, BoolTE):
        return BoolT()
    elif isinstance(e, GlobalValTE):
        return IntT()
    elif isinstance(e, VoidTE):
        return VoidT()
    
    return VoidT()


def expose_alloc(p: RlamProgramT) -> RlamProgramT:
    """
    Transforms 'vector' forms into explicit memory allocations, with conditional
    calls to the garbage collector.
    :param e: A typed Rlam expression
    :return: A typed Rlam expression, without 'vector' forms
    """

    def expose_alloc_def(defn) -> RlamDefT:
        
        new_body = expose_alloc_exp(defn.body)
        return RlamDefT(defn.name,
                        defn.args,
                        defn.output_type,
                        new_body)

    def expose_alloc_exp(e: RlamExpT) -> RlamExpT:

        # Add case for funcall and funref

        if isinstance(e, LetTE):
            new_e1 = expose_alloc_exp(e.e1)
            new_body = expose_alloc_exp(e.body)
            return LetTE(e.x, new_e1, new_body)

        elif isinstance(e, FuncallTE):
            new_fun = expose_alloc_exp(e.fun)
            new_args = [expose_alloc_exp(a) for a in e.args]
            return FuncallTE(new_fun, new_args, e.typ)

        elif isinstance(e, (IntTE, BoolTE, VarTE, FunRefTE)):
            return e

        elif isinstance(e, IfTE):
            return IfTE(expose_alloc_exp(e.e1),
                        expose_alloc_exp(e.e2),
                        expose_alloc_exp(e.e3),
                        e.typ)

        elif isinstance(e, PrimTE):

            new_args = [expose_alloc_exp(arg) for arg in e.args]

            if e.op == 'vector':
                vec_type = e.typ
                assert isinstance(vec_type, VectorT)

                bindings = {}

                # Step 1.
                # make a name for each element of the vector
                # bind the name to the input expression
                var_names = [gensym('v') for _ in new_args]
                for var, a in zip(var_names, new_args):
                    bindings[var] = a

                # Step 2.
                # run the collector if we don't have enough space
                # to do the allocation
                total_bytes = 8 + 8*len(new_args)
                bindings[gensym('_')] = \
                    IfTE(PrimTE('<', [PrimTE('+', [GlobalValTE('free_ptr'),
                                                IntTE(total_bytes)], IntT()),
                                    GlobalValTE('fromspace_end')], BoolT()),
                        VoidTE(),
                        PrimTE('collect', [IntTE(total_bytes)], VoidT()),
                        VoidT())

                # Step 3.
                # allocate the bytes for the vector and give it a name
                vec_name = gensym('vec')
                bindings[vec_name] = PrimTE('allocate', [IntTE(len(new_args))], vec_type)

                # Step 4.
                # vectorSet each element of the allocated vector to its variable
                # from Step 1
                for idx in range(len(new_args)):
                    typ = vec_type.types[idx]
                    var = var_names[idx]

                    bindings[gensym('_')] = PrimTE('vectorSet',
                                                [
                                                    VarTE(vec_name, vec_type),
                                                    IntTE(idx),
                                                    VarTE(var, typ)
                                                ],
                                                VoidT())

                # Step 5.
                # Make a big Let with all the bindings
                return mk_let(bindings, VarTE(vec_name, vec_type))

            else:
                return PrimTE(e.op, new_args, e.typ)

        else:
            raise Exception('expose_alloc_exp', e)
    
    
    new_defns = [expose_alloc_def(d) for d in p.defs]
    new_body = expose_alloc_exp(p.body)
    
    return RlamProgramT(new_defns, new_body)


##################################################
# remove-complex-opera*
##################################################

def rco(p: RlamProgramT) -> RlamProgramT:
    """
    Removes complex operands. After this pass, the program will be in A-Normal
    Form (the arguments to Prim operations will be atomic).
    :param e: An Rlam expression
    :return: An Rlam expression in A-Normal Form
    """

    def rco_def(defn):

        new_body = rco_exp(defn.body)
        return RlamDefT(defn.name,
                        defn.args,
                        defn.output_type,
                        new_body)

    def rco_atm(e: RlamExpT, bindings: Dict[str, RlamExpT]) -> RlamExpT:
        
        if isinstance(e, (IntTE, BoolTE, VarTE)):
            return e

        elif isinstance(e, (GlobalValTE, VoidTE, FunRefTE)):

            new_v = gensym('tmp')
            bindings[new_v] = e
            return VarTE(new_v, typ=get_type(e))
        
        elif isinstance(e, LetTE):
            new_e1 = rco_exp(e.e1)
            bindings[e.x] = new_e1
            v = rco_atm(e.body, bindings)
            return v
 
        elif isinstance(e, PrimTE):
            new_args = [rco_atm(arg, bindings) for arg in e.args]
            new_v = gensym('tmp')
            bindings[new_v] = PrimTE(e.op, new_args, typ=e.typ)
            return VarTE(new_v, e.typ)

        elif isinstance(e, IfTE):
            
            new_if = IfTE(rco_atm(e.e1, bindings),
                          rco_atm(e.e2, bindings),
                          rco_atm(e.e3, bindings),
                          typ=e.typ)

            new_v = gensym('tmp')
            bindings[new_v] = new_if

            return VarTE(new_v, typ=e.typ)

        elif isinstance(e, FuncallTE):
            
            new_args = [rco_atm(a, bindings) for a in e.args]
            new_fun = rco_atm(e.fun, bindings)
            new_func_call = FuncallTE(new_fun, new_args, e.typ)

            new_v = gensym('tmp')
            bindings[new_v] = new_func_call
            return VarTE(new_v, typ=e.typ)

        else:
            raise Exception('rco_atm', e)

    def rco_exp(e: RlamExpT) -> RlamExpT:

        if isinstance(e, (IntTE, BoolTE, VarTE, GlobalValTE, VoidTE, FunRefTE)):
            return e

        elif isinstance(e, LetTE):

            new_e1 = rco_exp(e.e1)
            new_body = rco_exp(e.body)
            return LetTE(e.x, new_e1, new_body)
        
        elif isinstance(e, FuncallTE):
            
            bindings = {}
            new_fun = rco_atm(e.fun, bindings)
            new_args = [rco_atm(a, bindings) for a in e.args]
            return mk_let(bindings, FuncallTE(new_fun, new_args, e.typ))

        elif isinstance(e, PrimTE):
            
            bindings = {}
            new_args = [rco_atm(arg, bindings) for arg in e.args]
            return mk_let(bindings, PrimTE(e.op, new_args, e.typ))

        elif isinstance(e, IfTE):
            return IfTE(rco_exp(e.e1),
                        rco_exp(e.e2),
                        rco_exp(e.e3),
                        typ=e.typ)

        else:
            raise Exception('rco_exp', e)
    
    
    new_defns = [rco_def(d) for d in p.defs]
    new_body = rco_exp(p.body)
    
    return RlamProgramT(new_defns, new_body)


##################################################
# explicate-control
##################################################

def explicate_control(p: RlamProgramT) -> cfun.Program:
    """
    Transforms an Rlam Program into a Cfun program.
    :param e: An Rlam Program
    :return: A Cfun Program
    """

    def explicate_control_help(e: RlamExpT) -> Dict[str, cfun.Tail]:

        cfg: Dict[str, cfun.Tail] = {}

        def ec_atm(e: RlamExpT) -> cfun.Atm:
            
            if isinstance(e, IntTE):
                return cfun.Int(e.val)
            elif isinstance(e, BoolTE):
                return cfun.Bool(e.val)
            elif isinstance(e, VarTE):
                return cfun.Var(e.var, e.typ)
            elif isinstance(e, VoidTE):
                return cfun.Void()
            elif isinstance(e, GlobalValTE):
                return cfun.GlobalVal(e.var)
            else:
                raise Exception('ec_atm', e)

        def ec_exp(e: RlamExpT) -> cfun.Exp:
            
            if isinstance(e, PrimTE):
                return cfun.Prim(e.op, [ec_atm(a) for a in e.args],
                                typ=e.typ)
            elif isinstance(e, FunRefTE):
                return cfun.FunRef(e.name)

            elif isinstance(e, FuncallTE):
                new_fun = ec_atm(e.fun)
                new_args = [ec_atm(a) for a in e.args]
                return cfun.Call(new_fun, new_args, e.typ)

            return cfun.AtmExp(ec_atm(e))

        def ec_assign(x: str, e: RlamExpT, k: cfun.Tail) -> cfun.Tail:

            if isinstance(e, (IntTE, BoolTE, VarTE, PrimTE, FuncallTE, VoidTE, GlobalValTE, FunRefTE)):

                if isinstance(e, PrimTE):
                    if e.op == 'collect':
                        return cfun.Seq(cfun.Collect(e.args[0].val), k)

                is_vec = isinstance(get_type(e), VectorT)

                return cfun.Seq(cfun.Assign(x, ec_exp(e), is_vec=is_vec), k)
            
            elif isinstance(e, LetTE):
                return ec_assign(e.x, e.e1, ec_assign(x, e.body, k))

            elif isinstance(e, IfTE):
                finally_label = gensym('label')
                cfg[finally_label] = k
                b2 = ec_assign(x, e.e2, cfun.Goto(finally_label))
                b3 = ec_assign(x, e.e3, cfun.Goto(finally_label))
                return ec_pred(e.e1, b2, b3)

            else:
                raise Exception('ec_assign', e)

        def ec_pred(test: RlamExpT, b1: cfun.Tail, b2: cfun.Tail) -> cfun.Tail:
            
            if isinstance(test, BoolTE):
                if test.val:
                    return b1
                else:
                    return b2
    
            elif isinstance(test, VarTE):
                then_label = gensym('label')
                else_label = gensym('label')

                cfg[then_label] = b1
                cfg[else_label] = b2

                return cfun.If(
                    cfun.Prim('==', [cfun.Var(test.var),
                                    cfun.Bool(True)],
                            typ=BoolT()),
                    then_label, else_label)

            elif isinstance(test, PrimTE):

                if test.op == 'not':
                    return ec_pred(test.args[0], b2, b1)

                then_label = gensym('label')
                else_label = gensym('label')

                cfg[then_label] = b1
                cfg[else_label] = b2

                return cfun.If(ec_exp(test), then_label, else_label)

            elif isinstance(test, LetTE):

                body_block = ec_pred(test.body, b1, b2)
                return ec_assign(test.x, test.e1, body_block)

            elif isinstance(test, IfTE):

                label1 = gensym('label')
                label2 = gensym('label')
                cfg[label1] = b1
                cfg[label2] = b2

                new_b2 = ec_pred(test.e2, cfun.Goto(label1), cfun.Goto(label2))
                new_b3 = ec_pred(test.e3, cfun.Goto(label1), cfun.Goto(label2))

                return ec_pred(test.e1, new_b2, new_b3)

            else:
                raise Exception('ec_pred', test)

        def ec_tail(e: RlamExpT) -> cfun.Tail:

            if isinstance(e, (IntTE, BoolTE, VarTE, PrimTE)):
                return cfun.Return(ec_exp(e))

            elif isinstance(e, LetTE):
                return ec_assign(e.x, e.e1, ec_tail(e.body))

            elif isinstance(e, IfTE):
                b1 = ec_tail(e.e2)
                b2 = ec_tail(e.e3)
                return ec_pred(e.e1, b1, b2)

            elif isinstance(e, FuncallTE):
                new_fun = ec_atm(e.fun)
                new_args = [ec_atm(a) for a in e.args]
                return cfun.TailCall(new_fun, new_args, e.typ)

            else:
                raise Exception('ec_tail', e)

        cfg['start'] = ec_tail(e)
        return cfg
    
    # handle definitions
    new_defs = []
    for d in p.defs:
        cfg = explicate_control_help(d.body)
        new_def = cfun.Def(d.name, d.args, d.output_type, cfg)
        new_defs.append(new_def)

    # body
    new_body_cfg = explicate_control_help(p.body)

    def get_return_type(e):

        if hasattr(e, 'typ'):
            return e.typ

        if isinstance(e, cfun.Seq):
            return get_return_type(e.tail)
        
        elif isinstance(e, cfun.If):
            # Then and else label should have same type
            return get_return_type(new_body_cfg[e.then_label])

        elif isinstance(e, cfun.Goto):
            return get_return_type(new_body_cfg[e.label])

        elif isinstance(e, cfun.Return):
            return get_return_type(e.exp)

        raise Exception('get_return_type', e)

    new_body = cfun.Def('main', [], get_return_type(new_body_cfg['start']), new_body_cfg)
    new_defs.append(new_body)

    output_program = cfun.Program(new_defs)
    return output_program


##################################################
# select-instructions
##################################################

def select_instructions(p: cfun.Program) -> Dict[str, x86.Program]:
    """
    Transforms a Cfun program into a pseudo-x86 assembly program.
    :param p: a Cfun program
    :return: a set of pseudo-x86 definitions, as a dictionary mapping function
    names to pseudo-x86 programs.
    """

    def select_instructions_help(p: cfun.Def) -> x86.Program:

        def si_atm(a: cfun.Atm) -> x86.Arg:

            if isinstance(a, cfun.Int):
                return x86.Int(a.val)
            
            elif isinstance(a, cfun.Bool):
                if a.val == True:
                    return x86.Int(1)
                elif a.val == False:
                    return x86.Int(0)
                
                raise Exception('si_atm', a)

            elif isinstance(a, cfun.Void):
                return x86.Int(0)

            elif isinstance(a, cfun.Var):

                if isinstance(a.typ, VectorT):
                    return x86.VecVar(a.var)

                return x86.Var(a.var)

            elif isinstance(a, str):
                return x86.Var(a)

            elif isinstance(a, cfun.GlobalVal):
                return x86.GlobalVal(a.val)

            else:
                raise Exception('si_atm', a)

        op_cc = {
            '==': 'e',
            '>': 'g',
            '<': 'l',
        }

        def get_tag(e):

            if len(e.typ.types) == 0:
                return int((0 << 1) + 1)

            pointer_mask = eval('0b' + ''.join([str(int(isinstance(t, VectorT)))
                                            for t in e.typ.types]))
            len_tag = (pointer_mask << 6) + int(e.args[0].val)
            tag = (len_tag << 1) + 1

            return int(tag)

        def si_stmt(e: cfun.Stmt) -> List[x86.Instr]:

            if isinstance(e, cfun.Assign):

                assign_var = x86.Var(e.var)
                if e.is_vec:
                    assign_var = x86.VecVar(e.var)
                
                if isinstance(e.exp, cfun.AtmExp):
                    return [x86.Movq(si_atm(e.exp.atm), assign_var)]

                elif isinstance(e.exp, cfun.Prim):
                    if e.exp.op == '+':
                        a1, a2 = e.exp.args
                        return [x86.Movq(si_atm(a1), assign_var),
                                x86.Addq(si_atm(a2), assign_var)]

                    elif e.exp.op == 'neg':
                        return [x86.Movq(si_atm(e.exp.args[0]), assign_var),
                                x86.Negq(assign_var)]

                    elif e.exp.op in ['==', '<']:
                        a1, a2 = e.exp.args
                        return [x86.Cmpq(si_atm(a2), si_atm(a1)),
                                x86.Set(op_cc[e.exp.op], x86.ByteReg('al')),
                                x86.Movzbq(x86.ByteReg('al'), assign_var)]

                    elif e.exp.op == 'not':
                        arg = si_atm(e.exp.args[0])

                        return [x86.Movq(arg, assign_var),
                                x86.Xorq(x86.Int(1), assign_var)]

                    elif e.exp.op == 'allocate':

                        free_ptr = x86.GlobalVal('free_ptr')
                        vec_var = x86.VecVar(e.var)
                        sz = int(e.exp.args[0].val)
                        space = x86.Int(int(8 * (1 + sz)))
                        tag = x86.Int(get_tag(e.exp))

                        return [x86.Movq(free_ptr, vec_var),
                                x86.Addq(space, free_ptr),
                                x86.Movq(vec_var, x86.Reg('r11')),
                                x86.Movq(tag, x86.Deref(0, 'r11'))]

                    elif e.exp.op in ['vectorSet', 'vectorRef']:

                        vec_var = si_atm(e.exp.args[0])
                        n = int(8 * (1 + e.exp.args[1].val))
                        deref = x86.Deref(n, 'r11')
                        
                        # Overlapping first step
                        steps = [x86.Movq(vec_var, x86.Reg('r11'))]

                        if e.exp.op == 'vectorSet':
                            val = si_atm(e.exp.args[2])
                            steps += [x86.Movq(val, deref),
                                    x86.Movq(x86.Int(0), assign_var)]
                        else:
                            steps += [x86.Movq(deref, assign_var)]

                        return steps

                elif isinstance(e.exp, cfun.FunRef):
                    return [x86.Leaq(x86.FunRef(e.exp.label), si_atm(e.var))]

                elif isinstance(e.exp, cfun.Call):

                    steps = []
                    
                    # Move args
                    for arg, reg in zip(e.exp.args, constants.parameter_passing_registers):
                        steps.append(x86.Movq(si_atm(arg), x86.Reg(reg)))

                    # Indirect callq
                    steps.append(x86.IndirectCallq(si_atm(e.exp.fun), len(e.exp.args)))

                    # Return
                    steps.append(x86.Movq(x86.Reg('rax'), assign_var))

                    return steps

                raise Exception('si_stmt Assign', e)

            elif isinstance(e, cfun.Collect):

                amt = x86.Int(int(e.amount))

                return [x86.Movq(x86.Reg('r15'), x86.Reg('rdi')),
                        x86.Movq(amt, x86.Reg('rsi')),
                        x86.Callq('collect')]

            raise Exception('si_stmt', e)

        def si_tail(e: cfun.Tail) -> List[x86.Instr]:

            if isinstance(e, cfun.Return):
                new_var = gensym('retvar')

                is_vec = isinstance(get_type(e.exp), VectorT)
                instrs = si_stmt(cfun.Assign(new_var, e.exp, is_vec=is_vec))

                return instrs + \
                    [x86.Movq(x86.Var(new_var), x86.Reg('rax')),
                        x86.Jmp(p.name + '_conclusion')]

            elif isinstance(e, cfun.Seq):
                return si_stmt(e.stmt) + si_tail(e.tail)

            elif isinstance(e, cfun.If):
                assert isinstance(e.test, cfun.Prim)
                e1, e2 = e.test.args
                return [x86.Cmpq(si_atm(e2), si_atm(e1)),
                        x86.JmpIf(e.test.op, e.then_label),
                        x86.Jmp(e.else_label)]

            elif isinstance(e, cfun.Goto):
                return [x86.Jmp(e.label)]

            elif isinstance(e, cfun.TailCall):
                
                steps = []
                
                # Move args
                for arg, reg in zip(e.args, constants.parameter_passing_registers):
                    steps.append(x86.Movq(si_atm(arg), x86.Reg(reg)))

                # Tail jump
                steps.append(x86.TailJmp(si_atm(e.fun), len(e.args)))

                return steps

            raise Exception('si_tail', e)
        
        start_steps = []
        for arg, reg in zip(p.args, constants.parameter_passing_registers):

            if isinstance(arg[1], VectorT):
                var_arg = x86.VecVar(arg[0])
            else:
                var_arg = x86.Var(arg[0])

            start_steps.append(x86.Movq(x86.Reg(reg), var_arg))

        blocks = {}
        for label, block in p.blocks.items():

            steps = si_tail(block)
            if label == 'start':
                steps = start_steps + steps
            
            if label in ['start', 'conclusion']:
                label = p.name + '_' + label

            blocks[label] = steps

        return x86.Program(blocks)
    
    outputs = {}
    for d in p.defs:
        outputs[d.name] = select_instructions_help(d)

    return outputs


##################################################
# uncover-live
##################################################

def uncover_live(program: Dict[str, x86.Program]) -> \
    Tuple[Dict[str, x86.Program],
          Dict[str, List[Set[x86.Var]]]]:
    """
    Performs liveness analysis. Returns the input program, plus live-after sets
    for its blocks.
    :param program: pseudo-x86 assembly program definitions
    :return: A tuple. The first element is the same as the input program. The
    second element is a dict of live-after sets. This dict maps each label in
    the program to a list of live-after sets for that label. The live-after 
    sets are in the same order as the label's instructions.
    """

    # Empty for all conclusion
    label_live: Dict[str, Set[x86.Var]] = {
        'conclusion': set()
    }

    for label in program:
        label_live[label + '_conclusion'] = set()
    
    # Blocks contain all labels for all functions
    blocks = {}
    for label in program:
        blocks.update(program[label].blocks)

    live_after_sets: Dict[str, List[Set[x86.Var]]] = {}

    def vars_arg(a: x86.Arg) -> Set[x86.Var]:
        if isinstance(a, (x86.Int, x86.Reg, x86.ByteReg,
                          x86.Deref, x86.GlobalVal, x86.FunRef)):
            return set()
        elif isinstance(a, (x86.Var, x86.VecVar)):
            return {a}
        else:
            raise Exception('ul_arg', a)

    def ul_instr(e: x86.Instr, live_after: Set[x86.Var]) -> Set[x86.Var]:
        if isinstance(e, (x86.Movq, x86.Movzbq, x86.Leaq)):
            return live_after.difference(vars_arg(e.e2)).union(vars_arg(e.e1))
        elif isinstance(e, (x86.Addq, x86.Xorq)):
            return live_after.union(vars_arg(e.e1).union(vars_arg(e.e2)))
        elif isinstance(e, (x86.Callq, x86.Retq, x86.Set)):
            return live_after
        elif isinstance(e, x86.Cmpq):
            return live_after.union(vars_arg(e.e1).union(vars_arg(e.e2)))
        elif isinstance(e, (x86.Jmp, x86.JmpIf)):
            if e.label not in label_live:
                ul_block(e.label)

            return live_after.union(label_live[e.label])
        
        elif isinstance(e, (x86.TailJmp, x86.IndirectCallq, x86.Negq)):
            return live_after.union(vars_arg(e.e1))

        else:
            raise Exception('ul_instr', e)
        
    def ul_block(label: str):
        instrs = blocks[label]

        current_live_after: Set[x86.Var] = set()

        local_live_after_sets = []
        for i in reversed(instrs):
            local_live_after_sets.append(current_live_after)
            current_live_after = ul_instr(i, current_live_after)

        live_after_sets[label] = list(reversed(local_live_after_sets))
        label_live[label] = current_live_after
    
    # Need to call on all starts
    for label in program:
        ul_block(label + '_start')

    return program, live_after_sets

##################################################
# build-interference
##################################################

class InterferenceGraph:
    """
    A class to represent an interference graph: an undirected graph where nodes 
    are x86.Arg objects and an edge between two nodes indicates that the two
    nodes cannot share the same locations.
    """
    graph: DefaultDict[x86.Arg, Set[x86.Arg]]

    def __init__(self):
        self.graph = defaultdict(lambda: set())

    def add_edge(self, a: x86.Arg, b: x86.Arg):
        if a != b:
            self.graph[a].add(b)
            self.graph[b].add(a)

    def neighbors(self, a: x86.Arg) -> Set[x86.Arg]:
        if a in self.graph:
            return self.graph[a]
        else:
            return set()

    def __str__(self):
        strings = []
        for k, v in dict(self.graph).items():
            if isinstance(k, (x86.Var, x86.VecVar)):
                t = ', '.join([print_ast(i) for i in v])
                tt = '\n      '.join(textwrap.wrap(t))
                strings.append(f'{print_ast(k)}: {tt}')
        lines = '\n  '.join(strings)
        return f'InterferenceGraph (\n  {lines}\n )\n'



def build_interference(inputs: Tuple[Dict[str, x86.Program],
                                     Dict[str, List[Set[x86.Var]]]]) -> \
        Tuple[Dict[str, x86.Program],
              Dict[str, InterferenceGraph]]:
    """
    Build the interference graph.
    :param inputs: A Tuple. The first element is a pseudo-x86 program. The 
    second element is the dict of live-after sets produced by the uncover-live 
    pass.
    :return: A Tuple. The first element is the same as the input program. 
    The second is a dict mapping each function name to its completed 
    interference graph.

    Will have one interference graph per function. Can run our previous function once per each function.

    Create an interference graph for each one
    - aadd support for `TailJmp` and `IndirectCallQ`
    """

    def build_interference_func(inputs: Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]) -> \
            Tuple[x86.Program, InterferenceGraph]:

        caller_saved_registers = [x86.Reg(r) for r in constants.caller_saved_registers]
        callee_saved_registers = [x86.Reg(r) for r in constants.callee_saved_registers]

        def vars_arg(a: x86.Arg) -> Set[x86.Var]:
            if isinstance(a, (x86.Int, x86.Deref, x86.GlobalVal)):
                return set()
            elif isinstance(a, (x86.Var, x86.VecVar, x86.Reg)):
                return {a}
            else:
                raise Exception('bi_arg', a)

        def reads_of(e: x86.Instr) -> Set[x86.Var]:
            if isinstance(e, (x86.Movq, x86.Leaq)):
                return vars_arg(e.e1)
            elif isinstance(e, (x86.Addq, x86.Xorq)):
                return vars_arg(e.e1).union(vars_arg(e.e2))
            elif isinstance(e, (x86.Callq, x86.Retq, x86.Jmp)):
                return set()
            else:
                raise Exception('reads_of', e)

        def writes_of(e: x86.Instr) -> Set[x86.Var]:
            if isinstance(e, (x86.Movq, x86.Leaq, x86.Addq, x86.Movzbq, x86.Xorq)):
                return vars_arg(e.e2)
            elif isinstance(e, x86.Negq):
                return vars_arg(e.e1)
            elif isinstance(e, (x86.Callq, x86.Retq, x86.Jmp)):
                return set()
            else:
                raise Exception('writes_of', e)

        def bi_instr(e: x86.Instr, live_after: Set[x86.Var], graph: InterferenceGraph):

            if isinstance(e, (x86.Movq, x86.Leaq, x86.Addq, x86.Negq, x86.Movzbq, x86.Xorq)):
                for v1 in writes_of(e):
                    for v2 in live_after:
                        graph.add_edge(v1, v2)
            
            elif isinstance(e, (x86.Callq, x86.TailJmp, x86.IndirectCallq)):
                for v in live_after:
                    for r in caller_saved_registers:
                        graph.add_edge(v, r)
                    if isinstance(v, x86.VecVar):
                        for r in callee_saved_registers:
                            graph.add_edge(v, r)
            elif isinstance(e, (x86.Retq, x86.Jmp, x86.Cmpq, x86.Jmp, x86.JmpIf, x86.Set)):
                pass
            
            else:
                raise Exception('bi_instr', e)

        def bi_block(instrs: List[x86.Instr], live_afters: List[Set[x86.Var]], graph: InterferenceGraph):
            for instr, live_after in zip(instrs, live_afters):
                bi_instr(instr, live_after, graph)

        program, live_after_sets = inputs
        blocks = program.blocks

        interference_graph = InterferenceGraph()

        for label in blocks.keys():
            bi_block(blocks[label], live_after_sets[label], interference_graph)

        return interference_graph


    program, live_after_sets = inputs
    igs = {}
    for func_name, prog in program.items():
        igs[func_name] = build_interference_func((prog, live_after_sets))

    return program, igs


##################################################
# allocate-registers
##################################################


Color = int
Coloring = Dict[x86.Var, Color]
Saturation = Set[Color]

def allocate_registers(inputs: Tuple[Dict[str, x86.Program],
                                     Dict[str, InterferenceGraph]]) -> \
    Dict[str, Tuple[x86.Program, int, int]]:
    """
    Assigns homes to variables in the input program. Allocates registers and 
    stack locations as needed, based on a graph-coloring register allocation 
    algorithm.
    :param inputs: A Tuple. The first element is the pseudo-x86 program. The
    second element is a dict mapping function names to interference graphs.

    :return: A dict mapping each function name to a Tuple. The first element
    of each tuple is an x86 program (with no variable references). The second
    element is the number of bytes needed in regular stack locations. The third
    element is the number of variables spilled to the root (shadow) stack.
    """

    def allocate_registers_func(inputs: Tuple[x86.Program, InterferenceGraph]) -> \
        Tuple[x86.Program, int, int]:

        ## Functions for listing the variables in the program
        def vars_arg(a: x86.Arg) -> Set[x86.Var]:
            if isinstance(a, (x86.Int, x86.Reg, x86.ByteReg,
                              x86.GlobalVal, x86.Deref, x86.FunRef)):
                return set()
            elif isinstance(a, x86.Var):
                return {a}
            else:
                raise Exception('vars_arg', a)

        def vars_instr(e: x86.Instr) -> Set[x86.Var]:
            if isinstance(e, (x86.Movq, x86.Addq, x86.Cmpq, x86.Leaq, x86.Movzbq, x86.Xorq)):
                return vars_arg(e.e1).union(vars_arg(e.e2))
            elif isinstance(e, (x86.Set, x86.TailJmp, x86.IndirectCallq, x86.Negq)):
                return vars_arg(e.e1)
            elif isinstance(e, (x86.Callq, x86.Retq, x86.Jmp, x86.JmpIf)):
                return set()
            else:
                raise Exception('vars_instr', e)

        # Defines the set of registers to use
        register_locations = [x86.Reg(r) for r in constants.caller_saved_registers + constants.callee_saved_registers]
        
        # Mapping from color to register
        color_map = dict(enumerate(register_locations))

        ## Functions for graph coloring
        def color_graph(local_vars: Set[x86.Var], interference_graph: InterferenceGraph) -> Coloring:

            coloring = {}

            to_color = local_vars.copy()
            saturation_sets = {x: set() for x in local_vars}

            # init the saturation sets
            for color, register in enumerate(register_locations):
                for neighbor in interference_graph.neighbors(register):
                    if isinstance(neighbor, x86.Var):
                        saturation_sets[neighbor].add(color)

            while to_color:
                x = max(to_color, key=lambda x: len(saturation_sets[x]))
                to_color.remove(x)

                x_color = next(i for i in itertools.count() if i not in saturation_sets[x])
                coloring[x] = x_color

                for y in interference_graph.neighbors(x):
                    if isinstance(y, x86.Var):
                        saturation_sets[y].add(x_color)

            return coloring

        # Functions for allocating registers
        def make_stack_loc(offset):
            return x86.Deref(-(offset * 8), 'rbp')
        def make_root_stack_loc(offset):
            return x86.Deref(-(offset * 8), 'r15')

        # Functions for replacing variables with their homes
        homes: Dict[str, x86.Arg] = {}

        def ah_arg(a: x86.Arg) -> x86.Arg:
            if isinstance(a, (x86.Int, x86.Reg, x86.ByteReg,
                              x86.GlobalVal, x86.Deref, x86.FunRef)):
                return a
            elif isinstance(a, x86.Var):
                return homes[a]
            else:
                raise Exception('ah_arg', a)

        def ah_instr(e: x86.Instr) -> x86.Instr:

            if isinstance(e, (x86.Movq, x86.Addq, x86.Cmpq,
                              x86.Movzbq, x86.Xorq, x86.Leaq)):
                return e.__class__(ah_arg(e.e1), ah_arg(e.e2))
            elif isinstance(e, x86.Set):
                return x86.Set(e.cc, ah_arg(e.e1))
            elif isinstance(e, (x86.Callq, x86.Retq, x86.Jmp, x86.JmpIf)):
                return e
            elif isinstance(e, (x86.TailJmp, x86.IndirectCallq)):
                return e.__class__(ah_arg(e.e1), e.num_args)
            elif isinstance(e, x86.Negq):
                return x86.Negq(ah_arg(e.e1))
            else:
                raise Exception('ah_instr', e)

        def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
            return [ah_instr(i) for i in instrs]

        def align(num_bytes: int) -> int:
            if num_bytes % 16 == 0:
                return num_bytes
            else:
                return num_bytes + (16 - (num_bytes % 16))

        # Main body of the pass
        program, interference_graph = inputs
        blocks = program.blocks

        local_vars = set()
        for block in blocks.values():
            for instr in block:
                local_vars = local_vars.union(vars_instr(instr))

        coloring = color_graph(local_vars, interference_graph)

        color_map_root_stack = color_map.copy()
        stack_spilled, root_stack_spilled = 0, 0

        for v in local_vars:
            
            color = coloring[v]
            
            if isinstance(v, x86.VecVar):
                
                if color not in color_map_root_stack:
                    root_stack_spilled += 1
                    color_map_root_stack[color] = make_root_stack_loc(root_stack_spilled)
                
                homes[v] = color_map_root_stack[color]
            
            else:

                if color not in color_map:
                    stack_spilled += 1
                    color_map[color] = make_stack_loc(stack_spilled)
                
                homes[v] = color_map[color]

        blocks = program.blocks
        new_blocks = {label: ah_block(block) for label, block in blocks.items()}
        
        return x86.Program(new_blocks), align(8 * stack_spilled), root_stack_spilled


    program, graphs = inputs
    ret_program = {}

    for label in program:
        ret_program[label] = allocate_registers_func((program[label], graphs[label]))

    return ret_program



##################################################
# patch-instructions
##################################################

def patch_instructions(inputs: Dict[str, Tuple[x86.Program, int, int]]) -> \
    Dict[str, Tuple[x86.Program, int, int]]:
    """
    Patches instructions with two memory location inputs, using %rax as a 
    temporary location.
    :param inputs: A dict mapping each function name to a Tuple. The first
    element of each tuple is an x86 program. The second element is the stack
    space in bytes. The third is the number of variables spilled to the root
    stack.
    :return: A Tuple. The first element is the patched x86 program. The second
    and third elements stay the same.
    """

    def patch_instructions_func(inputs: Tuple[x86.Program, int, int]) -> Tuple[x86.Program, int, int]:

        def pi_instr(e: x86.Instr) -> List[x86.Instr]:
            if isinstance(e, x86.Movq) and \
                    isinstance(e.e1, x86.Deref) and \
                    isinstance(e.e2, x86.Deref):
                return [x86.Movq(e.e1, x86.Reg('rax')),
                        x86.Movq(x86.Reg('rax'), e.e2)]
            elif isinstance(e, x86.Addq) and \
                    isinstance(e.e1, x86.Deref) and \
                    isinstance(e.e2, x86.Deref):
                return [x86.Movq(e.e1, x86.Reg('rax')),
                        x86.Addq(x86.Reg('rax'), e.e2)]
            elif isinstance(e, x86.Cmpq) and \
                    isinstance(e.e2, x86.Int):
                return [x86.Movq(e.e2, x86.Reg('rax')),
                        x86.Cmpq(e.e1, x86.Reg('rax'))]
            elif isinstance(e, x86.Leaq) and \
                    isinstance(e.e2, x86.Deref):
                    return [x86.Movq(e.e2, x86.Reg('rax')),
                            x86.Leaq(e.e1, x86.Reg('rax'))]
            elif isinstance(e, (x86.Callq, x86.Retq, x86.Jmp, x86.JmpIf,
                                x86.Movq, x86.Addq, x86.Cmpq, x86.Set,
                                x86.Movzbq, x86.Xorq, x86.Leaq, x86.Negq)):
                return [e]

            elif isinstance(e, (x86.IndirectCallq, x86.TailJmp)):
                return [x86.Movq(e.e1, x86.Reg('rax')),
                        e.__class__(x86.Reg('rax'), e.num_args)]
            
            else:
                raise Exception('pi_instr', e)

        def pi_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
            new_instrs = [pi_instr(i) for i in instrs]
            flattened = [val for sublist in new_instrs for val in sublist]
            return flattened

        program, stack_size, shadow_stack_size = inputs
        blocks = program.blocks
        new_blocks = {label: pi_block(block) for label, block in blocks.items()}
        return (x86.Program(new_blocks), stack_size, shadow_stack_size)
    

    outputs = {}
    for key in inputs:
        outputs[key] = patch_instructions_func(inputs[key])

    return outputs



##################################################
# print-x86
##################################################

def print_x86(inputs: Dict[str, Tuple[x86.Program, int, int]]) -> str:
    """
    Prints an x86 program to a string.
    :param inputs: A dict mapping each function name to a Tuple. The first
    element of the Tuple is an x86 program. The second element is the stack
    space in bytes. The third is the number of variables spilled to the
    root stack.
    :return: A string, ready for gcc.
    """

    def print_x86_func(name: str, inputs: Tuple[x86.Program, int, int]) -> str:
        """
        Prints an x86 program to a string.
        :param inputs: A Tuple. The first element is the x86 program. The second element is the stack space in bytes.
        :return: A string, ready for gcc.
        """

        bs = [f'popq %{c}' for c in constants.callee_saved_registers[::-1]]
        bs.append('popq %rbp')
        rq = '\n  '.join(bs)

        def print_arg(a: x86.Arg) -> str:
            if isinstance(a, x86.Int):
                return f'${a.val}'
            elif isinstance(a, (x86.Reg, x86.ByteReg)):
                return f'%{a.val}'
            elif isinstance(a, x86.Var):
                return f'#{a.var}'
            elif isinstance(a, x86.Deref):
                return f'{a.offset}(%{a.val})'
            elif isinstance(a, x86.GlobalVal):
                return f'{a.val}(%rip)'
            elif isinstance(a, x86.FunRef):
                return f'{a.label}(%rip)'
            else:
                raise Exception('print_arg', a)

        ccs = {
            '==': 'e',
            '<' : 'l',
            '<=': 'le',
            '>' : 'g',
            '>=': 'ge'
        }

        def print_instr(e: x86.Instr) -> str:
            if isinstance(e, x86.Movq):
                return f'movq {print_arg(e.e1)}, {print_arg(e.e2)}'
            elif isinstance(e, x86.Addq):
                return f'addq {print_arg(e.e1)}, {print_arg(e.e2)}'
            elif isinstance(e, x86.Negq):
                return f'negq {print_arg(e.e1)}'
            elif isinstance(e, x86.Cmpq):
                return f'cmpq {print_arg(e.e1)}, {print_arg(e.e2)}'
            elif isinstance(e, x86.Movzbq):
                return f'movzbq {print_arg(e.e1)}, {print_arg(e.e2)}'
            elif isinstance(e, x86.Xorq):
                return f'xorq {print_arg(e.e1)}, {print_arg(e.e2)}'
            elif isinstance(e, x86.Callq):
                return f'callq {e.label}'
            elif isinstance(e, x86.Retq):
                return f'retq'
            elif isinstance(e, x86.Jmp):
                return f'jmp {e.label}'
            elif isinstance(e, x86.Leaq):
                return f'leaq {print_arg(e.e1)}, {print_arg(e.e2)}'
            elif isinstance(e, x86.JmpIf):
                cc = ccs[e.cc]
                return f'j{cc} {e.label}'
            elif isinstance(e, x86.Set):
                return f'set{e.cc} {print_arg(e.e1)}'
            
            elif isinstance(e, x86.TailJmp):

                if name == 'main':
                    return f'callq *{print_arg(e.e1)}\n  jmp main_conclusion'

                return f"""
  addq $0, %rsp
  subq $0, %r15
  {rq}
  jmp *{print_arg(e.e1)}

"""

            elif isinstance(e, x86.IndirectCallq):
                return f'callq *{print_arg(e.e1)}'

            else:
                raise Exception('print_instr', e)

        def print_block(label: str, instrs: List[x86.Instr]) -> str:
            name = f'{label}:\n'
            instr_strs = '\n'.join(['  ' + print_instr(i) for i in instrs])
            return name + instr_strs

        program, stack_size, shadow_stack_size = inputs
        blocks = program.blocks
        block_instrs = '\n'.join([print_block(label, block) for label, block in blocks.items()])
        
        if name == 'main':
            main_init = f"""
  movq ${constants.root_stack_size}, %rdi
  movq ${constants.heap_size}, %rsi
  callq initialize
  movq rootstack_begin(%rip), %r15
"""

            main_conc_end = f"""
  movq %rax, %rdi
  callq print_int
  movq $0, %rax
"""
        else:
            main_init = ''
            main_conc_end = ''

        pq = '\n  '.join([f'pushq %{c}' for c in constants.callee_saved_registers])
        repeat = 'movq $0, (%r15)\n  addq $8, %r15\n  ' * shadow_stack_size

        program = f"""
  .globl {name}
{name}:
  pushq %rbp
  movq %rsp, %rbp
  subq ${stack_size}, %rsp
  {pq}
{main_init}
  {repeat}
  jmp {name}_start
{block_instrs}
{name}_conclusion:
  {main_conc_end}
  addq ${stack_size}, %rsp
  subq ${int(shadow_stack_size*8)}, %r15
  {rq}
  retq
"""

        return program
    
    final_program = ''
    for name in inputs:
        final_program += print_x86_func(name, inputs[name])

    return final_program




##################################################
# Compiler definition
##################################################

compiler_passes = {
    'typecheck': typecheck,
    'shrink': shrink,
    'uniquify': uniquify,
    'flatten lambda': flatten_lambda,
    'reveal functions': reveal_functions,
    'convert to closure': convert_to_closure,
    'limit functions': limit_functions,
    'expose allocation': expose_alloc,
    'remove complex opera*': rco,
    'explicate control': explicate_control,
    'select instructions': select_instructions,
    'uncover live': uncover_live,
    'build interference': build_interference,
    'allocate registers': allocate_registers,
    'patch instructions': patch_instructions,
    'print x86': print_x86
}

def run_compiler(s: str, logging=False) -> str:
    """
    Run the compiler on an input program.
    :param s: An Rlam program, as a string.
    :param logging: Whether or not to print out debugging information.
    :return: An x86 program, as a string
    """
    current_program = parse_rlam(s)

    if logging == True:
        print()
        print('==================================================')
        print(' Input program')
        print('==================================================')
        print()
        print(print_ast(current_program))

    for pass_name, pass_fn in compiler_passes.items():
        current_program = pass_fn(current_program)

        if logging == True:
            print()
            print('==================================================')
            print(f' Output of pass: {pass_name}')
            print('==================================================')
            print()
            print(print_ast(current_program))

    assert isinstance(current_program, str)
    return current_program


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            program = f.read()
            x86_program = run_compiler(program, logging=True)

            with open(file_name + '.s', 'w') as output_file:
                output_file.write(x86_program)
