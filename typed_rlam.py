from dataclasses import dataclass
from cs202_support.base_ast import AST, RType
from typing import List, Tuple

##################################################
# Types: Typed Rlam
##################################################

@dataclass
class RlamType(RType):
    pass

@dataclass
class IntT(RlamType):
    pass

@dataclass
class BoolT(RlamType):
    pass

@dataclass
class VoidT(RlamType):
    pass

@dataclass
class VectorT(RlamType):
    types: List[RlamType]

@dataclass
class FunT(RlamType):
    arg_types: List[RlamType]
    return_type: RlamType

@dataclass
class DynamT(FunT):
    arg_types: List[RlamType]
    return_type: RlamType
    closure_args: List[Tuple[str, RlamType]]


##################################################
# Abstract Syntax Trees: Typed Rlam
##################################################

@dataclass
class RlamExpT(AST):
    pass

@dataclass
class IntTE(RlamExpT):
    val: int

@dataclass
class BoolTE(RlamExpT):
    val: bool

@dataclass
class VoidTE(RlamExpT):
    pass

@dataclass
class VarTE(RlamExpT):
    var: str
    typ: RlamType

@dataclass
class GlobalValTE(RlamExpT):
    var: str

@dataclass
class LetTE(RlamExpT):
    x: str
    e1: RlamExpT
    body: RlamExpT

@dataclass
class PrimTE(RlamExpT):
    op: str
    args: List[RlamExpT]
    typ: RlamType

@dataclass
class IfTE(RlamExpT):
    e1: RlamExpT
    e2: RlamExpT
    e3: RlamExpT
    typ: RlamType

@dataclass
class FuncallTE(RlamExpT):
    fun: RlamExpT
    args: List[RlamExpT]
    typ: RlamType

@dataclass
class FunRefTE(RlamExpT):
    name: str
    typ: FunT

@dataclass
class DynamTE(RlamExpT):
    args: List[Tuple[str, RlamType]]
    body: RlamExpT
    closure_args: List[Tuple[str, RlamType]]
    output_type: RlamType

@dataclass
class LambdaTE(RlamExpT):
    args: List[Tuple[str, RlamType]]
    output_type: RlamType
    body: RlamExpT

@dataclass
class RlamDefT(AST):
    name: str
    args: List[Tuple[str, RlamType]]
    output_type: RlamType
    body: RlamExpT

@dataclass
class RlamProgramT(AST):
    defs: List[RlamDefT]
    body: RlamExpT
