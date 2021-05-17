from dataclasses import dataclass
from typing import List, Set, Dict, Tuple
from cs202_support.base_ast import AST
import typed_rlam

@dataclass
class Atm(AST):
    pass

@dataclass
class Int(Atm):
    val: int

@dataclass
class Bool(Atm):
    val: bool

@dataclass
class Void(Atm):
    pass

@dataclass
class Var(Atm):
    var: str
    typ: typed_rlam.RlamType

@dataclass
class GlobalVal(Atm):
    val: str

@dataclass
class Exp(AST):
    pass

@dataclass
class AtmExp(Exp):
    atm: Atm

@dataclass
class Prim(Exp):
    op: str
    args: List[Atm]
    typ: typed_rlam.RlamType

@dataclass
class FunRef(Exp):
    label: str

@dataclass
class Call(Exp):
    fun: Atm
    args: List[Atm]
    typ: typed_rlam.RlamType


@dataclass
class Stmt(AST):
    pass

@dataclass
class Assign(Stmt):
    var: str
    exp: Exp
    is_vec: bool

@dataclass
class Collect(Stmt):
    amount: int

@dataclass
class Tail(AST):
    pass

@dataclass
class Return(Tail):
    exp: Exp

@dataclass
class Goto(Tail):
    label: str

@dataclass
class If(Tail):
    test: Exp
    then_label: str
    else_label: str

@dataclass
class TailCall(Tail):
    fun: Atm
    args: List[Atm]
    typ: typed_rlam.RlamType


@dataclass
class Seq(Tail):
    stmt: Stmt
    tail: Tail

@dataclass
class Def(AST):
    name: str
    args: List[Tuple[str, typed_rlam.RlamType]]
    output_type: typed_rlam.RlamType
    blocks: Dict[str, Tail]

@dataclass
class Program(AST):
    defs: List[Def]
