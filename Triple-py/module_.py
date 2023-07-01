import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_

assert "module_" == __name__
module_ = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "_module._default"
    @staticmethod
    def Triple(x):
        r: int = int(0)
        d_0_y_: int
        d_0_y_ = (2) * (x)
        r = (x) + (d_0_y_)
        return r

    @staticmethod
    def TripleIf(x):
        r: int = int(0)
        if (x) == (0):
            r = 0
        elif True:
            d_1_y_: int
            d_1_y_ = (2) * (x)
            r = (x) + (d_1_y_)
        return r

    @staticmethod
    def TripleOver(x):
        r: int = int(0)
        if (x) < (18):
            d_2_a_: int
            d_3_b_: int
            rhs0_: int = (2) * (x)
            rhs1_: int = (4) * (x)
            d_2_a_ = rhs0_
            d_3_b_ = rhs1_
            r = _dafny.euclidian_division((d_2_a_) + (d_3_b_), 2)
        elif (0) <= (x):
            d_4_y_: int
            d_4_y_ = (2) * (x)
            r = (x) + (d_4_y_)
        elif True:
            raise Exception("unreachable alternative")
        return r

    @staticmethod
    def TripleConditions(x):
        r: int = int(0)
        d_5_y_: int
        d_5_y_ = _dafny.euclidian_division(x, 2)
        r = (6) * (d_5_y_)
        return r

    @staticmethod
    def Caller():
        d_6_t_: int
        out0_: int
        out0_ = module_.default__.TripleConditions(18)
        d_6_t_ = out0_

