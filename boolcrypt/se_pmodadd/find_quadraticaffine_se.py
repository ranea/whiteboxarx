"""Find quadratic-affine self-equivalences (QASE) of the permuted modular addition."""
import collections
import itertools
import math
import sys
import datetime

from boolcrypt.utilities import (
    str2bp, get_time, get_smart_print, BooleanPolynomialRing, get_symbolic_anf,
    get_anf_coeffmatrix_str, matrix2anf, anf2matrix, get_ct_coeff, substitute_anf,
)
from boolcrypt.functionalequations import find_fixed_vars
from boolcrypt.cczselfequivalence import find_self_equivalence
from boolcrypt.modularaddition import get_modadd_anf, get_ccz_modadd_anf, get_admissible_mapping

import sage.all


def shape(wordsize, prefix_symbolic_anf, verbose, filename):
    """Symbolic shape of the CCZ QASE of the "H" quadratic CCZ of the permuted modular addition."""
    ws = wordsize

    assert ws >= 4

    if isinstance(prefix_symbolic_anf, str):
        prefix_symbolic_anf = [prefix_symbolic_anf]
    assert len(prefix_symbolic_anf) in [1, 2], str(len(prefix_symbolic_anf))

    smart_print = get_smart_print(filename)

    var2val = collections.OrderedDict()

    varnames = []
    set_final_varnames = set()

    # ----- NON-LINEAR COEFFS -----

    # A = common coefficients excluding  {(0, 2*ws), (2*ws, 3*ws)}
    # B = type I row with non-zero coeffs {(0, 2*ws), (2*ws, 3*ws)}
    # C = type II row with non-zero coeffs {(0, 2*ws), (0, 2*ws + 1), (2*ws, 3*ws - (ws - 1)), (2*ws, 3*ws), (2*ws + 1, 3*ws)}
    # D = type III row with no zero coeffs
    # All C share A0, All D share A1, and A0 and A1 share all coeffs except (0, 2*ws + 1), (2*ws, 3*ws - (ws - 1)), (2*ws + 1, 3*ws)
    # In B and C, column (0, 2*ws) is the same as column (2*ws, 3*ws)

    positions_B = {(0, 2*ws), (2*ws, 3*ws)}
    positions_C = {(0, 2*ws), (0, 2*ws + 1), (2*ws, 3*ws - (ws - 1)), (2*ws, 3*ws), (2*ws + 1, 3*ws)}

    class MyOrderedDict(collections.OrderedDict):
        def __setitem__(self, key, value):
            assert key not in self
            return super().__setitem__(key, value)

    fixed_A0_coeffs = MyOrderedDict()
    for index_vars in itertools.combinations(range(4*ws), 2):
        varname = "aa{}" + "_{}" * len(index_vars)
        varname = varname.format("A0", *index_vars)

        j = index_vars
        if (j[0] == 0 and (ws - 1 <= j[1] <= 2 * ws - 1 or 2 * ws + 2 <= j[1] <= 4 * ws - 4)) or \
                (j[0] in [ws - 3, ws - 2] and ws <= j[1] <= 2 * ws - 1) or \
                (ws >= 5 and 1 <= j[0] <= ws - 4 and ws - 1 <= j[1] <= 4 * ws - 4) or \
                (j[0] == ws - 1 and ws <= j[1] <= 4 * ws - 4) or \
                (ws <= j[0] <= 2 * ws - 1 and j[0] + 1 <= j[1] <= 4 * ws - 1) or \
                (j[0] in [2 * ws, 2 * ws + 1] and 2 * ws + 2 <= j[1] <= 3 * ws - 1) or \
                (ws >= 5 and j[0] in [2 * ws, 2 * ws + 1] and 3 * ws + 1 <= j[1] <= 4 * ws - 4) or \
                (2 * ws + 2 <= j[0] <= 4 * ws - 6 and j[0] + 1 <= j[1] <= 4 * ws - 4):
            fixed_A0_coeffs[varname] = 0

        elif (0 <= j[0] <= ws - 4 and j[1] in [4 * ws - 1]) or \
                (ws >= 5 and j[0] in [0] and 1 <= j[1] <= ws - 4) or \
                (ws - 3 <= j[0] <= ws - 1 and j[1] in [3 * ws + j[0]]) or \
                (2 * ws <= j[0] <= 4 * ws - 4 and j[1] in [4 * ws - 1]) or \
                (j[0] in [4 * ws - 5] and j[1] in [4 * ws - 4]):
            fixed_A0_coeffs[varname] = 0

        #   w = 4, 5: (),
        #   w = 6:  (aaA0_1_2, 0),
        #   w = 7:  (aaA0_1_2, 0), (aaA0_1_3, 0),
        #           (aaA0_2_3, 0),
        #   w = 8:  (aaA0_1_2, 0), (aaA0_1_3, 0), (aaA0_1_4, 0),
        #           (aaA0_2_3, 0), (aaA0_2_4, 0),
        #           (aaA0_3_4, 0),
        elif 1 <= j[0] <= ws - 5 and j[0] < j[1] <= ws - 4:
            fixed_A0_coeffs[varname] = 0

    for i in range(0, ws - 2):
        fixed_A0_coeffs[f"aaA0_{i}_{4*ws-2}"] = f"aaA0_{i}_{ws-2}"

    for i in range(0, ws - 3):
        fixed_A0_coeffs[f"aaA0_{i}_{4*ws-3}"] = f"aaA0_{i}_{ws-3}"

    for i in range(0, ws - 4):
        fixed_A0_coeffs[f"aaA0_{ws-3}_{2*ws+1+i}"] = f"aaA0_{1+i}_{ws-3}"

    fixed_A0_coeffs[f"aaA0_{ws-3}_{3*ws-1}"] = f"aaA0_{ws-3}_{ws-1}"

    for i in range(0, ws - 3):
        fixed_A0_coeffs[f"aaA0_{ws-3}_{3*ws+i}"] = f"aaA0_{i}_{ws-3}"

    fixed_A0_coeffs[f"aaA0_{ws-3}_{4*ws-1}"] = f"aaA0_{ws-3}_{ws-1}"

    for i in range(0, ws - 4):
        fixed_A0_coeffs[f"aaA0_{ws-2}_{2*ws+1+i}"] = f"aaA0_{1+i}_{ws-2}"

    fixed_A0_coeffs[f"aaA0_{ws-2}_{3*ws-1}"] = f"aaA0_{ws-2}_{ws-1}"
    fixed_A0_coeffs[f"aaA0_{ws-2}_{3*ws}"] = f"aaA0_{0}_{ws-2}"

    for i in range(0, ws - 3):
        fixed_A0_coeffs[f"aaA0_{ws-2}_{3*ws+1+i}"] = f"aaA0_{1+i}_{ws-2}"

    fixed_A0_coeffs[f"aaA0_{ws-2}_{4*ws-1}"] = f"aaA0_{ws-2}_{ws-1}"

    fixed_A0_coeffs[f"aaA0_{ws-1}_{4*ws-3}"] = f"aaA0_{ws-3}_{ws-1}"

    fixed_A0_coeffs[f"aaA0_{ws-1}_{4*ws-2}"] = f"aaA0_{ws-2}_{ws-1}"

    fixed_A0_coeffs[f"aaA0_{2*ws}_{4*ws-3}"] = f"aaA0_{ws-3}_{2*ws}"

    fixed_A0_coeffs[f"aaA0_{2*ws}_{4*ws-2}"] = f"aaA0_{ws-2}_{2*ws}"

    # ignore for w=4 (aaA0_9_13, aaA0_1_9), (aaA0_9_14, aaA0_2_9),
    fixed_A0_coeffs[f"aaA0_{2*ws+1}_{3*ws}"] = f"aaA0_{0}_{2*ws+1}"

    for i in range(0, ws - 4):
        fixed_A0_coeffs[f"aaA0_{2*ws+1+i}_{4*ws-3}"] = f"aaA0_{1+i}_{ws-3}"
        fixed_A0_coeffs[f"aaA0_{2*ws+1+i}_{4*ws-2}"] = f"aaA0_{1+i}_{ws-2}"

    # ignore for w=4 (aaA0_10_13, aaA0_1_10), (aaA0_10_14, aaA0_2_10),

    if ws >= 5:
        #   (aaA0_12_17, aaA0_2_12), (aaA0_12_18, aaA0_3_12),
        #       (aaA0_15_21, aaA0_3_15), (aaA0_15_22, aaA0_4_15),
        #           (aaA0_18_26, aaA0_5_18), ...
        fixed_A0_coeffs[f"aaA0_{3*ws-3}_{4*ws-3}"] = f"aaA0_{ws-3}_{3*ws-3}"
        fixed_A0_coeffs[f"aaA0_{3*ws-3}_{4*ws-2}"] = f"aaA0_{ws-2}_{3*ws-3}"

    if ws >= 5:
        fixed_A0_coeffs[f"aaA0_{3*ws-2}_{4*ws-3}"] = f"aaA0_{ws-3}_{3*ws-2}"
        fixed_A0_coeffs[f"aaA0_{3*ws-2}_{4*ws-2}"] = f"aaA0_{ws-2}_{3*ws-2}"

    fixed_A0_coeffs[f"aaA0_{3*ws-1}_{4*ws-3}"] = f"aaA0_{ws-3}_{ws-1}"

    fixed_A0_coeffs[f"aaA0_{3*ws-1}_{4*ws-2}"] = f"aaA0_{ws-2}_{ws-1}"

    for i in range(0, ws - 3):
        fixed_A0_coeffs[f"aaA0_{3*ws+i}_{4*ws-3}"] = f"aaA0_{i}_{ws-3}"

    for i in range(0, ws - 2):
        fixed_A0_coeffs[f"aaA0_{3*ws+i}_{4*ws-2}"] = f"aaA0_{i}_{ws-2}"

    fixed_A0_coeffs[f"aaA0_{4*ws-3}_{4*ws-1}"] = f"aaA0_{ws-3}_{ws-1}"

    fixed_A0_coeffs[f"aaA0_{4*ws-2}_{4*ws-1}"] = f"aaA0_{ws-2}_{ws-1}"

    fixed_A1_coeffs = MyOrderedDict()
    for index_vars in itertools.combinations(range(4*ws), 2):
        # ('aaA1_0_{2*ws+1}', 0), ('aaA1_{2*ws}_{2*ws+1}', 0), ('aaA1_{2*ws+1}_{3*ws}', 0)]
        if index_vars in [(0, 2*ws+1), (2*ws, 2*ws+1), (2*ws+1, 3*ws)]:
            varname = "aa{}" + "_{}" * len(index_vars)
            varname = varname.format("A1", *index_vars)
            fixed_A1_coeffs[varname] = 0

    fixed_B_coeffs = MyOrderedDict()
    for i in range(0, ws - 4):
        fixed_B_coeffs[f"aaB{2+i}_{0}_{2*ws}"] = f"aaB{1}_{0}_{2*ws}"

    #

    index_vars2coeffs_A0 = MyOrderedDict()
    index_vars2coeffs_A1 = MyOrderedDict()
    for index_vars in itertools.combinations(range(4*ws), 2):
        # in the i-component, ai_j[0]_..._j[-1] is the coeff with x_j[0]*...*x_j[-1]
        coeff = "aa{}" + "_{}" * len(index_vars)
        coeff = coeff.format("A0", *index_vars)
        coeff = fixed_A0_coeffs.get(coeff, coeff)
        if index_vars not in positions_B:
            index_vars2coeffs_A0[index_vars] = coeff
            if index_vars not in positions_C:
                index_vars2coeffs_A1[index_vars] = coeff
            else:
                coeff = "aa{}" + "_{}" * len(index_vars)
                coeff = coeff.format("A1", *index_vars)
                coeff = fixed_A1_coeffs.get(coeff, coeff)
                index_vars2coeffs_A1[index_vars] = coeff

    def get_B_component(index, prefix="B"):
        coeffs = []
        for index_vars in itertools.combinations(range(4*ws), 2):
            if index_vars == (2*ws, 3*ws):
                index_vars = (0, 2*ws)
            varname = "aa{}{}" + "_{}" * len(index_vars)
            varname = varname.format(prefix, index, *index_vars)
            varname = fixed_B_coeffs.get(varname, varname)
            if index_vars in positions_B:
                coeffs.append(varname)
            else:
                coeffs.append(0)
        return coeffs

    def get_C_component(index, prefix="C"):
        coeffs = []
        for index_vars in itertools.combinations(range(4*ws), 2):
            if index_vars == (2*ws, 3*ws):
                index_vars = (0, 2*ws)
            varname = "aa{}{}" + "_{}" * len(index_vars)
            varname = varname.format(prefix, index, *index_vars)
            if index_vars in positions_B:
                coeffs.append(varname)
            elif index_vars in positions_C:
                coeffs.append(index_vars2coeffs_A0[index_vars])
            else:
                coeffs.append(0)
        return coeffs

    def get_D_component(index, prefix="D"):
        coeffs = []
        for index_vars in itertools.combinations(range(4*ws), 2):
            if index_vars == (2*ws, 3*ws):
                index_vars = (0, 2*ws)
            varname = "aa{}{}" + "_{}" * len(index_vars)
            varname = varname.format(prefix, index, *index_vars)
            if index_vars in positions_B:
                coeffs.append(varname)
            else:
                coeffs.append(index_vars2coeffs_A1[index_vars])
        return coeffs

    # {ws}zero
    # B0,      C0, B1,      ..., B{ws-3}, D0
    # B0,      C0, B1,      ..., B{ws-3}, D0
    # B{ws-2}, C1, {ws-3}zero,            D1
    #  - between B1 and B{ws-3}, there are {ws-3} components

    B_rows = [get_B_component(i, "B") for i in range(ws - 1)]
    C0, C1 = get_C_component(0, "C"), get_C_component(1, "C")
    D0, D1 = get_D_component(0, "D"), get_D_component(1, "D")

    for component in B_rows + [C0, C1, D0, D1]:
        for coeff in component:
            if isinstance(coeff, str) and coeff not in varnames:
                varnames.append(coeff)

    zero_component = [0 for _ in itertools.combinations(range(4*ws), 2)]

    nl_matrix = []
    last_B_row = -1
    for index_comp in range(4*ws):
        if 0 <= index_comp < ws or 3*ws + 2 <= index_comp < 4*ws - 1:
            component = zero_component
        elif index_comp in [ws, 2*ws]:
            component = B_rows[0]
        elif index_comp in [ws + 1, 2*ws + 1]:
            component = C0
        elif ws + 2 <= index_comp < 2*ws - 1 or 2*ws + 2 <= index_comp < 3*ws - 1:
            component = B_rows[(index_comp % ws) - 1]
            last_B_row = max(last_B_row, (index_comp % ws) - 1)
        elif index_comp in [2*ws - 1, 3*ws - 1]:
            component = D0
        elif index_comp in [3*ws]:
            component = B_rows[last_B_row + 1]
            last_B_row = None
        elif index_comp in [3*ws + 1]:
            component = C1
        elif index_comp in [4*ws - 1]:
            component = D1
        else:
            raise ValueError(f"invalid index_comp {index_comp}")

        nl_matrix.append(component)

    if verbose:
        smart_print("non-linear shape:")
        nl_matrix_sr = [
            [sage.all.symbolic_expression(f"x{j[0]}*x{j[1]}") for j in itertools.combinations(range(4*ws), 2)]
        ]
        for row in nl_matrix:
            nl_matrix_sr.append([sage.all.symbolic_expression(coeff) for coeff in row])
        nl_matrix_sr = sage.all.matrix(sage.all.SR, len(nl_matrix_sr), len(nl_matrix_sr[0]), nl_matrix_sr)
        nl_matrix_sr.subdivide(row_lines=[1, 1+ ws, 1 + 2*ws, 1 + 3*ws])
        smart_print(nl_matrix_sr, "\n")

    for index_comp in range(4*ws):
        counter = 0
        for index_vars in itertools.combinations(range(4*ws), 2):
            varname = "{}{}" + "_{}" * len(index_vars)
            if len(prefix_symbolic_anf) == 1 or index_comp < 2 * ws:
                varname = varname.format(prefix_symbolic_anf[0], index_comp, *index_vars)
            else:
                varname = varname.format(prefix_symbolic_anf[1], index_comp - (2*ws), *index_vars)
            assert varname not in var2val
            if nl_matrix[index_comp][counter] not in [0, 1]:
                assert "+" not in nl_matrix[index_comp][counter] and "*" not in nl_matrix[index_comp][counter]
                set_final_varnames.add(nl_matrix[index_comp][counter])
            var2val[varname] = nl_matrix[index_comp][counter]
            counter += 1
        assert counter == len(nl_matrix[index_comp])

    # ----- LINEAR COEFFS -----

    # identity-based blocks
    # ws = 4
    # xx00, x100, xxxx, xxxx A
    # xx00, x100, xx1x, xxxx B
    # ws = 5
    # xx000, x1000, 00100, xxxxx, xxxxx A
    # xx000, x1000, xx100, xx010, xxxxx B

    def get_A_block(index, prefix="A"):
        block = sage.all.identity_matrix(sage.all.SR, ws)
        block[0, 0] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, 0, 0))
        block[0, 1] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, 0, 1))
        block[1, 0] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, 1, 0))
        for i in [ws - 2, ws - 1]:
            for j in range(ws):
                block[i, j] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, i, j))
        return block

    def get_B_block(index, prefix="B"):
        block = sage.all.identity_matrix(sage.all.SR, ws)
        for i in range(ws - 1):
            block[i, 0] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, i, 0))
            block[i, 1] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, i, 1))
        block[1, 1] = 1
        for j in range(ws):
            block[ws - 1, j] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, ws - 1, j))
        return block

    # xx000-based blocks
    # ws = 4
    # xx00, xx00, xxxx, xxxx D !
    # xx00, xx00, xxxx, xxxx E !
    # xx00, xx00, xxxx, xxxx F !
    # xx00, x000, xxxx, xxxx H !
    # xx00, xx00, xxxx, xxxx I !
    # ws = 5
    # xx000, xx000, 00000, xxxxx, xxxxx D !
    # xx000, xx000, xx000, xxxxx, xxxxx E !
    # xx000, xx000, xx000, xxxxx, xxxxx F ! # NOTE: replaced F shape by E
    # xx000, x0000, 00000, xxxxx, xxxxx H ! # NOTE: replaced H shape by E
    # xx000, xx000, 00000, xxxxx, xxxxx I ! # NOTE: replaced I shape by E

    def get_D_block(index, prefix="D"):
        block = sage.all.zero_matrix(sage.all.SR, ws, ws)
        block[0, 0] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, 0, 0))
        block[0, 1] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, 0, 1))
        block[1, 0] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, 1, 0))
        block[1, 1] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, 1, 1))
        for i in [ws - 2, ws - 1]:
            for j in range(ws):
                block[i, j] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, i, j))
        return block

    def get_E_block(index, prefix="E"):
        block = sage.all.zero_matrix(sage.all.SR, ws, ws)
        for i in range(ws - 2):
            block[i, 0] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, i, 0))
            block[i, 1] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, i, 1))
        for i in [ws - 2, ws - 1]:
            for j in range(ws):
                block[i, j] = sage.all.var("ab{}{}_{}_{}".format(prefix, index, i, j))
        return block

    def get_F_block(index, prefix="F"):
        return get_E_block(index, prefix=prefix)

    def get_H_block(index, prefix="H"):
        return get_E_block(index, prefix=prefix)

    def get_I_block(index, prefix="I"):
        return get_E_block(index, prefix=prefix)

    # def get_full_block(index, prefix):
    #     block = sage.all.zero_matrix(sage.all.SR, nrows=ws, ncols=ws)
    #     for i in range(ws):
    #         for j in range(ws):
    #             block[i, j] = sage.all.var("ab{}{}_{}_{}".format(index, prefix, i, j))
    #     return block

    A0, = [get_A_block(i) for i in range(1)]
    B0, = [get_B_block(i) for i in range(1)]

    D0, = [get_D_block(i) for i in range(1)]
    E0, = [get_E_block(i) for i in range(1)]

    F0, F1, = [get_F_block(i) for i in range(2)]
    H0, = [get_H_block(i) for i in range(1)]
    I0, = [get_I_block(i) for i in range(1)]

    right_ct = sage.all.zero_matrix(sage.all.SR, nrows=1, ncols=ws * 4)
    for i in range(4 * wordsize):
        right_ct[0, i] = sage.all.var("ac" + str(i))

    for matrix in [A0, B0, D0, E0, F0, F1, H0, I0, right_ct]:
        for v in matrix.variables():
            if str(v) not in varnames:
                varnames.append(str(v))

    bpr = BooleanPolynomialRing(names=varnames)

    aux = []
    for matrix in [A0, B0, D0, E0, F0, F1, H0, I0, right_ct]:
        aux.append(sage.all.matrix(bpr, matrix.nrows(), matrix.ncols(),
                                   [bpr(str(x)) for x in matrix.list()]))
    A0, B0, D0, E0, F0, F1, H0, I0, right_ct = aux

    # -----

    bpr_gens_dict = bpr.gens_dict()
    to_sr = lambda x: str2bp(x, bpr_gens_dict)

    replacements = MyOrderedDict()

    # -----

    # 'aaB0_0_{2ws} + abA0_0_1', ('abA0_1_0', 0),
    replacements[to_sr("abA0_0_1")] = to_sr(f"aaB0_0_{2*ws}")
    replacements[to_sr("abA0_1_0")] = 0

    replacements[to_sr(f"abA0_{ws-2}_0")] = to_sr(f"aaA0_{ws-2}_{2*ws}")
    for i in range(0, ws - 4):
        replacements[to_sr(f"abA0_{ws-2}_{1+i}")] = to_sr(f"aaA0_{1+i}_{ws-2}")
    replacements[to_sr(f"abA0_{ws-2}_{ws-3}")] = to_sr(f"aaA0_{ws-2}_{3*ws-3}")
    replacements[to_sr(f"abA0_{ws-2}_{ws-2}")] = to_sr(f"aaA0_{ws-2}_{3*ws-2} + 1")
    replacements[to_sr(f"abA0_{ws-2}_{ws-1}")] = to_sr(f"aaA0_{ws-2}_{ws-1}")

    # ('abB0_0_1', 0),
    # ws >= 4, ('abB0_2_1', 0), ...,  ('abB0_{ws - 2}_1', 0),
    replacements[to_sr("abB0_0_1")] = 0
    for i in range(2, ws - 1):
        replacements[to_sr(f"abB0_{i}_1 + 0")] = 0

    if ws >= 5:
        for i in range(0, ws - 3):
            replacements[to_sr(f"abB0_{2+i}_{0}")] = to_sr(f"abB0_{1}_{0}")

    # ('abD0_0_1', 0), ('abD0_1_0', 0), ('abD0_1_1', 0),  # last one new
    replacements[to_sr("abD0_0_1")] = 0
    replacements[to_sr("abD0_1_0")] = 0
    replacements[to_sr("abD0_1_1")] = 0

    for i in range(0, ws - 3):
        replacements[to_sr(f"abD0_{ws-2}_{i}")] = to_sr(f"aaA0_{i}_{ws-2}")
    replacements[to_sr(f"abD0_{ws-2}_{ws-3}")] = to_sr(f"aaA0_{ws-2}_{3*ws-3}")
    replacements[to_sr(f"abD0_{ws-2}_{ws-2}")] = to_sr(f"aaA0_{ws-2}_{3*ws-2}")
    replacements[to_sr(f"abD0_{ws-2}_{ws-1}")] = to_sr(f"aaA0_{ws-2}_{ws-1}")
    replacements[to_sr(f"abD0_{ws-1}_{1}")] = to_sr(f"abA0_{ws-1}_1 + aaD0_0_{2*ws} + aaB1_0_{2*ws}")
    for i in range(0, ws - 4):
        replacements[to_sr(f"abD0_{ws-1}_{2+i}")] = to_sr(f"abA0_{ws-1}_{2+i}")
    replacements[to_sr(f"abD0_{ws-1}_{ws-1}")] = to_sr(f"abA0_{ws-1}_{ws-1} + 1")

    # ('abE0_0_1', 0), ('abE0_1_1', 0), ('abE0_2_1', 0), ..., ('abE0_{ws - 3}_1', 0),  # abE0_1_1 new
    for i in range(0, ws - 2):
        replacements[to_sr(f"abE0_{i}_1")] = 0

    replacements[to_sr("abE0_0_0")] = to_sr(f"abD0_0_0 + aaB0_0_{2*ws}")
    if ws >= 5:
        replacements[to_sr("abE0_1_0")] = to_sr(f"abB0_1_0 + aaA0_0_{2*ws+1} + aaC0_0_{2*ws}")
    for i in range(0, ws - 4):
        replacements[to_sr(f"abE0_{2+i}_{0}")] = to_sr(f"abB0_1_0 + aaB1_0_{2*ws}")
    replacements[to_sr(f"abE0_{ws-2}_{0}")] = to_sr(f"abB0_{2 if ws == 4 else 1}_0 + aaA0_0_{ws-2} + aaB1_0_{2*ws}")
    for i in range(0, ws - 4):
        replacements[to_sr(f"abE0_{ws-2}_{1+i}")] = to_sr(f"aaA0_{1+i}_{ws-2}")
    replacements[to_sr(f"abE0_{ws-2}_{ws-3}")] = to_sr(f"aaA0_{ws-3}_{3*ws-2} + aaA0_{ws-3}_{ws-2}")
    replacements[to_sr(f"abE0_{ws-2}_{ws-2}")] = to_sr(f"aaA0_{ws-2}_{3*ws-2}")
    replacements[to_sr(f"abE0_{ws-2}_{ws-1}")] = to_sr(f"aaA0_{ws-2}_{ws-1}")

    replacements[to_sr("abF0_0_1")] = to_sr(f"aaB{ws-2}_{0}_{2*ws}")
    replacements[to_sr("abF0_1_1")] = to_sr(f"aaC1_0_{2*ws} + aaC0_0_{2*ws}")
    for i in range(0, ws - 4):
        replacements[to_sr(f"abF0_{2+i}_{0}")] = to_sr(f"abF0_1_0 + aaA0_0_{2*ws+1} + aaC0_0_{2*ws} + aaB1_0_{2*ws}")
        replacements[to_sr(f"abF0_{2+i}_{1}")] = to_sr(f"aaB1_{0}_{2*ws}")
    if ws == 4:
        replacements[to_sr(f"abF0_{ws-2}_{1}")] = to_sr(f"aaA0_1_10 + aaA0_1_2 + aaB1_0_{2*ws}")
    else:
        replacements[to_sr(f"abF0_{ws-2}_{0}")] = to_sr(f"abF0_1_0 + aaA0_0_{ws-2} + aaA0_0_{2*ws+1} + aaC0_0_{2*ws} + aaB1_0_{2*ws}")
        replacements[to_sr(f"abF0_{ws-2}_{1}")] = to_sr(f"aaA0_1_{ws-2} + aaB1_0_{2*ws}")
        replacements[to_sr(f"abF0_{ws-2}_{ws-3}")] = to_sr(f"aaA0_{ws-3}_{3*ws-2} + aaA0_{ws-3}_{ws-2}")
    for i in range(ws - 5):
        replacements[to_sr(f"abF0_{ws-2}_{2+i}")] = to_sr(f"aaA0_{2+i}_{ws-2}")
    replacements[to_sr(f"abF0_{ws-2}_{ws-2}")] = to_sr(f"aaA0_{ws-2}_{3*ws-2}")
    replacements[to_sr(f"abF0_{ws-2}_{ws-1}")] = to_sr(f"aaA0_{ws-2}_{ws-1}")
    replacements[to_sr(f"abF0_{ws-1}_{1}")] = to_sr(f"abE0_{ws-1}_1 + abB0_{ws-1}_1 + aaD1_0_{2*ws} + aaB1_0_{2*ws}")
    for i in range(0, ws - 4):
        replacements[to_sr(f"abF0_{ws-1}_{2+i}")] = to_sr(f"abE0_{ws-1}_{2+i} + abB0_{ws-1}_{2+i}")
    replacements[to_sr(f"abF0_{ws-1}_{ws-2}")] = to_sr(f"abE0_{ws-1}_{ws-2} + abD0_{ws-1}_{ws-2} + abB0_{ws-1}_{ws-2} + abA0_{ws-1}_{ws-2}")
    replacements[to_sr(f"abF0_{ws-1}_{ws-1}")] = to_sr(f"abE0_{ws-1}_{ws-1} + abB0_{ws-1}_{ws-1} + 1")

    # ignore for w=4 (abF1_2_0, abF0_2_0 + aaA0_2_8 + aaA0_0_2 + aaB1_0_8),

    replacements[to_sr(f"abF1_0_0")] = to_sr(f"abB0_0_0 + abA0_0_0")
    replacements[to_sr("abF1_0_1")] = to_sr(f"aaB0_{0}_{2*ws}")
    if ws >= 5:
        replacements[to_sr("abF1_1_0")] = to_sr(f"abF0_1_0 + aaA0_{2*ws}_{2*ws+1} + aaA0_0_{2*ws+1} + aaC0_0_{2*ws}")
    replacements[to_sr("abF1_1_1")] = to_sr(f"aaA0_0_{2*ws+1} + aaC0_0_{2*ws}")
    for i in range(0, ws - 4):
        replacements[to_sr(f"abF1_{2+i}_{0}")] = to_sr(f"abF0_1_0 + aaA0_0_{2*ws+1} + aaC0_0_{2*ws}")
        replacements[to_sr(f"abF1_{2+i}_{1}")] = to_sr(f"aaB1_{0}_{2*ws}")
    if ws == 4:
        replacements[to_sr(f"abF1_{ws-2}_{1}")] = to_sr(f"aaA0_2_9 + aaB1_0_{2*ws}")
    else:
        replacements[to_sr(f"abF1_{ws-2}_{0}")] = to_sr(f"abF0_1_0 + aaA0_{ws-2}_{2*ws} + aaA0_0_{2*ws+1} + aaC0_0_{2*ws}")
        replacements[to_sr(f"abF1_{ws-2}_{1}")] = to_sr(f"aaA0_1_{ws-2} + aaB1_0_{2*ws}")
        replacements[to_sr(f"abF1_{ws-2}_{ws-3}")] = to_sr(f"aaA0_{ws-2}_{3*ws-3}")
    for i in range(ws - 5):
        replacements[to_sr(f"abF1_{ws-2}_{2+i}")] = to_sr(f"aaA0_{2+i}_{ws-2}")
    replacements[to_sr(f"abF1_{ws-2}_{ws-2}")] = to_sr(f"aaA0_{ws-2}_{3*ws-2}")
    replacements[to_sr(f"abF1_{ws-2}_{ws-1}")] = to_sr(f"aaA0_{ws-2}_{ws-1}")
    if ws >= 5:
        replacements[to_sr(f"abF1_{ws-1}_{1}")] = to_sr(f"abE0_{ws-1}_1 + abB0_{ws-1}_1 + aaD0_0_{2*ws}")
    replacements[to_sr(f"abF1_{ws-1}_{ws-1}")] = to_sr(f"abE0_{ws-1}_{ws-1} + abB0_{ws-1}_{ws-1} + 1")

    # ws >= 4, (), ('abH0_1_1', 0) | ('abH0_2_0', 0), ('abH0_2_1', 0), | ..., | ('abH0_{ws - 3}_0', 0), ('abH0_{ws - 3}_1', 0),
    for i in range(1, ws - 2):
        if i >= 2:
            replacements[to_sr(f"abH0_{i}_0")] = 0
        replacements[to_sr(f"abH0_{i}_1")] = 0

    replacements[to_sr("abH0_0_0")] = to_sr(f"abB0_0_0 + abA0_0_0 + aaB{ws-2}_0_{2*ws}")
    replacements[to_sr("abH0_0_1")] = to_sr(f"aaB0_0_{2*ws}")
    if ws == 4:
        replacements[to_sr("abH0_1_0")] = to_sr("abE0_1_0 + abB0_1_0 + aaC1_0_8 + aaC0_0_8")
    else:
        replacements[to_sr("abH0_1_0")] = to_sr(f"aaC1_0_{2*ws} + aaA0_0_{2*ws+1}")
    replacements[to_sr(f"abH0_{ws-2}_{0}")] = to_sr(f"aaA0_{ws-2}_{2*ws}")
    for i in range(0, ws - 4):
        replacements[to_sr(f"abH0_{ws-2}_{1+i}")] = to_sr(f"aaA0_{1+i}_{ws-2}")
    replacements[to_sr(f"abH0_{ws-2}_{ws-3}")] = to_sr(f"aaA0_{ws-3}_{3*ws-2} + aaA0_{ws-3}_{ws-2}")
    replacements[to_sr(f"abH0_{ws-2}_{ws-2}")] = to_sr(f"aaA0_{ws-2}_{3*ws-2}")
    replacements[to_sr(f"abH0_{ws-2}_{ws-1}")] = to_sr(f"aaA0_{ws-2}_{ws-1}")
    replacements[to_sr(f"abH0_{ws-1}_{0}")] = to_sr(f"abE0_{ws-1}_0 + abD0_{ws-1}_0 + abB0_{ws-1}_0 + abA0_{ws-1}_0 + aaD1_0_{2*ws} + aaD0_0_{2*ws}")
    replacements[to_sr(f"abH0_{ws-1}_{1}")] = to_sr(f"abE0_{ws-1}_1 + abB0_{ws-1}_1 + aaD0_0_{2*ws} + aaB1_0_{2*ws}")
    for i in range(0, ws - 4):
        replacements[to_sr(f"abH0_{ws-1}_{2+i}")] = to_sr(f"abE0_{ws-1}_{2+i} + abB0_{ws-1}_{2+i}")
    replacements[to_sr(f"abH0_{ws-1}_{ws-2}")] = to_sr(f"abE0_{ws-1}_{ws-2} + abD0_{ws-1}_{ws-2} + abB0_{ws-1}_{ws-2} + abA0_{ws-1}_{ws-2}")
    replacements[to_sr(f"abH0_{ws-1}_{ws-1}")] = to_sr(f"abE0_{ws-1}_{ws-1} + abB0_{ws-1}_{ws-1} + 1")

    # ws >= 5, ('abI0_2_0', 0), ('abI0_2_1', 0), ..., ('abI0_{ws - 3}_0', 0), ('abI0_{ws - 3}_1', 0),
    for i in range(2, ws - 2):
        replacements[to_sr(f"abI0_{i}_0")] = 0
        replacements[to_sr(f"abI0_{i}_1")] = 0

    # missing w=4 (abI0_3_1, abF1_3_1 + aaD1_0_8 + aaD0_0_8)

    replacements[to_sr("abI0_0_0")] = to_sr(f"abF0_0_0 + aaB0_0_{2*ws}")
    replacements[to_sr("abI0_0_1")] = to_sr(f"aaB{ws-2}_0_{2*ws}")
    if ws >= 5:
        replacements[to_sr("abI0_1_0")] = to_sr(f"aaA0_{2*ws}_{2*ws+1}")
    replacements[to_sr("abI0_1_1")] = to_sr(f"aaC1_0_{2*ws} + aaA0_0_{2*ws + 1}")
    for i in range(0, ws - 3):
        replacements[to_sr(f"abI0_{ws-2}_{i}")] = to_sr(f"aaA0_{i}_{ws-2}")
    if ws >= 5:
        replacements[to_sr(f"abI0_{ws-2}_{ws-3}")] = to_sr(f"aaA0_{ws-2}_{3*ws-3}")
    replacements[to_sr(f"abI0_{ws-2}_{ws-2}")] = to_sr(f"aaA0_{ws-2}_{3*ws-2}")
    replacements[to_sr(f"abI0_{ws-2}_{ws-1}")] = to_sr(f"aaA0_{ws-2}_{ws-1}")
    replacements[to_sr(f"abI0_{ws-1}_{0}")] = to_sr(f"abF1_{ws-1}_0 + abF0_{ws-1}_0 + abE0_{ws-1}_0 + abD0_{ws-1}_0 + abB0_{ws-1}_0 + abA0_{ws-1}_0")
    if ws >= 5:
        replacements[to_sr(f"abI0_{ws-1}_{1}")] = to_sr(f"abE0_{ws-1}_1 + abB0_{ws-1}_1 + aaD1_0_{2*ws}")
    for i in range(0, ws - 3):
        replacements[to_sr(f"abI0_{ws-1}_{2+i}")] = to_sr(f"abF1_{ws-1}_{2+i}")
    replacements[to_sr(f"abI0_{ws-1}_{ws-1}")] = to_sr(f"abE0_{ws-1}_{ws-1} + abB0_{ws-1}_{ws-1} + 1")

    # ws = 4, 5, 6, 7
    # ()
    # (ac1, 0),
    # (ac1, 0), (ac2, 0),
    # (ac1, 0), (ac2, 0), (ac3, 0),
    for i in range(1, ws - 3):
        assert ws >= 5
        replacements[to_sr(f"ac{i}")] = 0

    # ws = 4, 5, 6, 7
    # ()
    # ()
    # (ac8, 0),
    # (ac9, 0), (ac10, 0),
    for i in range(ws + 2, 2*ws - 4):
        assert ws >= 6
        replacements[to_sr(f"ac{i}")] = 0

    # ws = 4, 5, 6, 7
    # ()
    # ()
    # (ac20, 0),
    # (ac23, 0), (ac24, 0),
    for i in range(3*ws + 2, 4*ws - 4):
        assert ws >= 6
        replacements[to_sr(f"ac{i}")] = 0

    replacements[to_sr(f"ac{ws-3}")] = to_sr(f"aaA0_{ws-2}_{3*ws-3} + aaA0_{ws-3}_{3*ws-2} + aaA0_{ws-3}_{ws-2}")
    if ws >= 5:
        replacements[to_sr(f"ac{2*ws-3}")] = to_sr(f"aaA0_{ws-2}_{3*ws-3} + aaA0_{ws-3}_{3*ws-2} + aaA0_{ws-3}_{ws-2}")

    replacements[to_sr(f"ac{ws-2}")] = to_sr(f"abF1_{ws-1}_{ws-2} + abE0_{ws-1}_{ws-2} + abB0_{ws-1}_{ws-2} + aaA0_{ws-2}_{3*ws-2}")

    if ws >= 5:
        replacements[to_sr(f"ac{ws+1}")] = to_sr(f"aaA0_0_{2*ws+1} + aaC0_0_{2*ws} + aaB1_0_{2*ws}")
        replacements[to_sr(f"ac{3*ws+1}")] = to_sr(f"aaA0_0_{2*ws+1} + aaC0_0_{2*ws} + aaB1_0_{2*ws}")

    # w=6: (ac8, 0), (ac20, 0),
    # w=7: (ac10, 0), (ac24, 0),
    # w=8: (ac12, 0), (ac28, 0),
    if ws >= 6:
        replacements[to_sr(f"ac{2*ws-4}")] = 0
        replacements[to_sr(f"ac{4*ws-4}")] = 0

    replacements[to_sr(f"ac{2*ws-2}")] = to_sr(f"abF1_{ws-1}_{ws-2} + abE0_{ws-1}_{ws-2} + abD0_{ws-1}_{ws-2} + abB0_{ws-1}_{ws-2} + abA0_{ws-1}_{ws-2} + aaA0_{ws-2}_{3*ws-2}")
    replacements[to_sr(f"ac{4*ws-2}")] = to_sr(f"abF1_{ws-1}_{ws-2} + abE0_{ws-1}_{ws-2} + abD0_{ws-1}_{ws-2} + abB0_{ws-1}_{ws-2} + abA0_{ws-1}_{ws-2} + aaA0_{ws-2}_{3*ws-2}")

    replacements[to_sr(f"ac{2*ws}")] = to_sr("ac0")

    # w=6: (ac14, ac13 + aaA0_0_13 + aaC0_0_12 + aaB1_0_12),
    # w=7: (ac16, ac15 + aaA0_0_15 + aaC0_0_14 + aaB1_0_14),
    #      (ac17, ac15 + aaA0_0_15 + aaC0_0_14 + aaB1_0_14),
    # w=8: (ac18, ac17 + aaA0_0_17 + aaC0_0_16 + aaB1_0_16),
    #      (ac19, ac17 + aaA0_0_17 + aaC0_0_16 + aaB1_0_16),
    #      (ac20, ac17 + aaA0_0_17 + aaC0_0_16 + aaB1_0_16),
    for i in range(0, ws - 5):
        replacements[to_sr(f"ac{2*ws+2+i}")] = to_sr(f"ac{2*ws+1} + aaA0_{0}_{2*ws+1} + aaC0_0_{2*ws} + aaB1_0_{2*ws}")

    if ws >= 5:
        replacements[to_sr(f"ac{3*ws-3}")] = to_sr(f"ac{2*ws+1} + aaA0_{ws-2}_{3*ws-3} + aaA0_{ws-3}_{3*ws-2} + aaA0_{ws-3}_{ws-2} + aaA0_0_{2*ws+1} + aaC0_0_{2*ws} + aaB1_0_{2*ws}")
        replacements[to_sr(f"ac{3*ws-2}")] = to_sr(f"ac{2*ws+1} + abF1_{ws-1}_{ws-2} + abE0_{ws-1}_{ws-2} + abB0_{ws-1}_{ws-2} + aaA0_{ws-2}_{3*ws-2} + aaA0_0_{2*ws+1} + aaC0_0_{2*ws} + aaB1_0_{2*ws}")

    replacements[to_sr(f"ac{3*ws}")] = to_sr(f"ac{ws}")
    replacements[to_sr(f"ac{4*ws-1}")] = to_sr(f"ac{2*ws-1}")

    if ws >= 5:
        replacements[to_sr(f"ac{4*ws-3}")] = to_sr(f"aaA0_{ws-2}_{3*ws-3} + aaA0_{ws-3}_{3*ws-2} + aaA0_{ws-3}_{ws-2}")

    # -----

    A0 = A0.subs(replacements)
    B0 = B0.subs(replacements)
    D0 = D0.subs(replacements)
    E0 = E0.subs(replacements)
    F0, F1 = F0.subs(replacements), F1.subs(replacements)
    H0 = H0.subs(replacements)
    I0 = I0.subs(replacements)
    right_ct = right_ct.subs(replacements)

    # ----

    zz = sage.all.zero_matrix(A0.base_ring(), ws, ws)

    right_matrix = sage.all.block_matrix([
        [A0, D0, D0,      zz],
        [F0, B0, F1,      E0],
        [E0, zz, B0 + F1, E0],
        [H0, D0, I0,      A0 + H0], ])

    if verbose:
        smart_print("linear shape:")
        smart_print(right_matrix)
        smart_print("ct shape:")
        smart_print(right_ct, "\n")

    for i in range(right_matrix.nrows()):
        for j in range(right_matrix.ncols()):
            if len(prefix_symbolic_anf) == 1 or i < 2*ws:
                varname = "{}{}_{}".format(prefix_symbolic_anf[0], i, j)
            else:
                varname = "{}{}_{}".format(prefix_symbolic_anf[1], i - (2*ws), j)
            assert varname not in var2val
            for var in right_matrix[i, j]:
                if var not in [0, 1]:
                    assert "+" not in str(var) and "*" not in str(var)
                    set_final_varnames.add(str(var))
            var2val[varname] = int(right_matrix[i, j]) if right_matrix[i, j] in [0, 1] \
                else str(right_matrix[i, j])

    assert right_ct.nrows() == 1
    for i in range(right_ct.ncols()):
        if len(prefix_symbolic_anf) == 1 or i < 2 * ws:
            varname = "{}{}".format(prefix_symbolic_anf[0], i)
        else:
            varname = "{}{}".format(prefix_symbolic_anf[1], i - (2 * ws))
        assert varname not in var2val
        for var in right_ct[0, i]:
            if var not in [0, 1]:
                assert "+" not in str(var) and "*" not in str(var)
                set_final_varnames.add(str(var))
        var2val[varname] = int(right_ct[0, i]) if right_ct[0, i] in [0, 1] \
            else str(right_ct[0, i])

    # ---------------

    initial_equations = []

    determinants = {
        4: "abF0_0_0*abD0_3_2*abD0_0_0*aaA0_2_3 + abF0_0_0*abD0_0_0*abB0_3_3*aaA0_2_10 + abF0_0_0*abD0_0_0*abB0_3_3 + abF0_0_0*abD0_0_0*abB0_3_2*aaA0_2_3 + abF0_0_0*abD0_0_0*abA0_3_3*aaA0_2_10 + abF0_0_0*abD0_0_0*abA0_3_3 + abF0_0_0*abD0_0_0*aaA0_2_10 + abF0_0_0*abD0_0_0 + abD0_3_2*abD0_0_0*aaA0_2_3*aaB0_0_8 +  abD0_3_2*abD0_0_0*aaA0_2_3 + abD0_3_2*abB0_0_0*abA0_0_0*aaA0_2_3 + abD0_0_0*abB0_3_3*aaA0_2_10*aaB0_0_8 +  abD0_0_0*abB0_3_3*aaA0_2_10 + abD0_0_0*abB0_3_3*aaB0_0_8 +  abD0_0_0*abB0_3_3 + abD0_0_0*abB0_3_2*aaA0_2_3*aaB0_0_8 +  abD0_0_0*abB0_3_2*aaA0_2_3 + abD0_0_0*abA0_3_3*aaA0_2_10*aaB0_0_8 +  abD0_0_0*abA0_3_3*aaA0_2_10 + abD0_0_0*abA0_3_3*aaB0_0_8 +  abD0_0_0*abA0_3_3 + abD0_0_0*aaA0_2_10*aaB0_0_8 +  abD0_0_0*aaA0_2_10 + abD0_0_0*aaB0_0_8 +  abD0_0_0 + abB0_3_3*abB0_0_0*abA0_0_0*aaA0_2_10 + abB0_3_3*abB0_0_0*abA0_0_0 + abB0_3_2*abB0_0_0*abA0_0_0*aaA0_2_3 + abB0_0_0*abA0_3_3*abA0_0_0*aaA0_2_10 + abB0_0_0*abA0_3_3*abA0_0_0 + abB0_0_0*abA0_0_0*aaA0_2_10 + abB0_0_0*abA0_0_0",
        5: "abF0_0_0*abD0_4_3*abD0_0_0*aaA0_3_4 + abF0_0_0*abD0_0_0*abB0_4_4*aaA0_3_13 + abF0_0_0*abD0_0_0*abB0_4_4 + abF0_0_0*abD0_0_0*abB0_4_3*aaA0_3_4 + abF0_0_0*abD0_0_0*abA0_4_4*aaA0_3_13 + abF0_0_0*abD0_0_0*abA0_4_4 + abF0_0_0*abD0_0_0*aaA0_3_13 + abF0_0_0*abD0_0_0 + abD0_4_3*abD0_0_0*aaA0_3_4*aaB0_0_10 + abD0_4_3*abD0_0_0*aaA0_3_4 + abD0_4_3*abB0_0_0*abA0_0_0*aaA0_3_4 + abD0_0_0*abB0_4_4*aaA0_3_13*aaB0_0_10 + abD0_0_0*abB0_4_4*aaA0_3_13 + abD0_0_0*abB0_4_4*aaB0_0_10 + abD0_0_0*abB0_4_4 + abD0_0_0*abB0_4_3*aaA0_3_4*aaB0_0_10 + abD0_0_0*abB0_4_3*aaA0_3_4 + abD0_0_0*abA0_4_4*aaA0_3_13*aaB0_0_10 + abD0_0_0*abA0_4_4*aaA0_3_13 + abD0_0_0*abA0_4_4*aaB0_0_10 + abD0_0_0*abA0_4_4 + abD0_0_0*aaA0_3_13*aaB0_0_10 + abD0_0_0*aaA0_3_13 + abD0_0_0*aaB0_0_10 + abD0_0_0 + abB0_4_4*abB0_0_0*abA0_0_0*aaA0_3_13 + abB0_4_4*abB0_0_0*abA0_0_0 + abB0_4_3*abB0_0_0*abA0_0_0*aaA0_3_4 + abB0_0_0*abA0_4_4*abA0_0_0*aaA0_3_13 + abB0_0_0*abA0_4_4*abA0_0_0 + abB0_0_0*abA0_0_0*aaA0_3_13 + abB0_0_0*abA0_0_0",
        6: "abF0_0_0*abD0_5_4*abD0_0_0*aaA0_4_5 + abF0_0_0*abD0_0_0*abB0_5_5*aaA0_4_16 + abF0_0_0*abD0_0_0*abB0_5_5 + abF0_0_0*abD0_0_0*abB0_5_4*aaA0_4_5 + abF0_0_0*abD0_0_0*abA0_5_5*aaA0_4_16 + abF0_0_0*abD0_0_0*abA0_5_5 + abF0_0_0*abD0_0_0*aaA0_4_16 + abF0_0_0*abD0_0_0 + abD0_5_4*abD0_0_0*aaA0_4_5*aaB0_0_12 + abD0_5_4*abD0_0_0*aaA0_4_5 + abD0_5_4*abB0_0_0*abA0_0_0*aaA0_4_5 + abD0_0_0*abB0_5_5*aaA0_4_16*aaB0_0_12 + abD0_0_0*abB0_5_5*aaA0_4_16 + abD0_0_0*abB0_5_5*aaB0_0_12 + abD0_0_0*abB0_5_5 + abD0_0_0*abB0_5_4*aaA0_4_5*aaB0_0_12 + abD0_0_0*abB0_5_4*aaA0_4_5 + abD0_0_0*abA0_5_5*aaA0_4_16*aaB0_0_12 + abD0_0_0*abA0_5_5*aaA0_4_16 + abD0_0_0*abA0_5_5*aaB0_0_12 + abD0_0_0*abA0_5_5 + abD0_0_0*aaA0_4_16*aaB0_0_12 + abD0_0_0*aaA0_4_16 + abD0_0_0*aaB0_0_12 + abD0_0_0 + abB0_5_5*abB0_0_0*abA0_0_0*aaA0_4_16 + abB0_5_5*abB0_0_0*abA0_0_0 + abB0_5_4*abB0_0_0*abA0_0_0*aaA0_4_5 + abB0_0_0*abA0_5_5*abA0_0_0*aaA0_4_16 + abB0_0_0*abA0_5_5*abA0_0_0 + abB0_0_0*abA0_0_0*aaA0_4_16 + abB0_0_0*abA0_0_0",
        7: "abF0_0_0*abD0_6_5*abD0_0_0*aaA0_5_6 + abF0_0_0*abD0_0_0*abB0_6_6*aaA0_5_19 + abF0_0_0*abD0_0_0*abB0_6_6 + abF0_0_0*abD0_0_0*abB0_6_5*aaA0_5_6 + abF0_0_0*abD0_0_0*abA0_6_6*aaA0_5_19 + abF0_0_0*abD0_0_0*abA0_6_6 + abF0_0_0*abD0_0_0*aaA0_5_19 + abF0_0_0*abD0_0_0 + abD0_6_5*abD0_0_0*aaA0_5_6*aaB0_0_14 + abD0_6_5*abD0_0_0*aaA0_5_6 + abD0_6_5*abB0_0_0*abA0_0_0*aaA0_5_6 + abD0_0_0*abB0_6_6*aaA0_5_19*aaB0_0_14 + abD0_0_0*abB0_6_6*aaA0_5_19 + abD0_0_0*abB0_6_6*aaB0_0_14 + abD0_0_0*abB0_6_6 + abD0_0_0*abB0_6_5*aaA0_5_6*aaB0_0_14 + abD0_0_0*abB0_6_5*aaA0_5_6 + abD0_0_0*abA0_6_6*aaA0_5_19*aaB0_0_14 + abD0_0_0*abA0_6_6*aaA0_5_19 + abD0_0_0*abA0_6_6*aaB0_0_14 + abD0_0_0*abA0_6_6 + abD0_0_0*aaA0_5_19*aaB0_0_14 + abD0_0_0*aaA0_5_19 + abD0_0_0*aaB0_0_14 + abD0_0_0 + abB0_6_6*abB0_0_0*abA0_0_0*aaA0_5_19 + abB0_6_6*abB0_0_0*abA0_0_0 + abB0_6_5*abB0_0_0*abA0_0_0*aaA0_5_6 + abB0_0_0*abA0_6_6*abA0_0_0*aaA0_5_19 + abB0_0_0*abA0_6_6*abA0_0_0 + abB0_0_0*abA0_0_0*aaA0_5_19 + abB0_0_0*abA0_0_0"
    }

    det = f"abF0_0_0*abD0_{ws-1}_{ws-2}*abD0_0_0*aaA0_{ws-2}_{ws-1} + abF0_0_0*abD0_0_0*abB0_{ws-1}_{ws-1}*aaA0_{ws-2}_{3*ws-2} + abF0_0_0*abD0_0_0*abB0_{ws-1}_{ws-1} + abF0_0_0*abD0_0_0*abB0_{ws-1}_{ws-2}*aaA0_{ws-2}_{ws-1} + abF0_0_0*abD0_0_0*abA0_{ws-1}_{ws-1}*aaA0_{ws-2}_{3*ws-2} + abF0_0_0*abD0_0_0*abA0_{ws-1}_{ws-1} + abF0_0_0*abD0_0_0*aaA0_{ws-2}_{3*ws-2} + abF0_0_0*abD0_0_0 + abD0_{ws-1}_{ws-2}*abD0_0_0*aaA0_{ws-2}_{ws-1}*aaB0_0_{2*ws} + abD0_{ws-1}_{ws-2}*abD0_0_0*aaA0_{ws-2}_{ws-1} + abD0_{ws-1}_{ws-2}*abB0_0_0*abA0_0_0*aaA0_{ws-2}_{ws-1} + abD0_0_0*abB0_{ws-1}_{ws-1}*aaA0_{ws-2}_{3*ws-2}*aaB0_0_{2*ws} + abD0_0_0*abB0_{ws-1}_{ws-1}*aaA0_{ws-2}_{3*ws-2} + abD0_0_0*abB0_{ws-1}_{ws-1}*aaB0_0_{2*ws} + abD0_0_0*abB0_{ws-1}_{ws-1} + abD0_0_0*abB0_{ws-1}_{ws-2}*aaA0_{ws-2}_{ws-1}*aaB0_0_{2*ws} + abD0_0_0*abB0_{ws-1}_{ws-2}*aaA0_{ws-2}_{ws-1} + abD0_0_0*abA0_{ws-1}_{ws-1}*aaA0_{ws-2}_{3*ws-2}*aaB0_0_{2*ws} + abD0_0_0*abA0_{ws-1}_{ws-1}*aaA0_{ws-2}_{3*ws-2} + abD0_0_0*abA0_{ws-1}_{ws-1}*aaB0_0_{2*ws} + abD0_0_0*abA0_{ws-1}_{ws-1} + abD0_0_0*aaA0_{ws-2}_{3*ws-2}*aaB0_0_{2*ws} + abD0_0_0*aaA0_{ws-2}_{3*ws-2} + abD0_0_0*aaB0_0_{2*ws} + abD0_0_0 + abB0_{ws-1}_{ws-1}*abB0_0_0*abA0_0_0*aaA0_{ws-2}_{3*ws-2} + abB0_{ws-1}_{ws-1}*abB0_0_0*abA0_0_0 + abB0_{ws-1}_{ws-2}*abB0_0_0*abA0_0_0*aaA0_{ws-2}_{ws-1} + abB0_0_0*abA0_{ws-1}_{ws-1}*abA0_0_0*aaA0_{ws-2}_{3*ws-2} + abB0_0_0*abA0_{ws-1}_{ws-1}*abA0_0_0 + abB0_0_0*abA0_0_0*aaA0_{ws-2}_{3*ws-2} + abB0_0_0*abA0_0_0"
    if ws in determinants:
        assert to_sr(det) == to_sr(determinants[ws]), f"\n{det}\n{determinants[ws]}\n{to_sr(det) + to_sr(determinants[ws])}"

    initial_equations.append(det + " + 1")

    varnames = [vn for vn in varnames if vn in set_final_varnames]

    return var2val, initial_equations, varnames


def graph_qase_coeffs2modadd_qase_anf(coeff2expr, wordsize, verbose, debug, filename, equations=None):
    """Given the symbolic coefficients of the CCZ ASE of the "H" quadratic CCZ,
    return the symbolic anf ASE of the permuted modular addition.
    """
    verbose = verbose or debug

    ws = wordsize
    ccz_anf_name = "H"
    permuted = 1

    if filename is True:
        now = datetime.datetime.now()
        now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
        filename = f"result-graph_qase_coeffs2modadd_qase_anf-w{ws}-{now}.txt"

    admissible_mapping = get_admissible_mapping(ws, name=ccz_anf_name, permuted=permuted)

    x_varnames = ["x" + str(i) for i in range(4*ws)]
    coeff_varnames = []
    if isinstance(coeff2expr, (list, tuple)):
        coeff2expr = collections.OrderedDict(coeff2expr)
    for _, value in coeff2expr.items():
        if value in [0, 1]:
            continue
        if isinstance(value, str):
            value = sage.all.symbolic_expression(value)
        for var in value.variables():
            varname = str(var)
            if varname not in coeff_varnames:
                coeff_varnames.append(varname)
    bpr = BooleanPolynomialRing(names=x_varnames + coeff_varnames)

    prefix_get_symbolic_anf = "b"
    c = get_symbolic_anf(2, 4 * ws, 4 * ws, ct_terms=True, prefix_inputs="x",
                         prefix_coeffs=prefix_get_symbolic_anf,
                         coeff2expr=coeff2expr, bpr=bpr)
    c_input_vars = [bpr(x) for x in x_varnames]

    smart_print = get_smart_print(filename)

    if verbose:
        smart_print(f"\nfree variables ({len(coeff_varnames)}): {coeff_varnames}")

    if verbose and wordsize <= 8:
        smart_print(f"- C:")
        smart_print(get_anf_coeffmatrix_str(c, c_input_vars))

    from sage.structure.element import is_Matrix
    if is_Matrix(admissible_mapping):
        am_anf = matrix2anf(admissible_mapping, bool_poly_ring=bpr, input_vars=c_input_vars)
        am_matrix = admissible_mapping
    elif len(admissible_mapping) == 2 and is_Matrix(admissible_mapping[0]):
        for bit in admissible_mapping[1]:
            if bit != 0:
                raise NotImplementedError("affine admissible mappings not supported")
        am_anf = matrix2anf(admissible_mapping[0], bool_poly_ring=bpr,
                            input_vars=c_input_vars, bin_vector=admissible_mapping[1])
        am_matrix = admissible_mapping[0]
    else:
        am_anf = admissible_mapping
        am_matrix = anf2matrix(admissible_mapping[0], c_input_vars)
        for bit in get_ct_coeff(admissible_mapping[0], c_input_vars):
            if bit != 0:
                raise NotImplementedError("affine admissible mappings not supported")
    inv_am_anf = matrix2anf(am_matrix.inverse(), bool_poly_ring=bpr, input_vars=c_input_vars)

    num_c_input_vars = len(c_input_vars)
    l_c_linv = substitute_anf(
        c, {c_input_vars[i]: inv_am_anf[i] for i in range(num_c_input_vars)}, bpr)
    l_c_linv = substitute_anf(
        am_anf, {c_input_vars[i]: l_c_linv[i] for i in range(num_c_input_vars)}, bpr)

    l_c_linv = list(l_c_linv)

    if verbose and wordsize <= 8:
        smart_print(f"- L C L^(-1):")
        smart_print(get_anf_coeffmatrix_str(l_c_linv, c_input_vars))

    aux_rep = {v: bpr(0) for v in c_input_vars[2*ws:]}
    a = substitute_anf(l_c_linv[:2*ws], aux_rep, bpr)
    aux_rep = {}
    for i in range(num_c_input_vars):
        if i < 2*ws:
            aux_rep[c_input_vars[i]] = bpr(0)
        else:
            aux_rep[c_input_vars[i]] = c_input_vars[i - 2*ws]
    b_inv = substitute_anf(l_c_linv[2*ws:], aux_rep, bpr)

    if verbose and wordsize <= 8:
        smart_print(f"- SE (A, B) of F:")
        smart_print(" - A:")
        smart_print(get_anf_coeffmatrix_str(a, c_input_vars[:2 * ws]))
        smart_print(" - B^(-1):")
        smart_print(get_anf_coeffmatrix_str(b_inv, c_input_vars[:2 * ws]))

    if equations is not None:
        # print the self-equivalence with variables c0, c1, c2,..
        bpr = BooleanPolynomialRing(names=list(bpr.variable_names()) + ["c" + str(i) for i in range(len(coeff_varnames))])
        aux_rep = {}
        for i, v in enumerate(coeff_varnames):
            aux_rep[bpr(v)] = bpr("c" + str(i))
        a = substitute_anf(a, aux_rep, bpr)
        b_inv = substitute_anf(b_inv, aux_rep, bpr)
        smart_print(f"- SE (A, B) of permuted modular addition for wordsize {ws}:")
        smart_print(" - Variables: ", aux_rep.values())
        smart_print(" - A:")
        smart_print(get_anf_coeffmatrix_str(a, c_input_vars[:2 * ws]))
        smart_print(" - B^(-1):")
        smart_print(get_anf_coeffmatrix_str(b_inv, c_input_vars[:2 * ws]))
        smart_print("\n - Constrains:")
        for eq in equations:
            smart_print(bpr(eq).subs(aux_rep))

    # from boolcrypt.utilities import simplify_symbolic_anf
    # a_b_inv = simplify_symbolic_anf(list(a) + list(b_inv), c_input_vars[:2 * ws], prefix="c")
    # a, b_inv = a_b_inv[:2*ws], a_b_inv[2*ws:]
    # # b_inv = simplify_symbolic_anf(b_inv, c_input_vars[:2 * ws])
    # smart_print(f"\n- Simplified SE (A, B) of F:")
    # smart_print(" - A:")
    # smart_print(get_anf_coeffmatrix_str(a, c_input_vars[:2 * ws], full_repr=True))
    # smart_print(" - B^(-1):")
    # smart_print(get_anf_coeffmatrix_str(b_inv, c_input_vars[:2 * ws], full_repr=True))
    # smart_print()

    return a, b_inv


def find_qase_pmodadd_slow(wordsize, check, threads, verbose, debug, filename):
    """Find all QASE of the permuted modular addition for a fixed wordsize"""
    assert wordsize <= 5

    verbose = verbose or debug

    ws = wordsize
    ccz_anf_name = "H"
    permuted = 1

    if filename is True:
        now = datetime.datetime.now()
        now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
        filename = f"result-find_qase_pmodadd_slow-w{ws}-{now}.txt"

    ccz_modadd_anf = get_ccz_modadd_anf(ws, name=ccz_anf_name, permuted=permuted)
    admissible_mapping = get_admissible_mapping(ws, name=ccz_anf_name, permuted=permuted)

    num_input_anf_vars = 2*ws
    if ws <= 6:
        modadd_anf = get_modadd_anf(ws, permuted=permuted)
    else:
        modadd_anf = None

    prefix_se_coeffs = "a"

    left_se_degree, inv_left_se_degree = 1, 1
    inv_right_se_degree, right_se_degree = 2, None
    # changing the order of degrees doesn't make the computation faster
    # left_se_degree, inv_left_se_degree = 2, None
    # inv_right_se_degree, right_se_degree = 1, 1
    ct_terms = True
    return_ccz_se = False

    invertibility = True

    smart_print = get_smart_print(filename)

    # 1st pass - find linear fixed vars from raw equations

    initial_fixed_vars = {}
    smart_print(f"initial_fixed_vars: {initial_fixed_vars}\n")

    smart_print(f"{get_time()} | finding raw equations")
    ignore_determinant_equation = True  # for w=5 we get an error otherwise
    solve_args = {
        "return_mode": "raw_equations",
        "only_linear_fixed_vars": True,  # set deglex as the order
        "initial_fixed_vars": initial_fixed_vars,
    }
    raw_equations = find_self_equivalence(
        ccz_modadd_anf, admissible_mapping,
        anf=modadd_anf, num_input_anf_vars=num_input_anf_vars,
        #
        left_se_degree=left_se_degree, inv_right_se_degree=inv_right_se_degree,
        inv_left_se_degree=inv_left_se_degree, right_se_degree=right_se_degree,
        prefix_se_coeffs=prefix_se_coeffs, se_ct_terms=ct_terms,
        #
        add_invertibility_equations=invertibility,
        ignore_determinant_equation=ignore_determinant_equation,
        #
        return_ccz_se=return_ccz_se,
        #
        check_se=check,
        #
        threads=threads,
        verbose=False, debug=False, filename=filename,
        #
        **solve_args
    )

    smart_print(f"\n{get_time()} | finding linear fixed variables from raw equations")

    bpr = raw_equations[0].parent()
    initial_fixed_vars, _ = find_fixed_vars(
        raw_equations, only_linear=True,  initial_r_mode="gauss", repeat_with_r_mode="gauss",
        initial_fixed_vars={bpr(k): bpr(v) for k, v in initial_fixed_vars.items()},
        bpr=bpr, check=True, verbose=verbose, debug=debug, filename=filename)

    input_ccz_anf_vars = bpr.gens()[:2*ws]
    ccz_modadd_anf = get_ccz_modadd_anf(ws, name=ccz_anf_name, permuted=permuted,
                                        bpr=bpr, input_vars=input_ccz_anf_vars)

    # 2nd pass - find redundant equations

    smart_print(f"\n{get_time()} | finding redundant equations")

    num_sat_solutions = 256
    solve_args = {
        "reduction_mode": "gauss",
        "only_linear_fixed_vars": True,
        "num_sat_solutions": num_sat_solutions,
        "return_mode": "lincomb_solutions",
        "find_linear_combinations_in_solutions": True,
        "initial_fixed_vars": initial_fixed_vars,
        "num_sols_per_base_sol_to_check": 0,
        "return_total_num_solutions": True,
        "ignore_initial_parsing": True,
        "check_find_fixed_vars": check,
    }
    redundant_equations = find_self_equivalence(
        ccz_modadd_anf, admissible_mapping,
        anf=modadd_anf, num_input_anf_vars=num_input_anf_vars,
        input_ccz_anf_vars=input_ccz_anf_vars,
        #
        left_se_degree=left_se_degree, inv_right_se_degree=inv_right_se_degree,
        inv_left_se_degree=inv_left_se_degree, right_se_degree=right_se_degree,
        prefix_se_coeffs=prefix_se_coeffs, se_ct_terms=ct_terms,
        #
        add_invertibility_equations=invertibility,
        ignore_determinant_equation=ignore_determinant_equation,
        #
        return_ccz_se=return_ccz_se,
        #
        check_se=check,
        #
        bpr=bpr,
        threads=threads,
        verbose=verbose, debug=debug, filename=filename,
        #
        **solve_args
    )

    smart_print(f"\nredundant equations found ({len(redundant_equations)}): "
                f"{[str(x) for x in redundant_equations]}")

    if len(redundant_equations) >= 1:
        smart_print(f"\n{get_time()} | filtering redundant equations")
        solve_args = {
            "reduction_mode": "gauss",
            "only_linear_fixed_vars": True,
            "return_mode": "symbolic_anf",
            "find_redundant_equations": redundant_equations,
            "initial_fixed_vars": initial_fixed_vars,
            "ignore_initial_parsing": True,
            "check_find_fixed_vars": False,
        }
        redundant_equations = find_self_equivalence(
            ccz_modadd_anf, admissible_mapping,
            anf=modadd_anf, num_input_anf_vars=num_input_anf_vars,
            input_ccz_anf_vars=input_ccz_anf_vars,
            #
            left_se_degree=left_se_degree, inv_right_se_degree=inv_right_se_degree,
            inv_left_se_degree=inv_left_se_degree, right_se_degree=right_se_degree,
            prefix_se_coeffs=prefix_se_coeffs, se_ct_terms=ct_terms,
            #
            add_invertibility_equations=invertibility,
            ignore_determinant_equation=ignore_determinant_equation,
            #
            return_ccz_se=return_ccz_se,
            #
            check_se=check,
            #
            bpr=bpr,
            threads=threads,
            verbose=verbose, debug=debug, filename=filename,
            #
            **solve_args
        )

        smart_print(f"\nvalid redundant equations found ({len(redundant_equations)}): "
                    f"{[str(x) for x in redundant_equations]}")

    # 3rd pass - find symbolic coeffs

    smart_print(f"\n{get_time()} | solving final pass")
    if ws == 3:
        num_sat_solutions = 0  # too many SAT solutions
    else:
        num_sat_solutions = 0 if len(redundant_equations) == 0 and check is False else sage.all.infinity
    ignore_determinant_equation = False
    solve_args = {
        "reduction_mode": "gauss",
        "only_linear_fixed_vars": False,
        "num_sat_solutions": num_sat_solutions,
        "return_mode": "symbolic_coeffs",
        "initial_fixed_vars": initial_fixed_vars,
        "initial_equations": redundant_equations,
        "find_linear_combinations_in_solutions": True,
        "num_sols_per_base_sol_to_check": 0,
        "return_total_num_solutions": True,
        "ignore_initial_parsing": True,
        "check_find_fixed_vars": False,
    }
    symbolic_coeffs, equations, num_total_solutions = find_self_equivalence(
        ccz_modadd_anf, admissible_mapping,
        anf=modadd_anf, num_input_anf_vars=num_input_anf_vars,
        input_ccz_anf_vars=input_ccz_anf_vars,
        #
        left_se_degree=left_se_degree, inv_right_se_degree=inv_right_se_degree,
        inv_left_se_degree=inv_left_se_degree, right_se_degree=right_se_degree,
        prefix_se_coeffs=prefix_se_coeffs, se_ct_terms=ct_terms,
        #
        add_invertibility_equations=invertibility,
        ignore_determinant_equation=ignore_determinant_equation,
        #
        return_ccz_se=return_ccz_se,
        #
        check_se=check,
        #
        bpr=bpr,
        threads=threads,
        verbose=verbose, debug=debug, filename=filename,
        #
        **solve_args
    )

    smart_print("\nnum_total_solutions:", num_total_solutions,
                None if num_total_solutions is None
                else f"= 2^({math.log2(num_total_solutions)})")

    variables = list(reversed([v for v in bpr.gens()[4*ws:] if v not in symbolic_coeffs]))
    smart_print(f"non-fixed variables ({len(variables)} out of {len(bpr.gens()[4*ws:])}): {variables}")

    smart_print("equations:")
    for eq in equations:
        smart_print(f"\t{eq}")

    smart_print(f"symbolic_coeffs = {symbolic_coeffs}\n")

    return symbolic_coeffs, equations, num_total_solutions


def find_qase_pmodadd_with_shape(wordsize, check, threads, save_coeffs_eqs, verbose, debug, filename):
    """Find all QASE of the permuted modular addition for a fixed wordsize using a predefined shape."""
    assert wordsize >= 4, "only supported for wordsize >= 4"

    verbose = verbose or debug

    ws = wordsize
    ccz_anf_name = "H"
    permuted = 1

    if filename is True:
        now = datetime.datetime.now()
        now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
        filename = f"result-find_qase_pmodadd_with_shape-w{ws}-{now}.txt"

    num_input_anf_vars = 2*ws
    if ws <= 6:
        modadd_anf = get_modadd_anf(ws, permuted=permuted)
    else:
        modadd_anf = None

    prefix_se_coeffs = "a"

    left_se_degree, inv_left_se_degree = 1, 1
    inv_right_se_degree, right_se_degree = 2, None
    ct_terms = True
    return_ccz_se = False

    invertibility = not(ws >= 5)
    ignore_diagonal_equations = ws >= 5

    #

    prefix_get_symbolic_anf = "b"  # coeffs starting with this prefix only used for next get_symbolic_anf()
    assert prefix_se_coeffs[0] != prefix_get_symbolic_anf[0]
    shape_fixed_vars, initial_equations, shape_varnames = shape(ws, prefix_get_symbolic_anf, verbose, filename)

    x_varnames = ["x" + str(i) for i in range(4*ws)]
    # # shape_fixed_vars contains assignments B0* <- A0*
    # # however, default assignments is A0* <- B0* if bpr order is A0 > B0 > ...
    # # (default is left vars are replaced by right vars)
    # # thus, coeffs are reversed to preserve shape_fixed_vars order
    coeff_varnames = list(reversed(shape_varnames))
    bpr = BooleanPolynomialRing(names=x_varnames + coeff_varnames)
    ccz_se_anf = get_symbolic_anf(2, 4 * ws, 4 * ws, ct_terms=True, prefix_inputs="x",
                                  prefix_coeffs=prefix_get_symbolic_anf,
                                  coeff2expr=shape_fixed_vars, bpr=bpr)
    bpr_gens_dict = bpr.gens_dict()

    input_ccz_anf_vars = [str2bp(vn, bpr_gens_dict) for vn in x_varnames[:2*ws]]
    ccz_modadd_anf = get_ccz_modadd_anf(ws, name=ccz_anf_name, permuted=permuted,
                                        bpr=bpr, input_vars=input_ccz_anf_vars)
    admissible_mapping = get_admissible_mapping(ws, name=ccz_anf_name, permuted=permuted)

    # fast conversion with str2bp
    # (the conversion when calling bpr() uses slow and memory-limited Singular)
    initial_equations = [str2bp(eq, bpr_gens_dict) for eq in initial_equations]
    fixed_vars = collections.OrderedDict(
        (str2bp(k, bpr_gens_dict), bpr(v) if v in [0, 1] else str2bp(v, bpr_gens_dict))
        for k, v in shape_fixed_vars.items() if not k.startswith(prefix_get_symbolic_anf))

    if ws == 3:
        num_sat_solutions = 0  # too many SAT solutions
    else:
        num_sat_solutions = sage.all.infinity
    solve_args = {
        "reduction_mode": "gauss",
        "only_linear_fixed_vars": False,
        "num_sat_solutions": num_sat_solutions,
        "return_mode": "symbolic_coeffs",
        "initial_equations": initial_equations,
        "initial_fixed_vars": fixed_vars,
        "find_linear_combinations_in_solutions": True,
        "num_sols_per_base_sol_to_check": 0,
        "return_total_num_solutions": True,
        "ignore_initial_parsing": True,
        "check_find_fixed_vars": False,
    }
    symbolic_coeffs, equations, num_total_solutions = find_self_equivalence(
        ccz_modadd_anf, admissible_mapping,
        # degree args
        left_se_degree=left_se_degree, inv_right_se_degree=inv_right_se_degree,
        inv_left_se_degree=inv_left_se_degree, right_se_degree=right_se_degree,
        se_ct_terms=ct_terms,
        # optimization constraints
        ignore_diagonal_equations=ignore_diagonal_equations,
        add_invertibility_equations=invertibility,
        check_se=check,
        bpr=bpr,
        # optional input args
        ccz_se_anf=ccz_se_anf,
        prefix_se_coeffs=prefix_se_coeffs,
        input_ccz_anf_vars=input_ccz_anf_vars,
        anf=modadd_anf, num_input_anf_vars=num_input_anf_vars,
        # optional output args
        return_ccz_se=return_ccz_se,
        # printing args
        verbose=verbose, debug=debug, filename=filename,
        # extra args passed to solve_functional_equation()
        threads=threads,
        **solve_args
    )

    smart_print = get_smart_print(filename)

    smart_print("num_total_solutions:", num_total_solutions,
                None if num_total_solutions is None
                else f"= 2^({math.log2(num_total_solutions)})")

    variables = list(reversed([v for v in bpr.gens()[4*ws:] if v not in symbolic_coeffs]))
    smart_print(f"non-fixed variables ({len(variables)} out of {len(bpr.gens()[4*ws:])}): {variables}")
    var2found = {str(v): False for v in variables}

    smart_print("equations:")
    for eq in equations:
        smart_print(f"\t{eq}")

    str_symbolic_coeffs = []
    for var, value in shape_fixed_vars.items():
        if var.startswith(prefix_get_symbolic_anf):
            if value not in [0, 1]:
                value = bpr(value).subs(symbolic_coeffs)
                for v in value.variables():
                    var2found[str(v)] = True
                value = str(value)
        str_symbolic_coeffs.append((var, value))

    smart_print(f"graph_se_coeffs = {str_symbolic_coeffs}\n")

    assert set(var2found.values()) == {True}, f"{var2found}"
    assert len(equations) == 14 if ws == 4 else 3

    if save_coeffs_eqs:
        filename_sobj = f"stored_qase_pmodadd_w{ws}.sobj"
        str_equations = tuple([str(eq) for eq in equations])
        sage.all.save((str_symbolic_coeffs, str_equations), filename_sobj, compress=True)

    return str_symbolic_coeffs, equations, num_total_solutions


if __name__ == '__main__':
    sys.setrecursionlimit(sys.getrecursionlimit()*1000)

    wordsize = 5
    check = True
    threads = 4

    save = False
    verbose = True
    debug = False
    filename = None

    symbolic_coeffs, _, _ = find_qase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)
    # graph_qase_coeffs2modadd_qase_anf(symbolic_coeffs, wordsize, verbose, debug, filename)

    # find_qase_pmodadd_slow(wordsize, check, threads, verbose, debug, filename)

    # # - run find_qase_pmodadd_slow and find_qase_pmodadd_with_shape for multiple wordsizes
    # import time
    # threads = 4
    # save = False
    # verbose = True
    # debug = False
    # filename = True
    # for wordsize in [2, 3, 4, 5, 6, 16, 24, 32, 48, 64]:
    #     if wordsize in [2, 3]:
    #         check = True
    #         find_qase_pmodadd_slow(wordsize, check, threads, verbose, debug, filename)
    #     elif 4 == wordsize:
    #         check = True
    #         find_qase_pmodadd_slow(wordsize, check, threads, verbose, debug, filename)
    #         check = False
    #         symbolic_coeffs, _, _ = find_qase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)
    #         graph_qase_coeffs2modadd_qase_anf(symbolic_coeffs, wordsize, verbose, debug, filename)
    #     else:
    #         check = False
    #         symbolic_coeffs, _, _ = find_qase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)
    #         graph_qase_coeffs2modadd_qase_anf(symbolic_coeffs, wordsize, verbose, debug, filename)

    # # - save coeffs and eqs of QSE for multiple wordsize
    # threads = 4
    # save = True
    # verbose = False
    # debug = False
    # check = False
    # filename = False
    # for wordsize in [16, 24, 32, 48, 64]:
    #     find_qase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)

    # - load coeffs and eqs of QSE
    # verbose = True
    # debug = False
    # filename = None
    # for wordsize in [16, 24, 32, 48, 64]:
    #     filename_sobj = f"stored_qase_pmodadd_w{wordsize}.sobj"
    #     coeff2expr, equations = sage.all.load(filename_sobj, compress=True)
    #     a, b_inv = graph_qase_coeffs2modadd_qase_anf(coeff2expr, wordsize, verbose, debug, filename)
    #     print(equations)
    #     print(a[0])
    #     print("...")
    #     print(b_inv[-1], "\n")

    # # - check cardinality 3^2 \times 2^{3n + 14}
    # threads = 4
    # check = False
    # save = False
    # verbose = False
    # debug = False
    # now = datetime.datetime.now()
    # now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
    # filename = f"result-cardinality_quadraticaffine_pmodadd-{now}.txt"
    # smart_print = get_smart_print(filename)
    # for wordsize in range(4, 64 + 1):
    #     ws = wordsize
    #     _, _, num_total_solutions = find_qase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)
    #     smart_print(f"w = {ws} | quadratic-affine | num_total_solutions = {num_total_solutions} | "
    #                 f"{9 * (2**(3 * ws + 14))} = 9 * (2**(3 * {ws} + 14)")
    #     if num_total_solutions != 9 * (2**(3 * ws + 14)):
    #         raise ValueError(f"invalid number of quadratic-affine self-equivalences")
