"""Find affine self-equivalences (ASE) of the permuted modular addition."""
import collections
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
    """Symbolic shape of the CCZ ASE of the "H" quadratic CCZ of the permuted modular addition."""
    ws = wordsize

    assert ws >= 3  # for ws = 3, all non-zero blocks have no shape

    if isinstance(prefix_symbolic_anf, str):
        prefix_symbolic_anf = [prefix_symbolic_anf]
    assert len(prefix_symbolic_anf) in [1, 2], str(len(prefix_symbolic_anf))

    smart_print = get_smart_print(filename)

    var2val = collections.OrderedDict()

    # ----- LINEAR COEFFS -----

    # identity-based blocks
    # ws = 3
    # x 0 0, 0 1 0, x x x A
    # x 0 0, x 1 0, x x x B
    # ws = 4
    # x 0 0 0, 0 1 0 0, 0 0 1 0, x x x x A
    # x 0 0 0, x 1 0 0, x 0 1 0, x x x x B
    # ws = 5
    # x 0 0 0 0, 0 1 0 0 0, ..., x x x x x A
    # x 0 0 0 0, x 1 0 0 0, ..., x x x x x B

    def get_A_block(index, prefix="A"):
        block = sage.all.identity_matrix(sage.all.SR, ws)
        block[0, 0] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, 0, 0))
        for j in range(ws):
            block[ws - 1, j] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws - 1, j))
        return block

    def get_B_block(index, prefix="B"):
        block = sage.all.identity_matrix(sage.all.SR, ws)
        for i in range(ws - 1):
            block[i, 0] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, i, 0))
        for j in range(ws):
            block[ws - 1, j] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws - 1, j))
        return block

    # x000/0000-based blocks
    # ws = 3
    # x 0 0, 0 0 0, x x x C
    # x 0 0, 0 0 0, x x 0 D
    # ws = 4
    # x 0 0 0, 0 0 0 0, 0 0 0 0, x x x x C
    # x 0 0 0, 0 0 0 0, 0 0 0 0, x x x 0 D
    # ws = 5
    # x 0 0 0 0, 0 0 0 0 0, ..., 0 0 0 0 0, x x x x x C
    # x 0 0 0 0, 0 0 0 0 0, ..., 0 0 0 0 0, x x x x x D

    def get_C_block(index, prefix="C"):
        block = sage.all.zero_matrix(sage.all.SR, ws, ws)
        block[0, 0] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, 0, 0))
        for j in range(ws):
            block[ws - 1, j] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws - 1, j))
        return block

    def get_D_block(index, prefix="D"):
        block = get_C_block(index, prefix=prefix)
        block[ws - 1, ws - 1] = 0
        return block

    # x000/x000-based blocks
    # ws = 3
    # x 0 0, x 0 0, x x x E
    # x 0 0, x 0 0, x x 0 F
    # ws = 4
    # x 0 0 0, x 0 0 0, x 0 0 0, x x x x E
    # x 0 0 0, x 0 0 0, x 0 0 0, x x x 0 F
    # ws = 5
    # x 0 0 0 0, ..., x 0 0 0 0, x x x x x E
    # x 0 0 0 0, ..., x 0 0 0 0, x x x x 0 F

    def get_E_block(index, prefix="E"):
        block = sage.all.zero_matrix(sage.all.SR, ws, ws)
        for i in range(ws - 1):
            block[i, 0] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, i, 0))
        for j in range(ws):
            block[ws - 1, j] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws - 1, j))
        return block

    def get_F_block(index, prefix="F"):
        block = get_E_block(index, prefix=prefix)
        block[ws - 1, ws - 1] = 0
        return block

    # def get_full_block(index, prefix):
    #     block = sage.all.zero_matrix(sage.all.SR, nrows=ws, ncols=ws)
    #     for i in range(ws):
    #         for j in range(ws):
    #             block[i, j] = sage.all.var("ab{}{}_{}_{}".format(index, prefix, i, j))
    #     return block

    A0, A1, = [get_A_block(i) for i in range(2)]
    B0, B1, = [get_B_block(i) for i in range(2)]

    C0, = [get_C_block(i) for i in range(1)]
    D0, D1, = [get_D_block(i) for i in range(2)]

    E0, = [get_E_block(i) for i in range(1)]
    F0, F1, = [get_F_block(i) for i in range(2)]

    right_ct = sage.all.zero_matrix(sage.all.SR, nrows=1, ncols=ws * 4)
    for i in range(4 * wordsize):
        right_ct[0, i] = sage.all.var("a" + str(i))

    varnames = []
    for matrix in [A0, A1, B0, B1, C0, D0, D1, E0, F0, F1, right_ct]:
        varnames.extend([str(v) for v in matrix.variables()])

    bpr = BooleanPolynomialRing(names=varnames)

    aux = []
    for matrix in [A0, A1, B0, B1, C0, D0, D1, E0, F0, F1, right_ct]:
        aux.append(sage.all.matrix(bpr, matrix.nrows(), matrix.ncols(),
                                   [bpr(str(x)) for x in matrix.list()]))
    A0, A1, B0, B1, C0, D0, D1, E0, F0, F1, right_ct = aux

    # -----

    class MyOrderedDict(collections.OrderedDict):
        def __setitem__(self, key, value):
            assert key not in self
            return super().__setitem__(key, value)

    bpr_gens_dict = bpr.gens_dict()
    to_sr = lambda x: str2bp(x, bpr_gens_dict)

    replacements = MyOrderedDict()

    # -----

    # a
    # w = 4
    # ('a1', 0),
    # ('a5', 0),
    # ('a13', 0)
    # w = 5
    # ('a1', 0), ('a2', 0),
    # ('a6', 0), ('a7', 0),
    # ('a16', 0), ('a17', 0)
    # w = 6
    # ('a1', 0), ('a2', 0), ('a3', 0),
    # ('a7', 0), ('a8', 0), ('a9', 0),
    # ('a19', 0), ('a20', 0), ('a21', 0)
    # w = 7
    # ('a1', 0), ('a2', 0), ('a3', 0), ('a4', 0),
    # ('a8', 0), ('a9', 0), ('a10', 0), ('a11', 0),
    # ('a22', 0), ('a23', 0), ('a24', 0), ('a25', 0)
    for i in range(0, ws - 4 + 1):
        assert ws >= 4
        replacements[to_sr("a{}".format(1 + i))] = 0
        replacements[to_sr("a{}".format(ws + 1 + i))] = 0
        replacements[to_sr("a{}".format(3*ws + 1 + i))] = 0

    # not all aB
    # w = 4, ('aB0_2_0', 'aB0_1_0'),
    # w = 5, ('aB0_2_0', 'aB0_1_0'), ('aB0_3_0', 'aB0_1_0'),
    # w = 6, ('aB0_2_0', 'aB0_1_0'), ('aB0_3_0', 'aB0_1_0'), ('aB0_4_0', 'aB0_1_0'),
    # w = 7, ('aB0_2_0', 'aB0_1_0'), ('aB0_3_0', 'aB0_1_0'), ('aB0_4_0', 'aB0_1_0'), ('aB0_5_0', 'aB0_1_0')
    for i in range(0, ws - 4 + 1):
        assert ws >= 4
        replacements[to_sr("aB0_{}_0".format(2 + i))] = to_sr("aB0_{}_0".format(1))

    # not all AC (w from 4 to 7)
    # ('aC0_3_1', 'aA0_3_1'),
    # ('aC0_4_1', 'aA0_4_1'), ('aC0_4_2', 'aA0_4_2'),
    # ('aC0_5_1', 'aA0_5_1'), ('aC0_5_2', 'aA0_5_2'), ('aC0_5_3', 'aA0_5_3'),
    # ('aC0_6_1', 'aA0_6_1'), ('aC0_6_2', 'aA0_6_2'), ('aC0_6_3', 'aA0_6_3'), ('aC0_6_4', 'aA0_6_4'),
    for i in range(0, ws - 4 + 1):
        assert ws >= 4
        replacements[to_sr("aC0_{}_{}".format(ws - 1, 1 + i))] = to_sr("aA0_{}_{}".format(ws - 1, 1 + i))

    # not all aD0/aD1
    # ('aD0_3_1', 'aB0_3_1 + aA0_3_1'),
    # ('aD0_4_1', 'aB0_4_1 + aA0_4_1'), ('aD0_4_2', 'aB0_4_2 + aA0_4_2'),
    # ('aD0_5_1', 'aB0_5_1 + aA0_5_1'), ('aD0_5_2', 'aB0_5_2 + aA0_5_2'), ('aD0_5_3', 'aB0_5_3 + aA0_5_3'),
    # ('aD0_6_1', 'aB0_6_1 + aA0_6_1'), ('aD0_6_2', 'aB0_6_2 + aA0_6_2'), ('aD0_6_3', 'aB0_6_3 + aA0_6_3'), ('aD0_6_4', 'aB0_6_4 + aA0_6_4'),
    #
    # ('aD1_3_1', 'aB0_3_1 + aA0_3_1'),
    # ('aD1_4_1', 'aB0_4_1 + aA0_4_1'), ('aD1_4_2', 'aB0_4_2 + aA0_4_2'),
    # ('aD1_5_1', 'aB0_5_1 + aA0_5_1'), ('aD1_5_2', 'aB0_5_2 + aA0_5_2'), ('aD1_5_3', 'aB0_5_3 + aA0_5_3'),
    # ('aD1_6_1', 'aB0_6_1 + aA0_6_1'), ('aD1_6_2', 'aB0_6_2 + aA0_6_2'), ('aD1_6_3', 'aB0_6_3 + aA0_6_3'), ('aD1_6_4', 'aB0_6_4 + aA0_6_4'),
    for i in range(0, ws - 4 + 1):
        assert ws >= 4
        replacements[to_sr("aD0_{}_{}".format(ws - 1, 1 + i))] = to_sr("aB0_{0}_{1} + aA0_{0}_{1}".format(ws - 1, 1 + i))
        replacements[to_sr("aD1_{}_{}".format(ws - 1, 1 + i))] = to_sr("aB0_{0}_{1} + aA0_{0}_{1}".format(ws - 1, 1 + i))

    # not all E0 (from w=3 to w=7)
    # ('aE0_1_0', 'aB0_1_0'),
    # ('aE0_1_0', 'aB0_1_0'), ('aE0_2_0', 'aB0_1_0'),
    # ('aE0_1_0', 'aB0_1_0'), ('aE0_2_0', 'aB0_1_0'), ('aE0_3_0', 'aB0_1_0'),
    # ('aE0_1_0', 'aB0_1_0'), ('aE0_2_0', 'aB0_1_0'), ('aE0_3_0', 'aB0_1_0'), ('aE0_4_0', 'aB0_1_0'),
    # ('aE0_1_0', 'aB0_1_0'), ('aE0_2_0', 'aB0_1_0'), ('aE0_3_0', 'aB0_1_0'), ('aE0_4_0', 'aB0_1_0'), ('aE0_5_0', 'aB0_1_0'),
    #
    # ()
    # ('aE0_3_1', 'aA0_3_1'),
    # ('aE0_4_1', 'aA0_4_1'), ('aE0_4_2', 'aA0_4_2'),
    # ('aE0_5_1', 'aA0_5_1'), ('aE0_5_2', 'aA0_5_2'), ('aE0_5_3', 'aA0_5_3'),
    # ('aE0_6_1', 'aA0_6_1'), ('aE0_6_2', 'aA0_6_2'), ('aE0_6_3', 'aA0_6_3'), ('aE0_6_4', 'aA0_6_4'),
    for i in range(0, ws - 3 + 1):
        assert ws >= 3
        replacements[to_sr("aE0_{}_0".format(1 + i))] = to_sr("aB0_{}_0".format(1))
    for i in range(0, ws - 4 + 1):
        assert ws >= 4
        replacements[to_sr("aE0_{}_{}".format(ws - 1, 1 + i))] = to_sr("aA0_{}_{}".format(ws - 1, 1 + i))

    # not all F0
    # ('aF0_2_0', 'aF0_1_0'),
    # ('aF0_2_0', 'aF0_1_0'), ('aF0_3_0', 'aF0_1_0'),
    # ('aF0_2_0', 'aF0_1_0'), ('aF0_3_0', 'aF0_1_0'), ('aF0_4_0', 'aF0_1_0'),
    # ('aF0_2_0', 'aF0_1_0'), ('aF0_3_0', 'aF0_1_0'), ('aF0_4_0', 'aF0_1_0'), ('aF0_5_0', 'aF0_1_0'),
    #
    # ('aF0_3_1', 'aB0_3_1 + aA0_3_1'),
    # ('aF0_4_1', 'aB0_4_1 + aA0_4_1'), ('aF0_4_2', 'aB0_4_2 + aA0_4_2'),
    # ('aF0_5_1', 'aB0_5_1 + aA0_5_1'), ('aF0_5_2', 'aB0_5_2 + aA0_5_2'), ('aF0_5_3', 'aB0_5_3 + aA0_5_3'),
    # ('aF0_6_1', 'aB0_6_1 + aA0_6_1'), ('aF0_6_2', 'aB0_6_2 + aA0_6_2'), ('aF0_6_3', 'aB0_6_3 + aA0_6_3'), ('aF0_6_4', 'aB0_6_4 + aA0_6_4'),
    for i in range(0, ws - 4 + 1):
        assert ws >= 4
        replacements[to_sr("aF0_{}_0".format(2 + i))] = to_sr("aF0_{}_0".format(1))
        replacements[to_sr("aF0_{}_{}".format(ws - 1, 1 + i))] = to_sr("aB0_{0}_{1} + aA0_{0}_{1}".format(ws - 1, 1 + i))

    # not all F1
    # ('aF1_1_0', 'aF0_1_0'),
    # ('aF1_1_0', 'aF0_1_0'), ('aF1_2_0', 'aF0_1_0'),
    # ('aF1_1_0', 'aF0_1_0'), ('aF1_2_0', 'aF0_1_0'), ('aF1_3_0', 'aF0_1_0'),
    # ('aF1_1_0', 'aF0_1_0'), ('aF1_2_0', 'aF0_1_0'), ('aF1_3_0', 'aF0_1_0'), ('aF1_4_0', 'aF0_1_0'),
    # ('aF1_1_0', 'aF0_1_0'), ('aF1_2_0', 'aF0_1_0'), ('aF1_3_0', 'aF0_1_0'), ('aF1_4_0', 'aF0_1_0'), ('aF1_5_0', 'aF0_1_0'),
    #
    # ()
    # ('aF1_3_1', 'aB0_3_1 + aA0_3_1'),
    # ('aF1_4_1', 'aB0_4_1 + aA0_4_1'), ('aF1_4_2', 'aB0_4_2 + aA0_4_2'),
    # ('aF1_5_1', 'aB0_5_1 + aA0_5_1'), ('aF1_5_2', 'aB0_5_2 + aA0_5_2'), ('aF1_5_3', 'aB0_5_3 + aA0_5_3'),
    # ('aF1_6_1', 'aB0_6_1 + aA0_6_1'), ('aF1_6_2', 'aB0_6_2 + aA0_6_2'), ('aF1_6_3', 'aB0_6_3 + aA0_6_3'), ('aF1_6_4', 'aB0_6_4 + aA0_6_4'),
    for i in range(0, ws - 3 + 1):
        assert ws >= 3
        replacements[to_sr("aF1_{}_0".format(1 + i))] = to_sr("aF0_{}_0".format(1))
    for i in range(0, ws - 4 + 1):
        assert ws >= 4
        replacements[to_sr("aF1_{}_{}".format(ws - 1, 1 + i))] = to_sr("aB0_{0}_{1} + aA0_{0}_{1}".format(ws - 1, 1 + i))

    # -----

    # A0, A1 = A0.subs(replacements), A1.subs(replacements)
    B0 = B0.subs(replacements)
    # B1 = B1.subs(replacements)
    C0 = C0.subs(replacements)
    D0, D1 = D0.subs(replacements), D1.subs(replacements)
    E0 = E0.subs(replacements)
    F0, F1 = F0.subs(replacements), F1.subs(replacements)
    right_ct = right_ct.subs(replacements)

    # ----

    B1 = F1 + B0
    A1 = D0 + A0

    zz = sage.all.zero_matrix(bpr, ws, ws)

    # Z0, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, ZA, ZB, ZC, ZD = [get_full_block(i, i) for i in range(14)]

    # A0 C0 C0 0
    # F0 B0 F1 E0
    # E0 0  B1 E0
    # D0 C0 D1 A1

    right_matrix = sage.all.block_matrix([
        [A0, C0, C0, zz],
        [F0, B0, F1, E0],
        [E0, zz, B1, E0],
        [D0, C0, D1, A1], ])

    if verbose:
        smart_print("matrix shape:")
        smart_print(right_matrix)
        smart_print("ct shape:")
        smart_print(right_ct, "\n")

    set_final_varnames = set()
    for i in range(right_matrix.nrows()):
        for j in range(right_matrix.ncols()):
            if len(prefix_symbolic_anf) == 1 or i < 2*ws:
                varname = "{}{}_{}".format(prefix_symbolic_anf[0], i, j)
            else:
                varname = "{}{}_{}".format(prefix_symbolic_anf[1], i - (2*ws), j)
            assert varname not in var2val
            for var in right_matrix[i, j]:
                if var not in [0, 1]:
                    str_var = str(var)
                    assert "+" not in str(var) and "*" not in str(var)
                    set_final_varnames.add(str_var)
            var2val[varname] = int(right_matrix[i, j]) if right_matrix[i, j] in [0, 1] \
                else str(right_matrix[i, j])

    assert right_ct.nrows() == 1
    for i in range(right_ct.ncols()):
        if len(prefix_symbolic_anf) == 1 or i < 2*ws:
            varname = "{}{}".format(prefix_symbolic_anf[0], i)
        else:
            varname = "{}{}".format(prefix_symbolic_anf[1], i - (2*ws))
        assert varname not in var2val
        for var in right_ct[0, i]:
            if var not in [0, 1]:
                str_var = str(var)
                assert "+" not in str(var) and "*" not in str(var), str_var
                set_final_varnames.add(str(var))
        var2val[varname] = int(right_ct[0, i]) if right_ct[0, i] in [0, 1] \
            else str(right_ct[0, i])

    # checked for w = 3,4,5 and 6
    inv_equations = [
        (f'aF0_0_0*aE0_{ws-1}_{ws-1}*aC0_{ws-1}_{ws-1}*aC0_0_0 + aF0_0_0*aC0_0_0*aB0_{ws-1}_{ws-1}*aA0_{ws-1}_{ws-1} + '
         f'aE0_{ws-1}_{ws-1}*aE0_0_0*aC0_{ws-1}_{ws-1}*aC0_0_0 + aE0_{ws-1}_{ws-1}*aC0_{ws-1}_{ws-1}*aB0_0_0*aA0_0_0 + '
         f'aE0_0_0*aC0_0_0*aB0_{ws-1}_{ws-1}*aA0_{ws-1}_{ws-1} + aB0_{ws-1}_{ws-1}*aB0_0_0*aA0_{ws-1}_{ws-1}*aA0_0_0 + 1')
    ]

    varnames = [vn for vn in varnames if vn in set_final_varnames]

    return var2val, inv_equations, varnames


def graph_ase_coeffs2modadd_ase_anf(coeff2expr, wordsize, verbose, debug, filename, equations=None):
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
        filename = f"result-graph_ase_coeffs2modadd_ase_anf-w{ws}-{now}.txt"

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
    c = get_symbolic_anf(1, 4 * ws, 4 * ws, ct_terms=True, prefix_inputs="x",
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


def find_ase_pmodadd_slow(wordsize, check, threads, verbose, debug, filename):
    """Find all affine self-equivalences of the permuted modular addition for a fixed wordsize"""
    assert wordsize <= 6

    verbose = verbose or debug

    ws = wordsize
    ccz_anf_name = "H"
    permuted = 1

    if filename is True:
        now = datetime.datetime.now()
        now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
        filename = f"result-find_ase_pmodadd_slow-w{ws}-{now}.txt"

    ccz_modadd_anf = get_ccz_modadd_anf(ws, name=ccz_anf_name, permuted=permuted)
    admissible_mapping = get_admissible_mapping(ws, name=ccz_anf_name, permuted=permuted)

    num_input_anf_vars = 2*ws
    if ws <= 6:
        modadd_anf = get_modadd_anf(ws, permuted=permuted)
    else:
        modadd_anf = None

    prefix_se_coeffs = "a"

    deg = 1
    ct_terms = True
    return_ccz_se = False

    # 1st pass without invertibility

    first_pass_invertibility = False
    first_pass_verbose = False
    first_pass_debug = False
    first_pass_bpr = None
    first_pass_solve_args = {
        "return_mode": "raw_equations",  # no need to solve (no LC found w/o invertibility)
    }

    raw_equations = find_self_equivalence(
        ccz_modadd_anf, admissible_mapping,
        anf=modadd_anf, num_input_anf_vars=num_input_anf_vars,
        #
        left_se_degree=deg, inv_right_se_degree=deg, inv_left_se_degree=deg, right_se_degree=deg,
        prefix_se_coeffs=prefix_se_coeffs, se_ct_terms=ct_terms,
        #
        add_invertibility_equations=first_pass_invertibility,
        #
        return_ccz_se=return_ccz_se,
        #
        check_se=check,
        #
        bpr=first_pass_bpr,
        threads=threads,
        verbose=first_pass_verbose, debug=first_pass_debug, filename=filename,
        #
        **first_pass_solve_args
    )

    smart_print = get_smart_print(filename)
    if verbose:
        smart_print(f"{get_time()} | raw equations without invertibility constraints obtained")

    bpr = raw_equations[0].parent()
    fixed_vars, _ = find_fixed_vars(
        raw_equations, only_linear=True,
        initial_r_mode="gauss", repeat_with_r_mode="gauss",
        initial_fixed_vars=None, bpr=bpr, check=check,
        verbose=verbose, debug=debug, filename=filename)

    invertibility = True

    solve_args = {
        "reduction_mode": "gauss",  # gauss obtained better eqs than groebner
        "only_linear_fixed_vars": False,  # w/o too many SAT solutions
        "num_sat_solutions": sage.all.infinity,
        "return_mode": "symbolic_coeffs",
        # "initial_equations": equations,  # no need to pass redundant equations
        "initial_fixed_vars": fixed_vars,
        "find_linear_combinations_in_solutions": True,
        "num_sols_per_base_sol_to_check": 0,
        "return_total_num_solutions": True,
    }

    if verbose:
        smart_print()

    symbolic_coeffs, equations, num_total_solutions = find_self_equivalence(
        ccz_modadd_anf, admissible_mapping,
        anf=modadd_anf, num_input_anf_vars=num_input_anf_vars,
        #
        left_se_degree=deg, inv_right_se_degree=deg, inv_left_se_degree=deg, right_se_degree=deg,
        prefix_se_coeffs=prefix_se_coeffs, se_ct_terms=ct_terms,
        #
        add_invertibility_equations=invertibility,
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

    smart_print(f"\nnum_total_solutions: {num_total_solutions} = 2^({math.log2(num_total_solutions)})")

    variables = list(reversed([v for v in bpr.gens()[4*ws:] if v not in symbolic_coeffs]))
    smart_print(f"non-fixed variables ({len(variables)} out of {len(bpr.gens()[4*ws:])}): {variables}")

    smart_print("equations:")
    for eq in equations:
        smart_print(f"\t{eq}")

    smart_print(f"symbolic_coeffs = {symbolic_coeffs}\n")

    return symbolic_coeffs, equations, num_total_solutions


def find_ase_pmodadd_with_shape(wordsize, check, threads, save_coeffs_eqs, verbose, debug, filename, lse=False):
    """Find all affine self-equivalences of the permuted modular addition for a fixed wordsize
    using a predefined shape."""
    assert wordsize >= 3, "only supported for wordsize >= 3"

    verbose = verbose or debug

    ws = wordsize
    ccz_anf_name = "H"
    permuted = 1

    if filename is True:
        now = datetime.datetime.now()
        now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
        filename = f"result-find_ase_pmodadd_with_shape-w{ws}{'-lse' if lse else ''}-{now}.txt"

    num_input_anf_vars = 2*ws
    if ws <= 6:
        modadd_anf = get_modadd_anf(ws, permuted=permuted)
    else:
        modadd_anf = None

    prefix_se_coeffs = "a"

    deg = 1
    ct_terms = True
    return_ccz_se = False

    invertibility = False  # determinant constraint obtain from initial_equations
    ignore_diagonal_equations = True  # no diagonal equations added with shape

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
    ccz_se_anf = get_symbolic_anf(1, 4 * ws, 4 * ws, ct_terms=True, prefix_inputs="x",
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

    if lse:
        initial_equations.extend(get_zero_constant_terms_equations(ccz_se_anf, wordsize, verbose, debug, filename))

    solve_args = {
        "reduction_mode": "gauss",  # gauss obtained better eqs than groebner
        "only_linear_fixed_vars": False,  # w/o too many SAT solutions
        "num_sat_solutions": sage.all.infinity,
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
        left_se_degree=deg, inv_right_se_degree=deg,
        inv_left_se_degree=deg, right_se_degree=deg,
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

    smart_print(f"\nnum_total_solutions: {num_total_solutions} = 2^({math.log2(num_total_solutions)})")

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
                value = bpr(bpr(value).subs(symbolic_coeffs))
                for v in value.variables():
                    var2found[str(v)] = True
                value = str(value)
        str_symbolic_coeffs.append((var, value))

    smart_print(f"graph_se_coeffs = {str_symbolic_coeffs}\n")

    assert set(var2found.values()) == {True}, f"{var2found}"
    assert len(equations) == 1

    if save_coeffs_eqs:
        if lse:
            filename_sobj = f"stored_lse_pmodadd_w{ws}.sobj"
        else:
            filename_sobj = f"stored_ase_pmodadd_w{ws}.sobj"
        str_equations = tuple([str(eq) for eq in equations])
        sage.all.save((str_symbolic_coeffs, str_equations), filename_sobj, compress=True)

    return str_symbolic_coeffs, equations, num_total_solutions


def get_zero_constant_terms_equations(c_anf, wordsize, verbose, debug, filename):
    """Get the equations to reduce the ASE of pmodadd to LSE."""
    verbose = verbose or debug

    ws = wordsize
    ccz_anf_name = "H"
    permuted = 1

    assert filename is not True
    smart_print = get_smart_print(filename)

    admissible_mapping = get_admissible_mapping(ws, name=ccz_anf_name, permuted=permuted)

    bpr = c_anf[0].parent()
    c_input_vars = bpr.gens()[:4*ws]

    if verbose and wordsize <= 8:
        smart_print(f"- C:")
        smart_print(get_anf_coeffmatrix_str(c_anf, c_input_vars))

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
        c_anf, {c_input_vars[i]: inv_am_anf[i] for i in range(num_c_input_vars)}, bpr)
    l_c_linv = substitute_anf(
        am_anf, {c_input_vars[i]: l_c_linv[i] for i in range(num_c_input_vars)}, bpr)

    if verbose and wordsize <= 8:
        smart_print(f"- L C L^(-1):")
        smart_print(get_anf_coeffmatrix_str(l_c_linv, c_input_vars))

    if verbose:
        smart_print("Getting equations to set to 0 the constant terms of L C L:")

    equations = set()
    replacements = {v: bpr(0) for v in c_input_vars}
    for index_component, component in enumerate(l_c_linv):
        component = bpr(component.subs(replacements))
        if verbose:
            smart_print(f"\t{index_component}-th component | 0 == {component}")
        equations.add(component)
    return list(equations)


def _get_number_self_equivalences(wordsize, verbose=False, lse=False):
    """Get the number of affine/linear SE of the permuted modular addition
    using the slow algorithm of Biryukov.

        >>> _get_number_self_equivalences(2, lse=True)
        192
        >>> _get_number_self_equivalences(2, lse=False)
        3072
        >>> _get_number_self_equivalences(3, lse=True)
        768

    """
    from boolcrypt.modularaddition import get_modadd_lut
    from boolcrypt.equivalence import get_number_self_le, get_number_self_ae
    if lse:
        assert wordsize <= 4
    else:
        assert wordsize <= 3
    lut = get_modadd_lut(wordsize, permuted=True)
    if lse:
        result = get_number_self_le(lut)
    else:
        result = get_number_self_ae(lut, verbose=verbose, debug=verbose)
    if verbose:
        from math import log2
        print("permuted modadd with wordsize {} has {} = 2^{} {} SE".format(
            wordsize, result, log2(result), "linear" if lse else "affine"))
    return result


if __name__ == '__main__':
    sys.setrecursionlimit(sys.getrecursionlimit()*1000)

    wordsize = 3
    check = True
    threads = 4

    save = False
    verbose = True
    debug = False
    filename = None

    lse = False

    symbolic_coeffs, equations, _ = find_ase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename, lse)
    graph_ase_coeffs2modadd_ase_anf(symbolic_coeffs, wordsize, verbose, debug, filename)
    # graph_ase_coeffs2modadd_ase_anf(symbolic_coeffs, wordsize, verbose, debug, filename, equations=equations)

    # find_ase_pmodadd_slow(wordsize, check, threads, verbose, debug, filename)

    # # - run find_ase_pmodadd_slow and find_ase_pmodadd_with_shape for multiple wordsizes
    # import time
    # threads = 4
    # save = False
    # verbose = True
    # debug = False
    # filename = True
    # for wordsize in [2, 3, 4, 5, 6, 16, 24, 32, 48, 64]:
    #     if wordsize == 2:
    #         check = True
    #         find_ase_pmodadd_slow(wordsize, check, threads, verbose, debug, filename)
    #     elif 3 <= wordsize <= 6:
    #         check = True
    #         find_ase_pmodadd_slow(wordsize, check, threads, verbose, debug, filename)
    #         check = False
    #         symbolic_coeffs, _, _ = find_ase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)
    #         graph_ase_coeffs2modadd_ase_anf(symbolic_coeffs, wordsize, verbose, debug, filename)
    #     else:
    #         check = False
    #         symbolic_coeffs, _, _ = find_ase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)
    #         graph_ase_coeffs2modadd_ase_anf(symbolic_coeffs, wordsize, verbose, debug, filename)

    # - save coeffs and eqs of ASE for multiple wordsize
    # threads = 4
    # save = True
    # verbose = False
    # debug = False
    # check = False
    # filename = False
    # for wordsize in [16, 24, 32, 48, 64]:
    #     find_ase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)

    # # - load coeffs and eqs of ASE
    # verbose = True
    # debug = False
    # filename = None
    # for wordsize in [16, 24, 32, 48, 64]:
    #     filename_sobj = f"stored_ase_pmodadd_w{wordsize}.sobj"
    #     coeff2expr, equations = sage.all.load(filename_sobj, compress=True)
    #     a, b_inv = graph_ase_coeffs2modadd_ase_anf(coeff2expr, wordsize, verbose, debug, filename)
    #     print(equations)
    #     print(a[0])
    #     print("...")
    #     print(b_inv[-1], "\n")

    # # - check affine cardinality 3 * (2**(2 * {ws} + 8) and linear cardinality 3 * (2**(2 * {ws} + 2)
    # threads = 4
    # check = False
    # save = False
    # verbose = False
    # debug = False
    # now = datetime.datetime.now()
    # now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
    # filename = f"result-cardinality_ase_pmodadd-{now}.txt"
    # smart_print = get_smart_print(filename)
    # for wordsize in range(3, 64 + 1):
    #     ws = wordsize
    #     _, _, num_total_solutions = find_ase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)
    #     smart_print(f"w = {ws} | affine | num_total_solutions = {num_total_solutions} | "
    #                 f"{3 * (2**(2 * ws + 8))} = 3 * (2**(2 * {ws} + 8)")
    #     if num_total_solutions != 3 * (2**(2 * ws + 8)):
    #         raise ValueError(f"invalid number of affine self-equivalences")
    #     _, _, num_total_solutions = find_ase_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename, lse=True)
    #     smart_print(f"w = {ws} | linear | num_total_solutions = {num_total_solutions} | "
    #                 f"{3 * (2**(2 * ws + 2))} = 3 * (2**(2 * {ws} + 2)")
    #     if num_total_solutions != 3 * (2**(2 * ws + 2)):
    #         raise ValueError(f"invalid number of linear self-equivalences")
