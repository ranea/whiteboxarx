"""Find quasi-linear quadratic implicit functions of the permuted modular addition.

Given the well-known implicit T of pmoddadd, this script finds a CCZ C' of pmodadd
such that T C' is quasi-linear.

F(x, y) is quasi-linear if for any fixed x0, F(x0, y) is linear (up to a constant).
"""
import collections
import itertools
import math
import sys
import datetime
import warnings

from boolcrypt.utilities import (
    BooleanPolynomialRing, get_num_inputs_anf, is_balanced,
    matrix2anf, get_ct_coeff, get_smart_print, get_anf_coeffmatrix_str,
    substitute_anf, get_time, anf2matrix, get_all_symbolic_coeff, get_symbolic_anf,
    int2vector, BooleanPolynomialVector, str2bp
)
from boolcrypt.equivalence import check_ccz_equivalence_anf
from boolcrypt.functionalequations import (
    _sp, find_fixed_vars, solve_functional_equation, find_inverse,
)
from boolcrypt.cczselfequivalence import _get_lowdeg_inv_equations
from boolcrypt.modularaddition import (
    get_modadd_anf, get_ccz_modadd_anf, get_admissible_mapping,
    get_implicit_modadd_anf
)

import sage.all

from sage.sat.boolean_polynomials import solve as solve_sat

GF = sage.all.GF
PolynomialRing = sage.all.PolynomialRing
BooleanPolynomialRing = sage.all.BooleanPolynomialRing


def check_partial_fixed_implicit_is_a_permutation(wordsize, verbose):
    """Check T(x_0, y) is invertible for all x_0, with T implicit of pmodadd."""
    ws = wordsize
    implicit_anf = get_implicit_modadd_anf(ws, permuted=True, only_x_names=True)
    bpr = BooleanPolynomialRing(names=["x" + str(i) for i in range(2 * ws, 4 * ws)])

    if verbose:
        print("\nws:", ws, "|", get_num_inputs_anf(implicit_anf), len(implicit_anf))

    for x in range(0, 2 ** (2 * ws)):
        x = int2vector(x, 2 * ws)
        rep = {"x" + str(i): int(x[i]) for i in range(len(x))}
        implicit_anf_x0 = [bpr(f.subs(rep)) for f in implicit_anf]
        assert get_num_inputs_anf(implicit_anf_x0) == len(implicit_anf_x0)
        is_inv = is_balanced(implicit_anf_x0)
        if verbose:
            print(f"\tx0: {x}, T(x_0, y) is a permutation: {is_inv}")
        if not is_inv:
            raise ValueError(f"found non-invertible T({x}, y)")

    if verbose:
        print("All T(x_0, y) are permutations")


# copy of cczselfequivalence.find_self_equivalence with
# add_allones_equations and modified invertibility section
def find_self_equivalence_quasilinear_implicit_pmodadd(
    # main args
    ccz_anf, admissible_mapping,
    # alternative modes
    ccz_anf_implicit=False,
    # degree args
    left_se_degree=1, inv_right_se_degree=1, inv_left_se_degree=1, right_se_degree=1, se_ct_terms=True,
    # optimization constraints
    ignore_diagonal_equations=False,
    add_invertibility_equations=True, ignore_determinant_equation=False,
    add_allones_equations=None,  # NEW PARAMETER
    check_se=True,
    bpr=None,
    # optional input args
    ccz_se_anf=None,
    prefix_se_coeffs="c",
    input_ccz_anf_vars=None,
    anf=None, input_anf_vars=None, num_input_anf_vars=None,
    # optional output args
    return_ccz_se=False,
    # printing args
    verbose=False, debug=False, filename=None,
    # extra args passed to solve_functional_equation()
    **solve_args
):
    smart_print = get_smart_print(filename)

    if debug:
        verbose = True

    if return_ccz_se is False or left_se_degree != 1 or inv_left_se_degree != 1 or ccz_anf_implicit:
        raise ValueError("invalid arguments")

    if left_se_degree == 1 or inv_left_se_degree == 1:
        assert left_se_degree == inv_left_se_degree == 1

    if right_se_degree == 1 or inv_right_se_degree == 1:
        assert right_se_degree == inv_right_se_degree == 1

    assert not isinstance(ccz_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    if input_ccz_anf_vars is None:
        aux_bpr = ccz_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in ccz_anf)
        input_ccz_anf_vars = aux_bpr.gens()

    missing_anf = anf is None
    if not missing_anf:
        assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
        if input_anf_vars is None:
            aux_bpr = anf[0].parent()
            assert all(aux_bpr == f.parent() for f in anf)
            input_anf_vars = aux_bpr.gens()
    else:
        assert num_input_anf_vars is not None
        anf_bpr = BooleanPolynomialRing(n=num_input_anf_vars, names='x')
        input_anf_vars = [anf_bpr("x" + str(i)) for i in range(num_input_anf_vars)]
        if not ccz_anf_implicit:
            anf = [anf_bpr(0) for _ in range(len(ccz_anf))]
        else:
            anf = [anf_bpr(0) for _ in range(len(input_ccz_anf_vars) - num_input_anf_vars)]

    assert all(not str(v).startswith(prefix_se_coeffs)
               for v in list(input_anf_vars) + list(input_ccz_anf_vars))
    assert not prefix_se_coeffs.startswith("x")
    if not ccz_anf_implicit:
        assert len(anf) == len(ccz_anf)
        assert len(input_anf_vars) == len(input_ccz_anf_vars)
    else:
        assert len(input_ccz_anf_vars) == len(input_anf_vars) + len(anf)
        if add_invertibility_equations:
            if verbose:
                smart_print('ignoring add_invertibility_equations when ccz_anf_implicit is True')
        add_invertibility_equations = False

    if ignore_diagonal_equations:
        assert bpr is not None or add_invertibility_equations is False  # t_l_c_linv not created when ignore_diagonal_equations

    if solve_args.get("return_mode", None) == "list_coeffs":
        raise NotImplementedError('return_mode="list_coeffs" not supported in find_self_equivalence')

    initial_equations = solve_args.get("initial_equations", [])
    initial_fixed_vars = solve_args.get("initial_fixed_vars", collections.OrderedDict())
    ignore_initial_parsing = solve_args.get("ignore_initial_parsing", False)
    check_find_fixed_vars = solve_args.get("check_find_fixed_vars", True)

    if ignore_initial_parsing and bpr is None:
        raise ValueError("bpr must be given if ignore_initial_parsing is True")

    if initial_equations is None:
        initial_equations = []
    if initial_fixed_vars is None:
        initial_fixed_vars = collections.OrderedDict()

    if verbose:
        smart_print("finding SE of F through the graph of G "
                    f"with degrees {left_se_degree, inv_right_se_degree} and "
                    f"inverse degrees {inv_left_se_degree, right_se_degree}")
        smart_print("- F:")
        smart_print(get_anf_coeffmatrix_str(anf, input_anf_vars))
        smart_print(f"- G (CCZ-{'implicit-' if ccz_anf_implicit else ''}equivalent of F):")
        smart_print(get_anf_coeffmatrix_str(ccz_anf, input_ccz_anf_vars))
        smart_print("")

    # 1 - Create C such that T L C L^(-1) is quasi-linear

    if verbose:
        smart_print(f"{get_time()} | computing C")

    # use anf and input_anf_vars instead of ccz_anf and input_ccz_anf_vars
    # to consider also the case ccz_anf_implicit=True
    num_c_input_vars = len(input_anf_vars) + len(anf)
    c_deg = max(left_se_degree, inv_right_se_degree)

    if bpr is not None:
        all_varnames = bpr.variable_names()
        num_total_symbolic_coeffs = len(all_varnames) - num_c_input_vars

    if ignore_initial_parsing:
        if ccz_se_anf is None:
            c_0 = get_symbolic_anf(c_deg, num_c_input_vars, len(input_anf_vars), ct_terms=se_ct_terms,
                                   prefix_inputs="x", prefix_coeffs=prefix_se_coeffs + "a",
                                   bpr=bpr, coeff2expr=initial_fixed_vars)
            c_1 = get_symbolic_anf(c_deg, num_c_input_vars, len(anf), ct_terms=se_ct_terms,
                                   prefix_inputs="x", prefix_coeffs=prefix_se_coeffs + "b",
                                   bpr=bpr, coeff2expr=initial_fixed_vars)
        else:
            assert len(ccz_se_anf) == len(input_anf_vars) + len(anf)
            c_0, c_1 = BooleanPolynomialVector(), BooleanPolynomialVector()
            for i in range(len(input_anf_vars) + len(anf)):
                assert ccz_se_anf[i].parent() == bpr
                if i < len(input_anf_vars):
                    c_0.append(ccz_se_anf[i])
                else:
                    c_1.append(ccz_se_anf[i])

        if ccz_anf_implicit:
            d = get_symbolic_anf(c_deg, len(ccz_anf), len(ccz_anf), ct_terms=False,
                                 prefix_inputs="x", prefix_coeffs=prefix_se_coeffs + "d",
                                 bpr=bpr, coeff2expr=initial_fixed_vars)
        c = BooleanPolynomialVector()
        for component in itertools.chain(c_0, c_1):
            c.append(component)
        c_input_vars = [bpr("x" + str(i)) for i in range(num_c_input_vars)]
    else:
        if ccz_se_anf is None:
            # cannot use coeff2ct since all coeffs are needed to build bpr
            c_0 = get_symbolic_anf(c_deg, num_c_input_vars, len(input_anf_vars), ct_terms=se_ct_terms,
                                   prefix_inputs="x", prefix_coeffs=prefix_se_coeffs+"a")
            c_1 = get_symbolic_anf(c_deg, num_c_input_vars, len(anf), ct_terms=se_ct_terms,
                                   prefix_inputs="x", prefix_coeffs=prefix_se_coeffs+"b")
        else:
            assert len(ccz_se_anf) == len(input_anf_vars) + len(anf)
            c_0, c_1 = BooleanPolynomialVector(), BooleanPolynomialVector()
            for i in range(len(input_anf_vars) + len(anf)):
                if i < len(input_anf_vars):
                    c_0.append(ccz_se_anf[i])
                else:
                    c_1.append(ccz_se_anf[i])
        if ccz_anf_implicit:
            d = get_symbolic_anf(c_deg, len(ccz_anf), len(ccz_anf), ct_terms=False,
                                 prefix_inputs="x", prefix_coeffs=prefix_se_coeffs+"d")

        if bpr is None:
            all_varnames = list(c_0[0].parent().variable_names())
            all_varnames.extend(vn for vn in c_1[0].parent().variable_names() if vn not in all_varnames)
            for value in initial_fixed_vars.values():
                if value in [0, 1]:
                    continue
                if isinstance(value, str):
                    value = sage.all.symbolic_expression(value)
                for var in value.variables():
                    varname = str(var)
                    if varname not in all_varnames:
                        all_varnames.append(varname)
            for eq in initial_equations:
                if isinstance(eq, str):
                    eq = sage.all.symbolic_expression(eq)
                for var in eq.variables():
                    varname = str(var)
                    if varname not in all_varnames:
                        all_varnames.append(varname)
            if ccz_anf_implicit:
                all_varnames.extend(vn for vn in d[0].parent().variable_names() if vn not in all_varnames)
            # if ignore_determinant_equation:
            #     # default assignments is x <- y if bpr order is x > y > ...
            #     # to have assignments ac <- aa/ab, bpr order must be ac > aa/ab
            #     aux_varnames = get_symbolic_anf(1, num_c_input_vars, len(c_0) + len(c_1), prefix_inputs="x",
            #                                     prefix_coeffs=prefix_se_coeffs+"c", return_varnames=True)
            #     all_varnames = all_varnames[:num_c_input_vars] + aux_varnames[num_c_input_vars:] + \
            #                    [v for v in all_varnames[num_c_input_vars:] if v not in aux_varnames]
            num_total_symbolic_coeffs = len(all_varnames) - num_c_input_vars
            if solve_args.get("only_linear_fixed_vars", False):
                order = "deglex"
            else:
                order = "lex"
            bpr = BooleanPolynomialRing(len(all_varnames), all_varnames, order=order)

        aux_ifv = collections.OrderedDict()
        for var, value in initial_fixed_vars.items():
            aux_ifv[bpr(var)] = bpr(value)
        initial_fixed_vars = aux_ifv

        c = BooleanPolynomialVector()
        aux_c_0 = BooleanPolynomialVector()
        aux_c_1 = BooleanPolynomialVector()
        for component in c_0:
            component = bpr(bpr(component).subs(initial_fixed_vars))
            c.append(component)
            aux_c_0.append(component)
        for component in c_1:
            component = bpr(bpr(component).subs(initial_fixed_vars))
            c.append(component)
            aux_c_1.append(component)
        c_0 = aux_c_0
        c_1 = aux_c_1

        c_input_vars = [bpr("x" + str(i)) for i in range(num_c_input_vars)]

        aux_ie = BooleanPolynomialVector()
        for eq in initial_equations:
            eq = bpr(bpr(eq).subs(initial_fixed_vars))
            if eq == 0:
                continue
            if eq == 1:
                raise ValueError("found invalid initial equation 0 == 1")
            aux_ie.append(eq)
        initial_equations = aux_ie

        if ccz_anf_implicit:
            aux_d = BooleanPolynomialVector()
            for component in d:
                component = bpr(bpr(component).subs(initial_fixed_vars))
                aux_d.append(component)
            d = aux_d

        aux_ccz_anf = BooleanPolynomialVector()
        for component in ccz_anf:
            aux_ccz_anf.append(bpr(component))
        ccz_anf = aux_ccz_anf

        input_ccz_anf_vars = [bpr(v) for v in input_ccz_anf_vars]

    if verbose:
        smart_print("- C (self-equivalence of Graph(G)):")
        smart_print(get_anf_coeffmatrix_str(c, c_input_vars))
        if not debug:
            smart_print("number of C input variables:", num_c_input_vars)
            smart_print("number of symbolic coefficients:", num_total_symbolic_coeffs)
            if initial_fixed_vars:
                smart_print("number of initial fixed vars:", len(initial_fixed_vars))
            if initial_equations:
                smart_print("number of initial equations:", len(initial_equations))
        if debug:
            smart_print(f"input variables ({num_c_input_vars}): {all_varnames[:num_c_input_vars]}")
            smart_print(f"symbolic coefficients ({num_total_symbolic_coeffs}): "
                        f"{all_varnames[-num_total_symbolic_coeffs:]}")
            smart_print(bpr)
            if initial_fixed_vars:
                smart_print(f"initial fixed vars ({len(initial_fixed_vars)}):")
                for var, value in initial_fixed_vars.items():
                    smart_print(f"\t{var} <- {_sp(value)}")
            if initial_equations:
                smart_print(f"initial equations ({len(initial_equations)}):")
                for eq in initial_equations:
                    smart_print("\t" + _sp(eq))
            if ccz_anf_implicit:
                smart_print("- D (from G = D G C):")
                smart_print(get_anf_coeffmatrix_str(d, [bpr("x" + str(i)) for i in range(len(ccz_anf))]))
        smart_print("")

    # 1.2  Getting the equations T L C L^(-1) = quasi-linear

    equations = BooleanPolynomialVector(initial_equations)

    # variables used when adding quasi-linear equations and when checking at the end
    ws = len(c_input_vars) // 4
    implicit_modadd = [bpr(f) for f in get_implicit_modadd_anf(ws, permuted=True, only_x_names=True)]
    output_vars = c_input_vars[2*ws:]

    if not ignore_diagonal_equations:
        if verbose:
            if left_se_degree < c_deg or inv_right_se_degree < c_deg:
                aux = f" with top/bottom degrees {left_se_degree}/{inv_right_se_degree}"
            else:
                aux = ""
            smart_print(f"{get_time()} | getting equations from T L C L^(-1) = quasi-linear{aux}")
            smart_print(" - T:")
            smart_print(get_anf_coeffmatrix_str(implicit_modadd, c_input_vars))

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

        if len(input_anf_vars) <= 6 and not missing_anf:  # complexity 2^12
            inv_am_matrix = anf2matrix(inv_am_anf, c_input_vars) if ccz_anf_implicit else None
            if not ccz_anf_implicit:
                result_check = check_ccz_equivalence_anf(
                    ccz_anf, anf, am_matrix,
                    f_input_vars=input_ccz_anf_vars, g_input_vars=input_anf_vars, a_input_vars=c_input_vars)
            else:
                result_check = check_ccz_equivalence_anf(
                    anf, ccz_anf, inv_am_matrix, g_implicit=True,
                    f_input_vars=input_anf_vars, g_input_vars=input_ccz_anf_vars, a_input_vars=c_input_vars)
            if result_check is False:
                raise ValueError("L(Graph(G)) != Graph(F)")

        # l_c_linv_* variables changed to t_l_c_linv_*
        t_l_c_linv = substitute_anf(c, {c_input_vars[i]: inv_am_anf[i] for i in range(num_c_input_vars)}, bpr)
        t_l_c_linv = substitute_anf(am_anf, {c_input_vars[i]: t_l_c_linv[i] for i in range(num_c_input_vars)}, bpr)
        t_l_c_linv_b4_t = t_l_c_linv
        t_l_c_linv = substitute_anf(implicit_modadd, {c_input_vars[i]: t_l_c_linv[i] for i in range(num_c_input_vars)}, bpr)
        t_l_c_linv = list(t_l_c_linv)
        assert t_l_c_linv_b4_t[0] != t_l_c_linv[0]

        if verbose:
            smart_print("- L C L^(-1) (L admissible mapping L(Graph(G)=Graph(F)):")
            smart_print(get_anf_coeffmatrix_str(t_l_c_linv_b4_t, c_input_vars))
            smart_print("- T L C L^(-1) (L admissible mapping L(Graph(G)=Graph(F)):")
            smart_print(get_anf_coeffmatrix_str(t_l_c_linv, c_input_vars))
        if debug:
            if left_se_degree < c_deg or inv_right_se_degree < c_deg:
                aux = f" with degrees {left_se_degree}/{inv_right_se_degree}"
            else:
                aux = ""
            smart_print(f"equations from T L C L^(-1) = quasi-linear{aux}:")

        index_eq = len(initial_equations)
        for index_component, component in enumerate(t_l_c_linv):
            all_coeffs = get_all_symbolic_coeff(component, c_input_vars)

            for monomial, coeff in all_coeffs.items():
                monomial_vars = [bpr(v) for v in monomial.variables()]
                if len(monomial_vars) <= 1:
                    continue

                assert len(monomial_vars) == 2

                # degree equations removed and diagonal equations replaced by quasi-linear equations

                # check no z_i z_j, t_i t_j, z_i t_j terms appears
                if monomial_vars[0] in output_vars and monomial_vars[1] in output_vars:
                    if coeff == 0:
                        continue
                    if coeff == 1:
                        raise ValueError(f"T L C L^(-1) cannot be quasi-linear, {index_component}-th component "
                                         f"has monomial {monomial} with non-zero coeff {coeff}")
                    if debug:
                        smart_print(f"\teq[{index_eq}]: ({index_component}-th component) "
                                    f"0 == coefficient(monomial={monomial}) = {_sp(coeff)}")
                    equations.append(coeff)
                    index_eq += 1

        if len(equations) == len(initial_equations) and verbose:
            smart_print("no equations added from T L C L^(-1) = diagonal")

        if verbose:
            smart_print("")

    assert add_allones_equations in [None, False, "print", "fix", "check"]
    if add_allones_equations:
        assert ignore_diagonal_equations is False
        len_eqs_b4_or = len(equations)
        cvar2index = {v: i for i, v in enumerate(c_input_vars)}

        if verbose:
            smart_print(f"{get_time()} | adding AllOnes equations over L C L^(-1) (mode {add_allones_equations}):")
            smart_print(get_anf_coeffmatrix_str(t_l_c_linv_b4_t, c_input_vars))

        if add_allones_equations == "print":
            or_coeffs = set()
            or_coeffs_list = []
        for index_component, component in enumerate(t_l_c_linv_b4_t):
            all_coeffs = get_all_symbolic_coeff(component, c_input_vars)

            for monomial, coeff in all_coeffs.items():
                monomial_vars = [bpr(v) for v in monomial.variables()]
                if len(monomial_vars) == 0:
                    continue

                assert len(monomial_vars) == 1

                index_var = cvar2index[monomial_vars[0]]
                ic, iv = index_component, index_var

                if (ic < 2*ws and iv >= 2*ws) or (ic >= 2*ws and iv < 2*ws):
                    if ws in [2]:
                        # w2: ic < 2w, iv == x5,         ic >= 2w, iv == x1
                        non_ones_columns = (ic < 2*ws and iv in [3*ws-1]) or (ic >= 2*ws and iv in [ws-1])
                    else:
                        # w3: ic < 2w, iv == x8,         ic >= 2w, iv == x2
                        # w4: ic < 2w, iv == x10, x11,   ic >= 2w, iv == x2, x3
                        non_ones_columns = (ic < 2*ws and 3*ws-1-(ws-3) <= iv <= 3*ws-1) or (ic >= 2*ws and ws-1-(ws-3) <= iv <= ws-1)

                    if non_ones_columns:
                        pass
                    else:
                        if debug:
                            smart_print(f"\teq[{index_eq}]: ({index_component}-th component) "
                                        f"coefficient(monomial={monomial}) = {_sp(coeff)}")
                        if add_allones_equations == "print":
                            or_coeffs.add(coeff)
                            or_coeffs_list.append([index_component, index_var, str(coeff)])
                        elif add_allones_equations == "fix":
                            if coeff != 1:
                                equations.append(coeff + bpr(1))
                        elif add_allones_equations == "check":
                            if coeff != 1:
                                raise ValueError(f"found non-one | eq[{index_eq}]: ({index_component}-th component) "
                                                 f"coefficient(monomial={monomial}) = {_sp(coeff)}")
                        else:
                            assert False

        if add_allones_equations == "print":
            or_coeffs = sorted(or_coeffs)
            smart_print("\n - or_coeffs/or_coeffs_list:")
            smart_print([str(eq) for eq in or_coeffs])
            smart_print(or_coeffs_list)
            exit(-1)

        # def or_bits(a, b):
        #     return a + b + (a * b)
        # equations.append(bpr(sage.all.reduce(or_bits, or_coeffs)) + bpr(1))

        if verbose:
            smart_print(f"added {len(equations) - len_eqs_b4_or} AllOnes equations")
            if debug:
                for i in range(len_eqs_b4_or, len(equations)):
                    smart_print(f"\t{_sp(equations[i])}")
            smart_print("")

    # 1.5 - Reducing initial and diagonal equations

    if solve_args.get("return_mode", None) != "raw_equations" and not ignore_diagonal_equations:
        if verbose:
            smart_print(f"{get_time()} | finding fixed variables and reducing initial and quasi-linear equations")

        reduction_mode = solve_args.get("reduction_mode", "gauss")
        initial_fixed_vars, equations = find_fixed_vars(
            equations, only_linear=True,
            initial_r_mode=reduction_mode, repeat_with_r_mode=reduction_mode,
            initial_fixed_vars=initial_fixed_vars, bpr=bpr, check=check_find_fixed_vars,
            verbose=verbose, debug=debug, filename=filename)

        c = list(substitute_anf(c, initial_fixed_vars, bpr))  # to list to be sliced

        if verbose:
            smart_print("- C (reduced by initial and quasi-linear equations):")
            smart_print(get_anf_coeffmatrix_str(c, c_input_vars))

        if verbose:
            smart_print("")

    # 2 - Add invertibility equations imposed over C

    len_eqs_b4_inv = len(equations)
    if add_invertibility_equations:
        if verbose:
            smart_print(f"{get_time()} | adding invertibility equations over C")

        assert left_se_degree == 1 and inv_right_se_degree == 1

        base_matrix = anf2matrix(c, c_input_vars)

        # is_special_shape = True
        bottom_right = base_matrix.submatrix(row=2*ws)
        for col in range(2 * ws + 1 + ws - 1):  # 2*ws + ws
            if col == 2 * ws:
                continue
            column = bottom_right.column(col).list()
            if not all(cell == 0 for row, cell in enumerate(column) if row == 0 or row >= ws):
                raise ValueError(f"is_special_shape check failed:\n{bottom_right}\n{col}-th col: {column}\n"
                                 f"cells: {[(cell == 0, row, cell) for row, cell in enumerate(column) if row == 0 or row >= ws]}")
                # is_special_shape = False
                # break
        # assert is_special_shape
        bottom_right = bottom_right.delete_columns([col for col in range(2 * ws + 1 + ws - 1) if col != 2*ws])
        bottom_right = bottom_right.delete_rows([row for row in range(1 + ws - 1) if row != 0])
        assert bottom_right.is_square(), f"{bottom_right}"
        if verbose:
            smart_print(f"- C 'bottom right' block:\n{bottom_right}")

        # assert is_special_shape
        good_rows = [row for row in range(2*ws + 1, 2*ws + 1 + ws - 1)]
        upper_left = base_matrix.delete_rows([row for row in range(2*ws, 4*ws) if row not in good_rows])
        good_columns = [col for col in range(2 * ws + 1 + ws - 1) if col != 2*ws]
        upper_left = upper_left.delete_columns([col for col in range(2*ws, 4*ws) if col not in good_columns])
        assert upper_left.is_square()
        if verbose:
            smart_print(f" - C 'upper right' block: \n{upper_left}")

        lowdeg_inv_equations_added = False
        for block_matrix in [bottom_right, upper_left]:
            # depth is computed as follows:
            #   sum_{i=0}^{k} binom(n,i) < n^k + 1  (k == depth, n == nrows == num components)
            #   n^k <= 2^16 (max complexity) <==> k = k log(n,n) <= log(2^16, n)
            #   (nrows = num output vars, ncols = num inputs vars)
            depth = int(sage.all.log(2**16, block_matrix.nrows()))
            for matrix in [block_matrix, block_matrix.transpose()]:
                aux_num_input = matrix.ncols()
                matrix_anf = matrix2anf(matrix, bool_poly_ring=bpr, input_vars=c_input_vars[:aux_num_input])
                for eq in _get_lowdeg_inv_equations(matrix_anf, bpr, max_deg=2, depth=depth, input_vars=c_input_vars[:aux_num_input]):
                    lowdeg_inv_equations_added = True
                    equations.append(eq)

        if solve_args.get("return_mode", None) != "raw_equations" and lowdeg_inv_equations_added:
            reduction_mode = solve_args.get("reduction_mode", "gauss")
            initial_fixed_vars, equations = find_fixed_vars(
                equations, only_linear=True,
                initial_r_mode=reduction_mode, repeat_with_r_mode=reduction_mode,
                initial_fixed_vars=initial_fixed_vars, bpr=bpr, check=check_find_fixed_vars,
                verbose=verbose, debug=debug, filename=filename)

        if not ignore_determinant_equation:
            if lowdeg_inv_equations_added:
                bottom_right = bottom_right.subs(initial_fixed_vars)
                upper_left = upper_left.subs(initial_fixed_vars)
            equations.append(bpr(bottom_right.determinant()) + bpr(1))
            equations.append(bpr(upper_left.determinant()) + bpr(1))
        # else:
        #     smart_print(f" - calling find_inverse()")
        #     raw_eqs = find_inverse(
        #         c, inv_left_se_degree, # c already subs. with initial_fixed_vars
        #         inv_position="left", prefix_inv_coeffs=prefix_se_coeffs+"c",
        #         input_vars=c_input_vars, return_mode="raw_equations",
        #         #
        #         initial_fixed_vars=initial_fixed_vars,
        #         ignore_initial_parsing=ignore_initial_parsing,
        #         check_find_fixed_vars=check_find_fixed_vars,
        #         bpr=bpr,
        #         #
        #         verbose=False, debug=False, filename=filename
        #     )
        #     for eq in raw_eqs:
        #         equations.append(eq)

        if verbose:
            smart_print(f"added {len(equations)-len_eqs_b4_inv} invertibility equations")
            if debug:
                for i in range(len_eqs_b4_inv, len(equations)):
                    smart_print(f"\t{_sp(equations[i])}")
            smart_print("")

    # 3 - Find a Graph(G)-SE of G

    if verbose:
        smart_print(f"{get_time()} | solving the Graph(G)-self-equivalence functional equation")

    if not ccz_anf_implicit:
        #  G(c_0(u, G(u))) = c_1(u, G(u)))
        c_0 = substitute_anf(c_0, initial_fixed_vars, bpr)
        c_1 = substitute_anf(c_1, initial_fixed_vars, bpr)
        f2 = ccz_anf
        f1 = c_0
        f0 = BooleanPolynomialVector()
        for component in itertools.chain(input_ccz_anf_vars, ccz_anf):
            f0.append(component)
        f2_input_vars = input_ccz_anf_vars
        f1_input_vars = c_input_vars
        f0_input_vars = input_ccz_anf_vars
        g1 = c_1
        g0 = f0
        g1_input_vars = c_input_vars
        g0_input_vars = f0_input_vars
        lhs_anfs = [f0, f1, f2]
        lhs_input_vars = [f0_input_vars, f1_input_vars, f2_input_vars]
        rhs_anfs = [g0, g1]
        rhs_input_vars = [g0_input_vars, g1_input_vars]
    else:
        # D G C  = G
        c = substitute_anf(c, initial_fixed_vars, bpr)
        f2 = d
        f1 = ccz_anf
        f0 = c
        f2_input_vars = [bpr("x" + str(i)) for i in range(len(ccz_anf))]
        f1_input_vars = input_ccz_anf_vars
        f0_input_vars = c_input_vars
        g0 = ccz_anf
        g0_input_vars = f1_input_vars
        lhs_anfs = [f0, f1, f2]
        lhs_input_vars = [f0_input_vars, f1_input_vars, f2_input_vars]
        rhs_anfs = [g0]
        rhs_input_vars = [g0_input_vars]

    new_kwargs = solve_args.copy()
    if "num_sat_solutions" not in new_kwargs:
        new_kwargs["num_sat_solutions"] = 1
    else:
        if "return_mode" not in new_kwargs:
            raise ValueError("return_mode must be specified if num_sat_solutions is")
    if "return_mode" not in new_kwargs:
        new_kwargs["return_mode"] = "list_anfs"

    new_kwargs["ignore_initial_parsing"] = True
    new_kwargs["initial_equations"] = equations
    new_kwargs["initial_fixed_vars"] = initial_fixed_vars

    if "find_redundant_equations" in new_kwargs:
        aux_fre = BooleanPolynomialVector()
        for eq in new_kwargs["find_redundant_equations"]:
            eq = bpr(bpr(eq).subs(initial_fixed_vars))
            aux_fre.append(eq)
        new_kwargs["find_redundant_equations"] = aux_fre

    if ccz_anf_implicit:
        new_kwargs["ignore_varnames"] = [vn for vn in all_varnames if vn.startswith(prefix_se_coeffs + "d")]
        for var, val in initial_fixed_vars.copy().items():
            if str(var).startswith(prefix_se_coeffs+"d"):
                if debug:
                    smart_print(f"removing from initial_fixed_vars {var} <- {val}")
                del initial_fixed_vars[var]

    try:
        graph_solutions = solve_functional_equation(
            lhs_anfs, rhs_anfs, lhs_input_vars, rhs_input_vars, bpr=bpr,
            verbose=verbose, debug=debug, filename=filename, **new_kwargs
        )
    except ValueError as e:
        get_smart_print(filename)(f"No solution found ({e})")
        return None

    if verbose:
        smart_print("")

    # 4 - Parsing and checking L C L^(-1) is a CCZ-SE and T L C L^{-1} is quasi-linear for one solution

    if new_kwargs["return_mode"] in ["raw_equations", "lincomb_solutions"] \
            or new_kwargs.get("find_redundant_equations", None) is not None:
        return graph_solutions

    if verbose:
        smart_print(f"{get_time()} | parsing {'and checking' if check_se else ''} "
                    f"the Graph(G)-self-equivalence solutions")

    se_solutions = []
    extra_var2val = {}
    symbolic_coeffs = None
    if new_kwargs["return_mode"] == "list_anfs":
        for i in range(len(graph_solutions)):
            if solve_args.get("return_total_num_solutions", False):
                se_solutions.append(graph_solutions[0][i])
            else:
                se_solutions.append(graph_solutions[i])
    else:
        assert new_kwargs["return_mode"] in ["symbolic_anf", "symbolic_coeffs"]
        if new_kwargs["return_mode"] == "symbolic_anf":
            se_solutions = [graph_solutions[0]]
        else:
            symbolic_coeffs = graph_solutions[0]
            if not ccz_anf_implicit:
                # se_solutions[0][0][1] == c_0, se_solutions[0][1][1] == g1
                se_solutions = [
                    [
                        [
                            None, substitute_anf(c_0, symbolic_coeffs, bpr)
                        ],  # se_solutions[0][0]
                        [
                            None, substitute_anf(c_1, symbolic_coeffs, bpr)
                        ]  # se_solutions[0][1]
                    ]  # se_solutions[0]
                ]
            else:
                # se_solutions[0][0][0] == c
                se_solutions = [
                    [
                        [
                            substitute_anf(c, symbolic_coeffs, bpr)
                        ] # se_solutions[0][0]
                    ] # se_solutions[0]
                ]

        if check_se:
            extra_equations = graph_solutions[1]
            if extra_equations:
                if verbose:
                    smart_print(f"finding a solution of the remaining {len(extra_equations)} equations for checking")
                    if debug:
                        for eq in extra_equations:
                            smart_print(f"\t{_sp(eq)}")
                extra_var2val = solve_sat(extra_equations, n=1, s_threads=new_kwargs.get("threads", 1))
                if not extra_var2val:
                    raise ValueError('equations from "symbolic_anf" output are inconsistent (unsatisfiable)')
                extra_var2val = {bpr(k): bpr(v) for k, v in extra_var2val[0].items()}  # first solution
                if verbose:
                    smart_print(f" - solution: {extra_var2val}")
            free_vars = set()
            if not ccz_anf_implicit:
                aux_loop = itertools.chain(se_solutions[0][0][1], se_solutions[0][1][1])
            else:
                aux_loop = itertools.chain(se_solutions[0][0][0])
            for aux_anf in aux_loop:
                for component in aux_anf:  # avoid anf
                    for var in component.variables():
                        var = bpr(var)
                        if var not in c_input_vars and var not in extra_var2val:
                            free_vars.add(var)
            if free_vars:
                smart_print(f"setting to 0 the free variables {free_vars} for checking")
                for v in free_vars:
                    extra_var2val[v] = bpr(0)

    if ignore_diagonal_equations and (check_se or not return_ccz_se):
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

    for index_se_sol in range(len(se_solutions)):
        if not ccz_anf_implicit:
            c_0_sol = se_solutions[index_se_sol][0][1]  # f1
            c_1_sol = se_solutions[index_se_sol][1][1]  # g1
            c_sol = BooleanPolynomialVector()
            for component in itertools.chain(c_0_sol, c_1_sol):
                c_sol.append(component)
        else:
            c_sol = se_solutions[index_se_sol][0][0]  # f0

        if return_ccz_se:
            se_solutions[index_se_sol] = c_sol
            if not check_se:
                continue

        if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
            smart_print(f"Solution {index_se_sol + 1} out of {len(se_solutions)}:")

        if check_se and len(input_anf_vars) <= 8 and not ccz_anf_implicit:
            if extra_var2val:
                c_sol_fixed = substitute_anf(c_sol, extra_var2val, bpr)
                if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
                    smart_print(f"- C:")
                    smart_print(get_anf_coeffmatrix_str(c_sol, c_input_vars))
                    smart_print(f"- C (with {extra_var2val}):")
                    smart_print(get_anf_coeffmatrix_str(c_sol_fixed, c_input_vars))
            else:
                c_sol_fixed = c_sol
            aux_bpr = BooleanPolynomialRing(names=[str(v) for v in c_input_vars])
            c_sol_fixed = [aux_bpr(component) for component in c_sol_fixed]
            # if not check_ccz_equivalence_anf(ccz_anf_simple_bpr, ccz_anf_simple_bpr, c_sol_fixed):
            result_check = check_ccz_equivalence_anf(
                ccz_anf, ccz_anf, c_sol_fixed,
                f_input_vars=input_ccz_anf_vars, g_input_vars=input_ccz_anf_vars, a_input_vars=c_input_vars)
            if result_check is False:
                raise ValueError("C is not a Graph-SE of G")

        t_l_c_linv_sol = substitute_anf(
            c_sol, {c_input_vars[i]: inv_am_anf[i] for i in range(num_c_input_vars)}, bpr)
        t_l_c_linv_sol = substitute_anf(
            am_anf, {c_input_vars[i]: t_l_c_linv_sol[i] for i in range(num_c_input_vars)}, bpr)
        t_l_c_linv_sol = substitute_anf(
            implicit_modadd, {c_input_vars[i]: t_l_c_linv_sol[i] for i in range(num_c_input_vars)}, bpr)
        t_l_c_linv_sol = list(t_l_c_linv_sol)

        if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
            smart_print(f"- T L C L^(-1):")
            smart_print(get_anf_coeffmatrix_str(t_l_c_linv_sol, c_input_vars))

        if check_se:
            if extra_var2val:
                t_l_c_linv_sol_fixed = substitute_anf(t_l_c_linv_sol, extra_var2val, bpr)
                if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
                    smart_print(f"- T L C L^(-1) (with {extra_var2val}):")
                    smart_print(get_anf_coeffmatrix_str(t_l_c_linv_sol_fixed, c_input_vars))
            else:
                t_l_c_linv_sol_fixed = t_l_c_linv_sol

            aux_bpr = BooleanPolynomialRing(names=[str(v) for v in c_input_vars])
            t_l_c_linv_sol_fixed = [aux_bpr(component) for component in t_l_c_linv_sol_fixed]

            for index_component, component in enumerate(t_l_c_linv_sol_fixed):
                for monomial, coeff in get_all_symbolic_coeff(component, c_input_vars).items():
                    monomial_vars = [bpr(v) for v in monomial.variables()]
                    if len(monomial_vars) <= 1:
                        continue
                    assert len(monomial_vars) == 2
                    if monomial_vars[0] in output_vars and monomial_vars[1] in output_vars:
                        if coeff != 0:
                            raise ValueError(f"T L C L^(-1) (from {index_se_sol}-th solution) is not quasi-linear, "
                                             f"{index_component}-th component has monomial {monomial} "
                                             f"with non-zero coeff {coeff}")

    if verbose:
        smart_print("")

    # 5 - Output

    if verbose:
        smart_print(f"{get_time()} | returning outputs with mode='{new_kwargs['return_mode']}'")

    if "return_mode" not in solve_args and "num_sat_solutions" not in solve_args:
        if solve_args.get("return_total_num_solutions", False):
            smart_print("ignoring return_total_num_solutions")
        return se_solutions[0]
    elif new_kwargs['return_mode'] == "list_anfs":
        if solve_args.get("return_total_num_solutions", False):
            return se_solutions
        else:
            return se_solutions, graph_solutions[-1]
    elif new_kwargs['return_mode'] == "symbolic_anf":
        return se_solutions + list(graph_solutions[1:])
    else:
        assert new_kwargs['return_mode'] == "symbolic_coeffs"
        return [symbolic_coeffs] + list(graph_solutions[1:])


def shape(wordsize, prefix_symbolic_anf, verbose, filename):
    """Symbolic shape of the CCZ-SE of the "q" quadratic CCZ of the permuted modular addition."""
    ws = wordsize

    assert ws >= 3

    if isinstance(prefix_symbolic_anf, str):
        prefix_symbolic_anf = [prefix_symbolic_anf]
    assert len(prefix_symbolic_anf) in [1, 2], str(len(prefix_symbolic_anf))

    smart_print = get_smart_print(filename)

    var2val = collections.OrderedDict()

    # ----- LINEAR COEFFS -----

    def get_full_block(index, prefix):
        block = sage.all.zero_matrix(sage.all.SR, nrows=ws, ncols=ws)
        for i in range(ws):
            for j in range(ws):
                block[i, j] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, i, j))
        return block

    def get_A_block(index, prefix="A"):
        block = sage.all.zero_matrix(sage.all.SR, ws)
        # mid square
        for j in range(ws - 3):
            for i in range(ws - 3):
                if index in [0, 3]:
                    block[1+i, 2+j] = int(i == j)
                elif index in [1, 2]:
                    block[1+i, 2+j] = 0
                else:
                    assert False
                    # block[1+i, 2+j] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, 1+i, 2+j))
        block[ws - 2, 0] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws - 2, 0))
        for j in range(ws):  # last row
            block[ws - 1, j] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws - 1, j))
        if index in [0, 3]:
            block[0, 1] = 1
            if index == 3:
                block[ws - 1, 1] = 1
        elif index == 1:
            block[ws - 1, 1] = 0
        return block

    def get_C_block(index, prefix="C"):
        block = sage.all.zero_matrix(sage.all.SR, ws)
        block[ws - 2, 0] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws - 2, 0))
        for j in range(ws):  # last row
            block[ws - 1, j] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws - 1, j))
        return block

    def get_I_block(index, prefix="I"):
        assert index == 0
        block = get_F_block(1) + get_A_block(1)
        for i in range(ws):
            for j in range(1, ws):  # all except first column
                block[i, j] = 0
        return block

    def get_D_block(index, prefix="D"):
        block = get_full_block(index, prefix)
        for j in range(2, ws):  # 1st row, right part
            block[0, j] = 0
        for i in range(ws - 2):  # column 0
            block[i, 0] = 1
        for i in range(ws - 1):  # column 1
            block[i, 1] = 1
        block[ws - 2, ws - 1] = 1  # last coeff
        return block

    def get_H_block(index, prefix="H"):
        assert index == 0
        block = get_D_block(0)
        for i in range(ws):
            for j in range(ws):
                block[i, j] += 1
        return block

    def get_F_block(index, prefix="F"):
        block = sage.all.zero_matrix(sage.all.SR, ws)
        block[ws-1, 0] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws-1, 0))
        for j in range(ws - 3):
            assert ws >= 4
            for i in range(ws - 2):
                block[ws-1-i, 2+j] = sage.all.var("a" + "{}{}_{}_{}".format(prefix, index, ws-1-i, 2+j))
        return block

    def get_G_block(index, prefix="G"):
        block = get_full_block(index, prefix)
        for j in range(1, ws):  # 1st row
            block[0, j] = 0
        for j in range(1, ws):  # 2nd row
            block[1, j] = 1 if j in [1, 2] else 0
        for i in range(ws - 2):  # first 2 cols
            block[i, 0] = 1
            block[i+1, 1] = 1
        # last 2 rows are 0*01 (after first 2 columns)
        for j in range(2, ws):
            block[ws - 2, j] = 1 if j == ws - 1 else 0
            block[ws - 1, j] = 1 if j == ws - 1 else 0
        return block

    def get_K_block(index, prefix="K"):
        block = get_full_block(index, prefix)
        for j in range(1, ws):  # first row
            block[0, j] = 0
        for i in range(ws - 2):  # first two cols
            block[i, 0] = 1
            block[i+1, 1] = 1
        block[1, ws - 1] = 0
        block[ws - 2, ws - 1] = 1  # last coeff
        return block

    #

    A0, A1, A2, A3 = [get_A_block(i) for i in range(4)]

    C0, C1, = [get_C_block(i) for i in range(2)]
    I0, = [get_I_block(i) for i in range(1)]

    D0, = [get_D_block(i) for i in range(1)]
    H0, = [get_H_block(i) for i in range(1)]

    F0, F1, = [get_F_block(i) for i in range(2)]

    G0, = [get_G_block(i) for i in range(1)]

    K0, = [get_K_block(i) for i in range(1)]

    right_ct = sage.all.zero_matrix(sage.all.SR, nrows=1, ncols=ws * 4)
    for j in range(4 * wordsize):
        right_ct[0, j] = sage.all.var("a" + "{}{}_{}_{}".format("R", 0, 0, j))

    varnames = []
    for matrix in [A0, A1, A2, A3, C0, C1, D0, F0, F1, G0, H0, I0, K0, right_ct]:
        varnames.extend([str(v) for v in matrix.variables() if str(v) not in varnames])

    bpr = BooleanPolynomialRing(names=varnames)

    aux = []
    for matrix in [A0, A1, A2, A3, C0, C1, D0, F0, F1, G0, H0, I0, K0, right_ct]:
        aux.append(sage.all.matrix(bpr, matrix.nrows(), matrix.ncols(),
                                   [bpr(str(x)) for x in matrix.list()]))
    A0, A1, A2, A3, C0, C1, D0, F0, F1, G0, H0, I0, K0, right_ct = aux

    # -----

    class MyOrderedDict(collections.OrderedDict):
        def __setitem__(self, key, value):
            assert key not in self
            return super().__setitem__(key, value)

    bpr_gens_dict = bpr.gens_dict()
    to_sr = lambda x: str2bp(x, bpr_gens_dict)

    replacements = MyOrderedDict()

    # -----

    # # moved A-replacements to the function creating A

    # for j in range(ws - 3):
    #     for i in range(ws - 3):
    #         replacements[to_sr(f"aA0_{1 + i}_{2 + j}")] = int(i == j)
    #         replacements[to_sr(f"aA1_{1 + i}_{2 + j}")] = 0

    # for i in range(0, ws - 4):
    #     for j in range(0, ws - 4):
    for i in range(ws - 3, ws - 4):
        for j in range(ws - 3, ws - 4):
            replacements[to_sr(f"aA2_{1+i}_{2+j}")] = to_sr(f"aA1_{1+i}_{2+j}")

    # for i in range(0, ws - 3):
    #     for j in range(0, ws - 3):
    #         replacements[to_sr(f"aA3_{1+i}_{2+j}")] = to_sr(f"aA0_{1+i}_{2+j}")

    # w=3,4,5
    # aA3_1_0 + aA0_1_0
    #     aA3_2_0 + aA0_2_0
    #         aA3_3_0 + aA0_3_0
    replacements[to_sr(f"aC0_{ws-2}_0")] = to_sr(f"aA3_{ws-2}_0 + aA0_{ws-2}_0")
    # w=3,4,5
    # aA0_2_1 + 1
    #     aA0_3_1 + 1
    #         aA0_4_1 + 1
    replacements[to_sr(f"aC0_{ws-1}_1")] = to_sr(f"aA0_{ws-1}_1 + 1")

    # w=3,4,5
    # aA2_1_0 + aA1_1_0),  # aC1_1_0, aC1_2_0
    #     aA2_2_0 + aA1_2_0
    #         aA3_3_0 + aA0_3_0
    replacements[to_sr(f"aC1_{ws-2}_0")] = to_sr(f"aA2_{ws-2}_0 + aA1_{ws-2}_0")
    # w=3,4,5
    # aC0_2_0 + aA3_2_0 + aA2_2_0 + aA1_2_0 + aA0_2_0),  # aC1_2_0, aC1_3_0
    # aC0_3_0 + aA3_3_0 + aA2_3_0 + aA1_3_0 + aA0_3_0
    # aC0_4_0 + aA3_4_0 + aA2_4_0 + aA1_4_0 + aA0_4_0
    replacements[to_sr(f"aC1_{ws-1}_0")] = to_sr(f"aC0_{ws-1}_0 + aA3_{ws-1}_0 + aA2_{ws-1}_0 + aA1_{ws-1}_0 + aA0_{ws-1}_0")
    # w=3,4,5
    # aA2_2_1,  # aC1_2_1, aC1_3_2
    #     aA2_3_1
    #         aA2_4_1
    replacements[to_sr(f"aC1_{ws-1}_1")] = to_sr(f"aA2_{ws-1}_1")

    if ws >= 4:
        replacements[to_sr(f"aD0_1_{ws-1}")] = 0

    # (aD0_1_0, aA3_1_0 + aA2_1_0 + aA1_1_0 + aA0_1_0 + 1
    # (aD0_2_0, aA3_2_0 + aA2_2_0 + aA1_2_0 + aA0_2_0 + 1
    #           aA3_3_0 + aA2_3_0 + aA1_3_0 + aA0_3_0 + 1
    replacements[to_sr(f"aD0_{ws-2}_0")] = to_sr(f"aA3_{ws-2}_0 + aA2_{ws-2}_0 + aA1_{ws-2}_0 + aA0_{ws-2}_0 + 1")

    # (aD0_2_1, aA2_2_1 + aA0_2_1
    # (aD0_3_1, aA2_3_1 + aA0_3_1
    #           aA2_4_1 + aA0_4_1
    replacements[to_sr(f"aD0_{ws-1}_1")] = to_sr(f"aA2_{ws-1}_1 + aA0_{ws-1}_1")

    for i in range(0, ws - 3):
        replacements[to_sr(f"aD0_{ws-1}_{2+i}")] = \
            to_sr(f"aD0_{ws-2}_{2+i} + aC1_{ws-1}_{2+i} + aC0_{ws-1}_{2+i} + aA3_{ws-1}_{2+i} + aA1_{ws-1}_{2+i}")

    # (aD0_2_2, aC1_2_2 + aC0_2_2 + aA3_2_2 + aA1_2_2 + 1
    # (aD0_3_3, aC1_3_3 + aC0_3_3 + aA3_3_3 + aA1_3_3 + 1
    #           aC1_4_4 + aC0_4_4 + aA3_4_4 + aA1_4_4 + 1
    replacements[to_sr(f"aD0_{ws-1}_{ws-1}")] = to_sr(f"aC1_{ws-1}_{ws-1} + aC0_{ws-1}_{ws-1} + aA3_{ws-1}_{ws-1} + aA1_{ws-1}_{ws-1} + 1")

    # w=3,4,5
    # aD0_2_0 + aC0_2_0 + aA2_2_0 + aA1_2_0 + 1
    #   aD0_3_0 + aC0_3_0 + aA2_3_0 + aA1_3_0 + 1
    #     aD0_4_0 + aC0_4_0 + aA2_4_0 + aA1_4_0 + 1
    replacements[to_sr(f"aF0_{ws-1}_0")] = to_sr(f"aD0_{ws-1}_0 + aC0_{ws-1}_0 + aA2_{ws-1}_0 + aA1_{ws-1}_0 + 1")

    for i in range(0, ws - 3):
        replacements[to_sr(f"aF0_{ws-1}_{2+i}")] = to_sr(f"aF0_{ws-2}_{2+i}")

    # w=3,4,5
    # aC0_2_0 + aA3_2_0 + aA0_2_0
    #   aC0_3_0 + aA3_3_0 + aA0_3_0
    #     aC0_4_0 + aA3_4_0 + aA0_4_0
    replacements[to_sr(f"aF1_{ws-1}_0")] = to_sr(f"aC0_{ws-1}_0 + aA3_{ws-1}_0 + aA0_{ws-1}_0")

    if ws >= 5:
        for i in range(0, ws - 3):
            replacements[to_sr(f"aF1_{ws-2}_{2+i}")] = to_sr(f"aD0_{ws-2}_{2+i}")
            replacements[to_sr(f"aF1_{ws-1}_{2+i}")] = to_sr(f"aD0_{ws-1}_{2+i}")

    # (aG0_1_0, aA3_1_0 + aA1_1_0 + 1),
    # (aG0_2_0, aA3_2_0 + aA1_2_0 + 1
    #           aA3_3_0 + aA1_3_0 + 1
    replacements[to_sr(f"aG0_{ws-2}_{0}")] = to_sr(f"aA3_{ws-2}_0 + aA1_{ws-2}_0 + 1")
    # (aG0_2_0, aD0_2_0 + aC0_2_0 + aA3_2_0 + aA2_2_0),
    # (aG0_3_0, aD0_3_0 + aC0_3_0 + aA3_3_0 + aA2_3_0
    #           aD0_4_0 + aC0_4_0 + aA3_4_0 + aA2_4_0
    replacements[to_sr(f"aG0_{ws-1}_{0}")] = to_sr(f"aD0_{ws-1}_0 + aC0_{ws-1}_0 + aA3_{ws-1}_0 + aA2_{ws-1}_0")
    # (aG0_2_1, 0),
    # (aG0_3_1, 0)
    #           0
    replacements[to_sr(f"aG0_{ws-1}_{1}")] = 0

    # (aK0_1_0, aA1_1_0 + aA0_1_0 + 1),
    # (aK0_2_0, aA1_2_0 + aA0_2_0 + 1
    # (aK0_3_0, aA1_3_0 + aA0_3_0 + 1
    replacements[to_sr(f"aK0_{ws-2}_{0}")] = to_sr(f"aA1_{ws-2}_0 + aA0_{ws-2}_0 + 1")
    # (aK0_2_0, aD0_2_0 + aA3_2_0 + aA2_2_0),
    # (aK0_3_0, aD0_3_0 + aA3_3_0 + aA2_3_0
    # (aK0_4_0, aD0_4_0 + aA3_4_0 + aA2_4_0
    replacements[to_sr(f"aK0_{ws-1}_{0}")] = to_sr(f"aD0_{ws-1}_0 + aA3_{ws-1}_0 + aA2_{ws-1}_0")
    # (aK0_2_1, aA0_2_1 + 1),
    # (aK0_3_1, aA0_3_1 + 1
    # (aK0_4_1, aA0_4_1 + 1
    replacements[to_sr(f"aK0_{ws-1}_{1}")] = to_sr(f"aA0_{ws-1}_1 + 1")
    # (aK0_2_2, aC0_2_2 + aA1_2_2 + 1)
    # (aK0_3_3, aC0_3_3 + aA1_3_3 + 1
    # (aK0_4_4, aC0_4_4 + aA1_4_4 + 1
    replacements[to_sr(f"aK0_{ws-1}_{ws-1}")] = to_sr(f"aC0_{ws-1}_{ws-1} + aA1_{ws-1}_{ws-1} + 1")

    # reorder
    if ws >= 5:
        try:
            replacements[to_sr(f"aK0_1_2")] = to_sr(f"aA1_1_2 + 1")
        except NameError:
            replacements[to_sr(f"aK0_1_2")] = 0 + 1

    a0_ones = []
    for i in range(ws-3):
        for j in range(ws-3):
            if i == j:
                a0_ones.append(f"aA0_{1+i}_{2+j}")

    for i in range(0, ws - 4):
        for j in range(0, ws - 3):
            try:
                replacements[to_sr(f"aK0_{2+i}_{2+j}")] = to_sr(f"aD0_{2+i}_{2+j} + aA0_{2+i}_{2+j}")
            except NameError:
                aux = 1 if f"aA0_{2+i}_{2+j}" in a0_ones else 0
                replacements[to_sr(f"aK0_{2+i}_{2+j}")] = to_sr(f"aD0_{2+i}_{2+j} + {aux}")
    for i in range(0, ws - 3):
        replacements[to_sr(f"aK0_{ws-2}_{2+i}")] = to_sr(f"aD0_{ws-2}_{2+i}")
    for i in range(0, ws - 3):
        replacements[to_sr(f"aK0_{ws-1}_{2+i}")] = to_sr(f"aD0_{ws-2}_{2+i} + aC0_{ws-1}_{2+i} + aA1_{ws-1}_{2+i}")

    #

    replacements[to_sr(f"aR0_0_{0}")] = 0
    replacements[to_sr(f"aR0_0_{ws}")] = 0
    replacements[to_sr(f"aR0_0_{2*ws}")] = 0
    replacements[to_sr(f"aR0_0_{2*ws + 1}")] = 0
    for i in range(ws):
        replacements[to_sr(f"aR0_0_{3*ws + i}")] = 0

    # -----

    A0 = A0.subs(replacements)
    A1 = A1.subs(replacements)
    A2 = A2.subs(replacements)
    A3 = A3.subs(replacements)
    C0 = C0.subs(replacements)
    C1 = C1.subs(replacements)
    D0 = D0.subs(replacements)
    F0 = F0.subs(replacements)
    F1 = F1.subs(replacements)
    G0 = G0.subs(replacements)
    H0 = H0.subs(replacements)
    I0 = I0.subs(replacements)
    K0 = K0.subs(replacements)
    right_ct = right_ct.subs(replacements)

    # ----

    zz = sage.all.zero_matrix(bpr, ws, ws)

    # Z0, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, ZA, ZB, ZC, ZD = [get_full_block(i, i) for i in range(14)]

    # A0 A1 C0 D0| *
    # A2 A3 C1 D0| *
    # F0 F1 G0 H0| *
    # 0  0  I0 K0 | 0

    right_matrix = sage.all.block_matrix(bpr, [
        [A0, A1, C0, D0],
        [A2, A3, C1, D0],
        [F0, F1, G0, H0],
        [zz, zz, I0, K0], ])

    if verbose:
        smart_print("matrix shape:")
        smart_print(right_matrix)
        smart_print("ct shape:")
        smart_print(right_ct, "\n")

    #

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

    varnames = [vn for vn in varnames if vn in set_final_varnames]

    inv_equations = []

    return var2val, inv_equations, varnames


def graph_cczse_coeffs2modadd_cczse_anf(coeff2expr, wordsize, verbose, debug, filename):
    """Given the symbolic coefficients of the CCZ-SE of the "q" quadratic CCZ,
    return the symbolic anf CCZ-SE of the permuted modular addition.
    """
    verbose = verbose or debug

    ws = wordsize
    ccz_anf_name = "q"
    permuted = 2

    if filename is True:
        now = datetime.datetime.now()
        now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
        filename = f"result-graph_cczse_coeffs2modadd_cczse_anf-w{ws}-{now}.txt"

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

    return l_c_linv


def find_cczse_pmodadd_3passes(wordsize, check_se, threads, verbose, debug, filename):
    """Find CCZ-SE of the permuted modular addition for a fixed wordsize"""
    assert 3 <= wordsize <= 8

    verbose = verbose or debug

    ws = wordsize
    ccz_anf_name = "q"  # "H"
    permuted = 2  # 1

    if filename is True:
        now = datetime.datetime.now()
        now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
        filename = f"result-find_cczse_pmodadd_3passes-w{ws}-{now}.txt"

    num_input_anf_vars = 2*ws
    if ws <= 6:
        modadd_anf = get_modadd_anf(ws, permuted=permuted)
    else:
        modadd_anf = None

    prefix_se_coeffs = "a"

    deg = 1
    ct_terms = True
    return_ccz_se = True

    invertibility = True
    ignore_determinant_equation = True  # det eq not easy to reduce and no redundant eq can be found
    add_allones_equations = "fix"

    #

    prefix_get_symbolic_anf = "b"  # coeffs starting with this prefix only used for next get_symbolic_anf()
    assert prefix_se_coeffs[0] != prefix_get_symbolic_anf[0]
    shape_fixed_vars, initial_equations, shape_varnames = shape(ws, prefix_get_symbolic_anf, verbose, filename)

    x_varnames = ["x" + str(i) for i in range(4 * ws)]
    # # shape_fixed_vars contains assignments B0* <- A0*
    # # however, default assignments is A0* <- B0* if bpr order is A0 > B0 > ...
    # # (default is left vars are replaced by right vars)
    # # thus, coeffs are reversed to preserve shape_fixed_vars order
    coeff_varnames = list(reversed(shape_varnames))
    bpr = BooleanPolynomialRing(names=x_varnames + coeff_varnames)
    bpr_gens_dict = bpr.gens_dict()

    # # enable to ignore shape
    # prefix_get_symbolic_anf = "a"
    # shape_fixed_vars = {}
    # initial_equations = []
    # varnames = get_symbolic_anf(1, 4 * ws, 4 * ws, ct_terms=True, prefix_inputs="x", prefix_coeffs="a", return_varnames=True)
    # bpr = BooleanPolynomialRing(names=varnames)
    # bpr_gens_dict = bpr.gens_dict()

    ccz_se_anf = get_symbolic_anf(1, 4 * ws, 4 * ws, ct_terms=True, prefix_inputs="x",
                                  prefix_coeffs=prefix_get_symbolic_anf,
                                  coeff2expr=shape_fixed_vars, bpr=bpr)

    input_ccz_anf_vars = [str2bp(vn, bpr_gens_dict) for vn in x_varnames[:2 * ws]]
    ccz_modadd_anf = get_ccz_modadd_anf(ws, name=ccz_anf_name, permuted=permuted,
                                        bpr=bpr, input_vars=input_ccz_anf_vars)
    admissible_mapping = get_admissible_mapping(ws, name=ccz_anf_name, permuted=permuted)

    # fast conversion with str2bp
    # (the conversion when calling bpr() uses slow and memory-limited Singular)
    initial_equations = [str2bp(eq, bpr_gens_dict) for eq in initial_equations]
    initial_fixed_vars = collections.OrderedDict(
        (str2bp(k, bpr_gens_dict), bpr(v) if v in [0, 1] else str2bp(v, bpr_gens_dict))
        for k, v in shape_fixed_vars.items() if not k.startswith(prefix_get_symbolic_anf))

    #

    # 1st pass - find linear fixed vars from raw equations

    smart_print = get_smart_print(filename)
    smart_print(f"initial_fixed_vars: {initial_fixed_vars}")
    smart_print(f"initial_equations: {initial_equations}\n")

    smart_print(f"{get_time()} | 1st pass - finding raw equations")
    solve_args = {
        "reduction_mode": None,
        "only_linear_fixed_vars": True,
        "return_mode": "raw_equations",
        "initial_fixed_vars": initial_fixed_vars,
        "initial_equations": initial_equations,
        "ignore_initial_parsing": False,  # 1st parsing is done
        "check_find_fixed_vars": True,  # 1st check is True
    }
    raw_equations = find_self_equivalence_quasilinear_implicit_pmodadd(
        ccz_modadd_anf, admissible_mapping,
        # degree args
        left_se_degree=deg, inv_right_se_degree=deg,
        inv_left_se_degree=deg, right_se_degree=deg,
        se_ct_terms=ct_terms,
        # optimization constraints
        add_allones_equations=add_allones_equations,
        add_invertibility_equations=invertibility,
        ignore_determinant_equation=ignore_determinant_equation,
        check_se=check_se,
        bpr=bpr,
        # optional input args
        ccz_se_anf=ccz_se_anf,
        prefix_se_coeffs=prefix_se_coeffs,
        input_ccz_anf_vars=input_ccz_anf_vars,
        anf=modadd_anf, num_input_anf_vars=num_input_anf_vars,
        # optional output args
        return_ccz_se=return_ccz_se,
        # printing args
        verbose=False, debug=False, filename=filename,
        # extra args passed to solve_functional_equation()
        threads=threads,
        **solve_args
    )

    smart_print(f"\n{get_time()} | finding linear fixed variables from raw equations")

    initial_fixed_vars, _ = find_fixed_vars(
        raw_equations, only_linear=True,
        initial_r_mode="gauss", repeat_with_r_mode="gauss",
        initial_fixed_vars=initial_fixed_vars,
        bpr=bpr, check=True,  # check=True in slow
        verbose=verbose, debug=debug, filename=filename)

    # 2nd pass - find redundant equations

    smart_print(f"\n{get_time()} | 2nd pass - finding redundant equations")

    num_sat_solutions = 512
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
        "check_find_fixed_vars": False,
    }
    redundant_equations = find_self_equivalence_quasilinear_implicit_pmodadd(
        ccz_modadd_anf, admissible_mapping,
        # degree args
        left_se_degree=deg, inv_right_se_degree=deg,
        inv_left_se_degree=deg, right_se_degree=deg,
        se_ct_terms=ct_terms,
        # optimization constraints
        add_allones_equations=add_allones_equations,
        add_invertibility_equations=invertibility,
        ignore_determinant_equation=ignore_determinant_equation,
        check_se=check_se,
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

    smart_print(f"\nredundant equations found ({len(redundant_equations)}): "
                f"{[str(x) for x in redundant_equations]}")

    if len(redundant_equations) == 0:
        warnings.warn("no redundant equations found")

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
        redundant_equations = find_self_equivalence_quasilinear_implicit_pmodadd(
            ccz_modadd_anf, admissible_mapping,
            # degree args
            left_se_degree=deg, inv_right_se_degree=deg,
            inv_left_se_degree=deg, right_se_degree=deg,
            se_ct_terms=ct_terms,
            # optimization constraints
            add_allones_equations=add_allones_equations,
            add_invertibility_equations=invertibility,
            ignore_determinant_equation=ignore_determinant_equation,
            check_se=check_se,
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

        smart_print(f"\nvalid redundant equations found ({len(redundant_equations)}): "
                    f"{[str(x) for x in redundant_equations]}")

    # 3rd pass - find symbolic coeffs

    smart_print(f"\n{get_time()} | 3rd pass - solving final system")

    if ws >= 6 and ignore_determinant_equation is False:
        num_sat_solutions = 1
        find_linear_combinations_in_solutions = False
    else:
        num_sat_solutions = sage.all.infinity
        find_linear_combinations_in_solutions = True

    solve_args = {
        "reduction_mode": "gauss",
        "only_linear_fixed_vars": False,
        "num_sat_solutions": num_sat_solutions,
        "return_mode": "symbolic_coeffs",
        "initial_fixed_vars": initial_fixed_vars,
        "initial_equations": redundant_equations,
        "find_linear_combinations_in_solutions": find_linear_combinations_in_solutions,
        "num_sols_per_base_sol_to_check": 0,
        "return_total_num_solutions": True,
        "ignore_initial_parsing": True,
        "check_find_fixed_vars": False,
    }
    symbolic_coeffs, equations, num_total_solutions = find_self_equivalence_quasilinear_implicit_pmodadd(
        ccz_modadd_anf, admissible_mapping,
        # degree args
        left_se_degree=deg, inv_right_se_degree=deg,
        inv_left_se_degree=deg, right_se_degree=deg,
        se_ct_terms=ct_terms,
        # optimization constraints
        add_allones_equations=add_allones_equations,
        add_invertibility_equations=invertibility,
        ignore_determinant_equation=ignore_determinant_equation,
        check_se=check_se,
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

    smart_print("\nnum_total_solutions:", num_total_solutions,
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
                value = bpr(bpr(value).subs(symbolic_coeffs))
                for v in value.variables():
                    var2found[str(v)] = True
                value = str(value)
        str_symbolic_coeffs.append((var, value))

    smart_print(f"graph_se_coeffs = {str_symbolic_coeffs}\n")

    assert set(var2found.values()) == {True}, f"{var2found}"

    # base_coeff2ct_str = {str(k): str(v) for k, v in base_initial_fixed_vars.items()}
    # new_symbolic_coeffs = []
    # for k, v in symbolic_coeffs.items():
    #     if str(k).startswith("aa") or str(k).startswith("ab") or str(k).startswith("ac"):
    #         continue
    #     if "*" in str(v):
    #         continue
    #     if str(v) != base_coeff2ct_str.get(str(k), None):
    #         new_symbolic_coeffs.append((k, v))
    # smart_print(f"new_symbolic_coeffs = {sorted(new_symbolic_coeffs)}\n")
    # print_new_symbolic_coeffs(base_coeff2ct_str, symbolic_coeffs, filename)

    return str_symbolic_coeffs, equations, num_total_solutions


def find_cczse_pmodadd_with_shape(wordsize, check_se, threads, save_coeffs_eqs, verbose, debug, filename):
    """Find CCZ-SE of the permuted modular addition for a fixed wordsize"""
    assert wordsize >= 3, "only supported for wordsize >= 3"

    verbose = verbose or debug

    ws = wordsize
    ccz_anf_name = "q"
    permuted = 2

    if filename is True:
        now = datetime.datetime.now()
        now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
        filename = f"result-find_cczse_pmodadd_with_shape-w{ws}-{now}.txt"

    num_input_anf_vars = 2*ws
    if ws <= 6:
        modadd_anf = get_modadd_anf(ws, permuted=permuted)
    else:
        modadd_anf = None

    prefix_se_coeffs = "a"

    deg = 1
    ct_terms = True
    return_ccz_se = True

    invertibility = True
    ignore_determinant_equation = True  # det eq not easy to reduce
    add_allones_equations = "fix"

    #

    prefix_get_symbolic_anf = "b"  # coeffs starting with this prefix only used for next get_symbolic_anf()
    assert prefix_se_coeffs[0] != prefix_get_symbolic_anf[0]
    shape_fixed_vars, initial_equations, shape_varnames = shape(ws, prefix_get_symbolic_anf, verbose, filename)

    x_varnames = ["x" + str(i) for i in range(4 * ws)]
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

    input_ccz_anf_vars = [str2bp(vn, bpr_gens_dict) for vn in x_varnames[:2 * ws]]
    ccz_modadd_anf = get_ccz_modadd_anf(ws, name=ccz_anf_name, permuted=permuted,
                                        bpr=bpr, input_vars=input_ccz_anf_vars)
    admissible_mapping = get_admissible_mapping(ws, name=ccz_anf_name, permuted=permuted)

    # fast conversion with str2bp
    # (the conversion when calling bpr() uses slow and memory-limited Singular)
    initial_equations = [str2bp(eq, bpr_gens_dict) for eq in initial_equations]
    fixed_vars = collections.OrderedDict(
        (str2bp(k, bpr_gens_dict), bpr(v) if v in [0, 1] else str2bp(v, bpr_gens_dict))
        for k, v in shape_fixed_vars.items() if not k.startswith(prefix_get_symbolic_anf))

    if ws >= 6 and ignore_determinant_equation is False:
        num_sat_solutions = 1
        find_linear_combinations_in_solutions = False
    else:
        num_sat_solutions = sage.all.infinity
        find_linear_combinations_in_solutions = True
    solve_args = {
        "reduction_mode": "gauss",
        "only_linear_fixed_vars": False,
        "num_sat_solutions": num_sat_solutions,
        "return_mode": "symbolic_coeffs",
        "initial_fixed_vars": fixed_vars,
        "initial_equations": initial_equations,
        "find_linear_combinations_in_solutions": find_linear_combinations_in_solutions,
        "num_sols_per_base_sol_to_check": 0,
        "return_total_num_solutions": True,
        "ignore_initial_parsing": True,
        "check_find_fixed_vars": False,
    }

    symbolic_coeffs, equations, num_total_solutions = find_self_equivalence_quasilinear_implicit_pmodadd(
        ccz_modadd_anf, admissible_mapping,
        # degree args
        left_se_degree=deg, inv_right_se_degree=deg,
        inv_left_se_degree=deg, right_se_degree=deg,
        se_ct_terms=ct_terms,
        # optimization constraints
        add_allones_equations=add_allones_equations,
        add_invertibility_equations=invertibility,
        ignore_determinant_equation=ignore_determinant_equation,
        check_se=check_se,
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

    smart_print("\nnum_total_solutions:", num_total_solutions,
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
                value = bpr(bpr(value).subs(symbolic_coeffs))
                for v in value.variables():
                    var2found[str(v)] = True
                value = str(value)
        str_symbolic_coeffs.append((var, value))

    smart_print(f"graph_se_coeffs = {str_symbolic_coeffs}\n")

    assert set(var2found.values()) == {True}, f"{var2found}"

    if save_coeffs_eqs:
        filename_sobj = f"stored_cczse_pmodadd_w{ws}.sobj"
        str_equations = tuple([str(eq) for eq in equations])
        sage.all.save((str_symbolic_coeffs, str_equations), filename_sobj, compress=True)

    # base_coeff2ct_str = {str(k): str(v) for k, v in initial_fixed_vars.items()}
    # new_symbolic_coeffs = []
    # for k, v in symbolic_coeffs.items():
    #     if str(k).startswith("aa") or str(k).startswith("ab") or str(k).startswith("ac"):
    #         continue
    #     if "*" in str(v):
    #         continue
    #     if str(v) != base_coeff2ct_str.get(str(k), None):
    #         new_symbolic_coeffs.append((k, v))
    # smart_print(f"new_symbolic_coeffs = {sorted(new_symbolic_coeffs)}\n")
    # print_new_symbolic_coeffs(base_coeff2ct_str, symbolic_coeffs, filename)

    # TODO: deprecated (code used to found A0/A1 inner square can be Id and 0 blocks)
    # if ws >= 5:
    #     equations = list(equations)
    #     first_bad_equation = -1
    #     for index_eq, eq in enumerate(equations):
    #         if eq.constant_coefficient() == 0:
    #             first_bad_equation = index_eq
    #             break
    #     smart_print("first_bad_equation:", first_bad_equation)
    #     equations = equations[first_bad_equation:]
    #     counter_variables = collections.Counter()
    #     for eq in equations:
    #         for term in eq:
    #             if term.degree() != 2:
    #                 continue
    #             for var in term.variables():
    #                 counter_variables[var] += 1
    #     smart_print(f"counter_variables:\n{counter_variables}")

    return str_symbolic_coeffs, equations, num_total_solutions


def print_new_symbolic_coeffs(base_coeff2ct_str, all_coeff2expr, filename):
    new_coeff2ct = []
    # only [0,1] or linear v
    all_coeff2expr = [(str(k), str(v)) for k, v in all_coeff2expr.items() if "*" not in str(v) and str(k)[1].isupper()]
    all_coeff2expr = sorted(all_coeff2expr, key=lambda x: [x[0].split("_")[0]] + [int(x_i) for x_i in x[0].split("_")[1:]])
    for k, v in all_coeff2expr:
        if v != base_coeff2ct_str.get(k, None):
            new_coeff2ct.append((k, v))

    smart_print = get_smart_print(filename)
    if len(new_coeff2ct) != 0:
        last_k = new_coeff2ct[0][0]
        for k_v in itertools.chain(new_coeff2ct):
            k, v = k_v
            last_j0, last_j1 = [int(x_i) for x_i in last_k.split("_")[1:]]
            new_j0, new_j1 = [int(x_i) for x_i in k.split("_")[1:]]
            if last_k[:4] != k[:4] or abs(new_j0 - last_j0) > 1 or abs(new_j1 - last_j1) > 1:
                smart_print("")
            smart_print(f"({k}, {v}), ", end="")
            last_k = k
        smart_print("\n")


if __name__ == '__main__':
    raise ValueError("latest changes not tested")

    sys.setrecursionlimit(sys.getrecursionlimit()*1000)

    wordsize = 3
    check_se = False
    threads = 4

    save = False
    verbose = True
    debug = False
    filename = None

    find_cczse_pmodadd_with_shape(wordsize, check_se, threads, save, verbose, debug, filename)

    # find_cczse_pmodadd_3passes(wordsize, check_se, threads, verbose, debug, filename)

    # check_partial_fixed_implicit_is_a_permutation(3, True)

    # # - save coeffs and eqs of CCZ-SE (implicit) for multiple wordsize
    # threads = 4
    # save = True
    # verbose = False
    # debug = False
    # check = False
    # filename = False
    # for wordsize in [16, 24, 32, 48, 64]:
    #     find_cczse_pmodadd_with_shape(wordsize, check, threads, save, verbose, debug, filename)

    # # - load coeffs and eqs of CCZ-SE (implicit)
    # verbose = True
    # debug = False
    # filename = None
    # for wordsize in [16, 24, 32, 48, 64]:
    #     filename_sobj = f"stored_cczse_pmodadd_w{wordsize}.sobj"
    #     coeff2expr, equations = sage.all.load(filename_sobj, compress=True)
    #     l_c_linv = graph_cczse_coeffs2modadd_cczse_anf(coeff2expr, wordsize, verbose, debug, filename)
    #     print(equations)
    #     print(l_c_linv[0])
    #     print("...")
    #     print(l_c_linv[-1], "\n")