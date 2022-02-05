"""Implicit implementation with affine encodings."""
import collections
import functools
import itertools
import math
import os
import warnings
from functools import partial

import sage.all
from sage.sat.boolean_polynomials import solve as solve_sat

from boolcrypt.utilities import (
    substitute_variables, BooleanPolynomialRing,
    int2vector, vector2int, get_anf_coeffmatrix_str,
    compose_affine, matrix2anf, compose_anf_fast, anf2matrix,
    get_time, get_smart_print, get_all_symbolic_coeff
)

from boolcrypt.functionalequations import find_fixed_vars

from boolcrypt.modularaddition import get_implicit_modadd_anf

from boolcrypt.se_pmodadd.find_implicit import graph_cczse_coeffs2modadd_cczse_anf

# TODO: (adrian) finish get_graph_automorphisms
# TODO: (adrian) implement USE_REDUNDANT_PERTURBATIONS and search for exceptions
# TODO: (adrian) add definition of USE_REDUNDANT_PERTURBATIONS
# TODO: (adrian) add definitions of TRIVIAL_*

# TODO: seed should be a parameter
SEED = abs(hash("eurocrypt2021"))
sage.all.set_random_seed(SEED)

# TODO: USE_REDUNDANT_PERTURBATIONS should be a parameter (but current code doesn't support USE_REDUNDANT_PERTURBATIONS=False)
USE_REDUNDANT_PERTURBATIONS = True

# TODO: TRIVIAL_* should be parameters
TRIVIAL_EE = False
TRIVIAL_GA = False  # True, "repeat", or False  # needed for TRIVIAL_QSE
TRIVIAL_RP = False
TRIVIAL_AP = False

if USE_REDUNDANT_PERTURBATIONS is False:
    assert TRIVIAL_RP is None

# TODO: PRINT_* should be parameters
PRINT_TIME_GENERATION = True
PRINT_DEBUG_GENERATION = True
PRINT_INTERMEDIATE_VALUES = True
PRINT_DEBUG_INTERMEDIATE_VALUES = True

_DEBUG_SPLIT_RP = False  # split the redundant perturbations, only for debugging

AffineEncoding = collections.namedtuple('AffineEncoding', ['matrix', 'cta', 'bitsize', 'inverse'])


def get_random_affine_permutations(bitsize, number_of_permutations, bpr=None):
    vs = sage.all.VectorSpace(sage.all.GF(2), bitsize)

    if bpr is None:
        bpr = sage.all.GF(2)

    def _get_affine_encoding():
        if not TRIVIAL_AP:
            # while loop faster than sage.all.random_matrix(..., algorithm="unimodular")
            while True:
                matrix = sage.all.matrix(bpr, bitsize, entries=[vs.random_element() for _ in range(bitsize)])
                if matrix.is_invertible():
                    break
            cta = sage.all.vector(bpr, list(vs.random_element()))
            # matrix = sage.all.random_matrix(sage.all.GF(2), nrows=bitsize, ncols=bitsize, algorithm="unimodular")
            # cta = sage.all.random_vector(sage.all.GF(2), bitsize)
        else:
            matrix = sage.all.identity_matrix(bpr, bitsize)
            cta = sage.all.vector(bpr, [0 for _ in range(bitsize)])

        # inverse_matrix = matrix.inverse()
        # inverse_affine_encoding = AffineEncoding(
        #     inverse_matrix,
        #     inverse_matrix * cta,
        #     bitsize,
        #     inverse=None
        # )
        affine_encoding = AffineEncoding(
            matrix,
            cta,
            bitsize,
            inverse=None,  # inverse_affine_encoding
        )
        return affine_encoding

    affine_encodings = []
    for _ in range(number_of_permutations):
        affine_encodings.append(_get_affine_encoding())

    return affine_encodings


def get_implicit_round_encodings(wordsize, rounds, bpr_pmodadd=None):
    ws = wordsize

    bpr = sage.all.GF(2)
    identity_matrix = partial(sage.all.identity_matrix, bpr)
    zero_matrix = partial(sage.all.zero_matrix, bpr)

    if bpr_pmodadd is None:
        names = ["x" + str(i) for i in range(ws)]
        names += ["y" + str(i) for i in range(ws)]
        names += ["z" + str(i) for i in range(ws)]
        names += ["t" + str(i) for i in range(ws)]
        bpr_pmodadd = BooleanPolynomialRing(names=names, order="deglex")

    # bpr_ext = BooleanPolynomialRing(names=bpr_pmodadd.variable_names()[:2*ws], order="deglex")
    # identity_anf = bpr_pmodadd.gens()

    implicit_round_encodings = [None for _ in range(rounds - 1)]

    affine_encodings = get_random_affine_permutations(2 * ws, rounds - 2)

    for i in range(rounds - 1):
        if i == 0:
            if TRIVIAL_EE:
                input_ee_matrix = identity_matrix(2*ws)
                input_ee_cta = [0 for _ in range(2*ws)]
            else:
                input_ee = get_random_affine_permutations(2 * ws, 1)[0]
                input_ee_matrix = input_ee.matrix
                input_ee_cta = list(input_ee.cta)
            matrix = sage.all.block_matrix(bpr, 2, 2, [
                [input_ee_matrix, zero_matrix(2*ws, 2*ws)],
                [zero_matrix(2*ws, 2*ws), affine_encodings[i].matrix]])
            cta = input_ee_cta + list(affine_encodings[i].cta)
            implicit_round_encodings[i] = matrix2anf(matrix, bool_poly_ring=bpr_pmodadd, bin_vector=cta)
        elif 1 <= i < rounds - 2:
            matrix = sage.all.block_matrix(bpr, 2, 2, [
                [affine_encodings[i-1].matrix, zero_matrix(2*ws, 2*ws)],
                [zero_matrix(2*ws, 2*ws), affine_encodings[i].matrix]])
            cta = list(affine_encodings[i-1].cta) + list(affine_encodings[i].cta)
            implicit_round_encodings[i] = matrix2anf(matrix, bool_poly_ring=bpr_pmodadd, bin_vector=cta)
        else:
            assert i == rounds - 2
            if TRIVIAL_EE:
                output_ee_matrix = identity_matrix(2*ws)
                output_ee_cta = [0 for _ in range(2*ws)]
            else:
                output_ee = get_random_affine_permutations(2 * ws, 1)[0]
                output_ee_matrix = output_ee.matrix
                output_ee_cta = list(output_ee.cta)
            matrix = sage.all.block_matrix(bpr, 2, 2, [
                [affine_encodings[i-1].matrix, zero_matrix(2*ws, 2*ws)],
                [zero_matrix(2*ws, 2*ws), output_ee_matrix]])
            cta = list(affine_encodings[i-1].cta) + output_ee_cta
            implicit_round_encodings[i] = matrix2anf(matrix, bool_poly_ring=bpr_pmodadd, bin_vector=cta)

    if TRIVIAL_EE is True:
        def explicit_extin_function(v):
            return v

        def explicit_extout_function(v):
            return v
    else:
        aux_matrix = input_ee.matrix.inverse()
        def explicit_extin_function(v):
            v = sage.all.vector(v[0].parent(), v)
            return (aux_matrix * v) + (aux_matrix * input_ee.cta)

        def explicit_extout_function(v):
            v = sage.all.vector(v[0].parent(), v)
            return (output_ee.matrix * v) + output_ee.cta

    return implicit_round_encodings, explicit_extin_function, explicit_extout_function


def get_graph_automorphisms(wordsize, rounds, filename):
    ws = wordsize

    smart_print = get_smart_print(filename)

    if TRIVIAL_GA is True:
        names = ["x" + str(i) for i in range(ws)] + ["y" + str(i) for i in range(ws)]
        names += ["z" + str(i) for i in range(ws)] + ["t" + str(i) for i in range(ws)]
        bpr = BooleanPolynomialRing(names=names, order="deglex")
        identity_matrix = partial(sage.all.identity_matrix, bpr)

        list_graph_automorphisms = []
        for i in range(rounds - 1):
            list_graph_automorphisms.append(matrix2anf(identity_matrix(4*ws), bool_poly_ring=bpr))

        return list_graph_automorphisms

    from boolcrypt.functionalequations import solve_functional_equation
    from boolcrypt.utilities import get_symbolic_anf

    try:
        filename_sobj = f"data/stored_cczse_pmodadd_w{wordsize}.sobj"
        coeff2expr, equations = sage.all.load(filename_sobj, compress=True)
    except FileNotFoundError:
        filename_sobj = f"whiteboxarx/data/stored_cczse_pmodadd_w{wordsize}.sobj"
        coeff2expr, equations = sage.all.load(filename_sobj, compress=True)
    l_c_linv = graph_cczse_coeffs2modadd_cczse_anf(coeff2expr, ws, verbose=False, debug=False, filename=None)

    names_x = ["x" + str(i) for i in range(ws)]
    names_yzy = ["y" + str(i) for i in range(ws)] + ["z" + str(i) for i in range(ws)] + ["t" + str(i) for i in range(ws)]
    all_names = names_x + names_yzy + list(l_c_linv[0].parent().variable_names()[4*ws:])
    bpr = BooleanPolynomialRing(names=all_names, order="deglex")
    bpr_simple = BooleanPolynomialRing(names=names_x + names_yzy, order="deglex")

    intermediate_bpr = BooleanPolynomialRing(names=all_names + ["x" + str(i) for i in range(ws, 4*ws)], order="deglex")
    repr_to_bpr = {"x" + str(ws + i): intermediate_bpr(v_i) for i, v_i in enumerate(names_yzy)}

    l_c_linv = [bpr(intermediate_bpr(f).subs(repr_to_bpr)) for f in l_c_linv]
    equations = [bpr(intermediate_bpr(eq).subs(repr_to_bpr)) for eq in equations]  # eq is str

    ordered_replacement = []
    variable_names = bpr.variable_names()
    strvar2index = lambda x: variable_names.index(x)
    for i in range(len(variable_names)):
        if i < 4*ws:
            ordered_replacement.append(bpr.gens()[i])
        else:
            ordered_replacement.append(None)

    list_extra_var2val = solve_sat(equations, n=sage.all.infinity)
    if not list_extra_var2val:
        raise ValueError(f'equations from "stored_cczse_pmodadd_w{wordsize}" are inconsistent (unsatisfiable)')
    if PRINT_DEBUG_GENERATION:
        smart_print(f"get_graph_automorphims | found {len(list_extra_var2val)} extra_var2val-solutions for ws {wordsize}")

    list_graph_automorphisms = []

    implicit_pmodadd = [bpr_simple(str(f)) for f in get_implicit_modadd_anf(ws, permuted=True, only_x_names=False)]

    if wordsize <= 4:
        from boolcrypt.modularaddition import get_modadd_anf
        from boolcrypt.equivalence import check_ccz_equivalence_anf
        modadd_anf = get_modadd_anf(ws, permuted=True)

    # TODO: (adrian) choose final max_tries_per_index in get_graph_automorphisms
    max_tries_per_index = 6
    bad_indices = []
    while True:
        # not enough GA
        if len(list_extra_var2val) >= len(bad_indices):  bad_indices = []
        random_index = sage.all.ZZ.random_element(0, len(list_extra_var2val))
        if random_index in bad_indices:
            continue

        ordered_replacement_copy = ordered_replacement[:]
        for k, v in list_extra_var2val[random_index].items():
            ordered_replacement_copy[strvar2index(str(k))] = bpr(str(v))

        ordered_replacement_copy_copy = ordered_replacement_copy[:]

        for _ in range(max_tries_per_index):
            for j in range(4*ws, len(variable_names)):
                if ordered_replacement_copy_copy[j] is None:
                    ordered_replacement_copy_copy[j] = bpr(sage.all.GF(2).random_element())

            l_c_linv_i = [bpr_simple(str(substitute_variables(bpr, ordered_replacement_copy_copy, f))) for f in l_c_linv]
            l_c_linv_i_matrix = anf2matrix(l_c_linv_i, bpr_simple.gens())

            if PRINT_DEBUG_GENERATION: smart_print(".", end="")

            if l_c_linv_i_matrix.is_invertible():
                if PRINT_DEBUG_GENERATION: smart_print(":", end="")

                # only 1 way to check a GA is not a right SE of T: symbolically T = B (T l_c_linv_i)
                # (check_self_ae_anf not possible since we cannot get implicit_pmodadd_inv)
                symbolic_anf = get_symbolic_anf(1, len(implicit_pmodadd), len(implicit_pmodadd), ct_terms=True, prefix_inputs="x")
                try:
                    solutions = solve_functional_equation(
                        lhs_anfs=[l_c_linv_i, implicit_pmodadd, symbolic_anf],
                        rhs_anfs=[implicit_pmodadd],
                        lhs_input_vars=[bpr_simple.gens(), bpr_simple.gens(), ["x" + str(i) for i in range(len(implicit_pmodadd))]],
                        rhs_input_vars=[bpr_simple.gens()],
                        num_sat_solutions=1,
                        return_mode="list_coeffs",
                        only_linear_fixed_vars=True,
                        verbose=False, debug=False, filename=None
                        # print_common_nonlinear_vars=False,
                    )
                except ValueError as e:
                    assert str(e).startswith("found invalid equation")
                    to_break = True
                else:
                    to_break = solutions is None or len(solutions) == 0

                if to_break:
                    if PRINT_DEBUG_GENERATION: smart_print(";")
                    break
        else:
            if PRINT_DEBUG_GENERATION: smart_print("|", end="")
            bad_indices.append(random_index)
            continue

        if wordsize <= 4:
            assert check_ccz_equivalence_anf(modadd_anf, modadd_anf, l_c_linv_i, a_input_vars=bpr_simple.gens())

        list_graph_automorphisms.append(l_c_linv_i)

        if TRIVIAL_GA == "repeat":
            for _ in range(len(list_graph_automorphisms), rounds - 1):
                list_graph_automorphisms.append(l_c_linv_i)
            assert len(list_graph_automorphisms) == rounds - 1

        if len(list_graph_automorphisms) == rounds - 1:
            break

    return list_graph_automorphisms


def get_redundant_perturbations(wordsize, rounds, degree_qi, bpr):
    ws = wordsize

    use_quasilinear_rp = True

    if TRIVIAL_RP is True:
        list_redundant_perturbations = []
        for i in range(rounds - 1):
            anf = [bpr(0) for _ in range(2*ws)]
            anf_one = [bpr(1) for _ in range(2*ws)]
            list_redundant_perturbations.append([anf, anf, anf, anf_one])

        return list_redundant_perturbations

    def get_a0_a1_b0_b1():
        """Return A0, A1, B0, B1 such that B0, B1 != A0, A1."""
        if use_quasilinear_rp:
            def get_random_boolean_function():
                p1 = bpr.random_element(degree=1, terms=sage.all.Infinity, vars_set=list(range(4*ws)))
                p2 = bpr.random_element(degree=degree_qi, terms=sage.all.Infinity, vars_set=list(range(2*ws)))
                return p1 + p2
        else:
            def get_random_boolean_function():
                return bpr.random_element(degree=degree_qi, terms=sage.all.Infinity, vars_set=list(range(4*ws)))

        list_d = []
        for index_d in range(3):
            if index_d in [0, 1]:
                d = [get_random_boolean_function() for _ in range(2*ws - 1)]
            else:
                assert index_d == 2
                d = [get_random_boolean_function() for _ in range(2*ws - 2)]
            while True:
                lc = sage.all.random_vector(sage.all.GF(2), len(d))
                if 1 not in lc:
                    continue
                lc = sage.all.vector(bpr, list(lc))
                d.append(lc.dot_product(sage.all.vector(bpr, d)) + 1)
                break

            sage.all.shuffle(d)
            random_affine = get_random_affine_permutations(len(d), 1)[0]
            d = list(random_affine.matrix * sage.all.vector(bpr, d) + random_affine.cta)

            if index_d == 2:
                random_index = sage.all.ZZ.random_element(0, 2*ws)
                d.insert(random_index, list_d[0][random_index] + list_d[1][random_index] + 1)
                # d.append(list_d[0][-1] + list_d[1][-1] + 1)

            list_d.append(sage.all.vector(bpr, d))

        if wordsize == 4:
            from boolcrypt.cczselfequivalence import _get_lowdeg_inv_equations
            list_d.append(list_d[0] + list_d[1] + list_d[2])
            for d in list_d:
                is_inconsistent = False
                try:
                    _get_lowdeg_inv_equations(d, bpr, max_deg=sage.all.infinity, depth=sage.all.infinity)
                except ValueError as e:
                    is_inconsistent = str(e).startswith("found non-balanced component")
                assert is_inconsistent

        assert all(len(d) == 2*ws for d in list_d), f"{[len(d) for d in list_d]}"

        # a0 does not need to be a permutation
        a0 = [get_random_boolean_function() for _ in range(2*ws)]
        a0 = sage.all.vector(bpr, a0)
        # a0 = get_random_affine_permutations(2*ws, 1)[0]
        # a0 = sage.all.vector(bpr, matrix2anf(a0.matrix, bpr, bin_vector=a0.cta))

        d0, d1, d2 = list_d[:3]

        b0 = d0 + a0
        a1 = d1 + b0
        b1 = d2 + a0

        return a0, a1, b0, b1

    list_redundant_perturbations = []
    for i in range(rounds - 1):
        while True:
            # only input variables
            l01 = bpr.random_element(degree=1, terms=sage.all.Infinity, vars_set=list(range(2*ws)))
            l23 = bpr.random_element(degree=1, terms=sage.all.Infinity, vars_set=list(range(2*ws)))
            if 0 != l01 != 1 and 0 != l23 != 1:
                break
        q0, q1, q2, q3 = get_a0_a1_b0_b1()

        p0 = [l01 * f for f in q0]
        p1 = [(l01 + bpr(1)) * f for f in q1]
        p2 = [l23 * f for f in q2]
        p3 = [(l23 + bpr(1)) * f for f in q3]

        my_list = [p0, p1, p2, p3]

        sage.all.shuffle(my_list)
        for j in range(len(my_list)):
            random_affine = get_random_affine_permutations(len(my_list[j]), 1)[0]
            my_list[j] = list(random_affine.matrix * sage.all.vector(bpr, my_list[j]))

        list_redundant_perturbations.append(my_list)

    return list_redundant_perturbations


def get_encoded_implicit_round_funcions(wordsize, implicit_affine_layers, filename):
    """
    implicit_affine_layers contains the affine layers of each round
    (since it is in implicit form, it contains the "input" and "output" affine part
    of each round)

    this function only supports ciphers where the non-linear layer of each
    round is exactly (x, y) = (x \boxplus y,y)

    wordsize is the bit-size of one of the inputs of the modular addition
    (half of the total blocksize since only 1 modular addition is supported)
    """
    rounds = len(implicit_affine_layers)
    assert 1 <= rounds
    assert rounds == len(implicit_affine_layers)

    ws = wordsize

    smart_print = get_smart_print(filename)

    if PRINT_TIME_GENERATION:
        smart_print(f"# {get_time()} | started generation of implicit white-box implementation with affine encodings with parameters:")
        smart_print(f" - wordsize: {ws}")
        smart_print(f" - rounds: {rounds}")
        smart_print(f" - seed: {SEED}")
        smart_print(f" - USE_REDUNDANT_PERTURBATIONS: {USE_REDUNDANT_PERTURBATIONS}")
        smart_print(f" - TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AP: {[TRIVIAL_EE,TRIVIAL_GA,TRIVIAL_RP,TRIVIAL_AP]}")
        smart_print()

    bpr_pmodadd = implicit_affine_layers[0][0].parent()
    assert ws == len(bpr_pmodadd.gens()) // 4

    implicit_pmodadd = [bpr_pmodadd(str(f)) for f in get_implicit_modadd_anf(ws, permuted=True, only_x_names=False)]

    graph_automorphisms = get_graph_automorphisms(ws, rounds, filename)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated graph automorphisms")

    implicit_round_encodings, explicit_extin_function, explicit_extout_function = get_implicit_round_encodings(ws, rounds)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated implicit round encodings")

    left_permutations = get_random_affine_permutations(2 * ws, rounds - 1, bpr=bpr_pmodadd)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated left permutations")

    if USE_REDUNDANT_PERTURBATIONS:
        redundant_perturbations = get_redundant_perturbations(ws, rounds, degree_qi=1, bpr=bpr_pmodadd)

        if PRINT_TIME_GENERATION:
            smart_print(f"{get_time()} | generated redundant perturbations")

    implicit_round_functions = []
    list_degs = []
    for i in range(rounds - 1):
        anf = compose_anf_fast(implicit_pmodadd, graph_automorphisms[i])
        anf = compose_anf_fast(anf, implicit_affine_layers[i])
        anf = compose_anf_fast(anf, implicit_round_encodings[i])
        anf = list(left_permutations[i].matrix * sage.all.vector(bpr_pmodadd, anf))
        assert bpr_pmodadd == implicit_affine_layers[i][0].parent()

        degs = [f.degree() for f in anf]
        assert max(degs) == 2
        list_degs.append(degs)

        list_anfs = []
        if USE_REDUNDANT_PERTURBATIONS:
            for index_rp, rp in enumerate(redundant_perturbations[i]):
                assert len(anf) == len(rp)
                if _DEBUG_SPLIT_RP:
                    list_anfs.append([anf, rp])
                else:
                    # list_anfs.append([f + g for f, g in zip(anf, rp)])
                    perturbed_anf = sage.all.vector(bpr_pmodadd, [f + g for f, g in zip(anf, rp)])
                    invertible_matrix = get_random_affine_permutations(2*ws, 1, bpr=bpr_pmodadd)[0].matrix
                    perturbed_anf = list(invertible_matrix * perturbed_anf)
                    list_anfs.append(perturbed_anf)
            if not _DEBUG_SPLIT_RP:
                assert bpr_pmodadd == list_anfs[0][0].parent()
        else:
            list_anfs.append(anf)

        implicit_round_functions.append(list_anfs)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated implicit round functions with degrees {[collections.Counter(degs) for degs in list_degs]}")

    return implicit_round_functions, explicit_extin_function, explicit_extout_function


def get_eval_implicit_wb_implementation(
        wordsize, encoded_implicit_round_functions, filename=None,
        explicit_extin_function=None, explicit_extout_function=None,
        first_explicit_round=None, last_explicit_round=None,
    ):
    """
    get a function that evaluates the implicit white-box implementation
    the eval function takes and returns a GF(2) vector

    (optional) explicit_extin_function is a python function that
    cancels the input external encoding (obtained in get_encoded_implicit_round_funcions)
    similar for explicit_extout_function

    (optional) first_explicit_round is a python function that
    evaluates the first round of the cipher explicitly (that was not included
    in the encoded_implicit_round_functions)
    similar for last_explicit_round
    """
    rounds = len(encoded_implicit_round_functions)
    ws = wordsize

    smart_print = get_smart_print(filename)

    if USE_REDUNDANT_PERTURBATIONS is False:
        raise NotImplementedError("")
    
    if not _DEBUG_SPLIT_RP:
        bpr_pmodadd = encoded_implicit_round_functions[0][0][0].parent()  # round, perturbed system, component
    else:
        bpr_pmodadd = encoded_implicit_round_functions[0][0][0][0].parent()

    ordered_replacement = []
    assert len(bpr_pmodadd.gens()) == 4*ws
    for i in range(4*ws):
        if i < 2*ws:
            ordered_replacement.append(None)
        else:
            ordered_replacement.append(bpr_pmodadd.gens()[i])

    output_vars = bpr_pmodadd.gens()[2*ws: 4*ws]

    def eval_round_function(v, round_index):
        ordered_replacement_copy = ordered_replacement[:]
        for i in range(2 * ws):
            ordered_replacement_copy[i] = bpr_pmodadd(v[i])

        if _DEBUG_SPLIT_RP:
            implicit_rf = encoded_implicit_round_functions[round_index][0][0]
            system = [substitute_variables(bpr_pmodadd, ordered_replacement_copy, f) for f in implicit_rf]
            fixed_vars, new_equations = find_fixed_vars(
                system, only_linear=True, initial_r_mode="gauss", repeat_with_r_mode=None,
                initial_fixed_vars=None, bpr=bpr_pmodadd, check=False, verbose=False, debug=False, filename=None)
            assert len(new_equations) == 0, f"{fixed_vars}\n{list(new_equations)}"
            sol = [fixed_vars.get(v, None) for v in output_vars]
            base_sol = sol

            if PRINT_DEBUG_INTERMEDIATE_VALUES:
                smart_print(f" - base system:")
                smart_print(f"   > equations                           : {implicit_rf}")
                smart_print(f"   > (after substitution) equations      : {system}")
                smart_print(f"   > (after solving) remaining equations : {list(new_equations)}")
                smart_print(f"   > solution: {fixed_vars}")

            assert None not in sol
            assert all(f.degree() <= 1 for f in system)

            list_perturbation_values = []
            for index_rp, (_, rp) in enumerate(encoded_implicit_round_functions[round_index]):
                rp_system = [substitute_variables(bpr_pmodadd, ordered_replacement_copy, f) for f in rp]
                list_perturbation_values.append(rp_system)
                if PRINT_DEBUG_INTERMEDIATE_VALUES:
                    smart_print(f"   - perturbed system {index_rp}:")
                    smart_print(f"     >> equations                        : {rp}")
                    smart_print(f"     >> (after substitution) solutions   : {rp_system}")

            assert any(all(v_i == 0 for v_i in v) for v in list_perturbation_values)
            v0 = base_sol
        else:
            list_outputs = []

            for index_irf, implicit_rf in enumerate(encoded_implicit_round_functions[round_index]):
                system = [substitute_variables(bpr_pmodadd, ordered_replacement_copy, f) for f in implicit_rf]

                if PRINT_DEBUG_INTERMEDIATE_VALUES:
                    smart_print(f" - perturbed system {index_irf}:")
                    if ws == 4:
                        smart_print(f"   > equations                           : {implicit_rf}")
                        smart_print(f"   > (after substitution) equations      : {system}")

                if not all(f.degree() <= 1 for f in system):  # assuming QUASILINEAR_RP is True
                    raise ValueError("found non-quasilinear perturbed system")

                try:
                    fixed_vars, new_equations = find_fixed_vars(
                        system, only_linear=True, initial_r_mode="gauss", repeat_with_r_mode=None,
                        initial_fixed_vars=None, bpr=bpr_pmodadd, check=False, verbose=False, debug=False, filename=None)
                except ValueError as e:
                    if PRINT_DEBUG_INTERMEDIATE_VALUES:
                        smart_print(f"   > invalid system                      : {e}")
                    assert str(e).startswith("found 0 == 1")
                    continue

                if PRINT_DEBUG_INTERMEDIATE_VALUES:
                    smart_print(f"   > (after solving) remaining equations : {list(new_equations)}")
                    smart_print(f"   > solution: {fixed_vars}", end="")

                found_non_cta = any(v not in [0, 1] for v in fixed_vars.values())
                if found_non_cta or len(new_equations) >= 1:
                    if PRINT_DEBUG_INTERMEDIATE_VALUES:
                        smart_print(" = INVALID")
                    continue

                assert len(new_equations) == 0, f"{fixed_vars}\n{list(new_equations)}"

                sol = [fixed_vars.get(v, None) for v in output_vars]
                # v = sage.all.vector(sage.all.GF(2), sol)
                if PRINT_DEBUG_INTERMEDIATE_VALUES:
                    smart_print(f" = {sol}")
                if None not in sol:
                    list_outputs.append(tuple(sol))

            occurrences = collections.Counter(list_outputs)

            if PRINT_DEBUG_INTERMEDIATE_VALUES:
                smart_print(f" - output = most_common({occurrences})")

            if len(occurrences) >= 2:
                (v0, n0), (_, n1) = occurrences.most_common(2)
                assert n0 >= 2 and n0 > n1, f"{occurrences}\n{list_outputs}"
            else:
                v0, _ = occurrences.most_common(1)[0]

        return sage.all.vector(sage.all.GF(2), v0)

    def eval_implicit_wb_implementation(v):
        if PRINT_INTERMEDIATE_VALUES:
            smart_print(f"\nplaintext | {hex(vector2int(v))} = {v}")

        if first_explicit_round is not None:
            v = first_explicit_round(v)
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"after first explicit round | {hex(vector2int(v))} = {v}")

        if explicit_extin_function is not None:
            v = explicit_extin_function(v)
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"Inverse of external input encodings:\n - output | {hex(vector2int(v))} = {v}")
                smart_print("")

        for i in range(rounds):
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"Implicit round function {i}:")
            v = eval_round_function(v, i)
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f" - output | {hex(vector2int(v))} = {v}")

        if explicit_extout_function is not None:
            v = explicit_extout_function(v)
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"\nInverse of external output encodings:\n - output | {hex(vector2int(v))} = {v}")

        if last_explicit_round is not None:
            v = last_explicit_round(v)
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"after last explicit round | {hex(vector2int(v))} = {v}")

        if PRINT_INTERMEDIATE_VALUES:
            smart_print(f"ciphertext | {hex(vector2int(v))} = {v}")
            
        return v

    return eval_implicit_wb_implementation
