"""Implicit implementation with affine encodings."""
import collections
from functools import partial

import sage.all

from boolcrypt.utilities import (
    substitute_variables, BooleanPolynomialRing,
    vector2int,
    matrix2anf, compose_anf_fast,
    get_time, get_smart_print
)

from boolcrypt.functionalequations import (
    find_fixed_vars
)

from boolcrypt.modularaddition import get_implicit_modadd_anf


# -- Script parameters --

SEED = abs(hash("eurocrypt2021"))

USE_REDUNDANT_PERTURBATIONS = True  # whether to add redundant perturbations to each implicit round function

TRIVIAL_EE = False  # whether to use trivial external encodins
TRIVIAL_GA = False  # whether to use trivial graph automorphisms (True, "repeat", or False)
TRIVIAL_RP = False  # whether to use trivial redundant perturbations
TRIVIAL_AE = False  # whether to use trivial affine encodings

PRINT_TIME_GENERATION = True  # whether to print time when each step finished
PRINT_DEBUG_GENERATION = True  # whether to print debug information
PRINT_INTERMEDIATE_VALUES = True  # whether to print intermediate values in eval_implicit_wb_implementation
PRINT_DEBUG_INTERMEDIATE_VALUES = True  # whether to print intermediate values in eval_round_function

# ----

sage.all.set_random_seed(SEED)
assert not (USE_REDUNDANT_PERTURBATIONS is False and TRIVIAL_RP is True)
_DEBUG_SPLIT_RP = False  # do not merge the redundant perturbations with the implicit round functions, _DEBUG_SPLIT_RP=True only meant for debugging


AffineEncoding = collections.namedtuple('AffineEncoding', ['matrix', 'cta', 'bitsize', 'inverse'])


def get_random_affine_permutations(bitsize, number_of_permutations, bpr=None):
    vs = sage.all.VectorSpace(sage.all.GF(2), bitsize)

    if bpr is None:
        bpr = sage.all.GF(2)

    def _get_affine_encoding():
        if not TRIVIAL_AE:
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


def get_implicit_affine_round_encodings(wordsize, rounds):
    ws = wordsize

    bpr = sage.all.GF(2)
    identity_matrix = partial(sage.all.identity_matrix, bpr)
    zero_matrix = partial(sage.all.zero_matrix, bpr)

    names = ["x" + str(i) for i in range(ws)]
    names += ["y" + str(i) for i in range(ws)]
    names += ["z" + str(i) for i in range(ws)]
    names += ["t" + str(i) for i in range(ws)]
    bpr_pmodadd = BooleanPolynomialRing(names=names, order="deglex")

    # bpr_ext = BooleanPolynomialRing(names=bpr_pmodadd.variable_names()[:2*ws], order="deglex")
    # identity_anf = bpr_pmodadd.gens()

    implicit_round_encodings = [None for _ in range(rounds)]

    affine_encodings = get_random_affine_permutations(2 * ws, rounds - 1)

    for i in range(rounds):
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
        elif 1 <= i < rounds - 1:
            matrix = sage.all.block_matrix(bpr, 2, 2, [
                [affine_encodings[i-1].matrix, zero_matrix(2*ws, 2*ws)],
                [zero_matrix(2*ws, 2*ws), affine_encodings[i].matrix]])
            cta = list(affine_encodings[i-1].cta) + list(affine_encodings[i].cta)
            implicit_round_encodings[i] = matrix2anf(matrix, bool_poly_ring=bpr_pmodadd, bin_vector=cta)
        else:
            assert i == rounds - 1
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

    if TRIVIAL_GA is True:
        names = ["x" + str(i) for i in range(ws)] + ["y" + str(i) for i in range(ws)]
        names += ["z" + str(i) for i in range(ws)] + ["t" + str(i) for i in range(ws)]
        bpr = BooleanPolynomialRing(names=names, order="deglex")
        identity_matrix = partial(sage.all.identity_matrix, bpr)

        list_graph_automorphisms = []
        for i in range(rounds):
            list_graph_automorphisms.append(matrix2anf(identity_matrix(4*ws), bool_poly_ring=bpr))

        return list_graph_automorphisms
    else:
        from graph_automorphisms import get_graph_automorphisms as gga
        return gga(ws, rounds, filename, PRINT_DEBUG_GENERATION, use_same_ga_for_all_rounds=TRIVIAL_GA=="repeat")


def get_redundant_perturbations(wordsize, rounds, degree_qi, bpr):
    ws = wordsize

    use_quasilinear_rp = True

    if TRIVIAL_RP is True:
        list_redundant_perturbations = []
        for i in range(rounds):
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
    for i in range(rounds):
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
        smart_print(f" - TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AP: {[TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE]}")
        smart_print()

    bpr_pmodadd = implicit_affine_layers[0][0].parent()
    assert ws == len(bpr_pmodadd.gens()) // 4

    implicit_pmodadd = [bpr_pmodadd(str(f)) for f in get_implicit_modadd_anf(ws, permuted=True, only_x_names=False)]

    graph_automorphisms = get_graph_automorphisms(ws, rounds, filename)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated graph automorphisms")

    implicit_round_encodings, explicit_extin_function, explicit_extout_function = get_implicit_affine_round_encodings(ws, rounds)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated implicit round encodings")

    left_permutations = get_random_affine_permutations(2 * ws, rounds, bpr=bpr_pmodadd)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated left permutations")

    if USE_REDUNDANT_PERTURBATIONS:
        redundant_perturbations = get_redundant_perturbations(ws, rounds, degree_qi=1, bpr=bpr_pmodadd)

        if PRINT_TIME_GENERATION:
            smart_print(f"{get_time()} | generated redundant perturbations")

    implicit_round_functions = []
    list_degs = []
    for i in range(rounds):
        anf = compose_anf_fast(implicit_pmodadd, graph_automorphisms[i])
        anf = compose_anf_fast(anf, implicit_affine_layers[i])
        anf = compose_anf_fast(anf, implicit_round_encodings[i])
        anf = list(left_permutations[i].matrix * sage.all.vector(bpr_pmodadd, anf))
        assert bpr_pmodadd == implicit_affine_layers[i][0].parent()

        degs = [f.degree() for f in anf]
        assert max(degs) == 2
        list_degs.append(degs)

        if USE_REDUNDANT_PERTURBATIONS:
            list_anfs = []
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
            implicit_round_functions.append(list_anfs)
        else:
            implicit_round_functions.append(anf)

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

    if not USE_REDUNDANT_PERTURBATIONS:
        bpr_pmodadd = encoded_implicit_round_functions[0][0].parent()  # round 0, component boolean function 0
    else:
        if not _DEBUG_SPLIT_RP:
            bpr_pmodadd = encoded_implicit_round_functions[0][0][0].parent()  # round 0, perturbed system 0, component boolean function 0
        else:
            bpr_pmodadd = encoded_implicit_round_functions[0][0][0][0].parent()  # round 0, perturbed system 0, anf, component boolean function 0

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

            if not USE_REDUNDANT_PERTURBATIONS:
                systems_in_round_i = [encoded_implicit_round_functions[round_index]]
                assert len(systems_in_round_i) == 1
            else:
                systems_in_round_i = encoded_implicit_round_functions[round_index]
                assert len(systems_in_round_i) == 4

            for index_irf, implicit_rf in enumerate(systems_in_round_i):
                system = [substitute_variables(bpr_pmodadd, ordered_replacement_copy, f) for f in implicit_rf]

                if PRINT_DEBUG_INTERMEDIATE_VALUES:
                    smart_print(f" - {'' if USE_REDUNDANT_PERTURBATIONS else 'non-'}perturbed system {index_irf}:")
                    if ws == 4:
                        smart_print(f"   > equations                           : {implicit_rf}")
                        smart_print(f"   > (after substitution) equations      : {system}")

                if not all(f.degree() <= 1 for f in system):  # assuming QUASILINEAR_RP is True
                    raise ValueError(f"implicit round function {index_irf} is not quasilinear "
                                     f"(has degrees {[f.degree() for f in system]} after fixing the input variables)")

                try:
                    fixed_vars, new_equations = find_fixed_vars(
                        system, only_linear=True, initial_r_mode="gauss", repeat_with_r_mode=None,
                        initial_fixed_vars=None, bpr=bpr_pmodadd, check=False, verbose=False, debug=False, filename=None)
                except ValueError as e:
                    if not USE_REDUNDANT_PERTURBATIONS:
                        raise ValueError(f"implicit round function {index_irf} has no solution, found error {e}")
                    if PRINT_DEBUG_INTERMEDIATE_VALUES:
                        smart_print(f"   > invalid perturbed system            : {e}")
                    assert str(e).startswith("found 0 == 1")
                    continue

                if PRINT_DEBUG_INTERMEDIATE_VALUES:
                    smart_print(f"   > (after solving) remaining equations : {list(new_equations)}")
                    smart_print(f"   > solution: {fixed_vars}", end="")

                found_non_cta = any(v not in [0, 1] for v in fixed_vars.values())
                if found_non_cta or len(new_equations) >= 1:
                    if not USE_REDUNDANT_PERTURBATIONS:
                        raise ValueError(f"implicit round function {index_irf} has no unique solution")
                    if PRINT_DEBUG_INTERMEDIATE_VALUES:
                        smart_print(f"   > invalid perturbed system            : multiple solutions")
                    continue

                assert len(new_equations) == 0, f"{fixed_vars}\n{list(new_equations)}"

                sol = [fixed_vars.get(v, None) for v in output_vars]
                # v = sage.all.vector(sage.all.GF(2), sol)
                if PRINT_DEBUG_INTERMEDIATE_VALUES:
                    smart_print(f" = {sol}")

                if None in sol:
                    if not USE_REDUNDANT_PERTURBATIONS:
                        raise ValueError(f"implicit round function {index_irf} has no unique solution")
                    if PRINT_DEBUG_INTERMEDIATE_VALUES:
                        smart_print(f"   > invalid perturbed system            : multiple solutions")

                list_outputs.append(tuple(sol))

            if not USE_REDUNDANT_PERTURBATIONS:
                assert len(list_outputs) == 1
                v0 = list_outputs[0]
            else:
                assert 1 <= len(list_outputs) <= 4
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
