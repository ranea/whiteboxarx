"""Implicit implementation with affine encodings."""
import collections
from functools import partial

import sage.all

from boolcrypt.utilities import (
    substitute_variables, BooleanPolynomialRing,
    matrix2anf, compose_anf_fast,
    get_time, get_smart_print
)


from boolcrypt.modularaddition import get_implicit_modadd_anf


_DEBUG_SPLIT_RP = False  # do not merge the redundant perturbations with the implicit round functions, _DEBUG_SPLIT_RP=True only meant for debugging


AffineEncoding = collections.namedtuple('AffineEncoding', ['matrix', 'cta', 'bitsize', 'inverse'])


def get_random_affine_permutations(bitsize, number_of_permutations, TRIVIAL_AE, bpr=None):
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


def get_implicit_affine_round_encodings(wordsize, rounds, TRIVIAL_EE, TRIVIAL_AE):
    if not TRIVIAL_EE and TRIVIAL_AE:
        raise ValueError("using non-trivial external encoding with trivial affine encodings is not supported")

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

    affine_encodings = get_random_affine_permutations(2 * ws, rounds - 1, TRIVIAL_AE)

    for i in range(rounds):
        if i == 0:
            if TRIVIAL_EE:
                input_ee_matrix = identity_matrix(2*ws)
                input_ee_cta = [0 for _ in range(2*ws)]
            else:
                input_ee = get_random_affine_permutations(2 * ws, 1, TRIVIAL_AE)[0]
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
                output_ee = get_random_affine_permutations(2 * ws, 1, TRIVIAL_AE)[0]
                output_ee_matrix = output_ee.matrix
                output_ee_cta = list(output_ee.cta)
            matrix = sage.all.block_matrix(bpr, 2, 2, [
                [affine_encodings[i-1].matrix, zero_matrix(2*ws, 2*ws)],
                [zero_matrix(2*ws, 2*ws), output_ee_matrix]])
            cta = list(affine_encodings[i-1].cta) + output_ee_cta
            implicit_round_encodings[i] = matrix2anf(matrix, bool_poly_ring=bpr_pmodadd, bin_vector=cta)

    if TRIVIAL_EE:
        explicit_extin_anf = bpr_pmodadd.gens()[:2*ws]
        explicit_extout_anf = bpr_pmodadd.gens()[:2*ws]
    else:
        aux_matrix = input_ee.matrix.inverse()
        explicit_extin_anf = matrix2anf(aux_matrix, bool_poly_ring=bpr_pmodadd, bin_vector=aux_matrix * input_ee.cta)
        explicit_extout_anf = matrix2anf(output_ee.matrix, bool_poly_ring=bpr_pmodadd, bin_vector=output_ee.cta)

    bpr_xy = BooleanPolynomialRing(names=bpr_pmodadd.variable_names()[:2*ws], order="deglex")
    explicit_extin_anf = [bpr_xy(str(f)) for f in explicit_extin_anf]
    explicit_extout_anf = [bpr_xy(str(f)) for f in explicit_extout_anf]

    return implicit_round_encodings, explicit_extin_anf, explicit_extout_anf


def get_graph_automorphisms(wordsize, rounds, filename, TRIVIAL_GA, PRINT_DEBUG_GENERATION):
    ws = wordsize

    if TRIVIAL_GA == True:
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


def get_redundant_perturbations(wordsize, rounds, degree_qi, bpr, TRIVIAL_RP, TRIVIAL_AE):
    ws = wordsize

    use_quasilinear_rp = True

    if TRIVIAL_RP:
        list_redundant_perturbations = []
        for i in range(rounds):
            anf = [bpr(0) for _ in range(2*ws)]
            anf_one = [bpr(1) for _ in range(2*ws)]
            list_redundant_perturbations.append([anf, anf, anf, anf_one])

        return list_redundant_perturbations

    def get_a0_a1_b0_b1():
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
            random_affine = get_random_affine_permutations(len(d), 1, TRIVIAL_AE)[0]
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
        # a0 = get_random_affine_permutations(2*ws, 1, TRIVIAL_AE)[0]
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
            random_affine = get_random_affine_permutations(len(my_list[j]), 1, TRIVIAL_AE)[0]
            my_list[j] = list(random_affine.matrix * sage.all.vector(bpr, my_list[j]))

        list_redundant_perturbations.append(my_list)

    return list_redundant_perturbations


def get_implicit_encoded_round_funcions(
        implicit_affine_layers, filename,
        SEED, USE_REDUNDANT_PERTURBATIONS,
        TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE,
        PRINT_TIME_GENERATION, PRINT_DEBUG_GENERATION):
    """
    The argument implicit_affine_layers contains the affine layers of each round
    (since it is in implicit form, it contains the "input" and "output" affine part
    of each round).

    This function currently only supports ciphers where the non-linear layer of each
    round is exactly (x, y) = (x \boxplus y,y).
    """
    rounds = len(implicit_affine_layers)
    assert 1 <= rounds
    assert rounds == len(implicit_affine_layers)

    bpr_pmodadd = implicit_affine_layers[0][0].parent()
    ws = len(bpr_pmodadd.gens()) // 4

    # wordsize is the bit-size of one of the inputs of the modular addition
    # (half of the total blocksize since only 1 modular addition is supported)

    smart_print = get_smart_print(filename)

    if PRINT_TIME_GENERATION:
        smart_print(f"# {get_time()} | started generation of implicit white-box implementation with affine encodings with parameters:")
        smart_print(f" - wordsize: {ws}, blocksize: {2*ws}")
        smart_print(f" - rounds: {rounds}")
        smart_print(f" - seed: {SEED}")
        smart_print(f" - USE_REDUNDANT_PERTURBATIONS: {USE_REDUNDANT_PERTURBATIONS}")
        smart_print(f" - TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE: {[TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE]}")
        smart_print()

    assert ws == len(bpr_pmodadd.gens()) // 4

    implicit_pmodadd = [bpr_pmodadd(str(f)) for f in get_implicit_modadd_anf(ws, permuted=True, only_x_names=False)]

    if not USE_REDUNDANT_PERTURBATIONS:
        num_ga = rounds
    else:
        redundant_perturbations = get_redundant_perturbations(ws, rounds, 1, bpr_pmodadd, TRIVIAL_RP, TRIVIAL_AE)
        num_rp_per_round = len(redundant_perturbations[0])
        assert all(num_rp_per_round == len(redundant_perturbations[i]) for i in range(len(redundant_perturbations)))

        if PRINT_TIME_GENERATION:
            smart_print(f"{get_time()} | generated redundant perturbations")

        num_ga = rounds * num_rp_per_round

    graph_automorphisms = get_graph_automorphisms(ws, num_ga, filename, TRIVIAL_GA, PRINT_DEBUG_GENERATION)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated graph automorphisms")

    implicit_round_encodings, explicit_extin_anf, explicit_extout_anf = get_implicit_affine_round_encodings(ws, rounds, TRIVIAL_EE, TRIVIAL_AE)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated implicit round encodings")

    left_permutations = get_random_affine_permutations(2 * ws, rounds, TRIVIAL_AE, bpr=bpr_pmodadd)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated left permutations")

    implicit_round_functions = []
    list_degs = []
    for i in range(rounds):
        if not USE_REDUNDANT_PERTURBATIONS:
            anf = compose_anf_fast(implicit_pmodadd, graph_automorphisms[i])
            anf = compose_anf_fast(anf, implicit_affine_layers[i])
            anf = compose_anf_fast(anf, implicit_round_encodings[i])
            anf = list(left_permutations[i].matrix * sage.all.vector(bpr_pmodadd, anf))
            assert bpr_pmodadd == implicit_affine_layers[i][0].parent()

            degs = [f.degree() for f in anf]
            assert max(degs) == 2
            list_degs.append(degs)

            implicit_round_functions.append(anf)
        else:
            list_anfs = []
            for index_rp, rp in enumerate(redundant_perturbations[i]):
                anf = compose_anf_fast(implicit_pmodadd, graph_automorphisms[num_rp_per_round*i + index_rp])
                anf = compose_anf_fast(anf, implicit_affine_layers[i])
                anf = compose_anf_fast(anf, implicit_round_encodings[i])
                anf = list(left_permutations[i].matrix * sage.all.vector(bpr_pmodadd, anf))
                assert bpr_pmodadd == implicit_affine_layers[i][0].parent()

                degs = [f.degree() for f in anf]
                assert max(degs) == 2
                if index_rp == 0:
                    list_degs.append(degs)

                assert len(anf) == len(rp)
                if _DEBUG_SPLIT_RP:
                    list_anfs.append([anf, rp])
                else:
                    # list_anfs.append([f + g for f, g in zip(anf, rp)])
                    perturbed_anf = sage.all.vector(bpr_pmodadd, [f + g for f, g in zip(anf, rp)])
                    invertible_matrix = get_random_affine_permutations(2*ws, 1, TRIVIAL_AE, bpr=bpr_pmodadd)[0].matrix
                    perturbed_anf = list(invertible_matrix * perturbed_anf)
                    list_anfs.append(perturbed_anf)
            if not _DEBUG_SPLIT_RP:
                assert bpr_pmodadd == list_anfs[0][0].parent()
            implicit_round_functions.append(list_anfs)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated implicit round functions with degrees {[collections.Counter(degs) for degs in list_degs]}")

    return ws, implicit_round_functions, explicit_extin_anf, explicit_extout_anf
