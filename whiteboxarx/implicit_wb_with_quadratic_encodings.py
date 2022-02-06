"""Implicit implementation with quadratic encodings."""
import collections
from functools import partial

import sage.all

from boolcrypt.utilities import (
    substitute_variables, BooleanPolynomialRing,
    matrix2anf, compose_anf_fast,
    get_time, get_smart_print
)

from boolcrypt.modularaddition import get_implicit_modadd_anf


from whiteboxarx.implicit_wb_with_affine_encodings import (
    SEED, USE_REDUNDANT_PERTURBATIONS,
    TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE,
    PRINT_TIME_GENERATION, PRINT_DEBUG_GENERATION,
    _DEBUG_SPLIT_RP,
    get_graph_automorphisms, get_redundant_perturbations, get_implicit_affine_round_encodings, get_random_affine_permutations,
)

# -- Script parameters --

TRIVIAL_QSE = True  # whether to use trivial quadratic encodings
CUBIC_IRF = False  # if True, quadratic encodings and graph automorphisms are chosen such that the encoded implicit round functions are cubic and not quartic

# ----

sage.all.set_random_seed(SEED)
assert not (TRIVIAL_GA is True and CUBIC_IRF is True)


def get_explicit_affine_quadratic_se(wordsize, explicit_affine_layers, graph_automorphisms, filename):
    ws = wordsize

    if TRIVIAL_QSE is True:
        rounds = len(explicit_affine_layers)
        assert rounds == len(graph_automorphisms)

        names_x = ["x" + str(i) for i in range(ws)]
        names_y = ["y" + str(i) for i in range(ws)]
        names_z = ["z" + str(i) for i in range(ws)]
        names_t = ["t" + str(i) for i in range(ws)]
        names_xyzt = names_x + names_y + names_z + names_t

        bpr = BooleanPolynomialRing(names=names_xyzt, order="deglex")
        identity_matrix = partial(sage.all.identity_matrix, bpr)
        identity_anf = matrix2anf(identity_matrix(2*ws), bool_poly_ring=bpr)

        def trivial_foo(v):
            return v

        list_aq_se = []
        for i in range(rounds):
            list_aq_se.append(identity_anf)

        return list_aq_se, trivial_foo, trivial_foo
    else:
        from quadratic_self_equivalences import get_explicit_affine_quadratic_se as geaq
        return geaq(wordsize, explicit_affine_layers, graph_automorphisms, filename, TRIVIAL_EE, PRINT_DEBUG_GENERATION)


def get_encoded_implicit_round_funcions(wordsize, implicit_affine_layers, explicit_affine_layers, filename):
    rounds = len(implicit_affine_layers)
    assert 1 <= rounds
    assert rounds == len(implicit_affine_layers)

    ws = wordsize

    smart_print = get_smart_print(filename)

    if PRINT_TIME_GENERATION:
        smart_print(f"# {get_time()} | started generation of implicit white-box implementation with quadratic encodings with parameters:")
        smart_print(f" - wordsize: {ws}")
        smart_print(f" - rounds: {rounds}")
        smart_print(f" - seed: {SEED}")
        smart_print(f" - CUBIC_MODE: {CUBIC_IRF}")
        smart_print(f" - USE_REDUNDANT_PERTURBATIONS: {USE_REDUNDANT_PERTURBATIONS}")
        smart_print(f" - TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AP, TRIVIAL_QSE: {[TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE, TRIVIAL_QSE]}")
        smart_print()

    bpr_pmodadd = implicit_affine_layers[0][0].parent()
    assert ws == len(bpr_pmodadd.gens()) // 4

    implicit_pmodadd = [bpr_pmodadd(str(f)) for f in get_implicit_modadd_anf(ws, permuted=True, only_x_names=False)]

    graph_automorphisms = get_graph_automorphisms(ws, rounds, filename)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated graph automorphisms")

    explicit_affine_quadratic_se, explicit_affine_quadraticextin_function, explicit_affine_quadratic_extout_function = \
        get_explicit_affine_quadratic_se(ws, explicit_affine_layers, graph_automorphisms, filename)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated affine-quadratic self-equivalences")

    implicit_affine_round_encodings, explicit_affine_extin_function, explicit_affine_extout_function = get_implicit_affine_round_encodings(ws, rounds)

    def explicit_extin_function(v):
        v = explicit_affine_quadraticextin_function(v)
        return explicit_affine_extin_function(v)

    def explicit_extout_function(v):
        v = explicit_affine_quadratic_extout_function(v)
        return explicit_affine_extout_function(v)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated implicit round encodings")

    left_permutations = get_random_affine_permutations(2 * ws, rounds, bpr=bpr_pmodadd)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated left permutations")

    if USE_REDUNDANT_PERTURBATIONS:
        redundant_perturbations = get_redundant_perturbations(ws, rounds, degree_qi=2 if CUBIC_IRF else 3, bpr=bpr_pmodadd)

        if PRINT_TIME_GENERATION:
            smart_print(f"{get_time()} | generated redundant perturbations")

    implicit_round_functions = []
    list_degs = []
    for i in range(rounds):
        anf = compose_anf_fast(implicit_pmodadd, graph_automorphisms[i])
        anf = compose_anf_fast(anf, implicit_affine_layers[i])
        #
        aq_layer = tuple(explicit_affine_quadratic_se[i]) + bpr_pmodadd.gens()[2*ws:4*ws]
        anf = compose_anf_fast(anf, aq_layer)
        #
        anf = compose_anf_fast(anf, implicit_affine_round_encodings[i])
        anf = list(left_permutations[i].matrix * sage.all.vector(bpr_pmodadd, anf))
        assert bpr_pmodadd == implicit_affine_layers[i][0].parent()

        degs = [f.degree() for f in anf]
        if TRIVIAL_QSE is True or (i == 0 and TRIVIAL_EE):
            assert max(degs) == 2
        else:
            assert max(degs) == (3 if CUBIC_IRF else 4), f"{degs}"
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
