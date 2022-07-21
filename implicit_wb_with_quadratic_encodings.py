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
    _DEBUG_SPLIT_RP,
    get_graph_automorphisms, get_redundant_perturbations, get_implicit_affine_round_encodings, get_random_affine_permutations,
)


def get_explicit_affine_quadratic_se_encodings(wordsize, explicit_affine_layers, graph_automorphisms, filename, CUBIC_IRF, MAX_DEG_IRF, TRIVIAL_EE, TRIVIAL_QE, PRINT_DEBUG_GENERATION):
    ws = wordsize

    if TRIVIAL_QE:
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

        list_aq_se = []
        for i in range(rounds):
            list_aq_se.append(identity_anf)

        bpr_xy = BooleanPolynomialRing(names=bpr.variable_names()[:2 * ws], order="deglex")
        trivial_anf = list(bpr_xy.gens())

        return list_aq_se, trivial_anf, trivial_anf
    else:
        from quadratic_self_equivalences import get_explicit_affine_quadratic_se_encodings as geaqse
        return geaqse(wordsize, explicit_affine_layers, graph_automorphisms,
                      use_external_encodings=not TRIVIAL_EE, use_cubic_irf=CUBIC_IRF, ensure_max_degree=MAX_DEG_IRF,
                      verbose=PRINT_DEBUG_GENERATION, filename=filename)


def get_implicit_encoded_round_funcions(
        implicit_affine_layers, explicit_affine_layers, filename,
        SEED, CUBIC_IRF, MAX_DEG_IRF, USE_REDUNDANT_PERTURBATIONS,
        TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE, TRIVIAL_QE,
        PRINT_TIME_GENERATION, PRINT_DEBUG_GENERATION):
    rounds = len(implicit_affine_layers)
    assert 1 <= rounds
    assert rounds == len(implicit_affine_layers)

    bpr_pmodadd = implicit_affine_layers[0][0].parent()
    ws = len(bpr_pmodadd.gens()) // 4

    smart_print = get_smart_print(filename)

    if PRINT_TIME_GENERATION:
        smart_print(f"# {get_time()} | started generation of implicit white-box implementation with quadratic encodings with parameters:")
        smart_print(f" - wordsize: {ws}, blocksize: {2*ws}")
        smart_print(f" - rounds: {rounds}")
        smart_print(f" - seed: {SEED}")
        smart_print(f" - CUBIC_MODE: {CUBIC_IRF}")
        smart_print(f" - USE_REDUNDANT_PERTURBATIONS: {USE_REDUNDANT_PERTURBATIONS}")
        smart_print(f" - TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE, TRIVIAL_QE: {[TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE, TRIVIAL_QE]}")
        smart_print()

    assert ws == len(bpr_pmodadd.gens()) // 4

    implicit_pmodadd = [bpr_pmodadd(str(f)) for f in get_implicit_modadd_anf(ws, permuted=True, only_x_names=False)]

    graph_automorphisms = get_graph_automorphisms(ws, rounds, filename, TRIVIAL_GA, PRINT_DEBUG_GENERATION)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated graph automorphisms")

    explicit_affine_quadratic_se_encodings, explicit_affine_quadratic_extin_anf, explicit_affine_quadratic_extout_anf = \
        get_explicit_affine_quadratic_se_encodings(ws, explicit_affine_layers, graph_automorphisms, filename, CUBIC_IRF, MAX_DEG_IRF, TRIVIAL_EE, TRIVIAL_QE, PRINT_DEBUG_GENERATION)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated affine-quadratic self-equivalences")

    implicit_affine_round_encodings, explicit_affine_extin_anf, explicit_affine_extout_anf = get_implicit_affine_round_encodings(ws, rounds, TRIVIAL_EE, TRIVIAL_AE)

    explicit_extin_anf = list(compose_anf_fast(explicit_affine_extin_anf, explicit_affine_quadratic_extin_anf))
    explicit_extout_anf = list(compose_anf_fast(explicit_affine_quadratic_extout_anf, explicit_affine_extout_anf))

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated implicit round encodings")

    left_permutations = get_random_affine_permutations(2 * ws, rounds, TRIVIAL_AE, bpr=bpr_pmodadd)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated left permutations")

    if USE_REDUNDANT_PERTURBATIONS:
        redundant_perturbations = get_redundant_perturbations(ws, rounds, 2 if CUBIC_IRF else 3, bpr_pmodadd, TRIVIAL_RP, TRIVIAL_AE)

        if PRINT_TIME_GENERATION:
            smart_print(f"{get_time()} | generated redundant perturbations")

    implicit_round_functions = []
    list_degs = []
    for i in range(rounds):
        anf = compose_anf_fast(implicit_pmodadd, graph_automorphisms[i])
        anf = compose_anf_fast(anf, implicit_affine_layers[i])
        #
        aq_layer = tuple(bpr_pmodadd(str(f)) for f in explicit_affine_quadratic_se_encodings[i]) + bpr_pmodadd.gens()[2*ws:4*ws]
        anf = compose_anf_fast(anf, aq_layer)
        #
        anf = compose_anf_fast(anf, implicit_affine_round_encodings[i])
        anf = list(left_permutations[i].matrix * sage.all.vector(bpr_pmodadd, anf))
        assert bpr_pmodadd == implicit_affine_layers[i][0].parent()

        degs = [f.degree() for f in anf]
        # if TRIVIAL_QE or (i == 0 and TRIVIAL_EE):  # input external encoding is affine
        if TRIVIAL_QE or i == 0:
            assert max(degs) == 2
        elif not MAX_DEG_IRF:
            assert max(degs) >= 3
        else:
            assert max(degs) == (3 if CUBIC_IRF else 4), f"{degs}, {i}/{rounds}"
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
                    invertible_matrix = get_random_affine_permutations(2*ws, 1, TRIVIAL_AE, bpr=bpr_pmodadd)[0].matrix
                    perturbed_anf = list(invertible_matrix * perturbed_anf)
                    list_anfs.append(perturbed_anf)
            if not _DEBUG_SPLIT_RP:
                assert bpr_pmodadd == list_anfs[0][0].parent()
            implicit_round_functions.append(list_anfs)
        else:
            implicit_round_functions.append(anf)

    if PRINT_TIME_GENERATION:
        smart_print(f"{get_time()} | generated implicit round functions with degrees {[collections.Counter(degs) for degs in list_degs]}")

    return ws, implicit_round_functions, explicit_extin_anf, explicit_extout_anf
