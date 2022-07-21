"""Get a list of graph automorphisms from `stored_cczse_pmodadd_w*.sobj`.

The file `data/stored_cczse_pmodadd_w*.sobj` contains subsets of functions
where graph automorphisms of the permuted modular addition (that are not
right SE of the implicit function of the permuted modular addition) for
the wordsize w* can be sampled. These subsets of functions also contain other
functions, and sampling graph automorphisms requires the filtering done here.

Note that the file `stored_cczse_pmodadd_w*.sobj` does not contain all
the graph automorphisms of the permuted modular addition,
and the sampling is not uniformly.
"""
import sage.all
from sage.sat.boolean_polynomials import solve as solve_sat

from boolcrypt.utilities import (
    substitute_variables, BooleanPolynomialRing, anf2matrix,
    get_smart_print, get_symbolic_anf
)

from boolcrypt.functionalequations import solve_functional_equation

from boolcrypt.modularaddition import get_implicit_modadd_anf

from boolcrypt.se_pmodadd.find_quasilinear_ga import graph_cczse_coeffs2modadd_cczse_anf


def get_graph_automorphisms(wordsize, rounds, filename, print_debug_generation, use_same_ga_for_all_rounds=False):
    ws = wordsize
    smart_print = get_smart_print(filename)

    try:
        filename_sobj = f"data/stored_cczse_pmodadd_w{wordsize}.sobj"
        coeff2expr, equations = sage.all.load(filename_sobj, compress=True)
    except FileNotFoundError:
        filename_sobj = f"whiteboxarx/data/stored_cczse_pmodadd_w{wordsize}.sobj"
        coeff2expr, equations = sage.all.load(filename_sobj, compress=True)

    # 1 - Get l_c_linv and equations with the correct BooleanPolynomialRing

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

    # 2 - Get all the subsets

    list_extra_var2val = solve_sat(equations, n=sage.all.infinity)
    if not list_extra_var2val:
        raise ValueError(f'equations from "stored_cczse_pmodadd_w{wordsize}" are inconsistent (unsatisfiable)')
    if print_debug_generation:
        smart_print(f"get_graph_automorphims | found {len(list_extra_var2val)} subsets of graph automorphisms (GA) to use for ws {wordsize}")

    # 3 - Auxiliary variables for the following loop
    # a subset is "good"/"bad" depending or whether it contains any good GA for MAX_SAMPLES_PER_GA_SUBSET tries

    list_graph_automorphisms = []
    bad_subset_indices = []
    good_subset_indices = []

    ordered_replacement = []
    variable_names = bpr.variable_names()
    strvar2index = lambda x: variable_names.index(x)
    for i in range(len(variable_names)):
        if i < 4*ws:
            ordered_replacement.append(bpr.gens()[i])
        else:
            ordered_replacement.append(None)

    implicit_pmodadd = [bpr_simple(str(f)) for f in get_implicit_modadd_anf(ws, permuted=True, only_x_names=False)]

    while len(list_graph_automorphisms) < rounds:
        # 4 - Loop to obtain a GA for each round

        assert len(bad_subset_indices) < len(list_extra_var2val)
        if len(bad_subset_indices) + len(good_subset_indices) >= len(list_extra_var2val):
            subset_index = good_subset_indices[sage.all.ZZ.random_element(0, len(good_subset_indices))]
            # warnings.warn(f"finding GA from subset {subset_index} again")
        else:
            subset_index = sage.all.ZZ.random_element(0, len(list_extra_var2val))
            if subset_index in bad_subset_indices or subset_index in good_subset_indices:
                continue

        ordered_replacement_copy = ordered_replacement[:]
        for k, v in list_extra_var2val[subset_index].items():
            ordered_replacement_copy[strvar2index(str(k))] = bpr(str(v))

        ordered_replacement_copy_copy = ordered_replacement_copy[:]

        subset_cardinality_log2 = ordered_replacement_copy_copy[4*ws:  len(variable_names)].count(None)
        subset_cardinality = 2**subset_cardinality_log2
        num_samples = min(subset_cardinality, max(subset_cardinality_log2, 8))  # MAX_SAMPLES_PER_GA_SUBSET
        if print_debug_generation:
            smart_print(f"\tfinding GA in subset {subset_index} by sampling "
                        f"{num_samples} functions out of 2^{subset_cardinality_log2}: ", end="")

        for index_sample in range(num_samples):
            for j in range(4*ws, len(variable_names)):
                if ordered_replacement_copy_copy[j] is None:
                    ordered_replacement_copy_copy[j] = bpr(sage.all.GF(2).random_element())

            l_c_linv_i = [bpr_simple(str(substitute_variables(bpr, ordered_replacement_copy_copy, f))) for f in l_c_linv]
            l_c_linv_i_matrix = anf2matrix(l_c_linv_i, bpr_simple.gens())

            if not l_c_linv_i_matrix.is_invertible():
                # sampled GA not invertible
                if print_debug_generation: smart_print(".", end="")
                continue  # sample again ordered_replacement_copy_copy

            # check GA is not a right SE of T: symbolically T = B (T l_c_linv_i)
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
                is_right_SE = False
            else:
                is_right_SE = solutions is not None and len(solutions) != 0

            if is_right_SE:
                # sampled GA invertible but a right SE of T
                if print_debug_generation: smart_print(":", end="")
                continue  # sample again ordered_replacement_copy_copy

            # found valid GA
            if print_debug_generation:
                smart_print(f"\n\t\tfound GA in subset {subset_index} after {index_sample} tries")
            if subset_index not in good_subset_indices:
                good_subset_indices.append(subset_index)
            list_graph_automorphisms.append(l_c_linv_i)
            if use_same_ga_for_all_rounds:
                for _ in range(len(list_graph_automorphisms), rounds):
                    list_graph_automorphisms.append(l_c_linv_i)
                assert len(list_graph_automorphisms) == rounds
            break  # choose another subset_index
        else:
            if print_debug_generation:
                smart_print(f"\n\t\tno GA found in subset {subset_index} after {num_samples} tries")
            assert not (subset_index in good_subset_indices and num_samples == subset_cardinality)
            if subset_index not in good_subset_indices and subset_index not in bad_subset_indices:
                bad_subset_indices.append(subset_index)
            continue

    if wordsize <= 4:
        # check each function in list_graph_automorphisms is indeed a CCZ
        # (check only for wordsize 4, ows too slow)
        from boolcrypt.modularaddition import get_modadd_anf
        from boolcrypt.equivalence import check_ccz_equivalence_anf
        modadd_anf = get_modadd_anf(ws, permuted=True)
        for l_c_linv_i in list_graph_automorphisms:
            assert check_ccz_equivalence_anf(modadd_anf, modadd_anf, l_c_linv_i, a_input_vars=bpr_simple.gens())

    return list_graph_automorphisms
