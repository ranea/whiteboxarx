"""Get a list of affine-quadratic self-equivalences from `stored_aqse_pmodadd_w*.sobj`.

The file `data/stored_aqse_pmodadd_w*.sobj` contains affine-quadratic
self-equivalences (given as solutions of a system of equations)
of the permuted modular addition for the wordsize w*-.

To sample affine-quadratic self-equivalences, first
`MAX_SUBSET_SOLUTIONS * rounds` class solutions are obtained
from the system of equations included in `stored_aqse_pmodadd_w*.sobj`.
Each class solution gives a subset of self-equivalences.

If `ensure_max_degree=False`, a random self-equivalence is sampled for each
subset until obtaining all the needed self-equivalences.
Otherwise, for each subset we try `MAX_SAMPLES_PER_SE_SUBSET` times;
if no self-equivalence is obtained such that the resulting implicit round
function has maximum degree, the current subset is ignored and a new one is chosen.

Note that the file `stored_aqse_pmodadd_w*.sobj` does not contain all
the affine-quadratic self-equivalences of the permuted modular addition
(only the subset with cardinality 3^2 × 2^{3n+14} − 3 × 2^{2n+8} for wordsize n),
and the sampling is not uniformly.

Moreover, if `use_external_encodings=True`, note the external encodings
are not chosen as random quadratic permutation (not implemented yet).
Instead, the input external encoding returned here is the identity,
and the output external encoding is a right quadratic self-equivalence
(and these external encodings are composed with random affine permutations in
get_implicit_encoded_round_funcions()).
"""
import sage.all
from sage.sat.boolean_polynomials import solve as solve_sat

from boolcrypt.utilities import (
    substitute_variables, BooleanPolynomialRing,
    matrix2anf, compose_anf_fast, anf2matrix,
    get_smart_print, get_all_symbolic_coeff, get_ct_coeff, is_balanced
)

from boolcrypt.modularaddition import get_implicit_modadd_anf

from boolcrypt.se_pmodadd.find_affinequadratic_se import graph_aqse_coeffs2modadd_aqse_anf


MAX_SUBSET_SOLUTIONS = 128


def get_explicit_affine_quadratic_se_encodings(
        wordsize, explicit_affine_layers, graph_automorphisms,
        use_external_encodings, use_cubic_irf, ensure_max_degree,
        verbose, filename
    ):
    ws = wordsize
    rounds = len(explicit_affine_layers)
    assert rounds == len(graph_automorphisms)
    smart_print = get_smart_print(filename)

    try:
        filename_sobj = f"data/stored_aqse_pmodadd_w{wordsize}.sobj"
        coeff2expr, equations = sage.all.load(filename_sobj, compress=True)
    except FileNotFoundError:
        filename_sobj = f"whiteboxarx/data/stored_aqse_pmodadd_w{wordsize}.sobj"
        coeff2expr, equations = sage.all.load(filename_sobj, compress=True)

    if verbose:
        smart_print(f"get_explicit_affine_quadratic_se_encodings:")

    # 1 - Get inv_A_symbolic, B_symbolic and equations with the correct BooleanPolynomialRing
    # (inv_A_symbolic, B_symbolic) are symbolic ANF pairs representin
    # each solution from the solution set of stored_aqse_pmodadd_w{wordsize}
    # A solution is a pair (C, D) where (C^{-1}, D) or (C, D^{-1}) is an
    # affine-quadratic self-equivalences (in this function, we invert the affine C)

    names_x = ["x" + str(i) for i in range(ws)]
    names_y = ["y" + str(i) for i in range(ws)]
    names_z = ["z" + str(i) for i in range(ws)]
    names_t = ["t" + str(i) for i in range(ws)]
    names_xy = names_x + names_y
    names_xyzt = names_x + names_y + names_z + names_t

    inv_A_symbolic, B_symbolic = graph_aqse_coeffs2modadd_aqse_anf(coeff2expr, ws, verbose=False, debug=False, filename=None)

    names_coeff = list(inv_A_symbolic[0].parent().variable_names()[4*ws:])

    all_names = names_xyzt + names_coeff
    bpr = BooleanPolynomialRing(names=all_names, order="deglex")
    bpr_xy = BooleanPolynomialRing(names=names_xy, order="deglex")
    bpr_xyzt = BooleanPolynomialRing(names=names_xyzt, order="deglex")

    intermediate_bpr = BooleanPolynomialRing(names=all_names + ["x" + str(i) for i in range(ws, 4*ws)], order="deglex")
    repr_to_bpr = {"x" + str(ws + i): intermediate_bpr(v_i) for i, v_i in enumerate(names_y + names_z + names_t)}

    inv_A_symbolic = [bpr(intermediate_bpr(f).subs(repr_to_bpr)) for f in inv_A_symbolic]
    B_symbolic = [bpr(intermediate_bpr(f).subs(repr_to_bpr)) for f in B_symbolic]
    equations = [bpr(intermediate_bpr(eq).subs(repr_to_bpr)) for eq in equations]  # eq is str

    # 2 - Auxiliary variables for the following loop

    list_explicit_affinequadratic_encodings = [None for _ in range(rounds)]

    ordered_replacement = []
    variable_names = bpr.variable_names()
    strvar2index = lambda x: variable_names.index(x)
    for i in range(len(variable_names)):
        if i < 4*ws:
            ordered_replacement.append(bpr.gens()[i])
        else:
            ordered_replacement.append(None)

    implicit_pmodadd = [bpr_xyzt(str(f)) for f in get_implicit_modadd_anf(ws, permuted=True, only_x_names=False)]

    if not use_cubic_irf:
        # Get SE subsets
        list_solution_se_invAi_Bi = solve_sat(equations, n=MAX_SUBSET_SOLUTIONS*rounds)
        if list_solution_se_invAi_Bi is None or len(list_solution_se_invAi_Bi) == 0:
            raise ValueError(f'equations from "stored_aqse_pmodadd_w{wordsize}" are inconsistent (unsatisfiable)')
        if verbose:
            smart_print(f"\tfound {len(list_solution_se_invAi_Bi)} self-equivalence subsets "
                        f"to use for ws {wordsize}")
        from sage.misc.prandom import sample as sage_sample
        num_se = rounds - 1 if not use_external_encodings else rounds  # we are using a SE for input external encoding B_{0-1}
        list_solution_se_invAi_Bi = sage_sample(list_solution_se_invAi_Bi, num_se)
        bad_subset_indices = []  # to be used later
        good_subset_indices = []

    for index_round in range(rounds - 1, -1, -1):  # first is r-1, last is 0
        # - Let (A_i, B_i) an affine-quadratic SE of S. Recall A_i is used in round i and B_i in round (i+1).

        # - The first and intermediate implicit encoded round function is of the form
        #     T \circ GA_i \circ (AL_i, Id)            \circ ((AL_i^{-1} A_i AL_i) \circ B_{i-1}, Id) \circ AffineEncodings
        #   (in the 1st round, B_{i-1} is an arbitrary found being the external input encoding)

        # - For the last round (i = r-1), the implicit encoded round function is of the form
        #     T \circ GA_i \circ (AL_i, AL_{i+1}^{-1}) \circ ((AL_i^{-1} A_i AL_i) \circ B_{i-1}, Id) \circ AffineEncodings
        #   where B_i = AL_{i+1} B_i AL_{i+1}^{-1} is the external output encoding

        # - Therefore, the implicit encoded round function can be written in general
        #     T \circ GA_i \circ ....                  \circ (                    *             , Id) \circ AffineEncodings
        #   and the goal in this loop is to compute the * function (in explicit form) and to store it in
        #   list_explicit_affinequadratic_encodings

        # - Without external encodings, the first and last implicit encoded round function is of the form
        #     T \circ GA_i \circ (AL_i, Id)            \circ ((AL_i^{-1} A_i AL_i)              , Id) \circ AffineEncodings
        #     T \circ GA_i \circ (AL_i, AL_{i+1}^{-1}) \circ (B_{i-1}                           , Id) \circ AffineEncodings

        # ------ Get A_i, AL_i, and (AL_i^{-1} A_i AL_i) -----

        # - Auxiliary functions

        def invert_affine(my_matrix=None, my_ct=None, my_anf=None):
            # A^(-1)(x) =  L^(-1)(x) + L^(-1)(c)
            if my_anf is not None:
                my_matrix = anf2matrix(my_anf, input_vars=names_xy)
                my_ct = get_ct_coeff(my_anf, input_vars=names_xy)
            if my_matrix.base_ring() != sage.all.GF(2):
                my_matrix = my_matrix.change_ring(sage.all.GF(2))
            my_inv_matrix = my_matrix ** (-1)
            my_inv_ct = my_inv_matrix * sage.all.vector(bpr_xy, my_ct)
            return my_inv_matrix, my_inv_ct

        def get_invALj_Aj_ALj(Aj, ALj, ALj_matrix_ct):
            if Aj[0].parent() != bpr_xy:
                Aj = [bpr_xy(str(f)) for f in Aj]
            # ALj = matrix2anf(ALj_matrix_ct[0], bpr_simple, names_xy, ALj_matrix_ct[1])
            invALj_matrix, invALj_ct = invert_affine(*ALj_matrix_ct)
            # invALj_matrix = ALj_matrix_ct[0] ** (-1)
            # invALj_ct = invALj_matrix * sage.all.vector(bpr_xy, ALj_matrix_ct[1])
            invALj = matrix2anf(invALj_matrix, bpr_xy, names_xy, invALj_ct)

            # invALj_Aj_ALj ‹- invALj \circ Aj
            invALj_Aj_ALj = compose_anf_fast(invALj, Aj)
            # invALj_Aj_ALj ‹- invALj_Aj_ALj \circ ALj
            invALj_Aj_ALj = compose_anf_fast(invALj_Aj_ALj, ALj)

            assert len(invALj_Aj_ALj) == 2 * ws
            return invALj_Aj_ALj

        def get_Aj_from_Bj(solution_se_invAj_Bj):
            # solution_se_invAj_Bj is given in the form of ordered_replacement
            invAj = [bpr_xy(str(substitute_variables(bpr, solution_se_invAj_Bj, f))) for f in inv_A_symbolic]
            assert all(f.degree() <= 1 for f in invAj)

            # A^(-1)(x) =  L^(-1)(x) + L^(-1)(c)
            Aj_matrix, Aj_ct = invert_affine(my_anf=invAj)
            # Aj_matrix = anf2matrix(invAj, input_vars=names_xy) ** (-1)
            # Aj_ct = Aj_matrix * sage.all.vector(bpr_xy, get_ct_coeff(invAj, input_vars=names_xy))
            Aj = matrix2anf(Aj_matrix, bpr_xy, names_xy, Aj_ct)
            return Aj

        # - Get A_i

        if index_round == rounds - 1:
            if not use_external_encodings:
                # If not external encodings, (A_i, B_i) is the trivial SE
                A_i = bpr_xy.gens()

                explicit_affine_quadratic_extout_anf = list(bpr_xy.gens())
            else:
                # Sample a random affine-quadratic SE (A_i, B_i) and use
                # AL_{i+1} B_i AL_{i+1}^{-1} for the external output encoding
                aux_list_solution_se_invAi_Bi = solve_sat(equations, n=MAX_SUBSET_SOLUTIONS)
                assert not aux_list_solution_se_invAi_Bi is None or len(aux_list_solution_se_invAi_Bi) == 0
                subset_index = 0 #  sage.all.ZZ.random_element(0, len(aux_list_solution_se_invAi_Bi))
                ordered_replacement_copy = ordered_replacement[:]
                for k, v in aux_list_solution_se_invAi_Bi[subset_index].items():
                    ordered_replacement_copy[strvar2index(str(k))] = bpr(str(v))
                for i in range(4 * ws, len(ordered_replacement_copy)):
                    if ordered_replacement_copy[i] is None:
                        ordered_replacement_copy[i] = bpr(sage.all.GF(2).random_element())

                # ordered_replacement_copy is a solution containing (A_i^{-1}, B_i)
                A_i = get_Aj_from_Bj(ordered_replacement_copy)
                B_i = [bpr_xy(str(substitute_variables(bpr, ordered_replacement_copy, f))) for f in B_symbolic]

                # for the last round, explicit_affine_layers[index_round] contains 2 functions
                # (the right AL_i and left AL_{i+1} affine layers)
                AL_nexti_matrix_ct = explicit_affine_layers[index_round][1]

                inv_AL_nexti_matrix_ct = invert_affine(*AL_nexti_matrix_ct)
                inv_AL_nexti = matrix2anf(inv_AL_nexti_matrix_ct[0], bpr_xy, names_xy, inv_AL_nexti_matrix_ct[1])
                ALnexti_Bi_invALnexti = get_invALj_Aj_ALj(B_i, inv_AL_nexti, inv_AL_nexti_matrix_ct)

                explicit_affine_quadratic_extout_anf = ALnexti_Bi_invALnexti

                del aux_list_solution_se_invAi_Bi, subset_index, ordered_replacement_copy
        else:
            # solution_se_invAi_Bi computed in the previous iteration (for round i+1)
            A_i = get_Aj_from_Bj(solution_se_invAi_Bi)

        assert A_i[0].parent() == bpr_xy

        # - Get AL_i and AL_i^{-1} A_i AL_i

        if index_round == rounds - 1:
            # for the last round, explicit_affine_layers[index_round] contains 2 functions
            # (the right AL_i and left AL_{i+1} affine layers)
            AL_i_matrix_ct = explicit_affine_layers[index_round][0]
        else:
            AL_i_matrix_ct = explicit_affine_layers[index_round]
        AL_i = matrix2anf(AL_i_matrix_ct[0], bpr_xy, names_xy, AL_i_matrix_ct[1])
        invALi_Ai_ALi = get_invALj_Aj_ALj(A_i, AL_i, AL_i_matrix_ct)

        if index_round == rounds -1 and not use_external_encodings:
            assert list(invALi_Ai_ALi) == list(bpr_xy.gens())

        assert invALi_Ai_ALi[0].parent() == bpr_xy

        # ------ Get a random B_{i-1} -----

        # if index_round == 0 and not use_external_encodings:  # input EE is always the identity
        if index_round == 0:
            # B_{i-1} is the identity
            B_iprev = bpr_xy.gens()
            affine_quadratic_encoding = compose_anf_fast(invALi_Ai_ALi, B_iprev)
            assert affine_quadratic_encoding[0].parent() == bpr_xy
            assert len(affine_quadratic_encoding) == 2 * ws
            list_explicit_affinequadratic_encodings[index_round] = affine_quadratic_encoding

            explicit_affine_quadratic_extin_anf = list(bpr_xy.gens())

            break

        # 1. Get P_i = (T \circ GA_i)_0 \circ AL_i \circ (AL_i^{-1} A_i AL_i)
        # (needed not only for use_cubic_irf)

        T = implicit_pmodadd
        GA_i = graph_automorphisms[index_round]
        assert T[0].parent() == GA_i[0].parent() == bpr_xyzt

        # P_i ‹- (T \circ GA_i)_0
        P_i = [bpr_xy(str(f.subs({v: 0 for v in names_z + names_t}))) for f in compose_anf_fast(T, GA_i)]
        # P_i ‹- P_i \circ AL_i
        P_i = compose_anf_fast(P_i, AL_i)
        # P_i ‹- P_i \circ (AL_i^{-1} A_i AL_i)
        P_i = compose_anf_fast(P_i, invALi_Ai_ALi)

        # 2. If use_cubic_irf, get cubic_equations and list_solution_se_invAi_Bi
        # cubic_equations are the equations that ensure that P_i \circ B_{i-1} has no quartic monomials
        # (note that we only need P_i and not the whole implicit round function)

        if use_cubic_irf:
            Pi_circ_Biprev = [bpr(f.subs({x_i: v_i for x_i, v_i in zip(names_xy, B_symbolic)})) for f in [bpr(str(g)) for g in P_i]]
            list_mon2coeff = [get_all_symbolic_coeff(f, names_xyzt, ignore_terms_of_deg_strictly_less=4) for f in Pi_circ_Biprev]
            cubic_equations = set()
            for mon2coeff in list_mon2coeff:
                for coeff in mon2coeff.values():
                    cubic_equations.add(coeff)
            cubic_equations = list(cubic_equations)
            del list_mon2coeff

            # # ensure 1 cubic term is non-zero; too slow; deprecated
            # quad_monomials = [bpr(v) for v in names_coeff if v.startswith("aa")]
            # def or_bits(var1, var2):
            #     return var1 + var2 + (var1 * var2)
            # cubic_equations.append(bpr(sage.all.reduce(or_bits, quad_monomials)) + bpr(1))
            # # ensure sum of cubic terms is non-zero (implies at least 1 is non-zero); too strong; deprecated
            # ensure at least 1 quadratic monomial (ignored)
            # quad_monomials = [bpr(v) for v in names_coeff if v.startswith("aa")]
            # extra_eq = quad_monomials[sage.all.ZZ.random_element(0, len(quad_monomials))] + bpr(1)

            list_solution_se_invAi_Bi = solve_sat(equations + cubic_equations, n=MAX_SUBSET_SOLUTIONS)
            if not list_solution_se_invAi_Bi:
                raise ValueError(f'equations from "stored_aqse_pmodadd_w{wordsize}" are inconsistent (unsatisfiable)')
            if verbose:
                smart_print(f"\tfound {len(list_solution_se_invAi_Bi)} self-equivalence subsets "
                            f"to use for ws {wordsize} and round {index_round}")

            bad_subset_indices = []  # to be used later
            good_subset_indices = []

        # 3. Get B_{i-1} from a SE subset
        # a subset is "good"/"bad" depending or whether it contains a SE with corresponding IRF of max degree

        B_iprev = None
        ordered_replacement_copy_copy = None  # for solution_se_invAi_Bi later
        while True:
            assert len(bad_subset_indices) < len(list_solution_se_invAi_Bi)
            if len(bad_subset_indices) + len(good_subset_indices) >= len(list_solution_se_invAi_Bi):
                subset_index = good_subset_indices[sage.all.ZZ.random_element(0, len(good_subset_indices))]
                # warnings.warn(f"finding SE from subset {subset_index} again")
            else:
                subset_index = sage.all.ZZ.random_element(0, len(list_solution_se_invAi_Bi))
                if subset_index in bad_subset_indices or subset_index in good_subset_indices:
                    continue

            ordered_replacement_copy = ordered_replacement[:]
            for k, v in list_solution_se_invAi_Bi[subset_index].items():
                ordered_replacement_copy[strvar2index(str(k))] = bpr(str(v))

            ordered_replacement_copy_copy = ordered_replacement_copy[:]

            if not ensure_max_degree:
                subset_cardinality = 1
                num_samples = 1
            else:
                subset_cardinality_log2 = ordered_replacement_copy_copy[4 * ws:  len(variable_names)].count(None)
                subset_cardinality = 2 ** subset_cardinality_log2
                num_samples = min(subset_cardinality, max(subset_cardinality_log2, 8))  # MAX_SAMPLES_PER_SE_SUBSET
                if verbose:
                    smart_print(f"\t\tfinding SE leading to max IRF-degree in subset {subset_index} "
                                f"by sampling {num_samples} functions out of 2^{subset_cardinality_log2}: ", end="")

            for index_sample in range(num_samples):
                for j in range(4 * ws, len(variable_names)):
                    if ordered_replacement_copy_copy[j] is None:
                        ordered_replacement_copy_copy[j] = bpr(sage.all.GF(2).random_element())

                new_B_iprev = [bpr_xy(str(substitute_variables(bpr, ordered_replacement_copy_copy, f))) for f in B_symbolic]
                new_Pi_circ_Biprev = compose_anf_fast(P_i, new_B_iprev)
                degs = [f.degree() for f in new_Pi_circ_Biprev]

                if use_cubic_irf:
                    assert max(degs) <= 3
                if ensure_max_degree:
                    if (use_cubic_irf and max(degs) < 3) or (not use_cubic_irf and max(degs) < 3):
                        if verbose: smart_print(f"d{max(degs)},", end="")
                        continue  # sample again ordered_replacement_copy_copy

                # found good SE
                B_iprev = new_B_iprev
                if ensure_max_degree and verbose:
                    smart_print(f"\n\t\t\tfound SE in subset {subset_index} after {index_sample} tries")
                if subset_index not in good_subset_indices:
                    good_subset_indices.append(subset_index)
                break
            else:
                if verbose:
                    smart_print(f"\n\t\t\tno SE found in subset {subset_index} after {num_samples} tries")
                assert not (subset_index in good_subset_indices and num_samples == subset_cardinality)
                if subset_index not in good_subset_indices and subset_index not in bad_subset_indices:
                    bad_subset_indices.append(subset_index)
                continue

            if B_iprev is not None:
                break

        assert ordered_replacement_copy_copy is not None
        if B_iprev[0].parent() != bpr_xy:
            B_iprev = [bpr_xy(str(f)) for f in B_iprev]
        assert B_iprev[0].parent() == bpr_xy

        # ----- Store the affine-quadratic encoding (AL_i^{-1} A_i AL_i) \circ B_{i-1} -----

        affine_quadratic_encoding = compose_anf_fast(invALi_Ai_ALi, B_iprev)
        assert affine_quadratic_encoding[0].parent() == bpr_xy
        assert len(affine_quadratic_encoding) == 2 * ws
        assert any(f.degree() >= 2 for f in affine_quadratic_encoding), f"{[f.degree() for f in affine_quadratic_encoding]}"

        list_explicit_affinequadratic_encodings[index_round] = affine_quadratic_encoding

        solution_se_invAi_Bi = ordered_replacement_copy_copy  # for next round

        # # disabled finding the ANF othe inverse of B_{-1} (to cancel B_{-1}) not implemented
        # # ----- External input encodings -----
        #
        # if index_round == 0 and use_external_encodings:
        #     # Building explicit_affine_quadratic_extin_anf, an auxiliary function
        #     # which cancels the external input encoding B_{-1}
        #     # (by finding the input (x,y) such that v = B_{-1}(x, y) with v given)
        #
        #     assert B_iprev[0].parent() == bpr_xy
        #
        #     def explicit_affine_quadratic_extin_function(v):
        #         preimage_equations = [bpr_xy(v[i]) + f(*bpr_xy.gens()) for i, f in enumerate(B_iprev)]
        #
        #         # if verbose:
        #         #     smart_print(f"finding preimage of {v} = B_{{-1}}(...), with B_{{-1}} quadratic part of external input encoding")
        #
        #         solution_preimage = solve_sat(preimage_equations, n=1)
        #         if solution_preimage is None or len(solution_preimage) == 0:
        #             raise ValueError('could not find the inverse of external input encoding B_{-1}')
        #
        #         new_v = [None for _ in range(len(v))]
        #         strvar2index = lambda x: bpr_xy.variable_names().index(x)
        #         for sol_var, sol_val in solution_preimage[0].items():
        #             new_v[strvar2index(str(sol_var))] = v[0].parent()(str(sol_val))
        #
        #         return sage.all.vector(v[0].parent(), new_v)
        #
        #     # # finding the inverse is not possible for ws › 4
        #     # from boolcrypt.functionalequations import find_inverse
        #     #
        #     # assert B_iprev[0].parent() == bpr_xy
        #     #
        #     # bpr_xx = BooleanPolynomialRing(names=["x" + str(i) for i in range(2 * ws)], order="deglex")
        #     # # intermediate_bpr_xxy contains both bpr_xx bpr_xy
        #     # intermediate_bpr_xxy = BooleanPolynomialRing(names=["x" + str(i) for i in range(2 * ws)] + names_y, order="deglex")
        #     # replacements = {str(bpr_xy.gens()[ws + i]): intermediate_bpr_xxy.gens()[ws + i] for i in range(ws)}
        #     # B_iprev_xx = [bpr_xx(str(f.subs(replacements))) for f in B_iprev]
        #     #
        #     # if verbose:
        #     #     smart_print(f"\tfinding inverse of right quadratic SE B_{{-1}} for external input encoding:")
        #     #
        #     # for inv_deg in range(2, min(len(B_iprev_xx), len(bpr_xx.gens()))):
        #     #     inv_B_iprev_xx = find_inverse(
        #     #         B_iprev_xx, inv_deg, inv_position="left",
        #     #         reduction_mode=None, only_linear_fixed_vars=True, check_find_fixed_vars=False,
        #     #         verbose=True, debug=False, filename=None,
        #     #     )
        #     #     found_inverse = inv_B_iprev_xx is not None and len(inv_B_iprev_xx) != 0
        #     #     if verbose:
        #     #         smart_print(f"\t\tinverse{' ' if found_inverse else ' not '}found with degree={inv_deg}")
        #     #     if found_inverse:
        #     #         break
        #     # else:
        #     #     raise ValueError("inverse of B_0 not found")
        #     #
        #     # replacements = {str(bpr_xx.gens()[ws + i]): intermediate_bpr_xxy.gens()[2*ws + i] for i in range(ws)}
        #     # inv_B_iprev = [bpr_xy(str(f.subs(replacements))) for f in inv_B_iprev_xx]
        #     #
        #     # explicit_affine_quadratic_extin_anf = inv_B_iprev

    if wordsize <= 4:
        for affine_quadratic_encoding in list_explicit_affinequadratic_encodings:
            assert is_balanced(affine_quadratic_encoding)

    return list_explicit_affinequadratic_encodings, explicit_affine_quadratic_extin_anf, explicit_affine_quadratic_extout_anf
