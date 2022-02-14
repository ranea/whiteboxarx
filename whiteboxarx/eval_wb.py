import collections

import sage.all

from boolcrypt.functionalequations import find_fixed_vars

from boolcrypt.utilities import (
    substitute_variables, vector2int,
    int2vector, get_smart_print
)

from whiteboxarx.implicit_wb_with_affine_encodings import (
    _DEBUG_SPLIT_RP
)


def bitvectors_to_gf2vector(x, y, ws):
    return sage.all.vector(sage.all.GF(2), list(int2vector(x, ws)) + list(int2vector(y, ws)))


def gf2vector_to_bitvectors(v, ws):
    return vector2int(v[:ws]), vector2int(v[ws:])


def get_eval_implicit_wb_implementation(
        wordsize, encoded_implicit_round_functions,
        USE_REDUNDANT_PERTURBATIONS,
        PRINT_INTERMEDIATE_VALUES, PRINT_DEBUG_INTERMEDIATE_VALUES, filename=None,
        explicit_extin_function=None, explicit_extout_function=None,
        first_explicit_round=None, last_explicit_round=None,
    ):
    """Return a Python function that evaluates the implicit white-box implementation.

    This function takes and return a single SageMath-GF(2) vector.

    The (optional) argument explicit_extin_function is a python function that
    cancels the input external encoding (obtained in get_encoded_implicit_round_funcions).
    Similar for explicit_extout_function.

    The (optional) argument first_explicit_round is a python function that
    evaluates the first round of the cipher explicitly (that was not included
    in the encoded_implicit_round_functions).
    Similar for last_explicit_round.
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
