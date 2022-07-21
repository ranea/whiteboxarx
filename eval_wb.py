import collections
import os

import sage.all

from boolcrypt.functionalequations import find_fixed_vars

from boolcrypt.utilities import (
    substitute_variables, vector2int,
    int2vector, get_smart_print
)

from argparse import ArgumentParser


def bitvectors_to_gf2vector(x, y, ws):
    return sage.all.vector(sage.all.GF(2), list(int2vector(x, ws)) + list(int2vector(y, ws)))


def gf2vector_to_bitvectors(v, ws):
    return vector2int(v[:ws]), vector2int(v[ws:])


def get_eval_implicit_wb_implementation(
        wordsize, implicit_encoded_round_functions,
        USE_REDUNDANT_PERTURBATIONS,
        PRINT_INTERMEDIATE_VALUES, PRINT_DEBUG_INTERMEDIATE_VALUES, filename=None,
        explicit_extin_anf=None, explicit_extout_anf=None,
        first_explicit_round=None, last_explicit_round=None,
        DEBUG_SPLIT_RP=False,
    ):
    """Return a Python function that evaluates the implicit white-box implementation.

    This function takes and return a single SageMath-GF(2) vector.

    The (optional) argument explicit_extin_anf is a vectorial Boolean function that
    cancels the input external encoding (obtained in get_implicit_encoded_round_funcions).
    Similar for explicit_extout_anf.

    The (optional) argument first_explicit_round is a string representing python code that
    evaluates the first round of the cipher explicitly (that was not included
    in the implicit_encoded_round_functions).
    Similar for last_explicit_round.
    """
    rounds = len(implicit_encoded_round_functions)
    ws = wordsize

    smart_print = get_smart_print(filename)

    if not USE_REDUNDANT_PERTURBATIONS:
        bpr_pmodadd = implicit_encoded_round_functions[0][0].parent()  # round 0, component Boolean function 0
    else:
        if not DEBUG_SPLIT_RP:
            bpr_pmodadd = implicit_encoded_round_functions[0][0][0].parent()  # round 0, perturbed system 0, component Boolean function 0
        else:
            bpr_pmodadd = implicit_encoded_round_functions[0][0][0][0].parent()  # round 0, perturbed system 0, anf, component Boolean function 0

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

        if DEBUG_SPLIT_RP:
            implicit_rf = implicit_encoded_round_functions[round_index][0][0]
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
            for index_rp, (_, rp) in enumerate(implicit_encoded_round_functions[round_index]):
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
                systems_in_round_i = [implicit_encoded_round_functions[round_index]]
                assert len(systems_in_round_i) == 1
            else:
                systems_in_round_i = implicit_encoded_round_functions[round_index]
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

        if first_explicit_round is not None and first_explicit_round != "":
            x, y = gf2vector_to_bitvectors(v, ws)
            locs = {"x": x, "y": y, "WORD_SIZE": ws, "WORD_MASK": 2**ws - 1}
            exec(first_explicit_round, globals(), locs)
            v = bitvectors_to_gf2vector(locs["x"], locs["y"], ws)
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"after first explicit round | {hex(vector2int(v))} = {v}")

        if explicit_extin_anf is not None:
            v = [f(*v) for f in explicit_extin_anf]
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"Inverse of external input encodings:\n - output | {hex(vector2int(v))} = {v}")
                smart_print("")

        for i in range(rounds):
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"Implicit round function {i}:")
            v = eval_round_function(v, i)
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f" - output | {hex(vector2int(v))} = {v}")

        if explicit_extout_anf is not None:
            v = [f(*v) for f in explicit_extout_anf]
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"\nInverse of external output encodings:\n - output | {hex(vector2int(v))} = {v}")

        if last_explicit_round is not None and last_explicit_round != "":
            x, y = gf2vector_to_bitvectors(v, ws)
            locs = {"x": x, "y": y, "WORD_SIZE": ws, "WORD_MASK": 2**ws - 1}
            exec(last_explicit_round, globals(), locs)
            v = bitvectors_to_gf2vector(locs["x"], locs["y"], ws)
            if PRINT_INTERMEDIATE_VALUES:
                smart_print(f"after last explicit round | {hex(vector2int(v))} = {v}")

        if PRINT_INTERMEDIATE_VALUES:
            smart_print(f"ciphertext | {hex(vector2int(v))} = {v}")

        return v

    return eval_implicit_wb_implementation


if __name__ == '__main__':
    parser = ArgumentParser(prog="sage -python eval_wb.py", description="Evaluate the given implicit white-box implementation")
    parser.add_argument("--input-file", default="stored_irf_and_ee.sobj", help="the file containing the implicit encoded round functions and the external encodings")
    parser.add_argument("--plaintext", nargs=2, help="the input plaintext given as a hexadecimal representation of the words")
    #
    parser.add_argument("--cancel-external-encodings", action="store_true", help="cancel the external encodings to evaluate unencoded plaintexts and to obtain unencoded ciphertexts")
    parser.add_argument("--disabled-redundant-perturbations", action="store_true", help="assume the implicit encoded round functions do NOT contain redundant perturbations")
    parser.add_argument("--first-explicit-round", default="", help="the Python code describing the first explicit round not included in the implicit round functions")
    parser.add_argument("--last-explicit-round", default="", help="the Python code describing the last explicit round  not included in the implicit round functions")
    parser.add_argument("--output-file", help="the file to store the output ciphertext and the debug output (default: stdout)")
    parser.add_argument("--print-intermediate-values", action="store_true", help="print intermediate values output while evaluating the implicit implementation")
    parser.add_argument("--print-debug-intermediate-values", action="store_true", help="print debug information while evaluating the implicit round function")

    args = parser.parse_args()

    assert args.plaintext is not None
    assert args.output_file is None or not os.path.isfile(args.output_file), f"{args.output_file} already exists"

    implicit_encoded_round_functions, explicit_extin_anf, explicit_extout_anf = sage.all.load(args.input_file, compress=True)

    if not args.cancel_external_encodings:
        explicit_extin_anf, explicit_extout_anf = None, None

    USE_REDUNDANT_PERTURBATIONS = not args.disabled_redundant_perturbations

    if not USE_REDUNDANT_PERTURBATIONS:
        bpr_pmodadd = implicit_encoded_round_functions[0][0].parent()  # round 0, component Boolean function 0
    else:
        bpr_pmodadd = implicit_encoded_round_functions[0][0][0].parent()  # round 0, perturbed system 0, component Boolean function 0

    ws = len(bpr_pmodadd.gens()) // 4

    eval_wb = get_eval_implicit_wb_implementation(
        ws, implicit_encoded_round_functions, USE_REDUNDANT_PERTURBATIONS,
        args.print_intermediate_values, args.print_debug_intermediate_values, filename=args.output_file,
        explicit_extin_anf=explicit_extin_anf, explicit_extout_anf=explicit_extout_anf,
        first_explicit_round=args.first_explicit_round, last_explicit_round=args.last_explicit_round
    )

    smart_print = get_smart_print(args.output_file)

    plaintext = tuple(map(lambda p: int(p, 16), args.plaintext))

    if args.print_debug_intermediate_values:
        smart_print(f"Evaluating implicit white-box implementation with input ({plaintext[0]:x}, {plaintext[1]:x})\n")

    plaintext = bitvectors_to_gf2vector(*plaintext, ws)
    ciphertext = eval_wb(plaintext)
    ciphertext = gf2vector_to_bitvectors(ciphertext, ws)

    if args.print_debug_intermediate_values:
        smart_print(f"\nCiphertext = ({ciphertext[0]:x}, {ciphertext[1]:x})\n")
    else:
        smart_print(f"{ciphertext[0]:x} {ciphertext[1]:x}")
