import os

import sage.all

from argparse import ArgumentParser


if __name__ == '__main__':
    parser = ArgumentParser(prog="sage -python generate_wb.py", description="Generate implicit white-box implementations of ARX ciphers")
    parser.add_argument("--mode", default="export", choices=["export", "eval"], help="the mode to use: 'export' exports the generated implementation to C code, 'eval' evaluates it in Python (default: %(default)s)")
    parser.add_argument("--input-file", default="stored_affine_layers.sobj", help="the file used to store the (unencoded) implicit and explicit affine layers (default: %(default)s)")
    parser.add_argument("--debug-file", help="the file used to store the debug output (default: stdout)")
    parser.add_argument("--irf-degree", type=int, default=2, choices=[2, 3, 4], help="the degree of the encoded implicit round functions (default: %(default)i)")
    parser.add_argument("--seed", type=int, default=abs(hash("crypto2022")), help="the seed used to generate random values (default: a random value)")
    parser.add_argument("--trivial-affine-encodings", action="store_true", help="use trivial affine encodings")
    parser.add_argument("--trivial-quadratic-encodings", action="store_true", help="use trivial quadratic encodings")
    parser.add_argument("--trivial-external-encodings", action="store_true", help="use trivial external encodings")
    parser.add_argument("--trivial-redundant-perturbations", action="store_true", help="use trivial redundant perturbations")
    parser.add_argument("--trivial-graph-automorphisms", nargs="?", default=False, const=True, choices=["repeat"], help="use trivial graph automorphisms (if set to 'repeat', the same graph automorphism is used for each round)")
    parser.add_argument("--disable-redundant-perturbations", action="store_true", help="disable redundant perturbations")
    parser.add_argument("--ensure-max-degree", action="store_true", help="ensure that the encoded implicit round functions have maximum degree")
    parser.add_argument("--print-time-generation", action="store_true", help="print time generation output")
    parser.add_argument("--print-debug-generation", action="store_true", help="print debug information output")
    parser.add_argument("--export-file", default="white_box_backend.c", help="the file used to store the exported C code (default: %(default)s)")
    parser.add_argument("--encoding-mode", default="bin", choices=["hex", "bin", "bin_zero"], help="how to store the encoded implicit round functions in the exported C code (default: %(default)s)")
    parser.add_argument("--first-explicit-round", default="", help="C code describing the first explicit round; refer to README.md for examples (default: %(default)s)")
    parser.add_argument("--last-explicit-round", default="", help="C code describing the last explicit round; refer to README.md for examples (default: %(default)s)")
    parser.add_argument("--plaintext", nargs=2, help="the plaintext to use to evaluate the implicit implementation, a hexadecimal representation of the words (default: %(default)s)")
    parser.add_argument("--print-intermediate-values", action="store_true", help="print intermediate values output while evaluating the implicit implementation")
    parser.add_argument("--print-debug-intermediate-values", action="store_true", help="print intermediate values output while evaluating the implicit round function")

    args = parser.parse_args()

    assert args.debug_file is None or not os.path.isfile(args.debug_file), f"{args.debug_file} already exists"

    (unencoded_implicit_affine_layers, unencoded_explicit_affine_layers) = sage.all.load(args.input_file, compress=True)

    SEED = args.seed
    sage.all.set_random_seed(SEED)

    TRIVIAL_AE = args.trivial_affine_encodings
    TRIVIAL_QE = args.trivial_quadratic_encodings
    TRIVIAL_EE = args.trivial_external_encodings
    TRIVIAL_RP = args.trivial_redundant_perturbations
    TRIVIAL_GA = args.trivial_graph_automorphisms
    USE_REDUNDANT_PERTURBATIONS = not args.disable_redundant_perturbations
    MAX_DEG_IRF = args.ensure_max_degree
    PRINT_TIME_GENERATION = args.print_time_generation
    PRINT_DEBUG_GENERATION = args.print_debug_generation

    assert not (not USE_REDUNDANT_PERTURBATIONS and TRIVIAL_RP)

    assert not (args.mode == "export" and os.path.isfile(args.export_file)), f"{args.export_file} already exists"

    # degree of the encoded implicit round functions
    irf_degree = args.irf_degree

    if irf_degree == 2:
        from whiteboxarx.implicit_wb_with_affine_encodings import get_encoded_implicit_round_funcions

        # affine encodings
        ws, encoded_implicit_round_functions, explicit_extin_function, explicit_extout_function = \
            get_encoded_implicit_round_funcions(
                unencoded_implicit_affine_layers, args.debug_file,
                SEED, USE_REDUNDANT_PERTURBATIONS,
                TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE,
                PRINT_TIME_GENERATION, PRINT_DEBUG_GENERATION)
    elif irf_degree == 3 or irf_degree == 4:
        from whiteboxarx.implicit_wb_with_quadratic_encodings import get_encoded_implicit_round_funcions

        # quadratic encodings
        ws, encoded_implicit_round_functions, explicit_extin_function, explicit_extout_function = \
            get_encoded_implicit_round_funcions(
                unencoded_implicit_affine_layers, unencoded_explicit_affine_layers, args.debug_file,
                SEED, (irf_degree == 3), MAX_DEG_IRF, USE_REDUNDANT_PERTURBATIONS,
                TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE, TRIVIAL_QE,
                PRINT_TIME_GENERATION, PRINT_DEBUG_GENERATION)

    if args.mode == "export":
        from whiteboxarx.export_wb import export_implicit_functions_to_C

        export_implicit_functions_to_C(
            encoded_implicit_round_functions, irf_degree, USE_REDUNDANT_PERTURBATIONS,
            args.debug_file, args.export_file, args.encoding_mode,
            args.first_explicit_round, args.last_explicit_round, PRINT_TIME_GENERATION)

    if args.mode == "eval":
        from whiteboxarx.eval_wb import get_eval_implicit_wb_implementation, bitvectors_to_gf2vector, gf2vector_to_bitvectors
        from whiteboxarx.speck import get_first_and_last_explicit_rounds, speck_instances

        block_size = 2 * ws

        first_explicit_round, last_explicit_round = get_first_and_last_explicit_rounds(
            speck_instances[block_size], args.print_intermediate_values, filename=args.debug_file)

        eval_wb = get_eval_implicit_wb_implementation(
            ws, encoded_implicit_round_functions,
            USE_REDUNDANT_PERTURBATIONS,
            args.print_intermediate_values, args.print_debug_intermediate_values, filename=args.debug_file,
            explicit_extin_function=explicit_extin_function, explicit_extout_function=explicit_extout_function,
            first_explicit_round=first_explicit_round, last_explicit_round=last_explicit_round
        )

        plaintext = tuple(map(lambda p: int(p, 16), args.plaintext))
        print(f"\nEvaluating implicit white-box implementation with input ({plaintext[0]:x}, {plaintext[1]:x})\n")
        plaintext = bitvectors_to_gf2vector(*plaintext, ws)
        ciphertext = eval_wb(plaintext)
        ciphertext = gf2vector_to_bitvectors(ciphertext, ws)
        print(f"\nCiphertext = ({ciphertext[0]:x}, {ciphertext[1]:x})\n")
