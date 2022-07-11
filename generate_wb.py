"""Script to generate an implicit white-box implementation of a given ARX cipher"""
import os

import sage.all

from argparse import ArgumentParser


if __name__ == '__main__':
    parser = ArgumentParser(prog="sage -python generate_wb.py", description="Generate an implicit white-box implementation of a given ARX cipher")
    parser.add_argument("--input-file", help="the file containing the implicit (unencoded) and explicit affine layers")
    parser.add_argument("--irf-degree", type=int, choices=[2, 3, 4], help="the degree of the implicit encoded round functions")
    parser.add_argument("--output-file", help="the file to store the implicit encoded round functions and the external excodings")
    #
    parser.add_argument("--seed", type=int, default=0, help="the seed used to generate random values (default: 0)")
    parser.add_argument("--trivial-affine-encodings", action="store_true", help="use trivial affine encodings")
    parser.add_argument("--trivial-quadratic-encodings", action="store_true", help="use trivial quadratic encodings")
    parser.add_argument("--trivial-external-encodings", action="store_true", help="use trivial external encodings")
    parser.add_argument("--trivial-graph-automorphisms", nargs="?", default=False, const=True, choices=["repeat"], help="use trivial graph automorphisms (if set to 'repeat', the same graph automorphism is used for each round)")
    parser.add_argument("--trivial-redundant-perturbations", action="store_true", help="use trivial redundant perturbations")
    parser.add_argument("--disable-redundant-perturbations", action="store_true", help="disable the countermeasure based on redundant perturbations")
    parser.add_argument("--disable-max-degree", action="store_true", help="disable sampling encondings until all implicit encoded round functions have exactly irf-degree")
    parser.add_argument("--print-time-generation", action="store_true", help="print time generation output")
    parser.add_argument("--print-debug-generation", action="store_true", help="print debug information output")
    parser.add_argument("--debug-file", help="the file to store the debug output (default: stdout)")

    args = parser.parse_args()

    assert not os.path.isfile(args.output_file), f"{args.output_file} already exists"
    assert args.debug_file is None or not os.path.isfile(args.debug_file), f"{args.debug_file} already exists"

    unimplicit_encoded_affine_layers, unencoded_explicit_affine_layers = sage.all.load(args.input_file, compress=True)

    SEED = args.seed
    sage.all.set_random_seed(SEED)

    TRIVIAL_AE = args.trivial_affine_encodings
    TRIVIAL_QE = args.trivial_quadratic_encodings
    TRIVIAL_EE = args.trivial_external_encodings
    TRIVIAL_RP = args.trivial_redundant_perturbations
    TRIVIAL_GA = args.trivial_graph_automorphisms
    USE_REDUNDANT_PERTURBATIONS = not args.disable_redundant_perturbations
    MAX_DEG_IRF = not args.disable_max_degree
    PRINT_TIME_GENERATION = args.print_time_generation
    PRINT_DEBUG_GENERATION = args.print_debug_generation

    if not USE_REDUNDANT_PERTURBATIONS:
        assert not TRIVIAL_RP
        TRIVIAL_RP = None

    # degree of the implicit encoded round functions
    irf_degree = args.irf_degree

    if irf_degree == 2:
        from whiteboxarx.implicit_wb_with_affine_encodings import get_implicit_encoded_round_funcions

        # affine encodings
        ws, implicit_encoded_round_functions, explicit_extin_anf, explicit_extout_anf = \
            get_implicit_encoded_round_funcions(
                unimplicit_encoded_affine_layers, args.debug_file,
                SEED, USE_REDUNDANT_PERTURBATIONS,
                TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE,
                PRINT_TIME_GENERATION, PRINT_DEBUG_GENERATION)
    elif irf_degree == 3 or irf_degree == 4:
        from whiteboxarx.implicit_wb_with_quadratic_encodings import get_implicit_encoded_round_funcions

        # quadratic encodings
        ws, implicit_encoded_round_functions, explicit_extin_anf, explicit_extout_anf = \
            get_implicit_encoded_round_funcions(
                unimplicit_encoded_affine_layers, unencoded_explicit_affine_layers, args.debug_file,
                SEED, (irf_degree == 3), MAX_DEG_IRF, USE_REDUNDANT_PERTURBATIONS,
                TRIVIAL_EE, TRIVIAL_GA, TRIVIAL_RP, TRIVIAL_AE, TRIVIAL_QE,
                PRINT_TIME_GENERATION, PRINT_DEBUG_GENERATION)

    sage.all.save((implicit_encoded_round_functions, explicit_extin_anf, explicit_extout_anf), args.output_file, compress=True)
