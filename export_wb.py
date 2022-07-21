"""Script to export the given implicit white-box implementation to C code"""
import functools
import itertools
import math
import os
import warnings

import sage.all

from boolcrypt.utilities import (
    vector2int, get_time, get_smart_print, get_all_symbolic_coeff
)

from argparse import ArgumentParser


def bool_poly2sorted_coeffs(equation, input_variables, output_variables, max_degree, store_sorted_monomials=True):
    """Return a list of coefficients representing a system of binary equations.

    Given a system of equations and an ordering of monomials fixed,
    returns:
     - A list of bitvectors, where the i-th bitvector contains the coefficients
       of the i-th monomial of all the equations
     - The list of monomials sorted following the ordering used.
     - The number of zero coefficients.

     An example of the monomial ordering for a system with input_variables=[x,y,z],
     output_variables=[u, v] and degree=2 is:
      - [1, x, y, z, x*y, x*z, y*z | u, u*x, u*y, u*z | v, v*x, v*y, v*z]

    """
    # coeff2str = lambda x: x  # functools.partial(int2binary, bitsize=bitsize)
    one = equation.parent().one()
    sorted_coeffs = []
    sorted_monomials = []
    num_zero_coeffs = 0

    ct_coeff = equation.constant_coefficient()
    sorted_coeffs.append(ct_coeff)
    if store_sorted_monomials:
        sorted_monomials.append(one)
    num_zero_coeffs += int(ct_coeff == 0)
    # if verbose:
    #     print("ct_coeff:", ct_coeff, sorted_coeffs[-1])

    mon2coeff = get_all_symbolic_coeff(equation, equation.parent().gens())

    # this loops over all quasilinear monomials
    for out_var in [one] + list(output_variables):
        offset_d = 1 if out_var == one else 0
        for input_degree in range(offset_d, max_degree + offset_d):
            for in_mon in itertools.combinations(input_variables, input_degree):
                aux = one
                for term in in_mon:
                    aux *= term
                monomial = out_var * aux
                # coeff = equation.monomial_coefficient(monomial)
                coeff = mon2coeff.get(monomial, 0)
                sorted_coeffs.append(coeff)
                if store_sorted_monomials:
                    sorted_monomials.append(monomial)
                num_zero_coeffs += int(coeff == 0)
                # if verbose:
                #     print(f"monomial / coeff: {monomial} / {coeff} = {sorted_coeffs[-1]}")

    if store_sorted_monomials:
        assert set(equation.monomials()).issubset(set(sorted_monomials))
    # assert len(equation) <= len(sorted_coeffs) == len(sorted_monomials)

    return sorted_coeffs, sorted_monomials, num_zero_coeffs


def component2sorted_coeffs(component, input_variables, max_degree, store_sorted_monomials=True):
    """Return a list of coefficients representing a component of a vectorial Boolean function.

    Given a component and an ordering of monomials fixed, returns:
     - A list of bitvectors, where the i-th bitvector contains the coefficients
       of the i-th monomial of all the equations
     - The list of monomials sorted following the ordering used.
     - The number of zero coefficients.

     An example of the monomial ordering for a component with input_variables=[x,y,z], and degree=3 is:
      - [1, x, y, z, x*y, x*z, y*z, x*y*z]

    """
    # coeff2str = lambda x: x  # functools.partial(int2binary, bitsize=bitsize)
    one = component.parent().one()
    sorted_coeffs = []
    sorted_monomials = []
    num_zero_coeffs = 0

    ct_coeff = component.constant_coefficient()
    sorted_coeffs.append(ct_coeff)
    if store_sorted_monomials:
        sorted_monomials.append(one)
    num_zero_coeffs += int(ct_coeff == 0)
    # if verbose:
    #     print("ct_coeff:", ct_coeff, sorted_coeffs[-1])

    mon2coeff = get_all_symbolic_coeff(component, component.parent().gens())

    for input_degree in range(1, max_degree + 1):
        for in_mon in itertools.combinations(input_variables, input_degree):
            monomial = one
            for term in in_mon:
                monomial *= term
            # coeff = equation.monomial_coefficient(monomial)
            coeff = mon2coeff.get(monomial, 0)
            sorted_coeffs.append(coeff)
            if store_sorted_monomials:
                sorted_monomials.append(monomial)
            num_zero_coeffs += int(coeff == 0)
            # if verbose:
            #     print(f"monomial / coeff: {monomial} / {coeff} = {sorted_coeffs[-1]}")

    if store_sorted_monomials:
        assert set(component.monomials()).issubset(set(sorted_monomials))
    # assert len(equation) <= len(sorted_coeffs) == len(sorted_monomials)

    return sorted_coeffs, sorted_monomials, num_zero_coeffs


def write_integer_with_encoding(my_integer, opened_file_object, encoding_mode=False):
    r"""Writes an integer between 0 and 255 as a byte into the given file object
    using binary or hexadecimal encoding for C literal strings.

    encoding_mode can be "hex", "bin", and "bin_zero"

    In the "hex" encoding, the integer is converted to a C hex escape sequence
    and printed to the file.
    A hex escape sequence is a C string literal that have at least one hex digit following \x,
    with no upper bound; it continues for as many hex digits as there are.

    In the "bin" encoding, the integers corresponding to `"`, `\`, and the newline
    characters `\n` and `\r` are converted to characters, prepended
    with "\" (to escape these values), and printed to the file.
    The rest of the integers in the internal [0, 255] are converted to bytes are
    written to the file in binary mode.
    The values are escaped so that the they can be used within a C literal string.

    The "bin_zero" encoding is similar to "bin" but the integer 0
    is converted `\000` to avoid the null warning character
    if the output file is compiled with gcc.

    See also:
    - https://en.wikipedia.org/wiki/Escape_sequences_in_C#Table_of_escape_sequences
    - https://en.cppreference.com/w/c/language/string_literal
    - https://en.cppreference.com/w/c/language/escape
    """
    if encoding_mode == "hex":
        replacements = {i: f"\\x{i:0x}" for i in range(256)}
    elif encoding_mode == "bin_zero":
        replacements = {
            0x00: r'\000',  # (avoid warning null character)
            # 0x07: r'\a',
            # 0x08: r'\b',
            # 0x1B: r'\e',
            # 0x0C: r'\f',
            0x0A: r'\n',  # needed
            0x0D: r'\r',  # needed
            # 0x09: r'\t',
            # 0x0B: r'\v',
            0x5C: r'\\',  # needed
            # 0x27: r'\'',
            0x22: r'\"',  # needed
            0x3F: r'\?',  # optionally, to avoid trigraph pragma
        }
    elif encoding_mode == "bin":
        replacements = {
            0x0A: r'\n',  # needed
            0x0D: r'\r',  # needed
            0x5C: r'\\',  # needed
            0x22: r'\"',  # needed
            0x3F: r'\?',  # avoid trigraph pragma
        }
    else:
        raise ValueError("invalid encoding_mode")

    my_integer = int(my_integer)

    assert 0 <= my_integer <= 255

    if opened_file_object is None:
        aux_write_foo = functools.partial(print, end="")
    else:
        aux_write_foo = opened_file_object.write

    if my_integer in replacements:
        aux_write_foo(replacements[my_integer].encode('ascii'))
    else:
        # byteorder must be given (even for length 1)
        aux_write_foo(my_integer.to_bytes(length=1, byteorder='big', signed=False))


def export_implicit_functions_to_C(
        implicit_encoded_round_functions, max_degree, use_redundant_perturbations,
        filename_C_info, filename_C_array, encoding_mode,
        first_explicit_round, last_explicit_round,
        explicit_extin_anf=None, explicit_extout_anf=None,
        print_time_generation=False):
    if not use_redundant_perturbations:
        bpr_pmodadd = implicit_encoded_round_functions[0][0].parent()  # round 0, component Boolean function 0
    else:
        bpr_pmodadd = implicit_encoded_round_functions[0][0][0].parent()  # round 0, perturbed system 0, component Boolean function 0

    ws = len(bpr_pmodadd.gens()) // 4

    smart_print_C_info = get_smart_print(filename_C_info)
    smart_print_C_array_header = get_smart_print(filename_C_array)

    if not use_redundant_perturbations:
        num_boolean_systems_per_round = 1
        num_eqs_per_system = len(implicit_encoded_round_functions[0])
        assert all(num_eqs_per_system == len(implicit_encoded_round_functions[i]) for i in range(len(implicit_encoded_round_functions)))
    else:
        num_boolean_systems_per_round = 4
        num_eqs_per_system = len(implicit_encoded_round_functions[0][0])
        for j in range(4):
            for i in range(len(implicit_encoded_round_functions)):
                assert num_eqs_per_system == len(implicit_encoded_round_functions[i][j])
    assert num_eqs_per_system == 2*ws  # num eqs per system

    input_vars = bpr_pmodadd.gens()[:2*ws]
    output_vars = bpr_pmodadd.gens()[2*ws:]
    num_words_per_monomial = int(math.ceil(num_eqs_per_system / 8))

    if filename_C_info is None:
        smart_print_C_info("")
    smart_print_C_info(f"// number of implicit round functions (IRF): {len(implicit_encoded_round_functions)}")
    smart_print_C_info(f"// number of {'' if use_redundant_perturbations else 'non-'}perturbed system of each IRF: {num_boolean_systems_per_round}")
    smart_print_C_info(f"// number of equations in each {'' if use_redundant_perturbations else 'non-'}perturbed system: {num_eqs_per_system}")
    smart_print_C_info(f"// algebraic degree of all equations: {max_degree}")
    smart_print_C_info(f"// input variables of all equations (total={len(input_vars)}): {input_vars}")
    smart_print_C_info(f"// output variables of all equations (total={len(output_vars)}): {output_vars}")
    smart_print_C_info(f"// number of words per monomial: {num_words_per_monomial}")

    # word types for input/output variables
    WORD_TYPE = {4: "uint8_t", 16: "uint16_t", 32: "uint32_t", 64: "uint64_t"}
    WORD_IN_TYPE = {4: "SCNx8", 16: "SCNx16", 32: "SCNx32", 64: "SCNx64"}
    WORD_OUT_TYPE = {4: "PRIx8", 16: "PRIx16", 32: "PRIx32", 64: "PRIx64"}
    WORD_CONSTANT_TYPE = {4: "UINT8_C", 16: "UINT16_C", 32: "UINT32_C", 64: "UINT64_C"}

    smart_print_C_array_header(f"#define USE_REDUNDANT_PERTURBATIONS {int(use_redundant_perturbations)}")
    smart_print_C_array_header(f"#define MAX_DEGREE {max_degree}")
    smart_print_C_array_header(f"#define ROUNDS {len(implicit_encoded_round_functions)}")
    smart_print_C_array_header(f"#define WORD_SIZE {ws}")
    smart_print_C_array_header(f"#define WORD_TYPE {WORD_TYPE[ws]}")
    smart_print_C_array_header(f"#define WORD_IN_TYPE {WORD_IN_TYPE[ws]}")
    smart_print_C_array_header(f"#define WORD_OUT_TYPE {WORD_OUT_TYPE[ws]}")
    smart_print_C_array_header(f"#define WORD_CONSTANT_TYPE {WORD_CONSTANT_TYPE[ws]}")
    smart_print_C_array_header(f"#define WORD_MASK WORD_CONSTANT_TYPE({2 ** ws - 1})")

    smart_print_C_array_header(f"#define MONOMIAL_WORD_TYPE uint8_t")
    smart_print_C_array_header(f"#define MONOMIAL_WORD_SIZE 8")

    smart_print_C_array_header(f"#define FIRST_EXPLICIT_ROUND(x, y) {first_explicit_round}")
    smart_print_C_array_header(f"#define LAST_EXPLICIT_ROUND(x, y) {last_explicit_round}")

    list_zero = [0]*(num_eqs_per_system - 1)
    sorted_monomials = None

    for round_index in range(len(implicit_encoded_round_functions)):
        if not use_redundant_perturbations:
            boolean_systems_in_round_i = [implicit_encoded_round_functions[round_index]]
            assert len(boolean_systems_in_round_i) == 1
        else:
            boolean_systems_in_round_i = implicit_encoded_round_functions[round_index]
            assert len(boolean_systems_in_round_i) == 4

        total_num_zero_coeffs = 0

        for _, boolean_system in enumerate(boolean_systems_in_round_i):
            assert len(boolean_system) == 2*ws == num_eqs_per_system
            list_sorted_coeffs = None

            for index_eq, eq in enumerate(boolean_system):
                sorted_coeffs, new_sorted_monomials, num_zero_coeffs = bool_poly2sorted_coeffs(
                    eq, input_vars, output_vars, max_degree, store_sorted_monomials=sorted_monomials is None)

                total_num_zero_coeffs += num_zero_coeffs

                if sorted_monomials is None:
                    sorted_monomials = new_sorted_monomials
                    total_number_monomials = len(sorted_monomials) * num_boolean_systems_per_round * len(implicit_encoded_round_functions)
                    total_number_monomial_words = total_number_monomials * num_words_per_monomial

                    smart_print_C_info(f"// monomial ordering used (total={len(sorted_monomials)}): {sorted_monomials}")
                    smart_print_C_info(f"// total number of monomials = {total_number_monomials} = "
                                       f"({len(sorted_monomials)} monomials) x ({num_boolean_systems_per_round} num_boolean_systems_per_round)"
                                       f" x ({len(implicit_encoded_round_functions)} IRF)")
                    smart_print_C_info(f"// total number of monomial words = {total_number_monomial_words} = "
                                       f"({total_number_monomials} total_number_monomials) x ({num_words_per_monomial} num_words_per_monomial)\n")

                    smart_print_C_array_header(f"#define MONOMIALS {len(sorted_monomials)}\n")
                    smart_print_C_array_header(f'const MONOMIAL_WORD_TYPE* COEFFS = "', end="")

                    # ensure smart_print_C_array_header is not used more
                    del smart_print_C_array_header
                    if filename_C_array is None:
                        warnings.warn("printing C array to standard output")
                        fileobject_C_array = None
                    else:
                        fileobject_C_array = open(filename_C_array, "ab")

                if list_sorted_coeffs is None:
                    assert index_eq == 0
                    list_sorted_coeffs = [[coeff] + list_zero.copy() for coeff in sorted_coeffs]
                else:
                    assert len(sorted_coeffs) == len(sorted_monomials)
                    for index_mon in range(len(sorted_monomials)):
                        list_sorted_coeffs[index_mon][index_eq] = sorted_coeffs[index_mon]

            for index_mon in range(len(sorted_monomials)):
                coeffs = list_sorted_coeffs[index_mon]
                # coeffs[j] is the bit value of the `index_mon`-th monomial for the j-th equation

                for i in range(0, len(coeffs), 8):
                    small_integer = vector2int(coeffs[i:i + 8])  # in [0, 255]
                    # print(coeffs, vector2int(coeffs[i:i + 8]), single_byte,
                    #       single_byte.decode('ascii') if int.from_bytes(single_byte, 'big') < 128 else None)
                    write_integer_with_encoding(small_integer, opened_file_object=fileobject_C_array, encoding_mode=encoding_mode)

        if print_time_generation:
            smart_print_C_info(f"\n{get_time()} | exported {round_index}-th implicit round function with num zero coefficients {total_num_zero_coeffs}")

    if fileobject_C_array is not None:
        fileobject_C_array.close()

    get_smart_print(filename_C_array)('";')

    # - external encodings

    if explicit_extin_anf is None or explicit_extout_anf is None:
        return

    assert explicit_extin_anf is not None and explicit_extout_anf is not None
    assert len(explicit_extin_anf) == 2 * ws == num_eqs_per_system
    assert len(explicit_extout_anf) == 2 * ws == num_eqs_per_system

    deg_extin = max(f.degree() for f in explicit_extin_anf)
    deg_extout = max(f.degree() for f in explicit_extout_anf)

    smart_print_C_info(f"\n\n\n// external input and output encodings:")
    smart_print_C_info(f"//     number of components: {num_eqs_per_system}")
    smart_print_C_info(f"//     algebraic degree: {deg_extin}, {deg_extout}")
    smart_print_C_info(f"//     input variables (total={len(input_vars)}): {input_vars}")
    smart_print_C_info(f"//     number of words per monomial: {num_words_per_monomial}\n")

    for my_anf, my_deg, my_name in zip([explicit_extin_anf, explicit_extout_anf], [deg_extin, deg_extout], ["extin", "extout"]):
        list_sorted_coeffs = None
        sorted_monomials = None
        smart_print_C_array_header = get_smart_print(filename_C_array)

        for index_component, component in enumerate(my_anf):
            sorted_coeffs, new_sorted_monomials, _ = component2sorted_coeffs(
                component, input_vars, my_deg, store_sorted_monomials=sorted_monomials is None)

            if sorted_monomials is None:
                sorted_monomials = new_sorted_monomials

                smart_print_C_info(f"\n//     {my_name} monomial ordering used (total={len(sorted_monomials)}): {sorted_monomials}")

                smart_print_C_array_header(f"\n#define MONOMIALS_{my_name.upper()} {len(sorted_monomials)}")
                smart_print_C_array_header(f"#define MAX_DEGREE_{my_name.upper()} {my_deg}\n")
                smart_print_C_array_header(f'const MONOMIAL_WORD_TYPE* COEFFS_{my_name.upper()} = "', end="")

                # ensure smart_print_C_array_header is not used more
                del smart_print_C_array_header
                if filename_C_array is None:
                    warnings.warn("printing C array to standard output")
                    fileobject_C_array = None
                else:
                    fileobject_C_array = open(filename_C_array, "ab")

            if list_sorted_coeffs is None:
                assert index_component == 0
                list_sorted_coeffs = [[coeff] + list_zero.copy() for coeff in sorted_coeffs]
            else:
                assert len(sorted_coeffs) == len(sorted_monomials)
                for index_mon in range(len(sorted_monomials)):
                    list_sorted_coeffs[index_mon][index_component] = sorted_coeffs[index_mon]

        for index_mon in range(len(sorted_monomials)):
            coeffs = list_sorted_coeffs[index_mon]
            # coeffs[j] is the bit value of the `index_mon`-th monomial for the j-th component

            for i in range(0, len(coeffs), 8):
                small_integer = vector2int(coeffs[i:i + 8])  # in [0, 255]
                # print(coeffs, vector2int(coeffs[i:i + 8]), single_byte,
                #       single_byte.decode('ascii') if int.from_bytes(single_byte, 'big') < 128 else None)
                write_integer_with_encoding(small_integer, opened_file_object=fileobject_C_array,
                                            encoding_mode=encoding_mode)

        if print_time_generation:
            smart_print_C_info(
                f"\n{get_time()} | exported explicit {my_name} encoding implicit")

        if fileobject_C_array is not None:
            fileobject_C_array.close()

        get_smart_print(filename_C_array)('";\n')


if __name__ == '__main__':
    parser = ArgumentParser(prog="sage -python export_wb.py", description="Export the given implicit white-box implementation to C code")
    parser.add_argument("--input-file", help="the file containing the implicit encoded round functions and the external encodings")
    parser.add_argument("--irf-degree", type=int, choices=[2, 3, 4], help="the degree of the implicit encoded round functions")
    #
    parser.add_argument("--output-file", default="white_box_backend.c", help="the file to store the exported C code")
    parser.add_argument("--cancel-external-encodings", action="store_true", help="cancel the external encodings to evaluate unencoded plaintexts and to obtain unencoded ciphertexts")
    parser.add_argument("--disabled-redundant-perturbations", action="store_true", help="assume the implicit encoded round functions do NOT contain redundant perturbations")
    parser.add_argument("--encoding-mode", default="bin", choices=["hex", "bin", "bin_zero"], help="the coefficient encoding of the implicit round functions in the exported C code (default: %(default)s)")
    parser.add_argument("--first-explicit-round", default="", help="the C code describing the first explicit round not included in the implicit round functions")
    parser.add_argument("--last-explicit-round", default="", help="the C code describing the last explicit round  not included in the implicit round functions")
    parser.add_argument("--print-time-generation", action="store_true", help="print time generation output")
    parser.add_argument("--debug-file", help="the file to store the debug output (default: stdout)")

    args = parser.parse_args()

    assert not os.path.isfile(args.output_file), f"{args.output_file} already exists"
    assert args.debug_file is None or not os.path.isfile(args.debug_file), f"{args.debug_file} already exists"

    implicit_encoded_round_functions, explicit_extin_anf, explicit_extout_anf = sage.all.load(args.input_file, compress=True)

    # degree of the implicit encoded round functions
    irf_degree = args.irf_degree

    USE_REDUNDANT_PERTURBATIONS = not args.disabled_redundant_perturbations
    PRINT_TIME_GENERATION = args.print_time_generation

    if not USE_REDUNDANT_PERTURBATIONS:
        bpr_pmodadd = implicit_encoded_round_functions[0][0].parent()  # round 0, component Boolean function 0
    else:
        bpr_pmodadd = implicit_encoded_round_functions[0][0][0].parent()  # round 0, perturbed system 0, component Boolean function 0

    ws = len(bpr_pmodadd.gens()) // 4

    if not args.cancel_external_encodings:
        explicit_extin_anf, explicit_extout_anf = None, None

    export_implicit_functions_to_C(
        implicit_encoded_round_functions, irf_degree, USE_REDUNDANT_PERTURBATIONS,
        args.debug_file, args.output_file, args.encoding_mode,
        args.first_explicit_round, args.last_explicit_round,
        explicit_extin_anf=explicit_extin_anf, explicit_extout_anf=explicit_extout_anf,
        print_time_generation=PRINT_TIME_GENERATION
    )
