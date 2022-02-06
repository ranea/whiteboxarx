import os

import implicit_wb_with_affine_encodings
import implicit_wb_with_quadratic_encodings

import C_exporting

import speck

import sage.all


if __name__ == '__main__':
    # ----- Speck generation of unencoded_implicit_affine_layers -----

    # Speck initial parameters
    use_test_vector_key = True
    # speck_instance = speck.Speck_8_16
    speck_instance = speck.Speck_32_64
    # speck_instance = speck.Speck_64_128
    # speck_instance = speck.Speck_128_256

    ws = speck_instance.ws
    rounds = speck_instance.default_rounds
    if use_test_vector_key:
        if speck_instance == speck.Speck_8_16:
            master_key = (1, 2, 3, 4)
        elif speck_instance == speck.Speck_32_64:
            master_key = (0x1918, 0x1110, 0x0908, 0x0100)
        elif speck_instance == speck.Speck_64_128:
            master_key = (0x1b1a1918, 0x13121110, 0x0b0a0908, 0x03020100)
        elif speck_instance == speck.Speck_128_256:
            master_key = (0x1f1e1d1c1b1a1918, 0x1716151413121110, 0x0f0e0d0c0b0a0908, 0x0706050403020100)
        else:
            assert False
    else:
        master_key = [sage.all.ZZ.random_element(0, 2**ws) for _ in range(4)]

    unencoded_implicit_affine_layers, _ = speck.get_unencoded_implicit_affine_layers(speck_instance, rounds, master_key)

    # ----- non-Speck initial parameters -----

    from implicit_wb_with_affine_encodings import (
        USE_REDUNDANT_PERTURBATIONS, PRINT_TIME_GENERATION, TRIVIAL_EE, PRINT_INTERMEDIATE_VALUES
    )

    # degree of the encoded implicit round functions
    irf_degree = 2  # 2, 3, 4

    export_to_C = False
    if export_to_C:
        encoding_mode = "bin"  # "hex", "bin", "bin_zero"
    else:
        encoding_mode = None

    filename_debug = None
    filename_c_info = None
    filename_c_array = None

    """
    filename_debug = f"intermediate_values_{speck_instance.name.lower()}_irfdeg{degree}_{encoding_mode}.txt"
    filename_c_info = f"equations_info_{speck_instance.name.lower()}_irfdeg{degree}_{encoding_mode}.txt"
    filename_c_array = f"equations_{speck_instance.name.lower()}_irfdeg{degree}_{encoding_mode}.c"
    for fn in [filename_debug, filename_c_info, filename_c_array]:
        assert not os.path.isfile(fn), f"{fn} already exists"
    """

    # ----- generation of white-box implementation -----

    if irf_degree == 2:
        # affine encodings
        get_encoded_implicit_round_funcions = implicit_wb_with_affine_encodings.get_encoded_implicit_round_funcions
    elif irf_degree in [3, 4]:
        # quadratic encodings
        assert (irf_degree == 3) == implicit_wb_with_quadratic_encodings.CUBIC_MODE
        get_encoded_implicit_round_funcions = implicit_wb_with_quadratic_encodings.get_encoded_implicit_round_funcions
    else:
        raise ValueError("invalid irf_degree")

    encoded_implicit_round_functions, explicit_extin_function, explicit_extout_function = \
        get_encoded_implicit_round_funcions(ws, unencoded_implicit_affine_layers, filename=filename_debug)

    # # debug
    # for i in range(len(encoded_implicit_round_functions)):
    #     print(f"round {i}:")
    #     for j in range(len(encoded_implicit_round_functions[i])):
    #         print(f"encoded_implicit_round_functions[round={i}][component={j}]:", encoded_implicit_round_functions[i][j])

    if export_to_C:
        C_exporting.export_implicit_functions_to_C(
            ws, encoded_implicit_round_functions, irf_degree, USE_REDUNDANT_PERTURBATIONS,
            filename_c_info, filename_c_array, encoding_mode, PRINT_TIME_GENERATION)
    else:
        first_explicit_round, last_explicit_round = speck.get_first_and_last_explicit_rounds(
            speck_instance, PRINT_INTERMEDIATE_VALUES, filename=filename_debug)

        if not use_test_vector_key:
            # explicit_*_function cancel the input/output external encodings (to get same output as unencoded test vectors)
            explicit_extin_function = None
            explicit_extout_function = None

        eval_wb = implicit_wb_with_affine_encodings.get_eval_implicit_wb_implementation(
            ws, encoded_implicit_round_functions, filename=filename_debug,
            explicit_extin_function=explicit_extin_function, explicit_extout_function=explicit_extout_function,
            first_explicit_round=first_explicit_round, last_explicit_round=last_explicit_round
        )

        # example evaluation
        plaintext = sage.all.vector(sage.all.GF(2), [0]*(2*ws))
        print(f"\nEvaluating implicit white-box implementation with input {plaintext}\n")
        ciphertext = eval_wb(plaintext)
        print(f"\nCiphertext = {ciphertext}\n")

        # Speck-specific code for test vectors
        if use_test_vector_key:
            if speck_instance == speck.Speck_8_16:
                plaintext = (1, 2)
            elif speck_instance == speck.Speck_32_64:
                plaintext = (0x6574, 0x694c)
            elif speck_instance == speck.Speck_64_128:
                plaintext = (0x3b726574, 0x7475432d)
            elif speck_instance == speck.Speck_128_256:
                plaintext = (0x65736f6874206e49, 0x202e72656e6f6f70)
            plaintext = speck.bitvectors_to_gf2vector(*plaintext, ws)
            ciphertext = eval_wb(plaintext)
            ciphertext = speck.gf2vector_to_bitvectors(ciphertext, ws)
            if TRIVIAL_EE or (explicit_extin_function is not None and explicit_extout_function is not None):
                if speck_instance == speck.Speck_8_16:
                    assert ciphertext == (4, 8), f"{ciphertext}"
                elif speck_instance == speck.Speck_32_64:
                    assert ciphertext == (0xa868, 0x42f2), f"{ciphertext}"
                elif speck_instance == speck.Speck_64_128:
                    assert ciphertext == (0x8c6fa548, 0x454e028b), f"{ciphertext}"
                elif speck_instance == speck.Speck_128_256:
                    assert ciphertext == (0x4109010405c0f53e, 0x4eeeb48d9c188f43), f"{ciphertext}"
