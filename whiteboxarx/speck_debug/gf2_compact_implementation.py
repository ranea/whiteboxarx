"""Unprotected implicit implementation of Speck with affine and non-linear layer merged."""
import sage.all

from boolcrypt.utilities import (
    substitute_variables, int2vector, vector2int,
)

from boolcrypt.functionalequations import find_fixed_vars

from whiteboxarx.speck import get_unencoded_implicit_affine_layers


def get_encryption(speck_instance, rounds, master_key):
    """Return an instance of the Speck family."""
    default_rounds = speck_instance.default_rounds
    n = speck_instance.ws
    alpha = speck_instance.alpha

    if rounds is None:
        rounds = default_rounds

    assert 1 <= rounds <= default_rounds

    ws = n

    bpr = sage.all.GF(2)

    def bitvectors_to_gf2vector(x, y):
        return sage.all.vector(bpr, list(int2vector(x, ws)) + list(int2vector(y, ws)))

    def gf2vector_to_bitvectors(v):
        return vector2int(v[:ws]), vector2int(v[ws:])

    implicit_round_functions = get_unencoded_implicit_affine_layers(
        speck_instance, rounds, master_key, return_implicit_round_functions=True)

    bpr_pmodadd = implicit_round_functions[0][0].parent()

    ordered_replacement = []
    assert len(bpr_pmodadd.gens()) == 4*ws
    for i in range(4*ws):
        if i < 2*ws:
            ordered_replacement.append(None)
        else:
            ordered_replacement.append(bpr_pmodadd.gens()[i])

    def RoundFunction(v, round_index):
        implicit_rf = implicit_round_functions[round_index]

        ordered_replacement_copy = ordered_replacement[:]
        for i in range(2*ws):
            ordered_replacement_copy[i] = bpr_pmodadd(v[i])
        system = [substitute_variables(bpr_pmodadd, ordered_replacement_copy, f) for f in implicit_rf]

        fixed_vars, new_equations = find_fixed_vars(
            system, only_linear=True, initial_r_mode="gauss", repeat_with_r_mode=None,
            initial_fixed_vars=None, bpr=bpr_pmodadd, check=False, verbose=False, debug=False, filename=None)

        assert len(new_equations) == 0

        sol = [fixed_vars[ordered_replacement[i]] for i in range(2*ws, 4*ws)]
        v = sage.all.vector(sage.all.GF(2), sol)

        return v

    def RotateRight_Identity(val, right_operand):
        r, width = alpha, n
        mask = 2 ** width - 1
        r = r % width
        return ((val & mask) >> r) | (val << (width - r) & mask), right_operand

    def PermutedBvAdd(x, y):
        return (x + y) % (2 ** n), y

    def SpeckEncryption(x, y):
        x, y = RotateRight_Identity(x, y)
        x, y = PermutedBvAdd(x, y)
        v = bitvectors_to_gf2vector(x, y)

        for i in range(rounds):
            if i not in [rounds - 2, rounds - 1]:
                v = RoundFunction(v, i)
            elif i == rounds - 2:
                v = RoundFunction(v, i)
            else:
                continue

        x, y = gf2vector_to_bitvectors(v)
        return x, y

    return SpeckEncryption


if __name__ == '__main__':
    from whiteboxarx.speck_debug.test_vectors import run_test_vectors
    run_test_vectors(get_encryption, use_rounds_keys=False)
