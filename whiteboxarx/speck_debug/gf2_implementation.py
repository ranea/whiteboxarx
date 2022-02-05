"""Unprotected implicit implementation of Speck without affine and non-linear layer merged."""
from functools import partial

import sage.all

from boolcrypt.utilities import (
    substitute_variables, BooleanPolynomialRing,
    int2vector, vector2int
)

from boolcrypt.functionalequations import find_fixed_vars

from boolcrypt.modularaddition import get_implicit_modadd_anf

from whiteboxarx.speck_debug.test_vectors import get_round_keys, run_test_vectors


def get_encryption(speck_instance, rounds, master_key):
    """Return an instance of the Speck family."""
    default_rounds = speck_instance.default_rounds
    n = speck_instance.ws
    alpha = speck_instance.alpha
    beta = speck_instance.beta

    if rounds is None:
        rounds = default_rounds

    assert 1 <= rounds <= default_rounds

    ws = n
    bpr = sage.all.GF(2)

    identity_matrix = partial(sage.all.identity_matrix, bpr)
    zero_matrix = partial(sage.all.zero_matrix, bpr)

    ra = sage.all.block_matrix(bpr, 2, 2, [
        [zero_matrix(ws - alpha, alpha), identity_matrix(ws - alpha)],
        [identity_matrix(alpha), zero_matrix(alpha, ws - alpha)]])
    lb = sage.all.block_matrix(bpr, 2, 2, [
        [zero_matrix(beta, ws - beta), identity_matrix(beta)],
        [identity_matrix(ws - beta), zero_matrix(ws - beta, beta)]])
    assert ra.is_square() and lb.is_square()

    ii = identity_matrix(ws)
    zz = zero_matrix(ws, ws)

    identity_rotateleft_matrix = sage.all.block_matrix(bpr, 2, 2, [
        [ii, zz],
        [zz, lb]])

    rotateright_identity_matrix = sage.all.block_matrix(bpr, 2, 2, [
        [ra, zz],
        [zz, ii]])

    identity_xor_matrix = sage.all.block_matrix(bpr, 2, 2, [
        [ii, zz],
        [ii, ii]])

    implicit_pmodadd = get_implicit_modadd_anf(ws, permuted=True, only_x_names=True)
    bpr_pmodadd = implicit_pmodadd[0].parent()
    bpr_pmodadd = BooleanPolynomialRing(names=bpr_pmodadd.variable_names(), order="deglex")
    implicit_pmodadd = [bpr_pmodadd(str(f)) for f in implicit_pmodadd]

    ordered_replacement = []
    assert len(bpr_pmodadd.gens()) == 4*ws
    for i in range(4*ws):
        if i < 2*ws:
            ordered_replacement.append(None)
        else:
            ordered_replacement.append(bpr_pmodadd.gens()[i])

    def bitvectors_to_gf2vector(x, y):
        return sage.all.vector(bpr, list(int2vector(x, ws)) + list(int2vector(y, ws)))

    def gf2vector_to_bitvectors(v):
        return vector2int(v[:ws]), vector2int(v[ws:])

    def Identity_RotateLeft(v):
        return identity_rotateleft_matrix * v

    def RotateRight_Identity(v):
        return rotateright_identity_matrix * v

    def PermutedBvAdd(v):
        # system = [f.subs({"x" + str(i): v[i] for i in range(2*ws)}) for f in implicit_pmodadd]
        # solutions = solve_sat(system, n=2)
        # assert len(solutions) == 1, f"{solutions}"
        # sol = solutions[0]
        # sol = [sol[bpr_pmodadd("x" + str(i))] for i in range(2*ws, 4*ws)]
        # v = sage.all.vector(sage.all.GF(2), sol)

        ordered_replacement_copy = ordered_replacement[:]
        for i in range(2*ws):
            ordered_replacement_copy[i] = bpr_pmodadd(v[i])
        system = [substitute_variables(bpr_pmodadd, ordered_replacement_copy, f) for f in implicit_pmodadd]

        # vars = [bpr_pmodadd("x" + str(i)) for i in range(2*ws, 4*ws)]
        # print(get_anf_coeffmatrix_str(system, vars))

        fixed_vars, new_equations = find_fixed_vars(
            system, only_linear=True, initial_r_mode="gauss", repeat_with_r_mode=None,
            initial_fixed_vars=None, bpr=bpr_pmodadd, check=False, verbose=False, debug=False, filename=None)

        assert len(new_equations) == 0

        sol = [fixed_vars[bpr_pmodadd("x" + str(i))] for i in range(2*ws, 4*ws)]
        v = sage.all.vector(sage.all.GF(2), sol)

        return v

    def Identity_Xor(v):
        return identity_xor_matrix * v

    round_keys = get_round_keys(speck_instance, rounds, master_key)

    for i in range(len(round_keys)):
        round_keys[i] = bitvectors_to_gf2vector(round_keys[i], 0)

    def SpeckEncryption(x, y):
        v = bitvectors_to_gf2vector(x, y)
        # assert gf2vector_to_bitvectors(v) == (x, y)
        v = RotateRight_Identity(v)
        v = PermutedBvAdd(v)

        for i in range(rounds):
            if i not in [rounds - 2, rounds - 1]:
                v = v + round_keys[i]
                v = Identity_RotateLeft(v)
                v = Identity_Xor(v)
                v = RotateRight_Identity(v)
                v = PermutedBvAdd(v)
            elif i == rounds - 2:
                v = v + round_keys[i]
                v = Identity_RotateLeft(v)
                v = Identity_Xor(v)
                v = RotateRight_Identity(v)
                v = PermutedBvAdd(v)
                v = v + round_keys[i+1]
                v = Identity_RotateLeft(v)
                v = Identity_Xor(v)
            else:
                continue

        x, y = gf2vector_to_bitvectors(v)
        return x, y

    return SpeckEncryption


if __name__ == '__main__':
    run_test_vectors(get_encryption)
