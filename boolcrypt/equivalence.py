"""Find whether two functions are linear/affine equivalent and
count the number of linear/affine self-equivalences.

For equivalence-based functions solved via a functional equation
with a SAT solver, see functionalequation.py
"""
import math

from boolcrypt.utilities import (
    get_lut_inversion, int2vector, get_time, get_bitsize, lut2matrix, get_algebraic_degree,
    matrix2lut, compose_lut, is_invertible, invert_lut, substitute_anf, matrix2anf
)

import sage.all

GF = sage.all.GF


# ------------
# equivalences
# ------------


@sage.all.cached_function(key=lambda x: tuple(x))
def get_linear_repr(lut):
    """Return the linear representative of the given LUT.

    For 8-bit functions or bigger, it can take more than 1 minute.

        >>> get_linear_repr([0, 1, 2, 3, 4, 5, 6, 7])
        [0, 1, 2, 3, 4, 5, 6, 7]
        >>> get_linear_repr(get_lut_inversion(4))
        [0, 1, 2, 3, 4, 6, 8, 11, 5, 14, 15, 7, 12, 10, 13, 9]
        >>> get_linear_repr(get_lut_inversion(5))  # doctest: +NORMALIZE_WHITESPACE
        [0, 1, 2, 4, 3, 8, 16, 14, 5, 9, 21, 24, 30, 26, 17, 13, 6,
        27, 18, 28, 31, 7, 23, 29, 19, 22, 25, 10, 11, 20, 15, 12]
        >>> get_linear_repr(get_lut_inversion(6))[:32]  # doctest: +NORMALIZE_WHITESPACE, +SKIP
        [0, 1, 2, 3, 4, 8, 13, 16, 5, 30, 32, 20, 58, 40, 33, 11, 6,
        48, 38, 53, 49, 24, 31, 9, 12, 29, 55, 43, 62, 46, 28, 17]
        >>> get_linear_repr(get_lut_inversion(7))[:32]  # doctest: +NORMALIZE_WHITESPACE, +SKIP
        [0, 1, 2, 4, 3, 8, 16, 32, 5, 9, 64, 56, 95, 97, 29, 116, 6,
        96, 18, 60, 125, 89, 66, 122, 115, 43, 106, 36, 91, 124, 21, 113]

    """
    if get_algebraic_degree(lut) == 1 and lut[0] == 0:
        return list(range(2 ** get_bitsize(lut)))

    if get_bitsize(lut) >= 16:
        raise ValueError("lut with bitsize {}>=16 not supported".format(get_bitsize(lut)))

    assert isinstance(lut, list)
    assert isinstance(lut[0], int)

    from sboxU import le_class_representative
    return le_class_representative(lut)


# -----------------
# self-equivalences
# -----------------


def has_affine_but_no_linear_se(lut, verbose=False, number_self_ae=None, len_common_reprs=None):
    """Check whether the permutation has affine but no linear self equivalences.

        >>> lut = get_lut_inversion(3)
        >>> has_affine_but_no_linear_se(lut) is None
        True
        >>> new_lut = [0 ^ lut[i ^ 1] for i in range(len(lut))]
        >>> has_affine_but_no_linear_se(new_lut) is None
        True
        >>> from boolcrypt.sboxes import high_se_4bit_sboxes
        >>> has_affine_but_no_linear_se(high_se_4bit_sboxes[-1])
        True

    """
    n = int(math.log(len(lut), 2))

    # ----- first test -----
    if number_self_ae is None:
        number_self_ae = get_number_self_ae(lut)
    if number_self_ae == 0:
        return False
    if not sage.all.Integer(number_self_ae).divides(sage.all.GL(n, GF(2)).cardinality()):
        if verbose:
            print("number of self-equivalences is not a divisor of |GL|")
        return True

    # ----- second test -----
    if len_common_reprs is None:
        len_common_reprs = len(get_common_linear_reprs(lut))
    if len_common_reprs == 1:
        return True

    return None


def get_common_linear_reprs(lut, verbose=False, debug=False):
    """Return the common linear representatives between F(x + c) and F(x) + d.

    It return a dictionary with entries lr -> (left_cts, right_cts) where
     - lr is a linear representative
     - left_cts are those constants c such that c + F has representative lr
     - right_cts are those constants c such that F(x + c) has representative lr

     If for some lr, left_cts or right_cts is empty, lr is not included in the dictionary.

        >>> lut = get_lut_inversion(4)
        >>> get_common_linear_reprs(lut, verbose=True)
        for i in (0,), i + F(x) is linear equivalent to F(x + 0)
        {(0, 1, 2, 3, 4, 6, 8, 11, 5, 14, 15, 7, 12, 10, 13, 9): ((0,), (0,))}
        >>> get_common_linear_reprs([0 ^ lut[i ^ 1] for i in range(len(lut))])  # doctest: +NORMALIZE_WHITESPACE
        {(1, 0, 2, 3, 4, 6, 8, 11, 5, 13, 7, 12, 9, 15, 14, 10):
        ((0,), (0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15))}
        >>> get_common_linear_reprs([1 ^ lut[i ^ 0] for i in range(len(lut))])  # doctest: +NORMALIZE_WHITESPACE
        {(1, 0, 2, 3, 4, 6, 8, 11, 5, 12, 7, 13, 14, 9, 10, 15):
        ((0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15), (0,))}
        >>> get_common_linear_reprs([2 ^ lut[i ^ 5] for i in range(len(lut))])  # doctest: +NORMALIZE_WHITESPACE
        {(1, 0, 2, 4, 3, 5, 8, 15, 6, 10, 11, 14, 13, 9, 12, 7): ((0, 1, 5, 15), (0, 1, 3, 11)),
        (1, 0, 2, 4, 3, 6, 8, 15, 5, 13, 7, 10, 14, 12, 11, 9): ((3, 7, 8, 12), (4, 7, 13, 14)),
        (1, 0, 2, 4, 3, 6, 8, 12, 5, 14, 13, 15, 10, 7, 9, 11): ((4, 10, 11, 14), (2, 8, 9, 10)),
        (1, 0, 2, 3, 4, 6, 8, 11, 5, 14, 7, 15, 13, 10, 9, 12): ((6, 13), (6, 15)),
        (0, 1, 2, 3, 4, 6, 8, 11, 5, 12, 13, 7, 15, 9, 14, 10): ((9,), (12,))}

    """
    left_reprs = dict()  # \oplus_ct \circ f
    for ct in range(len(lut)):
        if verbose and debug:
            print("{} | computing representative of {} + F(x)".format(get_time(), ct))
        ct_lut = tuple(get_linear_repr([ct ^ lut[i] for i in range(len(lut))]))
        left_reprs[ct_lut] = tuple(left_reprs.get(ct_lut, ()) + (ct,))

    leftct2rightct = dict()
    for ct in range(len(lut)):  # f \circ \oplus_c
        if verbose and debug:
            print("{} | computing representative of F(x + {})".format(get_time(), ct))
        lut_ct = tuple(get_linear_repr([lut[ct ^ i] for i in range(len(lut))]))
        left_cts = left_reprs.get(lut_ct, None)
        if left_cts is not None:
            if verbose:
                print("for i in {}, i + F(x) is linear equivalent to F(x + {})".format(left_cts, ct))
            leftct2rightct[left_cts] = tuple(leftct2rightct.get(left_cts, ()) + (ct,))

    repr2match = dict()
    for linear_repr in left_reprs:
        alphas = left_reprs[linear_repr]
        betas = leftct2rightct.get(alphas, None)
        if betas is not None:
            repr2match[linear_repr] = (alphas, betas)

    return repr2match


def get_number_self_le(lut):
    """Return the number of self linear equivalences.

        >>> get_number_self_le([0, 1, 2, 3])
        6
        >>> get_number_self_le(get_lut_inversion(4))
        60
        >>> from sage.crypto.sboxes import PRESENT
        >>> get_number_self_le(list(PRESENT))
        1
        >>> get_number_self_le(get_lut_inversion(7))
        889
        >>> get_number_self_le(get_lut_inversion(8))
        2040
        >>> from sage.crypto.sboxes import AES
        >>> get_number_self_le(list(AES))
        8

    """
    bitsize = get_bitsize(lut)

    if get_algebraic_degree(lut) == 1 and lut[0] == 0:
        return sage.all.GL(bitsize, GF(2)).cardinality()

    if get_bitsize(lut) >= 16:
        raise ValueError("lut with bitsize {}>=16 not supported".format(get_bitsize(lut)))

    assert isinstance(lut, list)
    assert isinstance(lut[0], int)

    from sboxU import number_linear_equivalences
    return number_linear_equivalences(lut, lut)


def get_number_self_ae(lut, common_reprs=None, verbose=False, debug=False):
    """Return the number of affine self-equivalences.

    For 8-bit functions or bigger, it can take more than 1 minute.

        >>> get_number_self_ae([0, 1, 2, 3])
        24
        >>> get_number_self_ae(get_lut_inversion(4))
        60
        >>> from sage.crypto.sboxes import PRESENT
        >>> get_number_self_ae(list(PRESENT))
        4
        >>> get_number_self_ae(get_lut_inversion(7))  # doctest: +SKIP
        889
        >>> from sage.crypto.sboxes import AES
        >>> get_number_self_ae(list(AES))  # doctest: +SKIP
        2040

    """
    if common_reprs is None:
        common_reprs = get_common_linear_reprs(lut, verbose, debug)
    number_self_ae = 0

    for linear_repr, (alphas, betas) in common_reprs.items():
        self_le = get_number_self_le(list(linear_repr))
        if verbose:
            print(linear_repr, "has", self_le, "self LE and matches", (alphas, betas))
        number_self_ae += self_le * len(alphas) * len(betas)

    return number_self_ae


def get_all_self_le(lut, return_matrices=False):
    """Return all the linear self-equivalences as pairs of LUTs or GF(2)-matrices.

        >>> get_all_self_le([0, 1, 2, 3])[-1]
        [[0, 3, 2, 1], [0, 3, 2, 1]]
        >>> right, left = get_all_self_le([0, 1, 2, 3], return_matrices=True)[-1]
        >>> sage.all.block_matrix(1, 2, [right, left])
        [1 0|1 0]
        [1 1|1 1]
        >>> matrix2lut(right), matrix2lut(left)
        ([0, 3, 2, 1], [0, 3, 2, 1])
        >>> right, left = get_all_self_le(get_lut_inversion(4), return_matrices=True)[-1]
        >>> sage.all.block_matrix(1, 2, [right, left])
        [1 1 1 1|1 1 1 1]
        [1 0 0 0|1 0 0 0]
        [1 1 0 0|1 1 0 0]
        [1 1 1 0|1 1 1 0]
        >>> from sage.crypto.sboxes import AES
        >>> sage.all.block_matrix(1, 2, get_all_self_le(list(AES), return_matrices=True)[-1])  # doctest: +SKIP
        [0 1 0 0 0 1 1 1|1 1 0 0 1 1 0 1]
        [0 0 1 1 0 0 1 1|1 0 1 1 0 1 1 1]
        [0 1 1 1 0 0 1 1|0 1 0 1 1 0 1 1]
        [0 0 0 1 0 0 0 0|1 0 0 1 1 0 1 1]
        [0 0 1 1 0 1 1 0|0 0 1 1 1 0 0 0]
        [1 1 0 0 0 0 1 1|0 1 0 0 1 0 0 0]
        [1 0 0 0 1 1 0 0|1 1 0 0 0 1 0 1]
        [0 1 1 1 1 0 0 0|1 1 1 0 0 1 1 1]

    """
    bitsize = get_bitsize(lut)

    if get_bitsize(lut) >= 4 and get_algebraic_degree(lut) == 1:
        raise ValueError("linear lut with bitsize {}>=4 not supported".format(bitsize))

    if get_bitsize(lut) >= 16:
        raise ValueError("lut with bitsize {}>=16 not supported".format(bitsize))

    assert isinstance(lut, list)
    assert isinstance(lut[0], int)

    from sboxU import all_linear_equivalences_fast
    result = all_linear_equivalences_fast(lut, lut)
    if len(result) == 0:
        return []
    elif return_matrices:
        return [[lut2matrix(result[i]), lut2matrix(result[i+1])] for i in range(0, len(result), 2)]
    else:
        return [[result[i], result[i+1]] for i in range(0, len(result), 2)]


def get_all_self_ae(lut, return_lut=False, verbose=False, debug=False):
    """Return all the affine self-equivalences as LUTS or (matrix, vector) pairs.

        >>> get_all_self_ae([0, 1, 2, 3], return_lut=True)[-1]
        [[3, 1, 2, 0], [3, 1, 2, 0]]
        >>> right, left = get_all_self_ae([0, 1, 2, 3])[-1]
        >>> to_m = sage.all.matrix
        >>> sage.all.block_matrix(2, 2, [right[0], left[0], to_m(right[1]), to_m(left[1])])
        [0 1|0 1]
        [1 0|1 0]
        [---+---]
        [1 1|1 1]
        >>> right, left = get_all_self_ae([0, 1, 2, 3])[-1]
        >>> sage.all.block_matrix(2, 2, [right[0], left[0], to_m(right[1]), to_m(left[1])])
        [0 1|0 1]
        [1 0|1 0]
        [---+---]
        [1 1|1 1]
        >>> from sage.crypto.sboxes import PRESENT
        >>> self_ae = get_all_self_ae(list(PRESENT))
        >>> for r, l in self_ae: print(sage.all.block_matrix(2, 2, [r[0], l[0], to_m(r[1]), to_m(l[1])]))
        [1 0 0 0|1 0 0 0]
        [0 1 0 0|0 1 0 0]
        [0 0 1 0|0 0 1 0]
        [0 0 0 1|0 0 0 1]
        [-------+-------]
        [0 0 0 0|0 0 0 0]
        [1 0 0 0|1 0 0 0]
        [0 0 1 0|0 0 0 1]
        [0 1 0 0|0 0 1 0]
        [0 0 0 1|0 1 0 0]
        [-------+-------]
        [1 1 1 1|0 0 1 0]
        [1 0 0 0|1 0 0 0]
        [0 0 1 0|0 1 0 0]
        [0 1 0 0|0 1 1 1]
        [0 1 1 1|0 0 0 1]
        [-------+-------]
        [0 0 0 1|1 1 0 1]
        [1 0 0 0|1 0 0 0]
        [0 1 0 0|0 0 0 1]
        [0 0 1 0|0 1 1 1]
        [0 1 1 1|0 1 0 0]
        [-------+-------]
        [1 1 1 0|1 1 1 1]

    """
    common_reprs = get_common_linear_reprs(lut, verbose, debug)
    number_self_ae = 0
    se_pairs = []

    bitsize = get_bitsize(lut)

    for linear_repr, (betas, alphas) in common_reprs.items():
        # (alphas, betas) from get_common_linear_reprs() swapped to (betas, alphas)
        # L(x) is linear repr of F(x+alpha) and beta+F(x)
        # Let L = A_2 F alpha A_1
        # Let L = L_2 L L_1
        # Then L = L_2 A_2 F alpha A_1 L_1
        # Let L = B_2 beta F B_1
        # Then, F = beta B_2^{-1} L_2 A_2 F alpha A_1 L_1 B_1^{-1}
        # Then, (alpha A_1 L_1 B_1^{-1}, beta B_2^{-1} L_2 A_2) is a affine SE
        linear_repr = list(linear_repr)
        lr_le = get_all_self_le(linear_repr)

        for alpha in alphas:
            lut_alpha = [lut[i.__xor__(alpha)] for i in range(len(lut))]
            a1, a2 = are_linear_equivalent_lut(linear_repr, lut_alpha)

            for beta in betas:
                beta_lut = [x.__xor__(beta) for x in lut]
                b1, b2 = are_linear_equivalent_lut(linear_repr, beta_lut)

                b1 = invert_lut(b1)
                b2 = invert_lut(b2)

                for (l1, l2) in lr_le:
                    right_matrix = compose_lut(a1, compose_lut(l1, b1))
                    right_ct = alpha

                    left_matrix = compose_lut(b2, compose_lut(l2, a2))
                    left_ct = beta

                    if return_lut:
                        right_lut = [x.__xor__(right_ct) for x in right_matrix]
                        left_lut = [x.__xor__(left_ct) for x in left_matrix]
                        se_pairs.append([right_lut, left_lut])
                    else:
                        right_matrix = lut2matrix(right_matrix)
                        left_matrix = lut2matrix(left_matrix)
                        right_ct = int2vector(right_ct, bitsize)
                        left_ct = int2vector(left_ct, bitsize)
                        se_pairs.append([[right_matrix, right_ct], [left_matrix, left_ct]])

        number_self_ae += len(lr_le) * len(alphas) * len(betas)

    assert len(se_pairs) == number_self_ae

    return se_pairs


def check_self_le_lut(lut, right_le=None, left_le=None, affine=False, return_missing=None):
    """Check that the given right-left pair is a linear SE of the given lut.

    If return_missing is True, it returns the right (left) SE part if the
    left (right) SE is given. In that case, if raises an Exception
    if the input half pair is not a SE.

        >>> lut = [0, 1, 2, 3]
        >>> right, left = [0, 3, 2, 1], [0, 3, 2, 1]
        >>> check_self_le_lut(lut, right, left)
        True
        >>> check_self_le_lut(lut, right_le=right) and check_self_le_lut(lut, left_le=left)
        True
        >>> check_self_le_lut(lut, right_le=right, return_missing=True)
        [0, 3, 2, 1]
        >>> lut = get_lut_inversion(4)
        >>> right, left = get_all_self_le(lut)[-1]
        >>> check_self_le_lut(lut, right, left)
        True
        >>> check_self_le_lut(lut, right_le=right) and check_self_le_lut(lut, left_le=left)
        True

    """
    assert not (right_le is None and left_le is None)
    assert not (return_missing and right_le is not None and left_le is not None)

    if right_le is not None:
        assert affine or right_le[0] == 0
    if left_le is not None:
        assert affine or left_le[0] == 0

    if right_le is not None and left_le is not None:
        return lut == compose_lut(left_le, compose_lut(lut, right_le))
    else:
        assert is_invertible(lut)
        if right_le is not None:
            # S = B S A equivalent B^{-1} = S A S^{-1}
            new_lut = compose_lut(lut, compose_lut(right_le, invert_lut(lut)))
        else:
            # S = B S A equivalent A^{-1} = S^{-1} B S
            new_lut = compose_lut(invert_lut(lut), compose_lut(left_le, lut))
        condition = is_invertible(new_lut) and get_algebraic_degree(new_lut) <= 1 and (affine or new_lut[0] == 0)
        if return_missing:
            if not condition:
                raise ValueError("input is not a part of a self-equivalence")
            return invert_lut(new_lut)
        else:
            return condition


def check_self_ae_lut(lut, right_le=None, left_le=None, return_missing=None):
    """Check that the given right-left pair is an affine SE of the given lut.

    If return_missing is True, it returns the right (left) SE part if the
    left (right) SE is given. In that case, if raises an Exception
    if the input half pair is not a SE.

        >>> lut = [0, 1, 2, 3]
        >>> right, left = [3, 1, 2, 0], [3, 1, 2, 0]
        >>> check_self_ae_lut(lut, right, left)
        True
        >>> check_self_ae_lut(lut, right_le=right) and check_self_ae_lut(lut, left_le=left)
        True
        >>> check_self_ae_lut(lut, left_le=left, return_missing=True)
        [3, 1, 2, 0]
        >>> from sage.crypto.sboxes import PRESENT
        >>> lut = list(PRESENT)
        >>> right, left = get_all_self_ae(lut)[-1]
        >>> check_self_ae_lut(lut, right, left)
        True
        >>> check_self_ae_lut(lut, right_le=right) and check_self_ae_lut(lut, left_le=left)
        True

    """
    return check_self_le_lut(lut, right_le=right_le, left_le=left_le, affine=True, return_missing=return_missing)


def check_self_le_anf(anf, right_le_anf=None, left_le_anf=None, anf_inv=None,
                      input_anf_vars=None, input_right_vars=None, input_left_vars=None,
                      input_inv_vars=None, affine=False):
    """Check that the given right-left pair is a linear SE of the given anf.

    If a function is symbolic, its input variables must be given
    as a list of Boolean variables or strings.

    If right or left is not given, the inverse of anf must be given.

    If both right and left are given, this function can also check for
    non-linear self-equivalences.

        >>> from boolcrypt.utilities import lut2anf
        >>> anf = lut2anf([0, 1, 2, 3])
        >>> right, left = lut2anf([0, 3, 2, 1]), lut2anf([0, 3, 2, 1])
        >>> check_self_le_anf(anf, right, left)
        True
        >>> check_self_le_anf(anf, right, None, anf) and check_self_le_anf(anf, None, left, anf)
        True
        >>> anf = lut2anf(get_lut_inversion(4))
        >>> right, left = get_all_self_le(get_lut_inversion(4))[-1]
        >>> right, left = lut2anf(right), lut2anf(left)
        >>> check_self_le_anf(anf, right, left)
        True
        >>> check_self_le_anf(anf, right, None, anf) and check_self_le_anf(anf, None, left, anf)
        True

    """
    assert not (right_le_anf is None and left_le_anf is None)

    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    variable_names = list(anf[0].parent().variable_names())
    if right_le_anf is not None:
        assert all(right_le_anf[0].parent() == f.parent() for f in right_le_anf)
        for v in right_le_anf[0].parent().variable_names():
            if v not in variable_names:
                variable_names.append(v)
    if left_le_anf is not None:
        assert all(left_le_anf[0].parent() == f.parent() for f in left_le_anf)
        for v in left_le_anf[0].parent().variable_names():
            if v not in variable_names:
                variable_names.append(v)
    bpr = sage.all.BooleanPolynomialRing(names=variable_names)

    if input_anf_vars is None:
        assert all(anf[0].parent() == f.parent() for f in anf)
        input_anf_vars = anf[0].parent().variable_names()
    input_anf_vars = [bpr(v) for v in input_anf_vars]
    if right_le_anf is not None:
        if input_right_vars is None:
            input_right_vars = right_le_anf[0].parent().variable_names()
        input_right_vars = [bpr(v) for v in input_right_vars]
        assert len(right_le_anf) == len(input_anf_vars)
    if left_le_anf is not None:
        if input_left_vars is None:
            input_left_vars = left_le_anf[0].parent().variable_names()
        input_left_vars = [bpr(v) for v in input_left_vars]
        assert len(input_left_vars) == len(anf)

    anf = [bpr(f) for f in anf]
    if right_le_anf is not None:
        right_le_anf = [bpr(f) for f in right_le_anf]
    if left_le_anf is not None:
        left_le_anf = [bpr(f) for f in left_le_anf]

    if right_le_anf is not None and left_le_anf is not None:
        new_anf = substitute_anf(anf, {input_anf_vars[i]: f for i, f in enumerate(right_le_anf)}, bpr)
        new_anf = substitute_anf(left_le_anf, {input_left_vars[i]: f for i, f in enumerate(new_anf)}, bpr)
        return anf == list(new_anf)
    else:
        from boolcrypt.utilities import get_symbolic_alg_deg, get_symbolic_coeff
        assert anf_inv is not None

        if input_inv_vars is None:
            assert all(anf_inv[0].parent() == f.parent() for f in anf_inv)
            input_inv_vars = anf_inv[0].parent().variable_names()
        input_inv_vars = [bpr(v) for v in input_inv_vars]
        anf_inv = [bpr(f) for f in anf_inv]

        if right_le_anf is not None:
            assert affine or all(get_symbolic_coeff(f, input_right_vars, 1) == 0 for f in right_le_anf)
            assert len(input_right_vars) == len(anf_inv)
            # S = B S A equivalent B^{-1} = S A S^{-1}
            new_anf = substitute_anf(right_le_anf, {input_right_vars[i]: f for i, f in enumerate(anf_inv)}, bpr)
            new_anf = substitute_anf(anf, {input_anf_vars[i]: f for i, f in enumerate(new_anf)}, bpr)
        else:
            assert affine or all(get_symbolic_coeff(f, input_left_vars, 1) == 0 for f in left_le_anf)
            # S = B S A equivalent A^{-1} = S^{-1} B S
            assert len(left_le_anf) == len(input_inv_vars)
            new_anf = substitute_anf(left_le_anf, {input_left_vars[i]: f for i, f in enumerate(anf)}, bpr)
            new_anf = substitute_anf(anf_inv, {input_inv_vars[i]: f for i, f in enumerate(new_anf)}, bpr)
        valid_se = True
        for f in new_anf:
            valid_se |= get_symbolic_alg_deg(f, input_anf_vars) <= 1
            if not affine:
                valid_se |= get_symbolic_coeff(f, input_anf_vars, 1) == 0
            if not valid_se:
                break
        return valid_se


def check_self_ae_anf(anf, right_ae_anf=None, left_ae_anf=None, anf_inv=None,
                      input_anf_vars=None, input_right_vars=None, input_left_vars=None,
                      input_inv_vars=None):
    """Check that the given right-left pair is an affine SE of the given anf.

    If a function is symbolic, its input variables must be given
    as a list of Boolean variables or strings.

    If right or left is not given, the inverse of anf must be given.

    If both right and left are given, this function can also check for
    non-linear self-equivalences.

        >>> from boolcrypt.utilities import lut2anf
        >>> anf = lut2anf([0, 1, 2, 3])
        >>> right, left = lut2anf([3, 1, 2, 0]), lut2anf([3, 1, 2, 0])
        >>> check_self_ae_anf(anf, right, left)
        True
        >>> check_self_ae_anf(anf, right, None, anf) and check_self_ae_anf(anf, None, left, anf)
        True
        >>> from sage.crypto.sboxes import PRESENT
        >>> lut = list(PRESENT)
        >>> anf = lut2anf(lut)
        >>> anf_inv = lut2anf(invert_lut(lut))
        >>> right, left = get_all_self_ae(lut, return_lut=True)[-1]
        >>> right, left = lut2anf(right), lut2anf(left)
        >>> check_self_ae_anf(anf, right, left)
        True
        >>> check_self_ae_anf(anf, right, None, anf_inv) and check_self_ae_anf(anf, None, left, anf_inv)
        True

    """
    return check_self_le_anf(
        anf, right_le_anf=right_ae_anf, left_le_anf=left_ae_anf, anf_inv=anf_inv,
        input_anf_vars=input_anf_vars, input_right_vars=input_right_vars,
        input_left_vars=input_left_vars, input_inv_vars=input_inv_vars, affine=True)


def are_linear_equivalent_lut(f, g):
    """Return a pair of invertible matrices (a,b) such that f = b g a.

    The permutations f, g are given as LUT.

    If no such pair exists, return an empty list.

        >>> are_linear_equivalent_lut([0, 1, 2, 3], [0, 1, 2, 3])
        [[0, 1, 2, 3], [0, 1, 2, 3]]
        >>> are_linear_equivalent_lut([0, 1, 2, 3], [x.__xor__(1) for x in [0, 1, 2, 3]])
        []
        >>> are_linear_equivalent_lut(list(range(2**4)), get_lut_inversion(4))
        []
        >>> repr_inv = [0, 1, 2, 3, 4, 6, 8, 11, 5, 14, 15, 7, 12, 10, 13, 9]
        >>> right, left = are_linear_equivalent_lut(repr_inv, get_lut_inversion(4))
        >>> right, left
        ([0, 1, 7, 6, 5, 4, 2, 3, 12, 13, 11, 10, 9, 8, 14, 15], [0, 1, 12, 13, 14, 15, 2, 3, 9, 8, 5, 4, 7, 6, 11, 10])
        >>> repr_inv == compose_lut(left, compose_lut(get_lut_inversion(4), right))
        True

    """
    if get_bitsize(f) >= 16:
        raise ValueError("lut with bitsize {}>=16 not supported".format(get_bitsize(f)))

    assert isinstance(f, list) and isinstance(g, list)
    assert isinstance(f[0], int) and isinstance(g[0], int)

    from sboxU import linear_equivalence_fast

    if len(f) != len(g):
        raise ValueError("f and g are of different dimensions!")
    if (f[0] == 0 and g[0] != 0) or (f[0] != 0 and g[0] == 0):
        return []

    return linear_equivalence_fast(f, g)


def are_affine_equivalent_lut(f, g):
    """Return a pair of affine permutations (a,b) such that f = b g a.

    The permutations f,g are given as LUT.

    If no such pair exists, return an empty list.

        >>> are_affine_equivalent_lut([0, 1, 2, 3], [0, 1, 2, 3])
        [[0, 1, 2, 3], [0, 1, 2, 3]]
        >>> are_affine_equivalent_lut([0, 1, 2, 3], [x.__xor__(1) for x in [0, 1, 2, 3]])
        [[0, 3, 1, 2], [3, 1, 0, 2]]
        >>> are_affine_equivalent_lut(list(range(2**4)), get_lut_inversion(4))
        []
        >>> from sage.crypto.sboxes import SERPENT_S3, Golden_S0
        >>> are_affine_equivalent_lut(list(SERPENT_S3), list(Golden_S0))
        [[13, 2, 15, 0, 3, 12, 1, 14, 4, 11, 6, 9, 10, 5, 8, 7], [7, 11, 6, 10, 0, 12, 1, 13, 8, 4, 9, 5, 15, 3, 14, 2]]

    """
    if get_bitsize(f) >= 16:
        raise ValueError("lut with bitsize {}>=16 not supported".format(get_bitsize(f)))

    assert isinstance(f, list) and isinstance(g, list)
    assert isinstance(f[0], int) and isinstance(g[0], int)

    from sboxU.ccz import affine_equivalence
    result = affine_equivalence(f, g)
    if not result:
        return []
    else:
        right_matrix, right_ct, left_matrix, left_ct = result
        return [matrix2lut(right_matrix, right_ct), matrix2lut(left_matrix, left_ct)]


def check_ccz_equivalence_anf(f, g, a, g_implicit=False,
                              f_input_vars=None, g_input_vars=None, a_input_vars=None):
    """Check whether A(Graph(f)) = Graph(g).

    Graph(f) is is the set of points {(x, f(x))}, and similar for Graph(g).
    However, if g_implicit=True, Graph(g) is built as {(x, y) : g(x, y) = 0}.

    The admissible mapping A can be given in ANF, as a matrix or as
    a pair (matrix, vector).

    If F = G, this methods checks whether A is a CCZ self-equivalence.

        >>> from boolcrypt.utilities import lut2anf
        >>> from sage.crypto.sbox import SBox
        >>> # CCZ of inversion found with sboxU.ccz_equivalent_permutations
        >>> f = lut2anf([0, 15, 9, 7, 4, 14, 1, 3, 10, 6, 13, 2, 8, 5, 11, 12])
        >>> g = lut2anf(get_lut_inversion(4))
        >>> am = [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1,
        ... 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1,
        ... 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1]
        >>> am = sage.all.matrix(GF(2), 4*2, 4*2, am)
        >>> check_ccz_equivalence_anf(f, g, am)
        True
        >>> boolean_vars = sage.all.BooleanPolynomialRing(8, 'x').gens()
        >>> iv, ov = boolean_vars[:4], boolean_vars[4:]
        >>> iv, ov = list(reversed(iv)), list(reversed(ov))  # polynomials() takes x0 as MSB
        >>> g_implicit = SBox(get_lut_inversion(4)).polynomials(iv, ov, groebner=True)
        >>> check_ccz_equivalence_anf(f, g_implicit, am, g_implicit=True)
        True
        >>> # Graph-SE found with sat.find_ccz_equivalence
        >>> f = lut2anf((0, 1, 2, 3, 4, 6, 7, 5))
        >>> am = [0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1,
        ...       0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0,]
        >>> am = sage.all.matrix(GF(2), 3*2, 3*2, am)
        >>> check_ccz_equivalence_anf(f, f, am)
        True
        >>> check_ccz_equivalence_anf(f, f, am, f_input_vars=["x0", "x1", "x2"],
        ...     g_input_vars=["x0", "x1", "x2"], a_input_vars=["x" + str(i) for i in range(6)])
        True

    """
    import itertools
    from boolcrypt.utilities import anf2matrix, get_num_inputs_anf

    assert not isinstance(f, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    assert not isinstance(g, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    from sage.structure.element import is_Matrix
    if is_Matrix(a):
        matrix_a = a
        anf_a = matrix2anf(matrix_a)
    elif len(a) == 2 and is_Matrix(a[0]):
        matrix_a, vector_a = a
        anf_a = matrix2anf(matrix_a, bin_vector=vector_a)
    else:
        anf_a = a
        if max(f.degree() for f in anf_a) == 1:
            matrix_a = anf2matrix(anf_a)
        else:
            matrix_a = None

    if matrix_a is not None:
        if not matrix_a.is_invertible():
            raise ValueError(f"the admissible mapping is not invertible:\n{matrix_a}")

    if f_input_vars is None:
        input_size = get_num_inputs_anf(f)
    else:
        input_size = len(f_input_vars)

    for x in sage.all.VectorSpace(sage.all.GF(2), input_size):
        if f_input_vars is None:
            fx = [f_i(*x) for f_i in f]
        else:
            fx = substitute_anf(f, {var_i: x_i for var_i, x_i in zip(f_input_vars, x)}, f[0].parent())
        xfx = sage.all.vector(sage.all.GF(2), itertools.chain(x, fx))
        # a_xfx = (matrix_a * xfx) + vector_a
        if a_input_vars is None:
            a_xfx = [f_i(*xfx) for f_i in anf_a]
        else:
            a_xfx = substitute_anf(anf_a, {var_i: x_i for var_i, x_i in zip(a_input_vars, xfx)}, anf_a[0].parent())
        a_xfx = sage.all.vector(sage.all.GF(2), a_xfx)

        if g_implicit:
            y = a_xfx
            if g_input_vars is None:
                gy = [g_i(*y) for g_i in g]
            else:
                gy = substitute_anf(g, {var_i: y_i for var_i, y_i in zip(g_input_vars, y)}, g[0].parent())
            result = all(bit == 0 for bit in gy)
        else:
            y = a_xfx[:input_size]
            if g_input_vars is None:
                gy = [g_i(*y) for g_i in g]
            else:
                gy = substitute_anf(g, {var_i: y_i for var_i, y_i in zip(g_input_vars, y)}, g[0].parent())
            gy = sage.all.vector(sage.all.GF(2), gy)
            result = a_xfx[input_size:] == gy

        if not result:
            # print("x:           ", x)
            # print("f(x):        ", fx)
            # print("x | f(x):    ", xfx)
            # print("A(x | f(x)): ", a_xfx)
            # print("y:           ", y)
            # print("g(y):        ", gy)
            # if g_implicit:
            #     print("result:", [bit == 0 for bit in gy])
            # else:
            #     print("result:", a_xfx[input_size:], gy)
            # print()
            return False
    else:
        return True
