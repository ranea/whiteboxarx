"""Find an affine equivalent permutation minimizing some objective function."""
import math

from boolcrypt.utilities import (
    get_time, get_lut_inversion, compose_matrix_lut, compose_anf_fast, matrix2anf, lut2anf,
    normalize_poly, matrix2poly, lut2poly, get_smart_print
)

import sage.all

from sage.rings.polynomial.pbori.pbori import BooleanPolynomialVector

GF = sage.all.GF
PolynomialRing = sage.all.PolynomialRing
BooleanPolynomialRing = sage.all.BooleanPolynomialRing


def find_optimal_equiv_poly(lut, field=None, mode="random", minimize="deg", filename=None, verbose=False):
    """Find an affine equivalent permutation minimizing some objective function.

    Given F, finds G = B circ F circ A such that the polynomial representing G
    minimizes some objective function Obj.

    B is taken linear (adding a constant would not minimize the objective function)
    and A is taken affine.

    mode="deg" minimizes the polynomial degree,
    mode="terms" minimizes the number of term
    mode="linear_terms" minimizes the number of linear terms x^(q^i)

    mode="random" tries random A and L
    mode="all_matrices" iterates all invertible matrices (and constants)
    mode="all_linearized" iterates all linearized polynomial (and constants).

        >>> lut = get_lut_inversion(3)
        >>> bin_matrix = sage.all.matrix(GF(2), 3, 3, [[1, 0, 0], [0, 1, 0], [1, 0, 1]]).inverse()
        >>> new_lut = compose_matrix_lut(bin_matrix, lut)
        >>> find_optimal_equiv_poly(new_lut, mode="all_matrices", minimize="terms", verbose=False)
        6*x^5

    """
    dimension = int(math.log(len(lut), 2))
    assert 2**dimension == len(lut)

    if field is None:
        field = GF(2**dimension, repr="int")

    poly_ring = PolynomialRing(field, 'x')

    smart_print = get_smart_print(filename)

    if minimize == "deg":
        def objective(p):
            # taking into account Frobenius
            offset = min([bin(e)[2:].find('1') for e in p.exponents()])
            return p.degree() // (2**offset)
    elif minimize == "terms":
        def objective(p):
            number_of_terms = p.number_of_terms()
            if p.constant_coefficient() != 0:
                number_of_terms -= 1
            return number_of_terms
    elif minimize == "linear_terms":
        def objective(p):
            num_terms = 0
            for e in p.exponents():
                if bin(e).count("1") == 1:
                    num_terms += 1
            return num_terms
    else:
        assert False

    # TODO: v2 add an optional parameter to avoid recomputing the linear group
    linear_group = sage.all.GL(dimension, GF(2))
    linear_group_list = linear_group
    linear_group_list = []
    for m in linear_group:
        m = m.matrix()
        m.set_immutable()
        linear_group_list.append(m)
    del linear_group

    def random_invertible_matrix():
        return linear_group_list[sage.all.randint(0, len(linear_group_list) - 1)]

    vectors, v2ff, ff2v = field.vector_space(GF(2), map=True)

    poly = lut2poly(lut, poly_ring.gen())

    # polynomial given as map between vectors
    poly_map = {}
    for v in vectors:
        poly_map[tuple(v)] = ff2v(poly(v2ff(v)))

    size_search = len(linear_group_list) * len(linear_group_list) * len(vectors)

    if mode == "random":
        def next_polynomial():
            while True:
                right_matrix, left_matrix = random_invertible_matrix(), random_invertible_matrix()
                right_ct = vectors.random_element()

                new_points = []
                for x in vectors:
                    y = left_matrix * poly_map[tuple(right_matrix*(x + right_ct))]
                    new_points.append((v2ff(x), v2ff(y)))

                yield poly_ring.lagrange_polynomial(new_points)
    elif mode == "all_matrices":
        def next_polynomial():
            for right_matrix, left_matrix, right_ct in sage.all.cartesian_product_iterator([
                linear_group_list, linear_group_list, vectors
            ]):
                # right_matrix, left_matrix = right_matrix.matrix(), left_matrix.matrix()
                new_points = []
                for x in vectors:
                    y = left_matrix * poly_map[tuple(right_matrix*(x + right_ct))]
                    new_points.append((v2ff(x), v2ff(y)))

                yield poly_ring.lagrange_polynomial(new_points)
    elif mode == "all_linearized":
        linearized_polynomials = [matrix2poly(g, field, poly_ring) for g in linear_group_list]
        modulus = poly_ring.gen()**(2**dimension) - poly_ring.gen()

        def next_polynomial():
            for right_linpoly, left_linpoly, right_ct in sage.all.cartesian_product_iterator([
                linearized_polynomials, linearized_polynomials, field
            ]):
                right_composition = poly(right_linpoly + right_ct).mod(modulus)
                yield left_linpoly(right_composition).mod(modulus)
    else:
        raise ValueError("invalid mode")

    best_poly = poly
    minimum = objective(best_poly)

    if verbose:
        smart_print("input\t{}: {}\tdeg: {}\tterm: {}\n\t{}\n\t{}".format(
            minimize, minimum, best_poly.degree(), best_poly.number_of_terms(),
            best_poly, normalize_poly(best_poly)
        ))

    if minimum == 1:
        return best_poly

    counter = 0
    progress_bar = -1
    for new_poly in next_polynomial():
        new_poly_obj = objective(new_poly)
        if new_poly_obj < minimum:
            best_poly = new_poly
            minimum = new_poly_obj
            if verbose:
                smart_print("{}\t{}: {}\tdeg: {}\tterm: {}\n\t{}\n\t{}".format(
                    get_time(), minimize, minimum, best_poly.degree(), best_poly.number_of_terms(),
                    best_poly, normalize_poly(best_poly)
                ))
            if minimum == 1:
                break

        counter += 1
        new_progress_bar = (counter * 100) // size_search
        if new_progress_bar > progress_bar:
            progress_bar = new_progress_bar
            if verbose:
                smart_print("{}% searched".format(progress_bar))
            if progress_bar == 100:
                break

    return best_poly


def find_optimal_equiv_anf(sbox_lut, mode="random", minimize="terms", filename=None, verbose=True):
    """Find an affine equivalent permutation minimizing some objective function.

    Given F, finds G = B circ F circ A such that the ANF representing G
    minimizes some objective function Obj.

    B is taken linear (adding a constant would not minimize the objective function)
    and A is taken affine.

    mode="terms" minimizes the number of terms

    mode="random" tries random A and L
    mode="all_matrices" iterates all invertible matrices (and constants)
    mode="all_linearized" iterates all linearized polynomial (and constants).

        >>> lut = [i for i in range(2**3)]
        >>> bin_matrix = sage.all.matrix(GF(2), 3, 3, [[1, 0, 0], [0, 1, 0], [1, 0, 1]]).inverse()
        >>> new_lut = compose_matrix_lut(bin_matrix, lut)
        >>> list(find_optimal_equiv_anf(new_lut, mode="all_matrices", minimize="terms", verbose=False))
        [x0, x1, x2]

    """
    n = int(math.log(len(sbox_lut), 2))
    assert 2**n == len(sbox_lut)

    sbox_anf = lut2anf(sbox_lut)

    bool_ring = sbox_anf[0].ring()

    smart_print = get_smart_print(filename)

    if minimize == "terms":
        def objective(anf):
            return sum([len(p_i) for p_i in anf])
    else:
        raise NotImplementedError("only minimize=terms implemented")

    # TODO: v2 add an optional parameter to avoid recomputing the linear group
    linear_group = sage.all.GL(n, GF(2))
    linear_group_list = linear_group
    linear_group_list = []
    for m in linear_group:
        m = m.matrix()
        linear_group_list.append(matrix2anf(m, bool_ring))
    del linear_group

    def random_invertible_matrix():
        return linear_group_list[sage.all.randint(0, len(linear_group_list) - 1)]

    vectors = sage.all.VectorSpace(GF(2), n)

    size_search = len(linear_group_list) * len(linear_group_list) * len(vectors)

    if mode == "random":
        def next_anf():
            while True:
                right_matrix, left_matrix = random_invertible_matrix(), random_invertible_matrix()
                right_ct = vectors.random_element()

                right_affine = BooleanPolynomialVector(
                    [component + bit for component, bit in zip(right_matrix, right_ct)]
                )
                yield compose_anf_fast(left_matrix, compose_anf_fast(sbox_anf, right_affine))
    elif mode == "all_matrices":
        def next_anf():
            for right_matrix, left_matrix, right_ct in sage.all.cartesian_product_iterator([
                linear_group_list, linear_group_list, vectors
            ]):
                right_affine = BooleanPolynomialVector(
                    [component + bit for component, bit in zip(right_matrix, right_ct)]
                )
                yield compose_anf_fast(left_matrix, compose_anf_fast(sbox_anf, right_affine))
    else:
        raise ValueError("invalid mode")

    best_anf = sbox_anf
    minimum = objective(best_anf)

    if verbose:
        smart_print("{}\t{}: {}\t{}".format(get_time(), minimize, minimum, best_anf))

    # TODO: v2 generalize the objective function
    if minimum == n:
        return best_anf

    counter = 0
    progress_bar = -1
    for new_anf in next_anf():
        new_anf_obj = objective(new_anf)
        if new_anf_obj < minimum:
            best_anf = new_anf
            minimum = new_anf_obj
            if verbose:
                smart_print("{} | {}:{} | {}".format(get_time(), minimize, minimum, best_anf))
            if minimum == n:
                break

        counter += 1
        new_progress_bar = (counter * 100) // size_search
        if new_progress_bar > progress_bar:
            progress_bar = new_progress_bar
            if verbose:
                smart_print("{}% searched".format(progress_bar))
            if progress_bar == 100:
                break

    return best_anf
