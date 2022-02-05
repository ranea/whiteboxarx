"""Functions to search for non-binary permutation polynomials."""
from boolcrypt.utilities import (
    get_smart_print, get_time
)

from boolcrypt.findpoly import is_permutation_poly

import sage.all

GF = sage.all.GF
PolynomialRing = sage.all.PolynomialRing


def get_anf(poly, degree_extension, verbose=False):
    """Return the ANF over a non-binary field.

        >>> p, n = 3, 2
        >>> ff = GF(p, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = 2*x**6 + 4*x**4 + 3*x**3 + x**2
        >>> get_anf(poly, n, verbose=True)
        irreducible: x^2 + 2*x + 2 -> x by t -> t^2 - t - 1
        input_ext: x1*t + x0
        poly_ext: x0*x1*t - x1^2*t + x0^2 - x0*x1 + x1^2
        [x0^2 - x0*x1 + x1^2, x0*x1 - x1^2]
        >>> p, n = 3, 3
        >>> ff = GF(p, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = x**2
        >>> get_anf(poly, n, verbose=False)
        [x0^2 + x1*x2, -x0*x1 - x1*x2 - x2^2, x1^2 - x0*x2 + x2^2]
        >>> p, n = 3, 4
        >>> ff = GF(p, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = x**2
        >>> get_anf(poly, n, verbose=False)  # doctest: +NORMALIZE_WHITESPACE
        [x0^2 + x2^2 - x1*x3 - x2*x3 + x3^2,
        -x0*x1 - x2*x3 + x3^2, x1^2 - x0*x2 + x3^2,
        -x1*x2 + x2^2 - x0*x3 - x1*x3 - x2*x3 + x3^2]

    """
    field = poly.base_ring()
    p = field.characteristic()
    assert len(field) == p

    names = ["x" + str(i) for i in range(degree_extension)] + ["t"]
    polyring = field[','.join(names)]  # asterisk is critical
    polyring_x = polyring.gens()[:-1]
    polyring_t = polyring.gens()[-1]

    modulus = GF(p ** degree_extension, repr="int").modulus()
    irreducible_poly = 0
    for i in range(degree_extension + 1):
        # if modulus[i]:  # i-coefficient != 0
        irreducible_poly += modulus[i] * polyring_t**i
    # modulus is a poly over x, but it need to be a poly in t
    if verbose:
        print("irreducible:", modulus, "-> x by t ->", irreducible_poly)

    ideal = [var**p - var for var in polyring_x]
    ideal.append(irreducible_poly)

    input_ext = 0
    for i in range(degree_extension):
        input_ext += polyring_x[i] * polyring_t**i
    if verbose:
        print("input_ext:", input_ext)
    poly_ext = poly(input_ext).mod(ideal)
    if verbose:
        print("poly_ext:", poly_ext)

    anf = []
    for i in range(degree_extension):
        anf.append(poly_ext.coefficient({polyring_t: i}))
    return anf


def is_quadratic_poly(poly, degree_extension, verbose=False):
    """Return whether the polynomial has algebraic degree 2.

    The given poly must be defined over the base field, not the extension field.

        >>> p, n = 3, 2
        >>> ff = GF(p, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = 2*x**6 + 4*x**4 + 3*x**3 + x**2
        >>> is_quadratic_poly(poly, n, verbose=True)
        irreducible: x^2 + 2*x + 2 -> x by t -> t^2 - t - 1
        input_ext: x1*t + x0
        poly_ext: x0*x1*t - x1^2*t + x0^2 - x0*x1 + x1^2
        degree(x0^2 - x0*x1 + x1^2) = 2
        degree(x0*x1 - x1^2) = 2
        True
        >>> p, n = 3, 3
        >>> ff = GF(p, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = x**2
        >>> is_quadratic_poly(poly, n, verbose=False)
        True
        >>> p, n = 3, 4
        >>> ff = GF(p, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = x**2
        >>> is_quadratic_poly(poly, n, verbose=False)
        True

    """
    anf = get_anf(poly, degree_extension, verbose)

    degrees = set()
    for i in range(degree_extension):
        degrees.add(anf[i].degree())
        if verbose:
            print("degree({}) = {}".format(anf[i], anf[i].degree()))

    return 2 in degrees and all(d <= 2 for d in degrees)


def int2basep(integer, p, bin_format=False):
    """Convert the given integer to its representation in base p.

        >>> for i in range(0, 8): sage.all.Integer(i).bits()
        []
        [1]
        [0, 1]
        [1, 1]
        [0, 0, 1]
        [1, 0, 1]
        [0, 1, 1]
        [1, 1, 1]
        >>> for i in range(0, 8): int2basep(i, 2)
        [0]
        [1]
        [0, 1]
        [1, 1]
        [0, 0, 1]
        [1, 0, 1]
        [0, 1, 1]
        [1, 1, 1]

    """
    # to convert integer to binary, start with the integer in question and
    # divide it by 2, keeping notice of the quotient and the remainder.
    # Continue dividing the quotient by 2 until you get a quotient of zero,
    # then just write out the remainders in the reverse order.

    remainders = []
    while True:
        quo, rem = divmod(integer, p)
        remainders.append(rem)
        if quo == 0:
            break
        else:
            integer = quo

    if bin_format:
        return '0p' + ''.join([str(x) for x in reversed(remainders)])

    return remainders


def get_degd_exponents(p, degree_extension, d, verbose=False):
    """Return the exponents of the extension field with algebraic degree d.

        >>> get_degd_exponents(3, 2, 1)
        [1, 3]
        >>> get_degd_exponents(3, 2, 2)
        [2, 4, 6]

    """
    qe = []
    for exp in range(1, p ** degree_extension):
        coeffs = int2basep(exp, p)
        if sum(coeffs) == d:
            if verbose:
                print("{}, {}".format(exp, coeffs))
            qe.append(exp)
    return qe


def get_algebraic_degree_poly(polynomial):
    """Return the algebraic degree of a polynomial.

        >>> p, n = 3, 2
        >>> ff = GF(p, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = 2*x**6 + 4*x**4 + 3*x**3 + x**2
        >>> get_algebraic_degree_poly(poly)
        2
        >>> p, n = 3, 3
        >>> ff = GF(p, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = x**2
        >>> get_algebraic_degree_poly(poly)
        2
        >>> p, n = 3, 4
        >>> ff = GF(p, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = x**2
        >>> get_algebraic_degree_poly(poly)
        2

    """
    field = polynomial.base_ring()
    p = field.characteristic()

    exp2coeff = polynomial.dict()  # k, v = exp, coeff
    max_alg_deg = -1
    for exp in exp2coeff:
        alg_deg = sum(int2basep(exp, p))
        if alg_deg > max_alg_deg:
            max_alg_deg = alg_deg
    return max_alg_deg


def invert_poly(polynomial):
    """Return the inverse of a permutation polynomial.

        >>> p, n = 3, 2
        >>> ff = GF(p**n, repr="int")
        >>> x = PolynomialRing(ff, 'x').gen()
        >>> poly = 2 * x
        >>> inv_poly = invert_poly(poly)
        >>> inv_poly
        2*x
        >>> inv_poly(poly).mod(x**(p**n) - x)
        x
        >>> poly = x**6 + x**4 + x**3 + x**2
        >>> inv_poly = invert_poly(poly)
        >>> inv_poly
        2*x^6 + 2*x^4 + x^3 + 2*x^2
        >>> inv_poly(poly).mod(x**(p**n) - x)
        x

    """
    field = polynomial.base_ring()
    poly_ring = polynomial.parent()

    points = []
    for x in field:
        points.append((polynomial(x), x))
    return poly_ring.lagrange_polynomial(points)


def find_quadratic_krssb(p, n, terms, k=None, field_var=None,
                         print_alg_deg_inverse=False, print_anf=False,
                         filename=None, verbose=False, debug=False, print_time=False):
    """Find quadratic "rotation-symmetric" permutations over non-binary fields.

        >>> p, n, terms, k = 3, 2, 2, 1
        >>> find_quadratic_krssb(p, n, terms, k, verbose=True)  # smallest n
        # find_quadratic_krssb(3, 2, 2, 1)
        valid_exponents: [6, 4, 3, 2, 1]
        get_exponents_algdeg2: [2, 4, 6]
        get_exponents_algdeg1: [1, 3]
        subfield: [1, 2]
        recursion(x^2, 1, 3)
        recursion(x^4, 1, 1)
        recursion(x^6, 1, 0)
        >>> p, n, terms, k = 3, 2, 4, 1
        >>> find_quadratic_krssb(p, n, terms, k, verbose=False, print_alg_deg_inverse=True, print_anf=True)  # smallest binomials
        # alg deg of inverse:  2
        # [-x1^2 + x0 + x1, -x1]
        x^6 + x^4 + x^3 + x^2
        # alg deg of inverse:  2
        # [-x1^2 - x0 - x1, x1]
        x^6 + x^4 + 2*x^3 + x^2
        # alg deg of inverse:  2
        # [-x1^2 + x0, x1]
        x^6 + x^4 + x^2 + x
        # alg deg of inverse:  2
        # [-x1^2 - x0, -x1]
        x^6 + x^4 + x^2 + 2*x

    """
    if field_var is None:
        field = GF(p ** n, repr="int")
        x = PolynomialRing(field, 'x').gen()
    else:
        field = field_var.base_ring()
        x = field_var

    smart_print = get_smart_print(filename)

    assert not(debug and not verbose)

    if k is None:
        k = n

    assert terms > 1
    assert n % k == 0

    if verbose:
        smart_print("# find_quadratic_krssb({}, {}, {}, {})".format(p, n, terms, k))

    # from bigger to lower
    alg_deg2 = get_degd_exponents(p, n, d=2)
    alg_deg1 = get_degd_exponents(p, n, d=1)
    valid_exponents = sorted(alg_deg2 + alg_deg1, reverse=True)
    valid_exponents_deg2 = set(alg_deg2)
    num_valid_exponents = len(valid_exponents)

    # no zero
    if k == n:
        subfield = [field.fetch_int(i) for i in range(1, p**n)]
    else:
        subfield = []
        for i in range(1, p**n):
            beta = field.fetch_int(i)
            if beta == beta**(p ** k):
                subfield.append(beta)

    if verbose:
        smart_print("valid_exponents:", valid_exponents)
        smart_print("get_exponents_algdeg2:", alg_deg2)
        smart_print("get_exponents_algdeg1:", alg_deg1)
        smart_print("subfield:", subfield)

    def recursion(polynomial, monomials_remaining, last_index_exp):
        if num_valid_exponents - last_index_exp <= monomials_remaining:
            # example entering if: num_valid_exponents=4, last_index_exp=3 and monomials_remaining=1
            return

        if monomials_remaining > 1:
            for index_exp in range(last_index_exp + 1, num_valid_exponents):
                exp = valid_exponents[index_exp]
                for alpha in subfield:
                    if debug:
                        smart_print("trying", polynomial + alpha * (x ** exp))
                    recursion(polynomial + alpha * (x ** exp),
                              monomials_remaining - 1,
                              index_exp)
        else:
            for index_exp in range(last_index_exp + 1, num_valid_exponents):
                exp = valid_exponents[index_exp]
                for alpha in subfield:
                    if debug:
                        smart_print("trying", polynomial + alpha * (x ** exp))
                    if is_permutation_poly(polynomial + alpha * (x ** exp)):
                        if print_alg_deg_inverse:
                            d = get_algebraic_degree_poly(invert_poly(polynomial + alpha * (x ** exp)))
                            smart_print("# alg deg of inverse: ", d)
                        if print_anf:
                            anf = get_anf(PolynomialRing(GF(p, repr="int"), 'x')(polynomial + alpha * (x ** exp)), n)
                            smart_print("#", anf)
                        smart_print(polynomial + alpha * (x ** exp))

    for index_leading_exp in reversed(range(num_valid_exponents)):  # from low to big
        leading_exp = valid_exponents[index_leading_exp]
        if leading_exp not in valid_exponents_deg2:
            continue

        if verbose:
            smart_print("{}recursion({}, {}, {})".format(
                get_time() if print_time else "",
                x ** leading_exp,
                terms - 1,
                index_leading_exp)
            )

        recursion(x ** leading_exp,
                  terms - 1,
                  index_leading_exp)
