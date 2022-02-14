"""Functions to search for binary permutation polynomials."""
from boolcrypt.utilities import (
    get_smart_print, lut2hex_string, poly2lut, hex_string2lut, invert_lut,
    lut2poly, compose_lut, get_time, get_rijndael_field, get_algebraic_degree
)

import sage.all

GF = sage.all.GF
PolynomialRing = sage.all.PolynomialRing
BooleanPolynomialRing = sage.all.BooleanPolynomialRing


zz_var = PolynomialRing(sage.all.ZZ, 'x').gen()  # avoiding generating the PolynomialRing each time


def str2poly(line, field_var):
    """Parse an string containing a finite field polynomial.

        >>> x = PolynomialRing(get_rijndael_field(), 'x').gen()
        >>> fpoly = str2poly("53*x^208 + x^13", x)
        >>> fpoly
        53*x^208 + x^13
        >>> fpoly.parent()
        Univariate Polynomial Ring in x over Finite Field in a of size 2^8

    """
    zpoly = sage.all.sage_eval(line.strip(), locals={str(field_var): zz_var})

    # return zpoly2fpoly(zpoly, field_var)

    field = field_var.base_ring()
    fpoly = field.fetch_int(0)
    for exp, coeff in zpoly.dict().items():
        fpoly += field.fetch_int(coeff) * (field_var ** exp)
    return fpoly


def is_permutation_poly(polynomial):
    """Check whether the input polynomial is a permutation.

        >>> x = PolynomialRing(get_rijndael_field(), 'x').gen()
        >>> is_permutation_poly(x**3)
        False
        >>> is_permutation_poly(x**127)
        True
        >>> is_permutation_poly(str2poly("(23)*x^7 + x^28", x))
        True

    """
    collision = set()
    num_collisions = 0
    for x in polynomial.base_ring():
        collision.add(polynomial(x))
        if len(collision) == num_collisions:
            return False
        else:
            num_collisions += 1
    return True


def poly2lut_fast(polynomial, field, output_lut):
    """Return the LUT representation of a permutation polynomial.

        >>> field = GF(2**4, repr="int")
        >>> x = PolynomialRing(field, 'x').gen()
        >>> output_lut = [None for i in range(2**4)]
        >>> poly2lut_fast(x, field, output_lut)
        >>> output_lut
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

    """
    for i in range(len(output_lut)):
        output_lut[i] = polynomial(field.fetch_int(i)).integer_representation()


def find_krssb(n, d, terms, k, field_var=None, filename=None, verbose=False, print_time=False):
    """Find all k-rotation-symmetric S-boxes of given algebraic degree.

    Find permutations S = sum(a_i + x^i), where a_i^(2^k) = a_i.

    Some "left" affine equivalent krssb do not appear in the list,
    that is, if f(x) and g(x) are two k-rssbb of the same alg_deg
    and f(x) = A(g(x)), with A affine, then g(x) might not appear.

    This function do not return anything (to prevent high memory usage).

    Apart from the polynomials, the signature of the function
    and the leading monomials (e.g., # x^192) is printed
    to the output.

        >>> find_krssb(3, 2, 3, 1, verbose=True)
        # find_krssb(3, 2, 3, 1)
        valid_exponents: [6, 5, 4, 3, 2, 1]
        valid_exponents_lsb_set: {1, 3, 5}
        subfield: [1]
        maximal_subfield: {1}
        # x^3
        recursion(x^3, 2, 3, True, False)
        x^3 + x^2 + x
        # x^5
        recursion(x^5, 2, 1, True, False)
        x^5 + x^4 + x
        x^5 + x^3 + x
        # x^6
        recursion(x^6, 2, 0, False, False)
        x^6 + x^5 + x^4
        x^6 + x^3 + x^2
        >>> find_krssb(4, 2, 5, 2)
        # find_krssb(4, 2, 5, 2)
        # x^3
        # x^5
        # x^6
        # x^9
        # x^10
        x^10 + 6*x^9 + 7*x^8 + 6*x^6 + 7*x^5
        x^10 + 6*x^9 + 6*x^6 + 7*x^5 + x^4
        x^10 + 6*x^9 + 6*x^6 + 7*x^5 + 7*x^2
        x^10 + 6*x^9 + 6*x^6 + 7*x^5 + x
        x^10 + 7*x^9 + 6*x^8 + 7*x^6 + 6*x^5
        x^10 + 7*x^9 + 7*x^6 + 6*x^5 + x^4
        x^10 + 7*x^9 + 7*x^6 + 6*x^5 + 6*x^2
        x^10 + 7*x^9 + 7*x^6 + 6*x^5 + x
        # x^12
        x^12 + 6*x^10 + 7*x^8 + 7*x^5 + x^3
        x^12 + 6*x^10 + 7*x^5 + 6*x^4 + x^3
        x^12 + 6*x^10 + 7*x^5 + x^3 + 7*x^2
        x^12 + 6*x^10 + 7*x^5 + x^3 + 6*x
        x^12 + 7*x^10 + 6*x^8 + 6*x^5 + x^3
        x^12 + 7*x^10 + 6*x^5 + 7*x^4 + x^3
        x^12 + 7*x^10 + 6*x^5 + x^3 + 6*x^2
        x^12 + 7*x^10 + 6*x^5 + x^3 + 7*x
        x^12 + x^9 + 6*x^8 + x^6 + x^3
        x^12 + x^9 + 7*x^8 + x^6 + x^3
        x^12 + x^9 + x^6 + 6*x^4 + x^3
        x^12 + x^9 + x^6 + 7*x^4 + x^3
        x^12 + x^9 + x^6 + x^3 + 6*x^2
        x^12 + x^9 + x^6 + x^3 + 7*x^2
        x^12 + x^9 + x^6 + x^3 + 6*x
        x^12 + x^9 + x^6 + x^3 + 7*x

    """
    if field_var is None:
        if n == 8:
            field = get_rijndael_field()
        else:
            field = GF(2 ** n, repr="int")
        x = PolynomialRing(field, 'x').gen()
    else:
        field = field_var.base_ring()
        x = field_var

    smart_print = get_smart_print(filename)

    assert terms > 1
    assert n % k == 0

    smart_print("# find_krssb({}, {}, {}, {})".format(n, d, terms, k))

    # from bigger to lower
    valid_exponents = []
    valid_exponents_lsb_set = set()
    for valid_exp in range(2**n - 1, 0, -1):
        if bin(valid_exp)[2:].count("1") <= d:
            valid_exponents.append(valid_exp)
            if bin(valid_exp)[-1] == "1":
                valid_exponents_lsb_set.add(valid_exp)

    num_valid_exponents = len(valid_exponents)

    subfield = []
    maximal_subfield = set()
    for beta in field:
        if beta != 0 and beta == beta**(2 ** k):
            subfield.append(beta)
            if k == 1:
                maximal_subfield.add(beta)
            elif beta != beta**(2 ** (k-1)):
                maximal_subfield.add(beta)

    if verbose:
        print("valid_exponents:", valid_exponents)
        print("valid_exponents_lsb_set:", valid_exponents_lsb_set)
        print("subfield:", subfield)
        print("maximal_subfield:", maximal_subfield)

    def recursion(polynomial, monomials_remaining, last_index_exp, lsb_exp_set, maximal_subfield_set):
        if num_valid_exponents - last_index_exp <= monomials_remaining:
            # example entering if: num_valid_exponents=4, last_index_exp=3 and monomials_remaining=1
            return

        if monomials_remaining > 1:
            for index_exp in range(last_index_exp + 1, num_valid_exponents):
                exp = valid_exponents[index_exp]
                for alpha in subfield:
                    recursion(polynomial + alpha * (x ** exp),
                              monomials_remaining - 1,
                              index_exp,
                              lsb_exp_set | (exp in valid_exponents_lsb_set),
                              maximal_subfield_set | (alpha in maximal_subfield))
        else:
            for index_exp in range(last_index_exp + 1, num_valid_exponents):
                exp = valid_exponents[index_exp]
                if not lsb_exp_set and exp not in valid_exponents_lsb_set:
                    continue
                for alpha in subfield:
                    if not maximal_subfield_set and alpha not in maximal_subfield:
                        continue
                    if is_permutation_poly(polynomial + alpha * (x ** exp)):
                        # avoid creating a long-lasting object
                        smart_print(polynomial + alpha * (x ** exp))

    for index_leading_exp in reversed(range(num_valid_exponents)):  # from low to big
        leading_exp = valid_exponents[index_leading_exp]
        if bin(leading_exp)[2:].count("1") == d:
            # fixing leading coefficient to one
            # for alpha in subfield:
            if print_time:
                smart_print("# x^{}\t|\t{}".format(str(leading_exp), get_time()))
            else:
                smart_print("# x^{}".format(str(leading_exp)))
            if verbose:
                print("recursion({}, {}, {}, {}, False)".format(
                    x ** leading_exp,
                    terms - 1,
                    index_leading_exp,
                    leading_exp in valid_exponents_lsb_set)
                )
            recursion(x ** leading_exp,
                      terms - 1,
                      index_leading_exp,
                      leading_exp in valid_exponents_lsb_set,
                      False)  # alpha in maximal_subfield)


# def find_krssb8b_givaro(d, terms, k, output_filename):
#     """Find all 8-bit k-rotation-symmetric S-boxes of given algebraic degree.
#
#     This function is faster than find_find_rotation_symmetric_sboxes(),
#     but only works with n = 8.
#
#         >>> temp_file = sage.all.tmp_filename('testing_find_8b_krssb', '.txt')
#         >>> find_krssb8b_givaro(d=2, terms=5, k=1, output_filename=temp_file)
#         >>> with open(temp_file, "r") as file:
#         ...     print(file.read())  # doctest: +ELLIPSIS
#         # x^3
#         # x^5
#         # x^6
#         # x^9
#         # x^10
#         # x^12
#         # x^17
#         # x^18
#         # x^20
#         # x^24
#         # x^33
#         # x^34
#         # x^36
#         # x^40
#         # x^48
#         x^3 + x^18 + x^32 + x^33 + x^48
#         x^3 + x^16 + x^18 + x^33 + x^48
#         x^3 + x^8 + x^18 + x^33 + x^48
#         x^3 + x^4 + x^18 + x^33 + x^48
#         x^2 + x^3 + x^18 + x^33 + x^48
#         x + x^3 + x^18 + x^33 + x^48
#         # x^65
#         ...
#
#     """
#     path_binary = "./find_krss8b"
#     if not os.path.isfile(path_binary):
#         raise ValueError("cannot find find_krss8b binary in " + path_binary)
#     subprocess.check_call([path_binary, str(d), str(terms), str(k), output_filename])


def find_divisors_or_selfequivs(permutation, input_file, output_file=None,
                                deg_remainder=None, deg_other_se=None,
                                side_divisor="both", side_se="both",
                                xor_cts=None,
                                verbose=False,
                                field_var=None, num_char_per_elem=None, time_marks=None):
    """Find divisors and/or self-equivalences of a permutation.

    The list of candidates P can be given as a file
    containing hex strings or str polynomials.
    If given as hex strings, the number of characters used
    element must be given (see hex_string2lut).
    If given as str polynomials, the variable of the
    polynomials must also be given.

    The permutation S can be given as a LUT, a polynomial
    or in the same format as the list of candidates.

    If side_divisor="left", outputs the candidates P such that S = P R.
    If side_divisor="right", outputs the candidates P such that S = R P.
    In both cases, outputs those P when deg(R) <= deg_remainder.

    If side_se="left", outputs the candidates P such that S = P S R.
    If side_se="right", outputs the candidates P such that S = R S P.
    In both cases, outputs those P when deg(R) <= deg_other_se.

    If loop_over_all_ct="left", for each candidate P, check also k + P(x).
    If loop_over_all_ct="right", for each candidate P, check also P(x+k).

        >>> temp_file = sage.all.tmp_filename('testing_find_all_divisor_se', '.txt')
        >>> find_krssb(n=3, d=2, terms=3, k=1, filename=temp_file)
        >>> x = PolynomialRing(GF(2**3, repr="int"), "x").gen()
        >>> # finding left divisors P such that S = P R, with deg(R)<=2
        >>> find_divisors_or_selfequivs("x^6", temp_file, deg_remainder=2, side_divisor="left", field_var=x, verbose=True)
        # found left divisor; deg(R): 2, poly(R): x^6 + x^3 + x^2
        x^3 + x^2 + x
        # found left divisor; deg(R): 2, poly(R): x^6 + x^5 + x^4
        x^5 + x^4 + x
        # found left divisor; deg(R): 2, poly(R): x^6 + x^5 + x^4 + x^3 + x^2
        x^5 + x^3 + x
        # found left divisor; deg(R): 2, poly(R): x^6 + x^5 + x^4 + x^3 + x
        x^6 + x^5 + x^4
        # found left divisor; deg(R): 2, poly(R): x^6 + x^5 + x^3 + x^2 + x
        x^6 + x^3 + x^2
        >>> # finding left self-equivalences P such that S = P S R, with deg(R)<=2
        >>> find_divisors_or_selfequivs("x^6", temp_file, deg_other_se=2, side_se="left", field_var=x, verbose=False)
        [0, 1, 5, 2, 7, 4, 3, 6]
        [0, 1, 3, 6, 5, 2, 7, 4]
        [0, 1, 6, 5, 2, 7, 4, 3]
        [0, 1, 4, 3, 6, 5, 2, 7]
        [0, 1, 2, 7, 4, 3, 6, 5]
        >>> x =  PolynomialRing(get_rijndael_field(), 'x').gen()
        >>> temp_file = sage.all.tmp_filename('testing_find_all_divisor_se_part2', '.txt')
        >>> # find_krssb8b_givaro(d=2, terms=5, k=1, output_filename=temp_file)
        >>> # finding left divisors P such that x^13 = P R, with deg(R)<=3
        >>> # find_divisors_or_selfequivs("x^13", temp_file, deg_remainder=3, side_divisor="left", field_var=x, verbose=True)
        # found left divisor; deg(R): 3, poly(R): x^80 + x^65 + x^52 + x^20 + x^5
        x^5 + x^20 + x^64 + x^65 + x^80
        # found left divisor; deg(R): 3, poly(R): x^104 + x^80 + x^65 + x^20 + x^5
        x^5 + x^20 + x^32 + x^65 + x^80
        # found left divisor; deg(R): 3, poly(R): x^208 + x^80 + x^65 + x^20 + x^5
        x^5 + x^16 + x^20 + x^65 + x^80
        # found left divisor; deg(R): 3, poly(R): x^161 + x^80 + x^65 + x^20 + x^5
        x^5 + x^8 + x^20 + x^65 + x^80
        # found left divisor; deg(R): 3, poly(R): x^80 + x^67 + x^65 + x^20 + x^5
        x^4 + x^5 + x^20 + x^65 + x^80
        # found left divisor; deg(R): 3, poly(R): x^134 + x^80 + x^65 + x^20 + x^5
        x^2 + x^5 + x^20 + x^65 + x^80
        # found left divisor; deg(R): 3, poly(R): x^80 + x^65 + x^20 + x^13 + x^5
        x + x^5 + x^20 + x^65 + x^80
        # found left divisor; deg(R): 3, poly(R): x^160 + x^130 + x^40 + x^13 + x^10
        x + x^10 + x^40 + x^130 + x^160

    """
    assert field_var is not None or num_char_per_elem is not None

    smart_print = get_smart_print(output_file)

    if isinstance(permutation, (list, tuple)):
        permutation_lut = list(permutation)
    elif hasattr(permutation, "base_ring"):
        # is a polynomial whp
        permutation_lut = poly2lut(permutation)
    else:
        if field_var is not None:
            permutation_lut = poly2lut(str2poly(permutation, field_var))
        else:
            permutation_lut = hex_string2lut(permutation.strip(), num_char_per_elem)

    inv_permutation_lut = invert_lut(permutation_lut)

    if field_var is not None:
        field = field_var.base_ring()
    else:
        field = None

    size_field = len(permutation_lut)

    if xor_cts is not None:
        assert xor_cts in ["right", "left"]
        cts = [i for i in range(size_field)]
    else:
        cts = [0]

    candidate_lut = [None for _ in range(size_field)]
    xor_candidate_lut = [None for _ in range(size_field)]

    with open("{}".format(input_file)) as file:
        for index, line in enumerate(file):
            if line.startswith("#") or line.startswith("find"):
                continue

            if time_marks is not None:
                if index % time_marks == 0:
                    smart_print("# {} | index: {}".format(get_time(), index))

            line = line.strip()

            if field_var is not None:
                poly2lut_fast(str2poly(line, field_var), field, candidate_lut)
            else:
                candidate_lut = hex_string2lut(line.strip(), num_char_per_elem)

            for ct in cts:
                if ct == 0:
                    xor_candidate_lut = candidate_lut
                else:
                    if xor_cts == "right":
                        for i in range(size_field):
                            xor_candidate_lut[i] = candidate_lut[i.__xor__(ct)]
                    else:
                        for i in range(size_field):
                            xor_candidate_lut[i] = candidate_lut[i].__xor__(ct)

                inv_candidate_lut = invert_lut(xor_candidate_lut)

                if deg_remainder is not None:
                    if side_divisor == "left" or side_divisor == "both":
                        # S = P R   <==>    P^(-1) S = R
                        composition = compose_lut(inv_candidate_lut, permutation_lut)
                        degree = get_algebraic_degree(composition)
                        if degree <= deg_remainder:
                            if not verbose:
                                smart_print(candidate_lut)
                            else:
                                to_output = "# found left divisor; deg(R): {}".format(degree)
                                if xor_cts:
                                    to_output += ", ct:{}".format(ct)
                                if field_var is not None:
                                    to_output += ", poly(R): {}".format(lut2poly(composition, field_var))
                                smart_print(to_output)
                                smart_print(line)

                    if side_divisor == "right" or side_divisor == "both":
                        # S = R P   <==>    S P^(-1) = R
                        composition = compose_lut(permutation_lut, inv_candidate_lut)
                        degree = get_algebraic_degree(composition)
                        if degree <= deg_remainder:
                            if not verbose:
                                smart_print(candidate_lut)
                            else:
                                to_output = "# found right divisor; deg(R): {}".format(degree)
                                if xor_cts:
                                    to_output += ", ct:{}".format(ct)
                                if field_var is not None:
                                    to_output += ", poly(R): {}".format(lut2poly(composition, field_var))
                                smart_print(to_output)
                                smart_print(line)

                if deg_other_se is not None:
                    if side_se == "left" or side_se == "both":
                        # S = P S R   <==>    S^(-1) P^(-1) S      = R
                        composition = compose_lut(inv_permutation_lut, compose_lut(inv_candidate_lut, permutation_lut))
                        degree = get_algebraic_degree(composition)
                        if degree <= deg_other_se:
                            if not verbose:
                                smart_print(candidate_lut)
                            else:
                                to_output = "# found left selfequiv; deg(R): {}".format(degree)
                                if xor_cts:
                                    to_output += ", ct:{}".format(ct)
                                if field_var is not None:
                                    to_output += ", poly(R): {}".format(lut2poly(composition, field_var))
                                smart_print(to_output)
                                smart_print(line)

                    if side_se == "right" or side_se == "both":
                        # S = R S P   <==>    S P^(-1) S^(-1) = R
                        composition = compose_lut(permutation_lut, compose_lut(inv_candidate_lut, inv_permutation_lut))
                        degree = get_algebraic_degree(composition)
                        if degree <= deg_other_se:
                            if not verbose:
                                smart_print(candidate_lut)
                            else:
                                to_output = "# right selfequiv; deg(R): {}".format(degree)
                                if xor_cts:
                                    to_output += ", ct:{}".format(ct)
                                if field_var is not None:
                                    to_output += ", poly(R): {}".format(lut2poly(composition, field_var))
                                smart_print(to_output)
                                smart_print(line)


def check_permutation(input_file, mode, degree=None, output_file=None,
                      field_var=None, num_char_per_elem=None, verbose=False):
    """Check properties of permutations given in a file.

    The permutation can be given as hex strings or str polynomials.
    If given as hex strings, the number of characters used
    element must be given (see hex_string2lut).
    If given as str polynomials, the variable of the
    polynomials must also be given.

    List of modes:

    "is_odd" outputs the permutations that are odd (like the inversion)
    "inv_deg_max" outputs the permutations whose inverse degree
                  are greater than the target degree
    "inv_deg_min" outputs the permutations whose inverse degree
                  are lower than the target degree
    "unique" outputs the list of permutations without duplicates
    "invertible" outputs the permutations that are invertible
    "linear_repr" outputs the linear representatives, without duplicates

        >>> x = PolynomialRing(get_rijndael_field(), 'x').gen()
        >>> temp_file = sage.all.tmp_filename('testing_check_lut', '.txt')
        >>> with open(temp_file, "w") as file:
        ...     print("x", file=file)
        ...     print("x", file=file)
        ...     print("x**127", file=file)
        >>> check_permutation(temp_file, "is_odd", output_file=None, field_var=x)
        x**127
        >>> check_permutation(temp_file, "inv_deg_min", degree=3, output_file=None, field_var=x)
        # 7
        x**127
        >>> check_permutation(temp_file, "inv_deg_max", degree=2, output_file=None, field_var=x)
        # 1
        x
        # 1
        x
        >>> check_permutation(temp_file, "unique", output_file=None, field_var=x)
        x
        x**127
        >>> x = PolynomialRing(GF(2**4, repr="int"), 'x').gen()
        >>> cpe = 2
        >>> temp_file = sage.all.tmp_filename('testing_check_lut2', '.txt')
        >>> with open(temp_file, "w") as file:
        ...     print(lut2hex_string(poly2lut(x**2), cpe), file=file)
        ...     print(lut2hex_string(poly2lut(x**3), cpe), file=file)
        ...     print(lut2hex_string(poly2lut(x**6), cpe), file=file)
        >>> check_permutation(temp_file, "invertible", output_file=None, num_char_per_elem=cpe)
        00010405030207060c0d08090f0e0b0a
        >>> check_permutation(temp_file, "linear_repr", output_file=None, num_char_per_elem=cpe)
        (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
        (16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16)

    """
    assert field_var is not None or num_char_per_elem == 2

    smart_print = get_smart_print(output_file)

    if field_var is not None:
        field = field_var.base_ring()
        lut = [None for _ in range(len(field))]
    else:
        field = None
        lut = None

    previous_lut = set()
    num_luts = 0

    # avoid for 8-bit quadratic permutations
    if mode == "linear_repr":
        from boolcrypt.equivalence import get_linear_repr

    # if mode == "linear_equiv":
    #     previous_lut = []
    #     num_luts = 0
    #     import sboxu
    #     import multiprocessing
    #     import time
    #
    #     return_dictionary = {'is_le': False}
    #
    #     def is_le(left_lut, right_lut, queue):
    #         # https://stackoverflow.com/a/37736655/4355013
    #         status = sboxu.linear_equivalence_fast(left_lut, right_lut)
    #         print("is_le?:", len(status) > 0)
    #         ret = queue.get()
    #         ret['is_le'] = True
    #         queue.put(ret)
    #         # return_dictionary_input["is_le"] = len(status) > 0

    with open("{}".format(input_file)) as file:
        for index, line in enumerate(file):
            if line.startswith("#") or line.startswith("find"):
                continue

            line = line.strip()

            if field_var is not None:
                poly2lut_fast(str2poly(line, field_var), field, lut)
            else:
                lut = hex_string2lut(line.strip(), num_char_per_elem)

            if mode == "is_odd":
                # noinspection PyArgumentList
                is_even = sage.all.Permutation([i+1 for i in lut]).is_even()
                if not is_even:
                    smart_print(line)

            elif mode == "inv_deg_min":
                inv_lut = invert_lut(lut)
                deg = get_algebraic_degree(inv_lut)
                if deg >= degree:
                    smart_print("# " + str(deg))
                    smart_print(line)

            elif mode == "inv_deg_max":
                inv_lut = invert_lut(lut)
                deg = get_algebraic_degree(inv_lut)
                if deg <= degree:
                    smart_print("# " + str(deg))
                    smart_print(line)

            elif mode == "unique":
                previous_lut.add(tuple(lut))
                if num_luts == len(previous_lut):
                    pass
                else:
                    smart_print(line)
                num_luts = len(previous_lut)

            elif mode == "invertible":
                if len(lut) == len(set(lut)):
                    smart_print(line)

            elif mode == "linear_repr":
                if verbose:
                    print("{} | computing get_linear_repr(candidate[{}])".format(get_time(), index))

                lr = tuple(get_linear_repr(lut))  # to get hashed

                previous_lut.add(lr)
                if num_luts == len(previous_lut):
                    pass
                else:
                    smart_print(lr)  # prints linear reprs, not luts!
                num_luts = len(previous_lut)

            else:
                raise ValueError("invalid mode")

            # elif mode == "linear_equiv":
            #     for i, p_lut in enumerate(reversed(previous_lut)):
            #         print("{} | computing le(candidate[{}], lut[-{}])".format(get_time(), index, i))
            #         # is_le = linear_equivalence(p_lut, lut)
            #
            #         queue = multiprocessing.Queue()
            #         queue.put(return_dictionary)
            #         p = multiprocessing.Process(target=is_le, args=(p_lut, lut, queue))
            #         p.start()
            #         p.join(1)  # Wait a maximum of 10 seconds for foo
            #         result = queue.get()['is_le']
            #         print("queue.get()['is_le']:", result)
            #         if result:
            #             break
            #         return_dictionary['is_le'] = False
            #         if p.is_alive():
            #             print("aborting...")
            #             p.terminate()
            #             p.join()
            #     else:
            #         smart_print(line)
            #         previous_lut.append(lut)


def polyfile2hex(n, input_file, output_file=None, field_var=None):
    """Return the hex representation of permutation polynomials.

        >>> temp_file = sage.all.tmp_filename('test_poly2hex', '.txt')
        >>> with open(temp_file, "w") as file:
        ...     print("x", file=file)
        ...     print("x**127", file=file)
        >>> polyfile2hex(4, temp_file, output_file=None)
        000102030405060708090a0b0c0d0e0f
        00010b0d090e06070c0508030f02040a

    """
    smart_print = get_smart_print(output_file)

    if field_var is None:
        if n != 8:
            field_var = PolynomialRing(GF(2 ** n, repr="int"), 'x').gen()
        else:
            field_var = PolynomialRing(get_rijndael_field(), 'x').gen()

    field = field_var.base_ring()

    lut = [None for _ in range(2**n)]
    size_lut = len(lut)

    with open("{}".format(input_file)) as file:
        for index, line in enumerate(file):
            if line.startswith("#") or line.startswith("find"):
                continue

            line = line.strip()

            # avoid poly2lut() for efficiency
            # lut = poly2lut(str2poly(line, field_var))
            polynomial = str2poly(line, field_var)
            for i in range(size_lut):
                lut[i] = polynomial(field.fetch_int(i)).integer_representation()

            smart_print(lut2hex_string(lut, num_char_per_elem=2))


def get_sas_decomposition(exponent, n, degree, max_degree=None):
    """
    Find an SAS decomposition of a given power function f(x)=x^exponent,
    where A is an invertible linear monomial (x^2^i) and
    the S's are invertible non-linear monomials with given algebraic degree.

    Each decomposition is given by a triplet [a, b, c] where (a, c)
    are the exponents of the non-linear monomials and b is the exponent
    of the linear monomial.

        >>> decompositions = get_sas_decomposition(127, 8, 3)
        >>> decompositions[:5]
        [[13, 1, 49], [13, 2, 152], [13, 4, 76], [13, 8, 38], [13, 16, 19]]

    """
    import itertools
    ring_exps = sage.all.IntegerModRing(2**n - 1)
    exponent = ring_exps(exponent)

    if max_degree is None:
        max_degree = 2 ** n

    linear_exps = [ring_exps(2**i) for i in range(n)]
    nonlin_exps = [ring_exps(x) for x in range(2**n) if 1 < bin(x).count("1") <= degree and x < max_degree]

    decompositions = []

    for s_1, a_1, s_2 in itertools.product(nonlin_exps, linear_exps, nonlin_exps):
        if s_1 * a_1 * s_2 == exponent:
            # print(s_1, a_1, s_2)
            decompositions.append([s_1, a_1, s_2])

    return decompositions


def get_monomial_permutation(n, alg_deg, field=None, ignore_le=False, verbose=False):
    """Get all permutation monomials in GF(2^n) with given algebraic degree.

        >>> get_monomial_permutation(4, 3, ignore_le=True, verbose=True)
        x^7
        found x^11 but is LE to x^7
        found x^13 but is LE to x^7
        found x^14 but is LE to x^7
        [x^7]
        >>> get_monomial_permutation(4, 3)
        [x^7, x^11, x^13, x^14]
        >>> get_monomial_permutation(8, 3, ignore_le=True, verbose=True)  # doctest: +SKIP
        x^7
        x^11
        x^13
        found x^14 but is LE to x^7
        x^19
        found x^22 but is LE to x^11
        found x^26 but is LE to x^13
        found x^28 but is LE to x^7
        x^37
        found x^38 but is LE to x^19
        found x^41 but is LE to x^37
        found x^44 but is LE to x^11
        found x^49 but is LE to x^19
        found x^52 but is LE to x^13
        found x^56 but is LE to x^7
        found x^67 but is LE to x^13
        found x^73 but is LE to x^37
        found x^74 but is LE to x^37
        found x^76 but is LE to x^19
        found x^82 but is LE to x^37
        found x^88 but is LE to x^11
        found x^97 but is LE to x^11
        found x^98 but is LE to x^19
        found x^104 but is LE to x^13
        found x^112 but is LE to x^7
        found x^131 but is LE to x^7
        found x^133 but is LE to x^11
        found x^134 but is LE to x^13
        found x^137 but is LE to x^19
        found x^146 but is LE to x^37
        found x^148 but is LE to x^37
        found x^152 but is LE to x^19
        found x^161 but is LE to x^13
        found x^164 but is LE to x^37
        found x^176 but is LE to x^11
        found x^193 but is LE to x^7
        found x^194 but is LE to x^11
        found x^196 but is LE to x^19
        found x^208 but is LE to x^13
        found x^224 but is LE to x^7
        [x^7, x^11, x^13, x^19, x^37]

    """
    from boolcrypt.equivalence import get_linear_repr

    if field is None:
        if n == 8:
            field = get_rijndael_field()
        else:
            field = GF(2 ** n, repr="int")

    x = PolynomialRing(field, 'x').gen()

    # looping over all polynomials x^(le)
    # - ignoring affine constant

    monomial_permutations = []
    lin_reprs = {}

    for exp in range(2**n):
        if bin(exp).count("1") != alg_deg:
            continue

        monomial = x**exp
        if is_permutation_poly(monomial):
            if ignore_le:
                lr = tuple(get_linear_repr(poly2lut(monomial)))
                if lr in lin_reprs:
                    if verbose:
                        print("found {} but is LE to {}".format(monomial, lin_reprs[lr]))
                    continue
                else:
                    lin_reprs[lr] = monomial

            if verbose:
                print(monomial)

            monomial_permutations.append(monomial)

    return monomial_permutations


def find_quadratic_permutations(n, strong=False, filename=None):
    """Find quadratic permutation in ANF form.

    If strong=True, find permutations without linear components
    and with good differential properties. In this cases,
    LUTs are printed (instead of ANFs) together with their
    differential uniformity.

        >>> find_quadratic_permutations(n=3)
        [x0, x1, x2]
        [x0, x1, x0*x1 + x2]
        [x0, x0*x2 + x1, x2]
        [x0, x0*x2 + x1, x0*x1 + x0*x2 + x2]
        [x0, x0*x1 + x0*x2 + x1, x0*x1 + x2]
        [x0, x0*x1 + x0*x2 + x1, x0*x1 + x0*x2 + x2]
        [x0 + x1*x2, x1, x2]
        [x0 + x1*x2, x1, x0*x1 + x1*x2 + x2]
        [x0 + x1*x2, x0*x1 + x0*x2 + x1, x0*x1 + x0*x2 + x2]
        [x0 + x1*x2, x0*x1 + x0*x2 + x1, x0*x1 + x1*x2 + x2]
        [x0 + x1*x2, x0*x2 + x1*x2 + x1, x2]
        [x0 + x1*x2, x0*x2 + x1*x2 + x1, x0*x1 + x0*x2 + x2]
        [x0*x1 + x0 + x1*x2, x1, x0*x1 + x2]
        [x0*x1 + x0 + x1*x2, x1, x0*x1 + x1*x2 + x2]
        [x0*x1 + x0 + x1*x2, x0*x2 + x1, x0*x1 + x0*x2 + x2]
        [x0*x1 + x0 + x1*x2, x0*x2 + x1, x0*x1 + x1*x2 + x2]
        [x0*x1 + x0 + x1*x2, x0*x2 + x1*x2 + x1, x0*x1 + x2]
        [x0*x1 + x0 + x1*x2, x0*x2 + x1*x2 + x1, x0*x1 + x0*x2 + x2]
        [x0*x2 + x0 + x1*x2, x0*x2 + x1, x2]
        [x0*x2 + x0 + x1*x2, x0*x2 + x1, x0*x1 + x1*x2 + x2]
        [x0*x2 + x0 + x1*x2, x0*x1 + x0*x2 + x1, x0*x1 + x2]
        [x0*x2 + x0 + x1*x2, x0*x1 + x0*x2 + x1, x0*x1 + x1*x2 + x2]
        [x0*x2 + x0 + x1*x2, x0*x2 + x1*x2 + x1, x2]
        [x0*x2 + x0 + x1*x2, x0*x2 + x1*x2 + x1, x0*x1 + x2]
        >>> find_quadratic_permutations(n=3, strong=True)
        2 [0, 1, 2, 5, 4, 7, 3, 6]
        2 [0, 1, 2, 7, 4, 3, 5, 6]
        2 [0, 1, 2, 6, 4, 3, 7, 5]
        2 [0, 1, 2, 6, 4, 7, 5, 3]
        2 [0, 1, 2, 7, 4, 6, 3, 5]
        2 [0, 1, 2, 5, 4, 6, 7, 3]

    """
    from boolcrypt.utilities import vector2int
    import itertools

    smart_print = get_smart_print(filename)

    # smart_print("sample_quadratic_boolfunc({})".format(n))

    balanced = len(sage.all.VectorSpace(GF(2), n)) // 2
    vector_space_gf2n = sage.all.VectorSpace(GF(2), n)

    @sage.all.cached_function
    def is_balanced(my_component):
        counter = 0
        for w in vector_space_gf2n:
            counter += int(my_component(*w))
        return counter == balanced

    def are_balanced(old_components, new_component):
        # check all combinations considering new_component are balanced
        i = len(old_components)
        for r in range(1, i + 1):  # i = 1, r in [1,]
            for combination in itertools.combinations(range(i), r):  # i = 1, combinations = (0,)
                aux = bool_ring(0)
                for c in combination:
                    aux += old_components[c]

                aux = aux + new_component

                if strong and aux.degree() <= 1:
                    return False

                if not is_balanced(aux):
                    # print(len(old_components)*"\t" + "non-balanced {} <-> {}".format(new_component, combination))
                    return False
        return True

    def is_permutation(anf):
        collision = [False for _ in range(2 ** n)]
        for w in vector_space_gf2n:
            result = vector2int([f(*w) for f in anf])
            if collision[result] is True:
                return False
            collision[result] = True
        return True

    bool_ring = BooleanPolynomialRing(n, 'x')

    # affine ct to zero
    quadratic_terms = []  # list(B.gens())
    for i in range(n):
        for j in range(i):
            quadratic_terms.append(bool_ring.variable(i) * bool_ring.variable(j))
    quadratic_terms = sage.all.vector(quadratic_terms)

    quadratic_coeff_space = [sage.all.VectorSpace(GF(2), len(quadratic_terms)) for _ in range(n)]

    # if randomized is True:
    #     _quadratic_coeff_space = quadratic_coeff_space[:]
    #
    #     for i in range(n):
    #         quadratic_coeff_space[i] = (_quadratic_coeff_space[i].random_element() for _ in range(1000000))

    from boolcrypt.utilities import get_differential_uniformity, anf2lut

    def recursion(components):
        if len(components) >= n:
            if is_permutation(components):
                if not strong:
                    smart_print("{}".format(components))
                else:
                    lut = anf2lut(components)
                    du = get_differential_uniformity(lut)
                    if du < 2**n:
                        smart_print("{} {}".format(du, lut))
        else:
            i = len(components)
            for quadratic_coeff in quadratic_coeff_space[i]:
                if strong and quadratic_coeff == 0:
                    continue

                new_component = quadratic_coeff * quadratic_terms + bool_ring.variable(i)
                if is_balanced(new_component):
                    if are_balanced(components, new_component):
                        # smart_print(len(components)*"\t" + "found {}-th component: {}".format(
                        #             len(components), new_component))
                        # components.append(new_component)
                        recursion(components + [new_component])
                else:
                    pass
                    # smart_print(len(components)*"\t" + "non-balanced {}-th component: {}".format(
                    #             len(components), new_component))

    for leading_quadratic_coeff in quadratic_coeff_space[0]:
        if strong and leading_quadratic_coeff == 0:
            continue

        component = leading_quadratic_coeff * quadratic_terms + bool_ring.variable(0)

        if is_balanced(component):
            # smart_print("found 0-th component:", component)
            recursion([component],)
        else:
            pass
            #  smart_print("non-balanced 0-th component:", component)
