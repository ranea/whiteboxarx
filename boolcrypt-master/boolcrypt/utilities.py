"""Basic utilities of boolcrypt."""

import datetime
import itertools
import math
import pprint

import sage.all

from sage.rings.polynomial.pbori.pbori import BooleanPolynomialVector, substitute_variables

GF = sage.all.GF
PolynomialRing = sage.all.PolynomialRing
BooleanPolynomialRing = sage.all.BooleanPolynomialRing


# ------
# python
# ------


def get_time():
    now = datetime.datetime.now()
    return "{}D-{}:{}".format(now.day, now.hour, now.minute)


def get_smart_print(filename):
    """Return a print-like function."""
    if filename is None:
        def smart_print(*args, **kwargs):
            print(*args, **kwargs, flush=True)
    elif filename is False:
        def smart_print(*args):
            return
    else:
        assert isinstance(filename, str)

        def smart_print(*args, **kwargs):
            with open(filename, "a") as f:
                print(*args, **kwargs, file=f)
                f.flush()
    return smart_print


# ------------
# finite field
# ------------


def get_rijndael_field(name="a"):
    """Return the finite field used in AES

        >>> get_rijndael_field().modulus()
        x^8 + x^4 + x^3 + x + 1

    """
    return GF(2 ** 8, name=name, repr="int", modulus=[1, 1, 0, 1, 1, 0, 0, 0, 1])


# ----------
# conversion
# ----------


def matrix2poly(bin_matrix, field=None, poly_ring=None):
    """Return the linearized polynomial given by the binary matrix.

        >>> matrix2poly(sage.all.identity_matrix(GF(2), 4), GF(2**4))
        x
        >>> # See In How Many Ways Can You Write Rijndael?
        >>> entries = [
        ... [1, 0, 0, 0, 1, 1, 1, 1], [1, 1, 0, 0, 0, 1, 1, 1], [1, 1, 1, 0, 0, 0, 1, 1], [1, 1, 1, 1, 0, 0, 0, 1],
        ... [1, 1, 1, 1, 1, 0, 0, 0], [0, 1, 1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 1, 1, 0], [0, 0, 0, 1, 1, 1, 1, 1]]
        >>> bin_matrix = sage.all.matrix(GF(2), 8, 8, entries)
        >>> ct = get_rijndael_field().fetch_int(vector2int([1, 1, 0 ,0, 0, 1, 1, 0]))
        >>> poly = matrix2poly(bin_matrix, get_rijndael_field()) + ct
        >>> poly
        143*x^128 + 181*x^64 + x^32 + 244*x^16 + 37*x^8 + 249*x^4 + 9*x^2 + 5*x + 99
        >>> [hex(c.integer_representation()) for c in poly.coefficients()]  # [ct term, ..., leading coeff]
        ['0x63', '0x5', '0x9', '0xf9', '0x25', '0xf4', '0x1', '0xb5', '0x8f']

    Sources:
     - https://ask.sagemath.org/question/40008/how-can-we-make-the-aes-s-box-using-lagrange-interpolation/
    """
    if field is None:
        field = GF(2 ** bin_matrix.ncols(), repr="int")
    if poly_ring is None:
        poly_ring = PolynomialRing(field, 'x')
    base_field = field.base_ring()
    z = field.gen()
    n = field.degree()
    p = field.characteristic()

    def psi_inverse(v):
        return sum(v[kk] * (z ** kk) for kk in range(n))

    poly_ring_base_field = PolynomialRing(base_field, 'y')

    def psi(a):
        coeffs = poly_ring_base_field(a).list()
        coeffs += ([base_field(0), ] * (n - len(coeffs)))
        return sage.all.vector(base_field, coeffs)

    m = sage.all.matrix(field, n, n,
                        [[(z ** i) ** (p ** k) for k in range(n)] for i in range(n)])

    w = sage.all.matrix(field, n, 1, [psi_inverse(bin_matrix * psi(z ** k)) for k in range(n)])

    poly_coeffs = m.inverse() * w

    x = poly_ring.gen()

    return sum(poly_coeffs[i][0] * (x ** (p ** i)) for i in range(n))


def matrix2anf(bin_matrix, bool_poly_ring=None, input_vars=None, bin_vector=None):
    """Return the ANF (the canonical components) of a given matrix.

    If bool_poly_ring is given, the list input_vars can be given as
    a list of Boolean variables, strings or input variable indices.
    Otherwise, input_vars is given as a a list of Boolean variables.

        >>> anf = matrix2anf(sage.all.identity_matrix(GF(2), 4, 4), bin_vector=[0, 1, 0, 1])
        >>> for p in anf: print(p)
        x0
        x1 + 1
        x2
        x3 + 1
        >>> bool_poly_ring = BooleanPolynomialRing(names=('a','b','c','d','y0','y1','y2','y3'))
        >>> a, b, c, d, y0, y1, y2, y3 = bool_poly_ring.gens()
        >>> symbolic_matrix = sage.all.matrix(2, 2, [[a, b], [c, d]])
        >>> symbolic_matrix
        [a b]
        [c d]
        >>> anf = matrix2anf(symbolic_matrix, bool_poly_ring, input_vars=[y0, y1, y2, y3])
        >>> for p in anf: print(p)
        a*y0 + b*y1
        c*y0 + d*y1

    """
    if bool_poly_ring is None and input_vars is None:
        bool_poly_ring = BooleanPolynomialRing(bin_matrix.ncols(), 'x')
        input_vars = bool_poly_ring.gens()[:bin_matrix.ncols()]
    elif bool_poly_ring is not None and input_vars is None:
        input_vars = bool_poly_ring.gens()[:bin_matrix.ncols()]
    elif bool_poly_ring is None and input_vars is not None:
        bool_poly_ring = input_vars[0].parent()
    else:
        if isinstance(input_vars[0], int):
            input_vars = [bool_poly_ring.gens()[i] for i in input_vars]
        elif isinstance(input_vars[0], str):
            input_vars = [bool_poly_ring(vn) for vn in input_vars]

    anf = BooleanPolynomialVector()
    for i, row in enumerate(bin_matrix.rows()):
        component = bool_poly_ring(0)
        for a_ij, x_j in zip(row, input_vars):
            if a_ij not in [0, 1]:
                a_ij = str(a_ij)  # SR
            component += bool_poly_ring(a_ij) * x_j
        if bin_vector:
            component += bool_poly_ring(bin_vector[i])
        anf.append(component)

    assert all(anf[0].parent() == anf[i].parent() for i in range(1, len(anf)))

    return anf


def matrix2lut(bin_matrix, bin_vector=None):
    """Return the LUT of a given matrix.

        >>> matrix2lut(sage.all.identity_matrix(GF(2), 4, 4), bin_vector=sage.all.vector(GF(2), [1, 0, 0, 0]))
        [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]

    """
    n = bin_matrix.ncols()
    lut = []
    if bin_vector is None:
        bin_vector = 0
    if isinstance(bin_vector, int):
        bin_vector = int2vector(bin_vector, n)
    for x in sage.all.VectorSpace(GF(2), n):
        lut.append(vector2int(bin_matrix * x + bin_vector))
    return lut


def poly2matrix(lin_poly):
    """Return the binary matrix given by the linearized polynomial.

        >>> x = PolynomialRing(GF(2**4), 'x').gen()
        >>> poly2matrix(x)
        [1 0 0 0]
        [0 1 0 0]
        [0 0 1 0]
        [0 0 0 1]
        >>> x = PolynomialRing(get_rijndael_field(), 'x').gen()
        >>> # See In How Many Ways Can You Write Rijndael
        >>> poly2matrix(x**2)
        [1 0 0 0 1 0 1 0]
        [0 0 0 0 1 0 1 1]
        [0 1 0 0 0 1 0 0]
        [0 0 0 0 1 1 1 1]
        [0 0 1 0 1 0 0 1]
        [0 0 0 0 0 1 1 0]
        [0 0 0 1 0 1 0 0]
        [0 0 0 0 0 0 1 1]

    """
    field = lin_poly.base_ring()
    vectors, v2ff, ff2v = field.vector_space(GF(field.characteristic()), map=True)
    return sage.all.matrix([ff2v(lin_poly(v2ff(v))) for v in vectors.basis()]).transpose()


def lut2matrix(lut, return_ct=False):
    """Return the binary matrix given by the LUT

        >>> x = PolynomialRing(GF(2**4), 'x').gen()
        >>> lut2matrix(poly2lut(x))
        [1 0 0 0]
        [0 1 0 0]
        [0 0 1 0]
        [0 0 0 1]
        >>> lut2matrix(poly2lut(x + 1), return_ct=True)
        [[0 1 1 1]
        [0 1 0 0]
        [0 0 1 0]
        [0 0 0 1], (1, 0, 0, 0)]
        >>> x = PolynomialRing(get_rijndael_field(), 'x').gen()
        >>> lut2matrix(poly2lut(x**2))  # See In How Many Ways Can You Write Rijndael
        [1 0 0 0 1 0 1 0]
        [0 0 0 0 1 0 1 1]
        [0 1 0 0 0 1 0 0]
        [0 0 0 0 1 1 1 1]
        [0 0 1 0 1 0 0 1]
        [0 0 0 0 0 1 1 0]
        [0 0 0 1 0 1 0 0]
        [0 0 0 0 0 0 1 1]

    """
    if return_ct:
        return [poly2matrix(lut2poly(lut)), int2vector(lut[0], get_bitsize(lut))]
    else:
        return poly2matrix(lut2poly(lut))


def hex_string2lut(s, num_char_per_elem):
    """Return the LUT given as a compact hex string.

        >>> s = "6512304789ABCDEF"
        >>> lut = hex_string2lut(s, 1)
        >>> lut
        [6, 5, 1, 2, 3, 0, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        >>> [hex(x) for x in lut]
        ['0x6', '0x5', '0x1', '0x2', '0x3', '0x0', '0x4', '0x7', '0x8', '0x9', '0xa', '0xb', '0xc', '0xd', '0xe', '0xf']
        >>> assert lut == hex_string2lut("0x6512304789ABCDEF", 1)
        >>> assert lut == hex_string2lut("0x060501020300040708090a0b0c0d0e0f", 2)

    """
    if s.startswith("0x"):
        s = s[2:]
    assert bin(len(s) // num_char_per_elem).count("1") == 1  # is a power of two
    base = 16
    lut = []
    for i in range(0, len(s), num_char_per_elem):
        lut.append(int(s[i:i + num_char_per_elem], base))
    return lut


def lut2hex_string(lut, num_char_per_elem, prefix0x=False):
    """Return the hex string representation.

        >>> lut = [6, 5, 1, 2, 3, 0, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        >>> lut2hex_string(lut, 1)
        '6512304789abcdef'
        >>> assert lut2hex_string(lut, 2, True) == "0x060501020300040708090a0b0c0d0e0f"

    """
    if prefix0x:
        s = "0x"
    else:
        s = ""
    return s + ''.join([("{:0" + str(num_char_per_elem) + "x}").format(elem) for elem in lut])


def lut2poly(lut, field_var=None):
    """Return the polynomial representation of a given LUT.

        >>> lut2poly(get_lut_inversion(4))
        x^14
        >>> field_var = PolynomialRing(get_rijndael_field(), 'y').gen()
        >>> lut2poly(get_lut_inversion(8, field_var.base_ring()), field_var)
        y^254

    """
    if field_var is None:
        field = GF(len(lut), repr="int")
        poly_ring = PolynomialRing(field, 'x')
    else:
        field = field_var.base_ring()
        poly_ring = field_var.parent()

    points = []
    for i in range(len(field)):
        x = field.fetch_int(i)
        y = field.fetch_int(lut[i])
        points.append((x, y))
    return poly_ring.lagrange_polynomial(points)


def lut2anf(lut, bool_poly_ring=None, num_inputs=None, num_outputs=None):
    """Return the ANF (the canonical components) of a function given as a LUT.

        >>> for p in lut2anf(get_lut_inversion(4)): print(p)
        x0*x1*x2 + x0*x2 + x0 + x1*x2*x3 + x1*x2 + x1 + x2 + x3
        x0*x1*x3 + x0*x1 + x0*x2 + x1*x2 + x1*x3 + x3
        x0*x1 + x0*x2*x3 + x0*x2 + x0*x3 + x2 + x3
        x0*x3 + x1*x2*x3 + x1*x3 + x1 + x2*x3 + x2 + x3
        >>> bpr = BooleanPolynomialRing(3, 'x')
        >>> for p in lut2anf([0] * (2**3), bool_poly_ring=bpr): print(p)
        0
        0
        0
        >>> # more inputs that outputs
        >>> lut = [[bpr("x0*x1 + x0 + x1")(*v), bpr("x0")(*v)] for v in sage.all.VectorSpace(GF(2), 3)]
        >>> for p in lut2anf([vector2int(v) for v in lut]): print(p)
        x0*x1 + x0 + x1
        x0
        0
        >>> for p in lut2anf([vector2int(v) for v in lut], num_outputs=2): print(p)
        x0*x1 + x0 + x1
        x0
        >>> # more outputs than inputs
        >>> lut = [[bpr("x0")(*v), bpr("x1")(*v), bpr("x2")(*v), bpr("x0*x1 + x2")(*v), ] for v in sage.all.VectorSpace(GF(2), 3)]
        >>> # for p in lut2anf([vector2int(v) for v in lut]): print(p)  # AssertionError
        >>> for p in lut2anf([vector2int(v) for v in lut], num_outputs=4): print(p)
        x0
        x1
        x2
        x0*x1 + x2

    """
    if num_inputs is None:
        if bool_poly_ring is None:
            num_inputs = get_bitsize(lut)
        else:
            num_inputs = len(bool_poly_ring.gens())
    if num_outputs is None:
        assert max(lut) < 2**get_bitsize(lut)
        num_outputs = get_bitsize(lut)

    def component_function(b):
        """Return the component function <b,S> as a Boolean function."""
        m, n = num_inputs, num_outputs
        ZZ = sage.rings.integer_ring.ZZ
        return sage.crypto.boolean_function.BooleanFunction([ZZ(b & lut[x]).popcount() & 1 for x in range(1 << m)])

    anf = BooleanPolynomialVector()

    if bool_poly_ring is None:
        # the same as .algebraic_normal_form()
        bool_poly_ring = BooleanPolynomialRing(num_inputs, "x")

    assert len(bool_poly_ring.gens()) == num_inputs

    component = component_function(2 ** 0).algebraic_normal_form()
    # if still getting an error, make a singleton Boolean polynomial ring
    if component.parent() != bool_poly_ring:
        # otherwise, Operands come from different manager
        # substitute_variables doesn't require same parent bpr
        try:
            component = bool_poly_ring(component)
        except TypeError:
            component = substitute_variables(bool_poly_ring, bool_poly_ring.gens(), component)
    anf.append(component)

    for i in range(1, num_outputs):
        bb = 2 ** i
        component = component_function(bb).algebraic_normal_form()
        if component.parent() != bool_poly_ring:
            try:
                component = bool_poly_ring(component)
            except TypeError:
                component = substitute_variables(bool_poly_ring, bool_poly_ring.gens(), component)
        anf.append(component)

    assert all(anf[0].parent() == anf[i].parent() for i in range(1, len(anf)))

    return anf


def poly2lut(polynomial):
    """Return the LUT representation of a permutation polynomial.

        >>> x = PolynomialRing(GF(2**4, repr="int"), 'x').gen()
        >>> poly2lut(x)
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        >>> from sage.crypto.sboxes import AES
        >>> poly = AES.interpolation_polynomial()
        >>> poly2lut(poly) == list(AES)
        True

    """
    field = polynomial.base_ring()
    return [polynomial(field.fetch_int(i)).integer_representation() for i in range(len(field))]


def anf2lut(anf):
    """Return the LUT representation of a permutation given by its ANF.

        >>> x0, x1, x2, x3 = BooleanPolynomialRing(4, 'x').gens()
        >>> anf2lut([x0, x1, x2, x3])
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        >>> anf2lut(lut2anf(get_lut_inversion(4))) == get_lut_inversion(4)
        True

    """
    # ensure input is a list of Boolean polynomials
    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    if any(len(anf) != anf[i].parent().n_variables() for i in range(len(anf))):
        raise ValueError("input anf is not an (n,n)-bit function: \n{}".format([str(f) for f in anf]))

    n = len(anf)
    lut = []
    for x in sage.all.VectorSpace(GF(2), n):
        lut.append(vector2int(sage.all.vector(GF(2), [f(*x) for f in anf])))
    return lut


def anf2matrix(anf, input_vars=None):
    """Return the binary index_input_vars of the vectorial Boolean function given in ANF.

    If the anf is symbolic, index_input_vars must be given.
    The list input_vars can be given as a list of Boolean variables,
    strings or input variable indices.

        >>> x, y = BooleanPolynomialRing(names="x, y").gens()
        >>> anf2matrix([x + y, x])
        [1 1]
        [1 0]
        >>> x, y, a, b, c = BooleanPolynomialRing(names="x, y, a, b, c").gens()
        >>> anf = [0*x + (a + b)*y, c*x + y]
        >>> anf2matrix(anf, (0, 1))
        [    0 a + b]
        [    c     1]

    """
    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    bpr = anf[0].parent()
    assert all(bpr == f.parent() for f in anf)

    if input_vars is None:
        input_vars = bpr.gens()
    else:
        if isinstance(input_vars[0], int):
            input_vars = [bpr.gens()[i] for i in input_vars]
        elif isinstance(input_vars[0], str):
            input_vars = [bpr(vn) for vn in input_vars]
    assert all(v in bpr.gens() for v in input_vars)

    rows = []
    for f in anf:
        coeffs = get_all_symbolic_coeff(f, input_vars)
        current_row = []
        for v in input_vars:
            current_row.append(coeffs.get(v, 0))
        rows.append(current_row)
    return sage.all.matrix(ring=bpr, nrows=len(rows), entries=rows)


def get_ct_coeff(anf, input_vars=None):
    """Return the binary constant of the vectorial Boolean function given in ANF.

    If the anf is symbolic, index_input_vars must be given.
    The list input_vars can be given as a list of Boolean variables,
    strings or input variable indices.

        >>> from sage.crypto.sboxes import AES
        >>> hex(vector2int(get_ct_coeff(lut2anf(list(AES)))))
        '0x63'
        >>> x, y, a, b, c = BooleanPolynomialRing(names="x, y, a, b, c").gens()
        >>> anf = [x + x*a + x*b + x*y*(a*b + c) + (a*b*c), y + 1 + a + b + c]
        >>> get_ct_coeff(anf, [x, y])
        (a*b*c, a + b + c + 1)

    """
    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    bpr = anf[0].parent()
    assert all(bpr == f.parent() for f in anf)

    bin_ct = []
    for f in anf:
        if input_vars is None:
            bin_ct.append(f.constant_coefficient())
        else:
            bin_ct.append(get_symbolic_coeff(f, input_vars, 1))
    return sage.all.vector(bpr, bin_ct)


def int2vector(x, size):
    """Return the integer associated to the given binary vector.

        >>> pprint.pprint([int2vector(i, 3) for i in range(2**3)])
        [(0, 0, 0),
         (1, 0, 0),
         (0, 1, 0),
         (1, 1, 0),
         (0, 0, 1),
         (1, 0, 1),
         (0, 1, 1),
         (1, 1, 1)]

    """
    v = bin(x)[2:][::-1]
    v = v + "0" * (size - len(v))
    return sage.all.vector(GF(2), [int(v_i) for v_i in v])
    # return vector(GF(2), [(x >> i) & 1 for i in reversed(range(0, dimension))])


def vector2int(v):
    """Return the binary vector associated to the given integer.

        >>> vectors = sage.all.VectorSpace(GF(2), 3).list()
        >>> vectors
        [(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)]
        >>> [vector2int(v) for v in vectors]
        [0, 1, 2, 3, 4, 5, 6, 7]
        >>> assert all([i == vector2int(int2vector(i, 4)) for i in range(2**4)])

    """
    return int("0b" + "".join([str(v_i) for v_i in reversed(v)]), base=2)


def test_conversion(iterations=100):
    """Test the conversion functions

        >>> test_conversion(100)
        True

    """
    n = 4

    for _ in range(iterations):
        m = sage.all.random_matrix(GF(2), n, n, algorithm="unimodular")

        if m != poly2matrix(matrix2poly(m)):
            return False

        if matrix2lut(m) != anf2lut(matrix2anf(m)):
            return False

        if lut2matrix(matrix2lut(m)) != m:
            return False

        lut = sage.all.Permutations(range(2 ** n)).random_element()

        if poly2lut(lut2poly(lut)) != lut:
            return False

        if anf2lut(lut2anf(lut)) != lut:
            return False

        if hex_string2lut(lut2hex_string(lut, 1), 1) != lut:
            return False

        if m != anf2matrix(matrix2anf(m)):
            return False

    else:
        return True


# ---
# lut
# ---


def get_lut_inversion(n, field=None):
    """Return the LUT representing the inversion of GF(2**n).

        >>> lut = get_lut_inversion(4)
        >>> lut
        [0, 1, 9, 14, 13, 11, 7, 6, 15, 2, 12, 5, 10, 4, 3, 8]
        >>> lut2poly(lut)
        x^14

    """
    if field is None:
        field = GF(2 ** n, repr="int")
    return [0] + [(field.fetch_int(i) ** (-1)).integer_representation() for i in range(1, 2 ** n)]


def invert_lut(lut):
    """Return the inverse of a LUT

        >>> invert_lut([0, 1, 2, 3])
        [0, 1, 2, 3]
        >>> invert_lut(get_lut_inversion(4)) == get_lut_inversion(4)
        True
        >>> invert_lut(get_lut_inversion(9)) == get_lut_inversion(9)
        True

    """
    inv_lut = [None for _ in range(len(lut))]
    for i in range(len(lut)):
        inv_lut[lut[i]] = i
    return inv_lut


def get_bitsize(lut):
    """Return the bitsize of the given permutation.

        >>> get_bitsize(get_lut_inversion(4))
        4

    """
    bitsize = int(math.log(len(lut), 2))
    assert len(lut) == 2 ** bitsize, f"{len(lut)} != {2**bitsize}"
    return bitsize


def is_invertible(lut):
    """Return whether the function is a permutation.

        >>> is_invertible(get_lut_inversion(3))
        True
        >>> is_invertible([0, 1, 2, 0])
        False
        >>> is_invertible(get_lut_inversion(9))
        True
        >>> is_invertible([0 for i in range(2**9)])
        False
        >>> is_invertible([0, 1, 2, 4])
        False

    """
    return len(set([x for x in lut])) == 2 ** get_bitsize(lut) and max(lut) < 2**(get_bitsize(lut))


# ---
# anf
# ---


def str2bp(my_str, bpr_gens_dict):
    """Fast conversion of a string to a Boolean polynomial given the gens of a BooleanPolynomialRing.

        >>> bpr = BooleanPolynomialRing(names="x, y")
        >>> str2bp("x + y", bpr.gens_dict())
        x + y

    """
    assert isinstance(my_str, str)
    assert "^" not in my_str
    if my_str == "0":
        p = next(iter(bpr_gens_dict.values())).parent().zero()
    elif my_str == "1":
        p = next(iter(bpr_gens_dict.values())).parent().one()
    else:
        p = eval(my_str, bpr_gens_dict, {})
    return p


def get_num_inputs_anf(anf):
    """Return the number of inputs of the given vectorial anf"""
    # ensure input is a list of BooleanPolynomial
    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    bpr = None
    for f in anf:
        if bpr is None:
            bpr = f.parent()
        else:
            assert bpr == f.parent()
    return len(bpr.gens())
    # variables = set()
    # for f in anf:
    #     for var in f.parent().gens():
    #         variables.add(var)
    # return len(variables)


def is_balanced(anf):
    """Return whether the anf is balanced.

        >>> is_balanced(lut2anf(get_lut_inversion(4)))
        True
        >>> bpr = BooleanPolynomialRing(n=4, names="x")
        >>> is_balanced([bpr("x0*x1 + x0*x2 + x1*x2")])  # only 3-var 2-deg-homo balanced
        True
        >>> is_balanced([bpr("x0*x1 + x0*x2 + x0*x3 + x1*x2 + x1*x3")])
        True
        >>> is_balanced([bpr("x0*x1")])
        False
        >>> is_balanced([bpr("x0*x1 + x0*x2")])
        False

    """
    from collections import Counter
    n = get_num_inputs_anf(anf)
    counter = Counter()
    for w in sage.all.VectorSpace(sage.all.GF(2), n):
        counter[tuple([f(*w) for f in anf])] += 1
    return len(set(counter.values())) == 1


# TODO: add to docstring full_repr
def get_anf_coeffmatrix_str(anf, input_vars=None, full_repr=None):
    """Return the coefficient matrix of a (symbolic) anf as a string.

    If the anf is symbolic, input_vars must be given.
    The list input_vars can be given as a list of Boolean variables,
    strings or input variable indices.

    If the anf is symbolic and the number of symbolic coefficients
    is greater than 32, then instead of the coefficient matrix,
    a short string representation of the ANF is returned.

        >>> x, y, z = BooleanPolynomialRing(names="x, y, z").gens()
        >>> f0 = x*y*z + x*y + x*z + y*z + x + y + z + 1
        >>> f1 =         x*y +     + y*z + x +   + z + 1
        >>> f2 = 0*x
        >>> [f0, f1, f2]
        [x*y*z + x*y + x*z + x + y*z + y + z + 1, x*y + x + y*z + z + 1, 0]
        >>> get_anf_coeffmatrix_str([f0, f1, f2])
        [x*y*z|  x*y   x*z   y*z|    x     y     z|    1]
        [-----+-----------------+-----------------+-----]
        [    1|    1     1     1|    1     1     1|    1]
        [    0|    1     0     1|    1     0     1|    1]
        [    0|    0     0     0|    0     0     0|    0]
        >>> names = "x, y, z, ax, ay, az, a"
        >>> x, y, z, ax, ay, az, a = BooleanPolynomialRing(names=names).gens()
        >>> f0 = ax*x + ay*y + az*z
        >>> f1 =    x +      + z
        >>> f2 = 0*x
        >>> get_anf_coeffmatrix_str([f0, f1, f2], input_vars=[x, y, z])
        [ x  y  z]
        [--------]
        [ax ay az]
        [ 1  0  1]
        [ 0  0  0]
        >>> vars = BooleanPolynomialRing(names=["x0", "x1"] + ["a" + str(i) for i in range(32)]).gens()
        >>> anf = [vars[0]*sage.all.prod(vars[2:2+32]), vars[1]*vars[-2] + vars[-1]]
        >>> print(get_anf_coeffmatrix_str(anf, input_vars=["x0", "x1"]))  # doctest:+NORMALIZE_WHITESPACE
        [
            BooleanPolynomial(x0, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31)
            x1*a30 + a31
        ]

    """
    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    bpr = anf[0].parent()
    assert all(bpr == f.parent() for f in anf)

    if input_vars is None:
        index_input_vars = list(range(bpr.n_variables()))
    else:
        if isinstance(input_vars[0], int):
            index_input_vars = input_vars
        else:
            aux_dict = {str(v): i for i, v in enumerate(bpr.gens())}
            index_input_vars = [aux_dict[str(v)] for v in input_vars]

    if full_repr is None or full_repr is False:
        if len(index_input_vars) != len(bpr.gens()) and max(len(f.variables()) for f in anf) >= 32:
            from boolcrypt.functionalequations import _sp
            return "[\n\t" + "\n\t".join(_sp(component) for component in anf) + "\n]"

    list_mon2coeffs = [get_all_symbolic_coeff(f, index_input_vars) for f in anf]

    deglex_bpr = BooleanPolynomialRing(names=bpr.variable_names(), order="deglex")
    deglex_bpr_gens_dict = deglex_bpr.gens_dict()

    all_mons = set()
    for mon2coeffs in list_mon2coeffs:
        all_mons |= set(mon2coeffs)
    all_mons = sorted(all_mons, reverse=True, key=lambda x: str2bp(str(x), deglex_bpr_gens_dict))

    entries = [[0 for _ in range(len(all_mons))] for _ in range(len(anf) + 1)]
    entries[0] = all_mons
    for index_row in range(1, len(entries)):
        mon2coeff = list_mon2coeffs[index_row - 1]
        entries[index_row] = [mon2coeff.get(v, 0) for v in all_mons]

    matrix = sage.all.matrix(bpr, len(anf) + 1, len(all_mons), entries)

    subdivision = []
    if len(all_mons) > 0:  # anf != 0
        d = all_mons[-1].degree()
        for index_var in reversed(range(len(all_mons))):
            if all_mons[index_var].degree() > d:
                subdivision.append(index_var + 1)
                d = all_mons[index_var].degree()
    matrix.subdivide(row_lines=[1], col_lines=subdivision)

    return matrix


# ----------
# polynomial
# ----------


def pretty_poly(polynomial, ignore_coefficients=False):
    """Return a string representation of a finite field polynomial
    where the coefficients are represented as integers.

        >>> F = GF(2**8, 'z')
        >>> x = PolynomialRing(F, 'x').gen()
        >>> polynomial = F.fetch_int(1) + F.fetch_int(2) * x + F.fetch_int(4) * x**2
        >>> polynomial
        z^2*x^2 + z*x + 1
        >>> pretty_poly(polynomial)
        '4*x^2 + 2*x + 1'

    """
    s = ""
    exp2coeff = polynomial.dict()  # k, v = exp, coeff
    for exp in sorted(exp2coeff, reverse=True):
        coeff = exp2coeff[exp].integer_representation()
        if exp == 0:
            s += "{} + ".format(coeff)
        else:
            if (coeff == 1 or ignore_coefficients) and exp == 1:
                s += "x + "
            elif (coeff == 1 or ignore_coefficients) and exp > 1:
                s += "x^{} + ".format(exp)
            elif coeff > 1 and exp == 1:
                s += "{}*x + ".format(coeff)
            else:
                s += "{}*x^{} + ".format(coeff, exp)
    return s[:-3]


def normalize_poly(polynomial):
    """Return the normalized representation of a polynomial.

    Given f(x) = sum_{i=0}_{n} a_i x^i, return g(x) = c f(x + b) + d,
    such that g(0) = 0, g is monic, and g doesn't have x^{n-1} term
    (if n != 0 mod p for n = deg(f) and GF(p**r)).

        >>> F = GF(2**4, 'z')
        >>> x = PolynomialRing(F, 'x').gen()
        >>> normalize_poly(F.fetch_int(2) * x**2 + 1)
        x^2
        >>> normalize_poly(F.fetch_int(2) * x**3 + x**2 + 1)
        x^3 + (z^3 + z^2 + 1)*x

    See also Section 1.5 of arXiv:1211.6044 [math.NT]
    """
    x = polynomial.variables()[0]
    a_n = polynomial.leading_coefficient()
    n = polynomial.degree()

    c = a_n ** (-1)
    if n % polynomial.base_ring().characteristic() != 0:
        b = (-polynomial.monomial_coefficient(x ** (n - 1))) / (a_n * n)
        d = (-c) * sum([a_i * (b ** i) for i, a_i in enumerate(polynomial.list())])
    else:
        b = 0
        d = (-c) * polynomial.constant_coefficient()
    return c * polynomial(x + b) + d


# --------
# matrices
# --------


def pretty_container_with_matrices(matrices):
    """Print a sequence of matrices each one in a different line, similar to IPython."""
    s = pprint.pformat(matrices, indent=0)
    return s[0] + "\n" + s[1:-1] + "\n" + s[-1]


def get_canonical_matrix(rank, nrows, ncols=None):
    """Return the canonical matrix with given rank over GF(2).

    The square canonical matrix of rank r is the following matrix

        ( I_r   0   )
        (  0  O_n-r )

    Note that any matrix of dimension (n,m) and rank r is
    matrix equivalent to the canonical matrix of same dimension
    and rank k.

        >>> get_canonical_matrix(1, nrows=2, ncols=2)
        [1|0]
        [-+-]
        [0|0]
        >>> get_canonical_matrix(2, nrows=4, ncols=5)
        [1 0|0 0 0]
        [0 1|0 0 0]
        [---+-----]
        [0 0|0 0 0]
        [0 0|0 0 0]

    """
    if ncols is None:
        ncols = nrows
    return sage.all.block_diagonal_matrix(sage.all.identity_matrix(GF(2), rank),
                                          sage.all.zero_matrix(GF(2), nrows - rank, ncols - rank))


def find_monomial_matrices(n, field=None, condition=None, verbose=False):
    """Find the binary matrices corresponding to the polynomials a*x^(2^i)
    verifying some condition.

        >>> n = 4
        >>> condition = lambda m: m.column(0)[1:].is_zero() and m.submatrix(1, 1, n-1, n-1).is_invertible()
        >>> matrices = find_monomial_matrices(4, condition=condition)
        >>> print(pretty_container_with_matrices(matrices))  # not necessary in IPython
        [
        [1 0 0 0]
        [0 1 0 0]
        [0 0 1 0]
        [0 0 0 1],
        [1 0 1 0]
        [0 0 1 0]
        [0 1 0 1]
        [0 0 0 1],
        [1 1 1 1]
        [0 1 0 1]
        [0 0 1 1]
        [0 0 0 1],
        [1 1 0 0]
        [0 0 1 1]
        [0 1 0 0]
        [0 0 0 1]
        ]

    """
    assert condition is not None
    if field is None:
        field = GF(2 ** n, repr="int")

    x = PolynomialRing(field, 'x').gen()  # temporary var

    matrices = []
    for alpha in range(1, 2 ** n):
        alpha = field.fetch_int(alpha)
        for exp in range(n):
            m = poly2matrix(alpha * (x ** 2 ** exp))
            if condition(m):
                matrices.append(m)
                if verbose:
                    print("alpha: {}, exp: {}, matrix:\n{}\n".format(alpha, exp, m))
    return matrices


def lin_poly2pseudocirc_matrix(polynomial):
    """Return the pseudo-circulant matrix associated to a linearized polynomial.

    A linearized polynomial is invertible iff its associated matrix
    is non-singular.

        >>> n = 4
        >>> z0 = GF(2**n).gen()
        >>> R = PolynomialRing(GF(2**n), 'x')
        >>> x = R.gen()
        >>> lin_poly2pseudocirc_matrix(x + z0*x**2 + (z0 + 1)*x**4)
        [       1        0       z4 z4^2 + 1]
        [      z4        1        0     z4^2]
        [  z4 + 1     z4^2        1        0]
        [       0 z4^2 + 1   z4 + 1        1]
        >>> for _ in range(100):
        ...     poly = R.random_element()
        ...     poly -= poly.constant_coefficient()
        ...     assert lin_poly2pseudocirc_matrix(poly).is_invertible() == poly2matrix(poly).is_invertible()

    """
    field = polynomial.base_ring()
    n = field.degree()
    pseudocirc_matrix = sage.all.zero_matrix(field, n, n)
    exp2coeff = polynomial.dict()
    for i in range(n):
        for j in range(n):
            exp = 2 ** ((j - i) % n)
            # L[i, j] = coeff(x^2^(j - i))^2^i  (j - i % n)
            if exp in exp2coeff:
                pseudocirc_matrix[i, j] = exp2coeff[exp] ** (2 ** i)
    return pseudocirc_matrix.transpose()


# -----------
# composition
# -----------


def compose_lut(left, right):
    """Return the LUT representing F(G(x)).

    F and G can be given as LUTs, matrices or affine functions,
    but one of them should be given as a LUT.

        >>> compose_lut(get_lut_inversion(4), get_lut_inversion(4))
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        >>> rm = sage.all.random_matrix(GF(2), 4, 4, algorithm="unimodular")
        >>> compose_lut(matrix2lut(rm), rm.inverse())
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        >>> compose_lut([rm.inverse(), rm.inverse() * sage.all.vector([1, 0, 0, 0])], [x.__xor__(1) for x in matrix2lut(rm)])
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        >>> lut = get_lut_inversion(4)
        >>> field = GF(2**4, repr="int")
        >>> right_self = field.fetch_int(3) * PolynomialRing(field, 'x').gen()
        >>> left_self = right_self
        >>> left_self(lut2poly(lut)(right_self))  # checking is a self_equivalence
        x^14
        >>> right_self, left_self = poly2matrix(right_self), poly2matrix(left_self)
        >>> lut2poly(compose_lut(left_self, compose_lut(lut, right_self)))
        x^14

    """
    from sage.structure.element import is_Matrix
    new_lut = []
    if is_Matrix(left):
        for i in range(len(right)):
            new_lut.append(vector2int(left * int2vector(right[i], left.nrows())))
    elif len(left) == 2 and is_Matrix(left[0]):
        if isinstance(left[1], int):
            bin_ct = int2vector(left[1], left[0].nrows())
        else:
            bin_ct = left[1]
        for i in range(len(right)):
            new_lut.append(vector2int(left[0] * int2vector(right[i], left[0].nrows()) + bin_ct))
    elif is_Matrix(right):
        for i in range(len(left)):
            new_lut.append(left[vector2int((right * int2vector(i, right.nrows())))])
    elif len(right) == 2 and is_Matrix(right[0]):
        if isinstance(right[1], int):
            bin_ct = int2vector(right[1], right[0].nrows())
        else:
            bin_ct = right[1]
        for i in range(len(left)):
            new_lut.append(left[vector2int(right[0] * int2vector(i, right[0].nrows()) + bin_ct)])
    else:
        assert len(left) == len(right)
        for i in right:
            new_lut.append(left[i])
    return new_lut


def compose_affine(left_matrix, left_ct, right_matrix, right_ct):
    """Return the composition of two affine functions as a (matrix, vector) pair.

        >>> left_rot = sage.all.matrix.circulant(sage.all.vector(GF(2), [0,0,0,1]))
        >>> compose_affine(left_rot.inverse(), 1, left_rot, 1)
        [[1 0 0 0]
        [0 1 0 0]
        [0 0 1 0]
        [0 0 0 1], (1, 0, 0, 1)]

    """
    new_matrix = left_matrix * right_matrix
    if isinstance(right_ct, int):
        right_ct = int2vector(right_ct, right_matrix.nrows())
    if isinstance(left_ct, int):
        left_ct = int2vector(left_ct, left_matrix.nrows())
    new_ct = left_ct + (left_matrix * right_ct)
    return [new_matrix, new_ct]


# deprecated
def compose_lut_matrix(lut, bin_matrix, bin_ct=0):
    """Return the LUT representing F A, F given as a lut and
    A given as a pair of a binary matrix and a binary constant"""
    return compose_lut(lut, [bin_matrix, bin_ct])


# deprecated
def compose_matrix_lut(bin_matrix, lut, bin_ct=0):
    """Return the LUT representing A F, F given as a lut and
    A given as a pair of a binary matrix and a binary constant"""
    return compose_lut([bin_matrix, bin_ct], lut)


# @sage.all.parallel
# def _substitute_anf_component(component, replacement, bpr, index=None):
#     """Substitute variables from an ANF component according to the given dictionary."""
#     if isinstance(component, int):
#         return bpr(component)
#     new_component = component.subs(replacement)
#     if isinstance(new_component, int) or new_component.parent() != bpr:
#         return bpr(new_component)
#     else:
#         return new_component


def substitute_anf(anf, replacement, output_bool_poly_ring):
    """Substitute variables from the given anf according to the given dictionary.

        >>> B = BooleanPolynomialRing(4, "x")
        >>> x0, x1, x2, x3 = B.gens()
        >>> identity = [x0, x1, x2, x3]
        >>> for p in substitute_anf(identity, {x0:x0, x3:x3}, B): print(p)
        x0
        x1
        x2
        x3
        >>> inv_anf = lut2anf(get_lut_inversion(4))
        >>> B = inv_anf[0].parent()
        >>> for p in substitute_anf(inv_anf, {B.gens()[0]: B(0)}, B): print(p)
        x1*x2*x3 + x1*x2 + x1 + x2 + x3
        x1*x2 + x1*x3 + x3
        x2 + x3
        x1*x2*x3 + x1*x3 + x1 + x2*x3 + x2 + x3

    """
    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    new_anf = BooleanPolynomialVector()

    n_vars = anf[0].parent().n_variables()
    slow_sub = len(replacement) < (n_vars // 4) and n_vars < 32

    if not slow_sub:
        ordered_replacement = []
        anf_bpr = anf[0].parent()
        str2key = {str(var): var for var in replacement}
        for vn in anf_bpr.variable_names():
            if vn in str2key:
                value = replacement[str2key[vn]]
            else:
                value = vn
            ordered_replacement.append(output_bool_poly_ring(value))

    for f_i in anf:
        if isinstance(f_i, int):
            new_anf.append(output_bool_poly_ring(f_i))
        else:
            if slow_sub:
                f_i_replaced = f_i.subs(replacement)  # .subs() can be an int
            else:
                # substitute_variables doesn't call singular, which has memory limit
                # in f[i], the i-th variable is replaced by g[i]
                f_i_replaced = substitute_variables(output_bool_poly_ring, ordered_replacement, f_i)
            if isinstance(f_i_replaced, int) or f_i.parent() != output_bool_poly_ring:
                new_anf.append(output_bool_poly_ring(f_i_replaced))
            else:
                new_anf.append(f_i_replaced)

    # new_anf = BooleanPolynomialVector([output_bool_poly_ring(0) for _ in range(len(anf))])
    # for arg, output in _substitute_anf_component([(f_i, replacement, output_bool_poly_ring, i)
    #                                               for i, f_i in enumerate(anf)]):
    #     new_anf[arg[0][-1]] = output

    assert all(id(new_anf[0].parent()) == id(new_anf[i].parent()) for i in range(1, len(new_anf)))

    return new_anf


# @sage.all.parallel()
# def _compose_anf_component(component, vectorial_anf, bpr, index=None):
#     """Compose a component with a vectorial ANF."""
#     return pbori.substitute_variables(bpr, vectorial_anf, component)


def compose_anf_fast(left_anf, right_anf):
    """Compose two functions compatible given by their anf.

    The output size of right_anf must be the same as the input size of left_anf.

        >>> x0, x1, x2, x3 = BooleanPolynomialRing(4, "x").gens()
        >>> identity = BooleanPolynomialVector([x0, x1, x2, x3])
        >>> for p in compose_anf_fast(identity, identity): print(p)
        x0
        x1
        x2
        x3
        >>> inversion = lut2anf(get_lut_inversion(4))
        >>> for p in compose_anf_fast(inversion, inversion): print(p)
        x0
        x1
        x2
        x3

    """
    """
    # modifying one single variable is faster with substitute_anf
    from sage.rings.polynomial.pbori.pbori import BooleanPolynomialVector
    n = 32  # num_inputs = num_components
    B = BooleanPolynomialRing(n, "x");
    f = BooleanPolynomialVector()
    for i in range(n):  
        f.append(B.random_element(degree=2, terms=Infinity))
    g = BooleanPolynomialVector(B.gens())
    g[-1] = B(0)
    sleep(1)
    %timeit compose_anf_fast(f, g)
    sleep(1)
    %timeit substitute_anf(f, {g[-1]: B(0)}, B)
    # ows, compose_anf_fast is faster
    g = BooleanPolynomialVector()
    for i in range(n):  
        g.append(B.random_element(degree=1, terms=Infinity))
    replacements = {x_i: g_i for x_i, g_i in zip(B.gens(), g)}
    sleep(1)
    %timeit compose_anf_fast(f, g)
    sleep(1)
    %timeit substitute_anf(f, replacements, B)
    """
    f, g = left_anf, right_anf

    bpr_f = f[0].parent()  # Boolean polynomial ring
    bpr_g = g[0].parent()  # Boolean polynomial ring

    assert all(bpr_f == f[i].parent() for i in range(1, len(f)))
    assert all(bpr_g == g[i].parent() for i in range(1, len(g)))
    assert len(g) == bpr_f.n_variables(), "{} != {}".format(len(g), bpr_f.n_variables())
    assert not isinstance(f, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    assert not isinstance(g, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    # assert isinstance(g, BooleanPolynomialVector)

    fg = BooleanPolynomialVector()
    for i in range(len(f)):
        # in f[i], the i-th variable is replaced by g[i]
        fg.append(substitute_variables(bpr_g, g, f[i]))

    # fg = BooleanPolynomialVector([bpr(0) for _ in range(len(f))])
    # for argument, output in _compose_anf_component([(f_i, g, bpr, i) for i, f_i in enumerate(f)]):
    #     fg[argument[0][-1]] = output

    assert all(bpr_g == fg[i].parent() for i in range(1, len(fg)))

    return fg


# -------------
# concatenation
# -------------


def concatenate_lut(left_lut, right_lut):
    """Return the concatenation of two permutations F || G given by their lut.

        >>> n = 3
        >>> identity = [i for i in range(2**n)]
        >>> for p in lut2anf(concatenate_lut(identity, identity)): print(p)
        x0
        x1
        x2
        x3
        x4
        x5
        >>> inversion = get_lut_inversion(n)
        >>> for p in lut2anf(inversion): print(p)
        x0 + x1*x2 + x1 + x2
        x0*x1 + x2
        x0*x2 + x1 + x2
        >>> for p in lut2anf(concatenate_lut(inversion, inversion)): print(p)
        x0 + x1*x2 + x1 + x2
        x0*x1 + x2
        x0*x2 + x1 + x2
        x3 + x4*x5 + x4 + x5
        x3*x4 + x5
        x3*x5 + x4 + x5

    """
    new_lut = []
    n_left = int(math.log(len(left_lut), 2))
    n_right = int(math.log(len(right_lut), 2))
    for x in range(2 ** (n_left + n_right)):
        x = int2vector(x, n_left + n_right)
        x_left, x_right = x[:n_left], x[-n_left:]
        y_left = int2vector(left_lut[vector2int(x_left)], n_left)
        y_right = int2vector(right_lut[vector2int(x_right)], n_right)
        y = vector2int(list(y_left) + list(y_right))
        new_lut.append(y)
    return new_lut


def concatenate_anf(left_anf, right_anf, prefix="x", input_vars_left=None, input_vars_right=None):
    """Return the concatenation of two functions given by their anf

    By default, the input variables of the concatenation are set to x0, x1, ...
    If prefix=None, the input variables are set to the input variables
    of left concatenated to the input variables of right (assuming they
    don't collide).

    If left/right are symbolic anf, input_vars_left/right must be given.

    The lists input_vars_* can be given as a list of Boolean variables or strings.

        >>> x, = BooleanPolynomialRing(1, "x").gens()
        >>> concatenation = concatenate_anf([x], [x])
        >>> list(concatenation)
        [x0, x1]
        >>> concatenation[0].parent()
        Boolean PolynomialRing in x0, x1
        >>> left_anf, right_anf = [BooleanPolynomialRing(1, "x")("x")], [BooleanPolynomialRing(1, "y")("y")]
        >>> concatenation = concatenate_anf(left_anf, right_anf, prefix=None)
        >>> list(concatenation)
        [x, y]
        >>> concatenation[0].parent()
        Boolean PolynomialRing in x, y
        >>> x, a, b = BooleanPolynomialRing(3, "x, a, b").gens()
        >>> concatenation = concatenate_anf([x + a], [x + a*b], input_vars_left=[x], input_vars_right=["x"])
        >>> list(concatenation)
        [x0 + a, x1 + a*b]
        >>> concatenation[0].parent()
        Boolean PolynomialRing in x0, x1, a, b

    """
    assert not isinstance(left_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    assert not isinstance(right_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    bpr_left = left_anf[0].parent()
    bpr_right = right_anf[0].parent()
    assert all(bpr_left == f.parent() for f in left_anf)
    assert all(bpr_right == f.parent() for f in right_anf)

    if input_vars_left is None:
        input_vars_left = bpr_left.gens()
    if prefix is not None:
        new_input_names = [prefix + str(i) for i in range(len(input_vars_left))]
        bpr_left = BooleanPolynomialRing(names=new_input_names + [vn for vn in bpr_left.variable_names() if vn not in new_input_names])
        rep = {bpr_left(x_i): bpr_left(v_i) for x_i, v_i in zip(input_vars_left, new_input_names)}
        left_anf = substitute_anf(left_anf, rep, bpr_left)
        # left_anf = [bpr_left(f).subs(rep) for f in left_anf]
        old_input_names = [str(v) for v in input_vars_left if str(v) not in new_input_names]
        bpr_left = BooleanPolynomialRing(names=[vn for vn in bpr_left.variable_names() if vn not in old_input_names])
        left_anf = [bpr_left(f) for f in left_anf]

    if input_vars_right is None:
        input_vars_right = bpr_right.gens()
    if prefix is not None:
        new_input_names = [prefix + str(i + len(input_vars_left)) for i in range(len(input_vars_right))]
        bpr_right = BooleanPolynomialRing(names=new_input_names + [vn for vn in bpr_right.variable_names() if vn not in new_input_names])
        rep = {bpr_right(x_i): bpr_right(v_i) for x_i, v_i in zip(input_vars_right, new_input_names)}
        right_anf = substitute_anf(right_anf, rep, bpr_right)
        # right_anf = [bpr_right(f).subs(rep) for f in right_anf]
        old_input_names = [str(v) for v in input_vars_right if str(v) not in new_input_names]
        bpr_right = BooleanPolynomialRing(names=[vn for vn in bpr_right.variable_names() if vn not in old_input_names])
        right_anf = [bpr_right(f) for f in right_anf]

    if prefix is None:
        assert len(input_vars_left) + len(input_vars_right) == len(set(input_vars_left + input_vars_right)), \
            f"${input_vars_left} ${input_vars_right} ${input_vars_left + input_vars_right}"

    names_left, names_right = list(bpr_left.variable_names()), list(bpr_right.variable_names())
    nl, nr = len(input_vars_left), len(input_vars_right)
    names = names_left[:nl] + names_right[:nr] + names_left[nl:]
    names = names + [n for n in names_right[nr:] if n not in names]
    bpr_concat = BooleanPolynomialRing(names=names)

    concatenation = BooleanPolynomialVector()
    for f in left_anf + right_anf:
        concatenation.append(bpr_concat(f))

    assert all(bpr_concat == f.parent() for f in concatenation)

    return concatenation


def concatenate_anf_fast(*list_anfs):
    """Return the concatenation of several non-symbolic functions given by their anf-

    The inputs of each function must be x0, x1, ...

        >>> x0, = BooleanPolynomialRing(1, "x0").gens()
        >>> list(concatenate_anf_fast([x0], [x0], [x0], [x0]))
        [x0, x1, x2, x3]

    """
    num_inputs = []
    for anf in list_anfs:
        assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
        ni = get_num_inputs_anf(anf)
        assert anf[0].parent().variable_names() == tuple("x" + str(i) for i in range(ni))
        num_inputs.append(ni)

    bpr_concat = BooleanPolynomialRing(sum(num_inputs), "x")

    concatenation = BooleanPolynomialVector()
    offset = 0
    for i, anf in enumerate(list_anfs):
        rep = {"x" + str(i): bpr_concat("x" + str(i + offset)) for i in range(num_inputs[i])}
        offset += num_inputs[i]
        anf = substitute_anf(anf, rep, bpr_concat)
        # anf = [bpr_concat(f).subs(rep) for f in anf]
        for f in anf:
            concatenation.append(f)

    assert all(bpr_concat == f.parent() for f in concatenation)

    return concatenation


# --------
# size anf
# --------


def get_upper_bound_monomials(alg_deg, domain, int2log2=False):
    """Return the maximum number of monomials a function can have with given algebraic degree.

    If the domain is GF(2)**n, return the maximum number of GF(2) monomials of a component.
    If the domain is GF(2**n), return the maximum number of GF(2**n) monomials
    of the univariate representation.

        >>> get_upper_bound_monomials(7, GF(2)**8)
        255
        >>> get_upper_bound_monomials(7, GF(2**8), int2log2=True)
        7
        >>> n, d = 4, 2
        >>> p = sage.all.BooleanPolynomialRing(4, 'x').random_element(d, terms=sage.all.Infinity)
        >>> len(p) <= get_upper_bound_monomials(d, GF(2)**n)
        True

    """
    # n size of the field (in log) and k the algebraic degree
    if hasattr(domain, "dimension"):
        n = domain.dimension()
    else:
        n = domain.degree()
    bound = sum(sage.all.binomial(n, i) for i in range(alg_deg + 1))  # * n
    if int2log2:
        return int(math.log(bound, 2))
    else:
        return bound


def get_upper_bound_gf2_splitdegree_monomials(nx, ny, dx, dy, dxy, int2log2=False):
    """Return the maximum number of monomials a bit-function with split degree.

    Return the maximum number of monomoials of a (nx,ny)-bit function
    f(x, y) with x-degree dx and y-degree dy and mixed degree dxy.

        >>> get_upper_bound_monomials(4, GF(2)**8)
        163
        >>> get_upper_bound_gf2_splitdegree_monomials(4, 4, 2, 2, 4)
        121
        >>> get_upper_bound_gf2_splitdegree_monomials(4, 4, 4, 1, 4)
        76

    """
    assert 1 <= dx <= nx
    assert 1 <= dy <= ny
    bound = 0
    for ix in range(dx + 1):
        aux_x = sage.all.binomial(nx, ix)
        aux_y = 0
        for iy in range(dy + 1):
            if ix > 0 and iy > 0 and ix + iy > dxy:
                break
            aux_y += sage.all.binomial(ny, iy)
        bound += aux_x*aux_y
    if int2log2:
        return int(math.log(bound, 2))
    else:
        return bound


def get_megabyte_size_anf(n, d, m=None):
    """Return the maximum megabytes size of a system of m Boolean functions,
    where each n-bit Boolean function is of degree d.

    This is assuming we represent the coefficient of a monomial
    of each Boolean function with a unique n-bit integer.
    """
    if m is None:
        m = n
    bitsize = m * get_upper_bound_monomials(d, GF(2) ** n)
    return bitsize / 8000000.0


def get_megabyte_size_splitdegree_anf(nx, ny, dx, dy, dxy, m=None):
    """Return the maximum megabytes size of a system of m Boolean functions,
    where each (nx, ny)-bit Boolean function is of x-degree dx and y-degree dy
    and mixed degree dxy.

    This is assuming we represent the coefficient of a monomial
    of each Boolean function with a unique n-bit integer.
    """
    if m is None:
        m = nx + ny
    bitsize = m * get_upper_bound_gf2_splitdegree_monomials(nx, ny, dx, dy, dxy)
    return bitsize / 8000000.0


# ---------------
# Sbox properties
# ---------------


def get_algebraic_degree(lut, only_maximum=True):
    """Return the maximum and minumum algebraic degree of the canonical components of a permutation.

        >>> get_algebraic_degree(get_lut_inversion(4))
        3
        >>> get_algebraic_degree(get_lut_inversion(8), only_maximum=False)
        (7, 7)
        >>> get_algebraic_degree(get_lut_inversion(9), only_maximum=False)
        (8, 8)

    """
    bitsize = get_bitsize(lut)

    def component_function(b):
        """Return the component function <b,S> as a Boolean function."""
        m, n = bitsize, bitsize
        ZZ = sage.rings.integer_ring.ZZ
        return sage.crypto.boolean_function.BooleanFunction([ZZ(b & lut[x]).popcount() & 1 for x in range(1 << m)])

    maximum = 0
    minimum = get_bitsize(lut)

    for i in range(bitsize):
        deg_Si = component_function(1 << i).algebraic_degree()
        if deg_Si > maximum:
            maximum = deg_Si
            if deg_Si == bitsize - 1 and only_maximum:
                return maximum
        if not only_maximum:
            minimum = min(minimum, deg_Si)
        if deg_Si < minimum:
            minimum = deg_Si
    if only_maximum:
        return maximum
    else:
        return maximum, minimum


def get_all_algebraic_degrees(lut):
    """Return the algebraic degree of all components of a permutation.

        >>> lut = get_lut_inversion(4)
        >>> get_all_algebraic_degrees(lut)
        [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]
        >>> import collections
        >>> print(collections.Counter(get_all_algebraic_degrees(lut)))
        Counter({3: 15})

    """
    # warnings.warn("get_all_algebraic_degrees() has a memory bug when doctesting")
    from sage.crypto.sbox import SBox as createSbox
    sbox = createSbox(lut)
    size = len(lut)
    # n = int(math.log(len(lut), 2))
    # assert 2**n == size
    degrees = []
    for b in range(1, size):
        component = sbox.component_function(b)
        degrees.append(component.algebraic_degree())
    return degrees


def get_differential_uniformity(lut):
    """See sage.crypto.sbox.Sbox.maximal_difference_probability_absolute

    In other words, the biggest entry in the DDT table for a non-zero differential.

        >>> get_differential_uniformity(get_lut_inversion(4))
        4
        >>> get_differential_uniformity(get_lut_inversion(8))
        4

    """
    from sage.crypto.sbox import SBox as createSbox
    return createSbox(lut).maximal_difference_probability_absolute()


def get_linearity(lut):
    """See sage.crypto.sbox.Sbox.maximal_linear_bias_absolute

    In other words, the biggest entry in the LAT table for a non-zero input mask.

        >>> get_linearity(get_lut_inversion(4))
        4
        >>> get_linearity(get_lut_inversion(8))
        16

    """
    from sage.crypto.sbox import SBox as createSbox
    return createSbox(lut).maximal_linear_bias_absolute()


def has_linear_structures(lut):
    """See sage.crypto.sbox.Sbox.has_linear_structures

        >>> from sage.crypto.sboxes import AES, PRESENT
        >>> has_linear_structures(list(AES))
        False
        >>> has_linear_structures(list(PRESENT))
        True

    """
    from sage.crypto.sbox import SBox as createSbox
    sbox = createSbox(lut)
    return sbox.has_linear_structure()


def get_all_components(lut):
    """Return all components (in ANF) of a permutation.

        >>> pprint.pprint(get_all_components(get_lut_inversion(4)))
        {1: x0*x1*x2 + x0*x2 + x0 + x1*x2*x3 + x1*x2 + x1 + x2 + x3,
         2: x0*x1*x3 + x0*x1 + x0*x2 + x1*x2 + x1*x3 + x3,
         3: x0*x1*x2 + x0*x1*x3 + x0*x1 + x0 + x1*x2*x3 + x1*x3 + x1 + x2,
         4: x0*x1 + x0*x2*x3 + x0*x2 + x0*x3 + x2 + x3,
         5: x0*x1*x2 + x0*x1 + x0*x2*x3 + x0*x3 + x0 + x1*x2*x3 + x1*x2 + x1,
         6: x0*x1*x3 + x0*x2*x3 + x0*x3 + x1*x2 + x1*x3 + x2,
         7: x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x3 + x1 + x3,
         8: x0*x3 + x1*x2*x3 + x1*x3 + x1 + x2*x3 + x2 + x3,
         9: x0*x1*x2 + x0*x2 + x0*x3 + x0 + x1*x2 + x1*x3 + x2*x3,
         10: x0*x1*x3 + x0*x1 + x0*x2 + x0*x3 + x1*x2*x3 + x1*x2 + x1 + x2*x3 + x2,
         11: x0*x1*x2 + x0*x1*x3 + x0*x1 + x0*x3 + x0 + x2*x3 + x3,
         12: x0*x1 + x0*x2*x3 + x0*x2 + x1*x2*x3 + x1*x3 + x1 + x2*x3,
         13: x0*x1*x2 + x0*x1 + x0*x2*x3 + x0 + x1*x2 + x1*x3 + x2*x3 + x2 + x3,
         14: x0*x1*x3 + x0*x2*x3 + x1*x2*x3 + x1*x2 + x1 + x2*x3 + x3,
         15: x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x0*x2 + x0 + x2*x3 + x2}

    """
    from sage.crypto.sbox import SBox as createSbox
    sbox = createSbox(lut)
    size = len(lut)
    all_components = {}
    for b in range(1, size):  # excluding b=0
        component = sbox.component_function(b)
        all_components[b] = component.algebraic_normal_form()
    return all_components


# -------------------------
# symbolic AMF
# -------------------------


def get_symbolic_anf(degree, num_inputs, num_outputs, ct_terms=True,
                     prefix_inputs="x", prefix_coeffs="a",
                     coeff2ct=None, coeff2expr=None, bpr=None, return_varnames=False):
    """Return an ANF with symbolic coefficients given as Boolean variables.

    Parameters:
        - prefix_inputs: the prefix string to label the input variables of the ANF.
        - prefix_coeffs: the prefix string to label the coefficients of the ANF.
        - degree: the algebraic degree of the ANF.
        - ct_terms: whether to consider constant terms
        - num_inputs, num_outputs: the dimension of the ANF
        - coeff2ct: a dictionary mapping string/Boolean coefficient labels to constants
          to replace those coefficients to fixed values.
        - coeff2expr: a dictionary mapping string/Boolean coefficient labels to Boolean
          to replace those coefficients to Boolean expressions (bpr must be given)
        - bpr: if given, each ANF component is an element of given Boolean poly ring
        - return_varnames: if True, return the varnames of the parent BooleanPolynomialRing
          of the symbolic anf.

        >>> get_anf_coeffmatrix_str(get_symbolic_anf(1, 3, 3), input_vars=[0, 1, 2])
        [  x0   x1   x2|   1]
        [--------------+----]
        [a0_0 a0_1 a0_2|  a0]
        [a1_0 a1_1 a1_2|  a1]
        [a2_0 a2_1 a2_2|  a2]
        >>> anf = get_symbolic_anf(2, 3, 1, ct_terms=False, prefix_inputs="y",
        ...     prefix_coeffs="b", coeff2ct={"b0_0": 1})
        >>> get_anf_coeffmatrix_str(anf, input_vars=[0, 1, 2])
        [ y0*y1  y0*y2  y1*y2|    y0     y1     y2]
        [--------------------+--------------------]
        [b0_0_1 b0_0_2 b0_1_2|     1   b0_1   b0_2]
        >>> bpr = BooleanPolynomialRing(names=["x0", "a0_0", "b"])
        >>> anf = get_symbolic_anf(1, 1, 1, ct_terms=False, prefix_inputs="x",
        ...     prefix_coeffs="a", coeff2expr={"a0_0": "b"}, bpr=bpr)
        >>> get_anf_coeffmatrix_str(anf, input_vars=["x0"])
        [x0]
        [--]
        [ b]
        >>> get_symbolic_anf(1, 3, 3, return_varnames=True)
        ['x0', 'x1', 'x2', 'a0_0', 'a0_1', 'a0_2', 'a0', 'a1_0', 'a1_1', 'a1_2', 'a1', 'a2_0', 'a2_1', 'a2_2', 'a2']

    """
    if coeff2expr is not None and len(coeff2expr) > 0:
        assert bpr is not None

    if return_varnames:
        assert bpr is None

    if coeff2ct is None and coeff2expr is None:
        coeff2val = {}
    elif coeff2ct is not None and coeff2expr is None:
        coeff2val = coeff2ct
    elif coeff2ct is None and coeff2expr is not None:
        coeff2val = coeff2expr
    else:
        coeff2val = {**coeff2ct, **coeff2expr}

    all_coeff_mon = []
    for i in range(num_outputs):
        component_coeff_mon = []
        for current_degree in reversed(range(1, degree + 1)):
            for j in itertools.combinations(range(num_inputs), current_degree):
                # in the i-component, Ai_j[0]_..._j[-1] is the coeff
                #   associated to Xj[0] * ... * Xj[-1]
                coeff = "{}{}" + "_{}" * len(j)
                coeff = coeff.format(prefix_coeffs, i, *j)
                if coeff in coeff2val:
                    coeff = coeff2val[coeff]
                elif bpr is not None:
                    coeff = bpr(coeff)
                    if coeff in coeff2val:
                        coeff = coeff2val[coeff]
                mon = '*'.join([f"{prefix_inputs}{index_var}" for index_var in j])
                component_coeff_mon.append([coeff, mon])

        if ct_terms:
            # the ct terms are labelled Ai
            coeff = "{}{}".format(prefix_coeffs, i)
            if coeff in coeff2val:
                coeff = coeff2val[coeff]
            elif bpr is not None:
                coeff = bpr(coeff)
                if coeff in coeff2val:
                    coeff = coeff2val[coeff]
            component_coeff_mon.append([coeff, 1])
        else:
            component_coeff_mon.append([0, 1])

        all_coeff_mon.append(component_coeff_mon)

    if bpr is None:
        varnames = [prefix_inputs + str(i) for i in range(num_inputs)]
        for component_coeff_mon in all_coeff_mon:
            for coeff, _ in component_coeff_mon:
                if coeff not in [0, 1]:
                    varnames.append(coeff)
        if return_varnames:
            return varnames
        bpr = BooleanPolynomialRing(len(varnames), varnames)

    anf = BooleanPolynomialVector()
    for component_coeff_mon in all_coeff_mon:
        component = bpr.zero()
        for coeff, mon in component_coeff_mon:
            component += bpr(coeff) * bpr(mon)
        anf.append(component)
    return anf


def get_symbolic_coeff(bool_poly, input_vars, monomial):
    """Return the symbolic coefficient of a symbolic Boolean polynomial.

    A symbolic Boolean function is a Boolean function of the form
    f(x1, dots, xn-1, a1, dots,), where xi are the inputs
    and ai are parameters.

    Given a monomial x_i1 * dots * x_ir, it returns the
    symbolic coefficient (in terms of ai) of the monomial
    x_i1 * dots * x_ir.

    It is assumed the given monomial only contains input_vars variables.

    The list input_vars can be given as a list of Boolean variables,
    strings or input variable indices.

        >>> x, y, a, b, c = BooleanPolynomialRing(names="x, y, a, b, c").gens()
        >>> poly = x + x*a + x*b + x*y*(a*b + c) + (a*b*c)
        >>> get_symbolic_coeff(poly, ("x", "y"), "x")
        a + b + 1
        >>> get_symbolic_coeff(poly, (x, y, a, b, c), x)
        1
        >>> poly.monomial_coefficient(x)
        1
        >>> get_symbolic_coeff(poly, [0, 1], 1)
        a*b*c

    """
    if isinstance(monomial, int):
        assert monomial == 1
        monomial_vars = []
    else:
        monomial_vars = bool_poly.parent()(monomial).variables()
    if isinstance(input_vars[0], int):
        input_vars = [bool_poly.ring().gens()[i] for i in input_vars]
    elif isinstance(input_vars[0], str):
        input_vars = [bool_poly.parent()(vn) for vn in input_vars]

    if len(input_vars) == len(bool_poly.parent().gens()):
        return bool_poly.monomial_coefficient(monomial)

    good_indices = []
    bad_indices = []
    for i, var in enumerate(bool_poly.ring().gens()):
        if var in monomial_vars:
            good_indices.append(i)
        elif var in input_vars:
            bad_indices.append(i)

    monomials_set = bool_poly.set()
    for i in good_indices:
        monomials_set = monomials_set.subset1(i)
    for j in bad_indices:
        monomials_set = monomials_set.subset0(j)
    return bool_poly.ring()(monomials_set)


def get_all_symbolic_coeff(bool_poly, input_vars, ignore_terms_of_deg_strictly_less=0):
    """Return all the symbolic coefficients of a symbolic Boolean polynomial.

    A symbolic Boolean function is a Boolean function of the form
    f(x1, dots, xn-1, a1, dots,), where xi are the inputs
    and ai are parameters.

    It returns a dictionary with entries (X, A), where X is a monomial with input vars
    and A is a polynomial of symbolic variables corresponding to the monomial X.
    For example, the entry (x_0*x_1, a_0a_1+_a2), means the symbolic polynomial
    contains the monomial (a_0a_1+_a2) * x_0_x1 (after grouping).

    By default, the ct terms are always returned in the dictionary
    mapping the monomial to the coefficients.

    The list input_vars can be given as a list of Boolean variables,
    strings or input variable indices.

        >>> x, y, a, b, c = BooleanPolynomialRing(names="x, y, a, b, c").gens()
        >>> poly = x + x*a + x*b + x*y*(a*b + c) + (a*b*c)
        >>> poly
        x*y*a*b + x*y*c + x*a + x*b + x + a*b*c
        >>> get_all_symbolic_coeff(poly, (0, 1))
        {x*y: a*b + c, x: a + b + 1, 1: a*b*c}
        >>> get_all_symbolic_coeff(poly, (x, y))
        {x*y: a*b + c, x: a + b + 1, 1: a*b*c}
        >>> get_all_symbolic_coeff(poly, ("x", "y"), ignore_terms_of_deg_strictly_less=1)
        {x*y: a*b + c, x: a + b + 1}
        >>> get_all_symbolic_coeff(poly, (0, 1, 2, 3, 4))
        {x*y*a*b: 1, x*y*c: 1, x*a: 1, x*b: 1, x: 1, a*b*c: 1}

    """
    # # for profiling
    # n = 3000; B = BooleanPolynomialRing(n, "x"); p = B.random_element(degree=int(log(n, 2)), terms=n)
    # %prun get_all_symbolic_coeff(p, [2 ** i for i in range(int(log(n, 2)))])

    bpr = bool_poly.parent()
    bpr_variables = bpr.gens()
    one = bpr.one()
    zero = bpr.zero()

    if isinstance(input_vars[0], int):
        index_input_vars = input_vars
    else:
        aux_dict = {str(v): i for i, v in enumerate(bpr_variables)}
        index_input_vars = [aux_dict[str(v)] for v in input_vars]

    if len(input_vars) == len(bpr_variables):
        return {m: one for m in bool_poly.monomials()}

    var_poly2coeff_poly = {}
    for coeff_mon in bool_poly:
        var_mon = one
        coeff_poly = one
        deg = 0

        for index in coeff_mon.iterindex():
            if index in index_input_vars:
                var_mon *= bpr_variables[index]
                deg += 1
            else:
                coeff_poly *= bpr_variables[index]
        if deg < ignore_terms_of_deg_strictly_less:
            continue
        var_poly2coeff_poly[var_mon] = var_poly2coeff_poly.get(var_mon, zero) + coeff_poly

    return var_poly2coeff_poly


def get_symbolic_alg_deg(bool_poly, input_vars):
    """"Return the algebraic degree of a symbolic Boolean function.

    A symbolic Boolean function is a Boolean function of the form
    f(x1, dots, xn-1, a1, dots,), where xi are the inputs
    and ai are parameters (not necessarily ordered).

    The list input_vars can be given as a list of Boolean variables,
    strings or input variable indices.

        >>> x, a, b = BooleanPolynomialRing(names="x, a, b").gens()
        >>> get_symbolic_alg_deg(x + a * b, [0])
        1
        >>> get_symbolic_alg_deg(x + a * b, [x])
        1
        >>> (x + a * b).degree()
        2

    """
    if isinstance(input_vars[0], int):
        index_input_vars = input_vars
    else:
        aux_dict = {str(v): i for i, v in enumerate(bool_poly.parent().gens())}
        index_input_vars = [aux_dict[str(v)] for v in input_vars]

    if len(input_vars) == len(bool_poly.parent().gens()):
        return bool_poly.degree()

    max_deg = 0
    for coeff_mon in bool_poly:
        deg = 0
        for index in coeff_mon.iterindex():
            if index in index_input_vars:
                deg += 1
        max_deg = max(deg, max_deg)

    return max_deg


def simplify_symbolic_matrix(matrix, prefix="x"):
    """Return a symbolic matrix where each symbolic coeff is replaced by a symbolic var.

        >>> a, b, c, d = BooleanPolynomialRing(names=('a','b','c','d')).gens()
        >>> matrix = sage.all.matrix(2, 3, [[a*b, a*b + c, 0], [a*b, d, 1]])
        >>> simplify_symbolic_matrix(matrix)
        [x0 x1  0]
        [x0 x2  1]

    """
    bpr = BooleanPolynomialRing(matrix.nrows()*matrix.ncols(), prefix)
    coeff2label = {}
    entries = [[None for _ in range(matrix.ncols())] for _ in range(matrix.nrows())]
    for i in range(matrix.nrows()):
        for j in range(matrix.ncols()):
            if matrix[i][j] not in [0, 1]:
                if matrix[i][j] in coeff2label:
                    entries[i][j] = coeff2label[matrix[i][j]]
                else:
                    entries[i][j] = bpr.gens()[len(coeff2label)]
                    coeff2label[matrix[i][j]] = entries[i][j]
            else:
                entries[i][j] = int(matrix[i][j])
    return sage.all.matrix(bpr, matrix.nrows(), matrix.ncols(), entries)


def simplify_symbolic_anf(anf, input_vars, prefix="a", order="lex"):
    """Return a symbolic anf where each symbolic coeff is replaced by a symbolic var.

    The list input_vars can be given as a list of Boolean variables,
    strings or input variable indices.

        >>> x, y, z, a, b, c = BooleanPolynomialRing(names="x, y, z, a, b, c").gens()
        >>> f0 = a*x*y*z + b*x*y + c*y*z + (a+b)*x + (b+c)*z + a*b*c
        >>> f1 = a*b*c*x*y*z + x*y + y*z + (b+c)*x + (a+b)*z + 1
        >>> simplify_symbolic_anf([f0, f1], [x, y, z])
        [x*y*z*a0 + x*y*a1 + x*a2 + y*z*a3 + z*a4 + a5, x*y*z*a5 + x*y + x*a4 + y*z + z*a2 + 1]
        >>> simplify_symbolic_anf([f0, f1], ["x", "y", "z"], order="deglex")
        [x*y*z*a0 + x*y*a1 + x*a3 + y*z*a2 + z*a4 + a5, x*y*z*a5 + x*y + x*a4 + y*z + z*a3 + 1]

    """
    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    list_mon2coeff = [get_all_symbolic_coeff(f, input_vars) for f in anf]
    num_coeffs = sum(len(m2c) for m2c in list_mon2coeff)
    bpr = BooleanPolynomialRing(
        len(input_vars) + num_coeffs,
        [str(x) for x in input_vars] + [prefix + str(i) for i in range(num_coeffs)])
    bpr_aux = bpr.change_ring(order=order)

    coeff2label = {}
    new_anf = []
    for mon2coeff in list_mon2coeff:
        mon2coeff = reversed(sorted(mon2coeff.items(), key=lambda mon: bpr_aux(mon[0])))
        component = bpr.zero()
        for mon, coeff in mon2coeff:
            if coeff not in [0, 1]:
                if coeff in coeff2label:
                    coeff = coeff2label[coeff]
                else:
                    new_label = bpr.gens()[len(input_vars) + len(coeff2label)]
                    coeff2label[coeff] = new_label
                    coeff = new_label
            else:
                coeff = int(coeff)
            component += bpr(mon)*coeff
        new_anf.append(component)

    return new_anf
