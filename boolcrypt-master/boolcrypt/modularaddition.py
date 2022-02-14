"""Auxiliary functions for the modular addition modulo a power of two."""
import sage.all

from sage.rings.polynomial.pbori.pbori import BooleanPolynomialVector

GF = sage.all.GF
PolynomialRing = sage.all.PolynomialRing
BooleanPolynomialRing = sage.all.BooleanPolynomialRing


def get_modadd_lut(wordsize, permuted=False):
    """Get the LUT of the binary modular addition.

    If permuted is True, returns (x, y) -> (x \boxplus y, y).

        >>> get_modadd_lut(2)
        [0, 1, 2, 3, 1, 2, 3, 0, 2, 3, 0, 1, 3, 0, 1, 2]
        >>> get_modadd_lut(2, permuted=True)
        [0, 1, 2, 3, 5, 6, 7, 4, 10, 11, 8, 9, 15, 12, 13, 14]

    """
    from boolcrypt.utilities import int2vector, vector2int

    new_lut = []
    n_left = wordsize
    n_right = wordsize

    for x_y in range(2**(n_left + n_right)):
        x_y = int2vector(x_y, n_left + n_right)
        x, y = x_y[:n_left], x_y[-n_left:]

        z_left = (vector2int(x) + vector2int(y)) % (2**wordsize)
        z_left = int2vector(z_left, n_left)
        z_right = y

        if permuted:
            z = vector2int(list(z_left) + list(z_right))
        else:
            z = vector2int(list(z_left))

        new_lut.append(z)

    return new_lut


def get_modadd_anf(wordsize, permuted=False, only_x_names=True):
    """Return the anf of the modular addition.

    If permuted is True, returns (x, y) -> (x \boxplus y, y).

    If only_x_names is True, the input variables are denoted by x0, x1, ...
    Otherwise, the inputs are denoted by x0, x1,...,y0,y1,...

        >>> for f in get_modadd_anf(2): print(f)
        x0 + x2
        x0*x2 + x1 + x3
        >>> for f in get_modadd_anf(3, permuted=True, only_x_names=False): print(f)
        x0 + y0
        x0*y0 + x1 + y1
        x0*x1*y0 + x0*y0*y1 + x1*y1 + x2 + y2
        y0
        y1
        y2

    """
    if only_x_names:
        x_names = ["x" + str(i) for i in range(wordsize)]
        y_names = ["x" + str(i) for i in range(wordsize, 2 * wordsize)]
    else:
        x_names = ["x" + str(i) for i in range(wordsize)]
        y_names = ["y" + str(i) for i in range(wordsize)]

    bpr = BooleanPolynomialRing(names=x_names + y_names)

    x = bpr.gens()[:wordsize]
    y = bpr.gens()[wordsize:]

    anf = BooleanPolynomialVector()
    c = BooleanPolynomialVector([bpr(0)])
    for i in range(wordsize):
        anf.append(x[i] + y[i] + c[i])
        c.append((x[i]*y[i]) + (x[i]*c[i]) + (y[i]*c[i]))  # c[i+1]

    if permuted:
        for i in range(wordsize):
            anf.append(y[i])

    return anf


def get_implicit_modadd_anf(wordsize, permuted=False, only_x_names=True):
    """Return the quadratic anf of the implicit function of the modular addition.

    Let F(x,y)=x \boxplus y (F(x,y)=(x \boxplus y,y) if permuted).
    The quadratic implicit function of \boxplus is a quadratic function G
    such that Graph(F) = {(x, y) = G(x, y) = 0}.

    For permuted=False, G(x, y, z) =  (x ^ y ^ z ^ q(x ^ z, y ^ z)),
    where q(x, y) = (0, x_0 y_0, ..., x_0 y_0 ^ ... ^ x_{n-2} y_{n-2}).
    For permuted=True, G(x, y, z, y) same but with the extra component t ^ y.

        >>> for f in get_implicit_modadd_anf(2): print(f)
        x0 + x2 + x4
        x0*x2 + x0*x4 + x1 + x2*x4 + x3 + x4 + x5
        >>> for f in get_implicit_modadd_anf(3, permuted=True, only_x_names=False): print(f)
        x0 + y0 + z0
        x0*y0 + x0*z0 + x1 + y0*z0 + y1 + z0 + z1
        x0*y0 + x0*z0 + x1*y1 + x1*z1 + x2 + y0*z0 + y1*z1 + y2 + z0 + z1 + z2
        y0 + t0
        y1 + t1
        y2 + t2

    """
    if only_x_names:
        x_names = ["x" + str(i) for i in range(wordsize)]
        y_names = ["x" + str(i) for i in range(wordsize, 2 * wordsize)]
    else:
        x_names = ["x" + str(i) for i in range(wordsize)]
        y_names = ["y" + str(i) for i in range(wordsize)]

    if only_x_names:
        z_names = ["x" + str(i) for i in range(2*wordsize, 3*wordsize)]
    else:
        z_names = ["z" + str(i) for i in range(wordsize)]
    t_names = []
    if permuted:
        if only_x_names:
            t_names = ["x" + str(i) for i in range(3*wordsize, 4*wordsize)]
        else:
            t_names = ["t" + str(i) for i in range(wordsize)]

    bpr = sage.all.BooleanPolynomialRing(names=x_names + y_names + z_names + t_names)

    x = bpr.gens()[:wordsize]
    y = bpr.gens()[wordsize:2*wordsize]
    z = bpr.gens()[2*wordsize:3*wordsize]
    if permuted:
        t = bpr.gens()[3*wordsize:4*wordsize]

    anf = BooleanPolynomialVector([x[0] + y[0] + z[0]])
    q_anf = BooleanPolynomialVector([bpr(0)])
    for i in range(1, wordsize):
        # x ^ y ^ z ^ q(x \oplus z, y \oplus z))
        aux_q = q_anf[i - 1] + (x[i - 1] + z[i - 1]) * (y[i - 1] + z[i - 1])
        anf.append(x[i] + y[i] + z[i] + aux_q)
        q_anf.append(aux_q)

    if permuted:
        for i in range(wordsize):
            anf.append(y[i] + t[i])
    return anf


def get_ccz_modadd_anf(wordsize, name, permuted=0, only_x_names=True,
                       bpr=None, input_vars=None):
    """Return a CCZ-equivalent function of the modular addition.

    The argument name can take the values "q", "Q", "H" and "p" and the
    following quadratic CCZ functions are returned:
    - q(x, y) = (0, x_0 y_0, ..., x_0 y_0 ^ ... ^ x_{n-2} y_{n-2})
    - Q(x, y) = x ^ y ^ q(x, y)
    - H(x, y) = x ^ q(x ^ y, y)
    - p(x, y) = (0, x_0 y_0, ..., x_{n-2} y_{n-2})

    If permuted=1 or permuted is True, appends the component 'y'.
    If permuted=2, appends the component '0'.

    If a BooleanPolynomialRing is given in bpr and a list of
    input variables (of x and y) of the same bpr are given in input_vars,
    then bpr is set as the parent of the CCZ-equivalent function.

        >>> for f in get_ccz_modadd_anf(3, "q", only_x_names=False): print(f)
        0
        x0*y0
        x0*y0 + x1*y1
        >>> for f in get_ccz_modadd_anf(3, "H", only_x_names=False): print(f)
        x0
        x0*y0 + x1 + y0
        x0*y0 + x1*y1 + x2 + y0 + y1
        >>> for f in get_ccz_modadd_anf(3, "Q", only_x_names=False): print(f)
        x0 + y0
        x0*y0 + x1 + y1
        x0*y0 + x1*y1 + x2 + y2
        >>> for f in get_ccz_modadd_anf(3, "p", only_x_names=False): print(f)
        0
        x0*y0
        x1*y1
        >>> for f in get_ccz_modadd_anf(2, "q", permuted=2): print(f)
        0
        x0*x2
        0
        0
        >>> for f in get_ccz_modadd_anf(2, "H", permuted=1): print(f)
        x0
        x0*x2 + x1 + x2
        x2
        x3

    """
    assert name in ["q", "Q", "H", "p"]

    if permuted is False:
        permuted = 0
    if permuted is True:
        permuted = 1
    assert permuted in [0, 1, 2]

    if bpr is None:
        if only_x_names:
            x_names = ["x" + str(i) for i in range(wordsize)]
            y_names = ["x" + str(i) for i in range(wordsize, 2 * wordsize)]
        else:
            x_names = ["x" + str(i) for i in range(wordsize)]
            y_names = ["y" + str(i) for i in range(wordsize)]

        bpr = sage.all.BooleanPolynomialRing(names=x_names + y_names)

        x = bpr.gens()[:wordsize]
        y = bpr.gens()[wordsize:]
    else:
        assert input_vars is not None and len(input_vars) == 2*wordsize
        x = [bpr(v) for v in input_vars[:wordsize]]
        y = [bpr(v) for v in input_vars[wordsize:]]

    anf = BooleanPolynomialVector()
    q_anf = BooleanPolynomialVector()
    for i in range(wordsize):
        if i == 0:
            aux_q = bpr(0)
        else:
            if name in ["q", "Q"]:
                aux_q = q_anf[i - 1] + (x[i - 1] * y[i - 1])
            elif name == "H":
                aux_q = q_anf[i - 1] + y[i - 1] + (x[i - 1] * y[i - 1])
            elif name == "p":
                aux_q = x[i - 1] * y[i - 1]
        q_anf.append(aux_q)

        if name in ["q", "p"]:
            anf.append(aux_q)
        elif name == "Q":
            anf.append(x[i] + y[i] + aux_q)
        elif name == "H":
            anf.append(x[i] + aux_q)

    if permuted:
        for i in range(wordsize):
            if permuted == 1:
                anf.append(y[i])
            elif permuted == 2:
                anf.append(bpr(0))

    return anf


def get_admissible_mapping(wordsize, name, permuted=0, bpr=None):
    """Return the admissible mapping L of G s.t. L(Graph(G))=Graph(modadd).

    G is the function from get_ccz_modadd(wordsize, name, permuted),

        >>> get_admissible_mapping(3, "q")
        [1 0 0|0 0 0|1 0 0]
        [0 1 0|0 0 0|0 1 0]
        [0 0 1|0 0 0|0 0 1]
        [-----+-----+-----]
        [0 0 0|1 0 0|1 0 0]
        [0 0 0|0 1 0|0 1 0]
        [0 0 0|0 0 1|0 0 1]
        [-----+-----+-----]
        [1 0 0|1 0 0|1 0 0]
        [0 1 0|0 1 0|0 1 0]
        [0 0 1|0 0 1|0 0 1]
        >>> get_admissible_mapping(3, "H")
        [0 0 0|1 0 0|1 0 0]
        [0 0 0|0 1 0|0 1 0]
        [0 0 0|0 0 1|0 0 1]
        [-----+-----+-----]
        [1 0 0|1 0 0|1 0 0]
        [0 1 0|0 1 0|0 1 0]
        [0 0 1|0 0 1|0 0 1]
        [-----+-----+-----]
        [0 0 0|0 0 0|1 0 0]
        [0 0 0|0 0 0|0 1 0]
        [0 0 0|0 0 0|0 0 1]
        >>> get_admissible_mapping(2, "q", permuted=2)
        [0 0|1 0|1 0|0 0]
        [0 0|0 1|0 1|0 0]
        [---+---+---+---]
        [1 0|0 0|1 0|0 0]
        [0 1|0 0|0 1|0 0]
        [---+---+---+---]
        [1 0|1 0|1 0|0 0]
        [0 1|0 1|0 1|0 0]
        [---+---+---+---]
        [1 0|0 0|1 0|1 0]
        [0 1|0 0|0 1|0 1]
        >>> get_admissible_mapping(2, "H", permuted=1)
        [0 0|1 0|1 0|0 0]
        [0 0|0 1|0 1|0 0]
        [---+---+---+---]
        [1 0|1 0|1 0|0 0]
        [0 1|0 1|0 1|0 0]
        [---+---+---+---]
        [0 0|0 0|1 0|0 0]
        [0 0|0 0|0 1|0 0]
        [---+---+---+---]
        [1 0|0 0|1 0|1 0]
        [0 1|0 0|0 1|0 1]

    """
    ws = wordsize

    if bpr is None:
        bpr = sage.all.GF(2)

    ib = sage.all.identity_matrix(bpr, ws)  # identity matrix block
    zb = sage.all.zero_matrix(bpr, ws, ws)  # zero matrix block

    assert name in ["q", "Q", "H", "p"]

    if permuted is False:
        permuted = 0
    if permuted is True:
        permuted = 1
    assert permuted in [0, 1, 2]

    if name == "q":
        if not permuted:
            am = sage.all.block_matrix([
                [ib, zb, ib],
                [zb, ib, ib],
                [ib, ib, ib]])
        elif permuted == 1:
            am = sage.all.block_matrix([
                [ib, zb, ib, zb],
                [zb, ib, ib, zb],
                [ib, ib, ib, zb],
                [zb, zb, ib, ib]])
        elif permuted == 2:
            am = sage.all.block_matrix([
                [zb, ib, ib, zb],
                [ib, zb, ib, zb],
                [ib, ib, ib, zb],
                [ib, zb, ib, ib]])
            # # both are admissible mappings
            # am = sage.all.block_matrix([
            #     [ib, zb, ib, zb],
            #     [zb, ib, ib, zb],
            #     [ib, ib, ib, zb],
            #     [zb, ib, ib, ib]])
    elif name == "H":
        if not permuted:
            am = sage.all.block_matrix([
                [zb, ib, ib],
                [ib, ib, ib],
                [zb, zb, ib]])
        else:
            if permuted == 1:
                am = sage.all.block_matrix([
                    [zb, ib, ib, zb],
                    [ib, ib, ib, zb],
                    [zb, zb, ib, zb],
                    [ib, zb, ib, ib]])
            if permuted == 2:
                am = sage.all.block_matrix([
                    [zb, ib, ib, zb],
                    [ib, ib, ib, zb],
                    [zb, zb, ib, zb],
                    [ib, ib, ib, ib]])
    elif name == "Q":
        if not permuted:
            am = sage.all.block_matrix([
                [zb, ib, ib],
                [ib, zb, ib],
                [zb, zb, ib]])
        else:
            if permuted == 1:
                am = sage.all.block_matrix([
                    [zb, ib, ib, zb],
                    [ib, zb, ib, zb],
                    [zb, zb, ib, zb],
                    [ib, ib, ib, ib]])
            elif permuted == 2:
                am = sage.all.block_matrix([
                    [zb, ib, ib, zb],
                    [ib, zb, ib, zb],
                    [zb, zb, ib, zb],
                    [ib, zb, ib, ib]])
    elif name == "p":
        # p = bb \circ q
        # bb:
        # 1 0 0
        # 1 1 0
        # 1 1 1
        bb = sage.all.matrix(bpr, ws, ws, [[1 if j <= i else 0 for j in range(ws)] for i in range(ws)])
        if not permuted:
            p2q = sage.all.block_matrix([
                [ib, zb, zb],
                [zb, ib, zb],
                [zb, zb, bb]])  # (bb^{-1})^{-1}
        else:
            p2q = sage.all.block_matrix([
                [ib, zb, zb, zb],
                [zb, ib, zb, zb],
                [zb, zb, bb, zb],
                [zb, zb, zb, ib]])

        if not permuted:
            am = sage.all.block_matrix([
                [ib, zb, ib],
                [zb, ib, ib],
                [ib, ib, ib]])
        elif permuted == 1:
            am = sage.all.block_matrix([
                [ib, zb, ib, zb],
                [zb, ib, ib, zb],
                [ib, ib, ib, zb],
                [zb, zb, ib, ib]])
        elif permuted == 2:
            am = sage.all.block_matrix([
                [zb, ib, ib, zb],
                [ib, zb, ib, zb],
                [ib, ib, ib, zb],
                [ib, zb, ib, ib]])
        am = am * p2q
    return am


def test_modadd_functions(wordsize_range=range(2, 5)):
    """Test the conversion functions

        >>> test_modadd_functions()
        True

    """
    from itertools import zip_longest
    from boolcrypt.utilities import lut2anf
    from boolcrypt.equivalence import check_ccz_equivalence_anf

    for ws in wordsize_range:
        modadd_anf = get_modadd_anf(ws)
        modadd_permuted_anf = get_modadd_anf(ws, permuted=True)

        if any(f != g for f, g in zip_longest(modadd_anf, lut2anf(get_modadd_lut(ws), num_outputs=ws))):
            return False
        if any(f != g for f, g in zip_longest(modadd_permuted_anf, lut2anf(get_modadd_lut(ws, permuted=True)))):
            return False

        if not check_ccz_equivalence_anf(modadd_anf, get_implicit_modadd_anf(ws),
                                         sage.all.identity_matrix(GF(2), ws * 3), g_implicit=True):
            return False
        if not check_ccz_equivalence_anf(modadd_permuted_anf, get_implicit_modadd_anf(ws, permuted=True),
                                         sage.all.identity_matrix(GF(2), ws * 4), g_implicit=True):
            return False

        for permuted in [0, 1, 2]:
            modadd_anf_aux = modadd_anf if not permuted else modadd_permuted_anf
            for name in ["q", "Q", "H", "p"]:
                ccz_anf = get_ccz_modadd_anf(ws, name, permuted=permuted)
                am = get_admissible_mapping(ws, name, permuted=permuted)
                if not check_ccz_equivalence_anf(ccz_anf, modadd_anf_aux, am):
                    return False

    return True


# def find_admissible_mapping(wordsize, name, mode, permuted=False, simplify=False):
#     """Return admissible mappings to be CCZ to the the modular addition.
#
#     If mode == 0, it considers all matrices with identity or zero blocks.
#     If mode == 1, it expands the 3x3 block admissible mapping of the non-permuted version
#     with all combinations of identity and zero blocks.
#     If mode == 2, it expands the 3x3 block admissible mapping of the non-permuted version
#     (but with the 4 column being zero) with all combinations of identity and zero blocks.
#
#         >>> for m in find_admissible_mapping(3, "p", mode=0, permuted=False, simplify=True): print(m)
#         [1 0|1 0|1 0]
#         [0 1|0 1|0 1]
#         [---+---+---]
#         [1 0|1 0|0 0]
#         [0 1|0 1|0 0]
#         [---+---+---]
#         [1 0|0 0|0 0]
#         [0 1|0 0|0 0]
#         >>> for m in find_admissible_mapping(3, "p", mode=0, permuted=True, simplify=True): print(m)
#         [0 0|1 0|1 0|0 0]
#         [0 0|0 1|0 1|0 0]
#         [---+---+---+---]
#         [1 0|1 0|1 0|0 0]
#         [0 1|0 1|0 1|0 0]
#         [---+---+---+---]
#         [0 0|0 0|1 0|0 0]
#         [0 0|0 0|0 1|0 0]
#         [---+---+---+---]
#         [1 0|0 0|1 0|1 0]
#         [0 1|0 0|0 1|0 1]
#
#     """
#     if not permuted:
#         assert mode == 0
#
#     ws = wordsize
#
#     ib = sage.all.identity_matrix(sage.all.GF(2), ws)
#     zb = sage.all.zero_matrix(sage.all.GF(2), ws, ws)
#
#     modadd_anf = get_modadd_anf(ws, permuted=permuted)
#
#     ccz_anf = get_ccz_modadd_anf(ws, name, permuted=permuted)
#
#     if not permuted or mode == 0:
#         l = []
#     else:
#         assert permuted is True
#         matrix_l = get_admissible_mapping(wordsize, name, permuted=False)
#         if mode in [1, 2]:
#             l = []
#             for row in range(3):
#                 block_row = []
#                 for col in range(3):
#                     block_row.append(matrix_l.submatrix(row*ws, col*ws, ws, ws))
#                 if mode == 2:
#                     block_row.append(zb)
#                 l.append(block_row)
#         else:
#             assert False
#
#     nb = 3 if not permuted else 4  # num_blocks per row
#     if mode == 0:
#         new_nb = nb * nb
#     elif mode == 1:
#         new_nb = 3 + 4
#     elif mode == 2:
#         new_nb = 4
#     else:
#         assert False
#
#     blocks_to_sample = [ib, zb]
#
#     import itertools
#     from boolcrypt.equivalence import check_ccz_equivalence_anf
#
#     for combination in itertools.product(blocks_to_sample, repeat=new_nb):
#         if mode == 0:
#             blocks = [[] for _ in range(nb)]
#             for i in range(len(combination)):
#                 blocks[i // nb].append(combination[i])
#             admissible_mapping = sage.all.block_matrix(sage.all.GF(2), nb, nb, blocks)
#         elif mode == 1:
#             blocks = []
#             for row in range(3):
#                 blocks.append(l[row] + [combination[row]])
#             blocks.append(combination[3:])
#             admissible_mapping = sage.all.block_matrix(sage.all.GF(2), nb, nb, blocks)
#         elif mode == 2:
#             blocks = l + [combination]
#             admissible_mapping = sage.all.block_matrix(sage.all.GF(2), nb, nb, blocks)
#         else:
#             raise ValueError("invalid mode")
#
#         if not admissible_mapping.is_invertible():
#             continue
#
#         result = check_ccz_equivalence_anf(ccz_anf, modadd_anf, admissible_mapping)
#         if result:
#             print("found")
#             if simplify:
#                 admissible_mapping = []
#                 for row in blocks:
#                     new_row = []
#                     for cell in row:
#                         if cell == ib:
#                             new_row.append(1)
#                         elif cell == zb:
#                             new_row.append(0)
#                         else:
#                             raise ValueError("invalid cell " + str(cell))
#                     admissible_mapping.append(new_row)
#                 admissible_mapping = sage.all.matrix(sage.all.GF(2), nb, nb, admissible_mapping)
#             yield admissible_mapping