"""Find self-equivalences of a function by finding the self-equivalences
of its graph parametrized by a CCZ-equivalent function with lower degree."""
import collections
import itertools
import warnings

from boolcrypt.utilities import (
    matrix2anf, get_ct_coeff, get_smart_print, get_anf_coeffmatrix_str,
    substitute_anf, get_time, anf2matrix, get_all_symbolic_coeff, get_symbolic_anf,
    vector2int, int2vector, anf2lut, is_invertible, compose_anf_fast
)
from boolcrypt.equivalence import check_ccz_equivalence_anf

from boolcrypt.functionalequations import (
    _sp, find_fixed_vars, solve_functional_equation,
)

import sage.all

from sage.rings.polynomial.pbori.pbori import BooleanPolynomialVector
from sage.sat.boolean_polynomials import solve as solve_sat

GF = sage.all.GF
PolynomialRing = sage.all.PolynomialRing
BooleanPolynomialRing = sage.all.BooleanPolynomialRing


# TODO: add to docstring ignore_determinant_equation, ccz_se_anf
def find_self_equivalence(
    # main args
    ccz_anf, admissible_mapping,
    # alternative modes
    ccz_anf_implicit=False,
    # degree args
    left_se_degree=1, inv_right_se_degree=1, inv_left_se_degree=1, right_se_degree=1, se_ct_terms=True,
    # optimization constraints
    ignore_diagonal_equations=False,
    add_invertibility_equations=True, ignore_determinant_equation=False,
    check_se=True,
    bpr=None,
    # optional input args
    ccz_se_anf=None,
    prefix_se_coeffs="c",
    input_ccz_anf_vars=None,
    anf=None, input_anf_vars=None, num_input_anf_vars=None,
    # optional output args
    return_ccz_se=False,
    # printing args
    verbose=False, debug=False, filename=None,
    # extra args passed to solve_functional_equation()
    **solve_args
):
    """Find a SE of F by finding a SE of the graph of G.

    Let F be the function (optionally) given by `anf` and
    G its CCZ-equivalent function through the `admissible_mapping` L,
    that is, Graph(F)=L(Graph(G)).
    F (if given) and G must be in ANF form, but L can be given in ANF,
    as a matrix, or as a (matrix, vector) pair.
    If F is not given, its number of input variables must be
    given in `num_input_anf_vars`.

    Graph(F) is defined as usual, {(x, y): for all x, y=F(x)}.
    If ccz_anf_implicit=False, Graph(G) is defined similarly as Graph(F):
    Otherwise, Graph(G)={(x, y): G(x, y)=0} if ccz_anf_implicit=True.

    This methods finds a self-equivalence (SE) (A, B) with given degrees of F
    (a pair of permutations (A,B) such that B F A = F) by finding
    a SE (an automorphism) of the graph of F parametrized by G.
    A is also called a right SE and B a left SE.
    If no solution is found, None is returned.

    If the SE degrees are both 1 and se_ct_terms=True
    (resp. False), this method finds an affine (resp. linear) SE.

    This methods returns SE (A, B) by finding a Graph(G)-SE C=(c_0, c_1)
    s.t. L C L^{-1} is diagonal and can be written as L C L^{-1} = (A, B^(-1)).
    This is done by solving the functional eq.
    G(c_0(u, G(u))) = c_1(u, G(u))) if ccz_anf_implicit=False,
    or D G C = C (D invertible, D(0)=0) if ccz_anf_implicit=True.
    When ccz_anf_implicit=True, this method is not complete, meaning that
    not all the Graph(G)-SE can be found from the equation G C = C.

    If return_ccz_se=False, the SE of F are returned. However,
    the left SE B are not given in the output, but their inverses B^(-1).
    If return_ccz_se=True, instead of returning the SE (A, B),
    the Graph(G)-self-equivalences C are returned instead.

    If check_se=True, checks that the found SE (A, B) are indeed SE of F.

    If add_invertibility_equations=True, the equations that
    impose (A, B) to be invertible are added to the system of equations.
    In this case, if the self-equivalences are non-linear then
    either inv_left_se_degree or right_se_degree is used to
    build the invertibility equations

    input_ccz_anf_vars and input_anf_vars are two lists with the inputs vars
    (containing Boolean variables or strings) of the given G and F
    (not needed for non-symbolic anfs).

    A Boolean polynomial ring bpr can be given to determine the
    term order. Otherwise, lexicographic order will be used
    (x0 > x1 > ..., F0 > F1 > ... > G0 > G1 > ... ).

    If ignore_diagonal_equations is True, the constraints that ensured
    that L C L^{-1} is diagonal and with proper degrees are ignored.
    In this case, add_invertibility_equations must be False.

    Named arguments from **solve_args are passed to solve_functional_equation().
    In particular, if return_mode and num_sat_solutions are not given,
    only one solution is found and the ANF of A and B^(-1) are given.

        >>> from boolcrypt.utilities import lut2anf, get_lut_inversion, anf2lut, invert_lut
        >>> from boolcrypt.equivalence import check_self_le_lut
        >>> f = lut2anf(get_lut_inversion(4))
        >>> g = lut2anf([0, 15, 9, 7, 4, 14, 1, 3, 10, 6, 13, 2, 8, 5, 11, 12])
        >>> am = [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1,
        ... 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1,
        ... 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1]
        >>> am = sage.all.matrix(GF(2), 4*2, 4*2, am)
        >>> a, b_inv = find_self_equivalence(g, am, anf=f, se_ct_terms=False,
        ...     only_linear_fixed_vars=True, verbose=True)  # doctest:+ELLIPSIS,+NORMALIZE_WHITESPACE
        finding SE of F through the graph of G with degrees (1, 1) and inverse degrees (1, 1)
        - F:
        [x0*x1*x2 x0*x1*x3 x0*x2*x3 x1*x2*x3|   x0*x1    x0*x2    x0*x3    x1*x2    x1*x3    x2*x3|      x0       x1       x2       x3]
        [-----------------------------------+-----------------------------------------------------+-----------------------------------]
        [       1        0        0        1|       0        1        0        1        0        0|       1        1        1        1]
        [       0        1        0        0|       1        1        0        1        1        0|       0        0        0        1]
        [       0        0        1        0|       1        1        1        0        0        0|       0        0        1        1]
        [       0        0        0        1|       0        0        1        0        1        1|       0        1        1        1]
        - G (CCZ-equivalent of F):
        [x0*x1*x2 x0*x1*x3 x0*x2*x3 x1*x2*x3|   x0*x1    x0*x2    x0*x3    x1*x2    x1*x3    x2*x3|      x0       x1       x2       x3]
        [-----------------------------------+-----------------------------------------------------+-----------------------------------]
        [       1        0        0        0|       1        1        1        0        0        0|       1        1        0        0]
        [       0        1        0        0|       0        0        1        0        1        1|       1        0        0        1]
        [       0        0        1        0|       0        1        0        1        1        1|       1        0        1        0]
        [       1        0        0        1|       0        0        0        1        1        0|       1        1        0        1]
        <BLANKLINE>
        ... | computing C
        - C (self-equivalence of Graph(G)):
        [   x0    x1    x2    x3    x4    x5    x6    x7]
        [-----------------------------------------------]
        [ca0_0 ca0_1 ca0_2 ca0_3 ca0_4 ca0_5 ca0_6 ca0_7]
        [ca1_0 ca1_1 ca1_2 ca1_3 ca1_4 ca1_5 ca1_6 ca1_7]
        [ca2_0 ca2_1 ca2_2 ca2_3 ca2_4 ca2_5 ca2_6 ca2_7]
        [ca3_0 ca3_1 ca3_2 ca3_3 ca3_4 ca3_5 ca3_6 ca3_7]
        [cb0_0 cb0_1 cb0_2 cb0_3 cb0_4 cb0_5 cb0_6 cb0_7]
        [cb1_0 cb1_1 cb1_2 cb1_3 cb1_4 cb1_5 cb1_6 cb1_7]
        [cb2_0 cb2_1 cb2_2 cb2_3 cb2_4 cb2_5 cb2_6 cb2_7]
        [cb3_0 cb3_1 cb3_2 cb3_3 cb3_4 cb3_5 cb3_6 cb3_7]
        number of C input variables: 8
        number of symbolic coefficients: 64
        <BLANKLINE>
        ... | getting equations from L C L^(-1) = diagonal
        - L C L^(-1) (L admissible mapping L(Graph(G)=Graph(F)):
        [...]
        <BLANKLINE>
        ... | finding fixed variables and reducing initial and diagonal equations
        reducing 32 equations with mode gauss and degrees (d,#) Counter({1: 32})
        gauss-reduction obtained 32 equations with degrees (d,#) Counter({1: 32})
        found 32 fixed variables, resulting in 0 equations
        > repeating find_fixed_vars with initial reduction_mode gauss
        > last find_fixed_vars call found 0 new fixed variables and removed 0 equations
        - L C L^(-1) (reduced by initial and diagonal equations):
        [...]
        <BLANKLINE>
        ... | adding invertibility equations over L C L^(-1)
        added 1 invertibility equations
        <BLANKLINE>
        ... | solving the Graph(G)-self-equivalence functional equation
        ...
        <BLANKLINE>
        ... | parsing and checking the Graph(G)-self-equivalence solutions
        Solution 1 out of 1:
        - L C L^(-1):
        [...]
        - SE (A, B) of F:
         - A:
        [...]
         - B^(-1):
        [...]
        <BLANKLINE>
        ... | returning outputs with mode='list_anfs'
        >>> bpr = BooleanPolynomialRing(4, 'x')
        >>> a = anf2lut([bpr(component) for component in a])
        >>> b = invert_lut(anf2lut([bpr(component) for component in b_inv]))
        >>> check_self_le_lut(get_lut_inversion(4), right_le=a, left_le=b)
        True
        >>> from sage.crypto.sbox import SBox
        >>> f = lut2anf((0, 1, 2, 3, 4, 6, 7, 5))  # 12 LSE
        >>> boolean_vars = sage.all.BooleanPolynomialRing(3*2, 'x').gens()
        >>> iv, ov = boolean_vars[:3], boolean_vars[3:]
        >>> iv, ov = list(reversed(iv)), list(reversed(ov))  # polynomials() takes x0 as MSB
        >>> g = SBox((0, 1, 2, 3, 4, 6, 7, 5)).polynomials(iv, ov, groebner=True)
        >>> am = sage.all.identity_matrix(GF(2), 3*2)
        >>> fixed_vars = dict([('cb2_2', 0), ('cb2_1', 0), ('cb2_0', 0), ('cb1_2', 0), ('cb1_1', 0), ('cb1_0', 0),
        ... ('cb0_1', 0), ('cb0_0', 0), ('ca2_5', 0), ('ca2_4', 0), ('ca2_3', 0), ('ca1_5', 0), ('ca1_4', 0),
        ... ('ca0_5', 0), ('ca0_4', 0), ('ca0_3', 0), ('ca2_0', 0), ('ca2_1', 0), ('ca2_2', 1), ('cb2_3', 0),
        ... ('cb0_2', 0), ('ca1_3', 0), ('cb2_4', 0), ('cb2_5', 1), ('cd2_0', 0), ('cd2_1', 0), ('cd2_2', 1)])
        >>> [a, b_inv], eqs, num_sols = find_self_equivalence(g, am, num_input_anf_vars=3, ccz_anf_implicit=True,
        ...     se_ct_terms=False, reduction_mode=None, only_linear_fixed_vars=True, return_mode="symbolic_anf",
        ...     num_sat_solutions=12+1, return_total_num_solutions=True,  initial_fixed_vars=fixed_vars,
        ...     verbose=True, debug=True)  # doctest:+ELLIPSIS,+NORMALIZE_WHITESPACE
        ignoring add_invertibility_equations when ccz_anf_implicit is True
        finding SE of F through the graph of G with degrees (1, 1) and inverse degrees (1, 1)
        - F:
        []
        - G (CCZ-implicit-equivalent of F):
        [x3*x5 x4*x5|   x0    x1    x2    x3    x4    x5]
        [-----------+-----------------------------------]
        [    0     1|    1     0     0     1     0     0]
        [    1     1|    0     1     0     0     1     0]
        [    0     0|    0     0     1     0     0     1]
        <BLANKLINE>
        ... | computing C
        - C (self-equivalence of Graph(G)):
        [   x0    x1    x2    x3    x4    x5]
        [-----------------------------------]
        [ca0_0 ca0_1 ca0_2     0     0     0]
        [ca1_0 ca1_1 ca1_2     0     0     0]
        [    0     0     1     0     0     0]
        [    0     0     0 cb0_3 cb0_4 cb0_5]
        [    0     0     0 cb1_3 cb1_4 cb1_5]
        [    0     0     0     0     0     1]
        input variables (6): ['x0', 'x1', 'x2', 'x3', 'x4', 'x5']
        symbolic coefficients (45): ['ca0_0', ..., 'cd2_2']
        Boolean PolynomialRing in x0, x1, x2, x3, x4, x5, ca0_0, ..., cd2_2
        initial fixed vars (27):
            cb2_2 <- 0
            ...
            cd2_2 <- 1
        - D (from G = D G C):
        [   x0    x1    x2]
        [-----------------]
        [cd0_0 cd0_1 cd0_2]
        [cd1_0 cd1_1 cd1_2]
        [    0     0     1]
        <BLANKLINE>
        ... | getting equations from L C L^(-1) = diagonal
        - L C L^(-1) (L admissible mapping L(Graph(G)=Graph(F)):
        [   x0    x1    x2    x3    x4    x5]
        [-----------------------------------]
        [ca0_0 ca0_1 ca0_2     0     0     0]
        [ca1_0 ca1_1 ca1_2     0     0     0]
        [    0     0     1     0     0     0]
        [    0     0     0 cb0_3 cb0_4 cb0_5]
        [    0     0     0 cb1_3 cb1_4 cb1_5]
        [    0     0     0     0     0     1]
        equations from L C L^(-1) = diagonal:
        no equations added from L C L^(-1) = diagonal
        <BLANKLINE>
        ... | finding fixed variables and reducing initial and diagonal equations
        - L C L^(-1) (reduced by initial and diagonal equations):
        [   x0    x1    x2    x3    x4    x5]
        [-----------------------------------]
        [ca0_0 ca0_1 ca0_2     0     0     0]
        [ca1_0 ca1_1 ca1_2     0     0     0]
        [    0     0     1     0     0     0]
        [    0     0     0 cb0_3 cb0_4 cb0_5]
        [    0     0     0 cb1_3 cb1_4 cb1_5]
        [    0     0     0     0     0     1]
        <BLANKLINE>
        ... | solving the Graph(G)-self-equivalence functional equation
        removing from initial_fixed_vars cd2_0 <- 0
        removing from initial_fixed_vars cd2_1 <- 0
        removing from initial_fixed_vars cd2_2 <- 1
        ...
        <BLANKLINE>
        ... | parsing and checking the Graph(G)-self-equivalence solutions
        finding a solution of the remaining 3 equations for checking
            cb0_5*cd1_1 + cb1_5*cd1_0 + cb1_5*cd1_1 + cd0_2
            cd1_0*cd1_1 + cd1_0 + cd1_1 + 1
            cb0_5*cd1_0 + cb0_5*cd1_1 + cb1_5*cd1_0 + cd1_2
         - solution: {cd1_2: 0, cd1_1: 0, cd1_0: 1, cd0_2: 0, cb1_5: 0, cb0_5: 0}
        Solution 1 out of 1:
        - L C L^(-1):
        [           x0            x1            x2            x3            x4            x5]
        [-----------------------------------------------------------------------------------]
        [        cd1_1         cd1_0 cb0_5 + cb1_5             0             0             0]
        [        cd1_0 cd1_0 + cd1_1         cb0_5             0             0             0]
        [            0             0             1             0             0             0]
        [            0             0             0         cd1_1         cd1_0         cb0_5]
        [            0             0             0         cd1_0 cd1_0 + cd1_1         cb1_5]
        [            0             0             0             0             0             1]
        - L C L^(-1) (with {cd1_2: 0, cd1_1: 0, cd1_0: 1, cd0_2: 0, cb1_5: 0, cb0_5: 0}):
        [x0 x1 x2 x3 x4 x5]
        [-----------------]
        [ 0  1  0  0  0  0]
        [ 1  1  0  0  0  0]
        [ 0  0  1  0  0  0]
        [ 0  0  0  0  1  0]
        [ 0  0  0  1  1  0]
        [ 0  0  0  0  0  1]
        - SE (A, B) of F:
         - A:
        [           x0            x1            x2]
        [-----------------------------------------]
        [        cd1_1         cd1_0 cb0_5 + cb1_5]
        [        cd1_0 cd1_0 + cd1_1         cb0_5]
        [            0             0             1]
         - B^(-1):
        [           x0            x1            x2]
        [-----------------------------------------]
        [        cd1_1         cd1_0         cb0_5]
        [        cd1_0 cd1_0 + cd1_1         cb1_5]
        [            0             0             1]
        - SE (A, B) of F (with {cd1_2: 0, cd1_1: 0, cd1_0: 1, cd0_2: 0, cb1_5: 0, cb0_5: 0}):
         - A:
        [x0 x1 x2]
        [--------]
        [ 0  1  0]
        [ 1  1  0]
        [ 0  0  1]
         - B^(-1):
        [x0 x1 x2]
        [--------]
        [ 0  1  0]
        [ 1  1  0]
        [ 0  0  1]
        <BLANKLINE>
        ... | returning outputs with mode='symbolic_anf'
        >>> get_anf_coeffmatrix_str(a, ["x" + str(i) for i in range(3)])
        [           x0            x1            x2]
        [-----------------------------------------]
        [        cd1_1         cd1_0 cb0_5 + cb1_5]
        [        cd1_0 cd1_0 + cd1_1         cb0_5]
        [            0             0             1]
        >>> get_anf_coeffmatrix_str(b_inv, ["x" + str(i) for i in range(3)])
        [           x0            x1            x2]
        [-----------------------------------------]
        [        cd1_1         cd1_0         cb0_5]
        [        cd1_0 cd1_0 + cd1_1         cb1_5]
        [            0             0             1]
        >>> for eq in eqs: print(eq)
        cb0_5*cd1_1 + cb1_5*cd1_0 + cb1_5*cd1_1 + cd0_2
        cd1_0*cd1_1 + cd1_0 + cd1_1 + 1
        cb0_5*cd1_0 + cb0_5*cd1_1 + cb1_5*cd1_0 + cd1_2
        >>> num_sols
        12

    """
    smart_print = get_smart_print(filename)

    if debug:
        verbose = True

    if left_se_degree == 1 or inv_left_se_degree == 1:
        assert left_se_degree == inv_left_se_degree == 1

    if right_se_degree == 1 or inv_right_se_degree == 1:
        assert right_se_degree == inv_right_se_degree == 1

    assert not isinstance(ccz_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    if input_ccz_anf_vars is None:
        aux_bpr = ccz_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in ccz_anf)
        input_ccz_anf_vars = aux_bpr.gens()

    missing_anf = anf is None
    if not missing_anf:
        assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
        if input_anf_vars is None:
            aux_bpr = anf[0].parent()
            assert all(aux_bpr == f.parent() for f in anf)
            input_anf_vars = aux_bpr.gens()
    else:
        assert num_input_anf_vars is not None
        anf_bpr = BooleanPolynomialRing(n=num_input_anf_vars, names='x')
        input_anf_vars = [anf_bpr("x" + str(i)) for i in range(num_input_anf_vars)]
        if not ccz_anf_implicit:
            anf = [anf_bpr(0) for _ in range(len(ccz_anf))]
        else:
            anf = [anf_bpr(0) for _ in range(len(input_ccz_anf_vars) - num_input_anf_vars)]

    assert all(not str(v).startswith(prefix_se_coeffs)
               for v in list(input_anf_vars) + list(input_ccz_anf_vars))
    assert not prefix_se_coeffs.startswith("x")
    if not ccz_anf_implicit:
        assert len(anf) == len(ccz_anf)
        assert len(input_anf_vars) == len(input_ccz_anf_vars)
    else:
        assert len(input_ccz_anf_vars) == len(input_anf_vars) + len(anf)
        if add_invertibility_equations:
            if verbose:
                smart_print('ignoring add_invertibility_equations when ccz_anf_implicit is True')
        add_invertibility_equations = False

    if ignore_diagonal_equations:
        assert add_invertibility_equations is False  # l_c_linv not created when ignore_diagonal_equations

    if solve_args.get("return_mode", None) == "list_coeffs":
        raise NotImplementedError('return_mode="list_coeffs" not supported in find_self_equivalence')

    initial_equations = solve_args.get("initial_equations", [])
    initial_fixed_vars = solve_args.get("initial_fixed_vars", collections.OrderedDict())
    ignore_initial_parsing = solve_args.get("ignore_initial_parsing", False)
    check_find_fixed_vars = solve_args.get("check_find_fixed_vars", True)

    if ignore_initial_parsing and bpr is None:
        raise ValueError("bpr must be given if ignore_initial_parsing is True")

    if initial_equations is None:
        initial_equations = []
    if initial_fixed_vars is None:
        initial_fixed_vars = collections.OrderedDict()

    if verbose:
        smart_print("finding SE of F through the graph of G "
                    f"with degrees {left_se_degree, inv_right_se_degree} and "
                    f"inverse degrees {inv_left_se_degree, right_se_degree}")
        smart_print("- F:")
        smart_print(get_anf_coeffmatrix_str(anf, input_anf_vars))
        smart_print(f"- G (CCZ-{'implicit-' if ccz_anf_implicit else ''}equivalent of F):")
        smart_print(get_anf_coeffmatrix_str(ccz_anf, input_ccz_anf_vars))
        smart_print("")

    # 1 - Create C such that L C L^(-1) is diagonal

    if verbose:
        smart_print(f"{get_time()} | computing C")

    # use anf and input_anf_vars instead of ccz_anf and input_ccz_anf_vars
    # to consider also the case ccz_anf_implicit=True
    num_c_input_vars = len(input_anf_vars) + len(anf)
    c_deg = max(left_se_degree, inv_right_se_degree)

    if bpr is not None:
        all_varnames = bpr.variable_names()
        num_total_symbolic_coeffs = len(all_varnames) - num_c_input_vars

    if ignore_initial_parsing:
        if ccz_se_anf is None:
            c_0 = get_symbolic_anf(c_deg, num_c_input_vars, len(input_anf_vars), ct_terms=se_ct_terms,
                                   prefix_inputs="x", prefix_coeffs=prefix_se_coeffs + "a",
                                   bpr=bpr, coeff2expr=initial_fixed_vars)
            c_1 = get_symbolic_anf(c_deg, num_c_input_vars, len(anf), ct_terms=se_ct_terms,
                                   prefix_inputs="x", prefix_coeffs=prefix_se_coeffs + "b",
                                   bpr=bpr, coeff2expr=initial_fixed_vars)
        else:
            assert len(ccz_se_anf) == len(input_anf_vars) + len(anf)
            c_0, c_1 = BooleanPolynomialVector(), BooleanPolynomialVector()
            for i in range(len(input_anf_vars) + len(anf)):
                assert ccz_se_anf[i].parent() == bpr
                if i < len(input_anf_vars):
                    c_0.append(ccz_se_anf[i])
                else:
                    c_1.append(ccz_se_anf[i])

        if ccz_anf_implicit:
            d = get_symbolic_anf(c_deg, len(ccz_anf), len(ccz_anf), ct_terms=False,
                                 prefix_inputs="x", prefix_coeffs=prefix_se_coeffs + "d",
                                 bpr=bpr, coeff2expr=initial_fixed_vars)
        c = BooleanPolynomialVector()
        for component in itertools.chain(c_0, c_1):
            c.append(component)
        c_input_vars = [bpr("x" + str(i)) for i in range(num_c_input_vars)]
    else:
        if ccz_se_anf is None:
            # cannot use coeff2ct since all coeffs are needed to build bpr
            c_0 = get_symbolic_anf(c_deg, num_c_input_vars, len(input_anf_vars), ct_terms=se_ct_terms,
                                   prefix_inputs="x", prefix_coeffs=prefix_se_coeffs+"a")
            c_1 = get_symbolic_anf(c_deg, num_c_input_vars, len(anf), ct_terms=se_ct_terms,
                                   prefix_inputs="x", prefix_coeffs=prefix_se_coeffs+"b")
        else:
            assert len(ccz_se_anf) == len(input_anf_vars) + len(anf)
            c_0, c_1 = BooleanPolynomialVector(), BooleanPolynomialVector()
            for i in range(len(input_anf_vars) + len(anf)):
                if i < len(input_anf_vars):
                    c_0.append(ccz_se_anf[i])
                else:
                    c_1.append(ccz_se_anf[i])
        if ccz_anf_implicit:
            d = get_symbolic_anf(c_deg, len(ccz_anf), len(ccz_anf), ct_terms=False,
                                 prefix_inputs="x", prefix_coeffs=prefix_se_coeffs+"d")

        if bpr is None:
            all_varnames = list(c_0[0].parent().variable_names())
            all_varnames.extend(vn for vn in c_1[0].parent().variable_names() if vn not in all_varnames)
            for value in initial_fixed_vars.values():
                if value in [0, 1]:
                    continue
                if isinstance(value, str):
                    value = sage.all.symbolic_expression(value)
                for var in value.variables():
                    varname = str(var)
                    if varname not in all_varnames:
                        all_varnames.append(varname)
            for eq in initial_equations:
                if isinstance(eq, str):
                    eq = sage.all.symbolic_expression(eq)
                for var in eq.variables():
                    varname = str(var)
                    if varname not in all_varnames:
                        all_varnames.append(varname)
            if ccz_anf_implicit:
                all_varnames.extend(vn for vn in d[0].parent().variable_names() if vn not in all_varnames)
            num_total_symbolic_coeffs = len(all_varnames) - num_c_input_vars
            if solve_args.get("only_linear_fixed_vars", False):
                order = "deglex"
            else:
                order = "lex"
            bpr = BooleanPolynomialRing(len(all_varnames), all_varnames, order=order)

        aux_ifv = collections.OrderedDict()
        for var, value in initial_fixed_vars.items():
            aux_ifv[bpr(var)] = bpr(value)
        initial_fixed_vars = aux_ifv

        c = BooleanPolynomialVector()
        aux_c_0 = BooleanPolynomialVector()
        aux_c_1 = BooleanPolynomialVector()
        for component in c_0:
            component = bpr(bpr(component).subs(initial_fixed_vars))
            c.append(component)
            aux_c_0.append(component)
        for component in c_1:
            component = bpr(bpr(component).subs(initial_fixed_vars))
            c.append(component)
            aux_c_1.append(component)
        c_0 = aux_c_0
        c_1 = aux_c_1

        c_input_vars = [bpr("x" + str(i)) for i in range(num_c_input_vars)]

        aux_ie = BooleanPolynomialVector()
        for eq in initial_equations:
            eq = bpr(bpr(eq).subs(initial_fixed_vars))
            if eq == 0:
                continue
            if eq == 1:
                raise ValueError("found invalid initial equation 0 == 1")
            aux_ie.append(eq)
        initial_equations = aux_ie

        if ccz_anf_implicit:
            aux_d = BooleanPolynomialVector()
            for component in d:
                component = bpr(bpr(component).subs(initial_fixed_vars))
                aux_d.append(component)
            d = aux_d

        aux_ccz_anf = BooleanPolynomialVector()
        for component in ccz_anf:
            aux_ccz_anf.append(bpr(component))
        ccz_anf = aux_ccz_anf

        input_ccz_anf_vars = [bpr(v) for v in input_ccz_anf_vars]

    if verbose:
        smart_print("- C (self-equivalence of Graph(G)):")
        smart_print(get_anf_coeffmatrix_str(c, c_input_vars))
        if not debug:
            smart_print("number of C input variables:", num_c_input_vars)
            smart_print("number of symbolic coefficients:", num_total_symbolic_coeffs)
            if initial_fixed_vars:
                smart_print("number of initial fixed vars:", len(initial_fixed_vars))
            if initial_equations:
                smart_print("number of initial equations:", len(initial_equations))
        if debug:
            smart_print(f"input variables ({num_c_input_vars}): {all_varnames[:num_c_input_vars]}")
            smart_print(f"symbolic coefficients ({num_total_symbolic_coeffs}): "
                        f"{all_varnames[-num_total_symbolic_coeffs:]}")
            smart_print(bpr)
            if initial_fixed_vars:
                smart_print(f"initial fixed vars ({len(initial_fixed_vars)}):")
                for var, value in initial_fixed_vars.items():
                    smart_print(f"\t{var} <- {_sp(value)}")
            if initial_equations:
                smart_print(f"initial equations ({len(initial_equations)}):")
                for eq in initial_equations:
                    smart_print("\t" + _sp(eq))
            if ccz_anf_implicit:
                smart_print("- D (from G = D G C):")
                smart_print(get_anf_coeffmatrix_str(d, [bpr("x" + str(i)) for i in range(len(ccz_anf))]))
        smart_print("")

    # 1.2  Getting the equations L C L^(-1) = diagonal

    equations = BooleanPolynomialVector(initial_equations)
    cvar2index = {v: i for i, v in enumerate(c_input_vars)}

    if not ignore_diagonal_equations:
        if verbose:
            if left_se_degree < c_deg or inv_right_se_degree < c_deg:
                aux = f" with top/bottom degrees {left_se_degree}/{inv_right_se_degree}"
            else:
                aux = ""
            smart_print(f"{get_time()} | getting equations from L C L^(-1) = diagonal{aux}")

        from sage.structure.element import is_Matrix
        if is_Matrix(admissible_mapping):
            am_anf = matrix2anf(admissible_mapping, bool_poly_ring=bpr, input_vars=c_input_vars)
            am_matrix = admissible_mapping
        elif len(admissible_mapping) == 2 and is_Matrix(admissible_mapping[0]):
            for bit in admissible_mapping[1]:
                if bit != 0:
                    raise NotImplementedError("affine admissible mappings not supported")
            am_anf = matrix2anf(admissible_mapping[0], bool_poly_ring=bpr,
                                input_vars=c_input_vars, bin_vector=admissible_mapping[1])
            am_matrix = admissible_mapping[0]
        else:
            am_anf = admissible_mapping
            am_matrix = anf2matrix(admissible_mapping[0], c_input_vars)
            for bit in get_ct_coeff(admissible_mapping[0], c_input_vars):
                if bit != 0:
                    raise NotImplementedError("affine admissible mappings not supported")

        inv_am_anf = matrix2anf(am_matrix.inverse(), bool_poly_ring=bpr, input_vars=c_input_vars)

        if len(input_anf_vars) <= 6 and not missing_anf:  # complexity 2^12
            inv_am_matrix = anf2matrix(inv_am_anf, c_input_vars) if ccz_anf_implicit else None
            if not ccz_anf_implicit:
                result_check = check_ccz_equivalence_anf(
                    ccz_anf, anf, am_matrix,
                    f_input_vars=input_ccz_anf_vars, g_input_vars=input_anf_vars, a_input_vars=c_input_vars)
            else:
                result_check = check_ccz_equivalence_anf(
                    anf, ccz_anf, inv_am_matrix, g_implicit=True,
                    f_input_vars=input_anf_vars, g_input_vars=input_ccz_anf_vars, a_input_vars=c_input_vars)
            if result_check is False:
                raise ValueError("L(Graph(G)) != Graph(F)")

        l_c_linv = substitute_anf(c, {c_input_vars[i]: inv_am_anf[i] for i in range(num_c_input_vars)}, bpr)
        l_c_linv = substitute_anf(am_anf, {c_input_vars[i]: l_c_linv[i] for i in range(num_c_input_vars)}, bpr)
        l_c_linv = list(l_c_linv)

        if verbose:
            smart_print("- L C L^(-1) (L admissible mapping L(Graph(G)=Graph(F)):")
            smart_print(get_anf_coeffmatrix_str(l_c_linv, c_input_vars))
        if debug:
            if left_se_degree < c_deg or inv_right_se_degree < c_deg:
                aux = f" with degrees {left_se_degree}/{inv_right_se_degree}"
            else:
                aux = ""
            smart_print(f"equations from L C L^(-1) = diagonal{aux}:")

        index_eq = len(initial_equations)
        for index_component, component in enumerate(l_c_linv):
            all_coeffs = get_all_symbolic_coeff(component, c_input_vars)
            for monomial, coeff in all_coeffs.items():
                monomial_vars = [bpr(v) for v in monomial.variables()]
                if len(monomial_vars) == 0:
                    continue

                if (index_component < len(input_anf_vars) and monomial.degree() > left_se_degree) or \
                        (index_component >= len(input_anf_vars) and monomial.degree() > inv_right_se_degree):
                    if coeff == 0:
                        continue
                    if coeff == 1:
                        raise ValueError(f"L C L^(-1) has different degree, {index_component}-th component "
                                         f"has monomial {monomial} with non-zero coeff {coeff}")
                    if debug:
                        smart_print(f"\teq[{index_eq}]: ({index_component}-th component) "
                                    f"0 == coefficient(monomial/degree={monomial}/{monomial.degree()}) = {_sp(coeff)}")
                    equations.append(coeff)
                    index_eq += 1

                # for first len(input_anf_vars) components,
                # only monomials involving the first len(input_anf_vars) variables
                # for the rest, only monomials involving the remaining variables
                if (index_component < len(input_anf_vars) and
                    any(cvar2index[v] >= len(input_anf_vars) for v in monomial_vars)) or \
                        (index_component >= len(input_anf_vars) and
                         any(cvar2index[v] < len(input_anf_vars) for v in monomial_vars)):
                    if coeff == 0:
                        continue
                    if coeff == 1:
                        raise ValueError(f"L C L^(-1) cannot be diagonal, {index_component}-th component "
                                         f"has monomial {monomial} with non-zero coeff {coeff}")
                    if debug:
                        smart_print(f"\teq[{index_eq}]: ({index_component}-th component) "
                                    f"0 == coefficient(monomial={monomial}) = {_sp(coeff)}")
                    equations.append(coeff)
                    index_eq += 1

        if len(equations) == len(initial_equations) and verbose:
            smart_print("no equations added from L C L^(-1) = diagonal")

        if verbose:
            smart_print("")

    # 1.5 - Reducing initial and diagonal equations

    # no calls to find_fixed_vars() when "raw_equations" mode
    if solve_args.get("return_mode", None) != "raw_equations" and not ignore_diagonal_equations:
        if verbose:
            smart_print(f"{get_time()} | finding fixed variables and reducing initial and diagonal equations")

        reduction_mode = solve_args.get("reduction_mode", "gauss")
        initial_fixed_vars, equations = find_fixed_vars(
            equations, only_linear=True,
            initial_r_mode=reduction_mode, repeat_with_r_mode=reduction_mode,
            initial_fixed_vars=initial_fixed_vars, bpr=bpr, check=check_find_fixed_vars,
            verbose=verbose, debug=debug, filename=filename)

        l_c_linv = list(substitute_anf(l_c_linv, initial_fixed_vars, bpr))  # to list to be sliced

        if verbose:
            smart_print("- L C L^(-1) (reduced by initial and diagonal equations):")
            smart_print(get_anf_coeffmatrix_str(l_c_linv, c_input_vars))

        if verbose:
            smart_print("")

    # 2 - Add invertibility equations imposed over L C L^(-1)

    len_eqs_b4_inv = len(equations)
    if add_invertibility_equations:
        #   create a new LCL^(-1) with linear vars from diagonal_equations + initial_equations
        #   if A or B^(-1) is of degree 1, then add the determinant equation
        #   otherwise, add find_inverse equations from the one whose inverse degree is given
        #   finally save the invertibility equations and ignore the reduced LCL^(-1)

        if verbose:
            smart_print(f"{get_time()} | adding invertibility equations over L C L^(-1)")

        inv_equations = BooleanPolynomialVector()
        if left_se_degree == 1 or inv_right_se_degree == 1:
            # first part tries to get easy fixed variables from sparse row/columns
            # nrows = num output vars, ncols = num inputs vars

            # depth is computed as follows:
            #   sum_{i=0}^{k} binom(n,i) < n^k + 1  (k == depth, n == nrows == num components)
            #   n^k <= 2^16 (max complexity) <==> k = k log(n,n) <= log(2^16, n)

            if inv_right_se_degree == 1:
                base_matrix = anf2matrix(l_c_linv[len(anf):], c_input_vars).submatrix(col=len(input_anf_vars))
                assert base_matrix.is_square()
                depth = int(sage.all.log(2**16, base_matrix.nrows()))
                aux_iv = c_input_vars[:len(anf)]
                for matrix in [base_matrix, base_matrix.transpose()]:
                    matrix_anf = matrix2anf(matrix, bool_poly_ring=bpr, input_vars=aux_iv)
                    for eq in _get_lowdeg_inv_equations(matrix_anf, bpr, max_deg=3, depth=depth, input_vars=aux_iv):
                        inv_equations.append(eq)
            else:
                aux_anf = l_c_linv[len(anf):]
                depth = int(sage.all.log(2**16, len(aux_anf)))
                for eq in _get_lowdeg_inv_equations(aux_anf, bpr, max_deg=3, depth=depth, input_vars=c_input_vars):
                    inv_equations.append(eq)

            if left_se_degree == 1:
                base_matrix = anf2matrix(l_c_linv[:len(anf)], c_input_vars).submatrix(ncols=len(input_anf_vars))
                assert base_matrix.is_square()
                depth = int(sage.all.log(2**16, base_matrix.nrows()))
                aux_iv = c_input_vars[:len(input_anf_vars)]
                for matrix in [base_matrix, base_matrix.transpose()]:
                    matrix_anf = matrix2anf(matrix, bool_poly_ring=bpr, input_vars=aux_iv)
                    for eq in _get_lowdeg_inv_equations(matrix_anf, bpr, max_deg=3, depth=depth, input_vars=aux_iv):
                        inv_equations.append(eq)
            else:
                aux_anf = l_c_linv[:len(anf)]
                depth = int(sage.all.log(2**16, len(aux_anf)))
                for eq in _get_lowdeg_inv_equations(aux_anf, bpr, max_deg=3, depth=depth, input_vars=c_input_vars):
                    inv_equations.append(eq)

            # no calls to find_fixed_vars() when "raw_equations" mode
            if solve_args.get("return_mode", None) != "raw_equations" and not ignore_determinant_equation:
                reduction_mode = solve_args.get("reduction_mode", "gauss")
                inv_fixed_vars, inv_equations = find_fixed_vars(
                    inv_equations, only_linear=True,
                    initial_r_mode=reduction_mode, repeat_with_r_mode=reduction_mode,
                    initial_fixed_vars=initial_fixed_vars, bpr=bpr, check=check_find_fixed_vars,
                    verbose=verbose, debug=debug, filename=filename)
                if len(inv_fixed_vars) > len(initial_fixed_vars):
                    for i in range(len(equations)):
                        equations[i] = equations[i].subs(inv_fixed_vars)
                    base_matrix = base_matrix.subs(inv_fixed_vars)
                initial_fixed_vars = inv_fixed_vars
                for eq in inv_equations:
                    equations.append(eq)
                equations.append(bpr(base_matrix.determinant()) + bpr(1))
            else:
                for eq in inv_equations:
                    equations.append(eq)
        else:
            # TODO: v2 implement non-linear add_invertibility equations
            # main problem: bpr need to be incremented with the new vars from find_inverse
            # for NL I could also add easy vars taking into account the balanced functions
            raise NotImplementedError("both left_se_degree and inv_right_se_degree > 1 not supported")
            # aux_left = inv_left_se_degree if inv_left_se_degree else sage.all.infinity
            # aux_right = right_se_degree if right_se_degree else sage.all.infinity
            # if aux_left <= aux_right:
            #     aux_rep = {v: bpr(0) for v in c_input_vars[len(input_anf_vars):]}
            #     aux_anf = substitute_anf(l_c_linv[:len(anf)], aux_rep, bpr)
            #     raw_eqs = find_inverse(
            #         aux_anf, inv_left_se_degree, inv_position="left", prefix_inv_coeffs=prefix_se_coeffs+"c",
            #         input_vars=c_input_vars[:len(input_anf_vars)], return_mode="raw_equations",
            #         verbose=verbose, debug=debug, filename=filename
            #     )
            # else:
            #     aux_rep = {}
            #     for i in range(num_c_input_vars):
            #         if i < len(input_anf_vars):
            #             aux_rep[c_input_vars[i]] = bpr(0)
            #         else:
            #             aux_rep[c_input_vars[i]] = c_input_vars[i - len(input_anf_vars)]
            #     aux_anf = substitute_anf(l_c_linv[len(anf):], aux_rep, bpr)
            #     raw_eqs = find_inverse(
            #         aux_anf, right_se_degree, inv_position="left", prefix_inv_coeffs=prefix_se_coeffs+"c",
            #         input_vars=c_input_vars[:len(input_anf_vars)], return_mode="raw_equations",
            #         verbose=verbose, debug=debug, filename=filename
            #     )
            # assert raw_eqs is not None
            # # bpr cannot be pass to find_inverse (new vars are created)
            # reduction_mode = solve_args.get("reduction_mode", "gauss")
            # aux_fixed_vars, aux_equations = find_fixed_vars(
            #     raw_eqs, only_linear=False,
            #     initial_r_mode=reduction_mode, repeat_with_r_mode=reduction_mode,
            #     initial_fixed_vars=None, check=check_find_fixed_vars,
            #     # verbose=verbose, debug=debug, filename=filename)
            #     verbose=True, debug=True, filename=None)
            # equations = list(equations)
            # for eq in aux_equations:
            #     equations.append(str(eq))

        if verbose:
            smart_print(f"added {len(equations)-len_eqs_b4_inv} invertibility equations")
            if debug:
                for i in range(len_eqs_b4_inv, len(equations)):
                    smart_print(f"\t{_sp(equations[i])}")
            smart_print("")

    # 3 - Find a Graph(G)-SE of G

    if verbose:
        smart_print(f"{get_time()} | solving the Graph(G)-self-equivalence functional equation")

    if not ccz_anf_implicit:
        #  G(c_0(u, G(u))) = c_1(u, G(u)))
        c_0 = substitute_anf(c_0, initial_fixed_vars, bpr)
        c_1 = substitute_anf(c_1, initial_fixed_vars, bpr)
        f2 = ccz_anf
        f1 = c_0
        f0 = BooleanPolynomialVector()
        for component in itertools.chain(input_ccz_anf_vars, ccz_anf):
            f0.append(component)
        f2_input_vars = input_ccz_anf_vars
        f1_input_vars = c_input_vars
        f0_input_vars = input_ccz_anf_vars
        g1 = c_1
        g0 = f0
        g1_input_vars = c_input_vars
        g0_input_vars = f0_input_vars
        lhs_anfs = [f0, f1, f2]
        lhs_input_vars = [f0_input_vars, f1_input_vars, f2_input_vars]
        rhs_anfs = [g0, g1]
        rhs_input_vars = [g0_input_vars, g1_input_vars]
    else:
        # D G C  = G
        c = substitute_anf(c, initial_fixed_vars, bpr)
        f2 = d
        f1 = ccz_anf
        f0 = c
        f2_input_vars = [bpr("x" + str(i)) for i in range(len(ccz_anf))]
        f1_input_vars = input_ccz_anf_vars
        f0_input_vars = c_input_vars
        g0 = ccz_anf
        g0_input_vars = f1_input_vars
        lhs_anfs = [f0, f1, f2]
        lhs_input_vars = [f0_input_vars, f1_input_vars, f2_input_vars]
        rhs_anfs = [g0]
        rhs_input_vars = [g0_input_vars]

    new_kwargs = solve_args.copy()
    if "num_sat_solutions" not in new_kwargs:
        new_kwargs["num_sat_solutions"] = 1
    else:
        if "return_mode" not in new_kwargs:
            raise ValueError("return_mode must be specified if num_sat_solutions is")
    if "return_mode" not in new_kwargs:
        new_kwargs["return_mode"] = "list_anfs"

    new_kwargs["ignore_initial_parsing"] = True
    new_kwargs["initial_equations"] = equations
    new_kwargs["initial_fixed_vars"] = initial_fixed_vars

    if "find_redundant_equations" in new_kwargs:
        aux_fre = BooleanPolynomialVector()
        for eq in new_kwargs["find_redundant_equations"]:
            eq = bpr(bpr(eq).subs(initial_fixed_vars))
            aux_fre.append(eq)
        new_kwargs["find_redundant_equations"] = aux_fre

    # TODO: v2 implement non-linear add_invertibility equations
    if ccz_anf_implicit:
        new_kwargs["ignore_varnames"] = [vn for vn in all_varnames if vn.startswith(prefix_se_coeffs + "d")]
        for var, val in initial_fixed_vars.copy().items():
            if str(var).startswith(prefix_se_coeffs+"d"):
                if debug:
                    smart_print(f"removing from initial_fixed_vars {var} <- {val}")
                del initial_fixed_vars[var]

    try:
        graph_solutions = solve_functional_equation(
            lhs_anfs, rhs_anfs, lhs_input_vars, rhs_input_vars, bpr=bpr,
            verbose=verbose, debug=debug, filename=filename, **new_kwargs
        )
    except ValueError as e:
        get_smart_print(filename)(f"No solution found ({e})")
        return None

    if verbose:
        smart_print("")

    # 4 - Parsing and checking L C L^(-1) is a SE of F for one solution

    if new_kwargs["return_mode"] in ["raw_equations", "lincomb_solutions"] \
            or new_kwargs.get("find_redundant_equations", None) is not None:
        return graph_solutions

    if verbose:
        smart_print(f"{get_time()} | parsing {'and checking' if check_se else ''} "
                    f"the Graph(G)-self-equivalence solutions")

    se_solutions = []
    extra_var2val = {}
    symbolic_coeffs = None
    if new_kwargs["return_mode"] == "list_anfs":
        for i in range(len(graph_solutions)):
            if solve_args.get("return_total_num_solutions", False):
                se_solutions.append(graph_solutions[0][i])
            else:
                se_solutions.append(graph_solutions[i])
    else:
        assert new_kwargs["return_mode"] in ["symbolic_anf", "symbolic_coeffs"]
        if new_kwargs["return_mode"] == "symbolic_anf":
            se_solutions = [graph_solutions[0]]
        else:
            symbolic_coeffs = graph_solutions[0]
            if not ccz_anf_implicit:
                # se_solutions[0][0][1] == c_0, se_solutions[0][1][1] == g1
                se_solutions = [
                    [
                        [
                            None, substitute_anf(c_0, symbolic_coeffs, bpr)
                        ],  # se_solutions[0][0]
                        [
                            None, substitute_anf(c_1, symbolic_coeffs, bpr)
                        ]  # se_solutions[0][1]
                    ]  # se_solutions[0]
                ]
            else:
                # se_solutions[0][0][0] == c
                se_solutions = [
                    [
                        [
                            substitute_anf(c, symbolic_coeffs, bpr)
                        ] # se_solutions[0][0]
                    ] # se_solutions[0]
                ]

        if check_se:
            extra_equations = graph_solutions[1]
            if extra_equations:
                if verbose:
                    smart_print(f"finding a solution of the remaining {len(extra_equations)} equations for checking")
                    if debug:
                        for eq in extra_equations:
                            smart_print(f"\t{_sp(eq)}")
                extra_var2val = solve_sat(extra_equations, n=1, s_threads=new_kwargs.get("threads", 1))
                if not extra_var2val:
                    raise ValueError('equations from "symbolic_anf" output are inconsistent (unsatisfiable)')
                extra_var2val = {bpr(k): bpr(v) for k, v in extra_var2val[0].items()}  # first solution
                if verbose:
                    smart_print(f" - solution: {extra_var2val}")
            free_vars = set()
            if not ccz_anf_implicit:
                aux_loop = itertools.chain(se_solutions[0][0][1], se_solutions[0][1][1])
            else:
                aux_loop = itertools.chain(se_solutions[0][0][0])
            for aux_anf in aux_loop:
                for component in aux_anf:  # avoid anf
                    for var in component.variables():
                        var = bpr(var)
                        if var not in c_input_vars and var not in extra_var2val:
                            free_vars.add(var)
            if free_vars:
                smart_print(f"setting to 0 the free variables {free_vars} for checking")
                for v in free_vars:
                    extra_var2val[v] = bpr(0)

    if ignore_diagonal_equations and (check_se or not return_ccz_se):
        from sage.structure.element import is_Matrix
        if is_Matrix(admissible_mapping):
            am_anf = matrix2anf(admissible_mapping, bool_poly_ring=bpr, input_vars=c_input_vars)
            am_matrix = admissible_mapping
        elif len(admissible_mapping) == 2 and is_Matrix(admissible_mapping[0]):
            for bit in admissible_mapping[1]:
                if bit != 0:
                    raise NotImplementedError("affine admissible mappings not supported")
            am_anf = matrix2anf(admissible_mapping[0], bool_poly_ring=bpr,
                                input_vars=c_input_vars, bin_vector=admissible_mapping[1])
            am_matrix = admissible_mapping[0]
        else:
            am_anf = admissible_mapping
            am_matrix = anf2matrix(admissible_mapping[0], c_input_vars)
            for bit in get_ct_coeff(admissible_mapping[0], c_input_vars):
                if bit != 0:
                    raise NotImplementedError("affine admissible mappings not supported")

        inv_am_anf = matrix2anf(am_matrix.inverse(), bool_poly_ring=bpr, input_vars=c_input_vars)

    for index_se_sol in range(len(se_solutions)):
        if not ccz_anf_implicit:
            c_0_sol = se_solutions[index_se_sol][0][1]  # f1
            c_1_sol = se_solutions[index_se_sol][1][1]  # g1
            c_sol = BooleanPolynomialVector()
            for component in itertools.chain(c_0_sol, c_1_sol):
                c_sol.append(component)
        else:
            c_sol = se_solutions[index_se_sol][0][0]  # f0

        if return_ccz_se:
            se_solutions[index_se_sol] = c_sol
            if not check_se:
                continue

        if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
            smart_print(f"Solution {index_se_sol + 1} out of {len(se_solutions)}:")

        if check_se and len(input_anf_vars) <= 6 and not ccz_anf_implicit:
            if extra_var2val:
                c_sol_fixed = substitute_anf(c_sol, extra_var2val, bpr)
                if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
                    smart_print(f"- C:")
                    smart_print(get_anf_coeffmatrix_str(c_sol, c_input_vars))
                    smart_print(f"- C (with {extra_var2val}):")
                    smart_print(get_anf_coeffmatrix_str(c_sol_fixed, c_input_vars))
            else:
                c_sol_fixed = c_sol
            aux_bpr = BooleanPolynomialRing(names=[str(v) for v in c_input_vars])
            c_sol_fixed = [aux_bpr(component) for component in c_sol_fixed]
            # if not check_ccz_equivalence_anf(ccz_anf_simple_bpr, ccz_anf_simple_bpr, c_sol_fixed):
            result_check = check_ccz_equivalence_anf(
                ccz_anf, ccz_anf, c_sol_fixed,
                f_input_vars=input_ccz_anf_vars, g_input_vars=input_ccz_anf_vars, a_input_vars=c_input_vars)
            if result_check is False:
                raise ValueError("C is not a Graph-SE of G")

        l_c_linv_sol = substitute_anf(
            c_sol, {c_input_vars[i]: inv_am_anf[i] for i in range(num_c_input_vars)}, bpr)
        l_c_linv_sol = substitute_anf(
            am_anf, {c_input_vars[i]: l_c_linv_sol[i] for i in range(num_c_input_vars)}, bpr)

        if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
            smart_print(f"- L C L^(-1):")
            smart_print(get_anf_coeffmatrix_str(l_c_linv_sol, c_input_vars))

        if check_se:
            if extra_var2val:
                l_c_linv_sol_fixed = substitute_anf(l_c_linv_sol, extra_var2val, bpr)
                if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
                    smart_print(f"- L C L^(-1) (with {extra_var2val}):")
                    smart_print(get_anf_coeffmatrix_str(l_c_linv_sol_fixed, c_input_vars))
            else:
                l_c_linv_sol_fixed = l_c_linv_sol

            aux_bpr = BooleanPolynomialRing(names=[str(v) for v in c_input_vars])
            l_c_linv_sol_fixed = [aux_bpr(component) for component in l_c_linv_sol_fixed]

            if len(input_anf_vars) <= 6 and not missing_anf:  # complexity 2^12
                # if not check_ccz_equivalence_anf(anf_simple_bpr, anf_simple_bpr, l_c_linv_sol_fixed):
                result_check = check_ccz_equivalence_anf(
                    anf, anf, l_c_linv_sol_fixed,
                    f_input_vars=input_anf_vars, g_input_vars=input_anf_vars, a_input_vars=c_input_vars)
                if result_check is False:
                    raise ValueError("L C L^(-1) is not a Graph-SE of F")

            if c_deg == 1:
                if not anf2matrix(l_c_linv_sol_fixed, c_input_vars).is_invertible():
                    raise ValueError("L C L^(-1) is not invertible")
            elif len(c_input_vars) <= 12:
                if not is_invertible(anf2lut(l_c_linv_sol_fixed)):
                    raise ValueError("L C L^(-1) is not invertible")

            for index_component, component in enumerate(l_c_linv_sol_fixed):
                for monomial, coeff in get_all_symbolic_coeff(component, c_input_vars).items():
                    monomial_vars = [bpr(v) for v in monomial.variables()]
                    if len(monomial_vars) == 0:
                        continue
                    if (index_component < len(input_anf_vars) and monomial.degree() > left_se_degree) or \
                            (index_component >= len(input_anf_vars) and monomial.degree() > inv_right_se_degree):
                        if coeff != 0:
                            raise ValueError(f"L C L^(-1) (from {index_se_sol}-th solution) has different degree, "
                                             f"{index_component}-th component has monomial {monomial} "
                                             f"with non-zero coeff {coeff}")
                    if (index_component < len(input_anf_vars) and
                        any(cvar2index[v] >= len(input_anf_vars) for v in monomial_vars)) or \
                            (index_component >= len(input_anf_vars) and
                             any(cvar2index[v] < len(input_anf_vars) for v in monomial_vars)):
                        if coeff != 0:
                            raise ValueError(f"L C L^(-1) (from {index_se_sol}-th solution) is not diagonal, "
                                             f"{index_component}-th component has monomial {monomial} "
                                             f"with non-zero coeff {coeff}")

        l_c_linv_sol = list(l_c_linv_sol)  # to be sliced

        aux_rep = {v: bpr(0) for v in c_input_vars[len(input_anf_vars):]}
        a_sol = substitute_anf(l_c_linv_sol[:len(anf)], aux_rep, bpr)
        aux_rep = {}
        for i in range(num_c_input_vars):
            if i < len(input_anf_vars):
                aux_rep[c_input_vars[i]] = bpr(0)
            else:
                aux_rep[c_input_vars[i]] = c_input_vars[i - len(input_anf_vars)]
        b_inv_sol = substitute_anf(l_c_linv_sol[len(anf):], aux_rep, bpr)

        if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
            smart_print(f"- SE (A, B) of F:")
            smart_print(" - A:")
            smart_print(get_anf_coeffmatrix_str(a_sol, c_input_vars[:len(input_anf_vars)]))
            smart_print(" - B^(-1):")
            smart_print(get_anf_coeffmatrix_str(b_inv_sol, c_input_vars[:len(anf)]))

        if check_se:
            if extra_var2val:
                a_sol_fixed = substitute_anf(a_sol, extra_var2val, bpr)
                b_inv_sol_fixed = substitute_anf(b_inv_sol, extra_var2val, bpr)
                if (index_se_sol == 0 and verbose) or (index_se_sol <= 2 and debug):
                    smart_print(f"- SE (A, B) of F (with {extra_var2val}):")
                    smart_print(" - A:")
                    smart_print(get_anf_coeffmatrix_str(a_sol_fixed, c_input_vars[:len(input_anf_vars)]))
                    smart_print(" - B^(-1):")
                    smart_print(get_anf_coeffmatrix_str(b_inv_sol_fixed, c_input_vars[:len(anf)]))
            else:
                a_sol_fixed = a_sol
                b_inv_sol_fixed = b_inv_sol

            aux_bpr = BooleanPolynomialRing(names=[str(v) for v in c_input_vars[:len(input_anf_vars)]])
            a_sol_fixed = [aux_bpr(component) for component in a_sol_fixed]
            aux_bpr = BooleanPolynomialRing(names=[str(v) for v in c_input_vars[:len(anf)]])
            b_inv_sol_fixed = [aux_bpr(component) for component in b_inv_sol_fixed]

            if left_se_degree == 1:
                if not anf2matrix(a_sol_fixed, c_input_vars[:len(input_anf_vars)]).is_invertible():
                    raise ValueError("A is not invertible")
            elif len(input_anf_vars) <= 12:
                if not is_invertible(anf2lut(a_sol_fixed)):
                    raise ValueError("A is not invertible")
            if inv_right_se_degree == 1:
                if not anf2matrix(b_inv_sol_fixed, c_input_vars[:len(anf)]).is_invertible():
                    raise ValueError("B is not invertible")
            elif len(anf) <= 12:
                if not is_invertible(anf2lut(b_inv_sol_fixed)):
                    raise ValueError("A is not invertible")

            if not missing_anf:
                # lhs = compose_anf_fast(b_inv_sol_fixed, anf_simple_bpr)
                # rhs = compose_anf_fast(anf_simple_bpr, a_sol_fixed)
                lhs = substitute_anf(b_inv_sol_fixed, {c_input_vars[i]: f for i, f in enumerate(anf)}, bpr)
                rhs = substitute_anf(anf, {input_anf_vars[i]: f for i, f in enumerate(a_sol_fixed)}, bpr)
                if len(lhs) != len(rhs) or any(lhs[i] != rhs[i] for i in range(len(lhs))):
                    msg = f"B^(-1) F != F A (from {index_se_sol}-th solution):\n"
                    msg += f"- B^(-1) F: \n{get_anf_coeffmatrix_str(lhs, c_input_vars[:len(input_anf_vars)])}\n"
                    msg += f"- F A: \n{get_anf_coeffmatrix_str(rhs, c_input_vars[:len(input_anf_vars)])}"
                    raise ValueError(msg)

        if not return_ccz_se:
            se_solutions[index_se_sol] = [a_sol, b_inv_sol]

    if verbose:
        smart_print("")

    # 5 - Output

    if verbose:
        smart_print(f"{get_time()} | returning outputs with mode='{new_kwargs['return_mode']}'")

    if "return_mode" not in solve_args and "num_sat_solutions" not in solve_args:
        if solve_args.get("return_total_num_solutions", False):
            smart_print("ignoring return_total_num_solutions")
        return se_solutions[0]
    elif new_kwargs['return_mode'] == "list_anfs":
        if solve_args.get("return_total_num_solutions", False):
            return se_solutions
        else:
            return se_solutions, graph_solutions[-1]
    elif new_kwargs['return_mode'] == "symbolic_anf":
        return se_solutions + list(graph_solutions[1:])
    else:
        assert new_kwargs['return_mode'] == "symbolic_coeffs"
        return [symbolic_coeffs] + list(graph_solutions[1:])


def _get_lowdeg_inv_equations(anf, bpr, max_deg=3, depth=2, input_vars=None):
    """Get some low degree invertibility constraints from a symbolic anf.

        >>> bpr = BooleanPolynomialRing(names=('x','y','z','a','b','c','d','e','f'))
        >>> x, y, z, a, b, c, d, e, f = bpr.gens()
        >>> matrix = sage.all.matrix(bpr, 3, 3, [[a, b, 0], [c, 0, d], [0, e, f]])
        >>> matrix.determinant() + 1
        a*d*e + b*c*f + 1
        >>> bin_vector = [a, b, c]
        >>> anf = matrix2anf(matrix, bool_poly_ring=bpr, input_vars=['x','y','z'], bin_vector=bin_vector)
        >>> get_anf_coeffmatrix_str(anf, input_vars=['x','y','z'])
        [x y z|1]
        [-----+-]
        [a b 0|a]
        [c 0 d|b]
        [0 e f|c]
        >>> for eq in _get_lowdeg_inv_equations(anf, bpr, max_deg=2, input_vars=['x','y','z']): print(_sp(eq))
        a*b + a + b + 1
        c*d + c + d + 1
        e*f + e + f + 1
        >>> anf = [a*x*y + b*x, c*x*y + d*a + e*z]
        >>> for eq in _get_lowdeg_inv_equations(anf, bpr, max_deg=2, input_vars=['x','y','z']): print(_sp(eq))
        a
        b + 1
        e + 1

    """
    if input_vars is None:
        aux_bpr = anf[0].parent()
        assert all(aux_bpr == f.parent() for f in anf)
        input_vars = aux_bpr.gens()

    def or_bits(a, b):
        return a + b + (a * b)

    vectorindex2_component = {}
    canonical_vectorindex = []

    for index_component, component in enumerate(anf):
        vectorindex = int2vector(2**index_component, len(anf))
        canonical_vectorindex.append(vectorindex)
        vectorindex.set_immutable()
        vectorindex2_component[vectorindex] = component - get_ct_coeff([component], input_vars=input_vars)[0]

    for current_depth in range(2, min(depth, len(canonical_vectorindex)) + 1):
        for currentd_vi in itertools.combinations(canonical_vectorindex, current_depth):
            currentd_vi = sum(currentd_vi)
            assert list(currentd_vi).count(1) == current_depth
            currentd_vi.set_immutable()

            first_one = None
            for first_one, bit in enumerate(currentd_vi):
                if bit == 1:
                    break
            d1_vi = int2vector(2**first_one, len(anf))
            d1_vi.set_immutable()
            prevd_vi = currentd_vi + d1_vi
            prevd_vi.set_immutable()

            assert list(d1_vi).count(1) == 1
            assert list(prevd_vi).count(1) == current_depth - 1

            vectorindex2_component[currentd_vi] = vectorindex2_component[d1_vi] + vectorindex2_component[prevd_vi]

    equations = BooleanPolynomialVector()
    for index_component, component in vectorindex2_component.items():
        if component in [0, 1]:  # ct functions are not balanced
            raise ValueError(f"found non-balanced component: {index_component}-th component {_sp(component)}")
        mon2coeff = get_all_symbolic_coeff(component, input_vars)
        eq_is_a_list = False
        deg_component = max(mon.degree() for mon in mon2coeff)

        if deg_component == 0:
            continue
        elif deg_component == 1:
            row_coeffs = set(mon2coeff.values())
            if 1 in row_coeffs or bpr.one() in row_coeffs or len(row_coeffs) - 2 > max_deg:
                # row_coeffs contains unique polys (non-zero, non-one)
                # if there are t unique terms in row_coeffs,
                # then deg(OR(row_coeffs)) >= t (with very high pr)
                # -2 is to consider dependent polys
                continue
            eq = bpr(sage.all.reduce(or_bits, row_coeffs)) + bpr(1)
        elif deg_component == 2:
            quad_mons = [mon for mon in mon2coeff if mon.degree() == 2]
            if len(quad_mons) > 1:
                # TODO: v2 consider QBVF with 2 quadratic terms and no foreign terms
                # in this case, only balanced class is
                # a(b1 + b2) + linear terms (excluded a, b1+b2, a+b1+b2)
                continue
            # general case: a*x*y + a*x + b*y + c*z + d*t
            # 2 cases:
            #   a == 1, then c | d == 1
            #   a == 0, then b | c | d must be 1
            # grouped by constraint: a(c | d) + (a+1)(b | c | d) == 1
            # equivalently, (c | d | b*(a-1) | a*(a-1)) == 1
            quad_mon = quad_mons[0]
            lin_mons = [mon for mon in mon2coeff if mon.degree() == 1]
            foreign_lin_mons = [mon for mon in lin_mons if mon.variables()[0] not in quad_mon.variables()]
            quad_coeff = mon2coeff[quad_mon]
            lin_coeffs = [mon2coeff[mon] for mon in lin_mons]
            foreign_lin_coeffs = [mon2coeff[mon] for mon in foreign_lin_mons]

            if not lin_coeffs:
                # a*x*y is not balanced for any a
                raise ValueError(f"found invalid equation 0 == 1 (from {index_component}-th component {_sp(component)}")
            else:
                if not foreign_lin_coeffs:
                    # if a*x*y + a*x + b*y, then a = 0, (a|b) = 1
                    eq = [bpr(quad_coeff + 0), bpr(sage.all.reduce(or_bits, lin_coeffs).subs({quad_coeff: 0}) + 1)]
                    eq_is_a_list = True
                else:
                    aux_eq1 = quad_coeff * sage.all.reduce(or_bits, foreign_lin_coeffs).subs({quad_coeff: 1})
                    aux_eq2 = (quad_coeff + 1) * sage.all.reduce(or_bits, lin_coeffs).subs({quad_coeff: 0})
                    eq = bpr(aux_eq1) + bpr(aux_eq2) + bpr(1)
                    # # equivalent equation (c | d | b*(a-1) | a*(a-1)) == 1 results in the same Boolean polynomial
                    # non_foreign_lin_mons = [mon for mon in lin_mons if mon.variables()[0] in quad_mon.variables()]
                    # non_foreign_lin_coeffs = [mon2coeff[mon] * (quad_coeff + 1) for mon in non_foreign_lin_mons]
                    # eq = bpr(sage.all.reduce(or_bits, foreign_lin_coeffs + non_foreign_lin_coeffs)) + 1
        else:
            continue

        if not eq_is_a_list:
            eq_list = [eq]
        else:
            eq_list = eq

        for eq in eq_list:
            if eq == 0:
                continue
            if eq == 1:
                raise ValueError(f"found invalid equation 0 == 1 (from {index_component}-th component {_sp(component)}")
            if eq.degree() <= max_deg:
                equations.append(eq)

    return equations
