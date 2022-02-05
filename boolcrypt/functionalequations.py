"""Solve functional equations with a SAT solver."""
import collections
import itertools
import math
import warnings

from boolcrypt.utilities import (
    get_smart_print, get_anf_coeffmatrix_str, substitute_anf, get_time,
    anf2matrix, get_all_symbolic_coeff, int2vector, get_symbolic_alg_deg,
    get_symbolic_anf, concatenate_anf, str2bp
)

import sage.all

from sage.rings.polynomial.pbori.pbori import BooleanPolynomialVector, substitute_variables, gauss_on_polys
from sage.sat.boolean_polynomials import solve as solve_sat

GF = sage.all.GF
PolynomialRing = sage.all.PolynomialRing
BooleanPolynomialRing = sage.all.BooleanPolynomialRing


# ----------------------------------------------------
# auxiliary functions for solve_functional_equation()
# ----------------------------------------------------


MAX_PRINTED_SIZE = 50  # polynomials are truncated after X chars when printed


def reduce(equations, mode="gauss", bpr=None, verbose=False, debug=False, filename=None):
    """Reduce a Boolean system of equations given as a list of Boolean polynomials.

    mode can be "gauss" (a BooleanPolynomialVector is returned)
    or "groebner" (a PolynomialSequence_gf2 is returned)

        >>> from boolcrypt.utilities import lut2anf, matrix2anf, compose_anf_fast
        >>> sbox3b = [0, 1, 2, 3, 4, 6, 7, 5]  # one linear component
        >>> bpr = BooleanPolynomialRing(3, "x0, x1, x2")
        >>> equations = lut2anf(sbox3b)
        >>> list(equations)
        [x0*x2 + x0 + x1*x2, x0*x2 + x1, x2]
        >>> m = matrix2anf(sage.all.matrix(bpr, 3, 3, [1, 0, 1, 1, 1, 1, 1, 1, 0]))
        >>> equations = compose_anf_fast(m, equations)
        >>> list(equations)
        [x0*x2 + x0 + x1*x2 + x2, x0 + x1*x2 + x1 + x2, x0 + x1*x2 + x1]
        >>> list(reduce(equations, mode="gauss", verbose=True, debug=True))
        reducing 3 equations with mode gauss and degrees (d,#) Counter({2: 3})
        system coefficient matrix:
        [x0*x2    x0 x1*x2    x1    x2]
        [-----------------------------]
        [    1     1     1     0     1]
        [    0     1     1     1     1]
        [    0     1     1     1     0]
        reduced system coefficient matrix:
        [x0*x2    x0 x1*x2    x1    x2]
        [-----------------------------]
        [    1     0     0     1     0]
        [    0     1     1     1     0]
        [    0     0     0     0     1]
        gauss-reduction obtained 3 equations with degrees (d,#) Counter({2: 2, 1: 1})
        [x0*x2 + x1, x0 + x1*x2 + x1, x2]
        >>> reduce(equations, mode="groebner", verbose=True)  # sbox3b is a permutation
        reducing 3 equations with mode groebner and degrees (d,#) Counter({2: 3})
        groebner-reduction obtained 3 equations with degrees (d,#) Counter({1: 3})
        [x0, x1, x2]

    """
    assert mode in ["gauss", "groebner"]

    if len(equations) == 0:
        return equations

    if bpr is None:
        bpr = equations[0].parent()
    assert all(eq.parent() == bpr for eq in equations)

    smart_print = get_smart_print(filename)

    if verbose:
        equation_degrees = collections.Counter()
        for eq in equations:
            equation_degrees[eq.degree()] += 1
        smart_print("reducing {} equations with mode {} and degrees (d,#) {}".format(
            len(equations), mode, equation_degrees))
    if debug and len(equations) <= 8:
        # .coefficient_matrix is too slow
        m, v = sage.all.Sequence(equations, bpr).coefficient_matrix()
        smart_print("system coefficient matrix:")
        aux = sage.all.matrix(bpr, m.nrows() + 1, m.ncols(), v.list() + m.list())
        aux.subdivide(row_lines=[1])
        smart_print(aux)

    if mode == "gauss":
        # gauss_on_polys is sensitive to different context managers
        # even if they are the same Boolean polynomial ring
        assert all(id(eq.parent()) == id(bpr) for eq in equations)
        reduced_eqs = gauss_on_polys(equations)
    elif mode == "groebner":
        try:
            reduced_eqs = bpr.ideal(list(equations)).groebner_basis()
        except RuntimeError as e:
            if not verbose:
                num_nonlinear_eqs = sum(int(eq.degree() >= 2) for eq in equations)
            else:
                num_nonlinear_eqs = sum(num for d, num in equation_degrees.items() if d >= 2)
            if num_nonlinear_eqs > 48:
                if verbose:
                    smart_print(f"groebner raised RuntimeError {e}, retrying with gauss")
                # for i in range(len(equations)):  equations[i] = bpr(str(equations[i]))
                reduced_eqs = gauss_on_polys(equations)
            else:
                if verbose:
                    smart_print(f"groebner raised RuntimeError {e}, retrying with C groebner")
                # old_bpr = bpr [...]  # if .change_ring, undo changes afterwards
                # bpr = BooleanPolynomialRing(names=[v for v in bpr.variable_names()], order="deglex")
                # smart_print("applying groebner with term order:", bpr.term_order())
                # equations = [bpr(eq) for eq in equations]
                from sage.rings.polynomial.pbori.parallel import groebner_basis_first_finished
                args1 = {'heuristic': False, "implementation": "C"}
                args2 = {'heuristic': True, "implementation": "C"}
                reduced_eqs = groebner_basis_first_finished(list(equations), args1, args2)
    else:
        raise ValueError("invalid mode")

    if debug and len(equations) <= 8:
        # .coefficient_matrix is too slow
        m, v = sage.all.Sequence(reduced_eqs, bpr).coefficient_matrix()
        smart_print("reduced system coefficient matrix:")
        aux = sage.all.matrix(bpr, m.nrows() + 1, m.ncols(), v.list() + m.list())
        aux.subdivide(row_lines=[1])
        smart_print(aux)
    if verbose:
        equation_degrees = collections.Counter()
        for eq in reduced_eqs:
            equation_degrees[eq.degree()] += 1
        smart_print("{}-reduction obtained {} equations with degrees (d,#) {}".format(
            mode, len(reduced_eqs), equation_degrees))

    return reduced_eqs


def _sp(polynomial):  # short print
    aux = str(polynomial)
    if len(aux) > MAX_PRINTED_SIZE:
        return f"BooleanPolynomial{polynomial.variables()}"
        # return aux[:MAX_PRINTED_SIZE] + "..."
    else:
        return aux


def _is_fixed_var(var, eq, bpr):
    for v in (eq + var).variables():
        if var == bpr(v):
            return False
    return True
    # return var not in [bpr(v) for v in (eq + var).variables()]


# TODO: update docstring with updated_vars
def _find_fix_var(eq, only_linear=False, prev_eqs=None, fixedvar2ct=None, fixedvar2expr=None,
                  bpr=None, check=True, verbose=False, filename=None, indentation_lvl=0):
    """Find one fixed variable in a Boolean equation given by a Boolean polynomial.

    Given an equation with Boolean variables x0 > ... > xi > ... > xn,
    find one fixed/dependent variable, that is, an assignment x{i} = f(x{i+1},..,xn).
    Among all the possible fixed variables, the biggest one is chosen.
    (according to the term order of the Boolean polynomial ring).

    This method returns None if no fixed variable is found, otherwise
    a triple (x{i}, f(x{i+1},..,xn), J), where J is a list of indices
    of prev_eqs (if not None) that are found to contained fixed variables
    after the found fixed variable is replaces in prev_eqs.

    If only_linear=True, only find linear assignments.

    If check=True, ensures that the found fixed variable doesn't appear
    in other equations or in the value/expression of other fixed variable.

        >>> x, y, z, t = BooleanPolynomialRing(4, "x, y, z, t").gens()
        >>> _find_fix_var(x + y + z*t)
        (x, y + z*t, [], [])
        >>> _find_fix_var(x + y + z*t, only_linear=True)
        >>> other_bpr = BooleanPolynomialRing(4, "t, z, y, x")
        >>> _find_fix_var(other_bpr(x + y + z*t))
        (y, t*z + x, [], [])
        >>> _find_fix_var(x + y + z*t, prev_eqs=[x, y, z, t])
        (x, y + z*t, [0], [])
        >>> _find_fix_var(x + y + z, fixedvar2expr={t: x}, fixedvar2ct={})
        (x, y + z, [], [t])

    """
    if only_linear:
        if eq.degree() >= 2:
            return None

    smart_print = get_smart_print(filename)

    if bpr is None:
        bpr = eq.parent()
    assert not(fixedvar2ct is None and fixedvar2expr is not None)
    assert not(fixedvar2ct is not None and fixedvar2expr is None)
    if fixedvar2ct is None:
        fixedvar2ct = {}
    if fixedvar2expr is None:
        fixedvar2expr = {}
    if prev_eqs is None:
        prev_eqs = []

    slow_sub = bpr.n_variables() < 32
    if not slow_sub:
        base_ordered_replacement = []
        var2index = {}
        for index_var, var in enumerate(bpr.gens()):
            var2index[var] = index_var
            base_ordered_replacement.append(var)

    def subs(expr, var, val):
        if slow_sub:
            return bpr(expr.subs({var: val}))
        else:
            return substitute_variables(bpr, ordered_replacement, expr)

    # take the biggest variable (probably the pivot)
    # thus, smallest vars represent free parameters
    first_var = True
    for var in reversed(sorted(bpr(v) for v in eq.variables())):
        if _is_fixed_var(var, eq, bpr):
            if var in fixedvar2ct or var in fixedvar2expr:
                raise ValueError("fixed variable {} found but already in fixed_vars {} | eq={}".format(
                    var, {**fixedvar2ct, **fixedvar2expr}, eq))

            val = eq + var
            prev_eqs_with_fx = []
            updated_vars = []

            if verbose:
                smart_print("\t"*indentation_lvl + "found {}fixed variable {} <- {}".format(
                    "" if first_var else "non-pivot ", var, _sp(val)))

            if check:
                if not slow_sub:
                    ordered_replacement = base_ordered_replacement.copy()
                    ordered_replacement[var2index[var]] = val

                il = indentation_lvl + 1
                for fx_var in list(fixedvar2expr.keys()):  # list() to avoid "mutated during iteration error"
                    if any(var == bpr(v_i) for v_i in fixedvar2expr[fx_var].variables()):
                        updated_vars.append(fx_var)
                        other_val = subs(fixedvar2expr[fx_var], var, val)
                        if other_val in [0, 1]:
                            del fixedvar2expr[fx_var]
                            fixedvar2ct[fx_var] = other_val
                        else:
                            fixedvar2expr[fx_var] = other_val
                        if verbose:
                            smart_print("\t"*il + "fixed_vars[{}] <-- {}".format(
                                fx_var, _sp(other_val)))

                for i in range(len(prev_eqs)):
                    if any(var == bpr(v_i) for v_i in prev_eqs[i].variables()):
                        prev_eqs[i] = subs(prev_eqs[i], var, val)
                        if verbose:
                            smart_print("\t"*il + "prev_eqs[{}] <-- {}".format(
                                i, _sp(prev_eqs[i])))
                        if i not in prev_eqs_with_fx and (not only_linear or prev_eqs[i].degree() <= 1):
                            if any(_is_fixed_var(bpr(v), prev_eqs[i], bpr) for v in prev_eqs[i].variables()):
                                prev_eqs_with_fx.append(i)
                                if verbose:
                                    smart_print("\t"*(il+1) + "prev_eqs[{}] now contains a fixed variable".format(i))

            return var, val, prev_eqs_with_fx, updated_vars
        else:
            first_var = False
    else:
        if eq.degree() <= 1:
            raise ValueError("could not find any fixed variable in linear equation {}".format(eq))
        return None


def find_fixed_vars(equations, only_linear=False, initial_r_mode=None, repeat_with_r_mode=None,
                    initial_fixed_vars=None, bpr=None, check=True, verbose=False, debug=False, filename=None):
    """Find fixed variables in a system of equations given as a list of Boolean polynomials.

    Given a system with Boolean variables x0 > ... > xi > ... > xn,
    find fixed/dependent variables, that is, assignments x{i} = f(x{i+1},..,xn).
    Note that the term order of the Boolean polynomial ring
    affects the variables that are fixed.

    This method returns a pair containing an OrderedDic with the
    fixed variables found and a BooleanPolynomialVector with the
    resulting system after replacing the fixed variables by their
    value/expression.

    The parameters initial_r_mode and repeat_with_r_mode can be "gauss" or "groebner"
    as in reduce(). initial_r_mode is used to reduce the the given list of equations.
    If repeat_with_r_mode is given, this method is repeatdly called again
    (with initial reduction the one given by repeat_with_r_mode) until
    no fixed variables are found.

    If the optional parameter initial_fixed_vars is given with a
    dictionary containing initial fixed variables, this method
    replaces the expression of these initial fixed variables
    with the new fixed variables found.

    If only_linear=True, only find linear assignment, that is,
    relations x{i} = f(x{i+1},..,xn) with f of degree up to 1.

    If check=True, ensures that no fixed variables appears in the
    resulting system or in the value/expression of other fixed variable.

    verbose and debug determine the amount of information printed to the output.
    if a string is given to filename, the output is printed to that file

        >>> from sage.crypto.sbox import SBox
        >>> from boolcrypt.utilities import lut2anf
        >>> sbox3b = SBox((0, 1, 2, 3, 4, 6, 7, 5))  # one linear component
        >>> list(lut2anf(list(sbox3b)))
        [x0*x2 + x0 + x1*x2, x0*x2 + x1, x2]
        >>> bpr = BooleanPolynomialRing(6, "y0, y1, y2, x0, x1, x2", order="lex")
        >>> input_vars, output_vars = list(reversed(bpr.gens()[3:])), list(reversed(bpr.gens()[:3]))
        >>> eqs = [bpr(f) for f in sbox3b.polynomials(X=input_vars, Y=output_vars)]
        >>> eqs = reduce(eqs, mode="groebner", bpr=bpr)
        >>> list(eqs)
        [y0 + x0*x2 + x0 + x1*x2, y1 + x0*x2 + x1, y2 + x2]
        >>> fixed_vars, new_eqs = find_fixed_vars(eqs, only_linear=False,
        ...     verbose=True, debug=True)  # doctest: +NORMALIZE_WHITESPACE
        finding fixed variables in 3 equations with degrees (d, #) Counter({2: 2, 1: 1})
        in Boolean PolynomialRing in y0, y1, y2, x0, x1, x2 with term order Lexicographic term order
            eqs[2] = y2 + x2
                found fixed variable y2 <- x2
            eqs[1] = y1 + x0*x2 + x1
                found fixed variable y1 <- x0*x2 + x1
            eqs[0] = y0 + x0*x2 + x0 + x1*x2
                found fixed variable y0 <- x0*x2 + x0 + x1*x2
        found 3 fixed variables, resulting in 0 equations
        >>> fixed_vars, list(new_eqs)
        (OrderedDict([(y2, x2), (y1, x0*x2 + x1), (y0, x0*x2 + x0 + x1*x2)]), [])
        >>> fixed_vars, new_eqs = find_fixed_vars(eqs, only_linear=True, initial_r_mode="gauss",
        ...     repeat_with_r_mode="gauss", verbose=True, debug=False)  # doctest: +NORMALIZE_WHITESPACE
        reducing 3 equations with mode gauss and degrees (d,#) Counter({2: 2, 1: 1})
        gauss-reduction obtained 3 equations with degrees (d,#) Counter({2: 2, 1: 1})
        found 1 fixed variables, resulting in 2 equations with degrees (d, #) Counter({2: 2})
        > repeating find_fixed_vars with initial reduction_mode gauss
        reducing 2 equations with mode gauss and degrees (d,#) Counter({2: 2})
        gauss-reduction obtained 2 equations with degrees (d,#) Counter({2: 2})
        found 1 fixed variables, resulting in 2 equations with degrees (d, #) Counter({2: 2})
        > last find_fixed_vars call found 0 new fixed variables and removed 0 equations
        >>> fixed_vars, list(new_eqs)
        (OrderedDict([(y2, x2)]), [y0 + x0*x2 + x0 + x1*x2, y1 + x0*x2 + x1])
        >>> x, y, z, t = BooleanPolynomialRing(names="x, y, z, t").gens()
        >>> eqs = [(x*y + z + 1) * (t*z + y) + 1]
        >>> fixed_vars, new_eqs = find_fixed_vars(eqs, verbose=True, debug=True)  # doctest: +NORMALIZE_WHITESPACE
        finding fixed variables in 1 equations with degrees (d, #) Counter({4: 1})
        in Boolean PolynomialRing in x, y, z, t with term order Lexicographic term order
            eqs[0] = x*y*z*t + x*y + y*z + y + 1
                adding equations from common factors
            eqs[1] = y + 1
                found fixed variable y <- 1
            eqs[0] = x*z*t + x + z
        found 1 fixed variables, resulting in 1 equations with degrees (d, #) Counter({3: 1})
        >>> fixed_vars, list(new_eqs)
        (OrderedDict([(y, 1)]), [x*z*t + x + z])

    """
    smart_print = get_smart_print(filename)

    if len(equations) == 0:
        if initial_fixed_vars is None:
            initial_fixed_vars = collections.OrderedDict()
        return initial_fixed_vars, equations

    if initial_fixed_vars is not None:
        var2ct = collections.OrderedDict()
        var2expr = collections.OrderedDict()
        for var, value in initial_fixed_vars.items():
            if value in [0, 1]:
                var2ct[var] = value
            else:
                var2expr[var] = value
    else:
        var2ct = collections.OrderedDict()
        var2expr = collections.OrderedDict()

    if bpr is None:
        bpr = equations[0].parent()
    assert all(eq.parent() == bpr for eq in equations)
    bpr_gens_dict = bpr.gens_dict()

    if debug:
        verbose = True

    if initial_r_mode is not None:
        equations = reduce(equations, mode=initial_r_mode, bpr=bpr, verbose=verbose, debug=debug, filename=filename)

    if debug:
        aux = ""
        if initial_r_mode is None:
            equation_degrees = collections.Counter()
            for eq in equations:
                equation_degrees[eq.degree()] += 1
            aux += "in {} equations with degrees (d, #) {}".format(len(equations), equation_degrees)
            aux += "\n" if debug else ""
        aux += "in {} with term order {}".format(bpr, bpr.term_order())
        smart_print("finding fixed variables {}".format(aux))

    ordered_replacement = []
    var2index_ordered_replacement = {}
    for index_var, var in enumerate(bpr.gens()):
        var2index_ordered_replacement[var] = index_var
        if var in var2ct:
            value = var2ct[var]
        elif var in var2expr:
            value = var2expr[var]
        else:
            value = var
        ordered_replacement.append(value)

    if only_linear and len(var2expr) == 0 and initial_r_mode is not None and \
            all(order == sage.all.TermOrder('deglex') for order in bpr.term_order().blocks()):
        # in this case, the first linear equations are not checked
        check_find_fix_var = False
    else:
        check_find_fix_var = True

    # backward substitution with an upper triangular matrix (starting with the last equation)
    equations = list(equations)  # need to be a list to use pop()
    new_equations = []  # need to be a list to remove elements
    while len(equations) > 0:
        index_eq = len(equations) - 1

        if check_find_fix_var is False and equations[-1].degree() >= 2:
            check_find_fix_var = True

        eq = equations.pop(-1)
        # only need to sub previous equations and fixed_vars
        new_eq = substitute_variables(bpr, ordered_replacement, eq)
        # new_eq = bpr(eq.subs(var2ct).subs(var2expr))

        if new_eq == 0:
            continue
        elif new_eq == 1:
            raise ValueError(f"found 0 == 1 from eqs[{index_eq}] = ({eq}).subs({var2ct, var2expr})")

        if debug:
            if new_eq != eq:
                aux = " | before substitution {}".format(_sp(eq))
            else:
                aux = ""
            smart_print("\teqs[{}] = {}{}".format(index_eq, _sp(new_eq), aux))

        result = _find_fix_var(new_eq, only_linear=only_linear, prev_eqs=new_equations,
                               fixedvar2ct=var2ct, fixedvar2expr=var2expr, bpr=bpr, check=check_find_fix_var,
                               verbose=debug, filename=filename, indentation_lvl=2 if debug else 1)
        if result is not None:
            var, val, prev_eqs_with_fv, updated_vars = result
            if val in [0, 1]:
                var2ct[var] = val
                ordered_replacement[var2index_ordered_replacement[var]] = val
            else:
                var2expr[var] = val
                ordered_replacement[var2index_ordered_replacement[var]] = val
            if prev_eqs_with_fv:
                if debug:
                    smart_print("\t\tchecking new_equations{} before checking eq[{}]".format(
                        prev_eqs_with_fv, index_eq - 1))
                for index_eq_w_fv in reversed(prev_eqs_with_fv):
                    aux = new_equations[index_eq_w_fv]
                    del new_equations[index_eq_w_fv]
                    equations.append(aux)
            for u_v in updated_vars:
                if debug:
                    smart_print("\t\tupdating ordered_replacement with updated_vars", updated_vars)
                if u_v in var2ct:
                    ordered_replacement[var2index_ordered_replacement[u_v]] = var2ct[u_v]
                else:
                    ordered_replacement[var2index_ordered_replacement[u_v]] = var2expr[u_v]
        else:
            if len(str(new_eq)) >= 128:
                if new_eq not in new_equations:
                    new_equations.append(new_eq)
            else:
                # e.g., if x1*x2 + 1 == 0, add the equations x1==1, x2==1
                if new_eq.constant_coefficient() == 1:
                    sr_expr = sage.all.symbolic_expression(str(new_eq)) - 1
                else:
                    sr_expr = sage.all.symbolic_expression(str(new_eq)) + 1
                sr_expr = sr_expr.collect_common_factors()
                if sr_expr.operator().__name__.startswith("mul"):
                    if debug:
                        smart_print(f"\t\tadding equations from common factors")
                    for operand in sr_expr.collect_common_factors().operands():
                        equations.append(str2bp(str(operand) + " + 1", bpr_gens_dict))
                else:
                    if new_eq not in new_equations:
                        new_equations.append(new_eq)

    if verbose:
        aux = ""
        num_zero_eqs = 0
        if new_equations:
            equation_degrees = collections.Counter()
            for eq in new_equations:
                if eq == 0:
                    num_zero_eqs += 1
                    continue
                deg = eq.degree()
                equation_degrees[deg] += 1
            aux += f" with degrees (d, #) {equation_degrees}"
        smart_print("found {} fixed variables, resulting in {} equations{}".format(
            len(var2expr) + len(var2ct), len(new_equations) - num_zero_eqs, aux))

    if repeat_with_r_mode is not None:
        while True:
            if verbose:
                smart_print("> repeating find_fixed_vars with initial reduction_mode {}".format(repeat_with_r_mode))
            other_coeff2expr, other_new_equations = find_fixed_vars(
                new_equations, only_linear=only_linear, initial_r_mode=repeat_with_r_mode, repeat_with_r_mode=None,
                initial_fixed_vars=var2expr, bpr=bpr, check=check, verbose=verbose, debug=debug, filename=filename)
            assert len(other_coeff2expr) >= len(var2expr)
            if verbose:
                smart_print(f"> last find_fixed_vars call found {len(other_coeff2expr) - len(var2expr)}"
                            f" new fixed variables and removed {len(new_equations) - len(other_new_equations)} equations")
            to_break = other_coeff2expr == var2expr
            var2expr = other_coeff2expr
            new_equations = other_new_equations
            if to_break:
                # even if other_coeff2expr == coeff2expr, other_new_equations < new_equations
                break
    else:
        # always return a BooleanPolynomialVector for consistency
        aux = BooleanPolynomialVector()
        for new_eq in reversed(new_equations):
            if new_eq != 0:
                aux.append(new_eq)
        new_equations = aux

    fixed_vars = var2ct.copy()
    fixed_vars.update(var2expr)

    if check:
        for prev_var in fixed_vars:
            for v in fixed_vars[prev_var].variables():
                v = bpr(v)
                if v in fixed_vars:
                    raise ValueError("fixed variable {} in fixed_vars[{}] = {} ".format(
                        v, prev_var, fixed_vars[prev_var]))
        for i in range(len(new_equations)):
            for v in new_equations[i].variables():
                v = bpr(v)
                eq = new_equations[i]
                if v in fixed_vars:
                    raise ValueError("fixed variable {} in new_equations[{}] = {} ".format(v, i, eq))
                if (not only_linear or eq.degree() == 1) and _is_fixed_var(v, eq, bpr):
                    raise ValueError("undetected fixed var {} in new_equations[{}] = {} ".format(v, i, eq))

    return fixed_vars, new_equations

# ----------------------------------------------------
# ----------------------------------------------------
# ----------------------------------------------------


# TODO: add to docstring initial_fixed_vars, ignore_initial_parsing, check_find_fixed_vars
#       return_mode = ["symbolic_coeffs", "lincomb_solutions"],
# TODO: v2 print_common_nonlinear_vars
def solve_functional_equation(
    # mandatory args
    lhs_anfs, rhs_anfs,
    lhs_input_vars, rhs_input_vars,
    num_sat_solutions,
    return_mode,
    # alternative modes
    find_redundant_equations=None,
    # solving args
    initial_equations=None,
    initial_fixed_vars=None,
    reduction_mode="gauss",
    only_linear_fixed_vars=False,
    find_linear_combinations_in_solutions=False,
    # optimization args
    threads=1,
    num_sols_per_base_sol_to_check=1,
    bpr=None,
    ignore_varnames=None,
    ignore_initial_parsing=False,
    check_find_fixed_vars=True,
    # printing args
    return_total_num_solutions=False,
    verbose=False, debug=False, filename=None
    # print_common_nonlinear_vars=False,
):
    """Solve a functional equation F = G given by list of Boolean polynomials.

    This methods requires the CryptoMiniSat package to be installed in SageMath.

    The left hand side F(x) = ...F1(F0(x) is given a list of ANF [F0, F1, ...],
    where some of them can be symbolic ANFs.
    The right hand side G(x) = ...G1(G0(x) can be given similarly [G0, G1, ...],
    or it can be given a list of integers [d0, d1, ..., dd].
    In the latter case, the problem changes to find F that only have
    monomials with degrees [d0, d1, ..., dd].
    At least one of the ANFs Fi or Gj should be a symbolic anf.

    lhs_input_vars is a list of the inputs vars (a list of Boolean variables
    or strings) for each ANF in F (similarly for rhs_input_vars and G).
    If rhs_anfs is given as a list of integers, the value of rhs_input_vars
    is ignored.

    num_sat_solutions is the number of solutions to be found by the SAT solver.
    To find all solutions, use None or sage.all.infinity.
    Note that number of actual solutions can be higher than the
    number of solutions internally found by the SAT solver,
    as fixed variables and free variables are not passed to the SAT solver.

    If the system of equations is found to be inconsistent (unsatisfiable),
    a ValueError exception is raised.

    If return_mode="list_anfs", return a list of solutions [s0, s1, ...],
    where each solution si = [siF, siG] is a pair containing the list of
    non-symbolic ANFs of the left and right side, that is,
    [siF, siG] = [[siF0, siF1, ...], [siG0, siG1, ...]].
    If return_mode="list_coeffs", return a tuple containing
    the list of solutions [s0, s1, ...], where each si is a list
    containing the ANF coefficients of [siF, siG], and a list
    with the free variables.

    If return_mode="symbolic_anf", the solutions are given symbolically
    that is, a 4-tuple is returned (symF, symG, num_sols, eqs).
    For symF = [symF0, symF1, ...], symFi is the symbolic ANF of Fi,
    where each coefficient is substituted with the fixed variables found
    (and similar for symG and symGi).
    The number num_sols represents the total number of solutions found.
    The list eqs contain the equations that the symbolic coefficients
    satisfy that could not be reduced more.

    If return_mode=raw_equations, return the list of equations associated
    to the functional problem before finding fixed variables and before
    calling the SAT solver.

    A Boolean polynomial ring bpr can be given to determine the
    term order. Otherwise, lexicographic order will be used
    (x0 > x1 > ..., F0 > F1 > ... > G0 > G1 > ... ).

    A list of equations can be given in find_redundant_equations.
    In that case, instead of solving the functional equation,
    it is returned the list of equations that are satisfied by all solutions.

    A list of Boolean equations (or strings) can be given in initial_equations
    which will be added as extra constraints to the funcional equation.

    reduction_mode is the type of reduction (None, "gauss" or "groebner")
    to apply before the SAT solver.

    Before the SAT solver is called, fixed variables are searched
    in the equations. If only_linear_fixed_vars is True, only
    linear assignments are searched, that is,
    relations x{i} = f(x{i+1},..,xn) with f of degree up to 1.

    find_linear_combinations_in_solutions determines whether to search
    for linear combinations among the solutions obtained from the SAT solver.
    The obtained linear combinations are used to simplify
    the system of equations and the list of fixed variables.
    If the number of obtained SAT solutions is less than the given
    num_sat_solutions, find_linear_combinations_in_solutions is
    automatically enabled.

    If return_total_num_solutions is True, append to the output
    the number of total solutions (taking into account the free variables).

    A list of variables (strings or Boolean variables) can be given in
    ignore_varnames, which won't be included in the solutions and will
    be set to 0 if they are free variables.

    num_sols_per_base_sol_to_check determines the number of solutions
    per base solution that are checked, that is, that are given
    to the verification test F = G where F and G are substituted with
    the exact non-symbolic coefficients of the solution.

    threads determines the number of threads for the SAT solver to use.

    verbose and debug (True or False values) determine
    the amount of information printed to the output.
    if a string is given to filename, the output is printed to that file

        >>> from boolcrypt.utilities import lut2anf, invert_lut
        >>> # example 1: finding the inverse of F0 by solving F1(F0) = Identity
        >>> f0 = lut2anf((0, 1, 2, 3, 4, 6, 7, 5))
        >>> f1 = get_symbolic_anf(2, 3, 3)
        >>> g0 = lut2anf(list(range(2**3)))  # identity
        >>> input_vars = ["x0", "x1", "x2", "x3"]
        >>> list_anfs = solve_functional_equation([f0, f1], [g0], [input_vars, input_vars], [input_vars],
        ...     num_sat_solutions=1, return_mode="list_anfs", verbose=True)  # doctest: +NORMALIZE_WHITESPACE, +ELLIPSIS
        solving the functional equation F1(F0) = G0
        - F1:
        [ x0*x1  x0*x2  x1*x2|    x0     x1     x2|     1]
        [--------------------+--------------------+------]
        [a0_0_1 a0_0_2 a0_1_2|  a0_0   a0_1   a0_2|    a0]
        [a1_0_1 a1_0_2 a1_1_2|  a1_0   a1_1   a1_2|    a1]
        [a2_0_1 a2_0_2 a2_1_2|  a2_0   a2_1   a2_2|    a2]
        - F0:
        [x0*x2 x1*x2|   x0    x1    x2]
        [-----------+-----------------]
        [    1     1|    1     0     0]
        [    1     0|    0     1     0]
        [    0     0|    0     0     1]
        - G0:
        [x0 x1 x2]
        [--------]
        [ 1  0  0]
        [ 0  1  0]
        [ 0  0  1]
        number of input variables: 4
        number of symbolic coefficients: 21
        ... | computing F and G
        ... | getting equations from F + G = 0
        ... | finding fixed and free variables and reducing system
        reducing 21 equations with mode gauss and degrees (d,#) Counter({1: 21})
        gauss-reduction obtained 21 equations with degrees (d,#) Counter({1: 21})
        found 21 fixed variables, resulting in 0 equations
        > repeating find_fixed_vars with initial reduction_mode gauss
        > last find_fixed_vars call found 0 new fixed variables and removed 0 equations
        fixed variables (21): [('a2', 0), ('a2_2', 1), ('a2_1', 0), ('a2_0', 0), ('a2_1_2', 0), ('a2_0_2', 0),
        ('a2_0_1', 0), ('a1', 0), ('a1_2', 0), ('a1_1', 1), ('a1_0', 0), ('a1_1_2', 1), ('a1_0_2', 1),
        ('a1_0_1', 0), ('a0', 0), ('a0_2', 0), ('a0_1', 0), ('a0_0', 1), ('a0_1_2', 1), ('a0_0_2', 0), ('a0_0_1', 0)]
        free variables (0): []
        ... | ignoring SAT solving step
        total number of solutions: 1
        ... | returning outputs with mode='list_anfs'
        >>> get_anf_coeffmatrix_str(list_anfs[0][0][1], input_vars=input_vars)  # f1
        [x0*x2 x1*x2|   x0    x1    x2]
        [-----------+-----------------]
        [    0     1|    1     0     0]
        [    1     1|    0     1     0]
        [    0     0|    0     0     1]
        >>> # same example, but now f1 is given and f0 is symbolic
        >>> f0 = get_symbolic_anf(2, 3, 3)
        >>> f1 = lut2anf(invert_lut([0, 1, 2, 3, 4, 6, 7, 5]))
        >>> list_anfs = solve_functional_equation([f0, f1], [g0], [input_vars, input_vars], [input_vars],
        ...     num_sat_solutions=1, return_mode="list_anfs")
        >>> get_anf_coeffmatrix_str(list_anfs[0][0][0], input_vars=input_vars)  # f0
        [x0*x2 x1*x2|   x0    x1    x2]
        [-----------+-----------------]
        [    1     1|    1     0     0]
        [    1     0|    0     1     0]
        [    0     0|    0     0     1]
        >>> # example 2: finding a 2-bit linear permutation F0 by solving [(y,x), F0] = [1, 1]
        >>> #            with the extra condition a0_0 + 0
        >>> f0 = get_symbolic_anf(1, 2, 2, ct_terms=False)
        >>> f1 = lut2anf([0, 2, 1, 3])  # (x, y) to (y, x)
        >>> input_vars = ["x0", "x1"]
        >>> init_eq = ["a0_0", anf2matrix(f0, input_vars).determinant() + 1]
        >>> result = solve_functional_equation([f0, f1], [1, 1], [input_vars, input_vars], None,
        ...     num_sat_solutions=None, return_mode="symbolic_anf", initial_equations=init_eq, reduction_mode=None,
        ...     verbose=True, debug=True)  # doctest: +NORMALIZE_WHITESPACE, +ELLIPSIS
        solving the functional equation F1(F0) = degrees([1, 1])
        - F1:
        [x0 x1]
        [-----]
        [ 0  1]
        [ 1  0]
        - F0:
        [  x0   x1]
        [---------]
        [a0_0 a0_1]
        [a1_0 a1_1]
        input variables (2): ['x0', 'x1']
        symbolic coefficients (4): ['a0_0', 'a0_1', 'a1_0', 'a1_1']
        Boolean PolynomialRing in x0, x1, a0_0, a0_1, a1_0, a1_1
        initial equations (2):
    	    a0_0
    	    a0_0*a1_1 + a0_1*a1_0 + 1
        ... | computing F and G
        - F (after composition):
        [  x0   x1]
        [---------]
        [a1_0 a1_1]
        [a0_0 a0_1]
        ... | getting equations from F + G = 0
        no equation added from F + G = 0
        ... | finding fixed and free variables
        finding fixed variables in 2 equations with degrees (d, #) Counter({1: 1, 2: 1})
        in Boolean PolynomialRing in x0, x1, a0_0, a0_1, a1_0, a1_1 with term order Lexicographic term order
            eqs[1] = a0_0*a1_1 + a0_1*a1_0 + 1
            eqs[0] = a0_0
                found fixed variable a0_0 <- 0
                    prev_eqs[0] <-- a0_1*a1_0 + 1
        found 1 fixed variables, resulting in 1 equations with degrees (d, #) Counter({2: 1})
        fixed variables (1): [('a0_0', 0)]
        free variables (1): [a1_1]
        ... | solving 1 equations with 2 variables using SAT solver
        solver options: num_sat_solutions=+Infinity, threads=1
        system variables: [a1_0, a0_1]
        ... | parsing 1 SAT solutions found (total number of solutions 2 = 2^{1})
        SAT solutions:
            {a0_1: 1, a1_0: 1}
        Base solution 1 out of 1, checking full solution 1 out of 1:
         - sat solution                          : {a0_1: 1, a1_0: 1}
         - sat solution + fixed vars             : OrderedDict([(a0_1, 1), (a1_0, 1), (a0_0, 0)])
         - sat solution + fixed vars + free vars : {a0_1: 1, a1_0: 1, a0_0: 0, a1_1: 0}
         - F:
        [x0 x1]
        [-----]
        [ 1  0]
        [ 0  1]
        ... | finding linear combinations of variables among the SAT solutions
        linear combinations (2): ['a1_0 + 1', 'a0_1 + 1']
        linear combinations (matrix form)
        [a1_0 a0_1    1]
        [--------------]
        [   1    0    1]
        [   0    1    1]
        ... | reducing system with the linear combinations obtained
        finding fixed variables in 3 equations with degrees (d, #) Counter({1: 2, 2: 1})
        in Boolean PolynomialRing in x0, x1, a0_0, a0_1, a1_0, a1_1 with term order Lexicographic term order
            eqs[2] = a0_1 + 1
                found fixed variable a0_1 <- 1
            eqs[1] = a1_0 + 1
                found fixed variable a1_0 <- 1
        found 2 fixed variables, resulting in 0 equations
        fixed variables (3): [('a0_0', 0), ('a0_1', 1), ('a1_0', 1)]
        number of system variables changed to 0
        system variables (0): []
        number of equations changed to 0
        ... | returning outputs with mode='symbolic_anf'
        >>> get_anf_coeffmatrix_str(result[0][0][0], input_vars=input_vars)  # f0
        [  x0   x1]
        [---------]
        [   0    1]
        [   1 a1_1]
        >>> list(result[1])  # equations
        []

    """
    smart_print = get_smart_print(filename)

    if debug:
        verbose = True

    assert return_mode in ["list_anfs", "list_coeffs", "symbolic_anf", "symbolic_coeffs",
                           "raw_equations", "lincomb_solutions"]
    assert reduction_mode in [None, "gauss", "groebner"]

    if all(isinstance(component, int) for component in rhs_anfs):
        rhs_degrees = rhs_anfs
        rhs_anfs = []
        rhs_input_vars = []
    else:
        rhs_degrees = None

    assert len(lhs_anfs) == len(lhs_input_vars) and len(rhs_anfs) == len(rhs_input_vars), \
        f"{len(lhs_anfs)} == {len(lhs_input_vars)}, {len(rhs_anfs)} == {len(rhs_input_vars)}"

    if initial_equations is None:
        initial_equations = []
    if initial_fixed_vars is None:
        initial_fixed_vars = collections.OrderedDict()

    if ignore_varnames is None:
        ignore_varnames = set()
    else:
        ignore_varnames = set(str(v) for v in ignore_varnames)

    # 1. Find common Boolean polynomial ring

    if bpr is None:
        # (x0 > x1 > ..., F0 > F1 > ... > G0 > G1 > ... > initial equations)
        all_varnames = []
        for anf_input_vars in itertools.chain(lhs_input_vars, rhs_input_vars):
            for var in anf_input_vars:
                assert not isinstance(var, int)
                varname = str(var)
                if varname not in all_varnames:
                    all_varnames.append(varname)
        num_total_input_vars = len(all_varnames)
        for anf in itertools.chain(lhs_anfs, rhs_anfs):
            aux_anf_bpr = anf[0].parent()
            assert all(aux_anf_bpr == component.parent() for component in anf)
            for varname in aux_anf_bpr.variable_names():
                if varname not in all_varnames:
                    all_varnames.append(varname)
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
        if find_redundant_equations is not None:
            for eq in find_redundant_equations:
                if isinstance(eq, str):
                    eq = sage.all.symbolic_expression(eq)
                for var in eq.variables():
                    varname = str(var)
                    if varname not in all_varnames:
                        all_varnames.append(varname)
        if only_linear_fixed_vars:
            order = "deglex"
        else:
            order = "lex"
        bpr = BooleanPolynomialRing(len(all_varnames), all_varnames, order=order)
        num_total_symbolic_coeffs = len(all_varnames) - num_total_input_vars
    else:
        input_varnames = set()
        for anf_input_vars in itertools.chain(lhs_input_vars, rhs_input_vars):
            for var in anf_input_vars:
                assert not isinstance(var, int)
                input_varnames.add(str(var))
        num_total_input_vars = len(input_varnames)
        num_total_symbolic_coeffs = len(bpr.gens()) - num_total_input_vars
        all_varnames = bpr.variable_names()

    if not ignore_initial_parsing:
        aux_ifv = collections.OrderedDict()
        for var, value in initial_fixed_vars.items():
            aux_ifv[bpr(var)] = bpr(value)
        initial_fixed_vars = aux_ifv

        aux_list_anfs = []
        for anf in lhs_anfs:
            aux_anf = substitute_anf(anf, initial_fixed_vars, bpr)
            # aux_anf = BooleanPolynomialVector()
            # for component in anf:
            #     aux_anf.append(bpr(bpr(component).subs(initial_fixed_vars)))
            aux_list_anfs.append(aux_anf)
        lhs_anfs = aux_list_anfs
        aux_list_anfs = []
        for anf in rhs_anfs:
            aux_anf = substitute_anf(anf, initial_fixed_vars, bpr)
            # aux_anf = BooleanPolynomialVector()
            # for component in anf:
            #     aux_anf.append(bpr(bpr(component).subs(initial_fixed_vars)))
            aux_list_anfs.append(aux_anf)
        rhs_anfs = aux_list_anfs

        lhs_input_vars = [[bpr(v) for v in anf_iv] for anf_iv in lhs_input_vars]
        rhs_input_vars = [[bpr(v) for v in anf_iv] for anf_iv in rhs_input_vars]

        if initial_equations:
            if isinstance(initial_equations[0], str):
                for i in range(len(initial_equations)):
                    initial_equations[i] = bpr(initial_equations[i])
            initial_equations = substitute_anf(initial_equations, initial_fixed_vars, bpr)

        if find_redundant_equations is not None:
            if isinstance(find_redundant_equations[0], str):
                for i in range(len(find_redundant_equations)):
                    find_redundant_equations[i] = bpr(find_redundant_equations[i])
            find_redundant_equations = substitute_anf(find_redundant_equations, initial_fixed_vars, bpr)
    else:
        for var, value in initial_fixed_vars.items():
            assert id(bpr) == id(var.parent()) == id(value.parent())
            break
        for anf in lhs_anfs:
            for component in anf:
                assert id(bpr) == id(component.parent())
                break
            break
        for anf in rhs_anfs:
            for component in anf:
                assert id(bpr) == id(component.parent())
                break
            break
        for anf_iv in lhs_input_vars:
            for v in anf_iv:
                assert id(bpr) == id(v.parent())
                break
            break
        for anf_iv in rhs_input_vars:
            for v in anf_iv:
                assert id(bpr) == id(v.parent())
                break
            break
        for eq in initial_equations:
            assert id(bpr) == id(eq.parent())
            break
        if find_redundant_equations is not None:
            for eq in find_redundant_equations:
                assert id(bpr) == id(eq.parent())
                break

    if verbose:
        lla = len(lhs_anfs)
        aux_f = f"{'('.join(['F' + str(lla - i - 1) + (')' if i > 0 else '') for i in range(lla)])}"
        if rhs_degrees:
            smart_print(f"solving the functional equation {aux_f} = degrees({rhs_degrees})")
        else:
            lra = len(rhs_anfs)
            aux_g = f"{'('.join(['G' + str(lra - i - 1) + (')' if i > 0 else '') for i in range(lra)])}"
            smart_print(f"solving the functional equation {aux_f} = {aux_g}")
        for i in reversed(range(len(lhs_anfs))):
            smart_print(f"- F{i}:")
            smart_print(get_anf_coeffmatrix_str(lhs_anfs[i], lhs_input_vars[i]))
        if not rhs_degrees:
            for i in reversed(range(len(rhs_anfs))):
                smart_print(f"- G{i}:")
                smart_print(get_anf_coeffmatrix_str(rhs_anfs[i], rhs_input_vars[i]))
        if not debug:
            smart_print("number of input variables:", num_total_input_vars)
            smart_print("number of symbolic coefficients:", num_total_symbolic_coeffs)
            if initial_fixed_vars:
                smart_print("number of initial fixed vars:", len(initial_fixed_vars))
            if initial_equations:
                smart_print("number of initial equations:", len(initial_equations))
            if find_redundant_equations is not None:
                smart_print("number of candidate redundant equations:", len(find_redundant_equations))
        if debug:
            smart_print(f"input variables ({num_total_input_vars}): {all_varnames[:num_total_input_vars]}")
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
            if find_redundant_equations is not None:
                smart_print(f"initial equations ({len(find_redundant_equations)}):")
                for eq in find_redundant_equations:
                    smart_print("\t" + _sp(eq))
        smart_print("")  # only new line after step

    # 2.1 Compute the concatenation of F and G

    if verbose:
        smart_print(f"{get_time()} | computing F and G")

    lhs_composition_anf = None
    for index_anf, anf in enumerate(lhs_anfs):
        if lhs_composition_anf is None:
            lhs_composition_anf = anf
        else:
            input_vars = lhs_input_vars[index_anf]
            replacement = {v: component for v, component in zip(input_vars, lhs_composition_anf)}
            lhs_composition_anf = substitute_anf(anf, replacement, bpr)
    if not rhs_degrees:
        rhs_composition_anf = None
        for index_anf, anf in enumerate(rhs_anfs):
            if rhs_composition_anf is None:
                rhs_composition_anf = anf
            else:
                input_vars = rhs_input_vars[index_anf]
                replacement = {v: component for v, component in zip(input_vars, rhs_composition_anf)}
                rhs_composition_anf = substitute_anf(anf, replacement, bpr)

    if debug:
        smart_print("- F (after composition):")
        smart_print(get_anf_coeffmatrix_str(lhs_composition_anf, lhs_input_vars[0]))
        if not rhs_degrees:
            smart_print("- G (after composition):")
            smart_print(get_anf_coeffmatrix_str(rhs_composition_anf, rhs_input_vars[0]))
    if verbose:
        smart_print("")

    if rhs_degrees:
        if len(lhs_composition_anf) != len(rhs_degrees):
            raise ValueError("len(lhs_composition_anf) = {} != {} = len(rhs_degrees)".format(
                len(lhs_composition_anf), len(rhs_degrees)
            ))
    else:
        if len(lhs_composition_anf) != len(rhs_composition_anf):
            raise ValueError("len(lhs_composition_anf) = {} != {} = len(rhs_composition_anf)".format(
                len(lhs_composition_anf), len(rhs_composition_anf)
            ))

    # 2.2 Compute the system of equations from F + G = 0

    if verbose:
        smart_print(f"{get_time()} | getting equations from F + G = 0")

    equations = BooleanPolynomialVector(initial_equations)
    index_eq = len(initial_equations)
    for index_component in range(len(lhs_composition_anf)):
        # if verbose:
        #     smart_print(f"{get_time()} | getting symbolic coeffs of {index_component}-th component")

        lhs_component = lhs_composition_anf[index_component]
        if rhs_degrees:
            d = rhs_degrees[index_component]
            mon2coeff = get_all_symbolic_coeff(lhs_component, lhs_input_vars[0], ignore_terms_of_deg_strictly_less=d+1)
            for monomial, coeff in mon2coeff.items():
                assert monomial.degree() > d
                if coeff == 0:
                    continue
                if coeff == 1:
                    raise ValueError("found invalid equation 0 == 1")
                if debug:
                    smart_print(f"\teq[{index_eq}]: ({index_component}-th component) "
                                f"0 == coefficient(monomial={monomial}) = {_sp(coeff)}")
                equations.append(coeff)
                index_eq += 1
        else:
            component = lhs_component + rhs_composition_anf[index_component]
            input_vars = lhs_input_vars[0] + rhs_input_vars[0]
            for monomial, coeff in get_all_symbolic_coeff(component, input_vars).items():
                if coeff == 0:
                    continue
                if coeff == 1:
                    raise ValueError("found invalid equation 0 == 1")
                if debug:
                    smart_print(f"\teq[{index_eq}]: coefficient(monomial={monomial}) = {_sp(coeff)}")
                equations.append(coeff)
                index_eq += 1

    if index_eq == len(initial_equations) and verbose:
        smart_print("no equation added from F + G = 0")

    if return_mode == "raw_equations":
        return equations

    if verbose:
        smart_print("")

    # 3. Reduce and find fixed/free vars

    if verbose:
        aux = ""
        if reduction_mode:
            aux += " and reducing system"
        smart_print(f"{get_time()} | finding fixed and free variables{aux}")

    assert return_mode != "raw_equations"  # no calls to find_fixed_vars() when "raw_equations" mode
    fixed_vars, equations = find_fixed_vars(
        equations, only_linear=only_linear_fixed_vars,
        initial_r_mode=reduction_mode, repeat_with_r_mode=reduction_mode,
        initial_fixed_vars=initial_fixed_vars, bpr=bpr, check=check_find_fixed_vars,
        verbose=verbose, debug=debug, filename=filename)

    eq_vars = set()
    for eq in equations:
        for var in eq.variables():
            eq_vars.add(var)
    eq_vars = set(bpr(var) for var in eq_vars)
    free_vars = []
    for var in bpr.gens()[num_total_input_vars:]:
        if var not in eq_vars and var not in fixed_vars and str(var) not in ignore_varnames:
            free_vars.append(var)
    eq_vars = sorted(eq_vars)

    if verbose:
        fv_str = []
        fv_str_linear = []
        fv_str_ct = []
        for k, v in fixed_vars.items():
            aux_v = str(v) if v not in [0, 1] else v
            fv_str.append((str(k), aux_v))
            if v.degree() <= 1:
                fv_str_linear.append((str(k), aux_v))
            if v in [0, 1]:
                fv_str_ct.append((str(k), aux_v))
        smart_print(f"fixed variables ({len(fv_str)}): {fv_str}")
        if len(fv_str) > len(fv_str_linear) and not only_linear_fixed_vars:
            smart_print(f"(linear) fixed variables ({len(fv_str_linear)}): {fv_str_linear}")
        if 0 < len(fv_str_ct) < len(fv_str):
            smart_print(f"(constant) fixed variables ({len(fv_str_ct)}): {fv_str_ct}")
        smart_print(f"free variables ({len(free_vars)}): {free_vars}")
        smart_print("")

    # if print_common_nonlinear_vars:
    #     raise NotImplementedError("print_common_nonlinear_vars not implemented")

    # 4. SAT solving

    if find_redundant_equations:
        if verbose:
            smart_print("{} | finding redundant equations among {} given equations in:".format(
                get_time(), len(find_redundant_equations)))
            smart_print(f"base system with {len(equations)} and {len(eq_vars)} variables")
            if debug:
                smart_print(f"system variables: {eq_vars}")

        # find_redundant_equations previous parsed to bpr
        find_redundant_equations = substitute_anf(find_redundant_equations, fixed_vars, bpr)

        sat_varnames = [str(var) for var in eq_vars]
        for eq in find_redundant_equations:
            for var in eq.variables():
                varname = str(var)
                if varname not in sat_varnames:
                    sat_varnames.append(varname)

        if verbose and len(eq_vars) < len(sat_varnames):
            aux_vars = sat_varnames[len(eq_vars):]
            smart_print(f"added {len(aux_vars)} variables from redundant equations")
            if verbose:
                smart_print(f"added variables: {aux_vars}")

        sat_bpr = BooleanPolynomialRing(names=sat_varnames)
        sat_base_problem = [sat_bpr(eq) for eq in equations]
        found_red_eqs = []
        for red_eq in find_redundant_equations:
            if red_eq in [0, 1]:
                smart_print(f"ignoring redundant equation 0 == {red_eq}")
                continue
            red_eq = sat_bpr(red_eq)
            smart_print(f"{get_time()} | checking redundant equation {_sp(red_eq)} with SAT solver")
            solutions = solve_sat(sat_base_problem + [red_eq + 1], n=1, s_threads=threads)
            if not solutions:
                found_red_eqs.append(str(red_eq))
                sat_base_problem.append(red_eq)
                smart_print(f"\tredundant equation found, all found up to now: {found_red_eqs}")

        smart_print("redundant equations found ({}/{}): {}".format(
            len(found_red_eqs), len(find_redundant_equations), found_red_eqs))
        found_red_eqs = [bpr(x) for x in found_red_eqs]  # x is str
        found_red_eqs = gauss_on_polys(found_red_eqs)
        smart_print("redundant equations found reduced with gauss ({}):\n{}".format(
            len(found_red_eqs), [str(x) for x in found_red_eqs]))
        return found_red_eqs

    if num_sat_solutions is None:
        num_sat_solutions = sage.all.infinity

    if equations and eq_vars and num_sat_solutions > 0:
        sat_bpr = BooleanPolynomialRing(names=[str(var) for var in eq_vars])
        sat_problem = [sat_bpr(eq) for eq in equations]

        if verbose:
            smart_print(f"{get_time()} | solving {len(sat_problem)} equations with "
                        f"{len(eq_vars)} variables using SAT solver")
            smart_print(f"solver options: num_sat_solutions={num_sat_solutions}, threads={threads}", end="")
            if ignore_varnames:
                smart_print(f", ignore_varnames={ignore_varnames}", end="")
            smart_print()
            if debug:
                smart_print(f"system variables: {eq_vars}")
            if verbose:
                smart_print("")

        target_variables = []
        for v in sat_bpr.gens():
            if str(v) not in ignore_varnames:
                target_variables.append(v)

        sat_solutions = solve_sat(
            sat_problem, n=num_sat_solutions if num_sat_solutions else sage.all.infinity,
            target_variables=sat_bpr.gens(), s_threads=threads,
        )  # cryptominisat default, avoid passing solver objects

        if not sat_solutions:
            raise ValueError("system of equations is inconsistent (unsatisfiable)")
    else:
        assert not equations or num_sat_solutions == 0
        sat_solutions = []

    # 5. Parsing solutions

    if not sat_solutions:
        if equations:
            num_total_solutions = None
        else:
            num_total_solutions = 2 ** len(free_vars)
        if verbose:
            smart_print(f"{get_time()} | ignoring SAT solving step")
            smart_print(f"total number of solutions: {num_total_solutions}")
    else:
        num_total_solutions = 2 ** len(free_vars) * len(sat_solutions)
        if verbose:
            aux = math.log2(num_total_solutions)
            aux = f"2^{{{int(aux)}}}" if aux.is_integer() else f"approx. 2^{{{round(aux, ndigits=2)}}}"
            smart_print(f"{get_time()} | parsing {len(sat_solutions)} SAT solutions found "
                        f"(total number of solutions {num_total_solutions} = {aux})")
        if debug:
            smart_print("{}SAT solutions:".format("First 10 " if len(sat_solutions) > 10 else ""))
            for sat_sol in sat_solutions[:10]:
                smart_print(f"\t{sat_sol}")

        ordered_replacement = []
        var2index_ordered_replacement = {}
        for index_var, var in enumerate(bpr.gens()):
            var2index_ordered_replacement[var] = index_var
            ordered_replacement.append(var)

    bpr_gens_dict = bpr.gens_dict()

    extended_solutions = []  # with the fixed vars substituted (but not the free vars)
    for index_sat_sol in range(len(sat_solutions)):
        # avoid printing
        sat_sol = sat_solutions[index_sat_sol]
        assert len(sat_sol) == len(eq_vars)

        sol_ordered_replacement = ordered_replacement.copy()
        ext_sol = collections.OrderedDict()
        for var, value in sat_sol.items():
            var, value = str2bp(str(var), bpr_gens_dict), str2bp(str(value), bpr_gens_dict)
            ext_sol[var] = value
            sol_ordered_replacement[var2index_ordered_replacement[var]] = value

        for var, value in fixed_vars.items():
            if value not in [0, 1]:
                value = substitute_variables(bpr, sol_ordered_replacement, value)
            ext_sol[var] = value

        # ext_sol = sat_sol.copy()  # copy for fast .subs() below
        #
        # for var, value in fixed_vars.items():
        #     if value not in [0, 1]:
        #         value = value.subs(sat_sol)  # avoid casting to bpr for fast .subs()
        #     ext_sol[var] = value

        extended_solutions.append(ext_sol)

        if num_sols_per_base_sol_to_check:
            for value in ext_sol.values():
                if value not in [0, 1]:
                    assert value == value.subs(ext_sol)
                    assert all(bpr(v) in free_vars for v in value.variables())
            for index_sol in range(min(num_sols_per_base_sol_to_check, 2**len(free_vars))):
                if not free_vars:
                    full_sol = ext_sol
                else:
                    full_sol = ext_sol.copy()
                    free_vars_var2value = {}
                    for var, val in zip(free_vars, int2vector(index_sol, len(free_vars))):
                        free_vars_var2value[var] = val
                    for var, value in full_sol.items():
                        if value not in [0, 1]:
                            full_sol[var] = value.subs(free_vars_var2value)
                    full_sol = {**full_sol, **free_vars_var2value}
                msg = f"Base solution {index_sat_sol + 1} out of {len(sat_solutions)}, " \
                      f"checking full solution {index_sol + 1} out of {num_sols_per_base_sol_to_check}:\n"
                msg += f" - sat solution                          : {sat_sol}\n"
                msg += f" - sat solution + fixed vars             : {ext_sol}\n"
                if free_vars:
                    msg += f" - sat solution + fixed vars + free vars : {full_sol}\n"
                assert all(val in [0, 1] for val in full_sol.values()), msg
                full_sol = {bpr(k): bpr(v) for k, v in full_sol.items()}
                for index_eq, eq in enumerate(initial_equations):
                    if 0 != eq.subs(full_sol):
                        raise ValueError(f"0 != initial_equations[{index_eq}].subs("
                                         f"full_sol={full_sol}) = {eq.subs(full_sol)}")
                aux_lhs_anfs = []
                for anf in lhs_anfs:
                    aux_anf = substitute_anf(anf, full_sol, bpr)
                    # aux_anf = BooleanPolynomialVector()
                    # for component in anf:
                    #     aux_anf.append(bpr(component.subs(full_sol)))
                    aux_lhs_anfs.append(aux_anf)
                aux_lhs_composition_anf = None
                for index_anf, anf in enumerate(aux_lhs_anfs):
                    if aux_lhs_composition_anf is None:
                        aux_lhs_composition_anf = anf
                    else:
                        input_vars = lhs_input_vars[index_anf]
                        replacement = {v: component for v, component in zip(input_vars, aux_lhs_composition_anf)}
                        aux_lhs_composition_anf = substitute_anf(anf, replacement, bpr)
                msg += " - F:\n"
                msg += str(get_anf_coeffmatrix_str(aux_lhs_composition_anf, lhs_input_vars[0])) + "\n"
                if not rhs_degrees:
                    aux_rhs_anfs = []
                    for anf in rhs_anfs:
                        aux_anf = substitute_anf(anf, full_sol, bpr)
                        # aux_anf = BooleanPolynomialVector()
                        # for component in anf:
                        #     aux_anf.append(bpr(component.subs(full_sol)))
                        aux_rhs_anfs.append(aux_anf)
                    aux_rhs_composition_anf = None
                    for index_anf, anf in enumerate(aux_rhs_anfs):
                        if aux_rhs_composition_anf is None:
                            aux_rhs_composition_anf = anf
                        else:
                            input_vars = rhs_input_vars[index_anf]
                            replacement = {v: component for v, component in zip(input_vars, aux_rhs_composition_anf)}
                            aux_rhs_composition_anf = substitute_anf(anf, replacement, bpr)
                    msg += " - G:\n"
                    msg += str(get_anf_coeffmatrix_str(aux_rhs_composition_anf, lhs_input_vars[0])) + "\n"
                for ic in range(len(aux_lhs_composition_anf)):
                    if rhs_degrees:
                        d = get_symbolic_alg_deg(aux_lhs_composition_anf[ic], lhs_input_vars[0])
                        if d != rhs_degrees[ic]:
                            raise ValueError(f"degree(F[{ic}]) = {d} != {rhs_degrees[ic]} = degree(G[{ic}])\n{msg}")
                    else:
                        component = aux_lhs_composition_anf[ic] + aux_rhs_composition_anf[ic]
                        if component != 0:
                            raise ValueError(f"0 != F[{ic}] + G[{ic}] = {component}\n{msg}")
                if debug and index_sat_sol <= 2 and index_sol <= 2:
                    smart_print(msg[:-1])  # without the last \n

    if verbose:
        smart_print("")

    # 6. Finding linear combinations

    if len(sat_solutions) < num_sat_solutions:
        find_linear_combinations_in_solutions = True

    linear_combinations = []
    if sat_solutions and find_linear_combinations_in_solutions:
        if verbose:
            smart_print(f"{get_time()} | finding linear combinations of variables among the SAT solutions")

        # each "column" of sat_solutions.values() contains the values each var takes for each sol
        # we need each column as a set of vectors to call V.linear_dependence(vectors)
        vectors = list(zip(*(sat_sol.values() for sat_sol in sat_solutions)))  # transpose
        # before that we need to sort vectors s.t. smallest var is the last vector
        vars_in_vectors = [(var, i) for i, var in enumerate(sat_solutions[0].keys())]
        vars_in_vectors = list(reversed(sorted(vars_in_vectors)))
        assert len(vectors) == len(vars_in_vectors)
        aux = []
        for _, i in vars_in_vectors:
            aux.append(vectors[i])
        vectors = aux
        vars_in_vectors = [var for var, _ in vars_in_vectors]
        # to detect linear combinations equal to 1 (instead of 0) we add 1 to the end
        vectors.append([1 for _ in range(len(vectors[0]))])
        vars_in_vectors.append(sat_bpr(1))

        vs = sage.all.VectorSpace(sage.all.GF(2), len(vars_in_vectors))
        linear_combinations_matrix = sage.all.matrix(sat_bpr, vs.linear_dependence(vectors, check=False))
        if linear_combinations_matrix.nrows() > 0:
            linear_combinations = linear_combinations_matrix * sage.all.vector(vars_in_vectors)
        if verbose:
            smart_print(f"linear combinations ({len(linear_combinations)}): "
                        f"{[str(lc) for lc in linear_combinations]}")
        if debug and linear_combinations:
            aux_matrix = sage.all.matrix(
                nrows=linear_combinations_matrix.nrows()+1, ncols=linear_combinations_matrix.ncols(),
                entries=vars_in_vectors + linear_combinations_matrix.list()
            )
            aux_matrix.subdivide(row_lines=1)
            smart_print(f"linear combinations (matrix form)\n{aux_matrix}")
        if verbose:
            smart_print("")

    if return_mode == "lincomb_solutions":
        return [bpr(lc) for lc in linear_combinations]

    # 7. Reducing system if linear combinations are found

    if linear_combinations:
        if verbose:
            smart_print(f"{get_time()} | reducing system with the linear combinations obtained")

        for lc in linear_combinations:
            equations.append(bpr(lc))

        new_fixed_vars, new_equations = find_fixed_vars(
            equations, only_linear=only_linear_fixed_vars,
            initial_r_mode=reduction_mode, repeat_with_r_mode=reduction_mode,
            initial_fixed_vars=None, bpr=bpr, check=check_find_fixed_vars,
            verbose=verbose, debug=debug, filename=filename)

        # TODO: v2 replace .subs()
        fixed_vars_modified = len(new_fixed_vars) > 0
        for var, expr in fixed_vars.items():
            new_expr = bpr(expr.subs(new_fixed_vars))
            if expr != new_expr:
                fixed_vars[var] = new_expr
                fixed_vars_modified = True
        for var, expr in new_fixed_vars.items():
            assert var not in fixed_vars
            fixed_vars[var] = expr

        new_eq_vars = set()
        for eq in new_equations:
            for var in eq.variables():
                new_eq_vars.add(var)
        new_eq_vars = set(bpr(var) for var in new_eq_vars)
        new_free_vars = []
        for var in bpr.gens()[num_total_input_vars:]:
            if var not in new_eq_vars and var not in fixed_vars and var not in new_fixed_vars:
                new_free_vars.append(var)
        new_eq_vars = sorted(new_eq_vars)

        if verbose:
            if fixed_vars_modified:
                fv_str = []
                fv_str_linear = []
                fv_str_ct = []
                for k, v in fixed_vars.items():
                    aux_v = str(v) if v not in [0, 1] else v
                    fv_str.append((str(k), aux_v))
                    if v.degree() <= 1:
                        fv_str_linear.append((str(k), aux_v))
                    if v in [0, 1]:
                        fv_str_ct.append((str(k), aux_v))
                smart_print(f"fixed variables ({len(fv_str)}): {fv_str}")
                if len(fv_str) > len(fv_str_linear) and not only_linear_fixed_vars:
                    smart_print(f"(linear) fixed variables ({len(fv_str_linear)}): {fv_str_linear}")
                if 0 < len(fv_str_ct) < len(fv_str):
                    smart_print(f"(constant) fixed variables ({len(fv_str_ct)}): {fv_str_ct}")
            if free_vars != new_free_vars:
                smart_print(f"free variables ({len(new_free_vars)}): {new_free_vars}")
                if 2 ** (len(new_free_vars)) != num_total_solutions:
                    smart_print(f"2^{{number_free_vars={len(new_free_vars)}}} != "
                                f"{math.log2(num_total_solutions)} = number_solutions")
            if eq_vars != new_eq_vars:
                smart_print(f"number of system variables changed to {len(new_eq_vars)}")
                if debug:
                    smart_print(f"system variables ({len(new_eq_vars)}): {new_eq_vars}")
            if new_fixed_vars:
                smart_print(f"number of equations changed to {len(new_equations)}")
                if debug:
                    for index_eq, eq in enumerate(new_equations):
                        smart_print(f"\teq[{index_eq}] = {_sp(eq)}")
            smart_print("")

        # if print_common_nonlinear_vars:
        #     raise NotImplementedError("print_common_nonlinear_vars not implemented")

        equations = new_equations
        free_vars = new_free_vars
        eq_vars = new_eq_vars

    # 8. Returning solutions

    if verbose:
        smart_print(f"{get_time()} | returning outputs with mode='{return_mode}'")

    if return_mode == "list_coeffs":
        if return_total_num_solutions:
            return extended_solutions, free_vars, num_total_solutions
        else:
            return extended_solutions, free_vars

    if return_mode == "list_anfs":
        if len(extended_solutions) == 0:
            extended_solutions.append(fixed_vars)  # SAT solver was not called
        if free_vars:
            smart_print(f"setting to 0 the free variables {free_vars}")
            free_vars_var2value = {}
            for v in free_vars:
                free_vars_var2value[v] = bpr(0)
        list_anfs = []
        input_var_bpr = BooleanPolynomialRing(num_total_input_vars, all_varnames[:num_total_input_vars])
        for extended_sol in extended_solutions:
            extended_sol = {bpr(k): bpr(v) for k, v in extended_sol.items()}
            if free_vars:
                for k, v in extended_sol.items():
                    if v not in [0, 1]:
                        extended_sol[k] = bpr(v.subs(free_vars_var2value))
                extended_sol = {**extended_sol, **free_vars_var2value}
            aux_lhs_anfs = []
            for anf in lhs_anfs:
                anf = substitute_anf(anf, extended_sol, bpr)
                aux_anf = BooleanPolynomialVector()
                for component in anf:
                    aux_anf.append(input_var_bpr(component))
                # aux_anf = BooleanPolynomialVector()
                # for component in anf:
                #     aux_anf.append(input_var_bpr(bpr(component.subs(extended_sol))))
                aux_lhs_anfs.append(aux_anf)
            if rhs_degrees:
                list_anfs.append([aux_lhs_anfs])
            else:
                aux_rhs_anfs = []
                for anf in rhs_anfs:
                    anf = substitute_anf(anf, extended_sol, bpr)
                    aux_anf = BooleanPolynomialVector()
                    for component in anf:
                        aux_anf.append(input_var_bpr(component))
                    # aux_anf = BooleanPolynomialVector()
                    # for component in anf:
                    #     aux_anf.append(input_var_bpr(bpr(component.subs(extended_sol))))
                    aux_rhs_anfs.append(aux_anf)
                list_anfs.append([aux_lhs_anfs, aux_rhs_anfs])
        if return_total_num_solutions:
            return list_anfs, num_total_solutions
        else:
            return list_anfs

    if return_mode == "symbolic_anf":
        aux_lhs_anfs = []
        for anf in lhs_anfs:
            aux_anf = substitute_anf(anf, fixed_vars, bpr)
            # aux_anf = BooleanPolynomialVector()
            # for component in anf:
            #     aux_anf.append(bpr(component.subs(fixed_vars)))
            aux_lhs_anfs.append(aux_anf)
        if rhs_degrees:
            symbolic_anf = [aux_lhs_anfs]
        else:
            aux_rhs_anfs = []
            for anf in rhs_anfs:
                aux_anf = substitute_anf(anf, fixed_vars, bpr)
                # aux_anf = BooleanPolynomialVector()
                # for component in anf:
                #     aux_anf.append(bpr(component.subs(fixed_vars)))
                aux_rhs_anfs.append(aux_anf)
            symbolic_anf = [aux_lhs_anfs, aux_rhs_anfs]
        if return_total_num_solutions:
            return symbolic_anf, equations, num_total_solutions
        else:
            return symbolic_anf, equations

    if return_mode == "symbolic_coeffs":
        if return_total_num_solutions:
            return fixed_vars, equations, num_total_solutions
        else:
            return fixed_vars, equations


def find_inverse(
    anf, inv_degree, inv_position="left", input_vars=None, prefix_inv_coeffs="a",
    verbose=False, debug=False, filename=None, **solve_args
):
    """Find the inverse of an ANF by calling solve_functional_equation().

    Given a function F, find A s.t. A(F) = Identity if inv_position="left".
    If inv_position="right",  find A' s.t. F(A) = Identity.
    If no inverse is found, None returned.

    input_vars is a list of the inputs vars (containing Boolean variables
    or strings) of the given anf (not needed for non-symbolic anf).

    Named arguments from **solve_args are passed to solve_functional_equation().
    By default, return_mode="list_anfs" and num_sat_solutions="1".
    If there two parameters are not given, only one solution is found
    and the ANF of the inverse is returned.

        >>> sage.all.set_random_seed(0)
        >>> from boolcrypt.utilities import lut2anf, matrix2anf, compose_anf_fast
        >>> anf = lut2anf((0, 1, 2, 3, 4, 6, 7, 5))
        >>> inv_anf = find_inverse(anf, 2)
        >>> get_anf_coeffmatrix_str(inv_anf, input_vars=["x0", "x1", "x2"])
        [x0*x2 x1*x2|   x0    x1    x2]
        [-----------+-----------------]
        [    0     1|    1     0     0]
        [    1     1|    0     1     0]
        [    0     0|    0     0     1]
        >>> get_anf_coeffmatrix_str(compose_anf_fast(inv_anf, anf), input_vars=["x0", "x1", "x2"])
        [x0 x1 x2]
        [--------]
        [ 1  0  0]
        [ 0  1  0]
        [ 0  0  1]
        >>> matrix = sage.all.matrix(GF(2), 2, 3, [[1, 1, 0], [1, 1, 1]])
        >>> anf = matrix2anf(matrix)
        >>> result = find_inverse(anf, 1, inv_position="right", return_mode="symbolic_anf", num_sat_solutions=None)
        >>> get_anf_coeffmatrix_str(result[0][0][0], input_vars=["x0", "x1", "x2"])
        [      x0       x1       x2|       1]
        [--------------------------+--------]
        [a1_0 + 1     a1_1     a1_2|      a1]
        [    a1_0     a1_1     a1_2|      a1]
        [       1        1        0|       0]
        >>> list(result[1])  # equations
        []
        >>> matrix * anf2matrix(result[0][0][0], input_vars=["x0", "x1", "x2"])
        [1 0 0]
        [0 1 0]

    """
    assert inv_position in ["left", "right"]
    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    if solve_args.get("bpr", None) is not None:
        assert solve_args.get("ignore_initial_parsing", False) is not True

    # bpr = solve_args.get("bpr", None)
    # initial_fixed_vars = solve_args.get("initial_fixed_vars", {})
    # initial_fixed_vars = collections.OrderedDict(
    #     [(k, v) for k, v in initial_fixed_vars.items() if str(k).startswith(prefix_inv_coeffs)])

    if input_vars is None:
        aux_bpr = anf[0].parent()
        assert all(aux_bpr == f.parent() for f in anf)
        input_vars = list(aux_bpr.gens())

    assert all(not str(v).startswith(prefix_inv_coeffs) for v in input_vars)
    assert not prefix_inv_coeffs.startswith("x")

    if inv_position == "left":
        f1 = get_symbolic_anf(inv_degree, len(anf), len(anf),
                              prefix_inputs="x", prefix_coeffs=prefix_inv_coeffs)
                              # bpr=bpr, coeff2expr=initial_fixed_vars)
        f0 = anf
        f1_input_vars = ["x" + str(i) for i in range(len(anf))]
        f0_input_vars = input_vars
    else:
        f1 = anf
        f0 = get_symbolic_anf(inv_degree, len(input_vars), len(input_vars),
                              prefix_inputs="x", prefix_coeffs=prefix_inv_coeffs)
                              # bpr=bpr, coeff2expr=initial_fixed_vars)
        f1_input_vars = input_vars
        f0_input_vars = ["x" + str(i) for i in range(len(input_vars))]

    # if bpr is not None:
    #     f0_input_vars = [bpr(v) for v in f0_input_vars]
    #     f1_input_vars = [bpr(v) for v in f1_input_vars]

    lhs_anfs = [f0, f1]
    lhs_input_vars = [f0_input_vars, f1_input_vars]

    g_bpr = BooleanPolynomialRing(len(f1_input_vars), 'x')
    assert len(g_bpr.gens()) >= len(f1)
    g0 = g_bpr.gens()[:len(f1)]
    g0_input_vars = g_bpr.gens()
    # if bpr is not None:
    #     g0 = [bpr(component) for component in g0]
    #     g0_input_vars = [bpr(v) for v in g0_input_vars]
    rhs_anfs = [g0]
    rhs_input_vars = [g0_input_vars]

    new_kwargs = solve_args.copy()
    if "num_sat_solutions" not in new_kwargs:
        new_kwargs["num_sat_solutions"] = 1
    if "return_mode" not in new_kwargs:
        new_kwargs["return_mode"] = "list_anfs"

    try:
        result = solve_functional_equation(
            lhs_anfs, rhs_anfs, lhs_input_vars, rhs_input_vars,
            verbose=verbose, debug=debug, filename=filename, **new_kwargs
        )
    except ValueError as e:
        get_smart_print(filename)(f"No solution found ({e})")
        return None
    else:
        if "return_mode" not in solve_args and "num_sat_solutions" not in solve_args:
            if solve_args.get("return_total_num_solutions", False):
                get_smart_print(filename)("ignoring return_total_num_solutions")
            if inv_position == "left":
                return result[0][0][1]  # return f1
            else:
                return result[0][0][0]  # return f0
        else:
            return result


# TODO: add to docstring add_invertibility_equations (needed if left or right are NOT permutations)
def find_equivalence(
    left_anf, right_anf, left_equiv_degree=1, right_equiv_degree=1,
    equiv_ct_terms=True, left_input_vars=None, right_input_vars=None,
    prefix_left_equiv_coeffs="b", prefix_right_equiv_coeffs="a",
    add_invertibility_equations=False,
    verbose=False, debug=False, filename=None, **solve_args
):
    """Find a pair of functions (A, B) such that B F A = G.

    Given the left function F and the right function G,
    this method finds a pair of functions (A, B) of given degrees
    such that B F A = G. If no solution is found, None is returned.

    If given degrees are 1 and equiv_ct_terms=True (resp. False),
    this methods finds whether F and G are affine (resp. linear) equivalent.

    If F and G are the same, this methods finds self-equivalences.

    The pair (A, B) is found by solving the functional equation B F A = G.

    left_input_vars and right_input_vars are two lists with the inputs vars
    (containing Boolean variables or strings) of the given F and G
    (not needed for non-symbolic anfs).

    Named arguments from **solve_args are passed to solve_functional_equation().
    By default, return_mode="list_anfs" and num_sat_solutions="1".
    If there two parameters are not given, only one solution is found
    and a pair containing the ANF of A and B is returned.

        >>> from boolcrypt.utilities import lut2anf, get_lut_inversion
        >>> from boolcrypt.equivalence import get_linear_repr
        >>> from boolcrypt.equivalence import check_self_le_anf
        >>> left_anf = lut2anf([0, 1, 2, 3, 4, 6, 7, 5])
        >>> right_anf = lut2anf(get_linear_repr([0, 1, 2, 3, 4, 6, 7, 5]))
        >>> right_lin, left_lin = find_equivalence(left_anf, right_anf, equiv_ct_terms=False)  # linear
        >>> get_anf_coeffmatrix_str(right_lin, input_vars=["x0", "x1", "x2"])
        [x0 x1 x2]
        [--------]
        [ 0  1  0]
        [ 1  1  1]
        [ 0  0  1]
        >>> right_anf = lut2anf([x.__xor__(1) for x in [0, 1, 2, 3, 4, 6, 7, 5]])
        >>> find_equivalence(left_anf, right_anf, equiv_ct_terms=False)
        No solution found (found invalid equation 0 == 1)
        >>> right_aff, left_aff = find_equivalence(left_anf, right_anf, equiv_ct_terms=True)  # affine
        >>> get_anf_coeffmatrix_str(right_aff, input_vars=["x0", "x1", "x2"])
        [x0 x1 x2| 1]
        [--------+--]
        [ 0  1  0| 1]
        [ 1  0  0| 0]
        [ 0  0  1| 1]
        >>> find_equivalence(left_anf, lut2anf(get_lut_inversion(3)))
        No solution found (system of equations is inconsistent (unsatisfiable))
        >>> right_se, left_se = find_equivalence(left_anf, left_anf, 1, 1, equiv_ct_terms=False)  # linear SE
        >>> assert check_self_le_anf(left_anf, right_se, left_se, None)
        >>> right_se, left_se = find_equivalence(left_anf, left_anf, 2, 2, equiv_ct_terms=False)  # non-linear SE
        >>> assert check_self_le_anf(left_anf, right_se, left_se, None)
        >>> get_anf_coeffmatrix_str(right_se, input_vars=["x0", "x1", "x2"])
        [x0*x2 x1*x2|   x0    x1    x2]
        [-----------+-----------------]
        [    1     1|    0     1     1]
        [    0     1|    1     0     1]
        [    1     0|    1     1     1]

    """
    assert not isinstance(left_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    assert not isinstance(right_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    assert add_invertibility_equations in [False, "right", "left", "both"]

    if solve_args.get("bpr", None) is not None:
        assert solve_args.get("ignore_initial_parsing", False) is not True

    # bpr = solve_args.get("bpr", None)
    # initial_fixed_vars = solve_args.get("initial_fixed_vars", {})
    # initial_fixed_vars = collections.OrderedDict(
    #     [(k, v) for k, v in initial_fixed_vars.items() if str(k).startswith(prefix_left_equiv_coeffs) or
    #      str(k).startswith(prefix_right_equiv_coeffs)])

    if left_input_vars is None:
        aux_bpr = left_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in left_anf)
        left_input_vars = aux_bpr.gens()
    if right_input_vars is None:
        aux_bpr = right_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in right_anf)
        right_input_vars = aux_bpr.gens()

    for v in itertools.chain(left_input_vars, right_input_vars):
        assert not str(v).startswith(prefix_left_equiv_coeffs)
        assert not str(v).startswith(prefix_right_equiv_coeffs)
    assert not prefix_left_equiv_coeffs.startswith("x")
    assert not prefix_right_equiv_coeffs.startswith("x")

    f2 = get_symbolic_anf(left_equiv_degree, len(left_anf), len(right_anf), ct_terms=equiv_ct_terms,
                          prefix_inputs="x", prefix_coeffs=prefix_left_equiv_coeffs)
                          # bpr=bpr, coeff2expr=initial_fixed_vars)
    f1 = left_anf
    f0 = get_symbolic_anf(right_equiv_degree, len(right_input_vars), len(left_input_vars), ct_terms=equiv_ct_terms,
                          prefix_inputs="x", prefix_coeffs=prefix_right_equiv_coeffs)
                          # bpr=bpr, coeff2expr=initial_fixed_vars)
    f2_input_vars = ["x" + str(i) for i in range(len(left_anf))]
    f1_input_vars = left_input_vars
    f0_input_vars = ["x" + str(i) for i in range(len(right_input_vars))]

    # if bpr is not None:
    #     f2_input_vars = [bpr(v) for v in f2_input_vars]
    #     f0_input_vars = [bpr(v) for v in f0_input_vars]

    g0 = right_anf
    g0_input_vars = right_input_vars

    lhs_anfs = [f0, f1, f2]
    lhs_input_vars = [f0_input_vars, f1_input_vars, f2_input_vars]

    rhs_anfs = [g0]
    rhs_input_vars = [g0_input_vars]

    initial_equations = []
    if add_invertibility_equations in ["right", "both"]:
        aux_bpr = f0[0].parent()
        aux_iv = [aux_bpr(v) for v in f0_input_vars]
        initial_equations.append(aux_bpr(anf2matrix(f0, aux_iv).determinant()) + aux_bpr(1))
    if add_invertibility_equations in ["left", "both"]:
        aux_bpr = f2[0].parent()
        aux_iv = [aux_bpr(v) for v in f2_input_vars]
        initial_equations.append(aux_bpr(anf2matrix(f2, aux_iv).determinant()) + aux_bpr(1))

    new_kwargs = solve_args.copy()
    if "num_sat_solutions" not in new_kwargs:
        new_kwargs["num_sat_solutions"] = 1
    if "return_mode" not in new_kwargs:
        new_kwargs["return_mode"] = "list_anfs"
    if "initial_equations" in new_kwargs:
        new_kwargs["initial_equations"].extend(initial_equations)
    else:
        new_kwargs["initial_equations"] = initial_equations

    try:
        result = solve_functional_equation(
            lhs_anfs, rhs_anfs, lhs_input_vars, rhs_input_vars,
            verbose=verbose, debug=debug, filename=filename, **new_kwargs
        )
    except ValueError as e:
        get_smart_print(filename)(f"No solution found ({e})")
        return None
    else:
        if "return_mode" not in solve_args and "num_sat_solutions" not in solve_args:
            if solve_args.get("return_total_num_solutions", False):
                get_smart_print(filename)("ignoring return_total_num_solutions")
            return result[0][0][0], result[0][0][2]  # return f0, f2
        else:
            return result


# TODO: add to docstring add_invertibility_equations
def find_half_affine_equivalence(
    left_anf, inv_right_anf, left_input_vars=None, inv_right_input_vars=None,
    prefix_equiv_coeffs="a", add_invertibility_equations=True,
    verbose=False, debug=False, filename=None, **solve_args
):
    """Find an affine permutation A such that F A G^{-1} is affine.

    Given the left permutation F and the right permutation G^{-1},
    this method finds an affine permutation A such that F A G^{-1} is affine
    Note that this is equivalent to the existence of B such that B F A = G.
    In particular, if F = G, A is a right affine self-equivalence of F.
    If no solution is found, None is returned.

    left_input_vars and inv_right_input_vars are 2 lists of the inputs vars
    (containing Boolean variables or strings) of the given F and G^{-1}
    (not needed for non-symbolic anfs).

    Named arguments from **solve_args are passed to solve_functional_equation().

    Named arguments from **solve_args are passed to solve_functional_equation().
    By default, return_mode="list_anfs" and num_sat_solutions="1".
    If there two parameters are not given, only one solution is found
    and the ANF of A is returned.

        >>> sage.all.set_random_seed(0)
        >>> from boolcrypt.utilities import lut2anf, invert_lut
        >>> from boolcrypt.equivalence import check_self_ae_anf
        >>> anf = lut2anf((0, 1, 2, 3, 4, 6, 7, 5))
        >>> inv_anf = lut2anf(invert_lut([x.__xor__(1) for x in [0, 1, 2, 3, 4, 6, 7, 5]]))
        >>> right_se = find_half_affine_equivalence(anf, inv_anf)
        setting to 0 the free variables [a0_2, a0, a1_2, a1, a2]
        >>> get_anf_coeffmatrix_str(right_se, input_vars=["x0", "x1", "x2"])
        [x0 x1 x2]
        [--------]
        [ 1  1  0]
        [ 1  0  0]
        [ 0  0  1]
        >>> inv_anf = lut2anf(invert_lut((0, 1, 2, 3, 4, 6, 7, 5)))
        >>> right_se = find_half_affine_equivalence(anf, inv_anf)
        setting to 0 the free variables [a0_2, a0, a1_2, a1, a2]
        >>> assert check_self_ae_anf(anf, right_se, None, inv_anf)
        >>> get_anf_coeffmatrix_str(right_se, input_vars=["x0", "x1", "x2"])
        [x0 x1 x2]
        [--------]
        [ 1  1  0]
        [ 1  0  0]
        [ 0  0  1]

    """
    assert not isinstance(left_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    assert not isinstance(inv_right_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    if solve_args.get("bpr", None) is not None:
        assert solve_args.get("ignore_initial_parsing", False) is not True

    if left_input_vars is None:
        aux_bpr = left_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in left_anf)
        left_input_vars = aux_bpr.gens()
    if inv_right_input_vars is None:
        aux_bpr = inv_right_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in inv_right_anf)
        inv_right_input_vars = aux_bpr.gens()

    for v in left_input_vars + inv_right_input_vars:
        assert not str(v).startswith(prefix_equiv_coeffs)
    assert not prefix_equiv_coeffs.startswith("x")
    assert len(left_anf) == len(left_input_vars) == len(inv_right_anf) == len(inv_right_input_vars)

    n = len(left_anf)  # n = num inputs = num outputs

    f2 = left_anf
    f1 = get_symbolic_anf(1, n, n, ct_terms=True, prefix_inputs="x",
                          prefix_coeffs=prefix_equiv_coeffs)
    f0 = inv_right_anf

    f1_input_vars = ["x" + str(i) for i in range(n)]

    lhs_anfs = [f0, f1, f2]
    lhs_input_vars = [inv_right_input_vars, f1_input_vars, left_input_vars]

    rhs_degrees = [1 for _ in range(n)]
    rhs_input_vars = None

    if add_invertibility_equations:
        aux_bpr = f1[0].parent()
        aux_iv = [aux_bpr(v) for v in f1_input_vars]
        initial_equations = [aux_bpr(anf2matrix(f1, aux_iv).determinant()) + aux_bpr(1)]
    else:
        initial_equations = []

    new_kwargs = solve_args.copy()
    if "num_sat_solutions" not in new_kwargs:
        new_kwargs["num_sat_solutions"] = 1
    if "return_mode" not in new_kwargs:
        new_kwargs["return_mode"] = "list_anfs"
    if "initial_equations" in new_kwargs:
        new_kwargs["initial_equations"].extend(initial_equations)
    else:
        new_kwargs["initial_equations"] = initial_equations

    try:
        result = solve_functional_equation(
            lhs_anfs, rhs_degrees, lhs_input_vars, rhs_input_vars,
            verbose=verbose, debug=debug, filename=filename, **new_kwargs
        )
    except ValueError as e:
        get_smart_print(filename)(f"No solution found ({e})")
        return None
    else:
        if "return_mode" not in solve_args and "num_sat_solutions" not in solve_args:
            if solve_args.get("return_total_num_solutions", False):
                get_smart_print(filename)("ignoring return_total_num_solutions")
            return result[0][0][1]  # return f1
        else:
            return result


def find_nondiagonal_ase(
    left_anf, right_anf, se_ct_terms=True, left_input_vars=None, right_input_vars=None,
    prefix_se_left_coeffs="b", prefix_se_right_coeffs="a",
    verbose=False, debug=False, filename=None, **solve_args
):
    """Find an affine non-diagonal self-equivalence of F || G.

    Given the function F by left_anf and G by right_anf,
    finds an affine self-equivalence (A, B) of the concatenation F || G,
    where A is non-diagonal (A in matrix form is not a block
    diagonal matrix up to block row permutations).
    If no solution is found, None is returned.

    If se_ct_terms=False, the constant terms of A and B are set to zero.

    left_input_vars and right_input_vars are two lists containing the
    inputs vars (Boolean variables or strings) of the given
    left and right anfs (not needed for non-symbolic anfs).

    Named arguments from **solve_args are passed to solve_functional_equation().
    By default, return_mode="list_anfs" and num_sat_solutions="1".
    If there two parameters are not given, only one solution is found
    and a pair with the ANF of A and B is returned.

        >>> sage.all.set_random_seed(0)
        >>> from boolcrypt.utilities import lut2anf, invert_lut, get_lut_inversion
        >>> from boolcrypt.equivalence import check_self_le_anf
        >>> left_anf = lut2anf([0, 1, 2, 3, 4, 5, 7, 6])
        >>> right_anf = left_anf
        >>> right_se, left_se = find_nondiagonal_ase(left_anf, right_anf, se_ct_terms=False)
        >>> concat_anf = concatenate_anf(left_anf, right_anf)
        >>> assert check_self_le_anf(concat_anf, right_se, left_se, None)
        >>> get_anf_coeffmatrix_str(right_se, input_vars=["x" + str(i) for i in range(6)])
        [x0 x1 x2 x3 x4 x5]
        [-----------------]
        [ 1  0  0  0  1  1]
        [ 0  0  1  0  0  0]
        [ 0  1  1  0  0  0]
        [ 0  0  0  1  1  0]
        [ 0  0  0  0  0  1]
        [ 0  0  0  0  1  1]
        >>> left_anf = lut2anf(get_lut_inversion(3))
        >>> right_anf = left_anf
        >>> find_nondiagonal_ase(left_anf, right_anf, se_ct_terms=False)  # doctest:+SKIP
        No solution found (system of equations is inconsistent (unsatisfiable))

    """
    assert not isinstance(left_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    assert not isinstance(right_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    if solve_args.get("bpr", None) is not None:
        assert solve_args.get("ignore_initial_parsing", False) is not True

    if left_input_vars is None:
        aux_bpr = left_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in left_anf)
        left_input_vars = aux_bpr.gens()
    if right_input_vars is None:
        aux_bpr = right_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in right_anf)
        right_input_vars = aux_bpr.gens()

    assert all(not str(v).startswith(prefix_se_left_coeffs) for v in left_input_vars + right_input_vars)
    assert all(not str(v).startswith(prefix_se_right_coeffs) for v in left_input_vars + right_input_vars)
    assert not prefix_se_left_coeffs.startswith("x")
    assert not prefix_se_right_coeffs.startswith("x")

    anf = concatenate_anf(left_anf, right_anf, prefix="x",
                          input_vars_left=left_input_vars, input_vars_right=right_input_vars)
    input_anf_vars = ["x" + str(i) for i in range(len(left_input_vars) + len(right_input_vars))]

    f0 = get_symbolic_anf(1, len(input_anf_vars), len(input_anf_vars), ct_terms=se_ct_terms,
                          prefix_inputs="x", prefix_coeffs=prefix_se_right_coeffs)
    f0_input_vars = ["x" + str(i) for i in range(len(input_anf_vars))]

    # initial equations
    aux_bpr = f0[0].parent()
    aux_iv = [aux_bpr(v) for v in f0_input_vars]
    right_matrix = anf2matrix(f0, aux_iv)
    right_matrix.subdivide(len(left_input_vars), len(left_input_vars))
    if len(left_input_vars) <= len(right_input_vars):
        left_block = right_matrix.subdivision(0, 0).list()
        right_block = right_matrix.subdivision(0, 1).list()
    else:
        left_block = right_matrix.subdivision(1, 0).list()
        right_block = right_matrix.subdivision(1, 1).list()
    def or_bits(a, b):
        return a + b + (a * b)
    # boolean_poly == 1 works, but 1 in boolean_poly.coefficients() not
    if 1 in left_block or aux_bpr(1) in left_block:
        eq1 = aux_bpr(0)
    else:
        eq1 = aux_bpr(sage.all.reduce(or_bits, left_block)) + aux_bpr(1)
    if 1 in right_block or aux_bpr(1) in right_block:
        eq2 = aux_bpr(0)
    else:
        eq2 = aux_bpr(sage.all.reduce(or_bits, right_block)) + aux_bpr(1)
    initial_equations = [eq1, eq2]

    return find_equivalence(
        anf, anf, left_equiv_degree=1, right_equiv_degree=1, equiv_ct_terms=se_ct_terms,
        left_input_vars=input_anf_vars, right_input_vars=input_anf_vars,
        prefix_left_equiv_coeffs=prefix_se_left_coeffs,
        prefix_right_equiv_coeffs=prefix_se_right_coeffs,
        verbose=verbose, debug=debug, filename=filename,
        initial_equations=initial_equations, **solve_args
    )


def find_noninvertible_ase(
    anf, se_ct_terms=True, input_anf_vars=None,
    prefix_left_se_coeffs="b", prefix_right_se_coeffs="a",
    verbose=False, debug=False, filename=None, **solve_args
):
    """Find a non-invertible pair (A, B) such that F A = B F.

    An affine non-invertible self-equivalence of F is a pair of
    non-invertible affine functions (A, B) such that B F = F A.
    A is also called a right SE and B a left SE.
    If no solution is found, None is returned.

    If se_ct_terms=False, the constant terms of A and B are set to zero.

    input_anf_vars is a list of the inputs vars (containing Boolean variables
    or strings) of the given anf (not needed for non-symbolic anfs).

    Named arguments from **solve_args are passed to solve_functional_equation().
    By default, return_mode="list_anfs" and num_sat_solutions="1".
    If there two parameters are not given, only one solution is found
    and a pair containing the ANF of A and B is returned.

        >>> from boolcrypt.utilities import lut2anf, get_lut_inversion
        >>> anf = lut2anf([0, 1, 2, 3, 4, 5, 7, 6])
        >>> right_se, left_se = find_noninvertible_ase(anf)
        setting to 0 the free variables [b0, b1, b2]
        >>> get_anf_coeffmatrix_str(right_se, input_vars=["x0", "x1", "x2"])
        [x1]
        [--]
        [ 0]
        [ 0]
        [ 1]
        >>> get_anf_coeffmatrix_str(left_se, input_vars=["x0", "x1", "x2"])
        [x1]
        [--]
        [ 0]
        [ 0]
        [ 1]
        >>> find_noninvertible_ase(lut2anf(get_lut_inversion(3)))
        No solution found (system of equations is inconsistent (unsatisfiable))

    """
    assert not isinstance(anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    if solve_args.get("bpr", None) is not None:
        assert solve_args.get("ignore_initial_parsing", False) is not True

    if input_anf_vars is None:
        aux_bpr = anf[0].parent()
        assert all(aux_bpr == f.parent() for f in anf)
        input_anf_vars = aux_bpr.gens()

    assert all(not str(v).startswith(prefix_right_se_coeffs) for v in input_anf_vars)
    assert all(not str(v).startswith(prefix_left_se_coeffs) for v in input_anf_vars)
    assert not prefix_right_se_coeffs.startswith("x")
    assert not prefix_left_se_coeffs.startswith("x")

    num_inputs, num_outputs = len(input_anf_vars), len(anf)

    f1 = anf
    f0 = get_symbolic_anf(1, num_inputs, num_inputs, ct_terms=se_ct_terms,
                          prefix_inputs="x", prefix_coeffs=prefix_right_se_coeffs)
    g1 = get_symbolic_anf(1, num_outputs, num_outputs, ct_terms=se_ct_terms,
                          prefix_inputs="x", prefix_coeffs=prefix_left_se_coeffs)
    g0 = anf
    f1_input_vars, g0_input_vars = input_anf_vars, input_anf_vars
    f0_input_vars = ["x" + str(i) for i in range(num_inputs)]
    g1_input_vars = ["x" + str(i) for i in range(num_outputs)]

    lhs_anfs = [f0, f1]
    lhs_input_vars = [f0_input_vars, f1_input_vars]
    rhs_anfs = [g0, g1]
    rhs_input_vars = [g0_input_vars, g1_input_vars]

    new_kwargs = solve_args.copy()
    if "num_sat_solutions" not in new_kwargs:
        new_kwargs["num_sat_solutions"] = 1
    if "return_mode" not in new_kwargs:
        new_kwargs["return_mode"] = "list_anfs"

    # initial equations
    aux_bpr = f0[0].parent()
    aux_iv = [aux_bpr(v) for v in f0_input_vars]
    right_matrix = anf2matrix(f0, aux_iv)
    def or_bits(a, b):
        return a + b + (a * b)
    if 1 in right_matrix.list() or aux_bpr(1) in right_matrix.list():
        eq1 = aux_bpr(0)
    else:
        eq1 = aux_bpr(sage.all.reduce(or_bits, right_matrix.list())) + aux_bpr(1)
    eq2 = aux_bpr(right_matrix.determinant()) + aux_bpr(0)
    initial_equations = [eq1, eq2]

    try:
        result = solve_functional_equation(
            lhs_anfs, rhs_anfs, lhs_input_vars, rhs_input_vars,
            initial_equations=initial_equations,
            verbose=verbose, debug=debug, filename=filename, **new_kwargs
        )
    except ValueError as e:
        get_smart_print(filename)(f"No solution found ({e})")
        return None
    else:
        if "return_mode" not in solve_args and "num_sat_solutions" not in solve_args:
            if solve_args.get("return_total_num_solutions", False):
                get_smart_print(filename)("ignoring return_total_num_solutions")
            return result[0][0][0], result[0][1][1]  # return f0 and g1
        else:
            return result


def find_horizontal_decomposition(
    anf, degree_anf, num_inputs_first_factor, aff_ct_terms=True, input_anf_vars=None,
    prefix_left_aff_coeffs="b", prefix_right_aff_coeffs="a",
    prefix_first_factor="p", prefix_second_factor="q",
    verbose=False, debug=False, filename=None, **solve_args
):
    """Find an horizontal decomposition P(x')|Q(x'') of G(x) in the affine class.

    An horizontal decomposition of G(x) is a pair of functions P(x'), Q(x''),
    such that x = x' || x'' and (P,Q) and G are affine equivalent
    (linear equivalent if aff_ct_terms=False), that is, B (P, Q) A = G.
    P and Q are called the first and the second factor, respectively.
    If no solution is found, None is returned.

    The triple ((P, Q), A, B) is found by solving B (P, Q) A = G.

    If aff_ct_terms=False, finds A and B linear instead of affine.

    input_anf_vars is a list of the inputs vars (containing Boolean variables
    or strings) of the given anf G (not needed for non-symbolic anfs).

    Named arguments from **solve_args are passed to solve_functional_equation().
    By default, return_mode="list_anfs" and num_sat_solutions="1".
    If there two parameters are not given, only one solution is found
    abd the triple ((P, Q), A, B), each one in ANF form, is returned.

        >>> sage.all.set_random_seed(0)
        >>> from boolcrypt.utilities import lut2anf, get_lut_inversion
        >>> anf = lut2anf([1, 0, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])  # 2nd to last 4b aff class
        >>> decomp, right_aff, left_aff = find_horizontal_decomposition(anf, 2, 1)
        setting to 0 the free variables [a0, p0, q0, q1, q2]
        >>> get_anf_coeffmatrix_str(decomp, input_vars=["x0", "x1", "x2", "x3"])
        [x2*x3|   x0    x1    x2    x3]
        [-----+-----------------------]
        [    0|    1     0     0     0]
        [    0|    0     0     1     0]
        [    0|    0     0     0     1]
        [    1|    0     1     1     1]
        >>> get_anf_coeffmatrix_str(right_aff, input_vars=["x0", "x1", "x2", "x3"])
        [x0 x1 x2 x3]
        [-----------]
        [ 0  1  0  0]
        [ 1  0  0  0]
        [ 0  0  1  0]
        [ 0  0  0  1]
        >>> get_anf_coeffmatrix_str(left_aff, input_vars=["x0", "x1", "x2", "x3"])
        [x0 x1 x2 x3| 1]
        [-----------+--]
        [ 0  0  0  1| 1]
        [ 1  0  0  0| 0]
        [ 0  1  0  0| 0]
        [ 0  0  1  0| 0]
        >>> anf = lut2anf((0, 1, 2, 3, 4, 6, 7, 5))
        >>> find_horizontal_decomposition(anf, 2, 1)  # non-linear 3b cannot be decomposed
        No solution found (system of equations is inconsistent (unsatisfiable))

    """
    if solve_args.get("bpr", None) is not None:
        assert solve_args.get("ignore_initial_parsing", False) is not True

    if input_anf_vars is None:
        aux_bpr = anf[0].parent()
        assert all(aux_bpr == f.parent() for f in anf)
        input_anf_vars = aux_bpr.gens()

    num_p_vars = num_inputs_first_factor

    concat_anf = concatenate_anf(
        get_symbolic_anf(degree_anf, num_p_vars, num_p_vars, ct_terms=aff_ct_terms,
                         prefix_inputs="x", prefix_coeffs=prefix_first_factor),
        get_symbolic_anf(degree_anf, len(input_anf_vars) - num_p_vars, len(anf) - num_p_vars,
                         ct_terms=aff_ct_terms,
                         prefix_inputs="x", prefix_coeffs=prefix_second_factor),
        prefix="x", input_vars_left=["x" + str(i) for i in range(num_p_vars)],
        input_vars_right=["x" + str(i) for i in range(len(input_anf_vars) - num_p_vars)]
    )
    input_concat_vars = ["x" + str(i) for i in range(len(input_anf_vars))]

    simplify_output = "return_mode" not in solve_args and "num_sat_solutions" not in solve_args
    if "return_mode" not in solve_args:
        # force full output in result
        solve_args["return_mode"] = "list_anfs"

    result = find_equivalence(
        concat_anf, anf, left_equiv_degree=1, right_equiv_degree=1, equiv_ct_terms=aff_ct_terms,
        left_input_vars=input_concat_vars, right_input_vars=input_anf_vars,
        prefix_left_equiv_coeffs=prefix_left_aff_coeffs,
        prefix_right_equiv_coeffs=prefix_right_aff_coeffs,
        verbose=verbose, debug=debug, filename=filename, **solve_args
    )

    if result and simplify_output:
        if solve_args.get("return_total_num_solutions", False):
            get_smart_print(filename)("ignoring return_total_num_solutions")
        return result[0][0][1], result[0][0][0], result[0][0][2]  # return f1, f0, f21
    else:
        return result


# TODO: v2 support right_anf to be in implicit form
def find_ccz_equivalence(
    left_anf, right_anf,
    equiv_degree=1, inv_equiv_degree=1, equiv_ct_terms=True,
    add_invertibility_equations=True,
    left_input_vars=None, right_input_vars=None, prefix_am_coeffs="a",
    verbose=False, debug=False, filename=None, **solve_args
):
    """Find an affine A such that A(graph F) = graph G.

    Given the left function F and the right function G,
    this method finds an invertible admissible mapping A of given degree
    such that the graph of G is equal to the graph of F transformed by A.
    If no solution is found, None is returned.

    Graph(f) is is the set of points {(x, F(x))}, and similar for Graph(G).

    If the given degree is 1 and equiv_ct_terms=True (resp. False),
    this method finds an affine (resp. linear) admissible mapping.

    If F and G are the same, this methods finds
    Graph(F) self-equivalences/automorphisms, that is,
    invertibles A such that A(graph F) = graph F.

    A = (a_0, a_1) is returned by solving the functional equation
    G(a_0(u, F(u))) = a_1(u, F(u)).

    If add_invertibility_equations=True, the equations that
    impose A to be invertible are added to the system of equations.
    In this case, if equiv_degree>1, the inv_equiv_degree is used to
    build the invertibility equations.

    left_input_vars and right_input_vars are two lists with the inputs vars
    (containing Boolean variables or strings) of the given F and G
    (not needed for non-symbolic anfs).

    Named arguments from **solve_args are passed to solve_functional_equation().
    By default, return_mode="list_anfs" and num_sat_solutions="1".
    If there two parameters are not given, only one solution is found
    and the ANF of A is returned.

        >>> sage.all.set_random_seed(0)
        >>> from boolcrypt.utilities import get_lut_inversion, lut2anf
        >>> left_anf = lut2anf((0, 1, 2, 3, 4, 6, 7, 5))
        >>> am = find_ccz_equivalence(left_anf, left_anf, only_linear_fixed_vars=True, equiv_ct_terms=False)
        >>> get_anf_coeffmatrix_str(am, input_vars=["x" + str(i) for i in range(3*2)])  # Graph-SE
        [x0 x1 x2 x3 x4 x5]
        [-----------------]
        [ 0  0  0  0  1  0]
        [ 1  0  0  0  0  0]
        [ 0  0  0  0  0  1]
        [ 1  1  0  1  0  0]
        [ 0  0  0  1  0  0]
        [ 0  0  1  0  0  0]
        >>> find_ccz_equivalence(left_anf, lut2anf(get_lut_inversion(3)), only_linear_fixed_vars=True)  # doctest:+SKIP
        No solution found (system of equations is inconsistent (unsatisfiable))
        >>> # CCZ of inversion found with sboxU.ccz_equivalent_permutations
        >>> left_anf = lut2anf([0, 15, 9, 7, 4, 14, 1, 3, 10, 6, 13, 2, 8, 5, 11, 12])
        >>> right_anf = lut2anf(get_lut_inversion(4))
        >>> # next call might require to increase Python's recursionlimit
        >>> am = find_ccz_equivalence(left_anf, right_anf, equiv_ct_terms=False,
        ...     only_linear_fixed_vars=True, verbose=True)  # doctest:+SKIP
        >>> get_anf_coeffmatrix_str(am, input_vars=["x" + str(i) for i in range(4*2)])  # doctest:+SKIP
        [x0 x1 x2 x3 x4 x5 x6 x7]
        [-----------------------]
        [ 0  1  0  1  0  0  0  0]
        [ 0  0  1  1  0  0  0  0]
        [ 1  1  1  1  0  0  0  0]
        [ 1  1  0  1  0  0  0  0]
        [ 0  1  1  1  1  1  0  0]
        [ 0  1  0  1  1  1  1  0]
        [ 0  0  0  0  1  0  1  0]
        [ 0  0  1  0  1  0  1  1]

    """
    if solve_args.get("bpr", None) is not None:
        assert solve_args.get("ignore_initial_parsing", False) is not True

    # The original equation is with the inverse, that is,
    # if B^{-1} = (b_0, b_1) verifies b_1(u, F(u)) = G(b_0(u, F(u))),
    # then Gamma_F = B(Gamma_G).
    # But this is equivalent to B(Gamma_F) = Gamma_G
    if equiv_degree == 1 or inv_equiv_degree == 1:
        assert equiv_degree == inv_equiv_degree == 1

    assert not isinstance(left_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    assert not isinstance(right_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    if left_input_vars is None:
        aux_bpr = left_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in left_anf)
        left_input_vars = aux_bpr.gens()
    if right_input_vars is None:
        aux_bpr = right_anf[0].parent()
        assert all(aux_bpr == f.parent() for f in right_anf)
        right_input_vars = aux_bpr.gens()

    assert all(not str(v).startswith(prefix_am_coeffs)
               for v in left_input_vars + right_input_vars)
    assert not prefix_am_coeffs.startswith("x")
    assert len(left_anf) == len(right_anf)
    assert len(left_input_vars) == len(right_input_vars)

    num_a_inputs = len(left_input_vars) + len(left_anf)

    a_0 = get_symbolic_anf(equiv_degree, num_a_inputs, len(left_input_vars), ct_terms=equiv_ct_terms,
                           prefix_inputs="x", prefix_coeffs=prefix_am_coeffs+"a")
    a_1 = get_symbolic_anf(equiv_degree, num_a_inputs, len(left_anf), ct_terms=equiv_ct_terms,
                           prefix_inputs="x", prefix_coeffs=prefix_am_coeffs+"b")
    a_varnames = list(a_0[0].parent().variable_names())
    a_varnames.extend(vn for vn in a_1[0].parent().variable_names() if vn not in a_varnames)
    a_bpr = BooleanPolynomialRing(len(a_varnames), a_varnames)
    a = BooleanPolynomialVector()
    for component in itertools.chain(a_0, a_1):
        a.append(a_bpr(component))

    # G(a_0(u, F(u))) = a_1(u, F(u))
    f2 = right_anf
    f1 = a_0
    f0 = BooleanPolynomialVector()
    for component in itertools.chain(left_input_vars, left_anf):
        f0.append(component)

    f2_input_vars = right_input_vars
    f1_input_vars = ["x" + str(i) for i in range(num_a_inputs)]
    f0_input_vars = ["x" + str(i) for i in range(len(left_input_vars))]

    g1 = a_1
    g0 = f0

    g1_input_vars = ["x" + str(i) for i in range(num_a_inputs)]
    g0_input_vars = f0_input_vars

    lhs_anfs = [f0, f1, f2]
    lhs_input_vars = [f0_input_vars, f1_input_vars, f2_input_vars]

    rhs_anfs = [g0, g1]
    rhs_input_vars = [g0_input_vars, g1_input_vars]

    if add_invertibility_equations:
        if equiv_degree == 1:
            a_matrix = anf2matrix(a, [a_bpr("x" + str(i)) for i in range(num_a_inputs)])
            initial_equations = [a_bpr(a_matrix.determinant()) + a_bpr(1)]
        else:
            initial_equations = find_inverse(
                a, inv_equiv_degree, inv_position="left", prefix_inv_coeffs=prefix_am_coeffs+"c",
                input_vars=["x" + str(i) for i in range(num_a_inputs)],
                verbose=verbose, debug=debug, filename=filename, return_mode="raw_equations"
            )
            assert initial_equations is not None
    else:
        initial_equations = []

    new_kwargs = solve_args.copy()
    if "num_sat_solutions" not in new_kwargs:
        new_kwargs["num_sat_solutions"] = 1
    if "return_mode" not in new_kwargs:
        new_kwargs["return_mode"] = "list_anfs"
    if "initial_equations" in new_kwargs:
        new_kwargs["initial_equations"].extend(initial_equations)
    else:
        new_kwargs["initial_equations"] = initial_equations

    try:
        result = solve_functional_equation(
            lhs_anfs, rhs_anfs, lhs_input_vars, rhs_input_vars,
            verbose=verbose, debug=debug, filename=filename, **new_kwargs
        )
    except ValueError as e:
        get_smart_print(filename)(f"No solution found ({e})")
        return None
    else:
        if "return_mode" not in solve_args and "num_sat_solutions" not in solve_args:
            if solve_args.get("return_total_num_solutions", False):
                get_smart_print(filename)("ignoring return_total_num_solutions")
            a_0_sol = result[0][0][1]  # f1
            a_1_sol = result[0][1][1]  # g1
            a_sol = BooleanPolynomialVector()
            for component in itertools.chain(a_0_sol, a_1_sol):
                a_sol.append(component)
            return a_sol
        else:
            return result
