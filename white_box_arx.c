#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdbool.h>
#include <m4ri/m4ri.h>

#include "white_box_backend.c"

typedef struct monomial {
    WORD_TYPE x_exps;
    WORD_TYPE y_exps;
    WORD_TYPE z_exps;
    WORD_TYPE t_exps;
} monomial;

monomial *monomial_one() {
    monomial *mon = (monomial *) malloc(sizeof(monomial));
    mon->x_exps = WORD_CONSTANT_TYPE(0);
    mon->y_exps = WORD_CONSTANT_TYPE(0);
    mon->z_exps = WORD_CONSTANT_TYPE(0);
    mon->t_exps = WORD_CONSTANT_TYPE(0);
    return mon;
}

monomial *monomial_substitute(monomial *mon, WORD_TYPE x, WORD_TYPE y) {
    if (mon == NULL || (mon->x_exps | mon->y_exps) == 0) {
        return mon;
    }

    for (size_t i = 0; i < WORD_SIZE; i++) {
        if (((mon->x_exps >> i) & 1) && !((x >> i) & 1) || ((mon->y_exps >> i) & 1) && !((y >> i) & 1)) {
            return NULL;
        }
    }

    monomial *ans = monomial_one();
    ans->z_exps = mon->z_exps;
    ans->t_exps = mon->t_exps;
    return ans;
}

monomial *make_monomial(size_t *in_vars, size_t in_degree, size_t out_var) {
    monomial *mon = monomial_one();
    for (size_t i = 0; i < in_degree; i++) {
        size_t in_var = in_vars[i];
        if (0 * WORD_SIZE <= in_var && in_var < 1 * WORD_SIZE) {
            mon->x_exps |= WORD_CONSTANT_TYPE(1) << (in_var - 0 * WORD_SIZE);
        }
        if (1 * WORD_SIZE <= in_var && in_var < 2 * WORD_SIZE) {
            mon->y_exps |= WORD_CONSTANT_TYPE(1) << (in_var - 1 * WORD_SIZE);
        }
    }

    if (0 * WORD_SIZE <= out_var && out_var < 1 * WORD_SIZE) {
        mon->z_exps |= WORD_CONSTANT_TYPE(1) << (out_var - 0 * WORD_SIZE);
    }
    if (1 * WORD_SIZE <= out_var && out_var < 2 * WORD_SIZE) {
        mon->t_exps |= WORD_CONSTANT_TYPE(1) << (out_var - 1 * WORD_SIZE);
    }

    return mon;
}

void initialize_monomials_combinations(monomial **monomials, size_t in_degree, size_t out_var, size_t *m) {
    assert(monomials != NULL);

    if (in_degree > 2 * WORD_SIZE) {
        return;
    }

    size_t in_vars[in_degree];
    for (size_t i = 0; i < in_degree; i++) {
        in_vars[i] = i;
    }

    monomials[(*m)++] = make_monomial(in_vars, in_degree, out_var);
    for (;;) {
        size_t i = in_degree;
        while (i-- > 0) {
            if (in_vars[i] != i + 2 * WORD_SIZE - in_degree) {
                break;
            }
        }

        if (i > in_degree) {
            return;
        }

        in_vars[i] += 1;
        for (size_t j = i + 1; j < in_degree; j++) {
            in_vars[j] = in_vars[j - 1] + 1;
        }

        monomials[(*m)++] = make_monomial(in_vars, in_degree, out_var);
    }
}

void initialize_monomials(monomial **monomials) {
    assert(monomials != NULL);

    size_t m = 0;
    monomials[m++] = monomial_one();
    for (size_t in_degree = 1; in_degree < MAX_DEGREE + 1; in_degree++) {
        initialize_monomials_combinations(monomials, in_degree, 2 * WORD_SIZE, &m);
    }

    for (size_t out_var = 0; out_var < 2 * WORD_SIZE; out_var++) {
        for (size_t in_degree = 0; in_degree < MAX_DEGREE; in_degree++) {
            initialize_monomials_combinations(monomials, in_degree, out_var, &m);
        }
    }
}

void solve_system(monomial **substituted, size_t *coeffs_index, WORD_TYPE *z, WORD_TYPE *t) {
    assert(substituted != NULL);

    mzd_t *A = mzd_init(2 * WORD_SIZE, 2 * WORD_SIZE);
    mzd_t *B = mzd_init(2 * WORD_SIZE, 1);
    for (size_t j = 0; j < MONOMIALS; j++) {
        monomial *mon = substituted[j];
        for (size_t k = 0; k < 2 * WORD_SIZE; k += MONOMIAL_WORD_SIZE) {
            MONOMIAL_WORD_TYPE coeff = coeffs[(*coeffs_index)++];
            if (mon == NULL) {
                continue;
            }

            assert((mon->x_exps | mon->y_exps) == 0);
            assert(mon->z_exps == 0 || mon->t_exps == 0);
            assert((mon->z_exps & (mon->z_exps - 1)) == 0);
            assert((mon->t_exps & (mon->t_exps - 1)) == 0);
            for (size_t i = 0; i < MONOMIAL_WORD_SIZE; i++) {
                if ((coeff >> i) & 1) {
                    if ((mon->z_exps | mon->t_exps) == 0) {
                        mzd_xor_bits(B, k + i, 0, 1, 1);
                    } else{
                        mzd_xor_bits(A, k + i, 0, WORD_SIZE, mon->z_exps);
                        mzd_xor_bits(A, k + i, WORD_SIZE, WORD_SIZE, mon->t_exps);
                    }
                }
            }
        }
    }

    mzd_solve_left(A, B, 0, 0);

    *z = 0;
    *t = 0;
    for (size_t i = 0; i < WORD_SIZE; i++) {
        if (mzd_read_bit(B, i, 0)) {
            *z |= (WORD_CONSTANT_TYPE(1) << i);
        }
        if (mzd_read_bit(B, WORD_SIZE + i, 0)) {
            *t |= (WORD_CONSTANT_TYPE(1) << i);
        }
    }

    mzd_free(A);
    mzd_free(B);
}

void solve_implicit(monomial **monomials, WORD_TYPE x, WORD_TYPE y, size_t *coeffs_index, WORD_TYPE *z, WORD_TYPE *t) {
    monomial *substituted[MONOMIALS];
    for (size_t i = 0; i < MONOMIALS; i++) {
        substituted[i] = monomial_substitute(monomials[i], x, y);
    }

#if USE_REDUNDANT_PERTURBATIONS
    WORD_TYPE z0;
    WORD_TYPE t0;
    solve_system(substituted, coeffs_index, &z0, &t0);
    WORD_TYPE z1;
    WORD_TYPE t1;
    solve_system(substituted, coeffs_index, &z1, &t1);
    WORD_TYPE z2;
    WORD_TYPE t2;
    solve_system(substituted, coeffs_index, &z2, &t2);
    WORD_TYPE z3;
    WORD_TYPE t3;
    solve_system(substituted, coeffs_index, &z3, &t3);

    if ((z0 == z1 && t0 == t1) || (z0 == z2 && t0 == t2) || (z0 == z3 && t0 == t3)) {
        *z = z0;
        *t = t0;
    } else if ((z1 == z2 && t1 == t2) || (z1 == z3 && t1 == t3)) {
        *z = z1;
        *t = t1;
    } else if ((z2 == z3 && t2 == t3)) {
        *z = z2;
        *t = t2;
    } else {
        printf("Could not find consensus for solutions of perturbed variants\n");
        printf("z0 = %" WORD_OUT_TYPE ", t0 = %" WORD_OUT_TYPE "\n", z0, t0);
        printf("z1 = %" WORD_OUT_TYPE ", t1 = %" WORD_OUT_TYPE "\n", z1, t1);
        printf("z2 = %" WORD_OUT_TYPE ", t2 = %" WORD_OUT_TYPE "\n", z2, t2);
        printf("z3 = %" WORD_OUT_TYPE ", t3 = %" WORD_OUT_TYPE "\n", z3, t3);
        exit(1);
    }
#else
    solve_system(substituted, coeffs_index, z, t);
#endif
}

void encrypt(monomial **monomials, WORD_TYPE p[2], WORD_TYPE c[2]) {
    c[0] = p[0];
    c[1] = p[1];

    FIRST_EXPLICIT_ROUND(c[0], c[1]);

    size_t coeffs_index = 0;
    for (size_t r = 0; r < ROUNDS; r++) {
//         printf("%" WORD_OUT_TYPE " %" WORD_OUT_TYPE "\n", c[0], c[1]);
        solve_implicit(monomials, c[0], c[1], &coeffs_index, &c[0], &c[1]);
    }

    LAST_EXPLICIT_ROUND(c[0], c[1]);
}

int main(int argc, char *argv[]) {
    monomial *monomials[MONOMIALS];
    initialize_monomials(monomials);

    WORD_TYPE p[2];
    WORD_TYPE c[2];
    if (argc < 3) {
        return -1;
    } else {
        sscanf(argv[1], "%" WORD_IN_TYPE, &p[0]);
        sscanf(argv[2], "%" WORD_IN_TYPE, &p[1]);
        encrypt(monomials, p, c);
        printf("%" WORD_OUT_TYPE " %" WORD_OUT_TYPE "\n", c[0], c[1]);
    }
}

