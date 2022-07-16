#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdbool.h>
#include <m4ri/m4ri.h>

#include "white_box_backend.c"

// A monomial consists of a boolean flag and four bit-packed words.
// If is_zero is set, the monomial represents '0' and the other fields are ignored.
// Otherwise, the i-th bit in a word means that variable x_i is included in the monomial.
// This representation is multiplicative with respect to the variables.
// Consequently, if all words are 0, all exponents are 0, and the monomial represents '1'.
typedef struct monomial {
    bool is_zero;
    WORD_TYPE x_exps;
    WORD_TYPE y_exps;
    WORD_TYPE z_exps;
    WORD_TYPE t_exps;
} monomial;

// Sets a monomial to '1'.
void monomial_set_one(monomial *mon) {
    mon->is_zero = false;
    mon->x_exps = 0;
    mon->y_exps = 0;
    mon->z_exps = 0;
    mon->t_exps = 0;
}

// Initializes a monomial with some input variables (x_i and y_i) and one output variable (z_i or t_i).
void monomial_init(size_t in_degree, size_t *in_vars, size_t out_var, monomial *mon) {
    assert(in_vars != NULL && mon != NULL);

    monomial_set_one(mon);

    for (size_t i = 0; i < in_degree; i++) {
        size_t in_var = in_vars[i];
        assert(0 * WORD_SIZE <= in_var && in_var <= 2 * WORD_SIZE);
        if (0 * WORD_SIZE <= in_var && in_var < 1 * WORD_SIZE) {
            mon->x_exps |= WORD_CONSTANT_TYPE(1) << (in_var - 0 * WORD_SIZE);
        }
        if (1 * WORD_SIZE <= in_var && in_var < 2 * WORD_SIZE) {
            mon->y_exps |= WORD_CONSTANT_TYPE(1) << (in_var - 1 * WORD_SIZE);
        }
    }

    assert(0 * WORD_SIZE <= out_var && out_var <= 2 * WORD_SIZE);
    if (0 * WORD_SIZE <= out_var && out_var < 1 * WORD_SIZE) {
        mon->z_exps |= WORD_CONSTANT_TYPE(1) << (out_var - 0 * WORD_SIZE);
    }
    if (1 * WORD_SIZE <= out_var && out_var < 2 * WORD_SIZE) {
        mon->t_exps |= WORD_CONSTANT_TYPE(1) << (out_var - 1 * WORD_SIZE);
    }
}

void initialize_sorted_monomials_(monomial *monomials, size_t in_degree, size_t out_var, size_t *m) {
    assert(monomials != NULL && m != NULL);

    if (in_degree > 2 * WORD_SIZE) {
        return;
    }

    size_t in_vars[in_degree];
    for (size_t i = 0; i < in_degree; i++) {
        in_vars[i] = i;
    }

    monomial_init(in_degree, in_vars, out_var, &monomials[(*m)++]);
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

        monomial_init(in_degree, in_vars, out_var, &monomials[(*m)++]);
    }
}

void initialize_sorted_monomials(monomial *monomials) {
    assert(monomials != NULL);

    size_t m = 0;
    // The first monomial is always '1'.
    monomial_set_one(&monomials[m++]);

    for (size_t in_degree = 1; in_degree < MAX_DEGREE + 1; in_degree++) {
        initialize_sorted_monomials_(monomials, in_degree, 2 * WORD_SIZE, &m);
    }

    for (size_t out_var = 0; out_var < 2 * WORD_SIZE; out_var++) {
        for (size_t in_degree = 0; in_degree < MAX_DEGREE; in_degree++) {
            initialize_sorted_monomials_(monomials, in_degree, out_var, &m);
        }
    }
}

// Substitutes some x and y values in a monomial.
void monomial_substitute(monomial *in, WORD_TYPE x, WORD_TYPE y, monomial *out) {
    assert(in != NULL && out != NULL);

    // If the input is 0, the output is 0.
    if (in->is_zero) {
        out->is_zero = true;
        return;
    }

    for (size_t i = 0; i < WORD_SIZE; i++) {
        // If the input contains x_i and the x_i value to be substituted is 0, the output is 0.
        if (((in->x_exps >> i) & 1) && !((x >> i) & 1)) {
            out->is_zero = true;
            return;
        }
        // If the input contains y_i and the y_i value to be substituted is 0, the output is 0.
        if (((in->y_exps >> i) & 1) && !((y >> i) & 1)) {
            out->is_zero = true;
            return;
        }
    }

    // Only the z and t variables are left in the output.
    monomial_set_one(out);
    out->z_exps = in->z_exps;
    out->t_exps = in->t_exps;
}

void solve_system(monomial *substituted, size_t *coeffs_index, WORD_TYPE *z, WORD_TYPE *t) {
    assert(substituted != NULL && coeffs_index != NULL && z != NULL && t != NULL);
    assert((2 * WORD_SIZE) % MONOMIAL_WORD_SIZE == 0);

    mzd_t *A = mzd_init(2 * WORD_SIZE, 2 * WORD_SIZE);
    mzd_t *B = mzd_init(2 * WORD_SIZE, 1);
    // Coefficients are sorted by the monomial order.
    for (size_t j = 0; j < MONOMIALS; j++) {
        monomial mon = substituted[j];
        if (mon.is_zero) {
            *coeffs_index += (2 * WORD_SIZE) / MONOMIAL_WORD_SIZE;
            continue;
        }

        // Substituted monomials shouldn't contain x or y variables.
        assert((mon.x_exps | mon.y_exps) == 0);
        // Substituted monomials shouldn't contain both z and t variables.
        assert(mon.z_exps == 0 || mon.t_exps == 0);
        // Substituted monomials should contain at most one z variable.
        assert((mon.z_exps & (mon.z_exps - 1)) == 0);
        // Substituted monomials should contain at most one t variable.
        assert((mon.t_exps & (mon.t_exps - 1)) == 0);
        for (size_t k = 0; k < 2 * WORD_SIZE; k += MONOMIAL_WORD_SIZE) {
            MONOMIAL_WORD_TYPE coeff = COEFFS[(*coeffs_index)++];
            for (size_t i = 0; i < MONOMIAL_WORD_SIZE; i++) {
                if ((coeff >> i) & 1) {
                    if ((mon.z_exps | mon.t_exps) == 0) {
                        // If the substituted monomial is '1', we XOR the vector.
                        mzd_xor_bits(B, k + i, 0, 1, 1);
                    } else{
                        // Otherwise, we XOR the matrix corresponding to the unknowns.
                        mzd_xor_bits(A, k + i, 0, WORD_SIZE, mon.z_exps);
                        mzd_xor_bits(A, k + i, WORD_SIZE, WORD_SIZE, mon.t_exps);
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
            *z |= WORD_CONSTANT_TYPE(1) << i;
        }
        if (mzd_read_bit(B, WORD_SIZE + i, 0)) {
            *t |= WORD_CONSTANT_TYPE(1) << i;
        }
    }

    mzd_free(A);
    mzd_free(B);
}

void solve_implicit(monomial *monomials, monomial *substituted, WORD_TYPE x, WORD_TYPE y, size_t *coeffs_index, WORD_TYPE *z, WORD_TYPE *t) {
    assert(monomials != NULL && substituted != NULL && coeffs_index != NULL && z != NULL && t != NULL);

    for (size_t i = 0; i < MONOMIALS; i++) {
        monomial_substitute(&monomials[i], x, y, &substituted[i]);
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

void evaluate_explicit(monomial *monomials, monomial *substituted, WORD_TYPE x, WORD_TYPE y, size_t substituted_max, const MONOMIAL_WORD_TYPE *coeffs, WORD_TYPE *z, WORD_TYPE *t) {
    assert(monomials != NULL && substituted != NULL && coeffs != NULL && z != NULL && t != NULL);
    assert((2 * WORD_SIZE) % MONOMIAL_WORD_SIZE == 0);

    for (size_t i = 0; i < substituted_max; i++) {
        monomial_substitute(&monomials[i], x, y, &substituted[i]);
    }

    *z = 0;
    *t = 0;
    size_t coeffs_index = 0;
    for (size_t j = 0; j < substituted_max; j++) {
        monomial mon = substituted[j];
        if (mon.is_zero) {
            coeffs_index += (2 * WORD_SIZE) / MONOMIAL_WORD_SIZE;
            continue;
        }

        // Substituted monomials shouldn't contain any variables here.
        assert((mon.x_exps | mon.y_exps | mon.z_exps | mon.t_exps) == 0);
        for (size_t k = 0; k < 2 * WORD_SIZE; k += MONOMIAL_WORD_SIZE) {
            MONOMIAL_WORD_TYPE coeff = coeffs[coeffs_index++];
            for (size_t i = 0; i < MONOMIAL_WORD_SIZE; i++) {
                if ((coeff >> i) & 1) {
                    if (k + i < WORD_SIZE) {
                        *z ^= WORD_CONSTANT_TYPE(1) << (k + i);
                    } else {
                        *t ^= WORD_CONSTANT_TYPE(1) << (k + i - WORD_SIZE);
                    }
                }
            }
        }
    }
}

void encrypt(monomial *monomials, monomial *substituted, WORD_TYPE p[2], WORD_TYPE c[2]) {
    c[0] = p[0];
    c[1] = p[1];

    FIRST_EXPLICIT_ROUND(c[0], c[1]);

#ifdef MONOMIALS_EXTIN
    evaluate_explicit(monomials, substituted, c[0], c[1], MONOMIALS_EXTIN, COEFFS_EXTIN, &c[0], &c[1]);
#endif

    size_t coeffs_index = 0;
    for (size_t r = 0; r < ROUNDS; r++) {
        solve_implicit(monomials, substituted, c[0], c[1], &coeffs_index, &c[0], &c[1]);
    }

#ifdef MONOMIALS_EXTOUT
    evaluate_explicit(monomials, substituted, c[0], c[1], MONOMIALS_EXTOUT, COEFFS_EXTOUT, &c[0], &c[1]);
#endif

    LAST_EXPLICIT_ROUND(c[0], c[1]);
}

int main(int argc, char *argv[]) {
    monomial *monomials = malloc(MONOMIALS * sizeof(monomial));
    initialize_sorted_monomials(monomials);
    monomial *substituted = malloc(MONOMIALS * sizeof(monomial));

    WORD_TYPE p[2];
    WORD_TYPE c[2];
    if (argc < 3) {
        return -1;
    } else {
        sscanf(argv[1], "%" WORD_IN_TYPE, &p[0]);
        sscanf(argv[2], "%" WORD_IN_TYPE, &p[1]);
        encrypt(monomials, substituted, p, c);
        printf("%" WORD_OUT_TYPE " %" WORD_OUT_TYPE "\n", c[0], c[1]);
    }

    free(substituted);
    free(monomials);
}
