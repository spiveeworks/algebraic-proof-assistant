#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define STB_DS_IMPLEMENTATION
#include "stb_ds.h"

/***********/
/* Strings */
/***********/

typedef struct str {
    long size;
    char *data;
} str;

#define CSTR(STR) ((struct str){strlen(STR), STR})

void fputstr(str string, FILE *f) {
    fwrite(string.data, 1, string.size, f);
}

/********************/
/* Rational numbers */
/********************/

typedef struct rational {
    long numerator;
    unsigned long denominator;
} rational;

#define INT(X) ((struct rational){X, 1})

unsigned long gcd(long x_signed, long y_signed) {
    unsigned long x = x_signed >= 0 ? x_signed : -x_signed;
    unsigned long y = y_signed >= 0 ? y_signed : -y_signed;
    unsigned int twos = 0;
    while (x % 2 == 0) {
        x /= 2;
        if (y % 2 == 0) {
            y /= 2;
            twos += 1;
        }
    }
    while (y % 2 == 0) {
        y /= 2;
    }
    while (x != y) {
        unsigned long min = x < y ? x : y;
        unsigned long max = x < y ? y : x;
        /* x and y are both odd, so their difference is even */
        x = max - min;
        y = min;
        while (x % 2 == 0) {
            x /= 2;
        }
    }
    return x << twos;
}

void normalise(rational *r) {
    unsigned long cf = gcd(r->numerator, r->denominator);
    r->numerator /= cf;
    r->denominator /= cf;
}

void rat_add(rational *x, rational *y) {
    unsigned long cf = gcd(x->denominator, y->denominator);
    unsigned long xscale = y->denominator / cf;
    unsigned long yscale = x->denominator / cf;

    x->denominator *= xscale;
    x->numerator = xscale * x->numerator + yscale * y->numerator;
}

rational rat_mul(rational x, rational y) {
    return (rational){
        x.numerator * y.numerator,
        x.denominator * y.denominator
    };
}

/***************/
/* Polynomials */
/***************/

struct polynomial {
    str *variables;
    rational *coefficients;
    int *term_indices;
};

struct polynomial poly_dup(struct polynomial p) {
    str *variables = NULL;
    rational *coefficients = NULL;
    int *term_indices = NULL;

    long len = arrlen(p.variables);
    arrsetlen(variables, len);
    for (int i = 0; i < len; i++) variables[i] = p.variables[i];

    len = arrlen(p.coefficients);
    arrsetlen(coefficients, len);
    for (int i = 0; i < len; i++) coefficients[i] = p.coefficients[i];

    len = arrlen(p.term_indices);
    arrsetlen(term_indices, len);
    for (int i = 0; i < len; i++) term_indices[i] = p.term_indices[i];

    return (struct polynomial){variables, coefficients, term_indices};
}

void poly_print(FILE *out, struct polynomial p) {
    int term_count = arrlen(p.coefficients);
    int variable_count = arrlen(p.variables);
    for (int i = 0; i < term_count; i++) {
        rational *c = &p.coefficients[i];
        if (c->numerator == 0) continue;
        if (c->numerator > 0) fprintf(out, " + ");
        fprintf(out, "%ld", c->numerator);
        if (c->denominator != 1) fprintf(out, "/%lu", c->denominator);
        int *indices = &p.term_indices[i * variable_count];
        for (int j = 0; j < variable_count; j++) {
            int index = indices[j];
            if (index == 0) continue;
            fputstr(p.variables[j], out);
            if (index != 1) fprintf(out, "^%d", index);
        }
    }
}

struct monomial {
    int variable_count;
    rational coefficient;
    int *term_indices;
};

struct monomial poly_index(struct polynomial *p, int i) {
    int variable_count = arrlen(p->variables);
    return (struct monomial){
        variable_count,
        p->coefficients[i],
        &p->term_indices[(long)i * variable_count]
    };
}

void poly_add_mono(struct polynomial *p, struct monomial q) {
    int p_i;
    bool found = false;
    int variable_count = arrlen(p->variables);
    int p_term_count = arrlen(p->coefficients);
    for (p_i = 0; p_i < p_term_count; p_i++) {
        int *p_indices = &p->term_indices[p_i * variable_count];
        found = true;
        for (int j = 0; j < q.variable_count; j++) {
            if (p_indices[j] != q.term_indices[j]) {
                found = false;
                break;
            }
        }
        if (found) break;
    }
    if (found) {
        rat_add(&p->coefficients[p_i], &q.coefficient);
    } else {
        arrpush(p->coefficients, q.coefficient);
        int *p_indices = arraddnptr(p->term_indices, variable_count);
        for (int j = 0; j < variable_count; j++) {
            p_indices[j] = q.term_indices[j];
        }
    }
}

void poly_add(struct polynomial *p, struct polynomial *q) {
    int variable_count = arrlen(p->variables);
    if (variable_count != arrlen(q->variables)) {
        fprintf(stderr, "Tried to add polynomials with differing numbers of terms.\n");
        exit(EXIT_FAILURE);
    }
    int q_term_count = arrlen(q->coefficients);
    for (int i = 0; i < q_term_count; i++) {
        poly_add_mono(p, poly_index(q, i));
    }
}

void poly_mul_add(struct polynomial *p, struct polynomial *q1, struct polynomial *q2) {
    int variable_count = arrlen(p->variables);
    if (variable_count != arrlen(q1->variables)
        || variable_count != arrlen(q2->variables))
    {
        fprintf(stderr, "Tried to multiply-add polynomials with differing numbers of terms.\n");
        exit(EXIT_FAILURE);
    }
    int q1_term_count = arrlen(q1->coefficients);
    int q2_term_count = arrlen(q2->coefficients);
    struct monomial m;
    int term_indices[variable_count];
    m.variable_count = variable_count;
    m.term_indices = term_indices;
    for (int i1 = 0; i1 < q1_term_count; i1++) {
        int *q1_term_indices = &q1->term_indices[i1 * variable_count];
        for (int i2 = 0; i2 < q2_term_count; i2++) {
            int *q2_term_indices = &q2->term_indices[i2 * variable_count];
            m.coefficient = rat_mul(q1->coefficients[i1], q2->coefficients[i2]);
            for (int j = 0; j < variable_count; j++) {
                m.term_indices[j] = q1_term_indices[j] + q2_term_indices[j];
            }
            poly_add_mono(p, m);
        }
    }
}

/**********/
/* Output */
/**********/

int main(int argc, char **argv) {
    str *variables = NULL;
    arrpush(variables, CSTR("x"));
    arrpush(variables, CSTR("y"));
    struct polynomial p = {.variables = variables};
    struct polynomial q = {.variables = variables};
    arrpush(q.coefficients, INT(1));
    arrpush(q.term_indices, 1);
    arrpush(q.term_indices, 0);
    arrpush(q.coefficients, INT(1));
    arrpush(q.term_indices, 0);
    arrpush(q.term_indices, 1);
    poly_mul_add(&p, &q, &q);
    fprintf(stdout, "(");
    poly_print(stdout, q);
    fprintf(stdout, ")^2 =");
    poly_print(stdout, p);
    fprintf(stdout, "\n");

    return 0;
}

