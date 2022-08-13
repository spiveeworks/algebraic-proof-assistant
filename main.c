#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <errno.h>

#ifdef _MSC_VER
#define alloca _alloca
#endif

#define STB_DS_IMPLEMENTATION
#include "stb_ds.h"

/***********/
/* Strings */
/***********/

typedef struct str {
    char *data;
    long size;
} str;

bool str_eq(str a, str b) {
    if (a.size != b.size) return false;
    return strncmp(a.data, b.data, a.size) == 0;
}

#define CSTR(STR) ((struct str){STR, strlen(STR)})

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

    if (x == 0) return y;
    if (y == 0) return x;

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

void rat_normalise(rational *r) {
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

struct polynomial poly_dup_terms(struct polynomial p) {
    {
        rational *coefficients = NULL;
        long len = arrlen(p.coefficients);
        arrsetlen(coefficients, len);
        for (int i = 0; i < len; i++) coefficients[i] = p.coefficients[i];
        p.coefficients = coefficients;
    }

    {
        int *term_indices = NULL;
        long len = arrlen(p.term_indices);
        arrsetlen(term_indices, len);
        for (int i = 0; i < len; i++) term_indices[i] = p.term_indices[i];
        p.term_indices = term_indices;
    }

    return p;
}

struct polynomial poly_dup(struct polynomial p) {
    {
        str *variables = NULL;
        long len = arrlen(p.variables);
        arrsetlen(variables, len);
        for (int i = 0; i < len; i++) variables[i] = p.variables[i];
        p.variables = variables;
    }

    return poly_dup_terms(p);
}

void poly_free_terms(struct polynomial *p) {
    arrfree(p->coefficients);
    arrfree(p->term_indices);
}

void poly_free(struct polynomial *p) {
    arrfree(p->variables);
    arrfree(p->coefficients);
    arrfree(p->term_indices);
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

void mono_print(str *variables, struct monomial p) {
    if (p.coefficient.numerator > 0) printf(" + ");
    printf("%ld", p.coefficient.numerator);
    if (p.coefficient.denominator != 1) printf("/%lu", p.coefficient.denominator);
    for (int j = 0; j < p.variable_count; j++) {
        int index = p.term_indices[j];
        if (index == 0) continue;
        fputstr(variables[j], stdout);
        if (index != 1) printf("^%d", index);
    }
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
        //int *p_indices = arraddnptr(p->term_indices, variable_count);
        for (int j = 0; j < variable_count; j++) {
            //p_indices[j] = q.term_indices[j];
            arrpush(p->term_indices, q.term_indices[j]);
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
    int *term_indices = alloca(variable_count * sizeof(int));
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

void mono_mul(struct monomial *p, struct monomial q) {
    str *vars = NULL;
    arrpush(vars, CSTR("x"));
    arrpush(vars, CSTR("b"));
    arrpush(vars, CSTR("c"));
    p->coefficient = rat_mul(p->coefficient, q.coefficient);
    for (int j = 0; j < q.variable_count; j++) {
        p->term_indices[j] += q.term_indices[j];
    }
}

void poly_mul_mono(struct polynomial *p, struct monomial q) {
    int variable_count = arrlen(p->variables);
    if (variable_count != q.variable_count) {
        fprintf(stderr, "Tried to multiply a polynomial and a monomial with differing numbers of terms.\n");
        exit(EXIT_FAILURE);
    }
    int term_count = arrlen(p->coefficients);
    for (int i = 0; i < term_count; i++) {
        int *term_indices = &p->term_indices[i * variable_count];

        p->coefficients[i] = rat_mul(p->coefficients[i], q.coefficient);
        for (int j = 0; j < variable_count; j++) {
            p->term_indices[j] += q.term_indices[j];
        }
    }
}

/**********************/
/* Expression Parsing */
/**********************/

#define IS_LOWER(c) ('a' <= (c) && (c) <= 'z')
#define IS_UPPER(c) ('A' <= (c) && (c) <= 'Z')
#define IS_ALPHA(c) (IS_LOWER(c) || IS_UPPER(c))
#define IS_NUM(c) ('0' <= (c) && (c) <= '9')
#define IS_ALPHANUM(c) (IS_ALPHA(c) || IS_NUM(c) || (c) == '_')
#define IS_WHITESPACE(c) ((c) == ' ' || (c) == '\t' || (c) == '\n' || (c) == '\r')
#define IS_PRINTABLE(c) (' ' <= (c) && (c) <= '~')

enum atom_type {
    ATOM_NUMERAL,
    ATOM_VAR,
    ATOM_PLUS = '+',
    ATOM_MINUS = '-',
    ATOM_TIMES = '*',
};

struct atom {
    enum atom_type type;
    union {
        int id;
        rational value;
    };
};

void atom_print(struct atom x) {
    switch (x.type) {
      case ATOM_NUMERAL:
        rat_normalise(&x.value);
        printf("%ld/%lu", x.value.numerator, x.value.denominator);
        break;
      case ATOM_VAR:
        printf("var%d", x.id);
        break;
      case ATOM_PLUS:
        fputc('+', stdout);
        break;
      case ATOM_MINUS:
        fputc('-', stdout);
        break;
      case ATOM_TIMES:
        fputc('*', stdout);
        break;
      default:
        printf("?");
        break;
    }
}

bool atom_eq(struct atom x, struct atom y) {
    if (x.type != y.type) return false;
    if (x.type == ATOM_NUMERAL && x.value.numerator * y.value.denominator != y.value.numerator * x.value.denominator) return false;
    if (x.type == ATOM_VAR && x.id != y.id) return false;
    /* else */
    return true;
}

enum operation_stack_type {
    OP_PLUS = '+',
    OP_MINUS = '-',
    OP_TIMES = '*',
    OP_PAREN = '(',
};

enum operation_precedence {
    PRECEDENCE_MULTIPLICATIVE,
    PRECEDENCE_ADDITIVE,
    PRECEDENCE_GROUPING,
};

struct partial_operation {
    enum operation_stack_type type;
    enum operation_precedence precedence;
};

struct expr {
    str *variables;
    struct atom *body;
};

int lookup_name(str *variables, str name) {
    for (int i = 0; i < arrlen(variables); i++) {
        if (str_eq(variables[i], name)) return i;
    }
    return -1;
}

/* TODO: Make a get_token function instead, which skips whitespace and pushes
   the input string forward. We could also change parse_expression to use its
   str pointer the whole way through, just calling get_token for everything. */
int get_alphanum_prefix(str input) {
    char *end = input.data + input.size;
    int result = 0;
    while (input.data < end && IS_ALPHANUM(*input.data)) {
        result++;
        input.data++;
    }
    return result;
}

struct expr parse_expression(str *input, str *variables) {
    /* TODO: Track the number of values that would be on the stack during
       execution of the RPN stream, and complain if there wouldn't be enough
       values for a given operation, or if there wouldn't exactly one value at
       the end. */
    char *stream = input->data;
    char *end = stream + input->size;

    struct partial_operation *stack = NULL;
    struct atom *body = NULL;
    while (stream < end) {
        char c = *stream;
        if (IS_WHITESPACE(c)) {
            stream++;
        } else if (IS_ALPHA(c)) {
            str varname = {stream, 1};
            stream++;
            while (stream < end && IS_ALPHANUM(*stream)) {
                varname.size++;
                stream++;
            }

            int id = lookup_name(variables, varname);
            if (id == -1) {
                fprintf(stderr, "Error: Unknown variable name \"");
                fputstr(varname, stderr);
                fprintf(stderr, "\"\n");
                exit(EXIT_FAILURE);
            }

            struct atom next;
            next.type = ATOM_VAR;
            next.id = id;
            arrpush(body, next);
        } else if (IS_NUM(c) || (c == '.' && stream + 1 < end && IS_NUM(stream[1]))) {
            rational num = {0,1};
            bool fractional = false;

            if (c == '.') fractional = true;
            else num.numerator = c - '0';

            stream++;

            while (stream < end && (IS_NUM(*stream) || (*stream == '.' && stream + 1 < end && IS_NUM(stream[1])))) {
                if (*stream == '.') {
                    fractional = true;
                } else {
                    num.numerator *= 10;
                    num.numerator += *stream - '0';
                    if (fractional) num.denominator *= 10;
                }
                stream++;
            }

            rat_normalise(&num);

            struct atom next;
            next.type = ATOM_NUMERAL;
            next.value = num;
            arrpush(body, next);
        } else if (c == '-' && stream + 1 < end && stream[1] == '|') {
            break;
        } else if (c == '(' || c == '+' || c == '-' || c == '*') {
            struct partial_operation op;
            op.type = c;
            if (c == '(') op.precedence = PRECEDENCE_GROUPING;
            if (c == '+' || c == '-') op.precedence = PRECEDENCE_ADDITIVE;
            if (c == '*') op.precedence = PRECEDENCE_MULTIPLICATIVE;
            stream++;

            if (op.precedence != PRECEDENCE_GROUPING) {
                while (arrlen(stack) > 0
                    && arrlast(stack).precedence <= op.precedence)
                {
                    /* emit instructions with earlier or equal precedence */
                    struct atom next;
                    next.type = (enum atom_type)arrpop(stack).type;
                    arrpush(body, next);
                }
            }
            arrpush(stack, op);
        } else if (c == ')') {
            stream++;

            while (arrlen(stack) > 0
                && arrlast(stack).precedence != PRECEDENCE_GROUPING)
            {
                /* emit instructions up until the opening paren */
                struct atom next;
                next.type = (enum atom_type)arrpop(stack).type;
                arrpush(body, next);
            }
            if (arrlen(stack) == 0) {
                fprintf(stderr, "Error: Unexpected close paren.\n");
                exit(EXIT_FAILURE);
            }
            enum operation_stack_type type = arrpop(stack).type;
            if (type != '(') {
                fprintf(stderr, "Error: Unexpected close paren.\n");
                exit(EXIT_FAILURE);
            }
        } else {
            break;
        }
    }

    while (arrlen(stack) > 0
        && arrlast(stack).precedence != PRECEDENCE_GROUPING)
    {
        /* emit instructions up until any unclosed grouping */
        struct atom next;
        next.type = (enum atom_type)arrpop(stack).type;
        arrpush(body, next);
    }
    if (arrlen(stack) > 0) {
        fprintf(stderr, "Error: There are unclosed parentheses.\n");
        exit(EXIT_FAILURE);
    }
    arrfree(stack);

    input->data = stream;
    input->size = end - stream;

    return (struct expr){variables, body};
}

/****************/
/* Verification */
/****************/

struct subexpr_result {
    bool is_poly;
    union {
        struct polynomial poly;
        struct monomial mono;
    };
};

struct polynomial expand_expression(struct expr expr) {
    int variable_count = arrlen(expr.variables);
    struct subexpr_result *poly_stack = NULL;
    int *mono_index_stack = NULL;
    for (int i = 0; i < arrlen(expr.body); i++) {
        struct atom *it = &expr.body[i];
        switch (it->type) {
          case ATOM_NUMERAL:
          {
            struct subexpr_result next;
            next.is_poly = false;
            next.mono.variable_count = variable_count;
            next.mono.coefficient = it->value;
            next.mono.term_indices = calloc(variable_count, sizeof(int));
            arrpush(poly_stack, next);
            break;
          }
          case ATOM_VAR:
          {
            struct subexpr_result next;
            next.is_poly = false;
            next.mono.variable_count = variable_count;
            next.mono.coefficient = INT(1);
            next.mono.term_indices = calloc(variable_count, sizeof(int));
            next.mono.term_indices[it->id] = 1;
            arrpush(poly_stack, next);
            break;
          }
          case ATOM_PLUS:
          case ATOM_MINUS:
          {
            struct subexpr_result y = arrpop(poly_stack);
            struct subexpr_result x = arrpop(poly_stack);
            if (it->type == ATOM_MINUS) {
                if (y.is_poly) {
                    rational *coefficients = y.poly.coefficients;
                    for (int j = 0; j < arrlen(coefficients); j++) {
                        coefficients[j].numerator *= -1;
                    }
                } else {
                    y.mono.coefficient.numerator *= -1;
                }
            }
            if (!x.is_poly && !y.is_poly) {
                struct polynomial poly = {.variables = expr.variables};
                poly_add_mono(&poly, x.mono);
                poly_add_mono(&poly, y.mono);

                struct subexpr_result sum;
                sum.is_poly = true;
                sum.poly = poly;
                arrpush(poly_stack, sum);
            } else if (x.is_poly && y.is_poly) {
                poly_add(&x.poly, &y.poly);
                poly_free_terms(&y.poly);
                arrpush(poly_stack, x);
            } else if (x.is_poly) {
                poly_add_mono(&x.poly, y.mono);
                arrpush(poly_stack, x);
            } else {
                poly_add_mono(&y.poly, x.mono);
                arrpush(poly_stack, y);
            }
            break;
          }
          case ATOM_TIMES:
          {
            struct subexpr_result y = arrpop(poly_stack);
            struct subexpr_result x = arrpop(poly_stack);
            if (!x.is_poly && !y.is_poly) {
                struct polynomial poly = {.variables = expr.variables};
                mono_mul(&x.mono, y.mono);
                arrpush(poly_stack, x);
            } else if (x.is_poly && y.is_poly) {
                struct polynomial poly = {.variables = expr.variables};
                poly_mul_add(&poly, &x.poly, &y.poly);

                poly_free_terms(&x.poly);
                poly_free_terms(&y.poly);

                struct subexpr_result prod;
                prod.is_poly = true;
                prod.poly = poly;
                arrpush(poly_stack, prod);
            } else if (x.is_poly) {
                poly_mul_mono(&x.poly, y.mono);
                arrpush(poly_stack, x);
            } else {
                poly_mul_mono(&y.poly, x.mono);
                arrpush(poly_stack, y);
            }
            break;
          }
        }
    }
    if (arrlen(poly_stack) != 1) {
        fprintf(stderr, "Error: Evaluated expression but didn't get exactly one polynomial result.\n");
        exit(EXIT_FAILURE);
    }

    struct subexpr_result top = poly_stack[0];
    struct polynomial result = {.variables = expr.variables};
    if (top.is_poly) result = top.poly;
    else poly_add_mono(&result, top.mono);

    arrfree(poly_stack);
    arrfree(mono_index_stack);

    return result;
}

bool check_subexpression(struct atom *x, int x_i, struct atom *y, int *i_out) {
    /* Count the balance of branches to leaves, when we run out of leaves, we
       have parsed the whole subexpression. */
    int leaves_remaining = 1;
    int y_i = arrlen(y) - 1;
    while (leaves_remaining > 0 && x_i >= 0 && y_i >= 0) {
        struct atom it_x = x[x_i];
        struct atom it_y = y[y_i];
        if (!atom_eq(x[x_i], y[y_i])) return false;
        x_i--;
        y_i--;
        enum atom_type ty = it_x.type;
        if (ty == ATOM_PLUS || ty == ATOM_MINUS || ty == ATOM_TIMES) {
            leaves_remaining++;
        } else {
            leaves_remaining--;
        }
    }
    if (leaves_remaining > 0) {
        fprintf(stderr, "Error: Reached end of expression before reaching the "
            "end of any valid subexpression.\n");
        exit(EXIT_FAILURE);
    }
    if (y_i >= 0) {
        fprintf(stderr, "Error: Tried to compare to an expression with "
            "multiple values?\n");
        exit(EXIT_FAILURE);
    }
    if (i_out) *i_out = x_i;
    return true;
}

bool expr_eq(struct atom *x, struct atom *y) {
    int x_i = arrlen(x) - 1;
    bool success = check_subexpression(x, x_i, y, &x_i);
    if (success && x_i >= 0) {
        fprintf(stderr, "Error: Tried to compare an expression with "
            "multiple values?\n");
        exit(EXIT_FAILURE);
    }
    return success;
}

struct equation {
    struct expr lhs;
    struct expr rhs;
};

bool verify_substitution(struct equation goal, struct equation identity) {
    struct atom *lhs = goal.lhs.body;
    struct atom *rhs = goal.rhs.body;
    int l_i = arrlen(lhs) - 1;
    int r_i = arrlen(rhs) - 1;
    int *l_stack = NULL;
    int *r_stack = NULL;
    int *args_remaining = NULL;

    while (l_i >= 0 && r_i >= 0) {
        struct atom lx = lhs[l_i];
        struct atom rx = rhs[r_i];
        if (atom_eq(lx, rx)) {
            enum atom_type ty = lx.type;
            if (ty == ATOM_PLUS || ty == ATOM_MINUS || ty == ATOM_TIMES) {
                arrpush(l_stack, l_i);
                arrpush(r_stack, r_i);
                arrpush(args_remaining, 2);
            } else {
                while (arrlen(args_remaining) > 0 && arrlast(args_remaining) == 1) {
                    arrpop(l_stack);
                    arrpop(r_stack);
                    arrpop(args_remaining);
                }
                if (arrlen(args_remaining) == 0) {
                    arrfree(l_stack);
                    arrfree(r_stack);
                    arrfree(args_remaining);
                    return true;
                }
                arrlast(args_remaining) -= 1;
            }
            l_i -= 1;
            r_i -= 1;
        } else {
            while (true) {
                int l_out;
                int r_out;
                bool matches =
                    check_subexpression(lhs, l_i, identity.lhs.body, &l_out)
                    && check_subexpression(rhs, r_i, identity.rhs.body, &r_out);
                if (!matches) {
                    matches =
                        check_subexpression(lhs, l_i, identity.rhs.body, &l_out)
                        && check_subexpression(rhs, r_i, identity.lhs.body, &r_out);
                }
                if (matches) {
                    while (arrlen(args_remaining) > 0 && arrlast(args_remaining) == 1) {
                        arrpop(l_stack);
                        arrpop(r_stack);
                        arrpop(args_remaining);
                    }
                    if (arrlen(args_remaining) == 0) {
                        arrfree(l_stack);
                        arrfree(r_stack);
                        arrfree(args_remaining);
                        return true;
                    }
                    arrlast(args_remaining) -= 1;
                    l_i = l_out;
                    r_i = r_out;
                    break;
                }
                /* else */
                if (arrlen(args_remaining) == 0) {
                    arrfree(l_stack);
                    arrfree(r_stack);
                    arrfree(args_remaining);
                    return false;
                }
                l_i = arrpop(l_stack);
                r_i = arrpop(r_stack);
                arrpop(args_remaining);
            }
        }
    }
    fprintf(stderr, "Error: Reached end of expression before reaching the end "
        "of some subexpressions.\n");
    exit(EXIT_FAILURE);
}

bool verify_manipulation(struct equation *p) {
    struct polynomial lhs_poly = expand_expression(p->lhs);
    struct polynomial rhs_poly = expand_expression(p->rhs);

    for (int i = 0; i < arrlen(rhs_poly.coefficients); i++) {
        rhs_poly.coefficients[i].numerator *= -1;
    }
    poly_add(&lhs_poly, &rhs_poly);

    bool equal = true;
    for (int i = 0; i < arrlen(lhs_poly.coefficients); i++) {
        if (lhs_poly.coefficients[i].numerator != 0) {
            equal = false;
            break;
        }
    }
    poly_free_terms(&lhs_poly);
    /* TODO store rhs_poly, in case it is about to be used again in a chained
       equality proof. */
    poly_free_terms(&rhs_poly);
    return equal;
}

/************/
/* Theorems */
/************/

void parse_varnames(str *input, str **varnames) {
    while (true) {
        while (input->size > 0 && IS_WHITESPACE(*input->data)) {
            input->data++;
            input->size--;
        }
        str token;
        token.data = input->data;
        token.size = get_alphanum_prefix(*input);
        if (token.size == 0) {
            fprintf(stderr, "Error: Expected variable name, got "
                "'%c'.\n", input->data[0]);
            exit(EXIT_FAILURE);
        }
        input->data += token.size;
        input->size -= token.size;
        arrpush(*varnames, token);

        while (input->size > 0 && IS_WHITESPACE(*input->data)) {
            input->data++;
            input->size--;
        }
        if (input->size == 0) {
            fprintf(stderr, "Error: Reached end of file.\n");
            exit(EXIT_FAILURE);
        }
        if (input->data[0] != ',') break;
        input->data++;
        input->size--;
    }
}

struct items {
    str *varnames;
    str *identity_names;
    struct equation *identities;
};

struct equation parse_equation(str *input, struct items *items) {
    struct equation result = {0};

    result.lhs = parse_expression(input, items->varnames);
    if (input->size == 0) {
        fprintf(stderr, "Error: Expected the rest of a theorem "
            "signature, but got to the end of the file.\n");
        exit(EXIT_FAILURE);
    }
    if (input->data[0] != '=') {
        fprintf(stderr, "Error: Hit unexpected character '%c' after "
            "parsing an expression.\n", input->data[0]);
        exit(EXIT_FAILURE);
    }
    input->data++;
    input->size--;

    result.rhs = parse_expression(input, items->varnames);

    return result;
}

void parse_proof(str *input, struct items *items, struct equation goal) {
    struct equation p = {0};
    p.lhs = parse_expression(input, items->varnames);

    if (input->size == 0) {
        fprintf(stderr, "Error: Expected '=', but got to the end of the "
            "file.\n");
        exit(EXIT_FAILURE);
    }
    if (input->data[0] != '=') {
        fprintf(stderr, "Error: Expected '=', but got '%c'.\n",
            input->data[0]);
        exit(EXIT_FAILURE);
    }
    input->data++;
    input->size--;

    bool valid = true;
    bool lhs_match = expr_eq(p.lhs.body, goal.lhs.body);

    while (true) {
        p.rhs = parse_expression(input, items->varnames);

        if (input->size == 0) {
            fprintf(stderr, "Error: Expected '-|' or '=' or '.', but got to "
                "the end of the file.\n");
            exit(EXIT_FAILURE);
        }

        if (input->size >= 2 && input->data[0] == '-' && input->data[1] == '|') {
            input->data += 2;
            input->size -= 2;

            while (input->size > 0 && IS_WHITESPACE(*input->data)) {
                input->data++;
                input->size--;
            }
            str token;
            token.data = input->data;
            token.size = get_alphanum_prefix(*input);
            if (token.size == 0) {
                fprintf(stderr, "Error: Expected identity name, got '%c'.\n",
                    input->data[0]);
                exit(EXIT_FAILURE);
            }

            int identity_id = lookup_name(items->identity_names, token);
            if (identity_id == -1) {
                fprintf(stderr, "Error: Unknown theorem \"");
                fputstr(token, stderr);
                fprintf(stderr, "\".\n");
                exit(EXIT_FAILURE);
            }
            input->data += token.size;
            input->size -= token.size;

            bool match = verify_substitution(p, items->identities[identity_id]);
            if (!match) {
                printf("Subsitution step was not successful.\n");
                valid = false;
            }

            while (input->size > 0 && IS_WHITESPACE(*input->data)) {
                input->data++;
                input->size--;
            }

            if (input->size == 0) {
                fprintf(stderr, "Error: Expected '=' or '.', but got to "
                    "the end of the file.\n");
                exit(EXIT_FAILURE);
            }
            if (input->data[0] != '=' && input->data[0] != '.') {
                fprintf(stderr, "Error: Expected '=' or '.', but got '%c'.\n",
                    input->data[0]);
                exit(EXIT_FAILURE);
            }
        } else if (input->data[0] == '.' || input->data[0] == '=') {
            bool equal = verify_manipulation(&p);
            if (!equal) {
                printf("Polynomial manipulation step was not successful.\n");
                valid = false;
            }
        } else {
            fprintf(stderr, "Error: Expected '-|' or '=' or '.', but got "
                "'%c'.\n", input->data[0]);
            exit(EXIT_FAILURE);
        }

        if (input->data[0] == '.') {
            input->data++;
            input->size--;
            break;
        }

        /* input->data[0] is '=' */
        input->data++;
        input->size--;

        arrfree(p.lhs.body);
        p.lhs = p.rhs;
        p.rhs = (struct expr){0};

        /* continue */
    }

    bool rhs_match = expr_eq(p.rhs.body, goal.rhs.body);

    if (!lhs_match) printf("The starting point of the proof did not agree "
            "with the left hand side of the goal.\n");
    if (!rhs_match) printf("The end point of the proof did not agree with the "
            "right hand side of the goal.\n");

    if (lhs_match && rhs_match && valid) printf("Proof was valid.\n");
    else printf("Proof was invalid.\n");

    arrfree(p.lhs.body);
    arrfree(p.rhs.body);
}

void parse_theorem(str *input_ptr, struct items *items) {
    str input = *input_ptr;

    while (input.size > 0 && IS_WHITESPACE(*input.data)) {
        input.data++;
        input.size--;
    }

    str token;
    token.data = input.data;
    token.size = get_alphanum_prefix(input);
    if (token.size == 0) {
        fprintf(stderr, "Error: Expected theorem name, got '%c'.\n",
            *input.data);
        exit(EXIT_FAILURE);
    }
    input.data += token.size;
    input.size -= token.size;
    /* Discard the theorem name, for now. */
    if (input.size == 0) {
        fprintf(stderr, "Error: Expected the theorem signature, but "
            "got to the end of the file.\n");
        exit(EXIT_FAILURE);
    }
    if (input.data[0] != ':') {
        fprintf(stderr, "Error: Expected ':', but got '%c'.\n", *input.data);
        exit(EXIT_FAILURE);
    }
    input.data++;
    input.size--;

    while (input.size > 0 && IS_WHITESPACE(*input.data)) {
        input.data++;
        input.size--;
    }
    token.data = input.data;
    token.size = get_alphanum_prefix(input);
    int global_var_count = arrlen(items->varnames);
    if (str_eq(token, CSTR("forall"))) {
        input.data += token.size;
        input.size -= token.size;

        parse_varnames(&input, &items->varnames);
        if (input.data[0] != ':') {
            fprintf(stderr, "Error: Expected ':' or ',', got '%c'.\n",
                input.data[0]);
            exit(EXIT_FAILURE);
        }
        input.data++;
        input.size--;

        while (input.size > 0 && IS_WHITESPACE(*input.data)) {
            input.data++;
            input.size--;
        }
        token.data = input.data;
        token.size = get_alphanum_prefix(input);
        if (token.size == 0) {
            fprintf(stderr, "Error: Expected variable type, got '%c'.\n",
                input.data[0]);
            exit(EXIT_FAILURE);
        }
        if (!str_eq(token, CSTR("Number"))) {
            fprintf(stderr, "Error: Currently the only data type is "
                "\"Number\".\n");
            exit(EXIT_FAILURE);
        }
        input.data += token.size;
        input.size -= token.size;

        while (input.size > 0 && IS_WHITESPACE(*input.data)) {
            input.data++;
            input.size--;
        }
        if (input.size == 0) {
            fprintf(stderr, "Error: Reached end of file.\n");
            exit(EXIT_FAILURE);
        }
        if (input.data[0] != ',') {
            fprintf(stderr, "Error: Expected ',', got '%c'.\n", input.data[0]);
        }
        input.data++;
        input.size--;
    }

    struct equation p = parse_equation(&input, items);

    if (input.size == 0) {
        fprintf(stderr, "Error: Expected ',' or '-|' or '.', but got to the "
            "end of the file.\n");
        exit(EXIT_FAILURE);
    }
    if (input.data[0] == '.') {
        input.data++;
        input.size--;

        bool equal = verify_manipulation(&p);

        if (equal) printf("These are equal.\n");
        else printf("These are not equal.\n");
    } else if (input.size >= 2
        && input.data[0] == '-' && input.data[1] == '|')
    {
        input.data += 2;
        input.size -= 2;

        while (input.size > 0 && IS_WHITESPACE(*input.data)) {
            input.data++;
            input.size--;
        }
        token.data = input.data;
        token.size = get_alphanum_prefix(input);
        if (token.size == 0) {
            fprintf(stderr, "Error: Expected identity name, got '%c'.\n",
                input.data[0]);
            exit(EXIT_FAILURE);
        }

        int identity_id = lookup_name(items->identity_names, token);
        if (identity_id == -1) {
            fprintf(stderr, "Error: Unknown theorem \"");
            fputstr(token, stderr);
            fprintf(stderr, "\".\n");
            exit(EXIT_FAILURE);
        }
        input.data += token.size;
        input.size -= token.size;

        bool match = verify_substitution(p, items->identities[identity_id]);
        if (match) {
            printf("Substitution was successful.\n");
        } else {
            printf("Substitution was not successful.\n");
        }

        while (input.size > 0 && IS_WHITESPACE(*input.data)) {
            input.data++;
            input.size--;
        }

        if (input.size == 0) {
            fprintf(stderr, "Error: Expected theorem end, but got to "
                "the end of the file.\n");
            exit(EXIT_FAILURE);
        }
        if (input.data[0] != '.') {
            fprintf(stderr, "Error: Expected '.', but got '%c'.\n",
                input.data[0]);
            exit(EXIT_FAILURE);
        }
        input.data++;
        input.size--;
    } else if (input.data[0] == ',') {
        input.data++;
        input.size--;

        while (input.size > 0 && IS_WHITESPACE(*input.data)) {
            input.data++;
            input.size--;
        }

        token.data = input.data;
        token.size = get_alphanum_prefix(input);
        if (!str_eq(token, CSTR("Proof"))) {
            if (input.size == 0) {
                fprintf(stderr, "Error: Expected \"Proof:\", "
                    "got end of file.\n");
            } else if (token.size == 0) {
                fprintf(stderr, "Error: Expected "
                    "\"Proof:\", got '%c'.\n", input.data[0]);
            } else {
                fprintf(stderr, "Error: Expected \"Proof:\", got \"");
                fputstr(token, stderr);
                fprintf(stderr, "\".\n");
            }
            exit(EXIT_FAILURE);
        }
        input.data += token.size;
        input.size -= token.size;

        while (input.size > 0 && IS_WHITESPACE(*input.data)) {
            input.data++;
            input.size--;
        }
        if (input.size == 0) {
            fprintf(stderr, "Error: Expected ':', but got to the end of the "
                "file.\n");
            exit(EXIT_FAILURE);
        }
        if (input.data[0] != ':') {
            fprintf(stderr, "Error: Expected ':', but got '%c'.\n",
                input.data[0]);
            exit(EXIT_FAILURE);
        }
        input.data++;
        input.size--;

        parse_proof(&input, items, p);
    } else if (input.size == 0) {
        exit(EXIT_FAILURE);
    } else {
        fprintf(stderr, "Error: Expected ',' or '-|' or '.', but got '%c'.\n", input.data[0]);
        exit(EXIT_FAILURE);
    }

    arrfree(p.lhs.body);
    arrfree(p.rhs.body);

    *input_ptr = input;
    arrsetlen(items->varnames, global_var_count);
}

void parse_postulate(str *input, struct items *items) {
    str *varnames = NULL;
    parse_varnames(input, &varnames);
    if (input->data[0] != ':') {
        fprintf(stderr, "Error: Expected ':' or ',', got '%c'.\n",
            input->data[0]);
        exit(EXIT_FAILURE);
    }
    input->data++;
    input->size--;

    while (input->size > 0 && IS_WHITESPACE(*input->data)) {
        input->data++;
        input->size--;
    }
    str token;
    token.data = input->data;
    token.size = get_alphanum_prefix(*input);
    if (token.size == 0) {
        fprintf(stderr, "Error: Expected variable type, got '%c'.\n",
            input->data[0]);
        exit(EXIT_FAILURE);
    }

    if (str_eq(token, CSTR("Number"))) {
        input->data += token.size;
        input->size -= token.size;

        str *emplace = arraddnptr(items->varnames, arrlen(varnames));
        for (int i = 0; i < arrlen(varnames); i++) emplace[i] = varnames[i];
    } else {
        struct equation p = parse_equation(input, items);

        if (arrlen(varnames) != 1) {
            fprintf(stderr, "Error: Cannot multiple-declare proofs.\n");
            exit(EXIT_FAILURE);
        }

        arrpush(items->identity_names, varnames[0]);
        arrpush(items->identities, p);
    }

    arrfree(varnames);

    while (input->size > 0 && IS_WHITESPACE(*input->data)) {
        input->data++;
        input->size--;
    }
    if (input->size == 0) {
        fprintf(stderr, "Error: Reached end of file.\n");
        exit(EXIT_FAILURE);
    }
    if (input->data[0] != '.') {
        fprintf(stderr, "Error: Expected '.', got '%c'.\n", input->data[0]);
        exit(EXIT_FAILURE);
    }
    input->data++;
    input->size--;
}

/****************/
/* Input/Output */
/****************/

str read_file(char *path) {
    FILE *input = NULL;
    str contents;

    input = fopen(path, "r");
    if (!input) {
        perror("error opening file");
    }

    fseek(input, 0L, SEEK_END);
    contents.size = ftell(input);
    contents.data = malloc(contents.size + 1);

    rewind(input);
    fread(contents.data, 1, contents.size, input);
    contents.data[contents.size] = '\0';

    fclose(input);

    return contents;
}

int main(int argc, char **argv) {
    if (argc == 1) {
        fprintf(stderr, "Error: Expected input file.\n");
        exit(EXIT_FAILURE);
    }
    if (argc > 2) {
        fprintf(stderr, "Error: Too many arguments.\n");
        exit(EXIT_FAILURE);
    }

    str input = read_file(argv[1]);

    struct items items = {0};

    while (input.size != 0) {
        while (input.size > 0 && IS_WHITESPACE(*input.data)) {
            input.data++;
            input.size--;
        }

        if (input.size == 0) break;

        str token;
        token.data = input.data;
        token.size = get_alphanum_prefix(input);
        input.data += token.size;
        input.size -= token.size;
        if (str_eq(token, CSTR("Theorem"))) {
            parse_theorem(&input, &items);
        } else if (str_eq(token, CSTR("Postulate"))) {
            parse_postulate(&input, &items);
        } else if (token.size == 0) {
            fprintf(stderr, "Error: Unexpected character \"%c\", expected "
                "\"Theorem\", or \"Postulate\".\n", input.data[0]);
            exit(EXIT_FAILURE);
        } else {
            fprintf(stderr, "Error: Unknown keyword \"");
            fputstr(token, stderr);
            fprintf(stderr, "\", expected \"Theorem\", or \"Postulate\".\n");
            exit(EXIT_FAILURE);
        }
    }
}

