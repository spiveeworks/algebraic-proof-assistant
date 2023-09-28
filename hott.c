#include <stdbool.h>
#include <stdio.h>

#include "buffer.h"

struct str {
    char *data;
    int count;
};

struct str c_str(char *data) {
    struct str result = {data};
    result.count = strlen(data);
    return result;
}

void fput_str(struct str it, FILE *out) {
    fwrite(it.data, 1, it.count, out);
}

void put_str(struct str it) {
    fwrite(it.data, 1, it.count, stdout);
}

struct shared_buffer_header {
    int reference_count;
    size_t elem_count;
    size_t elem_capacity;
};

void *shared_buffer_addn(
    struct shared_buffer_header **ptr_out,
    size_t size,
    size_t n,
    size_t *copied_count_out
) {
    struct shared_buffer_header *ptr = *ptr_out;
    size_t prev_count = ptr ? ptr->elem_count : 0;
    size_t new_count = prev_count + n;

    size_t prev_cap = ptr ? ptr->elem_capacity : 0;
    size_t new_cap = prev_cap;
    if (new_cap < new_count) new_cap *= 2;
    if (new_cap < new_count) new_cap = new_count;
    if (new_cap < 16) new_cap = 16;
    size_t new_size = sizeof(struct shared_buffer_header) + size * new_cap;

    if (!ptr || ptr->reference_count > 1) {
        struct shared_buffer_header *new_ptr = malloc(new_size);
        new_ptr->reference_count = 1;
        new_ptr->elem_count = prev_count;
        new_ptr->elem_capacity = new_cap;
        if (ptr) {
            ptr->reference_count -= 1;
            memcpy(&new_ptr[1], &ptr[1], size * prev_count);
        }
        ptr = new_ptr;
        *ptr_out = new_ptr;
        if (copied_count_out) *copied_count_out = prev_count;
    } else if (new_count > prev_cap) {
        /* We own it uniquely, but it still isn't big enough. */
        ptr = realloc(ptr, new_size);
        ptr->elem_capacity = new_cap;
        *ptr_out = ptr;
        if (copied_count_out) *copied_count_out = 0;
    } else {
        /* We own it, it's big enough, just use it. */
        if (copied_count_out) *copied_count_out = 0;
    }

    ptr->elem_count = new_count;
    char *elements = (char*)&ptr[1];
    return elements + size * prev_count;
}

enum expr_head_type {
    EXPR_NULL,
    EXPR_APPLY_LAMBDA,
    EXPR_VAR,
    EXPR_GLOBAL,
    EXPR_SORT,
};

union expr_head_data {
    int var_index;
    int function_index;
};

/* Optimized for head normal form. Variables are directly introduced, the head
   is specified, and then all the args are put into a contiguous buffer. */
struct expr {
    /* lambdas, probably belong later, but conceptually come first */
    int lambda_intro_count;
    int pi_intro_count;
    /* shared buffer of (string, type) pairs, for type checking */
    struct shared_buffer_header *lambda_intro_types;

    /* head */
    enum expr_head_type head_type;
    int head_var_index;
    /* int tail_eval_len; cache this here? */

    int highest_variable_referenced; /* For clever short-circuiting. */
    /* shared buffer of expressions like this */
    int arg_count;
    struct shared_buffer_header *arg_buffer;
};

struct expr *expr_buffer_addn(
    struct shared_buffer_header **ptr_out,
    size_t n
) {
    size_t copied_count = 0;
    struct expr *result = shared_buffer_addn(
        ptr_out,
        sizeof(struct expr),
        n,
        &copied_count
    );

    if (copied_count > 0) {
        struct expr *copied_vals =
            (struct expr*)&(*ptr_out)[1];
        for (int i = 0; i < copied_count; i++) {
            struct expr *it = &copied_vals[i];
            if (it->lambda_intro_types) {
                it->lambda_intro_types->reference_count += 1;
            }
            if (it->arg_buffer) {
                it->arg_buffer->reference_count += 1;
            }
        }
    }

    return result;
}

struct parameter_spec {
    struct str name;
    struct expr type;
};

struct parameter_spec *parameter_spec_buffer_addn(
    struct shared_buffer_header **ptr_out,
    size_t n
) {
    size_t copied_count = 0;
    struct parameter_spec *result = shared_buffer_addn(
        ptr_out,
        sizeof(struct parameter_spec),
        n,
        &copied_count
    );

    if (copied_count > 0) {
        struct parameter_spec *copied_vals =
            (struct parameter_spec*)&(*ptr_out)[1];
        for (int i = 0; i < copied_count; i++) {
            struct expr *it = &copied_vals[i].type;
            if (it->lambda_intro_types) {
                it->lambda_intro_types->reference_count += 1;
            }
            if (it->arg_buffer) {
                it->arg_buffer->reference_count += 1;
            }
        }
    }

    return result;
}

struct global_definition {
    struct str name;
    /* int eval_var_count; is this a thing? */
    struct expr type;
    struct expr definition;
};

struct name_tracker {
    struct str name;
    /*int mangle_index; */
};

struct name_buffer {
    struct name_tracker *data;
    size_t count;
    size_t capacity;
};

struct pretty_print_state {
    int indentation;
    int squeeze_width;
    struct name_buffer names;
};

void pretty_print_expr_rec(
    struct expr *it,
    bool is_subexpr,
    struct pretty_print_state *state
) {
    bool print_parens = is_subexpr
        && (it->lambda_intro_count > 0
                || it->pi_intro_count > 0
                || it->arg_count > 0);

    if (print_parens) printf("(");

    if (it->lambda_intro_count > 0) {
        printf("\\");
        struct parameter_spec *specs =
            (struct parameter_spec*)&it->lambda_intro_types[1];
        for (int i = 0; i < it->lambda_intro_count; i++) {
            struct parameter_spec *spec = &specs[i];
            struct name_tracker *new_name = buffer_addn(state->names, 1);
            new_name->name = spec->name;
            /* TODO: name mangling */

            put_str(spec->name);
            printf(": ");
            pretty_print_expr_rec(&spec->type, false, state);

            if (i < it->lambda_intro_count - 1) printf(",");
            printf(" ");
        }

        printf("-> ");
    }

    if (it->pi_intro_count > 0) {
        printf("Pi ");
        struct parameter_spec *specs =
            (struct parameter_spec*)&it->lambda_intro_types[1];
        specs += it->lambda_intro_count;
        for (int i = 0; i < it->pi_intro_count; i++) {
            struct parameter_spec *spec = &specs[i];
            struct name_tracker *new_name = buffer_addn(state->names, 1);
            new_name->name = spec->name;
            /* TODO: name mangling */

            put_str(spec->name);
            printf(": ");
            pretty_print_expr_rec(&spec->type, false, state);

            if (i < it->pi_intro_count - 1) printf(",");
            printf(" ");
        }

        printf("-> ");
    }

    switch (it->head_type) {
        case EXPR_NULL:
        {
            printf("?");
            break;
        }
        case EXPR_APPLY_LAMBDA:
        {
            /* Do nothing. */
            break;
        }
        case EXPR_VAR:
        {
            put_str(state->names.data[it->head_var_index].name);
            break;
        }
        case EXPR_GLOBAL:
        {
            printf("global");
            /* TODO */
            break;
        }
        case EXPR_SORT:
        {
            printf("Type");
            break;
        }
    }

    struct expr *args = (struct expr*)&it->arg_buffer[1];
    for (int i = 0; i < it->arg_count; i++) {
        struct expr *arg = &args[i];
        if (i > 0 || it->head_type != EXPR_APPLY_LAMBDA) printf(" ");
        pretty_print_expr_rec(arg, true, state);
    }

    if (print_parens) printf(")");


    for (int i = 0; i < it->pi_intro_count; i++) buffer_pop(state->names);
    for (int i = 0; i < it->lambda_intro_count; i++) buffer_pop(state->names);
}

void pretty_print_expr(struct expr *it) {
    struct pretty_print_state state = {0, 80};
    pretty_print_expr_rec(it, false, &state);
    buffer_free(state.names);
}

int main(int arg_count, char **args) {
    struct expr it = {0};
    it.lambda_intro_count = 4;
    struct parameter_spec *specs = parameter_spec_buffer_addn(
        &it.lambda_intro_types,
        it.lambda_intro_count
    );
    specs[0].name = c_str("A");
    specs[0].type = (struct expr){.head_type = EXPR_SORT};
    specs[1].name = c_str("B");
    specs[1].type = (struct expr){0};
    {
        specs[1].type.pi_intro_count = 1;
        struct parameter_spec *b_specs = parameter_spec_buffer_addn(
            &specs[1].type.lambda_intro_types,
            1
        );
        b_specs[0].name = c_str("_");
        b_specs[0].type = (struct expr){.head_type = EXPR_VAR, .head_var_index = 0};

        specs[1].type.head_type = EXPR_SORT;
    }
    specs[2].name = c_str("f");
    specs[2].type = (struct expr){0};
    {
        specs[2].type.pi_intro_count = 1;
        struct parameter_spec *f_specs = parameter_spec_buffer_addn(
            &specs[2].type.lambda_intro_types,
            1
        );
        f_specs[0].name = c_str("x");
        f_specs[0].type = (struct expr){.head_type = EXPR_VAR, .head_var_index = 0};

        specs[2].type.head_type = EXPR_VAR;
        specs[2].type.head_var_index = 1;

        specs[2].type.arg_count = 1;
        struct expr *pi_output_args = expr_buffer_addn(
            &specs[2].type.arg_buffer,
            1
        );
        pi_output_args[0] = (struct expr){.head_type = EXPR_VAR, .head_var_index = 2};
    }
    specs[3].name = c_str("x");
    specs[3].type = (struct expr){.head_type = EXPR_VAR, .head_var_index = 0};
    it.head_type = EXPR_VAR;
    it.head_var_index = 2;

    it.arg_count = 1;
    struct expr *body_args = expr_buffer_addn(
        &it.arg_buffer,
        1
    );
    body_args[0] = (struct expr){.head_type = EXPR_VAR, .head_var_index = 3};

    printf("Expr: ");
    pretty_print_expr(&it);

    return 0;
}

