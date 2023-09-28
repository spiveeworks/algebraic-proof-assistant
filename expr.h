#ifndef APA_EXPR_H
#define APA_EXPR_H

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "buffer.h"

/* TODO: Move str to another file? */
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

/* TODO: Move shared buffer to another file? */
struct shared_buffer_header {
    int reference_count;
    size_t elem_count;
    size_t elem_capacity;
};

void shared_buffer_make_mut(
    struct shared_buffer_header **ptr_out,
    size_t size,
    size_t *copied_count_out
) {
    struct shared_buffer_header *ptr = *ptr_out;
    if (ptr && ptr->reference_count > 1) {
        size_t count = ptr->elem_count;
        size_t cap = count;
        if (cap < 16) cap = 16;
        size_t new_size = sizeof(struct shared_buffer_header) + size * cap;
        struct shared_buffer_header *new_ptr = malloc(new_size);
        new_ptr->reference_count = 1;
        new_ptr->elem_count = count;
        new_ptr->elem_capacity = cap;

        ptr->reference_count -= 1;

        memcpy(&new_ptr[1], &ptr[1], size * count);
        *ptr_out = new_ptr;
        if (copied_count_out) *copied_count_out = count;
    }
    /* else we already own it, or it is null so there's nothing to own. */
}

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
        /* Similar to make_mut, but with a custom capacity. */
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

struct destroy_expr_frame {
    struct expr *it;
    size_t lambda_intros_destroyed;

    size_t args_destroyed;
};

struct destroy_expr_stack {
    struct destroy_expr_frame *it;
    size_t count;
    size_t capacity;
};

void copy_expr(struct expr *out, struct expr *in) {
    if (in->lambda_intro_types) {
        in->lambda_intro_types->reference_count += 1;
    }
    if (in->arg_buffer) {
        in->arg_buffer->reference_count += 1;
    }
    if (out) *out = *in;
}

void expr_buffer_make_mut(struct shared_buffer_header **ptr_out) {
    size_t copied_count = 0;
    shared_buffer_make_mut(
        ptr_out,
        sizeof(struct expr),
        &copied_count
    );

    if (copied_count > 0) {
        struct expr *copied_vals =
            (struct expr*)&(*ptr_out)[1];
        for (int i = 0; i < copied_count; i++) {
            copy_expr(NULL, &copied_vals[i]);
        }
    }
}

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
            copy_expr(NULL, &copied_vals[i]);
        }
    }

    return result;
}

struct parameter_spec {
    struct str name;
    struct expr type;
};

void parameter_spec_buffer_make_mut(struct shared_buffer_header **ptr_out) {
    size_t copied_count = 0;
    shared_buffer_make_mut(
        ptr_out,
        sizeof(struct parameter_spec),
        &copied_count
    );

    if (copied_count > 0) {
        struct parameter_spec *copied_vals =
            (struct parameter_spec*)&(*ptr_out)[1];
        for (int i = 0; i < copied_count; i++) {
            copy_expr(NULL, &copied_vals[i].type);
        }
    }
}

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
            copy_expr(NULL, &copied_vals[i].type);
        }
    }

    return result;
}

struct parameter_spec *parameter_spec_split_destructive(
    struct shared_buffer_header **ptr_out,
    size_t n
) {
    if (n == 0) return NULL;

    parameter_spec_buffer_make_mut(ptr_out);
    struct shared_buffer_header *ptr = *ptr_out;

    struct parameter_spec *new_specs = malloc(n * sizeof(struct parameter_spec));
    struct parameter_spec *old_specs = (struct parameter_spec*)&ptr[1];
    memcpy(new_specs, old_specs, n * sizeof(struct parameter_spec));
    size_t new_count = ptr->elem_count - n;
    ptr->elem_count = new_count;
    memmove(old_specs, &old_specs[n], new_count * sizeof(struct parameter_spec));

    return new_specs;
}

void destroy_expr(struct expr *it) {
    if (it->lambda_intro_types) {
        it->lambda_intro_types->reference_count -= 1;
        if (it->lambda_intro_types->reference_count == 0) {
            size_t count = it->lambda_intro_types->elem_count;
            printf("Destroying lambda specs. (%llu params)\n", count);
            struct parameter_spec *specs =
                (struct parameter_spec*)&it->lambda_intro_types[1];
            for (int i = 0; i < count; i++) {
                destroy_expr(&specs[i].type);
            }
            free(it->lambda_intro_types);
        }
    }
    if (it->arg_buffer) {
        it->arg_buffer->reference_count -= 1;
        if (it->arg_buffer->reference_count == 0) {
            size_t count = it->arg_buffer->elem_count;
            printf("Destroying arg list. (%llu args)\n", count);
            struct expr *exprs =
                (struct expr*)&it->arg_buffer[1];
            for (int i = 0; i < count; i++) {
                destroy_expr(&exprs[i]);
            }
            free(it->arg_buffer);
        }
    }
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

void name_buffer_push(struct name_buffer *names, struct str name) {
    struct name_tracker *new_name = buffer_addn(*names, 1);
    new_name->name = name;
    /* TODO: name mangling */
}

struct pretty_print_state {
    int indentation;
    int squeeze_width;
    struct name_buffer names;
};

enum print_pos {
    PRINT_NAKED,
    PRINT_PARAM_SPEC,
    PRINT_ARG_SUBEXPR
};

void pretty_print_expr_rec(
    struct expr *it,
    enum print_pos print_pos,
    struct pretty_print_state *state
) {
    bool print_parens = false;
    switch (print_pos) {
        case PRINT_NAKED:
            print_parens = false;
            break;
        case PRINT_PARAM_SPEC:
            /* Nested arrows are confusing, but type families are fine. */
            print_parens = it->lambda_intro_count > 0
                || it->pi_intro_count > 0;
            break;
        case PRINT_ARG_SUBEXPR:
            /* Already in an arg, args need to be wrapped further. */
            print_parens = it->lambda_intro_count > 0
                || it->pi_intro_count > 0
                || it->arg_count > 0;
            break;
    }

    if (print_parens) printf("(");

    if (it->lambda_intro_count > 0) {
        struct parameter_spec *specs =
            (struct parameter_spec*)&it->lambda_intro_types[1];
        for (int i = 0; i < it->lambda_intro_count; i++) {
            struct parameter_spec *spec = &specs[i];

            printf("\\");
            put_str(spec->name);
            printf(": ");
            pretty_print_expr_rec(&spec->type, PRINT_PARAM_SPEC, state);

            printf(" -> ");

            name_buffer_push(&state->names, spec->name);
        }
    }

    if (it->pi_intro_count > 0) {
        struct parameter_spec *specs =
            (struct parameter_spec*)&it->lambda_intro_types[1];
        specs += it->lambda_intro_count;
        for (int i = 0; i < it->pi_intro_count; i++) {
            struct parameter_spec *spec = &specs[i];

            if (spec->name.data) {
                put_str(spec->name);
                printf(": ");
            }
            pretty_print_expr_rec(&spec->type, PRINT_PARAM_SPEC, state);

            printf(" -> ");

            name_buffer_push(&state->names, spec->name);
        }

    }

    switch (it->head_type) {
        case EXPR_NULL:
            printf("?");
            break;
        case EXPR_APPLY_LAMBDA:
            /* Do nothing. */
            break;
        case EXPR_VAR:
            if (it->head_var_index < state->names.count) {
                put_str(state->names.data[it->head_var_index].name);
            } else {
                printf("?v%d", it->head_var_index);
            }
            break;
        case EXPR_GLOBAL:
            printf("global");
            /* TODO */
            break;
        case EXPR_SORT:
            printf("Type");
            break;
    }

    struct expr *args = (struct expr*)&it->arg_buffer[1];
    for (int i = 0; i < it->arg_count; i++) {
        struct expr *arg = &args[i];
        if (i > 0 || it->head_type != EXPR_APPLY_LAMBDA) printf(" ");
        pretty_print_expr_rec(arg, PRINT_ARG_SUBEXPR, state);
    }

    if (print_parens) printf(")");


    for (int i = 0; i < it->pi_intro_count; i++) buffer_pop(state->names);
    for (int i = 0; i < it->lambda_intro_count; i++) buffer_pop(state->names);
}

void pretty_print_expr(struct expr *it) {
    struct pretty_print_state state = {0, 80};
    pretty_print_expr_rec(it, PRINT_NAKED, &state);
    buffer_free(state.names);
}

void pretty_print_expr_open(struct expr *it, struct name_buffer *names) {
    struct pretty_print_state state = {0, 80, *names};
    pretty_print_expr_rec(it, PRINT_NAKED, &state);
}

void deepen_expr_context(
    struct expr *it,
    size_t from_depth,
    size_t to_depth
) {
    /* TODO: short circuit this to avoid all the make_mut? */
    parameter_spec_buffer_make_mut(&it->lambda_intro_types);
    size_t intro_count = it->lambda_intro_count + it->pi_intro_count;
    struct parameter_spec *specs =
        (struct parameter_spec*)&it->lambda_intro_types[1];
    for (int i = 0; i < intro_count; i++) {
        struct parameter_spec *spec = &specs[i];
        deepen_expr_context(&spec->type, from_depth, to_depth);
    }

    if (it->head_type == EXPR_VAR) {
        if (it->head_var_index >= from_depth) {
            it->head_var_index += to_depth - from_depth;
        }
    }

    expr_buffer_make_mut(&it->arg_buffer);
    struct expr *args = (struct expr*)&it->arg_buffer[1];
    for (size_t i = 0; i < it->arg_count; i++) {
        deepen_expr_context(&args[i], from_depth, to_depth);
    }
}

bool expr_eq(struct expr *a, struct expr *b) {
    if (a->lambda_intro_count != b->lambda_intro_count) return false;
    if (a->pi_intro_count != b->pi_intro_count) return false;
    size_t intro_count = a->lambda_intro_count + a->pi_intro_count;
    struct parameter_spec *a_specs =
        (struct parameter_spec*)&a->lambda_intro_types[1];
    struct parameter_spec *b_specs =
        (struct parameter_spec*)&b->lambda_intro_types[1];
    for (int i = 0; i < intro_count; i++) {
        struct parameter_spec *a_spec = &a_specs[i];
        struct parameter_spec *b_spec = &b_specs[i];
        if (!expr_eq(&a_spec->type, &b_spec->type)) return false;
    }

    if (a->head_type != b->head_type) return false;

    if (a->head_type == EXPR_VAR || a->head_type == EXPR_GLOBAL) {
        if (a->head_var_index != b->head_var_index) return false;
    }
    /* else arity 0, heads are automatically equal. */

    if (a->arg_count != b->arg_count) return false;
    struct expr *a_args = (struct expr*)&a->arg_buffer[1];
    struct expr *b_args = (struct expr*)&b->arg_buffer[1];
    for (size_t i = 0; i < a->arg_count; i++) {
        if (!expr_eq(&a_args[i], &b_args[i])) return false;
    }

    return true;
}

bool expr_is_sort(struct expr *it) {
    if (it->lambda_intro_count != 0) return false;
    if (it->pi_intro_count != 0) return false;
    if (it->head_type != EXPR_SORT) return false;
    if (it->arg_count != 0) {
        fprintf(stderr, "Error: Universe 'Type' cannot be applied to arguments??.\n");
        exit(EXIT_FAILURE);
    }
    return true;
}

/* Useful for tracking contexts during expression type-checking. */
struct expr_buffer {
    struct expr *data;
    size_t count;
    size_t capacity;
};

#endif
