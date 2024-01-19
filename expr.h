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
    if (n == 0) {
        if (copied_count_out) *copied_count_out = 0;
        return NULL;
    }

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

    /* Equality stuff */
    /* (A: Type -> B: Type -> A -> B -> Type) */
    EXPR_EQUALS,
    /* (A: Type -> x: A -> x = x) */
    /* Where x = y means Equal A B x y. */
    EXPR_REFL,
    /* (A: Type -> B: Type -> x: A -> y: B -> x = y -> A = B) */
    EXPR_ENDPOINT_TYPES_EQ,
    /* (A: Type -> B: Type -> A = B -> A -> B) */
    EXPR_TRANSPORT,
    /* (A: Type -> B: Type -> p: A = B -> x: A -> x = transport p x) */
    EXPR_TRANSPORT_EQ,

    /* Path stuff */
    /* (A, B, C: Type -> x: A -> y: B -> z: C -> x = y -> y = z -> x = z) */
    EXPR_TRANS,
    /* (A, B: Type -> x: A -> y: B -> x = y -> y = x) */
    EXPR_SYM,

    /* (A1: Type -> B1: Type -> A2: Type -> B2: Type
           -> A1 = A2 -> B1 = B2 -> (A1 = B1) = (A2 = B2)) */
    EXPR_BOX,
    /* (A1: Type -> A2: Type -> B1: (A1 -> Type) -> B2: (A2 -> Type)
           -> p: A1 = A2 -> q: (x1: A1 -> x2: A2 -> transport p x1 = x2 -> B1 x1 = B2 x2)
           -> (x: A1 -> B1 x) = (x: A2 -> B2 x)) */
    EXPR_ARROW,

    /* Extensionality */
    /* Inverse of extensionality, takes a path between f and g, and 'applies'
       it to a path between x1 and x2.
       (A1: Type -> A2: Type -> B1: (A1 -> Type) -> B2: (A2 -> Type)
           -> f: (x: A1 -> B1 x) -> g: (x: A2 -> B2 x)
           -> f = g
           -> x1: A1 -> x2: A2
           -> x1 = x2 -> f x1 = g x2) */
    EXPR_APPLY_PATH,
    /* lets us define
       cong: (A: Type -> B: (A -> Type) -> f: (x: A -> B x)
           -> x: A -> y: A -> p: x = y -> f x = f y)
       cong A B f x y p = apply_path (refl f) p */

    /* Heterogeneous Extensionality */
    /* (A1: Type -> A2: Type -> B1: (A1 -> Type) -> B2: (A2 -> Type)
           -> p: A1 = A2
           -> f: (x: A1 -> B1 x) -> g: (x: A2 -> B2 x)
           -> (x1: A1 -> x2: A2 -> x1 = x2 -> f x1 = g x2)
           -> f = g) */
    EXPR_HETEXT,
    /* Then we can implement:
       mk_pathmap: (A: Type -> B: (A -> Type)
           -> f: (x: A -> B x) -> g: (x: A -> B x) -> p: (x: A -> f x = g x)
           -> (x1: A1 -> x2: A2 -> x1 = x2 -> f x1 = g x2))
       mk_pathmap A B f g p x1 x2 px = trans (p x1) (picong A B g x1 x2 px)

       ext: (A: Type -> B: (A -> Type) -> f: (x: A -> B x) -> g: (x: A -> B x)
           -> (x: A -> f x = g x) -> f = g)
       ext A B f g p = het_ext (refl A) f g (mk_pathmap A B f g p) */

    /* HIT stuff */
    /* (A: Type -> R: (A -> A -> Type) -> Type) */
    EXPR_QUOTIENT,
    /* (A: Type -> R: (A -> A -> Type) -> A -> Quotient A R) */
    EXPR_QUOTIENT_PROJECT,
    /* (A: Type -> R: (A -> A -> Type)
           -> x: A -> y: A -> R x y -> project A R x = project A R y) */
    EXPR_QUOTIENT_EDGE,
    /* (A: Type -> R: (A -> A -> Type) -> B: Type -> f: (A -> B)
           -> (x: A -> y: A -> R x y -> f x = f y) -> Quotient A R -> B) */
    EXPR_QUOTIENT_ELIM,
    /* Could make an actual dependently typed one, idk. */

    /* Univalence stuff? */
    /* (A: Type -> B: Type -> f: (A -> B) -> g: (B -> A)
           -> gof: (x: A -> g (f x) = x) -> fog: (y: B -> f (g y) = y)
           -> commute: (x: A -> cong f (gof x) = fog (f x)) -> A = B) */
    EXPR_UV,
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

/* Useful for tracking contexts during expression type-checking. */
struct expr_buffer {
    struct expr *data;
    size_t count;
    size_t capacity;
};

/* We don't actually use this yet? */
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
            printf("(null)");
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

        case EXPR_EQUALS:
            printf("Equal");
            break;
        case EXPR_REFL:
            printf("refl");
            break;
        case EXPR_APPLY_PATH:
            printf("apply_path");
            break;
        case EXPR_HETEXT:
            printf("het_ext");
            break;

        default:
            printf("?");
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

void destroy_expr(struct expr *it) {
#if 0
    if (it->lambda_intro_types
        && it->lambda_intro_types->reference_count == 1)
    {
        printf("Destroying lambda specs of: ");
        pretty_print_expr(it);
        printf("\n");
    }
    if (it->arg_buffer
        && it->arg_buffer->reference_count == 1)
    {
        printf("Destroying arg buffer of: ");
        pretty_print_expr(it);
        printf("\n");
    }
#endif
    if (it->lambda_intro_types) {
        it->lambda_intro_types->reference_count -= 1;
        if (it->lambda_intro_types->reference_count == 0) {
            size_t count = it->lambda_intro_types->elem_count;
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
            struct expr *exprs =
                (struct expr*)&it->arg_buffer[1];
            for (int i = 0; i < count; i++) {
                destroy_expr(&exprs[i]);
            }
            free(it->arg_buffer);
        }
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

void deepen_expr_context(
    struct expr *it,
    size_t from_depth,
    size_t to_depth
) {
    /* TODO: short circuit this to avoid some of the make_mut? */
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

/* Whenever we manipulate the head of an expression, we end up needing to
   place a new expression where the old head was. In doing so we then need to
   concatenate that expression with the old introduction rules, set its head
   and args to the head and args of the new expression, and while we
   are there we might as well allocate room for the old arguments as well. This
   function does those 3 things. `it` is modified and `to_add` is consumed in
   the process, but neither have to own their intro list/arg list uniquely;
   `it` must have no args, however. */
struct expr *concat_intros_set_head_alloc_args(
    struct expr *it,
    struct expr to_add,
    size_t additional_arg_count
) {
    if (it->arg_count != 0) {
        fprintf(stderr, "Error: Tried to concat intros to an expression that "
                "already had arguments?\n");
        exit(EXIT_FAILURE);
    }

    size_t intro_count = it->lambda_intro_count + it->pi_intro_count;
    size_t new_intro_count = to_add.lambda_intro_count + to_add.pi_intro_count;
    if (intro_count == 0 && additional_arg_count == 0) {
        /* Target is literally just a single variable. Use to_add as is. */
        *it = to_add;
    } else if ((it->pi_intro_count == 0 || to_add.lambda_intro_count == 0)
        && additional_arg_count == 0)
    {
        /* Lambda (Lambda Pi) or Lambda Pi (Pi), both just concatenate into a
           single intro list. */
        it->lambda_intro_count += to_add.lambda_intro_count;
        it->pi_intro_count += to_add.pi_intro_count;
        if (new_intro_count > 0) {
            struct parameter_spec *new_specs = parameter_spec_buffer_addn(
                &it->lambda_intro_types,
                new_intro_count
            );
            struct parameter_spec *arg_specs =
                (struct parameter_spec*)&to_add.lambda_intro_types[1];
            if (to_add.lambda_intro_types->reference_count > 1) {
                /* to_add.lambda_intro_types is shared, so copy out of it, and
                   then decrement the reference count, since we don't use
                   to_add other than to steal its arg_buffer. */
                for (int i = 0; i < new_intro_count; i++) {
                    new_specs[i].name = arg_specs[i].name;
                    copy_expr(&new_specs[i].type, &arg_specs[i].type);
                }
                to_add.lambda_intro_types->reference_count -= 1;
            } else {
                /* We own to_add.lambda_intro_types, so just move out of it,
                   and free the (now unused) buffer. */
                memcpy(
                    new_specs,
                    arg_specs,
                    new_intro_count * sizeof(struct parameter_spec)
                );
                free(to_add.lambda_intro_types);
            }
        }
        /* TODO: What if to_add.lambda_intro_types is allocated but unused?
           Should be impossible right now, since we don't slice into buffers
           but actually share them wholesale, but this may become a case to
           keep in mind. */

        it->head_type = to_add.head_type;
        it->head_var_index = to_add.head_var_index;

        it->arg_count = to_add.arg_count;
        it->arg_buffer = to_add.arg_buffer;

        /* We stole to_add.arg_buffer, and either freed or decremented
           to_add.lambda_intro_types, so to_add is already cleaned up, and
           should NOT be explicitly destroyed. */
    } else if (new_intro_count == 0) {
        /* Lambda Pi (f w x) y z, concatenate the args. */
        it->head_type = to_add.head_type;
        it->head_var_index = to_add.head_var_index;

        /* Steal the args, and then let later code addn to it as if it were an
           empty list. Funnily enough this ends up being equivalent code to the
           previous case, but it's easier to just write these four lines as a
           separate case, than mangle the previous case's condition more. */
        it->arg_count = to_add.arg_count;
        it->arg_buffer = to_add.arg_buffer;
        /* to_add.lambda_intro_types is empty, and to_add.arg_buffer has been
           moved out, so to_add is already cleaned up, and should NOT be
           explicitly destroyed. */
    } else {
        /* Most general case, Lambda Pi (Lambda Pi f w x) y z, write this as
           Lambda Pi APPLY (Lambda Pi f w x) y z */
        it->head_type = EXPR_APPLY_LAMBDA;

        it->arg_count = 1;
        /* Allocate enough for to_add, and additional_arg_count */
        struct expr *result_args = expr_buffer_addn(
            &it->arg_buffer,
            additional_arg_count + 1
        );
        /* Set the first arg to to_add, and return the rest as the allocation
           we promised. */
        result_args[0] = to_add;
        return &result_args[1];
    }

    /* In the EXPR_APPLY_LAMBDA case above we allocate room for to_add and
       additional_arg_count at the same time, but in all other cases we need to
       explicitly allocate the rest ourselves. */
    return expr_buffer_addn(&it->arg_buffer, additional_arg_count);
}

/* Fill in the top n variables of the current context. */
struct expr subst_exprs(
    size_t target_depth, /* arg_depth + the number of lambda/pi wrappers we
                            have traversed, so this is what we need to deepen
                            each arg to if we want to sub them into target. */
    struct expr *target,
    bool strip_intros, /* Skip arg_count many lambda introductions, to
                          implement beta reduction. */
    size_t arg_depth,
    size_t arg_count,
    struct expr *args
) {
    struct expr result = {0};

    /* Vacuous case, just increase the reference counts and return. */
    if (arg_count == 0) {
        copy_expr(&result, target);
        return result;
    }

    result.lambda_intro_count = target->lambda_intro_count;
    result.pi_intro_count = target->pi_intro_count;
    /* TODO: short circuit this to avoid some of the recursion? */
    size_t intro_count = target->lambda_intro_count + target->pi_intro_count;
    struct parameter_spec *specs =
        (struct parameter_spec*)&target->lambda_intro_types[1];
    if (strip_intros) {
        if (result.lambda_intro_count >= arg_count) {
            result.lambda_intro_count -= arg_count;
        } else if (result.lambda_intro_count != 0) {
            fprintf(stderr, "Error: Tried to apply arguments to eliminate "
                "%llu introduction rules, but there were only %d lambda "
                "introduction rules present?\n", arg_count,
                result.lambda_intro_count);
            exit(EXIT_FAILURE);
        } else if (result.pi_intro_count >= arg_count) {
            result.pi_intro_count -= arg_count;
        } else {
            fprintf(stderr, "Error: Tried to apply arguments to eliminate "
                "%llu introduction rules, but there were only %d pi "
                "introduction rules present?\n", arg_count,
                result.pi_intro_count);
            exit(EXIT_FAILURE);
        }

        intro_count -= arg_count;
        specs = &specs[arg_count];
    }
    struct parameter_spec *result_specs = parameter_spec_buffer_addn(
        &result.lambda_intro_types,
        intro_count
    );
    for (int i = 0; i < intro_count; i++) {
        struct parameter_spec *spec = &specs[i];
        struct expr new_type = subst_exprs(
            target_depth + i,
            &spec->type,
            false,
            arg_depth,
            arg_count,
            args
        );

        struct parameter_spec *result_spec = &result_specs[i];
        result_spec->name = spec->name;
        result_spec->type = new_type;
    }

    /* Check if head needs to be susbtituted, and maybe allocate
       result.arg_buffer at the same time. */
    struct expr *result_args = NULL;
    if (target->head_type == EXPR_VAR) {
        if (target->head_var_index >= arg_depth + arg_count) {
            /* This variable has been introduced by target itself, move it to
               the new context where some variables have been eliminated. */
            result.head_type = EXPR_VAR;
            result.head_var_index = target->head_var_index - arg_count;
        } else if (target->head_var_index >= arg_depth) {
            /* This variable is one of the ones being substituted, do it! */
            struct expr arg = {0};
            copy_expr(&arg, &args[target->head_var_index - arg_depth]);
            if (target_depth + intro_count != arg_depth) {
                deepen_expr_context(&arg, arg_depth, target_depth + intro_count);
            }

            /* Concatenate */
            result_args = concat_intros_set_head_alloc_args(
                &result,
                arg,
                target->arg_count
            );
        } else {
            /* This variable is from the common context of target and args,
               use it as-is. */
            result.head_type = EXPR_VAR;
            result.head_var_index = target->head_var_index;
        }
    } else {
        result.head_type = target->head_type;
        result.head_var_index = target->head_var_index;
    }

    if (!result_args) {
        /* result.arg_buffer hasn't been allocated yet, do it now. */
        result_args = expr_buffer_addn(&result.arg_buffer, target->arg_count);
    }
    result.arg_count += target->arg_count;
    struct expr *target_args = (struct expr*)&target->arg_buffer[1];
    for (size_t i = 0; i < target->arg_count; i++) {
        result_args[i] = subst_exprs(
            target_depth + intro_count,
            &target_args[i],
            false,
            arg_depth,
            arg_count,
            args
        );
    }

    return result;
}

/* Simple function that can be used to evaluate builtins. Lambda and pi intros
   are preserved, but the head and first n arguments are removed, and replaced
   with a new expression. The remaining arguments are kept. */
void replace_head(
    struct expr *target,
    size_t consume_arg_count,
    struct expr new_head
) {
    struct expr result = *target;
    result.arg_count = 0;
    result.arg_buffer = NULL;
    target->lambda_intro_count = 0;
    target->pi_intro_count = 0;
    target->lambda_intro_count = 0;
    target->lambda_intro_types = NULL;

    size_t remaining_arg_count = target->arg_count - consume_arg_count;
    if (remaining_arg_count < 0) remaining_arg_count = 0;
    struct expr *remaining_args_out = concat_intros_set_head_alloc_args(
        &result,
        new_head,
        remaining_arg_count
    );

    /* The only thing concat_intros_set_head_alloc_args doesn't do, is actually
       add the new args. This is because usually we are substituting variables
       into those args as well, but for built ins we don't need to do any such
       thing. So write the args now. */
    struct shared_buffer_header *ptr = target->arg_buffer;
    if (ptr) {
        struct expr *old_args = (struct expr*)&ptr[1];
        if (ptr->reference_count > 1) {
            for (int i = 0; i < remaining_arg_count; i++) {
                struct expr *out = &remaining_args_out[i];
                struct expr *arg = &old_args[i + consume_arg_count];
                copy_expr(out, arg);
            }
            ptr->reference_count -= 1;
        } else {
            for (int i = 0; i < consume_arg_count; i++) {
                destroy_expr(&old_args[i]);
            }
            memcpy(
                remaining_args_out,
                old_args + consume_arg_count,
                remaining_arg_count * sizeof(struct expr)
            );
            free(ptr);
        }
    }
    result.arg_count += remaining_arg_count;

    /* target->arg_buffer has been decremented or destroyed,
       target->lambda_intro_types has been moved into result, so target is now
       deinitialized, which means we can overwrite it. */
    *target = result;
}

const struct expr universe = {.head_type = EXPR_SORT};

void add_pi(struct expr *it, char *name, struct expr type) {
    it->pi_intro_count += 1;
    struct parameter_spec *spec = parameter_spec_buffer_addn(
        &it->lambda_intro_types,
        1
    );
    spec->name = c_str(name);
    spec->type = type;
}

void add_exp(struct expr *it, struct expr type) {
    it->pi_intro_count += 1;
    struct parameter_spec *spec = parameter_spec_buffer_addn(
        &it->lambda_intro_types,
        1
    );
    spec->name = (struct str){0};
    spec->type = type;
}

void apply_body(struct expr *it, struct expr arg) {
    it->arg_count += 1;
    struct expr *out = expr_buffer_addn(&it->arg_buffer, 1);
    *out = arg;
}

struct expr var(size_t index) {
    return (struct expr){.head_type = EXPR_VAR, .head_var_index = index};
}

struct expr pi(char *name, struct expr type, struct expr body) {
    add_pi(&body, name, type);
    return body;
}

struct expr exp(struct expr type, struct expr body) {
    add_exp(&body, type);
    return body;
}

static struct expr apply(struct expr f, struct expr x) {
    if (f.lambda_intro_count == 0 && f.pi_intro_count == 0) {
        apply_body(&f, x);
        return f;
    }
    /* else */
    struct expr result = {.head_type = EXPR_APPLY_LAMBDA};
    apply_body(&result, f);
    apply_body(&result, x);
    return result;
}

struct expr apply_path_type(size_t ctx_depth) {
    /* apply_path: (A1: Type -> A2: Type
                     -> B1: (A1 -> Type) -> B2: (A2 -> Type)
                     -> f: (x: A1 -> B1 x) -> g: (x: A2 -> B2 x)
                     -> f = g
                     -> x1: A1 -> x2: A2
                     -> x1 = x2 -> f x1 = g x2) */
    struct expr curr_type = {0};

    add_pi(&curr_type, "A1", universe);
    add_pi(&curr_type, "A2", universe);
    add_pi(&curr_type, "B1", exp(var(ctx_depth), universe));
    add_pi(&curr_type, "B2", exp(var(ctx_depth + 1), universe));

    {
        struct expr b1x = apply(var(ctx_depth + 2), var(ctx_depth + 4));
        add_pi(&curr_type, "f1", pi("x", var(ctx_depth), b1x));

        struct expr b2x = apply(var(ctx_depth + 3), var(ctx_depth + 5));
        add_pi(&curr_type, "f2", pi("x", var(ctx_depth + 1), b2x));
    }
    {
        struct expr feq = {0};
        feq.head_type = EXPR_EQUALS;
        struct expr b1x = apply(var(ctx_depth + 2), var(ctx_depth + 6));
        apply_body(&feq, pi("x", var(ctx_depth), b1x));

        struct expr b2x = apply(var(ctx_depth + 3), var(ctx_depth + 6));
        apply_body(&feq, pi("x", var(ctx_depth + 1), b2x));
        apply_body(&feq, var(ctx_depth + 4));
        apply_body(&feq, var(ctx_depth + 5));
        add_exp(&curr_type, feq);
    }
    add_pi(&curr_type, "x1", var(ctx_depth));
    add_pi(&curr_type, "x2", var(ctx_depth + 1));
    {
        struct expr xeq = {0};
        xeq.head_type = EXPR_EQUALS;
        apply_body(&xeq, var(ctx_depth));
        apply_body(&xeq, var(ctx_depth + 1));
        apply_body(&xeq, var(ctx_depth + 7));
        apply_body(&xeq, var(ctx_depth + 8));
        add_exp(&curr_type, xeq);
    }

    curr_type.head_type = EXPR_EQUALS;

    apply_body(&curr_type, apply(var(ctx_depth + 2), var(ctx_depth + 7)));
    apply_body(&curr_type, apply(var(ctx_depth + 3), var(ctx_depth + 8)));
    apply_body(&curr_type, apply(var(ctx_depth + 4), var(ctx_depth + 7)));
    apply_body(&curr_type, apply(var(ctx_depth + 5), var(ctx_depth + 8)));

    return curr_type;
}

struct expr het_ext_type(size_t ctx_depth) {
    /* (A1: Type -> A2: Type -> B1: (A1 -> Type) -> B2: (A2 -> Type)
           -> p: A1 = A2
           -> f: (x: A1 -> B1 x) -> g: (x: A2 -> B2 x)
           -> (x1: A1 -> x2: A2 -> x1 = x2 -> f x1 = g x2)
           -> f = g) */
    struct expr curr_type = {0};

    add_pi(&curr_type, "A1", universe);
    add_pi(&curr_type, "A2", universe);
    add_pi(&curr_type, "B1", exp(var(ctx_depth), universe));
    add_pi(&curr_type, "B2", exp(var(ctx_depth + 1), universe));

    {
        struct expr aeq = {0};
        aeq.head_type = EXPR_EQUALS;
        apply_body(&aeq, universe);
        apply_body(&aeq, universe);

        apply_body(&aeq, var(ctx_depth));
        apply_body(&aeq, var(ctx_depth + 1));
        add_exp(&curr_type, aeq);
    }

    {
        struct expr b1x = apply(var(ctx_depth + 2), var(ctx_depth + 5));
        add_pi(&curr_type, "f1", pi("x", var(ctx_depth), b1x));

        struct expr b2x = apply(var(ctx_depth + 3), var(ctx_depth + 6));
        add_pi(&curr_type, "f2", pi("x", var(ctx_depth + 1), b2x));
    }
    /* (x1: A1 -> x2: A2 -> x1 = x2 -> f x1 = g x2) */
    {
        struct expr pathmap = {0};

        add_pi(&pathmap, "x1", var(ctx_depth));
        add_pi(&pathmap, "x2", var(ctx_depth + 1));

        struct expr xeq = {0};
        xeq.head_type = EXPR_EQUALS;
        apply_body(&xeq, var(ctx_depth));
        apply_body(&xeq, var(ctx_depth + 1));
        apply_body(&xeq, var(ctx_depth + 7));
        apply_body(&xeq, var(ctx_depth + 8));
        add_exp(&pathmap, xeq);

        pathmap.head_type = EXPR_EQUALS;

        apply_body(&pathmap, apply(var(ctx_depth + 2), var(ctx_depth + 7)));
        apply_body(&pathmap, apply(var(ctx_depth + 3), var(ctx_depth + 8)));
        apply_body(&pathmap, apply(var(ctx_depth + 5), var(ctx_depth + 7)));
        apply_body(&pathmap, apply(var(ctx_depth + 6), var(ctx_depth + 8)));

        add_exp(&curr_type, pathmap);
    }

    curr_type.head_type = EXPR_EQUALS;
    struct expr b1x = apply(var(ctx_depth + 2), var(ctx_depth + 8));
    apply_body(&curr_type, pi("x", var(ctx_depth), b1x));

    struct expr b2x = apply(var(ctx_depth + 3), var(ctx_depth + 8));
    apply_body(&curr_type, pi("x", var(ctx_depth + 1), b2x));
    apply_body(&curr_type, var(ctx_depth + 5));
    apply_body(&curr_type, var(ctx_depth + 6));

    return curr_type;
}

#endif
