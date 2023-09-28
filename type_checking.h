#ifndef APA_TYPE_CHECKING_H
#define APA_TYPE_CHECKING_H

#include <stdio.h>

#include "buffer.h"

struct check_type_state {
    struct name_buffer names;
    struct expr_buffer var_types;
};

struct expr check_type_rec(struct expr *it, struct check_type_state *state) {
    size_t intro_count = it->lambda_intro_count + it->pi_intro_count;
    struct parameter_spec *specs =
        (struct parameter_spec*)&it->lambda_intro_types[1];
    for (int i = 0; i < intro_count; i++) {
        struct parameter_spec *spec = &specs[i];
        struct expr spec_type_type = check_type_rec(&spec->type, state);
        if (!expr_is_sort(&spec_type_type)) {
            if (spec->name.data) {
                printf("Type error: Parameter %s was annotated with the type ",
                    spec->name.data);
            } else {
                printf("Type error: An arrow expression was given the input "
                    "type ");
            }
            pretty_print_expr_open(&spec->type, &state->names);
            printf(", but this has type ");
            pretty_print_expr_open(&spec_type_type, &state->names);
            printf(", so it is not a valid type annotation.\n");

            /* Only need to destroy it if it isn't a sort. Sorts don't borrow
               anything. */
            destroy_expr(&spec_type_type);
        }

        name_buffer_push(&state->names, spec->name);
        /* Just borrow the type. */
        buffer_push(state->var_types, spec->type);
    }

    struct expr curr_type = {0};

    switch (it->head_type) {
        case EXPR_NULL:
        {
            fprintf(stderr, "Error: Cannot infer type of NULL expression.\n");
            exit(EXIT_FAILURE);
            break;
        }
        case EXPR_APPLY_LAMBDA:
        {
            /* Do nothing. */
            break;
        }
        case EXPR_VAR:
        {
            copy_expr(&curr_type, &state->var_types.data[it->head_var_index]);
            /* If binding types contain nested pi/lambda contexts, then we need
               to rewrite them into this context. */
            deepen_expr_context(
                &curr_type,
                it->head_var_index,
                state->var_types.count
            );
            break;
        }
        case EXPR_GLOBAL:
        {
            fprintf(stderr, "Error: Type inference for global terms is not yet implemented.\n");
            exit(EXIT_FAILURE);
            break;
        }
        case EXPR_SORT:
        {
            curr_type.head_type = EXPR_SORT;
            /* Increase universe level here. */
            break;
        }
    }

    size_t skip = 0;
    /* Skip the first argument if we already used it to get a type. */
    if (it->head_type == EXPR_APPLY_LAMBDA) skip = 1;

    /* TODO: Embed this skip variable into a loop that incrementally extracts
       pi parameter specs. */
    size_t args_remaining = it->arg_count - skip;

    if (args_remaining > 0) {
        if (args_remaining > curr_type.pi_intro_count) {
            fprintf(stderr, "Error: Tried to apply type that wasn't a pi type. (beta reduction of pi types is not yet implemented.)\n");
            exit(EXIT_FAILURE);
        }
        struct parameter_spec *param_types = parameter_spec_split_destructive(
            &curr_type.lambda_intro_types,
            args_remaining
        );
        curr_type.pi_intro_count -= args_remaining;

        struct expr *args = (struct expr*)&it->arg_buffer[1];
        for (size_t i = 0; i < args_remaining; i++) {
            struct expr *arg = &args[i + skip];
            struct expr arg_type = check_type_rec(arg, state);
            struct expr *expected_type = &param_types[i].type;
            if (!expr_eq(&arg_type, expected_type)) {
                printf("Type checking error: A function expected ");
                pretty_print_expr_open(expected_type, &state->names);
                printf(", but it was applied to ");
                pretty_print_expr_open(arg, &state->names);
                printf(", which is of type ");
                pretty_print_expr_open(&arg_type, &state->names);
                printf(".\n");
            }
            destroy_expr(&arg_type);
        }

        for (int i = 0; i < args_remaining; i++) {
            destroy_expr(&param_types[i].type);
        }
        /* TODO: Reuse this buffer between incremental parameter extractions? */
        free(param_types);
    }

    if (it->pi_intro_count > 0) {
        if (!expr_is_sort(&curr_type)) {
            /* Borrow `it` but hide the lambda/pi part. */
            struct expr it_copy = *it;
            it_copy.lambda_intro_count = 0;
            it_copy.pi_intro_count = 0;

            printf("Type error: Arrow expression was applied to ");
            pretty_print_expr_open(&it_copy, &state->names);
            printf(", which is not a type.\n");
        }
    }

    if (it->lambda_intro_count > 0) {
        size_t prev_param_count = curr_type.pi_intro_count;
        parameter_spec_buffer_addn(
            &curr_type.lambda_intro_types,
            it->lambda_intro_count
        );
        struct parameter_spec *curr_specs =
            (struct parameter_spec *)&curr_type.lambda_intro_types[1];
        /* Move curr[0..prev_count] to curr[it.count..new_count] */
        memmove(
            &curr_specs[it->lambda_intro_count],
            curr_specs,
            prev_param_count * sizeof(struct parameter_spec)
        );
        /* Copy it[0..it.count] to curr[0..it.count] */
        struct parameter_spec *it_specs =
            (struct parameter_spec *)&it->lambda_intro_types[1];
        for (int i = 0; i < it->lambda_intro_count; i++) {
            curr_specs[i].name = it_specs[i].name;
            copy_expr(&curr_specs[i].type, &it_specs[i].type);
        }
        curr_type.pi_intro_count += it->lambda_intro_count;
    }

    for (int i = 0; i < intro_count; i++) {
        buffer_pop(state->names);
        buffer_pop(state->var_types);
    }

    return curr_type;
}

struct expr check_type(struct expr *it) {
    struct check_type_state state = {0};
    struct expr result = check_type_rec(it, &state);
    buffer_free(state.names);
    buffer_free(state.var_types);
    return result;
}

#endif
