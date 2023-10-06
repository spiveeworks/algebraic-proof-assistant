#ifndef APA_EVAL_H
#define APA_EVAL_H

bool reduce_expr_once(size_t depth, struct expr *it) {
    if (it->head_type != EXPR_APPLY_LAMBDA) return false;
    if (it->arg_count == 0) {
        fprintf(stderr, "Error: Got EXPR_APPLY_LAMBDA with no args?\n");
        exit(EXIT_FAILURE);
    }

    depth += it->lambda_intro_count + it->pi_intro_count;

    struct expr *args = (struct expr*)&it->arg_buffer[1];

    struct expr *f = args;
    size_t arg_count = it->arg_count - 1;
    args = &args[1];

    size_t lambda_count = f->lambda_intro_count;

    /* Sub in as many args as we can, stripping off the lambdas as we go. */
    size_t sub_count = arg_count;
    if (sub_count > lambda_count) sub_count = lambda_count;
    struct expr subbed;
    if (sub_count == 0) {
        fprintf(stderr, "Warning: Got EXPR_APPLY_LAMBDA that wasn't "
            "beta-reducible?\n");
        /* The goal is to substitute enough arguments that either there are no
           lambdas left, or no arguments left, so that `it` can be concatenated
           with this subbed result. If there are already no lambdas left, or no
           arguments left, then the expression can be concatenated as-is. */
        copy_expr(&subbed, it);
    } else {
        subbed = subst_exprs(depth, f, true, depth, sub_count, args);
    }

    /* Now piece it together. */
    struct expr result = {0};
    result.lambda_intro_count = it->lambda_intro_count;
    result.pi_intro_count = it->pi_intro_count;
    result.lambda_intro_types = it->lambda_intro_types;

    size_t leftover_arg_count = arg_count - sub_count;
    struct expr *leftover_args = concat_intros_set_head_alloc_args(
        &result,
        subbed,
        leftover_arg_count
    );

    for (int i = 0; i < leftover_arg_count; i++) {
        copy_expr(&leftover_args[i], &args[sub_count + i]);
    }

    /* Hide intros that we consumed, and destroy the args that we have now
       copied out of. */
    it->lambda_intro_count = 0;
    it->pi_intro_count = 0;
    it->lambda_intro_types = NULL;
    destroy_expr(it);

    /* Now that the input is uninitialised, overwrite it with the result we
       just calculated. */
    *it = result;

    return true;
}

void head_normalise(struct expr *it) {
    while (reduce_expr_once(0, it));
}

#endif
