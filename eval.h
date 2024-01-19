#ifndef APA_EVAL_H
#define APA_EVAL_H

void reduce_apply_lambda(size_t depth, struct expr *it) {
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
}

bool reduce_apply_path(size_t depth, struct expr *it) {
    /* A1 A2 B1 B2 f1 f2 feq x1 x2 xeq */
    if (it->arg_count < 7) return false;
    struct expr *apply_path_args = (struct expr*)&it->arg_buffer[1];
    struct expr *feq = &apply_path_args[6];
    if (feq->head_type == EXPR_HETEXT) {
        /* A1 A2 B1 B2 aeq f1 f2 pathmap */
        if (feq->arg_count < 8) return false;
        struct expr *het_ext_args = (struct expr*)&feq->arg_buffer[1];
        struct expr pathmap = {0};
        copy_expr(&pathmap, &het_ext_args[7]);

        /* Replace apply_path and the first 7 args, with the pathmap
           itself. */
        replace_head(it, 7, pathmap);

        return true;
    }

    if (feq->head_type != EXPR_REFL) return false;

    /* Now the complicated case, we have to actually convert a function on
       points into a function on paths. */
    /* TODO :P */

    return false;
}

bool reduce_expr_once(size_t depth, struct expr *it) {
    bool reduced = false;
    if (it->head_type == EXPR_APPLY_LAMBDA) {
        reduce_apply_lambda(depth, it);
        reduced = true;
    } else if (it->head_type == EXPR_APPLY_PATH) {
        reduced = reduce_apply_path(depth, it);
    }

    return reduced;
}

void head_normalise(struct expr *it) {
    while (reduce_expr_once(0, it));
}

#endif
