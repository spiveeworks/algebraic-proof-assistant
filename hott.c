#include <stdbool.h>
#include <stdio.h>

#include "buffer.h"

#include "expr.h"
#include "type_checking.h"

/* Build a test expression, pretty print it, type check it, print the type,
   then try destroying both. */
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
        b_specs[0].name = (struct str){0};
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
    printf("\n");

    struct expr it_type = check_type(&it);

    printf("Type: ");
    pretty_print_expr(&it_type);
    printf("\n");

    printf("\nDestroying expr.\n");
    destroy_expr(&it);
    printf("\nDestroying type.\n");
    destroy_expr(&it_type);

    return 0;
}

