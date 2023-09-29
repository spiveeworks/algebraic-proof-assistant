#include <stdbool.h>
#include <stdio.h>

#include "buffer.h"

#include "expr.h"
#include "type_checking.h"

/* Build a test expression, pretty print it, type check it, print the type,
   then try destroying both. */
int main(int arg_count, char **args) {
    struct check_type_state check_type_state = {0};

    struct expr it = {0};
    bool closed = true;
    it.lambda_intro_count = closed ? 4 : 3;
    struct parameter_spec *specs = parameter_spec_buffer_addn(
        &it.lambda_intro_types,
        it.lambda_intro_count
    );
    int i = 0;
    if (closed) {
        specs[i].name = c_str("A");
        specs[i].type = (struct expr){.head_type = EXPR_SORT};
        i++;
    } else {
        buffer_push(
            check_type_state.var_types,
            (struct expr){.head_type = EXPR_SORT}
        );
        name_buffer_push(
            &check_type_state.names,
            c_str("A")
        );
    }
    specs[i].name = c_str("B");
    specs[i].type = (struct expr){0};
    {
        specs[i].type.pi_intro_count = 1;
        struct parameter_spec *b_specs = parameter_spec_buffer_addn(
            &specs[i].type.lambda_intro_types,
            1
        );
        b_specs[0].name = (struct str){0};
        b_specs[0].type = (struct expr){.head_type = EXPR_VAR, .head_var_index = 0};

        specs[i].type.head_type = EXPR_SORT;
    }
    i++;
    specs[i].name = c_str("f");
    specs[i].type = (struct expr){0};
    {
        specs[i].type.pi_intro_count = 1;
        struct parameter_spec *f_specs = parameter_spec_buffer_addn(
            &specs[i].type.lambda_intro_types,
            1
        );
        f_specs[0].name = c_str("x");
        f_specs[0].type = (struct expr){.head_type = EXPR_VAR, .head_var_index = 0};

        specs[i].type.head_type = EXPR_VAR;
        specs[i].type.head_var_index = 1;

        specs[i].type.arg_count = 1;
        struct expr *pi_output_args = expr_buffer_addn(
            &specs[i].type.arg_buffer,
            1
        );
        pi_output_args[0] = (struct expr){.head_type = EXPR_VAR, .head_var_index = 2};
    }
    i++;
    specs[i].name = c_str("x");
    specs[i].type = (struct expr){.head_type = EXPR_VAR, .head_var_index = 0};
    it.head_type = EXPR_VAR;
    it.head_var_index = 2;

    it.arg_count = 1;
    struct expr *body_args = expr_buffer_addn(
        &it.arg_buffer,
        1
    );
    body_args[0] = (struct expr){.head_type = EXPR_VAR, .head_var_index = 3};

    printf("Expr: ");
    pretty_print_expr_open(&it, &check_type_state.names);
    printf("\n");

    {
        struct expr it_type = check_type_rec(&it, &check_type_state);

        printf("Type: ");
        pretty_print_expr_open(&it_type, &check_type_state.names);
        printf("\n");

        printf("\nDestroying type.\n");
        destroy_expr(&it_type);
    }

    {
        struct expr a_val = {0};
        struct parameter_spec *spec;

        spec = parameter_spec_buffer_addn(&a_val.lambda_intro_types, 1);
        spec->name = c_str("C");
        spec->type = (struct expr){.head_type = EXPR_SORT};

        spec = parameter_spec_buffer_addn(&a_val.lambda_intro_types, 1);
        spec->name = (struct str){0};
        spec->type = (struct expr){.head_type = EXPR_VAR, .head_var_index = 0};

        a_val.pi_intro_count = a_val.lambda_intro_types->elem_count;

        a_val.head_type = EXPR_VAR;
        a_val.head_var_index = 0;

        printf("\nSubstituting A <- ");
        pretty_print_expr(&a_val);
        printf("\n");

        struct expr a_type = check_type(&a_val);

        printf("Type: ");
        pretty_print_expr(&a_type);
        printf("\n");

        struct expr subbed = subst_exprs(
            0, &it, closed, /* turn `it` into a closed expression */
            0, 1, &a_val /* using the single closed expression a_val */
        );
        printf("Result: ");
        pretty_print_expr(&subbed);

        printf("\nDestroying subbed value.\n");
        destroy_expr(&subbed);

        printf("\nDestroying type.\n");
        destroy_expr(&a_type);

        printf("\nDestroying A.\n");
        destroy_expr(&a_val);
    }

    printf("\nDestroying expr.\n");
    destroy_expr(&it);

    return 0;
}

