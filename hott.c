#include <stdbool.h>
#include <stdio.h>

#include "buffer.h"

#include "expr.h"
#include "type_checking.h"

static void add_input(struct expr *it, char *name, struct expr type) {
    if (it->pi_intro_count != 0) {
        fprintf(stderr, "Error: Can't append a lambda introduction to a pi type expression.\n");
        exit(EXIT_FAILURE);
    }

    it->lambda_intro_count += 1;
    struct parameter_spec *spec = parameter_spec_buffer_addn(
        &it->lambda_intro_types,
        1
    );
    spec->name = c_str(name);
    spec->type = type;
}

static void set_head(struct expr *it, struct expr reference) {
    it->head_type = reference.head_type;
    it->head_var_index = reference.head_var_index;
}

static void set_body(struct expr *it, struct expr reference) {
    it->head_type = reference.head_type;
    it->head_var_index = reference.head_var_index;
    it->arg_count = reference.arg_count;
    it->arg_buffer = reference.arg_buffer;
}

static const struct expr equality_type = {.head_type = EXPR_EQUALS};

/* Build a test expression, pretty print it, type check it, print the type,
   then try destroying both. */
void pi_test(bool closed) {
    struct check_type_state check_type_state = {0};

    struct expr it = {0};
    if (closed) {
        add_input(&it, "A", universe);
    } else {
        buffer_push(check_type_state.var_types, universe);
        name_buffer_push(&check_type_state.names, c_str("A"));
    }
    {
        struct expr b = {0};
        add_exp(&b, var(0));
        set_head(&b, universe);
        add_input(&it, "B", b);
    }
    {
        struct expr f = {0};

        add_pi(&f, "x", var(0));

        set_head(&f, var(1));
        apply_body(&f, var(2));

        add_input(&it, "f", f);
    }
    add_input(&it, "x", var(0));

    set_head(&it, var(2));
    apply_body(&it, var(3));

    printf("Expr: ");
    pretty_print_expr_open(&it, &check_type_state.names);
    printf("\n");

    {
        struct expr it_type = check_type_rec(&it, &check_type_state);

        printf("Type: ");
        pretty_print_expr_open(&it_type, &check_type_state.names);
        printf("\n");

        /* printf("\nDestroying type.\n"); */
        destroy_expr(&it_type);
    }

    {
        struct expr a_val = {0};

        add_pi(&a_val, "C", universe);
        add_exp(&a_val, var(0));
        set_head(&a_val, var(0));

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
        printf("\n");

        /* printf("Destroying subbed value.\n"); */
        destroy_expr(&subbed);

        /* printf("\nDestroying type.\n"); */
        destroy_expr(&a_type);

        /* printf("\nDestroying A.\n"); */
        destroy_expr(&a_val);
    }

    /* printf("\nDestroying expr.\n"); */
    destroy_expr(&it);
    printf("\n");
}

void beta_test(void) {
    /* We need an expression that requires beta evaluation to type-check
       correctly. It doesn't even need to be complicated, could just be
       a function (\A.A)A -> (\A.A)A applied to an A and vice versa.
       We also want to test substitution of functions into expressions, so we
       might even want to define this as a `(T: (Type -> Type) -> T A -> T A)`
       and apply it to (\A.A).

       \A: Type -> \f: (A -> A) -> \g: (T: (Type -> Type) -> T A -> T A)
         -> \x: A -> f (g (\B: Type -> B) x)

       */
    struct expr it = {0};

    add_input(&it, "A", universe);

    struct expr f = {0};
    add_exp(&f, var(0));
    set_head(&f, var(0));
    add_input(&it, "f", f);

    struct expr g = {0};
    struct expr t = {0};
    add_exp(&t, universe);
    set_head(&t, universe);
    add_pi(&g, "T", t);
    add_exp(&g, apply(var(2), var(0)));
    set_body(&g, apply(var(2), var(0)));
    add_input(&it, "g", g);

    add_input(&it, "x", var(0));

    struct expr t_val = {0};
    add_input(&t_val, "B", universe);
    set_head(&t_val, var(4));
    set_body(&it, apply(var(1), apply(apply(var(2), t_val), var(3))));

    printf("Expr := ");
    pretty_print_expr(&it);
    /* printf("\n\n"); */
    struct expr it_type = check_type(&it);
    printf("\nType := ");
    pretty_print_expr(&it_type);
    printf("\n");

    /* printf("\nDestroying expr.\n"); */
    destroy_expr(&it);

    /* printf("\nDestroying type.\n"); */
    destroy_expr(&it_type);
}

void eval_test(void) {
    struct expr const_fun = {0};
    add_input(&const_fun, "A", universe);
    add_input(&const_fun, "x", var(0));
    add_input(&const_fun, "B", universe);
    add_input(&const_fun, "y", var(2));
    set_head(&const_fun, var(1));

    struct expr id = {0};
    add_input(&id, "C", universe);
    add_input(&id, "x", var(0));
    set_head(&id, var(1));

    struct expr id_type = check_type(&id);

    struct expr it = apply(apply(const_fun, id_type), id);

    printf("Expr := ");
    pretty_print_expr(&it);
    printf("\n");
    struct expr it_type = check_type(&it);
    printf("Type := ");
    pretty_print_expr(&it_type);
    printf("\n");

    head_normalise(&it);
    printf("Reduced := ");
    pretty_print_expr(&it);
    printf("\n");
}

void eq_test(void) {
    {
        struct expr it = {0};
        set_head(&it, equality_type);

        printf("Expr := ");
        pretty_print_expr(&it);
        printf("\n");
        struct expr it_type = check_type(&it);
        printf("Typeof(Expr) := ");
        pretty_print_expr(&it_type);
        printf("\n");

        struct expr type_type = check_type(&it_type);
        printf("Typeof(Typeof(Expr)) := ");
        pretty_print_expr(&type_type);
        printf("\n");
    }

    {
        struct expr it = {0};
        it.head_type = EXPR_REFL;

        printf("Expr := ");
        pretty_print_expr(&it);
        printf("\n");
        struct expr it_type = check_type(&it);
        printf("Typeof(Expr) := ");
        pretty_print_expr(&it_type);
        printf("\n");

        struct expr type_type = check_type(&it_type);
        printf("Typeof(Typeof(Expr)) := ");
        pretty_print_expr(&type_type);
        printf("\n");
    }

    {
        struct expr it = {0};
        it.head_type = EXPR_APPLY_PATH;

        printf("Expr := ");
        pretty_print_expr(&it);
        printf("\n");
        struct expr it_type = check_type(&it);
        printf("Typeof(Expr) := ");
        pretty_print_expr(&it_type);
        printf("\n");

        struct expr type_type = check_type(&it_type);
        printf("Typeof(Typeof(Expr)) := ");
        pretty_print_expr(&type_type);
        printf("\n");
    }

    {
        struct expr it = {0};
        it.head_type = EXPR_HETEXT;

        printf("Expr := ");
        pretty_print_expr(&it);
        printf("\n");
        struct expr it_type = check_type(&it);
        printf("Typeof(Expr) := ");
        pretty_print_expr(&it_type);
        printf("\n");

        struct expr type_type = check_type(&it_type);
        printf("Typeof(Typeof(Expr)) := ");
        pretty_print_expr(&type_type);
        printf("\n");
    }
}

void ext_test(void) {
    /* Suppose we have a unit type, so
           A: Type,
           x: A,
           centre: (y: A -> x = y),
       and we have two functions (A -> A):
           f1 y = x
       and
           f2 y = y
       id, and const x. These are extensionally equal:
           pathmap: (y1, y2: A -> y1 = y2 -> f1 y1 = f2 y2)
               i.e. (y1, y2: A -> y1 = y2 -> x = y2)
           pathmap y1 y2 yeq = centre y2
       then we get
           feq: f1 = f2
           feq = hetext A A (\_ -> A) (\_ -> A) (refl Type A) f1 f2 pathmap
       and then if we have some specific y in A, and a proof that y = x, we
       should be able to do something like apply_path to that path, and get
       centre x as the result.
          test_thing: (y: A -> y = x -> x = x)
          test_thing y p = apply_path A A (\_ -> A) (\_ -> A) f1 f2 feq y x p
       */
    struct expr it = {0};
    add_input(&it, "A", universe);
    add_input(&it, "x", var(0));
    {
        struct expr centre = {0};
        add_pi(&centre, "y", var(0));
        centre.head_type = EXPR_EQUALS;
        apply_body(&centre, var(0));
        apply_body(&centre, var(0));
        apply_body(&centre, var(1));
        apply_body(&centre, var(2));
        add_input(&it, "centre", centre);
    }
    add_input(&it, "y", var(0));
    {
        struct expr eq = {0};
        eq.head_type = EXPR_EQUALS;
        apply_body(&eq, var(0));
        apply_body(&eq, var(0));
        apply_body(&eq, var(3));
        apply_body(&eq, var(1));
        add_input(&it, "p", eq);
    }
    it.head_type = EXPR_APPLY_PATH;
    apply_body(&it, var(0));
    apply_body(&it, var(0));

    struct expr family = {0};
    add_input(&family, "_", var(0));
    set_head(&family, var(0));
    apply_body(&it, family);
    copy_expr(NULL, &family);
    apply_body(&it, family);

    struct expr f1 = {0};
    add_input(&f1, "y", var(0));
    set_head(&f1, var(1));
    apply_body(&it, f1);

    struct expr f2 = {0};
    add_input(&f2, "y", var(0));
    set_head(&f2, var(5));
    apply_body(&it, f2);

    struct expr feq = {0};
    feq.head_type = EXPR_HETEXT;
    apply_body(&feq, var(0));
    apply_body(&feq, var(0));
    copy_expr(NULL, &family);
    apply_body(&feq, family);
    copy_expr(NULL, &family);
    apply_body(&feq, family);
    {
        struct expr aeq = {0};
        aeq.head_type = EXPR_REFL;
        apply_body(&aeq, universe);
        apply_body(&aeq, var(0));
        apply_body(&feq, aeq);
    }
    copy_expr(NULL, &f1);
    apply_body(&feq, f1);
    copy_expr(NULL, &f2);
    apply_body(&feq, f2);

    struct expr pathmap = {0};
    add_input(&pathmap, "y1", var(0));
    add_input(&pathmap, "y2", var(0));
    {
        struct expr yeq = {0};
        yeq.head_type = EXPR_EQUALS;
        apply_body(&yeq, var(0));
        apply_body(&yeq, var(0));
        apply_body(&yeq, var(5));
        apply_body(&yeq, var(6));
        add_input(&pathmap, "yeq", yeq);
    }
    set_body(&pathmap, apply(var(2), var(6))); /* centre */

    apply_body(&feq, pathmap);

    apply_body(&it, feq);

    apply_body(&it, var(3));
    apply_body(&it, var(1));
    apply_body(&it, var(4));

    printf("Expr := ");
    pretty_print_expr(&it);
    printf("\n");
    struct expr it_type = check_type(&it);
    printf("Type := ");
    pretty_print_expr(&it_type);
    printf("\n");

    head_normalise(&it);
    printf("Reduced := ");
    pretty_print_expr(&it);
    printf("\n");
}

int main(int argc, char **argv) {
    /* pi_test(true); */
    /* beta_test(); */
    /* eval_test(); */
    /* eq_test(); */
    ext_test();

    printf("Done.\n");
    return 0;
}

