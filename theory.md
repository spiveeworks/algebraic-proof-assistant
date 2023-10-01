
# Path Computations

Normally equality is understood as the unique type that provides refl and J,
but J doesn't tell us how to apply quotient or extensionality proofs to
things.

In our type theory we take trans and sym to be primitives, so equality
really becomes a path built out of edges, and if those edges are between
types, then we can transport from one type to another easily, which is why
we have transport: (A = B -> A -> B) as a primitive. Implementing a J
eliminator then becomes a question of computing a path between types, from a
path between terms, which we can do using cong: (x = y -> F x = F y). This
divides the problem cleanly into two builtins that we might be able to
implement.

Of these two built in computation rules, transport is by far the easiest,
the only valid paths between types are refl and uv, (and box/arrow paths, which
are explained later,) which compute as follows:
    transport (refl A) x := x
    transport (uv f g gof fog comm) x := f x

The hard part is cong, which maps all of our paths between terms to other
paths between terms, and ultimately, to paths between types that we can
transport between. Actually, cong applied to terms is often easy:
    cong f (refl x) := refl (f x)
    cong (qelim f m) (qedge r) := m r
    cong (\f -> g (f x)) (ext pw) := cong g (pw x)
    cong (\f -> g (f x1) (f x2)) (ext pw)
        := trans (cong (\y -> g y (f1 x2)) (pw x1))
                 (cong (\y -> g (f2 x1) y) (pw x2))
    cong (\f -> \x -> g (f x)) (ext pw) := ext (\x -> cong g (pw x))
    cong (\f -> \z -> g (f x) z) (ext pw) := ext (\z -> cong (\y -> g y z) (pw x))

The two hard parts are
 1. cong/transport applied to heterogeneous equality, and
 2. cong applied to uv

## Heterogeneous cong

When two types A and B are equal, and we have x: A and y: B, we might want to
define a type that represents proof that x is equal to y.
    heteq: (A: Type -> B: Type -> A = B -> A -> B -> Type)
The way we do this is
    heteq A B p x y := transport p x = y

Now if we have a type family `B: (A -> Type)`, and `p: x1 = x2`, then
`B x1 = B x2` via `cong B p`, so type families induce paths between types, and
these paths induce a heterogeneous equality relation between elements of those
types.

Now if we want to apply a function to both sides of a heterogeneous equality,
we need that function to type check differently on each side, which we can do
by making the function dependently typed, and defining both sides of the
equation as some type family applied to equal values x1 and x2. This means
heterogeneous cong is actually cong for equality in type families.
As a type annotation, this would look like:
    hcong1: (A: Type -> x1: A -> x2: A -> p: x1 = x2
        -> B: (A -> Type) -> y1: B x1 -> y2: B x2 -> transport (cong B p) y1 = y2
        -> C: Type -> f: (x: A -> B x -> C) -> f x1 y1 = f x2 y2
or if the result is itself a type family
    hcong2: (A: Type -> x1: A -> x2: A -> p: x1 = x2
        -> B: (A -> Type) -> y1: B x1 -> y2: B x2 -> transport (cong B p) y1 = y2
        -> C: (A -> Type) -> f: (x: A -> B x -> C x) -> transport (cong C p) (f x1 y1) = f x2 y2

We can actually implement these functions using dependently typed cong:
    picong: (A: Type -> B: (A -> Type) -> f: (x: A -> B x) -> x1: A -> x2: A
        -> x1 = x2 -> transport (cong B p) (f x1) = f x2)
To summarise, picong maps a homogeneous equality to a heterogeneous equality.

Then hcong follows from showing that both sides are equal to
    transport (cong (\x -> B x -> C x) p) (f x1) (transport (cong B p) y1)
One path from there to `transport (cong C p) (f x1)` might be to suppose that
it simply beta-reduces as
    transport (cong (\x -> B x -> C x) p) f1 y
        := transport (cong C p) f1 (transport (sym (cong B p)) y)
then when applied to y = transport (cong B p) y1, we can cancel out the
symmetric transports, using either another computation rule, or a builtin
sym-inv axiom.

To make transport compute on cong like this, we can introduce an intermediate
path type:
    arrow: (B1: Type -> B2: Type -> C1: Type -> C2: Type
        -> B1 = B2 -> C1 = C2 -> (B1 -> C1) = (B2 -> C2))
    cong (\x -> B x -> C x) p
        := arrow (B x1) (B x2) (C x1) (C x2) (cong B p) (cong C p)
    transport (arrow B1 B2 C1 C2 p q) f
        := \x: B2 -> transport q (f (transport (sym p) x))

On the other hand, to get from our intermediate step to our actual goal, we use
our base paths `p` and `q`, and picong:
      transport (cong (\x -> B x -> C x) p) (f x1) (transport (cong B p) y1)
    = f x2 (transport (cong B p) y1) -| pointwise (picong f p)
                                                  (transport (cong B p) y1)
    = f x2 y2                        -| cong (f x2) q

so all together we have
    hcong2 A x1 x2 p B y1 y2 q C f
        :: transport (cong C p) (f x1 y2)
         = transport (cong C p) (f x1
                         (transport (sym (cong B p)) (transport (cong B p) y2)))
                             -| sym-inv (cong B p) y2
         = transport (arrow (B x1) (B x2) (C x1) (C x2) (cong C p) (cong B p))
                     (f x1)
                     (transport (cong B p) y2)
         = transport (cong (\x -> B x -> C x) p)
                     (f x1)
                     (transport (cong B p y2))
         = f x2 (transport (cong B p y2)) -| pointwise (picong f p)
                                                       (transport (cong B p y2))
         = f x2 y2                        -| cong (f x2) q

Once we have hcong2, hcong1 is simply
    hcong1 A x1 x2 p B y1 y2 q C f
        := hcong2 A x1 x2 p B y1 y2 q (\x: A -> C) f

Then you can actually implement J elimination in terms of hcong:
    J: (A: Type -> x1: A -> M: (x2: A -> x1 = x2 -> Type)
        -> m: (M x (refl x))
        -> (x2: A -> p: x1 = x2 -> M x2 p)
To do this we construct a path from `refl x1` to `p`, and then use hcong to
apply `M` to both sides, to get a path from `M x1 (refl x1)` to `M x2 p`,
then we can transport `m` along this path.
    refl-transport: (A: Type -> x1: A -> x2: A -> p: x1 = x2
        -> transport (cong (\x: A -> x1 = x) p) (refl x1) = p
    refl-transport A x1 x2 p := refl p -- explained later

    J-path: (A: Type -> x1: A -> x2: A -> p: x1 = x2
        -> M: (x2: A -> x1 = x2 -> Type)
        -> M x1 refl = M x2 p
    J-path A x1 x2 p M
        := hcong1 A x1 x2 p
                  (\x: A -> x1 = x)
                  (refl x1)
                  p
                  (refl-transport A x1 x2 p)
                  Type
                  M

    J A x1 M m x2 p := transport (J-path A x1 x2 p M) m

We provided `refl p` as the definition of `refl-transport`, but how does this
work? Look at the type of `cong (\x: A -> x1 = x) p`, it is of type
`(x1 = x1) = (x1 = x2)`, "the type of paths from x1 to x1, is equal to the type
of paths from x1 to x2", or put another way, "there is a path from `x1 = x1` to
`x2 = x2`". How would you transport along this path? How can a path `x1 = x1`
be turned into a path `x2 = x2`? More generally, how can a path `x1 = y1` be
turned into a path `x2 = y2`?
    box-transport: (A: type -> x1: A -> x2: A -> y1: A -> y2: A
        -> x1 = x2 -> y1 = y2
        -> (x1 = y1 -> x2 = y2)
    box-transport A x1 x2 y1 y2 px py p = trans (trans (sym px) p) py
So to make `transport (cong (\x -> f x = g x) p)` compute to something like
this box-transport, we introduce another path type, called a box path, for
paths between equality types, similar to the arrow path between exponential
types.
    box: (A: type -> x1: A -> x2: A -> y1: A -> y2: A
        -> x1 = x2 -> y1 = y2
        -> (x1 = y1) = (x2 = y2)
    cong (\x: A -> f x = g x) p
        := box A (f x1) (g x1) (f x2) (g x2) (cong f p) (cong g p)
    transport (box A x1 x2 y1 y2 px py) p = trans (trans (sym px) p) py

## Univalence

We have `transport A B (uv f g gof fog comm) x = f g`, but if we want to
compute `cong F (uv ...)`, then we basically need to implement a generic
functor instances for `F`, in order to set
    transport (cong F (uv f g ...)) ax := fmap F f ax
One way of doing this would be to use `fmap F f` and `fmap F g` to actually
build an isomorphism between `F A` and `F B`, and then literally define
    cong F (uv f g ...) := uv (fmap F f) (fmap F g) ...

If we can implement this recursively for the case that `F` is a pi type between
two smaller type constructors, then we can use this as a basis to work out how
all other types should compute. Pi is hard, but for exponentials this looks
something like:
    cong (\T -> (F T -> G T)) (p = uv f g gof fog comm)
        := (uv (\af: (F A -> G A) -> \bx: F B
                   -> transport (cong G p) (af (transport (sym (cong F p)) bx)))
               (\bf: (F B -> G B) -> \ax: F A
                   -> transport (sym (cong G p)) (bf (transport (cong F p)) ax))
               (\af: (F A -> G A) -> ext (\ax: F A
                   -> somehow show transport p (transport (sym p)) ax = ax))
               (\bf: (F B -> G B) -> ext (\bx: F B
                   -> .......))
               (\af: (F A -> G A) -> ext (\ax: F A
                   -> I don't even know.)))

But notice, `\af -> \bx -> transport (af (transport bx))` looks an awful lot
like the arrow transport rule, in fact if we just ignore uv, and look at how we
said cong on exponential type constructors should compute, the above expression
should really compute as
    cong (\T -> (F T -> G T)) p
        := arrow (F A) (F B) (G A) (G B) (cong F p) (cong G p)
then we don't need to worry about building an isomorphism, we can just
transport using this arrow path.
This raises the question, however, are these arrow paths symmetric?
    sym (arrow B1 B2 C1 C2 p q) := arrow B2 B1 C2 C1 (sym p) (sym q)
Looks like yes.

So the real question is, how do we generate and transport along arrow paths
between dependently typed functions?

## Dependently Typed Arrow Paths

If we wanted to make an arrow path for pi types,
`(x: B1 -> C1 x) = (x: B2 -> C2 x)`, with the expectation that
`cong (\x -> (y: B x -> C x y)) p` would compute down to some such arrow path,
then in order to even specify the type of this `deparrow`, we need to choose a
way of even representing that `C1 x = C2 x`, given that there is no `x` that
will type check on both sides of that equation. We can start by asking what we
can even produce when computing cong:
    cong (\x -> (y: B x -> C x y)) p
        := deparrow (B x1) (B x2) (\y: B x1 -> C x1 y) (\y: B x2 -> C x2 y) (cong B p) (picong A (\x: A -> B x -> Type) C x1 x2 p)

Analogous to the `cong C p` in the `arrow` computation rule, we have
`picong C p` of type `transport (cong (\x -> B x -> Type) p) (C x1) = C x2`,
but the left hand side of this equation can be beta reduced using the
independently typed arrow rules:
  transport (cong (\x -> B x -> Type) p) (C x1)
= transport (arrow (B x1) (B x2) Type Type (cong B p) refl) (C x1)
= \y: B x2 -> transport refl (C x1 (transport (sym (cong B p)) y))
= \y: B x2 -> C x1 (transport (sym (cong B p)) y)

so we could define the type of deparrow to be
    deparrow: (B1: Type -> B2: Type -> C1: (B1 -> Type) -> C2: (B2 -> Type)
        -> p: B1 = B2
        -> (\x: B2 -> C1 (transport (sym p) x)) = C2
        -> (x: B1 -> C1 x) = (x: B2 -> C2 x))
then if we had to transport from one deparrow to another, we might do
    transport (deparrow B1 B2 C1 C2 p q) f
        := \x: B2 -> transport (cong (\C: (B2 -> Type) -> C x) q)
                               (f (transport (sym p) x))
but this immediately turns the definitional equality between C1 and C2 into a
pointwise equality, so we could simply generalize deparrow to only require
the pointwise version, and make cong convert the definitional into pointwise:
    deparrow: (B1: Type -> B2: Type -> C1: (B1 -> Type) -> C2: (B2 -> Type)
        -> p: B1 = B2
        -> (x: B2 -> C1 (transport (sym p) x) = C2 x)
        -> (x: B1 -> C1 x) = (x: B2 -> C2 x))
    cong (\x -> (y: B x -> C x y)) p
        := deparrow (B x1) (B x2) (\y: B x1 -> C x1 y) (\y: B x2 -> C x2 y)
            (cong B p)
            (pointwise (B x2) Type
                (transport (cong (\x -> B x -> Type) p) (C x1))
                (C x2)
                (picong A (\x: A -> B x -> Type) C x1 x2 p))
    where pointwise: (B: Type -> C: Type -> f1: (B -> C) -> f2: (B -> C)
              -> f1 = f1 -> (x: B -> f1 x = f2 x)
          pointwise B C f g p x = cong (\f: (B -> C) -> f x) p
    transport (deparrow B1 B2 C1 C2 p q) f
        := \x: B2 -> transport (q x) (f (transport (sym p) x))

The other important consideration is how to compute `sym` of such a deparrow
path.
    sym (deparrow B1 B2 C1 C2 p q)
        := deparrow B2 B1 C2 C1 (sym p) (reverse-lemma B1 B2 C1 C2 p q)
    reverse-lemma
    reverse-lemma: (B1: Type -> B2: Type -> C1: (B1 -> Type) -> C2: (B2 -> Type)
        -> p: B1 = B2
        -> (x2: B2 -> C1 (transport (sym p) x2) = C2 x2)
        -> (x1: B1 -> C2 (transport (sym (sym p)) x1) = C1 x1)
    reverse-lemma B1 B2 C1 C2 p q x1
        :: C2 (transport (sym (sym p)) x1)
         = C2 (transport           p   x1)         -| sym-inv p
         = C1 (transport (sym p) (transport p x1)) -| sym (q (transport p x1))
         = C1 x1                                   -| transport-inv p x1

Now _this_ is where everything gets hairy, we depend on `sym-inv` again, which
probably suggests that `sym-inv` is supposed to be a builtin, which means we
actually need to compute `sym-inv` of all of our paths, in particular
`sym (sym uv) = uv`, and `reverse-lemma (sym p) (reverse-lemma p q) = q`...

