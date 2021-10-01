# inside-out

An algorithm of inside-out bidirectional typing, where types can flow from inside to outside.

## Features

- Simply typed lambda calculus
- No unification when typing
- (Outside-in) bidirectional typing[^1]
- Inside-out bidirectional typing
- Application mode[^2]
- Partial type-checking with holes

## Inside-out bidirectional typing

The *inside-out bidirectional typing* is bidirectional typing, where the type information can flow from inside to outside.
Consider the following example:

```lean
abs x ⇒ x ∷ bool
```

The traditional bidirectional typing gives up on inferring the type of this expression because it does not know the type of `x`.
However, in this case, the type of `x` is obvious: `bool`.

The inside-out bidirectional typing takes into account how the variables are used.
When it encounters an abstraction, it *dives into* the abstraction body and *lifts up* the context.
We refer to the traditional bidirectional typing, where the type information only flows from outside to inside as *outside-in bidirectional typing* to distinguish it from inside-out bidirectional typing.

## References

[^1]: Jana Dunfield and Neel Krishnaswami. 2021. Bidirectional Typing. <i>ACM Comput. Surv.</i> 54, 5, Article 98 (June 2021), 38 pages. DOI:https://doi.org/10.1145/3450952
[^2]: Xie, N., & Oliveira, B. (2018). Let Arguments Go First. ESOP.
