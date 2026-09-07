# Does HKS implicitly allow an algebraic exceptional set?

The evidence strongly supports reading Hölzl–Kleine–Stephan (HKS) literally:
their conjecture does **not** include an implicit exceptional set of the
kind allowed by Vojta. This conclusion follows from how they use the
statement, as well as from its definition.

## The stated problem

In [HKS, Conjecture 7](https://arxiv.org/html/2409.13439v2), the set `R(n)`
consists of integer tuples with zero total sum, no nonempty proper zero
subsum, and pairwise coprime entries. The conjecture predicts `Q_R(n) = 1`.
Their introduction distinguishes their subject from Vojta's general
conjecture. Immediately after Conjecture 7, they explicitly discuss the
potential difficulty of disproving `Q_R(4) = 1`.

The numbering here follows arXiv v2. Conjecture 7 and Theorem 14 below are
Conjecture 1.8 and Theorem 2.1 in the
[published paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/881532D8B69924BBFA5C76A32A52063A/S1446788725000084a.pdf/improved_lower_bounds_for_strong_nconjectures.pdf).

## Their own examples can be excluded algebraically

In [HKS, §2, Theorem 14](https://arxiv.org/html/2409.13439v2), they use
`t = 6^(2^k)`, for integers `k ≥ 1`, and the family

```math
(a,b,c,d,e)=\bigl((t+1)^3,-(t-1)^3,-6t^2,-31,29\bigr).
```

They verify stronger admissibility conditions and obtain a quality limsup
at least `3/2`, hence also `Q_R(5) ≥ 3/2`.

The following geometric observation is our inference from that construction.
Every example satisfies

```math
29d+31e=29(-31)+31(29)=0.
```

Thus all its projective points lie in

```math
E=X_5\cap\{29d+31e=0\},\qquad
X_5=\{[a:b:c:d:e]\in\mathbb P^4:a+b+c+d+e=0\}.
```

The extra equation is independent of the zero-sum equation, so `E` is a
proper Zariski-closed subset of `X₅`. In ordinary terms, all these examples
belong to a special algebraic subset that a Vojta-style exception could
remove in its entirety.

Consequently, this construction would not establish the corresponding
lower bound if one were permitted to discard an arbitrary proper algebraic
exceptional set first. Yet HKS use it to bound the very quantities appearing
in their conjecture. Reading an unstated exception into those quantities
would change the meaning of their own argument.

## What this establishes

An implicit Vojta-style restriction is therefore a very unlikely reading
of HKS. The absence of such a restriction is supported by their mathematical
practice, rather than merely by a missing phrase in one displayed statement.
This is evidence about the paper's meaning, not a report of private
confirmation from its authors.

The repository's four-variable lower bound addresses the unrestricted
`Q_R(4)` question discussed in HKS. This interpretation argument does not
establish the result's novelty or importance; those require a separate
literature assessment. It also does not turn the result into a refutation
of [Vojta's formulation, §2](https://arxiv.org/html/math/9806171v1), which
explicitly permits algebraic exceptions.
