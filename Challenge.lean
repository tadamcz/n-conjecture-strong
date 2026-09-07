import Mathlib

/-!
# The strong $n$ conjecture for $n = 4$

The *strong $n$ conjecture* generalizes the *abc* conjecture to $n \geq 3$ integers.
Let $R(n)$ be the set of $n$-tuples of integers $(a_1, \dots, a_n)$ such that
(i) $a_1, \dots, a_n$ are pairwise coprime,
(ii) $a_1 + \dots + a_n = 0$, and
(iii) no nonempty proper subsum of $a_1, \dots, a_n$ equals $0$.
The conjecture predicts that the limit superior over $R(n)$ of the *quality*
$$q(a_1, \dots, a_n) = \frac{\log \max(|a_1|, \dots, |a_n|)}
  {\log \operatorname{rad}(|a_1 a_2 \cdots a_n|)}$$
equals $1$; equivalently, that for every $\varepsilon > 0$ there is a constant $C$ with
$\max_i |a_i| < C \cdot \operatorname{rad}(|a_1 \cdots a_n|)^{1 + \varepsilon}$ on $R(n)$.
For $n = 3$ this is the *abc* conjecture.

Hölzl, Kleine and Stephan state the conjecture as their Conjecture 7 and attribute it to
Ramaekers (2009, Conjecture 5.1). They prove it false for every $n \geq 5$ and remark that
disproving the case $n = 4$ "might be even harder than disproving the abc-conjecture".
Their statement has no exceptional algebraic set of the kind allowed by Vojta (1998).

This file specializes the statement to $n = 4$. The theorem `conjecture_false` asserts that
no uniform bound of the above form exists, and `qualityLimsup_ne_one` asserts that the limit
superior of the qualities over $R(4)$ is not $1$.

*References:*
- R. Hölzl, S. Kleine, F. Stephan, *Improved lower bounds for strong n-conjectures*,
  J. Aust. Math. Soc. 119 (2025), 61–81. [arXiv:2409.13439](https://arxiv.org/abs/2409.13439)
- C. Ramaekers, *The abc-conjecture and the n-conjecture*, Master's thesis, TU Eindhoven, 2009.
  [pure.tue.nl](https://pure.tue.nl/ws/portalfiles/portal/67739846/657782-1.pdf)
- P. Vojta, *A more general abc conjecture*, Int. Math. Res. Not. 1998 (1998), 1103–1116.
  [arXiv:math/9806171](https://arxiv.org/abs/math/9806171)
- [Wikipedia, n conjecture](https://en.wikipedia.org/wiki/n_conjecture)
-/

namespace StrongFour

/-- A $4$-tuple of integers $(a_1, a_2, a_3, a_4)$. -/
abbrev Tuple := Fin 4 → ℤ

/-- Condition (iii): no nonempty proper subsum of $a_1, \dots, a_4$ equals $0$, i.e.
$\sum_{i \in s} a_i \neq 0$ for every nonempty proper subset $s$ of the indices.
This forces every $a_i$ to be nonzero. -/
def NoVanishingSubsum (a : Tuple) : Prop :=
  ∀ s : Finset (Fin 4), s.Nonempty → s ≠ Finset.univ → ∑ i ∈ s, a i ≠ 0

/-- Membership in $R(4)$: (i) $a_1, \dots, a_4$ are pairwise coprime, (ii) $a_1 + \dots + a_4 = 0$,
and (iii) no nonempty proper subsum equals $0$. -/
def Admissible (a : Tuple) : Prop :=
  (Pairwise fun i j ↦ IsCoprime (a i) (a j)) ∧ ∑ i, a i = 0 ∧ NoVanishingSubsum a

/-- The height $\max(|a_1|, \dots, |a_4|)$. -/
def height (a : Tuple) : ℕ := Finset.univ.sup fun i ↦ (a i).natAbs

/-- The radical $\operatorname{rad}(|a_1 a_2 a_3 a_4|)$, the product of the distinct primes
dividing $a_1 a_2 a_3 a_4$. -/
noncomputable def rad (a : Tuple) : ℕ :=
  UniqueFactorizationMonoid.radical (∏ i, (a i).natAbs)

/-- The quality $q(a) = \log(\max_i |a_i|) / \log \operatorname{rad}(|a_1 a_2 a_3 a_4|)$.
For every admissible tuple the radical is at least $2$, so the denominator is positive. -/
noncomputable def quality (a : Tuple) : ℝ := Real.log (height a) / Real.log (rad a)

/-- The limit superior of the qualities over $R(4)$, taken along the cofinite filter on the
set of admissible tuples (equivalently, along $\max_i |a_i| \to \infty$ in $R(4)$).
It is valued in `EReal` so that an unbounded set of qualities has limit superior $+\infty$. -/
noncomputable def qualityLimsup : EReal :=
  Filter.limsup (fun a : {a : Tuple // Admissible a} ↦ (quality a.1 : EReal)) Filter.cofinite

/-- The uniform-bound formulation of the strong $4$ conjecture, as a proposition. -/
def Conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a : Tuple, Admissible a →
    (height a : ℝ) < C * (rad a : ℝ) ^ (1 + ε)

/-- Negation of the uniform-bound formulation of the strong $4$ conjecture: it is not the case
that for every $\varepsilon > 0$ there is a constant $C$ with
$$\max(|a_1|, |a_2|, |a_3|, |a_4|) < C \cdot \operatorname{rad}(|a_1 a_2 a_3 a_4|)^{1 + \varepsilon}$$
for all $(a_1, a_2, a_3, a_4) \in R(4)$. -/
theorem conjecture_false : ¬ Conjecture := by
  sorry

/-- Negation of the quality formulation of the strong $4$ conjecture (Hölzl–Kleine–Stephan,
Conjecture 7, case $n = 4$): the limit superior of the qualities over $R(4)$ is not $1$. -/
theorem qualityLimsup_ne_one : qualityLimsup ≠ 1 := by
  sorry

end StrongFour
