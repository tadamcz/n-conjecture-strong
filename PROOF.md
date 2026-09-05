# The degree-nine construction

Write

\[
B(u)=u-8,\quad C(u)=u^2+20u+280,\quad L(u)=2u-3,
\]

and

\[
D(u)=130032u^4+10728480u^3-202978980u^2+1238324220u-2568934655.
\]

Direct expansion gives

\[
u^9-B(u)^5C(u)^2-105L(u)^6+D(u)=0. \tag{1}
\]

The four integers in the family are

\[
A(u)=\bigl(u^9,-B(u)^5C(u)^2,-105L(u)^6,D(u)\bigr).
\]

All the identities and inequalities used below are proved in the active
Lean project, without importing the archived conjecture declarations.

## Coprimality

For the following pairs of base polynomials, explicit integer-polynomial
Bézout identities have the indicated nonzero constant on the right:

| Pair | Bézout constant |
| --- | ---: |
| `u, B` | 8 |
| `u, C` | 280 |
| `u, L` | 3 |
| `u, D` | 2568934655 |
| `B, L` | 13 |
| `B, D` | 372597217 |
| `C, L` | 1249 |
| `C, D` | 2084099646478812202205 |
| `L, D` | 1131284123 |

The cofactors are written out in `StrongFour/Construction.lean` and checked
by `ring`. Coprimality of `B` and `C` is unnecessary: they occur in the same
entry of the four-tuple.

Let

\[
M=25126489963081279061731322208117706216604104298982120.
\]

This is the least common multiple of the nine displayed constants and 105.
The Lean proof needs only their divisibility into `M`, verified by exact
arithmetic; the independent Python check also verifies the least-common-multiple claim.

At `u = 19`, the five base values are

\[
19,\quad11,\quad1021,\quad35,\quad38216358337.
\]

Each required pair is coprime, and `u, B, C, D` are individually coprime to
105. These properties persist whenever `u ≡ 19 (mod M)`. Indeed, a common
divisor of a pair divides its Bézout constant, hence `M`; congruence then
makes it a divisor of both seed values. It must therefore be a unit.
The same reasoning applies to the constant factor 105. Taking powers and
multiplying the appropriate factors proves that the four entries of `A(u)`
are pairwise coprime.

## The infinite sequence

Set `K = 2M + 1` and

\[
u_n=\frac{35K^n+3}{2}.
\]

Since `K` is odd, these are integers. In Lean the sequence is defined without
division:

\[
u_0=19,\qquad u_{n+1}=K u_n-3M.
\]

The proof establishes

\[
u_n\geq n+19,\qquad u_n\equiv19\pmod M,\qquad L(u_n)=35K^n.
\]

Thus the parameters tend to infinity and every four-tuple is pairwise
coprime. All five base values exceed one for `u ≥ 19`. For the only less
immediate case, one can write

\[
D(u)=u^2\bigl(130032u^2+10728480(u-19)+862140\bigr)
      +1238324220u-2568934655>1.
\]

Equation (1) gives zero total sum. A vanishing proper subsum of four nonzero
entries could have size one, two, or three. Sizes one and three are impossible
by nonzeroness and zero total sum. Size two would give opposite entries,
contradicting their coprimality and magnitudes greater than one. Therefore
every `A(uₙ)` is admissible.

## Radical and height estimates

Let `Hₙ` be the maximum absolute entry and `Rₙ` the radical of the product.
The first entry immediately gives

\[
H_n\geq u_n^9.
\]

Removing powers from the radical and using `L(uₙ) = 35Kⁿ` gives

\[
R_n\mid105\cdot35\cdot K\cdot u_n B(u_n)C(u_n)D(u_n).
\]

For `u ≥ 19`, the elementary upper bounds

\[
B(u)\leq u,\qquad C(u)\leq301u^2,\qquad
D(u)\leq1249182732u^4
\]

therefore imply

\[
R_n\leq C_0u_n^8,\qquad
C_0=105\cdot35\cdot301\cdot1249182732\cdot K>0.
\]

No squarefreeness estimate for polynomial values is assumed. Only an upper
bound for the radical is needed.

For `0 ≤ ε < 1/8`, these bounds imply

\[
\frac{H_n}{R_n^{1+\varepsilon}}
\geq C_0^{-(1+\varepsilon)}u_n^{1-8\varepsilon}\longrightarrow\infty.
\]

Consequently no constant can give the conjectured uniform bound. The Lean
argument proves this using logarithms, and also proves that for every real
`q < 9/8`, eventually

\[
q<\frac{\log H_n}{\log R_n}.
\]

The denominator is eventually positive: a nonzero integer tuple of height
greater than one has radical greater than one. Height tending to infinity
also means this family leaves every finite set of tuples. The eventual
quality bounds thus imply the cofinite limsup over **all** admissible
four-tuples is at least `9/8`. They do not establish equality or convergence
of the actual qualities to `9/8`.

## How the identity was found

The binomial-series construction in
[Pakovich–Zvonkin, §3](https://arxiv.org/html/1509.07973)
with `(t,s,k) = (5,2,2)` gives

\[
P(x)=x^9,\qquad
Q(x)=(x-1)^5\left(x^2+\frac52x+\frac{35}{8}\right)^2.
\]

The difference has degree six. Subtracting
`(105/8)(x − 3/16)⁶` cancels its two highest-degree terms, leaving degree four.
Substitution `x = u/8` and multiplication by `8⁹` yield (1).

A bounded search through the binomial-series examples of total degree at
most 20 and the fork examples of total degree at most 24 found this family
with a suitable rational seed. The unsuccessful seed searches for smaller
examples are not impossibility proofs. The improvement over the supplied
`20/19` and `180/179` constructions is verified; optimality and publication
novelty are not claimed.

## Which conjecture is refuted

The admissibility conditions match
[Ramaekers's Conjecture 5.1](https://pure.tue.nl/ws/portalfiles/portal/67739846/657782-1.pdf#page=24),
also stated in [Hölzl–Kleine–Stephan, Conjecture 7](https://arxiv.org/html/2409.13439v2).
For `n = 4`, this is the statement displayed in
[Wikipedia's “Stronger form” section](https://en.wikipedia.org/wiki/N_conjecture#Stronger_form).
The Lean results refute both its uniform-bound and quality-limsup formulations.

The attribution to Vojta on Wikipedia needs a qualification.
[Vojta's 1998 paper, §2, following (2.5)](https://arxiv.org/html/math/9806171v1)
asserts the exponent `1 + ε` outside a proper Zariski-closed subset of the
zero-sum projective hyperplane. Its integer tuples have collective gcd one;
the paper does not replace the exceptional set by pairwise coprimality and
the absence of zero subsums.

For four coordinates the ambient space is the projective plane

\[
X=\{[a_1:a_2:a_3:a_4]\in\mathbb P^3:a_1+a_2+a_3+a_4=0\}.
\]

The map `u ↦ [A(u)]` is rational and nonconstant: for example, its coordinate
ratio `a₁/a₃ = -u⁹/(105(2u − 3)⁶)` is nonconstant. Its image therefore has
Zariski closure an irreducible algebraic curve `Y`, a proper subset of `X`.
Every point of the constructed sequence belongs to `Y`. The sequence gives
infinitely many distinct projective points, since its tuples are primitive
and their heights tend to infinity.

Vojta's exceptional set is allowed to contain `Y`. In fact, for any fixed
`0 < ε < 1/8`, a bound of his form would force its exceptional set to contain
`Y`: the eventual violations give infinitely many points on `Y`, whereas
a closed subset not containing an irreducible curve meets it in only
finitely many points. The subsum condition excludes certain hyperplanes;
it does not exclude this curve.

Thus this construction does not contradict Vojta's formulation. The curve
argument is an ordinary geometric explanation of the scope of the result,
not a formalized Lean theorem. Nothing here settles the three-variable
abc conjecture.
