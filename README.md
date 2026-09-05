> **Note.** This entire repository was machine-written by AI assistants at the direction of Tom Adamczewski. The Lean proof itself was written by GPT-6 Astra, as described below.

# A counterexample to the strong four-conjecture

A standalone Lean proof that the [strong four-conjecture](https://en.wikipedia.org/wiki/N_conjecture#Stronger_form) is false:

\[
\limsup_{\substack{a_1+\cdots+a_4=0\\
\text{pairwise coprime, no proper zero subsum}}}
\frac{\log\max_i|a_i|}{\log\operatorname{rad}(|a_1a_2a_3a_4|)}
\;\geq\;\frac98.
\]

The same family disproves every uniform bound
`max |aᵢ| < C · rad(∏ |aᵢ|)^(1 + ε)` for `0 ≤ ε < 1/8`.
The conclusion concerns **four integers only** and does not settle the
three-variable abc conjecture.

## Attribution and relation to Vojta

The statement refuted here is the `n = 4` case of the strong n-conjecture
displayed in Wikipedia's “Stronger form” section. The same statement appears
in [Coen Ramaekers's 2009 thesis, Conjecture 5.1](https://pure.tue.nl/ws/portalfiles/portal/67739846/657782-1.pdf#page=24),
and [Hölzl–Kleine–Stephan, Conjecture 7](https://arxiv.org/html/2409.13439v2)
attribute this formulation to Ramaekers: pairwise coprime integers, zero
total sum, no nonempty proper zero subsum, and quality limsup equal to one.

Wikipedia attributes its displayed statement to Vojta, but
[Vojta's 1998 paper, §2, following (2.5)](https://arxiv.org/html/math/9806171v1)
allows a **proper Zariski-closed exceptional set**. His bound applies outside
that set to tuples with collective gcd one; it does not assert that pairwise
coprimality and the subsum condition eliminate all exceptions.

An exceptional set can contain an entire algebraic curve, not just finitely
many points. Our family depends on one parameter and lies on such a curve
in the projective plane `a₁ + a₂ + a₃ + a₄ = 0`. Vojta's formulation can
exclude this curve. Thus the proof **refutes the statement displayed on
Wikipedia for four integers, but does not refute Vojta's formulation with
an exceptional set**. See [PROOF.md](PROOF.md#which-conjecture-is-refuted)
for the geometric distinction.

## The proof

Import [StrongFour.lean](StrongFour.lean). The main results are in
[StrongFour/Result.lean](StrongFour/Result.lean):

- `StrongFour.no_uniform_bound`: failure for every `0 ≤ ε < 1/8`.
- `StrongFour.conjecture_false`: negation of the four-variable statement above.
- `StrongFour.qualityLimsup_ge`: the lower bound `9/8`.
- `StrongFour.qualityLimsup_ne_one`: refutation of the quality formulation.

The construction is the integer identity

\[
u^9-(u-8)^5(u^2+20u+280)^2-105(2u-3)^6+D(u)=0,
\]

where

\[
D(u)=130032u^4+10728480u^3-202978980u^2+1238324220u-2568934655.
\]

A congruence progression ensures pairwise coprimality. On the subsequence
`2u − 3 = 35 Kⁿ`, the radical of the third term has bounded prime support.
The height grows at least as `u⁹`, while the radical is bounded by a constant
times `u⁸`. See [PROOF.md](PROOF.md) for the mathematical argument, explicit
constants, and provenance.

This improves the two input submissions' bounds, `20/19` and `180/179`, and
replaces both constructions with one degree-nine family. `9/8` is a **lower
bound**, not a claim of equality or optimality. Novelty in the literature has
not been established.

## Reproduce with Docker

The image is built from public Debian, Elan, and Mathlib sources. Both Lean
and Mathlib are pinned:

- Lean `4.27.0`.
- Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
- Transitive dependencies are pinned in [lake-manifest.json](lake-manifest.json).

```sh
docker build -t strong-four-proof:lean4.27 .
docker run --rm strong-four-proof:lean4.27 bash scripts/check.sh
```

The build itself runs the arithmetic checks and compiles every proof module.
The first build downloads Lean and the Mathlib cache; subsequent builds reuse
those layers.

To create an editable working container from the verified image, with build
files isolated from the host:

```sh
docker run -d --name strong-four-lean \
  --mount type=bind,source="$PWD",target=/work \
  --mount type=volume,target=/work/.lake \
  --workdir /work strong-four-proof:lean4.27 \
  bash -c 'ln -s /opt/strong-four/.lake/packages /work/.lake/packages; exec sleep infinity'
docker exec strong-four-lean bash scripts/check.sh
```

## Reproduce without Docker

With Elan installed, from this directory:

```sh
lake exe cache get
lake build
```

The optional independent check requires Python and SymPy:

```sh
python3 scripts/check_construction.py
```

It verifies the identity, all nine Bézout certificates, the modulus, and
several large members of the family directly from the Lean coefficients.
These computations supplement the Lean proof; they are not trusted axioms.

## Layout

| File | Purpose |
| --- | --- |
| `StrongFour/Definitions.lean` | Four-variable statement and admissibility |
| `StrongFour/Construction.lean` | Identity, coprimality certificates, sequence |
| `StrongFour/Estimates.lean` | Admissibility, height and radical bounds |
| `StrongFour/Result.lean` | Uniform-bound and limsup conclusions |
| `scripts/check_construction.py` | Independent exact arithmetic |
| `archive/` | Original evaluation artifacts, excluded from the build |
