# Strong n-conjecture (Vojta): n = 4 refutations

Data from a Hawk autoformalization eval run (`wikipedia-autoformalized-v-mn0wtzf7uda6y0dc`). Two formulations of the
*strong n-conjecture*, both stated for n in {3,4}; each submission refutes only the n = 4
instance and leaves n = 3 (the abc conjecture) untouched.

- `first-formulation/` - sample `NConjecture.n_conjecture.variants.strong` (uuid `h7sLgxyz42JWYDEkwtPQpa`), scored C / disproof. Quality tends to 20/19 via a Beukers-Stewart (5,2) Davenport-Zannier pair.
- `quality-formulation/` - sample `NConjecture.n_conjecture.variants.strong_quality` (uuid `DPumQDXkoXpfGod6xePoVD`), scored C / disproof. limsup quality >= 1080/1074 via a degree-45 curve on x^4 + y^4 = z^4 + w^4 with a forced square factor.

Combined into one repo because they are two independent proofs of the same fact: the strong
4-conjecture is false. See each subdirectory's `ANALYSIS.md`.
