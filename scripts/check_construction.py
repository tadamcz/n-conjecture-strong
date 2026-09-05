"""Independent exact-arithmetic checks; Lean remains the proof authority.

Requires SymPy (included in the Docker image). Reads the actual Lean
polynomials and certificates, rather than maintaining another coefficient list.
"""

from functools import reduce
from itertools import combinations
from math import gcd, lcm, log
from pathlib import Path
import re

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
source = (ROOT / "StrongFour/Construction.lean").read_text()
u = sp.Symbol("u")
names = ("a", "b", "c", "ell", "d")
polynomials = {}
for name in names:
    match = re.search(rf"def {name} \(u : ℤ\) : ℤ := ([^\n]+)", source)
    assert match, name
    polynomials[name] = sp.sympify(match[1].replace("^", "**"), locals={"u": u})
a, b, c, ell, d = (polynomials[name] for name in names)
assert sp.expand(a**9 - b**5 * c**2 - 105 * ell**6 + d) == 0
assert sp.degree(a**9, u) == 9
assert sp.degree(a * b * c * d, u) == 8
print("Exact identity and degree gap 9 versus 8: PASS")

modulus = int(re.search(r"def modulus : ℤ := (\d+)", source)[1])
constants = []
for name, body in re.findall(
    r"private theorem bezout_(\w+) \(u : ℤ\) :\s*(.*?) := by", source, re.S
):
    lhs, rhs = body.split("=")
    lhs = re.sub(r"\b(a|b|c|ell|d) u\b", r"\1", lhs).replace("^", "**")
    value = sp.sympify(lhs, locals=polynomials | {"u": u})
    constant = int(rhs)
    assert sp.expand(value - constant) == 0, name
    assert modulus % constant == 0, name
    constants.append(constant)
assert len(constants) == 9
assert modulus == lcm(105, *constants)
print("Nine Bézout certificates and common modulus: PASS")

base = 2 * modulus + 1
parameter = 19
for n in range(4):
    values = [int(p.subs(u, parameter)) for p in (a, b, c, ell, d)]
    av, bv, cv, lv, dv = values
    terms = [av**9, -(bv**5 * cv**2), -105 * lv**6, dv]
    assert parameter >= 19 and (parameter - 19) % modulus == 0
    assert lv == 35 * base**n
    assert all(abs(t) > 1 for t in terms)
    assert sum(terms) == 0
    assert all(gcd(x, y) == 1 for x, y in combinations(terms, 2))
    assert all(sum(t) != 0 for k in range(1, 4) for t in combinations(terms, k))
    assert reduce(gcd, terms) == 1
    # This bounds the radical from above; it does not factor the large values.
    radical_bound = 105 * 35 * base * av * bv * cv * dv
    quality_lower_bound = log(max(map(abs, terms))) / log(radical_bound)
    print(f"Family index {n}: admissibility PASS; quality >= {quality_lower_bound:.8f}")
    parameter = base * parameter - 3 * modulus

print("All independent checks passed.")
