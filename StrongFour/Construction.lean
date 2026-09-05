import StrongFour.Definitions

/-!
# A degree-nine counterexample family

The identity comes from the (t,s,k) = (5,2,2) binomial-series construction
in Pakovich–Zvonkin, arXiv:1509.07973, §3. After setting x = u/8,
subtract the leading sixth power of the centered remainder. What remains
has degree four. Every identity below is checked by Lean's kernel.
-/

namespace StrongFour

def a (u : ℤ) : ℤ := u

def b (u : ℤ) : ℤ := u - 8

def c (u : ℤ) : ℤ := u ^ 2 + 20 * u + 280

def ell (u : ℤ) : ℤ := 2 * u - 3

def d (u : ℤ) : ℤ := 130032 * u ^ 4 + 10728480 * u ^ 3 - 202978980 * u ^ 2 + 1238324220 * u - 2568934655

def rawTuple (u : ℤ) : Tuple := ![a u ^ 9, -(b u ^ 5 * c u ^ 2), -(105 * ell u ^ 6), d u]

theorem identity (u : ℤ) : a u ^ 9 - b u ^ 5 * c u ^ 2 - 105 * ell u ^ 6 + d u = 0 := by
  unfold a b c ell d
  ring

/-- A common multiple of 105 and the nine Bézout constants below. -/
def modulus : ℤ := 25126489963081279061731322208117706216604104298982120

theorem modulus_pos : 0 < modulus := by norm_num [modulus]

private theorem isCoprime_of_bezout_modEq {x y x₀ y₀ c m U V : ℤ}
    (hbez : U * x + V * y = c) (hcm : c ∣ m)
    (hx : x ≡ x₀ [ZMOD m]) (hy : y ≡ y₀ [ZMOD m])
    (hseed : IsCoprime x₀ y₀) : IsCoprime x y := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  have hdx := Int.gcd_dvd_left x y
  have hdy := Int.gcd_dvd_right x y
  have hdc : (Int.gcd x y : ℤ) ∣ c := by
    rw [← hbez]
    exact dvd_add (dvd_mul_of_dvd_right hdx U) (dvd_mul_of_dvd_right hdy V)
  have hdm : (Int.gcd x y : ℤ) ∣ m := hdc.trans hcm
  have hdx₀ : (Int.gcd x y : ℤ) ∣ x₀ := (hx.of_dvd hdm).dvd_iff.mp hdx
  have hdy₀ : (Int.gcd x y : ℤ) ∣ y₀ := (hy.of_dvd hdm).dvd_iff.mp hdy
  have hdseed := Int.dvd_gcd hdx₀ hdy₀
  rw [Int.isCoprime_iff_gcd_eq_one.mp hseed] at hdseed
  exact Nat.dvd_one.mp hdseed

/-- The constant-polynomial instance of the seed argument. -/
private theorem isCoprime_constant_of_modEq {x x₀ c m : ℤ}
    (hcm : c ∣ m) (hx : x ≡ x₀ [ZMOD m]) (hseed : IsCoprime x₀ c) :
    IsCoprime x c :=
  isCoprime_of_bezout_modEq (U := 0) (V := 1) (by ring) hcm hx
    Int.ModEq.rfl hseed

private theorem a_mod (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    a u ≡ a 19 [ZMOD modulus] := by
  unfold a
  gcongr

private theorem b_mod (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    b u ≡ b 19 [ZMOD modulus] := by
  unfold b
  gcongr

private theorem c_mod (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    c u ≡ c 19 [ZMOD modulus] := by
  unfold c
  gcongr

private theorem ell_mod (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    ell u ≡ ell 19 [ZMOD modulus] := by
  unfold ell
  gcongr

private theorem d_mod (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    d u ≡ d 19 [ZMOD modulus] := by
  unfold d
  gcongr

private theorem bezout_a_b (u : ℤ) :
    (1) * a u + (-1) * b u = 8 := by
  unfold a b
  ring

private theorem coprime_a_b (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (a u) (b u) :=
  isCoprime_of_bezout_modEq (m := modulus) (bezout_a_b u)
    (by norm_num [modulus]) (a_mod u hu) (b_mod u hu)
    (by norm_num [a, b])

private theorem bezout_a_c (u : ℤ) :
    (-u - 20) * a u + (1) * c u = 280 := by
  unfold a c
  ring

private theorem coprime_a_c (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (a u) (c u) :=
  isCoprime_of_bezout_modEq (m := modulus) (bezout_a_c u)
    (by norm_num [modulus]) (a_mod u hu) (c_mod u hu)
    (by norm_num [a, c])

private theorem bezout_a_ell (u : ℤ) :
    (2) * a u + (-1) * ell u = 3 := by
  unfold a ell
  ring

private theorem coprime_a_ell (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (a u) (ell u) :=
  isCoprime_of_bezout_modEq (m := modulus) (bezout_a_ell u)
    (by norm_num [modulus]) (a_mod u hu) (ell_mod u hu)
    (by norm_num [a, ell])

private theorem bezout_a_d (u : ℤ) :
    (130032 * u ^ 3 + 10728480 * u ^ 2 - 202978980 * u + 1238324220) * a u + (-1) * d u = 2568934655 := by
  unfold a d
  ring

private theorem coprime_a_d (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (a u) (d u) :=
  isCoprime_of_bezout_modEq (m := modulus) (bezout_a_d u)
    (by norm_num [modulus]) (a_mod u hu) (d_mod u hu)
    (by norm_num [a, d])

private theorem bezout_b_ell (u : ℤ) :
    (-2) * b u + (1) * ell u = 13 := by
  unfold b ell
  ring

private theorem coprime_b_ell (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (b u) (ell u) :=
  isCoprime_of_bezout_modEq (m := modulus) (bezout_b_ell u)
    (by norm_num [modulus]) (b_mod u hu) (ell_mod u hu)
    (by norm_num [b, ell])

private theorem bezout_b_d (u : ℤ) :
    (-130032 * u ^ 3 - 11768736 * u ^ 2 + 108829092 * u - 367691484) * b u + (1) * d u = 372597217 := by
  unfold b d
  ring

private theorem coprime_b_d (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (b u) (d u) :=
  isCoprime_of_bezout_modEq (m := modulus) (bezout_b_d u)
    (by norm_num [modulus]) (b_mod u hu) (d_mod u hu)
    (by norm_num [b, d])

private theorem bezout_c_ell (u : ℤ) :
    (4) * c u + (-2 * u - 43) * ell u = 1249 := by
  unfold c ell
  ring

private theorem coprime_c_ell (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (c u) (ell u) :=
  isCoprime_of_bezout_modEq (m := modulus) (bezout_c_ell u)
    (by norm_num [modulus]) (c_mod u hu) (ell_mod u hu)
    (by norm_num [c, ell])

private theorem bezout_c_d (u : ℤ) :
    (182081828432448 * u ^ 3 + 12162857834916432 * u ^ 2 - 513984089089536720 * u + 7388067383983043940) * c u + (-1400284764 * u - 6010576771) * d u = 2084099646478812202205 := by
  unfold c d
  ring

private theorem coprime_c_d (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (c u) (d u) :=
  isCoprime_of_bezout_modEq (m := modulus) (bezout_c_d u)
    (by norm_num [modulus]) (c_mod u hu) (d_mod u hu)
    (by norm_num [c, d])

private theorem bezout_ell_d (u : ℤ) :
    (65016 * u ^ 3 + 5461764 * u ^ 2 - 93296844 * u + 479216844) * ell u + (-1) * d u = 1131284123 := by
  unfold ell d
  ring

private theorem coprime_ell_d (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (ell u) (d u) :=
  isCoprime_of_bezout_modEq (m := modulus) (bezout_ell_d u)
    (by norm_num [modulus]) (ell_mod u hu) (d_mod u hu)
    (by norm_num [ell, d])

private theorem coprime_a_105 (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (a u) (105 : ℤ) :=
  isCoprime_constant_of_modEq (by norm_num [modulus]) (a_mod u hu)
    (by norm_num [a])

private theorem coprime_b_105 (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (b u) (105 : ℤ) :=
  isCoprime_constant_of_modEq (by norm_num [modulus]) (b_mod u hu)
    (by norm_num [b])

private theorem coprime_c_105 (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (c u) (105 : ℤ) :=
  isCoprime_constant_of_modEq (by norm_num [modulus]) (c_mod u hu)
    (by norm_num [c])

private theorem coprime_d_105 (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    IsCoprime (d u) (105 : ℤ) :=
  isCoprime_constant_of_modEq (by norm_num [modulus]) (d_mod u hu)
    (by norm_num [d])

private theorem pairwise_coprime_four {x₀ x₁ x₂ x₃ : ℤ}
    (h01 : IsCoprime x₀ x₁) (h02 : IsCoprime x₀ x₂) (h03 : IsCoprime x₀ x₃)
    (h12 : IsCoprime x₁ x₂) (h13 : IsCoprime x₁ x₃) (h23 : IsCoprime x₂ x₃) :
    Pairwise fun i j : Fin 4 => IsCoprime (![x₀, x₁, x₂, x₃] i) (![x₀, x₁, x₂, x₃] j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals first
    | exact h01.symm
    | exact h02.symm
    | exact h03.symm
    | exact h12.symm
    | exact h13.symm
    | exact h23.symm

theorem rawTuple_coprime (u : ℤ) (hu : u ≡ 19 [ZMOD modulus]) :
    Pairwise fun i j ↦ IsCoprime (rawTuple u i) (rawTuple u j) := by
  apply pairwise_coprime_four
  · exact ((coprime_a_b u hu).pow.mul_right (coprime_a_c u hu).pow).neg_right
  · exact ((coprime_a_105 u hu).pow_left.mul_right (coprime_a_ell u hu).pow).neg_right
  · exact (coprime_a_d u hu).pow_left
  · exact (((coprime_b_105 u hu).pow_left.mul_right (coprime_b_ell u hu).pow).mul_left
      ((coprime_c_105 u hu).pow_left.mul_right (coprime_c_ell u hu).pow)).neg_neg
  · exact ((coprime_b_d u hu).pow_left.mul_left (coprime_c_d u hu).pow_left).neg_left
  · exact ((coprime_d_105 u hu).symm.mul_left (coprime_ell_d u hu).pow_left).neg_left

/-- A fixed base, congruent to one modulo twice the modulus. -/
def base : ℕ := 2 * modulus.natAbs + 1

theorem base_pos : 0 < base := by unfold base; omega

theorem base_cast : (base : ℤ) = 2 * modulus + 1 := by
  simp only [base, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Int.natCast_natAbs, abs_of_pos modulus_pos]

/-- Division-free version of uₙ = (35 baseⁿ + 3)/2. -/
def parameter : ℕ → ℤ
  | 0 => 19
  | n + 1 => (2 * modulus + 1) * parameter n - 3 * modulus

theorem parameter_lower (n : ℕ) : (n : ℤ) + 19 ≤ parameter n := by
  induction n with
  | zero => norm_num [parameter]
  | succ n ih =>
    have hM : 1 ≤ modulus := modulus_pos
    have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    simp only [parameter, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem parameter_ge (n : ℕ) : 19 ≤ parameter n := by
  have := parameter_lower n
  have := Nat.cast_nonneg (α := ℤ) n
  omega

theorem parameter_mod (n : ℕ) : parameter n ≡ 19 [ZMOD modulus] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hM : modulus ≡ 0 [ZMOD modulus] := Int.modEq_zero_iff_dvd.mpr dvd_rfl
    simpa only [parameter, mul_zero, zero_add, one_mul, sub_zero] using
      ((hM.mul_left 2 |>.add Int.ModEq.rfl).mul ih).sub (hM.mul_left 3)

theorem parameter_ell (n : ℕ) : ell (parameter n) = 35 * (base : ℤ) ^ n := by
  induction n with
  | zero => norm_num [parameter, ell]
  | succ n ih =>
    have heq : ell (parameter (n + 1)) = (2 * modulus + 1) * ell (parameter n) := by
      simp only [parameter, ell]
      ring
    rw [heq, ih, base_cast, pow_succ]
    ring

def family (n : ℕ) : Tuple := rawTuple (parameter n)

end StrongFour
