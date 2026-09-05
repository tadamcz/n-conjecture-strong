import StrongFour.Construction

/-!
# Admissibility and the degree gap

Along the explicit family, height is at least u⁹ and the radical is at most
a fixed positive constant times u⁸. No factorization of evaluated integers
and no conjectural estimate is used.
-/

namespace StrongFour

open Filter UniqueFactorizationMonoid

theorem factors_large (u : ℤ) (hu : 19 ≤ u) :
    1 < a u ∧ 1 < b u ∧ 1 < c u ∧ 1 < ell u ∧ 1 < d u := by
  have hu0 : 0 ≤ u := by omega
  have h2 : 0 ≤ u ^ 2 := sq_nonneg u
  have h4 : 0 ≤ u ^ 4 := by positivity
  have h3 : 0 ≤ (u - 19) * u ^ 2 := mul_nonneg (by omega) h2
  dsimp [a, b, c, ell, d]
  refine ⟨by omega, by omega, by nlinarith, by omega, ?_⟩
  nlinarith

theorem family_admissible (n : ℕ) : Admissible (family n) := by
  let u := parameter n
  obtain ⟨ha, hb, hc, hl, hd⟩ := factors_large u (parameter_ge n)
  apply admissible_of_coprime_of_sum
  · exact rawTuple_coprime u (parameter_mod n)
  · have := identity u
    change (∑ i, rawTuple u i) = 0
    simp [rawTuple, Fin.sum_univ_succ]
    linarith
  · have habs {z : ℤ} (hz : 1 < z) : 1 < z.natAbs := by
      have : (1 : ℤ) < (z.natAbs : ℤ) := by
        simpa only [Int.natCast_natAbs, abs_of_pos (lt_trans zero_lt_one hz)] using hz
      exact_mod_cast this
    have ha' := one_lt_pow₀ (habs ha) (by norm_num : (9 : ℕ) ≠ 0)
    have hb' := one_lt_pow₀ (habs hb) (by norm_num : (5 : ℕ) ≠ 0)
    have hc' := one_lt_pow₀ (habs hc) (by norm_num : (2 : ℕ) ≠ 0)
    have hl' := one_lt_pow₀ (habs hl) (by norm_num : (6 : ℕ) ≠ 0)
    intro i
    fin_cases i
    · change 1 < (a u ^ 9).natAbs
      simpa only [Int.natAbs_pow] using ha'
    · change 1 < (-(b u ^ 5 * c u ^ 2)).natAbs
      simp only [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_pow]
      nlinarith
    · change 1 < (-(105 * ell u ^ 6)).natAbs
      norm_num [Int.natAbs_mul, Int.natAbs_pow]
      omega
    · change 1 < (d u).natAbs
      exact habs hd

theorem parameter_tendsto : Tendsto (fun n ↦ (parameter n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ ↦ (n : ℝ)) _ tendsto_natCast_atTop_atTop
  intro n
  have := parameter_lower n
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  have : (n : ℤ) ≤ parameter n := by omega
  change (n : ℝ) ≤ (parameter n : ℝ)
  exact_mod_cast this

theorem height_lower (n : ℕ) : (parameter n : ℝ) ^ 9 ≤ (height (family n) : ℝ) := by
  let u := parameter n
  have hu : 0 ≤ u := le_trans (by norm_num) (parameter_ge n)
  have ha : u ≤ a u := by dsimp [a]; omega
  have hpow : u ^ 9 ≤ a u ^ 9 := pow_le_pow_left₀ hu ha 9
  have hfirst : (family n 0).natAbs ≤ height (family n) :=
    Finset.le_sup (f := fun i ↦ (family n i).natAbs) (Finset.mem_univ (0 : Fin 4))
  have heq : ((family n 0).natAbs : ℤ) = a u ^ 9 := by
    change ((a u ^ 9).natAbs : ℤ) = a u ^ 9
    rw [Int.natCast_natAbs, abs_of_nonneg (pow_nonneg (hu.trans ha) _)]
  have hcast : (u ^ 9 : ℤ) ≤ (height (family n) : ℤ) :=
    hpow.trans (by rw [← heq]; exact_mod_cast hfirst)
  exact_mod_cast hcast

private theorem factor_upper (u : ℤ) (hu : 19 ≤ u) :
    a u ≤ u ∧ b u ≤ u ∧ c u ≤ 301 * u ^ 2 ∧ d u ≤ 1249182732 * u ^ 4 := by
  have hu1 : 1 ≤ u := by omega
  refine ⟨by dsimp [a]; omega, by dsimp [b]; omega, ?_, ?_⟩
  · calc
      c u = u ^ 2 + 20 * u ^ 1 + 280 * u ^ 0 := by simp [c]
      _ ≤ u ^ 2 + 20 * u ^ 2 + 280 * u ^ 2 := by
        gcongr <;> first | exact hu1 | norm_num
      _ = 301 * u ^ 2 := by ring
  · calc
      d u ≤ 130032 * u ^ 4 + 10728480 * u ^ 3 + 1238324220 * u ^ 1 := by
        have := sq_nonneg u
        dsimp [d]
        nlinarith
      _ ≤ 130032 * u ^ 4 + 10728480 * u ^ 4 + 1238324220 * u ^ 4 := by
        gcongr <;> first | exact hu1 | norm_num
      _ = 1249182732 * u ^ 4 := by ring

private theorem radical_power_dvd (x n : ℕ) : radical (x ^ n) ∣ x := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [radical_pow x hn]
    exact radical_dvd_self

private theorem radical_product_dvd (a b c d K n : ℕ) :
    radical (a ^ 9 * (b ^ 5 * c ^ 2) * (105 * (35 * K ^ n) ^ 6) * d) ∣
      105 * 35 * K * a * b * c * d := by
  have hl : radical (35 * K ^ n) ∣ 35 * K :=
    radical_mul_dvd.trans (mul_dvd_mul radical_dvd_self (radical_power_dvd K n))
  have hl6 : radical ((35 * K ^ n) ^ 6) ∣ 35 * K := by
    rwa [radical_pow _ (by norm_num : (6 : ℕ) ≠ 0)]
  have h105 : radical (105 * (35 * K ^ n) ^ 6) ∣ 105 * (35 * K) :=
    radical_mul_dvd.trans (mul_dvd_mul radical_dvd_self hl6)
  have hbc : radical (b ^ 5 * c ^ 2) ∣ b * c :=
    radical_mul_dvd.trans (mul_dvd_mul (radical_power_dvd b 5) (radical_power_dvd c 2))
  have habc : radical (a ^ 9 * (b ^ 5 * c ^ 2)) ∣ a * (b * c) :=
    radical_mul_dvd.trans (mul_dvd_mul (radical_power_dvd a 9) hbc)
  have hall := radical_mul_dvd.trans (mul_dvd_mul
    (radical_mul_dvd.trans (mul_dvd_mul habc h105)) (radical_dvd_self (a := d)))
  convert hall using 1
  ring

/-- An explicit constant, independent of the sequence index. -/
def radicalConstant : ℝ := (105 * 35 * 301 * 1249182732) * (base : ℝ)

theorem radicalConstant_pos : 0 < radicalConstant := by
  have : (0 : ℝ) < base := by exact_mod_cast base_pos
  unfold radicalConstant
  positivity

theorem radical_upper (n : ℕ) :
    (rad (family n) : ℝ) ≤ radicalConstant * (parameter n : ℝ) ^ 8 := by
  let u := parameter n
  obtain ⟨ha, hb, hc, hl, hd⟩ := factors_large u (parameter_ge n)
  have hapos : 0 < a u := lt_trans zero_lt_one ha
  have hbpos : 0 < b u := lt_trans zero_lt_one hb
  have hcpos : 0 < c u := lt_trans zero_lt_one hc
  have hdpos : 0 < d u := lt_trans zero_lt_one hd
  have hdiv : rad (family n) ∣ 105 * 35 * base * (a u).natAbs * (b u).natAbs *
      (c u).natAbs * (d u).natAbs := by
    simpa [rad, family, rawTuple, Fin.prod_univ_succ, parameter_ell,
      Int.natAbs_mul, Int.natAbs_pow, mul_assoc, u] using
      radical_product_dvd (a u).natAbs (b u).natAbs (c u).natAbs (d u).natAbs base n
  have hbound : rad (family n) ≤ 105 * 35 * base * (a u).natAbs * (b u).natAbs *
      (c u).natAbs * (d u).natAbs := by
    apply Nat.le_of_dvd _ hdiv
    have := Int.natAbs_pos.mpr hapos.ne'
    have := Int.natAbs_pos.mpr hbpos.ne'
    have := Int.natAbs_pos.mpr hcpos.ne'
    have := Int.natAbs_pos.mpr hdpos.ne'
    have := base_pos
    positivity
  have hcast : (rad (family n) : ℝ) ≤ 105 * 35 * (base : ℝ) * (a u : ℝ) *
      (b u : ℝ) * (c u : ℝ) * (d u : ℝ) := by
    have hcast := (show (rad (family n) : ℝ) ≤
      (105 * 35 * base * (a u).natAbs * (b u).natAbs * (c u).natAbs * (d u).natAbs : ℕ) by
        exact_mod_cast hbound)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_natAbs,
      abs_of_pos hapos, abs_of_pos hbpos, abs_of_pos hcpos, abs_of_pos hdpos] using hcast
  obtain ⟨haU, hbU, hcU, hdU⟩ := factor_upper u (parameter_ge n)
  have haR : (a u : ℝ) ≤ (u : ℝ) := by exact_mod_cast haU
  have hbR : (b u : ℝ) ≤ (u : ℝ) := by exact_mod_cast hbU
  have hcR : (c u : ℝ) ≤ 301 * (u : ℝ) ^ 2 := by exact_mod_cast hcU
  have hdR : (d u : ℝ) ≤ 1249182732 * (u : ℝ) ^ 4 := by exact_mod_cast hdU
  have ha0 : (0 : ℝ) ≤ a u := by exact_mod_cast hapos.le
  have hb0 : (0 : ℝ) ≤ b u := by exact_mod_cast hbpos.le
  have hc0 : (0 : ℝ) ≤ c u := by exact_mod_cast hcpos.le
  have hd0 : (0 : ℝ) ≤ d u := by exact_mod_cast hdpos.le
  have hu0 : (0 : ℝ) ≤ u := by
    exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 19) (parameter_ge n))
  calc
    (rad (family n) : ℝ) ≤ 105 * 35 * (base : ℝ) * (a u : ℝ) *
        (b u : ℝ) * (c u : ℝ) * (d u : ℝ) := hcast
    _ ≤ 105 * 35 * (base : ℝ) * (u : ℝ) * (u : ℝ) *
        (301 * (u : ℝ) ^ 2) * (1249182732 * (u : ℝ) ^ 4) := by gcongr
    _ = radicalConstant * (parameter n : ℝ) ^ 8 := by dsimp [radicalConstant, u]; ring

end StrongFour
