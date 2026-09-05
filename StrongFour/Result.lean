import StrongFour.Estimates

/-!
# Refutation of the strong four-conjecture

The same explicit family disproves every uniform exponent below 9/8 and
gives the lower bound 9/8 for the cofinite quality limsup.
-/

namespace StrongFour

open Filter

theorem family_height_tendsto : Tendsto (fun n ↦ height (family n)) atTop atTop := by
  have hreal : Tendsto (fun n ↦ (height (family n) : ℝ)) atTop atTop :=
    tendsto_atTop_mono height_lower
    ((tendsto_pow_atTop (by norm_num : (9 : ℕ) ≠ 0)).comp parameter_tendsto)
  exact tendsto_natCast_atTop_iff.mp hreal

private theorem eventually_rad_gt_one : ∀ᶠ n : ℕ in atTop, 1 < (rad (family n) : ℝ) := by
  filter_upwards [family_height_tendsto.eventually_gt_atTop 1] with n hn
  have hne (i : Fin 4) : family n i ≠ 0 := by
    simpa only [Finset.sum_singleton] using
      (family_admissible n).2.2 {i} (Finset.singleton_nonempty i) (Finset.singleton_ne_univ i)
  have hprod : height (family n) ≤ ∏ i, (family n i).natAbs := by
    apply Finset.sup_le
    intro i hi
    exact Finset.single_le_prod'
      (fun j _ ↦ Nat.succ_le_of_lt (Int.natAbs_pos.mpr (hne j))) hi
  have : 1 < rad (family n) := Nat.one_lt_radical_iff.mpr (hn.trans_le hprod)
  exact_mod_cast this

/-- The height/radical ratio is unbounded for every exponent below 9/8. -/
theorem eventually_exceeds (s C : ℝ) (hs : 0 ≤ s) (hs' : s < 9 / 8) :
    ∀ᶠ n : ℕ in atTop, C * (rad (family n) : ℝ) ^ s < (height (family n) : ℝ) := by
  let C' := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  have hgap : 0 < 9 - 8 * s := by linarith
  have hgrowth : Tendsto (fun n ↦ (9 - 8 * s) * Real.log (parameter n : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp parameter_tendsto).const_mul_atTop hgap
  filter_upwards [eventually_rad_gt_one,
    hgrowth.eventually_gt_atTop (Real.log C' + s * Real.log radicalConstant)] with n hr hlarge
  have hu : (0 : ℝ) < parameter n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 19) (parameter_ge n))
  have hr0 : (0 : ℝ) < rad (family n) := lt_trans zero_lt_one hr
  have hH0 : (0 : ℝ) < height (family n) := (pow_pos hu 9).trans_le (height_lower n)
  have hlogH := Real.log_le_log (pow_pos hu 9) (height_lower n)
  have hlogR := Real.log_le_log hr0 (radical_upper n)
  rw [Real.log_pow] at hlogH
  rw [Real.log_mul radicalConstant_pos.ne' (pow_ne_zero _ hu.ne'), Real.log_pow] at hlogR
  norm_num only [Nat.cast_ofNat] at hlogH hlogR
  have hmul := mul_le_mul_of_nonneg_left hlogR hs
  have hlog : Real.log (C' * (rad (family n) : ℝ) ^ s) < Real.log (height (family n)) := by
    rw [Real.log_mul hC'.ne' (Real.rpow_pos_of_pos hr0 s).ne', Real.log_rpow hr0]
    nlinarith only [hlogH, hmul, hlarge]
  have hlt := (Real.log_lt_log_iff (mul_pos hC' (Real.rpow_pos_of_pos hr0 s)) hH0).mp hlog
  exact (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.rpow_nonneg hr0.le s)).trans_lt hlt

/-- In particular every positive ε < 1/8 fails in the usual formulation.
The endpoint ε = 0 is included as well. -/
theorem no_uniform_bound (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε < 1 / 8) :
    ¬ ∃ C : ℝ, ∀ a : Tuple, Admissible a →
      (height a : ℝ) < C * (rad a : ℝ) ^ (1 + ε) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := (eventually_exceeds (1 + ε) C (by linarith) (by linarith)).exists
  exact lt_asymm hn (hC _ (family_admissible n))

theorem conjecture_false : ¬ Conjecture := by
  intro h
  exact no_uniform_bound (1 / 16) (by norm_num) (by norm_num) (h (1 / 16) (by norm_num))

/-- Every threshold strictly below 9/8 is eventually exceeded by the family. -/
theorem eventually_quality_gt (q : ℝ) (hq : q < 9 / 8) :
    ∀ᶠ n : ℕ in atTop, q < quality (family n) := by
  have hq' : max q 0 < (9 / 8 : ℝ) := max_lt hq (by norm_num)
  filter_upwards [eventually_exceeds (max q 0) 1 (le_max_right _ _) hq',
    eventually_rad_gt_one] with n hn hr
  rw [one_mul] at hn
  have hlog := Real.log_lt_log (Real.rpow_pos_of_pos (lt_trans zero_lt_one hr) _) hn
  rw [Real.log_rpow (lt_trans zero_lt_one hr)] at hlog
  exact (le_max_left q 0).trans_lt ((lt_div_iff₀ (Real.log_pos hr)).mpr hlog)

/-- This is a lower bound, not a claim that the limsup equals 9/8. -/
theorem qualityLimsup_ge : ((9 / 8 : ℝ) : EReal) ≤ qualityLimsup := by
  let f : ℕ → {a : Tuple // Admissible a} := fun n ↦ ⟨family n, family_admissible n⟩
  have hcof : Tendsto f atTop cofinite := by
    apply Filter.le_cofinite_iff_eventually_ne.mpr
    intro a
    change ∀ᶠ n in atTop, f n ≠ a
    filter_upwards [family_height_tendsto.eventually_gt_atTop (height a.1)] with n hn
    intro heq
    exact (ne_of_gt hn) (congrArg (fun b ↦ height b.1) heq)
  by_contra h
  obtain ⟨q, hqL, hq⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hq' : q < (9 / 8 : ℝ) := EReal.coe_lt_coe_iff.mp hq
  have hle : (q : EReal) ≤ qualityLimsup := by
    apply Filter.le_limsup_of_frequently_le'
    apply hcof.frequently
    exact (eventually_quality_gt q hq').frequently.mono fun n hn ↦
      EReal.coe_le_coe_iff.mpr hn.le
  exact not_le_of_gt hqL hle

theorem qualityLimsup_ne_one : qualityLimsup ≠ 1 := by
  have h : (1 : EReal) < ((9 / 8 : ℝ) : EReal) := by
    exact_mod_cast (show (1 : ℝ) < 9 / 8 by norm_num)
  exact (h.trans_le qualityLimsup_ge).ne'

end StrongFour
