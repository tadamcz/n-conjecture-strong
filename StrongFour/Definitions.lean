import Mathlib

/-!
# The strong four-conjecture

These definitions specialize the strong n-conjecture displayed on Wikipedia
to four integers. That source statement has no exceptional algebraic set.
See README.md for its distinction from Vojta's formulation and for literature references.
-/

namespace StrongFour

abbrev Tuple := Fin 4 → ℤ

def NoVanishingSubsum (a : Tuple) : Prop :=
  ∀ s : Finset (Fin 4), s.Nonempty → s ≠ Finset.univ → ∑ i ∈ s, a i ≠ 0

def Admissible (a : Tuple) : Prop :=
  (Pairwise fun i j ↦ IsCoprime (a i) (a j)) ∧ ∑ i, a i = 0 ∧ NoVanishingSubsum a

def height (a : Tuple) : ℕ := Finset.univ.sup fun i ↦ (a i).natAbs

noncomputable def rad (a : Tuple) : ℕ :=
  UniqueFactorizationMonoid.radical (∏ i, (a i).natAbs)

noncomputable def quality (a : Tuple) : ℝ := Real.log (height a) / Real.log (rad a)

/-- The cofinite filter discards finitely many tuples, not finitely many presentations. -/
noncomputable def qualityLimsup : EReal :=
  Filter.limsup (fun a : {a : Tuple // Admissible a} ↦ (quality a.1 : EReal)) Filter.cofinite

def Conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a : Tuple, Admissible a →
    (height a : ℝ) < C * (rad a : ℝ) ^ (1 + ε)

/-- For four pairwise coprime integers of magnitude greater than one,
the zero-sum condition already rules out every nonempty proper zero subsum. -/
theorem admissible_of_coprime_of_sum (a : Tuple)
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hsum : ∑ i, a i = 0) (habs : ∀ i, 1 < (a i).natAbs) : Admissible a := by
  classical
  refine ⟨hcop, hsum, ?_⟩
  have hne : ∀ i, a i ≠ 0 := fun i hi ↦ by simpa [hi] using habs i
  intro s hs hs' hz
  have hcpos := hs.card_pos
  have hclt : s.card < 4 := (Finset.card_lt_iff_ne_univ s).2 hs'
  have hcases : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with hc | hc | hc
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    exact hne i (by simpa using hz)
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hc
    have hpair : a i + a j = 0 := by simpa [hij] using hz
    have heq : a j = -a i := by linarith
    have h : IsCoprime (a i) (a j) := hcop hij
    rw [heq, IsCoprime.neg_right_iff, isCoprime_self, Int.isUnit_iff_natAbs_eq] at h
    exact (ne_of_gt (habs i)) h
  · have hccompl : sᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, hc]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hccompl
    have htotal := Finset.sum_add_sum_compl s a
    rw [hi, Finset.sum_singleton, hz, hsum, zero_add] at htotal
    exact hne i htotal

end StrongFour
