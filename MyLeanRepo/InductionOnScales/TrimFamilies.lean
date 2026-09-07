module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Trim tube families to uniform size via dyadic pigeonhole

Given per-square tube families of varying positive sizes bounded by `max_size`,
use dyadic pigeonhole to find a size band `[MΔ, 2·MΔ)` containing a
`1 / numDyadicLevels(max_size)` fraction of squares, then trim each family in
that band to exactly `MΔ` elements.

## Main result

`trim_families_to_uniform_size`: returns `MΔ`, a restricted `QSet'`,
and trimmed families of uniform size `MΔ`, preserving SSet (with constant
scaled by 2), incidence, parameter strip, and superset membership.

## Loss factors
- Square count retention: `|QSet| ≤ 2 * numDyadicLevels(max_size) * |QSet'|`
- SSet constant: factor 2 (from trimming at most half)

## Why trimming, not padding

Padding adds tubes outside the original fiber-uniform set `ctSub`, breaking the
cardinality estimate (5.5). Trimming keeps everything inside `ctSub`.

## Proof route

1. `exists_dyadic_size_subfamily` on family sizes finds `MΔ0` and `QSet0`
   with `MΔ0 ≤ |fam Q| < 2·MΔ0` for `Q ∈ QSet0`.
2. If `QSet0` is empty, fall back to a singleton `{Q0}` with `MΔ = |fam Q0|`.
3. For each selected `Q`, choose a subset `G_Q ⊆ fam Q` of size `MΔ`
   (`Finset.exists_subset_card_eq`).
4. SSet preservation: `|fam Q| < 2·MΔ = 2·|G_Q|`, so `subset_with_loss`
   gives constant `2·C`.
5. Retention bound: from `|QSet0| ≥ |QSet| / L` and remainder `< L`,
   derive `|QSet| ≤ 2·L·|QSet'|`.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

variable {m : ℕ}

/-- Arithmetic helper: if `s'.card ≥ s.card / L` with `L > 0` and `s'.Nonempty`,
then `(s.card : ℝ) ≤ 2 * (L : ℝ) * (s'.card : ℝ)`. -/
lemma dyadic_retention_bound {ι : Type*} [DecidableEq ι]
    (s s' : Finset ι) (L : ℕ) (hL_pos : 0 < L)
    (h_card : s.card / L ≤ s'.card) (h_s'_nonempty : s'.Nonempty) :
    (s.card : ℝ) ≤ (2 * (L : ℝ)) * (s'.card : ℝ) := by
  have h1 : s.card = (s.card / L) * L + s.card % L := by
    exact Eq.symm (Nat.div_add_mod' s.card L)
  have h2 : s.card % L < L := Nat.mod_lt _ hL_pos
  have h3 : 0 < s'.card := h_s'_nonempty.card_pos
  have h4 : L ≤ L * s'.card := Nat.le_mul_of_pos_right L h3
  have h5 : s.card % L ≤ L - 1 := by omega
  have h6 : L - 1 ≤ L * s'.card := by omega
  have h7 : s.card ≤ 2 * L * s'.card := by
    calc s.card
      = (s.card / L) * L + s.card % L := h1
    _ ≤ s'.card * L + (L - 1) := by gcongr <;> omega
    _ ≤ s'.card * L + L * s'.card := by gcongr
    _ = 2 * L * s'.card := by ring
  exact_mod_cast h7

/-- Trim per-square families to a uniform size via dyadic pigeonhole.

Given a family function `fam` meaningful on `QSet`, all subsets of `superset`
(e.g. `ctSub`), find `QSet' ⊆ QSet`, `MΔ > 0`, and trimmed families of size
exactly `MΔ`, preserving SSet (factor 2), incidence, strip, and superset
membership.

Square retention loss: `2 * numDyadicLevels(max_size)`. -/
lemma trim_families_to_uniform_size
    {s C : ℝ}
    (QSet : Finset (DyadicSquare m))
    (hQSet_nonempty : QSet.Nonempty)
    (fam : DyadicSquare m → Finset (DyadicTube m))
    (h_fam_nonempty : ∀ Q ∈ QSet, (fam Q).Nonempty)
    (h_fam_sset : ∀ Q ∈ QSet, IsFiniteTubeSSet s C (fam Q))
    (h_fam_incidence : ∀ Q ∈ QSet, ∀ U ∈ fam Q, (U.toSet ∩ Q.toSet).Nonempty)
    (h_fam_strip : ∀ Q ∈ QSet, ∀ U ∈ fam Q, U.IsInAllowedParameterStrip)
    (superset : Finset (DyadicTube m))
    (h_fam_sub : ∀ Q ∈ QSet, fam Q ⊆ superset)
    (max_size : ℕ) (hmax_pos : 0 < max_size)
    (h_max : ∀ Q ∈ QSet, (fam Q).card ≤ max_size) :
    ∃ (QSet' : Finset (DyadicSquare m))
      (MΔ : ℕ) (hMΔ_pos : 0 < MΔ)
      (trimmed : (Q : DyadicSquare m) → Q ∈ QSet' → Finset (DyadicTube m)),
      QSet' ⊆ QSet ∧
      (QSet.card : ℝ) ≤ (2 * numDyadicLevels max_size : ℝ) * (QSet'.card : ℝ) ∧
      (∀ Q hQ, trimmed Q hQ ⊆ fam Q) ∧
      (∀ Q hQ, (trimmed Q hQ).card = MΔ) ∧
      (∀ Q hQ, trimmed Q hQ ⊆ superset) ∧
      (∀ Q hQ, IsFiniteTubeSSet s (2 * C) (trimmed Q hQ)) ∧
      (∀ Q hQ U, U ∈ trimmed Q hQ → (U.toSet ∩ Q.toSet).Nonempty) ∧
      (∀ Q hQ U, U ∈ trimmed Q hQ → U.IsInAllowedParameterStrip) := by
  let f (Q : DyadicSquare m) : ℕ := (fam Q).card
  have h_bound : ∀ Q ∈ QSet, f Q ≤ max_size := h_max
  have h_pos : ∀ Q ∈ QSet, 0 < f Q := by
    intro Q hQ
    exact (h_fam_nonempty Q hQ).card_pos

  -- Step 1: dyadic pigeonhole on family sizes
  rcases exists_dyadic_size_subfamily QSet f hmax_pos h_bound h_pos with
    ⟨MΔ0, QSet0, hQSet0_sub, h_band, h_card0⟩

  -- Step 2: handle empty QSet0 by falling back to a singleton
  rcases hQSet_nonempty with ⟨Q0, hQ0⟩
  let QSet' : Finset (DyadicSquare m) :=
    if h : QSet0.Nonempty then QSet0 else {Q0}
  let MΔ : ℕ :=
    if h : QSet0.Nonempty then MΔ0 else f Q0

  have hQSet'_sub : QSet' ⊆ QSet := by
    dsimp only [QSet']
    split_ifs <;> simp [hQSet0_sub, hQ0] <;> tauto

  have h_band' : ∀ Q ∈ QSet', MΔ ≤ f Q ∧ f Q < 2 * MΔ := by
    intro Q hQ
    by_cases h : QSet0.Nonempty
    · have hQSet'_eq : QSet' = QSet0 := by
        dsimp only [QSet']; rw [dif_pos h]
      have hMΔ_eq : MΔ = MΔ0 := by
        dsimp only [MΔ]; rw [dif_pos h]
      have hQ0 : Q ∈ QSet0 := by
        rw [hQSet'_eq] at hQ; exact hQ
      rw [hMΔ_eq]
      exact h_band Q hQ0
    · have hQSet'_eq : QSet' = {Q0} := by
        dsimp only [QSet']; rw [dif_neg h]
      have hMΔ_eq : MΔ = f Q0 := by
        dsimp only [MΔ]; rw [dif_neg h]
      have hQ_eq : Q = Q0 := by
        rw [hQSet'_eq] at hQ
        exact Finset.mem_singleton.mp hQ
      rw [hMΔ_eq, hQ_eq]
      have hpos : 0 < f Q0 := h_pos Q0 hQ0
      exact ⟨by rfl, by linarith⟩

  have hQSet'_nonempty : QSet'.Nonempty := by
    dsimp only [QSet']
    split_ifs with h
    · exact h
    · exact Finset.singleton_nonempty Q0

  have hMΔ_pos : 0 < MΔ := by
    by_cases h : QSet0.Nonempty
    · have hMΔ_eq : MΔ = MΔ0 := by
        dsimp only [MΔ]; rw [dif_pos h]
      rw [hMΔ_eq]
      rcases h with ⟨Q, hQ⟩
      have h2 : MΔ0 ≤ f Q := (h_band Q hQ).1
      have h3 : 0 < f Q := h_pos Q (hQSet0_sub hQ)
      have h4 : f Q < 2 * MΔ0 := (h_band Q hQ).2
      by_contra h5
      have h6 : MΔ0 = 0 := by omega
      rw [h6] at h4
      omega
    · have hMΔ_eq : MΔ = f Q0 := by
        dsimp only [MΔ]; rw [dif_neg h]
      rw [hMΔ_eq]
      exact h_pos Q0 hQ0

  -- Step 3: retention bound
  let L := numDyadicLevels max_size
  have hL_pos : 0 < L := by simp [L, numDyadicLevels] <;> omega

  have h_retention : (QSet.card : ℝ) ≤ (2 * (L : ℝ)) * (QSet'.card : ℝ) := by
    dsimp only [QSet']
    split_ifs with h
    · -- QSet0 nonempty: use arithmetic helper
      exact dyadic_retention_bound QSet QSet0 L hL_pos h_card0 h
    · -- QSet0 empty: QSet.card < L, QSet' = {Q0}, card = 1
      have h_empty : QSet0 = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using h
      have h1 : QSet.card / L ≤ QSet0.card := h_card0
      rw [h_empty] at h1
      have h2 : QSet.card / L = 0 := Nat.eq_zero_of_le_zero h1
      have h3 : QSet.card < L := by
        exact (Nat.div_eq_zero_iff).mp h2 |>.resolve_left hL_pos.ne'
      have h4 : QSet.card ≤ 2 * L := by omega
      have h5 : (QSet.card : ℝ) ≤ (2 * (L : ℝ)) := by exact_mod_cast h4
      have h6 : ({Q0} : Finset (DyadicSquare m)).card = 1 := by simp
      rw [h6]
      <;> simpa using h5

  -- Step 4: choose trimmed subsets of size MΔ
  have h_choose : ∀ (Q : DyadicSquare m) (hQ : Q ∈ QSet'),
      ∃ (G_Q : Finset (DyadicTube m)), G_Q ⊆ fam Q ∧ G_Q.card = MΔ := by
    intro Q hQ
    have h1 : MΔ ≤ (fam Q).card := (h_band' Q hQ).1
    exact Finset.exists_subset_card_eq h1

  classical
  choose G_Q hG_Q_sub hG_Q_card using h_choose
  let trimmed (Q : DyadicSquare m) (hQ : Q ∈ QSet') : Finset (DyadicTube m) :=
    G_Q Q hQ

  have h_trimmed_sub : ∀ Q hQ, trimmed Q hQ ⊆ fam Q := by
    intro Q hQ
    exact hG_Q_sub Q hQ

  have h_trimmed_card : ∀ Q hQ, (trimmed Q hQ).card = MΔ := by
    intro Q hQ
    exact hG_Q_card Q hQ

  have h_trimmed_superset : ∀ Q hQ, trimmed Q hQ ⊆ superset := by
    intro Q hQ
    have hQ_in_QSet : Q ∈ QSet := hQSet'_sub hQ
    exact Finset.Subset.trans (h_trimmed_sub Q hQ) (h_fam_sub Q hQ_in_QSet)

  -- Step 5: SSet preservation with factor 2
  have h_trimmed_sset : ∀ Q hQ, IsFiniteTubeSSet s (2 * C) (trimmed Q hQ) := by
    intro Q hQ
    set F := fam Q with hF_def
    set G := trimmed Q hQ with hG_def
    have hG_sub : G ⊆ F := h_trimmed_sub Q hQ
    have hG_nonempty : G.Nonempty := by
      have h1 : G.card = MΔ := h_trimmed_card Q hQ
      exact Finset.card_pos.mp (by rw [h1] <;> exact hMΔ_pos)
    have h_size_bound : (F.card : ℝ) ≤ (2 : ℝ) * (G.card : ℝ) := by
      have h1 : f Q < 2 * MΔ := (h_band' Q hQ).2
      have h2 : G.card = MΔ := h_trimmed_card Q hQ
      have h3 : (F.card : ℝ) = (f Q : ℝ) := by rfl
      rw [h3, h2]
      exact_mod_cast h1.le
    have h_sset_F : IsFiniteTubeSSet s C F := h_fam_sset Q (hQSet'_sub hQ)
    have h : IsFiniteTubeSSet s (C * (2 : ℝ)) G :=
      IsFiniteTubeSSet.subset_with_loss h_sset_F hG_sub hG_nonempty h_size_bound
    have h_comm : C * (2 : ℝ) = 2 * C := by ring
    rw [h_comm] at h
    exact h

  have h_trimmed_incidence : ∀ Q hQ U, U ∈ trimmed Q hQ →
      (U.toSet ∩ Q.toSet).Nonempty := by
    intro Q hQ U hU
    have hQ_in_QSet : Q ∈ QSet := hQSet'_sub hQ
    have h_in_fam : U ∈ fam Q := h_trimmed_sub Q hQ hU
    exact h_fam_incidence Q hQ_in_QSet U h_in_fam

  have h_trimmed_strip : ∀ Q hQ U, U ∈ trimmed Q hQ →
      U.IsInAllowedParameterStrip := by
    intro Q hQ U hU
    have hQ_in_QSet : Q ∈ QSet := hQSet'_sub hQ
    have h_in_fam : U ∈ fam Q := h_trimmed_sub Q hQ hU
    exact h_fam_strip Q hQ_in_QSet U h_in_fam

  exact ⟨QSet', MΔ, hMΔ_pos, trimmed,
    hQSet'_sub, h_retention, h_trimmed_sub, h_trimmed_card,
    h_trimmed_superset, h_trimmed_sset, h_trimmed_incidence, h_trimmed_strip⟩

end InductionOnScales
