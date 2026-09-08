/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Multiplicity

/-!
# The spine cardinality dichotomy of Main Lemma 2
-/

@[expose] public section

open MeasureTheory ShadedBody

namespace Kakeya.MainLemma2.Reduction

/-! ### Arithmetic spine -/

/-- **`δ ^ (-γ) ≤ N ^ γ` as soon as `δ⁻¹ ≤ N`.** -/
theorem rpow_neg_le_rpow_of_inv_le {d N : ENNReal} {γ : ℝ} (hγ : 0 ≤ γ) (h : d⁻¹ ≤ N) :
    d ^ (-γ) ≤ N ^ γ := by
  rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow]
  exact ENNReal.rpow_le_rpow h hγ

/-- Bridge: a real cardinality lower bound `δ⁻¹ ≤ N` becomes the `ℝ≥0∞` one. -/
theorem coe_inv_le_natCast {δ : NNReal} (hδ : 0 < δ) {n : ℕ} (h : (δ : ℝ)⁻¹ ≤ (n : ℝ)) :
    (δ : ENNReal)⁻¹ ≤ (n : ENNReal) := by
  rw [← ENNReal.coe_inv hδ.ne']
  rw [show ((n : ENNReal)) = ((n : NNReal) : ENNReal) by simp]
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa using h

/-- Bridge: a real cardinality upper bound `N ≤ δ ^ (-θ)` becomes the `ℝ≥0∞` one. -/
theorem natCast_le_coe_rpow {δ : NNReal} (hδ : 0 < δ) {θ : ℝ} {n : ℕ}
    (h : (n : ℝ) ≤ (δ : ℝ) ^ (-θ)) : (n : ENNReal) ≤ (δ : ENNReal) ^ (-θ) := by
  rw [← ENNReal.coe_rpow_of_ne_zero hδ.ne']
  rw [show ((n : ENNReal)) = ((n : NNReal) : ENNReal) by simp]
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa [NNReal.coe_rpow] using h


/-! ### Elementary cardinality/multiplicity facts -/

section Multiplicity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **The trivial mass bound.**  This is `ShadedBody.multiplicity_le_card` read through
`ShadedBody.multiplicity_le_iff`. -/
theorem sum_shade_le_card_mul_iUnion (s : Finset ι) (V : ι → ShadedBody E) :
    ∑ i ∈ s, volume (V i).shade ≤ (s.card : ENNReal) * volume (⋃ i ∈ s, (V i).shade) :=
  (ShadedBody.multiplicity_le_iff s V).mp (ShadedBody.multiplicity_le_card s V)

/-- **The trivial mass bound is attained.** -/
theorem multiplicity_const (s : Finset ι) (hs : s.Nonempty) (V₀ : ShadedBody E)
    (hv : volume V₀.shade ≠ 0) :
    ShadedBody.multiplicity s (fun _ ↦ V₀) = (s.card : ENNReal) := by
  have hvtop : volume V₀.shade ≠ ⊤ :=
    ne_top_of_le_ne_top V₀.isCompact.measure_ne_top (measure_mono V₀.shade_subset)
  have hU : (⋃ i ∈ s, ((fun _ : ι ↦ V₀) i).shade) = V₀.shade := by
    have : ((s : Set ι)).Nonempty := by simpa using hs
    simpa using Set.biUnion_const this V₀.shade
  rw [ShadedBody.multiplicity_eq_div, hU, Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_div_cancel_right hv hvtop

end Multiplicity


/-! ### The two branches of the cardinality dichotomy -/

section Branches

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **Small-cardinality branch.** -/
theorem katzTaoGoal_of_card_le_rpow {s : Finset ι} {V : ι → ShadedBody E} {δ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε γ θ : ℝ} (hγ1 : γ ≤ 1)
    (hcost : θ * (1 - γ) ≤ ε) (hcard : (s.card : ℝ) ≤ (δ : ℝ) ^ (-θ)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (V i).shade) := by
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]
    simp
  have hN0 : (s.card : ENNReal) ≠ 0 := by
    simpa using hpos.ne'
  have hNtop : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hd1 : (δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1
  -- `N ^ (1 - γ) ≤ δ ^ (-ε)`
  have hstep : (s.card : ENNReal) ^ (1 - γ) ≤ (δ : ENNReal) ^ (-ε) := by
    have h1 : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-θ) := natCast_le_coe_rpow hδ hcard
    calc (s.card : ENNReal) ^ (1 - γ)
        ≤ ((δ : ENNReal) ^ (-θ)) ^ (1 - γ) := ENNReal.rpow_le_rpow h1 (by linarith)
      _ = (δ : ENNReal) ^ (-θ * (1 - γ)) := by rw [← ENNReal.rpow_mul]
      _ ≤ (δ : ENNReal) ^ (-ε) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by nlinarith)
  calc ∑ i ∈ s, volume (V i).shade
      ≤ (s.card : ENNReal) * volume (⋃ i ∈ s, (V i).shade) :=
        sum_shade_le_card_mul_iUnion s V
    _ = ((s.card : ENNReal) ^ γ * (s.card : ENNReal) ^ (1 - γ)) *
          volume (⋃ i ∈ s, (V i).shade) := by
        rw [← ENNReal.rpow_add _ _ hN0 hNtop]
        norm_num
    _ ≤ ((s.card : ENNReal) ^ γ * (δ : ENNReal) ^ (-ε)) *
          volume (⋃ i ∈ s, (V i).shade) := by gcongr
    _ = (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ *
          volume (⋃ i ∈ s, (V i).shade) := by ring

/-- **Large-cardinality branch.** -/
theorem katzTaoGoal_of_absoluteLoss_of_card_ge {s : Finset ι} {V : ι → ShadedBody E} {δ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε ε₀ γ : ℝ} (hγ0 : 0 ≤ γ) (hloss : ε₀ ≤ ε + γ)
    (hcard : (δ : ℝ)⁻¹ ≤ (s.card : ℝ))
    (h : ∑ i ∈ s, volume (V i).shade
          ≤ (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ s, (V i).shade)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (V i).shade) := by
  have hd0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hdtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hd1 : (δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1
  have hkey : (δ : ENNReal) ^ (-ε₀) ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ := by
    calc (δ : ENNReal) ^ (-ε₀)
        ≤ (δ : ENNReal) ^ (-ε + -γ) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith)
      _ = (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-γ) := ENNReal.rpow_add _ _ hd0 hdtop
      _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ := by
          gcongr
          exact rpow_neg_le_rpow_of_inv_le hγ0 (coe_inv_le_natCast hδ hcard)
  exact h.trans (by gcongr)

end Branches


/-! ### The dichotomy -/

section Dichotomy

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **The parametrised cardinality dichotomy.** -/
theorem rpow_lt_card_or_katzTaoGoal {s : Finset ι} (V : ι → ShadedBody E) {δ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε γ θ : ℝ} (hγ1 : γ ≤ 1) (hcost : θ * (1 - γ) ≤ ε) :
    (δ : ℝ) ^ (-θ) < (s.card : ℝ) ∨
      ∑ i ∈ s, volume (V i).shade
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (V i).shade) := by
  rcases lt_or_ge ((δ : ℝ) ^ (-θ)) ((s.card : ℝ)) with h | h
  · exact Or.inl h
  · exact Or.inr (katzTaoGoal_of_card_le_rpow hδ hδ1 hγ1 hcost h)

/-- **The dichotomy in eliminator form.** -/
theorem katzTaoGoal_of_card_gt_branch {s : Finset ι} {V : ι → ShadedBody E} {δ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε γ θ : ℝ} (hγ1 : γ ≤ 1) (hcost : θ * (1 - γ) ≤ ε)
    (hbig : (δ : ℝ) ^ (-θ) < (s.card : ℝ) →
      ∑ i ∈ s, volume (V i).shade
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (V i).shade)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (V i).shade) :=
  (rpow_lt_card_or_katzTaoGoal V hδ hδ1 hγ1 hcost).elim hbig id

/-- **The dichotomy at the threshold `δ⁻¹` that Prof. Wang's remark names.** -/
theorem delta_inv_lt_card_or_katzTaoGoal {s : Finset ι} (V : ι → ShadedBody E) {δ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε γ : ℝ} (hγ1 : γ ≤ 1) (hcost : 1 - γ ≤ ε) :
    (δ : ℝ)⁻¹ < (s.card : ℝ) ∨
      ∑ i ∈ s, volume (V i).shade
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (V i).shade) := by
  have := rpow_lt_card_or_katzTaoGoal (s := s) V hδ hδ1 (θ := 1) hγ1 (by linarith)
  rwa [Real.rpow_neg_one] at this

end Dichotomy


/-! ### Discharging `δ⁻¹ ≤ |T|` from a coarse-scale count -/

section ScaleCount

/-- A count carried by the image of `s` is a count carried by `s`. -/
theorem le_card_of_le_card_image {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (f : ι → κ) {c : ℝ}
    (h : c ≤ ((s.image f).card : ℝ)) : c ≤ (s.card : ℝ) :=
  h.trans (by exact_mod_cast Finset.card_image_le)

/-- **The `ρ`-scale count at `ρ = δ ^ (1 - b)` forces `δ⁻¹ ≤ |T|`.** -/
theorem delta_inv_le_card_of_scaleCount {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (f : ι → κ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {b ζ : ℝ} (hb : b ≤ 1 / 2) (hζ : 0 ≤ ζ)
    (hcount : (δ ^ (1 - b)) ^ (-2 - ζ) ≤ ((s.image f).card : ℝ)) :
    δ⁻¹ ≤ (s.card : ℝ) := by
  refine le_card_of_le_card_image s f (le_trans ?_ hcount)
  rw [← Real.rpow_neg_one δ, ← Real.rpow_mul hδ.le]
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)

/-- The `NNReal` form of `Kakeya.MainLemma2.Reduction.delta_inv_le_card_of_scaleCount`. -/
theorem delta_inv_le_card_of_scaleCount_nnreal {ι κ : Type*} [DecidableEq κ] (s : Finset ι)
    (f : ι → κ) {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {b ζ : ℝ} (hb : b ≤ 1 / 2) (hζ : 0 ≤ ζ)
    (hcount : ((δ ^ (1 - b) : NNReal) : ℝ) ^ (-2 - ζ) ≤ ((s.image f).card : ℝ)) :
    (δ : ℝ)⁻¹ ≤ (s.card : ℝ) := by
  refine delta_inv_le_card_of_scaleCount s f (by exact_mod_cast hδ) (by exact_mod_cast hδ1) hb hζ ?_
  rwa [NNReal.coe_rpow] at hcount


/-- **A cover-indexed count transfers to the fine family.** -/
theorem le_card_of_cover_count {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (R : ι → κ → Prop)
    (hcov : ∀ i ∈ s, ∃ j ∈ t, R i j) {c : ℝ}
    (hcount : ∀ t' : Finset κ, t' ⊆ t → (∀ i ∈ s, ∃ j ∈ t', R i j) → c ≤ (t'.card : ℝ)) :
    c ≤ (s.card : ℝ) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simpa using hcount ∅ (Finset.empty_subset t) (by simp)
  obtain ⟨j₀, -, -⟩ := hcov i₀ hi₀
  set f : ι → κ := fun i ↦ if h : ∃ j ∈ t, R i j then h.choose else j₀ with hf
  have hfmem : ∀ i ∈ s, f i ∈ t ∧ R i (f i) := by
    intro i hi
    have h : ∃ j ∈ t, R i j := hcov i hi
    simp only [hf, dif_pos h]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  refine le_card_of_le_card_image s f (hcount (s.image f) ?_ ?_)
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (hfmem i hi).1
  · intro i hi
    exact ⟨f i, Finset.mem_image_of_mem f hi, (hfmem i hi).2⟩

/-- **The very-not-sticky third bullet supplies `δ⁻¹ ≤ |T|`.** -/
theorem delta_inv_le_card_of_cover_count {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (R : ι → κ → Prop)
    (hcov : ∀ i ∈ s, ∃ j ∈ t, R i j)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {b ζ : ℝ} (hb : b ≤ 1 / 2) (hζ : 0 ≤ ζ)
    (hcount : ∀ t' : Finset κ, t' ⊆ t → (∀ i ∈ s, ∃ j ∈ t', R i j) →
        ((δ ^ (1 - b) : NNReal) : ℝ) ^ (-2 - ζ) ≤ (t'.card : ℝ)) :
    (δ : ℝ)⁻¹ ≤ (s.card : ℝ) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1R : ((δ : ℝ)) ≤ 1 := by exact_mod_cast hδ1
  have key : ((δ : ℝ) ^ (1 - b)) ^ (-2 - ζ) ≤ (s.card : ℝ) := by
    refine le_card_of_cover_count s t R hcov ?_
    intro t' hsub hcov'
    have := hcount t' hsub hcov'
    rwa [NNReal.coe_rpow] at this
  refine le_trans ?_ key
  rw [← Real.rpow_neg_one (δ : ℝ), ← Real.rpow_mul hδR.le]
  exact Real.rpow_le_rpow_of_exponent_ge hδR hδ1R (by nlinarith)


/-- **The bullet-shaped form.** -/
theorem delta_inv_le_card_of_scaleCount_bullet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {ι κ : Type*} [DecidableEq κ] {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {exscal ζ : ℝ} (hex : exscal ≤ 1 / 2) (hζ : 0 ≤ ζ)
    (s : Finset ι) (T : ι → ShadedTube δ E)
    (tρ : Finset κ) (Tρ : κ → Tube (δ ^ (1 - exscal)) E)
    (hcov : ∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody)
    (hpair : (tρ : Set κ).Pairwise
      (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier))
    (hcount : ∀ (t' : Finset κ) (Tρ' : κ → Tube (δ ^ (1 - exscal)) E),
        (∀ i ∈ s, ∃ j ∈ t', (T i).toConvexSpaceBody ≤ (Tρ' j).toConvexSpaceBody) →
        (t' : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ' j).carrier (Tρ' k).carrier) →
        ((δ ^ (1 - exscal) : NNReal) : ℝ) ^ (-2 - ζ) ≤ (t'.card : ℝ)) :
    (δ : ℝ)⁻¹ ≤ (s.card : ℝ) :=
  delta_inv_le_card_of_cover_count s tρ
    (fun i j ↦ (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) hcov hδ hδ1 hex hζ
    (fun t' hsub hcov' ↦ hcount t' Tρ hcov' (hpair.mono (Finset.coe_subset.mpr hsub)))

end ScaleCount



/-! ### Sharpness of the trivial branch -/

section Sharpness

/-- **The cost of the trivial branch at threshold `δ⁻¹`.** -/
theorem trivialBranch_cost_sharp {δ ε γ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hcost : ε < 1 - γ) :
    δ ^ (-ε) < (δ⁻¹) ^ (1 - γ) := by
  rw [Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le]
  exact Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by linarith)

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **The trivial branch cannot be improved without extra hypotheses.** -/
theorem katzTaoGoal_fails_of_const (s : Finset ι) (hs : s.Nonempty) (V₀ : ShadedBody E)
    (hv : volume V₀.shade ≠ 0) {δ : NNReal} {ε γ : ℝ}
    (hbad : (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ < (s.card : ENNReal)) :
    ¬ (∑ i ∈ s, volume ((fun _ : ι ↦ V₀) i).shade
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ *
            volume (⋃ i ∈ s, ((fun _ : ι ↦ V₀) i).shade)) := by
  intro h
  have hmul := (ShadedBody.multiplicity_le_iff s (fun _ : ι ↦ V₀)).mpr h
  rw [multiplicity_const s hs V₀ hv] at hmul
  exact absurd hmul (not_le.mpr hbad)

end Sharpness

end Kakeya.MainLemma2.Reduction
