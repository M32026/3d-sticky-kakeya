/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHupProducer

/-!
# The step-8 canonical cover at ONE radius

The centring hand-back reads the canonical cover of the
rescaled bodies at a radius contracted by the absolute constant
`Kakeya.VeryNotSticky.centringCoverRadiusConstant`, so the *supplying* clause has to be available
slightly below Lemma 9.1's window.  Widening the `σ`-side statements in place would re-state
`Kakeya.ML2Reduction.canonicalCover_of_step8`, `Kakeya.ML2Reduction.hup_of_step8` and
`Kakeya.ML2Reduction.canonicalCover_of_upstairs_essDistinct`, each of which has consumers outside
the moving set — source stop rule.  So nothing is re-stated: the chain is re-expressed
**pointwise**, at a single `ρ`, and the interval statements keep their texts.

Every body in that chain was already window-agnostic — it used the window only for `0 < ρ` and
`ρ ≤ 1/4` before handing off to the pointwise
`Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs_edMult`.  These lemmas make that explicit.

## Main declarations

* `Kakeya.ML2Reduction.hupAt_of_step8At` — `hup_of_step8` at one radius.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs_essDistinct` —
  `canonicalCover_of_upstairs_essDistinct` at one radius.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_step8` — `canonicalCover_of_step8` at one radius.

Each is followed by a **tie**: a theorem re-deriving the interval sibling's conclusion from the
pointwise one, and an `example` inhabiting the *same stated type* with the existing interval
theorem.  If either spelling drifts, this file stops compiling.
-/

@[expose] public section

open MeasureTheory Metric Set ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {θ τ σ : NNReal}

/-! ## `hup`, at one radius -/

open Classical in
/-- **`Kakeya.ML2Reduction.hup_of_step8` at a single radius.**  No window: the interval was used
only to produce `0 < ρ` and to pass the budget through. -/
theorem hupAt_of_step8At {ζ ζ' m Lam : ℝ} (hθ0 : 0 < θ)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ)
    {κ₀ : Type u} (t₈ : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) {M : ℕ}
    (hsubW : ∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    (hM : ∀ i ∈ t₈, (t₈.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M)
    (hMρ : (M : ℝ) ≤ (ρ : ℝ) ^ (-m))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbud : Lam ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ∃ (κ : Type u) (t : Finset κ) (W' : κ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))),
      (∀ k ∈ t, (W' k).carrier ⊆ T₀.carrier) ∧
      (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W' k).carrier) ∧
      ((t : Set κ).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W' j).carrier (W' k).carrier) ∧
      Lam ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ)) ∧
      (ρ : ℝ) ^ (-2 - (ζ' - m)) ≤ (t.card : ℝ) := by
  obtain ⟨t, hts, hED, hcnt⟩ := exists_edCover_of_count hρ0 hθ0 W hM hMρ hcard
  exact ⟨κ₀, t, W, fun k hk ↦ hsubW k (hts hk), fun k hk ↦ hused k (hts hk), hED, hbud, hcnt⟩

open Classical in
/-- **Tie: the interval spelling of `hup` is the pointwise one, quantified.**  This re-derives
`Kakeya.ML2Reduction.hup_of_step8`'s conclusion from `hupAt_of_step8At`; the `example` below
inhabits the *same stated type* with the existing interval theorem, so neither spelling can drift
without breaking this file. -/
theorem hup_of_step8_of_At {ϖ ζ ζ' m Lam : ℝ} (hθ0 : 0 < θ) (hσ0 : 0 < σ)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hstep8 : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-m) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      Lam ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))),
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        Lam ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ)) ∧
        (ρ : ℝ) ^ (-2 - (ζ' - m)) ≤ (t.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ₀, t₈, W, M, hsubW, hused, hM, hMρ, hcard⟩ := hstep8 ρ hρ
  exact hupAt_of_step8At hθ0 T₀ 𝕋 (lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1) t₈ W
    hsubW hused hM hMρ hcard (hbudget ρ hρ)

open Classical in
/-- **Drift check for `hup`.**  Both sides must elaborate at the *same* type; if either the
pointwise route or `Kakeya.ML2Reduction.hup_of_step8` changes shape, this stops compiling. -/
example {ϖ ζ ζ' m Lam : ℝ} (hθ0 : 0 < θ) (hσ0 : 0 < σ)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hstep8 : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-m) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      Lam ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    hup_of_step8_of_At hθ0 hσ0 T₀ 𝕋 hstep8 hbudget
      = hup_of_step8 hθ0 hσ0 T₀ 𝕋 hstep8 hbudget := rfl

/-! ## The upstairs-to-canonical step, at one radius -/

open Classical in
/-- **`Kakeya.ML2Reduction.canonicalCover_of_upstairs_essDistinct` at a single radius.** -/
theorem canonicalCoverAt_of_upstairs_essDistinct {R ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    (hED : (t : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hslack : (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
        * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hM : ∀ i ∈ t, (t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card
      ≤ ⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ :=
    fun i hi ↦ edMultNat_le_of_upstairs_essDistinct hsit hR hfr T₀ hρ0 hρ4 W hsubW hED hi
  have hne : t.Nonempty := by
    rw [← Finset.card_pos]
    have hpos : (0 : ℝ) < (ρ : ℝ) ^ (-2 - ζ') := Real.rpow_pos_of_pos hρR _
    have : (0 : ℝ) < (t.card : ℝ) := lt_of_lt_of_le hpos hcard
    exact_mod_cast this
  have hM0 : 0 < ⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ :=
    lt_of_lt_of_le zero_lt_one
      (one_le_edMult hρ0 (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hne hM)
  exact canonicalCoverAt_of_upstairs_edMult hsit hR T₀ 𝕋 hρ0 hρ4 t W hsubW hused hM0 hM
    hslack hcard

/-! ## The step-8 canonical cover, at one radius -/

open Classical in
/-- **`Kakeya.ML2Reduction.canonicalCover_of_step8` at a single radius.**  The composition of the
two pointwise steps above, with the reading exponent reduced from `ζ'` to `ζ' - m` by the
extraction, exactly as the interval version does. -/
theorem canonicalCoverAt_of_step8 {R ζ ζ' m : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t₈ : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) {M : ℕ}
    (hsubW : ∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    (hM : ∀ i ∈ t₈, (t₈.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M)
    (hMρ : (M : ℝ) ≤ (ρ : ℝ) ^ (-m))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbud : (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
        * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  obtain ⟨κ, t, W', hsubW', hused', hED', hbud', hcnt'⟩ :=
    hupAt_of_step8At hsit.pos_ambient T₀ 𝕋 hρ0 t₈ W hsubW hused hM hMρ hcard hbud
  exact canonicalCoverAt_of_upstairs_essDistinct (ζ' := ζ' - m) hsit hR T₀ 𝕋 hρ0 hρ4 t W'
    hsubW' hused' hED' hbud' hcnt'

open Classical in
/-- **Tie: `canonicalCover_of_step8` is `canonicalCoverAt_of_step8`, quantified.** -/
theorem canonicalCover_of_step8_of_At {ϖ R ζ ζ' m : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hσ0 : 0 < σ) (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hstep8 : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-m) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((u : Set κ₁).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
        (∀ j ∈ u, ∃ i ∈ s,
          (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (V j).toConvexSpaceBody) ∧
        (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ₀, t₈, W, M, hsubW, hused, hM, hMρ, hcard⟩ := hstep8 ρ hρ
  exact canonicalCoverAt_of_step8 hsit hR T₀ 𝕋
    (lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1)
    (le_trans (by exact_mod_cast hρ.2) hwin4) t₈ W hsubW hused hM hMρ hcard (hbudget ρ hρ)

open Classical in
/-- **Drift check for the step-8 cover.** -/
example {ϖ R ζ ζ' m : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hσ0 : 0 < σ) (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hstep8 : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-m) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    canonicalCover_of_step8_of_At hsit hR T₀ 𝕋 hσ0 hwin4 hstep8 hbudget
      = canonicalCover_of_step8 hsit hR T₀ 𝕋 hσ0 hwin4 hstep8 hbudget := rfl

/-! ## The budget at a contracted radius -/

/-- **The budget descends to a smaller radius.**  At a non-positive exponent a smaller base gives
a larger value, so a budget clause proved at `ρ` holds at every `ρ' ≤ ρ`.  This is what lets the
`hbudget` binders stay on Lemma 9.1's window while the cover is read at `ρ/C`
The non-positivity of the exponent is **not** derivable from the budget itself: the left factor
`⌈Tube.essDistinctTubesInSelfDilate.C 3 _⌉₊` has no positivity lemma in the tree
(`Kakeya/Tube/CoverCountComparable.lean:172` records this), so `1 ≤ K` is unavailable and the
caller must supply the reading gap. -/
theorem budget_descends {lo ρ' K e : ℝ} (hρ'0 : 0 < ρ') (hle : ρ' ≤ lo) (he : e ≤ 0)
    (h : K ≤ lo ^ e) : K ≤ ρ' ^ e :=
  h.trans (Real.rpow_le_rpow_of_nonpos hρ'0 hle he)

/-! ## The same, at a named count constant

The centring transport's antecedent reads the count at the
**packing** constant `Kakeya.VeryNotSticky.centringCountLossConstant R`, not at
`Kakeya.ML2Reduction.spineOuterCountLoss`.  Nothing about the extraction changes: the count is a
free parameter of `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_edMult` (`{c : ℝ}`,
`hlow : M · c ≤ t.card` gives `c ≤ u.card`), and the `σ`-side wrappers merely instantiate it at
`Λ · ρ^{-2-ζ}`.  These instantiate it at `Kc · ρ^{-2-ζ}` instead — **one inequality, one payment,
one threshold**, exactly as states.  No `σ`-side statement is re-stated. -/

open Classical in
/-- **`canonicalCoverAt_of_upstairs_essDistinct` at a named count constant.** -/
theorem canonicalCoverAt_of_upstairs_essDistinct_const {R ζ ζ' Kc : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    (hED : (t : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hslack : (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
        * Kc ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      Kc * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hM : ∀ i ∈ t, (t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card
      ≤ ⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ :=
    fun i hi ↦ edMultNat_le_of_upstairs_essDistinct hsit hR hfr T₀ hρ0 hρ4 W hsubW hED hi
  have hne : t.Nonempty := by
    rw [← Finset.card_pos]
    have hpos : (0 : ℝ) < (ρ : ℝ) ^ (-2 - ζ') := Real.rpow_pos_of_pos hρR _
    have : (0 : ℝ) < (t.card : ℝ) := lt_of_lt_of_le hpos hcard
    exact_mod_cast this
  have hM0 : 0 < ⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ :=
    lt_of_lt_of_le zero_lt_one
      (one_le_edMult hρ0 (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hne hM)
  have hsit2 := isRescalingSituation_scaledUp hsit hρ0 hρ4
  have hused' := outerTube_used_of_used hfr hsit2 hR (ratio_scaledUp hsit.pos_ambient ρ)
    T₀ 𝕋 W hsubW hused
  exact canonicalCoverAt_of_used_of_edMult hsit.pos_ambient T₀ (hR := hR) 𝕋 hρ0 t
    (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hM0 hM hused'
    (edCount_budget_of_slack hρ0 hslack hcard)

open Classical in
/-- **`canonicalCoverAt_of_step8` at a named count constant.** -/
theorem canonicalCoverAt_of_step8_const {R ζ ζ' m Kc : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t₈ : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) {M : ℕ}
    (hsubW : ∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    (hM : ∀ i ∈ t₈, (t₈.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M)
    (hMρ : (M : ℝ) ≤ (ρ : ℝ) ^ (-m))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbud : (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
        * Kc ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      Kc * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  obtain ⟨κ, t, W', hsubW', hused', hED', hbud', hcnt'⟩ :=
    hupAt_of_step8At hsit.pos_ambient T₀ 𝕋 hρ0 t₈ W hsubW hused hM hMρ hcard hbud
  exact canonicalCoverAt_of_upstairs_essDistinct_const (ζ' := ζ' - m) hsit hR T₀ 𝕋 hρ0 hρ4 t W'
    hsubW' hused' hED' hbud' hcnt'

/-- **Dropping the rescaling loss from the strengthened budget.**  `hcntbudget` is each site's own
`hbudget` with `centringCountLossConstant R ·` inserted at the head of the left-hand side, so it
implies `hbudget` (that is "one inequality, one payment") and it also implies the same
bound with the trailing `spineOuterCountLoss R` dropped, since that factor is `≥ 1`. -/
theorem le_of_mul_spineOuterCountLoss {R x y : ℝ} (hx : 0 ≤ x)
    (h : x * (spineOuterCountLoss R : ℝ) ≤ y) : x ≤ y :=
  le_trans (le_mul_of_one_le_right hx (one_le_spineOuterCountLoss R)) h

/-- **`hcntbudget` gives the `Kc`-form budget**.  The strengthened clause is the site's own
`hbudget` with `Kc ·` at the head; dropping the trailing `spineOuterCountLoss R` (which is `≥ 1`)
and commuting leaves exactly the budget the `Kc`-form cover step asks for.  One inequality, one
payment. -/
theorem hbud_of_hcntbudget {R e ρ Kc : ℝ} (hKc0 : 0 ≤ Kc)
    (h : Kc * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
        * (spineOuterCountLoss R : ℝ) ≤ ρ ^ e) :
    (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ) * Kc ≤ ρ ^ e := by
  refine le_trans ?_ h
  have hc0 : (0 : ℝ) ≤ Kc * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ) := by positivity
  calc (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ) * Kc = Kc * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ) := mul_comm _ _
    _ ≤ Kc * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ) * (spineOuterCountLoss R : ℝ) :=
        le_mul_of_one_le_right hc0 (one_le_spineOuterCountLoss R)

/-! ## the `Kc`-forms are the `Λ`-forms, as equations at the same stated type -/

open Classical in
/-- **the `Kc`-form IS the `Λ`-form** (upstairs, essentially distinct).  An equation at
the same stated type; an implication would not rule out the two spellings drifting. -/
theorem canonicalCoverAt_of_upstairs_essDistinct_of_const {R ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    (hED : (t : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hslack : (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
        * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    canonicalCoverAt_of_upstairs_essDistinct_const (Kc := (spineOuterCountLoss R : ℝ))
        hsit hR T₀ 𝕋 hρ0 hρ4 t W hsubW hused hED hslack hcard
      = canonicalCoverAt_of_upstairs_essDistinct hsit hR T₀ 𝕋 hρ0 hρ4 t W hsubW hused hED
          hslack hcard := rfl

open Classical in
/-- **the `Kc`-form IS the `Λ`-form** (step 8). -/
theorem canonicalCoverAt_of_step8_of_const {R ζ ζ' m : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t₈ : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) {M : ℕ}
    (hsubW : ∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    (hM : ∀ i ∈ t₈, (t₈.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M)
    (hMρ : (M : ℝ) ≤ (ρ : ℝ) ^ (-m))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbud : (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
        * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    canonicalCoverAt_of_step8_const (Kc := (spineOuterCountLoss R : ℝ))
        hsit hR T₀ 𝕋 hρ0 hρ4 t₈ W hsubW hused hM hMρ hcard hbud
      = canonicalCoverAt_of_step8 hsit hR T₀ 𝕋 hρ0 hρ4 t₈ W hsubW hused hM hMρ hcard hbud := rfl

end Kakeya.ML2Reduction

end
