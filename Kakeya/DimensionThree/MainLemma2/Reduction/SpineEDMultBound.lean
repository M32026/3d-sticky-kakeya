/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDExtraction

/-!
# The ED-multiplicity of the pushed-down family is a constant

Blueprint: `blueprint/src/GWZAdapted/section9.tex`, the non-eccentric case.

 refutes the route that buys essential distinctness of the pushed-down `ρ`-cover with
a maximal-density bound.   replaces that price by the family's **ED-multiplicity**
`M` and leaves one obligation: bound `M`.  **This file discharges it, with existing tools only, and
the answer is that `M` is a constant** depending on the dimension and on the rescaling radius `R`:

```
M ≤ ⌈Tube.essDistinctTubesInSelfDilate.C 3 (16 R C_n)⌉₊,   C_n = Tube.tubeOverlapCoreClose.C 3
```

**provided the parents are pairwise essentially distinct upstairs.**  Essential distinctness moves
to where GWZ has it by construction — `𝕋_ρ` is an essentially distinct cover by definition — and
off the pushed-down family, where it cannot be bought.

## The chain, all existing

1. `¬ IsEssentiallyDistinct (V j) (V i)` unfolds to the heavy overlap
   `½ |V i| < |V i ∩ V j|`, and `Kakeya.Tube.tubeOverlapCoreClose` turns that into
   `V j ⊆ C_n · V i` downstairs.
2. `Kakeya.ML2Reduction.outerTube_spec` puts `Ψ(W j)` inside `V j`, hence inside `C_n · V i`.
3. `Tube.preimage_rescale_dilate_subset_dilate` — whose own docstring names exactly this use:
   *"a failure of essential distinctness upstairs is turned by `Tube.tubeOverlapCoreClose` into a
   containment in `C_n · V`, and this lemma turns that into a containment in a bounded dilate of
   the original `τ`-tube, where `Tube.essDistinctTubesInSelfDilate` counts"* — pulls `C_n · V i`
   back to `16 R C_n · W i`.  Its tilt hypothesis is `κ = 2`, discharged from `W i ⊆ T₀` by
   `Tube.perp_norm_core_sub_le_of_subset` (`perp_le_of_subset`).
4. `Tube.essDistinctTubesInSelfDilate` counts the parents inside that dilate — this is the step
   that consumes pairwise essential distinctness upstairs — and returns the constant.

**No bounded-overlap datum is used.**  See  for why the
`Tube.UniformTubeSet.boundedOverlap` route was abandoned: its container must be a tube of the
*exact* grid radius, while step 3 produces a `16 R C_n`-dilate; the dilate form exists only in the
loose model (`Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil`), which the spine does not
use; and it bounds *members*, whose conversion to nodes costs the branching number, not a constant.

## The budget is now a threshold

With `M` an explicit constant the count budget `M · Λ ≤ ρ^{-(ζ'-ζ)}` stops being a competition
between two `ρ`-powers and becomes a threshold on `ρ`: `exists_threshold_const_le_rpow`.

## Main declarations

* `Kakeya.ML2Reduction.perp_le_of_subset`, `Kakeya.ML2Reduction.one_le_radius` — the two side
  conditions of the pull-back.
* `Kakeya.ML2Reduction.subset_dilate_of_not_essDistinct_outerTube` — steps 1–3: a failure of
  essential distinctness downstairs puts the parents in a bounded dilate of one another.
* `Kakeya.ML2Reduction.edMult_le_of_upstairs_essDistinct`,
  `Kakeya.ML2Reduction.edMultNat_le_of_upstairs_essDistinct` — **the bound on `M`**.
* `Kakeya.ML2Reduction.exists_threshold_const_le_rpow` — the budget clause is a threshold.
* `Kakeya.ML2Reduction.canonicalCover_of_upstairs_essDistinct` — the canonical-cover datum, over
  an interface whose only geometric input is upstairs essential distinctness.
* `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_upstairs_essDistinct` — step 10.
-/

@[expose] public section

open MeasureTheory Metric Set ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {θ τ σ : NNReal}

/-- The tilt hypothesis of `Tube.preimage_rescale_dilate_subset_dilate` at `κ = 2`, from
`T ⊆ T₀`. -/
theorem perp_le_of_subset (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖ ≤ 2 * (θ : ℝ) := by
  have h := (_root_.Tube.perp_norm_core_sub_le_of_subset T₀ T hT).2.2
  have heq : T.x - T.y - (inner ℝ T₀.direction (T.x - T.y) : ℝ) • T₀.direction
      = -(T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction) := by
    have hd : T.direction = T.y - T.x := rfl
    have hxy' : T.x - T.y = -(T.y - T.x) := by abel
    rw [hd, hxy', inner_neg_right]
    module
  rw [heq, norm_neg] at h
  exact h

/-- `1 ≤ R` in a rescaling situation. -/
theorem one_le_radius {R : ℝ} {n : ℕ} (hsit : Tube.IsRescalingSituation θ τ σ R n) : 1 ≤ R :=
  le_trans (by exact_mod_cast _root_.Tube.normalization.one_le_C n)
    hsit.normalizationConst_le_radius

/-! ### From a failure of essential distinctness downstairs to a dilate upstairs -/

/-- **The pull-back step.**  If the pushed-down `ρ`-tubes of two parents fail to be essentially
distinct, then the parents themselves lie in a bounded dilate of one another — with the ratio
`16 R C_n` depending only on the dimension and on the rescaling radius `R`.

The chain is entirely existing: `Kakeya.Tube.tubeOverlapCoreClose` turns the heavy overlap into a
containment in the `C_n`-dilate downstairs, `Kakeya.ML2Reduction.outerTube_spec` puts the image of
the parent inside its own outer tube, and `Tube.preimage_rescale_dilate_subset_dilate` — whose own
docstring names exactly this use — pulls the dilate back. -/
theorem subset_dilate_of_not_essDistinct_outerTube [Nontrivial E] {R : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hn : Module.finrank ℝ E = 3)
    (T₀ : Tube θ E) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    (Wj Wi : Tube (ρ * θ) E)
    (hWj : Wj.carrier ⊆ T₀.carrier) (hWi : Wi.carrier ⊆ T₀.carrier)
    (hne : ¬ _root_.IsEssentiallyDistinct
      (outerTube hsit.pos_ambient T₀ hR ρ Wj).carrier
      (outerTube hsit.pos_ambient T₀ hR ρ Wi).carrier) :
    Wj.carrier ⊆ (Kakeya.Tube.dilate Wi
      (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := by
  classical
  have hsit2 := isRescalingSituation_scaledUp hsit hρ0 hρ4
  have hρ1 : ρ ≤ 1 := by
    have : (ρ : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  set Vj := outerTube hsit.pos_ambient T₀ hR ρ Wj with hVj
  set Vi := outerTube hsit.pos_ambient T₀ hR ρ Wi with hVi
  -- (1) heavy overlap
  have hheavy : (1 / 2 : ENNReal) * volume Vi.carrier < volume (Vi.carrier ∩ Vj.carrier) := by
    rw [_root_.IsEssentiallyDistinct, not_le] at hne
    calc (1 / 2 : ENNReal) * volume Vi.carrier
        ≤ (1 / 2 : ENNReal) * max (volume Vj.carrier) (volume Vi.carrier) := by
          gcongr; exact le_max_right _ _
      _ < volume (Vj.carrier ∩ Vi.carrier) := hne
      _ = volume (Vi.carrier ∩ Vj.carrier) := by rw [Set.inter_comm]
  -- (2) containment in the dilate downstairs
  have hdown : Vj.carrier
      ⊆ (Kakeya.Tube.dilate Vi
          (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier :=
    Tube.tubeOverlapCoreClose hρ0 hρ1 Vi Vj hheavy
  -- (3) the image of the parent sits inside its own outer tube
  have himg : spineRescaleUnit hsit.pos_ambient T₀ hR '' Wj.carrier ⊆ Vj.carrier :=
    (outerTube_spec hn hsit2 hR (ratio_scaledUp hsit.pos_ambient ρ) T₀ Wj hWj).1
  -- (4) the pull-back
  have hperp := perp_le_of_subset T₀ Wi hWi
  have hxy : T₀.rescaleMap R Wi.x ≠ T₀.rescaleMap R Wi.y :=
    rescaleMap_x_ne_rescaleMap_y hsit.pos_ambient T₀ hR Wi
  have hpre := _root_.Tube.preimage_rescale_dilate_subset_dilate hsit2
    (by norm_num : (0 : ℝ) ≤ 2)
    (le_of_lt (Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)))
    T₀ Wi hperp hxy
  intro z hz
  have hz' : T₀.rescaleMap R z
      ∈ (Kakeya.Tube.dilate Vi
          (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := by
    refine hdown ?_
    refine himg ⟨z, hz, ?_⟩
    rw [spineRescaleUnit_coe hsit.pos_ambient T₀ hR]
  exact hpre hz'

/-! ### The ED-multiplicity of the pushed-down family is a constant -/

/-- **The bound on `M`.**  If the *upstairs* parent family is pairwise essentially distinct, then
the ED-multiplicity of the pushed-down `ρ`-tube family is at most
`Tube.essDistinctTubesInSelfDilate.C 3 (16 R C_n)` — a constant depending only on the dimension
and on the rescaling radius `R`.

This is the obligation that  left open, discharged.  Essential distinctness has
moved *upstairs*, where GWZ has it by construction (`𝕋_ρ` is an essentially distinct cover by
definition), and off the pushed-down family, where  shows it cannot be bought. -/
theorem edMult_le_of_upstairs_essDistinct [Nontrivial E] {R : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R) (hn : Module.finrank ℝ E = 3)
    (T₀ : Tube θ E) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type*} {t : Finset κ₀} (W : κ₀ → Tube (ρ * θ) E)
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hED : (t : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    {i : κ₀} (hi : i ∈ t) :
    (((open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card : ℕ) : ENNReal)
      ≤ ((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ENNReal) := by
  classical
  have hR1 : (1 : ℝ) ≤ R := one_le_radius hsit
  have hCn : (1 : ℝ) < Tube.tubeOverlapCoreClose.C 3 := by
    exact Tube.tubeOverlapCoreClose.one_lt_C 3
  have hc : (1 : ℝ) ≤ 4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3 := by nlinarith
  have hρ1 : ρ ≤ 1 := by
    have : (ρ : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hδ0 : 0 < ρ * θ := mul_pos hρ0 hsit.pos_ambient
  have hδ1 : ρ * θ ≤ 1 := by
    calc ρ * θ ≤ 1 * 1 := by gcongr; exact hsit.ambient_le_one
      _ = 1 := one_mul 1
  set a := (t.filter (fun j ↦
    ¬ _root_.IsEssentiallyDistinct
        (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
        (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)) with ha
  have hasub : a ⊆ t := Finset.filter_subset _ _
  have hUED : (↑a : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier :=
    hED.mono (by exact_mod_cast hasub)
  have hUT : ∀ j ∈ a, (W j).carrier
      ⊆ (Kakeya.Tube.dilate (W i)
          (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3)).carrier := by
    intro j hj
    have hjt : j ∈ t := hasub hj
    have hne : ¬ _root_.IsEssentiallyDistinct
        (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
        (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier := by
      have := Finset.mem_filter.mp hj
      exact this.2
    have h := subset_dilate_of_not_essDistinct_outerTube hsit hR hn T₀ hρ0 hρ4 (W j) (W i)
      (hsubW j hjt) (hsubW i hi) hne
    rwa [hn] at h
  have h := _root_.Tube.essDistinctTubesInSelfDilate (E := E) (ι := κ₀) (δ := ρ * θ)
    (c := 4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) hc hδ0 hδ1 (W i) a W hUED hUT
  rwa [hn] at h

/-- The `ℕ`-valued reading of `edMult_le_of_upstairs_essDistinct`, in the shape the
ED-multiplicity clause of 's interface asks for. -/
theorem edMultNat_le_of_upstairs_essDistinct [Nontrivial E] {R : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R) (hn : Module.finrank ℝ E = 3)
    (T₀ : Tube θ E) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type*} {t : Finset κ₀} (W : κ₀ → Tube (ρ * θ) E)
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hED : (t : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    {i : κ₀} (hi : i ∈ t) :
    (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card
      ≤ ⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ := by
  classical
  have h := edMult_le_of_upstairs_essDistinct hsit hR hn T₀ hρ0 hρ4 W hsubW hED hi
  have h' := ENNReal.coe_le_coe.mp (by exact_mod_cast h)
  have h'' : (((t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card : ℕ) : ℝ)
      ≤ ((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ) := by
    exact_mod_cast h'
  have hfin := h''.trans (Nat.le_ceil ((_root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ))
  exact_mod_cast hfin

/-! ### The budget clause is a threshold on `ρ` only -/

/-- **A constant is below `ρ^{-g}` for all small `ρ`.**  With `M` now an explicit constant, the
count budget `M · Λ ≤ ρ^{-(ζ'-ζ)}` is no longer a competition between two `ρ`-powers: it is a
threshold, met at every scale below an explicit `ρ₀`. -/
theorem exists_threshold_const_le_rpow {A g : ℝ} (hg : 0 < g) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → A ≤ ρ ^ (-g) := by
  have hA1 : (1 : ℝ) ≤ max A 1 := le_max_right _ _
  have hA0 : (0 : ℝ) < max A 1 := lt_of_lt_of_le zero_lt_one hA1
  have hg1 : (0 : ℝ) < 1 / g := by positivity
  refine ⟨(max A 1) ^ (-(1 / g)), Real.rpow_pos_of_pos hA0 _,
    Real.rpow_le_one_of_one_le_of_nonpos hA1 (by linarith), ?_⟩
  intro ρ hρ0 hρ
  have hkey : ((max A 1) ^ (-(1 / g))) ^ (-g) = max A 1 := by
    rw [← Real.rpow_mul hA0.le, show (-(1 / g)) * (-g) = 1 by field_simp, Real.rpow_one]
  have hmono : ((max A 1) ^ (-(1 / g))) ^ (-g) ≤ ρ ^ (-g) := by
    rw [Real.rpow_neg (Real.rpow_pos_of_pos hA0 _).le, Real.rpow_neg hρ0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hρ0 _)
      (Real.rpow_le_rpow hρ0.le hρ hg.le)
  calc A ≤ max A 1 := le_max_left _ _
    _ = ((max A 1) ^ (-(1 / g))) ^ (-g) := hkey.symm
    _ ≤ ρ ^ (-g) := hmono

/-! ### The final interface: essential distinctness upstairs, and nothing else -/

/-- **The canonical-cover datum from an essentially distinct *upstairs* family.**

The ED-multiplicity clause of 's interface is gone: it is discharged by
`edMultNat_le_of_upstairs_essDistinct` from pairwise essential distinctness of the parents, and
`M` has become the explicit constant
`⌈Tube.essDistinctTubesInSelfDilate.C 3 (16 R C_n)⌉₊`.  The conclusion is the `hcanon` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` character for
character. -/
theorem canonicalCover_of_upstairs_essDistinct {R ϖ ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hσ0 : 0 < σ) (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))),
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
            * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((u : Set κ₁).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
        (∀ j ∈ u, ∃ i ∈ s,
          (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (V j).toConvexSpaceBody) ∧
        (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  classical
  intro ρ hρ
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨κ₀, t, W, hsubW, hused, hED, hslack, hcard⟩ := hup ρ hρ
  have hρ4 : (ρ : ℝ) ≤ 1 / 4 := le_trans (by exact_mod_cast hρ.2) hwin4
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1
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

/-- **Step 10, over the final interface.**  The existing consumer
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`, with `hcanon`
discharged by `canonicalCover_of_upstairs_essDistinct`. -/
theorem multiplicity_le_of_lemma91At_outer_of_upstairs_essDistinct
    {β ϖ ζ ζ' ν ηd cst : ℝ} {R : ℝ}
    (hL : Lemma91At.{u} β ϖ ζ ν ηd σ)
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).  Symbol-indexed
    --: the same text in this statement's own `ζ`, `ϖ`, `ηd`.
    -- The criterion's derivation needs the scale `< 1` (monotonicity of `s^{-x}` in `x`).
    -- MEASURED: available here, and strictly stronger — `hsit.out_le_quarter` gives
    -- `(σ : ℝ) ≤ 1/4` (`Kakeya/Tube/Rescale.lean:2627`), and this statement carries `hsit`.
    -- So `σ ≤ 1` is a citation, not an added binder.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (hσ0 : 0 < σ) (hϖ : 0 ≤ ϖ)
    (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {α : Type u} (s : Finset α)
    (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hloss : outerLoss R ≤ σ ^ (-cst))
    (hmax : Kakeya.maxDensity s (fun i ↦ (𝕋 i).toConvexSpaceBody)
      ≤ (σ : ENNReal) ^ (-(ηd - cst)))
    (hfull : σ ^ (ηd - cst) ≤ ShadedBody.fullness s (fun i ↦ (𝕋 i).toShadedBody))
    (hcen : ∀ i ∈ s, (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube.IsCentred)
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (σ : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s
        (outerFamily hsit.pos_ambient T₀ hR σ 𝕋) (Tube.ssfGridLen σ) C))
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))),
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
            * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ShadedBody.multiplicity s (fun i ↦ (𝕋 i).toShadedBody)
      ≤ (σ : ENNReal) ^ ν * (s.card : ENNReal) ^ β :=
  multiplicity_le_of_lemma91At_outer_of_canonicalCover hL hζ hsit hR hR1 hτσ hσ0 hϖ T₀ s 𝕋 hsub
    hloss hmax hfull hcen huni
    (canonicalCover_of_upstairs_essDistinct hsit hR T₀ 𝕋 hσ0 hwin4 hup)

end Kakeya.ML2Reduction

end
