/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.Factoring.RhoTubesUndilatedRich

/-!
# Product-only one-scale factoring

This file exposes exactly the multiplicity product, average-fullness, refinement, and nonemptiness
data supplied by the axiom-clean one-scale factoring theorem.  It deliberately omits the legacy
uniformity and density bundles used by the superseded Section 8 construction.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The product-only content of one-scale factoring, directly from the axiom-clean undilated GWZ
estimate.  No uniformity or density output is requested. -/
theorem exists_oneScaleProductOnly_rich_w49 (hdim : Module.finrank ℝ E = 3)
    {σ ρ : NNReal} (hσ0 : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type u} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily s (fun i => (V i).toTube) t Vρ p)
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade) :
    ∃ t' ⊆ t, ∃ u : Finset ι, u ⊆ s ∧
      ∃ (Zρ : κ → ShadedTube ρ E) (Z' : ι → ShadedTube σ E),
      t'.Nonempty ∧
      (∀ i ∈ u, p i ∈ t') ∧
      (∀ k ∈ t', (fibre u p k).Nonempty) ∧
      (∀ k ∈ t', ∀ k' ∈ t',
        ((fibre u p k).card : ENNReal) ≤ 2 * ((fibre u p k').card : ENNReal)) ∧
      0 < ∑ k ∈ t', volume (Zρ k).shade ∧
      0 < ∑ i ∈ u, volume (Z' i).shade ∧
      (∀ k, (Zρ k).toTube = Vρ k) ∧
      (∀ i, (Z' i).toTube = (V i).toTube) ∧
      (factorOneScale.C s.card σ)⁻¹ *
          ShadedBody.fullness s (fun i => (V i).toShadedBody)
        ≤ ShadedBody.fullness t' (fun k => (Zρ k).toShadedBody) ∧
      ShadedBody.IsCRefinement u
        (fun i => (Z' i).toShadedBody) s (fun i => (V i).toShadedBody)
        (factorOneScale.C s.card σ)⁻¹ ∧
      ∀ k ∈ t', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (factorOneScale.C s.card σ : ENNReal)
          * ShadedBody.multiplicity t' (fun k' => (Zρ k').toShadedBody)
          * ShadedBody.multiplicity (fibre u p k)
              (fun i => (Z' i).toShadedBody) := by
  classical
  have hcover : ∀ i ∈ s, (V i).toShadedBody.toConvexSpaceBody ≤
      (Vρ (p i)).toConvexSpaceBody := by
    intro i hi
    simpa using hparent.le_parent i hi
  let F : ShadedBody.FactorFamily E ι κ :=
    { innerSet := s
      innerBody := fun i => (V i).toShadedBody
      outerSet := t
      outerBody := fun k => (Vρ k).toConvexSpaceBody
      parent := p
      parent_mem := hparent.mapsTo
      inner_le_parent := hcover }
  obtain ⟨G, hGouter, hGinner, hGparent, hOuterBody, hInnerBody, _hGfiberNe, hne,
      _hfull, _href, hmult, _hcontain,
      ⟨u, huG, hrefActive, hufiberNe, hucard, hmulFiber⟩, _hvol⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilatedRich hσ0 ⟨hσρ, hρ1⟩
      F V Vρ (by intros; rfl) (by intros; rfl) (by
        intro i hi
        simpa [F] using hball i hi)
  let t' : Finset κ := G.outerSet
  let Sout : κ → ShadedBody E := G.outerBody
  let Sin : ι → ShadedBody E := G.innerBody
  have ht't : t' ⊆ t := by simpa [t'] using hGouter
  have hGinner' : G.innerSet = s.filter (fun i => p i ∈ t') := by
    simpa [F, t'] using hGinner
  have hOutCarrier : ∀ k ∈ t', (Sout k).carrier = (Vρ k).carrier := by
    intro k hk
    have h := hOuterBody k hk
    simpa [t', Sout, F] using congrArg (fun b : ConvexSpaceBody E => b.carrier) h
  let Zρ : κ → ShadedTube ρ E := fun k =>
    if hk : k ∈ t' then
      { toTube := Vρ k
        shade := (Sout k).shade
        measurableSet_shade := (Sout k).measurableSet_shade
        shade_subset := by rw [← hOutCarrier k hk]; exact (Sout k).shade_subset }
    else
      { toTube := Vρ k
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  let Z' : ι → ShadedTube σ E := fun i =>
    if hi : i ∈ s.filter (fun i => p i ∈ t') then
      { toTube := (V i).toTube
        shade := (Sin i).shade
        measurableSet_shade := (Sin i).measurableSet_shade
        shade_subset := by
          have hbody : (Sin i).toConvexSpaceBody = (V i).toConvexSpaceBody := by
            simpa [Sin, F] using hInnerBody i (Finset.mem_filter.mp hi).1
          change (Sin i).shade ⊆ (V i).toConvexSpaceBody.carrier
          rw [← hbody]
          exact (Sin i).shade_subset }
    else
      { toTube := (V i).toTube
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  have hsumInner : 0 < ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    have hcoef : 0 < (factorOneScale.C s.card σ : ENNReal)⁻¹ := by
      exact ENNReal.inv_pos.mpr ENNReal.coe_ne_top
    have hC0 : factorOneScale.C s.card σ ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1)
        (one_le_factorOneScale_C s.card σ))
    have hpos : 0 < (factorOneScale.C s.card σ : ENNReal)⁻¹ *
        ∑ i ∈ s, volume (V i).shade :=
      ENNReal.mul_pos hcoef.ne' hmass.ne'
    have hsumActive : 0 < ∑ i ∈ u, volume (G.innerBody i).shade := by
      apply hpos.trans_le
      have hmassActive := hrefActive.2
      rw [hdim] at hmassActive
      simp only [F] at hmassActive
      have hCeq : factorOneScale.C s.card σ =
          ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 s.card σ 1 := by rfl
      have hC0orig :
          ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 s.card σ 1 ≠ 0 := by
        simpa [hCeq] using hC0
      rw [ENNReal.coe_inv hC0orig] at hmassActive
      rw [← hCeq] at hmassActive
      simpa using hmassActive
    exact hsumActive.trans_le
      (Finset.sum_le_sum_of_subset_of_nonneg huG
        (fun i hi hnot => bot_le))
  have hsumOuter : 0 < ∑ k ∈ t', volume (Sout k).shade := by
    obtain ⟨i, hi, hvi⟩ := Finset.sum_pos_iff.mp hsumInner
    have hparent : G.parent i ∈ t' := G.parent_mem i hi
    have hmono : volume (G.innerBody i).shade ≤
        volume (G.outerBody (G.parent i)).shade := by
      exact measure_mono (G.shade_subset_parent i hi)
    have hvp : 0 < volume (G.outerBody (G.parent i)).shade := hvi.trans_le hmono
    have hvp' : 0 < volume (Sout (G.parent i)).shade := by simpa [Sout] using hvp
    have hle : volume (Sout (G.parent i)).shade ≤
        ∑ k ∈ t', volume (Sout k).shade := by
      exact Finset.single_le_sum (f := fun k => volume (Sout k).shade)
        (fun k hk => by positivity) hparent
    exact hvp'.trans_le hle
  have hZρshade : ∀ k ∈ t', (Zρ k).shade = (Sout k).shade := by
    intro k hk; simp [Zρ, hk]
  have hZρcarrier : ∀ k ∈ t', (Zρ k).carrier = (Sout k).carrier := by
    intro k hk
    have : (Zρ k).carrier = (Vρ k).carrier := by simp [Zρ, hk]
    rw [this, hOutCarrier k hk]
  have huFilter : u ⊆ s.filter (fun i => p i ∈ t') := by
    intro i hi
    have hiG := huG hi
    simpa [hGinner'] using hiG
  have huSub : u ⊆ s := fun i hi => (Finset.mem_filter.mp (huFilter hi)).1
  have huMaps : ∀ i ∈ u, p i ∈ t' :=
    fun i hi => (Finset.mem_filter.mp (huFilter hi)).2
  have hZ'shade : ∀ i ∈ u, (Z' i).shade = (Sin i).shade := by
    intro i hi
    have hi' := Finset.mem_filter.mp (huFilter hi)
    simp [Z', hi'.1, hi'.2]
  have hsumActive : 0 < ∑ i ∈ u, volume (Sin i).shade := by
    have hcoef : 0 < (factorOneScale.C s.card σ)⁻¹ :=
      inv_pos.mpr (zero_lt_one.trans_le (one_le_factorOneScale_C s.card σ))
    have hpos := ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hcoef.ne') hmass.ne'
    apply hpos.trans_le
    simpa [factorOneScale.C, hdim, F, Sin] using hrefActive.2
  have hsumZInner : 0 < ∑ i ∈ u, volume (Z' i).shade := by
    rw [Finset.sum_congr rfl (fun i hi => congrArg volume (hZ'shade i hi))]
    exact hsumActive
  have hfullOuter : (factorOneScale.C s.card σ)⁻¹ *
        ShadedBody.fullness s (fun i => (V i).toShadedBody)
      ≤ ShadedBody.fullness t' (fun k => (Zρ k).toShadedBody) := by
    have heq : ShadedBody.fullness t' (fun k => (Zρ k).toShadedBody) =
        ShadedBody.fullness t' Sout := by
      apply ENNReal.coe_injective
      rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
      dsimp only [ShadedBody.fullness']
      congr 1
      · exact Finset.sum_congr rfl fun k hk => congrArg volume (hZρshade k hk)
      · exact Finset.sum_congr rfl fun k hk => congrArg volume (hZρcarrier k hk)
    rw [heq]
    simpa [factorOneScale.C, hdim, F, t', Sout] using _hfull
  have hrefInner : ShadedBody.IsCRefinement u
      (fun i => (Z' i).toShadedBody) s (fun i => (V i).toShadedBody)
      (factorOneScale.C s.card σ)⁻¹ := by
    refine ⟨⟨huSub, ?_⟩, ?_⟩
    · intro i hi
      have hbody := hrefActive.1.2 i hi
      constructor
      · have hi' := Finset.mem_filter.mp (huFilter hi)
        simp [Z', hi'.1, hi'.2]
      · change (Z' i).shade ⊆ (V i).shade
        rw [hZ'shade i hi]
        exact hbody.2
    · rw [Finset.sum_congr rfl (fun i hi => congrArg volume (hZ'shade i hi))]
      simpa [factorOneScale.C, hdim, F, Sin] using hrefActive.2
  refine ⟨t', ht't, u, huSub, Zρ, Z', ?_, huMaps, ?_, ?_, ?_, hsumZInner,
    ?_, ?_, hfullOuter, hrefInner, ?_⟩
  · exact hne (by simpa [F] using hmass)
  · intro k hk
    have h := hufiberNe k hk
    simpa [fibre, F, hGparent] using h
  · intro k hk k' hk'
    simpa [fibre, F, hGparent] using hucard k hk k' hk'
  · calc
      0 < ∑ k ∈ t', volume (Sout k).shade := hsumOuter
      _ = ∑ k ∈ t', volume (Zρ k).shade := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hZρshade k hk).symm ▸ rfl
  · intro k
    by_cases hk : k ∈ t' <;> simp [Zρ, hk]
  · intro i
    by_cases hi : i ∈ s ∧ p i ∈ t' <;> simp [Z', hi]
  · intro k hk
    have hm := hmult k hk
    rw [hmulFiber k hk] at hm
    have hm' : ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
        (factorOneScale.C s.card σ : ENNReal) * ShadedBody.multiplicity t' Sout *
          ShadedBody.multiplicity (fibre u p k) Sin := by
      simpa [factorOneScale.C, hdim, F, t', Sout, Sin, fibre, hGparent] using hm
    have houtEq : ShadedBody.multiplicity t' (fun j => (Zρ j).toShadedBody) =
        ShadedBody.multiplicity t' Sout := by
      unfold ShadedBody.multiplicity
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        simp [hZρshade j hj]
      · apply congrArg volume
        apply Set.iUnion₂_congr
        intro j hj
        simp [hZρshade j hj]
    have hinEq : ShadedBody.multiplicity (fibre u p k)
          (fun i => (Z' i).toShadedBody) =
        ShadedBody.multiplicity (fibre u p k) Sin := by
      unfold ShadedBody.multiplicity
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ∈ u :=
          (Finset.mem_filter.mp hi).1
        simp [hZ'shade i hi']
      · apply congrArg volume
        apply Set.iUnion₂_congr
        intro i hi
        have hi' : i ∈ u :=
          (Finset.mem_filter.mp hi).1
        simp [hZ'shade i hi']
    simpa [houtEq, hinEq] using hm'

end Kakeya.ml1Boot

#print axioms Kakeya.ml1Boot.exists_oneScaleProductOnly_rich_w49
