/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

open scoped Classical in
/-- S:1220-1289 and the proved undilated theorem: the same named one-scale
outputs as exists_spineOneScale, retaining its discarded thickening clause.
This is an auxiliary wrapper obligation, pending exact formal review. -/
theorem source_exists_spineOneScale_thickening
    {sigma rho : NNReal} (hsigma : 0 < sigma) (hscale : sigma <= rho) (hrho : rho <= 1)
    {ifine icoarse : Type u} {s : Finset ifine} {t : Finset icoarse}
    (V : ifine -> ShadedTube sigma E) (W : icoarse -> Tube rho E)
    (parent : ifine -> icoarse)
    (hball : forall i, i ∈ s -> (V i).carrier <= Metric.closedBall (0 : E) 1)
    (hmaps : forall i, i ∈ s -> parent i ∈ t)
    (hcontain : forall i, i ∈ s ->
      (V i).toConvexSpaceBody <= (W (parent i)).toConvexSpaceBody) :
    exists t' : Finset icoarse, t' <= t /\
      exists (Zrho : icoarse -> ShadedTube rho E) (Z' : ifine -> ShadedTube sigma E),
      (forall k, (Zrho k).toTube = W k) /\
      (forall i, (Z' i).toTube = (V i).toTube) /\
      (forall i, (Z' i).shade <= (V i).shade) /\
      (0 < ∑ i ∈ s, volume (V i).shade -> t'.Nonempty) /\
      (0 < ∑ i ∈ s, volume (V i).shade -> 0 < ∑ k ∈ t', volume (Zrho k).shade) /\
      (forall i, i ∈ s -> parent i ∈ t' -> (Z' i).shade <= (Zrho (parent i)).shade) /\
      (spineScaleLoss (Module.finrank Real E) s.card sigma)⁻¹ *
          ShadedBody.fullness s (fun i => (V i).toShadedBody) <=
        ShadedBody.fullness t' (fun k => (Zrho k).toShadedBody) /\
      ShadedBody.IsCRefinement (s.filter (fun i => parent i ∈ t'))
        (fun i => (Z' i).toShadedBody) s (fun i => (V i).toShadedBody)
        (spineScaleLoss (Module.finrank Real E) s.card sigma)⁻¹ /\
      (forall k, k ∈ t' -> ShadedBody.multiplicity s (fun i => (V i).toShadedBody) <=
        (spineScaleLoss (Module.finrank Real E) s.card sigma : ENNReal) *
          ShadedBody.multiplicity t' (fun j => (Zrho j).toShadedBody) *
          ShadedBody.multiplicity (s.filter (fun i => parent i = k))
            (fun i => (Z' i).toShadedBody)) /\
      (forall j, j ∈ t' -> forall i, i ∈ s -> parent i = j ->
        (W j).carrier ∩ Metric.cthickening (2 * (rho : Real)) (Z' i).shade <=
          (Zrho j).shade) := by
  classical
  let F : ShadedBody.FactorFamily E ifine icoarse :=
    { innerSet := s
      innerBody := fun i => (V i).toShadedBody
      outerSet := t
      outerBody := fun k => (W k).toConvexSpaceBody
      parent := parent
      parent_mem := hmaps
      inner_le_parent := hcontain }
  obtain ⟨G, hGouter, hGinner, hGparent, hOuterBody, hInnerBody, hne, hfull,
      href, hmult, hsub, _hvol, hthick⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated hsigma
      ⟨hscale, hrho⟩ F V W (fun _ _ => rfl) (fun _ _ => rfl)
      (fun i hi => hball i hi)
  set t' : Finset icoarse := G.outerSet with ht'def
  set Sout : icoarse -> ShadedBody E := G.outerBody with hSoutdef
  set Sin : ifine -> ShadedBody E := G.innerBody with hSindef
  have hGinner' : G.innerSet = s.filter (fun i => parent i ∈ t') := hGinner
  have hOutCarrier : forall k, k ∈ t' -> (Sout k).carrier = (W k).carrier := by
    intro k hk
    exact congrArg (fun b : ConvexSpaceBody E => b.carrier) (hOuterBody k hk)
  have hInBody : forall i, i ∈ s ->
      (Sin i).toConvexSpaceBody = (V i).toConvexSpaceBody := fun i hi => hInnerBody i hi
  let Zrho : icoarse -> ShadedTube rho E := fun k =>
    if hk : k ∈ t' then
      { toTube := W k
        shade := (Sout k).shade
        measurableSet_shade := (Sout k).measurableSet_shade
        shade_subset := by rw [← hOutCarrier k hk]; exact (Sout k).shade_subset }
    else
      { toTube := W k
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  let Z' : ifine -> ShadedTube sigma E := fun i =>
    if hi : i ∈ G.innerSet then
      { toTube := (V i).toTube
        shade := (Sin i).shade
        measurableSet_shade := (Sin i).measurableSet_shade
        shade_subset := by
          have hbody : (Sin i).toConvexSpaceBody = (V i).toConvexSpaceBody :=
            hInBody i (by rw [hGinner'] at hi; exact (Finset.mem_filter.mp hi).1)
          change (Sin i).shade <= (V i).toConvexSpaceBody.carrier
          rw [← hbody]
          exact (Sin i).shade_subset }
    else
      { toTube := (V i).toTube
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  have hZrhoShade : forall k, k ∈ t' -> (Zrho k).shade = (Sout k).shade :=
    fun k hk => by simp [Zrho, hk]
  have hZrhoCarrier : forall k, k ∈ t' ->
      ((Zrho k).toShadedBody).carrier = (Sout k).carrier := by
    intro k hk
    have : ((Zrho k).toShadedBody).carrier = (W k).carrier := by simp [Zrho, hk]
    rw [this, hOutCarrier k hk]
  have hZ'Shade : forall i, i ∈ G.innerSet -> (Z' i).shade = (Sin i).shade :=
    fun i hi => by simp [Z', hi]
  have hZ'Body : forall i, i ∈ G.innerSet ->
      ((Z' i).toShadedBody).toConvexSpaceBody = (Sin i).toConvexSpaceBody := by
    intro i hi
    have h1 : ((Z' i).toShadedBody).toConvexSpaceBody = (V i).toConvexSpaceBody := by
      simp [Z', hi]
    rw [h1, hInBody i (by rw [hGinner'] at hi; exact (Finset.mem_filter.mp hi).1)]
  have houtFullEq : ShadedBody.fullness t' (fun k => (Zrho k).toShadedBody) =
      ShadedBody.fullness t' Sout := by
    unfold ShadedBody.fullness ShadedBody.fullness'
    congr 2
    · exact Finset.sum_congr rfl fun k hk => congrArg volume (hZrhoShade k hk)
    · exact Finset.sum_congr rfl fun k hk => congrArg volume (hZrhoCarrier k hk)
  have houtMultEq : ShadedBody.multiplicity t' (fun k => (Zrho k).toShadedBody) =
      ShadedBody.multiplicity t' Sout := by
    unfold ShadedBody.multiplicity
    congr 1
    · exact Finset.sum_congr rfl fun k hk => congrArg volume (hZrhoShade k hk)
    · exact congrArg volume (Set.iUnion₂_congr fun k hk => hZrhoShade k hk)
  refine ⟨t', hGouter, Zrho, Z',
    fun k => by by_cases hk : k ∈ t' <;> simp [Zrho, hk],
    fun i => by by_cases hi : i ∈ G.innerSet <;> simp [Z', hi],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ G.innerSet
    · rw [hZ'Shade i hi]
      have := (href.1.2 i hi).2
      simpa [hSindef] using this
    · simp [Z', hi]
  · exact hne
  · intro hmass
    have hCinv : (0 : ENNReal) <
        (((spineScaleLoss (Module.finrank Real E) s.card sigma)⁻¹ : NNReal) : ENNReal) := by
      refine ENNReal.coe_pos.mpr ?_
      exact pos_iff_ne_zero.mpr
        (inv_ne_zero (spineScaleLoss_ne_zero (Module.finrank Real E) s.card sigma))
    have hsumInner : 0 < ∑ i ∈ G.innerSet, volume (Sin i).shade := by
      refine lt_of_lt_of_le ?_ href.2
      exact ENNReal.mul_pos (ne_of_gt hCinv) (ne_of_gt hmass)
    obtain ⟨i, hi, hvi⟩ := Finset.sum_pos_iff.mp hsumInner
    have hpMem : G.parent i ∈ t' := G.parent_mem i hi
    have hmono : volume (Sin i).shade <= volume (Sout (G.parent i)).shade :=
      measure_mono (G.shade_subset_parent i hi)
    have hpPos : 0 < volume (Zrho (G.parent i)).shade := by
      rw [hZrhoShade (G.parent i) hpMem]
      exact hvi.trans_le hmono
    exact hpPos.trans_le
      (Finset.single_le_sum (f := fun k => volume (Zrho k).shade)
        (fun _ _ => by positivity) hpMem)
  · intro i hi hip
    have hiG : i ∈ G.innerSet := by
      rw [hGinner']; exact Finset.mem_filter.mpr ⟨hi, hip⟩
    have h := hsub i hiG
    rw [hZ'Shade i hiG, hZrhoShade (parent i) hip]
    have hpar : G.parent i = parent i := by rw [hGparent]
    simpa [hSindef, hSoutdef, hpar] using h
  · rw [houtFullEq]
    simpa [spineScaleLoss, hSoutdef] using hfull
  · have href1 : ShadedBody.IsRefinement (s.filter (fun i => parent i ∈ t'))
        (fun i => (Z' i).toShadedBody) s (fun i => (V i).toShadedBody) := by
      refine ⟨?_, ?_⟩
      · rw [← hGinner']; exact href.1.1
      · intro i hi
        have hiG : i ∈ G.innerSet := by rw [hGinner']; exact hi
        refine ⟨?_, ?_⟩
        · show ((Z' i).toShadedBody).toConvexSpaceBody =
              ((V i).toShadedBody).toConvexSpaceBody
          rw [hZ'Body i hiG]
          exact (href.1.2 i hiG).1
        · show ((Z' i).toShadedBody).shade <= ((V i).toShadedBody).shade
          rw [show ((Z' i).toShadedBody).shade = (Z' i).shade from rfl, hZ'Shade i hiG]
          exact (href.1.2 i hiG).2
    refine ⟨href1, ?_⟩
    show (((spineScaleLoss (Module.finrank Real E) s.card sigma)⁻¹ : NNReal) : ENNReal) *
        ∑ i ∈ s, volume ((V i).toShadedBody).shade <=
      ∑ i ∈ s.filter (fun i => parent i ∈ t'), volume ((Z' i).toShadedBody).shade
    rw [← hGinner']
    have hsum : ∑ i ∈ G.innerSet, volume ((Z' i).toShadedBody).shade =
        ∑ i ∈ G.innerSet, volume (Sin i).shade :=
      Finset.sum_congr rfl fun i hi => congrArg volume (hZ'Shade i hi)
    rw [hsum]
    exact href.2
  · intro k hk
    have hfiber : G.fiber k = s.filter (fun i => parent i = k) := by
      ext i
      simp only [ShadedBody.ShadedFactorFamily.fiber, Finset.mem_filter,
        hGinner', Finset.mem_filter]
      constructor
      · rintro ⟨⟨hi, _⟩, hpi⟩
        exact ⟨hi, by rw [hGparent] at hpi; exact hpi⟩
      · rintro ⟨hi, hpi⟩
        exact ⟨⟨hi, by rw [hpi]; exact hk⟩, by rw [hGparent]; exact hpi⟩
    have hm := hmult k hk
    have hinEq : ShadedBody.multiplicity (s.filter (fun i => parent i = k))
        (fun i => (Z' i).toShadedBody) = ShadedBody.multiplicity (G.fiber k) Sin := by
      rw [hfiber]
      unfold ShadedBody.multiplicity
      have hsub' : forall i, i ∈ s.filter (fun i => parent i = k) -> i ∈ G.innerSet := by
        intro i hi
        rw [hGinner']
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, by rw [hi.2]; exact hk⟩
      congr 1
      · exact Finset.sum_congr rfl fun i hi => congrArg volume (hZ'Shade i (hsub' i hi))
      · exact congrArg volume (Set.iUnion₂_congr fun i hi => hZ'Shade i (hsub' i hi))
    rw [houtMultEq, hinEq]
    simpa [spineScaleLoss, hSoutdef, hSindef] using hm
  · intro j hj i hi hij
    have hiG : i ∈ G.innerSet := by
      rw [hGinner']; exact Finset.mem_filter.mpr ⟨hi, by rw [hij]; exact hj⟩
    rw [hZ'Shade i hiG, hZrhoShade j hj, ← hOutCarrier j hj]
    exact hthick j hj i hiG (by rw [hGparent]; exact hij)

end Kakeya.ML2Reduction
