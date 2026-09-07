import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GeneralizedADTransport
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import Mathlib.Tactic

/-!
# Generalized pre-grain data with arbitrary Lipschitz constants

This module provides `PureWZ2GeneralPreGrainData`, a version of
`PureWZ2PreGrainData` parameterized by arbitrary Lipschitz and incidence constants.

This enables dilation by a scale `s ≥ max(L_planeMap, L_slope, incidence_factor)`
to normalize all constants to 1, rather than being hardcoded to factor 6.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric ENNReal

attribute [local instance] Classical.propDecidable

/-- Generalized pre-grain data with arbitrary Lipschitz and incidence constants. -/
structure PureWZ2GeneralPreGrainData
    {delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    (shading : WZ1PaperTubeShading family)
    (sigma loss_src : ℝ)
    (L_planeMap L_slope : NNReal) (incidence_factor : ℝ) where
  planeMap : {point : Point3 // point ∈ shading.union} → Point3
  planeMap_lipschitz : LipschitzWith L_planeMap planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence :
    ∀ (index : Fin family.card) (point : Point3),
      ∀ (hpoint : point ∈ shading.carrier index),
        |inner ℝ (family.tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ incidence_factor * delta'
  slope : ℝ → ℝ
  slope_lipschitz : LipschitzOnWith L_slope slope (Set.Icc (-1 : ℝ) 1)
  local_ad :
    ∀ rho : ℝ, delta' ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma) (Kakeya.realRpowENN delta' (-loss_src))
  global_ad :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta' (1 - sigma) (Kakeya.realRpowENN delta' (-loss_src))

/-- Enlarge the two Lipschitz constants without changing the shading, maps,
incidence, or AD certificates. -/
def PureWZ2GeneralPreGrainData.weakenLipschitz
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {Lplane Lslope Lplane' Lslope' : NNReal}
    {incidence : ℝ}
    (data : PureWZ2GeneralPreGrainData shading sigma loss
      Lplane Lslope incidence)
    (hplane : Lplane ≤ Lplane') (hslope : Lslope ≤ Lslope') :
    PureWZ2GeneralPreGrainData shading sigma loss
      Lplane' Lslope' incidence where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz.weaken hplane
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := data.planeMap_incidence
  slope := data.slope
  slope_lipschitz := data.slope_lipschitz.weaken hslope
  local_ad := data.local_ad
  global_ad := data.global_ad

/-- Weaken the AD loss exponent while keeping the same geometric maps and
Lipschitz constants. -/
def PureWZ2GeneralPreGrainData.weakenLoss
    {delta sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {Lplane Lslope : NNReal}
    {incidence : ℝ}
    (data : PureWZ2GeneralPreGrainData shading sigma sourceLoss
      Lplane Lslope incidence)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : sourceLoss ≤ targetLoss) :
    PureWZ2GeneralPreGrainData shading sigma targetLoss
      Lplane Lslope incidence where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := data.planeMap_incidence
  slope := data.slope
  slope_lipschitz := data.slope_lipschitz
  local_ad := by
    intro rho hdeltaRho hrhoOne point
    exact (data.local_ad rho hdeltaRho hrhoOne point).mono_const
      (Kakeya.Assouad.realRpowENN_antitone hdelta hdeltaOne (by linarith))
      (by simp [Kakeya.realRpowENN])
  global_ad := by
    intro height hheight
    exact (data.global_ad height hheight).mono_const
      (Kakeya.Assouad.realRpowENN_antitone hdelta hdeltaOne (by linarith))
      (by simp [Kakeya.realRpowENN])

/-- Restrict generalized pre-grain data to a carrierwise subshading on the
same tube family.  Both AD conclusions pass to subsets and the two maps keep
their original quantitative constants. -/
def PureWZ2GeneralPreGrainData.restrict
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source target : WZ1PaperTubeShading family}
    {Lplane Lslope : NNReal}
    {incidence : ℝ}
    (data : PureWZ2GeneralPreGrainData source sigma loss
      Lplane Lslope incidence)
    (hsub : PaperIsSubshading target source) :
    PureWZ2GeneralPreGrainData target sigma loss
      Lplane Lslope incidence := by
  have hunion : target.union ⊆ source.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hsub index hpoint⟩
  let planeMap : {point : Point3 // point ∈ target.union} → Point3 :=
    fun point => data.planeMap ⟨point, hunion point.prop⟩
  exact
    { planeMap := planeMap
      planeMap_lipschitz := by
        intro first second
        exact data.planeMap_lipschitz
          ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
      planeMap_unit := fun point =>
        data.planeMap_unit ⟨point, hunion point.prop⟩
      planeMap_incidence := by
        intro index point hpoint
        exact data.planeMap_incidence index point (hsub index hpoint)
      slope := data.slope
      slope_lipschitz := data.slope_lipschitz
      local_ad := by
        intro rho hdeltaRho hrhoOne point
        apply (data.local_ad rho hdeltaRho hrhoOne
          ⟨point, hunion point.prop⟩).mono_set
        rintro value ⟨other, hother, rfl⟩
        exact ⟨other, ⟨hunion hother.1, hother.2⟩, rfl⟩
      global_ad := by
        intro height hheight
        apply (data.global_ad height hheight).mono_set
        rintro value ⟨point, hpoint, rfl⟩
        exact ⟨point, ⟨hunion hpoint.1, hpoint.2⟩, rfl⟩ }

/-- Restrict generalized pre-grain data to a genuine tube subfamily.

This is the tube-selection operation used after choosing the mass-popular
cube in Proposition 6.3.  It changes neither geometric map: both AD
conclusions pass to the selected union, and incidence is read through the
stored subfamily embedding. -/
def PureWZ2GeneralPreGrainData.restrictSubfamily
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {Lplane Lslope : NNReal}
    {incidence : ℝ}
    (data : PureWZ2GeneralPreGrainData source sigma loss
      Lplane Lslope incidence)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    PureWZ2GeneralPreGrainData
      (restrictPaperShading selected source) sigma loss
      Lplane Lslope incidence := by
  have hunion : (restrictPaperShading selected source).union ⊆
      source.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨selected.embedding index, hpoint⟩
  let planeMap :
      {point : Point3 //
        point ∈ (restrictPaperShading selected source).union} → Point3 :=
    fun point => data.planeMap ⟨point, hunion point.prop⟩
  exact
    { planeMap := planeMap
      planeMap_lipschitz := by
        intro first second
        exact data.planeMap_lipschitz
          ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
      planeMap_unit := fun point =>
        data.planeMap_unit ⟨point, hunion point.prop⟩
      planeMap_incidence := by
        intro index point hpoint
        rw [selected.tube_eq index]
        exact data.planeMap_incidence
          (selected.embedding index) point hpoint
      slope := data.slope
      slope_lipschitz := data.slope_lipschitz
      local_ad := by
        intro rho hdeltaRho hrhoOne point
        apply (data.local_ad rho hdeltaRho hrhoOne
          ⟨point, hunion point.prop⟩).mono_set
        rintro value ⟨other, hother, rfl⟩
        exact ⟨other, ⟨hunion hother.1, hother.2⟩, rfl⟩
      global_ad := by
        intro height hheight
        apply (data.global_ad height hheight).mono_set
        rintro value ⟨point, hpoint, rfl⟩
        exact ⟨point, ⟨hunion hpoint.1, hpoint.2⟩, rfl⟩ }

/-- Convert standard Lip 6 pre-grain data to generalized form. -/
def PureWZ2PreGrainData.toGeneral
    {delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    {sigma loss_src : ℝ}
    (data : PureWZ2PreGrainData shading sigma loss_src) :
    PureWZ2GeneralPreGrainData shading sigma loss_src 6 6 (6 : ℝ) :=
  { planeMap := data.planeMap
    planeMap_lipschitz := data.planeMap_lipschitz
    planeMap_unit := data.planeMap_unit
    planeMap_incidence := data.planeMap_incidence
    slope := data.slope
    slope_lipschitz := data.slope_lipschitz
    local_ad := data.local_ad
    global_ad := data.global_ad }

/-- Convert a constant Lip-6 pre-grain to Lip-1 generalized form.

Requires proofs that `planeMap` is constant, `slope` is zero on `Icc (-1) 1`,
and incidence is exactly zero. These hold for the pre-grain constructed by
`pre_grain_hypotheses_from_sticky`, where `planeMap` is a fixed perpendicular
vector and `slope` is `fun _ => 0`.

The AD fields are reused unchanged. -/
def PureWZ2PreGrainData.toGeneralOne
    {delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    {sigma loss_src : ℝ}
    (data : PureWZ2PreGrainData shading sigma loss_src)
    (hdelta'_pos : 0 < delta')
    (h_planeMap_const :
      ∃ (v : Point3), ∀ (x : {point : Point3 // point ∈ shading.union}),
        data.planeMap x = v)
    (h_slope_zero :
      ∀ (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 → data.slope x = 0)
    (h_incidence_zero :
      ∀ (index : Fin family.card) (point : Point3)
        (hpoint : point ∈ shading.carrier index),
        inner ℝ (family.tube index).direction
          (data.planeMap ⟨point, ⟨index, hpoint⟩⟩) = 0) :
    PureWZ2GeneralPreGrainData shading sigma loss_src 1 1 (1 : ℝ) :=
  have hdelta'_nonneg : 0 ≤ delta' := hdelta'_pos.le
  { planeMap := data.planeMap
    planeMap_lipschitz := by
      rcases h_planeMap_const with ⟨v, hv⟩
      intro x y
      have h1 : data.planeMap x = v := hv x
      have h2 : data.planeMap y = v := hv y
      have h_main : edist (data.planeMap x) (data.planeMap y) = 0 := by
        rw [h1, h2]; simp
      rw [h_main]; simp
    planeMap_unit := data.planeMap_unit
    planeMap_incidence := by
      intro index point hpoint
      have h := h_incidence_zero index point hpoint
      rw [h]
      have h_abs : |(0 : ℝ)| = 0 := by simp
      rw [h_abs]; linarith
    slope := data.slope
    slope_lipschitz := by
      intro x hx y hy
      have h1 : data.slope x = 0 := h_slope_zero x hx
      have h2 : data.slope y = 0 := h_slope_zero y hy
      have h_main : edist (data.slope x) (data.slope y) = 0 := by
        rw [h1, h2]; simp
      rw [h_main]; simp
    local_ad := data.local_ad
    global_ad := data.global_ad }

end Kakeya.Assouad

end
