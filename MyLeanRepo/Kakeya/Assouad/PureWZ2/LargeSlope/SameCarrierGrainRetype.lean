import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Retyping grain data across unchanged carriers

This file records the small orientation-free interface needed when a family
of ordinary tube representatives is replaced without changing its shaded
sets.  Indices may be relabelled, and directions may be reversed.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Data identifying two shaded tube families carrier by carrier.  Reversing
a tube direction is allowed because local grain incidence is inside an
absolute value. -/
structure PureWZ2SameCarrierGrainRetype
    {delta : ℝ}
    (sourceFamily targetFamily : Kakeya.Streamlined.TubeFamily delta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (targetShading : WZ1PaperTubeShading targetFamily) where
  indexEquiv : Fin targetFamily.card ≃ Fin sourceFamily.card
  carrier_eq :
    ∀ index, targetShading.carrier index =
      sourceShading.carrier (indexEquiv index)
  direction_eq_or_neg :
    ∀ index,
      (targetFamily.tube index).direction =
          (sourceFamily.tube (indexEquiv index)).direction ∨
        (targetFamily.tube index).direction =
          -(sourceFamily.tube (indexEquiv index)).direction

namespace PureWZ2SameCarrierGrainRetype

variable
    {delta : ℝ}
    {sourceFamily targetFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {targetShading : WZ1PaperTubeShading targetFamily}

/-- Carrier-by-carrier equality along an index equivalence gives equality of
the shaded unions. -/
theorem union_eq
    (retype : PureWZ2SameCarrierGrainRetype sourceFamily targetFamily
      sourceShading targetShading) :
    targetShading.union = sourceShading.union := by
  ext point
  constructor
  · rintro ⟨index, hpoint⟩
    exact ⟨retype.indexEquiv index, by
      rw [← retype.carrier_eq index]
      exact hpoint⟩
  · rintro ⟨index, hpoint⟩
    refine ⟨retype.indexEquiv.symm index, ?_⟩
    rw [retype.carrier_eq]
    simpa using hpoint

/-- The identity-on-points map between the two equal shaded unions. -/
def pointEquiv
    (retype : PureWZ2SameCarrierGrainRetype sourceFamily targetFamily
      sourceShading targetShading) :
    {point : Point3 // point ∈ targetShading.union} ≃
      {point : Point3 // point ∈ sourceShading.union} :=
  Equiv.setCongr retype.union_eq

@[simp] theorem pointEquiv_coe
    (retype : PureWZ2SameCarrierGrainRetype sourceFamily targetFamily
      sourceShading targetShading)
    (point : {point : Point3 // point ∈ targetShading.union}) :
    ((retype.pointEquiv point :
      {point : Point3 // point ∈ sourceShading.union}) : Point3) = point :=
  rfl

theorem pointEquiv_lipschitz
    (retype : PureWZ2SameCarrierGrainRetype sourceFamily targetFamily
      sourceShading targetShading) :
    LipschitzWith 1 retype.pointEquiv := by
  intro first second
  simp only [Subtype.edist_eq, pointEquiv_coe, ENNReal.coe_one, one_mul]
  exact le_rfl

end PureWZ2SameCarrierGrainRetype

/-- Retype global grain data across the same shaded union. -/
def PureWZ2C2GlobalGrainData.retypeSameCarrier
    {delta : ℝ}
    {sourceFamily targetFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {targetShading : WZ1PaperTubeShading targetFamily}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData sourceShading sigma C)
    (retype : PureWZ2SameCarrierGrainRetype sourceFamily targetFamily
      sourceShading targetShading) :
    PureWZ2C2GlobalGrainData targetShading sigma C where
  f := data.f
  normalized := data.normalized
  global_ad := by
    intro z
    rw [retype.union_eq]
    exact data.global_ad z

@[simp] theorem PureWZ2C2GlobalGrainData.slope_retypeSameCarrier
    {delta : ℝ}
    {sourceFamily targetFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {targetShading : WZ1PaperTubeShading targetFamily}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData sourceShading sigma C)
    (retype : PureWZ2SameCarrierGrainRetype sourceFamily targetFamily
      sourceShading targetShading) :
    (data.retypeSameCarrier retype).slope = data.slope :=
  rfl

/-- Retype local grain data across unchanged carriers and orientation-free
tube directions. -/
def PureWZ2LocalGrainData.retypeSameCarrier
    {delta : ℝ}
    {sourceFamily targetFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {targetShading : WZ1PaperTubeShading targetFamily}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2LocalGrainData sourceShading sigma C)
    (retype : PureWZ2SameCarrierGrainRetype sourceFamily targetFamily
      sourceShading targetShading) :
    PureWZ2LocalGrainData targetShading sigma C where
  planeMap := fun point => data.planeMap (retype.pointEquiv point)
  planeMap_lipschitz := by
    simpa [Function.comp_def] using
      data.planeMap_lipschitz.comp retype.pointEquiv_lipschitz
  planeMap_unit := fun point => data.planeMap_unit (retype.pointEquiv point)
  planeMap_incidence := by
    intro index point hpoint
    have hsource :
        point ∈ sourceShading.carrier (retype.indexEquiv index) := by
      rw [← retype.carrier_eq index]
      exact hpoint
    have hincidence := data.planeMap_incidence
      (retype.indexEquiv index) point hsource
    rcases retype.direction_eq_or_neg index with hdirection | hdirection
    · simpa [hdirection, PureWZ2SameCarrierGrainRetype.pointEquiv]
        using hincidence
    · simpa [hdirection, inner_neg_left, abs_neg,
        PureWZ2SameCarrierGrainRetype.pointEquiv] using hincidence
  local_ad := by
    intro rho hdeltaRho hrhoOne point
    simpa [PureWZ2SameCarrierGrainRetype.pointEquiv, retype.union_eq] using
      data.local_ad rho hdeltaRho hrhoOne (retype.pointEquiv point)

@[simp] theorem PureWZ2LocalGrainData.planeMap_retypeSameCarrier
    {delta : ℝ}
    {sourceFamily targetFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {targetShading : WZ1PaperTubeShading targetFamily}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2LocalGrainData sourceShading sigma C)
    (retype : PureWZ2SameCarrierGrainRetype sourceFamily targetFamily
      sourceShading targetShading)
    (point : {point : Point3 // point ∈ targetShading.union}) :
    (data.retypeSameCarrier retype).planeMap point =
      data.planeMap (retype.pointEquiv point) :=
  rfl

end Kakeya.Assouad

end
