import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SelectedTubeFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredFullFiberCWA
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Selected centered targets inside one complete strict full fiber

This module reindexes a selected set of source indices inside one literal
strict full fiber as centered ordinary target tubes.  The target shading is
the exact centered affine image of the original source shading.

All source provenance is through `wz2PaperPureFullFiberSubfamily`; no assigned
parent map or assigned-fiber API occurs.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Full-fiber indices whose ambient fine index belongs to `selected`. -/
def wz2PaperCenteredSelectedFullFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (selected : Finset (Fin fine.card)) :
    Finset
      (Fin (wz2PaperPureFullFiberSubfamily
        fine coarse parent).family.card) :=
  Finset.univ.filter fun fiberIndex =>
    (wz2PaperPureFullFiberSubfamily
      fine coarse parent).embedding fiberIndex ∈ selected

/-- The centered ordinary target family on exactly the selected source
indices in one strict full fiber. -/
def wz2PaperCenteredSelectedFullFiberFamily
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (selected : Finset (Fin fine.card)) :
    Kakeya.Streamlined.TubeFamily (delta / rho) :=
  selectedTubeFamily
    (wz2PaperCenteredPublicFullFiberFamily
      fine coarse parent hrho)
    (wz2PaperCenteredSelectedFullFiberIndices
      fine coarse parent selected)

/-- Original fine-family index represented by one selected centered target. -/
def wz2PaperCenteredSelectedFullFiberSourceIndex
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (selected : Finset (Fin fine.card)) :
    Fin (wz2PaperCenteredSelectedFullFiberFamily
      fine coarse parent hrho selected).card →
      Fin fine.card := fun target =>
  let selectedFiber :=
    wz2PaperCenteredSelectedFullFiberIndices
      fine coarse parent selected
  let fiberIndex : Fin
      (wz2PaperPureFullFiberSubfamily
        fine coarse parent).family.card :=
    (selectedFiber.equivFin.symm target).1
  (wz2PaperPureFullFiberSubfamily
    fine coarse parent).embedding fiberIndex

theorem wz2PaperCenteredSelectedFullFiberSourceIndex_mem_selected
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (selected : Finset (Fin fine.card))
    (target : Fin (wz2PaperCenteredSelectedFullFiberFamily
      fine coarse parent hrho selected).card) :
    wz2PaperCenteredSelectedFullFiberSourceIndex
      fine coarse parent hrho selected target ∈ selected := by
  let selectedFiber :=
    wz2PaperCenteredSelectedFullFiberIndices
      fine coarse parent selected
  have hmembership :
      (selectedFiber.equivFin.symm target).1 ∈ selectedFiber :=
    (selectedFiber.equivFin.symm target).2
  exact (Finset.mem_filter.mp hmembership).2

theorem wz2PaperCenteredSelectedFullFiberSourceIndex_mem_fullFiber
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (selected : Finset (Fin fine.card))
    (target : Fin (wz2PaperCenteredSelectedFullFiberFamily
      fine coarse parent hrho selected).card) :
    wz2PaperCenteredSelectedFullFiberSourceIndex
        fine coarse parent hrho selected target ∈
      wz2PaperOrdinaryFullFiberIndices fine coarse parent := by
  let selectedFiber :=
    wz2PaperCenteredSelectedFullFiberIndices
      fine coarse parent selected
  let fiberIndex : Fin
      (wz2PaperPureFullFiberSubfamily
        fine coarse parent).family.card :=
    (selectedFiber.equivFin.symm target).1
  exact
    Finset.orderEmbOfFin_mem
      (wz2PaperOrdinaryFullFiberIndices fine coarse parent)
      rfl fiberIndex

/-- The selected centered family has exactly the ambient selected indices
whose literal geometric parent is `parent`. -/
theorem wz2PaperCenteredSelectedFullFiberFamily_card_eq_parent_filter
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (selected : Finset (Fin fine.card)) :
    (wz2PaperCenteredSelectedFullFiberFamily
        fine coarse parent hrho selected).card =
      (selected.filter fun source =>
        cover.parent source = parent).card := by
  let fiber :=
    wz2PaperOrdinaryFullFiberIndices fine coarse parent
  let selectedFiber :=
    wz2PaperCenteredSelectedFullFiberIndices
      fine coarse parent selected
  have himage :
      selectedFiber.map (fiber.orderEmbOfFin rfl).toEmbedding =
        selected.filter fun source =>
          cover.parent source = parent := by
    ext source
    constructor
    · intro hsource
      rcases Finset.mem_map.mp hsource with
        ⟨fiberIndex, hfiberIndex, rfl⟩
      have hselected :
          (fiber.orderEmbOfFin rfl fiberIndex) ∈ selected :=
        (Finset.mem_filter.mp hfiberIndex).2
      have hfull :
          (fiber.orderEmbOfFin rfl fiberIndex) ∈ fiber :=
        Finset.orderEmbOfFin_mem fiber rfl fiberIndex
      exact
        Finset.mem_filter.mpr
          ⟨hselected,
            (cover.mem_fullFiber_iff_parent_eq
              hrho.le parent _).mp hfull⟩
    · intro hsource
      rcases Finset.mem_filter.mp hsource with
        ⟨hselected, hparent⟩
      have hfull : source ∈ fiber :=
        (cover.mem_fullFiber_iff_parent_eq
          hrho.le parent source).mpr hparent
      let fiberIndex : Fin fiber.card :=
        (fiber.orderIsoOfFin rfl).symm ⟨source, hfull⟩
      have hvalue :
          fiber.orderEmbOfFin rfl fiberIndex = source := by
        exact congr_arg Subtype.val
          ((fiber.orderIsoOfFin rfl).apply_symm_apply
            ⟨source, hfull⟩)
      apply Finset.mem_map.mpr
      refine ⟨fiberIndex, ?_, hvalue⟩
      have hembedding :
          (wz2PaperPureFullFiberSubfamily
            fine coarse parent).embedding fiberIndex = source := by
        change fiber.orderEmbOfFin rfl fiberIndex = source
        exact hvalue
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ fiberIndex, by
            rw [hembedding]
            exact hselected⟩
  change selectedFiber.card =
    (selected.filter fun source =>
      cover.parent source = parent).card
  rw [← himage]
  exact
    (Finset.card_map
      (s := selectedFiber)
      (fiber.orderEmbOfFin rfl).toEmbedding).symm

theorem wz2PaperCenteredSelectedFullFiberFamily_tube
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (selected : Finset (Fin fine.card))
    (target : Fin (wz2PaperCenteredSelectedFullFiberFamily
      fine coarse parent hrho selected).card) :
    (wz2PaperCenteredSelectedFullFiberFamily
      fine coarse parent hrho selected).tube target =
      wz2PaperCenteredLiteralOrdinaryRescaledTube
        (fine.tube
          (wz2PaperCenteredSelectedFullFiberSourceIndex
            fine coarse parent hrho selected target))
        (coarse.tube parent) hrho := by
  let selectedFiber :=
    wz2PaperCenteredSelectedFullFiberIndices
      fine coarse parent selected
  let fiberIndex : Fin
      (wz2PaperPureFullFiberSubfamily
        fine coarse parent).family.card :=
    (selectedFiber.equivFin.symm target).1
  change
    wz2PaperCenteredLiteralOrdinaryRescaledTube
        ((wz2PaperPureFullFiberSubfamily
          fine coarse parent).family.tube fiberIndex)
        (coarse.tube parent) hrho =
      wz2PaperCenteredLiteralOrdinaryRescaledTube
        (fine.tube
          ((wz2PaperPureFullFiberSubfamily
            fine coarse parent).embedding fiberIndex))
        (coarse.tube parent) hrho
  rw [(wz2PaperPureFullFiberSubfamily
    fine coarse parent).tube_eq fiberIndex]

/-- Every tube in the selected centered strict fiber lies in the unit ball
once the rescaled radius is sufficiently small. -/
theorem wz2PaperCenteredSelectedFullFiberFamily_isInUnitBall
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdeltaRho : delta ≤ rho)
    (hscaleSmall : delta / rho ≤ 39 / 80)
    (selected : Finset (Fin fine.card)) :
    (wz2PaperCenteredSelectedFullFiberFamily
      fine coarse parent hrho selected).IsInUnitBall := by
  intro target
  rw [wz2PaperCenteredSelectedFullFiberFamily_tube]
  apply centered_target_unit_ball
    (fine.tube
      (wz2PaperCenteredSelectedFullFiberSourceIndex
        fine coarse parent hrho selected target))
    (coarse.tube parent)
    hdelta hrho hdeltaRho hrhoSmall
  · exact
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        parent
        (wz2PaperCenteredSelectedFullFiberSourceIndex
          fine coarse parent hrho selected target)).mp
        (wz2PaperCenteredSelectedFullFiberSourceIndex_mem_fullFiber
          fine coarse parent hrho selected target)
  · exact hscaleSmall

/-- Exact centered affine-image shading on the selected target family. -/
def wz2PaperCenteredSelectedFullFiberShading
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdeltaRho : delta ≤ rho)
    (selected : Finset (Fin fine.card))
    (sourceShading : Kakeya.Streamlined.TubeShading fine) :
    Kakeya.Streamlined.TubeShading
      (wz2PaperCenteredSelectedFullFiberFamily
        fine coarse parent hrho selected) where
  carrier target :=
    wz2PaperCenteredLiteralRescalingAffineEquiv
        (coarse.tube parent) hrho ''
      sourceShading.carrier
        (wz2PaperCenteredSelectedFullFiberSourceIndex
          fine coarse parent hrho selected target)
  measurable_carrier target := by
    let equivalence :=
      wz2PaperCenteredLiteralRescalingAffineEquiv
        (coarse.tube parent) hrho
    let sourceSet :=
      sourceShading.carrier
        (wz2PaperCenteredSelectedFullFiberSourceIndex
          fine coarse parent hrho selected target)
    have himage :
        equivalence '' sourceSet =
          equivalence.symm ⁻¹' sourceSet := by
      ext point
      constructor
      · rintro ⟨sourcePoint, hsource, rfl⟩
        simpa using hsource
      · intro hsource
        exact
          ⟨equivalence.symm point, hsource,
            equivalence.apply_symm_apply point⟩
    rw [himage]
    exact
      (sourceShading.measurable_carrier
        (wz2PaperCenteredSelectedFullFiberSourceIndex
          fine coarse parent hrho selected target)).preimage
        equivalence.symm.continuous_of_finiteDimensional.measurable
  subset_body target := by
    change
      wz2PaperCenteredLiteralRescalingAffineEquiv
          (coarse.tube parent) hrho ''
        sourceShading.carrier
          (wz2PaperCenteredSelectedFullFiberSourceIndex
            fine coarse parent hrho selected target) ⊆
      ((wz2PaperCenteredSelectedFullFiberFamily
        fine coarse parent hrho selected).tube target).carrier
    rw [wz2PaperCenteredSelectedFullFiberFamily_tube]
    have hsourceContainment :
        (fine.tube
          (wz2PaperCenteredSelectedFullFiberSourceIndex
            fine coarse parent hrho selected target)).carrier ⊆
          (coarse.tube parent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        parent
        (wz2PaperCenteredSelectedFullFiberSourceIndex
          fine coarse parent hrho selected target)).mp
        (wz2PaperCenteredSelectedFullFiberSourceIndex_mem_fullFiber
          fine coarse parent hrho selected target)
    intro imagePoint himagePoint
    rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
    have hsourceTube :
        sourcePoint ∈
          (fine.tube
            (wz2PaperCenteredSelectedFullFiberSourceIndex
              fine coarse parent hrho selected target)).carrier :=
      sourceShading.subset_body
        (wz2PaperCenteredSelectedFullFiberSourceIndex
          fine coarse parent hrho selected target)
        hsourcePoint
    exact
      centered_image_carrier_subset
        hdelta
        (fine.tube
          (wz2PaperCenteredSelectedFullFiberSourceIndex
            fine coarse parent hrho selected target))
        (coarse.tube parent) hrho hrhoOne hrhoSmall
        hdeltaRho hsourceContainment
        ⟨sourcePoint, hsourceTube,
          (wz2PaperCenteredLiteralRescalingAffineEquiv_apply
            (coarse.tube parent) hrho sourcePoint).symm⟩

/-- Exact determinant formula for one selected target shaded carrier. -/
theorem wz2PaperCenteredSelectedFullFiberShading_volume
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdeltaRho : delta ≤ rho)
    (selected : Finset (Fin fine.card))
    (sourceShading : Kakeya.Streamlined.TubeShading fine)
    (target : Fin (wz2PaperCenteredSelectedFullFiberFamily
      fine coarse parent hrho selected).card) :
    MeasureTheory.volume
        ((wz2PaperCenteredSelectedFullFiberShading
          fine coarse parent hdelta hrho hrhoOne hrhoSmall
          hdeltaRho selected sourceShading).carrier target) =
      ENNReal.ofReal
          ((1 / 100 : ℝ) ^ 3 * (1 / rho) ^ 2) *
        MeasureTheory.volume
          (sourceShading.carrier
            (wz2PaperCenteredSelectedFullFiberSourceIndex
              fine coarse parent hrho selected target)) := by
  change
    MeasureTheory.volume
        (wz2PaperCenteredLiteralRescalingAffineEquiv
            (coarse.tube parent) hrho ''
          sourceShading.carrier
            (wz2PaperCenteredSelectedFullFiberSourceIndex
              fine coarse parent hrho selected target)) =
      ENNReal.ofReal
          ((1 / 100 : ℝ) ^ 3 * (1 / rho) ^ 2) *
        MeasureTheory.volume
          (sourceShading.carrier
            (wz2PaperCenteredSelectedFullFiberSourceIndex
              fine coarse parent hrho selected target))
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have hlinear :
      (wz2PaperCenteredLiteralRescalingAffineEquiv
        (coarse.tube parent) hrho).linear =
        (wz2PaperLiteralUnitRescalingAffineEquiv
          (coarse.tube parent) hrho).linear := by
    rfl
  rw [hlinear,
    wz2PaperLiteralUnitRescalingAffineEquiv_abs_det
      (coarse.tube parent) hrho]

/-- Exact Jacobian factor of the centered literal rescaling. -/
def pureWZ2CenteredJacobian (rho : ℝ) : ENNReal :=
  ENNReal.ofReal
    ((1 / 100 : ℝ) ^ 3 * (1 / rho) ^ 2)

/-- The density constant obtained after exact centered affine rescaling. -/
def pureWZ2CenteredDensityConstant
    (delta rho : ℝ) (densityConstant : ENNReal) : ENNReal :=
  pureWZ2CenteredJacobian rho *
    densityConstant *
    Kakeya.deltaTubeVolume delta *
    (Kakeya.deltaTubeVolume (delta / rho))⁻¹

/-- The selected centered shading lies in the centered image of the original
shaded union. -/
theorem wz2PaperCenteredSelectedFullFiberShading_union_subset
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdeltaRho : delta ≤ rho)
    (selected : Finset (Fin fine.card))
    (sourceShading : Kakeya.Streamlined.TubeShading fine) :
    (wz2PaperCenteredSelectedFullFiberShading
      fine coarse parent hdelta hrho hrhoOne hrhoSmall
      hdeltaRho selected sourceShading).union ⊆
      wz2PaperCenteredLiteralRescalingAffineEquiv
          (coarse.tube parent) hrho ''
        sourceShading.union := by
  rintro point ⟨target, hpoint⟩
  change
    point ∈
      wz2PaperCenteredLiteralRescalingAffineEquiv
          (coarse.tube parent) hrho ''
        sourceShading.carrier
          (wz2PaperCenteredSelectedFullFiberSourceIndex
            fine coarse parent hrho selected target) at hpoint
  rcases hpoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  exact
    ⟨sourcePoint,
      ⟨wz2PaperCenteredSelectedFullFiberSourceIndex
          fine coarse parent hrho selected target,
        hsourcePoint⟩,
      rfl⟩

/-- Pointwise source density transfers exactly to the centered selected
strict fiber after accounting for the common source and target tube
volumes. -/
theorem wz2PaperCenteredSelectedFullFiberShading_perTube
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdeltaRho : delta ≤ rho)
    (selected : Finset (Fin fine.card))
    (sourceShading : Kakeya.Streamlined.TubeShading fine)
    (densityConstant : ENNReal)
    (hperTube :
      ∀ source ∈ selected,
        densityConstant * (fine.tube source).volume ≤
          MeasureTheory.volume
            (sourceShading.carrier source)) :
    ∀ target,
      pureWZ2CenteredDensityConstant
            delta rho densityConstant *
          ((wz2PaperCenteredSelectedFullFiberFamily
            fine coarse parent hrho selected).tube target).volume ≤
        MeasureTheory.volume
          ((wz2PaperCenteredSelectedFullFiberShading
            fine coarse parent hdelta hrho hrhoOne hrhoSmall
            hdeltaRho selected sourceShading).carrier target) := by
  intro target
  let targetScale := delta / rho
  have htargetScale : 0 < targetScale := div_pos hdelta hrho
  have htargetScaleOne : targetScale ≤ 1 :=
    (div_le_one hrho).mpr hdeltaRho
  have htargetVolumeZero :
      Kakeya.deltaTubeVolume targetScale ≠ 0 :=
    (tube_volume_scaling.2.1 targetScale
      htargetScale htargetScaleOne).1.ne'
  have htargetVolumeTop :
      Kakeya.deltaTubeVolume targetScale ≠ ⊤ :=
    (tube_volume_scaling.2.1 targetScale
      htargetScale htargetScaleOne).2
  have hsourceVolume :
      (fine.tube
        (wz2PaperCenteredSelectedFullFiberSourceIndex
          fine coarse parent hrho selected target)).volume =
        Kakeya.deltaTubeVolume delta :=
    tube_volume_scaling.1 delta _
  have htargetVolume :
      ((wz2PaperCenteredSelectedFullFiberFamily
        fine coarse parent hrho selected).tube target).volume =
        Kakeya.deltaTubeVolume targetScale :=
    tube_volume_scaling.1 targetScale _
  rw [wz2PaperCenteredSelectedFullFiberShading_volume,
    htargetVolume]
  change
    (pureWZ2CenteredJacobian rho *
        densityConstant *
        Kakeya.deltaTubeVolume delta *
        (Kakeya.deltaTubeVolume targetScale)⁻¹) *
        Kakeya.deltaTubeVolume targetScale ≤
      pureWZ2CenteredJacobian rho *
        MeasureTheory.volume
          (sourceShading.carrier
            (wz2PaperCenteredSelectedFullFiberSourceIndex
              fine coarse parent hrho selected target))
  have hcancel :
      (Kakeya.deltaTubeVolume targetScale)⁻¹ *
          Kakeya.deltaTubeVolume targetScale = 1 :=
    ENNReal.inv_mul_cancel htargetVolumeZero htargetVolumeTop
  rw [show
    (pureWZ2CenteredJacobian rho *
        densityConstant *
        Kakeya.deltaTubeVolume delta *
        (Kakeya.deltaTubeVolume targetScale)⁻¹) *
        Kakeya.deltaTubeVolume targetScale =
      pureWZ2CenteredJacobian rho *
        (densityConstant *
          Kakeya.deltaTubeVolume delta) by
      rw [mul_assoc, hcancel, mul_one]
      ring]
  gcongr
  rw [← hsourceVolume]
  exact
    hperTube
      (wz2PaperCenteredSelectedFullFiberSourceIndex
        fine coarse parent hrho selected target)
      (wz2PaperCenteredSelectedFullFiberSourceIndex_mem_selected
        fine coarse parent hrho selected target)

/-- Restrict a body CWA to selected indices with an explicit cardinality
fraction. -/
theorem wz2PaperBodyConvexWolffBound_selectedTubeFamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C weight : ENNReal}
    (hCWA : WZ2PaperBodyConvexWolffBound family.toBodyFamily C)
    (selected : Finset (Fin family.card))
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hretention :
      weight * family.enncard ≤
        (selectedTubeFamily family selected).enncard) :
    WZ2PaperBodyConvexWolffBound
      (selectedTubeFamily family selected).toBodyFamily
      (weight⁻¹ * C) := by
  let selectedFamily := selectedTubeFamily family selected
  let toAmbient : Fin selectedFamily.card → Fin family.card :=
    fun index => (selected.equivFin.symm index).1
  have hinjective : Function.Injective toAmbient := by
    intro first second heq
    apply selected.equivFin.symm.injective
    exact Subtype.ext heq
  have hambientCard :
      family.enncard ≤ weight⁻¹ * selectedFamily.enncard := by
    calc
      family.enncard =
          (weight⁻¹ * weight) * family.enncard := by
        rw [ENNReal.inv_mul_cancel hweightZero hweightTop, one_mul]
      _ = weight⁻¹ * (weight * family.enncard) := by
        ring
      _ ≤ weight⁻¹ * selectedFamily.enncard := by
        gcongr
  intro convexSet hconvex
  let selectedContained :=
    selectedFamily.toBodyFamily.containedIndices convexSet
  let ambientContained :=
    family.toBodyFamily.containedIndices convexSet
  have hsubset :
      Finset.image toAmbient selectedContained ⊆ ambientContained := by
    intro ambientIndex hindex
    rcases Finset.mem_image.mp hindex with
      ⟨selectedIndex, hselectedIndex, rfl⟩
    exact
      Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
        ((Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp
          hselectedIndex) : (family.tube (toAmbient selectedIndex)).carrier ⊆
            convexSet)
  have hcount :
      selectedFamily.toBodyFamily.containedCount convexSet ≤
        family.toBodyFamily.containedCount convexSet := by
    change (selectedContained.card : ENNReal) ≤
      (ambientContained.card : ENNReal)
    exact_mod_cast
      (calc
        selectedContained.card =
            (Finset.image toAmbient selectedContained).card :=
          (Finset.card_image_of_injective
            selectedContained hinjective).symm
        _ ≤ ambientContained.card := Finset.card_le_card hsubset)
  calc
    selectedFamily.toBodyFamily.containedCount convexSet ≤
        family.toBodyFamily.containedCount convexSet := hcount
    _ ≤ C * MeasureTheory.volume convexSet * family.enncard :=
      hCWA convexSet hconvex
    _ ≤ C * MeasureTheory.volume convexSet *
          (weight⁻¹ * selectedFamily.enncard) := by
      gcongr
    _ = (weight⁻¹ * C) * MeasureTheory.volume convexSet *
          selectedFamily.enncard := by
      ring

end Kakeya.Assouad

end
