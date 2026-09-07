import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05PostGrainReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.GrainRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationSynchronizedPerTubeCore

/-!
# Synchronized post-grain re-entry

The first grain call changes the cropped shading.  Consequently the identity
family cannot inherit the ancestor's per-tube ordinary density.  This module
performs one new indexed pruning on the literal overlap with the *actual*
post-grain shading.  The ordinary and cropped traces are then restricted on
the same retained cropped indices.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Dense cubicalization is unchanged after intersecting its ordinary source
with a positive-mass union of whole grid cells. -/
private lemma denseCubicalization_inter_whole_cells_selected
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (ordinary cropped : Set Point3)
    (hdelta : 0 < delta)
    (hcropped : cropped ⊆ pureWZ2DenseCubicalization tube ordinary)
    (hwhole : ∀ point ∈ cropped,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆ cropped)
    (hpositive : 0 < volume (ordinary ∩ cropped)) :
    pureWZ2DenseCubicalization tube (ordinary ∩ cropped) = cropped := by
  ext point
  constructor
  · intro hpoint
    by_contra hpointCropped
    have hempty :
        (ordinary ∩ cropped) ∩
            wz1PaperGridCube delta (wz1PaperGridIndex delta point) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨other, hother⟩
      have hgrid : wz1PaperGridIndex delta other =
          wz1PaperGridIndex delta point :=
        (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta point) other).mp hother.2
      have hpointCell : point ∈
          wz1PaperGridCube delta (wz1PaperGridIndex delta other) :=
        (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta other) point).mpr hgrid.symm
      exact hpointCropped (hwhole other hother.1.2 hpointCell)
    have hinvPositive : 0 < (volume tube.carrier)⁻¹ :=
      ENNReal.inv_pos.mpr
        (wz2_paper_ordinary_tube_volume_ne_top tube hdelta)
    have hcubePositive : 0 <
        volume (wz1PaperGridCube delta
          (wz1PaperGridIndex delta point)) :=
      wz1PaperGridCube_volume_pos hdelta _
    have hfactorPositive : 0 <
        (100 : ENNReal)⁻¹ * volume (ordinary ∩ cropped) *
          (volume tube.carrier)⁻¹ *
          volume (wz1PaperGridCube delta
            (wz1PaperGridIndex delta point)) := by
      exact ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos (ENNReal.inv_pos.mpr (by norm_num)).ne'
            hpositive.ne').ne' hinvPositive.ne').ne' hcubePositive.ne'
    have hzero : volume
        ((ordinary ∩ cropped) ∩
          wz1PaperGridCube delta
            (wz1PaperGridIndex delta point)) = 0 := by
      rw [hempty]
      exact measure_empty
    have hle := hpoint.2
    rw [hzero] at hle
    exact (not_lt_of_ge hle) hfactorPositive
  · intro hpoint
    have hold := hcropped hpoint
    refine ⟨hold.1, ?_⟩
    have hsourceMass : volume (ordinary ∩ cropped) ≤ volume ordinary :=
      measure_mono Set.inter_subset_left
    have hcellSubset :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆ cropped :=
      hwhole point hpoint
    have hintersection :
        (ordinary ∩ cropped) ∩
            wz1PaperGridCube delta (wz1PaperGridIndex delta point) =
          ordinary ∩
            wz1PaperGridCube delta (wz1PaperGridIndex delta point) := by
      ext other
      constructor
      · rintro ⟨⟨hordinary, _⟩, hcell⟩
        exact ⟨hordinary, hcell⟩
      · rintro ⟨hordinary, hcell⟩
        exact ⟨⟨hordinary, hcellSubset hcell⟩, hcell⟩
    calc
      (100 : ENNReal)⁻¹ * volume (ordinary ∩ cropped) *
            (volume tube.carrier)⁻¹ *
            volume (wz1PaperGridCube delta
              (wz1PaperGridIndex delta point))
          ≤ (100 : ENNReal)⁻¹ * volume ordinary *
            (volume tube.carrier)⁻¹ *
            volume (wz1PaperGridCube delta
              (wz1PaperGridIndex delta point)) := by
              gcongr
      _ ≤ volume
          (ordinary ∩ wz1PaperGridCube delta
            (wz1PaperGridIndex delta point)) := hold.2
      _ = volume
          ((ordinary ∩ cropped) ∩
            wz1PaperGridCube delta
              (wz1PaperGridIndex delta point)) := by
              rw [hintersection]

/-- Literal framed-ordinary overlap with the actual post-grain shading. -/
noncomputable def pureWZ2Node05PostGrainOverlapShading
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss) :
    Kakeya.Streamlined.TubeShading coarseRefinement.selected.family where
  carrier index :=
    (ancestor.geometry.frame ''
        ancestor.geometry.ordinaryRefined.carrier
          (ancestor.geometry.indexEquiv.symm index)) ∩
      coarseGrains.shading.carrier index
  measurable_carrier index := by
    let measurableFrame : Point3 ≃ᵐ Point3 :=
      { toFun := ancestor.geometry.frame
        invFun := ancestor.geometry.frame.symm
        left_inv := ancestor.geometry.frame.left_inv
        right_inv := ancestor.geometry.frame.right_inv
        measurable_toFun :=
          ancestor.geometry.frame.continuous_of_finiteDimensional.measurable
        measurable_invFun :=
          ancestor.geometry.frame.symm.continuous_of_finiteDimensional.measurable }
    exact ((measurableFrame.measurableSet_image).mpr
      (ancestor.geometry.ordinaryRefined.measurable_carrier
        (ancestor.geometry.indexEquiv.symm index))).inter
      (coarseGrains.shading.measurable_carrier index)
  subset_body index := by
    intro point pointMem
    rcases pointMem.1 with ⟨ordinaryPoint, ordinaryPointMem, rfl⟩
    have imageBody :
        ancestor.geometry.frame ordinaryPoint ∈
          ancestor.geometry.frame ''
            (ancestor.geometry.selected.family.tube
              (ancestor.geometry.indexEquiv.symm index)).carrier :=
      ⟨ordinaryPoint,
        ancestor.geometry.ordinaryRefined.subset_body
          (ancestor.geometry.indexEquiv.symm index) ordinaryPointMem, rfl⟩
    rw [← ancestor.geometry.ordinary_carrier_image_eq
      (ancestor.geometry.indexEquiv.symm index),
      ancestor.geometry.indexEquiv.apply_symm_apply index] at imageBody
    exact imageBody

/-- The retained cropped family, with its embedding into the first coarse
refinement exposed rather than hidden behind a fresh existential family. -/
noncomputable def pureWZ2Node05PostGrainSelectedSubfamily
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (retained : Finset (Fin family.card)) :
    Kakeya.Streamlined.TubeSubfamily family where
  family := selectedTubeFamily family retained
  embedding :=
    ⟨fun index => (retained.equivFin.symm index).1, by
      intro first second equality
      apply retained.equivFin.symm.injective
      exact Subtype.ext equality⟩
  tube_eq _ := rfl

/-- The corresponding ordinary subfamily.  Its index `i` is sent through the
stored ancestor equivalence to exactly the retained cropped index `i`. -/
noncomputable def pureWZ2Node05PostGrainSelectedOrdinarySubfamily
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (retained : Finset (Fin coarseRefinement.selected.family.card)) :
    Kakeya.Streamlined.TubeSubfamily ancestor.geometry.selected.family where
  family :=
    { card := retained.card
      tube := fun index => ancestor.geometry.selected.family.tube
        (ancestor.geometry.indexEquiv.symm
          ((retained.equivFin.symm index).1)) }
  embedding :=
    ⟨fun index => ancestor.geometry.indexEquiv.symm
        ((retained.equivFin.symm index).1), by
      intro first second equality
      apply retained.equivFin.symm.injective
      apply Subtype.ext
      exact ancestor.geometry.indexEquiv.symm.injective equality⟩
  tube_eq _ := rfl

/-- Pull the synchronized overlap back through the unchanged ancestor frame. -/
noncomputable def pureWZ2Node05PostGrainSelectedOrdinaryTrace
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (retained : Finset (Fin coarseRefinement.selected.family.card)) :
    Kakeya.Streamlined.TubeShading
      (pureWZ2Node05PostGrainSelectedOrdinarySubfamily
        coarseRefinement ancestor retained).family where
  carrier index := ancestor.geometry.frame.symm ''
    (selectedTubeShading
      (pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains) retained).carrier index
  measurable_carrier index := by
    let measurableFrame : Point3 ≃ᵐ Point3 :=
      { toFun := ancestor.geometry.frame.symm
        invFun := ancestor.geometry.frame
        left_inv := ancestor.geometry.frame.symm.left_inv
        right_inv := ancestor.geometry.frame.symm.right_inv
        measurable_toFun :=
          ancestor.geometry.frame.symm.continuous_of_finiteDimensional.measurable
        measurable_invFun :=
          ancestor.geometry.frame.continuous_of_finiteDimensional.measurable }
    exact (measurableFrame.measurableSet_image).mpr
      ((selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) retained).measurable_carrier index)
  subset_body index := by
    rintro point ⟨framedPoint, framedPointMem, rfl⟩
    rcases framedPointMem.1 with ⟨ordinaryPoint, ordinaryPointMem, pointEq⟩
    rw [← pointEq, ancestor.geometry.frame.symm_apply_apply]
    exact ancestor.geometry.ordinaryRefined.subset_body
      (ancestor.geometry.indexEquiv.symm
        ((retained.equivFin.symm index).1)) ordinaryPointMem

theorem pureWZ2Node05PostGrainSelectedOrdinaryTrace_frame_image
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (retained : Finset (Fin coarseRefinement.selected.family.card))
    (index : Fin retained.card) :
    ancestor.geometry.frame ''
        (pureWZ2Node05PostGrainSelectedOrdinaryTrace
          coarseRefinement ancestor coarseGrains retained).carrier index =
      (selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) retained).carrier index := by
  ext point
  constructor
  · rintro ⟨sourcePoint, ⟨framedPoint, framedPointMem, sourceEq⟩, rfl⟩
    rwa [← sourceEq, ancestor.geometry.frame.apply_symm_apply]
  · intro pointMem
    exact ⟨ancestor.geometry.frame.symm point,
      ⟨point, pointMem, rfl⟩,
      ancestor.geometry.frame.apply_symm_apply point⟩

theorem pureWZ2Node05PostGrainSelectedOrdinaryTrace_volume_eq
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (retained : Finset (Fin coarseRefinement.selected.family.card))
    (index : Fin retained.card) :
    volume
        ((pureWZ2Node05PostGrainSelectedOrdinaryTrace
          coarseRefinement ancestor coarseGrains retained).carrier index) =
      volume ((selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) retained).carrier index) := by
  rw [← pureWZ2Node05PostGrainSelectedOrdinaryTrace_frame_image
    coarseRefinement ancestor coarseGrains retained index]
  exact (Kakeya.Streamlined.AffineIsometryEquiv.volume_image
    ancestor.geometry.frame _
    ((pureWZ2Node05PostGrainSelectedOrdinaryTrace
      coarseRefinement ancestor coarseGrains retained).measurable_carrier index)).symm

/-- Cropped grain shading and ordinary overlap, restricted on exactly the
same retained cropped indices. -/
structure PureWZ2Node05SynchronizedPostGrainCore
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (outputEta : ℝ) (croppedMassFraction : ENNReal) where
  retained : Finset (Fin coarseRefinement.selected.family.card)
  retained_nonempty : retained.Nonempty
  retentionLoss : ENNReal
  retentionLoss_ne_zero : retentionLoss ≠ 0
  retentionLoss_ne_top : retentionLoss ≠ ⊤
  cardinality_retention :
    Kakeya.realRpowENN delta outputEta *
          coarseRefinement.selected.family.enncard ≤
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family retained).family.enncard
  overlap_mass_retention :
    (pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains).mass ≤
      retentionLoss * (selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) retained).mass
  cropped_mass_retention :
    croppedMassFraction * coarseGrains.shading.mass ≤
      retentionLoss * (restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family retained)
        coarseGrains.shading).mass
  ordinary_overlap_per_tube :
    ∀ index : Fin retained.card,
      Kakeya.realRpowENN delta outputEta *
            ((pureWZ2Node05PostGrainSelectedSubfamily
              coarseRefinement.selected.family retained).family.tube index).volume ≤
        volume ((selectedTubeShading
          (pureWZ2Node05PostGrainOverlapShading
            coarseRefinement ancestor coarseGrains) retained).carrier index)

/-- One bicriteria aggregate overlap premise produces all synchronized
quantitative conclusions.  No aggregate mass estimate is reused as a
per-tube estimate: the latter comes only from indexed per-tube pruning. -/
theorem exists_pureWZ2Node05SynchronizedPostGrainCore_with_loss_two
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (inputEta outputEta : ℝ)
    (croppedMassFraction : ENNReal)
    (densitySeparation :
      Kakeya.realRpowENN delta outputEta ≤
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta inputEta)
    (aggregateOverlap :
      max
          (Kakeya.realRpowENN delta inputEta *
            coarseRefinement.selected.family.toBodyFamily.mass)
          (croppedMassFraction * coarseGrains.shading.mass) ≤
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains).mass) :
    ∃ core : PureWZ2Node05SynchronizedPostGrainCore
        coarseRefinement ancestor coarseGrains outputEta croppedMassFraction,
      core.retentionLoss = 2 := by
  let overlap := pureWZ2Node05PostGrainOverlapShading
    coarseRefinement ancestor coarseGrains
  have overlapDense : overlap.IsLambdaDense
      (Kakeya.realRpowENN delta inputEta) :=
    (le_max_left
      (Kakeya.realRpowENN delta inputEta *
        coarseRefinement.selected.family.toBodyFamily.mass)
      (croppedMassFraction * coarseGrains.shading.mass)).trans aggregateOverlap
  rcases pure_wz2_indexed_per_tube_pruning
      ancestor.cropped_extremal.delta_pos
      ancestor.cropped_extremal.delta_le_one
      ancestor.cropped_extremal.nonempty overlap
      overlapDense densitySeparation with
    ⟨retained, retainedNonempty, cardinalityRetention,
      overlapMassRetention, overlapPerTube⟩
  have selectedOverlapLeCropped :
      (selectedTubeShading overlap retained).mass ≤
        (restrictPaperShading
          (pureWZ2Node05PostGrainSelectedSubfamily
            coarseRefinement.selected.family retained)
          coarseGrains.shading).mass := by
    apply Finset.sum_le_sum
    intro index _
    apply measure_mono
    exact Set.inter_subset_right
  have croppedDemand :
      croppedMassFraction * coarseGrains.shading.mass ≤ overlap.mass :=
    (le_max_right
      (Kakeya.realRpowENN delta inputEta *
        coarseRefinement.selected.family.toBodyFamily.mass)
      (croppedMassFraction * coarseGrains.shading.mass)).trans aggregateOverlap
  refine ⟨{
    retained := retained
    retained_nonempty := retainedNonempty
    retentionLoss := 2
    retentionLoss_ne_zero := by norm_num
    retentionLoss_ne_top := by norm_num
    cardinality_retention := cardinalityRetention
    overlap_mass_retention := overlapMassRetention
    cropped_mass_retention := ?_
    ordinary_overlap_per_tube := ?_ }, rfl⟩
  · calc
      croppedMassFraction * coarseGrains.shading.mass ≤ overlap.mass := croppedDemand
      _ ≤ 2 * (selectedTubeShading overlap retained).mass := overlapMassRetention
      _ ≤ 2 * (restrictPaperShading
          (pureWZ2Node05PostGrainSelectedSubfamily
            coarseRefinement.selected.family retained)
          coarseGrains.shading).mass := by
        gcongr
  · intro index
    exact overlapPerTube
      (retained.equivFin.symm index).1
      (retained.equivFin.symm index).2

/-- Compatibility wrapper for callers which do not need the exact factor-two
identity of the original pruning construction. -/
theorem exists_pureWZ2Node05SynchronizedPostGrainCore
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (inputEta outputEta : ℝ)
    (croppedMassFraction : ENNReal)
    (densitySeparation :
      Kakeya.realRpowENN delta outputEta ≤
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta inputEta)
    (aggregateOverlap :
      max
          (Kakeya.realRpowENN delta inputEta *
            coarseRefinement.selected.family.toBodyFamily.mass)
          (croppedMassFraction * coarseGrains.shading.mass) ≤
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains).mass) :
    Nonempty (PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction) := by
  rcases exists_pureWZ2Node05SynchronizedPostGrainCore_with_loss_two
      coarseRefinement ancestor coarseGrains inputEta outputEta
      croppedMassFraction densitySeparation aggregateOverlap with
    ⟨core, _⟩
  exact ⟨core⟩

namespace PureWZ2Node05SynchronizedPostGrainCore

variable
    {delta sigma sourceLoss normalizationLoss grainLoss outputEta : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    {coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent}
    {ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss}
    {coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss}
    {croppedMassFraction : ENNReal}
    (core : PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction)

/-- The selected ordinary family is genuinely nonempty. -/
theorem ordinary_family_nonempty :
    (pureWZ2Node05PostGrainSelectedOrdinarySubfamily
      coarseRefinement ancestor core.retained).family.Nonempty := by
  exact Finset.card_pos.mpr core.retained_nonempty

/-- The per-tube lower bound in ordinary coordinates, on the very same
indices used for cropped mass and cardinality retention. -/
theorem ordinary_per_tube
    (index : Fin core.retained.card) :
    Kakeya.realRpowENN delta outputEta *
          ((pureWZ2Node05PostGrainSelectedOrdinarySubfamily
            coarseRefinement ancestor core.retained).family.tube index).volume ≤
      volume
        ((pureWZ2Node05PostGrainSelectedOrdinaryTrace
          coarseRefinement ancestor coarseGrains core.retained).carrier index) := by
  rw [pureWZ2Node05PostGrainSelectedOrdinaryTrace_volume_eq
    coarseRefinement ancestor coarseGrains core.retained index]
  have hcarrier := ancestor.geometry.ordinary_carrier_image_eq
    (ancestor.geometry.indexEquiv.symm
      ((core.retained.equivFin.symm index).1))
  rw [ancestor.geometry.indexEquiv.apply_symm_apply] at hcarrier
  have hvolume := Kakeya.Streamlined.AffineIsometryEquiv.volume_image
    ancestor.geometry.frame
    (ancestor.geometry.selected.family.tube
      (ancestor.geometry.indexEquiv.symm
        ((core.retained.equivFin.symm index).1))).carrier
    (wz2_paper_ordinary_tube_carrier_measurable
      (ancestor.geometry.selected.family.tube
        (ancestor.geometry.indexEquiv.symm
          ((core.retained.equivFin.symm index).1)))
      ancestor.cropped_extremal.delta_pos)
  have htubeVolume :
      ((pureWZ2Node05PostGrainSelectedOrdinarySubfamily
        coarseRefinement ancestor core.retained).family.tube index).volume =
      ((pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family.tube index).volume := by
    change volume
        (ancestor.geometry.selected.family.tube
          (ancestor.geometry.indexEquiv.symm
            ((core.retained.equivFin.symm index).1))).carrier =
      volume (coarseRefinement.selected.family.tube
        ((core.retained.equivFin.symm index).1)).carrier
    calc
      volume
          (ancestor.geometry.selected.family.tube
            (ancestor.geometry.indexEquiv.symm
              ((core.retained.equivFin.symm index).1))).carrier =
        volume
          (ancestor.geometry.frame ''
            (ancestor.geometry.selected.family.tube
              (ancestor.geometry.indexEquiv.symm
                ((core.retained.equivFin.symm index).1))).carrier) := hvolume.symm
      _ = volume (coarseRefinement.selected.family.tube
          ((core.retained.equivFin.symm index).1)).carrier := by rw [← hcarrier]
  rw [htubeVolume]
  exact core.ordinary_overlap_per_tube index

/-- Selected ordinary indexed mass equals the synchronized overlap mass. -/
theorem ordinary_mass_eq :
    (pureWZ2Node05PostGrainSelectedOrdinaryTrace
      coarseRefinement ancestor coarseGrains core.retained).mass =
      (selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) core.retained).mass := by
  apply Finset.sum_congr rfl
  intro index _
  exact pureWZ2Node05PostGrainSelectedOrdinaryTrace_volume_eq
    coarseRefinement ancestor coarseGrains core.retained index

/-- Exact dense cubicalization on every retained index.  Positivity is supplied
by the synchronized per-tube estimate, not by aggregate mass. -/
theorem exact_dense_cubicalization
    (index : Fin core.retained.card) :
    (restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained)
        coarseGrains.shading).carrier index =
      pureWZ2DenseCubicalization
        ((pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained).family.tube index)
        (ancestor.geometry.frame ''
          (pureWZ2Node05PostGrainSelectedOrdinaryTrace
            coarseRefinement ancestor coarseGrains core.retained).carrier index) := by
  let ambient := (core.retained.equivFin.symm index).1
  let ordinary := ancestor.geometry.frame ''
    ancestor.geometry.ordinaryRefined.carrier
      (ancestor.geometry.indexEquiv.symm ambient)
  let cropped := coarseGrains.shading.carrier ambient
  let tube := coarseRefinement.selected.family.tube ambient
  have hcropped : cropped ⊆ pureWZ2DenseCubicalization tube ordinary := by
    intro point pointMem
    have ancestorMem := coarseGrains.subshading ambient pointMem
    have hancestor := ancestor.geometry.cropped_carrier_eq_dense_cubicalization
      (ancestor.geometry.indexEquiv.symm ambient)
    rw [ancestor.geometry.indexEquiv.apply_symm_apply] at hancestor
    rw [hancestor] at ancestorMem
    exact ancestorMem
  have hwhole : ∀ point ∈ cropped,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆ cropped :=
    coarseGrains.cubical ambient
  have hdensityPositive : 0 < Kakeya.realRpowENN delta outputEta :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos ancestor.cropped_extremal.delta_pos outputEta)
  have htubePositive : 0 < volume tube.carrier :=
    wz2_paper_ordinary_tube_volume_pos tube
      ancestor.cropped_extremal.delta_pos
  have hoverlapPositive : 0 < volume (ordinary ∩ cropped) := by
    have hproduct : 0 <
        Kakeya.realRpowENN delta outputEta *
          ((pureWZ2Node05PostGrainSelectedSubfamily
            coarseRefinement.selected.family core.retained).family.tube index).volume := by
      exact ENNReal.mul_pos hdensityPositive.ne' htubePositive.ne'
    have hbound := core.ordinary_overlap_per_tube index
    have hselectedPositive : 0 < volume
        ((selectedTubeShading
          (pureWZ2Node05PostGrainOverlapShading
            coarseRefinement ancestor coarseGrains) core.retained).carrier index) :=
      hproduct.trans_le hbound
    exact hselectedPositive
  have hdense := denseCubicalization_inter_whole_cells_selected
    tube ordinary cropped ancestor.cropped_extremal.delta_pos
    hcropped hwhole hoverlapPositive
  have hframe :=
    pureWZ2Node05PostGrainSelectedOrdinaryTrace_frame_image
      coarseRefinement ancestor coarseGrains core.retained index
  have hframe' :
      ancestor.geometry.frame ''
          (pureWZ2Node05PostGrainSelectedOrdinaryTrace
            coarseRefinement ancestor coarseGrains core.retained).carrier index =
        ordinary ∩ cropped := by
    exact hframe
  change cropped = pureWZ2DenseCubicalization tube
    (ancestor.geometry.frame ''
      (pureWZ2Node05PostGrainSelectedOrdinaryTrace
        coarseRefinement ancestor coarseGrains core.retained).carrier index)
  calc
    cropped = pureWZ2DenseCubicalization tube (ordinary ∩ cropped) := hdense.symm
    _ = pureWZ2DenseCubicalization tube
        (ancestor.geometry.frame ''
          (pureWZ2Node05PostGrainSelectedOrdinaryTrace
            coarseRefinement ancestor coarseGrains core.retained).carrier index) := by
      rw [hframe']

end PureWZ2Node05SynchronizedPostGrainCore

/-- Honest non-hereditary receipts needed to promote the synchronized
restriction to a new grain configuration. -/
structure PureWZ2Node05SelectedGrainReceipt
    {delta sigma sourceLoss normalizationLoss grainLoss outputEta : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    {coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent}
    {ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss}
    {coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss}
    {croppedMassFraction : ENNReal}
    (core : PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction)
    (selectedLoss : ℝ) where
  grainLoss_le : grainLoss ≤ selectedLoss
  extremal : WZ2PaperCroppedIsExtremal sigma selectedLoss
    (pureWZ2Node05PostGrainSelectedSubfamily
      coarseRefinement.selected.family core.retained).family
    (restrictPaperShading
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained)
      coarseGrains.shading)
  top_level_cwa : WZ2PaperConvexWolffBound
    (pureWZ2Node05PostGrainSelectedSubfamily
      coarseRefinement.selected.family core.retained).family
    (Kakeya.realRpowENN delta (-selectedLoss))
  volume_lower : Kakeya.realRpowENN delta (sigma + selectedLoss) ≤
    volume (restrictPaperShading
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained)
      coarseGrains.shading).union

namespace PureWZ2Node05SelectedGrainReceipt

variable
    {delta sigma sourceLoss normalizationLoss grainLoss outputEta selectedLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    {coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent}
    {ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss}
    {coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss}
    {croppedMassFraction : ENNReal}
    {core : PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction}

/-- Restrict the full grain package to the synchronized family.  Only the
three non-hereditary scalar/structural facts come from the honest receipt. -/
noncomputable def toGrainConfiguration
    (receipt : PureWZ2Node05SelectedGrainReceipt core selectedLoss) :
    PureWZ2GrainConfiguration sigma selectedLoss delta := by
  let selected := pureWZ2Node05PostGrainSelectedSubfamily
    coarseRefinement.selected.family core.retained
  let shading : WZ1PaperTubeShading selected.family :=
    restrictPaperShading selected coarseGrains.shading
  let sub : ∀ index, shading.carrier index ⊆
      coarseGrains.shading.carrier (selected.embedding index) :=
    fun _ => Set.Subset.rfl
  have hconstant :
      Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-selectedLoss) :=
    pureWZ2_grain_constant_mono ancestor.cropped_extremal.delta_pos
      ancestor.cropped_extremal.delta_le_one receipt.grainLoss_le
  have hconstantTop : Kakeya.realRpowENN delta (-selectedLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let restrictedGlobal := coarseGrains.globalGrains.restrictSubfamilyWithShading
    selected shading sub
  let restrictedLocal := coarseGrains.localGrains.restrictSubfamilyWithShading
    selected shading sub
  let globalGrains := restrictedGlobal.restrict
    (fun _ => Set.Subset.rfl) hconstant hconstantTop
  let localGrains := restrictedLocal.restrictWithConstant
    (fun _ => Set.Subset.rfl) hconstant hconstantTop
  exact
    { family := selected.family
      shading := shading
      line_class := coarseGrains.line_class.subfamily selected
      cubical := restrictPaperShading_cubical selected coarseGrains.cubical
      extremal := receipt.extremal
      top_level_cwa := receipt.top_level_cwa
      globalGrains := globalGrains
      localGrains := localGrains }

/-- Retain the construction-only quantitative facts on the exact selected
configuration.  Restriction and loss weakening preserve the same global
slope, so the slope certificate remains indexed by this output. -/
noncomputable def toQuantitativeGrainConfiguration
    (receipt : PureWZ2Node05SelectedGrainReceipt core selectedLoss)
    (slope_bound : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 →
      |coarseGrains.globalGrains.slope z| ≤ 3) :
    PureWZ2QuantitativeGrainConfiguration sigma selectedLoss delta where
  family := receipt.toGrainConfiguration.family
  shading := receipt.toGrainConfiguration.shading
  line_class := receipt.toGrainConfiguration.line_class
  cubical := receipt.toGrainConfiguration.cubical
  extremal := receipt.toGrainConfiguration.extremal
  top_level_cwa := receipt.toGrainConfiguration.top_level_cwa
  volume_lower := receipt.volume_lower
  globalGrains :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound
      receipt.toGrainConfiguration.globalGrains slope_bound
  localGrains := receipt.toGrainConfiguration.localGrains
  planeMap_vertical_bound := by
    intro point
    exact coarseGrains.planeMap_vertical_bound
      ⟨point, by
        rcases point.property with ⟨index, pointMem⟩
        exact ⟨(pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained).embedding index,
          pointMem⟩⟩

end PureWZ2Node05SelectedGrainReceipt

/-- Additional scalar receipts needed for exact sticky re-entry.  These are
not inferred from aggregate mass or from arbitrary-subfamily inheritance. -/
structure PureWZ2Node05SelectedReentryReceipt
    {delta sigma sourceLoss normalizationLoss grainLoss outputEta : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    {coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent}
    {ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss}
    {coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss}
    {croppedMassFraction : ENNReal}
    (core : PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction)
    (selectedLoss : ℝ) (selectedNormalizationExponent : ℕ)
    extends PureWZ2Node05SelectedGrainReceipt core selectedLoss where
  normalizationLoss_le : normalizationLoss ≤ selectedLoss
  retained_ordinary_mass :
    wz2PaperPureRefinementFraction delta selectedNormalizationExponent *
        ancestor.ordinarySource.shading.mass ≤
      (pureWZ2Node05PostGrainSelectedOrdinaryTrace
        coarseRefinement ancestor coarseGrains core.retained).mass
  density_budget : Kakeya.realRpowENN delta sourceLoss / 2 ≤
    Kakeya.realRpowENN delta outputEta

namespace PureWZ2Node05SelectedReentryReceipt

variable
    {delta sigma sourceLoss normalizationLoss grainLoss outputEta selectedLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent
      selectedNormalizationExponent : ℕ}
    {coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent}
    {ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss}
    {coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss}
    {croppedMassFraction : ENNReal}
    {core : PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction}

/-- Exact re-entry on the selected post-grain shading, retaining the ancestor
ordinary source, frame, and index provenance. -/
noncomputable def toReentryData
    (receipt : PureWZ2Node05SelectedReentryReceipt core selectedLoss
      selectedNormalizationExponent) :
    PureWZ2PropStickyReentryData
      (sigma := sigma)
      (restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained)
        coarseGrains.shading)
      selectedNormalizationExponent sourceLoss selectedLoss := by
  let croppedSelected := pureWZ2Node05PostGrainSelectedSubfamily
    coarseRefinement.selected.family core.retained
  let ordinarySelected := pureWZ2Node05PostGrainSelectedOrdinarySubfamily
    coarseRefinement ancestor core.retained
  let ordinaryTrace := pureWZ2Node05PostGrainSelectedOrdinaryTrace
    coarseRefinement ancestor coarseGrains core.retained
  let ordinaryInSource : Kakeya.Streamlined.TubeSubfamily
      ancestor.ordinarySource.family :=
    ancestor.geometry.selected.comp ordinarySelected
  exact
    { sourceLoss_pos := ancestor.sourceLoss_pos
      normalizationLoss_pos :=
        ancestor.normalizationLoss_pos.trans_le receipt.normalizationLoss_le
      sourceLoss_le_half := by
        calc
          sourceLoss ≤ normalizationLoss / 2 := ancestor.sourceLoss_le_half
          _ ≤ selectedLoss / 2 :=
            div_le_div_of_nonneg_right receipt.normalizationLoss_le (by norm_num)
      ordinarySource := ancestor.ordinarySource
      geometry :=
        { selected := ordinaryInSource
          selected_nonempty := core.ordinary_family_nonempty
          ordinaryRefined := ordinaryTrace
          ordinary_subshading := by
            intro index point pointMem
            rcases pointMem with ⟨framedPoint, framedPointMem, rfl⟩
            rcases framedPointMem.1 with
              ⟨ordinaryPoint, ordinaryPointMem, pointEq⟩
            rw [← pointEq, ancestor.geometry.frame.symm_apply_apply]
            exact ancestor.geometry.ordinary_subshading _ ordinaryPointMem
          retained_mass := receipt.retained_ordinary_mass
          frame := ancestor.geometry.frame
          indexEquiv := Equiv.refl (Fin core.retained.card)
          ordinary_carrier_image_eq := by
            intro index
            have hancestor := ancestor.geometry.ordinary_carrier_image_eq
              (ancestor.geometry.indexEquiv.symm
                ((core.retained.equivFin.symm index).1))
            rw [ancestor.geometry.indexEquiv.apply_symm_apply] at hancestor
            exact hancestor
          ordinaryDensity := Kakeya.realRpowENN delta outputEta
          ordinaryDensity_pos := ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos ancestor.cropped_extremal.delta_pos outputEta)
          ordinary_per_tube := core.ordinary_per_tube
          ordinary_axial_window := by
            intro index point pointMem
            have hframe :=
              pureWZ2Node05PostGrainSelectedOrdinaryTrace_frame_image
                coarseRefinement ancestor coarseGrains core.retained index
            rw [hframe] at pointMem
            exact ancestor.geometry.ordinary_axial_window _ point pointMem.1
          cropped_carrier_eq_dense_cubicalization := by
            intro index
            exact core.exact_dense_cubicalization index
          cropped_cubical := restrictPaperShading_cubical
            croppedSelected coarseGrains.cubical
          line_class := coarseGrains.line_class.subfamily croppedSelected
          ordinary_cell_containment := by
            intro index cell cellHit
            have hhit :
                ((ancestor.geometry.frame ''
                    ancestor.geometry.ordinaryRefined.carrier
                      (ancestor.geometry.indexEquiv.symm
                        ((core.retained.equivFin.symm index).1))) ∩
                  wz1PaperGridCube delta cell).Nonempty :=
              cellHit.mono (Set.inter_subset_inter_left _
                (Set.image_mono (by
                  intro point pointMem
                  rcases pointMem with ⟨framedPoint, framedPointMem, rfl⟩
                  rcases framedPointMem.1 with
                    ⟨ordinaryPoint, ordinaryPointMem, pointEq⟩
                  rw [← pointEq, ancestor.geometry.frame.symm_apply_apply]
                  exact ordinaryPointMem)))
            have hcontain := ancestor.geometry.ordinary_cell_containment
              (ancestor.geometry.indexEquiv.symm
                ((core.retained.equivFin.symm index).1)) cell hhit
            change wz1PaperGridCube delta cell ⊆
              wz1PaperTubeCarrier
                (coarseRefinement.selected.family.tube
                  ((core.retained.equivFin.symm index).1))
            simpa using hcontain
          ordinary_bounded_base := selectedTubeFamily_hasBoundedBase
            coarseRefinement.selected.family core.retained
            ancestor.geometry.ordinary_bounded_base }
      ordinary_density_budget := receipt.density_budget
      cropped_top_level_cwa := receipt.top_level_cwa
      cropped_extremal := receipt.extremal }

end PureWZ2Node05SelectedReentryReceipt

end Kakeya.Assouad

end
