import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64Normalization

/-!
# Preparing the Proposition 6.4 short-slab image

This module composes the paper steps which precede Lemma 3.5: choose the
mass-heavy slab, choose an occupied anchor height `z_*`, restrict the raw
Proposition 5.7 slope certificate to that slab, and apply the exact affine
normalization from `wz2_64.tex`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- All data immediately before the final Lemma 3.5 rediscretization. -/
structure PureWZ2Proposition64PreparedData
    {sigma inputLoss delta finalLoss hierarchyLoss rawLoss
      extensionConstant : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss)
    (raw : PureWZ2RawC2GlobalGrainData hierarchy.shading sigma
      (Kakeya.realRpowENN delta (-finalLoss)) rawLoss extensionConstant) where
  slab : PureWZ2Proposition64ShortSlab hierarchy
  restrictedRaw : PureWZ2RawC2GlobalGrainData slab.shading sigma
    (Kakeya.realRpowENN delta (-finalLoss)) rawLoss extensionConstant
  restrictedRaw_slope : restrictedRaw.slope = raw.slope
  normalization : ℝ
  normalization_one : 1 ≤ normalization
  normalized : PureWZ2Proposition64NormalizedData restrictedRaw
    slab.center slab.anchorHeight slab.halfHeight normalization

/-- The active point chosen by the mass pigeonhole makes the anchor height a
genuine member of the source height set `D` in `wz2_64.tex`. -/
theorem PureWZ2Proposition64ShortSlab.anchor_active
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss}
    (slab : PureWZ2Proposition64ShortSlab hierarchy) :
    horizontalSlice slab.shading.union slab.anchorHeight ≠ ∅ := by
  apply Set.nonempty_iff_ne_empty.mp
  exact ⟨slab.anchorPoint, slab.anchorPoint_mem, slab.anchorHeight_eq.symm⟩

/-- Execute the pre-rediscretization part of Proposition 6.4 once the fixed
normalization constant has been chosen. -/
theorem PureWZ2LocallyLinearHierarchyData.prepareProposition64
    {sigma inputLoss delta finalLoss hierarchyLoss rawLoss
      extensionConstant : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss)
    (raw : PureWZ2RawC2GlobalGrainData hierarchy.shading sigma
      (Kakeya.realRpowENN delta (-finalLoss)) rawLoss extensionConstant)
    (normalization : ℝ) (hnormalizationOne : 1 ≤ normalization)
    (hnormalization : ∀ slab : PureWZ2Proposition64ShortSlab hierarchy,
      2 * slab.halfHeight * extensionConstant *
        Real.rpow delta (-rawLoss) ≤ normalization) :
    Nonempty {prepared : PureWZ2Proposition64PreparedData hierarchy raw //
      prepared.normalization = normalization} := by
  rcases hierarchy.selectProposition64ShortSlab with ⟨slab⟩
  let restrictedRaw := raw.restrict slab.subshading
  have hrawSlope : restrictedRaw.slope = raw.slope := rfl
  have hanchorActive' :
      horizontalSlice slab.shading.union slab.anchorHeight ≠ ∅ :=
    slab.anchor_active
  have hnormalizationPos : 0 < normalization := lt_of_lt_of_le zero_lt_one hnormalizationOne
  rcases restrictedRaw.proposition64Normalize
      slab.center slab.anchorHeight slab.halfHeight normalization
      hierarchy.delta_pos slab.halfHeight_pos slab.halfHeight_le_one
      slab.anchorHeight_mem hanchorActive' (hnormalization slab)
      slab.source_window with ⟨normalized⟩
  exact ⟨⟨{
    slab := slab
    restrictedRaw := restrictedRaw
    restrictedRaw_slope := hrawSlope
    normalization := normalization
    normalization_one := hnormalizationOne
    normalized := normalized }, rfl⟩⟩

end Kakeya.Assouad

end
