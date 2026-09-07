import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationFinalOrdinaryTrace
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Re-entry after the first Node 5 grain refinement

This file isolates the genuinely new geometric input needed to re-enter the
sticky kernel on the *actual* shading produced by the intervening grain call.
The cropped family is unchanged.  The first coarse refinement remains in the
types, so the construction cannot silently switch to an unrelated extremizer.

All structural fields are inherited from the ancestor re-entry datum or from
the grain refinement.  The general receipt exposes only a new ordinary
subshading, its quantitative retention, and the exact dense-cubicalization
identity.  For the canonical trace, that identity is derived from whole-cell
restriction and positive per-tube mass.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Whole-cell restriction commutes with dense cubicalization when the
restricted source has positive mass. -/
private lemma denseCubicalization_inter_whole_cells
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (ordinary cropped : Set Point3)
    (hdelta : 0 < delta)
    (hcropped : cropped ⊆
      pureWZ2DenseCubicalization tube ordinary)
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
      have hhundred : 0 < (100 : ENNReal)⁻¹ :=
        ENNReal.inv_pos.mpr (by norm_num)
      exact ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos hhundred.ne' hpositive.ne').ne'
          hinvPositive.ne').ne'
        hcubePositive.ne'
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
      simp only [Set.mem_inter_iff]
      constructor
      · intro hother
        exact ⟨hother.1.1, hother.2⟩
      · intro hother
        exact ⟨⟨hother.1, hcellSubset hother.2⟩, hother.2⟩
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

private noncomputable def identitySubfamily
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeSubfamily family where
  family := family
  embedding := Equiv.toEmbedding (Equiv.refl (Fin family.card))
  tube_eq := fun _ => rfl

/-- The identity paper refinement used to retain an exact cropped shading
while applying the canonical post-grain trace construction. -/
noncomputable def pureWZ2Node05PostGrainIdentityRefinement
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    WZ1PaperRefinement shading 0 where
  selected := identitySubfamily family
  refined := shading
  subshading := fun _ => Set.Subset.rfl
  retained_mass := by
    rw [show wz1PaperRefinementFraction delta 0 = 1 by
      simp [wz1PaperRefinementFraction], one_mul]
    exact le_rfl

/-- The canonical cropped trace of the actual post-grain shading. -/
noncomputable def pureWZ2Node05PostGrainCroppedTrace
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
    Kakeya.Streamlined.TubeShading coarseRefinement.selected.family :=
  ancestor.toNormalizationData.finalOrdinaryTrace
    (identitySubfamily coarseRefinement.selected.family)
    coarseGrains.shading

/-- Pull the canonical cropped trace back through the ancestor rigid frame. -/
noncomputable def pureWZ2Node05PostGrainOrdinaryTrace
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
    Kakeya.Streamlined.TubeShading ancestor.geometry.selected.family where
  carrier index :=
    ancestor.geometry.frame.symm ''
      (pureWZ2Node05PostGrainCroppedTrace
        coarseRefinement ancestor coarseGrains).carrier
        (ancestor.geometry.indexEquiv index)
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
      ((pureWZ2Node05PostGrainCroppedTrace
        coarseRefinement ancestor coarseGrains).measurable_carrier _)
  subset_body index := by
    rintro point ⟨framedPoint, framedPointMem, rfl⟩
    have indexEq :
        ancestor.toNormalizationData.ordinaryIndex
            (identitySubfamily coarseRefinement.selected.family)
            (ancestor.geometry.indexEquiv index) = index := by
      change ancestor.geometry.indexEquiv.symm
        ((identitySubfamily coarseRefinement.selected.family).embedding
          (ancestor.geometry.indexEquiv index)) = index
      rw [show
        (identitySubfamily coarseRefinement.selected.family).embedding
            (ancestor.geometry.indexEquiv index) =
          ancestor.geometry.indexEquiv index by rfl]
      exact ancestor.geometry.indexEquiv.symm_apply_apply index
    have ordinaryMemRaw : framedPoint ∈ ancestor.geometry.frame ''
        ancestor.geometry.ordinaryRefined.carrier
          (ancestor.toNormalizationData.ordinaryIndex
            (identitySubfamily coarseRefinement.selected.family)
            (ancestor.geometry.indexEquiv index)) := by
      exact framedPointMem.1
    rw [indexEq] at ordinaryMemRaw
    have ordinaryMem := ordinaryMemRaw
    rcases ordinaryMem with ⟨ordinaryPoint, ordinaryPointMem, pointEq⟩
    rw [← pointEq, ancestor.geometry.frame.symm_apply_apply]
    exact ancestor.geometry.ordinaryRefined.subset_body index ordinaryPointMem

theorem pureWZ2Node05PostGrainOrdinaryTrace_subshading
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
    (index) :
    (pureWZ2Node05PostGrainOrdinaryTrace
      coarseRefinement ancestor coarseGrains).carrier index ⊆
      ancestor.geometry.ordinaryRefined.carrier index := by
  rintro point ⟨framedPoint, framedPointMem, rfl⟩
  have indexEq :
      ancestor.toNormalizationData.ordinaryIndex
          (identitySubfamily coarseRefinement.selected.family)
          (ancestor.geometry.indexEquiv index) = index := by
    change ancestor.geometry.indexEquiv.symm
      ((identitySubfamily coarseRefinement.selected.family).embedding
        (ancestor.geometry.indexEquiv index)) = index
    rw [show
      (identitySubfamily coarseRefinement.selected.family).embedding
          (ancestor.geometry.indexEquiv index) =
        ancestor.geometry.indexEquiv index by rfl]
    exact ancestor.geometry.indexEquiv.symm_apply_apply index
  have ordinaryMemRaw : framedPoint ∈ ancestor.geometry.frame ''
      ancestor.geometry.ordinaryRefined.carrier
        (ancestor.toNormalizationData.ordinaryIndex
          (identitySubfamily coarseRefinement.selected.family)
          (ancestor.geometry.indexEquiv index)) := by
    exact framedPointMem.1
  rw [indexEq] at ordinaryMemRaw
  have ordinaryMem := ordinaryMemRaw
  rcases ordinaryMem with ⟨ordinaryPoint, ordinaryPointMem, pointEq⟩
  rwa [← pointEq, ancestor.geometry.frame.symm_apply_apply]

/-- Pullback through the rigid frame and reindexing by the stored equivalence
preserve the total indexed mass of the canonical trace. -/
theorem pureWZ2Node05PostGrainOrdinaryTrace_mass_eq
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
    (pureWZ2Node05PostGrainOrdinaryTrace
      coarseRefinement ancestor coarseGrains).mass =
      (pureWZ2Node05PostGrainCroppedTrace
        coarseRefinement ancestor coarseGrains).mass := by
  let croppedTrace := pureWZ2Node05PostGrainCroppedTrace
    coarseRefinement ancestor coarseGrains
  calc
    (pureWZ2Node05PostGrainOrdinaryTrace
        coarseRefinement ancestor coarseGrains).mass =
        ∑ index : Fin ancestor.geometry.selected.family.card,
          volume (croppedTrace.carrier
            (ancestor.geometry.indexEquiv index)) := by
      apply Finset.sum_congr rfl
      intro index _
      exact Kakeya.Streamlined.AffineIsometryEquiv.volume_image
        ancestor.geometry.frame.symm
        (croppedTrace.carrier (ancestor.geometry.indexEquiv index))
        (croppedTrace.measurable_carrier
          (ancestor.geometry.indexEquiv index))
    _ = ∑ index : Fin coarseRefinement.selected.family.card,
          volume (croppedTrace.carrier index) := by
      exact Equiv.sum_comp ancestor.geometry.indexEquiv
        (fun index => volume (croppedTrace.carrier index))
    _ = croppedTrace.mass := rfl

/--
Minimal receipt when the ordinary shading is chosen canonically from
`finalOrdinaryTrace`.  The trace definition supplies the subshading and hence
all inherited geometric fields; only quantitative retention/density, the loss
comparison remain as premises.

The density below is deliberately fresh.  A grain subshading need not retain
the ancestor's per-tube density constant.  Its strict positivity and per-tube
lower bound make each canonical trace fiber positive; together with cubicality
and containment in the ancestor dense cubicalization, this recovers the exact
dense-cubicalization identity by whole-cell restriction.
-/
structure PureWZ2Node05CanonicalPostGrainReceipt
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
        coarseRefinement.refined sigma grainLoss) where
  normalizationLoss_le : normalizationLoss ≤ grainLoss
  retained_mass :
    wz2PaperPureRefinementFraction delta normalizationExponent *
        ancestor.ordinarySource.shading.mass ≤
      (pureWZ2Node05PostGrainOrdinaryTrace
        coarseRefinement ancestor coarseGrains).mass
  ordinaryDensity : ENNReal
  ordinaryDensity_pos : 0 < ordinaryDensity
  ordinary_density_budget :
    Kakeya.realRpowENN delta sourceLoss / 2 ≤ ordinaryDensity
  ordinary_per_tube :
    ∀ index,
      ordinaryDensity *
            volume
              (ancestor.geometry.selected.family.tube index).carrier ≤
        volume
          ((pureWZ2Node05PostGrainOrdinaryTrace
            coarseRefinement ancestor coarseGrains).carrier index)

/-- Minimal quantitative input for the canonical identity-family re-entry.

The aggregate trace estimate supplies the final retention inequality from one
scalar absorption.  The ordinary density is fixed at the normalization floor;
only its genuinely new per-tube survival through the grain restriction remains
an input. -/
structure PureWZ2Node05CanonicalPostGrainProducerInput
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
        coarseRefinement.refined sigma grainLoss) where
  normalizationLoss_le : normalizationLoss ≤ grainLoss
  retained_scalar :
    wz2PaperPureRefinementFraction delta normalizationExponent *
        ancestor.ordinarySource.shading.mass ≤
      (100 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta sourceLoss / 2) *
        coarseGrains.shading.mass
  post_grain_per_tube :
    ∀ index,
      (Kakeya.realRpowENN delta sourceLoss / 2) *
            volume
              (ancestor.geometry.selected.family.tube index).carrier ≤
        volume
          ((pureWZ2Node05PostGrainOrdinaryTrace
            coarseRefinement ancestor coarseGrains).carrier index)

namespace PureWZ2Node05CanonicalPostGrainProducerInput

variable
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
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

/-- Package the three irreducible quantitative inputs into the canonical
post-grain receipt. -/
noncomputable def toCanonicalReceipt
    (input : PureWZ2Node05CanonicalPostGrainProducerInput
      coarseRefinement ancestor coarseGrains) :
    PureWZ2Node05CanonicalPostGrainReceipt
      coarseRefinement ancestor coarseGrains where
  normalizationLoss_le := input.normalizationLoss_le
  retained_mass := by
    calc
      wz2PaperPureRefinementFraction delta normalizationExponent *
            ancestor.ordinarySource.shading.mass ≤
          (100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta sourceLoss / 2) *
            coarseGrains.shading.mass := input.retained_scalar
      _ ≤ (pureWZ2Node05PostGrainCroppedTrace
            coarseRefinement ancestor coarseGrains).mass :=
        ancestor.toNormalizationData.finalOrdinaryTrace_mass_lower_normalized
          (identitySubfamily coarseRefinement.selected.family)
          coarseGrains.shading ancestor.cropped_extremal.delta_pos
          coarseGrains.cubical coarseGrains.subshading
      _ = (pureWZ2Node05PostGrainOrdinaryTrace
            coarseRefinement ancestor coarseGrains).mass :=
        (pureWZ2Node05PostGrainOrdinaryTrace_mass_eq
          coarseRefinement ancestor coarseGrains).symm
  ordinaryDensity := Kakeya.realRpowENN delta sourceLoss / 2
  ordinaryDensity_pos := by
    apply ENNReal.div_pos
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos ancestor.cropped_extremal.delta_pos sourceLoss)).ne'
    · norm_num
  ordinary_density_budget := le_rfl
  ordinary_per_tube := input.post_grain_per_tube

end PureWZ2Node05CanonicalPostGrainProducerInput

/--
The missing ordinary-coordinate receipt for the post-grain shading.

The ancestor already supplies the ordinary family, rigid frame, index
equivalence, axial window, cell containment, bounded base, and density
budget.  Consequently none of those facts is repeated here.
-/
structure PureWZ2Node05PostGrainOrdinaryReceipt
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
        coarseRefinement.refined sigma grainLoss) where
  normalizationLoss_le : normalizationLoss ≤ grainLoss
  ordinaryRefined :
    Kakeya.Streamlined.TubeShading
      ancestor.geometry.selected.family
  ordinary_subshading :
    ∀ index,
      ordinaryRefined.carrier index ⊆
        ancestor.geometry.ordinaryRefined.carrier index
  retained_mass :
    wz2PaperPureRefinementFraction delta normalizationExponent *
        ancestor.ordinarySource.shading.mass ≤
      ordinaryRefined.mass
  ordinaryDensity : ENNReal
  ordinaryDensity_pos : 0 < ordinaryDensity
  ordinary_density_budget :
    Kakeya.realRpowENN delta sourceLoss / 2 ≤ ordinaryDensity
  ordinary_per_tube :
    ∀ index,
      ordinaryDensity *
            volume
              (ancestor.geometry.selected.family.tube index).carrier ≤
        volume (ordinaryRefined.carrier index)
  cropped_carrier_eq_dense_cubicalization :
    ∀ index,
      coarseGrains.shading.carrier
          (ancestor.geometry.indexEquiv index) =
        pureWZ2DenseCubicalization
          (coarseRefinement.selected.family.tube
            (ancestor.geometry.indexEquiv index))
          (ancestor.geometry.frame '' ordinaryRefined.carrier index)

namespace PureWZ2Node05CanonicalPostGrainReceipt

variable
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
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

private theorem frame_image_ordinaryTrace
    (_receipt : PureWZ2Node05CanonicalPostGrainReceipt
      coarseRefinement ancestor coarseGrains)
    (index) :
    ancestor.geometry.frame ''
        (pureWZ2Node05PostGrainOrdinaryTrace
          coarseRefinement ancestor coarseGrains).carrier index =
      (pureWZ2Node05PostGrainCroppedTrace
        coarseRefinement ancestor coarseGrains).carrier
          (ancestor.geometry.indexEquiv index) := by
  ext point
  simp only [pureWZ2Node05PostGrainOrdinaryTrace, Set.mem_image]
  constructor
  · rintro ⟨sourcePoint, ⟨framedPoint, framedMem, sourceEq⟩, rfl⟩
    rwa [← sourceEq, ancestor.geometry.frame.apply_symm_apply]
  · intro pointMem
    exact ⟨ancestor.geometry.frame.symm point,
      ⟨point, pointMem, rfl⟩,
      ancestor.geometry.frame.apply_symm_apply point⟩

private theorem exact_dense_cubicalization
    (receipt : PureWZ2Node05CanonicalPostGrainReceipt
      coarseRefinement ancestor coarseGrains)
    (index) :
    coarseGrains.shading.carrier
        (ancestor.geometry.indexEquiv index) =
      pureWZ2DenseCubicalization
        (coarseRefinement.selected.family.tube
          (ancestor.geometry.indexEquiv index))
        (ancestor.geometry.frame ''
          (pureWZ2Node05PostGrainOrdinaryTrace
            coarseRefinement ancestor coarseGrains).carrier index) := by
  let tube := coarseRefinement.selected.family.tube
    (ancestor.geometry.indexEquiv index)
  let ordinary := ancestor.geometry.frame ''
    ancestor.geometry.ordinaryRefined.carrier index
  let cropped := coarseGrains.shading.carrier
    (ancestor.geometry.indexEquiv index)
  have hcropped : cropped ⊆ pureWZ2DenseCubicalization tube ordinary := by
    intro point pointMem
    have pointAncestor := coarseGrains.subshading
      (ancestor.geometry.indexEquiv index) pointMem
    rw [ancestor.geometry.cropped_carrier_eq_dense_cubicalization index]
      at pointAncestor
    simpa [tube, ordinary] using pointAncestor
  have hwhole : ∀ point ∈ cropped,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆ cropped :=
    coarseGrains.cubical (ancestor.geometry.indexEquiv index)
  have htracePositive : 0 < volume
      ((pureWZ2Node05PostGrainOrdinaryTrace
        coarseRefinement ancestor coarseGrains).carrier index) := by
    have htubePositive : 0 < volume
        (ancestor.geometry.selected.family.tube index).carrier :=
      wz2_paper_ordinary_tube_volume_pos _
        ancestor.cropped_extremal.delta_pos
    have hproduct : 0 < receipt.ordinaryDensity *
        volume (ancestor.geometry.selected.family.tube index).carrier :=
      ENNReal.mul_pos receipt.ordinaryDensity_pos.ne' htubePositive.ne'
    exact hproduct.trans_le (receipt.ordinary_per_tube index)
  have hintersectionPositive : 0 < volume (ordinary ∩ cropped) := by
    have htraceCarrier :
        ancestor.geometry.frame ''
            (pureWZ2Node05PostGrainOrdinaryTrace
              coarseRefinement ancestor coarseGrains).carrier index =
          ordinary ∩ cropped := by
      calc
        ancestor.geometry.frame ''
              (pureWZ2Node05PostGrainOrdinaryTrace
                coarseRefinement ancestor coarseGrains).carrier index =
            (pureWZ2Node05PostGrainCroppedTrace
              coarseRefinement ancestor coarseGrains).carrier
                (ancestor.geometry.indexEquiv index) :=
          frame_image_ordinaryTrace receipt index
        _ = ordinary ∩ cropped := by
          simp [pureWZ2Node05PostGrainCroppedTrace,
            PureWZ2CroppedCriticalNormalizationData.finalOrdinaryTrace_carrier,
            PureWZ2CroppedCriticalNormalizationData.ordinaryIndex,
            PureWZ2PropStickyReentryData.toNormalizationData,
            identitySubfamily, ordinary, cropped]
    rw [← htraceCarrier]
    rw [Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      ancestor.geometry.frame
      ((pureWZ2Node05PostGrainOrdinaryTrace
        coarseRefinement ancestor coarseGrains).carrier index)
      ((pureWZ2Node05PostGrainOrdinaryTrace
        coarseRefinement ancestor coarseGrains).measurable_carrier index)]
    exact htracePositive
  have hdense := denseCubicalization_inter_whole_cells
    tube ordinary cropped ancestor.cropped_extremal.delta_pos
    hcropped hwhole hintersectionPositive
  calc
    coarseGrains.shading.carrier (ancestor.geometry.indexEquiv index) =
        pureWZ2DenseCubicalization tube (ordinary ∩ cropped) := hdense.symm
    _ = pureWZ2DenseCubicalization
        (coarseRefinement.selected.family.tube
          (ancestor.geometry.indexEquiv index))
        (ancestor.geometry.frame ''
          (pureWZ2Node05PostGrainOrdinaryTrace
            coarseRefinement ancestor coarseGrains).carrier index) := by
      change pureWZ2DenseCubicalization tube (ordinary ∩ cropped) =
        pureWZ2DenseCubicalization tube
          (ancestor.geometry.frame ''
            (pureWZ2Node05PostGrainOrdinaryTrace
              coarseRefinement ancestor coarseGrains).carrier index)
      rw [frame_image_ordinaryTrace receipt index]
      simp [pureWZ2Node05PostGrainCroppedTrace,
        PureWZ2CroppedCriticalNormalizationData.finalOrdinaryTrace_carrier,
        PureWZ2CroppedCriticalNormalizationData.ordinaryIndex,
        PureWZ2PropStickyReentryData.toNormalizationData,
        identitySubfamily, ordinary, cropped]

/-- Forget the canonical choice while preserving precisely the required facts. -/
noncomputable def toOrdinaryReceipt
    (receipt : PureWZ2Node05CanonicalPostGrainReceipt
      coarseRefinement ancestor coarseGrains) :
    PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains where
  normalizationLoss_le := receipt.normalizationLoss_le
  ordinaryRefined := pureWZ2Node05PostGrainOrdinaryTrace
    coarseRefinement ancestor coarseGrains
  ordinary_subshading :=
    pureWZ2Node05PostGrainOrdinaryTrace_subshading
      coarseRefinement ancestor coarseGrains
  retained_mass := receipt.retained_mass
  ordinaryDensity := receipt.ordinaryDensity
  ordinaryDensity_pos := receipt.ordinaryDensity_pos
  ordinary_density_budget := receipt.ordinary_density_budget
  ordinary_per_tube := receipt.ordinary_per_tube
  cropped_carrier_eq_dense_cubicalization :=
    receipt.exact_dense_cubicalization

end PureWZ2Node05CanonicalPostGrainReceipt

namespace PureWZ2Node05PostGrainOrdinaryReceipt

variable
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
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

/-- The new ordinary shading still lies in the ancestor source shading. -/
theorem ordinary_source_subshading
    (receipt : PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains)
    (index) :
    receipt.ordinaryRefined.carrier index ⊆
      ancestor.ordinarySource.shading.carrier
        (ancestor.geometry.selected.embedding index) :=
  (receipt.ordinary_subshading index).trans
    (ancestor.geometry.ordinary_subshading index)

/-- The ancestor axial window is inherited by the smaller ordinary shading. -/
theorem ordinary_axial_window
    (receipt : PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains)
    (index point)
    (pointMem :
      point ∈ ancestor.geometry.frame ''
        receipt.ordinaryRefined.carrier index) :
    |point (2 : Fin 3)| ≤ 1 / 4 := by
  exact ancestor.geometry.ordinary_axial_window index
    point
    (Set.image_mono (receipt.ordinary_subshading index) pointMem)

/-- Source-intersecting cells inherit the ancestor's exact carrier inclusion. -/
theorem ordinary_cell_containment
    (receipt : PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains)
    (index) (cell : ℤ × ℤ × ℤ)
    (cellHit :
      ((ancestor.geometry.frame '' receipt.ordinaryRefined.carrier index) ∩
        wz1PaperGridCube delta cell).Nonempty) :
    wz1PaperGridCube delta cell ⊆
      wz1PaperTubeCarrier
        (coarseRefinement.selected.family.tube
          (ancestor.geometry.indexEquiv index)) := by
  apply ancestor.geometry.ordinary_cell_containment index cell
  exact cellHit.mono (Set.inter_subset_inter_left _
    (Set.image_mono (receipt.ordinary_subshading index)))

/--
Produce exact re-entry data for the actual post-grain shading.

The selected ordinary family, rigid frame, index equivalence, density, CWA
coordinate system, and bounded-base certificate are not reselected.  The
target CWA and extremality are the ones already proved by `coarseGrains`.
-/
noncomputable def toReentryData
    (receipt : PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) coarseGrains.shading normalizationExponent
      sourceLoss grainLoss where
  sourceLoss_pos := ancestor.sourceLoss_pos
  normalizationLoss_pos :=
    ancestor.normalizationLoss_pos.trans_le receipt.normalizationLoss_le
  sourceLoss_le_half := by
    calc
      sourceLoss ≤ normalizationLoss / 2 := ancestor.sourceLoss_le_half
      _ ≤ grainLoss / 2 := by
        exact div_le_div_of_nonneg_right receipt.normalizationLoss_le (by norm_num)
  ordinarySource := ancestor.ordinarySource
  geometry :=
    { selected := ancestor.geometry.selected
      selected_nonempty := ancestor.geometry.selected_nonempty
      ordinaryRefined := receipt.ordinaryRefined
      ordinary_subshading := receipt.ordinary_source_subshading
      retained_mass := receipt.retained_mass
      frame := ancestor.geometry.frame
      indexEquiv := ancestor.geometry.indexEquiv
      ordinary_carrier_image_eq :=
        ancestor.geometry.ordinary_carrier_image_eq
      ordinaryDensity := receipt.ordinaryDensity
      ordinaryDensity_pos := receipt.ordinaryDensity_pos
      ordinary_per_tube := receipt.ordinary_per_tube
      ordinary_axial_window := receipt.ordinary_axial_window
      cropped_carrier_eq_dense_cubicalization :=
        receipt.cropped_carrier_eq_dense_cubicalization
      cropped_cubical := coarseGrains.cubical
      line_class := coarseGrains.line_class
      ordinary_cell_containment := receipt.ordinary_cell_containment
      ordinary_bounded_base := ancestor.geometry.ordinary_bounded_base }
  ordinary_density_budget := receipt.ordinary_density_budget
  cropped_top_level_cwa := coarseGrains.top_level_cwa
  cropped_extremal := coarseGrains.extremal

@[simp] theorem toReentryData_ordinarySource
    (receipt : PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains) :
    receipt.toReentryData.ordinarySource = ancestor.ordinarySource := rfl

@[simp] theorem toReentryData_selected
    (receipt : PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains) :
    receipt.toReentryData.geometry.selected =
      ancestor.geometry.selected := rfl

@[simp] theorem toReentryData_frame
    (receipt : PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains) :
    receipt.toReentryData.geometry.frame = ancestor.geometry.frame := rfl

@[simp] theorem toReentryData_indexEquiv
    (receipt : PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains) :
    receipt.toReentryData.geometry.indexEquiv =
      ancestor.geometry.indexEquiv := rfl

@[simp] theorem toReentryData_croppedShading
    (receipt : PureWZ2Node05PostGrainOrdinaryReceipt
      coarseRefinement ancestor coarseGrains) :
    receipt.toReentryData.geometry.cropped_cubical =
      coarseGrains.cubical := rfl

end PureWZ2Node05PostGrainOrdinaryReceipt

namespace PureWZ2Node05CanonicalPostGrainReceipt

variable
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
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

/-- Canonical identity-family re-entry for the actual grain shading. -/
noncomputable def toReentryData
    (receipt : PureWZ2Node05CanonicalPostGrainReceipt
      coarseRefinement ancestor coarseGrains) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) coarseGrains.shading normalizationExponent
      sourceLoss grainLoss :=
  receipt.toOrdinaryReceipt.toReentryData

@[simp] theorem toReentryData_ordinarySource
    (receipt : PureWZ2Node05CanonicalPostGrainReceipt
      coarseRefinement ancestor coarseGrains) :
    receipt.toReentryData.ordinarySource = ancestor.ordinarySource := rfl

@[simp] theorem toReentryData_croppedRefined
    (receipt : PureWZ2Node05CanonicalPostGrainReceipt
      coarseRefinement ancestor coarseGrains) :
    receipt.toReentryData.toNormalizationData.croppedRefined =
      coarseGrains.shading := rfl

@[simp] theorem toReentryData_ordinaryRefined
    (receipt : PureWZ2Node05CanonicalPostGrainReceipt
      coarseRefinement ancestor coarseGrains) :
    receipt.toReentryData.geometry.ordinaryRefined =
      pureWZ2Node05PostGrainOrdinaryTrace
        coarseRefinement ancestor coarseGrains := rfl

@[simp] theorem toReentryData_ordinaryDensity
    (receipt : PureWZ2Node05CanonicalPostGrainReceipt
      coarseRefinement ancestor coarseGrains) :
    receipt.toReentryData.geometry.ordinaryDensity =
      receipt.ordinaryDensity := rfl

end PureWZ2Node05CanonicalPostGrainReceipt

end Kakeya.Assouad

end
