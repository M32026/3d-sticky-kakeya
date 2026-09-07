import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedPostGrainExtremality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationRigidCWATransport
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Refreshing the ordinary source after synchronized post-grain pruning

The retained ordinary mass in a re-entry certificate is measured relative to
that certificate's ordinary source.  Iterating the synchronized pruning while
keeping the original ordinary source would therefore multiply the raw density
loss at every hierarchy level.

This module implements the paper-facing reset.  After one synchronized step,
the inverse rigid image of the selected overlap becomes the next ordinary
source.  Its refinement is the identity refinement, so the next normalization
does not retain another power-sized fraction of the initial ordinary mass.
The selected-family nearby-CWA certificate remains an explicit input.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Below the standard synchronized-pruning cutoff, every fixed
polylogarithmic refinement fraction is at most one. -/
theorem wz2PaperPureRefinementFraction_le_one_of_le_one_twelfth
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 12)
    (exponent : ℕ) :
    wz2PaperPureRefinementFraction delta exponent ≤ 1 := by
  have hThree : (3 : ℝ) ≤ 1 / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hLogOne : 1 ≤ Real.log (1 / delta) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have hExp : Real.exp 1 < 3 := Real.exp_one_lt_three
    exact hExp.le.trans hThree
  unfold wz2PaperPureRefinementFraction
  apply pow_le_one₀
  · positivity
  · exact ENNReal.inv_le_one.mpr (ENNReal.one_le_ofReal.mpr hLogOne)

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

/-- The selected cropped family pulled back through the current rigid frame. -/
noncomputable def refreshedOrdinaryFamily :
    Kakeya.Streamlined.TubeFamily delta :=
  pureWZ2RigidImageFamily ancestor.geometry.frame.symm
    (pureWZ2Node05PostGrainSelectedSubfamily
      coarseRefinement.selected.family core.retained).family

/-- The selected overlap pulled back through the same rigid frame. -/
noncomputable def refreshedOrdinaryShading :
    Kakeya.Streamlined.TubeShading core.refreshedOrdinaryFamily where
  carrier index := ancestor.geometry.frame.symm ''
    (selectedTubeShading
      (pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains) core.retained).carrier index
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
          coarseRefinement ancestor coarseGrains) core.retained).measurable_carrier index)
  subset_body index := by
    rintro point ⟨targetPoint, targetPointMem, rfl⟩
    change ancestor.geometry.frame.symm targetPoint ∈
      (core.refreshedOrdinaryFamily.tube index).carrier
    change ancestor.geometry.frame.symm targetPoint ∈
      ((pureWZ2RigidImageFamily ancestor.geometry.frame.symm
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained).family).tube index).carrier
    rw [pureWZ2RigidImageFamily_carrier]
    exact ⟨targetPoint,
      (selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) core.retained).subset_body
            index targetPointMem,
      rfl⟩

theorem refreshedOrdinaryShading_frame_image
    (index : Fin core.refreshedOrdinaryFamily.card) :
    ancestor.geometry.frame ''
        core.refreshedOrdinaryShading.carrier index =
      (selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) core.retained).carrier index := by
  ext point
  simp [refreshedOrdinaryShading]

theorem refreshedOrdinaryFamily_frame_image
    (index : Fin core.refreshedOrdinaryFamily.card) :
    ancestor.geometry.frame ''
        (core.refreshedOrdinaryFamily.tube index).carrier =
      ((pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family.tube index).carrier := by
  change ancestor.geometry.frame ''
      ((pureWZ2RigidImageFamily ancestor.geometry.frame.symm
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained).family).tube index).carrier = _
  rw [pureWZ2RigidImageFamily_carrier]
  ext point
  simp [refreshedOrdinaryFamily]

theorem refreshedOrdinaryShading_volume_eq
    (index : Fin core.refreshedOrdinaryFamily.card) :
    volume (core.refreshedOrdinaryShading.carrier index) =
      volume ((selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) core.retained).carrier index) := by
  exact Kakeya.Streamlined.AffineIsometryEquiv.volume_image
    ancestor.geometry.frame.symm _
    ((selectedTubeShading
      (pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains) core.retained).measurable_carrier index)

theorem refreshedOrdinaryFamily_volume_eq
    (index : Fin core.refreshedOrdinaryFamily.card) :
    (core.refreshedOrdinaryFamily.tube index).volume =
      ((pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family.tube index).volume := by
  change volume
      ((pureWZ2RigidImageFamily ancestor.geometry.frame.symm
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained).family).tube index).carrier = _
  rw [pureWZ2RigidImageFamily_carrier]
  exact Kakeya.Streamlined.AffineIsometryEquiv.volume_image
    ancestor.geometry.frame.symm _
    (wz2_paper_ordinary_tube_carrier_measurable
      ((pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family.tube index)
      ancestor.cropped_extremal.delta_pos)

theorem refreshedOrdinary_per_tube
    {nextSourceLoss : ℝ}
    (densityPower :
      Kakeya.realRpowENN delta nextSourceLoss ≤
        Kakeya.realRpowENN delta outputEta)
    (index : Fin core.refreshedOrdinaryFamily.card) :
    Kakeya.realRpowENN delta nextSourceLoss *
          (core.refreshedOrdinaryFamily.tube index).volume ≤
      volume (core.refreshedOrdinaryShading.carrier index) := by
  rw [core.refreshedOrdinaryFamily_volume_eq index,
    core.refreshedOrdinaryShading_volume_eq index]
  exact (mul_le_mul_right' densityPower _).trans
    (core.ordinary_overlap_per_tube index)

theorem refreshedOrdinaryShading_dense
    {nextSourceLoss : ℝ}
    (densityPower :
      Kakeya.realRpowENN delta nextSourceLoss ≤
        Kakeya.realRpowENN delta outputEta) :
    core.refreshedOrdinaryShading.IsLambdaDense
      (Kakeya.realRpowENN delta nextSourceLoss) := by
  change
    Kakeya.realRpowENN delta nextSourceLoss *
        (∑ index : Fin core.refreshedOrdinaryFamily.card,
          (core.refreshedOrdinaryFamily.tube index).volume) ≤
      ∑ index : Fin core.refreshedOrdinaryFamily.card,
        volume (core.refreshedOrdinaryShading.carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  exact core.refreshedOrdinary_per_tube densityPower index

theorem refreshedOrdinaryShading_union_image :
    ancestor.geometry.frame '' core.refreshedOrdinaryShading.union =
      (selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) core.retained).union := by
  ext point
  constructor
  · rintro ⟨sourcePoint, ⟨index, sourcePointMem⟩, rfl⟩
    exact ⟨index, by
      rw [← core.refreshedOrdinaryShading_frame_image index]
      exact ⟨sourcePoint, sourcePointMem, rfl⟩⟩
  · rintro ⟨index, pointMem⟩
    rw [← core.refreshedOrdinaryShading_frame_image index] at pointMem
    rcases pointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
    exact ⟨sourcePoint, ⟨index, sourcePointMem⟩, rfl⟩

theorem refreshedOrdinaryShading_volume_upper
    {nextSourceLoss : ℝ}
    (grainLoss_le : grainLoss ≤ nextSourceLoss) :
    volume core.refreshedOrdinaryShading.union ≤
      Kakeya.realRpowENN delta (sigma - nextSourceLoss) := by
  have imageVolume :
      volume (ancestor.geometry.frame ''
        core.refreshedOrdinaryShading.union) =
        volume core.refreshedOrdinaryShading.union :=
    Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      ancestor.geometry.frame _
      (measurableSet_shading_union core.refreshedOrdinaryShading)
  rw [core.refreshedOrdinaryShading_union_image] at imageVolume
  rw [← imageVolume]
  calc
    volume ((selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) core.retained).union) ≤
        volume coarseGrains.shading.union := by
      apply measure_mono
      rintro point ⟨index, pointMem⟩
      exact ⟨
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained).embedding index,
        pointMem.2⟩
    _ ≤ Kakeya.realRpowENN delta (sigma - grainLoss) :=
      coarseGrains.extremal.volume_upper
    _ ≤ Kakeya.realRpowENN delta (sigma - nextSourceLoss) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge
        ancestor.cropped_extremal.delta_pos
        ancestor.cropped_extremal.delta_le_one (by linarith)

/-- Apply the ordinary critical floor directly to the refreshed ordinary
source, then push its union back into the literal selected cropped shading. -/
theorem selectedCropped_volume_lower_of_refreshedOrdinary
    {selectedLoss densityLoss structuralBudget : ℝ}
    (criticalFloor : PureWZ2CriticalFloorSelectionData
      sigma selectedLoss structuralBudget)
    (hdeltaCutoff : delta ≤ criticalFloor.delta₀)
    (densityLoss_le_structural :
      densityLoss ≤ criticalFloor.structuralLoss)
    (outputEta_le_structural :
      outputEta ≤ criticalFloor.structuralLoss)
    (nearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-densityLoss))) :
    Kakeya.realRpowENN delta (sigma + selectedLoss) ≤
      volume (restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained)
        coarseGrains.shading).union := by
  let selected := pureWZ2Node05PostGrainSelectedSubfamily
    coarseRefinement.selected.family core.retained
  have ordinaryNearby : WZ2PaperPureCWAAtNearbyScales
      core.refreshedOrdinaryFamily
      (Kakeya.realRpowENN delta (-criticalFloor.structuralLoss)) := by
    exact (pureWZ2RigidImageFamily_pureCWA ancestor.geometry.frame.symm
      selected.family nearby).mono_loss ancestor.cropped_extremal.delta_pos
        ancestor.cropped_extremal.delta_le_one densityLoss_le_structural
  have densityPower :
      Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        Kakeya.realRpowENN delta outputEta :=
    pure_wz2_rpowENN_antitone ancestor.cropped_extremal.delta_pos
      ancestor.cropped_extremal.delta_le_one outputEta_le_structural
  have ordinaryDense :=
    core.refreshedOrdinaryShading_dense densityPower
  have ordinaryLower :
      Kakeya.realRpowENN delta (sigma + selectedLoss) ≤
        volume core.refreshedOrdinaryShading.union :=
    criticalFloor.volume_floor delta ancestor.cropped_extremal.delta_pos
      hdeltaCutoff core.refreshedOrdinaryFamily
      (by
        change 0 < core.refreshedOrdinaryFamily.card
        change 0 < core.retained.card
        exact Finset.card_pos.mpr core.retained_nonempty)
      core.refreshedOrdinaryShading ordinaryNearby ordinaryDense
  have imageVolume :
      volume (ancestor.geometry.frame ''
        core.refreshedOrdinaryShading.union) =
        volume core.refreshedOrdinaryShading.union :=
    Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      ancestor.geometry.frame _
      (measurableSet_shading_union core.refreshedOrdinaryShading)
  rw [core.refreshedOrdinaryShading_union_image] at imageVolume
  calc
    Kakeya.realRpowENN delta (sigma + selectedLoss) ≤
        volume core.refreshedOrdinaryShading.union := ordinaryLower
    _ = volume ((selectedTubeShading
        (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains) core.retained).union) :=
      imageVolume.symm
    _ ≤ volume (restrictPaperShading selected coarseGrains.shading).union := by
      apply measure_mono
      rintro point ⟨index, pointMem⟩
      exact ⟨index, pointMem.2⟩

/-- Refresh the exact re-entry on the selected cropped grain source.  The
ordinary source is the inverse rigid image of the selected overlap and its
normalization refinement is the identity. -/
noncomputable def refreshedReentry
    {selectedLoss nextSourceLoss : ℝ}
    (grainReceipt : PureWZ2Node05SelectedGrainReceipt core selectedLoss)
    (nextSourceLoss_pos : 0 < nextSourceLoss)
    (nextSourceLoss_le_half : nextSourceLoss ≤ selectedLoss / 2)
    (grainLoss_le : grainLoss ≤ nextSourceLoss)
    (densityPower :
      Kakeya.realRpowENN delta nextSourceLoss ≤
        Kakeya.realRpowENN delta outputEta)
    (fraction_le_one :
      wz2PaperPureRefinementFraction delta normalizationExponent ≤ 1)
    (ordinaryNearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-nextSourceLoss))) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) grainReceipt.toGrainConfiguration.shading
      normalizationExponent nextSourceLoss selectedLoss := by
  let selected := pureWZ2Node05PostGrainSelectedSubfamily
    coarseRefinement.selected.family core.retained
  let ordinarySource : PureWZ2ExtremalConfiguration
      sigma nextSourceLoss delta :=
    { family := core.refreshedOrdinaryFamily
      shading := core.refreshedOrdinaryShading
      extremal :=
        { delta_pos := ancestor.cropped_extremal.delta_pos
          delta_le_one := ancestor.cropped_extremal.delta_le_one
          nonempty := by
            change 0 < core.refreshedOrdinaryFamily.card
            change 0 < core.retained.card
            exact Finset.card_pos.mpr core.retained_nonempty
          cwa_nearby_scales :=
            pureWZ2RigidImageFamily_pureCWA ancestor.geometry.frame.symm
              selected.family ordinaryNearby
          dense := core.refreshedOrdinaryShading_dense densityPower
          volume_upper :=
            core.refreshedOrdinaryShading_volume_upper grainLoss_le } }
  let identity : Kakeya.Streamlined.TubeSubfamily ordinarySource.family :=
    { family := ordinarySource.family
      embedding := Function.Embedding.refl _
      tube_eq := fun _ => rfl }
  exact
    { sourceLoss_pos := nextSourceLoss_pos
      normalizationLoss_pos :=
        by linarith [nextSourceLoss_pos, nextSourceLoss_le_half]
      sourceLoss_le_half := nextSourceLoss_le_half
      ordinarySource := ordinarySource
      geometry :=
        { selected := identity
          selected_nonempty := ordinarySource.extremal.nonempty
          ordinaryRefined := ordinarySource.shading
          ordinary_subshading := fun _ => Set.Subset.rfl
          retained_mass := by
            calc
              wz2PaperPureRefinementFraction delta normalizationExponent *
                    ordinarySource.shading.mass ≤
                  1 * ordinarySource.shading.mass := by gcongr
              _ = ordinarySource.shading.mass := by simp
          frame := ancestor.geometry.frame
          indexEquiv := Equiv.refl _
          ordinary_carrier_image_eq := by
            intro index
            change (selected.family.tube index).carrier =
              ancestor.geometry.frame ''
                (core.refreshedOrdinaryFamily.tube index).carrier
            exact (core.refreshedOrdinaryFamily_frame_image index).symm
          ordinaryDensity := Kakeya.realRpowENN delta nextSourceLoss
          ordinaryDensity_pos := ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos ancestor.cropped_extremal.delta_pos _)
          ordinary_per_tube := by
            intro index
            change Kakeya.realRpowENN delta nextSourceLoss *
                (core.refreshedOrdinaryFamily.tube index).volume ≤
              volume (core.refreshedOrdinaryShading.carrier index)
            exact core.refreshedOrdinary_per_tube densityPower index
          ordinary_axial_window := by
            intro index point pointMem
            rw [core.refreshedOrdinaryShading_frame_image index] at pointMem
            exact ancestor.geometry.ordinary_axial_window _ point pointMem.1
          cropped_carrier_eq_dense_cubicalization := by
            intro index
            change
              (restrictPaperShading selected coarseGrains.shading).carrier index =
                pureWZ2DenseCubicalization (selected.family.tube index)
                  (ancestor.geometry.frame ''
                    core.refreshedOrdinaryShading.carrier index)
            rw [core.refreshedOrdinaryShading_frame_image index]
            rw [← pureWZ2Node05PostGrainSelectedOrdinaryTrace_frame_image
              coarseRefinement ancestor coarseGrains core.retained index]
            exact core.exact_dense_cubicalization index
          cropped_cubical := grainReceipt.extremal.cubical
          line_class := coarseGrains.line_class.subfamily selected
          ordinary_cell_containment := by
            intro index cell cellHit
            have overlapHit :
                ((ancestor.geometry.frame ''
                    ancestor.geometry.ordinaryRefined.carrier
                      (ancestor.geometry.indexEquiv.symm
                        ((core.retained.equivFin.symm index).1))) ∩
                  wz1PaperGridCube delta cell).Nonempty := by
              rcases cellHit with ⟨point, pointOrdinary, pointCell⟩
              rw [core.refreshedOrdinaryShading_frame_image index] at pointOrdinary
              exact ⟨point, pointOrdinary.1, pointCell⟩
            have containment := ancestor.geometry.ordinary_cell_containment
              (ancestor.geometry.indexEquiv.symm
                ((core.retained.equivFin.symm index).1)) cell overlapHit
            change wz1PaperGridCube delta cell ⊆
              wz1PaperTubeCarrier (selected.family.tube index)
            change wz1PaperGridCube delta cell ⊆
              wz1PaperTubeCarrier
                (coarseRefinement.selected.family.tube
                  ((core.retained.equivFin.symm index).1))
            simpa only [ancestor.geometry.indexEquiv.apply_symm_apply]
              using containment
          ordinary_bounded_base :=
            selectedTubeFamily_hasBoundedBase
              coarseRefinement.selected.family core.retained
              ancestor.geometry.ordinary_bounded_base }
      ordinary_density_budget := by
        change Kakeya.realRpowENN delta nextSourceLoss / 2 ≤
          Kakeya.realRpowENN delta nextSourceLoss
        rw [ENNReal.div_eq_inv_mul]
        exact mul_le_of_le_one_left (by positivity) (by norm_num)
      cropped_top_level_cwa := grainReceipt.top_level_cwa
      cropped_extremal := grainReceipt.extremal }

end PureWZ2Node05SynchronizedPostGrainCore

end Kakeya.Assouad

end
