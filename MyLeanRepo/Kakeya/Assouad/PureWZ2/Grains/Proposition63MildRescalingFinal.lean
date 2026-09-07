import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingScheduleAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CenteredGeneralizedADTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureNearbyToTopLevelCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalGrainRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GeneralPreGrainData
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingNormalizedGlobalGrain
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingIsotropicVolume

/-!
# Final assembly after the Proposition 6.3 mild rescaling

The two finite selections made while transporting Definition 2.12 are also
applied to the actual isotropic image shading.  This file records the common
final family and shading and transports both grain estimates to that exact
configuration.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

namespace Proposition63MildRescalingFiniteParentScheduleData

private theorem paperBodyFamily_mass_subfamily_le
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    (wz1PaperBodyFamily selected.family).mass ≤
      (wz1PaperBodyFamily family).mass := by
  let selectedIndices : Finset (Fin family.card) :=
    Finset.univ.map selected.embedding
  have hselected :
      (wz1PaperBodyFamily selected.family).mass =
        ∑ index ∈ selectedIndices,
          volume (wz1PaperTubeCarrier (family.tube index)) := by
    change (∑ index : Fin selected.family.card,
        volume (wz1PaperTubeCarrier (selected.family.tube index))) = _
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro index _
    rw [selected.tube_eq]
  rw [hselected]
  change (∑ index ∈ selectedIndices,
      volume (wz1PaperTubeCarrier (family.tube index))) ≤
    ∑ index : Fin family.card,
      volume (wz1PaperTubeCarrier (family.tube index))
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ selectedIndices) (fun _ _ _ => bot_le)

private lemma abs_inner_paperDirection_eq'
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (normal : Point3) :
    |inner ℝ tube.direction normal| =
      |inner ℝ (wz1PaperDirection tube) normal| := by
  unfold wz1PaperDirection
  split_ifs
  · rfl
  · simp [inner_neg_left]

/-- The final shading after the complete-parent selection and the strict
full-fiber degree regularization. -/
def finalShading
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)) :
    WZ1PaperTubeShading (fiberRegularizedSubfamily regularized).family :=
  restrictPaperShading
    (fiberRegularizedSubfamily regularized).toTubeSubfamily
    (selectedTargetShading selection targetShading)

/-- Every point of the final shading is the isotropic image of a point of
the original source shading. -/
theorem finalShading_union_subset_image
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {sourcePaperShading : WZ1PaperTubeShading sourceFine}
    {region : Set Point3}
    {hsourceDelta : 0 < sourceDelta}
    {hscaleDeltaSmall : scale * sourceDelta < 1 / 54}
    {width : ℝ}
    {hwidth : width = 1 / (9 * scale) - 6 * sourceDelta}
    {hregionMeasurable : MeasurableSet region}
    {hregionBox : ∀ point ∈ region, ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤ width}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (htarget : targetShading = proposition63MildRescalingShading hscale raw
      sourcePaperShading region hsourceDelta hscaleDeltaSmall width hwidth
      hregionMeasurable hregionBox)
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)) :
    (finalShading regularized).union ⊆
      wz1IsotropicRescalingMap center scale '' sourcePaperShading.union := by
  rintro point ⟨index, hpoint⟩
  have htargetPoint : point ∈ targetShading.carrier
      ((selectedTarget selection).embedding
        ((fiberRegularizedSubfamily regularized).embedding index)) := hpoint
  have htargetUnion : point ∈ targetShading.union :=
    ⟨(selectedTarget selection).embedding
      ((fiberRegularizedSubfamily regularized).embedding index),
      htargetPoint⟩
  have himage : targetShading.union ⊆
      wz1IsotropicRescalingMap center scale '' sourcePaperShading.union := by
    rw [htarget, proposition63MildRescalingShading_union]
    exact Set.image_mono Set.inter_subset_left
  exact himage htargetUnion

/-- The final target family remains in the paper line class. -/
theorem finalFamily_lineClass
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (hrawLine : WZ1PaperIsLineClass raw.family) :
    WZ1PaperIsLineClass (fiberRegularizedSubfamily regularized).family :=
  ((proposition63MildRescalingFamily_lineClass hscale raw hrawLine).subfamily
    (selectedTarget selection).toTubeSubfamily).subfamily
      (fiberRegularizedSubfamily regularized).toTubeSubfamily

/-- The final target family is supported in the ordinary unit ball. -/
theorem finalFamily_isInUnitBall
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (hsourceDelta : 0 < sourceDelta)
    (hscaleDelta : scale * sourceDelta ≤ 1 / 54)
    (hrawLine : WZ1PaperIsLineClass raw.family) :
    (fiberRegularizedSubfamily regularized).family.IsInUnitBall := by
  intro index
  rw [(fiberRegularizedSubfamily regularized).tube_eq,
    (selectedTarget selection).tube_eq]
  exact proposition63MildRescalingFamily_isInUnitBall
    hsourceDelta hscale hscaleDelta raw hrawLine _

/-- Restriction through both finite selections preserves cubicality. -/
theorem finalShading_cubical
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (htargetCubical : WZ1PaperIsCubicalShading targetShading) :
    WZ1PaperIsCubicalShading (finalShading regularized) :=
  restrictPaperShading_cubical
    (fiberRegularizedSubfamily regularized).toTubeSubfamily
    (restrictPaperShading_cubical
      (selectedTarget selection).toTubeSubfamily htargetCubical)

/-- The two genuine finite selections retain the target shaded mass with the
product of their explicit losses.  The first selection is weighted by the
actual target carrier volumes; the second is the simultaneous strict-fiber
degree regularization. -/
theorem finalShading_mass_retention
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (hweight : ∀ index, weight index = volume (targetShading.carrier index))
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)) :
    targetShading.mass ≤
      ((data.degree : ENNReal) ^ sourceSchedule.scaleCount *
        ((8 : ENNReal) *
          (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
            ENNReal) ^ (sourceSchedule.scaleCount + 1))) *
        (finalShading regularized).mass := by
  have hfirst : targetShading.mass ≤
      (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
        (selectedTargetShading selection targetShading).mass := by
    change (∑ index : Fin sourceFine.card,
        volume (targetShading.carrier index)) ≤
      (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
        (selectedTargetShading selection targetShading).mass
    calc
      (∑ index : Fin sourceFine.card,
          volume (targetShading.carrier index)) =
          ∑ index : Fin sourceFine.card, weight index := by
        apply Finset.sum_congr rfl
        intro index _
        exact (hweight index).symm
      _ ≤ (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
          ∑ index ∈ selection.selected, weight index :=
        selection.retained_weight
      _ = (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
          (selectedTargetShading selection targetShading).mass := by
        congr 1
        change (∑ index ∈ selection.selected, weight index) =
          ∑ index : Fin selection.selected.card,
            volume (targetShading.carrier
              (selection.selected.orderEmbOfFin rfl index))
        let equivalence : Fin selection.selected.card ≃ selection.selected :=
          (selection.selected.orderIsoOfFin rfl).toEquiv
        calc
          (∑ index ∈ selection.selected, weight index) =
              ∑ index ∈ selection.selected,
                volume (targetShading.carrier index) := by
            apply Finset.sum_congr rfl
            intro index _
            exact hweight index
          _ = ∑ index : selection.selected,
              volume (targetShading.carrier index.1) := by
            exact (Finset.sum_coe_sort selection.selected
              (fun index => volume (targetShading.carrier index))).symm
          _ = ∑ index : Fin selection.selected.card,
              volume (targetShading.carrier
                (selection.selected.orderEmbOfFin rfl index)) := by
            exact (Equiv.sum_comp (M := ENNReal) equivalence
              (fun index : selection.selected =>
                volume (targetShading.carrier index.1))).symm
  calc
    targetShading.mass ≤
        (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
          (selectedTargetShading selection targetShading).mass := hfirst
    _ ≤ (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
        (((8 : ENNReal) *
            (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
              ENNReal) ^ (sourceSchedule.scaleCount + 1)) *
          (finalShading regularized).mass) := by
      gcongr
      exact regularized.retained_mass
    _ = ((data.degree : ENNReal) ^ sourceSchedule.scaleCount *
        ((8 : ENNReal) *
          (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
            ENNReal) ^ (sourceSchedule.scaleCount + 1))) *
        (finalShading regularized).mass := by ring

/-- The mass ledger in the order used by Proposition 6.3: first remove
ordinary centered-containment conflicts, then make all nearby-scale parents
simultaneously separated, and finally regularize the complete parent fibers.
Unlike `finalShading_mass_retention`, the parent-selection weight is allowed
to be zero outside the cleanup set. -/
theorem finalShading_mass_retention_after_cleanup
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (cleanup : Proposition63MildRescalingCleanupData
      hscale raw targetShading)
    (hselectionMass :
      (∑ index ∈ cleanup.selectedIndices,
          volume (targetShading.carrier index)) ≤
        (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
          ∑ index ∈ selection.selected,
            volume (targetShading.carrier index))
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)) :
    targetShading.mass ≤
      (((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
          ℕ) : ENNReal) *
        (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
        ((8 : ENNReal) *
          (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
            ENNReal) ^ (sourceSchedule.scaleCount + 1))) *
        (finalShading regularized).mass := by
  have hcleanupMass :
      (restrictPaperShading
        (proposition63MildRescalingSelectedSubfamily
          (proposition63MildRescalingFamily hscale raw)
          cleanup.selectedIndices)
        targetShading).mass =
      ∑ index ∈ cleanup.selectedIndices,
        volume (targetShading.carrier index) := by
    change (∑ index : Fin cleanup.selectedIndices.card,
        volume (targetShading.carrier
          (cleanup.selectedIndices.equivFin.symm index).1)) = _
    calc
      (∑ index : Fin cleanup.selectedIndices.card,
          volume (targetShading.carrier
            (cleanup.selectedIndices.equivFin.symm index).1)) =
          ∑ index : cleanup.selectedIndices,
            volume (targetShading.carrier index.1) := by
        exact Equiv.sum_comp (M := ENNReal)
          cleanup.selectedIndices.equivFin.symm
          (fun index : cleanup.selectedIndices =>
            volume (targetShading.carrier index.1))
      _ = ∑ index ∈ cleanup.selectedIndices,
          volume (targetShading.carrier index) := by
        exact Finset.sum_coe_sort cleanup.selectedIndices
          (fun index => volume (targetShading.carrier index))
  have hselectedMass :
      (selectedTargetShading selection targetShading).mass =
        ∑ index ∈ selection.selected,
          volume (targetShading.carrier index) := by
    change (∑ index : Fin selection.selected.card,
        volume (targetShading.carrier
          (selection.selected.orderEmbOfFin rfl index))) = _
    let equivalence : Fin selection.selected.card ≃ selection.selected :=
      (selection.selected.orderIsoOfFin rfl).toEquiv
    calc
      (∑ index : Fin selection.selected.card,
          volume (targetShading.carrier
            (selection.selected.orderEmbOfFin rfl index))) =
          ∑ index : selection.selected,
            volume (targetShading.carrier index.1) := by
        exact Fintype.sum_equiv equivalence
          (fun index : Fin selection.selected.card =>
            volume (targetShading.carrier
              (selection.selected.orderEmbOfFin rfl index)))
          (fun index : selection.selected =>
            volume (targetShading.carrier index.1))
          (fun _ => rfl)
      _ = ∑ index ∈ selection.selected,
          volume (targetShading.carrier index) := by
        exact Finset.sum_coe_sort selection.selected
          (fun index => volume (targetShading.carrier index))
  calc
    targetShading.mass ≤
        (((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
            ℕ) : ENNReal) *
          (restrictPaperShading
            (proposition63MildRescalingSelectedSubfamily
              (proposition63MildRescalingFamily hscale raw)
              cleanup.selectedIndices)
            targetShading).mass) := cleanup.mass_retention
    _ = (((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
            ℕ) : ENNReal) *
          ∑ index ∈ cleanup.selectedIndices,
            volume (targetShading.carrier index)) := by
      rw [hcleanupMass]
    _ ≤ (((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
            ℕ) : ENNReal) *
          ((data.degree : ENNReal) ^ sourceSchedule.scaleCount *
            ∑ index ∈ selection.selected,
              volume (targetShading.carrier index))) := by
      gcongr
    _ = ((((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
            ℕ) : ENNReal) *
          (data.degree : ENNReal) ^ sourceSchedule.scaleCount) *
          (selectedTargetShading selection targetShading).mass) := by
      rw [hselectedMass]
      ring
    _ ≤ ((((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
            ℕ) : ENNReal) *
          (data.degree : ENNReal) ^ sourceSchedule.scaleCount) *
          (((8 : ENNReal) *
            (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
              ENNReal) ^ (sourceSchedule.scaleCount + 1)) *
            (finalShading regularized).mass)) := by
      gcongr
      exact regularized.retained_mass
    _ = (((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
            ℕ) : ENNReal) *
          (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
          ((8 : ENNReal) *
            (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
              ENNReal) ^ (sourceSchedule.scaleCount + 1))) *
          (finalShading regularized).mass := by ring

/-- Absorb the two selection losses into the final density exponent. -/
theorem finalShading_dense
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (hweight : ∀ index, weight index = volume (targetShading.carrier index))
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (sourceDensity finalDensity : ENNReal)
    (htargetDense : targetShading.IsLambdaDense sourceDensity)
    (hlossPos : 0 <
      (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
        ((8 : ENNReal) *
          (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
            ENNReal) ^ (sourceSchedule.scaleCount + 1)))
    (habsorb :
      (((data.degree : ENNReal) ^ sourceSchedule.scaleCount *
          ((8 : ENNReal) *
            (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
              ENNReal) ^ (sourceSchedule.scaleCount + 1))) *
        finalDensity) ≤ sourceDensity) :
    (finalShading regularized).IsLambdaDense finalDensity := by
  let loss : ENNReal :=
    (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
      ((8 : ENNReal) *
        (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
          ENNReal) ^ (sourceSchedule.scaleCount + 1))
  have hbody := paperBodyFamily_mass_subfamily_le
    ((selectedTarget selection).toTubeSubfamily.comp
      (fiberRegularizedSubfamily regularized).toTubeSubfamily)
  change (wz1PaperBodyFamily
      (fiberRegularizedSubfamily regularized).family).mass ≤
    (wz1PaperBodyFamily
      (proposition63MildRescalingFamily hscale raw)).mass at hbody
  have hretained := finalShading_mass_retention hweight regularized
  change targetShading.mass ≤
    loss * (finalShading regularized).mass at hretained
  have habsorb' : loss * finalDensity ≤ sourceDensity := by
    simpa only [loss] using habsorb
  have hscaled : loss *
      (finalDensity *
        (wz1PaperBodyFamily
          (fiberRegularizedSubfamily regularized).family).mass) ≤
      loss * (finalShading regularized).mass := by
    calc
      loss * (finalDensity *
          (wz1PaperBodyFamily
            (fiberRegularizedSubfamily regularized).family).mass) =
          (loss * finalDensity) *
            (wz1PaperBodyFamily
              (fiberRegularizedSubfamily regularized).family).mass := by ring
      _ ≤ sourceDensity *
          (wz1PaperBodyFamily
            (fiberRegularizedSubfamily regularized).family).mass := by
        gcongr
      _ ≤ sourceDensity *
          (wz1PaperBodyFamily
            (proposition63MildRescalingFamily hscale raw)).mass := by
        gcongr
      _ ≤ targetShading.mass := htargetDense
      _ ≤ loss * (finalShading regularized).mass := hretained
  have hlossZero : loss ≠ 0 := by
    exact (show 0 < loss by simpa only [loss] using hlossPos).ne'
  have hlossTop : loss ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top data.degree)
    · apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.pow_ne_top
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.natCast_ne_top
              (Nat.log 2 (2 * (selectedTarget selection).family.card)),
              by norm_num⟩)
  calc
    finalDensity *
        (wz1PaperBodyFamily
          (fiberRegularizedSubfamily regularized).family).mass =
        loss⁻¹ * (loss *
          (finalDensity *
            (wz1PaperBodyFamily
              (fiberRegularizedSubfamily regularized).family).mass)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlossZero hlossTop, one_mul]
    _ ≤ loss⁻¹ * (loss * (finalShading regularized).mass) := by gcongr
    _ = (finalShading regularized).mass := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlossZero hlossTop, one_mul]

/-- Density after the paper-order cleanup-first construction.  The loss is
the product of the ordinary-conflict cleanup, the simultaneous complete-
parent selection, and the full-fiber degree regularization. -/
theorem finalShading_dense_after_cleanup
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (cleanup : Proposition63MildRescalingCleanupData
      hscale raw targetShading)
    (hselectionMass :
      (∑ index ∈ cleanup.selectedIndices,
          volume (targetShading.carrier index)) ≤
        (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
          ∑ index ∈ selection.selected,
            volume (targetShading.carrier index))
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (sourceDensity finalDensity : ENNReal)
    (htargetDense : targetShading.IsLambdaDense sourceDensity)
    (hlossPos : 0 <
      ((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
          ℕ) : ENNReal) *
        (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
        ((8 : ENNReal) *
          (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
            ENNReal) ^ (sourceSchedule.scaleCount + 1)))
    (habsorb :
      ((((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
            ℕ) : ENNReal) *
          (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
          ((8 : ENNReal) *
            (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
              ENNReal) ^ (sourceSchedule.scaleCount + 1))) *
        finalDensity) ≤ sourceDensity) :
    (finalShading regularized).IsLambdaDense finalDensity := by
  let loss : ENNReal :=
    ((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
        ℕ) : ENNReal) *
      (data.degree : ENNReal) ^ sourceSchedule.scaleCount *
      ((8 : ENNReal) *
        (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 :
          ENNReal) ^ (sourceSchedule.scaleCount + 1))
  have hbody := paperBodyFamily_mass_subfamily_le
    ((selectedTarget selection).toTubeSubfamily.comp
      (fiberRegularizedSubfamily regularized).toTubeSubfamily)
  change (wz1PaperBodyFamily
      (fiberRegularizedSubfamily regularized).family).mass ≤
    (wz1PaperBodyFamily
      (proposition63MildRescalingFamily hscale raw)).mass at hbody
  have hretained := finalShading_mass_retention_after_cleanup
    cleanup hselectionMass regularized
  change targetShading.mass ≤
    loss * (finalShading regularized).mass at hretained
  have habsorb' : loss * finalDensity ≤ sourceDensity := by
    simpa only [loss] using habsorb
  have hscaled : loss *
      (finalDensity *
        (wz1PaperBodyFamily
          (fiberRegularizedSubfamily regularized).family).mass) ≤
      loss * (finalShading regularized).mass := by
    calc
      loss * (finalDensity *
          (wz1PaperBodyFamily
            (fiberRegularizedSubfamily regularized).family).mass) =
          (loss * finalDensity) *
            (wz1PaperBodyFamily
              (fiberRegularizedSubfamily regularized).family).mass := by ring
      _ ≤ sourceDensity *
          (wz1PaperBodyFamily
            (fiberRegularizedSubfamily regularized).family).mass := by
        gcongr
      _ ≤ sourceDensity *
          (wz1PaperBodyFamily
            (proposition63MildRescalingFamily hscale raw)).mass := by
        gcongr
      _ ≤ targetShading.mass := htargetDense
      _ ≤ loss * (finalShading regularized).mass := hretained
  have hlossZero : loss ≠ 0 := by
    exact (show 0 < loss by simpa only [loss] using hlossPos).ne'
  have hlossTop : loss ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.natCast_ne_top _
      · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top data.degree)
    · apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.pow_ne_top
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.natCast_ne_top
              (Nat.log 2 (2 * (selectedTarget selection).family.card)),
              by norm_num⟩)
  calc
    finalDensity *
        (wz1PaperBodyFamily
          (fiberRegularizedSubfamily regularized).family).mass =
        loss⁻¹ * (loss *
          (finalDensity *
            (wz1PaperBodyFamily
              (fiberRegularizedSubfamily regularized).family).mass)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlossZero hlossTop, one_mul]
    _ ≤ loss⁻¹ * (loss * (finalShading regularized).mass) := by gcongr
    _ = (finalShading regularized).mass := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlossZero hlossTop, one_mul]

/-- Positive final shaded mass prevents either finite selection from
collapsing the output family to the empty family. -/
theorem finalFamily_nonempty_of_mass_pos
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (hmass : 0 < (finalShading regularized).mass) :
    (fiberRegularizedSubfamily regularized).family.Nonempty := by
  by_contra hempty
  have hcard : (fiberRegularizedSubfamily regularized).family.card = 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.Nonempty, not_lt] using hempty
  have hzero : (finalShading regularized).mass = 0 := by
    change (∑ _index : Fin
      (fiberRegularizedSubfamily regularized).family.card, _) = 0
    apply Finset.sum_eq_zero
    intro index _
    exact Fin.elim0 (Fin.cast hcard index)
  rw [hzero] at hmass
  exact lt_irrefl 0 hmass

/-- A subshading of a positive isotropic image inherits the source volume
upper bound after the cubic Jacobian and the final exponent gap are paid. -/
theorem isotropicSubshading_volume_upper
    {sourceDelta scale sigma sourceLoss outputLoss : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFine}
    {targetFine : Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    {targetShading : WZ1PaperTubeShading targetFine}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFine sourceShading)
    (center : Point3)
    (hscale : 0 < scale)
    (htargetUnion : targetShading.union ⊆
      wz1IsotropicRescalingMap center scale '' sourceShading.union)
    (habsorb : ENNReal.ofReal (scale ^ 3) *
        Kakeya.realRpowENN sourceDelta (sigma - sourceLoss) ≤
      Kakeya.realRpowENN (scale * sourceDelta) (sigma - outputLoss)) :
    volume targetShading.union ≤
      Kakeya.realRpowENN (scale * sourceDelta) (sigma - outputLoss) := by
  calc
    volume targetShading.union ≤
        volume (wz1IsotropicRescalingMap center scale ''
          sourceShading.union) := measure_mono htargetUnion
    _ = ENNReal.ofReal (scale ^ 3) * volume sourceShading.union :=
      volume_image_wz1IsotropicRescalingMap hscale center
        sourceShading.union_measurable
    _ ≤ ENNReal.ofReal (scale ^ 3) *
        Kakeya.realRpowENN sourceDelta (sigma - sourceLoss) := by
      gcongr
      exact sourceExtremal.volume_upper
    _ ≤ Kakeya.realRpowENN (scale * sourceDelta)
        (sigma - outputLoss) := habsorb

/-- Assemble the final cropped extremal record once the paper's two mass
selections, nearby-scale CWA transport, and isotropic volume calculation have
been discharged. -/
theorem finalCroppedExtremal
    {sourceDelta scale sigma outputLoss : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (hsourceDelta : 0 < sourceDelta)
    (htargetDeltaOne : scale * sourceDelta ≤ 1)
    (hmass : 0 < (finalShading regularized).mass)
    (hnearby : WZ2PaperPureCWAAtNearbyScales
      (fiberRegularizedSubfamily regularized).family
      (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss)))
    (hcubical : WZ1PaperIsCubicalShading (finalShading regularized))
    (hdense : (finalShading regularized).IsLambdaDense
      (Kakeya.realRpowENN (scale * sourceDelta) outputLoss))
    (hvolume : volume (finalShading regularized).union ≤
      Kakeya.realRpowENN (scale * sourceDelta) (sigma - outputLoss)) :
    WZ2PaperCroppedIsExtremal sigma outputLoss
      (fiberRegularizedSubfamily regularized).family
      (finalShading regularized) :=
  { delta_pos := mul_pos (lt_of_lt_of_le zero_lt_one hscale) hsourceDelta
    delta_le_one := htargetDeltaOne
    nonempty := finalFamily_nonempty_of_mass_pos regularized hmass
    cwa_nearby_scales := hnearby
    cubical := hcubical
    dense := hdense
    volume_upper := hvolume }

/-- The finite target schedule gives the final ordinary nearby-scale CWA;
unit-ball support then converts it to the cropped top-level bound.  The
factor four is paid explicitly by the outer loss hierarchy. -/
theorem finalTopLevelCWA
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hsourceDelta : 0 < sourceDelta}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceRawShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    {regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)}
    {bodyConstant targetConstant finalConstant : ENNReal}
    (cwa : Proposition63MildRescalingFiniteCWAData
      data selection regularized bodyConstant targetConstant)
    (htargetDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      (fiberRegularizedSubfamily regularized).family)
    (htargetRho : ∀ coordinate,
      scale * (sourceSchedule.witness coordinate).rho ≤
        data.targetRho coordinate)
    (htargetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (htargetWindow : ∀ target :
      WZ2PaperRequestedScale (scale * sourceDelta),
      ENNReal.ofReal
          (data.targetRho
            (sourceSchedule.representative
              (proposition63MildRescalingSourceRequest
                hsourceDelta hscale target))) <
        targetConstant * ENNReal.ofReal target.1)
    (htargetSmall : scale * sourceDelta ≤ 1 / 24)
    (hsupport : (fiberRegularizedSubfamily regularized).family.IsInUnitBall)
    (habsorb : (4 : ENNReal) * targetConstant ≤ finalConstant) :
    WZ2PaperConvexWolffBound
      (fiberRegularizedSubfamily regularized).family finalConstant := by
  have hnearby := cwa.toNearbyScales htargetDistinct
    htargetRho htargetFinite htargetWindow
  have htop := pure_nearby_to_top_level
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale) hsourceDelta)
    htargetSmall hsupport hnearby
  intro convexSet hconvex
  exact (htop convexSet hconvex).trans <| by
    gcongr

/-- Construction-private companion to the paper-facing grain output.  It
records that the final slope and plane map are the literal transported maps
constructed below, so bounds on those exact source maps survive the final
mild rescaling without strengthening `PureWZ2GrainConfiguration`. -/
structure Proposition63MildRescalingFinalGrainData
    {sourceDelta scale sigma sourceLoss outputLoss : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFine)
    {Lplane Lslope : NNReal}
    (preGrains : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1)
    (targetFine : Kakeya.Streamlined.TubeFamily (scale * sourceDelta))
    (targetShading : WZ1PaperTubeShading targetFine) where
  line_class : WZ1PaperIsLineClass targetFine
  cubical : WZ1PaperIsCubicalShading targetShading
  extremal : WZ2PaperCroppedIsExtremal sigma outputLoss
    targetFine targetShading
  top_level_cwa : WZ2PaperConvexWolffBound targetFine
    (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))
  globalGrains : PureWZ2LipschitzGlobalGrainData targetShading sigma
    (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))
  localGrains : PureWZ2LocalGrainData targetShading sigma
    (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))
  planeMap_vertical_bound :
    (∀ point : {point : Point3 // point ∈ sourceShading.union},
      |preGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2) →
    ∀ point : {point : Point3 // point ∈ targetShading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  slope_bound :
    (∀ height : ℝ, height ∈ Set.Icc (-1 : ℝ) 1 →
      |preGrains.slope height| ≤ 3) →
    ∀ height : ℝ, height ∈ Set.Icc (-1 : ℝ) 1 →
      |globalGrains.slope height| ≤ 3

namespace Proposition63MildRescalingFinalGrainData

/-- Forget only the private construction provenance. -/
noncomputable def toGrainConfiguration
    {sourceDelta scale sigma sourceLoss outputLoss : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFine}
    {Lplane Lslope : NNReal}
    {preGrains : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {targetFine : Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    {targetShading : WZ1PaperTubeShading targetFine}
    (data : Proposition63MildRescalingFinalGrainData
      (outputLoss := outputLoss) sourceShading preGrains targetFine
      targetShading) :
    PureWZ2GrainConfiguration sigma outputLoss (scale * sourceDelta) where
  family := targetFine
  shading := targetShading
  line_class := data.line_class
  cubical := data.cubical
  extremal := data.extremal
  top_level_cwa := data.top_level_cwa
  globalGrains := data.globalGrains
  localGrains := data.localGrains

end Proposition63MildRescalingFinalGrainData

/-- Mechanical terminal step of the genuine mild rescaling, retaining the
construction-level map provenance needed by the Node-5-private quantitative
wrapper. -/
theorem finalGrainConfigurationWithBounds
    {sourceDelta scale sigma sourceLoss outputLoss : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFine}
    {Lplane Lslope : NNReal}
    (preGrains : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1)
    {targetFine : Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    {targetShading : WZ1PaperTubeShading targetFine}
    (sourceIndex : Fin targetFine.card → Fin sourceFine.card)
    (hdirection : ∀ index, (targetFine.tube index).direction =
      wz1PaperDirection (sourceFine.tube (sourceIndex index)))
    (center : Point3)
    (htargetCarrier : ∀ index, targetShading.carrier index ⊆
      wz1IsotropicRescalingMap center scale ''
        sourceShading.carrier (sourceIndex index))
    (htargetUnion : targetShading.union ⊆
      wz1IsotropicRescalingMap center scale '' sourceShading.union)
    (hscale : 1 ≤ scale)
    (hplaneScale : (Lplane : ℝ) ≤ scale)
    (hslopeScale : (Lslope : ℝ) ≤ scale)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDeltaOne : scale * sourceDelta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hsourceLoss : 0 < sourceLoss)
    (hsourceOutput : sourceLoss < outputLoss)
    (hADAbsorb : Real.rpow sourceDelta (outputLoss - sourceLoss) ≤
      Real.rpow scale (-outputLoss))
    (hline : WZ1PaperIsLineClass targetFine)
    (hcubical : WZ1PaperIsCubicalShading targetShading)
    (hextremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      targetFine targetShading)
    (htopLevel : WZ2PaperConvexWolffBound targetFine
      (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))) :
    Nonempty (Proposition63MildRescalingFinalGrainData
      (outputLoss := outputLoss) sourceShading preGrains targetFine
      targetShading) := by
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  let inverse : Point3 → Point3 :=
    wz1IsotropicRescalingInverse center scale
  have hinverseMem : ∀ point ∈ targetShading.union,
      inverse point ∈ sourceShading.union := by
    intro point hpoint
    rcases htargetUnion hpoint with ⟨source, hsource, hsourcePoint⟩
    have hinverse : inverse
        (wz1IsotropicRescalingMap center scale source) = source := by
      ext coordinate
      simp [inverse, wz1IsotropicRescalingInverse,
        wz1IsotropicRescalingMap]
      field_simp [hscalePos.ne']
      ring
    rw [← hsourcePoint, hinverse]
    exact hsource
  let targetPlaneMap :
      {point : Point3 // point ∈ targetShading.union} → Point3 :=
    fun point => preGrains.planeMap
      ⟨inverse point, hinverseMem point point.prop⟩
  have hplaneLipschitz : LipschitzWith 1 targetPlaneMap := by
    apply LipschitzWith.mk_one
    intro first second
    have hsource := preGrains.planeMap_lipschitz.dist_le_mul
      ⟨inverse first, hinverseMem first first.prop⟩
      ⟨inverse second, hinverseMem second second.prop⟩
    have hinverseDistance : dist (inverse first) (inverse second) =
        (1 / scale) * dist (first : Point3) second := by
      simp only [inverse, wz1IsotropicRescalingInverse, dist_eq_norm]
      rw [show center + scale⁻¹ • (first : Point3) -
          (center + scale⁻¹ • (second : Point3)) =
        scale⁻¹ • ((first : Point3) - second) by module,
        norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hscalePos]
      ring
    calc
      dist (targetPlaneMap first) (targetPlaneMap second) ≤
          (Lplane : ℝ) * dist (inverse first) (inverse second) := hsource
      _ = ((Lplane : ℝ) / scale) * dist (first : Point3) second := by
        rw [hinverseDistance]
        ring
      _ ≤ dist (first : Point3) second := by
        apply mul_le_of_le_one_left dist_nonneg
        exact (div_le_one hscalePos).2 hplaneScale
  have hplaneUnit : ∀ point, ‖targetPlaneMap point‖ = 1 :=
    fun point => preGrains.planeMap_unit _
  have hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ targetShading.carrier index,
        |inner ℝ (targetFine.tube index).direction
          (targetPlaneMap ⟨point, ⟨index, hpoint⟩⟩)| ≤
            scale * sourceDelta := by
    intro index point hpoint
    rcases htargetCarrier index hpoint with
      ⟨sourcePoint, hsourceCarrier, hsourcePoint⟩
    have hinversePoint : inverse point = sourcePoint := by
      rw [← hsourcePoint]
      ext coordinate
      simp [inverse, wz1IsotropicRescalingInverse,
        wz1IsotropicRescalingMap]
      field_simp [hscalePos.ne']
      ring
    have hsourceUnion : inverse point ∈ sourceShading.union :=
      ⟨sourceIndex index, by simpa [hinversePoint] using hsourceCarrier⟩
    calc
      |inner ℝ (targetFine.tube index).direction
          (targetPlaneMap ⟨point, ⟨index, hpoint⟩⟩)| =
          |inner ℝ (sourceFine.tube (sourceIndex index)).direction
            (preGrains.planeMap
              ⟨inverse point, hsourceUnion⟩)| := by
        rw [hdirection index, ← abs_inner_paperDirection_eq']
      _ ≤ sourceDelta := by
        simpa only [one_mul] using preGrains.planeMap_incidence
          (sourceIndex index) (inverse point) (by
            simpa [hinversePoint] using hsourceCarrier)
      _ ≤ scale * sourceDelta := by
        exact le_mul_of_one_le_left hsourceDelta.le hscale
  let targetSlope : ℝ → ℝ := fun height =>
    preGrains.slope (wz1ClampHeight (center 2 + height / scale))
  have hslopeLipschitz :
      LipschitzOnWith 1 targetSlope (Set.Icc (-1 : ℝ) 1) := by
    intro first _ second _
    have hfirst :
        wz1ClampHeight (center 2 + first / scale) ∈ Set.Icc (-1 : ℝ) 1 :=
      wz1ClampHeight_mem_Icc _
    have hsecond :
        wz1ClampHeight (center 2 + second / scale) ∈ Set.Icc (-1 : ℝ) 1 :=
      wz1ClampHeight_mem_Icc _
    have hsource := preGrains.slope_lipschitz
      hfirst hsecond
    have hclamp : dist
        (wz1ClampHeight (center 2 + first / scale))
        (wz1ClampHeight (center 2 + second / scale)) ≤
      (1 / scale) * dist first second := by
      simp only [Real.dist_eq]
      calc
        |wz1ClampHeight (center 2 + first / scale) -
            wz1ClampHeight (center 2 + second / scale)| ≤
            |(center 2 + first / scale) -
              (center 2 + second / scale)| :=
          wz1ClampHeight_dist_le _ _
        _ = (1 / scale) * |first - second| := by
          have h :
              (center 2 + first / scale) -
                  (center 2 + second / scale) =
                (first - second) / scale := by
            ring
          rw [h, abs_div, abs_of_pos hscalePos]
          ring
    calc
      edist (targetSlope first) (targetSlope second) ≤
          (Lslope : ENNReal) * edist
            (wz1ClampHeight (center 2 + first / scale))
            (wz1ClampHeight (center 2 + second / scale)) := hsource
      _ ≤ (Lslope : ENNReal) *
          ENNReal.ofReal ((1 / scale) * dist first second) := by
        rw [edist_dist]
        gcongr
      _ = ((Lslope : ENNReal) * ENNReal.ofReal (1 / scale)) *
          ENNReal.ofReal (dist first second) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
      _ ≤ (1 : ENNReal) * ENNReal.ofReal (dist first second) := by
        have hcoefficient :
            (Lslope : ENNReal) * ENNReal.ofReal (1 / scale) ≤ 1 := by
          rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_one.mpr <| by
            simpa [div_eq_mul_inv] using
              ((div_le_one hscalePos).2 hslopeScale)
        gcongr
      _ = (1 : ENNReal) * edist first second := by
        rw [edist_dist]
  have hlocalAD := local_ad_transport_centered_general preGrains.planeMap
    preGrains.local_ad hscalePos hscale center htargetUnion targetPlaneMap
    (fun _ => rfl) hsourceLoss hsourceOutput hADAbsorb hsourceDelta
    (by exact sub_pos.mpr hsigmaOne)
  have hglobalAD : ∀ height ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (targetSlope height))
          (horizontalSlice targetShading.union height))
        (scale * sourceDelta) (1 - sigma)
        (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss)) := by
    apply global_ad_transport_centered_general preGrains.slope
      preGrains.global_ad hscalePos center htargetUnion targetSlope
    · intro height hslice
      simp only [targetSlope]
      congr 1
      apply wz1ClampHeight_id
      rcases hslice with ⟨point, hpoint, hheight⟩
      rcases htargetUnion hpoint with ⟨source, hsource, hmap⟩
      have hcoordinate := congrArg (fun value : Point3 => value 2) hmap
      simp only [wz1IsotropicRescalingMap, PiLp.smul_apply, smul_eq_mul]
        at hcoordinate
      rw [hheight] at hcoordinate
      have hsourceHeight : source 2 = center 2 + height / scale := by
        have hcoordinate' :
            (source 2 - center 2) * scale = height := by
          simpa [mul_comm] using hcoordinate
        have hquotient : source 2 - center 2 = height / scale :=
          (eq_div_iff hscalePos.ne').2 hcoordinate'
        linarith
      rw [← hsourceHeight]
      have hbox := (sourceShading.subset_body
        (Classical.choose hsource) (Classical.choose_spec hsource)).2
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
    · exact hsourceLoss
    · exact hsourceOutput
    · exact hADAbsorb
    · exact hsourceDelta
    · exact sub_pos.mpr hsigmaOne
  exact ⟨{
    line_class := hline
    cubical := hcubical
    extremal := hextremal
    top_level_cwa := htopLevel
    globalGrains := PureWZ2LipschitzGlobalGrainData.ofRealFunction
      targetSlope hslopeLipschitz hglobalAD
    localGrains := {
      planeMap := targetPlaneMap
      planeMap_lipschitz := hplaneLipschitz
      planeMap_unit := hplaneUnit
      planeMap_incidence := hplaneIncidence
      local_ad := hlocalAD }
    planeMap_vertical_bound := by
      intro sourceVertical point
      exact sourceVertical _
    slope_bound := by
      intro sourceBound height _heightMem
      exact sourceBound _ (wz1ClampHeight_mem_Icc _)
  }⟩

/-- Paper-facing compatibility projection. -/
theorem finalGrainConfiguration
    {sourceDelta scale sigma sourceLoss outputLoss : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFine}
    {Lplane Lslope : NNReal}
    (preGrains : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1)
    {targetFine : Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    {targetShading : WZ1PaperTubeShading targetFine}
    (sourceIndex : Fin targetFine.card → Fin sourceFine.card)
    (hdirection : ∀ index, (targetFine.tube index).direction =
      wz1PaperDirection (sourceFine.tube (sourceIndex index)))
    (center : Point3)
    (htargetCarrier : ∀ index, targetShading.carrier index ⊆
      wz1IsotropicRescalingMap center scale ''
        sourceShading.carrier (sourceIndex index))
    (htargetUnion : targetShading.union ⊆
      wz1IsotropicRescalingMap center scale '' sourceShading.union)
    (hscale : 1 ≤ scale)
    (hplaneScale : (Lplane : ℝ) ≤ scale)
    (hslopeScale : (Lslope : ℝ) ≤ scale)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDeltaOne : scale * sourceDelta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hsourceLoss : 0 < sourceLoss)
    (hsourceOutput : sourceLoss < outputLoss)
    (hADAbsorb : Real.rpow sourceDelta (outputLoss - sourceLoss) ≤
      Real.rpow scale (-outputLoss))
    (hline : WZ1PaperIsLineClass targetFine)
    (hcubical : WZ1PaperIsCubicalShading targetShading)
    (hextremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      targetFine targetShading)
    (htopLevel : WZ2PaperConvexWolffBound targetFine
      (Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))) :
    Nonempty (PureWZ2GrainConfiguration sigma outputLoss
      (scale * sourceDelta)) := by
  rcases finalGrainConfigurationWithBounds preGrains sourceIndex hdirection
      center htargetCarrier htargetUnion hscale hplaneScale hslopeScale
      hsourceDelta htargetDeltaOne hsigma hsigmaOne hsourceLoss hsourceOutput
      hADAbsorb hline hcubical hextremal htopLevel with ⟨data⟩
  exact ⟨data.toGrainConfiguration⟩

end Proposition63MildRescalingFiniteParentScheduleData

end Kakeya.Assouad.PureWZ2

end
