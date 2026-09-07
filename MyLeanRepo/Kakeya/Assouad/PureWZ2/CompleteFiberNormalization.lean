import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberCanonicalOrientation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationRigidCWATransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationSourceDerivedProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationRigidBodyMassRatio
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationRigidCropMassRetention
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationDenseCubicalVolumeBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ExtremalSpatialCellCWAProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CriticalHeavyCellNormalizationStepProducer

/-!
# Cropped normalization from one complete strict fiber

The complete-fiber localization supplies all-scale pure CWA and one common
parent.  Canonical orientation is used only to construct the common rigid
frame; the final cropped family is the exact rigid image of the original
localized family.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2ExactRigidCropFrameCertificate

variable
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (certificate : PureWZ2ExactRigidCropFrameCertificate family)

/-- The exact rigid-frame margin makes every source-intersecting grid cell a
valid cropped paper cell. -/
theorem ordinary_cell_containment
    (deltaPos : 0 < delta)
    (shading : Kakeya.Streamlined.TubeShading family)
    (index : Fin family.card)
    (cell : ℤ × ℤ × ℤ)
    (cellMeets :
      ((certificate.frame '' shading.carrier index) ∩
          wz1PaperGridCube delta cell).Nonempty) :
    wz1PaperGridCube delta cell ⊆
      wz1PaperTubeCarrier
        ((pureWZ2RigidImageFamily
          certificate.frame family).tube index) := by
  let tube :=
    (pureWZ2RigidImageFamily certificate.frame family).tube index
  let framedSource := certificate.frame '' shading.carrier index
  have sourceSubset : framedSource ⊆ tube.carrier := by
    rw [pureWZ2RigidImageFamily_carrier]
    exact Set.image_mono (shading.subset_body index)
  apply
    pureWZ2_gridCube_subset_paperCarrier_of_rigid_margin
      deltaPos tube framedSource sourceSubset
  · intro point pointMem coordinate
    have bounds := certificate.carrier_margin index point pointMem
    fin_cases coordinate
    · exact bounds.1
    · exact bounds.2.1
    · exact bounds.2.2
  · exact cellMeets

/-- The exact rigid-frame margin places every target basepoint in the public
radius-four parameter window. -/
theorem hasBoundedBase_four
    (deltaPos : 0 < delta) :
    HasBoundedBase
      (pureWZ2RigidImageFamily certificate.frame family) 4 := by
  intro index
  let tube :=
    (pureWZ2RigidImageFamily certificate.frame family).tube index
  have baseSegment :
      tube.base ∈ Kakeya.unitSegment tube.base tube.direction :=
    ⟨0, by norm_num, by simp [Kakeya.unitSegment]⟩
  have baseCarrier : tube.base ∈ tube.carrier :=
    Metric.mem_cthickening_of_dist_le
      _ _ delta _ baseSegment (by simpa using deltaPos.le)
  have bounds := certificate.carrier_margin index tube.base baseCarrier
  have oneMinusLe : 1 - delta ≤ 1 := by linarith
  have coordinateBounds :
      |tube.base 0| ≤ 1 ∧ |tube.base 1| ≤ 1 ∧ |tube.base 2| ≤ 1 :=
    ⟨bounds.1.trans oneMinusLe,
      bounds.2.1.trans oneMinusLe,
      bounds.2.2.trans oneMinusLe⟩
  have normSquared :
      ‖tube.base‖ ^ 2 =
        tube.base 0 ^ 2 + tube.base 1 ^ 2 + tube.base 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have squareZero : tube.base 0 ^ 2 ≤ 1 := by
    have :=
      (sq_le_sq₀ (abs_nonneg (tube.base 0))
        (by norm_num : (0 : ℝ) ≤ 1)).mpr coordinateBounds.1
    simpa [sq_abs] using this
  have squareOne : tube.base 1 ^ 2 ≤ 1 := by
    have :=
      (sq_le_sq₀ (abs_nonneg (tube.base 1))
        (by norm_num : (0 : ℝ) ≤ 1)).mpr coordinateBounds.2.1
    simpa [sq_abs] using this
  have squareTwo : tube.base 2 ^ 2 ≤ 1 := by
    have :=
      (sq_le_sq₀ (abs_nonneg (tube.base 2))
        (by norm_num : (0 : ℝ) ≤ 1)).mpr coordinateBounds.2.2
    simpa [sq_abs] using this
  nlinarith [norm_nonneg tube.base]

end PureWZ2ExactRigidCropFrameCertificate

/--
Forget the auxiliary indexing of a finite rigid-crop certificate once its
target family has been identified with the canonical rigid image.
-/
noncomputable def PureWZ2RigidCropFrameCertificate.toExact
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (certificate : PureWZ2RigidCropFrameCertificate family) :
    PureWZ2ExactRigidCropFrameCertificate family := by
  exact
    {
      frame := certificate.frame
      carrier_margin := by
        intro index point pointMem
        apply
          certificate.carrier_margin
            (certificate.indexEquiv index) point
        rwa [certificate.cropped_tube_eq index]
      axisBox := by
        intro index point pointMem
        apply
          certificate.axisBox
            (certificate.indexEquiv index)
        rwa [certificate.cropped_tube_eq index]
      line_class := by
        intro index
        have line :=
          certificate.line_class
            (certificate.indexEquiv index)
        rwa [certificate.cropped_tube_eq index] at line
    }

namespace PureWZ2CompleteFiberLocalizationData

/--
Structural normalization data on the whole localized complete fiber.

The ordinary selection and shading are unchanged.  Thus exponent zero retains
all ordinary mass, while pure CWA is transported through one common rigid
isometry.
-/
noncomputable def toSourceDerivedStructuralData
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (data :
      PureWZ2CompleteFiberLocalizationData source localized)
    (certificate :
      PureWZ2ExactRigidCropFrameCertificate localized.family)
    (inputLossLeHalf : inputLoss ≤ outputLoss / 2)
    (inputLossLe : inputLoss ≤ outputLoss)
    (perTubeDensity :
      ∀ index,
        (Kakeya.realRpowENN delta inputLoss / 2) *
              volume (localized.family.tube index).carrier ≤
          volume (localized.shading.carrier index))
    (ordinaryAxialWindow :
      ∀ index point,
        point ∈ certificate.frame '' localized.shading.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8)
    (topLevelCWA :
      WZ2PaperConvexWolffBound
        (pureWZ2RigidImageFamily certificate.frame localized.family)
        (Kakeya.realRpowENN delta (-outputLoss))) :
    PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
      (outputLoss := outputLoss) source localized 0 := by
  let selected :
      Kakeya.Streamlined.TubeSubfamily localized.family :=
    {
      family := localized.family
      embedding := Equiv.toEmbedding (Equiv.refl _)
      tube_eq := fun _ => rfl
    }
  refine
    {
      input_loss_le_half := inputLossLeHalf
      selected := selected
      selected_nonempty := ?_
      ordinaryRefined := localized.shading
      ordinary_subshading := ?_
      retained_mass := ?_
      frame := certificate.frame
      croppedFamily :=
        pureWZ2RigidImageFamily certificate.frame localized.family
      indexEquiv := Equiv.refl _
      ordinary_carrier_image_eq :=
        pureWZ2RigidImageFamily_carrier
          certificate.frame localized.family
      ordinary_per_tube := by
        intro index
        simpa [selected] using perTubeDensity index
      ordinary_axial_window := by
        intro index point pointMem
        simpa [selected] using
          ordinaryAxialWindow index point pointMem
      line_class := certificate.line_class
      cropped_pure_cwa := ?_
      cropped_top_level_cwa := topLevelCWA
      ordinary_cell_containment := ?_
      ordinary_bounded_base :=
        certificate.hasBoundedBase_four localized.extremal.delta_pos
    }
  · simpa [selected] using localized.extremal.nonempty
  · intro index
    simpa [selected]
  · simp [wz2PaperPureRefinementFraction]
  · have transported :=
      pureWZ2RigidImageFamily_pureCWA
        certificate.frame localized.family
        (localized.extremal.cwa_nearby_scales.mono_loss
          localized.extremal.delta_pos
          localized.extremal.delta_le_one inputLossLe)
    exact transported
  · intro index cell cellMeets
    change
      wz1PaperGridCube delta cell ⊆
        wz1PaperTubeCarrier
          ((pureWZ2RigidImageFamily
            certificate.frame localized.family).tube index)
    exact
      certificate.ordinary_cell_containment
        localized.extremal.delta_pos localized.shading
        index cell cellMeets

end PureWZ2CompleteFiberLocalizationData

/--
Generic exact-rigid structural data.  The stronger source is retained only as
provenance; all ordinary and cropped objects belong to the same final
localized extremizer.
-/
noncomputable def pureWZ2ExactRigidCropStructuralData
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta)
    (certificate :
      PureWZ2ExactRigidCropFrameCertificate localized.family)
    (inputLossLeHalf : inputLoss ≤ outputLoss / 2)
    (inputLossLe : inputLoss ≤ outputLoss)
    (perTubeDensity :
      ∀ index,
        (Kakeya.realRpowENN delta inputLoss / 2) *
              volume (localized.family.tube index).carrier ≤
          volume (localized.shading.carrier index))
    (ordinaryAxialWindow :
      ∀ index point,
        point ∈ certificate.frame '' localized.shading.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8)
    (topLevelCWA :
      WZ2PaperConvexWolffBound
        (pureWZ2RigidImageFamily certificate.frame localized.family)
        (Kakeya.realRpowENN delta (-outputLoss))) :
    PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
      (outputLoss := outputLoss) source localized 0 := by
  let selected :
      Kakeya.Streamlined.TubeSubfamily localized.family :=
    {
      family := localized.family
      embedding := Equiv.toEmbedding (Equiv.refl _)
      tube_eq := fun _ => rfl
    }
  refine
    {
      input_loss_le_half := inputLossLeHalf
      selected := selected
      selected_nonempty := ?_
      ordinaryRefined := localized.shading
      ordinary_subshading := ?_
      retained_mass := ?_
      frame := certificate.frame
      croppedFamily :=
        pureWZ2RigidImageFamily certificate.frame localized.family
      indexEquiv := Equiv.refl _
      ordinary_carrier_image_eq :=
        pureWZ2RigidImageFamily_carrier
          certificate.frame localized.family
      ordinary_per_tube := by
        intro index
        simpa [selected] using perTubeDensity index
      ordinary_axial_window := by
        intro index point pointMem
        simpa [selected] using
          ordinaryAxialWindow index point pointMem
      line_class := certificate.line_class
      cropped_pure_cwa :=
        pureWZ2RigidImageFamily_pureCWA
          certificate.frame localized.family
          (localized.extremal.cwa_nearby_scales.mono_loss
            localized.extremal.delta_pos
            localized.extremal.delta_le_one inputLossLe)
      cropped_top_level_cwa := topLevelCWA
      ordinary_cell_containment := ?_
      ordinary_bounded_base :=
        certificate.hasBoundedBase_four localized.extremal.delta_pos
    }
  · simpa [selected] using localized.extremal.nonempty
  · intro index
    simpa [selected]
  · simp [wz2PaperPureRefinementFraction]
  · intro index cell cellMeets
    change
      wz1PaperGridCube delta cell ⊆
        wz1PaperTubeCarrier
          ((pureWZ2RigidImageFamily
            certificate.frame localized.family).tube index)
    exact
      certificate.ordinary_cell_containment
        localized.extremal.delta_pos localized.shading
        index cell cellMeets

/--
The complete parent together with aggregate-to-pointwise pruning supplies a
genuine weighted-CWA preselection without any spatial-cell cut.
-/
noncomputable def pureWZ2CompleteFiberPruningPreselection
    {sigma originalLoss sourceLoss pruningLoss delta : ℝ}
    {original :
      PureWZ2ExtremalConfiguration sigma originalLoss delta}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (completeData :
      PureWZ2CompleteFiberLocalizationData original source)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (cellLoss : ℝ)
    (rhoQuarter : completeData.nearby.rho ≤ 1 / 4)
    (massAbsorption :
      2 * Kakeya.realRpowENN delta cellLoss ≤ 1) :
    PureWZ2SpatialCellPreselectionData
      (cellLoss := cellLoss) source pruning := by
  let preSelected :
      WZ2PaperPureTubeSubfamily source.family :=
    {
      family := selectedTubeFamily source.family pruning.indices
      embedding :=
        {
          toFun := fun index =>
            (pruning.indices.equivFin.symm index).1
          inj' := by
            intro first second equal
            apply pruning.indices.equivFin.symm.injective
            apply Subtype.ext
            exact equal
        }
      tube_eq := fun _ => rfl
    }
  let localShading :=
    selectedTubeShading source.shading pruning.indices
  refine
    {
      preSelected := preSelected
      preSelected_nonempty := ?_
      selected_from_pruning := ?_
      localShading := localShading
      subshading := ?_
      per_tube_local_density := ?_
      source_mass_retention := ?_
      center :=
        wz2PaperTubeMidpoint
          (completeData.nearby.scaleData.coarse.tube
            completeData.parent)
      family_bases_local := ?_
      shading_support_local := ?_
    }
  · change 0 < pruning.indices.card
    exact pruning.nonempty.card_pos
  · intro index
    exact (pruning.indices.equivFin.symm index).2
  · intro index
    exact Set.Subset.rfl
  · intro index
    have raw :=
      pruning.per_tube_density
        (preSelected.embedding index)
        (pruning.indices.equivFin.symm index).2
    change
      Kakeya.realRpowENN delta pruningLoss *
          volume (preSelected.family.tube index).carrier ≤
        volume (localShading.carrier index)
    rw [preSelected.tube_eq index]
    simpa [localShading, preSelected,
      selectedTubeShading, Kakeya.DeltaTube.volume] using raw
  · have halfRetention := pruning.mass_retention
    calc
      Kakeya.realRpowENN delta cellLoss *
            source.shading.mass ≤
          Kakeya.realRpowENN delta cellLoss *
            (2 * localShading.mass) := by
        gcongr
      _ =
          (2 * Kakeya.realRpowENN delta cellLoss) *
            localShading.mass := by ring
      _ ≤ 1 * localShading.mass := by
        gcongr
      _ = localShading.mass := one_mul _
  · intro index
    let ambientIndex := preSelected.embedding index
    let parentTube :=
      completeData.nearby.scaleData.coarse.tube
        completeData.parent
    have baseFine :
        (source.family.tube ambientIndex).base ∈
          (source.family.tube ambientIndex).carrier := by
      apply Metric.mem_cthickening_of_dist_le
        (source.family.tube ambientIndex).base
        (source.family.tube ambientIndex).base delta
        (Kakeya.unitSegment
          (source.family.tube ambientIndex).base
          (source.family.tube ambientIndex).direction)
      · exact ⟨0, by norm_num, by simp⟩
      · simp [source.extremal.delta_pos.le]
    have baseParent : (source.family.tube ambientIndex).base ∈
        parentTube.carrier :=
      completeData.parent_containment ambientIndex baseFine
    have parentBound :=
      tube_subset_midpoint_closedBall
        completeData.nearby.scaleData.rho_pos
        parentTube baseParent
    change
      dist (source.family.tube ambientIndex).base
          (wz2PaperTubeMidpoint parentTube) ≤
        1 / 2 + completeData.nearby.rho at parentBound
    change
      dist (preSelected.family.tube index).base
          (wz2PaperTubeMidpoint parentTube) ≤ 3
    rw [preSelected.tube_eq index]
    exact parentBound.trans (by linarith)
  · rintro point ⟨index, pointMem⟩
    let ambientIndex := preSelected.embedding index
    let parentTube :=
      completeData.nearby.scaleData.coarse.tube
        completeData.parent
    have pointFine :
        point ∈ (source.family.tube ambientIndex).carrier := by
      exact source.shading.subset_body ambientIndex pointMem
    have pointParent : point ∈ parentTube.carrier :=
      completeData.parent_containment ambientIndex pointFine
    have parentBound :=
      tube_subset_midpoint_closedBall
        completeData.nearby.scaleData.rho_pos
        parentTube pointParent
    change
      dist point (wz2PaperTubeMidpoint parentTube) ≤
        1 / 2 + completeData.nearby.rho at parentBound
    change
      dist point (wz2PaperTubeMidpoint parentTube) ≤ 1
    exact parentBound.trans (by linarith)

/--
Every pruning subfamily of one complete parent has the same six-parameter
log-cardinality envelope as a fixed spatial cluster.
-/
theorem pureWZ2CompleteFiberPruning_card_log_bound
    {sigma originalLoss sourceLoss pruningLoss delta : ℝ}
    {original :
      PureWZ2ExtremalConfiguration sigma originalLoss delta}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (completeData :
      PureWZ2CompleteFiberLocalizationData original source)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (rhoQuarter : completeData.nearby.rho ≤ 1 / 4) :
    (Nat.log 2
        (2 *
          (selectedTubeFamily
            source.family pruning.indices).card) + 1 : ℝ) ≤
      pureWZ2HeavyCellCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  let family :=
    selectedTubeFamily source.family pruning.indices
  have familyDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct family := by
    intro first second distinct
    let firstAmbient :=
      (pruning.indices.equivFin.symm first).1
    let secondAmbient :=
      (pruning.indices.equivFin.symm second).1
    have ambientDistinct : firstAmbient ≠ secondAmbient := by
      intro equal
      apply distinct
      exact
        pruning.indices.equivFin.symm.injective
          (Subtype.ext equal)
    simpa [family, selectedTubeFamily] using
      source.extremal.cwa_nearby_scales.2.2.1
        firstAmbient secondAmbient ambientDistinct
  let parentTube :=
    completeData.nearby.scaleData.coarse.tube
      completeData.parent
  have midpointLocal :
      ∀ index : Fin family.card,
        ‖wz2PaperTubeMidpoint (family.tube index) -
            wz2PaperTubeMidpoint parentTube‖ ≤ 4 := by
    intro index
    let ambientIndex :=
      (pruning.indices.equivFin.symm index).1
    have contained :
        (source.family.tube ambientIndex).carrier ⊆
          parentTube.carrier :=
      completeData.parent_containment ambientIndex
    have raw :=
      wz2PaperSourceMidpoint_dist_le_five_mul_of_carrier_subset
        source.extremal.delta_pos
        completeData.nearby.scaleData.rho_pos
        (source.family.tube ambientIndex) parentTube contained
    change
      ‖wz2PaperTubeMidpoint (family.tube index) -
          wz2PaperTubeMidpoint parentTube‖ ≤ 4
    rw [show family.tube index =
        source.family.tube ambientIndex by rfl]
    rw [← dist_eq_norm]
    exact raw.trans (by linarith)
  have raw :=
    wz2PaperOrdinary_local_six_grid_card_bound
      source.extremal.delta_pos
      (show (0 : ℝ) ≤ 4 by norm_num)
      familyDistinct Finset.univ
      (wz2PaperTubeMidpoint parentTube)
      (fun index _ => midpointLocal index)
  have firstArgument :
      4 / (delta / 64) = 256 / delta := by
    field_simp [source.extremal.delta_pos.ne']
    norm_num
  have secondArgument :
      1 / (delta / 64) ≤ 256 / delta := by
    have identity :
        1 / (delta / 64) = 64 / delta := by
      field_simp [source.extremal.delta_pos.ne']
    rw [identity]
    exact
      div_le_div_of_nonneg_right
        (by norm_num) source.extremal.delta_pos.le
  have cardBound :
      family.card ≤
        (2 * Nat.ceil (256 / delta) + 1) ^ 6 := by
    calc
      family.card ≤
          (2 * Nat.ceil (4 / (delta / 64)) + 1) ^ 3 *
            (2 * Nat.ceil (1 / (delta / 64)) + 1) ^ 3 := by
        simpa [family] using raw
      _ ≤
          (2 * Nat.ceil (256 / delta) + 1) ^ 3 *
            (2 * Nat.ceil (256 / delta) + 1) ^ 3 := by
        rw [firstArgument]
        gcongr
      _ = (2 * Nat.ceil (256 / delta) + 1) ^ 6 := by ring
  have deltaLeOne := source.extremal.delta_le_one
  exact
    pureWZ2HeavyCell_card_log_bound
      source.extremal.delta_pos deltaLeOne
      (by
        simpa [family] using cardBound)

/--
Uniform scalar absorptions for the same-parent complete-fiber localization.

The coarser branch spends five source-loss copies: four from the quadratic
scale ratio and one from the ambient pure-CWA constant.
-/
theorem exists_pureWZ2CompleteFiberAbsorptions
    {sourceLoss inputLoss : ℝ}
    (sourceLossPos : 0 < sourceLoss)
    (fiveSourceLossLt : 5 * sourceLoss < inputLoss) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ,
        0 < delta →
        delta ≤ delta₀ →
          (1 : ENNReal) ≤
              Kakeya.realRpowENN delta (-inputLoss) ∧
          (4 : ENNReal) *
              Kakeya.realRpowENN delta (-sourceLoss) <
            Kakeya.realRpowENN delta (-inputLoss) ∧
          ∀ actual coarser : ℝ,
            Real.rpow delta (2 * sourceLoss) ≤ actual →
            actual ≤ coarser →
            coarser ≤ 1 →
              ENNReal.ofReal
                    (81 * (coarser / actual) ^ 2) *
                  Kakeya.realRpowENN delta (-sourceLoss) ≤
                Kakeya.realRpowENN delta (-inputLoss) := by
  have oneGapPos :
      0 < inputLoss - sourceLoss := by
    linarith
  have fiveGapPos :
      0 < inputLoss - 5 * sourceLoss := by
    linarith
  rcases
      exists_delta_realRpowENN_bound
        (5 : ENNReal) (by norm_num) oneGapPos
    with
    ⟨fourDelta, fourDeltaPos, fourDeltaLeOne, fourBound⟩
  rcases
      exists_delta_realRpowENN_bound
        (81 : ENNReal) (by norm_num) fiveGapPos
    with
    ⟨ratioDelta, ratioDeltaPos, ratioDeltaLeOne, ratioBound⟩
  let delta₀ := min fourDelta ratioDelta
  have delta₀Pos : 0 < delta₀ :=
    lt_min fourDeltaPos ratioDeltaPos
  have delta₀LeOne : delta₀ ≤ 1 :=
    (min_le_left fourDelta ratioDelta).trans fourDeltaLeOne
  refine ⟨delta₀, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe
  have deltaOne : delta ≤ 1 :=
    deltaLe.trans delta₀LeOne
  have deltaFour : delta ≤ fourDelta :=
    deltaLe.trans (min_le_left fourDelta ratioDelta)
  have deltaRatio : delta ≤ ratioDelta :=
    deltaLe.trans (min_le_right fourDelta ratioDelta)
  have outputOne :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (-inputLoss) := by
    have raw :=
      pure_wz2_rpowENN_antitone
        deltaPos deltaOne
        (show -inputLoss ≤ 0 by
          linarith [fiveSourceLossLt, sourceLossPos])
    simpa [Kakeya.realRpowENN] using raw
  have fourStrict :
      (4 : ENNReal) *
            Kakeya.realRpowENN delta (-sourceLoss) <
          Kakeya.realRpowENN delta (-inputLoss) := by
    have gapBound :
        (5 : ENNReal) ≤
          Kakeya.realRpowENN delta
            (-(inputLoss - sourceLoss)) :=
      fourBound delta deltaPos deltaFour
    have fourGap :
        (4 : ENNReal) <
          Kakeya.realRpowENN delta
            (-(inputLoss - sourceLoss)) :=
      (show (4 : ENNReal) < 5 by norm_num).trans_le gapBound
    have sourcePowerPos :
        0 <
          Kakeya.realRpowENN delta (-sourceLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos deltaPos (-sourceLoss))
    calc
      (4 : ENNReal) *
            Kakeya.realRpowENN delta (-sourceLoss) <
          Kakeya.realRpowENN delta
              (-(inputLoss - sourceLoss)) *
            Kakeya.realRpowENN delta (-sourceLoss) := by
        rw [mul_comm (4 : ENNReal),
          mul_comm
            (Kakeya.realRpowENN delta
              (-(inputLoss - sourceLoss)))]
        exact
          ENNReal.mul_lt_mul_right
            sourcePowerPos.ne' ENNReal.ofReal_ne_top fourGap
      _ =
          Kakeya.realRpowENN delta (-inputLoss) := by
        rw [Subunit.realRpowENN_mul deltaPos]
        congr 1
        ring
  refine ⟨outputOne, fourStrict, ?_⟩
  intro actual coarser actualLower actualLeCoarser coarserLeOne
  have deltaPowerPos :
      0 < Real.rpow delta (2 * sourceLoss) :=
    Real.rpow_pos_of_pos deltaPos _
  have actualPos : 0 < actual :=
    deltaPowerPos.trans_le actualLower
  have coarserPos : 0 < coarser :=
    actualPos.trans_le actualLeCoarser
  have inverseActual :
      actual⁻¹ ≤
        (Real.rpow delta (2 * sourceLoss))⁻¹ :=
    (inv_le_inv₀ actualPos deltaPowerPos).2 actualLower
  have ratioUpper :
      coarser / actual ≤
        (Real.rpow delta (2 * sourceLoss))⁻¹ := by
    rw [div_eq_mul_inv]
    calc
      coarser * actual⁻¹ ≤
          1 * actual⁻¹ := by
        gcongr
      _ ≤
          1 *
            (Real.rpow delta (2 * sourceLoss))⁻¹ := by
        gcongr
      _ =
          (Real.rpow delta (2 * sourceLoss))⁻¹ := one_mul _
  have ratioNonnegative : 0 ≤ coarser / actual :=
    div_nonneg coarserPos.le actualPos.le
  have inverseNonnegative :
      0 ≤ (Real.rpow delta (2 * sourceLoss))⁻¹ := by
    positivity
  have ratioSquare :
      (coarser / actual) ^ 2 ≤
        Real.rpow delta (-(4 * sourceLoss)) := by
    calc
      (coarser / actual) ^ 2 ≤
          ((Real.rpow delta (2 * sourceLoss))⁻¹) ^ 2 := by
        gcongr
      _ =
          Real.rpow delta (-(4 * sourceLoss)) := by
        have negativePower :
            (Real.rpow delta (2 * sourceLoss))⁻¹ =
              Real.rpow delta (-(2 * sourceLoss)) :=
          (Real.rpow_neg deltaPos.le (2 * sourceLoss)).symm
        rw [negativePower, pow_two]
        calc
          Real.rpow delta (-(2 * sourceLoss)) *
                Real.rpow delta (-(2 * sourceLoss)) =
              Real.rpow delta
                (-(2 * sourceLoss) + -(2 * sourceLoss)) :=
            (Real.rpow_add deltaPos _ _).symm
          _ = Real.rpow delta (-(4 * sourceLoss)) := by
            congr 1
            ring
  have ratioENN :
      ENNReal.ofReal (81 * (coarser / actual) ^ 2) ≤
        (81 : ENNReal) *
          Kakeya.realRpowENN delta (-(4 * sourceLoss)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
    gcongr
    exact ENNReal.ofReal_mono (by simpa only [neg_mul] using ratioSquare)
  have constantBound :
      (81 : ENNReal) ≤
        Kakeya.realRpowENN delta
          (-(inputLoss - 5 * sourceLoss)) :=
    ratioBound delta deltaPos deltaRatio
  calc
    ENNReal.ofReal (81 * (coarser / actual) ^ 2) *
          Kakeya.realRpowENN delta (-sourceLoss) ≤
        ((81 : ENNReal) *
          Kakeya.realRpowENN delta (-(4 * sourceLoss))) *
          Kakeya.realRpowENN delta (-sourceLoss) := by
      gcongr
    _ =
        (81 : ENNReal) *
          Kakeya.realRpowENN delta (-(5 * sourceLoss)) := by
      rw [show
        ((81 : ENNReal) *
            Kakeya.realRpowENN delta (-(4 * sourceLoss))) *
            Kakeya.realRpowENN delta (-sourceLoss) =
          (81 : ENNReal) *
            (Kakeya.realRpowENN delta (-(4 * sourceLoss)) *
              Kakeya.realRpowENN delta (-sourceLoss)) by ring,
        Subunit.realRpowENN_mul deltaPos]
      congr 2
      ring
    _ ≤
        Kakeya.realRpowENN delta
            (-(inputLoss - 5 * sourceLoss)) *
          Kakeya.realRpowENN delta (-(5 * sourceLoss)) := by
      gcongr
    _ =
        Kakeya.realRpowENN delta (-inputLoss) := by
      rw [Subunit.realRpowENN_mul deltaPos]
      congr 1
      ring

/-- Final ordinary loss before the cropped normalization output loss. -/
def pureWZ2CompleteNormalizationFinalLoss
    (outputLoss : ℝ) : ℝ :=
  min (outputLoss / 8) (1 / 2)

/-- Loss of the complete strict fiber before pointwise-density pruning. -/
def pureWZ2CompleteNormalizationFiberLoss
    (outputLoss : ℝ) : ℝ :=
  pureWZ2CompleteNormalizationFinalLoss outputLoss / 8

/-- Loss of the source extremizer before complete-fiber localization. -/
def pureWZ2CompleteNormalizationSourceLoss
    (outputLoss : ℝ) : ℝ :=
  pureWZ2CompleteNormalizationFiberLoss outputLoss / 8

/-- Pointwise-density pruning loss inside the complete strict fiber. -/
def pureWZ2CompleteNormalizationPruningLoss
    (outputLoss : ℝ) : ℝ :=
  (3 / 2) * pureWZ2CompleteNormalizationFiberLoss outputLoss

/--
The exact-loss complete-fiber normalization interface.

Unlike the existential public normalizer, this interface exposes that the
localized source returned to the cropped continuation has loss exactly
`pureWZ2CompleteNormalizationFinalLoss outputLoss`.
-/
def PureWZ2CompleteFiberNormalizationAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
      ∃ sourceLoss delta₁ : ℝ,
        0 < sourceLoss ∧
        0 < pureWZ2CompleteNormalizationFinalLoss outputLoss ∧
        pureWZ2CompleteNormalizationFinalLoss outputLoss ≤
          outputLoss / 2 ∧
        0 < delta₁ ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₁ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma sourceLoss delta,
            ∃ localized :
                PureWZ2ExtremalConfiguration
                  sigma
                  (pureWZ2CompleteNormalizationFinalLoss outputLoss)
                  delta,
              Nonempty
                (PureWZ2CroppedCriticalNormalizationSourceLeaves
                  (outputLoss := outputLoss)
                  localized normalizationExponent)

/-- The complete-fiber normalization together with the quantitative axial
bound proved by its exact rigid crop.  The ordinary family and shading are
those of `leaves`; this record only retains a sharper bound that the public
normalization interface intentionally forgets. -/
structure PureWZ2CompleteFiberNormalizationAxialData
    {sigma outputLoss delta : ℝ}
    (localized : PureWZ2ExtremalConfiguration sigma
      (pureWZ2CompleteNormalizationFinalLoss outputLoss) delta)
    (normalizationExponent : ℕ) where
  leaves : PureWZ2CroppedCriticalNormalizationSourceLeaves
    (outputLoss := outputLoss) localized normalizationExponent
  ordinary_axial_bound : ∀ index point,
    point ∈ leaves.frame '' leaves.ordinaryRefined.carrier index →
      |point (2 : Fin 3)| ≤ Real.sqrt 3 / 16 + 4 * delta

/-- Exact-loss normalization retaining the rigid crop's quantitative axial
slack for the first sampled-coarse call in Proposition 6.3. -/
def PureWZ2CompleteFiberNormalizationAxialAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
      ∃ sourceLoss delta₁ : ℝ,
        0 < sourceLoss ∧
        0 < pureWZ2CompleteNormalizationFinalLoss outputLoss ∧
        pureWZ2CompleteNormalizationFinalLoss outputLoss ≤ outputLoss / 2 ∧
        0 < delta₁ ∧
        delta₁ ≤ 1 / 1000 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₁ →
          ∀ source : PureWZ2ExtremalConfiguration sigma sourceLoss delta,
            ∃ localized : PureWZ2ExtremalConfiguration sigma
                (pureWZ2CompleteNormalizationFinalLoss outputLoss) delta,
              Nonempty (PureWZ2CompleteFiberNormalizationAxialData
                localized normalizationExponent)

theorem pureWZ2CompleteNormalizationLossHierarchy
    {outputLoss : ℝ}
    (outputLossPos : 0 < outputLoss) :
    let finalLoss :=
      pureWZ2CompleteNormalizationFinalLoss outputLoss
    let fiberLoss :=
      pureWZ2CompleteNormalizationFiberLoss outputLoss
    let sourceLoss :=
      pureWZ2CompleteNormalizationSourceLoss outputLoss
    let pruningLoss :=
      pureWZ2CompleteNormalizationPruningLoss outputLoss
    0 < sourceLoss ∧
      5 * sourceLoss < fiberLoss ∧
      sourceLoss ≤ fiberLoss ∧
      2 * sourceLoss ≤ 1 ∧
      0 < fiberLoss ∧
      fiberLoss < pruningLoss ∧
      pruningLoss ≤ finalLoss ∧
      0 < finalLoss ∧
      finalLoss ≤ outputLoss ∧
      finalLoss ≤ 1 ∧
      4 * fiberLoss < finalLoss ∧
      3 * finalLoss < outputLoss ∧
      2 * finalLoss < outputLoss := by
  dsimp only [
    pureWZ2CompleteNormalizationFinalLoss,
    pureWZ2CompleteNormalizationFiberLoss,
    pureWZ2CompleteNormalizationSourceLoss,
    pureWZ2CompleteNormalizationPruningLoss
  ]
  have finalPos :
      0 < min (outputLoss / 8) (1 / 2) :=
    lt_min (by positivity) (by norm_num)
  have finalOutput :
      min (outputLoss / 8) (1 / 2) ≤ outputLoss / 8 :=
    min_le_left _ _
  have finalHalf :
      min (outputLoss / 8) (1 / 2) ≤ 1 / 2 :=
    min_le_right _ _
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · exact finalPos
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- Convert the existing rigid-crop scalar package to the exact constants. -/
theorem pureWZ2ExactRigidCropScalarConsequences
    {sigma inputLoss outputLoss delta : ℝ}
    (deltaPos : 0 < delta)
    (absorption :
      PureWZ2LocalizedCanonicalRigidCropScalarAbsorption
        inputLoss outputLoss delta) :
    Kakeya.realRpowENN delta (outputLoss - inputLoss) *
          (13824 : ENNReal) ≤
        (100 : ENNReal)⁻¹ ∧
      (100 : ENNReal) *
            (Kakeya.realRpowENN delta inputLoss)⁻¹ *
            Kakeya.realRpowENN delta (sigma - inputLoss) ≤
          Kakeya.realRpowENN delta (sigma - outputLoss) := by
  constructor
  · exact absorption.body_crop.trans (by
      exact ENNReal.inv_le_inv.mpr (by norm_num))
  · have inversePower :
        (Kakeya.realRpowENN delta inputLoss)⁻¹ =
          Kakeya.realRpowENN delta (-inputLoss) :=
      pure_wz2_realRpowENN_inv deltaPos
    have powerIdentity :
        Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta (sigma - inputLoss) =
          Kakeya.realRpowENN delta
              (outputLoss - 2 * inputLoss) *
            Kakeya.realRpowENN delta
              (sigma - outputLoss) := by
      rw [Subunit.realRpowENN_mul deltaPos,
        Subunit.realRpowENN_mul deltaPos]
      congr 1
      ring
    rw [inversePower]
    calc
      (100 : ENNReal) *
            Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta (sigma - inputLoss) =
          100 *
            (Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta (sigma - inputLoss)) := by
        ring
      _ =
          (100 *
            Kakeya.realRpowENN delta
              (outputLoss - 2 * inputLoss)) *
            Kakeya.realRpowENN delta
              (sigma - outputLoss) := by
        rw [powerIdentity]
        ring
      _ ≤
          (200 *
            Kakeya.realRpowENN delta
              (outputLoss - 2 * inputLoss)) *
            Kakeya.realRpowENN delta
              (sigma - outputLoss) := by
        gcongr
        norm_num
      _ ≤
          1 *
            Kakeya.realRpowENN delta
              (sigma - outputLoss) := by
        gcongr
        exact absorption.union
      _ =
          Kakeya.realRpowENN delta
            (sigma - outputLoss) := one_mul _

private theorem pureWZ2_per_tube_density_half
    {delta densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family)
    (perTubeDensity :
      ∀ index,
        Kakeya.realRpowENN delta densityLoss *
              volume (family.tube index).carrier ≤
          volume (shading.carrier index)) :
    ∀ index,
      (Kakeya.realRpowENN delta densityLoss / 2) *
            volume (family.tube index).carrier ≤
        volume (shading.carrier index) := by
  intro index
  have halfPower :
      Kakeya.realRpowENN delta densityLoss / (2 : ENNReal) ≤
        Kakeya.realRpowENN delta densityLoss := by
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
    calc
      Kakeya.realRpowENN delta densityLoss =
          Kakeya.realRpowENN delta densityLoss * 1 := by simp
      _ ≤ Kakeya.realRpowENN delta densityLoss * (2 : ENNReal) :=
        mul_le_mul_left' (by norm_num) _
  exact
    (mul_le_mul_right' halfPower
      (volume (family.tube index).carrier)).trans
      (perTubeDensity index)

/--
Quantitative canonical-crop bounds from an exact rigid-frame certificate and
pointwise ordinary density.
-/
noncomputable def pureWZ2ExactRigidCanonicalCropQuantitativeBounds
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta)
    (certificate :
      PureWZ2ExactRigidCropFrameCertificate localized.family)
    (topLevelCWA :
      WZ2PaperConvexWolffBound
        (pureWZ2RigidImageFamily certificate.frame localized.family)
        (Kakeya.realRpowENN delta (-outputLoss)))
    (inputLossLeHalf : inputLoss ≤ outputLoss / 2)
    (inputLossLe : inputLoss ≤ outputLoss)
    (deltaTriple : 3 * delta ≤ 1)
    (perTubeDensity :
      ∀ index,
        Kakeya.realRpowENN delta inputLoss *
            volume (localized.family.tube index).carrier ≤
          volume (localized.shading.carrier index))
    (ordinaryAxialWindow :
      ∀ index point,
        point ∈ certificate.frame '' localized.shading.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8)
    (densityAbsorption :
      Kakeya.realRpowENN delta (outputLoss - inputLoss) *
          (13824 : ENNReal) ≤
        (100 : ENNReal)⁻¹)
    (volumeAbsorption :
      (100 : ENNReal) *
          (Kakeya.realRpowENN delta inputLoss)⁻¹ *
          Kakeya.realRpowENN delta (sigma - inputLoss) ≤
        Kakeya.realRpowENN delta (sigma - outputLoss)) :
    PureWZ2CanonicalCropQuantitativeBounds
      (pureWZ2ExactRigidCropStructuralData
        source localized certificate
          inputLossLeHalf inputLossLe
          (pureWZ2_per_tube_density_half
            (densityLoss := inputLoss)
            localized.shading perTubeDensity)
          ordinaryAxialWindow
          topLevelCWA) := by
  let data :=
    pureWZ2ExactRigidCropStructuralData
      source localized certificate
        inputLossLeHalf inputLossLe
        (pureWZ2_per_tube_density_half
          (densityLoss := inputLoss)
          localized.shading perTubeDensity)
        ordinaryAxialWindow
        topLevelCWA
  have paperBody :
      (wz1PaperBodyFamily data.croppedFamily).mass ≤
        (13824 : ENNReal) *
          localized.family.toBodyFamily.mass := by
    have raw :=
      wz2PaperBodyFamily_mass_le_ordinary
        localized.extremal.delta_pos
        localized.extremal.delta_le_one
        data.croppedFamily data.line_class
    calc
      (wz1PaperBodyFamily data.croppedFamily).mass ≤
          (13824 : ENNReal) *
            data.croppedFamily.toBodyFamily.mass := raw
      _ =
          (13824 : ENNReal) *
            localized.family.toBodyFamily.mass := by
        congr 1
        change
          (∑ index : Fin localized.family.card,
              volume
                ((pureWZ2RigidImageFamily
                  certificate.frame localized.family).tube index).carrier) =
            ∑ index : Fin localized.family.card,
              volume (localized.family.tube index).carrier
        apply Finset.sum_congr rfl
        intro index _
        rw [pureWZ2RigidImageFamily_carrier,
          Kakeya.Streamlined.AffineIsometryEquiv.volume_image
            certificate.frame
            (localized.family.tube index).carrier
            (wz2_paper_ordinary_tube_carrier_measurable
              (localized.family.tube index)
              localized.extremal.delta_pos)]
  have cropMass :
      (100 : ENNReal)⁻¹ * data.ordinaryRefined.mass ≤
        data.canonicalCroppedShading.mass := by
    change
      (100 : ENNReal)⁻¹ *
          ∑ index : Fin localized.family.card,
            volume (localized.shading.carrier index) ≤
        ∑ index : Fin localized.family.card,
          volume
            (pureWZ2DenseCubicalization
              ((pureWZ2RigidImageFamily
                certificate.frame localized.family).tube index)
              (certificate.frame ''
                localized.shading.carrier index))
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index _
    have sourceMeasurable :
        MeasurableSet
          (certificate.frame ''
            localized.shading.carrier index) :=
      certificate.frame.toHomeomorph.measurableEmbedding
        |>.measurableSet_image'
          (localized.shading.measurable_carrier index)
    have sourceSubset :
        certificate.frame ''
              localized.shading.carrier index ⊆
          ((pureWZ2RigidImageFamily
            certificate.frame localized.family).tube index).carrier := by
      rw [pureWZ2RigidImageFamily_carrier]
      exact Set.image_mono (localized.shading.subset_body index)
    have margin :
        ∀ point,
          point ∈
              ((pureWZ2RigidImageFamily
                certificate.frame localized.family).tube index).carrier →
            ∀ coordinate : Fin 3,
              |point coordinate| ≤ 1 - delta := by
      intro point pointMem coordinate
      have bounds :=
        certificate.carrier_margin
          index point pointMem
      fin_cases coordinate <;> tauto
    have lower :=
      pureWZ2_denseCubicalization_volume_lower_of_rigid_margin
        localized.extremal.delta_pos deltaTriple
        ((pureWZ2RigidImageFamily
          certificate.frame localized.family).tube index)
        (certificate.frame ''
          localized.shading.carrier index)
        sourceMeasurable sourceSubset margin
    rw [Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      certificate.frame
      (localized.shading.carrier index)
      (localized.shading.measurable_carrier index)] at lower
    simpa using lower
  have paperCarrierCover :
      ∀ index,
        wz1PaperTubeCarrier
            ((pureWZ2RigidImageFamily
              certificate.frame localized.family).tube index) ⊆
          ⋃ cell ∈
            wz1PaperGridIndicesInWindow
              delta localized.extremal.delta_pos,
            wz1PaperGridCube delta cell := by
    intro index point pointMem
    let cell := wz1PaperGridIndex delta point
    have pointBox :
        point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      pointMem.2
    have cellMem :
        cell ∈ wz1PaperGridIndicesInWindow
          delta localized.extremal.delta_pos :=
      rigidCrop_gridIndex_mem_window
        localized.extremal.delta_pos pointBox
    exact
      Set.mem_iUnion₂.mpr
        ⟨cell, cellMem,
          (mem_wz1PaperGridCube delta cell point).mpr rfl⟩
  have framedPerTubeDensity :
      ∀ index,
        Kakeya.realRpowENN delta inputLoss *
              volume
                ((pureWZ2RigidImageFamily
                  certificate.frame localized.family).tube index).carrier ≤
          volume
            (certificate.frame ''
              localized.shading.carrier index) := by
    intro index
    have raw := perTubeDensity index
    rw [pureWZ2RigidImageFamily_carrier,
      Kakeya.Streamlined.AffineIsometryEquiv.volume_image
        certificate.frame
        (localized.family.tube index).carrier
        (wz2_paper_ordinary_tube_carrier_measurable
          (localized.family.tube index)
          localized.extremal.delta_pos),
      Kakeya.Streamlined.AffineIsometryEquiv.volume_image
        certificate.frame
        (localized.shading.carrier index)
        (localized.shading.measurable_carrier index)]
    exact raw
  have unionExpansion :
      volume data.canonicalCroppedShading.union ≤
        ((100 : ENNReal) *
          (Kakeya.realRpowENN delta inputLoss)⁻¹) *
          volume
            (data.frame '' data.ordinaryRefined.union) := by
    exact
      @pureWZ2NormalizationCroppedShading_union_volume_upper
        delta localized.extremal.delta_pos
        localized.family
        (pureWZ2RigidImageFamily
          certificate.frame localized.family)
        certificate.frame (Equiv.refl _)
        localized.shading
        (Kakeya.realRpowENN delta inputLoss)
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos
            localized.extremal.delta_pos inputLoss))
        ENNReal.ofReal_ne_top
        (wz1PaperGridIndicesInWindow
          delta localized.extremal.delta_pos)
        paperCarrierCover framedPerTubeDensity
  exact
    {
      bodyFactor := 13824
      cropMassFactor := (100 : ENNReal)⁻¹
      volumeFactor :=
        (100 : ENNReal) *
          (Kakeya.realRpowENN delta inputLoss)⁻¹
      paper_body_mass_upper := paperBody
      crop_mass_retention := cropMass
      density_absorption := densityAbsorption
      union_volume_expansion := unionExpansion
      volume_absorption := volumeAbsorption
    }

/--
Complete strict-fiber normalization closes the source-derived frozen leaf at
exponent zero.

The source threshold is fixed before the source extremizer.  The construction
then runs, in order:

1. complete-parent same-scale localization;
2. aggregate-to-pointwise density pruning;
3. weighted nearby-CWA recovery on the pruned family;
4. the inherited exact common rigid frame; and
5. canonical dense-crop scalar assembly.
-/
theorem pureWZ2_completeFiber_normalization_exact_with_axial_bound :
    PureWZ2CompleteFiberNormalizationAxialAt 0 := by
  intro sigma outputLoss outputLossPos
  let finalLoss :=
    pureWZ2CompleteNormalizationFinalLoss outputLoss
  let fiberLoss :=
    pureWZ2CompleteNormalizationFiberLoss outputLoss
  let sourceLoss :=
    pureWZ2CompleteNormalizationSourceLoss outputLoss
  let pruningLoss :=
    pureWZ2CompleteNormalizationPruningLoss outputLoss
  let geometryPruningLoss := 2 * fiberLoss
  let baseCellLoss := pruningLoss
  let geometryCellLoss := 2 * fiberLoss
  rcases
      pureWZ2CompleteNormalizationLossHierarchy outputLossPos
    with
    ⟨sourceLossPos, fiveSourceFiber, sourceFiber,
      twoSourceOne, fiberLossPos, fiberPruning,
      pruningFinal, finalLossPos, finalOutput,
      finalOne, fourFiberFinal, threeFinalOutput,
      twoFinalOutput⟩
  have fiberFinal : fiberLoss < finalLoss :=
    fiberPruning.trans_le pruningFinal
  have finalHalfOutput : finalLoss ≤ outputLoss / 2 := by
    linarith
  have baseCellLossPos : 0 < baseCellLoss := by
    dsimp only [baseCellLoss, pruningLoss,
      pureWZ2CompleteNormalizationPruningLoss]
    positivity
  have geometryPruningFinal :
      geometryPruningLoss ≤ finalLoss := by
    dsimp only [geometryPruningLoss, finalLoss, fiberLoss,
      pureWZ2CompleteNormalizationFiberLoss]
    nlinarith [fiberLossPos]
  have geometryCellLossPos : 0 < geometryCellLoss := by
    dsimp only [geometryCellLoss]
    positivity
  have geometryCellFinal : geometryCellLoss < finalLoss := by
    dsimp only [geometryCellLoss, finalLoss, fiberLoss,
      pureWZ2CompleteNormalizationFiberLoss]
    nlinarith [fiberLossPos]
  have baseCellGeometry : baseCellLoss < geometryCellLoss := by
    dsimp only [baseCellLoss, geometryCellLoss, pruningLoss,
      pureWZ2CompleteNormalizationPruningLoss]
    nlinarith [fiberLossPos]
  have pruningGeometry : pruningLoss < geometryPruningLoss := by
    dsimp only [geometryPruningLoss, pruningLoss, fiberLoss,
      pureWZ2CompleteNormalizationPruningLoss,
      pureWZ2CompleteNormalizationFiberLoss]
    nlinarith [fiberLossPos]
  have weightedGap :
      3 * fiberLoss + geometryCellLoss < finalLoss := by
    dsimp only [geometryCellLoss]
    have finalIdentity :
        finalLoss = 8 * fiberLoss := by
      dsimp only [finalLoss, fiberLoss,
        pureWZ2CompleteNormalizationFiberLoss]
      ring
    rw [finalIdentity]
    nlinarith [fiberLossPos]
  rcases
      exists_pureWZ2CompleteFiberAbsorptions
        sourceLossPos fiveSourceFiber
    with
    ⟨completeDelta, completeDeltaPos, _completeDeltaOne,
      completeAbsorption⟩
  have pruningGapPos : 0 < pruningLoss - fiberLoss := by
    linarith
  rcases
      Subunit.exists_delta₀_mul_pow_le_one
        2 (by norm_num)
        (pruningLoss - fiberLoss) pruningGapPos
    with
    ⟨pruningDelta, pruningDeltaPos, _pruningDeltaOne,
      pruningAbsorption⟩
  rcases
      Subunit.exists_delta₀_mul_pow_le_one
        2 (by norm_num) baseCellLoss baseCellLossPos
    with
    ⟨massDelta, massDeltaPos, _massDeltaOne,
      massAbsorption⟩
  rcases
      Subunit.exists_delta₀_mul_pow_le_one
        235298 (by norm_num)
        (geometryPruningLoss - pruningLoss)
        (by linarith)
    with
    ⟨fineCellDensityDelta, fineCellDensityDeltaPos,
      _fineCellDensityDeltaOne, fineCellDensityAbsorption⟩
  rcases
      Subunit.exists_delta₀_mul_pow_le_one
        2823576 (by norm_num)
        (geometryCellLoss - baseCellLoss)
        (by linarith)
    with
    ⟨finiteSelectionDelta, finiteSelectionDeltaPos,
      _finiteSelectionDeltaOne, finiteSelectionAbsorption⟩
  rcases
      exists_pureWZ2HeavyCellActualAbsorptions
        finalLossPos fiberFinal geometryCellFinal weightedGap
    with
    ⟨weightedDelta, weightedDeltaPos, _weightedDeltaOne,
      weightedAbsorption⟩
  rcases
      pure_wz2_exists_delta₀_rpow_le
        (show (0 : ℝ) < 1 / 1000 by norm_num)
        sourceLossPos
    with
    ⟨sourcePowerDelta, sourcePowerDeltaPos,
      _sourcePowerDeltaOne, sourcePowerSmall⟩
  rcases
      exists_pureWZ2_pureNearby_topCWA_absorption
        threeFinalOutput
    with
    ⟨topDelta, topDeltaPos, _topDeltaOne, topAbsorption⟩
  rcases
      exists_pureWZ2LocalizedCanonicalRigidCropScalarAbsorption
        finalLossPos twoFinalOutput
    with
    ⟨cropDelta, cropDeltaPos, _cropDeltaOne, cropAbsorption⟩
  let geometryDelta :=
    min pruningDelta
      (min massDelta
        (min fineCellDensityDelta finiteSelectionDelta))
  let outputDelta :=
    min weightedDelta
      (min sourcePowerDelta
        (min topDelta (min cropDelta (1 / 1000))))
  let delta₁ :=
    min completeDelta (min geometryDelta outputDelta)
  have delta₁Pos : 0 < delta₁ := by
    dsimp only [delta₁]
    positivity
  have delta₁Small : delta₁ ≤ 1 / 1000 := by
    have outputSmall : outputDelta ≤ 1 / 1000 := by
      dsimp only [outputDelta]
      exact (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
    exact (show delta₁ ≤ outputDelta by
      dsimp only [delta₁]
      exact (min_le_right _ _).trans (min_le_right _ _)).trans outputSmall
  refine
    ⟨sourceLoss, delta₁,
      sourceLossPos, finalLossPos, finalHalfOutput,
      delta₁Pos, delta₁Small, ?_⟩
  intro delta deltaPos deltaLe source
  have deltaComplete : delta ≤ completeDelta :=
    deltaLe.trans (min_le_left _ _)
  have deltaGeometry : delta ≤ geometryDelta :=
    deltaLe.trans <|
      (min_le_right completeDelta _).trans (min_le_left _ _)
  have deltaOutput : delta ≤ outputDelta :=
    deltaLe.trans <|
      (min_le_right completeDelta _).trans (min_le_right _ _)
  have deltaPruning : delta ≤ pruningDelta :=
    deltaGeometry.trans (min_le_left _ _)
  have deltaMass : delta ≤ massDelta :=
    deltaGeometry.trans <|
      (min_le_right pruningDelta _).trans (min_le_left _ _)
  have deltaWeighted : delta ≤ weightedDelta :=
    deltaOutput.trans (min_le_left _ _)
  have deltaFineCellDensity : delta ≤ fineCellDensityDelta :=
    deltaGeometry.trans <|
      (min_le_right pruningDelta _).trans <|
        (min_le_right massDelta _).trans (min_le_left _ _)
  have deltaFiniteSelection : delta ≤ finiteSelectionDelta :=
    deltaGeometry.trans <|
      (min_le_right pruningDelta _).trans <|
        (min_le_right massDelta _).trans (min_le_right _ _)
  have deltaSourcePower : delta ≤ sourcePowerDelta :=
    deltaOutput.trans <|
      (min_le_right weightedDelta _).trans (min_le_left _ _)
  have deltaTop : delta ≤ topDelta :=
    deltaOutput.trans <|
      (min_le_right weightedDelta _).trans <|
        (min_le_right sourcePowerDelta _).trans (min_le_left _ _)
  have deltaCrop : delta ≤ cropDelta :=
    deltaOutput.trans <|
      (min_le_right weightedDelta _).trans <|
        (min_le_right sourcePowerDelta _).trans <|
          (min_le_right topDelta _).trans (min_le_left _ _)
  have deltaRigid : delta ≤ 1 / 1000 :=
    deltaOutput.trans <|
      (min_le_right weightedDelta _).trans <|
        (min_le_right sourcePowerDelta _).trans <|
          (min_le_right topDelta _).trans (min_le_right _ _)
  have deltaLeOne : delta ≤ 1 := by
    linarith
  have deltaLtOne : delta < 1 := by
    linarith
  have completeScalar :=
    completeAbsorption delta deltaPos deltaComplete
  rcases
      pureWZ2_exists_completeFiber_extremal
        source sourceLossPos sourceFiber twoSourceOne
        deltaLtOne completeScalar.1 completeScalar.2.1
        completeScalar.2.2
    with
    ⟨complete, ⟨completeData⟩⟩
  have densitySeparation :
      Kakeya.realRpowENN delta pruningLoss ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta fiberLoss := by
    apply pure_wz2_pruning_power_bound deltaPos
    exact
      pruningAbsorption delta deltaPos deltaPruning
  rcases
      exists_pureWZ2_perTubeDensityPruningData
        complete densitySeparation
    with
    ⟨pruning⟩
  have sourcePower :
      Real.rpow delta sourceLoss ≤ 1 / 1000 :=
    sourcePowerSmall delta deltaPos deltaSourcePower
  have rhoQuarter :
      completeData.nearby.rho ≤ 1 / 4 :=
    completeData.rho_quarter_of_source_power_small sourcePower
  have massAbsorptionENN :
      (2 : ENNReal) *
          Kakeya.realRpowENN delta baseCellLoss ≤ 1 := by
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by
      norm_num, Kakeya.realRpowENN,
      ← ENNReal.ofReal_mul (by norm_num)]
    simpa using
      ENNReal.ofReal_mono
        (massAbsorption delta deltaPos deltaMass)
  let preselection :=
    pureWZ2CompleteFiberPruningPreselection
      completeData pruning baseCellLoss rhoQuarter
      massAbsorptionENN
  have baseCardLog :
      (Nat.log 2
          (2 * preselection.preSelected.family.card) + 1 : ℝ) ≤
        pureWZ2HeavyCellCardLogConstant *
          (1 + Real.log delta⁻¹) := by
    simpa [preselection,
      pureWZ2CompleteFiberPruningPreselection] using
      pureWZ2CompleteFiberPruning_card_log_bound
        completeData pruning rhoQuarter
  have fineCellDensityAbsorptionENN :
      ENNReal.ofReal (235298 : ℝ) *
          Kakeya.realRpowENN delta
            (geometryPruningLoss - pruningLoss) ≤
        1 := by
    rw [Kakeya.realRpowENN,
      ← ENNReal.ofReal_mul (by norm_num)]
    simpa using
      ENNReal.ofReal_mono
        (fineCellDensityAbsorption
          delta deltaPos deltaFineCellDensity)
  have fineCellDensity :
      Kakeya.realRpowENN delta geometryPruningLoss ≤
        pureWZ2DirectionalHalfDensityFactor *
          Kakeya.realRpowENN delta pruningLoss := by
    simpa [pureWZ2DirectionalHalfDensityFactor] using
      (pure_wz2_density_power_from_absorption
        deltaPos (show (0 : ℝ) < 235298 by norm_num)
        fineCellDensityAbsorptionENN)
  have finiteSelectionAbsorptionENN :
      ENNReal.ofReal (2823576 : ℝ) *
          Kakeya.realRpowENN delta
            (geometryCellLoss - baseCellLoss) ≤
        1 := by
    rw [Kakeya.realRpowENN,
      ← ENNReal.ofReal_mul (by norm_num)]
    simpa using
      ENNReal.ofReal_mono
        (finiteSelectionAbsorption
          delta deltaPos deltaFiniteSelection)
  have finiteSelectionPower :
      Kakeya.realRpowENN delta
          (geometryCellLoss - baseCellLoss) ≤
        pureWZ2DirectionalHalfSelectionFactor := by
    have raw :=
      pure_wz2_density_power_from_absorption
        (delta := delta)
        (sourceEta := geometryCellLoss - baseCellLoss)
        (targetEta := 0)
        deltaPos
        (show (0 : ℝ) < 2823576 by norm_num)
        (by simpa using finiteSelectionAbsorptionENN)
    simpa [pureWZ2DirectionalHalfSelectionFactor,
      Kakeya.realRpowENN] using raw
  rcases
      exists_pureWZ2_directionalHalfPreselectionData
        preselection fineCellDensity
    with
    ⟨directional⟩
  have selectedCardLe :
      (directional.toSpatialCellPreselectionData
          geometryCellLoss fineCellDensity
          finiteSelectionPower).preSelected.family.card ≤
        preselection.preSelected.family.card := by
    change
      directional.selectedPre.family.card ≤
        preselection.preSelected.family.card
    have raw :=
      Fintype.card_le_of_injective
        directional.selectedPre.embedding
        directional.selectedPre.embedding.injective
    simpa using raw
  have selectedLogLe :
      Nat.log 2
          (2 *
            (directional.toSpatialCellPreselectionData
              geometryCellLoss fineCellDensity
              finiteSelectionPower).preSelected.family.card) ≤
        Nat.log 2
          (2 * preselection.preSelected.family.card) := by
    exact
      Nat.log_mono_right
        (Nat.mul_le_mul_left 2 selectedCardLe)
  have geometryCardLog :
      (Nat.log 2
          (2 *
            (directional.toSpatialCellPreselectionData
              geometryCellLoss fineCellDensity
              finiteSelectionPower).preSelected.family.card) + 1 : ℝ) ≤
        pureWZ2HeavyCellCardLogConstant *
          (1 + Real.log delta⁻¹) := by
    calc
      (Nat.log 2
            (2 *
              (directional.toSpatialCellPreselectionData
                geometryCellLoss fineCellDensity
                finiteSelectionPower).preSelected.family.card) : ℝ) +
            1 ≤
          (Nat.log 2
              (2 * preselection.preSelected.family.card) : ℝ) + 1 := by
        gcongr
      _ ≤
          pureWZ2HeavyCellCardLogConstant *
            (1 + Real.log delta⁻¹) :=
        baseCardLog
  let geometry :=
    directional.toGeometrySelectedSpatialCellPreselectionData
      geometryCellLoss fineCellDensity finiteSelectionPower
      geometryCardLog
  let weakenedPruning :=
    PureWZ2DirectionalHalfPreselectionData.toWeakerPruningData
      (source := complete) (pruning := pruning) fineCellDensity
  rcases
      pureWZ2_spatialCellSelectionCertificate_withGeometry_of_preselection
        complete weakenedPruning geometry fiberFinal
        geometryPruningFinal deltaLtOne
        (weightedAbsorption delta deltaPos deltaWeighted)
    with
    ⟨geometrySelection⟩
  let selection := geometrySelection.certificate
  let localized :=
    selection.toLocalizedExtremal fiberFinal.le
  have localizedPerTube :
      ∀ index,
        Kakeya.realRpowENN delta finalLoss *
            volume (localized.family.tube index).carrier ≤
          volume (localized.shading.carrier index) :=
    selection.per_tube_density
  let frameInput :
      PureWZ2RigidCropFrameInput localized.family :=
    {
      centerDirection := geometry.referenceDirection
      centerDirection_unit := geometry.referenceDirection_unit
      commonPoint := geometry.commonPoint
      halfStart := geometry.halfStart
      halfStart_cases := geometry.halfStart_cases
      direction_cone := geometrySelection.direction_cone
      segment_near := geometrySelection.segment_near
    }
  rcases
      exists_pureWZ2RigidCropFrameCertificate_with_window
        frameInput deltaPos deltaRigid
    with
    ⟨rigidCertificate, windowCenterEq⟩
  let finalCertificate := rigidCertificate.toExact
  have localizedAxialWindow :
      ∀ index point,
        point ∈
            finalCertificate.frame ''
              localized.shading.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8 := by
    intro index point pointMem
    rcases pointMem with
      ⟨sourcePoint, sourcePointMem, rfl⟩
    apply rigidCertificate.local_axial_window
    rw [windowCenterEq]
    change
      dist sourcePoint geometry.commonPoint ≤
        Real.sqrt 3 / 32
    rw [geometry.commonPoint_eq]
    exact
      (by
        simpa [pureWZ2RigidCropGridScale] using
          pureWZ2_rigidCropCell_point_dist_center_le
            (geometrySelection.localShading_subset_cell
              index sourcePointMem))
  have topCWA :
      WZ2PaperConvexWolffBound
        (pureWZ2RigidImageFamily
          finalCertificate.frame localized.family)
        (Kakeya.realRpowENN delta (-outputLoss)) := by
    apply
      pureWZ2RigidImageFamily_croppedTopCWA_of_axisBox
        finalCertificate.frame deltaPos.le
        finalLossPos finalOne deltaLeOne
        localized.extremal.nonempty
        localized.extremal.cwa_nearby_scales
        finalCertificate.line_class
        finalCertificate.axisBox
    intro rho rhoPos deltaRho rhoOne requestedRho
    exact
      topAbsorption delta rho deltaPos deltaTop
        rhoPos deltaRho rhoOne requestedRho
  let structural :=
    pureWZ2ExactRigidCropStructuralData
      source localized finalCertificate
        finalHalfOutput finalOutput
        (pureWZ2_per_tube_density_half
          (densityLoss := finalLoss)
          localized.shading localizedPerTube)
        localizedAxialWindow
        topCWA
  have cropScalar :=
    cropAbsorption delta deltaPos deltaCrop
  have scalarConsequences :=
    pureWZ2ExactRigidCropScalarConsequences
      (sigma := sigma) deltaPos cropScalar
  have deltaTriple : 3 * delta ≤ 1 := by
    linarith
  let quantitative :=
    pureWZ2ExactRigidCanonicalCropQuantitativeBounds
      source localized finalCertificate topCWA
      finalHalfOutput finalOutput deltaTriple localizedPerTube
      localizedAxialWindow
      scalarConsequences.1 scalarConsequences.2
  let leaves := structural.toSourceLeaves quantitative.toCanonicalScalars
  have localizedAxialBound :
      ∀ index point,
        point ∈ leaves.frame '' leaves.ordinaryRefined.carrier index →
          |point (2 : Fin 3)| ≤ Real.sqrt 3 / 16 + 4 * delta := by
    intro index point pointMem
    rcases pointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
    apply rigidCertificate.local_axial_bound
    rw [windowCenterEq]
    change dist sourcePoint geometry.commonPoint ≤ Real.sqrt 3 / 32
    rw [geometry.commonPoint_eq]
    simpa [pureWZ2RigidCropGridScale] using
      pureWZ2_rigidCropCell_point_dist_center_le
        (geometrySelection.localShading_subset_cell index sourcePointMem)
  exact ⟨localized, ⟨{
    leaves := leaves
    ordinary_axial_bound := localizedAxialBound
  }⟩⟩

/-- Compatibility projection which forgets only the quantitative axial
slack. -/
theorem pureWZ2_completeFiber_normalization_exact :
    PureWZ2CompleteFiberNormalizationAt 0 := by
  intro sigma outputLoss outputLossPos
  rcases pureWZ2_completeFiber_normalization_exact_with_axial_bound
      sigma outputLoss outputLossPos with
    ⟨sourceLoss, delta₁, sourceLossPos, finalLossPos, finalHalfOutput,
      delta₁Pos, _delta₁Small, produce⟩
  refine ⟨sourceLoss, delta₁, sourceLossPos, finalLossPos, finalHalfOutput,
    delta₁Pos, ?_⟩
  intro delta deltaPos deltaLe source
  rcases produce delta deltaPos deltaLe source with ⟨localized, ⟨data⟩⟩
  exact ⟨localized, ⟨data.leaves⟩⟩

/-- The exact-loss theorem implies the legacy source-derived normalization leaf. -/
theorem
    pureWZ2_cropped_critical_normalization_sourceDerivedLeaf_completeFiber :
    PureWZ2CroppedCriticalNormalizationSourceDerivedLeafAt 0 := by
  intro sigma outputLoss outputLossPos
  rcases
      pureWZ2_completeFiber_normalization_exact
        sigma outputLoss outputLossPos
    with
    ⟨sourceLoss, delta₁, sourceLossPos, finalLossPos,
      finalHalfOutput, delta₁Pos, produce⟩
  exact
    ⟨sourceLoss,
      pureWZ2CompleteNormalizationFinalLoss outputLoss,
      delta₁, sourceLossPos, finalLossPos, finalHalfOutput,
      delta₁Pos, produce⟩

/-- The frozen critical normalization statement at exponent zero. -/
theorem pureWZ2_cropped_critical_normalization_completeFiber :
    PureWZ2CroppedCriticalNormalizationAt 0 :=
  pureWZ2_cropped_critical_normalization_of_sourceDerivedLeaf
    0
    pureWZ2_cropped_critical_normalization_sourceDerivedLeaf_completeFiber

end Kakeya.Assouad

end
