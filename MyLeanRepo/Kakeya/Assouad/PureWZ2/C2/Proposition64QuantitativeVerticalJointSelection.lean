import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalNearbySchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64FurtherSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64P7ScaleSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection

/-!
# Joint multiscale selection for quantitative vertical rediscretization

The first paper-ED output is only an ambient weighted selection.  A second,
simultaneous finite-scale selection is made inside that exact family.  Its
mass loss is charged through `restrictFurther`; hence the family carrying the
uniform covers is definitionally the final canonical ED family.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)

private noncomputable abbrev initialED :=
  quantitativeVerticalPaperED quantitativeOutput geometry frostman

/-- The family-free finite scale grid.  Its window is exactly the critical
floor structural-loss window; it does not use or assume nearby CWA. -/
noncomputable def quantitativeVerticalRequestedScaleSchedule :=
  quantitativeVerticalRequestedScaleScheduleOfLoss
    quantitativeOutput geometry floor.structuralLoss floor.structuralLoss_pos

/-- The sole geometric leaf left after constructing the finite scale grid:
literal covers of the exact initial ED family at those predetermined scales,
plus parent packing.  It contains no selection, uniformity, or nearby CWA. -/
structure QuantitativeVerticalAmbientStrictCoverReceipt where
  coarse :
    ∀ coordinate :
        Fin (quantitativeVerticalRequestedScaleSchedule
          quantitativeOutput geometry floor).levelCount,
      Kakeya.Streamlined.TubeFamily
        ((quantitativeVerticalRequestedScaleSchedule
          quantitativeOutput geometry floor).requested coordinate).1
  cover :
    ∀ coordinate,
      WZ2PaperPurePartitioningCover
        (initialED quantitativeOutput geometry frostman).subfamily.family
        (coarse coordinate)
  parentCountConstant :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount → ENNReal
  parentCount :
    ∀ coordinate,
      (coarse coordinate).enncard ≤
        parentCountConstant coordinate *
          (Kakeya.realRpowENN
            ((quantitativeVerticalRequestedScaleSchedule
              quantitativeOutput geometry floor).requested coordinate).1 2)⁻¹

/-- Non-conclusion input to the simultaneous selector: finite literal strict
covers of the initial ED family, their parent packing, and scale rounding. -/
structure QuantitativeVerticalJointSelectorInput where
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  actualScale : Fin coordinateCount → ℝ
  actualScale_pos : ∀ coordinate, 0 < actualScale coordinate
  coarse :
    ∀ coordinate,
      Kakeya.Streamlined.TubeFamily (actualScale coordinate)
  cover :
    ∀ coordinate,
      WZ2PaperPurePartitioningCover
        (initialED quantitativeOutput geometry frostman).subfamily.family
        (coarse coordinate)
  parentCountConstant : Fin coordinateCount → ENNReal
  parentCount :
    ∀ coordinate,
      (coarse coordinate).enncard ≤
        parentCountConstant coordinate *
          (Kakeya.realRpowENN (actualScale coordinate) 2)⁻¹
  rounding :
    ∀ requested : WZ2PaperRequestedScale
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta),
      ∃ coordinate : Fin coordinateCount,
        requested.1 ≤ actualScale coordinate ∧
          ENNReal.ofReal (actualScale coordinate) <
            Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                (-floor.structuralLoss) *
              ENNReal.ofReal requested.1

/-- Raw output of the one simultaneous finite-scale weighted selection.

This stores the selected indices and their literal strict covers, not a
nearby-CWA or a prepackaged final uniformity receipt. -/
structure QuantitativeVerticalJointFiniteSelectionReceipt where
  selected : Kakeya.Streamlined.TubeSubfamily
    (initialED quantitativeOutput geometry frostman).subfamily.family
  selected_nonempty : selected.family.Nonempty
  retentionConstant : ENNReal
  retentionConstant_ne_top : retentionConstant ≠ ⊤
  retained_mass :
    (initialED quantitativeOutput geometry frostman).finalShading.mass ≤
      retentionConstant *
        (restrictPaperShading selected
          (initialED quantitativeOutput geometry frostman).finalShading).mass
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  actualScale : Fin coordinateCount → ℝ
  actualScale_pos : ∀ coordinate, 0 < actualScale coordinate
  coarse :
    ∀ coordinate,
      Kakeya.Streamlined.TubeFamily (actualScale coordinate)
  cover :
    ∀ coordinate,
      WZ2PaperPurePartitioningCover selected.family (coarse coordinate)
  degreeConstant : Fin coordinateCount → ENNReal
  fullFiberUniform :
    ∀ coordinate,
      WZ2PaperPureFullFibersAreCUniform selected.family
        (coarse coordinate) (degreeConstant coordinate)
  parentCountConstant : Fin coordinateCount → ENNReal
  parentCount :
    ∀ coordinate,
      (coarse coordinate).enncard ≤
        parentCountConstant coordinate *
          (Kakeya.realRpowENN (actualScale coordinate) 2)⁻¹
  rounding :
    ∀ requested : WZ2PaperRequestedScale
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta),
      ∃ coordinate : Fin coordinateCount,
        requested.1 ≤ actualScale coordinate ∧
          ENNReal.ofReal (actualScale coordinate) <
            Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                (-floor.structuralLoss) *
              ENNReal.ofReal requested.1

namespace QuantitativeVerticalJointFiniteSelectionReceipt

/-- Assemble the selector input from the fixed family-free scale grid and
the exact same-family ambient cover leaf. -/
noncomputable def selectorInputOfAmbientCovers
    (ambient : QuantitativeVerticalAmbientStrictCoverReceipt
      quantitativeOutput geometry frostman floor) :
    QuantitativeVerticalJointSelectorInput
      quantitativeOutput geometry frostman floor where
  coordinateCount :=
    (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount
  coordinateCount_pos :=
    (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount_pos
  actualScale := fun coordinate =>
    ((quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).requested coordinate).1
  actualScale_pos := fun coordinate =>
    geometry.scales.finalDelta_pos.trans_le
      ((quantitativeVerticalRequestedScaleSchedule
        quantitativeOutput geometry floor).requested coordinate).2.1
  coarse := ambient.coarse
  cover := ambient.cover
  parentCountConstant := ambient.parentCountConstant
  parentCount := ambient.parentCount
  rounding := by
    intro requested
    rcases (quantitativeVerticalRequestedScaleSchedule
        quantitativeOutput geometry floor).rounding requested with
      ⟨coordinate, hrequested, hwindow⟩
    refine ⟨coordinate, hrequested, ?_⟩
    simpa [quantitativeVerticalRequestedScaleSchedule,
      Kakeya.realRpowENN] using hwindow

/-- Perform one weighted simultaneous degree regularization on all supplied
strict covers.  Colors are unnecessary here because the input covers are
already strict; no coordinate is selected sequentially. -/
theorem select
    (input : QuantitativeVerticalJointSelectorInput
      quantitativeOutput geometry frostman floor) :
    Nonempty (QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) := by
  let ed := initialED quantitativeOutput geometry frostman
  let weight : Fin ed.subfamily.family.card → ENNReal :=
    fun index => MeasureTheory.volume (ed.finalShading.carrier index)
  let Vertex : Fin input.coordinateCount → Type :=
    fun coordinate => Fin (input.coarse coordinate).card
  let parent : ∀ coordinate, Fin ed.subfamily.family.card → Vertex coordinate :=
    fun coordinate => (input.cover coordinate).parent
  let regularized := Classical.choice <|
    wz2_finite_weighted_degree_selection input.coordinateCount
      Vertex parent weight input.coordinateCount_pos
  let selectedIndices := regularized.selected
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      ed.subfamily.family selectedIndices
  have selectedMem :
      ∀ index : Fin selected.family.card,
        selected.embedding index ∈ selectedIndices := by
    intro index
    exact Finset.orderEmbOfFin_mem selectedIndices rfl index
  have totalWeightPos : 0 < ∑ index, weight index := by
    change 0 < ed.finalShading.mass
    have hright : 0 <
        (quantitativeVerticalPaperEDLoss quantitativeOutput geometry + 1) *
          ed.finalShading.mass :=
      geometry.cleanup_finalShading_mass_pos.trans_le ed.mass_retention
    by_contra hzero
    rw [not_lt, nonpos_iff_eq_zero] at hzero
    simp [hzero] at hright
  have selectedNonempty : selected.family.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selectedIndices = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp <| by
        intro hnonempty
        exact hempty hnonempty.card_pos
    have hselectedSum : (∑ index ∈ selectedIndices, weight index) = 0 := by
      rw [hselectedEmpty]
      simp
    have htotalZero : (∑ index, weight index) ≤ 0 := by
      have hretained := regularized.retained_weight
      rw [hselectedSum, mul_zero] at hretained
      exact hretained
    exact (not_le_of_gt totalWeightPos) htotalZero
  have selectedFilterCard :
      ∀ (coordinate : Fin input.coordinateCount)
        (vertex : Vertex coordinate),
        (selectedIndices.filter fun index =>
          parent coordinate index = vertex).card =
        ((Finset.univ : Finset (Fin selected.family.card)).filter fun index =>
          parent coordinate (selected.embedding index) = vertex).card := by
    intro coordinate vertex
    let localIndices := (Finset.univ :
      Finset (Fin selected.family.card)).filter fun index =>
        parent coordinate (selected.embedding index) = vertex
    have himage :
        Finset.image selected.embedding localIndices =
          selectedIndices.filter fun index =>
            parent coordinate index = vertex := by
      ext index
      simp only [Finset.mem_image, localIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨source, hparent, rfl⟩
        exact ⟨selectedMem source, hparent⟩
      · rintro ⟨hselected, hparent⟩
        let source : Fin selected.family.card :=
          (selectedIndices.orderIsoOfFin rfl).symm ⟨index, hselected⟩
        have hembedding : selected.embedding source = index :=
          congrArg Subtype.val
            ((selectedIndices.orderIsoOfFin rfl).apply_symm_apply
              ⟨index, hselected⟩)
        exact ⟨source, by rwa [hembedding], hembedding⟩
    calc
      (selectedIndices.filter fun index =>
          parent coordinate index = vertex).card =
          (Finset.image selected.embedding localIndices).card :=
        congrArg Finset.card himage.symm
      _ = localIndices.card :=
        Finset.card_image_of_injective _ selected.embedding.injective
  let selectedPure : WZ2PaperPureTubeSubfamily ed.subfamily.family :=
    { family := selected.family
      embedding := selected.embedding
      tube_eq := selected.tube_eq }
  let selectedCoarse : ∀ coordinate,
      WZ2PaperPureTubeSubfamily (input.coarse coordinate) :=
    fun coordinate =>
      (input.cover coordinate).hitParentSubfamily selectedPure
  have selectedUniform :
      ∀ coordinate,
        WZ2PaperPureFullFibersAreCUniform selected.family
          (selectedCoarse coordinate).family
          (16 * (input.coordinateCount : ENNReal) *
            (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^
              input.coordinateCount) := by
    intro coordinate
    apply (input.cover coordinate)
      |>.restrictToHitParents_fullFiber_uniform_of_subfamily
        (input.actualScale_pos coordinate).le selectedPure
        (16 * (input.coordinateCount : ENNReal) *
          (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^
            input.coordinateCount)
    intro first second hfirst hsecond
    rw [← selectedFilterCard coordinate, ← selectedFilterCard coordinate]
    simpa only [selectedIndices, Fintype.card_fin] using
      regularized.degree_uniform coordinate
        first second (by
          rw [selectedFilterCard coordinate]
          exact hfirst)
        (by
          rw [selectedFilterCard coordinate]
          exact hsecond)
  let retentionConstant :=
    8 * (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^
      (input.coordinateCount + 1)
  have retainedWeight :
      (∑ index, weight index) ≤
        retentionConstant * ∑ index ∈ selectedIndices, weight index := by
    simpa only [retentionConstant, weight, selectedIndices,
      Fintype.card_fin] using regularized.retained_weight
  have retainedMass :
      ed.finalShading.mass ≤ retentionConstant *
        (restrictPaperShading selected ed.finalShading).mass := by
    let equivalence := selectedIndices.orderIsoOfFin rfl
    have hsum :
        (∑ index : Fin selected.family.card,
          weight (selected.embedding index)) =
          ∑ index ∈ selectedIndices, weight index := by
      exact
        (Fintype.sum_equiv equivalence.toEquiv
          (fun index : Fin selected.family.card =>
            weight (selected.embedding index))
          (fun index : selectedIndices => weight index.1)
          (fun _ => rfl)).trans
          (Finset.sum_coe_sort selectedIndices weight)
    calc
      ed.finalShading.mass = ∑ index, weight index := rfl
      _ ≤ retentionConstant * ∑ index ∈ selectedIndices, weight index :=
        retainedWeight
      _ = retentionConstant *
          (restrictPaperShading selected ed.finalShading).mass := by
        apply congrArg (fun mass => retentionConstant * mass)
        exact hsum.symm.trans
          (restrictPaperShading_mass selected ed.finalShading).symm
  refine ⟨{
    selected := selected
    selected_nonempty := selectedNonempty
    retentionConstant := retentionConstant
    retentionConstant_ne_top := by
      apply ENNReal.mul_ne_top
      · norm_num
      · simp
    retained_mass := retainedMass
    coordinateCount := input.coordinateCount
    coordinateCount_pos := input.coordinateCount_pos
    actualScale := input.actualScale
    actualScale_pos := input.actualScale_pos
    coarse := fun coordinate => (selectedCoarse coordinate).family
    cover := fun coordinate =>
      (input.cover coordinate).restrictToHitParents selectedPure
    degreeConstant := fun _ =>
      16 * (input.coordinateCount : ENNReal) *
        (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^
          input.coordinateCount
    fullFiberUniform := selectedUniform
    parentCountConstant := input.parentCountConstant
    parentCount := ?_
    rounding := input.rounding
  }⟩
  intro coordinate
  have hcard :
      (selectedCoarse coordinate).family.card ≤
        (input.coarse coordinate).card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        (selectedCoarse coordinate).embedding
        (selectedCoarse coordinate).embedding.injective
  calc
    (selectedCoarse coordinate).family.enncard ≤
        (input.coarse coordinate).enncard := by
      simp only [Kakeya.Streamlined.TubeFamily.enncard]
      exact_mod_cast hcard
    _ ≤ _ := input.parentCount coordinate

/-- Active same-witness route: the caller supplies only the exact geometric
ambient-cover leaf, while this module fixes the scales and performs the
weighted simultaneous selection. -/
theorem selectOfAmbientCovers
    (ambient : QuantitativeVerticalAmbientStrictCoverReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) :=
  select quantitativeOutput geometry frostman floor
    (selectorInputOfAmbientCovers
      quantitativeOutput geometry frostman floor ambient)

/-- The final ED loss includes both the initial Frostman/ED loss and the
simultaneous multiscale-selection retention factor. -/
noncomputable def finalLoss
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) : ENNReal :=
  (quantitativeVerticalPaperEDLoss quantitativeOutput geometry + 1) *
    joint.retentionConstant

/-- Re-freeze the further selected family as the final canonical paper ED. -/
noncomputable def finalED
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) :
    PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading joint.finalLoss :=
  (initialED quantitativeOutput geometry frostman).restrictFurther
    joint.selected joint.retained_mass

/-- The R4 top-level constant evaluated at the true final ED loss. -/
noncomputable def finalTopConstant
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) : ENNReal :=
  ENNReal.ofReal
        (quantitativeOutput.normalized.prepared.normalization *
          quantitativeOutput.normalized.prepared.slab.halfHeight /
            pureWZ2Proposition64Lemma35Scale ^ 3) *
    ENNReal.ofReal
        (27 *
          (2 * pureWZ2Proposition64TopCarrierFactor
            (quantitativeOutput := quantitativeOutput) - 1) ^ 3) *
    ((pureWZ2Proposition64TopWeight
          (quantitativeOutput := quantitativeOutput))⁻¹ *
        pureWZ2Proposition64TopRetention
          (sourceDelta := sourceDelta) joint.finalLoss) *
      Kakeya.realRpowENN sourceDelta
        (-quantitativeOutput.normalized.inputLoss)

/-- Scalar tail evaluated on the true post-selection ED loss. -/
structure ScalarReceipt
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) : Prop where
  finalDelta_le_floor :
    pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ floor.delta₀
  density_absorption :
    (147 * (joint.finalLoss + 1)) *
          (Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                floor.structuralLoss *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)) ≤
      pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        Kakeya.realRpowENN sourceDelta 2
  cwa_absorption :
    4 * Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-floor.structuralLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)
  volume_absorption :
    pureWZ2Proposition64VolumeCoefficient quantitativeOutput.normalized *
        Kakeya.realRpowENN sourceDelta
          (sigma - quantitativeOutput.normalized.inputLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (sigma - outputLoss)
  local_constant_absorption :
    192 * Kakeya.realRpowENN sourceDelta (-workLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)
  global_constant_absorption :
    7077888 * (24000 * Kakeya.realRpowENN sourceDelta (-workLoss)) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)

/-- Family-free absorption of every finite-scale degree/packing cost. -/
structure ScheduleAbsorptionReceipt
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) : Prop where
  scaleAbsorption :
    ∀ coordinate,
      let bodyConstant :=
        joint.degreeConstant coordinate *
          joint.parentCountConstant coordinate *
          (108 * ENNReal.ofReal
            (1 + 2 * joint.actualScale coordinate)) *
          212776173 * joint.finalTopConstant
      max (joint.degreeConstant coordinate) bodyConstant ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-floor.structuralLoss)

theorem finalLoss_ne_top
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) :
    joint.finalLoss ≠ ⊤ := by
  unfold finalLoss
  exact ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr
      ⟨quantitativeVerticalPaperEDLoss_ne_top quantitativeOutput geometry,
        by norm_num⟩)
    joint.retentionConstant_ne_top

/-- The final canonical ED family receives nearby CWA from the literal covers
created by the same joint selection. -/
theorem nearby
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor)
    (absorption : ScheduleAbsorptionReceipt
      quantitativeOutput geometry frostman floor joint) :
    WZ2PaperPureCWAAtNearbyScales joint.finalED.subfamily.family
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-floor.structuralLoss)) := by
  change WZ2PaperPureCWAAtNearbyScales joint.selected.family
    (Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      (-floor.structuralLoss))
  let ed := joint.finalED
  let outputConstant := Kakeya.realRpowENN
    (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
    (-floor.structuralLoss)
  have topLevel :
      WZ2PaperConvexWolffBound joint.selected.family
        joint.finalTopConstant := by
    change WZ2PaperConvexWolffBound ed.subfamily.family _
    simpa [finalTopConstant, mul_assoc] using
      (paperED_topLevelCWA
        (quantitativeOutput := quantitativeOutput) geometry ed)
  have finalLine : WZ1PaperIsLineClass joint.selected.family := by
    change WZ1PaperIsLineClass ed.subfamily.family
    exact geometry.paperED_lineClass ed
  have finalLocal :
      ∀ index, ‖wz2PaperTubeMidpoint
        (joint.selected.family.tube index)‖ ≤ 3 := by
    intro index
    have hcentered :
        wz2PaperTubeMidpoint (joint.selected.family.tube index) =
          wz1TubeAxisZeroPoint (joint.selected.family.tube index) := by
      change wz2PaperTubeMidpoint (ed.subfamily.family.tube index) =
        wz1TubeAxisZeroPoint (ed.subfamily.family.tube index)
      have hvertical := (geometry.paperED_lineClass ed index).vertical
      rw [ed.tube_provenance index] at hvertical
      rw [ed.tube_provenance index]
      apply pureWZ2Proposition64IsotropicRebasedPaperTube_midpoint
      simpa [pureWZ2Proposition64IsotropicPaperFamily,
        pureWZ2Proposition64IsotropicRebasedPaperTube,
        pureWZ2Proposition64IsotropicPaperTube] using hvertical
    rw [hcentered]
    have hzeroTwo :
        wz1TubeAxisZeroPoint (joint.selected.family.tube index) (2 : Fin 3) = 0 :=
      wz1TubeAxisZeroPoint_coord_two _ (finalLine index).vertical
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
    constructor
    · positivity
    · simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, hzeroTwo]
      have hzero := sq_le_sq₀
        (abs_nonneg (wz1TubeAxisZeroPoint
          (joint.selected.family.tube index) 0))
        (by norm_num : 0 ≤ (1 / 3 : ℝ)) |>.2 (finalLine index).2.1
      have hone := sq_le_sq₀
        (abs_nonneg (wz1TubeAxisZeroPoint
          (joint.selected.family.tube index) 1))
        (by norm_num : 0 ≤ (1 / 3 : ℝ)) |>.2 (finalLine index).2.2
      rw [sq_abs] at hzero hone
      nlinarith
  have outputOne : 1 ≤ outputConstant := by
    change 1 ≤ Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      (-floor.structuralLoss)
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      geometry.scales.finalDelta_pos
      (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      (by linarith [floor.structuralLoss_pos])
  have outputTop : outputConstant ≠ ⊤ := by
    simp [outputConstant, Kakeya.realRpowENN]
  apply pureWZ2_nearby_from_finite_witnesses
    geometry.scales.finalDelta_pos outputOne outputTop
    (by
      change WZ2PaperOrdinaryIsEssentiallyDistinct ed.subfamily.family
      exact ed.essentially_distinct)
    joint.coordinateCount joint.coordinateCount_pos
    (fun coordinate => ⟨joint.actualScale coordinate, ?_⟩)
    joint.rounding
  let rho := joint.actualScale coordinate
  let coarse := joint.coarse coordinate
  let bodyConstant :=
    joint.degreeConstant coordinate *
      joint.parentCountConstant coordinate *
      (108 * ENNReal.ofReal (1 + 2 * rho)) *
      212776173 * joint.finalTopConstant
  have habsorb := absorption.scaleAbsorption coordinate
  have degreeLe :
      joint.degreeConstant coordinate ≤ outputConstant :=
    (le_max_left _ bodyConstant).trans habsorb
  refine {
    delta_pos := geometry.scales.finalDelta_pos
    rho_pos := joint.actualScale_pos coordinate
    coarse := coarse
    cover := joint.cover coordinate
    full_fiber_uniform := fun first second =>
      (joint.fullFiberUniform coordinate first second).trans (by
        gcongr)
    rescaledFiber := ?_
  }
  intro parent
  apply pureWZ2Proposition64_pure_fullFiber_cwa_of_topLevel
    (joint.cover coordinate) joint.selected_nonempty
    (joint.actualScale_pos coordinate) topLevel
    (joint.fullFiberUniform coordinate) (joint.parentCount coordinate)
    (fun coarseParent targetSet => by
      simpa [rho, mul_assoc, mul_left_comm, mul_comm] using
        pureWZ2Proposition64_outerJohn_inverse_volume_le_general
          (joint.actualScale_pos coordinate) (coarse.tube coarseParent)
          (WZ2PaperAssouadUnitRescalingData.ofTube
            (coarse.tube coarseParent) (joint.actualScale_pos coordinate))
          targetSet)
    (fun _coarseParent sourceSet hsourceConvex => by
      rcases pureWZ2Proposition64_localized_common_cropped_envelope
          geometry.scales.finalDelta_pos
          (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
          finalLine finalLocal sourceSet hsourceConvex with
        ⟨paperSet, hpaperConvex, hpaperVolume, hpaperCarrier⟩
      exact ⟨paperSet, hpaperConvex, hpaperVolume,
        fun source _ hcarrier => hpaperCarrier source hcarrier⟩)
    ((le_max_right _ bodyConstant).trans habsorb) parent

/-- Complete wiring from one joint-selection witness to vertical
rediscretization on its re-frozen final canonical ED family. -/
theorem verticalRediscretization
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor)
    (scheduleAbsorption : ScheduleAbsorptionReceipt
      quantitativeOutput geometry frostman floor joint)
    (scalars : ScalarReceipt
      quantitativeOutput geometry frostman floor joint) :
    Nonempty (PureWZ2VerticalRediscretizationData
      quantitativeOutput.normalized.prepared.normalized
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss) := by
  let ed := joint.finalED
  apply geometry.assembleVerticalRediscretizationOfCriticalFloor
    quantitativeOutput ed floor
  exact {
    nearby := nearby quantitativeOutput geometry frostman floor
      joint scheduleAbsorption
    finalDelta_le_floor := scalars.finalDelta_le_floor
    ed_loss_ne_top := joint.finalLoss_ne_top
    density_absorption := scalars.density_absorption
    cwa_absorption := scalars.cwa_absorption
    volume_absorption := scalars.volume_absorption
    local_constant_absorption := scalars.local_constant_absorption
    global_constant_absorption := scalars.global_constant_absorption
  }

end QuantitativeVerticalJointFiniteSelectionReceipt

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
