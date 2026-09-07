import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreePrefix
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PrebalanceParentDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalParentCWA
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
/-!
# Proposition 6.2 terminal-parent CWA bound

This module isolates the cardinality ledger behind the parent-family CWA
constant in the fourth paper lemma.  The ambient-to-selected parent ratio is
obtained from aggregate density, the weighted parent selection, and complete
full-fiber uniformity.  No coarse packing estimate is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem prop62ParentCWA_card_relation_eq_sum_left
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β)
    (relation : α → β → Prop) [DecidableRel relation] :
    ((left ×ˢ right).filter fun pair =>
        relation pair.1 pair.2).card =
      ∑ first ∈ left,
        (right.filter fun second =>
          relation first second).card := by
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [Finset.card_filter]

private theorem prop62ParentCWA_card_relation_eq_sum_right
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β)
    (relation : α → β → Prop) [DecidableRel relation] :
    ((left ×ˢ right).filter fun pair =>
        relation pair.1 pair.2).card =
      ∑ second ∈ right,
        (left.filter fun first =>
          relation first second).card := by
  rw [Finset.card_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  simp_rw [Finset.card_filter]

/--
Exact non-asymptotic parent-cardinality comparison.

The proof chooses one selected parent.  Uniformity compares its complete fiber
with every ambient fiber, while weighted retention compares the total mass with
the selected parent weights.  The common selected weight is bounded by the
chosen complete-fiber size, after which the positive finite fiber-volume factor
cancels.
-/
theorem pureWZ2_prop62_parent_card_ratio_of_weighted_retention
    {Parent : Type*}
    [Fintype Parent] [DecidableEq Parent]
    (selectedParents : Finset Parent)
    (selectedParentsNonempty : selectedParents.Nonempty)
    (fiberCount parentWeight : Parent → ENNReal)
    (fineCard fineVolume totalMass densityConstant
      parentConstant selectionLoss tubeMassConstant : ENNReal)
    (fiberSum :
      (∑ parent : Parent, fiberCount parent) = fineCard)
    (fullFiberUniform :
      ∀ first second,
        fiberCount first ≤ parentConstant * fiberCount second)
    (density :
      densityConstant * fineCard * fineVolume ≤ totalMass)
    (weightedRetention :
      totalMass ≤
        selectionLoss *
          ∑ parent ∈ selectedParents, parentWeight parent)
    (selectedWeightComparable :
      ∀ first ∈ selectedParents, ∀ second ∈ selectedParents,
        parentWeight first ≤ 2 * parentWeight second)
    (selectedWeightUpper :
      ∀ parent ∈ selectedParents,
        parentWeight parent ≤
          fiberCount parent * tubeMassConstant * fineVolume)
    (selectedFiberPos :
      ∀ parent ∈ selectedParents, 0 < fiberCount parent)
    (selectedFiberFinite :
      ∀ parent ∈ selectedParents, fiberCount parent ≠ ⊤)
    (fineVolumePos : 0 < fineVolume)
    (fineVolumeFinite : fineVolume ≠ ⊤) :
    densityConstant * (Fintype.card Parent : ENNReal) ≤
      (2 * selectionLoss * parentConstant * tubeMassConstant) *
        (selectedParents.card : ENNReal) := by
  let anchor : Parent := Classical.choose selectedParentsNonempty
  have anchorMem : anchor ∈ selectedParents :=
    Classical.choose_spec selectedParentsNonempty
  have anchorFiberPos : 0 < fiberCount anchor :=
    selectedFiberPos anchor anchorMem
  have anchorFiberFinite : fiberCount anchor ≠ ⊤ :=
    selectedFiberFinite anchor anchorMem
  have ambientFiberComparison :
      (Fintype.card Parent : ENNReal) * fiberCount anchor ≤
        parentConstant * fineCard := by
    calc
      (Fintype.card Parent : ENNReal) * fiberCount anchor =
          ∑ _parent : Parent, fiberCount anchor := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤
          ∑ parent : Parent,
            parentConstant * fiberCount parent := by
        exact Finset.sum_le_sum fun parent _ =>
          fullFiberUniform anchor parent
      _ = parentConstant * fineCard := by
        rw [← Finset.mul_sum, fiberSum]
  have selectedWeightSum :
      (∑ parent ∈ selectedParents, parentWeight parent) ≤
        (selectedParents.card : ENNReal) *
          (2 * parentWeight anchor) := by
    calc
      (∑ parent ∈ selectedParents, parentWeight parent) ≤
          ∑ _parent ∈ selectedParents,
            2 * parentWeight anchor := by
        exact Finset.sum_le_sum fun parent parentMem =>
          selectedWeightComparable parent parentMem anchor anchorMem
      _ =
          (selectedParents.card : ENNReal) *
            (2 * parentWeight anchor) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have withCancellation :
      (densityConstant * (Fintype.card Parent : ENNReal)) *
          (fiberCount anchor * fineVolume) ≤
        ((2 * selectionLoss * parentConstant * tubeMassConstant) *
          (selectedParents.card : ENNReal)) *
            (fiberCount anchor * fineVolume) := by
    calc
      (densityConstant * (Fintype.card Parent : ENNReal)) *
            (fiberCount anchor * fineVolume) =
          densityConstant *
            ((Fintype.card Parent : ENNReal) * fiberCount anchor) *
              fineVolume := by ring
      _ ≤
          densityConstant * (parentConstant * fineCard) *
            fineVolume := by
        gcongr
      _ =
          parentConstant * (densityConstant * fineCard * fineVolume) := by
        ring
      _ ≤ parentConstant * totalMass := by
        gcongr
      _ ≤
          parentConstant *
            (selectionLoss *
              ∑ parent ∈ selectedParents, parentWeight parent) := by
        gcongr
      _ ≤
          parentConstant *
            (selectionLoss *
              ((selectedParents.card : ENNReal) *
                (2 * parentWeight anchor))) := by
        gcongr
      _ ≤
          parentConstant *
            (selectionLoss *
              ((selectedParents.card : ENNReal) *
                (2 *
                  (fiberCount anchor * tubeMassConstant * fineVolume)))) := by
        gcongr
        exact selectedWeightUpper anchor anchorMem
      _ =
          ((2 * selectionLoss * parentConstant * tubeMassConstant) *
            (selectedParents.card : ENNReal)) *
              (fiberCount anchor * fineVolume) := by
        ring
  exact
    (ENNReal.mul_le_mul_iff_left
      (ENNReal.mul_pos anchorFiberPos.ne' fineVolumePos.ne').ne'
      (ENNReal.mul_ne_top anchorFiberFinite fineVolumeFinite)).mp <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using withCancellation

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}

/-- The three weighted dyadic losses used before the parent-tree cleanup. -/
def terminalParentSelectionLoss : ENNReal :=
  (multiplicity.binCount : ENNReal) *
    parentClass.weightBinCount *
    parentClass.fiberBinCount

/--
The packet-cell weight of one selected parent is bounded by the total volume
of all complete-fiber tube carriers.  This is a local incidence double count:
no cardinality packing estimate enters.
-/
theorem selectedParentMass_le_completeFiberTubeMass
    (deltaLeOneTwentyFour : delta ≤ 1 / 24)
    (parent : Fin coarse.card)
    (parentMem : parent ∈ parentClass.selectedParents) :
    input.parentClassMass multiplicity parent ≤
      (input.parentFiberCard parent : ENNReal) *
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 := by
  let pairs := input.selectedPairsAt multiplicity parent
  let fiber := wz2PaperFullFiberIndices fine coarse parent
  let relation :
      (Fin coarse.card × WZ2PaperCellIndex) →
        Fin fine.card → Prop :=
    fun pair source =>
      source ∈ input.packetCellSources pair.1 pair.2
  have packetFiber :
      ∀ pair ∈ pairs,
        fiber.filter (relation pair) =
          input.packetCellSources pair.1 pair.2 := by
    intro pair pairMem
    have pairParent : pair.1 = parent :=
      (Finset.mem_filter.mp pairMem).2
    ext source
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_sourceFiber, sourcePacket⟩
      exact sourcePacket
    · intro sourcePacket
      refine ⟨?_, sourcePacket⟩
      have sourceFiber :
          source ∈ wz2PaperFullFiberIndices fine coarse pair.1 :=
        (input.mem_packetCellSources_iff pair.1 pair.2 source).mp
          sourcePacket |>.2.1
      simpa only [fiber, pairParent] using sourceFiber
  have selectedRelationSubset :
      ∀ source,
        pairs.filter (fun pair => relation pair source) ⊆
          input.positivePairs.filter fun pair =>
            source ∈ input.packetCellSources pair.1 pair.2 := by
    intro source pair pairMem
    have pairData := Finset.mem_filter.mp pairMem
    apply Finset.mem_filter.mpr
    refine ⟨?_, pairData.2⟩
    exact multiplicity.selectedPairs_subset
      (Finset.mem_filter.mp pairData.1).1
  have countBound :
      input.parentIncidenceWeight multiplicity parent ≤
        ∑ source ∈ fiber,
          (input.sourceCellsForSource source).card := by
    calc
      input.parentIncidenceWeight multiplicity parent =
          ∑ pair ∈ pairs,
            (fiber.filter fun source =>
              relation pair source).card := by
        unfold parentIncidenceWeight
        apply Finset.sum_congr rfl
        intro pair pairMem
        change
          (input.packetCellSources pair.1 pair.2).card =
            (fiber.filter fun source =>
              relation pair source).card
        rw [packetFiber pair pairMem]
      _ =
          ((pairs ×ˢ fiber).filter fun pair =>
            relation pair.1 pair.2).card :=
        (prop62ParentCWA_card_relation_eq_sum_left
          pairs fiber relation).symm
      _ =
          ∑ source ∈ fiber,
            (pairs.filter fun pair =>
              relation pair source).card :=
        prop62ParentCWA_card_relation_eq_sum_right
          pairs fiber relation
      _ ≤
          ∑ source ∈ fiber,
            (input.sourceCellsForSource source).card := by
        apply Finset.sum_le_sum
        intro source _
        calc
          (pairs.filter fun pair =>
              relation pair source).card ≤
              (input.positivePairs.filter fun pair =>
                source ∈ input.packetCellSources pair.1 pair.2).card :=
            Finset.card_le_card (selectedRelationSubset source)
          _ = (input.sourceCellsForSource source).card :=
            (input.sourceCellsForSource_card source).symm
  unfold parentClassMass
  calc
    (input.parentIncidenceWeight multiplicity parent : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) ≤
        ((∑ source ∈ fiber,
          (input.sourceCellsForSource source).card : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      gcongr
    _ =
        ∑ source ∈ fiber,
          ((input.sourceCellsForSource source).card : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ =
        ∑ source ∈ fiber,
          volume (shading.carrier source) := by
      apply Finset.sum_congr rfl
      intro source _
      exact (input.source_carrier_volume_eq source).symm
    _ ≤
        ∑ source ∈ fiber,
          volume (wz1PaperTubeCarrier (fine.tube source)) := by
      exact Finset.sum_le_sum fun source _ =>
        measure_mono (shading.subset_body source)
    _ ≤
        ∑ _source ∈ fiber,
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2 := by
      exact Finset.sum_le_sum fun source _ =>
        (wz2PaperTubeCarrier_convex_and_volume_quadratic
          wz2_paper_tube_carrier_geometry input.delta_pos
          deltaLeOneTwentyFour (fine.tube source)
          (cover.fine_line_class source)).2
    _ =
        (input.parentFiberCard parent : ENNReal) *
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2 := by
      simp [fiber, parentFiberCard, Finset.sum_const, nsmul_eq_mul]
      ring

/--
The exact scalar coefficient left after the ambient/selected parent-cardinality
ratio is inserted into the terminal CWA constant.
-/
def terminalParentExactCoefficient
    (fiberUniformConstant tubeMassConstant : ENNReal)
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification
          parentDegree bins A0) : ENNReal :=
  ((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
    (2 * input.terminalParentSelectionLoss multiplicity parentClass *
      fiberUniformConstant * tubeMassConstant) *
    ambientConstant

/--
V4-specialized exact ratio bound.  The only local geometric premise is the
natural upper bound saying that the selected packet-cell mass of one parent is
at most `tubeMassConstant * delta²` times its complete-fiber cardinality.
-/
theorem terminalParent_card_ratio_exact
    (densityConstant fiberUniformConstant tubeMassConstant : ENNReal)
    (fullFiberUniform :
      ∀ first second : Fin coarse.card,
        (input.parentFiberCard first : ENNReal) ≤
          fiberUniformConstant *
            (input.parentFiberCard second : ENNReal))
    (density :
      densityConstant * fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (selectedParentMassUpper :
      ∀ parent ∈ parentClass.selectedParents,
        input.parentClassMass multiplicity parent ≤
          input.parentFiberCard parent *
            tubeMassConstant * Kakeya.realRpowENN delta 2) :
    densityConstant * coarse.enncard ≤
      (2 * input.terminalParentSelectionLoss multiplicity parentClass *
        fiberUniformConstant * tubeMassConstant) *
          (parentClass.selectedParents.card : ENNReal) := by
  let selectedParent : Fin coarse.card :=
    Classical.choose parentClass.selectedParents_nonempty
  have selectedParentMem :
      selectedParent ∈ parentClass.selectedParents :=
    Classical.choose_spec parentClass.selectedParents_nonempty
  have fiberSum :
      (∑ parent : Fin coarse.card,
        (input.parentFiberCard parent : ENNReal)) = fine.enncard := by
    have raw :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card))
        cover.toWZ1PaperTubeCover.parent
    have fiberEq :
        ∀ parent : Fin coarse.card,
          input.parentFiberCard parent =
            ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
              cover.toWZ1PaperTubeCover.parent source = parent).card := by
      intro parent
      unfold parentFiberCard
      congr 1
      ext source
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        mem_wz2PaperFullFiberIndices_iff]
      constructor
      · intro sourceCovered
        exact
          (cover.toWZ1PaperTubeCover.parent_unique
            source parent sourceCovered).symm
      · intro parentEq
        rw [← parentEq]
        exact cover.toWZ1PaperTubeCover.parent_covers source
    have naturalSum :
        (∑ parent : Fin coarse.card, input.parentFiberCard parent) =
          fine.card := by
      calc
        (∑ parent : Fin coarse.card, input.parentFiberCard parent) =
            ∑ parent : Fin coarse.card,
              ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
                cover.toWZ1PaperTubeCover.parent source = parent).card := by
          apply Finset.sum_congr rfl
          intro parent _
          exact fiberEq parent
        _ = fine.card := by simpa using raw
    change
      (∑ parent : Fin coarse.card,
        (input.parentFiberCard parent : ENNReal)) =
          (fine.card : ENNReal)
    rw [← Nat.cast_sum]
    exact congrArg (fun value : ℕ => (value : ENNReal)) naturalSum
  have weightedRetention :
      shading.mass ≤
        input.terminalParentSelectionLoss multiplicity parentClass *
          ∑ parent ∈ parentClass.selectedParents,
            input.parentClassMass multiplicity parent := by
    have raw :=
      input.sourceShading_mass_le_selectedParentWeight
        multiplicity parentClass
    rw [show
      (∑ parent ∈ parentClass.selectedParents,
          input.parentClassMass multiplicity parent) =
        (∑ parent ∈ parentClass.selectedParents,
          (input.parentIncidenceWeight multiplicity parent : ENNReal)) *
            volume (wz1PaperGridCube delta (0, 0, 0)) by
      simp only [parentClassMass]
      rw [Finset.sum_mul]]
    simpa only [terminalParentSelectionLoss, mul_assoc] using raw
  have selectedWeightComparable :
      ∀ first ∈ parentClass.selectedParents,
        ∀ second ∈ parentClass.selectedParents,
          input.parentClassMass multiplicity first ≤
            2 * input.parentClassMass multiplicity second := by
    intro first firstMem second secondMem
    have firstUpper :=
      (parentClass.selectedParent_mass_band
        input multiplicity first firstMem).2.le
    have secondLower :=
      (parentClass.selectedParent_mass_band
        input multiplicity second secondMem).1
    exact firstUpper.trans <| by
      calc
        (2 * parentClass.weightFloor : ENNReal) *
              volume (wz1PaperGridCube delta (0, 0, 0)) =
            2 * ((parentClass.weightFloor : ENNReal) *
              volume (wz1PaperGridCube delta (0, 0, 0))) := by
          norm_num only [Nat.cast_mul, Nat.cast_ofNat]
          ring
        _ ≤ 2 * input.parentClassMass multiplicity second := by
          gcongr
  simpa only [Kakeya.Streamlined.TubeFamily.enncard, Fintype.card_fin] using
    pureWZ2_prop62_parent_card_ratio_of_weighted_retention
      parentClass.selectedParents parentClass.selectedParents_nonempty
      (fun parent => (input.parentFiberCard parent : ENNReal))
      (input.parentClassMass multiplicity)
      fine.enncard (Kakeya.realRpowENN delta 2) shading.mass
      densityConstant fiberUniformConstant
      (input.terminalParentSelectionLoss multiplicity parentClass)
      tubeMassConstant
      fiberSum
      fullFiberUniform
      density weightedRetention selectedWeightComparable
      selectedParentMassUpper
      (fun parent parentMem => by
        exact_mod_cast
          input.parentFiberCard_pos multiplicity <|
            parentClass.weightClass_subset <|
              parentClass.selectedParents_subset parentMem)
      (fun _parent _parentMem => ENNReal.natCast_ne_top _)
      (by
        rw [Kakeya.realRpowENN]
        exact ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos input.delta_pos 2))
      (by simp [Kakeya.realRpowENN])

/--
The terminal nearby-CWA constant is bounded by its exact non-asymptotic
coefficient times the inverse refined density.
-/
theorem terminalParentOutputConstant_le_exact
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification
          parentDegree bins A0)
    (densityConstant fiberUniformConstant tubeMassConstant : ENNReal)
    (densityConstantPos : 0 < densityConstant)
    (densityConstantFinite : densityConstant ≠ ⊤)
    (fullFiberUniform :
      ∀ first second : Fin coarse.card,
        (input.parentFiberCard first : ENNReal) ≤
          fiberUniformConstant *
            (input.parentFiberCard second : ENNReal))
    (density :
      densityConstant * fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (selectedParentMassUpper :
      ∀ parent ∈ parentClass.selectedParents,
        input.parentClassMass multiplicity parent ≤
          input.parentFiberCard parent *
            tubeMassConstant * Kakeya.realRpowENN delta 2)
    (exactScaleBound : ENNReal)
    (scaleWindow_le : scaleWindow ≤ exactScaleBound)
    (exactScale_le :
      input.terminalParentExactCoefficient
          multiplicity parentClass fiberUniformConstant tubeMassConstant
            treeCleanup exactification parentDegree core *
          densityConstant⁻¹ ≤
        exactScaleBound) :
    input.terminalParentOutputConstant
        multiplicity parentClass treeCleanup exactification
          parentDegree core ≤
      exactScaleBound := by
  have ratio :=
    input.terminalParent_card_ratio_exact
      multiplicity parentClass
      densityConstant fiberUniformConstant tubeMassConstant
      fullFiberUniform
      density selectedParentMassUpper
  have selectedCardPos :
      (parentClass.selectedParents.card : ENNReal) ≠ 0 := by
    exact_mod_cast parentClass.selectedParents_nonempty.card_pos.ne'
  have selectedCardFinite :
      (parentClass.selectedParents.card : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have ratioWithInverse :
      coarse.enncard *
          (parentClass.selectedParents.card : ENNReal)⁻¹ ≤
        (2 * input.terminalParentSelectionLoss multiplicity parentClass *
          fiberUniformConstant * tubeMassConstant) *
            densityConstant⁻¹ := by
    apply
      (ENNReal.mul_le_mul_iff_right
        densityConstantPos.ne' densityConstantFinite).mp
    calc
      densityConstant *
          (coarse.enncard *
            (parentClass.selectedParents.card : ENNReal)⁻¹) =
          (densityConstant * coarse.enncard) *
            (parentClass.selectedParents.card : ENNReal)⁻¹ := by ring
      _ ≤
          ((2 * input.terminalParentSelectionLoss multiplicity parentClass *
            fiberUniformConstant * tubeMassConstant) *
              (parentClass.selectedParents.card : ENNReal)) *
                (parentClass.selectedParents.card : ENNReal)⁻¹ := by
        gcongr
      _ =
          2 * input.terminalParentSelectionLoss multiplicity parentClass *
            fiberUniformConstant * tubeMassConstant := by
        calc
          (2 * input.terminalParentSelectionLoss multiplicity parentClass *
                fiberUniformConstant * tubeMassConstant) *
                (parentClass.selectedParents.card : ENNReal) *
              (parentClass.selectedParents.card : ENNReal)⁻¹ =
            (2 * input.terminalParentSelectionLoss multiplicity parentClass *
                fiberUniformConstant * tubeMassConstant) *
              ((parentClass.selectedParents.card : ENNReal) *
                (parentClass.selectedParents.card : ENNReal)⁻¹) := by ring
          _ =
              2 * input.terminalParentSelectionLoss multiplicity parentClass *
                fiberUniformConstant * tubeMassConstant := by
            rw [ENNReal.mul_inv_cancel selectedCardPos selectedCardFinite]
            simp
      _ =
          densityConstant *
            ((2 * input.terminalParentSelectionLoss multiplicity parentClass *
              fiberUniformConstant * tubeMassConstant) *
                densityConstant⁻¹) := by
        calc
          2 * input.terminalParentSelectionLoss multiplicity parentClass *
                fiberUniformConstant * tubeMassConstant =
              (2 * input.terminalParentSelectionLoss multiplicity parentClass *
                fiberUniformConstant * tubeMassConstant) *
                  (densityConstant * densityConstant⁻¹) := by
            rw [ENNReal.mul_inv_cancel densityConstantPos.ne'
              densityConstantFinite]
            simp
          _ =
              densityConstant *
                ((2 * input.terminalParentSelectionLoss multiplicity parentClass *
                  fiberUniformConstant * tubeMassConstant) *
                    densityConstant⁻¹) := by ring
  rw [terminalParentOutputConstant]
  rw [max_le_iff]
  refine ⟨scaleWindow_le, ?_⟩
  apply exactScale_le.trans'
  unfold terminalParentScaleConstant terminalDensityLoss
  dsimp only [terminalParentExactCoefficient]
  calc
    (((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
          coarse.enncard *
          (parentClass.selectedParents.card : ENNReal)⁻¹) *
        ambientConstant ≤
      ((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
        ((2 * input.terminalParentSelectionLoss multiplicity parentClass *
          fiberUniformConstant * tubeMassConstant) *
            densityConstant⁻¹) *
        ambientConstant := by
      calc
        (((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
              coarse.enncard *
              (parentClass.selectedParents.card : ENNReal)⁻¹) *
            ambientConstant =
          ((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
            (coarse.enncard *
              (parentClass.selectedParents.card : ENNReal)⁻¹) *
            ambientConstant := by ring
        _ ≤
          ((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
            ((2 * input.terminalParentSelectionLoss multiplicity parentClass *
              fiberUniformConstant * tubeMassConstant) *
                densityConstant⁻¹) *
            ambientConstant := by
          gcongr
    _ =
      input.terminalParentExactCoefficient
          multiplicity parentClass fiberUniformConstant tubeMassConstant
            treeCleanup exactification parentDegree core *
        densityConstant⁻¹ := by
      unfold terminalParentExactCoefficient
      ring

/--
V4 power wrapper.  All logarithmic and depth estimates are concentrated in
the final scalar absorption premise; the parent ratio itself is proved above
from density, weighted retention, and complete-fiber uniformity.
-/
theorem terminalParentOutputConstant_le_power
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification
          parentDegree bins A0)
    (eta : ℝ)
    (cwaLossExponent : ℕ)
    (densityConstant fiberUniformConstant tubeMassConstant : ENNReal)
    (densityConstantPos : 0 < densityConstant)
    (densityConstantFinite : densityConstant ≠ ⊤)
    (fullFiberUniform :
      ∀ first second : Fin coarse.card,
        (input.parentFiberCard first : ENNReal) ≤
          fiberUniformConstant *
            (input.parentFiberCard second : ENNReal))
    (density :
      densityConstant * fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (selectedParentMassUpper :
      ∀ parent ∈ parentClass.selectedParents,
        input.parentClassMass multiplicity parent ≤
          input.parentFiberCard parent *
            tubeMassConstant * Kakeya.realRpowENN delta 2)
    (scaleWindowPower :
      scaleWindow ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta))
    (exactPowerAbsorption :
      input.terminalParentExactCoefficient
          multiplicity parentClass fiberUniformConstant tubeMassConstant
            treeCleanup exactification parentDegree core *
          densityConstant⁻¹ ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta)) :
    input.terminalParentOutputConstant
        multiplicity parentClass treeCleanup exactification
          parentDegree core ≤
      Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta) := by
  exact
    input.terminalParentOutputConstant_le_exact
      multiplicity parentClass treeCleanup exactification parentDegree core
      densityConstant fiberUniformConstant tubeMassConstant
      densityConstantPos densityConstantFinite fullFiberUniform
      density selectedParentMassUpper
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta))
      scaleWindowPower exactPowerAbsorption

/-- CWA loss budget for the terminal parent family: `D + 2 * B + 4`. -/
def terminalParentCWALossExponent
    (densityExponent cwaExponent : ℕ) : ℕ :=
  densityExponent + 2 * cwaExponent + 4

@[simp] theorem terminalParentCWALossExponent_eq
    (densityExponent cwaExponent : ℕ) :
    terminalParentCWALossExponent densityExponent cwaExponent =
      densityExponent + 2 * cwaExponent + 4 :=
  rfl

/-- Power target associated to `terminalParentCWALossExponent`. -/
def terminalParentCWATarget
    (delta eta : ℝ)
    (densityExponent cwaExponent : ℕ) : ENNReal :=
  Kakeya.realRpowENN delta
    (-((terminalParentCWALossExponent
      densityExponent cwaExponent : ℕ) : ℝ) * eta)

private theorem terminalParentCWA_realRpowENN_inv
    {delta exponent : ℝ}
    (deltaPos : 0 < delta) :
    (Kakeya.realRpowENN delta exponent)⁻¹ =
      Kakeya.realRpowENN delta (-exponent) := by
  simp only [Kakeya.realRpowENN]
  calc
    (ENNReal.ofReal (Real.rpow delta exponent))⁻¹ =
        ENNReal.ofReal ((Real.rpow delta exponent)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos
        (Real.rpow_pos_of_pos deltaPos exponent)).symm
    _ = ENNReal.ofReal (Real.rpow delta (-exponent)) :=
      congrArg ENNReal.ofReal
        (Real.rpow_neg deltaPos.le exponent).symm

/--
Generic high-level terminal-parent CWA bound.

The parent-cardinality ratio is proved internally from the aggregate density,
the three weighted dyadic selections in `prefixData`, and `fullFiberUniform`.
The selected-parent mass upper bound is also proved internally by the
packet-cell double count and the quadratic paper-tube volume bound.

The scalar hypotheses expose the paper bookkeeping:

* the complete-fiber uniformity costs `delta ^ (-B * eta)`;
* the schedule ambient CWA costs `delta ^ (-(B + 1) * eta)`;
* the depth, peeling, dyadic, and absolute geometric factors cost
  `delta ^ (-3 * eta)`;
* inversion of the input density costs `delta ^ (-D * eta)`.

Thus the final exponent is exactly `D + 2 * B + 4`.
-/
theorem terminalParentCWA_power_bound
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    {scheduleAmbientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse scheduleAmbientConstant scaleWindow)
    (prefixData : input.FourDegreePrefixData schedule)
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
          prefixData.exactification prefixData.parentDegree prefixData.bins A0)
    (families :
      input.TerminalCompleteFamiliesData
        prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
          prefixData.exactification core.ranges)
    (densityExponent cwaExponent : ℕ)
    (eta : ℝ)
    (densityConstant fiberUniformConstant : ENNReal)
    (densityConstant_eq :
      densityConstant =
        Kakeya.realRpowENN delta
          ((densityExponent : ℝ) * eta))
    (refinedDensity :
      shading.IsLambdaDense densityConstant)
    (fullFiberUniform :
      ∀ first second : Fin coarse.card,
        (input.parentFiberCard first : ENNReal) ≤
          fiberUniformConstant *
            (input.parentFiberCard second : ENNReal))
    (fiberUniformBound :
      fiberUniformConstant ≤
        Kakeya.realRpowENN delta
          (-(cwaExponent : ℝ) * eta))
    (scheduleAmbientBound :
      scheduleAmbientConstant ≤
        Kakeya.realRpowENN delta
          (-((cwaExponent : ℝ) + 1) * eta))
    (deltaLeOneTwentyFour : delta ≤ 1 / 24)
    (scaleWindowBound :
      scaleWindow ≤
        terminalParentCWATarget delta eta
          densityExponent cwaExponent)
    (structuralAbsorption :
      ((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
          (2 *
            input.terminalParentSelectionLoss
              prefixData.multiplicity prefixData.parentClass *
            (55296 * Kakeya.deltaTubeVolume 1)) ≤
        Kakeya.realRpowENN delta ((-3 : ℝ) * eta)) :
    input.terminalParentOutputConstant
          prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
            prefixData.exactification prefixData.parentDegree core ≤
        terminalParentCWATarget delta eta
          densityExponent cwaExponent ∧
      WZ2PaperPureCWAAtNearbyScales
        families.restriction.coarseSelected.family
        (terminalParentCWATarget delta eta
          densityExponent cwaExponent) := by
  have bodyLower :=
    pureWZ2_prop62_paper_body_mass_lower
      input.delta_pos
      (deltaLeOneTwentyFour.trans (by norm_num))
      cover.fine_line_class
  have density :
      densityConstant * fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass := by
    calc
      densityConstant * fine.enncard *
            Kakeya.realRpowENN delta 2 =
          densityConstant *
            (fine.enncard * Kakeya.realRpowENN delta 2) := by
        ring
      _ ≤
          densityConstant * (wz1PaperBodyFamily fine).mass := by
        gcongr
      _ ≤ shading.mass := refinedDensity
  have densityConstantPos : 0 < densityConstant := by
    rw [densityConstant_eq]
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos input.delta_pos]
  have densityConstantFinite : densityConstant ≠ ⊤ := by
    rw [densityConstant_eq]
    simp [Kakeya.realRpowENN]
  have selectedParentMassUpper :
      ∀ parent ∈ prefixData.parentClass.selectedParents,
        input.parentClassMass prefixData.multiplicity parent ≤
          input.parentFiberCard parent *
            (55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta 2 := by
    intro parent parentMem
    exact
      input.selectedParentMass_le_completeFiberTubeMass
        prefixData.multiplicity prefixData.parentClass
        deltaLeOneTwentyFour parent parentMem
  let fiberUniformPower :=
    Kakeya.realRpowENN delta
      (-(cwaExponent : ℝ) * eta)
  let scheduleAmbientPower :=
    Kakeya.realRpowENN delta
      (-((cwaExponent : ℝ) + 1) * eta)
  let structuralPower :=
    Kakeya.realRpowENN delta ((-3 : ℝ) * eta)
  have exactCoefficientBound :
      input.terminalParentExactCoefficient
          prefixData.multiplicity prefixData.parentClass fiberUniformConstant
            (55296 * Kakeya.deltaTubeVolume 1) prefixData.treeCleanup
            prefixData.exactification prefixData.parentDegree core ≤
        structuralPower * fiberUniformPower * scheduleAmbientPower := by
    unfold terminalParentExactCoefficient
    calc
      ((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
            (2 *
              input.terminalParentSelectionLoss
                prefixData.multiplicity prefixData.parentClass *
              fiberUniformConstant *
              (55296 * Kakeya.deltaTubeVolume 1)) *
            scheduleAmbientConstant =
          (((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
            (2 *
              input.terminalParentSelectionLoss
                prefixData.multiplicity prefixData.parentClass *
              (55296 * Kakeya.deltaTubeVolume 1))) *
            fiberUniformConstant * scheduleAmbientConstant := by
        ring
      _ ≤
          structuralPower * fiberUniformConstant *
            scheduleAmbientConstant := by
        gcongr
      _ ≤
          structuralPower * fiberUniformPower *
            scheduleAmbientConstant := by
        gcongr
      _ ≤
          structuralPower * fiberUniformPower *
            scheduleAmbientPower := by
        gcongr
  have densityInverse :
      densityConstant⁻¹ =
        Kakeya.realRpowENN delta
          (-((densityExponent : ℝ) * eta)) := by
    rw [densityConstant_eq]
    exact terminalParentCWA_realRpowENN_inv input.delta_pos
  have exactPowerAbsorption :
      input.terminalParentExactCoefficient
            prefixData.multiplicity prefixData.parentClass
              fiberUniformConstant
              (55296 * Kakeya.deltaTubeVolume 1)
              prefixData.treeCleanup prefixData.exactification
              prefixData.parentDegree core *
          densityConstant⁻¹ ≤
        terminalParentCWATarget delta eta
          densityExponent cwaExponent := by
    calc
      input.terminalParentExactCoefficient
              prefixData.multiplicity prefixData.parentClass
                fiberUniformConstant
                (55296 * Kakeya.deltaTubeVolume 1)
                prefixData.treeCleanup prefixData.exactification
                prefixData.parentDegree core *
            densityConstant⁻¹ ≤
          (structuralPower * fiberUniformPower * scheduleAmbientPower) *
            densityConstant⁻¹ := by
        gcongr
      _ =
          structuralPower * fiberUniformPower * scheduleAmbientPower *
            Kakeya.realRpowENN delta
              (-((densityExponent : ℝ) * eta)) := by
        rw [densityInverse]
      _ =
          terminalParentCWATarget delta eta
            densityExponent cwaExponent := by
        dsimp only [structuralPower, fiberUniformPower, scheduleAmbientPower]
        unfold terminalParentCWATarget
        rw [← realRpowENN_add input.delta_pos,
          ← realRpowENN_add input.delta_pos,
          ← realRpowENN_add input.delta_pos]
        congr 1
        simp only [terminalParentCWALossExponent]
        push_cast
        ring
  have constantBound :=
    input.terminalParentOutputConstant_le_power
      prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
      prefixData.exactification prefixData.parentDegree core eta
      (terminalParentCWALossExponent densityExponent cwaExponent)
      densityConstant fiberUniformConstant
      (55296 * Kakeya.deltaTubeVolume 1)
      densityConstantPos densityConstantFinite fullFiberUniform density
      selectedParentMassUpper scaleWindowBound exactPowerAbsorption
  refine ⟨constantBound, ?_⟩
  exact
    (input.terminalParentCWA
      prefixData.multiplicity prefixData.parentClass prefixData.treeCleanup
        prefixData.exactification prefixData.parentDegree core families).mono
      constantBound
      (by simp [terminalParentCWATarget, Kakeya.realRpowENN])

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
