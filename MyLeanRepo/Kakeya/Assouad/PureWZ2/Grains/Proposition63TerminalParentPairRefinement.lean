import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AmplifiedLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseParentPairRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperTransversePairCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureCarrierDirectionAlignment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperOrientedCellRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NearbyCellResidueRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyShadingExtension

/-!
# Terminal-balanced parent-pair refinement for Proposition 6.3

The arbitrary pure-cover parent-pair argument loses the square of the whole
fine-family cardinality.  At a terminal Proposition 6.2 output we can instead
use the parents which meet the current balanced cell.  Their number is bounded
by the terminal coarse multiplicity, while each parent contributes at most the
terminal fine-fiber multiplicity.  This is the paper Lemma 4.7 cancellation.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Cancel the terminal fine-fiber and coarse-multiplicity factors after the
cross-degree comparison.  This is the algebraic step that prevents a fixed
`delta^(4 - 2 * sigma)` loss from entering Lemma 4.7. -/
lemma proposition63_terminal_parent_pair_cross_degree_cancel
    {fineDegree fiberMultiplicity coarseMultiplicity : ℕ}
    {power sourceMass selectedMass : ENNReal}
    (hfiber : 0 < fiberMultiplicity)
    (hcoarse : 0 < coarseMultiplicity)
    (hcross : power * (coarseMultiplicity : ENNReal) ≤ fineDegree)
    (hmass : ((fineDegree * fiberMultiplicity : ℕ) : ENNReal) ^ 2 *
        sourceMass ≤
      (2 * (fiberMultiplicity : ENNReal) ^ 2) *
        (coarseMultiplicity : ENNReal) ^ 2 * selectedMass) :
    power ^ 2 * sourceMass ≤ 2 * selectedMass := by
  let common : ENNReal :=
    ((fiberMultiplicity : ENNReal) * coarseMultiplicity) ^ 2
  have common_pos : 0 < common := by
    dsimp only [common]
    positivity
  have common_top : common ≠ ⊤ := by
    dsimp only [common]
    apply ENNReal.pow_ne_top
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  apply (ENNReal.mul_le_mul_iff_left common_pos.ne' common_top).mp
  calc
    (power ^ 2 * sourceMass) * common =
        ((power * (coarseMultiplicity : ENNReal)) ^ 2 *
          (fiberMultiplicity : ENNReal) ^ 2) * sourceMass := by
      dsimp only [common]
      ring
    _ ≤ (((fineDegree : ENNReal) ^ 2 *
          (fiberMultiplicity : ENNReal) ^ 2) * sourceMass) := by
      gcongr
    _ = ((fineDegree * fiberMultiplicity : ℕ) : ENNReal) ^ 2 *
          sourceMass := by
      simp only [Nat.cast_mul]
      ring
    _ ≤ (2 * (fiberMultiplicity : ENNReal) ^ 2) *
          (coarseMultiplicity : ENNReal) ^ 2 * selectedMass := hmass
    _ = (2 * selectedMass) * common := by
      dsimp only [common]
      ring

/-- Close-direction counts are monotone under a genuine tube-subfamily
embedding, even though the two shadings live on different indexed family
types.  This is the dependent-family transport needed between the robust and
target Proposition 6.2 calls. -/
lemma paperCloseDirectionCount_le_of_tubeSubfamily
    {delta kappa : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (sub : Kakeya.Streamlined.TubeSubfamily ambient)
    {ambientShading : WZ1PaperTubeShading ambient}
    {selectedShading : WZ1PaperTubeShading sub.family}
    (hsub : ∀ index, selectedShading.carrier index ⊆
      ambientShading.carrier (sub.embedding index))
    (point : Point3) (center : Fin sub.family.card) :
    paperCloseDirectionCount selectedShading point center kappa ≤
      paperCloseDirectionCount ambientShading point (sub.embedding center)
        kappa := by
  let selectedClose : Finset (Fin sub.family.card) :=
    Finset.univ.filter fun index =>
      point ∈ selectedShading.carrier index ∧
        ‖wz1Cross (sub.family.tube center).direction
          (sub.family.tube index).direction‖ < kappa
  let ambientClose : Finset (Fin ambient.card) :=
    Finset.univ.filter fun index =>
      point ∈ ambientShading.carrier index ∧
        ‖wz1Cross (ambient.tube (sub.embedding center)).direction
          (ambient.tube index).direction‖ < kappa
  have imageSubset : Finset.image sub.embedding selectedClose ⊆
      ambientClose := by
    intro ambientIndex ambientMem
    rcases Finset.mem_image.mp ambientMem with
      ⟨selectedIndex, selectedMem, rfl⟩
    rcases Finset.mem_filter.mp selectedMem with
      ⟨_, selectedPoint, selectedDirection⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hsub selectedIndex selectedPoint, ?_⟩
    simpa only [sub.tube_eq center, sub.tube_eq selectedIndex] using
      selectedDirection
  have imageCard : (Finset.image sub.embedding selectedClose).card =
      selectedClose.card := by
    exact Finset.card_image_of_injective _ sub.embedding.injective
  change selectedClose.card ≤ ambientClose.card
  rw [← imageCard]
  exact Finset.card_le_card imageSubset

/-- Zero-extension introduces no extra active tubes.  Hence at an embedded
center its close-direction count is exactly the count in the selected
subfamily. -/
lemma paperCloseDirectionCount_extendShading
    {delta kappa : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (sub : Kakeya.Streamlined.TubeSubfamily ambient)
    (selectedShading : WZ1PaperTubeShading sub.family)
    (point : Point3) (center : Fin sub.family.card) :
    paperCloseDirectionCount (extendShading sub selectedShading) point
        (sub.embedding center) kappa =
      paperCloseDirectionCount selectedShading point center kappa := by
  let selectedClose : Finset (Fin sub.family.card) :=
    Finset.univ.filter fun index =>
      point ∈ selectedShading.carrier index ∧
        ‖wz1Cross (sub.family.tube center).direction
          (sub.family.tube index).direction‖ < kappa
  let ambientClose : Finset (Fin ambient.card) :=
    Finset.univ.filter fun index =>
      point ∈ (extendShading sub selectedShading).carrier index ∧
        ‖wz1Cross (ambient.tube (sub.embedding center)).direction
          (ambient.tube index).direction‖ < kappa
  have imageEq : Finset.image sub.embedding selectedClose = ambientClose := by
    ext ambientIndex
    constructor
    · intro ambientMem
      rcases Finset.mem_image.mp ambientMem with
        ⟨selectedIndex, selectedMem, rfl⟩
      rcases Finset.mem_filter.mp selectedMem with
        ⟨_, selectedPoint, selectedDirection⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · simpa only [extendShading_carrier_mem] using selectedPoint
      · simpa only [sub.tube_eq center, sub.tube_eq selectedIndex] using
          selectedDirection
    · intro ambientMem
      rcases Finset.mem_filter.mp ambientMem with
        ⟨_, ambientPoint, ambientDirection⟩
      by_cases imageMem : ∃ selectedIndex,
          sub.embedding selectedIndex = ambientIndex
      · rcases imageMem with ⟨selectedIndex, rfl⟩
        apply Finset.mem_image.mpr
        refine ⟨selectedIndex, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · simpa only [extendShading_carrier_mem] using ambientPoint
        · simpa only [sub.tube_eq center, sub.tube_eq selectedIndex] using
            ambientDirection
      · rw [extendShading_carrier_empty imageMem] at ambientPoint
        exact False.elim ambientPoint
  change ambientClose.card = selectedClose.card
  rw [← imageEq, Finset.card_image_of_injective _ sub.embedding.injective]

/-- Package the dependent-family transport with the scalar comparison used by
the two-rich-call Lemma 4.7 step.  The robust estimate is made on the outer
family, while the transverse-pair threshold is the inner terminal total
degree. -/
lemma paperCloseDirectionCount_absorbed_of_tubeSubfamily
    {delta kappa : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (sub : Kakeya.Streamlined.TubeSubfamily ambient)
    {ambientShading : WZ1PaperTubeShading ambient}
    {selectedShading : WZ1PaperTubeShading sub.family}
    (hsub : ∀ index, selectedShading.carrier index ⊆
      ambientShading.carrier (sub.embedding index))
    (bound : ENNReal) (multiplicity : ℕ)
    (hbound : ∀ point ∈ ambientShading.union, ∀ index,
      point ∈ ambientShading.carrier index →
        (paperCloseDirectionCount ambientShading point index kappa :
          ENNReal) ≤ bound)
    (habsorb : 2 * bound ≤ (multiplicity : ENNReal)) :
    ∀ point ∈ selectedShading.union, ∀ index,
      point ∈ selectedShading.carrier index →
        2 * paperCloseDirectionCount selectedShading point index kappa ≤
          multiplicity := by
  intro point pointMem index pointIndex
  have ambientPoint : point ∈ ambientShading.union := by
    rcases pointMem with ⟨selectedIndex, selectedPoint⟩
    exact ⟨sub.embedding selectedIndex, hsub selectedIndex selectedPoint⟩
  have transported :
      (paperCloseDirectionCount selectedShading point index kappa :
          ENNReal) ≤
        paperCloseDirectionCount ambientShading point (sub.embedding index)
          kappa := by
    exact_mod_cast paperCloseDirectionCount_le_of_tubeSubfamily
      sub hsub point index
  have resultENN :
      (2 * paperCloseDirectionCount selectedShading point index kappa : ℕ) ≤
        multiplicity := by
    exact_mod_cast
      (calc
        (2 : ENNReal) *
              (paperCloseDirectionCount selectedShading point index kappa :
                ENNReal) ≤
            2 * (paperCloseDirectionCount ambientShading point
              (sub.embedding index) kappa : ENNReal) := by gcongr
        _ ≤ 2 * bound := by
          gcongr
          exact hbound point ambientPoint (sub.embedding index)
            (hsub index pointIndex)
        _ ≤ (multiplicity : ENNReal) := habsorb)
  exact resultENN

/-- Select one transverse ordered parent pair in every spatial cell, charging
only the terminal fiber and coarse multiplicity bands.  In particular the
right side contains no global fine-family cardinality. -/
theorem Proposition63TerminalMultiplicityCertificate.parent_pair_refinement
    {delta rho sigma terminalLoss kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading S : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (terminal : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading)
    (hSSubFine : PaperIsSubshading S fineShading)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (hFineMultiplicity : ∀ point ∈ S.union,
      terminal.fineDegreeFloor * terminal.muFine ≤
        S.pointMultiplicity point)
    (hclose : ∀ point ∈ S.union, ∀ index,
      point ∈ S.carrier index →
        2 * paperCloseDirectionCount S point index kappa ≤
          terminal.fineDegreeFloor * terminal.muFine)
    (K : ℕ) (hK : 0 < K)
    (hrhoAligned : rho = (K : ℝ) * delta) :
    ∃ (chosen : (ℤ × ℤ × ℤ) → Fin coarse.card × Fin coarse.card)
      (selected : WZ1PaperTubeShading fine),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        ∃ first second : Fin fine.card,
          point ∈ S.carrier first ∧ point ∈ S.carrier second ∧
          selectParent cover first =
            (chosen (wz1PaperGridIndex rho point)).1 ∧
          selectParent cover second =
            (chosen (wz1PaperGridIndex rho point)).2 ∧
          kappa ≤ ‖wz1Cross (fine.tube first).direction
            (fine.tube second).direction‖) ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      ((terminal.fineDegreeFloor * terminal.muFine : ℕ) : ENNReal) ^ 2 *
          S.mass ≤
        (2 * (terminal.muFine : ENNReal) ^ 2) *
          ((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) ^ 2 *
            selected.mass := by
  classical
  let Cell := ℤ × ℤ × ℤ
  let Label := Fin coarse.card × Fin coarse.card
  let cell : Point3 → Cell := wz1PaperGridIndex rho
  have hcellMeasurable : Measurable cell := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / rho⌋, ⌊point 1 / rho⌋,
          ⌊point 2 / rho⌋)) := by
      fun_prop
    convert h using 1
    funext point
    simp [cell, wz1PaperGridIndex, gridIndex]
  let allowed : Cell → Finset Label := fun currentCell =>
    (paperBalancedCellParents terminal.balanced currentCell).product
      (paperBalancedCellParents terminal.balanced currentCell)
  have hsupport : ∀ point ∈ S.union,
      cell point ∈ terminal.balanced.activeCells := by
    intro point point_mem
    apply paperBalanced_fine_point_active terminal.balanced point
    rcases point_mem with ⟨index, index_mem⟩
    exact ⟨index, hSSubFine index index_mem⟩
  have hallowedNonempty : ∀ currentCell ∈ terminal.balanced.activeCells,
      (allowed currentCell).Nonempty := by
    intro currentCell cell_mem
    rcases terminal.balanced.cellIntersection_nonempty currentCell cell_mem with
      ⟨point, point_mem, _point_cell⟩
    rcases point_mem with ⟨index, index_mem⟩
    have parent_mem : selectParent cover index ∈
        paperBalancedCellParents terminal.balanced currentCell := by
      have point_index : wz1PaperGridIndex rho point = currentCell :=
        (mem_wz1PaperGridCube rho currentCell point).mp _point_cell
      simpa [point_index] using
        selectedParent_mem_paperBalancedCellParents terminal.balanced index_mem
    exact ⟨(selectParent cover index, selectParent cover index),
      Finset.mem_product.mpr ⟨parent_mem, parent_mem⟩⟩
  let good (point : Point3) (parents : Label) : Prop :=
    ∃ first second : Fin fine.card,
      point ∈ S.carrier first ∧ point ∈ S.carrier second ∧
      selectParent cover first = parents.1 ∧
      selectParent cover second = parents.2 ∧
      kappa ≤ ‖wz1Cross (fine.tube first).direction
        (fine.tube second).direction‖
  have hgoodMeasurable : ∀ parents : Label,
      MeasurableSet {point | good point parents} := by
    intro parents
    let pairs : Finset (Fin fine.card × Fin fine.card) :=
      Finset.univ.filter fun pair =>
        selectParent cover pair.1 = parents.1 ∧
        selectParent cover pair.2 = parents.2 ∧
        kappa ≤ ‖wz1Cross (fine.tube pair.1).direction
          (fine.tube pair.2).direction‖
    have set_eq : {point | good point parents} =
        ⋃ pair ∈ pairs, S.carrier pair.1 ∩ S.carrier pair.2 := by
      ext point
      simp only [good, pairs, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨first, second, hfirst, hsecond, hp1, hp2, htransverse⟩
        exact ⟨(first, second), ⟨hp1, hp2, htransverse⟩, hfirst, hsecond⟩
      · rintro ⟨pair, ⟨hp1, hp2, htransverse⟩, hfirst, hsecond⟩
        exact ⟨pair.1, pair.2, hfirst, hsecond, hp1, hp2, htransverse⟩
    rw [set_eq]
    exact Finset.measurableSet_biUnion pairs fun pair _ =>
      (S.measurable_carrier pair.1).inter (S.measurable_carrier pair.2)
  have hgoodAllowed : ∀ point ∈ S.union, ∀ parents : Label,
      good point parents → parents ∈ allowed (cell point) := by
    intro point _point_mem parents good_at
    rcases good_at with
      ⟨first, second, first_mem, second_mem, first_parent, second_parent, _⟩
    apply Finset.mem_product.mpr
    constructor
    · rw [← first_parent]
      exact selectedParent_mem_paperBalancedCellParents terminal.balanced
        (hSSubFine first first_mem)
    · rw [← second_parent]
      exact selectedParent_mem_paperBalancedCellParents terminal.balanced
        (hSSubFine second second_mem)
  let labelWeight : Cell → Label → ENNReal := fun _ _ => 1
  let goodCount : Point3 → Cell → ENNReal := fun point currentCell =>
    ∑ parents ∈ allowed currentCell,
      ({point | good point parents}.indicator
        (fun _ => labelWeight currentCell parents)) point
  have hgoodCount : ∀ point currentCell, goodCount point currentCell =
      ∑ parents ∈ allowed currentCell,
        ({point | good point parents}.indicator
          (fun _ => labelWeight currentCell parents)) point := by
    intro _ _
    rfl
  have hlabelBound : ∀ currentCell ∈ terminal.balanced.activeCells,
      (∑ parents ∈ allowed currentCell, labelWeight currentCell parents) ≤
        ((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) ^ 2 := by
    intro currentCell cell_mem
    have parent_card_nat :=
      paperBalancedCellParents_card_le_multiplicity terminal.balanced cell_mem
    have representativeFine :=
      terminal.balanced.cellRep_in_union currentCell cell_mem
    rcases representativeFine with ⟨source, source_mem⟩
    have representativeCoarse :
        terminal.balanced.cellRep currentCell cell_mem ∈
          coarseShading.union :=
      ⟨selectParent cover source,
        terminal.balanced.point_compatibility source
          (selectParent cover source) (selectedParent_covers cover source)
          _ source_mem⟩
    have parent_card :
        ((paperBalancedCellParents terminal.balanced currentCell).card :
            ENNReal) ≤
          ((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) := by
      have parent_card_cast :
          ((paperBalancedCellParents terminal.balanced currentCell).card :
              ENNReal) ≤
            (coarseShading.pointMultiplicity
              (terminal.balanced.cellRep currentCell cell_mem) : ENNReal) := by
        exact_mod_cast parent_card_nat
      exact parent_card_cast.trans
        (terminal.coarse_pointMultiplicity_band representativeCoarse).2
    calc
      (∑ parents ∈ allowed currentCell, labelWeight currentCell parents) =
          ((paperBalancedCellParents terminal.balanced currentCell).card :
            ENNReal) ^ 2 := by
        change
          (∑ _parents ∈
              (paperBalancedCellParents terminal.balanced currentCell).product
                (paperBalancedCellParents terminal.balanced currentCell),
              (1 : ENNReal)) = _
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        norm_cast
        change
          ((paperBalancedCellParents terminal.balanced currentCell) ×ˢ
              (paperBalancedCellParents terminal.balanced currentCell)).card = _
        rw [Finset.card_product, pow_two]
      _ ≤ ((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) ^ 2 :=
        pow_le_pow_left' parent_card 2
  have hpointwise : ∀ point ∈ S.union,
      ((terminal.fineDegreeFloor * terminal.muFine : ℕ) : ENNReal) ^ 2 ≤
        (2 * (terminal.muFine : ENNReal) ^ 2) *
          goodCount point (cell point) := by
    intro point point_mem
    let active : Finset (Fin fine.card) :=
      Finset.univ.filter fun index => point ∈ S.carrier index
    let transversePairs : Finset (Fin fine.card × Fin fine.card) :=
      (active ×ˢ active).filter fun pair =>
        kappa ≤ ‖wz1Cross (fine.tube pair.1).direction
          (fine.tube pair.2).direction‖
    have transverse_lower :
        ((terminal.fineDegreeFloor * terminal.muFine : ℕ) : ENNReal) ^ 2 ≤
          2 * (transversePairs.card : ENNReal) := by
      have transverse_lower_nat :=
        paper_transverse_ordered_pairs_lower hclose
          hFineMultiplicity point point_mem
      have floor_square_le :
          (terminal.fineDegreeFloor * terminal.muFine) ^ 2 ≤
            S.pointMultiplicity point ^ 2 :=
        Nat.pow_le_pow_left (hFineMultiplicity point point_mem) 2
      exact_mod_cast floor_square_le.trans transverse_lower_nat
    let goodLabels : Finset Label :=
      (allowed (cell point)).filter fun parents => good point parents
    let fiberPairs (parents : Label) :
        Finset (Fin fine.card × Fin fine.card) :=
      transversePairs.filter fun pair =>
        selectParent cover pair.1 = parents.1 ∧
        selectParent cover pair.2 = parents.2
    have pair_decomposition : transversePairs =
        goodLabels.biUnion fiberPairs := by
      ext pair
      constructor
      · intro pair_mem
        have first_mem : point ∈ S.carrier pair.1 :=
          (Finset.mem_filter.mp (Finset.mem_product.mp
            (Finset.mem_filter.mp pair_mem).1).1).2
        have second_mem : point ∈ S.carrier pair.2 :=
          (Finset.mem_filter.mp (Finset.mem_product.mp
            (Finset.mem_filter.mp pair_mem).1).2).2
        let parents : Label :=
          (selectParent cover pair.1, selectParent cover pair.2)
        have parents_allowed : parents ∈ allowed (cell point) :=
          hgoodAllowed point point_mem parents
            ⟨pair.1, pair.2, first_mem, second_mem, rfl, rfl,
              (Finset.mem_filter.mp pair_mem).2⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨parents, Finset.mem_filter.mpr
          ⟨parents_allowed, ?_⟩, ?_⟩
        · exact ⟨pair.1, pair.2, first_mem, second_mem, rfl, rfl,
            (Finset.mem_filter.mp pair_mem).2⟩
        · exact Finset.mem_filter.mpr ⟨pair_mem, rfl, rfl⟩
      · intro pair_mem
        rcases Finset.mem_biUnion.mp pair_mem with
          ⟨parents, _parents_mem, pair_fiber⟩
        exact (Finset.mem_filter.mp pair_fiber).1
    have fiber_pair_bound : ∀ parents ∈ goodLabels,
        ((fiberPairs parents).card : ENNReal) ≤
          (terminal.muFine : ENNReal) ^ 2 := by
      intro parents _parents_mem
      let firstFiber : Finset (Fin fine.card) :=
        Finset.univ.filter fun index =>
          selectParent cover index = parents.1 ∧ point ∈ S.carrier index
      let secondFiber : Finset (Fin fine.card) :=
        Finset.univ.filter fun index =>
          selectParent cover index = parents.2 ∧ point ∈ S.carrier index
      have pair_subset : fiberPairs parents ⊆ firstFiber.product secondFiber := by
        intro pair pair_mem
        rcases Finset.mem_filter.mp pair_mem with ⟨transverse_mem, hp1, hp2⟩
        rcases Finset.mem_filter.mp transverse_mem with ⟨active_mem, _⟩
        rcases Finset.mem_product.mp active_mem with
          ⟨first_active, second_active⟩
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1,
              (Finset.mem_filter.mp first_active).2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2,
              (Finset.mem_filter.mp second_active).2⟩⟩
      have first_subset : firstFiber ⊆
          (cover.toWZ1PaperTubeCover.fiberIndices parents.1).filter
            fun index => point ∈ fineShading.carrier index := by
        intro index index_mem
        rcases Finset.mem_filter.mp index_mem with
          ⟨_, index_parent, index_point⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, index_parent⟩,
            hSSubFine index index_point⟩
      have second_subset : secondFiber ⊆
          (cover.toWZ1PaperTubeCover.fiberIndices parents.2).filter
            fun index => point ∈ fineShading.carrier index := by
        intro index index_mem
        rcases Finset.mem_filter.mp index_mem with
          ⟨_, index_parent, index_point⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, index_parent⟩,
            hSSubFine index index_point⟩
      have first_cap : (firstFiber.card : ENNReal) ≤ terminal.muFine := by
        have first_card_le :
            (firstFiber.card : ENNReal) ≤
              (((cover.toWZ1PaperTubeCover.fiberIndices parents.1).filter
                fun index => point ∈ fineShading.carrier index).card :
                  ENNReal) := by
          exact_mod_cast Finset.card_le_card first_subset
        exact first_card_le.trans
          (terminal.fiber_pointMultiplicity_le parents.1 point)
      have second_cap : (secondFiber.card : ENNReal) ≤ terminal.muFine := by
        have second_card_le :
            (secondFiber.card : ENNReal) ≤
              (((cover.toWZ1PaperTubeCover.fiberIndices parents.2).filter
                fun index => point ∈ fineShading.carrier index).card :
                  ENNReal) := by
          exact_mod_cast Finset.card_le_card second_subset
        exact second_card_le.trans
          (terminal.fiber_pointMultiplicity_le parents.2 point)
      calc
        ((fiberPairs parents).card : ENNReal) ≤
            ((firstFiber.product secondFiber).card : ENNReal) := by
          exact_mod_cast Finset.card_le_card pair_subset
        _ = (firstFiber.card : ENNReal) * (secondFiber.card : ENNReal) := by
          simp [Finset.card_product]
        _ ≤ (terminal.muFine : ENNReal) * terminal.muFine := by gcongr
        _ = (terminal.muFine : ENNReal) ^ 2 := by ring
    have transverse_upper : (transversePairs.card : ENNReal) ≤
        (terminal.muFine : ENNReal) ^ 2 *
          ∑ parents ∈ goodLabels, labelWeight (cell point) parents := by
      rw [pair_decomposition]
      calc
        ((goodLabels.biUnion fiberPairs).card : ENNReal) ≤
            ∑ parents ∈ goodLabels,
              ((fiberPairs parents).card : ENNReal) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ parents ∈ goodLabels,
            (terminal.muFine : ENNReal) ^ 2 := by
          exact Finset.sum_le_sum fun parents parents_mem =>
            fiber_pair_bound parents parents_mem
        _ = (terminal.muFine : ENNReal) ^ 2 *
            ∑ parents ∈ goodLabels, labelWeight (cell point) parents := by
          rw [Finset.sum_const]
          simp [labelWeight]
          ring
    have good_weight : goodCount point (cell point) =
        ∑ parents ∈ goodLabels, labelWeight (cell point) parents := by
      rw [hgoodCount point (cell point)]
      simp [goodLabels, Set.indicator_apply, Finset.sum_filter]
    calc
      ((terminal.fineDegreeFloor * terminal.muFine : ℕ) : ENNReal) ^ 2 ≤
          2 * (transversePairs.card : ENNReal) := transverse_lower
      _ ≤ 2 * ((terminal.muFine : ENNReal) ^ 2 *
          ∑ parents ∈ goodLabels, labelWeight (cell point) parents) := by
        gcongr
      _ = (2 * (terminal.muFine : ENNReal) ^ 2) *
          goodCount point (cell point) := by
        rw [good_weight]
        ring
  let terminalEdge := Classical.choose terminal.packetCells_nonempty
  let defaultParent : Fin coarse.card := terminalEdge.1
  letI : Nonempty Label := ⟨(defaultParent, defaultParent)⟩
  rcases paper_cellwise_amplified_label_mass_refinement
      (Cell := Cell) (Label := Label) S cell hcellMeasurable
      terminal.balanced.activeCells hsupport allowed hallowedNonempty good
      hgoodMeasurable hgoodAllowed labelWeight goodCount hgoodCount
      (((terminal.fineDegreeFloor * terminal.muFine : ℕ) : ENNReal) ^ 2)
      (2 * (terminal.muFine : ENNReal) ^ 2)
      (((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) ^ 2)
      hpointwise hlabelBound with
    ⟨chosen, selected, selected_sub, selected_eq, _chosen_allowed,
      selected_good, selected_multiplicity, selected_mass⟩
  have cell_const : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        cell first = cell second := by
    intro first second fine_cell
    exact wz1PaperGridIndex_fine_to_coarse
      K hK hrhoAligned fine_cell
  have good_const : ∀ parents first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        (good first parents ↔ good second parents) := by
    intro parents first second fine_cell
    have carrier_iff : ∀ index, first ∈ S.carrier index ↔
        second ∈ S.carrier index := fun index =>
      hSCubical.carrier_mem_iff_of_same_cell index fine_cell
    constructor
    · rintro ⟨i, j, hi, hj, hpi, hpj, htransverse⟩
      exact ⟨i, j, (carrier_iff i).mp hi, (carrier_iff j).mp hj,
        hpi, hpj, htransverse⟩
    · rintro ⟨i, j, hi, hj, hpi, hpj, htransverse⟩
      exact ⟨i, j, (carrier_iff i).mpr hi, (carrier_iff j).mpr hj,
        hpi, hpj, htransverse⟩
  have selected_cubical : WZ1PaperIsCubicalShading selected := by
    rw [selected_eq]
    exact paperCellwisePredicateRestriction_cubical hSCubical
      cell hcellMeasurable good hgoodMeasurable chosen (by fun_prop)
      cell_const good_const
  exact ⟨chosen, selected, selected_sub, selected_cubical, selected_good,
    selected_multiplicity, selected_mass⟩

/-- Complete one-scale variation on a terminal balanced target cover.  The
mass bound retains the exact terminal fine-fiber and coarse point-multiplicity
factors, so `cross_degree` can cancel them without a global cardinality loss. -/
theorem Proposition63TerminalMultiplicityCertificate.asymmetric_variation
    {delta rho sigma terminalLoss variationScale kappa incidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading S : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (terminal : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading)
    (hSSubFine : PaperIsSubshading S fineShading)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second)
    (hFineMultiplicity : ∀ point ∈ S.union,
      terminal.fineDegreeFloor * terminal.muFine ≤
        S.pointMultiplicity point)
    (hclose : ∀ point ∈ S.union, ∀ index,
      point ∈ S.carrier index →
        2 * paperCloseDirectionCount S point index kappa ≤
          terminal.fineDegreeFloor * terminal.muFine)
    (hincidenceNonnegative : 0 ≤ incidence)
    (hrho : 0 < rho)
    (hvariationScale : 0 < variationScale)
    (hkappa : rho < kappa)
    (K : ℕ) (hK : 0 < K)
    (hrhoAligned : rho = (K : ℝ) * delta) :
    ∃ selected : WZ1PaperTubeShading fine,
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union, ∀ other ∈ selected.union,
        dist point other ≤ rho →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ variationScale) ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      ((terminal.fineDegreeFloor * terminal.muFine : ℕ) : ENNReal) ^ 2 *
          S.mass ≤
        27 * ((2 * (terminal.muFine : ENNReal) ^ 2) *
          ((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) ^ 2 *
          (wz1OrientationCapCount
            (10 * (incidence + rho / 2) / (kappa - rho)) variationScale :
              ENNReal)) * selected.mass := by
  rcases terminal.parent_pair_refinement hSSubFine hSCubical
      hFineMultiplicity hclose K hK hrhoAligned with
    ⟨chosen, paired, paired_sub, paired_cubical, paired_good,
      paired_multiplicity, paired_mass⟩
  let pairedCells : Finset (ℤ × ℤ × ℤ) :=
    (wz1PaperGridIndicesInWindow rho hrho).filter fun cell =>
      ∃ point ∈ paired.union, wz1PaperGridIndex rho point = cell
  have paired_support : ∀ point ∈ paired.union,
      wz1PaperGridIndex rho point ∈ pairedCells := by
    intro point point_mem
    apply Finset.mem_filter.mpr
    refine ⟨?_, point, point_mem, rfl⟩
    rcases point_mem with ⟨index, index_mem⟩
    exact paper_point_gridIndex_in_window hrho
      (S.subset_body index (paired_sub index index_mem)).2
  let firstDirection : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    wz1PaperDirection (coarse.tube (chosen cell).1)
  let secondDirection : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    wz1PaperDirection (coarse.tube (chosen cell).2)
  have first_unit : ∀ cell, ‖firstDirection cell‖ = 1 := fun _ =>
    wz1PaperDirection_norm _
  have second_unit : ∀ cell, ‖secondDirection cell‖ = 1 := fun _ =>
    wz1PaperDirection_norm _
  have transverse : ∀ cell ∈ pairedCells,
      kappa - rho ≤ ‖wz1Cross (firstDirection cell)
        (secondDirection cell)‖ := by
    intro cell cell_mem
    rcases (Finset.mem_filter.mp cell_mem).2 with
      ⟨point, point_mem, point_cell⟩
    rcases paired_good point point_mem with
      ⟨first, second, first_mem, second_mem, first_parent, second_parent,
        fine_transverse⟩
    have first_cover : WZ1PaperTubeCovers
        (fine.tube first) (coarse.tube (chosen cell).1) := by
      have covered := selectedParent_covers cover first
      simpa [first_parent, point_cell] using covered
    have second_cover : WZ1PaperTubeCovers
        (fine.tube second) (coarse.tube (chosen cell).2) := by
      have covered := selectedParent_covers cover second
      simpa [second_parent, point_cell] using covered
    have fine_transverse_paper :
        kappa ≤ ‖wz1Cross (wz1PaperDirection (fine.tube first))
          (wz1PaperDirection (fine.tube second))‖ := by
      rw [← raw_cross_norm_eq_paper_cross_norm]
      exact fine_transverse
    simpa [firstDirection, secondDirection] using
      paper_cover_parent_pair_transverse first_cover second_cover
        fine_transverse_paper
  have plane_unit : ∀ point ∈ paired.union,
      ‖planeMap.planeMap point‖ = 1 := by
    intro point point_mem
    apply planeMap.unit point
    rcases point_mem with ⟨index, index_mem⟩
    exact ⟨index, paired_sub index index_mem⟩
  have parent_covers : ∀ point ∈ paired.union,
      ∃ first second : Fin fine.card,
        point ∈ S.carrier first ∧ point ∈ S.carrier second ∧
        WZ1PaperTubeCovers (fine.tube first)
          (coarse.tube
            (chosen (wz1PaperGridIndex rho point)).1) ∧
        WZ1PaperTubeCovers (fine.tube second)
          (coarse.tube
            (chosen (wz1PaperGridIndex rho point)).2) := by
    intro point point_mem
    rcases paired_good point point_mem with
      ⟨first, second, first_mem, second_mem, first_parent, second_parent, _⟩
    exact ⟨first, second, first_mem, second_mem, by
      simpa [first_parent] using selectedParent_covers cover first, by
      simpa [second_parent] using selectedParent_covers cover second⟩
  have first_incidence : ∀ point ∈ paired.union,
      |inner ℝ (planeMap.planeMap point)
        (firstDirection (wz1PaperGridIndex rho point))| ≤
          incidence + rho / 2 := by
    intro point point_mem
    rcases parent_covers point point_mem with
      ⟨first, _, first_mem, _, first_cover, _⟩
    have fine_incidence :
        |inner ℝ (wz1PaperDirection (fine.tube first))
          (planeMap.planeMap point)| ≤ incidence := by
      rw [← abs_inner_raw_eq_paperDirection]
      exact planeMap.incidence first point first_mem
    have coarse_incidence := paper_cover_parent_incidence
      first_cover (plane_unit point point_mem) fine_incidence
    rw [real_inner_comm]
    simpa [firstDirection] using coarse_incidence
  have second_incidence : ∀ point ∈ paired.union,
      |inner ℝ (planeMap.planeMap point)
        (secondDirection (wz1PaperGridIndex rho point))| ≤
          incidence + rho / 2 := by
    intro point point_mem
    rcases parent_covers point point_mem with
      ⟨_, second, _, second_mem, _, second_cover⟩
    have fine_incidence :
        |inner ℝ (wz1PaperDirection (fine.tube second))
          (planeMap.planeMap point)| ≤ incidence := by
      rw [← abs_inner_raw_eq_paperDirection]
      exact planeMap.incidence second point second_mem
    have coarse_incidence := paper_cover_parent_incidence
      second_cover (plane_unit point point_mem) fine_incidence
    rw [real_inner_comm]
    simpa [secondDirection] using coarse_incidence
  have grid_measurable : Measurable (wz1PaperGridIndex rho) := by
    have measurable_coordinates : Measurable (fun point : Point3 =>
        (⌊point 0 / rho⌋, ⌊point 1 / rho⌋,
          ⌊point 2 / rho⌋)) := by
      fun_prop
    convert measurable_coordinates using 1
    funext point
    simp [wz1PaperGridIndex, gridIndex]
  have grid_fine : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
      wz1PaperGridIndex rho first =
        wz1PaperGridIndex rho second :=
    fun first second fine_cell =>
      wz1PaperGridIndex_fine_to_coarse K hK hrhoAligned fine_cell
  have kappa_difference : 0 < kappa - rho := sub_pos.mpr hkappa
  have coarse_incidence_nonnegative : 0 ≤ incidence + rho / 2 := by
    positivity
  rcases paper_oriented_cell_refinement paired paired_cubical
      planeMap.planeMap planeMap.measurable
      (wz1PaperGridIndex rho) grid_measurable grid_fine hplaneCell
      pairedCells paired_support firstDirection secondDirection
      kappa_difference coarse_incidence_nonnegative hvariationScale
      first_unit second_unit transverse plane_unit first_incidence
      second_incidence with
    ⟨oriented, oriented_sub, oriented_cubical, cell_variation,
      oriented_multiplicity, oriented_mass⟩
  have hdelta : 0 < delta := by
    exact terminal.delta_pos
  rcases paper_aligned_nearby_cell_residue_refinement_cubical
      planeMap.planeMap hdelta hrho oriented_cubical
      K hK hrhoAligned cell_variation with
    ⟨selected, selected_sub_oriented, selected_cubical, variation,
      residue_multiplicity, residue_mass⟩
  have selected_sub : PaperIsSubshading selected S := fun index =>
    (selected_sub_oriented index).trans ((oriented_sub index).trans
      (paired_sub index))
  have selected_multiplicity : ∀ point ∈ selected.union,
      selected.pointMultiplicity point = S.pointMultiplicity point := by
    intro point point_mem
    have point_oriented : point ∈ oriented.union := by
      rcases point_mem with ⟨index, index_mem⟩
      exact ⟨index, selected_sub_oriented index index_mem⟩
    have point_paired : point ∈ paired.union := by
      rcases point_oriented with ⟨index, index_mem⟩
      exact ⟨index, oriented_sub index index_mem⟩
    exact (residue_multiplicity point point_mem).trans
      ((oriented_multiplicity point point_oriented).trans
        (paired_multiplicity point point_paired))
  refine ⟨selected, selected_sub, selected_cubical, variation,
    selected_multiplicity, ?_⟩
  let orientation : ENNReal :=
    (wz1OrientationCapCount
      (10 * (incidence + rho / 2) / (kappa - rho)) variationScale :
        ENNReal)
  calc
    ((terminal.fineDegreeFloor * terminal.muFine : ℕ) : ENNReal) ^ 2 *
          S.mass ≤
        (2 * (terminal.muFine : ENNReal) ^ 2) *
          ((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) ^ 2 *
            paired.mass := paired_mass
    _ ≤ (2 * (terminal.muFine : ENNReal) ^ 2) *
          ((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) ^ 2 *
            (orientation * oriented.mass) := by gcongr
    _ ≤ (2 * (terminal.muFine : ENNReal) ^ 2) *
          ((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) ^ 2 *
            (orientation * (27 * selected.mass)) := by gcongr
    _ = 27 * ((2 * (terminal.muFine : ENNReal) ^ 2) *
          ((terminal.regularity * terminal.muCoarse : ℕ) : ENNReal) ^ 2 *
          orientation) * selected.mass := by ring

/-- The mass-efficient target-scale conclusion after cancelling both terminal
multiplicity factors with the rich cross-degree inequality. -/
theorem Proposition63RichTerminalStickyData.asymmetric_variation
    {delta sigma outputLoss sourceLoss normalizationLoss
      variationScale kappa incidence : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    {S : WZ1PaperTubeShading rich.data.selected.family}
    (hSSubFine : PaperIsSubshading S rich.data.refined)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second)
    (hFineMultiplicity : ∀ point ∈ S.union,
      rich.terminal.fineDegreeFloor * rich.terminal.muFine ≤
        S.pointMultiplicity point)
    (hclose : ∀ point ∈ S.union, ∀ index,
      point ∈ S.carrier index →
        2 * paperCloseDirectionCount S point index kappa ≤
          rich.terminal.fineDegreeFloor * rich.terminal.muFine)
    (hincidenceNonnegative : 0 ≤ incidence)
    (hvariationScale : 0 < variationScale)
    (hkappa : rho.1 < kappa)
    (K : ℕ) (hK : 0 < K)
    (hrhoAligned : rho.1 = (K : ℝ) * delta) :
    ∃ selected : WZ1PaperTubeShading rich.data.selected.family,
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union, ∀ other ∈ selected.union,
        dist point other ≤ rho.1 →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ variationScale) ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      Kakeya.realRpowENN rho.1 (2 * outputLoss) * S.mass ≤
        27 * (2 *
          (wz1OrientationCapCount
            (10 * (incidence + rho.1 / 2) / (kappa - rho.1))
              variationScale : ENNReal)) * selected.mass := by
  rcases rich.terminal.asymmetric_variation hSSubFine hSCubical planeMap
      hplaneCell hFineMultiplicity hclose hincidenceNonnegative
      rich.data.coarse_extremal.delta_pos hvariationScale hkappa K hK
      hrhoAligned with
    ⟨selected, selected_sub, selected_cubical, variation,
      selected_multiplicity, selected_mass⟩
  refine ⟨selected, selected_sub, selected_cubical, variation,
    selected_multiplicity, ?_⟩
  let coarseMultiplicity : ℕ :=
    rich.terminal.regularity * rich.terminal.muCoarse
  have canceled : Kakeya.realRpowENN rho.1 outputLoss ^ 2 * S.mass ≤
      2 *
        ((wz1OrientationCapCount
          (10 * (incidence + rho.1 / 2) / (kappa - rho.1))
            variationScale : ENNReal) * (27 * selected.mass)) := by
    apply proposition63_terminal_parent_pair_cross_degree_cancel
      rich.terminal.muFine_pos
    · exact Nat.mul_pos rich.terminal.regularity_pos
        rich.terminal.muCoarse_pos
    · simpa only [coarseMultiplicity] using rich.cross_degree
    · calc
        ((rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) :
              ENNReal) ^ 2 * S.mass ≤
            27 * ((2 * (rich.terminal.muFine : ENNReal) ^ 2) *
              ((rich.terminal.regularity * rich.terminal.muCoarse : ℕ) :
                ENNReal) ^ 2 *
              (wz1OrientationCapCount
                (10 * (incidence + rho.1 / 2) / (kappa - rho.1))
                  variationScale : ENNReal)) * selected.mass := selected_mass
        _ = (2 * (rich.terminal.muFine : ENNReal) ^ 2) *
              (coarseMultiplicity : ENNReal) ^ 2 *
              ((wz1OrientationCapCount
                (10 * (incidence + rho.1 / 2) / (kappa - rho.1))
                  variationScale : ENNReal) * (27 * selected.mass)) := by
          dsimp only [coarseMultiplicity]
          ring
  calc
    Kakeya.realRpowENN rho.1 (2 * outputLoss) * S.mass =
        Kakeya.realRpowENN rho.1 outputLoss ^ 2 * S.mass := by
      rw [show 2 * outputLoss = outputLoss + outputLoss by ring,
        realRpowENN_add rich.data.coarse_extremal.delta_pos]
      ring
    _ ≤ 2 *
        ((wz1OrientationCapCount
          (10 * (incidence + rho.1 / 2) / (kappa - rho.1))
            variationScale : ENNReal) * (27 * selected.mass)) := canceled
    _ = 27 * (2 *
        (wz1OrientationCapCount
          (10 * (incidence + rho.1 / 2) / (kappa - rho.1))
            variationScale : ENNReal)) * selected.mass := by ring

end Kakeya.Assouad.PureWZ2

end
