import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma17RefinementLeafStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.CellMassDecomposition

/-!
# Whole-cell fine pullback infrastructure for WZ1 Lemma 17

This module constructs the literal same-family restriction used by the fine
parent-cell pullback leaf.  A fine point is retained exactly when its coarse
parent has a point of the supplied coarse shading in the same balanced cell.
-/

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Kakeya.Assouad

/-- Restrict the fine shading to parent-cell fibers touched by `coarse`. -/
def fineParentCellPullbackShading
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho)) :
    Kakeya.Streamlined.TubeShading F :=
  let touchedCells
      (parent : Fin (U.coarse rho).card) :
      Set (Fin balanced.cellCount) :=
    balanced.cell '' coarse.carrier parent
  { carrier := fun index =>
      balanced.refined.carrier index ∩
        balanced.cell ⁻¹'
          touchedCells ((U.cover rho).parent index)
    measurable_carrier := by
      intro index
      have htouched :
          MeasurableSet
            (touchedCells ((U.cover rho).parent index)) := by
        simpa [touchedCells] using inferInstance
      exact
        (balanced.refined.measurable_carrier index).inter
          (balanced.cell_measurable htouched)
    subset_body := fun index =>
      Set.inter_subset_left.trans
        (balanced.refined.subset_body index) }

@[simp]
lemma fineParentCellPullbackShading_carrier
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (index : Fin F.card) :
    (fineParentCellPullbackShading balanced coarse).carrier index =
      balanced.refined.carrier index ∩
        balanced.cell ⁻¹'
          (balanced.cell ''
            coarse.carrier ((U.cover rho).parent index)) :=
  rfl

/-- The whole-cell pullback is a subshading of the balanced fine shading. -/
lemma fineParentCellPullbackShading_subshading
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho)) :
    IsSubshading
      (fineParentCellPullbackShading balanced coarse)
      balanced.refined :=
  fun _ => Set.inter_subset_left

/--
Every retained fine point has an actual coarse witness with the same parent
and the same balanced cell.
-/
lemma fineParentCellPullbackShading_support
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho)) :
    ∀ index point,
      point ∈
          (fineParentCellPullbackShading balanced coarse).carrier
            index →
        ∃ witness,
          witness ∈
              coarse.carrier ((U.cover rho).parent index) ∧
            balanced.cell witness = balanced.cell point := by
  intro index point hpoint
  rcases hpoint.2 with ⟨witness, hwitness, hcell⟩
  exact ⟨witness, hwitness, hcell⟩

/-- Fine shaded mass carried by one actual coarse-parent/cell pair. -/
def fineParentCellPairMass
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (parent : Fin (U.coarse rho).card)
    (cell : Fin balanced.cellCount) : ENNReal :=
  ∑ index ∈ (U.cover rho).toFactoring.fiberIndices parent,
    MeasureTheory.volume
      (balanced.refined.carrier index ∩
        {point | balanced.cell point = cell})

/-- Parent-cell pairs occupied by the balanced coarse shading. -/
def activeParentCells
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho) :
    Finset
      (Fin (U.coarse rho).card × Fin balanced.cellCount) :=
  Finset.univ.filter fun pair =>
    {point |
      point ∈ balanced.coarseShading.carrier pair.1 ∧
        balanced.cell point = pair.2}.Nonempty

/-- Parent-cell pairs touched by a supplied coarse subshading. -/
def touchedParentCells
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho)) :
    Finset
      (Fin (U.coarse rho).card × Fin balanced.cellCount) :=
  Finset.univ.filter fun pair =>
    {point |
      point ∈ coarse.carrier pair.1 ∧
        balanced.cell point = pair.2}.Nonempty

@[simp]
lemma mem_activeParentCells
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (pair :
      Fin (U.coarse rho).card × Fin balanced.cellCount) :
    pair ∈ activeParentCells balanced ↔
      {point |
        point ∈ balanced.coarseShading.carrier pair.1 ∧
          balanced.cell point = pair.2}.Nonempty := by
  simp [activeParentCells]

@[simp]
lemma mem_touchedParentCells
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (pair :
      Fin (U.coarse rho).card × Fin balanced.cellCount) :
    pair ∈ touchedParentCells balanced coarse ↔
      {point |
        point ∈ coarse.carrier pair.1 ∧
          balanced.cell point = pair.2}.Nonempty := by
  simp [touchedParentCells]

private lemma sum_fiberIndices_eq_sum
    {fine coarse : Kakeya.Streamlined.BodyFamily}
    (factoring : Kakeya.Streamlined.Factoring fine coarse)
    (weight : Fin fine.card → ENNReal) :
    ∑ parent : Fin coarse.card,
        ∑ index ∈ factoring.fiberIndices parent, weight index =
      ∑ index : Fin fine.card, weight index := by
  have hdisjoint :
      Set.PairwiseDisjoint
        (↑(Finset.univ : Finset (Fin coarse.card)))
        factoring.fiberIndices := by
    intro first _ second _ hne
    change
      Disjoint
        (factoring.fiberIndices first)
        (factoring.fiberIndices second)
    rw [Finset.disjoint_left]
    intro index hfirst hsecond
    have hfirstParent :
        factoring.parent index = first :=
      (Finset.mem_filter.mp hfirst).2
    have hsecondParent :
        factoring.parent index = second :=
      (Finset.mem_filter.mp hsecond).2
    exact hne (hfirstParent.symm.trans hsecondParent)
  have hunion :
      Finset.biUnion
          (Finset.univ : Finset (Fin coarse.card))
          factoring.fiberIndices =
        Finset.univ := by
    ext index
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact
      ⟨fun _ => trivial,
        fun _ =>
          ⟨factoring.parent index,
            by
              simp [Kakeya.Streamlined.Factoring.fiberIndices]⟩⟩
  calc
    ∑ parent : Fin coarse.card,
        ∑ index ∈ factoring.fiberIndices parent, weight index =
        ∑ index ∈
            Finset.biUnion
              (Finset.univ : Finset (Fin coarse.card))
              factoring.fiberIndices,
          weight index := by
            rw [Finset.sum_biUnion hdisjoint]
    _ = ∑ index : Fin fine.card, weight index := by
          rw [hunion]

private lemma refined_carrier_volume_cell_decomposition
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (index : Fin F.card) :
    MeasureTheory.volume (balanced.refined.carrier index) =
      ∑ cell : Fin balanced.cellCount,
        MeasureTheory.volume
          (balanced.refined.carrier index ∩
            {point | balanced.cell point = cell}) := by
  let cellSlice : Fin balanced.cellCount → Set Point3 :=
    fun cell => {point | balanced.cell point = cell}
  let pieces : Fin balanced.cellCount → Set Point3 :=
    fun cell => balanced.refined.carrier index ∩ cellSlice cell
  have hdisjoint :
      Set.PairwiseDisjoint
        (↑(Finset.univ : Finset (Fin balanced.cellCount)))
        pieces := by
    intro first _ second _ hne
    change Disjoint (pieces first) (pieces second)
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    exact hne (hfirst.2.symm.trans hsecond.2)
  have hmeasurable :
      ∀ cell ∈ (Finset.univ : Finset (Fin balanced.cellCount)),
        MeasurableSet (pieces cell) := by
    intro cell _
    exact
      (balanced.refined.measurable_carrier index).inter
        (balanced.cell_measurable (MeasurableSet.singleton cell))
  have hcover :
      balanced.refined.carrier index =
        ⋃ cell : Fin balanced.cellCount, pieces cell := by
    ext point
    simp only [pieces, cellSlice, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    exact
      ⟨fun hpoint => ⟨balanced.cell point, hpoint, rfl⟩,
        fun hpoint => hpoint.choose_spec.1⟩
  have hmeasure :
      MeasureTheory.volume
          (⋃ cell : Fin balanced.cellCount, pieces cell) =
        ∑ cell : Fin balanced.cellCount,
          MeasureTheory.volume (pieces cell) := by
    have hfinite :
        MeasureTheory.volume
            (⋃ cell ∈
              (Finset.univ : Finset (Fin balanced.cellCount)),
                pieces cell) =
          ∑ cell ∈
              (Finset.univ : Finset (Fin balanced.cellCount)),
            MeasureTheory.volume (pieces cell) :=
      MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
    simpa [Set.biUnion_univ, Finset.mem_univ] using hfinite
  calc
    MeasureTheory.volume (balanced.refined.carrier index) =
        MeasureTheory.volume
          (⋃ cell : Fin balanced.cellCount, pieces cell) := by
          rw [hcover]
    _ = ∑ cell : Fin balanced.cellCount,
          MeasureTheory.volume (pieces cell) := hmeasure
    _ = ∑ cell : Fin balanced.cellCount,
          MeasureTheory.volume
            (balanced.refined.carrier index ∩
              {point | balanced.cell point = cell}) := by
          rfl

/-- The refined mass is the sum of all actual parent-cell pair masses. -/
lemma refined_mass_eq_sum_fineParentCellPairMass
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho) :
    balanced.refined.mass =
      ∑ pair :
          Fin (U.coarse rho).card × Fin balanced.cellCount,
        fineParentCellPairMass balanced pair.1 pair.2 := by
  let factoring := (U.cover rho).toFactoring
  have hproduct :
      (∑ pair :
          Fin (U.coarse rho).card × Fin balanced.cellCount,
        fineParentCellPairMass balanced pair.1 pair.2) =
        ∑ parent : Fin (U.coarse rho).card,
          ∑ cell : Fin balanced.cellCount,
            fineParentCellPairMass balanced parent cell := by
    calc
      (∑ pair :
          Fin (U.coarse rho).card × Fin balanced.cellCount,
        fineParentCellPairMass balanced pair.1 pair.2) =
          ∑ pair ∈
              (Finset.univ : Finset (Fin (U.coarse rho).card)) ×ˢ
                (Finset.univ : Finset (Fin balanced.cellCount)),
            fineParentCellPairMass balanced pair.1 pair.2 := by
              rw [Finset.univ_product_univ]
      _ = ∑ parent : Fin (U.coarse rho).card,
            ∑ cell : Fin balanced.cellCount,
              fineParentCellPairMass balanced parent cell := by
            rw [Finset.sum_product]
  rw [hproduct]
  change
    (∑ index : Fin F.card,
        MeasureTheory.volume (balanced.refined.carrier index)) =
      ∑ parent : Fin (U.coarse rho).card,
        ∑ cell : Fin balanced.cellCount,
          ∑ index ∈ factoring.fiberIndices parent,
            MeasureTheory.volume
              (balanced.refined.carrier index ∩
                {point | balanced.cell point = cell})
  calc
    ∑ index : Fin F.card,
        MeasureTheory.volume (balanced.refined.carrier index) =
        ∑ index : Fin F.card,
          ∑ cell : Fin balanced.cellCount,
            MeasureTheory.volume
              (balanced.refined.carrier index ∩
                {point | balanced.cell point = cell}) := by
          apply Finset.sum_congr rfl
          intro index _
          exact refined_carrier_volume_cell_decomposition balanced index
    _ =
        ∑ parent : Fin (U.coarse rho).card,
          ∑ index ∈ factoring.fiberIndices parent,
            ∑ cell : Fin balanced.cellCount,
              MeasureTheory.volume
                (balanced.refined.carrier index ∩
                  {point | balanced.cell point = cell}) := by
          symm
          exact sum_fiberIndices_eq_sum factoring _
    _ =
        ∑ parent : Fin (U.coarse rho).card,
          ∑ cell : Fin balanced.cellCount,
            ∑ index ∈ factoring.fiberIndices parent,
              MeasureTheory.volume
                (balanced.refined.carrier index ∩
                  {point | balanced.cell point = cell}) := by
          apply Finset.sum_congr rfl
          intro parent _
          rw [Finset.sum_comm]

/--
Inactive parent-cell pairs carry no refined mass, so the all-pair
decomposition restricts exactly to the active pairs.
-/
lemma refined_mass_eq_sum_activeParentCells
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho) :
    balanced.refined.mass =
      ∑ pair ∈ activeParentCells balanced,
        fineParentCellPairMass balanced pair.1 pair.2 := by
  have hzero :
      ∀ pair :
          Fin (U.coarse rho).card × Fin balanced.cellCount,
        pair ∉ activeParentCells balanced →
          fineParentCellPairMass balanced pair.1 pair.2 = 0 := by
    intro pair hinactive
    apply Finset.sum_eq_zero
    intro index hindex
    have hparent :
        (U.cover rho).parent index = pair.1 := by
      have hparent' := (Finset.mem_filter.mp hindex).2
      change (U.cover rho).parent index = pair.1 at hparent'
      exact hparent'
    have hempty :
        balanced.refined.carrier index ∩
            {point | balanced.cell point = pair.2} =
          ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨point, hpoint⟩
      apply hinactive
      rw [mem_activeParentCells]
      exact
        ⟨point,
          by
            simpa [hparent] using
              balanced.point_compatibility index point hpoint.1,
          hpoint.2⟩
    rw [hempty]
    simp
  rw [refined_mass_eq_sum_fineParentCellPairMass balanced]
  symm
  exact
    Finset.sum_subset
      (Finset.subset_univ (activeParentCells balanced))
      (fun pair _ hinactive => hzero pair hinactive)

/--
A coarse subshading can only touch parent-cell pairs already active in the
balanced coarse shading.
-/
lemma touchedParentCells_subset_activeParentCells
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (hcoarse : IsSubshading coarse balanced.coarseShading) :
    touchedParentCells balanced coarse ⊆
      activeParentCells balanced := by
  intro pair htouched
  rw [mem_touchedParentCells] at htouched
  rw [mem_activeParentCells]
  rcases htouched with ⟨point, hpoint, hcell⟩
  exact ⟨point, hcoarse pair.1 hpoint, hcell⟩

private lemma fineParentCellPullback_carrier_volume
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (index : Fin F.card) :
    MeasureTheory.volume
        ((fineParentCellPullbackShading balanced coarse).carrier index) =
      ∑ cell ∈
          (Finset.univ : Finset (Fin balanced.cellCount)).filter
            (fun cell =>
              ((U.cover rho).parent index, cell) ∈
                touchedParentCells balanced coarse),
        MeasureTheory.volume
          (balanced.refined.carrier index ∩
            {point | balanced.cell point = cell}) := by
  let selectedCells : Finset (Fin balanced.cellCount) :=
    (Finset.univ : Finset (Fin balanced.cellCount)).filter
      (fun cell =>
        ((U.cover rho).parent index, cell) ∈
          touchedParentCells balanced coarse)
  let pieces : Fin balanced.cellCount → Set Point3 :=
    fun cell =>
      balanced.refined.carrier index ∩
        {point | balanced.cell point = cell}
  have hdisjoint :
      Set.PairwiseDisjoint (↑selectedCells) pieces := by
    intro first _ second _ hne
    change Disjoint (pieces first) (pieces second)
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    exact hne (hfirst.2.symm.trans hsecond.2)
  have hmeasurable :
      ∀ cell ∈ selectedCells, MeasurableSet (pieces cell) := by
    intro cell _
    exact
      (balanced.refined.measurable_carrier index).inter
        (balanced.cell_measurable (MeasurableSet.singleton cell))
  have hcover :
      (fineParentCellPullbackShading balanced coarse).carrier index =
        ⋃ cell ∈ selectedCells, pieces cell := by
    ext point
    constructor
    · intro hpoint
      rcases
          fineParentCellPullbackShading_support
            balanced coarse index point hpoint with
        ⟨witness, hwitness, hcell⟩
      have htouched :
          ((U.cover rho).parent index, balanced.cell point) ∈
            touchedParentCells balanced coarse := by
        rw [mem_touchedParentCells]
        exact ⟨witness, hwitness, hcell⟩
      exact
        Set.mem_iUnion₂.mpr
          ⟨balanced.cell point,
            by simpa [selectedCells] using htouched,
            hpoint.1, rfl⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcellSelected, hpointRefined, hpointCell⟩
      have htouched :
          ((U.cover rho).parent index, cell) ∈
            touchedParentCells balanced coarse := by
        simpa [selectedCells] using hcellSelected
      rw [mem_touchedParentCells] at htouched
      rcases htouched with ⟨witness, hwitness, hwitnessCell⟩
      exact
        ⟨hpointRefined,
          ⟨witness, hwitness,
            hwitnessCell.trans hpointCell.symm⟩⟩
  rw [hcover]
  have hmeasure :
      MeasureTheory.volume (⋃ cell ∈ selectedCells, pieces cell) =
        ∑ cell ∈ selectedCells,
          MeasureTheory.volume (pieces cell) :=
    MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
  simpa [selectedCells, pieces] using hmeasure

/--
The whole-cell pullback mass is exactly the sum of the original fine masses
over the actual parent-cell pairs touched by the coarse shading.
-/
lemma fineParentCellPullback_mass_eq_sum_touchedParentCells
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho)) :
    (fineParentCellPullbackShading balanced coarse).mass =
      ∑ pair ∈ touchedParentCells balanced coarse,
        fineParentCellPairMass balanced pair.1 pair.2 := by
  let factoring := (U.cover rho).toFactoring
  let selectedCells :
      Fin (U.coarse rho).card →
        Finset (Fin balanced.cellCount) :=
    fun parent =>
      (Finset.univ : Finset (Fin balanced.cellCount)).filter
        (fun cell =>
          (parent, cell) ∈ touchedParentCells balanced coarse)
  have hpairs :
      (∑ pair ∈ touchedParentCells balanced coarse,
          fineParentCellPairMass balanced pair.1 pair.2) =
        ∑ parent : Fin (U.coarse rho).card,
          ∑ cell ∈ selectedCells parent,
            fineParentCellPairMass balanced parent cell := by
    calc
      (∑ pair ∈ touchedParentCells balanced coarse,
          fineParentCellPairMass balanced pair.1 pair.2) =
          ∑ pair :
              Fin (U.coarse rho).card × Fin balanced.cellCount,
            if pair ∈ touchedParentCells balanced coarse then
              fineParentCellPairMass balanced pair.1 pair.2
            else 0 := by
              rw [← Finset.sum_filter]
              congr 1
              ext pair
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      _ = ∑ pair ∈
              (Finset.univ : Finset (Fin (U.coarse rho).card)) ×ˢ
                (Finset.univ : Finset (Fin balanced.cellCount)),
            if pair ∈ touchedParentCells balanced coarse then
              fineParentCellPairMass balanced pair.1 pair.2
            else 0 := by
              rw [Finset.univ_product_univ]
      _ = ∑ parent : Fin (U.coarse rho).card,
            ∑ cell : Fin balanced.cellCount,
              if (parent, cell) ∈
                  touchedParentCells balanced coarse then
                fineParentCellPairMass balanced parent cell
              else 0 := by
            rw [Finset.sum_product]
      _ = ∑ parent : Fin (U.coarse rho).card,
            ∑ cell ∈ selectedCells parent,
              fineParentCellPairMass balanced parent cell := by
            apply Finset.sum_congr rfl
            intro parent _
            rw [Finset.sum_filter]
  rw [hpairs]
  change
    (∑ index : Fin F.card,
      MeasureTheory.volume
        ((fineParentCellPullbackShading balanced coarse).carrier index)) =
      ∑ parent : Fin (U.coarse rho).card,
        ∑ cell ∈ selectedCells parent,
          ∑ index ∈ factoring.fiberIndices parent,
            MeasureTheory.volume
              (balanced.refined.carrier index ∩
                {point | balanced.cell point = cell})
  calc
    (∑ index : Fin F.card,
      MeasureTheory.volume
        ((fineParentCellPullbackShading balanced coarse).carrier index)) =
        ∑ index : Fin F.card,
          ∑ cell ∈ selectedCells ((U.cover rho).parent index),
            MeasureTheory.volume
              (balanced.refined.carrier index ∩
                {point | balanced.cell point = cell}) := by
          apply Finset.sum_congr rfl
          intro index _
          simpa [selectedCells] using
            fineParentCellPullback_carrier_volume
              balanced coarse index
    _ = ∑ parent : Fin (U.coarse rho).card,
          ∑ index ∈ factoring.fiberIndices parent,
            ∑ cell ∈ selectedCells parent,
              MeasureTheory.volume
                (balanced.refined.carrier index ∩
                  {point | balanced.cell point = cell}) := by
          symm
          calc
            ∑ parent : Fin (U.coarse rho).card,
                ∑ index ∈ factoring.fiberIndices parent,
                  ∑ cell ∈ selectedCells parent,
                    MeasureTheory.volume
                      (balanced.refined.carrier index ∩
                        {point | balanced.cell point = cell}) =
                ∑ parent : Fin (U.coarse rho).card,
                  ∑ index ∈ factoring.fiberIndices parent,
                    ∑ cell ∈
                        selectedCells (factoring.parent index),
                      MeasureTheory.volume
                        (balanced.refined.carrier index ∩
                          {point | balanced.cell point = cell}) := by
              apply Finset.sum_congr rfl
              intro parent _
              apply Finset.sum_congr rfl
              intro index hindex
              have hparent := (Finset.mem_filter.mp hindex).2
              rw [hparent]
            _ = ∑ index : Fin F.card,
                  ∑ cell ∈
                      selectedCells (factoring.parent index),
                    MeasureTheory.volume
                      (balanced.refined.carrier index ∩
                        {point | balanced.cell point = cell}) :=
              sum_fiberIndices_eq_sum factoring _
    _ = ∑ parent : Fin (U.coarse rho).card,
          ∑ cell ∈ selectedCells parent,
            ∑ index ∈ factoring.fiberIndices parent,
              MeasureTheory.volume
                (balanced.refined.carrier index ∩
                  {point | balanced.cell point = cell}) := by
          apply Finset.sum_congr rfl
          intro parent _
          rw [Finset.sum_comm]

/--
The aggregate fine shaded mass in one active parent-cell pair is comparable
to `fiberMultiplicity * fiberCellMass`.
-/
lemma fineParentCellFiber_mass_bounds
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (parent : Fin (U.coarse rho).card)
    (cell : Fin balanced.cellCount)
    (hactive :
      {point |
        point ∈ balanced.coarseShading.carrier parent ∧
          balanced.cell point = cell}.Nonempty) :
    let factoring := (U.cover rho).toFactoring
    let cellSet := {point : Point3 | balanced.cell point = cell}
    let pairMass :=
      ∑ index ∈ factoring.fiberIndices parent,
        MeasureTheory.volume
          (balanced.refined.carrier index ∩ cellSet)
    (balanced.fiberMultiplicity : ENNReal) *
          balanced.fiberCellMass ≤ pairMass ∧
      pairMass ≤
        (4 * balanced.fiberMultiplicity : ENNReal) *
          balanced.fiberCellMass := by
  let factoring := (U.cover rho).toFactoring
  let cellSet : Set Point3 :=
    {point | balanced.cell point = cell}
  let fiberUnion :=
    factoring.fiberShadedUnion balanced.refined parent ∩ cellSet
  let multiplicity : Point3 → ENNReal := fun point =>
    (factoring.fiberPointMultiplicity
      balanced.refined parent point : ENNReal)
  have hcellMeasurable : MeasurableSet cellSet :=
    balanced.cell_measurable (MeasurableSet.singleton cell)
  have hfiberMeasurable :
      MeasurableSet
        (factoring.fiberShadedUnion balanced.refined parent) := by
    have hfiber :
        factoring.fiberShadedUnion balanced.refined parent =
          ⋃ index ∈
              (factoring.fiberIndices parent :
                Set (Fin F.toBodyFamily.card)),
            balanced.refined.carrier index := by
      ext point
      simp [Kakeya.Streamlined.Factoring.fiberShadedUnion,
        Kakeya.Streamlined.Factoring.fiberIndices]
    rw [hfiber]
    exact
      MeasurableSet.biUnion
        (Finset.countable_toSet (factoring.fiberIndices parent))
        (fun index _ => balanced.refined.measurable_carrier index)
  have hfiberUnionMeasurable : MeasurableSet fiberUnion :=
    hfiberMeasurable.inter hcellMeasurable
  have hmultiplicity :
      ∀ point ∈ fiberUnion,
        (balanced.fiberMultiplicity : ENNReal) ≤
            multiplicity point ∧
          multiplicity point ≤
            (2 * balanced.fiberMultiplicity : ENNReal) := by
    intro point hpoint
    have hraw :=
      balanced.fiber_constant_multiplicity parent point hpoint.1
    have hlower :
        (balanced.fiberMultiplicity : ENNReal) ≤
          (factoring.fiberPointMultiplicity
            balanced.refined parent point : ENNReal) := by
      exact_mod_cast hraw.1
    have hupper :
        (factoring.fiberPointMultiplicity
            balanced.refined parent point : ENNReal) ≤
          (2 * balanced.fiberMultiplicity : ENNReal) := by
      exact_mod_cast hraw.2
    exact
      ⟨by simpa [multiplicity] using hlower,
        by simpa [multiplicity] using hupper⟩
  have hmultiplicityZero :
      ∀ point,
        point ∉
            factoring.fiberShadedUnion balanced.refined parent →
          multiplicity point = 0 := by
    intro point hpoint
    have hempty :
        (factoring.fiberIndices parent).filter
            (fun index => point ∈ balanced.refined.carrier index) =
          ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro index hindex hpointIndex
      apply hpoint
      exact ⟨index,
        by simpa [Kakeya.Streamlined.Factoring.fiberIndices] using hindex,
        hpointIndex⟩
    simp [multiplicity,
      Kakeya.Streamlined.Factoring.fiberPointMultiplicity, hempty]
  have hindicator :
      Set.indicator cellSet multiplicity =
        Set.indicator fiberUnion multiplicity := by
    funext point
    by_cases hpoint : point ∈ fiberUnion
    · simp [hpoint, hpoint.2]
    · by_cases hcell : point ∈ cellSet
      · have hzero : multiplicity point = 0 := by
          apply hmultiplicityZero
          intro hfiber
          exact hpoint ⟨hfiber, hcell⟩
        simp [hpoint, hcell, hzero]
      · simp [hpoint, hcell]
  have hmultiplicitySum :
      ∀ point,
        multiplicity point =
          ∑ index ∈ factoring.fiberIndices parent,
            Set.indicator
              (balanced.refined.carrier index)
              (fun _ => (1 : ENNReal)) point := by
    intro point
    simp [multiplicity,
      Kakeya.Streamlined.Factoring.fiberPointMultiplicity,
      Set.indicator_apply, Finset.sum_ite]
  have hsum :
      ∫⁻ point in cellSet, multiplicity point =
        ∑ index ∈ factoring.fiberIndices parent,
          MeasureTheory.volume
            (balanced.refined.carrier index ∩ cellSet) := by
    calc
      ∫⁻ point in cellSet, multiplicity point =
          ∫⁻ point in cellSet,
            ∑ index ∈ factoring.fiberIndices parent,
              Set.indicator
                (balanced.refined.carrier index)
                (fun _ => (1 : ENNReal)) point := by
            congr 1
            funext point
            exact hmultiplicitySum point
      _ = ∑ index ∈ factoring.fiberIndices parent,
            ∫⁻ point in cellSet,
              Set.indicator
                (balanced.refined.carrier index)
                (fun _ => (1 : ENNReal)) point := by
            rw [MeasureTheory.lintegral_finsetSum]
            intro index _
            exact
              measurable_const.indicator
                (balanced.refined.measurable_carrier index)
      _ = ∑ index ∈ factoring.fiberIndices parent,
            MeasureTheory.volume
              (balanced.refined.carrier index ∩ cellSet) := by
            apply Finset.sum_congr rfl
            intro index _
            rw [MeasureTheory.setLIntegral_indicator
              (balanced.refined.measurable_carrier index)]
            simp [MeasureTheory.setLIntegral_const]
  have hintegralEq :
      ∫⁻ point in cellSet, multiplicity point =
        ∫⁻ point in fiberUnion, multiplicity point := by
    rw [← MeasureTheory.lintegral_indicator hcellMeasurable]
    rw [← MeasureTheory.lintegral_indicator hfiberUnionMeasurable]
    rw [hindicator]
  have hlower :
      (balanced.fiberMultiplicity : ENNReal) *
          MeasureTheory.volume fiberUnion ≤
        ∫⁻ point in fiberUnion, multiplicity point := by
    calc
      (balanced.fiberMultiplicity : ENNReal) *
          MeasureTheory.volume fiberUnion =
          ∫⁻ _point in fiberUnion,
            (balanced.fiberMultiplicity : ENNReal) := by
              rw [MeasureTheory.setLIntegral_const]
      _ ≤ ∫⁻ point in fiberUnion, multiplicity point := by
            exact MeasureTheory.setLIntegral_mono'
              hfiberUnionMeasurable
              (fun point hpoint => (hmultiplicity point hpoint).1)
  have hupper :
      (∫⁻ point in fiberUnion, multiplicity point) ≤
        (2 * balanced.fiberMultiplicity : ENNReal) *
          MeasureTheory.volume fiberUnion := by
    calc
      (∫⁻ point in fiberUnion, multiplicity point) ≤
          ∫⁻ _point in fiberUnion,
            (2 * balanced.fiberMultiplicity : ENNReal) := by
              exact MeasureTheory.setLIntegral_mono'
                hfiberUnionMeasurable
                (fun point hpoint => (hmultiplicity point hpoint).2)
      _ = (2 * balanced.fiberMultiplicity : ENNReal) *
            MeasureTheory.volume fiberUnion := by
              rw [MeasureTheory.setLIntegral_const]
  have hbalance :=
    balanced.fiber_cell_balance parent cell hactive
  have hbalance' :
      balanced.fiberCellMass ≤
          MeasureTheory.volume fiberUnion ∧
        MeasureTheory.volume fiberUnion ≤
          2 * balanced.fiberCellMass := by
    simpa [fiberUnion, cellSet, factoring] using hbalance
  dsimp only
  rw [← hsum, hintegralEq]
  exact
    ⟨
      (by
        calc
          (balanced.fiberMultiplicity : ENNReal) *
              balanced.fiberCellMass ≤
              (balanced.fiberMultiplicity : ENNReal) *
                MeasureTheory.volume fiberUnion := by
                  gcongr
                  exact hbalance'.1
          _ ≤ ∫⁻ point in fiberUnion, multiplicity point := hlower),
      hupper.trans <| by
        calc
          (2 * balanced.fiberMultiplicity : ENNReal) *
              MeasureTheory.volume fiberUnion ≤
              (2 * balanced.fiberMultiplicity : ENNReal) *
                (2 * balanced.fiberCellMass) := by
                  gcongr
                  exact hbalance'.2
          _ = (4 * balanced.fiberMultiplicity : ENNReal) *
                balanced.fiberCellMass := by ring
    ⟩

/--
A cardinality proportion between touched and active parent-cell pairs gives
the corresponding fine-mass retention, with the factor four coming exactly
from `fiber_cell_balance` and fiber constant multiplicity.
-/
lemma fineParentCellPullback_mass_retention_of_cardinality
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (hcoarse : IsSubshading coarse balanced.coarseShading)
    (retention : ENNReal)
    (hcard :
      retention *
          (4 * ((activeParentCells balanced).card : ENNReal)) ≤
        ((touchedParentCells balanced coarse).card : ENNReal)) :
    retention * balanced.refined.mass ≤
      (fineParentCellPullbackShading balanced coarse).mass := by
  let pairScale : ENNReal :=
    (balanced.fiberMultiplicity : ENNReal) *
      balanced.fiberCellMass
  have hactiveUpper :
      ∀ pair ∈ activeParentCells balanced,
        fineParentCellPairMass balanced pair.1 pair.2 ≤
          4 * pairScale := by
    intro pair hpair
    have hactive :
        {point |
          point ∈ balanced.coarseShading.carrier pair.1 ∧
            balanced.cell point = pair.2}.Nonempty :=
      (mem_activeParentCells balanced pair).mp hpair
    simpa [pairScale, fineParentCellPairMass, mul_assoc] using
      (fineParentCellFiber_mass_bounds
        balanced pair.1 pair.2 hactive).2
  have htouchedLower :
      ∀ pair ∈ touchedParentCells balanced coarse,
        pairScale ≤
          fineParentCellPairMass balanced pair.1 pair.2 := by
    intro pair hpair
    have hactiveMem :
        pair ∈ activeParentCells balanced :=
      touchedParentCells_subset_activeParentCells
        balanced coarse hcoarse hpair
    have hactive :
        {point |
          point ∈ balanced.coarseShading.carrier pair.1 ∧
            balanced.cell point = pair.2}.Nonempty :=
      (mem_activeParentCells balanced pair).mp hactiveMem
    simpa [pairScale, fineParentCellPairMass] using
      (fineParentCellFiber_mass_bounds
        balanced pair.1 pair.2 hactive).1
  have hrefinedUpper :
      balanced.refined.mass ≤
        ((activeParentCells balanced).card : ENNReal) *
          (4 * pairScale) := by
    rw [refined_mass_eq_sum_activeParentCells balanced]
    calc
      (∑ pair ∈ activeParentCells balanced,
          fineParentCellPairMass balanced pair.1 pair.2) ≤
          ∑ _pair ∈ activeParentCells balanced,
            4 * pairScale := by
              exact Finset.sum_le_sum hactiveUpper
      _ =
          ((activeParentCells balanced).card : ENNReal) *
            (4 * pairScale) := by
              simp [Finset.sum_const]
  have hpullbackLower :
      ((touchedParentCells balanced coarse).card : ENNReal) *
          pairScale ≤
        (fineParentCellPullbackShading balanced coarse).mass := by
    rw [fineParentCellPullback_mass_eq_sum_touchedParentCells
      balanced coarse]
    calc
      ((touchedParentCells balanced coarse).card : ENNReal) *
          pairScale =
          ∑ _pair ∈ touchedParentCells balanced coarse,
            pairScale := by
              simp [Finset.sum_const]
      _ ≤
          ∑ pair ∈ touchedParentCells balanced coarse,
            fineParentCellPairMass balanced pair.1 pair.2 := by
              exact Finset.sum_le_sum htouchedLower
  calc
    retention * balanced.refined.mass ≤
        retention *
          (((activeParentCells balanced).card : ENNReal) *
            (4 * pairScale)) := by
          gcongr
    _ =
        (retention *
          (4 * ((activeParentCells balanced).card : ENNReal))) *
            pairScale := by ring
    _ ≤
        ((touchedParentCells balanced coarse).card : ENNReal) *
          pairScale := by
          gcongr
    _ ≤
        (fineParentCellPullbackShading balanced coarse).mass :=
      hpullbackLower

end Kakeya.Assouad
