import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteLabelMassRefinement

/-!
# Cellwise finite-label mass refinement

For each cell of a finite active cell set, select the label carrying the
largest shaded mass in that cell.  Restricting to the selected label in every
cell loses at most the number of labels globally.  The cell type itself may be
infinite; only the supplied active `Finset` is summed.

Cubicality is kept as a separate conclusion.  It requires both the cell map
and the label map to be constant on fine grid cells.  This makes the grid
alignment obligation explicit rather than silently treating arbitrary
requested scales as dyadic.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Restrict to the label selected for the cell containing each point. -/
def paperCellwiseLabelRestriction
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label] [MeasurableEq Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (label : Point3 → Label) (hlabel : Measurable label)
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    WZ1PaperTubeShading F :=
  { carrier := fun i => S.carrier i ∩ {p | label p = chosen (cell p)}
    measurable_carrier := fun i => by
      have heq : MeasurableSet {p : Point3 | label p = chosen (cell p)} :=
        measurableSet_eq_fun hlabel (hchosen.comp hcell)
      exact (S.measurable_carrier i).inter heq
    subset_body := fun i =>
      Set.inter_subset_left.trans (S.subset_body i) }

lemma paperCellwiseLabelRestriction_subshading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label] [MeasurableEq Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (label : Point3 → Label) (hlabel : Measurable label)
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    PaperIsSubshading
      (paperCellwiseLabelRestriction S cell hcell label hlabel chosen hchosen) S :=
  fun _ => Set.inter_subset_left

lemma paperCellwiseLabelRestriction_selected
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label] [MeasurableEq Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (label : Point3 → Label) (hlabel : Measurable label)
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    ∀ p ∈ (paperCellwiseLabelRestriction
        S cell hcell label hlabel chosen hchosen).union,
      label p = chosen (cell p) := by
  intro p hp
  rcases hp with ⟨i, hi⟩
  exact hi.2

lemma paperCellwiseLabelRestriction_pointMultiplicity_eq
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label] [MeasurableEq Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (label : Point3 → Label) (hlabel : Measurable label)
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    ∀ p ∈ (paperCellwiseLabelRestriction
        S cell hcell label hlabel chosen hchosen).union,
      (paperCellwiseLabelRestriction
        S cell hcell label hlabel chosen hchosen).pointMultiplicity p =
        S.pointMultiplicity p := by
  intro p hp
  have hpLabel : label p = chosen (cell p) :=
    paperCellwiseLabelRestriction_selected
      S cell hcell label hlabel chosen hchosen p hp
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  ext i
  simp [paperCellwiseLabelRestriction, hpLabel]

/-- If both discrete labels are constant on each fine grid cell, the
cellwise-label restriction is cubical. -/
lemma paperCellwiseLabelRestriction_cubical
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label] [MeasurableEq Label]
    {S : WZ1PaperTubeShading F}
    (hS : WZ1PaperIsCubicalShading S)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (label : Point3 → Label) (hlabel : Measurable label)
    (chosen : Cell → Label) (hchosen : Measurable chosen)
    (hcellConst : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        cell p = cell q)
    (hlabelConst : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        label p = label q) :
    WZ1PaperIsCubicalShading
      (paperCellwiseLabelRestriction
        S cell hcell label hlabel chosen hchosen) := by
  intro i p hp q hq
  have hgrid :
      wz1PaperGridIndex delta q = wz1PaperGridIndex delta p :=
    (mem_wz1PaperGridCube delta (wz1PaperGridIndex delta p) q).mp hq
  have hqS : q ∈ S.carrier i := hS i p hp.1 hq
  have hcellEq : cell q = cell p := hcellConst q p hgrid
  have hlabelEq : label q = label p := hlabelConst q p hgrid
  exact ⟨hqS, by simpa [hcellEq, hlabelEq] using hp.2⟩

/-- Per-cell finite pigeonhole: select one label in each active cell while
losing at most the number of labels in total shaded mass. -/
theorem paper_cellwise_finite_label_mass_refinement
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [DecidableEq Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [MeasurableEq Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (activeCells : Finset Cell)
    (hsupport : ∀ p ∈ S.union, cell p ∈ activeCells)
    (label : Point3 → Label) (hlabel : Measurable label)
    (hmeasurableChosen : ∀ chosen : Cell → Label, Measurable chosen) :
    ∃ (chosen : Cell → Label) (selected : WZ1PaperTubeShading F),
      PaperIsSubshading selected S ∧
      selected = paperCellwiseLabelRestriction
        S cell hcell label hlabel chosen (hmeasurableChosen chosen) ∧
      (∀ p ∈ selected.union, label p = chosen (cell p)) ∧
      S.mass ≤ (Fintype.card Label : ENNReal) * selected.mass := by
  classical
  let cellSet (c : Cell) : Set Point3 := {p | cell p = c}
  have hcellSetMeasurable : ∀ c, MeasurableSet (cellSet c) := by
    intro c
    exact hcell (measurableSet_singleton c)
  let atom (c : Cell) (a : Label) : Set Point3 :=
    cellSet c ∩ {p | label p = a}
  have hatomMeasurable : ∀ c a, MeasurableSet (atom c a) := by
    intro c a
    exact (hcellSetMeasurable c).inter
      (hlabel (measurableSet_singleton a))
  let atomMass (c : Cell) (a : Label) : ENNReal :=
    ∑ i : Fin F.card, volume (S.carrier i ∩ atom c a)
  let cellMass (c : Cell) : ENNReal :=
    ∑ i : Fin F.card, volume (S.carrier i ∩ cellSet c)
  have hlabelPartition : ∀ c,
      cellMass c = ∑ a : Label, atomMass c a := by
    intro c
    dsimp only [cellMass, atomMass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    let piece : Label → Set Point3 := fun a => S.carrier i ∩ atom c a
    have hcover : S.carrier i ∩ cellSet c = ⋃ a : Label, piece a := by
      ext p
      simp [piece, atom]
    have hdisjoint :
        Set.PairwiseDisjoint (Finset.univ : Finset Label) piece := by
      intro first _ second _ hne
      change Disjoint (piece first) (piece second)
      rw [Set.disjoint_left]
      intro p hpFirst hpSecond
      exact hne (hpFirst.2.2.symm.trans hpSecond.2.2)
    have hmeasurable :
        ∀ a ∈ (Finset.univ : Finset Label), MeasurableSet (piece a) := by
      intro a _
      exact (S.measurable_carrier i).inter (hatomMeasurable c a)
    have hfinite :
        volume (⋃ a ∈ (Finset.univ : Finset Label), piece a) =
          ∑ a ∈ (Finset.univ : Finset Label), volume (piece a) :=
      MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
    have hindexed :
        (⋃ a : Label, piece a) =
          ⋃ a ∈ (Finset.univ : Finset Label), piece a := by
      ext p
      simp
    rw [hcover, hindexed, hfinite]
  have hchoice : ∀ c : Cell, ∃ a : Label,
      cellMass c ≤ (Fintype.card Label : ENNReal) * atomMass c a := by
    intro c
    rcases finset_ennreal_pigeonhole
        (s := (Finset.univ : Finset Label)) Finset.univ_nonempty
        (atomMass c) with ⟨a, _, ha⟩
    exact ⟨a, (hlabelPartition c).trans_le ha⟩
  choose chosen hchosen using hchoice
  let hchosenMeasurable : Measurable chosen := hmeasurableChosen chosen
  let selected := paperCellwiseLabelRestriction
    S cell hcell label hlabel chosen hchosenMeasurable
  have hcellPartition : S.mass = ∑ c ∈ activeCells, cellMass c := by
    calc
      S.mass = ∑ i : Fin F.card, volume (S.carrier i) := rfl
      _ = ∑ i : Fin F.card, ∑ c ∈ activeCells,
          volume (S.carrier i ∩ cellSet c) := by
            apply Finset.sum_congr rfl
            intro i _
            let piece : Cell → Set Point3 := fun c =>
              S.carrier i ∩ cellSet c
            have hcover :
                S.carrier i = ⋃ c ∈ activeCells, piece c := by
              ext p
              constructor
              · intro hp
                have hpa : cell p ∈ activeCells :=
                  hsupport p ⟨i, hp⟩
                exact Set.mem_iUnion.mpr ⟨cell p,
                  Set.mem_iUnion.mpr ⟨hpa, hp, rfl⟩⟩
              · intro hpUnion
                rcases Set.mem_iUnion.mp hpUnion with ⟨c, hpUnion⟩
                rcases Set.mem_iUnion.mp hpUnion with ⟨_hc, hpPiece⟩
                exact hpPiece.1
            have hdisjoint : Set.PairwiseDisjoint activeCells piece := by
              intro first _ second _ hne
              change Disjoint (piece first) (piece second)
              rw [Set.disjoint_left]
              intro p hpFirst hpSecond
              exact hne (hpFirst.2.symm.trans hpSecond.2)
            have hmeasurable :
                ∀ c ∈ activeCells, MeasurableSet (piece c) := by
              intro c _
              exact (S.measurable_carrier i).inter
                (hcellSetMeasurable c)
            calc
              volume (S.carrier i) =
                  volume (⋃ c ∈ activeCells, piece c) := by rw [hcover]
              _ = ∑ c ∈ activeCells, volume (piece c) :=
                MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
              _ = ∑ c ∈ activeCells,
                  volume (S.carrier i ∩ cellSet c) := by rfl
      _ = ∑ c ∈ activeCells, ∑ i : Fin F.card,
          volume (S.carrier i ∩ cellSet c) := by
            rw [Finset.sum_comm]
      _ = ∑ c ∈ activeCells, cellMass c := rfl
  have hselectedCellMass : selected.mass =
      ∑ c ∈ activeCells, atomMass c (chosen c) := by
    calc
      selected.mass = ∑ i : Fin F.card, volume (selected.carrier i) := rfl
      _ = ∑ i : Fin F.card, ∑ c ∈ activeCells,
          volume (S.carrier i ∩ atom c (chosen c)) := by
            apply Finset.sum_congr rfl
            intro i _
            let piece : Cell → Set Point3 := fun c =>
              S.carrier i ∩ atom c (chosen c)
            have hcover : selected.carrier i =
                ⋃ c ∈ activeCells, piece c := by
              ext p
              constructor
              · intro hp
                have hpS : p ∈ S.carrier i := hp.1
                have hpa : cell p ∈ activeCells :=
                  hsupport p ⟨i, hpS⟩
                exact Set.mem_iUnion.mpr ⟨cell p,
                  Set.mem_iUnion.mpr ⟨hpa, hpS, rfl, hp.2⟩⟩
              · intro hpUnion
                rcases Set.mem_iUnion.mp hpUnion with ⟨c, hpUnion⟩
                rcases Set.mem_iUnion.mp hpUnion with ⟨_hc, hpPiece⟩
                have hcellPoint : cell p = c := hpPiece.2.1
                have hlabelPoint : label p = chosen c := hpPiece.2.2
                exact ⟨hpPiece.1, by simpa [hcellPoint] using hlabelPoint⟩
            have hdisjoint : Set.PairwiseDisjoint activeCells piece := by
              intro first _ second _ hne
              change Disjoint (piece first) (piece second)
              rw [Set.disjoint_left]
              intro p hpFirst hpSecond
              exact hne (hpFirst.2.1.symm.trans hpSecond.2.1)
            have hmeasurable :
                ∀ c ∈ activeCells, MeasurableSet (piece c) := by
              intro c _
              exact (S.measurable_carrier i).inter
                (hatomMeasurable c (chosen c))
            calc
              volume (selected.carrier i) =
                  volume (⋃ c ∈ activeCells, piece c) := by rw [hcover]
              _ = ∑ c ∈ activeCells, volume (piece c) :=
                MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
              _ = ∑ c ∈ activeCells,
                  volume (S.carrier i ∩ atom c (chosen c)) := by rfl
      _ = ∑ c ∈ activeCells, ∑ i : Fin F.card,
          volume (S.carrier i ∩ atom c (chosen c)) := by
            rw [Finset.sum_comm]
      _ = ∑ c ∈ activeCells, atomMass c (chosen c) := rfl
  refine ⟨chosen, selected, ?_, rfl, ?_, ?_⟩
  · exact paperCellwiseLabelRestriction_subshading
      S cell hcell label hlabel chosen hchosenMeasurable
  · exact paperCellwiseLabelRestriction_selected
      S cell hcell label hlabel chosen hchosenMeasurable
  · rw [hcellPartition, hselectedCellMass]
    calc
      ∑ c ∈ activeCells, cellMass c
          ≤ ∑ c ∈ activeCells,
              (Fintype.card Label : ENNReal) * atomMass c (chosen c) := by
            apply Finset.sum_le_sum
            intro c _
            exact hchosen c
      _ = (Fintype.card Label : ENNReal) *
          ∑ c ∈ activeCells, atomMass c (chosen c) := by
            rw [Finset.mul_sum]

/-- Cellwise pigeonholing with a cell-dependent set of admissible labels.
Only the uniform bound `labelBound` on the local label-set cardinality is
lost; the cardinality of the ambient label type does not enter. -/
theorem paper_cellwise_bounded_label_mass_refinement
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [DecidableEq Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    [Nonempty Label] [DecidableEq Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [MeasurableEq Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (activeCells : Finset Cell)
    (hsupport : ∀ p ∈ S.union, cell p ∈ activeCells)
    (label : Point3 → Label) (hlabel : Measurable label)
    (allowed : Cell → Finset Label)
    (hallowedNonempty : ∀ c ∈ activeCells, (allowed c).Nonempty)
    (hlabelAllowed : ∀ p ∈ S.union, label p ∈ allowed (cell p))
    (labelBound : ENNReal)
    (hlabelBound : ∀ c ∈ activeCells, ((allowed c).card : ENNReal) ≤ labelBound)
    (hmeasurableChosen : ∀ chosen : Cell → Label, Measurable chosen) :
    ∃ (chosen : Cell → Label) (selected : WZ1PaperTubeShading F),
      PaperIsSubshading selected S ∧
      selected = paperCellwiseLabelRestriction
        S cell hcell label hlabel chosen (hmeasurableChosen chosen) ∧
      (∀ c ∈ activeCells, chosen c ∈ allowed c) ∧
      (∀ p ∈ selected.union, label p = chosen (cell p)) ∧
      S.mass ≤ labelBound * selected.mass := by
  classical
  let cellSet (c : Cell) : Set Point3 := {p | cell p = c}
  have hcellSetMeasurable : ∀ c, MeasurableSet (cellSet c) := by
    intro c
    exact hcell (measurableSet_singleton c)
  let atom (c : Cell) (a : Label) : Set Point3 :=
    cellSet c ∩ {p | label p = a}
  have hatomMeasurable : ∀ c a, MeasurableSet (atom c a) := by
    intro c a
    exact (hcellSetMeasurable c).inter
      (hlabel (measurableSet_singleton a))
  let atomMass (c : Cell) (a : Label) : ENNReal :=
    ∑ i : Fin F.card, volume (S.carrier i ∩ atom c a)
  let cellMass (c : Cell) : ENNReal :=
    ∑ i : Fin F.card, volume (S.carrier i ∩ cellSet c)
  have hallowedPartition : ∀ c ∈ activeCells,
      cellMass c = ∑ a ∈ allowed c, atomMass c a := by
    intro c hc
    dsimp only [cellMass, atomMass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    let piece : Label → Set Point3 := fun a =>
      S.carrier i ∩ atom c a
    have hcover : S.carrier i ∩ cellSet c =
        ⋃ a ∈ allowed c, piece a := by
      ext p
      constructor
      · intro hp
        have hpUnion : p ∈ S.union := ⟨i, hp.1⟩
        have hallowedAtPoint : label p ∈ allowed (cell p) :=
          hlabelAllowed p hpUnion
        have hcellPoint : cell p = c := hp.2
        have hallowedAtCell : label p ∈ allowed c := by
          simpa [hcellPoint] using hallowedAtPoint
        exact Set.mem_iUnion.mpr ⟨label p,
          Set.mem_iUnion.mpr ⟨hallowedAtCell, hp.1, hp.2, rfl⟩⟩
      · intro hpUnion
        rcases Set.mem_iUnion.mp hpUnion with ⟨a, hpUnion⟩
        rcases Set.mem_iUnion.mp hpUnion with ⟨_ha, hpPiece⟩
        exact ⟨hpPiece.1, hpPiece.2.1⟩
    have hdisjoint : Set.PairwiseDisjoint (allowed c) piece := by
      intro first _ second _ hne
      change Disjoint (piece first) (piece second)
      rw [Set.disjoint_left]
      intro p hpFirst hpSecond
      exact hne (hpFirst.2.2.symm.trans hpSecond.2.2)
    have hmeasurable :
        ∀ a ∈ allowed c, MeasurableSet (piece a) := by
      intro a _
      exact (S.measurable_carrier i).inter (hatomMeasurable c a)
    calc
      volume (S.carrier i ∩ cellSet c) =
          volume (⋃ a ∈ allowed c, piece a) := by rw [hcover]
      _ = ∑ a ∈ allowed c, volume (piece a) :=
        MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
      _ = ∑ a ∈ allowed c,
          volume (S.carrier i ∩ atom c a) := by rfl
  have hchoiceActive : ∀ c ∈ activeCells, ∃ a ∈ allowed c,
      cellMass c ≤ labelBound * atomMass c a := by
    intro c hc
    rcases finset_ennreal_pigeonhole
        (hallowedNonempty c hc) (atomMass c) with
      ⟨a, ha, hmass⟩
    have hcardBound :
        ((allowed c).card : ENNReal) * atomMass c a ≤
          labelBound * atomMass c a := by
      gcongr
      exact hlabelBound c hc
    exact ⟨a, ha, (hallowedPartition c hc).trans_le
      (hmass.trans hcardBound)⟩
  let defaultLabel : Label := Classical.choice inferInstance
  let chosen (c : Cell) : Label :=
    if hc : c ∈ activeCells then
      Classical.choose (hchoiceActive c hc)
    else defaultLabel
  have hchosenMem : ∀ c ∈ activeCells, chosen c ∈ allowed c := by
    intro c hc
    simp only [chosen, dif_pos hc]
    exact (Classical.choose_spec (hchoiceActive c hc)).1
  have hchosenBound : ∀ c ∈ activeCells,
      cellMass c ≤ labelBound * atomMass c (chosen c) := by
    intro c hc
    simp only [chosen, dif_pos hc]
    exact (Classical.choose_spec (hchoiceActive c hc)).2
  let hchosenMeasurable : Measurable chosen := hmeasurableChosen chosen
  let selected := paperCellwiseLabelRestriction
    S cell hcell label hlabel chosen hchosenMeasurable
  have hcellPartition : S.mass = ∑ c ∈ activeCells, cellMass c := by
    calc
      S.mass = ∑ i : Fin F.card, volume (S.carrier i) := rfl
      _ = ∑ i : Fin F.card, ∑ c ∈ activeCells,
          volume (S.carrier i ∩ cellSet c) := by
            apply Finset.sum_congr rfl
            intro i _
            let piece : Cell → Set Point3 := fun c =>
              S.carrier i ∩ cellSet c
            have hcover : S.carrier i = ⋃ c ∈ activeCells, piece c := by
              ext p
              constructor
              · intro hp
                have hpa : cell p ∈ activeCells :=
                  hsupport p ⟨i, hp⟩
                exact Set.mem_iUnion.mpr ⟨cell p,
                  Set.mem_iUnion.mpr ⟨hpa, hp, rfl⟩⟩
              · intro hpUnion
                rcases Set.mem_iUnion.mp hpUnion with ⟨c, hpUnion⟩
                rcases Set.mem_iUnion.mp hpUnion with ⟨_hc, hpPiece⟩
                exact hpPiece.1
            have hdisjoint : Set.PairwiseDisjoint activeCells piece := by
              intro first _ second _ hne
              change Disjoint (piece first) (piece second)
              rw [Set.disjoint_left]
              intro p hpFirst hpSecond
              exact hne (hpFirst.2.symm.trans hpSecond.2)
            have hmeasurable : ∀ c ∈ activeCells,
                MeasurableSet (piece c) := by
              intro c _
              exact (S.measurable_carrier i).inter
                (hcellSetMeasurable c)
            calc
              volume (S.carrier i) =
                  volume (⋃ c ∈ activeCells, piece c) := by rw [hcover]
              _ = ∑ c ∈ activeCells, volume (piece c) :=
                MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
              _ = ∑ c ∈ activeCells,
                  volume (S.carrier i ∩ cellSet c) := by rfl
      _ = ∑ c ∈ activeCells, ∑ i : Fin F.card,
          volume (S.carrier i ∩ cellSet c) := by
            rw [Finset.sum_comm]
      _ = ∑ c ∈ activeCells, cellMass c := rfl
  have hselectedCellMass : selected.mass =
      ∑ c ∈ activeCells, atomMass c (chosen c) := by
    calc
      selected.mass = ∑ i : Fin F.card, volume (selected.carrier i) := rfl
      _ = ∑ i : Fin F.card, ∑ c ∈ activeCells,
          volume (S.carrier i ∩ atom c (chosen c)) := by
            apply Finset.sum_congr rfl
            intro i _
            let piece : Cell → Set Point3 := fun c =>
              S.carrier i ∩ atom c (chosen c)
            have hcover : selected.carrier i =
                ⋃ c ∈ activeCells, piece c := by
              ext p
              constructor
              · intro hp
                have hpS : p ∈ S.carrier i := hp.1
                have hpa : cell p ∈ activeCells :=
                  hsupport p ⟨i, hpS⟩
                exact Set.mem_iUnion.mpr ⟨cell p,
                  Set.mem_iUnion.mpr ⟨hpa, hpS, rfl, hp.2⟩⟩
              · intro hpUnion
                rcases Set.mem_iUnion.mp hpUnion with ⟨c, hpUnion⟩
                rcases Set.mem_iUnion.mp hpUnion with ⟨_hc, hpPiece⟩
                have hcellPoint : cell p = c := hpPiece.2.1
                have hlabelPoint : label p = chosen c := hpPiece.2.2
                exact ⟨hpPiece.1, by simpa [hcellPoint] using hlabelPoint⟩
            have hdisjoint : Set.PairwiseDisjoint activeCells piece := by
              intro first _ second _ hne
              change Disjoint (piece first) (piece second)
              rw [Set.disjoint_left]
              intro p hpFirst hpSecond
              exact hne (hpFirst.2.1.symm.trans hpSecond.2.1)
            have hmeasurable : ∀ c ∈ activeCells,
                MeasurableSet (piece c) := by
              intro c _
              exact (S.measurable_carrier i).inter
                (hatomMeasurable c (chosen c))
            calc
              volume (selected.carrier i) =
                  volume (⋃ c ∈ activeCells, piece c) := by rw [hcover]
              _ = ∑ c ∈ activeCells, volume (piece c) :=
                MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
              _ = ∑ c ∈ activeCells,
                  volume (S.carrier i ∩ atom c (chosen c)) := by rfl
      _ = ∑ c ∈ activeCells, ∑ i : Fin F.card,
          volume (S.carrier i ∩ atom c (chosen c)) := by
            rw [Finset.sum_comm]
      _ = ∑ c ∈ activeCells, atomMass c (chosen c) := rfl
  refine ⟨chosen, selected, ?_, rfl, hchosenMem, ?_, ?_⟩
  · exact paperCellwiseLabelRestriction_subshading
      S cell hcell label hlabel chosen hchosenMeasurable
  · exact paperCellwiseLabelRestriction_selected
      S cell hcell label hlabel chosen hchosenMeasurable
  · rw [hcellPartition, hselectedCellMass]
    calc
      ∑ c ∈ activeCells, cellMass c
          ≤ ∑ c ∈ activeCells,
              labelBound * atomMass c (chosen c) := by
            apply Finset.sum_le_sum
            intro c hc
            exact hchosenBound c hc
      _ = labelBound * ∑ c ∈ activeCells, atomMass c (chosen c) := by
            rw [Finset.mul_sum]

/-- Package cellwise bounded-label pigeonholing as a one-scale variation
refinement.  Geometry enters only through `hsameLabel`. -/
theorem paper_cellwise_bounded_label_variation_refinement
    {delta scale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [DecidableEq Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    [Nonempty Label] [DecidableEq Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [MeasurableEq Label]
    (S : WZ1PaperTubeShading F)
    (planeMap : Point3 → Point3)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (activeCells : Finset Cell)
    (hsupport : ∀ p ∈ S.union, cell p ∈ activeCells)
    (label : Point3 → Label) (hlabel : Measurable label)
    (allowed : Cell → Finset Label)
    (hallowedNonempty : ∀ c ∈ activeCells, (allowed c).Nonempty)
    (hlabelAllowed : ∀ p ∈ S.union, label p ∈ allowed (cell p))
    (labelBoundENN : ENNReal)
    (hlabelBound : ∀ c ∈ activeCells,
      ((allowed c).card : ENNReal) ≤ labelBoundENN)
    (hmeasurableChosen : ∀ chosen : Cell → Label, Measurable chosen)
    (hsameLabel : ∀ p ∈ S.union, ∀ q ∈ S.union,
      cell p = cell q → label p = label q →
        dist (planeMap p) (planeMap q) ≤ scale) :
    ∃ (chosen : Cell → Label) (selected : WZ1PaperTubeShading F),
      selected = paperCellwiseLabelRestriction
        S cell hcell label hlabel chosen (hmeasurableChosen chosen) ∧
      PaperIsSubshading selected S ∧
      (∀ p ∈ selected.union, ∀ q ∈ selected.union,
        cell p = cell q →
          dist (planeMap p) (planeMap q) ≤ scale) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      S.mass ≤ labelBoundENN * selected.mass := by
  rcases paper_cellwise_bounded_label_mass_refinement
      S cell hcell activeCells hsupport label hlabel allowed
      hallowedNonempty hlabelAllowed labelBoundENN hlabelBound
      hmeasurableChosen with
    ⟨chosen, selected, hsub, _hselectedEq, _hchosenAllowed,
      hselectedLabel, hmass⟩
  refine ⟨chosen, selected, _hselectedEq, hsub, ?_, ?_, hmass⟩
  · intro p hp q hq hcellEq
    have hpS : p ∈ S.union := by
      rcases hp with ⟨i, hi⟩
      exact ⟨i, hsub i hi⟩
    have hqS : q ∈ S.union := by
      rcases hq with ⟨i, hi⟩
      exact ⟨i, hsub i hi⟩
    have hpLabel := hselectedLabel p hp
    have hqLabel := hselectedLabel q hq
    have hlabelEq : label p = label q := by
      rw [hpLabel, hqLabel, hcellEq]
    exact hsameLabel p hpS q hqS hcellEq hlabelEq
  · rw [_hselectedEq]
    exact paperCellwiseLabelRestriction_pointMultiplicity_eq
      S cell hcell label hlabel chosen (hmeasurableChosen chosen)

end Kakeya.Assouad

end
