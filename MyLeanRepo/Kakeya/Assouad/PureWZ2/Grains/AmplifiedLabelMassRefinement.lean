import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase2
import MyLeanRepo.Kakeya.Assouad.WZ1.Helpers

/-!
# Multiplicity-amplified cellwise label selection

This is the weighted pigeonhole used in the paper's Lemma 14.  A point may
support many good labels.  The point-multiplicity weight is therefore counted
once for each good label before selecting the heaviest label in each cell.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Restrict a paper shading to the predicate selected independently in each
cell. -/
def paperCellwisePredicateRestriction
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label]
    [Fintype Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (good : Point3 → Label → Prop)
    (hgood : ∀ label, MeasurableSet {p | good p label})
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    WZ1PaperTubeShading F := by
  let selectedSet : Set Point3 := {p | good p (chosen (cell p))}
  have hselectedMeasurable : MeasurableSet selectedSet := by
    have heq : selectedSet = ⋃ label : Label,
        {p | chosen (cell p) = label} ∩ {p | good p label} := by
      ext p
      simp [selectedSet]
    rw [heq]
    apply MeasurableSet.iUnion
    intro label
    exact ((hchosen.comp hcell) (measurableSet_singleton label)).inter
      (hgood label)
  exact
    { carrier := fun i => S.carrier i ∩ selectedSet
      measurable_carrier := fun i =>
        (S.measurable_carrier i).inter hselectedMeasurable
      subset_body := fun i =>
        Set.inter_subset_left.trans (S.subset_body i) }

lemma paperCellwisePredicateRestriction_subshading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label]
    [Fintype Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (good : Point3 → Label → Prop)
    (hgood : ∀ label, MeasurableSet {p | good p label})
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    PaperIsSubshading
      (paperCellwisePredicateRestriction
        S cell hcell good hgood chosen hchosen) S :=
  fun _ => Set.inter_subset_left

lemma paperCellwisePredicateRestriction_good
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label]
    [Fintype Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (good : Point3 → Label → Prop)
    (hgood : ∀ label, MeasurableSet {p | good p label})
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    ∀ p ∈ (paperCellwisePredicateRestriction
        S cell hcell good hgood chosen hchosen).union,
      good p (chosen (cell p)) := by
  intro p hp
  rcases hp with ⟨i, hi⟩
  exact hi.2

/-- A common spatial restriction deletes or retains all tube carriers at a
point simultaneously.  Hence point multiplicity is unchanged at every point
which survives the restriction. -/
lemma paperCellwisePredicateRestriction_pointMultiplicity_eq
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label]
    [Fintype Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (good : Point3 → Label → Prop)
    (hgood : ∀ label, MeasurableSet {p | good p label})
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    ∀ p ∈ (paperCellwisePredicateRestriction
        S cell hcell good hgood chosen hchosen).union,
      (paperCellwisePredicateRestriction
        S cell hcell good hgood chosen hchosen).pointMultiplicity p =
        S.pointMultiplicity p := by
  intro p hp
  have hselected : good p (chosen (cell p)) :=
    paperCellwisePredicateRestriction_good
      S cell hcell good hgood chosen hchosen p hp
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  ext i
  simp [paperCellwisePredicateRestriction, hselected]

/-- A predicate restriction is cubical when its spatial cell and every fixed
label predicate are constant on fine paper cells. -/
lemma paperCellwisePredicateRestriction_cubical
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [MeasurableSpace Label]
    [Fintype Label] [MeasurableSingletonClass Label]
    {S : WZ1PaperTubeShading F}
    (hS : WZ1PaperIsCubicalShading S)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (good : Point3 → Label → Prop)
    (hgood : ∀ label, MeasurableSet {p | good p label})
    (chosen : Cell → Label) (hchosen : Measurable chosen)
    (hcellConst : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      cell first = cell second)
    (hgoodConst : ∀ label first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      (good first label ↔ good second label)) :
    WZ1PaperIsCubicalShading
      (paperCellwisePredicateRestriction
        S cell hcell good hgood chosen hchosen) := by
  intro index point hpoint other hother
  have hgrid : wz1PaperGridIndex delta other =
      wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) other).mp hother
  have hotherSource : other ∈ S.carrier index :=
    hS index point hpoint.1 hother
  have hcellEq : cell other = cell point :=
    hcellConst other point hgrid
  have hgoodOther : good other (chosen (cell point)) :=
    (hgoodConst (chosen (cell point)) other point hgrid).mpr hpoint.2
  exact ⟨hotherSource, by simpa [hcellEq] using hgoodOther⟩

/-- Weighted cellwise pigeonhole.

At every point the amplification factor is bounded by `coefficient` times
the number of good labels.  Each cell has at most `labelBound` admissible
labels.  Selecting the label with maximal shaded mass in every cell gives the
displayed global mass inequality. -/
theorem paper_cellwise_amplified_label_mass_refinement
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [Countable Cell] [DecidableEq Cell]
    [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (activeCells : Finset Cell)
    (hsupport : ∀ p ∈ S.union, cell p ∈ activeCells)
    (allowed : Cell → Finset Label)
    (hallowedNonempty : ∀ c ∈ activeCells, (allowed c).Nonempty)
    (good : Point3 → Label → Prop)
    (hgoodMeasurable : ∀ label, MeasurableSet {p | good p label})
    (hgoodAllowed : ∀ p ∈ S.union, ∀ label, good p label →
      label ∈ allowed (cell p))
    (labelWeight : Cell → Label → ENNReal)
    (goodCount : Point3 → Cell → ENNReal)
    (hgoodCount : ∀ p c, goodCount p c =
      ∑ label ∈ allowed c,
        ({p | good p label}.indicator
          (fun _ => labelWeight c label)) p)
    (amplification coefficient labelBound : ENNReal)
    (hpointwise : ∀ p ∈ S.union,
      amplification ≤ coefficient * goodCount p (cell p))
    (hlabelBound : ∀ c ∈ activeCells,
      (∑ label ∈ allowed c, labelWeight c label) ≤ labelBound) :
    ∃ (chosen : Cell → Label) (selected : WZ1PaperTubeShading F),
      PaperIsSubshading selected S ∧
      selected = paperCellwisePredicateRestriction
        S cell hcell good hgoodMeasurable chosen (by fun_prop) ∧
      (∀ c ∈ activeCells, chosen c ∈ allowed c) ∧
      (∀ p ∈ selected.union, good p (chosen (cell p))) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      amplification * S.mass ≤
        coefficient * labelBound * selected.mass := by
  classical
  let multiplicity : Point3 → ENNReal := fun p =>
    (S.pointMultiplicity p : ENNReal)
  have hmultiplicityMeasurable : Measurable multiplicity :=
    PureWZ2.pointMultiplicity_measurable S
  let cellSet (c : Cell) : Set Point3 := {p | cell p = c}
  have hcellSetMeasurable : ∀ c, MeasurableSet (cellSet c) := by
    intro c
    exact hcell (measurableSet_singleton c)
  let goodSet (c : Cell) (label : Label) : Set Point3 :=
    cellSet c ∩ {p | good p label}
  have hgoodSetMeasurable : ∀ c label,
      MeasurableSet (goodSet c label) := by
    intro c label
    exact (hcellSetMeasurable c).inter (hgoodMeasurable label)
  let labelMass (c : Cell) (label : Label) : ENNReal :=
    ∫⁻ p in goodSet c label, multiplicity p
  let cellMass (c : Cell) : ENNReal :=
    ∫⁻ p in cellSet c, multiplicity p
  have hcellMassSum : S.mass = ∑ c ∈ activeCells, cellMass c := by
    have houtside : ∀ p, p ∉ S.union → multiplicity p = 0 := by
      intro p hp
      have hzero : S.pointMultiplicity p = 0 := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_eq_zero.mpr
        simp
        exact fun i hi => hp ⟨i, hi⟩
      simpa [multiplicity] using congrArg (fun n : ℕ => (n : ENNReal)) hzero
    have hpartition :
        ∫⁻ p, multiplicity p = ∑ c ∈ activeCells, cellMass c := by
      let pieces : Cell → Set Point3 := cellSet
      have hdisjoint : Set.PairwiseDisjoint activeCells pieces := by
        intro first _ second _ hne
        change Disjoint (pieces first) (pieces second)
        rw [Set.disjoint_left]
        intro p hfirst hsecond
        exact hne (hfirst.symm.trans hsecond)
      have hmeasurable : ∀ c ∈ activeCells, MeasurableSet (pieces c) :=
        fun c _ => hcellSetMeasurable c
      let activeUnion : Set Point3 := ⋃ c ∈ activeCells, pieces c
      have hunionIntegral :
          (∫⁻ p in activeUnion, multiplicity p) =
            ∑ c ∈ activeCells, cellMass c := by
        rw [show activeUnion = ⋃ c ∈ activeCells, pieces c from rfl]
        exact MeasureTheory.lintegral_biUnion_finset
          hdisjoint hmeasurable multiplicity
      have houtsideUnion : ∀ p ∉ activeUnion, multiplicity p = 0 := by
        intro p hp
        apply houtside p
        intro hpS
        have hc := hsupport p hpS
        apply hp
        exact Set.mem_iUnion.mpr ⟨cell p,
          Set.mem_iUnion.mpr ⟨hc, rfl⟩⟩
      have hfull : (∫⁻ p, multiplicity p) =
          ∫⁻ p in activeUnion, multiplicity p := by
        rw [← MeasureTheory.lintegral_indicator]
        · congr 1
          funext p
          by_cases hp : p ∈ activeUnion
          · simp [Set.indicator_apply, hp]
          · simp [Set.indicator_apply, hp, houtsideUnion p hp]
        · exact Finset.measurableSet_biUnion activeCells fun c _ =>
            hcellSetMeasurable c
      rw [hfull, hunionIntegral]
    rw [← lintegral_pointMultiplicity S]
    exact hpartition
  have hweightedCell : ∀ c ∈ activeCells,
      amplification * cellMass c ≤
        coefficient * ∑ label ∈ allowed c,
          labelWeight c label * labelMass c label := by
    intro c hc
    have hpoint : ∀ p ∈ cellSet c,
        amplification * multiplicity p ≤
          coefficient * goodCount p c *
              multiplicity p := by
      intro p hpc
      by_cases hpS : p ∈ S.union
      · have hcellEq : cell p = c := hpc
        have h := hpointwise p hpS
        rw [hcellEq] at h
        exact mul_le_mul_right' h (multiplicity p)
      · have hzero : multiplicity p = 0 := by
          have hpMultiplicity : S.pointMultiplicity p = 0 := by
            simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
            apply Finset.card_eq_zero.mpr
            simp
            exact fun i hi => hpS ⟨i, hi⟩
          simpa [multiplicity] using
            congrArg (fun n : ℕ => (n : ENNReal)) hpMultiplicity
        rw [hzero]
        simp
    have hleft : amplification * cellMass c =
        ∫⁻ p in cellSet c, amplification * multiplicity p := by
      exact (MeasureTheory.lintegral_const_mul
        amplification hmultiplicityMeasurable).symm
    have hmono :
        (∫⁻ p in cellSet c, amplification * multiplicity p) ≤
          ∫⁻ p in cellSet c,
            coefficient * goodCount p c *
                multiplicity p :=
      MeasureTheory.setLIntegral_mono' (hcellSetMeasurable c) hpoint
    have hright :
        (∫⁻ p in cellSet c,
          coefficient * goodCount p c *
              multiplicity p) =
          coefficient * ∑ label ∈ allowed c,
            labelWeight c label * labelMass c label := by
      have hcount : ∀ p,
          goodCount p c *
              multiplicity p =
            ∑ label ∈ allowed c,
              labelWeight c label *
                ({p | good p label}.indicator multiplicity) p := by
        intro p
        rw [hgoodCount p c, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro label _
        by_cases hgood : good p label
        · simp [Set.indicator_apply, hgood]
        · simp [Set.indicator_apply, hgood]
      have hcountFunctionMeasurable : Measurable (fun p : Point3 =>
          goodCount p c *
            multiplicity p) := by
        have heq : (fun p : Point3 =>
            goodCount p c *
              multiplicity p) =
            fun p => ∑ label ∈ allowed c,
              labelWeight c label *
                ({p | good p label}.indicator multiplicity) p := by
          funext p
          exact hcount p
        rw [heq]
        apply Finset.measurable_sum
        intro label _
        exact measurable_const.mul
          (hmultiplicityMeasurable.indicator (hgoodMeasurable label))
      calc
        (∫⁻ p in cellSet c, coefficient *
            goodCount p c *
              multiplicity p) =
            coefficient *
              ∫⁻ p in cellSet c,
                goodCount p c *
                  multiplicity p := by
            have h := (MeasureTheory.lintegral_const_mul
              (μ := volume.restrict (cellSet c))
              coefficient hcountFunctionMeasurable)
            simpa only [mul_assoc] using h
        _ = coefficient *
            ∫⁻ p in cellSet c,
              ∑ label ∈ allowed c,
                labelWeight c label *
                  ({p | good p label}.indicator multiplicity) p := by
            congr 2
            funext p
            exact hcount p
        _ = coefficient * ∑ label ∈ allowed c,
            ∫⁻ p in cellSet c,
              labelWeight c label *
                ({p | good p label}.indicator multiplicity) p := by
            rw [MeasureTheory.lintegral_finsetSum]
            intro label _
            exact measurable_const.mul
              (hmultiplicityMeasurable.indicator (hgoodMeasurable label))
        _ = coefficient * ∑ label ∈ allowed c,
            labelWeight c label * labelMass c label := by
            congr 1
            apply Finset.sum_congr rfl
            intro label _
            have hbase :
                (∫⁻ p in cellSet c,
                  ({p | good p label}.indicator multiplicity) p) =
                  labelMass c label := by
              rw [← MeasureTheory.lintegral_indicator
                (hcellSetMeasurable c)]
              change
                (∫⁻ p, (cellSet c).indicator
                  (({p | good p label}).indicator multiplicity) p) =
                  ∫⁻ p in goodSet c label, multiplicity p
              rw [← MeasureTheory.lintegral_indicator
                (hgoodSetMeasurable c label)]
              congr 1
              funext p
              by_cases hc' : p ∈ cellSet c <;>
                by_cases hg' : good p label <;>
                simp [Set.indicator_apply, hc', hg', goodSet]
            calc
              (∫⁻ p in cellSet c, labelWeight c label *
                  ({p | good p label}.indicator multiplicity) p) =
                  labelWeight c label *
                    ∫⁻ p in cellSet c,
                      ({p | good p label}.indicator multiplicity) p :=
                MeasureTheory.lintegral_const_mul
                  (labelWeight c label)
                  (hmultiplicityMeasurable.indicator
                    (hgoodMeasurable label))
              _ = labelWeight c label * labelMass c label := by
                rw [hbase]
    rw [hleft]
    exact hmono.trans_eq hright
  let defaultLabel : Label := Classical.choice inferInstance
  have hbest : ∀ c ∈ activeCells, ∃ label ∈ allowed c,
      (∑ other ∈ allowed c, labelWeight c other) *
          labelMass c label ≥
        ∑ other ∈ allowed c,
          labelWeight c other * labelMass c other := by
    intro c hc
    rcases Finset.exists_max_image (allowed c) (labelMass c)
        (hallowedNonempty c hc) with ⟨label, hlabel, hmax⟩
    refine ⟨label, hlabel, ?_⟩
    calc
      ∑ other ∈ allowed c,
          labelWeight c other * labelMass c other ≤
          ∑ other ∈ allowed c,
            labelWeight c other * labelMass c label := by
        apply Finset.sum_le_sum
        intro other hother
        gcongr
        exact hmax other hother
      _ = (∑ other ∈ allowed c, labelWeight c other) *
          labelMass c label := by
        rw [Finset.sum_mul]
  let chosen (c : Cell) : Label :=
    if hc : c ∈ activeCells then Classical.choose (hbest c hc) else defaultLabel
  have hchosenAllowed : ∀ c ∈ activeCells, chosen c ∈ allowed c := by
    intro c hc
    simp only [chosen, dif_pos hc]
    exact (Classical.choose_spec (hbest c hc)).1
  have hchosenMass : ∀ c ∈ activeCells,
      ∑ label ∈ allowed c, labelWeight c label * labelMass c label ≤
        labelBound * labelMass c (chosen c) := by
    intro c hc
    have hpigeon := (Classical.choose_spec (hbest c hc)).2
    have hweight := hlabelBound c hc
    simp only [chosen, dif_pos hc]
    exact hpigeon.trans (by gcongr)
  have hchosenMeasurable : Measurable chosen := Measurable.of_discrete
  let selected := paperCellwisePredicateRestriction
    S cell hcell good hgoodMeasurable chosen hchosenMeasurable
  have hselectedMass : selected.mass =
      ∑ c ∈ activeCells, labelMass c (chosen c) := by
    have hcarrier : ∀ i : Fin F.card,
        volume (selected.carrier i) =
          ∑ c ∈ activeCells,
            volume (S.carrier i ∩ goodSet c (chosen c)) := by
      intro i
      let piece : Cell → Set Point3 := fun c =>
        S.carrier i ∩ goodSet c (chosen c)
      have hunion : selected.carrier i = ⋃ c ∈ activeCells, piece c := by
        ext p
        constructor
        · intro hp
          have hpS : p ∈ S.union := ⟨i, hp.1⟩
          have hc := hsupport p hpS
          exact Set.mem_iUnion.mpr ⟨cell p,
            Set.mem_iUnion.mpr ⟨hc, hp.1, rfl, hp.2⟩⟩
        · intro hp
          rcases Set.mem_iUnion.mp hp with ⟨c, hp⟩
          rcases Set.mem_iUnion.mp hp with ⟨_hc, hp⟩
          have hcellPoint : cell p = c := hp.2.1
          exact ⟨hp.1, by simpa [hcellPoint] using hp.2.2⟩
      have hdisjoint : Set.PairwiseDisjoint activeCells piece := by
        intro first _ second _ hne
        change Disjoint (piece first) (piece second)
        rw [Set.disjoint_left]
        intro p hfirst hsecond
        exact hne (hfirst.2.1.symm.trans hsecond.2.1)
      have hmeasurable : ∀ c ∈ activeCells, MeasurableSet (piece c) := by
        intro c _
        exact (S.measurable_carrier i).inter
          (hgoodSetMeasurable c (chosen c))
      rw [hunion, MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable]
    calc
      selected.mass = ∑ i : Fin F.card, volume (selected.carrier i) := rfl
      _ = ∑ i : Fin F.card, ∑ c ∈ activeCells,
          volume (S.carrier i ∩ goodSet c (chosen c)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hcarrier i
      _ = ∑ c ∈ activeCells, ∑ i : Fin F.card,
          volume (S.carrier i ∩ goodSet c (chosen c)) := by
            rw [Finset.sum_comm]
      _ = ∑ c ∈ activeCells, labelMass c (chosen c) := by
            apply Finset.sum_congr rfl
            intro c _
            exact sum_volume_inter_eq_setLIntegral_pointMultiplicity
              S (hgoodSetMeasurable c (chosen c))
  refine ⟨chosen, selected, ?_, rfl, hchosenAllowed, ?_, ?_, ?_⟩
  · exact paperCellwisePredicateRestriction_subshading
      S cell hcell good hgoodMeasurable chosen hchosenMeasurable
  · exact paperCellwisePredicateRestriction_good
      S cell hcell good hgoodMeasurable chosen hchosenMeasurable
  · exact paperCellwisePredicateRestriction_pointMultiplicity_eq
      S cell hcell good hgoodMeasurable chosen hchosenMeasurable
  · rw [hcellMassSum, hselectedMass, Finset.mul_sum]
    calc
      ∑ c ∈ activeCells, amplification * cellMass c ≤
          ∑ c ∈ activeCells, coefficient *
            ∑ label ∈ allowed c,
              labelWeight c label * labelMass c label := by
        apply Finset.sum_le_sum
        intro c hc
        exact hweightedCell c hc
      _ ≤ ∑ c ∈ activeCells, coefficient *
          (labelBound * labelMass c (chosen c)) := by
        apply Finset.sum_le_sum
        intro c hc
        gcongr
        exact hchosenMass c hc
      _ = coefficient * labelBound *
          ∑ c ∈ activeCells, labelMass c (chosen c) := by
        calc
          ∑ c ∈ activeCells, coefficient *
              (labelBound * labelMass c (chosen c)) =
              ∑ c ∈ activeCells, (coefficient * labelBound) *
                labelMass c (chosen c) := by
            apply Finset.sum_congr rfl
            intro c _
            ring
          _ = coefficient * labelBound *
              ∑ c ∈ activeCells, labelMass c (chosen c) := by
            rw [Finset.mul_sum]

end Kakeya.Assouad

end
