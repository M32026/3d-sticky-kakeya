import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseWeakPlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase1
import MyLeanRepo.Kakeya.Assouad.WZ1.Helpers

/-!
# Finite-label mass refinements for paper shadings

This module supplies the exact finite pigeonhole used by the one-scale
plane-map argument.  It does not change the plane map: it only restricts a
paper shading to one measurable label class.

The generic theorem works for any nonempty finite label type.  The specialized
corollary labels a point by the ordered pair of coarse parents of its two
cellwise transverse fine tubes.  Consequently every retained point uses one
common ordered parent pair, while the original, genuinely cellwise plane map
is left unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Restrict a paper shading to one fiber of a finite measurable label. -/
def paperFiniteLabelRestriction
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {α : Type*} [MeasurableSpace α]
    (S : WZ1PaperTubeShading F)
    (label : Point3 → α) (hlabel : Measurable label) (value : α)
    (hvalue : MeasurableSet ({value} : Set α)) :
    WZ1PaperTubeShading F :=
  { carrier := fun i => S.carrier i ∩ label ⁻¹' {value}
    measurable_carrier := fun i =>
      (S.measurable_carrier i).inter (hlabel hvalue)
    subset_body := fun i =>
      Set.inter_subset_left.trans (S.subset_body i) }

lemma paperFiniteLabelRestriction_subshading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {α : Type*} [MeasurableSpace α]
    (S : WZ1PaperTubeShading F)
    (label : Point3 → α) (hlabel : Measurable label) (value : α)
    (hvalue : MeasurableSet ({value} : Set α)) :
    PaperIsSubshading
      (paperFiniteLabelRestriction S label hlabel value hvalue) S :=
  fun _ => Set.inter_subset_left

lemma paperFiniteLabelRestriction_label
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {α : Type*} [MeasurableSpace α]
    (S : WZ1PaperTubeShading F)
    (label : Point3 → α) (hlabel : Measurable label) (value : α)
    (hvalue : MeasurableSet ({value} : Set α)) :
    ∀ p ∈ (paperFiniteLabelRestriction S label hlabel value hvalue).union,
      label p = value := by
  intro p hp
  rcases hp with ⟨i, hi⟩
  exact hi.2

lemma paperFiniteLabelRestriction_pointMultiplicity_eq
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {α : Type*} [MeasurableSpace α]
    (S : WZ1PaperTubeShading F)
    (label : Point3 → α) (hlabel : Measurable label) (value : α)
    (hvalue : MeasurableSet ({value} : Set α)) :
    ∀ p ∈ (paperFiniteLabelRestriction
        S label hlabel value hvalue).union,
      (paperFiniteLabelRestriction
        S label hlabel value hvalue).pointMultiplicity p =
        S.pointMultiplicity p := by
  intro p hp
  have hpLabel : label p = value :=
    paperFiniteLabelRestriction_label S label hlabel value hvalue p hp
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  ext i
  simp [paperFiniteLabelRestriction, hpLabel]

/-- Restriction to a label which is constant on `delta`-cells preserves
cubicality. -/
lemma paperFiniteLabelRestriction_cubical
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {α : Type*} [MeasurableSpace α]
    {S : WZ1PaperTubeShading F}
    (hS : WZ1PaperIsCubicalShading S)
    (label : Point3 → α) (hlabel : Measurable label) (value : α)
    (hvalue : MeasurableSet ({value} : Set α))
    (hconst : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        label p = label q) :
    WZ1PaperIsCubicalShading
      (paperFiniteLabelRestriction S label hlabel value hvalue) := by
  intro i p hp q hq
  have hcell :
      wz1PaperGridIndex delta q = wz1PaperGridIndex delta p :=
    (mem_wz1PaperGridCube delta (wz1PaperGridIndex delta p) q).mp hq
  have hqS : q ∈ S.carrier i := hS i p hp.1 hq
  have hlabelEq : label q = label p := hconst q p hcell
  exact ⟨hqS, by simpa [hlabelEq] using hp.2⟩

/-- A finite measurable labeling has a label class carrying at least the
average shaded mass. -/
theorem paper_finite_label_mass_refinement
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (S : WZ1PaperTubeShading F)
    (label : Point3 → α) (hlabel : Measurable label) :
    ∃ (value : α) (selected : WZ1PaperTubeShading F),
      PaperIsSubshading selected S ∧
      selected = paperFiniteLabelRestriction S label hlabel value
        (measurableSet_singleton value) ∧
      (∀ p ∈ selected.union, label p = value) ∧
      S.mass ≤ (Fintype.card α : ENNReal) * selected.mass := by
  classical
  let restricted : α → WZ1PaperTubeShading F := fun value =>
    paperFiniteLabelRestriction S label hlabel value (measurableSet_singleton value)
  have hcarrierPartition : ∀ i,
      volume (S.carrier i) =
        ∑ value : α, volume ((restricted value).carrier i) := by
    intro i
    let piece : α → Set Point3 := fun value =>
      S.carrier i ∩ label ⁻¹' ({value} : Set α)
    have hcover : S.carrier i = ⋃ value : α, piece value := by
      ext p
      simp [piece]
    have hdisjoint :
        Set.PairwiseDisjoint (Finset.univ : Finset α) piece := by
      intro first _ second _ hne
      change Disjoint (piece first) (piece second)
      rw [Set.disjoint_left]
      intro p hpFirst hpSecond
      exact hne (hpFirst.2.symm.trans hpSecond.2)
    have hmeasurable :
        ∀ value ∈ (Finset.univ : Finset α), MeasurableSet (piece value) := by
      intro value _
      exact (S.measurable_carrier i).inter
        (hlabel (measurableSet_singleton value))
    have hfinite :
        volume (⋃ value ∈ (Finset.univ : Finset α), piece value) =
          ∑ value ∈ (Finset.univ : Finset α), volume (piece value) :=
      MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
    have hindexed :
        (⋃ value : α, piece value) =
          ⋃ value ∈ (Finset.univ : Finset α), piece value := by
      ext p
      simp
    rw [hcover, hindexed, hfinite]
    simp [restricted, piece, paperFiniteLabelRestriction]
  have hmassPartition :
      S.mass = ∑ value : α, (restricted value).mass := by
    calc
      S.mass = ∑ i : Fin F.card, volume (S.carrier i) := rfl
      _ = ∑ i : Fin F.card, ∑ value : α,
          volume ((restricted value).carrier i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hcarrierPartition i
      _ = ∑ value : α, ∑ i : Fin F.card,
          volume ((restricted value).carrier i) := by
            rw [Finset.sum_comm]
      _ = ∑ value : α, (restricted value).mass := rfl
  rcases finset_ennreal_pigeonhole
      (s := (Finset.univ : Finset α)) Finset.univ_nonempty
      (fun value => (restricted value).mass) with
    ⟨value, _, hvalueMass⟩
  let selected := restricted value
  refine ⟨value, selected, ?_, rfl, ?_, ?_⟩
  · exact paperFiniteLabelRestriction_subshading
      S label hlabel value (measurableSet_singleton value)
  · exact paperFiniteLabelRestriction_label
      S label hlabel value (measurableSet_singleton value)
  · rw [hmassPartition]
    simpa [selected] using hvalueMass

/-- Specialize finite-label pigeonholing to the ordered pair of selected
coarse parents.  The fine direction selection and its plane map are not
replaced. -/
theorem paper_parent_pair_mass_refinement
    {delta rho kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {source selected : WZ1PaperTubeShading fine}
    (cover : PureWZ2Section6Cover fine coarse)
    (selection : PaperWZ1NarrowDirectionSelection source kappa)
    (hselectedCubical : WZ1PaperIsCubicalShading selected)
    (hselectionCell : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        selection.first p = selection.first q ∧
        selection.second p = selection.second q) :
    ∃ (parents : Fin coarse.card × Fin coarse.card)
      (refined : WZ1PaperTubeShading fine),
      PaperIsSubshading refined selected ∧
      WZ1PaperIsCubicalShading refined ∧
      (∀ p ∈ refined.union,
        PureWZ2.selectParent cover (selection.first p) = parents.1 ∧
        PureWZ2.selectParent cover (selection.second p) = parents.2) ∧
      selected.mass ≤
        (Fintype.card (Fin coarse.card × Fin coarse.card) : ENNReal) *
          refined.mass := by
  classical
  let fineIndex : Fin fine.card := selection.first 0
  let coarseIndex : Fin coarse.card := PureWZ2.selectParent cover fineIndex
  letI : Nonempty (Fin coarse.card) := ⟨coarseIndex⟩
  let parentPair : Point3 → Fin coarse.card × Fin coarse.card := fun p =>
    (PureWZ2.selectParent cover (selection.first p),
      PureWZ2.selectParent cover (selection.second p))
  have hparentPairMeasurable : Measurable parentPair := by
    have hfirst : Measurable selection.first := selection.first_measurable
    have hsecond : Measurable selection.second := selection.second_measurable
    have hparent : Measurable (PureWZ2.selectParent cover) :=
      measurable_of_finite _
    exact (hparent.comp hfirst).prod (hparent.comp hsecond)
  rcases paper_finite_label_mass_refinement
      selected parentPair hparentPairMeasurable with
    ⟨parents, refined, hsub, hrefinedEq, hparents, hmass⟩
  have hparentPairCell : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        parentPair p = parentPair q := by
    intro p q hcell
    rcases hselectionCell p q hcell with ⟨hfirst, hsecond⟩
    simp [parentPair, hfirst, hsecond]
  have hrefinedCubical : WZ1PaperIsCubicalShading refined := by
    have hrestricted := paperFiniteLabelRestriction_cubical
      hselectedCubical parentPair hparentPairMeasurable parents
      (measurableSet_singleton parents) hparentPairCell
    rw [hrefinedEq]
    exact hrestricted
  refine ⟨parents, refined, hsub, hrefinedCubical, ?_, hmass⟩
  intro p hp
  have heq := hparents p hp
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

end Kakeya.Assouad

end
