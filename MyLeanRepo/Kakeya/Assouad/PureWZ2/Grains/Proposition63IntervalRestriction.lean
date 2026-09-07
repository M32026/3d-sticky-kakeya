import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceAxialAssembly

/-!
# Restrict a shading to a finite set of axial intervals
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def proposition63IntervalRegion
    {rho width : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (selected : Finset (commonSliceIntervalType width)) : Set Point3 :=
  ⋃ interval ∈ selected,
    proposition63AxialSlab anchor hrho width interval.1

lemma proposition63IntervalRegion_measurable
    {rho width : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (selected : Finset (commonSliceIntervalType width)) :
    MeasurableSet (proposition63IntervalRegion anchor hrho selected) := by
  apply MeasurableSet.iUnion
  intro interval
  apply MeasurableSet.iUnion
  intro _hinterval
  exact proposition63AxialSlab_measurable anchor hrho interval.1

def proposition63IntervalRestriction
    {delta rho width : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (selected : Finset (commonSliceIntervalType width)) :
    WZ1PaperTubeShading family where
  carrier tube := source.carrier tube ∩
    proposition63IntervalRegion anchor hrho selected
  measurable_carrier tube := (source.measurable_carrier tube).inter
    (proposition63IntervalRegion_measurable anchor hrho selected)
  subset_body tube := Set.inter_subset_left.trans (source.subset_body tube)

lemma proposition63IntervalRestriction_subshading
    {delta rho width : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (selected : Finset (commonSliceIntervalType width)) :
    PaperIsSubshading
      (proposition63IntervalRestriction source anchor hrho selected) source :=
  fun _ => Set.inter_subset_left

theorem proposition63IntervalRestriction_mass
    {delta rho width : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (hwidth : 0 < width)
    (selected : Finset (commonSliceIntervalType width)) :
    (proposition63IntervalRestriction source anchor hrho selected).mass =
      ∑ interval ∈ selected,
        proposition63AxialPartitionMass source anchor hrho interval := by
  classical
  simp_rw [proposition63AxialPartitionMass, commonSliceSlabMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tube _
  have hpairwise : Set.PairwiseDisjoint
      (↑selected : Set (commonSliceIntervalType width))
      (fun interval => source.carrier tube ∩
        proposition63AxialSlab anchor hrho width interval.1) := by
    intro first _ second _ hne
    have hvalueNe : first.1 ≠ second.1 := fun heq => hne (Subtype.ext heq)
    exact (proposition63_axialSlab_disjoint hwidth anchor hrho hvalueNe).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeasurable : ∀ interval ∈ selected,
      MeasurableSet (source.carrier tube ∩
        proposition63AxialSlab anchor hrho width interval.1) := by
    intro interval _
    exact (source.measurable_carrier tube).inter
      (proposition63AxialSlab_measurable anchor hrho interval.1)
  have hunion :
      ⋃ interval ∈ selected, source.carrier tube ∩
        proposition63AxialSlab anchor hrho width interval.1 =
      (proposition63IntervalRestriction source anchor hrho selected).carrier tube := by
    ext point
    constructor
    · rintro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨interval, hinterval, hsource, hslab⟩
      exact ⟨hsource, Set.mem_iUnion₂.mpr
        ⟨interval, hinterval, hslab⟩⟩
    · rintro ⟨hsource, hregion⟩
      rcases Set.mem_iUnion₂.mp hregion with ⟨interval, hinterval, hslab⟩
      exact Set.mem_iUnion₂.mpr
        ⟨interval, hinterval, hsource, hslab⟩
  change volume ((proposition63IntervalRestriction
    source anchor hrho selected).carrier tube) = _
  rw [← hunion, MeasureTheory.measure_biUnion_finset hpairwise hmeasurable]

lemma proposition63IntervalRestriction_sub_commonSlice
    {delta rho width : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (distinguished : Fin family.card)
    (selected : Finset (commonSliceIntervalType width))
    (hselected : ∀ interval ∈ selected,
      proposition63AxialPartitionMeets source anchor hrho
        distinguished interval) :
    PaperIsSubshading
      (proposition63IntervalRestriction source anchor hrho selected)
      (proposition63AxialAnchorShading
        (Delta := width) source anchor hrho distinguished) := by
  intro tube point hpoint
  refine ⟨hpoint.1, ?_⟩
  rcases Set.mem_iUnion₂.mp hpoint.2 with ⟨interval, hinterval, hslab⟩
  exact proposition63AxialAnchorRegion_mem_of_interval interval
    (hselected interval hinterval) hslab

end Kakeya.Assouad.PureWZ2

end
