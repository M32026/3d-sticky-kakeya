import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceAxialHeightPartition
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Axial common-slice selection and refinement

This is the concrete common-slice construction used by Proposition 6.3.
Intervals are measured in the third coordinate of the frozen literal unit
rescaling, so they become horizontal slabs after rescaling.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

def proposition63AxialPartitionMass
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (interval : commonSliceIntervalType Delta) : ENNReal :=
  commonSliceSlabMass shading
    (proposition63AxialSlab anchor hrho Delta interval.1)

def proposition63AxialPartitionMeets
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (tube : Fin family.card)
    (interval : commonSliceIntervalType Delta) : Prop :=
  commonSliceSlabMeets shading
    (proposition63AxialSlab anchor hrho Delta interval.1) tube

lemma proposition63AxialPartitionMass_sum
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (hanchorLine : WZ1PaperTubeInLineClass anchor)
    (hDelta : 0 < Delta) :
    (∑ interval : commonSliceIntervalType Delta,
      proposition63AxialPartitionMass
        (Delta := Delta) shading anchor hrho interval) =
      shading.mass := by
  rw [show (∑ interval : commonSliceIntervalType Delta,
      proposition63AxialPartitionMass
        (Delta := Delta) shading anchor hrho interval) =
      ∑ index ∈ commonSliceHeightIndices Delta,
        commonSliceSlabMass shading
          (proposition63AxialSlab anchor hrho Delta index) by
    exact (Finset.sum_subtype
      (s := commonSliceHeightIndices Delta)
      (f := fun index => commonSliceSlabMass shading
        (proposition63AxialSlab anchor hrho Delta index))
      (p := fun index => index ∈ commonSliceHeightIndices Delta)
      (by simp [proposition63AxialPartitionMass])).symm]
  exact proposition63_axial_slab_mass_sum shading anchor hrho
    hanchorLine hDelta

/-- Double counting in parent-axial intervals selects the paper's
distinguished tube `T₀`. -/
theorem exists_proposition63_axial_anchor
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (hanchorLine : WZ1PaperTubeInLineClass anchor)
    (hfamilyNonempty : family.Nonempty)
    (hline : WZ1PaperIsLineClass family)
    (hcovered : ∀ tube : Fin family.card,
      WZ1PaperTubeCovers (family.tube tube) anchor)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrhoOne : rho ≤ 1)
    (hDelta : 0 < Delta)
    (target : ENNReal)
    (haggregate :
      (family.card : ENNReal) * target *
          ((Fintype.card (commonSliceIntervalType Delta) : ENNReal) *
            commonSliceSingleTubeBound delta (100 * Delta)) ≤
        shading.mass ^ 2) :
    ∃ distinguished : Fin family.card,
      target ≤ commonSliceRetainedMass
        (proposition63AxialPartitionMeets
          (Delta := Delta) shading anchor hrho)
        (proposition63AxialPartitionMass
          (Delta := Delta) shading anchor hrho)
        distinguished := by
  letI : Nonempty (Fin family.card) := ⟨⟨0, hfamilyNonempty⟩⟩
  have hintervalNonempty : Nonempty (commonSliceIntervalType Delta) := by
    let index := Int.floor (0 / Delta)
    exact ⟨⟨index, commonSlice_height_index_mem hDelta (by norm_num)⟩⟩
  letI : Nonempty (commonSliceIntervalType Delta) := hintervalNonempty
  have hshadingFinite : shading.mass ≠ ⊤ := by
    have hupper := wz2_paper_shading_mass_upper
      hdelta hdeltaSmall hline shading
    have hboundTop :
        (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2 * family.enncard < ⊤ := by
      apply (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num)
            (tube_volume_scaling.2.1 1 (by norm_num) (by norm_num)).2)
          (by simp [Kakeya.realRpowENN]))
        (by simp [Kakeya.Streamlined.TubeFamily.enncard])).lt_top
    exact (hupper.trans_lt hboundTop).ne
  have hmassFinite : ∀ interval : commonSliceIntervalType Delta,
      proposition63AxialPartitionMass
        (Delta := Delta) shading anchor hrho interval ≠ ⊤ := by
    intro interval
    apply commonSliceSlabMass_ne_top
    intro tube
    have hsingle : volume (shading.carrier tube) ≤ shading.mass :=
      Finset.single_le_sum
        (fun index (_ : index ∈ (Finset.univ : Finset (Fin family.card))) =>
          (show (0 : ENNReal) ≤ volume (shading.carrier index) from bot_le))
        (Finset.mem_univ tube)
    exact hsingle.trans_lt hshadingFinite.lt_top |>.ne
  have hmassCount : ∀ interval : commonSliceIntervalType Delta,
      proposition63AxialPartitionMass
        (Delta := Delta) shading anchor hrho interval ≤
        commonSliceSingleTubeBound delta (100 * Delta) *
          (commonSliceMeetingCount
            (proposition63AxialPartitionMeets
              (Delta := Delta) shading anchor hrho)
            interval : ENNReal) := by
    intro interval
    apply commonSliceSlabMass_le_meetingCount
    intro tube _
    calc
      volume (shading.carrier tube ∩
          proposition63AxialSlab anchor hrho Delta interval.1) ≤
        volume (wz1PaperTubeCarrier (family.tube tube) ∩
          proposition63AxialSlab anchor hrho Delta interval.1) :=
        measure_mono (Set.inter_subset_inter_left _
          (shading.subset_body tube))
      _ ≤ commonSliceSingleTubeBound delta (100 * Delta) :=
        proposition63_single_tube_axial_slab_volume hdelta hdeltaSmall
          hrho hrhoOne hDelta (family.tube tube) anchor (hline tube)
          (hcovered tube) interval.1
  have hAZero : commonSliceSingleTubeBound delta (100 * Delta) ≠ 0 := by
    simp [commonSliceSingleTubeBound]
    positivity
  have hAFinite : commonSliceSingleTubeBound delta (100 * Delta) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  apply exists_common_slice_anchor_of_mass_square
    (proposition63AxialPartitionMeets
      (Delta := Delta) shading anchor hrho)
    (proposition63AxialPartitionMass
      (Delta := Delta) shading anchor hrho)
    hmassFinite (commonSliceSingleTubeBound delta (100 * Delta)) target
    hAZero hAFinite hmassCount
  rw [proposition63AxialPartitionMass_sum shading anchor hrho
    hanchorLine hDelta]
  simpa using haggregate

def proposition63AxialAnchorRegion
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (distinguished : Fin family.card) : Set Point3 :=
  ⋃ interval : commonSliceIntervalType Delta,
    if proposition63AxialPartitionMeets (Delta := Delta) shading anchor hrho
        distinguished interval then
      proposition63AxialSlab anchor hrho Delta interval.1 else ∅

lemma proposition63AxialAnchorRegion_measurable
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (distinguished : Fin family.card) :
    MeasurableSet (proposition63AxialAnchorRegion
      (Delta := Delta) shading anchor hrho distinguished) := by
  apply MeasurableSet.iUnion
  intro interval
  split_ifs
  · exact proposition63AxialSlab_measurable anchor hrho interval.1
  · exact MeasurableSet.empty

def proposition63AxialAnchorShading
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (distinguished : Fin family.card) : WZ1PaperTubeShading family where
  carrier tube := shading.carrier tube ∩
    proposition63AxialAnchorRegion
      (Delta := Delta) shading anchor hrho distinguished
  measurable_carrier tube := (shading.measurable_carrier tube).inter
    (proposition63AxialAnchorRegion_measurable
      (Delta := Delta) shading anchor hrho distinguished)
  subset_body tube := Set.inter_subset_left.trans (shading.subset_body tube)

lemma proposition63AxialAnchorShading_subshading
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (distinguished : Fin family.card) :
    PaperIsSubshading
      (proposition63AxialAnchorShading
        (Delta := Delta) shading anchor hrho distinguished) shading :=
  fun _ => Set.inter_subset_left

lemma proposition63AxialAnchorRegion_mem_of_interval
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {anchor : Kakeya.DeltaTube rho} {hrho : 0 < rho}
    {distinguished : Fin family.card}
    (interval : commonSliceIntervalType Delta)
    (hmeets : proposition63AxialPartitionMeets
      (Delta := Delta) shading anchor hrho
      distinguished interval)
    {point : Point3}
    (hpoint : point ∈ proposition63AxialSlab anchor hrho Delta interval.1) :
    point ∈ proposition63AxialAnchorRegion
      (Delta := Delta) shading anchor hrho distinguished := by
  apply Set.mem_iUnion.mpr
  exact ⟨interval, by rw [if_pos hmeets]; exact hpoint⟩

theorem proposition63AxialAnchorShading_mass
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (hDelta : 0 < Delta)
    (distinguished : Fin family.card) :
    (proposition63AxialAnchorShading
      (Delta := Delta) shading anchor hrho distinguished).mass =
      commonSliceRetainedMass
        (proposition63AxialPartitionMeets
          (Delta := Delta) shading anchor hrho)
        (proposition63AxialPartitionMass
          (Delta := Delta) shading anchor hrho)
        distinguished := by
  classical
  rw [commonSliceRetainedMass]
  simp only [proposition63AxialPartitionMass]
  rw [← Finset.sum_filter]
  simp_rw [commonSliceSlabMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tube _
  let selectedIntervals :=
    (Finset.univ : Finset (commonSliceIntervalType Delta)).filter
      fun interval => proposition63AxialPartitionMeets
        (Delta := Delta) shading anchor hrho distinguished interval
  have hpairwise : Set.PairwiseDisjoint
      (↑selectedIntervals : Set (commonSliceIntervalType Delta))
      (fun interval => shading.carrier tube ∩
        proposition63AxialSlab anchor hrho Delta interval.1) := by
    intro first _ second _ hne
    have hvalueNe : first.1 ≠ second.1 := fun heq => hne (Subtype.ext heq)
    exact (proposition63_axialSlab_disjoint hDelta anchor hrho hvalueNe).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeasurable : ∀ interval ∈ selectedIntervals,
      MeasurableSet (shading.carrier tube ∩
        proposition63AxialSlab anchor hrho Delta interval.1) := by
    intro interval _
    exact (shading.measurable_carrier tube).inter
      (proposition63AxialSlab_measurable anchor hrho interval.1)
  have hunion :
      ⋃ interval ∈ selectedIntervals, shading.carrier tube ∩
        proposition63AxialSlab anchor hrho Delta interval.1 =
      (proposition63AxialAnchorShading
        (Delta := Delta) shading anchor hrho distinguished).carrier tube := by
    ext point
    constructor
    · rintro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨interval, hinterval, hsource, hslab⟩
      have hmeets := (Finset.mem_filter.mp hinterval).2
      exact ⟨hsource, proposition63AxialAnchorRegion_mem_of_interval
        (Delta := Delta) interval hmeets hslab⟩
    · rintro ⟨hsource, hregion⟩
      rcases Set.mem_iUnion.mp hregion with ⟨interval, hinterval⟩
      by_cases hmeets : proposition63AxialPartitionMeets
          (Delta := Delta) shading anchor hrho
          distinguished interval
      · rw [if_pos hmeets] at hinterval
        exact Set.mem_iUnion₂.mpr ⟨interval,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmeets⟩,
          hsource, hinterval⟩
      · rw [if_neg hmeets] at hinterval
        exact False.elim hinterval
  change volume ((proposition63AxialAnchorShading
    (Delta := Delta) shading anchor hrho distinguished).carrier tube) = _
  rw [← hunion, MeasureTheory.measure_biUnion_finset hpairwise hmeasurable]

structure Proposition63AxialCommonSliceData
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (target : ENNReal) where
  distinguished : Fin family.card
  subshading : PaperIsSubshading
    (proposition63AxialAnchorShading
      (Delta := Delta) source anchor hrho distinguished) source
  retained_mass : target ≤
    (proposition63AxialAnchorShading
      (Delta := Delta) source anchor hrho distinguished).mass

namespace Proposition63AxialCommonSliceData

def shading
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {anchor : Kakeya.DeltaTube rho} {hrho : 0 < rho}
    {target : ENNReal}
    (data : Proposition63AxialCommonSliceData
      (Delta := Delta) source anchor hrho target) :
    WZ1PaperTubeShading family :=
  proposition63AxialAnchorShading
    (Delta := Delta) source anchor hrho data.distinguished

end Proposition63AxialCommonSliceData

theorem proposition63_axial_common_slice
    {delta rho Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (hanchorLine : WZ1PaperTubeInLineClass anchor)
    (hfamilyNonempty : family.Nonempty)
    (hline : WZ1PaperIsLineClass family)
    (hcovered : ∀ tube : Fin family.card,
      WZ1PaperTubeCovers (family.tube tube) anchor)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 24)
    (hrhoOne : rho ≤ 1) (hDelta : 0 < Delta)
    (target : ENNReal)
    (haggregate :
      (family.card : ENNReal) * target *
          ((Fintype.card (commonSliceIntervalType Delta) : ENNReal) *
            commonSliceSingleTubeBound delta (100 * Delta)) ≤
        source.mass ^ 2) :
    Nonempty (Proposition63AxialCommonSliceData
      (Delta := Delta) source anchor hrho target) := by
  rcases exists_proposition63_axial_anchor source anchor hrho hanchorLine
      hfamilyNonempty hline hcovered hdelta hdeltaSmall hrhoOne hDelta
      target haggregate with ⟨distinguished, hretained⟩
  let shading := proposition63AxialAnchorShading
    (Delta := Delta) source anchor hrho distinguished
  have hsub := proposition63AxialAnchorShading_subshading
    (Delta := Delta) source anchor hrho distinguished
  have hmass : target ≤ shading.mass := hretained.trans_eq
    (proposition63AxialAnchorShading_mass
      (Delta := Delta) source anchor hrho hDelta distinguished).symm
  exact ⟨{
    distinguished := distinguished
    subshading := hsub
    retained_mass := hmass
  }⟩

end Kakeya.Assouad.PureWZ2

end
