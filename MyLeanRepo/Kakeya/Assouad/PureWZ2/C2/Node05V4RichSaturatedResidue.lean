import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedTrapezoids
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderReentryTrace

/-!
# A mass-weighted separated residue of saturated heavy slabs

The weight of a slab is the indexed mass of its literal complete-height
restriction of the original source shading.  The mod-`64` selection is made
only after all exact dependent Theorem-5.2 tails have been fixed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private lemma saturatedSlabResidue_separated
    {first second : ℤ}
    (hne : first ≠ second)
    (hmod : first % (64 : ℤ) = second % (64 : ℤ)) :
    (64 : ℤ) ≤ |first - second| := by
  have hzero : (first - second) % (64 : ℤ) = 0 := by
    rw [Int.sub_emod, hmod]
    simp
  exact Int.le_abs_of_dvd (sub_ne_zero.mpr hne)
    (by rwa [Int.dvd_iff_emod_eq_zero])

/-- One mod-`64` class of heavy source slabs, weighted by the indexed mass of
the exact complete-height restriction in each slab. -/
structure PureWZ2Node05V4RichSaturatedResidueData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection}
    (trapezoids : PureWZ2Node05V4RichSaturatedTrapezoidFamily tail) where
  residue : Fin 64
  selected : Finset {heightIndex //
    heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}
  selected_eq : selected = Finset.univ.filter fun heightIndex =>
    (heightIndex.1.1 % (64 : ℤ)).toNat = residue
  selected_nonempty : selected.Nonempty
  selectedIndex : Fin selected.card → {heightIndex //
    heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}
  selectedIndex_mem : ∀ index, selectedIndex index ∈ selected
  selectedIndex_injective : Function.Injective selectedIndex
  selectedIndex_surjective :
    ∀ heightIndex ∈ selected, ∃ index, selectedIndex index = heightIndex
  total_completeMass_le :
    (∑ heightIndex : {heightIndex //
        heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback},
      (tail.complete heightIndex).sourceRestriction.mass) ≤
        64 * ∑ index : Fin selected.card,
          (tail.complete (selectedIndex index)).sourceRestriction.mass
  separated_cores :
    ∀ first second : Fin selected.card, first ≠ second →
      ∀ z ∈ (trapezoids.block (selectedIndex first)).trapezoid.core,
        ∀ w ∈ (trapezoids.block (selectedIndex second)).trapezoid.core,
          Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w|

namespace PureWZ2Node05V4RichSaturatedTrapezoidFamily

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection}
    (trapezoids : PureWZ2Node05V4RichSaturatedTrapezoidFamily tail)

theorem completeMass_pos
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    0 < (tail.complete heightIndex).sourceRestriction.mass := by
  let complete := tail.complete heightIndex
  have hfloorNat : 0 < complete.multiplicityFloor := by
    rw [complete.multiplicityFloor_eq]
    exact Nat.mul_pos
      twoScale.first.fourDegreeReceipts.fineDegreeFloor_pos
      twoScale.first.fourDegreeReceipts.muFine_pos
  have hfloor : 0 < (complete.multiplicityFloor : ENNReal) := by
    exact_mod_cast hfloorNat
  have hvolume : 0 < volume complete.sourceRestriction.union := by
    rw [complete.sourceRestriction_volume_eq]
    have hcard : 0 < (complete.completeSourceCells.card : ENNReal) := by
      exact_mod_cast complete.completeSourceCells_nonempty.card_pos
    exact ENNReal.mul_pos hcard.ne'
      pullback.firstPostBalanced.cellMass_pos.ne'
  exact (ENNReal.mul_pos hfloor.ne' hvolume.ne').trans_le
    complete.sourceRestriction_mass_lower

private theorem saturated_cores_separated_of_slab_gap
    (first second : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback})
    (hslabs : (64 : ℤ) ≤ |first.1.1 - second.1.1|) :
    ∀ z ∈ (trapezoids.block first).trapezoid.core,
      ∀ w ∈ (trapezoids.block second).trapezoid.core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  let root := Real.sqrt rho
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hscale := pureWZ2SourceHorizontalFinalScale_sqrt_le hrho
  intro z hz w hw
  rw [(trapezoids.block first).core_eq] at hz
  rw [(trapezoids.block second).core_eq] at hw
  by_cases horder : first.1.1 < second.1.1
  · have hdiffInt : (64 : ℤ) ≤ second.1.1 - first.1.1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr horder.le)] at hslabs
      simpa using hslabs
    have hdiffReal : (64 : ℝ) ≤
        (second.1.1 : ℝ) - (first.1.1 : ℝ) := by
      exact_mod_cast hdiffInt
    have hwz : 63 * root ≤ w - z := by
      dsimp only [root] at hroot ⊢
      nlinarith [hz.2, hw.1]
    have hwzNonneg : 0 ≤ w - z :=
      (mul_pos (by norm_num) hroot).le.trans hwz
    rw [abs_sub_comm, abs_of_nonneg hwzNonneg]
    exact hscale.trans (by
      dsimp only [root] at hwz ⊢
      nlinarith)
  · have hreverse : second.1.1 < first.1.1 := by
      have hne : first.1.1 ≠ second.1.1 := by
        intro heq
        rw [heq, sub_self, abs_zero] at hslabs
        norm_num at hslabs
      omega
    have hdiffInt : (64 : ℤ) ≤ first.1.1 - second.1.1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hreverse.le)] at hslabs
      exact hslabs
    have hdiffReal : (64 : ℝ) ≤
        (first.1.1 : ℝ) - (second.1.1 : ℝ) := by
      exact_mod_cast hdiffInt
    have hzw : 63 * root ≤ z - w := by
      dsimp only [root] at hroot ⊢
      nlinarith [hz.1, hw.2]
    have hzwNonneg : 0 ≤ z - w :=
      (mul_pos (by norm_num) hroot).le.trans hzw
    rw [abs_of_nonneg hzwNonneg]
    exact hscale.trans (by
      dsimp only [root] at hzw ⊢
      nlinarith)

/-- Select one separated heavy-slab class after all complete source-height
restrictions have been constructed. -/
theorem selectResidue :
    Nonempty (PureWZ2Node05V4RichSaturatedResidueData trapezoids) := by
  let HeavySlab := {heightIndex //
    heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}
  let label : HeavySlab → Fin 64 := fun heightIndex =>
    ⟨(heightIndex.1.1 % (64 : ℤ)).toNat, by
      have hn := Int.emod_nonneg heightIndex.1.1
        (by norm_num : (64 : ℤ) ≠ 0)
      have hl := Int.emod_lt_of_pos heightIndex.1.1
        (by norm_num : (0 : ℤ) < 64)
      omega⟩
  let weight : HeavySlab → ENNReal := fun heightIndex =>
    (tail.complete heightIndex).sourceRestriction.mass
  rcases finset_ennreal_weighted_pigeonhole (n := 64) (by norm_num)
      Finset.univ weight label with ⟨residue, hselected⟩
  let selected := Finset.univ.filter fun heightIndex : HeavySlab =>
    (heightIndex.1.1 % (64 : ℤ)).toNat = residue
  have hselected' :
      (∑ heightIndex : HeavySlab, weight heightIndex) ≤
        64 * ∑ heightIndex ∈ selected, weight heightIndex := by
    simpa [selected, label, Fin.ext_iff] using hselected
  let first : HeavySlab :=
    ⟨Classical.choose pullback.heavySlabs_nonempty,
      Classical.choose_spec pullback.heavySlabs_nonempty⟩
  have htotalPos : 0 < ∑ heightIndex : HeavySlab, weight heightIndex := by
    rw [Finset.sum_pos_iff]
    exact ⟨first, Finset.mem_univ _, by
      simpa only [weight] using completeMass_pos (tail := tail) first⟩
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hzero : ∑ heightIndex ∈ selected, weight heightIndex = 0 := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
    have hleZero : (∑ heightIndex : HeavySlab, weight heightIndex) ≤ 0 := by
      simpa [hzero] using hselected'
    exact (not_le_of_gt htotalPos) hleZero
  let selectedEquiv := selected.equivFin
  let selectedIndex : Fin selected.card → HeavySlab := fun index =>
    (selectedEquiv.symm index).1
  have hmem : ∀ index, selectedIndex index ∈ selected := fun index =>
    (selectedEquiv.symm index).2
  have hinj : Function.Injective selectedIndex := by
    intro firstIndex secondIndex heq
    apply selectedEquiv.symm.injective
    exact Subtype.ext heq
  have hsurj : ∀ heightIndex ∈ selected,
      ∃ index, selectedIndex index = heightIndex := by
    intro heightIndex hheightIndex
    let selectedValue : {heightIndex // heightIndex ∈ selected} :=
      ⟨heightIndex, hheightIndex⟩
    exact ⟨selectedEquiv selectedValue, by
      change (selectedEquiv.symm (selectedEquiv selectedValue)).1 = heightIndex
      simp [selectedValue]⟩
  have hsum :
      (∑ heightIndex ∈ selected, weight heightIndex) =
        ∑ index : Fin selected.card, weight (selectedIndex index) := by
    symm
    apply Finset.sum_bij (fun index _ => selectedIndex index)
    · exact fun index _ => hmem index
    · exact fun firstIndex _ secondIndex _ heq => hinj heq
    · intro heightIndex hheightIndex
      rcases hsurj heightIndex hheightIndex with ⟨index, hindex⟩
      exact ⟨index, Finset.mem_univ index, hindex⟩
    · intro _ _
      rfl
  refine ⟨{
    residue := residue
    selected := selected
    selected_eq := rfl
    selected_nonempty := hselectedNonempty
    selectedIndex := selectedIndex
    selectedIndex_mem := hmem
    selectedIndex_injective := hinj
    selectedIndex_surjective := hsurj
    total_completeMass_le := by
      rw [← hsum]
      simpa only [weight] using hselected'
    separated_cores := ?_
  }⟩
  intro firstIndex secondIndex hne
  have hindexNe : selectedIndex firstIndex ≠ selectedIndex secondIndex :=
    fun heq => hne (hinj heq)
  have hslabNe :
      (selectedIndex firstIndex).1.1 ≠
        (selectedIndex secondIndex).1.1 := by
    intro heq
    exact hindexNe (Subtype.ext (Subtype.ext heq))
  have hsameResidue :
      (selectedIndex firstIndex).1.1 % (64 : ℤ) =
        (selectedIndex secondIndex).1.1 % (64 : ℤ) := by
    have hfirst := (Finset.mem_filter.mp (hmem firstIndex)).2
    have hsecond := (Finset.mem_filter.mp (hmem secondIndex)).2
    have hn1 := Int.emod_nonneg (selectedIndex firstIndex).1.1
      (by norm_num : (64 : ℤ) ≠ 0)
    have hn2 := Int.emod_nonneg (selectedIndex secondIndex).1.1
      (by norm_num : (64 : ℤ) ≠ 0)
    have hcast := congrArg (fun value : ℕ => (value : ℤ))
      (hfirst.trans hsecond.symm)
    simpa [Int.toNat_of_nonneg hn1, Int.toNat_of_nonneg hn2] using hcast
  exact trapezoids.saturated_cores_separated_of_slab_gap _ _
    (saturatedSlabResidue_separated hslabNe hsameResidue)

end PureWZ2Node05V4RichSaturatedTrapezoidFamily

namespace PureWZ2Node05V4RichSaturatedResidueData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection}
    {trapezoids : PureWZ2Node05V4RichSaturatedTrapezoidFamily tail}
    (residueData : PureWZ2Node05V4RichSaturatedResidueData trapezoids)

/-- Literal union of the selected complete-height restrictions. -/
def shading : WZ1PaperTubeShading current.grain.family where
  carrier sourceIndex := ⋃ index : Fin residueData.selected.card,
    (tail.complete (residueData.selectedIndex index)).sourceRestriction.carrier
      sourceIndex
  measurable_carrier sourceIndex := MeasurableSet.iUnion fun index =>
    (tail.complete (residueData.selectedIndex index)).sourceRestriction
      |>.measurable_carrier sourceIndex
  subset_body sourceIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
    exact (tail.complete (residueData.selectedIndex index)).sourceRestriction
      |>.subset_body sourceIndex hindex

theorem mem_shading_union_iff (point : Point3) :
    point ∈ residueData.shading.union ↔
      ∃ index : Fin residueData.selected.card,
        point ∈ (tail.complete
          (residueData.selectedIndex index)).sourceRestriction.union := by
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
    exact ⟨index, sourceIndex, hindex⟩
  · rintro ⟨index, sourceIndex, hpoint⟩
    exact ⟨sourceIndex, Set.mem_iUnion.mpr ⟨index, hpoint⟩⟩

theorem subshading :
    PureWZ2PaperIsSubshading residueData.shading current.grain.shading := by
  intro sourceIndex point hpoint
  rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
  exact (tail.complete (residueData.selectedIndex index))
    |>.sourceRestriction_sub_source sourceIndex hindex

theorem cubical : WZ1PaperIsCubicalShading residueData.shading := by
  intro sourceIndex point hpoint other hother
  rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
  exact Set.mem_iUnion.mpr ⟨index,
    (tail.complete (residueData.selectedIndex index))
      |>.sourceRestriction_whole_delta_cells sourceIndex point hindex hother⟩

theorem sourceRestriction_union_pairwise_disjoint :
    Pairwise fun first second : Fin residueData.selected.card =>
      Disjoint
        (tail.complete (residueData.selectedIndex first)).sourceRestriction.union
        (tail.complete (residueData.selectedIndex second)).sourceRestriction.union := by
  intro first second hne
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  have hindexNe : residueData.selectedIndex first ≠
      residueData.selectedIndex second := fun heq =>
    hne (residueData.selectedIndex_injective heq)
  have hslabNe : (residueData.selectedIndex first).1.1 ≠
      (residueData.selectedIndex second).1.1 := by
    intro heq
    exact hindexNe (Subtype.ext (Subtype.ext heq))
  have hfirstWindow := (tail.complete (residueData.selectedIndex first))
    |>.sourceRestriction_height_window point hfirst
  have hsecondWindow := (tail.complete (residueData.selectedIndex second))
    |>.sourceRestriction_height_window point hsecond
  rw [(family.block (residueData.selectedIndex first)).heightIndex_eq]
    at hfirstWindow
  rw [(family.block (residueData.selectedIndex second)).heightIndex_eq]
    at hsecondWindow
  by_cases horder : (residueData.selectedIndex first).1.1 <
      (residueData.selectedIndex second).1.1
  · have hstep : (residueData.selectedIndex first).1.1 + 1 ≤
        (residueData.selectedIndex second).1.1 := by omega
    have hstepReal :
        ((residueData.selectedIndex first).1.1 : ℝ) + 1 ≤
          (residueData.selectedIndex second).1.1 := by exact_mod_cast hstep
    have hroot : 0 < Real.sqrt rho := by
      apply Real.sqrt_pos.mpr
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    nlinarith [hfirstWindow.2, hsecondWindow.1]
  · have hstep : (residueData.selectedIndex second).1.1 + 1 ≤
        (residueData.selectedIndex first).1.1 := by omega
    have hstepReal :
        ((residueData.selectedIndex second).1.1 : ℝ) + 1 ≤
          (residueData.selectedIndex first).1.1 := by exact_mod_cast hstep
    have hroot : 0 < Real.sqrt rho := by
      apply Real.sqrt_pos.mpr
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    nlinarith [hfirstWindow.1, hsecondWindow.2]

theorem shading_mass_eq_sum :
    residueData.shading.mass =
      ∑ index : Fin residueData.selected.card,
        (tail.complete
          (residueData.selectedIndex index)).sourceRestriction.mass := by
  have hcarrier : ∀ sourceIndex : Fin current.grain.family.card,
      Pairwise fun first second : Fin residueData.selected.card =>
        Disjoint
          ((tail.complete
            (residueData.selectedIndex first)).sourceRestriction.carrier sourceIndex)
          ((tail.complete
            (residueData.selectedIndex second)).sourceRestriction.carrier sourceIndex) := by
    intro sourceIndex first second hne
    exact (residueData.sourceRestriction_union_pairwise_disjoint hne).mono
      (fun point (hpoint : point ∈
          (tail.complete
            (residueData.selectedIndex first)).sourceRestriction.carrier sourceIndex) =>
        show point ∈ (tail.complete
          (residueData.selectedIndex first)).sourceRestriction.union from
            ⟨sourceIndex, hpoint⟩)
      (fun point (hpoint : point ∈
          (tail.complete
            (residueData.selectedIndex second)).sourceRestriction.carrier sourceIndex) =>
        show point ∈ (tail.complete
          (residueData.selectedIndex second)).sourceRestriction.union from
            ⟨sourceIndex, hpoint⟩)
  calc
    residueData.shading.mass =
        ∑ sourceIndex : Fin current.grain.family.card,
          volume (⋃ index : Fin residueData.selected.card,
            (tail.complete
              (residueData.selectedIndex index)).sourceRestriction.carrier
                sourceIndex) := rfl
    _ = ∑ sourceIndex : Fin current.grain.family.card,
          ∑ index : Fin residueData.selected.card,
            volume ((tail.complete
              (residueData.selectedIndex index)).sourceRestriction.carrier
                sourceIndex) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [MeasureTheory.measure_iUnion (hcarrier sourceIndex)
        (fun index => (tail.complete
          (residueData.selectedIndex index)).sourceRestriction.measurable_carrier
            sourceIndex)]
      simp [tsum_fintype]
    _ = ∑ index : Fin residueData.selected.card,
          ∑ sourceIndex : Fin current.grain.family.card,
            volume ((tail.complete
              (residueData.selectedIndex index)).sourceRestriction.carrier
                sourceIndex) := by
      rw [Finset.sum_comm]
    _ = ∑ index : Fin residueData.selected.card,
        (tail.complete
          (residueData.selectedIndex index)).sourceRestriction.mass := rfl

theorem total_completeMass_le_shading_mass :
    (∑ heightIndex : {heightIndex //
        heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback},
      (tail.complete heightIndex).sourceRestriction.mass) ≤
        64 * residueData.shading.mass := by
  rw [residueData.shading_mass_eq_sum]
  exact residueData.total_completeMass_le

/-- Exact one-scale trapezoid geometry on the literal selected source
restriction, before the final density/re-entry argument. -/
theorem geometry : Nonempty (PureWZ2LiteralCurrentSourceOneScaleGeometry
    current.grain residueData.shading finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  let first : Fin residueData.selected.card :=
    ⟨0, Finset.card_pos.mpr residueData.selected_nonempty⟩
  let firstBlock := trapezoids.block (residueData.selectedIndex first)
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    dsimp only [pureWZ2SourceHorizontalFinalScale]
    positivity
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  have hdeltaScale : delta ≤ pureWZ2SourceHorizontalFinalScale rho := by
    calc
      delta ≤ rho := hdeltaRho
      _ ≤ pureWZ2SourceHorizontalFinalScale rho := by
        dsimp only [pureWZ2SourceHorizontalFinalScale]
        nlinarith
  have hscaleOne : pureWZ2SourceHorizontalFinalScale rho ≤ 1 := by
    rw [← firstBlock.scale_eq]
    exact firstBlock.scale_le_one
  let trapezoidSet : Finset WZ1VerticalTrapezoid :=
    Finset.univ.image fun index : Fin residueData.selected.card =>
      (trapezoids.block (residueData.selectedIndex index)).trapezoid
  have htrapezoidNonempty : trapezoidSet.Nonempty :=
    ⟨firstBlock.trapezoid,
      Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩⟩
  exact ⟨{
    rho_pos := hscalePos
    delta_le_rho := hdeltaScale
    rho_le_one := hscaleOne
    trapezoids := trapezoidSet
    trapezoids_nonempty := htrapezoidNonempty
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _hindex, rfl⟩
      rw [(trapezoids.block (residueData.selectedIndex index)).height_eq]
      exact (trapezoids.block
        (residueData.selectedIndex index)).scale_eq
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _hindex, rfl⟩
      exact (trapezoids.block
        (residueData.selectedIndex index)).slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _hindex, rfl⟩
      simpa [(trapezoids.block
        (residueData.selectedIndex index)).scale_eq] using
          (trapezoids.block
            (residueData.selectedIndex index)).length_bounds
    separated_cores := by
      intro firstTrap hfirstTrap secondTrap hsecondTrap hne
      rcases Finset.mem_image.mp hfirstTrap with
        ⟨firstIndex, _hfirstIndex, rfl⟩
      rcases Finset.mem_image.mp hsecondTrap with
        ⟨secondIndex, _hsecondIndex, rfl⟩
      have hindexNe : firstIndex ≠ secondIndex := by
        intro heq
        subst secondIndex
        exact hne rfl
      exact residueData.separated_cores firstIndex secondIndex hindexNe
    slope_approximation := by
      intro targetTrap htargetTrap z hz hslice
      rcases Finset.mem_image.mp htargetTrap with
        ⟨targetIndex, _htargetIndex, rfl⟩
      rcases Set.nonempty_iff_ne_empty.mpr hslice with
        ⟨point, hpoint, hpointHeight⟩
      rcases (residueData.mem_shading_union_iff point).mp hpoint with
        ⟨sourceIndex, hsourcePoint⟩
      have hsourceSlice : horizontalSlice
          (tail.complete
            (residueData.selectedIndex sourceIndex)).sourceRestriction.union z ≠ ∅ :=
        Set.nonempty_iff_ne_empty.mp
          ⟨point, hsourcePoint, hpointHeight⟩
      have hsourceCore := (trapezoids.block
        (residueData.selectedIndex sourceIndex)).active_height_coverage
          z hsourceSlice
      by_cases heq :
          (trapezoids.block
              (residueData.selectedIndex targetIndex)).trapezoid =
            (trapezoids.block
              (residueData.selectedIndex sourceIndex)).trapezoid
      · rw [heq]
        simpa [(trapezoids.block
          (residueData.selectedIndex sourceIndex)).scale_eq] using
            (trapezoids.block (residueData.selectedIndex sourceIndex))
              |>.slope_approximation z hsourceCore hsourceSlice
      · have hindexNe : targetIndex ≠ sourceIndex := by
          intro hindex
          subst sourceIndex
          exact heq rfl
        have hsep := residueData.separated_cores targetIndex sourceIndex
          hindexNe z hz z hsourceCore
        exact False.elim <|
          (not_le_of_gt (Real.sqrt_pos.mpr hscalePos)) <| by
            simpa using hsep
    active_height_coverage := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with
        ⟨point, hpoint, hpointHeight⟩
      rcases (residueData.mem_shading_union_iff point).mp hpoint with
        ⟨index, hindexPoint⟩
      have hindexSlice : horizontalSlice
          (tail.complete
            (residueData.selectedIndex index)).sourceRestriction.union z ≠ ∅ :=
        Set.nonempty_iff_ne_empty.mp
          ⟨point, hindexPoint, hpointHeight⟩
      exact ⟨
        (trapezoids.block (residueData.selectedIndex index)).trapezoid,
        Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩,
        (trapezoids.block
          (residueData.selectedIndex index)).active_height_coverage
            z hindexSlice⟩
  }⟩

end PureWZ2Node05V4RichSaturatedResidueData

end Kakeya.Assouad

end
