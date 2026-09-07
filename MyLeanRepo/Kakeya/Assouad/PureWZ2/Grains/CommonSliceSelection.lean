import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceHeightPartition
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceEnergy
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma17GridPruningBudget
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Concrete common-slice anchor selection

Combine the exact height partition, the per-tube slab bound, finite
Cauchy--Schwarz, and double counting to choose the paper's distinguished
anchor tube `T₀`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

def commonSliceIntervalType (Delta : ℝ) :=
  {index : ℤ // index ∈ commonSliceHeightIndices Delta}

instance (Delta : ℝ) : Fintype (commonSliceIntervalType Delta) :=
  Finset.fintypeCoeSort _

def commonSlicePartitionMass
    {delta Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (interval : commonSliceIntervalType Delta) : ENNReal :=
  commonSliceSlabMass shading (commonSliceHeightSlab Delta interval.1)

def commonSlicePartitionMeets
    {delta Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (tube : Fin family.card)
    (interval : commonSliceIntervalType Delta) : Prop :=
  commonSliceSlabMeets shading
    (commonSliceHeightSlab Delta interval.1) tube

lemma commonSlicePartitionMass_sum
    {delta Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hDelta : 0 < Delta) :
    (∑ interval : commonSliceIntervalType Delta,
      commonSlicePartitionMass shading interval) = shading.mass := by
  rw [show (∑ interval : commonSliceIntervalType Delta,
      commonSlicePartitionMass shading interval) =
      ∑ index ∈ commonSliceHeightIndices Delta,
        commonSliceSlabMass shading (commonSliceHeightSlab Delta index) by
    exact (Finset.sum_subtype
      (s := commonSliceHeightIndices Delta)
      (f := fun index =>
        commonSliceSlabMass shading (commonSliceHeightSlab Delta index))
      (p := fun index => index ∈ commonSliceHeightIndices Delta)
      (by simp)).symm]
  exact commonSlice_height_slab_mass_sum shading hDelta

/-- Concrete paper common-slice selection, with the final aggregate power
absorption left explicit. -/
theorem exists_common_slice_height_anchor
    {delta Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hfamilyNonempty : family.Nonempty)
    (hline : WZ1PaperIsLineClass family)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hDelta : 0 < Delta)
    (target : ENNReal)
    (haggregate :
      (family.card : ENNReal) * target *
          ((Fintype.card (commonSliceIntervalType Delta) : ENNReal) *
            commonSliceSingleTubeBound delta Delta) ≤
        shading.mass ^ 2) :
    ∃ anchor : Fin family.card,
      target ≤ commonSliceRetainedMass
        (commonSlicePartitionMeets (Delta := Delta) shading)
        (commonSlicePartitionMass (Delta := Delta) shading) anchor := by
  letI : Nonempty (Fin family.card) := ⟨⟨0, hfamilyNonempty⟩⟩
  have hintervalNonempty : Nonempty (commonSliceIntervalType Delta) := by
    let index := Int.floor (0 / Delta)
    refine ⟨⟨index, ?_⟩⟩
    apply commonSlice_height_index_mem hDelta
    norm_num
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
      commonSlicePartitionMass shading interval ≠ ⊤ := by
    intro interval
    apply commonSliceSlabMass_ne_top
    intro tube
    have hsingle : volume (shading.carrier tube) ≤ shading.mass := by
      exact Finset.single_le_sum
        (fun index (_ : index ∈ (Finset.univ : Finset (Fin family.card))) =>
          (show (0 : ENNReal) ≤ volume (shading.carrier index) from bot_le))
        (Finset.mem_univ tube)
    exact hsingle.trans_lt hshadingFinite.lt_top |>.ne
  have hmassCount : ∀ interval : commonSliceIntervalType Delta,
      commonSlicePartitionMass shading interval ≤
        commonSliceSingleTubeBound delta Delta *
          (commonSliceMeetingCount
            (commonSlicePartitionMeets shading) interval : ENNReal) := by
    intro interval
    change commonSliceSlabMass shading
        (commonSliceHeightSlab Delta interval.1) ≤
      commonSliceSingleTubeBound delta Delta *
        (commonSliceMeetingCount
          (fun tube : Fin family.card =>
            commonSlicePartitionMeets (Delta := Delta) shading tube)
          interval : ENNReal)
    have hcount : commonSliceMeetingCount
        (fun tube : Fin family.card => fun _ : Unit =>
          commonSliceSlabMeets shading
            (commonSliceHeightSlab Delta interval.1) tube) () =
      commonSliceMeetingCount
        (fun tube : Fin family.card =>
          commonSlicePartitionMeets (Delta := Delta) shading tube)
        interval := by
      unfold commonSliceMeetingCount commonSlicePartitionMeets
      congr
    rw [← hcount]
    exact commonSlice_height_slab_mass_le_meetingCount shading hline hdelta
      hdeltaSmall hDelta interval.1
  have hAZero : commonSliceSingleTubeBound delta Delta ≠ 0 := by
    simp [commonSliceSingleTubeBound]
    positivity
  have hAFinite : commonSliceSingleTubeBound delta Delta ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  apply exists_common_slice_anchor_of_mass_square
    (commonSlicePartitionMeets (Delta := Delta) shading)
    (commonSlicePartitionMass (Delta := Delta) shading) hmassFinite
    (commonSliceSingleTubeBound delta Delta) target hAZero hAFinite
    hmassCount
  rw [commonSlicePartitionMass_sum shading hDelta]
  simpa using haggregate

end Kakeya.Assouad.PureWZ2

end
