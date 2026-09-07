import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceEnergy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Shaded mass and meeting counts in common-slice slabs

This module turns a per-tube slab-volume bound into the paper estimate
`m_I ≤ B n_I`.  The geometry of the actual longitudinal slabs is kept
separate.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- One tube meets a slab when its selected shading has a point there. -/
def commonSliceSlabMeets
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (slab : Set Point3)
    (tube : Fin family.card) : Prop :=
  (shading.carrier tube ∩ slab).Nonempty

/-- Total indexed shaded mass in one slab. -/
def commonSliceSlabMass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (slab : Set Point3) : ENNReal :=
  ∑ tube : Fin family.card, volume (shading.carrier tube ∩ slab)

lemma commonSliceSlabMass_ne_top
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (slab : Set Point3)
    (hcarrierFinite : ∀ tube, volume (shading.carrier tube) ≠ ⊤) :
    commonSliceSlabMass shading slab ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro tube _
  exact ((measure_mono Set.inter_subset_left).trans_lt
    (hcarrierFinite tube).lt_top).ne

/-- The paper estimate `m_I ≤ B n_I` from a uniform single-tube slab bound. -/
theorem commonSliceSlabMass_le_meetingCount
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (slab : Set Point3)
    (B : ENNReal)
    (hvolume : ∀ tube, commonSliceSlabMeets shading slab tube →
      volume (shading.carrier tube ∩ slab) ≤ B) :
    commonSliceSlabMass shading slab ≤
      B * (commonSliceMeetingCount
        (fun tube : Fin family.card => fun _ : Unit =>
          commonSliceSlabMeets shading slab tube) () : ENNReal) := by
  classical
  let meeting : Finset (Fin family.card) :=
    Finset.univ.filter fun tube => commonSliceSlabMeets shading slab tube
  have hzero : ∀ tube ∉ meeting,
      volume (shading.carrier tube ∩ slab) = 0 := by
    intro tube htube
    have hnot : ¬ commonSliceSlabMeets shading slab tube := by
      simpa [meeting] using htube
    have hempty : shading.carrier tube ∩ slab = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnot
    rw [hempty, measure_empty]
  calc
    commonSliceSlabMass shading slab =
        ∑ tube ∈ meeting, volume (shading.carrier tube ∩ slab) := by
      rw [commonSliceSlabMass, ← Finset.sum_subset
        (Finset.subset_univ meeting)]
      intro tube _ htube
      exact hzero tube htube
    _ ≤ ∑ _tube ∈ meeting, B := by
      apply Finset.sum_le_sum
      intro tube htube
      exact hvolume tube (by simpa [meeting] using htube)
    _ = B * (meeting.card : ENNReal) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = B * (commonSliceMeetingCount
        (fun tube : Fin family.card => fun _ : Unit =>
          commonSliceSlabMeets shading slab tube) () : ENNReal) := by
      simp [meeting, commonSliceMeetingCount]

end Kakeya.Assouad.PureWZ2

end
