import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import Mathlib.Tactic

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined Metric Set

/-- Extended segment of a tube (length 2, centered at midpoint). -/
def extendedSegment {δ : ℝ} (T : Kakeya.DeltaTube δ) : Set Point3 :=
  (fun s : ℝ => T.base + s • T.direction) '' Set.Icc (-1 / 2) (3 / 2)

/-- Points on a tube's unit segment belong to its carrier. -/
lemma point_on_segment_in_carrier
    {δ : ℝ} (hδ : 0 ≤ δ) (T : Kakeya.DeltaTube δ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    T.base + t • T.direction ∈ T.carrier := by
  let y := T.base + t • T.direction
  have hy : y ∈ unitSegment T.base T.direction := ⟨t, ht, rfl⟩
  exact Metric.mem_cthickening_of_dist_le y y δ (unitSegment T.base T.direction) hy (by simp [hδ])

/-- Points in the 2-dilation are within 2δ of the extended segment. -/
lemma dilation_infDist_extended
    {δ : ℝ} (hδ : 0 ≤ δ) (T : Kakeya.DeltaTube δ) (x : Point3)
    (hx : x ∈ wz2PaperCenteredDilatedCarrier (2 : ℝ) T) :
    Metric.infDist x (extendedSegment T) ≤ 2 * δ := by
  let m := T.base + (1 / 2 : ℝ) • T.direction
  let h_hom : Point3 → Point3 := AffineMap.homothety m (2 : ℝ)
  let S_ext := extendedSegment T
  let S_unit := (fun s : ℝ => T.base + s • T.direction) '' Set.Icc (0 : ℝ) 1
  rcases hx with ⟨y, hy, rfl⟩
  have h_ne : S_unit.Nonempty := ⟨T.base, ⟨0, by norm_num, by simp⟩⟩
  have hy_dist : Metric.infDist y S_unit ≤ δ := by
    have h1 : Metric.infEDist y S_unit ≤ ENNReal.ofReal δ := Metric.mem_cthickening_iff.mp hy
    have h2 : Metric.infDist y S_unit = ENNReal.toReal (Metric.infEDist y S_unit) := by rfl
    rw [h2]
    exact ENNReal.toReal_le_of_le_ofReal hδ h1
  have h_cp : IsCompact S_unit := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  rcases h_cp.exists_infDist_eq_dist h_ne y with ⟨z, hz, hz_eq⟩
  have h_yz : dist y z ≤ δ := by rw [←hz_eq]; exact hy_dist
  rcases hz with ⟨t, ht, rfl⟩
  have h_hom_eq : ∀ (x : Point3), h_hom x = (2 : ℝ) • (x - m) + m := by
    intro x; simpa [vadd_eq_add, vsub_eq_sub] using AffineMap.homothety_apply m (2 : ℝ) x
  have h_z'_form : h_hom (T.base + t • T.direction) =
      T.base + ((2 : ℝ) * t - 1 / 2) • T.direction := by
    rw [h_hom_eq]
    have h2 : (T.base + t • T.direction) - m = (t - 1 / 2 : ℝ) • T.direction := by
      have hm : m = T.base + (1 / 2 : ℝ) • T.direction := by rfl
      rw [hm]; simp [sub_smul] <;> abel
    rw [h2, smul_smul]
    have h6 : (2 : ℝ) * (t - 1 / 2) = (2 : ℝ) * t - 1 := by ring
    rw [h6]
    have hm : m = T.base + (1 / 2 : ℝ) • T.direction := by rfl
    rw [hm]
    have h7 : ((2 : ℝ) * t - 1) • T.direction + (T.base + (1 / 2 : ℝ) • T.direction) =
        T.base + (((2 : ℝ) * t - 1 + 1 / 2) • T.direction) := by
      rw [add_comm, add_assoc, ←add_smul] <;> abel
    rw [h7]
    have h8 : (2 : ℝ) * t - 1 + 1 / 2 = (2 : ℝ) * t - 1 / 2 := by ring
    rw [h8]
  have h_z'_in : h_hom (T.base + t • T.direction) ∈ S_ext := by
    rw [h_z'_form]
    refine ⟨(2 : ℝ) * t - 1 / 2, ?_, rfl⟩
    constructor <;> linarith [ht.1, ht.2]
  have h_hom_dist : dist (h_hom y) (h_hom (T.base + t • T.direction)) = 2 * dist y (T.base + t • T.direction) := by
    have h1 : h_hom y - h_hom (T.base + t • T.direction) = (2 : ℝ) • (y - (T.base + t • T.direction)) := by
      rw [h_hom_eq y, h_hom_eq (T.base + t • T.direction)]
      simp [smul_sub] <;> abel
    calc
      dist (h_hom y) (h_hom (T.base + t • T.direction))
        = ‖h_hom y - h_hom (T.base + t • T.direction)‖ := by rw [dist_eq_norm]
      _ = ‖(2 : ℝ) • (y - (T.base + t • T.direction))‖ := by rw [h1]
      _ = (2 : ℝ) * ‖y - (T.base + t • T.direction)‖ := by rw [norm_smul] <;> norm_num
      _ = 2 * dist y (T.base + t • T.direction) := by rw [dist_eq_norm] <;> ring
  have h_xz' : dist (h_hom y) (h_hom (T.base + t • T.direction)) ≤ 2 * δ := by
    rw [h_hom_dist]; exact mul_le_mul_of_nonneg_left h_yz (by norm_num)
  exact (Metric.infDist_le_dist_of_mem h_z'_in).trans h_xz'

end Kakeya.Assouad

end
