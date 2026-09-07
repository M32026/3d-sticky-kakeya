import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import Mathlib.Tactic

/-!
# Axis line equality implies direction parallelism
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/--
Cross-radius version: axis line equality implies direction parallelism.
Works when source and target tubes have different radius parameters.
-/
lemma target_direction_parallel_to_image_cross
    {delta1 delta2 : ℝ}
    {sourceTube : Kakeya.DeltaTube delta1}
    {targetTube : Kakeya.DeltaTube delta2}
    {L : Point3 →ₗ[ℝ] Point3}
    {b : Point3}
    (h_axis : tubeAxisLine targetTube =
        (fun p => L p + b) '' tubeAxisLine sourceTube) :
    ∃ (c : ℝ), c ≠ 0 ∧ targetTube.direction = c • L sourceTube.direction := by
  have h1 : targetTube.base ∈ tubeAxisLine targetTube := by
    refine ⟨0, by simp⟩
  have h2 : targetTube.base + targetTube.direction ∈ tubeAxisLine targetTube := by
    refine ⟨1, by simp⟩
  rw [h_axis] at h1 h2
  rcases h1 with ⟨p1, hp1, h_eq1⟩
  rcases h2 with ⟨p2, hp2, h_eq2⟩
  have h_eq1b : targetTube.base = L p1 + b := by
    have h : (fun p : Point3 => L p + b) p1 = L p1 + b := by rfl
    rw [h] at h_eq1
    exact h_eq1.symm
  have h_eq2b : targetTube.base + targetTube.direction = L p2 + b := by
    have h : (fun p : Point3 => L p + b) p2 = L p2 + b := by rfl
    rw [h] at h_eq2
    exact h_eq2.symm
  rcases hp1 with ⟨t1, ht1⟩
  rcases hp2 with ⟨t2, ht2⟩
  have h_eq1' : targetTube.base = L sourceTube.base + t1 • L sourceTube.direction + b := by
    have h_p1 : p1 = sourceTube.base + t1 • sourceTube.direction := ht1
    rw [h_p1] at h_eq1b
    have h_L : L (sourceTube.base + t1 • sourceTube.direction) = L sourceTube.base + t1 • L sourceTube.direction := by
      rw [map_add, map_smul]
    rw [h_L] at h_eq1b
    exact h_eq1b
  have h_eq2' : targetTube.base + targetTube.direction = L sourceTube.base + t2 • L sourceTube.direction + b := by
    have h_p2 : p2 = sourceTube.base + t2 • sourceTube.direction := ht2
    rw [h_p2] at h_eq2b
    have h_L : L (sourceTube.base + t2 • sourceTube.direction) = L sourceTube.base + t2 • L sourceTube.direction := by
      rw [map_add, map_smul]
    rw [h_L] at h_eq2b
    exact h_eq2b
  have h_sub : targetTube.direction = (t2 - t1) • L sourceTube.direction := by
    calc targetTube.direction
        = (targetTube.base + targetTube.direction) - targetTube.base := by abel
      _ = (L sourceTube.base + t2 • L sourceTube.direction + b) - (L sourceTube.base + t1 • L sourceTube.direction + b) := by rw [h_eq2', h_eq1']
      _ = (t2 - t1) • L sourceTube.direction := by
        simp [sub_smul] <;> abel
  refine ⟨t2 - t1, ?_, h_sub⟩
  intro hc
  rw [hc] at h_sub
  have h_contra : targetTube.direction = 0 := by simpa using h_sub
  have h_unit : ‖targetTube.direction‖ = 1 := targetTube.direction_unit
  rw [h_contra] at h_unit
  <;> norm_num at h_unit

end Kakeya.Assouad

end
