import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Geometric helper lemmas for Point3

Shared utility lemmas used across the hairbrush balanced broad decomposition.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Given a unit vector `v` in `Point3`, find a unit vector `n` perpendicular to `v`. -/
lemma exists_perp_unit (v : Point3) (hv : ‖v‖ = 1) :
    ∃ (n : Point3), ‖n‖ = 1 ∧ inner ℝ v n = 0 := by
  let e0 : Point3 := EuclideanSpace.single 0 (1 : ℝ)
  -- w = (-v 1, v 0, 0), always perpendicular to v
  let w : Point3 := EuclideanSpace.single 0 (-(v 1)) + EuclideanSpace.single 1 (v 0)
  have h_perp : inner ℝ v w = 0 := by
    simp [w, e0, PiLp.inner_apply, EuclideanSpace.single_apply, Fin.sum_univ_succ]
    <;> ring
  by_cases h : w = 0
  · -- w = 0 means v 0 = 0 and v 1 = 0, so v = (0,0,±1); e0 is perpendicular
    have h_w0 : w 0 = 0 := by rw [h] <;> simp
    have h_w1 : w 1 = 0 := by rw [h] <;> simp
    have h0 : v 0 = 0 := by
      simpa [w, EuclideanSpace.single_apply] using h_w1
    have h1 : v 1 = 0 := by
      simpa [w, EuclideanSpace.single_apply] using h_w0
    have hn1 : ‖e0‖ = 1 := by simp [e0, EuclideanSpace.norm_eq] <;> norm_num
    have hn2 : inner ℝ v e0 = 0 := by
      simp [e0, PiLp.inner_apply, Fin.sum_univ_succ, h0, h1] <;> norm_num
    exact ⟨e0, hn1, hn2⟩
  · -- w ≠ 0, normalize it
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr h
    let n : Point3 := (‖w‖⁻¹ : ℝ) • w
    have hn1 : ‖n‖ = 1 := by
      have h : ‖n‖ = |(‖w‖⁻¹ : ℝ)| * ‖w‖ := norm_smul _ _
      rw [h]
      have hpos : 0 < ‖w‖ := hwn
      have habs : |(‖w‖⁻¹ : ℝ)| = ‖w‖⁻¹ := by
        rw [abs_of_pos] <;> positivity
      rw [habs]
      field_simp [hpos.ne'] <;> norm_num
    have hn2 : inner ℝ v n = 0 := by
      rw [inner_smul_right, h_perp] <;> ring
    exact ⟨n, hn1, hn2⟩

/-- Acute angle of a vector with itself is zero. -/
lemma acute_angle_self (v : Point3) (hv : ‖v‖ = 1) :
    hairbrushAcuteDirectionAngle v v = 0 := by
  have h_inner : inner ℝ v v = 1 := by
    have h : inner ℝ v v = ‖v‖ ^ 2 := by
      simpa [inner_self_eq_norm_sq_to_K] using rfl
    rw [h, hv] <;> norm_num
  rw [hairbrushAcuteDirectionAngle, h_inner]
  have h_arccos : Real.arccos 1 = 0 := Real.arccos_one
  rw [h_arccos]
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  exact min_eq_left (by linarith)

end Kakeya.Assouad
