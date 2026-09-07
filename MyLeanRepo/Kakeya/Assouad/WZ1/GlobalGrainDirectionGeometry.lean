import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Helper lemmas for global grain direction geometry

Norm calculations and bounds for `globalGrainDirection`.
-/

namespace Kakeya.Assouad

open Metric Set

/-- Norm squared of a global grain direction vector. -/
lemma globalGrainDirection_norm_sq (m : ℝ) :
    ‖globalGrainDirection m‖ ^ 2 = 1 + m ^ 2 := by
  have h_eq1 : ‖globalGrainDirection m‖ ^ 2 = ∑ i : Fin 3, (globalGrainDirection m i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq _
  rw [h_eq1]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  <;> simp [globalGrainDirection]

/-- Norm bound for global grain direction with slope in [-3, 3]. -/
lemma globalGrainDirection_norm_le_4 {m : ℝ} (h : |m| ≤ 3) :
    ‖globalGrainDirection m‖ ≤ 4 := by
  have h_m_sq : m ^ 2 ≤ 9 := by
    have h4 : m ^ 2 = |m| ^ 2 := by rw [sq_abs]
    rw [h4]
    have h5 : |m| ^ 2 ≤ 9 := by
      calc |m| ^ 2 ≤ 3 ^ 2 := by gcongr
           _ = 9 := by norm_num
    exact h5
  have h6 : ‖globalGrainDirection m‖ ^ 2 ≤ 16 := by
    rw [globalGrainDirection_norm_sq m]
    have h7 : 1 + m ^ 2 ≤ 16 := by linarith [h_m_sq]
    exact h7
  have h7 : 0 ≤ ‖globalGrainDirection m‖ := by positivity
  by_cases h8 : ‖globalGrainDirection m‖ ≤ 4
  · exact h8
  · have h9 : ‖globalGrainDirection m‖ > 4 := by linarith
    have h10 : ‖globalGrainDirection m‖ ^ 2 > 16 := by nlinarith
    exact False.elim (not_le.mpr h10 h6)

end Kakeya.Assouad
