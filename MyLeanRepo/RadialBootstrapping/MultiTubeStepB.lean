module

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.TxDeltaSet
public import MyLeanRepo.RadialBootstrapping.TubeFamilies
public import MyLeanRepo.RadialBootstrapping.FullMetricOverlap
public import MyLeanRepo.RadialBootstrapping.AbsoluteCountBound

@[expose] public section

/-!
# Multi-Tube Step B Geometric Helpers

Provides geometric lemmas needed for the multi-tube Step B construction:

1. `tube_ball_to_tube_general` — tube-to-tube containment without `r ≤ ρ`
2. `point_mem_tube_via_nearby_line` — bound point-to-line distance via nearby line
3. `grid_family_absolute_count_conditional` — count bound with conditional upper bound

Whiteprint node: non-concentrated-case/multi-tube-step-b
-/

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal

noncomputable section

namespace RadialBootstrapping

/-! ==========================================================================
   1. Generalized tube-to-tube containment

   If dist(L₁, L₂) ≤ ρ and r ≤ 1, then
   tube(r, L₂) ∩ B(0,1) ⊆ tube(r + 5ρ, L₁).
   Uses R=3 in line_ball_to_tube_general, valid when r ≤ 1.
   ========================================================================== -/

/-- Generalized tube-to-tube containment: if dist(L₁, L₂) ≤ ρ and r ≤ 1, then
    tube(r, L₂) ∩ B(0,1) ⊆ tube(r + 5ρ, L₁). -/
lemma tube_2r_ball_to_tube (L₁ L₂ : Line2) (r ρ : ℝ)
    (hr : 0 < r) (hr2 : 2 * r ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h : dist L₁ L₂ ≤ ρ) :
    tube (2 * r) L₂ ∩ Metric.closedBall (0 : Point) 1 ⊆ tube (2 * r + 4 * ρ) L₁ := by
  intro y hy
  have hy_tube : y ∈ tube (2 * r) L₂ := hy.1
  have hynorm : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hy.2
  rcases (Metric.mem_thickening_iff).mp hy_tube with ⟨z, hzL2, hdist_yz⟩
  have hz_norm : ‖z‖ ≤ 2 := by
    have h1 : ‖z‖ ≤ ‖y‖ + ‖z - y‖ := by
      calc ‖z‖ = ‖y + (z - y)‖ := by rw [add_sub_cancel]
        _ ≤ ‖y‖ + ‖z - y‖ := norm_add_le _ _
    have h2 : ‖z - y‖ = dist z y := by simp [dist_eq_norm]
    rw [h2] at h1
    have h3 : dist z y = dist y z := dist_comm z y
    rw [h3] at h1
    have h4 : dist y z < 2 * r := hdist_yz
    have h5 : ‖z‖ ≤ ‖y‖ + dist y z := by exact_mod_cast h1
    have h6 : ‖y‖ + dist y z ≤ 1 + 2 * r := by linarith [hynorm]
    have h7 : 1 + 2 * r ≤ 2 := by linarith
    linarith
  have hz_in : z ∈ Line2.toSet L₂ ∩ Metric.closedBall (0 : Point) 2 :=
    ⟨hzL2, by simpa [Metric.mem_closedBall] using hz_norm⟩
  have hz_tube : z ∈ tube (4 * ρ) L₁ := by
    have h_general := line_ball_to_tube_general L₁ L₂ ρ 2 hρ (by norm_num) h hz_in
    have h_eq : (2 + 2) * ρ = 4 * ρ := by ring
    rw [h_eq] at h_general; exact h_general
  rcases (Metric.mem_thickening_iff).mp hz_tube with ⟨w, hwL1, hdist_zw⟩
  have hdist_yw : dist y w < 2 * r + 4 * ρ := by
    have h1 : dist y w ≤ dist y z + dist z w := dist_triangle y z w
    linarith [hdist_yz, hdist_zw, h1]
  simp only [tube, Metric.mem_thickening_iff]
  exact ⟨w, hwL1, hdist_yw⟩

/-! ==========================================================================
   2. Point-to-tube membership via nearby line

   If x ∈ tube(2r, L') and dist(L, L') ≤ ρ, then x ∈ tube(2r + 5ρ, L).
   For r ≤ ρ, this gives x ∈ tube(7ρ, L).
   ========================================================================== -/

/-- If x is in the 2r-tube of L' and L is within ρ of L' (in lineDist),
    then x is in the (2r+5ρ)-tube of L. -/
lemma grid_family_absolute_count_gen_conditional
    (r σ κ : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hr2 : 2 * r ≤ 1) (hσ : 0 ≤ σ)
    (hκ : 0 < κ) (hκ_lt_one : κ < 1)
    (hr_small : 4 * r^(1 - κ) ≤ 1)
    (x : Point) (hxBall : x ∈ Metric.closedBall (0 : Point) 1)
    (S_x : Finset Line2) (hS_sub : S_x ⊆ tubeFamily r)
    (hS_in_2r_tube : ∀ L ∈ S_x, x ∈ tube (2 * r) L)
    (Y_x : Set Point) (hY_meas : MeasurableSet Y_x)
    (hY_sub : Y_x ⊆ Metric.closedBall (0 : Point) 1)
    (ν : Measure Point) [IsProbabilityMeasure ν]
    (A : Line2 → Set Point)
    (hA_meas : ∀ L' ∈ S_x, MeasurableSet (A L'))
    (hA_sub : ∀ L' ∈ S_x, A L' ⊆ tube (2 * r) L')
    (hA_Y : ∀ L' ∈ S_x, A L' ⊆ Y_x)
    (h_nonconc : ∀ L' ∈ S_x,
        ν (A L' ∩ Metric.ball x (Real.rpow r κ)) ≤
          (1 / 3 : ENNReal) * ν (A L'))
    (K m : ℝ) (hK : 0 ≤ K) (hm : 0 < m)
    (h_mass_upper_cond : ∀ (L : Line2) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 →
      (S_x.filter (fun L' => L' ∈ Metric.ball L ρ)).Nonempty →
        ν (tube (2 * r + 4 * ρ) L ∩ Y_x) ≤ ENNReal.ofReal (K * Real.rpow ρ σ))
    (h_mass_lower : ∀ L' ∈ S_x, ν (A L') ≥ ENNReal.ofReal m)
    (L : Line2) (ρ : ℝ) (hρ : r ≤ ρ) (hρ1 : ρ ≤ 1) :
    (S_x.filter (fun L' => L' ∈ Metric.ball L ρ)).card ≤
      ((30000 / Real.rpow r κ) * K / m) * Real.rpow ρ σ := by
  let S_ball : Finset Line2 := S_x.filter (fun L' => L' ∈ Metric.ball L ρ)
  by_cases h_empty : S_ball = ∅
  · have h_card : S_ball.card = 0 := by rw [h_empty]; simp
    have h1 : 0 < Real.rpow r κ := Real.rpow_pos_of_pos hr κ
    have h2 : 0 ≤ Real.rpow ρ σ := Real.rpow_nonneg (by linarith) _
    have h_rhs_nonneg : 0 ≤ ((30000 / Real.rpow r κ) * K / m) * Real.rpow ρ σ := by
      have h3 : 0 ≤ 30000 / Real.rpow r κ := by positivity
      positivity
    have h_goal : (S_ball.card : ℝ) ≤ ((30000 / Real.rpow r κ) * K / m) * Real.rpow ρ σ := by
      rw [h_card]; simpa using h_rhs_nonneg
    exact_mod_cast h_goal
  · have h_nonempty : S_ball.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    have h_upper : ν (tube (2 * r + 4 * ρ) L ∩ Y_x) ≤
        ENNReal.ofReal (K * Real.rpow ρ σ) :=
      h_mass_upper_cond L ρ hρ hρ1 h_nonempty
    let ov : ℝ := 30000 / Real.rpow r κ
    have h_rpow_kappa_pos : 0 < Real.rpow r κ := Real.rpow_pos_of_pos hr κ
    have hov_nonneg : 0 ≤ ov := by
      dsimp only [ov]; exact div_nonneg (by norm_num) h_rpow_kappa_pos.le
    let S_gen : Finset Line2 := S_x.filter (fun L' => A L' ⊆ tube (2 * r + 4 * ρ) L)
    have h_ball_sub_gen : S_ball ⊆ S_gen := by
      intro L' hL'
      have h1 : L' ∈ S_x := (Finset.mem_filter.mp hL').1
      have h2 : L' ∈ Metric.ball L ρ := (Finset.mem_filter.mp hL').2
      have h3 : dist L' L < ρ := Metric.mem_ball.mp h2
      have h3' : dist L L' < ρ := by rwa [dist_comm] at h3
      have h4 : dist L L' ≤ ρ := by linarith
      have hρ_pos : 0 < ρ := by linarith
      have h5 : A L' ⊆ tube (2 * r + 4 * ρ) L := by
        have h6 : A L' ⊆ tube (2 * r) L' := hA_sub L' h1
        have h7 : tube (2 * r) L' ∩ Metric.closedBall (0 : Point) 1 ⊆
            tube (2 * r + 4 * ρ) L :=
          tube_2r_ball_to_tube L L' r ρ hr hr2 hρ_pos hρ1 h4
        have h8 : A L' ⊆ Metric.closedBall (0 : Point) 1 := by
          exact hA_Y L' h1 |>.trans hY_sub
        have h9 : A L' ⊆ tube (2 * r) L' ∩ Metric.closedBall (0 : Point) 1 := by
          exact subset_inter h6 h8
        exact h9.trans h7
      exact Finset.mem_filter.mpr ⟨h1, h5⟩
    have h_overlap : ∑ L' ∈ S_gen, ν (A L') ≤
        ENNReal.ofReal ov * ν (tube (2 * r + 4 * ρ) L ∩ Y_x) :=
      grid_family_overlap_bound_gen r κ hr hκ hκ_lt_one hr_small x hxBall
        S_x hS_sub hS_in_2r_tube Y_x hY_meas hY_sub ν A hA_meas hA_sub hA_Y h_nonconc
        L ρ hρ hρ1
    have h_leq : ∀ L' ∈ S_gen, ENNReal.ofReal m ≤ ν (A L') := by
      intro L' hL'
      have h_in_Sx : L' ∈ S_x := (Finset.mem_filter.mp hL').1
      exact h_mass_lower L' h_in_Sx
    have h_sum_ge : (S_gen.card : ENNReal) * ENNReal.ofReal m ≤
        ∑ L' ∈ S_gen, ν (A L') := by
      calc
        (S_gen.card : ENNReal) * ENNReal.ofReal m
          = ∑ L' ∈ S_gen, ENNReal.ofReal m := by simp [Finset.sum_const] <;> ring
        _ ≤ ∑ L' ∈ S_gen, ν (A L') := Finset.sum_le_sum h_leq
    have h_sum_le : ∑ L' ∈ S_gen, ν (A L') ≤
        ENNReal.ofReal ov * ν (tube (2 * r + 4 * ρ) L ∩ Y_x) := h_overlap
    have h_main : (S_gen.card : ENNReal) * ENNReal.ofReal m ≤
        ENNReal.ofReal (ov * K * Real.rpow ρ σ) := by
      calc
        (S_gen.card : ENNReal) * ENNReal.ofReal m
          ≤ ∑ L' ∈ S_gen, ν (A L') := h_sum_ge
        _ ≤ ENNReal.ofReal ov * ν (tube (2 * r + 4 * ρ) L ∩ Y_x) := h_sum_le
        _ ≤ ENNReal.ofReal ov * ENNReal.ofReal (K * Real.rpow ρ σ) := by gcongr
        _ = ENNReal.ofReal (ov * (K * Real.rpow ρ σ)) := by
          rw [ENNReal.ofReal_mul hov_nonneg]
        _ = ENNReal.ofReal (ov * K * Real.rpow ρ σ) := by congr 1; ring
    have h_pos2 : 0 ≤ ov * K * Real.rpow ρ σ := by
      have h3 : 0 ≤ Real.rpow ρ σ := Real.rpow_nonneg (by linarith) _
      positivity
    have h_iff : (S_gen.card : ENNReal) * ENNReal.ofReal m ≤
        ENNReal.ofReal (ov * K * Real.rpow ρ σ) ↔
        (S_gen.card : ℝ) * m ≤ ov * K * Real.rpow ρ σ := by
      have h2 : (S_gen.card : ENNReal) * ENNReal.ofReal m =
          ENNReal.ofReal ((S_gen.card : ℝ) * m) := by
        have h_nat : (S_gen.card : ENNReal) = ENNReal.ofReal (S_gen.card : ℝ) := by simp
        rw [h_nat]
        rw [ENNReal.ofReal_mul (show 0 ≤ (S_gen.card : ℝ) from by positivity)]
        <;> ring
      rw [h2]
      exact ENNReal.ofReal_le_ofReal_iff h_pos2
    have h9 : (S_gen.card : ℝ) * m ≤ ov * K * Real.rpow ρ σ := h_iff.mp h_main
    have h10 : 0 < m := hm
    have h_eq : ((S_gen.card : ℝ) * m) / m = (S_gen.card : ℝ) := by
      have h_comm : (S_gen.card : ℝ) * m = m * (S_gen.card : ℝ) := by ring
      rw [h_comm]
      exact mul_div_cancel_left₀ (S_gen.card : ℝ) h10.ne'
    have h_div_le : ((S_gen.card : ℝ) * m) / m ≤ (ov * K * Real.rpow ρ σ) / m :=
      div_le_div_of_nonneg_right h9 (by linarith)
    have h11 : (S_gen.card : ℝ) ≤ (ov * K * Real.rpow ρ σ) / m := by
      rw [h_eq] at h_div_le
      exact h_div_le
    have h_count_gen : (S_gen.card : ℝ) ≤ (ov * K / m) * Real.rpow ρ σ := by
      have h12 : (ov * K * Real.rpow ρ σ) / m = (ov * K / m) * Real.rpow ρ σ := by ring
      rw [h12] at h11
      exact h11
    have h6 : S_ball.card ≤ S_gen.card := Finset.card_le_card h_ball_sub_gen
    have h7 : (S_ball.card : ℝ) ≤ (S_gen.card : ℝ) := by exact_mod_cast h6
    exact le_trans h7 h_count_gen

end RadialBootstrapping

end
