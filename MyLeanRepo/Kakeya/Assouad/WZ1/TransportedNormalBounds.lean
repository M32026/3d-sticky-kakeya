import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import Mathlib.Tactic

/-!
# Normal bounds for the transported normal

Given v = unit normal with incidence |inner d v| ≤ 6*sourceDelta, prove:
- ‖Nv‖ ≤ 1
- ‖Nv‖ ≥ rho
- |n 2| ≤ 1/2
- max(|n 0|, |n 1|) ≥ 1/3
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

private lemma one_third_le_abs_of_three_eighth_le_sq
    {x : ℝ} (h : (3 / 8 : ℝ) ≤ x ^ 2) :
    (1 / 3 : ℝ) ≤ |x| := by
  have habs : 0 ≤ |x| := abs_nonneg x
  have hsquare : (1 / 3 : ℝ) ^ 2 ≤ |x| ^ 2 := by
    rw [sq_abs]
    nlinarith
  nlinarith

/-- Compute coordinates of the transported normal. -/
lemma transported_normal_coords
    {sourceDelta rho : ℝ}
    (anchor : Kakeya.DeltaTube sourceDelta)
    (hrho : 0 < rho)
    (v : Point3)
    (hnorm_v : ‖v‖ = 1) :
    let d := anchor.direction
    let a : ℝ := 100 * rho
    let R := householderToE3 d anchor.direction_unit
    let w : Point3 := R v
    let Nv := wz1AnchoredUnitRescalingNormalLinear anchor rho v
    Nv 0 = a * w 0 ∧ Nv 1 = a * w 1 ∧ Nv 2 = w 2 ∧ ‖w‖ = 1 := by
  let d := anchor.direction
  let a : ℝ := 100 * rho
  let R := householderToE3 d anchor.direction_unit
  let w : Point3 := R v
  let Nv := wz1AnchoredUnitRescalingNormalLinear anchor rho v
  have h_eq : Nv = transverseScaleLin (1 / a) w := by
    simp [Nv, wz1AnchoredUnitRescalingNormalLinear, unitRescalingNormalLinear, w, a]
    <;> rfl
  have hNv0 : Nv 0 = a * w 0 := by
    rw [h_eq, transverseScaleLin_coord0]
    field_simp [hrho.ne'] <;> ring
  have hNv1 : Nv 1 = a * w 1 := by
    rw [h_eq, transverseScaleLin_coord1]
    field_simp [hrho.ne'] <;> ring
  have hNv2 : Nv 2 = w 2 := by
    rw [h_eq]; exact transverseScaleLin_coord2 (1 / a) w
  have h_norm_w : ‖w‖ = 1 := (householderToE3 d anchor.direction_unit).norm_map v ▸ hnorm_v
  exact ⟨hNv0, hNv1, hNv2, h_norm_w⟩

/-- Norm squared of the transported normal. -/
lemma transported_normal_norm_sq
    {sourceDelta rho : ℝ}
    (anchor : Kakeya.DeltaTube sourceDelta)
    (hrho : 0 < rho)
    (v : Point3)
    (hnorm_v : ‖v‖ = 1) :
    let d := anchor.direction
    let a : ℝ := 100 * rho
    let v_par : ℝ := inner ℝ v d
    let Nv := wz1AnchoredUnitRescalingNormalLinear anchor rho v
    ‖Nv‖ ^ 2 = a ^ 2 * (1 - v_par ^ 2) + v_par ^ 2 := by
  dsimp only
  let d := anchor.direction
  let a : ℝ := 100 * rho
  let R := householderToE3 d anchor.direction_unit
  let w : Point3 := R v
  let Nv := wz1AnchoredUnitRescalingNormalLinear anchor rho v
  let v_par : ℝ := inner ℝ v d
  have hR_sym : R e3 = d := householderToE3_sends_e3_to_d d anchor.direction_unit
  have h_w2 : w 2 = v_par := by
    have h_coord2 : w 2 = inner ℝ w e3 := by
      have h := EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ) w
      simpa [e3] using h.symm
    rw [h_coord2]
    have h_sym : inner ℝ w e3 = inner ℝ v (R e3) :=
      householderToE3_symmetric d anchor.direction_unit v e3
    rw [h_sym, hR_sym] <;> rfl
  have h_coords := transported_normal_coords anchor hrho v hnorm_v
  rcases h_coords with ⟨hNv0, hNv1, hNv2, h_norm_w⟩
  have h_w01 : w 0 ^ 2 + w 1 ^ 2 = 1 - v_par ^ 2 := by
    have h_sum : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1 := by
      have h' : ‖w‖ ^ 2 = ∑ i : Fin 3, (w i) ^ 2 := EuclideanSpace.real_norm_sq_eq w
      have h_sum3 : ∑ i : Fin 3, (w i) ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
        simp [Fin.sum_univ_succ] <;> ring
      have h_norm_sq : ‖w‖ ^ 2 = 1 := by rw [h_norm_w] <;> norm_num
      rw [h', h_sum3] at h_norm_sq; exact h_norm_sq
    rw [h_w2] at h_sum; linarith
  have h_norm2 : ‖Nv‖ ^ 2 = (Nv 0) ^ 2 + (Nv 1) ^ 2 + (Nv 2) ^ 2 := by
    have h : ‖Nv‖ ^ 2 = ∑ i : Fin 3, (Nv i) ^ 2 := EuclideanSpace.real_norm_sq_eq Nv
    have h_sum3 : ∑ i : Fin 3, (Nv i) ^ 2 = (Nv 0) ^ 2 + (Nv 1) ^ 2 + (Nv 2) ^ 2 := by
      simp [Fin.sum_univ_succ] <;> ring
    rw [h, h_sum3]
  calc ‖Nv‖ ^ 2
    = (Nv 0) ^ 2 + (Nv 1) ^ 2 + (Nv 2) ^ 2 := h_norm2
    _ = (a * w 0) ^ 2 + (a * w 1) ^ 2 + w 2 ^ 2 := by rw [hNv0, hNv1, hNv2] <;> ring
    _ = a ^ 2 * (w 0 ^ 2 + w 1 ^ 2) + w 2 ^ 2 := by ring
    _ = a ^ 2 * (1 - v_par ^ 2) + v_par ^ 2 := by rw [h_w01, h_w2] <;> ring

/-- Normal bounds for the transported normal. -/
lemma transported_normal_bounds
    {sourceDelta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily sourceDelta}
    (anchor : Kakeya.DeltaTube sourceDelta)
    (hrho : 0 < rho)
    (v : Point3)
    (hnorm_v : ‖v‖ = 1)
    (hincidence : |inner ℝ anchor.direction v| ≤ 6 * sourceDelta)
    (hrho_small : rho ≤ 1 / 200)
    (hsourceDelta_pos : 0 < sourceDelta)
    (hsourceDelta_le_rho : sourceDelta ≤ rho)
    (hsourceDelta_rho_ratio : sourceDelta / rho ≤ 1 / 4) :
    let Nv := wz1AnchoredUnitRescalingNormalLinear anchor rho v
    let n := (1 / ‖Nv‖) • Nv
    ‖Nv‖ ≤ 1 ∧
    rho ≤ ‖Nv‖ ∧
    50 * rho ≤ ‖Nv‖ ∧
    |n 2| ≤ 1 / 2 ∧
    (1 / 3 ≤ |n 0| ∨ 1 / 3 ≤ |n 1|) := by
  dsimp only
  let d := anchor.direction
  let a : ℝ := 100 * rho
  let v_par : ℝ := inner ℝ v d
  let Nv := wz1AnchoredUnitRescalingNormalLinear anchor rho v
  let n := (1 / ‖Nv‖) • Nv
  have hv_par : |v_par| ≤ 6 * sourceDelta := by
    have h_comm : inner ℝ v d = inner ℝ anchor.direction v := real_inner_comm d v
    dsimp only [v_par]; rw [h_comm]; exact hincidence
  have h_vpar2_le : v_par ^ 2 ≤ (6 * sourceDelta) ^ 2 := by
    calc v_par ^ 2 ≤ |v_par| ^ 2 := by rw [sq_abs]
         _ ≤ (6 * sourceDelta) ^ 2 := by gcongr
  have h_vpar_le_one : v_par ^ 2 ≤ 1 := by
    have h9 : |inner ℝ v d| ≤ ‖v‖ * ‖d‖ := abs_real_inner_le_norm v d
    have h10 : ‖d‖ = 1 := anchor.direction_unit
    have h11 : |v_par| ≤ 1 := by
      dsimp only [v_par]; rw [h10, hnorm_v] at h9; simpa using h9
    have h13 : |v_par| ^ 2 ≤ 1 := by
      have h14 : |v_par| ^ 2 ≤ 1 ^ 2 := by gcongr
      simpa using h14
    have h15 : v_par ^ 2 = |v_par| ^ 2 := by
      have h16 : |v_par| ^ 2 = v_par ^ 2 := sq_abs v_par
      exact h16.symm
    rw [h15]; exact h13
  have h1 : ‖Nv‖ ^ 2 = a ^ 2 * (1 - v_par ^ 2) + v_par ^ 2 :=
    transported_normal_norm_sq anchor hrho v hnorm_v
  have ha_pos : 0 < a := by positivity
  -- Upper bound
  have h_upper : ‖Nv‖ ≤ 1 := by
    have h2 : ‖Nv‖ ^ 2 ≤ a ^ 2 + (6 * sourceDelta) ^ 2 := by
      rw [h1]
      have h3 : 0 ≤ 1 - v_par ^ 2 := by linarith
      have h3a : a ^ 2 * (1 - v_par ^ 2) ≤ a ^ 2 := by
        have h3b : 0 ≤ a ^ 2 := by positivity
        nlinarith
      have h3c : v_par ^ 2 ≤ (6 * sourceDelta) ^ 2 := h_vpar2_le
      nlinarith
    have h4 : a ^ 2 + (6 * sourceDelta) ^ 2 ≤ 1 := by
      have h5 : a ≤ 1 / 2 := by dsimp only [a]; linarith
      have h6 : 6 * sourceDelta ≤ 6 * rho := by gcongr
      nlinarith
    have h7 : 0 ≤ ‖Nv‖ := by positivity
    nlinarith
  -- Positivity
  have hNv_pos : 0 < ‖Nv‖ := by
    have h9 : a ^ 2 * (1 - v_par ^ 2) + v_par ^ 2 > 0 := by
      by_cases h10 : v_par ^ 2 = 1
      · rw [h10]; norm_num
      · have h11 : v_par ^ 2 < 1 := lt_of_le_of_ne h_vpar_le_one h10
        have h12 : 0 < 1 - v_par ^ 2 := by linarith
        have h13 : 0 < a ^ 2 := by positivity
        have h14 : 0 < a ^ 2 * (1 - v_par ^ 2) := mul_pos h13 h12
        have h15 : 0 ≤ v_par ^ 2 := by positivity
        linarith
    have h14 : ‖Nv‖ ^ 2 > 0 := by rw [h1]; exact h9
    have h15 : 0 ≤ ‖Nv‖ := by positivity
    nlinarith
  -- Lower bound
  have h_sourceDelta_le_quarter : sourceDelta ≤ rho / 4 := by
    have h : sourceDelta / rho ≤ 1 / 4 := hsourceDelta_rho_ratio
    have h' : sourceDelta ≤ (1 / 4 : ℝ) * rho := by
      calc sourceDelta = (sourceDelta / rho) * rho := by field_simp [hrho.ne'] <;> ring
        _ ≤ (1 / 4 : ℝ) * rho := by gcongr
    linarith
  have h17 : (6 * sourceDelta) ^ 2 ≤ 3 / 4 := by
    have h18 : (6 * sourceDelta) ^ 2 ≤ (6 * (rho / 4)) ^ 2 := by gcongr
    have h19 : (6 * (rho / 4)) ^ 2 ≤ 3 / 4 := by
      have h20 : rho ≤ 1 / 200 := hrho_small
      nlinarith
    linarith
  have h_lower50 : 50 * rho ≤ ‖Nv‖ := by
    have h21 : ‖Nv‖ ^ 2 ≥ (50 * rho) ^ 2 := by
      rw [h1]
      have h22 : a ^ 2 * (1 - v_par ^ 2) + v_par ^ 2 ≥ a ^ 2 * (1 - (6 * sourceDelta) ^ 2) := by
        have h23 : 0 ≤ a ^ 2 := by positivity
        nlinarith [h_vpar2_le]
      have h24 : a ^ 2 * (1 - (6 * sourceDelta) ^ 2) ≥ a ^ 2 * (1 / 4 : ℝ) := by
        have h25 : 1 - (6 * sourceDelta) ^ 2 ≥ 1 / 4 := by linarith [h17]
        gcongr
      have h26 : a ^ 2 * (1 / 4 : ℝ) = (50 * rho) ^ 2 := by dsimp only [a]; ring
      linarith
    have h27 : 0 ≤ ‖Nv‖ := by positivity
    have h28 : 0 ≤ 50 * rho := by positivity
    nlinarith
  have h_lower : rho ≤ ‖Nv‖ := by
    have h29 : 0 ≤ rho := by linarith
    linarith [h_lower50]
  -- n2 bound
  have h_coords := transported_normal_coords anchor hrho v hnorm_v
  rcases h_coords with ⟨hNv0, hNv1, hNv2, h_norm_w⟩
  have hR_sym : (householderToE3 d anchor.direction_unit) e3 = d :=
    householderToE3_sends_e3_to_d d anchor.direction_unit
  let R := householderToE3 d anchor.direction_unit
  let w : Point3 := R v
  have h_w2 : w 2 = v_par := by
    have h_coord2 : w 2 = inner ℝ w e3 := by
      have h := EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ) w
      simpa [e3] using h.symm
    rw [h_coord2]
    have h_sym : inner ℝ w e3 = inner ℝ v (R e3) :=
      householderToE3_symmetric d anchor.direction_unit v e3
    rw [h_sym, hR_sym] <;> rfl
  have h_n2 : |n 2| ≤ 1 / 2 := by
    have h29 : n 2 = v_par / ‖Nv‖ := by
      have h30 : n 2 = (1 / ‖Nv‖) * (Nv 2) := by
        exact Pi.smul_apply (1 / ‖Nv‖) Nv 2
      rw [h30, hNv2, h_w2]
      <;> field_simp [hNv_pos.ne'] <;> ring
    rw [h29]
    have h31 : |v_par / ‖Nv‖| = |v_par| / ‖Nv‖ := by
      rw [abs_div, abs_of_nonneg (show 0 ≤ ‖Nv‖ from by positivity)]
    rw [h31]
    have h32 : |v_par| / ‖Nv‖ ≤ (6 * sourceDelta) / (50 * rho) := by
      calc |v_par| / ‖Nv‖ ≤ (6 * sourceDelta) / ‖Nv‖ := by gcongr
        _ ≤ (6 * sourceDelta) / (50 * rho) := by gcongr
    have h33 : (6 * sourceDelta) / (50 * rho) ≤ 1 / 2 := by
      have h34 : sourceDelta / rho ≤ 1 / 4 := hsourceDelta_rho_ratio
      have h35 : (6 * sourceDelta) / (50 * rho) = (3 / 25 : ℝ) * (sourceDelta / rho) := by
        field_simp [hrho.ne'] <;> ring
      rw [h35]
      have h36 : (3 / 25 : ℝ) * (sourceDelta / rho) ≤ (3 / 25 : ℝ) * (1 / 4 : ℝ) := by gcongr
      linarith
    exact h32.trans h33
  -- max(|n0|, |n1|) ≥ 1/3
  have h_norm_n : ‖n‖ = 1 := by
    have h : n = (1 / ‖Nv‖) • Nv := by rfl
    rw [h, norm_smul]
    have h_pos2 : 0 < 1 / ‖Nv‖ := by positivity
    have h_abs : ‖(1 / ‖Nv‖ : ℝ)‖ = 1 / ‖Nv‖ := by
      rw [Real.norm_eq_abs, abs_of_pos h_pos2]
    rw [h_abs] <;> field_simp [hNv_pos.ne'] <;> ring
  have h36 : (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 = 1 := by
    have h37 : ‖n‖ ^ 2 = ∑ i : Fin 3, (n i) ^ 2 := EuclideanSpace.real_norm_sq_eq n
    have h38 : ∑ i : Fin 3, (n i) ^ 2 = (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 := by
      simp [Fin.sum_univ_succ] <;> ring
    have h39 : ‖n‖ ^ 2 = (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 := by rw [h37, h38]
    have h40 : ‖n‖ ^ 2 = 1 := by rw [h_norm_n] <;> norm_num
    linarith [h39, h40]
  have h41 : (n 0) ^ 2 + (n 1) ^ 2 ≥ 3 / 4 := by
    have h42 : (n 2) ^ 2 ≤ 1 / 4 := by
      have h43 : |n 2| ≤ 1 / 2 := h_n2
      have h44 : (n 2) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        calc (n 2) ^ 2 ≤ |n 2| ^ 2 := by rw [sq_abs]
             _ ≤ (1 / 2 : ℝ) ^ 2 := by gcongr
      linarith
    linarith [h36]
  have h45 : (n 0) ^ 2 ≥ 3 / 8 ∨ (n 1) ^ 2 ≥ 3 / 8 := by
    by_contra h
    have h_not : (n 0) ^ 2 < 3 / 8 ∧ (n 1) ^ 2 < 3 / 8 := by
      simpa [not_or] using h
    have h46 : (n 0) ^ 2 < 3 / 8 := h_not.1
    have h47 : (n 1) ^ 2 < 3 / 8 := h_not.2
    linarith [h41]
  rcases h45 with (h45 | h45)
  · have h48 : 1 / 3 ≤ |n 0| :=
      one_third_le_abs_of_three_eighth_le_sq h45
    exact ⟨h_upper, h_lower, h_lower50, h_n2, Or.inl h48⟩
  · have h48 : 1 / 3 ≤ |n 1| :=
      one_third_le_abs_of_three_eighth_le_sq h45
    exact ⟨h_upper, h_lower, h_lower50, h_n2, Or.inr h48⟩

end Kakeya.Assouad
