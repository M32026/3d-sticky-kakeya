import MyLeanRepo.Kakeya.Assouad.WZ1.NeighborPackingBound
import Mathlib.Tactic

/-!
# Grid cell partition for WZ1 balanced cover

A uniform grid partition of ℝ³ into cubes of side `s = 2*rho/√3`,
so each cube has diameter at most `2*rho`.

This module provides the grid side length, the grid index function,
and the key diameter and neighbor-count properties used by the
balanced cover's cell structure.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The side length of a grid cube: `2*rho/√3`, chosen so the cube diameter is `2*rho`. -/
def gridSide (rho : ℝ) : ℝ := 2 * rho / Real.sqrt 3

/--
The grid index of a point at scale `rho`.

Two points with the same grid index lie in the same open-closed cube
of side `gridSide rho`.
-/
def rhoGridIndex (rho : ℝ) (p : Point3) : ℤ × ℤ × ℤ :=
  gridIndex (gridSide rho) p

/--
If two points have the same grid index, their distance is at most `2*rho`.

Proof: each coordinate differs by strictly less than `gridSide rho`,
so the Euclidean distance is strictly less than `√3 * gridSide rho = 2*rho`.
-/
lemma grid_cell_diameter {rho : ℝ} (hrho : 0 < rho)
    {p q : Point3} (h : rhoGridIndex rho p = rhoGridIndex rho q) :
    dist p q ≤ 2 * rho := by
  set s : ℝ := gridSide rho with hs
  have hs_pos : 0 < s := by
    rw [hs]
    simp only [gridSide]
    positivity
  have h0 : ⌊(p 0) / s⌋ = ⌊(q 0) / s⌋ := by
    simpa [rhoGridIndex, gridIndex] using congr_arg Prod.fst h
  have h1 : ⌊(p 1) / s⌋ = ⌊(q 1) / s⌋ := by
    simpa [rhoGridIndex, gridIndex] using congr_arg (fun x : ℤ × ℤ × ℤ => x.2.1) h
  have h2 : ⌊(p 2) / s⌋ = ⌊(q 2) / s⌋ := by
    simpa [rhoGridIndex, gridIndex] using congr_arg (fun x : ℤ × ℤ × ℤ => x.2.2) h
  have h_coord : ∀ (k : Fin 3), |p k - q k| < s := by
    intro k
    have h_floor : ⌊(p k) / s⌋ = ⌊(q k) / s⌋ := by
      fin_cases k <;> tauto
    have h5 : (p k) / s - (q k) / s < 1 := by
      have h6 : (p k) / s < (⌊(p k) / s⌋ : ℝ) + 1 := Int.lt_floor_add_one ((p k) / s)
      have h7 : (⌊(q k) / s⌋ : ℝ) ≤ (q k) / s := Int.floor_le ((q k) / s)
      rw [h_floor] at h6
      linarith
    have h8 : (q k) / s - (p k) / s < 1 := by
      have h9 : (q k) / s < (⌊(q k) / s⌋ : ℝ) + 1 := Int.lt_floor_add_one ((q k) / s)
      have h10 : (⌊(p k) / s⌋ : ℝ) ≤ (p k) / s := Int.floor_le ((p k) / s)
      rw [←h_floor] at h9
      linarith
    have h9 : |(p k) / s - (q k) / s| < 1 := by
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have h10 : |(p k - q k) / s| < 1 := by
      have h11 : (p k - q k) / s = (p k) / s - (q k) / s := by rw [sub_div]
      rw [h11]
      exact h9
    have h12 : |p k - q k| / s < 1 := by
      have h13 : |(p k - q k) / s| = |p k - q k| / s := by
        rw [abs_div, abs_of_pos hs_pos]
      rw [h13] at h10
      exact h10
    have h14 : |p k - q k| < s := by
      calc
        |p k - q k| = |p k - q k| / s * s := by
          field_simp [hs_pos.ne'] <;> ring
        _ < 1 * s := by gcongr
        _ = s := by ring
    exact h14
  have h_dist_sq : dist p q ^ 2 < 3 * s ^ 2 := by
    have h15 : dist p q ^ 2 = ∑ k : Fin 3, (p k - q k) ^ 2 := by
      have h_dist : dist p q = ‖p - q‖ := by rw [dist_eq_norm]
      rw [h_dist]
      rw [PiLp.norm_eq_of_L2]
      have h_nonneg : 0 ≤ ∑ i : Fin 3, ‖(p - q) i‖ ^ 2 := by positivity
      rw [Real.sq_sqrt h_nonneg]
      apply Finset.sum_congr rfl
      intro i _
      simp [Real.norm_eq_abs, sq_abs]
    rw [h15]
    have h16 : ∑ k : Fin 3, (p k - q k) ^ 2 < 3 * s ^ 2 := by
      have h_sq : ∀ (k : Fin 3), (p k - q k) ^ 2 < s ^ 2 := by
        intro k
        have h18 : |p k - q k| < s := h_coord k
        have h19 : (p k - q k) ^ 2 = |p k - q k| ^ 2 := by rw [sq_abs]
        rw [h19]
        have h20 : |p k - q k| ^ 2 < s ^ 2 := by gcongr
        exact h20
      have h170 := h_sq 0
      have h171 := h_sq 1
      have h172 := h_sq 2
      have h_sum : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2 < 3 * s ^ 2 := by linarith
      have h_eq : ∑ k : Fin 3, (p k - q k) ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2 := by
        simp [Fin.sum_univ_succ] <;> ring
      rw [h_eq]
      exact h_sum
    exact h16
  have h20 : 3 * s ^ 2 = (2 * rho) ^ 2 := by
    rw [hs]
    simp only [gridSide]
    have h21 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    field_simp [h21.ne'] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  rw [h20] at h_dist_sq
  have h22 : dist p q < 2 * rho := by
    have h_nonneg : 0 ≤ dist p q := dist_nonneg
    nlinarith [h_nonneg, hrho]
  exact h22.le

/--
If two representatives are within `6*rho`, their grid indices differ
by at most 6 in each coordinate.
-/
lemma grid_neighbor_count {rho : ℝ} (hrho : 0 < rho)
    {p q : Point3} (h : dist p q ≤ 6 * rho) :
    let ip := rhoGridIndex rho p
    let iq := rhoGridIndex rho q
    |ip.1 - iq.1| ≤ (6 : ℤ) ∧
    |ip.2.1 - iq.2.1| ≤ (6 : ℤ) ∧
    |ip.2.2 - iq.2.2| ≤ (6 : ℤ) := by
  set s : ℝ := gridSide rho with hs
  have hs_pos : 0 < s := by
    rw [hs]
    simp only [gridSide]
    positivity
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h_ratio : 6 * rho / s = 3 * Real.sqrt 3 := by
    rw [hs]
    simp only [gridSide]
    field_simp [hsqrt3_pos.ne'] <;> ring
  have h3sqrt3_lt_6 : 3 * Real.sqrt 3 < 6 := by
    have h : Real.sqrt 3 < 2 := Real.sqrt_lt' (by norm_num) |>.mpr (by norm_num)
    linarith
  have h_coord : ∀ (k : Fin 3), |(p k / s) - (q k / s)| < 6 := by
    intro k
    have h1 : |p k - q k| ≤ dist p q := PiLp.dist_apply_le p q k
    have h2 : |p k - q k| ≤ 6 * rho := h1.trans h
    have h3 : |(p k - q k) / s| ≤ 6 * rho / s := by
      calc
        |(p k - q k) / s|
          = |p k - q k| / s := by rw [abs_div, abs_of_pos hs_pos]
        _ ≤ (6 * rho) / s := by gcongr
        _ = 6 * rho / s := by ring
    have h4 : (p k / s) - (q k / s) = (p k - q k) / s := by rw [sub_div]
    rw [h4]
    rw [h_ratio] at h3
    exact h3.trans_lt h3sqrt3_lt_6
  have hf0 := wz1_abs_floor_sub_lt_le (N := 6) (by norm_num) (h_coord 0)
  have hf1 := wz1_abs_floor_sub_lt_le (N := 6) (by norm_num) (h_coord 1)
  have hf2 := wz1_abs_floor_sub_lt_le (N := 6) (by norm_num) (h_coord 2)
  exact ⟨hf0, hf1, hf2⟩

end Kakeya.Assouad
