module

/-
Copyright (c) 2024 The Discretised Furstenberg Estimate Team.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raven Team
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.Core

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate

namespace MultiscaleDecomposition

/-! # Grid covering helpers

This module contains grid-based covering lemmas used in `superlinearToDeltaSSet`:
- `grid_cover_square`: k×k grid of balls covers a dyadic square when k ≥ L√2/(2r)
- `nine_balls_cover_square`: 9 balls cover a dyadic square when r ≥ L√2/6
-/

-- ======================================================================
-- Grid covering helpers for superlinearToDeltaSSet
-- ======================================================================

/-- A k×k grid of balls covers a dyadic square when k ≥ L√2/(2r). -/
lemma grid_cover_square (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (k : ℕ) (hk : (k : ℝ) ≥ L * Real.sqrt 2 / (2 * r)) (a b : ℤ) :
    ∃ (c : Finset EuclideanPlane),
      (dyadicSquare L a b) ⊆ ⋃ x ∈ c, Metric.closedBall x r ∧ c.card ≤ k^2 := by
  by_cases hk0 : k = 0
  · exfalso
    rw [hk0] at hk
    have h' : 0 < L * Real.sqrt 2 / (2 * r) := by positivity
    linarith
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
  let I : Finset ℕ := Finset.range k
  let mkCenter (p : ℕ × ℕ) : EuclideanPlane :=
    WithLp.toLp 2 fun i : Fin 2 =>
      if i = 0 then (a : ℝ) * L + ((p.1 : ℝ) + 1 / 2) * L / (k : ℝ)
      else (b : ℝ) * L + ((p.2 : ℝ) + 1 / 2) * L / (k : ℝ)
  let centers : Finset EuclideanPlane := (I ×ˢ I).image mkCenter
  have h_card : centers.card ≤ k^2 := by
    have h : centers.card ≤ (I ×ˢ I).card := Finset.card_image_le
    have h2 : (I ×ˢ I).card = k * k := by
      simp [I, Finset.card_product] <;> ring
    rw [h2] at h
    have h3 : k * k = k^2 := by ring
    rw [h3] at h
    exact h
  have h_cover : dyadicSquare L a b ⊆ ⋃ x ∈ centers, Metric.closedBall x r := by
    intro p hp
    have h0 : p 0 ∈ Set.Ico ((a : ℝ) * L) (((a : ℝ) + 1) * L) := hp.1
    have h1 : p 1 ∈ Set.Ico ((b : ℝ) * L) (((b : ℝ) + 1) * L) := hp.2
    set dx : ℝ := p 0 - (a : ℝ) * L with hdx_def
    set dy : ℝ := p 1 - (b : ℝ) * L with hdy_def
    have hdx1 : 0 ≤ dx := by linarith [h0.1]
    have hdx2 : dx < L := by linarith [h0.2]
    have hdy1 : 0 ≤ dy := by linarith [h1.1]
    have hdy2 : dy < L := by linarith [h1.2]
    have hdx_nonneg : 0 ≤ dx * (k : ℝ) / L := by positivity
    have hdy_nonneg : 0 ≤ dy * (k : ℝ) / L := by positivity
    let jx : ℕ := Nat.floor (dx * (k : ℝ) / L)
    let jy : ℕ := Nat.floor (dy * (k : ℝ) / L)
    have hjx1 : (jx : ℝ) ≤ dx * (k : ℝ) / L := Nat.floor_le hdx_nonneg
    have hjx2 : dx * (k : ℝ) / L < (jx : ℝ) + 1 := Nat.lt_floor_add_one (dx * (k : ℝ) / L)
    have hjy1 : (jy : ℝ) ≤ dy * (k : ℝ) / L := Nat.floor_le hdy_nonneg
    have hjy2 : dy * (k : ℝ) / L < (jy : ℝ) + 1 := Nat.lt_floor_add_one (dy * (k : ℝ) / L)
    have hjx_lt_k : jx < k := by
      have h1 : (jx : ℝ) ≤ dx * (k : ℝ) / L := hjx1
      have h2 : dx * (k : ℝ) / L < (k : ℝ) := by
        have h3 : dx < L := hdx2
        have h4 : dx * (k : ℝ) / L < (k : ℝ) := by
          calc dx * (k : ℝ) / L
            < L * (k : ℝ) / L := by gcongr
          _ = (k : ℝ) := by field_simp [hL.ne'] <;> ring
        exact h4
      have h5 : (jx : ℝ) < (k : ℝ) := by linarith
      exact_mod_cast h5
    have hjy_lt_k : jy < k := by
      have h1 : (jy : ℝ) ≤ dy * (k : ℝ) / L := hjy1
      have h2 : dy * (k : ℝ) / L < (k : ℝ) := by
        have h3 : dy < L := hdy2
        have h4 : dy * (k : ℝ) / L < (k : ℝ) := by
          calc dy * (k : ℝ) / L
            < L * (k : ℝ) / L := by gcongr
          _ = (k : ℝ) := by field_simp [hL.ne'] <;> ring
        exact h4
      have h5 : (jy : ℝ) < (k : ℝ) := by linarith
      exact_mod_cast h5
    have hjx_in : jx ∈ I := Finset.mem_range.mpr hjx_lt_k
    have hjy_in : jy ∈ I := Finset.mem_range.mpr hjy_lt_k
    set center' : EuclideanPlane := mkCenter (jx, jy) with hcenter'_def
    have hcenter_in : center' ∈ centers := by
      apply Finset.mem_image.mpr
      exact ⟨(jx, jy), Finset.mem_product.mpr ⟨hjx_in, hjy_in⟩, rfl⟩
    have hdx_cx : |dx - (((jx : ℝ) + 1 / 2) * L / (k : ℝ))| ≤ L / (2 * (k : ℝ)) := by
      have h1 : (jx : ℝ) * L / (k : ℝ) ≤ dx := by
        calc (jx : ℝ) * L / (k : ℝ)
          = ((jx : ℝ) * (L / (k : ℝ))) := by ring
        _ ≤ (dx * (k : ℝ) / L) * (L / (k : ℝ)) := by gcongr
        _ = dx := by field_simp [hk_pos.ne'] <;> ring
      have h2 : dx < ((jx : ℝ) + 1) * L / (k : ℝ) := by
        calc dx
          = (dx * (k : ℝ) / L) * (L / (k : ℝ)) := by field_simp [hk_pos.ne'] <;> ring
        _ < (((jx : ℝ) + 1) * (L / (k : ℝ))) := by gcongr
        _ = ((jx : ℝ) + 1) * L / (k : ℝ) := by ring
      set z : ℝ := dx - (((jx : ℝ) + 1 / 2) * L / (k : ℝ)) with hz_def
      have h3 : z ≥ -L / (2 * (k : ℝ)) := by
        have h4 : z = dx - ((jx : ℝ) + 1 / 2) * L / (k : ℝ) := by rfl
        rw [h4]
        have h5 : (jx : ℝ) * L / (k : ℝ) - (((jx : ℝ) + 1 / 2) * L / (k : ℝ)) = -L / (2 * (k : ℝ)) := by ring
        linarith [h1, h5]
      have h6 : z ≤ L / (2 * (k : ℝ)) := by
        have h7 : z = dx - ((jx : ℝ) + 1 / 2) * L / (k : ℝ) := by rfl
        rw [h7]
        have h8 : ((jx : ℝ) + 1) * L / (k : ℝ) - (((jx : ℝ) + 1 / 2) * L / (k : ℝ)) = L / (2 * (k : ℝ)) := by ring
        linarith [h2, h8]
      have h3' : -(L / (2 * (k : ℝ))) ≤ z := by
        simpa [neg_div] using h3
      exact abs_le.mpr ⟨h3', h6⟩
    have hdy_cy : |dy - (((jy : ℝ) + 1 / 2) * L / (k : ℝ))| ≤ L / (2 * (k : ℝ)) := by
      have h1 : (jy : ℝ) * L / (k : ℝ) ≤ dy := by
        calc (jy : ℝ) * L / (k : ℝ)
          = ((jy : ℝ) * (L / (k : ℝ))) := by ring
        _ ≤ (dy * (k : ℝ) / L) * (L / (k : ℝ)) := by gcongr
        _ = dy := by field_simp [hk_pos.ne'] <;> ring
      have h2 : dy < ((jy : ℝ) + 1) * L / (k : ℝ) := by
        calc dy
          = (dy * (k : ℝ) / L) * (L / (k : ℝ)) := by field_simp [hk_pos.ne'] <;> ring
        _ < (((jy : ℝ) + 1) * (L / (k : ℝ))) := by gcongr
        _ = ((jy : ℝ) + 1) * L / (k : ℝ) := by ring
      set z : ℝ := dy - (((jy : ℝ) + 1 / 2) * L / (k : ℝ)) with hz_def
      have h3 : z ≥ -L / (2 * (k : ℝ)) := by
        have h4 : z = dy - ((jy : ℝ) + 1 / 2) * L / (k : ℝ) := by rfl
        rw [h4]
        have h5 : (jy : ℝ) * L / (k : ℝ) - (((jy : ℝ) + 1 / 2) * L / (k : ℝ)) = -L / (2 * (k : ℝ)) := by ring
        linarith [h1, h5]
      have h6 : z ≤ L / (2 * (k : ℝ)) := by
        have h7 : z = dy - ((jy : ℝ) + 1 / 2) * L / (k : ℝ) := by rfl
        rw [h7]
        have h8 : ((jy : ℝ) + 1) * L / (k : ℝ) - (((jy : ℝ) + 1 / 2) * L / (k : ℝ)) = L / (2 * (k : ℝ)) := by ring
        linarith [h2, h8]
      have h3' : -(L / (2 * (k : ℝ))) ≤ z := by
        simpa [neg_div] using h3
      exact abs_le.mpr ⟨h3', h6⟩
    set y : EuclideanPlane := p - center' with hy_def
    have hy0 : y 0 = dx - (((jx : ℝ) + 1 / 2) * L / (k : ℝ)) := by
      simp [hy_def, hcenter'_def, mkCenter, hdx_def] <;> ring
    have hy1 : y 1 = dy - (((jy : ℝ) + 1 / 2) * L / (k : ℝ)) := by
      simp [hy_def, hcenter'_def, mkCenter, hdy_def] <;> ring
    have h4 : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
      have h5 : ‖y‖ ^ 2 = ∑ i : Fin 2, (y i) ^ 2 := EuclideanSpace.real_norm_sq_eq y
      rw [h5] <;> simp [Fin.sum_univ_two] <;> ring
    have h61 : |y 0| ≤ L / (2 * (k : ℝ)) := by rw [hy0] <;> exact hdx_cx
    have h62 : |y 1| ≤ L / (2 * (k : ℝ)) := by rw [hy1] <;> exact hdy_cy
    have h6 : (y 0) ^ 2 ≤ (L / (2 * (k : ℝ))) ^ 2 := by
      have h : (y 0) ^ 2 = |y 0| ^ 2 := by rw [sq_abs]
      rw [h]; gcongr
    have h8 : (y 1) ^ 2 ≤ (L / (2 * (k : ℝ))) ^ 2 := by
      have h : (y 1) ^ 2 = |y 1| ^ 2 := by rw [sq_abs]
      rw [h]; gcongr
    have h10 : ‖y‖ ^ 2 ≤ (L * Real.sqrt 2 / (2 * (k : ℝ))) ^ 2 := by
      rw [h4]
      have h11 : (L * Real.sqrt 2 / (2 * (k : ℝ))) ^ 2 = 2 * (L / (2 * (k : ℝ))) ^ 2 := by
        have h12 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        calc (L * Real.sqrt 2 / (2 * (k : ℝ))) ^ 2
          = L^2 * (Real.sqrt 2)^2 / (4 * (k : ℝ)^2) := by ring
        _ = L^2 * 2 / (4 * (k : ℝ)^2) := by rw [h12] <;> ring
        _ = 2 * (L / (2 * (k : ℝ))) ^ 2 := by ring
      rw [h11] <;> nlinarith
    have h_pos : 0 ≤ L * Real.sqrt 2 / (2 * (k : ℝ)) := by positivity
    have h13 : ‖y‖ ≤ L * Real.sqrt 2 / (2 * (k : ℝ)) := by
      exact le_of_sq_le_sq h10 h_pos
    have h14 : ‖y‖ ≤ r := by
      calc ‖y‖ ≤ L * Real.sqrt 2 / (2 * (k : ℝ)) := h13
        _ ≤ r := by
          have h15 : L * Real.sqrt 2 / (2 * (k : ℝ)) ≤ r := by
            have h16 : (k : ℝ) ≥ L * Real.sqrt 2 / (2 * r) := hk
            have h17 : L * Real.sqrt 2 / (2 * (k : ℝ)) ≤ L * Real.sqrt 2 / (2 * (L * Real.sqrt 2 / (2 * r))) := by gcongr
            have h18 : L * Real.sqrt 2 / (2 * (L * Real.sqrt 2 / (2 * r))) = r := by
              field_simp [hL.ne', hr.ne'] <;> ring
            rw [h18] at h17
            exact h17
          exact h15
    have hdist : dist p center' ≤ r := by
      simpa [dist_eq_norm, hy_def] using h14
    exact Set.mem_iUnion₂.mpr ⟨center', hcenter_in, hdist⟩
  exact ⟨centers, h_cover, h_card⟩

/-- Nine balls cover a dyadic square when r ≥ L√2/6. -/
lemma nine_balls_cover_square (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (h : r ≥ L * Real.sqrt 2 / 6) (a b : ℤ) :
    ∃ (c : Finset EuclideanPlane),
      (dyadicSquare L a b) ⊆ ⋃ x ∈ c, Metric.closedBall x r ∧ c.card ≤ 9 := by
  have h9 : (3 : ℝ) ≥ L * Real.sqrt 2 / (2 * r) := by
    have h_eq : L * Real.sqrt 2 / (2 * (L * Real.sqrt 2 / 6)) = 3 := by
      field_simp [hL.ne'] <;> ring
    calc (3 : ℝ)
      = L * Real.sqrt 2 / (2 * (L * Real.sqrt 2 / 6)) := h_eq.symm
    _ ≥ L * Real.sqrt 2 / (2 * r) := by gcongr
  rcases grid_cover_square L r hL hr 3 h9 a b with ⟨c, hcover, hcard⟩
  have hcard9 : c.card ≤ 9 := by
    have h : c.card ≤ 3 ^ 2 := hcard
    have h2 : 3 ^ 2 = 9 := by norm_num
    rw [h2] at h
    exact h
  exact ⟨c, hcover, hcard9⟩

end MultiscaleDecomposition

end DirecretisedFurstenbergEstimate

end
