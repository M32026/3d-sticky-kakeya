module

/-
  Appendix A, A4 helper: AffineLine packing bound.

  Proves that any Δ-separated finite set S in AffineLine satisfies
  Ncover(Δ, S) ≥ |S| / M for constant M = 9^6 = 531441.

  Uses a 6-coordinate grid argument (4 starProjection matrix entries +
  2 offset coordinates). Each Δ-ball contains at most 9^6 Δ-separated points.

  Whiteprint node: appendix_a_alternative / A4_packing
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4Plane
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA4

open DirecretisedFurstenbergEstimate

/-- Packing constant: maximum number of Δ-separated AffineLine points in a Δ-ball. -/
def affinePackingM : ℕ := 9 ^ 6

def e0 : Plane := EuclideanSpace.single 0 1
def e1 : Plane := EuclideanSpace.single 1 1

/-- Coordinate bound: each coordinate of a vector has absolute value ≤ its norm. -/
lemma coord_abs_le_norm {v : Plane} {i : Fin 2} : |v i| ≤ ‖v‖ := by
  have h1 : (v i)^2 ≤ ‖v‖^2 := by
    have h2 : ‖v‖^2 = ∑ j : Fin 2, (v j)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq] <;> rfl
    rw [h2]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have h4 : 0 ≤ |v i| := by positivity
  have h5 : 0 ≤ ‖v‖ := by positivity
  nlinarith [sq_abs (v i), sq_abs ‖v‖]

/-- Six coordinates of an AffineLine relative to a center. -/
def affineCoordDiff (T0 T : AffineLine) : Fin 6 → ℝ :=
  let sp := T.1.direction.starProjection
  let sp0 := T0.1.direction.starProjection
  ![ (sp e0) 0 - (sp0 e0) 0,
     (sp e0) 1 - (sp0 e0) 1,
     (sp e1) 0 - (sp0 e1) 0,
     (sp e1) 1 - (sp0 e1) 1,
     T.offset 0 - T0.offset 0,
     T.offset 1 - T0.offset 1 ]

/-- Grid cell index for one coordinate. -/
def gridCell (Δ : ℝ) (x : ℝ) : ℤ :=
  Int.floor ((x + Δ) / (Δ / 4))

/-- If dist(T, T0) ≤ Δ, each coordinate difference is bounded by Δ. -/
lemma coord_diff_bound {Δ : ℝ} (hΔ_pos : 0 < Δ) {T0 T : AffineLine}
    (h : dist T T0 ≤ Δ) (i : Fin 6) :
    |affineCoordDiff T0 T i| ≤ Δ := by
  let sp := T.1.direction.starProjection
  let sp0 := T0.1.direction.starProjection
  have hdef : dist T T0 = ‖sp - sp0‖ + ‖T.offset - T0.offset‖ := by rfl
  have h_sp : ‖sp - sp0‖ ≤ Δ := by
    have h_nonneg : 0 ≤ ‖T.offset - T0.offset‖ := norm_nonneg _
    have h1 : ‖sp - sp0‖ ≤ ‖sp - sp0‖ + ‖T.offset - T0.offset‖ := le_add_of_nonneg_right h_nonneg
    rw [hdef] at h
    exact h1.trans h
  have h_off : ‖T.offset - T0.offset‖ ≤ Δ := by
    have h_nonneg : 0 ≤ ‖sp - sp0‖ := norm_nonneg _
    have h1 : ‖T.offset - T0.offset‖ ≤ ‖sp - sp0‖ + ‖T.offset - T0.offset‖ := le_add_of_nonneg_left h_nonneg
    rw [hdef] at h
    exact h1.trans h
  have he0_norm : ‖e0‖ = 1 := by
    have h4 : ‖e0‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      simp [e0, EuclideanSpace.single_apply] <;> norm_num
    have h7 : 0 ≤ ‖e0‖ := by positivity
    nlinarith
  have he1_norm : ‖e1‖ = 1 := by
    have h4 : ‖e1‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      simp [e1, EuclideanSpace.single_apply] <;> norm_num
    have h7 : 0 ≤ ‖e1‖ := by positivity
    nlinarith
  have h_sp_e0 : ‖(sp - sp0) e0‖ ≤ Δ := by
    have h1 : ‖(sp - sp0) e0‖ ≤ ‖sp - sp0‖ * ‖e0‖ := ContinuousLinearMap.le_opNorm _ _
    rw [he0_norm] at h1
    simpa using h1.trans (by rw [mul_one] <;> exact h_sp)
  have h_sp_e1 : ‖(sp - sp0) e1‖ ≤ Δ := by
    have h1 : ‖(sp - sp0) e1‖ ≤ ‖sp - sp0‖ * ‖e1‖ := ContinuousLinearMap.le_opNorm _ _
    rw [he1_norm] at h1
    simpa using h1.trans (by rw [mul_one] <;> exact h_sp)
  fin_cases i
  · simpa [affineCoordDiff, e0, e1] using coord_abs_le_norm.trans h_sp_e0
  · simpa [affineCoordDiff, e0, e1] using coord_abs_le_norm.trans h_sp_e0
  · simpa [affineCoordDiff, e0, e1] using coord_abs_le_norm.trans h_sp_e1
  · simpa [affineCoordDiff, e0, e1] using coord_abs_le_norm.trans h_sp_e1
  · simpa [affineCoordDiff, e0, e1] using coord_abs_le_norm.trans h_off
  · simpa [affineCoordDiff, e0, e1] using coord_abs_le_norm.trans h_off

/-- If |x| ≤ Δ, then gridCell Δ x ∈ {0, ..., 8}. -/
lemma gridCell_range {Δ : ℝ} (hΔ_pos : 0 < Δ) {x : ℝ} (h : |x| ≤ Δ) :
    gridCell Δ x ∈ Finset.Icc (0 : ℤ) 8 := by
  have h1 : 0 ≤ x + Δ := by linarith [abs_le.mp h]
  have h2 : x + Δ ≤ 2 * Δ := by linarith [abs_le.mp h]
  have h_pos4 : 0 < Δ / 4 := by positivity
  have h3 : 0 ≤ (x + Δ) / (Δ / 4) := by positivity
  have h4 : (x + Δ) / (Δ / 4) ≤ 8 := by
    have h5 : (x + Δ) / (Δ / 4) ≤ (2 * Δ) / (Δ / 4) := by gcongr
    have h6 : (2 * Δ) / (Δ / 4) = 8 := by
      field_simp [hΔ_pos.ne'] <;> ring
    rw [h6] at h5
    exact h5
  have h6 : 0 ≤ Int.floor ((x + Δ) / (Δ / 4)) := Int.floor_nonneg.mpr h3
  have h71 : (Int.floor ((x + Δ) / (Δ / 4)) : ℝ) ≤ ((x + Δ) / (Δ / 4)) := Int.floor_le _
  have h72 : (Int.floor ((x + Δ) / (Δ / 4)) : ℝ) ≤ 8 := by linarith
  have h7 : Int.floor ((x + Δ) / (Δ / 4)) ≤ 8 := by exact_mod_cast h72
  simp only [Finset.mem_Icc]
  exact ⟨h6, h7⟩

/-- If two coordinates have the same grid cell, their difference is < Δ/4. -/
lemma same_cell_abs_lt {Δ : ℝ} (hΔ_pos : 0 < Δ) {x y : ℝ}
    (h : gridCell Δ x = gridCell Δ y) : |x - y| < Δ / 4 := by
  let k := gridCell Δ x
  have hky : k = gridCell Δ y := h
  set a := (x + Δ) / (Δ / 4) with ha_def
  set b := (y + Δ) / (Δ / 4) with hb_def
  have h1 : (k : ℝ) ≤ a := Int.floor_le a
  have h2 : a < (k : ℝ) + 1 := Int.lt_floor_add_one a
  have h3 : (k : ℝ) ≤ b := by rw [hky] <;> exact Int.floor_le b
  have h4 : b < (k : ℝ) + 1 := by rw [hky] <;> exact Int.lt_floor_add_one b
  have h5 : |a - b| < 1 := by
    by_cases h6 : a ≤ b
    · have h7 : b - a < 1 := by linarith
      have h8 : |a - b| = b - a := by
        rw [abs_of_nonpos (show a - b ≤ 0 by linarith)] <;> linarith
      rw [h8] <;> linarith
    · have h7 : a - b < 1 := by linarith
      have h8 : |a - b| = a - b := by
        rw [abs_of_nonneg (show 0 ≤ a - b by linarith)]
      rw [h8] <;> linarith
  have h_pos4 : 0 < Δ / 4 := by positivity
  have h9 : a - b = (x - y) / (Δ / 4) := by
    simp only [ha_def, hb_def] <;> ring
  have h10 : |(x - y) / (Δ / 4)| < 1 := by
    rw [← h9] <;> exact h5
  have h11 : |(x - y) / (Δ / 4)| = |x - y| / (Δ / 4) := by
    have h_pos4' : 0 < Δ / 4 := h_pos4
    rw [abs_div, abs_of_pos h_pos4']
  rw [h11] at h10
  have h12 : |x - y| / (Δ / 4) < 1 := h10
  have h13 : |x - y| < Δ / 4 := by
    calc |x - y|
      = (|x - y| / (Δ / 4)) * (Δ / 4) := by field_simp [h_pos4.ne'] <;> ring
    _ < 1 * (Δ / 4) := by gcongr
    _ = Δ / 4 := by ring
  exact h13

/-- Helper: if ‖v‖^2 < 2*(Δ/4)^2 then ‖v‖ < √2*Δ/4. -/
lemma norm_lt_sqrt2 {Δ : ℝ} (hΔ_pos : 0 < Δ) {v : Plane}
    (h : ‖v‖ ^ 2 < 2 * (Δ / 4) ^ 2) : ‖v‖ < Real.sqrt 2 * Δ / 4 := by
  have h_pos : 0 ≤ ‖v‖ := by positivity
  have h_rhs_pos : 0 < Real.sqrt 2 * Δ / 4 := by positivity
  have h_sq : (Real.sqrt 2 * Δ / 4) ^ 2 = 2 * (Δ / 4) ^ 2 := by
    calc (Real.sqrt 2 * Δ / 4) ^ 2
      = (Real.sqrt 2) ^ 2 * (Δ / 4) ^ 2 := by ring
    _ = 2 * (Δ / 4) ^ 2 := by
      have h5 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      rw [h5] <;> ring
  have h6 : ‖v‖ ^ 2 < (Real.sqrt 2 * Δ / 4) ^ 2 := by rw [h_sq] <;> exact h
  have h7 : |‖v‖| < |Real.sqrt 2 * Δ / 4| := sq_lt_sq.mp h6
  rw [abs_of_nonneg h_pos, abs_of_pos h_rhs_pos] at h7
  exact h7

/-- Helper: operator norm squared ≤ sum of squared norms on orthonormal basis. -/
lemma op_norm_sq_le_sum {f : Plane →L[ℝ] Plane} :
    ‖f‖ ^ 2 ≤ ‖f e0‖ ^ 2 + ‖f e1‖ ^ 2 := by
  have h1 : ∀ (v : Plane), ‖f v‖ ^ 2 ≤ ‖v‖ ^ 2 * (‖f e0‖ ^ 2 + ‖f e1‖ ^ 2) := by
    intro v
    have h_decomp : v = (v 0) • e0 + (v 1) • e1 := by
      ext i; fin_cases i <;> simp [e0, e1] <;> ring
    have h51 : f v = (v 0) • f e0 + (v 1) • f e1 := by
      have h1 : f v = f ((v 0) • e0 + (v 1) • e1) := by
        apply congr_arg f
        exact h_decomp
      rw [h1]
      have h2 : f ((v 0) • e0 + (v 1) • e1) = f ((v 0) • e0) + f ((v 1) • e1) := map_add f _ _
      rw [h2]
      have h3 : f ((v 0) • e0) = (v 0) • f e0 := map_smul f (v 0) e0
      have h4 : f ((v 1) • e1) = (v 1) • f e1 := map_smul f (v 1) e1
      rw [h3, h4]
    have h_tri : ‖f v‖ ≤ |v 0| * ‖f e0‖ + |v 1| * ‖f e1‖ := by
      rw [h51]
      have h6 : ‖(v 0) • f e0 + (v 1) • f e1‖ ≤ ‖(v 0) • f e0‖ + ‖(v 1) • f e1‖ := norm_add_le _ _
      have h7 : ‖(v 0) • f e0‖ = |v 0| * ‖f e0‖ := by rw [norm_smul] <;> rfl
      have h8 : ‖(v 1) • f e1‖ = |v 1| * ‖f e1‖ := by rw [norm_smul] <;> rfl
      calc ‖(v 0) • f e0 + (v 1) • f e1‖
        ≤ ‖(v 0) • f e0‖ + ‖(v 1) • f e1‖ := h6
      _ = |v 0| * ‖f e0‖ + |v 1| * ‖f e1‖ := by rw [h7, h8] <;> ring
    have h_cs : (|v 0| * ‖f e0‖ + |v 1| * ‖f e1‖) ^ 2 ≤ ((v 0) ^ 2 + (v 1) ^ 2) * (‖f e0‖ ^ 2 + ‖f e1‖ ^ 2) := by
      set a := |v 0|
      set b := |v 1|
      set c := ‖f e0‖
      set d := ‖f e1‖
      have h_pos1 : 0 ≤ a := by positivity
      have h_pos2 : 0 ≤ b := by positivity
      have h_pos3 : 0 ≤ c := by positivity
      have h_pos4 : 0 ≤ d := by positivity
      have h_lagrange : (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
        ring
      have h5 : (a * d - b * c) ^ 2 ≥ 0 := sq_nonneg _
      have h_abs1 : a ^ 2 = (v 0) ^ 2 := by simp [a, sq_abs]
      have h_abs2 : b ^ 2 = (v 1) ^ 2 := by simp [b, sq_abs]
      nlinarith
    have h_norm2 : (v 0) ^ 2 + (v 1) ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    have h4 : ‖f v‖ ^ 2 ≤ (|v 0| * ‖f e0‖ + |v 1| * ‖f e1‖) ^ 2 := by gcongr
    rw [h_norm2] at h_cs
    exact h4.trans h_cs
  have h2 : ∀ (v : Plane), ‖f v‖ ≤ Real.sqrt (‖f e0‖ ^ 2 + ‖f e1‖ ^ 2) * ‖v‖ := by
    intro v
    have h3 := h1 v
    have h4 : 0 ≤ ‖f v‖ := by positivity
    have h5 : 0 ≤ Real.sqrt (‖f e0‖ ^ 2 + ‖f e1‖ ^ 2) * ‖v‖ := by positivity
    nlinarith [Real.sq_sqrt (show 0 ≤ ‖f e0‖ ^ 2 + ‖f e1‖ ^ 2 by positivity)]
  have h6 : ‖f‖ ≤ Real.sqrt (‖f e0‖ ^ 2 + ‖f e1‖ ^ 2) := by
    simpa [ContinuousLinearMap.opNorm_le_iff] using h2
  have h7 : 0 ≤ ‖f‖ := by positivity
  nlinarith [Real.sq_sqrt (show 0 ≤ ‖f e0‖ ^ 2 + ‖f e1‖ ^ 2 by positivity)]

/-- If all 6 coordinate differences are < Δ/4, then AffineLine distance < Δ. -/
lemma all_coords_lt_imp_dist_lt {Δ : ℝ} (hΔ_pos : 0 < Δ) {T1 T2 : AffineLine}
    (h : ∀ i : Fin 6, |affineCoordDiff T1 T2 i| < Δ / 4) :
    dist T1 T2 < Δ := by
  let sp1 := T1.1.direction.starProjection
  let sp2 := T2.1.direction.starProjection
  let dsp := sp2 - sp1
  let doff := T2.offset - T1.offset
  have h_pos4 : 0 < Δ / 4 := by positivity
  have h_eq00 : (dsp e0) 0 = affineCoordDiff T1 T2 0 := by
    simp [dsp, affineCoordDiff, e0, e1] <;> rfl
  have h_eq01 : (dsp e0) 1 = affineCoordDiff T1 T2 1 := by
    simp [dsp, affineCoordDiff, e0, e1] <;> rfl
  have h_eq10 : (dsp e1) 0 = affineCoordDiff T1 T2 2 := by
    simp [dsp, affineCoordDiff, e0, e1] <;> rfl
  have h_eq11 : (dsp e1) 1 = affineCoordDiff T1 T2 3 := by
    simp [dsp, affineCoordDiff, e0, e1] <;> rfl
  have h_eqo0 : doff 0 = affineCoordDiff T1 T2 4 := by
    simp [doff, affineCoordDiff] <;> rfl
  have h_eqo1 : doff 1 = affineCoordDiff T1 T2 5 := by
    simp [doff, affineCoordDiff] <;> rfl
  have h00 : |(dsp e0) 0| < Δ / 4 := by rw [h_eq00]; exact h 0
  have h01 : |(dsp e0) 1| < Δ / 4 := by rw [h_eq01]; exact h 1
  have h10 : |(dsp e1) 0| < Δ / 4 := by rw [h_eq10]; exact h 2
  have h11 : |(dsp e1) 1| < Δ / 4 := by rw [h_eq11]; exact h 3
  have ho0 : |doff 0| < Δ / 4 := by rw [h_eqo0]; exact h 4
  have ho1 : |doff 1| < Δ / 4 := by rw [h_eqo1]; exact h 5
  have h_e0_sq : ‖dsp e0‖ ^ 2 < 2 * (Δ / 4) ^ 2 := by
    have h_norm : ‖dsp e0‖ ^ 2 = ((dsp e0) 0) ^ 2 + ((dsp e0) 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    rw [h_norm]
    have h1 : ((dsp e0) 0) ^ 2 < (Δ / 4) ^ 2 := by
      have h2 : |(dsp e0) 0| < |Δ / 4| := by rw [abs_of_pos h_pos4] <;> exact h00
      exact sq_lt_sq.mpr h2
    have h2 : ((dsp e0) 1) ^ 2 < (Δ / 4) ^ 2 := by
      have h3 : |(dsp e0) 1| < |Δ / 4| := by rw [abs_of_pos h_pos4] <;> exact h01
      exact sq_lt_sq.mpr h3
    linarith
  have h_e1_sq : ‖dsp e1‖ ^ 2 < 2 * (Δ / 4) ^ 2 := by
    have h_norm : ‖dsp e1‖ ^ 2 = ((dsp e1) 0) ^ 2 + ((dsp e1) 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    rw [h_norm]
    have h1 : ((dsp e1) 0) ^ 2 < (Δ / 4) ^ 2 := by
      have h2 : |(dsp e1) 0| < |Δ / 4| := by rw [abs_of_pos h_pos4] <;> exact h10
      exact sq_lt_sq.mpr h2
    have h2 : ((dsp e1) 1) ^ 2 < (Δ / 4) ^ 2 := by
      have h3 : |(dsp e1) 1| < |Δ / 4| := by rw [abs_of_pos h_pos4] <;> exact h11
      exact sq_lt_sq.mpr h3
    linarith
  have h_off_sq : ‖doff‖ ^ 2 < 2 * (Δ / 4) ^ 2 := by
    have h_norm : ‖doff‖ ^ 2 = (doff 0) ^ 2 + (doff 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    rw [h_norm]
    have h1 : (doff 0) ^ 2 < (Δ / 4) ^ 2 := by
      have h2 : |doff 0| < |Δ / 4| := by rw [abs_of_pos h_pos4] <;> exact ho0
      exact sq_lt_sq.mpr h2
    have h2 : (doff 1) ^ 2 < (Δ / 4) ^ 2 := by
      have h3 : |doff 1| < |Δ / 4| := by rw [abs_of_pos h_pos4] <;> exact ho1
      exact sq_lt_sq.mpr h3
    linarith
  have h_op_sq : ‖dsp‖ ^ 2 ≤ ‖dsp e0‖ ^ 2 + ‖dsp e1‖ ^ 2 := op_norm_sq_le_sum (f := dsp)
  have h_sum : ‖dsp e0‖ ^ 2 + ‖dsp e1‖ ^ 2 < (Δ / 2) ^ 2 := by
    linarith
  have h_op_lt : ‖dsp‖ < Δ / 2 := by
    have h_pos : 0 ≤ ‖dsp‖ := by positivity
    have h_sq : ‖dsp‖ ^ 2 < (Δ / 2) ^ 2 := by linarith
    have h_abs : |‖dsp‖| < |Δ / 2| := sq_lt_sq.mp h_sq
    rw [abs_of_nonneg h_pos, abs_of_pos (by positivity)] at h_abs
    exact h_abs
  have h_off_lt : ‖doff‖ < Real.sqrt 2 * Δ / 4 := norm_lt_sqrt2 hΔ_pos h_off_sq
  have h_main : dist T1 T2 = ‖sp1 - sp2‖ + ‖T1.offset - T2.offset‖ := by rfl
  have h_dsp_symm : ‖sp1 - sp2‖ = ‖dsp‖ := by
    have h : sp1 - sp2 = -dsp := by simp [dsp] <;> ring
    rw [h]; rw [norm_neg]
  have h_off_symm : ‖T1.offset - T2.offset‖ = ‖doff‖ := by
    have h : T1.offset - T2.offset = -doff := by simp [doff] <;> ring
    rw [h]; rw [norm_neg]
  rw [h_main, h_dsp_symm, h_off_symm]
  have h9 : (2 : ℝ) + Real.sqrt 2 < 4 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  calc ‖dsp‖ + ‖doff‖
    ≤ Δ / 2 + ‖doff‖ := by linarith
  _ < Δ / 2 + Real.sqrt 2 * Δ / 4 := by gcongr
  _ = ((2 + Real.sqrt 2) / 4) * Δ := by ring
  _ < Δ := by
    have h10 : (2 + Real.sqrt 2) / 4 < 1 := by linarith
    have h11 : 0 < Δ := hΔ_pos
    nlinarith

/-- The cell map from an AffineLine (relative to center T0) to 6 grid indices. -/
def affineCellMap (Δ : ℝ) (T0 T : AffineLine) : Fin 6 → ℤ :=
  fun i => gridCell Δ (affineCoordDiff T0 T i)

/-- Helper: extract first base-9 digit from equality. -/
lemma base9_step (a0 a1 b0 b1 : ℕ) (ha0 : a0 ≤ 8) (hb0 : b0 ≤ 8)
    (h : a0 + 9 * a1 = b0 + 9 * b1) : a0 = b0 ∧ a1 = b1 := by
  have ha0_mod : a0 % 9 = a0 := Nat.mod_eq_of_lt (by omega)
  have hb0_mod : b0 % 9 = b0 := Nat.mod_eq_of_lt (by omega)
  have h_mod : (a0 + 9 * a1) % 9 = (b0 + 9 * b1) % 9 := by rw [h]
  have h0 : a0 % 9 = b0 % 9 := by
    simp [Nat.add_mod, Nat.mul_mod] at h_mod <;> exact h_mod
  have h_eq0 : a0 = b0 := by
    rw [ha0_mod, hb0_mod] at h0; exact h0
  have h1 : 9 * a1 = 9 * b1 := by
    rw [h_eq0] at h; exact add_left_cancel h
  have h_eq1 : a1 = b1 := by
    apply mul_left_cancel₀ (show (9 : ℕ) ≠ 0 by norm_num); exact h1
  exact ⟨h_eq0, h_eq1⟩

/-- Ball packing: any Δ-separated subset of a Δ-ball has at most 9^6 points. -/
lemma affineLine_ball_packing {Δ : ℝ} (hΔ_pos : 0 < Δ) (T0 : AffineLine)
    {S : Finset AffineLine} (hS_sep : SeparatedAt Δ (S : Set AffineLine))
    (hS_in_ball : (S : Set AffineLine) ⊆ Metric.closedBall T0 Δ) :
    S.card ≤ affinePackingM := by
  let cellMap := affineCellMap Δ T0
  have h_inj : Set.InjOn cellMap (S : Set AffineLine) := by
    intro T1 hT1 T2 hT2 h_eq
    by_contra h_ne
    have h_sep : Δ ≤ dist T1 T2 := hS_sep hT1 hT2 h_ne
    have h1 : dist T1 T0 ≤ Δ := hS_in_ball hT1
    have h2 : dist T2 T0 ≤ Δ := hS_in_ball hT2
    have h_coords : ∀ i : Fin 6, |affineCoordDiff T1 T2 i| < Δ / 4 := by
      intro i
      have h_i1 : |affineCoordDiff T0 T1 i| ≤ Δ := coord_diff_bound hΔ_pos h1 i
      have h_i2 : |affineCoordDiff T0 T2 i| ≤ Δ := coord_diff_bound hΔ_pos h2 i
      have h_cell_eq : gridCell Δ (affineCoordDiff T0 T1 i) = gridCell Δ (affineCoordDiff T0 T2 i) :=
        congr_fun h_eq i
      have h_abs : |affineCoordDiff T0 T1 i - affineCoordDiff T0 T2 i| < Δ / 4 :=
        same_cell_abs_lt hΔ_pos h_cell_eq
      have h_diff : affineCoordDiff T1 T2 i = affineCoordDiff T0 T2 i - affineCoordDiff T0 T1 i := by
        fin_cases i <;> simp [affineCoordDiff, e0, e1] <;> ring
      rw [h_diff]
      have h_symm : |affineCoordDiff T0 T2 i - affineCoordDiff T0 T1 i| =
          |affineCoordDiff T0 T1 i - affineCoordDiff T0 T2 i| := by
        rw [show affineCoordDiff T0 T2 i - affineCoordDiff T0 T1 i =
            -(affineCoordDiff T0 T1 i - affineCoordDiff T0 T2 i) by ring]
        rw [abs_neg]
      rw [h_symm]
      exact h_abs
    have h_dist_lt : dist T1 T2 < Δ := all_coords_lt_imp_dist_lt hΔ_pos h_coords
    linarith
  let encode : AffineLine → ℕ := fun T =>
    let c := cellMap T
    (c 0).toNat + 9 * (c 1).toNat + 81 * (c 2).toNat + 729 * (c 3).toNat + 6561 * (c 4).toNat + 59049 * (c 5).toNat
  have h_bound : ∀ (T : AffineLine), T ∈ (S : Set AffineLine) → ∀ (i : Fin 6),
      0 ≤ cellMap T i ∧ cellMap T i ≤ 8 := by
    intro T hT i
    have h_dist : dist T T0 ≤ Δ := hS_in_ball hT
    have h := gridCell_range hΔ_pos (coord_diff_bound hΔ_pos h_dist i)
    simp only [Finset.mem_Icc] at h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have h_toNat_le8 : ∀ (T : AffineLine), T ∈ (S : Set AffineLine) → ∀ (i : Fin 6),
      (cellMap T i).toNat ≤ 8 := by
    intro T hT i
    have hb := h_bound T hT i
    have h_nonneg : 0 ≤ cellMap T i := hb.1
    have h_le : cellMap T i ≤ 8 := hb.2
    have h_coe : ((cellMap T i).toNat : ℤ) = cellMap T i := Int.toNat_of_nonneg h_nonneg
    have h : ((cellMap T i).toNat : ℤ) ≤ 8 := by linarith
    exact_mod_cast h
  have h_encode_lt : ∀ (T : AffineLine), T ∈ (S : Set AffineLine) → encode T < 9 ^ 6 := by
    intro T hT
    have hb := h_toNat_le8 T hT
    have h0 := hb 0
    have h1 := hb 1
    have h2 := hb 2
    have h3 := hb 3
    have h4 := hb 4
    have h5 := hb 5
    dsimp only [encode]
    omega
  have h_encode_inj : Set.InjOn encode (S : Set AffineLine) := by
    intro T1 hT1 T2 hT2 h_eq
    have hb1 := h_toNat_le8 T1 hT1
    have hb2 := h_toNat_le8 T2 hT2
    let x0 := (cellMap T1 0).toNat
    let x1 := (cellMap T1 1).toNat
    let x2 := (cellMap T1 2).toNat
    let x3 := (cellMap T1 3).toNat
    let x4 := (cellMap T1 4).toNat
    let x5 := (cellMap T1 5).toNat
    let y0 := (cellMap T2 0).toNat
    let y1 := (cellMap T2 1).toNat
    let y2 := (cellMap T2 2).toNat
    let y3 := (cellMap T2 3).toNat
    let y4 := (cellMap T2 4).toNat
    let y5 := (cellMap T2 5).toNat
    have hx0 : x0 ≤ 8 := hb1 0
    have hx1 : x1 ≤ 8 := hb1 1
    have hx2 : x2 ≤ 8 := hb1 2
    have hx3 : x3 ≤ 8 := hb1 3
    have hx4 : x4 ≤ 8 := hb1 4
    have hx5 : x5 ≤ 8 := hb1 5
    have hy0 : y0 ≤ 8 := hb2 0
    have hy1 : y1 ≤ 8 := hb2 1
    have hy2 : y2 ≤ 8 := hb2 2
    have hy3 : y3 ≤ 8 := hb2 3
    have hy4 : y4 ≤ 8 := hb2 4
    have hy5 : y5 ≤ 8 := hb2 5
    have h_eq' : x0 + 9 * (x1 + 9 * (x2 + 9 * (x3 + 9 * (x4 + 9 * x5)))) =
        y0 + 9 * (y1 + 9 * (y2 + 9 * (y3 + 9 * (y4 + 9 * y5)))) := by
      dsimp only [encode] at h_eq
      <;> ring_nf at h_eq ⊢ <;> exact h_eq
    have s1 := base9_step x0 (x1 + 9 * (x2 + 9 * (x3 + 9 * (x4 + 9 * x5))))
        y0 (y1 + 9 * (y2 + 9 * (y3 + 9 * (y4 + 9 * y5)))) hx0 hy0 h_eq'
    have h0 : x0 = y0 := s1.1
    have s2 := base9_step x1 (x2 + 9 * (x3 + 9 * (x4 + 9 * x5)))
        y1 (y2 + 9 * (y3 + 9 * (y4 + 9 * y5))) hx1 hy1 s1.2
    have h1 : x1 = y1 := s2.1
    have s3 := base9_step x2 (x3 + 9 * (x4 + 9 * x5))
        y2 (y3 + 9 * (y4 + 9 * y5)) hx2 hy2 s2.2
    have h2 : x2 = y2 := s3.1
    have s4 := base9_step x3 (x4 + 9 * x5) y3 (y4 + 9 * y5) hx3 hy3 s3.2
    have h3 : x3 = y3 := s4.1
    have s5 := base9_step x4 x5 y4 y5 hx4 hy4 s4.2
    have h4 : x4 = y4 := s5.1
    have h5 : x5 = y5 := s5.2
    have h_eq_all : ∀ i, (cellMap T1 i).toNat = (cellMap T2 i).toNat := by
      intro i; fin_cases i <;> tauto
    have h_nonneg1 : ∀ i, 0 ≤ cellMap T1 i := fun i => (h_bound T1 hT1 i).1
    have h_nonneg2 : ∀ i, 0 ≤ cellMap T2 i := fun i => (h_bound T2 hT2 i).1
    have h_cell_eq : cellMap T1 = cellMap T2 := by
      ext i
      have h6 : (cellMap T1 i).toNat = (cellMap T2 i).toNat := h_eq_all i
      have h7 : ((cellMap T1 i).toNat : ℤ) = cellMap T1 i := Int.toNat_of_nonneg (h_nonneg1 i)
      have h8 : ((cellMap T2 i).toNat : ℤ) = cellMap T2 i := Int.toNat_of_nonneg (h_nonneg2 i)
      have h9 : cellMap T1 i = cellMap T2 i := by linarith
      exact h9
    exact h_inj hT1 hT2 h_cell_eq
  have h_image_card : (S.image encode).card = S.card :=
    Finset.card_image_of_injOn h_encode_inj
  have h_image_sub : S.image encode ⊆ Finset.range (9 ^ 6) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨T, hT, rfl⟩
    exact Finset.mem_range.mpr (h_encode_lt T hT)
  calc S.card
    = (S.image encode).card := h_image_card.symm
  _ ≤ (Finset.range (9 ^ 6)).card := Finset.card_le_card h_image_sub
  _ = 9 ^ 6 := by simp
  _ = affinePackingM := by rfl

/-- Main packing bound: Ncover(Δ, S) ≥ |S| / affinePackingM for Δ-separated S. -/
lemma affineLine_ncover_lower {Δ : ℝ} (hΔ_pos : 0 < Δ)
    {S : Finset AffineLine} (hS_sep : SeparatedAt Δ (S : Set AffineLine)) :
    (S.card : ENNReal) ≤
      (affinePackingM : ENNReal) * (Metric.externalCoveringNumber Δ.toNNReal (S : Set AffineLine) : ENNReal) := by
  have h_main : ∀ (C : Set AffineLine),
      Metric.IsCover Δ.toNNReal (S : Set AffineLine) C →
      (S.card : ENNReal) ≤ (affinePackingM : ENNReal) * (C.encard : ENNReal) := by
    intro C hC
    by_cases hS_empty : S = ∅
    · simp [hS_empty]
    · classical
      have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
      let x0 : AffineLine := Classical.choose hS_nonempty
      have hx0 : x0 ∈ S := Classical.choose_spec hS_nonempty
      let f : AffineLine → AffineLine := fun x =>
        if h : x ∈ (S : Set AffineLine) then (hC h).choose else x0
      have hf_spec : ∀ (x : AffineLine), x ∈ (S : Set AffineLine) →
          f x ∈ C ∧ edist x (f x) ≤ ↑Δ.toNNReal := by
        intro x hx
        have h_fx : f x = (hC hx).choose := by
          have h : f x = (if h : x ∈ (S : Set AffineLine) then (hC h).choose else x0) := by rfl
          rw [h, dif_pos hx]
        rw [h_fx]
        exact (hC hx).choose_spec
      let Im : Finset AffineLine := S.image f
      have hIm_sub : (Im : Set AffineLine) ⊆ C := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
        exact (hf_spec x hx).1
      have h_fiber_bound : ∀ y ∈ Im, (S.filter (fun x => f x = y)).card ≤ affinePackingM := by
        intro y hy
        let fiber := S.filter (fun x => f x = y)
        have hfiber_sub : (fiber : Set AffineLine) ⊆ Metric.closedBall y Δ := by
          intro x hx
          have hxS : x ∈ (S : Set AffineLine) := (Finset.mem_filter.mp hx).1
          have hfy : f x = y := (Finset.mem_filter.mp hx).2
          have h_edist : edist x (f x) ≤ ↑Δ.toNNReal := (hf_spec x hxS).2
          rw [hfy] at h_edist
          have h_dist : dist x y ≤ Δ := by
            have h1 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
            have h2 : (↑Δ.toNNReal : ENNReal) = ENNReal.ofReal Δ := by
              have h3 : 0 ≤ Δ := hΔ_pos.le
              have h4 : (Δ.toNNReal : ℝ) = max Δ 0 := by exact Real.coe_toNNReal' Δ
              have h5 : (Δ.toNNReal : ℝ) = Δ := by
                rw [h4, max_eq_left h3]
              have h6 : (↑Δ.toNNReal : ENNReal) = ENNReal.ofReal (Δ.toNNReal : ℝ) := by
                exact Eq.symm ENNReal.ofReal_coe_nnreal
              rw [h6, h5]
            rw [h1, h2] at h_edist
            exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h_edist
          exact h_dist
        have hfiber_sep : SeparatedAt Δ (fiber : Set AffineLine) :=
          hS_sep.mono (fun x hx => (Finset.mem_filter.mp hx).1)
        exact affineLine_ball_packing hΔ_pos y hfiber_sep hfiber_sub
      have h_disj : ∀ (y : AffineLine), y ∈ Im → ∀ (z : AffineLine), z ∈ Im → y ≠ z →
          Disjoint (S.filter (fun x => f x = y)) (S.filter (fun x => f x = z)) := by
        intro y _ z _ hyz
        rw [Finset.disjoint_left]
        intro x hx
        have h1 : f x = y := (Finset.mem_filter.mp hx).2
        intro h2
        have h3 : f x = z := (Finset.mem_filter.mp h2).2
        rw [h1] at h3
        exact hyz h3
      have h1 : S = Im.biUnion (fun y => S.filter (fun x => f x = y)) := by
        ext z
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · intro hz
          refine ⟨f z, ?_, hz, rfl⟩
          exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
        · rintro ⟨y, _, hz, _⟩
          exact hz
      have h_biUnion_card : (Im.biUnion (fun y => S.filter (fun x => f x = y))).card =
          ∑ y ∈ Im, (S.filter (fun x => f x = y)).card :=
        Finset.card_biUnion (fun y _ z _ hyz => h_disj y ‹_› z ‹_› hyz)
      have h_partition : S.card = ∑ y ∈ Im, (S.filter (fun x => f x = y)).card := by
        have h_card_eq : S.card = (Im.biUnion (fun y => S.filter (fun x => f x = y))).card := by
          apply congr_arg Finset.card
          exact h1
        rw [h_card_eq, h_biUnion_card]
      have h_sum_le : ∑ y ∈ Im, (S.filter (fun x => f x = y)).card ≤ affinePackingM * Im.card := by
        calc ∑ y ∈ Im, (S.filter (fun x => f x = y)).card
          ≤ ∑ y ∈ Im, affinePackingM := Finset.sum_le_sum h_fiber_bound
        _ = affinePackingM * Im.card := by
          simp [Finset.sum_const] <;> ring
      have h_card : S.card ≤ affinePackingM * Im.card := by
        rw [h_partition]
        exact h_sum_le
      have h_encard : (Im.card : ENNReal) ≤ (C.encard : ENNReal) := by
        exact_mod_cast Set.encard_le_encard hIm_sub
      calc (S.card : ENNReal)
        ≤ (affinePackingM : ENNReal) * (Im.card : ENNReal) := by exact_mod_cast h_card
      _ ≤ (affinePackingM : ENNReal) * (C.encard : ENNReal) := by gcongr
  let N : ENat := Metric.externalCoveringNumber Δ.toNNReal (S : Set AffineLine)
  cases' hN : N with n
  · -- N = ⊤
    have h_coe : (↑N : ENNReal) = ⊤ := by
      rw [hN] <;> rfl
    rw [h_coe]
    have h_mul_top : (affinePackingM : ENNReal) * (⊤ : ENNReal) = ⊤ := by
      simp [affinePackingM]
      <;> norm_num
    rw [h_mul_top]
    <;> simp
  · -- N = ↑n
    have hn : N = ↑n := hN
    have h2 : ¬ (↑(n + 1) ≤ N) := by
      rw [hn]
      have h_lt : (↑n : ENat) < ↑(n + 1) := by
        exact_mod_cast (Nat.lt_succ_self n)
      exact not_le.mpr h_lt
    have h3 : ∃ (C : Set AffineLine) (hC : Metric.IsCover Δ.toNNReal (S : Set AffineLine) C),
        ¬ (↑(n + 1) ≤ C.encard) := by
      by_contra h
      push Not at h
      have h4 : ↑(n + 1) ≤ N := by
        simp only [N, Metric.externalCoveringNumber, le_iInf_iff] at * <;> tauto
      exact h2 h4
    rcases h3 with ⟨C, hC, h4⟩
    have h5 : C.encard < ↑(n + 1) := by exact Std.not_le.mp h4
    have h6 : N ≤ C.encard := by
      simp only [N, Metric.externalCoveringNumber]
      exact iInf_le_of_le C (iInf_le_of_le hC le_rfl)
    rw [hn] at h6
    obtain ⟨m, hm⟩ : ∃ m : ℕ, C.encard = ↑m := by
      have h7 : C.encard ≠ ⊤ := by intro h8; rw [h8] at h5; simp at h5
      exact Option.ne_none_iff_exists'.mp h7
    rw [hm] at h5 h6
    have h7 : n ≤ m := by exact_mod_cast h6
    have h8 : m < n + 1 := by exact_mod_cast h5
    have h9 : m = n := by linarith
    have hCenc : C.encard = N := by
      rw [hm, h9, hn]
    have h_main_enat : (S.card : ENat) ≤ (affinePackingM : ENat) * C.encard := by
      have h := h_main C hC
      exact_mod_cast h
    rw [hCenc] at h_main_enat
    exact_mod_cast h_main_enat

end DirecretisedFurstenbergEstimate.AppendixA4
