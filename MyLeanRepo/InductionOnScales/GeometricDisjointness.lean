module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.Homothety
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Geometric Packet Disjointness (OS Lemma 3)

Proves that global tube packets for local tubes with the same slope cell but
intercept indices differing by at least 9 are disjoint.

Uses 9-separation (factor 9) instead of 8 because interval arithmetic gives
< 8δ_k while 8-separation gives ≥ 7δ_k (no contradiction).

## Main result

`packet_geo_disjointness_core`: if a global tube T belongs to packets for
two local tubes U1, U2 with same slope cell and |U1.b - U2.b| ≥ 9, then False.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

section GeometricDisjointness

/-- Two lines through the same dyadic square with slopes within δ have
intercepts within 3*δ. -/
lemma two_lines_through_square_intercept_close
    {k : ℕ} (q : DyadicSquare k)
    (σ1 β1 σ2 β2 : ℝ)
    (h_q_bounded : q.toSet ⊆ unitSquare)
    (h_line1 : ∃ (x y : ℝ), (x, y) ∈ q.toSet ∧ y = σ1 * x + β1)
    (h_line2 : ∃ (x y : ℝ), (x, y) ∈ q.toSet ∧ y = σ2 * x + β2)
    (h_slope_close : |σ1 - σ2| < dyadicDelta k)
    (h_slope_bound : |σ1| ≤ 1) :
    |β1 - β2| < 3 * dyadicDelta k := by
  rcases h_line1 with ⟨x1, y1, h_pt1, h_eq1⟩
  rcases h_line2 with ⟨x2, y2, h_pt2, h_eq2⟩
  let δ := dyadicDelta k
  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have h_x1_in : x1 ∈ Set.Ico ((q.i : ℝ) * δ) ((q.i + 1 : ℝ) * δ) :=
    (Set.mem_prod.mp h_pt1).1
  have h_y1_in : y1 ∈ Set.Ico ((q.j : ℝ) * δ) ((q.j + 1 : ℝ) * δ) :=
    (Set.mem_prod.mp h_pt1).2
  have h_x2_in : x2 ∈ Set.Ico ((q.i : ℝ) * δ) ((q.i + 1 : ℝ) * δ) :=
    (Set.mem_prod.mp h_pt2).1
  have h_y2_in : y2 ∈ Set.Ico ((q.j : ℝ) * δ) ((q.j + 1 : ℝ) * δ) :=
    (Set.mem_prod.mp h_pt2).2
  have h_x2_unit : 0 ≤ x2 ∧ x2 < 1 := by
    have h : (x2, y2) ∈ unitSquare := h_q_bounded h_pt2
    exact (Set.mem_prod.mp h).1
  have h_abs_x2 : |x2| ≤ 1 := by rw [abs_le] <;> constructor <;> linarith
  have h_y_diff : |y1 - y2| < δ := by
    have h1 : (q.j : ℝ) * δ ≤ y1 := h_y1_in.1
    have h2 : y1 < ((q.j + 1 : ℝ) * δ) := h_y1_in.2
    have h3 : (q.j : ℝ) * δ ≤ y2 := h_y2_in.1
    have h4 : y2 < ((q.j + 1 : ℝ) * δ) := h_y2_in.2
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have h_x_diff : |x1 - x2| < δ := by
    have h1 : (q.i : ℝ) * δ ≤ x1 := h_x1_in.1
    have h2 : x1 < ((q.i + 1 : ℝ) * δ) := h_x1_in.2
    have h3 : (q.i : ℝ) * δ ≤ x2 := h_x2_in.1
    have h4 : x2 < ((q.i + 1 : ℝ) * δ) := h_x2_in.2
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have h_eq : β1 - β2 = (y1 - y2) - σ1 * (x1 - x2) - (σ1 - σ2) * x2 := by
    have h1 : β1 = y1 - σ1 * x1 := by linarith
    have h2 : β2 = y2 - σ2 * x2 := by linarith
    rw [h1, h2] <;> ring
  have h_tri : |β1 - β2| ≤
      |y1 - y2| + |σ1 * (x1 - x2)| + |(σ1 - σ2) * x2| := by
    rw [h_eq]
    set a := y1 - y2 with ha_def
    set b := σ1 * (x1 - x2) + (σ1 - σ2) * x2 with hb_def
    have h_sum : (y1 - y2) - σ1 * (x1 - x2) - (σ1 - σ2) * x2 = a - b := by
      simp [ha_def, hb_def] <;> ring
    rw [h_sum]
    have h1 : |a - b| ≤ |a| + |b| := by
      have h : |a - b| ≤ |a| + |b| := by
        calc |a - b| = |a + (-b)| := by ring_nf
          _ ≤ |a| + |(-b)| := by exact abs_add_le a (-b)
          _ = |a| + |b| := by simp
      exact h
    have h2 : |b| ≤ |σ1 * (x1 - x2)| + |(σ1 - σ2) * x2| := by
      simp only [hb_def]
      exact abs_add_le (σ1 * (x1 - x2)) ((σ1 - σ2) * x2)
    linarith
  have h_main : |y1 - y2| + |σ1 * (x1 - x2)| + |(σ1 - σ2) * x2| < 3 * δ := by
    have h1 : |y1 - y2| < δ := h_y_diff
    have h2 : |σ1 * (x1 - x2)| < δ := by
      rw [abs_mul]
      have h21 : |σ1| ≤ 1 := h_slope_bound
      have h22 : |x1 - x2| < δ := h_x_diff
      calc |σ1| * |x1 - x2| ≤ 1 * |x1 - x2| := by gcongr
        _ = |x1 - x2| := by ring
        _ < δ := h22
    have h3 : |(σ1 - σ2) * x2| < δ := by
      rw [abs_mul]
      have h31 : |σ1 - σ2| < δ := h_slope_close
      have h32 : |x2| ≤ 1 := h_abs_x2
      calc |σ1 - σ2| * |x2| ≤ |σ1 - σ2| * 1 := by gcongr
        _ = |σ1 - σ2| := by ring
        _ < δ := h31
    linarith
  exact lt_of_le_of_lt h_tri h_main


/-- Helper: slope bound from parameter strip. -/
lemma slope_bound_from_strip {n : ℕ} {T : DyadicTube n} {σ : ℝ}
    (hT_strip : T.IsInAllowedParameterStrip)
    (hσ_range : σ ∈ Set.Ico ((T.a : ℝ) * dyadicDelta n) ((T.a + 1 : ℝ) * dyadicDelta n)) :
    |σ| ≤ 1 := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h1 : -((2 ^ n : ℕ) : ℤ) ≤ T.a := hT_strip.1
  have h2 : T.a < ((2 ^ n : ℕ) : ℤ) := hT_strip.2
  have h3 : (T.a : ℝ) * δ ≤ σ := hσ_range.1
  have h4 : σ < ((T.a + 1 : ℝ) * δ) := hσ_range.2
  have hδ_eq : δ = 1 / (2 ^ n : ℝ) := dyadicDelta_eq_inv n
  have h5 : -1 ≤ σ := by
    have h6 : (T.a : ℝ) ≥ -((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h1
    have h7 : (T.a : ℝ) * δ ≤ σ := h3
    rw [hδ_eq] at h7
    have h7' : (T.a : ℝ) / (2 ^ n : ℝ) ≤ σ := by
      have h_eq2 : (T.a : ℝ) * (1 / (2 ^ n : ℝ)) = (T.a : ℝ) / (2 ^ n : ℝ) := by ring
      rw [h_eq2] at h7
      exact h7
    have h8 : (-1 : ℝ) ≤ (T.a : ℝ) / (2 ^ n : ℝ) := by
      have h9 : (T.a : ℝ) ≥ -((2 ^ n : ℕ) : ℝ) := h6
      have h10 : (2 ^ n : ℝ) > 0 := by positivity
      have h11 : (-1 : ℝ) * (2 ^ n : ℝ) = -((2 ^ n : ℕ) : ℝ) := by
        simp <;> ring
      have h12 : (-1 : ℝ) * (2 ^ n : ℝ) ≤ (T.a : ℝ) := by
        rw [h11] <;> exact h9
      calc (-1 : ℝ)
        = ((-1 : ℝ) * (2 ^ n : ℝ)) / (2 ^ n : ℝ) := by field_simp <;> ring
      _ ≤ (T.a : ℝ) / (2 ^ n : ℝ) := by gcongr
    linarith
  have h10 : σ < 1 := by
    have h11 : T.a + 1 ≤ (2 ^ n : ℕ) := by exact h2
    have h12 : σ < ((T.a + 1 : ℝ) * δ) := h4
    rw [hδ_eq] at h12
    have h12' : σ < ((T.a + 1 : ℝ) / (2 ^ n : ℝ)) := by
      have h_eq2 : ((T.a + 1 : ℝ) * (1 / (2 ^ n : ℝ))) = ((T.a + 1 : ℝ) / (2 ^ n : ℝ)) := by ring
      rw [h_eq2] at h12
      exact h12
    have h13 : ((T.a + 1 : ℝ) / (2 ^ n : ℝ)) ≤ 1 := by
      have h14 : (T.a + 1 : ℝ) ≤ (2 ^ n : ℝ) := by exact_mod_cast h11
      have h15 : (2 ^ n : ℝ) > 0 := by positivity
      calc ((T.a + 1 : ℝ) / (2 ^ n : ℝ))
        ≤ ((2 ^ n : ℝ) / (2 ^ n : ℝ)) := by gcongr
      _ = 1 := by
        have h16 : (2 ^ n : ℝ) ≠ 0 := by positivity
        field_simp [h16]
    linarith
  rw [abs_le] <;> constructor <;> linarith

/-- **Core geometric disjointness**: a global tube T cannot belong to packets
for two local tubes U1, U2 with the same slope cell and intercept indices
differing by at least 9. -/
lemma packet_geo_disjointness_core
    {n m : ℕ} (hnm : m ≤ n)
    {k : ℕ}
    (hδ_k_eq : dyadicDelta k = (2 ^ m : ℝ) * dyadicDelta n)
    (Q : DyadicSquare m)
    (q1 q2 : DyadicSquare k)
    (p1 p2 : DyadicSquare n)
    (hp1Q : squareContained hnm p1 Q)
    (hp2Q : squareContained hnm p2 Q)
    (hq1_image : ∀ (x : InductionPlane), x ∈ p1.toSet → homothetyS_Q m Q x ∈ q1.toSet)
    (hq2_image : ∀ (x : InductionPlane), x ∈ p2.toSet → homothetyS_Q m Q x ∈ q2.toSet)
    (hq1_bounded : q1.toSet ⊆ unitSquare)
    (hq2_bounded : q2.toSet ⊆ unitSquare)
    (hQ_bounded : Q.toSet ⊆ unitSquare)
    -- Global tube T
    (T : DyadicTube n)
    (hT_strip : T.IsInAllowedParameterStrip)
    (hT_inc1 : (T.toSet ∩ p1.toSet).Nonempty)
    (hT_inc2 : (T.toSet ∩ p2.toSet).Nonempty)
    -- Local tubes U1, U2
    (U1 U2 : DyadicTube k)
    (hU1_strip : U1.IsInAllowedParameterStrip)
    (hU2_strip : U2.IsInAllowedParameterStrip)
    (hU1_inc : (U1.toSet ∩ q1.toSet).Nonempty)
    (hU2_inc : (U2.toSet ∩ q2.toSet).Nonempty)
    (h_same_slope : U1.a = U2.a)
    (h_slope_cell1 : localSlopeCellIndex m T.a = U1.a)
    (h_far : |(U1.b : ℤ) - (U2.b : ℤ)| ≥ 9) :
    False := by
  let δ_n := dyadicDelta n
  let δ_k := dyadicDelta k
  let Δ := dyadicDelta m
  have hδ_n_pos : 0 < δ_n := dyadicDelta_pos n
  have hδ_k_pos : 0 < δ_k := dyadicDelta_pos k
  have hΔ_pos : 0 < Δ := dyadicDelta_pos m

  -- Q bounds from hQ_bounded: lower-left corner of Q is in Q.toSet, hence in unitSquare
  have h_corner_in_Q : ((Q.i : ℝ) * Δ, (Q.j : ℝ) * Δ) ∈ Q.toSet := by
    have hxi : (Q.i : ℝ) * Δ ∈ Set.Ico ((Q.i : ℝ) * Δ) ((Q.i + 1 : ℝ) * Δ) := by
      exact ⟨by linarith, by linarith [hΔ_pos]⟩
    have hyi : (Q.j : ℝ) * Δ ∈ Set.Ico ((Q.j : ℝ) * Δ) ((Q.j + 1 : ℝ) * Δ) := by
      exact ⟨by linarith, by linarith [hΔ_pos]⟩
    exact ⟨hxi, hyi⟩
  have h_corner_in_unit : ((Q.i : ℝ) * Δ, (Q.j : ℝ) * Δ) ∈ unitSquare :=
    hQ_bounded h_corner_in_Q
  have hQ_i_nonneg : 0 ≤ (Q.i : ℝ) := by
    have h1 : 0 ≤ (Q.i : ℝ) * Δ := (Set.mem_prod.mp h_corner_in_unit).1.1
    have h2 : 0 < Δ := hΔ_pos
    have h3 : 0 ≤ (Q.i : ℝ) := by
      nlinarith
    exact h3
  have hQ_i_lt : (Q.i : ℝ) < (2 ^ m : ℝ) := by
    have h1 : (Q.i : ℝ) * Δ < 1 := (Set.mem_prod.mp h_corner_in_unit).1.2
    have h2 : Δ = 1 / (2 ^ m : ℝ) := dyadicDelta_eq_inv m
    rw [h2] at h1
    have h3 : (Q.i : ℝ) / (2 ^ m : ℝ) < 1 := by
      have h4 : (Q.i : ℝ) * (1 / (2 ^ m : ℝ)) = (Q.i : ℝ) / (2 ^ m : ℝ) := by ring
      rw [h4] at h1
      exact h1
    have h5 : (2 ^ m : ℝ) > 0 := by positivity
    have h6 : (Q.i : ℝ) < (2 ^ m : ℝ) := by
      calc (Q.i : ℝ)
        = ((Q.i : ℝ) / (2 ^ m : ℝ)) * (2 ^ m : ℝ) := by field_simp <;> ring
      _ < 1 * (2 ^ m : ℝ) := by gcongr
      _ = (2 ^ m : ℝ) := by ring
    exact h6
  have hQ_i_bound : |(Q.i : ℝ)| < (2 ^ m : ℝ) := by
    have h1 : 0 ≤ (Q.i : ℝ) := hQ_i_nonneg
    have h2 : (Q.i : ℝ) < (2 ^ m : ℝ) := hQ_i_lt
    rw [abs_of_nonneg h1] <;> exact h2

  -- Extract lines from T through p1 and p2
  rcases hT_inc1 with ⟨pt1, hpt1_T, hpt1_p1⟩
  rcases hpt1_T with ⟨σ1, hσ1_range, β1, hβ1_range, h_eq1⟩
  rcases hT_inc2 with ⟨pt2, hpt2_T, hpt2_p2⟩
  rcases hpt2_T with ⟨σ2, hσ2_range, β2, hβ2_range, h_eq2⟩

  -- Extract lines from U1 through q1 and U2 through q2
  rcases hU1_inc with ⟨ptU1, hptU1_U1, hptU1_q1⟩
  rcases hptU1_U1 with ⟨σU1, hσU1_range, βU1, hβU1_range, h_eqU1⟩
  rcases hU2_inc with ⟨ptU2, hptU2_U2, hptU2_q2⟩
  rcases hptU2_U2 with ⟨σU2, hσU2_range, βU2, hβU2_range, h_eqU2⟩

  -- Slope bounds
  have hσ1_bound : |σ1| ≤ 1 := slope_bound_from_strip hT_strip hσ1_range
  have hσ2_bound : |σ2| ≤ 1 := slope_bound_from_strip hT_strip hσ2_range

  -- T's slope range is contained in U1's slope range
  have hT_a_bounds1 : (U1.a : ℝ) * (2 ^ m : ℝ) ≤ (T.a : ℝ) ∧
      (T.a : ℝ) < ((U1.a : ℝ) + 1) * (2 ^ m : ℝ) := by
    have h := localSlopeCellIndex_bounds m T.a
    rw [h_slope_cell1] at h
    exact_mod_cast h
  have hσ1_in_U1_range : σ1 ∈ Set.Ico ((U1.a : ℝ) * δ_k) ((U1.a + 1 : ℝ) * δ_k) := by
    have h1 : (U1.a : ℝ) * δ_k ≤ (T.a : ℝ) * δ_n := by
      have h2 : (U1.a : ℝ) * (2 ^ m : ℝ) ≤ (T.a : ℝ) := hT_a_bounds1.1
      have h3 : δ_k = (2 ^ m : ℝ) * δ_n := hδ_k_eq
      calc (U1.a : ℝ) * δ_k
        = (U1.a : ℝ) * ((2 ^ m : ℝ) * δ_n) := by rw [h3]
      _ = ((U1.a : ℝ) * (2 ^ m : ℝ)) * δ_n := by ring
      _ ≤ (T.a : ℝ) * δ_n := by gcongr
    have h4 : ((T.a + 1 : ℝ) * δ_n) ≤ ((U1.a + 1 : ℝ) * δ_k) := by
      have h5 : (T.a : ℝ) < ((U1.a : ℝ) + 1) * (2 ^ m : ℝ) := hT_a_bounds1.2
      have h5_int : T.a + 1 ≤ (U1.a + 1) * (2 ^ m : ℕ) := by
        have h5' : T.a < (U1.a + 1) * (2 ^ m : ℕ) := by exact_mod_cast h5
        omega
      have h5_real : (T.a + 1 : ℝ) ≤ ((U1.a : ℝ) + 1) * (2 ^ m : ℝ) := by exact_mod_cast h5_int
      have h6 : δ_k = (2 ^ m : ℝ) * δ_n := hδ_k_eq
      calc ((T.a + 1 : ℝ) * δ_n)
        ≤ (((U1.a : ℝ) + 1) * (2 ^ m : ℝ)) * δ_n := by gcongr
      _ = ((U1.a + 1 : ℝ) * ((2 ^ m : ℝ) * δ_n)) := by ring
      _ = ((U1.a + 1 : ℝ) * δ_k) := by rw [h6]
    exact ⟨by linarith [hσ1_range.1], by linarith [hσ1_range.2]⟩
  have h_slope_close1 : |σ1 - σU1| < δ_k := by
    have h1 : (U1.a : ℝ) * δ_k ≤ σ1 := hσ1_in_U1_range.1
    have h2 : σ1 < ((U1.a + 1 : ℝ) * δ_k) := hσ1_in_U1_range.2
    have h3 : (U1.a : ℝ) * δ_k ≤ σU1 := hσU1_range.1
    have h4 : σU1 < ((U1.a + 1 : ℝ) * δ_k) := hσU1_range.2
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

  -- Similarly for σ2 and U2
  have h_slope_cell2 : localSlopeCellIndex m T.a = U2.a := by
    rw [h_slope_cell1, h_same_slope]
  have hT_a_bounds2 : (U2.a : ℝ) * (2 ^ m : ℝ) ≤ (T.a : ℝ) ∧
      (T.a : ℝ) < ((U2.a : ℝ) + 1) * (2 ^ m : ℝ) := by
    have h := localSlopeCellIndex_bounds m T.a
    rw [h_slope_cell2] at h
    exact_mod_cast h
  have hσ2_in_U2_range : σ2 ∈ Set.Ico ((U2.a : ℝ) * δ_k) ((U2.a + 1 : ℝ) * δ_k) := by
    have h1 : (U2.a : ℝ) * δ_k ≤ (T.a : ℝ) * δ_n := by
      have h2 : (U2.a : ℝ) * (2 ^ m : ℝ) ≤ (T.a : ℝ) := hT_a_bounds2.1
      have h3 : δ_k = (2 ^ m : ℝ) * δ_n := hδ_k_eq
      calc (U2.a : ℝ) * δ_k
        = (U2.a : ℝ) * ((2 ^ m : ℝ) * δ_n) := by rw [h3]
      _ = ((U2.a : ℝ) * (2 ^ m : ℝ)) * δ_n := by ring
      _ ≤ (T.a : ℝ) * δ_n := by gcongr
    have h4 : ((T.a + 1 : ℝ) * δ_n) ≤ ((U2.a + 1 : ℝ) * δ_k) := by
      have h5 : (T.a : ℝ) < ((U2.a : ℝ) + 1) * (2 ^ m : ℝ) := hT_a_bounds2.2
      have h5_int : T.a + 1 ≤ (U2.a + 1) * (2 ^ m : ℕ) := by
        have h5' : T.a < (U2.a + 1) * (2 ^ m : ℕ) := by exact_mod_cast h5
        omega
      have h5_real : (T.a + 1 : ℝ) ≤ ((U2.a : ℝ) + 1) * (2 ^ m : ℝ) := by exact_mod_cast h5_int
      have h6 : δ_k = (2 ^ m : ℝ) * δ_n := hδ_k_eq
      calc ((T.a + 1 : ℝ) * δ_n)
        ≤ (((U2.a : ℝ) + 1) * (2 ^ m : ℝ)) * δ_n := by gcongr
      _ = ((U2.a + 1 : ℝ) * ((2 ^ m : ℝ) * δ_n)) := by ring
      _ = ((U2.a + 1 : ℝ) * δ_k) := by rw [h6]
    exact ⟨by linarith [hσ2_range.1], by linarith [hσ2_range.2]⟩
  have h_slope_close2 : |σ2 - σU2| < δ_k := by
    have h1 : (U2.a : ℝ) * δ_k ≤ σ2 := hσ2_in_U2_range.1
    have h2 : σ2 < ((U2.a + 1 : ℝ) * δ_k) := hσ2_in_U2_range.2
    have h3 : (U2.a : ℝ) * δ_k ≤ σU2 := hσU2_range.1
    have h4 : σU2 < ((U2.a + 1 : ℝ) * δ_k) := hσU2_range.2
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

  -- Reconstruct membership proofs from destructured line parameters
  have hpt1_T' : pt1 ∈ T.toSet := ⟨σ1, hσ1_range, β1, hβ1_range, h_eq1⟩
  have hpt2_T' : pt2 ∈ T.toSet := ⟨σ2, hσ2_range, β2, hβ2_range, h_eq2⟩

  -- Local intercepts of T's lines under homothety
  let β1_local := σ1 * (Q.i : ℝ) + (β1 - (Q.j : ℝ) * Δ) / Δ
  let β2_local := σ2 * (Q.i : ℝ) + (β2 - (Q.j : ℝ) * Δ) / Δ

  -- The local line (σ1, β1_local) passes through q1
  have h_local_line1_q1 : ∃ (x y : ℝ), (x, y) ∈ q1.toSet ∧ y = σ1 * x + β1_local := by
    let x1_local := (pt1.1 - (Q.i : ℝ) * Δ) / Δ
    let y1_local := (pt1.2 - (Q.j : ℝ) * Δ) / Δ
    have h_pt1_local_in_q1 : (x1_local, y1_local) ∈ q1.toSet := by
      have h1 : (x1_local, y1_local) = homothetyS_Q m Q pt1 := by
        apply Prod.ext <;> simp [homothetyS_Q, x1_local, y1_local] <;> rfl
      rw [h1]
      have h2 : homothetyS_Q m Q pt1 ∈ q1.toSet := hq1_image pt1 hpt1_p1
      exact h2
    have h_eq : y1_local = σ1 * x1_local + β1_local := by
      simp only [β1_local, x1_local, y1_local]
      have h5 : pt1.2 = σ1 * pt1.1 + β1 := h_eq1
      field_simp [hΔ_pos.ne'] <;> linarith
    exact ⟨x1_local, y1_local, h_pt1_local_in_q1, h_eq⟩

  -- The local line (σ2, β2_local) passes through q2
  have h_local_line2_q2 : ∃ (x y : ℝ), (x, y) ∈ q2.toSet ∧ y = σ2 * x + β2_local := by
    let x2_local := (pt2.1 - (Q.i : ℝ) * Δ) / Δ
    let y2_local := (pt2.2 - (Q.j : ℝ) * Δ) / Δ
    have h_pt2_local_in_q2 : (x2_local, y2_local) ∈ q2.toSet := by
      have h1 : (x2_local, y2_local) = homothetyS_Q m Q pt2 := by
        apply Prod.ext <;> simp [homothetyS_Q, x2_local, y2_local] <;> rfl
      rw [h1]
      have h2 : homothetyS_Q m Q pt2 ∈ q2.toSet := hq2_image pt2 hpt2_p2
      exact h2
    have h_eq : y2_local = σ2 * x2_local + β2_local := by
      simp only [β2_local, x2_local, y2_local]
      have h5 : pt2.2 = σ2 * pt2.1 + β2 := h_eq2
      field_simp [hΔ_pos.ne'] <;> linarith
    exact ⟨x2_local, y2_local, h_pt2_local_in_q2, h_eq⟩

  -- Apply two-lines-through-square at q1
  have h_close1 : |β1_local - βU1| < 3 * δ_k :=
    two_lines_through_square_intercept_close q1
      σ1 β1_local σU1 βU1 hq1_bounded
      h_local_line1_q1 ⟨ptU1.1, ptU1.2, hptU1_q1, h_eqU1⟩
      h_slope_close1 hσ1_bound

  -- Apply two-lines-through-square at q2
  have h_close2 : |β2_local - βU2| < 3 * δ_k :=
    two_lines_through_square_intercept_close q2
      σ2 β2_local σU2 βU2 hq2_bounded
      h_local_line2_q2 ⟨ptU2.1, ptU2.2, hptU2_q2, h_eqU2⟩
      h_slope_close2 hσ2_bound

  -- Bound |β1_local - β2_local| < 2 * δ_k
  have h_diff_local : |β1_local - β2_local| < 2 * δ_k := by
    have h1 : β1_local - β2_local =
        (σ1 - σ2) * (Q.i : ℝ) + (β1 - β2) / Δ := by
      simp [β1_local, β2_local] <;> ring
    rw [h1]
    have h2 : |σ1 - σ2| < δ_n := by
      have h21 : (T.a : ℝ) * δ_n ≤ σ1 := hσ1_range.1
      have h22 : σ1 < ((T.a + 1 : ℝ) * δ_n) := hσ1_range.2
      have h23 : (T.a : ℝ) * δ_n ≤ σ2 := hσ2_range.1
      have h24 : σ2 < ((T.a + 1 : ℝ) * δ_n) := hσ2_range.2
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have h3 : |β1 - β2| < δ_n := by
      have h31 : (T.b : ℝ) * δ_n ≤ β1 := hβ1_range.1
      have h32 : β1 < ((T.b + 1 : ℝ) * δ_n) := hβ1_range.2
      have h33 : (T.b : ℝ) * δ_n ≤ β2 := hβ2_range.1
      have h34 : β2 < ((T.b + 1 : ℝ) * δ_n) := hβ2_range.2
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have h4 : |(σ1 - σ2) * (Q.i : ℝ) + (β1 - β2) / Δ| ≤
        |σ1 - σ2| * |(Q.i : ℝ)| + |β1 - β2| / Δ := by
      have h41 : |(σ1 - σ2) * (Q.i : ℝ) + (β1 - β2) / Δ| ≤
          |(σ1 - σ2) * (Q.i : ℝ)| + |(β1 - β2) / Δ| := by exact abs_add_le ((σ1 - σ2) * ↑Q.i) ((β1 - β2) / Δ)
      have h42 : |(σ1 - σ2) * (Q.i : ℝ)| = |σ1 - σ2| * |(Q.i : ℝ)| := by rw [abs_mul]
      have h43 : |(β1 - β2) / Δ| = |β1 - β2| / Δ := by
        rw [abs_div]
        have h44 : |Δ| = Δ := abs_of_pos hΔ_pos
        rw [h44]
      rw [h42, h43] at h41
      exact h41
    have h5 : |σ1 - σ2| * |(Q.i : ℝ)| < δ_k := by
      have h6 : |σ1 - σ2| * |(Q.i : ℝ)| < δ_n * (2 ^ m : ℝ) := by
        gcongr
        <;> exact hQ_i_bound
      have h7 : δ_n * (2 ^ m : ℝ) = δ_k := by
        have h8 : (2 ^ m : ℝ) * δ_n = δ_k := hδ_k_eq.symm
        linarith
      rw [h7] at h6
      exact h6
    have h6 : |β1 - β2| / Δ < δ_k := by
      have h7 : Δ = 1 / (2 ^ m : ℝ) := dyadicDelta_eq_inv m
      rw [h7]
      have h8 : |β1 - β2| / (1 / (2 ^ m : ℝ)) = |β1 - β2| * (2 ^ m : ℝ) := by
        field_simp <;> ring
      rw [h8]
      have h9 : |β1 - β2| * (2 ^ m : ℝ) < δ_n * (2 ^ m : ℝ) := by gcongr
      have h10 : δ_n * (2 ^ m : ℝ) = δ_k := by
        have h11 : (2 ^ m : ℝ) * δ_n = δ_k := hδ_k_eq.symm
        linarith
      rw [h10] at h9
      exact h9
    have h7 : |(σ1 - σ2) * (Q.i : ℝ) + (β1 - β2) / Δ| < δ_k + δ_k := by
      calc |(σ1 - σ2) * (Q.i : ℝ) + (β1 - β2) / Δ|
        ≤ |σ1 - σ2| * |(Q.i : ℝ)| + |β1 - β2| / Δ := h4
      _ < δ_k + δ_k := by linarith
    have h8 : δ_k + δ_k = 2 * δ_k := by ring
    rw [h8] at h7
    exact h7

  -- Triangle inequality: |βU1 - βU2| < 8 * δ_k
  have h_total : |βU1 - βU2| < 8 * δ_k := by
    have h1 : |βU1 - βU2| ≤ |βU1 - β1_local| + |β1_local - βU2| := by
      have h_eq : βU1 - βU2 = (βU1 - β1_local) + (β1_local - βU2) := by ring
      rw [h_eq]
      exact abs_add_le (βU1 - β1_local) (β1_local - βU2)
    have h2 : |β1_local - βU2| ≤ |β1_local - β2_local| + |β2_local - βU2| := by
      have h_eq : β1_local - βU2 = (β1_local - β2_local) + (β2_local - βU2) := by ring
      rw [h_eq]
      exact abs_add_le (β1_local - β2_local) (β2_local - βU2)
    have h3 : |βU1 - β1_local| = |β1_local - βU1| := by
      rw [show βU1 - β1_local = -(β1_local - βU1) by ring, abs_neg]
    have h4 : |βU2 - β2_local| = |β2_local - βU2| := by
      rw [show βU2 - β2_local = -(β2_local - βU2) by ring, abs_neg]
    have h5 : |βU1 - βU2| < 3 * δ_k + 2 * δ_k + 3 * δ_k := by
      calc |βU1 - βU2|
        ≤ |βU1 - β1_local| + |β1_local - βU2| := h1
      _ ≤ |βU1 - β1_local| + (|β1_local - β2_local| + |β2_local - βU2|) := by gcongr
      _ = |β1_local - βU1| + |β1_local - β2_local| + |β2_local - βU2| := by
          rw [h3] <;> ring
      _ < 3 * δ_k + 2 * δ_k + 3 * δ_k := by gcongr <;> linarith
    have h6 : 3 * δ_k + 2 * δ_k + 3 * δ_k = 8 * δ_k := by ring
    rw [h6] at h5
    exact h5

  -- 9-separation gives |βU1 - βU2| ≥ 8 * δ_k
  have h_far' : |βU1 - βU2| ≥ 8 * δ_k := by
    have hβU1_in : βU1 ∈ Set.Ico ((U1.b : ℝ) * δ_k) ((U1.b + 1 : ℝ) * δ_k) := hβU1_range
    have hβU2_in : βU2 ∈ Set.Ico ((U2.b : ℝ) * δ_k) ((U2.b + 1 : ℝ) * δ_k) := hβU2_range
    by_cases h : U1.b ≥ U2.b
    · have h5 : U1.b - U2.b ≥ 9 := by
        have h6 : U1.b - U2.b ≥ 0 := by omega
        have h7 : |U1.b - U2.b| = U1.b - U2.b := by
          rw [abs_of_nonneg] <;> omega
        omega
      have h5' : (U1.b : ℝ) - (U2.b : ℝ) ≥ 9 := by exact_mod_cast h5
      have h6 : βU1 - βU2 > ((U1.b : ℝ) - (U2.b : ℝ) - 1) * δ_k := by
        have h61 : βU1 ≥ (U1.b : ℝ) * δ_k := hβU1_in.1
        have h62 : βU2 < ((U2.b + 1 : ℝ) * δ_k) := hβU2_in.2
        linarith
      have h7 : ((U1.b : ℝ) - (U2.b : ℝ) - 1) * δ_k ≥ 8 * δ_k := by
        have h8 : (U1.b : ℝ) - (U2.b : ℝ) - 1 ≥ 8 := by linarith
        gcongr <;> linarith
      have h9 : 0 < βU1 - βU2 := by linarith [hδ_k_pos]
      have h10 : |βU1 - βU2| = βU1 - βU2 := abs_of_pos h9
      rw [h10]
      linarith
    · have h5 : U2.b - U1.b ≥ 9 := by
        have h6 : U2.b - U1.b ≥ 0 := by omega
        have h7 : |U1.b - U2.b| = U2.b - U1.b := by
          rw [abs_of_nonpos] <;> omega
        omega
      have h5' : (U2.b : ℝ) - (U1.b : ℝ) ≥ 9 := by exact_mod_cast h5
      have h6 : βU2 - βU1 > ((U2.b : ℝ) - (U1.b : ℝ) - 1) * δ_k := by
        have h61 : βU2 ≥ (U2.b : ℝ) * δ_k := hβU2_in.1
        have h62 : βU1 < ((U1.b + 1 : ℝ) * δ_k) := hβU1_in.2
        linarith
      have h7 : ((U2.b : ℝ) - (U1.b : ℝ) - 1) * δ_k ≥ 8 * δ_k := by
        have h8 : (U2.b : ℝ) - (U1.b : ℝ) - 1 ≥ 8 := by linarith
        gcongr <;> linarith
      have h9 : 0 < βU2 - βU1 := by linarith [hδ_k_pos]
      have h10 : βU1 - βU2 < 0 := by linarith
      have h11 : |βU1 - βU2| = βU2 - βU1 := by
        rw [abs_of_neg h10] <;> linarith
      rw [h11]
      linarith

  linarith

end GeometricDisjointness

end InductionOnScales
