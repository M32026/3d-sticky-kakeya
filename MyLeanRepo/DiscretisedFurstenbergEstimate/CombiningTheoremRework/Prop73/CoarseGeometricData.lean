module

/-
  Coarse Geometric Data Lemmas

  Constructs the four geometric data parameters needed by
  coarse_bound_from_combined_v2 from the B1 bridge and coarse config:
  1. hcoarse_P_nonempty - coarse P₀ is nonempty
  2. h_slope_coarse - coarse tube slopes bounded by 1
  3. h_diam_coarse - coarse DSquare diameter ≤ 3
  4. h_unit_coarse - coarse DSquares lie in unit strip |x| ≤ 1

  Whiteprint node: combining_theorem_genuine / coarse_geometric_data
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DiscretisedFurstenbergEstimate.InductionConfigurations

abbrev B1BridgeHypotheses' (n : ℕ) {s C : ℝ} {M : ℕ}
    (config : CTNiceConfiguration n s C M) :=
  DirecretisedFurstenbergEstimate.FormatConversion.M2.B1BridgeHypotheses n config

/-! ### 1. Nonemptiness -/

/-- If the fine subset P is nonempty, then its image under containingSquare
    is nonempty, hence coarseConfig.P₀ is nonempty. -/
lemma coarse_P_nonempty_from_image
    {k m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    {P : Finset (DyadicSquare k)}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    (hnm : m ≤ k)
    (hP_nonempty : P.Nonempty)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (containingSquare hnm)) :
    coarseConfig.P₀.Nonempty := by
  rw [hcoarse_P_eq]
  exact Finset.Nonempty.image hP_nonempty _

/-! ### 2. Slope bound from B1 bridge -/

/-- From B1 bridge strip bound, derive |T.slope| ≤ 1 for all tubes. -/
lemma coarse_slope_bound_from_B1
    {m : ℕ} {s C : ℝ} {M : ℕ}
    {config : CTNiceConfiguration m s C M}
    (hB1 : B1BridgeHypotheses' m config) :
    ∀ (T : DyadicTube m), T ∈ config.T₀ → |T.slope| ≤ 1 := by
  intro T hT
  have h_strip : -(2 ^ m : ℤ) ≤ T.a ∧ T.a < (2 ^ m : ℤ) :=
    hB1.h_tubes_strip T hT
  have h1 : -(2 ^ m : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h_strip.1
  have h2 : (T.a : ℝ) < (2 ^ m : ℝ) := by exact_mod_cast h_strip.2
  have h3 : |(T.a : ℝ)| ≤ (2 ^ m : ℝ) := by
    rw [abs_le] <;> constructor <;> linarith
  have h_slope_eq : T.slope = (T.a : ℝ) * dyadicDelta m := by rfl
  have hδ_eq : dyadicDelta m = 1 / (2 ^ m : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring
  rw [h_slope_eq, hδ_eq]
  have hpos : (0 : ℝ) < (2 ^ m : ℝ) := by positivity
  have h4 : |(T.a : ℝ) * (1 / (2 ^ m : ℝ))| =
      |(T.a : ℝ)| * (1 / (2 ^ m : ℝ)) := by
    have hpos2 : (0 : ℝ) < (1 / (2 ^ m : ℝ)) := by positivity
    rw [abs_mul, abs_of_pos hpos2]
  rw [h4]
  have h5 : |(T.a : ℝ)| * (1 / (2 ^ m : ℝ)) ≤ 1 := by
    calc |(T.a : ℝ)| * (1 / (2 ^ m : ℝ))
      ≤ (2 ^ m : ℝ) * (1 / (2 ^ m : ℝ)) := by gcongr
    _ = 1 := by field_simp [hpos.ne'] <;> ring
  exact h5

/-! ### 3. Full unit square bound from B1 bridge + containingSquare -/

/-- Coarse squares obtained via containingSquare from fine squares that
    satisfy the B1 unit bound themselves lie entirely in [0,1]². -/
lemma coarse_full_unit_bound_from_B1
    {k m : ℕ} {s C CΔ : ℝ} {M MΔ : ℕ}
    {config : CTNiceConfiguration k s C M}
    {P : Finset (DyadicSquare k)}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    (hnm : m ≤ k)
    (hB1 : B1BridgeHypotheses' k config)
    (hP_sub : P ⊆ config.P₀)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (containingSquare hnm)) :
    ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet →
        0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1 := by
  intro p hp x hx
  rcases Finset.mem_image.mp hp with ⟨q, hq_in_coarse, rfl⟩
  have hq_in_P0 : q ∈ coarseConfig.P₀ := hq_in_coarse
  rw [hcoarse_P_eq] at hq_in_P0
  rcases Finset.mem_image.mp hq_in_P0 with ⟨r, hr_in_P, hq_eq⟩
  have hr_in_config : r ∈ config.P₀ := hP_sub hr_in_P
  have h_bounds : 0 ≤ r.i ∧ r.i < (2 ^ k : ℤ) ∧
      0 ≤ r.j ∧ r.j < (2 ^ k : ℤ) :=
    hB1.h_squares_unit r hr_in_config
  have hq_i_eq : (dyadicSquareToDSquare q).i = r.i / (refinementFactor k m) := by
    have h : containingSquare hnm r = q := hq_eq
    have h' := congr_arg (fun (s : DyadicSquare m) => s.i) h
    simpa [containingSquare, dyadicSquareToDSquare] using h'.symm
  have hq_j_eq : (dyadicSquareToDSquare q).j = r.j / (refinementFactor k m) := by
    have h : containingSquare hnm r = q := hq_eq
    have h' := congr_arg (fun (s : DyadicSquare m) => s.j) h
    simpa [containingSquare, dyadicSquareToDSquare] using h'.symm
  have h_ri_nonneg : 0 ≤ r.i := h_bounds.1
  have h_rf_nonneg : 0 ≤ (refinementFactor k m : ℤ) := by positivity
  have h_i_nonneg : 0 ≤ (dyadicSquareToDSquare q).i := by
    rw [hq_i_eq]
    exact Int.ediv_nonneg h_ri_nonneg h_rf_nonneg
  have h_rf_pos : 0 < (refinementFactor k m : ℤ) := by
    have h : 0 < refinementFactor k m := by dsimp only [refinementFactor] <;> positivity
    exact_mod_cast h
  have h_rf_mul : (2 ^ m : ℤ) * (refinementFactor k m : ℤ) = (2 ^ k : ℤ) := by
    have h_sum : m + (k - m) = k := by omega
    have h : (2 ^ m : ℤ) * (2 ^ (k - m) : ℤ) = (2 ^ (m + (k - m)) : ℤ) := by
      rw [← pow_add] <;> rfl
    rw [h_sum] at h
    simpa [refinementFactor] using h
  have h_i_lt : (dyadicSquareToDSquare q).i < (2 ^ m : ℤ) := by
    rw [hq_i_eq]
    have h : r.i < (2 ^ m : ℤ) * (refinementFactor k m : ℤ) := by
      rw [h_rf_mul] <;> exact h_bounds.2.1
    exact Int.ediv_lt_of_lt_mul h_rf_pos h
  have h_rj_nonneg : 0 ≤ r.j := h_bounds.2.2.1
  have h_j_nonneg : 0 ≤ (dyadicSquareToDSquare q).j := by
    rw [hq_j_eq]
    exact Int.ediv_nonneg h_rj_nonneg h_rf_nonneg
  have h_j_lt : (dyadicSquareToDSquare q).j < (2 ^ m : ℤ) := by
    rw [hq_j_eq]
    have h : r.j < (2 ^ m : ℤ) * (refinementFactor k m : ℤ) := by
      rw [h_rf_mul] <;> exact h_bounds.2.2.2
    exact Int.ediv_lt_of_lt_mul h_rf_pos h
  have hδ_eq : δ m = 1 / (2 ^ m : ℝ) := by
    simp [δ, dyadicDelta] <;> field_simp <;> ring
  have h_x1_ge : 0 ≤ x.1 := by
    have h_lo : ((dyadicSquareToDSquare q).i : ℝ) * δ m ≤ x.1 := hx.1
    have h_i0 : 0 ≤ ((dyadicSquareToDSquare q).i : ℝ) := by exact_mod_cast h_i_nonneg
    have hδ_pos : 0 < δ m := δ_pos m
    have h_nonneg : 0 ≤ ((dyadicSquareToDSquare q).i : ℝ) * δ m := mul_nonneg h_i0 (le_of_lt hδ_pos)
    exact le_trans h_nonneg h_lo
  have h_i1_le : ((dyadicSquareToDSquare q).i : ℝ) + 1 ≤ (2 ^ m : ℝ) := by
    have h : (dyadicSquareToDSquare q).i < (2 ^ m : ℤ) := h_i_lt
    have h' : (dyadicSquareToDSquare q).i + 1 ≤ (2 ^ m : ℤ) := by omega
    exact_mod_cast h'
  have h_x1_lt : x.1 < 1 := by
    have h : x.1 < (((dyadicSquareToDSquare q).i : ℝ) + 1) * δ m := hx.2.1
    have h2 : (((dyadicSquareToDSquare q).i : ℝ) + 1) * δ m ≤ 1 := by
      rw [hδ_eq]
      have hpos : (0 : ℝ) < (2 ^ m : ℝ) := by positivity
      calc (((dyadicSquareToDSquare q).i : ℝ) + 1) * (1 / (2 ^ m : ℝ))
        ≤ (2 ^ m : ℝ) * (1 / (2 ^ m : ℝ)) := by gcongr
      _ = 1 := by field_simp [hpos.ne'] <;> ring
    exact lt_of_lt_of_le h h2
  have h_x2_ge : 0 ≤ x.2 := by
    have h_lo : ((dyadicSquareToDSquare q).j : ℝ) * δ m ≤ x.2 := hx.2.2.1
    have h_j0 : 0 ≤ ((dyadicSquareToDSquare q).j : ℝ) := by exact_mod_cast h_j_nonneg
    have hδ_pos : 0 < δ m := δ_pos m
    have h_nonneg : 0 ≤ ((dyadicSquareToDSquare q).j : ℝ) * δ m := mul_nonneg h_j0 (le_of_lt hδ_pos)
    exact le_trans h_nonneg h_lo
  have h_j1_le : ((dyadicSquareToDSquare q).j : ℝ) + 1 ≤ (2 ^ m : ℝ) := by
    have h : (dyadicSquareToDSquare q).j < (2 ^ m : ℤ) := h_j_lt
    have h' : (dyadicSquareToDSquare q).j + 1 ≤ (2 ^ m : ℤ) := by omega
    exact_mod_cast h'
  have h_x2_lt : x.2 < 1 := by
    have h : x.2 < (((dyadicSquareToDSquare q).j : ℝ) + 1) * δ m := hx.2.2.2
    have h2 : (((dyadicSquareToDSquare q).j : ℝ) + 1) * δ m ≤ 1 := by
      rw [hδ_eq]
      have hpos : (0 : ℝ) < (2 ^ m : ℝ) := by positivity
      calc (((dyadicSquareToDSquare q).j : ℝ) + 1) * (1 / (2 ^ m : ℝ))
        ≤ (2 ^ m : ℝ) * (1 / (2 ^ m : ℝ)) := by gcongr
      _ = 1 := by field_simp [hpos.ne'] <;> ring
    exact lt_of_lt_of_le h h2
  exact ⟨h_x1_ge, h_x1_lt, h_x2_ge, h_x2_lt⟩

/-- The consumer only needs |x.1| ≤ 1, which follows from the full bound. -/
lemma coarse_unit_coarse_from_full
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    (h_full : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1) :
    ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1 := by
  intro p hp x hx
  have h := h_full p hp x hx
  have h1 : 0 ≤ x.1 := h.1
  have h2 : x.1 < 1 := h.2.1
  rw [abs_le]
  constructor <;> linarith

/-! ### 4. Diameter bound from full unit bound -/

/-- Lower-left corner of a DSquare is always in its toSet. -/
lemma dSquare_toPoint_mem_toSet {m : ℕ} (p : DSquare m) : p.toPoint ∈ p.toSet := by
  have hδ_pos : 0 < δ m := δ_pos m
  simp only [DSquare.toPoint, DSquare.toSet, Set.mem_setOf_eq]
  have h1 : (p.i : ℝ) * δ m ≤ (p.i : ℝ) * δ m := by rfl
  have h2 : (p.i : ℝ) * δ m < ((p.i : ℝ) + 1) * δ m := by
    have h3 : (p.i : ℝ) < (p.i : ℝ) + 1 := by linarith
    exact mul_lt_mul_of_pos_right h3 hδ_pos
  have h4 : (p.j : ℝ) * δ m ≤ (p.j : ℝ) * δ m := by rfl
  have h5 : (p.j : ℝ) * δ m < ((p.j : ℝ) + 1) * δ m := by
    have h6 : (p.j : ℝ) < (p.j : ℝ) + 1 := by linarith
    exact mul_lt_mul_of_pos_right h6 hδ_pos
  exact ⟨h1, h2, h4, h5⟩

/-- If all coarse DSquares lie in [0,1]², then the distance between any
    two lower-left corners is at most √2 < 3. -/
lemma coarse_diam_from_full_unit
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    (h_full : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1) :
    ∀ (p q : DSquare m),
      p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      q ∈ finsetDyadicToDSquare coarseConfig.P₀ → dist p q ≤ 3 := by
  intro p q hp hq
  have h_p_in : p.toPoint ∈ p.toSet := dSquare_toPoint_mem_toSet p
  have h_q_in : q.toPoint ∈ q.toSet := dSquare_toPoint_mem_toSet q
  have hp_bounds := h_full p hp p.toPoint h_p_in
  have hq_bounds := h_full q hq q.toPoint h_q_in
  have h_p1 : 0 ≤ p.toPoint.1 := hp_bounds.1
  have h_p1' : p.toPoint.1 ≤ 1 := le_of_lt hp_bounds.2.1
  have h_p2 : 0 ≤ p.toPoint.2 := hp_bounds.2.2.1
  have h_p2' : p.toPoint.2 ≤ 1 := le_of_lt hp_bounds.2.2.2
  have h_q1 : 0 ≤ q.toPoint.1 := hq_bounds.1
  have h_q1' : q.toPoint.1 ≤ 1 := le_of_lt hq_bounds.2.1
  have h_q2 : 0 ≤ q.toPoint.2 := hq_bounds.2.2.1
  have h_q2' : q.toPoint.2 ≤ 1 := le_of_lt hq_bounds.2.2.2
  have h_dist : dist p q = dist p.toPoint q.toPoint := by rfl
  rw [h_dist]
  have h_sup : dist p.toPoint q.toPoint = max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2| := by
    simp [Prod.dist_eq]
    <;> rfl
  rw [h_sup]
  have h1_left : -1 ≤ p.toPoint.1 - q.toPoint.1 := by
    have h := sub_le_sub h_p1 h_q1'
    simpa using h
  have h1_right : p.toPoint.1 - q.toPoint.1 ≤ 1 := by
    have h := sub_le_sub h_p1' h_q1
    simpa using h
  have h1 : |p.toPoint.1 - q.toPoint.1| ≤ 1 := by
    rw [abs_le] <;> exact ⟨h1_left, h1_right⟩
  have h2_left : -1 ≤ p.toPoint.2 - q.toPoint.2 := by
    have h := sub_le_sub h_p2 h_q2'
    simpa using h
  have h2_right : p.toPoint.2 - q.toPoint.2 ≤ 1 := by
    have h := sub_le_sub h_p2' h_q2
    simpa using h
  have h2 : |p.toPoint.2 - q.toPoint.2| ≤ 1 := by
    rw [abs_le] <;> exact ⟨h2_left, h2_right⟩
  have h_max_le_1 : max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2| ≤ 1 :=
    max_le h1 h2
  have h_final : max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2| ≤ 3 := by
    calc max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2|
      ≤ 1 := h_max_le_1
    _ ≤ 3 := by norm_num
  exact h_final

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
