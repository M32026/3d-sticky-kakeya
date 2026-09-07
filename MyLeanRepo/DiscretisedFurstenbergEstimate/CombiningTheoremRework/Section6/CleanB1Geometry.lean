module

/-
  Clean B1 Geometry Lemmas

  Mechanical extraction of geometry facts from B1BridgeHypotheses,
  reproduced from B1ToSection6.lean to avoid Prop73 contamination.

  Provides foundational versions (taking only h_squares_unit):
  - b1_geometry_full_unit_of_bounds: all points in all DSquares lie in [0,1)²
  - b1_geometry_unit_of_bounds: |x.1| ≤ 1 for all points in all DSquares
  - b1_geometry_diam_of_bounds: dist p q ≤ 3 for any two DSquares

  And B1BridgeHypotheses wrappers:
  - b1_geometry_slope: |T.slope| ≤ 1 for all tubes
  - b1_geometry_full_unit: all points in all DSquares lie in [0,1)²
  - b1_geometry_unit: |x.1| ≤ 1 for all points in all DSquares
  - b1_geometry_diam: dist p q ≤ 3 for any two DSquares

  Dependencies: Base, CombiningTheorem, FormatConversionLemmas,
  DyadicTubes, DyadicConversion, Mathlib.

  Whiteprint node: clean_b1_geometry
  Status: COMPLETE (mechanical extraction)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ElementaryIncidence
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- From `hB1.h_tubes_strip`, derive `|T.slope| ≤ 1` for all tubes. -/
lemma b1_geometry_slope
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (hB1 : B1BridgeHypotheses k config) :
    ∀ (T : DyadicTube k), T ∈ config.T₀ → |T.slope| ≤ 1 := by
  intro T hT
  have h_strip : -(2 ^ k : ℤ) ≤ T.a ∧ T.a < (2 ^ k : ℤ) :=
    hB1.h_tubes_strip T hT
  have h1 : -(2 ^ k : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h_strip.1
  have h2 : (T.a : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast h_strip.2
  have h3 : |(T.a : ℝ)| ≤ (2 ^ k : ℝ) := by
    rw [abs_le] <;> constructor <;> linarith
  have h_slope_eq : T.slope = (T.a : ℝ) * dyadicDelta k := by rfl
  have hδ_eq : dyadicDelta k = 1 / (2 ^ k : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring
  rw [h_slope_eq, hδ_eq]
  have hpos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
  have h4 : |(T.a : ℝ) * (1 / (2 ^ k : ℝ))| =
      |(T.a : ℝ)| * (1 / (2 ^ k : ℝ)) := by
    have hpos2 : (0 : ℝ) < (1 / (2 ^ k : ℝ)) := by positivity
    rw [abs_mul, abs_of_pos hpos2]
  rw [h4]
  have h5 : |(T.a : ℝ)| * (1 / (2 ^ k : ℝ)) ≤ 1 := by
    calc |(T.a : ℝ)| * (1 / (2 ^ k : ℝ))
      ≤ (2 ^ k : ℝ) * (1 / (2 ^ k : ℝ)) := by gcongr
    _ = 1 := by field_simp [hpos.ne'] <;> ring
  exact h5

/-- Foundational version: from square index bounds, derive that all points
    in all DSquares lie in [0,1)². -/
lemma b1_geometry_full_unit_of_bounds
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (h_squares_unit : ∀ (q : DyadicSquare k), q ∈ config.P₀ →
      0 ≤ q.i ∧ q.i < (2 ^ k : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ k : ℤ)) :
    ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet →
        0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1 := by
  intro p hp x hx
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  have h_bounds := h_squares_unit q hq
  have h_i_nonneg : 0 ≤ (dyadicSquareToDSquare q).i := by
    simpa [dyadicSquareToDSquare] using h_bounds.1
  have h_i_lt : (dyadicSquareToDSquare q).i < (2 ^ k : ℤ) := by
    simpa [dyadicSquareToDSquare] using h_bounds.2.1
  have h_j_nonneg : 0 ≤ (dyadicSquareToDSquare q).j := by
    simpa [dyadicSquareToDSquare] using h_bounds.2.2.1
  have h_j_lt : (dyadicSquareToDSquare q).j < (2 ^ k : ℤ) := by
    simpa [dyadicSquareToDSquare] using h_bounds.2.2.2
  have hδ_eq : δ k = 1 / (2 ^ k : ℝ) := by
    simp [δ] <;> field_simp <;> ring
  have hδ_pos : 0 < δ k := δ_pos k
  have h_x1_ge : 0 ≤ x.1 := by
    have h_lo : ((dyadicSquareToDSquare q).i : ℝ) * δ k ≤ x.1 := hx.1
    have h_i0 : 0 ≤ ((dyadicSquareToDSquare q).i : ℝ) := by exact_mod_cast h_i_nonneg
    have h_nonneg : 0 ≤ ((dyadicSquareToDSquare q).i : ℝ) * δ k := mul_nonneg h_i0 (le_of_lt hδ_pos)
    exact le_trans h_nonneg h_lo
  have h_i1_le : ((dyadicSquareToDSquare q).i : ℝ) + 1 ≤ (2 ^ k : ℝ) := by
    have h : (dyadicSquareToDSquare q).i < (2 ^ k : ℤ) := h_i_lt
    have h' : (dyadicSquareToDSquare q).i + 1 ≤ (2 ^ k : ℤ) := by omega
    exact_mod_cast h'
  have h_x1_lt : x.1 < 1 := by
    have h : x.1 < (((dyadicSquareToDSquare q).i : ℝ) + 1) * δ k := hx.2.1
    have h2 : (((dyadicSquareToDSquare q).i : ℝ) + 1) * δ k ≤ 1 := by
      rw [hδ_eq]
      have hpos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
      calc (((dyadicSquareToDSquare q).i : ℝ) + 1) * (1 / (2 ^ k : ℝ))
        ≤ (2 ^ k : ℝ) * (1 / (2 ^ k : ℝ)) := by gcongr
      _ = 1 := by field_simp [hpos.ne'] <;> ring
    exact lt_of_lt_of_le h h2
  have h_x2_ge : 0 ≤ x.2 := by
    have h_lo : ((dyadicSquareToDSquare q).j : ℝ) * δ k ≤ x.2 := hx.2.2.1
    have h_j0 : 0 ≤ ((dyadicSquareToDSquare q).j : ℝ) := by exact_mod_cast h_j_nonneg
    have h_nonneg : 0 ≤ ((dyadicSquareToDSquare q).j : ℝ) * δ k := mul_nonneg h_j0 (le_of_lt hδ_pos)
    exact le_trans h_nonneg h_lo
  have h_j1_le : ((dyadicSquareToDSquare q).j : ℝ) + 1 ≤ (2 ^ k : ℝ) := by
    have h : (dyadicSquareToDSquare q).j < (2 ^ k : ℤ) := h_j_lt
    have h' : (dyadicSquareToDSquare q).j + 1 ≤ (2 ^ k : ℤ) := by omega
    exact_mod_cast h'
  have h_x2_lt : x.2 < 1 := by
    have h : x.2 < (((dyadicSquareToDSquare q).j : ℝ) + 1) * δ k := hx.2.2.2
    have h2 : (((dyadicSquareToDSquare q).j : ℝ) + 1) * δ k ≤ 1 := by
      rw [hδ_eq]
      have hpos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
      calc (((dyadicSquareToDSquare q).j : ℝ) + 1) * (1 / (2 ^ k : ℝ))
        ≤ (2 ^ k : ℝ) * (1 / (2 ^ k : ℝ)) := by gcongr
      _ = 1 := by field_simp [hpos.ne'] <;> ring
    exact lt_of_lt_of_le h h2
  exact ⟨h_x1_ge, h_x1_lt, h_x2_ge, h_x2_lt⟩

/-- Foundational version: from square index bounds, derive `|x.1| ≤ 1`
    for all points in all DSquares. -/
lemma b1_geometry_unit_of_bounds
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (h_squares_unit : ∀ (q : DyadicSquare k), q ∈ config.P₀ →
      0 ≤ q.i ∧ q.i < (2 ^ k : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ k : ℤ)) :
    ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1 := by
  have h_full := b1_geometry_full_unit_of_bounds h_squares_unit
  intro p hp x hx
  have h := h_full p hp x hx
  have h1 : 0 ≤ x.1 := h.1
  have h2 : x.1 < 1 := h.2.1
  rw [abs_le] <;> constructor <;> linarith

/-- Foundational version: from square index bounds, derive `dist p q ≤ 3`
    for any two DSquares. -/
lemma b1_geometry_diam_of_bounds
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (h_squares_unit : ∀ (q : DyadicSquare k), q ∈ config.P₀ →
      0 ≤ q.i ∧ q.i < (2 ^ k : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ k : ℤ)) :
    ∀ (p q : DSquare k),
      p ∈ finsetDyadicToDSquare config.P₀ →
      q ∈ finsetDyadicToDSquare config.P₀ → dist p q ≤ 3 := by
  have h_full := b1_geometry_full_unit_of_bounds h_squares_unit
  intro p q hp hq
  have h_p_in : p.toPoint ∈ p.toSet := by
    have hδ_pos : 0 < δ k := δ_pos k
    simp only [DSquare.toPoint, DSquare.toSet, Set.mem_setOf_eq]
    have h1 : (p.i : ℝ) * δ k ≤ (p.i : ℝ) * δ k := by rfl
    have h2 : (p.i : ℝ) * δ k < ((p.i : ℝ) + 1) * δ k := by
      have h3 : (p.i : ℝ) < (p.i : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_right h3 hδ_pos
    have h4 : (p.j : ℝ) * δ k ≤ (p.j : ℝ) * δ k := by rfl
    have h5 : (p.j : ℝ) * δ k < ((p.j : ℝ) + 1) * δ k := by
      have h6 : (p.j : ℝ) < (p.j : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_right h6 hδ_pos
    exact ⟨h1, h2, h4, h5⟩
  have h_q_in : q.toPoint ∈ q.toSet := by
    have hδ_pos : 0 < δ k := δ_pos k
    simp only [DSquare.toPoint, DSquare.toSet, Set.mem_setOf_eq]
    have h1 : (q.i : ℝ) * δ k ≤ (q.i : ℝ) * δ k := by rfl
    have h2 : (q.i : ℝ) * δ k < ((q.i : ℝ) + 1) * δ k := by
      have h3 : (q.i : ℝ) < (q.i : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_right h3 hδ_pos
    have h4 : (q.j : ℝ) * δ k ≤ (q.j : ℝ) * δ k := by rfl
    have h5 : (q.j : ℝ) * δ k < ((q.j : ℝ) + 1) * δ k := by
      have h6 : (q.j : ℝ) < (q.j : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_right h6 hδ_pos
    exact ⟨h1, h2, h4, h5⟩
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
    simp [Prod.dist_eq] <;> rfl
  rw [h_sup]
  have h1 : |p.toPoint.1 - q.toPoint.1| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith
  have h2 : |p.toPoint.2 - q.toPoint.2| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith
  have h_max_le_1 : max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2| ≤ 1 :=
    max_le h1 h2
  have h_final : max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2| ≤ 3 := by
    calc max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2|
      ≤ 1 := h_max_le_1
    _ ≤ 3 := by norm_num
  exact h_final

/-- Wrapper: from `hB1.h_squares_unit`, derive all points in all DSquares
    lie in [0,1)². -/
lemma b1_geometry_full_unit
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (hB1 : B1BridgeHypotheses k config) :
    ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet →
        0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1 :=
  b1_geometry_full_unit_of_bounds hB1.h_squares_unit

/-- Wrapper: from `hB1.h_squares_unit`, derive `|x.1| ≤ 1` for all points
    in all DSquares. -/
lemma b1_geometry_unit
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (hB1 : B1BridgeHypotheses k config) :
    ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1 :=
  b1_geometry_unit_of_bounds hB1.h_squares_unit

/-- Wrapper: from `hB1.h_squares_unit`, derive `dist p q ≤ 3` for any two DSquares. -/
lemma b1_geometry_diam
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (hB1 : B1BridgeHypotheses k config) :
    ∀ (p q : DSquare k),
      p ∈ finsetDyadicToDSquare config.P₀ →
      q ∈ finsetDyadicToDSquare config.P₀ → dist p q ≤ 3 :=
  b1_geometry_diam_of_bounds hB1.h_squares_unit

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
