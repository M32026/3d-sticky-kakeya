module

/-
  B1BridgeHypotheses Construction

  Provides forward lemmas and conditional construction for
  `B1BridgeHypotheses`, the geometric boundedness data required by
  the B1 induction-on-scales bridge and the Prop73 combining theorem.

  Main results:
  - `strip_from_slope_bound_strict`: |T.slope| < 1 → a-index strip
  - `strip_from_slope_bound_nonstrict`: |T.slope| ≤ 1 → non-strict a bounds
  - `tube_card_bounded_from_index_bounds`: bounded a,b indices → card ≤ 12·16^n
  - `intercept_bound_from_geometry`: square containment + strip → |b| < 3·2^n
  - `construct_B1BridgeHypotheses_from_bounds`: full conditional construction

  Whiteprint node: combining_theorem_genuine / b1_bridge_construction
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion

/-! ### Slope bound → strip constraint -/

/-- From strict slope bound `|T.slope| < 1`, derive the strip constraint
    `-2^n ≤ T.a ∧ T.a < 2^n`.

    The reverse direction (strip → `|slope| ≤ 1`) is `slope_bound_from_b1`
    in `Section9/ExtraHypothesesConstruction.lean`. -/
lemma strip_from_slope_bound_strict {n : ℕ} (T : DyadicTube n)
    (h_slope : |T.slope| < 1) :
    -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := by
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδ_eq : dyadicDelta n = 1 / (2 ^ n : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring
  have h_slope_eq : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
  have h1 : |(T.a : ℝ)| * dyadicDelta n < 1 := by
    have h2 : |(T.a : ℝ) * dyadicDelta n| = |(T.a : ℝ)| * dyadicDelta n := by
      rw [abs_mul, abs_of_pos hδ_pos]
    rw [h_slope_eq] at h_slope
    rw [h2] at h_slope
    exact h_slope
  rw [hδ_eq] at h1
  have h4 : |(T.a : ℝ)| < (2 ^ n : ℝ) := by
    have h5 : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    have h6 : |(T.a : ℝ)| * (1 / (2 ^ n : ℝ)) < 1 := h1
    calc |(T.a : ℝ)|
      = |(T.a : ℝ)| * (1 / (2 ^ n : ℝ)) * (2 ^ n : ℝ) := by field_simp [h5.ne'] <;> ring
    _ < 1 * (2 ^ n : ℝ) := by gcongr
    _ = (2 ^ n : ℝ) := by ring
  have h4' : -(2 ^ n : ℝ) < (T.a : ℝ) ∧ (T.a : ℝ) < (2 ^ n : ℝ) := abs_lt.mp h4
  have h8 : -(2 ^ n : ℤ) ≤ T.a := by
    have h9 : -(2 ^ n : ℝ) < (T.a : ℝ) := h4'.1
    by_contra h10
    have h11 : T.a < -(2 ^ n : ℤ) := by omega
    have h12 : (T.a : ℝ) < -(2 ^ n : ℝ) := by exact_mod_cast h11
    linarith
  have h9 : T.a < (2 ^ n : ℤ) := by
    have h10 : (T.a : ℝ) < (2 ^ n : ℝ) := h4'.2
    exact_mod_cast h10
  exact ⟨h8, h9⟩

/-- From non-strict slope bound `|T.slope| ≤ 1`, derive `-2^n ≤ T.a ∧ T.a ≤ 2^n`.
    Note: this gives `T.a ≤ 2^n`, not `T.a < 2^n`. For the strict strip
    constraint required by `B1BridgeHypotheses`, use
    `strip_from_slope_bound_strict`. -/
lemma strip_from_slope_bound_nonstrict {n : ℕ} (T : DyadicTube n)
    (h_slope : |T.slope| ≤ 1) :
    -(2 ^ n : ℤ) ≤ T.a ∧ T.a ≤ (2 ^ n : ℤ) := by
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδ_eq : dyadicDelta n = 1 / (2 ^ n : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring
  have h_slope_eq : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
  have h1 : |(T.a : ℝ)| * dyadicDelta n ≤ 1 := by
    have h2 : |(T.a : ℝ) * dyadicDelta n| = |(T.a : ℝ)| * dyadicDelta n := by
      rw [abs_mul, abs_of_pos hδ_pos]
    rw [h_slope_eq] at h_slope
    rw [h2] at h_slope
    exact h_slope
  rw [hδ_eq] at h1
  have h3 : |(T.a : ℝ)| ≤ (2 ^ n : ℝ) := by
    have h4 : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    have h5 : |(T.a : ℝ)| * (1 / (2 ^ n : ℝ)) ≤ 1 := h1
    calc |(T.a : ℝ)|
      = |(T.a : ℝ)| * (1 / (2 ^ n : ℝ)) * (2 ^ n : ℝ) := by field_simp [h4.ne'] <;> ring
    _ ≤ 1 * (2 ^ n : ℝ) := by gcongr
    _ = (2 ^ n : ℝ) := by ring
  have h6 : -(2 ^ n : ℝ) ≤ (T.a : ℝ) := by linarith [abs_le.mp h3]
  have h7 : (T.a : ℝ) ≤ (2 ^ n : ℝ) := by linarith [abs_le.mp h3]
  exact ⟨by exact_mod_cast h6, by exact_mod_cast h7⟩

/-! ### Counting lemma for h_tubes_bounded -/

/-- Pure counting lemma: if all tubes in a finset have bounded slope index
    and intercept index, then the cardinality is at most `12 · 16^n`.

    Given:
    - `-2^n ≤ T.a < 2^n` (from strip constraint): at most `2·2^n` values
    - `|(T.b : ℝ)| < 3·2^n` (from geometric intercept bound): at most `6·2^n` values

    Total: `(2·2^n) · (6·2^n) = 12·4^n ≤ 12·16^n`. -/
lemma tube_card_bounded_from_index_bounds {n : ℕ} {T₀ : Finset (DyadicTube n)}
    (ha_bound : ∀ T ∈ T₀, -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (hb_bound : ∀ T ∈ T₀, |(T.b : ℝ)| < 3 * (2 ^ n : ℝ)) :
    T₀.card ≤ 12 * 16 ^ n := by
  let f : DyadicTube n → ℤ × ℤ := fun T => (T.a, T.b)
  have hf_inj : Set.InjOn f (T₀ : Set (DyadicTube n)) := by
    intro T1 _ T2 _ h
    have h1 : T1.a = T2.a := by simp [f] at h <;> tauto
    have h2 : T1.b = T2.b := by simp [f] at h <;> tauto
    cases T1 <;> cases T2 <;> simp_all

  let A : Finset ℤ := Finset.Ico (-(2 ^ n)) (2 ^ n)
  let B : Finset ℤ := Finset.Ico (-(3 * 2 ^ n)) (3 * 2 ^ n)

  have hA_card : A.card = 2 * 2 ^ n := by
    have h : (A.card : ℤ) = (2 ^ n : ℤ) - (-(2 ^ n : ℤ)) := Int.card_Ico_of_le _ _ (by norm_num)
    have h2 : (A.card : ℤ) = 2 * (2 ^ n : ℤ) := by rw [h] <;> ring
    exact_mod_cast h2

  have hB_card : B.card = 6 * 2 ^ n := by
    have h : (B.card : ℤ) = (3 * (2 ^ n : ℤ)) - (-(3 * (2 ^ n : ℤ))) := Int.card_Ico_of_le _ _ (by norm_num)
    have h2 : (B.card : ℤ) = 6 * (2 ^ n : ℤ) := by rw [h] <;> ring
    exact_mod_cast h2

  have h_image_subset : (T₀.image f) ⊆ A ×ˢ B := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨T, hT, rfl⟩
    have ha1 : -(2 ^ n : ℤ) ≤ T.a := (ha_bound T hT).1
    have ha2 : T.a < (2 ^ n : ℤ) := (ha_bound T hT).2
    have hb : |(T.b : ℝ)| < 3 * (2 ^ n : ℝ) := hb_bound T hT
    have hb1 : -(3 * (2 ^ n : ℤ)) ≤ T.b := by
      have h : -(3 * (2 ^ n : ℝ)) < (T.b : ℝ) := (abs_lt.mp hb).1
      have h' : -(3 * (2 ^ n : ℤ)) < T.b := by exact_mod_cast h
      omega
    have hb2 : T.b < 3 * (2 ^ n : ℤ) := by
      have h : (T.b : ℝ) < 3 * (2 ^ n : ℝ) := (abs_lt.mp hb).2
      exact_mod_cast h
    simp only [Finset.mem_product, A, B, Finset.mem_Ico]
    exact ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩

  have h_card_product : (A ×ˢ B).card = A.card * B.card := by
    rw [Finset.card_product]

  have h_main : T₀.card = (T₀.image f).card := by
    rw [Finset.card_image_of_injOn hf_inj]

  have h_pow : (2 ^ n : ℝ) * (2 ^ n : ℝ) = 4 ^ n := by
    have h1 : (2 ^ n : ℝ) * (2 ^ n : ℝ) = (2 : ℝ) ^ (n + n) := by
      rw [← pow_add] <;> ring
    have h2 : n + n = 2 * n := by ring
    rw [h1, h2]
    have h3 : (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ 2) ^ n := by
      rw [pow_mul] <;> ring
    rw [h3] <;> norm_num

  have h_final : (T₀.image f).card ≤ 12 * 16 ^ n := by
    calc (T₀.image f).card
      ≤ (A ×ˢ B).card := Finset.card_le_card h_image_subset
    _ = A.card * B.card := h_card_product
    _ = (2 * 2 ^ n) * (6 * 2 ^ n) := by rw [hA_card, hB_card]
    _ = 12 * 4 ^ n := by
      have h_goal : ((2 : ℝ) * (2 ^ n : ℝ)) * ((6 : ℝ) * (2 ^ n : ℝ)) = (12 : ℝ) * (4 ^ n : ℝ) := by
        calc ((2 : ℝ) * (2 ^ n : ℝ)) * ((6 : ℝ) * (2 ^ n : ℝ))
          = (12 : ℝ) * ((2 ^ n : ℝ) * (2 ^ n : ℝ)) := by ring
        _ = (12 : ℝ) * (4 ^ n : ℝ) := by rw [h_pow] <;> ring
      exact_mod_cast h_goal
    _ ≤ 12 * 16 ^ n := by
      have h : 4 ^ n ≤ 16 ^ n := by gcongr <;> norm_num
      nlinarith

  rw [h_main]
  exact h_final

/-! ### Geometric intercept bound -/

/-- From `h_squares_unit`, `h_tubes_strip`, and the assumption that every
    tube in `T₀` intersects some square in `P₀`, derive the intercept index
    bound `|(T.b : ℝ)| < 3 · 2^n`.

    Proof sketch:
    - Pick `x ∈ T.toSet ∩ p.toSet`. By `h_squares_unit`, `x₀, x₁ ∈ [0, 1)`.
    - By `h_tubes_strip`, `|T.slope| ≤ 1`.
    - Tube equation: `|x₁ - T.slope·x₀ - T.intercept| ≤ δ_n`.
    - This gives `T.intercept ∈ (-1 - δ_n, 2 + δ_n)`.
    - Since `δ_n ≤ 1`, `|T.intercept| < 3`.
    - Since `T.intercept = T.b · δ_n`, we get `|T.b| < 3 / δ_n = 3 · 2^n`. -/
lemma intercept_bound_from_geometry {n : ℕ} {s C : ℝ} {M : ℕ}
    {config : NiceConfiguration n s C M}
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ))
    (h_tubes_strip : ∀ T ∈ config.T₀, -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (hT0_intersects : ∀ T ∈ config.T₀,
      ∃ (p : DyadicSquare n), p ∈ config.P₀ ∧ (T.toSet ∩ p.toSet).Nonempty) :
    ∀ T ∈ config.T₀, |(T.b : ℝ)| < 3 * (2 ^ n : ℝ) := by
  intro T hT
  rcases hT0_intersects T hT with ⟨p, hp, ⟨x, hxT, hxp⟩⟩
  have h_bounds := h_squares_unit p hp
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδ_le_one : dyadicDelta n ≤ 1 := dyadicDelta_le_one n
  have hδ_eq : dyadicDelta n = 1 / (2 ^ n : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring

  have hx0_ge : 0 ≤ x 0 := by
    have h : (p.i : ℝ) * dyadicDelta n ≤ x 0 := hxp.1
    have h_i0 : 0 ≤ (p.i : ℝ) := by exact_mod_cast h_bounds.1
    nlinarith
  have hx0_lt : x 0 < 1 := by
    have h : x 0 < ((p.i : ℝ) + 1) * dyadicDelta n := hxp.2.1
    have h_i1 : (p.i : ℝ) + 1 ≤ (2 ^ n : ℝ) := by
      have h' : p.i + 1 ≤ (2 ^ n : ℤ) := by omega
      exact_mod_cast h'
    have h2 : ((p.i : ℝ) + 1) * dyadicDelta n ≤ 1 := by
      rw [hδ_eq]
      have hpos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
      have h3 : ((p.i : ℝ) + 1) * (1 / (2 ^ n : ℝ)) ≤ 1 := by
        calc ((p.i : ℝ) + 1) * (1 / (2 ^ n : ℝ))
          ≤ (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) := by gcongr
        _ = 1 := by field_simp [hpos.ne'] <;> ring
      exact h3
    linarith
  have hx1_ge : 0 ≤ x 1 := by
    have h : (p.j : ℝ) * dyadicDelta n ≤ x 1 := hxp.2.2.1
    have h_j0 : 0 ≤ (p.j : ℝ) := by exact_mod_cast h_bounds.2.2.1
    nlinarith
  have hx1_lt : x 1 < 1 := by
    have h : x 1 < ((p.j : ℝ) + 1) * dyadicDelta n := hxp.2.2.2
    have h_j1 : (p.j : ℝ) + 1 ≤ (2 ^ n : ℝ) := by
      have h' : p.j + 1 ≤ (2 ^ n : ℤ) := by omega
      exact_mod_cast h'
    have h2 : ((p.j : ℝ) + 1) * dyadicDelta n ≤ 1 := by
      rw [hδ_eq]
      have hpos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
      have h3 : ((p.j : ℝ) + 1) * (1 / (2 ^ n : ℝ)) ≤ 1 := by
        calc ((p.j : ℝ) + 1) * (1 / (2 ^ n : ℝ))
          ≤ (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) := by gcongr
        _ = 1 := by field_simp [hpos.ne'] <;> ring
      exact h3
    linarith

  have h_slope_le_one : |T.slope| ≤ 1 := by
    have h_strip := h_tubes_strip T hT
    have h1 : -(2 ^ n : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h_strip.1
    have h2 : (T.a : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h_strip.2
    have h3 : |(T.a : ℝ)| ≤ (2 ^ n : ℝ) := by
      rw [abs_le] <;> constructor <;> linarith
    have h4 : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
    rw [h4, hδ_eq]
    have h5 : |(T.a : ℝ) * (1 / (2 ^ n : ℝ))| = |(T.a : ℝ)| * (1 / (2 ^ n : ℝ)) := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / (2 ^ n : ℝ) by positivity)]
    rw [h5]
    have h6 : |(T.a : ℝ)| * (1 / (2 ^ n : ℝ)) ≤ 1 := by
      have hpos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
      calc |(T.a : ℝ)| * (1 / (2 ^ n : ℝ))
        ≤ (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) := by gcongr
      _ = 1 := by field_simp [hpos.ne'] <;> ring
    exact h6

  have h_slope_ge_neg_one : -1 ≤ T.slope := by linarith [abs_le.mp h_slope_le_one]

  have h_slope_x0_ge : -1 ≤ T.slope * x 0 := by
    have h : T.slope * x 0 ≥ (-1 : ℝ) * x 0 := by
      exact mul_le_mul_of_nonneg_right h_slope_ge_neg_one (by linarith)
    have h2 : (-1 : ℝ) * x 0 ≥ -1 := by linarith
    linarith

  have h_slope_x0_lt_one : T.slope * x 0 < 1 := by
    by_cases h : T.slope ≤ 0
    · have h' : T.slope * x 0 ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg h (by linarith)
      linarith
    · have h_pos : 0 < T.slope := by linarith
      have h' : T.slope * x 0 < T.slope * 1 := by
        exact mul_lt_mul_of_pos_left hx0_lt h_pos
      have h'' : T.slope * 1 ≤ 1 := by
        have h_slope_le : T.slope ≤ 1 := by linarith [abs_le.mp h_slope_le_one]
        linarith
      linarith

  have h_eq : |x 1 - T.slope * x 0 - T.intercept| ≤ dyadicDelta n := hxT

  have h_intercept_lower : T.intercept > -1 - dyadicDelta n := by
    have h : x 1 - T.slope * x 0 - T.intercept ≤ dyadicDelta n := by
      calc x 1 - T.slope * x 0 - T.intercept
        ≤ |x 1 - T.slope * x 0 - T.intercept| := le_abs_self _
      _ ≤ dyadicDelta n := h_eq
    have h2 : x 1 - T.slope * x 0 > -1 := by linarith [hx1_ge, h_slope_x0_lt_one]
    linarith

  have h_intercept_upper : T.intercept < 2 + dyadicDelta n := by
    have h_abs : -(x 1 - T.slope * x 0 - T.intercept) ≤ |x 1 - T.slope * x 0 - T.intercept| := by
      have h4 : -|x 1 - T.slope * x 0 - T.intercept| ≤ x 1 - T.slope * x 0 - T.intercept := neg_abs_le _
      linarith
    have h : -(x 1 - T.slope * x 0 - T.intercept) ≤ dyadicDelta n := by
      calc -(x 1 - T.slope * x 0 - T.intercept)
        ≤ |x 1 - T.slope * x 0 - T.intercept| := h_abs
      _ ≤ dyadicDelta n := h_eq
    have h2 : T.intercept ≤ dyadicDelta n + x 1 - T.slope * x 0 := by linarith
    have h3 : T.intercept < dyadicDelta n + 2 := by linarith [hx1_lt, h_slope_x0_ge]
    have h4 : T.intercept < 2 + dyadicDelta n := by linarith
    exact h4

  have h_intercept_abs : |T.intercept| < 3 := by
    rw [abs_lt] <;> constructor <;> linarith [hδ_le_one]

  have h_b_abs : |(T.b : ℝ)| * dyadicDelta n < 3 := by
    have h_eq2 : T.intercept = (T.b : ℝ) * dyadicDelta n := by rfl
    have h_abs_mul : |T.intercept| = |(T.b : ℝ)| * dyadicDelta n := by
      rw [h_eq2, abs_mul, abs_of_pos hδ_pos]
    rw [h_abs_mul] at h_intercept_abs
    exact h_intercept_abs

  rw [hδ_eq] at h_b_abs
  have hpos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have h_final : |(T.b : ℝ)| < 3 * (2 ^ n : ℝ) := by
    calc |(T.b : ℝ)|
      = |(T.b : ℝ)| * (1 / (2 ^ n : ℝ)) * (2 ^ n : ℝ) := by field_simp [hpos.ne'] <;> ring
    _ < 3 * (2 ^ n : ℝ) := by
      have h : |(T.b : ℝ)| * (1 / (2 ^ n : ℝ)) < 3 := h_b_abs
      nlinarith
  exact h_final

/-! ### Full conditional construction -/

namespace DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- Conditional construction of `B1BridgeHypotheses` from explicit geometric bounds.

    Given:
    1. `config.pointSet ⊆ [0,1]²` → `h_squares_unit`
       (via existing `squares_unit_from_pointSet_bounded`)
    2. `∀ T ∈ config.T₀, |T.slope| < 1` → `h_tubes_strip`
       (via `strip_from_slope_bound_strict`)
    3. Every tube intersects some `P₀` square → intercept bound → `h_tubes_bounded`
       (via `intercept_bound_from_geometry` + `tube_card_bounded_from_index_bounds`)

    The hard part is obtaining these three hypotheses from the source data.
    In particular, the point-set normalization to `[0,1]²` and the slope
    bound must be established by the front-end extraction. -/
lemma construct_B1BridgeHypotheses_from_bounds
    {n : ℕ} {s C : ℝ} {M : ℕ}
    {config : NiceConfiguration n s C M}
    (h_pointSet_unit : config.pointSet ⊆
      {p : EuclideanPlane | p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1})
    (h_slopes_bounded : ∀ (T : DyadicTube n), T ∈ config.T₀ → |T.slope| < 1)
    (hT0_intersects : ∀ T ∈ config.T₀,
      ∃ (p : DyadicSquare n), p ∈ config.P₀ ∧ (T.toSet ∩ p.toSet).Nonempty) :
    B1BridgeHypotheses n config := by

  have h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ) :=
    squares_unit_from_pointSet_bounded h_pointSet_unit

  have h_tubes_strip : ∀ (T : DyadicTube n), T ∈ config.T₀ →
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := by
    intro T hT
    have h_slope : |T.slope| < 1 := h_slopes_bounded T hT
    exact strip_from_slope_bound_strict T h_slope

  have h_b_bound : ∀ T ∈ config.T₀, |(T.b : ℝ)| < 3 * (2 ^ n : ℝ) :=
    intercept_bound_from_geometry h_squares_unit h_tubes_strip hT0_intersects

  have h_tubes_bounded : config.T₀.card ≤ 12 * 16 ^ n :=
    tube_card_bounded_from_index_bounds h_tubes_strip h_b_bound

  exact {
    h_squares_unit := h_squares_unit
    h_tubes_strip := h_tubes_strip
    h_tubes_bounded := h_tubes_bounded
  }

end DirecretisedFurstenbergEstimate.FormatConversion.M2
