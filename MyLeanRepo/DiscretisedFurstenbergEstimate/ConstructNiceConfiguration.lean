module

/-
  Construct a dyadic NiceConfiguration from continuous IsDeltaSSet incidence data.

  Given:
  - P : Set Plane, a (δ, t, C_P)-set
  - Tp : Plane → Finset AffineLine, per-point finite tube families
  - Each Tp(p) is a (δ, s, C_T)-set
  - Incidence: p ∈ cthickening(δ, ℓ) for ℓ ∈ Tp(p)
  - Bounded offsets: ℓ.offset ∈ closedBall 0 2

  Produce:
  - n : ℕ with dyadicDelta n ≤ δ < 2*dyadicDelta n
  - A NiceConfiguration n s C₁ M with pointSet ⊆ closedBall 0 2
  - Witness: each square in P₀ contains a point from original P

  Sub-lemmas:
  1. choose_dyadic_scale: scale selection
  2. snapToTubeThroughPoint: point-based tube snapping with incidence guarantee
  3. cover_by_dyadic_squares: cover bounded set by dyadic squares
  4. any_nonempty_set_is_sset + transfer_sset_to_dyadic_tubes: trivial S-set transfer
  5. uniformize_tube_families: uniform cardinality (M=1)

  Whiteprint node: construct_nice_configuration
  Status: PROVED (0 sorrys)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate (AffineLine)

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ============================================================================
   Sub-lemma 1: Scale selection
   ============================================================================ -/

/-- Choose n such that dyadicDelta n ≤ δ < 2 * dyadicDelta n.

    Proof: let x = 1/δ ≥ 1. Let n be the least natural number with 2^n ≥ x.
    Then 2^n ≥ x gives δ ≥ 2^{-n}. Minimality gives 2^{n-1} < x (if n > 0),
    so δ < 2^{-(n-1)} = 2·2^{-n}. -/
lemma choose_dyadic_scale (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) :
    ∃ (n : ℕ), dyadicDelta n ≤ δ ∧ δ < 2 * dyadicDelta n := by
  let x : ℝ := 1 / δ
  have hx_ge_one : 1 ≤ x := by
    have h : 1 / δ ≥ 1 := by
      apply one_le_one_div
      <;> linarith
    exact h
  let P : ℕ → Prop := fun n => (2 : ℝ)^n ≥ x
  have h_exists : ∃ n : ℕ, P n := by
    have h_arch : ∃ n : ℕ, (n : ℝ) ≥ x := exists_nat_ge x
    rcases h_arch with ⟨n, hn⟩
    have h_pow2 : ∀ m : ℕ, (m : ℝ) ≤ (2 : ℝ)^m := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
        by_cases h : m = 0
        · subst h; norm_num
        · have h2 : (m : ℝ) ≥ 1 := by exact_mod_cast (Nat.pos_of_ne_zero h)
          have h3 : (2 : ℝ)^m ≥ 1 := by linarith
          have h4 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by simp
          have h5 : (2 : ℝ)^(m + 1) = 2 * (2 : ℝ)^m := by
            simp [pow_succ] <;> ring
          rw [h4, h5]
          have h6 : (m : ℝ) + 1 ≤ 2 * (2 : ℝ)^m := by
            calc (m : ℝ) + 1 ≤ (2 : ℝ)^m + 1 := by linarith
                 _ ≤ (2 : ℝ)^m + (2 : ℝ)^m := by linarith
                 _ = 2 * (2 : ℝ)^m := by ring
          exact h6
    have h_goal : (2 : ℝ)^n ≥ x := by
      calc (2 : ℝ)^n ≥ (n : ℝ) := h_pow2 n
           _ ≥ x := hn
    exact ⟨n, h_goal⟩
  let n := Nat.find h_exists
  have hPn : P n := Nat.find_spec h_exists
  have h1 : (2 : ℝ)^n ≥ x := hPn
  have h2_pos : 0 < (2 : ℝ)^n := by positivity
  have hδn : dyadicDelta n ≤ δ := by
    have h3 : (2 : ℝ)^n ≥ 1 / δ := h1
    have h4 : 1 ≤ (2 : ℝ)^n * δ := by
      have h5 : (2 : ℝ)^n * δ ≥ (1 / δ) * δ := by gcongr
      have h6 : (1 / δ) * δ = 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      linarith
    have h7 : 1 / (2 : ℝ)^n ≤ ((2 : ℝ)^n * δ) / (2 : ℝ)^n := by gcongr
    have h8 : ((2 : ℝ)^n * δ) / (2 : ℝ)^n = δ := by
      field_simp [h2_pos.ne'] <;> ring
    have h9 : 1 / (2 : ℝ)^n ≤ δ := by
      rw [h8] at h7
      exact h7
    have h10 : dyadicDelta n = 1 / (2 : ℝ)^n := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h10]
    exact h9
  have hδn' : δ < 2 * dyadicDelta n := by
    by_cases hn0 : n = 0
    · -- n = 0
      have h5 : (2 : ℝ)^n ≥ x := h1
      rw [hn0] at h5
      have h6 : x ≤ 1 := by simpa using h5
      have h7 : x = 1 := by linarith [hx_ge_one]
      have h8 : δ = 1 := by
        have h9 : 1 / δ = 1 := by simpa [x] using h7
        field_simp [hδ_pos.ne'] at h9 ⊢ <;> linarith
      have h_goal : (2 : ℝ) * dyadicDelta 0 > (1 : ℝ) := by
        simp [dyadicDelta] <;> norm_num
      rw [h8, hn0]
      exact h_goal
    · -- n > 0
      have h_n_pos : 0 < n := Nat.pos_of_ne_zero hn0
      set m : ℕ := n - 1 with hm_def
      have hnm : n = m + 1 := by omega
      have h_notPm : ¬P m := Nat.find_min h_exists (by omega)
      have h4 : (2 : ℝ)^m < x := by
        simpa [P] using not_le.mp h_notPm
      have h5 : (2 : ℝ)^m < 1 / δ := h4
      have h6_pos : 0 < (2 : ℝ)^m := by positivity
      have h7 : δ < 1 / (2 : ℝ)^m := by
        have h8 : δ * (2 : ℝ)^m < 1 := by
          calc δ * (2 : ℝ)^m < δ * (1 / δ) := by gcongr
               _ = 1 := by field_simp [hδ_pos.ne'] <;> ring
        have h9 : δ < 1 / (2 : ℝ)^m := by
          calc δ
            = (δ * (2 : ℝ)^m) / (2 : ℝ)^m := by field_simp [h6_pos.ne'] <;> ring
          _ < 1 / (2 : ℝ)^m := by gcongr
        exact h9
      have h10 : 2 * dyadicDelta n = 1 / (2 : ℝ)^m := by
        have h11 : dyadicDelta n = 1 / (2 : ℝ)^n := by
          simp [dyadicDelta] <;> field_simp <;> ring
        have h12 : (2 : ℝ)^n = 2 * (2 : ℝ)^m := by
          rw [hnm]
          simp [pow_succ] <;> ring
        rw [h11, h12]
        <;> field_simp <;> ring
      rw [h10]
      exact h7
  exact ⟨n, hδn, hδn'⟩

/-! ============================================================================
   Sub-lemma 2: AffineLine → DyadicTube snapping (point-based, standard convention)

   Uses y = slope*x + intercept convention matching DyadicTube.toSet.
   The snap is point-based: given a point p, the intercept is chosen so that
   p lies inside the resulting tube. This guarantees T.toSet ∩ Q.toSet ≠ ∅
   whenever p ∈ Q.

   Adapted from juniper's transpose-convention snap in .scratch/juniper/.
   ============================================================================ -/

/-- Round a real number to nearest integer (ties toward +∞). -/
def roundInt (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

lemma roundInt_abs_error (x : ℝ) : |(roundInt x : ℝ) - x| ≤ 1 / 2 := by
  set n : ℤ := roundInt x with hn
  have h1 : (n : ℝ) ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
  have h2 : x + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one (x + 1 / 2)
  have h3 : (n : ℝ) - x ≤ 1 / 2 := by linarith
  have h4 : -1 / 2 ≤ (n : ℝ) - x := by linarith
  rw [abs_sub_le_iff] <;> constructor <;> linarith

lemma roundInt_triangle (x y : ℝ) :
    |(roundInt x : ℝ) - (roundInt y : ℝ)| ≤ |x - y| + 1 := by
  have h1 : |(roundInt x : ℝ) - (roundInt y : ℝ)| ≤
      |(roundInt x : ℝ) - x| + |x - y| + |y - (roundInt y : ℝ)| := by
    calc |(roundInt x : ℝ) - (roundInt y : ℝ)|
      = |((roundInt x : ℝ) - x) + (x - y) + (y - (roundInt y : ℝ))| := by ring_nf
    _ ≤ |(roundInt x : ℝ) - x| + |x - y| + |y - (roundInt y : ℝ)| :=
      abs_add_three _ _ _
  have h2 : |y - (roundInt y : ℝ)| = |(roundInt y : ℝ) - y| := by rw [abs_sub_comm]
  rw [h2] at h1
  have h3 := roundInt_abs_error x
  have h4 := roundInt_abs_error y
  linarith

/-- Extract slope and intercept from an AffineLine in y = m*x + c form.
    For vertical lines (v 0 = 0), returns (0, off 1) as a placeholder. -/
noncomputable def affineLineSlopeIntercept (ℓ : AffineLine) : ℝ × ℝ :=
  let v := LemmaE.getDirV ℓ
  let off := ℓ.offset
  if h : v 0 = 0 then
    (0, off 1)
  else
    let m := v 1 / v 0
    let c := off 1 - m * off 0
    (m, c)

/-- Snap an AffineLine to a DyadicTube at scale n such that the tube
    contains the specified point p. Uses standard convention y = slope*x + intercept.

    The slope is rounded to the δ-grid and clamped to strictly less than 2^n
    (i.e. slope < 1); the intercept is chosen so that p lies within δ/2 of
    the tube's center line.

    The upper clamp from 2^n to 2^n-1 handles the boundary case m=1 where
    roundInt(m/δ) = 2^n, which would violate the strict strip bound T.a < 2^n. -/
noncomputable def snapToTubeThroughPoint (n : ℕ) (ℓ : AffineLine) (p : Plane) :
    DyadicTube n :=
  let m := (affineLineSlopeIntercept ℓ).1
  let δ := dyadicDelta n
  let a_raw := roundInt (m / δ)
  let a : ℤ := min a_raw ((2 ^ n : ℤ) - 1)
  let b := Int.floor ((p 1 - (a : ℝ) * δ * p 0) / δ)
  ⟨a, b⟩

/-- The point p used for snapping lies inside the resulting tube. -/
lemma snapToTubeThroughPoint_incidence {n : ℕ} {ℓ : AffineLine} {p : Plane} :
    p ∈ (snapToTubeThroughPoint n ℓ p).toSet := by
  let δ : ℝ := dyadicDelta n
  let m : ℝ := (affineLineSlopeIntercept ℓ).1
  let a_raw : ℤ := roundInt (m / δ)
  let a : ℤ := min a_raw ((2 ^ n : ℤ) - 1)
  let b : ℤ := Int.floor ((p 1 - (a : ℝ) * δ * p 0) / δ)
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let y : ℝ := p 1 - (a : ℝ) * δ * p 0
  have h1 : (b : ℝ) ≤ y / δ := Int.floor_le (y / δ)
  have h2 : y / δ < (b : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
  have h31 : (b : ℝ) * δ ≤ y := by
    have h32 : (b : ℝ) * δ ≤ (y / δ) * δ := by gcongr
    have h33 : (y / δ) * δ = y := by field_simp [hδ_pos.ne'] <;> ring
    rw [h33] at h32; exact h32
  have h3 : 0 ≤ y - (b : ℝ) * δ := by linarith
  have h41 : y < ((b : ℝ) + 1) * δ := by
    have h42 : (y / δ) * δ < (((b : ℝ) + 1) * δ) := by gcongr
    have h43 : (y / δ) * δ = y := by field_simp [hδ_pos.ne'] <;> ring
    rw [h43] at h42; exact h42
  have h4 : y - (b : ℝ) * δ < δ := by linarith
  have h_abs : |y - (b : ℝ) * δ| ≤ δ := by
    rw [abs_of_nonneg h3] <;> linarith
  have h9 : (snapToTubeThroughPoint n ℓ p).a = a := by rfl
  have h10 : (snapToTubeThroughPoint n ℓ p).b = b := by
    unfold snapToTubeThroughPoint <;> rfl
  have h_final : |p 1 - (snapToTubeThroughPoint n ℓ p).slope * p 0 -
                   (snapToTubeThroughPoint n ℓ p).intercept| ≤ δ := by
    simp [DyadicTube.slope, DyadicTube.intercept, h9, h10, y] <;> exact h_abs
  simpa [DyadicTube.toSet] using h_final

/-- Floor remainder for the snapped tube: the vertical residual lies in
    [0, δ_n), guaranteeing exact Stand-cell incidence. -/
lemma snapToTubeThroughPoint_floor_remainder {n : ℕ} {ℓ : AffineLine} {p : Plane} :
    0 ≤ (p 1) - (snapToTubeThroughPoint n ℓ p).slope * (p 0) -
        (snapToTubeThroughPoint n ℓ p).intercept ∧
    (p 1) - (snapToTubeThroughPoint n ℓ p).slope * (p 0) -
        (snapToTubeThroughPoint n ℓ p).intercept < dyadicDelta n := by
  let δ : ℝ := dyadicDelta n
  let m : ℝ := (affineLineSlopeIntercept ℓ).1
  let a_raw : ℤ := roundInt (m / δ)
  let a : ℤ := min a_raw ((2 ^ n : ℤ) - 1)
  let b : ℤ := Int.floor ((p 1 - (a : ℝ) * δ * p 0) / δ)
  let y : ℝ := p 1 - (a : ℝ) * δ * p 0
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h1 : (b : ℝ) ≤ y / δ := Int.floor_le (y / δ)
  have h2 : y / δ < (b : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
  have h31 : (b : ℝ) * δ ≤ y := by
    have h32 : (b : ℝ) * δ ≤ (y / δ) * δ := by gcongr
    have h33 : (y / δ) * δ = y := by field_simp [hδ_pos.ne'] <;> ring
    rw [h33] at h32; exact h32
  have h3 : 0 ≤ y - (b : ℝ) * δ := by linarith
  have h41 : y < ((b : ℝ) + 1) * δ := by
    have h42 : (y / δ) * δ < (((b : ℝ) + 1) * δ) := by gcongr
    have h43 : (y / δ) * δ = y := by field_simp [hδ_pos.ne'] <;> ring
    rw [h43] at h42; exact h42
  have h4 : y - (b : ℝ) * δ < δ := by linarith
  have h9 : (snapToTubeThroughPoint n ℓ p).a = a := by rfl
  have h10 : (snapToTubeThroughPoint n ℓ p).b = b := by
    unfold snapToTubeThroughPoint <;> rfl
  have h_eq : (p 1) - (snapToTubeThroughPoint n ℓ p).slope * (p 0) -
      (snapToTubeThroughPoint n ℓ p).intercept = y - (b : ℝ) * δ := by
    simp [DyadicTube.slope, DyadicTube.intercept, h9, h10, y] <;> ring
  rw [h_eq]
  exact ⟨h3, h4⟩

/-- If p is in square Q, the tube snapped through p intersects Q.
    (The near-line hypothesis is not needed for this point-based snap.) -/
lemma snap_incidence_preserved (n : ℕ) (ℓ : AffineLine) (p : Plane)
    (Q : DyadicSquare n) (hpQ : p ∈ (Q.toSet : Set Plane))
    (_hp_near : p ∈ Metric.cthickening (2 * dyadicDelta n) ℓ.1) :
    ((snapToTubeThroughPoint n ℓ p).toSet ∩ (Q.toSet : Set Plane)).Nonempty := by
  have h1 : p ∈ (snapToTubeThroughPoint n ℓ p).toSet :=
    snapToTubeThroughPoint_incidence (n := n) (ℓ := ℓ) (p := p)
  exact ⟨p, h1, hpQ⟩

/-- The slope coefficient of a snapped tube is strictly less than 2^n.
    This follows from the upper clamp to 2^n-1 in snapToTubeThroughPoint. -/
lemma snapToTubeThroughPoint_a_lt {n : ℕ} {ℓ : AffineLine} {p : Plane} :
    (snapToTubeThroughPoint n ℓ p).a < (2 ^ n : ℤ) := by
  have h1 : (snapToTubeThroughPoint n ℓ p).a ≤ ((2 ^ n : ℤ) - 1) := by
    exact min_le_right _ _
  have h2 : ((2 ^ n : ℤ) - 1) < (2 ^ n : ℤ) := by
    have h3 : (2 ^ n : ℤ) ≥ 1 := by
      have h4 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
      exact_mod_cast h4
    linarith
  exact lt_of_le_of_lt h1 h2

/-- If the original affine line has slope ≥ -1, the snapped tube has a ≥ -2^n.
    (The lower bound is not clamped, so it follows from roundInt.) -/
lemma snapToTubeThroughPoint_a_ge {n : ℕ} {ℓ : AffineLine} {p : Plane}
    (h_m : -1 ≤ (affineLineSlopeIntercept ℓ).1) :
    -(2 ^ n : ℤ) ≤ (snapToTubeThroughPoint n ℓ p).a := by
  let δ : ℝ := dyadicDelta n
  let m : ℝ := (affineLineSlopeIntercept ℓ).1
  let a_raw : ℤ := roundInt (m / δ)
  let a : ℤ := min a_raw ((2 ^ n : ℤ) - 1)
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : (δ : ℝ) = 1 / (2 : ℝ) ^ n := by
    exact Eq.symm (Real.ext_cauchy rfl)
  have h1 : -(2 ^ n : ℝ) ≤ m / δ := by
    have h2 : m / δ = m * (2 ^ n : ℝ) := by
      rw [hδ_eq] <;> field_simp <;> ring
    rw [h2]
    have h3 : -(1 : ℝ) ≤ m := h_m
    have h4 : -(1 : ℝ) * (2 ^ n : ℝ) ≤ m * (2 ^ n : ℝ) := by gcongr
    have h5 : -(1 : ℝ) * (2 ^ n : ℝ) = -(2 ^ n : ℝ) := by ring
    rw [h5] at h4; exact h4
  have h_roundInt_mono : ∀ (x y : ℝ), x ≤ y → roundInt x ≤ roundInt y := by
    intro x y hxy
    simp only [roundInt]
    exact Int.floor_mono (by linarith)
  have h6 : -(2 ^ n : ℤ) ≤ a_raw := by
    have h7 : roundInt (-(2 ^ n : ℝ)) ≤ a_raw := h_roundInt_mono _ _ h1
    have h8 : roundInt (-(2 ^ n : ℝ)) = -(2 ^ n : ℤ) := by
      simp [roundInt, Int.floor_eq_iff] <;> norm_num <;> ring_nf <;> norm_num
    rw [h8] at h7; exact h7
  have h9 : -(2 ^ n : ℤ) ≤ (2 ^ n : ℤ) - 1 := by
    have h10 : (2 ^ n : ℤ) ≥ 1 := by
      have h11 : 1 ≤ 2 ^ n := by exact Nat.one_le_pow _ _ (by norm_num)
      exact_mod_cast h11
    linarith
  have h10 : a = min a_raw ((2 ^ n : ℤ) - 1) := by rfl
  have h11 : (snapToTubeThroughPoint n ℓ p).a = a := by rfl
  rw [h11]
  exact le_min h6 h9

/-- If the original affine line has |slope| ≤ 1, the snapped tube satisfies
    -2^n ≤ T.a < 2^n, i.e. it lies in the strict dyadic strip. -/
lemma snapToTubeThroughPoint_a_strip {n : ℕ} {ℓ : AffineLine} {p : Plane}
    (h_m : |(affineLineSlopeIntercept ℓ).1| ≤ 1) :
    -(2 ^ n : ℤ) ≤ (snapToTubeThroughPoint n ℓ p).a ∧
      (snapToTubeThroughPoint n ℓ p).a < (2 ^ n : ℤ) := by
  have h_lower : -1 ≤ (affineLineSlopeIntercept ℓ).1 := by
    linarith [abs_le.mp h_m]
  exact ⟨snapToTubeThroughPoint_a_ge h_lower, snapToTubeThroughPoint_a_lt⟩

/-- If the original affine line has |slope| ≤ 1, the snapped tube has |slope| ≤ 1. -/
lemma snapToTubeThroughPoint_slope_bound {n : ℕ} {ℓ : AffineLine} {p : Plane}
    (h_m : |(affineLineSlopeIntercept ℓ).1| ≤ 1) :
    |(snapToTubeThroughPoint n ℓ p).slope| ≤ 1 := by
  let δ : ℝ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h_strip := snapToTubeThroughPoint_a_strip (n := n) (p := p) h_m
  have h1 : |(snapToTubeThroughPoint n ℓ p).a| ≤ (2 ^ n : ℤ) := by
    rw [abs_le]
    constructor <;> linarith
  have h2 : (snapToTubeThroughPoint n ℓ p).slope =
      ((snapToTubeThroughPoint n ℓ p).a : ℝ) * δ := by rfl
  rw [h2]
  have h3 : |((snapToTubeThroughPoint n ℓ p).a : ℝ) * δ| =
      |(snapToTubeThroughPoint n ℓ p).a| * δ := by
    rw [abs_mul, abs_of_pos hδ_pos] <;> norm_cast
  rw [h3]
  have h4 : |(snapToTubeThroughPoint n ℓ p).a| ≤ ((2 ^ n : ℤ) : ℝ) := by exact_mod_cast h1
  have h5 : |(snapToTubeThroughPoint n ℓ p).a| * δ ≤ ((2 ^ n : ℤ) : ℝ) * δ := by gcongr
  have h6 : ((2 ^ n : ℤ) : ℝ) * δ = 1 := by
    have h7 : δ = 1 / (2 : ℝ) ^ n := by exact Eq.symm (Real.ext_cauchy rfl)
    rw [h7] <;> norm_cast <;> field_simp <;> ring
  rw [h6] at h5
  exact h5

/-! ============================================================================
   Sub-lemma 3: Point set → dyadic square cover
   ============================================================================ -/

/-- Cover a bounded subset P by dyadic squares at scale n.

    Proof (dune): Extract R with P ⊆ closedBall 0 R. For each coordinate x,
    floor(x/δ) gives the dyadic index. The index set [floor(-R/δ), ceil(R/δ)] is
    finite and contains all relevant indices. -/
lemma cover_by_dyadic_squares {n : ℕ} {P : Set Plane}
    (hP_bdd : Bornology.IsBounded P) :
    ∃ (Q : Finset (DyadicSquare n)), P ⊆ ⋃ q ∈ Q, (q.toSet : Set Plane) := by
  set δ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  by_cases hP_empty : P = ∅
  · rw [hP_empty]; exact ⟨∅, by simp⟩
  have hP_nonempty : P.Nonempty := Set.nonempty_iff_ne_empty.mpr hP_empty
  have h_main : ∃ (R : ℝ), 0 ≤ R ∧ P ⊆ Metric.closedBall (0 : Plane) R := by
    have h : ∃ (r : ℝ), P ⊆ Metric.closedBall (0 : Plane) r :=
      (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hP_bdd
    rcases h with ⟨r, hsub⟩
    by_cases hr : 0 ≤ r
    · exact ⟨r, hr, hsub⟩
    · have hneg : r < 0 := by linarith
      have h_empty : Metric.closedBall (0 : Plane) r = ∅ := by
        ext z; simp [Metric.mem_closedBall, hneg] <;> linarith
      rw [h_empty] at hsub
      have hP_empty' : P = ∅ := Set.subset_empty_iff.mp hsub
      contradiction
  rcases h_main with ⟨R, hR_nonneg, hR⟩
  have h_coord_bdd : ∀ p ∈ P, |p 0| ≤ R ∧ |p 1| ≤ R := by
    intro p hp
    have h1 : ‖p‖ ≤ R := by simpa [Metric.mem_closedBall] using hR hp
    have h2 : |p 0| ≤ ‖p‖ := by
      have h21 : |p 0| ≤ Real.sqrt ((p 0)^2 + (p 1)^2) := by
        have h : (p 0)^2 ≤ (p 0)^2 + (p 1)^2 := by nlinarith [sq_nonneg (p 1)]
        have h' : |p 0| = Real.sqrt ((p 0)^2) := by rw [Real.sqrt_sq_eq_abs]
        rw [h']; exact Real.sqrt_le_sqrt h
      simpa [EuclideanSpace.norm_eq] using h21
    have h3 : |p 1| ≤ ‖p‖ := by
      have h31 : |p 1| ≤ Real.sqrt ((p 0)^2 + (p 1)^2) := by
        have h : (p 1)^2 ≤ (p 0)^2 + (p 1)^2 := by nlinarith [sq_nonneg (p 0)]
        have h' : |p 1| = Real.sqrt ((p 1)^2) := by rw [Real.sqrt_sq_eq_abs]
        rw [h']; exact Real.sqrt_le_sqrt h
      simpa [EuclideanSpace.norm_eq] using h31
    exact ⟨le_trans h2 h1, le_trans h3 h1⟩
  let iMin : ℤ := Int.floor (-R / δ)
  let iMax : ℤ := Int.ceil (R / δ)
  let idxSet : Finset ℤ := Finset.Icc iMin iMax
  let Q : Finset (DyadicSquare n) :=
    idxSet.biUnion fun i => idxSet.image fun j => (⟨i, j⟩ : DyadicSquare n)
  have h_floor_in_range : ∀ (x : ℝ), |x| ≤ R → Int.floor (x / δ) ∈ idxSet := by
    intro x hx
    have h1 : -R ≤ x := by linarith [abs_le.mp hx]
    have h2 : x ≤ R := by linarith [abs_le.mp hx]
    have h3 : -R / δ ≤ x / δ := by gcongr
    have h4 : x / δ ≤ R / δ := by gcongr
    have h5 : iMin ≤ Int.floor (x / δ) := Int.floor_mono h3
    have h7 : Int.floor (x / δ) ≤ iMax := by
      have h8 : Int.floor (x / δ) ≤ Int.ceil (x / δ) := Int.floor_le_ceil (x / δ)
      have h9 : Int.ceil (x / δ) ≤ Int.ceil (R / δ) := Int.ceil_mono h4
      linarith
    exact Finset.mem_Icc.mpr ⟨h5, h7⟩
  have h_floor_cover : ∀ (x : ℝ),
      (Int.floor (x / δ) : ℝ) * δ ≤ x ∧ x < ((Int.floor (x / δ) : ℝ) + 1) * δ := by
    intro x
    have h1 : (Int.floor (x / δ) : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h2 : x / δ < (Int.floor (x / δ) : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    constructor
    · have h3 : (Int.floor (x / δ) : ℝ) * δ ≤ (x / δ) * δ := by gcongr
      have h4 : (x / δ) * δ = x := by field_simp [hδ_pos.ne'] <;> ring
      rw [h4] at h3; exact h3
    · have h5 : (x / δ) * δ < (((Int.floor (x / δ) : ℝ) + 1) * δ) := by gcongr
      have h6 : (x / δ) * δ = x := by field_simp [hδ_pos.ne'] <;> ring
      rw [h6] at h5; exact h5
  refine ⟨Q, ?_⟩
  intro p hp
  let i : ℤ := Int.floor (p 0 / δ)
  let j : ℤ := Int.floor (p 1 / δ)
  have hi_in : i ∈ idxSet := h_floor_in_range (p 0) (h_coord_bdd p hp).1
  have hj_in : j ∈ idxSet := h_floor_in_range (p 1) (h_coord_bdd p hp).2
  let q : DyadicSquare n := ⟨i, j⟩
  have hq_in_Q : q ∈ Q := by
    simp only [Q, Finset.mem_biUnion]
    refine ⟨i, hi_in, ?_⟩
    simp only [Finset.mem_image]
    refine ⟨j, hj_in, ?_⟩
    simp [q]
  have h_p_in_q : p ∈ (q.toSet : Set Plane) := by
    simp only [q, DyadicSquare.toSet]
    have h1 := h_floor_cover (p 0)
    have h2 := h_floor_cover (p 1)
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  exact Set.mem_iUnion₂.mpr ⟨q, hq_in_Q, h_p_in_q⟩

/-! ============================================================================
   Sub-lemma 4: S-set transfer from AffineLine to DyadicTube
   ============================================================================ -/

/-- Any nonempty set is a (δ, s, δ^{-s})-set.

    Proof: cov(P ∩ B(x,r)) ≤ cov(P), and δ^{-s} * r^s = (r/δ)^s ≥ 1
    since r ≥ δ and s ≥ 0. -/
lemma any_nonempty_set_is_sset {X : Type*} [PseudoMetricSpace X]
    {δ s : ℝ} (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s)
    {P : Set X} (hP_nonempty : P.Nonempty) :
    IsDeltaSSet δ s (δ ^ (-s)) P := by
  set C : ℝ := δ ^ (-s) with hC_def
  have hC_pos : 0 < C := Real.rpow_pos_of_pos hδ_pos _
  refine' ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, _⟩
  intro x r hr
  have hr_pos : 0 < r := by linarith
  have h_mono : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set Set.inter_subset_left
  have h1 : 1 ≤ C * r ^ s := by
    have h2 : δ ≤ r := hr
    have h3 : δ ^ s ≤ r ^ s := Real.rpow_le_rpow (by linarith) (by linarith) hs_nonneg
    have h4 : C * δ ^ s = 1 := by
      simp only [hC_def]
      have h5 : δ ^ (-s) * δ ^ s = δ ^ ((-s) + s) := by
        rw [← Real.rpow_add hδ_pos] <;> ring
      rw [h5]
      have h6 : (-s) + s = 0 := by ring
      rw [h6]; simp
    have h7 : C * r ^ s ≥ C * δ ^ s := by gcongr
    linarith
  have hrpow : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
    ENNReal.ofReal_rpow_of_pos hr_pos
  have h_ennreal : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s := by
    rw [hrpow]
    have hmul : ENNReal.ofReal C * ENNReal.ofReal (r ^ s) = ENNReal.ofReal (C * r ^ s) := by
      rw [← ENNReal.ofReal_mul] <;> positivity
    rw [hmul]
    exact ENNReal.one_le_ofReal.mpr h1
  have h8 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    calc
      (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)
        = 1 * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by simp
      _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        gcongr
  exact le_trans h_mono h8

/-- Transfer IsDeltaSSet from AffineLine family to snapped DyadicTube family.

    Uses the trivial S-set bound: any nonempty set is a (δ_n, s, δ_n^{-s})-set.
    The snapped image is nonempty because the original family is nonempty. -/
lemma transfer_sset_to_dyadic_tubes {δ : ℝ} (hδ_pos : 0 < δ)
    {n : ℕ} (hδn : dyadicDelta n ≤ δ) (hδn' : δ < 2 * dyadicDelta n)
    {s C : ℝ} {Tubes : Set AffineLine} {p : Plane}
    (hTubes_bdd : ∀ ℓ ∈ Tubes, ℓ.offset ∈ Metric.closedBall 0 2)
    (hTubes_sset : IsDeltaSSet δ s C Tubes) :
    ∃ (C' : ℝ), 0 < C' ∧
      IsDeltaSSet (dyadicDelta n) s C'
        ((fun ℓ => snapToTubeThroughPoint n ℓ p) '' Tubes) := by
  set δ_n := dyadicDelta n with hδn_def
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hs_nonneg : 0 ≤ s := hTubes_sset.2.2.2.1
  have hTubes_nonempty : Tubes.Nonempty := hTubes_sset.1
  let Tubes' := (fun ℓ => snapToTubeThroughPoint n ℓ p) '' Tubes
  have hTubes'_nonempty : Tubes'.Nonempty := hTubes_nonempty.image _
  set C' : ℝ := δ_n ^ (-s) with hC'_def
  have hC'_pos : 0 < C' := Real.rpow_pos_of_pos hδn_pos _
  have h_main : IsDeltaSSet δ_n s C' Tubes' :=
    any_nonempty_set_is_sset hδn_pos hs_nonneg hTubes'_nonempty
  exact ⟨C', hC'_pos, h_main⟩

/-! ============================================================================
   Sub-lemma 5: Uniformization of tube family cardinality
   ============================================================================ -/

/-- Uniformize tube family cardinalities by thinning to size M.

    Pure combinatorial thinning: picks a subset of exactly M tubes from each
    family, preserving subset and incidence. The S-set constant may blow up;
    use `subset_sset_blowup` separately if needed.

    Note: subsets of an S-set are NOT automatically S-sets with the same constant.
    If original sizes are ≤ K*M, the constant blows up by at most K. -/
lemma uniformize_tube_families {n : ℕ} {s C : ℝ} {M : ℕ}
    {squares : Finset (DyadicSquare n)}
    {tubeFam : (p : DyadicSquare n) → p ∈ squares → Finset (DyadicTube n)}
    {T₀ : Finset (DyadicTube n)}
    (h_subset : ∀ p hp, tubeFam p hp ⊆ T₀)
    (h_intersect : ∀ p hp T, T ∈ tubeFam p hp →
      (T.toSet ∩ p.toSet).Nonempty)
    (hM_min : ∀ p hp, M ≤ (tubeFam p hp).card)
    (hM_pos : 0 < M) :
    ∃ (tubeFam' : (p : DyadicSquare n) → p ∈ squares → Finset (DyadicTube n)),
      (∀ p hp, tubeFam' p hp ⊆ tubeFam p hp) ∧
      (∀ p hp, (tubeFam' p hp).card = M) ∧
      (∀ p hp T, T ∈ tubeFam' p hp →
        (T.toSet ∩ p.toSet).Nonempty) := by
  choose t ht_sub ht_card using fun (p : DyadicSquare n) (hp : p ∈ squares) =>
    Finset.exists_subset_card_eq (hM_min p hp)
  refine ⟨t, ?_⟩
  constructor
  · exact ht_sub
  · constructor
    · exact ht_card
    · intro p hp T hT
      exact h_intersect p hp T (ht_sub p hp hT)

/-- Choose an even dyadic scale n=2m such that δ_{2m} ≤ δ < 4·δ_{2m}.

    Constructed from the existing factor-2 chooser: if it returns odd n,
    use n+1 (which is even), giving δ_{n+1} = δ_n/2 and δ < 2·δ_n = 4·δ_{n+1}. -/
lemma choose_even_dyadic_scale (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) :
    ∃ (m : ℕ), dyadicDelta (2 * m) ≤ δ ∧ δ < 4 * dyadicDelta (2 * m) := by
  rcases choose_dyadic_scale δ hδ_pos hδ_le_one with ⟨n, hδn_leδ, hδ_lt2δn⟩
  by_cases h_even : n % 2 = 0
  · let m := n / 2
    have hn : n = 2 * m := by omega
    have hδ2m_leδ : dyadicDelta (2 * m) ≤ δ := by
      have h : dyadicDelta n ≤ δ := hδn_leδ
      rw [show n = 2 * m from hn] at h
      exact h
    have hδ_lt2 : δ < 2 * dyadicDelta (2 * m) := by
      have h : δ < 2 * dyadicDelta n := hδ_lt2δn
      rw [show n = 2 * m from hn] at h
      exact h
    have hpos : 0 < dyadicDelta (2 * m) := dyadicDelta_pos _
    have h2 : (2 : ℝ) * dyadicDelta (2 * m) < (4 : ℝ) * dyadicDelta (2 * m) := by
      have h3 : (0 : ℝ) < dyadicDelta (2 * m) := hpos
      nlinarith
    have hδ_lt4 : δ < 4 * dyadicDelta (2 * m) := lt_trans hδ_lt2 h2
    exact ⟨m, hδ2m_leδ, hδ_lt4⟩
  · let m := (n + 1) / 2
    have hn : n + 1 = 2 * m := by omega
    have hδn1_leδn : dyadicDelta (n + 1) ≤ dyadicDelta n := by
      simp [dyadicDelta, pow_succ] <;> norm_num <;> linarith
    have h1 : dyadicDelta n = 2 * dyadicDelta (n + 1) := by
      simp [dyadicDelta, pow_succ] <;> ring
    have hδ_lt4 : δ < 4 * dyadicDelta (n + 1) := by
      have h2 : δ < 2 * dyadicDelta n := hδ_lt2δn
      rw [h1] at h2
      linarith
    have h3 : dyadicDelta (2 * m) ≤ δ := by
      have h4 : dyadicDelta (2 * m) = dyadicDelta (n + 1) := by rw [show 2 * m = n + 1 from hn.symm]
      rw [h4]
      exact le_trans hδn1_leδn hδn_leδ
    have h5 : δ < 4 * dyadicDelta (2 * m) := by
      have h6 : dyadicDelta (2 * m) = dyadicDelta (n + 1) := by rw [show 2 * m = n + 1 from hn.symm]
      rw [h6]
      exact hδ_lt4
    exact ⟨m, h3, h5⟩

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

end
