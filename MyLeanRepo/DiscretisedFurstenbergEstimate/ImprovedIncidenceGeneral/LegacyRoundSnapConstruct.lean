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

namespace LegacyRound

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
  let b := roundInt ((p 1 - (a : ℝ) * δ * p 0) / δ)
  ⟨a, b⟩

/-- The point p used for snapping lies inside the resulting tube. -/
lemma snapToTubeThroughPoint_incidence {n : ℕ} {ℓ : AffineLine} {p : Plane} :
    p ∈ (snapToTubeThroughPoint n ℓ p).toSet := by
  let δ : ℝ := dyadicDelta n
  let m : ℝ := (affineLineSlopeIntercept ℓ).1
  let a_raw : ℤ := roundInt (m / δ)
  let a : ℤ := min a_raw ((2 ^ n : ℤ) - 1)
  let b : ℤ := roundInt ((p 1 - (a : ℝ) * δ * p 0) / δ)
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h_main : |(b : ℝ) * δ - (p 1 - (a : ℝ) * δ * p 0)| ≤ δ / 2 := by
    have h_err : |(b : ℝ) - ((p 1 - (a : ℝ) * δ * p 0) / δ)| ≤ 1 / 2 := by
      exact roundInt_abs_error ((p 1 - (a : ℝ) * δ * p 0) / δ)
    have h3 : |(b : ℝ) * δ - (p 1 - (a : ℝ) * δ * p 0)| =
        δ * |(b : ℝ) - ((p 1 - (a : ℝ) * δ * p 0) / δ)| := by
      have h4 : (b : ℝ) * δ - (p 1 - (a : ℝ) * δ * p 0) =
          δ * ((b : ℝ) - ((p 1 - (a : ℝ) * δ * p 0) / δ)) := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h4, abs_mul, abs_of_pos hδ_pos]
    rw [h3]
    have h5 : δ * |(b : ℝ) - ((p 1 - (a : ℝ) * δ * p 0) / δ)| ≤ δ * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h_err hδ_pos.le
    have h6 : δ * (1 / 2 : ℝ) = δ / 2 := by ring
    rw [h6] at h5
    exact h5
  have h4 : |p 1 - (a : ℝ) * δ * p 0 - (b : ℝ) * δ| ≤ δ / 2 := by
    have h5 : p 1 - (a : ℝ) * δ * p 0 - (b : ℝ) * δ =
        -((b : ℝ) * δ - (p 1 - (a : ℝ) * δ * p 0)) := by ring
    rw [h5, abs_neg]
    exact h_main
  have h_final : |p 1 - (snapToTubeThroughPoint n ℓ p).slope * p 0 -
                   (snapToTubeThroughPoint n ℓ p).intercept| ≤ δ := by
    have h9 : (snapToTubeThroughPoint n ℓ p).a = a := by rfl
    have h10 : (snapToTubeThroughPoint n ℓ p).b = b := by rfl
    have h11 : |p 1 - (snapToTubeThroughPoint n ℓ p).slope * p 0 -
                   (snapToTubeThroughPoint n ℓ p).intercept| ≤ δ / 2 := by
      simp [DyadicTube.slope, DyadicTube.intercept, h9, h10] <;> exact h4
    linarith
  simpa [DyadicTube.toSet] using h_final

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

/-! ============================================================================
   Main lemma: construct_nice_configuration
   ============================================================================ -/

/-- Construct a dyadic NiceConfiguration from continuous IsDeltaSSet data.

    Takes finite tube families `Tp : Plane → Finset AffineLine`.
    The reduction from `Set AffineLine` to `Finset AffineLine` is a separate step. -/
lemma construct_nice_configuration
    {δ s t C_P C_T : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s) (hst : s < t)
    (hCP_pos : 0 < C_P) (hCT_pos : 0 < C_T)
    (P : Set Plane)
    (hP_bdd : P ⊆ Metric.closedBall 0 1)
    (hP_sset : IsDeltaSSet δ t C_P P)
    (Tp : Plane → Finset AffineLine)
    (hTp_sset : ∀ p ∈ P, IsDeltaSSet δ s C_T (Tp p : Set AffineLine))
    (hTp_near : ∀ p ∈ P, ∀ ℓ ∈ Tp p, p ∈ Metric.cthickening δ ℓ.1)
    (hTp_bdd : ∀ p ∈ P, ∀ ℓ ∈ Tp p, ℓ.offset ∈ Metric.closedBall 0 2) :
    ∃ (n : ℕ) (C₁ : ℝ) (M : ℕ)
      (hC₁ : 1 ≤ C₁) (hM : 0 < M)
      (config : NiceConfiguration n s C₁ M),
      dyadicDelta n ≤ δ ∧ δ < 2 * dyadicDelta n ∧
      config.pointSet ⊆ Metric.closedBall 0 2 ∧
      P ⊆ config.pointSet ∧
      (∀ p ∈ config.P₀, ∃ (x : Plane), x ∈ P ∧ x ∈ (p.toSet : Set Plane)) := by
  -- Step 1: Choose dyadic scale n
  rcases choose_dyadic_scale δ hδ_pos (by linarith) with ⟨n, hδn, hδn'⟩
  -- Step 2: Cover P by dyadic squares
  have hP_bdd' : Bornology.IsBounded P := by
    apply (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mpr
    exact ⟨1, hP_bdd⟩
  rcases cover_by_dyadic_squares (n := n) hP_bdd' with ⟨squares_all, hcover⟩
  -- Step 3: Filter to squares intersecting P and choose representative points
  let squares : Finset (DyadicSquare n) :=
    squares_all.filter (fun q => (P ∩ (q.toSet : Set Plane)).Nonempty)
  have hP_nonempty : P.Nonempty := hP_sset.1
  have h_squares_nonempty : squares.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    have hpc : p ∈ ⋃ q ∈ squares_all, (q.toSet : Set Plane) := hcover hp
    rcases Set.mem_iUnion₂.mp hpc with ⟨q, hq_all, hq_p⟩
    have hq : q ∈ squares := by
      simp only [squares, Finset.mem_filter]
      exact ⟨hq_all, ⟨p, hp, hq_p⟩⟩
    exact ⟨q, hq⟩
  have h_main_choose : ∀ (q : DyadicSquare n), q ∈ squares →
      ∃ (y : Plane), y ∈ P ∧ y ∈ (q.toSet : Set Plane) := by
    intro q hq
    have h : (P ∩ (q.toSet : Set Plane)).Nonempty := by
      simp only [squares, Finset.mem_filter] at hq
      exact hq.2
    rcases h with ⟨y, hyP, hyQ⟩
    exact ⟨y, hyP, hyQ⟩
  choose x hxP hxQ using h_main_choose
  -- Step 4: Snap each tube family through the representative point
  let rawTubes : (q : DyadicSquare n) → q ∈ squares → Finset (DyadicTube n) :=
    fun q hq => (Tp (x q hq)).image (fun ℓ => snapToTubeThroughPoint n ℓ (x q hq))
  have h_raw_eq : ∀ q hq, (rawTubes q hq : Set (DyadicTube n)) =
      (fun ℓ => snapToTubeThroughPoint n ℓ (x q hq)) '' (Tp (x q hq) : Set AffineLine) := by
    intro q hq
    simp [rawTubes, Finset.coe_image] <;> rfl
  have h_raw_nonempty : ∀ q hq, (rawTubes q hq).Nonempty := by
    intro q hq
    have hTp_nonempty : (Tp (x q hq)).Nonempty := (hTp_sset (x q hq) (hxP q hq)).1
    exact hTp_nonempty.image _
  -- Step 5: S-set property (trivial bound: any nonempty set is (δ_n, s, δ_n^{-s})-set)
  let C' (q : DyadicSquare n) (hq : q ∈ squares) : ℝ := (dyadicDelta n) ^ (-s)
  have hC'_pos : ∀ (q : DyadicSquare n) (hq : q ∈ squares), 0 < C' q hq := by
    intro q hq
    exact Real.rpow_pos_of_pos (dyadicDelta_pos n) _
  have hC'_sset : ∀ (q : DyadicSquare n) (hq : q ∈ squares),
      IsDeltaSSet (dyadicDelta n) s (C' q hq) (rawTubes q hq : Set (DyadicTube n)) := by
    intro q hq
    have h_nonempty : (rawTubes q hq : Set (DyadicTube n)).Nonempty := h_raw_nonempty q hq
    exact any_nonempty_set_is_sset (dyadicDelta_pos n) (by linarith [hs_pos]) h_nonempty
  -- Uniform S-set constant C₁
  let f (q : DyadicSquare n) : ℝ := if hq : q ∈ squares then C' q hq else 0
  have hf_eq : ∀ (q : DyadicSquare n) (hq : q ∈ squares), f q = C' q hq := by
    intro q hq
    simp [f, hq]
  let C₁ : ℝ := 1 + ∑ q ∈ squares, f q
  have hC₁_one : 1 ≤ C₁ := by
    have h_nonneg : 0 ≤ ∑ q ∈ squares, f q := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : i ∈ squares
      · rw [hf_eq i hi]; exact (hC'_pos i hi).le
      · simp [f, hi]
    linarith
  have hC₁_ge : ∀ (q : DyadicSquare n) (hq : q ∈ squares), C' q hq ≤ C₁ := by
    intro q hq
    have h1 : f q = C' q hq := hf_eq q hq
    have h : f q ≤ ∑ q' ∈ squares, f q' := by
      apply Finset.single_le_sum
      · intro i _
        by_cases hi : i ∈ squares
        · rw [hf_eq i hi]; exact (hC'_pos i hi).le
        · simp [f, hi]
      · exact hq
    rw [h1] at h
    linarith
  have h_raw_sset_C1 : ∀ q hq, IsDeltaSSet (dyadicDelta n) s C₁ (rawTubes q hq : Set (DyadicTube n)) := by
    intro q hq
    have h_mono : ∀ {C1 C2 : ℝ}, IsDeltaSSet (dyadicDelta n) s C1 (rawTubes q hq : Set (DyadicTube n)) →
        C1 ≤ C2 → IsDeltaSSet (dyadicDelta n) s C2 (rawTubes q hq : Set (DyadicTube n)) := by
      intro C1 C2 h hC
      rcases h with ⟨hne, hδ, hC1_pos, hs, hbound⟩
      have hC2_pos : 0 < C2 := by linarith
      refine ⟨hne, hδ, hC2_pos, hs, fun x r hr => ?_⟩
      have h4 := hbound x r hr
      have h5 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
      have h61 : ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s ≤
          ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
      have h62 : (ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s) *
          Metric.externalCoveringNumber (dyadicDelta n).toNNReal (rawTubes q hq : Set (DyadicTube n)) ≤
          (ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s) *
          Metric.externalCoveringNumber (dyadicDelta n).toNNReal (rawTubes q hq : Set (DyadicTube n)) :=
        mul_le_mul_of_nonneg_right h61 (by positivity)
      have h_final : ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber (dyadicDelta n).toNNReal (rawTubes q hq : Set (DyadicTube n)) ≤
          ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber (dyadicDelta n).toNNReal (rawTubes q hq : Set (DyadicTube n)) := by
        simpa [mul_assoc] using h62
      exact le_trans h4 h_final
    exact h_mono (hC'_sset q hq) (hC₁_ge q hq)
  -- Step 6: Uniformize
  let M : ℕ := 1
  have hM_pos : 0 < M := by norm_num
  have hM_min : ∀ q hq, M ≤ (rawTubes q hq).card := by
    intro q hq
    have h : 0 < (rawTubes q hq).card := (h_raw_nonempty q hq).card_pos
    exact h
  let T₀ : Finset (DyadicTube n) :=
    squares.attach.biUnion (fun q : {q // q ∈ squares} => rawTubes q q.property)
  have h_intersect : ∀ (q : DyadicSquare n) (hq : q ∈ squares) (T : DyadicTube n),
      T ∈ rawTubes q hq → (T.toSet ∩ (q.toSet : Set Plane)).Nonempty := by
    intro q hq T hT
    have h_exists : ∃ (ℓ : AffineLine), ℓ ∈ Tp (x q hq) ∧
        snapToTubeThroughPoint n ℓ (x q hq) = T := by
      simpa [rawTubes, Finset.mem_image] using hT
    rcases h_exists with ⟨ℓ, hℓ, h_eq⟩
    have h1 : x q hq ∈ (snapToTubeThroughPoint n ℓ (x q hq)).toSet :=
      snapToTubeThroughPoint_incidence
    rw [h_eq] at h1
    have h2 : x q hq ∈ (q.toSet : Set Plane) := hxQ q hq
    exact ⟨x q hq, h1, h2⟩
  have h_subset_T0 : ∀ q hq, rawTubes q hq ⊆ T₀ := by
    intro q hq
    intro T hT
    have hq' : (⟨q, hq⟩ : {q // q ∈ squares}) ∈ squares.attach := by simp
    simp only [T₀, Finset.mem_biUnion]
    exact ⟨⟨q, hq⟩, hq', hT⟩
  rcases @uniformize_tube_families n s C₁ M squares rawTubes T₀
    h_subset_T0 h_intersect hM_min hM_pos
    with ⟨tubeFamily, ht_sub, ht_card, ht_intersect⟩
  -- S-set property for uniformized families (trivial bound)
  have h_mono_const : ∀ {S : Set (DyadicTube n)} {C1 C2 : ℝ},
      IsDeltaSSet (dyadicDelta n) s C1 S → C1 ≤ C2 → IsDeltaSSet (dyadicDelta n) s C2 S := by
    intro S C1 C2 h hC
    rcases h with ⟨hne, hδ, hC1_pos, hs, hbound⟩
    have hC2_pos : 0 < C2 := by linarith
    refine ⟨hne, hδ, hC2_pos, hs, fun x r hr => ?_⟩
    have h4 := hbound x r hr
    have h5 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
    have h6 : ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s ≤
        ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    have h7 : (ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s) *
        Metric.externalCoveringNumber (dyadicDelta n).toNNReal S ≤
        (ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s) *
        Metric.externalCoveringNumber (dyadicDelta n).toNNReal S :=
      mul_le_mul_of_nonneg_right h6 (by positivity)
    exact le_trans h4 h7
  have h_tube_sset : ∀ q hq, IsDeltaSSet (dyadicDelta n) s C₁
      (tubeFamily q hq : Set (DyadicTube n)) := by
    intro q hq
    have h_nonempty : (tubeFamily q hq : Set (DyadicTube n)).Nonempty := by
      have h_card : (tubeFamily q hq).card = M := ht_card q hq
      have h_pos : 0 < (tubeFamily q hq).card := by rw [h_card] <;> exact hM_pos
      exact Finset.card_pos.mp h_pos
    have h_sset_small : IsDeltaSSet (dyadicDelta n) s ((dyadicDelta n) ^ (-s))
        (tubeFamily q hq : Set (DyadicTube n)) :=
      any_nonempty_set_is_sset (dyadicDelta_pos n) (by linarith [hs_pos]) h_nonempty
    have h_C'_le : (dyadicDelta n) ^ (-s) ≤ C₁ := hC₁_ge q hq
    exact h_mono_const h_sset_small h_C'_le
  let config : NiceConfiguration n s C₁ M :=
    { P₀ := squares
      T₀ := T₀
      tubeFamily := tubeFamily
      h_subset := fun q hq => Finset.Subset.trans (ht_sub q hq) (h_subset_T0 q hq)
      h_size := ht_card
      h_delta_s_set := h_tube_sset
      h_intersect := ht_intersect
      h_tube_parameters := Set.Finite.isBounded (Finset.finite_toSet T₀)
      h_bounded := by
        rw [Bornology.isBounded_biUnion (Finset.finite_toSet squares)]
        intro p _
        exact DyadicSquare.toSet_isBounded p }
  have h_pointSet_bdd : config.pointSet ⊆ Metric.closedBall 0 2 := by
    have hδn_half : dyadicDelta n ≤ 1 / 2 := by
      have h3 : dyadicDelta n < 1 := by linarith
      have h4 : ∃ k : ℕ, dyadicDelta n = (2 : ℝ) ^ (-(k : ℤ)) := by
        refine ⟨n, ?_⟩
        simp [dyadicDelta] <;> ring
      rcases h4 with ⟨k, hk⟩
      rw [hk] at h3
      have h5 : 1 ≤ k := by
        by_contra h6
        have h7 : k = 0 := by omega
        rw [h7] at h3
        norm_num at h3
      have h8 : (2 : ℝ) ^ (-(k : ℤ)) ≤ 1 / 2 := by
        have h9 : (k : ℤ) ≥ 1 := by exact_mod_cast h5
        have h10 : (2 : ℝ) ^ (-(k : ℤ)) ≤ (2 : ℝ) ^ (-1 : ℤ) := by gcongr <;> linarith
        norm_num at h10 ⊢ <;> exact h10
      rw [hk] <;> exact h8
    intro z hz
    rcases Set.mem_iUnion₂.mp hz with ⟨q, hq, hzq⟩
    have hq_intersect : (P ∩ (q.toSet : Set Plane)).Nonempty := by
      have h := Finset.mem_filter.mp hq
      exact h.2
    rcases hq_intersect with ⟨p, hpP, hpQ⟩
    have h_p_in_closedBall : p ∈ Metric.closedBall (0 : Plane) 1 := hP_bdd hpP
    have hp_in_ball : ‖p‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using h_p_in_closedBall
    have h_side : |z 0 - p 0| ≤ dyadicDelta n ∧ |z 1 - p 1| ≤ dyadicDelta n :=
      DyadicSquare.side_length hzq hpQ
    have h1 : |z 0 - p 0| ≤ dyadicDelta n := h_side.1
    have h2 : |z 1 - p 1| ≤ dyadicDelta n := h_side.2
    have h_norm_bound : ‖z - p‖ ≤ |z 0 - p 0| + |z 1 - p 1| := by
      have hsq : ‖z - p‖ ^ 2 = (z 0 - p 0)^2 + (z 1 - p 1)^2 := by
        simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using rfl
      have h : (z 0 - p 0)^2 + (z 1 - p 1)^2 ≤ (|z 0 - p 0| + |z 1 - p 1|)^2 := by
        have h2 : 0 ≤ 2 * |z 0 - p 0| * |z 1 - p 1| := by positivity
        have h31 : |z 0 - p 0| ^ 2 = (z 0 - p 0)^2 := by
          rw [sq_abs]
        have h32 : |z 1 - p 1| ^ 2 = (z 1 - p 1)^2 := by
          rw [sq_abs]
        nlinarith
      have h4 : ‖z - p‖ ^ 2 ≤ (|z 0 - p 0| + |z 1 - p 1|)^2 := by
        rw [hsq] <;> exact h
      have h5 : 0 ≤ ‖z - p‖ := by positivity
      have h6 : 0 ≤ |z 0 - p 0| + |z 1 - p 1| := by positivity
      nlinarith
    have h3 : ‖z - p‖ ≤ 2 * dyadicDelta n := by
      calc ‖z - p‖ ≤ |z 0 - p 0| + |z 1 - p 1| := h_norm_bound
           _ ≤ dyadicDelta n + dyadicDelta n := by gcongr
           _ = 2 * dyadicDelta n := by ring
    have h4 : ‖z‖ ≤ ‖p‖ + ‖z - p‖ := by
      calc ‖z‖ = ‖p + (z - p)‖ := by congr 1; abel
           _ ≤ ‖p‖ + ‖z - p‖ := norm_add_le p (z - p)
    have h5 : ‖z‖ ≤ 2 := by
      calc ‖z‖ ≤ ‖p‖ + ‖z - p‖ := h4
           _ ≤ 1 + 2 * dyadicDelta n := by gcongr
           _ ≤ 1 + 2 * (1 / 2) := by gcongr
           _ = 2 := by norm_num
    simpa [Metric.mem_closedBall] using h5
  have hP_cover : P ⊆ config.pointSet := by
    intro p hp
    have h1 : p ∈ ⋃ q ∈ squares_all, (q.toSet : Set Plane) := hcover hp
    rcases Set.mem_iUnion₂.mp h1 with ⟨q, hq_all, hpq⟩
    have hq : q ∈ squares := by
      simp only [squares, Finset.mem_filter]
      exact ⟨hq_all, ⟨p, hp, hpq⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨q, hq, hpq⟩
  have h_witness : ∀ q ∈ config.P₀, ∃ (x : Plane), x ∈ P ∧ x ∈ (q.toSet : Set Plane) := by
    intro q hq
    exact ⟨x q hq, hxP q hq, hxQ q hq⟩
  exact ⟨n, C₁, M, hC₁_one, hM_pos, config, hδn, hδn', h_pointSet_bdd, hP_cover, h_witness⟩

/-- Choose an even dyadic scale n such that dyadicDelta n ≤ δ < 4 * dyadicDelta n.
    If the optimal n is odd, we use n+1, weakening the upper bound from factor 2 to 4. -/
lemma choose_even_dyadic_scale (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) :
    ∃ (n : ℕ), n % 2 = 0 ∧ dyadicDelta n ≤ δ ∧ δ < 4 * dyadicDelta n := by
  rcases choose_dyadic_scale δ hδ_pos hδ_le_one with ⟨n, hδn, hδn'⟩
  by_cases h_even : n % 2 = 0
  · exact ⟨n, h_even, hδn, by linarith [hδn']⟩
  · let n' := n + 1
    have h_n'_even : n' % 2 = 0 := by
      simp [n', Nat.add_mod, h_even] <;> omega
    have h1 : dyadicDelta n' = dyadicDelta n / 2 := by
      simp [n', dyadicDelta, Real.rpow_neg, Real.rpow_natCast] <;> field_simp <;> ring
    have h2 : dyadicDelta n' ≤ δ := by
      rw [h1]
      have h3 : dyadicDelta n / 2 ≤ dyadicDelta n := by
        have h4 : 0 < dyadicDelta n := dyadicDelta_pos n
        linarith
      exact h3.trans hδn
    have h4 : δ < 4 * dyadicDelta n' := by
      rw [h1]
      have h5 : 4 * (dyadicDelta n / 2) = 2 * dyadicDelta n := by ring
      rw [h5]
      exact hδn'
    exact ⟨n', h_n'_even, h2, h4⟩

end LegacyRound

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
