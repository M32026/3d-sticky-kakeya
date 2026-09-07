module

/-
  MeasureExtractDeltaSetOuter.lean

  Extract an IsDeltaSet from a measure with explicit ball growth and mass bounds,
  WITHOUT requiring the set E to be measurable.

  Uses measurable partition cells and the Carathéodory criterion
  (`measure_inter_add_sdiff`) to establish the additive partition identity
  for arbitrary E.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.DiscreteFrostman
public import MyLeanRepo.RadialBootstrapping.DiscreteFrostmanIsDeltaSet

@[expose] public section

set_option maxHeartbeats 1000000

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal
open Vendored.MeasureTheory.FractalGeometry.FrostmanLemma

noncomputable section

namespace RadialBootstrapping

local notation "Point" => EuclideanSpace ℝ (Fin 2)

/-! ============================================================================
   Packing bound for separated sets in the unit ball
   ============================================================================ -/

/-- Grid index of a point: floor of each coordinate divided by δ. -/
def gridIndex (x : Point) (δ : ℝ) : ℤ × ℤ :=
  (Int.floor (x 0 / δ), Int.floor (x 1 / δ))

/-- If floor(a) = floor(b), then |a - b| < 1. -/
lemma abs_sub_lt_one_of_floor_eq {a b : ℝ} (h : Int.floor a = Int.floor b) :
    |a - b| < 1 := by
  have h1 : Int.floor a ≤ a := Int.floor_le a
  have h2 : a < Int.floor a + 1 := Int.lt_floor_add_one a
  have h3 : Int.floor b ≤ b := Int.floor_le b
  have h4 : b < Int.floor b + 1 := Int.lt_floor_add_one b
  rw [h] at *
  have h5 : a - b < 1 := by linarith
  have h6 : -1 < a - b := by linarith
  exact abs_lt.mpr ⟨h6, h5⟩

/-- Coordinate bound: |x i| ≤ ‖x‖. -/
lemma coord_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h_pos : 0 ≤ ∑ j : Fin n, (x j)^2 := by positivity
  have h_norm : ‖x‖ = Real.sqrt (∑ j : Fin n, (x j)^2) := by
    rw [EuclideanSpace.norm_eq]
    apply congr_arg Real.sqrt
    apply Finset.sum_congr rfl
    intro j _
    simp
    <;> ring
  have h2 : (x i)^2 ≤ ∑ j : Fin n, (x j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have h5 : ‖x‖^2 = ∑ j : Fin n, (x j)^2 := by
    rw [h_norm, Real.sq_sqrt h_pos]
  rw [←h5] at h2
  have h6 : 0 ≤ ‖x‖ := by positivity
  nlinarith [sq_abs (x i)]

/-- Two points in the same grid cell are less than 2δ apart. -/
lemma gridIndex_injective_of_separated
    {δ : ℝ} (hδ : 0 < δ)
    {P : Set Point} (hP : Metric.IsSeparated (ENNReal.ofReal (2 * δ)) P) :
    Set.InjOn (fun x : Point => gridIndex x δ) P := by
  intro x hx y hy h
  have h_coord0 : |x 0 - y 0| < δ := by
    have hfx : Int.floor (x 0 / δ) = Int.floor (y 0 / δ) := by
      simpa [gridIndex] using congr_arg Prod.fst h
    have h : |x 0 / δ - y 0 / δ| < 1 := abs_sub_lt_one_of_floor_eq hfx
    have h5 : |x 0 / δ - y 0 / δ| = |x 0 - y 0| / δ := by
      have h6 : x 0 / δ - y 0 / δ = (x 0 - y 0) / δ := by ring
      rw [h6, abs_div, abs_of_pos hδ]
    rw [h5] at h
    have h7 : |x 0 - y 0| / δ < 1 := h
    have h8 : |x 0 - y 0| < δ := by
      calc |x 0 - y 0|
        = (|x 0 - y 0| / δ) * δ := by field_simp [hδ.ne'] <;> ring
      _ < 1 * δ := by gcongr
      _ = δ := by ring
    exact h8
  have h_coord1 : |x 1 - y 1| < δ := by
    have hfx : Int.floor (x 1 / δ) = Int.floor (y 1 / δ) := by
      simpa [gridIndex] using congr_arg Prod.snd h
    have h : |x 1 / δ - y 1 / δ| < 1 := abs_sub_lt_one_of_floor_eq hfx
    have h5 : |x 1 / δ - y 1 / δ| = |x 1 - y 1| / δ := by
      have h6 : x 1 / δ - y 1 / δ = (x 1 - y 1) / δ := by ring
      rw [h6, abs_div, abs_of_pos hδ]
    rw [h5] at h
    have h7 : |x 1 - y 1| / δ < 1 := h
    have h8 : |x 1 - y 1| < δ := by
      calc |x 1 - y 1|
        = (|x 1 - y 1| / δ) * δ := by field_simp [hδ.ne'] <;> ring
      _ < 1 * δ := by gcongr
      _ = δ := by ring
    exact h8
  have h3 : dist x y < 2 * δ := by
    have h_dist : dist x y = Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) := by
      have h : dist x y = Real.sqrt (∑ i : Fin 2, (dist (x i) (y i))^2) := by exact EuclideanSpace.dist_eq x y
      rw [h]
      have h2 : ∑ i : Fin 2, (dist (x i) (y i))^2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
        simp [Fin.sum_univ_two, Real.dist_eq] <;> ring
      rw [h2]
    rw [h_dist]
    have h_pos : 0 ≤ (x 0 - y 0)^2 + (x 1 - y 1)^2 := by positivity
    have h_lt : (x 0 - y 0)^2 + (x 1 - y 1)^2 < (2 * δ)^2 := by
      have h6 : (x 0 - y 0)^2 < δ^2 := by
        have h7 : |x 0 - y 0| < δ := h_coord0
        nlinarith [abs_lt.mp h7]
      have h8 : (x 1 - y 1)^2 < δ^2 := by
        have h9 : |x 1 - y 1| < δ := h_coord1
        nlinarith [abs_lt.mp h9]
      nlinarith
    have h9 : Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) < Real.sqrt ((2 * δ)^2) :=
      Real.sqrt_lt_sqrt h_pos h_lt
    have h10 : Real.sqrt ((2 * δ)^2) = 2 * δ := by
      rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_pos (by linarith)]
    rw [h10] at h9 <;> exact h9
  by_contra hne
  have h10 : (ENNReal.ofReal (2 * δ) < edist x y) := hP hx hy hne
  have h11 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
  rw [h11] at h10
  have h12 : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal (2 * δ) := by
    gcongr <;> linarith
  exact not_le.mpr h10 h12

/-- A 2δ-separated subset of the unit ball has ncard ≤ ceil(100/δ^2). -/
lemma separated_set_unit_ball_card_le {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    {P : Set Point}
    (hP : Metric.IsSeparated (ENNReal.ofReal (2 * δ)) P)
    (hP_sub : P ⊆ closedBall (0 : Point) 1)
    (hP_finite : P.Finite) :
    P.ncard ≤ Nat.ceil (100 / δ^2) := by
  let a : ℤ := Int.ceil (-3 / δ)
  let b : ℤ := Int.floor (3 / δ) + 1
  let S : Finset (ℤ × ℤ) := (Finset.Icc a b).product (Finset.Icc a b)
  have h_inv : 1 ≤ 1 / δ := by
    have h1 : δ ≤ 1 := hδ_le_one
    have h2 : 0 ≤ 1 / δ := by positivity
    have h3 : δ * (1 / δ) ≤ 1 / δ := by
      have h31 : δ * (1 / δ) ≤ 1 * (1 / δ) := mul_le_mul_of_nonneg_right h1 h2
      have h32 : 1 * (1 / δ) = 1 / δ := by ring
      rw [h32] at h31
      exact h31
    have h4 : δ * (1 / δ) = 1 := by field_simp [hδ.ne'] <;> ring
    rw [h4] at h3
    exact h3
  have h_a_le : (a : ℝ) ≤ -1 / δ := by
    have h1 : (a : ℝ) ≤ -3 / δ + 1 := by
      exact Int.ceil_lt_add_one (-3 / δ) |>.le
    have h2 : -3 / δ + 1 ≤ -1 / δ := by
      have h3 : 2 ≤ 2 / δ := by
        calc 2 = 2 * 1 := by ring
          _ ≤ 2 * (1 / δ) := by gcongr
          _ = 2 / δ := by ring
      have h4 : 1 ≤ 2 / δ := by linarith
      have h5 : 0 ≤ 2 / δ - 1 := sub_nonneg.mpr h4
      have h6 : (-1 / δ) - (-3 / δ + 1) = 2 / δ - 1 := by ring
      have h7 : 0 ≤ (-1 / δ) - (-3 / δ + 1) := by rw [h6] <;> exact h5
      exact sub_nonneg.mp h7
    linarith
  have h_b_ge : (b : ℝ) ≥ 1 / δ := by
    have h1 : (b : ℝ) = (Int.floor (3 / δ) : ℝ) + 1 := by
      simp [b] <;> norm_cast
    rw [h1]
    have h2 : (Int.floor (3 / δ) : ℝ) > 3 / δ - 1 := Int.sub_one_lt_floor (3 / δ)
    have h3 : 3 / δ - 1 ≥ 1 / δ := by
      have h4 : 2 / δ ≥ 2 := by
        calc 2 / δ = 2 * (1 / δ) := by ring
          _ ≥ 2 * 1 := by gcongr
          _ = 2 := by ring
      have h5 : 1 ≤ 2 / δ := by linarith
      have h6 : 0 ≤ 2 / δ - 1 := sub_nonneg.mpr h5
      have h7 : (3 / δ - 1) - (1 / δ) = 2 / δ - 1 := by ring
      have h8 : 0 ≤ (3 / δ - 1) - (1 / δ) := by rw [h7] <;> exact h6
      exact sub_nonneg.mp h8
    linarith
  have h_ab : a ≤ b := by
    have h1 : (a : ℝ) ≤ -1 / δ := h_a_le
    have h2 : (b : ℝ) ≥ 1 / δ := h_b_ge
    have h3 : -1 / δ ≤ 1 / δ := by
      have h_pos : 0 ≤ 1 / δ := by positivity
      have h_neg : -1 / δ ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
      exact le_trans h_neg h_pos
    have h4 : (a : ℝ) ≤ (b : ℝ) := by linarith
    exact_mod_cast h4
  -- Any point in unit ball maps into S
  have h_mem : ∀ x ∈ closedBall (0 : Point) 1, gridIndex x δ ∈ S := by
    intro x hx
    have hx0 : |x 0| ≤ 1 := coord_le_norm x 0 |>.trans (by simpa [Metric.mem_closedBall] using hx)
    have hx1 : |x 1| ≤ 1 := coord_le_norm x 1 |>.trans (by simpa [Metric.mem_closedBall] using hx)
    have h10 : -1 / δ ≤ x 0 / δ := by
      have h11 : -1 ≤ x 0 := by linarith [abs_le.mp hx0]
      gcongr <;> linarith
    have h11 : x 0 / δ ≤ 1 / δ := by
      have h12 : x 0 ≤ 1 := by linarith [abs_le.mp hx0]
      gcongr <;> linarith
    have h12 : -1 / δ ≤ x 1 / δ := by
      have h13 : -1 ≤ x 1 := by linarith [abs_le.mp hx1]
      gcongr <;> linarith
    have h13 : x 1 / δ ≤ 1 / δ := by
      have h14 : x 1 ≤ 1 := by linarith [abs_le.mp hx1]
      gcongr <;> linarith
    have h_floor0 : a ≤ Int.floor (x 0 / δ) := by
      rw [Int.le_floor]
      <;> linarith [h_a_le]
    have h_ceil0 : Int.floor (x 0 / δ) ≤ b := by
      have h : x 0 / δ ≤ (b : ℝ) := by linarith [h_b_ge, h11]
      have h' : Int.floor (x 0 / δ) ≤ Int.floor ((b : ℝ)) := Int.floor_mono h
      simpa [b] using h'
    have h_floor1 : a ≤ Int.floor (x 1 / δ) := by
      rw [Int.le_floor] <;> linarith [h_a_le]
    have h_ceil1 : Int.floor (x 1 / δ) ≤ b := by
      have h : x 1 / δ ≤ (b : ℝ) := by linarith [h_b_ge, h13]
      have h' : Int.floor (x 1 / δ) ≤ Int.floor ((b : ℝ)) := Int.floor_mono h
      simpa [b] using h'
    dsimp only [S, gridIndex]
    exact Finset.mem_product.mpr ⟨
      Finset.mem_Icc.mpr ⟨h_floor0, h_ceil0⟩,
      Finset.mem_Icc.mpr ⟨h_floor1, h_ceil1⟩
    ⟩
  -- Cardinality of S
  have h_card1 : ((Finset.Icc a b).card : ℝ) = (b : ℝ) - (a : ℝ) + 1 := by
    simp [h_ab, Finset.card_eq_zero]
    <;> norm_cast <;> omega
  have h_card2 : ((Finset.Icc a b).card : ℝ) ≤ 8 / δ := by
    rw [h_card1]
    have h4 : (b : ℝ) ≤ 3 / δ + 1 := by
      simp [b]
      have h5 : (Int.floor (3 / δ) : ℝ) ≤ 3 / δ := Int.floor_le (3 / δ)
      linarith
    have h5 : (a : ℝ) ≥ -3 / δ := by
      simp [a]
      exact Int.le_ceil (-3 / δ)
    have h6 : 2 / δ ≥ 2 := by
      calc 2 / δ = 2 * (1 / δ) := by ring
        _ ≥ 2 * 1 := by gcongr
        _ = 2 := by ring
    have h10 : (b : ℝ) - (a : ℝ) + 1 ≤ 8 / δ := by
      calc (b : ℝ) - (a : ℝ) + 1
        ≤ (3 / δ + 1) - (-3 / δ) + 1 := by linarith
      _ = 6 / δ + 2 := by ring
      _ ≤ 8 / δ := by
        have h7 : 2 ≤ 2 / δ := by
          calc 2 = 2 * 1 := by ring
            _ ≤ 2 * (1 / δ) := by gcongr
            _ = 2 / δ := by ring
        have h8 : 0 ≤ 2 / δ - 2 := sub_nonneg.mpr h7
        have h9 : (8 / δ) - (6 / δ + 2) = 2 / δ - 2 := by ring
        have h10 : 0 ≤ (8 / δ) - (6 / δ + 2) := by rw [h9] <;> exact h8
        exact sub_nonneg.mp h10
    exact h10
  have h_S_card : (S.card : ℝ) ≤ 64 / δ^2 := by
    have h : S.card = (Finset.Icc a b).card ^ 2 := by
      simp [S, Finset.card_product] <;> ring
    rw [h]
    have h7 : ((Finset.Icc a b).card : ℝ) ^ 2 ≤ (8 / δ) ^ 2 := by gcongr
    have h8 : (8 / δ) ^ 2 = 64 / δ^2 := by ring
    rw [h8] at h7
    exact_mod_cast h7
  -- Injectivity gives cardinality bound
  let f : Point → ℤ × ℤ := fun x => gridIndex x δ
  have h_inj : Set.InjOn f P := gridIndex_injective_of_separated hδ hP
  let Pfin : Finset Point := hP_finite.toFinset
  have h_coe : (Pfin : Set Point) = P := hP_finite.coe_toFinset
  let indices : Finset (ℤ × ℤ) := Pfin.image f
  have h_indices_sub : indices ⊆ S := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have hxP : x ∈ P := by
      have h : x ∈ (Pfin : Set Point) := hx
      rw [h_coe] at h <;> exact h
    exact h_mem x (hP_sub hxP)
  have h_card_image : indices.card = Pfin.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy h
    have hxP : x ∈ P := by
      have h : x ∈ (Pfin : Set Point) := hx
      rw [h_coe] at h <;> exact h
    have hyP : y ∈ P := by
      have h : y ∈ (Pfin : Set Point) := hy
      rw [h_coe] at h <;> exact h
    exact h_inj hxP hyP h
  have h9 : P.ncard = Pfin.card := by
    have h10 : P = (Pfin : Set Point) := h_coe.symm
    rw [h10]
    simp
  rw [h9]
  have h10 : Pfin.card ≤ S.card := by
    rw [←h_card_image]
    exact Finset.card_le_card h_indices_sub
  have h11 : (Pfin.card : ℝ) ≤ 64 / δ^2 := by
    calc (Pfin.card : ℝ)
      ≤ (S.card : ℝ) := by exact_mod_cast h10
    _ ≤ 64 / δ^2 := h_S_card
  have h12 : (Pfin.card : ℝ) ≤ 100 / δ^2 := by
    calc (Pfin.card : ℝ)
      ≤ 64 / δ^2 := h11
    _ ≤ 100 / δ^2 := by gcongr <;> norm_num
  have h13 : (Pfin.card : ℝ) ≤ ↑(Nat.ceil (100 / δ^2)) := by
    calc (Pfin.card : ℝ)
      ≤ 100 / δ^2 := h12
    _ ≤ ↑(Nat.ceil (100 / δ^2)) := Nat.le_ceil (100 / δ^2)
  exact_mod_cast h13

/-! ============================================================================
   Packing bound for δ-separated sets in a δ-ball
   ============================================================================ -/

/-- A δ-separated subset of a closed δ-ball has cardinality at most 25.
Uses a grid of cell size δ/2: each coordinate maps to one of 5 integer values,
giving at most 5×5 = 25 cells, and each cell contains at most one point. -/
lemma separated_set_closedBall_delta_card_le {δ : ℝ} (hδ : 0 < δ) {z : Point}
    {P : Set Point} (hP : Metric.IsSeparated (ENNReal.ofReal δ) P)
    (hP_sub : P ⊆ closedBall z δ) (hP_finite : P.Finite) :
    P.ncard ≤ 25 := by
  let g (x : Point) : ℤ × ℤ :=
    (Int.floor (2 * (x 0 - z 0) / δ), Int.floor (2 * (x 1 - z 1) / δ))
  have h_inj : Set.InjOn g P := by
    intro x hx y hy h
    have h0 : |(x 0 - z 0) - (y 0 - z 0)| < δ / 2 := by
      have hfx : Int.floor (2 * (x 0 - z 0) / δ) = Int.floor (2 * (y 0 - z 0) / δ) :=
        by simpa [g] using congr_arg Prod.fst h
      have h : |2 * (x 0 - z 0) / δ - 2 * (y 0 - z 0) / δ| < 1 :=
        abs_sub_lt_one_of_floor_eq hfx
      have h5 : |2 * (x 0 - z 0) / δ - 2 * (y 0 - z 0) / δ| =
          2 * |(x 0 - z 0) - (y 0 - z 0)| / δ := by
        have h6 : 2 * (x 0 - z 0) / δ - 2 * (y 0 - z 0) / δ =
            2 * ((x 0 - z 0) - (y 0 - z 0)) / δ := by ring
        rw [h6, abs_div, abs_of_pos hδ, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        <;> ring
      rw [h5] at h
      have h7 : 2 * |(x 0 - z 0) - (y 0 - z 0)| / δ < 1 := h
      have h8 : 2 * |(x 0 - z 0) - (y 0 - z 0)| < δ := by
        calc 2 * |(x 0 - z 0) - (y 0 - z 0)|
          = (2 * |(x 0 - z 0) - (y 0 - z 0)| / δ) * δ := by field_simp [hδ.ne'] <;> ring
        _ < 1 * δ := by gcongr
        _ = δ := by ring
      linarith
    have h1 : |(x 1 - z 1) - (y 1 - z 1)| < δ / 2 := by
      have hfx : Int.floor (2 * (x 1 - z 1) / δ) = Int.floor (2 * (y 1 - z 1) / δ) :=
        by simpa [g] using congr_arg Prod.snd h
      have h : |2 * (x 1 - z 1) / δ - 2 * (y 1 - z 1) / δ| < 1 :=
        abs_sub_lt_one_of_floor_eq hfx
      have h5 : |2 * (x 1 - z 1) / δ - 2 * (y 1 - z 1) / δ| =
          2 * |(x 1 - z 1) - (y 1 - z 1)| / δ := by
        have h6 : 2 * (x 1 - z 1) / δ - 2 * (y 1 - z 1) / δ =
            2 * ((x 1 - z 1) - (y 1 - z 1)) / δ := by ring
        rw [h6, abs_div, abs_of_pos hδ, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        <;> ring
      rw [h5] at h
      have h7 : 2 * |(x 1 - z 1) - (y 1 - z 1)| / δ < 1 := h
      have h8 : 2 * |(x 1 - z 1) - (y 1 - z 1)| < δ := by
        calc 2 * |(x 1 - z 1) - (y 1 - z 1)|
          = (2 * |(x 1 - z 1) - (y 1 - z 1)| / δ) * δ := by field_simp [hδ.ne'] <;> ring
        _ < 1 * δ := by gcongr
        _ = δ := by ring
      linarith
    have h_dist : dist x y < δ := by
      have h_dist2 : dist x y = Real.sqrt (((x 0 - y 0)^2 + (x 1 - y 1)^2)) := by
        have h : dist x y = Real.sqrt (∑ i : Fin 2, (dist (x i) (y i))^2) := by exact EuclideanSpace.dist_eq x y
        rw [h]
        have h2 : ∑ i : Fin 2, (dist (x i) (y i))^2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
          simp [Fin.sum_univ_two, Real.dist_eq] <;> ring
        rw [h2]
      rw [h_dist2]
      have h_pos : 0 ≤ (x 0 - y 0)^2 + (x 1 - y 1)^2 := by positivity
      have h_lt : (x 0 - y 0)^2 + (x 1 - y 1)^2 < δ^2 := by
        have h9 : (x 0 - y 0)^2 < (δ / 2)^2 := by
          have h10 : |x 0 - y 0| < δ / 2 := by
            have h_eq : (x 0 - z 0) - (y 0 - z 0) = x 0 - y 0 := by ring
            rw [h_eq] at h0
            exact h0
          nlinarith [abs_lt.mp h10]
        have h11 : (x 1 - y 1)^2 < (δ / 2)^2 := by
          have h12 : |x 1 - y 1| < δ / 2 := by
            have h_eq : (x 1 - z 1) - (y 1 - z 1) = x 1 - y 1 := by ring
            rw [h_eq] at h1
            exact h1
          nlinarith [abs_lt.mp h12]
        nlinarith
      have h13 : Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) < Real.sqrt (δ^2) :=
        Real.sqrt_lt_sqrt h_pos h_lt
      have h14 : Real.sqrt (δ^2) = δ := by
        rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_pos hδ]
      rw [h14] at h13 <;> exact h13
    by_contra hne
    have h10 : (ENNReal.ofReal δ < edist x y) := hP hx hy hne
    have h11 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
    rw [h11] at h10
    have h12 : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal δ := by
      gcongr <;> linarith
    exact not_le.mpr h10 h12
  let S : Finset (ℤ × ℤ) := (Finset.Icc (-2 : ℤ) 2).product (Finset.Icc (-2 : ℤ) 2)
  have hS_card : S.card = 25 := by decide
  have h_mem : ∀ x ∈ P, g x ∈ S := by
    intro x hx
    have hxz : x ∈ closedBall z δ := hP_sub hx
    have h0 : |x 0 - z 0| ≤ δ := by
      have h : |x 0 - z 0| ≤ ‖x - z‖ := coord_le_norm (x - z) 0
      have h2 : ‖x - z‖ ≤ δ := by
        have h_dist_eq : dist x z = ‖x - z‖ := by
          rw [dist_eq_norm]
        have h3 : dist x z ≤ δ := by simpa [Metric.mem_closedBall] using hxz
        rw [h_dist_eq] at h3
        exact h3
      exact h.trans h2
    have h1 : |x 1 - z 1| ≤ δ := by
      have h : |x 1 - z 1| ≤ ‖x - z‖ := coord_le_norm (x - z) 1
      have h2 : ‖x - z‖ ≤ δ := by
        have h_dist_eq : dist x z = ‖x - z‖ := by
          rw [dist_eq_norm]
        have h3 : dist x z ≤ δ := by simpa [Metric.mem_closedBall] using hxz
        rw [h_dist_eq] at h3
        exact h3
      exact h.trans h2
    have h2 : -2 ≤ (2 * (x 0 - z 0) / δ : ℝ) := by
      have h3 : -δ ≤ x 0 - z 0 := by linarith [abs_le.mp h0]
      have h4 : -2 * δ ≤ 2 * (x 0 - z 0) := by linarith
      have h5 : -2 ≤ 2 * (x 0 - z 0) / δ := by
        calc -2
          = (-2 * δ) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ 2 * (x 0 - z 0) / δ := by gcongr
      exact h5
    have h3 : (2 * (x 0 - z 0) / δ : ℝ) ≤ 2 := by
      have h4 : x 0 - z 0 ≤ δ := by linarith [abs_le.mp h0]
      have h5 : 2 * (x 0 - z 0) ≤ 2 * δ := by linarith
      calc 2 * (x 0 - z 0) / δ
        ≤ (2 * δ) / δ := by gcongr
      _ = 2 := by field_simp [hδ.ne'] <;> ring
    have h4 : -2 ≤ (2 * (x 1 - z 1) / δ : ℝ) := by
      have h5 : -δ ≤ x 1 - z 1 := by linarith [abs_le.mp h1]
      have h6 : -2 * δ ≤ 2 * (x 1 - z 1) := by linarith
      calc -2
        = (-2 * δ) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ 2 * (x 1 - z 1) / δ := by gcongr
    have h5 : (2 * (x 1 - z 1) / δ : ℝ) ≤ 2 := by
      have h6 : x 1 - z 1 ≤ δ := by linarith [abs_le.mp h1]
      have h7 : 2 * (x 1 - z 1) ≤ 2 * δ := by linarith
      calc 2 * (x 1 - z 1) / δ
        ≤ (2 * δ) / δ := by gcongr
      _ = 2 := by field_simp [hδ.ne'] <;> ring
    have h_floor0 : -2 ≤ Int.floor (2 * (x 0 - z 0) / δ) := by
      rw [Int.le_floor] <;> linarith
    have h_ceil0 : Int.floor (2 * (x 0 - z 0) / δ) ≤ 2 := by
      have h : (Int.floor (2 * (x 0 - z 0) / δ) : ℝ) ≤ 2 := by
        exact (Int.floor_le (2 * (x 0 - z 0) / δ)).trans h3
      exact_mod_cast h
    have h_floor1 : -2 ≤ Int.floor (2 * (x 1 - z 1) / δ) := by
      rw [Int.le_floor] <;> linarith
    have h_ceil1 : Int.floor (2 * (x 1 - z 1) / δ) ≤ 2 := by
      have h : (Int.floor (2 * (x 1 - z 1) / δ) : ℝ) ≤ 2 := by
        exact (Int.floor_le (2 * (x 1 - z 1) / δ)).trans h5
      exact_mod_cast h
    dsimp only [g, S]
    exact Finset.mem_product.mpr ⟨
      Finset.mem_Icc.mpr ⟨h_floor0, h_ceil0⟩,
      Finset.mem_Icc.mpr ⟨h_floor1, h_ceil1⟩
    ⟩
  let Pfin : Finset Point := hP_finite.toFinset
  let indices : Finset (ℤ × ℤ) := Pfin.image g
  have h_indices_sub : indices ⊆ S := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have hxP : x ∈ P := by
      have h : x ∈ (Pfin : Set Point) := hx
      have h2 : (Pfin : Set Point) = P := hP_finite.coe_toFinset
      rw [h2] at h <;> exact h
    exact h_mem x hxP
  have h_card_image : indices.card = Pfin.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy h
    have hxP : x ∈ P := by
      have h : x ∈ (Pfin : Set Point) := hx
      have h2 : (Pfin : Set Point) = P := hP_finite.coe_toFinset
      rw [h2] at h <;> exact h
    have hyP : y ∈ P := by
      have h : y ∈ (Pfin : Set Point) := hy
      have h2 : (Pfin : Set Point) = P := hP_finite.coe_toFinset
      rw [h2] at h <;> exact h
    exact h_inj hxP hyP h
  have h9 : P.ncard = Pfin.card := by
    have h10 : P = (Pfin : Set Point) := hP_finite.coe_toFinset.symm
    rw [h10] <;> simp
  rw [h9]
  have h10 : Pfin.card ≤ S.card := by
    rw [←h_card_image]
    exact Finset.card_le_card h_indices_sub
  rw [hS_card] at h10
  exact h10

/-! ============================================================================
   Dyadic pigeonhole helper
   ============================================================================ -/

/-- Dyadic pigeonhole: given `K` disjoint ranges covering `s`, at least one
range has total weight ≥ total / K. -/
lemma dyadic_pigeonhole_simple {ι : Type*} {s : Finset ι} (hs_nonempty : s.Nonempty)
    (w : ι → ℝ) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (K : ℕ) (hK_pos : 0 < K)
    (range : ℕ → ι → Prop) [∀ k i, Decidable (range k i)]
    (h_cover : ∀ i ∈ s, ∃ k < K, range k i)
    (h_disj : ∀ i ∈ s, ∀ k l, range k i → range l i → k = l) :
    ∃ k < K,
      let R := s.filter (range k)
      (∑ i ∈ R, w i) ≥ (∑ i ∈ s, w i) / (K : ℝ) := by
  let R : ℕ → Finset ι := fun k => s.filter (range k)
  have h_partition : ∀ i ∈ s, ∃! k : ℕ, k < K ∧ i ∈ R k := by
    intro i hi
    rcases h_cover i hi with ⟨k, hkK, hk_range⟩
    have hki : i ∈ R k := Finset.mem_filter.mpr ⟨hi, hk_range⟩
    refine ⟨k, ⟨hkK, hki⟩, fun l hl => ?_⟩
    have hl_range : range l i := (Finset.mem_filter.mp hl.2).2
    exact (h_disj i hi k l hk_range hl_range).symm
  have h_sum : ∑ k ∈ Finset.range K, ∑ i ∈ R k, w i = ∑ i ∈ s, w i := by
    have h_disj' : ∀ k l, k ≠ l → Disjoint (R k) (R l) := by
      intro k l hne
      rw [Finset.disjoint_left]
      intro i hik hil
      have h1 : range k i := (Finset.mem_filter.mp hik).2
      have h2 : range l i := (Finset.mem_filter.mp hil).2
      have h3 : k = l := h_disj i (Finset.mem_filter.mp hik).1 k l h1 h2
      exact hne h3
    have h_union : (⋃ k ∈ Finset.range K, (R k : Set ι)) = (s : Set ι) := by
      ext i
      simp only [Set.mem_iUnion₂, Finset.mem_coe, Finset.mem_range]
      constructor
      · rintro ⟨k, _, hki⟩
        exact (Finset.mem_filter.mp hki).1
      · intro hi
        rcases h_cover i hi with ⟨k, hkK, hk_range⟩
        exact ⟨k, hkK, Finset.mem_filter.mpr ⟨hi, hk_range⟩⟩
    have h_disj'' : (Finset.range K : Set ℕ).PairwiseDisjoint R := by
      intro k _ l _ hne
      exact h_disj' k l hne
    have h_biUnion : (Finset.range K).biUnion R = s := by
      have h1 : (↑((Finset.range K).biUnion R) : Set ι) = ⋃ k ∈ Finset.range K, ↑(R k) := by
        rw [Finset.coe_biUnion] <;> simp
      have h2 : (↑((Finset.range K).biUnion R) : Set ι) = (s : Set ι) := by
        rw [h1, h_union]
      exact_mod_cast h2
    rw [←Finset.sum_biUnion h_disj'']
    rw [h_biUnion]
  by_contra h
  push Not at h
  have h6 : ∑ k ∈ Finset.range K, ∑ i ∈ R k, w i < ∑ i ∈ s, w i := by
    have h7 : ∑ k ∈ Finset.range K, ∑ i ∈ R k, w i <
        ∑ k ∈ Finset.range K, (∑ i ∈ s, w i) / (K : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨0, by simpa using hK_pos⟩
      · intro k hk
        have h9 : ¬(∑ i ∈ R k, w i ≥ (∑ i ∈ s, w i) / (K : ℝ)) := by
          simpa using h k (Finset.mem_range.mp hk)
        exact lt_of_not_ge h9
    have h8 : ∑ k ∈ Finset.range K, (∑ i ∈ s, w i) / (K : ℝ) = ∑ i ∈ s, w i := by
      simp [Finset.sum_const, Finset.card_range] <;> field_simp <;> ring
    rw [h8] at h7 <;> exact h7
  rw [h_sum] at h6
  exact lt_irrefl (∑ i ∈ s, w i) h6

/-! ============================================================================
   Main theorem: extract IsDeltaSet from a measure
   ============================================================================ -/

/-- Frostman bound extends from open balls to closed balls. -/
lemma frostman_closedBall {ν : Measure Point} {X : Set Point} {C : ℝ}
    (hFrostman : ∀ x r, 0 < r → ν (X ∩ ball x r) ≤ ENNReal.ofReal (C * r))
    {x : Point} {r : ℝ} (hr : 0 < r) (hC : 0 ≤ C) :
    ν (X ∩ closedBall x r) ≤ ENNReal.ofReal (C * r) := by
  have h1 : ∀ ε : ℝ, 0 < ε → ν (X ∩ closedBall x r) ≤ ENNReal.ofReal (C * (r + ε)) := by
    intro ε hε
    have h2 : closedBall x r ⊆ ball x (r + ε) := by
      intro y hy
      have h3 : dist y x ≤ r := by simpa [Metric.mem_closedBall] using hy
      have h4 : dist y x < r + ε := by linarith
      simpa [Metric.mem_ball] using h4
    have h5 : X ∩ closedBall x r ⊆ X ∩ ball x (r + ε) := Set.inter_subset_inter_right X h2
    have h6 : 0 < r + ε := by linarith
    exact (measure_mono h5).trans (hFrostman x (r + ε) h6)
  by_cases hC0 : C = 0
  · -- C = 0 case: h1 with any ε gives measure ≤ 0
    have h2 : ν (X ∩ closedBall x r) ≤ ENNReal.ofReal (C * (r + 1)) := h1 1 (by norm_num)
    rw [hC0] at h2
    have h3 : ENNReal.ofReal ((0 : ℝ) * (r + 1)) = 0 := by simp
    rw [h3] at h2
    have h4 : ν (X ∩ closedBall x r) = 0 := by simpa using h2
    rw [h4, hC0] <;> simp
  · -- C > 0 case: contradiction via ε = (a - C*r) / (2*C)
    have hCpos : 0 < C := by
      have h : C ≠ 0 := hC0
      exact lt_of_le_of_ne hC h.symm
    by_contra h7
    have h8 : ENNReal.ofReal (C * r) < ν (X ∩ closedBall x r) := not_le.mp h7
    have h9 : ν (X ∩ closedBall x r) ≠ ⊤ := by
      have h10 := h1 1 (by norm_num)
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h10
    let a : ℝ := (ν (X ∩ closedBall x r)).toReal
    have h11 : ENNReal.ofReal a = ν (X ∩ closedBall x r) := ENNReal.ofReal_toReal h9
    have ha_pos : 0 < a := by
      have h_pos : 0 < ν (X ∩ closedBall x r) := by
        have h_nonneg : 0 ≤ ENNReal.ofReal (C * r) := by positivity
        exact lt_of_le_of_lt h_nonneg h8
      exact ENNReal.toReal_pos h_pos.ne' h9
    have hCr_lt_a : C * r < a := by
      have h12 : ENNReal.ofReal (C * r) < ENNReal.ofReal a := by
        rw [h11] <;> exact h8
      exact (ENNReal.ofReal_lt_ofReal_iff ha_pos).mp h12
    set ε : ℝ := (a - C * r) / (2 * C) with hε_def
    have hε_pos : 0 < ε := by positivity
    have hε_lt : C * (r + ε) < a := by
      have h1 : C * (r + ε) = C * r + C * ε := by ring
      rw [h1]
      have h2 : C * ε = (a - C * r) / 2 := by
        rw [hε_def] <;> field_simp [hCpos.ne'] <;> ring
      rw [h2] <;> linarith
    have h10 : ENNReal.ofReal (C * (r + ε)) < ENNReal.ofReal a :=
      (ENNReal.ofReal_lt_ofReal_iff ha_pos).mpr hε_lt
    have h12 : ENNReal.ofReal a = ν (X ∩ closedBall x r) := by
      rw [ENNReal.ofReal_toReal h9]
    rw [h12] at h10
    have h13 := h1 ε hε_pos
    exact not_le.mpr h10 h13

/-- Core cardinality bound for the IsDeltaSet condition.

Given `I_card * a ≤ C * (r + 2δ)`, `a * P_card ≥ m / (8K)`, and `24K ≤ 100L`,
prove `I_card ≤ 100 * C * L / m * r * P_card`. -/
lemma card_bound_core (I_card P_card a C r δ m K L : ℝ)
    (ha_pos : 0 < a) (hC_pos : 0 < C) (hδ : 0 < δ) (hr : δ ≤ r)
    (hm_pos : 0 < m) (hK_pos : 0 < K) (hP_card_pos : 0 < P_card)
    (hL_nonneg : 0 ≤ L)
    (h12 : I_card * a ≤ C * (r + 2 * δ))
    (h15 : a * P_card ≥ m / (8 * K))
    (h24K : 24 * K ≤ 100 * L) :
    I_card ≤ 100 * C * L / m * r * P_card := by
  have h13 : I_card ≤ C * (r + 2 * δ) / a := by
    have hne : a ≠ 0 := ha_pos.ne'
    have h_eq : (I_card * a) / a = I_card := by field_simp [hne]
    calc I_card
      = (I_card * a) / a := h_eq.symm
      _ ≤ (C * (r + 2 * δ)) / a := div_le_div_of_nonneg_right h12 (by linarith)
  have h20 : 0 < m / (8 * K) := div_pos hm_pos (by positivity)
  have h21 : m / (8 * K) ≤ a * P_card := h15
  have hpos : 0 < a * (m / (8 * K)) := mul_pos ha_pos h20
  have h23 : 1 / a * (a * (m / (8 * K))) = m / (8 * K) := by
    field_simp [ha_pos.ne', h20.ne'] <;> ring
  have h24 : P_card / (m / (8 * K)) * (a * (m / (8 * K))) = a * P_card := by
    field_simp [ha_pos.ne', h20.ne'] <;> ring
  have h25 : 1 / a * (a * (m / (8 * K))) ≤ P_card / (m / (8 * K)) * (a * (m / (8 * K))) := by
    rw [h23, h24] <;> exact h21
  have h26 : 1 / a ≤ P_card / (m / (8 * K)) := by
    calc 1 / a
      = (1 / a * (a * (m / (8 * K)))) / (a * (m / (8 * K))) := by field_simp [hpos.ne'] <;> ring
    _ ≤ (P_card / (m / (8 * K)) * (a * (m / (8 * K)))) / (a * (m / (8 * K))) := by gcongr
    _ = P_card / (m / (8 * K)) := by field_simp [hpos.ne'] <;> ring
  have h16 : 1 / a ≤ 8 * K * P_card / m := by
    have h17 : P_card / (m / (8 * K)) = 8 * K * P_card / m := by
      field_simp [hm_pos.ne', hK_pos.ne'] <;> ring
    rw [h17] at h26
    exact h26
  have h_r_plus : r + 2 * δ ≤ 3 * r := by linarith
  have hC_nonneg : 0 ≤ C := by linarith
  have h_a2 : C * (r + 2 * δ) ≤ 3 * C * r := by
    have h : C * (r + 2 * δ) ≤ C * (3 * r) := mul_le_mul_of_nonneg_left h_r_plus hC_nonneg
    have h2 : C * (3 * r) = 3 * C * r := by ring
    rw [h2] at h; exact h
  have h_b2 : 0 ≤ C * (r + 2 * δ) := by
    have h_b1 : 0 ≤ r + 2 * δ := by linarith
    exact mul_nonneg hC_nonneg h_b1
  have h_d2 : 0 ≤ 1 / a := by positivity
  have h_c2 : 0 ≤ 8 * K * P_card / m := by positivity
  have h_mul : (C * (r + 2 * δ)) * (1 / a) ≤ (3 * C * r) * (8 * K * P_card / m) := by
    have h_3Cr_nonneg : 0 ≤ 3 * C * r := by
      have h1 : 0 ≤ C := by linarith
      have h2 : 0 ≤ r := by linarith [hr, hδ]
      positivity
    calc (C * (r + 2 * δ)) * (1 / a)
      ≤ (3 * C * r) * (1 / a) := by gcongr
      _ ≤ (3 * C * r) * (8 * K * P_card / m) := by gcongr
  have h_nonneg2 : 0 ≤ C * r * P_card / m := by
    have h1 : 0 ≤ C := by linarith
    have h2 : 0 ≤ r := by linarith [hr, hδ]
    have h3 : 0 ≤ P_card := by linarith
    have h4 : 0 ≤ m := by linarith [hm_pos]
    have h5 : 0 ≤ C * r := mul_nonneg h1 h2
    have h6 : 0 ≤ C * r * P_card := mul_nonneg h5 h3
    exact div_nonneg h6 h4
  have h_final : 3 * C * r * (8 * K * P_card / m) ≤ 100 * C * L / m * r * P_card := by
    have h_eq : 3 * C * r * (8 * K * P_card / m) = (24 * K) * (C * r * P_card / m) := by
      field_simp [hm_pos.ne'] <;> ring
    rw [h_eq]
    have h_eq2 : 100 * C * L / m * r * P_card = (100 * L) * (C * r * P_card / m) := by
      field_simp [hm_pos.ne'] <;> ring
    rw [h_eq2]
    exact mul_le_mul_of_nonneg_right h24K h_nonneg2
  calc I_card
    ≤ C * (r + 2 * δ) / a := h13
    _ = (C * (r + 2 * δ)) * (1 / a) := by ring
    _ ≤ (3 * C * r) * (8 * K * P_card / m) := h_mul
    _ = 3 * C * r * (8 * K * P_card / m) := by ring
    _ ≤ 100 * C * L / m * r * P_card := h_final

/-- Final mass bound calculation. -/
lemma mass_bound_final (K L C δ m P_card : ℝ)
    (hC_pos : 0 < C) (hδ : 0 < δ) (hm_pos : 0 < m)
    (hP_nonneg : 0 ≤ P_card) (h4K : 4 * K ≤ 50 * L) :
    4 * K * C * δ * P_card + m / 4 ≤ C * δ * 50 * L * P_card + m / 2 := by
  have hC_nonneg : 0 ≤ C := by linarith
  have hδ_nonneg : 0 ≤ δ := by linarith
  have h_part1 : 4 * K * C * δ * P_card ≤ C * δ * 50 * L * P_card := by
    have h61 : 0 ≤ C * δ := by positivity
    have h62 : 4 * K * (C * δ) ≤ 50 * L * (C * δ) := mul_le_mul_of_nonneg_right h4K h61
    have h63 : 0 ≤ P_card := hP_nonneg
    have h64 : 4 * K * (C * δ) * P_card ≤ 50 * L * (C * δ) * P_card :=
      mul_le_mul_of_nonneg_right h62 h63
    have h65 : 4 * K * (C * δ) * P_card = 4 * K * C * δ * P_card := by ring
    have h66 : 50 * L * (C * δ) * P_card = C * δ * 50 * L * P_card := by ring
    rw [h65, h66] at h64
    exact h64
  have h_part2 : m / 4 ≤ m / 2 := by linarith
  linarith

/-! ============================================================================
   Main extraction theorem
   ============================================================================ -/

/-- Helper: if `a ≤ c * b` and `c > 0`, then `a / c ≤ b`. -/
lemma sum_div_ineq {a b c : ℝ} (hc : 0 < c) (h : a ≤ c * b) : a / c ≤ b := by
  have hne : c ≠ 0 := hc.ne'
  by_contra h2
  have h3 : a / c > b := not_le.mp h2
  have h4 : c * (a / c) > c * b := mul_lt_mul_of_pos_left h3 hc
  have h5 : c * (a / c) = a := by
    have h6 : c * (a / c) = (a / c) * c := by ring
    rw [h6, div_mul_cancel₀ a hne]
  rw [h5] at h4
  linarith

/-- Additive partition of an arbitrary set E by measurable, pairwise disjoint cells.

    If `V i` are measurable and pairwise disjoint, then for any `E` (not necessarily
    measurable), the measure of `E ∩ ⋃ i ∈ s, V i` equals the sum of `m (E ∩ V i)`.
    Proof uses the Carathéodory criterion: each measurable `V i` splits `E` additively. -/
lemma measure_inter_finset_union_helper {α : Type*} [MeasurableSpace α] {m : Measure α} {E : Set α} {ι : Type*}
    (V : ι → Set α) (hV_meas : ∀ i, MeasurableSet (V i))
    (hV_disj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (s : Finset ι) :
    m (E ∩ ⋃ i ∈ s, V i) = ∑ i ∈ s, m (E ∩ V i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    have h_empty : (V i ∩ (⋃ j ∈ s, V j)) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨hxi, hxj⟩
      have h_exists : ∃ (j : ι), j ∈ s ∧ x ∈ V j := by
        simpa [Finset.mem_biUnion] using hxj
      rcases h_exists with ⟨j, hj, hxj'⟩
      have h_ne : i ≠ j := by
        intro h_eq
        exact hi (h_eq ▸ hj)
      have h_d : Disjoint (V i) (V j) := hV_disj i j h_ne
      have h_empty2 : V i ∩ V j = ∅ := Set.disjoint_iff_inter_eq_empty.mp h_d
      have h_contra : x ∈ (V i ∩ V j) := ⟨hxi, hxj'⟩
      rw [h_empty2] at h_contra
      simpa using h_contra
    have h_disj : Disjoint (V i) (⋃ j ∈ s, V j) :=
      Set.disjoint_iff_inter_eq_empty.mpr h_empty
    let A : Set α := E ∩ (V i ∪ ⋃ j ∈ s, V j)
    have h1 : A ∩ V i = E ∩ V i := by
      ext y
      simp only [A, Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨⟨hE, h | h⟩, hVi⟩
        · exact ⟨hE, hVi⟩
        · exfalso
          have h_contra : y ∈ V i ∩ (⋃ j ∈ s, V j) := ⟨hVi, h⟩
          rw [h_empty] at h_contra
          simpa using h_contra
      · rintro ⟨hE, hVi⟩
        exact ⟨⟨hE, Or.inl hVi⟩, hVi⟩
    have h2 : A \ V i = E ∩ ⋃ j ∈ s, V j := by
      ext y
      simp only [A, Set.mem_diff, Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨⟨hE, h | h⟩, hnVi⟩
        · exfalso; exact hnVi h
        · exact ⟨hE, h⟩
      · rintro ⟨hE, hU⟩
        exact ⟨⟨hE, Or.inr hU⟩, fun hVi => by
          have h_contra : y ∈ V i ∩ (⋃ j ∈ s, V j) := ⟨hVi, hU⟩
          rw [h_empty] at h_contra
          simpa using h_contra⟩
    have h3 : m (A ∩ V i) + m (A \ V i) = m A :=
      MeasureTheory.measure_inter_add_sdiff A (hV_meas i)
    have h4 : m A = m (E ∩ V i) + m (E ∩ ⋃ j ∈ s, V j) := by
      rw [h1, h2] at h3
      exact h3.symm
    have h5 : (⋃ j ∈ (insert i s), V j) = V i ∪ (⋃ j ∈ s, V j) := by
      ext y
      simp [Finset.mem_biUnion, Finset.mem_insert]
      <;> tauto
    have h6 : E ∩ ⋃ j ∈ (insert i s), V j = A := by
      rw [h5] <;> rfl
    rw [h6, h4, ih] <;> simp [Finset.sum_insert hi] <;> ring

theorem measure_extract_delta_set_explicit_outer
    {E : Set Point}
    (hE_sub_ball : E ⊆ closedBall (0 : Point) 1)
    (ν : Measure Point)
    {m C : ℝ} (hm_pos : 0 < m) (hC_pos : 0 < C)
    (hνE_ge : ENNReal.ofReal m ≤ ν E)
    (hν_frostman : ∀ (x : Point) (r : ℝ), 0 < r →
      ν (Metric.closedBall x r) ≤ ENNReal.ofReal (C * r))
    {δ : ℝ} (hδ : 0 < δ) (hδ_lt_one : δ < 1) :
    ∃ (P : Set Point), P ⊆ E ∧ P.Nonempty ∧ P.Finite ∧
      IsDeltaSet δ 1 (100 * C * (max 0 (Real.log (2000 * C / (m * δ))) + 1) / m) hδ
        (by norm_num) (by positivity) P ∧
      ν E ≤ ENNReal.ofReal (C * δ * 50 * (max 0 (Real.log (2000 * C / (m * δ))) + 1) * (P.ncard : ℝ)) +
        ENNReal.ofReal m / 2 := by
  let L_raw : ℝ := Real.log (2000 * C / (m * δ))
  let L : ℝ := max 0 L_raw + 1
  have hm_le_C : m ≤ C := by
    have h1 : ν E ≤ ν (closedBall (0 : Point) 1) := measure_mono hE_sub_ball
    have h2 : ν (closedBall (0 : Point) 1) ≤ ENNReal.ofReal (C * (1 : ℝ)) := hν_frostman 0 1 (by norm_num)
    have h3 : ν E ≤ ENNReal.ofReal C := by simpa using h1.trans h2
    have h4 : ENNReal.ofReal m ≤ ν E := hνE_ge
    have h5 : ENNReal.ofReal m ≤ ENNReal.ofReal C := h4.trans h3
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h5
  have hL_ge_one : 1 ≤ L := by
    dsimp only [L, L_raw]
    have h : 0 ≤ max 0 (Real.log (2000 * C / (m * δ))) := le_max_left _ _
    have h' : 1 ≤ max 0 (Real.log (2000 * C / (m * δ))) + 1 := by
      calc 1
        = 0 + 1 := by ring
      _ ≤ max 0 (Real.log (2000 * C / (m * δ))) + 1 := by gcongr
    exact h'
  have hL_nonneg : 0 ≤ L := le_trans (by norm_num) hL_ge_one
  have hL_pos : 0 < L := by
    have h : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le h hL_ge_one

  -- Step 1: Maximal (2δ)-separated set
  let δn : NNReal := ⟨δ, hδ.le⟩
  let εn : NNReal := 2 * δn
  have hδn_pos : 0 < δn := by exact_mod_cast hδ
  have hε_pos : 0 < εn := mul_pos (by norm_num) hδn_pos
  have hE_bounded : Bornology.IsBounded E :=
    Metric.isBounded_closedBall.subset hE_sub_ball
  have h_pack_ne_top : Metric.packingNumber εn E ≠ ⊤ :=
    Vendored.MeasureTheory.FractalGeometry.FrostmanLemma.bounded_packingNumber_ne_top hE_bounded hε_pos
  let P0 : Set Point := Metric.maximalSeparatedSet εn E
  have hP0_sub : P0 ⊆ E := Metric.maximalSeparatedSet_subset (ε := εn) (A := E)
  have hP0_sep : Metric.IsSeparated εn P0 := Metric.isSeparated_maximalSeparatedSet (ε := εn)
  have hP0_cover : Metric.IsCover εn E P0 := Metric.isCover_maximalSeparatedSet h_pack_ne_top
  have hP0_finite : P0.Finite := by
    have h : P0.encard = Metric.packingNumber εn E := Metric.encard_maximalSeparatedSet h_pack_ne_top
    have h2 : P0.encard ≠ ⊤ := by rw [h]; exact h_pack_ne_top
    exact Set.encard_ne_top_iff.mp h2
  let P0fin : Finset Point := hP0_finite.toFinset
  have h_coe : (P0fin : Set Point) = P0 := hP0_finite.coe_toFinset

  let N := P0fin.card
  let e : Fin N → Point := fun i => (Finset.equivFin P0fin).symm i
  have h_e_mem : ∀ i, e i ∈ P0fin := by
    intro i; exact (Finset.equivFin P0fin).symm i |>.property
  have h_e_surj : ∀ p ∈ P0fin, ∃ i : Fin N, e i = p := by
    intro p hp
    let p' : {x // x ∈ P0fin} := ⟨p, hp⟩
    let i : Fin N := (Finset.equivFin P0fin) p'
    have h4 : e i = (p' : Point) := by
      dsimp only [e, i]
      have h5 : (Finset.equivFin P0fin).symm ((Finset.equivFin P0fin) p') = p' :=
        (Finset.equivFin P0fin).left_inv p'
      exact_mod_cast h5
    refine ⟨i, ?_⟩
    rw [h4] <;> rfl

  -- Covering: E ⊆ ⋃ closedBall p (2δ)
  have h_cover_balls : E ⊆ ⋃ p ∈ P0fin, Metric.closedBall p (2 * δ) := by
    intro x hx
    have h : ∃ p ∈ P0, edist x p ≤ εn := hP0_cover hx
    rcases h with ⟨p, hp, hdist⟩
    have hp' : p ∈ P0fin := by
      have h9 : p ∈ (P0fin : Set Point) := by rw [h_coe]; exact hp
      exact h9
    have hdist' : dist x p ≤ 2 * δ := by exact_mod_cast hdist
    have h_goal : x ∈ Metric.closedBall p (2 * δ) := by
      simpa [Metric.mem_closedBall] using hdist'
    exact Set.mem_iUnion₂.mpr ⟨p, hp', h_goal⟩

  -- Step 2: Disjoint cells
  let U : Fin N → Set Point := fun i => Metric.closedBall (e i) (2 * δ)
  have hU_meas : ∀ i, MeasurableSet (U i) := by
    intro i; exact Metric.isClosed_closedBall.measurableSet
  have hU_sub_ball : ∀ i, U i ⊆ Metric.closedBall (e i) (2 * δ) := by
    intro i; simp [U] <;> tauto
  have hU_cover : E ⊆ ⋃ i, U i := by
    intro x hx
    have h : x ∈ ⋃ p ∈ P0fin, Metric.closedBall p (2 * δ) := h_cover_balls hx
    rcases Set.mem_iUnion₂.mp h with ⟨p, hp, hball⟩
    rcases h_e_surj p hp with ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, hball⟩

  let V : Fin N → Set Point := fun i =>
    U i \ ⋃ j ∈ (Finset.univ.filter (fun j : Fin N => j < i)), U j
  have hV_meas : ∀ i, MeasurableSet (V i) := by
    intro i
    have h1 : MeasurableSet (U i) := hU_meas i
    have h2 : MeasurableSet (⋃ j ∈ (Finset.univ.filter (fun j : Fin N => j < i)), U j) := by
      exact MeasurableSet.biUnion (Finset.countable_toSet _) (fun j _ => hU_meas j)
    exact h1.diff h2
  have hV_sub_U : ∀ i, V i ⊆ U i := by intro i; simp [V] <;> tauto
  have hV_sub_ball : ∀ i, V i ⊆ Metric.closedBall (e i) (2 * δ) := by
    intro i; exact (hV_sub_U i).trans (hU_sub_ball i)
  let EV : Fin N → Set Point := fun i => E ∩ V i
  have hEV_sub_E : ∀ i, EV i ⊆ E := by intro i; simp [EV] <;> tauto
  have hEV_sub_ball : ∀ i, EV i ⊆ Metric.closedBall (e i) (2 * δ) := by
    intro i
    have h : EV i ⊆ V i := by
      intro x hx
      exact hx.2
    exact h.trans (hV_sub_ball i)
  have hV_disj : ∀ i j, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hne
    by_cases h : i < j
    · have h2 : i ∈ (Finset.univ.filter (fun k : Fin N => k < j)) := by simp [h]
      have h4 : U i ⊆ ⋃ k ∈ (Finset.univ.filter (fun k : Fin N => k < j)), U k :=
        Set.subset_biUnion_of_mem h2
      have h3 : V j ⊆ U j \ U i := by
        dsimp only [V]; exact Set.diff_subset_diff_right h4
      have h5 : V i ⊆ U i := hV_sub_U i
      rw [Set.disjoint_left]; intro x hxi hxj
      have h6 : x ∈ U i := h5 hxi
      have h7 : x ∉ U i := h3 hxj |>.2
      exact h7 h6
    · have h' : j < i := by omega
      have h2 : j ∈ (Finset.univ.filter (fun k : Fin N => k < i)) := by simp [h']
      have h4 : U j ⊆ ⋃ k ∈ (Finset.univ.filter (fun k : Fin N => k < i)), U k :=
        Set.subset_biUnion_of_mem h2
      have h3 : V i ⊆ U i \ U j := by
        dsimp only [V]; exact Set.diff_subset_diff_right h4
      have h5 : V j ⊆ U j := hV_sub_U j
      rw [Set.disjoint_left]; intro x hxi hxj
      have h6 : x ∈ U j := h5 hxj
      have h7 : x ∉ U j := h3 hxi |>.2
      exact h7 h6

  have hV_cover : E ⊆ ⋃ i, V i := by
    intro x hx
    have h_in_U : x ∈ ⋃ i, U i := hU_cover hx
    rcases Set.mem_iUnion.mp h_in_U with ⟨i, hxi⟩
    let S : Finset (Fin N) := Finset.univ.filter (fun j => x ∈ U j)
    have hS_nonempty : S.Nonempty := ⟨i, by simp [S, hxi]⟩
    let i0 := Finset.min' S hS_nonempty
    have hi0S : i0 ∈ S := Finset.min'_mem S hS_nonempty
    have hxi0 : x ∈ U i0 := by simpa [S] using hi0S
    have h_forall : ∀ j ∈ (Finset.univ.filter (fun j : Fin N => j < i0)), x ∉ U j := by
      intro j hj
      have h_j_lt : j < i0 := by simpa [S] using (Finset.mem_filter.mp hj).2
      intro h
      have h_jS : j ∈ S := by simpa [S] using h
      have h_contra : ¬(j < i0) := not_lt.mpr (Finset.min'_le S j h_jS)
      exact h_contra h_j_lt
    have h_xin_V : x ∈ V i0 := by
      dsimp only [V]; exact ⟨hxi0, by simpa using h_forall⟩
    exact Set.mem_iUnion.mpr ⟨i0, h_xin_V⟩

  have hV_partition_measure : ∑ i : Fin N, ν (EV i) = ν E := by
    have h_main : ∀ (s : Finset (Fin N)), ν (E ∩ ⋃ i ∈ s, V i) = ∑ i ∈ s, ν (EV i) :=
      measure_inter_finset_union_helper V hV_meas hV_disj
    have h4 : E ⊆ ⋃ i : Fin N, V i := hV_cover
    have h5 : E ∩ ⋃ i : Fin N, V i = E := by
      rw [Set.inter_eq_left.mpr h4]
    have h6 : ν (E ∩ ⋃ i ∈ (Finset.univ : Finset (Fin N)), V i) = ∑ i ∈ (Finset.univ : Finset (Fin N)), ν (EV i) :=
      h_main (Finset.univ)
    have h7 : (⋃ i ∈ (Finset.univ : Finset (Fin N)), V i) = ⋃ i : Fin N, V i := by
      ext x; simp
    rw [h7] at h6
    rw [h5] at h6
    exact h6.symm

  -- All cell measures finite
  have h_all_finite : ∀ i, ν (EV i) ≠ ⊤ := by
    intro i
    have h3 : ν (EV i) ≤ ν (Metric.closedBall (e i) (2 * δ)) := measure_mono (hEV_sub_ball i)
    have h4 : ν (Metric.closedBall (e i) (2 * δ)) ≤ ENNReal.ofReal (C * (2 * δ)) :=
      hν_frostman (e i) (2 * δ) (by positivity)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h3.trans h4)

  -- Step 3: Weights
  let w : Fin N → ℝ := fun i => (ν (EV i)).toReal
  have hw_nonneg : ∀ i, 0 ≤ w i := by intro i; exact ENNReal.toReal_nonneg
  have h_sum_w : ∑ i : Fin N, w i = (ν E).toReal := by
    have h1 : ∑ i : Fin N, w i = (∑ i : Fin N, ν (EV i)).toReal := by
      rw [ENNReal.toReal_sum (hf := fun i _ => h_all_finite i)] <;> rfl
    rw [h1, hV_partition_measure]

  have hνE_ne_top : ν E ≠ ⊤ := by
    have h3 : ν E ≤ ν (closedBall (0 : Point) 1) := measure_mono hE_sub_ball
    have h4 : ν (closedBall (0 : Point) 1) ≤ ENNReal.ofReal (C * 1) := hν_frostman 0 1 (by norm_num)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h3.trans h4)

  have hνE_pos : 0 < ν E := by
    have h1 : 0 < ENNReal.ofReal m := ENNReal.ofReal_pos.mpr hm_pos
    exact lt_of_lt_of_le h1 hνE_ge

  let mE : ℝ := (ν E).toReal
  have hmE_pos : 0 < mE := ENNReal.toReal_pos hνE_pos.ne' hνE_ne_top
  have hm_le_mE : m ≤ mE := by
    have h1 : ENNReal.ofReal m ≤ ν E := hνE_ge
    have h2 : (ENNReal.ofReal m).toReal ≤ (ν E).toReal :=
      ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hνE_ne_top |>.mpr h1
    have h3 : (ENNReal.ofReal m).toReal = m := ENNReal.toReal_ofReal (by linarith)
    rw [h3] at h2; exact h2

  have h_sum_w' : ∑ i : Fin N, w i = mE := by
    rw [h_sum_w] <;> rfl

  -- Packing bound: N ≤ 100/δ²
  have hP0_sub_ball : P0 ⊆ closedBall (0 : Point) 1 := hP0_sub.trans hE_sub_ball
  have hN_bound : (N : ℝ) ≤ 200 / δ^2 := by
    have hP0_sep' : Metric.IsSeparated (ENNReal.ofReal (2 * δ)) P0 := by
      have h_eq : (↑εn : ENNReal) = ENNReal.ofReal (2 * δ) := by
        have h1 : (↑δn : ENNReal) = ENNReal.ofReal δ := by
          have h2 : (↑δn : ℝ) = δ := by
            change δn.val = δ
            rfl
          have h3 : (↑δn : ENNReal) = ENNReal.ofReal (↑δn : ℝ) := by
            simp
          rw [h3, h2]
        calc (↑εn : ENNReal)
          = 2 * (↑δn : ENNReal) := by simp [εn] <;> rfl
          _ = 2 * ENNReal.ofReal δ := by rw [h1]
          _ = ENNReal.ofReal (2 * δ) := by
            have h2 : ENNReal.ofReal (2 * δ) = (2 : ENNReal) * ENNReal.ofReal δ := by
              rw [ENNReal.ofReal_mul] <;> simp
            exact h2.symm
      rw [h_eq] at hP0_sep
      exact hP0_sep
    have h1 : P0.ncard ≤ Nat.ceil (100 / δ^2) :=
      separated_set_unit_ball_card_le hδ hδ_lt_one.le hP0_sep' hP0_sub_ball hP0_finite
    have h2 : P0.ncard = ↑N := by
      have h3 : P0 = (P0fin : Set Point) := h_coe.symm
      rw [h3]; simp [N]
    rw [h2] at h1
    have h4 : (N : ℝ) ≤ ↑(Nat.ceil (100 / δ^2)) := by exact_mod_cast h1
    have h5 : ↑(Nat.ceil (100 / δ^2)) ≤ 100 / δ^2 + 1 := by
      have h_lt : ↑(Nat.ceil (100 / δ^2)) < 100 / δ^2 + 1 := Nat.ceil_lt_add_one (show 0 ≤ 100 / δ^2 from by positivity)
      exact h_lt.le
    have h6 : 100 / δ^2 + 1 ≤ 200 / δ^2 := by
      have h71 : 0 < δ^2 := by positivity
      have h72 : 1 ≤ 100 / δ^2 := by
        have h73 : δ^2 ≤ 1 := by nlinarith [hδ_lt_one]
        calc (1 : ℝ)
          = δ^2 / δ^2 := by field_simp [h71.ne'] <;> ring
          _ ≤ 100 / δ^2 := by gcongr <;> nlinarith
      have h74 : 100 / δ^2 + 1 ≤ 100 / δ^2 + 100 / δ^2 := by gcongr
      have h75 : 100 / δ^2 + 100 / δ^2 = 200 / δ^2 := by ring
      linarith
    linarith

  -- Step 4: Light/heavy threshold
  have hN_pos : 0 < N := by
    by_contra h
    have hN0 : N = 0 := by omega
    have hP0_empty : P0 = ∅ := by
      have h1 : P0fin = ∅ := by
        simpa [N, Finset.card_eq_zero] using hN0
      have h2 : (P0fin : Set Point) = ∅ := by rw [h1] <;> simp
      rw [h_coe] at h2; exact h2
    have hE_empty : E = ∅ := by
      have h3 : E ⊆ ⋃ p ∈ (P0fin : Set Point), Metric.closedBall p (2 * δ) := h_cover_balls
      have h4 : (P0fin : Set Point) = ∅ := by
        have h5 : P0fin = ∅ := by simpa [N, Finset.card_eq_zero] using hN0
        rw [h5] <;> simp
      rw [h4] at h3
      simpa using h3
    rw [hE_empty] at hνE_pos; simp at hνE_pos
  let τ : ℝ := m / (4 * (N : ℝ))
  have hτ_pos : 0 < τ := by
    dsimp only [τ]
    have hN_pos' : (N : ℝ) > 0 := by exact_mod_cast hN_pos
    positivity

  let S_heavy : Finset (Fin N) := Finset.univ.filter (fun i => τ ≤ w i)
  have h_light_mass : ∑ i ∈ Finset.univ \ S_heavy, w i ≤ m / 4 := by
    have h1 : ∀ i ∈ Finset.univ \ S_heavy, w i ≤ τ := by
      intro i hi
      have h2 : i ∉ S_heavy := by simpa using hi
      have h3 : ¬(τ ≤ w i) := by simpa [S_heavy] using h2
      linarith
    have h4 : ∑ i ∈ Finset.univ \ S_heavy, w i ≤ ∑ i ∈ Finset.univ \ S_heavy, τ :=
      Finset.sum_le_sum h1
    have h5 : ∑ i ∈ Finset.univ \ S_heavy, τ = ((Finset.univ \ S_heavy).card : ℝ) * τ := by
      simp [Finset.sum_const] <;> ring
    rw [h5] at h4
    have h6 : ((Finset.univ \ S_heavy).card : ℝ) ≤ (N : ℝ) := by
      have h7 : (Finset.univ \ S_heavy) ⊆ (Finset.univ : Finset (Fin N)) := by simp
      have h8 : (Finset.univ \ S_heavy).card ≤ Finset.univ.card := Finset.card_le_card h7
      have h9 : (Finset.univ : Finset (Fin N)).card = N := by simp
      rw [h9] at h8
      exact_mod_cast h8
    have h10 : ((Finset.univ \ S_heavy).card : ℝ) * τ ≤ (N : ℝ) * τ := by gcongr
    have h11 : (N : ℝ) * τ = m / 4 := by
      dsimp only [τ] <;> field_simp [hN_pos.ne'] <;> ring
    rw [h11] at h10
    linarith

  have h_heavy_mass : ∑ i ∈ S_heavy, w i ≥ m / 2 := by
    have h1 : ∑ i ∈ Finset.univ, w i = ∑ i ∈ S_heavy, w i + ∑ i ∈ Finset.univ \ S_heavy, w i := by
      have h_disj : Disjoint S_heavy (Finset.univ \ S_heavy) := by
        exact Finset.disjoint_sdiff
      rw [←Finset.sum_union h_disj]
      have h2 : S_heavy ∪ (Finset.univ \ S_heavy) = Finset.univ := by simp
      rw [h2]
    have h_sum_w2 : ∑ i ∈ S_heavy, w i + ∑ i ∈ Finset.univ \ S_heavy, w i = mE := by
      rw [←h1, h_sum_w']
    linarith [hm_le_mE, h_light_mass, h_sum_w2]

  -- Step 5: Dyadic ranges
  -- Range k: τ * 2^k ≤ w i < τ * 2^(k+1)
  -- Number of ranges K
  have h_w_max_le : ∀ i, w i ≤ 2 * C * δ := by
    intro i
    have h1 : ν (EV i) ≤ ν (Metric.closedBall (e i) (2 * δ)) := measure_mono (hEV_sub_ball i)
    have h2 : ν (Metric.closedBall (e i) (2 * δ)) ≤ ENNReal.ofReal (C * (2 * δ)) :=
      hν_frostman (e i) (2 * δ) (by positivity)
    have h3 : ν (EV i) ≤ ENNReal.ofReal (C * (2 * δ)) := h1.trans h2
    have h4 : (ν (EV i)).toReal ≤ (ENNReal.ofReal (C * (2 * δ))).toReal :=
      ENNReal.toReal_le_toReal (h_all_finite i) ENNReal.ofReal_ne_top |>.mpr h3
    have h5 : (ENNReal.ofReal (C * (2 * δ))).toReal = C * (2 * δ) := by
      rw [ENNReal.toReal_ofReal (by positivity)]
    rw [h5] at h4
    have h6 : C * (2 * δ) = 2 * C * δ := by ring
    rw [h6] at h4
    exact h4

  let K : ℕ := Nat.ceil (Real.log (800 * C / (m * δ)) / Real.log 2) + 2
  have hK_pos : 0 < K := by simp [K]

  have h_range_bound : ∀ i ∈ S_heavy, w i < τ * (2 : ℝ) ^ K := by
    intro i hi
    have hwi_le : w i ≤ 2 * C * δ := h_w_max_le i
    dsimp only [K]
    have h11 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set x : ℝ := Real.log (800 * C / (m * δ)) / Real.log 2 with hx_def
    have h9 : (Nat.ceil x : ℝ) ≥ x := Nat.le_ceil _
    have h10 : (K : ℝ) ≥ x + 2 := by
      simp [K] <;> linarith
    have h12 : (K : ℝ) * Real.log 2 ≥ Real.log (800 * C / (m * δ)) + 2 * Real.log 2 := by
      calc (K : ℝ) * Real.log 2
        ≥ (x + 2) * Real.log 2 := by gcongr
        _ = Real.log (800 * C / (m * δ)) + 2 * Real.log 2 := by
          simp only [hx_def]
          field_simp [h11.ne'] <;> ring
    have h13 : Real.log ((2 : ℝ) ^ K) = (K : ℝ) * Real.log 2 := by
      simpa [Real.log_pow] using by ring
    have h14 : Real.log (800 * C / (m * δ)) + 2 * Real.log 2 = Real.log (3200 * C / (m * δ)) := by
      have h15 : 0 < 800 * C / (m * δ) := by positivity
      have h16 : 2 * Real.log 2 = Real.log 4 := by
        have h : Real.log ((2 : ℝ) ^ 2) = (2 : ℝ) * Real.log 2 := Real.log_pow (2 : ℝ) 2
        have h2 : Real.log 4 = 2 * Real.log 2 := by
          have h3 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          rw [h3]
          exact h
        exact h2.symm
      rw [h16]
      have h17 : Real.log (800 * C / (m * δ)) + Real.log 4 = Real.log ((800 * C / (m * δ)) * 4) := by
        rw [Real.log_mul (ne_of_gt h15) (by norm_num)]
      rw [h17] <;> ring_nf
    rw [←h13] at h12
    rw [h14] at h12
    have h16 : (2 : ℝ) ^ K ≥ 3200 * C / (m * δ) := by
      exact Real.log_le_log_iff (by positivity) (by positivity) |>.mp h12
    have h17 : τ * (2 : ℝ) ^ K ≥ τ * (3200 * C / (m * δ)) := by gcongr
    have h18 : τ * (3200 * C / (m * δ)) = (m / (4 * (N : ℝ))) * (3200 * C / (m * δ)) := by rfl
    have h19 : (m / (4 * (N : ℝ))) * (3200 * C / (m * δ)) = 800 * C / ((N : ℝ) * δ) := by
      field_simp [hm_pos.ne', hδ.ne'] <;> ring
    have h20 : 800 * C / ((N : ℝ) * δ) ≥ 4 * C * δ := by
      have h21 : (N : ℝ) ≤ 200 / δ^2 := hN_bound
      have h22 : 800 * C / ((N : ℝ) * δ) ≥ 800 * C / ((200 / δ^2) * δ) := by
        gcongr <;> positivity
      have h23 : 800 * C / ((200 / δ^2) * δ) = 4 * C * δ := by
        field_simp [hδ.ne'] <;> ring
      rw [h23] at h22
      linarith
    have h24 : 2 * C * δ < 4 * C * δ := by
      have h25 : 0 < C * δ := mul_pos hC_pos hδ
      linarith
    calc w i ≤ 2 * C * δ := hwi_le
      _ < 4 * C * δ := h24
      _ ≤ 800 * C / ((N : ℝ) * δ) := h20
      _ = τ * (3200 * C / (m * δ)) := by rw [h18, h19]
      _ ≤ τ * (2 : ℝ) ^ K := h17

  -- Define range function
  let range_k (k : ℕ) (i : Fin N) : Prop := τ * (2 : ℝ)^k ≤ w i ∧ w i < τ * (2 : ℝ)^(k+1)
  have h_cover : ∀ i ∈ S_heavy, ∃ k < K, range_k k i := by
    intro i hi
    have hwi_ge : τ ≤ w i := (Finset.mem_filter.mp hi).2
    have hwi_lt : w i < τ * (2 : ℝ)^K := h_range_bound i hi
    let h_exists : ∃ k : ℕ, w i < τ * (2 : ℝ)^k := ⟨K, hwi_lt⟩
    let k : ℕ := Nat.find h_exists
    have hk_le_K : k ≤ K := Nat.find_min' h_exists hwi_lt
    have hk_pos : 0 < k := by
      by_contra h0
      have h_k0 : k = 0 := by omega
      have h : w i < τ * (2 : ℝ)^k := Nat.find_spec h_exists
      rw [h_k0] at h
      have h' : (2 : ℝ)^0 = 1 := by norm_num
      rw [h'] at h
      have h'' : w i < τ := by simpa [mul_one] using h
      exact not_le.mpr h'' hwi_ge
    let k' := k - 1
    have hk'_lt_K : k' < K := by omega
    have hk'_lt : w i < τ * (2 : ℝ)^(k'+1) := by
      have h : k' + 1 = k := by omega
      rw [h]
      exact Nat.find_spec h_exists
    have hk'_ge : τ * (2 : ℝ)^k' ≤ w i := by
      have h : k' < k := by omega
      have h2 : ¬(w i < τ * (2 : ℝ)^k') := Nat.find_min h_exists h
      linarith
    exact ⟨k', hk'_lt_K, hk'_ge, hk'_lt⟩

  have h_disj : ∀ i ∈ S_heavy, ∀ k l, range_k k i → range_k l i → k = l := by
    intro i _ k l hk hl
    by_contra hne
    by_cases h : k < l
    · have h1 : w i < τ * (2 : ℝ)^(k+1) := hk.2
      have h2 : τ * (2 : ℝ)^l ≤ w i := hl.1
      have h3 : k + 1 ≤ l := by omega
      have h4 : (2 : ℝ)^(k+1) ≤ (2 : ℝ)^l := by
        exact pow_le_pow_right₀ (by norm_num) h3
      have h5 : τ * (2 : ℝ)^(k+1) ≤ τ * (2 : ℝ)^l := by
        have h6 : 0 ≤ τ := by linarith [hτ_pos]
        exact mul_le_mul_of_nonneg_left h4 h6
      have h_contra : τ * (2 : ℝ)^l < τ * (2 : ℝ)^(k+1) := by
        calc τ * (2 : ℝ)^l
          ≤ w i := h2
        _ < τ * (2 : ℝ)^(k+1) := h1
      exact not_le.mpr h_contra h5
    · have h' : l < k := by omega
      have h1 : w i < τ * (2 : ℝ)^(l+1) := hl.2
      have h2 : τ * (2 : ℝ)^k ≤ w i := hk.1
      have h3 : l + 1 ≤ k := by omega
      have h4 : (2 : ℝ)^(l+1) ≤ (2 : ℝ)^k := by
        exact pow_le_pow_right₀ (by norm_num) h3
      have h5 : τ * (2 : ℝ)^(l+1) ≤ τ * (2 : ℝ)^k := by
        have h6 : 0 ≤ τ := by linarith [hτ_pos]
        exact mul_le_mul_of_nonneg_left h4 h6
      have h_contra : τ * (2 : ℝ)^k < τ * (2 : ℝ)^(l+1) := by
        calc τ * (2 : ℝ)^k
          ≤ w i := h2
        _ < τ * (2 : ℝ)^(l+1) := h1
      exact not_le.mpr h_contra h5

  -- Step 6: Select range maximizing n_k * 2^k
  let R : ℕ → Finset (Fin N) := fun k => S_heavy.filter (range_k k)
  let n : ℕ → ℕ := fun k => (R k).card
  let score : ℕ → ℝ := fun k => (n k : ℝ) * (2 : ℝ)^k

  have h_sum_scores : ∑ k ∈ Finset.range K, score k ≥ (∑ i ∈ S_heavy, w i) / (2 * τ) := by
    have h1 : ∀ k ∈ Finset.range K, ∑ i ∈ R k, w i ≥ τ * score k := by
      intro k _
      have h2 : ∀ i ∈ R k, τ * (2 : ℝ)^k ≤ w i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2.1
      calc ∑ i ∈ R k, w i
        ≥ ∑ i ∈ R k, (τ * (2 : ℝ)^k) := Finset.sum_le_sum h2
        _ = (n k : ℝ) * (τ * (2 : ℝ)^k) := by simp [n, Finset.sum_const] <;> ring
        _ = τ * score k := by simp [score] <;> ring
    have h3 : ∑ k ∈ Finset.range K, ∑ i ∈ R k, w i = ∑ i ∈ S_heavy, w i := by
      have h_disj' : ∀ k l, k ≠ l → Disjoint (R k) (R l) := by
        intro k l hne
        rw [Finset.disjoint_left]
        intro i hik hil
        have h1 : range_k k i := (Finset.mem_filter.mp hik).2
        have h2 : range_k l i := (Finset.mem_filter.mp hil).2
        exact hne (h_disj i (Finset.mem_filter.mp hik).1 k l h1 h2)
      have h_union : (⋃ k ∈ Finset.range K, (R k : Set (Fin N))) = (S_heavy : Set (Fin N)) := by
        ext i
        simp only [Set.mem_iUnion₂, Finset.mem_coe, Finset.mem_range]
        constructor
        · rintro ⟨k, _, hki⟩; exact (Finset.mem_filter.mp hki).1
        · intro hi
          rcases h_cover i hi with ⟨k, hkK, hk_range⟩
          exact ⟨k, hkK, Finset.mem_filter.mpr ⟨hi, hk_range⟩⟩
      have h_disj'' : (Finset.range K : Set ℕ).PairwiseDisjoint R := by
        intro k _ l _ hne; exact h_disj' k l hne
      have h_biUnion : (Finset.range K).biUnion R = S_heavy := by
        have h1 : (↑((Finset.range K).biUnion R) : Set (Fin N)) =
            ⋃ k ∈ Finset.range K, ↑(R k) := by
          rw [Finset.coe_biUnion] <;> simp
        have h2 : (↑((Finset.range K).biUnion R) : Set (Fin N)) = (S_heavy : Set (Fin N)) := by
          rw [h1, h_union]
        exact_mod_cast h2
      rw [←Finset.sum_biUnion h_disj'', h_biUnion]
    have h1_upper : ∀ k ∈ Finset.range K, ∑ i ∈ R k, w i ≤ 2 * τ * score k := by
      intro k _
      have h2 : ∀ i ∈ R k, w i ≤ 2 * τ * (2 : ℝ)^k := by
        intro i hi
        have h3 : w i < τ * (2 : ℝ)^(k+1) := (Finset.mem_filter.mp hi).2.2
        have h4 : τ * (2 : ℝ)^(k+1) = 2 * τ * (2 : ℝ)^k := by
          simp [pow_succ] <;> ring
        linarith
      calc ∑ i ∈ R k, w i
        ≤ ∑ i ∈ R k, (2 * τ * (2 : ℝ)^k) := Finset.sum_le_sum h2
        _ = (n k : ℝ) * (2 * τ * (2 : ℝ)^k) := by simp [n, Finset.sum_const] <;> ring
        _ = 2 * τ * score k := by simp [score] <;> ring
    have h4_upper : ∑ k ∈ Finset.range K, ∑ i ∈ R k, w i ≤ ∑ k ∈ Finset.range K, (2 * τ * score k) :=
      Finset.sum_le_sum h1_upper
    rw [h3] at h4_upper
    have h5 : ∑ k ∈ Finset.range K, (2 * τ * score k) = 2 * τ * ∑ k ∈ Finset.range K, score k := by
      rw [Finset.mul_sum]
    rw [h5] at h4_upper
    have hτ_pos' : 0 < τ := hτ_pos
    have h2τ_pos : 0 < (2 * τ : ℝ) := by linarith [hτ_pos]
    have h2τ_ne : (2 * τ : ℝ) ≠ 0 := by linarith [hτ_pos]
    have h_div : (∑ i ∈ S_heavy, w i) / (2 * τ) ≤ ∑ k ∈ Finset.range K, score k :=
      sum_div_ineq h2τ_pos h4_upper
    exact h_div

  -- Pigeonhole: exists k maximizing score k
  have h_pigeonhole : ∃ k ∈ Finset.range K, ∀ j ∈ Finset.range K, score j ≤ score k :=
    Finset.exists_max_image (Finset.range K) score (by simp)

  rcases h_pigeonhole with ⟨kstar, hkK, hscore_max⟩
  have hscore_ge : score kstar ≥ (∑ j ∈ Finset.range K, score j) / (K : ℝ) := by
    have h1 : ∑ j ∈ Finset.range K, score j ≤ (K : ℝ) * score kstar := by
      calc ∑ j ∈ Finset.range K, score j
        ≤ ∑ j ∈ Finset.range K, score kstar := Finset.sum_le_sum hscore_max
        _ = (K : ℝ) * score kstar := by simp [Finset.sum_const] <;> ring
    have hK_pos' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
    calc (∑ j ∈ Finset.range K, score j) / (K : ℝ)
      ≤ ((K : ℝ) * score kstar) / (K : ℝ) := by gcongr
      _ = score kstar := by field_simp [hK_pos'.ne'] <;> ring
  let Pfin : Finset (Fin N) := R kstar
  have hPfin_nonempty : Pfin.Nonempty := by
    by_contra h
    have h_empty : Pfin = ∅ := by simpa using h
    have h_score0 : score kstar = 0 := by
      simp [score, n, Pfin, h_empty]
    have h_contra : (∑ j ∈ Finset.range K, score j) / (K : ℝ) ≤ 0 := by
      calc (∑ j ∈ Finset.range K, score j) / (K : ℝ)
        ≤ score kstar := hscore_ge
      _ = 0 := h_score0
    have h9 : 0 < ∑ i ∈ S_heavy, w i := by linarith [h_heavy_mass]
    have h2τ_pos' : 0 < (2 * τ : ℝ) := by linarith [hτ_pos]
    have h10 : 0 < ∑ j ∈ Finset.range K, score j := by
      have h11 : 0 < (∑ i ∈ S_heavy, w i) / (2 * τ) := div_pos h9 h2τ_pos'
      exact lt_of_lt_of_le h11 h_sum_scores
    have hK_pos' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
    have h_pos : 0 < (∑ j ∈ Finset.range K, score j) / (K : ℝ) := div_pos h10 hK_pos'
    exact False.elim (not_le.mpr h_pos h_contra)

  let P : Set Point := Set.image e Pfin
  have hP_sub_E : P ⊆ E := by
    intro x hx
    rcases hx with ⟨i, _, rfl⟩
    have h1 : e i ∈ P0fin := h_e_mem i
    have h2 : e i ∈ P0 := by
      have h3 : e i ∈ (P0fin : Set Point) := h1
      rw [h_coe] at h3; exact h3
    exact hP0_sub h2

  have hP_sub_P0 : P ⊆ P0 := by
    intro x hx
    rcases hx with ⟨i, _, rfl⟩
    have h1 : e i ∈ P0fin := h_e_mem i
    have h2 : e i ∈ P0 := by
      have h3 : e i ∈ (P0fin : Set Point) := h1
      rw [h_coe] at h3; exact h3
    exact h2

  have hP_sub_E : P ⊆ E := by
    intro x hx
    have h1 : x ∈ P0 := hP_sub_P0 hx
    exact hP0_sub h1

  have hP_finite : P.Finite := Set.Finite.image _ (Finset.finite_toSet _)
  have hP_nonempty : P.Nonempty := by
    rcases hPfin_nonempty with ⟨i, hi⟩
    exact ⟨e i, Set.mem_image_of_mem e hi⟩

  have hP_sep : Metric.IsSeparated εn P := by
    intro x hx y hy hne
    have hx' : x ∈ P0 := hP_sub_P0 hx
    have hy' : y ∈ P0 := hP_sub_P0 hy
    exact hP0_sep hx' hy' hne

  have h_inj : Set.InjOn e Pfin := by
    intro i _ j _ h
    have h' : (Finset.equivFin P0fin).symm i = (Finset.equivFin P0fin).symm j := by simpa [e] using h
    exact (Finset.equivFin P0fin).symm.injective h'

  have hP_card : P.encard = ↑(Pfin.card) := by
    have h_eq1 : P = ↑(Pfin.image e) := by
      ext x; simp [P, Finset.mem_image]
    rw [h_eq1]
    have h2 : (↑(Pfin.image e) : Set Point).encard = ↑(Pfin.image e).card :=
      encard_coe_eq_coe_finsetCard (Finset.image e Pfin)
    rw [h2]
    have h3 : (Pfin.image e).card = Pfin.card := by
      apply Finset.card_image_of_injOn
      exact h_inj
    rw [h3]

  -- Key bounds
  have h_wmin : ∀ i ∈ Pfin, τ * (2 : ℝ)^kstar ≤ w i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.1

  have h_wmax : ∀ i ∈ Pfin, w i < τ * (2 : ℝ)^(kstar+1) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.2

  have h_key : τ * (2 : ℝ)^kstar * (Pfin.card : ℝ) ≥ (∑ i ∈ S_heavy, w i) / (2 * (K : ℝ)) := by
    have h1 : score kstar = (Pfin.card : ℝ) * (2 : ℝ)^kstar := by
      simp [score, n, Pfin] <;> ring
    have h_goal : τ * score kstar ≥ (∑ i ∈ S_heavy, w i) / (2 * (K : ℝ)) := by
      set S_scores : ℝ := ∑ j ∈ Finset.range K, score j with hS_scores_def
      set S_heavy : ℝ := ∑ i ∈ S_heavy, w i with hS_heavy_def
      have hτ_nonneg : 0 ≤ τ := by linarith [hτ_pos]
      have hK_pos' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
      have h_step1 : τ * score kstar ≥ τ * (S_scores / (K : ℝ)) := by
        have h : score kstar ≥ S_scores / (K : ℝ) := hscore_ge
        exact mul_le_mul_of_nonneg_left h hτ_nonneg
      have h_step2 : S_heavy / (2 * τ) ≤ S_scores := h_sum_scores
      have h_step3 : τ * (S_scores / (K : ℝ)) ≥ τ * ((S_heavy / (2 * τ)) / (K : ℝ)) := by
        have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_of_lt hK_pos)
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h_step2 hK_nonneg) hτ_nonneg
      have h_step4 : τ * ((S_heavy / (2 * τ)) / (K : ℝ)) = S_heavy / (2 * (K : ℝ)) := by
        have hτ_ne : τ ≠ 0 := hτ_pos.ne'
        field_simp [hτ_ne]
        <;> ring
      linarith
    have h2 : τ * (2 : ℝ)^kstar * (Pfin.card : ℝ) = τ * score kstar := by
      rw [h1] <;> ring
    rw [h2]
    exact h_goal

  have h_key2 : τ * (2 : ℝ)^kstar * (Pfin.card : ℝ) ≥ m / (8 * (K : ℝ)) := by
    have h_heavy4 : m / 4 ≤ ∑ i ∈ S_heavy, w i := by linarith [h_heavy_mass]
    calc τ * (2 : ℝ)^kstar * (Pfin.card : ℝ)
      ≥ (∑ i ∈ S_heavy, w i) / (2 * (K : ℝ)) := h_key
      _ ≥ (m / 4) / (2 * (K : ℝ)) := by
        gcongr
        <;> exact h_heavy4
      _ = m / (8 * (K : ℝ)) := by ring

  -- Bounds relating K and L
  have h_log2_gt24 : Real.log 2 > (24 : ℝ) / 100 := by
    have h1 : Real.log 4 > 1 := by
      have h2 : Real.exp 1 < (4 : ℝ) := by
        have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
        linarith
      have h4 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h2
      have h5 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h5] at h4
      exact h4
    have h3 : Real.log 4 = 2 * Real.log 2 := by
      calc Real.log 4
        = Real.log (2 * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 := by rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 2 := by ring
    rw [h3] at h1
    linarith
  set y : ℝ := Real.log (2000 * C / (m * δ)) with hy_def
  set x : ℝ := Real.log (800 * C / (m * δ)) / Real.log 2 with hx_def
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_pos800 : 0 < 800 * C / (m * δ) := by positivity
  have h_pos2000 : 0 < 2000 * C / (m * δ) := by positivity
  have h800_lt_2000 : 800 * C / (m * δ) < 2000 * C / (m * δ) := by
    have h1 : 0 < C / (m * δ) := by positivity
    have h2 : 800 * C / (m * δ) = 800 * (C / (m * δ)) := by ring
    have h3 : 2000 * C / (m * δ) = 2000 * (C / (m * δ)) := by ring
    rw [h2, h3]
    exact mul_lt_mul_of_pos_right (by norm_num) h1
  have h_log800_lt_log2000 : Real.log (800 * C / (m * δ)) < Real.log (2000 * C / (m * δ)) :=
    Real.log_lt_log h_pos800 h800_lt_2000
  have h_y_eq_Lraw : y = L_raw := by
    simp [hy_def, L_raw]
    <;> rfl
  have hK_eq : (K : ℝ) = (Nat.ceil x : ℝ) + 2 := by
    have h1 : K = Nat.ceil (Real.log (800 * C / (m * δ)) / Real.log 2) + 2 := by rfl
    rw [h1]
    have h2 : Real.log (800 * C / (m * δ)) / Real.log 2 = x := hx_def.symm
    rw [h2]
    simp [Nat.cast_add]
    <;> ring
  have h_ceil_neg : ∀ (z : ℝ), z ≤ 0 → Nat.ceil z = 0 := by
    intro z hz
    have h6 : Nat.ceil z ≤ 0 := by
      apply Nat.ceil_le.mpr
      linarith
    omega
  have hK_le_2 : x < 0 → (K : ℝ) ≤ 2 := by
    intro hx_neg
    rw [hK_eq]
    have h5 : Nat.ceil x = 0 := h_ceil_neg x (by linarith)
    rw [h5]
    <;> norm_num
  have hK_le_x3 : 0 ≤ x → (K : ℝ) ≤ x + 3 := by
    intro hx
    rw [hK_eq]
    have h5 : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
    linarith
  have h_y_relation : y = x * Real.log 2 + Real.log (5 / 2) := by
    have h_eq : Real.log (2000 * C / (m * δ)) = Real.log (800 * C / (m * δ)) + Real.log (5 / 2) := by
      have h : (2000 * C / (m * δ)) = (800 * C / (m * δ)) * (5 / 2) := by ring
      rw [h, Real.log_mul (ne_of_gt h_pos800) (by norm_num)] <;> ring
    have hy : y = Real.log (2000 * C / (m * δ)) := by simp [hy_def]
    have hx : x = Real.log (800 * C / (m * δ)) / Real.log 2 := by simp [hx_def]
    calc y
      = Real.log (2000 * C / (m * δ)) := hy
    _ = Real.log (800 * C / (m * δ)) + Real.log (5 / 2) := h_eq
    _ = x * Real.log 2 + Real.log (5 / 2) := by
      rw [hx]
      field_simp [h_log2_pos.ne'] <;> ring
  have hL_eq1 : y < 0 → L = 1 := by
    intro hy_neg
    have h_max : max 0 L_raw = 0 := by
      rw [max_eq_left]
      · exact h_y_eq_Lraw ▸ le_of_lt hy_neg
    have h : L = max 0 L_raw + 1 := by
      simp [L] <;> rfl
    rw [h, h_max] <;> norm_num
  have hL_eq2 : 0 ≤ y → L = y + 1 := by
    intro hy_nonneg
    have h_max : max 0 L_raw = L_raw := by
      rw [max_eq_right]
      · exact h_y_eq_Lraw ▸ hy_nonneg
    have h : L = max 0 L_raw + 1 := by
      simp [L] <;> rfl
    rw [h, h_max]
    <;> linarith [h_y_eq_Lraw]
  have h_x_neg_from_y_neg : y < 0 → x < 0 := by
    intro hy_neg
    have h1 : Real.log (800 * C / (m * δ)) < y := h_log800_lt_log2000
    have h2 : Real.log (800 * C / (m * δ)) < 0 := by linarith
    exact div_neg_of_neg_of_pos h2 h_log2_pos
  have h24K_le_100L : 24 * (K : ℝ) ≤ 100 * L := by
    by_cases h_y_neg : y < 0
    · have hL : L = 1 := hL_eq1 h_y_neg
      have hx_neg : x < 0 := h_x_neg_from_y_neg h_y_neg
      have hK : (K : ℝ) ≤ 2 := hK_le_2 hx_neg
      rw [hL]
      <;> linarith
    · have h_y_nonneg : 0 ≤ y := by linarith
      have hL : L = y + 1 := hL_eq2 h_y_nonneg
      by_cases h_x_neg : x < 0
      · have hK : (K : ℝ) ≤ 2 := hK_le_2 h_x_neg
        rw [hL]
        <;> linarith [h_y_nonneg]
      · have h_x_nonneg : 0 ≤ x := by linarith
        have hK : (K : ℝ) ≤ x + 3 := hK_le_x3 h_x_nonneg
        rw [hL, h_y_relation]
        have h7 : 0 ≤ x * (100 * Real.log 2 - 24) := by
          have h8 : 0 < 100 * Real.log 2 - 24 := by linarith [h_log2_gt24]
          exact mul_nonneg h_x_nonneg (by linarith)
        have h9 : 0 ≤ 100 * Real.log (5 / 2) + 28 := by positivity
        nlinarith
  have h4K_le_50L : 4 * (K : ℝ) ≤ 50 * L := by
    by_cases h_y_neg : y < 0
    · have hL : L = 1 := hL_eq1 h_y_neg
      have hx_neg : x < 0 := h_x_neg_from_y_neg h_y_neg
      have hK : (K : ℝ) ≤ 2 := hK_le_2 hx_neg
      rw [hL] <;> linarith
    · have h_y_nonneg : 0 ≤ y := by linarith
      have hL : L = y + 1 := hL_eq2 h_y_nonneg
      by_cases h_x_neg : x < 0
      · have hK : (K : ℝ) ≤ 2 := hK_le_2 h_x_neg
        rw [hL] <;> linarith [h_y_nonneg]
      · have h_x_nonneg : 0 ≤ x := by linarith
        have hK : (K : ℝ) ≤ x + 3 := hK_le_x3 h_x_nonneg
        rw [hL, h_y_relation]
        have h7 : 0 ≤ x * (50 * Real.log 2 - 4) := by
          have h8 : 0 < 50 * Real.log 2 - 4 := by linarith [h_log2_gt24]
          exact mul_nonneg h_x_nonneg (by linarith)
        have h9 : 0 ≤ 50 * Real.log (5 / 2) + 38 := by positivity
        nlinarith

  -- Step 7: Prove IsDeltaSet
  let C' : ℝ := 100 * C * L / m
  have hC'_nonneg : 0 ≤ C' := by positivity

  have h_main_bound : ∀ (x : Point) (r : ℝ), δ ≤ r →
      (P ∩ Metric.ball x r).encard ≤ ENNReal.ofReal (C' * r) * P.encard := by
    intro x r hr
    by_cases h_empty : (P ∩ Metric.ball x r).Nonempty
    · let I_ball : Finset (Fin N) := Pfin.filter (fun i => e i ∈ Metric.ball x r)
      have h_image_ball : Set.image e I_ball = P ∩ Metric.ball x r := by
        ext y; simp only [Set.mem_image, Set.mem_inter_iff, P]
        constructor
        · rintro ⟨i, hi, rfl⟩
          have h_iP := (Finset.mem_filter.mp hi).1
          have h_iball := (Finset.mem_filter.mp hi).2
          exact ⟨Set.mem_image_of_mem e h_iP, h_iball⟩
        · rintro ⟨hy1, hy2⟩
          rcases hy1 with ⟨i, hi, rfl⟩
          exact ⟨i, Finset.mem_filter.mpr ⟨hi, hy2⟩, rfl⟩
      have h_encard_ball : (P ∩ Metric.ball x r).encard = ↑I_ball.card := by
        rw [←h_image_ball]
        have h_eq2 : (Set.image e I_ball) = ↑(I_ball.image e) := by
          ext x; simp [Finset.mem_image]
        rw [h_eq2]
        have h2 : (↑(I_ball.image e) : Set Point).encard = ↑(I_ball.image e).card :=
          encard_coe_eq_coe_finsetCard (Finset.image e I_ball)
        rw [h2]
        have h3 : (I_ball.image e).card = I_ball.card := by
          apply Finset.card_image_of_injOn
          intro i _ j _ h
          exact h_inj (Finset.mem_filter.mp ‹_›).1 (Finset.mem_filter.mp ‹_›).1 h
        rw [h3]

      have h_cells_in_ball : ∀ i ∈ I_ball, EV i ⊆ Metric.closedBall x (r + 2 * δ) := by
        intro i hi
        have h_ei_ball : e i ∈ Metric.ball x r := (Finset.mem_filter.mp hi).2
        have h_dist : dist (e i) x < r := by simpa [Metric.mem_ball] using h_ei_ball
        intro y hy
        have h2 : y ∈ Metric.closedBall (e i) (2 * δ) := hEV_sub_ball i hy
        have h3 : dist y (e i) ≤ 2 * δ := by simpa [Metric.mem_closedBall] using h2
        have h4 : dist y x ≤ r + 2 * δ := by
          calc dist y x ≤ dist y (e i) + dist (e i) x := dist_triangle _ _ _
            _ ≤ 2 * δ + r := by linarith
            _ = r + 2 * δ := by ring
        simpa [Metric.mem_closedBall] using h4

      have h_disj_ball : ∀ i ∈ I_ball, ∀ j ∈ I_ball, i ≠ j → Disjoint (V i) (V j) := by
        intro i _ j _ hne; exact hV_disj i j hne

      have h_sum_le : ∑ i ∈ I_ball, ν (EV i) ≤ ν (Metric.closedBall x (r + 2 * δ)) := by
        have h_union_sub : (⋃ i ∈ I_ball, EV i) ⊆ Metric.closedBall x (r + 2 * δ) := by
          intro y hy
          have h_exists : ∃ (i : Fin N), i ∈ I_ball ∧ y ∈ EV i := by
            simpa [Finset.mem_biUnion] using hy
          rcases h_exists with ⟨i, hi, hyi⟩
          exact h_cells_in_ball i hi hyi
        have h_main2 : ∀ (s : Finset (Fin N)), ν (E ∩ ⋃ i ∈ s, V i) = ∑ i ∈ s, ν (EV i) :=
          measure_inter_finset_union_helper V hV_meas hV_disj
        have h_eq : (⋃ i ∈ I_ball, EV i) = E ∩ ⋃ i ∈ I_ball, V i := by
          ext z; simp [EV, Finset.mem_biUnion] <;> tauto
        have h_add : ν (⋃ i ∈ I_ball, EV i) = ∑ i ∈ I_ball, ν (EV i) := by
          rw [h_eq]
          exact h_main2 I_ball
        rw [←h_add]; exact measure_mono h_union_sub

      have h_real_sum : ∑ i ∈ I_ball, w i = (∑ i ∈ I_ball, ν (EV i)).toReal := by
        have h2 : ∑ i ∈ I_ball, w i = ∑ i ∈ I_ball, (ν (EV i)).toReal := by rfl
        rw [h2, ENNReal.toReal_sum (hf := fun i _ => h_all_finite i)] <;> simp [w]

      have h_frostman : ν (Metric.closedBall x (r + 2 * δ)) ≤ ENNReal.ofReal (C * (r + 2 * δ)) :=
        hν_frostman x (r + 2 * δ) (by linarith)

      have h_ball_ne_top : ν (Metric.closedBall x (r + 2 * δ)) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_frostman
      have h_sum_ne_top : (∑ i ∈ I_ball, ν (EV i)) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h_sum_le.trans h_frostman)

      have h6 : (∑ i ∈ I_ball, ν (EV i)).toReal ≤ C * (r + 2 * δ) := by
        have h7 : (∑ i ∈ I_ball, ν (EV i)).toReal ≤ (ν (Metric.closedBall x (r + 2 * δ))).toReal :=
          (ENNReal.toReal_le_toReal h_sum_ne_top h_ball_ne_top).mpr h_sum_le
        have h8 : (ν (Metric.closedBall x (r + 2 * δ))).toReal ≤ C * (r + 2 * δ) := by
          have h9 : (ν (Metric.closedBall x (r + 2 * δ))).toReal ≤
              (ENNReal.ofReal (C * (r + 2 * δ))).toReal :=
            (ENNReal.toReal_le_toReal h_ball_ne_top ENNReal.ofReal_ne_top).mpr h_frostman
          have h10 : (ENNReal.ofReal (C * (r + 2 * δ))).toReal = C * (r + 2 * δ) := by
            have h11 : 0 ≤ C * (r + 2 * δ) := by
              have h12 : 0 ≤ r + 2 * δ := by linarith [hr, hδ]
              exact mul_nonneg (by linarith [hC_pos]) h12
            rw [ENNReal.toReal_ofReal h11]
          rw [h10] at h9; exact h9
        exact h7.trans h8

      have h_wmin_ball : ∀ i ∈ I_ball, τ * (2 : ℝ)^kstar ≤ w i := by
        intro i hi
        have h_iPfin : i ∈ Pfin := (Finset.mem_filter.mp hi).1
        exact h_wmin i h_iPfin

      have h7 : (I_ball.card : ℝ) * (τ * (2 : ℝ)^kstar) ≤ ∑ i ∈ I_ball, w i := by
        have h8 : ∀ i ∈ I_ball, τ * (2 : ℝ)^kstar ≤ w i := h_wmin_ball
        calc (I_ball.card : ℝ) * (τ * (2 : ℝ)^kstar)
          = ∑ i ∈ I_ball, (τ * (2 : ℝ)^kstar) := by simp [Finset.sum_const] <;> ring
        _ ≤ ∑ i ∈ I_ball, w i := Finset.sum_le_sum h8

      have hrpos : 0 < r := by linarith
      have h9 : C * (r + 2 * δ) ≤ 3 * C * r := by
        have h10 : r + 2 * δ ≤ 3 * r := by linarith
        have h11 : 0 ≤ C := by linarith [hC_pos]
        have h12 : C * (r + 2 * δ) ≤ C * (3 * r) := mul_le_mul_of_nonneg_left h10 h11
        have h13 : C * (3 * r) = 3 * C * r := by ring
        rw [h13] at h12
        exact h12

      have h11 : (I_ball.card : ℝ) ≤ C' * r * (Pfin.card : ℝ) := by
        dsimp only [C']
        set a : ℝ := τ * (2 : ℝ)^kstar with ha_def
        have ha_pos : 0 < a := by
          have h1 : 0 < τ := hτ_pos
          have h2 : 0 < (2 : ℝ)^kstar := by positivity
          exact mul_pos h1 h2
        have h12 : (I_ball.card : ℝ) * a ≤ C * (r + 2 * δ) := by
          rw [h_real_sum] at h7; linarith [h6, h9]
        have h15 : a * (Pfin.card : ℝ) ≥ m / (8 * (K : ℝ)) := h_key2
        have hP_card_pos : 0 < (Pfin.card : ℝ) := by
          have h : 0 < Pfin.card := Finset.card_pos.mpr hPfin_nonempty
          exact_mod_cast h
        have hK_pos' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
        have hL_nonneg : 0 ≤ L := by linarith [hL_pos]
        exact card_bound_core (I_ball.card : ℝ) (Pfin.card : ℝ) a C r δ m (K : ℝ) L
          ha_pos hC_pos hδ hr hm_pos hK_pos' hP_card_pos hL_nonneg h12 h15 h24K_le_100L

      rw [h_encard_ball, hP_card]
      have h_C_nonneg : 0 ≤ C' := hC'_nonneg
      have h25 : 0 ≤ C' * r := mul_nonneg h_C_nonneg (by linarith)
      have h26 : (I_ball.card : ℝ) ≤ C' * r * (Pfin.card : ℝ) := h11
      have h27 : ENNReal.ofReal (I_ball.card : ℝ) ≤ ENNReal.ofReal (C' * r * (Pfin.card : ℝ)) :=
        ENNReal.ofReal_le_ofReal h26
      have h28 : ENNReal.ofReal (C' * r * (Pfin.card : ℝ)) =
          ENNReal.ofReal (C' * r) * ENNReal.ofReal ((Pfin.card : ℝ)) := by
        rw [ENNReal.ofReal_mul h25]
      have h29 : ENNReal.ofReal ((Pfin.card : ℝ)) = (Pfin.card : ENNReal) := by simp
      rw [h28, h29] at h27
      simpa using h27
    · have h_empty' : P ∩ Metric.ball x r = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using h_empty
      rw [h_empty'] <;> simp

  -- Convert to externalCoveringNumber
  have h_ecard_P : (Metric.externalCoveringNumber δn P : ENNReal) = P.encard := by
    exact_mod_cast externalCoveringNumber_eq_encard_of_separated hP_finite hδn_pos hP_sep

  have h_ecard_ball : ∀ (x : Point) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δn (P ∩ Metric.ball x r) : ENNReal) =
        (P ∩ Metric.ball x r).encard := by
    intro x r hr
    let Q := P ∩ Metric.ball x r
    have hQ_sub : Q ⊆ P := by simp [Q]
    have hQ_finite : Q.Finite := hP_finite.subset hQ_sub
    have hQ_sep : Metric.IsSeparated εn Q := hP_sep.mono hQ_sub
    exact_mod_cast externalCoveringNumber_eq_encard_of_separated hQ_finite hδn_pos hQ_sep

  have h_isDelta : IsDeltaSet δ 1 C' hδ (by norm_num) hC'_nonneg P := by
    intro x r hr
    rw [h_ecard_ball x r hr, h_ecard_P]
    have h_rpow : Real.rpow r 1 = r := by
      have hr_pos : 0 ≤ r := by linarith [hδ]
      exact Real.rpow_one r
    have h_goal : ENNReal.ofReal (C' * Real.rpow r 1) = ENNReal.ofReal (C' * r) := by
      rw [h_rpow]
    rw [h_goal]
    exact h_main_bound x r hr

  -- Step 8: Mass bound
  have h_mass_bound1 : ∑ i ∈ S_heavy, w i ≤ 2 * τ * ∑ k ∈ Finset.range K, score k := by
    have h1 : ∀ k ∈ Finset.range K, ∑ i ∈ R k, w i ≤ 2 * τ * score k := by
      intro k _
      have h2 : ∀ i ∈ R k, w i < τ * (2 : ℝ)^(k+1) := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2.2
      have h3 : ∑ i ∈ R k, w i ≤ ∑ i ∈ R k, (τ * (2 : ℝ)^(k+1)) :=
        Finset.sum_le_sum (fun i hi => (h2 i hi).le)
      calc ∑ i ∈ R k, w i
        ≤ ∑ i ∈ R k, (τ * (2 : ℝ)^(k+1)) := h3
        _ = (n k : ℝ) * (τ * (2 : ℝ)^(k+1)) := by simp [n, Finset.sum_const] <;> ring
        _ = 2 * τ * score k := by simp [score] <;> ring
    have h4 : ∑ k ∈ Finset.range K, ∑ i ∈ R k, w i = ∑ i ∈ S_heavy, w i := by
      have h_disj' : ∀ k l, k ≠ l → Disjoint (R k) (R l) := by
        intro k l hne
        rw [Finset.disjoint_left]
        intro i hik hil
        have h1 : range_k k i := (Finset.mem_filter.mp hik).2
        have h2 : range_k l i := (Finset.mem_filter.mp hil).2
        exact hne (h_disj i (Finset.mem_filter.mp hik).1 k l h1 h2)
      have h_union : (⋃ k ∈ Finset.range K, (R k : Set (Fin N))) = (S_heavy : Set (Fin N)) := by
        ext i
        simp only [Set.mem_iUnion₂, Finset.mem_coe, Finset.mem_range]
        constructor
        · rintro ⟨k, _, hki⟩; exact (Finset.mem_filter.mp hki).1
        · intro hi
          rcases h_cover i hi with ⟨k, hkK, hk_range⟩
          exact ⟨k, hkK, Finset.mem_filter.mpr ⟨hi, hk_range⟩⟩
      have h_disj'' : (Finset.range K : Set ℕ).PairwiseDisjoint R := by
        intro k _ l _ hne; exact h_disj' k l hne
      have h_biUnion : (Finset.range K).biUnion R = S_heavy := by
        have h1 : (↑((Finset.range K).biUnion R) : Set (Fin N)) =
            ⋃ k ∈ Finset.range K, ↑(R k) := by
          rw [Finset.coe_biUnion] <;> simp
        have h2 : (↑((Finset.range K).biUnion R) : Set (Fin N)) = (S_heavy : Set (Fin N)) := by
          rw [h1, h_union]
        exact_mod_cast h2
      rw [←Finset.sum_biUnion h_disj'', h_biUnion]
    have h5 : ∑ k ∈ Finset.range K, ∑ i ∈ R k, w i ≤ ∑ k ∈ Finset.range K, (2 * τ * score k) :=
      Finset.sum_le_sum h1
    rw [h4] at h5
    have h6 : ∑ k ∈ Finset.range K, (2 * τ * score k) = 2 * τ * ∑ k ∈ Finset.range K, score k := by
      rw [Finset.mul_sum]
    rw [h6] at h5; exact h5

  have h_mass_bound2 : ∑ i ∈ S_heavy, w i ≤ 4 * (K : ℝ) * C * δ * (Pfin.card : ℝ) := by
    have h1 : ∑ k ∈ Finset.range K, score k ≤ (K : ℝ) * score kstar := by
      calc ∑ k ∈ Finset.range K, score k
        ≤ ∑ k ∈ Finset.range K, score kstar := Finset.sum_le_sum hscore_max
        _ = (K : ℝ) * score kstar := by simp [Finset.sum_const] <;> ring
    have h3 : score kstar = (Pfin.card : ℝ) * (2 : ℝ)^kstar := by
      simp [score, n, Pfin] <;> ring
    have h4 : τ * (2 : ℝ)^kstar ≤ 2 * C * δ := by
      have h5 : ∀ i ∈ Pfin, w i ≤ 2 * C * δ := fun i _ => h_w_max_le i
      rcases hPfin_nonempty with ⟨i, hi⟩
      have h6 : τ * (2 : ℝ)^kstar ≤ w i := h_wmin i hi
      have h7 : w i ≤ 2 * C * δ := h5 i hi
      linarith
    have h2τ_nonneg : 0 ≤ 2 * τ := by linarith [hτ_pos]
    have h_step1 : 2 * τ * ∑ k ∈ Finset.range K, score k ≤ 2 * τ * ((K : ℝ) * score kstar) :=
      mul_le_mul_of_nonneg_left h1 h2τ_nonneg
    have h_step2 : 2 * τ * ((K : ℝ) * score kstar) = 2 * (K : ℝ) * (τ * (2 : ℝ)^kstar) * (Pfin.card : ℝ) := by
      rw [h3] <;> ring
    have h_step3 : 2 * (K : ℝ) * (τ * (2 : ℝ)^kstar) * (Pfin.card : ℝ) ≤
        2 * (K : ℝ) * (2 * C * δ) * (Pfin.card : ℝ) := by
      have hK_nonneg : 0 ≤ (K : ℝ) := by exact_mod_cast (Nat.zero_le K)
      have hP_nonneg : 0 ≤ (Pfin.card : ℝ) := by exact_mod_cast (Nat.zero_le Pfin.card)
      have h2K_nonneg : 0 ≤ 2 * (K : ℝ) := by linarith
      have h4' : τ * (2 : ℝ)^kstar ≤ 2 * C * δ := h4
      have h5 : 2 * (K : ℝ) * (τ * (2 : ℝ)^kstar) ≤ 2 * (K : ℝ) * (2 * C * δ) :=
        mul_le_mul_of_nonneg_left h4' h2K_nonneg
      exact mul_le_mul_of_nonneg_right h5 hP_nonneg
    have h_step4 : 2 * (K : ℝ) * (2 * C * δ) * (Pfin.card : ℝ) =
        4 * (K : ℝ) * C * δ * (Pfin.card : ℝ) := by ring
    calc ∑ i ∈ S_heavy, w i
      ≤ 2 * τ * ∑ k ∈ Finset.range K, score k := h_mass_bound1
      _ ≤ 2 * τ * ((K : ℝ) * score kstar) := h_step1
      _ = 2 * (K : ℝ) * (τ * (2 : ℝ)^kstar) * (Pfin.card : ℝ) := h_step2
      _ ≤ 2 * (K : ℝ) * (2 * C * δ) * (Pfin.card : ℝ) := h_step3
      _ = 4 * (K : ℝ) * C * δ * (Pfin.card : ℝ) := h_step4

  have h_total_mass : mE ≤ ∑ i ∈ S_heavy, w i + m / 4 := by
    have h1 : ∑ i : Fin N, w i = ∑ i ∈ S_heavy, w i + ∑ i ∈ Finset.univ \ S_heavy, w i := by
      have h_disj : Disjoint S_heavy (Finset.univ \ S_heavy) := Finset.disjoint_sdiff
      rw [←Finset.sum_union h_disj]
      have h2 : S_heavy ∪ (Finset.univ \ S_heavy) = Finset.univ := by simp
      rw [h2]
    rw [h1] at h_sum_w'
    linarith [h_light_mass]

  have hP_ncard : (P.ncard : ℝ) = (Pfin.card : ℝ) := by
    have h1 : P.ncard = Pfin.card := by
      have h2 : P = Set.image e Pfin := by rfl
      rw [h2]
      rw [Set.ncard_image_of_injOn h_inj]
      <;> simp
    exact_mod_cast h1

  have hνE_le : ν E ≤ ENNReal.ofReal (C * δ * 50 * L * (P.ncard : ℝ)) + ENNReal.ofReal m / 2 := by
    have h1 : mE ≤ 4 * (K : ℝ) * C * δ * (Pfin.card : ℝ) + m / 4 := by
      linarith [h_total_mass, h_mass_bound2]
    have h2 : 4 * (K : ℝ) * C * δ * (Pfin.card : ℝ) + m / 4 ≤
        C * δ * 50 * L * (P.ncard : ℝ) + m / 2 := by
      rw [hP_ncard]
      have hP_nonneg : 0 ≤ (Pfin.card : ℝ) := by exact_mod_cast (Nat.zero_le Pfin.card)
      exact mass_bound_final (K : ℝ) L C δ m (Pfin.card : ℝ) hC_pos hδ hm_pos hP_nonneg h4K_le_50L
    have h5 : mE ≤ C * δ * 50 * L * (P.ncard : ℝ) + m / 2 := by linarith [h1, h2]
    have h6 : ν E = ENNReal.ofReal mE := by
      have h7 : ENNReal.ofReal (ν E).toReal = ν E := ENNReal.ofReal_toReal hνE_ne_top
      have h9 : (ν E).toReal = mE := by rfl
      have h10 : ENNReal.ofReal mE = ν E := by
        rw [←h9]
        exact h7
      exact h10.symm
    rw [h6]
    have h7 : 0 ≤ C * δ * 50 * L * (P.ncard : ℝ) := by positivity
    have h8 : 0 ≤ m / 2 := by linarith
    have h_div : ENNReal.ofReal (m / 2) = ENNReal.ofReal m / 2 := by
      have h9 : 0 ≤ m := by linarith [hm_pos]
      have h10 : ENNReal.ofReal (m / 2) = ENNReal.ofReal m * ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [←ENNReal.ofReal_mul h9] <;> ring_nf
      rw [h10]
      have h11 : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
        simp
      rw [h11]
      <;> simp [div_eq_mul_inv]
      <;> ring
    have h9 : ENNReal.ofReal (C * δ * 50 * L * (P.ncard : ℝ) + m / 2) ≤
        ENNReal.ofReal (C * δ * 50 * L * (P.ncard : ℝ)) + ENNReal.ofReal m / 2 := by
      have h10 : ENNReal.ofReal (C * δ * 50 * L * (P.ncard : ℝ) + m / 2) ≤
          ENNReal.ofReal (C * δ * 50 * L * (P.ncard : ℝ)) + ENNReal.ofReal (m / 2) :=
        ENNReal.ofReal_add_le
      rw [h_div] at h10
      exact h10
    have h10 : ENNReal.ofReal mE ≤ ENNReal.ofReal (C * δ * 50 * L * (P.ncard : ℝ) + m / 2) :=
      ENNReal.ofReal_le_ofReal h5
    exact le_trans h10 h9

  exact ⟨P, hP_sub_E, hP_nonempty, hP_finite, h_isDelta, hνE_le⟩
