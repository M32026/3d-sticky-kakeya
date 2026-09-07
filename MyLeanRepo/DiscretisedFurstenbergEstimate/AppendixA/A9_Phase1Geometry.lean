module

/-
  A9 Phase 1: Geometric data extraction.

  Extracts the geometric core of A9_buildSquareData into a separate lemma
  to reduce elaborator burden. Produces point sets, tube cells, projection
  bounds, witness, and residual incidence data.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Helpers
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate

open LemmaE
open DiscretisedFurstenbergEstimate.CoveringUtils
open TubesAndSlopes

namespace AppendixA

/-- Intermediate geometric data from A9 phase 1 construction. -/
structure A9_Phase1Data (Δ δ s t ε : ℝ) (Q : CoarseSquare Δ) where
  hδ_pos : 0 < δ
  T0 : CoarseTube
  sq : A8_SquareData Δ δ s t ε T0 Q
  z_Q : Plane
  P_orig_Q : Finset Plane
  hP_orig_Q_eq : P_orig_Q = sq.P'_Q.image sq.originalOfNorm
  F : Plane → Plane
  hF_def : F = AffineNormalization.normalizeMap (tubeSlope T0) (tubeIntercept T0)
  P_norm_Q : Finset Plane
  hP_norm_Q_eq : P_norm_Q = P_orig_Q.image F
  normOfSheared : Plane → Plane
  h_norm_mem : ∀ p ∈ P_norm_Q, normOfSheared p ∈ sq.P'_Q
  hP_phys_sub : (P_orig_Q : Set Plane) ⊆ squareSet Δ Q
  hP_phys_card : Real.rpow Δ (-t + 44 * ε) ≤ (P_orig_Q.card : ℝ)
  hP_norm_Q_card : (P_norm_Q.card : ℝ) = (P_orig_Q.card : ℝ)
  hP_orig_Q_card : (P_orig_Q.card : ℝ) = (sq.P'_Q.card : ℝ)
  hy_Q_bounds : (squareY Δ Q) ∈ Set.Icc (-2 : ℝ) 2
  squareIndex : CoarseSquare Δ
  hP_in_square : (P_norm_Q : Set Plane) ⊆ Metric.cthickening (2 * Δ) (squareSet Δ squareIndex)
  c_Q : ℝ
  h_c_Q_def : c_Q = z_Q 0 - tubeSlope T0 * z_Q 1 - tubeIntercept T0
  Pi_Q : Set ℝ
  h_Pi_Q_def : Pi_Q = (fun x : ℝ => Δ * x + c_Q) '' sq.proj.Pi
  hPi_Q_bounds : ∀ x ∈ Pi_Q, x ∈ Set.Icc (-6 : ℝ) 6
  hPi_Q_sset : IsDeltaSSet Δ s (Real.rpow Δ (-s - 49 * ε)) Pi_Q
  f_cell : FineTube → DyadicTubeCell δ
  h_f_cell_def : ∀ (T : FineTube), f_cell T =
    dyadicCellOfParams δ hδ_pos (tubeSlope T - tubeSlope T0, tubeIntercept T - tubeIntercept T0)
  fineTubes_norm : Plane → Finset (DyadicTubeCell δ)
  fineTubeOfCell : Plane → DyadicTubeCell δ → FineTube
  h_fineTubeOfCell_def : ∀ (p : Plane) (cell : DyadicTubeCell δ),
    fineTubeOfCell p cell = TubesAndSlopes.makeAffineLine
      (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2
  hfine_card_lower : ∀ p ∈ P_norm_Q, Real.rpow Δ (-s + 50 * ε) ≤ (fineTubes_norm p).card
  hfine_card_upper : ∀ p ∈ P_norm_Q, (fineTubes_norm p).card ≤ Real.rpow Δ (-s - 7 * ε)
  h_fine_def : ∀ p ∈ P_norm_Q,
    fineTubes_norm p = (sq.fineTubes (normOfSheared p)).image f_cell
  hfine_cell_bounds : ∀ p ∈ P_norm_Q, ∀ cell ∈ fineTubes_norm p,
    |(paramsOfDyadicCell δ cell).1| ≤ 7 * Δ ∧ |(paramsOfDyadicCell δ cell).2| ≤ 7 * Δ
  witness : ℝ → Plane
  h_witness : ∀ x ∈ Pi_Q, witness x ∈ P_norm_Q ∧ (witness x) 0 = x
  h_witness_y_close : ∀ x ∈ Pi_Q, |(witness x) 1 - squareY Δ Q| ≤ 3 * Δ
  h_residual : ∀ x ∈ Pi_Q, ∀ cell ∈ fineTubes_norm (witness x),
    let T := fineTubeOfCell (witness x) cell
    |x - tubeSlope T * (witness x) 1 - tubeIntercept T| ≤ 6 * δ
  h_orig_inj : Set.InjOn sq.originalOfNorm (sq.P'_Q : Set Plane)

/-- Phase 1 of A9 per-square construction: produces all geometric data. -/
def A9_phase1_geometry
    (Δ δ s t ε : ℝ)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_eq : δ = Δ ^ 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (hε_pos : 0 < ε)
    (hΔ_cover : (10000 : ℝ) ≤ Real.rpow Δ (-2 * s - ε))
    (hΔ_packing : Δ ^ (10 * ε) ≤ 1 / 144)
    (hΔ_small : 7 * Δ ≤ 1)
    (a8 : A8_Output Δ δ s t ε)
    (Q : CoarseSquare Δ) (hQ : Q ∈ a8.Q0) :
    A9_Phase1Data Δ δ s t ε Q := by
  let T0 := a8.T0_norm
  let σ₀ := tubeSlope T0
  let h₀ := tubeIntercept T0
  let F : Plane → Plane := AffineNormalization.normalizeMap σ₀ h₀
  let Finv : Plane → Plane := AffineNormalization.denormalizeMap σ₀ h₀
  have hF_inj : Function.Injective F :=
    AffineNormalization.normalizeMap_injective σ₀ h₀
  have hFinv_F : ∀ p, Finv (F p) = p :=
    AffineNormalization.normalizeMap_left_inverse σ₀ h₀
  have hFinv_inj : Function.Injective Finv :=
    (AffineNormalization.normalizeMap_right_inverse σ₀ h₀).injective
  have hδ_pos : 0 < δ := by rw [hδ_eq] <;> positivity
  let τ : ℝ := min (t - s) 1
  have hτ_pos : 0 < τ := by
    have h1 : 0 < t - s := by linarith
    exact lt_min h1 (by norm_num)
  have hτ_le_one : τ ≤ 1 := min_le_right _ _
  have hτ_le_t_sub_s : τ ≤ t - s := min_le_left _ _
  let Q0 := a8.Q0

  have h_coord_abs_le_norm : ∀ (p : Plane) (i : Fin 2), |p i| ≤ ‖p‖ := by
    intro p i
    have h_norm_sq : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
      have h : ‖p‖ = Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2) := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> simp
      rw [h]
      rw [Real.sq_sqrt (by positivity)] <;> ring
    have h2 : (p i) ^ 2 ≤ ‖p‖ ^ 2 := by
      rw [h_norm_sq]
      fin_cases i <;> simp [Fin.sum_univ_two] <;> positivity
    have h3 : (|p i|) ^ 2 ≤ (‖p‖) ^ 2 := by
      have h4 : (|p i|) ^ 2 = (p i) ^ 2 := by simp [sq_abs]
      rw [h4] <;> exact h2
    nlinarith [sq_abs (p i), norm_nonneg p]

  let sq := a8.perSquare Q hQ
  let z_Q := sq.a4.z_Q

  -- Step 1: Unnormalize to physical coordinates
  let P_orig_Q : Finset Plane := sq.P'_Q.image sq.originalOfNorm
  have h_orig_inj : Set.InjOn sq.originalOfNorm (sq.P'_Q : Set Plane) := by
    intro p _ q _ h
    have h1 : sq.originalOfNorm p = sq.originalOfNorm q := h
    have h2 : (1 / Δ : ℝ) • (sq.originalOfNorm p - z_Q) =
               (1 / Δ : ℝ) • (sq.originalOfNorm q - z_Q) := by rw [h1]
    have h3 : ∀ x ∈ sq.P'_Q, (1 / Δ : ℝ) • (sq.originalOfNorm x - z_Q) = x := by
      intro x hx
      have h4 : sq.originalOfNorm x = Δ • x + z_Q := sq.h_norm_formula x hx
      rw [h4]
      have h5 : (1 / Δ : ℝ) • ((Δ • x + z_Q) - z_Q) = (1 / Δ : ℝ) • (Δ • x) := by
        congr 1 <;> abel
      rw [h5]
      have h6 : (1 / Δ : ℝ) • (Δ • x) = x := by
        simpa [smul_smul, hΔ_pos.ne'] using rfl
      exact h6
    rw [h3 p ‹_›, h3 q ‹_›] at h2
    exact h2

  -- Step 2: Shear physical points
  let P_norm_Q : Finset Plane := P_orig_Q.image F

  -- Map sheared physical point back to normalized point
  let normOfSheared (p : Plane) : Plane := (1 / Δ : ℝ) • (Finv p - z_Q)

  -- Physical square coordinates
  let x_Q : ℝ := squareX Δ Q
  let y_Q : ℝ := squareY Δ Q
  have hx_Q_eq : x_Q = squareX Δ Q := by rfl
  have hy_Q_eq : y_Q = squareY Δ Q := by rfl
  -- Pre-shear physical points
  have hP_phys_sub : (P_orig_Q : Set Plane) ⊆ squareSet Δ Q := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have h1 : q ∈ sq.a4.P_norm := sq.hP'_Q_sub hq
    have h2 : Δ • q + z_Q ∈ sq.a4.base.P_Q := sq.a4.hP_norm_unnormalize q h1
    have h3 : sq.originalOfNorm q = Δ • q + z_Q := sq.h_norm_formula q hq
    rw [h3]
    exact sq.a4.base.hP_Q_in_square h2
  have hP_phys_card : Real.rpow Δ (-t + 44 * ε) ≤ (P_orig_Q.card : ℝ) := by
    have h1 : (P_orig_Q.card : ℝ) = (sq.P'_Q.card : ℝ) := by
      rw [Finset.card_image_of_injOn h_orig_inj]
    rw [h1]
    exact sq.hP'_Q_card_lower

  have hy_Q_bounds : y_Q ∈ Set.Icc (-2 : ℝ) 2 := by
    have h_nonempty : (P_orig_Q : Set Plane).Nonempty := by
      have h1 : 0 < (P_orig_Q.card : ℝ) := by
        have h2 : 0 < Real.rpow Δ (-t + 44 * ε) := Real.rpow_pos_of_pos hΔ_pos _
        exact lt_of_lt_of_le h2 hP_phys_card
      exact Finset.card_pos.mp (by exact_mod_cast h1)
    rcases h_nonempty with ⟨p_orig, hp_orig⟩
    have h_in_sq : p_orig ∈ squareSet Δ Q := hP_phys_sub hp_orig
    have hpy1 : p_orig 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := h_in_sq.2
    have h_in_PQ : p_orig ∈ sq.a4.base.P_Q := by
      rcases Finset.mem_image.mp hp_orig with ⟨q, hq, rfl⟩
      have h1 : q ∈ sq.a4.P_norm := sq.hP'_Q_sub hq
      have h2 : Δ • q + sq.a4.z_Q ∈ sq.a4.base.P_Q := sq.a4.hP_norm_unnormalize q h1
      have h3 : sq.originalOfNorm q = Δ • q + sq.a4.z_Q := sq.h_norm_formula q hq
      rw [h3]
      exact h2
    have h_in_ball : p_orig ∈ Metric.closedBall 0 (Real.sqrt 2) := sq.a4.base.hP_Q_in_ball h_in_PQ
    have hnorm : ‖p_orig‖ ≤ Real.sqrt 2 := by simpa [Metric.mem_closedBall] using h_in_ball
    have hpy_abs : |p_orig 1| ≤ Real.sqrt 2 := by
      have h : |p_orig 1| ≤ ‖p_orig‖ := h_coord_abs_le_norm p_orig 1
      linarith
    rcases hpy1 with ⟨hlo, hhi⟩
    have h_upper : Δ * (Q.2 : ℝ) ≤ 2 := by
      have h : Δ * (Q.2 : ℝ) ≤ p_orig 1 := hlo
      have h2 : p_orig 1 ≤ Real.sqrt 2 := (abs_le.mp hpy_abs).2
      have h_sqrt2_lt_2 : Real.sqrt 2 < (2 : ℝ) := by
        have h : Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have h4 : Real.sqrt 4 = 2 := by norm_num
        rw [h4] at h
        exact h
      linarith [h_sqrt2_lt_2]
    have h_lower : -2 ≤ Δ * (Q.2 : ℝ) := by
      have h3 : p_orig 1 < Δ * ((Q.2 : ℝ) + 1) := hhi
      have h4 : -Real.sqrt 2 ≤ p_orig 1 := (abs_le.mp hpy_abs).1
      have h5 : Δ * (Q.2 : ℝ) > -Real.sqrt 2 - Δ := by linarith
      have h6 : -Real.sqrt 2 - Δ ≥ -2 := by
        have h_sqrt2_le : Real.sqrt 2 ≤ 3 / 2 := by
          rw [Real.sqrt_le_iff] <;> norm_num
        linarith [hΔ_small]
      linarith
    simpa [y_Q, squareY] using ⟨h_lower, h_upper⟩

  -- Dyadic square containment: sheared x-coordinates have spread < 2Δ,
  -- so choose squareIndex dynamically to contain them within cthickening(2Δ)
  have hP_norm_Q_nonempty : P_norm_Q.Nonempty := by
    have h1 : 0 < (P_orig_Q.card : ℝ) := by
      have h2 : 0 < Real.rpow Δ (-t + 44 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact lt_of_lt_of_le h2 hP_phys_card
    have h3 : P_orig_Q.Nonempty := Finset.card_pos.mp (by exact_mod_cast h1)
    exact Finset.Nonempty.image h3 F

  let x_coords : Finset ℝ := P_norm_Q.image (fun p => p 0)
  have hx_coords_nonempty : x_coords.Nonempty :=
    Finset.Nonempty.image hP_norm_Q_nonempty _
  let x_min : ℝ := Finset.min' x_coords hx_coords_nonempty
  let k : ℤ := ⌊x_min / Δ⌋
  let squareIndex : CoarseSquare Δ := (k, Q.2)

  have hx_min_mem : x_min ∈ x_coords := Finset.min'_mem x_coords hx_coords_nonempty
  have hx_min_le : ∀ p ∈ P_norm_Q, x_min ≤ p 0 := by
    intro p hp
    have h1 : p 0 ∈ x_coords := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    exact Finset.min'_le x_coords (p 0) h1

  have hσ_bound : |σ₀| ≤ 1 := by
    have h4 : |tubeSlope a8.a7.T0| ≤ 1 := a8.a7.hT0_slope_bound
    have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
    have h5 : σ₀ = tubeSlope a8.a7.T0 := by
      exact congr_arg tubeSlope hT0_eq
    rw [h5]; exact h4

  have h_spread : ∀ (p1 : Plane), p1 ∈ P_norm_Q → ∀ (p2 : Plane), p2 ∈ P_norm_Q →
      |p1 0 - p2 0| < 2 * Δ := by
    intro p1 hp1 p2 hp2
    rcases Finset.mem_image.mp hp1 with ⟨p_orig1, h_orig1, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨p_orig2, h_orig2, rfl⟩
    have h1 : p_orig1 ∈ squareSet Δ Q := hP_phys_sub h_orig1
    have h2 : p_orig2 ∈ squareSet Δ Q := hP_phys_sub h_orig2
    have hdx : |p_orig1 0 - p_orig2 0| < Δ := by
      rcases h1 with ⟨⟨h1lo, h1hi⟩, _⟩
      rcases h2 with ⟨⟨h2lo, h2hi⟩, _⟩
      exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    have hdy : |p_orig1 1 - p_orig2 1| < Δ := by
      rcases h1 with ⟨_, ⟨h1lo, h1hi⟩⟩
      rcases h2 with ⟨_, ⟨h2lo, h2hi⟩⟩
      exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    have h_eq : (F p_orig1) 0 - (F p_orig2) 0 =
        (p_orig1 0 - p_orig2 0) - σ₀ * (p_orig1 1 - p_orig2 1) := by
      simp [F, AffineNormalization.normalizeMap] <;> ring
    rw [h_eq]
    set a : ℝ := p_orig1 0 - p_orig2 0 with ha_def
    set b : ℝ := σ₀ * (p_orig1 1 - p_orig2 1) with hb_def
    have h_tri : |a - b| ≤ |a| + |b| := abs_sub a b
    have h_abs_mul : |b| = |σ₀| * |p_orig1 1 - p_orig2 1| := by
      simp [hb_def, abs_mul] <;> ring
    have h_mul_lt : |σ₀| * |p_orig1 1 - p_orig2 1| < Δ := by
      calc |σ₀| * |p_orig1 1 - p_orig2 1|
        ≤ 1 * |p_orig1 1 - p_orig2 1| := by gcongr <;> exact hσ_bound
      _ = |p_orig1 1 - p_orig2 1| := by ring
      _ < Δ := hdy
    calc |a - b| ≤ |a| + |b| := h_tri
      _ = |p_orig1 0 - p_orig2 0| + |σ₀| * |p_orig1 1 - p_orig2 1| := by
        simp [ha_def, h_abs_mul] <;> ring
      _ < Δ + Δ := by linarith [hdx, h_mul_lt]
      _ = 2 * Δ := by ring

  have h_upper_bound : ∀ p ∈ P_norm_Q, p 0 < x_min + 2 * Δ := by
    intro p hp
    have h_exists : ∃ (p_min : Plane), p_min ∈ P_norm_Q ∧ p_min 0 = x_min := by
      rcases Finset.mem_image.mp hx_min_mem with ⟨p_min, hp_min, hpm⟩
      exact ⟨p_min, hp_min, hpm⟩
    rcases h_exists with ⟨p_min, hp_min, hpm⟩
    have h1 : |p 0 - p_min 0| < 2 * Δ := h_spread p hp p_min hp_min
    have h2 : x_min ≤ p 0 := hx_min_le p hp
    have h3 : p 0 - x_min ≥ 0 := by linarith
    have h4 : |p 0 - x_min| = p 0 - x_min := by
      rw [abs_of_nonneg h3]
    rw [hpm] at h1
    rw [h4] at h1
    linarith

  have h_floor1 : Δ * (k : ℝ) ≤ x_min := by
    have h4 : (k : ℝ) ≤ x_min / Δ := Int.floor_le (x_min / Δ)
    have h5 : Δ * (k : ℝ) ≤ Δ * (x_min / Δ) := by gcongr
    have h6 : Δ * (x_min / Δ) = x_min := by
      field_simp [hΔ_pos.ne'] <;> ring
    linarith
  have h_floor2 : x_min < Δ * ((k : ℝ) + 1) := by
    have h4 : x_min / Δ < ((k : ℝ) + 1) := Int.lt_floor_add_one (x_min / Δ)
    have h5 : x_min < Δ * (((k : ℝ) + 1)) := by
      calc x_min = Δ * (x_min / Δ) := by field_simp [hΔ_pos.ne'] <;> ring
        _ < Δ * (((k : ℝ) + 1)) := by gcongr
    exact h5

  have hP_in_square : (P_norm_Q : Set Plane) ⊆
      Metric.cthickening (2 * Δ) (squareSet Δ squareIndex) := by
    intro p hp
    have h_y : p 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := by
      rcases Finset.mem_image.mp hp with ⟨p_orig, h_orig, rfl⟩
      have h_sq : p_orig ∈ squareSet Δ Q := hP_phys_sub h_orig
      exact h_sq.2
    have h_x1 : Δ * (k : ℝ) ≤ p 0 := by
      have h : x_min ≤ p 0 := hx_min_le p hp
      linarith [h_floor1]
    have h_x2 : p 0 < Δ * ((k : ℝ) + 1) + 2 * Δ := by
      have h : p 0 < x_min + 2 * Δ := h_upper_bound p hp
      linarith [h_floor2]
    by_cases h_case : p 0 < Δ * ((k : ℝ) + 1)
    · -- p is already in the square
      have h_in : p ∈ squareSet Δ squareIndex := by
        simp only [squareIndex, squareSet]
        exact ⟨⟨h_x1, h_case⟩, h_y⟩
      have h_dist : dist p p ≤ 2 * Δ := by
        rw [dist_self]
        have h : 0 ≤ 2 * Δ := by positivity
        exact h
      exact Metric.mem_cthickening_of_dist_le p p (2 * Δ) (squareSet Δ squareIndex) h_in h_dist
    · -- p 0 ≥ (k+1)Δ, construct nearby point in the square
      have h_ge : Δ * ((k : ℝ) + 1) ≤ p 0 := by linarith
      set d : ℝ := p 0 - Δ * ((k : ℝ) + 1) with hd_def
      have hd_nonneg : 0 ≤ d := by linarith
      have hd_lt : d < 2 * Δ := by linarith
      set eps : ℝ := (2 * Δ - d) / 2 with heps_def
      have heps_pos : 0 < eps := by linarith
      have heps_le_Delta : eps ≤ Δ := by linarith
      set y0 : ℝ := Δ * ((k : ℝ) + 1) - eps with hy0_def
      have hy0_in1 : Δ * (k : ℝ) ≤ y0 := by linarith
      have hy0_in2 : y0 < Δ * ((k : ℝ) + 1) := by linarith
      let y : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm
        fun i : Fin 2 => if i = 0 then y0 else p 1
      have hy0 : y 0 = y0 := by
        simp [y, EuclideanSpace.equiv]
      have hy1 : y 1 = p 1 := by
        simp [y, EuclideanSpace.equiv]
      have hy_in_square : y ∈ squareSet Δ squareIndex := by
        simp only [squareIndex, squareSet, hy0, hy1]
        exact ⟨⟨hy0_in1, hy0_in2⟩, h_y⟩
      have h_diff1 : (p - y) 1 = 0 := by
        have h : p 1 - y 1 = 0 := by rw [hy1] <;> ring
        simpa using h
      have h_norm : ‖p - y‖ = |(p - y) 0| := by
        rw [EuclideanSpace.norm_eq]
        have h_sum : ∑ i : Fin 2, ‖(p - y) i‖ ^ 2 =
            ‖(p - y) 0‖ ^ 2 + ‖(p - y) 1‖ ^ 2 := by
          simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] <;> ring
        rw [h_sum]
        have h1 : ‖(p - y) 1‖ = 0 := by
          rw [Real.norm_eq_abs, h_diff1] <;> simp
        have h2 : ‖(p - y) 0‖ = |(p - y) 0| := by
          rw [Real.norm_eq_abs]
        rw [h1, h2]
        have h4 : |(p - y) 0| ^ 2 + (0 : ℝ) ^ 2 = |(p - y) 0| ^ 2 := by ring
        rw [h4]
        have h5 : 0 ≤ |(p - y) 0| := abs_nonneg _
        have h6 : Real.sqrt (|(p - y) 0| ^ 2) = |(p - y) 0| := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h5]
        exact h6
      have h_dist_le : dist p y ≤ 2 * Δ := by
        rw [dist_eq_norm, h_norm]
        have h_eq : (p - y) 0 = p 0 - y0 := by
          simp [hy0] <;> ring
        rw [h_eq]
        have h5 : p 0 - y0 = d + eps := by
          simp [hy0_def, hd_def] <;> ring
        rw [h5]
        have h6 : 0 ≤ d + eps := by linarith
        rw [abs_of_nonneg h6]
        have h7 : d + eps ≤ 2 * Δ := by
          simp [heps_def] <;> linarith
        exact h7
      exact Metric.mem_cthickening_of_dist_le p y (2 * Δ) (squareSet Δ squareIndex)
        hy_in_square h_dist_le

  -- Physical projection constant: F(z_Q) 0 = z_Q 0 - σ₀*z_Q 1 - h₀
  let c_Q : ℝ := z_Q 0 - σ₀ * z_Q 1 - h₀
  have h_c_Q_def : c_Q = z_Q 0 - σ₀ * z_Q 1 - h₀ := by rfl

  -- Dyadic δ-cells in FULLY sheared parameter space (a-σ₀, c-h₀)
  let f_cell (T : FineTube) : DyadicTubeCell δ :=
    dyadicCellOfParams δ hδ_pos (tubeSlope T - σ₀, tubeIntercept T - h₀)
  have h_f_cell_def : ∀ (T : FineTube), f_cell T =
      dyadicCellOfParams δ hδ_pos (tubeSlope T - σ₀, tubeIntercept T - h₀) := by
    intro T; rfl

  let fineTubes_norm (p : Plane) : Finset (DyadicTubeCell δ) :=
    if h : p ∈ P_norm_Q then
      let p_norm := normOfSheared p
      (sq.fineTubes p_norm).image f_cell
    else ∅

  let fineTubeOfCell (_p : Plane) (cell : DyadicTubeCell δ) : FineTube :=
    let params := paramsOfDyadicCell δ cell
    TubesAndSlopes.makeAffineLine params.1 params.2
  have h_fineTubeOfCell_def : ∀ (p : Plane) (cell : DyadicTubeCell δ),
      fineTubeOfCell p cell = TubesAndSlopes.makeAffineLine
        (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2 := by
    intro p cell; rfl

  have h_fine_def : ∀ p ∈ P_norm_Q,
      fineTubes_norm p = (sq.fineTubes (normOfSheared p)).image f_cell := by
    intro p hp
    simp [fineTubes_norm, hp]

  -- Helper: if p ∈ P_norm_Q, then normOfSheared p ∈ P'_Q
  have h_norm_mem : ∀ p ∈ P_norm_Q, normOfSheared p ∈ sq.P'_Q := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p_orig, h_orig, rfl⟩
    rcases Finset.mem_image.mp h_orig with ⟨q, hq, rfl⟩
    have h1 : Finv (F (sq.originalOfNorm q)) = sq.originalOfNorm q := hFinv_F _
    have h2 : normOfSheared (F (sq.originalOfNorm q)) = q := by
      have h_step1 : Finv (F (sq.originalOfNorm q)) = sq.originalOfNorm q := hFinv_F _
      have h_step2 : normOfSheared (F (sq.originalOfNorm q)) =
          (1 / Δ : ℝ) • (sq.originalOfNorm q - z_Q) := by
        simp [normOfSheared, h_step1]
      rw [h_step2]
      have h_step3 : sq.originalOfNorm q = Δ • q + z_Q := sq.h_norm_formula q hq
      rw [h_step3]
      have h_step4 : (1 / Δ : ℝ) • ((Δ • q + z_Q) - z_Q) = (1 / Δ : ℝ) • (Δ • q) := by
        congr 1 <;> abel
      rw [h_step4]
      simpa [smul_smul, hΔ_pos.ne'] using rfl
    rw [h2]
    exact hq

  have hfine_card_lower : ∀ p ∈ P_norm_Q,
      Real.rpow Δ (-s + 50 * ε) ≤ (fineTubes_norm p).card := by
    intro p hp
    let p_norm := normOfSheared p
    let S := sq.fineTubes p_norm
    have hp_norm_mem : p_norm ∈ sq.P'_Q := h_norm_mem p hp
    have h_sep : SeparatedAt (δ / 2) (S : Set FineTube) :=
      sq.hfine_tubes_separated p_norm hp_norm_mem
    have h_dir : ∀ T ∈ S, (LemmaE.getDirV T) 1 ≠ 0 :=
      fun T hT => sq.h_dirV_nonzero p_norm hp_norm_mem T hT
    have h_slope : ∀ T ∈ S, |tubeSlope T| ≤ 1 :=
      fun T hT => (sq.h_tube_param_bounds p_norm hp_norm_mem T hT).1
    have h_intercept : ∀ T ∈ S, |tubeIntercept T| ≤ 3 :=
      fun T hT => (sq.h_tube_param_bounds p_norm hp_norm_mem T hT).2
    have h_f_def : ∀ T ∈ S, f_cell T =
        (⌊(tubeSlope T - σ₀) / δ⌋, ⌊(tubeIntercept T - h₀) / δ⌋) := by
      intro T _
      dsimp only [f_cell, dyadicCellOfParams]
      <;> rfl
    have h_card_le : (S.card : ℝ) ≤ 144 * (S.image f_cell).card :=
      cell_image_lower_half δ hδ_pos S f_cell σ₀ h₀ h_sep h_dir h_slope h_intercept h_f_def
    have h_lower : Real.rpow Δ (-s + 40 * ε) ≤ (S.card : ℝ) :=
      sq.hfine_card_lower p_norm hp_norm_mem
    have hS : S = sq.fineTubes p_norm := by rfl
    have h_eq : fineTubes_norm p = S.image f_cell := by
      dsimp only [fineTubes_norm]
      rw [dif_pos hp]
      <;> rfl
    rw [h_eq]
    have h5 : (S.card : ℝ) ≤ 144 * ((S.image f_cell).card : ℝ) := by
      exact_mod_cast h_card_le
    have h7 : Real.rpow Δ (-s + 40 * ε) / 144 ≤ ((S.image f_cell).card : ℝ) := by
      calc Real.rpow Δ (-s + 40 * ε) / 144
        ≤ (S.card : ℝ) / 144 := by gcongr
      _ ≤ ((S.image f_cell).card : ℝ) := by linarith
    have h8 : Real.rpow Δ (-s + 50 * ε) ≤ Real.rpow Δ (-s + 40 * ε) / 144 := by
      have h9 : Real.rpow Δ ((-s + 40 * ε) + (10 * ε)) =
          Real.rpow Δ (-s + 40 * ε) * Real.rpow Δ (10 * ε) :=
        Real.rpow_add hΔ_pos (-s + 40 * ε) (10 * ε)
      have h_exp : (-s + 40 * ε) + (10 * ε) = -s + 50 * ε := by ring
      have h10 : Real.rpow Δ (-s + 50 * ε) =
          Real.rpow Δ (-s + 40 * ε) * Real.rpow Δ (10 * ε) := by
        rw [←h9, h_exp]
      rw [h10]
      have h11 : Real.rpow Δ (10 * ε) ≤ 1 / 144 := hΔ_packing
      have h12 : 0 ≤ Real.rpow Δ (-s + 40 * ε) := Real.rpow_nonneg (by linarith) _
      have h13 : Real.rpow Δ (-s + 40 * ε) * Real.rpow Δ (10 * ε) ≤
          Real.rpow Δ (-s + 40 * ε) * (1 / 144) := by
        exact mul_le_mul_of_nonneg_left h11 h12
      have h14 : Real.rpow Δ (-s + 40 * ε) * (1 / 144) =
          Real.rpow Δ (-s + 40 * ε) / 144 := by ring
      rw [h14] at h13
      exact h13
    exact le_trans h8 h7


  have hfine_card_upper : ∀ p ∈ P_norm_Q,
      (fineTubes_norm p).card ≤ Real.rpow Δ (-s - 7 * ε) := by
    intro p hp
    simp only [fineTubes_norm, dif_pos hp]
    let p_norm := normOfSheared p
    have hp_norm_mem : p_norm ∈ sq.P'_Q := h_norm_mem p hp
    have h_card : ((sq.fineTubes p_norm).image f_cell).card ≤ (sq.fineTubes p_norm).card :=
      Finset.card_image_le
    have h1 : (((sq.fineTubes p_norm).image f_cell).card : ℝ) ≤ ((sq.fineTubes p_norm).card : ℝ) :=
      by exact_mod_cast h_card
    have h2 : ((sq.fineTubes p_norm).card : ℝ) ≤ Real.rpow Δ (-s - 7 * ε) :=
      sq.hfine_card_upper p_norm hp_norm_mem
    exact_mod_cast le_trans h1 h2

  -- Physical projection: Pi_Q = Δ * Pi_norm + c_Q
  let Pi_Q : Set ℝ := {x' | ∃ x ∈ sq.proj.Pi, x' = Δ * x + c_Q}
  have h_Pi_Q_def : Pi_Q = (fun x : ℝ => Δ * x + c_Q) '' sq.proj.Pi := by
    ext x'
    simp only [Pi_Q, Set.mem_setOf_eq, Set.mem_image]
    <;> constructor <;> rintro ⟨x, hx, h⟩ <;> exact ⟨x, hx, by linarith⟩

  have hPi_Q_bounds : ∀ x ∈ Pi_Q, x ∈ Set.Icc (-6 : ℝ) 6 := by
    intro x' hx'
    rcases hx' with ⟨x, hx, rfl⟩
    have h1 : x ∈ sq.proj.projFun '' (sq.P'_Q : Set Plane) := sq.proj.hPi_sub hx
    rcases h1 with ⟨w, hw, rfl⟩
    let p_orig := sq.originalOfNorm w
    have hphys : p_orig = Δ • w + z_Q := sq.h_norm_formula w hw
    have h_in_PQ : p_orig ∈ sq.a4.base.P_Q := by
      have h : Δ • w + z_Q ∈ sq.a4.base.P_Q :=
        sq.a4.hP_norm_unnormalize w (sq.hP'_Q_sub hw)
      exact hphys ▸ h
    have h_in_ball : ‖p_orig‖ ≤ Real.sqrt 2 := by
      simpa [Metric.mem_closedBall] using sq.a4.base.hP_Q_in_ball h_in_PQ
    have hproj_eq : sq.proj.projFun w = w 0 - σ₀ * w 1 := by
      have hσ : sq.proj.σ = σ₀ := by
        rw [sq.proj.hσ_eq] <;> rfl
      have h1 : sq.proj.projFun = affineProj sq.proj.σ := sq.proj.hprojFun
      have h2 : sq.proj.projFun w = affineProj sq.proj.σ w := by rw [h1]
      rw [h2, hσ] <;> rfl
    have h_x'_eq : Δ * (sq.proj.projFun w) + c_Q = p_orig 0 - σ₀ * p_orig 1 - h₀ := by
      rw [hproj_eq, hphys]
      simp [c_Q] <;> ring
    rw [h_x'_eq]
    have h_p0 : |p_orig 0| ≤ Real.sqrt 2 := by
      have h : |p_orig 0| ≤ ‖p_orig‖ := h_coord_abs_le_norm p_orig 0
      linarith
    have h_p1 : |p_orig 1| ≤ Real.sqrt 2 := by
      have h : |p_orig 1| ≤ ‖p_orig‖ := h_coord_abs_le_norm p_orig 1
      linarith
    have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
    have h_sigma : |σ₀| ≤ 1 := by
      have h4 : |tubeSlope a8.a7.T0| ≤ 1 := a8.a7.hT0_slope_bound
      have h5 : σ₀ = tubeSlope a8.a7.T0 := congr_arg tubeSlope hT0_eq
      rw [h5]; exact h4
    have h_h0 : |h₀| ≤ 3 := by
      have h5 : |tubeIntercept a8.a7.T0| ≤ 3 := a8.a7.hT0_intercept_bound
      have h6 : h₀ = tubeIntercept a8.a7.T0 := congr_arg tubeIntercept hT0_eq
      rw [h6]; exact h5
    have h5 : |p_orig 0 - σ₀ * p_orig 1 - h₀| ≤
        |p_orig 0| + |σ₀| * |p_orig 1| + |h₀| := by
      calc |p_orig 0 - σ₀ * p_orig 1 - h₀|
        = |p_orig 0 + (-(σ₀ * p_orig 1)) + (-h₀)| := by ring_nf
      _ ≤ |p_orig 0 + (-(σ₀ * p_orig 1))| + |-h₀| := by
        exact abs_add_le _ _
      _ ≤ |p_orig 0| + |-(σ₀ * p_orig 1)| + |-h₀| := by
        have h2 : |p_orig 0 + (-(σ₀ * p_orig 1))| ≤ |p_orig 0| + |-(σ₀ * p_orig 1)| := abs_add_le _ _
        linarith
      _ = |p_orig 0| + |σ₀| * |p_orig 1| + |h₀| := by
        simp [abs_neg, abs_mul] <;> ring
    have h_sqrt2_le : Real.sqrt 2 ≤ 3 / 2 := by
      have hsq : (2 : ℝ) ≤ (3 / 2 : ℝ) ^ 2 := by norm_num
      have h_nonneg : 0 ≤ (3 / 2 : ℝ) := by norm_num
      exact Real.sqrt_le_iff.mpr ⟨h_nonneg, hsq⟩
    have h_p0' : |p_orig 0| ≤ 3 / 2 := by linarith [h_p0, h_sqrt2_le]
    have h_p1' : |p_orig 1| ≤ 3 / 2 := by linarith [h_p1, h_sqrt2_le]
    have h6 : |p_orig 0 - σ₀ * p_orig 1 - h₀| ≤ 6 := by
      calc |p_orig 0 - σ₀ * p_orig 1 - h₀|
        ≤ |p_orig 0| + |σ₀| * |p_orig 1| + |h₀| := h5
      _ ≤ (3 / 2 : ℝ) + 1 * (3 / 2 : ℝ) + 3 := by
        gcongr <;> linarith
      _ = 6 := by norm_num
    exact abs_le.mp h6

  have hPi_Q_nonempty : Pi_Q.Nonempty := by
    have hPi_nonempty : sq.proj.Pi.Nonempty := by
      by_contra h
      have h_empty : sq.proj.Pi = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have hcov : Metric.externalCoveringNumber Δ.toNNReal sq.proj.Pi = 0 := by
        rw [h_empty]; simp
      have h_lower : ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤
          Metric.externalCoveringNumber Δ.toNNReal sq.proj.Pi := sq.proj.hPi_lower
      rw [hcov] at h_lower
      have h_rpow_pos : 0 < Real.rpow Δ (576 * ε - s) := Real.rpow_pos_of_pos hΔ_pos _
      have h_pos : 0 < ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) :=
        ENNReal.ofReal_pos.mpr h_rpow_pos
      have h_contra : ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤ 0 := by simpa using h_lower
      exact not_le.mpr h_pos h_contra
    rcases hPi_nonempty with ⟨x, hx⟩
    let w := sq.proj.witness x
    have hw_mem : w ∈ sq.P'_Q := sq.proj.h_witness_mem x hx
    have hproj : sq.proj.projFun w = x := sq.proj.h_witness_proj x hx
    exact ⟨Δ * x + c_Q, ⟨x, hx, rfl⟩⟩
  have hPi_Q_sset : IsDeltaSSet Δ s (Real.rpow Δ (-s - 49 * ε)) Pi_Q := by
    have hC_pos : 0 < Real.rpow Δ (-s - 49 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_const : Real.rpow Δ (-s - 49 * ε) * Real.rpow Δ s ≥ 1 := by
      have h_add : Real.rpow Δ (-s - 49 * ε) * Real.rpow Δ s =
          Real.rpow Δ ((-s - 49 * ε) + s) :=
        (Real.rpow_add hΔ_pos (-s - 49 * ε) s).symm
      have h_exp : (-s - 49 * ε) + s = -49 * ε := by ring
      have h2 : Real.rpow Δ (-s - 49 * ε) * Real.rpow Δ s = Real.rpow Δ (-49 * ε) := by
        rw [h_add, h_exp]
      rw [h2]
      have h_pos2 : 0 < Real.rpow Δ (49 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h_lt1 : Real.rpow Δ (49 * ε) < 1 :=
        Real.rpow_lt_one (by linarith) (by linarith) (by linarith)
      have h_neg : Real.rpow Δ (-49 * ε) = (Real.rpow Δ (49 * ε))⁻¹ := by
        have h_eq : (-49 * ε) = -(49 * ε) := by ring
        rw [h_eq]
        exact Real.rpow_neg hΔ_pos.le (y := (49 * ε))
      rw [h_neg]
      have h_ge : (Real.rpow Δ (49 * ε))⁻¹ ≥ 1 := by
        have h_le : Real.rpow Δ (49 * ε) ≤ 1 := by linarith
        exact one_le_inv₀ h_pos2 |>.mpr h_le
      exact h_ge
    exact bounded_set_is_sset_of_large_constant_general hΔ_pos hs hC_pos h_const
      hPi_Q_nonempty hPi_Q_bounds

  -- Witness: physical sheared point with given x-coordinate
  let witness (x' : ℝ) : Plane :=
    F (sq.originalOfNorm (sq.proj.witness ((x' - c_Q) / Δ)))

  have h_witness : ∀ x' ∈ Pi_Q, witness x' ∈ P_norm_Q ∧ (witness x') 0 = x' := by
    intro x' hx'
    rcases hx' with ⟨x, hx, rfl⟩
    let w := sq.proj.witness x
    have hw_mem : w ∈ sq.P'_Q := sq.proj.h_witness_mem x hx
    have hproj : sq.proj.projFun w = x := sq.proj.h_witness_proj x hx
    have hproj_eq : sq.proj.projFun w = w 0 - σ₀ * w 1 := by
      have hσ : sq.proj.σ = σ₀ := by
        rw [sq.proj.hσ_eq] <;> rfl
      have h1 : sq.proj.projFun = affineProj sq.proj.σ := sq.proj.hprojFun
      have h2 : sq.proj.projFun w = affineProj sq.proj.σ w := by rw [h1]
      rw [h2, hσ] <;> rfl
    have h_eq1 : w 0 - σ₀ * w 1 = x := by
      rw [←hproj_eq, hproj]
    have h_phys : sq.originalOfNorm w = Δ • w + z_Q := sq.h_norm_formula w hw_mem
    have h_xcoord : (F (sq.originalOfNorm w)) 0 = Δ * x + c_Q := by
      rw [h_phys]
      have h7 : (F (Δ • w + z_Q)) 0 = Δ * (w 0 - σ₀ * w 1) + c_Q := by
        simp [F, AffineNormalization.normalizeMap, c_Q] <;> ring
      rw [h7, h_eq1] <;> ring
    have h_wit_eq : witness (Δ * x + c_Q) = F (sq.originalOfNorm w) := by
      simp [witness] <;> congr <;> field_simp [hΔ_pos.ne'] <;> ring
    constructor
    · -- witness x' ∈ P_norm_Q
      simp only [P_norm_Q, P_orig_Q, Finset.mem_image]
      exact ⟨sq.originalOfNorm w, ⟨w, hw_mem, rfl⟩, h_wit_eq.symm⟩
    · -- (witness x') 0 = x'
      rw [h_wit_eq]
      exact h_xcoord

  have h_witness_y_close : ∀ x' ∈ Pi_Q,
      |(witness x') 1 - y_Q| ≤ 3 * Δ := by
    intro x' hx'
    rcases hx' with ⟨x, hx, rfl⟩
    let w := sq.proj.witness x
    have hw_mem : w ∈ sq.P'_Q := sq.proj.h_witness_mem x hx
    have h_wit_eq : witness (Δ * x + c_Q) = F (sq.originalOfNorm w) := by
      simp [witness] <;> congr <;> field_simp [hΔ_pos.ne'] <;> ring
    have h_phys : sq.originalOfNorm w = Δ • w + z_Q := sq.h_norm_formula w hw_mem
    have h_in_PQ : Δ • w + z_Q ∈ sq.a4.base.P_Q :=
      sq.a4.hP_norm_unnormalize w (sq.hP'_Q_sub hw_mem)
    have h_in_sq : Δ • w + z_Q ∈ squareSet Δ Q :=
      sq.a4.base.hP_Q_in_square h_in_PQ
    have h_y_range : (Δ • w + z_Q) 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) :=
      h_in_sq.2
    have h_y1 : (witness (Δ * x + c_Q)) 1 = (Δ • w + z_Q) 1 := by
      rw [h_wit_eq, h_phys] <;> simp [F, AffineNormalization.normalizeMap]
    rw [h_y1]
    rcases h_y_range with ⟨hlo, hhi⟩
    have h_yQ_eq : y_Q = Δ * (Q.2 : ℝ) := by
      simp [y_Q, squareY] <;> ring
    rw [h_yQ_eq]
    have h6 : 0 ≤ (Δ • w + z_Q) 1 - Δ * (Q.2 : ℝ) := by linarith
    have h7 : (Δ • w + z_Q) 1 - Δ * (Q.2 : ℝ) < Δ := by linarith
    rw [abs_of_nonneg h6]
    linarith

  have h_residual : ∀ x' ∈ Pi_Q,
      ∀ (cell : DyadicTubeCell δ), cell ∈ fineTubes_norm (witness x') →
        |x' - tubeSlope (fineTubeOfCell (witness x') cell) * (witness x') 1 -
          tubeIntercept (fineTubeOfCell (witness x') cell)| ≤ 6 * δ := by
    intro x' hx' cell hcell
    rcases hx' with ⟨x, hx, rfl⟩
    let w := sq.proj.witness x
    have hw_mem : w ∈ sq.P'_Q := sq.proj.h_witness_mem x hx
    let p_orig := sq.originalOfNorm w
    have h_simp : (Δ * x + c_Q - c_Q) / Δ = x := by
      field_simp [hΔ_pos.ne'] <;> ring
    have h_wit_eq : witness (Δ * x + c_Q) = F p_orig := by
      have h : witness (Δ * x + c_Q) = F (sq.originalOfNorm (sq.proj.witness ((Δ * x + c_Q - c_Q) / Δ))) := by
        rfl
      rw [h, h_simp]
      <;> rfl
    have h_eq1 : w 0 - σ₀ * w 1 = x := by
      have hproj : sq.proj.projFun w = x := sq.proj.h_witness_proj x hx
      have hσ : sq.proj.σ = σ₀ := by
        rw [sq.proj.hσ_eq] <;> rfl
      have hproj_eq : sq.proj.projFun w = w 0 - σ₀ * w 1 := by
        have h1 : sq.proj.projFun = affineProj sq.proj.σ := sq.proj.hprojFun
        have h2 : sq.proj.projFun w = affineProj sq.proj.σ w := by rw [h1]
        rw [h2, hσ]
        <;> rfl
      rw [hproj_eq] at hproj
      exact hproj
    have h_x'_eq : Δ * x + c_Q = p_orig 0 - σ₀ * p_orig 1 - h₀ := by
      have h_phys : p_orig = Δ • w + z_Q := sq.h_norm_formula w hw_mem
      have h1 : p_orig 0 = Δ * w 0 + z_Q 0 := by
        rw [h_phys] <;> simp
      have h2 : p_orig 1 = Δ * w 1 + z_Q 1 := by
        rw [h_phys] <;> simp
      have h : p_orig 0 - σ₀ * p_orig 1 - h₀ = Δ * x + c_Q := by
        rw [h1, h2]
        have h_cQ : c_Q = z_Q 0 - σ₀ * z_Q 1 - h₀ := by rfl
        rw [h_cQ]
        have h4 : (Δ * w 0 + z_Q 0) - σ₀ * (Δ * w 1 + z_Q 1) - h₀ =
                 Δ * (w 0 - σ₀ * w 1) + (z_Q 0 - σ₀ * z_Q 1 - h₀) := by ring
        rw [h4, h_eq1] <;> ring
      exact h.symm
    have h_y'_eq : (witness (Δ * x + c_Q)) 1 = p_orig 1 := by
      rw [h_wit_eq] <;> simp [F, AffineNormalization.normalizeMap]
    have h_norm_eq : normOfSheared (witness (Δ * x + c_Q)) = w := by
      rw [h_wit_eq]
      have h1 : normOfSheared (F p_orig) = (1 / Δ : ℝ) • (Finv (F p_orig) - z_Q) := by
        rfl
      rw [h1]
      have h2 : Finv (F p_orig) = p_orig := hFinv_F p_orig
      rw [h2]
      have h3 : p_orig = Δ • w + z_Q := sq.h_norm_formula w hw_mem
      rw [h3]
      have h4 : (1 / Δ : ℝ) • ((Δ • w + z_Q) - z_Q) = (1 / Δ : ℝ) • (Δ • w) := by
        congr 1 <;> abel
      rw [h4]
      have h5 : (1 / Δ : ℝ) • (Δ • w) = w := by
        simpa [smul_smul, hΔ_pos.ne'] using rfl
      exact h5
    simp only [fineTubes_norm, dif_pos (h_witness (Δ * x + c_Q) (by exact ⟨x, hx, rfl⟩)).1] at hcell
    rw [h_norm_eq] at hcell
    rcases Finset.mem_image.mp hcell with ⟨_T_orig, _hT_orig, h_cell_f⟩
    let p_norm := w
    have hp_norm_mem : p_norm ∈ sq.P'_Q := hw_mem
    set a_orig : ℝ := tubeSlope _T_orig with ha_orig_def
    set b_orig : ℝ := tubeIntercept _T_orig with hb_orig_def
    have h_a_bound : |a_orig| ≤ 1 := (sq.h_tube_param_bounds p_norm hp_norm_mem _T_orig _hT_orig).1
    have h_b_bound : |b_orig| ≤ 3 := (sq.h_tube_param_bounds p_norm hp_norm_mem _T_orig _hT_orig).2
    have hv : (LemmaE.getDirV _T_orig) 1 ≠ 0 := sq.h_dirV_nonzero p_norm hp_norm_mem _T_orig _hT_orig
    have h_inc : p_orig ∈ Metric.cthickening (2 * δ) (_T_orig.1 : Set Plane) :=
      sq.hfine_inc p_norm hp_norm_mem _T_orig _hT_orig
    have h_res_orig : |p_orig 0 - a_orig * p_orig 1 - b_orig| ≤
        Real.sqrt (1 + a_orig^2) * (2 * δ) :=
      residual_from_cthickening p_orig _T_orig (2 * δ) (by positivity) hv h_inc
    have h_py_abs : |p_orig 1| ≤ Real.sqrt 2 := by
      have h1 : p_orig ∈ Metric.closedBall 0 (Real.sqrt 2) :=
        sq.a4.base.hP_Q_in_ball (sq.h_originalOfNorm p_norm hp_norm_mem)
      have h2 : |p_orig 1| ≤ ‖p_orig‖ := h_coord_abs_le_norm p_orig 1
      have h3 : ‖p_orig‖ ≤ Real.sqrt 2 := by simpa [Metric.mem_closedBall] using h1
      linarith
    set a' : ℝ := a_orig - σ₀ with ha'_def
    set b' : ℝ := b_orig - h₀ with hb'_def
    set a_T : ℝ := (paramsOfDyadicCell δ cell).1 with haT_def
    set b_T : ℝ := (paramsOfDyadicCell δ cell).2 with hbT_def
    set T_recon : FineTube := fineTubeOfCell (witness (Δ * x + c_Q)) cell with hT_recon_def
    have h_cell_eq : cell = (⌊a' / δ⌋, ⌊b' / δ⌋) := by
      have h : f_cell _T_orig = (⌊a' / δ⌋, ⌊b' / δ⌋) := by
        dsimp only [f_cell, dyadicCellOfParams] <;> rfl
      exact h_cell_f.symm.trans h
    have ha_quant1 : 0 ≤ a' - a_T := by
      have h_eq1 : a_T = δ * (cell.1 : ℝ) := by
        simp [haT_def, paramsOfDyadicCell] <;> ring
      have h_cell1 : (cell.1 : ℝ) = (⌊a' / δ⌋ : ℝ) := by
        rw [h_cell_eq] <;> simp
      rw [h_eq1, h_cell1]
      have h_floor : (⌊a' / δ⌋ : ℝ) ≤ a' / δ := Int.floor_le (a' / δ)
      have h : δ * (⌊a' / δ⌋ : ℝ) ≤ a' := by
        calc δ * (⌊a' / δ⌋ : ℝ) ≤ δ * (a' / δ) := by gcongr
          _ = a' := by field_simp [hδ_pos.ne'] <;> ring
      linarith
    have ha_quant2 : a' - a_T < δ := by
      have h_eq1 : a_T = δ * (cell.1 : ℝ) := by
        simp [haT_def, paramsOfDyadicCell] <;> ring
      have h_cell1 : (cell.1 : ℝ) = (⌊a' / δ⌋ : ℝ) := by
        rw [h_cell_eq] <;> simp
      rw [h_eq1, h_cell1]
      have h_floor : a' / δ < ((⌊a' / δ⌋ : ℝ) + 1) := Int.lt_floor_add_one (a' / δ)
      have h : a' < δ * (((⌊a' / δ⌋ : ℝ) + 1)) := by
        calc a' = δ * (a' / δ) := by field_simp [hδ_pos.ne'] <;> ring
          _ < δ * (((⌊a' / δ⌋ : ℝ) + 1)) := by gcongr
      have h2 : δ * (((⌊a' / δ⌋ : ℝ) + 1)) = δ * (⌊a' / δ⌋ : ℝ) + δ := by ring
      linarith
    have hb_quant1 : 0 ≤ b' - b_T := by
      have h_eq1 : b_T = δ * (cell.2 : ℝ) := by
        simp [hbT_def, paramsOfDyadicCell] <;> ring
      have h_cell2 : (cell.2 : ℝ) = (⌊b' / δ⌋ : ℝ) := by
        rw [h_cell_eq] <;> simp
      rw [h_eq1, h_cell2]
      have h_floor : (⌊b' / δ⌋ : ℝ) ≤ b' / δ := Int.floor_le (b' / δ)
      have h : δ * (⌊b' / δ⌋ : ℝ) ≤ b' := by
        calc δ * (⌊b' / δ⌋ : ℝ) ≤ δ * (b' / δ) := by gcongr
          _ = b' := by field_simp [hδ_pos.ne'] <;> ring
      linarith
    have hb_quant2 : b' - b_T < δ := by
      have h_eq1 : b_T = δ * (cell.2 : ℝ) := by
        simp [hbT_def, paramsOfDyadicCell] <;> ring
      have h_cell2 : (cell.2 : ℝ) = (⌊b' / δ⌋ : ℝ) := by
        rw [h_cell_eq] <;> simp
      rw [h_eq1, h_cell2]
      have h_floor : b' / δ < ((⌊b' / δ⌋ : ℝ) + 1) := Int.lt_floor_add_one (b' / δ)
      have h : b' < δ * (((⌊b' / δ⌋ : ℝ) + 1)) := by
        calc b' = δ * (b' / δ) := by field_simp [hδ_pos.ne'] <;> ring
          _ < δ * (((⌊b' / δ⌋ : ℝ) + 1)) := by gcongr
      have h2 : δ * (((⌊b' / δ⌋ : ℝ) + 1)) = δ * (⌊b' / δ⌋ : ℝ) + δ := by ring
      linarith
    have h1 : tubeSlope T_recon = a_T := by
      have h_params : LemmaE.affineLineParams T_recon = (a_T, b_T) := by
        simp [T_recon, fineTubeOfCell, haT_def, hbT_def, paramsOfDyadicCell,
          TubesAndSlopes.makeAffineLine_params] <;> rfl
      have h : tubeSlope T_recon = (LemmaE.affineLineParams T_recon).1 := by
        rfl
      rw [h, h_params] <;> rfl
    have h2 : tubeIntercept T_recon = b_T := by
      have h_params : LemmaE.affineLineParams T_recon = (a_T, b_T) := by
        simp [T_recon, fineTubeOfCell, haT_def, hbT_def, paramsOfDyadicCell,
          TubesAndSlopes.makeAffineLine_params] <;> rfl
      have h : tubeIntercept T_recon = (LemmaE.affineLineParams T_recon).2 := by
        rfl
      rw [h, h_params] <;> rfl
    have h_main : |(Δ * x + c_Q) - tubeSlope T_recon * (witness (Δ * x + c_Q)) 1 - tubeIntercept T_recon| ≤ 6 * δ := by
      have h_goal : (Δ * x + c_Q) - tubeSlope T_recon * (witness (Δ * x + c_Q)) 1 - tubeIntercept T_recon =
          (Δ * x + c_Q) - tubeSlope T_recon * p_orig 1 - tubeIntercept T_recon := by
        rw [h_y'_eq]
      rw [h_goal, h1, h2]
      exact residual_bound_core δ hδ_pos σ₀ h₀ p_orig a_orig b_orig h_a_bound h_py_abs h_res_orig a_T b_T
        ha_quant1 ha_quant2 hb_quant1 hb_quant2 (Δ * x + c_Q) h_x'_eq
    simpa [hT_recon_def] using h_main

  have hfine_cell_bounds : ∀ p ∈ P_norm_Q, ∀ cell ∈ fineTubes_norm p,
      |(paramsOfDyadicCell δ cell).1| ≤ 7 * Δ ∧ |(paramsOfDyadicCell δ cell).2| ≤ 7 * Δ := by
    intro p hp cell hcell
    have h_fine_def : fineTubes_norm p = (sq.fineTubes (normOfSheared p)).image f_cell := by
      simp [fineTubes_norm, hp]
    rw [h_fine_def] at hcell
    rcases Finset.mem_image.mp hcell with ⟨T_orig, hT_orig, hcell_eq⟩
    let p_norm := normOfSheared p
    have hp_norm_mem : p_norm ∈ sq.P'_Q := h_norm_mem p hp
    have h_in_parent : InParent Δ hΔ_pos T_orig T0 := by
      have h_pf : sq.fineTubes p_norm = pointFiber Δ hΔ_pos sq.a4.base.T_Q (sq.originalOfNorm p_norm) T0 :=
        sq.hfine_eq_pointFiber p_norm hp_norm_mem
      rw [h_pf] at hT_orig
      exact (Finset.mem_filter.mp hT_orig).2
    have h_slope_floor : ⌊tubeSlope T_orig / Δ⌋ = ⌊tubeSlope T0 / Δ⌋ :=
      congr_arg Prod.fst h_in_parent
    have h_intercept_floor : ⌊tubeIntercept T_orig / Δ⌋ = ⌊tubeIntercept T0 / Δ⌋ :=
      congr_arg Prod.snd h_in_parent
    have h_slope_diff : |tubeSlope T_orig - tubeSlope T0| < Δ := by
      exact abs_sub_lt_of_same_floor hΔ_pos h_slope_floor
    have h_intercept_diff : |tubeIntercept T_orig - tubeIntercept T0| < Δ := by
      exact abs_sub_lt_of_same_floor hΔ_pos h_intercept_floor
    have hcell1 : cell.1 = ⌊(tubeSlope T_orig - σ₀) / δ⌋ := by
      have h := congr_arg Prod.fst hcell_eq
      simpa [f_cell, dyadicCellOfParams] using h.symm
    have hcell2 : cell.2 = ⌊(tubeIntercept T_orig - h₀) / δ⌋ := by
      have h := congr_arg Prod.snd hcell_eq
      simpa [f_cell, dyadicCellOfParams] using h.symm
    have hσ_eq : σ₀ = tubeSlope T0 := by rfl
    have hh_eq : h₀ = tubeIntercept T0 := by rfl
    have h_slope_diff' : |tubeSlope T_orig - σ₀| < Δ := by
      rw [hσ_eq] <;> exact h_slope_diff
    have h_intercept_diff' : |tubeIntercept T_orig - h₀| < Δ := by
      rw [hh_eq] <;> exact h_intercept_diff
    have h_bound1 : |δ * (cell.1 : ℝ)| ≤ Δ + δ := by
      rw [hcell1]
      have h_floor : |δ * ⌊(tubeSlope T_orig - σ₀) / δ⌋| ≤ |tubeSlope T_orig - σ₀| + δ :=
        floor_mul_abs_bound hδ_pos
      have h_help : |tubeSlope T_orig - σ₀| + δ ≤ Δ + δ := by
        have h : |tubeSlope T_orig - σ₀| ≤ Δ := le_of_lt h_slope_diff'
        exact add_le_add h (by linarith)
      exact le_trans h_floor h_help
    have h_bound2 : |δ * (cell.2 : ℝ)| ≤ Δ + δ := by
      rw [hcell2]
      have h_floor : |δ * ⌊(tubeIntercept T_orig - h₀) / δ⌋| ≤ |tubeIntercept T_orig - h₀| + δ :=
        floor_mul_abs_bound hδ_pos
      have h_help2 : |tubeIntercept T_orig - h₀| + δ ≤ Δ + δ := by
        have h : |tubeIntercept T_orig - h₀| ≤ Δ := le_of_lt h_intercept_diff'
        exact add_le_add h (by linarith)
      exact le_trans h_floor h_help2
    have hδ2 : δ ≤ Δ := by
      rw [hδ_eq]
      have h_pos : 0 ≤ Δ := by linarith
      have h_lt_one : Δ < 1 := by linarith [hΔ_lt_half]
      have h_sq_le : Δ ^ 2 ≤ Δ := by
        calc Δ ^ 2 = Δ * Δ := by ring
          _ ≤ Δ * 1 := by gcongr <;> linarith
          _ = Δ := by ring
      exact h_sq_le
    have h_params1 : (paramsOfDyadicCell δ cell).1 = δ * (cell.1 : ℝ) := by
      simp [paramsOfDyadicCell]
    have h_params2 : (paramsOfDyadicCell δ cell).2 = δ * (cell.2 : ℝ) := by
      simp [paramsOfDyadicCell]
    exact ⟨by rw [h_params1] <;> linarith [h_bound1, hδ2],
           by rw [h_params2] <;> linarith [h_bound2, hδ2]⟩
  exact
    { hδ_pos := hδ_pos
      T0 := T0
      sq := sq
      z_Q := z_Q
      P_orig_Q := P_orig_Q
      hP_orig_Q_eq := by rfl
      F := F
      hF_def := by rfl
      P_norm_Q := P_norm_Q
      hP_norm_Q_eq := by rfl
      normOfSheared := normOfSheared
      h_norm_mem := h_norm_mem
      hP_phys_sub := hP_phys_sub
      hP_phys_card := hP_phys_card
      hP_norm_Q_card := by
        have h_inj : Set.InjOn F (P_orig_Q : Set Plane) := fun x _ y _ hxy => hF_inj hxy
        dsimp only [P_norm_Q]
        rw [Finset.card_image_of_injOn h_inj]
      hP_orig_Q_card := by
        dsimp only [P_orig_Q]
        rw [Finset.card_image_of_injOn h_orig_inj]
      hy_Q_bounds := hy_Q_bounds
      squareIndex := squareIndex
      hP_in_square := hP_in_square
      c_Q := c_Q
      h_c_Q_def := h_c_Q_def
      Pi_Q := Pi_Q
      h_Pi_Q_def := h_Pi_Q_def
      hPi_Q_bounds := hPi_Q_bounds
      hPi_Q_sset := hPi_Q_sset
      f_cell := f_cell
      h_f_cell_def := h_f_cell_def
      fineTubes_norm := fineTubes_norm
      fineTubeOfCell := fineTubeOfCell
      h_fineTubeOfCell_def := h_fineTubeOfCell_def
      hfine_card_lower := hfine_card_lower
      hfine_card_upper := hfine_card_upper
      h_fine_def := h_fine_def
      hfine_cell_bounds := hfine_cell_bounds
      witness := witness
      h_witness := h_witness
      h_witness_y_close := h_witness_y_close
      h_residual := h_residual
      h_orig_inj := h_orig_inj }

end AppendixA
end DirecretisedFurstenbergEstimate
