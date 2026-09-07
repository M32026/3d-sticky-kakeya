module

/-
  Geometric bounds and external data for B1BridgeDecomposition.

  Proves:
  - Numerical constant absorption (h_tube_sset_absorb, hK_pack_bound)
  - Geometric bounds from NiceConfiguration construction (h_squares_unit)
  - Tube geometric bounds (h_tubes_strip, h_tubes_intercept) from slope/intercept
  - Point S-set transfer integration (point_sset_transfer_integrated):
    transfers S-set from original points to square centers with constant
    δ^{-2ε} and ball-growth Δ^{-9ε/4}

  Blocked pending:
  - Genuine tube S-set transfer for hC_fine_bound
  - h_tubes_strip and h_tubes_intercept require slope/intercept bounds
    from the original AffineLine families

  Whiteprint node: geometric_and_external
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.LocalSquareCenter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.LegacyRoundSnapConstruct
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.PointSSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.DyadicSquareCenterSeparation
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.SsetExtractionBounds
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AssemblyNumerical

/-! ### Numerical constant absorption -/

/-- Absorb a constant into δ^{-α} for sufficiently small δ.
    The threshold Δ₀ = C^{-(1/α)} works. -/
lemma absorb_const_delta (C α : ℝ) (hC : 0 < C) (hα : 0 < α) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_small : δ < C ^ (-(1 / α))) :
    C ≤ Real.rpow δ (-α) := by
  let Δ₀ : ℝ := C ^ (-(1 / α))
  have hΔ₀_pos : 0 < Δ₀ := by positivity
  have h_main : ∀ (x : ℝ), 0 < x → x < Δ₀ → C ≤ Real.rpow x (-α) := by
    intro x hx_pos hx_lt
    have h5 : (Δ₀ ^ α) = 1 / C := by
      have h6 : Δ₀ ^ α = C ^ ((-(1 / α)) * α) := by
        rw [← Real.rpow_mul (by linarith)] <;> ring
      rw [h6]
      have h7 : (-(1 / α)) * α = -1 := by field_simp [hα.ne'] <;> ring
      rw [h7]
      have h8 : C ^ (-1 : ℝ) = 1 / C := by
        rw [Real.rpow_neg (by linarith)] <;> simp
      exact h8
    have h3 : x ^ α < 1 / C := by
      have h4 : x ^ α < Δ₀ ^ α := Real.rpow_lt_rpow (by linarith) hx_lt hα
      rw [h5] at h4
      exact h4
    have h_pos : 0 < x ^ α := Real.rpow_pos_of_pos hx_pos α
    have h9 : (x ^ α)⁻¹ > C := by
      have h10 : (x ^ α)⁻¹ > (1 / C)⁻¹ := by gcongr
      have h11 : (1 / C)⁻¹ = C := by field_simp [hC.ne']
      rw [h11] at h10
      exact h10
    have h7 : Real.rpow x (-α) = (Real.rpow x α)⁻¹ := by
      have h71 := Real.rpow_neg hx_pos.le α
      exact h71
    rw [h7]
    exact le_of_lt h9
  exact h_main δ hδ_pos hδ_small

/-- For s ∈ (0,1), 4000 * 44^s is bounded by 4000 * 44. -/
lemma tube_sset_absorb_const_bound (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (4000 : ℝ) * (44 : ℝ)^s ≤ 4000 * 44 := by
  have h1 : (44 : ℝ)^s ≤ (44 : ℝ) := by
    have h2 : s ≤ 1 := by linarith
    have h3 : (44 : ℝ)^s ≤ (44 : ℝ)^(1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    have h4 : (44 : ℝ)^(1 : ℝ) = (44 : ℝ) := by simp
    rw [h4] at h3
    exact h3
  have h5 : (4000 : ℝ) * (44 : ℝ)^s ≤ (4000 : ℝ) * (44 : ℝ) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  exact h5

/-- h_tube_sset_absorb: 4000 * 44^s ≤ δ^{-ε/2} for small δ. -/
lemma tube_sset_absorb (s ε : ℝ) (hs : 0 < s) (hs1 : s < 1) (hε : 0 < ε)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_small : δ < ((4000 * 44 : ℝ) ^ (-(1 / (ε / 2))))) :
    (4000 : ℝ) * (44 : ℝ)^s ≤ Real.rpow δ (-(ε / 2)) := by
  have h1 : (4000 : ℝ) * (44 : ℝ)^s ≤ 4000 * 44 :=
    tube_sset_absorb_const_bound s hs hs1
  have h2 : (4000 * 44 : ℝ) ≤ Real.rpow δ (-(ε / 2)) :=
    absorb_const_delta (4000 * 44) (ε / 2) (by norm_num) (by linarith) δ hδ_pos hδ_small
  exact le_trans h1 h2

/-- hK_pack_bound: K_pack ≤ Δ^{-2ε}/6 for small Δ. -/
lemma K_pack_absorb (K_pack ε Δ : ℝ) (hK_pos : 0 < K_pack) (hε : 0 < ε)
    (hΔ_pos : 0 < Δ) (hΔ_small : Δ < ((6 * K_pack) ^ (-(1 / (2 * ε))))) :
    K_pack ≤ Real.rpow Δ (-(2 * ε)) / 6 := by
  have h1 : 6 * K_pack ≤ Real.rpow Δ (-(2 * ε)) :=
    absorb_const_delta (6 * K_pack) (2 * ε) (by positivity) (by positivity) Δ hΔ_pos hΔ_small
  linarith

/-! ### Geometric bounds from NiceConfiguration construction -/

/-- h_squares_unit: dyadic squares intersecting [0,1]^2 have indices in [0, 2^n).

    Requires the point set P to be contained in [0,1]^2. If the original P is in
    closedBall 0 1, a normalization step (translation by (1,1) and scaling by 1/2)
    is needed first. -/
lemma squares_unit_from_cover {n : ℕ} {P : Set Plane}
    (hP_unit : P ⊆ {p : Plane | 0 ≤ p 0 ∧ p 0 < 1 ∧ 0 ≤ p 1 ∧ p 1 < 1})
    (squares : Finset (DyadicSquare n))
    (h_intersect : ∀ q ∈ squares, (P ∩ (q.toSet : Set Plane)).Nonempty) :
    ∀ q ∈ squares, 0 ≤ q.i ∧ q.i < (2 ^ n : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ n : ℤ) := by
  intro q hq
  have h_int : (P ∩ (q.toSet : Set Plane)).Nonempty := h_intersect q hq
  rcases h_int with ⟨p, hpP, hpQ⟩
  have hp_unit : 0 ≤ p 0 ∧ p 0 < 1 ∧ 0 ≤ p 1 ∧ p 1 < 1 := hP_unit hpP
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : δ = 1 / (2 : ℝ)^n := by
    simp only [hδ, dyadicDelta] <;> field_simp
  have hi1 : (q.i : ℝ) * δ ≤ p 0 := hpQ.1
  have hi2 : p 0 < ((q.i : ℝ) + 1) * δ := hpQ.2.1
  have hj1 : (q.j : ℝ) * δ ≤ p 1 := hpQ.2.2.1
  have hj2 : p 1 < ((q.j : ℝ) + 1) * δ := hpQ.2.2.2
  have h_i_nonneg : 0 ≤ q.i := by
    by_contra h
    have h' : q.i ≤ -1 := by linarith
    have h'' : (q.i : ℝ) ≤ -1 := by exact_mod_cast h'
    have h3 : ((q.i : ℝ) + 1) * δ ≤ 0 := by
      have h4 : (q.i : ℝ) + 1 ≤ 0 := by linarith
      nlinarith [hδ_pos]
    have h5 : 0 ≤ p 0 := hp_unit.1
    linarith [hi2, h3]
  have h_i_lt : q.i < (2 ^ n : ℤ) := by
    by_contra h
    have h' : q.i ≥ (2 ^ n : ℤ) := by linarith
    have h'' : (q.i : ℝ) ≥ (2 ^ n : ℝ) := by exact_mod_cast h'
    have h3 : (q.i : ℝ) * δ ≥ 1 := by
      rw [hδ_eq]
      have h4 : (q.i : ℝ) ≥ (2 ^ n : ℝ) := h''
      calc (q.i : ℝ) * (1 / (2 : ℝ)^n)
        ≥ (2 ^ n : ℝ) * (1 / (2 : ℝ)^n) := by gcongr
      _ = 1 := by
        have h5 : (2 : ℝ)^n > 0 := by positivity
        field_simp [h5.ne'] <;> ring
    have h4 : p 0 < 1 := hp_unit.2.1
    linarith [hi1, h3]
  have h_j_nonneg : 0 ≤ q.j := by
    by_contra h
    have h' : q.j ≤ -1 := by linarith
    have h'' : (q.j : ℝ) ≤ -1 := by exact_mod_cast h'
    have h3 : ((q.j : ℝ) + 1) * δ ≤ 0 := by
      have h4 : (q.j : ℝ) + 1 ≤ 0 := by linarith
      nlinarith [hδ_pos]
    have h5 : 0 ≤ p 1 := hp_unit.2.2.1
    linarith [hj2, h3]
  have h_j_lt : q.j < (2 ^ n : ℤ) := by
    by_contra h
    have h' : q.j ≥ (2 ^ n : ℤ) := by linarith
    have h'' : (q.j : ℝ) ≥ (2 ^ n : ℝ) := by exact_mod_cast h'
    have h3 : (q.j : ℝ) * δ ≥ 1 := by
      rw [hδ_eq]
      have h4 : (q.j : ℝ) ≥ (2 ^ n : ℝ) := h''
      calc (q.j : ℝ) * (1 / (2 : ℝ)^n)
        ≥ (2 ^ n : ℝ) * (1 / (2 : ℝ)^n) := by gcongr
      _ = 1 := by
        have h5 : (2 : ℝ)^n > 0 := by positivity
        field_simp [h5.ne'] <;> ring
    have h4 : p 1 < 1 := hp_unit.2.2.2
    linarith [hj1, h3]
  exact ⟨h_i_nonneg, h_i_lt, h_j_nonneg, h_j_lt⟩

/-! ### Tube geometric bounds from snap construction -/

/-- If the original affine line slope m satisfies -1 ≤ m < 1 - δ/2,
    then the snapped dyadic tube has slope index a ∈ [-2^n, 2^n). -/
lemma tubes_strip_from_slope_bound
    {n : ℕ} {ℓ : AffineLine} {p : Plane}
    (hm_lower : -1 ≤ (LegacyRound.affineLineSlopeIntercept ℓ).1)
    (hm_upper : (LegacyRound.affineLineSlopeIntercept ℓ).1 < 1 - dyadicDelta n / 2) :
    -(2 ^ n : ℤ) ≤ (LegacyRound.snapToTubeThroughPoint n ℓ p).a ∧
      (LegacyRound.snapToTubeThroughPoint n ℓ p).a < (2 ^ n : ℤ) := by
  set δ : ℝ := dyadicDelta n with hδ_def
  set m : ℝ := (LegacyRound.affineLineSlopeIntercept ℓ).1 with hm_def
  set a : ℤ := LegacyRound.roundInt (m / δ) with ha_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : δ = 1 / (2 : ℝ)^n := by
    simp only [hδ_def, dyadicDelta] <;> field_simp
  have h1 : m / δ ≥ -(2 ^ n : ℝ) := by
    have h2 : m ≥ -1 := hm_lower
    have h3 : m / δ ≥ (-1 : ℝ) / δ := by gcongr
    rw [hδ_eq] at h3
    have h4 : (-1 : ℝ) / (1 / (2 : ℝ)^n) = -(2 ^ n : ℝ) := by
      field_simp <;> ring
    rw [h4] at h3
    exact h3
  have h5 : m / δ < (2 ^ n : ℝ) - 1 / 2 := by
    have h6 : m < 1 - δ / 2 := hm_upper
    have h7 : m / δ < (1 - δ / 2) / δ := by gcongr
    have h8 : (1 - δ / 2) / δ = 1 / δ - 1 / 2 := by
      field_simp [hδ_pos.ne'] <;> ring
    rw [h8] at h7
    have h9 : 1 / δ = (2 ^ n : ℝ) := by
      rw [hδ_eq] <;> field_simp <;> ring
    rw [h9] at h7
    exact h7
  have h_abs_err : |(a : ℝ) - m / δ| ≤ 1 / 2 := LegacyRound.roundInt_abs_error (m / δ)
  have h_lower : -(2 ^ n : ℤ) ≤ a := by
    by_contra h
    have h' : a ≤ -(2 ^ n : ℤ) - 1 := by linarith
    have h'' : (a : ℝ) ≤ -(2 ^ n : ℝ) - 1 := by exact_mod_cast h'
    have h10 : (a : ℝ) - m / δ ≤ -1 := by linarith
    have h11 : |(a : ℝ) - m / δ| ≥ 1 := by
      have h12 : (a : ℝ) - m / δ ≤ -1 := h10
      have h13 : (a : ℝ) - m / δ < 0 := by linarith
      rw [abs_of_neg h13] <;> linarith
    linarith
  have h_upper : a < (2 ^ n : ℤ) := by
    by_contra h
    have h' : a ≥ (2 ^ n : ℤ) := by linarith
    have h'' : (a : ℝ) ≥ (2 ^ n : ℝ) := by exact_mod_cast h'
    have h10 : (a : ℝ) - m / δ > 1 / 2 := by linarith
    have h11 : (a : ℝ) - m / δ > 0 := by linarith
    have h12 : |(a : ℝ) - m / δ| > 1 / 2 := by
      rw [abs_of_pos h11] <;> linarith
    have h13 : |(a : ℝ) - m / δ| ≤ 1 / 2 := h_abs_err
    linarith
  have ha_eq : (LegacyRound.snapToTubeThroughPoint n ℓ p).a = a := by
    simp [LegacyRound.snapToTubeThroughPoint, ha_def]
    have h_a_le : a ≤ (2 ^ n : ℤ) - 1 := by linarith
    rw [min_eq_left h_a_le]
  rw [ha_eq]
  exact ⟨h_lower, h_upper⟩

/-- If the snapping point p is in [0,1]² and |T.a| ≤ 2^n, then |T.intercept| ≤ 3. -/
lemma tubes_intercept_from_snap
    {n : ℕ} {ℓ : AffineLine} {p : Plane}
    (hp0_0 : 0 ≤ p 0) (hp0_1 : p 0 ≤ 1)
    (hp1_0 : 0 ≤ p 1) (hp1_1 : p 1 ≤ 1)
    (ha_bound : |(LegacyRound.snapToTubeThroughPoint n ℓ p).a| ≤ (2 ^ n : ℤ)) :
    |(LegacyRound.snapToTubeThroughPoint n ℓ p).intercept| ≤ 3 := by
  set δ : ℝ := dyadicDelta n with hδ_def
  set T := LegacyRound.snapToTubeThroughPoint n ℓ p with hT_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_le_one : δ ≤ 1 := by
    have h : δ = 1 / (2 : ℝ)^n := by
      simp only [hδ_def, dyadicDelta] <;> field_simp
    rw [h]
    have h2 : (2 : ℝ)^n ≥ 1 := by
      have h21 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      have h22 : (1 : ℝ)^n ≤ (2 : ℝ)^n := by gcongr
      simpa using h22
    have h3 : (1 : ℝ) / (2 : ℝ)^n ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact h2
    exact h3
  have h_slope_le_one : |T.slope| ≤ 1 := by
    have h1 : T.slope = (T.a : ℝ) * δ := by rfl
    rw [h1]
    have h2 : |(T.a : ℝ)| ≤ (2 ^ n : ℝ) := by exact_mod_cast ha_bound
    have h3 : |(T.a : ℝ) * δ| ≤ (2 ^ n : ℝ) * δ := by
      calc
        |(T.a : ℝ) * δ| = |(T.a : ℝ)| * |δ| := by rw [abs_mul]
        _ = |(T.a : ℝ)| * δ := by rw [abs_of_pos hδ_pos]
        _ ≤ (2 ^ n : ℝ) * δ := by gcongr
    have h4 : (2 ^ n : ℝ) * δ = 1 := by
      have h5 : δ = 1 / (2 : ℝ)^n := by
        simp only [hδ_def, dyadicDelta] <;> field_simp
      rw [h5] <;> field_simp <;> ring
    rw [h4] at h3
    exact h3
  let a : ℤ := T.a
  let b : ℤ := T.b
  have h_err : |(b : ℝ) - ((p 1 - (a : ℝ) * δ * p 0) / δ)| ≤ 1 / 2 :=
    LegacyRound.roundInt_abs_error ((p 1 - (a : ℝ) * δ * p 0) / δ)
  have h_main : |T.intercept - (p 1 - T.slope * p 0)| ≤ δ / 2 := by
    have h3 : |(b : ℝ) * δ - (p 1 - (a : ℝ) * δ * p 0)| =
        δ * |(b : ℝ) - ((p 1 - (a : ℝ) * δ * p 0) / δ)| := by
      have h4 : (b : ℝ) * δ - (p 1 - (a : ℝ) * δ * p 0) =
          δ * ((b : ℝ) - ((p 1 - (a : ℝ) * δ * p 0) / δ)) := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h4, abs_mul, abs_of_pos hδ_pos]
    have h5 : δ * |(b : ℝ) - ((p 1 - (a : ℝ) * δ * p 0) / δ)| ≤ δ / 2 := by
      have h6 : δ * |(b : ℝ) - ((p 1 - (a : ℝ) * δ * p 0) / δ)| ≤ δ * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left h_err hδ_pos.le
      have h7 : δ * (1 / 2 : ℝ) = δ / 2 := by ring
      rw [h7] at h6; exact h6
    have h8 : T.intercept - (p 1 - T.slope * p 0) =
        (b : ℝ) * δ - (p 1 - (a : ℝ) * δ * p 0) := by
      simp [hT_def, DyadicTube.slope, DyadicTube.intercept] <;> ring
    rw [h8]
    rw [h3]; exact h5
  have h_p0_abs : |p 0| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h_p1_abs : |p 1| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h5 : |p 1 - T.slope * p 0| ≤ 2 := by
    have h6 : |p 1 - T.slope * p 0| ≤ |p 1| + |T.slope * p 0| := by exact real_abs_sub (p.ofLp 1) (T.slope * p.ofLp 0)
    have h7 : |T.slope * p 0| = |T.slope| * |p 0| := by rw [abs_mul]
    calc
      |p 1 - T.slope * p 0| ≤ |p 1| + |T.slope * p 0| := h6
      _ = |p 1| + |T.slope| * |p 0| := by rw [h7]
      _ ≤ 1 + 1 * 1 := by gcongr <;> linarith
      _ = 2 := by norm_num
  have h6 : |T.intercept| ≤ |p 1 - T.slope * p 0| + |T.intercept - (p 1 - T.slope * p 0)| := by
    set x := p 1 - T.slope * p 0 with hx
    set y := T.intercept - (p 1 - T.slope * p 0) with hy
    have h9 : T.intercept = x + y := by
      simp [hx, hy] <;> ring
    rw [h9]
    have h10 : -( |x| + |y|) ≤ x + y := by
      have h11 : -|x| ≤ x := neg_abs_le x
      have h12 : -|y| ≤ y := neg_abs_le y
      linarith
    have h13 : x + y ≤ |x| + |y| := by
      have h14 : x ≤ |x| := le_abs_self x
      have h15 : y ≤ |y| := le_abs_self y
      linarith
    exact abs_le.mpr ⟨h10, h13⟩
  calc
    |T.intercept| ≤ |p 1 - T.slope * p 0| + |T.intercept - (p 1 - T.slope * p 0)| := h6
    _ ≤ 2 + δ / 2 := by gcongr
    _ ≤ 2 + 1 / 2 := by gcongr
    _ = 5 / 2 := by norm_num
    _ ≤ 3 := by norm_num

/-! ### Point S-set transfer (continuous P → finite square centers) -/

/-- Coordinate absolute value bounded by Euclidean norm. -/
lemma abs_coord_le_norm {p c : Plane} (i : Fin 2) : |p i - c i| ≤ ‖p - c‖ := by
  have h_sum_nonneg : 0 ≤ ∑ j : Fin 2, ((p - c) j)^2 := by positivity
  have h_norm_sq : ‖p - c‖ ^ 2 = ∑ j : Fin 2, ((p - c) j)^2 := by
    have h_eq1 := EuclideanSpace.norm_eq (p - c)
    rw [h_eq1]
    have h_inner : ∀ (i : Fin 2), ‖(p - c) i‖ ^ 2 = ((p - c) i)^2 := by
      intro i
      have h : ‖(p - c) i‖ = |(p - c) i| := by exact Real.norm_eq_abs ((p - c).ofLp i)
      rw [h, sq_abs]
    have h_sum : (∑ i : Fin 2, ‖(p - c) i‖ ^ 2) = ∑ i : Fin 2, ((p - c) i)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_inner i
    have h_sum_pos : 0 ≤ (∑ i : Fin 2, ‖(p - c) i‖ ^ 2) := by positivity
    have h9 : Real.sqrt (∑ i : Fin 2, ‖(p - c) i‖ ^ 2) ^ 2 = (∑ i : Fin 2, ‖(p - c) i‖ ^ 2) :=
      Real.sq_sqrt h_sum_pos
    rw [h9, h_sum]
  have h2 : ((p - c) i)^2 ≤ ∑ j : Fin 2, ((p - c) j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((p - c) j)) (Finset.mem_univ i)
  have h1 : ((p - c) i)^2 ≤ ‖p - c‖ ^ 2 := by
    rw [h_norm_sq]
    exact h2
  have h3 : |p i - c i| ≤ ‖p - c‖ := by
    have h4 : |p i - c i| ^ 2 ≤ ‖p - c‖ ^ 2 := by
      simpa [sq_abs] using h1
    have h5 : 0 ≤ |p i - c i| := by positivity
    have h6 : 0 ≤ ‖p - c‖ := by positivity
    nlinarith
  exact h3

/-- A Euclidean ball of radius δ intersects at most 9 dyadic squares of side δ. -/
lemma ball_intersects_at_most_9_squares {n : ℕ} (c : Plane) (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta n) :
    ∃ (I : Finset (DyadicSquare n)), I.card ≤ 9 ∧
      ∀ (q : DyadicSquare n), (q.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ → q ∈ I := by
  let i0 : ℤ := ⌊c 0 / δ⌋
  let j0 : ℤ := ⌊c 1 / δ⌋
  let indices_i : Finset ℤ := Finset.Icc (i0 - 1) (i0 + 1)
  let indices_j : Finset ℤ := Finset.Icc (j0 - 1) (j0 + 1)
  have h_card3 : ∀ (z : ℤ), (Finset.Icc (z - 1) (z + 1)).card = 3 := by
    intro z
    simp [Finset.Icc_eq_empty_of_lt]
    <;> omega
  classical
  let I : Finset (DyadicSquare n) :=
    indices_i.biUnion fun i => indices_j.image (fun j => ⟨i, j⟩)
  have h_inj : ∀ (i : ℤ), Function.Injective (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n)) := by
    intro i _ _ h
    simpa [DyadicSquare.mk.injEq] using h
  have hI_card : I.card ≤ 9 := by
    have h1 : I.card ≤ ∑ i ∈ indices_i, (indices_j.image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n))).card :=
      Finset.card_biUnion_le
    have h2 : ∀ i ∈ indices_i, (indices_j.image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n))).card = indices_j.card := by
      intro i _
      rw [Finset.card_image_of_injective _ (h_inj i)]
    have h3 : I.card ≤ ∑ i ∈ indices_i, indices_j.card := by
      calc I.card
        ≤ ∑ i ∈ indices_i, (indices_j.image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n))).card := h1
      _ = ∑ i ∈ indices_i, indices_j.card := by
        apply Finset.sum_congr rfl
        intro i hi
        exact h2 i hi
    have h4 : indices_i.card = 3 := h_card3 i0
    have h5 : ∑ i ∈ indices_i, indices_j.card = indices_i.card * indices_j.card := by
      rw [Finset.sum_const] <;> ring
    have h6 : ∑ i ∈ indices_i, indices_j.card = 3 * 3 := by
      rw [h5, h4, h_card3 j0] <;> ring
    have h7 : I.card ≤ 9 := by
      calc I.card ≤ ∑ i ∈ indices_i, indices_j.card := h3
           _ = 3 * 3 := h6
           _ = 9 := by norm_num
    exact h7
  refine ⟨I, hI_card, ?_⟩
  intro q hq
  have h_nonempty : ((q.toSet : Set Plane) ∩ Metric.closedBall c δ).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hq
  rcases h_nonempty with ⟨p, hpQ, hpc⟩
  have hdist : dist p c ≤ δ := hpc
  have h_norm : ‖p - c‖ ≤ δ := by simpa [dist_eq_norm] using hdist
  have hx : |p 0 - c 0| ≤ δ := (abs_coord_le_norm 0).trans h_norm
  have hy : |p 1 - c 1| ≤ δ := (abs_coord_le_norm 1).trans h_norm
  have hqi1 : (q.i : ℝ) * δ ≤ p 0 := by
    have h : (q.i : ℝ) * dyadicDelta n ≤ p 0 := hpQ.1
    rwa [←hδ_eq] at h
  have hqi2 : p 0 < ((q.i : ℝ) + 1) * δ := by
    have h : p 0 < ((q.i : ℝ) + 1) * dyadicDelta n := hpQ.2.1
    rwa [←hδ_eq] at h
  have hqj1 : (q.j : ℝ) * δ ≤ p 1 := by
    have h : (q.j : ℝ) * dyadicDelta n ≤ p 1 := hpQ.2.2.1
    rwa [←hδ_eq] at h
  have hqj2 : p 1 < ((q.j : ℝ) + 1) * δ := by
    have h : p 1 < ((q.j : ℝ) + 1) * dyadicDelta n := hpQ.2.2.2
    rwa [←hδ_eq] at h
  have h_floor1 : (i0 : ℝ) ≤ c 0 / δ := Int.floor_le (c 0 / δ)
  have h_floor2 : c 0 / δ < (i0 : ℝ) + 1 := Int.lt_floor_add_one (c 0 / δ)
  have h_i_lower : i0 - 1 ≤ q.i := by
    have h1 : p 0 ≥ c 0 - δ := by linarith [abs_le.mp hx]
    have h2 : ((q.i : ℝ) + 1) * δ > c 0 - δ := by linarith
    have h3 : (q.i : ℝ) + 1 > c 0 / δ - 1 := by
      have h4 : ((q.i : ℝ) + 1) * δ / δ > (c 0 - δ) / δ := by gcongr
      have h5 : ((q.i : ℝ) + 1) * δ / δ = (q.i : ℝ) + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      have h6 : (c 0 - δ) / δ = c 0 / δ - 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h5, h6] at h4
      exact h4
    have h7 : (q.i : ℝ) > c 0 / δ - 2 := by linarith
    have h8 : (q.i : ℝ) > (i0 : ℝ) - 2 := by linarith [h_floor1]
    have h9 : q.i ≥ i0 - 1 := by
      by_contra h10
      have h11 : q.i ≤ i0 - 2 := by linarith
      have h12 : (q.i : ℝ) ≤ (i0 : ℝ) - 2 := by exact_mod_cast h11
      linarith
    exact h9
  have h_i_upper : q.i ≤ i0 + 1 := by
    have h1 : p 0 ≤ c 0 + δ := by linarith [abs_le.mp hx]
    have h2 : (q.i : ℝ) * δ ≤ c 0 + δ := by linarith
    have h3 : (q.i : ℝ) ≤ c 0 / δ + 1 := by
      have h4 : (q.i : ℝ) * δ / δ ≤ (c 0 + δ) / δ := by gcongr
      have h5 : (q.i : ℝ) * δ / δ = (q.i : ℝ) := by
        field_simp [hδ_pos.ne'] <;> ring
      have h6 : (c 0 + δ) / δ = c 0 / δ + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h5, h6] at h4
      exact h4
    have h7 : (q.i : ℝ) < (i0 : ℝ) + 2 := by linarith [h_floor2]
    have h8 : q.i ≤ i0 + 1 := by
      by_contra h9
      have h10 : q.i ≥ i0 + 2 := by linarith
      have h11 : (q.i : ℝ) ≥ (i0 : ℝ) + 2 := by exact_mod_cast h10
      linarith
    exact h8
  have h_i_in : q.i ∈ indices_i := by
    simp only [indices_i, Finset.mem_Icc]
    exact ⟨h_i_lower, h_i_upper⟩
  have h_floor3 : (j0 : ℝ) ≤ c 1 / δ := Int.floor_le (c 1 / δ)
  have h_floor4 : c 1 / δ < (j0 : ℝ) + 1 := Int.lt_floor_add_one (c 1 / δ)
  have h_j_lower : j0 - 1 ≤ q.j := by
    have h1 : p 1 ≥ c 1 - δ := by linarith [abs_le.mp hy]
    have h2 : ((q.j : ℝ) + 1) * δ > c 1 - δ := by linarith
    have h3 : (q.j : ℝ) + 1 > c 1 / δ - 1 := by
      have h4 : ((q.j : ℝ) + 1) * δ / δ > (c 1 - δ) / δ := by gcongr
      have h5 : ((q.j : ℝ) + 1) * δ / δ = (q.j : ℝ) + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      have h6 : (c 1 - δ) / δ = c 1 / δ - 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h5, h6] at h4
      exact h4
    have h7 : (q.j : ℝ) > c 1 / δ - 2 := by linarith
    have h8 : (q.j : ℝ) > (j0 : ℝ) - 2 := by linarith [h_floor3]
    have h9 : q.j ≥ j0 - 1 := by
      by_contra h10
      have h11 : q.j ≤ j0 - 2 := by linarith
      have h12 : (q.j : ℝ) ≤ (j0 : ℝ) - 2 := by exact_mod_cast h11
      linarith
    exact h9
  have h_j_upper : q.j ≤ j0 + 1 := by
    have h1 : p 1 ≤ c 1 + δ := by linarith [abs_le.mp hy]
    have h2 : (q.j : ℝ) * δ ≤ c 1 + δ := by linarith
    have h3 : (q.j : ℝ) ≤ c 1 / δ + 1 := by
      have h4 : (q.j : ℝ) * δ / δ ≤ (c 1 + δ) / δ := by gcongr
      have h5 : (q.j : ℝ) * δ / δ = (q.j : ℝ) := by
        field_simp [hδ_pos.ne'] <;> ring
      have h6 : (c 1 + δ) / δ = c 1 / δ + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h5, h6] at h4
      exact h4
    have h7 : (q.j : ℝ) < (j0 : ℝ) + 2 := by linarith [h_floor4]
    have h8 : q.j ≤ j0 + 1 := by
      by_contra h9
      have h10 : q.j ≥ j0 + 2 := by linarith
      have h11 : (q.j : ℝ) ≥ (j0 : ℝ) + 2 := by exact_mod_cast h10
      linarith
    exact h8
  have h_j_in : q.j ∈ indices_j := by
    simp only [indices_j, Finset.mem_Icc]
    exact ⟨h_j_lower, h_j_upper⟩
  have h_goal : q ∈ I := by
    rw [Finset.mem_biUnion]
    exact ⟨q.i, h_i_in, by
      rw [Finset.mem_image]
      exact ⟨q.j, h_j_in, by simp [DyadicSquare.mk.injEq]⟩⟩
  exact h_goal

/-! ### Point S-set transfer integration -/

/-- Transfer S-set from original point set P to square centers Pfin,
    with constant absorption into δ^{-2ε} and ball-growth into Δ^{-9ε/4}.

    Given matching conditions (P and square centers are δ-close), produces:
    - hPfin_sset: IsDeltaSSet δ t (δ^{-2ε}) Pfin
    - hP_ball_growth: |Pfin ∩ B(c,r)| ≤ Δ^{-9ε/4} · r^t · |Pfin| -/
lemma point_sset_transfer_integrated
    {n : ℕ} {Δ δ t ε : ℝ}
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (ht_nonneg : 0 ≤ t) (hε_pos : 0 < ε)
    (hδ_eq : δ = dyadicDelta n)
    (hδ_le_Δ : δ ≤ Δ)
    {P : Set Plane}
    (hP_sset : IsDeltaSSet δ t (Real.rpow δ (-ε)) P)
    {Q : Finset (DyadicSquare n)}
    (h_match_forward : ∀ p ∈ P, ∃ q ∈ Q, dist p (dyadicSquareCenter q) ≤ δ)
    (h_match_backward : ∀ q ∈ Q, ∃ p ∈ P, dist p (dyadicSquareCenter q) ≤ δ)
    (h_absorb1 : (625 : ℝ) * (2 : ℝ)^t ≤ Real.rpow δ (-ε))
    (h_absorb2 : (25 : ℝ) * Real.rpow δ (-2 * ε) ≤ Real.rpow Δ (-9 * ε / 4)) :
    let Pfin : Finset Plane := Q.image localSquareCenter
    IsDeltaSSet δ t (Real.rpow δ (-2 * ε)) (Pfin : Set Plane) ∧
    (∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Pfin.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^t * (Pfin.card : ℝ)) := by
  have h_inj : Set.InjOn dyadicSquareCenter (Q : Set (DyadicSquare n)) := by
    intro q1 _ q2 _ h
    exact dyadicSquareCenter_injective h
  have h_transfer : IsDeltaSSet δ t
      ((Real.rpow δ (-ε)) * 625 * (2 : ℝ)^t)
      (Q.image dyadicSquareCenter : Set Plane) :=
    sset_transfer_to_centers hδ_pos ht_nonneg (Real.rpow_pos_of_pos hδ_pos _)
      hP_sset h_match_forward h_match_backward h_inj
  have h_C_le : (Real.rpow δ (-ε)) * 625 * (2 : ℝ)^t ≤ Real.rpow δ (-2 * ε) := by
    have h1 : Real.rpow δ (-2 * ε) = Real.rpow δ (-ε) * Real.rpow δ (-ε) := by
      have h_exp : -2 * ε = -ε + -ε := by ring
      rw [h_exp]
      exact Real.rpow_add (by linarith) (-ε) (-ε)
    rw [h1]
    have h2 : (625 : ℝ) * (2 : ℝ)^t ≤ Real.rpow δ (-ε) := h_absorb1
    have h3 : 0 < Real.rpow δ (-ε) := Real.rpow_pos_of_pos hδ_pos _
    nlinarith
  have h_sset_2ε : IsDeltaSSet δ t (Real.rpow δ (-2 * ε))
      (Q.image dyadicSquareCenter : Set Plane) := by
    have hC'_pos : 0 < Real.rpow δ (-2 * ε) := Real.rpow_pos_of_pos hδ_pos _
    refine' ⟨h_transfer.1, h_transfer.2.1, hC'_pos, h_transfer.2.2.2.1, _⟩
    intro x r hr
    have h4 := h_transfer.2.2.2.2 x r hr
    have h5 : ENNReal.ofReal ((Real.rpow δ (-ε)) * 625 * (2 : ℝ)^t) ≤
        ENNReal.ofReal (Real.rpow δ (-2 * ε)) := ENNReal.ofReal_le_ofReal h_C_le
    calc
      (Metric.externalCoveringNumber δ.toNNReal (_ ∩ Metric.closedBall x r) : ENNReal)
        ≤ ENNReal.ofReal ((Real.rpow δ (-ε)) * 625 * (2 : ℝ)^t) * (ENNReal.ofReal r) ^ t *
            (Metric.externalCoveringNumber δ.toNNReal _ : ENNReal) := h4
      _ ≤ ENNReal.ofReal (Real.rpow δ (-2 * ε)) * (ENNReal.ofReal r) ^ t *
            (Metric.externalCoveringNumber δ.toNNReal _ : ENNReal) := by gcongr
  have h_centers_eq : (Q.image dyadicSquareCenter : Set Plane) =
      (Q.image localSquareCenter : Set Plane) := by
    congr with q
    <;> rfl
  rw [h_centers_eq] at h_sset_2ε
  let Pfin : Finset Plane := Q.image localSquareCenter
  have hPfin_sep : Set.Pairwise (Pfin : Set Plane) (fun p q => δ ≤ dist p q) := by
    have h_sep_delta_n : Set.Pairwise (Pfin : Set Plane) (fun p q => dyadicDelta n ≤ dist p q) :=
      dyadicSquareCenters_separated Q
    rw [show (fun p q : Plane => dyadicDelta n ≤ dist p q) =
        (fun p q : Plane => δ ≤ dist p q) from by
      funext p q
      rw [hδ_eq]] at h_sep_delta_n
    exact h_sep_delta_n
  have h_ball_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Pfin.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        (25 : ℝ) * Real.rpow δ (-2 * ε) * r^t * (Pfin.card : ℝ) := by
    intro c r hr
    have hδ_le_r : δ ≤ r := le_trans hδ_le_Δ hr
    exact @FrontEndExtraction.sset_ball_growth δ t (Real.rpow δ (-2 * ε)) Pfin
      hδ_pos ht_nonneg (Real.rpow_pos_of_pos hδ_pos _)
      hPfin_sep h_sset_2ε c r hδ_le_r
  have h_final : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Pfin.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^t * (Pfin.card : ℝ) := by
    intro c r hr
    have h4 : ((Pfin.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        (25 : ℝ) * Real.rpow δ (-2 * ε) * r^t * (Pfin.card : ℝ) :=
      h_ball_growth c r hr
    have h5 : (25 : ℝ) * Real.rpow δ (-2 * ε) ≤ Real.rpow Δ (-9 * ε / 4) := h_absorb2
    have h6 : 0 ≤ r^t := Real.rpow_nonneg (by linarith) t
    have h7 : 0 ≤ (Pfin.card : ℝ) := by positivity
    calc ((Pfin.filter (fun y => dist c y ≤ r)).card : ℝ)
      ≤ (25 : ℝ) * Real.rpow δ (-2 * ε) * r^t * (Pfin.card : ℝ) := h4
    _ ≤ Real.rpow Δ (-9 * ε / 4) * r^t * (Pfin.card : ℝ) := by
      gcongr
      <;> linarith
  exact ⟨h_sset_2ε, h_final⟩

/-- Explicit cardinality bound for dyadic tubes satisfying strip and intercept bounds. -/
lemma bounded_tubes_card_from_geometric
    {n : ℕ} {Tubes : Finset (DyadicTube n)}
    (hn : n ≥ 1)
    (h_strip : ∀ T ∈ Tubes, -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_intercept : ∀ T ∈ Tubes, |T.intercept| ≤ 3) :
    Tubes.card ≤ 12 * 16 ^ n := by
  set δ : ℝ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : δ = 1 / (2 : ℝ)^n := by
    simp only [hδ_def, dyadicDelta] <;> field_simp
  let A : Finset ℤ := Finset.Ico (-(2 ^ n : ℤ)) (2 ^ n : ℤ)
  let B : Finset ℤ := Finset.Ico (-(4 * (2 ^ n : ℤ))) (4 * (2 ^ n : ℤ))
  let f : DyadicTube n → ℤ × ℤ := fun T => (T.a, T.b)
  have h_inj : Function.Injective f := by
    intro T1 T2 h
    have h1 : T1.a = T2.a := by simp [f, Prod.ext_iff] at h <;> tauto
    have h2 : T1.b = T2.b := by simp [f, Prod.ext_iff] at h <;> tauto
    cases T1 <;> cases T2 <;> simp_all <;> tauto
  have h_a_sub : ∀ T ∈ Tubes, T.a ∈ A := by
    intro T hT
    have h := h_strip T hT
    simp only [A, Finset.mem_Ico] <;> omega
  have h_b_sub : ∀ T ∈ Tubes, T.b ∈ B := by
    intro T hT
    have h : |T.intercept| ≤ 3 := h_intercept T hT
    have h2 : |(T.b : ℝ) * δ| ≤ 3 := by simpa [DyadicTube.intercept] using h
    have h3 : |(T.b : ℝ)| * δ ≤ 3 := by
      have h4 : |(T.b : ℝ) * δ| = |(T.b : ℝ)| * δ := by
        rw [abs_mul, abs_of_pos hδ_pos]
      rw [h4] at h2
      exact h2
    have h5 : |(T.b : ℝ)| ≤ 3 / δ := by
      calc
        |(T.b : ℝ)| = (|(T.b : ℝ)| * δ) / δ := by
          field_simp [hδ_pos.ne'] <;> ring
        _ ≤ 3 / δ := by gcongr
    have h6 : (T.b : ℝ) ≤ 3 / δ := by linarith [abs_le.mp h5]
    have h7 : -(3 / δ) ≤ (T.b : ℝ) := by linarith [abs_le.mp h5]
    have h8 : 3 / δ = 3 * (2 ^ n : ℝ) := by
      rw [hδ_eq] <;> field_simp <;> ring
    rw [h8] at h6 h7
    have h9 : -(4 * (2 ^ n : ℤ)) ≤ T.b := by
      have h10 : -(3 * (2 ^ n : ℝ)) ≤ (T.b : ℝ) := h7
      have h11 : -(4 * (2 ^ n : ℤ)) ≤ -(3 * (2 ^ n : ℝ)) := by
        simp <;> norm_cast <;> omega
      exact_mod_cast le_trans h11 h10
    have h12 : T.b < 4 * (2 ^ n : ℤ) := by
      have h13 : (T.b : ℝ) ≤ 3 * (2 ^ n : ℝ) := h6
      have h14 : 3 * (2 ^ n : ℝ) < (4 * (2 ^ n : ℤ) : ℝ) := by
        simp <;> norm_cast <;> omega
      exact_mod_cast lt_of_le_of_lt h13 h14
    simp only [B, Finset.mem_Ico]
    exact ⟨h9, h12⟩
  have h_img_sub : Tubes.image f ⊆ A ×ˢ B := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨T, hT, rfl⟩
    exact Finset.mem_product.mpr ⟨h_a_sub T hT, h_b_sub T hT⟩
  have h_card_eq : Tubes.card = (Tubes.image f).card := by
    rw [Finset.card_image_of_injective _ h_inj]
  have hA_card : A.card = 2 ^ (n + 1) := by
    rw [Int.card_Ico]
    have h : (2 ^ n : ℤ) - (-(2 ^ n : ℤ)) = 2 * (2 ^ n : ℤ) := by ring
    rw [h]
    have hpos : 0 ≤ 2 * (2 ^ n : ℤ) := by positivity
    have h2 : (2 * (2 ^ n : ℤ)).toNat = 2 * 2 ^ n := by
      have h21 : ((2 * (2 ^ n : ℤ)).toNat : ℤ) = (2 * 2 ^ n : ℤ) := by
        rw [Int.toNat_of_nonneg hpos] <;> norm_cast
      exact_mod_cast h21
    rw [h2]
    have h3 : 2 * 2 ^ n = 2 ^ (n + 1) := by
      rw [pow_succ] <;> ring
    rw [h3]
  have hB_card : B.card = 2 ^ (n + 3) := by
    rw [Int.card_Ico]
    have h : (4 * (2 ^ n : ℤ)) - (-(4 * (2 ^ n : ℤ))) = 8 * (2 ^ n : ℤ) := by
      ring
    rw [h]
    have hpos : 0 ≤ 8 * (2 ^ n : ℤ) := by positivity
    have h2 : (8 * (2 ^ n : ℤ)).toNat = 8 * 2 ^ n := by
      have h21 : ((8 * (2 ^ n : ℤ)).toNat : ℤ) = (8 * 2 ^ n : ℤ) := by
        rw [Int.toNat_of_nonneg hpos] <;> norm_cast
      exact_mod_cast h21
    rw [h2]
    have h3 : 8 * 2 ^ n = 2 ^ (n + 3) := by
      rw [pow_add] <;> norm_num <;> ring
    rw [h3]
  have h2n : 2 ^ (2 * n) = 4 ^ n := by
    have h : 2 ^ (2 * n) = (2 ^ 2) ^ n := by
      rw [← Nat.pow_mul] <;> ring
    rw [h] <;> norm_num
  have h_main : (A ×ˢ B).card ≤ 12 * 16 ^ n := by
    calc
      (A ×ˢ B).card = A.card * B.card := by simp [Finset.card_product]
      _ = (2 ^ (n + 1)) * (2 ^ (n + 3)) := by rw [hA_card, hB_card]
      _ = 2 ^ (2 * n + 4) := by rw [← pow_add] <;> ring
      _ = 16 * 2 ^ (2 * n) := by
        rw [show 2 * n + 4 = 4 + 2 * n by ring, pow_add] <;> ring
      _ = 16 * 4 ^ n := by rw [h2n]
      _ ≤ 12 * 16 ^ n := by
        have h16 : 4 ^ n ≥ 4 := by
          have h17 : 4 ^ n ≥ 4 ^ 1 := by gcongr <;> norm_num
          simpa using h17
        have h21 : 16 ≤ 12 * 4 ^ n := by omega
        have h22 : 16 * 4 ^ n ≤ (12 * 4 ^ n) * 4 ^ n :=
          mul_le_mul_of_nonneg_right h21 (by positivity)
        have h23 : (12 * 4 ^ n) * 4 ^ n = 12 * 16 ^ n := by
          have h24 : 4 ^ n * 4 ^ n = 16 ^ n := by
            have h25 : 4 ^ n * 4 ^ n = 4 ^ (n + n) := by
              rw [← Nat.pow_add] <;> ring
            rw [h25]
            have h26 : n + n = 2 * n := by ring
            rw [h26]
            have h27 : 4 ^ (2 * n) = 16 ^ n := by
              have h28 : 4 ^ (2 * n) = (4 ^ 2) ^ n := by
                rw [← Nat.pow_mul] <;> ring
              rw [h28] <;> norm_num
            exact h27
          have h29 : (12 * 4 ^ n) * 4 ^ n = 12 * (4 ^ n * 4 ^ n) := by ring
          rw [h29, h24] <;> ring
        rw [h23] at h22
        exact h22
  calc
    Tubes.card = (Tubes.image f).card := h_card_eq
    _ ≤ (A ×ˢ B).card := Finset.card_le_card h_img_sub
    _ ≤ 12 * 16 ^ n := h_main

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
