module

/-
  Incidence Helpers for Coarse Regular Incidence Wiring

  Provides helper lemmas to construct the inputs to
  `coarse_config_regular_incidence` from a `CTNiceConfiguration`:

  1. Wide carrier strip for `DyadicTube m` and incidence proof
  2. `IsSquareRootRegular` from `IsRegularBetweenScales` with Δ=1
  3. Translation invariance of `IsSquareRootRegular`
  4. Unit-ball containment after translating [0,1)² by (-1/2,-1/2)

  Whiteprint: combining_theorem_genuine / incidence_helpers
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers1a
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence

/-! ========================================================================
   Wide carrier strip for DyadicTube
   ======================================================================== -/

/-- Wide carrier strip of width 3δ around a dyadic tube's representative line.

    For any point p in a δ-square Q whose δ-tube T intersects Q, the vertical
    distance from p to T's line is ≤ 3δ (using |slope| ≤ 1), so p ∈ wideCarrier T.
    Hence dist(p, wideCarrier T) = 0 ≤ δ. -/
def wideCarrier {m : ℕ} (T : DyadicTube m) : Set EuclideanPlane :=
  let δ := dyadicDelta m
  {p | |p 1 - T.slope * p 0 - T.intercept| ≤ 3 * δ}

/-- If tube T intersects square Q and p ∈ Q, and |T.slope| ≤ 1,
    then p is in the wide carrier of T. -/
lemma wideCarrier_contains_square_point
    {m : ℕ} {T : DyadicTube m} {Q : DyadicSquare m} {p : EuclideanPlane}
    (h_intersect : (T.toSet ∩ Q.toSet).Nonempty)
    (hpQ : p ∈ Q.toSet)
    (h_slope : |T.slope| ≤ 1) :
    p ∈ wideCarrier T := by
  let δ := dyadicDelta m
  have hδ_pos : 0 < δ := dyadicDelta_pos m
  rcases h_intersect with ⟨r, hrT, hrQ⟩
  have h_r_in_T : |r 1 - T.slope * r 0 - T.intercept| ≤ δ := hrT
  have h_pQ1 : |p 0 - r 0| ≤ δ := (DyadicSquare.side_length hpQ hrQ).1
  have h_pQ2 : |p 1 - r 1| ≤ δ := (DyadicSquare.side_length hpQ hrQ).2
  have h_main : |p 1 - T.slope * p 0 - T.intercept| ≤ 3 * δ := by
    have h1 : p 1 - T.slope * p 0 - T.intercept =
        (p 1 - r 1) - T.slope * (p 0 - r 0) + (r 1 - T.slope * r 0 - T.intercept) := by ring
    rw [h1]
    have h_abs1 : |(p 1 - r 1) - T.slope * (p 0 - r 0) + (r 1 - T.slope * r 0 - T.intercept)| ≤
        |(p 1 - r 1) - T.slope * (p 0 - r 0)| + |r 1 - T.slope * r 0 - T.intercept| := by
      exact real_abs_add (p.ofLp 1 - r.ofLp 1 - T.slope * (p.ofLp 0 - r.ofLp 0))
        (r.ofLp 1 - T.slope * r.ofLp 0 - T.intercept)
    have h_abs2 : |(p 1 - r 1) - T.slope * (p 0 - r 0)| ≤ |p 1 - r 1| + |T.slope| * |p 0 - r 0| := by
      calc |(p 1 - r 1) - T.slope * (p 0 - r 0)|
        ≤ |p 1 - r 1| + |T.slope * (p 0 - r 0)| := by exact real_abs_sub (p.ofLp 1 - r.ofLp 1) (T.slope * (p.ofLp 0 - r.ofLp 0))
      _ = |p 1 - r 1| + |T.slope| * |p 0 - r 0| := by rw [abs_mul]
    calc |(p 1 - r 1) - T.slope * (p 0 - r 0) + (r 1 - T.slope * r 0 - T.intercept)|
      ≤ |(p 1 - r 1) - T.slope * (p 0 - r 0)| + |r 1 - T.slope * r 0 - T.intercept| := h_abs1
    _ ≤ (|p 1 - r 1| + |T.slope| * |p 0 - r 0|) + δ := by gcongr <;> linarith
    _ ≤ δ + 1 * δ + δ := by gcongr <;> linarith
    _ = 3 * δ := by ring
  exact h_main

/-- If p ∈ wideCarrier T, then p ∈ Metric.cthickening δ (wideCarrier T). -/
lemma wideCarrier_mem_cthickening
    {m : ℕ} {T : DyadicTube m} {p : EuclideanPlane}
    (hp : p ∈ wideCarrier T) :
    p ∈ Metric.cthickening (dyadicDelta m) (wideCarrier T) := by
  have hδ_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have h_inf_le : Metric.infEDist p (wideCarrier T) ≤ edist p p :=
    Metric.infEDist_le_edist_of_mem hp
  have h_edist_self : edist p p = 0 := by simp
  have h : Metric.infEDist p (wideCarrier T) ≤ ENNReal.ofReal (dyadicDelta m) := by
    rw [h_edist_self] at h_inf_le
    exact le_trans h_inf_le (by simp)
  exact Metric.mem_cthickening_iff.mpr h

/-! ========================================================================
   IsSquareRootRegular from IsRegularBetweenScales (Δ=1)
   ======================================================================== -/

/-- Derive `IsSquareRootRegular δ t C K P` from `IsRegularBetweenScales P δ 1 t C K`
    when P is contained in the unit dyadic square [0,1)².

    When Δ=1, the only relevant dyadic square is (0,0), and the homothety
    is the identity, so the between-scales S-set and covering bounds directly
    give the square-root regularity of P. -/
lemma square_root_regular_from_unit_between_scales
    {δ t C K : ℝ} {P : Set EuclideanPlane}
    (hreg : IsRegularBetweenScales P δ 1 t C K)
    (hP_sub_unit : P ⊆ dyadicSquare 1 0 0)
    (hP_nonempty : P.Nonempty) :
    IsSquareRootRegular δ t C K P := by
  have hδ_pos : 0 < δ := hreg.1.1
  have h1_pos : (0 : ℝ) < 1 := by norm_num
  have hδ_le_one : δ ≤ 1 := hreg.1.2.2.1
  have hs_nonneg : 0 ≤ t := hreg.1.2.2.2.1
  have hC_pos : 0 < C := hreg.1.2.2.2.2.1
  have hK_pos : 0 < K := hreg.2.1

  -- P ∩ dyadicSquare 1 0 0 = P
  have hP_intersect : P ∩ dyadicSquare 1 0 0 = P := by
    have h : P ∩ dyadicSquare 1 0 0 = dyadicSquare 1 0 0 ∩ P := by rw [Set.inter_comm]
    rw [h, Set.inter_eq_right.mpr hP_sub_unit]

  -- P is nonempty (given)
  -- The unit square is nonempty intersection
  have h_nonempty_intersect : (P ∩ dyadicSquare 1 0 0).Nonempty := by
    rw [hP_intersect]
    exact hP_nonempty

  -- Part 1: IsDeltaSSet δ t C P
  have h_sset_square : IsDeltaSSet (δ / 1) t C
      (homothetyS 1 0 0 '' (P ∩ dyadicSquare 1 0 0)) :=
    hreg.1.2.2.2.2.2 0 0 h_nonempty_intersect
  have h_homothety_id : homothetyS 1 0 0 = id := by
    funext x
    simp [homothetyS]
    <;> ext i <;> fin_cases i <;> simp <;> ring
  have h_div_one : δ / 1 = δ := by ring
  rw [h_homothety_id, hP_intersect] at h_sset_square
  rw [h_div_one] at h_sset_square
  have h_sset_P : IsDeltaSSet δ t C P := by simpa using h_sset_square

  -- Part 2: Ncover (sqrt δ) P ≤ K * δ^{-t/2}
  have h_cov_square : (Metric.externalCoveringNumber (Real.sqrt (δ / 1)).toNNReal
        (homothetyS 1 0 0 '' (P ∩ dyadicSquare 1 0 0)) : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow (δ / 1) (-t / 2)) :=
    hreg.2.2 0 0 h_nonempty_intersect
  rw [h_homothety_id, hP_intersect] at h_cov_square
  have h_id_image : (id '' P) = P := by simp
  rw [h_id_image] at h_cov_square
  have h_div_one2 : Real.sqrt (δ / 1) = Real.sqrt δ := by
    have h : δ / 1 = δ := by ring
    rw [h]
  rw [h_div_one2] at h_cov_square
  have h_rpow : Real.rpow (δ / 1) (-t / 2) = Real.rpow δ (-t / 2) := by
    have h : δ / 1 = δ := by ring
    rw [h]
  rw [h_rpow] at h_cov_square
  exact ⟨h_sset_P, h_cov_square⟩

/-! ========================================================================
   Translation invariance of IsSquareRootRegular
   ======================================================================== -/

/-- Translation is an isometry equivalence of EuclideanPlane. -/
def translationEquiv (v : EuclideanPlane) : EuclideanPlane ≃ᵢ EuclideanPlane :=
  { toFun := fun p => p + v
    invFun := fun p => p - v
    left_inv := by intro p; simp
    right_inv := by intro p; simp
    isometry_toFun := by
      intro x y
      simp [dist_eq_norm] <;> rfl }

/-- `IsSquareRootRegular` is preserved under translation. -/
lemma isSquareRootRegular_translate
    {δ t C K : ℝ} {P : Set EuclideanPlane} {v : EuclideanPlane}
    (h : IsSquareRootRegular δ t C K P) :
    IsSquareRootRegular δ t C K ((translationEquiv v) '' P) := by
  let e := translationEquiv v
  have h1 : IsDeltaSSet δ t C (e '' P) :=
    isDeltaSSet_image_isometryEquiv e h.1
  have h2 : Metric.externalCoveringNumber (Real.sqrt δ).toNNReal (e '' P) =
      Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P :=
    DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_isometryEquiv e
  exact ⟨h1, by simpa [Ncover] using h2 ▸ h.2⟩

/-! ========================================================================
   Unit-ball containment after translation
   ======================================================================== -/

/-- The translation vector (-1/2, -1/2). -/
def centerTranslation : EuclideanPlane :=
  WithLp.toLp (2 : ENNReal) fun _ : Fin 2 => -1 / 2

/-- Translating [0,1)² by (-1/2,-1/2) gives [-1/2,1/2)², which is contained
    in the closed unit ball. -/
lemma unit_square_translate_sub_ball
    {P : Set EuclideanPlane}
    (hP_sub : P ⊆ dyadicSquare 1 0 0) :
    (translationEquiv centerTranslation '' P) ⊆ Metric.closedBall 0 1 := by
  intro p hp
  rcases hp with ⟨x, hx, rfl⟩
  have h_x_in : x ∈ dyadicSquare 1 0 0 := hP_sub hx
  simp only [dyadicSquare, Set.mem_setOf_eq] at h_x_in
  let y := x + centerTranslation
  have hy0 : -1 / 2 ≤ y 0 := by
    simp [y, centerTranslation] at h_x_in ⊢ <;> linarith
  have hy0' : y 0 < 1 / 2 := by
    simp [y, centerTranslation] at h_x_in ⊢ <;> linarith
  have hy1 : -1 / 2 ≤ y 1 := by
    simp [y, centerTranslation] at h_x_in ⊢ <;> linarith
  have hy1' : y 1 < 1 / 2 := by
    simp [y, centerTranslation] at h_x_in ⊢ <;> linarith
  have h_abs0 : |y 0| ≤ 1 / 2 := by
    have h : -(1 / 2 : ℝ) ≤ y 0 ∧ y 0 ≤ 1 / 2 := by
      constructor <;> linarith
    exact abs_le.mpr h
  have h_abs1 : |y 1| ≤ 1 / 2 := by
    have h : -(1 / 2 : ℝ) ≤ y 1 ∧ y 1 ≤ 1 / 2 := by
      constructor <;> linarith
    exact abs_le.mpr h
  have h_norm : ‖y‖ ≤ 1 := by
    have h_norm_eq : ‖y‖ = Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
    rw [h_norm_eq]
    have h_nonneg : 0 ≤ (y 0) ^ 2 + (y 1) ^ 2 := by positivity
    have h_sq_le : (y 0) ^ 2 + (y 1) ^ 2 ≤ 1 := by
      nlinarith [sq_abs (y 0), sq_abs (y 1)]
    exact Real.sqrt_le_one.mpr h_sq_le
  have h_goal : dist y 0 ≤ 1 := by
    simpa [dist_eq_norm] using h_norm
  exact h_goal

/-! ========================================================================
   Translated carrier (critical: translate BOTH points and carriers)
   ======================================================================== -/

/-- Translated wide carrier: apply the same translation to the carrier strip
    that was applied to the point set. This preserves all incidence relations. -/
def translatedWideCarrier {m : ℕ} (v : EuclideanPlane) (T : DyadicTube m) :
    Set EuclideanPlane :=
  (translationEquiv v) '' (wideCarrier T)

/-- If `p ∈ wideCarrier T`, then `p + v ∈ translatedWideCarrier v T`. -/
lemma translatedWideCarrier_mem
    {m : ℕ} {v : EuclideanPlane} {T : DyadicTube m} {p : EuclideanPlane}
    (hp : p ∈ wideCarrier T) :
    p + v ∈ translatedWideCarrier v T := by
  exact ⟨p, hp, by simp [translationEquiv]⟩

/-- If the original point `p` is in the wide carrier of T, then the translated
    point `p + v` is in the δ-thickening of the translated carrier.

    This is the key incidence transfer lemma: translating both the point and
    the carrier by the same isometry preserves the distance-zero relation. -/
lemma translatedWideCarrier_incidence
    {m : ℕ} {v : EuclideanPlane} {T : DyadicTube m} {p : EuclideanPlane}
    (hp : p ∈ wideCarrier T) :
    p + v ∈ Metric.cthickening (dyadicDelta m) (translatedWideCarrier v T) := by
  have hδ_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  let e := translationEquiv v
  have h1 : p + v ∈ translatedWideCarrier v T := translatedWideCarrier_mem hp
  have h_inf_le : Metric.infEDist (p + v) (translatedWideCarrier v T) ≤ edist (p + v) (p + v) :=
    Metric.infEDist_le_edist_of_mem h1
  have h_edist_self : edist (p + v) (p + v) = 0 := by simp
  have h : Metric.infEDist (p + v) (translatedWideCarrier v T) ≤
      ENNReal.ofReal (dyadicDelta m) := by
    rw [h_edist_self] at h_inf_le
    exact le_trans h_inf_le (by simp)
  exact Metric.mem_cthickening_iff.mpr h

/-- Full incidence chain: from square-level intersection to translated point-level
    thickening. Combines `wideCarrier_contains_square_point` with
    `translatedWideCarrier_incidence`. -/
lemma translated_incidence_from_square
    {m : ℕ} {v : EuclideanPlane} {T : DyadicTube m} {Q : DyadicSquare m}
    {p : EuclideanPlane}
    (h_intersect : (T.toSet ∩ Q.toSet).Nonempty)
    (hpQ : p ∈ Q.toSet)
    (h_slope : |T.slope| ≤ 1) :
    p + v ∈ Metric.cthickening (dyadicDelta m) (translatedWideCarrier v T) :=
  translatedWideCarrier_incidence
    (wideCarrier_contains_square_point h_intersect hpQ h_slope)

/-! ========================================================================
   Tube S-set from coarse config
   ======================================================================== -/

/-- The tube family for a coarse square Q is an S-set at scale δ_m with
    constant CΔ, directly from coarseConfig.h_delta_s_set. -/
lemma coarse_tube_sset
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.P₀) :
    IsDeltaSSet (dyadicDelta m) s CΔ
      (coarseConfig.tubeFamily Q hQ : Set (DyadicTube m)) :=
  coarseConfig.h_delta_s_set Q hQ

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
