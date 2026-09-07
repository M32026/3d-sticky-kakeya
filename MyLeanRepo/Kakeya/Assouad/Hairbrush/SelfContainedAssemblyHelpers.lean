import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves

/-!
# Helper lemmas for the self-contained hairbrush assembly

Pure utility lemmas used by the final assembly proof.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

/--
If `layer` is obtained by intersecting every carrier with a common `support`,
then at every point in `layer.union` the through-family is identical to that of `Y`,
so `IsTwoBroadAtScale` is inherited.
-/
lemma two_broad_inheritance
    {δ : ℝ} {F : Kakeya.TubeFamily δ}
    {Y layer : Kakeya.Shading F}
    {support : Set Point3}
    {theta eta : ℝ}
    (hY : IsTwoBroadAtScale Y theta eta)
    (h_layer : ∀ T ∈ F, layer.carrier T = Y.carrier T ∩ support) :
    IsTwoBroadAtScale layer theta eta := by
  classical
  intro x hx
  have hx_support : x ∈ support := by
    rcases hx with ⟨T, hT, hxT⟩
    rw [h_layer T hT] at hxT
    exact hxT.2
  have hx_Y : x ∈ Y.union := by
    rcases hx with ⟨T, hT, hxT⟩
    rw [h_layer T hT] at hxT
    exact ⟨T, hT, hxT.1⟩
  rcases hY x hx_Y with ⟨thetaLocal, hδ, h1, h2, h3⟩
  refine' ⟨thetaLocal, hδ, h1, h2, _⟩
  intro w hw r hr1 hr2
  have h_eq1 : ∀ (T : Kakeya.DeltaTube δ), T ∈ F →
      (x ∈ layer.carrier T ↔ x ∈ Y.carrier T) := by
    intro T hT
    constructor
    · intro h4
      rw [h_layer T hT] at h4
      exact h4.1
    · intro h4
      rw [h_layer T hT]
      exact ⟨h4, hx_support⟩
  have h_through : (F.filter fun T => x ∈ layer.carrier T) =
      (F.filter fun T => x ∈ Y.carrier T) := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT, h4⟩
      exact ⟨hT, (h_eq1 T hT).mp h4⟩
    · rintro ⟨hT, h4⟩
      exact ⟨hT, (h_eq1 T hT).mpr h4⟩
  have h_main := h3 w hw r hr1 hr2
  dsimp only at h_main ⊢
  have h_near : ((F.filter fun T => x ∈ layer.carrier T).filter fun T =>
        hairbrushAcuteDirectionAngle T.direction w ≤ r) =
      ((F.filter fun T => x ∈ Y.carrier T).filter fun T =>
        hairbrushAcuteDirectionAngle T.direction w ≤ r) := by
    rw [h_through]
  rw [h_near, h_through]
  exact h_main

/-- Recover a finite `ENNReal` from `toReal`. -/
lemma ennreal_ofReal_toReal {x : ENNReal} (h : x ≠ ⊤) :
    ENNReal.ofReal x.toReal = x :=
  ENNReal.ofReal_toReal_eq_iff.mpr h

/--
The product `ENNReal.ofReal (Real.rpow r zeta) * x` has positive `toReal`
when `r > 0`, `zeta > 0`, and `x` is nonzero and finite.
-/
lemma refined_density_pos
    {x : ENNReal} (h0 : x ≠ 0) (htop : x ≠ ⊤)
    {r zeta : ℝ} (hr : 0 < r) (hzeta : 0 < zeta) :
    0 < (ENNReal.ofReal (Real.rpow r zeta) * x).toReal := by
  set a := ENNReal.ofReal (Real.rpow r zeta) with ha_def
  set y := a * x with hy_def
  have h_rpow_pos : 0 < Real.rpow r zeta := Real.rpow_pos_of_pos hr zeta
  have ha_pos : a ≠ 0 := by
    rw [ha_def]
    have h : ¬(Real.rpow r zeta ≤ 0) := by linarith
    simpa [ENNReal.ofReal_eq_zero] using h
  have ha_top : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hy_zero : y ≠ 0 := by
    rw [hy_def]
    exact (mul_ne_zero_iff_right h0).mpr ha_pos
  have hy_top : y ≠ ⊤ := by
    rw [hy_def]
    exact ENNReal.mul_ne_top ha_top htop
  have h : 0 < y.toReal := ENNReal.toReal_pos hy_zero hy_top
  exact h

/--
Reduce the explicit normalized cardinality bound
`10^8 * δ^(-eta) * (theta/δ)^2` to the polynomial form `δ^(-(eta+3))`.
-/
lemma cardinality_bound_reduction
    {δ theta eta : ℝ}
    (hδ : 0 < δ)
    (hδ_small : δ ≤ 1 / 100000000)
    (htheta0 : 0 ≤ theta)
    (htheta1 : theta ≤ 1) :
    ENNReal.ofReal 100000000 * Kakeya.realRpowENN δ (-eta) *
        ENNReal.ofReal ((theta / δ) ^ 2) ≤
      Kakeya.realRpowENN δ (-(eta + 3)) := by
  have hδ' : 0 ≤ δ := by linarith
  have h_bound : (100000000 : ℝ) * (theta / δ) ^ 2 ≤ 1 / δ ^ 3 := by
    have h_theta2 : (theta / δ) ^ 2 ≤ 1 / δ ^ 2 := by
      have h1 : 0 ≤ theta / δ := by positivity
      have h2 : theta / δ ≤ 1 / δ := by
        gcongr
        <;> linarith
      have h4 : (theta / δ) ^ 2 ≤ (1 / δ) ^ 2 := by gcongr
      have h5 : (1 / δ) ^ 2 = 1 / δ ^ 2 := by
        field_simp [hδ.ne'] <;> ring
      rw [h5] at h4
      exact h4
    have h_key : (100000000 : ℝ) * δ ≤ 1 := by nlinarith
    have h_108_d2 : (100000000 : ℝ) / δ ^ 2 ≤ 1 / δ ^ 3 := by
      have h6 : (100000000 : ℝ) / δ ^ 2 = ((100000000 : ℝ) * δ) / δ ^ 3 := by
        field_simp [hδ.ne'] <;> ring
      rw [h6]
      gcongr <;> linarith
    calc
      (100000000 : ℝ) * (theta / δ) ^ 2
        ≤ (100000000 : ℝ) * (1 / δ ^ 2) := by gcongr
      _ = (100000000 : ℝ) / δ ^ 2 := by ring
      _ ≤ 1 / δ ^ 3 := h_108_d2
  have h_rpow3 : Real.rpow δ (3 : ℝ) = δ ^ 3 := by simp
  have h_mul : Real.rpow δ (-3 : ℝ) * Real.rpow δ (3 : ℝ) = 1 := by
    have h_add : Real.rpow δ ((-3 : ℝ) + (3 : ℝ)) =
        Real.rpow δ (-3 : ℝ) * Real.rpow δ (3 : ℝ) :=
      Real.rpow_add hδ (-3) 3
    have h_zero : (-3 : ℝ) + (3 : ℝ) = 0 := by norm_num
    rw [h_zero] at h_add
    have h_rpow0 : Real.rpow δ 0 = 1 := Real.rpow_zero δ
    rw [h_rpow0] at h_add
    exact h_add.symm
  have h_pos3 : 0 < Real.rpow δ (3 : ℝ) := Real.rpow_pos_of_pos hδ 3
  have h_rpow_neg3 : Real.rpow δ (-3 : ℝ) = 1 / δ ^ 3 := by
    have h : Real.rpow δ (-3 : ℝ) * Real.rpow δ (3 : ℝ) = 1 := h_mul
    have h' : Real.rpow δ (-3 : ℝ) = 1 / Real.rpow δ (3 : ℝ) := by
      rw [← h]
      <;> field_simp [h_pos3.ne'] <;> ring
    rw [h', h_rpow3]
    <;> field_simp [hδ.ne'] <;> ring
  have h_rpow_add : Real.rpow δ (-eta) * Real.rpow δ (-3 : ℝ) =
      Real.rpow δ (-(eta + 3)) := by
    have h8 : Real.rpow δ ((-eta) + (-3 : ℝ)) =
        Real.rpow δ (-eta) * Real.rpow δ (-3 : ℝ) :=
      Real.rpow_add hδ (-eta) (-3)
    have h9 : (-eta) + (-3 : ℝ) = (-(eta + 3)) := by ring
    rw [h9] at h8
    exact h8.symm
  have h_main_real : (100000000 : ℝ) * Real.rpow δ (-eta) * ((theta / δ) ^ 2) ≤
      Real.rpow δ (-(eta + 3)) := by
    have h10 : (100000000 : ℝ) * Real.rpow δ (-eta) * ((theta / δ) ^ 2) =
        Real.rpow δ (-eta) * ((100000000 : ℝ) * (theta / δ) ^ 2) := by ring
    rw [h10]
    have h11 : 0 ≤ Real.rpow δ (-eta) := Real.rpow_nonneg hδ' (-eta)
    have h12 : Real.rpow δ (-eta) * ((100000000 : ℝ) * (theta / δ) ^ 2) ≤
        Real.rpow δ (-eta) * (1 / δ ^ 3) := by gcongr
    rw [← h_rpow_neg3] at h12
    rw [← h_rpow_add]
    exact h12
  have h_pos_prod : 0 ≤ (100000000 : ℝ) * Real.rpow δ (-eta) * ((theta / δ) ^ 2) := by
    apply mul_nonneg
    · apply mul_nonneg
      · norm_num
      · exact Real.rpow_nonneg hδ' (-eta)
    · positivity
  have h_enn : ENNReal.ofReal ((100000000 : ℝ) * Real.rpow δ (-eta) * ((theta / δ) ^ 2)) ≤
      ENNReal.ofReal (Real.rpow δ (-(eta + 3))) :=
    ENNReal.ofReal_le_ofReal h_main_real
  have h_pos2 : 0 ≤ (100000000 : ℝ) := by norm_num
  have h_pos3 : 0 ≤ Real.rpow δ (-eta) := Real.rpow_nonneg hδ' (-eta)
  have h_pos4 : 0 ≤ (theta / δ) ^ 2 := by positivity
  have h1 : ENNReal.ofReal 100000000 * ENNReal.ofReal (Real.rpow δ (-eta)) =
      ENNReal.ofReal ((100000000 : ℝ) * Real.rpow δ (-eta)) := by
    rw [← ENNReal.ofReal_mul h_pos2]
  have h2 : 0 ≤ (100000000 : ℝ) * Real.rpow δ (-eta) :=
    mul_nonneg h_pos2 h_pos3
  have h_left : ENNReal.ofReal 100000000 * Kakeya.realRpowENN δ (-eta) *
        ENNReal.ofReal ((theta / δ) ^ 2) =
      ENNReal.ofReal ((100000000 : ℝ) * Real.rpow δ (-eta) * ((theta / δ) ^ 2)) := by
    simp only [Kakeya.realRpowENN]
    rw [h1]
    rw [← ENNReal.ofReal_mul h2]
    <;> rfl
  rw [h_left]
  simpa [Kakeya.realRpowENN] using h_enn

/-- Carrier-wise inclusion implies union-volume inclusion. -/
lemma union_volume_monotone
    {δ : ℝ} {F : Kakeya.TubeFamily δ}
    {Y layer : Kakeya.Shading F}
    (h : ∀ T ∈ F, layer.carrier T ⊆ Y.carrier T) :
    volume layer.union ≤ volume Y.union := by
  have h_sub : layer.union ⊆ Y.union := by
    intro x hx
    rcases hx with ⟨T, hT, hxT⟩
    have h4 : x ∈ layer.carrier T := hxT
    have h5 : x ∈ Y.carrier T := h T hT h4
    exact ⟨T, hT, h5⟩
  exact measure_mono h_sub

/--
Low-density exponent inequality:
`4*(4*eta + eta) + eta/2 + 3*eta*(1-eta) < loss`
when `0 < eta ≤ loss/200`.
-/
lemma assembly_lowdensity_ineq
    (loss eta : ℝ)
    (h_loss_pos : 0 < loss)
    (h_eta_pos : 0 < eta)
    (h_eta_le_loss : eta ≤ loss / 200) :
    4 * (4 * eta + eta) + eta / 2 + 3 * eta * (1 - eta) < loss := by
  have h1 : 4 * (4 * eta + eta) + eta / 2 + 3 * eta * (1 - eta) =
      (47 / 2 : ℝ) * eta - 3 * eta ^ 2 := by ring
  rw [h1]
  have h2 : (47 / 2 : ℝ) * eta - 3 * eta ^ 2 < (47 / 2 : ℝ) * eta := by
    have h3 : 0 < 3 * eta ^ 2 := by positivity
    linarith
  have h4 : (47 / 2 : ℝ) * eta ≤ (47 / 2 : ℝ) * (loss / 200) := by
    gcongr <;> linarith
  have h5 : (47 / 2 : ℝ) * (loss / 200) < loss := by
    have h6 : 0 < loss := h_loss_pos
    nlinarith
  linarith

/--
Small-scale exponent inequality:
`4*eta < loss` when `eta ≤ loss/200`.
-/
lemma assembly_smallscale_ineq
    (loss eta : ℝ)
    (h_loss_pos : 0 < loss)
    (h_eta_le_loss : eta ≤ loss / 200) :
    4 * eta < loss := by
  have h1 : 4 * eta ≤ 4 * (loss / 200) := by gcongr <;> linarith
  have h2 : 4 * (loss / 200) < loss := by
    have h3 : 0 < loss := h_loss_pos
    nlinarith
  linarith

/--
Numerical closure exponent inequality (B.29):
`(1 + 6*eta + 2 + 5*eta*(5-eta)/(1-eta) + 2*eta) / 2 < 3/2 + loss`
when `0 < eta ≤ loss/200` and `eta ≤ 1/200`.
-/
lemma numerical_closure_inequality
    (loss eta : ℝ)
    (h_loss_pos : 0 < loss)
    (h_eta_pos : 0 < eta)
    (h_eta_le_loss : eta ≤ loss / 200)
    (h_eta_small : eta ≤ 1 / 200) :
    (1 + 6 * eta + 2 + 5 * eta * ((5 - eta) / (1 - eta)) + 2 * eta) / 2 <
      3 / 2 + loss := by
  have h1 : 0 < 1 - eta := by linarith
  have h_denom_le : 1 / (1 - eta) ≤ 200 / 199 := by
    have h6 : 199 / 200 ≤ 1 - eta := by linarith
    have h_pos : 0 < 1 - eta := by linarith
    have h7 : 1 ≤ (1 - eta) * (200 / 199) := by
      nlinarith
    calc
      1 / (1 - eta)
        ≤ ((1 - eta) * (200 / 199)) / (1 - eta) := by gcongr <;> linarith
      _ = 200 / 199 := by
        field_simp [h_pos.ne'] <;> ring
  have h2 : (5 - eta) / (1 - eta) < 1000 / 199 := by
    have h9 : (5 - eta) / (1 - eta) = (5 - eta) * (1 / (1 - eta)) := by ring
    rw [h9]
    have h10 : 0 ≤ 1 / (1 - eta) := by positivity
    have h11 : (5 - eta) * (1 / (1 - eta)) ≤ (5 - eta) * (200 / 199) := by
      apply mul_le_mul_of_nonneg_left h_denom_le
      linarith
    have h12 : (5 - eta) * (200 / 199) < (5 : ℝ) * (200 / 199) := by
      have h13 : 0 < 200 / 199 := by norm_num
      nlinarith
    have h14 : (5 : ℝ) * (200 / 199) = 1000 / 199 := by norm_num
    linarith
  have h13 : (1000 / 199 : ℝ) < 253 / 10 := by norm_num
  have h2' : (5 - eta) / (1 - eta) < 253 / 10 := lt_trans h2 h13
  have h3 : 1 + 6 * eta + 2 + 5 * eta * ((5 - eta) / (1 - eta)) + 2 * eta <
      3 + (269 / 2 : ℝ) * eta := by
    have h4 : 5 * eta * ((5 - eta) / (1 - eta)) < 5 * eta * (253 / 10) := by
      have h5 : 0 < 5 * eta := by positivity
      exact mul_lt_mul_of_pos_left h2' h5
    have h6 : 5 * eta * (253 / 10) = (253 / 2 : ℝ) * eta := by ring
    linarith
  have h7 : (269 / 2 : ℝ) * eta < loss := by
    have h8 : (269 / 2 : ℝ) * eta ≤ (269 / 2 : ℝ) * (loss / 200) := by
      gcongr <;> linarith
    have h9 : (269 / 2 : ℝ) * (loss / 200) < loss := by
      have h10 : 0 < loss := h_loss_pos
      nlinarith
    linarith
  have h10 : 1 + 6 * eta + 2 + 5 * eta * ((5 - eta) / (1 - eta)) + 2 * eta <
      3 + loss := by
    calc
      1 + 6 * eta + 2 + 5 * eta * ((5 - eta) / (1 - eta)) + 2 * eta
        < 3 + (269 / 2 : ℝ) * eta := h3
      _ < 3 + loss := by
        have h : (269 / 2 : ℝ) * eta < loss := h7
        linarith
  linarith

/--
Exact numerical-closure exponent inequality used by the canonical local
assembly with output exponent `1 + 7 * eta`.
-/
lemma self_contained_numerical_closure_inequality
    (loss eta : ℝ)
    (h_loss_pos : 0 < loss)
    (h_eta_pos : 0 < eta)
    (h_eta_le_loss : eta ≤ loss / 200)
    (h_eta_small : eta ≤ 1 / 200) :
    ((1 + 7 * eta) + 2 + (4 * eta + eta) *
          (3 + hairbrushHomogeneousDensityPower eta + 1) +
        2 * eta) / 2 <
      3 / 2 + loss := by
  have h_eta_one : eta < 1 := by linarith
  have h_frac_bound : (5 - eta) / (1 - eta) ≤ 1000 / 199 := by
    have h_denom_pos : 0 < 1 - eta := by linarith
    have h_denom_lower : 199 / 200 ≤ 1 - eta := by linarith
    have h_inv_bound : 1 / (1 - eta) ≤ 200 / 199 := by
      apply (div_le_iff₀ h_denom_pos).2
      nlinarith
    calc
      (5 - eta) / (1 - eta)
          = (5 - eta) * (1 / (1 - eta)) := by ring
      _ ≤ (5 - eta) * (200 / 199) := by
        gcongr
        linarith
      _ ≤ 5 * (200 / 199) := by
        gcongr
        linarith
      _ = 1000 / 199 := by norm_num
  have h_power :
      3 + hairbrushHomogeneousDensityPower eta + 1 =
        (5 - eta) / (1 - eta) := by
    rw [hairbrushHomogeneousDensityPower]
    field_simp [ne_of_gt (by linarith : 0 < 1 - eta)]
    ring
  rw [h_power]
  have h_linear :
      9 * eta + 5 * eta * ((5 - eta) / (1 - eta)) < 2 * loss := by
    have h_first : 9 * eta ≤ (9 / 200 : ℝ) * loss := by
      calc
        9 * eta ≤ 9 * (loss / 200) := by gcongr
        _ = (9 / 200 : ℝ) * loss := by ring
    have h_second :
        5 * eta * ((5 - eta) / (1 - eta)) ≤
          (25 / 199 : ℝ) * loss := by
      calc
        5 * eta * ((5 - eta) / (1 - eta))
            ≤ 5 * eta * (1000 / 199) := by gcongr
        _ = (5000 / 199 : ℝ) * eta := by ring
        _ ≤ (5000 / 199 : ℝ) * (loss / 200) := by gcongr
        _ = (25 / 199 : ℝ) * loss := by ring
    have h_coeff :
        (9 / 200 : ℝ) * loss + (25 / 199 : ℝ) * loss < 2 * loss := by
      nlinarith
    linarith
  linarith

/--
Simplified low-density exponent inequality.
`4*(4*eta + eta) + eta/2 + 3*eta*(1-eta) < loss` when `eta ≤ loss/200`.
-/
lemma low_density_inequality
    (loss eta : ℝ)
    (h_loss_pos : 0 < loss)
    (h_eta_pos : 0 < eta)
    (h_eta_le : eta ≤ loss / 200) :
    4 * (4 * eta + eta) + eta / 2 + 3 * eta * (1 - eta) < loss := by
  nlinarith [sq_nonneg (eta - loss / 200)]

/--
Simplified small-scale exponent inequality.
`4*eta < loss` when `eta ≤ loss/100` and `loss > 0`.
-/
lemma small_scale_inequality
    (loss eta : ℝ)
    (h_loss_pos : 0 < loss)
    (h_eta_le : eta ≤ loss / 100) :
    4 * eta < loss := by
  linarith

/--
Deduce `brush.Nonempty` from the strictly positive cardinality lower bound in
`HairbrushAmbientStemSelectionData`.

Every factor in the lower bound is strictly positive (`angleScale > 0`,
`mu > 0`, `hairDensity > 0`, `H.enncard > 0`, finite positive denominator),
so `brush.enncard > 0`, which is equivalent to `brush.Nonempty`.
-/
lemma brush_nonempty_of_stem_selection
    {δ angleScale hairDensity : ℝ}
    {F : Kakeya.TubeFamily δ}
    {layer : Kakeya.Shading F}
    {mu : ℕ}
    {H : Kakeya.TubeFamily δ}
    {hairShading : Kakeya.Shading H}
    (data : HairbrushAmbientStemSelectionData
              (angleScale := angleScale)
              (hairDensity := hairDensity)
              layer mu hairShading)
    (hδ_pos : 0 < δ)
    (h_angleScale_pos : 0 < angleScale)
    (h_mu_pos : 0 < mu)
    (h_hairDensity_pos : 0 < hairDensity)
    (hH_nonempty : H.Nonempty)
    (hF_nonempty : F.Nonempty) :
    data.brush.Nonempty := by
  have h1 : (0 : ENNReal) < ENNReal.ofReal angleScale :=
    ENNReal.ofReal_pos.mpr h_angleScale_pos
  have h2 : (0 : ENNReal) < (mu : ENNReal) := by
    exact_mod_cast h_mu_pos
  have h3 : (0 : ENNReal) < ENNReal.ofReal hairDensity :=
    ENNReal.ofReal_pos.mpr h_hairDensity_pos
  have h4 : (0 : ENNReal) < H.enncard := by
    simpa [Kakeya.TubeFamily.enncard] using hH_nonempty.card_pos
  have h5 : (0 : ENNReal) < F.enncard := by
    simpa [Kakeya.TubeFamily.enncard] using hF_nonempty.card_pos
  have h6 : (0 : ENNReal) < ENNReal.ofReal (1000 * Real.pi) := by positivity
  have h7 : (0 : ENNReal) < ENNReal.ofReal δ :=
    ENNReal.ofReal_pos.mpr hδ_pos
  set denom : ENNReal :=
      ENNReal.ofReal (1000 * Real.pi) * ENNReal.ofReal δ * F.enncard with hden_def
  set numer : ENNReal :=
      ENNReal.ofReal angleScale * (mu : ENNReal) *
      ENNReal.ofReal hairDensity * H.enncard with hnum_def
  have hden_pos : (0 : ENNReal) < denom := by
    simp only [hden_def]; positivity
  have hden_ne_top : denom ≠ ⊤ := by
    rw [hden_def]
    have h1 : ENNReal.ofReal (1000 * Real.pi) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2 : ENNReal.ofReal δ ≠ ⊤ := ENNReal.ofReal_ne_top
    have h3 : F.enncard ≠ ⊤ := by simp [Kakeya.TubeFamily.enncard]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h1 h2) h3
  have hnum_pos : (0 : ENNReal) < numer := by
    simp only [hnum_def]; positivity
  have h_pos : (0 : ENNReal) < numer / denom :=
    ENNReal.div_pos hnum_pos.ne' hden_ne_top
  have h8 : (0 : ENNReal) < data.brush.enncard :=
    lt_of_lt_of_le h_pos data.brush_cardinality_lower
  have h9 : data.brush.enncard ≠ 0 := h8.ne'
  have h10 : data.brush.Nonempty := by
    simpa [Kakeya.TubeFamily.enncard, Finset.nonempty_iff_ne_empty] using h9
  exact h10

/--
Combine the ambient-stem parameter lower bound with the selected-brush
cardinality bound.  This is the ENNReal reassociation used by the hard-power
leaf in the self-contained assembly.
-/
lemma stem_cardinality_retention
    {δ stemLoss theta angleScale hairDensity : ℝ}
    {ambientCount refinedCount brushCount mu refinedDensity : ENNReal}
    (h_refined : ENNReal.ofReal hairDensity = refinedDensity)
    (h_stem :
      Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta ≤
        ENNReal.ofReal angleScale / ENNReal.ofReal (1000 * Real.pi))
    (h_brush :
      ENNReal.ofReal angleScale * mu * ENNReal.ofReal hairDensity * refinedCount /
          (ENNReal.ofReal (1000 * Real.pi) * ENNReal.ofReal δ * ambientCount) ≤
        brushCount) :
    Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * mu *
          refinedDensity * refinedCount /
        (ENNReal.ofReal δ * ambientCount) ≤
      brushCount := by
  set P : ENNReal := mu * refinedDensity * refinedCount with hP_def
  set Q : ENNReal := ENNReal.ofReal δ * ambientCount with hQ_def
  set Hden : ENNReal := ENNReal.ofReal (1000 * Real.pi) with hHden_def
  have hH_pos : Hden ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hH_top : Hden ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_stem' :
      Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta ≤
        ENNReal.ofReal angleScale / Hden := by
    simpa only [hHden_def] using h_stem
  have h_assoc : ∀ (x : ENNReal), x * P / Q = x * (P / Q) := by
    intro x
    simp only [div_eq_mul_inv]
    exact mul_assoc x P _
  have h_mul :
      Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * (P / Q) ≤
        (ENNReal.ofReal angleScale / Hden) * (P / Q) := by
    gcongr
  have h_main :
      Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * P / Q ≤
        (ENNReal.ofReal angleScale / Hden) * P / Q := by
    rw [h_assoc _, h_assoc _]
    exact h_mul
  have h_algebra :
      (ENNReal.ofReal angleScale / Hden) * P / Q =
        ENNReal.ofReal angleScale * P / (Hden * Q) := by
    rw [h_assoc _]
    exact (ENNReal.mul_div_mul_comm (Or.inl hH_pos) (Or.inl hH_top)).symm
  have hP' :
      P = mu * ENNReal.ofReal hairDensity * refinedCount := by
    simp only [hP_def]
    rw [h_refined]
  have h_brush' :
      ENNReal.ofReal angleScale * P / (Hden * Q) ≤ brushCount := by
    rw [hP', hHden_def, hQ_def]
    simpa only [mul_assoc] using h_brush
  have h_main_expanded :
      Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * mu *
            refinedDensity * refinedCount / Q ≤
        ENNReal.ofReal angleScale * P / (Hden * Q) := by
    have h_eq :
        Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * mu *
              refinedDensity * refinedCount / Q =
          Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * P / Q := by
      rw [hP_def]
      ac_rfl
    calc
      Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * mu *
            refinedDensity * refinedCount / Q =
          Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * P / Q := h_eq
      _ ≤ (ENNReal.ofReal angleScale / Hden) * P / Q := h_main
      _ = ENNReal.ofReal angleScale * P / (Hden * Q) := h_algebra
  exact h_main_expanded.trans h_brush'

/--
If `δ ≤ 2^(-1/eta)`, then the negative `eta` power of `δ` absorbs the
constant two.
-/
lemma two_le_realRpowENN_neg
    {δ eta : ℝ}
    (hδ : 0 < δ)
    (heta : 0 < eta)
    (hδ_bound : δ ≤ Real.rpow 2 (-1 / eta)) :
    (2 : ENNReal) ≤ Kakeya.realRpowENN δ (-eta) := by
  have h_half : Real.rpow δ eta ≤ 1 / 2 := by
    have h_rpow_mono :
        Real.rpow δ eta ≤ Real.rpow (Real.rpow 2 (-1 / eta)) eta :=
      Real.rpow_le_rpow hδ.le hδ_bound heta.le
    have h_rpow_eq :
        Real.rpow (Real.rpow 2 (-1 / eta)) eta =
          Real.rpow 2 ((-1 / eta) * eta) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (-1 / eta) eta).symm
    rw [h_rpow_eq] at h_rpow_mono
    have h_mul : (-1 / eta) * eta = -1 := by
      rw [neg_div, neg_mul, one_div_mul_cancel heta.ne']
    rw [h_mul] at h_rpow_mono
    have h_rpow2 : Real.rpow 2 (-1 : ℝ) = 1 / 2 := by
      have h :
          Real.rpow 2 (-1 : ℝ) = (Real.rpow 2 (1 : ℝ))⁻¹ :=
        Real.rpow_neg (by norm_num) (1 : ℝ)
      rw [h]
      norm_num
    simpa only [h_rpow2] using h_rpow_mono
  have h_neg : Real.rpow δ (-eta) = 1 / Real.rpow δ eta := by
    have h : Real.rpow δ (-eta) = (Real.rpow δ eta)⁻¹ :=
      Real.rpow_neg hδ.le eta
    rw [h, inv_eq_one_div]
  have h_real : (2 : ℝ) ≤ Real.rpow δ (-eta) := by
    rw [h_neg]
    calc
      (2 : ℝ) = 1 / (1 / 2 : ℝ) := by norm_num
      _ ≤ 1 / Real.rpow δ eta := by
        gcongr
        exact Real.rpow_pos_of_pos hδ eta
  rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
  exact ENNReal.ofReal_le_ofReal h_real

/-- A positive power of a number in `(0, 1]` is at most one. -/
lemma hairbrush_realRpowENN_le_one
    {δ eta : ℝ}
    (hδ : 0 < δ)
    (hδ_one : δ ≤ 1)
    (heta : 0 ≤ eta) :
    Kakeya.realRpowENN δ eta ≤ (1 : ENNReal) := by
  have h_real : Real.rpow δ eta ≤ 1 :=
    Real.rpow_le_one hδ.le hδ_one heta
  simpa only [Kakeya.realRpowENN, ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal h_real

/--
The single-scale tail of `HairbrushLocalNumericalClosureStatement`, after all
loss exponents and its uniform scale threshold have been selected.
-/
def HairbrushLocalNumericalClosureAtScale
    (densityExponent hairbrushExponent densityPower constantLoss outputLoss delta₀ : ℝ) :
    Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
    ∀ theta : ℝ, 0 < theta → theta ≤ 1 →
      ∀ N mu : ENNReal,
        N ≠ 0 → N ≠ ⊤ →
          mu ≠ 0 → mu ≠ ⊤ →
            ∀ density V : ENNReal,
              density ≠ 0 → density ≠ ⊤ →
                V ≠ ⊤ →
                  Kakeya.realRpowENN δ densityExponent ≤ density →
                    ∀ incidenceUpper hairbrushConstant : ENNReal,
                      incidenceUpper ≠ 0 →
                      incidenceUpper ≠ ⊤ →
                      hairbrushConstant ≠ 0 →
                      hairbrushConstant ≠ ⊤ →
                      incidenceUpper ≤
                        Kakeya.realRpowENN δ (-constantLoss) →
                      Kakeya.realRpowENN δ constantLoss ≤
                        hairbrushConstant →
                      ENNReal.ofReal (Real.rpow δ hairbrushExponent) *
                          hairbrushConstant * ENNReal.ofReal theta *
                          ENNReal.rpow density densityPower * mu ≤
                        V →
                      density * N * ENNReal.ofReal (δ ^ 2) ≤
                        incidenceUpper * mu * V →
                      Kakeya.realRpowENN δ (3 / 2 + outputLoss) *
                          ENNReal.ofReal (Real.sqrt theta) *
                          ENNReal.rpow N (1 / 2) ≤
                        V

/--
Apply the specialized numerical-closure tail with the fixed harmless
constants `incidenceUpper = 2` and `hairbrushConstant = 1`, and package its
conclusion as `HairbrushFiberTarget`.
-/
lemma close_hairbrush_fiber_target
    {densityExponent hairbrushExponent densityPower constantLoss outputLoss delta₀ : ℝ}
    (h_nc :
      HairbrushLocalNumericalClosureAtScale
        densityExponent hairbrushExponent densityPower constantLoss outputLoss delta₀)
    {δ theta : ℝ}
    (hδ : 0 < δ)
    (hδ₀ : δ ≤ delta₀)
    (htheta : 0 < theta)
    (htheta_one : theta ≤ 1)
    {F : Kakeya.TubeFamily δ}
    {Y : Kakeya.Shading F}
    {mu density : ENNReal}
    (hF_zero : F.enncard ≠ 0)
    (hF_top : F.enncard ≠ ⊤)
    (hmu_zero : mu ≠ 0)
    (hmu_top : mu ≠ ⊤)
    (hdensity_zero : density ≠ 0)
    (hdensity_top : density ≠ ⊤)
    (hvolume_top : volume Y.union ≠ ⊤)
    (hdensity : Kakeya.realRpowENN δ densityExponent ≤ density)
    (htwo : (2 : ENNReal) ≤ Kakeya.realRpowENN δ (-constantLoss))
    (hone : Kakeya.realRpowENN δ constantLoss ≤ (1 : ENNReal))
    (hhairbrush :
      ENNReal.ofReal (Real.rpow δ hairbrushExponent) * (1 : ENNReal) *
            ENNReal.ofReal theta * ENNReal.rpow density densityPower * mu ≤
        volume Y.union)
    (hincidence :
      density * F.enncard * ENNReal.ofReal (δ ^ 2) ≤
        (2 : ENNReal) * mu * volume Y.union) :
    HairbrushFiberTarget (theta := theta) (loss := outputLoss) Y := by
  have h :=
    h_nc δ hδ hδ₀ theta htheta htheta_one F.enncard mu
      hF_zero hF_top hmu_zero hmu_top density (volume Y.union)
      hdensity_zero hdensity_top hvolume_top hdensity
      (2 : ENNReal) (1 : ENNReal)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      htwo hone hhairbrush hincidence
  simpa only [HairbrushFiberTarget] using h

/--
A subfamily of an essentially-distinct tube family is itself essentially
distinct.
-/
lemma essentially_distinct_of_subset
    {δ : ℝ} {F G : Kakeya.TubeFamily δ}
    (hF : F.IsEssentiallyDistinct)
    (hG : G ⊆ F) :
    G.IsEssentiallyDistinct := by
  intro T hT U hU hne
  exact hF (hG hT) (hG hU) hne

end Kakeya.Assouad
