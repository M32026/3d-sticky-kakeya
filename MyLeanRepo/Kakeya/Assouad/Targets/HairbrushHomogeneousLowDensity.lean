import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.Hairbrush.ExpandedAssemblyAlgebra

namespace Kakeya.Assouad

/-- Generic algebra: if `d > 0`, `d * a * b ≤ 1`, `c ≥ 0`, then `a * (b * c) ≤ c / d`. -/
private lemma main_algebra (a b c d : ℝ) (hd_pos : 0 < d) (h1 : d * a * b ≤ 1) (hc : 0 ≤ c) :
    a * (b * c) ≤ c / d := by
  have h3 : a * (b * c) = (d * a * b) * (c / d) := by
    field_simp [hd_pos.ne']
  rw [h3]
  have h4 : 0 ≤ c / d := div_nonneg hc (by linarith)
  have h5 : (d * a * b) * (c / d) ≤ (1 : ℝ) * (c / d) :=
    mul_le_mul_of_nonneg_right h1 h4
  simpa using h5

/-- Generic algebra: `a * (b * c) = (d * a * b) * (c / d)` when `d ≠ 0`. -/
private lemma algebra_identity {a b c d : ℝ} (hd : d ≠ 0) :
    a * (b * c) = (d * a * b) * (c / d) := by
  have h_step2 : d * (c / d) = c := by
    field_simp [hd]
  calc a * (b * c)
    = a * b * c := by ring
  _ = (a * b) * c := by ring
  _ = (a * b) * (d * (c / d)) := by rw [h_step2]
  _ = d * (a * b) * (c / d) := by ring
  _ = (d * a * b) * (c / d) := by ring

theorem hairbrush_homogeneous_low_density :
    HairbrushHomogeneousLowDensityStatement := by
  intro zeta inputExponent layerLoss hairLoss angleLoss katzExponent outputLoss
    separation cardinalityConstant
    hzeta_pos hzeta_lt hinput_pos hlayer_loss hangle_loss hkatz_loss
    hseparation hcard hgap

  set S : ℝ := inputExponent + layerLoss with hS_def
  set omz : ℝ := 1 - zeta with homz_def
  have homz_pos : 0 < omz := by linarith
  set p : ℝ := 1 + 3 / (2 * omz) with hp_def
  have hp_lt_4 : p < 4 := by
    rw [hp_def]
    have h1 : 3 / (2 * omz) < 3 := by
      have h2 : 1 < 2 * omz := by linarith
      exact div_lt_self (by norm_num) h2
    linarith
  have hp_pos : 0 < p := by positivity

  set B : ℝ := (100 : ℝ) ^ (1 / omz) * separation / (1000 * Real.pi) with hB_def
  have hB_pos : 0 < B := by positivity
  set C : ℝ := (2 : ℝ) ^ p * Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ) with hC_def
  have hC_pos : 0 < C := by positivity

  set E : ℝ := outputLoss - katzExponent / 2 - (3 / 2 : ℝ) * angleLoss - p * S with hE_def
  have hE_pos : 0 < E := by
    rw [hE_def]
    have hS_pos : 0 < S := by linarith
    have h1 : p * S < 4 * S := by nlinarith
    have h2 : (3 / 2 : ℝ) * angleLoss ≤ 3 * omz * angleLoss := by
      have h3 : (3 / 2 : ℝ) ≤ 3 * omz := by linarith
      nlinarith
    nlinarith

  rcases Subunit.exists_delta₀_mul_pow_le_one C hC_pos E hE_pos with
    ⟨delta₀', hdelta₀'_pos, hdelta₀'_le_one, hδ_absorb⟩
  set delta₀ : ℝ := min delta₀' (1 / 1000) with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le : delta₀ ≤ 1 / 1000 := min_le_right _ _

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le, ?_⟩
  intro δ theta angleScale hδ hδ_le hδ_theta htheta_one hangleScale_pos
    hangle_comp katzTaoConstant hkatz_nonneg hkatz_bound F Y hF_card core hvol hlow_density

  have hδ_le_delta₀' : δ ≤ delta₀' := by
    calc δ ≤ delta₀ := hδ_le
         _ ≤ delta₀' := min_le_left _ _
  have hδ_le_half : δ ≤ 1 / 2 := by linarith
  have htheta_pos : 0 < theta := by linarith
  have hpi_pos : 0 < 1000 * Real.pi := by positivity
  have hδ_nonneg : 0 ≤ δ := by linarith

  set hd : ENNReal := core.hairDensity with hd_def
  have hd_ne_zero : hd ≠ 0 := core.hairDensity_pos
  have hd_ne_top : hd ≠ ⊤ := core.hairDensity_ne_top
  set hd_real : ℝ := hd.toReal with hd_real_def
  have hd_real_pos : 0 < hd_real := by
    have h_nonneg : 0 ≤ hd.toReal := by positivity
    by_contra h
    have h' : hd.toReal = 0 := by linarith
    have h'' : hd = 0 ∨ hd = ⊤ := (ENNReal.toReal_eq_zero_iff hd).mp h'
    cases h'' with
    | inl h0 => exact hd_ne_zero h0
    | inr htop => exact hd_ne_top htop

  -- Step 1: hd_real ≥ δ^S / 2
  have h_hd_lower_enn : Kakeya.realRpowENN δ S / 2 ≤ hd := by
    have h1 : Kakeya.realRpowENN δ S ≤ core.layerDensity := core.input_density_retention
    have h2 : Kakeya.realRpowENN δ S * (2 : ENNReal)⁻¹ ≤ core.layerDensity * (2 : ENNReal)⁻¹ := by gcongr
    have h3 : Kakeya.realRpowENN δ S * (2 : ENNReal)⁻¹ ≤ hd := by
      calc Kakeya.realRpowENN δ S * (2 : ENNReal)⁻¹
        ≤ core.layerDensity * (2 : ENNReal)⁻¹ := h2
      _ = core.layerDensity / 2 := by simp [div_eq_mul_inv]
      _ ≤ hd := core.layer_density_le_hair
    simpa [div_eq_mul_inv] using h3
  have h_hd_lower : Real.rpow δ S / 2 ≤ hd_real := by
    have h1 : (Kakeya.realRpowENN δ S / 2).toReal ≤ hd.toReal :=
      ENNReal.toReal_mono hd_ne_top h_hd_lower_enn
    have hpos : 0 ≤ Real.rpow δ S := Real.rpow_nonneg hδ_nonneg S
    have h3 : (Kakeya.realRpowENN δ S).toReal = Real.rpow δ S := by
      rw [Kakeya.realRpowENN, ENNReal.toReal_ofReal hpos]
    have h4 : (Kakeya.realRpowENN δ S / 2).toReal = (Kakeya.realRpowENN δ S).toReal / 2 := by
      rw [ENNReal.toReal_div] <;> norm_num
    rw [h4, h3] at h1
    exact h1

  -- Step 2: volume Y.union ≥ hd * δ²
  rcases core.hairs_nonempty with ⟨T, hT⟩
  have hT_in_F : T ∈ F := core.hairs_subset hT
  have h_vol_lower : hd * ENNReal.ofReal (δ ^ 2) ≤ MeasureTheory.volume Y.union := by
    have h_tube_vol : ENNReal.ofReal (δ ^ 2) ≤ T.volume :=
      tube_volume_lower_bound hδ hδ_le_half T
    have h_eq1 : core.hairShading.carrier T = core.layer.carrier T :=
      core.hair_shading_eq T hT
    have h_eq2 : core.layer.carrier T = Y.carrier T ∩ core.support :=
      core.layer_eq T hT_in_F
    have h_sub1 : core.layer.carrier T ⊆ Y.carrier T := by
      rw [h_eq2]; intro x hx; exact hx.1
    have h_sub2 : Y.carrier T ⊆ Y.union := by
      intro x hx; exact ⟨T, hT_in_F, hx⟩
    calc
      hd * ENNReal.ofReal (δ ^ 2)
        ≤ hd * T.volume := by gcongr
      _ ≤ MeasureTheory.volume (core.hairShading.carrier T) := core.per_hair_density_lower T hT
      _ = MeasureTheory.volume (core.layer.carrier T) := by rw [h_eq1]
      _ ≤ MeasureTheory.volume (Y.carrier T) := MeasureTheory.measure_mono h_sub1
      _ ≤ MeasureTheory.volume Y.union := MeasureTheory.measure_mono h_sub2

  -- Step 3: hd_real ≤ 100 * (separation * δ / angleScale)^omz
  have hbase_pos : 0 < separation * δ / angleScale := by positivity
  have hbase_nonneg : 0 ≤ separation * δ / angleScale := by linarith
  have hrpow_nonneg : 0 ≤ Real.rpow (separation * δ / angleScale) omz :=
    Real.rpow_nonneg hbase_nonneg _
  have hth : (hairbrushHomogeneousLowDensityThreshold δ zeta separation angleScale).toReal =
      100 * (separation * δ / angleScale) ^ omz := by
    have h1 : (hairbrushHomogeneousLowDensityThreshold δ zeta separation angleScale) =
        ENNReal.ofReal 100 * ENNReal.ofReal (Real.rpow (separation * δ / angleScale) omz) := by rfl
    rw [h1]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal hrpow_nonneg]
    <;> rfl
  have hth_top : (hairbrushHomogeneousLowDensityThreshold δ zeta separation angleScale) ≠ ⊤ := by
    have h1 : (hairbrushHomogeneousLowDensityThreshold δ zeta separation angleScale) =
        ENNReal.ofReal 100 * ENNReal.ofReal (Real.rpow (separation * δ / angleScale) omz) := by rfl
    rw [h1]
    have h_a : ENNReal.ofReal 100 ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_b : ENNReal.ofReal (Real.rpow (separation * δ / angleScale) omz) ≠ ⊤ := ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top h_a h_b
  have h3 : hd_real ≤ (hairbrushHomogeneousLowDensityThreshold δ zeta separation angleScale).toReal :=
    ENNReal.toReal_mono hth_top hlow_density
  rw [hth] at h3
  have h_low_real : hd_real ≤ 100 * (separation * δ / angleScale) ^ omz := h3

  -- Step 4: angleScale ≥ 1000π * δ^angleLoss * theta
  have hRhs_top : (ENNReal.ofReal angleScale / ENNReal.ofReal (1000 * Real.pi)) ≠ ⊤ := by
    have h1 : ENNReal.ofReal angleScale ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2 : ENNReal.ofReal (1000 * Real.pi) ≠ 0 := by
      intro h
      have h3 : (1000 * Real.pi) ≤ 0 := ENNReal.ofReal_eq_zero.mp h
      linarith [Real.pi_pos]
    exact ENNReal.div_ne_top h1 h2
  have h1 : (Kakeya.realRpowENN δ angleLoss * ENNReal.ofReal theta).toReal ≤
      (ENNReal.ofReal angleScale / ENNReal.ofReal (1000 * Real.pi)).toReal :=
    ENNReal.toReal_mono hRhs_top hangle_comp
  have hpos1 : 0 ≤ Real.rpow δ angleLoss := Real.rpow_nonneg hδ_nonneg _
  have h2 : (Kakeya.realRpowENN δ angleLoss * ENNReal.ofReal theta).toReal =
      Real.rpow δ angleLoss * theta := by
    rw [ENNReal.toReal_mul, Kakeya.realRpowENN, ENNReal.toReal_ofReal hpos1,
      ENNReal.toReal_ofReal (by linarith)] <;> ring
  have h3 : (ENNReal.ofReal angleScale / ENNReal.ofReal (1000 * Real.pi)).toReal =
      angleScale / (1000 * Real.pi) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
    <;> simp [hpi_pos.ne'] <;> ring
  rw [h2, h3] at h1
  have h_angleScale : angleScale ≥ 1000 * Real.pi * Real.rpow δ angleLoss * theta := by
    have h5 : (1000 * Real.pi) * (Real.rpow δ angleLoss * theta) ≤ angleScale := by
      calc (1000 * Real.pi) * (Real.rpow δ angleLoss * theta)
        ≤ (1000 * Real.pi) * (angleScale / (1000 * Real.pi)) := by gcongr
      _ = angleScale := by field_simp [hpi_pos.ne'] <;> ring
    linarith

  -- Step 5: theta bound
  set X : ℝ := (separation / (1000 * Real.pi)) * Real.rpow δ (1 - angleLoss) with hX_def
  have h_rpow1_pos : 0 < Real.rpow δ (1 - angleLoss) := Real.rpow_pos_of_pos hδ _
  have hX_pos : 0 < X := by
    dsimp only [X]
    positivity
  have h7 : δ / Real.rpow δ angleLoss = Real.rpow δ (1 - angleLoss) := by
    have h9 : Real.rpow δ 1 / Real.rpow δ angleLoss = Real.rpow δ (1 - angleLoss) :=
      (Real.rpow_sub hδ 1 angleLoss).symm
    have h10 : Real.rpow δ 1 = δ := by simp
    rw [h10] at h9
    exact h9
  have h_ratio : separation * δ / angleScale ≤ X / theta := by
    have hδa : 0 < Real.rpow δ angleLoss := Real.rpow_pos_of_pos hδ angleLoss
    calc separation * δ / angleScale
      ≤ separation * δ / (1000 * Real.pi * Real.rpow δ angleLoss * theta) := by gcongr
    _ = X / theta := by
      have h9 : separation * δ / (1000 * Real.pi * Real.rpow δ angleLoss * theta) =
          ((separation / (1000 * Real.pi)) * (δ / Real.rpow δ angleLoss)) / theta := by
        field_simp [hδa.ne', htheta_pos.ne', hpi_pos.ne'] <;> ring
      rw [h9, h7, hX_def] <;> ring
  have h5 : hd_real ≤ 100 * (X / theta) ^ omz := by
    calc hd_real
      ≤ 100 * (separation * δ / angleScale) ^ omz := h_low_real
    _ ≤ 100 * (X / theta) ^ omz := by gcongr
  have hXtheta_pos : 0 < X / theta := by positivity
  have h6 : theta ^ omz ≤ (100 : ℝ) * X ^ omz / hd_real := by
    have h_div_rpow : (X / theta) ^ omz = X ^ omz / theta ^ omz := by
      rw [Real.div_rpow (by positivity) (by positivity)]
    have h5' : hd_real ≤ (100 : ℝ) * X ^ omz / theta ^ omz := by
      rw [h_div_rpow] at h5
      have h_eq : 100 * (X ^ omz / theta ^ omz) = (100 : ℝ) * X ^ omz / theta ^ omz := by ring
      rw [h_eq] at h5
      exact h5
    have h_pos_theta : 0 < theta ^ omz := by positivity
    have h_nonneg_theta : 0 ≤ theta ^ omz := by positivity
    have h10 : hd_real * theta ^ omz ≤ ((100 : ℝ) * X ^ omz / theta ^ omz) * theta ^ omz :=
      mul_le_mul_of_nonneg_right h5' h_nonneg_theta
    have h11 : ((100 : ℝ) * X ^ omz / theta ^ omz) * theta ^ omz = (100 : ℝ) * X ^ omz := by
      field_simp [h_pos_theta.ne'] <;> ring
    have h_mul : hd_real * theta ^ omz ≤ (100 : ℝ) * X ^ omz := by
      rw [h11] at h10
      exact h10
    have h9 : 0 < hd_real := hd_real_pos
    calc theta ^ omz
      = (hd_real * theta ^ omz) / hd_real := by field_simp [h9.ne'] <;> ring
    _ ≤ ((100 : ℝ) * X ^ omz) / hd_real := by gcongr
  have h8 : theta ≤ ((100 : ℝ) * X ^ omz / hd_real) ^ (1 / omz) := by
    by_contra h12
    have h13 : (((100 : ℝ) * X ^ omz / hd_real) ^ (1 / omz)) < theta := by linarith
    have h14 : (((100 : ℝ) * X ^ omz / hd_real) ^ (1 / omz)) ^ omz < theta ^ omz := by
      gcongr <;> positivity
    have h15 : (((100 : ℝ) * X ^ omz / hd_real) ^ (1 / omz)) ^ omz = (100 : ℝ) * X ^ omz / hd_real := by
      rw [← Real.rpow_mul (by positivity) (1 / omz) omz]
      have h16 : (1 / omz) * omz = 1 := by field_simp [homz_pos.ne'] <;> ring
      rw [h16] <;> simp
    rw [h15] at h14
    linarith
  have h_pos3 : 0 < (100 : ℝ) * X ^ omz / hd_real := by positivity
  have h17 : (((100 : ℝ) * X ^ omz / hd_real) ^ (1 / omz)) =
      (100 : ℝ) ^ (1 / omz) * X * hd_real ^ (-(1 / omz)) := by
    have h_a : ((100 : ℝ) * X ^ omz / hd_real) ^ (1 / omz) =
        ((100 : ℝ) * X ^ omz) ^ (1 / omz) / hd_real ^ (1 / omz) := by
      rw [Real.div_rpow (by positivity) (by positivity)]
    rw [h_a]
    have h_b : ((100 : ℝ) * X ^ omz) ^ (1 / omz) =
        (100 : ℝ) ^ (1 / omz) * (X ^ omz) ^ (1 / omz) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [h_b]
    have h_c : (X ^ omz) ^ (1 / omz) = X := by
      rw [← Real.rpow_mul (by positivity)]
      have h_d : omz * (1 / omz) = 1 := by field_simp [homz_pos.ne'] <;> ring
      rw [h_d] <;> simp
    have h_e : (hd_real ^ (1 / omz))⁻¹ = hd_real ^ (-(1 / omz)) := by
      rw [← Real.rpow_neg (by positivity)] <;> ring
    rw [h_c]
    have h_f : (100 : ℝ) ^ (1 / omz) * X / hd_real ^ (1 / omz) =
        (100 : ℝ) ^ (1 / omz) * X * (hd_real ^ (1 / omz))⁻¹ := by ring
    rw [h_f, h_e] <;> ring
  rw [h17] at h8
  have h20 : (100 : ℝ) ^ (1 / omz) * X = B * Real.rpow δ (1 - angleLoss) := by
    simp [hX_def, hB_def] <;> ring
  rw [h20] at h8
  have h_theta_bound : theta ≤ B * Real.rpow δ (1 - angleLoss) * hd_real ^ (-(1 / omz)) := h8

  -- Step 6: F.enncard.toReal bound
  have hF_card_pos : 0 < F.card := Finset.card_pos.mpr ⟨T, hT_in_F⟩
  have hF_eq : F.enncard = ↑(F.card) := by
    simp [TubeFamily.enncard]
  have hF_ne_top : F.enncard ≠ ⊤ := by
    rw [hF_eq]
    <;> simp
  have hF_ne_zero : F.enncard ≠ 0 := by
    rw [hF_eq]
    intro h3
    have h4 : F.card = 0 := by simpa using h3
    linarith
  have hRhs_top : (ENNReal.ofReal cardinalityConstant * Kakeya.realRpowENN δ (-katzExponent) *
        ENNReal.ofReal ((theta / δ) ^ 2)) ≠ ⊤ := by
    have h1 : ENNReal.ofReal cardinalityConstant ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2 : Kakeya.realRpowENN δ (-katzExponent) ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    have h3 : ENNReal.ofReal ((theta / δ) ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h4 : (ENNReal.ofReal cardinalityConstant * Kakeya.realRpowENN δ (-katzExponent)) ≠ ⊤ := by
      apply ENNReal.mul_ne_top <;> tauto
    have h5 : ((ENNReal.ofReal cardinalityConstant * Kakeya.realRpowENN δ (-katzExponent)) *
          ENNReal.ofReal ((theta / δ) ^ 2)) ≠ ⊤ := by
      apply ENNReal.mul_ne_top <;> tauto
    simpa [mul_assoc] using h5
  have hF_card_real : F.enncard.toReal ≤ cardinalityConstant * Real.rpow δ (-katzExponent) * (theta / δ) ^ 2 := by
    have h30 : F.enncard ≤
        ENNReal.ofReal cardinalityConstant * Kakeya.realRpowENN δ (-katzExponent) *
          ENNReal.ofReal ((theta / δ) ^ 2) := by
      calc F.enncard
        ≤ ENNReal.ofReal cardinalityConstant * ENNReal.ofReal katzTaoConstant *
              ENNReal.ofReal ((theta / δ) ^ 2) := hF_card
      _ ≤ ENNReal.ofReal cardinalityConstant * Kakeya.realRpowENN δ (-katzExponent) *
            ENNReal.ofReal ((theta / δ) ^ 2) := by gcongr
    have h31 : (F.enncard).toReal ≤
        (ENNReal.ofReal cardinalityConstant * Kakeya.realRpowENN δ (-katzExponent) *
          ENNReal.ofReal ((theta / δ) ^ 2)).toReal := ENNReal.toReal_mono hRhs_top h30
    have hpos1 : 0 ≤ cardinalityConstant := by linarith
    have hpos2 : 0 ≤ Real.rpow δ (-katzExponent) := Real.rpow_nonneg hδ_nonneg _
    have hpos3 : 0 ≤ (theta / δ) ^ 2 := by positivity
    have h32 : (ENNReal.ofReal cardinalityConstant * Kakeya.realRpowENN δ (-katzExponent) *
          ENNReal.ofReal ((theta / δ) ^ 2)).toReal =
        cardinalityConstant * Real.rpow δ (-katzExponent) * (theta / δ) ^ 2 := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, Kakeya.realRpowENN,
        ENNReal.toReal_ofReal hpos1, ENNReal.toReal_ofReal hpos2, ENNReal.toReal_ofReal hpos3] <;> ring
    rw [h32] at h31
    exact h31

  -- Step 7: Main Real inequality
  have h_rpow_katz_nonneg : 0 ≤ Real.rpow δ (-katzExponent) := Real.rpow_nonneg hδ_nonneg _
  have h_sqrt_F : Real.sqrt (F.enncard.toReal) ≤
      Real.sqrt cardinalityConstant * Real.rpow δ (-katzExponent / 2) * (theta / δ) := by
    have h2 : 0 ≤ cardinalityConstant * Real.rpow δ (-katzExponent) * (theta / δ) ^ 2 := by
      positivity
    have h3 : Real.sqrt (F.enncard.toReal) ≤
        Real.sqrt (cardinalityConstant * Real.rpow δ (-katzExponent) * (theta / δ) ^ 2) :=
      Real.sqrt_le_sqrt hF_card_real
    have h5 : 0 ≤ cardinalityConstant := by linarith
    have h7 : 0 ≤ theta / δ := by positivity
    have h8 : Real.sqrt (cardinalityConstant * Real.rpow δ (-katzExponent) * (theta / δ) ^ 2) =
        Real.sqrt cardinalityConstant * Real.sqrt (Real.rpow δ (-katzExponent)) * Real.sqrt ((theta / δ) ^ 2) := by
      rw [Real.sqrt_mul, Real.sqrt_mul] <;> positivity
    have h91 : Real.sqrt (Real.rpow δ (-katzExponent)) = (Real.rpow δ (-katzExponent)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow] <;> positivity
    have h92 : (Real.rpow δ (-katzExponent)) ^ (1 / 2 : ℝ) = Real.rpow δ ((-katzExponent) * (1 / 2 : ℝ)) := by
      exact (Real.rpow_mul hδ_nonneg (-katzExponent) (1 / 2 : ℝ)).symm
    have h93 : (-katzExponent) * (1 / 2 : ℝ) = -katzExponent / 2 := by ring
    have h9 : Real.sqrt (Real.rpow δ (-katzExponent)) = Real.rpow δ (-katzExponent / 2) := by
      rw [h91, h92, h93]
    have h10 : Real.sqrt ((theta / δ) ^ 2) = theta / δ := by
      rw [Real.sqrt_sq] <;> positivity
    have h4 : Real.sqrt (cardinalityConstant * Real.rpow δ (-katzExponent) * (theta / δ) ^ 2) =
        Real.sqrt cardinalityConstant * Real.rpow δ (-katzExponent / 2) * (theta / δ) := by
      rw [h8, h9, h10] <;> ring
    rw [h4] at h3
    exact h3

  have h_theta32 : theta ^ (3 / 2 : ℝ) ≤
      (B * Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) * hd_real ^ (-(3 / (2 * omz))) := by
    have h1 : theta ≤ B * Real.rpow δ (1 - angleLoss) * hd_real ^ (-(1 / omz)) := h_theta_bound
    have h4 : 0 ≤ B * Real.rpow δ (1 - angleLoss) * hd_real ^ (-(1 / omz)) := by positivity
    have h5 : theta ^ (3 / 2 : ℝ) ≤
        (B * Real.rpow δ (1 - angleLoss) * hd_real ^ (-(1 / omz))) ^ (3 / 2 : ℝ) := by
      gcongr <;> positivity
    have h7 : 0 < B * Real.rpow δ (1 - angleLoss) := by positivity
    have h91 : (hd_real ^ (-(1 / omz))) ^ (3 / 2 : ℝ) = hd_real ^ ((-(1 / omz)) * (3 / 2 : ℝ)) := by
      rw [Real.rpow_mul (by linarith)]
    have h92 : (-(1 / omz)) * (3 / 2 : ℝ) = -(3 / (2 * omz)) := by ring
    have h9 : (hd_real ^ (-(1 / omz))) ^ (3 / 2 : ℝ) = hd_real ^ (-(3 / (2 * omz))) := by
      rw [h91, h92]
    have h6 : (B * Real.rpow δ (1 - angleLoss) * hd_real ^ (-(1 / omz))) ^ (3 / 2 : ℝ) =
        (B * Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) * hd_real ^ (-(3 / (2 * omz))) := by
      rw [Real.mul_rpow (by positivity) (by positivity), h9] <;> ring
    rw [h6] at h5
    exact h5

  have h_rpowS_pos : 0 < Real.rpow δ S := Real.rpow_pos_of_pos hδ S
  have h_hd_p_lower : hd_real ^ p ≥ Real.rpow δ (p * S) / (2 : ℝ) ^ p := by
    have h1 : Real.rpow δ S / 2 ≤ hd_real := h_hd_lower
    have h2 : 0 < Real.rpow δ S / 2 := by
      exact half_pos h_rpowS_pos
    have h3 : (Real.rpow δ S / 2) ^ p ≤ hd_real ^ p := by gcongr <;> positivity
    have h41 : (Real.rpow δ S / 2) ^ p = (Real.rpow δ S) ^ p / (2 : ℝ) ^ p := by
      rw [Real.div_rpow (by positivity) (by positivity)]
    have h42 : (Real.rpow δ S) ^ p = Real.rpow δ (S * p) := by
      exact (Real.rpow_mul hδ_nonneg S p).symm
    have h43 : S * p = p * S := by ring
    have h4 : (Real.rpow δ S / 2) ^ p = Real.rpow δ (p * S) / (2 : ℝ) ^ p := by
      rw [h41, h42, h43]
    rw [h4] at h3
    exact h3

  have h_C_ineq : C * Real.rpow δ E ≤ 1 := hδ_absorb δ hδ hδ_le_delta₀'

  set A' : ℝ := Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ) *
      Real.rpow δ (outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) with hA'_def
  have h3_C : C = (2 : ℝ) ^ p * Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ) := by
    exact hC_def
  have h61 : Real.rpow δ E * Real.rpow δ (p * S) = Real.rpow δ (E + p * S) :=
    (Real.rpow_add hδ E (p * S)).symm
  have h62 : E + p * S = outputLoss - katzExponent / 2 - (3 / 2) * angleLoss := by
    rw [hE_def] <;> ring
  have h6 : Real.rpow δ E * Real.rpow δ (p * S) =
      Real.rpow δ (outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) := by
    rw [h61, h62]
  have h7 : 0 < (2 : ℝ) ^ p := by positivity
  have h_key : A' ≤ hd_real ^ p := by
    have h1_raw : (2 : ℝ) ^ p * Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ) * Real.rpow δ E ≤ 1 := by
      rw [h3_C] at h_C_ineq; exact h_C_ineq
    have h1 : (2 : ℝ) ^ p * (Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ)) * Real.rpow δ E ≤ 1 := by
      have h_eq : (2 : ℝ) ^ p * (Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ)) * Real.rpow δ E =
          (2 : ℝ) ^ p * Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ) * Real.rpow δ E := by ring
      rw [h_eq]
      exact h1_raw
    have hc : 0 ≤ Real.rpow δ (p * S) := Real.rpow_nonneg hδ_nonneg _
    have hA'_split : A' = (Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ)) * (Real.rpow δ E * Real.rpow δ (p * S)) := by
      rw [hA'_def, ←h6] <;> ring
    rw [hA'_split]
    have h_main : (Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ)) * (Real.rpow δ E * Real.rpow δ (p * S)) ≤
        Real.rpow δ (p * S) / (2 : ℝ) ^ p :=
      main_algebra
        (Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ))
        (Real.rpow δ E)
        (Real.rpow δ (p * S))
        ((2 : ℝ) ^ p)
        h7
        h1
        hc
    exact h_main.trans h_hd_p_lower

  have h_exp1 : Real.rpow δ (3 / 2 + outputLoss) * Real.rpow δ (-katzExponent / 2) / δ =
      Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) := by
    have h1 : Real.rpow δ (-1 : ℝ) = (1 : ℝ) / δ := by
      have h1a : Real.rpow δ (-1 : ℝ) = (Real.rpow δ (1 : ℝ))⁻¹ := by
        simp [Real.rpow_neg, hδ.le]
      rw [h1a]
      have h1b : Real.rpow δ (1 : ℝ) = δ := Real.rpow_one δ
      rw [h1b] <;> field_simp
    have h2 : Real.rpow δ (3 / 2 + outputLoss) * Real.rpow δ (-katzExponent / 2) / δ =
        Real.rpow δ (3 / 2 + outputLoss) * Real.rpow δ (-katzExponent / 2) * Real.rpow δ (-1 : ℝ) := by
      rw [div_eq_mul_one_div, ←h1] <;> ring
    rw [h2]
    have h3 : Real.rpow δ (3 / 2 + outputLoss) * Real.rpow δ (-katzExponent / 2) * Real.rpow δ (-1 : ℝ) =
        Real.rpow δ (((3 / 2 + outputLoss) + (-katzExponent / 2)) + (-1 : ℝ)) := by
      have h3a : Real.rpow δ (3 / 2 + outputLoss) * Real.rpow δ (-katzExponent / 2) =
          Real.rpow δ ((3 / 2 + outputLoss) + (-katzExponent / 2)) :=
        (Real.rpow_add hδ (3 / 2 + outputLoss) (-katzExponent / 2)).symm
      rw [h3a]
      have h3b : Real.rpow δ ((3 / 2 + outputLoss) + (-katzExponent / 2)) * Real.rpow δ (-1 : ℝ) =
          Real.rpow δ (((3 / 2 + outputLoss) + (-katzExponent / 2)) + (-1 : ℝ)) :=
        (Real.rpow_add hδ ((3 / 2 + outputLoss) + (-katzExponent / 2)) (-1 : ℝ)).symm
      exact h3b
    rw [h3]
    have h4 : ((3 / 2 + outputLoss) + (-katzExponent / 2)) + (-1 : ℝ) = 1 / 2 + outputLoss - katzExponent / 2 := by ring
    rw [h4]
  have h_sqrt_theta_sq : Real.sqrt theta * theta = theta ^ (3 / 2 : ℝ) := by
    have hsqrt : Real.sqrt theta = theta ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow] <;> linarith
    rw [hsqrt]
    have h4 : theta ^ (1 / 2 : ℝ) * theta = theta ^ (1 / 2 : ℝ) * theta ^ (1 : ℝ) := by
      rw [Real.rpow_one theta]
    rw [h4]
    have h5 : theta ^ (1 / 2 : ℝ) * theta ^ (1 : ℝ) = theta ^ ((1 / 2 : ℝ) + (1 : ℝ)) :=
      (Real.rpow_add htheta_pos (1 / 2) 1).symm
    rw [h5]
    have h6 : (1 / 2 : ℝ) + (1 : ℝ) = (3 / 2 : ℝ) := by ring
    rw [h6]
  have h_B_exp : (B * Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) =
      B ^ (3 / 2 : ℝ) * Real.rpow δ ((1 - angleLoss) * (3 / 2 : ℝ)) := by
    have hB_nonneg : 0 ≤ B := hB_pos.le
    have h_rpow_nonneg : 0 ≤ Real.rpow δ (1 - angleLoss) := Real.rpow_nonneg hδ_nonneg _
    have h1 : (B * Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) =
        B ^ (3 / 2 : ℝ) * (Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) :=
      Real.mul_rpow hB_nonneg h_rpow_nonneg
    rw [h1]
    have h2 : (Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) =
        Real.rpow δ ((1 - angleLoss) * (3 / 2 : ℝ)) :=
      (Real.rpow_mul hδ_nonneg (1 - angleLoss) (3 / 2 : ℝ)).symm
    rw [h2] <;> ring
  have h_exp2 : Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) *
        Real.rpow δ ((1 - angleLoss) * (3 / 2 : ℝ)) =
      Real.rpow δ (2 + outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) := by
    have h : Real.rpow δ ((1 / 2 + outputLoss - katzExponent / 2) + ((1 - angleLoss) * (3 / 2 : ℝ))) =
        Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) * Real.rpow δ ((1 - angleLoss) * (3 / 2 : ℝ)) :=
      Real.rpow_add hδ (1 / 2 + outputLoss - katzExponent / 2) ((1 - angleLoss) * (3 / 2 : ℝ))
    have h2 : (1 / 2 + outputLoss - katzExponent / 2) + ((1 - angleLoss) * (3 / 2 : ℝ)) =
        2 + outputLoss - katzExponent / 2 - (3 / 2) * angleLoss := by ring
    exact h.symm.trans (by rw [h2])

  have h_final1 : A' * δ ^ 2 * hd_real ^ (-(3 / (2 * omz))) ≤ hd_real * δ ^ 2 := by
    have h9 : p + (-(3 / (2 * omz))) = 1 := by
      simp [hp_def] <;> ring
    have h10 : A' * hd_real ^ (-(3 / (2 * omz))) ≤ hd_real ^ p * hd_real ^ (-(3 / (2 * omz))) := by
      gcongr
    have h11 : hd_real ^ p * hd_real ^ (-(3 / (2 * omz))) = hd_real := by
      rw [← Real.rpow_add hd_real_pos, h9] <;> simp
    have h12 : A' * hd_real ^ (-(3 / (2 * omz))) ≤ hd_real := by
      calc A' * hd_real ^ (-(3 / (2 * omz)))
        ≤ hd_real ^ p * hd_real ^ (-(3 / (2 * omz))) := h10
      _ = hd_real := h11
    have h13 : 0 ≤ δ ^ 2 := by positivity
    calc A' * δ ^ 2 * hd_real ^ (-(3 / (2 * omz)))
      = (A' * hd_real ^ (-(3 / (2 * omz)))) * δ ^ 2 := by ring
    _ ≤ hd_real * δ ^ 2 := by gcongr

  have h_main_real : Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta * Real.sqrt (F.enncard.toReal) ≤
      hd_real * δ ^ 2 := by
    have h_S_pos2 : 0 < S := by rw [hS_def] <;> linarith
    have h4S_pos : 0 < 4 * S := mul_pos (by norm_num) h_S_pos2
    have h_katz_half_nonneg : 0 ≤ katzExponent / 2 := div_nonneg hkatz_loss (by norm_num)
    have h_angle_term_nonneg : 0 ≤ 3 * angleLoss * omz :=
      mul_nonneg (mul_nonneg (by norm_num) hangle_loss) homz_pos.le
    have h1 : 0 < 4 * S + katzExponent / 2 := add_pos_of_pos_of_nonneg h4S_pos h_katz_half_nonneg
    have h_left_pos : 0 < 4 * S + katzExponent / 2 + 3 * angleLoss * omz :=
      add_pos_of_pos_of_nonneg h1 h_angle_term_nonneg
    have h_outputLoss_pos : 0 < outputLoss := h_left_pos.trans hgap
    have h_rpow32_nonneg : 0 ≤ Real.rpow δ (3 / 2 + outputLoss) := Real.rpow_nonneg hδ_nonneg _
    have h_sqrt_theta_nonneg : 0 ≤ Real.sqrt theta := by positivity
    have h_left_nonneg : 0 ≤ Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta :=
      mul_nonneg h_rpow32_nonneg h_sqrt_theta_nonneg
    have h_step1 : Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta * Real.sqrt (F.enncard.toReal) ≤
        Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta *
          (Real.sqrt cardinalityConstant * Real.rpow δ (-katzExponent / 2) * (theta / δ)) :=
      mul_le_mul_of_nonneg_left h_sqrt_F h_left_nonneg
    have h_step2 : Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta *
          (Real.sqrt cardinalityConstant * Real.rpow δ (-katzExponent / 2) * (theta / δ)) =
        Real.sqrt cardinalityConstant * Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) * theta ^ (3 / 2 : ℝ) := by
      have h_rearrange : Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta *
          (Real.sqrt cardinalityConstant * Real.rpow δ (-katzExponent / 2) * (theta / δ)) =
          Real.sqrt cardinalityConstant * (Real.rpow δ (3 / 2 + outputLoss) * Real.rpow δ (-katzExponent / 2) / δ) *
          (Real.sqrt theta * theta) := by ring
      rw [h_rearrange, h_exp1, h_sqrt_theta_sq] <;> ring
    have h_step3 : Real.sqrt cardinalityConstant * Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) * theta ^ (3 / 2 : ℝ) ≤
        Real.sqrt cardinalityConstant * Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) *
          ((B * Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) * hd_real ^ (-(3 / (2 * omz)))) := by
      have h_sqrt_card_nonneg : 0 ≤ Real.sqrt cardinalityConstant := by positivity
      have h_rpow_half_nonneg : 0 ≤ Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) := Real.rpow_nonneg hδ_nonneg _
      have h_card_nonneg : 0 ≤ Real.sqrt cardinalityConstant * Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) :=
        mul_nonneg h_sqrt_card_nonneg h_rpow_half_nonneg
      exact mul_le_mul_of_nonneg_left h_theta32 h_card_nonneg
    have h_step4 : Real.sqrt cardinalityConstant * Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) *
          ((B * Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) * hd_real ^ (-(3 / (2 * omz)))) =
        A' * δ ^ 2 * hd_real ^ (-(3 / (2 * omz))) := by
      have h41 : (B * Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) =
          B ^ (3 / 2 : ℝ) * Real.rpow δ ((1 - angleLoss) * (3 / 2 : ℝ)) := h_B_exp
      have h42 : Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) * Real.rpow δ ((1 - angleLoss) * (3 / 2 : ℝ)) =
          Real.rpow δ (2 + outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) := h_exp2
      have h43 : Real.rpow δ (2 + outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) =
          Real.rpow δ (outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) * δ ^ 2 := by
        have h44 : Real.rpow δ (outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) * δ ^ 2 =
            Real.rpow δ (outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) * Real.rpow δ 2 := by
          have h45 : (δ ^ 2 : ℝ) = Real.rpow δ 2 := by simp
          rw [h45]
        rw [h44]
        have h46 : Real.rpow δ (outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) * Real.rpow δ 2 =
            Real.rpow δ ((outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) + 2) :=
          (Real.rpow_add hδ (outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) 2).symm
        rw [h46]
        have h47 : (outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) + 2 =
            2 + outputLoss - katzExponent / 2 - (3 / 2) * angleLoss := by ring
        rw [h47]
      have h_eq1 : Real.sqrt cardinalityConstant * Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) *
          ((B * Real.rpow δ (1 - angleLoss)) ^ (3 / 2 : ℝ) * hd_real ^ (-(3 / (2 * omz)))) =
        Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ) *
          (Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) * Real.rpow δ ((1 - angleLoss) * (3 / 2 : ℝ))) *
          hd_real ^ (-(3 / (2 * omz))) := by
        rw [h41] <;> ring
      rw [h_eq1]
      have h_eq2 : Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ) *
          (Real.rpow δ (1 / 2 + outputLoss - katzExponent / 2) * Real.rpow δ ((1 - angleLoss) * (3 / 2 : ℝ))) *
          hd_real ^ (-(3 / (2 * omz))) =
        Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ) *
          Real.rpow δ (2 + outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) *
          hd_real ^ (-(3 / (2 * omz))) := by
        rw [h42] <;> ring
      rw [h_eq2]
      have h_eq3 : Real.sqrt cardinalityConstant * B ^ (3 / 2 : ℝ) *
          Real.rpow δ (2 + outputLoss - katzExponent / 2 - (3 / 2) * angleLoss) *
          hd_real ^ (-(3 / (2 * omz))) =
        A' * δ ^ 2 * hd_real ^ (-(3 / (2 * omz))) := by
        rw [h43, hA'_def] <;> ring
      exact h_eq3
    calc
      _ ≤ _ := h_step1
      _ = _ := h_step2
      _ ≤ _ := h_step3
      _ = _ := h_step4
      _ ≤ hd_real * δ ^ 2 := h_final1

  -- Step 8: Convert to ENNReal
  have h_ofReal_hd : ENNReal.ofReal hd_real = hd := by
    rw [← ENNReal.ofReal_toReal hd_ne_top]
  have hF_toReal_nonneg : 0 ≤ F.enncard.toReal := by positivity
  have h2 : ENNReal.ofReal (F.enncard.toReal) = F.enncard := ENNReal.ofReal_toReal hF_ne_top
  have h1 : ENNReal.ofReal (Real.sqrt (F.enncard.toReal)) = ENNReal.rpow F.enncard (1 / 2 : ℝ) := by
    have h1a : ENNReal.ofReal (Real.sqrt (F.enncard.toReal)) = (ENNReal.ofReal (F.enncard.toReal)) ^ (1 / 2 : ℝ) :=
      hairbrush_ofReal_sqrt hF_toReal_nonneg
    have h1b : (ENNReal.ofReal (F.enncard.toReal)) ^ (1 / 2 : ℝ) = ENNReal.rpow F.enncard (1 / 2 : ℝ) := by
      rw [h2]
      <;> simp [ENNReal.rpow]
      <;> rfl
    exact h1a.trans h1b
  have h_main_real' : 0 ≤ Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta * Real.sqrt (F.enncard.toReal) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hδ_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have h3 : ENNReal.ofReal (Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta * Real.sqrt (F.enncard.toReal)) ≤
      ENNReal.ofReal (hd_real * δ ^ 2) := ENNReal.ofReal_le_ofReal h_main_real
  have hpos1 : 0 ≤ Real.rpow δ (3 / 2 + outputLoss) := Real.rpow_nonneg hδ_nonneg _
  have hpos2 : 0 ≤ Real.sqrt theta := by positivity
  have hpos3 : 0 ≤ Real.sqrt (F.enncard.toReal) := by positivity
  have hpos12 : 0 ≤ Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta := mul_nonneg hpos1 hpos2
  have h4 : ENNReal.ofReal (Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta * Real.sqrt (F.enncard.toReal)) =
      Kakeya.realRpowENN δ (3 / 2 + outputLoss) * ENNReal.ofReal (Real.sqrt theta) *
        ENNReal.ofReal (Real.sqrt (F.enncard.toReal)) := by
    have h41 : ENNReal.ofReal (Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta * Real.sqrt (F.enncard.toReal)) =
        ENNReal.ofReal (Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta) * ENNReal.ofReal (Real.sqrt (F.enncard.toReal)) :=
      ENNReal.ofReal_mul hpos12
    rw [h41]
    have h42 : ENNReal.ofReal (Real.rpow δ (3 / 2 + outputLoss) * Real.sqrt theta) =
        ENNReal.ofReal (Real.rpow δ (3 / 2 + outputLoss)) * ENNReal.ofReal (Real.sqrt theta) :=
      ENNReal.ofReal_mul hpos1
    rw [h42]
    have h43 : ENNReal.ofReal (Real.rpow δ (3 / 2 + outputLoss)) = Kakeya.realRpowENN δ (3 / 2 + outputLoss) := by
      rfl
    rw [h43]
    <;> rfl
  have hpos4 : 0 ≤ hd_real := by positivity
  have h5 : ENNReal.ofReal (hd_real * δ ^ 2) = hd * ENNReal.ofReal (δ ^ 2) := by
    rw [ENNReal.ofReal_mul hpos4, h_ofReal_hd] <;> ring
  have h_main_enn : Kakeya.realRpowENN δ (3 / 2 + outputLoss) *
      ENNReal.ofReal (Real.sqrt theta) * ENNReal.rpow F.enncard (1 / 2 : ℝ) ≤
      hd * ENNReal.ofReal (δ ^ 2) := by
    rw [h4, h5] at h3
    rw [h1] at h3
    exact h3

  have h_final : Kakeya.realRpowENN δ (3 / 2 + outputLoss) *
      ENNReal.ofReal (Real.sqrt theta) * ENNReal.rpow F.enncard (1 / 2 : ℝ) ≤
      MeasureTheory.volume Y.union := by
    calc
      _ ≤ hd * ENNReal.ofReal (δ ^ 2) := h_main_enn
      _ ≤ MeasureTheory.volume Y.union := h_vol_lower
  simpa [HairbrushFiberTarget] using h_final

end Kakeya.Assouad
