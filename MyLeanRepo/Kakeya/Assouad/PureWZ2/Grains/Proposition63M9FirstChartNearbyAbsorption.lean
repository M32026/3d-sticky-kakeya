import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.LogAbsorption
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic

/-!
# Family-free logarithmic absorption for the first chart

The first-chart packing estimate is stated directly in terms of the chart
ratio `q`.  This file converts its ninth-power cardinality bound into the
logarithmic majorant consumed by the finite nearby-scale absorption argument.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The family-free first-chart cardinality estimate gives a linear bound in
`log q⁻¹` for the dyadic level count. -/
theorem proposition63_firstChart_family_free_card_log_bound
    {q : ℝ} (hq : 0 < q) (hqOne : q ≤ 1)
    {cardinality : ℕ}
    (hcard : (cardinality : ℝ) ≤
      (259 : ℝ) ^ 3 * (67 : ℝ) ^ 3 * Real.rpow q (-9 : ℝ)) :
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
      (9 / Real.log 2) * Real.log q⁻¹ +
        (Real.log (2 * ((259 : ℝ) ^ 3 * (67 : ℝ) ^ 3)) /
          Real.log 2 + 1) := by
  let K : ℝ := (259 : ℝ) ^ 3 * (67 : ℝ) ^ 3
  have hK : 0 < K := by positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogInv : 0 ≤ Real.log q⁻¹ := by
    apply Real.log_nonneg
    rw [one_le_inv₀ hq]
    exact hqOne
  by_cases hcardZero : cardinality = 0
  · subst cardinality
    have hleft : (Nat.log 2 (2 * 0) + 1 : ℝ) = 1 := by
      rw [Nat.mul_zero, Nat.log_zero_right]
      norm_num
    have hconstantPos : 0 < Real.log (2 * K) / Real.log 2 := by
      have htwoK : 1 < 2 * K := by
        dsimp only [K]
        norm_num
      exact div_pos (Real.log_pos htwoK) hlogTwo
    have hcoefficientNonneg : 0 ≤ 9 / Real.log 2 := by positivity
    rw [hleft]
    have hvariableNonneg :
        0 ≤ (9 / Real.log 2) * Real.log q⁻¹ :=
      mul_nonneg hcoefficientNonneg hlogInv
    dsimp only [K] at hconstantPos
    linarith
  · have hcardPos : 0 < cardinality := Nat.pos_of_ne_zero hcardZero
    have htwoCardPos : 0 < 2 * cardinality := by positivity
    have hnatLog :
        (Nat.log 2 (2 * cardinality) : ℝ) ≤
          Real.log ((2 * cardinality : ℕ) : ℝ) / Real.log 2 := by
      have hpow : (2 : ℕ) ^ Nat.log 2 (2 * cardinality) ≤
          2 * cardinality :=
        Nat.pow_log_le_self 2 htwoCardPos.ne'
      have hpowReal :
          (2 : ℝ) ^ Nat.log 2 (2 * cardinality) ≤
            ((2 * cardinality : ℕ) : ℝ) := by
        exact_mod_cast hpow
      have hlog := Real.log_le_log (by positivity) hpowReal
      rw [Real.log_pow] at hlog
      exact (le_div_iff₀ hlogTwo).mpr (by simpa using hlog)
    have htwoCard : ((2 * cardinality : ℕ) : ℝ) ≤
        2 * (K * Real.rpow q (-9 : ℝ)) := by
      have h : 2 * (cardinality : ℝ) ≤
          2 * (K * Real.rpow q (-9 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa [K] using hcard) (by norm_num)
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    have hlogBound : Real.log ((2 * cardinality : ℕ) : ℝ) ≤
        Real.log (2 * (K * Real.rpow q (-9 : ℝ))) :=
      Real.log_le_log (by exact_mod_cast htwoCardPos) htwoCard
    have hlogProduct :
        Real.log (2 * (K * Real.rpow q (-9 : ℝ))) =
          Real.log (2 * K) + 9 * Real.log q⁻¹ := by
      rw [show 2 * (K * Real.rpow q (-9 : ℝ)) =
          (2 * K) * Real.rpow q (-9 : ℝ) by ring]
      have hmul :
          Real.log ((2 * K) * Real.rpow q (-9 : ℝ)) =
            Real.log (2 * K) + Real.log (Real.rpow q (-9 : ℝ)) :=
        Real.log_mul (by positivity) (Real.rpow_pos_of_pos hq _).ne'
      have hrpowLog : Real.log (Real.rpow q (-9 : ℝ)) =
          (-9 : ℝ) * Real.log q := Real.log_rpow hq _
      rw [hmul, hrpowLog, Real.log_inv]
      ring
    calc
      (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
          Real.log ((2 * cardinality : ℕ) : ℝ) / Real.log 2 + 1 := by
        linarith
      _ ≤ Real.log (2 * (K * Real.rpow q (-9 : ℝ))) /
            Real.log 2 + 1 := by gcongr
      _ = (9 / Real.log 2) * Real.log q⁻¹ +
          (Real.log (2 * ((259 : ℝ) ^ 3 * (67 : ℝ) ^ 3)) /
            Real.log 2 + 1) := by
        rw [hlogProduct]
        dsimp only [K]
        field_simp [hlogTwo.ne']
        ring

/-- Full family-free finite-nearby absorption at the first-chart ratio.  The
input loss is fixed to one quarter of the target loss, and the runtime family
enters only through the ninth-power cardinality bound. -/
theorem proposition63_m9_firstChart_family_free_nearby_absorption
    {targetLoss : ℝ}
    (htargetLoss_pos : 0 < targetLoss)
    (htargetLoss_one : targetLoss ≤ 1) :
    ∃ nearbyInputLoss ratioCutoff : ℝ, ∃ levelCount : ℕ,
      0 < nearbyInputLoss ∧
      3 * nearbyInputLoss < targetLoss ∧
      0 < levelCount ∧
      0 < ratioCutoff ∧
      ratioCutoff ≤ 1 / 24 ∧
      ∀ q : ℝ, 0 < q → q ≤ ratioCutoff →
        ∀ cardinality : ℕ,
        (cardinality : ℝ) ≤
          (259 : ℝ) ^ 3 * (67 : ℝ) ^ 3 * Real.rpow q (-9 : ℝ) →
        let ambientConstant := Kakeya.realRpowENN q (-nearbyInputLoss)
        let outputConstant := Kakeya.realRpowENN q (-targetLoss)
        let density := Kakeya.realRpowENN q nearbyInputLoss
        let degreeConstant :=
          16 * ((levelCount + 1 : ℕ) : ENNReal) *
            (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^ (levelCount + 1)
        let regularizationLoss :=
          (8 : ENNReal) *
            (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^ (levelCount + 2)
        let weight := (1 / 2 : ENNReal) * density
        let cardinalityLoss :=
          (2 * regularizationLoss) *
            (55296 * Kakeya.deltaTubeVolume 1)
        2 < ambientConstant ∧
        ambientConstant ≠ ⊤ ∧
        density ≠ 0 ∧
        density ≠ ⊤ ∧
        ENNReal.ofReal (1 / q) ≤ ambientConstant ^ levelCount ∧
        ambientConstant * ambientConstant ≤ outputConstant ∧
        max degreeConstant
            ((weight⁻¹ *
                (ambientConstant * cardinalityLoss * degreeConstant)) *
              ambientConstant) ≤ outputConstant := by
  set inputLoss : ℝ := targetLoss / 4 with hinputLoss_def
  have hinputLoss_pos : 0 < inputLoss := by positivity
  have h3inputLoss_lt : 3 * inputLoss < targetLoss := by
    rw [hinputLoss_def] <;> linarith
  set levelCount : ℕ := Nat.ceil (1 / inputLoss) + 1 with hlevelCount_def
  have hlevelCount_pos : 0 < levelCount := by positivity
  have hlevelCount_mul : (levelCount : ℝ) * inputLoss ≥ 1 := by
    have h1 : (Nat.ceil (1 / inputLoss) : ℝ) ≥ 1 / inputLoss := Nat.le_ceil _
    have h2 : (levelCount : ℝ) = (Nat.ceil (1 / inputLoss) : ℝ) + 1 := by
      simp [hlevelCount_def] <;> norm_cast
    rw [h2]
    have h3 : ((Nat.ceil (1 / inputLoss) : ℝ) + 1) * inputLoss ≥
        (1 / inputLoss + 1) * inputLoss := by gcongr
    have h4 : (1 / inputLoss + 1) * inputLoss = 1 + inputLoss := by
      field_simp [hinputLoss_pos.ne'] <;> ring
    linarith
  set gap : ℝ := targetLoss / 4 with hgap_def
  have hgap_pos : 0 < gap := by positivity
  have hgap_eq : gap + 3 * inputLoss = targetLoss := by
    rw [hgap_def, hinputLoss_def] <;> ring
  set P : ℕ := 2 * levelCount + 3 with hP_def
  have hP_pos : 0 < P := by positivity
  set C_card : ℝ := max
      (Real.log (2 * ((259 : ℝ) ^ 3 * (67 : ℝ) ^ 3)) / Real.log 2 + 1)
      (9 / Real.log 2) with hC_card_def
  have hC_card_nonneg : 0 ≤ C_card := by positivity
  have hA_le_C : (Real.log (2 * ((259 : ℝ) ^ 3 * (67 : ℝ) ^ 3)) / Real.log 2 + 1) ≤ C_card := by
    rw [hC_card_def] <;> exact le_max_left _ _
  have hB_le_C : (9 / Real.log 2) ≤ C_card := by
    rw [hC_card_def] <;> exact le_max_right _ _
  set K_coeff_ENN : ENNReal :=
      (2 * 16 * 55296 * 16 : ENNReal) * ((levelCount + 1 : ℕ) : ENNReal) *
        Kakeya.deltaTubeVolume 1
    with hK_coeff_ENN_def
  have hK_coeff_ne_top : K_coeff_ENN ≠ ⊤ := by
    dsimp only [K_coeff_ENN]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.natCast_ne_top _
    · exact deltaTubeVolume_one_ne_top
  set K_deg_ENN : ENNReal :=
      (16 : ENNReal) * ((levelCount + 1 : ℕ) : ENNReal)
    with hK_deg_ENN_def
  have hK_deg_ne_top : K_deg_ENN ≠ ⊤ := by
    dsimp only [K_deg_ENN]
    apply ENNReal.mul_ne_top
    · norm_num
    · exact ENNReal.natCast_ne_top _
  rcases exists_delta_realRpowENN_bound (3 : ENNReal) (by norm_num) hinputLoss_pos with
    ⟨δ₁, hδ₁_pos, hδ₁_one, hbound_ambient⟩
  rcases exists_delta_C_pow_log_absorbed_ennreal (n := P)
      K_coeff_ENN hK_coeff_ne_top C_card hC_card_nonneg hgap_pos hP_pos with
    ⟨δ₂, hδ₂_pos, hδ₂_one, hbound_second⟩
  rcases exists_delta_C_pow_log_absorbed_ennreal (n := levelCount + 1)
      K_deg_ENN hK_deg_ne_top C_card hC_card_nonneg htargetLoss_pos (by positivity) with
    ⟨δ₃, hδ₃_pos, hδ₃_one, hbound_degree⟩
  set ratioCutoff : ℝ := min (1 / 24) (min δ₁ (min δ₂ δ₃)) with hratioCutoff_def
  have hratioCutoff_pos : 0 < ratioCutoff := by positivity
  have hratioCutoff_le_24 : ratioCutoff ≤ 1 / 24 := min_le_left _ _
  have hratioCutoff_le_δ1 : ratioCutoff ≤ δ₁ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hratioCutoff_le_δ2 : ratioCutoff ≤ δ₂ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hratioCutoff_le_δ3 : ratioCutoff ≤ δ₃ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine' ⟨inputLoss, ratioCutoff, levelCount, _⟩
  constructor; exact hinputLoss_pos
  constructor; exact h3inputLoss_lt
  constructor; exact hlevelCount_pos
  constructor; exact hratioCutoff_pos
  constructor; exact hratioCutoff_le_24
  intro q hq_pos hq_le cardinality hcard
  dsimp only
  let ambientConstant := Kakeya.realRpowENN q (-inputLoss)
  let outputConstant := Kakeya.realRpowENN q (-targetLoss)
  let density := Kakeya.realRpowENN q inputLoss
  let logTerm : ENNReal := (Nat.log 2 (2 * cardinality) + 1 : ENNReal)
  let degreeConstant := (16 : ENNReal) * ((levelCount + 1 : ℕ) : ENNReal) *
      logTerm ^ (levelCount + 1)
  let regularizationLoss := (8 : ENNReal) * logTerm ^ (levelCount + 2)
  let weight := (1 / 2 : ENNReal) * density
  let cardinalityLoss := (2 * regularizationLoss) * (55296 * Kakeya.deltaTubeVolume 1)
  have hq_le_one : q ≤ 1 :=
    hq_le.trans (hratioCutoff_le_24.trans (by norm_num))
  have hlog_inv_nonneg : 0 ≤ Real.log (1 / q) :=
    Real.log_nonneg (by apply one_le_one_div <;> linarith)
  have hlog_one_eq : Real.log (1 / q) = Real.log q⁻¹ := by
    have h : (1 / q) = q⁻¹ := by field_simp [hq_pos.ne'] <;> ring
    rw [h] <;> rfl
  have hcard_log_real : (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
      C_card * (1 + Real.log q⁻¹) := by
    have h := proposition63_firstChart_family_free_card_log_bound
      hq_pos hq_le_one hcard
    have h5 : (9 / Real.log 2) * Real.log q⁻¹ +
          (Real.log (2 * ((259 : ℝ) ^ 3 * (67 : ℝ) ^ 3)) /
            Real.log 2 + 1) ≤
        C_card * (1 + Real.log q⁻¹) := by
      have h8 : 0 ≤ Real.log q⁻¹ := by
        rw [← hlog_one_eq]
        exact hlog_inv_nonneg
      have h6 : (9 / Real.log 2) * Real.log q⁻¹ ≤
          C_card * Real.log q⁻¹ :=
        mul_le_mul_of_nonneg_right hB_le_C h8
      have h7 :
          (Real.log (2 * ((259 : ℝ) ^ 3 * (67 : ℝ) ^ 3)) /
              Real.log 2 + 1) ≤ C_card := hA_le_C
      calc
        (9 / Real.log 2) * Real.log q⁻¹ +
            (Real.log (2 * ((259 : ℝ) ^ 3 * (67 : ℝ) ^ 3)) /
              Real.log 2 + 1)
            ≤ C_card * Real.log q⁻¹ + C_card := by gcongr
        _ = C_card * (1 + Real.log q⁻¹) := by ring
    exact h.trans h5
  have hcard_log_ENN : logTerm ≤ ENNReal.ofReal (C_card * (1 + Real.log q⁻¹)) := by
    have h9 : logTerm = ENNReal.ofReal ((Nat.log 2 (2 * cardinality) + 1 : ℝ)) := by
      dsimp only [logTerm]
      norm_cast
    rw [h9]
    exact ENNReal.ofReal_mono hcard_log_real
  have h_ambient_gt_two : (2 : ENNReal) < ambientConstant := by
    have h : (3 : ENNReal) ≤ ambientConstant :=
      hbound_ambient q hq_pos (hq_le.trans hratioCutoff_le_δ1)
    exact lt_of_lt_of_le (by norm_num) h
  have h_ambient_ne_top : ambientConstant ≠ ⊤ := by
    simp [ambientConstant, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
  have h_density_ne_zero : density ≠ 0 := by
    simp only [density, Kakeya.realRpowENN]
    have h : 0 < Real.rpow q inputLoss := Real.rpow_pos_of_pos hq_pos _
    have h2 : 0 < ENNReal.ofReal (Real.rpow q inputLoss) := ENNReal.ofReal_pos.mpr h
    exact h2.ne'
  have h_density_ne_top : density ≠ ⊤ := by
    simp [density, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
  have h_scale_reach : ENNReal.ofReal (1 / q) ≤ ambientConstant ^ levelCount := by
    have h1 : (levelCount : ℝ) * inputLoss ≥ 1 := hlevelCount_mul
    have h_exp : -1 ≥ -(levelCount : ℝ) * inputLoss := by linarith
    have h2 : Real.rpow q (-1) ≤ Real.rpow q (-(levelCount : ℝ) * inputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hq_pos hq_le_one h_exp
    have h3 : Real.rpow q (-1) = 1 / q := by
      have h4 : Real.rpow q (-1) = (Real.rpow q 1)⁻¹ := Real.rpow_neg hq_pos.le 1
      rw [h4]
      have h5 : Real.rpow q 1 = q := Real.rpow_one q
      rw [h5] <;> field_simp [hq_pos.ne']
    have h5 : ambientConstant ^ levelCount =
        ENNReal.ofReal (Real.rpow q (-(levelCount : ℝ) * inputLoss)) := by
      have h51 : ambientConstant = ENNReal.ofReal (Real.rpow q (-inputLoss)) := by
        simp [ambientConstant, Kakeya.realRpowENN]
      rw [h51]
      have hnonneg : 0 ≤ Real.rpow q (-inputLoss) := Real.rpow_nonneg hq_pos.le _
      have h52 : (ENNReal.ofReal (Real.rpow q (-inputLoss))) ^ levelCount =
          ENNReal.ofReal ((Real.rpow q (-inputLoss)) ^ levelCount) := by
        rw [ENNReal.ofReal_pow hnonneg]
      rw [h52]
      have h53 : (Real.rpow q (-inputLoss)) ^ levelCount =
          Real.rpow q (-(levelCount : ℝ) * inputLoss) := by
        rw [rpow_nat_pow hq_pos (-inputLoss) levelCount] <;> ring
      rw [h53]
    rw [h5]
    have h2' : (1 / q : ℝ) ≤ Real.rpow q (-(levelCount : ℝ) * inputLoss) := by
      have h_eq : Real.rpow q (-1) = 1 / q := h3
      rw [h_eq] at h2
      exact h2
    exact ENNReal.ofReal_mono h2'
  have h_two_windows : ambientConstant * ambientConstant ≤ outputConstant := by
    have h_add : Kakeya.realRpowENN q (-inputLoss) * Kakeya.realRpowENN q (-inputLoss) =
        Kakeya.realRpowENN q ((-inputLoss) + (-inputLoss)) := by
      exact (realRpowENN_add hq_pos (-inputLoss) (-inputLoss)).symm
    have h_amb : ambientConstant = Kakeya.realRpowENN q (-inputLoss) := by
      simp [ambientConstant]
    have h : ambientConstant * ambientConstant = Kakeya.realRpowENN q (-2 * inputLoss) := by
      rw [h_amb, h_add]
      have h_exp : (-inputLoss) + (-inputLoss) = -2 * inputLoss := by ring
      rw [h_exp]
    rw [h]
    have h2 : -targetLoss ≤ -2 * inputLoss := by
      rw [hinputLoss_def] <;> linarith
    have hq_lt_one : q < 1 := by
      have h : q ≤ 1 / 24 := hq_le.trans hratioCutoff_le_24
      linarith
    exact rpow_monotonic_exp hq_pos hq_lt_one h2
  have h_weight_inv : weight⁻¹ = (2 : ENNReal) * ambientConstant := by
    have h_pos : 0 < Real.rpow q inputLoss := Real.rpow_pos_of_pos hq_pos _
    have h1 : density = ENNReal.ofReal (Real.rpow q inputLoss) := by
      simp [density, Kakeya.realRpowENN]
    have h_density_inv : density⁻¹ = ambientConstant := by
      rw [h1]
      have h2 : (ENNReal.ofReal (Real.rpow q inputLoss))⁻¹ =
          ENNReal.ofReal ((Real.rpow q inputLoss)⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos h_pos]
      rw [h2]
      have h3 : (Real.rpow q inputLoss)⁻¹ = Real.rpow q (-inputLoss) := by
        exact (Real.rpow_neg hq_pos.le inputLoss).symm
      rw [h3]
      have h4 : ambientConstant = ENNReal.ofReal (Real.rpow q (-inputLoss)) := by
        simp [ambientConstant, Kakeya.realRpowENN]
      rw [h4]
    have h : weight⁻¹ = ((1 / 2 : ENNReal) * density)⁻¹ := by rfl
    rw [h]
    have h2 : ((1 / 2 : ENNReal) * density)⁻¹ = (1 / 2 : ENNReal)⁻¹ * density⁻¹ := by
      rw [ENNReal.mul_inv] <;> simp [h_density_ne_zero, h_density_ne_top]
    rw [h2, h_density_inv] <;> simp
  have h_second_term_eq :
      (weight⁻¹ * (ambientConstant * cardinalityLoss * degreeConstant)) * ambientConstant =
        K_coeff_ENN * ambientConstant ^ 3 * logTerm ^ P := by
    simp [h_weight_inv, cardinalityLoss, regularizationLoss, degreeConstant, P,
      K_coeff_ENN] <;> ring
  have h_second_absorb :
      K_coeff_ENN * (ENNReal.ofReal (C_card * (1 + Real.log q⁻¹))) ^ P ≤
        Kakeya.realRpowENN q (-gap) :=
    hbound_second q hq_pos (hq_le.trans hratioCutoff_le_δ2)
  have h_log_pow_le : logTerm ^ P ≤
      (ENNReal.ofReal (C_card * (1 + Real.log q⁻¹))) ^ P := by
    gcongr
  have h_ambient_cubed : ambientConstant ^ 3 = Kakeya.realRpowENN q (-3 * inputLoss) := by
    have h_amb : ambientConstant = ENNReal.ofReal (Real.rpow q (-inputLoss)) := by
      simp [ambientConstant, Kakeya.realRpowENN]
    rw [h_amb]
    have hnonneg2 : 0 ≤ Real.rpow q (-inputLoss) := Real.rpow_nonneg hq_pos.le _
    have h7 : (ENNReal.ofReal (Real.rpow q (-inputLoss))) ^ 3 =
        ENNReal.ofReal ((Real.rpow q (-inputLoss)) ^ 3) := by
      rw [ENNReal.ofReal_pow hnonneg2]
    rw [h7]
    have h8 : (Real.rpow q (-inputLoss)) ^ 3 = Real.rpow q (-3 * inputLoss) := by
      rw [rpow_nat_pow hq_pos (-inputLoss) (3 : ℕ)]
      <;> ring_nf
    rw [h8]
    <;> simp [Kakeya.realRpowENN]
  have h_second_bound :
      K_coeff_ENN * ambientConstant ^ 3 * logTerm ^ P ≤ outputConstant := by
    calc
      K_coeff_ENN * ambientConstant ^ 3 * logTerm ^ P
        ≤ K_coeff_ENN * ambientConstant ^ 3 *
            (ENNReal.ofReal (C_card * (1 + Real.log q⁻¹))) ^ P := by gcongr
      _ = ambientConstant ^ 3 *
            (K_coeff_ENN * (ENNReal.ofReal (C_card * (1 + Real.log q⁻¹))) ^ P) := by ring
      _ ≤ ambientConstant ^ 3 * Kakeya.realRpowENN q (-gap) := by gcongr
      _ = Kakeya.realRpowENN q (-3 * inputLoss) * Kakeya.realRpowENN q (-gap) := by
          rw [h_ambient_cubed]
      _ = Kakeya.realRpowENN q (-(3 * inputLoss + gap)) := by
          have h_add : Kakeya.realRpowENN q (-3 * inputLoss) * Kakeya.realRpowENN q (-gap) =
              Kakeya.realRpowENN q ((-3 * inputLoss) + (-gap)) := by
            exact (realRpowENN_add hq_pos (-3 * inputLoss) (-gap)).symm
          rw [h_add]
          have h_eq : (-3 * inputLoss) + (-gap) = -(3 * inputLoss + gap) := by ring
          rw [h_eq]
      _ = outputConstant := by
          have h4 : 3 * inputLoss + gap = targetLoss := by linarith [hgap_eq]
          rw [h4] <;> rfl
  have h_degree_absorb :
      K_deg_ENN * (ENNReal.ofReal (C_card * (1 + Real.log q⁻¹))) ^ (levelCount + 1) ≤
        outputConstant :=
    hbound_degree q hq_pos (hq_le.trans hratioCutoff_le_δ3)
  have h_degree_log_pow_le : logTerm ^ (levelCount + 1) ≤
      (ENNReal.ofReal (C_card * (1 + Real.log q⁻¹))) ^ (levelCount + 1) := by
    gcongr
  have h_degree_bound : degreeConstant ≤ outputConstant := by
    calc
      degreeConstant
        = K_deg_ENN * logTerm ^ (levelCount + 1) := by
          simp [degreeConstant, K_deg_ENN] <;> ring
      _ ≤ K_deg_ENN * (ENNReal.ofReal (C_card * (1 + Real.log q⁻¹))) ^ (levelCount + 1) := by
          gcongr
      _ ≤ outputConstant := h_degree_absorb
  have h_second_bound' :
      (weight⁻¹ * (ambientConstant * cardinalityLoss * degreeConstant)) * ambientConstant ≤
        outputConstant := by
    rw [h_second_term_eq]
    exact h_second_bound
  have h_max : max degreeConstant
        ((weight⁻¹ * (ambientConstant * cardinalityLoss * degreeConstant)) * ambientConstant) ≤
      outputConstant := by
    exact max_le h_degree_bound h_second_bound'
  exact ⟨h_ambient_gt_two, h_ambient_ne_top, h_density_ne_zero, h_density_ne_top,
    h_scale_reach, h_two_windows, h_max⟩


end Kakeya.Assouad.PureWZ2
