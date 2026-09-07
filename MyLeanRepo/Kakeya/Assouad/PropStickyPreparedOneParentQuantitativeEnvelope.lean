import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentQuantitativeEnvelopeStatements
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-! # Bound all prepared one-parent constants uniformly -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_prop_sticky_prepared_one_parent_quantitative_envelope :
    WZ2PropStickyPreparedOneParentQuantitativeEnvelopeStatement := by
  intro delta sourceLoss stableLoss hdelta hdeltaOne hstableLoss
    hsourceStable source shading caller preparationExponent prepared parent
    selection quantitative
  dsimp only
  let depth : ℕ := wz2PaperPreparedOneParentDepth sourceLoss
  let finiteLoss : ENNReal :=
    wz2PaperPreparedOneParentFiniteLoss sourceLoss
  let geometry : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  let ambient : ENNReal :=
    Kakeya.realRpowENN delta (-stableLoss)
  let retained : ENNReal := quantitative.massRetentionConstant
  let cardinalityLoss : ENNReal :=
    quantitative.cardinalityRetentionConstant
  let selectedConstant : ENNReal :=
    quantitative.selectedUniformConstant
  let restrictedConstant : ENNReal :=
    max 1
      (max selectedConstant
        ((quantitative.weight⁻¹ *
            (prepared.structuralConstant *
              cardinalityLoss * selectedConstant)) *
          prepared.structuralConstant))
  let rootConstant : ENNReal :=
    max 1
      ((quantitative.weight⁻¹ * cardinalityLoss) *
        prepared.structuralConstant)
  let coefficient : ENNReal :=
    max 1
      (max
        (4 * finiteLoss * geometry)
        (8 * (finiteLoss * geometry) ^ 2))
  let bound : ENNReal :=
    (81000000 : ENNReal) * coefficient *
      Kakeya.realRpowENN delta (-5 * stableLoss)
  have hdepth :
      wz2PaperPreparedOneParentFineScaleCount prepared parent ≤ depth := by
    dsimp only [wz2PaperPreparedOneParentFineScaleCount, depth,
      wz2PaperPreparedOneParentDepth]
    calc
      prepared.strictScaleCount - prepared.callerLevel.val ≤
          prepared.strictScaleCount := Nat.sub_le _ _
      _ ≤ prepared.levelCount + 1 := prepared.strictScaleCount_le
      _ = Nat.ceil (1 / sourceLoss) + 2 := by
        rw [prepared.levelCount_eq]
  have hfinite :
      retained ≤ finiteLoss := by
    dsimp only [retained]
    rw [quantitative.massRetentionConstant_eq]
    dsimp only [finiteLoss, wz2PaperPreparedOneParentFiniteLoss]
    gcongr
    exact (by norm_num : (1 : ENNReal) ≤ 2)
  have hcardinality :
      cardinalityLoss ≤ finiteLoss * geometry := by
    dsimp only [cardinalityLoss]
    rw [quantitative.cardinalityRetentionConstant_eq]
    simpa [retained, geometry] using
      mul_le_mul_right' hfinite geometry
  have hambientOne : 1 ≤ ambient :=
    middleConstant_ge_one hdelta hdeltaOne hstableLoss
  have hstructural :
      prepared.structuralConstant ≤ ambient := by
    rw [prepared.structuralConstant_eq]
    exact
      realRpowENN_antitone hdelta hdeltaOne
        (by
          have := prepared.structuralLoss_le_stable
          linarith)
  have hsourceAmbient :
      Kakeya.realRpowENN delta (-sourceLoss) ≤ ambient := by
    exact
      realRpowENN_antitone hdelta hdeltaOne
        (by linarith)
  have hweightInv :
      quantitative.weight⁻¹ =
        2 * Kakeya.realRpowENN delta (-sourceLoss) := by
    rw [quantitative.weight_eq]
    have hdensityPos :
        0 < Real.rpow delta sourceLoss :=
      Real.rpow_pos_of_pos hdelta _
    have hdensityInv :
        (Kakeya.realRpowENN delta sourceLoss)⁻¹ =
          Kakeya.realRpowENN delta (-sourceLoss) := by
      simp only [Kakeya.realRpowENN]
      calc
        (ENNReal.ofReal (Real.rpow delta sourceLoss))⁻¹ =
            ENNReal.ofReal
              ((Real.rpow delta sourceLoss)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos hdensityPos).symm
        _ = ENNReal.ofReal
              (Real.rpow delta (-sourceLoss)) := by
          exact congrArg ENNReal.ofReal
            (Real.rpow_neg hdelta.le sourceLoss).symm
    rw [ENNReal.mul_inv
      (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
    rw [hdensityInv]
    norm_num
  have hweight :
      quantitative.weight⁻¹ ≤ 2 * ambient := by
    rw [hweightInv]
    gcongr
  have hscaleZero :
      Kakeya.realRpowENN delta 2 ≠ 0 := by
    exact
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hdelta 2)).ne'
  have hscaleTop :
      Kakeya.realRpowENN delta 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hselectedEq :
      selectedConstant =
        4 * Kakeya.realRpowENN delta (-sourceLoss) *
          prepared.structuralConstant * retained * geometry := by
    dsimp only [selectedConstant]
    rw [quantitative.selectedUniformConstant_eq]
    have hfirstInv :
        ((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss *
            Kakeya.realRpowENN delta 2)⁻¹ =
          (2 * Kakeya.realRpowENN delta (-sourceLoss)) *
            (Kakeya.realRpowENN delta 2)⁻¹ := by
      rw [ENNReal.mul_inv
        (Or.inr hscaleTop)
        (Or.inr hscaleZero)]
      have hhalf :
          ((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta sourceLoss)⁻¹ =
            2 * Kakeya.realRpowENN delta (-sourceLoss) := by
        rw [ENNReal.mul_inv
          (Or.inl (by norm_num))
          (Or.inl (by norm_num))]
        have hdensityInv' :
            (Kakeya.realRpowENN delta sourceLoss)⁻¹ =
              Kakeya.realRpowENN delta (-sourceLoss) := by
          have hdensityPos :
              0 < Real.rpow delta sourceLoss :=
            Real.rpow_pos_of_pos hdelta _
          simp only [Kakeya.realRpowENN]
          calc
            (ENNReal.ofReal (Real.rpow delta sourceLoss))⁻¹ =
                ENNReal.ofReal
                  ((Real.rpow delta sourceLoss)⁻¹) :=
              (ENNReal.ofReal_inv_of_pos hdensityPos).symm
            _ = ENNReal.ofReal
                  (Real.rpow delta (-sourceLoss)) := by
              exact congrArg ENNReal.ofReal
                (Real.rpow_neg hdelta.le sourceLoss).symm
        rw [hdensityInv']
        norm_num
      rw [hhalf]
    rw [hfirstInv]
    calc
      (2 * Kakeya.realRpowENN delta (-sourceLoss) *
              (Kakeya.realRpowENN delta 2)⁻¹) *
            (2 * prepared.structuralConstant * retained *
              (geometry * Kakeya.realRpowENN delta 2)) =
          (4 * Kakeya.realRpowENN delta (-sourceLoss) *
              prepared.structuralConstant * retained * geometry) *
            (Kakeya.realRpowENN delta 2)⁻¹ *
              Kakeya.realRpowENN delta 2 := by ring
      _ =
          4 * Kakeya.realRpowENN delta (-sourceLoss) *
            prepared.structuralConstant * retained * geometry :=
        ENNReal.inv_mul_cancel_right hscaleZero hscaleTop
  have hselected :
      selectedConstant ≤
        (4 * finiteLoss * geometry) * ambient ^ 2 := by
    rw [hselectedEq]
    calc
      4 * Kakeya.realRpowENN delta (-sourceLoss) *
            prepared.structuralConstant * retained * geometry ≤
          4 * ambient * ambient * finiteLoss * geometry := by
        gcongr
      _ = (4 * finiteLoss * geometry) * ambient ^ 2 := by ring
  have hrootTerm :
      (quantitative.weight⁻¹ * cardinalityLoss) *
          prepared.structuralConstant ≤
        (2 * finiteLoss * geometry) * ambient ^ 2 := by
    calc
      (quantitative.weight⁻¹ * cardinalityLoss) *
            prepared.structuralConstant ≤
          ((2 * ambient) * (finiteLoss * geometry)) * ambient := by
        gcongr
      _ = (2 * finiteLoss * geometry) * ambient ^ 2 := by ring
  have hrestrictedTerm :
      (quantitative.weight⁻¹ *
          (prepared.structuralConstant *
            cardinalityLoss * selectedConstant)) *
        prepared.structuralConstant ≤
      (8 * (finiteLoss * geometry) ^ 2) * ambient ^ 5 := by
    calc
      (quantitative.weight⁻¹ *
            (prepared.structuralConstant *
              cardinalityLoss * selectedConstant)) *
          prepared.structuralConstant ≤
        ((2 * ambient) *
            (ambient * (finiteLoss * geometry) *
              ((4 * finiteLoss * geometry) * ambient ^ 2))) *
          ambient := by
        gcongr
      _ =
        (8 * (finiteLoss * geometry) ^ 2) * ambient ^ 5 := by ring
  have hambientTwoFive : ambient ^ 2 ≤ ambient ^ 5 := by
    exact pow_le_pow_right₀ hambientOne (by omega)
  have hambientOneFive : ambient ≤ ambient ^ 5 := by
    calc
      ambient = ambient ^ 1 := by simp
      _ ≤ ambient ^ 5 := pow_le_pow_right₀ hambientOne (by omega)
  have hcoefficientOne : 1 ≤ coefficient := by
    exact le_max_left _ _
  have hcoefficientFirst :
      4 * finiteLoss * geometry ≤ coefficient := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hcoefficientSecond :
      8 * (finiteLoss * geometry) ^ 2 ≤ coefficient := by
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hambientPow :
      ambient ^ 5 =
        Kakeya.realRpowENN delta (-5 * stableLoss) := by
    dsimp only [ambient, Kakeya.realRpowENN]
    have hnonneg :
        0 ≤ Real.rpow delta (-stableLoss) :=
      Real.rpow_nonneg hdelta.le _
    rw [← ENNReal.ofReal_pow hnonneg]
    rw [rpow_nat_pow hdelta (-stableLoss) 5]
    ring_nf
  have hrootNested :
      (81000000 : ENNReal) * rootConstant ≤ bound := by
    have hinside :
        rootConstant ≤ coefficient * ambient ^ 5 := by
      dsimp only [rootConstant]
      apply max_le
      · calc
          (1 : ENNReal) ≤ ambient ^ 5 :=
            one_le_pow₀ hambientOne
          _ ≤ coefficient * ambient ^ 5 := by
            simpa using
              mul_le_mul_right' hcoefficientOne (ambient ^ 5)
      · calc
          (quantitative.weight⁻¹ * cardinalityLoss) *
                prepared.structuralConstant ≤
              (2 * finiteLoss * geometry) * ambient ^ 2 :=
            hrootTerm
          _ ≤ (4 * finiteLoss * geometry) * ambient ^ 5 := by
            gcongr <;> norm_num
          _ ≤ coefficient * ambient ^ 5 := by
            exact mul_le_mul_right' hcoefficientFirst _
    calc
      (81000000 : ENNReal) * rootConstant ≤
          81000000 * (coefficient * ambient ^ 5) := by
        gcongr
      _ = bound := by
        dsimp only [bound,
          wz2PaperPreparedOneParentEnvelope]
        rw [hambientPow]
        ring
  have hrestrictedNested :
      (81000000 : ENNReal) * restrictedConstant ≤ bound := by
    have hinside :
        restrictedConstant ≤ coefficient * ambient ^ 5 := by
      dsimp only [restrictedConstant]
      apply max_le
      · calc
          (1 : ENNReal) ≤ ambient ^ 5 :=
            one_le_pow₀ hambientOne
          _ ≤ coefficient * ambient ^ 5 := by
            simpa using
              mul_le_mul_right' hcoefficientOne (ambient ^ 5)
      · apply max_le
        · calc
            selectedConstant ≤
                (4 * finiteLoss * geometry) * ambient ^ 2 :=
              hselected
            _ ≤ (4 * finiteLoss * geometry) * ambient ^ 5 := by
              gcongr
            _ ≤ coefficient * ambient ^ 5 := by
              exact mul_le_mul_right' hcoefficientFirst _
        · calc
            (quantitative.weight⁻¹ *
                  (prepared.structuralConstant *
                    cardinalityLoss * selectedConstant)) *
                prepared.structuralConstant ≤
              (8 * (finiteLoss * geometry) ^ 2) * ambient ^ 5 :=
                hrestrictedTerm
            _ ≤ coefficient * ambient ^ 5 := by
              exact mul_le_mul_right' hcoefficientSecond _
    calc
      (81000000 : ENNReal) * restrictedConstant ≤
          81000000 * (coefficient * ambient ^ 5) := by
        gcongr
      _ = bound := by
        dsimp only [bound,
          wz2PaperPreparedOneParentEnvelope]
        rw [hambientPow]
        ring
  have hprepared :
      (200 : ENNReal) * prepared.structuralConstant ≤ bound := by
    calc
      (200 : ENNReal) * prepared.structuralConstant ≤
          (81000000 : ENNReal) * ambient := by
        gcongr <;> norm_num
      _ ≤ (81000000 : ENNReal) *
          (coefficient * ambient ^ 5) := by
        gcongr
        calc
          ambient ≤ 1 * ambient ^ 5 := by
            simpa using hambientOneFive
          _ ≤ coefficient * ambient ^ 5 := by
            exact mul_le_mul_right' hcoefficientOne _
      _ = bound := by
        dsimp only [bound,
          wz2PaperPreparedOneParentEnvelope]
        rw [hambientPow]
        ring
  have hroot :
      (1000000 : ENNReal) * rootConstant ≤ bound := by
    exact
      (mul_le_mul_right'
        (by norm_num : (1000000 : ENNReal) ≤ 81000000)
        rootConstant).trans hrootNested
  have hrestricted :
      (1000000 : ENNReal) * restrictedConstant ≤ bound := by
    exact
      (mul_le_mul_right'
        (by norm_num : (1000000 : ENNReal) ≤ 81000000)
        restrictedConstant).trans hrestrictedNested
  simpa [restrictedConstant, rootConstant, cardinalityLoss,
    selectedConstant, retained, bound, ambient,
    finiteLoss, geometry, coefficient,
    wz2PaperPreparedOneParentEnvelope] using
    And.intro hroot
      (And.intro hrestricted
        (And.intro hrestrictedNested hprepared))

end Kakeya.Assouad

end
