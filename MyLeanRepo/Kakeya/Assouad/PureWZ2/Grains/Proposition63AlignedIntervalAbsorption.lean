import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedInnerIntervalGrid
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Family-free absorption for aligned ordered-pair interval bounds

Upward alignment of the lower interval scale costs a factor two when the
cover is transported back to the logical grid scale.  This file spends a
strictly smaller internal loss to absorb that factor before any runtime
family is chosen, and records the monotone transport of the ratio power.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- A family-free loss choice and small-scale threshold absorbing the fixed
factor two introduced by aligned-resolution refinement. -/
structure Proposition63AlignedIntervalAbsorptionData
    (discreteLoss : ℝ) where
  internalLoss : ℝ
  internal_loss_eq : internalLoss = discreteLoss / 2
  internal_loss_pos : 0 < internalLoss
  internal_loss_lt : internalLoss < discreteLoss
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb_two : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    2 * Kakeya.realRpowENN delta (-internalLoss) ≤
      Kakeya.realRpowENN delta (-discreteLoss)

/-- Choose half of the available discrete loss and absorb the alignment cost
two at a family-independent threshold. -/
theorem proposition63_aligned_interval_absorption
    {discreteLoss : ℝ} (hdiscreteLoss : 0 < discreteLoss) :
    Nonempty (Proposition63AlignedIntervalAbsorptionData discreteLoss) := by
  let internalLoss := discreteLoss / 2
  have hinternalPos : 0 < internalLoss := by
    dsimp only [internalLoss]
    linarith
  have hinternalLt : internalLoss < discreteLoss := by
    dsimp only [internalLoss]
    linarith
  have hgap : 0 < discreteLoss - internalLoss := by linarith
  rcases exists_delta_realRpowENN_bound (2 : ENNReal) (by norm_num) hgap with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, htwo⟩
  refine ⟨⟨internalLoss, rfl, hinternalPos, hinternalLt, delta₀, hdelta₀Pos,
    hdelta₀One, ?_⟩⟩
  intro delta hdelta hsmall
  have htwo' := htwo delta hdelta hsmall
  calc
    2 * Kakeya.realRpowENN delta (-internalLoss) ≤
        Kakeya.realRpowENN delta (-(discreteLoss - internalLoss)) *
          Kakeya.realRpowENN delta (-internalLoss) := by
      gcongr
    _ = Kakeya.realRpowENN delta (-discreteLoss) := by
      rw [← realRpowENN_add hdelta]
      congr 1
      ring

/-- Enlarging the denominator from the logical scale to its aligned surrogate
can only decrease the nonnegative paper ratio power. -/
theorem proposition63_aligned_ratio_power_le_logical
    {logicalR rhoHat tau exponent : ℝ}
    (hlogicalR : 0 < logicalR)
    (hlogicalR_le : logicalR ≤ rhoHat)
    (htau : 0 ≤ tau)
    (hexponent : 0 ≤ exponent) :
    Kakeya.realRpowENN (tau / rhoHat) exponent ≤
      Kakeya.realRpowENN (tau / logicalR) exponent := by
  have hratio : tau / rhoHat ≤ tau / logicalR :=
    div_le_div_of_nonneg_left htau hlogicalR hlogicalR_le
  simp only [Kakeya.realRpowENN]
  exact ENNReal.ofReal_mono
    (Real.rpow_le_rpow (div_nonneg htau (hlogicalR.trans_le hlogicalR_le).le)
      hratio hexponent)

/-- Absorb the aligned-resolution factor two and transport the internal paper
constant from `rhoHat` to the smaller logical resolution. -/
theorem proposition63_two_internal_paper_constant_le_logical
    {delta internalLoss discreteLoss logicalR rhoHat tau exponent : ℝ}
    (absorption : Proposition63AlignedIntervalAbsorptionData discreteLoss)
    (hinternalLoss : internalLoss = absorption.internalLoss)
    (hdelta : 0 < delta)
    (hsmall : delta ≤ absorption.delta₀)
    (hlogicalR : 0 < logicalR)
    (hlogicalR_le : logicalR ≤ rhoHat)
    (htau : 0 ≤ tau)
    (hexponent : 0 ≤ exponent) :
    2 * ENNReal.ofReal
        (Real.rpow delta (-internalLoss) *
          Real.rpow (tau / rhoHat) exponent) ≤
      ENNReal.ofReal
        (Real.rpow delta (-discreteLoss) *
          Real.rpow (tau / logicalR) exponent) := by
  subst internalLoss
  have htwo := absorption.absorb_two hdelta hsmall
  have hratio := proposition63_aligned_ratio_power_le_logical
    hlogicalR hlogicalR_le htau hexponent
  have hinternalMul : ENNReal.ofReal
      (Real.rpow delta (-absorption.internalLoss) *
        Real.rpow (tau / rhoHat) exponent) =
      Kakeya.realRpowENN delta (-absorption.internalLoss) *
        Kakeya.realRpowENN (tau / rhoHat) exponent :=
    ENNReal.ofReal_mul (Real.rpow_nonneg hdelta.le _)
  have hdiscreteMul : ENNReal.ofReal
      (Real.rpow delta (-discreteLoss) *
        Real.rpow (tau / logicalR) exponent) =
      Kakeya.realRpowENN delta (-discreteLoss) *
        Kakeya.realRpowENN (tau / logicalR) exponent :=
    ENNReal.ofReal_mul (Real.rpow_nonneg hdelta.le _)
  rw [hinternalMul, hdiscreteMul]
  change 2 *
      (Kakeya.realRpowENN delta (-absorption.internalLoss) *
        Kakeya.realRpowENN (tau / rhoHat) exponent) ≤
    Kakeya.realRpowENN delta (-discreteLoss) *
      Kakeya.realRpowENN (tau / logicalR) exponent
  calc
    2 *
        (Kakeya.realRpowENN delta (-absorption.internalLoss) *
          Kakeya.realRpowENN (tau / rhoHat) exponent) =
      (2 * Kakeya.realRpowENN delta (-absorption.internalLoss)) *
        Kakeya.realRpowENN (tau / rhoHat) exponent := by ring
    _ ≤ Kakeya.realRpowENN delta (-discreteLoss) *
        Kakeya.realRpowENN (tau / logicalR) exponent :=
      mul_le_mul htwo hratio (by positivity) (by positivity)

/-- Direct callback receipt: any internal constant bounded by the internal
paper expression is, after the aligned-resolution factor two, bounded by the
logical ordered-pair expression. -/
theorem proposition63_aligned_internal_constant_le_logical
    {delta internalLoss discreteLoss logicalR rhoHat tau sigma : ℝ}
    (absorption : Proposition63AlignedIntervalAbsorptionData discreteLoss)
    (hinternalLoss : internalLoss = absorption.internalLoss)
    (hdelta : 0 < delta)
    (hsmall : delta ≤ absorption.delta₀)
    (hlogicalR : 0 < logicalR)
    (hlogicalR_le : logicalR ≤ rhoHat)
    (htau : 0 ≤ tau)
    (hexponent : 0 ≤ 1 - sigma)
    {internalConstant : ENNReal}
    (hinternal : internalConstant ≤ ENNReal.ofReal
      (Real.rpow delta (-internalLoss) *
        Real.rpow (tau / rhoHat) (1 - sigma))) :
    2 * internalConstant ≤ ENNReal.ofReal
      (Real.rpow delta (-discreteLoss) *
        Real.rpow (tau / logicalR) (1 - sigma)) := by
  apply le_trans (b := 2 * ENNReal.ofReal
    (Real.rpow delta (-internalLoss) *
      Real.rpow (tau / rhoHat) (1 - sigma)))
  · gcongr
  · exact proposition63_two_internal_paper_constant_le_logical absorption
      hinternalLoss hdelta hsmall hlogicalR hlogicalR_le htau hexponent

/-- Grid-specialized form whose conclusion unfolds to the scalar bound used
by the ordered-pair callback. -/
theorem proposition63_aligned_internal_constant_le_ordered_pair_expression
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN index : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (absorption : Proposition63AlignedIntervalAbsorptionData discreteLoss)
    {rhoHat tau : ℝ}
    (hdelta : 0 < delta)
    (hsmall : delta ≤ absorption.delta₀)
    (hlogicalR : 0 <
      (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
    (hlogicalR_le :
      (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤ rhoHat)
    (htau : tau =
      (grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ))
    (htauNonnegative : 0 ≤ tau)
    (hsigma : 0 ≤ 1 - sigma)
    {internalConstant : ENNReal}
    (hinternal : internalConstant ≤ ENNReal.ofReal
      (Real.rpow delta (-absorption.internalLoss) *
        Real.rpow (tau / rhoHat) (1 - sigma))) :
    2 * internalConstant ≤ ENNReal.ofReal
      (Real.rpow delta (-discreteLoss) *
        Real.rpow
          ((grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ) /
            (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
          (1 - sigma)) := by
  have hbound := proposition63_aligned_internal_constant_le_logical
    absorption rfl hdelta hsmall hlogicalR hlogicalR_le htauNonnegative
      hsigma hinternal
  simpa only [htau] using hbound

end Kakeya.Assouad.PureWZ2
