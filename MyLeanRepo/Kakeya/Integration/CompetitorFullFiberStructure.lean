import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConcreteABI
import MyLeanRepo.Kakeya.Integration.CompetitorFiniteQuotientSelection

/-!
# Competitor all-real hierarchy to the pure WZ2 full-fiber ABI

This file packages the all-real output of the one-common-survivor competitor
construction as the complete-containment-fiber structure consumed by the
reanchored pure WZ2 Node 9.  The common coefficient is the maximum of the
actual all-real full-fiber uniformity and the proved complete-fiber Frostman
coefficient.

No assigned fiber is identified with a complete geometric fiber here.  The
Frostman input is exactly the assigned-to-complete transfer proved in
`CompetitorFiniteQuotientSelection`.
-/

noncomputable section

namespace Kakeya.Integration

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace CompetitorStickyInput.FiniteQuotientSelectionPackage

variable {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
  {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}
  {input :
    CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius}
  {hN : 0 < N} {hdelta : 0 < delta} {hdeltaOne : delta ≤ 1}
  {hsourceBall : input.source.IsInUnitBall}
  (selection :
    input.FiniteQuotientSelectionPackage
      hN hdelta hdeltaOne hsourceBall)

/-- The explicit complete-fiber Frostman coefficient of the all-real output. -/
def allRealFullContainmentFrostmanCoefficient
    (package : selection.AllRealPackage) : ENNReal :=
  fullContainmentBranchingLoss
      (dominatingUpperFromDilatedCoverDilation
        competitorSupportingLineQuotientDilation)
      package.outputDilation_one *
    ((allScaleBalancedFromDilatedCoverDegreeFactor
      (competitorFiniteQuotientDegree
        delta N hN hdelta hdeltaOne) : ℕ) : ENNReal) *
    competitorFiniteQuotientUniformity N input.source.card *
    (allScaleAssignedFrostmanTransportLoss
        competitorSupportingLineQuotientDilation
        (reverseGridK delta N) *
      (competitorFiniteQuotientFiberRetentionLoss
          lambda N input.source.card *
        (competitorSupportingLineQuotientFrostmanLoss *
          frostmanConstant)))

/-- One coefficient controls both complete-fiber cardinality and complete-
fiber Frostman concentration. -/
def allRealFullFiberCoefficient
    (package : selection.AllRealPackage) : ENNReal :=
  max package.uts.uniformity
    (selection.allRealFullContainmentFrostmanCoefficient package)

/-- The complete-fiber coefficient is the actual all-real full-fiber
uniformity times the four remaining Frostman transport factors. -/
lemma allRealFullContainmentFrostmanCoefficient_eq
    (package : selection.AllRealPackage) :
    selection.allRealFullContainmentFrostmanCoefficient package =
      package.uts.uniformity *
        allScaleAssignedFrostmanTransportLoss
          competitorSupportingLineQuotientDilation
          (reverseGridK delta N) *
        competitorFiniteQuotientFiberRetentionLoss
          lambda N input.source.card *
        competitorSupportingLineQuotientFrostmanLoss *
        frostmanConstant := by
  rw [package.uniformity_eq]
  unfold allRealFullContainmentFrostmanCoefficient
  ring

/-- The restricted shading on the one common selected source remains dense
after paying exactly the one-shot weighted-selection loss. -/
lemma selectedShading_isLambdaDense
    (hlambda : 0 < lambda) :
    (selection.selectedFine.restrictShading input.sourceShading).IsLambdaDense
      (lambda *
        (competitorFiniteQuotientWeightLoss
          N input.source.card)⁻¹) := by
  let loss := competitorFiniteQuotientWeightLoss N input.source.card
  have hlossZero : loss ≠ 0 := by
    simp [loss, competitorFiniteQuotientWeightLoss,
      weightedFiniteCoordinateFiberCoreWeightLoss,
      parentComponentColorCount,
      weightedFiniteCoordinateFiberCoreBinCount]
  have hlossTop : loss ≠ ⊤ := by
    unfold loss competitorFiniteQuotientWeightLoss
      weightedFiniteCoordinateFiberCoreWeightLoss
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by simp))
      ENNReal.coe_ne_top
  have hselectedMass :
      loss⁻¹ * input.sourceShading.mass ≤
        (selection.selectedFine.restrictShading input.sourceShading).mass := by
    calc
      loss⁻¹ * input.sourceShading.mass
          ≤ loss⁻¹ *
              (loss *
                (selection.selectedFine.restrictShading
                  input.sourceShading).mass) := by
            gcongr
            exact selection.shadingRetention
      _ = (selection.selectedFine.restrictShading
              input.sourceShading).mass := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hlossZero hlossTop, one_mul]
  have hsourceDense :
      input.sourceShading.IsLambdaDense lambda := by
    have hsourceNonempty : input.s.Nonempty := by
      apply Finset.card_pos.mp
      change 0 < input.source.card
      have hcard :
          selection.selectedFine.family.card ≤ input.source.card := by
        have h := Fintype.card_le_of_injective
          selection.selectedFine.embedding
          selection.selectedFine.embedding.injective
        simpa using h
      exact selection.selectedNonempty.trans_le hcard
    exact (competitorFullness_le_iff_isLambdaDense
      hdelta hsourceNonempty input.V lambda).1 input.fullness
  change
    (lambda * loss⁻¹) *
        selection.selectedFine.family.toBodyFamily.mass ≤
      (selection.selectedFine.restrictShading input.sourceShading).mass
  calc
    (lambda * loss⁻¹) *
          selection.selectedFine.family.toBodyFamily.mass =
        loss⁻¹ * (lambda *
          selection.selectedFine.family.toBodyFamily.mass) := by ring
    _ ≤ loss⁻¹ *
          (lambda * input.source.toBodyFamily.mass) := by
          exact mul_le_mul_left'
            (mul_le_mul_left'
              (by
                rw [selection.selectedFine.family.bodyMass_eq_nominalMass,
                  input.source.bodyMass_eq_nominalMass]
                change
                  (selection.selectedFine.family.card : ENNReal) *
                      Kakeya.deltaTubeVolume (delta : ℝ) ≤
                    (input.source.card : ENNReal) *
                      Kakeya.deltaTubeVolume (delta : ℝ)
                gcongr
                have hcard := Fintype.card_le_of_injective
                  selection.selectedFine.embedding
                  selection.selectedFine.embedding.injective
                simpa using hcard) lambda)
            loss⁻¹
    _ ≤ loss⁻¹ * input.sourceShading.mass :=
          mul_le_mul_left' hsourceDense loss⁻¹
    _ ≤ (selection.selectedFine.restrictShading
          input.sourceShading).mass := hselectedMass

lemma one_le_allRealFullFiberCoefficient
    (package : selection.AllRealPackage) :
    1 ≤ selection.allRealFullFiberCoefficient package :=
  package.uts.one_le_uniformity.trans (le_max_left _ _)

lemma uniformity_le_allRealFullFiberCoefficient
    (package : selection.AllRealPackage) :
    package.uts.uniformity ≤
      selection.allRealFullFiberCoefficient package :=
  le_max_left _ _

lemma frostmanCoefficient_le_allRealFullFiberCoefficient
    (package : selection.AllRealPackage) :
    selection.allRealFullContainmentFrostmanCoefficient package ≤
      selection.allRealFullFiberCoefficient package :=
  le_max_right _ _

lemma allRealFullContainmentFrostmanCoefficient_ne_top
    (hlambda : 0 < lambda)
    (hfrostmanConstantTop : frostmanConstant ≠ ⊤)
    (package : selection.AllRealPackage) :
    selection.allRealFullContainmentFrostmanCoefficient package ≠ ⊤ := by
  have hbranch :
      fullContainmentBranchingLoss
          (dominatingUpperFromDilatedCoverDilation
            competitorSupportingLineQuotientDilation)
          package.outputDilation_one ≠ ⊤ :=
    fullContainmentBranchingLoss_ne_top _ _
  have hdegree :
      (((allScaleBalancedFromDilatedCoverDegreeFactor
        (competitorFiniteQuotientDegree
          delta N hN hdelta hdeltaOne) : ℕ) : ENNReal)) ≠ ⊤ := by
    simp
  have huniformity :
      competitorFiniteQuotientUniformity N input.source.card ≠ ⊤ := by
    exact weightedFiniteCoordinateFiberCoreUniformity_ne_top _ _
  have htransport :
      allScaleAssignedFrostmanTransportLoss
          competitorSupportingLineQuotientDilation
          (reverseGridK delta N) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hweight :
      competitorFiniteQuotientWeightLoss N input.source.card ≠ ⊤ := by
    unfold competitorFiniteQuotientWeightLoss
      weightedFiniteCoordinateFiberCoreWeightLoss
    have htwo : (2 : ENNReal) ≠ ⊤ := by norm_num
    have hbin :
        ((weightedFiniteCoordinateFiberCoreBinCount
          input.source.card : ℕ) : ENNReal) ≠ ⊤ := by
      simp
    have hcolor :
        (((8 * parentComponentColorCount N
          (weightedFiniteCoordinateFiberCoreBinCount
            input.source.card ^ 2) : ℕ) : ENNReal)) ≠ ⊤ := by
      exact ENNReal.coe_ne_top
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top htwo hbin) hcolor
  have hretention :
      competitorFiniteQuotientFiberRetentionLoss
          lambda N input.source.card ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top
          (ENNReal.inv_ne_top.mpr hlambda.ne') hweight))
      huniformity
  have hquotient :
      competitorSupportingLineQuotientFrostmanLoss ≠ ⊤ :=
    competitorSupportingLineQuotientFrostmanLoss_ne_top
  unfold allRealFullContainmentFrostmanCoefficient
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hbranch hdegree) huniformity)
    (ENNReal.mul_ne_top htransport
      (ENNReal.mul_ne_top hretention
        (ENNReal.mul_ne_top hquotient hfrostmanConstantTop)))

lemma allRealFullFiberCoefficient_ne_top
    (hlambda : 0 < lambda)
    (hfrostmanConstantTop : frostmanConstant ≠ ⊤)
    (package : selection.AllRealPackage) :
    selection.allRealFullFiberCoefficient package ≠ ⊤ :=
  max_ne_top package.uts.uniformity_ne_top
    (selection.allRealFullContainmentFrostmanCoefficient_ne_top
      hlambda hfrostmanConstantTop package)

/-- The all-real competitor output, on the unchanged selected source witness,
is exactly a full-fiber structure accepted by the reanchored pure WZ2 ABI. -/
theorem allReal_pureWZ2GWZFullFiberStructure
    (hdeltaStrict : delta < 1)
    (hlambda : 0 < lambda)
    (hfrostmanConstantTop : frostmanConstant ≠ ⊤)
    (package : selection.AllRealPackage) :
    Kakeya.Assouad.PureWZ2GWZFullFiberStructure
      (A := dominatingUpperFromDilatedCoverDilation
        competitorSupportingLineQuotientDilation)
      selection.selectedFine.family
      (selection.allRealFullFiberCoefficient package) := by
  apply
    Kakeya.Assouad.pureWZ2GWZFullFiberStructure_of_dilatedUniformTubeStructure
      (by exact_mod_cast hdelta)
      (lt_of_lt_of_le zero_lt_one package.outputDilation_one)
      package.uts.toDilatedUniformTubeStructure
      (selection.uniformity_le_allRealFullFiberCoefficient package)
      _
      (selection.allRealFullFiberCoefficient_ne_top
        hlambda hfrostmanConstantTop package)
  intro rho parent
  exact
    (selection.allReal_fullContainmentFrostman
      hdeltaStrict package rho parent).trans
        (selection.frostmanCoefficient_le_allRealFullFiberCoefficient package)

/-- Once the explicit competitor coefficient has been paid by the requested
power, the same selected hierarchy has the exact coefficient required by
Node 9. -/
theorem allReal_pureWZ2GWZFullFiberStructure_of_coefficient_le
    (hdeltaStrict : delta < 1)
    (hlambda : 0 < lambda)
    (hfrostmanConstantTop : frostmanConstant ≠ ⊤)
    (package : selection.AllRealPackage)
    {inputLoss : ℝ}
    (hcoefficient :
      selection.allRealFullFiberCoefficient package ≤
        Kakeya.realRpowENN (delta : ℝ) (-inputLoss)) :
    Kakeya.Assouad.PureWZ2GWZFullFiberStructure
      (A := dominatingUpperFromDilatedCoverDilation
        competitorSupportingLineQuotientDilation)
      selection.selectedFine.family
      (Kakeya.realRpowENN (delta : ℝ) (-inputLoss)) := by
  exact
    (selection.allReal_pureWZ2GWZFullFiberStructure
      hdeltaStrict hlambda hfrostmanConstantTop package).mono
        hcoefficient (by simp [Kakeya.realRpowENN])

end CompetitorStickyInput.FiniteQuotientSelectionPackage

end Kakeya.Integration

end
