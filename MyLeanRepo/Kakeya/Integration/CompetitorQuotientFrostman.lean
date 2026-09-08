import MyLeanRepo.Kakeya.Integration.CompetitorGlobalDeltaMax
import MyLeanRepo.Kakeya.Integration.CompetitorSupportingLineQuotient
import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.DilatedTubeBodyGeometry

/-!
# Frostman control for the competitor supporting-line quotient

At one competitor grid scale, a quotient assigned fiber is a disjoint union
of the original raw node classes.  Every raw class carries the competitor's
node-Frostman estimate, while every source tube is contained both in its raw
node and in the actual dilated quotient parent.  Summing the cross-multiplied
raw estimates cancels the raw-class masses and therefore pays no raw-node
cardinality.

This file proves only the ambient one-scale assigned-fiber statement.  It does
not identify assigned fibers with complete geometric fibers, and it does not
yet transfer the estimate to the common selected survivor.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Integration

open Kakeya.Streamlined

/-- Fixed container-volume loss for a supporting-line quotient parent. -/
def competitorSupportingLineQuotientFrostmanLoss : ENNReal :=
  ENNReal.ofReal (competitorSupportingLineQuotientDilation ^ 3)

lemma competitorSupportingLineQuotientFrostmanLoss_ne_top :
    competitorSupportingLineQuotientFrostmanLoss ≠ ⊤ :=
  ENNReal.ofReal_ne_top

namespace CompetitorStickyInput
namespace OneScaleSupportingLineQuotientPackage

variable {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
  {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}
  {input :
    CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius}
  {hN : 0 < N} {hdelta : 0 < delta} {hdeltaOne : delta ≤ 1}
  {hsourceBall : input.source.IsInUnitBall}
  {k : ℕ} {hk : k ≤ N}

/--
The ambient supporting-line quotient has assigned-fiber Frostman control with
one fixed geometric volume loss.  The coefficient is independent of the
runtime family, the number of raw occupied nodes, and their longitudinal
stacking multiplicity.
-/
theorem quotientCover_assignedFrostman
    (package :
      input.OneScaleSupportingLineQuotientPackage
        hN hdelta hdeltaOne hsourceBall k hk) :
    package.quotientCover.toFactoring.FibersAreCFrostman
      (competitorSupportingLineQuotientFrostmanLoss * frostmanConstant) := by
  let rho : ℝ := (Tube.gridScale delta N k : ℝ)
  have hrho : 0 < rho := by
    exact_mod_cast Tube.gridScale_pos hdelta N k
  apply Factoring.regroup_frostman_of_common_middle_volume
      (P₁ := (input.levelStrictCover hk).toFactoring)
      (Q := package.quotientCover.toFactoring)
      (group := package.rawParentToQuotient)
      (C := frostmanConstant)
      (Cvol := competitorSupportingLineQuotientFrostmanLoss)
      (Vmid := Kakeya.deltaTubeVolume rho)
  · intro sourceIndex
    exact
      (package.rawParentToQuotient_rawParentOfSource sourceIndex).symm
  · exact input.levelStrictCover_assignedFrostman hk
  · exact GeometricLemmas.tubeFamily_bodies_convex (input.levelCoarse k)
  · intro rawParent
    exact RandomTranslation.tube_volume_eq_deltaTubeVolume
      ((input.levelCoarse k).tube rawParent)
  · intro quotientParent
    change
      volume
          (dilatedTubeCarrier competitorSupportingLineQuotientDilation
            (package.quotientCoarse.tube quotientParent)) ≤
        competitorSupportingLineQuotientFrostmanLoss *
          Kakeya.deltaTubeVolume rho
    rw [volume_dilatedTubeCarrier_of_pos hrho
      (by norm_num [competitorSupportingLineQuotientDilation,
        competitorSupportingLineCellDilation, composedDilatedCoverDilation])
      (package.quotientCoarse.tube quotientParent)]
    rw [RandomTranslation.tube_volume_eq_deltaTubeVolume]
    exact le_rfl

end OneScaleSupportingLineQuotientPackage
end CompetitorStickyInput
end Kakeya.Integration

end
