import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedParentPairIncidenceInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountAlgebra

/-!
# Tangency scale for the selected parent multiplicity

The heavy-parent threshold compares `M_parent * q_fiber` with the selected
edge mass below one parent.  Parentwise incidence-fiber regularization and the
good-pair double count supply the other hypotheses of the closed tangency
algebra.  The selected support cardinality is below `2 * l_coarse`, so the
resulting factor `4` remains explicit in the incidence scale.
-/

namespace Kakeya.Cinematic

noncomputable def ambientRestrictedParentTangencyScale
    (incidenceScale fiberCoefficient : ℝ)
    (degreeLoss : ℕ)
    (heavyLogLoss retention : ℝ) : ℝ :=
  5184 * (4 * incidenceScale) * fiberCoefficient *
    (2 * (degreeLoss : ℝ)) *
    heavyLogLoss ^ 2 * Real.rpow retention (-3)

def AmbientRestrictedParentTangencyScaleStatement : Prop :=
  ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
    ∀ (data : DyadicFineAssignmentData
        family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
      (center : C2Function)
      (hE : MeasurableSet E)
      {C_R C_count C_shading C_volume : ℝ}
      (fineSetup : AmbientRestrictedFSVSetupData
        data center hE C_R C_count C_shading C_volume)
      (coarseSetup : AmbientRestrictedCoarseSetupData
        data center hE fineSetup)
      {massExponent : ℝ}
      (refinement : AmbientRestrictedLargeBinRefinementData
        data center hE fineSetup coarseSetup massExponent)
      (degreeSetup : RetainedIncidenceDegreeSetupData
        data center hE fineSetup coarseSetup refinement)
      (q_fiber : ℕ)
      (fiberBound : ℝ)
      (heavySetup : RetainedHeavySupportSetupData
        data center hE fineSetup coarseSetup refinement
          degreeSetup q_fiber fiberBound)
      (parentSetup : AmbientRestrictedParentFiberRegularizationData
        data center hE fineSetup coarseSetup refinement
          degreeSetup q_fiber fiberBound heavySetup)
      (retention fiberCoefficient incidenceScale : ℝ),
      2 ≤ q_fiber →
      0 < fiberBound →
      0 < retention →
      0 < fiberCoefficient →
      0 ≤ incidenceScale →
      fiberBound ≤ fiberCoefficient * (data.mu : ℝ) →
      retention * (data.mu : ℝ) <
        4 * ((q_fiber : ℝ) + 1) →
      (∀ index :
          Fin
            (selectedCoarseSubfamily coarseSetup.coarseData
              heavySetup.selectedCoarse).card,
        ((parentSetup.selectedRectangles index).card : ℝ) *
              (parentSetup.pairLower index : ℝ) ^ 2 ≤
          3 *
              ((selectedCoarseIncidenceSupport
                coarseSetup.coarseData degreeSetup.selectedEdges
                  heavySetup.selectedCoarse index).card : ℝ) ^ 2 *
            incidenceScale) →
      ((heavySetup.M_parent : ℕ) : ℝ) ≤
        ambientRestrictedParentTangencyScale
            incidenceScale fiberCoefficient
            heavySetup.degreeLoss heavySetup.heavyLogLoss retention *
          Real.rpow (data.mu : ℝ) (-2) *
          Real.rpow (2 ^ heavySetup.supportLevel : ℕ) 2

end Kakeya.Cinematic
