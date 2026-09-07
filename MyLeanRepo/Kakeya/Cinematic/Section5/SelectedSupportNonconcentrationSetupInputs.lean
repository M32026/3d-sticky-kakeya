import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceCoarseFiberNonconcentrationAtInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedHeavySupportSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedCoarseIncidenceSubfamily

/-!
# Nonconcentration of selected fixed-bin supports

Transport pointwise selected-fiber ball bounds through the aggregate
incidence double count, then convert the resulting support estimate into the
half-mass tangent-count condition used by both cluster-selection branches.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance selectedSupportNonconcentrationDecidableEq :
    DecidableEq C2Function := Classical.decEq _

structure SelectedSupportNonconcentrationSetupData
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
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
    (coefficient radius : ℝ) where
  support_nonconcentration :
    ∀ coarse ∈ heavySetup.selectedCoarse, ∀ testCenter,
      (((incidenceSupportFamily degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse).carrier ∩
          c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
        coefficient *
          ((incidenceSupportFamily degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse).card : ℝ)
  cluster_tangent_half :
    2 * coefficient ≤ 1 →
      ∀ index :
          Fin
            (selectedCoarseSubfamily coarseSetup.coarseData
              heavySetup.selectedCoarse).card,
        ∀ testCenter,
          2 * RectangleFamily.tangentCount
                ((selectedCoarseSubfamily coarseSetup.coarseData
                  heavySetup.selectedCoarse).family.rectangle index)
                ((selectedCoarseIncidenceSupport
                  coarseSetup.coarseData degreeSetup.selectedEdges
                    heavySetup.selectedCoarse index).cluster
                      testCenter (11 * radius))
                coarseSetup.tangency ≤
            RectangleFamily.tangentCount
              ((selectedCoarseSubfamily coarseSetup.coarseData
                heavySetup.selectedCoarse).family.rectangle index)
              (selectedCoarseIncidenceSupport
                coarseSetup.coarseData degreeSetup.selectedEdges
                  heavySetup.selectedCoarse index)
              coarseSetup.tangency

def SelectedSupportNonconcentrationSetupStatement : Prop :=
  IncidenceCoarseFiberNonconcentrationAtStatement.{0, 0} →
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
        (mu₁ coefficient radius : ℝ),
        0 < q_fiber →
        0 ≤ coefficient →
        mu₁ ≤ coefficient * (q_fiber : ℝ) →
        (∀ coarse ∈ heavySetup.heavy,
          ∀ rectangle ∈
              incidenceRectangleSupport degreeSetup.selectedEdges
                coarseSetup.coarseData.parent coarse,
            ∀ testCenter,
              (((incidenceRectangleFiber degreeSetup.selectedEdges
                    rectangle : Set C2Function) ∩
                  c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
                mu₁) →
        Nonempty
          (SelectedSupportNonconcentrationSetupData
            data center hE fineSetup coarseSetup refinement
              degreeSetup q_fiber fiberBound heavySetup
                ((2 * heavySetup.heavyLogLoss) * coefficient)
                radius)

end Kakeya.Cinematic
