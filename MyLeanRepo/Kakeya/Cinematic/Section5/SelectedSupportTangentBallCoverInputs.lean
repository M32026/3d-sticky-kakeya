import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedSupportNonconcentrationSetupInputs

/-!
# One tangent-ball cover for all selected supports

Cover the fixed ambient family of one bin at the coarse radius.  Every
selected incidence support is then covered by the same center set, so both
the positive-quotient and singleton cluster routes use identical geometry.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance selectedSupportTangentBallCoverDecidableEq :
    DecidableEq C2Function := Classical.decEq _

structure SelectedSupportTangentBallCoverData
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
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
    (radius : ℝ) where
  centers : Finset C2Function
  centers_subset : (centers : Set C2Function) ⊆ family
  ambient_cover :
    (data.ambientSource.cluster center (3 * tRep)).carrier ⊆
      ⋃ c ∈ centers, c2Ball c radius
  depth : ℕ
  depth_scale :
    (6 * (C_R * tRep)) / 2 ^ depth ≤ radius
  centers_card :
    (centers.card : ℝ) ≤ D ^ depth
  centers_card_polynomial :
    (centers.card : ℝ) ≤
      D *
        Real.rpow
          (max (6 * (C_R * tRep)) radius / radius)
          (Real.log D / Real.log 2)
  centers_nonempty : centers.Nonempty
  selected_support_cover :
    ∀ index :
        Fin
          (selectedCoarseSubfamily coarseSetup.coarseData
            heavySetup.selectedCoarse).card,
      (selectedCoarseIncidenceSupport
        coarseSetup.coarseData degreeSetup.selectedEdges
          heavySetup.selectedCoarse index).carrier ⊆
        ⋃ c ∈ centers, c2Ball c radius

def SelectedSupportTangentBallCoverStatement : Prop :=
  FiniteTangentBallCoverStatement →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
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
        (radius : ℝ),
        1 ≤ D →
        IsCinematicFamily family K D →
        0 < C_R →
        0 < radius →
        Nonempty
          (SelectedSupportTangentBallCoverData
            (D := D) data center hE fineSetup coarseSetup refinement
              degreeSetup q_fiber fiberBound heavySetup radius)

end Kakeya.Cinematic
