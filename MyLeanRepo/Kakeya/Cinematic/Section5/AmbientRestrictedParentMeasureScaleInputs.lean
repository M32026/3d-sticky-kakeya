import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLargeBinRefinementInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberCarrierContainmentInputs

/-!
# Measure scale for the selected parent multiplicity

Every selected coarse parent contains at least `2^parentLevel` selected fine
rectangles.  The selected dyadic layer gives each corresponding disjoint piece
mass at least `(2^layer) * cutoff`, while coarse-fiber carrier containment
places all such pieces in one explicit parent neighborhood.  This statement
records the resulting first bound for `M_parent`.
-/

namespace Kakeya.Cinematic

def AmbientRestrictedParentMeasureScaleStatement : Prop :=
  CoarseFiberCarrierContainmentStatement →
    CommonTangentRectangleStatement →
    ComparableRectanglesStatement →
    ∀ K D C_shading : ℝ,
      1 ≤ K →
      1 ≤ D →
      1 ≤ C_shading →
      ∃ C_out : ℝ,
        1 ≤ C_out ∧
        ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
          {delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
          ∀ (data : DyadicFineAssignmentData
              family E K delta diameter epsilon eta
                tRep DeltaRep C_R₀)
            (center : C2Function)
            (hE : MeasurableSet E)
            {C_R C_count C_volume : ℝ}
            (fineSetup : AmbientRestrictedFSVSetupData
              data center hE C_R C_count C_shading C_volume)
            (coarseSetup : AmbientRestrictedCoarseSetupData
              data center hE fineSetup)
            {massExponent : ℝ}
            (refinement : AmbientRestrictedLargeBinRefinementData
              data center hE fineSetup coarseSetup massExponent),
            IsCinematicFamily family K D →
            0 < delta →
            1 ≤ C_R →
            ((2 ^ refinement.parentLevel : ℕ) : ℝ) ≤
              (4 * C_out ^ 2 * DeltaRep *
                  Real.sqrt (DeltaRep / (C_R * tRep))) /
                (((2 : ENNReal) ^ refinement.layer.val *
                  refinement.cutoff).toReal)

end Kakeya.Cinematic
