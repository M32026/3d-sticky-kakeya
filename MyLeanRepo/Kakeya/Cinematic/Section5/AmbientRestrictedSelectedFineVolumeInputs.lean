import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLargeBinRefinementInputs

/-!
# Selected-layer fine volume inside one ambient bin

The large-bin refinement retains a joint dyadic layer carrying a fixed
fraction of the bin mass.  Every selected piece lies in one enlarged fine
rectangle with a uniform area bound.  This statement combines those two facts
while retaining the refinement's exact explicit `massFactor`.
-/

open MeasureTheory

namespace Kakeya.Cinematic

def AmbientRestrictedSelectedFineVolumeStatement : Prop :=
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
        data center hE fineSetup coarseSetup massExponent),
      0 ≤ C_shading →
      0 ≤ delta →
      volume (ambientRestrictedSet data center) ≤
        (refinement.selected.card : ENNReal) *
          ENNReal.ofReal
            ((refinement.massFactor : ℝ) *
              (2 * (C_shading * delta) *
                Real.sqrt
                  ((C_shading * delta) /
                    (C_R * tRep * DeltaRep / delta))))

end Kakeya.Cinematic
