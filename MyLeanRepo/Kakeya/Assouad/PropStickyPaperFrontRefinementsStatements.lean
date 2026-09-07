import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancingStatements

/-!
# Initial paper refinements before whole-cell balancing

Package the complete heavy-parent selection and the global point-multiplicity
band as genuine paper refinements with explicit finite losses.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperHeavyParentSelectionLoss
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (heavy : WZ2PaperHeavyParentSelectionData cover shading) : ENNReal :=
  2 * (heavy.bins : ENNReal)

structure WZ2PaperHeavyParentRefinementData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (heavy : WZ2PaperHeavyParentSelectionData cover shading)
    (logExponent : ℕ) where
  retained_mass :
    wz1PaperRefinementFraction delta logExponent *
        shading.mass ≤
      heavy.selectedShading.mass

namespace WZ2PaperHeavyParentRefinementData

noncomputable def toRefinement
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {heavy : WZ2PaperHeavyParentSelectionData cover shading}
    {logExponent : ℕ}
    (data : WZ2PaperHeavyParentRefinementData heavy logExponent) :
    WZ1PaperRefinement shading logExponent where
  selected := heavy.selected
  refined := heavy.selectedShading
  subshading index := by
    rw [heavy.selectedShading_eq]
    exact Set.Subset.rfl
  retained_mass := data.retained_mass

end WZ2PaperHeavyParentRefinementData

def WZ2PaperHeavyParentRefinementStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ {cover : WZ2PaperPartitioningCover fine coarse},
          ∀ {shading : WZ1PaperTubeShading fine},
            ∀ (heavy : WZ2PaperHeavyParentSelectionData cover shading),
              ∀ (logExponent : ℕ),
                wz1PaperRefinementFraction delta logExponent *
                      wz2PaperHeavyParentSelectionLoss heavy ≤
                    1 →
                  Nonempty
                    (WZ2PaperHeavyParentRefinementData
                      heavy logExponent)

def wz2PaperGlobalMultiplicityBandLoss
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (bandData : WZ2PaperGlobalMultiplicityBandData shading) : ENNReal :=
  ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal)

structure WZ2PaperGlobalMultiplicityBandRefinementData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    (logExponent : ℕ) where
  source_mass_le :
    shading.mass ≤
      wz2PaperGlobalMultiplicityBandLoss bandData *
        bandData.band.mass
  retained_mass :
    wz1PaperRefinementFraction delta logExponent *
        shading.mass ≤
      bandData.band.mass

namespace WZ2PaperGlobalMultiplicityBandRefinementData

noncomputable def toRefinement
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {bandData : WZ2PaperGlobalMultiplicityBandData shading}
    {logExponent : ℕ}
    (data :
      WZ2PaperGlobalMultiplicityBandRefinementData
        bandData logExponent) :
    WZ1PaperRefinement shading logExponent where
  selected :=
    { family := fine
      embedding := Equiv.toEmbedding (Equiv.refl (Fin fine.card))
      tube_eq := fun _ => rfl }
  refined := bandData.band
  subshading index := by
    rw [bandData.band_eq]
    simpa using
      wz1PaperDyadicBandSubshading_isSubshading
        shading bandData.level index
  retained_mass := data.retained_mass

end WZ2PaperGlobalMultiplicityBandRefinementData

def WZ2PaperGlobalMultiplicityBandRefinementStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : WZ1PaperTubeShading fine},
        ∀ (bandData : WZ2PaperGlobalMultiplicityBandData shading),
          ∀ (logExponent : ℕ),
            wz1PaperRefinementFraction delta logExponent *
                  wz2PaperGlobalMultiplicityBandLoss bandData ≤
                1 →
              Nonempty
                (WZ2PaperGlobalMultiplicityBandRefinementData
                  bandData logExponent)

end Kakeya.Assouad

end
