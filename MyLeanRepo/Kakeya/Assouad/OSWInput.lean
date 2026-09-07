import MyLeanRepo.Kakeya.Assouad.WZ1.Inputs
import MyLeanRepo.radial_bootstrapping_measure_thin_tubes

/-!
# Closed OSW input for WZ2

The OSW workstream and the WZ1 migration use definitionally equal thin-tubes
predicates in different namespaces. This module records that boundary
explicitly and transports the proved OSW radial bootstrap to WZ2's frozen
input proposition.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

theorem hasMeasureThinTubes_iff_osw
    (β K c : ℝ)
    (ν₁ ν₂ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) :
    HasMeasureThinTubes β K c ν₁ ν₂ ↔
      _root_.HasMeasureThinTubes β K c ν₁ ν₂ := by
  rfl

theorem osw_input : RadialBootstrappingMeasureThinTubesInput := by
  intro β ε hβ hε
  rcases radial_bootstrapping_measure_thin_tubes β ε hβ hε with
    ⟨τ, hτ, M, hM, hbootstrap⟩
  refine ⟨τ, hτ, M, hM, ?_⟩
  intro σ c K C ν₁ ν₂ hν₁Support hν₂Support hσ hc hK hC
    hSupportDistance hν₁Growth hν₂Growth hThin₁₂ hThin₂₁
  have hThin₁₂OSW : _root_.HasMeasureThinTubes σ K c ν₁ ν₂ :=
    (hasMeasureThinTubes_iff_osw σ K c ν₁ ν₂).mp hThin₁₂
  have hThin₂₁OSW : _root_.HasMeasureThinTubes σ K c ν₂ ν₁ :=
    (hasMeasureThinTubes_iff_osw σ K c ν₂ ν₁).mp hThin₂₁
  have hImproved :=
    hbootstrap σ c K C ν₁ ν₂ hν₁Support hν₂Support hσ hc hK hC
      hSupportDistance hν₁Growth hν₂Growth hThin₁₂OSW hThin₂₁OSW
  exact ⟨
    (hasMeasureThinTubes_iff_osw
      (σ + τ) (Real.rpow (max K (C ^ 2 * M / c)) M) (3 * c) ν₁ ν₂).mpr
        hImproved.1,
    (hasMeasureThinTubes_iff_osw
      (σ + τ) (Real.rpow (max K (C ^ 2 * M / c)) M) (3 * c) ν₂ ν₁).mpr
        hImproved.2⟩

end Kakeya.Assouad
