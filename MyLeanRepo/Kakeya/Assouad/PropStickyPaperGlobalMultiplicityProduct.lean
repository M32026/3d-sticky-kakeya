import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityProductStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume

/-! # Global lower bound for the coarse/fiber multiplicity product -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_global_multiplicity_product :
    WZ2PaperGlobalMultiplicityProductStatement := by
  intro delta rho fine coarse cover fineShading coarseShading
    hCompatibility coarseCap fiberCap massLower volumeUpper
    hCoarse hFiber hMass hVolume
  have hPointwise :
      ∀ point,
        (fineShading.pointMultiplicity point : ENNReal) ≤
          coarseCap * fiberCap :=
    cover.pointMultiplicity_le_coarse_mul_fiber
      fineShading coarseShading hCompatibility
      hCoarse hFiber
  have hMassUpper :
      fineShading.mass ≤
        (coarseCap * fiberCap) *
          MeasureTheory.volume fineShading.union :=
    mass_le_of_pointMultiplicity_le
      (fun point _ => hPointwise point)
  calc
    massLower ≤ fineShading.mass := hMass
    _ ≤
        (coarseCap * fiberCap) *
          MeasureTheory.volume fineShading.union := hMassUpper
    _ ≤ (coarseCap * fiberCap) * volumeUpper := by
      gcongr

end Kakeya.Assouad

end
