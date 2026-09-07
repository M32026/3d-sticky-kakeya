import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers

/-!
# Global lower bound for the coarse/fiber multiplicity product

This is the formal core of the paper sentence

> “the integrand ... is pointwise bounded by
> `mu_fine mu_coarse`.”

If the final fine shading has retained mass `massLower` and its union still
lies in a set of volume at most `volumeUpper`, then any uniform coarse and
fiber multiplicity caps must have product at least
`massLower / volumeUpper`.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperGlobalMultiplicityProductStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ1PaperTubeCover fine coarse),
          ∀ (fineShading : WZ1PaperTubeShading fine),
            ∀ (coarseShading : WZ1PaperTubeShading coarse),
              (∀ source point,
                point ∈ fineShading.carrier source →
                  point ∈
                    coarseShading.carrier (cover.parent source)) →
              ∀ (coarseCap fiberCap massLower volumeUpper : ENNReal),
                (∀ point,
                  (coarseShading.pointMultiplicity point : ENNReal) ≤
                    coarseCap) →
                (∀ parent point,
                  (cover.fiberPointMultiplicity
                      fineShading parent point : ENNReal) ≤
                    fiberCap) →
                massLower ≤ fineShading.mass →
                MeasureTheory.volume fineShading.union ≤ volumeUpper →
                  massLower ≤
                    (coarseCap * fiberCap) * volumeUpper

end Kakeya.Assouad

end
