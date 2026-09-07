import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRootFamilyStatements

/-!
# Common convex envelope for the vertical unit-root rescaling

Relative to the fixed vertical unit root, the historical paper rescaling
preserves the longitudinal coordinate and compresses each transverse
coordinate by `1 / 100`.  Thus the inverse image of one convex target set is
a common convex source envelope with volume loss exactly `100 ^ 2 = 10000`.

This is the geometric transfer leaf only.  It does not construct an indexed
rescaled family or assert a Convex-Wolff bound.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def WZ2PaperUnitRootTransverseEnvelopeStatement : Prop :=
  ∀ {scale : ℝ},
    0 < scale →
    ∀ {sourceFamily :
        Kakeya.Streamlined.TubeFamily scale},
      ∀ {targetFamily :
          Kakeya.Streamlined.TubeFamily (scale / 1)},
        ∀ (indexEquiv :
            Fin targetFamily.card ≃ Fin sourceFamily.card),
          (∀ target,
            tubeAxisLine (targetFamily.tube target) =
              wz1PaperUnitRescalingMap
                  wz2PaperLiteralUnitRootTube (by norm_num) ''
                tubeAxisLine
                  (sourceFamily.tube (indexEquiv target))) →
          ∀ targetConvexSet : Set Point3,
            Convex ℝ targetConvexSet →
            ∃ sourceConvexSet : Set Point3,
              Convex ℝ sourceConvexSet ∧
              volume sourceConvexSet ≤
                (10000 : ENNReal) * volume targetConvexSet ∧
              ∀ target,
                wz1PaperTubeCarrier
                      (targetFamily.tube target) ⊆
                    targetConvexSet →
                  wz1PaperTubeCarrier
                      (sourceFamily.tube (indexEquiv target)) ⊆
                    sourceConvexSet

end Kakeya.Assouad

end
