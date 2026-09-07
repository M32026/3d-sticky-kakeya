import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry

/-!
# Aggregate mass upper bound for a paper shading

Each cropped paper tube has volume at most the fixed geometric constant times
`scale^2`.  Summing over the indexed family bounds the total shaded mass.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperShadingMassUpperStatement : Prop :=
  ∀ {scale : ℝ},
    0 < scale →
    scale ≤ 1 / 24 →
    ∀ {family : Kakeya.Streamlined.TubeFamily scale},
      WZ1PaperIsLineClass family →
      ∀ shading : WZ1PaperTubeShading family,
        shading.mass ≤
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN scale 2 *
              family.enncard

end Kakeya.Assouad

end
