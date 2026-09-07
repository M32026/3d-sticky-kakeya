import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Cropped refinement data for pure WZ2 large-slope step

Replaces `LargeSlopeRefinementData` by removing `UniformTubeStructure`
and `IsExtremalPair`, using `WZ1PaperTubeShading` and pure grain data instead.

This is the stable output of Steps 1–3 consumed by the Step4 witness and
the convex overload.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Total shaded mass inside a horizontal slab for a paper tube shading. -/
def paperShadedMassInSlab {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F) (a b : ℝ) : ENNReal :=
  ∑ i : Fin F.card,
    MeasureTheory.volume (Y.carrier i ∩ horizontalSlab a b)

/--
Stable output of Steps 1–3 for the pure cropped-carrier large-slope argument.

Carries the refined subshading, inherited C² grain data, selected slab,
card-proportional mass lower bound, and covering bound
needed by Steps 4 and the convex overload.  No `UniformTubeStructure`
or cardinality upper bound is present.

The absolute `slab_mass` bound was removed because it is not needed
for the card-proportional convex overload approach.
-/
structure LargeSlopeCroppedRefinementData
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (eta : ℝ) (C : ENNReal)
    (a b : ℝ) where
  left_mem : -1 ≤ a
  ordered : a < b
  right_mem : b ≤ 1
  scale_lower :
    Kakeya.realRpowENN delta (1 / 2 : ℝ) ≤
      ENNReal.ofReal (b - a)
  shading : WZ1PaperTubeShading cfg.family
  globalGrains :
    PureWZ2C2GlobalGrainData shading sigma C
  localGrains :
    PureWZ2LocalGrainData shading sigma C
  subshading :
    ∀ i, shading.carrier i ⊆ cfg.shading.carrier i
  slope_eq :
    globalGrains.f = cfg.globalGrains.f
  vertical_chart :
    IsInVerticalChart cfg.family
  ad_constant_one : 1 ≤ C
  ad_constant_ne_top : C ≠ ⊤
  ad_constant_bound :
    C ≤ Kakeya.realRpowENN delta (-(eta / 100))
  slab_mass_card :
    ENNReal.ofReal (Real.pi / 4) *
      Kakeya.realRpowENN delta (loss + 2) *
      cfg.family.enncard *
      ENNReal.ofReal (b - a) ≤
        paperShadedMassInSlab shading a b

end Kakeya.Assouad

end
