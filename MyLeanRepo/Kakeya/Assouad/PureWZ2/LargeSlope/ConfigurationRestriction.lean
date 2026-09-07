import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationWeakening
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalGrainRestriction

/-!
# Restrict pure WZ2 grain data to a paper subshading

Section 6 repeatedly replaces a shading by a whole-cell subshading.  The
global and local grain conclusions restrict functorially: the plane map is
precomposed with the subtype inclusion, and both AD conclusions use subset
monotonicity.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The union inclusion induced by a pointwise paper subshading. -/
theorem paperSubshading_union_subset
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source target : WZ1PaperTubeShading family}
    (hsub : ∀ index, target.carrier index ⊆ source.carrier index) :
    target.union ⊆ source.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨index, hsub index hpoint⟩

/-- Restrict the exact C2 global-grain record to a paper subshading. -/
def PureWZ2C2GlobalGrainData.restrict_same_constant
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source target : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData source sigma C)
    (hsub : ∀ index, target.carrier index ⊆ source.carrier index) :
    PureWZ2C2GlobalGrainData target sigma C where
  f := data.f
  normalized := data.normalized
  global_ad := by
    intro z
    exact (data.global_ad z).weaken_subset (by
      apply Set.image_mono
      intro point hpoint
      exact ⟨paperSubshading_union_subset hsub hpoint.1, hpoint.2⟩)

@[simp] theorem PureWZ2C2GlobalGrainData.slope_restrict_same_constant
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source target : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData source sigma C)
    (hsub : ∀ index, target.carrier index ⊆ source.carrier index) :
    (data.restrict_same_constant hsub).slope = data.slope := by
  rfl

end Kakeya.Assouad

end
