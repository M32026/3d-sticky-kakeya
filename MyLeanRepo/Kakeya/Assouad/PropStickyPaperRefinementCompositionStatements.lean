import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Composition of nested paper refinements

If an outer paper refinement retains a logarithmic fraction of a shading and
an inner refinement retains a logarithmic fraction of the outer refined
shading, their nested tube subfamilies and final shading form one refinement
of the original shading.  The logarithmic exponents add.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperRefinementCompositionData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (outerExponent innerExponent : ℕ)
    (outer : WZ1PaperRefinement shading outerExponent)
    (inner : WZ1PaperRefinement outer.refined innerExponent) where
  subshading :
    ∀ index,
      inner.refined.carrier index ⊆
        shading.carrier
          ((outer.selected.comp inner.selected).embedding index)
  retained_mass :
    wz1PaperRefinementFraction
          delta (outerExponent + innerExponent) *
        shading.mass ≤
      inner.refined.mass

namespace WZ2PaperRefinementCompositionData

/-- The canonical nested selection as one paper refinement. -/
noncomputable def toRefinement
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {outerExponent innerExponent : ℕ}
    {outer : WZ1PaperRefinement shading outerExponent}
    {inner : WZ1PaperRefinement outer.refined innerExponent}
    (data :
      WZ2PaperRefinementCompositionData
        shading outerExponent innerExponent outer inner) :
    WZ1PaperRefinement
      shading (outerExponent + innerExponent) where
  selected := outer.selected.comp inner.selected
  refined := inner.refined
  subshading := data.subshading
  retained_mass := data.retained_mass

end WZ2PaperRefinementCompositionData

def WZ2PaperRefinementCompositionStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ {family : Kakeya.Streamlined.TubeFamily delta},
      ∀ (shading : WZ1PaperTubeShading family),
        ∀ (outerExponent innerExponent : ℕ),
          ∀ (outer :
              WZ1PaperRefinement shading outerExponent),
            ∀ (inner :
                WZ1PaperRefinement
                  outer.refined innerExponent),
              Nonempty
                (WZ2PaperRefinementCompositionData
                  shading outerExponent innerExponent
                  outer inner)

end Kakeya.Assouad

end
