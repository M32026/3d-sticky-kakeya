import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Finite parent-map regularization for WZ2 `prop: sticky`

This is the finite combinatorial content of the paper's repeated
pigeonholing.  It does not claim that an arbitrary selected subfamily
automatically inherits the Convex Wolff axioms.  Instead, it simultaneously
regularizes the degrees of a prescribed finite list of parent maps while
retaining an explicit polylogarithmic fraction of the shaded mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure WZ2PaperFiniteParentRegularizationData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (scaleCount : ℕ)
    (Parent : Fin scaleCount → Type _)
    [∀ scale, Fintype (Parent scale)]
    [∀ scale, DecidableEq (Parent scale)]
    (parent : ∀ scale, Fin family.card → Parent scale) where
  selected : Finset (Fin family.card)
  degree_uniform :
    ∀ scale,
      ∀ first second : Parent scale,
        0 <
            (selected.filter
              (fun index => parent scale index = first)).card →
          0 <
            (selected.filter
              (fun index => parent scale index = second)).card →
          ((selected.filter
              (fun index => parent scale index = first)).card :
              ENNReal) ≤
            (16 * (scaleCount : ENNReal) *
                (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
                  scaleCount) *
              ((selected.filter
                (fun index => parent scale index = second)).card :
                ENNReal)
  retained_mass :
    shading.mass ≤
      (8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (scaleCount + 1) *
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            family selected)
          shading).mass

/--
Simultaneously regularize a finite family of parent maps, weighted by the
paper shaded mass of each source tube.
-/
def WZ2PropStickyFiniteParentRegularizationStatement : Prop :=
  ∀ {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (scaleCount : ℕ)
    (Parent : Fin scaleCount → Type)
    [∀ scale, Fintype (Parent scale)]
    [∀ scale, DecidableEq (Parent scale)]
    (parent : ∀ scale, Fin family.card → Parent scale),
      Nonempty
        (WZ2PaperFiniteParentRegularizationData
          shading scaleCount Parent parent)

end Kakeya.Assouad

end
