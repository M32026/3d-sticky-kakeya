import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementCompositionStatements

/-! # Composition of nested paper refinements -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_refinement_composition :
    WZ2PaperRefinementCompositionStatement := by
  intro delta family shading outerExponent innerExponent
    outer inner
  let outerFraction :=
    wz1PaperRefinementFraction delta outerExponent
  let innerFraction :=
    wz1PaperRefinementFraction delta innerExponent
  have hfraction :
      wz1PaperRefinementFraction
          delta (outerExponent + innerExponent) =
        outerFraction * innerFraction := by
    simp only [wz1PaperRefinementFraction, pow_add]
    rfl
  have hsubshading :
      ∀ index :
          Fin (outer.selected.comp inner.selected).family.card,
        inner.refined.carrier index ⊆
          shading.carrier
            ((outer.selected.comp inner.selected).embedding
              index) := by
    intro index
    have hinner :
        inner.refined.carrier index ⊆
          outer.refined.carrier
            (inner.selected.embedding index) :=
      inner.subshading index
    have houter :
        outer.refined.carrier
            (inner.selected.embedding index) ⊆
          shading.carrier
            (outer.selected.embedding
              (inner.selected.embedding index)) :=
      outer.subshading (inner.selected.embedding index)
    exact hinner.trans houter
  have hmass :
      wz1PaperRefinementFraction
            delta (outerExponent + innerExponent) *
          shading.mass ≤
        inner.refined.mass := by
    rw [hfraction]
    calc
      (outerFraction * innerFraction) * shading.mass =
          innerFraction *
            (outerFraction * shading.mass) := by
        ring
      _ ≤ innerFraction * outer.refined.mass := by
        exact
          mul_le_mul_left'
            outer.retained_mass innerFraction
      _ ≤ inner.refined.mass :=
        inner.retained_mass
  exact
    ⟨{
      subshading := hsubshading
      retained_mass := hmass
    }⟩

end Kakeya.Assouad

end
