import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageAssemblyStatements

/-!
# One-to-one literal-paper unit-rescaled family

Choose the canonical exact image-axis target tube independently for each
source index.  The target family has the same index type and uses the identity
source map.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_literal_unit_rescaled_family :
    WZ2PaperLiteralUnitRescaledFamilyStatement := by
  intro hCanonical delta rho hrho hrhoOne sourceFamily
    hsourceLine anchor hanchorLine hcovered
  let targetData :
      (source : Fin sourceFamily.card) →
        WZ2PaperLiteralCanonicalUnitRescaledTubeData
          (sourceFamily.tube source) anchor hrho :=
    fun source =>
      (hCanonical hrho hrhoOne
        (sourceFamily.tube source) anchor
        (hsourceLine source) hanchorLine
        (hcovered source)).some
  let targetFamily :
      Kakeya.Streamlined.TubeFamily (delta / rho) :=
    { card := sourceFamily.card
      tube := fun source => (targetData source).target }
  refine
    ⟨{
      targetFamily := targetFamily
      sourceIndex := id
      sourceIndex_bijective := Function.bijective_id
      target_line_class :=
        fun source => (targetData source).target_line_class
      target_axis :=
        fun source => (targetData source).target_axis }⟩

end Kakeya.Assouad

end
