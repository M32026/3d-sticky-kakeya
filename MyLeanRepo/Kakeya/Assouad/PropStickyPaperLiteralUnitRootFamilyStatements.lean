import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRootCoverStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageAssemblyStatements

/-!
# Singleton unit-root cover of a literal target family

Package the one-tube vertical-root geometry uniformly over an indexed literal
target family.  The unique parent map is surjective, its assigned fiber is the
whole family, and the unique coarse tube is essentially distinct.

This is only the cover/indexing half of the high-scale nearby witness.
Root-relative rescaled-fiber CWA is a separate leaf.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The singleton indexed family containing only the fixed vertical root. -/
def wz2PaperLiteralUnitRootFamily :
    Kakeya.Streamlined.TubeFamily 1 where
  card := 1
  tube := fun _ => wz2PaperLiteralUnitRootTube

/-- The unique index of the singleton root family. -/
def wz2PaperLiteralUnitRootIndex :
    Fin wz2PaperLiteralUnitRootFamily.card :=
  ⟨0, by
    change 0 < 1
    norm_num⟩

structure WZ2PaperLiteralUnitRootFamilyData
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube sigma}
    {hsigma : 0 < sigma}
    (literalFamily :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hsigma) where
  cover :
    WZ2PaperLiteralDilatedPartitioningCover
      literalFamily.targetFamily
      wz2PaperLiteralUnitRootFamily
  all_parent :
    ∀ target,
      cover.parent target = wz2PaperLiteralUnitRootIndex
  fiber_all :
    cover.fiberIndices wz2PaperLiteralUnitRootIndex =
      Finset.univ
  coarse_line_class :
    WZ1PaperIsLineClass wz2PaperLiteralUnitRootFamily
  coarse_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct
      wz2PaperLiteralUnitRootFamily

def WZ2PaperLiteralUnitRootFamilyStatement : Prop :=
  WZ2PaperLiteralUnitRootCoverStatement →
  ∀ {delta sigma : ℝ},
    ∀ (hsigma : 0 < sigma),
      sigma ≤ 1 →
      ∀ (sourceFamily :
          Kakeya.Streamlined.TubeFamily delta),
        0 < sourceFamily.card →
        WZ1PaperIsLineClass sourceFamily →
        ∀ (anchor : Kakeya.DeltaTube sigma),
          WZ1PaperTubeInLineClass anchor →
          (∀ source,
            WZ1PaperTubeCovers
              (sourceFamily.tube source) anchor) →
          ∀ (literalFamily :
              WZ2PaperLiteralUnitRescaledFamilyData
                sourceFamily anchor hsigma),
            Nonempty
              (WZ2PaperLiteralUnitRootFamilyData literalFamily)

end Kakeya.Assouad

end
