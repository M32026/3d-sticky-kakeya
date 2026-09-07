import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber

/-!
# Localized ordinary essential distinctness

For ordinary unit-segment tubes whose midpoints remain in the fixed local
window, sufficiently large pairwise paper line distance rules out carrier
containment in either centered doubled parent.
-/

noncomputable section

namespace Kakeya.Assouad

/--
A localized line-class family separated by more than the closed
centered-doubled containment loss is essentially distinct in the literal
ordinary sense of Assouad Definition 2.12.
-/
theorem wz2_paper_localized_ordinary_isEssentiallyDistinct
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (hline : WZ1PaperIsLineClass family)
    (hlocal :
      ∀ index,
        ‖wz2PaperTubeMidpoint (family.tube index)‖ ≤ 3)
    (hseparated :
      ∀ first second, first ≠ second →
        wz2PaperLocalizedDoubledFiberLineDistanceConstant * delta <
          wz1PaperLineDistance
            (family.tube first) (family.tube second)) :
    WZ2PaperOrdinaryIsEssentiallyDistinct family := by
  intro first second hne
  constructor
  · intro hcontained
    have hdistance :=
      wz2_paper_localized_centered_doubled_containment_lineDistance_le
        hdelta hdelta
        (hline first) (hline second)
        (hlocal first)
        hcontained
    exact (not_lt_of_ge hdistance) (hseparated first second hne)
  · intro hcontained
    have hdistance :=
      wz2_paper_localized_centered_doubled_containment_lineDistance_le
        hdelta hdelta
        (hline second) (hline first)
        (hlocal second)
        hcontained
    exact (not_lt_of_ge hdistance) (hseparated second first hne.symm)

end Kakeya.Assouad

end
