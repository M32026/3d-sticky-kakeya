import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCentered
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperCenteredWeightedSelection

/-!
# Ordinary-distinct cleanup on the actual direct half-offset terminal

The terminal family here is the literal output of
`DirectHalfOffsetTerminalCentered`, rather than a horizontally-normalized
proxy.  In particular, this module deliberately does not claim that the
source top-level Convex--Wolff bound survives the diagonal map
`diag(lambda, 1, lambda)`.  The sole quantitative input is the explicitly
stated centered-conflict degree bound for that actual centered terminal.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- Data retained by a weighted cleanup of the actual centered terminal. -/
structure PureWZ2HalfOffsetTerminalDistinctCleanupData
    (terminal : commonSource.TerminalGeometry)
    (degreeBound : ENNReal) where
  selected : Finset (Fin terminal.centeredFamily.card)
  distinct : WZ2PaperOrdinaryIsEssentiallyDistinct
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
      terminal.centeredFamily selected).family
  maximal : ∀ index : Fin terminal.centeredFamily.card, index ∈ selected ∨
    ∃ representative ∈ selected,
      pureWZ2PaperCenteredConflict terminal.centeredFamily index representative
  mass_lower : terminal.centeredCubicalShading.mass ≤
    (degreeBound + 1) *
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          terminal.centeredFamily selected)
        terminal.centeredCubicalShading).mass

namespace PureWZ2HalfOffsetTerminalDistinctCleanupData

/-- The genuine selected subfamily of the actual centered terminal. -/
def family
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (data : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset terminal.centeredFamily
    data.selected

/-- The literal restriction of the actual centered cubical shading. -/
def shading
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (data : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) :
    WZ1PaperTubeShading data.family.family :=
  restrictPaperShading data.family terminal.centeredCubicalShading

/-- The selected-family embedding lands in the original terminal index type.
This uses the definitional equality of the centered and original cardinalities. -/
def originalIndex
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (data : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (index : Fin data.family.family.card) : Fin terminal.family.card :=
  data.family.embedding index

end PureWZ2HalfOffsetTerminalDistinctCleanupData

/-- Weighted ordinary-distinct cleanup of the actual centered half-offset terminal.

`hdegree` is intentionally a hypothesis about the literal centered terminal family.
There is currently no proved API carrying `cfg.top_level_cwa`, together with
the terminal source-index provenance, through the diagonal terminal map to
this degree estimate. -/
theorem centered_distinct_selection
    (terminal : commonSource.TerminalGeometry)
    (degreeBound : ENNReal)
    (hdegree : ∀ reference : Fin terminal.centeredFamily.card,
      (((Finset.univ : Finset (Fin terminal.centeredFamily.card)).filter
        (pureWZ2PaperCenteredConflict terminal.centeredFamily reference)).card : ENNReal) ≤
          degreeBound) :
    Nonempty (PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) := by
  rcases pureWZ2_paper_weighted_centered_distinct_selection_ennreal
      terminal.centeredFamily terminal.centeredCubicalShading degreeBound hdegree with
    ⟨selected, hdistinct, hmaximal, hmass⟩
  let selectedFamily :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset terminal.centeredFamily selected
  exact ⟨{
    selected := selected
    distinct := hdistinct
    maximal := hmaximal
    mass_lower := hmass
  }⟩

/-- The centered terminal line-class certificate restricts to an actual
selected subfamily. -/
theorem line_class_subfamily
    (terminal : commonSource.TerminalGeometry)
    (selected : Kakeya.Streamlined.TubeSubfamily terminal.centeredFamily) :
    WZ1PaperIsLineClass selected.family :=
  terminal.centeredFamily_line_class.subfamily selected

/-- The centered terminal cubical shading restricts literally along an actual
selected subfamily. -/
theorem cubical_subfamily
    (terminal : commonSource.TerminalGeometry)
    (selected : Kakeya.Streamlined.TubeSubfamily terminal.centeredFamily) :
    WZ1PaperIsCubicalShading
      (restrictPaperShading selected terminal.centeredCubicalShading) :=
  restrictPaperShading_cubical selected terminal.centeredCubicalShading_cubical

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
