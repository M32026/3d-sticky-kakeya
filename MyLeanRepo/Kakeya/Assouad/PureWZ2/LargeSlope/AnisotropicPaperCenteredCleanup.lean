import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicCenteredConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperParameterFrostman

/-!
# Public centered cleanup of the exact triangular paper retubing

This is the duplicate-removal step in Proposition 6.5.  It applies the
public centered-containment relation directly to the one-to-one exact image
family.  Source Convex--Wolff control bounds the conflict degree through the
exact triangular inverse parameter estimate.  Every selected target tube
retains its literal source index and exact centered-image supporting line.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The source-parameter width forced by one public centered conflict in the
exact triangular target family. -/
def anisotropicPaperConflictWidth
    (targetDelta c d m : ℝ) : ℝ :=
  100 * (600 * targetDelta) / (m * (d - c) ^ 2)

/-- The corresponding target conflict-degree bound obtained from source CWA. -/
def anisotropicPaperConflictDegreeBound
    {sourceDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceConstant : ENNReal) (targetDelta c d m : ℝ) : ENNReal :=
  (3200 * sourceConstant) *
    Kakeya.realRpowENN
      (anisotropicPaperConflictWidth targetDelta c d m) 2 *
        sourceFamily.enncard

/-- Output of public centered-conflict cleanup of one exact triangular
retubing. -/
structure PureWZ2AnisotropicPaperCenteredCleanupData
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (sourceConstant : ENNReal) where
  conflict_width_le_one :
    anisotropicPaperConflictWidth targetDelta c d m ≤ 1
  selected : Finset (Fin (anisotropicPaperTargetFamily
    sourceFamily g c d m center targetDelta hcd hm).card)
  distinct :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        (anisotropicPaperTargetFamily
          sourceFamily g c d m center targetDelta hcd hm) selected).family
  maximal : ∀ index : Fin (anisotropicPaperTargetFamily
      sourceFamily g c d m center targetDelta hcd hm).card,
    index ∈ selected ∨
      ∃ representative ∈ selected,
        pureWZ2PaperCenteredConflict
          (anisotropicPaperTargetFamily
            sourceFamily g c d m center targetDelta hcd hm)
          index representative
  mass_lower : raw.shading.mass ≤
    (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
        targetDelta c d m + 1) *
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          (anisotropicPaperTargetFamily
            sourceFamily g c d m center targetDelta hcd hm) selected)
          raw.shading).mass
  line_class :
    WZ1PaperIsLineClass
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        (anisotropicPaperTargetFamily
          sourceFamily g c d m center targetDelta hcd hm) selected).family
  cubical :
    WZ1PaperIsCubicalShading
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          (anisotropicPaperTargetFamily
            sourceFamily g c d m center targetDelta hcd hm) selected)
          raw.shading)

namespace PureWZ2AnisotropicPaperCenteredCleanupData

/-- The genuine public family retained by centered cleanup. -/
def family
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (data : PureWZ2AnisotropicPaperCenteredCleanupData raw sourceConstant) :
    Kakeya.Streamlined.TubeFamily targetDelta :=
  (Kakeya.Streamlined.TubeSubfamily.fromFinset
    (anisotropicPaperTargetFamily
      sourceFamily g c d m center targetDelta hcd hm) data.selected).family

/-- The literal restricted cubical shading on the cleaned family. -/
def shading
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (data : PureWZ2AnisotropicPaperCenteredCleanupData raw sourceConstant) :
    WZ1PaperTubeShading data.family :=
  restrictPaperShading
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
      (anisotropicPaperTargetFamily
        sourceFamily g c d m center targetDelta hcd hm) data.selected)
    raw.shading

/-- Each cleaned tube remembers the unique source tube whose supporting line
was transformed. -/
def sourceIndex
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (data : PureWZ2AnisotropicPaperCenteredCleanupData raw sourceConstant) :
    Fin data.family.card → Fin sourceFamily.card :=
  (Kakeya.Streamlined.TubeSubfamily.fromFinset
    (anisotropicPaperTargetFamily
      sourceFamily g c d m center targetDelta hcd hm) data.selected).embedding

theorem sourceIndex_injective
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (data : PureWZ2AnisotropicPaperCenteredCleanupData raw sourceConstant) :
    Function.Injective data.sourceIndex :=
  (Kakeya.Streamlined.TubeSubfamily.fromFinset
    (anisotropicPaperTargetFamily
      sourceFamily g c d m center targetDelta hcd hm) data.selected).embedding.injective

/-- Exact centered triangular axis provenance survives cleanup. -/
theorem axis_source
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (data : PureWZ2AnisotropicPaperCenteredCleanupData raw sourceConstant)
    (index : Fin data.family.card) :
    tubeAxisLine (data.family.tube index) =
      anisotropicCenteredRescalingMap g c d m center ''
        tubeAxisLine (sourceFamily.tube (data.sourceIndex index)) := by
  change tubeAxisLine
      ((anisotropicPaperTargetFamily
        sourceFamily g c d m center targetDelta hcd hm).tube
        ((Kakeya.Streamlined.TubeSubfamily.fromFinset
          (anisotropicPaperTargetFamily
            sourceFamily g c d m center targetDelta hcd hm) data.selected).embedding index)) = _
  exact raw.axis
    ((Kakeya.Streamlined.TubeSubfamily.fromFinset
      (anisotropicPaperTargetFamily
        sourceFamily g c d m center targetDelta hcd hm) data.selected).embedding index)

theorem raw_mass_le
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (data : PureWZ2AnisotropicPaperCenteredCleanupData raw sourceConstant) :
    raw.shading.mass ≤
      (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
          targetDelta c d m + 1) * data.shading.mass :=
  data.mass_lower

end PureWZ2AnisotropicPaperCenteredCleanupData

/-- Apply source CWA, exact triangular inverse parameters, and the weighted
public centered independent-set selection to a paper retubing. -/
theorem PureWZ2AnisotropicPaperRetubingData.toCenteredCleanup
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hmOne : m ≤ 1)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (sourceConstant : ENNReal)
    (hsourceCWA : WZ2PaperConvexWolffBound sourceFamily sourceConstant)
    (hsourceWidth : sourceDelta ≤
      anisotropicPaperConflictWidth targetDelta c d m)
    (hwidthOne : anisotropicPaperConflictWidth targetDelta c d m ≤ 1) :
    Nonempty
      (PureWZ2AnisotropicPaperCenteredCleanupData raw sourceConstant) := by
  let targetFamily := anisotropicPaperTargetFamily
    sourceFamily g c d m center targetDelta hcd hm
  let width := anisotropicPaperConflictWidth targetDelta c d m
  let degreeBound := anisotropicPaperConflictDegreeBound
    sourceFamily sourceConstant targetDelta c d m
  have hsourceVertical : ∀ source : Fin sourceFamily.card,
      (sourceFamily.tube source).direction 2 ≠ 0 := by
    intro source hzero
    have hvertical := hsourceLine source |>.vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have htargetVertical : ∀ target : Fin targetFamily.card,
      (targetFamily.tube target).direction 2 ≠ 0 := by
    intro target hzero
    have hvertical := raw.line_class target |>.vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have hfiber : ∀ source : Fin sourceFamily.card,
      ((Finset.univ : Finset (Fin targetFamily.card)).filter fun target =>
        target = source).card ≤ 1 := by
    intro source
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    exact (Finset.mem_filter.mp hfirst).2.trans
      (Finset.mem_filter.mp hsecond).2.symm
  have hFrostman : TubeParameterFrostmanBound sourceFamily
      (3200 * sourceConstant) :=
    paper_tubeParameterFrostmanBound_of_croppedConvexWolff
      hsourceDelta sourceFamily hsourceLine sourceConstant hsourceCWA
  have hdegree : ∀ reference : Fin targetFamily.card,
      (((Finset.univ : Finset (Fin targetFamily.card)).filter
        (pureWZ2PaperCenteredConflict targetFamily reference)).card :
          ENNReal) ≤ degreeBound := by
    have h := anisotropic_recentered_conflict_degree_le
      hInverse hcd hdc hsub hm hmOne g center hgmid
      htargetDelta sourceFamily targetFamily
      (fun index => index) 1 hfiber raw.line_class raw.midpoint_local
      hsourceVertical htargetVertical raw.axis (3200 * sourceConstant)
      sourceFamily.enncard hFrostman width rfl hsourceWidth hwidthOne
    intro reference
    simpa [degreeBound, anisotropicPaperConflictDegreeBound, width]
      using h reference
  rcases pureWZ2_paper_weighted_centered_distinct_selection_ennreal
      targetFamily raw.shading degreeBound hdegree with
    ⟨selected, hdistinct, hmaximal, hmass⟩
  let selectedFamily :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset targetFamily selected
  exact ⟨{
    conflict_width_le_one := hwidthOne
    selected := selected
    distinct := hdistinct
    maximal := hmaximal
    mass_lower := by
      simpa [degreeBound, anisotropicPaperConflictDegreeBound] using hmass
    line_class := raw.line_class.subfamily selectedFamily
    cubical := restrictPaperShading_cubical selectedFamily raw.cubical
  }⟩

end Kakeya.Assouad

end
