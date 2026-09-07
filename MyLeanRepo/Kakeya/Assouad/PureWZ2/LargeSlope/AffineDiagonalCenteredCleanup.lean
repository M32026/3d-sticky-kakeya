import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalRawFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperCenteredConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperParameterFrostman

/-!
# Public centered-distinct cleanup of the affine diagonal family

The raw one-parent/one-tube family is cleaned up directly in the public
Definition 2.12 relation.  Conflict degree is pulled back through the exact
fully centered affine axis provenance and counted by the ambient Node-5 CWA.
The source-parent map is injective, so the parent-fiber cap is exactly one.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The source-parameter width of a public centered target conflict. -/
def pureWZ2AffineDiagonalConflictWidth
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (scale : PureWZ2AffineDiagonalScaleData subband) : ℝ :=
  16 * (1 + scale.slopeData.heightScale) *
    (1 + scale.slopeData.transverseScale⁻¹) *
      (600 * scale.targetDelta)

/-- The exact ENNReal conflict-degree bound supplied by ambient parameter
Frostman control. -/
def pureWZ2AffineDiagonalConflictDegreeBound
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (scale : PureWZ2AffineDiagonalScaleData subband) : ENNReal :=
  (3200 * band.sourceConstant) *
    Kakeya.realRpowENN (pureWZ2AffineDiagonalConflictWidth scale) 2 *
      band.lemma31.data.cfg.family.enncard

structure PureWZ2AffineDiagonalCenteredCleanupData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scale : PureWZ2AffineDiagonalScaleData subband) where
  raw : PureWZ2AffineDiagonalRawFamilyData popular scale
  conflict_width_le_one : pureWZ2AffineDiagonalConflictWidth scale ≤ 1
  selected : Finset (Fin raw.family.card)
  distinct :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        raw.family selected).family
  maximal : ∀ index : Fin raw.family.card,
    index ∈ selected ∨
      ∃ representative ∈ selected,
        pureWZ2PaperCenteredConflict raw.family index representative
  mass_lower : raw.shading.mass ≤
    (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset raw.family selected)
        raw.shading).mass
  line_class :
    WZ1PaperIsLineClass
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        raw.family selected).family
  cubical :
    WZ1PaperIsCubicalShading
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset raw.family selected)
        raw.shading)

namespace PureWZ2AffineDiagonalCenteredCleanupData

/-- The genuine public family retained by the centered cleanup. -/
def family
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    (data : PureWZ2AffineDiagonalCenteredCleanupData popular scale) :
    Kakeya.Streamlined.TubeFamily scale.targetDelta :=
  (Kakeya.Streamlined.TubeSubfamily.fromFinset
    data.raw.family data.selected).family

/-- The literal cubical shading on the cleaned family. -/
def shading
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    (data : PureWZ2AffineDiagonalCenteredCleanupData popular scale) :
    WZ1PaperTubeShading data.family :=
  restrictPaperShading
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
      data.raw.family data.selected)
    data.raw.shading

/-- Each cleaned tube retains its genuine source parent in the selected C2
configuration. -/
def sourceParent
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    (data : PureWZ2AffineDiagonalCenteredCleanupData popular scale) :
    Fin data.family.card → Fin band.lemma31.data.cfg.family.card :=
  fun index => data.raw.sourceParent
    ((Kakeya.Streamlined.TubeSubfamily.fromFinset
      data.raw.family data.selected).embedding index)

theorem sourceParent_injective
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    (data : PureWZ2AffineDiagonalCenteredCleanupData popular scale) :
    Function.Injective data.sourceParent := by
  intro first second heq
  apply (Kakeya.Streamlined.TubeSubfamily.fromFinset
    data.raw.family data.selected).embedding.injective
  exact data.raw.sourceParent_injective heq

/-- Exact fully-centered affine axis provenance survives cleanup. -/
theorem axis_ambient
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    (data : PureWZ2AffineDiagonalCenteredCleanupData popular scale)
    (index : Fin data.family.card) :
    tubeAxisLine (data.family.tube index) =
      pureWZ2AffineDiagonalMapCentered
        scale.slopeData.frameSlope data.raw.center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          tubeAxisLine
            (band.lemma31.data.cfg.family.tube
              (data.sourceParent index)) := by
  change tubeAxisLine
      (data.raw.family.tube
        ((Kakeya.Streamlined.TubeSubfamily.fromFinset
          data.raw.family data.selected).embedding index)) = _
  exact data.raw.axis_ambient
    ((Kakeya.Streamlined.TubeSubfamily.fromFinset
      data.raw.family data.selected).embedding index)

/-- The raw-to-cleaned shaded-mass loss in a stable field-free form. -/
theorem raw_mass_le
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    (data : PureWZ2AffineDiagonalCenteredCleanupData popular scale) :
    data.raw.shading.mass ≤
      (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
        data.shading.mass :=
  data.mass_lower

end PureWZ2AffineDiagonalCenteredCleanupData

theorem PureWZ2SubbandPopularBoxData.toAffineDiagonalCenteredCleanup
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scale : PureWZ2AffineDiagonalScaleData subband)
    (hwidthOne : pureWZ2AffineDiagonalConflictWidth scale ≤ 1) :
    Nonempty (PureWZ2AffineDiagonalCenteredCleanupData popular scale) := by
  rcases popular.toAffineDiagonalRawFamily scale with ⟨raw⟩
  let sourceFamily := band.lemma31.data.cfg.family
  let sourceConstant := band.sourceConstant
  let width := pureWZ2AffineDiagonalConflictWidth scale
  let degreeBound := pureWZ2AffineDiagonalConflictDegreeBound scale
  have hheight : 0 < scale.slopeData.heightScale := by
    linarith [scale.height_lower]
  have hsourceVertical : ∀ source : Fin sourceFamily.card,
      (sourceFamily.tube source).direction (2 : Fin 3) ≠ 0 := by
    intro source hzero
    have h := band.lemma31.data.cfg.line_class source |>.vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have htargetVertical : ∀ target : Fin raw.family.card,
      (raw.family.tube target).direction (2 : Fin 3) ≠ 0 := by
    intro target hzero
    have h := raw.line_class target |>.vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have hfiber : ∀ source : Fin sourceFamily.card,
      ((Finset.univ : Finset (Fin raw.family.card)).filter fun target =>
        raw.sourceParent target = source).card ≤ 1 := by
    intro source
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    apply raw.sourceParent_injective
    exact (Finset.mem_filter.mp hfirst).2.trans
      (Finset.mem_filter.mp hsecond).2.symm
  have hFrostman : TubeParameterFrostmanBound sourceFamily
      (3200 * sourceConstant) :=
    paper_tubeParameterFrostmanBound_of_croppedConvexWolff
      band.lemma31.data.cfg.extremal.delta_pos sourceFamily
      band.lemma31.data.cfg.line_class sourceConstant
      band.lemma31.data.cfg.top_level_cwa
  have hwidthPos : 0 < width := by
    dsimp only [width, pureWZ2AffineDiagonalConflictWidth]
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num) (by linarith [scale.height_lower]))
        (by
          have hinvPos : 0 < scale.slopeData.transverseScale⁻¹ :=
            inv_pos.mpr scale.transverse_pos
          linarith))
      (mul_pos (by norm_num) scale.targetDelta_pos)
  have hsourceWidth : delta ≤ width := by
    have hinvNonneg : 0 ≤ scale.slopeData.transverseScale⁻¹ :=
      inv_nonneg.mpr scale.transverse_pos.le
    have hfactor :
        1 ≤ 16 * (1 + scale.slopeData.heightScale) *
          (1 + scale.slopeData.transverseScale⁻¹) * 600 := by
      have hheightOne : 1 ≤ 1 + scale.slopeData.heightScale := by
        linarith [scale.height_lower]
      have hinvOne : 1 ≤ 1 + scale.slopeData.transverseScale⁻¹ := by
        linarith
      calc
        (1 : ℝ) ≤ 16 := by norm_num
        _ ≤ 16 * (1 + scale.slopeData.heightScale) := by nlinarith
        _ ≤ 16 * (1 + scale.slopeData.heightScale) *
            (1 + scale.slopeData.transverseScale⁻¹) := by
              exact le_mul_of_one_le_right
                (mul_nonneg (by norm_num) (by linarith [scale.height_lower]))
                hinvOne
        _ ≤ 16 * (1 + scale.slopeData.heightScale) *
            (1 + scale.slopeData.transverseScale⁻¹) * 600 := by
              exact le_mul_of_one_le_right
                (mul_nonneg
                  (mul_nonneg (by norm_num)
                    (by linarith [scale.height_lower]))
                  (by linarith))
                (by norm_num)
    calc
      delta ≤ scale.targetDelta := scale.source_le_target
      _ ≤ width := by
        dsimp only [width, pureWZ2AffineDiagonalConflictWidth]
        rw [show 16 * (1 + scale.slopeData.heightScale) *
            (1 + scale.slopeData.transverseScale⁻¹) *
              (600 * scale.targetDelta) =
            (16 * (1 + scale.slopeData.heightScale) *
              (1 + scale.slopeData.transverseScale⁻¹) * 600) *
                scale.targetDelta by ring]
        exact (le_mul_iff_one_le_left scale.targetDelta_pos).2 hfactor
  have hdegree : ∀ reference : Fin raw.family.card,
      (((Finset.univ : Finset (Fin raw.family.card)).filter
        (pureWZ2PaperCenteredConflict raw.family reference)).card :
          ENNReal) ≤ degreeBound := by
    have h := affine_centered_conflict_degree_le
      scale.slopeData.frameSlope raw.center
      scale.slopeData.heightScale scale.slopeData.transverseScale
      raw.frame_bound raw.center_height_bound scale.targetDelta_pos
      hheight scale.transverse_pos sourceFamily raw.family raw.sourceParent
      1 hfiber band.lemma31.data.cfg.line_class
      raw.line_class raw.midpoint_local raw.axis_ambient
      hsourceVertical htargetVertical (3200 * sourceConstant)
      sourceFamily.enncard hFrostman width rfl hsourceWidth hwidthOne
    intro reference
    simpa [degreeBound, pureWZ2AffineDiagonalConflictDegreeBound,
      sourceFamily, sourceConstant, width] using h reference
  rcases pureWZ2_paper_weighted_centered_distinct_selection_ennreal
      raw.family raw.shading degreeBound hdegree with
    ⟨selected, hdistinct, hmaximal, hmass⟩
  let selectedFamily :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset raw.family selected
  exact ⟨{
    raw := raw
    conflict_width_le_one := hwidthOne
    selected := selected
    distinct := hdistinct
    maximal := hmaximal
    mass_lower := by
      simpa [degreeBound, pureWZ2AffineDiagonalConflictDegreeBound] using hmass
    line_class := raw.line_class.subfamily selectedFamily
    cubical := restrictPaperShading_cubical selectedFamily raw.cubical
  }⟩

end Kakeya.Assouad

end
