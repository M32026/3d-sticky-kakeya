import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalDistinctCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureExternalWeightRegularization

/-!
# Ambient-source regularization synchronized with the direct half-offset terminal

The terminal cleanup is performed after two genuine restrictions and a centered
representative change.  Nearby-scale CWA is consequently restored on the
original ambient source family by external weights, rather than claimed for an
arbitrary terminal subfamily.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

namespace TerminalGeometry

namespace PureWZ2HalfOffsetTerminalDistinctCleanupData

/-- The actual composite provenance map from a selected centered terminal tube
to the ambient source family. -/
def sourceIndex
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) :
    Fin cleanup.family.family.card ↪
      Fin commonSource.halfOffsetAssembly.cfg.family.card where
  toFun := fun index =>
    (wz2PaperNonemptyCarrierSubfamily
      terminal.retubing.popular.popular.restricted).embedding
      ((wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).embedding
        (cleanup.originalIndex commonSource index))
  inj' := by
    intro first second heq
    apply cleanup.family.embedding.injective
    apply (wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).embedding.injective
    apply (wz2PaperNonemptyCarrierSubfamily
      terminal.retubing.popular.popular.restricted).embedding.injective
    exact heq

theorem sourceIndex_injective
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) :
    Function.Injective cleanup.sourceIndex := by
  exact cleanup.sourceIndex.injective

/-- Retained centered-terminal mass, extended by zero to ambient indices. -/
def sourceWeight
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (index : Fin commonSource.halfOffsetAssembly.cfg.family.card) : ENNReal :=
  ∑ target : Fin cleanup.family.family.card,
    if cleanup.sourceIndex target = index then
      volume (cleanup.shading.carrier target)
    else 0

theorem sourceWeight_sum
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) :
    (∑ index : Fin commonSource.halfOffsetAssembly.cfg.family.card,
      cleanup.sourceWeight index) = cleanup.shading.mass := by
  unfold sourceWeight
  rw [Finset.sum_comm]
  change (∑ target : Fin cleanup.family.family.card,
    ∑ index : Fin commonSource.halfOffsetAssembly.cfg.family.card,
      if cleanup.sourceIndex target = index then
        volume (cleanup.shading.carrier target) else 0) =
      ∑ target : Fin cleanup.family.family.card,
        volume (cleanup.shading.carrier target)
  apply Finset.sum_congr rfl
  intro target _
  rw [Fintype.sum_ite_eq]

/-- The external source weight has the natural terminal tube-area upper
bound.  Injectivity of `sourceIndex` ensures that at most one cleanup carrier
contributes at any ambient source index. -/
theorem sourceWeight_le_terminal_area
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (index : Fin commonSource.halfOffsetAssembly.cfg.family.card) :
    cleanup.sourceWeight index ≤
      (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN terminal.targetDelta 2 := by
  unfold sourceWeight
  by_cases hexists : ∃ target : Fin cleanup.family.family.card,
      cleanup.sourceIndex target = index
  · rcases hexists with ⟨target, htarget⟩
    have hunique : ∀ other : Fin cleanup.family.family.card,
        cleanup.sourceIndex other = index → other = target := by
      intro other hother
      apply cleanup.sourceIndex_injective
      exact hother.trans htarget.symm
    have hcondition : ∀ other : Fin cleanup.family.family.card,
        cleanup.sourceIndex other = index ↔ other = target := by
      intro other
      exact ⟨hunique other, fun heq => heq ▸ htarget⟩
    simp_rw [hcondition]
    rw [Fintype.sum_ite_eq']
    have hsubset : cleanup.shading.carrier target ⊆
        wz1PaperTubeCarrier (cleanup.family.family.tube target) :=
      cleanup.shading.subset_body target
    have hline : WZ1PaperTubeInLineClass
        (cleanup.family.family.tube target) :=
      TerminalGeometry.line_class_subfamily commonSource terminal cleanup.family
        target
    calc
      volume (cleanup.shading.carrier target) ≤
          volume (wz1PaperTubeCarrier
            (cleanup.family.family.tube target)) := measure_mono hsubset
      _ ≤ (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN terminal.targetDelta 2 :=
        (wz2PaperTubeCarrier_convex_and_volume_quadratic
          wz2_paper_tube_carrier_geometry
          commonSource.halfOffsetLineClassTargetDelta_pos
          (commonSource.halfOffsetLineClassTargetDelta_small.le.trans
            (by norm_num))
          (cleanup.family.family.tube target) hline).2
  · have hnone : ∀ target : Fin cleanup.family.family.card,
        cleanup.sourceIndex target ≠ index := by
      intro target heq
      exact hexists ⟨target, heq⟩
    calc
      (∑ target : Fin cleanup.family.family.card,
        if cleanup.sourceIndex target = index then
          volume (cleanup.shading.carrier target) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro target _
        rw [if_neg (hnone target)]
      _ ≤ (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN terminal.targetDelta 2 := bot_le

end PureWZ2HalfOffsetTerminalDistinctCleanupData

/-- External-weight nearby-CWA restoration on the ambient source family. -/
abbrev PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (sourceConstant scheduleConstant normalizationWeight : ENNReal)
    (levelCount : ℕ) :=
  PureWZ2ExternalWeightRegularizationData sourceConstant scheduleConstant
    normalizationWeight
      ((55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN terminal.targetDelta 2)
      levelCount cleanup.sourceWeight

theorem cleanup_source_regularization
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (hsourceConstant : sourceConstant =
      Kakeya.realRpowENN delta (-commonSource.halfOffsetAssembly.technicalLoss))
    (hnormalizationZero : normalizationWeight ≠ 0)
    (hnormalizationTop : normalizationWeight ≠ ⊤)
    (hmass : normalizationWeight *
      commonSource.halfOffsetAssembly.cfg.family.enncard ≤ cleanup.shading.mass)
    (levelCount : ℕ)
    (hsourceTwo : 2 < sourceConstant)
    (hlevels : ENNReal.ofReal (1 / delta) ≤ sourceConstant ^ levelCount)
    (hscheduleFinite : WZ2PaperFiniteErrorConstant scheduleConstant)
    (hscheduleConstant : sourceConstant * sourceConstant ≤ scheduleConstant) :
    Nonempty (PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) := by
  subst sourceConstant
  apply pureWZ2_external_weight_regularization
    commonSource.halfOffsetAssembly.cfg.extremal.cwa_nearby_scales
    commonSource.halfOffsetAssembly.cfg.extremal.nonempty
    commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
    hscheduleFinite hnormalizationZero hnormalizationTop
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      deltaTubeVolume_one_ne_top)
      (by simp [Kakeya.realRpowENN]))
    cleanup.sourceWeight ?_ cleanup.sourceWeight_le_terminal_area levelCount
    hsourceTwo hlevels hscheduleConstant
  rw [cleanup.sourceWeight_sum]
  exact hmass

namespace PureWZ2ExternalWeightRegularizationData

theorem halfOffsetTerminalCleanup_support
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    data.selected.embedding index ∈ Finset.univ.map cleanup.sourceIndex := by
  have hpositive := data.selected_weight_pos index
  unfold PureWZ2HalfOffsetTerminalDistinctCleanupData.sourceWeight at hpositive
  by_contra hnot
  have hnone : ∀ target : Fin cleanup.family.family.card,
      cleanup.sourceIndex target ≠ data.selected.embedding index := by
    intro target heq
    exact hnot (Finset.mem_map.mpr ⟨target, Finset.mem_univ _, heq⟩)
  have hzero : (∑ target : Fin cleanup.family.family.card,
      if cleanup.sourceIndex target = data.selected.embedding index then
        volume (cleanup.shading.carrier target) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro target _
    rw [if_neg (hnone target)]
  rw [hzero] at hpositive
  exact (lt_irrefl 0 hpositive).elim

def halfOffsetTerminalCleanupTargetPreimage
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) : Fin cleanup.family.family.card :=
  (Finset.mem_map.mp
    (halfOffsetTerminalCleanup_support (commonSource := commonSource) data index)).choose

theorem halfOffsetTerminalCleanupTargetPreimage_source
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    cleanup.sourceIndex
      (halfOffsetTerminalCleanupTargetPreimage (commonSource := commonSource)
        data index) =
      data.selected.embedding index :=
  (Finset.mem_map.mp
    (halfOffsetTerminalCleanup_support (commonSource := commonSource) data index)).choose_spec.2

def halfOffsetTerminalCleanupTargetSubfamily
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :
      Kakeya.Streamlined.TubeSubfamily cleanup.family.family where
  family :=
    { card := data.selected.family.card
      tube := fun index => cleanup.family.family.tube
        (halfOffsetTerminalCleanupTargetPreimage (commonSource := commonSource)
          data index) }
  embedding :=
    { toFun := halfOffsetTerminalCleanupTargetPreimage (commonSource := commonSource) data
      inj' := by
        intro first second heq
        apply data.selected.embedding.injective
        rw [← halfOffsetTerminalCleanupTargetPreimage_source
              (commonSource := commonSource) data first,
          ← halfOffsetTerminalCleanupTargetPreimage_source
              (commonSource := commonSource) data second, heq] }
  tube_eq _ := rfl

def halfOffsetTerminalCleanupTargetShading
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) : WZ1PaperTubeShading
      (halfOffsetTerminalCleanupTargetSubfamily (commonSource := commonSource)
        data).family :=
  restrictPaperShading
    (halfOffsetTerminalCleanupTargetSubfamily (commonSource := commonSource) data)
    cleanup.shading

theorem halfOffsetTerminalCleanupTargetSubfamily_distinct
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) : WZ2PaperOrdinaryIsEssentiallyDistinct
      (halfOffsetTerminalCleanupTargetSubfamily (commonSource := commonSource)
        data).family := by
  let selected : WZ2PaperPureTubeSubfamily cleanup.family.family :=
    { family := (halfOffsetTerminalCleanupTargetSubfamily
        (commonSource := commonSource) data).family
      embedding := (halfOffsetTerminalCleanupTargetSubfamily
        (commonSource := commonSource) data).embedding
      tube_eq := (halfOffsetTerminalCleanupTargetSubfamily
        (commonSource := commonSource) data).tube_eq }
  exact cleanup.distinct.subfamily selected

theorem halfOffsetTerminalCleanupTargetSubfamily_cubical
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) : WZ1PaperIsCubicalShading
      (halfOffsetTerminalCleanupTargetShading
        (commonSource := commonSource) data) := by
  exact restrictPaperShading_cubical
    (halfOffsetTerminalCleanupTargetSubfamily (commonSource := commonSource) data)
    (TerminalGeometry.cubical_subfamily commonSource terminal cleanup.family)

theorem halfOffsetTerminalCleanupTargetSubfamily_nonempty
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :
      (halfOffsetTerminalCleanupTargetSubfamily (commonSource := commonSource)
        data).family.Nonempty := by
  change 0 < data.selected.family.card
  exact data.selected_nonempty

theorem halfOffsetTerminalCleanupTargetSubfamily_carrier_subset
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    (halfOffsetTerminalCleanupTargetShading (commonSource := commonSource) data).carrier index ⊆
      cleanup.shading.carrier
        ((halfOffsetTerminalCleanupTargetSubfamily (commonSource := commonSource)
          data).embedding index) := by
  rfl

end PureWZ2ExternalWeightRegularizationData

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
