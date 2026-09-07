import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectSourceRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicRetubingSubfamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactPlaneMapSubfamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperCenteredCleanup
import MyLeanRepo.Kakeya.Assouad.Targets.AnisotropicTubeParamsInverseCluster

/-!
# Exact triangular retubing on the direct regularized source

Positive external mass factors the first nearby-CWA selection through the
nonempty-carrier family used by the direct exact retubing.  All source
geometry and local grains are then restricted along that literal factor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The packed nonempty-carrier index of a positive selected direct source. -/
def pureWZ2DirectPackedIndex
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount)
    (index : Fin regularized.selected.family.card) :
    Fin retubing.popular.family.card :=
  let indices := wz2PaperNonemptyCarrierIndices
    retubing.popular.popular.restricted
  (indices.orderIsoOfFin rfl).symm
    ⟨regularized.selected.embedding index, by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hempty
      have hset : retubing.popular.popular.restricted.carrier
          (regularized.selected.embedding index) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hempty
      have hweight := regularized.selected_weight_pos index
      simp [pureWZ2DirectPopularSourceWeight, hset] at hweight⟩

@[simp] theorem pureWZ2DirectPackedIndex_ambient
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount)
    (index : Fin regularized.selected.family.card) :
    (wz2PaperNonemptyCarrierSubfamily
        retubing.popular.popular.restricted).embedding
        (pureWZ2DirectPackedIndex retubing regularized index) =
      regularized.selected.embedding index := by
  unfold pureWZ2DirectPackedIndex wz2PaperNonemptyCarrierSubfamily
    Kakeya.Streamlined.TubeSubfamily.fromFinset
  exact congrArg Subtype.val
    (((wz2PaperNonemptyCarrierIndices retubing.popular.popular.restricted)
      |>.orderIsoOfFin rfl).apply_symm_apply _)

/-- The selected ambient source family as a genuine subfamily of the direct
nonempty-carrier family. -/
def PureWZ2ExternalWeightRegularizationData.toDirectNonemptySubfamily
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) :
    Kakeya.Streamlined.TubeSubfamily retubing.popular.family := by
  exact
    { family := regularized.selected.family
      embedding :=
        { toFun := pureWZ2DirectPackedIndex retubing regularized
          inj' := fun first second heq => by
            apply regularized.selected.embedding.injective
            rw [← pureWZ2DirectPackedIndex_ambient retubing regularized first,
              ← pureWZ2DirectPackedIndex_ambient retubing regularized second,
              heq] }
      tube_eq := fun index => by
        change regularized.selected.family.tube index =
          assembly.cfg.family.tube
            ((wz2PaperNonemptyCarrierSubfamily
              retubing.popular.popular.restricted).embedding
                (pureWZ2DirectPackedIndex retubing regularized index))
        rw [pureWZ2DirectPackedIndex_ambient,
          regularized.selected.tube_eq] }

/-- Literal open source shading on the first regularized source family. -/
def pureWZ2DirectRegularizedSourceShading
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) :
    WZ1PaperTubeShading regularized.selected.family :=
  restrictPaperShading (regularized.toDirectNonemptySubfamily retubing)
    retubing.popular.openSourceShading

/-- The direct local grains restricted by exactly the same selected indices. -/
def PureWZ2ExternalWeightRegularizationData.directRegularizedSourceLocalGrains
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) :
    PureWZ2LocalGrainData
      (pureWZ2DirectRegularizedSourceShading retubing regularized) sigma
      (Kakeya.realRpowENN delta (-assembly.technicalLoss)) :=
  retubing.popular.openSourceLocalGrains.subfamily
    (regularized.toDirectNonemptySubfamily retubing)

/-- Restrict the direct exact retubing to the source family already carrying
nearby-scale CWA. -/
def PureWZ2DirectAnisotropicRetubingData.regularizedRaw
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) :=
  retubing.raw.subfamily (regularized.toDirectNonemptySubfamily retubing)

/-- Restrict the exact inverse-transpose plane map by the identical source
selection. -/
def PureWZ2AnisotropicExactPlaneMapData.directRegularized
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    (exact : PureWZ2AnisotropicExactPlaneMapData retubing.raw
      retubing.popular.openSourceLocalGrains)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) :
    PureWZ2AnisotropicExactPlaneMapData
      (retubing.regularizedRaw regularized)
      (regularized.directRegularizedSourceLocalGrains retubing) :=
  exact.subfamily (regularized.toDirectNonemptySubfamily retubing)

@[simp] theorem pureWZ2DirectRegularizedSourceShading_mass
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) :
    (pureWZ2DirectRegularizedSourceShading retubing regularized).mass =
      regularized.selectedWeight := by
  rw [regularized.selectedWeight_eq]
  apply Finset.sum_congr rfl
  intro index _
  change volume
      (retubing.popular.sourceShading.carrier
          ((regularized.toDirectNonemptySubfamily retubing).embedding index) \
        {point : Point3 | point 2 = assembly.horizontalSource.d}) =
    volume (retubing.popular.popular.restricted.carrier
      (regularized.selected.embedding index))
  rw [measure_diff_null
    (volume_coordinate_hyperplane_zero 2 assembly.horizontalSource.d)]
  rw [retubing.popular.source_carrier_eq]
  change volume (retubing.popular.popular.restricted.carrier
      ((wz2PaperNonemptyCarrierSubfamily
        retubing.popular.popular.restricted).embedding
          ((regularized.toDirectNonemptySubfamily retubing).embedding index))) = _
  congr 2
  exact pureWZ2DirectPackedIndex_ambient retubing regularized index

/-- The first dyadic weight floor gives a per-tube mass floor on the exact
regularized source shading. -/
theorem PureWZ2ExternalWeightRegularizationData.directSelectedWeightLevel_mul_card_le_sourceMass
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) :
    regularized.selectedWeightLevel * regularized.selected.family.enncard ≤
      (pureWZ2DirectRegularizedSourceShading retubing regularized).mass := by
  rw [pureWZ2DirectRegularizedSourceShading_mass]
  rw [regularized.selectedWeight_eq]
  calc
    regularized.selectedWeightLevel * regularized.selected.family.enncard =
        ∑ _index : Fin regularized.selected.family.card,
          regularized.selectedWeightLevel := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
      ring
    _ ≤ ∑ index : Fin regularized.selected.family.card,
        pureWZ2DirectPopularSourceWeight retubing.popular
          (regularized.selected.embedding index) :=
      Finset.sum_le_sum fun index _ =>
        (regularized.selected_weight_band index).1

/-- Top-level source CWA after the first direct external-weight selection. -/
def pureWZ2DirectRegularizedSourceTopConstant
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) : ENNReal :=
  ((pureWZ2DirectPopularSourceNormalization assembly.horizontalSource)⁻¹ *
      regularized.retentionConstant) *
    Kakeya.realRpowENN delta (-assembly.technicalLoss)

/-- Centered cleanup of the regularized direct exact target. -/
theorem PureWZ2DirectAnisotropicRetubingData.toRegularizedCenteredCleanup
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) :
    Nonempty (PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)) := by
  let source := assembly.horizontalSource
  let targetDelta := anisotropicPaperAlignedScale delta source.c source.d
  let sourceConstant :=
    pureWZ2DirectRegularizedSourceTopConstant retubing regularized
  have hsourceScale : source.source_length = assembly.rho.1 := by
    simpa [source] using assembly.horizontalSource_scale
  have hsourceTop : WZ2PaperConvexWolffBound regularized.selected.family
      sourceConstant := by
    exact regularized.top_level_cwa assembly.cfg.top_level_cwa
      (pureWZ2DirectPopularSourceNormalization_pos source).ne'
      (pureWZ2DirectPopularSourceNormalization_ne_top source)
  have hlength : source.d - source.c = assembly.rho.1 / 100 := by
    rw [source.length_eq, hsourceScale]
  have hlengthPos : 0 < source.d - source.c :=
    sub_pos.mpr source.ordered
  have hrawPos : 0 < anisotropicPaperRawScale delta source.c source.d := by
    unfold anisotropicPaperRawScale
    exact div_pos (mul_pos (by norm_num) assembly.cfg.extremal.delta_pos)
      hlengthPos
  have hrawEq : anisotropicPaperRawScale delta source.c source.d =
      1600 * delta / assembly.rho.1 := by
    unfold anisotropicPaperRawScale
    rw [hlength]
    field_simp [show assembly.rho.1 ≠ 0 by
      exact ne_of_gt (assembly.cfg.extremal.delta_pos.trans_le
        assembly.rho.2.1)]
    ring
  have hrawHalf : anisotropicPaperRawScale delta source.c source.d ≤
      1 / 2 := by
    rw [hrawEq, div_le_iff₀
      (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1)]
    have hfactor : 0 ≤ (1 / 2 : ℝ) - 1600 * assembly.rho.1 := by
      linarith [assembly.rho_tiny]
    nlinarith [assembly.delta_le_rho_sq,
      mul_nonneg
        (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1).le
        hfactor]
  have htargetPos : 0 < targetDelta :=
    anisotropicPaperAlignedScale_pos hrawPos hrawHalf
  have hsourceWidth : delta ≤ anisotropicPaperConflictWidth targetDelta
      source.c source.d source.m := by
    unfold anisotropicPaperConflictWidth
    have htarget : delta ≤ targetDelta := by
      have hrawTarget := anisotropicPaperRawScale_le_aligned
        hrawPos hrawHalf
      unfold anisotropicPaperRawScale at hrawTarget
      have hlengthOne : source.d - source.c ≤ 16 := by
        rw [hlength]
        linarith [assembly.rho_tiny]
      calc
        delta ≤ 16 * delta / (source.d - source.c) := by
          rw [le_div_iff₀ hlengthPos]
          nlinarith [assembly.cfg.extremal.delta_pos]
        _ ≤ targetDelta := hrawTarget
    have hdenom : 0 < source.m * (source.d - source.c) ^ 2 :=
      mul_pos source.slopeScale_pos (sq_pos_of_pos hlengthPos)
    rw [le_div_iff₀ hdenom]
    have hlengthOne : source.d - source.c ≤ 1 := by
      rw [hlength]
      linarith [assembly.rho_tiny]
    have hdenomOne : source.m * (source.d - source.c) ^ 2 ≤ 1 := by
      have hsquare : (source.d - source.c) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg ((source.d - source.c) - 1)]
      exact (mul_le_mul source.slopeScale_le_one hsquare
        (sq_nonneg _) (by norm_num)).trans_eq (by norm_num)
    nlinarith
  have hwidthOne : anisotropicPaperConflictWidth targetDelta
      source.c source.d source.m ≤ 1 := by
    unfold anisotropicPaperConflictWidth
    have htargetUpper : targetDelta <
        32 * delta / (source.d - source.c) := by
      exact (anisotropicPaperAlignedScale_lt_two_mul_raw
        hrawPos hrawHalf).trans_eq <| by
          unfold anisotropicPaperRawScale
          ring
    have hdenom : 0 < source.m * (source.d - source.c) ^ 2 :=
      mul_pos source.slopeScale_pos (sq_pos_of_pos hlengthPos)
    rw [div_le_iff₀ hdenom]
    simp only [one_mul]
    have hrhoPos : 0 < assembly.rho.1 :=
      assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1
    have hrhoOne : assembly.rho.1 ≤ 1 :=
      assembly.rho_tiny.trans (by norm_num)
    have htargetTimesLength :
        targetDelta * (source.d - source.c) < 32 * delta :=
      (lt_div_iff₀ hlengthPos).mp htargetUpper
    have hrhoFour : assembly.rho.1 ^ 4 ≤ (1 / 6400 : ℝ) ^ 4 := by
      exact pow_le_pow_left₀ hrhoPos.le assembly.rho_tiny 4
    have hconstantRhoFour :
        (1920000000000 : ℝ) * assembly.rho.1 ^ 4 ≤ 1 := by
      calc
        (1920000000000 : ℝ) * assembly.rho.1 ^ 4 ≤
            1920000000000 * (1 / 6400 : ℝ) ^ 4 := by gcongr
        _ ≤ 1 := by norm_num
    have hscaledPower :
        (1920000000000 : ℝ) * assembly.rho.1 ^ 8 ≤
          assembly.rho.1 ^ 4 := by
      calc
        (1920000000000 : ℝ) * assembly.rho.1 ^ 8 =
            ((1920000000000 : ℝ) * assembly.rho.1 ^ 4) *
              assembly.rho.1 ^ 4 := by ring
        _ ≤ 1 * assembly.rho.1 ^ 4 :=
          mul_le_mul_of_nonneg_right hconstantRhoFour (by positivity)
        _ = assembly.rho.1 ^ 4 := by ring
    have hscaledDelta :
        (1920000000000 : ℝ) * delta ≤ assembly.rho.1 ^ 4 :=
      (mul_le_mul_of_nonneg_left assembly.delta_le_rho_eight
        (by norm_num)).trans hscaledPower
    have hcore : 1920000 * delta ≤
        source.m * (source.d - source.c) ^ 3 := by
      rw [hlength]
      have hleft : 1920000 * delta ≤ assembly.rho.1 ^ 4 / 1000000 := by
        calc
          1920000 * delta =
              ((1920000000000 : ℝ) * delta) / 1000000 := by ring
          _ ≤ assembly.rho.1 ^ 4 / 1000000 :=
            div_le_div_of_nonneg_right hscaledDelta (by norm_num)
      have hright : assembly.rho.1 ^ 4 / 1000000 ≤
          source.m * (assembly.rho.1 / 100) ^ 3 := by
        rw [show (assembly.rho.1 / 100) ^ 3 =
            assembly.rho.1 ^ 3 / 1000000 by ring]
        rw [show source.m * (assembly.rho.1 ^ 3 / 1000000) =
            (source.m * assembly.rho.1 ^ 3) / 1000000 by ring]
        apply div_le_div_of_nonneg_right _ (by norm_num)
        have hrhoM : assembly.rho.1 ≤ source.m := by
          rw [← hsourceScale]
          exact source.slopeScale_lower
        calc
          assembly.rho.1 ^ 4 = assembly.rho.1 * assembly.rho.1 ^ 3 := by ring
          _ ≤ source.m * assembly.rho.1 ^ 3 :=
            mul_le_mul_of_nonneg_right hrhoM (by positivity)
      exact hleft.trans hright
    apply le_of_mul_le_mul_right _ hlengthPos
    calc
      (100 * (600 * targetDelta)) * (source.d - source.c) ≤
          1920000 * delta := by
        calc
          (100 * (600 * targetDelta)) * (source.d - source.c) =
              60000 * (targetDelta * (source.d - source.c)) := by ring
          _ ≤ 60000 * (32 * delta) :=
            mul_le_mul_of_nonneg_left htargetTimesLength.le (by norm_num)
          _ = 1920000 * delta := by ring
      _ ≤ source.m * (source.d - source.c) ^ 3 := hcore
      _ = (source.m * (source.d - source.c) ^ 2) *
          (source.d - source.c) := by ring
  have hdcOne : source.d - source.c ≤ 1 := by
    rw [hlength]
    linarith [assembly.rho_tiny]
  have hgmid :
      |pureWZ2DirectGeometrySlope source
        (source.c + (source.d - source.c) / 2)| ≤ 1 :=
    (retubing.geometrySlope_normalized _
      (retubing.interval_sub_unit ⟨by linarith [source.ordered],
        by linarith [source.ordered]⟩)).1
  exact (retubing.regularizedRaw regularized).toCenteredCleanup
    anisotropic_tube_params_inverse_cluster hdcOne
    retubing.interval_sub_unit source.slopeScale_le_one hgmid
    assembly.cfg.extremal.delta_pos htargetPos
    (assembly.cfg.line_class.subfamily regularized.selected)
    sourceConstant hsourceTop hsourceWidth hwidthOne

end Kakeya.Assouad

end
