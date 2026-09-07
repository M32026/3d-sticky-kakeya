import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BaseConfig

/-!
# Combined base config + sticky provision (Node 4)

This module provides a theorem that combines the base config extraction with
the sticky provision derivation. It calls Node 3 FIRST to determine the
required input loss, then normalizes at that exact loss, ensuring compatibility
between the source/normalized data and Node 3's requirements.

## The problem with separate calls

Calling `pure_wz2_grain_base_config` and then `sticky_provision_for_normalized`
separately fails because:
1. Node 3 (`PureWZ2CroppedPropStickyAt`) requires source at its existential
   `inputLoss` and normalized data with `outputLoss := inputLoss`.
2. The normalization statement produces source at `inputLoss_norm ≤ outputLoss`
   and normalized at `outputLoss`.
3. There is no guarantee `inputLoss_norm = inputLoss_node3`.

## Solution

1. Call Node 3 with `outputLoss' := normLoss` → get `inputLoss_sticky`, `delta₀_sticky`
2. Call normalization with `outputLoss := inputLoss_sticky`, `delta₀ := min(external, delta₀_sticky)`
3. Weaken source from `inputLoss_norm` to `inputLoss_sticky`
4. Rebase normalized data onto the weakened source
5. Weaken normalized fields to `normLoss` for the base config
6. Node 3 gives sticky data at `normLoss`; weaken to `outputLoss` for the provision
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory ENNReal

attribute [local instance] Classical.propDecidable

/-- Restricted sticky provision: only requires data for rho in the grid range
`[δ^(1-outputLoss), δ^outputLoss]` and a fixed logExponent. This matches what
Node 3 actually provides and what consumers actually need. -/
def PureWZ2RestrictedStickyProvisionFor
    (delta : ℝ) (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : WZ1PaperTubeShading F)
    (sigma outputLoss : ℝ) (logExponent : ℕ) : Prop :=
  ∀ (rho : WZ2PaperRequestedScale delta),
    Real.rpow delta (1 - outputLoss) ≤ rho.1 →
    rho.1 ≤ Real.rpow delta outputLoss →
    Nonempty (PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      (sourceShading := Y) rho logExponent)

/-- Weaken a restricted sticky provision from `loss1` to `loss2` where `loss1 ≤ loss2`.

Since `delta < 1`, the scale range `[δ^(1-loss2), δ^loss2]` is a subset of
`[δ^(1-loss1), δ^loss1]`, so every scale in the target range is already covered
by the source provision. The sticky data itself is weakened via `mono_loss`. -/
lemma PureWZ2RestrictedStickyProvisionFor.mono_loss
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    {sigma loss1 loss2 : ℝ} {logExponent : ℕ}
    (h : PureWZ2RestrictedStickyProvisionFor delta F Y sigma loss1 logExponent)
    (hle : loss1 ≤ loss2)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1) :
    PureWZ2RestrictedStickyProvisionFor delta F Y sigma loss2 logExponent := by
  intro rho hlower2 hupper2
  have h1 : Real.rpow delta (1 - loss1) ≤ Real.rpow delta (1 - loss2) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (by linarith)
  have h2 : Real.rpow delta loss2 ≤ Real.rpow delta loss1 :=
    Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one hle
  have hlower1 : Real.rpow delta (1 - loss1) ≤ rho.1 := h1.trans hlower2
  have hupper1 : rho.1 ≤ Real.rpow delta loss1 := hupper2.trans h2
  rcases h rho hlower1 hupper1 with ⟨data⟩
  exact ⟨data.mono_loss hle⟩

/-- Obtain the base pair and reusable sticky provision from one synchronized
Node 3 realization.  The ordinary source, normalization, and all-scale output
are fields of the same dependent witness. -/
theorem pure_wz2_grain_base_config_with_sticky_pair_at
    {nE lE : ℕ}
    (hRealizationAt : PureWZ2PropStickyRealizationAt nE lE)
    (sigma : ℝ)
    (hcrit : PureWZ2CriticalPackage sigma)
    (normLoss outputLoss external_delta₀ : ℝ)
    (hnorm_loss_pos : 0 < normLoss)
    (hnorm_le_output : normLoss ≤ outputLoss)
    (hloss : 0 < outputLoss)
    (hexternal_delta₀_pos : 0 < external_delta₀) :
    ∃ (sourceLoss normalizationLoss delta_n : ℝ)
      (source : PureWZ2ExtremalConfiguration sigma sourceLoss delta_n)
      (normalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := normalizationLoss) source nE)
      (base : PureWZ2GrainBaseConfig sigma normLoss delta_n)
      (hNormProvision : PureWZ2RestrictedStickyProvisionFor
          delta_n base.family base.shading
          sigma normLoss lE)
      (hProvision : PureWZ2RestrictedStickyProvisionFor
          delta_n base.family base.shading
          sigma outputLoss lE),
      0 < sourceLoss ∧ 0 < normalizationLoss ∧ 0 < delta_n ∧
      delta_n ≤ external_delta₀ ∧
      base.family = normalized.croppedFamily ∧
      HEq base.shading normalized.croppedRefined := by
  rcases hRealizationAt sigma hcrit normLoss external_delta₀
      hnorm_loss_pos hexternal_delta₀_pos with ⟨root⟩
  have hnormalization_le_norm : root.normalizationLoss ≤ normLoss :=
    root.normalizationLoss_lt_continuation.le.trans
      root.continuationLoss_lt_output.le
  have hbase_ext : WZ2PaperCroppedIsExtremal sigma normLoss
      root.normalized.croppedFamily root.normalized.croppedRefined :=
    root.normalized.final_extremal.mono_loss hnormalization_le_norm
  have hbase_cwa : WZ2PaperConvexWolffBound root.normalized.croppedFamily
        (Kakeya.realRpowENN root.delta (-normLoss)) := by
    have h : Kakeya.realRpowENN root.delta (-root.normalizationLoss) ≤
          Kakeya.realRpowENN root.delta (-normLoss) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge root.delta_pos
        root.normalized.final_extremal.delta_le_one (by linarith)
    intro convexSet hconv
    have h' := root.normalized.cropped_top_level_cwa convexSet hconv
    exact h'.trans (by gcongr)
  let base : PureWZ2GrainBaseConfig sigma normLoss root.delta :=
    { family := root.normalized.croppedFamily
      shading := root.normalized.croppedRefined
      line_class := root.normalized.line_class
      cubical := root.normalized.cropped_cubical
      extremal := hbase_ext
      top_level_cwa := hbase_cwa }
  have hNormProvision : PureWZ2RestrictedStickyProvisionFor
      root.delta base.family base.shading
      sigma normLoss lE := by
    intro rho hrho_lower hrho_upper
    have hlower : Real.rpow root.delta (1 - root.continuationLoss) ≤ rho.1 :=
      (Real.rpow_le_rpow_of_exponent_ge root.delta_pos
        root.normalized.final_extremal.delta_le_one
        (by linarith [root.continuationLoss_lt_output])).trans
        hrho_lower
    have hupper : rho.1 ≤ Real.rpow root.delta root.continuationLoss :=
      hrho_upper.trans <| Real.rpow_le_rpow_of_exponent_ge root.delta_pos
        root.normalized.final_extremal.delta_le_one
        root.continuationLoss_lt_output.le
    exact root.output rho hlower hupper
  have hProvision : PureWZ2RestrictedStickyProvisionFor
      root.delta base.family base.shading
      sigma outputLoss lE :=
    hNormProvision.mono_loss hnorm_le_output root.delta_pos
      root.normalized.final_extremal.delta_le_one
  exact ⟨root.sourceLoss, root.normalizationLoss, root.delta, root.source,
    root.normalized, base,
    hNormProvision, hProvision,
    root.sourceLoss_pos, root.normalizationLoss_pos, root.delta_pos,
    root.delta_le_ceiling, rfl, HEq.rfl⟩

/-- Compatibility wrapper returning only the weakened `outputLoss` provision.

The pair producer above deliberately also preserves the stronger `normLoss`
view.  Existing consumers that need only the historical interface can keep
using this theorem unchanged. -/
theorem pure_wz2_grain_base_config_with_sticky_at
    {nE lE : ℕ}
    (hRealizationAt : PureWZ2PropStickyRealizationAt nE lE)
    (sigma : ℝ)
    (hcrit : PureWZ2CriticalPackage sigma)
    (normLoss outputLoss external_delta₀ : ℝ)
    (hnorm_loss_pos : 0 < normLoss)
    (hnorm_le_output : normLoss ≤ outputLoss)
    (hloss : 0 < outputLoss)
    (hexternal_delta₀_pos : 0 < external_delta₀) :
    ∃ (sourceLoss normalizationLoss delta_n : ℝ)
      (source : PureWZ2ExtremalConfiguration sigma sourceLoss delta_n)
      (normalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := normalizationLoss) source nE)
      (base : PureWZ2GrainBaseConfig sigma normLoss delta_n)
      (hProvision : PureWZ2RestrictedStickyProvisionFor
          delta_n base.family base.shading
          sigma outputLoss lE),
      0 < sourceLoss ∧ 0 < normalizationLoss ∧ 0 < delta_n ∧
      delta_n ≤ external_delta₀ ∧
      base.family = normalized.croppedFamily ∧
      HEq base.shading normalized.croppedRefined := by
  rcases pure_wz2_grain_base_config_with_sticky_pair_at
      hRealizationAt sigma hcrit normLoss outputLoss external_delta₀
      hnorm_loss_pos hnorm_le_output hloss hexternal_delta₀_pos with
    ⟨sourceLoss, normalizationLoss, delta_n, source, normalized, base,
      _hNormProvision, hProvision, hsourceLoss_pos, hnormalizationLoss_pos,
      hdelta_n_pos, hdelta_n_le, hbase_family, hbase_shading⟩
  exact ⟨sourceLoss, normalizationLoss, delta_n, source, normalized, base,
    hProvision, hsourceLoss_pos, hnormalizationLoss_pos, hdelta_n_pos,
    hdelta_n_le, hbase_family, hbase_shading⟩

/-- Wrapper that unpacks the unified Node 3 capability before applying the
quantifier-safe producer. -/
theorem pure_wz2_grain_base_config_with_sticky
    (h_sticky : PureWZ2PropStickyStatement)
    (h_subunit : PureWZ2SubunitPackageStatement)
    (h_extraction : PureWZ2CriticalExtractionStatement)
    (sigma : ℝ)
    (hcrit : PureWZ2CriticalPackage sigma)
    (normLoss outputLoss external_delta₀ : ℝ)
    (hnorm_loss_pos : 0 < normLoss)
    (hnorm_le_output : normLoss ≤ outputLoss)
    (hloss : 0 < outputLoss)
    (hexternal_delta₀_pos : 0 < external_delta₀) :
    ∃ (nE lE : ℕ) (sourceLoss normalizationLoss delta_n : ℝ)
      (source : PureWZ2ExtremalConfiguration sigma sourceLoss delta_n)
      (normalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := normalizationLoss) source nE)
      (base : PureWZ2GrainBaseConfig sigma normLoss delta_n)
      (hStickyAt : PureWZ2CroppedPropStickyAt nE lE)
      (hProvision : PureWZ2RestrictedStickyProvisionFor
          delta_n base.family base.shading sigma outputLoss lE),
      0 < sourceLoss ∧ 0 < normalizationLoss ∧ 0 < delta_n ∧
      delta_n ≤ external_delta₀ ∧
      base.family = normalized.croppedFamily ∧
      HEq base.shading normalized.croppedRefined := by
  rcases h_sticky h_subunit h_extraction with ⟨capability⟩
  rcases pure_wz2_grain_base_config_with_sticky_at
      capability.realization sigma hcrit normLoss outputLoss external_delta₀
      hnorm_loss_pos hnorm_le_output hloss hexternal_delta₀_pos with
    ⟨sourceLoss, normalizationLoss, delta_n, source, normalized, base,
      hProvision, hsourceLoss_pos, hnormalizationLoss_pos, hdelta_n_pos,
      hdelta_n_le, hbase_family, hbase_shading⟩
  exact ⟨capability.normalizationExponent, capability.logExponent, sourceLoss,
    normalizationLoss, delta_n, source, normalized, base,
    capability.continuation, hProvision, hsourceLoss_pos,
    hnormalizationLoss_pos, hdelta_n_pos, hdelta_n_le, hbase_family,
    hbase_shading⟩

end Kakeya.Assouad

end
