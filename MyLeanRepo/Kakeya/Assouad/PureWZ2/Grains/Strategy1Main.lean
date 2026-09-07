import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BaseConfigWithSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleTubeGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleTubeAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleTubeCWANearby
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Tactic

/-!
# Strategy 1: Main theorem for outputLoss ≥ 2

This module proves `PureWZ2GrainsFromCriticalStatement` for the range
`outputLoss ≥ 2` using the single-tube assembly.

## Proof structure

1. From the critical package, derive sticky data (`hNormAt`, `hStickyAt`)
2. Use `pure_wz2_grain_base_config_with_sticky_at` to get a base configuration
   (F, S, line_class, cubical, extremal, top_level_cwa) at `loss_src = outputLoss`
3. Use `exists_tube_satisfying_density` to select a tube with density bound
4. Apply `single_tube_assembly` with `hcwa_nearby` to get the grain config
5. Return the configuration

## Dependencies

- `hcwa_nearby`: direct self-cover nearby-scales CWA for the single-tube family
  (`single_tube_cwa_nearby` in `SingleTubeCWANearby.lean`) — COMPLETE
- Direction handling: SOLVED via `single_tube_local_grain_data_gen` (vertical case)

## Direction handling

The `hdir_nonzero` requirement has been ELIMINATED. The generalized
`single_tube_local_grain_data_gen` handles both horizontal-nonzero tubes and
perfectly vertical tubes (direction = (0,0,±1)), using `(1,0,0)` as the
perpendicular in the vertical case.

## Target wiring

In `PureWZ2Node04Grains.lean`, case split on `outputLoss ≥ 2`:
- `≥ 2`: use `pure_wz2_strategy1_main`
- `< 2`: use Strategy 2 (dilation path, still has gaps)
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set MeasureTheory Classical

attribute [local instance] Classical.propDecidable

/-- Strategy 1 main theorem: construct a grain configuration for outputLoss ≥ 2.

Takes the same inputs as `PureWZ2GrainsFromCriticalStatement` plus the
remaining hypothesis `hcwa_nearby` for the selected tube.

The horizontal-direction condition is handled internally by
`single_tube_local_grain_data_gen` (vertical tubes use `(1,0,0)`).

Uses `single_tube_cwa_nearby` for the nearby-scales CWA. -/
theorem pure_wz2_strategy1_main
    (h_subunit : PureWZ2SubunitPackageStatement)
    (h_extraction : PureWZ2CriticalExtractionStatement)
    (h_sticky : PureWZ2PropStickyStatement)
    (sigma : ℝ)
    (hcrit : PureWZ2CriticalPackage sigma)
    (outputLoss delta₀ : ℝ)
    (hloss_pos : 0 < outputLoss)
    (houtputLoss_ge_two : 2 ≤ outputLoss)
    (hdelta₀_pos : 0 < delta₀) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
      Nonempty (PureWZ2GrainConfiguration sigma outputLoss delta) := by
  -- Unpack Node 3 sticky data
  rcases h_sticky h_subunit h_extraction with ⟨capability⟩
  have h_sticky_from_crit : PureWZ2PropStickyFromCriticalStatement :=
    capability.toLegacyFromCritical
  rcases h_sticky_from_crit with
    ⟨nE, lE, hNormAt, hStickyAt, _realizationAt⟩

  -- Choose delta₀' small enough for all conditions
  let delta₀' : ℝ := min delta₀ (1 / 12)
  have hdelta₀'_pos : 0 < delta₀' := by positivity
  have hdelta₀'_le : delta₀' ≤ delta₀ := min_le_left _ _
  have hdelta₀'_small : delta₀' ≤ 1 / 12 := min_le_right _ _

  -- Step 1: Get base config at outputLoss (no loss weakening needed)
  rcases pure_wz2_grain_base_config_with_sticky_at
      _realizationAt sigma hcrit
      outputLoss outputLoss delta₀'
      hloss_pos (le_refl outputLoss) hloss_pos hdelta₀'_pos with
    ⟨_sourceLoss, _normalizationLoss, delta_n, _source, _normalized,
      ⟨family, shading, line_class, cubical, extremal, top_level_cwa⟩, hProvision,
      _sourceLoss_pos, _normalizationLoss_pos, hdelta_n_pos, hdelta_n_le,
      _hbase_family, _hbase_shading⟩
  let F := family
  let S := shading

  have hdelta_n_small : delta_n ≤ 1 / 12 :=
    hdelta_n_le.trans hdelta₀'_small
  have hdelta_n_le_one : delta_n ≤ 1 := by linarith

  -- Step 2: Select a tube with density bound
  have h_dense : S.IsLambdaDense (Kakeya.realRpowENN delta_n outputLoss) :=
    extremal.dense
  have h_nonempty : F.Nonempty := extremal.nonempty
  rcases exists_tube_satisfying_density h_dense h_nonempty with ⟨i, hdense_i⟩

  -- Step 3: Gather hypotheses for single_tube_assembly
  let hmeas : MeasurableSet (S.carrier i) := S.measurable_carrier i
  let hsub : S.carrier i ⊆ wz1PaperTubeCarrier (F.tube i) := S.subset_body i
  let hline : WZ1PaperIsLineClass F := line_class
  let hcub : WZ1PaperIsCubicalShading S := cubical
  let hvol : volume S.union ≤ Kakeya.realRpowENN delta_n (sigma - outputLoss) :=
    extremal.volume_upper
  let hdir_vertical : 1 / 2 ≤ |(F.tube i).direction (2 : Fin 3)| :=
    (hline i).vertical
  let hcwa_nearby : WZ2PaperPureCWAAtNearbyScales
      (singleTubeFamily i)
      (Kakeya.realRpowENN delta_n (-outputLoss)) :=
    single_tube_cwa_nearby (F.tube i) hdelta_n_pos hdelta_n_le_one houtputLoss_ge_two hdelta_n_small

  -- Step 4: Assemble the grain configuration
  let config : PureWZ2GrainConfiguration sigma outputLoss delta_n :=
    single_tube_assembly
      i hmeas hsub hline hcub hdense_i hvol
      hdelta_n_pos hdelta_n_le_one houtputLoss_ge_two
      hdir_vertical hdelta_n_small
      hcwa_nearby
      hcrit.sigma_pos hcrit.sigma_lt_one

  -- Step 5: Return
  exact ⟨delta_n, hdelta_n_pos, hdelta_n_le.trans hdelta₀'_le, ⟨config⟩⟩

end Kakeya.Assouad

end
