import MyLeanRepo.Kakeya.Assouad.PureWZ2.Critical

/-!
# Wolff floor from Assertion D via the full-fiber refinement

This module proves `PureWZ2WolffFloorFromAssertionDStatement`: given
Assertion D at `(1/2, 0)` and the strict-full-fiber localization refinement,
derive the pure WZ2 Wolff volume floor `δ^{1/2+ε} ≤ |Y|`.

## Proof outline

Given `ε > 0`:

1. Set `assertionEpsilon := ε/2` and `hAD_epsilon := ε/4`, so that
   `0 < hAD_epsilon < assertionEpsilon < ε`.
2. Apply Assertion D with `hAD_epsilon` to obtain `κ' > 0` and `η' > 0`.
3. Set `assertionEta := η'` and call the refinement statement with `κ'`
   directly (passing `κ'` rather than a `set`-bound alias avoids dependent-type
   rewrite issues when the refinement data type contains `κ`).
4. The refinement either gives the volume bound directly, or produces
   `d : PureWZ2FullFiberAssertionDRefinementData`.
5. In the latter case, apply Assertion D to `d.targetFamily` at the rescaled
   scale `δ' := δ / ρ`.  All hypotheses match exactly because
   `assertionEta = η'`:
   - `d.target_unit_ball`, `d.target_distinct`
   - `d.target_dense`, `d.target_katz_tao`, `d.target_frostman`
6. Assertion D concludes
   `|Y_target| ≥ κ' · (δ')^{hAD_epsilon} · N · |T| · (N · |T|^{1/2})^{-1/2}`.
7. Since `0 < δ' ≤ 1` and `hAD_epsilon < assertionEpsilon`,
   `(δ')^{assertionEpsilon} ≤ (δ')^{hAD_epsilon}` by
   `Real.rpow_le_rpow_of_exponent_ge`.
8. Therefore `|Y_target| ≥ κ' · (δ')^{assertionEpsilon} · tail`.
9. `d.source_power_le_assertion_rhs` already contains `κ'` in its type, giving
   `δ^{1/2+ε} ≤ pullbackFactor · κ' · (δ')^{assertionEpsilon} · tail`.
10. Chain via `d.target_union_pullback`:
    `δ^{1/2+ε} ≤ pullbackFactor · |Y_target| ≤ |Y|`.

## Whiteprint

Node: `wz2_node01_floor_from_assertionD`
Depends on: `wz2_node01_refinement`
-/

noncomputable section

open Kakeya MeasureTheory

namespace Kakeya.Assouad

/--
Derive the pure WZ2 Wolff volume floor from Assertion D and the full-fiber
localization refinement.
-/
theorem pure_wz2_wolff_floor_from_assertionD :
    PureWZ2WolffFloorFromAssertionDStatement := by
  intro hAD hRef
  intro epsilon h_eps
  set assertionEpsilon := epsilon / 2 with hae_def
  have h1 : 0 < assertionEpsilon := by linarith
  have h2 : assertionEpsilon < epsilon := by linarith
  set hAD_epsilon := epsilon / 4 with hade_def
  have h3 : 0 < hAD_epsilon := by linarith
  have h4 : hAD_epsilon < assertionEpsilon := by linarith

  -- Apply Assertion D(1/2, 0) with hAD_epsilon to get kappa', eta'
  rcases hAD.2.2 hAD_epsilon h3 with ⟨kappa', eta', hk_pos, heta_pos, hAD_main⟩

  set assertionEta := eta' with haeta_def

  -- Apply the full-fiber refinement statement with kappa' directly
  rcases hRef epsilon assertionEpsilon kappa' assertionEta h_eps h1 h2 hk_pos heta_pos
    with ⟨inputEta, delta₀, hinput_pos, hdelta₀_pos, hdelta₀_le_one, hRef_main⟩

  refine ⟨inputEta, delta₀, hinput_pos, hdelta₀_pos, hdelta₀_le_one, ?_⟩

  intro delta hdelta_pos hdelta_le family hfamily_nonempty hCWA shading hdense

  rcases hRef_main delta hdelta_pos hdelta_le family hfamily_nonempty shading hCWA hdense
    with (h_left | h_nonempty)

  · -- Case 1: refinement directly gives the volume bound
    exact h_left

  · -- Case 2: refinement gives data d; apply Assertion D to target family
    rcases h_nonempty with ⟨d⟩
    let δ' := delta / d.nearby.rho
    have hδ'_pos : 0 < δ' := d.rescaled_delta_pos
    have hδ'_le_one : δ' ≤ 1 := d.rescaled_delta_le_one

    -- Apply Assertion D to the target family/shading
    have hAD_lb : Kakeya.AssertionDLowerBound d.targetFamily d.targetShading
        kappa' (1 / 2) 0 hAD_epsilon :=
      hAD_main δ' hδ'_pos d.targetFamily d.target_unit_ball d.target_distinct
        d.targetShading
        (by simpa [haeta_def] using d.target_dense)
        (by simpa [haeta_def] using d.target_katz_tao)
        (by simpa [haeta_def] using d.target_frostman)

    -- Monotonicity: for 0 < x ≤ 1 and a ≤ b, x^b ≤ x^a
    have h_rpow_mono :
        Kakeya.realRpowENN δ' assertionEpsilon ≤ Kakeya.realRpowENN δ' hAD_epsilon := by
      simp only [Kakeya.realRpowENN]
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_ge hδ'_pos hδ'_le_one (by linarith)

    -- The common tail: N * |T| * (N * |T|^{1/2})^{-1/2}
    set tail : ENNReal :=
      d.targetFamily.enncard * Kakeya.deltaTubeVolume δ' *
      ENNReal.rpow (d.targetFamily.enncard *
        ENNReal.rpow (Kakeya.deltaTubeVolume δ') (1 / 2)) (-(1 / 2 : ℝ))
      with htail_def

    -- Unfold AssertionDLowerBound to get the concrete inequality
    have hAD_ineq : MeasureTheory.volume d.targetShading.union ≥
        ENNReal.ofReal kappa' * Kakeya.realRpowENN δ' hAD_epsilon * tail := by
      simpa [Kakeya.AssertionDLowerBound, htail_def, mul_assoc] using hAD_lb

    -- Weaken exponent from hAD_epsilon to assertionEpsilon (since hAD_epsilon < assertionEpsilon)
    have h_weak : ENNReal.ofReal kappa' * Kakeya.realRpowENN δ' assertionEpsilon * tail ≤
        MeasureTheory.volume d.targetShading.union := by
      have h_mul : ENNReal.ofReal kappa' * Kakeya.realRpowENN δ' assertionEpsilon * tail ≤
          ENNReal.ofReal kappa' * Kakeya.realRpowENN δ' hAD_epsilon * tail := by
        gcongr
      exact le_trans h_mul hAD_ineq

    -- Source bound already has kappa = kappa' in its type
    have h_source : Kakeya.realRpowENN delta (1 / 2 + epsilon) ≤
        d.pullbackFactor * (ENNReal.ofReal kappa' * Kakeya.realRpowENN δ' assertionEpsilon * tail) := by
      simpa [htail_def, mul_assoc] using d.source_power_le_assertion_rhs

    -- Chain the inequalities
    calc Kakeya.realRpowENN delta (1 / 2 + epsilon)
      ≤ d.pullbackFactor * (ENNReal.ofReal kappa' * Kakeya.realRpowENN δ' assertionEpsilon * tail) :=
        h_source
    _ ≤ d.pullbackFactor * MeasureTheory.volume d.targetShading.union := by
        gcongr
    _ ≤ MeasureTheory.volume shading.union := d.target_union_pullback

end Kakeya.Assouad

end
