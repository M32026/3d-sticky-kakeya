/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceSmallness

/-!
# Source parent bounds and raw VNS preparation at the chosen spine

The scalar choices below retain the literal next-rung raw VNS outputs.
The two property scaffolds do not assert a middle multiplicity or scale row.
-/

@[expose] public section

namespace Kakeya.ML2Assembly

universe u

/-- The source parent parameter is the minimum of all three source budgets. -/
noncomputable def sourceParentMinimum (e tau v dRaw : Real) : Real :=
  min (e ^ 2 * tau / 64) (min (e * v / 1000) (e * dRaw / 1000))

/-- The raw density exponent retained for the full VNS call. -/
noncomputable def sourceMiddleDensity (dRaw : Real) : Real := dRaw / 2

/-- The centring accuracy is fixed from both raw positive outputs. -/
noncomputable def sourceMiddleCenter (v dRaw : Real) : Real := min v dRaw / 12

/-- Half of the raw gain remains available after the centring charge. -/
noncomputable def sourceMiddleGain (v : Real) : Real := v / 2

/-- The proposed ambient exponent, before the separate actual-scale proof. -/
noncomputable def sourceMiddleNetGain (e v : Real) : Real := e * sourceMiddleGain v / 2

/-- Every parent-minimum and fixed-cost conclusion for the actual scalar arguments. -/
structure SourceParentMinBounds (beta c e q tau v dRaw : Real) : Prop where
  margin_pos : 0 < c
  margin_le_rung : c <= q
  next_pos : 0 < tau
  next_le_div : tau <= e
  div_pos : 0 < e
  raw_gain_pos : 0 < v
  raw_dens_pos : 0 < dRaw
  scaled_gain_pos : 0 < e * v
  parent_pos : 0 < sourceParentMinimum e tau v dRaw
  rung_le_beta_parent : q <= beta * sourceParentMinimum e tau v dRaw / 100
  rung_le_scaled_gain : q <= e * v / 100000
  parent_le_scaled_gain : sourceParentMinimum e tau v dRaw <= e * v / 1000
  fixed_cost : 6 * c + 2 * sourceParentMinimum e tau v dRaw + q <= e * v / 100

/-- The raw VNS body and all scalar centring and count-compatibility conclusions. -/
structure SourceMiddlePreparation (beta varpi e tau v dRaw : Real) : Prop where
  div_pos : 0 < e
  next_pos : 0 < tau
  next_le_div : tau <= e
  div_le_window : e <= varpi / 10
  tolerance_pos : 0 < tau / 16
  density_pos : 0 < sourceMiddleDensity dRaw
  density_le_raw : sourceMiddleDensity dRaw <= dRaw
  center_pos : 0 < sourceMiddleCenter v dRaw
  middle_gain_pos : 0 < sourceMiddleGain v
  half_raw_le_middle_gain : v / 2 <= sourceMiddleGain v
  gain_center_budget : sourceMiddleGain v + 3 * sourceMiddleCenter v dRaw <= v
  density_center_budget : 3 * sourceMiddleCenter v dRaw <= sourceMiddleDensity dRaw
  count_compatibility : (tau / 16) * (1 - varpi) <= sourceMiddleDensity dRaw + 2 * varpi
  body : VNSBody.{u} beta varpi (tau / 16) v (sourceMiddleDensity dRaw)
  net_gain_pos : 0 < sourceMiddleNetGain e v
  net_gain_eq : sourceMiddleNetGain e v = e * v / 4

/-- Parent bounds at every admissible rung, derived from the actual raw package. -/
theorem sourceSpine_parent_min_bounds {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
      SourceParentMinBounds beta
        (ML2Spine.spineNu beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens))
        (ML2Spine.spineDiv varpi eps1)
        (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m)
        (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
        (rawGain ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
        (rawDens ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16)) := by
  have hchoice := sourceParameterChoice hbeta0 hbeta1 hp
  have hsp := ML2Spine.spineRung_isSpine hbeta0 hbeta1 hp.window_pos heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  let G := sourceChoiceGain beta rawGain rawDens
  let D := sourceChoiceDens beta rawDens
  let rung := ML2Spine.spineRung beta varpi eps1 G D
  let e := ML2Spine.spineDiv varpi eps1
  let c := ML2Spine.spineNu beta varpi eps1 G D
  have he0 : 0 < e := ML2Spine.spineDiv_pos hp.window_pos heps1
  have hc0 : 0 < c := ML2Spine.spineNu_pos hbeta0 hp.window_pos heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  intro m hm
  let tau := rung (m + 1)
  let v := rawGain (tau / 16)
  let d := rawDens (tau / 16)
  change SourceParentMinBounds beta c e (rung m) tau v d
  have hcq : c <= rung m := hsp.rung_mono (Nat.zero_le m)
  have htau0 : 0 < tau := hsp.rung_pos (m + 1)
  have htau_e : tau <= e := hsp.rung_le_div (m + 1)
  have hv0 : 0 < v := hp.gain_pos (tau / 16) (by positivity)
  have hd0 : 0 < d := hp.dens_pos (tau / 16) (by positivity)
  have hev0 : 0 < e * v := mul_pos he0 hv0
  have hsmall : SourceSmallnessBounds beta e (rung m) tau v d :=
    sourceSpine_six_smallness hbeta0 hbeta1 heps1 hp m hm
  have hparent0 : 0 < sourceParentMinimum e tau v d := by
    unfold sourceParentMinimum
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hparent_gain : sourceParentMinimum e tau v d <= e * v / 1000 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hqgain : rung m <= e * v / 100000 := by
    have hmul := mul_le_mul_of_nonneg_right hbeta1 hev0.le
    nlinarith only [hsmall.beta_gain, hmul]
  have hqparent : rung m <= beta * sourceParentMinimum e tau v d / 100 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 100)]
    rw [show beta * sourceParentMinimum e tau v d =
      min (beta * (e ^ 2 * tau / 64))
        (min (beta * (e * v / 1000)) (beta * (e * d / 1000))) by
        unfold sourceParentMinimum
        rw [mul_min_of_nonneg _ _ hbeta0.le, mul_min_of_nonneg _ _ hbeta0.le]]
    exact le_min (by nlinarith only [hsmall.beta_geometric])
      (le_min (by nlinarith only [hsmall.beta_gain])
        (by nlinarith only [hsmall.beta_dens]))
  exact {
    margin_pos := hc0
    margin_le_rung := hcq
    next_pos := htau0
    next_le_div := htau_e
    div_pos := he0
    raw_gain_pos := hv0
    raw_dens_pos := hd0
    scaled_gain_pos := hev0
    parent_pos := hparent0
    rung_le_beta_parent := hqparent
    rung_le_scaled_gain := hqgain
    parent_le_scaled_gain := hparent_gain
    fixed_cost := by linarith only [hcq, hqgain, hparent_gain, hev0] }

/-- Full raw VNS preparation at every admissible rung of the same chosen spine. -/
theorem sourceSpine_middle_preparation {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
      SourceMiddlePreparation.{u} beta varpi (ML2Spine.spineDiv varpi eps1)
        (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
        (rawGain ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
        (rawDens ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16)) := by
  intro m hm
  have hparent := sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm
  let G := sourceChoiceGain beta rawGain rawDens
  let D := sourceChoiceDens beta rawDens
  let tau := ML2Spine.spineRung beta varpi eps1 G D (m + 1)
  let e := ML2Spine.spineDiv varpi eps1
  let v := rawGain (tau / 16)
  let d := rawDens (tau / 16)
  change SourceMiddlePreparation beta varpi e tau v d
  have he0 : 0 < e := hparent.div_pos
  have htau0 : 0 < tau := hparent.next_pos
  have htau_e : tau <= e := hparent.next_le_div
  have hv0 : 0 < v := hparent.raw_gain_pos
  have hd0 : 0 < d := hparent.raw_dens_pos
  have hwindow0 : 0 < varpi := hp.window_pos
  have hewindow : e <= varpi / 10 := by
    have hdiv := ML2Spine.spineDiv_le hp.window_pos heps1
    have hwindow := ML2Spine.spineEps₂_le_vnsWindow (ϖ := varpi) (ε₁ := eps1)
    dsimp [e]
    linarith only [hdiv, hwindow]
  have htolerance0 : 0 < tau / 16 := by positivity
  have hdensity0 : 0 < sourceMiddleDensity d := by
    unfold sourceMiddleDensity
    positivity
  have hdensity_le : sourceMiddleDensity d <= d := by
    unfold sourceMiddleDensity
    linarith only [hd0]
  have hcenter0 : 0 < sourceMiddleCenter v d := by
    unfold sourceMiddleCenter
    exact div_pos (lt_min hv0 hd0) (by norm_num)
  have hcenterv : sourceMiddleCenter v d <= v / 12 := by
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hcenterd : sourceMiddleCenter v d <= d / 12 := by
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hgain0 : 0 < sourceMiddleGain v := by
    unfold sourceMiddleGain
    positivity
  exact {
    div_pos := he0
    next_pos := htau0
    next_le_div := htau_e
    div_le_window := hewindow
    tolerance_pos := htolerance0
    density_pos := hdensity0
    density_le_raw := hdensity_le
    center_pos := hcenter0
    middle_gain_pos := hgain0
    half_raw_le_middle_gain := le_rfl
    gain_center_budget := by
      unfold sourceMiddleGain
      linarith only [hcenterv, hv0]
    density_center_budget := by
      unfold sourceMiddleDensity
      linarith only [hcenterd, hd0]
    count_compatibility := by
      have hprod : 0 <= (tau / 16) * varpi := mul_nonneg htolerance0.le hwindow0.le
      nlinarith only [hprod, htau_e, hewindow, hwindow0, hdensity0]
    body := (hp.body (tau / 16) htolerance0).mono_dens hdensity_le
    net_gain_pos := by
      unfold sourceMiddleNetGain
      exact div_pos (mul_pos he0 hgain0) (by norm_num)
    net_gain_eq := by unfold sourceMiddleNetGain sourceMiddleGain; ring }

end Kakeya.ML2Assembly
