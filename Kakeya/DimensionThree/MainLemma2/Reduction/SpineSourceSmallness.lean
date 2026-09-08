/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParameterChoice

/-!
# The six source smallness conclusions for the concrete chosen-function spine

The raw package remains an input, while every branch bound is a conclusion.
The canonical recurrence is unchanged and includes the bottom rung.
-/

@[expose] public section

namespace Kakeya.ML2Assembly

universe u

/-- The six source inequalities, in the order of the backward smallness minimum. -/
structure SourceSmallnessBounds (beta e q tau v dRaw : Real) : Prop where
  geometric : q <= e ^ 2 * tau / 100
  gain : q <= e * v / 8
  dens : q <= e * dRaw / 8
  beta_geometric : q <= beta * e ^ 2 * tau / 6400
  beta_gain : q <= beta * e * v / 100000
  beta_dens : q <= beta * e * dRaw / 100000

/-- All six source smallness bounds at every admissible rung of the chosen spine. -/
theorem sourceSpine_six_smallness {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
      SourceSmallnessBounds beta (ML2Spine.spineDiv varpi eps1)
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
  have he0 : 0 < e := ML2Spine.spineDiv_pos hp.window_pos heps1
  intro m hm
  let tau := rung (m + 1)
  change SourceSmallnessBounds beta e (rung m) tau (rawGain (tau / 16)) (rawDens (tau / 16))
  have htau0 : 0 < tau := hsp.rung_pos (m + 1)
  have htau_e : tau <= e := hsp.rung_le_div (m + 1)
  have hv0 := hp.gain_pos (tau / 16) (by positivity)
  have hd0 := hp.dens_pos (tau / 16) (by positivity)
  have harg : tau / 2 / 8 = tau / 16 := by ring
  have hgain_cap : G (tau / 2) <= 34 * rawGain (tau / 16) / 100000 := by
    simpa only [harg] using hchoice.gain_cap (tau / 2) (by positivity)
  have hdens_cap : D (tau / 2) <= beta * rawDens (tau / 16) / 50000 := by
    simpa only [harg] using hchoice.dens_cap (tau / 2) (by positivity)
  have hquad : D (tau / 2) <= beta * (tau / 2) ^ 2 / 800 :=
    hchoice.dens_quadratic_cap (tau / 2) (by positivity)
  have hstep : rung m =
      min (min (e ^ 2 * beta * tau / 1024) (e * beta * G (tau / 2) / 34))
        (e * D (tau / 2) / 2) :=
    ML2Spine.spineRung_eq_step hm
  have hstep_gain : rung m <= e * beta * G (tau / 2) / 34 := by
    rw [hstep]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hstep_dens : rung m <= e * D (tau / 2) / 2 := by
    rw [hstep]
    exact min_le_right _ _
  have hbeta_gain : rung m <= beta * e * rawGain (tau / 16) / 100000 := by
    calc
      rung m <= e * beta * G (tau / 2) / 34 := hstep_gain
      _ <= e * beta * (34 * rawGain (tau / 16) / 100000) / 34 := by gcongr
      _ = beta * e * rawGain (tau / 16) / 100000 := by ring
  have hbeta_dens : rung m <= beta * e * rawDens (tau / 16) / 100000 := by
    calc
      rung m <= e * D (tau / 2) / 2 := hstep_dens
      _ <= e * (beta * rawDens (tau / 16) / 50000) / 2 := by gcongr
      _ = beta * e * rawDens (tau / 16) / 100000 := by ring
  have hbeta_geometric : rung m <= beta * e ^ 2 * tau / 6400 := by
    calc
      rung m <= e * D (tau / 2) / 2 := hstep_dens
      _ <= e * (beta * (tau / 2) ^ 2 / 800) / 2 := by gcongr
      _ = beta * e * tau * tau / 6400 := by ring
      _ <= beta * e * e * tau / 6400 := by gcongr
      _ = beta * e ^ 2 * tau / 6400 := by ring
  have he2tau : 0 <= e ^ 2 * tau := by positivity
  have hev : 0 <= e * rawGain (tau / 16) := by positivity
  have hed : 0 <= e * rawDens (tau / 16) := by positivity
  have hgeomul := mul_le_mul_of_nonneg_right hbeta1 he2tau
  have hgainmul := mul_le_mul_of_nonneg_right hbeta1 hev
  have hdensmul := mul_le_mul_of_nonneg_right hbeta1 hed
  exact {
    geometric := by nlinarith only [hbeta_geometric, hgeomul, he2tau]
    gain := by nlinarith only [hbeta_gain, hgainmul, hev]
    dens := by nlinarith only [hbeta_dens, hdensmul, hed]
    beta_geometric := hbeta_geometric
    beta_gain := hbeta_gain
    beta_dens := hbeta_dens }

end Kakeya.ML2Assembly
