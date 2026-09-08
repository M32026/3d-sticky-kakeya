/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# Concrete source parameter choice and full VNS provenance

The raw functions remain distinct from the chosen functions. The property
scaffolds retain the complete existing VNS body at the same universe.
-/

@[expose] public section

open Filter Topology

namespace Kakeya.ML2Assembly

universe u

/-- The chosen density function, with value one at nonpositive arguments. -/
noncomputable def sourceChoiceDens (beta : Real) (rawDens : Real -> Real) (z : Real) : Real :=
  if 0 < z then min (beta * rawDens (z / 8) / 50000) (beta * z ^ 2 / 800) else 1

/-- The chosen gain function, with value one at nonpositive arguments. -/
noncomputable def sourceChoiceGain (beta : Real) (rawGain rawDens : Real -> Real)
    (z : Real) : Real :=
  if 0 < z then min (34 * rawGain (z / 8) / 100000)
    (25 * sourceChoiceDens beta rawDens z) else 1

/-- Density shrink for the full body, including all three density-dependent inputs. -/
theorem VNSBody.mono_dens {beta varpi z nu etaOld etaNew : Real}
    (hle : etaNew <= etaOld) (h : VNSBody.{u} beta varpi z nu etaOld) :
    VNSBody.{u} beta varpi z nu etaNew := by
  exact Kakeya.VNSUniform.VNSBody.mono_dens hle h

set_option linter.unusedVariables false in
/-- Tolerance transport keeps the output exponents and the entire cover interval. -/
theorem VNSBody.mono_tolerance {beta varpi z0 z1 nu eta : Real}
    (hvarpi : 0 < varpi) (hz0 : 0 < z0) (hz01 : z0 <= z1)
    (h : VNSBody.{u} beta varpi z0 nu eta) :
    VNSBody.{u} beta varpi z1 nu eta := by
  intro hKT hF
  filter_upwards [h hKT hF, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with delta hdelta hdelta1
  intro iota s T hball hcen huni hmax hfull hcount
  apply hdelta s T hball hcen huni hmax hfull
  intro rho hrho
  obtain ⟨kappa, trho, Trho, hdistinct, hcontains, hcard⟩ := hcount rho hrho
  refine ⟨kappa, trho, Trho, hdistinct, hcontains, le_trans ?_ hcard⟩
  have hrho0 : (0 : NNReal) < rho :=
    lt_of_lt_of_le (NNReal.rpow_pos hdelta1.1) hrho.1
  have hrho1 : rho <= 1 :=
    hrho.2.trans (NNReal.rpow_le_one hdelta1.2.le hvarpi.le)
  exact Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hrho0)
    (by exact_mod_cast hrho1) (by linarith only [hz01])

/-- The full chosen package, its small-tolerance provenance, and the pointwise caps. -/
structure SourceParameterChoice (beta varpi : Real) (rawGain rawDens : Real -> Real) : Prop where
  params : Lemma91ParamsAt.{u} beta varpi
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)
  small_body : forall z : Real, 0 < z ->
    VNSBody.{u} beta varpi (z / 8)
      (sourceChoiceGain beta rawGain rawDens z) (sourceChoiceDens beta rawDens z)
  gain_le_raw : forall z : Real, 0 < z ->
    sourceChoiceGain beta rawGain rawDens z <= rawGain (z / 8)
  dens_le_raw : forall z : Real, 0 < z ->
    sourceChoiceDens beta rawDens z <= rawDens (z / 8)
  gain_cap : forall z : Real, 0 < z ->
    sourceChoiceGain beta rawGain rawDens z <= 34 * rawGain (z / 8) / 100000
  dens_cap : forall z : Real, 0 < z ->
    sourceChoiceDens beta rawDens z <= beta * rawDens (z / 8) / 50000
  dens_quadratic_cap : forall z : Real, 0 < z ->
    sourceChoiceDens beta rawDens z <= beta * z ^ 2 / 800

/-- Construct the chosen parameters and their complete provenance from an actual raw package. -/
theorem sourceParameterChoice {beta varpi : Real} {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    SourceParameterChoice.{u} beta varpi rawGain rawDens := by
  have hdens_pos (z : Real) (hz : 0 < z) :
      0 < sourceChoiceDens beta rawDens z := by
    have hraw := hp.dens_pos (z / 8) (by positivity)
    simp only [sourceChoiceDens, if_pos hz]
    exact lt_min (by positivity) (by positivity)
  have hgain_pos (z : Real) (hz : 0 < z) :
      0 < sourceChoiceGain beta rawGain rawDens z := by
    have hraw := hp.gain_pos (z / 8) (by positivity)
    have hdens := hdens_pos z hz
    simp only [sourceChoiceGain, if_pos hz]
    exact lt_min (by positivity) (by positivity)
  have hdcap (z : Real) (hz : 0 < z) :
      sourceChoiceDens beta rawDens z <= beta * rawDens (z / 8) / 50000 := by
    simp only [sourceChoiceDens, if_pos hz]
    exact min_le_left _ _
  have hdquad (z : Real) (hz : 0 < z) :
      sourceChoiceDens beta rawDens z <= beta * z ^ 2 / 800 := by
    simp only [sourceChoiceDens, if_pos hz]
    exact min_le_right _ _
  have hgcap (z : Real) (hz : 0 < z) :
      sourceChoiceGain beta rawGain rawDens z <= 34 * rawGain (z / 8) / 100000 := by
    simp only [sourceChoiceGain, if_pos hz]
    exact min_le_left _ _
  have hgcenter (z : Real) (hz : 0 < z) :
      sourceChoiceGain beta rawGain rawDens z / 25 <= sourceChoiceDens beta rawDens z := by
    have hmin : sourceChoiceGain beta rawGain rawDens z <=
        25 * sourceChoiceDens beta rawDens z := by
      simp only [sourceChoiceGain, if_pos hz]
      exact min_le_right _ _
    linarith
  have hdle (z : Real) (hz : 0 < z) :
      sourceChoiceDens beta rawDens z <= rawDens (z / 8) := by
    have hraw := hp.dens_pos (z / 8) (by positivity)
    have hmul := mul_le_mul_of_nonneg_right hbeta1 hraw.le
    exact (hdcap z hz).trans (by nlinarith)
  have hgle (z : Real) (hz : 0 < z) :
      sourceChoiceGain beta rawGain rawDens z <= rawGain (z / 8) := by
    have hraw := hp.gain_pos (z / 8) (by positivity)
    exact (hgcap z hz).trans (by linarith)
  have hsmall (z : Real) (hz : 0 < z) :
      VNSBody.{u} beta varpi (z / 8)
        (sourceChoiceGain beta rawGain rawDens z) (sourceChoiceDens beta rawDens z) :=
    VNSBody.mono_dens (hdle z hz)
      (VNSBody.mono_gain (hgle z hz) (hp.body (z / 8) (by positivity)))
  refine {
    params := {
      window_pos := hp.window_pos
      gain_pos := hgain_pos
      dens_pos := hdens_pos
      gain_le_dens := hgcenter
      body := ?_ }
    small_body := hsmall
    gain_le_raw := hgle
    dens_le_raw := hdle
    gain_cap := hgcap
    dens_cap := hdcap
    dens_quadratic_cap := hdquad }
  intro z hz
  exact VNSBody.mono_tolerance hp.window_pos (by positivity) (by linarith) (hsmall z hz)

end Kakeya.ML2Assembly
