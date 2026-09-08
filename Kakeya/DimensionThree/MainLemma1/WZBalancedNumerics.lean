/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Setup

/-!
# Numerics for the WZ balanced-block endgame

This module isolates the scale gain in Wang--Zahl Lemma 6.4.  It does not assume the existence of
a balanced block.  The geometric producer and the three multiplicity estimates belong in later
modules.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

/-- The exponent ledger after setting `epsilon1 = zeta * t / 24`: three copies of `epsilon1`
against the scale-separation gain `zeta * t / 5` leave `3 * zeta * t / 40` of gain. -/
lemma wz_gain_exponent (zeta t : Real) :
    3 * (zeta * t / 24) + (-(zeta / 5) * t) = -3 * zeta * t / 40 := by
  ring

/-- If `tau <= delta^(zeta/5) rho`, the scale factor in the balanced endgame pays the three
`epsilon1` terms.  This is the NNReal form used before coercing multiplicity bounds to ENNReal. -/
theorem wz_separation_gain_nnreal
    {delta tau rho : NNReal} {zeta t epsilon1 : Real}
    (hdelta : 0 < delta) (htau : 0 < tau) (ht : 0 <= t)
    (hsep : tau <= delta ^ (zeta / 5) * rho)
    (hepsilon1 : epsilon1 = zeta * t / 24) :
    delta ^ (-3 * zeta * t / 40) <=
      delta ^ (3 * epsilon1) * (rho / tau) ^ t := by
  have hpow : 0 < delta ^ (zeta / 5) := NNReal.rpow_pos hdelta
  have hratio : delta ^ (-(zeta / 5)) <= rho / tau := by
    rw [NNReal.rpow_neg]
    rw [le_div_iff₀ htau]
    calc
      (delta ^ (zeta / 5))⁻¹ * tau <=
          (delta ^ (zeta / 5))⁻¹ * (delta ^ (zeta / 5) * rho) := by
        gcongr
      _ = rho := by
        rw [← mul_assoc, inv_mul_cancel₀ hpow.ne']
        simp
  have hratio_pow : delta ^ (-(zeta / 5) * t) <= (rho / tau) ^ t := by
    rw [NNReal.rpow_mul]
    exact NNReal.rpow_le_rpow hratio ht
  calc
    delta ^ (-3 * zeta * t / 40) =
        delta ^ (3 * epsilon1 + (-(zeta / 5) * t)) := by
          congr 1
          rw [hepsilon1, wz_gain_exponent]
    _ = delta ^ (3 * epsilon1) * delta ^ (-(zeta / 5) * t) := by
      rw [NNReal.rpow_add hdelta.ne']
    _ <= delta ^ (3 * epsilon1) * (rho / tau) ^ t := by
      gcongr

/-- ENNReal form of `wz_separation_gain_nnreal`, ready for the multiplicity ledger. -/
theorem wz_separation_gain
    {delta tau rho : NNReal} {zeta t epsilon1 : Real}
    (hdelta : 0 < delta) (htau : 0 < tau) (hrho : 0 < rho) (ht : 0 <= t)
    (hsep : tau <= delta ^ (zeta / 5) * rho)
    (hepsilon1 : epsilon1 = zeta * t / 24) :
    (delta : ENNReal) ^ (-3 * zeta * t / 40) <=
      (delta : ENNReal) ^ (3 * epsilon1) * ((rho / tau : NNReal) : ENNReal) ^ t := by
  have h := wz_separation_gain_nnreal hdelta htau ht hsep hepsilon1
  have hcoe :
      ((delta ^ (-3 * zeta * t / 40) : NNReal) : ENNReal) <=
        ((delta ^ (3 * epsilon1) * (rho / tau) ^ t : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr h
  simpa [← ENNReal.coe_rpow_of_ne_zero hdelta.ne',
    ← ENNReal.coe_rpow_of_ne_zero (div_ne_zero hrho.ne' htau.ne'), ENNReal.coe_mul] using
    hcoe

end Kakeya.ml1Boot
