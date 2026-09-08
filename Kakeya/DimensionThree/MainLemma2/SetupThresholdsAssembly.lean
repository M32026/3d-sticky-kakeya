/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupSideData

/-!
# The thresholds of conjunct 2 of `SideDataObligations` (T6), and the thin-constant obligation

Conjunct 2 of `Kakeya.VeryNotSticky.SideDataObligations` (the steps T6 of (a))
asks, for every configuration `cfg` at `a = b = δ` and every `bd : BallData cfg` with the pinned
`δ`-free constants and `δ ≤ w₁ ≤ 1`, for a thin configuration `tc : ThinConfig cfg bd` together
with the fixed-scale bundles `Kakeya.VeryNotSticky.SlabScale cfg bd tc τ`,
`Kakeya.VeryNotSticky.CaseScale cfg bd τ τ' (τ' β / 2) tc.C thr₀` and the tangential density
threshold `100 · tc.C ≤ δ^{-η}`, eventually as `δ → 0⁺`. Every one of these thresholds compares
the thin-case comparison constant `tc.C` — which is produced *after* `δ` — with a positive power
of `δ⁻¹`; they are arrangeable exactly when `tc.C` is sub-polynomial in `δ⁻¹`.

This file does two things.

1. **It reduces conjunct 2 to that one fact.** `Kakeya.VeryNotSticky.ThinConstantObligation`
   is the statement "for the pinned data there is a `tc` with `tc.C ≤ δ^{-ε}`", with the binders
   of conjunct 2, and `Kakeya.VeryNotSticky.sideDataObligations_conjunct2_of_thinConstant`
   proves conjunct 2 **verbatim** from it at the exponent
   `Kakeya.VeryNotSticky.thresholdExponent β exscal η τ`, whose size is dictated by the gaps of
   `Kakeya.VeryNotSticky.CaseParams` and by the polynomial degree of the thresholds in `tc.C`
   (one for `SlabScale.density`, seven for `SlabScale.final` through
   `Kakeya.VeryNotSticky.slabUnionConstant`, five for `CaseScale.transverse_ballFill` through
   `Kakeya.ThinCase.transferConstant`, one for the density threshold). The producers are the
   exponent-slack variants `Kakeya.VeryNotSticky.eventually_slabScale_of_C_le`,
   `Kakeya.VeryNotSticky.eventually_caseScale_of_C_le` (fourteen clauses as in
   `Kakeya.VeryNotSticky.eventually_caseScale_of_constants`; the fifteenth, O5, is vacuous at
   `a = b` by `Kakeya.VeryNotSticky.not_transverseGuard_of_a_eq_b`) and
   `Kakeya.VeryNotSticky.eventually_densityConstant_of_C_le`. Two `example`s check that the
   lemma's conclusion is the second component of `SideDataObligations`.

2. **It describes the quantitative bound needed for the produced thin constant.** `Kakeya.VeryNotSticky.exists_thinConfig` builds `tc` through
   `Kakeya.ThinCase.thinSetupExists`, whose binder `hCcoreNet` forces
   `Ccore ≥ Kakeya.ThinCase.thinEnvelopeTerm 3 #segs #bodies CF w₁` at every ball, and returns
   the constant `bd.Cg · thinSetupConstant … Ccore …`. Until pack F13
   the eccentricity exponent `Kakeya.ThinCase.thinEccentricityExponent 3 ns CF` was
   `⌈CF · ns · C_vol⌉₊` — *linear* in the segment count — so that envelope, and with it every
   constant produced by `thinSetupExists`, was at least `2 · CF · #segs B · C_vol 3`: polynomial in `δ⁻¹`,
   never `≤ δ^{-ε}`. That linear bound was an artefact of the old definition body, not of the
   construction: F13 repaired `Kakeya.ThinCase.twoPowExponent` to `⌊log₂ ⌈x⌉₊⌋ + 1`
   (`Kakeya.ThinCase.two_pow_twoPowExponent_le`), so the envelope is now polylogarithmic in
   `#segs`, `#bodies` and `δ⁻¹`, and the producer `exists_thinConfig_le` is what discharges the obligation. The lemmas of the last section are the parts of
   the old record that stay true for every exponent, kept for that producer.

Nothing here changes an existing statement; `Kakeya.VeryNotSticky.SideDataObligations` and its
consumers are untouched.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal

universe u

/-- A fixed constant times the `k`-th power of a factor bounded by `d^{-ε}` is eventually
dominated by `d^{-ν}` once `k ε < ν`. -/
theorem eventually_nnreal_mul_pow_le_rpow_neg (K : NNReal) (k : ℕ) {ε ν : ℝ}
    (hkε : (k : ℝ) * ε < ν) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ C : NNReal, C ≤ d ^ (-ε) → K * C ^ k ≤ d ^ (-ν) := by
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow K (p := -((k : ℝ) * ε)) (q := -ν)
    (by linarith)] with d hd C hC
  calc K * C ^ k ≤ K * (d ^ (-ε)) ^ k := by gcongr
    _ = K * d ^ (-((k : ℝ) * ε)) := by
        rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
        congr 2
        ring
    _ ≤ d ^ (-ν) := hd

/-- The scalar workhorse of the exponent-slack producers: a fixed constant, times the `k`-th
power of a factor bounded by `d^{-ε}`, times `d^p`, is eventually at most `d^q` once
`q + k ε < p`. -/
theorem eventually_nnreal_mul_pow_mul_rpow_le_rpow (K : NNReal) (k : ℕ) {ε p q : ℝ}
    (hq : q + (k : ℝ) * ε < p) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ C : NNReal, C ≤ d ^ (-ε) → K * C ^ k * d ^ p ≤ d ^ q := by
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow K (p := p - (k : ℝ) * ε) (q := q)
    (by linarith), self_mem_nhdsWithin] with d hd hd0 C hC
  have hdne : d ≠ 0 := ne_of_gt hd0
  calc K * C ^ k * d ^ p ≤ K * (d ^ (-ε)) ^ k * d ^ p := by gcongr
    _ = K * d ^ (p - (k : ℝ) * ε) := by
        rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, mul_assoc, ← NNReal.rpow_add hdne]
        congr 2
        ring
    _ ≤ d ^ q := hd

/-- The polynomial envelope of the two net constants of `Kakeya.ThinCase.transferConstant` and
`Kakeya.ThinCase.unionLowerConstant` in the thin-case comparison constant `C`: for `1 ≤ C`,
`netUpperConstant C C₀ · netLowerConstant C ≤ netPolyConstant C₀ · C^5`. -/
noncomputable def netPolyConstant (C₀ : NNReal) : NNReal :=
  2 ^ 12 * (1 + ThinCase.w1Constant C₀) ^ 3 * 125 ^ 2

lemma netUpperConstant_le_mul_pow {C C₀ : NNReal} (hC : 1 ≤ C) :
    ThinCase.netUpperConstant C C₀ ≤ 2 ^ 12 * (1 + ThinCase.w1Constant C₀) ^ 3 * C ^ 3 := by
  have hw : (1 : NNReal) ≤ (1 + ThinCase.w1Constant C₀) ^ 3 :=
    one_le_pow₀ (le_add_of_nonneg_right zero_le)
  have hC3 : (1 : NNReal) ≤ C ^ 3 := one_le_pow₀ hC
  refine max_le ?_ (le_of_eq (by ring))
  calc (1 : NNReal) = 1 * 1 * 1 := by ring
    _ ≤ 2 ^ 12 * (1 + ThinCase.w1Constant C₀) ^ 3 * C ^ 3 := by gcongr; norm_num

lemma netLowerConstant_le_mul_pow {C : NNReal} (hC : 1 ≤ C) :
    ThinCase.netLowerConstant C ≤ 125 ^ 2 * C ^ 2 := by
  have hC2 : (1 : NNReal) ≤ C ^ 2 := one_le_pow₀ hC
  have hsep : ((separatedNetCoverConstant 3 : ℕ) : NNReal) = 125 := by
    norm_num [separatedNetCoverConstant]
  have hball : ThinCase.ballDensityConstant C ≤ 125 * C ^ 2 := by
    rw [ThinCase.ballDensityConstant, hsep]
    refine max_le ?_ le_rfl
    calc (1 : NNReal) = 1 * 1 := by ring
      _ ≤ 125 * C ^ 2 := by gcongr; norm_num
  rw [ThinCase.netLowerConstant, hsep]
  refine max_le ?_ ?_
  · calc (1 : NNReal) = 1 * 1 := by ring
      _ ≤ 125 ^ 2 * C ^ 2 := by gcongr; norm_num
  · calc 125 * ThinCase.ballDensityConstant C ≤ 125 * (125 * C ^ 2) := by gcongr
      _ = 125 ^ 2 * C ^ 2 := by ring

lemma unionLowerConstant_le_mul_pow {C C₀ : NNReal} (hC : 1 ≤ C) :
    ThinCase.unionLowerConstant C C₀ ≤ netPolyConstant C₀ * C ^ 5 := by
  rw [ThinCase.unionLowerConstant, netPolyConstant]
  calc ThinCase.netUpperConstant C C₀ * ThinCase.netLowerConstant C
      ≤ (2 ^ 12 * (1 + ThinCase.w1Constant C₀) ^ 3 * C ^ 3) * (125 ^ 2 * C ^ 2) :=
        mul_le_mul' (netUpperConstant_le_mul_pow hC) (netLowerConstant_le_mul_pow hC)
    _ = 2 ^ 12 * (1 + ThinCase.w1Constant C₀) ^ 3 * 125 ^ 2 * C ^ 5 := by ring

lemma transferConstant_le_mul_pow {C C₀ : NNReal} (hC : 1 ≤ C) :
    ThinCase.transferConstant C C₀ ≤ 8 * netPolyConstant C₀ * C ^ 5 := by
  have h := unionLowerConstant_le_mul_pow (C₀ := C₀) hC
  rw [ThinCase.unionLowerConstant] at h
  calc ThinCase.transferConstant C C₀
      = 2 ^ 3 * (ThinCase.netUpperConstant C C₀ * ThinCase.netLowerConstant C) := by
        rw [ThinCase.transferConstant, mul_assoc]
    _ ≤ 2 ^ 3 * (netPolyConstant C₀ * C ^ 5) := by gcongr
    _ = 8 * netPolyConstant C₀ * C ^ 5 := by ring

lemma slabUnionConstant_le_mul_pow {C C₀ : NNReal} {exscal : ℝ} (hC : 1 ≤ C) :
    slabUnionConstant C C₀ exscal ≤
      netPolyConstant C₀ * slabMultBoundConstant exscal * C ^ 6 := by
  rw [slabUnionConstant, slabUnionFromMultConstant]
  calc C * ThinCase.unionLowerConstant C C₀ * slabMultBoundConstant exscal
      ≤ C * (netPolyConstant C₀ * C ^ 5) * slabMultBoundConstant exscal := by
        gcongr
        exact unionLowerConstant_le_mul_pow hC
    _ = netPolyConstant C₀ * slabMultBoundConstant exscal * C ^ 6 := by ring


/-! ### `SlabScale` at a sub-polynomially bounded thin constant -/

/-- **Exponent-slack variant of `Kakeya.VeryNotSticky.eventually_slabScale_of_uniform_bounds`.**
The thin-case comparison constant `tc.C` is not pinned to a fixed value but only bounded by
`d^{-ε}`; the three fixed-scale thresholds of `Kakeya.VeryNotSticky.SlabScale` then hold once
`ε` is small against the three gaps (`density`: one power of `tc.C`; `final`: seven powers,
through `Kakeya.VeryNotSticky.slabUnionConstant`). The fibre-count budget
`Cm · m ≤ fibreMassConstant · δ^{-(η+2 exscal)}` is passed through as a hypothesis and `Cdil` is a
ceiling `bd.Cdil ≤ Cdil` ; the former positivity hypothesis
`0 < η + 2 exscal` was consumed only by the pins' proof of the budget and is gone with them. -/
theorem eventually_slabScale_of_C_le {β exscal η ϱ τ ε : ℝ} (C₀ Cbias Cdil : NNReal)
    (hdensity_gap : 6 * η + ε < exscal) (hanti_gap : 2 * ϱ < exscal)
    (hfinal_gap : 12 * η + 12 * exscal + 3 * τ + 7 * ε < β / 2) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (tc : ThinConfig cfg bd),
        cfg.δ = d → cfg.β = β → cfg.exscal = exscal → cfg.η = η → cfg.ϱ = ϱ →
        bd.C₀ = C₀ → bd.Cbias = Cbias → bd.Cdil ≤ Cdil →
        (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
          (fibreMassConstant : ENNReal) *
            (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) →
        1 ≤ tc.C → tc.C ≤ d ^ (-ε) →
        SlabScale cfg bd tc τ := by
  have hsmall : ∀ᶠ d : NNReal in 𝓝[>] 0, d < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd
    exact hd.2
  filter_upwards [eventually_nnreal_mul_pow_mul_rpow_le_rpow (slabInputsConstant C₀) 1 (ε := ε)
      (p := exscal) (q := 6 * η) (by push_cast; linarith),
    eventually_nnreal_mul_rpow_le_rpow (slabInputsConstant C₀ * Cbias) (p := exscal)
      (q := 2 * ϱ) hanti_gap,
    eventually_nnreal_mul_pow_mul_rpow_le_rpow
      (fibreMassConstant * Cdil * (netPolyConstant C₀ * slabMultBoundConstant exscal)) 7 (ε := ε)
      (p := β / 2)
      (q := 12 * η + 12 * exscal + 3 * τ) (by push_cast; linarith),
    hsmall, self_mem_nhdsWithin] with d hden hanti hfin hd1 hd0
  intro cfg bd tc hδ hβ hex hη hϱ hC₀ hCb hCdil hSPH h1C hC
  have hdpos : (0 : NNReal) < d := hd0
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hcoe : ∀ (x : NNReal) (p q : ℝ), x * d ^ p ≤ d ^ q →
      (x : ENNReal) * (d : ENNReal) ^ p ≤ (d : ENNReal) ^ q := by
    intro x p q h
    rw [← ENNReal.coe_rpow_of_ne_zero hdne, ← ENNReal.coe_rpow_of_ne_zero hdne,
      ← ENNReal.coe_mul]
    exact_mod_cast h
  constructor
  · rw [hδ]; exact hd1
  · rw [hδ, hex, hη, hC₀, ← ENNReal.coe_mul]
    apply hcoe
    have := hden tc.C hC
    rw [pow_one] at this
    calc tc.C * slabInputsConstant C₀ * d ^ exscal
        = slabInputsConstant C₀ * tc.C * d ^ exscal := by ring
      _ ≤ d ^ (6 * η) := this
  · rw [hδ, hex, hϱ, hC₀, hCb, ← ENNReal.coe_mul]
    exact hcoe _ _ _ hanti
  · rw [hδ, hβ, hex, hη, hC₀]
    have hCdil' : (bd.Cdil : ENNReal) ≤ (Cdil : ENNReal) := ENNReal.coe_le_coe.mpr hCdil
    calc (fibreMassConstant : ENNReal) * (tc.C : ENNReal) * (bd.Cdil : ENNReal) *
          (slabUnionConstant tc.C C₀ exscal : ENNReal) * (d : ENNReal) ^ (β / 2)
        ≤ (fibreMassConstant : ENNReal) * (tc.C : ENNReal) * (Cdil : ENNReal) *
          (slabUnionConstant tc.C C₀ exscal : ENNReal) * (d : ENNReal) ^ (β / 2) := by
          gcongr
      _ = ((fibreMassConstant * tc.C * Cdil * slabUnionConstant tc.C C₀ exscal : NNReal) :
            ENNReal) * (d : ENNReal) ^ (β / 2) := by
          rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul]
      _ ≤ (d : ENNReal) ^ (12 * η + 12 * exscal + 3 * τ) := by
          apply hcoe
          have hpoly := slabUnionConstant_le_mul_pow (C₀ := C₀) (exscal := exscal) h1C
          calc fibreMassConstant * tc.C * Cdil * slabUnionConstant tc.C C₀ exscal * d ^ (β / 2)
              ≤ fibreMassConstant * tc.C * Cdil *
                  (netPolyConstant C₀ * slabMultBoundConstant exscal * tc.C ^ 6) *
                  d ^ (β / 2) := by gcongr
            _ = fibreMassConstant * Cdil * (netPolyConstant C₀ * slabMultBoundConstant exscal) *
                  tc.C ^ 7 * d ^ (β / 2) := by ring
            _ ≤ d ^ (12 * η + 12 * exscal + 3 * τ) := hfin tc.C hC
  · exact hSPH

/-! ### `CaseScale` at a sub-polynomially bounded thin constant, in the regime `a = b` -/

/-- **The transverse guard of O5 is false at `a = b`.** With `δ < 1` and `τ' > 0` one has
`δ^{-τ'} · (a/b) = δ^{-τ'} > 1`, so the clause
`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness` holds vacuously (the regime in which
`Kakeya.VeryNotSticky.false_of_transverseFill_fullness` refutes the unguarded clause is
exactly the one the guard excludes). -/
theorem not_transverseGuard_of_a_eq_b (cfg : VeryNotSticky.{u}) {τ' : ℝ} (hτ' : 0 < τ')
    (hδ1 : cfg.δ < 1) (hab : cfg.a = cfg.b) :
    ¬ cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ 1 := by
  have ha : cfg.a ≠ 0 := (lt_of_lt_of_le cfg.hδ cfg.hdims.1).ne'
  rw [← hab, div_self ha, mul_one]
  exact not_le.mpr (NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg cfg.hδ hδ1 (by linarith))

/-- **Exponent-slack variant of `Kakeya.VeryNotSticky.eventually_caseScale_of_constants`,
in the regime `a = b`.** Fourteen clauses are the arithmetic of that lemma; the one clause
reading the thin constant, `transverse_ballFill`, is discharged from `1 ≤ C ≤ d^{-ε}` through
the degree-five envelope `Kakeya.VeryNotSticky.transferConstant_le_mul_pow`, and the fifteenth,
O5 (`transverseFill_fullness`), is vacuous at `a = b`
(`Kakeya.VeryNotSticky.not_transverseGuard_of_a_eq_b`). -/
theorem eventually_caseScale_of_C_le (C₀ Cbias : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal η ϱ τ τ' ν ε : ℝ} (hexscal : 0 < exscal) (hexscal1 : exscal < 1) (hη : 0 < η)
    (hϱ : 0 < ϱ) (hτ' : 0 < τ') (hthin : τ + exscal < 1) (hε : 5 * ε < η) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (thr : ScaleThresholds) (C : NNReal),
        cfg.δ = d → cfg.exscal = exscal → cfg.η = η → cfg.ϱ = ϱ →
        bd.C₀ = C₀ → bd.Cbias = Cbias → cfg.a = cfg.b →
        1 ≤ C → C ≤ d ^ (-ε) →
        cfg.δ ≤ thr.aScale ν → cfg.δ ≤ thr.typical →
        CaseScale cfg bd τ τ' ν C thr := by
  have hsmall : ∀ᶠ d : NNReal in 𝓝[>] 0, d < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd
    exact hd.2
  filter_upwards [eventually_caseScale_clauses C₀ Cbias 1 hC₀ hexscal hexscal1 hη hϱ hτ' hthin,
    eventually_transverseFill_threshold (exscal := exscal) (ϱ := ϱ) hη hexscal1,
    eventually_multiplicity_large (η := 16 * η) (exscal := exscal)
      (by linarith : (0:ℝ) < 16 * η) hexscal1,
    eventually_typicalAngle_const.{u} (exscal := exscal) hη hϱ hexscal1,
    eventually_nnreal_mul_pow_le_rpow_neg (1000 * (8 * netPolyConstant C₀)) 5 (ε := ε)
      (ν := η) (by push_cast; linarith),
    hsmall, self_mem_nhdsWithin] with d hcl hfill hmult htyp hball hd1 hd0
  intro cfg bd thr C hδ hex hη' hϱ' hC hCb hab h1C hCle hthrA hthrT
  obtain ⟨c1, c2, c3, c4, c5, -, c7, c8, c9⟩ := hcl cfg bd hδ hex hη' hϱ' hC hCb
  have hdpos : (0 : NNReal) < d := hd0
  have hd1' : cfg.δ < 1 := by rw [hδ]; exact hd1
  exact
    { rho2Star_le_one := c1
      body_fits_ball := c2
      plank_small := c3
      multiplicity_large := by
        have hr : (cfg.δ / cfg.r₁ : NNReal) = (d / d ^ exscal : NNReal) := by
          simp only [VeryNotSticky.r₁, hδ, hex]
        rw [hr, hη']
        exact hmult
      transverse_radius := c4
      transverse_fill := c5
      transverse_ballFill := by
        rw [hC, hδ, hη']
        calc 1000 * ThinCase.transferConstant C C₀
            ≤ 1000 * (8 * netPolyConstant C₀ * C ^ 5) := by
              gcongr
              exact transferConstant_le_mul_pow h1C
          _ = 1000 * (8 * netPolyConstant C₀) * C ^ 5 := by ring
          _ ≤ d ^ (-η) := hball C hCle
      aScaleData_threshold := hthrA
      typicalAngle_threshold := hthrT
      typicalAngle_const := by
        have hr : (cfg.δ / cfg.r₁ : NNReal) = (d / d ^ exscal : NNReal) := by
          simp only [VeryNotSticky.r₁, hδ, hex]
        rw [hr, hη', hϱ', hδ]
        refine htyp (plankEnclosureConstant bd.C₀ * bd.Cbias) ?_
        rw [← hδ, ← hϱ']
        exact c7
      plankCard_bias := c7
      transverseFill_threshold := hfill cfg bd hδ hex hη' hϱ'
      transverseFill_fullness := fun _hthin hguard =>
        absurd hguard (not_transverseGuard_of_a_eq_b cfg hτ' hd1' hab)
      typicalAngle_selection := c8
      typicalAngle_cap := c9 }

/-- **The tangential density threshold at a sub-polynomially bounded thin constant**: the
field `Kakeya.VeryNotSticky.SlabMultKT.densityConstant`, `100 · C ≤ δ^{-η}`, from
`C ≤ d^{-ε}` with `ε < η`. -/
theorem eventually_densityConstant_of_C_le {η ε : ℝ} (hε : ε < η) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ C : NNReal, C ≤ d ^ (-ε) →
      ((tangentialSlabDecompConstant C : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-η) := by
  filter_upwards [eventually_nnreal_mul_pow_le_rpow_neg 100 1 (ε := ε) (ν := η)
    (by push_cast; linarith), self_mem_nhdsWithin] with d hd hd0 C hC
  have hdne : d ≠ 0 := ne_of_gt (show (0 : NNReal) < d from hd0)
  rw [← ENNReal.coe_rpow_of_ne_zero hdne, ENNReal.coe_le_coe, tangentialSlabDecompConstant]
  simpa using hd C hC

/-! ### The trivial threshold bundle -/

/-- The threshold bundle with all three thresholds equal to `1` and the absorbed constant `1`
(the witness of `Kakeya.VeryNotSticky.nonempty_scaleThresholds`, named so that its thresholds
can be read: `cfg.δ ≤ 1` is `Kakeya.VeryNotSticky.hδ1`). -/
noncomputable def unitScaleThresholds : ScaleThresholds where
  aScale := fun _ => 1
  aScale_mem := by
    intro ν
    norm_num
  aScaleConst := fun _ _ => 1
  one_le_aScaleConst := by
    intro ν η
    rfl
  aScale_absorb := by
    intro ν η hη δ hδ hδa
    have hd0 : (0 : ENNReal) < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ
    have hd1 : (δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδa
    have hneg : -η < 0 := neg_lt_zero.mpr hη
    have hone : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-η) :=
      ENNReal.one_le_rpow_of_pos_of_le_one_of_neg hd0 hd1 hneg
    simpa using hone
  typical := 1
  typical_mem := by norm_num
  fill := 1
  fill_mem := by norm_num

@[simp] lemma unitScaleThresholds_aScale (ν : ℝ) : unitScaleThresholds.aScale ν = 1 := rfl

@[simp] lemma unitScaleThresholds_typical : unitScaleThresholds.typical = 1 := rfl


/-! ### Conjunct 2 of `SideDataObligations`, from a sub-polynomial thin constant -/

/-- **The exponent slack the thresholds of conjunct 2 tolerate on the thin constant.** With
`ε = thresholdExponent β exscal η τ`, a thin constant `tc.C ≤ δ^{-ε}` satisfies every
`tc.C`-dependent clause of `Kakeya.VeryNotSticky.SlabScale` and `Kakeya.VeryNotSticky.CaseScale`
and the tangential density threshold `100 · tc.C ≤ δ^{-η}` under
`Kakeya.VeryNotSticky.CaseParams`: `ε ≤ (exscal - 6η)/2` for `density` (one power),
`ε ≤ (β/2 - (12η + 12 exscal + 3τ))/14` for `final` (seven powers), `ε ≤ η/10` for
`transverse_ballFill` (five powers) and `densityConstant` (one power). -/
noncomputable def thresholdExponent (β exscal η τ : ℝ) : ℝ :=
  min (min ((exscal - 6 * η) / 2) ((β / 2 - (12 * η + 12 * exscal + 3 * τ)) / 14)) (η / 10)

lemma thresholdExponent_pos {β ζ exscal ϱ η τ τ' : ℝ} (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ') : 0 < thresholdExponent β exscal η τ := by
  have h1 := params.slabDensity
  have h2 := params.slab
  unfold thresholdExponent
  refine lt_min (lt_min ?_ ?_) ?_ <;> linarith

lemma thresholdExponent_le_density (β exscal η τ : ℝ) :
    thresholdExponent β exscal η τ ≤ (exscal - 6 * η) / 2 :=
  le_trans (min_le_left _ _) (min_le_left _ _)

lemma thresholdExponent_le_final (β exscal η τ : ℝ) :
    thresholdExponent β exscal η τ ≤ (β / 2 - (12 * η + 12 * exscal + 3 * τ)) / 14 :=
  le_trans (min_le_left _ _) (min_le_right _ _)

lemma thresholdExponent_le_eta (β exscal η τ : ℝ) :
    thresholdExponent β exscal η τ ≤ η / 10 :=
  min_le_right _ _

/-- **The one fact conjunct 2 of `Kakeya.VeryNotSticky.SideDataObligations` still needs**: a
thin configuration over the pinned `bd` whose comparison constant is sub-polynomial in `δ⁻¹`,
`tc.C ≤ δ^{-ε}`. The binders are those of conjunct 2. The existing producer
`Kakeya.VeryNotSticky.exists_thinConfig` exposes no constant; the one it builds is
`bd.Cg · thinSetupConstant … Ccore …` with `Ccore ≥ thinEnvelopeTerm 3 #segs #bodies CF w₁`
at every ball. Before pack F13 that envelope was bounded below by a
positive constant times the number of segments — an artefact of the old body `⌈x⌉₊` of
`Kakeya.ThinCase.twoPowExponent`, now `⌊log₂ ⌈x⌉₊⌋ + 1`
(`Kakeya.ThinCase.two_pow_twoPowExponent_le`) — so the obligation was out of reach; after F13
the envelope is polylogarithmic in `#segs`, `#bodies` and `δ⁻¹`, and the producer
`exists_thinConfig_le` is pending. -/
def ThinConstantObligation (β exscal ϱ η ε : ℝ) (C₀bd Cbias CF Cdil c₁ Cg : NNReal)
    (D : ℕ) : Prop :=
  ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
    cfg.a = cfg.δ → cfg.b = cfg.δ →
    bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.Cdil = Cdil → bd.c₁ = c₁ → bd.D = D →
    bd.Cg = Cg → bd.m = 1 → bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
    ∃ tc : ThinConfig cfg bd, tc.C ≤ cfg.δ ^ (-ε)

/-- **Conjunct 2 of `Kakeya.VeryNotSticky.SideDataObligations`, from the thin-constant
obligation.** Its conclusion is that conjunct verbatim. Given `tc` with
`tc.C ≤ δ^{-thresholdExponent β exscal η τ}`, the thresholds follow:
`Kakeya.VeryNotSticky.SlabScale` by `Kakeya.VeryNotSticky.eventually_slabScale_of_C_le`,
`Kakeya.VeryNotSticky.CaseScale` at `tc.C` and the trivial bundle
`Kakeya.VeryNotSticky.unitScaleThresholds` by
`Kakeya.VeryNotSticky.eventually_caseScale_of_C_le` (O5 vacuous at `a = b = δ`), and the
tangential density threshold by `Kakeya.VeryNotSticky.eventually_densityConstant_of_C_le`.
The exponent gaps come from `Kakeya.VeryNotSticky.CaseParams` alone (`slabDensity`,
`slabBias`, `slab`, `scale`, `thinScale`, `hτ`, `hτ'`). -/
theorem sideDataObligations_conjunct2_of_thinConstant {β ζ exscal ϱ η τ τ' : ℝ}
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ}
    (h : ThinConstantObligation.{u} β exscal ϱ η (thresholdExponent β exscal η τ)
      C₀bd Cbias CF Cdil c₁ Cg D) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
    cfg.a = cfg.δ → cfg.b = cfg.δ →
    bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.Cdil = Cdil → bd.c₁ = c₁ → bd.D = D →
    bd.Cg = Cg → bd.m = 1 → bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
    ∃ (tc : ThinConfig cfg bd) (thr₀ : ScaleThresholds),
      SlabScale cfg bd tc τ ∧
      CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀ ∧
      ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  set ε := thresholdExponent β exscal η τ with hεdef
  have hε := thresholdExponent_pos hη params
  have hεd := thresholdExponent_le_density β exscal η τ
  have hεf := thresholdExponent_le_final β exscal η τ
  have hεη := thresholdExponent_le_eta β exscal η τ
  rw [← hεdef] at hε hεd hεf hεη
  have hslabDensity := params.slabDensity
  have hslab := params.slab
  have hscale := params.scale
  have hτ := params.hτ
  have hτ' := params.hτ'
  have hanti : 2 * ϱ < exscal := by
    have h := params.slabBias
    rw [parameterSeparationConstant] at h
    nlinarith
  filter_upwards [h,
    eventually_slabScale_of_C_le.{u} (β := β) (exscal := exscal) (η := η) (ϱ := ϱ) (τ := τ)
      (ε := ε) C₀bd Cbias Cdil (by linarith) hanti (by linarith),
    eventually_caseScale_of_C_le.{u} C₀bd Cbias hC₀bd (exscal := exscal) (η := η) (ϱ := ϱ)
      (τ := τ) (τ' := τ') (ν := τ' * β / 2) (ε := ε) hexscal (by linarith) hη hϱ
      (by linarith) params.thinScale (by linarith),
    eventually_densityConstant_of_C_le (η := η) (ε := ε) (by linarith)] with
    d hC hslabS hcaseS hdens
  intro cfg bd hδ hβ hη' hex hϱ' ha hb hC₀ hCb hCF hCdil hc₁ hD hCg hm hCm hδw₁ hw₁
  obtain ⟨tc, htc⟩ := hC cfg bd hδ hβ hη' hex hϱ' ha hb hC₀ hCb hCF hCdil hc₁ hD hCg hm hCm hδw₁ hw₁
  rw [hδ] at htc
  have h1C : 1 ≤ tc.C := by
    obtain ⟨B, hB⟩ := bd.bs_nonempty
    exact (tc.tb B hB).one_le_C
  refine ⟨tc, unitScaleThresholds, ?_, ?_, ?_⟩
  · exact hslabS cfg bd tc hδ hβ hex hη' hϱ' hC₀ hCb hCdil.le (fibreBudget_of_pins hm hCm) h1C
      htc
  · rw [hβ]
    exact hcaseS cfg bd unitScaleThresholds tc.C hδ hex hη' hϱ' hC₀ hCb (ha.trans hb.symm) h1C htc
      (by simpa using cfg.hδ1) (by simpa using cfg.hδ1)
  · rw [hδ, hη']
    exact hdens tc.C htc

/-! ### Tripwires: the lemma is conjunct 2 of `SideDataObligations` -/

/-- Tripwire 1: the conclusion of `sideDataObligations_conjunct2_of_thinConstant` slots into the
second component of `Kakeya.VeryNotSticky.SideDataObligations` by the anonymous constructor,
with the other five conjuncts taken from any witness of the `Prop`. -/
example {β ζ exscal ϱ η τ τ' : ℝ} (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ}
    (hall : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D)
    (hT6 : ThinConstantObligation.{u} β exscal ϱ η (thresholdExponent β exscal η τ)
      C₀bd Cbias CF Cdil c₁ Cg D) :
    SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D :=
  ⟨hall.1, sideDataObligations_conjunct2_of_thinConstant hexscal hϱ hη params hC₀bd hT6,
    hall.2.2.1, hall.2.2.2.1, hall.2.2.2.2⟩

/-- Tripwire 2: the lemma's conclusion, read back from the `Prop` — the second projection of
`SideDataObligations` is exactly its type. -/
example {β ζ exscal ϱ η τ τ' : ℝ} (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ}
    (hall : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D)
    (hT6 : ThinConstantObligation.{u} β exscal ϱ η (thresholdExponent β exscal η τ)
      C₀bd Cbias CF Cdil c₁ Cg D) :
    sideDataObligations_conjunct2_of_thinConstant hexscal hϱ hη params hC₀bd hT6 = hall.2.1 :=
  rfl


/-! ### Facts about the thin envelope, kept for the producer's sizing -/

/-- The retained-fraction product `L` of the thin envelope is at least one. -/
lemma one_le_thinRetentionLoss (ns nb : ℕ) {w₁ : NNReal} (hw₁ : 0 < w₁) :
    1 ≤ ThinCase.thinRetentionLoss 3 ns nb ((w₁ : ℝ) / 8) 2 := by
  have hlog : ∀ m : ℕ, (1 : NNReal) ≤ ((Nat.log 2 m + 1 : ℕ) : NNReal) := fun m =>
    Nat.one_le_cast.mpr (Nat.succ_le_succ (Nat.zero_le _))
  have hnet : (1 : NNReal) ≤ ((ThinCase.netCardBound 3 ((w₁ : ℝ) / 8) 2 : ℕ) : NNReal) := by
    refine Nat.one_le_cast.mpr (Nat.ceil_pos.mpr ?_)
    have hw : (0 : ℝ) < (w₁ : ℝ) / 8 := by positivity
    positivity
  have hball : (1 : NNReal) ≤ ThinCase.ballNetLoss 3 ((w₁ : ℝ) / 8) 2 := by
    rw [ThinCase.ballNetLoss]
    have hf := Kakeya.one_le_factoringStep1FiberPigeonholeConstant hnet
    calc (1 : NNReal) = 1 * (1 * 1) := by ring
      _ ≤ 5 ^ 3 * (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1
          ((ThinCase.netCardBound 3 ((w₁ : ℝ) / 8) 2 : ℕ) : NNReal)) := by
          gcongr <;> norm_num
  rw [ThinCase.thinRetentionLoss]
  calc (1 : NNReal) = 1 * (1 * 1) * (1 * 1) := by ring
    _ ≤ ((Nat.log 2 ns + 1 : ℕ) : NNReal) * (4 * ThinCase.ballNetLoss 3 ((w₁ : ℝ) / 8) 2) *
        ((5 : NNReal) ^ 3 * ((Nat.log 2 nb + 1 : ℕ) : NNReal)) := by
        gcongr <;> first | exact hlog _ | exact hball | norm_num

/-- The fibre-density band loss `B'` of the thin envelope is at least one once there is a
segment. -/
lemma one_le_fibreDensityBandLoss_toNNReal {ns : ℕ} (hns : 1 ≤ ns) {CF : NNReal}
    (hCF : 1 ≤ CF) : 1 ≤ (ThinCase.fibreDensityBandLoss 3 CF ns).toNNReal := by
  rw [ThinCase.fibreDensityBandLoss, ENNReal.ofReal, ENNReal.toNNReal_coe, Real.one_le_toNNReal]
  have hV : (1 : ℝ) ≤ ((Metric.volume_comparison.C 3 * CF : NNReal) : ℝ) := by
    have h384 : Metric.volume_comparison.C 3 = 384 := by
      norm_num [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c, Nat.factorial]
    rw [h384]
    have : (1 : NNReal) ≤ 384 * CF := by
      calc (1 : NNReal) = 1 * 1 := by ring
        _ ≤ 384 * CF := by gcongr; norm_num
    exact_mod_cast this
  have hns' : (1 : ℝ) ≤ (ns : ℝ) := by exact_mod_cast hns
  have hx : (1 : ℝ) ≤ (ns : ℝ) * ((Metric.volume_comparison.C 3 * CF : NNReal) : ℝ) :=
    one_le_mul_of_one_le_of_one_le hns' hV
  linarith [Real.logb_nonneg one_lt_two hx]

/-- The carrier-weighted Step 1 loss at the eccentricity exponent `N` is at least `2 (N + 1)`:
its logarithm is `log₂ (ns · C_vol · 2^N) ≥ N`. -/
lemma two_mul_succ_le_weightedStep1AtScaleConstant {ns : ℕ} (hns : 1 ≤ ns) (N : ℕ) :
    2 * ((N : NNReal) + 1) ≤ ShadedBody.FactorFamily.weightedStep1AtScaleConstant 3 ns N := by
  rw [ShadedBody.FactorFamily.weightedStep1AtScaleConstant,
    Kakeya.factoringStep1PigeonholeConstant_eq, Kakeya.factoringStep1FiberPigeonholeConstant,
    Kakeya.weightedStep1LowerBd, Kakeya.weightedStep1UpperBd]
  gcongr
  have hV : (0 : ℝ) < ((Metric.volume_comparison.C 3 : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Metric.volume_comparison.C_pos 3)
  have hV1 : (1 : ℝ) ≤ ((Metric.volume_comparison.C 3 : NNReal) : ℝ) := by
    have h384 : Metric.volume_comparison.C 3 = 384 := by
      norm_num [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c, Nat.factorial]
    rw [h384]; norm_num
  have hns' : (1 : ℝ) ≤ (ns : ℝ) := by exact_mod_cast hns
  have h2N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hprod : (((ns : NNReal) : ℝ)) /
      (((Metric.volume_comparison.C 3 * 2 ^ N)⁻¹ : NNReal) : ℝ)
      = (ns : ℝ) * ((Metric.volume_comparison.C 3 : NNReal) : ℝ) * (2 : ℝ) ^ N := by
    rw [NNReal.coe_inv, div_inv_eq_mul]; push_cast; ring
  have hlog : Real.logb 2 ((ns : ℝ) * ((Metric.volume_comparison.C 3 : NNReal) : ℝ) *
      (2 : ℝ) ^ N) = Real.logb 2 ((ns : ℝ) * ((Metric.volume_comparison.C 3 : NNReal) : ℝ)) +
        (N : ℝ) := by
    rw [Real.logb_mul (by positivity) h2N.ne', Real.logb_pow, Real.logb_self_eq_one one_lt_two,
      mul_one]
  have hnn : (0 : ℝ) ≤ Real.logb 2 ((ns : ℝ) * ((Metric.volume_comparison.C 3 : NNReal) : ℝ)) :=
    Real.logb_nonneg one_lt_two (one_le_mul_of_one_le_of_one_le hns' hV1)
  have hkey : ((N : ℝ) + 1) ≤ 1 + Real.logb 2 ((((ns : NNReal) : ℝ)) /
      (((Metric.volume_comparison.C 3 * 2 ^ N)⁻¹ : NNReal) : ℝ)) := by
    rw [hprod, hlog]
    linarith
  rw [Real.le_toNNReal_iff_coe_le (by linarith)]
  push_cast
  exact hkey


end Kakeya.VeryNotSticky
