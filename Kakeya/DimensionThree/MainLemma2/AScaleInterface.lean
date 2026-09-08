/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AScaleResidues
public import Kakeya.DimensionThree.MainLemma2.AScaleRounding
public import Kakeya.DimensionThree.MainLemma2.AScaleSetup

/-!
# The scale-`r` interface of Main Lemma 2, very not sticky case

This file assembles, from proved material and from the two statements that Sections 3 and 5 owe
the development, exactly the inputs that `Kakeya.VeryNotSticky.exists_aScaleData` (blueprint
`lem:ml2aScaleData`) needs.

What it consumes:

* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` — Section 5, blueprint
  `shadingMultiplicityEstimateForRhoTubes` at a *grid* scale, with pairwise essential
  distinctness of the coarse family replaced by the bounded overlap that
  `Tube.UniformTubeSet` actually carries;
* `Kakeya.VeryNotSticky.coarseKatzTaoBound` — Section 3, blueprint `genKKT` at the coarse
  family, with the same substitution and with the two `genKKT` thresholds absorbed.

Both live in `Kakeya.DimensionThree.MainLemma2.AScaleResidues`, with docstrings recording who
owns them, what they absorb, and where the losses are paid. Both are stated at the
configuration's *own* hierarchy — the shaded bundle of `Kakeya.VeryNotSticky.uniform`, at the
grid length `⌈log log 1/δ⌉` and the constant `cfg.C₀` — and not at a universally quantified
one: the substitution of bounded overlap for essential distinctness costs a factor `C₀`, so a
`C₀` quantified before the statement would leave that loss with nothing to pay it. At the
configuration's own constant the loss is sub-polynomial,
`Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta`.

## The scale objection is withdrawn

Earlier versions of this file, and the third remark of blueprint `lem:ml2aScaleData`, asserted
that the parent family `𝕋_r` at a general radius is a genuine obstruction, because the
transverse consumer invokes the interface at `r = θ b`, which is not a scale of the multiscale
grid. That is wrong, and the reason is elementary. The grid of GWZ Definition 2.1 has length
`N = ⌈log log 1/δ⌉`, so consecutive scales differ by `δ^{1/N}`, which is *sub-polynomially*
close to `1`: `δ^{-1/N} ≤ δ^{-ε}` for every fixed `ε > 0` once `δ` is small. Rounding an
arbitrary radius up to the nearest grid scale therefore costs nothing on the polynomial scale.
That is the design intent of the grid length `log log 1/δ`, and the same computation is already
recorded in the docstrings of `Tube.exists_uniformTubeSet_subfamily` and of
`Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, the lemma that actually
produces the bundle in `Kakeya.VeryNotSticky.uniform`. GWZ perform exactly this rounding
themselves at p. 41 — "we choose a radius `r` of the form `r = δ^{ηj}` with
`θ b ≤ r ≤ δ^{-η} θ b`" — paying `δ^{3η}`; rounding to the Definition 2.1 grid instead costs
`δ^{3/N}`, which is strictly cheaper.

The rounding is `Kakeya.VeryNotSticky.exists_gridIndex`, and its cost is charged as follows
(see `Kakeya.DimensionThree.MainLemma2.AScaleRounding`):

* the tube-volume comparison at `Kakeya.tubeVolumeRatioConstant 3` costs **nothing**. It was
  believed to pull against the two-scale multiplicity bound, one wanting a parent radius `≤ r`
  and the other `≥ r`; under rounding the parent radius *is* the grid scale for both, and the
  comparison is monotone in it, so it holds with no constant inflation
  (`Kakeya.tubeVolumeRatio_of_le`);
* the two-scale multiplicity bound costs `(ρ/r)² ≤ δ^{-2η}`, charged to the gain by reading the
  parent multiplicity at `δ^{ν/45} δ^η Δ_max(𝕋_ρ)`;
* the ball estimate costs the ratio of ball volumes `(ρ/r)³ ≤ δ^{-3η}`, charged to the factor
  `δ^{ν/9}` that `Kakeya.VeryNotSticky.AScaleData` carries — together with a further `δ^{η}`,
  the room in which Section 5 pays the `C₀` of the overlap substitution, so that the actual
  requirement is `ν ≥ 36 η`.

All charges are covered by the standing budget `ν ≥ 90 η`. The single new hypothesis is the
configuration field `Kakeya.VeryNotSticky.gridFine`, `1 ≤ η ⌈log log 1/δ⌉`, a condition on `δ`
alone which is arrangeable because `η` is fixed before `δ`.

## What is still absorbed

The upper bound `r ≤ 1` on the radius, a hypothesis of blueprint `lem:ml2aScaleData`, is *not*
absorbed anywhere: it is an explicit hypothesis of every statement below, and of
`Kakeya.VeryNotSticky.exists_aScaleData` itself, where it is the binder `hr1`. It has to be,
because without it those statements are false — at radii larger than the unit ball that
contains the tubes, estimate (ii) carries a factor `r^{2β}` on its left with nothing to match
it, so the unrestricted form is *refutable* and not merely unproved. It is no longer a gap:
both consumers discharge it, the thick branch at `r = cfg.a` through
`Kakeya.VeryNotSticky.cfg_a_le_one` and the transverse branch through
`Kakeya.VeryNotSticky.transverseFillRadius_le_one`. See the docstring of
`Kakeya.VeryNotSticky.exists_aScaleData`.

The two scale thresholds of blueprint `genKKT`, `δ < δ₀(ν/90, β)` and `η ≤ η_genKKT(ν/90, β)`,
remain absorbed, but into `Kakeya.VeryNotSticky.coarseKatzTaoBound`, which is where the
Katz–Tao estimate enters and which is owned by Section 3.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

/-- **Estimate (i) transported from the grid scale to the nominal radius** (blueprint
`lowerBoundTTScaleAAndABall`, clause (i) of `lem:ml2aScaleData`).

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` delivers the ball estimate at the grid
scale `ρ`; the consumer needs it at the nominal radius `r ≤ ρ`. Shrinking the ball shrinks its
intersection with the shaded union, but it also shrinks the ball itself, so the density
`|U ∩ B_r| / |B_r|` is not monotone: what is true is

`|U ∩ B_r| / |B_r| ≤ (ρ/r)³ · |U ∩ B_ρ| / |B_ρ|`,

the cube being the dimension (`Kakeya.volume_ball_mul_pow_comm`). The factor `(ρ/r)³` is one
grid step cubed, hence at most `δ^{-3η}`, and it is paid for by the `δ^{ν/9}` that
`Kakeya.VeryNotSticky.AScaleData` carries.

**Two charges are made against that `δ^{ν/9}`, not one, and both fit.** The hypothesis `hball`
is the ball conjunct of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`, which carries a
factor `δ^{cfg.η}` on its small side: that is the room out of which Section 5 pays the factor
`C₀` incurred by using bounded overlap in place of pairwise essential distinctness
(`Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta`). So the gain available for the change of ball
radius is `ν/9 - η`, and the requirement is `ν/9 - η ≥ 3η`, i.e. `ν ≥ 36 η`
(`Kakeya.VeryNotSticky.rpow_sub_eta_mul_cube_le_cube_of_gridStep`). The standing budget is
`ν ≥ 90 η`, so the surplus `ν/9 - 4η ≥ 6η` is left unspent and the *conclusion* is exactly what
it was before the factor was introduced: no downstream statement moves.

**The uniformity of the constant in the centre `x` is preserved**, and that is the point of the
statement. The constant is the fixed
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` that the section-5 interface
carries, quantified before `x`: one constant, valid simultaneously for all admissible centres.
Blueprint `lem:ml2goalfromdens` applies estimate (i) at the ball supplied by its density
hypothesis, and that hypothesis is stated at the constant `C ^ 2` produced here; a constant
depending on the ball would make the density currency, and hence that reduction, circular. The
`⪆` of `boundVolumeAcrossTwoScales` hides exactly this quantifier, which is why the requirement
is written out. Reading the constant at the section-5 value rather than existentially is also
what makes `Kakeya.aScaleBallConstant` a closed term, and hence what lets Configuration
`hyp:ml2setup` fix `δ` below a threshold absorbing it. -/
theorem coarseBallEstimate_of_gridScale (cfg : VeryNotSticky.{u}) {ν : ℝ}
    (hνη : 90 * cfg.η ≤ ν) {r ρ : NNReal} (hr0 : 0 < r) (hrρ : r ≤ ρ)
    (hρr : ρ ≤ cfg.δ ^ (-cfg.η) * r) {κ : Type*} {Cb : NNReal}
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι κ)
    (hball : ∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
      (cfg.δ : ENNReal) ^ cfg.η *
          (((Cb : NNReal) : ENNReal)⁻¹ *
              volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
              volume (ball x (ρ : ℝ)))) ≤
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) :
    ∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
      (cfg.δ : ENNReal) ^ (ν / 9) *
          (((Cb : NNReal) : ENNReal)⁻¹ *
              volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ)) /
              volume (ball x (r : ℝ)))) ≤
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade) := by
  classical
  intro x hx
  set W : ENNReal := volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
  set Uin : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ G.innerSet, (G.innerBody i).shade
  set V : ENNReal := volume Uin
  set C : ENNReal := ((Cb : NNReal) : ENNReal)
  set d9 : ENNReal := (cfg.δ : ENNReal) ^ (ν / 9)
  set dη : ENNReal := (cfg.δ : ENNReal) ^ cfg.η
  set dRest : ENNReal := (cfg.δ : ENNReal) ^ (ν / 9 - cfg.η)
  set Ar : ENNReal := volume (Uin ∩ ball x (r : ℝ))
  set Aρ : ENNReal := volume (Uin ∩ ball x (ρ : ℝ))
  set Br : ENNReal := volume (ball x (r : ℝ))
  set Bρ : ENNReal := volume (ball x (ρ : ℝ))
  have hr0' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := lt_of_lt_of_le hr0' (by exact_mod_cast hrρ)
  have hBr0 : Br ≠ 0 := (Metric.measure_ball_pos volume x hr0').ne'
  have hBρ0 : Bρ ≠ 0 := (Metric.measure_ball_pos volume x hρ0).ne'
  have hBrTop : Br ≠ ⊤ := ne_of_lt (MeasureTheory.measure_ball_lt_top (x := x) (r := (r : ℝ)))
  have hBρTop : Bρ ≠ ⊤ := ne_of_lt (MeasureTheory.measure_ball_lt_top (x := x) (r := (ρ : ℝ)))
  have hrENN0 : (r : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hr0.ne'
  have hpw3 : (r : ENNReal) ^ 3 ≠ (0 : ENNReal) := pow_ne_zero 3 hrENN0
  have hpw3top : (r : ENNReal) ^ 3 ≠ (⊤ : ENNReal) := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr cfg.hδ.ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hA : Ar ≤ Aρ := by
    dsimp [Ar, Aρ]
    exact measure_mono
      (inter_subset_inter_right Uin (Metric.ball_subset_ball (by exact_mod_cast hrρ)))
  have hcuberest : dRest * (ρ : ENNReal) ^ 3 ≤ (r : ENNReal) ^ 3 := by
    dsimp [dRest]
    exact rpow_sub_eta_mul_cube_le_cube_of_gridStep (cfg := cfg) (hνη := hνη) (hρ := hρr)
  have hBrest : dRest * Bρ ≤ Br := by
    have hstep : (r : ENNReal) ^ 3 * (dRest * Bρ) ≤ (r : ENNReal) ^ 3 * Br := by
      calc
        (r : ENNReal) ^ 3 * (dRest * Bρ)
            = dRest * ((r : ENNReal) ^ 3 * Bρ) := by ring
        _ = dRest * ((ρ : ENNReal) ^ 3 * Br) := by
            rw [volume_ball_mul_pow_comm x r ρ]
        _ = (dRest * (ρ : ENNReal) ^ 3) * Br := by ring
        _ ≤ (r : ENNReal) ^ 3 * Br := by
            dsimp [dRest]
            gcongr
    have hc : (dRest * Bρ) * (r : ENNReal) ^ 3 ≤ Br * (r : ENNReal) ^ 3 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
    exact (ENNReal.mul_le_mul_iff_left hpw3 hpw3top).mp hc
  have hnumRest : (dRest * Ar) * Bρ ≤ Aρ * Br := by
    calc
      (dRest * Ar) * Bρ = Ar * (dRest * Bρ) := by dsimp [dRest]; ring
      _ ≤ Aρ * Br := by exact mul_le_mul' hA hBrest
  have hdivRest : dRest * (Ar / Br) ≤ Aρ / Bρ := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hBρ0) (Or.inl hBρTop)]
    calc
      (dRest * (Ar / Br)) * Bρ = dRest * Ar * Bρ * (Br : ENNReal)⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ Aρ := by
        calc
          dRest * Ar * Bρ * (Br : ENNReal)⁻¹ ≤ Aρ * Br * (Br : ENNReal)⁻¹ := by
            gcongr
          _ = Aρ * (Br * (Br : ENNReal)⁻¹) := by ring
          _ = Aρ := by
            rw [ENNReal.mul_inv_cancel hBr0 hBrTop]
            simp
  have hd9 : d9 = dη * dRest := by
    dsimp [d9, dη, dRest]
    rw [← ENNReal.rpow_add cfg.η (ν / 9 - cfg.η) hδ0 hδtop]
    congr 1
    ring
  calc
    d9 * (C⁻¹ * W * (Ar / Br))
        = dη * (C⁻¹ * W * (dRest * (Ar / Br))) := by
            rw [hd9]
            ring
    _ ≤ dη * (C⁻¹ * W * (Aρ / Bρ)) := by
            gcongr
    _ ≤ V := hball x hx

/-- **`Kakeya.VeryNotSticky.coarseMassBound` with the fullness exponent left free.**

The exponent enters that lemma at exactly one place, the conversion of fullness into a lower
bound on the shaded sum (`ShadedBody.coe_fullness_mul_le_sum_volume_shade`), and comes straight
back out in the conclusion.  The honest coarse family needs it at `3 cfg.η` rather than
`2 cfg.η`; see `Kakeya.VeryNotSticky.rpow_three_eta_le_of_inducedFullness`. -/
theorem coarseMassBound_atFullness (cfg : VeryNotSticky.{u}) {κ : Type*} {t : Finset κ}
    {V : κ → ShadedBody (EuclideanSpace ℝ (Fin 3))} {Δ volTa : ENNReal} {ν e : ℝ}
    (hν : 0 < ν) (ha1 : cfg.a ≤ 1) (hδa : cfg.δ ≤ cfg.a)
    (hfull : (cfg.δ : NNReal) ^ e ≤ ShadedBody.fullness t V)
    (hvolTa : ∀ i ∈ t, volTa ≤ volume (V i).carrier)
    (hKT : ShadedBody.multiplicity t V ≤
      (cfg.a : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * (t.card : ENNReal) ^ cfg.β) :
    (cfg.δ : ENNReal) ^ e * ((t.card : ENNReal) * volTa) ≤
      (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * (t.card : ENNReal) ^ cfg.β *
        volume (⋃ i ∈ t, (V i).shade) := by
  have hsum : (cfg.δ : ENNReal) ^ e * ((t.card : ENNReal) * volTa) ≤
      ∑ i ∈ t, volume (V i).shade := by
    simpa [ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne'] using
      (ShadedBody.coe_fullness_mul_le_sum_volume_shade t V (a := cfg.δ ^ e)
        (c := volTa) hfull hvolTa)
  have ha_le : (cfg.a : ENNReal) ^ (-(ν / 90)) ≤ (cfg.δ : ENNReal) ^ (-(ν / 90)) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow (by exact_mod_cast hδa) (by positivity))
  calc
    (cfg.δ : ENNReal) ^ e * ((t.card : ENNReal) * volTa)
        ≤ ∑ i ∈ t, volume (V i).shade := hsum
    _ = ShadedBody.multiplicity t V * volume (⋃ i ∈ t, (V i).shade) := by
        rw [ShadedBody.sum_shade_eq_multiplicity_mul_union]
    _ ≤ (cfg.a : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * (t.card : ENNReal) ^ cfg.β *
          volume (⋃ i ∈ t, (V i).shade) := by
        gcongr
    _ ≤ (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * (t.card : ENNReal) ^ cfg.β *
          volume (⋃ i ∈ t, (V i).shade) := by
        gcongr

/-- **The scale-`r` parent data, assembled at a grid scale** (blueprint `uniformSetOfTubes` at
`ρ = ρ_k`, blueprint `volumeOfTTa`, clause (ii) of `lem:ml2aScaleData`).

The four geometric inputs of `Kakeya.VeryNotSticky.aScaleVolume` — a reference tube volume
`volT` factoring `∑_{T ∈ 𝕋} |T|`, a parent tube volume `volTa`, a parent multiplicity `Δ`, and
the two cardinalities `Na = |𝕋_ρ|` and `Nf = |𝕋[T_ρ]|` — read at the coarse union
`U(𝕋_ρ, Y_{𝕋_ρ}) = ⋃ j ∈ G.outerSet, (G.outerBody j).shade`, together with the four estimates
they must satisfy. Feeding them to `aScaleVolume` is estimate (ii); this statement produces the
inputs, not the estimate, so that the rearrangement and the exponent budget
`Kakeya.aScaleExponentBudget` are still genuinely performed.

The witnesses are explicit, and each estimate is proved:

* `volT = Kakeya.VeryNotSticky.meanTubeVolume cfg`, the mean tube volume. The blueprint writes
  `∑_{T ∈ 𝕋} |T| = |T| |𝕋|` with `|T|` "the" tube volume; the development has no congruence
  lemma for tubes, so there is no common value, and the mean does the same work — it factors
  the sum exactly and inherits the dimensional upper bound `C₃ δ²`.
* `volTa = c₃ ρ²`, the dimensional *lower* bound of `Tube.le_volume` for a `ρ`-tube.
  With these two the tube-volume comparison is `Kakeya.tubeVolumeRatio_of_le`, and it costs
  nothing: `r ≤ ρ` enters in the harmless direction.
* `Na = |𝕋_ρ|` and `Nf = |𝕋[T_ρ]|` at an active node `T_ρ`; the counting bound is
  `Kakeya.VeryNotSticky.card_le_card_activeTubeNodes_mul`, which is scale-free, and `Na ≠ 0` is
  `Kakeya.VeryNotSticky.activeTubeNodes_nonempty`.
* `Δ = δ^{ν/45} δ^η Δ_max(𝕋_ρ)`. The two-scale multiplicity bound of blueprint
  `lem:ml2DeltamaxScaleA` is `Kakeya.VeryNotSticky.maxDensity_activeTubeNodes_le`, which holds
  verbatim at every grid scale, and the factor `δ^{ν/45}` is what converts its right-hand side
  `ρ²` into the `r²` the consumer wants
  (`Kakeya.VeryNotSticky.rpow_mul_sq_le_sq_of_gridStep`).
* The mass bound is `Kakeya.VeryNotSticky.coarseMassBound`, which is proved, applied to the
  Katz–Tao input `Kakeya.VeryNotSticky.coarseKatzTaoBound`. That input is the whole residue of
  this statement, and it is owned by Section 3.

The two uniformity constants are the configuration's own `cfg.C₀` and `cfg.D₀`, not fresh
existentials: the parent family is the node family of the hierarchy `cfg.uniform` is uniform
for, so its branching and overlap constants are those of `cfg`. That is what ties the constant
`Kakeya.aScaleVolumeConstant cfg.C₀ cfg.D₀` produced here to the constant
`Kakeya.aScaleDataConstant cfg.C₀ cfg.D₀` absorbed by
`Kakeya.VeryNotSticky.aScaleData_absorb`.

**`cfg.D₀` is pinned by nothing beyond `1 ≤ D₀`, and this statement is an obligation at
whatever `D₀` the producer picks.** In the Lean bundle `Tube.UniformTubeSet` the
assignment is a *function*, so its classes partition `𝕋` and the honest overlap constant is
`D₀ = 1`; `D₀` is carried as a free parameter only so that the constants of blueprint
`def:ml2DeltamaxScaleAConstant` and `def:ml2aScaleVolumeConstant` read as the blueprint writes
them. Since those constants are monotone in `D₀`, the statement at a larger `D₀` is weaker, so
nothing is lost. -/
theorem rScaleParentData_of_gridScale (cfg : VeryNotSticky.{u}) {ν : ℝ} (hν : 0 < ν)
    (hνη : 90 * cfg.η ≤ ν) (hνwe : cfg.ckt.we ≤ ν / 180)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {r ρ : NNReal}
    (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (har : cfg.a ≤ r) (hr1 : r ≤ 1) (hrρ : r ≤ ρ) (hρr : ρ ≤ cfg.δ ^ (-cfg.η) * r)
    (hρ1 : ρ ≤ 1) (hrsmall : r ≤ 6 * cfg.δ ^ cfg.exscal)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒰 k)
    (houterBody : ∀ j ∈ G.outerSet,
      (G.outerBody j).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody)
    (hfull : (cfg.δ : NNReal) ^ (3 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody) :
    ∃ volT volTa Δ Na Nf : ENNReal,
      Na ≠ 0 ∧ Na ≠ ⊤ ∧ Nf ≠ ⊤ ∧
      ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier = volT * (cfg.s.card : ENNReal) ∧
      (cfg.δ : ENNReal) ^ (3 * cfg.η) * (Na * volTa) ≤
        (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * Na ^ cfg.β *
          volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) ∧
      Δ * (Nf * (cfg.δ : ENNReal) ^ 2) ≤
        (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (r : ENNReal) ^ 2 ∧
      (tubeVolumeRatioConstant 3 : ENNReal) * ((r : ENNReal) ^ 2 * volT) ≤
        (cfg.δ : ENNReal) ^ 2 * volTa ∧
      (cfg.s.card : ENNReal) ≤ (cfg.C₀ : ENNReal) ^ 2 * (Na * Nf) := by
  classical
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨j, hj⟩ := activeTubeNodes_nonempty cfg 𝒰 hk (s_nonempty cfg)
  have hjIdx : j ∈ 𝒰.cover.indexSet k := mem_indexSet_of_mem_activeTubeNodes cfg 𝒰 hj
  let volT : ENNReal := cfg.meanTubeVolume
  let volTa : ENNReal := (Tube.le_volume.c 3 : ENNReal) * (ρ : ENNReal) ^ 2
  let Na : ENNReal := (G.outerSet.card : ENNReal)
  let Nf : ENNReal := ((cfg.tubeFibre 𝒰 k j).card : ENNReal)
  let md : ENNReal := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j' => (𝒰.cover.tube k j').toConvexSpaceBody)
  let Delta : ENNReal := (cfg.δ : ENNReal) ^ (2 * cfg.η) *
    ((cfg.δ : ENNReal) ^ cfg.η * md)
  have hVol : ∀ j0 ∈ G.outerSet, volTa ≤ volume (G.outerBody j0).carrier := by
    intro j0 hj0
    have hlb : (Tube.le_volume.c 3 : ENNReal) * (ρ : ENNReal) ^ 2 ≤
        volume (𝒰.cover.tube k j0).carrier := by
      simpa [hfin, hgrid] using (Tube.le_volume (𝒰.cover.tube k j0))
    have hcar1 : (G.outerBody j0).carrier = (𝒰.cover.tube k j0).carrier :=
      congrArg ConvexSpaceBody.carrier (houterBody j0 hj0)
    dsimp [volTa]
    rw [hcar1]
    exact hlb
  have hKT : ShadedBody.multiplicity G.outerSet G.outerBody ≤
      (cfg.a : ENNReal) ^ (-(ν / 90)) * Delta ^ (1 - cfg.β) *
        (G.outerSet.card : ENNReal) ^ cfg.β := by
    simpa [Delta, md] using
      (coarseKatzTaoBound_of_etaBudget_atPair_atFullness cfg (ν := ν) (ε₀ := cfg.ckt.we)
        (e := 3 * cfg.η) (by linarith)
        (by
          have h1 := cfg.ckt.hηbud
          have hexs : (0 : ℝ) < cfg.exscal := cfg.hexscal
          have hβ1 : cfg.β ≤ 1 := cfg.hβ1
          have hβ0 : (0 : ℝ) < cfg.β := cfg.hβ
          have hη0 : (0 : ℝ) < cfg.η := cfg.hη
          nlinarith [mul_le_mul_of_nonneg_left
            (show cfg.ckt.we ≤ ν / 90 - cfg.ckt.we by linarith) hexs.le])
        cfg.ckt.hwη cfg.ckt.hwρhalf cfg.ckt.hwin 𝒰 hk hgrid ⟨le_trans har hrρ, hρ1⟩
        (le_trans (coarseRadius_of_grid cfg hρr hrsmall) cfg.ckt.hδrad) cfg.ckt.hηKT
        G houterSet houterBody hfull)
  have hMass : (cfg.δ : ENNReal) ^ (3 * cfg.η) * ((G.outerSet.card : ENNReal) * volTa) ≤
      (cfg.δ : ENNReal) ^ (-(ν / 90)) * Delta ^ (1 - cfg.β) *
        (G.outerSet.card : ENNReal) ^ cfg.β *
        volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) := by
    exact coarseMassBound_atFullness cfg hν (le_trans har hr1) cfg.hdims.1 hfull hVol hKT
  have hstep : (cfg.δ : ENNReal) ^ (2 * cfg.η) * (ρ : ENNReal) ^ 2 ≤ (r : ENNReal) ^ 2 :=
    rpow_two_eta_mul_sq_le_sq_of_gridStep (cfg := cfg) (hρ := hρr)
  have hMax : md * Nf * (cfg.δ : ENNReal) ^ cfg.η * (cfg.δ : ENNReal) ^ 2 ≤
      (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (ρ : ENNReal) ^ 2 := by
    simpa [md, Nf] using (maxDensity_activeTubeNodes_le cfg cfg.hC₀ 𝒰 hk cfg.hD₀ hjIdx hgrid hρ1)
  refine ⟨volT, volTa, Delta, Na, Nf, ?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7, ?c8⟩
  · have hNon : G.outerSet.Nonempty := by
      rw [houterSet]
      exact activeTubeNodes_nonempty cfg 𝒰 hk (s_nonempty cfg)
    have hpos : 0 < G.outerSet.card := Finset.card_pos.mpr hNon
    dsimp [Na]
    exact_mod_cast (ne_of_gt hpos)
  · dsimp [Na]
    exact ENNReal.natCast_ne_top _
  · dsimp [Nf]
    exact ENNReal.natCast_ne_top _
  · dsimp [volT]
    exact sum_volume_eq cfg
  · simpa [Na] using hMass
  · calc
      Delta * (Nf * (cfg.δ : ENNReal) ^ 2)
          = (cfg.δ : ENNReal) ^ (2 * cfg.η) *
              (md * Nf * (cfg.δ : ENNReal) ^ cfg.η * (cfg.δ : ENNReal) ^ 2) := by
            dsimp [Delta]
            ring
      _ ≤ (cfg.δ : ENNReal) ^ (2 * cfg.η) *
            ((deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (ρ : ENNReal) ^ 2) := by
            gcongr
      _ = (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) *
            ((cfg.δ : ENNReal) ^ (2 * cfg.η) * (ρ : ENNReal) ^ 2) := by
            ring
      _ ≤ (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (r : ENNReal) ^ 2 := by
            gcongr
  · dsimp [volT, volTa]
    exact tubeVolumeRatio_of_le hrρ (meanTubeVolume_le cfg)
  · have hcnt : (cfg.s.card : NNReal) ≤
        cfg.C₀ ^ 2 * (((cfg.activeTubeNodes 𝒰 k).card : NNReal) *
          ((cfg.tubeFibre 𝒰 k j).card : NNReal)) :=
      (card_le_card_activeTubeNodes_mul cfg 𝒰 hk cfg.hD₀ hjIdx).1
    dsimp [Na, Nf]
    rw [houterSet]
    exact_mod_cast hcnt

/-- **The complete input of `Kakeya.VeryNotSticky.exists_aScaleData`** (blueprint
`lem:ml2aScaleData`, clauses (i) and (ii)).

One coarse shaded factor family `G` at the rounded grid scale, carrying both estimate (i) at
the nominal radius `r` and the five quantities of estimate (ii). The two clauses must be
produced together because they share the coarse union `U(𝕋_ρ, Y_{𝕋_ρ})`, whose volume occurs on
the *left* of (i) and on the *right* of (ii): neither may be weakened independently of the
other.

The proof is the rounding of `r` to the grid (`Kakeya.VeryNotSticky.exists_gridIndex`), the
Section-5 family at that grid scale
(`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`), and the two bridges above.

Two conjuncts of that family arrive in a weaker form than the bridges consume, and both are
converted here, out of data the configuration carries:

* the outer fullness arrives as `C⁻¹ lam ≤ λ(𝕋_ρ, Y_{𝕋_ρ})`, which is what Section 5 concludes,
  at the per-tube shading density `cfg.lam`; `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale`
  wants it at `δ^{2 cfg.η}`. The field `Kakeya.VeryNotSticky.lam_ge` supplies `δ^{2η} ≤ lam`
  (see its docstring for why the exponent is `2η` and not `η`), and
  `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`;
* the ball estimate arrives with a factor `δ^{cfg.η}` on its small side, and
  `Kakeya.VeryNotSticky.coarseBallEstimate_of_gridScale` absorbs it into the gain.

Neither conversion changes this signature, which is why nothing in
`Kakeya.DimensionThree.MainLemma2.Goals` moves. -/
theorem exists_aScaleInputs (cfg : VeryNotSticky.{u}) {r : NNReal} (hr : cfg.a ≤ r)
    (hr1 : r ≤ 1) (hrsmall : r ≤ 6 * cfg.δ ^ cfg.exscal) {ν : ℝ} (hν : 0 < ν)
    (hνη : 90 * cfg.η ≤ ν) (hνwe : cfg.ckt.we ≤ ν / 180) :
    ∃ (κ : Type u) (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι κ)
      (volT volTa Δ Na Nf : ENNReal),
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ (ν / 9) *
            (((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ)) /
                volume (ball x (r : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) ∧
      Na ≠ 0 ∧ Na ≠ ⊤ ∧ Nf ≠ ⊤ ∧
      ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier = volT * (cfg.s.card : ENNReal) ∧
      (cfg.δ : ENNReal) ^ (3 * cfg.η) * (Na * volTa) ≤
        (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * Na ^ cfg.β *
          volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) ∧
      Δ * (Nf * (cfg.δ : ENNReal) ^ 2) ≤
        (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (r : ENNReal) ^ 2 ∧
      (tubeVolumeRatioConstant 3 : ENNReal) * ((r : ENNReal) ^ 2 * volT) ≤
        (cfg.δ : ENNReal) ^ 2 * volTa ∧
      (cfg.s.card : ENNReal) ≤ (cfg.C₀ : ENNReal) ^ 2 * (Na * Nf) := by
  classical
  obtain ⟨u⟩ := cfg.uniform
  obtain ⟨k, hk, hrρ, hρr⟩ := exists_gridIndex cfg hr hr1
  set ρ : NNReal := Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k with hρdef
  have hρ1 : ρ ≤ 1 := Tube.gridScale_le_one cfg.hδ1 (Tube.ssfGridLen cfg.δ) k
  have hδρ : cfg.δ ≤ ρ := le_trans (le_trans cfg.hdims.1 hr) hrρ
  have hr0 : 0 < r := lt_of_lt_of_le cfg.hδ (le_trans cfg.hdims.1 hr)
  have hρmem : ρ ∈ Set.Icc cfg.δ 1 := ⟨hδρ, hρ1⟩
  obtain ⟨G, hinner, hbody, houterSet, houterBody, hfull, hball⟩ :=
    exists_coarseShadedFamilyAtGrid cfg u hk hρdef.symm hρmem
  have hfull' : (cfg.δ : NNReal) ^ (3 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody :=
    rpow_three_eta_le_of_inducedFullness cfg hfull
  obtain ⟨volT, volTa, Δ, Na, Nf, hNa0, hNatop, hNftop, hSum, hmass, hΔ, hTa, hcount⟩ :=
    rScaleParentData_of_gridScale cfg hν hνη hνwe u.tubeUniform hk hρdef.symm hr hr1 hrρ hρr hρ1
      hrsmall G houterSet houterBody hfull'
  exact ⟨cfg.ι, G, volT, volTa, Δ, Na, Nf, hinner, hbody,
    coarseBallEstimate_of_gridScale cfg hνη hr0 hrρ hρr G hball,
    hNa0, hNatop, hNftop, hSum, hmass, hΔ, hTa, hcount⟩

end Kakeya.VeryNotSticky
