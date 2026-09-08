/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotSticky
public import Kakeya.DimensionThree.MainLemma2.AScaleInterface
public import Kakeya.DimensionThree.MainLemma2.AScaleSetup

/-!
# The goal-reduction layer of Main Lemma 2, very not sticky case

The leaves of the case analysis of Main Lemma 2 state their conclusions in three different
currencies: the multiplicity form `Kakeya.VeryNotSticky.goalMult` (blueprint `eqgoalmuT`), the
volume form `Kakeya.VeryNotSticky.goalUnion` (blueprint `eqgoalUT`), and the density form
`Kakeya.VeryNotSticky.goalDensity` (blueprint `eqgoaldens`). This file converts them into one
another:

* `Kakeya.VeryNotSticky.goalMult_of_goalUnion` and
  `Kakeya.VeryNotSticky.goalUnion_of_goalMult` are the two halves of blueprint
  `lem:ml2goalUTequiv`. Neither currency carries a comparison constant, so the equivalence is
  exact up to the loss `η` in the gain, which comes from `λ(T, Y) ≥ δ^η` alone.
* `Kakeya.VeryNotSticky.goalUnion_of_goalDensity` is blueprint `lem:ml2goalfromdens`. It
  consumes the two scale-`r` estimates of blueprint `lem:ml2aScaleData`, packaged as
  `Kakeya.VeryNotSticky.AScaleData`, and is otherwise exact bookkeeping.

Both the density currency and the cross-section interface carry a *variable radius* `r ≥ a`,
not the fixed scale `a`: the thick case produces its density estimate at `r = a` exactly,
while the transverse case produces it at `r = θ b ≥ δ^{-τ'} a`, and the requirement at radius
`a` carries the factor `(δ/a)^{2β}` that the transverse branch cannot make small. The
conversion is exact at every radius, since the two factors `r^{2β}` cancel.

`Kakeya.VeryNotSticky.AScaleData` is the *cross-section interface* of this layer: its two
estimates are blueprint `lowerBoundTTScaleAAndABall` (owned by Section 5, via
`ShadedBody.shadingMultiplicityEstimateForRhoTubes`) and blueprint `volumeOfTTa` (owned by
Section 3, via `Kakeya.KatzTaoEstimate.multiplicity_bound`). Its existence,
`Kakeya.VeryNotSticky.exists_aScaleData`, is proved here from the named interface statements
of `Kakeya.DimensionThree.MainLemma2.AScaleInterface`, which carry what those two sections owe;
see the docstring of that declaration.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

/-! ### Monotonicity in the gain -/

/-- The volume form of the goal is antitone in the gain (blueprint `lem:ml2goalAntitone`).
For `0 < δ ≤ 1` the map `s ↦ δ^s` is antitone, so a branch that supplies a larger gain
supplies the smaller one as well. This is the fact used whenever two branches of the case
split with different gains are combined. -/
theorem goalUnion_of_exponent_le (cfg : VeryNotSticky.{u}) {ν ν₁ : ℝ} (hν : ν ≤ ν₁)
    (h : cfg.goalUnion ν₁) : cfg.goalUnion ν := by
  have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  have hpow : (cfg.δ : ENNReal) ^ ν₁ ≤ (cfg.δ : ENNReal) ^ ν :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hν
  refine le_trans h ?_
  gcongr

/-! ### The volume and multiplicity currencies agree -/

/-- **Blueprint `lem:ml2goalUTequiv`(i)** (blueprint `lem:ml2goalMultOfUnion`).
The volume form with gain `ν` implies the multiplicity form with gain `ν`.

By `ShadedBody.multiplicity_mul_union`, `μ(T,Y) |U(T,Y)| = ∑_T |Y(T)|`, which equals
`λ(T,Y) ∑_T |T|` by `ShadedBody.sum_volumeReal_shade_eq_fullness_mul` and is at most
`∑_T |T|` because `λ(T,Y) ≤ 1` (`ShadedBody.fullness_le_one`). The volume form bounds that by
`δ^ν |U(T,Y)| |𝕋|^β`. Only `λ(T,Y) ≤ 1` is used, so no hypothesis on the configuration is
needed. -/
theorem goalMult_of_goalUnion (cfg : VeryNotSticky.{u}) {ν : ℝ} (h : cfg.goalUnion ν) :
    cfg.goalMult ν := by
  let V := fun i ↦ (cfg.T i).toShadedBody
  rw [goalMult, multiplicity_le_iff]
  calc
    ∑ i ∈ cfg.s, volume (V i).shade
        = (ShadedBody.fullness cfg.s V : ENNReal) * ∑ i ∈ cfg.s, volume (V i).carrier := by
      rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul cfg.s V]
    _ ≤ 1 * ∑ i ∈ cfg.s, volume (V i).carrier := by
      have hfull : (ShadedBody.fullness cfg.s V : ENNReal) ≤ (1 : ENNReal) :=
        ENNReal.coe_le_coe.mpr (ShadedBody.fullness_le_one cfg.s V)
      gcongr
    _ = ∑ i ∈ cfg.s, volume (V i).carrier := by simp
    _ ≤ (cfg.δ : ENNReal) ^ ν * volume (⋃ i ∈ cfg.s, (V i).shade) *
          (cfg.s.card : ENNReal) ^ cfg.β := h
    _ = ((cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β) *
          volume (⋃ i ∈ cfg.s, (V i).shade) := by ring

/-- **Blueprint `lem:ml2goalUTequiv`(ii)** (blueprint `lem:ml2goalUnionOfMult`).
The multiplicity form with gain `ν` implies the volume form with gain `ν - 2η`.

The chain is `δ^{2η} ∑_T |T| ≤ λ(T,Y) ∑_T |T| = ∑_T |Y(T)| = μ(T,Y) |U(T,Y)| ≤
δ^ν |𝕋|^β |U(T,Y)|`, using `cfg.fullness_ge`, `ShadedBody.sum_volumeReal_shade_eq_fullness_mul`
and `ShadedBody.multiplicity_mul_union`; dividing by `δ^{2η}`, which is positive and finite,
gives the volume form with gain `ν - 2η`. The loss `2η` is exactly the density lower bound of
(C1), and it is the only loss.

The loss reads `2η` and not `η` because `cfg.fullness_ge` is asserted at `δ^{2η}`: at `δ^η` it
was rigid against a flat family and therefore not deliverable — see that field's docstring and
`Kakeya.VeryNotSticky.not_rigidFullnessField_of_flat_island`. This declaration has no term-level
users, so the extra `η` is not spent anywhere; it is recorded here because the conversion
between the two currencies is exactly the fullness lower bound and nothing else. -/
theorem goalUnion_of_goalMult (cfg : VeryNotSticky.{u}) {ν : ℝ} (h : cfg.goalMult ν) :
    cfg.goalUnion (ν - (2 * cfg.η)) := by
  let V := fun i ↦ (cfg.T i).toShadedBody
  let d := (cfg.δ : ENNReal)
  let Nb := (cfg.s.card : ENNReal) ^ cfg.β
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr cfg.hδ.ne'
  have hdtop : d ≠ ⊤ := ENNReal.coe_ne_top
  -- relate δ^η (as ENNReal rpow) to λ = fullness (an NNReal)
  have hfull : d ^ (2 * cfg.η) ≤ (ShadedBody.fullness cfg.s V : ENNReal) := by
    calc
      d ^ (2 * cfg.η) = ((cfg.δ ^ (2 * cfg.η) : NNReal) : ENNReal) := by
        rw [ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne']
      _ ≤ (ShadedBody.fullness cfg.s V : ENNReal) :=
        ENNReal.coe_le_coe.mpr cfg.fullness_ge
  -- chain: δ^η * ∑|T| ≤ λ(T,Y) * ∑|T| = ∑|Y(T)| = μ(T,Y) * |U(T,Y)| ≤ δ^ν * |𝕋|^β * |U(T,Y)|
  have hkey : d ^ (2 * cfg.η) * ∑ i ∈ cfg.s, volume (V i).carrier ≤
      (d ^ ν * Nb) * volume (⋃ i ∈ cfg.s, (V i).shade) := by
    calc
      d ^ (2 * cfg.η) * ∑ i ∈ cfg.s, volume (V i).carrier
          ≤ (ShadedBody.fullness cfg.s V : ENNReal) * ∑ i ∈ cfg.s, volume (V i).carrier := by
        gcongr
      _ = ∑ i ∈ cfg.s, volume (V i).shade := by
        rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul cfg.s V]
      _ = ShadedBody.multiplicity cfg.s V * volume (⋃ i ∈ cfg.s, (V i).shade) := by
        rw [ShadedBody.multiplicity_mul_union cfg.s V]
      _ ≤ (d ^ ν * Nb) * volume (⋃ i ∈ cfg.s, (V i).shade) := by
        gcongr
        exact h
  -- δ^ν = δ^η * δ^(ν-η) via NNReal.rpow_add
  have hsplit : d ^ ν = d ^ (2 * cfg.η) * d ^ (ν - (2 * cfg.η)) := by
    calc
      d ^ ν = (cfg.δ : ENNReal) ^ ν := rfl
      _ = (cfg.δ : ENNReal) ^ ((2 * cfg.η) + (ν - (2 * cfg.η))) := by
        rw [show (2 * cfg.η) + (ν - (2 * cfg.η)) = ν by ring]
      _ = (cfg.δ : ENNReal) ^ (2 * cfg.η) * (cfg.δ : ENNReal) ^ (ν - (2 * cfg.η)) := by
        rw [← ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne']
        rw [NNReal.rpow_add cfg.hδ.ne' (2 * cfg.η) (ν - (2 * cfg.η))]
        simp [ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne']
      _ = d ^ (2 * cfg.η) * d ^ (ν - (2 * cfg.η)) := rfl
  have hdPow_zero : d ^ (2 * cfg.η) ≠ 0 := by
    intro hzero
    have hcases := ((ENNReal.rpow_eq_zero_iff (x := d) (y := (2 * cfg.η))).mp hzero)
    rcases hcases with (⟨hd0', hηpos⟩ | ⟨hdtop', hηneg⟩)
    · exact hd0 hd0'
    · exact hdtop hdtop'
  have hdPow_inf : d ^ (2 * cfg.η) ≠ ⊤ := by
    intro hinf
    have hcases := ((ENNReal.rpow_eq_top_iff (x := d) (y := (2 * cfg.η))).mp hinf)
    rcases hcases with (⟨hd0', hηneg⟩ | ⟨hdtop', hηpos⟩)
    · exact hd0 hd0'
    · exact hdtop hdtop'
  rw [goalUnion]
  have hrearrange : (d ^ ν * Nb) * volume (⋃ i ∈ cfg.s, (V i).shade) =
      d ^ (2 * cfg.η) * (d ^ (ν - (2 * cfg.η)) * volume (⋃ i ∈ cfg.s, (V i).shade) * Nb) := by
    calc
      (d ^ ν * Nb) * volume (⋃ i ∈ cfg.s, (V i).shade)
          = d ^ ν * volume (⋃ i ∈ cfg.s, (V i).shade) * Nb := by ring
      _ = (d ^ (2 * cfg.η) * d ^ (ν - (2 * cfg.η))) * volume (⋃ i ∈ cfg.s, (V i).shade) * Nb := by
        rw [hsplit]
      _ = d ^ (2 * cfg.η) *
            (d ^ (ν - (2 * cfg.η)) * volume (⋃ i ∈ cfg.s, (V i).shade) * Nb) := by ring
  have hkey' : d ^ (2 * cfg.η) * ∑ i ∈ cfg.s, volume (V i).carrier ≤
      d ^ (2 * cfg.η) * (d ^ (ν - (2 * cfg.η)) * volume (⋃ i ∈ cfg.s, (V i).shade) * Nb) := by
    calc
      d ^ (2 * cfg.η) * ∑ i ∈ cfg.s, volume (V i).carrier
          ≤ (d ^ ν * Nb) * volume (⋃ i ∈ cfg.s, (V i).shade) := hkey
      _ = d ^ (2 * cfg.η) *
            (d ^ (ν - (2 * cfg.η)) * volume (⋃ i ∈ cfg.s, (V i).shade) * Nb) := hrearrange
  have hcancel : ∑ i ∈ cfg.s, volume (V i).carrier ≤
      d ^ (ν - (2 * cfg.η)) * volume (⋃ i ∈ cfg.s, (V i).shade) * Nb := by
    have hcomm : (∑ i ∈ cfg.s, volume (V i).carrier) * (d ^ (2 * cfg.η)) ≤
        (d ^ (ν - (2 * cfg.η)) * volume (⋃ i ∈ cfg.s, (V i).shade) * Nb) * (d ^ (2 * cfg.η)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hkey'
    exact ((ENNReal.mul_le_mul_iff_left hdPow_zero hdPow_inf).mp hcomm)
  exact hcancel

/-! ### The scale-`a` interface -/

/-- **The two scale-`r` estimates** (blueprint `lem:ml2aScaleData`), as a predicate on the
configuration, the comparison constant `C`, the radius `r` and the gain `ν`.

`AScaleData cfg C r ν` asserts that there is a set `Ur` — the shaded union
`U(𝕋_r, Y_{𝕋_r})` of the family of `r`-tubes of Configuration `hyp:ml2setup` — such that

* (i) for every `r`-ball meeting `U(T, Y)`,
  `δ^{ν/9} |U(𝕋_r, Y_{𝕋_r})| |U(T,Y) ∩ B_r| ≤ C |U(T,Y)| |B_r|`;
  this is blueprint `lowerBoundTTScaleAAndABall`, and it comes from
  `ShadedBody.shadingMultiplicityEstimateForRhoTubes` applied to `(T, Y)` at the scale
  `ρ = r`, after re-centring the ball at a shaded point (blueprint
  `lem:ml2ballRecentre`);
* (ii) `δ^{ν/9} r^{2β} ∑_T |T| ≤ C |U(𝕋_r, Y_{𝕋_r})| δ^{2β} |𝕋|^β`;
  this is blueprint `volumeOfTTa`, and it comes from
  `Kakeya.KatzTaoEstimate.multiplicity_bound` applied to `(𝕋_r, Y_{𝕋_r})` together with the
  two-scale bound `Δ_max(𝕋_r) ≤ δ^{-η}(r/δ)²/|𝕋[T_r]|` (blueprint `lem:ml2DeltamaxScaleA`).

The radius is a parameter: the intended range is `cfg.a ≤ r`, at which the coarsening to
`r`-tubes is available, and the two estimates are always used at the radius at which the
consumer's density estimate `Kakeya.VeryNotSticky.goalDensity` was produced. Taking
`r = cfg.a` recovers the scale-`a` estimates of the blueprint verbatim, which is the form the
thick case uses.

Both are stated for the shading `Y` recorded by `cfg`, not for a further refinement of it.
This is the standing abuse of notation of the blueprint: the `≈ 1` refinement produced by
`ShadedBody.shadingMultiplicityEstimateForRhoTubes` at the scale `a` is taken *while*
Configuration `hyp:ml2setup` is being assembled (blueprint `lem:ml2setupexists` lists
`shadingMultiplicityEstimateForRhoTubes` among its inputs), so the pair recorded by `cfg` is
already the refined one.

Both estimates are written without division and without negative exponents, so that they are
statements about `[0, ∞]`-valued quantities requiring no finiteness side conditions. The
constant `C` is quantified *before* the ball in (i), which is what allows it to appear in the
hypothesis `Kakeya.VeryNotSticky.goalDensity` about a ball that is only chosen later. -/
def AScaleData (cfg : VeryNotSticky.{u}) (C : ENNReal) (r : NNReal) (ν : ℝ) : Prop :=
  ∃ Ur : Set (EuclideanSpace ℝ (Fin 3)),
    (∀ x : EuclideanSpace ℝ (Fin 3),
        ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball x (r : ℝ)).Nonempty →
        (cfg.δ : ENNReal) ^ (ν / 9) * volume Ur *
            volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball x (r : ℝ)) ≤
          C * volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) *
            volume (ball x (r : ℝ))) ∧
      (cfg.δ : ENNReal) ^ (ν / 9) * (r : ENNReal) ^ (2 * cfg.β) *
          ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
        C * volume Ur * (cfg.δ : ENNReal) ^ (2 * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β

/-- Both estimates of `Kakeya.VeryNotSticky.AScaleData` are monotone in the comparison
constant, the constant occurring only on the right of each. This is what lets the proof of
blueprint `lem:ml2aScaleData` produce its two clauses with the two different constants
`C_{lem:ml2aScaleBall}` and `C_{lem:ml2aScaleVolume}` and then take their maximum. -/
theorem AScaleData.mono (cfg : VeryNotSticky.{u}) {C C' : ENNReal} {r : NNReal} {ν : ℝ}
    (hCC' : C ≤ C') (h : cfg.AScaleData C r ν) : cfg.AScaleData C' r ν := by
  rcases h with ⟨Ur, h₁, h₂⟩
  refine ⟨Ur, ?_, ?_⟩
  · intro x hx
    exact le_trans (h₁ x hx) (by gcongr)
  · exact le_trans h₂ (by gcongr)

/-- **Estimate (i) of `Kakeya.VeryNotSticky.AScaleData` from the section-5 interface**
(blueprint `lem:ml2aScaleBall`, read at the scale `r`).

The hypothesis `hvol` is the ninth conclusion `boundVolumeAcrossTwoScales` of
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes` applied at `ρ = r`: it is asserted
for *every* admissible centre with the one constant `Cb`, which is the uniformity that
`Kakeya.aScaleBall` converts into an estimate at an arbitrary ball, by re-centring at a shaded
point (blueprint `lem:ml2ballRecentre`). The family `G` is the fully shaded factor family that
interface produces, and `hinner`, `hbody` say that its inner side is the pair `(𝕋, Y)` recorded
by `cfg` — the standing abuse of notation of the blueprint, under which the `≈ 1` refinement is
absorbed into Configuration `hyp:ml2setup` while that configuration is assembled.

Estimate (ii), `hcoarse`, is passed through: it is blueprint `lem:ml2aScaleVolume`, i.e.
`Kakeya.VeryNotSticky.aScaleVolume`, read at the coarse union `U(𝕋_r, Y_{𝕋_r})` of the same
family `G`, and this lemma does no work on it.

What is left between this bridge and `Kakeya.VeryNotSticky.exists_aScaleData` is exactly the
production of `G` and of `hcoarse`; see the docstring of that declaration. -/
theorem aScaleData_of_ballEstimate (cfg : VeryNotSticky.{u}) {κ : Type*}
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι κ)
    (hinner : G.innerSet = cfg.s)
    (hbody : ∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody)
    {Cb : NNReal} (hCb : 0 < Cb) {r : NNReal} (hr : 0 < (r : ℝ)) {ν : ℝ}
    (hvol : ∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
      (cfg.δ : ENNReal) ^ (ν / 9) *
          ((Cb : ENNReal)⁻¹ * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ)) /
              volume (ball x (r : ℝ)))) ≤
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
    {C : ENNReal} (hC : (aScaleBallConstant Cb : ENNReal) ≤ C)
    (hcoarse : (cfg.δ : ENNReal) ^ (ν / 9) * (r : ENNReal) ^ (2 * cfg.β) *
        ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
      C * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) * (cfg.δ : ENNReal) ^ (2 * cfg.β) *
        (cfg.s.card : ENNReal) ^ cfg.β) :
    cfg.AScaleData C r ν := by
  have hunion : (⋃ i ∈ G.innerSet, (G.innerBody i).shade) =
      ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade := by
    rw [hinner]
    apply Set.iUnion₂_congr
    intro i hi
    exact congrArg (fun b : ShadedBody (EuclideanSpace ℝ (Fin 3)) => b.shade) (hbody i hi)
  refine ⟨⋃ j ∈ G.outerSet, (G.outerBody j).shade, ?_, ?_⟩
  · intro x hne
    have hne' : ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ)).Nonempty := by
      simpa [← hunion] using hne
    have hball := Kakeya.aScaleBall G hCb hr hvol x hne'
    have hball' : (cfg.δ : ENNReal) ^ (ν / 9) * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
        volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball x (r : ℝ)) ≤
        (aScaleBallConstant Cb : ENNReal) * volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) *
          volume (ball x (r : ℝ)) := by
      simpa [hunion] using hball
    calc
      (cfg.δ : ENNReal) ^ (ν / 9) * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
          volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball x (r : ℝ))
          ≤ (aScaleBallConstant Cb : ENNReal) *
              volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) * volume (ball x (r : ℝ)) := hball'
      _ ≤ C * volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) * volume (ball x (r : ℝ)) := by
          gcongr
  · exact hcoarse

/-- **The absorption clause of blueprint `lem:ml2aScaleData`(iii)**, isolated from the
geometry.

A comparison constant bounded by the accumulated constant `C_⋆` that the threshold bundle
absorbs at the exponent `cfg.η` satisfies `C ^ 2 ≤ δ^{-η}`, provided `δ` lies below the
threshold at the gain `ν`. This is `Kakeya.VeryNotSticky.ScaleThresholds.aScale_absorb`
composed with the monotonicity of squaring, and it is the whole of what the hypothesis
`hthr` of `Kakeya.VeryNotSticky.exists_aScaleData` is for.

The hypothesis `hC` is the link that the threshold bundle cannot state on its own: neither
`Kakeya.aScaleBallConstant` nor `Kakeya.aScaleVolumeConstant` is nameable where
`Kakeya.VeryNotSticky.ScaleThresholds` is declared, and the second of them depends on the
uniformity constants `C₀, D₀` of the configuration, which the bundle does not see. See the
docstring of that structure. -/
theorem sq_le_rpow_neg_of_le_aScaleConst (cfg : VeryNotSticky.{u}) {thr : ScaleThresholds}
    {ν : ℝ} {C : ENNReal} (hthr : cfg.δ ≤ thr.aScale ν)
    (hC : C ≤ (thr.aScaleConst ν cfg.η : ENNReal)) :
    C ^ 2 ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  have habsorb : (thr.aScaleConst ν cfg.η : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-cfg.η) :=
    thr.aScale_absorb ν cfg.η cfg.hη cfg.δ cfg.hδ hthr
  exact le_trans (ENNReal.pow_le_pow_left hC) habsorb

/-- **Cross-section interface stub** (blueprint `lem:ml2aScaleData`).

Under Configuration `hyp:ml2setup`, for a radius `r ≥ a` and a gain `ν ≥ 90 η`, the two
scale-`r` estimates of `Kakeya.VeryNotSticky.AScaleData` hold with some finite comparison
constant `C ≥ 1`, and moreover `δ` lies below the fixed-scale threshold at which `C²` and a
prescribed finite factor `M` are absorbed by the power `δ^{-e}`, for any `e > 0`.

**The absorption, and why it is split.** It is the second obligation absorbed here, and it is
the one that makes the two producers of the density currency usable. Both of them have to
deliver `Kakeya.VeryNotSticky.goalDensity` at the *prescribed* constant `C²` — prescribed
because `Kakeya.VeryNotSticky.goalMult_of_goalDensity` demands exactly that value — while each
of them also carries a comparison constant `M` of its own, produced existentially by a
section-5 or section-6 interface (`Cbf` in the transverse case, `Θ`, `C₁` in the thick case).
Paying for both out of a surplus power of `δ` splits into two obligations of quite different
character, and they belong on different sides of the statement.

The producer's constant `M` is named by the consumer, hence *after* `δ` is fixed, so
"`δ` is small in terms of `M`" cannot be a conclusion here: for `M` large and `δ` already
fixed no threshold on `δ` can be met. An earlier version of this statement asserted
`C² * M ≤ δ^{-e}` outright for an arbitrary finite `M` and an arbitrary `e > 0`, and was for
that reason **refutable** rather than merely unproved. That half is now the hypothesis `hM'`,
`M ≤ δ^{-(e - η)}` (blueprint `aScaleAbsorbHyp`): exactly the "`δ` small in terms of the
constant being absorbed" threshold that the old clause was silently asserting, now stated
where it can be discharged, namely at the call site, by the branch that knows what `M` is.
The transverse case discharges it from the sub-polynomial bound on `Cbf` carried by
`Kakeya.VeryNotSticky.transverseBallFill` together with the budget
`Kakeya.VeryNotSticky.CaseParams.transverse`; the thick case invokes the statement at `M = 1`
and `e = cfg.η`, where it reads `1 ≤ δ^0`.

What remains is the conjunct `C ^ 2 ≤ δ^{-cfg.η}` (blueprint `aScaleAbsorbConcl`), a genuine
sub-polynomiality requirement on the constant *this* statement produces. Since `C` is chosen
here, this is the only place such a requirement can be stated; quantified over arbitrary `C`
in a hypothesis bundle such as `Kakeya.VeryNotSticky.CaseScale` it would be refutable and
would make that bundle — and with it every leaf consuming it — vacuous. Its exponent is the
*fixed* `cfg.η`, rendering blueprint `def:ml2aScaleDataExponent`, and **not** the consumer's
`e/2`: at the consumer's exponent the conjunct would inherit the very quantifier-order defect
just repaired for `M`, since `e` too is named after `δ`, and letting `e ↓ 0` would force
`C ≤ 1`. What it asks is the `δ`-independence of `C`, the open obligation blueprint
`def:ml2goalfromdensConstant` records, *together with* a threshold on `δ` — blueprint
`def:ml2aScaleDataThreshold`, the eighth clause of Configuration `hyp:ml2scale` — without
which it is false at `δ` near `1`. That threshold is the hypothesis `hthr`,
`cfg.δ ≤ thr.aScale ν`, and it is *not* among the hypotheses absorbed into this stub: it is
the one clause of Configuration `hyp:ml2scale` this statement uses, and it is stated at the
gain `ν` at which the statement is invoked, since blueprint `def:ml2aScaleDataThreshold`
makes the threshold a function of `ν` (and of `β, ζ, η, C₀, D₀`), all fixed before `δ`.
Consumers receive it threaded from blueprint `lem:ml2casesplit`, never arrange it: the
transverse case supplies it from
`Kakeya.VeryNotSticky.CaseScale.aScaleData_threshold` at the transverse gain, the thick case
from the corresponding binder of
`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_goalDensity` at the thick gain.

`Kakeya.VeryNotSticky.ScaleThresholds` now carries the defining property of blueprint
`def:ml2aScaleDataThreshold` for this field: below `thr.aScale ν` the accumulated constant
`thr.aScaleConst ν cfg.η` of the layer satisfies `C_⋆ ^ 2 ≤ δ^{-η}`. Spending `hthr` on it is
`Kakeya.VeryNotSticky.sq_le_rpow_neg_of_le_aScaleConst`, and that is the whole of the
absorption once a constant bounded by `C_⋆` is in hand.

One half of the absorption is not expressible where the bundle is declared: that the constants
this layer actually produces — `Kakeya.aScaleBallConstant`, read at the fixed constant of
`ShadedBody.shadingMultiplicityEstimateForRhoTubes`, and
`Kakeya.aScaleVolumeConstant cfg.C₀ cfg.D₀` — are absorbed too. Asserting it on the bundle
would need `aScale` to be a function of `C₀` and `D₀` as well as of `ν`, as blueprint
`def:ml2aScaleDataThreshold` writes it, since quantified over those constants it is false. It
is therefore carried by the configuration, as the field
`Kakeya.VeryNotSticky.aScaleData_absorb`, which absorbs
`Kakeya.aScaleDataConstant cfg.C₀ cfg.D₀`, the maximum of the two. The `δ → 1` refutation of
the conjunct is barred by that field, and arranging it is part of realising the
configuration.

Clause (iv) of blueprint `lem:ml2aScaleData`, `C ^ 2 * M ≤ δ^{-e}`, is *not* a conjunct of the
conclusion. It asserts nothing beyond the previous conjunct and the consumer's own threshold
on `M` — it is their product, by one `mul_le_mul'` and one `ENNReal.rpow_add`, the exponents
`cfg.η` and `e - cfg.η` summing to `e` — and carrying it here dragged five binders `e`, `he`,
`M`, `hM`, `hM'` into a signature that is otherwise one existential; `he` and `hM` were dead
even for that arithmetic. The recombination is `ENNReal.sq_mul_le_rpow_neg`, a standalone
`ℝ≥0∞` lemma with no Kakeya content, which each consumer applies to the conjunct
`C ^ 2 ≤ δ^{-η}` produced here and to its own bound on `M`.

**What this declaration assumes.** Its content is owned by other sections of the development,
not by the goal-reduction layer of Section 9:

* estimate (i) is blueprint `lowerBoundTTScaleAAndABall`, i.e. the conclusion
  `boundVolumeAcrossTwoScales` of `ShadedBody.shadingMultiplicityEstimateForRhoTubes`
  (Section 5, itself still unproved), applied at `ρ = r` and re-centred at a shaded point;
* estimate (ii) is blueprint `volumeOfTTa`, i.e. `Kakeya.KatzTaoEstimate.multiplicity_bound`
  (blueprint `genKKT`, Section 3, also still unproved) applied to the `r`-tube family,
  together with the two-scale multiplicity bound
  `Δ_max(𝕋_r) ≤ δ^{-η}(r/δ)²/|𝕋[T_r]|` of blueprint `lem:ml2DeltamaxScaleA`, which the
  blueprint records as an accepted stub of its own because it needs a two-scale counting
  statement the development does not yet contain.

Neither is assumed here in that raw form. What the proof below consumes are the two named
statements of `Kakeya.DimensionThree.MainLemma2.AScaleInterface`, each of which is the coarse-shading statement and a docstring saying which blueprint result owns it and why the existing
declaration cannot be applied as it stands. One obligation of blueprint `lem:ml2aScaleData`
that the Lean signature has no binder for is absorbed into those statements and recorded in
their docstrings: the scale thresholds `δ < δ_0(ν/90, β)` and `η ≤ η_{genKKT}(ν/90, β)`
demanded by blueprint `genKKT`, for which `Kakeya.VeryNotSticky` carries no field. The
blueprint's other extra hypothesis, the upper bound `r ≤ 1`, is *not* absorbed: it is the
binder `hr1` of this signature, and it may not be dropped, since without it the conjunction of
(i) and (ii) is refutable — see `Kakeya.VeryNotSticky.exists_aScaleData`. The
uniformity in the centre `x` of the constant hidden in the `⪆` of `boundVolumeAcrossTwoScales`
— one constant, valid for all admissible centres — is instead written out
explicitly, as the quantifier order of the ball conjunct of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` and of
`Kakeya.VeryNotSticky.coarseBallEstimate_of_gridScale`: without it the constant would depend on
the ball chosen by the density hypothesis and blueprint `lem:ml2goalfromdens` would be
circular.

Section 5's two-sided per-tube shading hypotheses are likewise not absorbed. They are not a
consequence of `cfg.fullness_ge`, which is a ratio of sums, so they are carried as the
configuration fields `Kakeya.VeryNotSticky.lam`, `Kakeya.VeryNotSticky.Cd`,
`Kakeya.VeryNotSticky.shading_lb` and `Kakeya.VeryNotSticky.shading_ub`, with
`Kakeya.VeryNotSticky.lam_ge` bridging the resulting outer-fullness conclusion back to the
`δ^{cfg.η}` this layer consumes.

Everything downstream of this declaration — `Kakeya.VeryNotSticky.goalUnion_of_goalDensity`
and `Kakeya.VeryNotSticky.goalMult_of_goalDensity` — is proved from `AScaleData` as an
explicit hypothesis and is independent of how it is obtained.

**How the proof runs.** Three of the four steps of the blueprint's proof are declarations of
their own:

* `Kakeya.VeryNotSticky.aScaleData_of_ballEstimate` turns the output of
  `ShadedBody.shadingMultiplicityEstimateForRhoTubes` at `ρ = r` into `AScaleData` at the
  constant `Kakeya.aScaleBallConstant`, passing estimate (ii) through;
* `Kakeya.VeryNotSticky.aScaleVolume` (blueprint `lem:ml2aScaleVolume`) is estimate (ii),
  proved outright from `Kakeya.VeryNotSticky.coarseVolumeLower` and the exponent budget
  `Kakeya.aScaleExponentBudget`, at inputs a parent family `𝕋_r` must supply;
* `Kakeya.VeryNotSticky.sq_le_rpow_neg_of_le_aScaleConst` is the conjunct `C ^ 2 ≤ δ^{-η}`,
  and `Kakeya.VeryNotSticky.AScaleData.mono` is the monotonicity that lets the two constants
  be replaced by their maximum.

What the two families cost is what the interface file carries, and it is a single call.
`Kakeya.VeryNotSticky.exists_aScaleInputs` produces one coarse shaded factor family carrying
both estimate (i) at the nominal radius and the five quantities of estimate (ii); its own two
residues are `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`, owned by Section 5, and
`Kakeya.VeryNotSticky.coarseKatzTaoBound`, owned by Section 3. Both are stated at a *grid*
scale of the hierarchy `cfg.uniform` and at the configuration's own overlap constant `cfg.C₀`,
and both are upstream of this layer, which is why they are assumed whole rather than derived.

**The general radius is not an obstruction, and the earlier claim that it was is withdrawn.**
That claim — that a `Tube.UniformTubeSet` parent family is unavailable at a radius `r`
which the hypothesis `cfg.a ≤ r` does not make a grid scale, "the constraint the third remark
of blueprint `lem:ml2aScaleData` calls genuine and not a formality" — is false. The grid of GWZ
Definition 2.1 has length `M = ⌈log log 1/δ⌉`, so its spacing `δ^{-1/M}` is `δ^{-o(1)}`, and
rounding `r` *up* to the nearest grid scale `ρ` therefore satisfies the two-scale multiplicity
bound and the tube-volume comparison simultaneously at a cost that is nothing on the polynomial
scale. The two were believed to pull against each other, one wanting a parent radius `≤ r` and
the other `≥ r`; read at the same rounded `ρ` the comparison is monotone in the parent radius
and costs nothing (`Kakeya.tubeVolumeRatio_of_le`), while only the multiplicity bound pays, and
it pays `(ρ/r)² ≤ δ^{-2η}` out of the gain. The rounding is
`Kakeya.VeryNotSticky.exists_gridIndex`, the sub-polynomiality of one step is the configuration
field `Kakeya.VeryNotSticky.gridFine`, and the accounting is the module docstring of
`Kakeya.DimensionThree.MainLemma2.AScaleRounding`. GWZ perform the same rounding by hand at
p. 41, at the strictly greater cost `δ^{3η}`.

The two further assumptions this proof used to make are gone. The normalisation `β ≤ 1` is
the field `cfg.hβ1` of Configuration `hyp:ml2setup`. The constant-domination link is no longer
needed at all: the two statements above produce their estimates at
`Kakeya.aScaleBallConstant` read at the fixed section-5 constant and at
`Kakeya.aScaleVolumeConstant cfg.C₀ cfg.D₀`, and `Kakeya.aScaleDataConstant cfg.C₀ cfg.D₀` is
by definition their maximum, so the domination is `le_max_left` and `le_max_right`. What used
to be assumed about it is the field `cfg.aScaleData_absorb`, the eighth clause of
Configuration `hyp:ml2scale`, which is stated at the configuration's own uniformity constants
because `Kakeya.VeryNotSticky.ScaleThresholds` cannot see them; see the docstring of that
field. The constant produced here is the maximum of that constant with the one the threshold
bundle absorbs, so both thresholds are spent and the conjunct `C ^ 2 ≤ δ^{-η}` follows from
the two absorptions together. -/
theorem exists_aScaleData_of_le_one (cfg : VeryNotSticky.{u}) {r : NNReal} (hr : cfg.a ≤ r)
    (hr1 : r ≤ 1) (hrsmall : r ≤ 6 * cfg.δ ^ cfg.exscal) {ν : ℝ} (hν : 0 < ν)
    (hνη : 90 * cfg.η ≤ ν) (hνwe : cfg.ckt.we ≤ ν / 180)
    {thr : ScaleThresholds} (hthr : cfg.δ ≤ thr.aScale ν) :
    ∃ C : ENNReal, 1 ≤ C ∧ C ≠ ⊤ ∧ cfg.AScaleData C r ν ∧
      C ^ 2 ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  obtain ⟨κ, G, volT, volTa, Δ, Na, Nf, hinner, hbody, hvol, hNa0, hNaTop, hNfTop, hSum,
      hmass, hΔ, hTa, hcount⟩ := cfg.exists_aScaleInputs hr hr1 hrsmall hν hνη hνwe
  let Cst : NNReal := max (thr.aScaleConst ν cfg.η) (aScaleDataConstant cfg.C₀ cfg.D₀)
  let C : ENNReal := (Cst : ENNReal)
  have hCb : 0 < _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 :=
    lt_of_lt_of_le zero_lt_one (_root_.ShadedBody.one_le_rhoTubesInducedFullnessLoss 3)
  have hC1 : 1 ≤ C := by
    dsimp [C, Cst]
    exact ENNReal.coe_le_coe.mpr (le_max_of_le_left (thr.one_le_aScaleConst ν cfg.η))
  have hCtop : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.coe_ne_top
  have hBallC :
      (aScaleBallConstant (_root_.ShadedBody.rhoTubesInducedFullnessLoss 3) : ENNReal) ≤ C := by
    dsimp [C, Cst]
    exact ENNReal.coe_le_coe.mpr
      (le_trans (aScaleBallConstant_le_aScaleDataConstant cfg.C₀ cfg.D₀) (le_max_right _ _))
  have hVolC : (aScaleVolumeConstant cfg.C₀ cfg.D₀ : ENNReal) ≤ C := by
    dsimp [C, Cst]
    exact ENNReal.coe_le_coe.mpr
      (le_trans (aScaleVolumeConstant_le_aScaleDataConstant cfg.C₀ cfg.D₀) (le_max_right _ _))
  -- side conditions for aScaleVolume
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by
    exact_mod_cast cfg.hδ.ne.symm
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  have hδa : (cfg.δ : ℝ) ≤ (cfg.a : ℝ) := by exact_mod_cast cfg.hdims.1
  have har : (cfg.a : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast cfg.hδ) (le_trans hδa har)
  have hNNpos : 0 < r := by exact_mod_cast hrpos
  have hA0 : (r : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hNNpos)
  have hAtop : (r : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hNs0 : (cfg.s.card : ENNReal) ≠ 0 := by
    intro hzero
    have hpos : (0 : ENNReal) < (cfg.δ : ENNReal) * (cfg.s.card : ENNReal) :=
      lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) cfg.tube_count
    have hz : (cfg.δ : ENNReal) * (cfg.s.card : ENNReal) = (0 : ENNReal) := by
      rw [hzero]
      simp
    exact (ne_of_gt hpos) hz
  have hNstop : (cfg.s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top cfg.s.card
  have hcoarse :
      (cfg.δ : ENNReal) ^ (ν / 9) * (r : ENNReal) ^ (2 * cfg.β) *
          ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
        C * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
          (cfg.δ : ENNReal) ^ (2 * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β := by
    calc
      (cfg.δ : ENNReal) ^ (ν / 9) * (r : ENNReal) ^ (2 * cfg.β) *
          ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier
          ≤ (aScaleVolumeConstant cfg.C₀ cfg.D₀ : ENNReal) *
              volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (cfg.δ : ENNReal) ^ (2 * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β := by
            -- the honest coarse fullness lands at `δ^{3η}`, one `η` weaker than the
            -- placeholder afforded; `Kakeya.VeryNotSticky.coarseLossExponentHeadroom` is the
            -- measurement that the layer's budget has room for that and five more.
            have hmass' : (cfg.δ : ENNReal) ^ (2 * (3 * cfg.η / 2)) * (Na * volTa) ≤
                (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * Na ^ cfg.β *
                  volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) := by
              rw [show (2 : ℝ) * (3 * cfg.η / 2) = 3 * cfg.η by ring]
              exact hmass
            have hbud : (cfg.δ : ENNReal) ^ (ν / 9)
                ≤ (cfg.δ : ENNReal) ^ (2 * (3 * cfg.η / 2) + ν / 90) := by
              refine ENNReal.rpow_le_rpow_of_exponent_ge hδ1 ?_
              have h1 : cfg.η ≤ ν / 90 := by linarith
              have h2 : (0 : ℝ) ≤ ν := by linarith [cfg.hη]
              nlinarith
            exact aScaleVolume (cfg := cfg) (hβ1 := cfg.hβ1) (hνη := hνη)
              (hC₀ := cfg.hC₀) (hD₀ := cfg.hD₀) (hd0 := hδ0) (hdtop := hδtop) (hd1 := hδ1)
              (hA0 := hA0) (hAtop := hAtop) (hNa0 := hNa0) (hNatop := hNaTop)
              (hNftop := hNfTop) (hNs0 := hNs0) (hNstop := hNstop) (hS := hSum)
              (ηc := 3 * cfg.η / 2) (hηc := by linarith [cfg.hη]) (hbud := hbud)
              (hmass := hmass') (hΔ := hΔ) (hTa := hTa) (hcount := hcount)
      _ ≤ C * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (cfg.δ : ENNReal) ^ (2 * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β := by
          gcongr
  have hdata : cfg.AScaleData C r ν := by
    exact aScaleData_of_ballEstimate cfg G hinner hbody hCb hrpos hvol
      (hC := hBallC) (hcoarse := hcoarse)
  refine ⟨C, hC1, hCtop, hdata, ?_⟩
  rcases max_choice (thr.aScaleConst ν cfg.η) (aScaleDataConstant cfg.C₀ cfg.D₀) with h | h
  · exact sq_le_rpow_neg_of_le_aScaleConst cfg hthr (hC := by
      dsimp [C, Cst]
      exact ENNReal.coe_le_coe.mpr (le_of_eq h))
  · have hCeq : C = (aScaleDataConstant cfg.C₀ cfg.D₀ : ENNReal) := by
      dsimp [C, Cst]
      exact congrArg (fun h : NNReal => (h : ENNReal)) h
    rw [hCeq]
    exact cfg.aScaleData_absorb

/-- **Cross-section interface** (blueprint `lem:ml2aScaleData`), at every radius `a ≤ r ≤ 1`.

This is `Kakeya.VeryNotSticky.exists_aScaleData_of_le_one` under its own name, kept as the
declaration the two branches call so that a future change to the producing layer touches one
signature. Both hypotheses on the radius are those of blueprint `lem:ml2aScaleData`, and the
upper one is not decoration:

* all tubes of Configuration `hyp:ml2setup` lie in the unit ball
  (`Kakeya.VeryNotSticky.contained`), so `|U(𝕋, Y)|` and `|U(𝕋_r, Y_{𝕋_r})|` are bounded, while
  the left-hand side of estimate (ii) carries `r^{2β}`, which is not. Letting `r → ∞` with
  everything else fixed refutes the conjunction of (i) and (ii): (i) caps `|U(𝕋_r, Y_{𝕋_r})|`
  from above, by `C δ^{-ν/9} |U(𝕋,Y)| / Δ`, uniformly in `r ≥ 1`, and (ii) forces it to grow
  like `r^{2β}`. * The hypothesis cannot be absorbed into the producers either; it has to appear in this
  signature.

Both call sites discharge it. The thick branch,
`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_goalDensity` in `ThickCase`, invokes the interface at
`r = cfg.a`, and `cfg.a ≤ cfg.b ≤ cfg.δ ^ cfg.exscal ≤ 1` by `cfg.hdims`, `cfg.hδ1` and
`cfg.hexscal` — this is `Kakeya.VeryNotSticky.cfg_a_le_one`. The transverse branch,
`Kakeya.VeryNotSticky.goalMult_of_theta_ge_explicit` in `TransverseCase`, invokes it at the
radius produced by `Kakeya.VeryNotSticky.transverseBallFill`, which now asserts `r ≤ 1`
alongside `θ b ≤ r`; that bound is
`Kakeya.VeryNotSticky.transverseFillRadius_le_one`, and it is where the fixed-scale threshold
`Kakeya.VeryNotSticky.CaseScale.transverse_fill` is spent a second time.

Everything else this declaration used to assume is now proved. In particular the objection that
the parent family `𝕋_r` at a general radius is unavailable because `r` is not a grid scale is
withdrawn: see the module docstring of
`Kakeya.DimensionThree.MainLemma2.AScaleInterface`. -/
theorem exists_aScaleData (cfg : VeryNotSticky.{u}) {r : NNReal} (hr : cfg.a ≤ r)
    (hr1 : r ≤ 1) (hrsmall : r ≤ 6 * cfg.δ ^ cfg.exscal) {ν : ℝ}
    (hν : 0 < ν) (hνη : 90 * cfg.η ≤ ν) (hνwe : cfg.ckt.we ≤ ν / 180)
    {thr : ScaleThresholds} (hthr : cfg.δ ≤ thr.aScale ν) :
    ∃ C : ENNReal, 1 ≤ C ∧ C ≠ ⊤ ∧ cfg.AScaleData C r ν ∧
      C ^ 2 ≤ (cfg.δ : ENNReal) ^ (-cfg.η) :=
  exists_aScaleData_of_le_one cfg hr hr1 hrsmall hν hνη hνwe hthr

/-! ### From the density estimate to the volume goal -/

/-- The `ENNReal` bookkeeping behind `Kakeya.VeryNotSticky.goalUnion_of_goalDensity`, isolated
from the geometry.

Read `e = δ^{ν/9}`, `P = δ^{2β}`, `Q = a^{2β}`, `M = δ^{2ν}`, `S = ∑_T |T|`, `Nb = |𝕋|^β`,
`V = |U(T,Y)|`, `W = |U(𝕋_a, Y_{𝕋_a})|`, `Ba = |B_a|` and `D = |U(T,Y) ∩ B_a|`; then `hvol`
is estimate (ii) of `Kakeya.VeryNotSticky.AScaleData`, `hball` is its estimate (i) at the
ball supplied by `hdens`, and `hdens` is `Kakeya.VeryNotSticky.goalDensity` at constant `C^2`.
The three powers of `C`, and the pair `P`, `Q`, all cancel; only the product
`C^2 * P * Ba` has to be nonzero and finite.

`Kakeya.VeryNotSticky.goalUnion_of_goalDensity` carries out the same computation inline,
interleaved with the rpow side conditions, so this lemma is not on its critical path; it is
kept as the standalone record of which cancellations the reduction actually performs, and it
is the form a future refactor of that proof should route through. -/
theorem mul_self_mul_le_of_aScaleChain {C e P Q S Nb V W Ba D M : ENNReal}
    (hK : C ^ 2 * P * Ba ≠ 0) (hK' : C ^ 2 * P * Ba ≠ ⊤)
    (hvol : e * Q * S ≤ C * W * P * Nb)
    (hdens : C ^ 2 * P * Ba ≤ M * D * Q)
    (hball : e * W * D ≤ C * V * Ba) :
    e * e * S ≤ M * Nb * V := by
  -- Step 1: e * e * (Q * S * D) ≤ C ^ 2 * P * Nb * V * Ba
  have step1 : e * e * (Q * S * D) ≤ C ^ 2 * P * Nb * V * Ba := by
    calc
      e * e * (Q * S * D) = (e * Q * S) * (e * D) := by ring
      _ ≤ (C * W * P * Nb) * (e * D) := mul_le_mul hvol (le_refl _) (by positivity) (by positivity)
      _ = (C * P * Nb) * (e * W * D) := by ring
      _ ≤ (C * P * Nb) * (C * V * Ba) :=
        mul_le_mul (le_refl _) hball (by positivity) (by positivity)
      _ = C ^ 2 * P * Nb * V * Ba := by ring
  -- Step 2: (C ^ 2 * P * Ba) * (e * e * S) ≤ (C ^ 2 * P * Ba) * (M * Nb * V)
  have step2 : (C ^ 2 * P * Ba) * (e * e * S) ≤ (C ^ 2 * P * Ba) * (M * Nb * V) := by
    calc
      (C ^ 2 * P * Ba) * (e * e * S) ≤ (M * D * Q) * (e * e * S) :=
        mul_le_mul hdens (le_refl _) (by positivity) (by positivity)
      _ = M * (e * e * (Q * S * D)) := by ring
      _ ≤ M * (C ^ 2 * P * Nb * V * Ba) :=
        mul_le_mul (le_refl _) step1 (by positivity) (by positivity)
      _ = (C ^ 2 * P * Ba) * (M * Nb * V) := by ring
  -- Step 3: Cancel the common factor C ^ 2 * P * Ba
  exact ((ENNReal.mul_le_mul_iff_right hK hK').mp step2)

/-- **Blueprint `lem:ml2goalfromdens`.**
Given the two scale-`r` estimates with comparison constant `C` (blueprint
`lem:ml2aScaleData`, here the hypothesis `hdata`) and the density form of the goal with
constant `C^2` and gain `ν` *at the same radius* `r ≥ a`, the volume form of the goal holds
with gain `ν`. The radius is otherwise unconstrained: it enters only through the two factors
`r^{2β}` that cancel, and through the positivity of `|B_r|`, which `cfg.a ≤ r` supplies.

The computation is exact bookkeeping. Writing `V = |U(T,Y)|`, `W = |U(𝕋_a, Y_{𝕋_a})|`,
`D = |U(T,Y) ∩ B_a|`, `S = ∑_T |T|` and `N = |𝕋|`, multiplying estimate (ii) by the density
hypothesis cancels `a^{2β}` and `δ^{2β}` and leaves
`C² |B_a| δ^{ν/9} S ≤ C N^β δ^{2ν} (W D)`; feeding in estimate (i), which applies because the
density hypothesis forces `D > 0`, and cancelling `C²` and `|B_a|` leaves
`δ^{2ν/9} S ≤ δ^{2ν} V N^β`, that is the volume form with gain `16ν/9`. Since `0 < δ ≤ 1` and
`16ν/9 ≥ ν`, `Kakeya.VeryNotSticky.goalUnion_of_exponent_le` gives it with gain `ν`.

The three powers of `C` cancel exactly, which is the point of demanding `C^2` in the density
hypothesis, and so do the two factors `(r/δ)^{2β}` and `(δ/r)^{2β}` implicit in the two
estimates. -/
theorem goalUnion_of_goalDensity (cfg : VeryNotSticky.{u}) {C : ENNReal} {r : NNReal} {ν : ℝ}
    (hν : 0 ≤ ν) (hr : cfg.a ≤ r)
    (hC : 1 ≤ C) (hC' : C ≠ ⊤) (hdata : cfg.AScaleData C r ν)
    (hdens : cfg.goalDensity (C ^ 2) r ν) : cfg.goalUnion ν := by
  -- Notation
  let d : ENNReal := (cfg.δ : ENNReal)
  let A : ENNReal := (r : ENNReal)
  let β := cfg.β
  let U := ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade
  let S := ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier
  let N : ENNReal := (cfg.s.card : ENNReal)
  let V := volume U
  rcases hdata with ⟨Ua, ⟨hdata_i, hdata_ii⟩⟩
  let W := volume Ua
  rcases hdens with ⟨x, hdens⟩
  let Ba := volume (Metric.ball x (r : ℝ))
  let D := volume (U ∩ Metric.ball x (r : ℝ))
  -- hdens: C ^ 2 * d ^ (2 * β) * Ba ≤ d ^ (2 * ν) * D * A ^ (2 * β)
  -- hdata_ii: d ^ (ν / 9) * A ^ (2 * β) * S ≤ C * W * d ^ (2 * β) * N ^ β
  -- hdata_i: ∀ x, (U ∩ ball x a).Nonempty → d ^ (ν / 9) * W * D' ≤ C * V * Ba'
  -- Goal: S ≤ d ^ ν * V * N ^ β
  -- 1. Basic positivity/finiteness facts
  have hδ_ne_zero : d ≠ 0 := by
    simpa [d] using (by exact_mod_cast cfg.hδ.ne.symm : (cfg.δ : ENNReal) ≠ 0)
  have hδ_ne_top : d ≠ ⊤ := ENNReal.coe_ne_top
  have hapos : 0 < (r : ℝ) := by
    have hδa : (cfg.δ : ℝ) ≤ (cfg.a : ℝ) := by exact_mod_cast cfg.hdims.1
    have har : (cfg.a : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    exact lt_of_lt_of_le cfg.hδ (le_trans hδa har)
  have ha_ne_zero : A ≠ 0 := by
    simpa [A] using (by exact_mod_cast hapos.ne.symm : (r : ENNReal) ≠ 0)
  have ha_ne_top : A ≠ ⊤ := ENNReal.coe_ne_top
  have hBa_pos : 0 < Ba := Metric.measure_ball_pos volume x hapos
  have hBa_ne_zero : Ba ≠ 0 := hBa_pos.ne.symm
  have hBa_ne_top : Ba ≠ ⊤ := by
    have hlt : Ba < ⊤ := MeasureTheory.measure_ball_lt_top (x := x) (r := (r : ℝ))
    exact hlt.ne
  have hCpos : 0 < C := by
    have h0pos : (0 : ENNReal) < 1 := by norm_num
    exact lt_of_lt_of_le h0pos hC
  have hC_ne_zero : C ≠ 0 := hCpos.ne.symm
  have hC2_ne_zero : C ^ 2 ≠ 0 := pow_ne_zero 2 hC_ne_zero
  have hC2_ne_top : C ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (a := C) (ha := hC') (n := 2)
  have hC2pos : 0 < C ^ 2 := by positivity
  -- Helper: if d ≠ 0 and d ≠ ⊤, then d^r ≠ 0
  have hrpow_ne_zero (r : ℝ) : d ^ r ≠ 0 := by
    intro hzero
    have h := (ENNReal.rpow_eq_zero_iff.mp hzero)
    rcases h with (⟨hd0, _⟩ | ⟨hdt, _⟩)
    · exact hδ_ne_zero hd0
    · exact hδ_ne_top hdt
  have hdpos : 0 < d := by
    have hδpos : 0 < (cfg.δ : ℝ) := cfg.hδ
    have : 0 < (cfg.δ : ENNReal) := by exact_mod_cast hδpos
    simpa [d]
  have hd2β_ne_zero : d ^ (2 * β) ≠ 0 := hrpow_ne_zero (2 * β)
  have hd2β_ne_top : d ^ (2 * β) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ_ne_zero hδ_ne_top
  have hA2β_ne_zero : A ^ (2 * β) ≠ 0 := by
    intro hzero
    have h := (ENNReal.rpow_eq_zero_iff.mp hzero)
    rcases h with (⟨hA0, _⟩ | ⟨hAt, _⟩)
    · exact ha_ne_zero hA0
    · exact ha_ne_top hAt
  have hA2β_ne_top : A ^ (2 * β) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero ha_ne_zero ha_ne_top
  have hdν9_ne_zero : d ^ (ν / 9) ≠ 0 := hrpow_ne_zero (ν / 9)
  have hdν9_ne_top : d ^ (ν / 9) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ_ne_zero hδ_ne_top
  have hd2ν_ne_zero : d ^ (2 * ν) ≠ 0 := hrpow_ne_zero (2 * ν)
  have hd2ν_ne_top : d ^ (2 * ν) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ_ne_zero hδ_ne_top
  have hd2ν9_ne_zero : d ^ (2 * ν / 9) ≠ 0 := hrpow_ne_zero (2 * ν / 9)
  have hd2ν9_ne_top : d ^ (2 * ν / 9) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ_ne_zero hδ_ne_top
  -- 2. D ≠ 0, thus (U ∩ ball x a).Nonempty
  have hD_ne_zero : D ≠ 0 := by
    intro hDzero
    have hzero : C ^ 2 * d ^ (2 * β) * Ba ≤ 0 := by
      calc
        C ^ 2 * d ^ (2 * β) * Ba ≤ d ^ (2 * ν) * D * A ^ (2 * β) := hdens
        _ = d ^ (2 * ν) * 0 * A ^ (2 * β) := by rw [hDzero]
        _ = 0 := by simp
    have h2β_nonneg : 0 ≤ 2 * β := by nlinarith [cfg.hβ]
    have hpos : 0 < C ^ 2 * d ^ (2 * β) * Ba := by
      have htemp' : 0 < d ^ (2 * β) := ENNReal.rpow_pos_of_nonneg hdpos h2β_nonneg
      positivity
    have : ¬ C ^ 2 * d ^ (2 * β) * Ba ≤ 0 := not_le.mpr hpos
    exact this hzero
  have h_nonempty : (U ∩ Metric.ball x (r : ℝ)).Nonempty := by
    by_contra! h_empty
    have : D = 0 := by
      have h_empty_set : (U ∩ Metric.ball x (r : ℝ)) = ∅ := h_empty
      simp [h_empty_set, D]
    exact hD_ne_zero this
  -- 3. Multiply hdata_ii by hdens, cancel A^(2*β) and d^(2*β)
  have htemp : d ^ (ν / 9) * S * C ^ 2 * Ba ≤ C * N ^ β * d ^ (2 * ν) * (W * D) := by
    let F := A ^ (2 * β) * d ^ (2 * β)
    have hF0 : F ≠ 0 := mul_ne_zero hA2β_ne_zero hd2β_ne_zero
    have hFtop : F ≠ ⊤ := ENNReal.mul_ne_top hA2β_ne_top hd2β_ne_top
    have hprod : F * (d ^ (ν / 9) * S * C ^ 2 * Ba) ≤ F * (C * N ^ β * d ^ (2 * ν) * (W * D)) := by
      calc
        F * (d ^ (ν / 9) * S * C ^ 2 * Ba)
            = (d ^ (ν / 9) * A ^ (2 * β) * S) * (C ^ 2 * d ^ (2 * β) * Ba) := by
          dsimp [F]
          ring_nf
        _ ≤ (C * W * d ^ (2 * β) * N ^ β) * (d ^ (2 * ν) * D * A ^ (2 * β)) :=
          mul_le_mul hdata_ii hdens (by positivity : (0 : ENNReal) ≤ _)
            (by positivity : (0 : ENNReal) ≤ _)
        _ = F * (C * N ^ β * d ^ (2 * ν) * (W * D)) := by
          dsimp [F]
          ring_nf
    have hcancel := (ENNReal.mul_le_mul_iff_right hF0 hFtop).mp hprod
    exact hcancel
  -- 4. Use hdata_i at x, multiply htemp by d^(ν/9), and replace W*D by C*V*Ba
  have htemp2 : d ^ (ν / 9) * (d ^ (ν / 9) * S * C ^ 2 * Ba) ≤
      C ^ 2 * N ^ β * d ^ (2 * ν) * V * Ba := by
    have hAi : d ^ (ν / 9) * W * D ≤ C * V * Ba :=
      hdata_i x h_nonempty
    have htemp_mul : d ^ (ν / 9) * (d ^ (ν / 9) * S * C ^ 2 * Ba) ≤
                    d ^ (ν / 9) * (C * N ^ β * d ^ (2 * ν) * (W * D)) :=
      mul_le_mul (le_refl (d ^ (ν / 9))) htemp (by positivity : (0 : ENNReal) ≤ _)
        (by positivity : (0 : ENNReal) ≤ _)
    have hRHS : d ^ (ν / 9) * (C * N ^ β * d ^ (2 * ν) * (W * D)) ≤
               C ^ 2 * N ^ β * d ^ (2 * ν) * V * Ba := by
      calc
        d ^ (ν / 9) * (C * N ^ β * d ^ (2 * ν) * (W * D))
            = C * N ^ β * d ^ (2 * ν) * (d ^ (ν / 9) * W * D) := by
          ring_nf
        _ ≤ C * N ^ β * d ^ (2 * ν) * (C * V * Ba) :=
          mul_le_mul (le_refl (C * N ^ β * d ^ (2 * ν))) hAi
            (by positivity : (0 : ENNReal) ≤ _) (by positivity : (0 : ENNReal) ≤ _)
        _ = (C * C) * N ^ β * d ^ (2 * ν) * V * Ba := by
          ring_nf
        _ = C ^ 2 * N ^ β * d ^ (2 * ν) * V * Ba := by
          simp [pow_two]
    exact le_trans htemp_mul hRHS
  -- 5. On the LHS, d^(ν/9) * (d^(ν/9) * S * C^2 * Ba) = d^(2*ν/9) * S * C^2 * Ba
  have hLHS_eq : d ^ (ν / 9) * (d ^ (ν / 9) * S * C ^ 2 * Ba) =
      d ^ (2 * ν / 9) * S * C ^ 2 * Ba := by
    calc
      d ^ (ν / 9) * (d ^ (ν / 9) * S * C ^ 2 * Ba)
          = (d ^ (ν / 9) * d ^ (ν / 9)) * (S * C ^ 2 * Ba) := by ring
      _ = d ^ (ν / 9 + ν / 9) * (S * C ^ 2 * Ba) := by
        rw [ENNReal.rpow_add (ν / 9) (ν / 9) hδ_ne_zero hδ_ne_top]
      _ = d ^ (2 * ν / 9) * (S * C ^ 2 * Ba) := by ring_nf
      _ = d ^ (2 * ν / 9) * S * C ^ 2 * Ba := by ring
  have htemp2' : d ^ (2 * ν / 9) * S * C ^ 2 * Ba ≤ C ^ 2 * N ^ β * d ^ (2 * ν) * V * Ba := by
    simpa [hLHS_eq] using htemp2
  -- 6. Cancel C^2 (nonzero, finite) and Ba (nonzero, finite)
  have hC2_factor : d ^ (2 * ν / 9) * S * Ba ≤ N ^ β * d ^ (2 * ν) * V * Ba := by
    have htemp_c2 : C ^ 2 * (d ^ (2 * ν / 9) * S * Ba) ≤
        C ^ 2 * (N ^ β * d ^ (2 * ν) * V * Ba) := by
      calc
        C ^ 2 * (d ^ (2 * ν / 9) * S * Ba) = d ^ (2 * ν / 9) * S * C ^ 2 * Ba := by ring
        _ ≤ C ^ 2 * N ^ β * d ^ (2 * ν) * V * Ba := htemp2'
        _ = C ^ 2 * (N ^ β * d ^ (2 * ν) * V * Ba) := by ring
    exact ((ENNReal.mul_le_mul_iff_right hC2_ne_zero hC2_ne_top).mp htemp_c2)
  have hresh : d ^ (2 * ν / 9) * S ≤ d ^ (2 * ν) * V * N ^ β := by
    have htemp_ba : Ba * (d ^ (2 * ν / 9) * S) ≤ Ba * (d ^ (2 * ν) * V * N ^ β) := by
      calc
        Ba * (d ^ (2 * ν / 9) * S) = d ^ (2 * ν / 9) * S * Ba := by ring
        _ ≤ N ^ β * d ^ (2 * ν) * V * Ba := hC2_factor
        _ = Ba * (d ^ (2 * ν) * V * N ^ β) := by ring
    exact ((ENNReal.mul_le_mul_iff_right hBa_ne_zero hBa_ne_top).mp htemp_ba)
  -- 7. Rewrite d^(2*ν) as d^(2*ν/9) * d^(2*ν - 2*ν/9) = d^(2*ν/9) * d^(16*ν/9)
  have h_rpow_add : d ^ (2 * ν) = d ^ (2 * ν / 9) * d ^ (2 * ν - 2 * ν / 9) := by
    calc
      d ^ (2 * ν) = d ^ ((2 * ν / 9) + (2 * ν - 2 * ν / 9)) := by ring_nf
      _ = d ^ (2 * ν / 9) * d ^ (2 * ν - 2 * ν / 9) :=
        ENNReal.rpow_add (2 * ν / 9) (2 * ν - 2 * ν / 9) hδ_ne_zero hδ_ne_top
  have h_goalUnion_16ν9 : cfg.goalUnion (16 * ν / 9) := by
    have h_reshaped : d ^ (2 * ν / 9) * S ≤ d ^ (2 * ν / 9) * (d ^ (16 * ν / 9) * V * N ^ β) := by
      calc
        d ^ (2 * ν / 9) * S ≤ d ^ (2 * ν) * V * N ^ β := hresh
        _ = (d ^ (2 * ν / 9) * d ^ (2 * ν - 2 * ν / 9)) * V * N ^ β := by rw [h_rpow_add]
        _ = d ^ (2 * ν / 9) * (d ^ (2 * ν - 2 * ν / 9) * V * N ^ β) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        _ = d ^ (2 * ν / 9) * (d ^ (16 * ν / 9) * V * N ^ β) := by
          have : 2 * ν - 2 * ν / 9 = 16 * ν / 9 := by ring
          rw [this]
    have h_cancel : S ≤ d ^ (16 * ν / 9) * V * N ^ β :=
      ((ENNReal.mul_le_mul_iff_right hd2ν9_ne_zero hd2ν9_ne_top).mp h_reshaped)
    dsimp [goalUnion]
    simpa [U, V, N, d] using h_cancel
  -- 8. Since ν ≤ 16*ν/9, apply goalUnion_of_exponent_le
  have h_ν_le_16ν9 : ν ≤ 16 * ν / 9 := by
    nlinarith
  exact goalUnion_of_exponent_le cfg h_ν_le_16ν9 h_goalUnion_16ν9

/-- **Blueprint `lem:ml2goalfromdens`, multiplicity form.**
The density form of the goal converts into the multiplicity form `eqgoalmuT` with the same
gain, by `Kakeya.VeryNotSticky.goalUnion_of_goalDensity` followed by
`Kakeya.VeryNotSticky.goalMult_of_goalUnion`. This is the form in which the case split
`Kakeya.VeryNotSticky.exists_goalMult` consumes a leaf that produces a density estimate. -/
theorem goalMult_of_goalDensity (cfg : VeryNotSticky.{u}) {C : ENNReal} {r : NNReal} {ν : ℝ}
    (hν : 0 ≤ ν) (hr : cfg.a ≤ r)
    (hC : 1 ≤ C) (hC' : C ≠ ⊤) (hdata : cfg.AScaleData C r ν)
    (hdens : cfg.goalDensity (C ^ 2) r ν) : cfg.goalMult ν :=
  goalMult_of_goalUnion cfg (goalUnion_of_goalDensity cfg hν hr hC hC' hdata hdens)

end Kakeya.VeryNotSticky
