/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.Uniform
public import Kakeya.Factorization
public import Kakeya.DimensionThree.Plank.AngleDef
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.MainLemma2.VeryNotSticky
public import Kakeya.DimensionThree.MainLemma2.Goals
public import Kakeya.DimensionThree.MainLemma2.ThinConfig
public import Kakeya.DimensionThree.MainLemma2.ThinEstimates
public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle
public import Kakeya.DimensionThree.MainLemma2.TypicalAngle

/-!
# The transverse case of Main Lemma 2

In this file, we prove the transverse case of the non-slab case
of the thin case of Main Lemma 2 (blueprint subsection "Transverse case").

The argument of the blueprint is carried out in four steps, one declaration each:

* `Kakeya.VeryNotSticky.transverseFill` (blueprint `lem:ml2transverseFill`): the factoring
  bodies almost fill each ball of radius `θ b`. This is the plank-to-slab reduction at a
  prescribed angle, `ShadedPlank.reduction_to_slab_atTypicalAngle`, applied to the refinement
  produced together with the typical angle; it is an interface statement as a proposition, and its docstring records the one input that is still missing. Its two purely
  bookkeeping steps are split off and *are* proved:
  `Kakeya.VeryNotSticky.transverseFillTransport` (blueprint
  `lem:ml2transverseFillTransport`), the passage from the two radii of Item 1 of the reduction
  to a single radius `r ≥ θ b`, and `Kakeya.VeryNotSticky.transverseFillConstantBound`
  (blueprint `lem:ml2transverseFillConstantBound`), the arithmetic behind the sub-polynomial
  bound on the constant it produces.
* `Kakeya.VeryNotSticky.transverseMassBall` (blueprint `lem:ml2transverseMassBall`): a ball of
  the *transfer* radius `ρ = θ b / 2 ≥ 3A` still carrying a proportional share of the mass,
  by `Kakeya.exists_mem_volume_inter_ball_ge`.
* `Kakeya.VeryNotSticky.transverseBallFill` (blueprint `lem:ml2transverseBallFill`): the
  filling transfers from `𝕎'_B` down to `𝕋` by `Kakeya.ThinCase.transfer_thin`.
* `Kakeya.VeryNotSticky.transverseDensity` (blueprint `lem:ml2transverseDensity`): the
  single-ball estimate becomes the density form of the goal.

`Kakeya.VeryNotSticky.goalMult_of_theta_ge` (blueprint `lem:ml2transverse`) assembles them and
converts the density form into the multiplicity form by
`Kakeya.VeryNotSticky.goalMult_of_goalDensity`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u
/-! ### The transverse gain -/

/-- The transverse gain `ν = τ' β / 2` is positive. -/
theorem transverseGain_pos (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') :
    0 < τ' * cfg.β / 2 := by
  have hτ' : 0 < τ' := lt_trans params.hτ params.hτ'
  exact div_pos (mul_pos hτ' cfg.hβ) (by norm_num)

/-- The transverse gain `ν = τ' β / 2` is at least `90 η`, so the scale-`a` interface
`Kakeya.VeryNotSticky.exists_aScaleData` is available at it. -/
theorem transverseGain_ge (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') :
    90 * cfg.η ≤ τ' * cfg.β / 2 := by
  have hη := cfg.hη
  have hβ := cfg.hβ
  have hτ := params.hτ
  have hT := params.hτ'
  have hslabBias := params.slabBias
  have hscale := params.scale
  have hthick := params.thick
  rw [show Kakeya.VeryNotSticky.parameterSeparationConstant = (2 : ℝ) ^ 20 from rfl]
    at hslabBias hthick
  have hϱ : cfg.ϱ < 1 / (2 : ℝ) ^ 21 := by
    have hslab : (2 : ℝ) ^ 20 * cfg.ϱ < 1 / 2 := by
      nlinarith [hslabBias, hscale]
    nlinarith
  have hβτpos : 0 < cfg.β * τ := mul_pos hβ hτ
  have hϱβτ : cfg.ϱ * (cfg.β * τ) < (1 / (2 : ℝ) ^ 21) * (cfg.β * τ) := by
    nlinarith [hϱ, hβτpos]
  have h20η : (2 : ℝ) ^ 20 * cfg.η < (1 / (2 : ℝ) ^ 21) * (cfg.β * τ) := by
    nlinarith [hthick, hϱβτ]
  have hβτgt : (2 : ℝ) ^ 41 * cfg.η < cfg.β * τ := by
    nlinarith
  have hητ'β : (2 : ℝ) ^ 41 * cfg.η < τ' * cfg.β := by
    nlinarith [hβτgt, hT, hβ]
  have hηhalf : (2 : ℝ) ^ 40 * cfg.η < τ' * cfg.β / 2 := by
    nlinarith
  have h90 : (90 : ℝ) * cfg.η ≤ (2 : ℝ) ^ 40 * cfg.η := by
    nlinarith [hη]
  nlinarith

/-! ### The transverse radius -/

/-- **Lower bounds for the transverse radius** (blueprint `lem:ml2transverseRadiusLower`).

Every step of the transverse case reads the transverse hypothesis `θ ≥ δ^{-τ'} a/b` as a
statement about the *radius* `θ b` rather than about the angle. Since `0 < δ ≤ a ≤ b`, the
factor `b` may be multiplied through the hypothesis, and the remaining bounds follow from
`δ ≤ a` and `1 ≤ δ^{-τ'}`. -/
theorem transverseRadiusLower (cfg : VeryNotSticky.{u}) {τ' : ℝ} (hτ' : 0 < τ') (θ : NNReal)
    (htrans : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ θ) :
    cfg.δ ^ (-τ') * cfg.a ≤ θ * cfg.b ∧ cfg.δ ^ (1 - τ') ≤ θ * cfg.b ∧
      cfg.a ≤ θ * cfg.b ∧ 0 < θ * cfg.b := by
  have hapos : 0 < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
  have hbpos : 0 < cfg.b := lt_of_lt_of_le hapos cfg.hdims.2.1
  have hbne : cfg.b ≠ 0 := ne_of_gt hbpos
  have h1 : cfg.δ ^ (-τ') * cfg.a ≤ θ * cfg.b := by
    calc
      cfg.δ ^ (-τ') * cfg.a
          = cfg.δ ^ (-τ') * (cfg.a / cfg.b) * cfg.b := by
            rw [mul_assoc, div_mul_cancel₀ cfg.a hbne]
      _ ≤ θ * cfg.b := mul_le_mul_left htrans cfg.b
  have hone : (1 : NNReal) ≤ cfg.δ ^ (-τ') :=
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos cfg.hδ cfg.hδ1 (neg_nonpos.mpr hτ'.le)
  have h3 : cfg.a ≤ θ * cfg.b := by
    calc
      cfg.a = 1 * cfg.a := by simp
      _ ≤ cfg.δ ^ (-τ') * cfg.a := mul_le_mul_left hone cfg.a
      _ ≤ θ * cfg.b := h1
  have h2 : cfg.δ ^ (1 - τ') ≤ θ * cfg.b := by
    calc
      cfg.δ ^ (1 - τ')
          = cfg.δ ^ ((-τ') + 1) := by congr 1; ring
      _ = cfg.δ ^ (-τ') * cfg.δ ^ (1 : ℝ) := by rw [NNReal.rpow_add cfg.hδ.ne' (-τ') 1]
      _ = cfg.δ ^ (-τ') * cfg.δ := by rw [NNReal.rpow_one]
      _ ≤ cfg.δ ^ (-τ') * cfg.a := mul_le_mul_right cfg.hdims.1 (cfg.δ ^ (-τ'))
      _ ≤ θ * cfg.b := h1
  exact ⟨h1, h2, h3, lt_of_lt_of_le hapos h3⟩

/-- **The transfer radius exceeds the covering radius** (blueprint `lem:ml2transverseRadius`).

Multiplying the fifth clause `6 C_{w₁}(C₀) ≤ δ^{-τ'}` of Configuration `hyp:ml2scale` — the
hypothesis `hsmall` — by `a` gives `6A ≤ δ^{-τ'} a`, and `δ^{-τ'} a ≤ θ b` is the first bound
of `Kakeya.VeryNotSticky.transverseRadiusLower`. Halving gives `3A ≤ θ b / 2`. -/
theorem transverseRadius_ge (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {τ' : ℝ}
    (hτ' : 0 < τ') (θ : NNReal) (htrans : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ θ)
    (hsmall : 6 * ThinCase.w1Constant bd.C₀ ≤ cfg.δ ^ (-τ')) :
    3 * ThinCase.rad bd.C₀ cfg.a ≤ θ * cfg.b / 2 := by
  have hkey : 6 * ThinCase.rad bd.C₀ cfg.a ≤ θ * cfg.b := by
    calc
      6 * ThinCase.rad bd.C₀ cfg.a
          = 6 * ThinCase.w1Constant bd.C₀ * cfg.a := by
            unfold ThinCase.rad
            ring
      _ ≤ cfg.δ ^ (-τ') * cfg.a := mul_le_mul_left hsmall cfg.a
      _ ≤ θ * cfg.b := (transverseRadiusLower cfg hτ' θ htrans).1
  rw [le_div_iff₀ (by norm_num : (0 : NNReal) < 2)]
  calc
    3 * ThinCase.rad bd.C₀ cfg.a * 2 = 6 * ThinCase.rad bd.C₀ cfg.a := by ring
    _ ≤ θ * cfg.b := hkey

/-! ### Step 1: the bodies almost fill a `θ b`-ball -/

/-- Scaling the radius of a ball in `ℝ³` by a nonnegative factor `k` multiplies its volume by
`k³`.

Lebesgue measure on `ℝ³` is an additive Haar measure, so
`MeasureTheory.Measure.addHaar_ball_mul` scales the radius by `k^{dim}`, the dimension being
`3` by `finrank_euclideanSpace_fin`, and `MeasureTheory.Measure.addHaar_ball_center` removes
the centre. `Kakeya.VeryNotSticky.volume_ball_two_mul_le` is the case `k = 2`, in the
inequality form that `Kakeya.VeryNotSticky.transverseBallFill` uses; this is the general
equality, and `Kakeya.VeryNotSticky.transverseFillTransport` needs it at `k = 3` and at
`k = max(1, C₀/3)`. -/
theorem volume_ball_mul (y : EuclideanSpace ℝ (Fin 3)) {k : ℝ} (hk : 0 ≤ k) (r : ℝ) :
    volume (ball y (k * r)) = ENNReal.ofReal (k ^ 3) * volume (ball y r) := by
  rw [MeasureTheory.Measure.addHaar_ball_mul volume y hk r,
    MeasureTheory.Measure.addHaar_ball_center volume y r,
    finrank_euclideanSpace_fin (𝕜 := ℝ)]

/-- **Transporting an almost-filling estimate to a radius above `θ b`** (blueprint
`lem:ml2transverseFillTransport`, equation `transverseFillTransport`).

This is the coordinate bookkeeping of `Kakeya.VeryNotSticky.transverseFill`, split off from it
for the reason the arithmetic of `Kakeya.VeryNotSticky.transverseFillConstantBound` is: the
statement it serves is an interface stub and should carry a single idea, there the application
of `ShadedPlank.reduction_to_slab_atTypicalAngle` at a prescribed angle. Nothing here is about
planks, angles or refinements; it is two moves on balls.

Read `ρ = r₁ θ b'` for the transported inner radius of the rescaled coordinates of blueprint
`lem:ml2plankpresentation` and `t = θ b` for the radius the transverse case must reach. The
hypothesis `h` is Item 1 of `ShadedPlank.reduction_to_slab_atTypicalAngle` after the rescaling
bridge `Kakeya.VeryNotSticky.PlankPresentationData.hbridge` has moved it to the original
coordinates, where the dilation `ShadedPlank.redPlankTube.ballDilation = 3` separates the two
radii `ρ` and `3ρ`. The comparison `hcomp`, `t ≤ C₀ ρ`, is the radius half of (C4):
`r₁ b' ≥ C₀⁻¹ b`, multiplied by `θ`. No nonnegativity of `t` is assumed; it is not needed,
and at the call site it is anyway a consequence of `hcomp`.

The two moves are the two factors of the constant, and they are exactly the two the sixth
clause `Kakeya.VeryNotSticky.CaseScale.transverse_fill` is sized for. *Collapsing the two
radii*: `|B(x, 3ρ)| = 3³ |B(x, ρ)|`, so discarding `3⁻³` gives the single-radius form at
`3ρ`. *Enlarging the radius*: at `r = max(3ρ, t)` one has `r ≥ t`, and `r ≤ max(1, C₀/3) · 3ρ`
— if `3ρ ≥ t` because `max(1, C₀/3) ≥ 1`, and otherwise because `hcomp` reads
`t ≤ C₀ ρ = (C₀/3) · 3ρ` — so the reference volume grows by at most `max(1, C₀/3)³` while the
shaded mass only grows.

An almost-filling estimate cannot be moved to a *smaller* radius, which is why the conclusion
is at *some* `r ≥ t` and not at `t` itself; every consumer of
`Kakeya.VeryNotSticky.transverseFill` needs only that inequality, through
`Kakeya.VeryNotSticky.transverseRadiusLower`.

The produced radius is also bounded *above*, by `max(3ρ, t)`, which is the value it is
constructed as. That second bound is what
`Kakeya.VeryNotSticky.transverseFillRadius_le_one` turns into `r ≤ 1`, the upper bound on the
radius that blueprint `lem:ml2aScaleData` demands and that
`Kakeya.VeryNotSticky.exists_aScaleData` therefore takes as a hypothesis. -/
theorem transverseFillTransport {C₀ : NNReal} {ρ t : ℝ} (hρ : 0 ≤ ρ)
    (hcomp : t ≤ (C₀ : ℝ) * ρ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (x : EuclideanSpace ℝ (Fin 3)) (γ : ENNReal)
    (h : γ * volume (ball x ρ) ≤ volume (U ∩ ball x (3 * ρ))) :
    ∃ r : NNReal, t ≤ (r : ℝ) ∧ (r : ℝ) ≤ max (3 * ρ) t ∧
      ((27 * max 1 (C₀ / 3) ^ 3 : NNReal) : ENNReal)⁻¹ * γ * volume (ball x (r : ℝ)) ≤
        volume (U ∩ ball x (r : ℝ)) := by
  set M : NNReal := max 1 (C₀ / 3)
  have hM1 : (1 : NNReal) ≤ M := le_max_left _ _
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  let R : ℝ := 3 * ρ
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  let rr : ℝ := max R t
  have hrr : 0 ≤ rr := by
    dsimp [rr]
    positivity
  -- collapse radii: `|B(x, 3ρ)| = 3³ |B(x, ρ)|`
  have h27 : volume (ball x R) = 27 * volume (ball x ρ) := by
    dsimp [R]
    calc
      volume (ball x (3 * ρ)) = ENNReal.ofReal (3 ^ 3) * volume (ball x ρ) :=
        volume_ball_mul x (k := 3) (by norm_num : (0 : ℝ) ≤ 3) ρ
      _ = 27 * volume (ball x ρ) := by norm_num [ENNReal.ofReal]
  -- enlarged radius: `rr ≤ M * R`
  have hle : rr ≤ (M : ℝ) * R := by
    dsimp [rr]
    apply max_le
    · -- R ≤ M * R
      calc
        R = (1 : ℝ) * R := by rw [one_mul]
        _ ≤ (M : ℝ) * R := mul_le_mul_of_nonneg_right hMR hR
    · -- t ≤ M * R
      have hC₀div : (C₀ : ℝ) / 3 ≤ (M : ℝ) := by
        exact_mod_cast (le_max_right (1 : NNReal) (C₀ / 3) : C₀ / 3 ≤ max 1 (C₀ / 3))
      have hC₀le3M : (C₀ : ℝ) ≤ 3 * (M : ℝ) := by
        calc
          (C₀ : ℝ) = 3 * ((C₀ : ℝ) / 3) := by ring
          _ ≤ 3 * (M : ℝ) := mul_le_mul_of_nonneg_left hC₀div (by norm_num : (0 : ℝ) ≤ 3)
      have hterm : (C₀ : ℝ) * ρ ≤ (M : ℝ) * R := by
        calc
          (C₀ : ℝ) * ρ ≤ (3 * (M : ℝ)) * ρ := by
            exact mul_le_mul_of_nonneg_right hC₀le3M hρ
          _ = (M : ℝ) * (3 * ρ) := by ring
          _ = (M : ℝ) * R := by dsimp [R]
      exact le_trans hcomp hterm
  -- reference volume growth: `|B(x, rr)| ≤ M³ |B(x, R)|`
  have hvolM : volume (ball x rr) ≤ (M : ENNReal) ^ 3 * volume (ball x R) := by
    have hmono : volume (ball x rr) ≤ volume (ball x ((M : ℝ) * R)) :=
      measure_mono (Metric.ball_subset_ball hle)
    have hS := volume_ball_mul x (k := (M : ℝ)) M.coe_nonneg R
    rw [hS] at hmono
    calc
      volume (ball x rr) ≤ ENNReal.ofReal ((M : ℝ) ^ 3) * volume (ball x R) := hmono
      _ = (M : ENNReal) ^ 3 * volume (ball x R) := by
        rw [ENNReal.ofReal_pow M.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  -- mass monotonicity
  have hmass : volume (U ∩ ball x R) ≤ volume (U ∩ ball x rr) := by
    apply measure_mono
    exact Set.inter_subset_inter_right _ (Metric.ball_subset_ball (le_max_left R t))
  -- ENNReal constant bookkeeping
  let M3 : ENNReal := (M : ENNReal) ^ 3
  have hM0e : (M : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hM1))
  have hM3e0 : M3 ≠ 0 := by
    dsimp [M3]
    exact pow_ne_zero 3 hM0e
  have hM3et : M3 ≠ ⊤ := by
    dsimp [M3]
    exact ENNReal.pow_ne_top (ENNReal.coe_ne_top : (M : ENNReal) ≠ ⊤)
  have h27e : (27 : ENNReal) ≠ 0 := by norm_num
  have h27t : (27 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  let Kinv : ENNReal := ((27 * M ^ 3 : NNReal) : ENNReal)⁻¹
  have hKM : Kinv * M3 = (27 : ENNReal)⁻¹ := by
    dsimp [Kinv, M3]
    calc
      ((27 : ENNReal) * (M : ENNReal) ^ 3)⁻¹ * (M : ENNReal) ^ 3
          = (27 : ENNReal)⁻¹ * (((M : ENNReal) ^ 3)⁻¹ * (M : ENNReal) ^ 3) := by
              rw [ENNReal.mul_inv (Or.inl (by norm_num : (27 : ENNReal) ≠ 0))
                                  (Or.inl (by exact ENNReal.coe_ne_top))]
              ring
      _ = (27 : ENNReal)⁻¹ := by
              rw [ENNReal.inv_mul_cancel hM3e0 hM3et]
              simp
  have hchain : Kinv * γ * volume (ball x rr) ≤ volume (U ∩ ball x rr) := by
    calc
      Kinv * γ * volume (ball x rr)
          ≤ Kinv * γ * (M3 * volume (ball x R)) := by gcongr
      _ = (27 : ENNReal)⁻¹ * γ * volume (ball x R) := by
              calc
                Kinv * γ * (M3 * volume (ball x R))
                    = (Kinv * M3) * γ * volume (ball x R) := by ring
                _ = (27 : ENNReal)⁻¹ * γ * volume (ball x R) := by rw [hKM]
      _ = (27 : ENNReal)⁻¹ * γ * (27 * volume (ball x ρ)) := by rw [h27]
      _ = γ * volume (ball x ρ) := by
              calc
                (27 : ENNReal)⁻¹ * γ * (27 * volume (ball x ρ))
                    = ((27 : ENNReal)⁻¹ * 27) * γ * volume (ball x ρ) := by ring
                _ = γ * volume (ball x ρ) := by
                    rw [ENNReal.inv_mul_cancel h27e h27t]
                    simp
      _ ≤ volume (U ∩ ball x (3 * ρ)) := h
      _ = volume (U ∩ ball x R) := by dsimp [R]
      _ ≤ volume (U ∩ ball x rr) := hmass
  refine ⟨⟨rr, hrr⟩, le_max_right R t, ?_, ?_⟩
  · exact le_rfl
  · exact hchain

/-- **The filling constant is sub-polynomial** (blueprint
`lem:ml2transverseFillConstantBound`, equation `transverseFillConstantBound`).

The constant assembled in the proof of `Kakeya.VeryNotSticky.transverseFill` is
`Cfill = max(1, 3³ max(1, C₀/3)³ c₁⁻¹)`, with `c₁` the constant of Item 1 of
`ShadedPlank.reduction_to_slab_atTypicalAngle` (blueprint `def:redPlankTubeFillConstant`): the
`3³` and the `max(1, C₀/3)³` are the two factors that
`Kakeya.VeryNotSticky.transverseFillTransport` discards, and `c₁⁻¹` is what Section 6
supplies. This lemma is the arithmetic that turns those three factors into
`transverseFillConstantBound`, `Cfill ≤ δ^{-η}`.

The exponent is split evenly. The first half, `3³ max(1, C₀/3)³ ≤ δ^{-η/2}`, is the sixth
clause `Kakeya.VeryNotSticky.CaseScale.transverse_fill`, whose left-hand side is literally
`27 * max 1 (C₀/3)³`. The second, `c₁⁻¹ ≤ (δ')^{-η/2}`, is item 5 of
`ShadedPlank.reduction_to_slab_atTypicalAngle` (blueprint `redPlankTubeConstantBound`), read
at the exponent `ε' = η/2` and *at the scale the lemma is applied at*, namely the rescaled
`δ' = δ/r₁ = δ^{1-exscal}` of blueprint `lem:ml2plankpresentation`. That is the hypothesis
`hc1`, and it is stated at `δ'` rather than at `δ` for the reason the blueprint gives:
reading it at `δ` would be reading it at a scale the lemma was not applied at. The passage
between the two is free, `δ ≤ δ'` following from `r₁ = δ^{exscal} ≤ 1`, and costs no constant;
the passage between `a` and `a'` would not be free, which is why no version of this lemma may
be stated at the unprimed scales.

The enlargement to `max(1, ·)` weakens neither conclusion: it is needed because `c₁` may
exceed `1`, and it is harmless because `δ^{-η} ≥ 1` for `0 < δ ≤ 1` and `η > 0`. So the single
inequality below carries both halves of what `transverseFill` must produce, `1 ≤ Cfill` being
`le_max_left`.

This is the exact analogue, one step earlier in the chain, of
`Kakeya.VeryNotSticky.transverseBallFillConstantBound`, and the threshold cannot be dispensed
with for the same reason: the explicit factors alone are at least `3³`, so at `δ = 1` no bound
of the form `δ^{-kη}` holds. -/
theorem transverseFillConstantBound (cfg : VeryNotSticky.{u}) {τ τ' νA : ℝ}
    {bd : BallData cfg} {tc : ThinConfig cfg bd} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr) {c1 : NNReal}
    (hc1 : c1⁻¹ ≤ (cfg.δ ^ (1 - cfg.exscal)) ^ (-(16 * cfg.η / 2))) :
    max 1 (27 * max 1 (bd.C₀ / 3) ^ 3 * c1⁻¹) ≤ cfg.δ ^ (-(9 * cfg.η)) := by
  -- the passage from the rescaled scale `δ' = δ^{1-exscal}` to `δ` is free, `δ ≤ δ'`
  have hc1' : c1⁻¹ ≤ cfg.δ ^ (-(16 * cfg.η / 2)) := by
    calc
      c1⁻¹ ≤ (cfg.δ ^ (1 - cfg.exscal)) ^ (-(16 * cfg.η / 2)) := hc1
      _ = cfg.δ ^ ((1 - cfg.exscal) * (-(16 * cfg.η / 2))) := by
          rw [← NNReal.rpow_mul]
      _ ≤ cfg.δ ^ (-(16 * cfg.η / 2)) := by
          exact NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1
            (by nlinarith [cfg.hexscal, cfg.hη] :
              -(16 * cfg.η / 2) ≤ (1 - cfg.exscal) * (-(16 * cfg.η / 2)))
  -- the two halves, `transverse_fill` (`η/2`) and `hc1'` (`8η`), multiply to `δ^{-17η/2}`,
  -- which is absorbed in the round figure `δ^{-9η}`.
  have hmul : 27 * max 1 (bd.C₀ / 3) ^ 3 * c1⁻¹ ≤ cfg.δ ^ (-(9 * cfg.η)) := by
    calc
      27 * max 1 (bd.C₀ / 3) ^ 3 * c1⁻¹
          ≤ 27 * max 1 (bd.C₀ / 3) ^ 3 * cfg.δ ^ (-(16 * cfg.η / 2)) := by
              gcongr
      _ ≤ cfg.δ ^ (-(cfg.η / 2)) * cfg.δ ^ (-(16 * cfg.η / 2)) := by
              gcongr
              exact scale.transverse_fill
      _ = cfg.δ ^ (-(cfg.η / 2) + -(16 * cfg.η / 2)) := (NNReal.rpow_add cfg.hδ.ne' _ _).symm
      _ ≤ cfg.δ ^ (-(9 * cfg.η)) :=
            NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 (by linarith [cfg.hη])
  -- the enlargement to `max 1 (·)` is harmless because `δ^{-9η} ≥ 1`
  exact max_le
    (NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos cfg.hδ cfg.hδ1
      (by linarith [cfg.hη] : -(9 * cfg.η) ≤ 0)) hmul

/-- **The radius produced by the filling step lies in the unit ball** (the upper half of the
radius hypothesis of blueprint `lem:ml2aScaleData`).

`Kakeya.VeryNotSticky.transverseFillTransport` builds its radius as `max(3ρ, t)` with
`ρ = 2 r₁ θ b'` the transported inner radius — the plank presentation normalizes by `2 r₁`, not
`r₁`, so the bridge of `Kakeya.VeryNotSticky.TypicalAngleData.hbridgeP` returns radii scaled by
`2 r₁` — and `t = θ b`; this lemma is the observation that
both entries are at most `1`, so that the transverse branch can discharge the hypothesis
`r ≤ 1` of `Kakeya.VeryNotSticky.exists_aScaleData`, which is not optional — without it the
scale-`r` interface is refutable, since estimate (ii) carries `r^{2β}` while every shaded
union in sight lies in `B₁`.

`t = θ b ≤ 1` is immediate from `θ ≤ 1` and `b ≤ δ^{exscal} ≤ 1`. The other entry needs a
threshold, and it is one the branch already carries: `3ρ = 6 r₁ θ b' ≤ 6 δ^{exscal}`, and the
sixth clause `Kakeya.VeryNotSticky.CaseScale.transverse_fill` gives
`6 ≤ 27 ≤ 27 max(1, C₀/3)³ ≤ δ^{-η/2}`, whence `6 δ^{exscal} ≤ δ^{exscal - η/2} ≤ 1` because
`η/2 < exscal` by `Kakeya.VeryNotSticky.CaseParams.slabDensity` and `δ ≤ 1`. So no new
fixed-scale assumption is introduced: the clause is simply spent twice. -/
theorem transverseFillRadius_le_one (cfg : VeryNotSticky.{u}) {τ τ' νA : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    {bd : BallData cfg} {tc : ThinConfig cfg bd} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    {θ b' r : NNReal} (hθ1 : θ ≤ 1) (hb1' : b' ≤ 1)
    (hr : (r : ℝ) ≤
      max (3 * (2 * (cfg.r₁ : ℝ) * ((θ * b' : NNReal) : ℝ))) ((θ * cfg.b : NNReal) : ℝ)) :
    r ≤ 1 := by
  -- `b ≤ δ^{exscal} ≤ 1`
  have hb_le1 : cfg.b ≤ 1 :=
    le_trans cfg.hdims.2.2 (NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le)
  -- entry 2 of the max: `θ b ≤ 1`
  have hθb1 : (θ * cfg.b : NNReal) ≤ 1 := by
    calc
      θ * cfg.b ≤ 1 * 1 := mul_le_mul' hθ1 hb_le1
      _ = 1 := by norm_num
  -- `3 ≤ δ^{-η/2}` from the sixth clause `transverse_fill`
  have h1le : (1 : NNReal) ≤ max 1 (bd.C₀ / 3) ^ 3 := one_le_pow₀ (le_max_left _ _)
  have h27le : (27 : NNReal) ≤ 27 * max 1 (bd.C₀ / 3) ^ 3 := by
    calc
      (27 : NNReal) = 27 * 1 := by ring
      _ ≤ 27 * max 1 (bd.C₀ / 3) ^ 3 := by gcongr
  have h27δ : (27 : NNReal) ≤ cfg.δ ^ (-(cfg.η / 2)) := le_trans h27le scale.transverse_fill
  have h6δ : (6 : NNReal) ≤ cfg.δ ^ (-(cfg.η / 2)) :=
    le_trans (by norm_num : (6 : NNReal) ≤ 27) h27δ
  -- `δ^{-η/2} ≤ δ^{-exscal}` because `η/2 ≤ exscal`
  have hδhalf_le_exscal_neg : cfg.δ ^ (-(cfg.η / 2)) ≤ cfg.δ ^ (-cfg.exscal) := by
    exact NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1
      (by nlinarith [params.slabDensity, cfg.hη, cfg.hexscal] :
        -cfg.exscal ≤ -(cfg.η / 2))
  have h6δe' : (6 : NNReal) ≤ cfg.δ ^ (-cfg.exscal) := le_trans h6δ hδhalf_le_exscal_neg
  -- `6 δ^{exscal} ≤ 1`
  have h6δe : 6 * cfg.δ ^ cfg.exscal ≤ 1 := by
    calc
      6 * cfg.δ ^ cfg.exscal
          ≤ cfg.δ ^ (-cfg.exscal) * cfg.δ ^ cfg.exscal := by gcongr
      _ = cfg.δ ^ (-cfg.exscal + cfg.exscal) :=
            (NNReal.rpow_add cfg.hδ.ne' (-cfg.exscal) cfg.exscal).symm
      _ = cfg.δ ^ (0 : ℝ) := by congr 1; ring
      _ = 1 := NNReal.rpow_zero _
  -- entry 1 of the max: `6 r₁ θ b' ≤ 1`
  have h6r1 : 6 * cfg.r₁ ≤ 1 := by
    rw [show cfg.r₁ = cfg.δ ^ cfg.exscal by rfl]
    exact h6δe
  have hθb'1 : (θ * b' : NNReal) ≤ 1 := by
    calc
      θ * b' ≤ 1 * 1 := mul_le_mul' hθ1 hb1'
      _ = 1 := by norm_num
  have hg1 : 3 * (2 * cfg.r₁ * (θ * b' : NNReal)) ≤ 1 := by
    calc
      3 * (2 * cfg.r₁ * (θ * b' : NNReal)) = (6 * cfg.r₁) * (θ * b' : NNReal) := by ring
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  -- both entries of the max are at most `1`
  have hmax1ℝ : max (3 * (2 * (cfg.r₁ : ℝ) * ((θ * b' : NNReal) : ℝ)))
      ((θ * cfg.b : NNReal) : ℝ) ≤ 1 := by
    exact max_le (by exact_mod_cast hg1) (by exact_mod_cast hθb1)
  exact NNReal.coe_le_one.mp (le_trans hr hmax1ℝ)

/-- **The transverse branch supplies it too, and needs no threshold at all.**

`Kakeya.VeryNotSticky.transverseFillRadius_le_one` bounds the same `max` by `1` and spends the
sixth clause of Configuration `hyp:ml2scale` to do so.  For the sharper `6 δ^{exscal}` no clause
is needed: the first entry is `6 r₁ (θ b') ≤ 6 r₁ = 6 δ^{exscal}` because `θ b' ≤ 1`, and the
second is `θ b ≤ b ≤ δ^{exscal}` by `cfg.hdims`.  This is the bound that theorem establishes
internally and discards. -/
theorem transverseFillRadius_le_six_rpow_exscal (cfg : VeryNotSticky.{u})
    {θ b' r : NNReal} (hθ1 : θ ≤ 1) (hb1' : b' ≤ 1)
    (hr : (r : ℝ) ≤
      max (3 * (2 * (cfg.r₁ : ℝ) * ((θ * b' : NNReal) : ℝ))) ((θ * cfg.b : NNReal) : ℝ)) :
    r ≤ 6 * cfg.δ ^ cfg.exscal := by
  have hr₁ : cfg.r₁ = cfg.δ ^ cfg.exscal := rfl
  have hθb'1 : (θ * b' : NNReal) ≤ 1 := by
    calc θ * b' ≤ 1 * 1 := mul_le_mul' hθ1 hb1'
      _ = 1 := by norm_num
  have hg1 : 3 * (2 * cfg.r₁ * (θ * b' : NNReal)) ≤ 6 * cfg.δ ^ cfg.exscal := by
    calc 3 * (2 * cfg.r₁ * (θ * b' : NNReal)) = (6 * cfg.r₁) * (θ * b' : NNReal) := by ring
      _ ≤ (6 * cfg.r₁) * 1 := by gcongr
      _ = 6 * cfg.δ ^ cfg.exscal := by rw [mul_one, hr₁]
  have hb_le : cfg.b ≤ cfg.δ ^ cfg.exscal := cfg.hdims.2.2
  have hθb1 : (θ * cfg.b : NNReal) ≤ 6 * cfg.δ ^ cfg.exscal := by
    calc θ * cfg.b ≤ 1 * cfg.δ ^ cfg.exscal := mul_le_mul' hθ1 hb_le
      _ = cfg.δ ^ cfg.exscal := one_mul _
      _ ≤ 6 * cfg.δ ^ cfg.exscal := by
          nth_rewrite 1 [show cfg.δ ^ cfg.exscal = 1 * cfg.δ ^ cfg.exscal from (one_mul _).symm]
          gcongr; norm_num
  have hmaxℝ : max (3 * (2 * (cfg.r₁ : ℝ) * ((θ * b' : NNReal) : ℝ))) ((θ * cfg.b : NNReal) : ℝ)
      ≤ ((6 * cfg.δ ^ cfg.exscal : NNReal) : ℝ) :=
    max_le (by exact_mod_cast hg1) (by exact_mod_cast hθb1)
  exact_mod_cast le_trans hr hmaxℝ

/-- **The reduction, run at the typical angle, in the rescaled coordinates** (the first half of
the proof of blueprint `lem:ml2transverseFill`).

This is `Kakeya.VeryNotSticky.CaseScale.transverseFill_threshold` — the eleventh clause of
Configuration `hyp:ml2scale`, i.e. `Kakeya.VeryNotSticky.IsReductionFillAvailable` at the
rescaled scale `δ' = δ/r₁` — applied to the plank data carried by `ta`, with its hypotheses
discharged one for one from the fields of `Kakeya.VeryNotSticky.TypicalAngleData`, and with
its Item 1 already fired at a point of the produced family and pushed up to the refined plank
shading `Y''_𝒫 = ta.YP`.

Two of those moves deserve a word. Item 1 is guarded by a nonemptiness condition, and the
point at which it is fired comes from the nonemptiness clause of `IsReductionFillAvailable`;
the passage from `U(𝒫', Y')` to `U(𝒫, Y''_𝒫)` is monotonicity of volume along the refinement
clause `ShadedBody.IsRefinement s' Y' 𝕊* ta.YP` of that same predicate, which is the clause
Section 6 supplies for exactly this step. The output family `(𝒫', Y')` does not appear in the
conclusion: what the rest of the argument needs is the estimate at `ta.YP`, which is where the
rescaling bridge `Kakeya.VeryNotSticky.TypicalAngleData.hbridgeP` picks it up.

The transverse-case hypothesis `htrans : δ^{-τ'} a/b ≤ θ` (GWZ l.2224) is what unlocks the
fullness clause `Kakeya.VeryNotSticky.TypicalAngleData.hfullP`, which is asserted only under
that guard; it is the only use of `htrans` here. -/
theorem transverseFillPlankEstimate (cfg : VeryNotSticky.{u}) {τ τ' νA : ℝ}
    {bd : BallData cfg} {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs}
    {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (ta : TypicalAngleData cfg tc hB τ')
    (htrans : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ ta.θ) :
    ∃ (c1 : NNReal) (x : EuclideanSpace ℝ (Fin 3)),
      0 < c1 ∧
      c1⁻¹ ≤ (cfg.δ ^ (1 - cfg.exscal)) ^ (-(16 * cfg.η / 2)) ∧
      (c1 : ENNReal) * (ta.a' : ENNReal) ^ (4 * (16 * cfg.η)) *
          (ta.a' : ENNReal) ^ (16 * cfg.η / 256) *
          volume (closedBall x ((ta.θ * ta.b' : NNReal) : ℝ)) ≤
        volume (iUnionShade ta.sel ta.YP ∩
          closedBall x
            ((ShadedPlank.redPlankTube.ballDilation * ta.θ * ta.b' : NNReal) : ℝ)) := by
  -- (A) the rescaled scale `δ' = δ / r₁ = δ^{1-exscal}`
  have hr₁pos : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hδr : cfg.δ / cfg.r₁ = cfg.δ ^ (1 - cfg.exscal) := by
    rw [show cfg.r₁ = cfg.δ ^ cfg.exscal by rfl]
    simpa [NNReal.rpow_one] using (NNReal.rpow_sub cfg.hδ.ne' 1 cfg.exscal).symm
  -- the `a'`-multiplicity hypothesis from `ta.hmultP`, `δ/r₁ ≤ a'` and the negative exponent
  have hmult_a :
      (ta.a' : ENNReal) ^ (-(16 * cfg.η)) ≤
        ShadedBody.multiplicity ta.sel (ShadedPlank.bodies ta.SP) := by
    have hle :
        (ta.a' : ENNReal) ^ (-(16 * cfg.η)) ≤
          ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) ^ (-(16 * cfg.η)) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      apply ENNReal.inv_le_inv'
      exact ENNReal.rpow_le_rpow
        (by exact_mod_cast (show cfg.δ / cfg.r₁ ≤ ta.a' from ta.hδa'))
        (by linarith [cfg.hη])
    exact le_trans hle ta.hmultP
  -- `ta.hCtyp` is at `-(η/256)`; the fill predicate at `16η` asks only for the *weaker*
  -- `-(16η/256)`, and `x ↦ (δ/r₁)^x` is antitone on a base `≤ 1`, so the existing clause pays.
  have hbasepos : (0 : NNReal) < cfg.δ / cfg.r₁ := div_pos cfg.hδ hr₁pos
  have hbase1 : cfg.δ / cfg.r₁ ≤ 1 := le_of_lt (lt_of_le_of_lt ta.hδa' ta.ha'1)
  have hCtyp16 : ta.Ctyp ≤ (cfg.δ / cfg.r₁) ^ (-(16 * cfg.η / 256)) :=
    le_trans (by simpa [hδr] using ta.hCtyp)
      (NNReal.rpow_le_rpow_of_exponent_ge hbasepos hbase1 (by linarith [cfg.hη]))
  -- (B) fire the plank-to-slab reduction at the rescaled scale
  have hred := scale.transverseFill_threshold (a := ta.a') (b := ta.b') (hab := ta.hab')
      (hb1 := ta.hb1') ta.sel ta.SP ta.θ ta.hθ1 ta.Ctyp ta.YP
  rcases hred (by exact div_pos cfg.hδ hr₁pos) ta.hδa' ta.ha'1
      (by simpa [ta.hSP] using ta.hwin)
      (ta.hfullP htrans)
      hmult_a
      ta.hmultP
      scale.multiplicity_large
      ta.hcard
      ta.hθab
      ta.hCtyp1
      hCtyp16
      ta.hPrefine ta.hPconst ta.hPtyp ta.hmaxAbsP with
    ⟨s', Y', c1, hc1pos, _href, href2, hneu, hitem1, hitem5⟩
  -- (C) a point of the nonempty `U(s', Y')`, and Item 1 fired at it
  rcases hneu with ⟨p, hp⟩
  have hmem : (ShadedBody.iUnionShade s' Y' ∩ Metric.closedBall p
      ((ta.θ * ta.b' : NNReal) : ℝ)).Nonempty := by
    refine ⟨p, hp, ?_⟩
    rw [Metric.mem_closedBall, dist_self]
    positivity
  have h1fill := hitem1 p hmem
  -- (D) `(s', Y')` refines `(sel, YP)`, so the estimate moves to `U(sel, YP)`
  have hcont' : ShadedBody.iUnionShade s' Y' ⊆ ShadedBody.iUnionShade ta.sel ta.YP := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxsh⟩
    exact Set.mem_iUnion₂.mpr ⟨i, href2.1 hi, (href2.2 i hi).2 hxsh⟩
  have hmono1 : volume (ShadedBody.iUnionShade s' Y' ∩ Metric.closedBall p
      ((ShadedPlank.redPlankTube.ballDilation * ta.θ * ta.b' : NNReal) : ℝ)) ≤
      volume (ShadedBody.iUnionShade ta.sel ta.YP ∩
        Metric.closedBall p
          ((ShadedPlank.redPlankTube.ballDilation * ta.θ * ta.b' : NNReal) : ℝ)) := by
    exact measure_mono (Set.inter_subset_inter hcont' (subset_rfl))
  have h1cont :
      (c1 : ENNReal) * (ta.a' : ENNReal) ^ (4 * (16 * cfg.η)) *
          (ta.a' : ENNReal) ^ (16 * cfg.η / 256) *
      volume (Metric.closedBall p ((ta.θ * ta.b' : NNReal) : ℝ)) ≤
      volume (ShadedBody.iUnionShade ta.sel ta.YP ∩
        Metric.closedBall p
          ((ShadedPlank.redPlankTube.ballDilation * ta.θ * ta.b' : NNReal) : ℝ)) :=
    le_trans h1fill hmono1
  -- (E) assemble the output
  refine ⟨c1, p, hc1pos, ?_, h1cont⟩
  simpa [hδr] using hitem5

/-- **The density budget of the filling estimate** (the constant arithmetic of blueprint
`lem:ml2transverseFill`).

The estimate produced by `Kakeya.VeryNotSticky.transverseFillTransport` carries the density
`(27 · max(1, C₀/3)³)⁻¹ · c₁ (a')^{4η} (a')^{η/256}`, while the conclusion of
`Kakeya.VeryNotSticky.transverseFill` asks for `C_fill⁻¹ δ^{5η}` with
`C_fill = max(1, 27 · max(1, C₀/3)³ · c₁⁻¹)`, the constant of
`Kakeya.VeryNotSticky.transverseFillConstantBound`. This is the comparison of the two, and it
is the place where the exponent `5η` of the conclusion is paid for: `a' ≥ δ^{1-exscal} ≥ δ`,
so `(a')^{4η + η/256} ≥ δ^{17η/256} ≥ δ^{5η}` because `δ ≤ 1`. The enlargement of `C_fill` to
`max(1, ·)` only decreases the left-hand side, so it costs nothing here. -/
theorem transverseFillDensityBound (cfg : VeryNotSticky.{u}) {C₀ a' c1 : NNReal}
    (ha' : cfg.δ ^ (1 - cfg.exscal) ≤ a') (hc1 : 0 < c1) :
    ((max 1 (27 * max 1 (C₀ / 3) ^ 3 * c1⁻¹) : NNReal) : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (65 * cfg.η) ≤
      ((27 * max 1 (C₀ / 3) ^ 3 : NNReal) : ENNReal)⁻¹ *
        ((c1 : ENNReal) * (a' : ENNReal) ^ (4 * (16 * cfg.η)) *
          (a' : ENNReal) ^ (16 * cfg.η / 256)) := by
  let M : NNReal := 27 * max 1 (C₀ / 3) ^ 3
  -- `δ ≤ δ^{1-exscal} ≤ a'` (free passage between the scales)
  have hδleδ' : cfg.δ ≤ cfg.δ ^ (1 - cfg.exscal) := by
    calc
      cfg.δ = (cfg.δ ^ (1 : ℝ)) := (NNReal.rpow_one _).symm
      _ ≤ cfg.δ ^ (1 - cfg.exscal) :=
        NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 (by linarith [cfg.hexscal])
  have hδa' : cfg.δ ≤ a' := le_trans hδleδ' ha'
  have hδa'e : (cfg.δ : ENNReal) ≤ (a' : ENNReal) := by exact_mod_cast hδa'
  have hδ1e : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  -- positivity of `a'`
  have ha'pos : (0 : NNReal) < a' := lt_of_lt_of_le cfg.hδ hδa'
  have ha'ne : a' ≠ 0 := ne_of_gt ha'pos
  have ha'0e : (a' : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha'ne
  have ha'eau : (a' : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the power comparison `δ^{65η} ≤ (a')^{64η} (a')^{16η/256}` (the fill predicate now runs
  -- at `16η`, so the two items are `4·16η` and `16η/256`, summing to `64 + 1/16 ≤ 65` times `η`)
  have hD : (cfg.δ : ENNReal) ^ (65 * cfg.η) ≤
      (a' : ENNReal) ^ (4 * (16 * cfg.η)) * (a' : ENNReal) ^ (16 * cfg.η / 256) := by
    calc
      (cfg.δ : ENNReal) ^ (65 * cfg.η)
          ≤ (cfg.δ : ENNReal) ^ (4 * (16 * cfg.η) + 16 * cfg.η / 256) :=
            ENNReal.rpow_le_rpow_of_exponent_ge hδ1e (by nlinarith [cfg.hη])
      _ ≤ (a' : ENNReal) ^ (4 * (16 * cfg.η) + 16 * cfg.η / 256) :=
            ENNReal.rpow_le_rpow hδa'e (by nlinarith [cfg.hη])
      _ = (a' : ENNReal) ^ (4 * (16 * cfg.η)) * (a' : ENNReal) ^ (16 * cfg.η / 256) := by
            rw [← ENNReal.rpow_add (4 * (16 * cfg.η)) (16 * cfg.η / 256) ha'0e ha'eau]
  -- ENNReal hypotheses on the constants
  have hc1ne : c1 ≠ 0 := ne_of_gt hc1
  have hMne : M ≠ 0 := by
    dsimp [M]
    exact mul_ne_zero (by norm_num : (27 : NNReal) ≠ 0)
      (by positivity : (0 : NNReal) < max 1 (C₀ / 3) ^ 3).ne'
  have hM0e : (M : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hMne
  have hMeau : (M : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- `(max 1 (M c1⁻¹))⁻¹ ≤ (M c1⁻¹)⁻¹ = M⁻¹ c1` (inverses antitone)
  have hMcMax : (M * c1⁻¹ : NNReal) ≤ max 1 (M * c1⁻¹) := le_max_right _ _
  have hInv_le :
      (((max 1 (M * c1⁻¹) : NNReal) : ENNReal))⁻¹ ≤
        (((M * c1⁻¹ : NNReal) : ENNReal))⁻¹ := by
    exact ENNReal.inv_le_inv' (by exact_mod_cast hMcMax)
  have hMcinv : (((M * c1⁻¹ : NNReal) : ENNReal))⁻¹ = (M : ENNReal)⁻¹ * (c1 : ENNReal) := by
    calc
      ((M * c1⁻¹ : NNReal) : ENNReal)⁻¹
          = ((M : ENNReal) * ((c1⁻¹ : NNReal) : ENNReal))⁻¹ := by rw [ENNReal.coe_mul]
      _ = ((M : ENNReal) * (c1 : ENNReal)⁻¹)⁻¹ := by rw [ENNReal.coe_inv hc1ne]
      _ = (M : ENNReal)⁻¹ * ((c1 : ENNReal)⁻¹)⁻¹ := by
            rw [ENNReal.mul_inv (Or.inl hM0e) (Or.inl hMeau)]
      _ = (M : ENNReal)⁻¹ * (c1 : ENNReal) := by simp
  -- assemble
  calc
    ((max 1 (M * c1⁻¹) : NNReal) : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η)
        ≤ (((M * c1⁻¹ : NNReal) : ENNReal))⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) := by
            gcongr
    _ = (M : ENNReal)⁻¹ * (c1 : ENNReal) * (cfg.δ : ENNReal) ^ (65 * cfg.η) := by
            rw [hMcinv]
    _ ≤ (M : ENNReal)⁻¹ * (c1 : ENNReal) *
          ((a' : ENNReal) ^ (4 * (16 * cfg.η)) * (a' : ENNReal) ^ (16 * cfg.η / 256)) := by
            gcongr
    _ = (M : ENNReal)⁻¹ *
          ((c1 : ENNReal) * (a' : ENNReal) ^ (4 * (16 * cfg.η)) *
            (a' : ENNReal) ^ (16 * cfg.η / 256)) := by
            ac_rfl

/-- **The bodies almost fill a `θ b`-ball** (blueprint `lem:ml2transverseFill`).

In the situation of `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` — so `θ` is a typical
angle of intersection for the plank family `P` presenting `𝕎'_B`, and `(𝕎''_B, Y_{𝕎''_B})`,
here `((tc.thinBall hB).bodies', YW)`, is the `⪆ 1` refinement produced with it — the pair
`(𝕎''_B, Y_{𝕎''_B})` has a further `⪆ 1` refinement `(𝕎'''_B, Y_{𝕎'''_B})`, here
`((tc.thinBall hB).bodies', YW')`, and a ball of *some* radius `r ≥ θ b` in which that
refinement has density `⪆ δ^{5η}`:

`|U(𝕎'_B, Y_{𝕎'_B}) ∩ B_r| ≥ |U(𝕎'''_B, Y_{𝕎'''_B}) ∩ B_r| ⪆ δ^{5η} |B_r|`.

The first inequality of that display is the containment clause
`U(𝕎'''_B, Y_{𝕎'''_B}) ⊆ U(𝕎'_B, Y_{𝕎'_B})` below, which is the useful form: the mass-ball
step needs the shaded points themselves, not only their measure.

The blueprint states the conclusion for *every* ball meeting `U(𝕎'''_B, Y_{𝕎'''_B})`; what is
recorded here is the existence of one such ball, which is all that
`Kakeya.VeryNotSticky.transverseMassBall` consumes and which avoids carrying the
non-emptiness of the refined union — a clause that, at this level of the development, would
have to be re-derived from `Kakeya.ThinCase.ThinBall.fullness_bodies` through two refinements.

**What this declaration rests on.** Its content is the plank-to-slab reduction *at a prescribed
angle*,
`ShadedPlank.reduction_to_slab_atTypicalAngle` (blueprint
`lemmaredplanktubeAtTypicalAngle`), whose Lean statement lives in
`Kakeya/DimensionThree/Plank/Reduction.lean` and is itself an accepted Section 6 stub. It is
*not* `ShadedPlank.reduction_to_slab`: that statement binds its angle existentially and so
offers no way to run the reduction at the `θ` which `htyp` already carries — the Lean rendering
of GWZ Remark 6.14 (blueprint `typicalAngleAlreadyPresent`) is exactly the availability of the
at-angle statement, and the corollary is proved from it and not conversely.

The ingredients of the derivation that are *not* the reduction itself are separate proved
lemmas of this file, so that nothing but the reduction and its inputs remains here:
`Kakeya.VeryNotSticky.transverseFillTransport` (blueprint
`lem:ml2transverseFillTransport`) performs the ball bookkeeping that turns Item 1 of the
reduction, transported to the original coordinates, into the display below at a radius
`r ≥ θ b`; and `Kakeya.VeryNotSticky.transverseFillConstantBound` (blueprint
`lem:ml2transverseFillConstantBound`) turns the constant so assembled into the sub-polynomial
bound `Cfill ≤ δ^{-η}` asserted below. The rescaling bridge itself is the last clause of
`Kakeya.VeryNotSticky.plankPresentation`.

One hypothesis of the reduction that a freely given plank family cannot supply is
now carried here, `hwin`, and it comes from
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`, which passes it through from
`Kakeya.VeryNotSticky.plankPresentation`. An essential-distinctness clause `hPed` was carried
beside it until R26 deleted that field. In particular the windowedness is stated at
`Plank.windowRadius`, the radius `reduction_to_slab` itself asks for: this is why
`Kakeya.VeryNotSticky.plankBallRadius` is defined from `Plank.windowRadius` rather than
chosen independently, an earlier version having localized the planks at the larger radius `5`,
which would not have discharged `Plank.IsWindowedFamily` at all.

Similarly `hCtyp` bounds the typicality constant. Without it `htyp` and `hconst` are vacuous —
both predicates weaken as their constant grows, and `Ctyp` is a free variable here — so the
lemma would not merely be unproved but unprovable; it is supplied, together with `htyp` and
`hconst`, by `exists_isTypicalAnglePlank`. Its companion `hCtyp1 : 1 ≤ Ctyp` is not used here
at all: it is carried only so that this statement's binders remain, field for field, those of
`Kakeya.VeryNotSticky.TypicalAngleData`, which
`Kakeya.VeryNotSticky.transverseMassBall` reassembles as a bundle when it calls
`Kakeya.VeryNotSticky.transverseFill`. The tangential leaf is where it is spent, in
`Kakeya.VeryNotSticky.tangentialSlabFibreCount`.

The bound carried is the *sharp* form `typicalAngleConstantBoundSharp`,
`Ctyp ≤ (δ')^{-η/256}` at the rescaled scale `δ' = δ/r₁ = δ^{1-exscal}`, and not the weaker
`Ctyp ≤ δ^{-η}`. That is the form `ShadedPlank.reduction_to_slab_atTypicalAngle` asks for
(blueprint `redPlankTubeAtAngleConstantBound`): it wants its
constant-bound hypothesis at the `ε` of the application, and by the exponent gap `128ε ≤ ε'`,
with `ε' = η/2` fixed by the sixth clause
`Kakeya.VeryNotSticky.CaseScale.transverse_fill`, that `ε` is at most `ε'/2 = η/256`; a
hypothesis at `δ^{-η}` would not discharge it, and with it the chain would not close, since
`c₁⁻¹` is bounded below by a quantity comparable to `Ctyp` and `Cfill ≤ δ^{-η}` would fail.
The obligation this places on the producer `exists_isTypicalAnglePlank` is left there, as the
blueprint prescribes, rather than discharged by weakening the binder here.

**What is in hand.** Three items that earlier versions of this note listed as gaps are gaps no
longer. The fullness `(a')^η ≤ λ(𝒫, Y_𝒫)` (blueprint `transverseFillFullness`) is the field
`Kakeya.VeryNotSticky.TypicalAngleData.hfullP`, an honest input traced to obligation O5 of
Configuration `hyp:ml2thinsetup` and delivered by the clause
`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`; the `ShadedPlank` packaging is the
field `Kakeya.VeryNotSticky.TypicalAngleData.SP`; and the plank-coordinate shading `Y''_𝒫` is
the field `Kakeya.VeryNotSticky.TypicalAngleData.YP`. Item (a) of the closing note of the
blueprint subsubsection, the prescribed-angle statement itself, is
`ShadedPlank.reduction_to_slab_atTypicalAngle`. So every hypothesis of blueprint
`lem:ml2transverseFillPlankHyps` is available, one for one, in the form in which the eleventh
clause `Kakeya.VeryNotSticky.CaseScale.transverseFill_threshold` packages the reduction, namely
`Kakeya.VeryNotSticky.IsReductionFillAvailable` at the rescaled scale `δ' = δ/r₁`, and the
clauses below are reachable from it: the two bounds on `Cfill`, by
`Kakeya.VeryNotSticky.transverseFillConstantBound`; and the containment together with the ball
estimate, by `Kakeya.VeryNotSticky.TypicalAngleData.hbridgeP0` followed by
`Kakeya.VeryNotSticky.transverseFillTransport`.

**What the fifth clause needed, and where it came from.** The refinement clause asks
`(𝕎'''_B, Y_{𝕎'''_B})` to be a `⪆ 1` refinement of `(𝕎''_B, Y_{𝕎''_B})`, that is, of
`ta.YW`. The only rescaling bridge whose output lands inside the shades of `ta.YW` is
`Kakeya.VeryNotSticky.TypicalAngleData.hbridgeP`, and it consumes a subfamily of the *refined*
plank shading `Y''_𝒫 = ta.YP`. A refinement of the *base* plank family alone,
`ShadedBody.IsRefinement s' Y' 𝕊* (ShadedPlank.bodies SP)`, does not fit it: `ta.YP` is
likewise a refinement of `ShadedPlank.bodies SP`, so nothing would relate the two subfamilies
of `U(𝒫, Y_𝒫)` to each other. The bridge that a base refinement does fit, `hbridgeP0`, lands
at the unrefined `Y_{𝕎'_B}`, which is enough for the containment and for the ball estimate but
cannot give a refinement of `ta.YW`.

What supplies it is a clause of the Section 6 statement, true of GWZ Lemma 6.13 as proved
there: the family that lemma produces refines the *prescribed* shading `Y''`, not merely the
base `Y`, the further refinement being taken inside `Y''`. That clause,
`ShadedBody.IsRefinement s' Y' s Y''`, is now part of the conclusion of
`ShadedPlank.reduction_to_slab_atTypicalAngle` and of
`Kakeya.VeryNotSticky.IsReductionFillAvailable`. With it `U(𝒫', Y') ⊆ U(𝒫, Y''_𝒫)`, so the
almost-filling estimate passes to `U(𝒫, Y''_𝒫)` by monotonicity, `hbridgeP` applies at
`t = 𝕊*`, `Z = ta.YP` and `c₂ = 1`, and all five clauses close, with `c' = 1`.

Two smaller repairs were made at the same time and for the same reason, that a clause the
argument reads was not in the statement it reads it from. `IsReductionFillAvailable` now also
concludes `(iUnionShade s' Y').Nonempty`: Item 1 fires only at a ball meeting `U(𝒫', Y')`, and
without a lower bound on the output family `s' = ∅` would satisfy the predicate vacuously, so
the guard could never be discharged; the clause follows from the fullness of the output, which
the full reduction supplies, and is derived there in
`Kakeya.VeryNotSticky.exists_isReductionFillAvailable`. And
`Kakeya.VeryNotSticky.transverseFillTransport` now asks for `t ≤ C₀ ρ` rather than
`t ≤ 3 C₀⁻¹ ρ`: what `ta.hb'lower` supplies is `r₁ b' ≥ C₀⁻¹ b`, hence `θ b ≤ C₀ ρ`, which is
weaker than the old hypothesis as soon as `C₀ > √3`. The factor paid is unchanged, since the
proof of that lemma needs only `t ≤ max(1, C₀/3) · 3ρ` and `3 max(1, C₀/3) = max(3, C₀) ≥ C₀`.

**The proof is split in three.** `Kakeya.VeryNotSticky.transverseFillPlankEstimate` discharges
the hypotheses of the reduction from the fields of `ta`, fires Item 1 and moves it to
`U(𝒫, Y''_𝒫)`; `Kakeya.VeryNotSticky.transverseFillDensityBound` is the comparison of the two
density budgets, where the exponent `5η` below is paid for; what remains here is the rescaling
bridge, the transport and the assembly of the five clauses.

One item that used to be listed here has been removed, because it is not a gap at all. The
smallness hypothesis of the reduction is a threshold on the *scale* and
not on `a'`, so it is discharged outright by the eleventh clause
`Kakeya.VeryNotSticky.CaseScale.transverseFill_threshold`, which arrives with `scale` and costs
this declaration no binder.

Two features of the display are forced by that source.

* The *exponent is* `5η`. Item 1 of `ShadedPlank.reduction_to_slab_atTypicalAngle` reads
  `c₁ a^{4η} a^{ε} |B̄(x, θ b')| ≤ |U(𝒫', Y') ∩ B̄(x, 3 θ b')|`, with `ε > 0` free but fixed and
  the dilation factor `ShadedPlank.redPlankTube.ballDilation = 3`. The branch applies it at
  `ε = η/256`, the largest value the exponent gap `128ε ≤ ε' = η/2` permits — and, by the sharp
  typicality bound discussed above, the value it is *forced* to. Since `a ≤ 1` and
  `ε = η/256 ≤ η`, one has `a^{4η + ε} ≥ a^{5η}`, so the budget is `5η`; this is an inequality and
  not an identity, and it would still read `5η` at any `ε ≤ η`. The earlier `3η` is *not*
  recoverable: `a^{4η+ε} ≤ a^{3η}` for `a ≤ 1`, and no
  constant may absorb `a^{-η}` without depending on the scale. The dilation is harmless — it
  changes the reference volume by `3³`, absorbed into `Cfill`. Accordingly the chain reaches
  `3τ + 7η` at `Kakeya.VeryNotSticky.transverseBallFill` (the transfer at the `tb` index `2η`,
  F8), and `Kakeya.VeryNotSticky.CaseParams.transverse` carries `3τ + 12η < τ' β`, which pays
  the further `3η` of the absorption split and still leaves the `2η` reserved for the passage
  to an
  admissible radius.
* The *radius is existentially quantified*. Item 1 lives at the radii `θ b'` and `3 θ b'` of the
  rescaled coordinates of blueprint `lem:ml2plankpresentation`, and the rescaling bridge
  transports it back with no loss in the ratio `K`, but only up to the comparison constant
  `bd.C₀` of (C4) in the *radius*: `r₁ b' ∈ [C₀⁻¹ b, C₀ b]`. So the produced radius is
  comparable to `θ b`, not equal to it, and an almost-filling estimate cannot be moved to a
  *smaller* radius. Consumers need the lower bound `θ b ≤ r`: it supplies the transfer-radius
  bound `r / 2 ≥ 3A` of `Kakeya.VeryNotSticky.transverseMassBall`, the lower bound
  `r ≥ δ^{1-τ'}` of `Kakeya.VeryNotSticky.transverseDensity`, and the admissibility `r ≥ a` of
  `Kakeya.VeryNotSticky.exists_aScaleData`. Enlarging the produced radius to `max(r, θ b)`
  costs a bounded factor, absorbed into `Cfill`.

  They also need the *upper* bound `r ≤ 1`, the second half of the radius hypothesis of
  blueprint `lem:ml2aScaleData`. It is asserted here rather than left to the consumer, because
  `r` is quantified existentially and no later statement could assume it; it is
  `Kakeya.VeryNotSticky.transverseFillRadius_le_one`, and it costs no new fixed-scale
  assumption, spending the sixth clause `Kakeya.VeryNotSticky.CaseScale.transverse_fill` a
  second time. Without it the transverse branch cannot invoke
  `Kakeya.VeryNotSticky.exists_aScaleData` at all, that statement being refutable at radii
  above `1`.

**A note on coordinates.** `htyp` pairs the *original-coordinate* shading `YW` on
`(tc.thinBall hB).bodies'` with the *rescaled* plank family `P`, whereas the blueprint states
typicality entirely in the rescaled coordinates of `lem:ml2plankpresentation`. This is not a
coordinate error; the two formulations are equivalent. `Kakeya.IsTypicalPlankAngle` sees the
shading only through `ShadedBody.shadeFibre`, i.e. through which *indices* shade a given point,
and the affine map `L_B` of `Kakeya.VeryNotSticky.plankPresentation` is a bijection carrying the
fibres of the rescaled shading onto those of `YW` index for index; the angles are read off `P`
alone, and `L_B`, a homothety followed by a translation, preserves them. Keeping the pair in
this mixed form is what lets the conclusion below speak about `(tc.thinBall hB).bodies'` and
`cfg.b` directly rather than about their rescalings.

The comparison constant `Cfill` is produced rather than defined: `ShadedPlank.reduction_to_slab`
supplies its `c₁` existentially, ahead of the family, and there is no formula for it. That it
does not depend on `cfg.δ` — which is what makes the fixed-scale threshold of
`Kakeya.VeryNotSticky.transverseDensity` achievable — is a further absorbed obligation, of the
same kind as obligation (e) of `Kakeya.VeryNotSticky.exists_denseInBody`.

**The sub-polynomial bound `Cfill ≤ δ^{-η}`** (blueprint `transverseFillConstantBound`) is
asserted alongside the ball estimate, and it is there for the reason every such bound in this
subsection is: `Cfill` is produced *after* `δ` has been fixed, so at one fixed scale a bare
`1 ≤ Cfill < ∞` says nothing quantitative about it, and no later statement can assume a
smallness hypothesis about a constant this one quantifies existentially. The only place a
bound on it can appear is the conclusion that produces it. It is what
`Kakeya.VeryNotSticky.transverseMassBall` and then
`Kakeya.VeryNotSticky.transverseBallFill` propagate into the bound on `Cbf` that
`Kakeya.VeryNotSticky.goalMult_of_theta_ge` needs in order to discharge the absorption
hypothesis of `Kakeya.VeryNotSticky.exists_aScaleData`. Its two halves are the sixth clause
`Kakeya.VeryNotSticky.CaseScale.transverse_fill`, which pays at `η/2` for the `3³` and the
`max(1, C₀/3)³` that the argument discards, and the `δ^{-η/2}` that Section 6 supplies with
Item 5 of `ShadedPlank.reduction_to_slab_atTypicalAngle` (blueprint
`redPlankTubeConstantBound`); both arrive with `scale` and with that item, and neither costs
this declaration a binder of its own. The arithmetic that combines them is already carried
out, in `Kakeya.VeryNotSticky.transverseFillConstantBound`, so no part of that accounting
remains here.

**The plank data travels in `ta`.** The binders
`sel, hsel, a', b', hab', hb1', P, YW, θ, c, Ctyp, hratio, hθab, hθ1, hwin, hc,
hrefine, hfull, hCtyp1, hCtyp, hconst, htyp` an earlier version listed are, field for field, the
fields of `Kakeya.VeryNotSticky.TypicalAngleData`, the bundle
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` returns and the sibling leaf
`Kakeya.VeryNotSticky.goalMult_of_theta_ge` already takes; they are received here as that
bundle instead. Nothing is weakened by the change — each of the three clauses argued for above
(`hwin`, `hCtyp`, `hfull`) is a field of `ta` and is still a hypothesis of this
statement — and the signature drops from twenty-two binder groups to eight. A fourth clause,
the essential distinctness `hPed`, was argued for here and carried by `ta` until R26 deleted the
field; `ShadedPlank.reduction_to_slab` no longer asks for it. Where the `a'/b'`
reading of the angle clause is wanted it is `ta.hθab`, and where the `a/b` reading is wanted
it is `ta.hθab'`. The transverse-case hypothesis `htrans` (GWZ l.2224) is passed to
`Kakeya.VeryNotSticky.transverseFillPlankEstimate`, where it unlocks the guarded fullness
clause `ta.hfullP`. -/
theorem transverseFill (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (_hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    {νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (ta : TypicalAngleData cfg tc hB τ')
    (htrans : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ ta.θ) :
    ∃ (Cfill c' r : NNReal) (YW' : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      1 ≤ Cfill ∧ Cfill ≤ cfg.δ ^ (-(9 * cfg.η)) ∧ cfg.δ ^ (2 * cfg.η) ≤ c' ∧
      ShadedBody.IsCRefinement ta.sel YW' ta.sel ta.YW c' ∧
      iUnionShade ta.sel YW' ⊆ (tc.thinBall hB).UW ∧
      ta.θ * cfg.b ≤ r ∧ r ≤ 1 ∧ r ≤ 6 * cfg.δ ^ cfg.exscal ∧
      ∃ x : EuclideanSpace ℝ (Fin 3),
        (Cfill : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) *
            volume (ball x (r : ℝ)) ≤
          volume (iUnionShade ta.sel YW' ∩ ball x (r : ℝ)) := by
  -- (A) the plank-to-slab reduction at the rescaled scale, as the separate lemma
  have hr₁pos : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hδr : cfg.δ / cfg.r₁ = cfg.δ ^ (1 - cfg.exscal) := by
    rw [show cfg.r₁ = cfg.δ ^ cfg.exscal by rfl]
    simpa [NNReal.rpow_one] using (NNReal.rpow_sub cfg.hδ.ne' 1 cfg.exscal).symm
  rcases transverseFillPlankEstimate cfg scale ta htrans with ⟨c1, p, hc1pos, hc1, h1cont⟩
  -- (B) the refined plank rescaling bridge, `c₂ := 1`, `t := sel`, `Z := YP`
  rcases (ta.hbridgeP (c₂ := 1) (t := ta.sel) (Z := ta.YP)
      (by rfl) (by intro i hi; exact subset_rfl) (by simp)) with ⟨YW', hrefine', hsubYW, htrans⟩
  let K : ENNReal :=
    (c1 : ENNReal) * (ta.a' : ENNReal) ^ (4 * (16 * cfg.η)) *
      (ta.a' : ENNReal) ^ (16 * cfg.η / 256)
  have h1K : K * volume (Metric.closedBall p ((ta.θ * ta.b' : NNReal) : ℝ)) ≤
      volume (ShadedBody.iUnionShade ta.sel ta.YP ∩
        Metric.closedBall p
          ((ShadedPlank.redPlankTube.ballDilation * ta.θ * ta.b' : NNReal) : ℝ)) := by
    dsimp [K]
    exact h1cont
  rcases htrans p ((ta.θ * ta.b' : NNReal) : ℝ)
      ((ShadedPlank.redPlankTube.ballDilation * ta.θ * ta.b' : NNReal) : ℝ) K h1K with ⟨x, hx⟩
  -- (C) transport to a single radius `r ≥ θ b`
  let ρ : ℝ := 2 * (cfg.r₁ : ℝ) * ((ta.θ * ta.b' : NNReal) : ℝ)
  have hρ0 : 0 ≤ ρ := by positivity
  have hxρ : K * volume (ball x ρ) ≤
      volume (ShadedBody.iUnionShade ta.sel YW' ∩ ball x (3 * ρ)) := by
    have hf : ShadedPlank.redPlankTube.ballDilation = (3 : NNReal) := rfl
    have hrad1 : 2 * (cfg.r₁ : ℝ) * ((ta.θ * ta.b' : NNReal) : ℝ) = ρ := rfl
    have hrad3 :
        2 * (cfg.r₁ : ℝ) *
            ((ShadedPlank.redPlankTube.ballDilation * ta.θ * ta.b' : NNReal) : ℝ) =
          3 * ρ := by
      dsimp [ρ]
      rw [hf]
      norm_num [NNReal.coe_mul]
      ring
    rw [hrad1] at hx
    rw [hrad3] at hx
    exact hx
  have hcomp : (ta.θ * cfg.b : NNReal) ≤ (bd.C₀ : ℝ) * ρ := by
    have hC₀pos : 0 < bd.C₀ := lt_of_lt_of_le (by norm_num) bd.hC₀
    have hb'lower' : cfg.b / (bd.C₀ * cfg.r₁) ≤ ta.b' := by
      simpa [div_eq_inv_mul, mul_comm, mul_assoc, mul_left_comm, one_div] using ta.hb'lower
    have hb' : cfg.b ≤ bd.C₀ * cfg.r₁ * ta.b' := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using
        ((div_le_iff₀ (mul_pos hC₀pos hr₁pos)).mp hb'lower')
    have hθb' : ta.θ * cfg.b ≤ bd.C₀ * cfg.r₁ * (ta.θ * ta.b') := by
      calc
        ta.θ * cfg.b ≤ ta.θ * (bd.C₀ * cfg.r₁ * ta.b') := by
          gcongr
        _ = bd.C₀ * cfg.r₁ * (ta.θ * ta.b') := by ring
    have hθb'ℝ : ((ta.θ * cfg.b : NNReal) : ℝ) ≤
        ((bd.C₀ * cfg.r₁ * (ta.θ * ta.b') : NNReal) : ℝ) := by
      exact_mod_cast hθb'
    have hmid : ((bd.C₀ * cfg.r₁ * (ta.θ * ta.b') : NNReal) : ℝ) ≤ (bd.C₀ : ℝ) * ρ := by
      have hle : (cfg.r₁ : ℝ) * ((ta.θ * ta.b' : NNReal) : ℝ) ≤
          2 * (cfg.r₁ : ℝ) * ((ta.θ * ta.b' : NNReal) : ℝ) := by
        have hpos : (0 : ℝ) ≤ (cfg.r₁ : ℝ) * ((ta.θ * ta.b' : NNReal) : ℝ) := by
          positivity
        nlinarith
      have hcast : ((bd.C₀ * cfg.r₁ * (ta.θ * ta.b' : NNReal) : NNReal) : ℝ) =
          (bd.C₀ : ℝ) * ((cfg.r₁ : ℝ) * ((ta.θ * ta.b' : NNReal) : ℝ)) := by
        norm_num [NNReal.coe_mul]
        ring
      rw [hcast]
      dsimp [ρ]
      exact mul_le_mul_of_nonneg_left hle (NNReal.coe_nonneg bd.C₀)
    exact le_trans hθb'ℝ hmid
  rcases transverseFillTransport hρ0 hcomp (ShadedBody.iUnionShade ta.sel YW') x K hxρ with
    ⟨r, htr, hrmax, htrans2⟩
  -- (D) assemble the output bundle
  let M : NNReal := max 1 (bd.C₀ / 3)
  let Cfill : NNReal := max 1 (27 * M ^ 3 * c1⁻¹)
  let c' : NNReal := 1
  let Kinv : ENNReal := ((27 * M ^ 3 : NNReal) : ENNReal)⁻¹
  have h1Cf : 1 ≤ Cfill := by dsimp [Cfill]; exact le_max_left _ _
  have h2Cf : Cfill ≤ cfg.δ ^ (-(9 * cfg.η)) := by
    dsimp [Cfill, M]
    exact transverseFillConstantBound cfg scale hc1
  have h3c : cfg.δ ^ (2 * cfg.η) ≤ c' := by
    dsimp [c']
    exact NNReal.rpow_le_one cfg.hδ1 (mul_nonneg (by norm_num) cfg.hη.le)
  have h4c : ShadedBody.IsCRefinement ta.sel YW' ta.sel ta.YW c' := by
    dsimp [c']
    exact hrefine'
  have h5c : ShadedBody.iUnionShade ta.sel YW' ⊆ (tc.thinBall hB).UW := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxsh⟩
    change x ∈ ShadedBody.iUnionShade (tc.thinBall hB).bodies' (tc.thinBall hB).W
    exact Set.mem_iUnion₂.mpr ⟨i, ta.hsel hi,
      ((ta.hrefine.1.2 i hi).2) ((hsubYW i hi) hxsh)⟩
  have h6c : ta.θ * cfg.b ≤ r := by exact_mod_cast htr
  have h7c : r ≤ 1 :=
    transverseFillRadius_le_one cfg params scale ta.hθ1 ta.hb1' hrmax
  have h7d : r ≤ 6 * cfg.δ ^ cfg.exscal :=
    transverseFillRadius_le_six_rpow_exscal cfg ta.hθ1 ta.hb1' hrmax
  -- the coefficient: `(Cfill)⁻¹ · δ^{65η} ≤ Kinv · K` by the density bound
  have ha' : cfg.δ ^ (1 - cfg.exscal) ≤ ta.a' := by
    simpa [hδr] using ta.hδa'
  have hcoef : (Cfill : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) ≤ Kinv * K := by
    have hd := transverseFillDensityBound cfg (C₀ := bd.C₀) (a' := ta.a') (c1 := c1) ha' hc1pos
    dsimp [Cfill, M, Kinv, K] at hd ⊢
    exact hd
  have htrans2' : Kinv * K * volume (ball x (r : ℝ)) ≤
      volume (ShadedBody.iUnionShade ta.sel YW' ∩ ball x (r : ℝ)) := by
    simpa [Kinv, M] using htrans2
  refine ⟨Cfill, c', r, YW', h1Cf, h2Cf, h3c, h4c, h5c, h6c, h7c, h7d, x, ?_⟩
  calc
    (Cfill : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) * volume (ball x (r : ℝ))
        ≤ Kinv * K * volume (ball x (r : ℝ)) := by gcongr
    _ ≤ volume (iUnionShade ta.sel YW' ∩ ball x (r : ℝ)) := htrans2'

/-! ### Step 2: a transfer ball carrying a proportional share of the mass -/

/-- **A transfer ball carrying a proportional share of the mass** (blueprint
`lem:ml2transverseMassBall`).

In the transverse case `θ ≥ δ^{-τ'} a/b`, the transfer radius `ρ = r / 2` at the radius
`r ≥ θ b` of `Kakeya.VeryNotSticky.transverseFill` exceeds the covering radius `3A` of
blueprint `def:ml2thinW1Constant`, and there is a ball of that radius in which
`U(𝕎'_B, Y_{𝕎'_B})` still has density `⪆ δ^{5η}`.

The set `S = U(𝕎'''_B, Y_{𝕎'''_B}) ∩ B(x, r)` supplied by
`Kakeya.VeryNotSticky.transverseFill` lies in a ball of radius `r = 2ρ`, so
`Kakeya.exists_mem_volume_inter_ball_ge` (blueprint `lem:massSubball`) applies with `K = 2`
and produces a point `y ∈ S` with
`|S ∩ B(y, ρ)| ≥ c_{lem:massSubball}(3, 2) |S| = 5^{-3}|S|`. The estimate is then pushed up
to `U(𝕎'_B, Y_{𝕎'_B})` by the containment clause of `transverseFill`, and `|B(y, ρ)|` is
bounded by `|B(x, r)|` because `ρ ≤ r` and the volume of a ball depends only on its radius.

The radius `r` is passed on to the consumers, together with `θ b ≤ r`: the transfer-radius
inequality `3A ≤ r / 2` is `Kakeya.VeryNotSticky.transverseRadius_ge` at `θ b` composed with
that bound, and it is the one place where the transverse hypothesis `htrans` and the
fixed-scale threshold `hsmall` are spent.

The hypothesis `hsmall` is the fixed-scale threshold `δ^{-τ'} ≥ 6 C_{w₁}(C₀)`, the field
`Kakeya.VeryNotSticky.CaseScale.transverse_radius`; the blueprint states it as "once `δ` is
small enough" inside the proof, and it is carried as a separate hypothesis here so that this
lemma is unconditional in `δ`.

As in `transverseFill`, the constant `Cmass = 5³ Cfill` is produced rather than defined,
because `Cfill` is. Its sub-polynomial bound `Cmass ≤ 5³ δ^{-η}` is the bound
`Cfill ≤ δ^{-η}` of `Kakeya.VeryNotSticky.transverseFill` multiplied by the explicit factor
`5³ = c_{lem:massSubball}(3,2)⁻¹`; that factor is *not* absorbed here, but is paid for one
step later, by the seventh clause `Kakeya.VeryNotSticky.CaseScale.transverse_ballFill`,
which carries the whole product `2³ · 5³ = 1000` together with the transfer constant. -/
theorem transverseMassBall (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    {νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (ta : TypicalAngleData cfg tc hB τ')
    (htrans : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ ta.θ)
    (hsmall : 6 * ThinCase.w1Constant bd.C₀ ≤ cfg.δ ^ (-τ')) :
    ∃ Cmass r : NNReal, 1 ≤ Cmass ∧ Cmass ≤ 125 * cfg.δ ^ (-(9 * cfg.η)) ∧ ta.θ * cfg.b ≤ r ∧
      r ≤ 1 ∧ r ≤ 6 * cfg.δ ^ cfg.exscal ∧
      3 * ((ThinCase.rad bd.C₀ cfg.a : NNReal) : ℝ) ≤ (r : ℝ) / 2 ∧
      ∃ y : EuclideanSpace ℝ (Fin 3),
        (Cmass : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) *
            volume (ball y ((r : ℝ) / 2)) ≤
          volume ((tc.thinBall hB).UW ∩ ball y ((r : ℝ) / 2)) := by
  · -- the plank data travels in the bundle `ta`, which is what `transverseFill` takes
    set sel := ta.sel with hseldef
    set θ := ta.θ with hθdef
    rcases transverseFill cfg params hnotslab tc hB scale ta htrans with
      ⟨Cfill, c', r, YW', hCfill, hCfillbd, hc', hrefine', hsub, hθbr, hr1, hr6, x, hx⟩
    have hsub : iUnionShade sel YW' ⊆ (tc.thinBall hB).UW := hsub
    have hθbr : θ * cfg.b ≤ r := hθbr
    have hx : (Cfill : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) *
        volume (ball x (r : ℝ)) ≤ volume (iUnionShade sel YW' ∩ ball x (r : ℝ)) := hx
    let R : ℝ := (r : ℝ)
    let ρ : ℝ := R / 2
    let S : Set (EuclideanSpace ℝ (Fin 3)) := iUnionShade sel YW' ∩ ball x R
    let δpow : ENNReal := (cfg.δ : ENNReal) ^ (65 * cfg.η)
    have hτ'pos : 0 < τ' := lt_trans params.hτ params.hτ'
    -- the four lower bounds for the transverse radius (blueprint `lem:ml2transverseRadiusLower`)
    obtain ⟨-, -, -, hθbpos⟩ := transverseRadiusLower cfg hτ'pos θ htrans
    have hθbR : ((θ * cfg.b : NNReal) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hθbr
    have hradR : 3 * ((ThinCase.rad bd.C₀ cfg.a : NNReal) : ℝ) ≤ (r : ℝ) / 2 := by
      have h : 3 * ThinCase.rad bd.C₀ cfg.a ≤ r / 2 :=
        le_trans (transverseRadius_ge cfg bd hτ'pos θ htrans hsmall) (by gcongr)
      exact_mod_cast h
    have hRpos : 0 < R := by
      have hrpos : (0 : NNReal) < r := lt_of_lt_of_le hθbpos hθbr
      dsimp [R]
      exact_mod_cast hrpos
    have hρpos : 0 < ρ := by
      dsimp [ρ]
      positivity
    have hSne : S.Nonempty := by
      have hCf_ne_top : (Cfill : ENNReal) ≠ ⊤ := by exact ENNReal.coe_ne_top
      have hδe_ne_top : (cfg.δ : ENNReal) ≠ ⊤ := by exact ENNReal.coe_ne_top
      have hδe_pos : 0 < (cfg.δ : ENNReal) := by exact_mod_cast cfg.hδ
      have hδrpow_ne0 : δpow ≠ 0 := by
        dsimp [δpow]
        exact (ENNReal.rpow_pos hδe_pos hδe_ne_top).ne'
      have hvolR_ne0 : volume (ball x R) ≠ 0 := (Metric.measure_ball_pos volume x hRpos).ne'
      have hprod_ne0 : (Cfill : ENNReal)⁻¹ * δpow * volume (ball x R) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hCf_ne_top) hδrpow_ne0) hvolR_ne0
      have hSvol_pos : 0 < volume S := by
        have hLpos : 0 < (Cfill : ENNReal)⁻¹ * δpow * volume (ball x R) :=
          pos_iff_ne_zero.mpr hprod_ne0
        exact lt_of_lt_of_le hLpos hx
      exact MeasureTheory.nonempty_of_measure_ne_zero (ne_of_gt hSvol_pos)
    rcases exists_mem_volume_inter_ball_ge (S := S) hSne (ρ := ρ) hρpos (K := (2 : NNReal))
        (by norm_num : (1 : NNReal) ≤ 2) x (by exact Set.inter_subset_right)
        (by
          dsimp [ρ]
          exact le_of_eq (by ring : (2 : ℝ) * (R / 2) = R).symm) with ⟨y, hyS, hy⟩
    have hy125 : (125 : ENNReal)⁻¹ * volume S ≤ volume (S ∩ ball y ρ) := by
      norm_num [massSubballConstant, finrank_euclideanSpace_fin, ENNReal.coe_inv] at hy ⊢
      exact hy
    have hyvol : volume (ball y ρ) ≤ volume (ball x R) := by
      calc
        volume (ball y ρ) = volume (ball (0 : EuclideanSpace ℝ (Fin 3)) ρ) := by
          rw [MeasureTheory.Measure.addHaar_ball_center volume y ρ]
        _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 3)) R) := by
          apply measure_mono
          exact Metric.ball_subset_ball (by dsimp [ρ]; linarith)
        _ = volume (ball x R) := by
          rw [MeasureTheory.Measure.addHaar_ball_center volume x R]
    let Cmass : NNReal := 125 * Cfill
    have hCfill_nonneg : (0 : NNReal) ≤ Cfill := by positivity
    have hCmass_le : 1 ≤ Cmass := by
      dsimp [Cmass]
      calc
        (1 : NNReal) ≤ Cfill := hCfill
        _ ≤ Cfill * 125 := le_mul_of_one_le_right hCfill_nonneg (by norm_num : (1 : NNReal) ≤ 125)
        _ = 125 * Cfill := by rw [mul_comm]
    have hCmass_inv : (Cmass : ENNReal)⁻¹ = (125 : ENNReal)⁻¹ * (Cfill : ENNReal)⁻¹ := by
      have hCmass' : (Cmass : ENNReal) = (125 : ENNReal) * (Cfill : ENNReal) := by
        dsimp [Cmass]
      rw [hCmass']
      rw [ENNReal.mul_inv (Or.inr (by exact ENNReal.coe_ne_top))
        (Or.inl (by norm_num : (125 : ENNReal) ≠ ⊤))]
    have hmid : (Cfill : ENNReal)⁻¹ * δpow * volume (ball y ρ) ≤
        (Cfill : ENNReal)⁻¹ * δpow * volume (ball x R) := by
      gcongr
    have hmid2 : (Cfill : ENNReal)⁻¹ * δpow * volume (ball y ρ) ≤ volume S :=
      le_trans hmid hx
    have hstep : (125 : ENNReal)⁻¹ * ((Cfill : ENNReal)⁻¹ * δpow * volume (ball y ρ)) ≤
        (125 : ENNReal)⁻¹ * volume S := by
      gcongr
    have hleft : (Cmass : ENNReal)⁻¹ * δpow * volume (ball y ρ) =
        (125 : ENNReal)⁻¹ * ((Cfill : ENNReal)⁻¹ * δpow * volume (ball y ρ)) := by
      rw [hCmass_inv]
      ac_rfl
    have hmain : (Cmass : ENNReal)⁻¹ * δpow * volume (ball y ρ) ≤
        volume ((tc.thinBall hB).UW ∩ ball y ρ) := by
      calc
        (Cmass : ENNReal)⁻¹ * δpow * volume (ball y ρ)
            ≤ (125 : ENNReal)⁻¹ * ((Cfill : ENNReal)⁻¹ * δpow * volume (ball y ρ)) := by
                exact le_of_eq hleft
        _ ≤ (125 : ENNReal)⁻¹ * volume S := hstep
        _ ≤ volume (S ∩ ball y ρ) := hy125
        _ ≤ volume ((tc.thinBall hB).UW ∩ ball y ρ) := by
                apply measure_mono
                have hS_UW : S ⊆ (tc.thinBall hB).UW := by
                  dsimp [S]
                  exact Set.Subset.trans (Set.inter_subset_left) hsub
                exact Set.inter_subset_inter hS_UW (subset_rfl)
    have hCmass_bd : Cmass ≤ 125 * cfg.δ ^ (-(9 * cfg.η)) := by
      dsimp [Cmass]
      gcongr
    refine ⟨Cmass, r, hCmass_le, hCmass_bd, hθbr, hr1, hr6, hradR, ⟨y, ?_⟩⟩
    simpa [ρ, R, δpow] using hmain

/-! ### Step 3: the filling transfers to the tube segments -/

/-- Doubling the radius of a ball in `ℝ³` multiplies its volume by `2³ = 8`.

This is the numerical content of the blueprint's remark that "the doubling of the radius costs
nothing, because `|B(y,ρ)| ∼ |B_{θb}|`": `Kakeya.ThinCase.transfer_thin` concludes at the ball
of radius `2ρ` while the mass it consumes sits in the ball of radius `ρ`, so the reference
volume changes by exactly this factor.

It is an *equality*, `|B(y,2r)| = 2³|B(y,r)|`, and is proved as one: Lebesgue measure on `ℝ³`
is an additive Haar measure, so `MeasureTheory.Measure.addHaar_ball_mul` scales the radius by
the factor `2^{dim} = 2³`, the dimension being `3` by `finrank_euclideanSpace_fin`, and
`MeasureTheory.Measure.addHaar_ball_center` removes the centre. It is *stated* as an
inequality, which is the direction `Kakeya.VeryNotSticky.transverseBallFill` uses. The
blueprint asks only for `r ≥ 0`; no such hypothesis is needed, since at `r < 0` both balls are
empty. -/
theorem volume_ball_two_mul_le (y : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    volume (ball y (2 * r)) ≤ 8 * volume (ball y r) := by
  refine le_of_eq ?_
  rw [MeasureTheory.Measure.addHaar_ball_mul volume y (by norm_num : (0 : ℝ) ≤ 2) r,
    MeasureTheory.Measure.addHaar_ball_center volume y r,
    finrank_euclideanSpace_fin (𝕜 := ℝ)]
  norm_num

/-- **The ball-filling constant is sub-polynomial** (blueprint
`lem:ml2transverseBallFillConstantBound`, equation `transverseBallFillConstantBound`).

The constant of `Kakeya.VeryNotSticky.transverseBallFill` is
`Cbf = 2³ C_{lem:ml2thinTransfer}(tc.C, bd.C₀) Cmass`, and `Cmass = 5³ Cfill`, so that
`Cbf = (2³ · 5³ C_{lem:ml2thinTransfer}(tc.C, bd.C₀)) Cfill`. The first factor is at most
`δ^{-η}` by the seventh clause `Kakeya.VeryNotSticky.CaseScale.transverse_ballFill`, which
carries the whole product `1000 C_{lem:ml2thinTransfer}`, and the second at most `δ^{-η}` by
`Kakeya.VeryNotSticky.transverseFill`, propagated through
`Kakeya.VeryNotSticky.transverseMassBall` as the hypothesis `hCmass`; so the two powers add to
`δ^{-2η}` and no further side condition is needed, both factors being at least `1`.

It is split off from `transverseBallFill` because it is pure arithmetic in the factors of the
constant and shares no step with the geometry of that lemma, which the blueprint accordingly
does *not* ask to assert it. The threshold cannot be dispensed with: `Cbf ≥ 10³` always, so at
`δ = 1` no bound of the form `δ^{-kη}` holds, which is why the seventh clause is a field of
`Kakeya.VeryNotSticky.CaseScale` rather than an assumption of the branch. -/
theorem transverseBallFillConstantBound (cfg : VeryNotSticky.{u}) {τ τ' νA : ℝ}
    {bd : BallData cfg} {tc : ThinConfig cfg bd} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr) {Cmass : NNReal}
    (hCmass : Cmass ≤ 125 * cfg.δ ^ (-(9 * cfg.η))) :
    8 * ThinCase.transferConstant tc.C bd.C₀ * Cmass ≤ cfg.δ ^ (-(10 * cfg.η)) := by
  have hstep : 8 * ThinCase.transferConstant tc.C bd.C₀ * Cmass ≤
      (1000 * ThinCase.transferConstant tc.C bd.C₀) * cfg.δ ^ (-(9 * cfg.η)) := by
    calc
      8 * ThinCase.transferConstant tc.C bd.C₀ * Cmass
          ≤ 8 * ThinCase.transferConstant tc.C bd.C₀ * (125 * cfg.δ ^ (-(9 * cfg.η))) := by
            gcongr
      _ = (1000 * ThinCase.transferConstant tc.C bd.C₀) * cfg.δ ^ (-(9 * cfg.η)) := by ring
  calc
    8 * ThinCase.transferConstant tc.C bd.C₀ * Cmass
        ≤ (1000 * ThinCase.transferConstant tc.C bd.C₀) * cfg.δ ^ (-(9 * cfg.η)) := hstep
    _ ≤ cfg.δ ^ (-cfg.η) * cfg.δ ^ (-(9 * cfg.η)) := by
        gcongr
        exact scale.transverse_ballFill
    _ = cfg.δ ^ (-cfg.η + -(9 * cfg.η)) := (NNReal.rpow_add cfg.hδ.ne' _ _).symm
    _ = cfg.δ ^ (-(10 * cfg.η)) := by congr 1; ring

/-- **`U(𝕋, Y)` almost fills a ball of radius `r ≥ θ b`** (blueprint
`lem:ml2transverseBallFill`, equation `transfillball`).

In the situation of `Kakeya.VeryNotSticky.transverseMassBall`, and using the thin-case
hypothesis `a ≤ δ^{1-τ}`, there is a ball of the radius `r ≥ θ b` of
`Kakeya.VeryNotSticky.transverseFill` with

`|U(𝕋, Y) ∩ B_r| ⪆ δ^{3τ + 7η} |B_r|`.

At the ball `B(y, ρ)` of `transverseMassBall`, whose radius satisfies `ρ ≥ 3A`,
`Kakeya.ThinCase.transfer_thin` (blueprint `lem:ml2thinTransfer`), at the `tb` index `2η` of
`Kakeya.VeryNotSticky.ThinConfig.tb` (F8), gives

`|U(𝕋_B, Y'_B) ∩ B(y, 2ρ)| ≥ C_{lem:ml2thinTransfer}(C, C₀)^{-1} δ^{3τ+2η}
  |U(𝕎'_B, Y_{𝕎'_B}) ∩ B(y, ρ)|`,

and `2ρ = r`. The two gains multiply to `δ^{3τ+7η}`; the doubling of the radius costs the
factor `|B(y, 2ρ)| = 2³ |B(y, ρ)|`, which is absorbed into the constant, and the passage from
the local union `U(𝕋_B, Y'_B)` to the global `U(𝕋, Y)` is
`Kakeya.VeryNotSticky.ThinConfig.localUnion_subset`, the `cfg`-relative reading of blueprint
`lem:ml2thinLocalToGlobal` (`Kakeya.ThinCase.localToGlobal`).

The output constant is `Cbf = 2³ C_{lem:ml2thinTransfer}(tc.C, bd.C₀) Cmass`. It is produced
rather than defined only because `Cmass` is; see `Kakeya.VeryNotSticky.transverseFill`.

The radius is passed on with *both* of its bounds, `θ b ≤ r` and `r ≤ 1`, exactly as
`Kakeya.VeryNotSticky.transverseFill` produces them; the upper one is what
`Kakeya.VeryNotSticky.goalMult_of_theta_ge_explicit` hands to
`Kakeya.VeryNotSticky.exists_aScaleData` as its hypothesis `hr1`.

**The sub-polynomial bound `Cbf ≤ δ^{-2η}`** (blueprint `transverseBallFillConstantBound`) is
asserted alongside the ball estimate, but it is *not proved here*: it is pure arithmetic in the
factors of the constant and shares no step with the geometry above, so it is
`Kakeya.VeryNotSticky.transverseBallFillConstantBound` (blueprint
`lem:ml2transverseBallFillConstantBound`).

It is what `Kakeya.VeryNotSticky.goalMult_of_theta_ge` spends to discharge the absorption
hypothesis `hM'` of `Kakeya.VeryNotSticky.exists_aScaleData` at `M = Cbf`, and it is the
reason the transverse budget `Kakeya.VeryNotSticky.CaseParams.transverse` must leave
`e ≥ 2η + η` at `e = τ'β - 3τ - 7η`: that requirement is `3τ + 10η ≤ τ'β`, exactly
`2η ≤ e - cfg.η` (blueprint `lem:ml2transverseAbsorbBudget`), and the field's `3τ + 12η < τ'β`
gives it with the further `2η` of reserve. Without it the branch could not
name a bound on the constant it produces, since `Cbf` is quantified existentially here and no
later statement may assume a smallness hypothesis about it. -/
theorem transverseBallFill (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    {νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (ta : TypicalAngleData cfg tc hB τ')
    (htrans : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ ta.θ)
    (hsmall : 6 * ThinCase.w1Constant bd.C₀ ≤ cfg.δ ^ (-τ')) :
    ∃ Cbf r : NNReal, 1 ≤ Cbf ∧ Cbf ≤ cfg.δ ^ (-(10 * cfg.η)) ∧ ta.θ * cfg.b ≤ r ∧ r ≤ 1 ∧
      r ≤ 6 * cfg.δ ^ cfg.exscal ∧
      ∃ y : EuclideanSpace ℝ (Fin 3),
      (Cbf : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) *
          volume (ball y (r : ℝ)) ≤
        volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball y (r : ℝ)) := by
  set θ := ta.θ with hθdef
  rcases transverseMassBall cfg params hnotslab tc hB scale ta htrans hsmall with
    ⟨Cmass, r, hCmass, hCmassbd, hθbr, hr1, hr6, hrad, y, hy⟩
  let R : ℝ := (r : ℝ)
  let ρ : ℝ := R / 2
  let Cbf : NNReal := 8 * ThinCase.transferConstant tc.C bd.C₀ * Cmass
  -- positivity of the radius (blueprint `lem:ml2transverseRadiusLower`, fourth bound)
  have hτ'pos : 0 < τ' := lt_trans params.hτ params.hτ'
  obtain ⟨-, -, -, hθbpos⟩ := transverseRadiusLower cfg hτ'pos θ htrans
  have hRpos : 0 < R := by
    have hrpos : (0 : NNReal) < r := lt_of_lt_of_le hθbpos hθbr
    dsimp [R]
    exact_mod_cast hrpos
  -- `2 * ρ = R`
  have h2ρ : 2 * ρ = R := by
    dsimp [ρ, R]
    ring
  -- ENNReal hypotheses on δ
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt cfg.hδ)
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- transfer_thin at the ball of radius ρ
  have hT : ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) *
        volume ((tc.thinBall hB).UW ∩ ball y ρ) ≤
      volume ((tc.thinBall hB).U ∩ ball y (2 * ρ)) := by
    exact ThinCase.transfer_thin (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3))
      (tc.thinBall hB) cfg.hδ cfg.hdims.1 hthin (r := ρ) hrad y
  -- multiply the mass-ball estimate by the transfer prefactor
  have hstep1 : ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) *
        ((Cmass : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) * volume (ball y ρ)) ≤
      ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) * volume ((tc.thinBall hB).UW ∩ ball y ρ) := by
    gcongr
  have hstep2 : ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) *
        ((Cmass : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) * volume (ball y ρ)) ≤
      volume ((tc.thinBall hB).U ∩ ball y (2 * ρ)) := by
    exact le_trans hstep1 hT
  -- combine the two powers of δ
  have hδpow : (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) * (cfg.δ : ENNReal) ^ (65 * cfg.η) =
      (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) := by
    rw [← ENNReal.rpow_add (3 * τ + 2 * cfg.η) (65 * cfg.η) hδ0 hδtop]
    congr 1
    ring
  have hcombine :
      ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) *
        ((Cmass : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) * volume (ball y ρ)) =
      ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y ρ) := by
    calc
      ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ *
            (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) *
            ((Cmass : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (65 * cfg.η) * volume (ball y ρ))
          = ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ *
              (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) * (cfg.δ : ENNReal) ^ (65 * cfg.η) *
              volume (ball y ρ) := by
            ring
      _ = ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ *
            ((cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) * (cfg.δ : ENNReal) ^ (65 * cfg.η)) *
            volume (ball y ρ) := by
            ring
      _ = ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ *
            (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y ρ) := by
            rw [hδpow]
  have hstep3 : ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ *
        (Cmass : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y ρ) ≤
      volume ((tc.thinBall hB).U ∩ ball y (2 * ρ)) := by
    rwa [hcombine] at hstep2
  -- pass from the local union to the global shaded union
  have hsub : (tc.thinBall hB).U ∩ ball y (2 * ρ) ⊆
      (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball y (2 * ρ) := by
    exact Set.inter_subset_inter (tc.localUnion_subset hB) le_rfl
  have hmono : volume ((tc.thinBall hB).U ∩ ball y (2 * ρ)) ≤
      volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball y (2 * ρ)) := by
    exact measure_mono hsub
  have hstep4 : ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ *
        (Cmass : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y ρ) ≤
      volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball y R) := by
    calc
      ((ThinCase.transferConstant tc.C bd.C₀ : NNReal) : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ *
            (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y ρ)
          ≤ volume ((tc.thinBall hB).U ∩ ball y (2 * ρ)) := hstep3
      _ ≤ volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball y (2 * ρ)) := hmono
      _ = volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball y R) := by rw [h2ρ]
  -- the volume of a ball of radius R = 2ρ is at most 8 times that of radius ρ
  have hvol : volume (ball y R) ≤ (8 : ENNReal) * volume (ball y ρ) := by
    rw [← h2ρ]
    exact volume_ball_two_mul_le y ρ
  -- the constant Cbf = 8 * transferConstant * Cmass
  have hCbf1 : (1 : NNReal) ≤ Cbf := by
    dsimp [Cbf]
    simpa using
      (mul_le_mul'
        (mul_le_mul' (by norm_num : (1 : NNReal) ≤ 8)
          (ThinCase.one_le_transferConstant tc.C bd.C₀)) hCmass)
  have hCtrpos : (0 : NNReal) < ThinCase.transferConstant tc.C bd.C₀ :=
    lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) (ThinCase.one_le_transferConstant tc.C bd.C₀)
  have hCmnz : Cmass ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCmass)
  have h8e : (8 : ENNReal) ≠ 0 := by norm_num
  have h8t : (8 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCbfe : (Cbf : ENNReal) = (8 : ENNReal) *
      (ThinCase.transferConstant tc.C bd.C₀ : ENNReal) * (Cmass : ENNReal) := by
    dsimp [Cbf]
  have hCbinv8 : (Cbf : ENNReal)⁻¹ * (8 : ENNReal) =
      (ThinCase.transferConstant tc.C bd.C₀ : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ := by
    calc
      (Cbf : ENNReal)⁻¹ * (8 : ENNReal)
          = ((8 : ENNReal) * (ThinCase.transferConstant tc.C bd.C₀ : ENNReal) *
              (Cmass : ENNReal))⁻¹ * (8 : ENNReal) := by
            rw [hCbfe]
      _ = ((8 : ENNReal)⁻¹ * (ThinCase.transferConstant tc.C bd.C₀ : ENNReal)⁻¹ *
            (Cmass : ENNReal)⁻¹) * (8 : ENNReal) := by
            rw [ENNReal.mul_inv (Or.inr (by exact ENNReal.coe_ne_top))
              (Or.inr (by exact_mod_cast hCmnz))]
            rw [ENNReal.mul_inv (Or.inl (by norm_num : (8 : ENNReal) ≠ 0))
              (Or.inr (by exact_mod_cast (ne_of_gt hCtrpos)))]
      _ = ((8 : ENNReal)⁻¹ * (8 : ENNReal)) *
            ((ThinCase.transferConstant tc.C bd.C₀ : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹) := by ring
      _ = (ThinCase.transferConstant tc.C bd.C₀ : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ := by
            rw [ENNReal.inv_mul_cancel h8e h8t]
            simp
  have hfinal_const : (Cbf : ENNReal)⁻¹ * (8 : ENNReal) ≤
      (ThinCase.transferConstant tc.C bd.C₀ : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ := by
    exact le_of_eq hCbinv8
  -- assemble
  have hfinal : (Cbf : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y R) ≤
      (ThinCase.transferConstant tc.C bd.C₀ : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ *
        (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y ρ) := by
    calc
      (Cbf : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y R)
          ≤ (Cbf : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) *
              (8 * volume (ball y ρ)) := by
            gcongr
      _ = (Cbf : ENNReal)⁻¹ * (8 : ENNReal) * (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) *
            volume (ball y ρ) := by
            ring
      _ ≤ (ThinCase.transferConstant tc.C bd.C₀ : ENNReal)⁻¹ * (Cmass : ENNReal)⁻¹ *
            (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y ρ) := by
            gcongr
  have hGoal : (Cbf : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) * volume (ball y R) ≤
      volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball y R) := by
    exact le_trans hfinal hstep4
  -- the sub-polynomial bound `Cbf ≤ δ^{-2η}` (blueprint `lem:ml2transverseBallFillConstantBound`)
  have hCbfbd : Cbf ≤ cfg.δ ^ (-(10 * cfg.η)) :=
    transverseBallFillConstantBound cfg scale hCmassbd
  refine ⟨Cbf, r, hCbf1, hCbfbd, hθbr, hr1, hr6, y, ?_⟩
  simpa [R] using hGoal

/-! ### Step 4: from one `θ b`-ball to the density estimate -/

/-- The `ENNReal` bookkeeping behind `Kakeya.VeryNotSticky.transverseDensity`, isolated from
the geometry, in the manner of `Kakeya.VeryNotSticky.mul_self_mul_le_of_aScaleChain`.

Read `d = δ`, `Cb = Cbf`, `B = |B_{θb}|`, `V = |U(𝕋,Y) ∩ B_{θb}|`, `R = θb`, and for the
exponents `m = 2ν = τ'β`, `p = 2β`, `q = 3τ + 7η`, `s = 1 - τ'`, `g = τ'β - 3τ - 7η`; then
`hR` is the lower bound `θ b ≥ δ^{1-τ'}` on the radius, `hfill` is the ball-fill estimate of
`Kakeya.VeryNotSticky.transverseBallFill`, `habsorb` is the fixed-scale threshold, and `hexp`
is the exponent identity `τ'β + (3τ+7η) + (1-τ')2β = 2β - (τ'β - 3τ - 7η)`, which is an
instance of `ring`. The conclusion is the density inequality at the ball.

The chain is
`d^m V R^p ≥ d^m (Cb⁻¹ d^q B) (d^s)^p = Cb⁻¹ d^{m+q+sp} B = Cb⁻¹ d^p d^{-g} B ≥
Cb⁻¹ d^p (K Cb) B = K d^p B`,
the last step cancelling `Cb⁻¹ Cb = 1`; the only side conditions are that `d` and `Cb` are
neither `0` nor `⊤` and that the exponent `p` is nonnegative, so that `x ↦ x^p` is monotone
in the base. -/
theorem mul_le_of_transverseChain {d Cb K B V R : ENNReal} {m p q s g : ℝ}
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hCb0 : Cb ≠ 0) (hCbtop : Cb ≠ ⊤) (hp : 0 ≤ p)
    (hR : d ^ s ≤ R) (hfill : Cb⁻¹ * d ^ q * B ≤ V) (habsorb : K * Cb ≤ d ^ (-g))
    (hexp : m + q + s * p = p - g) :
    K * d ^ p * B ≤ d ^ m * V * R ^ p := by
  have hRpow : (d ^ s) ^ p ≤ R ^ p := ENNReal.rpow_le_rpow hR hp
  have hcancel : Cb⁻¹ * Cb = 1 := ENNReal.inv_mul_cancel hCb0 hCbtop
  have hexp' : p + -g = m + q + s * p := by
    linarith
  calc
    K * d ^ p * B
        = Cb⁻¹ * d ^ p * (K * Cb) * B := by
            calc
              K * d ^ p * B = (Cb⁻¹ * Cb) * K * d ^ p * B := by
                rw [hcancel]
                simp
              _ = Cb⁻¹ * d ^ p * (K * Cb) * B := by
                ring
    _ ≤ Cb⁻¹ * d ^ p * d ^ (-g) * B := by
            exact mul_le_mul' (mul_le_mul' le_rfl habsorb) le_rfl
    _ = d ^ p * d ^ (-g) * Cb⁻¹ * B := by
            ring
    _ = d ^ (p + -g) * Cb⁻¹ * B := by
            rw [← ENNReal.rpow_add p (-g) hd0 hdtop]
    _ = Cb⁻¹ * d ^ (p + -g) * B := by
            ring
    _ = Cb⁻¹ * d ^ (m + q + s * p) * B := by
            rw [hexp']
    _ = Cb⁻¹ * d ^ (m + q) * d ^ (s * p) * B := by
            rw [ENNReal.rpow_add (m + q) (s * p) hd0 hdtop]
            ring
    _ = Cb⁻¹ * d ^ (m + q) * (d ^ s) ^ p * B := by
            rw [ENNReal.rpow_mul d s p]
    _ = d ^ m * (Cb⁻¹ * d ^ q * B) * (d ^ s) ^ p := by
            rw [ENNReal.rpow_add m q hd0 hdtop]
            ring
    _ ≤ d ^ m * V * R ^ p := by
            exact mul_le_mul' (mul_le_mul' le_rfl hfill) hRpow

/-- **From one ball of radius `r ≥ θ b` to the density estimate** (blueprint
`lem:ml2transverseDensity`).

In the situation of `Kakeya.VeryNotSticky.transverseBallFill`, the density form of the goal
`Kakeya.VeryNotSticky.goalDensity` (blueprint `eqgoaldens`) holds at the prescribed constant
`K`, at the radius `r` of `Kakeya.VeryNotSticky.transverseFill`, with the gain `ν = τ' β / 2`.

The blueprint value of the gain is `ν = τ'β - ½(3τ+7η)`, which
`Kakeya.VeryNotSticky.CaseParams.transverse` makes strictly larger than `½ τ' β`; the
guaranteed lower bound `½ τ' β` is what is formalized, because that is the value
`Kakeya.VeryNotSticky.bigmultExponent` hard-codes for this branch.

The estimate is produced at the radius `r ≥ θ b` at which the transverse chain works, and not
at the fixed scale `cfg.a`. This is what the variable radius of
`Kakeya.VeryNotSticky.goalDensity` is for: at radius `a` the requirement carries the factor
`(δ/a)^{2β}`, which this branch cannot make small, since nothing here bounds `a` from below
beyond `a ≥ δ`, and at `a ∼ δ` the requirement `K (δ/a)^{2β} ≤ δ^{2ν}` fails for every
positive gain. The consumer pairs it with `Kakeya.VeryNotSticky.AScaleData` at the same
radius, which `cfg.a ≤ θ b ≤ r` — a consequence of `htrans`, `a ≥ δ` and `δ ≤ 1` — makes
admissible.

Only the two inequalities `δ^{1-τ'} ≤ θ b ≤ r` are used, so the lemma holds verbatim at any
radius above `θ b`, which is what makes the existential radius of
`Kakeya.VeryNotSticky.transverseFill` harmless here. The blueprint chooses instead a nearby
radius of the admissible form `r = δ^{η j}`, paying `δ^{3η}` for the enlargement; no such
choice is needed, since `Kakeya.VeryNotSticky.exists_aScaleData` is stated at every radius
`≥ a`, and the `2η` left after F8 stays in the budget as reserve.

The proof is the comparison of exponents. From `hballfill`,

`δ^{2ν} |U(𝕋,Y) ∩ B_r| r^{2β} ≥ Cbf⁻¹ δ^{2ν + 3τ + 7η} r^{2β} |B_r|`,

and `r ≥ θ b ≥ δ^{-τ'} a ≥ δ^{1-τ'}` gives `r^{2β} ≥ δ^{2β} δ^{-2τ'β}`; since `2ν = τ'β` the
powers of `δ` collect to `δ^{2β} δ^{-(τ'β - 3τ - 7η)}`, and `habsorb` converts the surplus
into `K Cbf`, cancelling `Cbf`.

The hypothesis `habsorb` is the fixed-scale threshold of the branch: `K` is *prescribed* (the
consumer `Kakeya.VeryNotSticky.goalMult_of_goalDensity` demands the density form at `C^2` for
the one `C` supplied by `Kakeya.VeryNotSticky.exists_aScaleData`) and `Cbf` is produced by
`Kakeya.VeryNotSticky.transverseFill`, so with `cfg.δ` already fixed no argument can avoid
it: at `δ = 1` the conclusion is false for `K > 1`. It is discharged at the one call site,
`Kakeya.VeryNotSticky.goalMult_of_theta_ge`, from the absorption clause of
`Kakeya.VeryNotSticky.exists_aScaleData`, which is where the constant `C` is chosen and hence
the only place where a threshold in it can be asserted without making a hypothesis bundle
vacuous. The exponent `τ'β - 3τ - 7η` is positive by
`Kakeya.VeryNotSticky.CaseParams.transverse` — which reads `3τ + 12η < τ'β` — and `cfg.hη`,
with `5η` to spare: `3η` for the absorption split and `2η` for the margin the blueprint spends
on its admissible radius.

Only the hypotheses actually used are carried: the configuration parade of the three previous
steps (`params`, `hβ1`, `hthin`, `hnotslab`, `tc`, `hB`, `scale`, the plank data) enters this
step only through `hballfill` and `htrans`, so listing it would produce unused arguments
rather than information. -/
theorem transverseDensity (cfg : VeryNotSticky.{u}) {τ τ' : ℝ} (hτ' : 0 < τ') (θ r : NNReal)
    (htrans : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ θ) (hθbr : θ * cfg.b ≤ r)
    (Cbf : NNReal) (hCbf : 1 ≤ Cbf) (y : EuclideanSpace ℝ (Fin 3))
    (hballfill : (Cbf : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (3 * τ + 67 * cfg.η) *
        volume (ball y (r : ℝ)) ≤
      volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball y (r : ℝ)))
    (K : ENNReal)
    (habsorb : K * (Cbf : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ' * cfg.β - 3 * τ - 67 * cfg.η))) :
    cfg.goalDensity K r (τ' * cfg.β / 2) := by
  refine ⟨y, ?_⟩
  -- the geometric input: `r ≥ θ b ≥ δ^{1 - τ'}` in `NNReal`
  -- (blueprint `lem:ml2transverseRadiusLower`, second bound)
  have hnn : cfg.δ ^ (1 - τ') ≤ r :=
    le_trans (transverseRadiusLower cfg hτ' θ htrans).2.1 hθbr
  have hR : (cfg.δ : ENNReal) ^ (1 - τ') ≤ (r : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne' (1 - τ')]
    exact ENNReal.coe_le_coe.mpr hnn
  -- `ENNReal` side conditions
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr cfg.hδ.ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCb0 : (Cbf : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCbf))
  have hCbtop : (Cbf : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hp : 0 ≤ (2 * cfg.β) := le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) cfg.hβ)
  have hexp : 2 * (τ' * cfg.β / 2) + (3 * τ + 67 * cfg.η) + (1 - τ') * (2 * cfg.β) =
      2 * cfg.β - (τ' * cfg.β - 3 * τ - 67 * cfg.η) := by
    ring
  -- the transverse chain
  exact mul_le_of_transverseChain
    (d := (cfg.δ : ENNReal)) (Cb := (Cbf : ENNReal)) (K := K)
    (B := volume (ball y (r : ℝ)))
    (V := volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball y (r : ℝ)))
    (R := (r : ENNReal))
    (m := 2 * (τ' * cfg.β / 2)) (p := 2 * cfg.β) (q := 3 * τ + 67 * cfg.η)
    (s := 1 - τ') (g := τ' * cfg.β - 3 * τ - 67 * cfg.η)
    hδ0 hδtop hCb0 hCbtop hp hR hballfill habsorb hexp

/-! ### Assembling the transverse case -/

/-- **The transverse absorption budget** (blueprint `lem:ml2transverseAbsorbBudget`).

This is the only place where the transverse budget
`Kakeya.VeryNotSticky.CaseParams.transverse`, namely `3τ + 12η < τ'β`, is read:
`Kakeya.VeryNotSticky.goalMult_of_theta_ge` obtains both of its conclusions from here in one
`obtain`, and contains no exponent arithmetic of its own.

At `e = τ'β - 3τ - 7η` the two conclusions are *exactly* the two hypotheses that
`Kakeya.VeryNotSticky.exists_aScaleData` imposes on its prescribed data, at `M = Cbf` and at
this `e`: the first is its `he : 0 < e`, and the second is its absorption hypothesis
`hM' : M ≤ δ^{-(e - η)}` (blueprint `aScaleAbsorbHyp`), stated at the fixed exponent
`ν_{lem:ml2aScaleData} = η` of blueprint `def:ml2aScaleDataExponent`.

The hypothesis `hCbf` is the sub-polynomial bound `Cbf ≤ δ^{-2η}` produced by
`Kakeya.VeryNotSticky.transverseBallFill` (blueprint `transverseBallFillConstantBound`); the
constant `Cbf` is quantified existentially there, so the branch that produces it is the only
one that can discharge a bound on it.

The arithmetic is: `e > 5η > 0` from the budget and `cfg.hη`, which is the first conclusion;
and then `2η ≤ e - η`, i.e. `3τ + 10η ≤ τ'β`, which is weaker than the budget, so
`δ^{-2η} ≤ δ^{-(e - η)}` by monotonicity of `s ↦ δ^{-s}` for `0 < δ ≤ 1`. The margin between
the `3τ + 10η` consumed here and the `3τ + 12η` the field states is the `2η` reserved for the
passage to an admissible radius (it was `3η` before F8 moved `transverseBallFill` from `3τ + 6η`
to `3τ + 7η`). -/
theorem transverseAbsorbBudget (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') {Cbf : NNReal}
    (hCbf : Cbf ≤ cfg.δ ^ (-(10 * cfg.η))) :
    0 < τ' * cfg.β - 3 * τ - 67 * cfg.η ∧
      (Cbf : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-((τ' * cfg.β - 3 * τ - 67 * cfg.η) - cfg.η)) := by
  -- the transverse budget leaves the margin `10η`
  refine ⟨by nlinarith [params.transverse, cfg.hη], ?_⟩
  -- `10η ≤ e - η`, i.e. `3τ + 78η ≤ τ'β`, which is weaker than the budget `3τ + 87η`
  have hbudget : 10 * cfg.η ≤ (τ' * cfg.β - 3 * τ - 67 * cfg.η) - cfg.η := by
    nlinarith [params.transverse, cfg.hη]
  have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  calc
    (Cbf : ENNReal) ≤ ((cfg.δ ^ (-(10 * cfg.η)) : NNReal) : ENNReal) :=
        ENNReal.coe_le_coe.mpr hCbf
    _ = (cfg.δ : ENNReal) ^ (-(10 * cfg.η)) := ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne' _
    _ ≤ (cfg.δ : ENNReal) ^ (-((τ' * cfg.β - 3 * τ - 67 * cfg.η) - cfg.η)) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith)

set_option linter.unusedVariables false in
/-- [Main Lemma 2, transverse case] (blueprint `lem:ml2transverse`).
In the configuration `cfg`, together with the per-ball data `bd` of Configuration
`hyp:ml2setup`, the thin-case configuration `tc` of Configuration `hyp:ml2thinsetup` over it,
a ball `B ∈ 𝔅`, the thin-case refinement `a ≤ δ^{1-τ}` and `b ≤ δ^{exscal} r_1 = δ^{2·exscal}`,
let `θ` be a typical angle of intersection (blueprint Def 6.12,
`Kakeya.IsTypicalPlankAngle`) with comparison constant `Ctyp` for the plank family `P`
realising the factoring slabs `𝕎'_B` (with plank aspect ratio `a'/b' = a/b`), as produced by
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`. Suppose we are in the
*transverse case*, i.e. `θ ≥ δ^{-τ'} (a/b)`. The exact exponent budget
`3τ + 12η < τ'β` is `params.transverse`. Then the density estimate `eqgoaldens` holds, giving
the goal with the explicit gain

`ν = τ' β / 2`.

The blueprint value is `ν = τ'β - O(τ+η) ≥ ½ τ' β`; the guaranteed lower bound `½ τ' β` is
what is formalized, since it is the value that `Kakeya.VeryNotSticky.bigmultExponent` — the
minimum of `½ τ' β` and `½ exscal β ζ` — hard-codes for this branch. The weaker conclusion
`∃ ν > 0, cfg.goalMult ν` was insufficient: `Kakeya.VeryNotSticky.goalMult_of_multBodies_ge`
must conclude the *named* exponent `bigmultExponent`, and an existentially bound gain cannot
be weakened to it.

The plank presentation, the angle, the typicality constant and the refinement travel in the
single bundle `ta : Kakeya.VeryNotSticky.TypicalAngleData cfg tc hB τ'`, which is exactly what
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` returns and what the tangential sibling
`Kakeya.VeryNotSticky.goalMult_of_theta_lt` also consumes; see its docstring for the three
groups of fields. The plank family is indexed by `bd.ω` and carried by the family `𝕎'_B` of
the thin-case data at `B`, i.e. `(tc.thinBall hB).bodies'`, rather than by a free `Finset`.

Like its tangential sibling this leaf carries `hβ1 : β ≤ 1` and the maximality hypothesis
`hBmax`; both are threaded from `Kakeya.VeryNotSticky.goalMult_of_multBodies_ge`, and *neither
is used* in the Lean proof.

`hBmax` is unused for a mathematical reason: no step of the argument — neither
`Kakeya.VeryNotSticky.transverseMassBall`, nor `Kakeya.VeryNotSticky.transverseBallFill`, nor
`transverseDensity`, nor the ingredients behind them — refers to any ball other than the fixed
`B`. It is carried only so that the two angular leaves of
`Kakeya.VeryNotSticky.goalMult_of_multBodies_ge` present the same interface, the tangential
leaf genuinely needing it through `Kakeya.VeryNotSticky.nonslabSplitBound`.

`hβ1` is unused for a different, temporary reason, and it is *not* spent in
`Kakeya.VeryNotSticky.transverseDensity`, which needs only `β > 0` (so that the exponent
`p = 2β` of `Kakeya.VeryNotSticky.mul_le_of_transverseChain` is nonnegative). The place `β ≤ 1`
is genuinely consumed is blueprint `lem:ml2aScaleData`, whose Lean rendering
`Kakeya.VeryNotSticky.exists_aScaleData` reads it off the configuration field `cfg.hβ1` rather
than from a binder of its own; so in Lean, and only in Lean, this argument is idle. (The
blueprint's other extra hypothesis on that lemma, the radius bound `r ≤ 1`, is no longer
missing: it is the binder `hr1` of `exists_aScaleData`, discharged here from the conclusion
`R ≤ 1` of `Kakeya.VeryNotSticky.transverseBallFill`.)

The proof is the assembly of the four steps of the subsection. The field
`scale.transverse_radius` supplies the fixed-scale threshold `δ^{-τ'} ≥ 6 C_{w₁}(C₀)`;
`transverseBallFill` — through `transverseMassBall` and
`Kakeya.VeryNotSticky.transverseFill` — produces the ball of `transfillball`, at a radius
`R ≥ θ b`, with its constant `Cbf` and the sub-polynomial bound `Cbf ≤ δ^{-2η}` on it;
`Kakeya.VeryNotSticky.exists_aScaleData`, available at the radius `R ≥ θ b ≥ a` and at this
gain by `Kakeya.VeryNotSticky.transverseGain_pos` and
`Kakeya.VeryNotSticky.transverseGain_ge`, supplies the comparison constant `C` together with
the absorption `C² Cbf ≤ δ^{-(τ'β - 3τ - 7η)}`; `transverseDensity` gives the density form at
`C^2` and radius `R`; and `Kakeya.VeryNotSticky.goalMult_of_goalDensity`, at that same
radius, converts it to the multiplicity form.

**This branch is the one consumer of clause (iv) of `exists_aScaleData`,** and it therefore
owes that statement its hypothesis `hM'` at `M = Cbf` and `e = τ'β - 3τ - 7η`, namely
`Cbf ≤ δ^{-(e - η)}`. It is *not* discharged here: it and the positivity `e > 0` are the two
conclusions of `Kakeya.VeryNotSticky.transverseAbsorbBudget` (blueprint
`lem:ml2transverseAbsorbBudget`), obtained from `Cbf ≤ δ^{-2η}` in one `obtain`, so that no
exponent arithmetic and no reading of `params.transverse` happens in this assembly. That lemma
derives them from `Cbf ≤ δ^{-2η}` together with `δ ≤ 1` and the exponent inequality
`2η ≤ e - η`, i.e. `3τ + 10η ≤ τ'β`, which follows from
`Kakeya.VeryNotSticky.CaseParams.transverse`, namely `3τ + 12η < τ'β`.
This is exactly why the transverse budget is stated with
`12η` and not with `7η`: the absorption consumes `3τ + 10η ≤ τ'β`, and the margin between that
and the `3τ + 12η` the field states is the `2η` the blueprint reserves for the passage to an
admissible radius; releasing that reserve would replace the exponent `3τ + 7η` of
`transverseBallFill` by `3τ + 9η`, which the budget still covers. The product
`C² Cbf ≤ δ^{-e}`, clause (iv) of blueprint `lem:ml2aScaleData`, is then
`ENNReal.sq_mul_le_rpow_neg` applied to that second conclusion and to the
sub-polynomiality conjunct `C² ≤ δ^{-η}` of `exists_aScaleData`; the recombination sits here
rather than inside `exists_aScaleData` because it is derivable and carrying it there cost that
statement five binders. Only the first conclusion of `transverseAbsorbBudget`, `0 < e`, is now
unused, `sq_mul_le_rpow_neg` needing no positivity.

**It is also where the eighth clause is spent.** `exists_aScaleData` assumes
`cfg.δ ≤ thr.aScale ν` at the gain `ν` at which it is invoked, and that hypothesis is
discharged here by `scale.aScaleData_threshold`. This is why `scale` is read at the
transverse gain `τ'β/2` rather than at a free gain `νA`: the eighth clause of Configuration
`hyp:ml2scale` is indexed by the gain, and the gain at which the transverse branch invokes
the interface is this one. The three statements of the chain below —
`Kakeya.VeryNotSticky.transverseFill`, `Kakeya.VeryNotSticky.transverseMassBall` and
`Kakeya.VeryNotSticky.transverseBallFill` — keep the gain free, since none of them consumes
that clause; the specialization propagates up from here to
`Kakeya.VeryNotSticky.goalMult_of_multBodies_ge`,
`Kakeya.VeryNotSticky.goalMult_of_b_le` and `Kakeya.goalMult_of_a_le`, and meets the
instance that `Kakeya.VeryNotSticky.exists_goalMult` arranges. -/
@[nolint unusedArguments]
theorem goalMult_of_theta_ge_explicit (cfg : VeryNotSticky.{u})
    {τ τ' : ℝ} (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hβ1 : cfg.β ≤ 1)
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ (B' : bd.bι) (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr)
    (ta : TypicalAngleData cfg tc hB τ')
    (htrans : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ ta.θ) :
    cfg.goalMult (τ' * cfg.β / 2) := by
  set θ := ta.θ with hθdef
  have hνpos : 0 < τ' * cfg.β / 2 := transverseGain_pos cfg params
  have hνge : 90 * cfg.η ≤ τ' * cfg.β / 2 := transverseGain_ge cfg params
  obtain ⟨Cbf, R, hCbf, hCbfbd, hθbR, hR1, hR6, y, hy⟩ :=
    transverseBallFill cfg params hthin hnotslab tc hB scale ta htrans scale.transverse_radius
  -- the transverse radius dominates `a` (blueprint `lem:ml2transverseRadiusLower`, third bound)
  have hτ'pos : 0 < τ' := lt_trans params.hτ params.hτ'
  have hr : cfg.a ≤ R :=
    le_trans (transverseRadiusLower cfg hτ'pos θ htrans).2.2.1 hθbR
  -- the exponent budget for the absorption: `e > 0` and the hypothesis `hM'` of
  -- `exists_aScaleData` at `M = Cbf` (blueprint `lem:ml2transverseAbsorbBudget`)
  obtain ⟨_he, hM'⟩ := transverseAbsorbBudget cfg params hCbfbd
  obtain ⟨C, hC, hC', hdata, hCsub⟩ :=
    exists_aScaleData cfg hr hR1 hR6 hνpos hνge (ckt_we_le_transverseGain cfg params)
      scale.aScaleData_threshold
  -- clause (iv) of blueprint `lem:ml2aScaleData`, recombined from the sub-polynomiality of
  -- `C` and the transverse budget for `Cbf`
  have habs : C ^ 2 * (Cbf : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(τ' * cfg.β - 3 * τ - 67 * cfg.η)) :=
    ENNReal.sq_mul_le_rpow_neg cfg.hδ hCsub hM'
  exact goalMult_of_goalDensity cfg hνpos.le hr hC hC' hdata
    (transverseDensity cfg hτ'pos θ R htrans hθbR Cbf hCbf y hy (C ^ 2) habs)

set_option linter.unusedVariables false in
/-- **[Main Lemma 2, transverse case] with the gain left existential** (blueprint
`lem:ml2transverse`).

`Kakeya.VeryNotSticky.goalMult_of_theta_ge_explicit` read at `ν = τ'β/2`, whose positivity is
`Kakeya.VeryNotSticky.transverseGain_pos`. It is the blueprint's own phrasing — "the goal holds
with a positive gain, the blueprint value being `ν = τ'β - O(τ+η)`" — and is kept so that
blueprint `lem:ml2transverse` has a Lean statement in exactly that shape.

It carries the *same* hypotheses as the explicit form, and that is the point. Nothing consumed it: the live chain,
`Kakeya.VeryNotSticky.goalMult_of_multBodies_ge`, uses the explicit form. It is restated here
with the explicit form's hypotheses, and proved
from it, rather than deleted, because blueprint `lem:ml2transverse` points its `\lean{...}` at
this name.

Like the explicit form it carries `hβ1` and `hBmax` without using them; see that docstring. -/
@[nolint unusedArguments]
theorem goalMult_of_theta_ge (cfg : VeryNotSticky.{u})
    {τ τ' : ℝ} (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hβ1 : cfg.β ≤ 1)
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ (B' : bd.bι) (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr)
    (ta : TypicalAngleData cfg tc hB τ')
    (htrans : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ ta.θ) :
    ∃ ν > (0 : ℝ), cfg.goalMult ν := by
  exact ⟨τ' * cfg.β / 2, transverseGain_pos cfg params,
    goalMult_of_theta_ge_explicit cfg params hβ1 hthin hnotslab tc hB hBmax scale ta htrans⟩

end Kakeya.VeryNotSticky
