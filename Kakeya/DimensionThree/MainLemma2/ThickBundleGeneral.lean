/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickPlankPresentableProducer
public import Kakeya.DimensionThree.MainLemma2.DenseInBodyConstants
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase

/-!
# The thick bundle at general working dimensions

This file assembles `Kakeya.VeryNotSticky.ThickDensityThresholds` at general
working dimensions `(a, b)`, using the plank presentation from
`ThickPlankPresentableProducer.lean`.

`Kakeya.VeryNotSticky.thickDensityThresholds_canonical` supplies seven of the
eight fields from the geometric and analytic inputs. The density threshold
is an explicit hypothesis. The plank presentation follows from `hED` through
`Kakeya.VeryNotSticky.thickPlankPresentable_of_ballData`.

## Quantifiers in the density threshold

The constants in a quantitative threshold must be controlled witnesses.
A condition `C² · (δ-free constant) ≤ δ^{-ν}` cannot hold for every
admissible comparison constant `C`: `Kakeya.VeryNotSticky.AScaleData` is
upward closed in `C` (`AScaleData.mono`), so one admissible constant gives
arbitrarily large admissible constants. This obstruction is formalized by
`Kakeya.VeryNotSticky.no_densityAfter_forall_C`. The same issue arises when
a threshold quantifies over arbitrarily large density witnesses `(Θ, C₁)`.

`Kakeya.VeryNotSticky.goalMult_of_denseInBody_at` instead takes a particular
`C` and its `AScaleData` certificate. The density constants are the named
witnesses from `DenseInBodyConstants.lean`, and
`Kakeya.VeryNotSticky.thickDensityThresholds_general_of_denseAt` supplies the
corresponding density field.
-/

@[expose] public section

open Finset MeasureTheory Metric Set ShadedBody
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya.VeryNotSticky

open Kakeya

/-- Shorthand for the ambient space of the thick case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

universe u

/-- The thick bundle at general working dimensions `(a, b)`.
The geometric and analytic inputs provide the plank presentation, and
`hdens` supplies the density-threshold field. This threshold remains an
explicit hypothesis, since the other bundle fields do not bound all of
its constants. The theorem does not assume `cfg.a = cfg.b`.
The parameter bundle is retained in the interface as `_params`. -/
theorem thickDensityThresholds_general (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (_params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') (bd : BallData cfg)
    (hED : ∀ B ∈ bd.bs, (bd.segs B : Set bd.σ).Pairwise
      fun p q => _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier)
    (hbias : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    {ηF : ℝ} (hηF : 0 < ηF) (hbudget : 2 * cfg.η < τ * ηF)
    {C_NC b₀ : NNReal} (hC_NC : 1 ≤ C_NC)
    (hvol : PlankFrostmanVolumeAt.{u} cfg.β (cfg.ϱ * cfg.β * τ / 8) ηF b₀ C_NC)
    (hb₀ : thickPlankCP bd.C₀ * cfg.δ ^ τ ≤ b₀)
    (hc₁ : (thickPlankCP bd.C₀) ^ (1 + ηF) * cfg.δ ^ (τ * ηF - 2 * cfg.η) ≤ bd.c₁)
    (hdens : statement_of_universal_thickDensity_bare.{u} cfg bd τ (thickPlankCP bd.C₀)
      (thickPlankΘ bd.C₀ C_NC cfg.ϱ)) :
    ThickDensityThresholds cfg bd τ (thickPlankCP bd.C₀)
      (thickPlankΘ bd.C₀ C_NC cfg.ϱ) C_NC ηF :=
  thickDensityThresholds_canonical (one_le_thickPlankCP bd.hC₀)
    (one_le_thickPlankΘ bd.hC₀ hC_NC cfg.hϱ.le) hηF hbudget hbias
    (fun _hthick => thickPlankPresentable_of_ballData cfg bd
      (segsDegree_le_of_pairwise bd hED edMultiplicityConstant) C_NC hC_NC)
    hvol hb₀ hc₁ hdens

/-- The thick-case multiplicity conclusion from a controlled density threshold.
The comparison constant is the one supplied by
`goalMult_of_a_ge_of_goalDensity`; `goalMult_of_denseInBody_at` uses
the threshold at that constant and the named density witnesses.
The conclusion is `goalMult` at general dimensions `(a, b)`.

The inputs are the configuration assumptions, `hED`, and the per-`C`
threshold. No separate `density` field or plank-presentation hypothesis
is needed: `thickPlankPresentable_of_ballData` constructs the presentation
from `hED`. A threshold universal in arbitrary admissible comparison
constants would instead be false by `no_densityAfter_forall_C`. -/
theorem goalMult_of_thickBundle_general (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') (bd : BallData cfg)
    (hβ1 : cfg.β ≤ 1) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hbias : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    {ηF : ℝ} (hηF : 0 < ηF)
    {C_NC b₀ : NNReal} (hC_NC : 1 ≤ C_NC)
    (hvol : PlankFrostmanVolumeAt.{u} cfg.β (cfg.ϱ * cfg.β * τ / 8) ηF b₀ C_NC)
    (hb₀ : thickPlankCP bd.C₀ * cfg.δ ^ τ ≤ b₀)
    (hc₁ : (thickPlankCP bd.C₀) ^ (1 + ηF) * cfg.δ ^ (τ * ηF - 2 * cfg.η) ≤ bd.c₁)
    (hED : ∀ B ∈ bd.bs, (bd.segs B : Set bd.σ).Pairwise
      fun p q => _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier)
    {C : ENNReal} (hC1 : 1 ≤ C) (hCtop : C ≠ ⊤)
    (himp : cfg.goalDensity (C ^ 2) cfg.a (cfg.ϱ * cfg.β * τ / 8) →
      cfg.goalMult (cfg.ϱ * cfg.β * τ / 8))
    (hthrC : C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
        (denseInBodyC₁ (thickPlankCP bd.C₀) (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
        (denseInBodyΘ (thickPlankCP bd.C₀) (thickPlankΘ bd.C₀ C_NC cfg.ϱ)
          bd.Cbias : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8))) :
    cfg.goalMult (cfg.ϱ * cfg.β * τ / 8) :=
  goalMult_of_denseInBody_at cfg params bd hβ1 hthick hbias (one_le_thickPlankCP bd.hC₀)
    (one_le_thickPlankΘ bd.hC₀ hC_NC cfg.hϱ.le) hηF
    (plankFrostmanUsable_of_thick (one_le_thickPlankCP bd.hC₀) hηF hthick hvol hb₀ hc₁)
    (thickPlankPresentable_of_ballData cfg bd
      (segsDegree_le_of_pairwise bd hED edMultiplicityConstant) C_NC hC_NC) hC1 hCtop himp hthrC

end Kakeya.VeryNotSticky

end

end
