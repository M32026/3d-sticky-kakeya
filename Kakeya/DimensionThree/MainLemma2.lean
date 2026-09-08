/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectPointwiseClosed
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceClosure

/-!
# GWZ Main Lemma 2

In `ℝ^3`, if `β > 0` and both `K_KT(β)` and `K_F(β)` hold, then `K_KT(β - ν β)`
holds for a monotone `ν : ℝ → ℝ` that is unconditionally positive on `(0, 1]`.
-/

@[expose] public section

namespace Kakeya

universe u

/-- Derives Main Lemma 2 from Katz-Tao estimates at every exponent in `(0, 1]`. -/
theorem KatzTaoEstimate.mainLemma2_of_all
    (hall : ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) := by
  refine ⟨fun β ↦ β / 2, ?_, ?_, ?_⟩
  · intro x _hx y _hy hxy
    dsimp
    linarith
  · intro β hβ _hβ1
    dsimp
    linarith
  · intro β hβ hβ1 _hKKT _hF
    dsimp
    rw [show β - β / 2 = β / 2 by ring]
    exact hall (β / 2) (by linarith) (by linarith)

/-- [GWZ, Main Lemma 2]
There exists a monotone function `ν : ℝ → ℝ`, unconditionally positive on `(0, 1]`,
such that whenever `0 < β ≤ 1` and the Katz-Tao and Frostman partial estimates
`K_KT(β)` and `K_F(β)` hold in `ℝ^3`, the improved Katz-Tao estimate `K_KT(β - ν β)`
also holds.

The unconditional positivity of `ν` on `(0, 1]` lets the bootstrap to `K_KT(β)`
for every `0 < β ≤ 1` avoid a separate closure-from-above lemma. -/
theorem KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3))) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) := by
  exact ML2Assembly.mainLemma2Statement_of_pointwiseCore_free
    (ML2Assembly.source_pointwiseCore_of_actual_direct_trials hSFE)

end Kakeya
