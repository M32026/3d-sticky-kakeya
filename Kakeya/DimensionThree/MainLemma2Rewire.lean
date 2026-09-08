/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2Ptw
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze

/-!
# Pointwise and envelope formulations of the exponent drop

This module relates the pointwise Main Lemma 2 estimate to the envelope
formulation used for the final exponent descent. It keeps the geometric core
and small-cardinality assumptions explicit and records the resulting public
statement through named implications.
-/

@[expose] public section

namespace Kakeya.ML2Rewire

universe u

/-! ## The envelope layer is exact: the pointwise drop *is* Main Lemma 2 -/

/-- The protected statement gives the pointwise drop: take `d = ν β`. -/
theorem pointwiseDrop_of_mainLemma2Statement (h : VNSUniform.MainLemma2Statement.{u}) :
    ML2Assembly.PointwiseDrop.{u} := by
  obtain ⟨ν, _hmono, hpos, hstep⟩ := h
  intro β hβ hβ1 hKT hF
  exact ⟨ν β, hpos β hβ hβ1, hstep β hβ hβ1 hKT hF⟩

/-- **The envelope layer is a repackaging, not a reduction.**  `Kakeya.ML2Assembly.PointwiseDrop`
and the protected Main Lemma 2 are the same statement up to the `MonotoneOn ν` bookkeeping, which
`Kakeya.VNSUniform.estimateSet_shape` supplies unconditionally.  In particular nothing is gained
by weakening the target to the pointwise drop, and nothing is lost by aiming at it. -/
theorem pointwiseDrop_iff_mainLemma2Statement :
    ML2Assembly.PointwiseDrop.{u} ↔ VNSUniform.MainLemma2Statement.{u} :=
  ⟨VNSUniform.mainLemma2Statement_of_pointwise_drop, pointwiseDrop_of_mainLemma2Statement⟩

/-! ## The small-cardinality slot is the theorem -/

/-- **`Kakeya.ML2Assembly.SmallCardHyp` alone gives the pointwise drop**, at `d = β/2`.

`SmallCardHyp` hands over `Kakeya.ML2Assembly.SmallCard γ` for every `γ ∈ [β/2, β)`, and
`Kakeya.ML2Squeeze.katzTaoEstimate_of_smallCard` turns that into `K_KT γ` because the band
`|𝕋| < δ^{-1}` is affinely vacuous.  Reading it at `γ = β/2` gives `K_KT (β - β/2)`. -/
theorem pointwiseDrop_of_smallCardHyp (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    ML2Assembly.PointwiseDrop.{u} := by
  intro β hβ hβ1 hKT hF
  refine ⟨β / 2, by linarith, ?_⟩
  have hsc : ML2Assembly.SmallCard.{u} (β / 2) :=
    hsmall β hβ hβ1 hKT hF (β / 2) le_rfl (by linarith)
  have hEq : β - β / 2 = β / 2 := by ring
  rw [hEq]
  exact ML2Squeeze.katzTaoEstimate_of_smallCard (by linarith) hsc

/-- **The second hypothesis of the GWZ assembly implies Main Lemma 2 by itself.** -/
theorem mainLemma2Statement_of_smallCardHyp (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    VNSUniform.MainLemma2Statement.{u} :=
  VNSUniform.mainLemma2Statement_of_pointwise_drop (pointwiseDrop_of_smallCardHyp hsmall)

/-- **The same, landing on the protected statement's type written out in full**, so that the claim
is about `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate` itself and not about a
paraphrase of it.  (`Kakeya.ML2Ptw` Tripwires 1 and 2 pin
`Kakeya.VNSUniform.MainLemma2Statement` to that declaration in both directions.) -/
theorem protected_statement_of_smallCardHyp (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) :=
  mainLemma2Statement_of_smallCardHyp hsmall

set_option linter.unusedVariables false in
/-- The geometric-core hypothesis in
`Kakeya.ML2Ptw.protected_statement_of_geometricCoreAt` is unused when `hsmall`
is available. This theorem has the same binders as that implication. -/
theorem protected_statement_of_geometricCoreAt_core_unused
    (hcore : ML2Assembly.GeometricCoreAt.{u}) (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    VNSUniform.MainLemma2Statement.{u} :=
  mainLemma2Statement_of_smallCardHyp hsmall

set_option linter.unusedVariables false in
/-- **The same at the binder list of
`Kakeya.ML2Bridge.mainLemma2Statement_of_uniformPlankExponent`**: both the `β`-uniform
plank-Frostman residual and the windowed geometric core are unused.  So the
end-to-end bridge is a composability compatibility, exactly as its own docstring says, and not a
reduction of Main Lemma 2 to three smaller obligations. -/
theorem protected_statement_of_uniformPlankExponent_core_unused
    (hplank : ∀ β₀ : ℝ, 0 < β₀ → β₀ ≤ 1 → VNSUniform.UniformPlankExponent.{u} β₀)
    (hcore : ML2Assembly.GeometricCore.{u}) (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    VNSUniform.MainLemma2Statement.{u} :=
  mainLemma2Statement_of_smallCardHyp hsmall

/-! ## The rewire itself, stated against the protected type -/

/-- **The GWZ route to the protected statement, in the form `MainLemma2.lean` would use.**

This is `Kakeya.ML2Ptw.protected_statement_of_geometricCoreAt` with the conclusion written out as
`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate` states it, so that the rewire is
visibly a substitution of proof terms:

```lean
theorem KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate : … :=
  Kakeya.ML2Rewire.protected_statement_verbatim_of_geometricCoreAt <hcore> <hsmall>
```

What is missing is
`<hcore>` and `<hsmall>`: `Kakeya.ML2Assembly.GeometricCoreAt` has no producer in the tree, and
`Kakeya.ML2Assembly.SmallCardHyp` cannot acquire one short of proving Main Lemma 2, by
`Kakeya.ML2Rewire.protected_statement_of_smallCardHyp` above. -/
theorem protected_statement_verbatim_of_geometricCoreAt
    (hcore : ML2Assembly.GeometricCoreAt.{u}) (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) :=
  ML2Ptw.protected_statement_of_geometricCoreAt hcore hsmall

end Kakeya.ML2Rewire
