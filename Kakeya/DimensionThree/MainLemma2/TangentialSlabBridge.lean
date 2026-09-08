/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.EDConstants
public import Kakeya.DimensionThree.MainLemma2.BallFactoringLemma92
public import Kakeya.DimensionThree.MainLemma2.TangentialSlabLattice

/-!
# The conjunct-3 bridge: the lattice producer, in the boundary's own words

They are:

| the binder `hslabPackage` (`SetupSideDataGeneral.lean:502-511`) | the producer |
|---|---|
| `cfg.a ≤ cfg.δ ^ (1 - τ)` | `cfg.a ≤ cfg.δ ^ (1 - τ')` |
| `bd.Cbias = lemma92Bias C₀bd ϱ` | `bd.Cbias = Cbias`, a free `Cbias` |
| the single hypothesis `CaseParams β ζ exscal ϱ η τ τ'` | five explicit hypotheses |

Each difference is in the favourable direction, and this file closes all three so that the
boundary's binder can be discharged by a single `exact`:

* the thin guard — `CaseParams.hτ'` gives `τ ≤ τ'`, so `1 - τ' ≤ 1 - τ` and, `cfg.δ` being at
  most `1`, `cfg.δ ^ (1 - τ) ≤ cfg.δ ^ (1 - τ')`; the binder's hypothesis therefore **implies**
  the producer's. (In fact the producer never reads it — it is `_ha` there — so the implication
  is belt and braces.)
* the bias — the producer is stated at a free `Cbias`, so it instantiates at
  `lemma92Bias C₀bd ϱ`; a free constant is a generalisation, not a gap.
* the parameter bundle — the four facts the producer needs are derived here from `CaseParams`
  and the boundary's own binders: `4 ≤ C₀bd` from `Kakeya.four_le_edSegmentsConstant`, and
  `η < τ'` by the route `Kakeya.VeryNotSticky.smallMultiplicityBudget` already uses
  (`CaseParams.transverse` with `β ≤ 1` and `CaseParams.hτ` gives `87 η < τ' β ≤ τ'`).

The statement below is the binder's ten lines **copied verbatim**, and the tripwire `example`
that follows restates them once more and closes by `exact`, so that any later edit of the
binder makes this file fail to elaborate.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter
open scoped NNReal ENNReal RealInnerProductSpace

universe u

noncomputable section

/-- The slab-package input for the general side-data construction.
The conclusion is the `hslabPackage` hypothesis of
`Kakeya.VeryNotSticky.sideDataResidue_of_obligations_general`. The
five hypotheses here are the corresponding assumptions of that theorem. -/
theorem eventually_slabPackage_general_of_lattice' {β ζ exscal ϱ η τ τ' : ℝ}
    (_hβ : 0 < β) (hβ1 : β ≤ 1) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    {C₀bd : NNReal} (hC₀bd : edSegmentsConstant ≤ C₀bd) :
    (CaseParams β ζ exscal ϱ η τ τ' →
      ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
        (tc : ThinConfig cfg bd),
        cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
        cfg.a ≤ cfg.δ ^ (1 - τ) → cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) →
        bd.C₀ = C₀bd → bd.Cbias = lemma92Bias C₀bd ϱ →
        (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
          Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
            Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) →
        ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
          Nonempty (SlabPackage cfg ta))
    := by
  intro params
  have hC₀4 : (4 : NNReal) ≤ C₀bd := le_trans four_le_edSegmentsConstant hC₀bd
  have hτ'pos : (0 : ℝ) < τ' := lt_trans params.hτ params.hτ'
  have h87 : 87 * η < τ' * β := by nlinarith [params.transverse, params.hτ]
  have hτ'βle : τ' * β ≤ τ' := by nlinarith [hτ'pos, hβ1]
  have hητ' : η < τ' := by nlinarith [h87, hτ'βle, hη]
  filter_upwards [eventually_slabPackage_general_of_lattice (β := β) (exscal := exscal)
    (ϱ := ϱ) (η := η) (τ' := τ') hη hexscal hϱ hητ' C₀bd (lemma92Bias C₀bd ϱ) hC₀4] with d hd
  intro cfg bd tc hδ hβ' hη' hex hϱ' ha hb hC₀ hCb hmargin B hB ta
  refine hd cfg bd tc hδ hβ' hη' hex hϱ' ?_ hb hC₀ hCb hmargin hB ta
  -- the thin guard: `δ ≤ 1` and `τ ≤ τ'` make the binder's hypothesis the stronger one
  exact le_trans ha (NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1
    (by linarith [params.hτ']))

/-- **Tripwire.** The binder of
`Kakeya.VeryNotSticky.sideDataResidue_of_obligations_general`, restated and closed by `exact`:
this `example` fails to elaborate if either text moves. -/
example {β ζ exscal ϱ η τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    {C₀bd : NNReal} (hC₀bd : edSegmentsConstant ≤ C₀bd) :
    (CaseParams β ζ exscal ϱ η τ τ' →
      ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
        (tc : ThinConfig cfg bd),
        cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
        cfg.a ≤ cfg.δ ^ (1 - τ) → cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) →
        bd.C₀ = C₀bd → bd.Cbias = lemma92Bias C₀bd ϱ →
        (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
          Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
            Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) →
        ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
          Nonempty (SlabPackage cfg ta))
    :=
  eventually_slabPackage_general_of_lattice' hβ hβ1 hexscal hϱ hη hC₀bd

end

end Kakeya.VeryNotSticky
