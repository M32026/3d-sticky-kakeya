/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallConstruction

/-!
# Re-setting the working dimensions `(a, b)` of a configuration after the per-ball factoring

General-branch steps G1. GWZ §9.3 fix the
dimensions `a × b × r₁` of the factoring bodies **after** running the biased maximal density
factoring (Lemma 9.2) in every ball and pigeonholing (`gwz.txt` l.2036–2041): "by pigeonholing,
we can suppose that for each `B`, the convex sets `W ∈ 𝕎_B` have dimensions `a × b × r₁`". In the
tree the working scales live in the configuration (`Kakeya.VeryNotSticky.a`, `.b`, `.hdims`),
while the ball cover and the segment family (`Kakeya.VeryNotSticky.BallDataCore`) never read
them. So the construction may run T2b (`Kakeya.VeryNotSticky.exists_config_of_slackCut_at`,
at `a = b = δ`) and T3 (`Kakeya.VeryNotSticky.ballDataCoreOfCover`) first, Lemma 9.2 second,
and re-set `(a, b)` third:

* `Kakeya.VeryNotSticky.withDims` replaces `a`, `b`, `hdims` of a configuration and nothing
  else — every other field is copied, which the `rfl` lemmas record;
* `Kakeya.VeryNotSticky.BallDataCore.withDims` transports a `BallDataCore` along it
  **definitionally** (`{ core with }`): no field of `BallDataCore` mentions `a` or `b`;
* the closing `example` is a tripwire: T2b's refinement clause reads the same on
  `withDims cfg a b h` as on `cfg`, so T2b is reused unchanged.

Nothing here changes a existing statement.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace Kakeya.VeryNotSticky

/-- `cfg` with its working dimensions replaced. -/
def withDims (cfg : VeryNotSticky.{u}) (a b : NNReal)
    (h : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal) : VeryNotSticky.{u} :=
  { cfg with a := a, b := b, hdims := h }

variable (cfg : VeryNotSticky.{u}) (a b : NNReal) (h : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal)

@[simp] theorem withDims_a : (withDims cfg a b h).a = a := rfl
@[simp] theorem withDims_b : (withDims cfg a b h).b = b := rfl
@[simp] theorem withDims_ι : (withDims cfg a b h).ι = cfg.ι := rfl
@[simp] theorem withDims_s : (withDims cfg a b h).s = cfg.s := rfl
@[simp] theorem withDims_T : (withDims cfg a b h).T = cfg.T := rfl
@[simp] theorem withDims_δ : (withDims cfg a b h).δ = cfg.δ := rfl
@[simp] theorem withDims_β : (withDims cfg a b h).β = cfg.β := rfl
@[simp] theorem withDims_ζ : (withDims cfg a b h).ζ = cfg.ζ := rfl
@[simp] theorem withDims_η : (withDims cfg a b h).η = cfg.η := rfl
@[simp] theorem withDims_ϱ : (withDims cfg a b h).ϱ = cfg.ϱ := rfl
@[simp] theorem withDims_exscal : (withDims cfg a b h).exscal = cfg.exscal := rfl
@[simp] theorem withDims_r₁ : (withDims cfg a b h).r₁ = cfg.r₁ := rfl
@[simp] theorem withDims_C₀ : (withDims cfg a b h).C₀ = cfg.C₀ := rfl

/-- A `BallDataCore` transports along `withDims` field for field (no field reads `a` or `b`). -/
def BallDataCore.withDims (core : BallDataCore cfg) : BallDataCore (withDims cfg a b h) :=
  { core with }

@[simp] theorem BallDataCore.withDims_bs (core : BallDataCore cfg) :
    (BallDataCore.withDims cfg a b h core).bs = core.bs := rfl
@[simp] theorem BallDataCore.withDims_segs (core : BallDataCore cfg) :
    (BallDataCore.withDims cfg a b h core).segs = core.segs := rfl
@[simp] theorem BallDataCore.withDims_Y (core : BallDataCore cfg) :
    (BallDataCore.withDims cfg a b h core).Y = core.Y := rfl
@[simp] theorem BallDataCore.withDims_Yg (core : BallDataCore cfg) :
    (BallDataCore.withDims cfg a b h core).Yg = core.Yg := rfl

/-- The refinement clause of T2b's conclusion is unchanged by `withDims`: same index type, same
family, same shades. -/
example {ι : Type u} (e : cfg.ι ≃ ι) (s : Finset ι)
    (T : ι → ShadedTube cfg.δ (EuclideanSpace ℝ (Fin 3))) (c : NNReal)
    (href : ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
      (fun i ↦ (cfg.T (e.symm i)).toShadedBody) s (fun i ↦ (T i).toShadedBody) c) :
    ShadedBody.IsCRefinement ((withDims cfg a b h).s.map e.toEmbedding)
      (fun i ↦ ((withDims cfg a b h).T (e.symm i)).toShadedBody) s
      (fun i ↦ (T i).toShadedBody) c := href

end Kakeya.VeryNotSticky
