/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeM1
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale

/-!
# Is the genuine parent level below the fine level?  **No row says so** — measured

The four-way split  cuts at `a < p < b`, and its cardinality
telescoping (`Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_two_mul_card_le`) needs the
chain `a ≤ p ≤ b`: the level-`b` nodes must sit inside a level-`p` node and those inside a
level-`a` node, which is `Kakeya.ML2Reduction.tube_le_coarseNode` at `(p, b)` and at `(a, p)`.

**`hfac` quantifies `p` over `a ≤ p` and nothing else.**  The only other constraint the (F)
payload places on `p` is `Kakeya.ML2Core.FloorHypothesisAt`'s second row,

    ∀ m', a < m' → m' < b → (two window-ratio rows) → p < m'

and this file is the measurement of what that row does and does not give.  Three facts, all
one-liners, all stated on **abstract** predicates so that no guarded text is transcribed
here:

* `Kakeya.ML2Core.parentLevel_lt_fine_of_inset` — if the window has **any** inset level, `p < b`
  follows.  So in the regime the source describes (`𝒲 ≠ ∅`) the four-way split's chain is free.
* `Kakeya.ML2Core.parentLevel_unbounded_of_no_inset` — if it has **none**, *every* `p` satisfies
  the row.  The row is then vacuous and bounds `p` above by nothing.
* `Kakeya.ML2Core.no_inset_of_succ` — and that case is not hypothetical: at `b = a + 1` there is
  no `m'` with `a < m' < b` at all, while `IsKatzTaoDividingWindow.coarse_lt_fine` permits
  `b = a + 1`.

Two further one-liners record what a consumer *can* recover in the residual case `b < p`, by
re-reading the (F) payload at the level `b` itself:

* `Kakeya.ML2Core.parentRow_at_fine_of_fine_lt` — the parent row transfers to `p := b`;
* `Kakeya.ML2Core.countFloor_at_fine_vacuous` — the count-floor row at `p := b` is vacuous,
  because its own `p < m'` clause contradicts `m' < b`.

What does **not** transfer is the parent-density row at `p := b`; that is the one place the
residual case costs something; `Kakeya.ML2Core.parentDensity_at_fine_of_window` below is that
cost, priced at the single scalar comparison `κc + η m ≤ 2 η'` (row **R0d** of the estimate pass, an
addition to 's open list).

**Family / shading / level pair.**  None: every statement here is about the natural numbers
`a`, `p`, `b` and abstract predicates on levels.  That is deliberate — the question is a
quantifier question, not a geometric one.
-/

@[expose] public section

namespace Kakeya.ML2Core

/-- **One inset level bounds the parent level.**  If some `m'` strictly between `a` and `b`
satisfies the window's two ratio rows, the (F) payload's parent row gives `p < m' < b`. -/
theorem parentLevel_lt_fine_of_inset {a b p : ℕ} {R : ℕ → Prop}
    (hpm : ∀ m' : ℕ, a < m' → m' < b → R m' → p < m')
    {m' : ℕ} (h1 : a < m') (h2 : m' < b) (hR : R m') :
    p < b :=
  lt_trans (hpm m' h1 h2 hR) h2

/-- **No inset level, no bound.**  If no `m'` between `a` and `b` satisfies the ratio rows, then
the parent row holds for *every* `p` — so it constrains the parent level not at all, and the
four-way split's chain `p ≤ b` is not available from the payload. -/
theorem parentLevel_unbounded_of_no_inset {a b : ℕ} {R : ℕ → Prop}
    (hempty : ∀ m' : ℕ, a < m' → m' < b → ¬ R m') (p : ℕ) :
    ∀ m' : ℕ, a < m' → m' < b → R m' → p < m' :=
  fun m' h1 h2 hR => absurd hR (hempty m' h1 h2)

/-- **And the empty case is reachable**: `IsKatzTaoDividingWindow.coarse_lt_fine` is `a < b`, which
`b = a + 1` satisfies, and then there is no level strictly between. -/
theorem no_inset_of_succ {a : ℕ} {R : ℕ → Prop} :
    ∀ m' : ℕ, a < m' → m' < a + 1 → ¬ R m' := by
  intro m' h1 h2
  omega

/-- **The parent row transfers to `p := b` in the residual case `b < p`.** -/
theorem parentRow_at_fine_of_fine_lt {a b p : ℕ} {R : ℕ → Prop} (hbp : b < p)
    (hpm : ∀ m' : ℕ, a < m' → m' < b → R m' → p < m') :
    ∀ m' : ℕ, a < m' → m' < b → R m' → b < m' :=
  fun m' h1 h2 hR => lt_trans hbp (hpm m' h1 h2 hR)

/-- **The count-floor row at `p := b` is vacuous**: it is guarded by its own `p < m'` clause,
which at `p := b` contradicts the row's `m' < b`. -/
theorem countFloor_at_fine_vacuous {a b : ℕ} {C : ℕ → Prop} :
    ∀ m' : ℕ, a < m' → m' < b → b < m' → C m' := by
  intro m' _ h2 h3
  omega

section Density

open MeasureTheory ConvexSpaceBody Tube
open scoped NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {ι : Type*}

omit [Nontrivial E] in
/-- **The parent-density row at `p := b`, from the window itself — at the cost of one scalar.**

The residual case `b < p` of the four-way split needs the (F) payload re-read at `p := b`; its
parent row transfers (`Kakeya.ML2Core.parentRow_at_fine_of_fine_lt`) and its count-floor row is
vacuous (`Kakeya.ML2Core.countFloor_at_fine_vacuous`), but its **density** row does not transfer.
It does not have to be assumed either: the window's own `middle_maxDensity_le` is a bound of
exactly that shape at the pair `(a, b)`, and pushing it through `Cstar ≤ δ ^ (-κc)` and
`ρ_a / ρ_b ≤ δ⁻¹` yields `δ ^ (-(κc + η m))`.

So the whole residual case costs **one scalar comparison**, `κc + η m ≤ 2 η'`, and no geometry.
That is row **R0d**'s whole price, stated as a hypothesis rather than as prose.

**Family:** the hierarchy `𝒰` on `(s, T)`; no shading.  **Level pair:** `(a, b)` — the window's
own pair, read as the degenerate parent pair. -/
theorem parentDensity_at_fine_of_window {δ Cst : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cst) {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ}
    {N a b m : ℕ} {κc η' : ℝ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar η εd N a b m)
    (hδ0 : 0 < δ) (hCstar : Cstar ≤ (δ : ENNReal) ^ (-κc)) (hηm : 0 ≤ η m)
    (hρa : (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ≤ 1)
    (hρb : (δ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ))
    (hδ1 : (δ : ℝ) ≤ 1) (hscal : κc + η m ≤ 2 * η') :
    ∀ jθ ∈ 𝒰.cover.indexSet a,
      Kakeya.maxDensity (𝒰.nodesUnder b a jθ)
          (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        ≤ (δ : ENNReal) ^ (-(2 * η')) := by
  intro jθ hjθ
  have hδ0R : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hρb0 : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) := lt_of_lt_of_le hδ0R hρb
  -- the ratio is at most `δ⁻¹`
  have hratio : (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
      ≤ (δ : ℝ) ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, div_le_iff₀ hρb0]
    calc (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ≤ 1 := hρa
      _ = (δ : ℝ)⁻¹ * (δ : ℝ) := by field_simp
      _ ≤ (δ : ℝ)⁻¹ * (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) := by
          exact mul_le_mul_of_nonneg_left hρb (by positivity)
  have hpow : ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ η m ≤ (δ : ℝ) ^ (-(η m)) := by
    calc ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ η m
        ≤ ((δ : ℝ) ^ (-(1 : ℝ))) ^ η m := Real.rpow_le_rpow (by positivity) hratio hηm
      _ = (δ : ℝ) ^ (-(η m)) := by
          rw [← Real.rpow_mul hδ0R.le]
          norm_num
  have hofr : ENNReal.ofReal
      (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ η m)
      ≤ (δ : ENNReal) ^ (-(η m)) := by
    rw [← ML2Reduction.ofReal_rpow_coe hδ0]
    exact ENNReal.ofReal_le_ofReal hpow
  have hδE0 : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
  have hδEt : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  calc Kakeya.maxDensity (𝒰.nodesUnder b a jθ)
          (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
      ≤ Cstar * ENNReal.ofReal
          (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ η m) :=
        hwin.middle_maxDensity_le jθ hjθ
    _ ≤ (δ : ENNReal) ^ (-κc) * (δ : ENNReal) ^ (-(η m)) := mul_le_mul' hCstar hofr
    _ = (δ : ENNReal) ^ (-(κc + η m)) := by
        rw [← ENNReal.rpow_add _ _ hδE0 hδEt]
        congr 1
        ring
    _ ≤ (δ : ENNReal) ^ (-(2 * η')) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)

end Density

end Kakeya.ML2Core

end
