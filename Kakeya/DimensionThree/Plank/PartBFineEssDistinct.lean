/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabFibreFrostmanReduction
public import Kakeya.DimensionThree.Plank.InnerConflictDegree
public import Kakeya.DimensionThree.Plank.EDWeightedExtraction
public import Kakeya.DimensionThree.Plank.GlobalPlankFactorizationEstimate
public import Kakeya.Tube.EssentiallyDistinctReduction
/-!
# Essential distinctness and the density budget in Proposition 6.6(B)

GWZ Definition 2.1(ii) at `ρ = δ` makes a GWZ-uniform family of `δ`-tubes
essentially distinct. The explicit fine-family hypothesis in Proposition
6.6(B) expresses this part of uniformity. The density factor
`Δmax(T) ^ (1 - β)` separately accounts for repetition without imposing a
maximal-density bound on the fine family.

The proof through `factoringAndMultPropGlobal_of_remark53` restricts essential
distinctness to a fibre and uses it in `exists_inner_plank_conflict_degree_bound`.
This controls the conflict degree of the inner normalized plank family,
which is extracted to satisfy the essential-distinctness hypothesis of
`PlankEstimateAtMasterScaleWithDensity`. A weaker `IsEDUpToMult` hypothesis
at multiplicity `M` gives degree `M + (M + 1) * d`.

`multiplicity_bound_transfer_of_massShare` transfers the bound from `u ⊆ q`
with shade-mass loss `L` when
`L * Δmax(u) ^ (1 - β) * |u| ^ β ≤ Δmax(q) ^ (1 - β) * |q| ^ β`.
It introduces no additional power of `δ`. For `N` copies of one tube,
`L = N`, `|u| = 1`, `|q| = N`, and `Δmax(q) = N`, giving equality by
`rpow_one_sub_mul_rpow`. GWZ Lemma 3.7 pays the same density loss through
a cardinality reduction. Selecting a maximal essentially distinct subfamily
alone gives a cardinality lower bound, whereas this transfer also needs the
upper bound `|u| ≲ |q| / Δmax(q)` together with mass retention.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

universe u

/-! ### The accounting: what the essential-distinctness loss must satisfy -/

/-- **The identity that makes GWZ 6.6(B) duplication-invariant.**

`N ^ (1 - β) * N ^ β = N`.  Under `N`-fold duplication of a family, `multiplicity`, `maxDensity`
and `card` are each multiplied by `N`, so the right-hand side of 6.6(B) is multiplied by
`N ^ (1 - β) * N ^ β`; this says that is exactly `N`, i.e. both sides move together.  It is also the
equality case of `Kakeya.multiplicity_bound_transfer_of_massShare`'s budget hypothesis. -/
theorem rpow_one_sub_mul_rpow (β : ℝ) {N : ℝ≥0∞} (h0 : N ≠ 0) (htop : N ≠ ⊤) :
    N ^ (1 - β) * N ^ β = N := by
  rw [← ENNReal.rpow_add _ _ h0 htop, sub_add_cancel, ENNReal.rpow_one]

/-- **The transfer of a 6.6(B)-shaped bound from a subfamily, with the loss charged to the
`Δmax ^ (1 - β)` factor rather than to `δ ^ (-ε)`.**

If `u ⊆ q` carries a shade-mass share `L` and satisfies the 6.6(B) bound, then `q` satisfies it —
at the **same** `ε`, with no `δ`-power spent — as soon as the budget clause

`L * Δmax(u) ^ (1 - β) * |u| ^ β ≤ Δmax(q) ^ (1 - β) * |q| ^ β`

holds.  This is the whole of the accounting: `Kakeya.multiplicity_pigeon_transfer` supplies
`µ(q) ≤ L · µ(u)` from the mass share, and the budget clause absorbs `L`.

The clause is exactly what GWZ's Lemma 3.7 device produces, and it is sharp — see
`Kakeya.rpow_one_sub_mul_rpow` and the equality-case witness in
`Kakeya/DimensionThree/Plank/PartBFineEDBudget.lean`. -/
theorem multiplicity_bound_transfer_of_massShare
    {β ε : ℝ} {a b δ : ℝ≥0} {ι : Type*} {q u : Finset ι} (hu : u ⊆ q)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) {L : ℝ≥0∞}
    (hmass : (∑ i ∈ q, volume (T i).shade) ≤ L * ∑ i ∈ u, volume (T i).shade)
    (hsub : ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (-ε)
        * (maxDensity u (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (u.card : ℝ≥0∞) ^ β)
    (hbudget : L * (maxDensity u (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
        * (u.card : ℝ≥0∞) ^ β
      ≤ (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β) * (q.card : ℝ≥0∞) ^ β) :
    ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (-ε)
        * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
        * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (q.card : ℝ≥0∞) ^ β := by
  have hpig : ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      ≤ L * ShadedBody.multiplicity u (fun i => (T i).toShadedBody) :=
    multiplicity_pigeon_transfer _ hu (fun i => (T i).toShadedBody) hmass
  refine hpig.trans ?_
  calc L * ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
      ≤ L * ((δ : ℝ≥0∞) ^ (-ε)
          * (maxDensity u (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (u.card : ℝ≥0∞) ^ β) := by gcongr
    _ = (δ : ℝ≥0∞) ^ (-ε) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β
          * (L * (maxDensity u (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * (u.card : ℝ≥0∞) ^ β) := by ring
    _ ≤ (δ : ℝ≥0∞) ^ (-ε) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β
          * ((maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * (q.card : ℝ≥0∞) ^ β) := by gcongr
    _ = (δ : ℝ≥0∞) ^ (-ε)
          * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β * (q.card : ℝ≥0∞) ^ β := by ring



/-! ### The packing cap without essential distinctness -/

/-- **The windowed packing cap, with `Δmax` in place of essential distinctness.**

`Kakeya.Plank.card_le_of_windowed_essentiallyDistinct` bounds the cardinality of a windowed family
of `a × b × 1` planks by `Cwin · a ^ (-Dwin)`, and pairwise essential distinctness is exactly what
it spends.  The same count holds for **any** windowed family at the cost of one factor of the
family's own maximal density, and needs no distinctness at all:

`|s| · 8ab ≤ Δmax(s) · |window|`.

The proof is two facts already in the tree — every plank has volume exactly `8ab`
(`Kakeya.Prism3D.volume_carrier`, at `c = 1`), and a family all of whose bodies lie in a common
body has total volume at most `Δmax` times that body's volume
(`Kakeya.sum_volume_le_maxDensity_mul_volume'`).  Repetition is priced rather than forbidden: `N`
copies of one plank multiply both sides by `N`.

**This is the input the essential-distinctness deletion needs.**  Our GWZ Lemma 6.1 chain spends
distinctness at exactly two places, both of them this packing cap — once in
`Kakeya.KatzTaoEstimate.plankEstimate_auxScale` and once inside
`Kakeya.refinement_preassembly_uniform`, where it supplies the `hcard` slot of GWZ Lemma 6.11.
Everywhere else on the chain the hypothesis is carried and passed on; at the bottom,
`Kakeya.findingTypicalAngleOfIntersection_core` receives it and never uses it. -/
theorem card_mul_volume_le_maxDensity_mul_window
    {ι : Type*} (s : Finset ι) {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ι → Plank a b hab hb1) (hwin : Plank.IsWindowedFamily s P) :
    (s.card : ℝ≥0∞) * (8 * (a : ℝ≥0∞) * (b : ℝ≥0∞))
      ≤ maxDensity s (fun i => (P i).toConvexSpaceBody) * volume plankWindow.carrier := by
  classical
  have hle : ∀ i ∈ s, (P i).toConvexSpaceBody ≤ plankWindow := by
    intro i hi
    have h := hwin i hi
    have hsub : ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (plankWindow.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
      rw [plankWindow_carrier]
      refine h.trans (Metric.closedBall_subset_closedBall ?_)
      norm_num [Plank.windowRadius, plankWindowRadius]
    first
      | exact SetLike.coe_subset_coe.mp hsub
      | exact SetLike.coe_subset_coe.mpr hsub
      | exact hsub
  have hvol : ∀ i ∈ s,
      volume ((P i).toConvexSpaceBody.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = 8 * (a : ℝ≥0∞) * (b : ℝ≥0∞) := by
    intro i _
    have := Prism3D.volume_carrier (P i)
    simpa using this
  have hsum : (∑ i ∈ s, volume ((P i).toConvexSpaceBody.carrier
      : Set (EuclideanSpace ℝ (Fin 3))))
      = (s.card : ℝ≥0∞) * (8 * (a : ℝ≥0∞) * (b : ℝ≥0∞)) := by
    rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact sum_volume_le_maxDensity_mul_volume' (K := plankWindow) hle


/-! ### The exponent ledger of the deep branch, and the exact shortfall -/

/-- **What the essential-distinctness deletion costs in the deep branch of GWZ Lemma 6.1.**

`Kakeya.KatzTaoEstimate.plankEstimate_auxScale` splits on `τ ≤ a ^ C`.  In that *deep* branch the
tree does not run the plank estimate at all: it bounds the multiplicity by the **cardinality**
(`ShadedBody.multiplicity_le_card`) and then bounds the cardinality by the windowed packing cap
`|s| ≤ Cwin · a ^ (-Dwin)`, which is where pairwise essential distinctness is spent.

Replacing that cap by the distinctness-free
`Kakeya.card_mul_volume_le_maxDensity_mul_window` costs exactly one factor of `Δmax(s)`, so the
branch arrives at `M ≤ D · τ ^ (-ε/2)` instead of `M ≤ τ ^ (-ε/2)`.  This lemma is the rest of the
ledger, with every other input unchanged: `hfund` is the branch's own `hτfund`
(`τ ^ (ηβ) ≤ (a/b) ^ (γβ) · |s| ^ β`, from the slab hypothesis applied to one member's wide slab),
and `A` stands for `(a/b) ^ (γβ) · |s| ^ β`.

**`hbudget` is the shortfall, and it is the whole of it.**  With `ηβ ≤ ε/2` — which the branch
already imposes — the required inequality is

`Δmax(s) ^ β ≤ τ ^ (ηβ - ε/2)`,   i.e.   `Δmax(s) ≤ τ ^ (-(ε/2 - ηβ) / β)`,

a **sub-polynomial density budget on the plank family at the auxiliary scale**.  It is not among
Lemma 6.1's hypotheses, and it is not implied by them: `N`-fold repetition of one plank satisfies
every hypothesis with `Δmax = N` unbounded.

**But it is not a new gap.**  It is exactly the content of GWZ Lemma 3.7, which this tree already
renders for *tube* families — `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window`
(`Kakeya/PartialEstimatesWindowed.lean:453`) concludes
`µ ≤ τ ^ (-ε) · Δmax ^ (1 - β) · |s| ^ β` from `K_KT(β)` with **no** distinctness hypothesis, and
the random-subset device its proof uses is formalised in `Kakeya/Probability.lean`.  What the deep
branch needs is the *plank* analogue of that statement.  With it, `hbudget` is discharged outright
and the branch never needs the crude `multiplicity ≤ card` step that made the packing cap
load-bearing in the first place. -/
theorem deep_branch_ledger {β ε ηβ : ℝ} {τ : ℝ≥0} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    {M D A : ℝ≥0∞} (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (hmu : M ≤ D * (τ : ℝ≥0∞) ^ (-(ε / 2)))
    (hfund : (τ : ℝ≥0∞) ^ ηβ ≤ A)
    (hbudget : D ^ β ≤ (τ : ℝ≥0∞) ^ (ηβ - ε / 2)) :
    M ≤ (τ : ℝ≥0∞) ^ (-ε) * D ^ (1 - β) * A := by
  have hτne : ((τ : ℝ≥0∞)) ≠ 0 := by simpa using hτ0.ne'
  have hτtop : ((τ : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
  refine hmu.trans ?_
  have hsplit : D = D ^ (1 - β) * D ^ β := (rpow_one_sub_mul_rpow β hD0 hDtop).symm
  calc D * (τ : ℝ≥0∞) ^ (-(ε / 2))
      = D ^ (1 - β) * D ^ β * (τ : ℝ≥0∞) ^ (-(ε / 2)) := by rw [← hsplit]
    _ ≤ D ^ (1 - β) * (τ : ℝ≥0∞) ^ (ηβ - ε / 2) * (τ : ℝ≥0∞) ^ (-(ε / 2)) := by gcongr
    _ = D ^ (1 - β) * ((τ : ℝ≥0∞) ^ (ηβ - ε / 2) * (τ : ℝ≥0∞) ^ (-(ε / 2))) := by ring
    _ = D ^ (1 - β) * ((τ : ℝ≥0∞) ^ (-ε) * (τ : ℝ≥0∞) ^ ηβ) := by
        rw [← ENNReal.rpow_add _ _ hτne hτtop, ← ENNReal.rpow_add _ _ hτne hτtop]
        congr 2
        ring
    _ ≤ D ^ (1 - β) * ((τ : ℝ≥0∞) ^ (-ε) * A) := by gcongr
    _ = (τ : ℝ≥0∞) ^ (-ε) * D ^ (1 - β) * A := by ring


/-- **The deep branch closes with no density budget: split `|s|` as `|s| ^ (1-β) · |s| ^ β` and
spend the packing cap on the first factor only.**

`Kakeya.deep_branch_ledger` above charges the whole of `|s|` to the packing cap, arriving at
`M ≤ D · τ ^ (-ε/2)` and leaving the residual budget `hbudget`.  That is lossy, and the loss is
avoidable.  Writing `N = N ^ (1-β) · N ^ β` and applying the cap `N ≤ D · K` **only to the
`N ^ (1-β)` factor** produces the `D ^ (1-β)` of the conclusion *exactly*, with `K ^ (1-β)` — a
fixed power of `a` — left to be absorbed by the branch's own scale device.  No hypothesis on `D`
survives.

This is the same accounting as `Kakeya.multiplicity_bound_transfer_of_massShare` and
`Kakeya.rpow_one_sub_mul_rpow`, one level deeper: **repetition is priced by the `Δmax ^ (1-β)`
factor rather than forbidden by a distinctness hypothesis.**  Under `N`-fold repetition of one
plank, `M`, `D` and `N` all scale by `N` and both sides move by exactly `N`.

Instantiated at the deep branch of `Kakeya.KatzTaoEstimate.plankEstimate_auxScale`:
`M = µ(s, V)`, `N = |s|`, `D = Δmax(s)`, `A = (a/b) ^ (γβ)`, and
`K = Kakeya.plankWindow`-volume`/(8ab)`-type constant times `a ^ (-2)`, supplied by
`Kakeya.card_mul_volume_le_maxDensity_mul_window`.  `habs` is then
`K ^ (1-β) ≤ τ ^ (-ε) · A`, whose worst case has exponent `2(1-β) + γβ ≤ 3` on `a`, while the
branch hypothesis `τ ≤ a ^ C` with the file's own `C = 4(Dwin+1)/ε` delivers
`τ ^ (-ε) ≥ a ^ (-4(Dwin+1))` and `4(Dwin+1) ≥ 4 > 3`.  **So the branch has strictly more scale
room than the replacement needs**, and no plank-valued Lemma 3.7 is required. -/
theorem deep_branch_ledger_split {β ε : ℝ} (hβ1 : β ≤ 1) {τ : ℝ≥0}
    {M D N K A : ℝ≥0∞} (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hMN : M ≤ N)
    (hcard : N ≤ D * K)
    (habs : K ^ (1 - β) ≤ (τ : ℝ≥0∞) ^ (-ε) * A) :
    M ≤ (τ : ℝ≥0∞) ^ (-ε) * D ^ (1 - β) * A * N ^ β := by
  have hexp : (0 : ℝ) ≤ 1 - β := by linarith
  calc M ≤ N := hMN
    _ = N ^ (1 - β) * N ^ β := (rpow_one_sub_mul_rpow β hN0 hNtop).symm
    _ ≤ (D * K) ^ (1 - β) * N ^ β :=
        mul_le_mul_right' (ENNReal.rpow_le_rpow hcard hexp) _
    _ = D ^ (1 - β) * K ^ (1 - β) * N ^ β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hexp]
    _ ≤ D ^ (1 - β) * ((τ : ℝ≥0∞) ^ (-ε) * A) * N ^ β := by gcongr
    _ = (τ : ℝ≥0∞) ^ (-ε) * D ^ (1 - β) * A * N ^ β := by ring


/-- **The deep branch has strictly more scale room than the distinctness-free packing cap needs.**

The constant-free heart of the `habs` hypothesis of
`Kakeya.deep_branch_ledger_split`.  The replacement cap contributes `a ^ (-2(1-β))` after the
`(1-β)`-power is taken, and the conclusion supplies `a ^ (γβ)` as a lower bound for
`(a/b) ^ (γβ)` (valid since `b ≤ 1`).  The branch hypothesis `τ ≤ a ^ C` then converts
`τ ^ (-ε)` into `a ^ (-Cε)`, and the requirement is

`β(γ - 2) + 2 ≤ C ε`,

whose left side is **less than `2`** for every `0 < β ≤ 1`, `0 ≤ γ ≤ 1`.  The file's own
`C = 4(Dwin + 1)/ε` gives `Cε = 4(Dwin + 1) ≥ 4`, so the margin is at least a factor `a ^ (-2)` —
room to spare, and the reason the essential-distinctness deletion costs the deep branch nothing.

The exponent `Dwin = 12` of the distinctness-based cap is replaced by `2`, so the branch's scale
device is being asked to do **less** work than before, not more. -/
theorem deep_branch_scale_room {β ε γ C : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    {a τ : ℝ≥0} (ha0 : 0 < a) (ha1 : a ≤ 1) (hτ0 : 0 < τ)
    (hdeep : τ ≤ a ^ C) (hC : 4 ≤ C * ε) :
    a ^ (-(2 * (1 - β))) ≤ τ ^ (-ε) * a ^ (γ * β) := by
  have hpow : a ^ (-(C * ε)) ≤ τ ^ (-ε) := by
    have h := NNReal.rpow_le_rpow_of_nonpos hτ0 hdeep (neg_nonpos.mpr hε.le)
    calc a ^ (-(C * ε)) = (a ^ C) ^ (-ε) := by
          rw [← NNReal.rpow_mul]
          congr 1
          ring
      _ ≤ τ ^ (-ε) := h
  have hexp : γ * β - C * ε ≤ -(2 * (1 - β)) := by nlinarith [hβ0, hβ1, hγ0, hγ1, hC]
  calc a ^ (-(2 * (1 - β))) ≤ a ^ (γ * β - C * ε) :=
        NNReal.rpow_le_rpow_of_exponent_ge ha0 ha1 hexp
    _ = a ^ (-(C * ε)) * a ^ (γ * β) := by
        rw [← NNReal.rpow_add ha0.ne']
        congr 1
        ring
    _ ≤ τ ^ (-ε) * a ^ (γ * β) := by gcongr


/-! ### Why the deletion stops at GWZ Lemma 6.11, and does so structurally -/

/-- **`Nat.log 2` of the family cardinality admits no bound independent of the family.**

This is the obstruction that stops the essential-distinctness deletion one level above
`Kakeya.KatzTaoEstimate.plankEstimate_auxScale`.

`Kakeya.refineConst_bound_uniform_reserve_perScale` — the refinement-constant bound that GWZ
Lemma 6.11 runs on — has the shape

`∃ K, 0 ≤ K ∧ ∀ {a b δ}, … ∀ sc : ℕ, (sc : ℝ) ≤ C₀ · δ ^ (-Nexp) → … →
    δ ^ ε · (… · (Nat.log 2 sc + 1)) ≤ K`

with `K` quantified **outermost** and the cardinality `sc` quantified **after** it.  The
cardinality cap is spent there and nowhere else, and it is spent **logarithmically**.

Replacing the distinctness cap `|s| ≤ Cwin · a ^ (-Dwin)` by the distinctness-free
`Kakeya.card_mul_volume_le_maxDensity_mul_window` makes the bound on `sc` carry a factor
`Δmax(s)`, which is a function of the family.  At fixed `a`, `δ` and `ε` the quantity
`δ ^ ε · (Nat.log 2 sc + 1)` is then unbounded, so **no family-independent `K` exists** — which is
what this lemma says, with `c := δ ^ ε · (…)`.

The same obstruction recurs above: `Kakeya.plankReduction`'s output constants
`cN, cThk, Cbox, Cset, Cang, cP, cLam, c1, c2, c3, c4` are all quantified before the family too.
So `Δmax` cannot be threaded through Lemma 6.11 or Lemma 6.13 without moving those binders, and it
is the same structural fact that made `Csplit` unable to absorb a configuration-dependent constant
in `Kakeya.factoringAndMultPropGlobal_of_remark53`.

**Consequence.**  The deletion is affordable at the *auxiliary-scale* spend — the deep branch of
`plankEstimate_auxScale`, discharged by `Kakeya.deep_branch_ledger_split` and
`Kakeya.deep_branch_scale_room` with no hypothesis on `Δmax` — and it is **not** affordable at the
*Lemma 6.11* spend without either a density hypothesis at that level (which is the narrowing the
the source statement rejected, one level down) or a re-quantification of Lemma 6.13's constants. -/
theorem no_uniform_bound_of_log_card {c : ℝ} (hc : 0 < c) (K : ℝ) :
    ∃ N : ℕ, K < c * ((Nat.log 2 N + 1 : ℕ) : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (K / c)
  refine ⟨2 ^ m, ?_⟩
  have hlog : Nat.log 2 (2 ^ m) = m := Nat.log_pow (by norm_num) m
  rw [hlog]
  have hKm : K < c * (m : ℝ) := by
    rw [div_lt_iff₀ hc] at hm
    linarith
  have hstep : c * (m : ℝ) ≤ c * ((m : ℝ) + 1) := by nlinarith
  calc K < c * (m : ℝ) := hKm
    _ ≤ c * ((m : ℝ) + 1) := hstep
    _ = c * ((m + 1 : ℕ) : ℝ) := by push_cast; ring


/-! ### Option (3): the split at the 6.6(B) level, and what it needs -/

/-- **The 6.6(B)-level accounting: a `Δmax` multiplicity loss is paid by a cardinality-efficient
extraction, leaving exactly `Δmax ^ (1-β)`.**

Suppose a subfamily carries

* a **multiplicity transfer** `M ≤ L · D · M'` — the loss is one factor of the *ambient* maximal
  density `D`, at a sub-polynomial `L`; and
* a **cardinality-efficient** bound `N' · D ≤ N` — the subfamily is smaller by that same factor.

Then any 6.6(B)-shaped bound for the subfamily, `M' ≤ D' ^ (1-β) · A · N' ^ β`, transfers to the
whole family as `M ≤ L · D' ^ (1-β) · A · D ^ (1-β) · N ^ β`: the `D` of the multiplicity loss and
the `D ^ (-β)` of the cardinality drop combine to `D ^ (1-β)`, **which is exactly the factor
6.6(B) already carries**.  No hypothesis on `D` is required, and no `δ`-power is spent beyond `L`.

`A` stands for `(a/b) ^ β` and `D'` for the subfamily's own maximal density, which the extraction
also controls.

**Both inputs exist in this tree.**  `Kakeya.exists_random_subset` (`Kakeya/Probability.lean`) —
the random subset of GWZ Lemma 3.7 — returns, for a family of shaded `δ`-tubes in the unit ball,
a subfamily `s' ⊆ s` with

    (s'.card : ℝ) ≤ 2 * (s.card : ℝ) * (maxDensity s …)⁻¹          -- the cardinality-efficient half
    ConvexSpaceBody.IsKatzTao s' … (ENNReal.ofReal (δ ^ (-c)))     -- D' sub-polynomial
    multiplicityRLocal … s ≤ δ ^ (-c) * maxDensity s … * multiplicityRLocal … s'

which are precisely `hcard`, a bound on `D'`, and `hmult` with `L = δ ^ (-c)`.

**What is missing is packaging, not mathematics.**  `exists_random_subset` is consumed only inside
the proof of Lemma 3.7 (`Kakeya/PartialEstimates.lean`), and no exported statement exposes the
subfamily.  Making it available at the 6.6(B) call site is a re-export plus the discharge of its
hypothesis list (uniform tube volumes, a test family, and three smallness thresholds), all of which
Lemma 3.7's own proof already discharges for exactly this situation. -/
theorem multiplicity_bound_transfer_of_cardEfficient {β : ℝ} (hβ0 : 0 ≤ β)
    {M M' D D' N N' L A : ℝ≥0∞} (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (hmult : M ≤ L * D * M')
    (hcard : N' * D ≤ N)
    (hsub : M' ≤ D' ^ (1 - β) * A * N' ^ β) :
    M ≤ L * D' ^ (1 - β) * A * D ^ (1 - β) * N ^ β := by
  have hpow : D ^ β * N' ^ β ≤ N ^ β := by
    calc D ^ β * N' ^ β = (N' * D) ^ β := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hβ0]; ring
      _ ≤ N ^ β := ENNReal.rpow_le_rpow hcard hβ0
  calc M ≤ L * D * M' := hmult
    _ ≤ L * D * (D' ^ (1 - β) * A * N' ^ β) := by gcongr
    _ = L * D' ^ (1 - β) * A * (D * N' ^ β) := by ring
    _ = L * D' ^ (1 - β) * A * (D ^ (1 - β) * (D ^ β * N' ^ β)) := by
        have hDsplit : D ^ (1 - β) * (D ^ β * N' ^ β) = D * N' ^ β := by
          rw [← mul_assoc, rpow_one_sub_mul_rpow β hD0 hDtop]
        rw [hDsplit]
    _ ≤ L * D' ^ (1 - β) * A * (D ^ (1 - β) * N ^ β) := by gcongr
    _ = L * D' ^ (1 - β) * A * D ^ (1 - β) * N ^ β := by ring

/-! ### Route (a): the hypothesis is spent, but on our own rendering of GWZ Lemma 6.1 -/

/-- The master-scale density estimate without a pairwise-essential-distinctness hypothesis.

This predicate keeps the window, fullness, slab-count and interpolation assumptions
of `PlankEstimateAtMasterScaleWithDensity`, and its `Δmax(𝒫) ^ (1 - β)` factor.
Under `N`-fold repetition of a plank, multiplicity, maximal density and cardinality
scale by `N`, so the right side scales by `N ^ (1 - β) * N ^ β = N`.
Thus the density form is invariant under repetition. The version without this
hypothesis implies the version with it, by
`plankEstimateAtMasterScaleWithDensity_of_noED`.
-/
def PlankEstimateAtMasterScaleWithDensityNoED (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (s : Finset ι) {δ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
      (V : ι → ShadedPlank a b hab hb1),
      0 < δ → δ ≤ a → b ≤ b₀ →
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
      δ ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
      ∀ (γ : ℝ), 0 ≤ γ → γ ≤ 1 →
      (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
          ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
          ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
            ≤ δ ^ (-η) * φ ^ γ * (s.card : ℝ≥0)) →
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
          (δ : ENNReal) ^ (-ε)
            * (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β

set_option maxHeartbeats 1600000 in
/-- **The no-ED form of Lemma 6.1 implies the form the tree currently uses.**

Dropping a hypothesis strengthens the statement, so adopting
`Kakeya.PlankEstimateAtMasterScaleWithDensityNoED` costs no consumer anything.  This is the pin
that makes the proposed relaxation safe to consider. -/
theorem plankEstimateAtMasterScaleWithDensity_of_noED {β : ℝ}
    (h : PlankEstimateAtMasterScaleWithDensityNoED.{u} β) :
    PlankEstimateAtMasterScaleWithDensity.{u} β := by
  intro ε hε
  obtain ⟨η, hη, b₀, hb₀, H⟩ := h ε hε
  refine ⟨η, hη, b₀, hb₀, ?_⟩
  intro ι s δ a b hab hb1 V hδ hδa hbb₀ hwin _hed hfull γ hγ0 hγ1 hslab
  refine H (ι := ι) (s := s) (δ := δ) (a := a) (b := b) (hab := hab) (hb1 := hb1) (V := V)
    hδ hδa hbb₀ hwin hfull γ hγ0 hγ1 ?_
  exact hslab

/-! ### The conflict-degree bound without leaf-scale essential distinctness -/

/-- **`Kakeya.IsEDUpToMult` is hereditary.**  The non-essentially-distinct set only shrinks when
the ambient index set does. -/
theorem IsEDUpToMult.subset {ι : Type*} {E : Type*} [MeasureSpace E]
    {s t : Finset ι} {V : ι → Set E} {M : ℕ}
    (hED : IsEDUpToMult s V M) (hts : t ⊆ s) :
    IsEDUpToMult t V M := by
  classical
  intro i hi
  refine le_trans (Finset.card_le_card ?_) (hED i (hts hi))
  intro j hj
  simp only [notEssDistinctSet, Finset.mem_filter] at hj ⊢
  exact ⟨hts hj.1, hj.2⟩

/-- **The inner-plank conflict degree is bounded without assuming the fine tubes pairwise
essentially distinct.**

`Kakeya.exists_inner_plank_conflict_degree_bound` performs its count on the original fine tubes and
needs them pairwise essentially distinct: the geometric core
`Kakeya.exists_ED_directionCap_degree_bound` counts *essentially distinct* tubes in a fixed
container inside a single direction cap.  That hypothesis is exactly what GWZ Proposition 6.6(B)
does not carry.

Here it is replaced by `Kakeya.IsEDUpToMult q (fun i => (T i).carrier) M`, which
a caller must supply, and the degree bound degrades from `d` to `M + (M + 1) * d`.

The argument splits the plank-conflict set of `i` in two.  The members that are *not* essentially
distinct from `T i` number at most `M`, by the hypothesis.  The remaining ones are all essentially
distinct from `T i`, so a maximum-weight essentially distinct subfamily `B'` of them — losing at
most `M + 1` in cardinality — can be enlarged by `i` and still be pairwise essentially distinct.
`exists_inner_plank_conflict_degree_bound` applied to `insert i B'`, whose every member other than
`i` conflicts with `P i` by construction, bounds `|B'|` by `d`. -/
theorem exists_inner_plank_conflict_degree_bound_of_edUpToMult {kap : ℝ} (hkap : 0 < kap) :
    ∃ d : ℕ, 0 < d ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} {a b δ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (_ha : 0 < a) (_hδ0 : 0 < δ) (_hδle : (δ : ℝ) ≤ δ₀)
        {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
        (_ha'def : a' = δ / b) (_hb'def : b' = δ / a)
        (W : Plank a b hab hb1) (q : Finset ι)
        (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
        (P : ι → Plank a' b' ha'b' hb'1)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
        (F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
        (_hF : ∀ x, F x = f x) (_hJ : 0 < J)
        (_hnorm : Plank.IsPlankNormalisation W f kap g)
        (_hJab : J * (a * b) = Real.toNNReal kap ^ 3)
        (_hvolf : ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
            volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E)
              = (J : ENNReal) * volume E)
        (_hcarrier : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))))
        (_himg : ∀ i ∈ q, (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ''
            ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
        (_halign : ∀ i ∈ q, (P i).basis 2
            = (‖f.linear (T i).direction‖)⁻¹ • (f.linear (T i).direction))
        (_hortho : ∀ i ∈ q, (inner ℝ ((P i).basis 0) (g 0) : ℝ) = 0)
        {M : ℕ}
        (_hEDM : IsEDUpToMult q
            (fun i => ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) M),
        ∀ i ∈ q,
          edConflictDegree q
              (fun j => ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) i
            ≤ M + (M + 1) * d := by
  classical
  obtain ⟨d, hdpos, δ₀, hδ₀pos, hδ₀le, hbase⟩ :=
    exists_inner_plank_conflict_degree_bound hkap
  refine ⟨d, hdpos, δ₀, hδ₀pos, hδ₀le, ?_⟩
  intro ι a b δ hab hb1 ha hδ0 hδle a' b' ha'b' hb'1 ha'def hb'def W q T P f F J g
    hF hJ hnorm hJab hvolf hcarrier himg halign hortho M hEDM i hi
  set U : ι → Set (EuclideanSpace ℝ (Fin 3)) :=
    fun j => ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3))) with hU
  set A : Finset ι := notEssDistinctSet q U (U i) with hA
  set S : Finset ι :=
    ({j ∈ q | ¬ _root_.IsEssentiallyDistinct
      ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))} : Finset ι) with hS
  have hAcard : A.card ≤ M := hEDM i hi
  set B : Finset ι := S \ A with hB
  have hBq : B ⊆ q := fun j hj => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).1
  -- every member of `B` is essentially distinct from `T i`
  have hBED : ∀ j ∈ B, _root_.IsEssentiallyDistinct (U j) (U i) := by
    intro j hj
    obtain ⟨hjS, hjA⟩ := Finset.mem_sdiff.mp hj
    by_contra hcon
    exact hjA (by
      simp only [hA, notEssDistinctSet, Finset.mem_filter]
      exact ⟨hBq hj, hcon⟩)
  -- a maximum-weight essentially distinct subfamily of `B`
  obtain ⟨B', hB'sub, hB'pair, -, hB'card⟩ :=
    (hEDM.subset hBq).exists_pairwise_subset_with_weight_and_card
      (fun _ => (0 : ℝ)) (fun _ _ => le_rfl)
  have hB'q : B' ⊆ q := hB'sub.trans hBq
  -- `insert i B'` is pairwise essentially distinct
  have hins : (↑(insert i B') : Set ι).Pairwise
      (fun x y => _root_.IsEssentiallyDistinct (U x) (U y)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact _root_.isEssentiallyDistinct_symm (hBED y (hB'sub hy))
    · rcases hy with rfl | hy
      · exact hBED x (hB'sub hx)
      · exact hB'pair hx hy hxy
  have hinsq : insert i B' ⊆ q := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hi
    · exact hB'q hx'
  have hbase' := hbase ha hδ0 hδle ha'def hb'def W (insert i B') T P f F J g hF hJ hnorm hJab
    hvolf (fun j hj => hcarrier j (hinsq hj)) (fun j hj => himg j (hinsq hj))
    (fun j hj => halign j (hinsq hj)) (fun j hj => hortho j (hinsq hj)) hins
    i (Finset.mem_insert_self i B')
  -- `B'` sits inside the conflict set of `i` computed in `insert i B'`
  have hB'le : B'.card ≤ d := by
    refine le_trans (Finset.card_le_card ?_) hbase'
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_insert]
    refine ⟨Or.inr hj, ?_⟩
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hB'sub hj)).1).2
  -- assemble
  have hScard : S.card ≤ A.card + B.card := by
    have : S ⊆ (S ∩ A) ∪ B := by
      intro j hj
      by_cases hjA : j ∈ A
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hj, hjA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hj, hjA⟩)
    refine le_trans (Finset.card_le_card this) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    exact Nat.add_le_add_right (Finset.card_le_card Finset.inter_subset_right) _
  have hgoal : edConflictDegree q
      (fun j => ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) i = S.card := rfl
  rw [hgoal]
  calc S.card ≤ A.card + B.card := hScard
    _ ≤ M + (M + 1) * B'.card := Nat.add_le_add hAcard hB'card
    _ ≤ M + (M + 1) * d := Nat.add_le_add_left (Nat.mul_le_mul_left _ hB'le) _


/-- **The dimensional constant of the essentially-distinct reduction is finite.**  It is a quotient
of two `ENNReal.ofReal`s by a positive `ℝ≥0`; the fact was previously only available inline at a
single use site. -/
theorem refineToEssDistinctLeaves_C_three_ne_top :
    Tube.refineToEssDistinctLeaves.C 3 ≠ ⊤ := by
  rw [Tube.refineToEssDistinctLeaves.C]
  refine ENNReal.div_ne_top (ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top) ?_
  · rw [Tube.overlapContainment.C]
    exact ENNReal.ofReal_ne_top
  · exact_mod_cast (Tube.le_volume.c_pos 3).ne'

section InnerEDFamily

open Convexity ConvexSpaceBody
open scoped Real

/-- **The inner essentially-distinct plank family of Part (B), without leaf-scale essential
distinctness.**

`Kakeya.exists_inner_ED_family_of_partB` verbatim, with its pairwise-essential-distinctness
hypothesis on the fine tubes replaced by `Kakeya.IsEDUpToMult`, and every loss `d + 1` replaced by
`M + (M + 1) * d + 1`.  The proof is the same, with
`Kakeya.exists_inner_plank_conflict_degree_bound_of_edUpToMult` in place of
`Kakeya.exists_inner_plank_conflict_degree_bound`.

This is the statement in which the leaf-scale essential-distinctness obligation of GWZ Proposition
6.6(B) is reduced to the single number `M`.  What must then discharge `M` is **not** a new
hypothesis —  rejected that — but the accounting of
`Kakeya.multiplicity_bound_transfer_of_massShare` above, in which the loss is charged to the
`Δmax ^ (1 - β)` factor 6.6(B) already carries.

`M` is quantified *inside*, with the configuration, because it is a function of the family's
density; `d` and `δ₀` remain outside, as `Kakeya.factoringAndMultPropGlobal` needs them to be. -/
theorem exists_inner_ED_family_of_partB_of_edUpToMult {kap : ℝ} (hkap : 0 < kap)
    (cfac : ℝ≥0) (hcfac : 0 < cfac) :
    ∃ (Cnorm Cvol : ℝ≥0) (d : ℕ) (δ₀ : ℝ),
      1 ≤ Cnorm ∧ 1 ≤ Cvol ∧ 0 < d ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} [DecidableEq ι] {ιr : Type*} [DecidableEq ιr]
        {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (ha : 0 < a) (hδ0 : 0 < δ) (hδa : δ ≤ a) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρa : ρ ≤ a)
        (hδconf : (δ : ℝ) ≤ δ₀)
        (a₀ b₀ᵢ : ℝ≥0) (hsmalla : δ ≤ a₀ * b) (hsmallb : δ ≤ b₀ᵢ * a)
        (W : Plank a b hab hb1) (q : Finset ι) (r : Finset ιr)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF : ℝ≥0)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        0 < J →
        Plank.IsPlankNormalisation W f kap g →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1 →
        (∀ x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))), ‖f x - f W.center‖ ≤ 1) →
        cfac ≤ J * (a * b) →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∀ {M : ℕ},
        IsEDUpToMult q (fun i => ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) M →
        ∀ (data : CoarseParentSystem q r T R W Cfib CF m),
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1) (ιj : Type)
            (qj : Finset ιj) (P : ιj → ShadedPlank a' b' ha'b' hb'1),
            0 < a' ∧ δ ≤ a' ∧ b' ≤ b₀ᵢ ∧
            a' / b' = a / b ∧
            ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
            (∀ i ∈ qj, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
            (qj : Set ιj).Pairwise
              (fun i j => _root_.IsEssentiallyDistinct
                ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            q.card ≤ (M + (M + 1) * d + 1) * qj.card ∧ qj.card ≤ q.card ∧
            ShadedBody.fullness q (fun i => (T i).toShadedBody)
              ≤ Cnorm * (((M + (M + 1) * d : ℕ) : ℝ≥0) + 1)
                * ShadedBody.fullness qj (fun i => (P i).toShadedBody) ∧
            maxDensity qj (fun i => (P i).toConvexSpaceBody)
              ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
            (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
                ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
                ((Plank.inWideSlabFamily qj (fun i => (P i).toPrism3D) S).card : ℝ≥0)
                  ≤ (((M + (M + 1) * d : ℕ) : ℝ≥0) + 1)
                      * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
                      * φ ^ (1 : ℝ) * (qj.card : ℝ≥0)) ∧
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
              ≤ (((M + (M + 1) * d : ℕ) : ENNReal) + 1)
                * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := by
  classical
  obtain ⟨Cnorm, Cvol, hCnorm, hCvol, hinner⟩ := exists_inner_family_of_partB kap hkap cfac hcfac
  obtain ⟨d, hdpos, δ₀, hδ₀pos, hδ₀le, hdeg⟩ :=
    exists_inner_plank_conflict_degree_bound_of_edUpToMult hkap
  refine ⟨Cnorm, Cvol, d, δ₀, hCnorm, hCvol, hdpos, hδ₀pos, hδ₀le, ?_⟩
  intro ι _ ιr _ a b δ ρ hab hb1 ha hδ0 hδa hρ0 hρ1 hρa hδconf a₀ b₀ᵢ hsmalla hsmallb
    W q r T R m Cfib CF f J g hJ hnorm hvolf himg hWimg hJab hcarrier M hEDM data
  obtain ⟨a', b', ha'b', hb'1, Pj, ha'def, hb'def, ha'pos, hδa', ha'a₀, hb'b₀, hratioNN,
      hratioENN, hwindow, hfull, hmaxd, hslab, hshade, hcarrimg, halign, hortho⟩ :=
    hinner ha hδ0 hδa hρ0 hρ1 hρa a₀ b₀ᵢ hsmalla hsmallb W q r T R m Cfib CF f J g hJ hnorm hvolf
      himg hWimg hJab hcarrier data
  obtain ⟨F, hF⟩ := Plank.exists_affineEquiv_of_isPlankNormalisation ha W hkap hnorm
  have hJab_deg : J * (a * b) = Real.toNNReal kap ^ 3 :=
    Plank.jacobian_eq ha W hkap hnorm hvolf
  have hvolfF : ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
      volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E) =
        (J : ENNReal) * volume E := by
    intro E
    have himg : (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E =
        (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E :=
      congrArg (fun m : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) => m '' E)
        (funext hF)
    rw [himg]
    exact hvolf E
  have halignlin : ∀ i ∈ q, (Pj i).basis 2 =
      (‖f.linear (T i).direction‖)⁻¹ • (f.linear (T i).direction) := by
    intro i hi
    exact align_linear_of_align_sub (T i).toTube (Pj i).toPrism3D (halign i hi)
  have hdeg' : ∀ i ∈ q, edConflictDegree q (fun j => (Pj j).carrier) i ≤ M + (M + 1) * d := by
    intro i hi
    exact hdeg ha hδ0 hδconf (a' := a') (b' := b') (ha'b' := ha'b') (hb'1 := hb'1)
      ha'def hb'def W q (fun i => (T i).toTube) (fun i => (Pj i).toPrism3D)
      f F J g hF hJ hnorm hJab_deg hvolfF hcarrier hcarrimg halignlin hortho hEDM i hi
  let hpack := exists_inner_ED_factorisation_package q T Pj Cnorm
    (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol)) hCnorm hwindow hfull hmaxd hslab hdeg'
  let ιj := hpack.choose
  let hpack₁ := hpack.choose_spec
  let qj := hpack₁.choose
  let hpack₂ := hpack₁.choose_spec
  let P := hpack₂.choose
  let hpack₃ := hpack₂.choose_spec
  let _source := hpack₃.choose
  let hrest := hpack₃.choose_spec
  have hwin := hrest.2.2.1
  have hEDpair := hrest.2.2.2.1
  have hcard1 := hrest.2.2.2.2.1
  have hcard2 := hrest.2.2.2.2.2.1
  have hfull' := hrest.2.2.2.2.2.2.2.1
  have hmaxd' := hrest.2.2.2.2.2.2.2.2.1
  have hslab' := hrest.2.2.2.2.2.2.2.2.2.1
  have hmult := hrest.2.2.2.2.2.2.2.2.2.2
  have hmt : ShadedBody.multiplicity q (fun i => (Pj i).toShadedBody)
      = ShadedBody.multiplicity q (fun i => (T i).toShadedBody) :=
    inner_multiplicity_transport ha hkap W hnorm q T Pj hshade
  refine ⟨a', b', ha'b', hb'1, ιj, qj, P, ha'pos, hδa', hb'b₀, hratioNN, hratioENN, hwin,
    hEDpair, hcard1, hcard2, hfull', hmaxd', hslab', ?_⟩
  calc
    ShadedBody.multiplicity q (fun i ↦ (T i).toShadedBody) =
        ShadedBody.multiplicity q (fun i ↦ (Pj i).toShadedBody) := hmt.symm
    _ ≤ (((M + (M + 1) * d : ℕ) : ENNReal) + 1) *
        ShadedBody.multiplicity qj (fun i ↦ (P i).toShadedBody) := hmult

end InnerEDFamily

end Kakeya

end

end
