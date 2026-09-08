/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.DensityTransfer
public import Kakeya.DimensionThree.MainLemma1.TwoLoads

/-!
# Main Lemma 1, Step 5a: the anchor denominator, from the factoring and from the count

Blueprint `lem:ml1bootAnchorDenominatorFromFactoring` and the continuation
`section8_step5a_anchor_denominator_count.tex`.  The first statement,
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization`, **is an instance and not an
argument**: it is `Kakeya.ml1Boot.frostmanConstIn_anchor_le` of
`Kakeya/DimensionThree/MainLemma1/Rescaling/DensityTransfer.lean` read at `L = D / C_fact`, with the
`denom_pos`/`denom_le` half of that lemma's denominator bundle
`Kakeya.ml1Boot.IsAnchorDenominator` — and only that half, the placement half
`Kakeya.ml1Boot.IsAnchorPlacement` being carried unchanged — replaced by the two links of the
source's Step 5c route to `L` that this development already has.  The remaining
statements write the third link at one tested body and read the first statement at the `D` it
produces.

## What it is, and what it is not

Item (i) of blueprint `note:ml1bootAnchorFromLoadStatus` records the denominator `L` of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le` as the one owed item of which nothing at all is written.
The source reaches it in three links:

* (A) the **plank density identity** — for a block `t` of the factoring,
  `Δ_max(𝕍|_{s'}) ≤ C_fact · Δ(𝕍|_t, W)`, so that a lower bound for `Δ_max` of the retained share is
  a lower bound for the density *at the plank*, which is what the denominator hypothesis asks for;
* (B) the **maximal-density comparison** — `Δ_max(𝕍|_{s'}) ≥ Δ(𝕍|_{s'}, B)` at *any* tested body
  `B`, the source reading it at its `B_{2C₀}`;
* (C) the **count at that tested body** — `Δ(𝕍', B_{2C₀}) ≳ N_m δ̃ ²`, because `𝕍'` retains a
  `≳ 1`-share of the completed fibre and each member has volume `≈ δ̃ ²`.

Links (A) and (B) *are* in this development: (A) is `ConvexSpaceBody.Factorization.maxDensity_le_mul`
of `Kakeya/Factorization.lean`, a structure field, holding at `C_fact = 2` at the one producer this
development has, `ConvexSpaceBody.nonempty_factorization.factorization`; and (B) is
`Kakeya.le_maxDensity` of `Kakeya/Density.lean`, which is `Kakeya.maxDensity` read as the supremum it
is.  `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` writes the composition of those
two, leaving the third as the explicit hypothesis `hD` at a *free* tested body.

## Link (C), at one tested body

The rest of the file writes link (C) at the tested body `B = P_a(l)^{(Λ ρ_a)}` — an earlier version
of this docstring recorded link (C) as having no Lean declaration anywhere, which these statements
make false.  It is a count, `Kakeya.densityIn_ge_of_count_volume`, at two inputs:

* (C1) the **cardinality** `|\widetilde{𝒰'_b}(l)| ≥ Cu ⁻³ (N_a/N_b)` at the completed *unrefined*
  fibre — `Kakeya.ml1Boot.branchingRatio_le_card_completedFibre` of
  `Kakeya/DimensionThree/MainLemma1/TwoLoads.lean`, the composition of the lower half of the
  uniformity bracket with `Kakeya.ml1Boot.fibre_subset_completedFibre`, which is why this file now
  carries an import edge to that one;
* (C2) the **placement**, which at this tested body asks nothing at all: every member of the
  completion satisfies `P_b(k) ≤ B` *by the definition of* `Kakeya.ml1Boot.completedFibre`, so no
  cover, no enlargement lemma and no containment hypothesis on `B` occurs.  That is the reason link
  (C) is reachable here and only here, and the reason the statements are at the un-normalized grid
  scales `θ = ρ_a`, `τ = ρ_b`.

`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share` is the count, at a free retained subfamily
meeting the completion in a `κ`-share;
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_volume_share` is that count again with the
cardinality share replaced by the *volume* share that
`ConvexSpaceBody.nonempty_factorization.weight_subfamily` delivers — that lemma, and **not**
`ConvexSpaceBody.nonempty_factorization.factorization`, which is where link (A) comes from and says
nothing about a share — the two shares being interchangeable at the same `κ` for a family of tubes
of one common positive radius (`Tube.mul_sum_volume_le_iff_mul_card_le`);
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share_normalized`
divides by the upper volume bracket of `Kakeya.ml1Boot.volume_testedBody_bracket` to reach the
source's `≳ N_m (τ/Λθ) ²` shape; and `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count` reads
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` at the `D` the first of those produces,
which discharges `hD` — **and only `hD`**.

**The share is a hypothesis and nothing here produces it.**  It is *not* the fibrewise share of
blueprint `note:ml1bootEssDistinctFibrewiseShare`, which is stated relative to the *fibre* and is
therefore, at equal `κ`, a weaker demand than the one made here relative to the larger completion;
that note is **open and blocking** and nothing here reopens, weakens or closes it.  No essential
distinctness is asked and none is used.

**This is a change of shape, not a supplier.**  Nothing here produces a number `L`: what it does is
replace the bare lower bound `Δ(𝕍|_t, W) ≥ L` — a hypothesis about the *plank*, which no counting
argument in this development reaches directly — by a lower bound `Δ(𝕍|_{s'}, B) ≥ D` at a free
tested body `B`, which is the shape a counting argument *could* reach.  Everything else is carried
unchanged, in particular the two placement conditions `W ≤ K` and `|K| ≤ C_T (bp/ap) |W|`, which are
the plank-body placement gap of blueprint `note:ml1bootEnlargementTubeStatus` and are **not** touched
here, and the numerator hypothesis `hnum`, which is verbatim.  Blueprint
`note:ml1bootAnchorDenominatorStatus` itemizes all of this.

## `lemmafactmax` is not applied, and `s'` and `t` need not come from it

Only the *inequality* (A) is asked, as the hypothesis `hfact`.  Obtaining it by applying
`ConvexSpaceBody.nonempty_factorization.factorization` at `𝕍|_{s'}` would require that lemma's own
hypotheses at the un-normalized family of `τ`-tubes — containment in a unit ball and a lower bound on
the `ethickness` — and, in the normalized picture of `Kakeya.ml1Boot.tubeNormalizedFamily`, the
transport of the factoring across the normalization.  **Neither is performed**; stating the lemma at
the inequality is what keeps that obligation visible at the caller.  For the same reason
`Kakeya/Factorization.lean` is **not** imported by this file: nothing here reads the structure.

## It stands beside everything it reads and revises none of it

`Kakeya.ml1Boot.frostmanConstIn_anchor_le` is applied once, at one value of `L`, and is neither
edited nor weakened nor re-derived; `ConvexSpaceBody.Factorization` and `Kakeya.le_maxDensity` are
untouched; and neither
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_load`,
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents`,
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_uniformity` nor
`Kakeya.ml1Boot.plankWidth_le_of_anchor` is re-pointed at it.  No new constant is introduced,
deliberately: the only constants displayed are `C_T = Kakeya.ml1Boot.densityTransfer.C` and the
factoring constant `C_fact`, which is *data* here.

## This does not make (5.10b) unconditional

`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` leaves the numerator `U`, the placement
of `W` in `K`, and link (C) exactly as it found them, and says nothing about the Step 5c anchor —
nothing here relates `K` to the body `2 · T_b` of `Kakeya.ml1Boot.plankWidth_le_of_anchor`.  **It is
not a supplier for `L` and may not be reported as one**: it produces no number, and a caller must
still produce the `D` of `hD`.  `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count` is that caller,
and it commits in the open the reading of `D` as a constant multiple of `N_m τ ²` with
`N_m = N_a/N_b` — *not* as `N_m δ̃ ²`: the passage to the `δ̃` of
`Kakeya.ml1Boot.tubeNormalizedFamily` is a transport that is **not performed anywhere** in this
development, so `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share_normalized` may not be quoted as
the source's display.

What stands between this and an unconditional (5.10b) is therefore, exactly: the **share**; the
**plank-body placement** `W ≤ K` with `|K| ≤ C_T (bp/ap) |W|`, which is the gap of blueprint
`note:ml1bootEnlargementTubeStatus` and is carried verbatim, nothing here relating `K` to `B`; the
**factoring datum**, quoted as the inequality `hfact` rather than obtained from
`ConvexSpaceBody.nonempty_factorization.factorization`, whose own hypotheses at the un-normalized
family — containment in a unit ball and a lower bound on the `ethickness` — remain the caller's
obligation, which is also why `Kakeya/Factorization.lean` is still **not** imported here; the
**normalization transport**; and the **Step 5c anchor transport**.  An assembly of conditional inputs
is a conditional statement.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody StickyKakeya Tube Convexity

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The anchor denominator, from the factoring** (blueprint
`lem:ml1bootAnchorDenominatorFromFactoring`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  Let `dim_ℝ E = 3`, let `0 < ap ≤ bp`, let
`𝕍 = (T k)_{k ∈ u''}` be a family of `δ̃`-tubes and let `K` be a convex body, the *anchor*, these
being as in `Kakeya.ml1Boot.frostmanConstIn_anchor_le`.  Assume that lemma's numerator hypothesis
`hnum` **unchanged**: `Δ(𝕍, K') ≤ U` for every convex body `K' ≤ K`.  In place of its denominator
hypothesis, assume three groups, in which `𝕍|_v = (T k)_{k ∈ v}`:

* *the block and its plank* — `s' ⊆ u''` together with a
  `Kakeya.ml1Boot.IsAnchorPlacement` for `(𝕍, K, ap, bp)` at the ambient `s'`: a nonempty
  `t ⊆ s'` such that, writing `W = conv (⋃_{k ∈ t} T k)`, one has `W ≤ K` and
  `|K| ≤ C_T (bp/ap) |W|`.  This is the placement half of the denominator hypothesis of
  `Kakeya.ml1Boot.frostmanConstIn_anchor_le`, which is why the bundle carries its ambient index
  set as a parameter: it is read here at `t ⊆ s'` with a separate `s' ⊆ u''`;
* *the factoring datum* — a `C_fact` with `0 < C_fact < ∞` and
  `Δ_max(𝕍|_{s'}) ≤ C_fact · Δ(𝕍|_t, W)`.  This is link (A), the plank density identity: it is
  exactly `ConvexSpaceBody.Factorization.maxDensity_le_mul` read at the block `t`, so at the retained
  share and the partition that produces it holds with `C_fact = 2`, with `s'` the heavy subfamily and
  `t` one of its blocks;
* *the count at a tested body* — a convex body `B` and a `D` with `0 < D < ∞` such that
  `Δ(𝕍|_{s'}, B) ≥ D`.  This is link (C), **taken on trust**: `B` is free, so a caller may read it at
  the source's `B_{2C₀}` or at anything else.

Then `C_F(𝕍[K], K) ≤ C_T (bp/ap) · C_fact · U / D`.

*Intended proof.*  Put `L = D / C_fact` and read `Kakeya.ml1Boot.frostmanConstIn_anchor_le` at it.
One density step: `Kakeya.le_maxDensity` — link (B) — gives
`D ≤ Δ(𝕍|_{s'}, B) ≤ Δ_max(𝕍|_{s'}) ≤ C_fact · Δ(𝕍|_t, W)`.  Three arithmetic steps in `[0, ∞]`,
each spending only `0 < C_fact < ∞` and `0 < D < ∞`: that `L` is positive and finite; that dividing
the chain by `C_fact` gives `L ≤ Δ(𝕍|_t, W)`, the fourth display; and that `U / L = C_fact · U / D`,
the only rewriting done to the right-hand side.  The block `t` lies in `u''` because
`t ⊆ s' ⊆ u''`.

**Why the finiteness of `C_fact` is asked and that of `D` is not.**
`Kakeya.ml1Boot.frostmanConstIn_anchor_le` asks `0 < L < ∞` — positive because its proof divides by
`L`, finite because in `[0, ∞]` the identity `(U/L) · L = U` fails at `L = ∞`.  Positivity of
`L = D / C_fact` costs `0 < D` and `C_fact ≠ ∞`, and its finiteness costs `0 < C_fact` and
`D ≠ ∞`; of these four only the first three are binders, `D ≠ ∞` being derived (see below).  Each
is free at every intended reading: `C_fact = 2` at the factoring, and `D` is *meant* to be a
constant multiple of `N_m δ̃ ²`.  **No upper bound on `Δ_max(𝕍|_{s'})` is asked**, although the
proof does spend `Kakeya.maxDensity_ne_top`, which is `Kakeya.maxDensity_le_card` at the finite
`s'`.

**Both owed removals have been made.**  The former `hcapture` binder is gone: it was automatic —
each `T k` with `k ∈ t` lies in the convex hull of the union over `t`, so `𝕍|_t[W] = t` holds for
the plank of *any* block — and it is now the step
`Kakeya.ml1Boot.familyIn_convexHull_biUnion_self` of the proof, which is also why
`Kakeya.ml1Boot.IsAnchorPlacement` does not carry it as a field.  The former `hDtop` binder is gone
too, and for the same reason: `hD` already forces it, since
`D ≤ Δ(𝕍|_{s'}, B) ≤ Δ_max(𝕍|_{s'}) ≠ ∞` by `Kakeya.le_maxDensity` and
`Kakeya.maxDensity_ne_top` at the finite index set `s'`.  That derivation is *not* the one
`Kakeya.ml1Boot.IsAnchorDenominator.denom_ne_top` performs — it runs at the tested body `B` and at
`s'`, not at the plank and the block — but it is the same two lemmas, and it is now the step
`hDtop` of the proof, taken off the middle of the chain `hDmax` that the argument computes anyway.
Dropping the binder weakens the hypotheses: the former form is the instance of the present one at a
caller who happens to hold `D ≠ ∞`.  `hCfact0`, `hCfactTop` and `hD0` are *not* of this kind:
`C_fact` is free data, and the positivity of `D` is what makes the denominator positive, so none
follows from anything assumed.

**Conditional, and it supplies no `L`.**  See the module docstring: `hfact` is link (A) quoted as a
hypothesis rather than obtained, `hD` is link (C) and has no supplier in this development at all, and
the placement and the Step 5c transport are left exactly where they were. -/
theorem frostmanConstIn_anchor_le_of_factorization (hdim : Module.finrank ℝ E = 3)
    {δt ap bp : NNReal} (hap0 : 0 < ap) (hab : ap ≤ bp)
    {ι : Type*} {u'' s' t : Finset ι} (T : ι → Tube δt E) (K : ConvexSpaceBody E)
    {U : ENNReal}
    (hnum : ∀ K' : ConvexSpaceBody E, K' ≤ K →
      densityIn u'' (fun k => (T k).toConvexSpaceBody) K' ≤ U)
    (hs'u : s' ⊆ u'') (hplace : IsAnchorPlacement T K ap bp s' t)
    {Cfact : ENNReal} (hCfact0 : 0 < Cfact) (hCfactTop : Cfact ≠ ⊤)
    (hfact : maxDensity s' (fun k => (T k).toConvexSpaceBody)
      ≤ Cfact * densityIn t (fun k => (T k).toConvexSpaceBody)
        (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody))
    (B : ConvexSpaceBody E) {D : ENNReal} (hD0 : 0 < D)
    (hD : D ≤ densityIn s' (fun k => (T k).toConvexSpaceBody) B) :
    frostmanConstIn (familyIn u'' (fun k => (T k).toConvexSpaceBody) K)
        (fun k => (T k).toConvexSpaceBody) K
      ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) *
          (Cfact * U / D) := by
  classical
  let V : ι → ConvexSpaceBody E := fun k => (T k).toConvexSpaceBody
  let W : ConvexSpaceBody E := t.convexHull_biUnion V
  let L : ENNReal := D / Cfact
  have hDmax : D ≤ maxDensity s' V := by
    calc
      D ≤ densityIn s' V B := hD
      _ ≤ maxDensity s' V := le_maxDensity (s := s') (W := V) B
  have hDtop : D ≠ ⊤ := ne_top_of_le_ne_top (maxDensity_ne_top s' V) hDmax
  have hchain : D ≤ Cfact * densityIn t V W := by
    calc
      D ≤ maxDensity s' V := hDmax
      _ ≤ Cfact * densityIn t V W := by
        simpa [V, W] using hfact
  have hL : L ≤ densityIn t V W := by
    dsimp [L]
    rw [ENNReal.div_le_iff (ne_of_gt hCfact0) hCfactTop]
    simpa [mul_comm] using hchain
  have hL0 : 0 < L := by
    dsimp [L]
    rw [pos_iff_ne_zero, ENNReal.div_ne_zero]
    exact ⟨ne_of_gt hD0, hCfactTop⟩
  have hUdiv : U / (D / Cfact) = Cfact * U / D := by
    rw [← ENNReal.div_mul (a := U) (b := D) (c := Cfact)
      (h0 := Or.inr (ne_of_gt hCfact0)) (htop := Or.inl hDtop)]
    simp [ENNReal.div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm]
  have hanch : IsAnchorDenominator T K ap bp u'' t L :=
    { block_subset := hplace.block_subset.trans hs'u
      block_nonempty := hplace.block_nonempty
      plank_le := hplace.plank_le
      volume_le := hplace.volume_le
      denom_pos := hL0
      denom_le := hL }
  have hgoal : frostmanConstIn (familyIn u'' V K) V K
      ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * (U / L) := by
    exact frostmanConstIn_anchor_le (hdim := hdim) (δt := δt) (ap := ap) (bp := bp)
      (hap0 := hap0) (hab := hab) (ι := ι) (u'' := u'') (t := t) (T := T) (K := K) (U := U) (L := L)
      (hnum := hnum) (hanch := hanch)
  dsimp [L] at hgoal
  rwa [hUdiv] at hgoal

/-! ### Link (C): the count at the tested body

The tested body is `B = P_a(l)^{(Λ ρ_a)}`, the concentric radius-rescaling
`(𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)`, which in Lean *is* a tube of radius `Λ ρ_a` by
typing — `Kakeya.Tube.rescale` returns a `Tube` of the new radius — so the three tube-volume facts
apply to it directly.  Throughout this section `sl` is the leaf set of the hierarchy and `s'` is the
retained subfamily of `𝒰'_b` that the source calls `𝕍'`; the letter `s'` is the source's and is not
the leaf set, which the neighbouring Step 5a files write `s'` instead. -/

/-- **The volume of the tested body** (blueprint `lem:ml1bootTestedBodyVolume`).

For `B = P_a(l)^{(Λ θ)}` with `θ = ρ_a`, in the ambient `ℝ ³`:

* `|B| ≥ c(3) (Λθ) ²` **unconditionally**, by `Kakeya.Tube.le_volume`, which asks nothing at all of
  the radius of its tube;
* if `0 < Λθ ≤ 1` then `|B| ≤ C(3) (Λθ) ²` and `0 < |B| < ∞`, by `Kakeya.Tube.volume_le` and
  `Kakeya.Tube.volume_pos_and_lt_top`.

**The second group is behind its own implication and not merged into the binders**, because the two
volume lemmas ask different things of the radius: the lower bound asks nothing, whereas the upper
bound needs `Λθ ≤ 1` and the finiteness needs `0 < Λθ ≤ 1`.  In particular the finiteness `|B| < ∞`
belongs to the second group and may **not** be read off the first, and the first carries **no**
positivity binder — an earlier version put it behind `Λθ > 0` only in order to append a `0 < |B|`
that no consumer reads.  `Λ ≥ 1` is not asked either: the statement is about one rescaled grid tube
and reads no relation between the new radius and the old.  No node of level `b`, no parent map and no
fibre occurs. -/
theorem volume_testedBody_bracket (hdim : Module.finrank ℝ E = 3) {ι : Type*} {δ : NNReal}
    {sl : Finset ι} {T : ι → Tube δ E} {N a : ℕ} {Cu : NNReal}
    (𝒰' : UniformTubeSet sl T N Cu) (l : ι) (Λ : NNReal) :
    ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal)
          * ((Λ * gridScale δ N a : NNReal) : ENNReal) ^ 2
        ≤ volume ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).carrier
      ∧ (0 < Λ * gridScale δ N a → Λ * gridScale δ N a ≤ 1 →
        volume ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).carrier
            ≤ ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal)
              * ((Λ * gridScale δ N a : NNReal) : ENNReal) ^ 2
          ∧ 0 < volume ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).carrier
          ∧ volume ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).carrier < ⊤) := by
  refine ⟨?_, fun h0 h1 => ?_⟩
  · simpa [hdim] using _root_.Tube.le_volume
      ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a))
  · refine ⟨?_, ?_, ?_⟩
    · simpa [hdim] using _root_.Tube.volume_le h1
        ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a))
    · exact (_root_.Tube.volume_pos_and_lt_top h0 h1
        ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a))).1
    · exact (_root_.Tube.volume_pos_and_lt_top h0 h1
        ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a))).2

/-- **The small constant of the count at the tested body** (blueprint
`def:ml1bootAnchorCountConstant`), the product of the three inputs already carried by the count: the
share `κ`, the power `Cu ⁻³` of the lower half of the uniformity bracket
(`Kakeya.ml1Boot.branchingRatio_le_card_coarseFibre`), and the reverse tube-volume constant
`Kakeya.Tube.le_volume.c`.

It depends only on the ambient dimension, on the uniformity constant of the hierarchy and on the
share — on no grid scale, no branching number and no `δ` — and is read below at `n = 3`.  It is
positive whenever `0 < κ` and `Cu ≠ 0`, each factor being so, and it is *small*, hence the lower-case
name.  The share is written `κ` and not `σ`, the letter `σ` being a tube width in the neighbouring
Step 5a files. -/
noncomputable def anchorCountAtTestedBody.c (n : ℕ) (Cu κ : NNReal) : NNReal :=
  κ * (Cu ^ 3)⁻¹ * _root_.Tube.le_volume.c n

/-! ### The arithmetic of the constant and of the numerator

Six arithmetic statements are named at the end of blueprint
`section8_step5a_anchor_denominator_count.tex` so that the granularity debt recorded at
item (countLean) of `note:ml1bootAnchorDenominatorCountStatus` has something to discharge it: each
is a fact that one of the three long proofs below already establishes inline, and writing it out
separately changes no hypothesis, no constant and no conclusion.  The four that mention the constant
`Kakeya.ml1Boot.anchorCountAtTestedBody.c` stand here; the two that mention no tube, no grid, no
hierarchy and no density — `ENNReal.div_div_eq_mul_div` and `NNReal.div_mul_div_sq_eq` with its
image `ENNReal.coe_div_mul_coe_div_sq_eq` — stand in `Kakeya/Mathlib/ENNReal.lean` beside this
development's other generic `[0, ∞]` arithmetic.

**None of them is cited by anything above yet.**  They are stated; rewriting the three proofs
through them is a separate step, and until it is done the inline copies remain. -/

/-- **The constant of the count is positive** (blueprint
`lem:ml1bootAnchorCountConstantPos`).

`0 < c(n, Cu, κ)` whenever `0 < Cu` and `0 < κ`: by
`Kakeya.ml1Boot.anchorCountAtTestedBody.c` the constant is the product
`κ · (Cu ³)⁻¹ · c_{le_volume}(n)` of three positive factors — `κ` by hypothesis, `(Cu ³)⁻¹` because
`Cu > 0` and inversion is positive on positives, and `c_{le_volume}(n)` by
`Kakeya.Tube.le_volume.c_pos`.

**Only `0 < Cu` is asked, where the blueprint displays `C_ds ≥ 1`.**  Positivity is all the
inversion reads — in `NNReal`, `x⁻¹` is positive exactly when `x` is nonzero — so asking the
formally weaker hypothesis makes this the formally stronger statement; every consumer carries
`1 ≤ Cu` anyway, that being part of `Kakeya.uniformTubeSet`.

This is the positivity asserted in the display of blueprint `def:ml1bootAnchorCountConstant`, which
is at present unfolded and re-proved inline at each of the two places that need it — about eight of
the seventy lines of `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count` and a further few inside
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`.  *A positivity fact about a named constant
belongs once, at the constant.*

**No upper bound on `κ` is asked**, `κ ≤ 1` being dead here exactly as it is at
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`. -/
theorem anchorCountAtTestedBody.c_pos (n : ℕ) {Cu κ : NNReal} (hCu : 0 < Cu) (hκ0 : 0 < κ) :
    0 < anchorCountAtTestedBody.c n Cu κ := by
  dsimp [anchorCountAtTestedBody.c]
  have hCu3Pos : 0 < Cu ^ 3 := pow_pos hCu 3
  have hInvPos : 0 < (Cu ^ 3)⁻¹ := by
    positivity
  have hTubePos : 0 < _root_.Tube.le_volume.c n := Tube.le_volume.c_pos n
  exact mul_pos (mul_pos hκ0 hInvPos) hTubePos

/-- **The image of the constant in `[0, ∞]` is nonzero** (blueprint
`lem:ml1bootAnchorCountConstantPos`, second assertion).

`Kakeya.ml1Boot.anchorCountAtTestedBody.c_pos` through `ENNReal.coe_ne_zero`.  This is the form the
two consumers actually read, both of them working in `[0, ∞]`.

**The third assertion of that blueprint lemma — that the image is different from `∞` — is
`ENNReal.coe_ne_top` verbatim** and is deliberately *not* restated here: the coercion
`[0, ∞) → [0, ∞]` carries no nonnegative real to `∞`, with no hypothesis on the constant at all. -/
theorem anchorCountAtTestedBody.coe_c_ne_zero (n : ℕ) {Cu κ : NNReal} (hCu : 0 < Cu)
    (hκ0 : 0 < κ) :
    ((anchorCountAtTestedBody.c n Cu κ : NNReal) : ENNReal) ≠ 0 := by
  exact ENNReal.coe_ne_zero.mpr (ne_of_gt (anchorCountAtTestedBody.c_pos n hCu hκ0))

/-- **The share composed with the branching lower bound** (blueprint
`lem:ml1bootAnchorCountShareCompose`).

If `(Cu ³)⁻¹ · p ≤ m'` and `κ · m' ≤ m` then `(κ · (Cu ³)⁻¹) · p ≤ m`.

Read at `p = N_a/N_b`, at `m' = |\widetilde{𝒰'_b}(l)|` and at `m = |r|` this is the share hypothesis
of `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share` composed with
`Kakeya.ml1Boot.branchingRatio_le_card_completedFibre` and then reassociated so that the two
constant factors `κ` and `(Cu ³)⁻¹` stand together — which is the shape
`Kakeya.ml1Boot.anchorCountAtTestedBody.numerator_le` consumes, and the shape in which they are the
two constant factors of `Kakeya.ml1Boot.anchorCountAtTestedBody.c`.  It is about eight of the
fifty-five lines of `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`, namely the step from
`hbr` and `hshr` to `hrcard`.

**The statement is monotonicity and transitivity and nothing else.**  No positivity is asked of any
of the four quantities, the nonnegativity that makes the multiplication monotone being carried by
the type `NNReal`; at `κ = 0` or `p = 0` it is trivial.  The blueprint's `Cu ≥ 1` is *not* a binder:
it is read nowhere in the argument, so asking it would be a dead hypothesis, and dropping it makes
this the formally stronger statement. -/
theorem anchorCountAtTestedBody.share_compose {Cu κ p m m' : NNReal}
    (hbr : (Cu ^ 3)⁻¹ * p ≤ m') (hshare : κ * m' ≤ m) :
    κ * (Cu ^ 3)⁻¹ * p ≤ m := by
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left hbr (by positivity)).trans hshare

/-- **The constant against the retained count** (blueprint
`lem:ml1bootAnchorCountConstantAgainstCount`).

From `κ · (Cu ³)⁻¹ · p ≤ m`, at every ambient dimension `n`,

```
c(n, Cu, κ) · p · τ ² ≤ m · (c_{le_volume}(n) · τ ²).
```

Unfold the constant and regroup the left-hand side as `(κ · (Cu ³)⁻¹ · p) · (c_{le_volume}(n) τ ²)`,
a commutative-semiring rearrangement; multiplying the hypothesis by the nonnegative
`c_{le_volume}(3) τ ²` is monotone and gives the display.

**The right-hand side is deliberately grouped as `m` times a minimum volume**, that being the shape
`Kakeya.densityIn_ge_of_count_volume` consumes.  Read at `m = |r|`, at `p = N_a/N_b` and at
`τ = ρ_b` it is the whole of the passage from the constant to that shape: about twenty of the
fifty-five lines of `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`, the block `hnn`, and
about thirty together with `Kakeya.ml1Boot.anchorCountAtTestedBody.share_compose`, which supplies
its hypothesis.

**Nothing is asked to be positive**, so `τ = 0` and `κ = 0` are admitted, exactly as they are at
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`, where the display is then the trivial bound.
The blueprint's `Cu ≥ 1` is again not a binder, being read nowhere in the argument.

**The dimension is free, where the blueprint displays `n = 3`.**  No dimension fact is read: the
rearrangement is a commutative-semiring identity and `Kakeya.Tube.le_volume.c` is defined at every
`n`.  The exponent `3` on `Cu` is not the dimension — it is the power of the uniformity constant
carried by `Kakeya.ml1Boot.branchingRatio_le_card_completedFibre` — and stays fixed. -/
theorem anchorCountAtTestedBody.numerator_le (n : ℕ) {Cu κ p τ m : NNReal}
    (h : κ * (Cu ^ 3)⁻¹ * p ≤ m) :
    anchorCountAtTestedBody.c n Cu κ * p * τ ^ 2
      ≤ m * (_root_.Tube.le_volume.c n * τ ^ 2) := by
  dsimp [anchorCountAtTestedBody.c]
  calc
    (κ * (Cu ^ 3)⁻¹ * _root_.Tube.le_volume.c n) * p * τ ^ 2
        = (κ * (Cu ^ 3)⁻¹ * p) * (_root_.Tube.le_volume.c n * τ ^ 2) := by ring
    _ ≤ m * (_root_.Tube.le_volume.c n * τ ^ 2) := by
          exact mul_le_mul h (le_rfl) (by positivity) (by positivity)

/-- **The constant against the retained count, in `[0, ∞]`** (blueprint
`lem:ml1bootAnchorCountConstantAgainstCount`, second display).

The image of `Kakeya.ml1Boot.anchorCountAtTestedBody.numerator_le` under the coercion
`[0, ∞) → [0, ∞]`, which is a monotone ring homomorphism (`ENNReal.coe_le_coe`, `ENNReal.coe_mul`,
`ENNReal.coe_pow`) and so carries the inequality to the corresponding one.

**This is the form the count actually reads**: it is the step `hnumEN` of
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`, at `m = |r|` and with the right-hand
bracket the `vmin` of that proof, read there at `n = 3`; here the dimension is free, the coercion
reading no dimension fact any more than
`Kakeya.ml1Boot.anchorCountAtTestedBody.numerator_le` does. -/
theorem anchorCountAtTestedBody.coe_numerator_le (n : ℕ) {Cu κ p τ m : NNReal}
    (h : κ * (Cu ^ 3)⁻¹ * p ≤ m) :
    (anchorCountAtTestedBody.c n Cu κ : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2
      ≤ (m : ENNReal) *
        (((_root_.Tube.le_volume.c n : NNReal) : ENNReal) * (τ : ENNReal) ^ 2) := by
  exact_mod_cast anchorCountAtTestedBody.numerator_le n h

/-- **The numerator of the count is nonzero in `[0, ∞]`** (blueprint
`lem:ml1bootAnchorCountNumeratorPosFinite`, first assertion).

Each of the three factors is the image of a nonzero nonnegative real — the constant by
`Kakeya.ml1Boot.anchorCountAtTestedBody.coe_c_ne_zero`, and `p` and `τ ²` by hypothesis — so each is
nonzero by `ENNReal.coe_ne_zero`, and in `[0, ∞]` a product of nonzero factors is nonzero.

Read at `p = N_a/N_b` — positive when `0 < N_a` and `0 < N_b` — and at `τ = ρ_b`, this is the
positivity `0 < D` that `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` asks, as it is
read off inside `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count`: the factorwise ladder
`hF1ne`–`hX0ne` there.

**It says nothing about `|B|`**, which is not a factor of it and whose bracket is a separate
input.

**The dimension is free and only `0 < Cu` is asked**, where the blueprint displays `n = 3` and
`C_ds ≥ 1`: the hypothesis is passed straight to
`Kakeya.ml1Boot.anchorCountAtTestedBody.coe_c_ne_zero`, which asks no more, and no dimension fact is
read. -/
theorem anchorCountAtTestedBody.coe_numerator_ne_zero (n : ℕ) {Cu κ p τ : NNReal} (hCu : 0 < Cu)
    (hκ0 : 0 < κ) (hp0 : 0 < p) (hτ0 : 0 < τ) :
    (anchorCountAtTestedBody.c n Cu κ : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2 ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (anchorCountAtTestedBody.coe_c_ne_zero n hCu hκ0)
      (ENNReal.coe_ne_zero.mpr (ne_of_gt hp0)))
    (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (ne_of_gt hτ0)))

/-- **The numerator of the count is finite in `[0, ∞]`** (blueprint
`lem:ml1bootAnchorCountNumeratorPosFinite`, second assertion).

Each factor is the image of a nonnegative real, hence `≠ ∞` by `ENNReal.coe_ne_top` (with
`ENNReal.pow_ne_top` for the square), and in `[0, ∞]` a product of finite factors is finite by
`ENNReal.mul_ne_top`.  **No positivity is asked**: unlike
`Kakeya.ml1Boot.anchorCountAtTestedBody.coe_numerator_ne_zero`, finiteness costs nothing, and this
is the ladder `hF1top`–`hX0neTop` of `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count`, whose
finiteness `D ≠ ∞` is derived rather than asked but is spent at the inversion of `D`.  **The
dimension is free**, exactly as at the three statements above and for the same reason. -/
theorem anchorCountAtTestedBody.coe_numerator_ne_top (n : ℕ) (Cu κ p τ : NNReal) :
    (anchorCountAtTestedBody.c n Cu κ : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2 ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)

/-- **(GWZ Step 5a bullet (b)) The count at the tested body** (blueprint
`lem:ml1bootAnchorCountAtTestedBody`).

With `B = P_a(l)^{(Λ θ)}` the tested body, `𝕍 = (P_b(k))_{k ∈ 𝒰'_b}` the **unrefined** level-`b`
family, `s'` a retained subfamily meeting the completion `\widetilde{𝒰'_b}(l)` in a `κ`-share,

```
Δ(𝕍|_{s'}, B) ≥ c(3, Cu, κ) · (N_a / N_b) · τ ² / |B|.
```

`Kakeya.densityIn_ge_of_count_volume` at the subfamily `r = s' ∩ \widetilde{𝒰'_b}(l)`, at the body
`B` and at `v = c_{le_volume}(3) τ ²`.  Its two hypotheses are free: the containment `P_b(k) ≤ B` is
the *defining condition* of `Kakeya.ml1Boot.completedFibre` — this is (C2), and it is why the count is
reachable at this body and at no other — and `|P_b(k)| ≥ v` is `Kakeya.Tube.le_volume` at the
`τ`-tube `P_b(k)`.  The cardinality (C1) is then
`Kakeya.ml1Boot.branchingRatio_le_card_completedFibre`.

**The share is the hypothesis `hshare` and `κ` is free**; nothing produces such an `s'`, and at
`κ = 1` the statement is the count at the whole completion.  Neither `0 < κ ≤ 1` nor
`s' ⊆ 𝒰'_b` is asked: the count reads neither.  Of the blueprint's `0 < κ ≤ 1`, only the positivity
`0 < κ` is read downstream, at `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count`, where it is one
factor of that lemma's `0 < D`; **`κ ≤ 1` is read nowhere in this development**, neither here nor
there, and is recorded as omitted in that lemma's docstring.  No essential distinctness is asked and
none is used. -/
theorem densityIn_ge_of_completedFibre_share (hdim : Module.finrank ℝ E = 3) {ι : Type*}
    [DecidableEq ι] {δ : NNReal} {sl : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal}
    (hCu : 1 ≤ Cu) (𝒰' : UniformTubeSet sl T N Cu) {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents 𝒰' a b pθ) (hNb : 0 < 𝒰'.branchingN b) {Λ : NNReal} (hΛ : 1 ≤ Λ)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) {s' : Finset ι} {κ : NNReal}
    (hshare : κ * ((completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l).card : NNReal)
      ≤ ((s' ∩ completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l).card : NNReal)) :
    (anchorCountAtTestedBody.c 3 Cu κ : ENNReal)
          * ((𝒰'.branchingN a / 𝒰'.branchingN b : NNReal) : ENNReal)
          * (gridScale δ N b : ENNReal) ^ 2
          / volume ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).carrier
      ≤ densityIn s' (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
          ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody := by
  classical
  let cf : Finset ι := completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l
  let r : Finset ι := s' ∩ cf
  let B : ConvexSpaceBody E :=
    ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody
  let V : ι → ConvexSpaceBody E := fun k => (𝒰'.cover.tube b k).toConvexSpaceBody
  let vmin : ENNReal := ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal) *
    (gridScale δ N b : ENNReal) ^ 2
  have htss : r ⊆ s' := by
    intro k hk
    exact (Finset.mem_inter.mp hk).1
  have htK : ∀ k ∈ r, V k ≤ B := by
    intro k hk
    have hkcf : k ∈ (𝒰'.cover.indexSet b).filter
        fun j => (𝒰'.cover.tube b j).toConvexSpaceBody ≤ B := by
      simpa [cf, B, completedFibre] using (Finset.mem_inter.mp hk).2
    simpa [B, V] using (Finset.mem_filter.mp hkcf).2
  have htvol : ∀ k : ι, vmin ≤ volume (V k).carrier := by
    intro k
    dsimp [V, vmin]
    simpa [hdim] using _root_.Tube.le_volume (T := 𝒰'.cover.tube b k)
  have hvmin : ∀ k ∈ r, vmin ≤ volume (V k).carrier := fun k _ => htvol k
  have hbr : (Cu ^ 3)⁻¹ * (𝒰'.branchingN a / 𝒰'.branchingN b) ≤ (cf.card : NNReal) := by
    simpa [cf] using branchingRatio_le_card_completedFibre hCu 𝒰' hcnp hNb hΛ hl
  have hshr : κ * (cf.card : NNReal) ≤ (r.card : NNReal) := by
    simpa [r, cf] using hshare
  have hrat : κ * ((Cu ^ 3)⁻¹ * (𝒰'.branchingN a / 𝒰'.branchingN b)) ≤
      (r.card : NNReal) := by
    exact (mul_le_mul_of_nonneg_left hbr (by positivity)).trans hshr
  have hrcard : (κ * (Cu ^ 3)⁻¹) * (𝒰'.branchingN a / 𝒰'.branchingN b) ≤
      (r.card : NNReal) := by
    simpa [mul_assoc] using hrat
  have hnn : anchorCountAtTestedBody.c 3 Cu κ * (𝒰'.branchingN a / 𝒰'.branchingN b) *
        (gridScale δ N b) ^ 2 ≤
      (r.card : NNReal) * (_root_.Tube.le_volume.c 3) * (gridScale δ N b) ^ 2 := by
    dsimp [anchorCountAtTestedBody.c]
    calc
      (κ * (Cu ^ 3)⁻¹ * _root_.Tube.le_volume.c 3) *
          (𝒰'.branchingN a / 𝒰'.branchingN b) * (gridScale δ N b) ^ 2
          = (κ * (Cu ^ 3)⁻¹) * (𝒰'.branchingN a / 𝒰'.branchingN b) *
              (_root_.Tube.le_volume.c 3 * (gridScale δ N b) ^ 2) := by ring
      _ ≤ (r.card : NNReal) * (_root_.Tube.le_volume.c 3 * (gridScale δ N b) ^ 2) := by
            exact mul_le_mul hrcard (le_rfl) (by positivity) (by positivity)
      _ = (r.card : NNReal) * _root_.Tube.le_volume.c 3 * (gridScale δ N b) ^ 2 := by
            ring
  have hnumEN : (anchorCountAtTestedBody.c 3 Cu κ : ENNReal) *
        ((𝒰'.branchingN a / 𝒰'.branchingN b : NNReal) : ENNReal) *
        (gridScale δ N b : ENNReal) ^ 2
      ≤ (r.card : ENNReal) * vmin := by
    dsimp [vmin]
    rw [← mul_assoc]
    exact_mod_cast hnn
  have hcount := densityIn_ge_of_count_volume (t := r) (W := V) (K := B) (vmin := vmin)
    htss htK (fun k _ => htvol k)
  simpa [r, B, V] using (ENNReal.div_le_div_right hnumEN (volume B.carrier)).trans hcount

/-- **(GWZ Step 5a bullet (b), volume-share form) The count at the tested body from a volume
share** (blueprint `lem:ml1bootAnchorCountVolumeShare`).

`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share` with its *cardinality* share replaced by the
*volume* share

```
κ · ∑_{k ∈ \widetilde{𝒰'_b}(l)} |P_b(k)| ≤ ∑_{k ∈ s' ∩ \widetilde{𝒰'_b}(l)} |P_b(k)|,
```

at the price of the one extra hypothesis `hτ0 : 0 < τ` on the common radius `τ = ρ_b`.  The
conclusion is unchanged, and **the factor is not degraded**: the members of `𝕍` are `τ`-tubes of
one common radius, so `Tube.mul_sum_volume_le_iff_mul_card_le` converts the two shares into each
other at the *same* `κ` and the constant `Kakeya.ml1Boot.anchorCountAtTestedBody.c` is the same
constant.

**The point of this form is that its share hypothesis has the shape
`ConvexSpaceBody.nonempty_factorization.weight_subfamily` delivers** — the shape, and not more
than the shape.  What that lemma says about the subfamily that
`ConvexSpaceBody.nonempty_factorization.subfamily` returns is a *volume* share of exactly this
form: it reads `∑_{i ∈ s} |V i| ≤ C · ∑_{i ∈ subfamily} |V i|` with
`C = ConvexSpaceBody.nonempty_factorization.C`, which is this hypothesis at `κ = C⁻¹`.  What the
cardinality form asks is a cardinality share.  This statement removes that one shape mismatch and
nothing else.

**Two frictions remain even at the level of shape, and neither is closed here.**  First, `κ` is an
`NNReal` here whereas `C⁻¹` is an `ENNReal`, so a caller must present the factor as
`(C⁻¹).toNNReal` and discharge `((C⁻¹).toNNReal : ENNReal) = C⁻¹` from `C ≠ 0`; that is available,
since `C` is a product of `ENNReal.ofReal`s bounded below by `1`, but it is not done here.  Second
the share above is stated at the *intersection* `s' ∩ \widetilde{𝒰'_b}(l)`, whereas
`weight_subfamily` returns a subfamily of its input; matching them means reading it at the input
family `\widetilde{𝒰'_b}(l)` and taking `s'` to be the subfamily it returns.

**It is not a supplier of the share and may not be reported as one.**  The share is still a
hypothesis and `κ` is still free; nothing here produces an `s'`.  Reading
`ConvexSpaceBody.nonempty_factorization.weight_subfamily` at the input family
`\widetilde{𝒰'_b}(l)` — which is what would make its output share be the hypothesis below at
*this* completion — is performed nowhere, and its own hypotheses at that family (containment in a
unit ball and the `ethickness` condition, at a radius pinned to `τ` and not to `δ`) are verified
nowhere in this development.  The fibrewise share of blueprint
`note:ml1bootEssDistinctFibrewiseShare` likewise remains **open and blocking**, and this
hypothesis, being relative to the *completion* rather than the fibre, is at equal `κ` still the
formally stronger demand.

**The one extra hypothesis is not decorative, and no upper bound on `τ` accompanies it.**  At
`τ = 0` every `|P_b(k)|` vanishes in an ambient `ℝ ³`, so the volume share holds vacuously at
every `κ` and no cardinality share follows from it; this is the one respect in which this form is
weaker than `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`, which deliberately admits
`τ = 0`.  `τ ≤ 1` is **not** asked: `Tube.mul_sum_volume_le_iff_mul_card_le` reads only `0 < τ`,
positivity of the common tube volume being `Kakeya.Tube.le_volume` and its finiteness being
compactness of the carrier. -/
theorem densityIn_ge_of_completedFibre_volume_share (hdim : Module.finrank ℝ E = 3) {ι : Type*}
    [DecidableEq ι] {δ : NNReal} {sl : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal}
    (hCu : 1 ≤ Cu) (𝒰' : UniformTubeSet sl T N Cu) {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents 𝒰' a b pθ) (hNb : 0 < 𝒰'.branchingN b) {Λ : NNReal} (hΛ : 1 ≤ Λ)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) (hτ0 : 0 < gridScale δ N b)
    {s' : Finset ι} {κ : NNReal}
    (hshare : (κ : ENNReal)
          * ∑ k ∈ completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l,
              volume (𝒰'.cover.tube b k).carrier
        ≤ ∑ k ∈ s' ∩ completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l,
              volume (𝒰'.cover.tube b k).carrier) :
    (anchorCountAtTestedBody.c 3 Cu κ : ENNReal)
          * ((𝒰'.branchingN a / 𝒰'.branchingN b : NNReal) : ENNReal)
          * (gridScale δ N b : ENNReal) ^ 2
          / volume ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).carrier
      ≤ densityIn s' (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
          ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody := by
  classical
  let cf : Finset ι := completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l
  let r : Finset ι := s' ∩ cf
  have hh1 :
      (κ : ENNReal) * (∑ k ∈ cf, volume (𝒰'.cover.tube b k).carrier) ≤
        1 * (∑ k ∈ r, volume (𝒰'.cover.tube b k).carrier) := by
    simpa [cf, r, one_mul] using hshare
  have hcard : (κ : ENNReal) * (cf.card : ENNReal) ≤ (r.card : ENNReal) := by
    simpa [one_mul] using
      (_root_.Tube.mul_sum_volume_le_iff_mul_card_le (hδ0 := hτ0)
        (T := fun k => 𝒰'.cover.tube b k) (T₀ := 𝒰'.cover.tube b l)
        (s := cf) (r := r) (c := (κ : ENNReal)) (d := 1)).mp hh1
  have hhr : κ * (cf.card : NNReal) ≤ (r.card : NNReal) := by
    exact_mod_cast hcard
  simpa using densityIn_ge_of_completedFibre_share (hdim := hdim) (hCu := hCu)
    (𝒰' := 𝒰') (hcnp := hcnp) (hNb := hNb) (hΛ := hΛ) (hl := hl) (hshare := hhr)

/-- **(GWZ Step 5a bullet (b), normalized shape) The count against the width ratio** (blueprint
`lem:ml1bootAnchorCountNormalized`).

`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share` with `|B|` replaced, using the upper half of
`Kakeya.ml1Boot.volume_testedBody_bracket`, by `C(3) (Λθ) ²`:

```
Δ(𝕍|_{s'}, B) ≥ (c(3, Cu, κ) / C(3)) · (N_a / N_b) · (τ / (Λθ)) ².
```

Division is antitone in the denominator, so this is a weakening of the previous display and no new
argument occurs.  `hθ0` and `hθ1` are exactly what the upper half of the bracket asks of the radius
of `B`, and **both halves are needed**, the positivity as much as the bound.

**This is the source's shape, and the reading is not an identification.**  Where the source writes
`δ̃ ²` this writes `(τ / Λθ) ²`; the passage from the grid scales to the `δ̃` of the normalized
picture is the transport that is **not performed** in this development, here or anywhere, so this
display may not be quoted as the source's. -/
theorem densityIn_ge_of_completedFibre_share_normalized (hdim : Module.finrank ℝ E = 3) {ι : Type*}
    [DecidableEq ι] {δ : NNReal} {sl : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal}
    (hCu : 1 ≤ Cu) (𝒰' : UniformTubeSet sl T N Cu) {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents 𝒰' a b pθ) (hNb : 0 < 𝒰'.branchingN b) {Λ : NNReal} (hΛ : 1 ≤ Λ)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) (hθ0 : 0 < Λ * gridScale δ N a)
    (hθ1 : Λ * gridScale δ N a ≤ 1) {s' : Finset ι} {κ : NNReal}
    (hshare : κ * ((completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l).card : NNReal)
      ≤ ((s' ∩ completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l).card : NNReal)) :
    ((anchorCountAtTestedBody.c 3 Cu κ / _root_.Tube.volume_le.C 3 : NNReal) : ENNReal)
          * ((𝒰'.branchingN a / 𝒰'.branchingN b : NNReal) : ENNReal)
          * ((gridScale δ N b / (Λ * gridScale δ N a) : NNReal) : ENNReal) ^ 2
      ≤ densityIn s' (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
          ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody := by
  classical
  let c : NNReal := anchorCountAtTestedBody.c 3 Cu κ
  let p : NNReal := 𝒰'.branchingN a / 𝒰'.branchingN b
  let τ : NNReal := gridScale δ N b
  let C : NNReal := _root_.Tube.volume_le.C 3
  let θ : NNReal := Λ * gridScale δ N a
  let B : ConvexSpaceBody E := ((𝒰'.cover.tube a l).rescale θ).toConvexSpaceBody
  let V : ι → ConvexSpaceBody E := fun k => (𝒰'.cover.tube b k).toConvexSpaceBody
  have hθn : θ ≠ 0 := ne_of_gt (by simpa [θ] using hθ0)
  have hCn : C ≠ 0 := ne_of_gt (_root_.Tube.volume_le.C_pos 3)
  have hCθ : C * θ ^ 2 ≠ 0 := mul_ne_zero hCn (pow_ne_zero 2 hθn)
  have hident_nn : (c / C) * p * (τ / θ) ^ 2 = (c * p * τ ^ 2) / (C * θ ^ 2) := by
    field_simp [hθn, hCn]
  have hvolb := (volume_testedBody_bracket hdim 𝒰' l Λ).2 hθ0 hθ1
  have hvol : volume B.carrier ≤ (C : ENNReal) * (θ : ENNReal) ^ 2 := by
    simpa [B, C, θ] using hvolb.1
  have hdenom : (c : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2 /
      ((C : ENNReal) * (θ : ENNReal) ^ 2)
      ≤ (c : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2 / volume B.carrier := by
    exact ENNReal.div_le_div_left hvol ((c : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2)
  have hident : ((c / C : NNReal) : ENNReal) * ((p : NNReal) : ENNReal) *
      (((τ / θ : NNReal) : ENNReal) ^ 2)
      = (c : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2 /
        ((C : ENNReal) * (θ : ENNReal) ^ 2) := by
    calc
      ((c / C : NNReal) : ENNReal) * ((p : NNReal) : ENNReal) *
          (((τ / θ : NNReal) : ENNReal) ^ 2)
          = (((c / C) * p * (τ / θ) ^ 2 : NNReal) : ENNReal) := by
            norm_cast
      _ = (((c * p * τ ^ 2) / (C * θ ^ 2) : NNReal) : ENNReal) := by
            exact congrArg (fun x : NNReal => (x : ENNReal)) hident_nn
      _ = (c : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2 /
          ((C : ENNReal) * (θ : ENNReal) ^ 2) := by
            norm_cast
  calc
    ((c / C : NNReal) : ENNReal) * ((p : NNReal) : ENNReal) *
        (((τ / θ : NNReal) : ENNReal) ^ 2)
        = (c : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2 /
            ((C : ENNReal) * (θ : ENNReal) ^ 2) := hident
    _ ≤ (c : ENNReal) * (p : ENNReal) * (τ : ENNReal) ^ 2 / volume B.carrier := hdenom
    _ ≤ densityIn s' V B := by
          simpa [c, p, τ, B, V, θ] using densityIn_ge_of_completedFibre_share
            (hdim := hdim) (hCu := hCu) 𝒰' (hcnp := hcnp) (hNb := hNb) (hΛ := hΛ)
            (hl := hl) (hshare := hshare)

/-- **(GWZ Step 5c) The anchor bound with the denominator supplied by the count** (blueprint
`lem:ml1bootAnchorFrostmanFromCount`).

`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` at the family `𝕍 = (P_b(k))`, at
`u'' = 𝒰'_b`, at the tested body `B = P_a(l)^{(Λ θ)}` and at

```
D = c(3, Cu, κ) · (N_a / N_b) · τ ² / |B|,
```

the value `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share` produces.  So the conclusion is

```
C_F(𝕍[K], K) ≤ C_T · (bp/ap) · C_fact · U · |B| / (c(3, Cu, κ) · (N_a/N_b) · τ ²).
```

**Exactly one hypothesis of that lemma is discharged, its `hD` — link (C).**  Its numerator `hnum`,
its placement bundle `hplace : Kakeya.ml1Boot.IsAnchorPlacement` and its factoring datum `hfact`
are carried **verbatim** and are its own hypotheses still; the lemma is applied once and is neither
edited, weakened nor re-derived.

The three positivity hypotheses are what the two conditions `0 < D < ∞` cost: `hκ0` and `hCu` make
`c(3, Cu, κ)` positive, `hNa` makes the branching ratio positive, `hτ0` **is** the blueprint's
`τ > 0`, stated at `τ = ρ_b` itself rather than as `0 < δ` — the latter is the strictly stronger
demand, `Kakeya.gridScale_pos` being the one-way passage from it to this one — and `hθ0` with `hθ1`
give `0 < |B| < ∞` through `Kakeya.ml1Boot.volume_testedBody_bracket`, **both halves being spent**:
`|B| < ∞` is what makes `D = c · N_m · τ ² / |B|` positive, and `|B| > 0` is what lets the
right-hand side be rewritten from `C_fact U / D` into the displayed `C_fact U |B| / (c N_m τ ²)`.
Finiteness of `D` is no longer among the demands of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization`, so it is not derived here.  No upper
bound on `Δ_max(𝕍|_{s'})` is asked and none is used.

**Two upper bounds the blueprint displays are omitted, and each is read by nothing.**  It asks
`τ ≤ 1`, on the ground that the lemma being applied constrains the width of its family; but the Lean
form `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` carries no such condition.  It also
asks the share at `0 < κ ≤ 1`, of which only `hκ0 : 0 < κ` appears here: `κ ≤ 1` is read neither
here nor at `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`, hence nowhere in this
development.  Dropping an upper bound weakens the hypotheses, so neither omission is a
strengthening.

The signature is long because it is the *union* of two hypothesis groups, neither of which is this
statement's own: the whole situation of the count — hierarchy, parent map, branching positivity,
node, enlargement factor, tested-body radius, share — and the whole of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` minus its `hD`.  See the module docstring
for what remains open. -/
theorem frostmanConstIn_anchor_le_of_count (hdim : Module.finrank ℝ E = 3) {ap bp : NNReal}
    (hap0 : 0 < ap) (hab : ap ≤ bp) {ι : Type*} [DecidableEq ι] {δ : NNReal} {sl : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet sl T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hNa : 0 < 𝒰'.branchingN a) (hNb : 0 < 𝒰'.branchingN b) (hτ0 : 0 < gridScale δ N b)
    {Λ : NNReal} (hΛ : 1 ≤ Λ) {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a)
    (hθ0 : 0 < Λ * gridScale δ N a) (hθ1 : Λ * gridScale δ N a ≤ 1) {s' t : Finset ι}
    (hs' : s' ⊆ 𝒰'.cover.indexSet b) {κ : NNReal} (hκ0 : 0 < κ)
    (hshare : κ * ((completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l).card : NNReal)
      ≤ ((s' ∩ completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l).card : NNReal))
    (K : ConvexSpaceBody E) {U : ENNReal}
    (hnum : ∀ K' : ConvexSpaceBody E, K' ≤ K →
      densityIn (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K' ≤ U)
    (hplace : IsAnchorPlacement (fun k => 𝒰'.cover.tube b k) K ap bp s' t)
    {Cfact : ENNReal} (hCfact0 : 0 < Cfact) (hCfactTop : Cfact ≠ ⊤)
    (hfact : maxDensity s' (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
      ≤ Cfact * densityIn t (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
        (t.convexHull_biUnion fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)) :
    frostmanConstIn
          (familyIn (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K)
          (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K
      ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) *
          (Cfact * U * volume ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).carrier /
            ((anchorCountAtTestedBody.c 3 Cu κ : ENNReal)
              * ((𝒰'.branchingN a / 𝒰'.branchingN b : NNReal) : ENNReal)
              * (gridScale δ N b : ENNReal) ^ 2)) := by
  classical
  let B0 : ConvexSpaceBody E :=
    ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody
  let X0 : ENNReal := (anchorCountAtTestedBody.c 3 Cu κ : ENNReal)
    * ((𝒰'.branchingN a / 𝒰'.branchingN b : NNReal) : ENNReal)
    * (gridScale δ N b : ENNReal) ^ 2
  let Y0 : ENNReal := volume ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).carrier
  let D0 : ENNReal := X0 / Y0
  have hvolB := (volume_testedBody_bracket hdim (𝒰' := 𝒰') (l := l) (Λ := Λ)).2 hθ0 hθ1
  have hY0pos : 0 < Y0 := by
    simpa [Y0] using hvolB.2.1
  have hY0lt : Y0 < ⊤ := by
    simpa [Y0] using hvolB.2.2
  have hY0ne : Y0 ≠ 0 := ne_of_gt hY0pos
  have hY0neTop : Y0 ≠ ⊤ := ne_of_lt hY0lt
  have hcpe : 0 < anchorCountAtTestedBody.c 3 Cu κ := by
    dsimp [anchorCountAtTestedBody.c]
    have hCuPos : 0 < Cu := zero_lt_one.trans_le hCu
    have hCu3Pos : 0 < Cu ^ 3 := pow_pos hCuPos 3
    have hInvPos : 0 < (Cu ^ 3)⁻¹ := by
      positivity
    have hTubePos : 0 < _root_.Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
    exact mul_pos (mul_pos hκ0 hInvPos) hTubePos
  have hF1ne : (anchorCountAtTestedBody.c 3 Cu κ : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hcpe)
  have hF2ne : ((𝒰'.branchingN a / 𝒰'.branchingN b : NNReal) : ENNReal) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    have hratio : 0 < (𝒰'.branchingN a / 𝒰'.branchingN b : NNReal) := by
      positivity
    exact ne_of_gt hratio
  have hF3ne : (gridScale δ N b : ENNReal) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (ne_of_gt hτ0))
  have hX0ne : X0 ≠ 0 := by
    dsimp [X0]
    exact mul_ne_zero (mul_ne_zero hF1ne hF2ne) hF3ne
  have hX0pos : 0 < X0 := pos_iff_ne_zero.mpr hX0ne
  have hF1top : (anchorCountAtTestedBody.c 3 Cu κ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hF2top : ((𝒰'.branchingN a / 𝒰'.branchingN b : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hF3top : (gridScale δ N b : ENNReal) ^ 2 ≠ ⊤ := by
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hX0neTop : X0 ≠ ⊤ := by
    dsimp [X0]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hF1top hF2top) hF3top
  have hDpos : 0 < D0 := by
    dsimp [D0]
    exact ENNReal.div_pos hX0ne hY0neTop
  have hDden : D0 ≤ densityIn s' (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) B0 := by
    simpa [D0, X0, Y0, B0] using
      densityIn_ge_of_completedFibre_share (hdim := hdim) (hCu := hCu) (𝒰' := 𝒰')
        (hcnp := hcnp) (hNb := hNb) (hΛ := hΛ) (hl := hl) (hshare := hshare)
  have hIneq :
      frostmanConstIn
            (familyIn (𝒰'.cover.indexSet b)
              (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K)
            (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K
        ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * (Cfact * U / D0) := by
    exact frostmanConstIn_anchor_le_of_factorization
      (hdim := hdim) (δt := gridScale δ N b) (ap := ap) (bp := bp)
      (hap0 := hap0) (hab := hab) (ι := ι) (u'' := 𝒰'.cover.indexSet b) (s' := s') (t := t)
      (T := fun k => 𝒰'.cover.tube b k) (K := K) (U := U) (hnum := hnum)
      (hs'u := hs') (hplace := hplace)
      (Cfact := Cfact) (hCfact0 := hCfact0) (hCfactTop := hCfactTop) (hfact := hfact)
      (B := B0) (D := D0) (hD0 := hDpos) (hD := hDden)
  have hUdiv : Cfact * U / D0 = Cfact * U * Y0 / X0 := by
    dsimp [D0]
    rw [← ENNReal.div_mul (a := Cfact * U) (b := X0) (c := Y0)
      (h0 := Or.inr hY0ne) (htop := Or.inl hX0neTop)]
    simp [ENNReal.div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm]
  rw [hUdiv] at hIneq
  simpa [X0, Y0, B0] using hIneq

end ml1Boot

end Kakeya
