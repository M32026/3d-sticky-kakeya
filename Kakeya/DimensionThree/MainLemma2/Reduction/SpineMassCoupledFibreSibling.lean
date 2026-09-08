/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseFibreBracket
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMassCoupledSelection

/-!
# R0b's thread cell, measured: `𝕊''_b⟨S_p^*⟩` is the **assignment fibre**, and the faithful sibling

 F2 asked which reading the source's `𝕊''_b⟨S_p^*⟩` (l.4486-4492) is, since
`Kakeya.ML2Core.MassCoupledFullnessSelectionAt` renders it as `Tube.UniformTubeSet.nodesUnder` —
the **containment** set — in *two* places that move in **opposite** directions.

## The measurement — Definition 2.1(ii), l.222-224, settles it

> *"`π_{k-1} = q_k ∘ π_k`, so the **thread cells** `𝕋⟨S⟩ = {T : π_k(T) = S}` form compatible
> partitions"*

`𝕋⟨S⟩` is defined as a **fibre of the parent map**, and the source underlines the point at l.251:
*"every later expression such as `𝕋_ρ[T_θ]` refers to a specified thread cell"*.  l.4498 says it
again for this very selection: *"Both statements refer to the same **complete tagged fibres**;
this is precisely why the earlier pigeonholing was weighted by shaded mass."*

**So the source's object is the assignment fibre, not the containment set.**  `nodesUnder` is a
different, strictly larger set (`Kakeya.ML2Core.card_nodesUnder_le_card_coarseFibre` prices the
difference at `Cu ^ 5`), and  Trap B already recorded that the
two are different objects.

## Why the containment rendering is **incomparable**, not merely weaker

The two occurrences move opposite ways, which is what F2 flagged:

| clause | containment rendering | direction vs. the fibre form |
|---|---|---|
| localisation | `Ub ⊆ 𝒰.nodesUnder b p Sp` | **weaker** — larger set, less asserted |
| retention | `θ₀ * (𝒰.nodesUnder b p Sp).card ≤ Ub.card` | **stronger** — larger denominator |

Neither predicate implies the other, so the containment form is **not** a safe conservative
substitute for the source's.  That is the whole of F2's concern, and it is why the faithful form is
cut here as an **additive sibling** () with a bridge.

## The bridge, and its constant

`massCoupledFullnessSelectionAt_of_threadCell` derives the existing containment form from the faithful
fibre form at `θ₀ ↦ θ₀ / Cu ^ 5` — the **existing** bracket
`Kakeya.ML2Core.card_nodesUnder_le_card_coarseFibre`, the same vehicle
`Kakeya.ML2Core.retentionProportionAt_of_fibreRetention` uses.  **The dispatch called this a
`Cu²`-bracket; the existing bracket is `Cu ^ 5`**, and it is stated here rather than fitted.  `Cu` is
`δ`-free at every site this landing reaches, so the fifth power is
`δ`-free too and enters no exponent account; but `δ^{6η_c} ≤ θ₀ / Cu ^ 5` does **not** follow from
`δ^{6η_c} ≤ θ₀`, so that row is carried as an explicit hypothesis of the bridge rather than
smuggled — it is a `δ`-threshold, absorbed exactly as A3 absorbs the others.

## A naming trap, recorded

The existing `Kakeya.ML2Core.massCoupledFullnessSelectionAt_of_fibre`
(`SpineMassCoupledSelection.lean:308`) says *fibre* in its name but is stated **entirely on
`𝒰.nodesUnder b p Sp`** — every one of its `hne`, `hvol`, `hfin`, `hbud`, `hlam`, `hdens` rows is
read there.  It is the **containment** producer.  Nothing is wrong with it; the name is simply not
evidence about the reading, and this file's `massCoupledFullnessSelectionAt_of_threadCell` is the
genuinely fibre-side statement.

## Does the covering bridge's `hret` shape move?  **NO — measured, not assumed.**

`Kakeya.ML2Core.bridge_cellCount_chain` (`SpineDefectCoveringBridge.lean:216-226`, the estimate) takes

```
(Tb U : Finset ιU) … (hUsub : U ⊆ Tb) (hret : θ₀ * (Tb.card : ℝ) ≤ (U.card : ℝ))
```

with `Tb` a **bare `Finset` of a bare type** — it never mentions `nodesUnder`, `coverClass`, or a
hierarchy at all.  So instantiating `Tb` at the assignment fibre instead of at
`𝒰.nodesUnder b p Sp` typechecks with **no change to the bridge and no change to
`massCoupledFullnessSelection_retainedProportion`'s shape**; only the supplier chooses a different
`Tb`.

**And the fibre reading makes two of the bridge's other rows *more* faithful, not less.**  The same
theorem asks for descendant regularity on `Tb`,
`hDlo : ∀ x ∈ Tm, D ≤ (Tb.filter (anc · = x)).card` and `hDhi : … ≤ 2 * D`.  That two-sided
bracket is Definition 2.1(iii) — `D_k ≤ #𝕋⟨S⟩ < 2D_k`, l.226-228 — which the source states
**about thread cells**.  Read on `nodesUnder` it is a different assertion; read on the fibre it is
the source's own.  So moving `Tb` to the fibre costs the bridge nothing and buys fidelity in
`hDlo`/`hDhi`.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `threadCellFibre_subset_nodesUnder` | `𝒰` on `(s, V)`; no shading | `(p, b)` |
| `MassCoupledFullnessSelectionAtFibre` | `(𝕌_b, Z_b)` on the **fibre** | `(p, b)` |
| `massCoupledFullnessSelectionAt_of_threadCell` | as above | `(p, b)` |

## A1-a

Nothing here is a `GridUniformCore`, and nothing here enters `FloorHypothesisAt`,
`FloorDataAtTrichotomy`, `RefinedFloorHypothesis`, `hfac` or a field of
`IsKatzTaoDividingWindow(Levels)`.  This file adds one `Prop`, one inclusion and one bridge.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section MassCoupledFibre

variable {ι : Type*} {δ Cu : NNReal}

open Classical in
/-- **The coarse fibre sits inside the containment set.**  A level-`b` node whose `coarseNode`
ancestor at level `p` is `Sp` has its tube inside `Sp`'s tube
(`Kakeya.ML2Reduction.tube_le_coarseNode`), so the fibre is one of the sets `nodesUnder` collects.
Together with `card_nodesUnder_le_card_coarseFibre` this is the two-sided statement of the
containment-versus-assignment gap at the pair `(p,b)`: `fibre ⊆ nodesUnder` and
`#nodesUnder ≤ Cu ^ 5 · #fibre`. -/
theorem threadCellFibre_subset_nodesUnder {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty) {p b : ℕ} (hpb : p ≤ b) (hbN : b ≤ N)
    {Sp : ι} :
    ml1Boot.fibre (𝒰.cover.indexSet b) (ML2Reduction.coarseNode 𝒰.cover.toChain p b) Sp
      ⊆ 𝒰.nodesUnder b p Sp := by
  classical
  intro j hj
  rw [ml1Boot.fibre, Finset.mem_filter] at hj
  obtain ⟨hjidx, hjanc⟩ := hj
  have hact : j ∈ ML2Reduction.activeNodes 𝒰.cover.toChain b :=
    Finset.mem_filter.mpr ⟨hjidx,
      Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hbN hs hjidx⟩
  rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff]
  refine ⟨hjidx, ?_⟩
  rw [← hjanc]
  exact ML2Reduction.tube_le_coarseNode 𝒰.cover.toChain hpb hbN hact

open Classical in
/-- **The mass-coupled fullness selection, on the source's own object** (l.4486-4500).

Identical to `Kakeya.ML2Core.MassCoupledFullnessSelectionAt` except that both occurrences of
`𝕊''_b⟨S_p^*⟩` are the **assignment fibre** `ml1Boot.fibre` rather than
`Tube.UniformTubeSet.nodesUnder` — the reading Definition 2.1(ii) (l.222-224) fixes and l.4498
repeats (*"the same complete tagged fibres"*).

**Family/shading:** `(𝕌_b, Z_b)`, the selected level-`b` cells of the fibre over one retained
`p`-cell, with the shading induced on them.  **Level pair:** `(p, b)`. -/
def MassCoupledFullnessSelectionAtFibre (ηc ηJ : ℝ) (tAux θ₀ : NNReal) {s : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (p b : ℕ) : Prop :=
  ∀ Sp ∈ 𝒰.cover.indexSet p,
    ∃ (Ub : Finset ι)
      (Zb : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
        (EuclideanSpace ℝ (Fin 3))),
      Ub.Nonempty ∧
      Ub ⊆ ml1Boot.fibre (𝒰.cover.indexSet b)
        (ML2Reduction.coarseNode 𝒰.cover.toChain p b) Sp ∧
      (∀ j, (Zb j).toTube = 𝒰.cover.tube b j) ∧
      (δ : NNReal) ^ (5 * ηc) ≤ ShadedBody.fullness Ub (fun j ↦ (Zb j).toShadedBody) ∧
      Kakeya.maxDensity Ub (fun j ↦ (Zb j).toConvexSpaceBody) ≤ (tAux : ENNReal) ^ (-ηJ) ∧
      (δ : NNReal) ^ (6 * ηc) ≤ θ₀ ∧
      (θ₀ : ℝ) * ((ml1Boot.fibre (𝒰.cover.indexSet b)
          (ML2Reduction.coarseNode 𝒰.cover.toChain p b) Sp).card : ℝ) ≤ (Ub.card : ℝ)

open Classical in
/-- **The faithful form implies the existing one, at `θ₀ ↦ θ₀ / Cu ^ 5`.**

Both clauses are transported by the existing bracket
`Kakeya.ML2Core.card_nodesUnder_le_card_coarseFibre`: the localisation by
`threadCellFibre_subset_nodesUnder` (free), the retention by the `Cu ^ 5` count bracket.  The
`δ^{6η_c} ≤ θ₀ / Cu ^ 5` row is an **explicit hypothesis**, because it does not follow from
`δ^{6η_c} ≤ θ₀`; it is a `δ`-threshold against a `δ`-free constant, absorbed exactly as
 A3 absorbs the others.

**Family/shading** and **level pair**: as `MassCoupledFullnessSelectionAtFibre`. -/
theorem massCoupledFullnessSelectionAt_of_threadCell {ηc ηJ : ℝ} {tAux θ₀ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu}
    {p b : ℕ} (hCu : 1 ≤ Cu) (hpb : p ≤ b) (hbN : b ≤ Tube.ssfGridLen δ) (hs : s.Nonempty)
    (hθ6 : (δ : NNReal) ^ (6 * ηc) ≤ θ₀ / Cu ^ 5)
    (h : MassCoupledFullnessSelectionAtFibre ηc ηJ tAux θ₀ 𝒰 p b) :
    MassCoupledFullnessSelectionAt ηc ηJ tAux (θ₀ / Cu ^ 5) 𝒰 p b := by
  classical
  intro Sp hSp
  obtain ⟨Ub, Zb, hne, hsub, htube, hfull, hdens, -, hcard⟩ := h Sp hSp
  refine ⟨Ub, Zb, hne, hsub.trans (threadCellFibre_subset_nodesUnder 𝒰 hs hpb hbN),
    htube, hfull, hdens, hθ6, ?_⟩
  have hbr := card_nodesUnder_le_card_coarseFibre (E := EuclideanSpace ℝ (Fin 3))
    hCu 𝒰 hpb hbN hs hSp
  have hCu1 : (1 : ℝ) ≤ (Cu : ℝ) := by exact_mod_cast hCu
  have hpow : (0 : ℝ) < (Cu : ℝ) ^ 5 := by positivity
  have hdiv : ((θ₀ / Cu ^ 5 : NNReal) : ℝ) = (θ₀ : ℝ) / (Cu : ℝ) ^ 5 := by
    rw [NNReal.coe_div, NNReal.coe_pow]
  rw [hdiv, div_mul_eq_mul_div, div_le_iff₀ hpow]
  have hmono : (θ₀ : ℝ) * ((𝒰.nodesUnder b p Sp).card : ℝ)
      ≤ (θ₀ : ℝ) * ((Cu : ℝ) ^ 5
          * ((ml1Boot.fibre (𝒰.cover.indexSet b)
              (ML2Reduction.coarseNode 𝒰.cover.toChain p b) Sp).card : ℝ)) :=
    mul_le_mul_of_nonneg_left hbr (NNReal.coe_nonneg θ₀)
  have h3 := mul_le_mul_of_nonneg_left hcard hpow.le
  have hrw : (θ₀ : ℝ) * ((Cu : ℝ) ^ 5
      * ((ml1Boot.fibre (𝒰.cover.indexSet b)
          (ML2Reduction.coarseNode 𝒰.cover.toChain p b) Sp).card : ℝ))
      = (Cu : ℝ) ^ 5 * ((θ₀ : ℝ)
        * ((ml1Boot.fibre (𝒰.cover.indexSet b)
            (ML2Reduction.coarseNode 𝒰.cover.toChain p b) Sp).card : ℝ)) := by ring
  rw [hrw] at hmono
  exact (hmono.trans h3).trans (le_of_eq (mul_comm _ _))

end MassCoupledFibre

end Kakeya.ML2Core

end
