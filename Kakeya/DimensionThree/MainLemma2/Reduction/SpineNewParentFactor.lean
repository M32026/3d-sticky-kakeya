/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacFourProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze

/-!
# The new-parent factor at `(a, p)`, the seam-restricted split, and which set retention is about

Four rows of the four-way producer, closed.  Every declaration states its family, its shading and
its level pair, because the two defects this file exists to prevent are invisible to `check`,
`scan`, `axioms` and `guard`: a factor read at the wrong level pair, and a retention statement read
about the wrong set.

## 1. `hpar`: the new-parent factor is the existing defect estimate at `(a, p)`

`Kakeya.ML2Core.exists_coarse_factor` is level-agnostic — a family of `θ`-tubes with fullness
`≥ dt ^ η` and `maxDensity ≤ dt ^ (-ηc)` has multiplicity `≤ dt ^ (-(ε + ηc)) · card ^ β`.  The
outer factor instantiates it at level `a` with `ηc` from the window's `coarse_maxDensity_le`.  The
**new-parent** factor is the same estimate at the pair `(a, p)`, and its density input is not a
window field at all: it is the **(F) payload's own parent-density row**,
`∀ jθ ∈ indexSet a, maxDensity (nodesUnder p a jθ) ≤ δ ^ (-2η')`, the row
 lists as *"produced, consumed by nothing"*.

So the four-way split does not merely need that row — it is **the first consumer of it**, and the
loss it charges is `εp = ε + 2η'`.  That closes the loop the map opened.

## 2. `tτ' ⊆ t₁`: run the split on the seam-restricted family

`Kakeya.ML2Reduction.exists_spineThreeScale_ofChain` returns `tτ' ⊆ activeNodes 𝒞 b` while the
re-cut `hfac` asks `tτ' ⊆ t₁`.  The existing three-way route gets this by running the split on the
node-restricted family `{i ∈ s | assign b i ∈ t₁}`, where `assign b` maps into `t₁` by
construction; `Kakeya.ML2Core.exists_spineThreeScale_restricted` is that move at three levels, and
its multiplicity is read on exactly the family `hfac`'s `hprod` reads.

## 3. `hballπ`: the level-`p` ball row

Derived, not assumed, from the seam's level-`a` ball row and `tube_le_coarseNode`: a level-`p` node
whose `(a,p)`-parent is retained sits inside a retained level-`a` node, hence in the unit ball.
`TCTL4` is the control that the row is load-bearing.

## 4. Which set is retention about?

**`t₁`, the seam's retained set, is fibre-complete** —
`Kakeya.ML2Core.threeLevelSeam_fibre_complete`,
because the seam never selected at level `b`.  **`tτ'`, the split's retained set, is not**: it is
the mass-pigeonholed outer set of a one-scale application, and retention does **not** pass to
subsets — `Kakeya.ML2Core.not_retentionAt_empty` is the record of that, at the extreme
subset `∅ ⊆ t₁`.  For `tτ'` the vehicle is bracket ∘ retention:
`Kakeya.ML2Core.retentionProportionAt_of_fibreRetention`, at the cost `θ₀ ↦ θ₀ / Cu ^ 5`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

section NewParent

variable {δ Cu : NNReal} {ι : Type u}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **The `(a, p)` fibre sits under its level-`a` node.**

`{k ∈ tp' | coarseNode 𝒞 a p k = jθ} ⊆ 𝒰.nodesUnder p a jθ` for a retained set `tp'` of *active*
level-`p` nodes: membership of `indexSet p` is `activeNodes_subset`, and the containment is
`tube_le_coarseNode` read at the fibre's own value.

**Family:** `(s, T)` under `𝒰`, no shading.  **Level pair:** `(a, p)`. -/
theorem coarseFibre_subset_nodesUnder_at {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (𝒰 : Tube.UniformTubeSet s T N Cu) {a p : ℕ} (hap : a ≤ p) (hpN : p ≤ N)
    {tp' : Finset ι} (htp : tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p) (jθ : ι) :
    ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
      ⊆ 𝒰.nodesUnder p a jθ := by
  intro k hk
  obtain ⟨hkt, hkc⟩ := Finset.mem_filter.mp hk
  have hact := htp hkt
  have hle := ML2Reduction.tube_le_coarseNode 𝒰.cover.toChain hap hpN hact
  rw [hkc] at hle
  rw [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn, Finset.mem_filter]
  exact ⟨ML2Reduction.activeNodes_subset 𝒰.cover.toChain p hact, hle⟩

omit [Nontrivial E] in
open Classical in
/-- **The (F) parent-density row transfers to the `(a, p)` fibre, translated.**

`Kakeya.ML2Core.coarseFibre_subset_nodesUnder_at` plus
`Kakeya.ML2Core.maxDensity_le_of_translate_subset`: the density the (F) payload prints on
`nodesUnder p a jθ` is an upper bound for the density of the shaded, translated fibre the split
hands back.

**Family:** `(s, T)` under `𝒰`; **shading:** `Yp`, the split's level-`p` shading, translated by
`v`.  **Level pair:** `(a, p)`. -/
theorem maxDensity_newParentFibre_le {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (𝒰 : Tube.UniformTubeSet s T N Cu) {a p : ℕ} (hap : a ≤ p) (hpN : p ≤ N)
    {tp' : Finset ι} (htp : tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p)
    {Yp : ι → ShadedTube (Tube.gridScale δ N p) E} {v : E}
    (hYp : ∀ k, (Yp k).toTube = (𝒰.cover.tube p k).translate v)
    {ηc : ℝ} {jθ : ι}
    (hrow : Kakeya.maxDensity (𝒰.nodesUnder p a jθ)
        (fun k => (𝒰.cover.tube p k).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηc)) :
    Kakeya.maxDensity ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
        (fun k => (Yp k).toConvexSpaceBody)
      ≤ (δ : ENNReal) ^ (-ηc) :=
  le_trans (maxDensity_le_of_translate_subset
    (coarseFibre_subset_nodesUnder_at 𝒰 hap hpN htp jθ) hYp) hrow

open Classical in
/-- **`hpar`, discharged: the new-parent factor at `(a, p)`.**

`Kakeya.ML2Core.exists_coarse_factor` — the existing, level-agnostic defect estimate the outer factor
already runs on — read at the pair `(a, p)`, with its density input supplied by the **(F) payload's
parent-density row** through `Kakeya.ML2Core.maxDensity_newParentFibre_le`.  The loss it charges is

`εp = ε + 2 η'`,

`ε` the estimate's own accuracy and `2 η'` the (F) row's exponent.  Nothing new is assumed: the row
was already an antecedent of `hfac`, and this is its first consumer.

**Family:** `(s, T)` under `𝒰`; **shading:** the split's `Yp`, translated by `v`.
**Level pair:** `(a, p)` — the source's `ρ_p/(2ρ_a)`-family in the normalised `a`-cell (l.4448). -/
theorem exists_newParent_factor_at {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∃ θ₀ : NNReal, 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ {δ Cu : NNReal} {ι : Type u} {s : Finset ι} {T : ι → Tube δ E} {N a p : ℕ}
        {𝒰 : Tube.UniformTubeSet s T N Cu} {tp' : Finset ι}
        {Yp : ι → ShadedTube (Tube.gridScale δ N p) E} {v : E} {η' : ℝ} {jθ : ι},
        0 < δ → δ ≤ 1 → a ≤ p → p ≤ N →
        Tube.gridScale δ N p ≤ θ₀ → 0 ≤ η' →
        tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p →
        (∀ k, (Yp k).toTube = (𝒰.cover.tube p k).translate v) →
        (∀ k ∈ ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι),
          (Yp k).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (δ : NNReal) ^ η ≤ ShadedBody.fullness
            ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
            (fun k => (Yp k).toShadedBody) →
        Kakeya.maxDensity (𝒰.nodesUnder p a jθ)
            (fun k => (𝒰.cover.tube p k).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-(2 * η')) →
        ShadedBody.multiplicity
            ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
            (fun k => (Yp k).toShadedBody)
          ≤ (δ : ENNReal) ^ (-(ε + 2 * η'))
            * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} :
                Finset ι).card : ENNReal)) ^ β := by
  classical
  obtain ⟨η, hη, θ₀, hθ₀0, hθ₀1, hcore⟩ := exists_coarse_factor.{u} (E := E) hβ0 hβ1 hKT hε
  refine ⟨η, hη, θ₀, hθ₀0, hθ₀1, ?_⟩
  intro δ Cu ι s T N a p 𝒰 tp' Yp v η' jθ hδ0 hδ1 hap hpN hθle hη' htp hYp hball hfull hrow
  have hρp0 : 0 < Tube.gridScale δ N p := Tube.gridScale_pos hδ0 _ _
  have hδρp : δ ≤ Tube.gridScale δ N p := ML2Core.delta_le_gridScale hδ0 hδ1 hpN
  exact hcore hρp0 hθle δ hδ0 hδρp (by linarith : (0:ℝ) ≤ 2 * η') _ Yp hball hfull
    (maxDensity_newParentFibre_le 𝒰 hap hpN htp hYp hrow)

end NewParent

section Restricted

variable {δ : NNReal} {ι : Type u}

open Classical in
/-- **`tτ' ⊆ t₁`, discharged: the split run on the seam-restricted family.**

`Kakeya.ML2Reduction.exists_spineThreeScale` with the level-`b` node set taken to be the seam's
retained set `t₁` rather than all of `activeNodes 𝒞 b`, and the leaf family taken to be the
node-restricted `{i ∈ s | assign b i ∈ t₁}` — on which `assign b` maps into `t₁` by construction,
which is the only thing the restriction needs.  The multiplicity is then read on exactly the family
the re-cut `hfac`'s `hprod` reads.

This is the existing three-way route's own move (`exists_spineTwoScale_ofChain` is applied the same
way downstream), at three levels.

**Family/shading:** `({i ∈ s | assign b i ∈ t₁}, V)` under `𝒞`, with the split's four shadings.
**Level pairs:** leaf → `b`; seam `(p, b)`; new parent `(a, p)`; outer level `a`. -/
theorem exists_spineThreeScale_restricted {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {σ : ℕ → ℝ≥0} (hδ : 0 < δ) (𝒞 : Tube.ChainCoverSystem s (fun i => (V i).toTube) N σ)
    {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) (haN : a ≤ N) (hpN : p ≤ N) (hbN : b ≤ N)
    (hδτ : δ ≤ σ b) (hτπ : σ b ≤ σ p) (hπθ : σ p ≤ σ a) (hθ1 : σ a ≤ 1)
    {t₁ : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒞 b)
    (hball : ∀ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι),
      (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballτ : ∀ j ∈ t₁, (𝒞.tube b j).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballπ : ∀ k ∈ ML2Reduction.activeNodes 𝒞 p,
      (𝒞.tube p k).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ tτ' ⊆ t₁, ∃ tp' ⊆ ML2Reduction.activeNodes 𝒞 p, ∃ tθ' ⊆ 𝒞.indexSet a,
      ∃ (Yτ' : ι → ShadedTube (σ b) E) (Ypo Yp : ι → ShadedTube (σ p) E)
        (Yθ : ι → ShadedTube (σ a) E) (Y' : ι → ShadedTube δ E),
        (∀ j, (Yτ' j).toTube = 𝒞.tube b j) ∧
        (∀ k, (Ypo k).toTube = 𝒞.tube p k) ∧
        (∀ k, (Yp k).toTube = 𝒞.tube p k) ∧
        (∀ l, (Yθ l).toTube = 𝒞.tube a l) ∧
        (∀ i, (Y' i).toTube = (V i).toTube) ∧
        (∀ i, (Y' i).shade ⊆ (V i).shade) ∧
        (∀ k, (Yp k).shade ⊆ (Ypo k).shade) ∧
        (0 < ∑ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι), volume (V i).shade →
          tτ'.Nonempty ∧ tp'.Nonempty ∧ tθ'.Nonempty) ∧
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
                ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b))⁻¹ *
            ShadedBody.fullness ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
              (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tp' (fun k => (Ypo k).toShadedBody) ∧
        (∀ jτ ∈ tτ', ∀ jp ∈ tp', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
              (fun i => (V i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
                    ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b) *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tp'.card (σ p) : ℝ≥0) : ENNReal)
              * ShadedBody.multiplicity
                  ({i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι) | 𝒞.assign b i = jτ} : Finset ι)
                  (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 p b j = jp}
                  (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity {k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ}
                  (fun k => (Yp k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)) := by
  classical
  exact ML2Reduction.exists_spineThreeScale (E := E) hδ hδτ hτπ hπθ hθ1 V (𝒞.tube b)
    (𝒞.tube p) (𝒞.tube a) (𝒞.assign b) (ML2Reduction.coarseNode 𝒞 p b)
    (ML2Reduction.coarseNode 𝒞 a p) hball hballτ hballπ
    (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i hi => 𝒞.le_tube_assign b hbN i (Finset.mem_filter.mp hi).1)
    (fun j hj => coarseNode_mem_activeNodes 𝒞 hpb hbN (ht₁ hj))
    (fun j hj => ML2Reduction.tube_le_coarseNode 𝒞 hpb hbN (ht₁ hj))
    (fun k hk => ML2Reduction.coarseNode_mem 𝒞 haN hk)
    (fun k hk => ML2Reduction.tube_le_coarseNode 𝒞 hap hpN hk)

end Restricted

section BallRow

variable {δ : NNReal} {ι : Type u}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **Translation preserves node containment.**  `≤` on `ConvexSpaceBody` *is* carrier inclusion,
and `Tube.translate` is a preimage, so containment survives the seam's translate. -/
theorem translate_carrier_subset_of_le {ρ ρ' : NNReal} (A : Tube ρ E) (B : Tube ρ' E) (v : E)
    (h : A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :
    (A.translate v).carrier ⊆ (B.translate v).carrier := by
  simp only [Tube.translate_carrier]
  exact Set.preimage_mono h

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **`hballπ`, discharged: the level-`p` ball row from the seam's level-`a` one.**

A level-`p` node whose `(a, p)`-parent is retained sits inside a retained level-`a` node
(`tube_le_coarseNode`), and the seam's level-`a` ball row puts that node in the unit ball.  So the
third level costs no new geometric input — only the level-`a` row the seam already supplies, at the
`(a, p)` pair.

`TCTL4` is the control that the row is load-bearing: weakening it to `True` breaks the split.

**Family:** `(s, T)` under `𝒞`, no shading; the translate `v` is the seam's.
**Level pair:** `(a, p)`. -/
theorem ballRow_at_parent_of_coarse {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}
    (𝒞 : Tube.ChainCoverSystem s T N σ) {a p : ℕ} (hap : a ≤ p) (hpN : p ≤ N) {v : E}
    {t₀ tp : Finset ι} (htp : tp ⊆ ML2Reduction.activeNodes 𝒞 p)
    (hcn : ∀ k ∈ tp, ML2Reduction.coarseNode 𝒞 a p k ∈ t₀)
    (hball₀ : ∀ l ∈ t₀, ((𝒞.tube a l).translate v).carrier
      ⊆ Metric.closedBall (0 : E) 1) :
    ∀ k ∈ tp, ((𝒞.tube p k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1 := by
  intro k hk
  refine subset_trans ?_ (hball₀ _ (hcn k hk))
  exact translate_carrier_subset_of_le _ _ v
    (ML2Reduction.tube_le_coarseNode 𝒞 hap hpN (htp hk))

end BallRow

section Thresholds

variable {δ : NNReal}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **`≤` on tubes survives the seam's translate**, in the `ConvexSpaceBody` form the split
consumes.  The carrier form is `Kakeya.ML2Core.translate_carrier_subset_of_le`; `≤` on
`ConvexSpaceBody` *is* that inclusion, so the two are the same statement and this records it. -/
theorem tube_translate_le_translate {ρ ρ' : NNReal} (A : Tube ρ E) (B : Tube ρ' E) (v : E)
    (h : A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :
    (A.translate v).toConvexSpaceBody ≤ (B.translate v).toConvexSpaceBody :=
  translate_carrier_subset_of_le A B v h

/-- **R2a re-measured: `1 ≤ a` is NOT retired, and it never bound the new-parent factor.**

The defect estimate's threshold is `Tube.gridScale δ N · ≤ θ₀`.  At the **outer** level it reads
`gridScale δ N a ≤ θ₀`, which `Kakeya.ML2Core.not_gridScale_zero_le_of_lt_one` refutes at `a = 0`
— that is R2a, and it stands.  At the **new-parent** level it reads `gridScale δ N p ≤ θ₀`, a
condition on `p` alone: it is satisfiable at `p ≥ 1` whatever `a` is.

So §5(ii)'s "the two guards come apart" is now measured on the factor *thresholds*, not only on
the seam: at `a = 0` the outer factor is unavailable and the new-parent factor is live — which is
the source's own `a = 0` case, `n_a = 1` with the outer family the single ambient cell (l.4447).

**Family/shading/level pair:** none; these are conditions on grid scales. -/
theorem outer_threshold_fails_at_zero_newParent_lives {N p : ℕ} {θ₀ : NNReal} (hθ₀ : θ₀ < 1)
    (hp : Tube.gridScale δ N p ≤ θ₀) :
    ¬ (Tube.gridScale δ N 0 ≤ θ₀) ∧ Tube.gridScale δ N p ≤ θ₀ :=
  ⟨not_gridScale_zero_le_of_lt_one hθ₀, hp⟩

omit [Nontrivial E] in
open Classical in
/-- **`hfullπ`, in the shape the new-parent factor consumes.**

The split's fullness chain gives the level-`p` family's fullness
(`Kakeya.ML2Reduction.exists_spineThreeScale`, re-exported); `ShadedBody.fullness` is a **ratio of
sums**, not an infimum, so passing to the `(a, p)` fibre costs a mass share and nothing less —
`Kakeya.ML2Core.mul_fullness_le_of_subset` is the exact vehicle.  Composing the two gives the
fibre's fullness at the loss `c · (L₁ L₂)⁻¹`.

The share `c` is the same object as the sites' own `hfull` (which they take from the centred
hand-back, not from the split): it is a statement about *which* level-`a` node `jθ` is chosen, and
the split does not choose it by mass.  Named here rather than absorbed.

**Family:** `(s, V)`; **shading:** `Ypo`, the split's level-`p` outer shading.
**Level pair:** `(a, p)` — the fibre — over the level-`p` family. -/
theorem fullness_newParentFibre_ge {ι : Type u} {tp' : Finset ι}
    {Ypo : ι → ShadedTube δ E} {c : NNReal} {jθ : ι} {pmap : ι → ι}
    (hshare : (c : ENNReal) * ∑ k ∈ tp', volume (Ypo k).shade
      ≤ ∑ k ∈ ({k ∈ tp' | pmap k = jθ} : Finset ι), volume (Ypo k).shade) :
    c * ShadedBody.fullness tp' (fun k => (Ypo k).toShadedBody)
      ≤ ShadedBody.fullness ({k ∈ tp' | pmap k = jθ} : Finset ι)
          (fun k => (Ypo k).toShadedBody) :=
  Kakeya.ML2Squeeze.mul_fullness_le_of_subset (Finset.filter_subset _ _) _ hshare

end Thresholds

section Retention

variable {δ Cu : NNReal} {ι : Type u}

open Classical in
/-- **Retention is about a *set*, and it does not pass to subsets.**

`Kakeya.ML2Core.RetentionAt 𝒰 p c t` puts `t` on the **right** of a containment, so shrinking `t`
destroys it.  The extreme case is here: the empty set — a subset of every retained set —
fails retention as soon as one level-`p` node has a nonempty descendant set.

This is the record that `Kakeya.ML2Core.threeLevelSeam_fibre_complete`, which is about the
**seam's** `t₁`, says nothing about the split's mass-pigeonholed `tτ' ⊆ t₁`; for that set the
vehicle is `Kakeya.ML2Core.retentionProportionAt_of_fibreRetention`.

**Family/shading:** hierarchy `𝒰` on `(s, V)`.  **Level pair:** `(p, c)`. -/
theorem not_retentionAt_empty {s : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    {p c : ℕ} {jp : ι} (hjp : jp ∈ 𝒰.cover.indexSet p)
    (hne : (𝒰.nodesUnder c p jp).Nonempty) :
    ¬ RetentionAt 𝒰 p c (∅ : Finset ι) := by
  intro hret
  obtain ⟨k, hk⟩ := hne
  have := hret jp hjp hk
  simp at this

end Retention

end Kakeya.ML2Core

end
