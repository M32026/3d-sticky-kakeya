/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorProfile
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeM1

/-!
# `R7` — the parent fill transfers along the tower

The parent-fill/volume-transfer step of the floor-shape device.  `Kakeya.ML2Core.FillAt` at the
coarse pair `(p, m₀)` and at the fine pair `(m₀, m')` compose into `FillAt` at `(p, m')`, at a
`δ`-free constant loss.  This is what makes **one** genuine parent `p` serve every window level:
the per-level fills are not independent obligations.

## The route, and the two corrections to `§2.7`

* **the decomposition is `F1`'s own machinery** — `Kakeya.ML2Core.twoScaleConst_spec` splits
  `Δ_max(𝕊_{m'}⟨T_p⟩)` over the level-`m₀` `Kakeya.ML2Reduction.coarseNode`s of the cells, at
  `C₀²`, and `Kakeya.ML2Core.maxDensity_ancestors_le_mul_sup` (`F1b`) pays the ancestors by the
  level-`p` nodes at `Cu`;
* **the counts are `X4`** — `Kakeya.ML2Core.card_nodesUnder_band` pins every one-pair descendant
  count to the branching profile within `Cu ^ 3`, so
  `#𝕊_{m₀}⟨T_p⟩ · #𝕊_{m'}⟨T_{m₀}⟩ ≤ Cu ^ 8 · #𝕊_{m'}⟨T_p⟩` at **every** triple of nodes
  (`card_nodesUnder_mul_card_le_card_nodesUnder`).  `§2.7`'s `max #fibre / min #fibre` is this,
  uniformly;
* **`§2.7`'s "both factors cancel exactly" is WRONG, and the honest constant carries
  `Kakeya.ML2Core.tubeVolRatio`.**  The cancellation of `v_{m'}/v_{m₀}` in the sketch assumes cells
  at one level have *equal* volume.  The tree bounds tube volumes only two-sidedly
  (`Tube.le_volume`, `Tube.volume_le`), so each of the three levels `p`, `m₀`, `m'` is crossed once
  and the loss is `tubeVolRatio n ^ 3`, `n = finrank ℝ E`.  It is a **constant**, not a `δ`-power —
  `tubeVolRatio` compares two tubes at the *same* radius, so the `δ^{n-1}` cancels exactly.
* **`§2.7`'s "there is no `(ρ_{m₀}/ρ_{m'})²` loss" survives**: the constant
  `Kakeya.ML2Core.fillTransConst` mentions no grid scale and no `δ`.

## The one departure from `§2.7`'s binder list, and why it is forced

`§2.7` writes `hpm₀ : FillAt 𝒰 κ p m₀ jp` at the **single** node `jp`, and `hm₀m'` over
`𝒰.nodesUnder m₀ p jp`.  **That is not enough, and the gap is `F1`'s ancestor set.**  The level-`m₀`
ancestor of a level-`m'` cell inside `T_p` is the `m₀`-node of *some member* of that cell's class
(`Kakeya.ML2Reduction.coarseNode`); a common lower bound gives no containment between the two upper
bodies, so the ancestor need **not** lie inside `T_p` and need not belong to `𝒰.nodesUnder m₀ p jp`.
`Kakeya.ML2Core.not_le_of_common_lower_bound` is the control for that step, and
`Kakeya.ML2Core.maxDensity_ancestors_le_mul_sup` — the only existing route to the ancestors — pays
them by a `sup` over the **whole** of `𝒰.cover.indexSet p`, not by the single node.

So `R7` takes the two fills **quantified over the index sets**, which is the weakest form that is
true along this route and which costs nothing downstream: `F4a`'s own `hfill` binder
(`Kakeya.ML2Core.floor_of_windowLevels_of_fill`) is already quantified over all `p`-cells under all
level-`a` nodes, and `R7`'s conclusion has the *same* shape as its hypotheses, so it iterates along
a chain of levels — which is `§2.7`'s "the fill composes along levels".

## What this discharges

`Kakeya.ML2Core.floorHypothesisAt_of_fillChain` plugs `R7` into the **fourth** conjunct of
`Kakeya.ML2Core.FloorHypothesisAt` — the count floor `(ρ_p/ρ_{m'})^{2+4ζ} ≤ #𝕊_{m'}⟨T_p⟩` — through
`F4a`, and hands back the whole `∃ p, …` of `FloorHypothesisAt`, hence
`Kakeya.ML2Core.RefinedFloorHypothesis`'s last field, by `exact`.
-/

@[expose] public section

open MeasureTheory Tube Topology Filter
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type u} {δ : NNReal}

/-! ### The control for `§2.7`'s missing containment -/

/-- **The control for the binder departure.**  A body contained in two others relates the
two in no way whatsoever.  This is exactly the step  needs and does not
have: from `T_{m'} ⊆ T_p` and `T_{m'} ⊆ T_{m₀}` one cannot conclude `T_{m₀} ⊆ T_p`, so the
level-`m₀`
ancestors of the cells under `T_p` are not `𝒰.nodesUnder m₀ p jp` and a fill at the single node
`jp` does not reach them. -/
theorem not_le_of_common_lower_bound :
    ∃ X Y Z : Set ℝ, X ⊆ Y ∧ X ⊆ Z ∧ ¬ Z ⊆ Y :=
  ⟨∅, {0}, {1}, Set.empty_subset _, Set.empty_subset _, by
    intro h
    have := h (Set.mem_singleton 1)
    simp at this⟩

/-! ### `X4`, read uniformly at three levels -/

/-- **The two-level counts multiply, within `Cu ^ 8`.**  `X4`
(`Kakeya.ML2Core.card_nodesUnder_band`) pins each one-pair descendant count to the branching
profile, so the product of a `(p, m₀)` count at *any* level-`p` node and an `(m₀, m')` count at
*any* level-`m₀` node is bounded by a `(p, m')` count at *any* level-`p` node, at the absolute
constant `Cu ^ 8`.  The branching numbers cancel — this is `§2.7`'s `max #fibre / min #fibre`
bound, and it holds uniformly rather than only between siblings. -/
theorem card_nodesUnder_mul_card_le_card_nodesUnder
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    {p m₀ m' : ℕ} (hpm₀ : p ≤ m₀) (hm₀m' : m₀ ≤ m') (hm'N : m' ≤ N)
    {j₁ : ι} (hj₁ : j₁ ∈ 𝒰.cover.indexSet p)
    {j₂ : ι} (hj₂ : j₂ ∈ 𝒰.cover.indexSet m₀)
    {j₃ : ι} (hj₃ : j₃ ∈ 𝒰.cover.indexSet p) :
    ((𝒰.nodesUnder m₀ p j₁).card : NNReal) * ((𝒰.nodesUnder m' m₀ j₂).card : NNReal)
      ≤ Cu ^ 8 * ((𝒰.nodesUnder m' p j₃).card : NNReal) := by
  have hm₀N : m₀ ≤ N := hm₀m'.trans hm'N
  have hb₀ : 0 < 𝒰.branchingN m₀ := branchingN_pos 𝒰 hs hm₀N
  have hb' : 0 < 𝒰.branchingN m' := branchingN_pos 𝒰 hs hm'N
  have h1 := (card_nodesUnder_band 𝒰 hpm₀ hm₀N hj₁).2
  have h2 := (card_nodesUnder_band 𝒰 hm₀m' hm'N hj₂).2
  have h3 := (card_nodesUnder_band 𝒰 (hpm₀.trans hm₀m') hm'N hj₃).1
  have key : (((𝒰.nodesUnder m₀ p j₁).card : NNReal) * ((𝒰.nodesUnder m' m₀ j₂).card : NNReal))
        * (𝒰.branchingN m₀ * 𝒰.branchingN m')
      ≤ (Cu ^ 8 * ((𝒰.nodesUnder m' p j₃).card : NNReal))
        * (𝒰.branchingN m₀ * 𝒰.branchingN m') := by
    calc (((𝒰.nodesUnder m₀ p j₁).card : NNReal) * ((𝒰.nodesUnder m' m₀ j₂).card : NNReal))
          * (𝒰.branchingN m₀ * 𝒰.branchingN m')
        = (((𝒰.nodesUnder m₀ p j₁).card : NNReal) * 𝒰.branchingN m₀)
          * (((𝒰.nodesUnder m' m₀ j₂).card : NNReal) * 𝒰.branchingN m') := by ring
      _ ≤ (Cu ^ 3 * 𝒰.branchingN p) * (Cu ^ 3 * 𝒰.branchingN m₀) := mul_le_mul' h1 h2
      _ = Cu ^ 6 * 𝒰.branchingN p * 𝒰.branchingN m₀ := by ring
      _ ≤ Cu ^ 6 * (Cu ^ 2 * (𝒰.branchingN m' * ((𝒰.nodesUnder m' p j₃).card : NNReal)))
            * 𝒰.branchingN m₀ := by gcongr
      _ = (Cu ^ 8 * ((𝒰.nodesUnder m' p j₃).card : NNReal))
            * (𝒰.branchingN m₀ * 𝒰.branchingN m') := by ring
  exact le_of_mul_le_mul_right key (mul_pos hb₀ hb')

/-! ### `FillAt`, read against the two dimensional tube-volume bounds -/

/-- **`FillAt` in volume form.**  The fill's `densityIn` is turned into a count by the two-sided
`δ`-tube volume bounds: the level-`c` cells inside `T_k` each have volume at most `C_n ρ_c^{n-1}`
and `T_k` itself has volume at least `c_n ρ_k^{n-1}`.  This is the only place the fill hypothesis
is used, and it is where the `tubeVolRatio` of `Kakeya.ML2Core.fillTransConst` is bought. -/
theorem maxDensity_mul_le_card_of_fillAt
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (hδ1 : δ ≤ 1) (𝒰 : Tube.UniformTubeSet s T N Cu)
    {κ : ℝ} {k c : ℕ} {j : ι} (hfill : FillAt 𝒰 κ k c j) :
    ENNReal.ofReal κ
        * Kakeya.maxDensity (𝒰.nodesUnder c k j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((Tube.gridScale δ N k : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ ((𝒰.nodesUnder c k j).card : ENNReal)
        * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((Tube.gridScale δ N c : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
  classical
  set n := Module.finrank ℝ E with hn
  set W : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube c j').toConvexSpaceBody with hW
  set Kj : ConvexSpaceBody E := (𝒰.cover.tube k j).toConvexSpaceBody with hKj
  have hmem : ∀ j' ∈ 𝒰.nodesUnder c k j, W j' ≤ Kj := by
    intro j' hj'
    have h := hj'
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn,
      Finset.mem_filter] at h
    exact h.2
  have hfam : Kakeya.familyIn (𝒰.nodesUnder c k j) W Kj = 𝒰.nodesUnder c k j :=
    Finset.filter_true_of_mem hmem
  have hvhi : ∀ i ∈ 𝒰.nodesUnder c k j, volume (W i).carrier
      ≤ ((Tube.volume_le.C n : NNReal) : ENNReal)
        * ((Tube.gridScale δ N c : NNReal) : ENNReal) ^ (n - 1) := fun i _ =>
    Tube.volume_le (gridScale_le_one hδ1 _ _) (𝒰.cover.tube c i)
  have hvlo : ((Tube.le_volume.c n : NNReal) : ENNReal)
        * ((Tube.gridScale δ N k : NNReal) : ENNReal) ^ (n - 1) ≤ volume Kj.carrier :=
    Tube.le_volume (𝒰.cover.tube k j)
  have hband := Kakeya.densityIn_mul_le_of_volume_band (𝒰.nodesUnder c k j) W Kj hvhi hvlo
  rw [hfam] at hband
  refine le_trans (mul_le_mul' hfill le_rfl) hband

/-! ### The two geometric blocks -/

/-- **One block of the transfer.**  The fill at the pair `(p, c)`, held at *every* level-`p` node,
turns the `sup` of the level-`c` maximal densities over `𝒰.cover.indexSet p` into a branching
ratio, at `Cu ^ 3` (`X4`'s upper half) and one crossing of the two-sided tube-volume bound.  It is
used twice: at `(p, m₀)` and at `(m₀, m')`. -/
theorem fill_block
    (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu)
    {κ : ℝ} {p c : ℕ} (hpc : p ≤ c) (hcN : c ≤ N)
    (hfill : ∀ j ∈ 𝒰.cover.indexSet p, FillAt 𝒰 κ p c j) :
    ENNReal.ofReal κ * ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((Tube.gridScale δ N p : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
        * ((𝒰.branchingN c : NNReal) : ENNReal)
        * ((𝒰.cover.indexSet p).sup fun j => Kakeya.maxDensity (𝒰.nodesUnder c p j)
            fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ (Cu : ENNReal) ^ 3 * ((𝒰.branchingN p : NNReal) : ENNReal)
        * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((Tube.gridScale δ N c : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
  classical
  rcases (𝒰.cover.indexSet p).eq_empty_or_nonempty with he | hne
  · rw [he]
    simp
  · obtain ⟨j, hj, hEq⟩ := Finset.exists_mem_eq_sup (𝒰.cover.indexSet p) hne
      (fun j => Kakeya.maxDensity (𝒰.nodesUnder c p j)
        fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
    rw [hEq]
    have hvol := maxDensity_mul_le_card_of_fillAt hδ1 𝒰 (hfill j hj)
    have hX4 : (((𝒰.nodesUnder c p j).card : ℕ) : ENNReal) * ((𝒰.branchingN c : NNReal) : ENNReal)
        ≤ (Cu : ENNReal) ^ 3 * ((𝒰.branchingN p : NNReal) : ENNReal) := by
      exact_mod_cast (card_nodesUnder_band 𝒰 hpc hcN hj).2
    calc ENNReal.ofReal κ * ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((Tube.gridScale δ N p : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
            * ((𝒰.branchingN c : NNReal) : ENNReal)
            * Kakeya.maxDensity (𝒰.nodesUnder c p j)
                (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
        = (ENNReal.ofReal κ
              * Kakeya.maxDensity (𝒰.nodesUnder c p j)
                  (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
              * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
                * ((Tube.gridScale δ N p : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)))
            * ((𝒰.branchingN c : NNReal) : ENNReal) := by ring
      _ ≤ (((𝒰.nodesUnder c p j).card : ENNReal)
              * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
                * ((Tube.gridScale δ N c : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)))
            * ((𝒰.branchingN c : NNReal) : ENNReal) := by gcongr
      _ = (((𝒰.nodesUnder c p j).card : ENNReal) * ((𝒰.branchingN c : NNReal) : ENNReal))
            * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((Tube.gridScale δ N c : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by ring
      _ ≤ ((Cu : ENNReal) ^ 3 * ((𝒰.branchingN p : NNReal) : ENNReal))
            * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((Tube.gridScale δ N c : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
          gcongr
      _ = (Cu : ENNReal) ^ 3 * ((𝒰.branchingN p : NNReal) : ENNReal)
            * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((Tube.gridScale δ N c : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by ring

omit [Nontrivial E] in
open scoped Classical in
/-- **`F1`'s fibre `sup` is dominated by the `sup` of the fine cells under the level-`m₀` nodes.**
`F1` measures each fibre as the image of a level-`m₀` class under `assign m'`; that image is a
subset of `𝒰.nodesUnder m' m₀ ·` (the assignments nest), and the fibre's own base point is a
genuine level-`m₀` node (`Kakeya.ML2Reduction.coarseNode_mem`), so `Kakeya.maxDensity_mono` and
`Finset.le_sup` move the whole `sup` onto the index set `Kakeya.ML2Core.fill_block` is stated at. -/
theorem sup_fibre_le_sup_nodesUnder
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    {p m₀ m' : ℕ} (hm₀m' : m₀ ≤ m') (hm'N : m' ≤ N) (jp : ι) :
    ((𝒰.nodesUnder m' p jp).image (ML2Reduction.coarseNode 𝒰.cover.toChain m₀ m')).sup
        (fun jp' => Kakeya.maxDensity
          ((coverClass s (𝒰.cover.assign m₀) jp').image (𝒰.cover.assign m'))
          (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody))
      ≤ (𝒰.cover.indexSet m₀).sup fun j => Kakeya.maxDensity (𝒰.nodesUnder m' m₀ j)
          fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody := by
  classical
  refine Finset.sup_le (fun jp' hjp' => ?_)
  obtain ⟨jc, hjc, rfl⟩ := Finset.mem_image.mp hjp'
  have hjcidx : jc ∈ 𝒰.cover.indexSet m' := by
    have h := hjc
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn,
      Finset.mem_filter] at h
    exact h.1
  have hact : jc ∈ ML2Reduction.activeNodes 𝒰.cover.toChain m' :=
    Finset.mem_filter.mpr ⟨hjcidx,
      Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hm'N hs hjcidx⟩
  have hmem : ML2Reduction.coarseNode 𝒰.cover.toChain m₀ m' jc ∈ 𝒰.cover.indexSet m₀ :=
    ML2Reduction.coarseNode_mem 𝒰.cover.toChain (hm₀m'.trans hm'N) hact
  have hsub : (coverClass s (𝒰.cover.assign m₀)
        (ML2Reduction.coarseNode 𝒰.cover.toChain m₀ m' jc)).image (𝒰.cover.assign m')
      ⊆ 𝒰.nodesUnder m' m₀ (ML2Reduction.coarseNode 𝒰.cover.toChain m₀ m' jc) := by
    intro j' hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
    simp only [coverClass, Finset.mem_filter] at hi
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn, Finset.mem_filter]
    refine ⟨𝒰.cover.assign_mem m' hm'N i hi.1, ?_⟩
    have h : (𝒰.cover.tube m' (𝒰.cover.assign m' i)).toConvexSpaceBody
        ≤ (𝒰.cover.tube m₀ (𝒰.cover.assign m₀ i)).toConvexSpaceBody :=
      𝒰.cover.toChain.tube_assign_le hm₀m' hm'N hi.1
    rw [hi.2] at h
    exact h
  exact le_trans (Kakeya.maxDensity_mono _ hsub)
    (Finset.le_sup (f := fun j => Kakeya.maxDensity (𝒰.nodesUnder m' m₀ j)
      fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody) hmem)

/-! ### The algebra of the transfer, isolated -/

/-- **`R7`'s arithmetic, with the geometry removed.**  Every hypothesis is one of the five blocks — `F1`, `F1b`, the two fill/volume bounds, the count band and the lower volume bound — and
the conclusion is the fill at the composite pair.  Isolating it keeps the geometric proof free of
`ENNReal` bookkeeping, and it makes visible that **the only cancellations are of `b0`, `b'`, `ρ0`,
`ρp` and `cv`**: no grid ratio and no `δ`-power survives, which is 's
"there is no `(ρ_{m₀}/ρ_{m'})²` loss".  The three crossings of the two-sided tube-volume bound are
the three occurrences of `tvr` (`Kakeya.ML2Core.tubeVolRatio`) in `hk`. -/
theorem fill_trans_algebra
    {Δ M S SUPP D nQ bp b0 b' K C₀ Cu cv Cv ρp ρ0 ρ' tvr kk : ℝ≥0∞}
    (hF1 : Δ ≤ C₀ ^ 2 * M * S)
    (hF1b : M ≤ Cu * SUPP)
    (hSUPP : K * cv * ρp * b0 * SUPP ≤ Cu ^ 3 * bp * (Cv * ρ0))
    (hS : K * cv * ρ0 * b' * S ≤ Cu ^ 3 * b0 * (Cv * ρ'))
    (hlow : nQ * (cv * ρ') ≤ D * (Cv * ρp))
    (hband : bp ≤ Cu ^ 2 * (b' * nQ))
    (hCv : Cv = cv * tvr)
    (hk : kk * (C₀ ^ 2 * Cu ^ 9 * tvr ^ 3) ≤ K ^ 2)
    (hb00 : b0 ≠ 0) (hb0t : b0 ≠ ⊤) (hb'0 : b' ≠ 0) (hb't : b' ≠ ⊤)
    (hρ00 : ρ0 ≠ 0) (hρ0t : ρ0 ≠ ⊤) (hρp0 : ρp ≠ 0) (hρpt : ρp ≠ ⊤)
    (hcv0 : cv ≠ 0) (hcvt : cv ≠ ⊤)
    (hZ0 : C₀ ^ 2 * Cu ^ 9 * tvr ^ 3 ≠ 0) (hZt : C₀ ^ 2 * Cu ^ 9 * tvr ^ 3 ≠ ⊤) :
    kk * Δ ≤ D := by
  have hG0 : b0 * b' * ρ0 ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨hb00, hb'0⟩, hρ00⟩
  have hGt : b0 * b' * ρ0 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hb0t hb't) hρ0t
  -- the two blocks, multiplied
  have h2 : K ^ 2 * cv ^ 2 * ρp * Δ * (b0 * b' * ρ0)
      ≤ C₀ ^ 2 * Cu ^ 9 * Cv ^ 2 * ρ' * nQ * (b0 * b' * ρ0) := by
    calc K ^ 2 * cv ^ 2 * ρp * Δ * (b0 * b' * ρ0)
        = K * cv * ρp * b0 * (K * cv * ρ0 * b') * Δ := by ring
      _ ≤ K * cv * ρp * b0 * (K * cv * ρ0 * b') * (C₀ ^ 2 * (Cu * SUPP) * S) := by
          gcongr
          exact hF1.trans (by gcongr)
      _ = C₀ ^ 2 * Cu * (K * cv * ρp * b0 * SUPP) * (K * cv * ρ0 * b' * S) := by ring
      _ ≤ C₀ ^ 2 * Cu * (Cu ^ 3 * bp * (Cv * ρ0)) * (Cu ^ 3 * b0 * (Cv * ρ')) := by
          gcongr
      _ ≤ C₀ ^ 2 * Cu * (Cu ^ 3 * (Cu ^ 2 * (b' * nQ)) * (Cv * ρ0))
            * (Cu ^ 3 * b0 * (Cv * ρ')) := by
          gcongr
      _ = C₀ ^ 2 * Cu ^ 9 * Cv ^ 2 * ρ' * nQ * (b0 * b' * ρ0) := by ring
  have h3 : K ^ 2 * cv ^ 2 * ρp * Δ ≤ C₀ ^ 2 * Cu ^ 9 * Cv ^ 2 * ρ' * nQ :=
    (ENNReal.mul_le_mul_iff_left hG0 hGt).mp h2
  -- the lower volume bound
  have h4 : K ^ 2 * cv ^ 3 * Δ * ρp ≤ C₀ ^ 2 * Cu ^ 9 * Cv ^ 3 * D * ρp := by
    calc K ^ 2 * cv ^ 3 * Δ * ρp = K ^ 2 * cv ^ 2 * ρp * Δ * cv := by ring
      _ ≤ C₀ ^ 2 * Cu ^ 9 * Cv ^ 2 * ρ' * nQ * cv := by gcongr
      _ = C₀ ^ 2 * Cu ^ 9 * Cv ^ 2 * (nQ * (cv * ρ')) := by ring
      _ ≤ C₀ ^ 2 * Cu ^ 9 * Cv ^ 2 * (D * (Cv * ρp)) := by gcongr
      _ = C₀ ^ 2 * Cu ^ 9 * Cv ^ 3 * D * ρp := by ring
  have h5 : K ^ 2 * cv ^ 3 * Δ ≤ C₀ ^ 2 * Cu ^ 9 * Cv ^ 3 * D :=
    (ENNReal.mul_le_mul_iff_left hρp0 hρpt).mp h4
  -- trade `Cv` for `cv * tvr` and cancel `cv ^ 3`
  have h6 : K ^ 2 * Δ * cv ^ 3 ≤ C₀ ^ 2 * Cu ^ 9 * tvr ^ 3 * D * cv ^ 3 := by
    calc K ^ 2 * Δ * cv ^ 3 = K ^ 2 * cv ^ 3 * Δ := by ring
      _ ≤ C₀ ^ 2 * Cu ^ 9 * Cv ^ 3 * D := h5
      _ = C₀ ^ 2 * Cu ^ 9 * tvr ^ 3 * D * cv ^ 3 := by rw [hCv]; ring
  have h7 : K ^ 2 * Δ ≤ C₀ ^ 2 * Cu ^ 9 * tvr ^ 3 * D :=
    (ENNReal.mul_le_mul_iff_left (pow_ne_zero _ hcv0) (ENNReal.pow_ne_top hcvt)).mp h6
  -- spend the threshold on `kk`
  have h8 : C₀ ^ 2 * Cu ^ 9 * tvr ^ 3 * (kk * Δ) ≤ C₀ ^ 2 * Cu ^ 9 * tvr ^ 3 * D := by
    calc C₀ ^ 2 * Cu ^ 9 * tvr ^ 3 * (kk * Δ)
        = kk * (C₀ ^ 2 * Cu ^ 9 * tvr ^ 3) * Δ := by ring
      _ ≤ K ^ 2 * Δ := by gcongr
      _ ≤ C₀ ^ 2 * Cu ^ 9 * tvr ^ 3 * D := h7
  exact (ENNReal.mul_le_mul_iff_right hZ0 hZt).mp h8

/-! ### `R7` -/

/-- **`R7`'s constant.**  `C₀² · Cu⁹ · tubeVolRatio n ³`, with `C₀ = Kakeya.ML2Core.twoScaleConst E`
the two-scale constant of `F1`.  `Cu⁹ = Cu` (`F1b`'s ancestor payment) `· Cu⁸` (`X4`, three
one-pair bands); `tubeVolRatio n ³` is one crossing of the two-sided tube-volume bound at each of
the three levels `p`, `m₀`, `m'`.

**This constant is `δ`-FREE, and so is each one of its three factors** — stated explicitly here, per
(B) condition `C-R7a`, rather than left to be read off the syntax.

* `Kakeya.ML2Core.twoScaleConst E` is **`δ`-free**: it is `Classical.choose` of
  `Kakeya.ML2Core.exists_twoScale_nodesUnder`, whose `∃ C` is quantified **before** the
  `∀ {ι} {δ}` of the body.  It depends on `E` alone.
* `Cu` is **`δ`-free in this construction**: the descent site hoists `∃ Cu₀ : NNReal` before
  `∀ᶠ δ`, with `Cu ≤ Cu₀` the primitive row and `Cu ≤ δ⁻¹` the derived one, so
  `fillTransConst E Cu ≤ fillTransConst E Cu₀` bounds this constant by a `δ`-free quantity.
  Reading `Cu` through `Cu ≤ δ⁻¹` instead would make the constant `δ^{-9}` and would void the `+0`
  gain-ledger entry — that is precisely the reading  rejected.
* `Kakeya.ML2Core.tubeVolRatio (Module.finrank ℝ E)` is **`δ`-free** because it compares two tubes
  at the **same** radius: it is `Tube.volume_le.C n / Tube.le_volume.c n`, and the `δ^{n-1}`
  cancels exactly.  It
  depends on the dimension alone.

So no grid scale, no window level and no `δ`-power occurs anywhere in this definition — which is
's *"there is no `(ρ_{m₀}/ρ_{m'})²` loss"*, and which is why `R7` costs **no
exponent**: the entire price is a smaller `κ`, hence a smaller threshold `δ₀`, and `κ` reaches `F4a`
only through `hclose`, discharged by `floor_exponent_closes` below
`δ₀(β, ϖ, ε₁, gain, dens, κ, Cu₀, C₀)`.

**Why this paragraph is here.**  Twice on this run a quantity called a "constant" turned out to sit
on the wrong side of `∀ᶠ δ`: `Cu` at the descent site and `Λf` in `M1`'s binder
( — specified `Λf : NNReal → ℝ≥0∞`, with `hΛf` inside the filter).  Both were caught by
measurement, not by reading, because the `δ`-free claim had never been written down.  A later hand
that changes any factor above must re-establish this list factor by factor, or the `+0` ledger
entry is void. -/
noncomputable def fillTransConst (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (Cu : NNReal) : ℝ :=
  twoScaleConst.{u, v} E ^ 2 * (Cu : ℝ) ^ 9
    * ((tubeVolRatio (Module.finrank ℝ E) : NNReal) : ℝ) ^ 3

theorem fillTransConst_pos {Cu : NNReal} (hCu : 0 < Cu) : 0 < fillTransConst.{u, v} E Cu := by
  have h0 : 0 < twoScaleConst.{u, v} E := twoScaleConst_pos E
  have h1 : (0 : ℝ) < (Cu : ℝ) := by exact_mod_cast hCu
  have h2 : (0 : ℝ) < ((tubeVolRatio (Module.finrank ℝ E) : NNReal) : ℝ) := by
    have : (0 : NNReal) < tubeVolRatio (Module.finrank ℝ E) := by
      rw [tubeVolRatio]
      exact div_pos (Tube.volume_le.C_pos _) (Tube.le_volume.c_pos _)
    exact_mod_cast this
  rw [fillTransConst]
  positivity

open scoped Classical in
/-- **`R7` — the fill composes along the tower**.  Given the fill at the coarse pair `(p, m₀)` at every
level-`p` node and at the fine pair `(m₀, m')` at every level-`m₀` node, the fill holds at `(p, m')`
at every level-`p` node, at the constant loss `κ ↦ κ² / fillTransConst E Cu`.

`κ'` is a binder with a threshold rather than a formula — the shape `F4a`'s `hclose` uses — so that
a caller may spend a weaker `κ'` it already has; `Kakeya.ML2Core.fillAt_trans` is this at the
explicit quotient. -/
theorem fillAt_trans_of_le
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {κ κ' : ℝ} (hκ : 0 < κ)
    (hκ' : κ' * fillTransConst.{u, v} E Cu ≤ κ ^ 2)
    {p m₀ m' : ℕ} (hpm₀ : p ≤ m₀) (hm₀m' : m₀ ≤ m') (hm'N : m' ≤ N)
    (hgap : 4 * Tube.gridScale δ N m' ≤ Tube.gridScale δ N m₀)
    (hfillP : ∀ j ∈ 𝒰.cover.indexSet p, FillAt 𝒰 κ p m₀ j)
    (hfillM : ∀ j ∈ 𝒰.cover.indexSet m₀, FillAt 𝒰 κ m₀ m' j) :
    ∀ jp ∈ 𝒰.cover.indexSet p, FillAt 𝒰 κ' p m' jp := by
  classical
  intro jp hjp
  have hm₀N : m₀ ≤ N := hm₀m'.trans hm'N
  have hpN : p ≤ N := hpm₀.trans hm₀N
  have hCu : 0 < Cu := uniform_C_pos 𝒰 hs hpN
  -- `F1` and `F1b`, at the given `p`-cell
  have hF1 := twoScaleConst_spec hδ0 hδ1 𝒰 hs hball (a := p) hm₀m' hm'N hgap jp
  have hF1b := maxDensity_ancestors_le_mul_sup 𝒰 hs hpm₀ hm₀m' hm'N jp
  -- the two fill blocks
  have hblkP := fill_block hδ1 𝒰 hpm₀ hm₀N hfillP
  have hblkM := fill_block hδ1 𝒰 hm₀m' hm'N hfillM
  have hdom := sup_fibre_le_sup_nodesUnder 𝒰 hs (p := p) hm₀m' hm'N jp
  have hS : ENNReal.ofReal κ * ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((Tube.gridScale δ N m₀ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
        * ((𝒰.branchingN m' : NNReal) : ENNReal)
        * (((𝒰.nodesUnder m' p jp).image (ML2Reduction.coarseNode 𝒰.cover.toChain m₀ m')).sup
            (fun jp' => Kakeya.maxDensity
              ((coverClass s (𝒰.cover.assign m₀) jp').image (𝒰.cover.assign m'))
              (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody)))
      ≤ (Cu : ENNReal) ^ 3 * ((𝒰.branchingN m₀ : NNReal) : ENNReal)
        * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((Tube.gridScale δ N m' : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) :=
    le_trans (mul_le_mul' le_rfl hdom) hblkM
  -- the lower volume bound and the count band
  have hlow := Kakeya.MultiScaleFac.card_nodesUnder_mul_le_densityIn (a := p) (b := m')
    hδ0 hδ1 𝒰 hpN (j := jp)
  have hband : ((𝒰.branchingN p : NNReal) : ENNReal)
      ≤ (Cu : ENNReal) ^ 2 * (((𝒰.branchingN m' : NNReal) : ENNReal)
          * ((𝒰.nodesUnder m' p jp).card : ENNReal)) := by
    exact_mod_cast (card_nodesUnder_band 𝒰 (hpm₀.trans hm₀m') hm'N hjp).1
  have hCveq : ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
      = ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((tubeVolRatio (Module.finrank ℝ E) : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_mul, le_volume_c_mul_tubeVolRatio]
  -- the threshold, moved into `ℝ≥0∞`
  have htvrR : (0 : ℝ) ≤ ((tubeVolRatio (Module.finrank ℝ E) : NNReal) : ℝ) := (tubeVolRatio _).2
  have hCuR : (0 : ℝ) ≤ (Cu : ℝ) := Cu.2
  have hC₀R : (0 : ℝ) ≤ twoScaleConst.{u, v} E := (twoScaleConst_pos.{u, v} E).le
  have hZeq : ENNReal.ofReal (fillTransConst.{u, v} E Cu)
      = ENNReal.ofReal (twoScaleConst.{u, v} E) ^ 2 * (Cu : ENNReal) ^ 9
        * ((tubeVolRatio (Module.finrank ℝ E) : NNReal) : ENNReal) ^ 3 := by
    rw [fillTransConst, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hC₀R, ENNReal.ofReal_pow hCuR, ENNReal.ofReal_pow htvrR,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  have hk : ENNReal.ofReal κ' * (ENNReal.ofReal (twoScaleConst.{u, v} E) ^ 2 * (Cu : ENNReal) ^ 9
        * ((tubeVolRatio (Module.finrank ℝ E) : NNReal) : ENNReal) ^ 3)
      ≤ ENNReal.ofReal κ ^ 2 := by
    have h := ENNReal.ofReal_le_ofReal hκ'
    rw [ENNReal.ofReal_mul' (by rw [fillTransConst]; positivity), ENNReal.ofReal_pow hκ.le,
      hZeq] at h
    exact h
  -- the five nondegeneracy facts the cancellations need
  have hb00 : ((𝒰.branchingN m₀ : NNReal) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (branchingN_pos 𝒰 hs hm₀N).ne'
  have hb'0 : ((𝒰.branchingN m' : NNReal) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (branchingN_pos 𝒰 hs hm'N).ne'
  have hρ00 : ((Tube.gridScale δ N m₀ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ 0 :=
    pow_ne_zero _ (ENNReal.coe_ne_zero.mpr (gridScale_pos hδ0 N m₀).ne')
  have hρp0 : ((Tube.gridScale δ N p : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ 0 :=
    pow_ne_zero _ (ENNReal.coe_ne_zero.mpr (gridScale_pos hδ0 N p).ne')
  have hcv0 : ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos _).ne'
  have htvr0 : ((tubeVolRatio (Module.finrank ℝ E) : NNReal) : ENNReal) ≠ 0 := by
    refine ENNReal.coe_ne_zero.mpr ?_
    rw [tubeVolRatio]
    exact (div_pos (Tube.volume_le.C_pos _) (Tube.le_volume.c_pos _)).ne'
  have hCu0 : (Cu : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hCu.ne'
  have hC₀0 : ENNReal.ofReal (twoScaleConst.{u, v} E) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (twoScaleConst_pos.{u, v} E)).ne'
  exact fill_trans_algebra hF1 hF1b hblkP hS hlow hband hCveq hk
    hb00 ENNReal.coe_ne_top hb'0 ENNReal.coe_ne_top
    hρ00 (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    hρp0 (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    hcv0 ENNReal.coe_ne_top
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hC₀0) (pow_ne_zero _ hCu0)) (pow_ne_zero _ htvr0))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)) (ENNReal.pow_ne_top ENNReal.coe_ne_top))


/-! ### The explicit constant, and the monotonicity the chaining needs -/

omit [Nontrivial E] in
/-- **`FillAt` is antitone in `κ`.**  A weaker fill constant is a weaker statement. -/
theorem fillAt_mono {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) {κ κ' : ℝ} (hle : κ' ≤ κ) {k c : ℕ} {j : ι}
    (hfill : FillAt 𝒰 κ k c j) : FillAt 𝒰 κ' k c j :=
  le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl) hfill

/-- **`R7` at the explicit constant**: the composed fill holds at `κ² / fillTransConst E Cu`.  No hypothesis on `Cu` or on
the dimension is needed — at a degenerate constant the quotient is `0` and the statement is
vacuously true, which is why `Kakeya.ML2Core.fillAt_trans_of_le`'s threshold form is the primitive
and this is the derived row. -/
theorem fillAt_trans
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {κ : ℝ} (hκ : 0 < κ)
    {p m₀ m' : ℕ} (hpm₀ : p ≤ m₀) (hm₀m' : m₀ ≤ m') (hm'N : m' ≤ N)
    (hgap : 4 * Tube.gridScale δ N m' ≤ Tube.gridScale δ N m₀)
    (hfillP : ∀ j ∈ 𝒰.cover.indexSet p, FillAt 𝒰 κ p m₀ j)
    (hfillM : ∀ j ∈ 𝒰.cover.indexSet m₀, FillAt 𝒰 κ m₀ m' j) :
    ∀ jp ∈ 𝒰.cover.indexSet p,
      FillAt 𝒰 (κ ^ 2 / fillTransConst.{u, v} E Cu) p m' jp := by
  refine fillAt_trans_of_le hδ0 hδ1 𝒰 hs hball hκ ?_ hpm₀ hm₀m' hm'N hgap hfillP hfillM
  rcases eq_or_ne (fillTransConst.{u, v} E Cu) 0 with h | h
  · rw [h, mul_zero]
    positivity
  · rw [div_mul_cancel₀ _ h]

/-! ### `R7` in `F4a`'s binder shape, and the plug-in -/

/-- **`R7`, lifted to `F4a`'s `hfill` binder.**  One genuine parent `p` and one intermediate level
`m₀` serve **every** window level `c ≤ b`: above `m₀` by `R7`, at `m₀` by the coarse fill itself,
and below `m₀` — the finitely many levels the tower has between `p` and `m₀` — by `hbelow`, which
is empty whenever `m₀ = p + 1`.  This is 's *"with `R7` the per-level fills
are not independent obligations"*, in the exact shape
`Kakeya.ML2Core.floor_of_windowLevels_of_fill` consumes. -/
theorem fill_binder_of_trans
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {κ κ' : ℝ} (hκ : 0 < κ) (hκ'κ : κ' ≤ κ)
    (hκ' : κ' * fillTransConst.{u, v} E Cu ≤ κ ^ 2)
    {a p m₀ b : ℕ} (hpm₀ : p ≤ m₀) (hbN : b ≤ N)
    (hgap : ∀ c : ℕ, m₀ < c → c ≤ b →
      4 * Tube.gridScale δ N c ≤ Tube.gridScale δ N m₀)
    (hfillP : ∀ j ∈ 𝒰.cover.indexSet p, FillAt 𝒰 κ p m₀ j)
    (hfillM : ∀ c : ℕ, m₀ < c → c ≤ b → ∀ j ∈ 𝒰.cover.indexSet m₀, FillAt 𝒰 κ m₀ c j)
    (hbelow : ∀ c : ℕ, p < c → c < m₀ → ∀ j ∈ 𝒰.cover.indexSet p, FillAt 𝒰 κ' p c j) :
    ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ c : ℕ, p < c → c ≤ b →
      FillAt 𝒰 κ' p c jp := by
  intro jθ _ jp hjp c hpc hcb
  have hjpidx : jp ∈ 𝒰.cover.indexSet p := by
    have h := hjp
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn,
      Finset.mem_filter] at h
    exact h.1
  rcases lt_trichotomy c m₀ with h | h | h
  · exact hbelow c hpc h jp hjpidx
  · subst h
    exact fillAt_mono 𝒰 hκ'κ (hfillP jp hjpidx)
  · exact fillAt_trans_of_le hδ0 hδ1 𝒰 hs hball hκ hκ' hpm₀ h.le (hcb.trans hbN)
      (hgap c h hcb) hfillP (hfillM c h hcb) jp hjpidx

open scoped Classical in
/-- **The plug-in: `R7` discharges `Kakeya.ML2Core.FloorHypothesisAt`.**  With `F4a`
(`Kakeya.ML2Core.floor_of_windowLevels_of_fill`) for the count floor and `R7` for its `hfill`
binder, the four conjuncts of `FloorHypothesisAt` are `hap`, `hprec`, `hpar` and `F4a`'s
conclusion — the last of which is the existing `hfloor` clause 4 byte for byte.  Since
`Kakeya.ML2Core.RefinedFloorHypothesis`'s final field **is** `FloorHypothesisAt` read on
`Kakeya.ML2Core.refinedHierarchy`, this theorem discharges that field by `exact`.

The binders are `F4a`'s own, with `hfill` replaced by `R7`'s inputs and `hprec` — the "the parent
precedes every inset window level" conjunct of `FloorHypothesisAt` — added; nothing else moves. -/
theorem floorHypothesisAt_of_fillTrans
    {β ϖ ε₁ η' κ κ₀ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hκ₀ : 0 < κ₀) (hκκ₀ : κ ≤ κ₀)
    {ι : Type u} {δ Cu : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hκ' : κ * fillTransConst.{u, 0} (EuclideanSpace ℝ (Fin 3)) Cu ≤ κ₀ ^ 2)
    {u : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (hs : u.Nonempty)
    (hball : ∀ i ∈ u, ((V i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal} {a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar
      (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
      (ML2Spine.spineCount ϖ ε₁) a b m)
    (hCstar : Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)))
    (hcap : η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hgap : ∀ p c : ℕ, a ≤ p → p < c → c ≤ b →
      4 * (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ))
    {p m₀ : ℕ} (hap : a ≤ p) (hpm₀ : p ≤ m₀) (hpar : ParentAdmissible 𝒰 η' a p)
    (hprec : ∀ m' : ℕ, a < m' → m' < b →
      ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
        ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
      p < m')
    (hfillP : ∀ j ∈ 𝒰.cover.indexSet p, FillAt 𝒰 κ₀ p m₀ j)
    (hfillM : ∀ c : ℕ, m₀ < c → c ≤ b → ∀ j ∈ 𝒰.cover.indexSet m₀, FillAt 𝒰 κ₀ m₀ c j)
    (hbelow : ∀ c : ℕ, p < c → c < m₀ → ∀ j ∈ 𝒰.cover.indexSet p, FillAt 𝒰 κ p c j)
    (hclose : ∀ m' : ℕ, a + ⌈ML2Spine.spineDiv ϖ ε₁ * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m' → p < m' →
      m' ≤ b →
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
          * (Cstar ^ 2 * ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3)) ^ 2)
              * (Cu : ENNReal) * (δ : ENNReal) ^ (-(2 * η'))
              * ((Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
                : ENNReal))
        ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
          * ENNReal.ofReal κ
          * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
            : ENNReal)) :
    FloorHypothesisAt β ϖ ε₁ gain dens η' 𝒰 a b m := by
  refine ⟨p, hap, hprec, hpar, ?_⟩
  have hbN : b ≤ Tube.ssfGridLen δ := hwin.fine_le_gridLen
  have hgapw : ∀ c : ℕ, m₀ < c → c ≤ b →
      4 * Tube.gridScale δ (Tube.ssfGridLen δ) c
        ≤ Tube.gridScale δ (Tube.ssfGridLen δ) m₀ := by
    intro c hc hcb
    exact_mod_cast hgap m₀ c (hap.trans hpm₀) hc hcb
  exact floor_of_windowLevels_of_fill hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1 𝒰 hs hball
    hwin hCstar hcap hgap hap hpar
    (fill_binder_of_trans hδ0 hδ1.le 𝒰 hs hball hκ₀ hκκ₀ hκ' hpm₀ hbN hgapw hfillP hfillM hbelow)
    hclose

/-- **Which field `R7` discharges, made a fact.**  The last of
`Kakeya.ML2Core.RefinedFloorHypothesis`'s three fields is `Kakeya.ML2Core.FloorHypothesisAt` read
on `Kakeya.ML2Core.refinedHierarchy`; supplying it by `exact` is all that is left once the
refinement data and the `C-M1c` twin are in hand.  So the output of
`Kakeya.ML2Core.floorHypothesisAt_of_fillTrans`, at the refined hierarchy, is exactly `M1`'s
hypothesis — and `R7` is what removes the per-level quantifier from it. -/
theorem refinedFloorHypothesis_of_floorHypothesisAt {ι : Type u} {δ Cu : NNReal}
    {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {S : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet S (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (a b m : ℕ)
    {S' : Finset ι} {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hS' : S' ⊆ S) (hhom : IsClassHomogeneousOn 𝒰 S')
    (hW : (fun i ↦ (W i).toTube) = (fun i ↦ (T i).toTube))
    (href : IsShadedRefinementOf 𝒰 Λf S T S' W)
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels (refinedHierarchy 𝒰 hS' hhom hW)
      ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
      (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m)
    (hflo : FloorHypothesisAt β ϖ ε₁ gain dens η' (refinedHierarchy 𝒰 hS' hhom hW) a b m) :
    RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl)
      β ϖ ε₁ gain dens η' Λf 𝒰 a b m :=
  ⟨S', W, hS', hhom, hW, href, hwin, hflo⟩

end Kakeya.ML2Core
