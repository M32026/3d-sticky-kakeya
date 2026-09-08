/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorTwoScale

/-!
# GWZ Lemma 7.4 at `M = 2`, on an **arbitrary** level-`c` family

`Kakeya.ML2Core.exists_twoScale_nodesUnder` (`SpineFloorTwoScale.lean:107`) states the two-scale
bound for `Q₂ = Tube.UniformTubeSet.nodesUnder c a j`.  **Its proof never uses that shape.**  Read
it: the level-`a` node `T_a` does not enter the geometry at all — the three-level datum is
`ρ = (4, ρ_p, ρ_c)` with the *coarsest* tube the **ambient radius-`4` tube** `amb` centred at the
origin, and `j` appears only as the label of the singleton `Q 0 = {j}`.  The only property of `Q₂`
that is used is `hQ2idx : ∀ jc ∈ Q₂, jc ∈ 𝒰.cover.indexSet c`.

So the lemma holds for **any** subfamily of the level-`c` index set, and that is what this file
states.  The generalisation is what the **fibre** array needs: to run the two-scale inequality on a
thread cell `𝕋_c⟨S_a⟩` (the source's object, Definition 2.1(ii) l.222-224) rather than on the
containment set, `Q₂` must be the assignment fibre, which is not of the form `nodesUnder c a j`.

## Why this is the step that removes the `Cu`

In `Kakeya.ML2Core.towerDensityArray_submultiplicative` the first factor costs a `Cu`, paid by
`maxDensity_ancestors_le_mul_sup`, because a level-`p` ancestor of a cell *contained* in `T_a` need
not itself lie in `T_a`.  **On a thread cell that cannot happen**: Definition 2.1(ii) says
`π_{k-1} = q_k ∘ π_k`, so the ancestors of `𝕋_c⟨S_a⟩` lie in `𝕋_p⟨S_a⟩` — the compatible-partition
clause.  Compiled at `Kakeya.ML2Core.image_coarseNode_assignFibre_subset` in
`SpineTowerArrayFibre.lean`, and the fibre submultiplicativity is therefore at `C₀'(E)²` with **no
`Cu`**, which is the shape the source prints (`300⁹C₂`, with `C₂` its geometric-competitor constant
— the analogue of the `Cu` that only the containment reading needs).

## `twoScaleConst` is NOT touched

`Kakeya.ML2Core.twoScaleConst` and its two characterisations `twoScaleConst_pos` /
`twoScaleConst_spec` keep their definitions and statements verbatim, and every existing consumer
(`SpineFloorCount.lean`, `SpineFloorShapeParentFill.lean`) is untouched.  This file introduces one
new named constant `twoScaleSubsetConst`, and `twoScale_nodesUnder_at_subsetConst` records —
— that the `nodesUnder` form also holds at it, so the two are interchangeable and no
consumer is forced to choose.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `exists_twoScale_subset` | `𝒰` on `(s,T)`; no shading | `(p,c)`; the `a`-anchor is **gone** |
| `twoScaleSubsetConst` | none | none |
| `twoScaleSubsetConst_spec` | as `exists_twoScale_subset` | `(p,c)` |
| `twoScale_nodesUnder_at_subsetConst` | as above | `(a,p,c)` |

## A1-a

No `GridUniformCore`, no (F)-branch interface statement.
-/

@[expose] public section

open MeasureTheory Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open scoped Classical in
/-- **GWZ Lemma 7.4 at `M = 2`, on an arbitrary level-`c` subfamily.**

`Kakeya.ML2Core.exists_twoScale_nodesUnder` with `Q₂` freed from the shape
`Tube.UniformTubeSet.nodesUnder c a j`: the proof is the same one, and the level-`a` anchor is
dropped because it never entered it (the coarsest tube of the three-level datum is the ambient
radius-`4` tube, not `T_a`).  See the module docstring.

**Family/shading:** `𝒰` on `(s,T)`; no shading.  **Level pair:** `(p,c)`. -/
theorem exists_twoScale_subset :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
      ∀ {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
        (𝒰 : Tube.UniformTubeSet s T N Cu), s.Nonempty →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ {p c : ℕ}, p ≤ c → c ≤ N → 4 * gridScale δ N c ≤ gridScale δ N p →
      ∀ (Q2 : Finset ι), Q2 ⊆ 𝒰.cover.indexSet c →
        Kakeya.maxDensity Q2 (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
          ≤ ENNReal.ofReal C ^ 2
            * Kakeya.maxDensity
                (Q2.image (ML2Reduction.coarseNode 𝒰.cover.toChain p c))
                (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)
            * (Q2.image (ML2Reduction.coarseNode 𝒰.cover.toChain p c)).sup
                (fun jp => Kakeya.maxDensity
                  ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c))
                  (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) := by
  obtain ⟨C, hC, hmain⟩ :=
    Kakeya.MultiScaleSubmult.maxDensity_le_two_fibreDeltaMax (E := E) 5 (by norm_num) 1 one_pos
  refine ⟨C, hC, ?_⟩
  intro ι δ hδ0 hδ1 s T N Cu 𝒰 hs hball p c hpc hc hgap Q2 hQ2sub
  classical
  set proj : ι → ι := ML2Reduction.coarseNode 𝒰.cover.toChain p c with hproj
  set Q1 : Finset ι := Q2.image proj with hQ1
  set W2 : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube c j').toConvexSpaceBody with hW2
  set W1 : ι → ConvexSpaceBody E := fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody with hW1
  rcases Q2.eq_empty_or_nonempty with hQ2e | hQ2ne
  · rw [hQ2e, Kakeya.maxDensity_empty]
    exact zero_le
  set j : ι := hQ2ne.choose with hjdef
  have hp : p ≤ N := hpc.trans hc
  -- every level-`c` cell is active (has a class member), so its ancestor is a genuine node
  have hQ2idx : ∀ jc ∈ Q2, jc ∈ 𝒰.cover.indexSet c := fun _ hjc => hQ2sub hjc
  have hactive : ∀ jc ∈ Q2, jc ∈ ML2Reduction.activeNodes 𝒰.cover.toChain c := by
    intro jc hjc
    refine Finset.mem_filter.mpr ⟨hQ2idx jc hjc, ?_⟩
    exact Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hc hs (hQ2idx jc hjc)
  have hQ1idx : ∀ jp ∈ Q1, jp ∈ 𝒰.cover.indexSet p := by
    intro jp hjp
    obtain ⟨jc, hjc, rfl⟩ := Finset.mem_image.mp hjp
    exact ML2Reduction.coarseNode_mem 𝒰.cover.toChain hp (hactive jc hjc)
  have hcontain : ∀ jc ∈ Q2, W2 jc ≤ W1 (proj jc) := fun jc hjc =>
    ML2Reduction.tube_le_coarseNode 𝒰.cover.toChain hpc hc (hactive jc hjc)
  -- the ambient tube: radius `4`, centred at the origin
  obtain ⟨u, hu⟩ : ∃ u : E, ‖u‖ = 1 := exists_norm_eq E zero_le_one
  set amb : Tube 4 E := Tube.ofMidpointDirection 4 0 u hu with hamb
  have hambmid : _root_.midpoint ℝ amb.x amb.y = 0 := by
    rw [midpoint_eq_smul_add]
    change (⅟(2 : ℝ)) • ((0 - (1 / 2 : ℝ) • u) + (0 + (1 / 2 : ℝ) • u)) = 0
    simp
  have hamb_ball : amb.carrier ⊆ Metric.closedBall (0 : E) 5 := by
    intro z hz
    have := Tube.carrier_subset_closedBall_midpoint (E := E) amb hz
    rw [hambmid, Metric.mem_closedBall] at this
    rw [Metric.mem_closedBall]
    have h4 : ((4 : NNReal) : ℝ) = 4 := by norm_num
    rw [h4] at this
    linarith
  have hball_amb : Metric.closedBall (0 : E) 4 ⊆ amb.carrier := by
    intro z hz
    rw [amb.carrier_eq]
    refine Set.mem_biUnion (midpoint_mem_segment amb.x amb.y) ?_
    rw [hambmid]
    simpa using hz
  have hnode4 : ∀ k ≤ N, ∀ j' ∈ 𝒰.cover.indexSet k,
      (𝒰.cover.tube k j').carrier ⊆ Metric.closedBall (0 : E) 4 :=
    fun k hk j' hj' => node_carrier_subset_closedBall_four hδ0 hδ1 𝒰 hs hball hk hj'
  -- the three-level data of the lemma
  let ρ : Fin 3 → NNReal := fun k => match k with
    | ⟨0, _⟩ => 4
    | ⟨1, _⟩ => gridScale δ N p
    | ⟨_ + 2, _⟩ => gridScale δ N c
  let tb : ∀ k : Fin 3, ι → Tube (ρ k) E := fun k => match k with
    | ⟨0, _⟩ => fun _ => amb
    | ⟨1, _⟩ => fun jp => 𝒰.cover.tube p jp
    | ⟨_ + 2, _⟩ => fun jc => 𝒰.cover.tube c jc
  let Q : ∀ _k : Fin 3, Finset ι := fun k => match k with
    | ⟨0, _⟩ => {j}
    | ⟨1, _⟩ => Q1
    | ⟨_ + 2, _⟩ => Q2
  let pr : ∀ _m : Fin 2, ι → ι := fun m => match m with
    | ⟨0, _⟩ => fun _ => j
    | ⟨_ + 1, _⟩ => proj
  have hρ1 : (1 : NNReal) ≤ ρ 0 := by change (1 : NNReal) ≤ 4; norm_num
  have hρ4 : ρ 0 ≤ 4 := by change (4 : NNReal) ≤ 4; exact le_rfl
  have hρ2 : 0 < ρ 2 := by change 0 < gridScale δ N c; exact Tube.gridScale_pos hδ0 N c
  have hgap1 : 4 * ρ 1 ≤ ρ 0 := by
    change 4 * gridScale δ N p ≤ 4
    have := Tube.gridScale_le_one hδ1 N p
    calc 4 * gridScale δ N p ≤ 4 * 1 := by gcongr
      _ = 4 := by norm_num
  have hgap2 : 4 * ρ 2 ≤ ρ 1 := by change 4 * gridScale δ N c ≤ gridScale δ N p; exact hgap
  have key := hmain ρ hρ1 hρ4 hρ2 hgap1 hgap2 (κ := fun _ => ι) tb Q pr ?_ ?_ ?_ ?_ ?_
  · -- read the conclusion on the concrete data
    have key' : Kakeya.maxDensity Q2 W2
        ≤ ENNReal.ofReal C ^ 2
          * (Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({j} : Finset ι) (fun _ => j)
            * Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 proj) := by
      rw [Fin.prod_univ_two] at key
      exact key
    have hf1 : Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({j} : Finset ι) (fun _ => j)
        = Kakeya.maxDensity Q1 W1 := by
      unfold Kakeya.MultiScaleSubmult.fibreDeltaMax
      rw [Finset.sup_singleton]
      congr 1
      exact Finset.filter_true_of_mem (fun _ _ => rfl)
    have hf2 : Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 proj
        ≤ Q1.sup (fun jp => Kakeya.maxDensity
            ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c)) W2) := by
      unfold Kakeya.MultiScaleSubmult.fibreDeltaMax
      refine Finset.sup_mono_fun (fun jp _ => ?_)
      refine Kakeya.maxDensity_mono W2 ?_
      intro jc hjc
      obtain ⟨hjcQ2, hjceq⟩ := Finset.mem_filter.mp hjc
      -- the member the ancestor is read off is in the class of `jp` and is assigned to `jc`
      have hne : (Tube.coverClass s (𝒰.cover.toChain.assign c) jc).Nonempty :=
        (Finset.mem_filter.mp (hactive jc hjcQ2)).2
      have hmem := hne.choose_spec
      simp only [Tube.coverClass, Finset.mem_filter] at hmem
      have hproj_eq : proj jc = 𝒰.cover.assign p hne.choose := by
        change ML2Reduction.coarseNode 𝒰.cover.toChain p c jc = _
        rw [ML2Reduction.coarseNode, dif_pos hne]
        rfl
      refine Finset.mem_image.mpr ⟨hne.choose, ?_, hmem.2⟩
      simp only [Tube.coverClass, Finset.mem_filter]
      exact ⟨hmem.1, hproj_eq.symm.trans hjceq⟩
    calc Kakeya.maxDensity Q2 W2
        ≤ ENNReal.ofReal C ^ 2
          * (Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({j} : Finset ι) (fun _ => j)
            * Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 proj) := key'
      _ = ENNReal.ofReal C ^ 2 * Kakeya.maxDensity Q1 W1
            * Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 proj := by rw [hf1]; ring
      _ ≤ ENNReal.ofReal C ^ 2 * Kakeya.maxDensity Q1 W1
            * Q1.sup (fun jp => Kakeya.maxDensity
                ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c)) W2) :=
        mul_le_mul' le_rfl hf2
  · -- the projections land in the coarser level
    intro m
    fin_cases m
    · intro w _
      change j ∈ ({j} : Finset ι)
      exact Finset.mem_singleton_self j
    · intro w hw
      change proj w ∈ Q1
      exact Finset.mem_image_of_mem proj hw
  · -- the containments
    intro m
    fin_cases m
    · intro w hw
      change (𝒰.cover.tube p w).toConvexSpaceBody ≤ amb.toConvexSpaceBody
      refine SetLike.coe_subset_coe.mpr ?_
      exact (hnode4 p hp w (hQ1idx w hw)).trans hball_amb
    · intro w hw
      change (𝒰.cover.tube c w).toConvexSpaceBody ≤ (𝒰.cover.tube p (proj w)).toConvexSpaceBody
      exact hcontain w hw
  · -- the coarsest level has one node
    change (({j} : Finset ι).card : ℝ) ≤ 1 * (5 + 3) ^ (2 * Module.finrank ℝ E)
    rw [Finset.card_singleton, one_mul]
    exact_mod_cast one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 5 + 3)
  · -- everything lies in the ball of radius `5`
    intro k
    fin_cases k
    · intro t _
      change amb.carrier ⊆ Metric.closedBall (0 : E) 5
      exact hamb_ball
    · intro t ht
      change (𝒰.cover.tube p t).carrier ⊆ Metric.closedBall (0 : E) 5
      exact (hnode4 p hp t (hQ1idx t ht)).trans (Metric.closedBall_subset_closedBall (by norm_num))
    · intro t ht
      change (𝒰.cover.tube c t).carrier ⊆ Metric.closedBall (0 : E) 5
      exact (hnode4 c hc t (hQ2idx t ht)).trans (Metric.closedBall_subset_closedBall (by norm_num))
  · -- the two coarser levels are nonempty
    intro m
    fin_cases m
    · change ({j} : Finset ι).Nonempty
      exact Finset.singleton_nonempty j
    · change Q1.Nonempty
      exact hQ2ne.image proj

/-! ### The constant, named -/

universe v

/-- **The constant `C₀'(E)` of `exists_twoScale_subset`**, named for the same reason
`Kakeya.ML2Core.twoScaleConst` is: so that downstream hypotheses refer
to a definite constant rather than a fresh universally quantified one. -/
noncomputable def twoScaleSubsetConst (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] : ℝ :=
  Classical.choose (exists_twoScale_subset.{u, v} (E := E))

theorem twoScaleSubsetConst_pos (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] :
    0 < twoScaleSubsetConst.{u, v} E :=
  (Classical.choose_spec (exists_twoScale_subset.{u, v} (E := E))).1

open scoped Classical in
/-- `exists_twoScale_subset` at its own constant. -/
theorem twoScaleSubsetConst_spec {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type u} {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {p c : ℕ} (hpc : p ≤ c) (hc : c ≤ N) (hgap : 4 * gridScale δ N c ≤ gridScale δ N p)
    (Q2 : Finset ι) (hQ2 : Q2 ⊆ 𝒰.cover.indexSet c) :
    Kakeya.maxDensity Q2 (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ ENNReal.ofReal (twoScaleSubsetConst.{u, v} E) ^ 2
        * Kakeya.maxDensity
            (Q2.image (ML2Reduction.coarseNode 𝒰.cover.toChain p c))
            (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)
        * (Q2.image (ML2Reduction.coarseNode 𝒰.cover.toChain p c)).sup
            (fun jp => Kakeya.maxDensity
              ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c))
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) := by
  obtain ⟨-, h⟩ := Classical.choose_spec (exists_twoScale_subset.{u, v} (E := E))
  exact h hδ0 hδ1 𝒰 hs hball hpc hc hgap Q2 hQ2

open scoped Classical in
/-- **Compiled record: the `nodesUnder` form holds at the new constant too**, so nothing is forced
to choose between `twoScaleConst` and `twoScaleSubsetConst`.  This is `twoScaleConst_spec`'s
statement with the constant replaced, and it is a one-line instance of
`twoScaleSubsetConst_spec` at `Q₂ := 𝒰.nodesUnder c a j`. -/
theorem twoScale_nodesUnder_at_subsetConst {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] {ι : Type u} {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {a p c : ℕ} (hpc : p ≤ c) (hc : c ≤ N) (hgap : 4 * gridScale δ N c ≤ gridScale δ N p)
    (j : ι) :
    Kakeya.maxDensity (𝒰.nodesUnder c a j) (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ ENNReal.ofReal (twoScaleSubsetConst.{u, v} E) ^ 2
        * Kakeya.maxDensity
            ((𝒰.nodesUnder c a j).image (ML2Reduction.coarseNode 𝒰.cover.toChain p c))
            (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)
        * ((𝒰.nodesUnder c a j).image (ML2Reduction.coarseNode 𝒰.cover.toChain p c)).sup
            (fun jp => Kakeya.maxDensity
              ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c))
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :=
  twoScaleSubsetConst_spec hδ0 hδ1 𝒰 hs hball hpc hc hgap _
    (fun _ hjc => (Finset.mem_filter.mp hjc).1)

end Kakeya.ML2Core

end
