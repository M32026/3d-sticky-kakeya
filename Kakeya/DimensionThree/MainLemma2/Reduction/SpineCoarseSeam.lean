/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFactors

/-!
# The coarse seam, the level-`0` node count, and the estimate without residual hypotheses

`Kakeya.ML2Core.exists_coarse_factor_at_window` (the estimate, `Reduction/SpineFactors.lean`) carries two
hypotheses that existing output does not supply:

* the coarse family's containment in `B₁`, because `Kakeya.ML2Core.exists_parentSeam` is applied at
  the **fine** level `b` and a level-`a` node containing a normalised level-`b` node lies only in
  `B̄(0, 1 + 4θ)` (`Kakeya.ML2Core.coverTube_carrier_subset_closedBall`);
* the smallness `θ ≤ θ₀` of the coarse scale, which is false at `a = 0`, where
  `Tube.gridScale δ M 0 = 1` on the nose.

This file closes both, and it does so **without changing a single existing statement**.

## The coarse seam (`1 ≤ a`)

The seam is not re-derived: `Kakeya.ML2Core.exists_parentSeam` is applied at level `a` instead of
level `b`, and the fine data is recovered by *nestedness*, which runs the right way. Setting

`t₁ := {j ∈ activeNodes 𝒞 b | coarseNode 𝒞 a b j ∈ t₀}`,

a level-`b` node of `t₁` lies inside its level-`a` ancestor (`Tube.ChainCoverSystem.tube_assign_le`
through `Kakeya.ML2Reduction.tube_le_coarseNode`), so one pigeonhole at the coarse level delivers
**all three** ball conditions where the fine seam delivers two.  The cardinality retention is
carried across unchanged because the two retained leaf sets are *equal*:
`{i ∈ s | 𝒞.assign b i ∈ t₁} = {i ∈ s | 𝒞.assign a i ∈ t₀}`, by
`Kakeya.ML2Core.coarseNode_assign`.

`Kakeya.ML2Core.exists_spineTwoScale_ofChain_coarseSeam` then runs
`Kakeya.ML2Reduction.exists_spineTwoScale` — the *arbitrary-family* lemma, not the existing
`ofChain` wrapper — at `u := t₀` rather than at `u := 𝒞.indexSet a`.  That is the whole point: the
wrapper pins the coarse family to the entire index set, and a `tθ'` inside the entire index set
carries no ball information, whereas a `tθ'` inside `t₀` carries it by construction.  The coarse
ball condition is therefore a *conclusion* of the two-scale run, not a hypothesis of it.

## The level-`0` node count (`a = 0`)

At `a = 0` no smallness threshold on the tube scale can be met, and the only exit is the trivial
bound `Kakeya.ML2Core.multiplicity_le_of_card_le`, which needs a cardinality ceiling on the
retained coarse node set.  It is available, and from Definition 2.1(ii) alone:

* a tube of radius `≥ 1` containing `B̄(0,1)` exists
  (`Kakeya.ML2Core.exists_tube_superset_closedBall`), and `Tube.gridScale δ N 0 = 1`, so that the
  coarse endpoint of the grid has node radius exactly `1` and every **active** node meets it
  through the family and `Tube.UniformTubeSet.boundedOverlap` counts them all: at most `Cu`
  (`Kakeya.ML2Core.card_activeNodes_le_of_container`);
* and on a nonempty family **every** node is active
  (`Kakeya.ML2Core.indexSet_subset_activeNodes`): if some class were empty then Definition
  2.1(iii)'s lower half forces `branchingN k = 0`, and its upper half then forces *every* class to
  be empty, contradicting `Tube.GridCoverSystem.assign_mem` at any member.

So `|𝕋_0| ≤ Cu` (`Kakeya.ML2Core.card_indexSet_zero_le`) — with no smallness, no shading and no
translation.  The count is **not** obtained from
`Kakeya.VeryNotSticky.card_indexSet_mul_branchingN_le`, which gives
`|indexSet k| · branchingN k ≤ C |s|` and is vacuous exactly when `branchingN k = 0`; the second
bullet above is what rules that degeneracy out, and it is the same fact.

## What is delivered

`Kakeya.ML2Core.exists_coarse_factor_complete` bounds the coarse factor at **every** `a`, with the
`a = 0` branch taking the ceiling route and the `1 ≤ a` branch taking `K_KT(β)`; its coarse-scale
threshold is discharged internally by `Kakeya.ML2Core.eventually_gridScale_le`.  Its hypotheses are
actual outputs, the window, `s.Nonempty`, the leaves in `B₁`, and two exponent
absorptions.  `Kakeya.ML2Core.exists_coarseSeam_with_coarse_factor` is the compatibility that
the coarse seam, the coarse two-scale run and the coarse factor compose with no adapter.
-/

@[expose] public section

open MeasureTheory ShadedBody ConvexSpaceBody Tube Filter
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The coarse seam -/

section CoarseSeam

variable {ι : Type u}

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The level-`a` ancestor of a leaf's level-`b` node is the leaf's own level-`a` node.**

`Kakeya.ML2Reduction.coarseNode` reads the ancestor off an arbitrary member of the node's class,
which is legitimate because `Tube.ChainCoverSystem.assign_eq_of_le` makes the reading independent
of the member; this is that independence, at the member one actually has. -/
theorem coarseNode_assign {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
    (𝒞 : Tube.ChainCoverSystem s T N σ) {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {i : ι} (hi : i ∈ s) :
    ML2Reduction.coarseNode 𝒞 a b (𝒞.assign b i) = 𝒞.assign a i := by
  classical
  have h : (Tube.coverClass s (𝒞.assign b) (𝒞.assign b i)).Nonempty :=
    ⟨i, by simp [Tube.coverClass, hi]⟩
  rw [ML2Reduction.coarseNode, dif_pos h]
  have hmem := h.choose_spec
  simp only [Tube.coverClass, Finset.mem_filter] at hmem
  exact 𝒞.assign_eq_of_le hab hbN hmem.1 hi hmem.2

omit [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- **The parent-ball seam, run at the coarse level.**

`Kakeya.ML2Core.exists_parentSeam` applied at level `a`, with the fine data recovered by
nestedness.  The retained fine set is `t₁ = {j ∈ activeNodes 𝒞 b | coarseNode 𝒞 a b j ∈ t₀}`, and
the output is strictly stronger than the fine seam's: **three** ball conditions — coarse nodes,
fine nodes, leaves — plus the clause `coarseNode 𝒞 a b '' t₁ ⊆ t₀` that lets the two-scale run be
performed against `t₀` rather than against the whole level-`a` index set.

The cardinality retention is the fine seam's, unchanged, because the two retained leaf sets are
literally equal (`Kakeya.ML2Core.coarseNode_assign`); no second pigeonhole is paid for.

The side condition is `σ a ≤ 1/4` at the **coarse** scale, where the fine seam asks it at the fine
one.  Since `σ` is antitone, that is the stronger of the two requirements, and it is what makes
`a = 0` — where `Tube.gridScale δ M 0 = 1` — inaccessible to this route. -/
theorem exists_coarseParentSeam :
    ∃ M : ℕ, 0 < M ∧
      ∀ {δ : NNReal} {κ : Type u} {s : Finset κ} {T : κ → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
        (𝒞 : Tube.ChainCoverSystem s T N σ) {a b : ℕ} {Cu Bn : NNReal},
        a ≤ b → b ≤ N → (σ a : ℝ) ≤ 1 / 4 →
        (∀ j ∈ 𝒞.indexSet a, ((Tube.coverClass s (𝒞.assign a) j).card : NNReal) ≤ Cu * Bn) →
        (∀ j ∈ 𝒞.indexSet a, Bn ≤ Cu * ((Tube.coverClass s (𝒞.assign a) j).card : NNReal)) →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∃ (v : E) (t₀ t₁ : Finset κ),
          t₀ ⊆ ML2Reduction.activeNodes 𝒞 a ∧
          t₁ ⊆ ML2Reduction.activeNodes 𝒞 b ∧
          (∀ k ∈ t₀, ((𝒞.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ j ∈ t₁, ((𝒞.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ),
            ((T i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 a b j ∈ t₀) ∧
          (s.card : NNReal) ≤ (M : NNReal) * Cu * Cu
            * (({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ).card : NNReal) := by
  classical
  obtain ⟨M, hM0, hseam⟩ := exists_parentSeam (E := E)
  refine ⟨M, hM0, ?_⟩
  intro δ κ s T N σ 𝒞 a b Cu Bn hab hbN hσ4 hup hlo hball
  have haN : a ≤ N := hab.trans hbN
  obtain ⟨v, t₀, ht₀, hballt₀, hballs₀, hcard₀⟩ := hseam 𝒞 haN hσ4 hup hlo hball
  set t₁ : Finset κ :=
    {j ∈ ML2Reduction.activeNodes 𝒞 b | ML2Reduction.coarseNode 𝒞 a b j ∈ t₀} with ht₁def
  have ht₁sub : t₁ ⊆ ML2Reduction.activeNodes 𝒞 b := Finset.filter_subset _ _
  have hcoarse : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 a b j ∈ t₀ :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hsets : ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ)
      = ({i ∈ s | 𝒞.assign a i ∈ t₀} : Finset κ) := by
    ext i
    simp only [Finset.mem_filter, ht₁def]
    constructor
    · rintro ⟨his, _hact, hcn⟩
      rw [coarseNode_assign 𝒞 hab hbN his] at hcn
      exact ⟨his, hcn⟩
    · rintro ⟨his, hcn⟩
      refine ⟨his, ML2Reduction.assign_mem_activeNodes 𝒞 hbN his, ?_⟩
      rw [coarseNode_assign 𝒞 hab hbN his]
      exact hcn
  refine ⟨v, t₀, t₁, ht₀, ht₁sub, hballt₀, ?_, ?_, hcoarse, ?_⟩
  · intro j hj
    refine subset_trans ?_ (hballt₀ _ (hcoarse j hj))
    have hle : (𝒞.tube b j).carrier ⊆ (𝒞.tube a (ML2Reduction.coarseNode 𝒞 a b j)).carrier :=
      ML2Reduction.tube_le_coarseNode 𝒞 hab hbN (ht₁sub hj)
    exact Set.image_mono hle
  · rw [hsets]; exact hballs₀
  · rw [hsets]; exact hcard₀

end CoarseSeam

/-! ## the estimate against the coarse seam -/

section TwoScaleCoarse

variable [Nontrivial E]
variable {ι : Type u} {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
  {σ : ℕ → NNReal}

open Classical in
/-- **the estimate run against the coarse seam.**

`Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated` with the coarse family pinned to the
seam's retained set `t₀` instead of to the whole of `𝒞.indexSet a`.  Every clause of the existing
wrapper's conclusion is reproduced, and **one is added**: `tθ' ⊆ t₀`, hence
`∀ k ∈ tθ', (Yθ k).carrier ⊆ B₁`.

It is not a corollary of the existing wrapper and cannot be: that wrapper discharges
`Kakeya.ML2Reduction.exists_spineTwoScale`'s `hmapsθ` by
`Kakeya.ML2Reduction.coarseNode_mem`, which lands in the entire index set, and an existential
`tθ' ⊆ 𝒞.indexSet a` cannot afterwards be refined to `tθ' ⊆ t₀`.  So the arbitrary-family lemma is
applied directly, at `u := t₀`, with `hmapsθ` supplied by the seam's own clause.  Nothing in
`Reduction/SpineCoreWindow.lean` is edited or restated. -/
theorem exists_spineTwoScale_ofChain_coarseSeam
    (hδ0 : 0 < δ) (𝒞 : Tube.ChainCoverSystem s (fun i => (V i).toTube) N σ)
    {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    (hδτ : δ ≤ σ b) (hτθ : σ b ≤ σ a) (hθ1 : σ a ≤ 1)
    (v : E) {t₀ t₁ : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒞 b)
    (hcoarse : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 a b j ∈ t₀)
    (hballt₀ : ∀ k ∈ t₀, ((𝒞.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballt : ∀ j ∈ t₁, ((𝒞.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballs : ∀ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι),
      ((V i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ tτ' ⊆ t₁, ∃ tθ' ⊆ t₀,
      ∃ (Yτ Yτ' : ι → ShadedTube (σ b) E) (Yθ : ι → ShadedTube (σ a) E)
        (Y' : ι → ShadedTube δ E),
        tτ'.card ≤ t₁.card ∧
        (∀ j, (Yτ j).toTube = (𝒞.tube b j).translate v) ∧
        (∀ j, (Yτ' j).toTube = (𝒞.tube b j).translate v) ∧
        (∀ k, (Yθ k).toTube = (𝒞.tube a k).translate v) ∧
        (∀ i, (Y' i).toTube = ((V i).translate v).toTube) ∧
        (∀ i, (Y' i).shade ⊆ ((V i).translate v).shade) ∧
        (∀ j, (Yτ' j).shade ⊆ (Yτ j).shade) ∧
        (∀ k ∈ tθ', (Yθ k).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
        (0 < ∑ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι), volume (V i).shade →
          tτ'.Nonempty ∧ tθ'.Nonempty) ∧
        ShadedBody.IsCRefinement
            {i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι) | 𝒞.assign b i ∈ tτ'}
            (fun i => (Y' i).toShadedBody)
            ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
            (fun i => ((V i).translate v).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
              ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ ∧
        ShadedBody.IsCRefinement {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j ∈ tθ'}
            (fun j => (Yτ' j).toShadedBody) tτ' (fun j => (Yτ j).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b))⁻¹ ∧
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
              ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ *
            ShadedBody.fullness ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
              (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody) ∧
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
                ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b))⁻¹ *
            ShadedBody.fullness ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
              (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tθ' (fun k => (Yθ k).toShadedBody) ∧
        (∀ jτ ∈ tτ', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
              (fun i => (V i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
                    ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b)
                    : NNReal) : ENNReal)
              * ShadedBody.multiplicity
                  {i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι) | 𝒞.assign b i = jτ}
                  (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ}
                  (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k => (Yθ k).toShadedBody)) := by
  classical
  set s₁ : Finset ι := {i ∈ s | 𝒞.assign b i ∈ t₁} with hs₁
  have hs₁s : s₁ ⊆ s := Finset.filter_subset _ _
  have hmapsτ : ∀ i ∈ s₁, 𝒞.assign b i ∈ t₁ := fun i hi => (Finset.mem_filter.mp hi).2
  have hleτ : ∀ i ∈ s₁, ((V i).translate v).toConvexSpaceBody
      ≤ ((𝒞.tube b (𝒞.assign b i)).translate v).toConvexSpaceBody := by
    intro i hi
    exact translate_le_translate v (𝒞.le_tube_assign b hbN i (hs₁s hi))
  have hleθ : ∀ j ∈ t₁, ((𝒞.tube b j).translate v).toConvexSpaceBody
      ≤ ((𝒞.tube a (ML2Reduction.coarseNode 𝒞 a b j)).translate v).toConvexSpaceBody := by
    intro j hj
    exact translate_le_translate v (ML2Reduction.tube_le_coarseNode 𝒞 hab hbN (ht₁ hj))
  have hfullEq : ShadedBody.fullness s₁ (fun i => ((V i).translate v).toShadedBody)
      = ShadedBody.fullness s₁ (fun i => (V i).toShadedBody) :=
    ShadedBody.fullness_translate_const s₁ (fun i => (V i).toShadedBody) v
  have hmulEq : ShadedBody.multiplicity s₁ (fun i => ((V i).translate v).toShadedBody)
      = ShadedBody.multiplicity s₁ (fun i => (V i).toShadedBody) :=
    ShadedBody.multiplicity_translate_const s₁ (fun i => (V i).toShadedBody) v
  have hmassEq : ∀ i, volume ((V i).translate v).shade = volume (V i).shade := by
    intro i
    exact MeasureTheory.measure_image_add _ v (V i).shade
  obtain ⟨tτ', htτ', tθ', htθ', Yτ, Yτ', Yθ, Y', hcard, hYτ, hYτ', hYθ, hY'tube, hY'shade,
      hYτ'shade, hne, href1, href2, hfull1, hfull2, hprod⟩ :=
    ML2Reduction.exists_spineTwoScale (E := E) hδ0 hδτ hτθ hθ1
      (s := s₁) (t := t₁) (u := t₀)
      (fun i => (V i).translate v) (fun j => (𝒞.tube b j).translate v)
      (fun k => (𝒞.tube a k).translate v) (𝒞.assign b) (ML2Reduction.coarseNode 𝒞 a b)
      hballs hballt hmapsτ hleτ hcoarse hleθ
  refine ⟨tτ', htτ', tθ', htθ', Yτ, Yτ', Yθ, Y', hcard, hYτ, hYτ', hYθ, hY'tube, hY'shade,
    hYτ'shade, ?_, ?_, href1, href2, ?_, ?_, ?_⟩
  · intro k hk
    have hc : (Yθ k).carrier = ((𝒞.tube a k).translate v).carrier :=
      congrArg (fun T : Tube (σ a) E => T.carrier) (hYθ k)
    rw [hc]
    exact hballt₀ k (htθ' hk)
  · intro hpos
    exact hne (by simpa [hmassEq] using hpos)
  · rw [← hfullEq]; exact hfull1
  · rw [← hfullEq]; exact hfull2
  · intro jτ hjτ jθ hjθ
    rw [← hmulEq]
    exact hprod jτ hjτ jθ hjθ

end TwoScaleCoarse

/-! ## The level-`0` node count -/

section LevelZero

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A tube of radius `≥ 1` containing the unit ball.**

A `Kakeya.Tube` of radius `ρ` is the closed `ρ`-neighbourhood of a *unit* segment, so the tube
around a unit segment centred at the origin contains `B̄(0, ρ) ⊇ B̄(0, 1)` for `ρ ≥ 1`.  This is
what makes Definition 2.1(ii) count *every* active node at the coarse endpoint of the grid, where
the node radius is exactly `1`. -/
theorem exists_tube_superset_closedBall [Nontrivial E] {ρ : NNReal} (hρ : 1 ≤ ρ) :
    ∃ W : Tube ρ E, Metric.closedBall (0 : E) 1 ⊆ W.carrier := by
  obtain ⟨e, he⟩ : ∃ e : E, ‖e‖ = 1 := exists_norm_eq E zero_le_one
  have hd : dist (-((2 : ℝ)⁻¹ • e)) ((2 : ℝ)⁻¹ • e) = 1 := by
    rw [dist_eq_norm]
    have hsub : -((2 : ℝ)⁻¹ • e) - (2 : ℝ)⁻¹ • e = -e := by module
    rw [hsub, norm_neg, he]
  refine ⟨Tube.mk' ρ hd, ?_⟩
  have hzero : (0 : E) ∈ segment ℝ (-((2 : ℝ)⁻¹ • e)) ((2 : ℝ)⁻¹ • e) := by
    refine ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  intro z hz
  have hzb : z ∈ Metric.closedBall (0 : E) (ρ : ℝ) := by
    refine Metric.closedBall_subset_closedBall ?_ hz
    exact_mod_cast hρ
  exact Set.mem_biUnion hzero hzb

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Definition 2.1(ii) counts every active node inside a common container.**

If one tube of the level-`k` radius contains the whole family, then every active level-`k` node
shares a member with it, so `Tube.UniformTubeSet.boundedOverlap` bounds their number by `Cu`. -/
theorem card_activeNodes_le_of_container (𝒰 : Tube.UniformTubeSet s T N Cu) {k : ℕ} (hk : k ≤ N)
    (W : Tube (Tube.gridScale δ N k) E)
    (hW : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) :
    ((ML2Reduction.activeNodes 𝒰.cover.toChain k).card : NNReal) ≤ Cu := by
  classical
  refine le_trans ?_ (𝒰.boundedOverlap k hk W)
  have hsub : ML2Reduction.activeNodes 𝒰.cover.toChain k ⊆
      (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) := by
    intro j hj
    obtain ⟨hjidx, hne⟩ := Finset.mem_filter.mp hj
    obtain ⟨i, hi⟩ := hne
    simp only [Tube.coverClass, Finset.mem_filter] at hi
    refine Finset.mem_filter.mpr ⟨hjidx, ⟨i, hi.1, ?_, hW i hi.1⟩⟩
    have hthis := 𝒰.cover.le_tube_assign k hk i hi.1
    have heq : 𝒰.cover.assign k i = j := hi.2
    rwa [heq] at hthis
  exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **On a nonempty family, every node of the hierarchy is active.**

Definition 2.1(iii)'s two brackets are what rules out the degeneracy: an empty class at level `k`
forces `branchingN k = 0` through the lower bracket, and the upper bracket then forces *every*
level-`k` class to be empty — impossible, since `Tube.GridCoverSystem.assign_mem` puts any member
of `s` in one of them.

This is the fact that makes `Kakeya.VeryNotSticky.card_indexSet_mul_branchingN_le` non-vacuous, and
it is what turns the bound on the *active* nodes into a bound on `Tube.GridCoverSystem.indexSet`
itself. -/
theorem indexSet_subset_activeNodes (𝒰 : Tube.UniformTubeSet s T N Cu) {k : ℕ} (hk : k ≤ N)
    (hs : s.Nonempty) :
    𝒰.cover.indexSet k ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain k := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  have hj₀ : 𝒰.cover.assign k i₀ ∈ 𝒰.cover.indexSet k := 𝒰.cover.assign_mem k hk i₀ hi₀
  have hne₀ : (Tube.coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).Nonempty :=
    ⟨i₀, by simp [Tube.coverClass, hi₀]⟩
  have hcard₀ : (1 : NNReal)
      ≤ ((Tube.coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card : NNReal) := by
    have h1 : 1 ≤ (Tube.coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card :=
      Finset.card_pos.mpr hne₀
    exact_mod_cast h1
  intro j hj
  refine Finset.mem_filter.mpr ⟨hj, ?_⟩
  by_contra hemp
  have hzero : (Tube.coverClass s (𝒰.cover.assign k) j).card = 0 :=
    Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hemp)
  have hB : 𝒰.branchingN k = 0 := by
    have hlow := 𝒰.le_card_class k hk j hj
    rw [hzero] at hlow
    simpa using hlow
  have hcontra := 𝒰.card_class_le k hk _ hj₀
  rw [hB, mul_zero] at hcontra
  exact absurd (hcard₀.trans hcontra) (by norm_num)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The level-`0` node count is at most the uniformity constant.**

`Tube.gridScale δ N 0 = 1`, so the coarse endpoint of the grid has node radius exactly `1`, and the
two previous lemmas apply: every node is active, and every active node is counted by Definition
2.1(ii) against one unit tube containing `B̄(0,1)`.

No smallness of `δ`, no shading, no translation and no uniformity beyond Definition 2.1 enter. -/
theorem card_indexSet_zero_le [Nontrivial E] (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ((𝒰.cover.indexSet 0).card : NNReal) ≤ Cu := by
  classical
  have hg : (1 : NNReal) ≤ Tube.gridScale δ N 0 := by rw [Tube.gridScale_zero]
  obtain ⟨W, hW⟩ := exists_tube_superset_closedBall (E := E) hg
  have hcont : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody :=
    fun i hi => (hball i hi).trans hW
  refine le_trans ?_ (card_activeNodes_le_of_container 𝒰 (Nat.zero_le N) W hcont)
  exact_mod_cast Nat.cast_le.mpr
    (Finset.card_le_card (indexSet_subset_activeNodes 𝒰 (Nat.zero_le N) hs))

end LevelZero

/-! ## the estimate at every `a` -/

section CoarseFactorComplete

variable [Nontrivial E]

open Classical in
/-- **the estimate, complete: the coarse factor at every window index `a`.**

Two branches, one conclusion.

* `1 ≤ a`: `K_KT(β)` through `Kakeya.ML2Core.exists_coarse_factor_at_window`, whose two former
  residues are now supplied — the ball condition by
  `Kakeya.ML2Core.exists_spineTwoScale_ofChain_coarseSeam` (the hypothesis `hball` below is
  literally that theorem's eighth conclusion clause) and the coarse-scale threshold by
  `Kakeya.ML2Core.eventually_gridScale_le`, discharged **inside** this statement rather than
  passed on.
* `a = 0`: the trivial bound `Kakeya.ML2Core.multiplicity_le_of_card_le` against the ceiling
  `Kakeya.ML2Core.card_indexSet_zero_le`.  This branch uses neither the ball condition nor the
  fullness floor nor the window's density field — only `s.Nonempty` and the leaves in `B₁`.

The two exponent hypotheses are the reduction's standard subpolynomial absorptions, one per
branch: `hc` for the `K_KT` branch and `hCu` for the ceiling branch. -/
theorem exists_coarse_factor_complete {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {Cst : NNReal} {ι : Type u} {s : Finset ι} {T : ι → Tube δ E}
        {𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cst} {Cstar : ENNReal} {ηl : ℕ → ℝ}
        {εd : ℝ} {N a b m : ℕ} {κ c : ℝ} {t : Finset ι}
        {Yθ : ι → ShadedTube (Tube.gridScale δ (ssfGridLen δ) a) E} {v : E},
        0 < δ → δ ≤ 1 → s.Nonempty →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd N a b m →
        0 ≤ ηl m → 0 ≤ κ →
        Cstar ≤ (δ : ENNReal) ^ (-κ) →
        ε + (κ + ηl m) ≤ c →
        (Cst : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-c) →
        t ⊆ 𝒰.cover.indexSet a →
        (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
        (a ≠ 0 → ∀ k ∈ t, (Yθ k).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (δ : NNReal) ^ η ≤ ShadedBody.fullness t (fun k => (Yθ k).toShadedBody) →
        ShadedBody.multiplicity t (fun k => (Yθ k).toShadedBody)
          ≤ (δ : ENNReal) ^ (-c) * (t.card : ENNReal) ^ β := by
  classical
  obtain ⟨η, hη, θ₀, hθ₀0, hθ₀1, hwin⟩ :=
    exists_coarse_factor_at_window.{u} (E := E) hβ0 hβ1 hKT hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [eventually_gridScale_le hθ₀0] with δ hgrid
  intro Cst ι s T 𝒰 Cstar ηl εd N a b m κ c t Yθ v hδ0 hδ1 hs hballs hw hηm hκ hCstar hc hCu
    htu hY hball hfull
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  rcases Nat.eq_zero_or_pos a with ha0 | ha1
  · -- the degenerate coarse endpoint: the node count alone
    subst ha0
    have hcard : (t.card : NNReal) ≤ Cst := by
      refine le_trans ?_ (card_indexSet_zero_le (E := E) 𝒰 hs hballs)
      exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card htu)
    have hcardE : (t.card : ENNReal) ≤ (Cst : ENNReal) := by exact_mod_cast hcard
    refine (multiplicity_le_of_card_le (E := E) hβ1 hcardE).trans ?_
    exact mul_le_mul' hCu le_rfl
  · -- the honest branch
    have hane : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha1
    have haM : a ≤ ssfGridLen δ := le_trans hw.coarse_lt_fine.le hw.fine_le_gridLen
    have hθle : Tube.gridScale δ (ssfGridLen δ) a ≤ θ₀ := hgrid a ha1 haM
    refine (hwin hδ0 hδ1 hθle hw hηm hκ hCstar htu hY (hball hane) hfull).trans ?_
    refine mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 ?_) le_rfl
    linarith


omit [Nontrivial E] in
open Classical in
/-- **The coarse-seam entry point of branch (ii)**, the coarse-level companion of
`Kakeya.ML2Core.exists_windowSeam`.

Same shape, one level up: the side condition `σ a ≤ 1/4` is discharged by
`Kakeya.ML2Core.gridScale_le_quarter` from `1 ≤ a` and the eventually-true
`2 ⌈log log 1/δ⌉ ≤ log(1/δ)`, and the two class brackets are Definition 2.1(iii) read at level `a`.
The output is the coarse seam's, plus the three window scales. -/
theorem exists_coarseWindowSeam :
    ∃ M : ℕ, 0 < M ∧
      ∀ {δ Cu : NNReal} {κ : Type u} {s : Finset κ} {V : κ → ShadedTube δ E}
        (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) (ssfGridLen δ) Cu)
        {Cstar : ENNReal} {ηl : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ},
        0 < δ → δ ≤ 1 → 1 ≤ a → 2 * (ssfGridLen δ : ℝ) ≤ Real.log (1 / (δ : ℝ)) →
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd N a b m →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∃ (v : E) (t₀ t₁ : Finset κ),
          t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a ∧
          t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b ∧
          (∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset κ),
            ((V i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) ∧
          (s.card : NNReal) ≤ (M : NNReal) * Cu * Cu
            * (({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset κ).card : NNReal) ∧
          δ ≤ Tube.gridScale δ (ssfGridLen δ) b ∧
          Tube.gridScale δ (ssfGridLen δ) b ≤ Tube.gridScale δ (ssfGridLen δ) a ∧
          Tube.gridScale δ (ssfGridLen δ) a ≤ 1 := by
  classical
  obtain ⟨M, hM0, hseam⟩ := exists_coarseParentSeam (E := E)
  refine ⟨M, hM0, ?_⟩
  intro δ Cu κ s V 𝒰 Cstar ηl εd N a b m hδ0 hδ1 ha1 hlog hw hball
  obtain ⟨hδτ, hτθ, hθ1⟩ := window_scales hδ0 hδ1 hw
  have haM : a ≤ ssfGridLen δ := le_trans hw.coarse_lt_fine.le hw.fine_le_gridLen
  have hσ4 : ((Tube.gridScale δ (ssfGridLen δ) a : NNReal) : ℝ) ≤ 1 / 4 :=
    gridScale_le_quarter hδ0 hδ1 ha1 haM hlog
  obtain ⟨v, t₀, t₁, ht₀, ht₁, hb₀, hb₁, hbs, hcn, hcard⟩ :=
    hseam 𝒰.cover.toChain hw.coarse_lt_fine.le hw.fine_le_gridLen hσ4
      (𝒰.card_class_le a haM) (𝒰.le_card_class a haM) hball
  exact ⟨v, t₀, t₁, ht₀, ht₁, hb₀, hb₁, hbs, hcn, hcard, hδτ, hτθ, hθ1⟩

open Classical in
/-- **compatibility: the coarse seam, the coarse two-scale run and the estimate compose, with no residue.**

From a dividing window at `1 ≤ a` on a uniform hierarchy whose leaves lie in `B₁`, this produces
the retained coarse family together with **the coarse factor's bound**, conditional only on the
fullness floor.  Its point is that the two hypotheses that
`Kakeya.ML2Core.exists_coarse_factor_at_window` used to carry as residues — the coarse family in
`B₁`, and `θ ≤ θ₀` — are discharged here from the seam and from
`Kakeya.ML2Core.eventually_gridScale_le`, so neither appears.

The remaining antecedent `δ^η ≤ λ(tθ', Yθ)` is **not** a residue: it is own
`hfull2` clause composed with GC-P1's global fullness floor `λ(𝕋, Y) ≥ δ^{η₀}`, and it is stated
here rather than derived because the loss constants of `hfull2` mention the existentially bound
`tτ'.card`. -/
theorem exists_coarseSeam_with_coarse_factor {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {Cst : NNReal} {ι : Type u} {s : Finset ι} {V : ι → ShadedTube δ E}
        (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) (ssfGridLen δ) Cst)
        {Cstar : ENNReal} {ηl : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ} {κ c : ℝ},
        0 < δ → δ ≤ 1 → 1 ≤ a → s.Nonempty →
        2 * (ssfGridLen δ : ℝ) ≤ Real.log (1 / (δ : ℝ)) →
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd N a b m →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        0 ≤ ηl m → 0 ≤ κ → Cstar ≤ (δ : ENNReal) ^ (-κ) → ε + (κ + ηl m) ≤ c →
        (Cst : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-c) →
        ∃ (v : E) (t₀ t₁ tτ' tθ' : Finset ι)
          (Yθ : ι → ShadedTube (Tube.gridScale δ (ssfGridLen δ) a) E),
          tτ' ⊆ t₁ ∧ tθ' ⊆ t₀ ∧ t₀ ⊆ 𝒰.cover.indexSet a ∧
          (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) ∧
          (∀ k ∈ tθ', (Yθ k).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          ((δ : NNReal) ^ η ≤ ShadedBody.fullness tθ' (fun k => (Yθ k).toShadedBody) →
            ShadedBody.multiplicity tθ' (fun k => (Yθ k).toShadedBody)
              ≤ (δ : ENNReal) ^ (-c) * (tθ'.card : ENNReal) ^ β) := by
  classical
  obtain ⟨η, hη, hcf⟩ := exists_coarse_factor_complete.{u} (E := E) hβ0 hβ1 hKT hε
  obtain ⟨M, _hM0, hseam⟩ := exists_coarseWindowSeam.{u} (E := E)
  refine ⟨η, hη, ?_⟩
  filter_upwards [hcf] with δ hcfδ
  intro Cst ι s V 𝒰 Cstar ηl εd N a b m κ c hδ0 hδ1 ha1 hs hlog hw hball hηm hκ hCstar hc hCu
  obtain ⟨v, t₀, t₁, ht₀, ht₁, hb₀, hb₁, hbs, hcn, _hcard, hδτ, hτθ, hθ1⟩ :=
    hseam 𝒰 hδ0 hδ1 ha1 hlog hw hball
  obtain ⟨tτ', htτ', tθ', htθ', _Yτ, _Yτ', Yθ, _Y', _h1, _h2, _h3, hYθ, _h5, _h6, _h7,
      hballθ, _hne, _hr1, _hr2, _hf1, _hf2, _hprod⟩ :=
    exists_spineTwoScale_ofChain_coarseSeam (E := E) hδ0 𝒰.cover.toChain
      hw.coarse_lt_fine.le hw.fine_le_gridLen hδτ hτθ hθ1 v ht₁ hcn hb₀ hb₁ hbs
  have ht₀idx : t₀ ⊆ 𝒰.cover.indexSet a :=
    ht₀.trans (ML2Reduction.activeNodes_subset 𝒰.cover.toChain a)
  refine ⟨v, t₀, t₁, tτ', tθ', Yθ, htτ', htθ', ht₀idx, hYθ, hballθ, ?_⟩
  intro hfull
  exact hcfδ hδ0 hδ1 hs hball hw hηm hκ hCstar hc hCu (htθ'.trans ht₀idx) hYθ
    (fun _ => hballθ) hfull

end CoarseFactorComplete

end Kakeya.ML2Core
