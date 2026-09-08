/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Clump

/-!
# Restricting a grid-uniform system along a class-size band

A pass through the levels of a multiscale hierarchy deletes members of the leaf family and then has
to hand back an object of the same kind.  For `Tube.UniformTubeSet` that hand-back is
the *supplied-bracket* restriction: no hypothesis relates the retained family to the classes of any
level, the branching bracket is handed in rather than deduced, and every other clause is inherited
by an arbitrary subfamily.  This file gives `Kakeya.MultiScaleFac.GridUniform` the same hand-back.

The one clause that is genuinely not inherited is `Tube.IsUniformAtScale.card_filter_le`: it counts
the members of the retained family *contained in* a node, and such a member need not belong to that
node's class, so a bound in terms of the new branching number cannot come from the old one.  It is
recovered from bounded overlap, which caps the number of nodes that can donate members to a fixed
node — the argument already carried by `Tube.ChainUniformTubeSet.card_filter_le`, and
the source of the single squaring in `Kakeya.MultiScaleFac.gridUniformBandConst`.

All of the constant inflation is dimensional and band-ratio dependent; none of it involves `δ` or
the grid length, and no cardinality is lost — the subfamily is prescribed, not produced.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*}

/-! ### The per-scale reading of a grid bundle, as data -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The three data fields of the per-scale reading** (blueprint `lem:uniformAtToChainFields`).

`Tube.ChainUniformTubeSet.uniformAt` is defined by a term-mode `exact` behind a
`have`, so its projections are definitional but not syntactically apparent at a call site.  Naming
them once keeps the assembly below free of unfolding incantations. -/
theorem uniformAt_toChain_fields {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (hC : 1 ≤ C) {k : ℕ} (hk : k ≤ N) :
    (𝒰.toChain.uniformAt hC hk).parent = 𝒰.cover.indexSet k ∧
      (𝒰.toChain.uniformAt hC hk).parentTube = 𝒰.cover.tube k ∧
      (𝒰.toChain.uniformAt hC hk).branchingN = 𝒰.branchingN k :=
  ⟨rfl, rfl, rfl⟩

/-! ### Restricting the bundle along a class-size band -/

open scoped Classical in
omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Restricting a `UniformTubeSet` along a class-size band of ratio `A`** (blueprint
`lem:uniformTubeSetRestrictBand`).  The subfamily `s'` is *arbitrary*: the branching bracket is
supplied by `hband` rather than deduced, and the statement only checks that every other clause of
`GridCoverSystem` and `UniformTubeSet` is inherited by an arbitrary subfamily.

**Name note (do not rename back).** This was called
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band`, which *collided* with the declaration
of that name in `Kakeya/RelativePlank.lean` (ported from the Section-8 development). Here the two are the same statement *and*
the same proof term, character for character, so nothing was ever proved from the wrong lemma -- but
an edit to one copy would have been silently invisible. The `RelativePlank.lean` copy keeps the
old name because that file is upstream-owned and a re-port would undo a rename made there. -/
theorem exists_restrict_uniformTubeSet_of_supplied_band {δ : NNReal} {s s' : Finset ι}
    {T : ι → Tube δ E}
    {M : ℕ} {Cu A C : NNReal} (𝒰 : UniformTubeSet s T M Cu) (hs' : s' ⊆ s)
    (hCuC : Cu ≤ C) (hAC : A ≤ C) (hC1 : 1 ≤ C) (b : ℕ → NNReal)
    (hband : ∀ k ≤ M, ∀ j ∈ s'.image (𝒰.cover.assign k),
      b k ≤ ((coverClass s' (𝒰.cover.assign k) j).card : NNReal) ∧
        ((coverClass s' (𝒰.cover.assign k) j).card : NNReal) ≤ A * b k) :
    ∃ 𝒰' : UniformTubeSet s' T M C,
      (∀ k, 𝒰'.cover.indexSet k = s'.image (𝒰.cover.assign k)) ∧
        (∀ k, 𝒰'.cover.assign k = 𝒰.cover.assign k) ∧
          (∀ k, 𝒰'.cover.tube k = 𝒰.cover.tube k) ∧
            (∀ k, 𝒰'.branchingN k = b k) := by
  refine ⟨⟨⟨fun k => s'.image (𝒰.cover.assign k), 𝒰.cover.assign, 𝒰.cover.tube,
      (fun k hk i hi => Finset.mem_image_of_mem (𝒰.cover.assign k) hi),
      (fun k hk i hi => 𝒰.cover.le_tube_assign k hk i (hs' hi)),
      (fun k hk i hi j hj h => 𝒰.cover.nested k hk i (hs' hi) j (hs' hj) h),
      (fun k hk i hi => 𝒰.cover.tube_nested k hk i (hs' hi))⟩,
      b,
      ?tube_injOn, ?boundedOverlap, ?carrierLe, ?minorLt⟩,
    fun k => rfl, fun k => rfl, fun k => rfl, fun k => rfl⟩
  · intro k hk
    refine Set.InjOn.mono ?_ (𝒰.tube_injOn k hk)
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact 𝒰.cover.assign_mem k hk i (hs' hi)
  · intro k hk V
    refine le_trans ?_ ((𝒰.boundedOverlap k hk V).trans hCuC)
    refine Nat.cast_le.mpr (Finset.card_le_card ?_)
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    obtain ⟨hjm, i, hi, hb⟩ := hj
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hjm
    exact ⟨𝒰.cover.assign_mem k hk i' (hs' hi'), i, hs' hi, hb⟩
  · exact fun k hk j hj =>
      (hband k hk j hj).2.trans (mul_le_mul_of_nonneg_right hAC zero_le)
  · exact fun k hk j hj => (hband k hk j hj).1.trans (le_mul_of_one_le_left zero_le hC1)

/-! ### The tight net restricts -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The tight net restricts to a subfamily and a subset of the nodes** (blueprint
`lem:gridUniformNiceOfSubset`).  Both the node set and the set supplying the witnessing member
shrink, so the filtered node set only gets smaller and the tight constant is unchanged.  The node
tubes are passed in as `tb` with a proof `htb` that they are those of `𝒢`. -/
theorem gridUniform_nice_of_subset {δ : NNReal} {N : ℕ} {t t' : Finset ι} {T : ι → Tube δ E}
    {C : NNReal} (𝒢 : GridUniform t T N C) (ht' : t' ⊆ t)
    (idx : ℕ → Finset ι) (hidx : ∀ k ≤ N, idx k ⊆ 𝒢.cover.indexSet k)
    (tb : (k : ℕ) → ι → Tube (gridScale δ N k) E) (htb : ∀ k, tb k = 𝒢.cover.tube k) :
    ∀ k ≤ N,
      Set.InjOn (tb k) (idx k : Set ι) ∧
      ∀ V : Tube (gridScale δ N k) E,
        ((idx k).filter (fun v => ∃ i ∈ t',
          (T i).toConvexSpaceBody ≤ (tb k v).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
            Tube.overlapConstBOTight (Module.finrank ℝ E) := by
  classical
  intro k hk
  have hnice := 𝒢.nice k hk
  rw [htb k]
  refine ⟨hnice.1.mono (fun x hx => hidx k hk hx),
    fun V => (Finset.card_le_card fun v hv => ?_).trans (hnice.2 V)⟩
  rw [Finset.mem_filter] at hv ⊢
  exact ⟨hidx k hk hv.1, hv.2.imp fun i hi => ⟨ht' hi.1, hi.2⟩⟩

/-! ### The constants -/

/-- **Constant in `Kakeya.MultiScaleFac.exists_gridUniform_restrict_band`** (blueprint
`def:bandRestrictConst`): the bundle-level constant of the band restriction.  The inner maximum is
the constant of `Kakeya.MultiScaleFac.GridUniform.toUniformTubeSet`, the outer one absorbs the band
ratio `A` and keeps the value at least `1`.  It depends only on the dimension, on `C` and on `A`. -/
noncomputable def bandRestrictConst (C A : NNReal) : NNReal :=
  max (uniformTubeSetCuOf (E := E) C) (max A 1)

/-- **Constant in `Kakeya.MultiScaleFac.exists_gridUniform_restrict_band`** (blueprint
`def:gridUniformBandConst`): the square of `Kakeya.MultiScaleFac.bandRestrictConst`.  The square is
the passage from the *class* bracket carried by `UniformTubeSet` to the *containment* bracket of
`Tube.IsUniformAtScale`, and like the latter constant it depends only on `n`, `C` and `A`. -/
noncomputable def gridUniformBandConst (C A : NNReal) : NNReal :=
  (bandRestrictConst (E := E) C A) ^ 2

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The bundle-level band constant dominates `1` (blueprint `lem:oneLeBandRestrictConst`). -/
theorem one_le_bandRestrictConst {C A : NNReal} : 1 ≤ bandRestrictConst (E := E) C A :=
  le_max_of_le_right (le_max_right A 1)

/-! ### The assembly -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **A grid-uniform system restricted along a band, read as a bundle** (blueprint
`lem:uniformTubeSetOfGridUniformBand`).

`Kakeya.MultiScaleFac.GridUniform.toUniformTubeSet` followed by
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_of_supplied_band`. -/
theorem exists_uniformTubeSet_of_gridUniform_band {δ : NNReal} {N : ℕ} {t t' : Finset ι}
    {T : ι → Tube δ E} {C A : NNReal} (𝒢 : GridUniform t T N C) (ht' : t' ⊆ t) (b : ℕ → NNReal)
    (hband : ∀ k ≤ N, ∀ P ∈ t'.image (𝒢.cover.assign k),
      b k ≤ ((coverClass t' (𝒢.cover.assign k) P).card : NNReal) ∧
        ((coverClass t' (𝒢.cover.assign k) P).card : NNReal) ≤ A * b k) :
    ∃ 𝒰' : UniformTubeSet t' T N (bandRestrictConst (E := E) C A),
      (∀ k, 𝒰'.cover.indexSet k = t'.image (𝒢.cover.assign k)) ∧
        (∀ k, 𝒰'.cover.assign k = 𝒢.cover.assign k) ∧
          (∀ k, 𝒰'.cover.tube k = 𝒢.cover.tube k) ∧
            (∀ k, 𝒰'.branchingN k = b k) := by
  classical
  exact exists_restrict_uniformTubeSet_of_supplied_band (𝒰 := 𝒢.toUniformTubeSet)
    (C := bandRestrictConst (E := E) C A) ht' (le_max_left _ _)
    (le_max_of_le_right (le_max_left A 1)) one_le_bandRestrictConst b hband

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **Restricting a grid-uniform system along a class-size band** (blueprint
`lem:gridUniformRestrictBand`).  If `𝒢` makes `T` grid-uniform on `t` and an *arbitrary* `t' ⊆ t`
satisfies the two-sided band `b k ≤ (coverClass t' (assign k) P).card ≤ A * b k` at every level
`k ≤ N` and node `P` used by `t'`, then `t'` carries a grid-uniform system with the assignments and
node tubes of `𝒢`, branching numbers `b`, and constant `gridUniformBandConst C A`. -/
theorem exists_gridUniform_restrict_band {δ : NNReal} {N : ℕ} {t t' : Finset ι} {T : ι → Tube δ E}
    {C A : NNReal} (𝒢 : GridUniform t T N C) (ht' : t' ⊆ t) (b : ℕ → NNReal)
    (hband : ∀ k ≤ N, ∀ P ∈ t'.image (𝒢.cover.assign k),
      b k ≤ ((coverClass t' (𝒢.cover.assign k) P).card : NNReal) ∧
        ((coverClass t' (𝒢.cover.assign k) P).card : NNReal) ≤ A * b k) :
    ∃ 𝒢' : GridUniform t' T N (gridUniformBandConst (E := E) C A),
      (∀ k ≤ N, 𝒢'.cover.assign k = 𝒢.cover.assign k) ∧
        (∀ k, 𝒢'.cover.tube k = 𝒢.cover.tube k) ∧
          (∀ k (_hk : k ≤ N), 𝒢'.cover.indexSet k = t'.image (𝒢.cover.assign k)) ∧
            (∀ k (hk : k ≤ N), (𝒢'.uniformAt k hk).branchingN = b k) := by
  classical
  unfold gridUniformBandConst
  obtain ⟨U, hUidx, hUassign, hUtube, hUb⟩ :=
    exists_uniformTubeSet_of_gridUniform_band 𝒢 ht' b hband
  have hone : (1 : NNReal) ≤ bandRestrictConst (E := E) C A := one_le_bandRestrictConst
  have hfld := fun k (hk : k ≤ N) => uniformAt_toChain_fields U hone hk
  have hsubidx : ∀ k ≤ N, U.cover.indexSet k ⊆ 𝒢.cover.indexSet k := by
    intro k hk P hP
    rw [hUidx k] at hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
    exact 𝒢.cover.assign_mem k hk i (ht' hi)
  let huniform : ∀ k, k ≤ N →
      Tube.IsUniformAtScale t' T (gridScale δ N k) ((bandRestrictConst (E := E) C A) ^ 2) :=
    fun k hk => U.toChain.uniformAt hone hk
  have hparent : ∀ k (hk : k ≤ N), (huniform k hk).parent ⊆ U.cover.indexSet k :=
    fun k hk P hP => by rwa [(hfld k hk).1] at hP
  have hassign : ∀ k (hk : k ≤ N), ∀ i ∈ t', U.cover.assign k i ∈ (huniform k hk).parent :=
    fun k hk i hi => by rw [(hfld k hk).1]; exact U.cover.assign_mem k hk i hi
  have hparentTube : ∀ k (hk : k ≤ N), ∀ P ∈ (huniform k hk).parent,
      (huniform k hk).parentTube P = U.cover.tube k P :=
    fun k hk _ _ => by rw [(hfld k hk).2.1]
  have hlow : ∀ k (hk : k ≤ N), ∀ P ∈ (huniform k hk).parent,
      (huniform k hk).branchingN ≤ ((coverClass t' (U.cover.assign k) P).card : NNReal) := by
    intro k hk P hP
    rw [(hfld k hk).1] at hP
    rw [(hfld k hk).2.2, hUb k, hUassign k]
    exact (hband k hk P (by rwa [hUidx k] at hP)).1
  have hclump : ∀ k (hk0 : k < N), ∀ P ∈ (huniform k (le_of_lt hk0)).parent, ∃ i2 : ι,
      coverClass t' (U.cover.assign k) P ⊆ fibreIndex t' T δ (gridScale δ N k / 4) i2 := by
    intro k hk0 P hP
    rw [(hfld k hk0.le).1] at hP
    obtain ⟨i2, hsub⟩ := 𝒢.clumped k hk0 P (hsubidx k hk0.le hP)
    obtain ⟨j2, hsub2⟩ := clump_restrict_to_subset ht' (𝒢.cover.assign k) ⟨i2, hsub⟩
    exact ⟨j2, by rw [hUassign k]; exact hsub2⟩
  obtain ⟨G0, hGu, hGa, hGP, hGT⟩ :=
    exists_gridUniform_pack U.cover
      (gridUniform_nice_of_subset 𝒢 ht' U.cover.indexSet hsubidx U.cover.tube hUtube)
      huniform hparent hassign hparentTube hlow hclump
  exact ⟨G0, fun k hk => (hGa k hk).trans (hUassign k), fun k => (hGT k).trans (hUtube k),
    fun k hk => by rw [hGP k hk, (hfld k hk).1]; exact hUidx k,
    fun k hk => by rw [hGu k hk, (hfld k hk).2.2]; exact hUb k⟩

end MultiScaleFac

end Kakeya

end
