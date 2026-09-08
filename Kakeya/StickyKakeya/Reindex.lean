/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Sticky

/-!
# Reindexing a shaded family and its uniform hierarchy

`StickyKakeya.StickyKatzTaoEstimate` quantifies over `{ι : Type}`, i.e. over index types in
`Type 0`, while its Wang--Zahl consumer
`Kakeya.WangZahl.katzTaoEveryScale_multiplicity_le` is polymorphic in `{ι : Type u}`.  Applying
the former to the latter therefore needs a *reindexing*: every datum of the statement has to be
transported along a bijection between the (finite) index set actually in play and a type of
`Type 0`.

This file supplies that transport, for all of the data involved:

* `Kakeya.Reindex.Retract` -- the shape of the reindexing: a type `κ` together with maps
  `κ → ι` and `ι → κ` that are mutually inverse over a prescribed finite `F : Finset ι`.
  `Kakeya.Reindex.Retract.ofFinset` builds one with `κ = Fin F.card`, which lives in `Type 0`.
* `Kakeya.Reindex.Retract.idx` -- the transported index set, with `card`, `sum`, `filter` and
  `⋃` all preserved.
* `Kakeya.Reindex.Retract.gridCoverSystem`, `Kakeya.Reindex.Retract.uniformTubeSet`,
  `Kakeya.Reindex.Retract.shadedUniformTubeSet` -- the transported hierarchies.  Note that
  `Tube.GridCoverSystem` indexes its *nodes* by `ι` as well, so `F` has to contain the node
  index sets along the grid too; that is the hypothesis `hidx` throughout.
* `Kakeya.Reindex.Retract.isKatzTaoAtEveryScale`,
  `Kakeya.Reindex.Retract.maxDensity_idx`, `Kakeya.Reindex.Retract.fullness'_idx`,
  `Kakeya.Reindex.Retract.multiplicity_idx` -- the transported Katz--Tao / fullness /
  multiplicity data.

Nothing here is geometry: every proof is a bijection between two finite index sets.
-/

@[expose] public section

open MeasureTheory
open Tube
open ShadedTube

noncomputable section

namespace Kakeya.Reindex

universe u v

variable {ι : Type u} {κ : Type v}

/-- A **retraction of `ι` onto a finite subset `F`, with a small carrier `κ`**.

`toFun` embeds `κ` into `F` and `invFun` retracts `ι` onto `κ`; the two are mutually inverse
on `F`.  The point of the structure is that `κ` may live in a *different universe* from `ι`:
`Kakeya.Reindex.Retract.ofFinset` builds one with `κ = Fin F.card`, which is in `Type 0`. -/
structure Retract (κ : Type v) (ι : Type u) (F : Finset ι) where
  /-- The embedding of the small carrier into `ι`. -/
  toFun : κ → ι
  /-- The retraction of `ι` onto the small carrier. -/
  invFun : ι → κ
  /-- The embedding lands in `F`. -/
  mem : ∀ m, toFun m ∈ F
  /-- `invFun` is a left inverse of `toFun`. -/
  left_inv : ∀ m, invFun (toFun m) = m
  /-- `toFun` is a left inverse of `invFun` over `F`. -/
  right_inv : ∀ i ∈ F, toFun (invFun i) = i

namespace Retract

variable {F : Finset ι} (R : Retract κ ι F)

theorem toFun_injective : Function.Injective R.toFun :=
  Function.LeftInverse.injective R.left_inv

theorem invFun_injOn : Set.InjOn R.invFun (F : Set ι) := by
  intro a ha b hb hab
  have := congrArg R.toFun hab
  rwa [R.right_inv a ha, R.right_inv b hb] at this

open scoped Classical in
/-- `Fin F.card` is a retract carrier for any nonempty `F`, and it lives in `Type 0`. -/
def ofFinset (F : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ F) : Retract (Fin F.card) ι F where
  toFun := fun m => ((F.equivFin.symm m : {x // x ∈ F}) : ι)
  invFun := fun i => if h : i ∈ F then F.equivFin ⟨i, h⟩ else F.equivFin ⟨i₀, hi₀⟩
  mem := fun m => (F.equivFin.symm m).2
  left_inv := by
    intro m
    have h : ((F.equivFin.symm m : {x // x ∈ F}) : ι) ∈ F := (F.equivFin.symm m).2
    simp only [dif_pos h]
    rw [show (⟨((F.equivFin.symm m : {x // x ∈ F}) : ι), h⟩ : {x // x ∈ F})
        = F.equivFin.symm m from rfl]
    exact F.equivFin.apply_symm_apply m
  right_inv := by
    intro i hi
    simp only [dif_pos hi]
    rw [Equiv.symm_apply_apply]

/-! ### The transported index set -/

variable [DecidableEq κ]

/-- The transported index set. -/
def idx (s : Finset ι) : Finset κ := s.image R.invFun

variable {R}

theorem mem_idx {s : Finset ι} (hs : s ⊆ F) {m : κ} : m ∈ R.idx s ↔ R.toFun m ∈ s := by
  classical
  constructor
  · intro hm
    obtain ⟨i, hi, hmi⟩ := Finset.mem_image.mp hm
    rw [← hmi, R.right_inv i (hs hi)]
    exact hi
  · intro hm
    exact Finset.mem_image.mpr ⟨R.toFun m, hm, R.left_inv m⟩

theorem invFun_mem_idx {s : Finset ι} {i : ι} (hi : i ∈ s) : R.invFun i ∈ R.idx s :=
  Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem card_idx {s : Finset ι} (hs : s ⊆ F) : (R.idx s).card = s.card :=
  Finset.card_image_of_injOn (fun _ ha _ hb h => R.invFun_injOn (hs ha) (hs hb) h)

theorem idx_subset {s t : Finset ι} (h : s ⊆ t) : R.idx s ⊆ R.idx t :=
  Finset.image_subset_image h

theorem idx_nonempty {s : Finset ι} (h : s.Nonempty) : (R.idx s).Nonempty :=
  h.image _

theorem idx_filter {s : Finset ι} (hs : s ⊆ F) (p : ι → Prop) [DecidablePred p] :
    (R.idx s).filter (fun m => p (R.toFun m)) = R.idx (s.filter p) := by
  classical
  ext m
  simp only [Finset.mem_filter, mem_idx hs, mem_idx ((Finset.filter_subset p s).trans hs),
    Finset.mem_filter]

theorem sum_idx {M : Type*} [AddCommMonoid M] {s : Finset ι} (hs : s ⊆ F) (W : ι → M) :
    ∑ m ∈ R.idx s, W (R.toFun m) = ∑ i ∈ s, W i := by
  classical
  rw [idx, Finset.sum_image (fun _ ha _ hb h => R.invFun_injOn (hs ha) (hs hb) h)]
  exact Finset.sum_congr rfl (fun i hi => by rw [R.right_inv i (hs hi)])

theorem biUnion_idx {α : Type*} {s : Finset ι} (hs : s ⊆ F) (A : ι → Set α) :
    (⋃ m ∈ R.idx s, A (R.toFun m)) = ⋃ i ∈ s, A i := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, hx⟩
    exact ⟨R.toFun m, (mem_idx hs).mp hm, hx⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨R.invFun i, invFun_mem_idx hi, ?_⟩
    rwa [R.right_inv i (hs hi)]

/-! ### Transport of the analytic quantities -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem densityIn_idx {s : Finset ι} (hs : s ⊆ F) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) :
    Kakeya.densityIn (R.idx s) (fun m => W (R.toFun m)) K = Kakeya.densityIn s W K := by
  classical
  unfold Kakeya.densityIn
  congr 1
  rw [show ((R.idx s).filter (fun m => W (R.toFun m) ≤ K))
      = R.idx (s.filter (fun i => W i ≤ K)) from idx_filter hs (fun i => W i ≤ K)]
  exact sum_idx ((Finset.filter_subset _ s).trans hs) (fun i => volume (W i).carrier)

theorem maxDensity_idx {s : Finset ι} (hs : s ⊆ F) (W : ι → ConvexSpaceBody E) :
    Kakeya.maxDensity (R.idx s) (fun m => W (R.toFun m)) = Kakeya.maxDensity s W := by
  refine le_antisymm ?_ ?_
  · rw [Kakeya.maxDensity_le_iff]
    intro K
    rw [densityIn_idx hs W K]
    exact Kakeya.le_maxDensity s W K
  · rw [Kakeya.maxDensity_le_iff]
    intro K
    rw [← densityIn_idx (R := R) hs W K]
    exact Kakeya.le_maxDensity _ _ K

theorem isKatzTao_idx {s : Finset ι} (hs : s ⊆ F) (W : ι → ConvexSpaceBody E) {C : ENNReal}
    (h : ConvexSpaceBody.IsKatzTao s W C) :
    ConvexSpaceBody.IsKatzTao (R.idx s) (fun m => W (R.toFun m)) C := by
  rw [ConvexSpaceBody.IsKatzTao_def, maxDensity_idx hs W]
  exact h

theorem fullness'_idx {s : Finset ι} (hs : s ⊆ F) (V : ι → ShadedBody E) :
    ShadedBody.fullness' (R.idx s) (fun m => V (R.toFun m)) = ShadedBody.fullness' s V := by
  unfold ShadedBody.fullness'
  rw [sum_idx hs (fun i => volume (V i).shade), sum_idx hs (fun i => volume (V i).carrier)]

theorem multiplicity_idx {s : Finset ι} (hs : s ⊆ F) (V : ι → ShadedBody E) :
    ShadedBody.multiplicity (R.idx s) (fun m => V (R.toFun m))
      = ShadedBody.multiplicity s V := by
  unfold ShadedBody.multiplicity
  rw [sum_idx hs (fun i => volume (V i).shade),
    biUnion_idx hs (fun i => (V i).shade)]

/-! ### Membership in classes, with the classical instance normalised -/

theorem mem_coverClass {α : Type*} {u : Finset α} {assign : α → α} {P i : α} :
    i ∈ coverClass u assign P ↔ i ∈ u ∧ assign i = P := by
  simp only [coverClass, Finset.mem_filter]

theorem mem_shadeClass {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {α : Type*} {δ : NNReal} {u : Finset α} {V : α → ShadedTube δ E} {assign : α → α}
    {P : α} {x : E} {i : α} :
    i ∈ shadeClass u V assign P x ↔ (i ∈ u ∧ assign i = P) ∧ x ∈ (V i).shade := by
  simp only [shadeClass, coverClass, Finset.mem_filter]

/-! ### Transport of the uniform hierarchies -/

section Hierarchy

variable [Nontrivial E] (R)

/-- **The transported nested cover system.**  Since `Tube.GridCoverSystem` indexes its nodes by
the same type as its members, the finite set `F` has to contain the node index sets along the
grid as well; that is `hidx`. -/
def gridCoverSystem {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (G : GridCoverSystem s T N) (hs : s ⊆ F) (hidx : ∀ k, k ≤ N → G.indexSet k ⊆ F) :
    GridCoverSystem (R.idx s) (fun m => T (R.toFun m)) N where
  indexSet := fun k => R.idx (G.indexSet k)
  assign := fun k m => R.invFun (G.assign k (R.toFun m))
  tube := fun k m => G.tube k (R.toFun m)
  assign_mem := by
    intro k hk m hm
    exact invFun_mem_idx (G.assign_mem k hk _ ((mem_idx hs).mp hm))
  le_tube_assign := by
    intro k hk m hm
    have hgm : R.toFun m ∈ s := (mem_idx hs).mp hm
    have h1 : R.toFun (R.invFun (G.assign k (R.toFun m))) = G.assign k (R.toFun m) :=
      R.right_inv _ (hidx k hk (G.assign_mem k hk _ hgm))
    simp only [h1]
    exact G.le_tube_assign k hk _ hgm
  nested := by
    intro k hk m hm m' hm' h
    have hgm : R.toFun m ∈ s := (mem_idx hs).mp hm
    have hgm' : R.toFun m' ∈ s := (mem_idx hs).mp hm'
    have e1 : R.toFun (R.invFun (G.assign (k + 1) (R.toFun m))) = G.assign (k + 1) (R.toFun m) :=
      R.right_inv _ (hidx (k + 1) hk (G.assign_mem (k + 1) hk _ hgm))
    have e2 : R.toFun (R.invFun (G.assign (k + 1) (R.toFun m'))) = G.assign (k + 1) (R.toFun m') :=
      R.right_inv _ (hidx (k + 1) hk (G.assign_mem (k + 1) hk _ hgm'))
    have hh : G.assign (k + 1) (R.toFun m) = G.assign (k + 1) (R.toFun m') := by
      have := congrArg R.toFun h
      rwa [e1, e2] at this
    exact congrArg R.invFun (G.nested k hk _ hgm _ hgm' hh)
  tube_nested := by
    intro k hk m hm
    have hgm : R.toFun m ∈ s := (mem_idx hs).mp hm
    have e1 : R.toFun (R.invFun (G.assign (k + 1) (R.toFun m))) = G.assign (k + 1) (R.toFun m) :=
      R.right_inv _ (hidx (k + 1) hk (G.assign_mem (k + 1) hk _ hgm))
    have e2 : R.toFun (R.invFun (G.assign k (R.toFun m))) = G.assign k (R.toFun m) :=
      R.right_inv _ (hidx k (by omega) (G.assign_mem k (by omega) _ hgm))
    simp only [e1, e2]
    exact G.tube_nested k hk _ hgm

/-- **The transported uniform hierarchy** (GWZ Definition 2.1). -/
def uniformTubeSet {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (hs : s ⊆ F)
    (hidx : ∀ k, k ≤ N → 𝒰.cover.indexSet k ⊆ F) :
    UniformTubeSet (R.idx s) (fun m => T (R.toFun m)) N C where
  cover := R.gridCoverSystem 𝒰.cover hs hidx
  branchingN := 𝒰.branchingN
  tube_injOn := by
    intro k hk m hm m' hm' h
    have h1 : R.toFun m ∈ 𝒰.cover.indexSet k := (mem_idx (hidx k hk)).mp hm
    have h2 : R.toFun m' ∈ 𝒰.cover.indexSet k := (mem_idx (hidx k hk)).mp hm'
    exact R.toFun_injective (𝒰.tube_injOn k hk h1 h2 h)
  boundedOverlap := by
    classical
    intro k hk V
    have hcard :
        ((R.idx (𝒰.cover.indexSet k)).filter (fun j => ∃ i ∈ R.idx s,
            (T (R.toFun i)).toConvexSpaceBody ≤ (𝒰.cover.tube k (R.toFun j)).toConvexSpaceBody ∧
            (T (R.toFun i)).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card
          ≤ ((𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card := by
      refine Finset.card_le_card_of_injOn R.toFun ?_ (fun a _ b _ h => R.toFun_injective h)
      intro j hj
      obtain ⟨hj1, i, hi, hi1, hi2⟩ := by simpa using Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨(mem_idx (hidx k hk)).mp hj1, ?_⟩
      exact ⟨R.toFun i, (mem_idx hs).mp hi, hi1, hi2⟩
    exact le_trans (by exact_mod_cast hcard) (𝒰.boundedOverlap k hk V)
  card_class_le := by
    intro k hk j hj
    have hjg : R.toFun j ∈ 𝒰.cover.indexSet k := (mem_idx (hidx k hk)).mp hj
    refine le_trans (?_ : _ ≤ (((coverClass s (𝒰.cover.assign k) (R.toFun j)).card : ℕ) : NNReal))
      (𝒰.card_class_le k hk _ hjg)
    refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn R.toFun ?_
      (fun a _ b _ h => R.toFun_injective h))
    intro m hm
    simp only [Finset.mem_coe, mem_coverClass] at hm ⊢
    obtain ⟨hm1, hm2⟩ := hm
    have hgm : R.toFun m ∈ s := (mem_idx hs).mp hm1
    have hm2' : R.invFun (𝒰.cover.assign k (R.toFun m)) = j := hm2
    refine ⟨hgm, ?_⟩
    have := congrArg R.toFun hm2'
    rwa [R.right_inv _ (hidx k hk (𝒰.cover.assign_mem k hk _ hgm))] at this
  le_card_class := by
    intro k hk j hj
    have hjg : R.toFun j ∈ 𝒰.cover.indexSet k := (mem_idx (hidx k hk)).mp hj
    refine le_trans (𝒰.le_card_class k hk _ hjg) ?_
    gcongr
    refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn R.invFun ?_ ?_)
    · intro i hi
      simp only [Finset.mem_coe, mem_coverClass] at hi ⊢
      obtain ⟨hi1, hi2⟩ := hi
      refine ⟨invFun_mem_idx hi1, ?_⟩
      change R.invFun (𝒰.cover.assign k (R.toFun (R.invFun i))) = j
      rw [R.right_inv i (hs hi1), hi2, R.left_inv]
    · intro a ha b hb h
      rw [Finset.mem_coe, mem_coverClass] at ha hb
      exact R.invFun_injOn (hs ha.1) (hs hb.1) h

variable {R}

omit [Nontrivial E] in
/-- The transported hierarchy inherits the Katz--Tao every-scale bound. -/
theorem isKatzTaoAtEveryScale_idx {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (hs : s ⊆ F)
    (hidx : ∀ k, k ≤ N → 𝒰.cover.indexSet k ⊆ F) {A : ENNReal}
    (h : 𝒰.IsKatzTaoAtEveryScale A) :
    (R.uniformTubeSet 𝒰 hs hidx).IsKatzTaoAtEveryScale A := by
  intro k hk
  show Kakeya.maxDensity (R.idx (𝒰.cover.indexSet k))
      (fun m => (𝒰.cover.tube k (R.toFun m)).toConvexSpaceBody) ≤ A
  rw [maxDensity_idx (R := R) (hidx k hk) (fun j => (𝒰.cover.tube k j).toConvexSpaceBody)]
  exact h k hk

variable (R)

/-- **The transported shaded uniform hierarchy** (GWZ Definition 2.2). -/
def shadedUniformTubeSet {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C) (hs : s ⊆ F)
    (hidx : ∀ k, k ≤ N → 𝒱.tubeUniform.cover.indexSet k ⊆ F) :
    ShadedUniformTubeSet (R.idx s) (fun m => V (R.toFun m)) N C where
  tubeUniform := R.uniformTubeSet 𝒱.tubeUniform hs hidx
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := by
    intro x hx k hk m hm hxm
    have hx' : x ∈ ⋃ i ∈ s, (V i).shade := by
      rwa [biUnion_idx hs (fun i => (V i).shade)] at hx
    have hgm : R.toFun m ∈ s := (mem_idx hs).mp hm
    refine le_trans (?_ : _ ≤ (((shadeClass s V (𝒱.tubeUniform.cover.assign k)
        (𝒱.tubeUniform.cover.assign k (R.toFun m)) x).card : ℕ) : NNReal))
      (𝒱.card_shadeClass_le x hx' k hk _ hgm hxm)
    refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn R.toFun ?_
      (fun a _ b _ h => R.toFun_injective h))
    intro m' hm'
    simp only [Finset.mem_coe, mem_shadeClass] at hm' ⊢
    obtain ⟨⟨hm'3, hm'4⟩, hm'2⟩ := hm'
    have hgm' : R.toFun m' ∈ s := (mem_idx hs).mp hm'3
    have hm'4' : R.invFun (𝒱.tubeUniform.cover.assign k (R.toFun m'))
        = R.invFun (𝒱.tubeUniform.cover.assign k (R.toFun m)) := hm'4
    refine ⟨⟨hgm', ?_⟩, hm'2⟩
    have := congrArg R.toFun hm'4'
    rwa [R.right_inv _ (hidx k hk (𝒱.tubeUniform.cover.assign_mem k hk _ hgm')),
      R.right_inv _ (hidx k hk (𝒱.tubeUniform.cover.assign_mem k hk _ hgm))] at this
  le_card_shadeClass := by
    intro x hx k hk m hm hxm
    have hx' : x ∈ ⋃ i ∈ s, (V i).shade := by
      rwa [biUnion_idx hs (fun i => (V i).shade)] at hx
    have hgm : R.toFun m ∈ s := (mem_idx hs).mp hm
    refine le_trans (𝒱.le_card_shadeClass x hx' k hk _ hgm hxm) ?_
    gcongr
    refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn R.invFun ?_ ?_)
    · intro i hi
      simp only [Finset.mem_coe, mem_shadeClass] at hi ⊢
      obtain ⟨⟨hi3, hi4⟩, hi2⟩ := hi
      refine ⟨⟨invFun_mem_idx hi3, ?_⟩, ?_⟩
      · change R.invFun (𝒱.tubeUniform.cover.assign k (R.toFun (R.invFun i)))
            = R.invFun (𝒱.tubeUniform.cover.assign k (R.toFun m))
        rw [R.right_inv i (hs hi3), hi4]
      · rw [R.right_inv i (hs hi3)]; exact hi2
    · intro a ha b hb h
      simp only [Finset.mem_coe, mem_shadeClass] at ha hb
      exact R.invFun_injOn (hs ha.1.1) (hs hb.1.1) h
  branchingN_le := by
    intro x hx k hk
    have hx' : x ∈ ⋃ i ∈ s, (V i).shade := by
      rwa [biUnion_idx hs (fun i => (V i).shade)] at hx
    exact 𝒱.branchingN_le x hx' k hk
  le_branchingN := by
    intro x hx k hk
    have hx' : x ∈ ⋃ i ∈ s, (V i).shade := by
      rwa [biUnion_idx hs (fun i => (V i).shade)] at hx
    exact 𝒱.le_branchingN x hx' k hk

end Hierarchy

end Retract

end Reindex

end Kakeya

/-! ### The universe bridge for GWZ Theorem 7.3(B) -/

namespace StickyKakeya

open Kakeya.Reindex

universe w

/-- **`StickyKakeya.StickyKatzTaoEstimate`, applied at an arbitrary universe.**

`StickyKakeya.StickyKatzTaoEstimate` quantifies over `{ι : Type}`, i.e. over index types in
`Type 0`.  Its Wang--Zahl consumer `Kakeya.WangZahl.katzTaoEveryScale_multiplicity_le` is
polymorphic in `{ι : Type w}`.  This lemma bridges the two: given the estimate at `Type 0`, the
same conclusion holds for a family indexed by any `ι : Type w`.

There is no mathematics here.  All the data of the statement is supported on the finite set
`F = s ∪ ⋃_{k ≤ N} 𝕋_{ρ_k}` of members and nodes, and `Kakeya.Reindex.Retract.ofFinset`
transports it verbatim to `Fin F.card`, which lives in `Type 0`. -/
theorem stickyKatzTaoEstimate_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (h : StickyKatzTaoEstimate (E := E)) (ε : ℝ) (hε : 0 < ε) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ →
      ∀ {ι : Type w} (s : Finset ι) (V : ι → ShadedTube δ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∀ {C : NNReal} (𝒱 : ShadedUniformTubeSet s V (Tube.ssfGridLen δ) C),
        ENNReal.ofReal ((δ : ℝ) ^ η)
          ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody) →
        ConvexSpaceBody.IsKatzTao s (fun i => (V i).toConvexSpaceBody)
            (ENNReal.ofReal ((δ : ℝ) ^ (-η))) →
        𝒱.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-η))) →
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε)) := by
  classical
  obtain ⟨η, δ₀, hη, hδ₀, hmain⟩ := h ε hε
  refine ⟨η, δ₀, hη, hδ₀, ?_⟩
  intro δ hδ hδle ι s V hball C 𝒱 hfull hKT hKTES
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp [ShadedBody.multiplicity]
  · let F : Finset ι := s ∪ (Finset.range (Tube.ssfGridLen δ + 1)).biUnion
      (fun k => 𝒱.tubeUniform.cover.indexSet k)
    have hsF : s ⊆ F := Finset.subset_union_left
    have hidxF : ∀ k, k ≤ Tube.ssfGridLen δ → 𝒱.tubeUniform.cover.indexSet k ⊆ F := by
      intro k hk
      refine subset_trans ?_ Finset.subset_union_right
      exact Finset.subset_biUnion_of_mem _ (Finset.mem_range.mpr (by omega))
    have hi₀F : i₀ ∈ F := hsF hi₀
    set R : Retract (Fin F.card) ι F := Retract.ofFinset F i₀ hi₀F with hR
    have hres := hmain (δ := δ) hδ hδle (R.idx s) (fun m => V (R.toFun m))
      (fun m hm => hball _ ((Retract.mem_idx hsF).mp hm))
      (R.shadedUniformTubeSet 𝒱 hsF hidxF)
      (by rw [Retract.fullness'_idx hsF (fun i => (V i).toShadedBody)]; exact hfull)
      (Retract.isKatzTao_idx hsF (fun i => (V i).toConvexSpaceBody) hKT)
      (Retract.isKatzTaoAtEveryScale_idx 𝒱.tubeUniform hsF hidxF hKTES)
    rwa [Retract.multiplicity_idx hsF (fun i => (V i).toShadedBody)] at hres

end StickyKakeya

end

end
