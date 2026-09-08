/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.LooseUniform

/-!
# R18: what the exact→loose producer question is, and exactly what is compiled here

`MainLemma2/LooseUniform.lean` introduces the three loose
structures of the R18 route and says in its own module docstring that they have **no producer**. This file measures the gap between the exact and the loose bundle, and compiles one family on
which the loose bundle fails. Its results are conditional on the geometric hypotheses specified below.

## What is in scope at conjunct 6's call site

Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`
(`MainLemma2/SetupSideData.lean`) binds exactly `cfg : Kakeya.VeryNotSticky`,
`bd : Kakeya.VeryNotSticky.BallData cfg`, the six parameter equations, and the grid level `k`
with its two `Tube.gridScale` bounds.  The **only** uniformity datum `cfg` carries is the field
`Kakeya.VeryNotSticky.uniform`, namely
`Nonempty (ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)` — the
*exact* GWZ Definition 2.2 bundle on the *whole* family `cfg.s`.  So a producer of
`Kakeya.LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) 4 cfg.C₀`
must come from that exact bundle (possibly rebuilding the cover directly out of `cfg.s`
and `cfg.T`).

## Part 1 — the conditional producer: the gap is exactly TWO fields

`Kakeya.LooseUniform.Producer.looseShadedOfExact` builds the loose Definition-2.2 bundle from
the exact one, at the same `s`, `T`, `N` and `C`, given **exactly two** residual data:

* `hdir` — the loose `dir_close_tube_assign` bracket, and
* `hbo` — the loose `boundedOverlapDil` bracket.

Every other field is *derived*: `assign_mem`, `nested`, `tube_injOn`, `card_class_le`,
`le_card_class` and all six shade brackets transfer **verbatim** (they are literally the same
statements), and `le_dilate_tube_assign` follows from the exact `le_tube_assign` through
`Tube.subset_dilate`.  That is the honest measurement of the gap, compiler-established, and
 confirms it.

## Part 2 — `hdir` is not implied by exact containment at the coarse level

`Kakeya.LooseUniform.Producer.exists_le_tube_not_dir_close`: at the coarse grid level `k = 0`,
where `Tube.gridScale δ N 0 = 1`, a `δ`-tube through the origin **transverse** to the node's
axis is *exactly contained* in the node, while its direction is at distance `√2` from the
node's — vastly more than the `1/4` the loose bracket demands.  So exact containment carries
no direction information at all at the coarse level, at every `N`.

Note what `dir_close_tube_assign` is: GWZ's Definition 2.1 (`gwz.txt` l.177-184) has **no**
direction clause at any scale, and `Kakeya.LooseUniform.LooseGridCoverSystem`
(`MainLemma2/LooseUniform.lean`) adds this one.  At `k = 0` it demands every member's direction
lie within `1/4` of its node's, at a level where GWZ's Definition 2.1 says nothing at all
(`T_1 = {B₁}`).

## Part 3 — one family on which the loose bundle fails

`Kakeya.LooseUniform.Producer.not_nonempty_looseUniformTubeSet_bush`: on the family of `m`
distinct unit `δ`-tubes through the origin in the direction `e₁` (axial offsets
`i / (4(m+1))`) **plus one** transverse member in the direction `e₂`, there is **no**
`Kakeya.LooseUniform.LooseUniformTubeSet` at **any** dilation factor `K ≥ 0` and any constant
`C` with `C³ < m + 1`, for **every** grid length `N`.  The mechanism:

* the loose direction bracket at `ρ₀ = 1` forces the transverse member into a node of its own,
  so its class is a **singleton**, whence `branchingN 0 ≤ C`;
* `boundedOverlapDil` against the coarse node containing the whole family caps the number of
  nodes in use by `C`;
* the two class brackets then force `m + 1 ≤ C · (C · 1) · C = C³`.

`Kakeya.LooseUniform.Producer.not_nonempty_looseShaded_ssfGridLen` states the same failure at
the Section-9 grid length `N = Tube.ssfGridLen δ` and the Section-9 dilation factor `K = 4`.
`Kakeya.LooseUniform.Producer.exact_datum_does_not_produce_loose` puts an exact bundle and the
failure on **one** family — but at grid length `0` on both sides (see below).

## What this does and does not establish [narrowed by ]

* It does **not** establish that a producer cannot exist.  An earlier version of this docstring
  claimed that; -§3.6 measured the claim and it does not hold.  Three
  measurements are the reason:

  1. *(§3.5(a), measured)* `exact_datum_does_not_produce_loose` is stated at grid length **`0`**
     on both sides — `ShadedTube.ShadedUniformTubeSet … (bV δ m) 0 1` and
     `LooseShadedUniformTubeSet … (bV δ m) 0 K C`.  The exact bundle
     `Kakeya.LooseUniform.Producer.exactShaded` is built on
     `Kakeya.LooseUniform.Producer.gridScale_zero_len : Tube.gridScale δ 0 k = 1`, the
     degenerate one-node grid.  `not_nonempty_looseShaded_ssfGridLen` *is* at the Section-9
     grid length, but it carries **no exact-datum companion**: no family is exhibited here that
     holds the exact Definition-2.2 datum at `N = Tube.ssfGridLen δ` and fails the loose one.
  2. *(§3.5(b), compiled probe)* On that same family the **other** residual bracket, `hbo`
     (`boundedOverlapDil`), is **true** at `K = 4`, `C = 1` — the level's index set is `{0}`, so
     every filter of it has card `≤ 1`.  The sole refuted bracket is therefore
     `Kakeya.LooseUniform.LooseGridCoverSystem.dir_close_tube_assign`, the clause Part 2 records
     as this development's own addition to GWZ's Definition 2.1.
  3. *(§3.5(c)/(e), measured)* Every step of the impossibility lives at `k = 0`, where
     `Tube.gridScale δ N 0 = 1`.  Conjunct 6's level is pinned near
     `gridScale ≈ cfg.rho2Star bd.C₀`, and `Kakeya.LooseUniform.angularCone_card_le_of_loose`
     reads the brackets only at that same `k`.  So the clause that kills this family is imposed
     at a level GWZ's Definition 2.1 leaves empty and **no consumer reads**.

* The loose type is **not** empty, at any `N`.  `Kakeya.LooseUniform.NonVacuity` inhabits it on
  a genuinely two-membered family (`exists_looseShadedUniformTubeSet_card_two`, at `N = 1`,
  `K = 4`, `C = 2`, with loaded brackets), and 's compiled probe inhabits it at
  **every** `N` at `K = 4`, `C = 1`.  Nothing here is an emptiness result.

* What survives as an argument against the loose datum *as existing* is a reading of the source,
  not a consequence of Part 3: GWZ's l.191-193 only ever produces uniformity on a
  **refinement**, whereas the loose datum as existing is stated on the full `cfg.s`, which is
  fixed by the configuration and cannot be refined by a producer.   confirms
  that half and rests its §1 verdict on it.

* It does **not** establish that conjunct 6 is false, and nothing here may be cited to that
  effect.  It also does not establish that the bush-plus-transverse
  family satisfies the other 50 fields of `Kakeya.VeryNotSticky`; that question is untouched
  and remains uncompiled.  Finally,
  `Kakeya.VeryNotSticky.eventually_conjunct6_of_looseUniform` (`MainLemma2/LooseUniform.lean`)
  is **not** conjunct 6: it reads the fibres off a bound `LooseShadedUniformTubeSet`, whereas
  conjunct 6 names `cfg.activeTubeNodes cfg.splitHierarchy` / `cfg.tubeFibre cfg.splitHierarchy`
  — the `Classical.choice`-selected exact hierarchy.  Even a producer of the loose datum would
  not discharge conjunct 6 as existing.

## Duplicate short names, recorded not merged

`norm_e₂`, `inner_e₁_e₂` and `inner_e₂_e₁` below duplicate declarations of the same short names
in `Kakeya.DimensionThree.MainLemma1.Factoring`.  The full names differ (this file's live in
`Kakeya.LooseUniform.Producer`), and they are kept separate **deliberately**: importing
`MainLemma1/Factoring.lean` into `MainLemma2` would create a cross-area import for three
two-line orthonormality facts.  Recorded here so the duplication is not rediscovered as a defect.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya.LooseUniform.Producer

open Kakeya.LooseUniform Kakeya.LooseUniform.NonVacuity

/-! ## Part 1 — the conditional producer -/

section Conditional
variable {ι : Type*}

/-- **The loose cover system inherited from an exact one.**  Everything but the direction
bracket is derived: `Tube.GridCoverSystem.le_tube_assign` gives the `K`-dilate containment
through `Tube.subset_dilate`, and `assign_mem`/`nested` transfer verbatim.  The loose model
drops `Tube.GridCoverSystem.tube_nested`, so nothing is owed there. -/
noncomputable def looseCoverOfExact {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E3} {N : ℕ}
    {K : ℝ} (hK : 1 ≤ K) (G : Tube.GridCoverSystem s T N)
    (hdir : ∀ k, k ≤ N → ∀ i ∈ s, ∃ σ : ℝ, |σ| = 1 ∧
      ‖(T i).direction - σ • (G.tube k (G.assign k i)).direction‖
        ≤ (Tube.gridScale δ N k : ℝ) / 4) :
    LooseGridCoverSystem s T N K where
  indexSet := G.indexSet
  assign := G.assign
  tube := G.tube
  assign_mem := G.assign_mem
  le_dilate_tube_assign := fun k hk i hi =>
    le_trans (G.le_tube_assign k hk i hi) (fun _ hx => Tube.subset_dilate _ hK hx)
  dir_close_tube_assign := hdir
  nested := G.nested

/-- **The loose Definition-2.1 bundle inherited from the exact one**, at the *same* constant
`C`, given the two residual brackets.  `tube_injOn`, `card_class_le` and `le_card_class` are the
exact fields verbatim. -/
noncomputable def looseUniformOfExact {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E3} {N : ℕ}
    {K : ℝ} {C : NNReal} (hK : 1 ≤ K) (𝒰 : Tube.UniformTubeSet s T N C)
    (hdir : ∀ k, k ≤ N → ∀ i ∈ s, ∃ σ : ℝ, |σ| = 1 ∧
      ‖(T i).direction - σ • (𝒰.cover.tube k (𝒰.cover.assign k i)).direction‖
        ≤ (Tube.gridScale δ N k : ℝ) / 4)
    (hbo : ∀ k ≤ N, ∀ V : Tube (Tube.gridScale δ N k) E3,
      (open scoped Classical in
        (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s, 𝒰.cover.assign k i = j ∧
          (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V (K + 4))).card ≤ C) :
    LooseUniformTubeSet s T N K C where
  cover := looseCoverOfExact hK 𝒰.cover hdir
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlapDil := hbo
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

/-- **The loose Definition-2.2 bundle inherited from the exact one.**  All six shade brackets of
`ShadedTube.ShadedUniformTubeSet` are the loose ones verbatim, so the whole gap between the two
models is the pair `hdir`, `hbo`. -/
noncomputable def looseShadedOfExact {δ : NNReal} {s : Finset ι} {Y : ι → ShadedTube δ E3}
    {N : ℕ} {K : ℝ} {C : NNReal} (hK : 1 ≤ K)
    (𝒱 : ShadedTube.ShadedUniformTubeSet s Y N C)
    (hdir : ∀ k, k ≤ N → ∀ i ∈ s, ∃ σ : ℝ, |σ| = 1 ∧
      ‖(Y i).toTube.direction
          - σ • (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).direction‖
        ≤ (Tube.gridScale δ N k : ℝ) / 4)
    (hbo : ∀ k ≤ N, ∀ V : Tube (Tube.gridScale δ N k) E3,
      (open scoped Classical in
        (𝒱.tubeUniform.cover.indexSet k).filter
          (fun j => ∃ i ∈ s, 𝒱.tubeUniform.cover.assign k i = j ∧
            (Y i).toTube.toConvexSpaceBody ≤ Kakeya.Tube.dilate V (K + 4))).card ≤ C) :
    LooseShadedUniformTubeSet s Y N K C where
  tubeUniform := looseUniformOfExact hK 𝒱.tubeUniform hdir hbo
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := 𝒱.card_shadeClass_le
  le_card_shadeClass := 𝒱.le_card_shadeClass
  branchingN_le := 𝒱.branchingN_le
  le_branchingN := 𝒱.le_branchingN

end Conditional

/-! ## Elementary geometry of bush tubes through the origin -/

/-- The second coordinate direction of `E3`. -/
noncomputable def e₂ : E3 := EuclideanSpace.single 1 1

lemma norm_e₂ : ‖e₂‖ = 1 := by simp [e₂]

lemma inner_e₁_e₂ : (inner ℝ e₁ e₂ : ℝ) = 0 := by
  simp [e₁, e₂, EuclideanSpace.inner_single_left]

lemma inner_e₂_e₁ : (inner ℝ e₂ e₁ : ℝ) = 0 := by
  simp [e₁, e₂, EuclideanSpace.inner_single_left]

/-- Two orthonormal vectors are at distance `√2 > 1` however the second one is signed. -/
lemma one_lt_norm_sub_smul {u w : E3} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (huw : (inner ℝ u w : ℝ) = 0) {c : ℝ} (hc : |c| = 1) : 1 < ‖u - c • w‖ := by
  have hsq : ‖u - c • w‖ ^ 2 = 1 + c ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, huw, norm_smul, hu, hw]
    simp [Real.norm_eq_abs, sq_abs]
  have hc2 : c ^ 2 = 1 := by
    rcases (abs_eq (a := c) (b := 1) (by norm_num)).mp hc with h1 | h1 <;> rw [h1] <;> norm_num
  nlinarith [norm_nonneg (u - c • w), hsq, hc2]

/-- A bush tube through the origin sits in a ball about the origin. -/
lemma bushTube_carrier_subset_closedBall (δ : NNReal) (v : E3) (hv : ‖v‖ = 1) (t : ℝ) :
    (bushTube δ 0 v hv t).carrier ⊆ Metric.closedBall (0 : E3) (|t| + (1 / 2 + (δ : ℝ))) := by
  intro z hz
  have h := Tube.carrier_subset_closedBall_midpoint E3 (bushTube δ 0 v hv t) hz
  have hc : midpoint ℝ (bushTube δ 0 v hv t).x (bushTube δ 0 v hv t).y = t • v := by
    simpa using bushTube_center δ 0 v hv t
  rw [hc, Metric.mem_closedBall] at h
  rw [Metric.mem_closedBall]
  have h3 : dist (t • v) (0 : E3) = |t| := by
    rw [dist_zero_right, norm_smul, hv, Real.norm_eq_abs, mul_one]
  calc dist z 0 ≤ dist z (t • v) + dist (t • v) 0 := dist_triangle _ _ _
    _ ≤ (1 / 2 + (δ : ℝ)) + |t| := by rw [h3]; linarith
    _ = |t| + (1 / 2 + (δ : ℝ)) := by ring

/-- The ball of the tube's own radius about the origin sits inside a bush tube through the
origin. -/
lemma closedBall_subset_bushTube_carrier (ρ : NNReal) (v : E3) (hv : ‖v‖ = 1) {t : ℝ}
    (ht : |t| ≤ 1 / 2) :
    Metric.closedBall (0 : E3) (ρ : ℝ) ⊆ (bushTube ρ 0 v hv t).carrier :=
  (bushTube ρ 0 v hv t).closedBall_subset_carrier_of_mem_segment
    (mem_segment_bushTube ρ 0 v hv ht)

/-! ## Part 2 — exact containment does not give the loose direction bracket -/

/-- **The residual datum `hdir` of `looseUniformOfExact` is NOT implied by the exact model.**
At the coarse grid level `k = 0` the node has radius `Tube.gridScale δ N 0 = 1`, so a `δ`-tube
through the origin lies in it whatever its direction: exact containment carries no direction
information there, while the loose bracket demands the direction be within `1/4`.  The witness
is transverse, at distance `√2`. -/
theorem exists_le_tube_not_dir_close {δ : NNReal} (hδ : (δ : ℝ) ≤ 1 / 2) (N : ℕ) :
    ∃ (A : Tube δ E3) (V : Tube (Tube.gridScale δ N 0) E3),
      A.toConvexSpaceBody ≤ V.toConvexSpaceBody ∧
      ∀ σ : ℝ, |σ| = 1 →
        ¬ ‖A.direction - σ • V.direction‖ ≤ (Tube.gridScale δ N 0 : ℝ) / 4 := by
  refine ⟨bushTube δ 0 e₂ norm_e₂ 0, bushTube (Tube.gridScale δ N 0) 0 e₁ norm_e₁ 0, ?_, ?_⟩
  · intro z hz
    have h1 := bushTube_carrier_subset_closedBall δ e₂ norm_e₂ 0 hz
    refine closedBall_subset_bushTube_carrier (Tube.gridScale δ N 0) e₁ norm_e₁
      (by norm_num) ?_
    rw [Tube.gridScale_zero]
    simp only [NNReal.coe_one]
    rw [Metric.mem_closedBall] at h1 ⊢
    simp only [abs_zero, zero_add] at h1
    linarith
  · intro σ hσ hle
    have h14 : ((Tube.gridScale δ N 0 : NNReal) : ℝ) / 4 = 1 / 4 := by
      rw [Tube.gridScale_zero]; norm_num
    rw [bushTube_direction, bushTube_direction, h14] at hle
    have := one_lt_norm_sub_smul norm_e₂ norm_e₁ inner_e₂_e₁ hσ
    linarith

/-! ## Part 3 — the bush-plus-transverse family, and the impossibility -/

/-- The axial offsets of the `m` parallel members. -/
noncomputable def bOff (m : ℕ) (i : Fin (m + 1)) : ℝ := (i : ℝ) / (4 * (m + 1))

lemma bOff_nonneg (m : ℕ) (i : Fin (m + 1)) : 0 ≤ bOff m i := by
  unfold bOff; positivity

lemma bOff_abs_le (m : ℕ) (i : Fin (m + 1)) : |bOff m i| ≤ 1 / 4 := by
  have h0 : 0 ≤ bOff m i := bOff_nonneg m i
  rw [abs_of_nonneg h0]
  have him : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  have hpos : (0 : ℝ) < 4 * (m + 1) := by positivity
  rw [bOff, div_le_iff₀ hpos]
  nlinarith

lemma bOff_injective (m : ℕ) : Function.Injective (bOff m) := by
  intro i j h
  have hpos : (0 : ℝ) < 4 * ((m : ℝ) + 1) := by positivity
  have h1 : (i : ℝ) = (j : ℝ) := by
    have := h
    rw [bOff, bOff, div_eq_div_iff hpos.ne' hpos.ne'] at this
    exact (mul_right_cancel₀ hpos.ne' this)
  exact Fin.ext (by exact_mod_cast h1)

/-- **The family**: `m` distinct unit `δ`-tubes through the origin in the direction `e₁`, at
axial offsets `i / (4(m+1))`, plus **one** transverse member in the direction `e₂`.  This is a
bush — exactly the configuration `Kakeya.LooseUniform.bush_obstruction` is about — with one
member turned sideways. -/
noncomputable def bT (δ : NNReal) (m : ℕ) (i : Fin (m + 1)) : Tube δ E3 :=
  if (i : ℕ) < m then bushTube δ 0 e₁ norm_e₁ (bOff m i) else bushTube δ 0 e₂ norm_e₂ 0

lemma bT_direction_of_lt {δ : NNReal} {m : ℕ} {i : Fin (m + 1)} (hi : (i : ℕ) < m) :
    (bT δ m i).direction = e₁ := by
  rw [bT, if_pos hi, bushTube_direction]

lemma bT_direction_last {δ : NNReal} (m : ℕ) : (bT δ m (Fin.last m)).direction = e₂ := by
  rw [bT, if_neg (by simp), bushTube_direction]

/-- The `m` parallel members are pairwise distinct tubes. -/
lemma bT_injOn_of_lt {δ : NNReal} {m : ℕ} {i j : Fin (m + 1)} (hi : (i : ℕ) < m)
    (hj : (j : ℕ) < m) (h : bT δ m i = bT δ m j) : i = j := by
  rw [bT, if_pos hi, bT, if_pos hj] at h
  exact bOff_injective m (bushTube_offset_injective h)

lemma bT_carrier_subset {δ : NNReal} (hδ : (δ : ℝ) ≤ 1 / 4) (m : ℕ) (i : Fin (m + 1)) :
    (bT δ m i).carrier ⊆ Metric.closedBall (0 : E3) 1 := by
  have hmono : ∀ (v : E3) (hv : ‖v‖ = 1) (t : ℝ), |t| ≤ 1 / 4 →
      (bushTube δ 0 v hv t).carrier ⊆ Metric.closedBall (0 : E3) 1 := by
    intro v hv t ht
    refine (bushTube_carrier_subset_closedBall δ v hv t).trans ?_
    exact Metric.closedBall_subset_closedBall (by linarith)
  rw [bT]
  split
  · exact hmono e₁ norm_e₁ _ (bOff_abs_le m i)
  · exact hmono e₂ norm_e₂ 0 (by norm_num)

/-- The whole family lies in every dilate of the single coarse node. -/
lemma bT_le_dilate_node {δ : NNReal} (hδ : (δ : ℝ) ≤ 1 / 4) (m N : ℕ) (i : Fin (m + 1))
    {c : ℝ} (hc : 1 ≤ c) :
    (bT δ m i).toConvexSpaceBody ≤
      Kakeya.Tube.dilate (bushTube (Tube.gridScale δ N 0) 0 e₁ norm_e₁ 0) c := by
  intro z hz
  refine Tube.subset_dilate _ hc ?_
  refine closedBall_subset_bushTube_carrier (Tube.gridScale δ N 0) e₁ norm_e₁ (by norm_num) ?_
  rw [Tube.gridScale_zero]
  simpa using bT_carrier_subset hδ m i hz

/-- **The transverse member cannot share a loose node with any parallel member.**  This is the
direction bracket doing real work: no unit vector is within `1/4` of both `±e₁` and `±e₂`. -/
lemma dir_sep {δ : NNReal} {m N : ℕ} {K : ℝ} {C : NNReal}
    (𝒰 : LooseUniformTubeSet (Finset.univ : Finset (Fin (m + 1))) (bT δ m) N K C)
    {i : Fin (m + 1)} (hi : (i : ℕ) < m) :
    𝒰.cover.assign 0 i ≠ 𝒰.cover.assign 0 (Fin.last m) := by
  intro heq
  obtain ⟨σ, hσ, hσle⟩ :=
    𝒰.cover.dir_close_tube_assign 0 (Nat.zero_le N) i (Finset.mem_univ i)
  obtain ⟨τ, hτ, hτle⟩ :=
    𝒰.cover.dir_close_tube_assign 0 (Nat.zero_le N) (Fin.last m) (Finset.mem_univ _)
  have h14 : ((Tube.gridScale δ N 0 : NNReal) : ℝ) / 4 = 1 / 4 := by
    rw [Tube.gridScale_zero]; norm_num
  rw [h14] at hσle hτle
  rw [bT_direction_of_lt hi, heq] at hσle
  rw [bT_direction_last] at hτle
  set u : E3 := (𝒰.cover.tube 0 (𝒰.cover.assign 0 (Fin.last m))).direction with hu
  have hτ2 : τ * τ = 1 := by
    rcases (abs_eq (a := τ) (b := 1) (by norm_num)).mp hτ with h1 | h1 <;> rw [h1] <;> norm_num
  have hid : e₁ - (σ * τ) • e₂ = (e₁ - σ • u) - (σ * τ) • (e₂ - τ • u) := by
    have h : (e₁ - σ • u) - (σ * τ) • (e₂ - τ • u)
        = e₁ - (σ * τ) • e₂ + (σ * (τ * τ) - σ) • u := by module
    rw [h, hτ2]
    simp
  have habs : |σ * τ| = 1 := by rw [abs_mul, hσ, hτ]; norm_num
  have hle : ‖e₁ - (σ * τ) • e₂‖ ≤ 1 / 2 := by
    rw [hid]
    calc ‖(e₁ - σ • u) - (σ * τ) • (e₂ - τ • u)‖
        ≤ ‖e₁ - σ • u‖ + ‖(σ * τ) • (e₂ - τ • u)‖ := norm_sub_le _ _
      _ = ‖e₁ - σ • u‖ + ‖e₂ - τ • u‖ := by
          rw [norm_smul, Real.norm_eq_abs, habs, one_mul]
      _ ≤ 1 / 4 + 1 / 4 := by
          have h1 : ‖e₁ - σ • u‖ ≤ 1 / 4 := by simpa [hu] using hσle
          have h2 : ‖e₂ - τ • u‖ ≤ 1 / 4 := by simpa [hu] using hτle
          linarith
      _ = 1 / 2 := by norm_num
  have := one_lt_norm_sub_smul norm_e₁ norm_e₂ inner_e₁_e₂ habs
  linarith

open scoped Classical in
/-- **THE IMPOSSIBILITY.**  For every grid length `N`, every dilation factor `K ≥ 0` and every
constant `C` with `C³ < m + 1`, the bush-plus-transverse family admits **no** loose uniform
structure.

The three loose brackets fight each other on this family.  `dir_close_tube_assign` at the coarse
scale `ρ₀ = 1` isolates the transverse member in a node of its own, so its class is a singleton
and `le_card_class` gives `branchingN 0 ≤ C`; `boundedOverlapDil`, tested against the coarse node
that contains the entire family, caps the number of nodes in use by `C`; and `card_class_le` then
caps every class by `C · branchingN 0 ≤ C²`.  Summing the classes over the at most `C` nodes
gives `m + 1 ≤ C³`.

This is GWZ's own reason for refining (`gwz.txt` l.191-193 produces uniformity on a `⪆1`
**subset**, never on the whole family), rendered as a compiler fact. -/
theorem not_nonempty_looseUniformTubeSet_bush {δ : NNReal} (hδ : (δ : ℝ) ≤ 1 / 4)
    (m N : ℕ) {K : ℝ} (hK : 0 ≤ K) (C : NNReal) (hm : C ^ 3 < ((m + 1 : ℕ) : NNReal)) :
    ¬ Nonempty (LooseUniformTubeSet (Finset.univ : Finset (Fin (m + 1))) (bT δ m) N K C) := by
  rintro ⟨𝒰⟩
  classical
  set asg : Fin (m + 1) → Fin (m + 1) := 𝒰.cover.assign 0 with hasg
  set l : Fin (m + 1) := Fin.last m with hl
  -- the transverse member's class is the singleton `{l}`
  have hclass : Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg (asg l) = {l} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · simp [Tube.coverClass]
    · intro i hi
      simp only [Tube.coverClass, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hne
      have hlt : (i : ℕ) < m := by
        have h1 : (i : ℕ) < m + 1 := i.isLt
        have h2 : (i : ℕ) ≠ m := by
          intro h; exact hne (Fin.ext (by simpa [hl] using h))
        omega
      exact dir_sep 𝒰 hlt hi
  have hjl : asg l ∈ 𝒰.cover.indexSet 0 :=
    𝒰.cover.assign_mem 0 (Nat.zero_le N) l (Finset.mem_univ l)
  -- hence the branching number is at most `C`
  have hbr : 𝒰.branchingN 0 ≤ C := by
    have h := 𝒰.le_card_class 0 (Nat.zero_le N) (asg l) hjl
    rw [hasg] at hclass
    rw [hclass] at h
    simpa using h
  -- hence every class has at most `C²` members
  have hcl : ∀ j ∈ 𝒰.cover.indexSet 0,
      ((Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg j).card : NNReal) ≤ C * C := by
    intro j hj
    have h := 𝒰.card_class_le 0 (Nat.zero_le N) j hj
    calc ((Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg j).card : NNReal)
        ≤ C * 𝒰.branchingN 0 := h
      _ ≤ C * C := by gcongr
  -- and at most `C` nodes are in use at all
  set V : Tube (Tube.gridScale δ N 0) E3 := bushTube (Tube.gridScale δ N 0) 0 e₁ norm_e₁ 0 with hV
  have hbo := 𝒰.boundedOverlapDil 0 (Nat.zero_le N) V
  suffices H : ∀ J : Finset (Fin (m + 1)), (J.card : NNReal) ≤ C →
      (∀ j, j ∈ J ↔ (j ∈ 𝒰.cover.indexSet 0 ∧ ∃ i, 𝒰.cover.assign 0 i = j ∧
        (bT δ m i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V (K + 4))) → False by
    exact H _ hbo (fun j => by simp [Finset.mem_filter])
  intro J hJC hJmem
  have hsub : (Finset.univ : Finset (Fin (m + 1)))
      ⊆ J.biUnion (fun j => Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg j) := by
    intro i _
    refine Finset.mem_biUnion.mpr ⟨asg i, ?_, ?_⟩
    · exact (hJmem (asg i)).mpr ⟨𝒰.cover.assign_mem 0 (Nat.zero_le N) i (Finset.mem_univ i),
        i, rfl, bT_le_dilate_node hδ m N i (by linarith)⟩
    · simp [Tube.coverClass]
  have hcard : (m + 1 : ℕ)
      ≤ ∑ j ∈ J, (Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg j).card := by
    calc (m + 1 : ℕ) = (Finset.univ : Finset (Fin (m + 1))).card := by simp
      _ ≤ (J.biUnion (fun j => Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg j)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ j ∈ J, (Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg j).card :=
          Finset.card_biUnion_le
  have hfinal : ((m + 1 : ℕ) : NNReal) ≤ C ^ 3 := by
    have h1 : ((m + 1 : ℕ) : NNReal)
        ≤ ∑ j ∈ J,
            ((Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg j).card : NNReal) := by
      calc ((m + 1 : ℕ) : NNReal)
          ≤ ((∑ j ∈ J, (Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg j).card : ℕ)
              : NNReal) := by exact_mod_cast hcard
        _ = _ := by push_cast; rfl
    have h2 : ∑ j ∈ J,
        ((Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asg j).card : NNReal)
        ≤ ∑ _j ∈ J, C * C :=
      Finset.sum_le_sum (fun j hj => hcl j ((hJmem j).mp hj).1)
    have h3 : ∑ _j ∈ J, C * C = (J.card : NNReal) * (C * C) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    calc ((m + 1 : ℕ) : NNReal) ≤ (J.card : NNReal) * (C * C) := by rw [← h3]; exact h1.trans h2
      _ ≤ C * (C * C) := by gcongr
      _ = C ^ 3 := by ring
  exact absurd hfinal (not_le.mpr hm)

/-! ### The same family carries the EXACT Definition-2.2 datum -/

lemma gridScale_zero_len (δ : NNReal) (k : ℕ) : Tube.gridScale δ 0 k = 1 := by
  simp [Tube.gridScale]

lemma mem_segment_bT {δ : NNReal} (m : ℕ) (i : Fin (m + 1)) :
    (0 : E3) ∈ segment ℝ (bT δ m i).x (bT δ m i).y := by
  rw [bT]
  split
  · exact mem_segment_bushTube δ 0 e₁ norm_e₁ (by
      have := bOff_abs_le m i; linarith)
  · exact mem_segment_bushTube δ 0 e₂ norm_e₂ (by norm_num)

/-- The shaded family: the same tubes, each shaded by the ball about their common point, which
has positive volume for `δ > 0`. -/
noncomputable def bV (δ : NNReal) (m : ℕ) (i : Fin (m + 1)) : ShadedTube δ E3 where
  toTube := bT δ m i
  shade := Metric.closedBall 0 (δ : ℝ)
  measurableSet_shade := measurableSet_closedBall
  shade_subset := (bT δ m i).closedBall_subset_carrier_of_mem_segment (mem_segment_bT m i)

@[simp] lemma bV_toTube (δ : NNReal) (m : ℕ) (i : Fin (m + 1)) :
    (bV δ m i).toTube = bT δ m i := rfl

@[simp] lemma bV_shade (δ : NNReal) (m : ℕ) (i : Fin (m + 1)) :
    (bV δ m i).shade = Metric.closedBall 0 (δ : ℝ) := rfl

/-- The shades are nonempty, and of positive volume once `δ > 0`: the exact bundle below is not
supported on a null set. -/
lemma volume_bV_shade_pos {δ : NNReal} (hδ : 0 < δ) (m : ℕ) (i : Fin (m + 1)) :
    0 < volume (bV δ m i).shade := by
  rw [bV_shade]
  exact measure_closedBall_pos _ _ (by exact_mod_cast hδ)

/-- The exact one-node cover of the family, at grid length `0` (where every grid scale is `1`). -/
noncomputable def exactCover (δ : NNReal) (hδ : (δ : ℝ) ≤ 1 / 4) (m : ℕ) :
    Tube.GridCoverSystem (Finset.univ : Finset (Fin (m + 1))) (bT δ m) 0 where
  indexSet := fun _ => {0}
  assign := fun _ _ => 0
  tube := fun k _ => bushTube (Tube.gridScale δ 0 k) 0 e₁ norm_e₁ 0
  assign_mem := fun k _ i _ => Finset.mem_singleton_self 0
  le_tube_assign := by
    intro k hk i _ z hz
    refine closedBall_subset_bushTube_carrier (Tube.gridScale δ 0 k) e₁ norm_e₁ (by norm_num) ?_
    rw [gridScale_zero_len]
    simpa using bT_carrier_subset hδ m i hz
  nested := by intro k hk; omega
  tube_nested := by intro k hk; omega

/-- The exact Definition-2.1 bundle on the family, at the constant `1`. -/
noncomputable def exactUniform (δ : NNReal) (hδ : (δ : ℝ) ≤ 1 / 4) (m : ℕ) :
    Tube.UniformTubeSet (Finset.univ : Finset (Fin (m + 1))) (bT δ m) 0 1 where
  cover := exactCover δ hδ m
  branchingN := fun _ => ((m + 1 : ℕ) : NNReal)
  tube_injOn := by
    intro k hk a ha b hb _
    have ha0 : a = 0 := by simpa [exactCover] using ha
    have hb0 : b = 0 := by simpa [exactCover] using hb
    rw [ha0, hb0]
  boundedOverlap := by
    intro k hk W
    suffices H : ∀ t : Finset (Fin (m + 1)), t ⊆ (exactCover δ hδ m).indexSet k →
        (t.card : NNReal) ≤ 1 by
      refine H _ ?_
      intro j hj
      simp only [Finset.mem_filter] at hj
      exact hj.1
    intro t ht
    have h1 : t.card ≤ 1 := by
      calc t.card ≤ ((exactCover δ hδ m).indexSet k).card := Finset.card_le_card ht
        _ = 1 := by simp [exactCover]
    exact_mod_cast h1
  card_class_le := by
    intro k hk j hj
    have huniv : Tube.coverClass (Finset.univ : Finset (Fin (m + 1)))
        ((exactCover δ hδ m).assign k) j = Finset.univ := by
      have hj0 : j = 0 := by simpa [exactCover] using hj
      subst hj0
      simp [Tube.coverClass, exactCover]
    rw [huniv]
    simp
  le_card_class := by
    intro k hk j hj
    have huniv : Tube.coverClass (Finset.univ : Finset (Fin (m + 1)))
        ((exactCover δ hδ m).assign k) j = Finset.univ := by
      have hj0 : j = 0 := by simpa [exactCover] using hj
      subst hj0
      simp [Tube.coverClass, exactCover]
    rw [huniv]
    simp

lemma coverClass_const_eq_univ (m : ℕ) {asgn : Fin (m + 1) → Fin (m + 1)}
    (hasgn : ∀ i, asgn i = 0) :
    Tube.coverClass (Finset.univ : Finset (Fin (m + 1))) asgn 0 = Finset.univ := by
  refine Finset.eq_univ_iff_forall.mpr ?_
  intro i
  simp only [Tube.coverClass, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hasgn i

lemma shadeClass_const_eq_univ (δ : NNReal) (m : ℕ) {asgn : Fin (m + 1) → Fin (m + 1)}
    (hasgn : ∀ i, asgn i = 0) {x : E3} (hx : x ∈ Metric.closedBall (0 : E3) (δ : ℝ)) :
    ShadedTube.shadeClass (Finset.univ : Finset (Fin (m + 1))) (bV δ m) asgn 0 x
      = Finset.univ := by
  refine Finset.eq_univ_iff_forall.mpr ?_
  intro i
  simp only [ShadedTube.shadeClass, Finset.mem_filter, Tube.coverClass, Finset.mem_univ,
    true_and]
  exact ⟨hasgn i, by simpa using hx⟩

/-- **The exact GWZ Definition-2.2 datum on the bush-plus-transverse family, at the constant
`1`.**  This is the shape of `Kakeya.VeryNotSticky.uniform`, the only uniformity hypothesis a
configuration carries. -/
noncomputable def exactShaded (δ : NNReal) (hδ : (δ : ℝ) ≤ 1 / 4) (m : ℕ) :
    ShadedTube.ShadedUniformTubeSet (Finset.univ : Finset (Fin (m + 1))) (bV δ m) 0 1 where
  tubeUniform := exactUniform δ hδ m
  branchingN := fun _ => ((m + 1 : ℕ) : NNReal)
  localN := fun _ _ => ((m + 1 : ℕ) : NNReal)
  card_shadeClass_le := by
    intro x hx k hk i _ hxi
    have hxb : x ∈ Metric.closedBall (0 : E3) (δ : ℝ) := by simpa using hxi
    have hassign : ∀ i', (exactUniform δ hδ m).cover.assign k i' = 0 := fun _ => rfl
    rw [hassign i, shadeClass_const_eq_univ δ m hassign hxb]
    simp
  le_card_shadeClass := by
    intro x hx k hk i _ hxi
    have hxb : x ∈ Metric.closedBall (0 : E3) (δ : ℝ) := by simpa using hxi
    have hassign : ∀ i', (exactUniform δ hδ m).cover.assign k i' = 0 := fun _ => rfl
    rw [hassign i, shadeClass_const_eq_univ δ m hassign hxb]
    simp
  branchingN_le := by intro x hx k hk; simp
  le_branchingN := by intro x hx k hk; simp

/-- **One family, both sides, at grid length `0`.**  At `N = 0` the family carries the exact GWZ
Definition-2.2 datum at the constant `1` and admits **no** loose datum, at any dilation factor
`K ≥ 0` and any constant `C` with `C³ < m + 1`.

Read the grid length: **both** occurrences below are `0`, the degenerate one-node grid on which
`Kakeya.LooseUniform.Producer.gridScale_zero_len` makes every scale `1`.  This is therefore
*not* a statement that the exact datum fails to produce the loose one at the Section-9 grid
length: no family holding the exact datum at `N = Tube.ssfGridLen δ` and failing the loose one
is exhibited in this file ((a)).  The bracket that fails here is
`Kakeya.LooseUniform.LooseGridCoverSystem.dir_close_tube_assign` alone — `hbo` holds on this
family at `K = 4`, `C = 1` ((b)) — and it fails only at `k = 0`. -/
theorem exact_datum_does_not_produce_loose {δ : NNReal} (hδ : (δ : ℝ) ≤ 1 / 4) (m : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (C : NNReal) (hm : C ^ 3 < ((m + 1 : ℕ) : NNReal)) :
    Nonempty (ShadedTube.ShadedUniformTubeSet (Finset.univ : Finset (Fin (m + 1)))
        (bV δ m) 0 1) ∧
      ¬ Nonempty (LooseShadedUniformTubeSet (Finset.univ : Finset (Fin (m + 1)))
        (bV δ m) 0 K C) := by
  refine ⟨⟨exactShaded δ hδ m⟩, ?_⟩
  rintro ⟨𝒱⟩
  exact not_nonempty_looseUniformTubeSet_bush hδ m 0 hK C hm ⟨𝒱.tubeUniform⟩

/-- **At the Section-9 grid length and the Section-9 dilation factor.**  The same failure of the
loose bundle, stated at `N = Tube.ssfGridLen δ` and `K = 4`.

This is the *loose* side only: no exact-datum companion accompanies it at this `N`, so it does
not compose with `exact_datum_does_not_produce_loose` into a producer obstruction at the
Section-9 grid length ((a)). -/
theorem not_nonempty_looseShaded_ssfGridLen {δ : NNReal} (hδ : (δ : ℝ) ≤ 1 / 4) (m : ℕ)
    (C : NNReal) (hm : C ^ 3 < ((m + 1 : ℕ) : NNReal)) :
    ¬ Nonempty (LooseShadedUniformTubeSet (Finset.univ : Finset (Fin (m + 1)))
      (bV δ m) (Tube.ssfGridLen δ) 4 C) := by
  rintro ⟨𝒱⟩
  exact not_nonempty_looseUniformTubeSet_bush hδ m (Tube.ssfGridLen δ) (by norm_num) C hm
    ⟨𝒱.tubeUniform⟩

end Kakeya.LooseUniform.Producer

end
