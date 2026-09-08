/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsFibreCountLoose

/-!
# The joint (product) refinement: what it preserves, and the compiled obstruction

This file measures that recommendation.

The measurement is asymmetric, and this file compiles both halves.

* **The exact brackets DO survive** (`Kakeya.JointRefine.card_exactClass_le_of_joint`,
  `le_card_exactClass_of_joint`, fed by `card_image_assign_le_of_common_node`): an exact class
  is a union of joint classes, and the number of joint classes inside it is bounded by the
  *loose* datum's own Definition 2.1(ii), read at `V :=` the exact node itself — a `ρ_k`-tube,
  exactly the type `LooseUniform.LooseUniformTubeSet.boundedOverlapDil` quantifies over, and the
  exact containment `T i ≤ V` upgrades to `T i ≤ dilate V (K+4)` by `Tube.subset_dilate`.  So an
  exact class over the jointly pruned family has cardinality in `[N k, C · 2 N k]`.

* **The loose brackets DO NOT survive**, and the witness is already in the tree:
  `Kakeya.LooseUniform.bush_obstruction`.  A single loose class can contain `n ≈ 1/(6 ρ_k)`
  members lying in **pairwise distinct** exact nodes (`Kakeya.JointRefine.bush_joint_overlap`),
  so it is a union of `n` joint classes, while a loose class elsewhere may be a single joint
  class.  Two classes whose cardinalities differ by a factor `n` force
  `n ≤ C · C` (`Kakeya.JointRefine.bracket_forces_le_sq`), i.e. a hierarchy constant
  `C ≥ √n ≈ δ^{-Θ(1)}`, far above the `δ^{-η}` every Section-9 consumer needs.

The same computation refutes the other way of typing the loose datum over joint classes — index
the loose cover by joint classes instead of by loose nodes: then the classes *are* the joint
classes and are bracketed, but `boundedOverlapDil` fails, because all `n` bush members lie in
`Kakeya.Tube.dilate V 8` and belong to `n` distinct joint classes
(`Kakeya.JointRefine.bush_joint_overlap` again).

Nothing here is a refutation of conjunct 6, and nothing here discharges an obligation: it is a
measurement of one proposed *route*.  The honest reading is .
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

namespace JointRefine

variable {ι : Type*}

/-! ### The exact brackets survive the product pruning -/

/-- **Lower bracket, transported.**  If the joint assignment refines the exact one, then an exact
class contains the joint class of any of its members, so any lower bound on joint classes is a
lower bound on exact classes. -/
theorem le_card_exactClass_of_joint {s : Finset ι} {ea ja : ι → ι}
    (href : ∀ i ∈ s, ∀ j ∈ s, ja i = ja j → ea i = ea j)
    {Nk : ℕ} {i : ι} (hi : i ∈ s)
    (hlow : Nk ≤ (Tube.coverClass s ja (ja i)).card) :
    Nk ≤ (Tube.coverClass s ea (ea i)).card := by
  classical
  refine hlow.trans (Finset.card_le_card ?_)
  intro j hj
  simp only [Tube.coverClass, Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, href j hj.1 i hi hj.2⟩

/-- **Upper bracket, transported at the cost of the cross multiplicity.**  If the joint
assignment is exactly the pair `(ea, la)` on `s`, every joint class has at most `Nk` members and
the exact class of `i` meets at most `m` values of `la`, then that exact class has at most
`m * Nk` members. -/
theorem card_exactClass_le_of_joint [DecidableEq ι] {s : Finset ι} {ea la ja : ι → ι}
    (hja : ∀ i ∈ s, ∀ j ∈ s, (ja i = ja j ↔ ea i = ea j ∧ la i = la j))
    {Nk m : ℕ} {i : ι}
    (hhigh : ∀ j ∈ s, (Tube.coverClass s ja (ja j)).card ≤ Nk)
    (hm : ((Tube.coverClass s ea (ea i)).image la).card ≤ m) :
    (Tube.coverClass s ea (ea i)).card ≤ m * Nk := by
  classical
  have hcard : (Tube.coverClass s ea (ea i)).card =
      ∑ b ∈ (Tube.coverClass s ea (ea i)).image la,
        ((Tube.coverClass s ea (ea i)).filter (fun j => la j = b)).card :=
    Finset.card_eq_sum_card_fiberwise (fun j hj => Finset.mem_image_of_mem la hj)
  have hterm : ∀ b ∈ (Tube.coverClass s ea (ea i)).image la,
      ((Tube.coverClass s ea (ea i)).filter (fun j => la j = b)).card ≤ Nk := by
    intro b hb
    obtain ⟨j₀, hj₀A, hj₀b⟩ := Finset.mem_image.mp hb
    have hj₀' : j₀ ∈ s ∧ ea j₀ = ea i := by
      simpa only [Tube.coverClass, Finset.mem_filter] using hj₀A
    obtain ⟨hj₀s, hj₀e⟩ := hj₀'
    have hsub : (Tube.coverClass s ea (ea i)).filter (fun j => la j = b) ⊆
        Tube.coverClass s ja (ja j₀) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have hjA := hj.1
      have hjA' : j ∈ s ∧ ea j = ea i := by
        simpa only [Tube.coverClass, Finset.mem_filter] using hjA
      obtain ⟨hjs, hje⟩ := hjA'
      simp only [Tube.coverClass, Finset.mem_filter]
      refine ⟨hjs, (hja j hjs j₀ hj₀s).mpr ⟨by rw [hje, hj₀e], by rw [hj.2, hj₀b]⟩⟩
    exact le_trans (Finset.card_le_card hsub) (hhigh j₀ hj₀s)
  calc (Tube.coverClass s ea (ea i)).card
      = ∑ b ∈ (Tube.coverClass s ea (ea i)).image la,
          ((Tube.coverClass s ea (ea i)).filter (fun j => la j = b)).card := hcard
    _ ≤ ∑ _b ∈ (Tube.coverClass s ea (ea i)).image la, Nk := Finset.sum_le_sum hterm
    _ = ((Tube.coverClass s ea (ea i)).image la).card * Nk := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ m * Nk := Nat.mul_le_mul_right _ hm

/-! ### The cross multiplicity is bounded by the LOOSE datum, read at the exact node -/

open LooseUniform in
/-- **The one geometric input of the positive half.**  If every member of `u ⊆ s` sits (exactly)
inside one `ρ_k`-tube `V`, then the loose hierarchy assigns those members to at most `C` distinct
loose nodes.  This is `LooseUniform.LooseUniformTubeSet.boundedOverlapDil` at that very `V`,
using `Tube.subset_dilate` to upgrade `T i ≤ V` to `T i ≤ Kakeya.Tube.dilate V (K+4)`.

Applied with `u :=` an exact class and `V :=` its node, this is the bound `m` that
`Kakeya.JointRefine.card_exactClass_le_of_joint` consumes. -/
theorem card_image_assign_le_of_common_node [DecidableEq ι] {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ LooseUniform.E3} {N : ℕ} {K : ℝ} {C : NNReal}
    (𝒰 : LooseUniform.LooseUniformTubeSet s T N K C) (hK : (1 : ℝ) ≤ K + 4)
    {k : ℕ} (hk : k ≤ N) (V : Tube (Tube.gridScale δ N k) LooseUniform.E3)
    {u : Finset ι} (hu : u ⊆ s)
    (hV : ∀ i ∈ u, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    ((u.image (𝒰.cover.assign k)).card : NNReal) ≤ C := by
  classical
  refine le_trans ?_ (𝒰.boundedOverlapDil k hk V)
  have hsub : u.image (𝒰.cover.assign k) ⊆
      (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s, 𝒰.cover.assign k i = j ∧
        (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V (K + 4)) := by
    intro j hj
    obtain ⟨i, hiu, hij⟩ := Finset.mem_image.mp hj
    refine Finset.mem_filter.mpr ⟨hij ▸ 𝒰.cover.assign_mem k hk i (hu hiu),
      i, hu hiu, hij, ?_⟩
    exact le_trans (hV i hiu) (fun _ hx => Tube.subset_dilate V hK hx)
  exact_mod_cast Finset.card_le_card hsub

/-- **The product assignment types.**  The engine
`Tube.exists_pruned_subset_noroot_notop` demands `assign : ℕ → ι → ι`, so the literal pair
`i ↦ (ea i, la i)` does not typecheck; but the pair's *fibres* are the fibres of a map `ι → ι`,
namely the choice of a representative of the joint cell.  So the obstruction measured below is
about the brackets and not about the typing. -/
theorem exists_joint_assign (s : Finset ι) (ea la : ι → ι) :
    ∃ ja : ι → ι, (∀ i ∈ s, ja i ∈ s) ∧
      ∀ i ∈ s, ∀ j ∈ s, (ja i = ja j ↔ ea i = ea j ∧ la i = la j) := by
  classical
  set cell : ι → Finset ι :=
    fun i => s.filter (fun j => ea j = ea i ∧ la j = la i) with hcell
  refine ⟨fun i => if h : (cell i).Nonempty then h.choose else i, ?_, ?_⟩
  · intro i hi
    have hne : (cell i).Nonempty := ⟨i, by simp [hcell, hi]⟩
    simp only [dif_pos hne]
    have := hne.choose_spec
    simp only [hcell, Finset.mem_filter] at this
    exact this.1
  · intro i hi j hj
    have hnei : (cell i).Nonempty := ⟨i, by simp [hcell, hi]⟩
    have hnej : (cell j).Nonempty := ⟨j, by simp [hcell, hj]⟩
    have hsi := hnei.choose_spec
    have hsj := hnej.choose_spec
    simp only [hcell, Finset.mem_filter] at hsi hsj
    simp only [dif_pos hnei, dif_pos hnej]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [← hsi.2.1, h, hsj.2.1]
      · rw [← hsi.2.2, h, hsj.2.2]
    · rintro ⟨he, hl⟩
      have hcc : cell i = cell j := by
        apply Finset.filter_congr
        intro x _
        simp only [he, hl]
      have hchoose : ∀ (t u : Finset ι) (ht : t.Nonempty) (hu : u.Nonempty),
          t = u → ht.choose = hu.choose := by
        rintro t u ht hu rfl
        rfl
      exact hchoose _ _ hnei hnej hcc

/-- **The positive half, packaged.**  On a family whose *joint* classes at level `k` are banded
in `[Nk, 2 Nk]`, every *exact* class at level `k` is banded in `[Nk, C · 2 Nk]`, where `C` is the
loose datum's own Definition 2.1(ii) constant.  No extra pigeonholing and no new constant: the
cross multiplicity is paid by `Kakeya.JointRefine.card_image_assign_le_of_common_node`. -/
theorem exact_brackets_of_joint_band
    {δ : NNReal} {s : Finset ι} {T : ι → Tube δ LooseUniform.E3} {N : ℕ} {K : ℝ} {C : NNReal}
    (𝒰 : LooseUniform.LooseUniformTubeSet s T N K C) (hK : (1 : ℝ) ≤ K + 4)
    {k : ℕ} (hk : k ≤ N)
    (ea : ι → ι) (node : ι → Tube (Tube.gridScale δ N k) LooseUniform.E3)
    (hnode : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (node (ea i)).toConvexSpaceBody)
    (ja : ι → ι)
    (hja : ∀ i ∈ s, ∀ j ∈ s,
      (ja i = ja j ↔ ea i = ea j ∧ 𝒰.cover.assign k i = 𝒰.cover.assign k j))
    {Nk : ℕ}
    (hlow : ∀ i ∈ s, Nk ≤ (Tube.coverClass s ja (ja i)).card)
    (hhigh : ∀ i ∈ s, (Tube.coverClass s ja (ja i)).card ≤ 2 * Nk)
    {i : ι} (hi : i ∈ s) :
    Nk ≤ (Tube.coverClass s ea (ea i)).card ∧
      ((Tube.coverClass s ea (ea i)).card : NNReal) ≤ C * (2 * Nk) := by
  classical
  have hclass_sub : Tube.coverClass s ea (ea i) ⊆ s := by
    intro j hj
    have hj' : j ∈ s ∧ ea j = ea i := by
      simpa only [Tube.coverClass, Finset.mem_filter] using hj
    exact hj'.1
  have hV : ∀ j ∈ Tube.coverClass s ea (ea i),
      (T j).toConvexSpaceBody ≤ (node (ea i)).toConvexSpaceBody := by
    intro j hj
    have hj' : j ∈ s ∧ ea j = ea i := by
      simpa only [Tube.coverClass, Finset.mem_filter] using hj
    have := hnode j hj'.1
    rwa [hj'.2] at this
  have hm : (((Tube.coverClass s ea (ea i)).image (𝒰.cover.assign k)).card : NNReal) ≤ C :=
    card_image_assign_le_of_common_node 𝒰 hK hk (node (ea i)) hclass_sub hV
  refine ⟨le_card_exactClass_of_joint (fun a ha b hb h => ((hja a ha b hb).mp h).1) hi
      (hlow i hi), ?_⟩
  have hcard := card_exactClass_le_of_joint (s := s) (ea := ea)
    (la := 𝒰.cover.assign k) (ja := ja) hja (Nk := 2 * Nk)
    (m := ((Tube.coverClass s ea (ea i)).image (𝒰.cover.assign k)).card) hhigh le_rfl
  have hcardN : ((Tube.coverClass s ea (ea i)).card : NNReal) ≤
      ((((Tube.coverClass s ea (ea i)).image (𝒰.cover.assign k)).card : ℕ) : NNReal) *
        ((2 * Nk : ℕ) : NNReal) := by
    exact_mod_cast hcard
  refine hcardN.trans ?_
  have : (((2 * Nk : ℕ)) : NNReal) = 2 * (Nk : NNReal) := by push_cast; ring
  rw [this]
  gcongr

/-! ### The loose brackets do NOT survive: the compiled obstruction -/

open LooseUniform in
/-- **The obstruction, from `Kakeya.LooseUniform.bush_obstruction`.**  For every `n` with
`n · sp ≤ 1/2` and `sp > 2ρ` there are `n` unit `δ`-tubes that

* all lie in `Kakeya.Tube.dilate V 8` for a single `ρ`-tube `V`, with `V`'s direction — so a
  loose hierarchy may (and the anchored net does) put all `n` in **one** loose class, and all `n`
  count in the `boundedOverlapDil` filter at `V`;
* lie in **no** common exact `ρ`-tube — so any exact hierarchy puts them in `n` **distinct**
  classes, hence the product assignment puts them in `n` distinct joint classes.

Therefore one loose class is a union of `n` joint classes.  With `sp := 3ρ` one may take
`n = ⌊1/(6ρ)⌋`. -/
theorem bush_joint_overlap {δ ρ : NNReal} (hδρ : 4 * (δ : ℝ) ≤ ρ)
    (x v : LooseUniform.E3) (hv : ‖v‖ = 1) (n : ℕ) {sp : ℝ}
    (hsp : 2 * (ρ : ℝ) < sp) (hn : (n : ℝ) * sp ≤ 1 / 2) :
    ∃ (T : Fin n → Tube δ LooseUniform.E3) (V : Tube ρ LooseUniform.E3),
      (∀ i, (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8) ∧
      (∀ i, (T i).direction = V.direction) ∧
      (∀ i j, i ≠ j → ∀ W : Tube ρ LooseUniform.E3,
        (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody →
        ¬ (T j).toConvexSpaceBody ≤ W.toConvexSpaceBody) := by
  obtain ⟨T, V, _hx, hdir, hsep, hdil⟩ :=
    LooseUniform.bush_obstruction hδρ x v hv n hsp hn
  refine ⟨T, V, fun i => le_trans (hdil i) ?_, hdir, fun i j hij W hWi hWj => ?_⟩
  · exact Kakeya.VeryNotSticky.dilate_le_dilate_of_ratio_le V (by norm_num) (by norm_num)
  · exact hsep i j hij ⟨W, hWi, hWj⟩

/-- **The exact nodes of the bush are pairwise distinct.**  Restated from
`Kakeya.JointRefine.bush_joint_overlap`: if each member is assigned to some exact node containing
it, distinct members get distinct nodes. -/
theorem exactNode_injective_of_sep {δ ρ : NNReal} {n : ℕ}
    {T : Fin n → Tube δ LooseUniform.E3}
    (hsep : ∀ i j, i ≠ j → ∀ W : Tube ρ LooseUniform.E3,
      (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody →
      ¬ (T j).toConvexSpaceBody ≤ W.toConvexSpaceBody)
    (node : Fin n → Tube ρ LooseUniform.E3)
    (hnode : ∀ i, (T i).toConvexSpaceBody ≤ (node i).toConvexSpaceBody) :
    Function.Injective node := by
  intro i j hij
  by_contra hne
  exact hsep i j hne (node i) (hnode i) (hij ▸ hnode j)

/-- **What a class-size disparity costs.**  Definition 2.1(iii) reads
`|class| ≤ C · branchingN` and `branchingN ≤ C · |class|` at *every* node of the level.  A level
carrying one class of `n` members and one class of a single member therefore forces `n ≤ C²`. -/
theorem bracket_forces_le_sq {C B : NNReal} {n : ℕ}
    (h1 : (n : NNReal) ≤ C * B) (h2 : B ≤ C * 1) : (n : NNReal) ≤ C * C := by
  have hcc : C * B ≤ C * (C * 1) := by gcongr
  simpa using h1.trans hcc

/-- **The disparity is realised by the bush.**  With the exact assignment separating the `n`
members and the loose assignment collapsing them, the loose class has `n` members and each joint
(= exact) class has one.  Purely combinatorial; the geometry that makes both assignments legal is
`Kakeya.JointRefine.bush_joint_overlap`. -/
theorem bush_class_disparity (n : ℕ) :
    (Tube.coverClass (Finset.univ : Finset (Fin (n + 1))) (fun _ => (0 : Fin (n + 1)))
        0).card = n + 1 ∧
      ∀ i : Fin (n + 1),
        (Tube.coverClass (Finset.univ : Finset (Fin (n + 1))) id i).card = 1 := by
  classical
  constructor
  · simp [Tube.coverClass]
  · intro i
    have : (Tube.coverClass (Finset.univ : Finset (Fin (n + 1))) id i) = {i} := by
      ext j
      simp [Tube.coverClass, eq_comm]
    rw [this, Finset.card_singleton]

end JointRefine

end Kakeya

end
