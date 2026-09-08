/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6CoarseFactorisation
public import Mathlib.Combinatorics.Hall.Basic

/-!
# The coarse tube decomposition, with the fibre lower bound discharged

`Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale`
(`Kakeya/DimensionThree/Plank/Section6CoarseFactorisation.lean`) builds the Section-6 coarse tube
decomposition out of `Tube.IsUniformAtScale`, but it leaves one clause as a hypothesis
`hlb`, and its docstring says of it: *"Supplying `hlb` requires a bounded-overlap count for the
parent family; it is not invented here."*

`hlb` is the fibre **lower** bound `N / C ≤ |{i ∈ q | assign i = k}|`.  The reason it is not free is
recorded in `Kakeya.Section6CoarseTubeDecomposition.fibre_subset_filter_of_uniformAtScale`:
uniformity controls the *containment* sets `F_k = {i ∈ q | T i ≤ T_ρ k}`, while a decomposition
needs a **function** `assign`, and the fibres of a chosen function are only subsets of the
containment sets.  A parent all of whose leaves happen to choose some other parent has an empty
fibre.

This file supplies `hlb` by choosing the assignment rather than accepting an arbitrary one.  The
tool is **Hall's marriage theorem** (`Finset.all_card_le_biUnion_card_iff_exists_injective`), and
the bounded-overlap count the docstring asks for is exactly the one the structure already carries:
`Tube.IsUniformAtScale.parents_containing_tube_card_le` says each leaf lies under at most `C`
parents.  Double counting then gives, for every `P ⊆ 𝕋_ρ`,

`|P| · N ≤ C · ∑_{k ∈ P} |F_k| ≤ C² · |⋃_{k ∈ P} F_k|`,

which is Hall's condition for the bipartite system that asks each parent for
`t := ⌊N / C²⌋` distinct leaves (`Kakeya.hallTarget`).  Hall's theorem returns an injection
`f : 𝕋_ρ × Fin t → 𝕋` with `f (k, l) ∈ F_k`; declaring `assign (f (k, l)) := k` and falling back to
`Kakeya.uniformCoarseAssign` elsewhere gives `Kakeya.hallAssign`, whose fibres satisfy
`t ≤ |fibre k| ≤ |F_k| ≤ C · N` for **every** parent `k`.

## What it costs, and the one hypothesis it needs

The output is `Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScaleHall`, over the **full**
parent set `U.parent` (not the image of a chosen assignment), with fibre comparability constant
`Cfib = 2 C²` around the common size `m = N`.  Since `C ≤ δ ^ (-η)` in every Section-6 consumer,
`2 C² ≤ δ ^ (-3η)` once `δ` is small, so the constant stays inside the sub-polynomial budget.

The one hypothesis beyond `Tube.IsUniformAtScale` itself is the **branching floor**
`C ^ 2 ≤ U.branchingN`, and it is not removable: with `N ≤ C` the datum admits `C` distinct parent
`ρ`-tubes that all contain the *same* single leaf, and then no function `assign` can give every
parent a nonempty fibre, so `Kakeya.Section6CoarseTubeDecomposition.fibre_nonempty` fails over
`U.parent` for **every** assignment, not merely for the chosen one.  What the floor buys is exactly
`1 ≤ t`.  See `Kakeya.hallTarget_pos_iff_sq_le_branchingN`.

The second hypothesis, `δ ≤ ρ`, is what lets a leaf be tested against its own rescaling in
`Tube.IsUniformAtScale.parents_containing_tube_card_le`; it is available in every Section-6
setting, where `ρ` is a coarse scale above `δ`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

variable {ι : Type*} {δ : ℝ≥0} {q : Finset ι}
  {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}

/-! ### The containment sets of the parent family -/

open Classical in
/-- **The containment set of a parent**: the leaves of `q` that lie inside the parent tube indexed
by `j`.  This is the set `Tube.IsUniformAtScale` controls two-sidedly, and the set whose
subsets the fibres of any chosen assignment are. -/
def parentContainment (U : Tube.IsUniformAtScale q Tt ρ C) (j : ι) : Finset ι :=
  {i ∈ q | (Tt i).toConvexSpaceBody ≤ (U.parentTube j).toConvexSpaceBody}

theorem mem_parentContainment {U : Tube.IsUniformAtScale q Tt ρ C} {j i : ι} :
    i ∈ parentContainment U j ↔
      i ∈ q ∧ (Tt i).toConvexSpaceBody ≤ (U.parentTube j).toConvexSpaceBody := by
  classical
  simp [parentContainment, Finset.mem_filter]

theorem parentContainment_subset (U : Tube.IsUniformAtScale q Tt ρ C) (j : ι) :
    parentContainment U j ⊆ q := fun _ hi => (mem_parentContainment.mp hi).1

theorem branchingN_le_mul_card_parentContainment (U : Tube.IsUniformAtScale q Tt ρ C) {j : ι}
    (hj : j ∈ U.parent) : U.branchingN ≤ C * ((parentContainment U j).card : ℝ≥0) := by
  classical
  simpa [parentContainment] using U.le_mul_card_filter hj

theorem card_parentContainment_le (U : Tube.IsUniformAtScale q Tt ρ C) {j : ι}
    (hj : j ∈ U.parent) : ((parentContainment U j).card : ℝ≥0) ≤ C * U.branchingN := by
  classical
  simpa [parentContainment] using U.card_filter_le hj

open Classical in
/-- **The bounded-overlap count, in containment form**: a leaf of `q` lies in at most `C` of the
parents.  This is `Tube.IsUniformAtScale.parents_containing_tube_card_le` applied to the leaf
itself, and it is the "bounded-overlap count for the parent family" that
`Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale` asks for. -/
theorem card_parents_containing_le (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ)
    {i : ι} (hi : i ∈ q) {P : Finset ι} (hP : P ⊆ U.parent) :
    (((P.filter (fun j => i ∈ parentContainment U j)).card : ℝ≥0)) ≤ C := by
  have hsub : P.filter (fun j => i ∈ parentContainment U j)
      ⊆ U.parent.filter (fun j =>
        (Tt i).toConvexSpaceBody ≤ (U.parentTube j).toConvexSpaceBody) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hP hj.1, (mem_parentContainment.mp hj.2).2⟩
  refine le_trans ?_ (U.parents_containing_tube_card_le hδρ (Tt i) hi (le_refl _))
  exact_mod_cast Finset.card_le_card hsub

open Classical in
/-- **Double counting.**  The total containment count over a set of parents is at most `C` times the
number of leaves those parents see between them. -/
theorem sum_card_parentContainment_le (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ)
    {P : Finset ι} (hP : P ⊆ U.parent) :
    (∑ j ∈ P, ((parentContainment U j).card : ℝ≥0))
      ≤ C * (((P.biUnion (parentContainment U)).card : ℝ≥0)) := by
  classical
  set B : Finset ι := P.biUnion (parentContainment U) with hB
  have hFB : ∀ j ∈ P, parentContainment U j = B.filter (fun i => i ∈ parentContainment U j) := by
    intro j hj
    ext i
    simp only [Finset.mem_filter, hB, Finset.mem_biUnion]
    exact ⟨fun h => ⟨⟨j, hj, h⟩, h⟩, fun h => h.2⟩
  have hnat : (∑ j ∈ P, (parentContainment U j).card)
      = ∑ i ∈ B, (P.filter (fun j => i ∈ parentContainment U j)).card := by
    calc (∑ j ∈ P, (parentContainment U j).card)
        = ∑ j ∈ P, (B.filter (fun i => i ∈ parentContainment U j)).card := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← hFB j hj]
      _ = ∑ j ∈ P, ∑ i ∈ B, (if i ∈ parentContainment U j then 1 else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.card_filter]
      _ = ∑ i ∈ B, ∑ j ∈ P, (if i ∈ parentContainment U j then 1 else 0) := Finset.sum_comm
      _ = ∑ i ∈ B, (P.filter (fun j => i ∈ parentContainment U j)).card := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.card_filter]
  have hcast : (∑ j ∈ P, ((parentContainment U j).card : ℝ≥0))
      = ∑ i ∈ B, ((P.filter (fun j => i ∈ parentContainment U j)).card : ℝ≥0) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ≥0)) hnat
  rw [hcast]
  calc ∑ i ∈ B, ((P.filter (fun j => i ∈ parentContainment U j)).card : ℝ≥0)
      ≤ ∑ _i ∈ B, C := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hiq : i ∈ q := by
          rw [hB, Finset.mem_biUnion] at hi
          obtain ⟨j, _, hij⟩ := hi
          exact (mem_parentContainment.mp hij).1
        exact card_parents_containing_le U hδρ hiq hP
    _ = C * (B.card : ℝ≥0) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

open Classical in
/-- **The expansion bound behind Hall's condition.**  Any `k` parents see at least `k · N / C²`
leaves between them. -/
theorem card_mul_branchingN_le (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ)
    {P : Finset ι} (hP : P ⊆ U.parent) :
    (P.card : ℝ≥0) * U.branchingN
      ≤ C ^ 2 * (((P.biUnion (parentContainment U)).card : ℝ≥0)) := by
  classical
  have hstep : (P.card : ℝ≥0) * U.branchingN
      ≤ C * ∑ j ∈ P, ((parentContainment U j).card : ℝ≥0) := by
    rw [Finset.mul_sum]
    calc (P.card : ℝ≥0) * U.branchingN = ∑ _j ∈ P, U.branchingN := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ P, C * ((parentContainment U j).card : ℝ≥0) :=
          Finset.sum_le_sum fun j hj => branchingN_le_mul_card_parentContainment U (hP hj)
  refine hstep.trans ?_
  calc C * ∑ j ∈ P, ((parentContainment U j).card : ℝ≥0)
      ≤ C * (C * (((P.biUnion (parentContainment U)).card : ℝ≥0))) := by
        gcongr
        exact sum_card_parentContainment_le U hδρ hP
    _ = C ^ 2 * (((P.biUnion (parentContainment U)).card : ℝ≥0)) := by ring

/-! ### The Hall matching -/

/-- **The guaranteed fibre size**: the number of leaves Hall's theorem can reserve for every single
parent, `⌊N / C²⌋`. -/
def hallTarget (U : Tube.IsUniformAtScale q Tt ρ C) : ℕ := ⌊U.branchingN / C ^ 2⌋₊

/-- The branching floor `C² ≤ N` is exactly what makes the Hall target positive. -/
theorem hallTarget_pos_iff_sq_le_branchingN (U : Tube.IsUniformAtScale q Tt ρ C)
    (hC : 1 ≤ C) : 1 ≤ hallTarget U ↔ C ^ 2 ≤ U.branchingN := by
  have hC2 : (0 : ℝ≥0) < C ^ 2 := by positivity
  rw [hallTarget, Nat.one_le_floor_iff, le_div_iff₀ hC2, one_mul]

open Classical in
/-- **Hall's condition holds, so every parent can be given `hallTarget U` private leaves.** -/
theorem exists_hall_matching (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ) (hC : 1 ≤ C) :
    ∃ f : {j : ι // j ∈ U.parent} × Fin (hallTarget U) → ι,
      Function.Injective f ∧ ∀ p, f p ∈ parentContainment U p.1.1 := by
  classical
  have hC2 : (0 : ℝ≥0) < C ^ 2 := by positivity
  refine (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun p : {j : ι // j ∈ U.parent} × Fin (hallTarget U) => parentContainment U p.1.1)).mp ?_
  intro S
  set P' : Finset {j : ι // j ∈ U.parent} := S.image Prod.fst with hP'
  set P : Finset ι := P'.image Subtype.val with hPdef
  have hPsub : P ⊆ U.parent := by
    intro j hj
    rw [hPdef, Finset.mem_image] at hj
    obtain ⟨y, _, rfl⟩ := hj
    exact y.2
  have hbi : S.biUnion (fun p => parentContainment U p.1.1)
      = P.biUnion (parentContainment U) := by
    rw [hPdef, hP', Finset.image_image, Finset.image_biUnion]
    rfl
  have hScard : S.card ≤ P'.card * hallTarget U := by
    have hsub : S ⊆ P' ×ˢ (Finset.univ : Finset (Fin (hallTarget U))) := by
      intro p hp
      rw [Finset.mem_product]
      exact ⟨Finset.mem_image_of_mem Prod.fst hp, Finset.mem_univ _⟩
    calc S.card ≤ (P' ×ˢ (Finset.univ : Finset (Fin (hallTarget U)))).card :=
          Finset.card_le_card hsub
      _ = P'.card * hallTarget U := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hPcard : P.card = P'.card := by
    rw [hPdef]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hexp : ((P'.card * hallTarget U : ℕ) : ℝ≥0)
      ≤ ((P.biUnion (parentContainment U)).card : ℝ≥0) := by
    have hmain := card_mul_branchingN_le U hδρ hPsub
    have hle : ((hallTarget U : ℕ) : ℝ≥0) ≤ U.branchingN / C ^ 2 := Nat.floor_le (by positivity)
    have h1 : (P.card : ℝ≥0) * ((hallTarget U : ℕ) : ℝ≥0)
        ≤ (P.card : ℝ≥0) * (U.branchingN / C ^ 2) := by gcongr
    have h2 : (P.card : ℝ≥0) * (U.branchingN / C ^ 2)
        ≤ ((P.biUnion (parentContainment U)).card : ℝ≥0) := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ hC2]
      calc (P.card : ℝ≥0) * U.branchingN
          ≤ C ^ 2 * (((P.biUnion (parentContainment U)).card : ℝ≥0)) := hmain
        _ = ((P.biUnion (parentContainment U)).card : ℝ≥0) * C ^ 2 := by ring
    have h3 := h1.trans h2
    rw [hPcard] at h3
    push_cast
    exact h3
  rw [hbi]
  have hfin : ((S.card : ℕ) : ℝ≥0) ≤ ((P.biUnion (parentContainment U)).card : ℝ≥0) :=
    le_trans (by exact_mod_cast hScard) hexp
  exact_mod_cast hfin

open Classical in
/-- A choice of Hall matching. -/
def hallMatchingFun (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ) (hC : 1 ≤ C) :
    {j : ι // j ∈ U.parent} × Fin (hallTarget U) → ι :=
  (exists_hall_matching U hδρ hC).choose

theorem hallMatchingFun_injective (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ) (hC : 1 ≤ C) :
    Function.Injective (hallMatchingFun U hδρ hC) :=
  (exists_hall_matching U hδρ hC).choose_spec.1

theorem hallMatchingFun_mem (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ) (hC : 1 ≤ C)
    (p : {j : ι // j ∈ U.parent} × Fin (hallTarget U)) :
    hallMatchingFun U hδρ hC p ∈ parentContainment U p.1.1 :=
  (exists_hall_matching U hδρ hC).choose_spec.2 p

open Classical in
/-- **The balanced coarse assignment.**  A leaf reserved by the Hall matching goes to the parent
that reserved it; every other leaf falls back on `Kakeya.uniformCoarseAssign`. -/
def hallAssign (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ) (hC : 1 ≤ C) (i : ι) : ι :=
  if h : ∃ p, hallMatchingFun U hδρ hC p = i then (h.choose).1.1
  else uniformCoarseAssign U i

theorem hallAssign_matching (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ) (hC : 1 ≤ C)
    (p : {j : ι // j ∈ U.parent} × Fin (hallTarget U)) :
    hallAssign U hδρ hC (hallMatchingFun U hδρ hC p) = p.1.1 := by
  have h : ∃ p', hallMatchingFun U hδρ hC p' = hallMatchingFun U hδρ hC p := ⟨p, rfl⟩
  rw [hallAssign, dif_pos h]
  have hspec := h.choose_spec
  have heq := hallMatchingFun_injective U hδρ hC hspec
  rw [heq]

theorem hallAssign_mem (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ) (hC : 1 ≤ C)
    {i : ι} (hi : i ∈ q) : hallAssign U hδρ hC i ∈ U.parent := by
  rw [hallAssign]
  split
  · next h => exact (h.choose).1.2
  · exact uniformCoarseAssign.mem_parent U hi

theorem hallAssign_le (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ) (hC : 1 ≤ C)
    {i : ι} (hi : i ∈ q) :
    (Tt i).toConvexSpaceBody ≤ (U.parentTube (hallAssign U hδρ hC i)).toConvexSpaceBody := by
  rw [hallAssign]
  split
  · next h =>
      have hmem := hallMatchingFun_mem U hδρ hC h.choose
      rw [h.choose_spec] at hmem
      exact (mem_parentContainment.mp hmem).2
  · exact uniformCoarseAssign.le_rescale U hi

open Classical in
/-- **The fibre lower bound.**  Every parent — not merely every parent in the image of the
assignment — receives at least `hallTarget U` leaves. -/
theorem hallTarget_le_card_fibre (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ) (hC : 1 ≤ C)
    {k : ι} (hk : k ∈ U.parent) :
    hallTarget U ≤ (({i ∈ q | hallAssign U hδρ hC i = k} : Finset ι)).card := by
  classical
  have hmaps : ∀ l ∈ (Finset.univ : Finset (Fin (hallTarget U))),
      hallMatchingFun U hδρ hC (⟨k, hk⟩, l)
        ∈ ({i ∈ q | hallAssign U hδρ hC i = k} : Finset ι) := by
    intro l _
    rw [Finset.mem_filter]
    exact ⟨(mem_parentContainment.mp (hallMatchingFun_mem U hδρ hC (⟨k, hk⟩, l))).1,
      hallAssign_matching U hδρ hC (⟨k, hk⟩, l)⟩
  have hinj : Set.InjOn (fun l => hallMatchingFun U hδρ hC (⟨k, hk⟩, l))
      ((Finset.univ : Finset (Fin (hallTarget U))) : Set (Fin (hallTarget U))) := by
    intro l₁ _ l₂ _ h
    have hp := hallMatchingFun_injective U hδρ hC h
    exact (Prod.mk.injEq _ _ _ _ ▸ hp).2
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

open Classical in
/-- **The fibre upper bound.**  A fibre of the assignment is contained in the containment set of its
parent, so uniformity's own upper bound applies to it verbatim. -/
theorem fibre_subset_parentContainment (U : Tube.IsUniformAtScale q Tt ρ C) (hδρ : δ ≤ ρ)
    (hC : 1 ≤ C) (k : ι) :
    ({i ∈ q | hallAssign U hδρ hC i = k} : Finset ι) ⊆ parentContainment U k := by
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [mem_parentContainment]
  refine ⟨hi.1, ?_⟩
  have hle := hallAssign_le U hδρ hC hi.1
  rwa [hi.2] at hle

/-! ### What the branching floor is, and what the datum's numeric fields do not give -/

/-- **The branching floor, read on the configuration.**  `C ^ 2 ≤ N` forces every parent to carry at
least `C` leaves.  Together with `Kakeya.sq_le_branchingN_of_cube_le_card_parentContainment` below
this identifies the floor, to within one power of `C`, with the geometric statement *"every coarse
`ρ`-tube of the parent family contains at least `C` fine tubes"*. -/
theorem le_card_parentContainment_of_sq_le_branchingN (U : Tube.IsUniformAtScale q Tt ρ C)
    (hC : 1 ≤ C) (hNC : C ^ 2 ≤ U.branchingN) {j : ι} (hj : j ∈ U.parent) :
    C ≤ ((parentContainment U j).card : ℝ≥0) := by
  have hC0 : (0 : ℝ≥0) < C := lt_of_lt_of_le zero_lt_one hC
  have h : C * C ≤ C * ((parentContainment U j).card : ℝ≥0) := by
    calc C * C = C ^ 2 := (sq C).symm
      _ ≤ U.branchingN := hNC
      _ ≤ C * ((parentContainment U j).card : ℝ≥0) :=
          branchingN_le_mul_card_parentContainment U hj
  exact le_of_mul_le_mul_left h hC0

/-- **…and conversely**, a single well-populated parent gives the floor.  Because the containment
sets of a `Tube.IsUniformAtScale` are all within `C ^ 2` of one another, this is a statement about
one parent, not about all of them. -/
theorem sq_le_branchingN_of_cube_le_card_parentContainment
    (U : Tube.IsUniformAtScale q Tt ρ C) (hC : 1 ≤ C) {j : ι} (hj : j ∈ U.parent)
    (h : C ^ 3 ≤ ((parentContainment U j).card : ℝ≥0)) : C ^ 2 ≤ U.branchingN := by
  have hC0 : (0 : ℝ≥0) < C := lt_of_lt_of_le zero_lt_one hC
  have h1 : C * C ^ 2 ≤ C * U.branchingN := by
    calc C * C ^ 2 = C ^ 3 := by ring
      _ ≤ ((parentContainment U j).card : ℝ≥0) := h
      _ ≤ C * U.branchingN := card_parentContainment_le U hj
  exact le_of_mul_le_mul_left h1 hC0

/-! ### The floor is not implied by the numeric fields

The five numbers a proof over `Tube.IsUniformAtScale` may use about the bipartite system
"parent `j` ↦ its containment set `F_j`" are

* `1 ≤ |F_j|` — every parent carries a leaf (`0 < branchingN`);
* `|F_j| ≤ C · N` — `Tube.IsUniformAtScale.card_filter_le`;
* `N ≤ C · |F_j|` — `Tube.IsUniformAtScale.le_mul_card_filter`;
* each leaf lies in at most `C` of the `F_j` — `Kakeya.card_parents_containing_le`, the
  containment form of `boundedOverlap`;
* `⋃_j F_j` is all of `𝕋` — every leaf lies under a parent;

together with what the producers add: `1 ≤ N` and `|𝕋_ρ| · N ≤ |𝕋| ≤ 2 · |𝕋_ρ| · N`
(`Tube.refineToEssDistinctUniform`).

`Kakeya.not_exists_sdr_of_uniform_numeric_fields` exhibits a system satisfying **all seven** at
`C = N = 3`, `|𝕋| = 18`, `|𝕋_ρ| = 4` that admits **no** system of distinct representatives.  So no
function `assign` gives every parent a nonempty fibre there, and the `fibre_nonempty` clause of
`Kakeya.Section6CoarseTubeDecomposition` fails over the full parent set — for every assignment, not
merely for a chosen one.

`parentTube_injOn` cannot rescue it: it says distinct parent *indices* name distinct parent
*tubes*, and two distinct `ρ`-tubes may perfectly well have the same containment set, which is what
the two singleton parents below do.

This does not exhibit a `Tube.IsUniformAtScale`; it shows that the numbers such a structure exports
are consistent with Hall's condition failing, which is exactly the claim a proof over that structure
needs and cannot have. -/

/-- **The datum's numeric fields do not imply Hall's condition.**

The witness: four parents over eighteen leaves — two carrying nine leaves each, two carrying the
*same* single leaf — at `C = 3`, `N = 3`, `|𝕋_ρ| = 4`, `|𝕋| = 18`.  All seven numeric facts listed
above hold, and there is no system of distinct representatives, because the two singleton parents
would have to be given the same leaf. -/
theorem not_exists_sdr_of_uniform_numeric_fields :
    ∃ F : Fin 4 → Finset (Fin 18),
      (∀ j, 1 ≤ (F j).card) ∧
      (∀ j, (F j).card ≤ 3 * 3) ∧
      (∀ j, 3 ≤ 3 * (F j).card) ∧
      (∀ i : Fin 18, (Finset.univ.filter (fun j => i ∈ F j)).card ≤ 3) ∧
      (Finset.univ.biUnion F = Finset.univ) ∧
      (4 * 3 ≤ 18 ∧ 18 ≤ 2 * (4 * 3)) ∧
      ¬ ∃ f : Fin 4 → Fin 18, Function.Injective f ∧ ∀ j, f j ∈ F j := by
  classical
  refine ⟨![({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 18)),
            ({9, 10, 11, 12, 13, 14, 15, 16, 17} : Finset (Fin 18)),
            ({0} : Finset (Fin 18)), ({0} : Finset (Fin 18))],
    by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨f, hinj, hmem⟩
  have h2 : f 2 = 0 := by simpa using hmem 2
  have h3 : f 3 = 0 := by simpa using hmem 3
  exact absurd (hinj (h2.trans h3.symm)) (by decide)

/-! ### The multiscale route: what the grid uniformity buys, and why it is not the floor

GWZ Proposition 6.6(B) carries a multiscale uniformity clause,
`∃ C ≤ δ ^ (-η), Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C)`.  Its
underlying `Tube.UniformTubeSet` already contains a **function** — `cover.assign k` — whose classes
are bracketed on *both* sides by `card_class_le` and `le_card_class`.  That is precisely the
two-sided fibre comparability a `Kakeya.Section6CoarseTubeDecomposition` asks for, so at a grid
scale the decomposition needs **no Hall argument and no branching floor at all**, and its
comparability constant is `C` rather than `2 C ^ 2`.  That is
`Kakeya.Section6CoarseTubeDecomposition.ofUniformTubeSet` below.

**It does not remove the floor from Proposition 6.6(B), and the obstruction is at the level of
types.**  A `Kakeya.Section6PartBData` needs its `decomp` and its `factor` over *one and the same*
coarse family `R : κ → Tube ρ`.  The decomposition below produces
`R := 𝒰.cover.tube k : ι → Tube (Tube.gridScale δ N k) _`, while the factorisation comes from the
`Fz` of Proposition 6.6(B), which lives over `PS.parentTube : ι → Tube ρ _`.  Those two types are
equal only when `ρ = Tube.gridScale δ N k`, and the single application site supplies
`ρ = Kakeya.ML2Reduction.plankScale δ ε₂ = δ ^ (1 - ε₂)`, which is a grid scale only in the
accidental case `k / N = 1 - ε₂`.  Nor can it be approximated: consecutive grid scales differ by the
factor `δ ^ (1 / N)` with `N = Tube.ssfGridLen δ`, which is not close to `1`.

So the two routes are genuinely different objects, and Proposition 6.6(B) as its consumer needs it —
with a *free* coarse scale and a *given* `PS` unrelated to the grid — is served only by the Hall
route, which is why the floor is a hypothesis there.  The grid route is recorded because it is the
sharp statement of what the uniformity clause *would* pay for, and because a future restatement of
6.6(B) over a grid-aligned coarse family would get the decomposition for free. -/


/-! ### The decomposition -/

namespace Section6CoarseTubeDecomposition

open Classical in
/-- **The coarse tube decomposition supplied by single-scale uniformity, with no hypothesis about
the assignment.**

This is `Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale` with its hypothesis `hlb`
discharged, and over the **full** parent set rather than the image of a chosen assignment.  The
assignment is `Kakeya.hallAssign`; the fibre bounds are `Kakeya.hallTarget_le_card_fibre` and
`Kakeya.fibre_subset_parentContainment` together with
`Kakeya.card_parentContainment_le`.

The comparability constant is `2 C ^ 2` around the common size `N = U.branchingN`; both halves are
sharp up to the absolute factor `2`, which comes from rounding `N / C²` down to an integer.

The branching floor `C ^ 2 ≤ U.branchingN` cannot be dropped: it is equivalent to
`1 ≤ Kakeya.hallTarget U` (`Kakeya.hallTarget_pos_iff_sq_le_branchingN`), and without a positive
target the parent family may contain distinct `ρ`-tubes sharing all of their leaves, for which no
assignment whatever gives every parent a nonempty fibre. -/
def ofUniformAtScaleHall {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}
    (U : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ C) (hC : 1 ≤ C)
    (hδρ : δ ≤ ρ) (hN : 0 < U.branchingN) (hNC : C ^ 2 ≤ U.branchingN) :
    Section6CoarseTubeDecomposition q T U.parent U.parentTube U.branchingN (2 * C ^ 2) where
  assign := hallAssign U hδρ hC
  assign_mem := fun i hi => hallAssign_mem U hδρ hC hi
  leaf_le_parent := fun i hi => by simpa using hallAssign_le U hδρ hC hi
  one_le_Cfib := by
    calc (1 : ℝ≥0) ≤ C ^ 2 := one_le_pow₀ hC
      _ ≤ C ^ 2 + C ^ 2 := le_add_self
      _ = 2 * C ^ 2 := by ring
  m_pos := hN
  fibre_nonempty := by
    intro k hk
    have ht : 1 ≤ hallTarget U := (hallTarget_pos_iff_sq_le_branchingN U hC).mpr hNC
    have hcard := hallTarget_le_card_fibre U hδρ hC hk
    exact Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one (le_trans ht hcard))
  le_card_fibre := by
    intro k hk
    have hC2 : (0 : ℝ≥0) < C ^ 2 := by positivity
    have hx : (1 : ℝ≥0) ≤ U.branchingN / C ^ 2 := by
      rw [le_div_iff₀ hC2, one_mul]; exact hNC
    have h1 : (1 : ℝ≥0) ≤ ((hallTarget U : ℕ) : ℝ≥0) := by
      exact_mod_cast (hallTarget_pos_iff_sq_le_branchingN U hC).mpr hNC
    have h2 : U.branchingN / C ^ 2 < ((hallTarget U : ℕ) : ℝ≥0) + 1 := Nat.lt_floor_add_one _
    have h3 : U.branchingN / C ^ 2 < 2 * ((hallTarget U : ℕ) : ℝ≥0) := by
      calc U.branchingN / C ^ 2 < ((hallTarget U : ℕ) : ℝ≥0) + 1 := h2
        _ ≤ ((hallTarget U : ℕ) : ℝ≥0) + ((hallTarget U : ℕ) : ℝ≥0) := by gcongr
        _ = 2 * ((hallTarget U : ℕ) : ℝ≥0) := by ring
    rw [div_lt_iff₀ hC2] at h3
    have hstep : U.branchingN / (2 * C ^ 2) ≤ ((hallTarget U : ℕ) : ℝ≥0) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ≥0) < 2 * C ^ 2)]
      calc U.branchingN ≤ 2 * ((hallTarget U : ℕ) : ℝ≥0) * C ^ 2 := le_of_lt h3
        _ = ((hallTarget U : ℕ) : ℝ≥0) * (2 * C ^ 2) := by ring
    refine hstep.trans ?_
    exact_mod_cast hallTarget_le_card_fibre U hδρ hC hk
  card_fibre_le := by
    intro k hk
    have hsub : ((({i ∈ q | hallAssign U hδρ hC i = k} : Finset ι)).card : ℝ≥0)
        ≤ ((parentContainment U k).card : ℝ≥0) := by
      exact_mod_cast Finset.card_le_card (fibre_subset_parentContainment U hδρ hC k)
    refine hsub.trans ((card_parentContainment_le U hk).trans ?_)
    have hCle : C ≤ 2 * C ^ 2 := by
      calc C = C * 1 := (mul_one C).symm
        _ ≤ C * C := by gcongr
        _ = C ^ 2 := (sq C).symm
        _ ≤ C ^ 2 + C ^ 2 := le_add_self
        _ = 2 * C ^ 2 := by ring
    gcongr

open Classical in
/-- **The coarse tube decomposition of a grid-uniform family at a grid scale.**

No Hall argument, no branching floor, and comparability constant `C`: the classes of
`cover.assign k` are already bracketed two-sidedly by the structure's own
`card_class_le` / `le_card_class`.  See the section docstring above for why this does not discharge
the floor of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`. -/
def ofUniformTubeSet {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {C : ℝ≥0}
    (𝒰 : Tube.UniformTubeSet q (fun i => (T i).toTube) N C) (hC : 1 ≤ C)
    (hq : q.Nonempty) {k : ℕ} (hk : k ≤ N) :
    Section6CoarseTubeDecomposition q T (𝒰.cover.indexSet k) (𝒰.cover.tube k)
      (𝒰.branchingN k) C where
  assign := 𝒰.cover.assign k
  assign_mem := fun i hi => 𝒰.cover.assign_mem k hk i hi
  leaf_le_parent := fun i hi => by simpa using 𝒰.cover.le_tube_assign k hk i hi
  one_le_Cfib := hC
  m_pos := by
    obtain ⟨i, hi⟩ := hq
    have hj : 𝒰.cover.assign k i ∈ 𝒰.cover.indexSet k := 𝒰.cover.assign_mem k hk i hi
    have hne : (Tube.coverClass q (𝒰.cover.assign k) (𝒰.cover.assign k i)).Nonempty :=
      ⟨i, by simpa [Tube.coverClass, Finset.mem_filter] using hi⟩
    have h1 : (1 : ℝ≥0)
        ≤ ((Tube.coverClass q (𝒰.cover.assign k) (𝒰.cover.assign k i)).card : ℝ≥0) := by
      exact_mod_cast Finset.card_pos.mpr hne
    have h2 := 𝒰.card_class_le k hk _ hj
    rcases eq_zero_or_pos (𝒰.branchingN k) with h0 | h0
    · exfalso
      rw [h0, mul_zero] at h2
      exact absurd (h1.trans h2) (by norm_num)
    · exact h0
  fibre_nonempty := by
    intro j hj
    obtain ⟨i0, hi0⟩ := hq
    have hj0 : 𝒰.cover.assign k i0 ∈ 𝒰.cover.indexSet k := 𝒰.cover.assign_mem k hk i0 hi0
    have hne0 : (Tube.coverClass q (𝒰.cover.assign k) (𝒰.cover.assign k i0)).Nonempty :=
      ⟨i0, by simpa [Tube.coverClass, Finset.mem_filter] using hi0⟩
    have hNpos : 0 < 𝒰.branchingN k := by
      have h1 : (1 : ℝ≥0)
          ≤ ((Tube.coverClass q (𝒰.cover.assign k) (𝒰.cover.assign k i0)).card : ℝ≥0) := by
        exact_mod_cast Finset.card_pos.mpr hne0
      have h2 := 𝒰.card_class_le k hk _ hj0
      rcases eq_zero_or_pos (𝒰.branchingN k) with h0 | h0
      · exfalso; rw [h0, mul_zero] at h2; exact absurd (h1.trans h2) (by norm_num)
      · exact h0
    have h3 := 𝒰.le_card_class k hk j hj
    have hcpos : 0 < ((Tube.coverClass q (𝒰.cover.assign k) j).card : ℝ≥0) := by
      rcases eq_zero_or_pos ((Tube.coverClass q (𝒰.cover.assign k) j).card : ℝ≥0) with h0 | h0
      · exfalso; rw [h0, mul_zero] at h3; exact absurd (lt_of_lt_of_le hNpos h3) (by simp)
      · exact h0
    have : 0 < (Tube.coverClass q (𝒰.cover.assign k) j).card := by exact_mod_cast hcpos
    simpa [Tube.coverClass] using Finset.card_pos.mp this
  le_card_fibre := by
    intro j hj
    have h3 := 𝒰.le_card_class k hk j hj
    have hC0 : (0 : ℝ≥0) < C := lt_of_lt_of_le zero_lt_one hC
    rw [div_le_iff₀ hC0, mul_comm]
    simpa [Tube.coverClass] using h3
  card_fibre_le := by
    intro j hj
    simpa [Tube.coverClass] using 𝒰.card_class_le k hk j hj

end Section6CoarseTubeDecomposition

end Kakeya

end

end
