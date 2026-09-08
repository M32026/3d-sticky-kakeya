/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ShadeClassBand
public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyUniform
public import Kakeya.DimensionThree.MainLemma2.SetupProduce

/-!
# The class-dense heavy selection: GWZ Definition 2.2 together with a per-tube shade floor

`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` delivers GWZ Definition 2.2 with only an
*aggregate* control of the shading it deletes, while clause (d) of
`Kakeya.VeryNotSticky.BandUniformRefinement` asks for a *per-tube* floor.  Selecting the heavy
members destroys the two lower brackets of Definition 2.2, and a *common* cut cannot repair them
(`ShadedTube.sum_volume_interShade_eq_zero_of_light_cover`).

This file crosses that gap with a **per-tube** cut organised as a least fixed point:

* a member is *deleted* if it is light, if one of its nodes has become thin, or if the part of
  its shading on which all of its classes are still dense against the deletions has fallen
  below the floor;
* a point `x` is *retained* for the surviving member `i` exactly when every class of `i` at `x`
  keeps a `θ k` share after the deletions (`ShadedTube.retainedAt`).

Definition 2.2 for the result is read directly off the retained classes
(`ShadedTube.card_shadeClass_inter_retainedAt_ge`), and the mass the process destroys is
charged, node by node and stage by stage, to the deleted part of each fibre
(`ShadedTube.card_stagedBad_le`): the earliest-stage bad member of a node witnesses that the
whole node class was light at that stage, so all later bad members of the node are among the
`< θ · #class` survivors of that stage.  The total loss is a bounded multiple of the light mass
plus a count of thin-node members, both of which the caller controls.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

/-- **A monotone, bounded iteration on finite sets stabilises within `#s` steps.** -/
theorem exists_iterate_fixed_of_monotone {α : Type*} (s : Finset α)
    (G : Finset α → Finset α) (hG : Monotone G) (hGs : ∀ D, G D ⊆ s) :
    ∃ n, n ≤ s.card ∧ G (G^[n] ∅) = G^[n] ∅ := by
  set D : ℕ → Finset α := fun n => G^[n] ∅ with hD
  have hstep : ∀ n, D n ⊆ D (n + 1) := by
    intro n
    induction n with
    | zero => simp [hD]
    | succ n ih =>
      change G^[n + 1] ∅ ⊆ G^[n + 2] ∅
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' (n := n + 1)]
      exact hG ih
  by_contra hcon
  push Not at hcon
  have hcard : ∀ n, n ≤ s.card + 1 → n ≤ (D n).card := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hne : D n ≠ D (n + 1) := by
        intro heq
        have h := hcon n (by omega)
        apply h
        have heq' : G^[n] ∅ = G^[n + 1] ∅ := heq
        rw [Function.iterate_succ_apply' G n ∅] at heq'
        exact heq'.symm
      have hssub : D n ⊂ D (n + 1) := Finset.ssubset_iff_subset_ne.mpr ⟨hstep n, hne⟩
      have := Finset.card_lt_card hssub
      have := ih (by omega)
      omega
  have h1 := hcard (s.card + 1) le_rfl
  have h2 : (D (s.card + 1)).card ≤ s.card := by
    apply Finset.card_le_card
    change G^[s.card + 1] ∅ ⊆ s
    rw [Function.iterate_succ_apply']
    exact hGs _
  omega

/-- The iterates of a monotone map from `∅` form a monotone chain. -/
theorem monotone_iterate_of_monotone {α : Type*}
    (G : Finset α → Finset α) (hG : Monotone G) :
    Monotone (fun n => G^[n] (∅ : Finset α)) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    change G^[n + 1] ∅ ⊆ G^[n + 2] ∅
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' (n := n + 1)]
    exact hG ih

end Kakeya

namespace ShadedTube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*} [DecidableEq ι]

/-- The fibre of `x`: the members of `s` whose shading covers `x`. -/
noncomputable def fibreAt {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E) (x : E) :
    Finset ι :=
  open scoped Classical in s.filter (fun i => x ∈ (V i).shade)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [DecidableEq ι] in
theorem mem_fibreAt {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {x : E} {i : ι} :
    i ∈ fibreAt s V x ↔ i ∈ s ∧ x ∈ (V i).shade := by
  classical
  simp [fibreAt]

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem shadeClass_sdiff {δ : NNReal} (s D : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ι → ι) (j : ι) (x : E) :
    shadeClass (s \ D) V assign j x = shadeClass s V assign j x \ D := by
  classical
  ext i
  simp only [shadeClass, coverClass, Finset.mem_filter, Finset.mem_sdiff]
  tauto

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem shadeClass_eq_filter_fibreAt {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ι → ι) (j : ι) (x : E) :
    shadeClass s V assign j x = (fibreAt s V x).filter (fun i => assign i = j) := by
  classical
  ext i
  simp only [shadeClass, coverClass, Finset.mem_filter, mem_fibreAt]
  tauto

/-- **Class density of `i` at `x` after deleting `D`.**  The class of `i`'s node retains a
`θ` share once the members of `D` are removed. -/
def GoodAt {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E) (assign : ι → ι)
    (θ : NNReal) (D : Finset ι) (i : ι) (x : E) : Prop :=
  (θ : ℝ) * ((shadeClass s V assign (assign i) x).card : ℝ)
    ≤ ((shadeClass (s \ D) V assign (assign i) x).card : ℝ)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Class density is antitone in the deleted set. -/
theorem GoodAt.anti {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {assign : ι → ι}
    {θ : NNReal} {D D' : Finset ι} (hDD' : D ⊆ D') {i : ι} {x : E}
    (h : GoodAt s V assign θ D' i x) : GoodAt s V assign θ D i x := by
  unfold GoodAt at h ⊢
  refine le_trans h ?_
  rw [shadeClass_sdiff, shadeClass_sdiff]
  exact_mod_cast Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hDD')

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Class density depends on `i` only through its node. -/
theorem GoodAt.congr_node {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {assign : ι → ι}
    {θ : NNReal} {D : Finset ι} {i j : ι} {x : E} (hij : assign i = assign j) :
    GoodAt s V assign θ D i x ↔ GoodAt s V assign θ D j x := by
  unfold GoodAt
  rw [hij]

/-- **The staged bad set at scale `k`.**  Each member `i` carries a stage `m i`; `i` is bad at
scale `k` if it is not yet deleted at its own stage and its class fails the density test against
the deletions of that stage. -/
noncomputable def stagedBad {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ι → ι) (θ : NNReal) (D : ℕ → Finset ι) (m : ι → ℕ) (x : E) : Finset ι :=
  open scoped Classical in
  Finset.filter (fun i => i ∉ D (m i) ∧ ¬ GoodAt s V assign θ (D (m i)) i x) (fibreAt s V x)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **The staged charging bound, one scale.**  Within one node the earliest-stage bad member
witnesses that the whole node class is light at that stage; all later bad members of the node
are then among the `< θ · #class` survivors of that stage, and the class itself is dominated by
its deleted part.  Summing over nodes, the bad set is at most a `θ / (1 - θ)` fraction of the
deleted part of the fibre. -/
theorem card_stagedBad_le {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ι → ι) {θ : NNReal} (hθ1 : θ < 1) (D : ℕ → Finset ι) (hmono : Monotone D)
    (Dinf : Finset ι) (hDinf : ∀ n, D n ⊆ Dinf) (m : ι → ℕ) (x : E) :
    ((stagedBad s V assign θ D m x).card : ℝ)
      ≤ ((θ : ℝ) / (1 - θ)) * (((fibreAt s V x) ∩ Dinf).card : ℝ) := by
  classical
  set X := stagedBad s V assign θ D m x with hX
  have hθ1R : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  -- fibrewise decomposition along the node assignment
  have hfib : X.card = ∑ a ∈ X.image assign, (X.filter (fun i => assign i = a)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi => Finset.mem_image_of_mem assign hi)
  -- each fibre is bounded by the deleted part of its class
  have hfibre : ∀ a ∈ X.image assign,
      ((X.filter (fun i => assign i = a)).card : ℝ)
        ≤ ((θ : ℝ) / (1 - θ)) * (((shadeClass s V assign a x) ∩ Dinf).card : ℝ) := by
    intro a ha
    set F := X.filter (fun i => assign i = a) with hF
    have hFne : F.Nonempty := by
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hia⟩⟩
    obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image F m hFne
    have hi₀X : i₀ ∈ X := (Finset.mem_filter.mp hi₀).1
    have hi₀a : assign i₀ = a := (Finset.mem_filter.mp hi₀).2
    simp only [hX, stagedBad, Finset.mem_filter] at hi₀X
    obtain ⟨hi₀fib, hi₀D, hi₀bad⟩ := hi₀X
    set c := shadeClass s V assign a x with hc
    -- `F` lies in the survivors of the class at stage `m i₀`
    have hFsub : F ⊆ c \ D (m i₀) := by
      intro i hi
      have hiF := Finset.mem_filter.mp hi
      have hiX := hiF.1
      have hia := hiF.2
      simp only [hX, stagedBad, Finset.mem_filter, mem_fibreAt] at hiX
      obtain ⟨⟨his, hix⟩, hiD, -⟩ := hiX
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [hc, shadeClass_eq_filter_fibreAt]
        exact Finset.mem_filter.mpr ⟨mem_fibreAt.mpr ⟨his, hix⟩, hia⟩
      · intro hmem
        exact hiD (hmono (hmin i hi) hmem)
    -- the class is light at stage `m i₀`
    have hlight : ((c \ D (m i₀)).card : ℝ) < (θ : ℝ) * (c.card : ℝ) := by
      unfold GoodAt at hi₀bad
      rw [shadeClass_sdiff, hi₀a] at hi₀bad
      exact lt_of_not_ge hi₀bad
    -- split the class
    have hsplit : (c.card : ℝ) = ((c \ D (m i₀)).card : ℝ) + ((c ∩ D (m i₀)).card : ℝ) := by
      have := Finset.card_sdiff_add_card_inter c (D (m i₀))
      exact_mod_cast this.symm
    have hinter : ((c ∩ D (m i₀)).card : ℝ) ≤ ((c ∩ Dinf).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (Finset.inter_subset_inter (Finset.Subset.refl _) (hDinf _))
    have hFcard : ((F.card : ℕ) : ℝ) ≤ ((c \ D (m i₀)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hFsub
    -- `(1 - θ) #c < #(c ∩ D)`, hence `#(c \ D) < θ #c < θ/(1-θ) · #(c ∩ D)`
    have hkey : (1 - (θ : ℝ)) * (c.card : ℝ) ≤ ((c ∩ Dinf).card : ℝ) := by
      nlinarith
    calc ((F.card : ℕ) : ℝ) ≤ ((c \ D (m i₀)).card : ℝ) := hFcard
      _ ≤ (θ : ℝ) * (c.card : ℝ) := hlight.le
      _ = ((θ : ℝ) / (1 - θ)) * ((1 - (θ : ℝ)) * (c.card : ℝ)) := by
          field_simp
      _ ≤ ((θ : ℝ) / (1 - θ)) * (((c ∩ Dinf).card : ℝ)) := by
          gcongr
  -- the classes of distinct nodes are disjoint inside the fibre
  have hdisj : ∑ a ∈ X.image assign, (((shadeClass s V assign a x) ∩ Dinf).card : ℝ)
      ≤ (((fibreAt s V x) ∩ Dinf).card : ℝ) := by
    have hcard : ∑ a ∈ X.image assign, ((shadeClass s V assign a x) ∩ Dinf).card
        = ((X.image assign).biUnion (fun a => (shadeClass s V assign a x) ∩ Dinf)).card := by
      symm
      apply Finset.card_biUnion
      intro a _ b _ hab
      rw [Function.onFun, Finset.disjoint_left]
      intro i hia hib
      simp only [Finset.mem_inter, shadeClass_eq_filter_fibreAt, Finset.mem_filter] at hia hib
      exact hab (hia.1.2.symm.trans hib.1.2)
    have hsub : (X.image assign).biUnion (fun a => (shadeClass s V assign a x) ∩ Dinf)
        ⊆ (fibreAt s V x) ∩ Dinf := by
      intro i hi
      obtain ⟨a, -, hia⟩ := Finset.mem_biUnion.mp hi
      simp only [Finset.mem_inter, shadeClass_eq_filter_fibreAt, Finset.mem_filter] at hia ⊢
      exact ⟨hia.1.1, hia.2⟩
    have := Finset.card_le_card hsub
    rw [← hcard] at this
    exact_mod_cast this
  calc ((X.card : ℕ) : ℝ)
      = ∑ a ∈ X.image assign, (((X.filter (fun i => assign i = a)).card : ℕ) : ℝ) := by
        rw [hfib]; push_cast; rfl
    _ ≤ ∑ a ∈ X.image assign,
          ((θ : ℝ) / (1 - θ)) * (((shadeClass s V assign a x) ∩ Dinf).card : ℝ) :=
        Finset.sum_le_sum hfibre
    _ = ((θ : ℝ) / (1 - θ)) *
          ∑ a ∈ X.image assign, (((shadeClass s V assign a x) ∩ Dinf).card : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ ((θ : ℝ) / (1 - θ)) * (((fibreAt s V x) ∩ Dinf).card : ℝ) := by
        gcongr

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **The light-class bound.**  A set of members whose classes all fail the density test
against one common deleted set `D` is at most a `θ` share of any set containing all their
classes.  This is the fibrewise pigeonhole of `card_stagedBad_le` at a single stage. -/
theorem card_le_of_forall_not_goodAt {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ι → ι) (θ : NNReal) (D : Finset ι) (x : E) (B : Finset ι)
    (hsub : B ⊆ fibreAt s V x \ D)
    (hbad : ∀ j ∈ B, ¬ GoodAt s V assign θ D j x) (U : Finset ι)
    (hU : ∀ j ∈ B, shadeClass s V assign (assign j) x ⊆ U) :
    (B.card : ℝ) ≤ (θ : ℝ) * (U.card : ℝ) := by
  classical
  have hfib : B.card = ∑ a ∈ B.image assign, (B.filter (fun i => assign i = a)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi => Finset.mem_image_of_mem assign hi)
  have hfibre : ∀ a ∈ B.image assign,
      ((B.filter (fun i => assign i = a)).card : ℝ)
        ≤ (θ : ℝ) * ((shadeClass s V assign a x).card : ℝ) := by
    intro a ha
    obtain ⟨j₀, hj₀, hj₀a⟩ := Finset.mem_image.mp ha
    have hbad₀ := hbad j₀ hj₀
    unfold GoodAt at hbad₀
    rw [shadeClass_sdiff, hj₀a] at hbad₀
    have hlt := lt_of_not_ge hbad₀
    have hFsub : B.filter (fun i => assign i = a) ⊆ shadeClass s V assign a x \ D := by
      intro i hi
      have hiF := Finset.mem_filter.mp hi
      have hiB := hsub hiF.1
      rw [Finset.mem_sdiff, mem_fibreAt] at hiB
      refine Finset.mem_sdiff.mpr ⟨?_, hiB.2⟩
      rw [shadeClass_eq_filter_fibreAt]
      exact Finset.mem_filter.mpr ⟨mem_fibreAt.mpr hiB.1, hiF.2⟩
    calc ((B.filter (fun i => assign i = a)).card : ℝ)
        ≤ ((shadeClass s V assign a x \ D).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hFsub
      _ ≤ (θ : ℝ) * ((shadeClass s V assign a x).card : ℝ) := hlt.le
  have hdisj : ∑ a ∈ B.image assign, ((shadeClass s V assign a x).card : ℝ) ≤ (U.card : ℝ) := by
    have hcard : ∑ a ∈ B.image assign, (shadeClass s V assign a x).card
        = ((B.image assign).biUnion (fun a => shadeClass s V assign a x)).card := by
      symm
      apply Finset.card_biUnion
      intro a _ b _ hab
      rw [Function.onFun, Finset.disjoint_left]
      intro i hia hib
      simp only [shadeClass_eq_filter_fibreAt, Finset.mem_filter] at hia hib
      exact hab (hia.2.symm.trans hib.2)
    have hsub' : (B.image assign).biUnion (fun a => shadeClass s V assign a x) ⊆ U := by
      intro i hi
      obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp ha
      rw [← hja] at hia
      exact hU j hj hia
    have := Finset.card_le_card hsub'
    rw [← hcard] at this
    exact_mod_cast this
  calc ((B.card : ℕ) : ℝ)
      = ∑ a ∈ B.image assign, (((B.filter (fun i => assign i = a)).card : ℕ) : ℝ) := by
        rw [hfib]; push_cast; rfl
    _ ≤ ∑ a ∈ B.image assign, (θ : ℝ) * ((shadeClass s V assign a x).card : ℝ) :=
        Finset.sum_le_sum hfibre
    _ = (θ : ℝ) * ∑ a ∈ B.image assign, ((shadeClass s V assign a x).card : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ (θ : ℝ) * (U.card : ℝ) := by gcongr

/-- **The retained fibre at `x`.**  The survivors of the deletion `D` whose classes at every
scale pass the density test against `D`. -/
noncomputable def retainedAt {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ℕ → ι → ι) (N : ℕ) (θ : ℕ → NNReal) (D : Finset ι) (x : E) : Finset ι :=
  open scoped Classical in
  Finset.filter (fun i => ∀ k ≤ N, GoodAt s V (assign k) (θ k) D i x) (fibreAt s V x \ D)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem mem_retainedAt {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E}
    {assign : ℕ → ι → ι} {N : ℕ} {θ : ℕ → NNReal} {D : Finset ι} {x : E} {i : ι} :
    i ∈ retainedAt s V assign N θ D x ↔
      (i ∈ s ∧ x ∈ (V i).shade) ∧ i ∉ D ∧ ∀ k ≤ N, GoodAt s V (assign k) (θ k) D i x := by
  classical
  simp only [retainedAt, Finset.mem_filter, Finset.mem_sdiff, mem_fibreAt]
  tauto

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **The retained class bracket.**  Under a nested assignment and thresholds decaying fast enough
along the scales, every class met by the retained fibre keeps at least half of its `θ k` share:
members of the class fail only through their sub-classes at finer scales, and those sub-classes
are light. -/
theorem card_shadeClass_inter_retainedAt_ge {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ E) (assign : ℕ → ι → ι) (N : ℕ)
    (hnest : ∀ k l, k ≤ l → l ≤ N → ∀ i ∈ s, ∀ j ∈ s,
      assign l i = assign l j → assign k i = assign k j)
    (θ : ℕ → NNReal) (hθ : ∀ k ≤ N, 2 * ∑ k' ∈ Finset.Ioc k N, (θ k' : ℝ) ≤ θ k)
    (D : Finset ι) (x : E) {i : ι} (hi : i ∈ retainedAt s V assign N θ D x) {k : ℕ}
    (hk : k ≤ N) :
    ((θ k : ℝ) / 2) * ((shadeClass s V (assign k) (assign k i) x).card : ℝ)
      ≤ ((shadeClass s V (assign k) (assign k i) x ∩ retainedAt s V assign N θ D x).card : ℝ) := by
  classical
  obtain ⟨⟨his, hix⟩, hiD, hgood⟩ := mem_retainedAt.mp hi
  set c := shadeClass s V (assign k) (assign k i) x with hc
  set R := retainedAt s V assign N θ D x with hR
  -- the survivors of the class, and its bad part
  set c' := c \ D with hc'
  set B := c'.filter (fun j => ∃ k' ∈ Finset.Ioc k N, ¬ GoodAt s V (assign k') (θ k') D j x)
    with hB
  have hcR : c ∩ R = c' \ B := by
    ext j
    simp only [hR, mem_retainedAt, hc', hB, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter,
      not_and, not_exists, Finset.mem_Ioc, not_not]
    constructor
    · rintro ⟨hjc, ⟨_, hjD, hgd⟩⟩
      refine ⟨⟨hjc, hjD⟩, fun _ k' hk' => hgd k' hk'.2⟩
    · rintro ⟨⟨hjc, hjD⟩, hno⟩
      have hjfib : j ∈ fibreAt s V x := by
        rw [hc, shadeClass_eq_filter_fibreAt] at hjc
        exact (Finset.mem_filter.mp hjc).1
      refine ⟨hjc, ⟨mem_fibreAt.mp hjfib, hjD, fun k' hk' => ?_⟩⟩
      by_cases hkk' : k < k'
      · exact hno ⟨hjc, hjD⟩ k' ⟨hkk', hk'⟩
      · -- coarser scales: the class of `j` is the class of `i`
        have hjs : j ∈ s := (mem_fibreAt.mp hjfib).1
        have hjk : assign k j = assign k i := by
          rw [hc, shadeClass_eq_filter_fibreAt] at hjc
          exact (Finset.mem_filter.mp hjc).2
        have hjk' : assign k' j = assign k' i :=
          hnest k' k (not_lt.mp hkk') hk j hjs i his hjk
        exact (GoodAt.congr_node hjk').mpr (hgood k' hk')
  -- the class keeps a `θ k` share after deleting `D`
  have hc'ge : (θ k : ℝ) * (c.card : ℝ) ≤ (c'.card : ℝ) := by
    have h := hgood k hk
    unfold GoodAt at h
    rw [shadeClass_sdiff] at h
    exact h
  -- the bad part is small, scale by scale
  have hBle : (B.card : ℝ) ≤ (∑ k' ∈ Finset.Ioc k N, (θ k' : ℝ)) * (c.card : ℝ) := by
    have hBsub : B ⊆ (Finset.Ioc k N).biUnion
        (fun k' => c'.filter (fun j => ¬ GoodAt s V (assign k') (θ k') D j x)) := by
      intro j hj
      rw [hB, Finset.mem_filter] at hj
      obtain ⟨hjc', k', hk', hbad⟩ := hj
      exact Finset.mem_biUnion.mpr ⟨k', hk', Finset.mem_filter.mpr ⟨hjc', hbad⟩⟩
    have h1 : (B.card : ℝ) ≤ ∑ k' ∈ Finset.Ioc k N,
        ((c'.filter (fun j => ¬ GoodAt s V (assign k') (θ k') D j x)).card : ℝ) := by
      have := le_trans (Finset.card_le_card hBsub) Finset.card_biUnion_le
      exact_mod_cast this
    refine le_trans h1 ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k' hk' => ?_
    have hk'N : k' ≤ N := (Finset.mem_Ioc.mp hk').2
    have hkk' : k ≤ k' := (Finset.mem_Ioc.mp hk').1.le
    refine card_le_of_forall_not_goodAt s V (assign k') (θ k') D x _ ?_ ?_ c ?_
    · intro j hj
      have hjc' := (Finset.mem_filter.mp hj).1
      rw [hc', Finset.mem_sdiff] at hjc'
      rw [Finset.mem_sdiff]
      refine ⟨?_, hjc'.2⟩
      rw [hc, shadeClass_eq_filter_fibreAt] at hjc'
      exact (Finset.mem_filter.mp hjc'.1).1
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro j hj l hl
      have hjc' := (Finset.mem_filter.mp hj).1
      rw [hc', Finset.mem_sdiff, hc, shadeClass_eq_filter_fibreAt, Finset.mem_filter,
        mem_fibreAt] at hjc'
      rw [shadeClass_eq_filter_fibreAt, Finset.mem_filter, mem_fibreAt] at hl
      rw [hc, shadeClass_eq_filter_fibreAt, Finset.mem_filter, mem_fibreAt]
      refine ⟨hl.1, ?_⟩
      have h1 : assign k l = assign k j := hnest k k' hkk' hk'N l hl.1.1 j hjc'.1.1.1 hl.2
      rw [h1]
      exact hjc'.1.2
  -- assemble
  have hcard : ((c' \ B).card : ℝ) = (c'.card : ℝ) - (B.card : ℝ) := by
    have hBc' : B ⊆ c' := Finset.filter_subset _ _
    have := Finset.card_sdiff_add_card_eq_card hBc'
    have h2 : (c' \ B).card + B.card = c'.card := this
    have h3 : ((c' \ B).card : ℝ) + (B.card : ℝ) = (c'.card : ℝ) := by exact_mod_cast h2
    linarith
  have hθk := hθ k hk
  have hcnn : (0 : ℝ) ≤ (c.card : ℝ) := by positivity
  rw [hcR, hcard]
  have hsum_le : (∑ k' ∈ Finset.Ioc k N, (θ k' : ℝ)) * (c.card : ℝ)
      ≤ ((θ k : ℝ) / 2) * (c.card : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hcnn
    linarith
  linarith

section Process

variable {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {assign : ℕ → ι → ι} {N : ℕ}
  {θ : ℕ → NNReal} {θ' : NNReal} {t : ENNReal}

variable (s V assign N θ θ' t) in
/-- The points at which every class of `i` passes the density test against `D`. -/
def goodSet (D : Finset ι) (i : ι) : Set E :=
  {x | ∀ k ≤ N, GoodAt s V (assign k) (θ k) D i x}

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem measurableSet_setOf_goodAt (s : Finset ι) (V : ι → ShadedTube δ E) (D : Finset ι)
    (a : ι → ι) (ϑ : NNReal) (i : ι) :
    MeasurableSet {x | GoodAt s V a ϑ D i x} := by
  classical
  have hf : Measurable fun x => (ϑ : ℝ) * ((shadeClass s V a (a i) x).card : ℝ) :=
    (measurable_from_nat.comp (measurable_shadeClass_card s V a (a i))).const_mul _
  have hg : Measurable fun x => ((shadeClass (s \ D) V a (a i) x).card : ℝ) :=
    measurable_from_nat.comp (measurable_shadeClass_card (s \ D) V a (a i))
  exact measurableSet_le hf hg

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem measurableSet_goodSet (D : Finset ι) (i : ι) :
    MeasurableSet (goodSet s V assign N θ D i) := by
  have : goodSet s V assign N θ D i
      = ⋂ k ∈ Finset.range (N + 1), {x | GoodAt s V (assign k) (θ k) D i x} := by
    ext x
    simp [goodSet, Finset.mem_range]
  rw [this]
  exact MeasurableSet.biInter (Finset.range (N + 1)).countable_toSet
    fun k _ => measurableSet_setOf_goodAt s V D (assign k) (θ k) i

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem goodSet_anti {D D' : Finset ι} (h : D ⊆ D') (i : ι) :
    goodSet s V assign N θ D' i ⊆ goodSet s V assign N θ D i := by
  intro x hx k hk
  exact (hx k hk).anti h

variable (s V assign N θ θ' t) in
/-- The mass of `i`'s shading on which all of its classes are dense against `D`. -/
noncomputable def massAt (D : Finset ι) (i : ι) : ENNReal :=
  volume ((V i).shade ∩ goodSet s V assign N θ D i)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem massAt_anti {D D' : Finset ι} (h : D ⊆ D') (i : ι) :
    massAt s V assign N θ D' i ≤ massAt s V assign N θ D i :=
  measure_mono (Set.inter_subset_inter_right _ (goodSet_anti h i))

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem massAt_le (D : Finset ι) (i : ι) :
    massAt s V assign N θ D i ≤ volume (V i).shade :=
  measure_mono Set.inter_subset_left

variable (s V assign N θ θ' t) in
/-- **A thin node.**  Some node of `i` has lost more than a `1 - θ'` share of its class to `D`. -/
def ThinAt (D : Finset ι) (i : ι) : Prop :=
  ∃ k ≤ N, ((coverClass s (assign k) (assign k i) \ D).card : ℝ)
    < (θ' : ℝ) * ((coverClass s (assign k) (assign k i)).card : ℝ)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem ThinAt.mono {D D' : Finset ι} (h : D ⊆ D') {i : ι}
    (hi : ThinAt s assign N θ' D i) : ThinAt s assign N θ' D' i := by
  obtain ⟨k, hk, hlt⟩ := hi
  refine ⟨k, hk, lt_of_le_of_lt ?_ hlt⟩
  exact_mod_cast Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) h)

variable (s V assign N θ θ' t) in
/-- **One deletion step.**  Delete the light members, the members of thin nodes, and the members
whose dense mass has fallen below the floor. -/
noncomputable def deleteStep (D : Finset ι) : Finset ι :=
  open scoped Classical in
  s.filter (fun i => volume (V i).shade < 2 * t ∨ ThinAt s assign N θ' D i ∨
    massAt s V assign N θ D i < t)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem mem_deleteStep {D : Finset ι} {i : ι} :
    i ∈ deleteStep s V assign N θ θ' t D ↔
      i ∈ s ∧ (volume (V i).shade < 2 * t ∨ ThinAt s assign N θ' D i ∨
        massAt s V assign N θ D i < t) := by
  classical
  simp [deleteStep]

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem deleteStep_mono : Monotone (deleteStep s V assign N θ θ' t) := by
  intro D D' hDD' i hi
  rw [mem_deleteStep] at hi ⊢
  refine ⟨hi.1, ?_⟩
  rcases hi.2 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (ThinAt.mono hDD' h))
  · exact Or.inr (Or.inr (lt_of_le_of_lt (massAt_anti hDD' i) h))

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem deleteStep_subset (D : Finset ι) : deleteStep s V assign N θ θ' t D ⊆ s :=
  fun _ hi => (mem_deleteStep.mp hi).1

variable (s V assign N θ θ' t) in
/-- The deletion chain. -/
noncomputable def deleteChain (n : ℕ) : Finset ι :=
  (deleteStep s V assign N θ θ' t)^[n] ∅

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem monotone_deleteChain : Monotone (deleteChain s V assign N θ θ' t) :=
  Kakeya.monotone_iterate_of_monotone _ deleteStep_mono

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem deleteChain_succ (n : ℕ) :
    deleteChain s V assign N θ θ' t (n + 1)
      = deleteStep s V assign N θ θ' t (deleteChain s V assign N θ θ' t n) :=
  Function.iterate_succ_apply' _ n ∅

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem deleteChain_zero : deleteChain s V assign N θ θ' t 0 = ∅ := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem deleteChain_subset (n : ℕ) : deleteChain s V assign N θ θ' t n ⊆ s := by
  cases n with
  | zero => simp [deleteChain_zero]
  | succ n => rw [deleteChain_succ]; exact deleteStep_subset _

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem exists_fixStage : ∃ n, n ≤ s.card ∧
    deleteStep s V assign N θ θ' t (deleteChain s V assign N θ θ' t n)
      = deleteChain s V assign N θ θ' t n :=
  Kakeya.exists_iterate_fixed_of_monotone s _ deleteStep_mono deleteStep_subset

variable (s V assign N θ θ' t) in
/-- The stage at which the chain stabilises. -/
noncomputable def fixStage : ℕ :=
  Classical.choose (exists_fixStage (s := s) (V := V) (assign := assign) (N := N) (θ := θ)
    (θ' := θ') (t := t))

variable (s V assign N θ θ' t) in
/-- **The deleted set**: the least fixed point of the deletion step. -/
noncomputable def deleted : Finset ι :=
  deleteChain s V assign N θ θ' t (fixStage s V assign N θ θ' t)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem deleteStep_deleted :
    deleteStep s V assign N θ θ' t (deleted s V assign N θ θ' t) = deleted s V assign N θ θ' t :=
  (Classical.choose_spec (exists_fixStage (s := s) (V := V) (assign := assign) (N := N) (θ := θ)
    (θ' := θ') (t := t))).2

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem deleted_subset : deleted s V assign N θ θ' t ⊆ s := deleteChain_subset _

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem deleteChain_subset_deleted (n : ℕ) :
    deleteChain s V assign N θ θ' t n ⊆ deleted s V assign N θ θ' t := by
  by_cases hn : n ≤ fixStage s V assign N θ θ' t
  · exact monotone_deleteChain hn
  · have hfix := deleteStep_deleted (s := s) (V := V) (assign := assign) (N := N) (θ := θ)
      (θ' := θ') (t := t)
    have : deleteChain s V assign N θ θ' t n = deleted s V assign N θ θ' t := by
      obtain ⟨m, hm⟩ : ∃ m, n = m + fixStage s V assign N θ θ' t :=
        ⟨n - fixStage s V assign N θ θ' t, by omega⟩
      rw [hm]
      change (deleteStep s V assign N θ θ' t)^[m + fixStage s V assign N θ θ' t] ∅ = _
      rw [Function.iterate_add_apply]
      exact Function.iterate_fixed hfix m
    rw [this]

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Light members are deleted at the first step. -/
theorem mem_deleted_of_light {i : ι} (hi : i ∈ s) (hl : volume (V i).shade < 2 * t) :
    i ∈ deleted s V assign N θ θ' t := by
  apply deleteChain_subset_deleted 1
  rw [deleteChain_succ, deleteChain_zero, mem_deleteStep]
  exact ⟨hi, Or.inl hl⟩

variable (s V assign N θ θ' t) in
/-- **The stage of a member**: one before its deletion, or the final stage if it survives. -/
noncomputable def stage (i : ι) : ℕ :=
  open scoped Classical in
  if h : i ∈ deleted s V assign N θ θ' t then
    Nat.find (⟨fixStage s V assign N θ θ' t, h⟩ : ∃ n, i ∈ deleteChain s V assign N θ θ' t n) - 1
  else fixStage s V assign N θ θ' t

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem notMem_deleteChain_stage (i : ι) :
    i ∉ deleteChain s V assign N θ θ' t (stage s V assign N θ θ' t i) := by
  classical
  unfold stage
  split_ifs with h
  · set P : ℕ → Prop := fun n => i ∈ deleteChain s V assign N θ θ' t n with hP
    have hex : ∃ n, P n := ⟨fixStage s V assign N θ θ' t, h⟩
    have hpos : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0] at this
      simp [hP, deleteChain_zero] at this
    have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    exact Nat.find_min hex hlt
  · exact h

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem mem_deleteStep_stage_of_mem_deleted {i : ι} (h : i ∈ deleted s V assign N θ θ' t) :
    i ∈ deleteStep s V assign N θ θ' t
      (deleteChain s V assign N θ θ' t (stage s V assign N θ θ' t i)) := by
  classical
  unfold stage
  rw [dif_pos h]
  set P : ℕ → Prop := fun n => i ∈ deleteChain s V assign N θ θ' t n with hP
  have hex : ∃ n, P n := ⟨fixStage s V assign N θ θ' t, h⟩
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    simp [hP, deleteChain_zero] at this
  have hspec : i ∈ deleteChain s V assign N θ θ' t (Nat.find hex) := Nat.find_spec hex
  have heq : Nat.find hex = (Nat.find hex - 1) + 1 := by omega
  rw [heq, deleteChain_succ] at hspec
  exact hspec

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem deleteChain_stage_of_notMem {i : ι} (h : i ∉ deleted s V assign N θ θ' t) :
    deleteChain s V assign N θ θ' t (stage s V assign N θ θ' t i)
      = deleted s V assign N θ θ' t := by
  classical
  unfold stage
  rw [dif_neg h]
  rfl

variable (s V assign N θ θ' t) in
/-- **The dense shading.**  Each member keeps exactly the points at which it is retained. -/
noncomputable def denseShade (i : ι) : ShadedTube δ E :=
  { V i with
    shade := (V i).shade ∩ {x | i ∈ retainedAt s V assign N θ (deleted s V assign N θ θ' t) x}
    measurableSet_shade := by
      classical
      apply (V i).measurableSet_shade.inter
      by_cases hi : i ∈ s ∧ i ∉ deleted s V assign N θ θ' t
      · have : {x | i ∈ retainedAt s V assign N θ (deleted s V assign N θ θ' t) x}
            = (V i).shade ∩ goodSet s V assign N θ (deleted s V assign N θ θ' t) i := by
          ext x
          simp only [Set.mem_setOf_eq, mem_retainedAt, Set.mem_inter_iff, goodSet]
          tauto
        rw [this]
        exact (V i).measurableSet_shade.inter (measurableSet_goodSet _ _)
      · have : {x | i ∈ retainedAt s V assign N θ (deleted s V assign N θ θ' t) x} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, mem_retainedAt, Set.mem_empty_iff_false, iff_false]
          intro hx
          exact hi ⟨hx.1.1, hx.2.1⟩
        rw [this]
        exact MeasurableSet.empty
    shade_subset := Set.Subset.trans Set.inter_subset_left (V i).shade_subset }

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
@[simp] theorem denseShade_toTube (i : ι) :
    (denseShade s V assign N θ θ' t i).toTube = (V i).toTube := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem denseShade_shade (i : ι) :
    (denseShade s V assign N θ θ' t i).shade
      = (V i).shade ∩ {x | i ∈ retainedAt s V assign N θ (deleted s V assign N θ θ' t) x} := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem denseShade_shade_subset (i : ι) :
    (denseShade s V assign N θ θ' t i).shade ⊆ (V i).shade := Set.inter_subset_left

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem mem_denseShade_shade {i : ι} {x : E} :
    x ∈ (denseShade s V assign N θ θ' t i).shade ↔
      i ∈ retainedAt s V assign N θ (deleted s V assign N θ θ' t) x := by
  rw [denseShade_shade]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(mem_retainedAt.mp h).1.2, h⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- On a survivor the dense shading is the good part of the shading. -/
theorem denseShade_shade_of_notMem {i : ι} (hi : i ∈ s) (hD : i ∉ deleted s V assign N θ θ' t) :
    (denseShade s V assign N θ θ' t i).shade
      = (V i).shade ∩ goodSet s V assign N θ (deleted s V assign N θ θ' t) i := by
  ext x
  rw [mem_denseShade_shade, mem_retainedAt]
  simp only [Set.mem_inter_iff, goodSet, Set.mem_setOf_eq]
  tauto

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem volume_denseShade_of_notMem {i : ι} (hi : i ∈ s) (hD : i ∉ deleted s V assign N θ θ' t) :
    volume (denseShade s V assign N θ θ' t i).shade
      = massAt s V assign N θ (deleted s V assign N θ θ' t) i := by
  rw [denseShade_shade_of_notMem hi hD]
  rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **The retained class identity.**  A class of the dense family is the corresponding class of
the original family intersected with the retained fibre. -/
theorem shadeClass_denseShade (k : ℕ) (a : ι) (x : E) :
    shadeClass (s \ deleted s V assign N θ θ' t) (denseShade s V assign N θ θ' t) (assign k) a x
      = shadeClass s V (assign k) a x ∩
          retainedAt s V assign N θ (deleted s V assign N θ θ' t) x := by
  classical
  ext j
  simp only [shadeClass, coverClass, Finset.mem_filter, Finset.mem_inter, Finset.mem_sdiff,
    mem_denseShade_shade]
  constructor
  · rintro ⟨⟨⟨hjs, hjD⟩, hja⟩, hjR⟩
    exact ⟨⟨⟨hjs, hja⟩, (mem_retainedAt.mp hjR).1.2⟩, hjR⟩
  · rintro ⟨⟨⟨hjs, hja⟩, hjx⟩, hjR⟩
    exact ⟨⟨⟨hjs, (mem_retainedAt.mp hjR).2.1⟩, hja⟩, hjR⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Survivors of the fixed point are heavy, sit in no thin node, and keep the floor. -/
theorem survivor_spec {i : ι} (hi : i ∈ s) (hD : i ∉ deleted s V assign N θ θ' t) :
    2 * t ≤ volume (V i).shade ∧ ¬ ThinAt s assign N θ' (deleted s V assign N θ θ' t) i ∧
      t ≤ massAt s V assign N θ (deleted s V assign N θ θ' t) i := by
  have hfix := deleteStep_deleted (s := s) (V := V) (assign := assign) (N := N) (θ := θ)
    (θ' := θ') (t := t)
  have hnot : i ∉ deleteStep s V assign N θ θ' t (deleted s V assign N θ θ' t) := by
    rw [hfix]; exact hD
  rw [mem_deleteStep] at hnot
  push Not at hnot
  have h := hnot hi
  exact ⟨h.1, h.2.1, h.2.2⟩

end Process


section CoverRestrict

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq ι] in
theorem mem_coverClass {u : Finset ι} {assign : ι → ι} {P i : ι} :
    i ∈ coverClass u assign P ↔ i ∈ u ∧ assign i = P := by
  classical
  unfold coverClass
  exact Finset.mem_filter

omit [Nontrivial E] [MeasureSpace E] [BorelSpace E] in
/-- **A nested cover restricted to a subfamily, with the uninhabited nodes removed.**  Unlike
`Kakeya.ml1Boot.gridCoverRestrict`, the index set at each scale keeps only the nodes carrying a
member of the subfamily, which is what the lower class bracket of `Tube.UniformTubeSet` needs. -/
def restrictCoverInhabited {δ : NNReal} {s s' : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (cover : GridCoverSystem s T N) (hs : s' ⊆ s) : GridCoverSystem s' T N where
  indexSet k := open scoped Classical in
    (cover.indexSet k).filter (fun a => ∃ i ∈ s', cover.assign k i = a)
  assign := cover.assign
  tube := cover.tube
  assign_mem k hk i hi := by
    classical
    exact Finset.mem_filter.mpr ⟨cover.assign_mem k hk i (hs hi), i, hi, rfl⟩
  le_tube_assign k hk i hi := cover.le_tube_assign k hk i (hs hi)
  nested k hk i hi j hj h := cover.nested k hk i (hs hi) j (hs hj) h
  tube_nested k hk i hi := cover.tube_nested k hk i (hs hi)

omit [Nontrivial E] [MeasureSpace E] [BorelSpace E] in
theorem mem_indexSet_restrictCoverInhabited {δ : NNReal} {s s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (cover : GridCoverSystem s T N) (hs : s' ⊆ s) {k : ℕ} {a : ι} :
    a ∈ (restrictCoverInhabited cover hs).indexSet k ↔
      a ∈ cover.indexSet k ∧ ∃ i ∈ s', cover.assign k i = a := by
  classical
  unfold restrictCoverInhabited
  exact Finset.mem_filter

omit [Nontrivial E] [MeasureSpace E] [BorelSpace E] in
@[simp] theorem assign_restrictCoverInhabited {δ : NNReal} {s s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (cover : GridCoverSystem s T N) (hs : s' ⊆ s) :
    (restrictCoverInhabited cover hs).assign = cover.assign := rfl

omit [Nontrivial E] [MeasureSpace E] [BorelSpace E] in
@[simp] theorem tube_restrictCoverInhabited {δ : NNReal} {s s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (cover : GridCoverSystem s T N) (hs : s' ⊆ s) :
    (restrictCoverInhabited cover hs).tube = cover.tube := rfl

end CoverRestrict


section ThinCount

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
open scoped Classical in
/-- **The staged thin-node count.**  The members that are deleted for sitting in a thin node
number at most `(N + 1) θ' #s`: within one node the earliest-stage such member witnesses that
the node was thin at that stage, and all later ones are among its `< θ' · #class` survivors. -/
theorem card_stagedThin_le (s : Finset ι) (assign : ℕ → ι → ι) (N : ℕ) (θ' : NNReal)
    (D : ℕ → Finset ι) (hmono : Monotone D) (m : ι → ℕ) :
    ((s.filter (fun i => i ∉ D (m i) ∧ ThinAt s assign N θ' (D (m i)) i)).card : ℝ)
      ≤ ((N : ℝ) + 1) * (θ' : ℝ) * (s.card : ℝ) := by
  classical
  set Tk : ℕ → Finset ι := fun k => s.filter (fun i => i ∉ D (m i) ∧
    ((coverClass s (assign k) (assign k i) \ D (m i)).card : ℝ)
      < (θ' : ℝ) * ((coverClass s (assign k) (assign k i)).card : ℝ)) with hTk
  have hsub : s.filter (fun i => i ∉ D (m i) ∧ ThinAt s assign N θ' (D (m i)) i)
      ⊆ (Finset.range (N + 1)).biUnion Tk := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨his, hiD, k, hk, hlt⟩ := hi
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨his, hiD, hlt⟩
  have hTk_le : ∀ k, ((Tk k).card : ℝ) ≤ (θ' : ℝ) * (s.card : ℝ) := by
    intro k
    have hfib : (Tk k).card
        = ∑ a ∈ (Tk k).image (assign k), ((Tk k).filter (fun i => assign k i = a)).card :=
      Finset.card_eq_sum_card_fiberwise (fun i hi => Finset.mem_image_of_mem (assign k) hi)
    have hfibre : ∀ a ∈ (Tk k).image (assign k),
        (((Tk k).filter (fun i => assign k i = a)).card : ℝ)
          ≤ (θ' : ℝ) * ((coverClass s (assign k) a).card : ℝ) := by
      intro a ha
      set F := (Tk k).filter (fun i => assign k i = a) with hF
      have hFne : F.Nonempty := by
        obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
        exact ⟨i, Finset.mem_filter.mpr ⟨hi, hia⟩⟩
      obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image F m hFne
      have hi₀T : i₀ ∈ Tk k := (Finset.mem_filter.mp hi₀).1
      have hi₀a : assign k i₀ = a := (Finset.mem_filter.mp hi₀).2
      rw [hTk, Finset.mem_filter] at hi₀T
      obtain ⟨-, -, hlt⟩ := hi₀T
      rw [hi₀a] at hlt
      have hFsub : F ⊆ coverClass s (assign k) a \ D (m i₀) := by
        intro i hi
        have hiF := Finset.mem_filter.mp hi
        have hiT := hiF.1
        rw [hTk, Finset.mem_filter] at hiT
        refine Finset.mem_sdiff.mpr ⟨?_, fun hmem => hiT.2.1 (hmono (hmin i hi) hmem)⟩
        exact mem_coverClass.mpr ⟨hiT.1, hiF.2⟩
      calc (F.card : ℝ) ≤ ((coverClass s (assign k) a \ D (m i₀)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hFsub
        _ ≤ (θ' : ℝ) * ((coverClass s (assign k) a).card : ℝ) := hlt.le
    have hdisj : ∑ a ∈ (Tk k).image (assign k), ((coverClass s (assign k) a).card : ℝ)
        ≤ (s.card : ℝ) := by
      have hcard : ∑ a ∈ (Tk k).image (assign k), (coverClass s (assign k) a).card
          = (((Tk k).image (assign k)).biUnion (fun a => coverClass s (assign k) a)).card := by
        symm
        apply Finset.card_biUnion
        intro a _ b _ hab
        rw [Function.onFun, Finset.disjoint_left]
        intro i hia hib
        rw [mem_coverClass] at hia hib
        exact hab (hia.2.symm.trans hib.2)
      have hsub' : ((Tk k).image (assign k)).biUnion (fun a => coverClass s (assign k) a) ⊆ s := by
        intro i hi
        obtain ⟨a, -, hia⟩ := Finset.mem_biUnion.mp hi
        exact (mem_coverClass.mp hia).1
      have := Finset.card_le_card hsub'
      rw [← hcard] at this
      exact_mod_cast this
    calc ((Tk k).card : ℝ)
        = ∑ a ∈ (Tk k).image (assign k), (((Tk k).filter (fun i => assign k i = a)).card : ℝ) := by
          rw [hfib]; push_cast; rfl
      _ ≤ ∑ a ∈ (Tk k).image (assign k), (θ' : ℝ) * ((coverClass s (assign k) a).card : ℝ) :=
          Finset.sum_le_sum hfibre
      _ = (θ' : ℝ) * ∑ a ∈ (Tk k).image (assign k), ((coverClass s (assign k) a).card : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (θ' : ℝ) * (s.card : ℝ) := by gcongr
  calc ((s.filter (fun i => i ∉ D (m i) ∧ ThinAt s assign N θ' (D (m i)) i)).card : ℝ)
      ≤ (((Finset.range (N + 1)).biUnion Tk).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (N + 1), ((Tk k).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (N + 1), (θ' : ℝ) * (s.card : ℝ) := Finset.sum_le_sum fun k _ => hTk_le k
    _ = ((N : ℝ) + 1) * (θ' : ℝ) * (s.card : ℝ) := by
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
        push_cast
        ring

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A sum over a union is at most the sum of the two sums. -/
theorem sum_union_le' (s₁ s₂ : Finset ι) (f : ι → ENNReal) :
    ∑ i ∈ s₁ ∪ s₂, f i ≤ ∑ i ∈ s₁, f i + ∑ i ∈ s₂, f i := by
  rw [← Finset.sum_union_inter]
  exact le_self_add

end ThinCount


section Accounting

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **The staged bad set of a scale absorbs every bad incidence.**  A member of `s` whose shading
covers `x` but which is not retained at its own stage lies in the staged bad set of some scale. -/
theorem mem_biUnion_stagedBad {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E}
    {assign : ℕ → ι → ι} {N : ℕ} {θ : ℕ → NNReal} (D : ℕ → Finset ι) (m : ι → ℕ) {i : ι}
    (hi : i ∈ s) (hiD : i ∉ D (m i)) {x : E} (hx : x ∈ (V i).shade)
    (hbad : x ∉ goodSet s V assign N θ (D (m i)) i) :
    i ∈ (Finset.range (N + 1)).biUnion (fun k => stagedBad s V (assign k) (θ k) D m x) := by
  classical
  simp only [goodSet, Set.mem_setOf_eq, not_forall] at hbad
  obtain ⟨k, hk, hbad⟩ := hbad
  refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
  simp only [stagedBad, Finset.mem_filter, mem_fibreAt]
  exact ⟨⟨hi, hx⟩, hiD, hbad⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **The mass accounting of the deletion fixed point.**  The total shade mass exceeds the
retained dense mass by at most twice the light mass plus twice the thin-node count times the
per-member mass bound. -/
theorem sum_volume_shade_le_sum_volume_denseShade_add {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {assign : ℕ → ι → ι} {N : ℕ} {θ : ℕ → NNReal} {θ' : NNReal}
    {t : ENNReal} (hθ1 : ∀ k ≤ N, θ k < 1) {κ : ℝ}
    (hκ : ∑ k ∈ Finset.range (N + 1), (θ k : ℝ) / (1 - θ k) ≤ κ) (hκ4 : 4 * κ ≤ 1)
    {M : ENNReal} (hM : ∀ i ∈ s, volume (V i).shade ≤ M) (hMtop : M ≠ ⊤) :
    ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s \ deleted s V assign N θ θ' t, volume (denseShade s V assign N θ θ' t i).shade
        + 2 * (∑ i ∈ s.filter (fun i => volume (V i).shade < 2 * t), volume (V i).shade
          + ((N : ENNReal) + 1) * (θ' : ENNReal) * (s.card : ENNReal) * M) := by
  classical
  set D := deleted s V assign N θ θ' t with hD
  set Dc := deleteChain s V assign N θ θ' t with hDc
  set m := stage s V assign N θ θ' t with hm
  have hmono : Monotone Dc := monotone_deleteChain
  have hDcD : ∀ n, Dc n ⊆ D := deleteChain_subset_deleted
  have hnotm : ∀ i, i ∉ Dc (m i) := notMem_deleteChain_stage
  have hfin : ∀ i ∈ s, volume (V i).shade ≠ ⊤ := fun i hi => ne_top_of_le_ne_top hMtop (hM i hi)
  have hκ0 : 0 ≤ κ := by
    refine le_trans (Finset.sum_nonneg fun k hk => ?_) hκ
    have := hθ1 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have h1 : (θ k : ℝ) < 1 := by exact_mod_cast this
    exact div_nonneg (θ k).coe_nonneg (by linarith)
  set κ' : ENNReal := ENNReal.ofReal κ with hκ'
  have hκ'4 : 4 * κ' ≤ 1 := by
    have : ENNReal.ofReal (4 * κ) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hκ4
    rwa [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_one, show ENNReal.ofReal 4 = 4 by
      norm_num] at this
  -- the bad region of a member, read at its own stage
  set bad : ι → Set E := fun i => (V i).shade ∩ (goodSet s V assign N θ (Dc (m i)) i)ᶜ with hbad
  have hbad_meas : ∀ i, MeasurableSet (bad i) := fun i =>
    (V i).measurableSet_shade.inter (measurableSet_goodSet _ _).compl
  have hsplit : ∀ i, volume (V i).shade
      = massAt s V assign N θ (Dc (m i)) i + volume (bad i) := by
    intro i
    have := measure_inter_add_sdiff (μ := volume) (V i).shade
      (measurableSet_goodSet (s := s) (V := V) (assign := assign) (N := N) (θ := θ) (Dc (m i)) i)
    rw [Set.sdiff_eq] at this
    exact this.symm
  -- the light, thin and small members
  set light : ι → Prop := fun i => volume (V i).shade < 2 * t with hlight
  set Lset := s.filter light with hLset
  set Tset := s.filter (fun i => i ∈ D ∧ ¬ light i ∧ ThinAt s assign N θ' (Dc (m i)) i) with hTset
  set Bset := s.filter (fun i => i ∈ D ∧ ¬ light i ∧ ¬ ThinAt s assign N θ' (Dc (m i)) i)
    with hBset
  set sD := s.filter (fun i => i ∈ D) with hsD
  set H := s \ D with hH
  set W := ∑ i ∈ sD, volume (V i).shade with hW
  set ℓ := ∑ i ∈ Lset, volume (V i).shade with hℓ
  set Tm := ((N : ENNReal) + 1) * (θ' : ENNReal) * (s.card : ENNReal) * M with hTm
  -- (1) the deleted members are light, thin or small
  have hsD_sub : sD ⊆ Lset ∪ Tset ∪ Bset := by
    intro i hi
    rw [hsD, Finset.mem_filter] at hi
    obtain ⟨his, hiD⟩ := hi
    by_cases hl : light i
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨his, hl⟩))
    · by_cases hth : ThinAt s assign N θ' (Dc (m i)) i
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨his, hiD, hl, hth⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨his, hiD, hl, hth⟩)
  have hW_le : W ≤ ℓ + ∑ i ∈ Tset, volume (V i).shade + ∑ i ∈ Bset, volume (V i).shade := by
    calc W ≤ ∑ i ∈ Lset ∪ Tset ∪ Bset, volume (V i).shade :=
          Finset.sum_le_sum_of_subset_of_nonneg hsD_sub (fun _ _ _ => zero_le)
      _ ≤ ∑ i ∈ Lset ∪ Tset, volume (V i).shade + ∑ i ∈ Bset, volume (V i).shade :=
          sum_union_le' _ _ _
      _ ≤ ℓ + ∑ i ∈ Tset, volume (V i).shade + ∑ i ∈ Bset, volume (V i).shade := by
          gcongr
          exact sum_union_le' _ _ _
  -- (3) the thin members
  have hT_le : ∑ i ∈ Tset, volume (V i).shade ≤ Tm := by
    have hcount : ((Tset.card : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * (θ' : ℝ) * (s.card : ℝ) := by
      refine le_trans ?_ (card_stagedThin_le s assign N θ' Dc hmono m)
      exact_mod_cast Finset.card_le_card (fun i hi => by
        rw [hTset, Finset.mem_filter] at hi
        exact Finset.mem_filter.mpr ⟨hi.1, hnotm i, hi.2.2.2⟩)
    have hcountE : (Tset.card : ENNReal)
        ≤ ((N : ENNReal) + 1) * (θ' : ENNReal) * (s.card : ENNReal) := by
      have h := ENNReal.ofReal_le_ofReal hcount
      rw [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast,
        ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal] at h
      exact h
    calc ∑ i ∈ Tset, volume (V i).shade ≤ ∑ _i ∈ Tset, M :=
          Finset.sum_le_sum fun i hi => hM i (Finset.mem_filter.mp hi).1
      _ = (Tset.card : ENNReal) * M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Tm := by rw [hTm]; gcongr
  -- (4) the small members are dominated by their bad region
  have hB_le : ∀ i ∈ Bset, volume (V i).shade ≤ 2 * volume (bad i) := by
    intro i hi
    rw [hBset, Finset.mem_filter] at hi
    obtain ⟨his, hiD, hnl, hnth⟩ := hi
    have hstep := mem_deleteStep_stage_of_mem_deleted (s := s) (V := V) (assign := assign) (N := N)
      (θ := θ) (θ' := θ') (t := t) hiD
    rw [mem_deleteStep] at hstep
    have hsmall : massAt s V assign N θ (Dc (m i)) i < t := by
      rcases hstep.2 with h | h | h
      · exact absurd h hnl
      · exact absurd h hnth
      · exact h
    have h2t : 2 * t ≤ volume (V i).shade := not_lt.mp hnl
    have hsp := hsplit i
    have hne := hfin i his
    -- `2 |Y| = 2 massAt + 2 bad ≤ 2 t + 2 bad ≤ |Y| + 2 bad`
    have h1 : volume (V i).shade + volume (V i).shade
        ≤ volume (V i).shade + 2 * volume (bad i) := by
      calc volume (V i).shade + volume (V i).shade
          = 2 * massAt s V assign N θ (Dc (m i)) i + 2 * volume (bad i) := by
            rw [hsp]; ring
        _ ≤ 2 * t + 2 * volume (bad i) := by gcongr
        _ ≤ volume (V i).shade + 2 * volume (bad i) := by gcongr
    exact (ENNReal.add_le_add_iff_left hne).mp h1
  -- (5) the survivors
  have hH_split : ∑ i ∈ H, volume (V i).shade
      = ∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade + ∑ i ∈ H, volume (bad i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hH, Finset.mem_sdiff] at hi
    rw [hsplit i, volume_denseShade_of_notMem hi.1 hi.2]
    have : Dc (m i) = D := deleteChain_stage_of_notMem hi.2
    rw [this]
  -- (6) the layer cake: bad incidences against the deleted part of the fibre
  have hlayer : ∀ S : Finset ι, S ⊆ s → ∑ i ∈ S, volume (bad i) ≤ κ' * W := by
    intro S hS
    have hlc := MeasureTheory.sum_measure_inter_eq_setLIntegral_card_filter (μ := volume) S
      (fun i _ => hbad_meas i) Set.univ
    simp only [Set.inter_univ, Measure.restrict_univ] at hlc
    have hlc2 := MeasureTheory.sum_measure_inter_eq_setLIntegral_card_filter (μ := volume) sD
      (fun i _ => (V i).measurableSet_shade) Set.univ
    simp only [Set.inter_univ, Measure.restrict_univ] at hlc2
    rw [hlc]
    have hW' : W = ∫⁻ x, ((fibreAt s V x ∩ D).card : ENNReal) := by
      rw [hW, hlc2]
      congr 1
      funext x
      congr 2
      ext i
      simp only [Finset.mem_filter, hsD, Finset.mem_inter, mem_fibreAt]
      tauto
    have hpt : ∀ x, ((S.filter (fun i => x ∈ bad i)).card : ENNReal)
        ≤ κ' * ((fibreAt s V x ∩ D).card : ENNReal) := by
      intro x
      set X := (Finset.range (N + 1)).biUnion (fun k => stagedBad s V (assign k) (θ k) Dc m x)
        with hX
      have hsubX : S.filter (fun i => x ∈ bad i) ⊆ X := by
        intro i hi
        rw [Finset.mem_filter] at hi
        obtain ⟨hiS, hxi⟩ := hi
        exact mem_biUnion_stagedBad Dc m (hS hiS) (hnotm i) hxi.1 hxi.2
      have hXle : (X.card : ℝ) ≤ κ * ((fibreAt s V x ∩ D).card : ℝ) := by
        calc (X.card : ℝ)
            ≤ ∑ k ∈ Finset.range (N + 1), ((stagedBad s V (assign k) (θ k) Dc m x).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ k ∈ Finset.range (N + 1),
                ((θ k : ℝ) / (1 - θ k)) * ((fibreAt s V x ∩ D).card : ℝ) :=
              Finset.sum_le_sum fun k hk => card_stagedBad_le s V (assign k)
                (hθ1 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) Dc hmono D hDcD m x
          _ = (∑ k ∈ Finset.range (N + 1), (θ k : ℝ) / (1 - θ k)) *
                ((fibreAt s V x ∩ D).card : ℝ) := by
              rw [Finset.sum_mul]
          _ ≤ κ * ((fibreAt s V x ∩ D).card : ℝ) := by gcongr
      have hXleE : (X.card : ENNReal) ≤ κ' * ((fibreAt s V x ∩ D).card : ENNReal) := by
        have h := ENNReal.ofReal_le_ofReal hXle
        rwa [ENNReal.ofReal_natCast, ENNReal.ofReal_mul hκ0, ENNReal.ofReal_natCast] at h
      calc ((S.filter (fun i => x ∈ bad i)).card : ENNReal) ≤ (X.card : ENNReal) := by
            exact_mod_cast Finset.card_le_card hsubX
        _ ≤ κ' * ((fibreAt s V x ∩ D).card : ENNReal) := hXleE
    refine le_trans (lintegral_mono (g := fun x => κ' * ((fibreAt s V x ∩ D).card : ENNReal))
      fun x => ?_) ?_
    · convert hpt x using 3
      ext i
      simp only [Finset.mem_filter]
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hW']
  -- (7) assemble
  have hBH_disj : Disjoint Bset H := by
    rw [Finset.disjoint_left]
    intro i hiB hiH
    rw [hBset, Finset.mem_filter] at hiB
    rw [hH, Finset.mem_sdiff] at hiH
    exact hiH.2 hiB.2.1
  have hBHsub : Bset ∪ H ⊆ s := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_sdiff.mp h).1
  have hbadBH : ∑ i ∈ Bset, volume (bad i) + ∑ i ∈ H, volume (bad i) ≤ κ' * W := by
    rw [← Finset.sum_union hBH_disj]
    exact hlayer _ hBHsub
  have hBsum : ∑ i ∈ Bset, volume (V i).shade ≤ 2 * ∑ i ∈ Bset, volume (bad i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hB_le
  have hWfin : W ≠ ⊤ := by
    rw [hW]
    exact (ENNReal.sum_lt_top.2 fun i hi => lt_top_iff_ne_top.mpr
      (hfin i (Finset.mem_filter.mp hi).1)).ne
  -- `W ≤ ℓ + T + 2 κ' W`, hence `W ≤ 2 (ℓ + T)`
  have hW1 : W ≤ ℓ + Tm + 2 * (κ' * W) := by
    calc W ≤ ℓ + ∑ i ∈ Tset, volume (V i).shade + ∑ i ∈ Bset, volume (V i).shade := hW_le
      _ ≤ ℓ + Tm + 2 * ∑ i ∈ Bset, volume (bad i) := by gcongr
      _ ≤ ℓ + Tm + 2 * (κ' * W) := by
          gcongr
          exact le_trans le_self_add hbadBH
  have hW2 : W ≤ 2 * (ℓ + Tm) := by
    have h1 : W + W ≤ 2 * (ℓ + Tm) + W := by
      calc W + W = 2 * W := by ring
        _ ≤ 2 * (ℓ + Tm + 2 * (κ' * W)) := by gcongr
        _ = 2 * (ℓ + Tm) + (4 * κ') * W := by ring
        _ ≤ 2 * (ℓ + Tm) + 1 * W := by gcongr
        _ = 2 * (ℓ + Tm) + W := by rw [one_mul]
    exact (ENNReal.add_le_add_iff_right hWfin).mp h1
  -- total
  have htotal : ∑ i ∈ s, volume (V i).shade = W + ∑ i ∈ H, volume (V i).shade := by
    rw [hW, hsD, hH]
    have : s \ D = s.filter (fun i => i ∉ D) := by
      ext i; simp [Finset.mem_sdiff, Finset.mem_filter]
    rw [this]
    exact (Finset.sum_filter_add_sum_filter_not s (fun i => i ∈ D) _).symm
  calc ∑ i ∈ s, volume (V i).shade
      = W + ∑ i ∈ H, volume (V i).shade := htotal
    _ ≤ (ℓ + ∑ i ∈ Tset, volume (V i).shade + ∑ i ∈ Bset, volume (V i).shade)
          + (∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade
            + ∑ i ∈ H, volume (bad i)) := by
        rw [hH_split]; gcongr
    _ ≤ (ℓ + Tm + 2 * ∑ i ∈ Bset, volume (bad i))
          + (∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade
            + ∑ i ∈ H, volume (bad i)) := by
        gcongr
    _ ≤ ∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade
          + (ℓ + Tm + 2 * (∑ i ∈ Bset, volume (bad i) + ∑ i ∈ H, volume (bad i))) := by
        have : (ℓ + Tm + 2 * ∑ i ∈ Bset, volume (bad i))
            + (∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade + ∑ i ∈ H, volume (bad i))
            = ∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade
              + (ℓ + Tm + (2 * ∑ i ∈ Bset, volume (bad i) + ∑ i ∈ H, volume (bad i))) := by ring
        rw [this]
        gcongr
        calc 2 * ∑ i ∈ Bset, volume (bad i) + ∑ i ∈ H, volume (bad i)
            ≤ 2 * ∑ i ∈ Bset, volume (bad i) + 2 * ∑ i ∈ H, volume (bad i) := by
              gcongr
              exact le_mul_of_one_le_left zero_le (by norm_num)
          _ = 2 * (∑ i ∈ Bset, volume (bad i) + ∑ i ∈ H, volume (bad i)) := by ring
    _ ≤ ∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade + (ℓ + Tm + 2 * (κ' * W)) := by
        gcongr
    _ ≤ ∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade
          + (ℓ + Tm + 2 * (κ' * (2 * (ℓ + Tm)))) := by gcongr
    _ = ∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade
          + (ℓ + Tm + (4 * κ') * (ℓ + Tm)) := by ring
    _ ≤ ∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade
          + (ℓ + Tm + 1 * (ℓ + Tm)) := by gcongr
    _ = ∑ i ∈ H, volume (denseShade s V assign N θ θ' t i).shade + 2 * (ℓ + Tm) := by ring

end Accounting

section Structure

omit [Nontrivial E] [BorelSpace E] in
/-- **GWZ Definition 2.2 for the dense selection.**  The survivors of the deletion fixed point,
with the dense shading, are uniform at the constant `C'` as soon as `C'` absorbs the class
density `θ k / 2` at every scale and the node density `θ'`. -/
theorem nonempty_shadedUniformTubeSet_denseShade {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C)
    (θ : ℕ → NNReal) (θ' : NNReal) (t : ENNReal)
    (hθ : ∀ k ≤ N, 2 * ∑ k' ∈ Finset.Ioc k N, (θ k' : ℝ) ≤ θ k)
    (C' : NNReal) (hCC' : C ≤ C') (hCθ : ∀ k ≤ N, (C : ℝ) ≤ ((θ k : ℝ) / 2) * C')
    (hCθ' : (C : ℝ) ≤ (θ' : ℝ) * C') :
    Nonempty (ShadedUniformTubeSet (s \ deleted s V 𝒱.tubeUniform.cover.assign N θ θ' t)
      (denseShade s V 𝒱.tubeUniform.cover.assign N θ θ' t) N C') := by
  classical
  set A := 𝒱.tubeUniform.cover.assign with hA
  set D := deleted s V A N θ θ' t with hD
  set H := s \ D with hH
  set V' := denseShade s V A N θ θ' t with hV'
  have hHs : H ⊆ s := Finset.sdiff_subset
  have hnest : ∀ k l, k ≤ l → l ≤ N → ∀ i ∈ s, ∀ j ∈ s, A l i = A l j → A k i = A k j :=
    fun k l hkl hl i hi j hj h => 𝒱.tubeUniform.cover.assign_eq_of_le hkl hl hi hj h
  -- the shade union of the dense family lies in the old one
  have hunion : ∀ x ∈ (⋃ i ∈ H, (V' i).shade), x ∈ (⋃ i ∈ s, (V i).shade) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hHs hi, denseShade_shade_subset i hxi⟩
  -- the restricted cover, with the uninhabited nodes removed
  let cover : GridCoverSystem H (fun i => (V' i).toTube) N :=
    restrictCoverInhabited 𝒱.tubeUniform.cover hHs
  have hcover_assign : cover.assign = A := rfl
  let 𝒰 : UniformTubeSet H (fun i => (V' i).toTube) N C' :=
    { cover := cover
      branchingN := 𝒱.tubeUniform.branchingN
      tube_injOn := fun k hk => (𝒱.tubeUniform.tube_injOn k hk).mono (by
        intro a ha
        exact ((mem_indexSet_restrictCoverInhabited _ _).mp ha).1)
      boundedOverlap := by
        intro k hk W
        refine le_trans ?_ (le_trans (𝒱.tubeUniform.boundedOverlap k hk W) hCC')
        refine Nat.cast_le.mpr (Finset.card_le_card ?_)
        intro a ha
        rw [Finset.mem_filter] at ha ⊢
        obtain ⟨ha0, i, hi, h1, h2⟩ := ha
        exact ⟨((mem_indexSet_restrictCoverInhabited _ _).mp ha0).1, i, hHs hi, h1, h2⟩
      card_class_le := by
        intro k hk a ha
        have ha' : a ∈ 𝒱.tubeUniform.cover.indexSet k :=
          ((mem_indexSet_restrictCoverInhabited _ _).mp ha).1
        calc ((coverClass H (cover.assign k) a).card : NNReal)
            ≤ ((coverClass s (𝒱.tubeUniform.cover.assign k) a).card : NNReal) := by
              exact_mod_cast Finset.card_le_card (coverClass_subset_of_subset hHs _ _)
          _ ≤ C * 𝒱.tubeUniform.branchingN k := 𝒱.tubeUniform.card_class_le k hk a ha'
          _ ≤ C' * 𝒱.tubeUniform.branchingN k := mul_le_mul_of_nonneg_right hCC' zero_le
      le_card_class := by
        intro k hk a ha
        have ha' : a ∈ 𝒱.tubeUniform.cover.indexSet k :=
          ((mem_indexSet_restrictCoverInhabited _ _).mp ha).1
        obtain ⟨i, hi, hia⟩ := ((mem_indexSet_restrictCoverInhabited _ _).mp ha).2
        have hiD : i ∉ D := (Finset.mem_sdiff.mp hi).2
        have his : i ∈ s := (Finset.mem_sdiff.mp hi).1
        obtain ⟨-, hthin, -⟩ := survivor_spec (s := s) (V := V) (assign := A) (N := N) (θ := θ)
          (θ' := θ') (t := t) his hiD
        have hdense : (θ' : ℝ) * ((coverClass s (A k) (A k i)).card : ℝ)
            ≤ ((coverClass s (A k) (A k i) \ D).card : ℝ) := by
          by_contra hcon
          exact hthin ⟨k, hk, lt_of_not_ge hcon⟩
        have hia' : A k i = a := hia
        rw [hia'] at hdense
        have hHclass : coverClass H (cover.assign k) a = coverClass s (A k) a \ D := by
          ext j
          simp only [mem_coverClass, Finset.mem_sdiff, hH, hcover_assign]
          tauto
        have h1 : ((𝒱.tubeUniform.branchingN k : NNReal) : ℝ)
            ≤ (C : ℝ) * ((coverClass s (A k) a).card : ℝ) := by
          exact_mod_cast 𝒱.tubeUniform.le_card_class k hk a ha'
        have h2 : (C : ℝ) * ((coverClass s (A k) a).card : ℝ)
            ≤ (C' : ℝ) * ((coverClass s (A k) a \ D).card : ℝ) := by
          calc (C : ℝ) * ((coverClass s (A k) a).card : ℝ)
              ≤ ((θ' : ℝ) * C') * ((coverClass s (A k) a).card : ℝ) := by
                gcongr
            _ = (C' : ℝ) * ((θ' : ℝ) * ((coverClass s (A k) a).card : ℝ)) := by ring
            _ ≤ (C' : ℝ) * ((coverClass s (A k) a \ D).card : ℝ) := by gcongr
        rw [hHclass]
        exact_mod_cast h1.trans h2 }
  refine ⟨{
    tubeUniform := 𝒰
    branchingN := 𝒱.branchingN
    localN := 𝒱.localN
    card_shadeClass_le := ?_
    le_card_shadeClass := ?_
    branchingN_le := ?_
    le_branchingN := ?_ }⟩
  · intro x hx k hk i hi hxi
    have hx' := hunion x hx
    have hclass := shadeClass_denseShade (s := s) (V := V) (assign := A) (N := N) (θ := θ)
      (θ' := θ') (t := t) k (A k i) x
    change ((shadeClass H V' (A k) (A k i) x).card : NNReal) ≤ C' * 𝒱.localN x k
    rw [hclass]
    calc ((shadeClass s V (A k) (A k i) x ∩
            retainedAt s V A N θ D x).card : NNReal)
        ≤ ((shadeClass s V (A k) (A k i) x).card : NNReal) := by
          exact_mod_cast Finset.card_le_card Finset.inter_subset_left
      _ ≤ C * 𝒱.localN x k :=
          𝒱.card_shadeClass_le x hx' k hk i (hHs hi) (denseShade_shade_subset i hxi)
      _ ≤ C' * 𝒱.localN x k := mul_le_mul_of_nonneg_right hCC' zero_le
  · intro x hx k hk i hi hxi
    have hx' := hunion x hx
    have hclass := shadeClass_denseShade (s := s) (V := V) (assign := A) (N := N) (θ := θ)
      (θ' := θ') (t := t) k (A k i) x
    change 𝒱.localN x k ≤ C' * ((shadeClass H V' (A k) (A k i) x).card : NNReal)
    rw [hclass]
    have hiR : i ∈ retainedAt s V A N θ D x := mem_denseShade_shade.mp hxi
    have hbr := card_shadeClass_inter_retainedAt_ge s V A N hnest θ hθ D x hiR hk
    have h1 : ((𝒱.localN x k : NNReal) : ℝ)
        ≤ (C : ℝ) * ((shadeClass s V (A k) (A k i) x).card : ℝ) := by
      exact_mod_cast 𝒱.le_card_shadeClass x hx' k hk i (hHs hi) (denseShade_shade_subset i hxi)
    have h2 : (C : ℝ) * ((shadeClass s V (A k) (A k i) x).card : ℝ)
        ≤ (C' : ℝ) * ((shadeClass s V (A k) (A k i) x ∩ retainedAt s V A N θ D x).card : ℝ) := by
      calc (C : ℝ) * ((shadeClass s V (A k) (A k i) x).card : ℝ)
          ≤ (((θ k : ℝ) / 2) * C') * ((shadeClass s V (A k) (A k i) x).card : ℝ) := by
            gcongr
            exact hCθ k hk
        _ = (C' : ℝ) * (((θ k : ℝ) / 2) * ((shadeClass s V (A k) (A k i) x).card : ℝ)) := by
            ring
        _ ≤ (C' : ℝ) * ((shadeClass s V (A k) (A k i) x ∩
              retainedAt s V A N θ D x).card : ℝ) := by
            gcongr
    exact_mod_cast h1.trans h2
  · intro x hx k hk
    exact (𝒱.branchingN_le x (hunion x hx) k hk).trans
      (mul_le_mul_of_nonneg_right hCC' zero_le)
  · intro x hx k hk
    exact (𝒱.le_branchingN x (hunion x hx) k hk).trans
      (mul_le_mul_of_nonneg_right hCC' zero_le)

end Structure


section Selection

/-- **The geometric class-density thresholds** `θ k = 4^{-k} / 12`. -/
noncomputable def denseTheta (k : ℕ) : NNReal := (1 / 12 : NNReal) * (1 / 4 : NNReal) ^ k

theorem denseTheta_coe (k : ℕ) :
    ((denseTheta k : NNReal) : ℝ) = (1 / 12 : ℝ) * (1 / 4 : ℝ) ^ k := by
  simp [denseTheta]

theorem denseTheta_pos (k : ℕ) : 0 < denseTheta k := by
  unfold denseTheta; positivity

theorem denseTheta_le (k : ℕ) : denseTheta k ≤ 1 / 12 := by
  rw [← NNReal.coe_le_coe, denseTheta_coe]
  have : (1 / 4 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  push_cast
  nlinarith

theorem denseTheta_lt_one (k : ℕ) : denseTheta k < 1 :=
  lt_of_le_of_lt (denseTheta_le k) (by norm_num)

theorem denseTheta_anti {k l : ℕ} (hkl : k ≤ l) : denseTheta l ≤ denseTheta k := by
  rw [← NNReal.coe_le_coe, denseTheta_coe, denseTheta_coe]
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hkl
  nlinarith

theorem sum_Ioc_quarter_pow (k N : ℕ) (hkN : k ≤ N) :
    ∑ k' ∈ Finset.Ioc k N, (1 / 4 : ℝ) ^ k' = ((1 / 4 : ℝ) ^ k - (1 / 4 : ℝ) ^ N) / 3 := by
  induction N, hkN using Nat.le_induction with
  | base => simp
  | succ N hkN ih =>
    rw [Finset.sum_Ioc_succ_top hkN, ih]
    ring

theorem two_mul_sum_Ioc_denseTheta_le (k N : ℕ) :
    2 * ∑ k' ∈ Finset.Ioc k N, (denseTheta k' : ℝ) ≤ denseTheta k := by
  by_cases hkN : k ≤ N
  · simp only [denseTheta_coe, ← Finset.mul_sum]
    rw [sum_Ioc_quarter_pow k N hkN]
    have h1 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ N := by positivity
    have h2 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k := by positivity
    nlinarith
  · have : Finset.Ioc k N = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [this, Finset.sum_empty, mul_zero]
    exact (denseTheta k).coe_nonneg

theorem sum_range_denseTheta_div_le (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (denseTheta k : ℝ) / (1 - denseTheta k) ≤ 1 / 4 := by
  have hterm : ∀ k, (denseTheta k : ℝ) / (1 - denseTheta k)
      ≤ (12 / 11 : ℝ) * (1 / 12) * (1 / 4 : ℝ) ^ k := by
    intro k
    have h1 : (denseTheta k : ℝ) ≤ 1 / 12 := by exact_mod_cast denseTheta_le k
    have h2 : (11 / 12 : ℝ) ≤ 1 - denseTheta k := by linarith
    have h3 : (0 : ℝ) ≤ (denseTheta k : ℝ) := (denseTheta k).coe_nonneg
    calc (denseTheta k : ℝ) / (1 - denseTheta k) ≤ (denseTheta k : ℝ) / (11 / 12) :=
          div_le_div_of_nonneg_left h3 (by norm_num) h2
      _ = (12 / 11 : ℝ) * (denseTheta k : ℝ) := by ring
      _ = (12 / 11 : ℝ) * (1 / 12) * (1 / 4 : ℝ) ^ k := by rw [denseTheta_coe]; ring
  have hgeom : ∑ k ∈ Finset.range (N + 1), (1 / 4 : ℝ) ^ k ≤ 4 / 3 := by
    rw [geom_sum_eq (by norm_num) (N + 1)]
    have : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (N + 1) := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    linarith
  calc ∑ k ∈ Finset.range (N + 1), (denseTheta k : ℝ) / (1 - denseTheta k)
      ≤ ∑ k ∈ Finset.range (N + 1), (12 / 11 : ℝ) * (1 / 12) * (1 / 4 : ℝ) ^ k :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (12 / 11 : ℝ) * (1 / 12) * ∑ k ∈ Finset.range (N + 1), (1 / 4 : ℝ) ^ k := by
        rw [Finset.mul_sum]
    _ ≤ (12 / 11 : ℝ) * (1 / 12) * (4 / 3) := by gcongr
    _ ≤ 1 / 4 := by norm_num

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*} [DecidableEq ι]

/-- **The dense selection constant.** -/
noncomputable def denseConst (N : ℕ) (C θ' : NNReal) : NNReal := 24 * 4 ^ N * C + C / θ'

omit [Nontrivial E] [BorelSpace E] [DecidableEq ι] in
/-- **The class-dense heavy selection.**  From a uniform shaded family, a subfamily and a shrunken
shading that are again uniform (at `denseConst N C θ'`), every member of which carries at least
`t` of shade, and whose total mass is short of the original by at most twice the light mass plus
twice the thin-node count times the per-member bound `M`. -/
theorem exists_denseSelection {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C) {θ' : NNReal} (hθ' : 0 < θ') (t : ENNReal)
    {M : ENNReal} (hM : ∀ i ∈ s, volume (V i).shade ≤ M) (hMtop : M ≠ ⊤) :
    ∃ s' ⊆ s, ∃ V' : ι → ShadedTube δ E,
      (∀ i, (V' i).toTube = (V i).toTube) ∧ (∀ i, (V' i).shade ⊆ (V i).shade) ∧
      (∀ i ∈ s', t ≤ volume (V' i).shade) ∧
      Nonempty (ShadedUniformTubeSet s' V' N (denseConst N C θ')) ∧
      ∑ i ∈ s, volume (V i).shade ≤ ∑ i ∈ s', volume (V' i).shade
        + 2 * (∑ i ∈ s.filter (fun i => volume (V i).shade < 2 * t), volume (V i).shade
          + ((N : ENNReal) + 1) * (θ' : ENNReal) * (s.card : ENNReal) * M) := by
  classical
  set A := 𝒱.tubeUniform.cover.assign with hA
  refine ⟨s \ deleted s V A N denseTheta θ' t, Finset.sdiff_subset,
    denseShade s V A N denseTheta θ' t, fun i => rfl, denseShade_shade_subset, ?_, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_sdiff] at hi
    rw [volume_denseShade_of_notMem hi.1 hi.2]
    exact (survivor_spec hi.1 hi.2).2.2
  · -- the structure
    have hC' : C ≤ denseConst N C θ' := by
      unfold denseConst
      have h1 : (1 : NNReal) ≤ 24 * 4 ^ N := by
        calc (1 : NNReal) ≤ 24 := by norm_num
          _ = 24 * 1 := by ring
          _ ≤ 24 * 4 ^ N := by gcongr; exact one_le_pow₀ (by norm_num)
      calc C = 1 * C := (one_mul C).symm
        _ ≤ 24 * 4 ^ N * C := by gcongr
        _ ≤ 24 * 4 ^ N * C + C / θ' := le_self_add
    have hCθ : ∀ k ≤ N, (C : ℝ) ≤ ((denseTheta k : ℝ) / 2) * (denseConst N C θ' : ℝ) := by
      intro k hk
      have hθk : (denseTheta N : ℝ) ≤ denseTheta k := by exact_mod_cast denseTheta_anti hk
      have hθN : (denseTheta N : ℝ) = (1 / 12 : ℝ) * (1 / 4 : ℝ) ^ N := denseTheta_coe N
      have hconst : (denseConst N C θ' : ℝ) = 24 * 4 ^ N * C + C / θ' := by
        simp [denseConst]
      have hdiv : (0 : ℝ) ≤ (C : ℝ) / θ' := by positivity
      have hpow : ((1 / 4 : ℝ) ^ N) * (4 : ℝ) ^ N = 1 := by
        rw [← mul_pow]; norm_num
      calc (C : ℝ) = ((denseTheta N : ℝ) / 2) * (24 * 4 ^ N * C) := by
            rw [hθN]; nlinarith [hpow]
        _ ≤ ((denseTheta N : ℝ) / 2) * (24 * 4 ^ N * C + C / θ') := by
            gcongr
            exact le_add_of_nonneg_right hdiv
        _ = ((denseTheta N : ℝ) / 2) * (denseConst N C θ' : ℝ) := by rw [hconst]
        _ ≤ ((denseTheta k : ℝ) / 2) * (denseConst N C θ' : ℝ) := by gcongr
    have hCθ' : (C : ℝ) ≤ (θ' : ℝ) * (denseConst N C θ' : ℝ) := by
      have hconst : (denseConst N C θ' : ℝ) = 24 * 4 ^ N * C + C / θ' := by
        simp [denseConst]
      have hθ'R : (0 : ℝ) < θ' := by exact_mod_cast hθ'
      rw [hconst, mul_add, mul_div_cancel₀ _ hθ'R.ne']
      have : (0 : ℝ) ≤ (θ' : ℝ) * (24 * 4 ^ N * C) := by positivity
      linarith
    exact nonempty_shadedUniformTubeSet_denseShade 𝒱 denseTheta θ' t
      (fun k _ => two_mul_sum_Ioc_denseTheta_le k N) _ hC' hCθ hCθ'
  · exact sum_volume_shade_le_sum_volume_denseShade_add (fun k _ => denseTheta_lt_one k)
      (sum_range_denseTheta_div_le N) (by norm_num) hM hMtop

end Selection

end ShadedTube

namespace Kakeya.VeryNotSticky

open Topology Filter

/-- A power beats a logarithm: `δ^ε (a + b log(1/δ)) ≤ c` for all small `δ`. -/
theorem eventually_rpow_mul_add_log_le {ε : ℝ} (hε : 0 < ε) (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, (d : ℝ) ^ ε * (a + b * Real.log (1 / (d : ℝ))) ≤ c := by
  have hsmall : ∀ᶠ d : NNReal in 𝓝[>] 0, d < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd
    exact hd.2
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_nnreal_mul_rpow_le_const (Real.toNNReal |a|) (Real.toNNReal (c / 2))
      (by simpa using hc) hε,
    eventually_nnreal_mul_rpow_le_const (Real.toNNReal (|b| * (2 / ε))) (Real.toNNReal (c / 2))
      (by simpa using hc) hε2] with d hd0 hd1 ha hb
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show (0 : NNReal) < d from hd0)
  have hdR1 : (d : ℝ) < 1 := by exact_mod_cast hd1
  have haR : |a| * (d : ℝ) ^ ε ≤ c / 2 := by
    have h := NNReal.coe_le_coe.mpr ha
    rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ (abs_nonneg a),
      Real.coe_toNNReal _ (by linarith)] at h
    exact h
  have hbR : |b| * (2 / ε) * (d : ℝ) ^ (ε / 2) ≤ c / 2 := by
    have h := NNReal.coe_le_coe.mpr hb
    rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (by linarith)] at h
    exact h
  -- `log (1/d) ≤ (1/d)^{ε/2} / (ε/2)`
  have hlog : Real.log (1 / (d : ℝ)) ≤ (1 / (d : ℝ)) ^ (ε / 2) / (ε / 2) :=
    Real.log_le_rpow_div (by positivity) hε2
  have hlog0 : 0 ≤ Real.log (1 / (d : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hdpos]; linarith
  have hdε : (0 : ℝ) ≤ (d : ℝ) ^ ε := by positivity
  have hprod : (d : ℝ) ^ ε * (1 / (d : ℝ)) ^ (ε / 2) = (d : ℝ) ^ (ε / 2) := by
    rw [one_div, Real.inv_rpow hdpos.le, ← Real.rpow_neg hdpos.le, ← Real.rpow_add hdpos]
    congr 1; ring
  have hdivrw : (1 / (d : ℝ)) ^ (ε / 2) / (ε / 2) = (2 / ε) * (1 / (d : ℝ)) ^ (ε / 2) := by
    field_simp
  calc (d : ℝ) ^ ε * (a + b * Real.log (1 / (d : ℝ)))
      ≤ (d : ℝ) ^ ε * (|a| + |b| * Real.log (1 / (d : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_abs_self a) (mul_le_mul_of_nonneg_right (le_abs_self b) hlog0)) hdε
    _ ≤ (d : ℝ) ^ ε * (|a| + |b| * ((1 / (d : ℝ)) ^ (ε / 2) / (ε / 2))) := by
        gcongr
    _ = |a| * (d : ℝ) ^ ε + |b| * (2 / ε) * ((d : ℝ) ^ ε * (1 / (d : ℝ)) ^ (ε / 2)) := by
        rw [hdivrw]
        ring
    _ = |a| * (d : ℝ) ^ ε + |b| * (2 / ε) * (d : ℝ) ^ (ε / 2) := by rw [hprod]
    _ ≤ c / 2 + c / 2 := add_le_add haR hbR
    _ = c := by ring


/-- **The band pigeonhole's refinement constant beats `δ^{η'/4}`.**  At floor `δ^{2η-η'}/2` and
Markov fraction `δ^{η-η'}/2`, the constant of `Kakeya.VeryNotSticky.exists_shadingBand` is at
least `(1/2) · (2 + (2η-η') log₂(1/δ))⁻¹`, and a power beats the logarithm. -/
theorem denseBand_const_ge {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {η η' : ℝ} (hη' : 0 < η')
    (hηη' : η' < η)
    (hlog : (δ : ℝ) ^ (η' / 4) * (2 + ((2 * η - η') / Real.log 2) * Real.log (1 / (δ : ℝ)))
      ≤ 1 / 2) :
    δ ^ (η' / 4) ≤ (1 - δ ^ (η - η') / 2) *
      ((1 + Real.logb 2 (((δ ^ (2 * η - η') / 2 : NNReal) : ℝ)⁻¹)).toNNReal)⁻¹ := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1δ : 0 ≤ Real.log (1 / (δ : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδR]; linarith
  -- the logarithm of the inverse floor
  set X : ℝ := 1 + Real.logb 2 (((δ ^ (2 * η - η') / 2 : NNReal) : ℝ)⁻¹) with hX
  have hXeq : X = 2 + ((2 * η - η') / Real.log 2) * Real.log (1 / (δ : ℝ)) := by
    rw [hX]
    have hcoe : (((δ ^ (2 * η - η') / 2 : NNReal) : ℝ)⁻¹)
        = 2 * (1 / (δ : ℝ)) ^ (2 * η - η') := by
      rw [NNReal.coe_div, NNReal.coe_rpow]
      push_cast
      rw [one_div, Real.inv_rpow hδR.le]
      field_simp
    rw [hcoe, Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num),
      Real.logb_rpow_eq_mul_logb_of_pos (by positivity), Real.logb, div_eq_mul_inv]
    ring
  have hX2 : 2 ≤ X := by
    rw [hXeq]
    have : 0 ≤ ((2 * η - η') / Real.log 2) * Real.log (1 / (δ : ℝ)) := by
      apply mul_nonneg _ hlog1δ
      apply div_nonneg _ hlog2.le
      linarith
    linarith
  have hXpos : 0 < X := by linarith
  have hXnn : (X.toNNReal : ℝ) = X := Real.coe_toNNReal X hXpos.le
  have hXne : X.toNNReal ≠ 0 := by
    intro h
    have := congrArg (fun y : NNReal => (y : ℝ)) h
    simp only [hXnn, NNReal.coe_zero] at this
    linarith
  -- the Markov fraction is at most `1/2`
  have hq : δ ^ (η - η') / 2 ≤ 1 / 2 := by
    have h1 : δ ^ (η - η') ≤ 1 := NNReal.rpow_le_one hδ1 (by linarith)
    exact div_le_div_of_nonneg_right h1 (by norm_num)
  have hhalf : (1 / 2 : NNReal) ≤ 1 - δ ^ (η - η') / 2 := by
    have h2 : δ ^ (η - η') / 2 + 1 / 2 ≤ 1 := by
      calc δ ^ (η - η') / 2 + 1 / 2 ≤ 1 / 2 + 1 / 2 := by gcongr
        _ = 1 := by norm_num
    exact le_tsub_of_add_le_left h2
  -- the key inequality in `NNReal`
  have hkey : δ ^ (η' / 4) ≤ (1 / 2 : NNReal) * (X.toNNReal)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (pos_iff_ne_zero.mpr hXne)]
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow, hXnn, hXeq]
    push_cast
    exact hlog
  exact hkey.trans (mul_le_mul_of_nonneg_right hhalf zero_le)

/-- **The dense selection constant is below the sub-polynomial cap.** -/
theorem denseConst_le_rpow_neg {δ : NNReal} (hδ0 : 0 < δ) {η' : ℝ} (C : NNReal)
    (N : ℕ) (hpoly : (4 : ℝ) ^ (N + 1) ≤ (δ : ℝ) ^ (-(η' / 4)))
    (h6 : (6 * C : NNReal) * δ ^ (3 * η' / 4) ≤ 1 / 2)
    (h32 : (32 * C : NNReal) * δ ^ (η' / 4) ≤ 1 / 2) :
    ((ShadedTube.denseConst N C (δ ^ (η' / 2) / (32 * ((N : NNReal) + 1))) : NNReal) : ENNReal)
      ≤ (δ : ENNReal) ^ (-η') := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδne : δ ≠ 0 := hδ0.ne'
  rw [← ENNReal.coe_rpow_of_ne_zero hδne, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  have h6R : 6 * (C : ℝ) * (δ : ℝ) ^ (3 * η' / 4) ≤ 1 / 2 := by
    have := NNReal.coe_le_coe.mpr h6
    rw [NNReal.coe_mul, NNReal.coe_rpow] at this
    push_cast at this
    exact this
  have h32R : 32 * (C : ℝ) * (δ : ℝ) ^ (η' / 4) ≤ 1 / 2 := by
    have := NNReal.coe_le_coe.mpr h32
    rw [NNReal.coe_mul, NNReal.coe_rpow] at this
    push_cast at this
    exact this
  have hN1 : ((N : ℝ) + 1) ≤ (4 : ℝ) ^ (N + 1) := by
    have h : N + 1 < 4 ^ (N + 1) := Nat.lt_pow_self (by norm_num)
    exact_mod_cast h.le
  have h4N : (4 : ℝ) ^ N = (4 : ℝ) ^ (N + 1) / 4 := by
    rw [pow_succ]; field_simp
  have hpow1 : (δ : ℝ) ^ (-(η' / 4)) = (δ : ℝ) ^ (3 * η' / 4) * (δ : ℝ) ^ (-η') := by
    rw [← Real.rpow_add hδR]; congr 1; ring
  have hpow2 : (δ : ℝ) ^ (-(η' / 4)) * (δ : ℝ) ^ (-(η' / 2))
      = (δ : ℝ) ^ (η' / 4) * (δ : ℝ) ^ (-η') := by
    rw [← Real.rpow_add hδR, ← Real.rpow_add hδR]; congr 1; ring
  have hθ'R : ((δ ^ (η' / 2) / (32 * ((N : NNReal) + 1)) : NNReal) : ℝ)
      = (δ : ℝ) ^ (η' / 2) / (32 * ((N : ℝ) + 1)) := by
    rw [NNReal.coe_div, NNReal.coe_rpow]; push_cast; ring
  have hconst :
      ((ShadedTube.denseConst N C (δ ^ (η' / 2) / (32 * ((N : NNReal) + 1))) : NNReal) : ℝ)
      = 24 * (4 : ℝ) ^ N * C + (C : ℝ) * (32 * ((N : ℝ) + 1)) * (δ : ℝ) ^ (-(η' / 2)) := by
    simp only [ShadedTube.denseConst, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_pow, hθ'R]
    push_cast
    rw [Real.rpow_neg hδR.le]
    field_simp
  rw [hconst, NNReal.coe_rpow]
  have hC0 : (0 : ℝ) ≤ C := C.coe_nonneg
  have hδp : (0 : ℝ) < (δ : ℝ) ^ (-η') := Real.rpow_pos_of_pos hδR _
  have hδq : (0 : ℝ) ≤ (δ : ℝ) ^ (-(η' / 2)) := (Real.rpow_pos_of_pos hδR _).le
  -- first term
  have hA : 24 * (4 : ℝ) ^ N * C ≤ (1 / 2) * (δ : ℝ) ^ (-η') := by
    calc 24 * (4 : ℝ) ^ N * C = 6 * C * (4 : ℝ) ^ (N + 1) := by rw [h4N]; ring
      _ ≤ 6 * C * (δ : ℝ) ^ (-(η' / 4)) := by gcongr
      _ = (6 * C * (δ : ℝ) ^ (3 * η' / 4)) * (δ : ℝ) ^ (-η') := by rw [hpow1]; ring
      _ ≤ (1 / 2) * (δ : ℝ) ^ (-η') := by gcongr
  -- second term
  have hB : (C : ℝ) * (32 * ((N : ℝ) + 1)) * (δ : ℝ) ^ (-(η' / 2)) ≤ (1 / 2) * (δ : ℝ) ^ (-η') := by
    calc (C : ℝ) * (32 * ((N : ℝ) + 1)) * (δ : ℝ) ^ (-(η' / 2))
        ≤ (C : ℝ) * (32 * (4 : ℝ) ^ (N + 1)) * (δ : ℝ) ^ (-(η' / 2)) := by gcongr
      _ ≤ (C : ℝ) * (32 * (δ : ℝ) ^ (-(η' / 4))) * (δ : ℝ) ^ (-(η' / 2)) := by gcongr
      _ = 32 * C * ((δ : ℝ) ^ (-(η' / 4)) * (δ : ℝ) ^ (-(η' / 2))) := by ring
      _ = (32 * C * (δ : ℝ) ^ (η' / 4)) * (δ : ℝ) ^ (-η') := by rw [hpow2]; ring
      _ ≤ (1 / 2) * (δ : ℝ) ^ (-η') := by gcongr
  linarith


universe u

/-- The pure `ℝ≥0∞` bookkeeping of the mass-retention chain. -/
theorem retention_chain {ret M₃ Y₃ Y₂ Ys P a2 a4 b : ENNReal} {n₂ n₃ : ℕ}
    (h1 : M₃ ≤ 2 * ret) (h2 : a2 * Y₃ ≤ M₃) (h3 : (n₃ : ENNReal) * P ≤ 2 * Y₃)
    (h4 : a2 * (n₂ : ENNReal) ≤ (n₃ : ENNReal)) (h5 : Y₂ ≤ (n₂ : ENNReal) * (2 * P))
    (h6 : a4 * Ys ≤ Y₂) (h7 : 8 * b ≤ a2 * a2 * a4) :
    b * Ys ≤ ret := by
  have h8 : (8 : ENNReal) * (b * Ys) ≤ 8 * ret := by
    calc (8 : ENNReal) * (b * Ys) = (8 * b) * Ys := by ring
      _ ≤ (a2 * a2 * a4) * Ys := by gcongr
      _ = a2 * a2 * (a4 * Ys) := by ring
      _ ≤ a2 * a2 * Y₂ := by gcongr
      _ ≤ a2 * a2 * ((n₂ : ENNReal) * (2 * P)) := by gcongr
      _ = 2 * a2 * ((a2 * (n₂ : ENNReal)) * P) := by ring
      _ ≤ 2 * a2 * ((n₃ : ENNReal) * P) := by gcongr
      _ ≤ 2 * a2 * (2 * Y₃) := by gcongr
      _ = 4 * (a2 * Y₃) := by ring
      _ ≤ 4 * M₃ := by gcongr
      _ ≤ 4 * (2 * ret) := by gcongr
      _ = 8 * ret := by ring
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h8

/-- Cancelling the dense-selection accounting: if the light and thin losses are each at most an
eighth of the total, the retained mass is at least half of it. -/
theorem total_le_two_mul_retained {M₃ ret ℓ Cc : ENNReal} (hM : M₃ ≠ ⊤)
    (hacc : M₃ ≤ ret + 2 * (ℓ + Cc)) (hℓ : 8 * ℓ ≤ M₃) (hCc : 8 * Cc ≤ M₃) :
    M₃ ≤ 2 * ret := by
  have h4 : 4 * (ℓ + Cc) ≤ M₃ := by
    have : (2 : ENNReal) * (4 * (ℓ + Cc)) ≤ 2 * M₃ := by
      calc (2 : ENNReal) * (4 * (ℓ + Cc)) = 8 * ℓ + 8 * Cc := by ring
        _ ≤ M₃ + M₃ := add_le_add hℓ hCc
        _ = 2 * M₃ := by ring
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp this
  have h2 : M₃ + M₃ ≤ 2 * ret + M₃ := by
    calc M₃ + M₃ = 2 * M₃ := by ring
      _ ≤ 2 * (ret + 2 * (ℓ + Cc)) := by gcongr
      _ = 2 * ret + 4 * (ℓ + Cc) := by ring
      _ ≤ 2 * ret + M₃ := by gcongr
  exact (ENNReal.add_le_add_iff_right hM).mp h2

/-- The uniformization's relative fullness clause, cleared into a comparison of shade sums. -/
theorem rpow_mul_sum_shade_le_of_fullness'_le {ι : Type*} {s : Finset ι}
    {V V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {δ : NNReal} (hδ : δ ≠ 0) {α : ℝ}
    (hcar : ∀ i ∈ s, volume (V' i).carrier = volume (V i).carrier)
    (h : ShadedBody.fullness' s V
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α)) * ShadedBody.fullness' s V') :
    ((δ ^ α : NNReal) : ENNReal) * ∑ i ∈ s, volume (V i).shade ≤ ∑ i ∈ s, volume (V' i).shade := by
  have hcoe : ENNReal.ofReal ((δ : ℝ) ^ (-α)) = ((δ ^ (-α) : NNReal) : ENNReal) := by
    rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal]
  rw [hcoe, ← ShadedBody.coe_fullness, ← ShadedBody.coe_fullness] at h
  rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul,
    ShadedBody.sum_volumeReal_shade_eq_fullness_mul]
  have hsumcar : ∑ i ∈ s, volume (V' i).carrier = ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_congr rfl hcar
  rw [hsumcar, ← mul_assoc]
  gcongr
  rw [← ENNReal.coe_mul, ENNReal.coe_le_coe]
  calc δ ^ α * ShadedBody.fullness s V
      ≤ δ ^ α * (δ ^ (-α) * ShadedBody.fullness s V') := by
        gcongr
        exact_mod_cast h
    _ = ShadedBody.fullness s V' := by
        rw [← mul_assoc, ← NNReal.rpow_add hδ]
        simp

/-- **Clauses (a)–(d) and (f) of `Kakeya.VeryNotSticky.BandUniformRefinement`, from the
binders of `Kakeya.VeryNotSticky.exists_setup_caseSideData` alone.**

The route: the density-band pigeonhole at floor `δ^{2η-η'}/2`
(`Kakeya.VeryNotSticky.exists_shadingBand`), the shaded uniformization at both loss exponents
`η'/2` (`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`), and the class-dense heavy
selection `ShadedTube.exists_denseSelection` at the floor `t = δ^{η'} λ |T|`, with light
threshold `2t` and node threshold `θ' = δ^{η'/2} / (32 (N+1))`.  The uniformity constant
`ShadedTube.denseConst N C θ'` is sub-polynomial times `δ^{-η'/2}`, hence below `δ^{-η'}`;
the per-tube floor `t` is at least `δ^{2η} |T|` because the band puts `λ ≥ δ^{2η-η'}`; and the
mass retained is at least `δ^{5η'/4}/8` of the original, which beats `δ^η` as `8 η' < η`. -/
theorem eventually_exists_classDenseRefinement {η η' : ℝ} (hη' : 0 < η') (h8 : 8 * η' < η)
    (hη1 : η ≤ 1) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        δ ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
        ∃ s' ⊆ s, ∃ T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
          (∀ i, (T' i).toTube = (T i).toTube) ∧
          (∀ i, (T' i).shade ⊆ (T i).shade) ∧
          (∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
            Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀)) ∧
          (∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤ volume (T' i).shade) ∧
          (δ : ENNReal) ^ η * ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s', volume (T' i).shade := by
  have hη : 0 < η := by linarith
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨δ₁, hδ₁pos, -, Hssf⟩ := ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf.{u}
    (E := EuclideanSpace ℝ (Fin 3)) 4 (η' / 2) (η' / 2) (by linarith) (by linarith)
  obtain ⟨δ₂, hδ₂pos, -, Hpoly⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 4 (by norm_num) 0 1 (η' / 4) (by linarith)
  have hle₁ : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ δ₁ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ₁pos)] with d hd
    exact le_of_lt hd
  have hle₂ : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ δ₂ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ₂pos)] with d hd
    exact le_of_lt hd
  set C : NNReal := ShadedTube.ssfUniformConst 3 with hC
  filter_upwards [Kakeya.VNSUniform.eventually_card_thresholds', hle₁, hle₂,
    eventually_rpow_mul_add_log_le (by linarith : 0 < η' / 4) 2 ((2 * η - η') / Real.log 2)
      (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_nnreal_mul_rpow_le_const (6 * C) (1 / 2) (by norm_num)
      (by linarith : 0 < 3 * η' / 4),
    eventually_nnreal_mul_rpow_le_const (32 * C) (1 / 2) (by norm_num)
      (by linarith : 0 < η' / 4),
    eventually_nnreal_mul_rpow_le_const 32 1 (by norm_num) (by linarith : 0 < η' / 2),
    eventually_nnreal_mul_rpow_le_const 8 1 (by norm_num) (by linarith : 0 < η - 5 * η' / 4)]
    with δ hthr hδδ₁ hδδ₂ hlog h6C h32C h32 h8'
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  intro ι s T hball hmax hfull
  classical
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδne : δ ≠ 0 := hδ0.ne'
  have hδE0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδne
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  set V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i ↦ (T i).toShadedBody with hV
  -- `s` is nonempty
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · exfalso
      rw [h] at hfull
      have h0 : ShadedBody.fullness (∅ : Finset ι) V = 0 := by
        simp [ShadedBody.fullness, ShadedBody.fullness']
      rw [h0] at hfull
      exact absurd hfull (not_le.mpr (NNReal.rpow_pos hδ0))
    · exact h
  obtain ⟨i₀, hi₀⟩ := hsne
  set v : ENNReal := volume (T i₀).carrier with hv
  have hvol : ∀ i ∈ s, volume (V i).carrier = v := fun i _ =>
    Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
  have hvpos := Tube.volume_pos_and_lt_top hδ0 hδ1 (T i₀).toTube
  have hv0 : v ≠ 0 := hvpos.1.ne'
  have hvtop : v ≠ ⊤ := hvpos.2.ne
  -- Step 1: the band
  have ha0 : 0 < δ ^ η := NNReal.rpow_pos hδ0
  have hθb0 : 0 < δ ^ (2 * η - η') / 2 := by positivity
  have hθb1 : δ ^ (2 * η - η') / 2 ≤ 1 := by
    have h1 : δ ^ (2 * η - η') ≤ 1 := NNReal.rpow_le_one hδ1 (by linarith)
    calc δ ^ (2 * η - η') / 2 ≤ 1 / 2 := div_le_div_of_nonneg_right h1 (by norm_num)
      _ ≤ 1 := by norm_num
  have hq1 : δ ^ (η - η') / 2 < 1 := by
    have h1 : δ ^ (η - η') ≤ 1 := NNReal.rpow_le_one hδ1 (by linarith)
    calc δ ^ (η - η') / 2 ≤ 1 / 2 := div_le_div_of_nonneg_right h1 (by norm_num)
      _ < 1 := by norm_num
  have hθq : δ ^ (2 * η - η') / 2 ≤ δ ^ (η - η') / 2 * δ ^ η := by
    rw [div_mul_eq_mul_div, ← NNReal.rpow_add hδne]
    apply le_of_eq
    congr 2
    ring
  obtain ⟨s₂, hs₂, lam, hlam0, hlamge, hband, href⟩ :=
    exists_shadingBand hvol hv0 ha0 hθb0 hθb1 hfull hq1 hθq
  have hc₁ : δ ^ (η' / 4) ≤ (1 - δ ^ (η - η') / 2) *
      ((1 + Real.logb 2 (((δ ^ (2 * η - η') / 2 : NNReal) : ℝ)⁻¹)).toNNReal)⁻¹ :=
    denseBand_const_ge hδ0 hδ1 hη' (by linarith) hlog
  -- Step 2: the uniformization
  have hcard₂ : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) := by
    have h1 : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-4 : ℝ) :=
      Kakeya.VNSUniform.card_le_rpow_neg_four_enn hδ0 hδ1 hδC s T hball hη1 hmax
    rw [← ENNReal.coe_rpow_of_ne_zero hδne, ← ENNReal.coe_natCast, ENNReal.coe_le_coe] at h1
    have h2 : ((s.card : NNReal) : ℝ) ≤ ((δ ^ (-4 : ℝ) : NNReal) : ℝ) := NNReal.coe_le_coe.mpr h1
    rw [NNReal.coe_rpow, NNReal.coe_natCast] at h2
    have h3 : (s₂.card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast Finset.card_le_card hs₂
    push_cast
    linarith
  obtain ⟨s₃, hs₃, T', htube, hsh, hcard₃, hfull₃, ⟨𝒱₀⟩⟩ :=
    Hssf hδ0 hδδ₁ s₂ T (fun i hi => hball i (hs₂ hi)) hcard₂
  have 𝒱 : ShadedTube.ShadedUniformTubeSet s₃ T' (Tube.ssfGridLen δ) C := by
    rw [hfr] at 𝒱₀; exact 𝒱₀
  -- Step 3: the dense selection
  set N := Tube.ssfGridLen δ with hN
  set θ' : NNReal := δ ^ (η' / 2) / (32 * ((N : NNReal) + 1)) with hθ'
  have hθ'pos : 0 < θ' := by positivity
  set P : ENNReal := (lam : ENNReal) * v with hP
  have hPtop : P ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hvtop
  set t : ENNReal := (δ : ENNReal) ^ η' * P with ht
  set M : ENNReal := 2 * P with hM
  have hMtop : M ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hPtop
  have hband_lb : ∀ i ∈ s₂, P ≤ 2 * volume (T i).shade := by
    intro i hi
    have h := (hband i hi).1
    rw [hvol i (hs₂ hi)] at h
    calc P = 2 * (2⁻¹ * ((lam : ENNReal) * v)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2 * volume (T i).shade := by gcongr
  have hband_ub : ∀ i ∈ s₂, volume (T i).shade ≤ M := by
    intro i hi
    have h := (hband i hi).2
    rw [hvol i (hs₂ hi)] at h
    exact h
  have hMle : ∀ i ∈ s₃, volume (T' i).shade ≤ M := fun i hi =>
    (measure_mono (hsh i)).trans (hband_ub i (hs₃ hi))
  obtain ⟨s', hs', T'', htube'', hsh'', hfloor, huni, hacc⟩ :=
    ShadedTube.exists_denseSelection 𝒱 hθ'pos t hMle hMtop
  -- carriers
  have hcar'' : ∀ i ∈ s, volume (T'' i).carrier = v := by
    intro i hi
    have h : (T'' i).toTube = (T i).toTube := (htube'' i).trans (htube i)
    rw [show (T'' i).carrier = (T i).carrier from congrArg (fun U : Tube δ _ => U.carrier) h]
    exact hvol i hi
  have hcar' : ∀ i ∈ s₃,
      volume (T' i).toShadedBody.carrier = volume (T i).toShadedBody.carrier := by
    intro i _
    exact congrArg volume (congrArg (fun U : Tube δ _ => U.carrier) (htube i))
  -- the `ℝ≥0∞` powers
  set a2 : ENNReal := (δ : ENNReal) ^ (η' / 2) with ha2
  set a4 : ENNReal := (δ : ENNReal) ^ (η' / 4) with ha4
  refine ⟨s', hs'.trans (hs₃.trans hs₂), T'', fun i => (htube'' i).trans (htube i),
    fun i => (hsh'' i).trans (hsh i), ⟨ShadedTube.denseConst N C θ', ?_, ?_, huni⟩, ?_, ?_⟩
  · -- `1 ≤ C₀`
    have h1 : 1 ≤ C := ShadedTube.one_le_ssfUniformConst 3
    unfold ShadedTube.denseConst
    have h24 : (1 : NNReal) ≤ 24 * 4 ^ N := by
      calc (1 : NNReal) ≤ 24 := by norm_num
        _ = 24 * 1 := by ring
        _ ≤ 24 * 4 ^ N := by gcongr; exact one_le_pow₀ (by norm_num)
    calc (1 : NNReal) ≤ C := h1
      _ = 1 * C := (one_mul C).symm
      _ ≤ 24 * 4 ^ N * C := by gcongr
      _ ≤ 24 * 4 ^ N * C + C / θ' := le_self_add
  · -- the cap
    have hpoly : (4 : ℝ) ^ (N + 1) ≤ (δ : ℝ) ^ (-(η' / 4)) := by
      have h := (Hpoly hδ0 hδδ₂).2.2 1 (by norm_num) (by simp)
      simpa using h
    exact denseConst_le_rpow_neg hδ0 C N hpoly h6C h32C
  · -- clause (d)
    intro i hi
    have his : i ∈ s := hs₂ (hs₃ (hs' hi))
    rw [hcar'' i his]
    refine le_trans ?_ (hfloor i hi)
    rw [ht, hP, ← mul_assoc]
    gcongr
    have hl : ((δ ^ (2 * η - η') : NNReal) : ENNReal) ≤ (lam : ENNReal) := by
      have h1 : δ ^ (2 * η - η') ≤ lam := by
        calc δ ^ (2 * η - η') = 2 * (δ ^ (2 * η - η') / 2) := by
              rw [mul_div_cancel₀ _ (by norm_num : (2 : NNReal) ≠ 0)]
          _ ≤ lam := hlamge
      exact_mod_cast h1
    calc (δ : ENNReal) ^ (2 * η) = (δ : ENNReal) ^ η' * (δ : ENNReal) ^ (2 * η - η') := by
          rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
      _ = (δ : ENNReal) ^ η' * ((δ ^ (2 * η - η') : NNReal) : ENNReal) := by
          rw [ENNReal.coe_rpow_of_ne_zero hδne]
      _ ≤ (δ : ENNReal) ^ η' * (lam : ENNReal) := by gcongr
  · -- clause (f)
    set M₃ := ∑ i ∈ s₃, volume (T' i).shade with hM₃
    set Y₃ := ∑ i ∈ s₃, volume (T i).shade with hY₃
    set Y₂ := ∑ i ∈ s₂, volume (T i).shade with hY₂
    set Ys := ∑ i ∈ s, volume (T i).shade with hYs
    set ret := ∑ i ∈ s', volume (T'' i).shade with hret
    set ℓ := ∑ i ∈ s₃.filter (fun i => volume (T' i).shade < 2 * t), volume (T' i).shade with hℓ
    set Cc := ((N : ENNReal) + 1) * (θ' : ENNReal) * (s₃.card : ENNReal) * M with hCc
    have hM₃top : M₃ ≠ ⊤ :=
      (ENNReal.sum_lt_top.2 fun i hi => lt_of_le_of_lt (hMle i hi) hMtop.lt_top).ne
    have h2 : a2 * Y₃ ≤ M₃ := by
      have h := rpow_mul_sum_shade_le_of_fullness'_le (V := fun i => (T i).toShadedBody)
        (V' := fun i => (T' i).toShadedBody) hδne hcar' hfull₃
      rw [ENNReal.coe_rpow_of_ne_zero hδne] at h
      exact h
    have h3 : (s₃.card : ENNReal) * P ≤ 2 * Y₃ := by
      rw [hY₃, Finset.mul_sum]
      calc (s₃.card : ENNReal) * P = ∑ _i ∈ s₃, P := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i ∈ s₃, 2 * volume (T i).shade := Finset.sum_le_sum fun i hi => hband_lb i (hs₃ hi)
    have h4 : a2 * (s₂.card : ENNReal) ≤ (s₃.card : ENNReal) := by
      have hR : (δ : ℝ) ^ (η' / 2) * (s₂.card : ℝ) ≤ (s₃.card : ℝ) := by
        calc (δ : ℝ) ^ (η' / 2) * (s₂.card : ℝ)
            ≤ (δ : ℝ) ^ (η' / 2) * ((δ : ℝ) ^ (-(η' / 2)) * (s₃.card : ℝ)) := by gcongr
          _ = (s₃.card : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hδR]; simp
      have hN' : (δ ^ (η' / 2) : NNReal) * (s₂.card : NNReal) ≤ (s₃.card : NNReal) := by
        rw [← NNReal.coe_le_coe]
        push_cast
        exact hR
      have key := ENNReal.coe_le_coe.mpr hN'
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne, ENNReal.coe_natCast,
        ENNReal.coe_natCast] at key
      exact key
    have h5 : Y₂ ≤ (s₂.card : ENNReal) * (2 * P) := by
      calc Y₂ ≤ ∑ _i ∈ s₂, M := Finset.sum_le_sum hband_ub
        _ = (s₂.card : ENNReal) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    have h6 : a4 * Ys ≤ Y₂ := by
      have hr := href.2
      calc a4 * Ys = ((δ ^ (η' / 4) : NNReal) : ENNReal) * Ys := by
            rw [ENNReal.coe_rpow_of_ne_zero hδne]
        _ ≤ (((1 - δ ^ (η - η') / 2) *
            ((1 + Real.logb 2 (((δ ^ (2 * η - η') / 2 : NNReal) : ℝ)⁻¹)).toNNReal)⁻¹ : NNReal)
              : ENNReal) * Ys := mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hc₁) zero_le
        _ ≤ Y₂ := hr
    have h7 : 8 * (δ : ENNReal) ^ η ≤ a2 * a2 * a4 := by
      have hN' : (8 : NNReal) * δ ^ η ≤ δ ^ (η' / 2) * δ ^ (η' / 2) * δ ^ (η' / 4) := by
        calc (8 : NNReal) * δ ^ η = (8 * δ ^ (η - 5 * η' / 4)) * δ ^ (5 * η' / 4) := by
              rw [mul_assoc, ← NNReal.rpow_add hδne]; congr 2; ring
          _ ≤ 1 * δ ^ (5 * η' / 4) := by gcongr
          _ = δ ^ (η' / 2) * δ ^ (η' / 2) * δ ^ (η' / 4) := by
              rw [one_mul, ← NNReal.rpow_add hδne, ← NNReal.rpow_add hδne]; congr 1; ring
      have h := ENNReal.coe_le_coe.mpr hN'
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne η,
        ENNReal.coe_rpow_of_ne_zero hδne (η' / 2), ENNReal.coe_rpow_of_ne_zero hδne (η' / 4),
        ENNReal.coe_ofNat] at h
      exact h
    -- `32 δ^{η'} ≤ δ^{η'/2}`
    have h32E : (32 : ENNReal) * (δ : ENNReal) ^ η' ≤ a2 := by
      have hN' : (32 : NNReal) * δ ^ η' ≤ δ ^ (η' / 2) := by
        calc (32 : NNReal) * δ ^ η' = (32 * δ ^ (η' / 2)) * δ ^ (η' / 2) := by
              rw [mul_assoc, ← NNReal.rpow_add hδne]; congr 2; ring
          _ ≤ 1 * δ ^ (η' / 2) := by gcongr
          _ = δ ^ (η' / 2) := one_mul _
      have h := ENNReal.coe_le_coe.mpr hN'
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne η',
        ENNReal.coe_rpow_of_ne_zero hδne (η' / 2), ENNReal.coe_ofNat] at h
      exact h
    have hℓ1 : ℓ ≤ (s₃.card : ENNReal) * (2 * t) := by
      calc ℓ ≤ ∑ _i ∈ s₃.filter (fun i => volume (T' i).shade < 2 * t), 2 * t :=
            Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
        _ = ((s₃.filter (fun i => volume (T' i).shade < 2 * t)).card : ENNReal) * (2 * t) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (s₃.card : ENNReal) * (2 * t) := by
            gcongr
            exact Finset.filter_subset _ _
    have hℓ : 8 * ℓ ≤ M₃ := by
      have h : 2 * (8 * ℓ) ≤ 2 * M₃ := by
        calc 2 * (8 * ℓ) ≤ 2 * (8 * ((s₃.card : ENNReal) * (2 * t))) := by gcongr
          _ = (32 * (δ : ENNReal) ^ η') * ((s₃.card : ENNReal) * P) := by rw [ht]; ring
          _ ≤ a2 * ((s₃.card : ENNReal) * P) := by gcongr
          _ ≤ a2 * (2 * Y₃) := by gcongr
          _ = 2 * (a2 * Y₃) := by ring
          _ ≤ 2 * M₃ := by gcongr
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h
    have hCc : 8 * Cc ≤ M₃ := by
      have hθ'id : (32 : NNReal) * (((N : NNReal) + 1) * θ') = δ ^ (η' / 2) := by
        rw [hθ', ← mul_assoc]
        have hne : (32 : NNReal) * ((N : NNReal) + 1) ≠ 0 := by positivity
        rw [mul_div_cancel₀ _ hne]
      have hθ'E : (32 : ENNReal) * (((N : ENNReal) + 1) * (θ' : ENNReal)) = a2 := by
        have h := congrArg (fun x : NNReal => (x : ENNReal)) hθ'id
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_natCast,
          ENNReal.coe_one, ENNReal.coe_ofNat, ENNReal.coe_rpow_of_ne_zero hδne] at h
        exact h
      have h : 2 * (8 * Cc) ≤ 2 * M₃ := by
        calc 2 * (8 * Cc) = (32 * (((N : ENNReal) + 1) * (θ' : ENNReal))) *
              ((s₃.card : ENNReal) * P) := by rw [hCc, hM]; ring
          _ = a2 * ((s₃.card : ENNReal) * P) := by rw [hθ'E]
          _ ≤ a2 * (2 * Y₃) := by gcongr
          _ = 2 * (a2 * Y₃) := by ring
          _ ≤ 2 * M₃ := by gcongr
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h
    have h1 : M₃ ≤ 2 * ret := total_le_two_mul_retained hM₃top hacc hℓ hCc
    exact retention_chain h1 h2 h3 h4 h5 h6 h7

/-- **`Kakeya.VeryNotSticky.BandUniformRefinement` from the binders of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` together with the cardinality binder
`|𝕋| ≥ δ^{-1-2η}`.**

Clauses (a)–(d) and (f) are `Kakeya.VeryNotSticky.eventually_exists_classDenseRefinement`.
Clause (e), the tube count `1 ≤ δ |𝕋'|`, follows from the mass retention (f): the retained
family carries a `δ^η` share of the mass, the mass is at least `δ^η |𝕋| |T|` by the fullness
binder, and each member carries at most `|T|`, so `|𝕋'| ≥ δ^{2η} |𝕋|`.  The residue of the
configuration half of GWZ Lemma 9.1 is therefore exactly the binder `1 ≤ δ^{1+2η} |𝕋|`, which is
the `|𝕋| ≥ δ^{-1-α}` of `Kakeya.VeryNotSticky.tubeCount_of_parent_of_retention`. -/
theorem eventually_bandUniformRefinement_of_card {η η' : ℝ} (hη' : 0 < η') (h8 : 8 * η' < η)
    (hη1 : η ≤ 1) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        δ ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
        (1 : ENNReal) ≤ (δ : ENNReal) ^ (1 + 2 * η) * (s.card : ENNReal) →
        BandUniformRefinement δ η η' s T := by
  filter_upwards [eventually_exists_classDenseRefinement.{u} hη' h8 hη1,
    Kakeya.VNSUniform.eventually_card_thresholds'] with δ H hthr
  obtain ⟨hδ0, hδ1, -⟩ := hthr
  intro ι s T hball hmax hfull hcount
  obtain ⟨s', hs', T', htube, hsh, huni, hpt, hmass⟩ := H s T hball hmax hfull
  refine ⟨s', T', hs', htube, hsh, huni, hpt, ?_, hmass⟩
  classical
  have hδE0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · exfalso
      rw [h] at hcount
      simp at hcount
    · exact h
  obtain ⟨i₀, hi₀⟩ := hsne
  set v : ENNReal := volume (T i₀).carrier with hv
  have hvol : ∀ i ∈ s, volume (T i).carrier = v := fun i _ =>
    Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
  have hvpos := Tube.volume_pos_and_lt_top hδ0 hδ1 (T i₀).toTube
  have hYs : ((δ ^ η : NNReal) : ENNReal) * ((s.card : ENNReal) * v)
      ≤ ∑ i ∈ s, volume (T i).shade :=
    ShadedBody.coe_fullness_mul_le_sum_volume_shade s (fun i ↦ (T i).toShadedBody) hfull
      (fun i hi => (hvol i hi).symm.le)
  have hret : ∑ i ∈ s', volume (T' i).shade ≤ (s'.card : ENNReal) * v := by
    calc ∑ i ∈ s', volume (T' i).shade ≤ ∑ _i ∈ s', v := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [← hvol i (hs' hi)]
          calc volume (T' i).shade ≤ volume (T' i).carrier := measure_mono (T' i).shade_subset
            _ = volume (T i).carrier :=
                congrArg volume (congrArg (fun U : Tube δ _ => U.carrier) (htube i))
      _ = (s'.card : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]
  have h1 : (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) * v ≤ (s'.card : ENNReal) * v := by
    calc (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) * v
        = (δ : ENNReal) ^ η * (((δ ^ η : NNReal) : ENNReal) * ((s.card : ENNReal) * v)) := by
          rw [ENNReal.coe_rpow_of_ne_zero hδ0.ne', ← mul_assoc, ← mul_assoc,
            ← ENNReal.rpow_add _ _ hδE0 hδEtop]
          congr 2
          ring_nf
      _ ≤ (δ : ENNReal) ^ η * ∑ i ∈ s, volume (T i).shade := by gcongr
      _ ≤ ∑ i ∈ s', volume (T' i).shade := hmass
      _ ≤ (s'.card : ENNReal) * v := hret
  have h2 : (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) ≤ (s'.card : ENNReal) :=
    (ENNReal.mul_le_mul_iff_left hvpos.1.ne' hvpos.2.ne).mp h1
  calc (1 : ENNReal) ≤ (δ : ENNReal) ^ (1 + 2 * η) * (s.card : ENNReal) := hcount
    _ = (δ : ENNReal) * ((δ : ENNReal) ^ (2 * η) * (s.card : ENNReal)) := by
        rw [ENNReal.rpow_add _ _ hδE0 hδEtop, ENNReal.rpow_one, mul_assoc]
    _ ≤ (δ : ENNReal) * (s'.card : ENNReal) := by gcongr

end Kakeya.VeryNotSticky
