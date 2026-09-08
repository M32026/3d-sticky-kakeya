/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Mathlib.Data.Set.Card

/-!
# Essentially distinct up to multiplicity

This file introduces `IsEDUpToMult s V M`: the family `V : ι → Set E` is
*essentially distinct up to multiplicity `M` on `s : Finset ι`* if, for every
family member `V i` with `i ∈ s`, at most `M` carriers `V j` with `j ∈ s`
fail to be essentially distinct from `V i`.

This is a faithful Lean rendering of the "essentially distinct up to
multiplicity ≲ 1" notion used in [GWZ, Section 9, proof of Lemma `randCF`],
where the bound `|T'[100·T_0]| ≲ 1` plays the role of the strict
essentially-distinct hypothesis in [GWZ, Lemma 3.7] / `FrostmanEstimate`.

Mathematically `IsEDUpToMult` is implied by (and slightly weaker than) the
strict `Pairwise IsEssentiallyDistinct` predicate together with the dimensional
constant `C_ED` from `essentiallyDistinct_notED_bound'`.

The content is purely combinatorial: nothing here refers to a probability
measure or to a random translation, so it lives next to the other
essential-distinctness combinatorics rather than in `Kakeya/RandomTranslation/`.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya

variable {ι E : Type*} [MeasureSpace E]

/-- The indices `i ∈ s` whose carrier `V i` fails to be essentially
distinct from `U`. This generic helper is specialized to `U = V j` in
`IsEDUpToMult`. -/
noncomputable def notEssDistinctSet (s : Finset ι) (V : ι → Set E) (U : Set E) : Finset ι :=
  by
    classical
    exact {i ∈ s | ¬ IsEssentiallyDistinct (V i) U}

/-- The family `V : ι → Set E` is *essentially distinct up to multiplicity `M`*
on the finite set `s : Finset ι` if, for every family member `V i` with `i ∈ s`,
the number of indices `j ∈ s` for which `V j` fails to be essentially distinct
from `V i` is bounded by `M`.

This corresponds to the bound `|T'[100·T_0]| ≲ M` in [GWZ, Section 9], expressed
on the canonical Mathlib essentially-distinct relation. The quantification is
*family-internal* (over `V i` rather than arbitrary `U : Set E`), which mirrors
GWZ's "for any `T_0` in our scaled family" and is the form that admits a
dimensional bound `M ≲ 1`. -/
def IsEDUpToMult (s : Finset ι) (V : ι → Set E) (M : ℕ) : Prop :=
  ∀ i ∈ s, (notEssDistinctSet s V (V i)).card ≤ M

section ReverseBridge

/-- **Shade-weighted reverse bridge.**

If `V` is essentially distinct up to multiplicity `M` on `s`, and `w : ι → ℝ`
is a nonnegative weight on `s`, then `s` admits a strictly
`Pairwise`-essentially-distinct subset `s'` such that the total weight loses at
most a factor of `M + 1`:
  `∑_{i ∈ s} w i ≤ (M + 1) · ∑_{i ∈ s'} w i`.

This is the shade-weighted reverse bridge needed for the multiplicity transfer
(`multiplicity_pigeon_transfer`) in [GWZ, Section 9, Lemma `randCF`].

Proof: pick `s'` to be an `IsEssentiallyDistinct`-Pairwise subset of `s` of
maximum total weight `∑_{i ∈ s'} w i`. For `x ∈ s \ s'`, by maximality there
must be at least one non-ED neighbour in `s'`; moreover, replacing the entire
"bad-neighbour" set `N x := {y ∈ s' | ¬ ED (V x, V y)}` with the singleton
`{x}` produces an ED subset, so `w x ≤ ∑_{y ∈ N x} w y`. Double counting
over `x` and `y` then turns this into
`∑_{x ∈ s \ s'} w x ≤ ∑_{y ∈ s'} w y · |{x ∈ s : ¬ ED (V x, V y)}|`,
which `IsEDUpToMult` controls by `M · ∑_{y ∈ s'} w y`. -/
lemma IsEDUpToMult.exists_pairwise_subset_with_weight
    {s : Finset ι} {V : ι → Set E} {M : ℕ}
    (hED : IsEDUpToMult s V M) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ s' : Finset ι, s' ⊆ s ∧
      (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i) (V j)) ∧
      (∑ i ∈ s, w i) ≤ (M + 1 : ℝ) * (∑ i ∈ s', w i) := by
  classical
  -- Symmetry of `IsEssentiallyDistinct`.
  have hSymm : ∀ a b : Set E,
      ¬ IsEssentiallyDistinct a b → ¬ IsEssentiallyDistinct b a := by
    intro a b h hba
    apply h
    unfold IsEssentiallyDistinct at *
    rw [Set.inter_comm, max_comm]; exact hba
  -- The family of ED subsets of `s`.
  let G : Finset (Finset ι) :=
    s.powerset.filter
      (fun t => (↑t : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i) (V j)))
  have hG_ne : G.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [G, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset,
      true_and]
    intro i hi; simp at hi
  -- Pick `s' ∈ G` maximizing the total weight `∑ w`.
  obtain ⟨s', hs'_mem, hs'_max⟩ :=
    G.exists_max_image (fun t => ∑ i ∈ t, w i) hG_ne
  have hs'_sub : s' ⊆ s :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hs'_mem).1
  have hs'_ED :
      (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i) (V j)) :=
    (Finset.mem_filter.mp hs'_mem).2
  -- For each y ∈ s', the "bucket" of indices in `s \ s'` non-ED with y.
  let bucket : ι → Finset ι :=
    fun y => (s \ s').filter (fun x => ¬ IsEssentiallyDistinct (V x) (V y))
  -- Bucket cardinality controlled by `IsEDUpToMult`.
  have h_bucket_card : ∀ y ∈ s', (bucket y).card ≤ M := by
    intro y hy
    have h_sub : bucket y ⊆ notEssDistinctSet s V (V y) := by
      intro x hx
      simp only [bucket, notEssDistinctSet, Finset.mem_filter, Finset.mem_sdiff] at hx ⊢
      exact ⟨hx.1.1, hx.2⟩
    calc (bucket y).card
        ≤ (notEssDistinctSet s V (V y)).card := Finset.card_le_card h_sub
      _ ≤ M := hED y (hs'_sub hy)
  -- For each x ∈ s \ s', its non-ED neighbours inside s' have total weight ≥ w x.
  let N : ι → Finset ι :=
    fun x => s'.filter (fun y => ¬ IsEssentiallyDistinct (V x) (V y))
  have h_N_subset : ∀ x, N x ⊆ s' := fun _ => Finset.filter_subset _ _
  have h_replace : ∀ x ∈ s \ s', w x ≤ ∑ y ∈ N x, w y := by
    intro x₀ hx₀
    rcases Finset.mem_sdiff.mp hx₀ with ⟨hxs, hxns⟩
    -- s'' := insert x₀ (s' \ N x₀) is ED and a member of G.
    let s'' : Finset ι := insert x₀ (s' \ N x₀)
    have hx_notin_diff : x₀ ∉ s' \ N x₀ := fun h => hxns (Finset.mem_sdiff.mp h).1
    have hs''_ED :
        (↑s'' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i) (V j)) := by
      intro i hi j hj hij
      simp only [s'', Finset.coe_insert, Finset.coe_sdiff,
        Set.mem_insert_iff, Set.mem_sdiff, Finset.mem_coe] at hi hj
      rcases hi with hi_eq | ⟨hi_s', hi_nN⟩ <;>
        rcases hj with hj_eq | ⟨hj_s', hj_nN⟩
      · exact (hij (hi_eq.trans hj_eq.symm)).elim
      · -- i = x₀, j ∈ s' \ N x₀: need ED (V x₀) (V j).
        subst hi_eq
        by_contra hbad
        apply hj_nN
        exact Finset.mem_filter.mpr ⟨hj_s', hbad⟩
      · -- j = x₀, i ∈ s' \ N x₀.
        subst hj_eq
        by_contra hbad
        apply hi_nN
        exact Finset.mem_filter.mpr ⟨hi_s', hSymm _ _ hbad⟩
      · exact hs'_ED hi_s' hj_s' hij
    have hs''_sub : s'' ⊆ s := by
      intro a ha
      simp only [s'', Finset.mem_insert, Finset.mem_sdiff] at ha
      rcases ha with rfl | ⟨ha_s', _⟩
      · exact hxs
      · exact hs'_sub ha_s'
    have hs''_mem : s'' ∈ G := by
      simp only [G, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hs''_sub, hs''_ED⟩
    have h_max := hs'_max _ hs''_mem
    -- Sum on s'': (s'.sum w - N x₀.sum w) + w x₀.
    have h_sum_s'' : (∑ i ∈ s'', w i) = w x₀ + ∑ i ∈ s' \ N x₀, w i := by
      simp [s'', Finset.sum_insert hx_notin_diff]
    have h_sum_split : (∑ i ∈ s', w i) = (∑ i ∈ s' \ N x₀, w i) + ∑ i ∈ N x₀, w i := by
      rw [← Finset.sum_sdiff (h_N_subset x₀)]
    linarith [h_max, h_sum_s'', h_sum_split]
  -- Double sum: ∑_{x ∈ s\s'} w x ≤ ∑_{y ∈ s'} w y · |bucket y|.
  have h_swap :
      ∑ x ∈ s \ s', w x ≤ ∑ y ∈ s', (bucket y).card * w y := by
    -- For each x ∈ s\s', w x ≤ ∑_{y ∈ N x} w y, so
    -- ∑_x w x ≤ ∑_x ∑_{y ∈ N x} w y.
    have h_step1 :
        ∑ x ∈ s \ s', w x ≤
          ∑ x ∈ s \ s', ∑ y ∈ N x, w y :=
      Finset.sum_le_sum h_replace
    -- Swap double sum: ∑_x ∑_{y ∈ N x} w y = ∑_y w y · |{x ∈ s\s' : y ∈ N x}|.
    have h_step2 :
        ∑ x ∈ s \ s', ∑ y ∈ N x, w y =
          ∑ y ∈ s',
            ((s \ s').filter (fun x => ¬ IsEssentiallyDistinct (V x) (V y))).card *
              w y := by
      simp only [N, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      -- Goal: ∑ x ∈ s\s', if ¬ED(V x,V y) then w y else 0
      --     = ↑(filter...).card * w y
      rw [← Finset.sum_filter (s := s \ s')
            (p := fun x => ¬ IsEssentiallyDistinct (V x) (V y))
            (f := fun _ => w y),
          Finset.sum_const, nsmul_eq_mul]
    rw [h_step2] at h_step1
    -- bucket y = (s\s').filter (¬ ED (V x) (V y)) — the same as inside.
    have h_bucket_eq : ∀ y ∈ s',
        ((s \ s').filter (fun x => ¬ IsEssentiallyDistinct (V x) (V y))).card =
          (bucket y).card := by
      intro y _; rfl
    refine le_trans h_step1 ?_
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro y hy
    rw [h_bucket_eq y hy]
  -- Combine ∑_{s\s'} w x ≤ M · ∑_{s'} w y.
  have h_sdiff_w : ∑ x ∈ s \ s', w x ≤ M * ∑ y ∈ s', w y := by
    refine le_trans h_swap ?_
    have h_each_bd : ∀ y ∈ s', (bucket y).card * w y ≤ (M : ℝ) * w y := by
      intro y hy
      have hwy_nonneg : 0 ≤ w y := hw _ (hs'_sub hy)
      have h1 : ((bucket y).card : ℝ) ≤ M := by
        exact_mod_cast h_bucket_card y hy
      exact mul_le_mul_of_nonneg_right h1 hwy_nonneg
    calc ∑ y ∈ s', (bucket y).card * w y
        ≤ ∑ y ∈ s', (M : ℝ) * w y := Finset.sum_le_sum h_each_bd
      _ = M * ∑ y ∈ s', w y := by rw [Finset.mul_sum]
  -- ∑_s w = ∑_{s\s'} w + ∑_{s'} w ≤ (M+1)·∑_{s'} w.
  have h_sum_split_total : (∑ i ∈ s, w i) = (∑ i ∈ s \ s', w i) + ∑ i ∈ s', w i := by
    rw [← Finset.sum_sdiff hs'_sub]
  refine ⟨s', hs'_sub, hs'_ED, ?_⟩
  rw [h_sum_split_total]
  calc (∑ i ∈ s \ s', w i) + ∑ i ∈ s', w i
      ≤ M * (∑ i ∈ s', w i) + ∑ i ∈ s', w i := by linarith [h_sdiff_w]
    _ = ((M : ℝ) + 1) * ∑ i ∈ s', w i := by ring

/-- **Weighted reverse bridge with simultaneous cardinality retention.**

The strengthening of `Kakeya.IsEDUpToMult.exists_pairwise_subset_with_weight` that returns *one*
subset retaining both the total weight and the cardinality, each up to the factor `M + 1`.

Both clauses on the same subset are needed by the inner-family extraction of GWZ 6.6(B): the
fullness and multiplicity clauses are driven by the weight (shade mass), while the slab and
cardinality clauses are driven by `card`, and all four must speak about the same extracted family.
Neither clause implies the other — a maximum-weight essentially distinct subset can be a single
index, and a maximum-cardinality one can carry almost no weight.

The weight clause is inherited from the maximum-weight subset; the cardinality clause needs that
subset to be *inclusion-maximal*, which is arranged by extending it to an essentially distinct
subset of `s` of maximal cardinality (the weight clause survives the extension because `w ≥ 0`). -/
lemma IsEDUpToMult.exists_pairwise_subset_with_weight_and_card
    {s : Finset ι} {V : ι → Set E} {M : ℕ}
    (hED : IsEDUpToMult s V M) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ s' : Finset ι, s' ⊆ s ∧
      (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i) (V j)) ∧
      (∑ i ∈ s, w i) ≤ (M + 1 : ℝ) * (∑ i ∈ s', w i) ∧
      s.card ≤ (M + 1) * s'.card := by
  classical
  -- (1) The weight clause comes from the sibling lemma.
  obtain ⟨t, ht_sub, ht_ED, ht_w⟩ := hED.exists_pairwise_subset_with_weight w hw
  -- (2) Enlarge `t` to a maximum-cardinality ED subset `s'` of `s`.
  let G : Finset (Finset ι) :=
    s.powerset.filter
      (fun u => t ⊆ u ∧ (↑u : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i) (V j)))
  have hG_ne : G.Nonempty := by
    refine ⟨t, ?_⟩
    simp only [G, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨ht_sub, subset_rfl, ht_ED⟩
  obtain ⟨s', hs'_mem, hs'_max⟩ := G.exists_max_image (fun u => u.card) hG_ne
  have hs'_sub : s' ⊆ s :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hs'_mem).1
  have ht_s' : t ⊆ s' := (Finset.mem_filter.mp hs'_mem).2.1
  have hs'_ED :
      (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i) (V j)) :=
    (Finset.mem_filter.mp hs'_mem).2.2
  -- (3) The weight clause survives the extension because `w ≥ 0`.
  have h_sum_t_le_sum_s' : (∑ i ∈ t, w i) ≤ ∑ i ∈ s', w i :=
    Finset.sum_le_sum_of_subset_of_nonneg ht_s' (fun i hi _ => hw i (hs'_sub hi))
  have hweight_s' : (∑ i ∈ s, w i) ≤ (M + 1 : ℝ) * (∑ i ∈ s', w i) := by
    have hM_nonneg : 0 ≤ (M + 1 : ℝ) := by exact_mod_cast (Nat.zero_le (M + 1))
    calc
      (∑ i ∈ s, w i) ≤ (M + 1 : ℝ) * (∑ i ∈ t, w i) := ht_w
      _ ≤ (M + 1 : ℝ) * (∑ i ∈ s', w i) :=
        mul_le_mul_of_nonneg_left h_sum_t_le_sum_s' hM_nonneg
  -- (4) Every `x ∈ s \ s'` has a non-ED partner inside `s'`.
  have hbad : ∀ x ∈ s \ s', ∃ y ∈ s', ¬ IsEssentiallyDistinct (V x) (V y) := by
    intro x hx
    by_contra h
    push Not at h
    rcases Finset.mem_sdiff.mp hx with ⟨hxs, hxns'⟩
    have hx_insert_ED :
        (↑(insert x s') : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i) (V j)) := by
      rw [Finset.coe_insert]
      refine Set.Pairwise.insert hs'_ED ?_
      intro y hy _hne
      exact ⟨h y hy, isEssentiallyDistinct_symm (h y hy)⟩
    have hx_insert_sub : insert x s' ⊆ s := by
      intro a ha
      rw [Finset.mem_insert] at ha
      rcases ha with rfl | has'
      · exact hxs
      · exact hs'_sub has'
    have ht_insert : t ⊆ insert x s' := by
      intro a ha
      exact Finset.mem_insert_of_mem (ht_s' ha)
    have h_insert_mem : insert x s' ∈ G := by
      simp only [G, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hx_insert_sub, ht_insert, hx_insert_ED⟩
    have hmax := hs'_max (insert x s') h_insert_mem
    have hcard : s'.card + 1 ≤ s'.card := by
      rw [Finset.card_insert_of_notMem hxns'] at hmax
      exact hmax
    exact (Nat.not_succ_le_self s'.card) hcard
  -- (5) The complement `s \ s'` is covered by the non-ED buckets of `s'`.
  have hcover : s \ s' ⊆ s'.biUnion (fun y => notEssDistinctSet s V (V y)) := by
    intro x hx
    rw [Finset.mem_biUnion]
    rcases hbad x hx with ⟨y, hys', hnotED⟩
    refine ⟨y, hys', ?_⟩
    simp only [notEssDistinctSet, Finset.mem_filter]
    exact ⟨(Finset.mem_sdiff.mp hx).1, hnotED⟩
  -- (6) Bound the cardinality of the complement.
  have hcard_sdiff : (s \ s').card ≤ M * s'.card := by
    calc
      (s \ s').card ≤ (s'.biUnion (fun y => notEssDistinctSet s V (V y))).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ y ∈ s', (notEssDistinctSet s V (V y)).card := Finset.card_biUnion_le
      _ ≤ ∑ y ∈ s', M := by
        apply Finset.sum_le_sum
        intro y hy
        exact hED y (hs'_sub hy)
      _ = M * s'.card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact Nat.mul_comm s'.card M
  -- (7) Conclude the cardinality clause.
  have hcard_total : s.card ≤ (M + 1) * s'.card := by
    rw [← Finset.card_sdiff_add_card_eq_card hs'_sub]
    calc
      (s \ s').card + s'.card ≤ M * s'.card + s'.card :=
        Nat.add_le_add_right hcard_sdiff s'.card
      _ = (M + 1) * s'.card := by rw [Nat.succ_mul]
  exact ⟨s', hs'_sub, hs'_ED, hweight_s', hcard_total⟩

/-- **`ENNReal` form of the weighted reverse bridge with cardinality retention.**

The version consumed by the shade-mass arguments: the weight is an `ENNReal`-valued mass `f`
(in practice `fun i => volume (P i).shade`), finite on `s`.  The retention clause

`∑_{i ∈ s} f i ≤ (M + 1) · ∑_{i ∈ s'} f i`

is character for character the hypothesis of `ShadedBody.fullness'_le_of_subset_of_sum_shade_le`
and of `Kakeya.multiplicity_pigeon_transfer`, so a single application of this lemma feeds the
fullness transfer and the multiplicity split at once. -/
lemma IsEDUpToMult.exists_pairwise_subset_with_measure_and_card
    {s : Finset ι} {V : ι → Set E} {M : ℕ}
    (hED : IsEDUpToMult s V M) (f : ι → ENNReal) (hfin : ∀ i ∈ s, f i ≠ ⊤) :
    ∃ s' : Finset ι, s' ⊆ s ∧
      (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i) (V j)) ∧
      (∑ i ∈ s, f i) ≤ ((M : ENNReal) + 1) * (∑ i ∈ s', f i) ∧
      s.card ≤ (M + 1) * s'.card := by
  classical
  -- Apply the sibling theorem with the real-valued weights (f i).toReal.
  rcases hED.exists_pairwise_subset_with_weight_and_card (fun i => (f i).toReal)
      (fun i hi => ENNReal.toReal_nonneg) with ⟨s', hs'sub, hs'ED, hweight, hcard⟩
  · refine ⟨s', hs'sub, hs'ED, ?_, hcard⟩
    -- Lift the real inequality back to ENNReal.
    have hSfin : (∑ i ∈ s, f i) ≠ ⊤ := by
      exact (ENNReal.sum_ne_top).mpr hfin
    have hTfin : (∑ i ∈ s', f i) ≠ ⊤ := by
      exact (ENNReal.sum_ne_top).mpr (fun i hi => hfin i (hs'sub hi))
    have hSreal : ((∑ i ∈ s, f i).toReal) = ∑ i ∈ s, (f i).toReal :=
      ENNReal.toReal_sum hfin
    have hTreal : ((∑ i ∈ s', f i).toReal) = ∑ i ∈ s', (f i).toReal :=
      ENNReal.toReal_sum (fun i hi => hfin i (hs'sub hi))
    have hfactor : ((M : ENNReal) + 1).toReal = (M : ℝ) + 1 := by
      simp [ENNReal.toReal_add]
    have hprodfin : ((M : ENNReal) + 1) * (∑ i ∈ s', f i) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by simp) hTfin
    rw [← ENNReal.toReal_le_toReal hSfin hprodfin]
    rw [hSreal, ENNReal.toReal_mul, hfactor, hTreal]
    exact hweight

end ReverseBridge

end Kakeya
