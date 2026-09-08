/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform.GridNet
public import Kakeya.FibreCommon
public import Kakeya.Uniform
public import Kakeya.MultiScaleFac.Branching
public import Kakeya.Tube.CardEssentiallyDistinct

/-!
# Re-uniformizing a subfamily along the grid

The refined form of GWZ Lemma 7.7(A) discards tubes at every level of its stopping time, and
uniformity is *not* inherited by an arbitrary subset: deleting tubes destroys the constancy of the
class sizes.  Since the consumers of that lemma require a uniform family, every level must restore
uniformity — and, with it, the comparable fibre counts of GWZ Definition 2.1(iii) — before the next
test is run.  This file states that repair.

The refinement is run against a *system of covers fixed in advance* at all grid scales
(`GridCoverSystem`).  This is forced: clumping is a statement about the classes of a given cover,
so a uniformization that chose fresh covers afterwards would leave the clumping saying nothing
about the new nodes.

Three movements, then the assembly.

* **Clumping** (`exists_clumped_subset_of_leaves`, `exists_clumped_subset_along_grid`).  Inside one
  node the leaves are pigeonholed into a common tube of a quarter of the node's radius, at a
  dimensional cost; after that every retained leaf sees the whole retained class inside its own
  exact-scale thickening.  This is what supplies the *lower* bound on an individual fibre, which
  uniformity alone cannot give.
* **Uniformization** (`exists_uniformize_one_scale`, `exists_uniformize_along_grid`).  A dyadic
  pigeonhole over the class sizes at each of the `N + 1` grid scales, run as a single nested pass,
  makes the retained class sizes constant up to a factor `2`.
* **Comparability** (`card_fibreIndex_band_of_clumped`,
  `card_fibreIndex_four_mul_le_of_branching_lower`,
  `exists_const_card_fibreIndex_bottom_scale`).  Uniform *and* clumped gives the two-sided
  comparison of an exact-scale fibre with the branching number, whence
  `Kakeya.MultiScaleFac.ComparableFibreCounts`; a further covering step inflates the anchor, giving
  `Kakeya.MultiScaleFac.ComparableFibreCountsInflated`; and at the bottom grid scale `ρ = δ`, where
  there is no clumping, both come from essential distinctness instead.

`exists_uniformize_subfamily` is the assembly and the only statement the stopping time consumes.
Its loss is `(C log(1/δ))^{O(N)}`, which is `δ^{-o(1)}` for fixed `N` but not uniformly in `N`;
that, together with the threshold `δ ≤ 16^{-N}` needed to make the grid `16`-separated, is why the
threshold `δ₀` of GWZ Lemma 7.7(A) depends on `N`.
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

/-! ### Pigeonhole over a cover -/

/-- **Pigeonhole over a cover** (blueprint `lem:pigeonhole_over_cover`).

If the finite set `L` is covered by the sets `F a`, `a ∈ A`, then one of the classes retains a
proportion `1/|A|` of `L`.  Choosing `a` to maximize `|L ∩ F a|` and bounding `L` by the union is
the whole content. -/
theorem exists_card_le_mul_card_inter {α β : Type*} [DecidableEq α] {A : Finset β}
    (hA : A.Nonempty) (F : β → Finset α) (L : Finset α)
    (hcov : ∀ i ∈ L, ∃ a ∈ A, i ∈ F a) :
    ∃ a ∈ A, L.card ≤ A.card * (L ∩ F a).card := by
  have hsub : L ⊆ A.biUnion fun a => L ∩ F a := fun i hi => by
    obtain ⟨a, haA, hai⟩ := hcov i hi
    exact Finset.mem_biUnion.mpr ⟨a, haA, Finset.mem_inter.mpr ⟨hi, hai⟩⟩
  have hcsum : L.card ≤ A.sum fun a => (L ∩ F a).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  obtain ⟨a₀, ha₀A, hmax⟩ := Finset.exists_max_image A (fun a => (L ∩ F a).card) hA
  exact ⟨a₀, ha₀A, hcsum.trans ((Finset.sum_le_sum hmax).trans (by simp))⟩

/-! ### The two geometric one-move lemmas -/

variable {ι : Type*}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The leaves of a node lie in an inflated fibre** (blueprint
`lem:node_leaves_in_inflated_fibre`).  If the `δ`-tubes `T i₁` and `T i` both lie in one `ρ`-tube
`P`, then `Tube.rescale_le_of_le` puts `P` inside `T_{i₁}^{(4ρ)}`, hence `i ∈ s_{δ∣4ρ}(i₁)`.  This
factor `4` is the reason the grid scales of the multiscale chain are taken `16`-separated. -/
theorem mem_fibreIndex_four_mul_of_le_common {δ ρ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {P : Tube ρ E} {i₁ i : ι} (hi : i ∈ s)
    (hP₁ : (T i₁).toConvexSpaceBody ≤ P.toConvexSpaceBody)
    (hPi : (T i).toConvexSpaceBody ≤ P.toConvexSpaceBody) :
    i ∈ fibreIndex s T δ (4 * ρ) i₁ := by
  rw [fibreIndex_self]
  exact Finset.mem_filter.mpr ⟨hi, hPi.trans (Tube.rescale_le_of_le (T i₁) P hP₁)⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A common small tube is an exact-scale fibre of each of its members** (blueprint
`lem:common_small_tube_gives_exact_fibre`).  If `L' ⊆ s_{δ∣ρ/4}(i₂)` then `L' ⊆ s_{δ∣ρ}(i)` for
every `i ∈ L'`: the resolution `ρ/4` is the largest one for which the `4`-fold inflation lands back
at the exact scale `ρ`.  This is what turns a clumping into a *lower* bound on a single fibre. -/
theorem subset_fibreIndex_of_subset_fibreIndex_quarter {δ ρ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {i₂ : ι} {L' : Finset ι}
    (hL' : L' ⊆ fibreIndex s T δ (ρ / 4) i₂) {i : ι} (hi : i ∈ L') :
    L' ⊆ fibreIndex s T δ ρ i := by
  have h4 : (4 : NNReal) * (ρ / 4) = ρ := by
    rw [mul_comm]; exact div_mul_cancel₀ ρ (by norm_num : (4 : NNReal) ≠ 0)
  rw [fibreIndex_self] at hL'
  have hi' := Finset.mem_filter.mp (hL' hi)
  intro j hj
  have hj' := Finset.mem_filter.mp (hL' hj)
  rw [← h4]
  exact mem_fibreIndex_four_mul_of_le_common hj'.1 hi'.2 hj'.2

/-! ### Clumping -/

/-- **Clumping the leaves of a node** (blueprint `lem:clumping_refinement`).  At the cost of the
dimensional factor `2 · 25^{2n} · 16^{2n}` one may pass to a subset `L'` of the leaves of a `ρ`-tube
`P` all of whose members lie in one common tube of radius `ρ/4`; every retained leaf then sees the
whole retained set inside its own exact-scale thickening. -/
theorem exists_clumped_subset_of_leaves {δ ρ : NNReal} (hδ : 0 < δ) (hρ : 8 * δ ≤ ρ)
    (s : Finset ι) (T : ι → Tube δ E) (P : Tube ρ E) (L : Finset ι) (hL : L.Nonempty)
    (hLs : L ⊆ s) (hLP : ∀ i ∈ L, (T i).toConvexSpaceBody ≤ P.toConvexSpaceBody) :
    ∃ i₂ ∈ s, ∃ L' ⊆ L,
      (L.card : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
            * (16 : ℝ) ^ (2 * Module.finrank ℝ E) * (L'.card : ℝ) ∧
        L' ⊆ fibreIndex s T δ (ρ / 4) i₂ ∧
        ∀ i ∈ L', L' ⊆ fibreIndex s T δ ρ i := by
  classical
  rcases hL with ⟨i₁, hi₁L⟩
  have hρpos : 0 < ρ := lt_of_lt_of_le (mul_pos (by norm_num) hδ) hρ
  have hcov : L ⊆ fibreIndex s T δ (4 * ρ) i₁ := fun i hi =>
    mem_fibreIndex_four_mul_of_le_common (hLs hi) (hLP i₁ hi₁L) (hLP i hi)
  have hquarter : (2 : NNReal) * δ ≤ ρ / 4 := by
    rw [show (2 : NNReal) * δ = 8 * δ / 4 by ring]
    gcongr
  rcases exists_gapFibre_cover_of_ratio (σ := δ) (ρ := ρ / 4) (ρ' := 4 * ρ)
      (s := s) (T := T) (div_pos hρpos (by norm_num)) (le_refl δ) hquarter
      ((div_le_self zero_le (by norm_num)).trans (le_mul_of_one_le_left zero_le (by norm_num)))
      i₁ with ⟨A, hAs, hAcard, hAcov⟩
  have hcovL : ∀ i ∈ L, ∃ a ∈ A, i ∈ fibreIndex s T δ (ρ / 4) a := fun i hi => hAcov i (hcov hi)
  rcases exists_card_le_mul_card_inter ((hcovL i₁ hi₁L).imp fun _ ha => ha.1)
      (fun a : ι => fibreIndex s T δ (ρ / 4) a) L hcovL with ⟨i₂, hi₂A, hpig⟩
  have hρR : (ρ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hρpos)
  rw [show ((4 * ρ : NNReal) : ℝ) / ((ρ / 4 : NNReal) : ℝ) = 16 by push_cast; field_simp; ring]
    at hAcard
  refine ⟨i₂, hAs hi₂A, L ∩ fibreIndex s T δ (ρ / 4) i₂, Finset.inter_subset_left, ?_,
    Finset.inter_subset_right,
    fun i hi => subset_fibreIndex_of_subset_fibreIndex_quarter Finset.inter_subset_right hi⟩
  calc (L.card : ℝ)
      ≤ (A.card : ℝ) * ((L ∩ fibreIndex s T δ (ρ / 4) i₂).card : ℝ) := by exact_mod_cast hpig
    _ ≤ _ := mul_le_mul_of_nonneg_right hAcard (Nat.cast_nonneg _)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A fibre containment in an ambient index set restricts to any sub-index-set containing the
family in question: `fibreIndex` filters the ambient set by a condition that does not mention it. -/
private theorem subset_fibreIndex_restrict {δ ρ : NNReal} {s t' : Finset ι} {T : ι → Tube δ E}
    {i₂ : ι} {L : Finset ι} (hL : L ⊆ t') (h : L ⊆ fibreIndex s T δ ρ i₂) :
    L ⊆ fibreIndex t' T δ ρ i₂ := by
  rw [fibreIndex_self] at h ⊢
  exact fun j hj => Finset.mem_filter.mpr ⟨hL hj, (Finset.mem_filter.mp (h hj)).2⟩

/-- **One clumping pass at a fixed grid scale.**  The classes of `𝒞.indexSet k` are pairwise
disjoint, so `exists_clumped_subset_of_leaves` may be applied to each of them separately and the
retained parts unioned; the per-class losses do not accumulate over nodes, and the step costs the
single dimensional factor `2 · 25^{2n} · 16^{2n}`. -/
private theorem clump_one_scale {δ : NNReal} (hδ : 0 < δ) {N k : ℕ} {s t : Finset ι} (hts : t ⊆ s)
    (T : ι → Tube δ E) (𝒞 : GridCoverSystem t T N) (hk : k ≤ N)
    (hρ : 8 * δ ≤ gridScale δ N k) (hs : s.Nonempty) {u : Finset ι} (hut : u ⊆ t) :
    ∃ v ⊆ u,
      (u.card : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
            * (16 : ℝ) ^ (2 * Module.finrank ℝ E) * (v.card : ℝ) ∧
        ∀ P ∈ 𝒞.indexSet k, ∃ i₂ ∈ s,
          coverClass v (𝒞.assign k) P ⊆ fibreIndex s T δ (gridScale δ N k / 4) i₂ := by
  classical
  let ρ : NNReal := gridScale δ N k
  let C : ι → Finset ι := fun P => coverClass u (𝒞.assign k) P
  let factor : ℝ := 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (16 : ℝ) ^ (2 * Module.finrank ℝ E)
  have hclass_u : ∀ P, C P ⊆ u := fun _ _ hi => (Finset.mem_filter.mp hi).1
  have hCassign : ∀ P i, i ∈ C P → 𝒞.assign k i = P := fun _ _ hi => (Finset.mem_filter.mp hi).2
  have hdisj : ((𝒞.indexSet k : Finset ι) : Set ι).PairwiseDisjoint C :=
    fun a _ b _ hab =>
      Finset.disjoint_filter.mpr fun i _ hia hib => hab (hia.symm.trans hib)
  have hcover : u = (𝒞.indexSet k).biUnion C := Finset.Subset.antisymm
    (fun i hi => Finset.mem_biUnion.mpr ⟨𝒞.assign k i, 𝒞.assign_mem k hk i (hut hi),
      Finset.mem_filter.mpr ⟨hi, rfl⟩⟩)
    (fun _ hi => let ⟨P, _, hiP⟩ := Finset.mem_biUnion.mp hi; hclass_u P hiP)
  have hgood : ∀ P, ∃ a, a ∈ s ∧ ∃ l : Finset ι,
      l ⊆ C P ∧ (C P).card ≤ factor * (l.card : ℝ) ∧
        l ⊆ fibreIndex s T δ (ρ / 4) a := by
    intro P
    rcases Finset.eq_empty_or_nonempty (C P) with hCempty | hne
    · obtain ⟨a, ha⟩ := hs
      exact ⟨a, ha, ∅, Finset.empty_subset _, by simp [hCempty], Finset.empty_subset _⟩
    · have hLP : ∀ i ∈ C P, (T i).toConvexSpaceBody ≤ (𝒞.tube k P).toConvexSpaceBody := fun i hi =>
        hCassign P i hi ▸ 𝒞.le_tube_assign k hk i (hut (hclass_u P hi))
      obtain ⟨i₂, hi₂s, L', hL'sub, hcard, hfib, -⟩ :=
        exists_clumped_subset_of_leaves hδ hρ s T (𝒞.tube k P) (C P) hne
          (fun _ hi => hts (hut (hclass_u P hi))) hLP
      exact ⟨i₂, hi₂s, L', hL'sub, hcard, hfib⟩
  choose anchor hanchor clump hclump_sub hclump_card hclump_fib using hgood
  let v : Finset ι := (𝒞.indexSet k).biUnion (fun P => clump P)
  have hv_u : v ⊆ u := fun _ hi =>
    let ⟨P, _, hiP⟩ := Finset.mem_biUnion.mp hi; hclass_u P (hclump_sub P hiP)
  have hdisjclump : ((𝒞.indexSet k : Finset ι) : Set ι).PairwiseDisjoint clump :=
    fun a ha b hb hab => Disjoint.mono (hclump_sub a) (hclump_sub b) (hdisj ha hb hab)
  have hv_card : (v.card : ℝ) = ∑ P ∈ 𝒞.indexSet k, ((clump P).card : ℝ) := by
    dsimp [v]
    rw [Finset.card_biUnion hdisjclump, Nat.cast_sum]
  have hu_le : (u.card : ℝ) ≤ factor * (v.card : ℝ) :=
    calc
      (u.card : ℝ) = ∑ P ∈ 𝒞.indexSet k, ((C P).card : ℝ) := by
        rw [hcover, Finset.card_biUnion hdisj, Nat.cast_sum]
      _ ≤ ∑ P ∈ 𝒞.indexSet k, (factor * ((clump P).card : ℝ)) :=
        Finset.sum_le_sum fun P _ => hclump_card P
      _ = factor * (v.card : ℝ) := by rw [← Finset.mul_sum, hv_card]
  have hvc : ∀ P, P ∈ 𝒞.indexSet k → coverClass v (𝒞.assign k) P = clump P := by
    intro P hP
    refine Finset.Subset.antisymm (fun i hi => ?_) (fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨P, hP, hi⟩,
        hCassign P i (hclump_sub P hi)⟩)
    obtain ⟨hiv, hiP⟩ := Finset.mem_filter.mp hi
    obtain ⟨Q, -, hiQ⟩ := Finset.mem_biUnion.mp hiv
    exact ((hCassign Q i (hclump_sub Q hiQ)).symm.trans hiP) ▸ hiQ
  exact ⟨v, hv_u, hu_le, fun P hP => ⟨anchor P, hanchor P, by
    rw [hvc P hP]; exact hclump_fib P⟩⟩

/-- The induction step behind `clump_iterate`: at `m` scales already clumped, we have a retained
`u ⊆ t` proving the bound `|t| ≤ D^m · |u|` and, at every `k < m`, the clumping
`coverClass u (assign k) P ⊆ (ρ_k/4)-fibre`. -/
private theorem clump_iterate_aux {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {s t : Finset ι} (hts : t ⊆ s) (T : ι → Tube δ E)
    (𝒞 : GridCoverSystem t T N) (hs : s.Nonempty) :
    ∀ m, m ≤ N → ∃ u ⊆ t,
      (t.card : ℝ) ≤ (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
            * (16 : ℝ) ^ (2 * Module.finrank ℝ E)) ^ m * (u.card : ℝ) ∧
        ∀ k < m, ∀ P ∈ 𝒞.indexSet k, ∃ i₂ ∈ s,
          coverClass u (𝒞.assign k) P ⊆ fibreIndex s T δ (gridScale δ N k / 4) i₂ := by
  classical
  intro m
  induction m with
  | zero =>
      exact fun _ => ⟨t, Finset.Subset.refl t, by simp, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ m ih =>
      intro hmsucc
      have hmleN : m ≤ N := by omega
      obtain ⟨u, hut, hcard, hclump⟩ := ih hmleN
      have h8 : 8 * δ ≤ gridScale δ N m := eight_delta_le_gridScale hδ hδ1 (by omega) hδN
      obtain ⟨v, hvu, hvcard, hvclump⟩ := clump_one_scale hδ hts T 𝒞 hmleN h8 hs hut
      set D : ℝ := 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (16 : ℝ) ^ (2 * Module.finrank ℝ E)
        with hDdef
      have hDnonneg : (0 : ℝ) ≤ D := by rw [hDdef]; positivity
      refine ⟨v, fun i hi => hut (hvu hi), ?_, fun k hk P hP => ?_⟩
      · exact hcard.trans ((mul_le_mul_of_nonneg_left hvcard (pow_nonneg hDnonneg m)).trans
          (le_of_eq (by ring)))
      · rcases (by omega : k < m ∨ k = m) with hkm | rfl
        · obtain ⟨i₂, hi₂s, hsub⟩ := hclump k hkm P hP
          exact ⟨i₂, hi₂s, (coverClass_subset_of_subset hvu (𝒞.assign k) P).trans hsub⟩
        · exact hvclump P hP

/-- **The `N`-fold iteration of `clump_one_scale`.**  Step `k` is applied to the set retained by
step `k - 1`; the clumping installed at a scale is inherited by subsets
(`coverClass_subset_of_subset`), so later steps do not destroy earlier ones. -/
private theorem clump_iterate {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {s t : Finset ι} (hts : t ⊆ s) (T : ι → Tube δ E)
    (𝒞 : GridCoverSystem t T N) (hs : s.Nonempty) :
    ∃ t' ⊆ t,
      (t.card : ℝ) ≤ (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
            * (16 : ℝ) ^ (2 * Module.finrank ℝ E)) ^ N * (t'.card : ℝ) ∧
        ∀ k < N, ∀ P ∈ 𝒞.indexSet k, ∃ i₂ ∈ s,
          coverClass t' (𝒞.assign k) P ⊆ fibreIndex s T δ (gridScale δ N k / 4) i₂ :=
  clump_iterate_aux hδ hδ1 hδN hts T 𝒞 hs N (le_refl N)

/-- **Clumping at every grid scale** (blueprint `lem:clump_along_grid`).  One pass over
`k = 0, …, N-1`, each step applied to the set retained by the previous one and to each class of the
fixed cover separately; the classes at a fixed scale are disjoint, so the losses do not add over
nodes and a step costs one dimensional factor.  The bottom scale `ρ_N = δ` is not clumped. -/
theorem exists_clumped_subset_along_grid {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {s t : Finset ι} (hts : t ⊆ s) (T : ι → Tube δ E)
    (𝒞 : GridCoverSystem t T N) (hs : s.Nonempty) :
    ∃ t' ⊆ t,
      (t.card : ℝ) ≤ (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
            * (16 : ℝ) ^ (2 * Module.finrank ℝ E)) ^ N * (t'.card : ℝ) ∧
        ∀ k < N, ∀ P ∈ 𝒞.indexSet k,
          (∃ i₂ ∈ s, coverClass t' (𝒞.assign k) P ⊆ fibreIndex s T δ (gridScale δ N k / 4) i₂) ∧
          ∀ i ∈ coverClass t' (𝒞.assign k) P,
            coverClass t' (𝒞.assign k) P ⊆ fibreIndex t' T δ (gridScale δ N k) i := by
  classical
  obtain ⟨t', ht'_sub, hcard, hclump⟩ := clump_iterate hδ hδ1 hδN hts T 𝒞 hs
  refine ⟨t', ht'_sub, hcard, fun k hk P hP => ?_⟩
  obtain ⟨i₂, hi₂, hsub⟩ := hclump k hk P hP
  exact ⟨⟨i₂, hi₂, hsub⟩, fun i hi => subset_fibreIndex_of_subset_fibreIndex_quarter
    (subset_fibreIndex_restrict (fun j hj => (Finset.mem_filter.mp hj).1) hsub) hi⟩

/-! ### Uniformization -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- One dyadic-pigeonhole step at scale `k`: from a nonempty `u`, extract a nonempty `v ⊆ u`
together with a branching number `Nb = 2^j` such that every member of `v` has `𝒞.assign k`-class
size in `[Nb, 2·Nb)`.  Whole classes are retained, so each retained element keeps its entire class,
and the step loses the single share `1/(⌊log₂|u|⌋+1)`. -/
private theorem one_step
    {N k : ℕ} {ι : Type u} {δ : NNReal} {t : Finset ι} (T : ι → Tube δ E)
    (𝒞 : GridCoverSystem t T N) {u : Finset ι} (hu_n : u.Nonempty) :
    ∃ (v : Finset ι) (Nb : ℕ), v ⊆ u ∧ v.Nonempty ∧
      (∀ i ∈ v, Nb ≤ (coverClass v (𝒞.assign k) (𝒞.assign k i)).card ∧
        (coverClass v (𝒞.assign k) (𝒞.assign k i)).card < 2 * Nb) ∧
      (∀ i ∈ v, coverClass v (𝒞.assign k) (𝒞.assign k i) =
        coverClass u (𝒞.assign k) (𝒞.assign k i)) ∧
      (u.card : ℝ) / ((⌊Real.logb 2 (u.card : ℝ)⌋₊ + 1 : ℝ)) ≤ (v.card : ℝ) := by
  classical
  let assign : ι → ι := 𝒞.assign k
  obtain ⟨j, S, hS_sub, hS_band, hS_full, hS_bound, _⟩ :=
    Nat.dyadic_pigeonhole_fibre u assign
  have hs'_ne : S.Nonempty := Finset.card_pos.mp (by
    have h : (0 : ℝ) < (S.card : ℝ) :=
      lt_of_lt_of_le (div_pos (by exact_mod_cast Finset.card_pos.mpr hu_n) (by positivity)) hS_bound
    exact_mod_cast h)
  have hcls_v : ∀ (i₀ : ι), i₀ ∈ S →
      u.filter (fun i' => assign i' = assign i₀) = S.filter (fun i' => assign i' = assign i₀) :=
    fun i₀ hi₀ => Finset.Subset.antisymm (fun i' hi' =>
      Finset.mem_filter.mpr ⟨hS_full i' (Finset.mem_filter.mp hi').1
        (by rw [(Finset.mem_filter.mp hi').2]; exact hS_band i₀ hi₀),
        (Finset.mem_filter.mp hi').2⟩) (Finset.filter_subset_filter _ hS_sub)
  have hband_v : ∀ i ∈ S, 2 ^ j ≤ (S.filter (fun i' => assign i' = assign i)).card ∧
      (S.filter (fun i' => assign i' = assign i)).card < 2 * 2 ^ j := fun i hi => by
    rw [← hcls_v i hi]
    exact ⟨(hS_band i hi).1, by simpa [Nat.pow_succ, Nat.mul_comm] using (hS_band i hi).2⟩
  exact ⟨S, 2 ^ j, hS_sub, hs'_ne, fun i hi => by simpa [coverClass] using hband_v i hi,
    fun i hi => by simpa [coverClass] using (hcls_v i hi).symm, hS_bound⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Deleting whole `𝒞.assign p`-classes (`p < σ`) does not disturb `𝒞.assign σ`-classes: since
`𝒞.nested` puts each `assign σ`-class inside an `assign p`-class, and every retained element keeps
its whole `assign p`-class, its `assign σ`-class is unaffected (fact (b)). -/
private theorem coarse_pruning_preserves_class
    {N p σ : ℕ} {ι : Type u} {δ : NNReal} {t : Finset ι} (T : ι → Tube δ E)
    (𝒞 : GridCoverSystem t T N) (hpσ : p < σ) (hσN : σ ≤ N)
    {v w : Finset ι} (hv : v ⊆ t) (hwv : w ⊆ v)
    (hretain : ∀ i ∈ w, coverClass v (𝒞.assign p) (𝒞.assign p i) ⊆ w)
    {i : ι} (hi : i ∈ w) :
    coverClass w (𝒞.assign σ) (𝒞.assign σ i) = coverClass v (𝒞.assign σ) (𝒞.assign σ i) := by
  classical
  have hdown : ∀ q, p ≤ q → q ≤ N → ∀ x ∈ t, ∀ y ∈ t,
      𝒞.assign q x = 𝒞.assign q y → 𝒞.assign p x = 𝒞.assign p y := by
    refine Nat.le_induction (fun _ _ _ _ _ hxy => hxy) (fun n _ ih hqN x hx y hy hxy => ?_)
    exact ih (by omega) x hx y hy (𝒞.nested n hqN x hx y hy hxy)
  refine Finset.Subset.antisymm (coverClass_subset_of_subset hwv _ _) fun j hj => ?_
  obtain ⟨hjv, hjσ⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨hretain i hi (Finset.mem_filter.mpr ⟨hjv,
    hdown σ hpσ.le hσN j (hv hjv) i (hv (hwv hi)) hjσ⟩), hjσ⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The induction invariant: after pruning the `m` finest scales `N, …, N+1-m`, the surviving set
`u` carries a band `Nb k` at every scale `k ∈ [N+1-m, N]`, and loses the `m` share factors. -/
private theorem nested_pigeonhole_aux
    {N : ℕ} {ι : Type u} {δ : NNReal} {t : Finset ι} (T : ι → Tube δ E)
    (𝒞 : GridCoverSystem t T N) (ht : t.Nonempty) :
    ∀ m : ℕ, m ≤ N + 1 →
    ∃ (u : Finset ι) (Nb : ℕ → ℕ), u ⊆ t ∧ u.Nonempty ∧
      (t.card : ℝ) ≤ ((⌊Real.logb 2 (t.card : ℝ)⌋₊ + 1 : ℝ) ^ m) * (u.card : ℝ) ∧
      (∀ k : ℕ, N + 1 - m ≤ k → k ≤ N → ∀ i ∈ u,
        Nb k ≤ (coverClass u (𝒞.assign k) (𝒞.assign k i)).card ∧
        (coverClass u (𝒞.assign k) (𝒞.assign k i)).card < 2 * Nb k) := by
  classical
  intro m
  induction m with
  | zero =>
      exact fun _ => ⟨t, fun _ => 0, Finset.Subset.refl t, ht, by simp,
        fun k hk_ge hk_le => by omega⟩
  | succ m ih =>
      intro hm1
      rcases ih (by omega) with ⟨u, Nb, hu_t, hu_n, hbound, hbands⟩
      obtain ⟨v, M, hv_u, hv_n, hvBand, hvCls, hvShare⟩ := one_step T 𝒞 hu_n
      let Nb' : ℕ → ℕ := fun k => if k = N - m then M else Nb k
      have hretain : ∀ i ∈ v, (coverClass u (𝒞.assign (N - m)) (𝒞.assign (N - m) i)) ⊆ v :=
        fun i hi => by rw [← hvCls i hi]; exact Finset.filter_subset _ _
      let factor : ℝ := ((⌊Real.logb 2 (t.card : ℝ)⌋₊ : ℝ) + 1)
      have hfactor_pos : (0 : ℝ) < factor := by
        dsimp [factor]
        exact_mod_cast (Nat.succ_pos ⌊Real.logb 2 (t.card : ℝ)⌋₊)
      have hfactor : ((⌊Real.logb 2 (u.card : ℝ)⌋₊ : ℝ) + 1) ≤ factor := by
        have hlogu : Real.logb 2 (u.card : ℝ) ≤ Real.logb 2 (t.card : ℝ) :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast Finset.card_pos.mpr hu_n)
            (by exact_mod_cast Finset.card_le_card hu_t)
        dsimp [factor]
        exact_mod_cast Nat.succ_le_succ (Nat.floor_le_floor hlogu)
      have hfpos_u : (0 : ℝ) < ((⌊Real.logb 2 (u.card : ℝ)⌋₊ : ℝ) + 1) := by
        exact_mod_cast (Nat.succ_pos ⌊Real.logb 2 (u.card : ℝ)⌋₊)
      have hvshare'' : (u.card : ℝ) ≤ factor * (v.card : ℝ) := by
        rw [mul_comm]
        exact ((div_le_iff₀ hfpos_u).1 hvShare).trans
          (mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg v.card))
      have hbound' : (t.card : ℝ) ≤ factor ^ (m + 1) * (v.card : ℝ) := by
        rw [pow_succ, mul_assoc]
        exact hbound.trans (mul_le_mul_of_nonneg_left hvshare'' (pow_nonneg hfactor_pos.le m))
      refine ⟨v, Nb', fun i hi => hu_t (hv_u hi), hv_n, hbound', ?_⟩
      intro k hk_ge hk_le
      by_cases hkeq : k = N - m
      · subst k
        intro i hi
        simpa only [Nb', eq_self_iff_true, if_true] using hvBand i hi
      · intro i hi
        have hb_old := hbands k (by omega) hk_le i (hv_u hi)
        rw [← coarse_pruning_preserves_class T 𝒞 (show N - m < k by omega) hk_le hu_t hv_u
          hretain (i := i) hi] at hb_old
        simpa only [Nb', if_neg hkeq] using hb_old

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The full downward pass over `k = N, N−1, …, 0` (blueprint `lem:uniformize_along_grid`):
each step is `one_step` at scale `k` applied to `uSeq (k+1)`, giving `uSeq k`; the band installed
at scale `k` is preserved down to `uSeq 0` by `coarse_pruning_preserves_class` (the later, coarser
prunings keep whole classes), and the `N+1` share factors give
`|t| ≤ (⌊log₂|t|⌋+1)^(N+1) · |uSeq 0|`. -/
private theorem nested_pigeonhole_induct
    {N : ℕ} {ι : Type u} {δ : NNReal} {t : Finset ι} (T : ι → Tube δ E)
    (𝒞 : GridCoverSystem t T N) (ht : t.Nonempty) :
    ∃ (u : Finset ι) (Nb : ℕ → ℕ), u ⊆ t ∧ u.Nonempty ∧
      (t.card : ℝ) ≤ ((⌊Real.logb 2 (t.card : ℝ)⌋₊ + 1 : ℝ) ^ (N + 1)) * (u.card : ℝ) ∧
      (∀ k ≤ N, ∀ i ∈ u, Nb k ≤ (coverClass u (𝒞.assign k) (𝒞.assign k i)).card ∧
        (coverClass u (𝒞.assign k) (𝒞.assign k i)).card < 2 * Nb k) := by
  obtain ⟨u, Nb, hu_t, hu_n, hbound, hbands⟩ := nested_pigeonhole_aux T 𝒞 ht (N + 1) le_rfl
  exact ⟨u, Nb, hu_t, hu_n, hbound, fun k hkN i hi => hbands k (by omega) hkN i hi⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Nested dyadic pigeonhole over the `N + 1` grid scales.**  One `Nat.dyadic_pigeonhole_fibre`
per scale `k = N, N - 1, …, 0`, retaining complete classes; nestedness of the cover system makes a
retained coarse class a union of retained finer classes, so no constancy installed at one scale is
destroyed below it.  The loss is one factor of `⌊log₂ |t|⌋ + 1` per scale, `N + 1` in total. -/
private theorem exists_nested_pigeonhole (N : ℕ) {ι : Type u} {δ : NNReal}
    (t : Finset ι) (T : ι → Tube δ E) (ht : t.Nonempty)
    (𝒞 : GridCoverSystem t T N) :
    ∃ (u : Finset ι) (Nb : ℕ → ℕ), u ⊆ t ∧ u.Nonempty ∧
      (t.card : ℝ) ≤ ((⌊Real.logb 2 (t.card : ℝ)⌋₊ + 1 : ℝ) ^ (N + 1)) * (u.card : ℝ) ∧
      (∀ k ≤ N, ∀ i ∈ u, Nb k ≤ (coverClass u (𝒞.assign k) (𝒞.assign k i)).card ∧
        (coverClass u (𝒞.assign k) (𝒞.assign k i)).card < 2 * Nb k) :=
  nested_pigeonhole_induct T 𝒞 ht

/-- The vacuous single-scale uniformity carried by the empty family, with the parent tubes
prescribed.  Every field of `Tube.IsUniformAtScale` quantifies over members of `∅`, so both the
branching number and the parent family may be chosen freely; this is what dispatches the degenerate
cases of the hoisted lemmas and of `gridUniformEmpty`. -/
private noncomputable def isUniformAtScaleEmpty {δ ρ C D : NNReal} {ι : Type*}
    (T : ι → Tube δ E) (Tρ : ι → Tube ρ E) :
    Tube.IsUniformAtScale (∅ : Finset ι) T ρ C D where -- (extracted by Fuse golfer)
  branchingN := 1
  parent := ∅
  parentTube := Tρ
  exists_le_rescale := fun hi => absurd hi (Finset.notMem_empty _)
  boundedOverlap := fun _ => by
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_le]
  parentTube_injOn := fun a ha _ _ _ => absurd ha (Finset.notMem_empty a)
  card_filter_le := fun hj => absurd hj (Finset.notMem_empty _)
  le_mul_card_filter := fun hj => absurd hj (Finset.notMem_empty _)

/-- **Restoring uniformity along prescribed covers** (blueprint `lem:uniformize_along_grid`).  The
`N + 1` dyadic pigeonholes are run as a single nested pass from the finest scale upwards.  The
output cover is a *sub*-family of the prescribed one, and class sizes are compared with the
assigned **classes**.  Both constants are quantified *before* the grid length `N`. -/
private theorem exists_uniformize_along_grid_hoisted :
    ∃ (Cn : ℝ) (Cu : NNReal), 1 ≤ Cu ∧
      ∀ (N : ℕ),
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ < 1 →
      ∀ (s t : Finset ι) (T : ι → Tube δ E), t ⊆ s →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ 𝒞 : GridCoverSystem t T N,
        (∀ k ≤ N,
          Set.InjOn (𝒞.tube k) (𝒞.indexSet k : Set ι) ∧
          ∀ (V : Tube (gridScale δ N k) E),
            ((𝒞.indexSet k).filter (fun v => ∃ i ∈ t,
              (T i).toConvexSpaceBody ≤ (𝒞.tube k v).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
                Tube.overlapConstBOTight (Module.finrank ℝ E)) →
      ∃ u ⊆ t,
        (t.card : ℝ) ≤ (1 + 2 * (Module.finrank ℝ E : ℝ) * Real.logb 2 (1 / (δ : ℝ)) + Cn)
              ^ (N + 1) * (u.card : ℝ) ∧
          ∀ k ≤ N, ∃ h : Tube.IsUniformAtScale u T (gridScale δ N k) Cu,
            h.parent ⊆ 𝒞.indexSet k ∧
            (∀ i ∈ u, 𝒞.assign k i ∈ h.parent) ∧
            (∀ P ∈ h.parent, h.parentTube P = 𝒞.tube k P) ∧
            ∀ P ∈ h.parent,
              h.branchingN ≤ ((coverClass u (𝒞.assign k) P).card : NNReal) ∧
                ((coverClass u (𝒞.assign k) P).card : NNReal) ≤ 2 * h.branchingN := by
  classical
  set n : ℕ := Module.finrank ℝ E
  refine ⟨Real.logb 2 (Tube.card_le_of_EssDistinct.C n), 2 * (Tube.overlapConstBOTight n : NNReal),
    le_trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by simp [Tube.overlapConstBOTight]))
      (le_mul_of_one_le_left zero_le one_le_two), ?main⟩
  · intro N ι δ hδ hδ1 s t T hts hs_B1 hs_ED 𝒞 hNice
    rcases t.eq_empty_or_nonempty with rfl | ht_ne
    · exact ⟨∅, by simp, by simp, fun k _ =>
        ⟨isUniformAtScaleEmpty T fun i => (T i).rescale (gridScale δ N k),
          Finset.empty_subset _, fun i hi => absurd hi (Finset.notMem_empty i),
          fun P hP => absurd hP (Finset.notMem_empty P),
          fun P hP => absurd hP (Finset.notMem_empty P)⟩⟩
    · obtain ⟨u, Nb, hu_t, hu_n, hbound, hbands⟩ := exists_nested_pigeonhole N t T ht_ne 𝒞
      have hC_pos : (0 : ℝ) < Tube.card_le_of_EssDistinct.C n := Tube.card_le_of_EssDistinct.C_pos
      have hpow_pos : (0 : ℝ) < (1 / (δ : ℝ)) ^ (2 * n) :=
        pow_pos (one_div_pos.mpr (NNReal.coe_pos.mpr hδ)) _
      have hbase : ((⌊Real.logb 2 (t.card : ℝ)⌋₊ : ℝ) + 1) ≤
          1 + 2 * (n : ℝ) * Real.logb 2 (1 / (δ : ℝ))
            + Real.logb 2 (Tube.card_le_of_EssDistinct.C n) := by
        have hlog := (Real.logb_le_logb (b := 2) (by norm_num : (1 : ℝ) < 2)
          (Nat.cast_pos.mpr (Finset.card_pos.mpr ht_ne)) (mul_pos hC_pos hpow_pos)).mpr
          (Tube.card_le_of_EssDistinct (E := E) hδ (1 : ℝ) t T (fun i hi => hs_B1 i (hts hi))
            (hs_ED.mono (Finset.coe_subset.mpr hts)))
        rw [Real.logb_mul hC_pos.ne' hpow_pos.ne', Real.logb_pow] at hlog
        have hfl := Nat.floor_le (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
          (Nat.one_le_cast.mpr (Finset.card_pos.mpr ht_ne)))
        push_cast at hlog ⊢
        linarith
      refine ⟨u, hu_t, hbound.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
        (add_nonneg (Nat.cast_nonneg _) zero_le_one) hbase (N + 1)) (Nat.cast_nonneg u.card)),
        ?_band⟩
      · intro k hk
        let ρ : ℕ → NNReal := fun _ => gridScale δ N k
        let parentFull : ℕ → Finset ι := fun _ => 𝒞.indexSet k
        let assign : ℕ → ι → ι := fun _ => 𝒞.assign k
        let W : ∀ j, ι → Tube (ρ j) E := fun _ => 𝒞.tube k
        let parentAss : ℕ → Finset ι := fun _ => u.image (𝒞.assign k)
        have hpar'_sub : ∀ j ≤ 0, parentAss j ⊆ parentFull j := fun _ _ =>
          Finset.image_subset_iff.mpr fun i hi => 𝒞.assign_mem k hk i (hu_t hi)
        have hassign'_mem : ∀ j ≤ 0, ∀ i ∈ u, assign j i ∈ parentAss j :=
          fun _ _ _ hi => Finset.mem_image_of_mem (f := 𝒞.assign k) hi
        have hband_asm : ∀ j ≤ 0, ∀ v ∈ parentAss j,
            Nb k ≤ (u.filter (fun i => assign j i = v)).card ∧
            (u.filter (fun i => assign j i = v)).card < 2 * Nb k := by
          intro j _ v hv
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
          exact hbands k hk i hi
        obtain ⟨h0, -, -, hsub, hw, hbn⟩ :=
          Tube.isUniformAtScale_of_pruned_tight hδ hδ1 t T 0 ρ (fun _ => NNReal.rpow_pos hδ)
            parentFull assign W (fun _ _ i hi => 𝒞.le_tube_assign k hk i hi)
            (fun _ _ => (hNice k hk).1) (fun _ _ V => (hNice k hk).2 V)
            u (fun _ => Nb k) parentAss hu_t hpar'_sub hassign'_mem
            (fun _ _ _ hv => Finset.card_pos.mpr
              (Finset.filter_nonempty_iff.mpr (Finset.mem_image.mp hv)))
            hband_asm hu_n (fun kk hkk => absurd hkk (Nat.not_lt_zero kk))
            (k := 0) (hk := le_rfl)
        refine ⟨h0, hsub ▸ hpar'_sub 0 le_rfl, hsub ▸ hassign'_mem 0 le_rfl,
          fun P _ => congrFun hw P, fun P hP => ?_⟩
        have hb := hband_asm 0 le_rfl P (hsub ▸ hP)
        rw [hbn]; exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2.le⟩

/-! ### Comparable thickening counts -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Uniform and clumped implies comparable fibre counts** (blueprint
`lem:comparableFibreCounts_of_clumped`).  The upper bound is
`Kakeya.MultiScaleFac.card_fibreIndex_le_mul_branchingN`; the lower bound is the clumping, which
puts the whole class of `i₀` inside `s_{δ∣ρ}(i₀)`.  Together: `Cu²`-comparability at `ρ`. -/
theorem card_fibreIndex_band_of_clumped {δ ρ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}
    (h : Tube.IsUniformAtScale u T ρ Cu) {assign : ι → ι}
    (hassign : ∀ i ∈ u, assign i ∈ h.parent)
    (hlow : ∀ P ∈ h.parent, h.branchingN ≤ ((coverClass u assign P).card : NNReal))
    (hclump : ∀ P ∈ h.parent, ∃ i₂ : ι, coverClass u assign P ⊆ fibreIndex u T δ (ρ / 4) i₂)
    {i₀ : ι} (hi₀ : i₀ ∈ u) :
    h.branchingN ≤ ((fibreIndex u T δ ρ i₀).card : NNReal) ∧
      ((fibreIndex u T δ ρ i₀).card : NNReal) ≤ Cu ^ 2 * h.branchingN := by
  classical
  have hP : assign i₀ ∈ h.parent := hassign i₀ hi₀
  obtain ⟨i₂, hsub⟩ := hclump _ hP
  exact ⟨(hlow _ hP).trans (Nat.cast_le.mpr (Finset.card_le_card
      (subset_fibreIndex_of_subset_fibreIndex_quarter hsub (Finset.mem_filter.mpr ⟨hi₀, rfl⟩)))),
    card_fibreIndex_le_mul_branchingN_atScale h i₀⟩

/-- **Inflating the anchor once comparability holds** (blueprint `lem:comparable_inflate_anchor`).
`Kakeya.MultiScaleFac.exists_gapFibre_cover_of_ratio` covers `s_{δ∣4ρ}(i₀)` by at most
`2 · 100^{2n}` exact-scale fibres, each of which is at most `Cu² N'_ρ`; replacing `N'_ρ` by
`|s_{δ∣ρ}(i₁)|` uses the lower bound `hlow` supplied by the clumping. -/
theorem card_fibreIndex_four_mul_le_of_branching_lower {δ ρ Cu : NNReal} {u : Finset ι}
    {T : ι → Tube δ E} (h : Tube.IsUniformAtScale u T ρ Cu) (hρ : 0 < ρ) (h2δ : 2 * δ ≤ ρ)
    (hlow : ∀ i₁ ∈ u, h.branchingN ≤ ((fibreIndex u T δ ρ i₁).card : NNReal))
    (i₀ : ι) {i₁ : ι} (hi₁ : i₁ ∈ u) :
    ((fibreIndex u T δ (4 * ρ) i₀).card : ℝ)
      ≤ 2 * (100 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ) ^ 2
          * ((fibreIndex u T δ ρ i₁).card : ℝ) := by
  classical
  rcases exists_gapFibre_cover_of_ratio (s := u) (T := T) (δ := δ) (σ := δ) (ρ := ρ)
      (ρ' := 4 * ρ) hρ (le_refl δ) h2δ (le_mul_of_one_le_left zero_le (by norm_num)) i₀ with
    ⟨A, hA, hAcard, hcover⟩
  have hρne : (ρ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hρ)
  rw [show ((4 * ρ : NNReal) : ℝ) / (ρ : ℝ) = (4 : ℝ) by
    push_cast; rw [mul_div_assoc, div_self hρne, mul_one]] at hAcard
  have hAcard' : (A.card : ℝ) ≤ 2 * (100 : ℝ) ^ (2 * Module.finrank ℝ E) :=
    hAcard.trans_eq (by rw [mul_assoc, ← mul_pow]; norm_num)
  calc
    ((fibreIndex u T δ (4 * ρ) i₀).card : ℝ) ≤ ∑ a ∈ A, ((fibreIndex u T δ ρ a).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact Nat.cast_le.mpr ((Finset.card_le_card fun i hi =>
        Finset.mem_biUnion.mpr (hcover i hi)).trans Finset.card_biUnion_le)
    _ ≤ ∑ _a ∈ A, ((Cu : ℝ) ^ 2 * (h.branchingN : ℝ)) :=
      Finset.sum_le_sum fun a _ => by
        exact_mod_cast card_fibreIndex_le_mul_branchingN_atScale (s := u) (T := T) h a
    _ = (A.card : ℝ) * ((Cu : ℝ) ^ 2 * (h.branchingN : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (100 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ) ^ 2
        * ((fibreIndex u T δ ρ i₁).card : ℝ) := by
      rw [mul_assoc]
      exact mul_le_mul hAcard'
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hlow i₁ hi₁) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (NNReal.coe_nonneg _))
        (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))

/-- **Comparable fibre counts at the bottom grid scale** (blueprint
`lem:comparableFibreCounts_at_bottom_scale`).  At `ρ = δ` both bounds come from essential
distinctness: a packing net distributes the fibre among `C_n` classes each containing at most one
index, and the lower bound is `i₀ ∈ s_{δ∣δ}(i₀)`.  No uniformity and no clumping are involved. -/
private theorem card_fibreIndex_bottom_scale :
    ∀ {ι : Type u} {δ : NNReal}, 0 < δ →
      ∀ (u : Finset ι) (T : ι → Tube δ E),
      (↑u : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ i₀ ∈ u,
        ((fibreIndex u T δ (4 * δ) i₀).card : NNReal)
            ≤ 2 * (384 * (Module.finrank ℝ E) + 1) ^ (2 * Module.finrank ℝ E) ∧
          1 ≤ (fibreIndex u T δ δ i₀).card := by
  classical
  intro ι δ hδ u T hpair i₀ hi₀
  refine ⟨?_, Finset.card_pos.mpr ⟨i₀, mem_fibreIndex_self le_rfl hi₀⟩⟩
  let Cn : NNReal := 2 * (384 * (Module.finrank ℝ E) + 1) ^ (2 * Module.finrank ℝ E)
  change ((fibreIndex u T δ (4 * δ) i₀).card : NNReal) ≤ Cn
  let n : ℕ := Module.finrank ℝ E
  have hposn : 0 < n := Module.finrank_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hposn
  have hδ_ne : (δ : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hδ.ne'
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hposn.ne'
  let F : Finset ι := fibreIndex u T δ (4 * δ) i₀
  have hFmem : ∀ i ∈ F,
      i ∈ u ∧ (T i).toConvexSpaceBody ≤ ((T i₀).rescale (4 * δ)).toConvexSpaceBody :=
    fun i hi => by simpa only [F, fibreIndex_self, Finset.mem_filter] using hi
  have hFsub : F ⊆ u := fun i hi => (hFmem i hi).1
  have hFW : ∀ i ∈ F, (T i).toConvexSpaceBody ≤ ((T i₀).rescale (4 * δ)).toConvexSpaceBody :=
    fun i hi => (hFmem i hi).2
  let eps : ℝ := (δ : ℝ) / (8 * (n : ℝ))
  have heps : 0 < eps := by unfold eps; positivity
  have hratio : (3 * ((4 * δ : NNReal) : ℝ) + eps / 4) / (eps / 4) = (384 * (n : ℝ) + 1) := by
    rw [show ((4 * δ : NNReal) : ℝ) = 4 * (δ : ℝ) from by norm_num]
    unfold eps; field_simp [hδ_ne, hn_ne]; ring
  have hB : 2 * ((3 * ((4 * δ : NNReal) : ℝ) + eps / 4) / (eps / 4))
      ^ (2 * Module.finrank ℝ E) ≤ (Cn : ℝ) := by rw [hratio]; push_cast [Cn, n]; exact le_rfl
  obtain ⟨F', hF'sub, hnet, hcardF'⟩ :=
    exists_net_of_le_common_tube F T ((T i₀).rescale (4 * δ)) hFW heps hB
  have : Nonempty ι := ⟨i₀⟩
  choose! g hin_im hneti using hnet
  have hneti_x : ∀ i, i ∈ F → ‖(T i).x - (T (g i)).x‖ ≤ eps := fun i hi =>
    le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hneti i hi)
  have hneti_y : ∀ i, i ∈ F → ‖(T i).y - (T (g i)).y‖ ≤ eps := fun i hi =>
    le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hneti i hi)
  have hg_inj : Set.InjOn g (↑F : Set ι) := by
    intro a ha b hb hgab
    have haF : a ∈ F := Finset.mem_coe.mp ha
    have hbF : b ∈ F := Finset.mem_coe.mp hb
    by_contra hne
    let σ : ℝ := 1 / (4 * (n : ℝ))
    have hσ_nonneg : 0 ≤ σ := by unfold σ; positivity
    have hσ_le_one : σ ≤ 1 := by unfold σ; field_simp; linarith
    have hσ_strong : (1 / 2 : ℝ) < (1 - σ) ^ n := by
      have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -σ from by linarith [hσ_le_one]) n
      have hnσ : (n : ℝ) * σ = 1 / 4 := by unfold σ; field_simp [hn_ne]
      calc (1 / 2 : ℝ) < 3 / 4 := by norm_num
        _ = 1 - (n : ℝ) * σ := by rw [hnσ]; norm_num
        _ = 1 + (n : ℝ) * (-σ) := by ring
        _ ≤ (1 + (-σ)) ^ n := hbern
        _ = (1 - σ) ^ n := by ring
    have h2e : σ * (δ : ℝ) = eps + eps := by unfold σ eps; field_simp [hδ_ne, hn_ne]; ring
    have hcoord : ∀ p : ι → E, (∀ i, i ∈ F → ‖p i - p (g i)‖ ≤ eps) →
        ‖p a - p b‖ ≤ σ * (δ : ℝ) := fun p hp => calc
      ‖p a - p b‖ ≤ ‖p a - p (g a)‖ + ‖p (g a) - p b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖p a - p (g a)‖ + ‖p (g b) - p b‖ := by rw [hgab]
      _ ≤ eps + eps := add_le_add (hp a haF) (by rw [norm_sub_rev]; exact hp b hbF)
      _ = σ * (δ : ℝ) := h2e.symm
    exact (not_or.mpr ⟨not_lt.mpr (hcoord (fun i => (T i).x) hneti_x),
        not_lt.mpr (hcoord (fun i => (T i).y) hneti_y)⟩)
      (Tube.endpoint_separated_of_ed (δ := δ) (σ := σ) hδ hσ_nonneg hσ_le_one hσ_strong (T a) (T b)
        (hpair (hFsub haF) (hFsub hbF) hne))
  have hcF : (F.card : ℝ) ≤ (Cn : ℝ) := le_trans (Nat.cast_le.mpr
    ((Finset.card_image_of_injOn hg_inj).symm.trans_le
      (Finset.card_le_card (Finset.image_subset_iff.mpr hin_im)))) hcardF'
  exact_mod_cast hcF


variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Restriction of a cover system.**  A `GridCoverSystem s T N` restricts to any `t ⊆ s`: the
`indexSet`, `assign` and `tube` fields carry over verbatim, and the three axioms are inherited. -/
private theorem exists_restrict_gridCoverSystem {δ : NNReal} {N : ℕ} {s t : Finset ι}
    {T : ι → Tube δ E} (hts : t ⊆ s) (𝒞 : GridCoverSystem s T N) :
    ∃ 𝒞' : GridCoverSystem t T N,
      𝒞'.indexSet = 𝒞.indexSet ∧ 𝒞'.assign = 𝒞.assign ∧ 𝒞'.tube = 𝒞.tube :=
  ⟨{ indexSet := 𝒞.indexSet, assign := 𝒞.assign, tube := 𝒞.tube
     assign_mem := fun k hk i hi => 𝒞.assign_mem k hk i (hts hi)
     le_tube_assign := fun k hk i hi => 𝒞.le_tube_assign k hk i (hts hi)
     nested := fun k hk i hi j hj hij => 𝒞.nested k hk i (hts hi) j (hts hj) hij
     tube_nested := fun k hk i hi => 𝒞.tube_nested k hk i (hts hi) }, rfl, rfl, rfl⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Niceness restricts.**  The tight-net property of a system for `s` passes to any `t ⊆ s`:
the filtered set of nodes meeting a common tube only shrinks when the witnessing tubes are drawn
from a smaller family. -/
private theorem gridCoverSystem_nice_restrict {δ : NNReal} {N : ℕ} {s t : Finset ι}
    {T : ι → Tube δ E} {Cs : NNReal} (𝒢 : GridUniform s T N Cs) (hts : t ⊆ s)
    (𝒞' : GridCoverSystem t T N) (hparent : 𝒞'.indexSet = 𝒢.cover.indexSet)
    (htube : 𝒞'.tube = 𝒢.cover.tube) :
    ∀ k ≤ N,
      Set.InjOn (𝒞'.tube k) (𝒞'.indexSet k : Set ι) ∧
      ∀ V : Tube (gridScale δ N k) E,
        ((𝒞'.indexSet k).filter (fun v => ∃ i ∈ t,
            (T i).toConvexSpaceBody ≤ (𝒞'.tube k v).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
              Tube.overlapConstBOTight (Module.finrank ℝ E) := by
  classical
  intro k hk
  rw [hparent, htube]
  exact ⟨(𝒢.nice k hk).1, fun V => (Finset.card_le_card (Finset.monotone_filter_right _
    fun _ _ ⟨i, hi, h1, h2⟩ => ⟨i, hts hi, h1, h2⟩)).trans ((𝒢.nice k hk).2 V)⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Niceness restricts, ambient-system form.**  The same as `gridCoverSystem_nice_restrict`, but
reading the tight-net property off a bare `GridCoverSystem` rather than off a `GridUniform`.  This
is the form needed when the system is built directly by `exists_initial_gridCoverSystem`, where
no ambient uniform structure exists yet. -/
private theorem gridCoverSystem_nice_restrict_of_nice {δ : NNReal} {N : ℕ} {s t : Finset ι}
    {T : ι → Tube δ E} (𝒞 : GridCoverSystem s T N)
    (hnice : ∀ k ≤ N,
      Set.InjOn (𝒞.tube k) (𝒞.indexSet k : Set ι) ∧
      ∀ V : Tube (gridScale δ N k) E,
        ((𝒞.indexSet k).filter (fun v => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (𝒞.tube k v).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
              Tube.overlapConstBOTight (Module.finrank ℝ E))
    (hts : t ⊆ s) (𝒞' : GridCoverSystem t T N) (hparent : 𝒞'.indexSet = 𝒞.indexSet)
    (htube : 𝒞'.tube = 𝒞.tube) :
    ∀ k ≤ N,
      Set.InjOn (𝒞'.tube k) (𝒞'.indexSet k : Set ι) ∧
      ∀ V : Tube (gridScale δ N k) E,
        ((𝒞'.indexSet k).filter (fun v => ∃ i ∈ t,
            (T i).toConvexSpaceBody ≤ (𝒞'.tube k v).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
              Tube.overlapConstBOTight (Module.finrank ℝ E) := by
  classical
  intro k hk
  rw [hparent, htube]
  exact ⟨(hnice k hk).1, fun V => (Finset.card_le_card (Finset.monotone_filter_right _
    fun _ _ ⟨i, hi, h1, h2⟩ => ⟨i, hts hi, h1, h2⟩)).trans ((hnice k hk).2 V)⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Clumping restricts.**  A clump of a class inside a single `ρ`-fibre survives passing to a
subset: `fibreIndex` filters its ambient set by a condition that does not mention that set. -/
theorem clump_restrict_to_subset {δ ρ : NNReal} {t₁ t' : Finset ι} {T : ι → Tube δ E}
    (ht't : t' ⊆ t₁) (assign : ι → ι) {P : ι}
    (h : ∃ i₂ : ι, coverClass t₁ assign P ⊆ fibreIndex t₁ T δ ρ i₂) :
    ∃ i₂ : ι, coverClass t' assign P ⊆ fibreIndex t' T δ ρ i₂ := by
  classical
  exact h.imp fun i₂ hsub => subset_fibreIndex_restrict (s := t₁)
    (fun i hi => (Finset.mem_filter.mp hi).1)
    ((coverClass_subset_of_subset ht't assign P).trans hsub)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Packaging the per-scale uniform structures into a grid-uniform system.**  The cover is the
restricted system cut down to the uniform parents; `parent_eq` is then definitional and `nice` is
inherited from the ambient system. -/
theorem exists_gridUniform_pack {δ : NNReal} {N : ℕ} {u : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (𝒞' : GridCoverSystem u T N)
    (hnice : ∀ k ≤ N,
      Set.InjOn (𝒞'.tube k) (𝒞'.indexSet k : Set ι) ∧
      ∀ V : Tube (gridScale δ N k) E,
        ((𝒞'.indexSet k).filter (fun v => ∃ i ∈ u,
            (T i).toConvexSpaceBody ≤ (𝒞'.tube k v).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
              Tube.overlapConstBOTight (Module.finrank ℝ E))
    (huniform : ∀ k ≤ N, Tube.IsUniformAtScale u T (gridScale δ N k) Cu)
    (hparent : ∀ k (hk : k ≤ N), (huniform k hk).parent ⊆ 𝒞'.indexSet k)
    (hassign : ∀ k (hk : k ≤ N), ∀ i ∈ u, 𝒞'.assign k i ∈ (huniform k hk).parent)
    (hparentTube : ∀ k (hk : k ≤ N), ∀ P ∈ (huniform k hk).parent,
      (huniform k hk).parentTube P = 𝒞'.tube k P)
    (hlow : ∀ k (hk : k ≤ N), ∀ P ∈ (huniform k hk).parent,
      (huniform k hk).branchingN ≤ ((coverClass u (𝒞'.assign k) P).card : NNReal))
    (hclump : ∀ k (hk₀ : k < N), ∀ P ∈ (huniform k (le_of_lt hk₀)).parent, ∃ i₂ : ι,
      coverClass u (𝒞'.assign k) P ⊆ fibreIndex u T δ (gridScale δ N k / 4) i₂) :
    ∃ 𝒢 : GridUniform u T N Cu,
      (∀ k (hk : k ≤ N), 𝒢.uniformAt k hk = huniform k hk) ∧
      (∀ k ≤ N, 𝒢.cover.assign k = 𝒞'.assign k) ∧
      (∀ k (hk : k ≤ N), 𝒢.cover.indexSet k = (huniform k hk).parent) ∧
      (∀ k, 𝒢.cover.tube k = 𝒞'.tube k) := by
  classical
  let gparent : ℕ → Finset ι := fun k => if hk : k ≤ N then (huniform k hk).parent else ∅
  have hg : ∀ k (hk : k ≤ N), gparent k = (huniform k hk).parent := fun k hk => dif_pos hk
  refine ⟨{ cover := { indexSet := gparent,
                       assign := 𝒞'.assign,
                       tube := 𝒞'.tube,
                       assign_mem := fun k hk i hi => (hg k hk).symm ▸ hassign k hk i hi,
                       le_tube_assign := 𝒞'.le_tube_assign,
                       nested := 𝒞'.nested,
                       tube_nested := 𝒞'.tube_nested },
            uniformAt := huniform,
            parent_eq := fun k hk => (hg k hk).symm,
            tube_eq := fun k hk P hP => hparentTube k hk P (hg k hk ▸ hP),
            le_card_class := fun k hk P hP => hlow k hk P (hg k hk ▸ hP),
            clumped := fun k hk₀ P hP => hclump k hk₀ P (hg k (le_of_lt hk₀) ▸ hP),
            nice := ?_ }, fun _ _ => rfl, fun _ _ => rfl, hg, fun _ => rfl⟩
  intro k hk
  dsimp only
  rw [hg k hk]
  exact ⟨(hnice k hk).1.mono fun x hx => hparent k hk hx, fun V =>
    (Finset.card_le_card (Finset.filter_subset_filter _ (hparent k hk))).trans ((hnice k hk).2 V)⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The two-sided branching band at a middle grid scale: `card_fibreIndex_band_of_clumped`
transported from `(𝒢.uniformAt k).parent` to `𝒢.cover.indexSet k` along `𝒢.parent_eq`. -/
private theorem band_at_middle_scale {δ : NNReal} {N k : ℕ} {u : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) (hk : k < N) (𝒢 : GridUniform u T N Cu)
    (hlow : ∀ P ∈ 𝒢.cover.indexSet k,
      (𝒢.uniformAt k (le_of_lt hk)).branchingN
        ≤ ((coverClass u (𝒢.cover.assign k) P).card : NNReal))
    (hclump : ∀ P ∈ 𝒢.cover.indexSet k, ∃ i₂ : ι,
      coverClass u (𝒢.cover.assign k) P ⊆ fibreIndex u T δ (gridScale δ N k / 4) i₂) :
    ∀ i ∈ u,
      (𝒢.uniformAt k (le_of_lt hk)).branchingN
          ≤ ((fibreIndex u T δ (gridScale δ N k) i).card : NNReal) ∧
        ((fibreIndex u T δ (gridScale δ N k) i).card : NNReal)
          ≤ Cu ^ 2 * (𝒢.uniformAt k (le_of_lt hk)).branchingN := by
  classical
  intro i hi
  have hkN : k ≤ N := le_of_lt hk
  have hpe : (𝒢.uniformAt k hkN).parent = 𝒢.cover.indexSet k := 𝒢.parent_eq k hkN
  have _h8δ := eight_delta_le_gridScale hδ hδ1 hk hδN
  exact card_fibreIndex_band_of_clumped (h := 𝒢.uniformAt k hkN) (assign := 𝒢.cover.assign k)
    (fun j hj => by simpa [hpe] using 𝒢.cover.assign_mem k hkN j hj)
    (fun P hP => hlow P (by simpa [hpe] using hP))
    (fun P hP => hclump P (by simpa [hpe] using hP)) hi

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The comparability constant produced from a uniform structure at constant `Cu`: the bump of
`card_fibreIndex_four_mul_le_of_branching_lower` at the middle grid scales, folded with the
`exists_const_card_fibreIndex_bottom_scale` constant that covers the bottom scale `ρ = δ`. -/
noncomputable def comparableCuOf (Cu : NNReal) : NNReal :=
  max (2 * (100 : NNReal) ^ (2 * Module.finrank ℝ E) * Cu ^ 2)
      (2 * (384 * Module.finrank ℝ E + 1) ^ (2 * Module.finrank ℝ E))

/-- `Cu ^ 2` and the inflation constant `2 · 100^{2n} · Cu²` are both below `comparableCuOf Cu`. -/
theorem le_comparableCuOf {Cu : NNReal} :
    Cu ^ 2 ≤ comparableCuOf (E := E) Cu ∧
      2 * (100 : NNReal) ^ (2 * Module.finrank ℝ E) * Cu ^ 2 ≤ comparableCuOf (E := E) Cu := by
  refine ⟨(le_mul_of_one_le_left zero_le (one_le_two.trans
    (le_mul_of_one_le_right zero_le (one_le_pow₀ (by norm_num))))).trans (le_max_left _ _),
    le_max_left _ _⟩

/-- Helper for `comparableFibreCounts_of_gridUniform`: the comparison at a middle grid scale
`k < N`, where uniformity, the branching lower bound and clumping combine to give both the
exact-scale band and the `4`-inflated bound with constant `comparableCuOf Cu`. -/
private theorem comparable_at_middle_scale {δ : NNReal} {N k : ℕ} {u : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) (hk : k < N) (𝒢 : GridUniform u T N Cu)
    (hlow : ∀ P ∈ 𝒢.cover.indexSet k,
      (𝒢.uniformAt k (le_of_lt hk)).branchingN
        ≤ ((coverClass u (𝒢.cover.assign k) P).card : NNReal))
    (hclump : ∀ P ∈ 𝒢.cover.indexSet k, ∃ i₂ : ι,
      coverClass u (𝒢.cover.assign k) P ⊆ fibreIndex u T δ (gridScale δ N k / 4) i₂)
    (i₀ : ι) (hi₀ : i₀ ∈ u) (i₁ : ι) (hi₁ : i₁ ∈ u) :
    ((fibreIndex u T δ (gridScale δ N k) i₀).card : NNReal)
        ≤ comparableCuOf (E := E) Cu * ((fibreIndex u T δ (gridScale δ N k) i₁).card : NNReal) ∧
      ((fibreIndex u T δ (4 * gridScale δ N k) i₀).card : NNReal)
        ≤ comparableCuOf (E := E) Cu * ((fibreIndex u T δ (gridScale δ N k) i₁).card : NNReal) := by
  classical
  have hband := band_at_middle_scale hδ hδ1 hδN hk 𝒢 hlow hclump
  have h2 : 2 * δ ≤ gridScale δ N k :=
    (mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 8) hδ.le).trans
      (eight_delta_le_gridScale hδ hδ1 hk hδN)
  have hb2R := card_fibreIndex_four_mul_le_of_branching_lower
    (𝒢.uniformAt k (le_of_lt hk)) (gridScale_pos hδ N k) h2 (fun i hi => (hband i hi).1) i₀ hi₁
  exact ⟨((hband i₀ hi₀).2.trans (mul_le_mul_right (hband i₁ hi₁).1 (Cu ^ 2))).trans
      (mul_le_mul_left le_comparableCuOf.1 _),
    (NNReal.coe_le_coe.mp (by push_cast; linarith)).trans
      (mul_le_mul_left le_comparableCuOf.2 _)⟩

/-- Helper for `comparableFibreCounts_of_gridUniform`: the comparison at the bottom grid scale
`k = N`, where `gridScale δ N N = δ` and there is no clumping; both bounds come from essential
distinctness (`exists_const_card_fibreIndex_bottom_scale`). -/
private theorem comparable_at_bottom_scale {δ : NNReal} {N k : ℕ} {u : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (hδ : 0 < δ) (hN : 0 < N) (hk : k = N)
    (hED : (↑u : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    (i₀ : ι) (hi₀ : i₀ ∈ u) (i₁ : ι) (hi₁ : i₁ ∈ u) :
    ((fibreIndex u T δ (gridScale δ N k) i₀).card : NNReal)
        ≤ comparableCuOf (E := E) Cu * ((fibreIndex u T δ (gridScale δ N k) i₁).card : NNReal) ∧
      ((fibreIndex u T δ (4 * gridScale δ N k) i₀).card : NNReal)
        ≤ comparableCuOf (E := E) Cu * ((fibreIndex u T δ (gridScale δ N k) i₁).card : NNReal) := by
  classical
  subst hk
  rw [gridScale_self δ hN]
  have hlow₁ : (1 : NNReal) ≤ ((fibreIndex u T δ δ i₁).card : NNReal) := by
    exact_mod_cast (card_fibreIndex_bottom_scale hδ u T hED i₁ hi₁).2
  have hkey : ((fibreIndex u T δ (4 * δ) i₀).card : NNReal)
      ≤ comparableCuOf (E := E) Cu * ((fibreIndex u T δ δ i₁).card : NNReal) :=
    ((card_fibreIndex_bottom_scale hδ u T hED i₀ hi₀).1.trans (le_max_right _ _)).trans
      (le_mul_of_one_le_right zero_le hlow₁)
  refine ⟨le_trans ?_ hkey, hkey⟩
  exact_mod_cast Finset.card_le_card (fibreIndex_subset_of_anchor_le (s := u) (T := T) (σ := δ)
    (ρ := δ) (ρ' := 4 * δ) (le_mul_of_one_le_left zero_le (by norm_num)) i₀)

/-- **Comparability from the band and the clumping.**  At the middle grid scales
`card_fibreIndex_band_of_clumped` and `card_fibreIndex_four_mul_le_of_branching_lower` do the work;
at the bottom scale `ρ = δ`, where there is no clumping, `exists_const_card_fibreIndex_bottom_scale`
takes over. -/
theorem comparableFibreCounts_of_gridUniform {δ : NNReal} {N : ℕ} {u : Finset ι}
    {T : ι → Tube δ E} {Cu : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) (𝒢 : GridUniform u T N Cu)
    (hlow : ∀ k (hk : k ≤ N), ∀ P ∈ 𝒢.cover.indexSet k,
      (𝒢.uniformAt k hk).branchingN ≤ ((coverClass u (𝒢.cover.assign k) P).card : NNReal))
    (hclump : ∀ k < N, ∀ P ∈ 𝒢.cover.indexSet k, ∃ i₂ : ι,
      coverClass u (𝒢.cover.assign k) P ⊆ fibreIndex u T δ (gridScale δ N k / 4) i₂)
    (hED : (↑u : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)) :
    ComparableFibreCounts u T (gridScales δ N) (comparableCuOf (E := E) Cu) ∧
      ComparableFibreCountsInflated u T (gridScales δ N) (comparableCuOf (E := E) Cu) := by
  classical
  constructor <;> rintro ρ ⟨k, hk, rfl⟩ i₀ hi₀ i₁ hi₁ <;>
    rcases Nat.lt_or_eq_of_le hk with hklt | hkeq
  · exact (comparable_at_middle_scale hδ hδ1 hδN hklt 𝒢 (hlow k hklt.le) (hclump k hklt)
      i₀ hi₀ i₁ hi₁).1
  · exact (comparable_at_bottom_scale hδ hN hkeq hED i₀ hi₀ i₁ hi₁).1
  · exact (comparable_at_middle_scale hδ hδ1 hδN hklt 𝒢 (hlow k hklt.le) (hclump k hklt)
      i₀ hi₀ i₁ hi₁).2
  · exact (comparable_at_bottom_scale hδ hN hkeq hED i₀ hi₀ i₁ hi₁).2

/-- A grid threshold `δ ≤ 16^{-N}` forces `δ ≤ 1`, since `16^{-N} ≤ 1` for every `N`. -/
private theorem hoistedAbsorb_le_one_of_le_16_rpow_neg {N : ℕ} {δ : NNReal}
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) : δ ≤ 1 :=
  hδN.trans (NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (neg_nonpos.mpr (Nat.cast_nonneg N)))

/-- Below `1` the polylogarithmic weight `1 - log δ` is at least `1`. -/
private theorem hoistedAbsorb_one_le_one_sub_log {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := by
  linarith [Real.log_nonpos (by exact_mod_cast hδ.le : (0 : ℝ) ≤ (δ : ℝ))
    (by exact_mod_cast hδ1 : (δ : ℝ) ≤ 1)]

/-- The binary logarithm of `1/δ` is nonnegative and dominated by the weight `1 - log δ` scaled by
`1 / log 2`. -/
private theorem hoistedAbsorb_logb_bounds {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ Real.logb 2 (1 / (δ : ℝ)) ∧
      Real.logb 2 (1 / (δ : ℝ)) ≤ (1 - Real.log (δ : ℝ)) * (1 / Real.log 2) := by
  have hlog_le0 : Real.log (δ : ℝ) ≤ 0 :=
    Real.log_nonpos (by exact_mod_cast hδ.le) (by exact_mod_cast hδ1)
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, one_div (δ : ℝ), Real.log_inv, mul_one_div]
  exact ⟨div_nonneg (by linarith) hlog2pos.le,
    div_le_div_of_nonneg_right (by linarith) hlog2pos.le⟩

/-- The constant that absorbs an affine expression into the weight is at least `1`. -/
private theorem hoistedAbsorb_one_le_absConst (n Cn : ℝ) (hn : 0 ≤ n) :
    (1 : ℝ) ≤ 1 + 2 * n * (1 / Real.log 2) + |Cn| := by
  have h1 : (0 : ℝ) ≤ 1 / Real.log 2 := by positivity
  linarith [abs_nonneg Cn, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn) h1]

/-- An affine expression in a quantity bounded by `W * d` is, in absolute value, at most a constant
multiple of `W`.  The absolute value is what the additive constant `Cn` forces: it may be negative,
so the expression itself carries no usable lower bound. -/
private theorem hoistedAbsorb_abs_affine_le (n d Cn W x : ℝ) (hn : 0 ≤ n)
    (hW : 1 ≤ W) (hx0 : 0 ≤ x) (hxW : x ≤ W * d) :
    |1 + 2 * n * x + Cn| ≤ (1 + 2 * n * d + |Cn|) * W := by
  have h2n : (0 : ℝ) ≤ 2 * n := by linarith
  have hx' : (0 : ℝ) ≤ 2 * n * x := mul_nonneg h2n hx0
  have htri : |1 + 2 * n * x + Cn| ≤ 1 + 2 * n * x + |Cn| :=
    (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + 2 * n * x)])
  linarith [mul_le_mul_of_nonneg_left hxW h2n,
    mul_nonneg (abs_nonneg Cn) (by linarith : (0:ℝ) ≤ W - 1)]

/-- The core numerical step of the hoisted absorption: a geometric factor with exponent `N` times an
`(N+1)`-st power of a quantity whose absolute value is at most `A₀ W` is at most
`(Bc A₀)^{N+1} W^{N+1}`, one factor of the base and one of the weight per level. -/
private theorem hoistedAbsorb_core (Bc A₀ W b : ℝ) (N : ℕ) (hBc : 1 ≤ Bc) (hA₀ : 1 ≤ A₀)
    (hW : 1 ≤ W) (hb : |b| ≤ A₀ * W) :
    Bc ^ N * b ^ (N + 1) ≤ (Bc * A₀) ^ (N + 1) * W ^ (N + 1) := by
  have hb_pow : b ^ (N + 1) ≤ (A₀ * W) ^ (N + 1) :=
    ((le_abs_self _).trans_eq (abs_pow b (N + 1))).trans
      (pow_le_pow_left₀ (abs_nonneg b) hb (N + 1))
  rw [mul_pow, mul_assoc, ← mul_pow]
  exact (mul_le_mul_of_nonneg_left hb_pow (pow_nonneg (by linarith) N)).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hBc (Nat.le_succ N))
      (pow_nonneg (mul_nonneg (by linarith) (by linarith)) _))

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The base carrying the per-level clumping loss is at least `1`. -/
private theorem hoistedAbsorb_one_le_clumpBase :
    (1 : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (16 : ℝ) ^ (2 * Module.finrank ℝ E) :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ (by norm_num)))
    (one_le_pow₀ (by norm_num))

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Absorbing the uniformization losses, with the grid-length dependence displayed.**  The hoisted
form of `exists_absorb_uniformize_losses`: the two absorbing parameters are quantified *before* the
grid length `N`, at the cost of writing the `N`-dependence out.  What is `N`-independent, and what
the statement isolates, is the per-level base `A` and the per-level polylogarithmic exponent `K`. -/
theorem exists_absorb_uniformize_losses_hoisted (Cn : ℝ) :
    ∃ (A : ℝ) (K : ℕ), 1 ≤ A ∧
      ∀ (N : ℕ) (δ : NNReal), 0 < δ → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
        (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (16 : ℝ) ^ (2 * Module.finrank ℝ E)) ^ N
            * (1 + 2 * (Module.finrank ℝ E : ℝ) * Real.logb 2 (1 / (δ : ℝ)) + Cn) ^ (N + 1)
          ≤ A ^ (N + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (N + 1)) := by
  refine ⟨(2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (16 : ℝ) ^ (2 * Module.finrank ℝ E))
      * (1 + 2 * (Module.finrank ℝ E : ℝ) * (1 / Real.log 2) + |Cn|), 1, ?_, ?_⟩
  · exact hoistedAbsorb_one_le_clumpBase.trans (le_mul_of_one_le_right
      (zero_le_one.trans hoistedAbsorb_one_le_clumpBase)
      (hoistedAbsorb_one_le_absConst _ Cn (Nat.cast_nonneg _)))
  · intro N δ hδ hδN
    have hδ1 : δ ≤ 1 := hoistedAbsorb_le_one_of_le_16_rpow_neg hδN
    have hW : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := hoistedAbsorb_one_le_one_sub_log hδ hδ1
    obtain ⟨hx0, hxW⟩ := hoistedAbsorb_logb_bounds hδ hδ1
    simpa only [one_mul] using hoistedAbsorb_core
      (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (16 : ℝ) ^ (2 * Module.finrank ℝ E))
      (1 + 2 * (Module.finrank ℝ E : ℝ) * (1 / Real.log 2) + |Cn|)
      (1 - Real.log (δ : ℝ))
      (1 + 2 * (Module.finrank ℝ E : ℝ) * Real.logb 2 (1 / (δ : ℝ)) + Cn)
      N hoistedAbsorb_one_le_clumpBase
      (hoistedAbsorb_one_le_absConst _ Cn (Nat.cast_nonneg _)) hW
      (hoistedAbsorb_abs_affine_le ((Module.finrank ℝ E : ℝ)) (1 / Real.log 2) Cn
        (1 - Real.log (δ : ℝ)) (Real.logb 2 (1 / (δ : ℝ))) (Nat.cast_nonneg _) hW hx0 hxW)

/-- A grid threshold `δ ≤ 16^{-N}` with `0 < N` forces `δ < 1` strictly. -/
private theorem lt_one_of_le_16_rpow_neg {N : ℕ} {δ : NNReal} (hN : 0 < N)
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) : δ < 1 := -- (extracted by Fuse golfer)
  hδN.trans_lt (NNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (neg_lt_zero.mpr (by exact_mod_cast hN)))

/-- The grid-uniform system carried by the empty family, with the node tubes prescribed.  Every
field is vacuous, so the nodes may be chosen freely; this is what dispatches the degenerate case of
the two hoisted subfamily lemmas, where the ambient family — hence the subfamily — is empty. -/
private noncomputable def gridUniformEmpty {δ : NNReal} {ι : Type*} (T : ι → Tube δ E) (N : ℕ)
    (Cu : NNReal)
    (tube : ∀ k : ℕ, ι → Tube (gridScale δ N k) E) :
    GridUniform (∅ : Finset ι) T N Cu where -- (extracted by Fuse golfer)
  cover :=
    { indexSet := fun _ => ∅
      assign := fun _ i => i
      tube := tube
      assign_mem := fun _ _ i hi => absurd hi (Finset.notMem_empty i)
      le_tube_assign := fun _ _ i hi => absurd hi (Finset.notMem_empty i)
      nested := fun _ _ i hi => absurd hi (Finset.notMem_empty i)
      tube_nested := fun _ _ i hi => absurd hi (Finset.notMem_empty i) }
  uniformAt := fun k _ => isUniformAtScaleEmpty T fun i => (T i).rescale (gridScale δ N k)
  parent_eq := fun _ _ => rfl
  tube_eq := fun _ _ P hP => absurd hP (Finset.notMem_empty P)
  le_card_class := fun _ _ P hP => absurd hP (Finset.notMem_empty P)
  clumped := fun _ _ P hP => absurd hP (Finset.notMem_empty P)
  nice := fun _ _ => ⟨fun a ha _ _ _ => absurd ha (Finset.notMem_empty a), fun _ => by
    simp only [Finset.filter_empty, Finset.card_empty, Nat.zero_le]⟩

/-- **The clump-then-uniformize pass along the grid, relative to a prescribed nice system.**  Clump
along the grid with `exists_clumped_subset_along_grid`, uniformize with
`exists_uniformize_along_grid_hoisted` relative to the *same* system, then read off comparability.
The output system refines the input one, and the constants are quantified before the length `N`. -/
private theorem exists_gridUniform_subfamily_of_nice : -- (extracted by Fuse golfer)
    ∃ (A : ℝ) (K : ℕ) (Cu : NNReal), 1 ≤ A ∧ 1 ≤ Cu ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s t : Finset ι) (T : ι → Tube δ E), t ⊆ s →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ 𝒞 : GridCoverSystem t T N,
        (∀ k ≤ N,
          Set.InjOn (𝒞.tube k) (𝒞.indexSet k : Set ι) ∧
          ∀ V : Tube (gridScale δ N k) E,
            ((𝒞.indexSet k).filter (fun v => ∃ i ∈ t,
              (T i).toConvexSpaceBody ≤ (𝒞.tube k v).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
                Tube.overlapConstBOTight (Module.finrank ℝ E)) →
      ∃ t' ⊆ t,
        (t.card : ℝ) ≤ A ^ (N + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (N + 1)) * (t'.card : ℝ) ∧
          ∃ 𝒢' : GridUniform t' T N Cu,
            (∀ k (hk : k ≤ N), (𝒢'.uniformAt k hk).parent ⊆ 𝒞.indexSet k) ∧
            (∀ k, 𝒢'.cover.tube k = 𝒞.tube k) ∧
            ComparableFibreCounts t' T (gridScales δ N) Cu ∧
            ComparableFibreCountsInflated t' T (gridScales δ N) Cu := by
  classical
  obtain ⟨Cn, Cu₀, hCu₀, hmain⟩ := exists_uniformize_along_grid_hoisted (E := E)
  obtain ⟨M, K, hM, habs⟩ := exists_absorb_uniformize_losses_hoisted (E := E) Cn
  have hCu0_le_Cu : Cu₀ ≤ comparableCuOf (E := E) Cu₀ :=
    (le_self_pow hCu₀ two_ne_zero).trans le_comparableCuOf.1
  refine ⟨M, K, comparableCuOf (E := E) Cu₀, hM, hCu₀.trans hCu0_le_Cu, ?_⟩
  intro N hN ι δ hδ hδN s t T hts hs_B1 hs_ED 𝒞 hnice
  by_cases hs_empty : s = ∅
  · have ht_empty : t = ∅ := Finset.subset_empty.mp (hs_empty ▸ hts)
    exact ⟨∅, Finset.empty_subset t,
      by simp only [ht_empty, Finset.card_empty, Nat.cast_zero, mul_zero, le_refl],
      gridUniformEmpty T N _ 𝒞.tube, fun _ _ => Finset.empty_subset _, fun _ => rfl,
      fun _ _ i₀ hi₀ => absurd hi₀ (Finset.notMem_empty i₀),
      fun _ _ i₀ hi₀ => absurd hi₀ (Finset.notMem_empty i₀)⟩
  · have hδ1lt : δ < 1 := lt_one_of_le_16_rpow_neg hN hδN
    have hs_ne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
    obtain ⟨t₁, ht₁t, hcard_clump, hclump3⟩ :=
      exists_clumped_subset_along_grid hδ hδ1lt.le hδN hts T 𝒞 hs_ne
    obtain ⟨𝒞'', hpar₂, hassign₂, htube₂⟩ := exists_restrict_gridCoverSystem ht₁t 𝒞
    obtain ⟨u, hut₁, hu_card, hu_band⟩ := hmain N hδ hδ1lt s t₁ T (ht₁t.trans hts) hs_B1 hs_ED
      𝒞'' (gridCoverSystem_nice_restrict_of_nice 𝒞 hnice ht₁t 𝒞'' hpar₂ htube₂)
    choose huniform hcl₁ hcl₂ hcl₃ hcl₄ using hu_band
    have hu_t : u ⊆ t := hut₁.trans ht₁t
    obtain ⟨𝒞₃, hpar₃eq, hassign₃eq, htube₃eq⟩ := exists_restrict_gridCoverSystem hut₁ 𝒞''
    have htube₃' : 𝒞₃.tube = 𝒞.tube := htube₃eq.trans htube₂
    have hnice₃ := gridCoverSystem_nice_restrict_of_nice 𝒞 hnice hu_t 𝒞₃
      (hpar₃eq.trans hpar₂) htube₃'
    have hclump₃ : ∀ k (hk₀ : k < N), ∀ P ∈ (huniform k (le_of_lt hk₀)).parent, ∃ i₂ : ι,
        coverClass u (𝒞₃.assign k) P ⊆ fibreIndex u T δ (gridScale δ N k / 4) i₂ := by
      intro k hk₀ P hP
      have hP'' : P ∈ 𝒞.indexSet k := by rw [← hpar₂]; exact hcl₁ k hk₀.le hP
      obtain ⟨i₂, hi₂s, hsub⟩ := (hclump3 k hk₀ P hP'').1
      obtain ⟨j₂, hsub₂⟩ := clump_restrict_to_subset hut₁ (𝒞.assign k)
        ⟨i₂, subset_fibreIndex_restrict (fun j hj => (Finset.mem_filter.mp hj).1) hsub⟩
      exact ⟨j₂, by rw [hassign₃eq, hassign₂]; exact hsub₂⟩
    obtain ⟨𝒢₀, hGu, hGa, hGP, hGT⟩ := exists_gridUniform_pack 𝒞₃ hnice₃ huniform
      (fun k hk => by rw [hpar₃eq]; exact hcl₁ k hk)
      (fun k hk i hi => by rw [hassign₃eq]; exact hcl₂ k hk i hi)
      (fun k hk P hP => by rw [htube₃eq]; exact hcl₃ k hk P hP)
      (fun k hk P hP => by rw [hassign₃eq]; exact (hcl₄ k hk P hP).1) hclump₃
    have hlow : ∀ k (hk : k ≤ N), ∀ P ∈ 𝒢₀.cover.indexSet k,
        (𝒢₀.uniformAt k hk).branchingN ≤ ((coverClass u (𝒢₀.cover.assign k) P).card : NNReal) :=
      fun k hk P hP => by
        rw [hGu k hk, hGa k hk, hassign₃eq]; exact (hcl₄ k hk P (hGP k hk ▸ hP)).1
    have hclump : ∀ k (hk₀ : k < N), ∀ P ∈ 𝒢₀.cover.indexSet k, ∃ i₂ : ι,
        coverClass u (𝒢₀.cover.assign k) P ⊆ fibreIndex u T δ (gridScale δ N k / 4) i₂ :=
      fun k hk₀ P hP => by
        rw [hGa k hk₀.le]; exact hclump₃ k hk₀ P (hGP k hk₀.le ▸ hP)
    have hcomp := comparableFibreCounts_of_gridUniform hδ hδ1lt.le hN hδN 𝒢₀ hlow hclump
      (hs_ED.mono (Finset.coe_subset.mpr (hu_t.trans hts)))
    let 𝒢' : GridUniform u T N (comparableCuOf (E := E) Cu₀) := GridUniform.mono 𝒢₀ hCu0_le_Cu
    have hcard : (t.card : ℝ) ≤
        M ^ (N + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (N + 1)) * (u.card : ℝ) :=
      hcard_clump.trans
        (((mul_le_mul_of_nonneg_left hu_card (by positivity)).trans_eq
          (mul_assoc _ _ _).symm).trans
          (mul_le_mul_of_nonneg_right (habs N δ hδ hδN) (Nat.cast_nonneg _)))
    exact ⟨u, hu_t, hcard, 𝒢', fun k hk =>
      calc (𝒢'.uniformAt k hk).parent = (huniform k hk).parent :=
          congrArg (fun h => h.parent) (hGu k hk)
        _ ⊆ 𝒞''.indexSet k := hcl₁ k hk
        _ = 𝒞.indexSet k := congrFun hpar₂ k,
      fun k => (hGT k).trans (congrFun htube₃' k), hcomp.1, hcomp.2⟩

/-- **Re-uniformizing a subfamily along the grid** (blueprint `lem:uniformize_subfamily`), hoisted
form.  Clump along a prescribed nested cover system for `t`, then uniformize relative to that same
system; comparability follows scale by scale, the bottom scale `ρ_N = δ` coming from essential
distinctness.  The output system is a sub-system of the prescribed one, and the constants `A`, `K`,
`Cu` are quantified before the grid length `N`. -/
theorem exists_uniformize_subfamily_hoisted :
    ∃ (A : ℝ) (K : ℕ) (Cu : NNReal), 1 ≤ A ∧ 1 ≤ Cu ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s t : Finset ι) (T : ι → Tube δ E), t ⊆ s →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ (Cs : NNReal) (𝒢 : GridUniform s T N Cs),
      ∃ t' ⊆ t,
        (t.card : ℝ) ≤ A ^ (N + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (N + 1)) * (t'.card : ℝ) ∧
          ∃ 𝒢' : GridUniform t' T N Cu,
            (∀ k (hk : k ≤ N), (𝒢'.uniformAt k hk).parent ⊆ (𝒢.uniformAt k hk).parent) ∧
            (∀ k, 𝒢'.cover.tube k = 𝒢.cover.tube k) ∧
            ComparableFibreCounts t' T (gridScales δ N) Cu ∧
            ComparableFibreCountsInflated t' T (gridScales δ N) Cu := by
  classical
  obtain ⟨A, K, Cu, hA, hCu, hmain⟩ := exists_gridUniform_subfamily_of_nice (E := E)
  refine ⟨A, K, Cu, hA, hCu, ?_⟩
  intro N hN ι δ hδ hδN s t T hts hs_B1 hs_ED Cs 𝒢
  obtain ⟨𝒞, hpar, hassign, htube⟩ := exists_restrict_gridCoverSystem hts 𝒢.cover
  obtain ⟨t', ht't, hcard, 𝒢', hparent, htube', hcomp, hcompInf⟩ :=
    hmain N hN hδ hδN s t T hts hs_B1 hs_ED 𝒞
      (gridCoverSystem_nice_restrict 𝒢 hts 𝒞 hpar htube)
  refine ⟨t', ht't, hcard, 𝒢', fun k hk => ?_,
    fun k => (htube' k).trans (congrFun htube k), hcomp, hcompInf⟩
  rw [𝒢.parent_eq k hk, ← congrFun hpar k]
  exact hparent k hk

/-- **Consecutive grid scales are `2`-separated, over `ℝ`.**  The real-valued weakening of
`sixteen_mul_gridScale_succ_le` that the net-covering hypothesis of the downward recursion asks
for, shared by `gridCoverNodes` and `exists_initial_gridCoverSystem`. -/
private theorem two_mul_gridScale_succ_le {δ : NNReal} (hδ : 0 < δ) {N : ℕ}
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {k : ℕ} (hk : k < N) :
    2 * ((gridScale δ N (k + 1) : NNReal) : ℝ) ≤ (gridScale δ N k : ℝ) := by
  -- (extracted by Fuse golfer)
  have h : (16 : ℝ) * (gridScale δ N (k + 1) : ℝ) ≤ (gridScale δ N k : ℝ) :=
    mod_cast sixteen_mul_gridScale_succ_le hδ hδN hk
  linarith [(gridScale δ N (k + 1)).coe_nonneg]

/-- The node at one scale of the downward recursion: a `gridScale δ N k`-tube whose midpoint lies
in `B₃`, which is a net tube of `Gk k` when `k < N`, and which contains `T i`. -/
private structure GridCoverNode {δ : NNReal} {N k : ℕ} {ι : Type*}
    (t : Finset ι) (T : ι → Tube δ E) (i : ι)
    (Gk : (k : ℕ) → Finset (Tube (gridScale δ N k) E)) where
  tube : Tube (gridScale δ N k) E
  mem_ball : tube.midpoint ∈ Metric.closedBall (0 : E) 3
  mem_net : (k < N) → tube ∈ Gk k
  contains : i ∈ t → (T i).toConvexSpaceBody ≤ tube.toConvexSpaceBody

/-- The downward-recursive node assignment.  At each scale `k ≤ N` the node `f k i` is a
`gridScale δ N k`-tube; at `k = N` it is (the carrier-representative of) the leaf `T i`, and at
`k < N` it is a net tube of `Gk k` containing `f (k + 1) i`. -/
private noncomputable def gridCoverNodes {δ : NNReal} {N : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N) (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ)))
    {ι : Type*} (t : Finset ι) (T : ι → Tube δ E)
    (hmid : ∀ (i : ι), i ∈ t → (T i).midpoint ∈ Metric.closedBall (0 : E) 3)
    (i₀ : ι) (hi₀ : i₀ ∈ t)
    (Gk : (k : ℕ) → Finset (Tube (gridScale δ N k) E))
    (hGmid : (k : ℕ) → (hk : k ≤ N) → ∀ W ∈ Gk k, W.midpoint ∈ Metric.closedBall (0 : E) 3)
    (hGcover : (k : ℕ) → (hk : k < N) → ∀ {σ : NNReal} (U : Tube σ E),
      2 * (σ : ℝ) ≤ (gridScale δ N k : ℝ) →
      U.midpoint ∈ Metric.closedBall (0 : E) 3 →
      ∃ W ∈ Gk k, U.toConvexSpaceBody ≤ W.toConvexSpaceBody) :
    (k : ℕ) → (hk : k ≤ N) → (i : ι) → GridCoverNode (k := k) (Gk := Gk) t T i
  | k, hk, i => by
      by_cases hk_eq : k = N
      · subst k
        by_cases hi : i ∈ t
        · exact ⟨(T i).rescale _, hmid i hi, fun hlt => absurd hlt (lt_irrefl N),
            fun _ => by rw [gridScale_self δ hN, Tube.toConvexSpaceBody_rescale_self]⟩
        · exact ⟨(T i₀).rescale _, hmid i₀ hi₀, fun hlt => absurd hlt (lt_irrefl N),
            fun h => absurd h hi⟩
      · have hkN : k < N := by omega
        let fine := gridCoverNodes hδ hδ1 hN hδN t T hmid i₀ hi₀ Gk hGmid hGcover (k+1)
          (Nat.succ_le_of_lt hkN) i
        have hspec := (hGcover k hkN fine.tube (two_mul_gridScale_succ_le hδ hδN hkN)
          fine.mem_ball).choose_spec
        exact ⟨_, hGmid k hk _ hspec.1, fun _ => hspec.1,
          fun hi => (fine.contains hi).trans hspec.2⟩
  termination_by k => N - k
  decreasing_by omega

/-- **The initial nested cover system** (blueprint `lem:initial_gridCoverSystem`).  The one system
built directly: the nodes at each grid scale are drawn from `Tube.grid_net_tight`, and the
assignment is a single downward recursion, a member being assigned at each coarser scale to the net
tube containing the *node* it received one scale finer.  The conclusion includes the tight-net
clause, which is the `nice` field of `GridUniform`. -/
theorem exists_initial_gridCoverSystem {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    (hN : 0 < N) (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) (t : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hT_inj : Set.InjOn (fun i => (T i).carrier) (t : Set ι)) :
    ∃ 𝒞 : GridCoverSystem t T N,
      ∀ k ≤ N,
        Set.InjOn (𝒞.tube k) (𝒞.indexSet k : Set ι) ∧
        ∀ V : Tube (gridScale δ N k) E,
          ((𝒞.indexSet k).filter (fun v => ∃ i ∈ t,
            (T i).toConvexSpaceBody ≤ (𝒞.tube k v).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
              Tube.overlapConstBOTight (Module.finrank ℝ E) := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · exact
      ⟨{ indexSet := fun _ => (∅ : Finset ι),
         assign := fun _ => id,
         tube := fun k v => (T v).rescale (gridScale δ N k),
         assign_mem := fun _ _ i hi => absurd hi (Finset.notMem_empty i),
         le_tube_assign := fun _ _ i hi => absurd hi (Finset.notMem_empty i),
         nested := fun _ _ i hi => absurd hi (Finset.notMem_empty i),
         tube_nested := fun _ _ i hi => absurd hi (Finset.notMem_empty i) }, by simp⟩
  · choose Gk hGnet using fun k : ℕ =>
      Tube.grid_net_tight (E := E) (gridScale_pos hδ N k) (gridScale_le_one hδ1 N k)
    have hGcover : (k : ℕ) → (hk : k < N) → ∀ {σ : NNReal} (U : Tube σ E),
        2 * (σ : ℝ) ≤ (gridScale δ N k : ℝ) →
        U.midpoint ∈ Metric.closedBall (0 : E) 3 →
        ∃ W ∈ Gk k, U.toConvexSpaceBody ≤ W.toConvexSpaceBody := by
      intro k _ σ U h2σ hUmid
      exact ((hGnet k).1 U h2σ hUmid).imp fun _ h => ⟨h.1, h.2.1⟩
    have hGmid : (k : ℕ) → (hk : k ≤ N) → ∀ W ∈ Gk k,
        W.midpoint ∈ Metric.closedBall (0 : E) 3 := fun k _ => (hGnet k).2.2.2
    have hmid : ∀ i ∈ t, (T i).midpoint ∈ Metric.closedBall (0 : E) 3 := fun i hi =>
      Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3)
        (Tube.midpoint_mem_closedBall_of_subset hδ (T i) (hball i hi))
    have hsep2 : ∀ k, k < N →
        2 * ((gridScale δ N (k + 1) : NNReal) : ℝ) ≤ (gridScale δ N k : ℝ) :=
      fun _ hk => two_mul_gridScale_succ_le hδ hδN hk
    let G := gridCoverNodes hδ hδ1 hN hδN t T hmid i₀ hi₀ Gk hGmid hGcover
    let W : (k : ℕ) → ι → Tube (gridScale δ N k) E :=
      fun k v => if hk : k ≤ N then (G k hk v).tube else (T v).rescale (gridScale δ N k)
    let rep : (k : ℕ) → Tube (gridScale δ N k) E → ι := fun k U =>
      if h : ∃ j ∈ t, W k j = U then h.choose else i₀
    have hrep_spec : ∀ k, ∀ i ∈ t, rep k (W k i) ∈ t ∧ W k (rep k (W k i)) = W k i := by
      intro k i hi
      have hprop : ∃ j ∈ t, W k j = W k i := ⟨i, hi, rfl⟩
      simp only [rep, hprop, ↓reduceDIte]
      exact Classical.choose_spec hprop
    have hrep_idem : ∀ k, ∀ i ∈ t, W k (rep k (W k i)) = W k i :=
      fun k i hi => (hrep_spec k i hi).2
    have hW_eq : ∀ k (hk : k ≤ N) (i : ι), W k i = (G k hk i).tube := fun k hk i => dif_pos hk
    have hW_contains : ∀ k (hk : k ≤ N), ∀ i ∈ t,
        (T i).toConvexSpaceBody ≤ (W k i).toConvexSpaceBody :=
      fun k hk i hi => (hW_eq k hk i) ▸ (G k hk i).contains hi
    have hW_step : ∀ k (hk : k < N) (i : ι),
        W k i = (hGcover k hk (G (k + 1) hk i).tube (hsep2 k hk)
          (G (k + 1) hk i).mem_ball).choose := by
      intro k hk i
      simp only [W, dif_pos hk.le, G]
      conv_lhs => rw [gridCoverNodes, dif_neg hk.ne]
    have hW_le_step : ∀ k (hk : k < N) (i : ι),
        (W (k + 1) i).toConvexSpaceBody ≤ (W k i).toConvexSpaceBody := by
      intro k hk i
      rw [hW_step k hk i, hW_eq (k + 1) hk i]
      exact (hGcover k hk (G (k + 1) hk i).tube (hsep2 k hk)
        (G (k + 1) hk i).mem_ball).choose_spec.2
    have choose_congr : ∀ (k : ℕ) (hk : k < N) (U U' : Tube (gridScale δ N (k + 1)) E),
        U = U' → ∀ (h1 : 2 * ((gridScale δ N (k + 1) : NNReal) : ℝ) ≤ (gridScale δ N k : ℝ))
          (h2 : U.midpoint ∈ Metric.closedBall (0 : E) 3)
          (h2' : U'.midpoint ∈ Metric.closedBall (0 : E) 3),
        (hGcover k hk U h1 h2).choose = (hGcover k hk U' h1 h2').choose := by
      rintro k hk U _ rfl _ _ _; rfl
    have step_congr : ∀ k, k < N → ∀ i j : ι, W (k + 1) i = W (k + 1) j → W k i = W k j := by
      intro k hk i j hWstep
      rw [hW_eq (k + 1) hk i, hW_eq (k + 1) hk j] at hWstep
      rw [hW_step k hk i, hW_step k hk j]
      exact choose_congr k hk _ _ hWstep (hsep2 k hk) (G (k + 1) hk i).mem_ball
        (G (k + 1) hk j).mem_ball
    let 𝒞 : GridCoverSystem t T N :=
      { indexSet := fun k => t.image (fun i => rep k (W k i))
        assign := fun k i => rep k (W k i)
        tube := W
        assign_mem := fun _ _ i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
        le_tube_assign := fun k hk i hi => by
          rw [hrep_idem k i hi]; exact hW_contains k hk i hi
        nested := fun k hk i hi j hj hassign =>
          congrArg (rep k) (step_congr k hk i j
            ((hrep_idem (k + 1) i hi).symm.trans
              ((congrArg (W (k + 1)) hassign).trans (hrep_idem (k + 1) j hj))))
        tube_nested := fun k hk i hi => by
          rw [hrep_idem (k + 1) i hi, hrep_idem k i hi]; exact hW_le_step k hk i }
    have hW_mem_net : ∀ k (hklt : k < N) (m : ι), m ∈ t.image (fun i => rep k (W k i)) →
        W k m ∈ Gk k := by
      intro k hklt m hm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      rw [hrep_idem k i hi, hW_eq k hklt.le i]
      exact (G k hklt.le i).mem_net hklt
    have hrep_base : ∀ k, ∀ v ∈ t.image (fun i => rep k (W k i)), v = rep k (W k v) := by
      intro k v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      rw [hrep_idem k i hi]
    have hNice_inj : ∀ k, Set.InjOn (𝒞.tube k) (𝒞.indexSet k : Set ι) :=
      fun k v hv v' hv' htube =>
        (hrep_base k v hv).trans ((congrArg (rep k) htube).trans (hrep_base k v' hv').symm)
    refine ⟨𝒞, fun k hk => ⟨hNice_inj k, ?_⟩⟩
    · by_cases hkeq : k = N
      · subst k
        have hδρ : δ = gridScale δ N N := (gridScale_self δ hN).symm
        intro V
        refine le_trans (Finset.card_le_one.mpr ?_)
          (Nat.mul_pos Nat.zero_lt_two (Nat.pow_pos (Nat.succ_pos _)))
        have hmemt : ∀ v ∈ 𝒞.indexSet N, v ∈ t := fun v hv => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv; exact (hrep_spec N i hi).1
        have hcarV : ∀ v ∈ 𝒞.indexSet N, ∀ U : ι,
            (T U).toConvexSpaceBody ≤ (𝒞.tube N v).toConvexSpaceBody →
            (T U).toConvexSpaceBody ≤ V.toConvexSpaceBody → (T v).carrier = V.carrier := by
          intro v hv U hUv hUV
          calc (T v).carrier = (𝒞.tube N v).carrier :=
                Tube.carrier_eq_of_subset' hδρ (T v) (W N v)
                  (SetLike.coe_subset_coe.mpr (hW_contains N le_rfl v (hmemt v hv)))
            _ = (T U).carrier := (Tube.carrier_eq_of_subset' hδρ (T U) (𝒞.tube N v)
                (SetLike.coe_subset_coe.mpr hUv)).symm
            _ = V.carrier :=
                Tube.carrier_eq_of_subset' hδρ (T U) V (SetLike.coe_subset_coe.mpr hUV)
        intro a ha b hb
        obtain ⟨haP, U, hUt, hUa, hUV⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbP, U', hU't, hU'b, hU'V⟩ := Finset.mem_filter.mp hb
        exact hT_inj (hmemt a haP) (hmemt b hbP)
          ((hcarV a haP U hUa hUV).trans (hcarV b hbP U' hU'b hU'V).symm)
      · have hklt : k < N := Nat.lt_of_le_of_ne hk hkeq
        intro V
        refine (Finset.card_le_card_of_injOn (W k) (fun v hv => ?_)
            ((hNice_inj k).mono fun x hx => (Finset.mem_filter.mp hx).1)).trans
          (Tube.grid_overlap_tight (δ := δ) (gridScale_pos hδ N k) (Gk k) (hGnet k).2.1 V)
        obtain ⟨hvP, i, hit, hiv, hiV⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hW_mem_net k hklt v hvP, T i, hball i hit, hiv, hiV⟩

/-- **The initial grid-uniform system** (blueprint `lem:uniformize_subfamily_initial`), hoisted
form.  `exists_uniformize_subfamily` with no prescribed system: the cover system is built here by
the same nested pass instead of being inherited, and correspondingly there is no parent-containment
clause.  The constants `A`, `K` and `Cu` are quantified before the grid length `N`. -/
theorem exists_gridUniform_subfamily_hoisted :
    ∃ (A : ℝ) (K : ℕ) (Cu : NNReal), 1 ≤ A ∧ 1 ≤ Cu ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s t : Finset ι) (T : ι → Tube δ E), t ⊆ s →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∃ t' ⊆ t,
        (t.card : ℝ) ≤ A ^ (N + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (N + 1)) * (t'.card : ℝ) ∧
          Nonempty (GridUniform t' T N Cu) ∧
          ComparableFibreCounts t' T (gridScales δ N) Cu ∧
          ComparableFibreCountsInflated t' T (gridScales δ N) Cu := by
  classical
  obtain ⟨A, K, Cu, hA, hCu, hmain⟩ := exists_gridUniform_subfamily_of_nice (E := E)
  refine ⟨A, K, Cu, hA, hCu, ?_⟩
  intro N hN ι δ hδ hδN s t T hts hs_B1 hs_ED
  have hT_inj : Set.InjOn (fun i => (T i).carrier) (t : Set ι) := by
    intro i hi j hj h_eq
    by_contra hne
    have hEDij : IsEssentiallyDistinct (T i).carrier (T j).carrier :=
      hs_ED (hts hi) (hts hj) hne
    rw [show (T i).carrier = (T j).carrier from h_eq] at hEDij
    have hvol_pos : volume (T j).carrier ≠ 0 := by
      have h1 : (0 : NNReal) <
          Tube.le_volume.c (Module.finrank ℝ E) * δ ^ (Module.finrank ℝ E - 1) :=
        mul_pos (Tube.le_volume.c_pos _) (pow_pos hδ _)
      exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast h1) (Tube.le_volume (T j)))
    exact absurd hEDij
      (not_isEssentiallyDistinct_self hvol_pos (T j).isCompact.measure_lt_top.ne)
  obtain ⟨𝒞, hnice⟩ := exists_initial_gridCoverSystem hδ
    (lt_one_of_le_16_rpow_neg hN hδN).le hN hδN t T (fun i hi => hs_B1 i (hts hi)) hT_inj
  obtain ⟨t', ht't, hcard, 𝒢', -, -, hcomp, hcompInf⟩ :=
    hmain N hN hδ hδN s t T hts hs_B1 hs_ED 𝒞 hnice
  exact ⟨t', ht't, hcard, ⟨𝒢'⟩, hcomp, hcompInf⟩

end MultiScaleFac

end Kakeya
