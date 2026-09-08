/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountFloor
public import Kakeya.Tube.Rigidity
public import Kakeya.FrostmanTransfer
public import Kakeya.ShadedUniform
public import Kakeya.DimensionThree.MainLemma2.GridRounding
public import Kakeya.StickyKakeya.CrossScale

/-!
# GC-2: the refined count floor is FALSE on the tree's window package

 isolates alternative (F) of the refined source's
`lem:ml2-window-refinement` (l.4086–4104; `eq:ml2-count-floor`, l.4476–4482) as the hypothesis
`hfloor` of `Kakeya.ML2Core.geometricCoreAt_of_floor_middleFactor`: on the window package of the
wiring (`Kakeya.ML2Reduction.IsKatzTaoDividingWindow`, spine-pinned) there is a genuine parent
level `p` below the window with, per cell, `#𝕊_{m'}⟨T_p⟩ ≥ (ρ_p/ρ_{m'})^{2+4ζ}` at every window
level `m'`.  This file proves that **no producer of `hfloor` can exist**: the hypothesis is
refuted (`Kakeya.ML2Core.not_countFloor_hypothesis`).

## The obstruction

The tree's window reads its intermediate-scale lower bound
(`IsKatzTaoDividingWindow.le_window_maxDensity`, produced verbatim by the existing GWZ 7.7(B)
`Kakeya.MultiScaleFac.dividingScalesKatzTao`) on the **fine nodes rescaled to `ρ`, indexed by the
fine nodes** — that is, with multiplicity.  The refined source's window inequality
`Δ_max(𝕊'_m⟨S⟩) > ½(ρ_a/ρ_m)^{η_{J+1}}` (l.4056–4058) is on the **distinct** level-`m` cells.  A
*sticky* configuration — all fine nodes under a coarse node inside one `ρ`-tube for every window
radius `ρ` — satisfies the tree's clause by multiplicity alone while having a bounded number of
distinct nodes at every window level; the floor `(ρ_p/ρ_{m'})^{2+4ζ} → ∞` then fails for every
admissible `p`.

The configuration is : `K² ≈ δ^{-2e}/64` parallel unit `δ`-tubes on a `3δ`-grid
transverse to a common axis, inside the central `δ^{1-e}`-tube (`gridShaded`); the hierarchy is
the tree's own uniformiser (`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`); the window
is `a = 0`, `b = ssfGridLen δ`, `m = 0`, `C⋆ = ssfUniformConst 3` (`gridModel_window`).  Every
binder of `hfloor` holds and its conclusion fails (`not_countFloor_hypothesis`), at every small
`δ`.

## Contents

* counting in an abstract hierarchy: `card_indexSet_le_of_le_tube`, `card_coverClass_bot_le_one`,
  `card_le_mul_card_coverClass`, `card_coverClass_le_card_nodesUnder_bot`,
  `maxDensity_le_one_of_pairwiseDisjoint`;
* the grid family and its geometry: `gridE`, `gridW`, `gridTube`, `gridLeaf`, `gridShaded`,
  `gridIndex`, `disjoint_gridLeaf`, `gridLeaf_le_rescale`, `gridLeaf_rescale_le`,
  `gridLeaf_carrier_subset_ball`;
* the model: `gridModel_card_indexSet_le`, `le_mul_maxDensity_of_bounds`,
  `window_lower_bound_real`, `gridModel_window`;
* the obstruction: `not_countFloor_hypothesis`.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-! ## Counting in an abstract hierarchy -/

section Counting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A level all of whose nodes meet one common tube has at most `C` nodes.**  Every node has a
class member (`coverClass_nonempty_of_mem_parent`), which lies in the node and in `V`, so every
node is counted by `boundedOverlap` at `V`. -/
theorem card_indexSet_le_of_le_tube {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N) (hs : s.Nonempty)
    (V : Tube (Tube.gridScale δ N k) E)
    (hV : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    ((𝒰.cover.indexSet k).card : NNReal) ≤ C := by
  classical
  have hsub : 𝒰.cover.indexSet k ⊆ (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
    intro j hj
    obtain ⟨i, hi⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hk hs hj
    simp only [Tube.coverClass, Finset.mem_filter] at hi
    refine Finset.mem_filter.mpr ⟨hj, i, hi.1, ?_, hV i hi.1⟩
    have := 𝒰.cover.le_tube_assign k hk i hi.1
    rwa [hi.2] at this
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (𝒰.boundedOverlap k hk V)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- `Tube.carrier_eq_of_subset` across a propositional equality of radii. -/
theorem carrier_eq_of_subset_of_radius_eq {ρ : NNReal} (hρ : ρ = δ) (A : Tube δ E) (B : Tube ρ E)
    (h : A.carrier ⊆ B.carrier) : A.carrier = B.carrier := by
  subst hρ
  exact Tube.carrier_eq_of_subset A B h

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- `Tube.rescale_body_eq_of_carrier_eq` across a propositional equality of radii. -/
theorem rescale_body_eq_of_carrier_eq_of_radius_eq {ρ' ρ : NNReal} (hρ' : ρ' = δ) (A : Tube δ E)
    (B : Tube ρ' E) (h : A.carrier = B.carrier) (hδρ : δ ≤ ρ) :
    (A.rescale ρ).toConvexSpaceBody = (B.rescale ρ).toConvexSpaceBody := by
  subst hρ'
  exact Tube.rescale_body_eq_of_carrier_eq h hδρ

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The bottom-level nodes of a hierarchy on pairwise disjoint leaves are singletons**: two
leaves of one bottom class lie inside the same `δ`-tube, so (`Tube.carrier_eq_of_subset`) both
carriers equal the node's carrier, and disjoint nonempty sets cannot coincide. -/
theorem card_coverClass_bot_le_one {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) (hN : 0 < N)
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => (T i).carrier)) (j : ι) :
    (Tube.coverClass s (𝒰.cover.assign N) j).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi i' hi'
  simp only [Tube.coverClass, Finset.mem_filter] at hi hi'
  by_contra hne
  have h1 : (T i).carrier ⊆ (𝒰.cover.tube N j).carrier := by
    have := 𝒰.cover.le_tube_assign N le_rfl i hi.1
    rw [hi.2] at this
    exact this
  have h2 : (T i').carrier ⊆ (𝒰.cover.tube N j).carrier := by
    have := 𝒰.cover.le_tube_assign N le_rfl i' hi'.1
    rw [hi'.2] at this
    exact this
  have e1 := carrier_eq_of_subset_of_radius_eq (Tube.gridScale_self δ hN) (T i) _ h1
  have e2 := carrier_eq_of_subset_of_radius_eq (Tube.gridScale_self δ hN) (T i') _ h2
  have hd : Disjoint (T i).carrier (T i').carrier := hdisj hi.1 hi'.1 hne
  rw [e1, ← e2, disjoint_self, Set.bot_eq_empty] at hd
  exact (T i').toConvexSpaceBody.nonempty.ne_empty hd

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Every class of a level with at most `C` nodes carries at least a `C⁻³` share of the family**:
the classes of the level partition `s`, each is at most `C · N_k`, and `N_k ≤ C · #class`. -/
theorem card_le_mul_card_coverClass {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N)
    (hidx : ((𝒰.cover.indexSet k).card : NNReal) ≤ C) {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    (s.card : NNReal) ≤ C ^ 3 * ((Tube.coverClass s (𝒰.cover.assign k) j).card : NNReal) := by
  classical
  have hpart : s.card
      = ∑ j' ∈ 𝒰.cover.indexSet k, (Tube.coverClass s (𝒰.cover.assign k) j').card := by
    simp only [Tube.coverClass]
    exact Finset.card_eq_sum_card_fiberwise fun i hi => 𝒰.cover.assign_mem k hk i hi
  have h1 : (s.card : NNReal)
      ≤ ((𝒰.cover.indexSet k).card : NNReal) * (C * 𝒰.branchingN k) := by
    rw [hpart]
    push_cast
    calc ∑ j' ∈ 𝒰.cover.indexSet k, ((Tube.coverClass s (𝒰.cover.assign k) j').card : NNReal)
        ≤ ∑ _j' ∈ 𝒰.cover.indexSet k, C * 𝒰.branchingN k :=
          Finset.sum_le_sum fun j' hj' => 𝒰.card_class_le k hk j' hj'
      _ = ((𝒰.cover.indexSet k).card : NNReal) * (C * 𝒰.branchingN k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : 𝒰.branchingN k ≤ C * ((Tube.coverClass s (𝒰.cover.assign k) j).card : NNReal) :=
    𝒰.le_card_class k hk j hj
  calc (s.card : NNReal)
      ≤ ((𝒰.cover.indexSet k).card : NNReal) * (C * 𝒰.branchingN k) := h1
    _ ≤ C * (C * (C * ((Tube.coverClass s (𝒰.cover.assign k) j).card : NNReal))) := by
        gcongr
    _ = C ^ 3 * ((Tube.coverClass s (𝒰.cover.assign k) j).card : NNReal) := by ring

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **When the bottom classes are singletons, a coarse class injects into the bottom nodes under
its node**: the assignment fibre has the class's cardinality and lies in `nodesUnder`. -/
theorem card_coverClass_le_card_nodesUnder_bot {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C) {a : ℕ} (ha : a ≤ N)
    (hbot : ∀ j', (Tube.coverClass s (𝒰.cover.assign N) j').card ≤ 1) (j : ι) :
    (Tube.coverClass s (𝒰.cover.assign a) j).card ≤ (𝒰.nodesUnder N a j).card := by
  classical
  refine le_trans ?_ (Finset.card_le_card (𝒰.assignFibre_subset_nodesUnder ha le_rfl j))
  unfold Tube.UniformTubeSet.assignFibre
  rw [Finset.card_image_of_injOn]
  intro i hi i' hi' h
  have hi1 : i ∈ Tube.coverClass s (𝒰.cover.assign N) (𝒰.cover.assign N i) := by
    have hi0 : i ∈ s := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
    simp [Tube.coverClass, hi0]
  have hi1' : i' ∈ Tube.coverClass s (𝒰.cover.assign N) (𝒰.cover.assign N i) := by
    have hi0 : i' ∈ s := (Finset.mem_filter.mp (Finset.mem_coe.mp hi')).1
    simp only [Tube.coverClass, Finset.mem_filter]
    exact ⟨hi0, h.symm⟩
  exact Finset.card_le_one.mp (hbot _) i hi1 i' hi1'

omit [Nontrivial E] in
/-- **A family of pairwise disjoint bodies has maximal density at most `1`.** -/
theorem maxDensity_le_one_of_pairwiseDisjoint (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (h : (s : Set ι).PairwiseDisjoint (fun i => (W i).carrier)) :
    Kakeya.maxDensity s W ≤ 1 := by
  classical
  rw [Kakeya.maxDensity_le_iff]
  intro K
  unfold Kakeya.densityIn
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  have hpd : (((s.filter fun i => W i ≤ K) : Finset ι) : Set ι).PairwiseDisjoint
      (fun i => (W i).carrier) := by
    refine h.subset ?_
    intro i hi
    exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
  rw [← measure_biUnion_finset hpd (fun i _ => (W i).isCompact.isClosed.measurableSet)]
  refine measure_mono ?_
  refine Set.iUnion₂_subset fun i hi => ?_
  exact (Finset.mem_filter.mp hi).2

end Counting

/-! ## The parallel grid family -/

section Grid

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The coordinate vectors of `ℝ³`. -/
noncomputable def gridE (k : Fin 3) : E3 := EuclideanSpace.single k (1 : ℝ)

theorem norm_gridE (k : Fin 3) : ‖gridE k‖ = 1 := by
  simp [gridE]

theorem inner_gridE_of_ne {k l : Fin 3} (h : k ≠ l) : inner ℝ (gridE k) (gridE l) = 0 := by
  simp [gridE, EuclideanSpace.inner_single_left, h]

/-- The grid offsets: the `n`-th point of a `K × K` square grid of spacing `3δ` in the
`(e₀, e₁)`-plane, `n < K * K`. -/
noncomputable def gridW (δ : NNReal) (K n : ℕ) : E3 :=
  (3 * (δ : ℝ) * ((n / K : ℕ) : ℝ)) • gridE 0 + (3 * (δ : ℝ) * ((n % K : ℕ) : ℝ)) • gridE 1

/-- The central `δ`-tube: midpoint `0`, direction `e₂`. -/
noncomputable def gridTube (δ : NNReal) : Tube δ E3 :=
  Tube.ofMidpointDirection δ 0 (gridE 2) (norm_gridE 2)

/-- The `n`-th leaf: the central tube translated by the `n`-th grid offset. -/
noncomputable def gridLeaf (δ : NNReal) (K n : ℕ) : Tube δ E3 :=
  (gridTube δ).translate (gridW δ K n)

theorem inner_gridW_e₂ (δ : NNReal) (K n : ℕ) : inner ℝ (gridW δ K n) (gridE 2) = 0 := by
  simp only [gridW, inner_add_left, inner_smul_left]
  rw [inner_gridE_of_ne (by decide), inner_gridE_of_ne (by decide)]
  simp

theorem norm_gridW_le (δ : NNReal) {K n : ℕ} (hn : n < K * K) :
    ‖gridW δ K n‖ ≤ 6 * (δ : ℝ) * K := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hn
    · exact h
  have h1 : n / K < K := Nat.div_lt_of_lt_mul hn
  have h2 : n % K < K := Nat.mod_lt n hK
  have h1' : ((n / K : ℕ) : ℝ) ≤ K := by exact_mod_cast h1.le
  have h2' : ((n % K : ℕ) : ℝ) ≤ K := by exact_mod_cast h2.le
  have hδ : (0 : ℝ) ≤ δ := δ.coe_nonneg
  calc ‖gridW δ K n‖
      ≤ ‖(3 * (δ : ℝ) * ((n / K : ℕ) : ℝ)) • gridE 0‖
        + ‖(3 * (δ : ℝ) * ((n % K : ℕ) : ℝ)) • gridE 1‖ := norm_add_le _ _
    _ = 3 * (δ : ℝ) * ((n / K : ℕ) : ℝ) + 3 * (δ : ℝ) * ((n % K : ℕ) : ℝ) := by
        rw [norm_smul, norm_smul, norm_gridE, norm_gridE, mul_one, mul_one,
          Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    _ ≤ 3 * (δ : ℝ) * K + 3 * (δ : ℝ) * K := by gcongr
    _ = 6 * (δ : ℝ) * K := by ring

/-- Distinct grid indices below `K * K` have distinct `(quotient, remainder)` pairs. -/
theorem gridPair_ne {K n n' : ℕ} (h : n ≠ n') :
    n / K ≠ n' / K ∨ n % K ≠ n' % K := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  apply h
  calc n = K * (n / K) + n % K := (Nat.div_add_mod n K).symm
    _ = K * (n' / K) + n' % K := by rw [hcon.1, hcon.2]
    _ = n' := Nat.div_add_mod n' K

theorem one_le_abs_sub_of_ne {a b : ℕ} (h : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt
  · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast hlt
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **Grid separation**: distinct offsets are at least `3δ` apart. -/
theorem three_mul_le_norm_gridW_sub (δ : NNReal) {K n n' : ℕ} (h : n ≠ n') :
    3 * (δ : ℝ) ≤ ‖gridW δ K n - gridW δ K n'‖ := by
  set a : ℝ := 3 * (δ : ℝ) * (((n / K : ℕ) : ℝ) - ((n' / K : ℕ) : ℝ)) with ha
  set b : ℝ := 3 * (δ : ℝ) * (((n % K : ℕ) : ℝ) - ((n' % K : ℕ) : ℝ)) with hb
  have hdiff : gridW δ K n - gridW δ K n' = a • gridE 0 + b • gridE 1 := by
    simp only [gridW, ha, hb, sub_smul, mul_sub]
    module
  have hsq : ‖gridW δ K n - gridW δ K n'‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hdiff, norm_add_sq_real, inner_smul_left, inner_smul_right,
      inner_gridE_of_ne (by decide), norm_smul, norm_smul, norm_gridE, norm_gridE]
    simp [Real.norm_eq_abs, sq_abs]
  have hδ : (0 : ℝ) ≤ δ := δ.coe_nonneg
  have hlow : (3 * (δ : ℝ)) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    have h3 : (0 : ℝ) ≤ (3 * (δ : ℝ)) ^ 2 := by positivity
    rcases gridPair_ne (K := K) h with hq | hr
    · have h1 := one_le_abs_sub_of_ne hq
      set x : ℝ := ((n / K : ℕ) : ℝ) - ((n' / K : ℕ) : ℝ) with hx
      have hx2 : (1 : ℝ) ≤ x ^ 2 := by
        have := sq_abs x
        nlinarith [h1, abs_nonneg x]
      have : (3 * (δ : ℝ)) ^ 2 ≤ a ^ 2 := by
        calc (3 * (δ : ℝ)) ^ 2 = (3 * (δ : ℝ)) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (3 * (δ : ℝ)) ^ 2 * x ^ 2 := by gcongr
          _ = a ^ 2 := by rw [ha]; ring
      nlinarith [sq_nonneg b]
    · have h1 := one_le_abs_sub_of_ne hr
      set x : ℝ := ((n % K : ℕ) : ℝ) - ((n' % K : ℕ) : ℝ) with hx
      have hx2 : (1 : ℝ) ≤ x ^ 2 := by
        have := sq_abs x
        nlinarith [h1, abs_nonneg x]
      have : (3 * (δ : ℝ)) ^ 2 ≤ b ^ 2 := by
        calc (3 * (δ : ℝ)) ^ 2 = (3 * (δ : ℝ)) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (3 * (δ : ℝ)) ^ 2 * x ^ 2 := by gcongr
          _ = b ^ 2 := by rw [hb]; ring
      nlinarith [sq_nonneg a]
  rw [← hsq] at hlow
  by_contra hlt
  have hlt' : ‖gridW δ K n - gridW δ K n'‖ < 3 * (δ : ℝ) := not_le.mp hlt
  have h0 : (0 : ℝ) ≤ ‖gridW δ K n - gridW δ K n'‖ := norm_nonneg _
  nlinarith [hlow, hlt', h0, hδ]

/-- **Disjoint leaves.**  Two parallel `δ`-tubes whose offsets differ by at least `3δ` in a
direction orthogonal to the common axis are disjoint: for a common point `p = w + q = w' + q'`,
the difference `w - w' = q' - q` is orthogonal to the axis, so its squared norm is at most
`‖w - w'‖ · 2δ`. -/
theorem disjoint_gridLeaf {δ : NNReal} (hδ : 0 < δ) {K n n' : ℕ} (h : n ≠ n') :
    Disjoint (gridLeaf δ K n).carrier (gridLeaf δ K n').carrier := by
  rw [Set.disjoint_left]
  intro p hp hp'
  simp only [gridLeaf, Tube.translate_carrier, Set.mem_preimage] at hp hp'
  set q : E3 := -gridW δ K n + p with hq_def
  set q' : E3 := -gridW δ K n' + p with hq'_def
  have hq : q ∈ (gridTube δ).carrier := hp
  have hq' : q' ∈ (gridTube δ).carrier := hp'
  rw [(gridTube δ).carrier_eq] at hq hq'
  obtain ⟨z, hz, hqz⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨z', hz', hqz'⟩ := Set.mem_iUnion₂.mp hq'
  have hseg : ∀ w ∈ segment ℝ (gridTube δ).x (gridTube δ).y, ∃ t : ℝ, w = t • gridE 2 := by
    intro w hw
    rw [segment_eq_image] at hw
    obtain ⟨θ, -, rfl⟩ := hw
    refine ⟨θ - 1 / 2, ?_⟩
    simp only [gridTube, Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y]
    module
  obtain ⟨t, rfl⟩ := hseg z hz
  obtain ⟨t', rfl⟩ := hseg z' hz'
  rw [Metric.mem_closedBall, dist_eq_norm] at hqz hqz'
  set d := gridW δ K n - gridW δ K n' with hd
  have hdq : d = q' - q := by
    rw [hd, hq_def, hq'_def]
    abel
  have hinner : inner ℝ d (t' • gridE 2 - t • gridE 2) = 0 := by
    rw [inner_sub_right, inner_smul_right, inner_smul_right, hd, inner_sub_left,
      inner_gridW_e₂, inner_gridW_e₂]
    ring
  have hnorm : ‖d‖ ^ 2 ≤ ‖d‖ * (2 * (δ : ℝ)) := by
    have hself : ‖d‖ ^ 2 = inner ℝ d d := (real_inner_self_eq_norm_sq d).symm
    rw [hself]
    have hsplit : d = ((q' - t' • gridE 2) - (q - t • gridE 2)) + (t' • gridE 2 - t • gridE 2) := by
      rw [hdq]; abel
    calc inner ℝ d d
        = inner ℝ d (((q' - t' • gridE 2) - (q - t • gridE 2))
          + (t' • gridE 2 - t • gridE 2)) := congrArg (inner ℝ d) hsplit
      _ = inner ℝ d ((q' - t' • gridE 2) - (q - t • gridE 2))
          + inner ℝ d (t' • gridE 2 - t • gridE 2) := inner_add_right _ _ _
      _ = inner ℝ d ((q' - t' • gridE 2) - (q - t • gridE 2)) := by rw [hinner, add_zero]
      _ ≤ ‖d‖ * ‖(q' - t' • gridE 2) - (q - t • gridE 2)‖ := real_inner_le_norm _ _
      _ ≤ ‖d‖ * (2 * (δ : ℝ)) := by
          gcongr
          calc ‖(q' - t' • gridE 2) - (q - t • gridE 2)‖
              ≤ ‖q' - t' • gridE 2‖ + ‖q - t • gridE 2‖ := norm_sub_le _ _
            _ ≤ (δ : ℝ) + (δ : ℝ) := add_le_add hqz' hqz
            _ = 2 * (δ : ℝ) := by ring
  have h3 := three_mul_le_norm_gridW_sub δ (K := K) h
  rw [← hd] at h3
  have hδr : (0 : ℝ) < δ := hδ
  have hpos : 0 < ‖d‖ := lt_of_lt_of_le (by positivity) h3
  have h2 : ‖d‖ ≤ 2 * (δ : ℝ) := by
    have := hnorm
    rw [sq] at this
    exact le_of_mul_le_mul_left this hpos
  linarith

/-- The leaf lies inside the central tube rescaled to any radius `≥ δ + ‖w‖`. -/
theorem gridLeaf_le_rescale (δ : NNReal) (K n : ℕ) {ρ : NNReal}
    (hρ : (δ : ℝ) + ‖gridW δ K n‖ ≤ ρ) :
    (gridLeaf δ K n).toConvexSpaceBody ≤ ((gridTube δ).rescale ρ).toConvexSpaceBody := by
  have h1 : (gridLeaf δ K n).toConvexSpaceBody
      = ((gridLeaf δ K n).rescale δ).toConvexSpaceBody :=
    (Tube.toConvexSpaceBody_rescale_self _).symm
  rw [h1, gridLeaf]
  refine le_trans (Tube.translate_rescale_le (gridTube δ) (gridW δ K n)
    (ρ' := ‖gridW δ K n‖₊) (by simp) le_rfl) ?_
  refine Tube.rescale_le_rescale_of_radius_le _ ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  exact hρ

/-- The rescaled leaf lies inside the central tube rescaled to `ρ + R` once `‖w‖ ≤ R`. -/
theorem gridLeaf_rescale_le (δ : NNReal) (K n : ℕ) {ρ R : NNReal} (hR : ‖gridW δ K n‖ ≤ R)
    (hδρ : δ ≤ ρ) :
    ((gridLeaf δ K n).rescale ρ).toConvexSpaceBody
      ≤ ((gridTube δ).rescale (ρ + R)).toConvexSpaceBody :=
  Tube.translate_rescale_le (gridTube δ) (gridW δ K n) hR hδρ

/-- The leaves lie in the unit ball. -/
theorem gridLeaf_carrier_subset_ball (δ : NNReal) (K n : ℕ)
    (h : ‖gridW δ K n‖ + (1 / 2 + (δ : ℝ)) ≤ 1) :
    (gridLeaf δ K n).carrier ⊆ Metric.closedBall (0 : E3) 1 := by
  have hmid : midpoint ℝ (gridLeaf δ K n).x (gridLeaf δ K n).y = gridW δ K n := by
    rw [midpoint_eq_smul_add]
    simp only [gridLeaf, gridTube, Tube.translate_x, Tube.translate_y,
      Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y, invOf_eq_inv]
    module
  refine (Kakeya.Tube.carrier_subset_closedBall_midpoint (E := EuclideanSpace ℝ (Fin 3))
    (gridLeaf δ K n)).trans ?_
  rw [hmid]
  refine Metric.closedBall_subset_closedBall' ?_
  rw [dist_zero_right]
  linarith

/-- **The fully shaded leaves**, indexed in `Type u` through `ULift`. -/
noncomputable def gridShaded (δ : NNReal) (K : ℕ) (n : ULift.{u} ℕ) : ShadedTube δ E3 where
  toTube := gridLeaf δ K n.down
  shade := (gridLeaf δ K n.down).carrier
  measurableSet_shade := (gridLeaf δ K n.down).toConvexSpaceBody.isCompact.isClosed.measurableSet
  shade_subset := subset_rfl

/-- The index set `{0, …, K·K - 1}`, lifted to `Type u`. -/
noncomputable def gridIndex (K : ℕ) : Finset (ULift.{u} ℕ) :=
  (Finset.range (K * K)).map Equiv.ulift.symm.toEmbedding

theorem mem_gridIndex {K : ℕ} {n : ULift.{u} ℕ} : n ∈ gridIndex.{u} K ↔ n.down < K * K := by
  simp [gridIndex, Finset.mem_map_equiv]

theorem card_gridIndex (K : ℕ) : (gridIndex.{u} K).card = K * K := by
  simp [gridIndex]

theorem gridShaded_toTube (δ : NNReal) (K : ℕ) (n : ULift.{u} ℕ) :
    (gridShaded.{u} δ K n).toTube = gridLeaf δ K n.down := rfl

/-- Distinct members of the grid family are disjoint. -/
theorem pairwiseDisjoint_gridShaded {δ : NNReal} (hδ : 0 < δ) {K : ℕ}
    (s : Finset (ULift.{u} ℕ)) :
    (s : Set (ULift.{u} ℕ)).PairwiseDisjoint
      (fun n => ((gridShaded.{u} δ K n).toTube).carrier) := by
  intro n _ n' _ hnn'
  exact disjoint_gridLeaf hδ (K := K) (fun h => hnn' (ULift.ext _ _ h))

end Grid

/-! ## The window on an arbitrary hierarchy over the grid family -/

section Model

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem gridScale_coe (δ : NNReal) (N k : ℕ) :
    ((Tube.gridScale δ N k : NNReal) : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) := by
  simp [Tube.gridScale, NNReal.coe_rpow]

/-- **A level whose scale dominates the grid's spread has at most `C` nodes.** -/
theorem gridModel_card_indexSet_le {δ : NNReal} {K : ℕ} {C : NNReal}
    {s' : Finset (ULift.{u} ℕ)} (hs' : s' ⊆ gridIndex.{u} K) (hne : s'.Nonempty)
    (𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ) C)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen δ)
    (hRk : (δ : ℝ) + 6 * δ * K ≤ Tube.gridScale δ (Tube.ssfGridLen δ) k) :
    ((𝒰.cover.indexSet k).card : NNReal) ≤ C := by
  refine card_indexSet_le_of_le_tube 𝒰 hk hne ((gridTube δ).rescale _) ?_
  intro n hn
  refine gridLeaf_le_rescale δ K n.down ?_
  have := norm_gridW_le δ (mem_gridIndex.mp (hs' hn))
  linarith

/-- **The `ENNReal` bookkeeping of the window's lower bound, on atoms.**  A test body of volume
`V ≤ Cvol · ρR²`, a family whose bodies all lie in it with total volume `S ≥ n · cvol · ρ²`, and a
real inequality `x · Cvol · ρR² ≤ C · n · cvol · ρ²` give `x ≤ C · Δ_max` for any
`Δ_max ≥ S / V`. -/
theorem le_mul_maxDensity_of_bounds {x cvol Cvol C ρ ρR : NNReal} {n : ℕ} {V S M : ENNReal}
    (hV0 : V ≠ 0) (hVtop : V ≠ ⊤) (hV : V ≤ (Cvol : ENNReal) * (ρR : ENNReal) ^ 2)
    (hS : (n : ENNReal) * ((cvol : ENNReal) * (ρ : ENNReal) ^ 2) ≤ S) (hSM : S / V ≤ M)
    (hreal : (x : ℝ) * ((Cvol : ℝ) * (ρR : ℝ) ^ 2)
      ≤ (C : ℝ) * ((n : ℝ) * ((cvol : ℝ) * (ρ : ℝ) ^ 2))) :
    (x : ENNReal) ≤ (C : ENNReal) * M := by
  have hnn : x * (Cvol * ρR ^ 2) ≤ C * ((n : NNReal) * (cvol * ρ ^ 2)) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hreal
  calc (x : ENNReal) ≤ (C : ENNReal) * (S / V) := by
        rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVtop)]
        calc (x : ENNReal) * V ≤ (x : ENNReal) * ((Cvol : ENNReal) * (ρR : ENNReal) ^ 2) := by
              gcongr
          _ ≤ (C : ENNReal) * ((n : ENNReal) * ((cvol : ENNReal) * (ρ : ENNReal) ^ 2)) := by
              exact_mod_cast hnn
          _ ≤ (C : ENNReal) * S := by gcongr
    _ ≤ (C : ENNReal) * M := by gcongr

/-- **The real inequality behind the window's lower bound.**  With `ρ ≥ δ^{1-e}`, `R ≤ ρ`,
`η₁ ≤ e` and the cardinality input `δ^{-e} · 4 Cvol C² ≤ #s' · cvol ≤ C³ n · cvol`:
`ρ^{-η₁} · Cvol (ρ + R)² ≤ C · n · cvol · ρ²`. -/
theorem window_lower_bound_real {δ ρ R : ℝ} (hδr : 0 < δ) (hδr1 : δ ≤ 1) (hρpos : 0 < ρ)
    {e η₁ : ℝ} (he0 : 0 < e) (hη1 : 0 ≤ η₁) (hη1e : η₁ ≤ e)
    (hρlo : δ ^ (1 - e) ≤ ρ) (hR0 : 0 ≤ R) (hRρ : R ≤ ρ)
    {Cvol cvol C : ℝ} (hCvol : 0 < Cvol) (hcvol : 0 < cvol) (hC0 : 0 < C)
    {sc n : ℝ} (hcount : (1 / δ) ^ e * (4 * Cvol * C ^ 2) ≤ sc * cvol)
    (hsc : sc ≤ C ^ 3 * n) :
    ρ⁻¹ ^ η₁ * (Cvol * (ρ + R) ^ 2) ≤ C * (n * (cvol * ρ ^ 2)) := by
  have h1 : ρ⁻¹ ^ η₁ ≤ (1 / δ) ^ e := by
    have hinv : ρ⁻¹ ≤ δ ^ (-(1 - e)) := by
      rw [Real.rpow_neg hδr.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hδr _) hρlo
    calc ρ⁻¹ ^ η₁ ≤ (δ ^ (-(1 - e))) ^ η₁ :=
          Real.rpow_le_rpow (inv_nonneg.mpr hρpos.le) hinv hη1
      _ = δ ^ (-(1 - e) * η₁) := (Real.rpow_mul hδr.le _ _).symm
      _ ≤ δ ^ (-e) := by
          refine Real.rpow_le_rpow_of_exponent_ge hδr hδr1 ?_
          have := mul_nonneg he0.le hη1
          nlinarith [hη1e, hη1, he0, this]
      _ = (1 / δ) ^ e := by rw [one_div, Real.inv_rpow hδr.le, Real.rpow_neg hδr.le]
  have h2 : (ρ + R) ^ 2 ≤ 4 * ρ ^ 2 := by
    have h2' : ρ + R ≤ 2 * ρ := by linarith
    have h2'' : (ρ + R) * (ρ + R) ≤ (2 * ρ) * (2 * ρ) :=
      mul_le_mul h2' h2' (by linarith) (by linarith)
    nlinarith [h2'']
  have h3 : (1 / δ) ^ e * (4 * Cvol) ≤ C * n * cvol := by
    have h4 : sc * cvol ≤ C ^ 3 * n * cvol := by gcongr
    have h5 : (1 / δ) ^ e * (4 * Cvol) * C ^ 2 ≤ C * n * cvol * C ^ 2 := by
      have h6 : (1 / δ) ^ e * (4 * Cvol) * C ^ 2 = (1 / δ) ^ e * (4 * Cvol * C ^ 2) := by ring
      have h7 : C * n * cvol * C ^ 2 = C ^ 3 * n * cvol := by ring
      rw [h6, h7]
      exact hcount.trans h4
    exact le_of_mul_le_mul_right h5 (by positivity)
  have hpos1 : 0 ≤ ρ⁻¹ ^ η₁ := Real.rpow_nonneg (inv_nonneg.mpr hρpos.le) _
  calc ρ⁻¹ ^ η₁ * (Cvol * (ρ + R) ^ 2) ≤ (1 / δ) ^ e * (Cvol * (4 * ρ ^ 2)) := by gcongr
    _ = ((1 / δ) ^ e * (4 * Cvol)) * ρ ^ 2 := by ring
    _ ≤ (C * n * cvol) * ρ ^ 2 := by gcongr
    _ = C * (n * (cvol * ρ ^ 2)) := by ring

/-- **The window of `Kakeya.ML2Reduction.IsKatzTaoDividingWindow` holds on any hierarchy over a
large enough subfamily of the grid, at `a = 0`, `b = ssfGridLen δ`, `m = 0`, `C⋆ = C`.**

The three density clauses: the coarse level has at most `C` nodes (all meet the central
`1`-tube); the bottom nodes carry the leaves' carriers, which are pairwise disjoint, so their
density is at most `1`; and at every window radius `ρ ≥ δ^{1-e}` the bottom nodes rescaled to `ρ`
all lie inside the central tube rescaled to `ρ + R ≤ 2ρ`, so their density is at least
`#nodes · cvol ρ² / (Cvol (2ρ)²)`, which the cardinality hypothesis `hcount` makes at least
`C⁻¹ ρ^{-η₁}`.  **This is the sticky configuration**: the intermediate-scale lower bound of the
tree's window is met by *multiplicity* of nearly coincident rescaled nodes, not by many distinct
intermediate nodes. -/
theorem gridModel_window {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {K : ℕ}
    (hN0 : 0 < Tube.ssfGridLen δ)
    {C : NNReal} (hC1 : 1 ≤ C) {s' : Finset (ULift.{u} ℕ)} (hs' : s' ⊆ gridIndex.{u} K)
    (hne : s'.Nonempty)
    (𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ) C)
    {η : ℕ → ℝ} (hη0 : 0 ≤ η 0) (hη1 : 0 ≤ η 1) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1 / 2)
    (hη1e : η 1 ≤ e) {Nsp : ℕ} (hNsp : 0 < Nsp)
    (hR : (δ : ℝ) + 6 * δ * K ≤ (δ : ℝ) ^ (1 - e))
    (hsmall : (δ : ℝ) ^ e ≤ 1 / 2)
    (hcount : ((1 : ℝ) / δ) ^ e * (4 * (Tube.volume_le.C 3 : ℝ) * (C : ℝ) ^ 2)
      ≤ (s'.card : ℝ) * (Tube.le_volume.c 3 : ℝ)) :
    ML2Reduction.IsKatzTaoDividingWindow 𝒰 (C : ENNReal) η e Nsp 0 (Tube.ssfGridLen δ) 0 := by
  classical
  obtain ⟨R, hRdef⟩ : ∃ R : NNReal, R = δ + 6 * δ * K := ⟨_, rfl⟩
  have hRr : (R : ℝ) = (δ : ℝ) + 6 * δ * K := by rw [hRdef]; push_cast; ring
  have hδr : (0 : ℝ) < δ := hδ0
  have hδr1 : (δ : ℝ) ≤ 1 := hδ1
  have hg0 : Tube.gridScale δ (Tube.ssfGridLen δ) 0 = 1 := Tube.gridScale_zero δ _
  have hgN : Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) = δ :=
    Tube.gridScale_self δ hN0
  have hg0r : ((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : NNReal) : ℝ) = 1 := by rw [hg0]; simp
  have hgNr : ((Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : NNReal) : ℝ) = δ := by
    rw [hgN]
  have hδ1e : (R : ℝ) ≤ (δ : ℝ) ^ (1 - e) := by rw [hRr]; exact hR
  have hδ1e' : (δ : ℝ) ^ (1 - e) ≤ (δ : ℝ) ^ e :=
    Real.rpow_le_rpow_of_exponent_ge hδr hδr1 (by linarith)
  have hδe1 : (δ : ℝ) ^ e ≤ 1 := hsmall.trans (by norm_num)
  have hδle : (δ : ℝ) ≤ (δ : ℝ) ^ (1 - e) := by
    calc (δ : ℝ) = (δ : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (δ : ℝ) ^ (1 - e) := Real.rpow_le_rpow_of_exponent_ge hδr hδr1 (by linarith)
  -- leaves lie inside the central tube rescaled to any radius `≥ R`
  have hleaf : ∀ n ∈ s', ∀ ρ : NNReal, R ≤ ρ →
      ((gridShaded.{u} δ K n).toTube).toConvexSpaceBody
        ≤ ((gridTube δ).rescale ρ).toConvexSpaceBody := by
    intro n hn ρ hρ
    refine gridLeaf_le_rescale δ K n.down ?_
    have := norm_gridW_le δ (mem_gridIndex.mp (hs' hn))
    have hρ' : (R : ℝ) ≤ ρ := hρ
    linarith
  -- level `0` has at most `C` nodes
  have hidx0 : ((𝒰.cover.indexSet 0).card : NNReal) ≤ C := by
    refine card_indexSet_le_of_le_tube 𝒰 (Nat.zero_le _) hne
      ((gridTube δ).rescale (Tube.gridScale δ (Tube.ssfGridLen δ) 0)) ?_
    intro n hn
    refine hleaf n hn _ ?_
    rw [hg0]
    have : (R : ℝ) ≤ 1 := hδ1e.trans (hδ1e'.trans hδe1)
    exact_mod_cast this
  -- the leaves are pairwise disjoint, so the bottom classes are singletons
  have hdisj := pairwiseDisjoint_gridShaded.{u} hδ0 (K := K) s'
  have hbot : ∀ j', (Tube.coverClass s' (𝒰.cover.assign (Tube.ssfGridLen δ)) j').card ≤ 1 :=
    card_coverClass_bot_le_one 𝒰 hN0 hdisj
  -- the bottom nodes carry the leaves' carriers
  have hnodecar : ∀ j' ∈ 𝒰.cover.indexSet (Tube.ssfGridLen δ), ∃ i ∈ s',
      𝒰.cover.assign (Tube.ssfGridLen δ) i = j' ∧
      ((gridShaded.{u} δ K i).toTube).carrier = (𝒰.cover.tube (Tube.ssfGridLen δ) j').carrier := by
    intro j' hj'
    obtain ⟨i, hi⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 le_rfl hne hj'
    simp only [Tube.coverClass, Finset.mem_filter] at hi
    refine ⟨i, hi.1, hi.2, ?_⟩
    refine carrier_eq_of_subset_of_radius_eq hgN _ _ ?_
    have := 𝒰.cover.le_tube_assign (Tube.ssfGridLen δ) le_rfl i hi.1
    rw [hi.2] at this
    exact this
  refine ⟨hNsp, hN0, le_rfl, ?_, ?_, ?_, ?_⟩
  · -- scale separation: `δ ≤ δ^e · 1`
    rw [hgNr, hg0r, mul_one]
    calc (δ : ℝ) = (δ : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (δ : ℝ) ^ e := Real.rpow_le_rpow_of_exponent_ge hδr hδr1 (by linarith)
  · -- coarse density: at most `C` nodes
    rw [hg0r, Real.one_rpow, ENNReal.ofReal_one, mul_one]
    calc Kakeya.maxDensity (𝒰.cover.indexSet 0) (fun j => (𝒰.cover.tube 0 j).toConvexSpaceBody)
        ≤ ((𝒰.cover.indexSet 0).card : ENNReal) := Kakeya.maxDensity_le_card _ _
      _ ≤ C := by exact_mod_cast hidx0
  · -- middle density: the bottom nodes are pairwise disjoint
    intro j _
    rw [hg0r, hgNr]
    have hone : (1 : ENNReal) ≤ (C : ENNReal) * ENNReal.ofReal ((1 / (δ : ℝ)) ^ η 0) := by
      have h1 : (1 : ℝ) ≤ (1 / (δ : ℝ)) ^ η 0 :=
        Real.one_le_rpow (by rw [le_div_iff₀ hδr]; linarith) hη0
      calc (1 : ENNReal) = 1 * 1 := (mul_one 1).symm
        _ ≤ (C : ENNReal) * ENNReal.ofReal ((1 / (δ : ℝ)) ^ η 0) := by
            gcongr
            · exact_mod_cast hC1
            · exact ENNReal.one_le_ofReal.mpr h1
    refine le_trans ?_ hone
    refine maxDensity_le_one_of_pairwiseDisjoint _ _ ?_
    intro j₁ hj₁ j₂ hj₂ hne12
    have hj₁' : j₁ ∈ 𝒰.cover.indexSet (Tube.ssfGridLen δ) :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hj₁)).1
    have hj₂' : j₂ ∈ 𝒰.cover.indexSet (Tube.ssfGridLen δ) :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂)).1
    obtain ⟨i₁, hi₁, ha₁, e₁⟩ := hnodecar j₁ hj₁'
    obtain ⟨i₂, hi₂, ha₂, e₂⟩ := hnodecar j₂ hj₂'
    have hi12 : i₁ ≠ i₂ := by
      rintro rfl
      exact hne12 (ha₁.symm.trans ha₂)
    change Disjoint (𝒰.cover.tube (Tube.ssfGridLen δ) j₁).carrier
      (𝒰.cover.tube (Tube.ssfGridLen δ) j₂).carrier
    rw [← e₁, ← e₂]
    exact hdisj hi₁ hi₂ hi12
  · -- the window's lower bound: multiplicity of nearly coincident rescaled nodes
    intro ρ hρlo hρhi j hj
    rw [hg0r, hgNr] at hρlo hρhi
    rw [hg0r, zero_add]
    have hρlo' : (δ : ℝ) ^ (1 - e) ≤ ρ := by
      have h : (δ : ℝ) * (1 / (δ : ℝ)) ^ e = (δ : ℝ) ^ (1 - e) := by
        rw [one_div, Real.inv_rpow hδr.le, ← Real.rpow_neg hδr.le, Real.rpow_sub hδr,
          Real.rpow_one, Real.rpow_neg hδr.le, div_eq_mul_inv]
      rw [h] at hρlo
      exact hρlo
    have hρhi' : (ρ : ℝ) ≤ (δ : ℝ) ^ e := by
      rw [one_mul, div_one] at hρhi
      exact hρhi
    have hρpos : (0 : ℝ) < ρ := lt_of_lt_of_le (Real.rpow_pos_of_pos hδr _) hρlo'
    have hδρ : δ ≤ ρ := by exact_mod_cast hδle.trans hρlo'
    have hRρr : (R : ℝ) ≤ ρ := hδ1e.trans hρlo'
    have hRρ : R ≤ ρ := by exact_mod_cast hRρr
    have hρhalf : (ρ : ℝ) ≤ 1 / 2 := hρhi'.trans hsmall
    -- the test body: the central tube rescaled to `ρ + R ≤ 2ρ`
    obtain ⟨Kb, hKb⟩ : ∃ Kb : ConvexSpaceBody E3,
        Kb = ((gridTube δ).rescale (ρ + R)).toConvexSpaceBody := ⟨_, rfl⟩
    have hnodes : ∀ j' ∈ 𝒰.nodesUnder (Tube.ssfGridLen δ) 0 j,
        ((𝒰.cover.tube (Tube.ssfGridLen δ) j').rescale ρ).toConvexSpaceBody ≤ Kb := by
      intro j' hj'
      have hj'' : j' ∈ 𝒰.cover.indexSet (Tube.ssfGridLen δ) := (Finset.mem_filter.mp hj').1
      obtain ⟨i, hi, -, ecar⟩ := hnodecar j' hj''
      rw [hKb, ← rescale_body_eq_of_carrier_eq_of_radius_eq hgN _ _ ecar hδρ]
      refine gridLeaf_rescale_le δ K i.down ?_ hδρ
      have := norm_gridW_le δ (mem_gridIndex.mp (hs' hi))
      rw [hRr]
      linarith
    have hden := Kakeya.le_maxDensity (𝒰.nodesUnder (Tube.ssfGridLen δ) 0 j)
      (fun j' => ((𝒰.cover.tube (Tube.ssfGridLen δ) j').rescale ρ).toConvexSpaceBody) Kb
    rw [Kakeya.densityIn_of_all_le hnodes] at hden
    have hfr : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
    -- volume bounds
    have hle1 : ρ + R ≤ 1 := by
      have : (ρ : ℝ) + R ≤ 1 := by linarith
      exact_mod_cast this
    have hvolK : volume Kb.carrier
        ≤ ((Tube.volume_le.C 3 : NNReal) : ENNReal) * (((ρ + R : NNReal)) : ENNReal) ^ 2 := by
      have h := Tube.volume_le (E := E3) hle1 ((gridTube δ).rescale (ρ + R))
      rw [hfr, show (3 - 1 : ℕ) = 2 from rfl] at h
      rw [hKb]
      exact h
    have hvolnode : ∀ j' ∈ 𝒰.nodesUnder (Tube.ssfGridLen δ) 0 j,
        ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2
          ≤ volume
            (((𝒰.cover.tube (Tube.ssfGridLen δ) j').rescale ρ).toConvexSpaceBody).carrier := by
      intro j' _
      have h := Tube.le_volume (E := E3) ((𝒰.cover.tube (Tube.ssfGridLen δ) j').rescale ρ)
      rw [hfr, show (3 - 1 : ℕ) = 2 from rfl] at h
      exact h
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (𝒰.nodesUnder (Tube.ssfGridLen δ) 0 j).card := ⟨_, rfl⟩
    have hsum : (n : ENNReal) * (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2)
        ≤ ∑ j' ∈ 𝒰.nodesUnder (Tube.ssfGridLen δ) 0 j,
            volume
              (((𝒰.cover.tube (Tube.ssfGridLen δ) j').rescale ρ).toConvexSpaceBody).carrier := by
      have h := Finset.sum_le_sum hvolnode
      rwa [Finset.sum_const, nsmul_eq_mul, ← hn] at h
    -- the count lower bound
    have hcls := card_le_mul_card_coverClass 𝒰 (Nat.zero_le _) hidx0 hj
    have hnU := card_coverClass_le_card_nodesUnder_bot 𝒰 (Nat.zero_le _) hbot j
    rw [← hn] at hnU
    have hcount' : (s'.card : ℝ) ≤ (C : ℝ) ^ 3 * n := by
      have h1 : (s'.card : NNReal) ≤ C ^ 3 * (n : NNReal) :=
        hcls.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnU) zero_le)
      exact_mod_cast h1
    -- positivity and finiteness of the test volume
    have hKvol0 : volume Kb.carrier ≠ 0 := by
      have h := Tube.le_volume (E := E3) ((gridTube δ).rescale (ρ + R))
      rw [hfr, show (3 - 1 : ℕ) = 2 from rfl] at h
      rw [hKb]
      refine ne_of_gt (lt_of_lt_of_le ?_ h)
      have hρR : (ρ + R : NNReal) ≠ 0 := by
        have : (0 : ℝ) < ρ + R := by positivity
        exact_mod_cast this.ne'
      exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne')
        (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hρR))
    have hKvoltop : volume Kb.carrier ≠ ⊤ := Kb.isCompact.measure_ne_top
    -- assemble
    have hE : ENNReal.ofReal ((1 / (ρ : ℝ)) ^ η 1) = ((ρ⁻¹ ^ η 1 : NNReal) : ENNReal) := by
      have h : (1 / (ρ : ℝ)) ^ η 1 = ((ρ⁻¹ ^ η 1 : NNReal) : ℝ) := by
        push_cast
        rw [one_div]
      rw [h, ENNReal.ofReal_coe_nnreal]
    rw [hE]
    refine le_mul_maxDensity_of_bounds hKvol0 hKvoltop hvolK hsum hden ?_
    push_cast
    exact window_lower_bound_real hδr hδr1 hρpos he0 hη1 hη1e hρlo' R.coe_nonneg hRρr
      (NNReal.coe_pos.mpr (Tube.volume_le.C_pos 3)) (NNReal.coe_pos.mpr (Tube.le_volume.c_pos 3))
      (lt_of_lt_of_le one_pos (by exact_mod_cast hC1)) hcount hcount'

end Model

/-! ## The obstruction -/

section Obstruction

/-- **THE OBSTRUCTION: the count-floor hypothesis `hfloor` of
`Kakeya.ML2Core.geometricCoreAt_of_floor_middleFactor` is FALSE.**

For any admissible parameters `(β, ϖ, gain, dens)` — carried as hypotheses because Katz–Tao and
Frostman at `β` are the development's inputs, exactly as in
`Kakeya.ML2Core.not_middleFactor_hypothesis` — the statement `hfloor` fails at every small scale on
the following configuration, at `ε₁ = 1`, `η_in = ν`, `Cu₀ = C := ssfUniformConst 3`:

* the leaves are `K² ≈ δ^{-2e}/64` parallel unit `δ`-tubes on a `3δ`-grid transverse to a common
  axis, all inside the central `δ^{1-e}`-tube (`gridShaded`), fully shaded;
* the hierarchy is the tree's own uniformiser
  (`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`) on a retained subfamily;
* the window is `a = 0`, `b = ssfGridLen δ`, `m = 0`, `C⋆ = C` (`gridModel_window`): the
  intermediate-scale lower bound `le_window_maxDensity` is met because the bottom nodes, rescaled to
  any window radius `ρ ≥ δ^{1-e}`, are `≈ δ^{-3e/2}` nearly coincident `ρ`-tubes — a *sticky*
  configuration with maximal density `≫ ρ^{-η₁}` by **multiplicity**, not by many distinct
  intermediate nodes.

Every level `m'` in the window `𝒲 = [eN, (1-e)N]` has at most `C` nodes (all meet the central
`ρ_{m'}`-tube, `gridModel_card_indexSet_le`), while the floor demands
`(ρ_p/ρ_{m'})^{2+4ζ} ≥ δ^{-1}` at the top window level for any parent `p` below the bottom one.

**What this shows.**  The tree's window package (`IsKatzTaoDividingWindow`, produced by the existing
GWZ 7.7(B) `dividingScalesKatzTao`) reads the intermediate-scale density on the **fine nodes
rescaled to `ρ`, with multiplicity**; the refined source's count floor (`eq:ml2-count-floor`,
l.4476–4482) is a statement about the number of **distinct** intermediate cells, which that
reading does not control. -/
theorem not_countFloor_hypothesis {η' : ℝ}
    (hfloor : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ ηin : ℝ, 0 < ηin → ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∀ Cu₀ : NNReal,
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) →
        Cu ≤ Cu₀ →
        ∃ p : ℕ, a ≤ p ∧
          (∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m') ∧
          (∀ jθ ∈ 𝒰.cover.indexSet a,
            Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
              ≤ (δ : ENNReal) ^ (-(2 * η'))) ∧
          (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m' →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
                  ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
              ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)))
    (β' ϖ' : ℝ) (gain' dens' : ℝ → ℝ) (hβ0' : 0 < β') (hβ1' : β' ≤ 1)
    (hp' : ML2Assembly.Lemma91ParamsAt.{u} β' ϖ' gain' dens')
    (hKT' : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β')
    (hF' : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β') :
    False := by
  classical
  have hϖ := hp'.window_pos
  have hsp := ML2Spine.spineRung_isSpine hβ0' hβ1' hϖ one_pos hp'.gain_pos hp'.dens_pos
  have hν0 : 0 < ML2Spine.spineNu β' ϖ' 1 gain' dens' :=
    ML2Spine.spineNu_pos hβ0' hϖ one_pos hp'.gain_pos hp'.dens_pos
  have hNsp : 0 < ML2Spine.spineCount ϖ' 1 := ML2Spine.one_le_spineCount hϖ one_pos
  have hC1 : 1 ≤ ShadedTube.ssfUniformConst (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    ShadedTube.one_le_ssfUniformConst _
  have hev := hfloor β' ϖ' gain' dens' hβ0' hβ1' hp' hKT' hF' 1 one_pos _ hν0 le_rfl
    (ShadedTube.ssfUniformConst (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
  obtain ⟨δu, hδu0, hδu1, huni⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf.{u} (E := EuclideanSpace ℝ (Fin 3))
      4 (ML2Spine.spineDiv ϖ' 1 / 2) 1 (by have := hsp.div_pos; positivity) one_pos
  -- the constants of the construction, made opaque
  generalize hC_def : ShadedTube.ssfUniformConst (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) = C
    at hC1 hev huni
  generalize he_def : ML2Spine.spineDiv ϖ' 1 = e at hsp hev huni
  generalize hη_def : ML2Spine.spineRung β' ϖ' 1 gain' dens' = η at hsp hev
  generalize hν_def : ML2Spine.spineNu β' ϖ' 1 gain' dens' = ν at hν0 hev
  generalize hNsp_def : ML2Spine.spineCount ϖ' 1 = Nsp at hNsp hev
  have he0 : 0 < e := hsp.div_pos
  have he64 : e ≤ 1 / 64 := by
    have h1 := hsp.div_le
    have h2 : ML2Spine.spineEps₂ ϖ' 1 ≤ 1 / 64 := ML2Spine.spineEps₂_le_inv64
    linarith
  have hη0 : 0 < η 0 := hsp.rung_pos 0
  have hη1 : 0 < η 1 := hsp.rung_pos 1
  have hη1e : η 1 ≤ e := hsp.rung_le_div 1
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos (by exact_mod_cast hC1)
  -- the thresholds, all fixed before the scale
  obtain ⟨δg, hδg0, hδg⟩ := StickyKakeya.exists_threshold_le_ssfGridLen 8
  obtain ⟨δ64, hδ64, h64⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := 64) (by norm_num) he0
  obtain ⟨δC, hδC, hCν⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg hC1 (by positivity : (0 : ℝ) < ν / 20)
  obtain ⟨δC1, hδC1, hC1'⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := C + 1) (le_add_right hC1) one_pos
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : NNReal,
      A₀ = max 1 (1024 * Tube.volume_le.C 3 * C ^ 2 / Tube.le_volume.c 3) := ⟨_, rfl⟩
  have hA₀1 : 1 ≤ A₀ := by rw [hA₀]; exact le_max_left _ _
  obtain ⟨δA, hδA, hA⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := A₀) hA₀1 (by positivity : (0 : ℝ) < e / 2)
  have hall : ∀ᶠ δ : NNReal in 𝓝[>] 0, False := by
    filter_upwards [hev, Ioc_mem_nhdsGT hδu0,
      Ioc_mem_nhdsGT (show (0 : NNReal) < ⟨δg, hδg0.le⟩ from hδg0),
      Ioc_mem_nhdsGT hδ64, Ioc_mem_nhdsGT hδC, Ioc_mem_nhdsGT hδC1, Ioc_mem_nhdsGT hδA]
      with δ hP hδu hδg' hδ64' hδC' hδC1' hδA'
    obtain ⟨hδ0, hδu⟩ := hδu
    have hδ1 : δ ≤ 1 := hδu.trans hδu1
    have hδr : (0 : ℝ) < δ := hδ0
    have hδr1 : (δ : ℝ) ≤ 1 := hδ1
    -- the grid length is at least `8`
    have hN8r : (8 : ℝ) ≤ (Tube.ssfGridLen δ : ℝ) := by
      refine hδg hδ0 ?_
      have := hδg'.2
      exact_mod_cast this
    have hN8 : 8 ≤ Tube.ssfGridLen δ := by exact_mod_cast hN8r
    have hN0 : 0 < Tube.ssfGridLen δ := by omega
    have hNr : (0 : ℝ) < (Tube.ssfGridLen δ : ℝ) := by exact_mod_cast hN0
    -- `Y = δ^{-e/2}`, `X = δ^{-e} = Y²`
    obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (δ : ℝ) ^ (-(e / 2)) := ⟨_, rfl⟩
    obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (δ : ℝ) ^ (-e) := ⟨_, rfl⟩
    have hYpos : 0 < Y := by rw [hY]; exact Real.rpow_pos_of_pos hδr _
    have hX : X = Y ^ 2 := by
      rw [hY, hXdef, ← Real.rpow_mul_natCast hδr.le]
      congr 1
      push_cast
      ring
    have h64r : (64 : ℝ) ≤ X := by
      have h := h64 δ hδ0 hδ64'.2
      have h' : ((64 : NNReal) : ℝ) ≤ ((δ ^ (-e) : NNReal) : ℝ) := NNReal.coe_le_coe.mpr h
      rw [hXdef]
      simpa [NNReal.coe_rpow] using h'
    have hAr : (A₀ : ℝ) ≤ Y := by
      have h := hA δ hδ0 hδA'.2
      have h' : ((A₀ : NNReal) : ℝ) ≤ ((δ ^ (-(e / 2)) : NNReal) : ℝ) := NNReal.coe_le_coe.mpr h
      rw [hY]
      simpa [NNReal.coe_rpow] using h'
    have hc3 : (0 : ℝ) < Tube.le_volume.c 3 := NNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)
    have hA₀r : 1024 * (Tube.volume_le.C 3 : ℝ) * (C : ℝ) ^ 2 / (Tube.le_volume.c 3 : ℝ) ≤ A₀ := by
      have h : (1024 * Tube.volume_le.C 3 * C ^ 2 / Tube.le_volume.c 3 : NNReal) ≤ A₀ := by
        rw [hA₀]
        exact le_max_right _ _
      have h' := NNReal.coe_le_coe.mpr h
      push_cast at h'
      exact h'
    have hX0 : (0 : ℝ) ≤ X := by linarith
    have hδe : (δ : ℝ) ^ e ≤ 1 / 64 := by
      have h : (δ : ℝ) ^ e = X⁻¹ := by rw [hXdef, Real.rpow_neg hδr.le, inv_inv]
      rw [h, inv_le_comm₀ (by linarith) (by norm_num)]
      simpa using h64r
    -- the grid size
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊X / 8⌋₊ := ⟨_, rfl⟩
    have hKle : (K : ℝ) ≤ X / 8 := by rw [hK]; exact Nat.floor_le (by positivity)
    have hKge : X / 16 ≤ K := by
      have h1 := Nat.lt_floor_add_one (X / 8)
      rw [← hK] at h1
      linarith
    have hK8 : 8 ≤ K := by rw [hK]; exact Nat.le_floor (by linarith)
    have hKpos : 0 < K := by omega
    have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
    -- the spread `R = δ + 6δK` is at most `δ^{1-e}`
    have hδ1e : (δ : ℝ) ^ (1 - e) = δ * X := by
      rw [hXdef, sub_eq_add_neg, Real.rpow_add hδr, Real.rpow_one]
    have hR : (δ : ℝ) + 6 * δ * K ≤ (δ : ℝ) ^ (1 - e) := by
      rw [hδ1e]
      have h1 : 6 * (δ : ℝ) * K ≤ (3 / 4) * (δ * X) := by
        have := mul_le_mul_of_nonneg_left hKle hδr.le
        linarith
      have h2 : (δ : ℝ) ≤ (1 / 4) * (δ * X) := by
        have := mul_le_mul_of_nonneg_left h64r hδr.le
        linarith
      linarith
    have hδ1e_le : (δ : ℝ) ^ (1 - e) ≤ (δ : ℝ) ^ e :=
      Real.rpow_le_rpow_of_exponent_ge hδr hδr1 (by linarith)
    have hsmall : (δ : ℝ) ^ e ≤ 1 / 2 := hδe.trans (by norm_num)
    -- the family
    have hball : ∀ n ∈ gridIndex.{u} K,
        (gridShaded.{u} δ K n).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      intro n hn
      refine gridLeaf_carrier_subset_ball δ K n.down ?_
      have h1 := norm_gridW_le δ (mem_gridIndex.mp hn)
      linarith
    have hcards : ((gridIndex.{u} K).card : ℝ) = (K : ℝ) * K := by
      rw [card_gridIndex]
      push_cast
      ring
    have hcard4 : ((gridIndex.{u} K).card : ℝ) ≤ (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) := by
      rw [hcards]
      have hKX : (K : ℝ) ≤ X := by linarith
      have h1 : (K : ℝ) * K ≤ X * X := mul_le_mul hKX hKX hKr.le hX0
      have h2 : X * X = (δ : ℝ) ^ (-(2 * e)) := by
        rw [hXdef, ← sq, ← Real.rpow_mul_natCast hδr.le]
        congr 1
        push_cast
        ring
      have h3 : (δ : ℝ) ^ (-(2 * e)) ≤ (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hδr hδr1 (by push_cast; linarith)
      linarith
    obtain ⟨s', hs's, V', hVto, -, hcnt, -, ⟨𝒱⟩⟩ :=
      huni hδ0 hδu (gridIndex.{u} K) (gridShaded.{u} δ K) hball hcard4
    have hs'ne : s'.Nonempty := by
      rw [← Finset.card_pos]
      by_contra h0
      have h0' : s'.card = 0 := by omega
      rw [h0'] at hcnt
      have : ((gridIndex.{u} K).card : ℝ) ≤ 0 := by simpa using hcnt
      rw [hcards] at this
      have := mul_pos hKr hKr
      linarith
    have hs'card : (K : ℝ) * K ≤ Y * s'.card := by
      rw [← hcards, hY]
      exact hcnt
    -- the hierarchy, transported to the fully shaded family
    let 𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ)
        C :=
      𝒱.tubeUniform.copyTubes (fun n => (hVto n).symm)
    -- the cardinality input of the window's lower bound
    have hcount : ((1 : ℝ) / δ) ^ e * (4 * (Tube.volume_le.C 3 : ℝ) * (C : ℝ) ^ 2)
        ≤ (s'.card : ℝ) * (Tube.le_volume.c 3 : ℝ) := by
      have h1 : ((1 : ℝ) / δ) ^ e = Y ^ 2 := by
        rw [one_div, Real.inv_rpow hδr.le, ← Real.rpow_neg hδr.le, ← hXdef, hX]
      have hs'ge : Y ^ 3 / 256 ≤ s'.card := by
        have hKge' : Y ^ 2 / 16 ≤ K := by rw [← hX]; exact hKge
        have hK2 : Y ^ 2 * Y ^ 2 / 256 ≤ (K : ℝ) * K := by
          have h0 : 0 ≤ Y ^ 2 / 16 := by positivity
          have := mul_le_mul hKge' hKge' h0 hKr.le
          calc Y ^ 2 * Y ^ 2 / 256 = (Y ^ 2 / 16) * (Y ^ 2 / 16) := by ring
            _ ≤ (K : ℝ) * K := this
        have h := hK2.trans hs'card
        have hY' : Y ^ 2 * Y ^ 2 / 256 = Y * (Y ^ 3 / 256) := by ring
        rw [hY'] at h
        exact le_of_mul_le_mul_left h hYpos
      rw [h1]
      have hA' : 1024 * (Tube.volume_le.C 3 : ℝ) * (C : ℝ) ^ 2 ≤ Y * Tube.le_volume.c 3 := by
        have h := hA₀r.trans hAr
        rwa [div_le_iff₀ hc3] at h
      calc Y ^ 2 * (4 * (Tube.volume_le.C 3 : ℝ) * (C : ℝ) ^ 2)
          = Y ^ 2 * (1024 * (Tube.volume_le.C 3 : ℝ) * (C : ℝ) ^ 2) / 256 := by ring
        _ ≤ Y ^ 2 * (Y * Tube.le_volume.c 3) / 256 := by gcongr
        _ = (Y ^ 3 / 256) * Tube.le_volume.c 3 := by ring
        _ ≤ s'.card * Tube.le_volume.c 3 := by gcongr
    have hwin : ML2Reduction.IsKatzTaoDividingWindow 𝒰 (C : ENNReal) η e Nsp 0
        (Tube.ssfGridLen δ) 0 :=
      gridModel_window hδ0 hδ1 hN0 hC1 hs's hs'ne 𝒰 hη0.le hη1.le he0 (by linarith) hη1e hNsp
        hR hsmall hcount
    -- the remaining binders of `hP`
    have hball' : ∀ i ∈ s',
        (gridShaded.{u} δ K i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      fun i hi => hball i (hs's hi)
    have hone_le : ∀ x : ℝ, 0 ≤ x → (1 : ENNReal) ≤ (δ : ENNReal) ^ (-x) := by
      intro x hx
      have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
      have := ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith : -x ≤ (0 : ℝ))
      simpa using this
    have hmax : Kakeya.maxDensity s' (fun i => (gridShaded.{u} δ K i).toConvexSpaceBody)
        ≤ (δ : ENNReal) ^ (-ν) := by
      refine le_trans ?_ (hone_le _ hν0.le)
      exact maxDensity_le_one_of_pairwiseDisjoint _ _ (pairwiseDisjoint_gridShaded.{u} hδ0 s')
    have hdense : ML2Shaded.HasDenseShading 1 s'
        (fun i => (gridShaded.{u} δ K i).toShadedBody) := by
      intro i _
      simp [gridShaded]
    have hcomp : ML2Shaded.HasComparableDensities (1 : NNReal)⁻¹ s'
        (fun i => (gridShaded.{u} δ K i).toShadedBody) := by
      intro i _ j _
      simp [gridShaded, mul_comm]
    have hlam : δ ^ ν / 2 ≤ (1 : NNReal) := by
      have h1 : δ ^ ν ≤ 1 := NNReal.rpow_le_one hδ1 hν0.le
      calc δ ^ ν / 2 ≤ 1 / 2 := by gcongr
        _ ≤ 1 := by norm_num
    have hcard' : (s'.card : NNReal) ≤ δ ^ (-(4 : ℝ)) := by
      have h1 : (s'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) := by
        have h : (s'.card : ℝ) ≤ (gridIndex.{u} K).card := by
          exact_mod_cast Finset.card_le_card hs's
        have h4 : (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) = (δ : ℝ) ^ (-(4 : ℝ)) := by norm_num
        linarith [hcard4]
      rw [← NNReal.coe_le_coe]
      push_cast
      exact h1
    have hCstar : (C : ENNReal) ≤ (δ : ENNReal) ^ (-(ν / 20)) := hCν δ hδ0 hδC'.2
    obtain ⟨p, -, hpm, -, hflo⟩ :=
      hP s' (gridShaded.{u} δ K) C 1 𝒰 (C : ENNReal) 0 (Tube.ssfGridLen δ) 0 hwin hball' hs'ne
        hmax hdense hcomp hlam hcard' hCstar le_rfl
    -- the two window levels `mlo = ⌈eN⌉`, `mhi = ⌊(1-e)N⌋`
    obtain ⟨mlo, hmlo⟩ : ∃ m : ℕ, m = ⌈e * (Tube.ssfGridLen δ : ℝ)⌉₊ := ⟨_, rfl⟩
    obtain ⟨mhi, hmhi⟩ : ∃ m : ℕ, m = ⌊(1 - e) * (Tube.ssfGridLen δ : ℝ)⌋₊ := ⟨_, rfl⟩
    have heN : 0 < e * (Tube.ssfGridLen δ : ℝ) := by positivity
    have heN64 : e * (Tube.ssfGridLen δ : ℝ) ≤ (Tube.ssfGridLen δ : ℝ) / 64 := by
      have := mul_le_mul_of_nonneg_right he64 hNr.le
      linarith
    have hmlo_ge : e * (Tube.ssfGridLen δ : ℝ) ≤ mlo := by rw [hmlo]; exact Nat.le_ceil _
    have hmlo_lt : (mlo : ℝ) < e * (Tube.ssfGridLen δ : ℝ) + 1 := by
      rw [hmlo]; exact Nat.ceil_lt_add_one heN.le
    have hmhi_le : (mhi : ℝ) ≤ (1 - e) * (Tube.ssfGridLen δ : ℝ) := by
      rw [hmhi]; exact Nat.floor_le (mul_nonneg (by linarith) hNr.le)
    have hmhi_gt : (1 - e) * (Tube.ssfGridLen δ : ℝ) - 1 < mhi := by
      have := Nat.lt_floor_add_one ((1 - e) * (Tube.ssfGridLen δ : ℝ))
      rw [← hmhi] at this
      linarith
    have hmlo_pos : 0 < mlo := by
      have : (0 : ℝ) < mlo := lt_of_lt_of_le heN hmlo_ge
      exact_mod_cast this
    have hmlo_ltN : mlo < Tube.ssfGridLen δ := by
      have : (mlo : ℝ) < (Tube.ssfGridLen δ : ℝ) := by linarith
      exact_mod_cast this
    have hmhi_pos : 0 < mhi := by
      have : (0 : ℝ) < mhi := by linarith
      exact_mod_cast this
    have hmhi_ltN : mhi < Tube.ssfGridLen δ := by
      have : (mhi : ℝ) < (Tube.ssfGridLen δ : ℝ) := by linarith
      exact_mod_cast this
    have hmlo_lt_mhi : mlo < mhi := by
      have : (mlo : ℝ) < mhi := by linarith
      exact_mod_cast this
    have hmlo_le : (mlo : ℝ) ≤ (1 - e) * (Tube.ssfGridLen δ : ℝ) := by linarith
    have hmhi_ge : e * (Tube.ssfGridLen δ : ℝ) ≤ mhi := by linarith
    -- grid scales as real powers
    have hg0r : ((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : NNReal) : ℝ) = 1 := by
      rw [Tube.gridScale_zero]
      simp
    have hgNr : ((Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : NNReal) : ℝ) = δ := by
      rw [Tube.gridScale_self δ hN0]
    have h𝒲 : ∀ m' : ℕ, e * (Tube.ssfGridLen δ : ℝ) ≤ m' →
        (m' : ℝ) ≤ (1 - e) * (Tube.ssfGridLen δ : ℝ) →
        (((Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : NNReal) : ℝ)
            / ((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : NNReal) : ℝ)) ^ (1 - e)
          ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : NNReal) : ℝ)
            / ((Tube.gridScale δ (Tube.ssfGridLen δ) m' : NNReal) : ℝ) ∧
        ((Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : NNReal) : ℝ)
            / ((Tube.gridScale δ (Tube.ssfGridLen δ) m' : NNReal) : ℝ)
          ≤ (((Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : NNReal) : ℝ)
            / ((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : NNReal) : ℝ)) ^ e := by
      intro m' h1 h2
      rw [hgNr, hg0r, gridScale_coe, div_one]
      have hq : (δ : ℝ) / (δ : ℝ) ^ ((m' : ℝ) / (Tube.ssfGridLen δ : ℝ))
          = (δ : ℝ) ^ (1 - (m' : ℝ) / (Tube.ssfGridLen δ : ℝ)) := by
        rw [Real.rpow_sub hδr, Real.rpow_one]
      rw [hq]
      have hm'N : (m' : ℝ) / (Tube.ssfGridLen δ : ℝ) ≤ 1 - e := by
        rw [div_le_iff₀ hNr]
        linarith
      have hm'N' : e ≤ (m' : ℝ) / (Tube.ssfGridLen δ : ℝ) := by
        rw [le_div_iff₀ hNr]
        exact h1
      constructor
      · exact Real.rpow_le_rpow_of_exponent_ge hδr hδr1 (by linarith)
      · exact Real.rpow_le_rpow_of_exponent_ge hδr hδr1 (by linarith)
    obtain ⟨hlo1, hlo2⟩ := h𝒲 mlo hmlo_ge hmlo_le
    obtain ⟨hhi1, hhi2⟩ := h𝒲 mhi hmhi_ge hmhi_le
    have hp_lt : p < mlo := hpm mlo hmlo_pos hmlo_ltN hlo1 hlo2
    have hp_lt_hi : p < mhi := lt_trans hp_lt hmlo_lt_mhi
    have hpN : p ≤ Tube.ssfGridLen δ := by omega
    -- the cell: the parent node of any leaf under its coarse node
    obtain ⟨i₀, hi₀⟩ := hs'ne
    have hjθ : 𝒰.cover.assign 0 i₀ ∈ 𝒰.cover.indexSet 0 :=
      𝒰.cover.assign_mem 0 (Nat.zero_le _) i₀ hi₀
    have hjp : 𝒰.cover.assign p i₀ ∈ 𝒰.nodesUnder p 0 (𝒰.cover.assign 0 i₀) :=
      𝒰.assign_mem_nodesUnder (Nat.zero_le _) hpN hi₀
    have hfl := hflo _ hjθ _ hjp mhi hmhi_pos hmhi_ltN hhi1 hhi2 hp_lt_hi
    -- at most `C` nodes at the level `mhi`
    have hcnt_le : ((𝒰.nodesUnder mhi p (𝒰.cover.assign p i₀)).card : ℝ) ≤ C := by
      have h1 : (𝒰.nodesUnder mhi p (𝒰.cover.assign p i₀)).card ≤ (𝒰.cover.indexSet mhi).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have h2 : ((𝒰.cover.indexSet mhi).card : NNReal) ≤ C := by
        refine gridModel_card_indexSet_le hs's ⟨i₀, hi₀⟩ 𝒰 hmhi_ltN.le ?_
        rw [gridScale_coe]
        refine hR.trans (Real.rpow_le_rpow_of_exponent_ge hδr hδr1 ?_)
        rw [div_le_iff₀ hNr]
        linarith
      have h2' : ((𝒰.cover.indexSet mhi).card : ℝ) ≤ C := by exact_mod_cast h2
      calc ((𝒰.nodesUnder mhi p (𝒰.cover.assign p i₀)).card : ℝ)
          ≤ (𝒰.cover.indexSet mhi).card := by exact_mod_cast h1
        _ ≤ C := h2'
    -- the floor is at least `δ^{-1}`
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ℝ)
        / ((Tube.gridScale δ (Tube.ssfGridLen δ) mhi : NNReal) : ℝ) := ⟨_, rfl⟩
    have hratio : (δ : ℝ) ^ (-(1 / 2 : ℝ)) ≤ r := by
      rw [hr, gridScale_coe, gridScale_coe, ← Real.rpow_sub hδr]
      refine Real.rpow_le_rpow_of_exponent_ge hδr hδr1 ?_
      rw [div_sub_div_same, div_le_iff₀ hNr]
      have : (p : ℝ) + 1 ≤ mlo := by exact_mod_cast hp_lt
      linarith
    have hone_le_ratio : (1 : ℝ) ≤ r := by
      refine le_trans ?_ hratio
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδr hδr1 (by norm_num)
    have hζpos : 0 < η (0 + 1) := hsp.rung_pos (0 + 1)
    have hfloor_ge : (δ : ℝ) ^ (-(1 : ℝ)) ≤ r ^ (2 + 4 * (η (0 + 1) / 16)) := by
      calc (δ : ℝ) ^ (-(1 : ℝ)) = ((δ : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
            rw [← Real.rpow_mul hδr.le]
            norm_num
        _ ≤ r ^ (2 : ℝ) := Real.rpow_le_rpow (by positivity) hratio (by norm_num)
        _ ≤ r ^ (2 + 4 * (η (0 + 1) / 16)) :=
            Real.rpow_le_rpow_of_exponent_le hone_le_ratio (by linarith)
    have hC1r : (C : ℝ) + 1 ≤ (δ : ℝ) ^ (-(1 : ℝ)) := by
      have h := hC1' δ hδ0 hδC1'.2
      have h' : ((C + 1 : NNReal) : ℝ) ≤ ((δ ^ (-(1 : ℝ)) : NNReal) : ℝ) := NNReal.coe_le_coe.mpr h
      simpa [NNReal.coe_rpow] using h'
    rw [← hr] at hfl
    have hchain : (C : ℝ) + 1 ≤ C := hC1r.trans (hfloor_ge.trans (hfl.trans hcnt_le))
    exact lt_irrefl _ (lt_of_lt_of_le (lt_add_one (C : ℝ)) hchain)
  obtain ⟨δ, hδ⟩ := hall.exists
  exact hδ

end Obstruction

end Kakeya.ML2Core

end
