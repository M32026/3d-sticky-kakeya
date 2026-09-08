/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsProduce
public import Kakeya.DimensionThree.MainLemma2.SetupSideData

/-!
Conjunct 5 of `Kakeya.VeryNotSticky.SideDataObligations` — the
`Kakeya.VeryNotSticky.SplitInputs.fibreScaleCount` obligation at the level `k` of T8 — proved
from `cfg.rho_count : Kakeya.VeryNotSticky.RhoParentData`, using the parent-to-family count comparison
-/

@[expose] public section

open Filter Topology MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open Produce

universe u

/-! ### Geometry: transferring a tube dilate to a thinner coaxial tube -/

/-- **Enlarging the ratio and thinning the scale of a tube dilate.** If `W` has the same core
segment as `V` and the pair `(c', σ)` dominates `(c, ρ)` both in ratio and in the transverse
radius `c ρ`, then `c · V ⊆ c' · W`.

By `Tube.dilate_carrier_eq_cthickening` a dilate is the closed `c ρ`-neighbourhood of the
segment of length `c` through the centre in the direction of the tube; raising `c` enlarges the
segment and raising `c σ` the radius, and the two monotonicities compose. The special case
`σ = ρ` is `Kakeya.ml1Boot.dilate_le_dilate_of_le`, whose segment argument is reproduced here
(that file is Section 8's territory and is not in this module's import closure). -/
theorem dilate_subset_dilate_of_core_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ρ σ : NNReal} (V : Tube ρ E) (W : Tube σ E) (hx : W.x = V.x) (hy : W.y = V.y)
    {c c' : ℝ} (hc : 0 < c) (hcc' : c ≤ c') (hrad : c * (ρ : ℝ) ≤ c' * (σ : ℝ)) :
    (Tube.dilate V c).carrier ⊆ (Tube.dilate W c').carrier := by
  have hc' : 0 < c' := lt_of_lt_of_le hc hcc'
  have hctr : W.center = V.center := by
    simp only [Tube.center, hx, hy]
  have hdir : W.direction = V.direction := by
    simp only [Tube.direction, hx, hy]
  rw [_root_.Tube.dilate_carrier_eq_cthickening V hc,
    _root_.Tube.dilate_carrier_eq_cthickening W hc', hctr, hdir]
  refine (Metric.cthickening_subset_of_subset (c * (ρ : ℝ)) ?_).trans
    (Metric.cthickening_mono hrad _)
  refine Convex.segment_subset (convex_segment _ _) ?_ ?_
  · let t : ℝ := (c' - c) / (2 * c')
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (sub_nonneg.mpr hcc') (mul_pos (by norm_num) hc').le, ?_⟩
      rw [div_le_iff₀ (mul_pos (by norm_num) hc')]
      nlinarith [hc]
    have hpt : AffineMap.lineMap (V.center - (c' / 2) • V.direction)
        (V.center + (c' / 2) • V.direction) t = V.center - (c / 2) • V.direction := by
      rw [AffineMap.lineMap_apply_module]
      have hcombo : ∀ u : ℝ,
          (1 - u) • (V.center - (c' / 2) • V.direction)
              + u • (V.center + (c' / 2) • V.direction)
            = V.center + ((2 * u - 1) * (c' / 2)) • V.direction := by
        intro u; module
      rw [hcombo t]
      have : (2 * t - 1) * (c' / 2) = -(c / 2) := by
        dsimp [t]; field_simp; ring
      rw [this]
      module
    rw [← hpt]
    exact lineMap_mem_segment ℝ _ _ ht
  · let t : ℝ := (c' + c) / (2 * c')
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (by linarith) (mul_pos (by norm_num) hc').le, ?_⟩
      rw [div_le_iff₀ (mul_pos (by norm_num) hc')]
      nlinarith [hc]
    have hpt : AffineMap.lineMap (V.center - (c' / 2) • V.direction)
        (V.center + (c' / 2) • V.direction) t = V.center + (c / 2) • V.direction := by
      rw [AffineMap.lineMap_apply_module]
      have hcombo : ∀ u : ℝ,
          (1 - u) • (V.center - (c' / 2) • V.direction)
              + u • (V.center + (c' / 2) • V.direction)
            = V.center + ((2 * u - 1) * (c' / 2)) • V.direction := by
        intro u; module
      rw [hcombo t]
      have : (2 * t - 1) * (c' / 2) = c / 2 := by
        dsimp [t]; field_simp; ring
      rw [this]
    rw [← hpt]
    exact lineMap_mem_segment ℝ _ _ ht

/-! ### Geometry: the cross-scale packing count -/

/-- **A cross-scale packing count.** A family of pairwise essentially
distinct `σ`-tubes, each of which shares a chord of length `≥ 2/5` with a fixed `ρ`-tube `V`
(`σ ≤ ρ ≤ 1`), has at most `C_{lem:essDistinctTubesInSelfDilate}(n, 32 ρ/σ)` members.

The chord pins each thin tube inside `32 · V` (`Tube.norm_perp_direction_le_of_chord` and
`Tube.subset_dilate_of_norm_perp_direction_le` at `K = 1`, exactly as in
`Tube.subset_dilate_of_common_chord`, whose equal-scale hypothesis does not apply here), and
`32 · V` sits inside the `(32 ρ/σ)`-dilate of the *coaxial `σ`-tube* `V'`
(`Kakeya.VeryNotSticky.dilate_subset_dilate_of_core_eq`), where the same-scale count
`Tube.essDistinctTubesInSelfDilate` — whose dilation ratio is free — applies.

Using the free-ratio same-scale count rather than the cross-scale
`Tube.essDistinctTubesInDilate` costs the ratio exponent `4n` instead of `2n` and avoids both a
`Tube`-type transport across `(ρ/σ)⁻¹ ρ = σ` and the numerical obligation
`32 ≤ Tube.tubeOverlapCoreClose.C n`; the extra `2n` is spent in the `M` of the constant below,
which has room. -/
theorem card_le_selfDilate_of_common_chord {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] {κ : Type*} {ρ σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hσρ : (σ : ℝ) ≤ (ρ : ℝ)) (hρ1 : (ρ : ℝ) ≤ 1)
    (V : Tube ρ E) (a : Finset κ) (U : κ → Tube σ E)
    (hED : (↑a : Set κ).Pairwise fun j l ↦ IsEssentiallyDistinct (U j).carrier (U l).carrier)
    (hchord : ∀ j ∈ a, ∃ p ∈ V.carrier, ∃ q ∈ V.carrier,
      p ∈ (U j).carrier ∧ q ∈ (U j).carrier ∧ (2 / 5 : ℝ) ≤ dist p q) :
    (a.card : ℝ) ≤
      (Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E)
        (32 * (ρ : ℝ) / (σ : ℝ)) : ℝ) := by
  have hσ0R : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.2 hσ0
  set c : ℝ := 32 * (ρ : ℝ) / (σ : ℝ) with hc_def
  have hc32 : (32 : ℝ) ≤ c := by
    rw [hc_def, le_div_iff₀ hσ0R]
    nlinarith
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hcσ : c * (σ : ℝ) = 32 * (ρ : ℝ) := by
    rw [hc_def, div_mul_cancel₀ _ hσ0R.ne']
  -- the coaxial `σ`-tube
  set V' : Tube σ E :=
    Tube.ofMidpointDirection σ V.center V.direction V.norm_direction with hV'
  have hV'x : V'.x = V.x := by
    rw [hV', Tube.ofMidpointDirection_x, V.x_eq_center_sub]; norm_num
  have hV'y : V'.y = V.y := by
    rw [hV', Tube.ofMidpointDirection_y, V.y_eq_center_add]; norm_num
  -- every member of the family sits in the `c`-dilate of `V'`
  have hUT : ∀ j ∈ a, (U j).carrier ⊆ (Kakeya.Tube.dilate V' c).carrier := by
    intro j hj
    obtain ⟨p, hpV, q, hqV, hpU, hqU, hpq⟩ := hchord j hj
    have hpb : p ∈ (Kakeya.Tube.dilate (U j) 2).carrier :=
      Tube.subset_dilate (U j) (by norm_num) hpU
    have hqb : q ∈ (Kakeya.Tube.dilate (U j) 2).carrier :=
      Tube.subset_dilate (U j) (by norm_num) hqU
    have hchordS := Tube.norm_perp_direction_le_of_chord V (U j) (d := (2 / 5 : ℝ))
      (by norm_num) hpq hpV hqV hpb hqb
    have hS : ‖(U j).direction - inner ℝ V.direction (U j).direction • V.direction‖
        ≤ 15 * 1 * (ρ : ℝ) := by
      refine hchordS.trans ?_
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2 / 5)]
      nlinarith
    have h32 : (U j).carrier ⊆ (Kakeya.Tube.dilate V (32 * 1)).carrier :=
      Tube.subset_dilate_of_norm_perp_direction_le V (U j) (K := 1) le_rfl hρ1
        (by simpa using hσρ) hpV hpb hS
    refine h32.trans ?_
    refine dilate_subset_dilate_of_core_eq V V' hV'x hV'y (by norm_num) (by simpa using hc32) ?_
    rw [hcσ]; norm_num
  have h := Tube.essDistinctTubesInSelfDilate (E := E) (ι := κ) (δ := σ) (c := c)
    hc1 hσ0 hσ1 V' a U hED hUT
  have hcast : ((a.card : NNReal) : ENNReal)
      ≤ ((Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c : NNReal) : ENNReal) := by
    simpa using h
  exact_mod_cast ENNReal.coe_le_coe.mp hcast

/-! ### Counting on a `Tube.UniformTubeSet`: the two class bounds -/

section Counting

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The classes of a `Tube.GridCoverSystem` partition the family, so their cardinalities sum to
its cardinality. This is the "partitioning cover" content of Definition 2.1(i) recorded in
`Tube.GridCoverSystem` (the assignment is a *function*). -/
theorem sum_card_coverClass {ι : Type u} (u : Finset ι) (assign : ι → ι) (idx : Finset ι)
    (hmem : ∀ i ∈ u, assign i ∈ idx) :
    ∑ j ∈ idx, (Tube.coverClass u assign j).card = u.card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := assign) (s := u) (t := idx)
    (fun i hi => hmem i hi)
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1

/-- **The class bound  (`card_filter_le_of_uniform`).**
A hierarchy at the constant `C` bounds the members of the family contained in *any* tube of the
grid radius `ρ_k` by `C · (C · N_k)`: the members contained in `V` are distributed among the
nodes that meet `V` through the family, of which Definition 2.1(ii) (`boundedOverlap`) allows at
most `C`, and each such node's class has at most `C · N_k` members (Definition 2.1(iii), upper
half). -/
theorem card_filter_le_of_uniform {δ : NNReal} {ι : Type u} {sPar : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : Tube.UniformTubeSet sPar T N C)
    {k : ℕ} (hk : k ≤ N) (V : Tube (Tube.gridScale δ N k) E) :
    (((sPar.filter (fun i => (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal))
      ≤ C * (C * 𝒰.branchingN k) := by
  classical
  set F : Finset ι := (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ sPar,
    (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
    (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) with hF
  have hFcard : (F.card : NNReal) ≤ C := by
    have := 𝒰.boundedOverlap k hk V
    simpa [hF] using this
  have hsub : sPar.filter (fun i => (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) ⊆
      F.biUnion (fun j => Tube.coverClass sPar (𝒰.cover.assign k) j) := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    obtain ⟨hiS, hiV⟩ := hi
    have hnode : (T i).toConvexSpaceBody
        ≤ (𝒰.cover.tube k (𝒰.cover.assign k i)).toConvexSpaceBody :=
      𝒰.cover.le_tube_assign k hk i hiS
    refine Finset.mem_biUnion.2 ⟨𝒰.cover.assign k i, ?_, ?_⟩
    · simp only [hF, Finset.mem_filter]
      exact ⟨𝒰.cover.assign_mem k hk i hiS, i, hiS, hnode, hiV⟩
    · simp [Tube.coverClass, hiS]
  have hcard1 : (sPar.filter (fun i => (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card
      ≤ ∑ j ∈ F, (Tube.coverClass sPar (𝒰.cover.assign k) j).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  have hcast : (((sPar.filter
        (fun i => (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal))
      ≤ ∑ j ∈ F, ((Tube.coverClass sPar (𝒰.cover.assign k) j).card : NNReal) := by
    exact_mod_cast hcard1
  refine hcast.trans ?_
  have hterm : ∀ j ∈ F, ((Tube.coverClass sPar (𝒰.cover.assign k) j).card : NNReal)
      ≤ C * 𝒰.branchingN k := by
    intro j hj
    have hjidx : j ∈ 𝒰.cover.indexSet k := by
      simp only [hF, Finset.mem_filter] at hj; exact hj.1
    exact 𝒰.card_class_le k hk j hjidx
  calc ∑ j ∈ F, ((Tube.coverClass sPar (𝒰.cover.assign k) j).card : NNReal)
      ≤ ∑ _j ∈ F, C * 𝒰.branchingN k := Finset.sum_le_sum hterm
    _ = (F.card : NNReal) * (C * 𝒰.branchingN k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * (C * 𝒰.branchingN k) := by
        gcongr

/-- **The branching number against the node count.** Summing Definition 2.1(iii)'s lower half
over the nodes at level `k`, and using that the classes partition the family:
`#nodes_k · N_k ≤ C · |sPar|`. This is the half of Definition 2.1 the containment reading cannot
supply, and it is what turns the count on the parent's nodes into a count on the family. -/
theorem card_indexSet_mul_branchingN_le {δ : NNReal} {ι : Type u} {sPar : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : Tube.UniformTubeSet sPar T N C)
    {k : ℕ} (hk : k ≤ N) :
    ((𝒰.cover.indexSet k).card : NNReal) * 𝒰.branchingN k ≤ C * (sPar.card : NNReal) := by
  classical
  have hmem : ∀ i ∈ sPar, 𝒰.cover.assign k i ∈ 𝒰.cover.indexSet k :=
    fun i hi => 𝒰.cover.assign_mem k hk i hi
  calc ((𝒰.cover.indexSet k).card : NNReal) * 𝒰.branchingN k
      = ∑ _j ∈ 𝒰.cover.indexSet k, 𝒰.branchingN k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ 𝒰.cover.indexSet k,
          C * ((Tube.coverClass sPar (𝒰.cover.assign k) j).card : NNReal) :=
        Finset.sum_le_sum fun j hj => 𝒰.le_card_class k hk j hj
    _ = C * ∑ j ∈ 𝒰.cover.indexSet k,
          ((Tube.coverClass sPar (𝒰.cover.assign k) j).card : NNReal) := by
        rw [Finset.mul_sum]
    _ = C * (sPar.card : NNReal) := by
        congr 1
        rw [show ∑ j ∈ 𝒰.cover.indexSet k,
              ((Tube.coverClass sPar (𝒰.cover.assign k) j).card : NNReal)
            = ((∑ j ∈ 𝒰.cover.indexSet k,
              (Tube.coverClass sPar (𝒰.cover.assign k) j).card : ℕ) : NNReal) from by
          push_cast; ring]
        rw [sum_card_coverClass sPar (𝒰.cover.assign k) (𝒰.cover.indexSet k) hmem]

end Counting

/-! ### Parent-to-family and cross-scale comparisons  -/

section Chaining

set_option linter.unusedSectionVars false

/-- **Step 1: the count transported to the parent's node count.** An essentially distinct,
all-used family of `ρ₂`-tubes for `sPar` has at most `P` members per level-`k` node of the
parent's hierarchy, where `P` is the packing constant of
`Kakeya.VeryNotSticky.card_le_selfDilate_of_common_chord` at the ratio `32 ρ_k/ρ₂`: a `ρ₂`-tube
of the family and the node of the member witnessing it both contain that member's `δ`-tube,
hence share a chord of length `≥ 2/5`. -/
theorem card_count_le_mul_card_indexSet {δ ρ2 : NNReal} {ι : Type u} {sPar : Finset ι}
    {T : ι → ShadedTube δ E3} {N : ℕ} {Cpar : NNReal}
    (𝒰par : Tube.UniformTubeSet sPar (fun i ↦ (T i).toTube) N Cpar)
    {k : ℕ} (hk : k ≤ N) (hρ20 : 0 < ρ2)
    (hρ2le : (ρ2 : ℝ) ≤ (Tube.gridScale δ N k : ℝ))
    (hgs1 : (Tube.gridScale δ N k : ℝ) ≤ 1)
    {κ : Type u} (tρ : Finset κ) (Tρ : κ → Tube ρ2 E3)
    (hED : (↑tρ : Set κ).Pairwise fun j l ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ l).carrier)
    (hused : ∀ j ∈ tρ, ∃ i ∈ sPar, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) :
    (tρ.card : ℝ) ≤
      (Tube.essDistinctTubesInSelfDilate.C 3
        (32 * (Tube.gridScale δ N k : ℝ) / (ρ2 : ℝ)) : ℝ)
        * ((𝒰par.cover.indexSet k).card : ℝ) := by
  classical
  set P : ℝ := (Tube.essDistinctTubesInSelfDilate.C 3
    (32 * (Tube.gridScale δ N k : ℝ) / (ρ2 : ℝ)) : ℝ) with hP
  have hP0 : (0 : ℝ) ≤ P := by rw [hP]; positivity
  have hfr : Module.finrank ℝ E3 = 3 := by simp [E3]
  have hρ21 : ρ2 ≤ 1 := by
    have : (ρ2 : ℝ) ≤ 1 := hρ2le.trans hgs1
    exact_mod_cast this
  rcases tρ.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
  -- the witness function
  set Q : κ → ι → Prop := fun j i ↦ i ∈ sPar ∧
    (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody with hQ
  set g : κ → ι := fun j ↦ if h : ∃ i, Q j i then h.choose else i₀ with hg
  have hgspec : ∀ j ∈ tρ, Q j (g j) := by
    intro j hj
    obtain ⟨i, hi, hle⟩ := hused j hj
    have hex : ∃ i, Q j i := ⟨i, hi, hle⟩
    rw [hg]
    simp only [hex, dif_pos]
    exact hex.choose_spec
  set f : κ → ι := fun j ↦ 𝒰par.cover.assign k (g j) with hf
  have hmaps : ∀ j ∈ tρ, f j ∈ 𝒰par.cover.indexSet k := fun j hj =>
    𝒰par.cover.assign_mem k hk (g j) (hgspec j hj).1
  have hfib := Finset.card_eq_sum_card_fiberwise (f := f) (s := tρ)
    (t := 𝒰par.cover.indexSet k) (fun j hj => hmaps j hj)
  -- each fibre is bounded by the packing constant
  have hterm : ∀ p ∈ 𝒰par.cover.indexSet k, (({j ∈ tρ | f j = p}).card : ℝ) ≤ P := by
    intro p _
    refine card_le_selfDilate_of_common_chord (E := E3) hρ20 hρ21 hρ2le hgs1
      (𝒰par.cover.tube k p) _ Tρ (hED.mono (by intro x hx; simpa using (Finset.mem_filter.1 hx).1))
      ?_ |>.trans ?_
    · intro j hj
      simp only [Finset.mem_filter] at hj
      obtain ⟨hjt, hjp⟩ := hj
      have hgs := hgspec j hjt
      have hnode : (T (g j)).toConvexSpaceBody
          ≤ (𝒰par.cover.tube k p).toConvexSpaceBody := by
        have := 𝒰par.cover.le_tube_assign k hk (g j) hgs.1
        rwa [show 𝒰par.cover.assign k (g j) = p from hjp] at this
      obtain ⟨x, hx, y, hy, hxy⟩ := Tube.exists_chord_of_tube (T (g j)).toTube
      exact ⟨x, hnode hx, y, hnode hy, hgs.2 hx, hgs.2 hy, hxy⟩
    · rw [hP, hfr]
  calc (tρ.card : ℝ) = ((∑ p ∈ 𝒰par.cover.indexSet k, ({j ∈ tρ | f j = p}).card : ℕ) : ℝ) := by
        rw [← hfib]
    _ = ∑ p ∈ 𝒰par.cover.indexSet k, (({j ∈ tρ | f j = p}).card : ℝ) := by push_cast; ring
    _ ≤ ∑ _p ∈ 𝒰par.cover.indexSet k, P := Finset.sum_le_sum hterm
    _ = P * ((𝒰par.cover.indexSet k).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Step 2: the parent's node count against the family's own node count.** With the parent's
hierarchy at `Cpar`, a hierarchy of `s` at any constant, and the cardinality retention
`c |sPar| ≤ |s|`, the parent's level-`k` nodes are at most `Cpar³/c` times the family's.

The three inputs are the class and cover comparisons  and the family's own Definition 2.2
datum; no division by the branching number `N_k` occurs — it cancels between
`Kakeya.VeryNotSticky.card_indexSet_mul_branchingN_le` (used on the parent) and
`Kakeya.VeryNotSticky.card_filter_le_of_uniform` (used on the parent, against the *family's*
nodes), leaving `|sPar|` to be cancelled instead. -/
theorem card_indexSet_parent_le {δ : NNReal} {ι : Type u} {s sPar : Finset ι}
    {T : ι → ShadedTube δ E3} {N : ℕ} {Cpar C₀ : NNReal}
    (𝒰par : Tube.UniformTubeSet sPar (fun i ↦ (T i).toTube) N Cpar)
    (𝒰s : Tube.UniformTubeSet s (fun i ↦ (T i).toTube) N C₀)
    (hsub : s ⊆ sPar) (hne : sPar.Nonempty) {k : ℕ} (hk : k ≤ N)
    {c : NNReal} (hret : c * (sPar.card : NNReal) ≤ (s.card : NNReal)) :
    c * ((𝒰par.cover.indexSet k).card : NNReal)
      ≤ Cpar ^ 3 * ((𝒰s.cover.indexSet k).card : NNReal) := by
  classical
  set idxP : Finset ι := 𝒰par.cover.indexSet k with hidxP
  set idxS : Finset ι := 𝒰s.cover.indexSet k with hidxS
  set Nk : NNReal := 𝒰par.branchingN k with hNk
  -- (iii) the family's cardinality against its own node count
  have hs_le : (s.card : NNReal) ≤ (idxS.card : NNReal) * (Cpar * (Cpar * Nk)) := by
    have hmem : ∀ i ∈ s, 𝒰s.cover.assign k i ∈ idxS :=
      fun i hi => 𝒰s.cover.assign_mem k hk i hi
    have hsum := sum_card_coverClass s (𝒰s.cover.assign k) idxS hmem
    have hclass : ∀ j ∈ idxS,
        ((Tube.coverClass s (𝒰s.cover.assign k) j).card : NNReal) ≤ Cpar * (Cpar * Nk) := by
      intro j hj
      refine le_trans ?_ (card_filter_le_of_uniform 𝒰par hk (𝒰s.cover.tube k j))
      refine Nat.cast_le.2 (Finset.card_le_card ?_)
      intro i hi
      simp only [Tube.coverClass, Finset.mem_filter] at hi
      simp only [Finset.mem_filter]
      refine ⟨hsub hi.1, ?_⟩
      have := 𝒰s.cover.le_tube_assign k hk i hi.1
      rwa [hi.2] at this
    calc (s.card : NNReal)
        = ((∑ j ∈ idxS, (Tube.coverClass s (𝒰s.cover.assign k) j).card : ℕ) : NNReal) := by
          rw [hsum]
      _ = ∑ j ∈ idxS, ((Tube.coverClass s (𝒰s.cover.assign k) j).card : NNReal) := by
          push_cast; ring
      _ ≤ ∑ _j ∈ idxS, Cpar * (Cpar * Nk) := Finset.sum_le_sum hclass
      _ = (idxS.card : NNReal) * (Cpar * (Cpar * Nk)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- (ii) the parent's node count against its branching number
  have hpar : (idxP.card : NNReal) * Nk ≤ Cpar * (sPar.card : NNReal) :=
    card_indexSet_mul_branchingN_le 𝒰par hk
  -- multiply and cancel `|sPar|`
  have hkey : c * (idxP.card : NNReal) * (sPar.card : NNReal)
      ≤ Cpar ^ 3 * (idxS.card : NNReal) * (sPar.card : NNReal) := by
    calc c * (idxP.card : NNReal) * (sPar.card : NNReal)
        = (idxP.card : NNReal) * (c * (sPar.card : NNReal)) := by ring
      _ ≤ (idxP.card : NNReal) * (s.card : NNReal) := by gcongr
      _ ≤ (idxP.card : NNReal) * ((idxS.card : NNReal) * (Cpar * (Cpar * Nk))) := by gcongr
      _ = (idxS.card : NNReal) * Cpar ^ 2 * ((idxP.card : NNReal) * Nk) := by ring
      _ ≤ (idxS.card : NNReal) * Cpar ^ 2 * (Cpar * (sPar.card : NNReal)) := by gcongr
      _ = Cpar ^ 3 * (idxS.card : NNReal) * (sPar.card : NNReal) := by ring
  have hpos : (0 : NNReal) < (sPar.card : NNReal) := by
    have : 0 < sPar.card := Finset.card_pos.2 hne
    exact_mod_cast this
  exact le_of_mul_le_mul_right hkey hpos

end Chaining

/-! ### The measured constant -/

/-- The `δ`-free prefactor of the packing count at ambient dimension `3`:
`C_{lem:essDistinctTubesInSelfDilate}(3, c) = A₁ c⁶ + A₂ c¹²`, and this is `A₁ + A₂`, read off
as the value of the two summands at `c = 1`. -/
noncomputable def selfDilatePrefactor : NNReal :=
  Tube.essDistinctTubesInSelfDilate.thinC 3 1 + Tube.essDistinctTubesInSelfDilate.fatC 3 1

/-- **The packing count at a single power of the ratio.** For `1 ≤ c` the two regimes of
`Tube.essDistinctTubesInSelfDilate.C 3 c` — degrees `2n = 6` and `4n = 12` in `c` — are both
below `(A₁ + A₂) c¹²`. -/
theorem essDistinctTubesInSelfDilate_C_le {c : ℝ} (hc : 1 ≤ c) :
    Tube.essDistinctTubesInSelfDilate.C 3 c ≤ selfDilatePrefactor * c.toNNReal ^ 12 := by
  have hc1 : (1 : NNReal) ≤ c.toNNReal := by
    rw [← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hc
  have hthin : Tube.essDistinctTubesInSelfDilate.thinC 3 c
      = Tube.essDistinctTubesInSelfDilate.thinC 3 1 * c.toNNReal ^ 6 := by
    simp only [Tube.essDistinctTubesInSelfDilate.thinC, Real.toNNReal_one]
    norm_num
  have hfat : Tube.essDistinctTubesInSelfDilate.fatC 3 c
      = Tube.essDistinctTubesInSelfDilate.fatC 3 1 * c.toNNReal ^ 12 := by
    simp only [Tube.essDistinctTubesInSelfDilate.fatC, Real.toNNReal_one]
    norm_num
  have hpow : c.toNNReal ^ 6 ≤ c.toNNReal ^ 12 := pow_le_pow_right₀ hc1 (by norm_num)
  calc Tube.essDistinctTubesInSelfDilate.C 3 c
      = Tube.essDistinctTubesInSelfDilate.thinC 3 c
          + Tube.essDistinctTubesInSelfDilate.fatC 3 c := rfl
    _ = Tube.essDistinctTubesInSelfDilate.thinC 3 1 * c.toNNReal ^ 6
          + Tube.essDistinctTubesInSelfDilate.fatC 3 1 * c.toNNReal ^ 12 := by
        rw [hthin, hfat]
    _ ≤ Tube.essDistinctTubesInSelfDilate.thinC 3 1 * c.toNNReal ^ 12
          + Tube.essDistinctTubesInSelfDilate.fatC 3 1 * c.toNNReal ^ 12 := by gcongr
    _ = selfDilatePrefactor * c.toNNReal ^ 12 := by
        rw [selfDilatePrefactor]; ring

/-- **The `δ`-free part of the R17 constant**: the packing prefactor against the twelfth power of the
scale-ratio bound `32 ρ_k/ρ₂ ≤ 64 C_{lem:ml2bodyAngle}(C₀) δ^{-η}`. -/
noncomputable def fibreCountConstant (C₀ : NNReal) : NNReal :=
  selfDilatePrefactor * (64 * NonSlab.bodyAngleConstant C₀) ^ 12

/-! ### `ENNReal` → `NNReal` for the two carried bounds -/

/-- A `≤ δ^y` bound on a coerced `NNReal`, read in `NNReal`. -/
theorem le_rpow_neg_of_coe_le {δ x : NNReal} (hδ : 0 < δ) {y : ℝ}
    (h : (x : ENNReal) ≤ (δ : ENNReal) ^ y) : x ≤ δ ^ y := by
  rwa [← ENNReal.coe_rpow_of_ne_zero hδ.ne', ENNReal.coe_le_coe] at h

/-- The retention clause of `Kakeya.VeryNotSticky.RhoParentData`, read in `NNReal`. -/
theorem mul_le_of_coe_mul_le {δ : NNReal} (hδ : 0 < δ) {y : ℝ} {m n : ℕ}
    (h : (δ : ENNReal) ^ y * (m : ENNReal) ≤ (n : ENNReal)) :
    δ ^ y * (m : NNReal) ≤ (n : NNReal) := by
  rw [← ENNReal.coe_rpow_of_ne_zero hδ.ne', ← ENNReal.coe_natCast m, ← ENNReal.coe_natCast n,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe] at h
  exact h

/-! ### R17: conjunct 5 of `Kakeya.VeryNotSticky.SideDataObligations`, at one configuration -/

/-- **The `fibreScaleCount` obligation from the configuration's parent datum**.

At every level `k` of `cfg.splitHierarchy` sitting two-sidedly at `ρ₂*`,
`ρ₂^{-2-ζ} ≤ Ccnt · |𝕋_{ρ_k}|` with `Ccnt ≤ δ^{-18 η}`. The chain, all of it on the parent
`sPar` that `cfg.rho_count : Kakeya.VeryNotSticky.RhoParentData` names:

* the count clause at `ρ = ρ₂` (in the window by `Kakeya.VeryNotSticky.rho2_range` and
  `cfg.hscale`) gives an essentially distinct, all-used family `t_{ρ₂}` of `ρ₂`-tubes for `sPar`
  with `ρ₂^{-2-ζ} ≤ |t_{ρ₂}|`;
* `Kakeya.VeryNotSticky.card_count_le_mul_card_indexSet` spends it on the parent's level-`k`
  nodes at the packing loss `P = C_{lem:essDistinctTubesInSelfDilate}(3, 32 ρ_k/ρ₂)`;
* `Kakeya.VeryNotSticky.card_indexSet_parent_le` converts the parent's node count into
  `cfg.splitHierarchy`'s at the loss `Cpar³/δ^{2η}` — the parent's Definition 2.1 constant
  cubed against the retention;
* `ρ_k ≤ δ^{-η} ρ₂* = 2 C_{lem:ml2bodyAngle}(C₀) δ^{-η} ρ₂` makes `P ≤ A(C₀) δ^{-12η}` with
  `A` the `δ`-free `Kakeya.VeryNotSticky.fibreCountConstant`, and `1 ≤ Cpar ≤ δ^{-η}` makes
  `Cpar³ ≤ δ^{-3η}`, so the total is `A δ^{-17η}` and one further `η` absorbs `A` at the
  threshold `hthr`.

The exponent `M = 18` is the *measured* one. The exponent `M ≈ 13` suggested by the
cross-scale packing `Tube.essDistinctTubesInDilate` (ratio degree `2n = 6`) does not apply directly here; this proof uses
the free-ratio same-scale count (degree `4n = 12`), which is `+6`, and drops the `≠ k` level
comparison the prediction budgeted (`-1`). Both are `≪ 2^17`, the ceiling of
`Kakeya.VeryNotSticky.tangentialSlabMultAbsorb`. -/
theorem exists_fibreScaleCount_of_rhoParentData (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hC₀bd : 1 ≤ bd.C₀) (hexscal : cfg.exscal ≤ 1 / 2) (hb : cfg.b = cfg.δ)
    (hthr : (fibreCountConstant bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀) :
    ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
        ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) := by
  classical
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hCba : (1 : NNReal) ≤ NonSlab.bodyAngleConstant bd.C₀ :=
    NonSlab.one_le_bodyAngleConstant hC₀bd
  set ρk : NNReal := Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k with hρk
  set ρ2 : NNReal := cfg.rho2 with hρ2
  -- the non-slab hypothesis at `b = δ`
  have hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := by
    rw [hb]
    unfold r₁
    rw [← NNReal.rpow_add hδ0.ne']
    calc cfg.δ = cfg.δ ^ (1 : ℝ) := (NNReal.rpow_one _).symm
      _ ≤ cfg.δ ^ (cfg.exscal + cfg.exscal) :=
        NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  obtain ⟨hwin, -⟩ := rho2_range cfg hδ0 hδ1 hexscal hnotslab
  have hwinb : ρ2 ∈ Set.Icc (cfg.δ ^ (1 - cfg.exscalb)) (cfg.δ ^ cfg.exscalb) := by
    rw [← cfg.hscale]; exact hwin
  have hρ20 : 0 < ρ2 := lt_of_lt_of_le (NNReal.rpow_pos hδ0) hwinb.1
  have hρk1 : ρk ≤ 1 := Tube.gridScale_le_one hδ1 _ _
  have hρ2ρk : ρ2 ≤ ρk := (rho2_le_rho2Star cfg hC₀bd).trans hge
  -- the parent datum
  obtain ⟨sPar, hsub, -, -, hretE, ⟨Cpar, hCpar1, hCparE, ⟨𝒰par⟩⟩, hcount⟩ := cfg.rho_count
  obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := hcount ρ2 hwinb
  have hCpar : Cpar ≤ cfg.δ ^ (-cfg.η) := le_rpow_neg_of_coe_le hδ0 hCparE
  have hret : cfg.δ ^ (2 * cfg.η) * (sPar.card : NNReal) ≤ (cfg.s.card : NNReal) :=
    mul_le_of_coe_mul_le hδ0 hretE
  have hne : sPar.Nonempty := by
    rcases tρ.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
    · exfalso
      simp only [Finset.card_empty, Nat.cast_zero] at hcard
      exact absurd hcard (not_le.2 (Real.rpow_pos_of_pos (NNReal.coe_pos.2 hρ20) _))
    · obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
      exact ⟨i₀, hi₀⟩
  -- step 1: the count on the parent's nodes
  have hstep1 : (tρ.card : ℝ) ≤
      (Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ)) : ℝ)
        * ((𝒰par.cover.indexSet k).card : ℝ) :=
    card_count_le_mul_card_indexSet 𝒰par hk hρ20 (by exact_mod_cast hρ2ρk)
      (by exact_mod_cast hρk1) tρ Tρ hED hused
  -- step 2: the parent's nodes against the family's
  have hstep2 : cfg.δ ^ (2 * cfg.η) * ((𝒰par.cover.indexSet k).card : NNReal)
      ≤ Cpar ^ 3 * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) :=
    card_indexSet_parent_le 𝒰par cfg.splitHierarchy hsub hne hk hret
  -- the ratio bound `32 ρ_k/ρ₂ ≤ 64 C_bodyAngle δ^{-η}`
  set A : NNReal := fibreCountConstant bd.C₀ with hA
  set R : NNReal := 64 * NonSlab.bodyAngleConstant bd.C₀ * cfg.δ ^ (-cfg.η) with hR
  have hρ20R : (0 : ℝ) < (ρ2 : ℝ) := NNReal.coe_pos.2 hρ20
  rw [rho2Star] at hle
  have hNN : 32 * ρk ≤ R * ρ2 := by
    calc 32 * ρk
        ≤ 32 * (cfg.δ ^ (-cfg.η) * (2 * NonSlab.bodyAngleConstant bd.C₀ * ρ2)) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = R * ρ2 := by rw [hR]; ring
  have hratio : 32 * (ρk : ℝ) / (ρ2 : ℝ) ≤ (R : ℝ) := by
    rw [div_le_iff₀ hρ20R]
    have := NNReal.coe_le_coe.2 hNN
    push_cast at this
    linarith [this]
  have hratio1 : (1 : ℝ) ≤ 32 * (ρk : ℝ) / (ρ2 : ℝ) := by
    rw [le_div_iff₀ hρ20R]
    have : (ρ2 : ℝ) ≤ (ρk : ℝ) := by exact_mod_cast hρ2ρk
    linarith
  -- the powers of `δ^{-η}`
  have hpow3 : (cfg.δ ^ (-cfg.η)) ^ (3 : ℕ) = cfg.δ ^ (-((3 : ℝ) * cfg.η)) := by
    rw [← NNReal.rpow_natCast (cfg.δ ^ (-cfg.η)) 3, ← NNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have hpow12 : (cfg.δ ^ (-cfg.η)) ^ (12 : ℕ) = cfg.δ ^ (-((12 : ℝ) * cfg.η)) := by
    rw [← NNReal.rpow_natCast (cfg.δ ^ (-cfg.η)) 12, ← NNReal.rpow_mul]
    congr 1
    push_cast
    ring
  -- the packing constant against `A δ^{-12η}`
  have hPle : Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ))
      ≤ A * cfg.δ ^ (-((12 : ℝ) * cfg.η)) := by
    refine (essDistinctTubesInSelfDilate_C_le hratio1).trans ?_
    have hR12 : (32 * (ρk : ℝ) / (ρ2 : ℝ)).toNNReal ^ 12 ≤ R ^ 12 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 12
      have h := Real.toNNReal_le_toNNReal hratio
      rwa [Real.toNNReal_coe] at h
    refine le_trans (mul_le_mul_of_nonneg_left hR12 (by positivity)) ?_
    rw [hR, hA, fibreCountConstant, mul_pow, ← mul_assoc, hpow12]
  have hc0 : (0 : NNReal) < cfg.δ ^ (2 * cfg.η) := NNReal.rpow_pos hδ0
  have hIdx : ((𝒰par.cover.indexSet k).card : NNReal)
      ≤ Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
          ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by
    have hinv : cfg.δ ^ (-((2 : ℝ) * cfg.η)) = (cfg.δ ^ (2 * cfg.η))⁻¹ := by
      rw [← NNReal.rpow_neg]
    calc ((𝒰par.cover.indexSet k).card : NNReal)
        = (cfg.δ ^ (2 * cfg.η))⁻¹ * (cfg.δ ^ (2 * cfg.η)
            * ((𝒰par.cover.indexSet k).card : NNReal)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
      _ ≤ (cfg.δ ^ (2 * cfg.η))⁻¹ * (Cpar ^ 3
            * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal)) := by gcongr
      _ = Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
            ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by rw [hinv]; ring
  -- assemble in `NNReal`
  have hCpar3 : Cpar ^ 3 ≤ cfg.δ ^ (-((3 : ℝ) * cfg.η)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) hCpar 3) ?_
    rw [hpow3]
  have hadd : cfg.δ ^ (-((12:ℝ) * cfg.η)) * (cfg.δ ^ (-((3:ℝ) * cfg.η))
      * cfg.δ ^ (-((2:ℝ) * cfg.η))) = cfg.δ ^ (-((17:ℝ) * cfg.η)) := by
    rw [← NNReal.rpow_add hδ0.ne', ← NNReal.rpow_add hδ0.ne']
    congr 1
    ring
  refine ⟨A * cfg.δ ^ (-((17 : ℝ) * cfg.η)), ?_, ?_⟩
  · have hAle : A ≤ cfg.δ ^ (-cfg.η) := le_rpow_neg_of_coe_le hδ0 hthr
    have : A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) ≤ cfg.δ ^ (-(18 * cfg.η)) := by
      refine le_trans (mul_le_mul_of_nonneg_right hAle (by positivity)) ?_
      rw [← NNReal.rpow_add hδ0.ne']
      exact le_of_eq (by congr 1; ring)
    calc ((A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) : NNReal) : ENNReal)
        ≤ ((cfg.δ ^ (-(18 * cfg.η)) : NNReal) : ENNReal) := by exact_mod_cast this
      _ = (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) :=
          ENNReal.coe_rpow_of_ne_zero hδ0.ne' _
  · have hkeyN : Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ))
        * ((𝒰par.cover.indexSet k).card : NNReal)
        ≤ A * cfg.δ ^ (-((17 : ℝ) * cfg.η))
          * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by
      calc Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ))
            * ((𝒰par.cover.indexSet k).card : NNReal)
          ≤ (A * cfg.δ ^ (-((12 : ℝ) * cfg.η)))
              * (Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
                ((cfg.splitHierarchy.cover.indexSet k).card : NNReal)) := by
            exact mul_le_mul' hPle hIdx
        _ ≤ (A * cfg.δ ^ (-((12 : ℝ) * cfg.η)))
              * (cfg.δ ^ (-((3 : ℝ) * cfg.η)) * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
                ((cfg.splitHierarchy.cover.indexSet k).card : NNReal)) := by
            gcongr
        _ = A * (cfg.δ ^ (-((12:ℝ) * cfg.η)) * (cfg.δ ^ (-((3:ℝ) * cfg.η))
              * cfg.δ ^ (-((2:ℝ) * cfg.η))))
              * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by ring
        _ = A * cfg.δ ^ (-((17 : ℝ) * cfg.η))
              * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by rw [hadd]
    have hkeyR : (Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ)) : ℝ)
        * ((𝒰par.cover.indexSet k).card : ℝ)
        ≤ ((A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) : NNReal) : ℝ)
          * ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) := by
      have := NNReal.coe_le_coe.2 hkeyN
      push_cast at this ⊢
      linarith [this]
    linarith [hcard, hstep1, hkeyR]

/-! ### The `∀ᶠ δ` form: conjunct 5 of `SideDataObligations` with the licensed constant -/

/-- **R17 discharged, in the shape of conjunct 5.** This is conjunct 5 of
`Kakeya.VeryNotSticky.SideDataObligations` verbatim except that the over-strong `δ`-free constant
`(2 C_{lem:ml2bodyAngle}(C₀))²` of the boundary `Prop` is replaced by the quantified form `∃ Ccnt ≤ δ^{-M η}`, at the exponent `M = 18` measured here.

The one threshold on `δ` is the absorption of the `δ`-free
`Kakeya.VeryNotSticky.fibreCountConstant C₀bd` into a single `η`, of exactly the shape the
configuration's own `aScaleData_absorb`/`coarseLoss_absorb` already use
(`Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg`); `hexscal` and `hC₀bd` are parameter
facts the residue supplies from `params` and T4's constants. -/
theorem eventually_exists_fibreScaleCount (exscal η : ℝ) (C₀bd : NNReal) (hC₀bd : 1 ≤ C₀bd)
    (hexscal : exscal ≤ 1 / 2) (hη : 0 < η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.b = cfg.δ → bd.C₀ = C₀bd →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) := by
  filter_upwards [eventually_ennreal_le_rpow_neg
    (K := ((fibreCountConstant C₀bd : NNReal) : ENNReal)) ENNReal.coe_ne_top hη] with δ hδthr
  intro cfg bd hδ hη' hex hb hC₀ k hk hge hle
  refine exists_fibreScaleCount_of_rhoParentData cfg bd (by rw [hC₀]; exact hC₀bd)
    (by rw [hex]; exact hexscal) hb ?_ hk hge hle
  rw [hC₀, hδ, hη']
  exact hδthr

/-! ### The as-written constant, and why the repair is a weakening

The clause as it stands in the boundary `Prop` (`SetupSideData.lean`, conjunct 5) carries the
`δ`-free constant `(2 C_{lem:ml2bodyAngle}(C₀))²`, which does not cover the transport losses. The two facts below are the compiled record of the relation between the
two forms: for every small `δ` the reachable threshold `δ^{-18η}` **exceeds** the as-written
constant, and the as-written clause **implies** the repaired one. So the requested repair is a
weakening of the constant and of nothing else; it is not derivable in the other direction from
the configuration's data (the scale comparison costs `(ρ_k/ρ₂)^{2n} δ^{-2nη}`, gap 3
the essentially-distinct/bounded-overlap comparison, and F12b's own clauses cost `Cpar³ ≤ δ^{-3η}`
and the retention `δ^{-2η}` — four independent `δ^{-O(η)}` factors, none of which a `δ`-free
constant admits). -/

/-- **The reachable threshold dominates the as-written constant** for every small `δ`: the
repaired clause is the weaker of the two, so the quantified estimate is weaker. -/
theorem eventually_asWritten_constant_le (C₀ : NNReal) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0,
      (((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal)) ^ 2
        ≤ (δ : ENNReal) ^ (-(18 * η)) := by
  have h18 : (0 : ℝ) < 18 * η := by linarith
  filter_upwards [eventually_ennreal_le_rpow_neg
    (K := (((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal)) ^ 2)
    (by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_ne_top) h18] with δ hδ
  exact hδ

/-- **The as-written clause implies the repaired one.** Nothing the boundary `Prop`'s conjunct 5
promises is lost by the constant repair; only the constant moves. -/
theorem exists_fibreScaleCount_of_asWritten (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {k : ℕ}
    (hcnt : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ℝ) ^ 2 *
        ((cfg.splitHierarchy.cover.indexSet k).card : ℝ))
    (hthr : (((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal)) ^ 2
      ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η))) :
    ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
        ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) := by
  refine ⟨(2 * NonSlab.bodyAngleConstant bd.C₀) ^ 2, ?_, ?_⟩
  · rw [ENNReal.coe_pow]; exact hthr
  · push_cast
    exact hcnt

/-! ### Fibre-scale count with an explicit loss constant

The following theorem keeps the parameter `ϱ` fixed and supplies
`∃ Ccnt ≤ δ^{-18η}` for the hierarchy count. The loss accounts for
the parent-to-family and cross-scale comparisons.
-/
theorem sideDataObligations_conjunct5_after (exscal ϱ η : ℝ) (C₀bd : NNReal)
    (hC₀bd : 1 ≤ C₀bd) (hexscal : exscal ≤ 1 / 2) (hη : 0 < η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) := by
  filter_upwards [eventually_exists_fibreScaleCount.{u} exscal η C₀bd hC₀bd hexscal hη]
    with δ h
  intro cfg bd hδ hη' hex _hϱ hb hC₀ k hk hge hle
  exact h cfg bd hδ hη' hex hb hC₀ k hk hge hle

/-- The fifth component of `SideDataObligations`, stated explicitly.
It quantifies over exact `Tube.UniformTubeSet` hierarchies with
`1 ≤ C ≤ δ^{-η}` and compares the count at a grid level within the
prescribed interval around `ρ₂*`.

A count for a loose hierarchy is a distinct conditional statement:
`sideDataObligations_conjunct5_of_looseRhoParent` uses
`LooseRhoParentData`. Its directional bound is `ρ_k/4`, whereas exact
containment alone gives a bound of order `6ρ_k`; the two parent data
cannot be interchanged without an additional argument. -/
example {β exscal ϱ η τ τ' : ℝ} {C₀bd Cbias CF Cdil c₁ Cg : NNReal} {D : ℕ}
    (h : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D)
    (h5 : ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ C : NNReal, 1 ≤ C → (C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
      ∀ 𝒰s : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C,
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((𝒰s.cover.indexSet k).card : ℝ)) :
    SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h5⟩

end Kakeya.VeryNotSticky
