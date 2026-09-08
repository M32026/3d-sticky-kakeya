/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.MultiScaleFac.Branching

/-!
# Fibre counts at inflated containers

`Kakeya.MultiScaleFac.Branching` counts leaves and nodes only at *matched* scales: the container
radius and the uniformity scale are the same variable.  Every composition step of GWZ Lemma 7.7
needs the counts at a boundedly *inflated* container, because a node of scale `σ` only sits inside
the `4σ`-rescale of the `δ`-tubes it carries, and a node of the next scale down costs a further
inflation.  `Tube.IsUniformAtScale.boundedOverlap` quantifies over tubes *at the uniformity
scale*, so it does not apply to a `6σ`-container directly.

This file supplies the missing comparisons.  The geometric input is a net: a family of `δ`-tubes
contained in one common `r`-tube has, for every `ε > 0`, an `ε`-net in the `L¹` endpoint metric
of dimensional cardinality (`exists_net_of_le_common_tube`).  This is `Tube.grid_overlap`'s
packing argument (`Tube.endpoints_close_of_body_le` followed by
`Tube.card_le_of_L1_separated_in_box`) isolated as a reusable statement.  Two consequences:

* `exists_gapFibre_cover_of_inflated` — a fibre at a container of radius `θ ≤ 6σa` is covered by
  `C(n)` of the tight gap fibres `s_{σb∣σa}(i₂)`, so a hypothesis quantified over every anchor
  `i₂ ∈ s` may be applied inside a fattened container at a dimensional cost;
* `branchingN_le_mul_card_fibreIndex_of_comparable` — conversely `N_k ≤ C(n) · Cu² · Cf ·` the
  leaf count of the *tight* fibre, where `Cf` is the `ComparableFibreCounts` constant.  The
  comparability hypothesis is exactly what rules out a node whose leaves clump away from every
  tight fibre; without it only the `4 σ k`-inflated bound
  `branchingN_le_mul_card_fibreIndex` is available.

Finally `parent_card_mul_branchingN_le_of_subset` is the incidence double count of
`parent_card_mul_branchingN_le` restricted to a subfamily of nodes together with a leaf set
containing all of their leaves.

Every uniformity hypothesis in this file is the bundle
`Tube.ChainUniformTubeSet s T N σ Cu` together with `1 ≤ Cu` and a level bound
`k ≤ N`; each proof consumes the per-scale reading `ChainUniformTubeSet.uniformAt`, whose constant
is `Cu ^ 2`, and that is why the constants below are powers of `Cu ^ 2` rather than of `Cu`.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **The branching number is carried by the tight fibre.**  If the fibre counts at the chain scale
`σ k` are `Cf`-comparable to each other, then the branching number at that scale is bounded by
`C(n) · Cu² · Cf` times the leaf count of the *tight* fibre `𝕋_{δ∣σ k}[i₀]`, for every `i₀ ∈ s`.
Without comparability only `branchingN_le_mul_card_fibreIndex`, whose container is `4`-inflated. -/
theorem branchingN_le_mul_card_fibreIndex_of_comparable {ι : Type*} {δ Cu Cf : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
    (𝒰 : ChainUniformTubeSet s T N σ Cu) (hCu : 1 ≤ Cu) {k : ℕ} (hk : k ≤ N)
    (hρ : 0 < σ k) (hδρ : 2 * δ ≤ σ k)
    (hcmp : ∀ i₁ ∈ s, ∀ i₂ ∈ s,
      ((fibreIndex s T δ (σ k) i₁).card : NNReal)
        ≤ Cf * ((fibreIndex s T δ (σ k) i₂).card : NNReal))
    {i₀ : ι} (hi₀ : i₀ ∈ s) :
    𝒰.branchingN k
      ≤ fibrePackConst (Module.finrank ℝ E)
          * (Cu ^ 2 * (Cf * ((fibreIndex s T δ (σ k) i₀).card : NNReal)))
      := by
  classical
  set ρ := σ k
  set h : Tube.IsUniformAtScale s T ρ (Cu ^ 2) := 𝒰.uniformAt hCu hk
  set n := Module.finrank ℝ E
  obtain ⟨j, hj, -⟩ := h.exists_le_rescale hi₀
  set V := h.parentTube j
  set F := s.filter (fun i => (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
  have hF_sub_s : F ⊆ s := Finset.filter_subset _ _
  have hρpos : (0 : ℝ) < (ρ : ℝ) := NNReal.coe_pos.mpr hρ
  have h_net : 2 * ((3 * (ρ : ℝ) + (((ρ : ℝ) / 2) / 4)) / (((ρ : ℝ) / 2) / 4))
      ^ (2 * n) ≤ (fibrePackConst n : ℝ) := by
    rw [show (3 * (ρ : ℝ) + (((ρ : ℝ) / 2) / 4)) / (((ρ : ℝ) / 2) / 4) = 25 by
        rw [div_eq_iff (div_ne_zero (div_ne_zero hρpos.ne' two_ne_zero) (by norm_num))]; ring,
      show (fibrePackConst n : ℝ) = 2 * (145 : ℝ) ^ (2 * n) by push_cast [fibrePackConst]; ring]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by norm_num)
  obtain ⟨F', hF'_sub_F, hF'_net, hF'_card⟩ := exists_net_of_le_common_tube F T V
    (fun i hi => (Finset.mem_filter.mp hi).2) (ε := (ρ : ℝ) / 2) (B := (fibrePackConst n : ℝ))
    (hε := half_pos hρpos) (hB := h_net)
  have hδρ' : 2 * (δ : ℝ) ≤ (ρ : ℝ) := mod_cast hδρ
  have hF_cover : F ⊆ F'.biUnion (fun a => fibreIndex s T δ ρ a) := fun i hi => by
    obtain ⟨a, haF', hdist⟩ := hF'_net i hi
    refine Finset.mem_biUnion.mpr ⟨a, haF', ?_⟩
    rw [fibreIndex_self s T ρ a]
    exact Finset.mem_filter.mpr ⟨hF_sub_s hi,
      (Tube.toConvexSpaceBody_rescale_self (T i)).symm.trans_le
        (Tube.rescale_le_rescale_of_endpoint_dist (T i) (T a) (by linarith only [hdist, hδρ']))⟩
  have h_cardF' : (F.card : NNReal) ≤ (fibrePackConst n : NNReal)
      * (Cf * ((fibreIndex s T δ ρ i₀).card : NNReal)) := by
    have h1 : (F.card : NNReal) ≤ ∑ a ∈ F', ((fibreIndex s T δ ρ a).card : NNReal) := by
      rw [← Nat.cast_sum]
      exact Nat.cast_le.mpr ((Finset.card_le_card hF_cover).trans Finset.card_biUnion_le)
    refine h1.trans (le_trans ?_ (mul_le_mul_left
      (NNReal.coe_le_coe.mp (by rw [NNReal.coe_natCast]; exact hF'_card)) _))
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun a ha =>
      hcmp a (Finset.Subset.trans hF'_sub_F hF_sub_s ha) i₀ hi₀
  exact (h.le_mul_card_filter hj).trans
    ((mul_le_mul_right h_cardF' _).trans_eq (mul_left_comm _ _ _))

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The incidence double count on a subfamily of nodes, per-scale form.**
`parent_card_mul_branchingN_le` with the node family restricted to `P ⊆ parent` and the leaf family
restricted to any `L ⊆ s` that already contains every leaf of every node of `P`.  Per-scale form of
`parent_card_mul_branchingN_le_of_subset`. -/
theorem parent_card_mul_branchingN_le_of_subset_atScale {ι : Type*} {δ ρ Cu : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} (h : Tube.IsUniformAtScale s T ρ Cu) (hδρ : δ ≤ ρ)
    (P L : Finset ι) (hP : P ⊆ h.parent) (hL : L ⊆ s)
    (hleaf : ∀ j ∈ P, ∀ i ∈ s,
      (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody → i ∈ L)
    (K : ConvexSpaceBody E) :
    ((P.filter (fun j => (h.parentTube j).toConvexSpaceBody ≤ K)).card : NNReal) * h.branchingN
      ≤ Cu ^ 2 * ((L.filter (fun i => (T i).toConvexSpaceBody ≤ K)).card : NNReal) := by
  classical
  set Q : ι → ι → Prop :=
    fun j i => (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody
  set P_K := P.filter (fun j => (h.parentTube j).toConvexSpaceBody ≤ K) with hPK
  set L_K := L.filter (fun i => (T i).toConvexSpaceBody ≤ K) with hLK
  have h_sL_filter : ∀ j ∈ P_K, s.filter (fun i => Q j i) = L.filter (fun i => Q j i) :=
    fun j hj => by
      have hjP : j ∈ P := Finset.mem_of_mem_filter _ (hPK ▸ hj)
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun hi => ⟨hleaf j hjP i hi.1 hi.2, hi.2⟩, fun hi => ⟨hL hi.1, hi.2⟩⟩
  have hswap : ∑ j ∈ P_K, ((L.filter (fun i => Q j i)).card : NNReal)
      = ∑ i ∈ L, ((P_K.filter (fun j => Q j i)).card : NNReal) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    congr 1
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hlow : (P_K.card : NNReal) * h.branchingN
      ≤ Cu * ∑ j ∈ P_K, ((L.filter (fun i => Q j i)).card : NNReal) := by
    rw [← nsmul_eq_mul, Finset.mul_sum]
    refine Finset.card_nsmul_le_sum _ _ _ fun j hj => ?_
    rw [← h_sL_filter j hj]
    exact h.le_mul_card_filter (hP (Finset.mem_of_mem_filter _ (hPK ▸ hj)))
  have hup : ∑ i ∈ L, ((P_K.filter (fun j => Q j i)).card : NNReal)
      ≤ Cu * (L_K.card : NNReal) := by
    have hzero : ∀ i ∈ L, i ∉ L_K → ((P_K.filter (fun j => Q j i)).card : NNReal) = 0 := by
      intro i hi hiL
      rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun j hj hQji =>
        hiL (Finset.mem_filter.mpr ⟨hi, le_trans hQji (Finset.mem_filter.mp hj).2⟩)
    rw [← Finset.sum_subset (Finset.filter_subset (fun i => (T i).toConvexSpaceBody ≤ K) L) hzero,
      mul_comm Cu (L_K.card : NNReal), ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun i hi => le_trans ?_
      (h.parents_containing_tube_card_le hδρ (T i) (hL (Finset.mem_of_mem_filter i hi)) le_rfl)
    exact Nat.cast_le.mpr (Finset.card_le_card fun j hjf => Finset.mem_filter.mpr
      ⟨hP (Finset.mem_of_mem_filter _ (hPK ▸ (Finset.mem_filter.mp hjf).1)),
        (Finset.mem_filter.mp hjf).2⟩)
  refine hlow.trans ?_
  rw [hswap, sq, mul_assoc]
  exact mul_le_mul_right hup _

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The incidence double count on a subfamily of nodes.**  `parent_card_mul_branchingN_le` with
the node family restricted to `P ⊆ parent` and the leaf family restricted to any `L ⊆ s` that
already contains every leaf of every node of `P`.  The outer square of `(Cu ^ 2) ^ 2` comes from
the per-scale reading `ChainUniformTubeSet.uniformAt`, whose own constant is `Cu ^ 2`. -/
theorem parent_card_mul_branchingN_le_of_subset {ι : Type*} {δ Cu : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
    (𝒰 : ChainUniformTubeSet s T N σ Cu) (hCu : 1 ≤ Cu) {k : ℕ} (hk : k ≤ N)
    (hδρ : δ ≤ σ k)
    (P L : Finset ι) (hP : P ⊆ 𝒰.cover.indexSet k) (hL : L ⊆ s)
    (hleaf : ∀ j ∈ P, ∀ i ∈ s,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody → i ∈ L)
    (K : ConvexSpaceBody E) :
    ((P.filter (fun j => (𝒰.cover.tube k j).toConvexSpaceBody ≤ K)).card : NNReal)
        * 𝒰.branchingN k
      ≤ (Cu ^ 2) ^ 2 * ((L.filter (fun i => (T i).toConvexSpaceBody ≤ K)).card : NNReal) :=
  parent_card_mul_branchingN_le_of_subset_atScale (𝒰.uniformAt hCu hk) hδρ P L hP hL hleaf K

/-! ### Anchor-graded fibre counts -/

/-- **Anchor-graded fibre counts follow from uniformity at the finer scale, per-scale form.**  For a
family that is `Cu`-uniform at the single scale `ρ`, enlarging the anchor from `ρ` to any `ρ' ≥ ρ`
costs at most `C(n) · Cu³ · (ρ'/ρ)^{2n}`, provided the right-hand fibre is read at the `8`-inflated
anchor `8ρ`.  Per-scale form of `anchorGraded_of_isUniformAtScale`. -/
theorem anchorGraded_of_isUniformAtScale_atScale {ι : Type*} {δ σ ρ ρ' Cu : NNReal}
    {s : Finset ι} {T : ι → Tube δ E}
    (h : Tube.IsUniformAtScale s T ρ Cu) (hρ : 0 < ρ) (hδσ : δ ≤ σ) (hσρ : 2 * σ ≤ ρ)
    (hρρ' : ρ ≤ ρ') {i₀ : ι} (hi₀ : i₀ ∈ s) :
    ((fibreIndex s T σ ρ' i₀).card : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ) ^ 3
          * ((ρ' : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E)
          * ((fibreIndex s T σ (8 * ρ) i₀).card : ℝ) := by
  classical
  set C : ℝ := ((fibreIndex s T σ (8 * ρ) i₀).card : ℝ) with hC
  have hσle4ρ : σ ≤ 4 * ρ :=
    (le_mul_of_one_le_left zero_le one_le_two).trans
      (hσρ.trans (le_mul_of_one_le_left zero_le (by norm_num)))
  obtain ⟨A, -, hcardA, hcover⟩ :=
    exists_gapFibre_cover_of_ratio (s := s) (T := T) hρ hδσ hσρ hρρ' i₀
  calc
    ((fibreIndex s T σ ρ' i₀).card : ℝ)
        ≤ ∑ i₂ ∈ A, ((fibreIndex s T σ ρ i₂).card : ℝ) := by
          rw [← Nat.cast_sum]
          exact Nat.cast_le.mpr ((Finset.card_le_card
            ((fibreIndex_subset_of_member_le hδσ i₀).trans
              (fun i hi => Finset.mem_biUnion.mpr (hcover i hi)))).trans Finset.card_biUnion_le)
    _ ≤ (A.card : ℝ) * ((Cu : ℝ) ^ 3 * C) := by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul A _ _ fun i₂ _ => ?_
        rw [hC]
        exact_mod_cast comparableFibreCounts_of_isUniformAtScale_atScale h hδσ hσle4ρ i₂ hi₀
    _ ≤ (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * ((ρ' : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E))
          * ((Cu : ℝ) ^ 3 * C) :=
        mul_le_mul_of_nonneg_right hcardA
          (hC ▸ mul_nonneg (pow_nonneg Cu.coe_nonneg 3) (Nat.cast_nonneg _))
    _ = 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ) ^ 3
          * ((ρ' : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E) * C := by ring

end MultiScaleFac

end Kakeya
