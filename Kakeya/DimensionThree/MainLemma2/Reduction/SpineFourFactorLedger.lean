/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWiring
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreFinal

/-!
# The four-way split's ledger: four factors, four levels, one telescoping

 and the refined source l.4445-4452 cut the multiplicity at
**four** levels `a < p < b < leaf`, not three: an outer `ρ_a`-family, a `ρ_p/(2ρ_a)`-family in the
normalised `a`-cell (the **new-parent** factor), a `ρ_b/(2ρ_p)`-family in the normalised `p`-cell
(the **middle**, VNS, factor) and the inner `δ/(2ρ_b)`-family; and
`n_a n_p n_b n_i ≤ 16 #𝕊'` (`eq:ml2-four-cardinalities`, l.4451).

This file is the tree's version of that bookkeeping, and it is entirely **additive**: not one
existing declaration is touched.  Each theorem is the three-factor one with one more link in the
chain, and the map's claim that "there is no new estimate" is what the proofs show — the level-`p`
link is `Kakeya.ML2Reduction.branchingN_mul_card_le_of_tube_le` applied a **second** time.

* `Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_two_mul_card_le` — the cardinality
  telescoping, `Cu ^ 8` in place of `Cu ^ 5`;
* `Kakeya.ML2Core.card_four_factor_le` — the same in `ENNReal`, with the fine fibre read inside the
  node-restricted family;
* `Kakeya.ML2Core.multiplicity_le_of_four_factors` — the arithmetic, at the budget
  `g ≤ gm - εf - εp - εc - κ`;
* `Kakeya.ML2Core.mass_gain_of_four_factors` — the estimate at four factors;
* `Kakeya.ML2Core.spineScaleLoss_prod3_le` — three `spineScaleLoss` factors absorbed into
  `Cε ^ 3 · δ ^ (-15 ε)`, i.e. `ε := κ' / 30` where the two-factor ledger runs at `κ' / 20`

**Level pairs, stated once and carried in every docstring below.**  `F1` is the leaf fibre of a
level-`b` node; `F2` is the `(p, b)` fibre — the middle factor's, the pair the source's
`δ̃ = ρ_b/(2ρ_p)` names (l.4506); `F3` is the `(a, p)` fibre — the new-parent factor's (l.4448);
`F4` is the retained level-`a` family.  No shading is read anywhere in this file: these are node
counts and abstract multiplicities.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {δ : ℝ≥0} {ι : Type u} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0} {Cu : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **Cardinality multiplicativity across the THREE levels `a ≤ p ≤ b` of the §9 hierarchy** —
the tree's `eq:ml2-four-cardinalities` (l.4451).

`Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le` with one more link.  The four
index sets are the leaf fibre of `jτ`, the `(p, b)` fibre inside `tτ'`, the `(a, p)` fibre inside
`tp'`, and the retained level-`a` family `tθ'`; their cardinalities multiply to at most
`Cu ^ 8 · |s|`.

The proof is the three-factor telescoping with
`Kakeya.ML2Reduction.branchingN_mul_card_le_of_tube_le` applied **twice** — once at `(p, b)` and
once at `(a, p)` — which is exactly the map's claim that the four-way split introduces no new
estimate.  `Cu ^ 8` is not claimed optimal; as at `Cu ^ 5`, nothing downstream reads the exponent.

**Level pairs:** `(p, b)` for the middle fibre, `(a, p)` for the new-parent fibre.  No shading. -/
theorem card_class_mul_card_coarseFibre_two_mul_card_le
    (𝒰 : Tube.ChainUniformTubeSet s T N σ Cu)
    {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) (haN : a ≤ N) (hpN : p ≤ N) (hbN : b ≤ N)
    {tτ' tp' tθ' : Finset ι} (htτ : tτ' ⊆ activeNodes 𝒰.cover b)
    (htp : tp' ⊆ activeNodes 𝒰.cover p) (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jp jθ : ι} (hjτ : jτ ∈ 𝒰.cover.indexSet b) :
    (({i ∈ s | 𝒰.cover.assign b i = jτ}).card : ℝ≥0)
        * (({j ∈ tτ' | coarseNode 𝒰.cover p b j = jp}).card : ℝ≥0)
        * (({k ∈ tp' | coarseNode 𝒰.cover a p k = jθ}).card : ℝ≥0)
        * (tθ'.card : ℝ≥0)
      ≤ Cu ^ 8 * (s.card : ℝ≥0) := by
  classical
  set K₂ : Finset ι := {j ∈ tτ' | coarseNode 𝒰.cover p b j = jp} with hK₂
  set K₃ : Finset ι := {k ∈ tp' | coarseNode 𝒰.cover a p k = jθ} with hK₃
  -- the `(p, b)` fibre: level-`b` nodes inside the level-`p` node `jp`
  have hK₂sub : K₂ ⊆ 𝒰.cover.indexSet b := fun j hj =>
    activeNodes_subset 𝒰.cover b (htτ (Finset.mem_filter.mp hj).1)
  have hK₂le : ∀ j ∈ K₂, (𝒰.cover.tube b j).toConvexSpaceBody
      ≤ (𝒰.cover.tube p jp).toConvexSpaceBody := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have := tube_le_coarseNode 𝒰.cover hpb hbN (htτ hj'.1)
    rwa [hj'.2] at this
  -- the `(a, p)` fibre: level-`p` nodes inside the level-`a` node `jθ`
  have hK₃sub : K₃ ⊆ 𝒰.cover.indexSet p := fun k hk =>
    activeNodes_subset 𝒰.cover p (htp (Finset.mem_filter.mp hk).1)
  have hK₃le : ∀ k ∈ K₃, (𝒰.cover.tube p k).toConvexSpaceBody
      ≤ (𝒰.cover.tube a jθ).toConvexSpaceBody := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    have := tube_le_coarseNode 𝒰.cover hap hpN (htp hk'.1)
    rwa [hk'.2] at this
  -- the four brackets
  have h₁ : (({i ∈ s | 𝒰.cover.assign b i = jτ}).card : ℝ≥0) ≤ Cu * 𝒰.branchingN b := by
    have h := 𝒰.card_class_le b hbN jτ hjτ
    simpa [Tube.coverClass] using h
  have h₂ : 𝒰.branchingN b * (K₂.card : ℝ≥0) ≤ Cu ^ 3 * 𝒰.branchingN p :=
    branchingN_mul_card_le_of_tube_le 𝒰 hpN hbN hK₂sub hK₂le
  have h₃ : 𝒰.branchingN p * (K₃.card : ℝ≥0) ≤ Cu ^ 3 * 𝒰.branchingN a :=
    branchingN_mul_card_le_of_tube_le 𝒰 haN hpN hK₃sub hK₃le
  have h₄ : 𝒰.branchingN a * (tθ'.card : ℝ≥0) ≤ Cu * (s.card : ℝ≥0) :=
    branchingN_mul_card_le_subset_indexSet 𝒰 haN htθ
  calc (({i ∈ s | 𝒰.cover.assign b i = jτ}).card : ℝ≥0) * (K₂.card : ℝ≥0) * (K₃.card : ℝ≥0)
        * (tθ'.card : ℝ≥0)
      ≤ (Cu * 𝒰.branchingN b) * (K₂.card : ℝ≥0) * (K₃.card : ℝ≥0) * (tθ'.card : ℝ≥0) := by
        exact mul_le_mul' (mul_le_mul' (mul_le_mul' h₁ le_rfl) le_rfl) le_rfl
    _ = Cu * (𝒰.branchingN b * (K₂.card : ℝ≥0)) * (K₃.card : ℝ≥0) * (tθ'.card : ℝ≥0) := by ring
    _ ≤ Cu * (Cu ^ 3 * 𝒰.branchingN p) * (K₃.card : ℝ≥0) * (tθ'.card : ℝ≥0) := by
        exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl h₂) le_rfl) le_rfl
    _ = Cu ^ 4 * (𝒰.branchingN p * (K₃.card : ℝ≥0)) * (tθ'.card : ℝ≥0) := by ring
    _ ≤ Cu ^ 4 * (Cu ^ 3 * 𝒰.branchingN a) * (tθ'.card : ℝ≥0) := by
        exact mul_le_mul' (mul_le_mul' le_rfl h₃) le_rfl
    _ = Cu ^ 7 * (𝒰.branchingN a * (tθ'.card : ℝ≥0)) := by ring
    _ ≤ Cu ^ 7 * (Cu * (s.card : ℝ≥0)) := by exact mul_le_mul' le_rfl h₄
    _ = Cu ^ 8 * (s.card : ℝ≥0) := by ring

end Kakeya.ML2Reduction

namespace Kakeya.ML2Core

universe u

/-! ## The arithmetic: four factors against one cardinality bound -/

/-- **The four-factor multiplicity bound** — `Kakeya.ML2Core.multiplicity_le_of_three_factors`
with the new-parent factor `mp` inserted.

The budget is the condition `hexp` : one more subtracted loss,
`g ≤ gm - εf - εp - εc - κ`.  `εp` is a loss like `εf` and `εc`; only the middle factor gains.
Nothing here is spine-specific and no level pair is visible — the sets have already become the
numbers `Nf, Nm, Np, Nc`. -/
theorem multiplicity_le_of_four_factors
    {δ : NNReal} {mu mf mm mp mc L Cu : ENNReal} {Nf Nm Np Nc N : ℕ} {β εf gm εp εc κ g : ℝ}
    (hδ0 : (δ : ENNReal) ≠ 0) (hδ1 : (δ : ENNReal) ≤ 1) (hβ0 : 0 ≤ β)
    (hsplit : mu ≤ L * mf * mm * mp * mc)
    (hf : mf ≤ (δ : ENNReal) ^ (-εf) * (Nf : ENNReal) ^ β)
    (hm : mm ≤ (δ : ENNReal) ^ gm * (Nm : ENNReal) ^ β)
    (hp : mp ≤ (δ : ENNReal) ^ (-εp) * (Np : ENNReal) ^ β)
    (hc : mc ≤ (δ : ENNReal) ^ (-εc) * (Nc : ENNReal) ^ β)
    (hcard : (Nf : ENNReal) * (Nm : ENNReal) * (Np : ENNReal) * (Nc : ENNReal)
      ≤ Cu * (N : ENNReal))
    (hL : L * Cu ^ β ≤ (δ : ENNReal) ^ (-κ))
    (hexp : g ≤ gm - εf - εp - εc - κ) :
    mu ≤ (δ : ENNReal) ^ g * (N : ENNReal) ^ β := by
  have hδt : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hstep1 : mf * mm * mp * mc
      ≤ (δ : ENNReal) ^ (gm - εf - εp - εc)
        * (((Nf : ENNReal) * (Nm : ENNReal) * (Np : ENNReal) * (Nc : ENNReal)) ^ β) := by
    calc mf * mm * mp * mc
        ≤ ((δ : ENNReal) ^ (-εf) * (Nf : ENNReal) ^ β)
            * ((δ : ENNReal) ^ gm * (Nm : ENNReal) ^ β)
            * ((δ : ENNReal) ^ (-εp) * (Np : ENNReal) ^ β)
            * ((δ : ENNReal) ^ (-εc) * (Nc : ENNReal) ^ β) := by gcongr
      _ = ((δ : ENNReal) ^ (-εf) * (δ : ENNReal) ^ gm * (δ : ENNReal) ^ (-εp)
              * (δ : ENNReal) ^ (-εc))
            * ((Nf : ENNReal) ^ β * (Nm : ENNReal) ^ β * (Np : ENNReal) ^ β
              * (Nc : ENNReal) ^ β) := by ring
      _ = (δ : ENNReal) ^ (gm - εf - εp - εc)
            * (((Nf : ENNReal) * (Nm : ENNReal) * (Np : ENNReal) * (Nc : ENNReal)) ^ β) := by
          rw [← ENNReal.rpow_add _ _ hδ0 hδt, ← ENNReal.rpow_add _ _ hδ0 hδt,
            ← ENNReal.rpow_add _ _ hδ0 hδt,
            ENNReal.mul_rpow_of_nonneg _ _ hβ0, ENNReal.mul_rpow_of_nonneg _ _ hβ0,
            ENNReal.mul_rpow_of_nonneg _ _ hβ0]
          ring_nf
  have hstep2 : (((Nf : ENNReal) * (Nm : ENNReal) * (Np : ENNReal) * (Nc : ENNReal)) ^ β)
      ≤ Cu ^ β * (N : ENNReal) ^ β := by
    calc (((Nf : ENNReal) * (Nm : ENNReal) * (Np : ENNReal) * (Nc : ENNReal)) ^ β)
        ≤ (Cu * (N : ENNReal)) ^ β := ENNReal.rpow_le_rpow hcard hβ0
      _ = Cu ^ β * (N : ENNReal) ^ β := ENNReal.mul_rpow_of_nonneg _ _ hβ0
  calc mu ≤ L * mf * mm * mp * mc := hsplit
    _ = L * (mf * mm * mp * mc) := by ring
    _ ≤ L * ((δ : ENNReal) ^ (gm - εf - εp - εc) * (Cu ^ β * (N : ENNReal) ^ β)) :=
        mul_le_mul' le_rfl (hstep1.trans (mul_le_mul' le_rfl hstep2))
    _ = (L * Cu ^ β) * ((δ : ENNReal) ^ (gm - εf - εp - εc) * (N : ENNReal) ^ β) := by ring
    _ ≤ (δ : ENNReal) ^ (-κ) * ((δ : ENNReal) ^ (gm - εf - εp - εc) * (N : ENNReal) ^ β) := by
        gcongr
    _ = (δ : ENNReal) ^ (gm - εf - εp - εc - κ) * (N : ENNReal) ^ β := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδ0 hδt]
        ring_nf
    _ ≤ (δ : ENNReal) ^ g * (N : ENNReal) ^ β :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hexp) le_rfl

section Card

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {δ : NNReal} {ι : Type u} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
  {Cu : NNReal}

open Classical in
/-- **The four-factor cardinality bound in the shape the arithmetic consumes** — the `Cu ^ 8`
twin of `Kakeya.ML2Core.card_three_factor_le`.

Both moves are the existing ones: `Kakeya.ML2Core.filter_assign_eq_of_mem` reads the fine fibre
inside the node-restricted family, and the cast to `ENNReal` is free.

**Level pairs:** `(p, b)` middle, `(a, p)` new-parent.  No shading. -/
theorem card_four_factor_le (𝒰 : Tube.ChainUniformTubeSet s T N σ Cu)
    {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) (haN : a ≤ N) (hpN : p ≤ N) (hbN : b ≤ N)
    {t₁ tτ' tp' tθ' : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htp : tp' ⊆ ML2Reduction.activeNodes 𝒰.cover p) (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jp jθ : ι} (hjτ : jτ ∈ t₁) :
    ((({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i = jτ}).card : ENNReal))
        * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover p b j = jp}).card : ENNReal))
        * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover a p k = jθ}).card : ENNReal))
        * ((tθ'.card : ENNReal))
      ≤ ((Cu ^ 8 : NNReal) : ENNReal) * (s.card : ENNReal) := by
  have hmem : jτ ∈ 𝒰.cover.indexSet b :=
    ML2Reduction.activeNodes_subset 𝒰.cover b (ht₁ hjτ)
  have hW6 := ML2Reduction.card_class_mul_card_coarseFibre_two_mul_card_le 𝒰 hap hpb haN hpN hbN
    htτ htp htθ (jp := jp) (jθ := jθ) hmem
  rw [filter_assign_eq_of_mem s (𝒰.cover.assign b) t₁ hjτ]
  exact_mod_cast hW6

end Card

/-! ## the estimate at four factors -/

section Assembled

variable {δ : NNReal} {ι : Type u} {s : Finset ι}
  {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Nn : ℕ} {σ : ℕ → NNReal} {Cu : NNReal}

open Classical in
/-- **the estimate at four factors** — `Kakeya.ML2Core.mass_gain_of_three_factors` with the new-parent
factor.  Every index set is written as the four-way split produces it, so no adapter stands
between the split and this row.

**Family/shading:** the family `(s, V)` under the hierarchy `𝒰`; the four multiplicities are read
on the shadings `Y'`, `Yτ'`, `Yp`, `Yθ` the split produces.
**Level pairs:** fine `b → leaf`; middle `(p, b)`; new parent `(a, p)`; outer level `a`. -/
theorem mass_gain_of_four_factors
    (𝒰 : Tube.ChainUniformTubeSet s (fun i ↦ (V i).toTube) Nn σ Cu)
    {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) (haN : a ≤ Nn) (hpN : p ≤ Nn) (hbN : b ≤ Nn)
    {t₁ tτ' tp' tθ' : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htp : tp' ⊆ ML2Reduction.activeNodes 𝒰.cover p) (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jp jθ : ι} (hjτ : jτ ∈ t₁)
    {Yτ' : ι → ShadedTube (σ b) (EuclideanSpace ℝ (Fin 3))}
    {Yp : ι → ShadedTube (σ p) (EuclideanSpace ℝ (Fin 3))}
    {Yθ : ι → ShadedTube (σ a) (EuclideanSpace ℝ (Fin 3))}
    {Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {L : ENNReal} {β εf gm εp εc κ g : ℝ}
    (hδ0 : (δ : ENNReal) ≠ 0) (hδ1 : (δ : ENNReal) ≤ 1) (hβ0 : 0 ≤ β)
    (hprod : ShadedBody.multiplicity ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i ↦ (V i).toShadedBody)
        ≤ L
          * ShadedBody.multiplicity
              ({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
          * ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover p b j = jp} : Finset ι)
              (fun j ↦ (Yτ' j).toShadedBody)
          * ShadedBody.multiplicity
              ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover a p k = jθ} : Finset ι)
              (fun k ↦ (Yp k).toShadedBody)
          * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody))
    (hfine : ShadedBody.multiplicity
          ({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εf)
          * ((({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β)
    (hmid : ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover p b j = jp} : Finset ι)
          (fun j ↦ (Yτ' j).toShadedBody)
        ≤ (δ : ENNReal) ^ gm
          * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover p b j = jp}
                : Finset ι)).card : ENNReal) ^ β)
    (hpar : ShadedBody.multiplicity
          ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover a p k = jθ} : Finset ι)
          (fun k ↦ (Yp k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εp)
          * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover a p k = jθ}
                : Finset ι)).card : ENNReal) ^ β)
    (hcoarse : ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β)
    (hL : L * (((Cu ^ 8 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-κ))
    (hexp : g ≤ gm - εf - εp - εc - κ) :
    ∑ i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (V i).shade
      ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
        * volume (⋃ i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι), (V i).shade) := by
  refine sum_shade_le_of_multiplicity_le' V ?_
  exact multiplicity_le_of_four_factors hδ0 hδ1 hβ0 hprod hfine hmid hpar hcoarse
    (card_four_factor_le 𝒰 hap hpb haN hpN hbN ht₁ htτ htp htθ (jp := jp) (jθ := jθ) hjτ) hL hexp

end Assembled

/-! ## The third `spineScaleLoss`, and the collapse control -/

/-- **Three `Kakeya.ML2Reduction.spineScaleLoss` factors absorbed into one `δ`-power.**

`Kakeya.ML2Core.spineScaleLoss_prod_le` absorbs two into `Cε ² · δ ^ (-10 ε)`; the four-way split
threads a **third**, at the genuine-parent scale, and three absorb into `Cε ³ · δ ^ (-15 ε)`.
 condition L3: the ledger that ran at `ε := κ' / 20` to reach `δ ^ (-κ')`
runs at **`ε := κ' / 30`**.

**Family/shading:** none — this is the loss constant of the multiplicity estimate.  The three
scales are the leaf scale `δ`, the fine node scale `σ₁ = ρ_b` and the parent node scale
`σ₂ = ρ_p`; only `δ ≤ σᵢ ≤ 1` is used, so the two node scales may be given in either order. -/
theorem spineScaleLoss_prod3_le {n : ℕ} {δ σ₁ σ₂ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδσ₁ : δ ≤ σ₁) (hσ₁1 : σ₁ ≤ 1) (hδσ₂ : δ ≤ σ₂) (hσ₂1 : σ₂ ≤ 1)
    {n₁ n₂ n₃ : ℕ} (h1 : 0 < n₁) (h2 : 0 < n₂) (h3 : 0 < n₃)
    (hn1 : (n₁ : NNReal) ≤ δ ^ (-(4 : ℝ))) (hn2 : (n₂ : NNReal) ≤ δ ^ (-(4 : ℝ)))
    (hn3 : (n₃ : NNReal) ≤ δ ^ (-(4 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) {Cε : NNReal}
    (hCε : ∀ N : ℕ, 0 < N → ∀ d : NNReal, 0 < d → d ≤ 1 → ∀ c : NNReal, 1 ≤ c →
      ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C n N d c
        ≤ Cε * c ^ n * d ^ (-ε) * (N : NNReal) ^ ε) :
    ML2Reduction.spineScaleLoss n n₁ δ * ML2Reduction.spineScaleLoss n n₂ σ₁
        * ML2Reduction.spineScaleLoss n n₃ σ₂
      ≤ Cε ^ 3 * δ ^ (-(15 * ε)) := by
  have hσ₂0 : 0 < σ₂ := lt_of_lt_of_le hδ0 hδσ₂
  have h12 := spineScaleLoss_prod_le (n := n) hδ0 hδ1 hδσ₁ hσ₁1 h1 h2 hn1 hn2 hε hCε
  have e3 : ML2Reduction.spineScaleLoss n n₃ σ₂ ≤ Cε * σ₂ ^ (-ε) * ((n₃ : ℕ) : NNReal) ^ ε := by
    simpa [ML2Reduction.spineScaleLoss] using hCε n₃ h3 σ₂ hσ₂0 hσ₂1 1 le_rfl
  have hpow3 : ((n₃ : ℕ) : NNReal) ^ ε ≤ δ ^ (-(4 * ε)) := by
    calc ((n₃ : ℕ) : NNReal) ^ ε ≤ (δ ^ (-(4 : ℝ))) ^ ε := NNReal.rpow_le_rpow hn3 hε.le
      _ = δ ^ (-(4 * ε)) := by rw [← NNReal.rpow_mul]; ring_nf
  have g3 : σ₂ ^ (-ε) ≤ δ ^ (-ε) := by
    have h := ML2Core.rpow_neg_le_rpow_neg_of_le hδσ₂ hε.le
    rwa [← ENNReal.coe_rpow_of_ne_zero hσ₂0.ne', ← ENNReal.coe_rpow_of_ne_zero hδ0.ne',
      ENNReal.coe_le_coe] at h
  have e3' : ML2Reduction.spineScaleLoss n n₃ σ₂ ≤ Cε * δ ^ (-ε) * δ ^ (-(4 * ε)) :=
    e3.trans (mul_le_mul' (mul_le_mul' le_rfl g3) hpow3)
  calc ML2Reduction.spineScaleLoss n n₁ δ * ML2Reduction.spineScaleLoss n n₂ σ₁
          * ML2Reduction.spineScaleLoss n n₃ σ₂
      ≤ (Cε ^ 2 * δ ^ (-(10 * ε))) * (Cε * δ ^ (-ε) * δ ^ (-(4 * ε))) :=
        mul_le_mul' h12 e3'
    _ = Cε ^ 3 * (δ ^ (-(10 * ε)) * (δ ^ (-ε) * δ ^ (-(4 * ε)))) := by ring
    _ = Cε ^ 3 * δ ^ (-(15 * ε)) := by
        simp only [← NNReal.rpow_add hδ0.ne']
        congr 1
        ring_nf

/-- **The collapse control the site hand asked for,.**

At the four middle-factor sites the generic three-variable split
`Kakeya.ML2Core.spine_multiplicity_le_two_factors_sharp`'s `hsplit : mu ≤ L * (mub * muf)` is
instantiated with `muf := mu` — the fine factor is the left-hand side itself.  This records what
that costs: **the row then follows from `1 ≤ L * mub` alone**, with no finiteness and no
multiplicativity content, and the same collapse in the four-factor split
(`mf := mu`) is likewise implied by `1 ≤ L * mm * mp * mc`.

So a four-way split whose fine slot is instantiated at `mu` has moved no content: the whole
estimate then sits in the fine-factor bound `hf`, read directly on `mu`.  The firing control that
this is not vacuous is that the *un*-collapsed statement — `mu ≤ L * mf * mm * mp * mc` for a free
`mf` — is **not** derivable from `1 ≤ L * mm * mp * mc`, and does not compile.

**Family/shading/level pair:** none; this is `ENNReal` arithmetic. -/
theorem collapsed_four_split_of_one_le {mu L mm mp mc : ENNReal}
    (h : 1 ≤ L * mm * mp * mc) :
    mu ≤ L * mu * mm * mp * mc := by
  calc mu = mu * 1 := (mul_one mu).symm
    _ ≤ mu * (L * mm * mp * mc) := mul_le_mul' le_rfl h
    _ = L * mu * mm * mp * mc := by ring

/-! ## The two wiring wrappers, at four factors -/

section Wiring

variable {ι : Type u}

open Classical in
/-- **`Kakeya.ML2Core.sum_shade_gain_of_split` at four factors.**  Same two existing rows composed
(`Kakeya.ML2Core.mass_gain_of_four_factors` then `Kakeya.ML2Core.sum_shade_le_of_node_gain`); the
only new inputs are the retained level-`p` family `tp'`, its shading `Yp`, and the third
`spineScaleLoss`, which travels inside `L`.

**Level pairs:** middle `(p, b)`, new parent `(a, p)`. -/
theorem sum_shade_gain_of_split_four
    {β : ℝ} (hβ0 : 0 ≤ β) {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cu Kc lam : NNReal} (hlam0 : 0 < lam)
    {s u : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hus : u ⊆ s)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i ↦ (V i).toShadedBody))
    {Nn : ℕ} {σ : ℕ → NNReal}
    (𝒰 : Tube.ChainUniformTubeSet u (fun i ↦ (V i).toTube) Nn σ Cu)
    {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) (haN : a ≤ Nn) (hpN : p ≤ Nn) (hbN : b ≤ Nn)
    {t₁ tτ' tp' tθ' : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htτ : tτ' ⊆ t₁) (htp : tp' ⊆ ML2Reduction.activeNodes 𝒰.cover p)
    (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jp jθ : ι} (hjτ : jτ ∈ t₁)
    {Yτ' : ι → ShadedTube (σ b) (EuclideanSpace ℝ (Fin 3))}
    {Yp : ι → ShadedTube (σ p) (EuclideanSpace ℝ (Fin 3))}
    {Yθ : ι → ShadedTube (σ a) (EuclideanSpace ℝ (Fin 3))}
    {Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {L A : ENNReal} {εf gm εp εc κ g gt : ℝ}
    (hprod : ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i ↦ (V i).toShadedBody)
        ≤ L
          * ShadedBody.multiplicity
              ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
          * ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover p b j = jp} : Finset ι)
              (fun j ↦ (Yτ' j).toShadedBody)
          * ShadedBody.multiplicity
              ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover a p k = jθ} : Finset ι)
              (fun k ↦ (Yp k).toShadedBody)
          * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody))
    (hfine : ShadedBody.multiplicity
          ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εf)
          * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β)
    (hmid : ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover p b j = jp} : Finset ι)
          (fun j ↦ (Yτ' j).toShadedBody)
        ≤ (δ : ENNReal) ^ gm
          * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover p b j = jp}
                : Finset ι)).card : ENNReal) ^ β)
    (hpar : ShadedBody.multiplicity
          ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover a p k = jθ} : Finset ι)
          (fun k ↦ (Yp k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εp)
          * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover a p k = jθ}
                : Finset ι)).card : ENNReal) ^ β)
    (hcoarse : ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β)
    (hL : L * (((Cu ^ 8 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-κ))
    (hexp : g ≤ gm - εf - εp - εc - κ)
    (hmassloss : (lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
          * (∑ i ∈ s, volume (V i).shade)
        ≤ A * ∑ i ∈ u, volume (V i).shade)
    (hcardseam : (u.card : NNReal)
      ≤ Kc * ((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card : NNReal))
    (habs : A * ((Kc : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ g
        ≤ ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ gt) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ gt * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  have hδE0 : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hgain := mass_gain_of_four_factors (V := V) 𝒰 hap hpb haN hpN hbN ht₁ (htτ.trans ht₁)
    htp htθ (jp := jp) (jθ := jθ) hjτ (Yτ' := Yτ') (Yp := Yp) (Yθ := Yθ) (Y' := Y')
    hδE0 hδE1 hβ0 hprod hfine hmid hpar hcoarse hL hexp
  have hcardβ : ((u.card : ℕ) : ENNReal) ^ β ≤ ((s.card : ℕ) : ENNReal) ^ β := by
    have : ((u.card : ℕ) : ENNReal) ≤ ((s.card : ℕ) : ENNReal) := by
      exact_mod_cast Finset.card_le_card hus
    exact ENNReal.rpow_le_rpow this hβ0
  refine sum_shade_le_of_node_gain hδ1 hus (Finset.filter_subset _ _) hlam0 hdense hcardseam
    hmassloss hgain ?_
  calc A * ((Kc : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((δ : ENNReal) ^ g * ((u.card : ℕ) : ENNReal) ^ β)
      = (A * ((Kc : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ g) * ((u.card : ℕ) : ENNReal) ^ β := by ring
    _ ≤ (((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ gt) * ((s.card : ℕ) : ENNReal) ^ β := by gcongr
    _ = ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((δ : ENNReal) ^ gt * ((s.card : ℕ) : ENNReal) ^ β) := by ring

/-- **Non-vacuity of the residual-case condition.** The inequality
`∀ k < K, κc + rung k ≤ 2 η'` ranges over a bounded set, so some `η'` satisfies
it: `IsKatzTaoDividingWindow.step_lt` bounds the window's step index by
`ML2Spine.spineCount ϖ ε₁`. -/
theorem exists_bound_of_lt (f : ℕ → ℝ) : ∀ K : ℕ, ∃ B : ℝ, ∀ k : ℕ, k < K → f k ≤ B
  | 0 => ⟨0, by omega⟩
  | (K + 1) => by
    obtain ⟨B, hB⟩ := exists_bound_of_lt f K
    refine ⟨max B (f K), fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · exact (hB k h).trans (le_max_left _ _)
    · subst h; exact le_max_right _ _

/-- The residual row itself, satisfied. -/
theorem exists_residual_row (f : ℕ → ℝ) (κc : ℝ) (K : ℕ) :
    ∃ η' : ℝ, ∀ k : ℕ, k < K → κc + f k ≤ 2 * η' := by
  obtain ⟨B, hB⟩ := exists_bound_of_lt f K
  exact ⟨(κc + B) / 2, fun k hk => by have := hB k hk; linarith⟩

open Classical in
/-- **`Kakeya.ML2Core.sum_shade_gain_of_window` at four factors** — the row
`Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_bound`'s ledger calls.

Everything on either side of the four-factor package is discharged here, exactly as in the
three-factor original: cardinality bound at `Cu ^ 8`, the arithmetic below it, and the two
mass discards above it.  The genuine-parent level enters only through `hap`/`hpb` and the retained
family `tp'`.

**Level pairs:** middle `(p, b)`, new parent `(a, p)`; **family/shading:** `(u, T)` under `𝒰` with
the split's four shadings. -/
theorem sum_shade_gain_of_window_four
    {β : ℝ} (hβ0 : 0 ≤ β) {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cu Kc lam : NNReal} (hlam0 : 0 < lam)
    {s u : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hus : u ⊆ s)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody))
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {Cstar : ENNReal} {ηl : ℕ → ℝ} {εd : ℝ} {Nw a b m p : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd Nw a b m)
    (hap : a ≤ p) (hpb : p ≤ b)
    {t₁ : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b)
    (hcardseam : (u.card : NNReal) ≤ Kc * ((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card :
        NNReal))
    (hmasspos : 0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade)
    {A : ENNReal} {εf gm εp εc κ g gt : ℝ}
    (hcardu : (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)))
    (hfac : ∃ (tτ' tp' tθ' : Finset ι)
        (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
        (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p) (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jp jθ : ι),
        tτ' ⊆ t₁ ∧ tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p ∧
          tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧ tp'.Nonempty ∧
        ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tp'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) p) : NNReal) : ENNReal)
              * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j
                  = jp} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k
                  = jθ} : Finset ι) (fun k ↦ (Yp k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-εf) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} :
            Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ gm * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j =
                jp} : Finset ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} :
            Finset ι) (fun k ↦ (Yp k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-εp) * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k =
                jθ} : Finset ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β)
    (hL : ∀ n₁ n₂ n₃ : ℕ, 0 < n₁ → 0 < n₂ → 0 < n₃ →
      (n₁ : NNReal) ≤ δ ^ (-(4 : ℝ)) → (n₂ : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      (n₃ : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
            (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₃
            (Tube.gridScale δ (Tube.ssfGridLen δ) p) : NNReal) : ENNReal)
        * (((Cu ^ 8 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-κ))
    (hexp : g ≤ gm - εf - εp - εc - κ)
    (hmassloss : (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
        : ENNReal)
          * (∑ i ∈ s, volume (T i).shade)
        ≤ A * ∑ i ∈ u, volume (T i).shade)
    (habs : A * ((Kc : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
        : ENNReal)) * (δ : ENNReal) ^ g
        ≤ ((lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :
            ENNReal))
          * ((lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :
              ENNReal)) * (δ : ENNReal) ^ gt) :
    ∑ i ∈ s, volume (T i).shade
      ≤ (δ : ENNReal) ^ gt * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) := by
  classical
  have hab : a ≤ b := hwin.coarse_lt_fine.le
  have hbN : b ≤ Tube.ssfGridLen δ := hwin.fine_le_gridLen
  have haN : a ≤ Tube.ssfGridLen δ := hab.trans hbN
  have hpN : p ≤ Tube.ssfGridLen δ := hpb.trans hbN
  obtain ⟨tτ', tp', tθ', Yτ', Yp, Yθ, Y', jτ, jp, jθ, htτ', htp', htθ', hjτ, hjθ, hτne, hpne,
    hprod, hfine, hmid, hpar, hcoarse⟩ := hfac
  have hs₁ne : (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmasspos
    simp at hmasspos
  have hs₁pos : 0 < (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card := Finset.card_pos.mpr
      hs₁ne
  have hτpos : 0 < tτ'.card := Finset.card_pos.mpr hτne
  have hppos : 0 < tp'.card := Finset.card_pos.mpr hpne
  have hs₁card : (((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card : ℕ) : NNReal) ≤ δ ^ (-(4
      : ℝ)) := by
    refine le_trans ?_ hcardu
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hτcard : ((tτ'.card : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) := by
    refine le_trans ?_ hcardu
    have h1 : tτ'.card ≤ (ML2Reduction.activeNodes 𝒰.cover.toChain b).card :=
      Finset.card_le_card (htτ'.trans ht₁)
    have h2 := card_activeNodes_le_card (E := (EuclideanSpace ℝ (Fin 3))) 𝒰.cover.toChain b
    exact_mod_cast Nat.cast_le.mpr (h1.trans h2)
  have hpcard : ((tp'.card : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) := by
    refine le_trans ?_ hcardu
    have h1 : tp'.card ≤ (ML2Reduction.activeNodes 𝒰.cover.toChain p).card :=
      Finset.card_le_card htp'
    have h2 := card_activeNodes_le_card (E := (EuclideanSpace ℝ (Fin 3))) 𝒰.cover.toChain p
    exact_mod_cast Nat.cast_le.mpr (h1.trans h2)
  exact sum_shade_gain_of_split_four hβ0 hδ0 hδ1 hlam0 hus hdense 𝒰.toChain hap hpb haN hpN hbN
    ht₁ htτ' htp' htθ' (jp := jp) (jθ := jθ) hjτ hprod hfine hmid hpar hcoarse
    (hL _ _ _ hs₁pos hτpos hppos hs₁card hτcard hpcard) hexp hmassloss hcardseam habs

/-- **C1 / L1 for the residual row, at the spine constants themselves.**

The row `hres` that route (i) of R0d adds to the two guarded statements is satisfiable, with any
margin one likes: `IsKatzTaoDividingWindow.step_lt` bounds the window's step index by
`ML2Spine.spineCount ϖ ε₁`, so only finitely many rungs are constrained, and `η'` is a free
parameter of the statement.  Stated with a slack of `1` so that the margin is visible rather than
tight.

A scalar side condition nobody can meet is a vacuity by another route; this is the answer that it is not one. -/
theorem exists_residual_row_spine (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (κc : ℝ) :
    ∃ η' : ℝ, ∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
      κc + ML2Spine.spineRung β ϖ ε₁ gain dens k + 1 ≤ 2 * η' := by
  obtain ⟨B, hB⟩ := exists_bound_of_lt (ML2Spine.spineRung β ϖ ε₁ gain dens)
    (ML2Spine.spineCount ϖ ε₁)
  exact ⟨(κc + B + 1) / 2, fun k hk => by have := hB k hk; linarith⟩

end Wiring

end Kakeya.ML2Core

end
