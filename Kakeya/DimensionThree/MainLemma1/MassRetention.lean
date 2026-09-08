/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization

/-!
# Multiplicity is priced in shade mass

Blueprint §2's third invariant — *price every refinement in shade sum* — has a one-line
quantitative form which this file records and which the Case (ii) leaf needs twice.

`Kakeya.ml1Boot.multiplicity_le_mul_of_shade_mass`: if the shades of `(t, W)` are contained in
the shades of `(s, V)` and the total shade mass of `(s, V)` is at most `K` times that of `(t, W)`,
then `µ(s, V) ≤ K · µ(t, W)`.

The proof is the definition: `µ = (∑ shade) / |⋃ shade|`, the numerator on the left is `≤ K`
times the numerator on the right, and the denominator on the left is `≥` the denominator on the
right, so both moves go the same way.  Nothing about tubes, scales or geometry enters.

Two consequences are what the leaf uses.

* **Passing to a subfamily costs exactly its mass share.**  With `W = V` and `t ⊆ s`
  (`Kakeya.ml1Boot.multiplicity_le_mul_of_subset_of_shade_mass`), the multiplicity of the whole
  family is at most the retention factor times the multiplicity of the retained one.  This is the
  move that lets a factorization proved on a *refinement* be read on the ambient family.

* **Restricting the shading costs exactly its mass share.**
  `Kakeya.ml1Boot.IsTwoScaleFactors.of_shade_restriction` transports the whole B3 bundle from a
  restricted shading `Vr` back to the original shading `V`, at the single price `K · Lfact` in
  the total loss and with every other clause unchanged.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*}

theorem multiplicity_le_mul_of_shade_mass {s t : Finset ι} (V W : ι → ShadedBody E)
    {K : ENNReal}
    (hsub : (⋃ i ∈ t, (W i).shade) ⊆ ⋃ i ∈ s, (V i).shade)
    (hmass : ∑ i ∈ s, volume (V i).shade ≤ K * ∑ i ∈ t, volume (W i).shade) :
    ShadedBody.multiplicity s V ≤ K * ShadedBody.multiplicity t W := by
  have hK : K * ((∑ i ∈ t, volume (W i).shade) / volume (⋃ i ∈ t, (W i).shade))
      = (K * ∑ i ∈ t, volume (W i).shade) / volume (⋃ i ∈ t, (W i).shade) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hK]
  exact ENNReal.div_le_div hmass (measure_mono hsub)

theorem multiplicity_le_mul_of_subset_of_shade_mass {s t : Finset ι} (hts : t ⊆ s)
    (V : ι → ShadedBody E) {K : ENNReal}
    (hmass : ∑ i ∈ s, volume (V i).shade ≤ K * ∑ i ∈ t, volume (V i).shade) :
    ShadedBody.multiplicity s V ≤ K * ShadedBody.multiplicity t V := by
  refine multiplicity_le_mul_of_shade_mass V V ?_ hmass
  exact Set.iUnion₂_subset fun i hi => Set.subset_iUnion₂ (s := fun i (_ : i ∈ s) =>
    (V i).shade) i (hts hi)

section Transport

variable {κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
  {δ τ θ : NNReal}

theorem IsTwoScaleFactors.of_shade_restriction
    {Lfact Lcard K : ENNReal}
    {amb : Finset ι} {V Vr : ι → ShadedTube δ E}
    {tτAmb : Finset κ} {Vτ : κ → Tube τ E} {pτ : ι → κ}
    {tθAmb : Finset lc} {Vθ : lc → Tube θ E} {pθ : κ → lc}
    {kF : κ} {Yf : ι → ShadedTube δ E} {lamF : NNReal}
    {lM : lc} {Ym : κ → ShadedTube τ E} {lamM : NNReal}
    {tθAct : Finset lc} {Yc : lc → ShadedTube θ E} {lamC : NNReal}
    (h : IsTwoScaleFactors Lfact Lcard amb Vr tτAmb Vτ pτ tθAmb Vθ pθ
      kF Yf lamF lM Ym lamM tθAct Yc lamC)
    (htube : ∀ i ∈ amb, (Vr i).toTube = (V i).toTube)
    (hsub : ∀ i ∈ amb, (Vr i).shade ⊆ (V i).shade)
    (hmass : ∑ i ∈ amb, volume (V i).shade ≤ K * ∑ i ∈ amb, volume (Vr i).shade) :
    IsTwoScaleFactors (K * Lfact) Lcard amb V tτAmb Vτ pτ tθAmb Vθ pθ
      kF Yf lamF lM Ym lamM tθAct Yc lamC where
  skeleton_fine := h.skeleton_fine
  skeleton_mid := h.skeleton_mid
  fine_mem := h.fine_mem
  fine_nonempty := h.fine_nonempty
  fine_tube i hi := by
    rw [h.fine_tube i hi]
    exact htube i (Finset.mem_of_mem_filter i hi)
  fine_fullness := h.fine_fullness
  mid_mem := h.mid_mem
  mid_nonempty := h.mid_nonempty
  mid_tube := h.mid_tube
  mid_fullness := h.mid_fullness
  coarse_subset := h.coarse_subset
  coarse_nonempty := h.coarse_nonempty
  coarse_tube := h.coarse_tube
  coarse_fullness := h.coarse_fullness
  branch_card := h.branch_card
  product := by
    have hmul : ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
        ≤ K * ShadedBody.multiplicity amb (fun i => (Vr i).toShadedBody) := by
      refine multiplicity_le_mul_of_shade_mass _ _ ?_ hmass
      exact Set.iUnion₂_subset fun i hi =>
        (hsub i hi).trans (Set.subset_iUnion₂ (s := fun i (_ : i ∈ amb) =>
          ((V i).toShadedBody).shade) i hi)
    refine hmul.trans ?_
    calc K * ShadedBody.multiplicity amb (fun i => (Vr i).toShadedBody)
        ≤ K * (Lfact * ShadedBody.multiplicity (fibre amb pτ kF) (fun i => (Yf i).toShadedBody)
            * ShadedBody.multiplicity (fibre tτAmb pθ lM) (fun k => (Ym k).toShadedBody)
            * ShadedBody.multiplicity tθAct (fun l => (Yc l).toShadedBody)) :=
          mul_le_mul' le_rfl h.product
      _ = K * Lfact
            * ShadedBody.multiplicity (fibre amb pτ kF) (fun i => (Yf i).toShadedBody)
            * ShadedBody.multiplicity (fibre tτAmb pθ lM) (fun k => (Ym k).toShadedBody)
            * ShadedBody.multiplicity tθAct (fun l => (Yc l).toShadedBody) := by
          ring

end Transport

end ml1Boot

end Kakeya

end

#print axioms Kakeya.ml1Boot.multiplicity_le_mul_of_shade_mass
#print axioms Kakeya.ml1Boot.multiplicity_le_mul_of_subset_of_shade_mass
#print axioms Kakeya.ml1Boot.IsTwoScaleFactors.of_shade_restriction
