/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBackProducer

/-!
# The centring hand-back at the **uniformised** subfamily, and the A7 count clause

condition of record:  — (A) the `CountTransport` re-cut at the
contracted hypothesis radius, (B) `huni` stays a binder and is discharged at the producer with the
order **centre → uniformise → hand-back**.

## What is here

**(B), complete.**  `exists_centredPushforward_of_outerFamily` isolates the centring — the cover's
nodes with the *exact* pushforward shading, which is what the two ledger identities of
`Reduction/SpineCentringCover.lean` need — and `centredHandBack_of_uniformised` re-states all
eleven fields of `Kakeya.VeryNotSticky.CentredHandBack` at a shade-refined subfamily `(s'', U'')`.
Together they are the specified order: centre, then run the tree's uniformiser on the *centred* family,
then hand back at its output.  The uniformiser's two retention clauses are exactly the two extra
inputs (`hmass`, and `hret` at `3 qc - α'`), and `sum_shade_le_of_fullness'_le` is the one-line
bridge that turns its `fullness'` clause into the shading-mass form
`Kakeya.ML2Reduction.multiplicity_le_of_shade_refinement` reads.

**(A), partial — and a blocking finding.**  Two of the three clauses of the specified
`CountTransport` are discharged here for *any* radius constant `C`:
`count_le_of_contracted_radius` is the count bound, and `node_le_rescale` is the
containment.  The third — the conclusion's **pairwise essential distinctness** — does **not**
transport under the same-index construction, and `injOn_of_pairwise_essDistinct` /
`not_pairwise_essDistinct_of_shared_node` are the reason: a pairwise essentially distinct
family of tubes is *injective* on its index set, so a transport that keeps the hypothesis's index
set cannot factor through the canonical cover's node assignment, which is many-to-one by
construction (`Kakeya.VeryNotSticky.fibre_card_le_of_lineEDAt` bounds its fibre by `A`, not by
`1`).  See  for the measurement and for the shape that does work.

## Main declarations

* `Kakeya.VeryNotSticky.exists_centredPushforward_of_outerFamily` — the centring, packaged.
* `Kakeya.VeryNotSticky.sum_shade_le_of_fullness'_le` — the uniformiser's clause, denominator
  cleared.
* `Kakeya.VeryNotSticky.centredHandBack_of_uniformised` — **(B)**: the hand-back at `(s'', U'')`.
* `Kakeya.VeryNotSticky.count_le_of_contracted_radius`, `node_le_rescale` — **(A)**'s two
  discharged clauses, at an arbitrary radius constant.
* `Kakeya.VeryNotSticky.injOn_of_pairwise_essDistinct`,
  `not_pairwise_essDistinct_of_shared_node` — **(A)**'s obstruction,.
* `Kakeya.VeryNotSticky.exists_centredHandBack_uniformised_witness` —, the composite
  witness: centre, then the tree's real uniformiser, then the hand-back at its `s''`.
-/

@[expose] public section

open MeasureTheory Metric Kakeya.ML2Reduction
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

universe u

/-! ## (B) — the centring, packaged -/

/-- **The centring step, isolated.**  The canonical cover's nodes at `r := δ'/4`, shaded by the
**exact** normalised image of the member's shade — which is what
`Kakeya.VeryNotSticky.fullness_pushforward` and `Kakeya.VeryNotSticky.multiplicity_pushforward`
consume, and the reason the uniformiser must run *after* this step and not before
(the outer family's Definition 2.2 lower brackets do not survive a
many-to-one map). -/
theorem exists_centredPushforward_of_outerFamily
    {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (hδ'0 : 0 < δ') (hδ'20 : (δ' : ℝ) ≤ 1 / 20)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} (fib : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ fib, (Z' i).carrier ⊆ T₀.carrier) :
    ∃ U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)),
      (∀ i ∈ fib, (U' i).toTube.IsCentred) ∧
      (∀ i ∈ fib, (U' i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
      (∀ i ∈ fib, normalise 0 ''
        (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).carrier ⊆ (U' i).carrier) ∧
      (∀ i ∈ fib, (U' i).shade = normalise 0 ''
        (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).shade) := by
  classical
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set O : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ outerFamily hsit.pos_ambient T₀ hR δ' Z' i with hO
  have hball : ∀ i ∈ fib,
      (O i).toTube.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    outerFamily_carrier_subset_closedBall hn hsit hR hτσ hsub
  obtain ⟨G, ϖ, hmem, -, hcovD, hcen, hmid, -, -⟩ :=
    exists_centredRepresentatives (E := EuclideanSpace ℝ (Fin 3)) hδ'0 hδ'20 fib
      (fun i ↦ (O i).toTube) hball
  have hcov : ∀ i ∈ fib, normalise 0 '' (O i).carrier ⊆ (ϖ i).carrier := by
    intro i hi
    rw [← centringDilate_image_eq_normalise_zero_image]
    exact hcovD i hi
  refine ⟨fun i ↦ handBackRep (O i) (ϖ i), fun i hi ↦ hcen (ϖ i) (hmem i hi), fun i hi ↦ ?_,
    hcov, fun i hi ↦ handBackRep_shade_eq (O i) (ϖ i) (hcov i hi)⟩
  refine carrier_subset_unitBall_of_isCentred (ϖ i) (hcen (ϖ i) (hmem i hi))
    (R₀ := 2 / 5 + (δ' : ℝ) / 4) (by positivity) (hmid (ϖ i) (hmem i hi)) ?_
  have hr0 : (0 : ℝ) < (δ' : ℝ) / 4 := by positivity
  have hr80 : (δ' : ℝ) / 4 ≤ 1 / 80 := by linarith
  have hreach := canonicalCover_reach_lt hr0 hr80
  linarith

/-- **The uniformiser's fullness clause with the common denominator cleared.**  Both families have
the same tubes, hence the same carrier sum, so a bound between the two `fullness'` values is a
bound between the two shading masses — which is the shape
`Kakeya.ML2Reduction.multiplicity_le_of_shade_refinement` reads. -/
theorem sum_shade_le_of_fullness'_le {α : Type u} {δ' : NNReal} (s : Finset α)
    (V V' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (htube : ∀ i, (V' i).toTube = (V i).toTube)
    {c : ENNReal}
    (hden0 : (∑ i ∈ s, volume (V i).carrier) ≠ 0)
    (h : ShadedBody.fullness' s (fun i ↦ (V i).toShadedBody)
      ≤ c * ShadedBody.fullness' s (fun i ↦ (V' i).toShadedBody)) :
    (∑ i ∈ s, volume (V i).shade) ≤ c * ∑ i ∈ s, volume (V' i).shade := by
  have hden' : (∑ i ∈ s, volume (V' i).carrier) = ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_congr rfl fun i _ ↦ by rw [show (V' i).carrier = (V i).carrier from by
      rw [show (V' i).carrier = (V' i).toTube.carrier from rfl,
        show (V i).carrier = (V i).toTube.carrier from rfl, htube i]]
  have hdentop : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤ := by
    refine (ENNReal.sum_lt_top.mpr fun i _ ↦ ?_).ne
    exact (V i).isCompact.measure_lt_top
  set D : ENNReal := ∑ i ∈ s, volume (V i).carrier with hD
  have hA : (∑ i ∈ s, volume (V i).shade)
      = ShadedBody.fullness' s (fun i ↦ (V i).toShadedBody) * D :=
    (ENNReal.div_mul_cancel hden0 hdentop).symm
  have hB : ShadedBody.fullness' s (fun i ↦ (V' i).toShadedBody) * D
      = ∑ i ∈ s, volume (V' i).shade := by
    simp only [ShadedBody.fullness', hden']
    exact ENNReal.div_mul_cancel hden0 hdentop
  calc (∑ i ∈ s, volume (V i).shade)
      = ShadedBody.fullness' s (fun i ↦ (V i).toShadedBody) * D := hA
    _ ≤ (c * ShadedBody.fullness' s (fun i ↦ (V' i).toShadedBody)) * D :=
        mul_le_mul' h le_rfl
    _ = c * (ShadedBody.fullness' s (fun i ↦ (V' i).toShadedBody) * D) := by rw [mul_assoc]
    _ = c * ∑ i ∈ s, volume (V' i).shade := by rw [hB]

/-- **(B) — the hand-back at the uniformised subfamily**.

`U'` is the centred family of `exists_centredPushforward_of_outerFamily`; `U''` is what the tree's
uniformiser (`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`) returns on it — **the same
tubes, shrunk shades**, on a subfamily `s'' ⊆ fib`.  All eleven fields are re-stated at
`(fib, s'', Z', U'')`:

* `centred`, `contained`, `covers`, `maxDensity_le` read only the *tubes*, which the uniformiser
  does not move, so they survive verbatim;
* `fullness_ge` costs the uniformiser's `α'` and the Jacobian, and closes on the single threshold
  `512 ≤ (δ')^{-qc}` provided `α' ≤ qc`;
* `multiplicity_le` costs the uniformiser's `α'` too, which is why `hret` is stated at
  `3 qc - α'` and not at `3 qc`: `Kakeya.VeryNotSticky.multiplicity_pushforward` is an equality, so
  the whole of the `3 qc` is available to the selection and the shade refinement together.

The two inputs `hfullS`, `hret` are the subfamily's price, exactly as
`exists_centredHandBack_of_outerFamily_subfamily`; at `s'' = fib` and `α' = 0` they are free. -/
theorem centredHandBack_of_uniformised
    {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (hδ'0 : 0 < δ') (hδ'20 : (δ' : ℝ) ≤ 1 / 20)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {qc α' : ℝ} (_hqc0 : 0 < qc) (_hα'0 : 0 ≤ α') (hα'qc : α' ≤ qc)
    (hthr : (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc))
    {α : Type u} {fib s'' : Finset α} (hs'' : s'' ⊆ fib)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' U'' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hcen : ∀ i ∈ fib, (U' i).toTube.IsCentred)
    (hball : ∀ i ∈ fib, (U' i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hcov : ∀ i ∈ fib, normalise 0 ''
      (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).carrier ⊆ (U' i).carrier)
    (hsh : ∀ i ∈ fib, (U' i).shade = normalise 0 ''
      (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).shade)
    (htube : ∀ i, (U'' i).toTube = (U' i).toTube)
    (hshade : ∀ i, (U'' i).shade ⊆ (U' i).shade)
    (hmass : (∑ i ∈ s'', volume (U' i).shade)
      ≤ (δ' : ENNReal) ^ (-α') * ∑ i ∈ s'', volume (U'' i).shade)
    (hdens : Kakeya.maxDensity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-qc))
    (hfull : (δ' : ENNReal) ^ qc ≤ ShadedBody.fullness fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody))
    (hfullS : (δ' : ENNReal) ^ qc ≤ (ShadedBody.fullness s''
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) : ENNReal))
    (hret : ShadedBody.multiplicity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (-(3 * qc - α')) * ShadedBody.multiplicity s''
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)) :
    CentredHandBack hsit hR T₀ 0 qc fib s'' Z' U'' := by
  classical
  set O : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ outerFamily hsit.pos_ambient T₀ hR δ' Z' i with hO
  have hδE0 : (δ' : ENNReal) ≠ 0 := by simpa using ne_of_gt hδ'0
  have hδEt : (δ' : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hδ'1 : δ' ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hδE1 : (δ' : ENNReal) ≤ 1 := by exact_mod_cast hδ'1
  have hcar : ∀ i, (U'' i).carrier = (U' i).carrier := fun i ↦ by
    rw [show (U'' i).carrier = (U'' i).toTube.carrier from rfl,
      show (U' i).carrier = (U' i).toTube.carrier from rfl, htube i]
  have hcov'' : ∀ i ∈ s'', normalise 0 '' (O i).carrier ⊆ (U'' i).carrier := fun i hi ↦ by
    rw [hcar i]; exact hcov i (hs'' hi)
  have hsh'' : ∀ i ∈ s'', (U' i).shade = normalise 0 '' (O i).shade := fun i hi ↦ hsh i (hs'' hi)
  have hfp : (ShadedBody.fullness s'' (fun i ↦ (U' i).toShadedBody) : ENNReal)
      = ENNReal.ofReal (1 / 512)
        * (ShadedBody.fullness s'' (fun i ↦ (O i).toShadedBody) : ENNReal) :=
    fullness_pushforward s'' O U' 0 hsh''
  have hmp : ShadedBody.multiplicity s'' (fun i ↦ (U' i).toShadedBody)
      = ShadedBody.multiplicity s'' (fun i ↦ (O i).toShadedBody) :=
    multiplicity_pushforward s'' O U' 0 hsh''
  have hmref : ShadedBody.multiplicity s'' (fun i ↦ (U' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (-α') * ShadedBody.multiplicity s'' (fun i ↦ (U'' i).toShadedBody) :=
    Kakeya.ML2Reduction.multiplicity_le_of_shade_refinement (Finset.Subset.refl s'')
      (fun i ↦ hshade i) hmass
  refine
    { subset := hs''
      small := hδ'20
      dens := hdens
      full := hfull
      centred := fun i hi ↦ by rw [htube i]; exact hcen i (hs'' hi)
      contained := fun i hi ↦ by rw [hcar i]; exact hball i (hs'' hi)
      covers := hcov''
      maxDensity_le := ?_
      fullness_ge := ?_
      card_le := by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hs'')
      multiplicity_le := ?_ }
  · refine le_trans (maxDensity_nodes_le s'' O U'' hcov'') ?_
    have hmono : Kakeya.maxDensity s'' (fun i ↦ (O i).toConvexSpaceBody)
        ≤ (δ' : ENNReal) ^ (-qc) :=
      le_trans (Kakeya.maxDensity_mono (fun i ↦ (O i).toConvexSpaceBody) hs'') hdens
    calc (512 : ENNReal) * Kakeya.maxDensity s'' (fun i ↦ (O i).toConvexSpaceBody)
        ≤ (δ' : ENNReal) ^ (-qc) * (δ' : ENNReal) ^ (-qc) := mul_le_mul' hthr hmono
      _ = (δ' : ENNReal) ^ (-(2 * qc)) := by
          rw [← ENNReal.rpow_add _ _ hδE0 hδEt]; ring_nf
  · have hfu : (ShadedBody.fullness s'' (fun i ↦ (U' i).toShadedBody) : ENNReal)
        ≤ (δ' : ENNReal) ^ (-α')
          * (ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) : ENNReal) := by
      have hden' : (∑ i ∈ s'', volume (U'' i).carrier) = ∑ i ∈ s'', volume (U' i).carrier :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hcar i]
      rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
      simp only [ShadedBody.fullness']
      rw [hden', ← mul_div_assoc]
      exact ENNReal.div_le_div_right hmass _
    have hkey : (δ' : ENNReal) ^ α' * ((δ' : ENNReal) ^ (-α')
        * (ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) : ENNReal))
        = (ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) : ENNReal) := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδE0 hδEt]
      simp
    have hstep : (δ' : ENNReal) ^ α'
        * (ENNReal.ofReal (1 / 512) * (δ' : ENNReal) ^ qc)
        ≤ (ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) : ENNReal) := by
      rw [← hkey]
      refine mul_le_mul' le_rfl (le_trans ?_ hfu)
      rw [hfp]
      exact mul_le_mul' le_rfl hfullS
    refine le_trans ?_ hstep
    have hofr : ENNReal.ofReal (1 / 512) = (512 : ENNReal)⁻¹ := by
      rw [show ((1 : ℝ) / 512) = (512 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
      rw [show ENNReal.ofReal (512 : ℝ) = (512 : ENNReal) by
        rw [show (512 : ℝ) = ((512 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num]
    rw [hofr, ← mul_assoc, mul_comm ((δ' : ENNReal) ^ α') ((512 : ENNReal)⁻¹), mul_assoc,
      ← ENNReal.rpow_add _ _ hδE0 hδEt]
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num)), mul_comm]
    calc (512 : ENNReal) * (δ' : ENNReal) ^ (3 * qc)
        ≤ (δ' : ENNReal) ^ (-qc) * (δ' : ENNReal) ^ (3 * qc) := mul_le_mul' hthr le_rfl
      _ = (δ' : ENNReal) ^ (3 * qc - qc) := by
          rw [← ENNReal.rpow_add _ _ hδE0 hδEt]; ring_nf
      _ ≤ (δ' : ENNReal) ^ (α' + qc) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  · calc ShadedBody.multiplicity fib (fun i ↦ (O i).toShadedBody)
        ≤ (δ' : ENNReal) ^ (-(3 * qc - α'))
            * ShadedBody.multiplicity s'' (fun i ↦ (O i).toShadedBody) := hret
      _ = (δ' : ENNReal) ^ (-(3 * qc - α'))
            * ShadedBody.multiplicity s'' (fun i ↦ (U' i).toShadedBody) := by rw [hmp]
      _ ≤ (δ' : ENNReal) ^ (-(3 * qc - α'))
            * ((δ' : ENNReal) ^ (-α')
              * ShadedBody.multiplicity s'' (fun i ↦ (U'' i).toShadedBody)) :=
          mul_le_mul' le_rfl hmref
      _ = (δ' : ENNReal) ^ (-(3 * qc))
            * ShadedBody.multiplicity s'' (fun i ↦ (U'' i).toShadedBody) := by
          rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδE0 hδEt]; ring_nf

/-! ## (A) — the specified `CountTransport`: the two clauses that hold, at any radius constant -/

/-- **The count display,.**  Reading the hypothesis at the
contracted radius `ρ / C` with `1 ≤ C` and the hypothesis's own loss `1 ≤ Λ` already delivers the
conclusion's bare count `ρ^{-2-ζ}`: the rescaling pays for itself.  Stated for an arbitrary `C` so
that it is the specified clause at `C := centringCoverRadiusConstant` (whose definition is the GC
owner's, in `Reduction/SpineCentredHandBack.lean`) and at any other admissible constant. -/
theorem count_le_of_contracted_radius {ρ C : NNReal} (hρ0 : 0 < ρ) (hC1 : 1 ≤ C)
    {Λ ζ n : ℝ} (hΛ : 1 ≤ Λ) (hζ : 0 ≤ 2 + ζ)
    (h : Λ * ((ρ / C : NNReal) : ℝ) ^ (-2 - ζ) ≤ n) :
    (ρ : ℝ) ^ (-2 - ζ) ≤ n := by
  have hρr : (0 : ℝ) < (ρ : ℝ) := hρ0
  have hCr : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
  have hC0 : (0 : ℝ) < (C : ℝ) := by linarith
  have hdiv : ((ρ / C : NNReal) : ℝ) = (ρ : ℝ) / (C : ℝ) := NNReal.coe_div _ _
  rw [hdiv, Real.div_rpow hρr.le hC0.le] at h
  have hpow : (C : ℝ) ^ (-2 - ζ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hCr (by linarith)
  have hpow0 : (0 : ℝ) < (C : ℝ) ^ (-2 - ζ) := Real.rpow_pos_of_pos hC0 _
  have hρpow : (0 : ℝ) < (ρ : ℝ) ^ (-2 - ζ) := Real.rpow_pos_of_pos hρr _
  calc (ρ : ℝ) ^ (-2 - ζ) ≤ (ρ : ℝ) ^ (-2 - ζ) / (C : ℝ) ^ (-2 - ζ) := by
        rw [le_div_iff₀ hpow0]; nlinarith
    _ ≤ Λ * ((ρ : ℝ) ^ (-2 - ζ) / (C : ℝ) ^ (-2 - ζ)) := by nlinarith [div_pos hρpow hpow0]
    _ ≤ n := h

/-- **The containment clause of the specified `CountTransport`.**  A centred representative is a
unit-core `δ'`-tube, so at any window radius `ρ ≥ δ'` the `ρ`-tube on its own line contains it —
this is the clause `∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody`,
discharged with no geometry beyond `Tube.rescale`.  Note that this fixes `Tρ j` up to its radius:
a `ρ`-tube containing a unit-core tube is the `ρ`-tube on that tube's own line, which is why the
conclusion's essential distinctness is a statement about the *nodes'* lines and not something the
producer may choose. -/
theorem node_le_rescale {δ' ρ : NNReal} (hδρ : δ' ≤ ρ)
    (U : ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) :
    U.toConvexSpaceBody ≤ (U.toTube.rescale ρ).toConvexSpaceBody := by
  have h := Tube.rescale_le_rescale_of_radius_le U.toTube hδρ
  rwa [Tube.toConvexSpaceBody_rescale_self] at h

/-! ## (A) — the obstruction: essential distinctness forces an injective transport -/

/-- **A pairwise essentially distinct family of tubes is injective on its index set.**  A tube of
positive finite volume is never essentially distinct from itself
(`IsEssentiallyDistinct.not_isEssentiallyDistinct_self`), so two indices carrying the same tube
cannot both be retained. -/
theorem injOn_of_pairwise_essDistinct {κ : Type*} {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hED : (tρ : Set κ).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) :
    Set.InjOn Tρ (tρ : Set κ) := by
  intro j hj k hk heq
  by_contra hne
  have h : _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier := hED hj hk hne
  rw [heq] at h
  have hv := Tube.volume_pos_and_lt_top hρ0 hρ1 (Tρ k)
  exact _root_.not_isEssentiallyDistinct_self hv.1.ne' hv.2.ne h

/-- **The blocking finding for.**

Keeping every index would require "the transported family has the **same index set**", with `Tρ j` the
`ρ`-tube on the node of the family index `f j` that the cover member `W j` serves
(`node_le_rescale` shows that is the only choice).  But the canonical cover's node assignment is
**many-to-one** — that is what
`Kakeya.VeryNotSticky.fibre_card_le_of_lineEDAt` bounds, by `A` and not by `1` — and as soon as two
retained cover members are served by family indices sharing a node, the transported family repeats
a tube and **cannot** be pairwise essentially distinct.

So the conclusion's essential distinctness is not inherited index-for-index; a transport must be
allowed to pass to a *subfamily*, and the count then loses a packing constant.  The existing
precedent for exactly that trade is
`Kakeya.ML2Reduction.exists_edUsed_rescale_of_edUsed_body`, whose loss
`Tube.essDistinctTubesInSelfDilate.C 3 (outerTransportRatio 3 K)` is what
`Kakeya.ML2Reduction.spineOuterCountLoss` was sized to absorb for the *outer* transport.  See
 -/
theorem not_pairwise_essDistinct_of_shared_node {κ α : Type*} {ρ δ' : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {tρ : Finset κ}
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) (f : κ → α) {j k : κ}
    (hj : j ∈ tρ) (hk : k ∈ tρ) (hjk : j ≠ k)
    (hnode : (U' (f j)).toTube = (U' (f k)).toTube) :
    ¬ ((tρ : Set κ).Pairwise fun a bb ↦
        _root_.IsEssentiallyDistinct ((U' (f a)).toTube.rescale ρ).carrier
          ((U' (f bb)).toTube.rescale ρ).carrier) := by
  intro hED
  have h := injOn_of_pairwise_essDistinct hρ0 hρ1 tρ
    (fun a ↦ (U' (f a)).toTube.rescale ρ) hED (by simpa using hj) (by simpa using hk)
    (by simp only []; rw [hnode])
  exact hjk h


/-! ## the composite witness: centre, uniformise, hand back -/

/-- **the specified order, run end to end on a real family.**

The uniformisation construction requires that `hfullS` and `hret` be satisfiable **together
with the uniformiser's actual output**, not merely type-correct.  This does that: on a
two-member family of parallel `4δ'`-tubes with distinct midpoints inside the ambient unit tube it

1. centres (`exists_centredPushforward_of_outerFamily`),
2. runs the tree's own uniformiser `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` at
   `K₀ = 1`, `α = α' = α'` **on the centred family**, obtaining a genuine `s'' ⊆ fib` and a
   genuine shade-shrunk `U''`,
3. converts the uniformiser's `fullness'` clause into the shading-mass form with
   `sum_shade_le_of_fullness'_le`,
4. supplies `hfullS` **at whatever `s''` the uniformiser returned** — the outer family's fullness
   bound is proved for *every* nonempty subfamily here, so nothing is assumed about the
   uniformiser's choice — and `hret` from `ShadedBody.multiplicity_le_card` and
   `ShadedBody.one_le_multiplicity`,
5. concludes with `centredHandBack_of_uniformised`.

It also returns the uniform structure at `(s'', U'')`, so the same witness certifies that the
eliminator's `huni` binder is available exactly where the hand-back is produced — which is
's alignment: `s''` is one Finset, used by the hand-back, by `huni`, and (once A7 is
specified) by the count clause.

The three scalar hypotheses are `δ'`-thresholds and nothing else: `512 ≤ (δ')^{-qc}`,
`(δ')^{qc} ≤ (outerLoss (C_N 3))⁻¹`, and the two cardinality thresholds `2 ≤ (δ')^{-1}` and
`2 ≤ (δ')^{-(3qc-α')}`. -/
theorem exists_centredHandBack_uniformised_witness {α' : ℝ} (hα'0 : 0 < α') :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧
      ∀ {δ' : NNReal} (hδ0 : 0 < δ') (_hδle : δ' ≤ δ₀) (hδ20 : (δ' : ℝ) ≤ 1 / 20)
        {qc : ℝ} (_hqc0 : 0 < qc) (_hα'qc : α' ≤ qc)
        (_hthr : (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc))
        (_hδloss : (δ' : ENNReal) ^ qc
          ≤ ((Kakeya.ML2Reduction.outerLoss (Tube.normalization.C 3))⁻¹ : NNReal))
        (_hcard2 : (2 : ℝ) ≤ (δ' : ℝ) ^ (-(1 : ℝ)))
        (_hret2 : (2 : ENNReal) ≤ (δ' : ENNReal) ^ (-(3 * qc - α')))
        (u v : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ = 1) (_hv : ‖v‖ = 1),
      ∃ (Z' : Fin 2 → ShadedTube (4 * δ') (EuclideanSpace ℝ (Fin 3)))
        (s'' : Finset (Fin 2)) (U'' : Fin 2 → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))),
        s''.Nonempty ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
          (ShadedTube.ssfUniformConst 3)) ∧
        CentredHandBack (isRescalingSituation_witness hδ0 (by linarith))
          (lt_of_lt_of_le zero_lt_one (Tube.normalization.one_le_C 3))
          (Tube.ofMidpointDirection (1 : NNReal) 0 u hu) 0 qc
          (Finset.univ : Finset (Fin 2)) s'' Z' U'' := by
  classical
  obtain ⟨δ₀u, hδ₀u0, -, huni⟩ := ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf
    (E := EuclideanSpace ℝ (Fin 3)) 1 α' α' hα'0 hα'0
  refine ⟨δ₀u, hδ₀u0, ?_⟩
  intro δ' hδ0 hδle hδ20 qc hqc0 hα'qc hthr hδloss hcard2 hret2 u v hu hv
  have hδ4 : 4 * (δ' : ℝ) ≤ 1 := by linarith
  have hR : (0 : ℝ) < Tube.normalization.C 3 :=
    lt_of_lt_of_le zero_lt_one (Tube.normalization.one_le_C 3)
  have hR1 : (1 : ℝ) ≤ Tube.normalization.C 3 := Tube.normalization.one_le_C 3
  have h4δ0 : 0 < 4 * δ' := by positivity
  have h4δ1 : 4 * δ' ≤ 1 := by exact_mod_cast hδ4
  have hδ'1 : δ' ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  set hsit := isRescalingSituation_witness hδ0 hδ4 with hsitdef
  set T₀ : Tube 1 (EuclideanSpace ℝ (Fin 3)) := Tube.ofMidpointDirection 1 0 u hu with hT₀
  set c : EuclideanSpace ℝ (Fin 3) := (4 : ℝ)⁻¹ • v with hc
  set Zt : Fin 2 → Tube (4 * δ') (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ Tube.ofMidpointDirection (4 * δ') (if i = 0 then 0 else c) u hu with hZt
  set Z' : Fin 2 → ShadedTube (4 * δ') (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ fullShadeTube (Zt i) with hZ'
  have hcnorm : ‖c‖ = (4 : ℝ)⁻¹ := by
    rw [hc, norm_smul, norm_inv, Real.norm_ofNat, hv, mul_one]
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin 2)), (Z' i).carrier ⊆ T₀.carrier := by
    intro i _ z hz
    obtain ⟨t, g, ht, hg, rfl⟩ := (Zt i).exists_decomp_of_mem_carrier hz
    have hzm : (Zt i).midpoint = (if i = 0 then 0 else c) := by
      rw [hZt]; exact Tube.midpoint_ofMidpointDirection' _ _ _
    have hzd : (Zt i).direction = u := by
      rw [hZt]; exact Tube.direction_ofMidpointDirection' _ _ _
    have hTm : T₀.midpoint = 0 := by rw [hT₀, Tube.midpoint_ofMidpointDirection']
    have hTd : T₀.direction = u := by rw [hT₀, Tube.direction_ofMidpointDirection']
    refine T₀.mem_carrier_of_dist_le (T₀.midpoint_add_smul_mem_segment (t := t) ht) ?_
    rw [dist_eq_norm, hTm, hTd, hzm, hzd]
    have hsimp : (if i = 0 then (0 : EuclideanSpace ℝ (Fin 3)) else c) + t • u + g
        - (0 + t • u) = (if i = 0 then (0 : EuclideanSpace ℝ (Fin 3)) else c) + g := by abel
    rw [hsimp]
    have h4 : ‖g‖ ≤ 4 * (δ' : ℝ) := by
      have hcast : ((4 * δ' : NNReal) : ℝ) = 4 * (δ' : ℝ) := by push_cast; ring
      rwa [hcast] at hg
    have hone : ((1 : NNReal) : ℝ) = 1 := by norm_num
    rw [hone]
    have hmid : ‖(if i = 0 then (0 : EuclideanSpace ℝ (Fin 3)) else c)‖ ≤ (4 : ℝ)⁻¹ := by
      by_cases h : i = 0
      · simp [h]
      · simp [h, hcnorm]
    calc ‖(if i = 0 then (0 : EuclideanSpace ℝ (Fin 3)) else c) + g‖
        ≤ ‖(if i = 0 then (0 : EuclideanSpace ℝ (Fin 3)) else c)‖ + ‖g‖ := norm_add_le _ _
      _ ≤ (4 : ℝ)⁻¹ + 4 * (δ' : ℝ) := by gcongr
      _ ≤ 1 := by linarith
  set O : Fin 2 → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ outerFamily hsit.pos_ambient T₀ hR δ' Z' i with hOdef
  have hτσ : ((4 * δ' : NNReal) : ℝ) / ((1 : NNReal) : ℝ) ≤ 4 * (δ' : ℝ) := by
    push_cast; rw [div_one]
  -- the density and the fullness on the whole family
  have hdens : Kakeya.maxDensity (Finset.univ : Finset (Fin 2))
      (fun i ↦ (O i).toConvexSpaceBody) ≤ (δ' : ENNReal) ^ (-qc) := by
    refine le_trans (Kakeya.maxDensity_le_card _ _) (le_trans ?_ hthr)
    simp only [Finset.card_univ, Fintype.card_fin]
    norm_num
  -- fullness of the outer family on ANY nonempty subfamily
  have hfullAny : ∀ s : Finset (Fin 2), s.Nonempty →
      (δ' : ENNReal) ^ qc ≤ (ShadedBody.fullness s (fun i ↦ (O i).toShadedBody) : ENNReal) := by
    intro s hs
    have hZfull : ShadedBody.fullness s (fun i ↦ (Z' i).toShadedBody) = 1 := by
      refine fullness_eq_one_of_fullyShaded _ _ (fun i _ ↦ rfl) ?_
      obtain ⟨i₀, hi₀⟩ := hs
      have h0 : volume (Zt i₀).carrier ≠ 0 := (Tube.volume_pos_and_lt_top h4δ0 h4δ1 (Zt i₀)).1.ne'
      intro hsum
      exact h0 ((Finset.sum_eq_zero_iff.mp hsum) i₀ hi₀)
    have h := Kakeya.ML2Reduction.outerFamily_le_fullness (E := EuclideanSpace ℝ (Fin 3))
      (s := s) (𝕋 := Z') (T₀ := T₀) (by simp) hsit hR hR1 hτσ
      (fun i _ ↦ hsub i (Finset.mem_univ i))
    rw [hZfull, mul_one] at h
    exact le_trans hδloss (by exact_mod_cast h)
  have hfull := hfullAny Finset.univ ⟨0, Finset.mem_univ 0⟩
  -- T1: the centring
  obtain ⟨U', hcen, hball, hcov, hsh⟩ :=
    exists_centredPushforward_of_outerFamily hsit hR hτσ hδ0 hδ20 T₀ Finset.univ Z' hsub
  -- the uniformiser, on the CENTRED family
  have hcard1 : ((Finset.univ : Finset (Fin 2)).card : ℝ) ≤ (δ' : ℝ) ^ (-((1 : ℕ) : ℝ)) := by
    simpa using hcard2
  obtain ⟨s'', hs''sub, U'', htube, hshade, hcardret, hfullret, hstruct⟩ :=
    huni hδ0 hδle (Finset.univ : Finset (Fin 2)) U' hball hcard1
  -- `s''` is nonempty
  have hs''ne : s''.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp] at hcardret
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, Finset.card_univ,
      Fintype.card_fin] at hcardret
    norm_num at hcardret
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp] at hstruct
  refine ⟨Z', s'', U'', hs''ne, hstruct, ?_⟩
  -- the shading-mass retention, from the uniformiser's fullness clause
  have hden0 : (∑ i ∈ s'', volume (U' i).carrier) ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hs''ne
    have h0 : volume (U' i₀).carrier ≠ 0 :=
      (Tube.volume_pos_and_lt_top hδ0 hδ'1 (U' i₀).toTube).1.ne'
    intro hsum
    exact h0 ((Finset.sum_eq_zero_iff.mp hsum) i₀ hi₀)
  have hcoe : ENNReal.ofReal ((δ' : ℝ) ^ (-α')) = (δ' : ENNReal) ^ (-α') := by
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ0), ← NNReal.coe_rpow,
      ENNReal.ofReal_coe_nnreal]
  have hmass : (∑ i ∈ s'', volume (U' i).shade)
      ≤ (δ' : ENNReal) ^ (-α') * ∑ i ∈ s'', volume (U'' i).shade := by
    refine sum_shade_le_of_fullness'_le s'' U' U'' htube hden0 ?_
    rw [← hcoe]
    exact hfullret
  -- the two subfamily inputs
  have hfullS := hfullAny s'' hs''ne
  have hret : ShadedBody.multiplicity (Finset.univ : Finset (Fin 2))
      (fun i ↦ (O i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (-(3 * qc - α'))
        * ShadedBody.multiplicity s'' (fun i ↦ (O i).toShadedBody) := by
    have hone : (1 : ENNReal) ≤ ShadedBody.multiplicity s'' (fun i ↦ (O i).toShadedBody) := by
      refine ShadedBody.one_le_multiplicity s'' _ ?_
      intro hall
      have hposE : (0 : ENNReal)
          < ((ShadedBody.fullness s'' (fun i ↦ (O i).toShadedBody) : NNReal) : ENNReal) :=
        lt_of_lt_of_le (ENNReal.rpow_pos (by simpa using hδ0) ENNReal.coe_ne_top) hfullS
      have hpos : 0 < ShadedBody.fullness s'' (fun i ↦ (O i).toShadedBody) := by
        exact_mod_cast hposE
      have := ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos s'' _ hpos
      exact this (Finset.sum_eq_zero fun i hi ↦ hall i hi)
    calc ShadedBody.multiplicity (Finset.univ : Finset (Fin 2)) (fun i ↦ (O i).toShadedBody)
        ≤ ((Finset.univ : Finset (Fin 2)).card : ENNReal) := ShadedBody.multiplicity_le_card _ _
      _ = (2 : ENNReal) := by simp
      _ ≤ (δ' : ENNReal) ^ (-(3 * qc - α')) := hret2
      _ = (δ' : ENNReal) ^ (-(3 * qc - α')) * 1 := (mul_one _).symm
      _ ≤ (δ' : ENNReal) ^ (-(3 * qc - α'))
          * ShadedBody.multiplicity s'' (fun i ↦ (O i).toShadedBody) := mul_le_mul' le_rfl hone
  exact centredHandBack_of_uniformised hsit hR hδ0 hδ20 T₀ hqc0 hα'0.le hα'qc hthr hs''sub
    Z' U' U'' hcen hball hcov hsh htube hshade hmass hdens hfull hfullS hret

end Kakeya.VeryNotSticky

end
