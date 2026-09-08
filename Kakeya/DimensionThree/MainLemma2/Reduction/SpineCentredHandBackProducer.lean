/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentringCover

/-!
# Producing the centred hand-back for the outer family

The construction follows `lemcanonicalcover` in the refined proof
`260115_kakeyadetailedproofv3_revised_detailed.tex`, lines 4774-4800, under the
normalising similarity `lemaffineinvariance`, lines 4738-4772, at `ρ = 1`.
The cardinality and mass identities are `eq:defect-centred-ledger`, lines
6013-6023, with threshold absorption in lines 6079-6086.

The canonical representatives lie in `closedBall 0 1`. The convex-body image
under `normalise 0` is expressed using the homothety API. Density bounds pass
to this image through `maxDensity_le`. The hand-back records the common family,
its geometric containment and the quantitative transports used by
`fine_factor_of_lemma91At_of_canonicalCover`.

The margin parameters are `qc := ν/103`, `ηd := 3 * qc`, and
`gain' := gain - 3 * qc`. The construction keeps the resulting loss explicit.
-/

@[expose] public section

open MeasureTheory Metric RealInnerProductSpace Kakeya.ML2Reduction
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

universe u

/-! ## `normalise 0`, `centringDilate` and the existing homothety API -/

theorem normalise_zero_apply (x : EuclideanSpace ℝ (Fin 3)) :
    normalise 0 x = AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) ((8 : ℝ)⁻¹) x := by
  simp [normalise, AffineMap.homothety_apply]

theorem centringDilate_eq_normalise_zero (x : EuclideanSpace ℝ (Fin 3)) :
    centringDilate x = normalise 0 x := by
  simp [centringDilate, normalise]

theorem normalise_zero_image (A : Set (EuclideanSpace ℝ (Fin 3))) :
    normalise 0 '' A = AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) ((8 : ℝ)⁻¹) '' A :=
  Set.image_congr fun x _ ↦ normalise_zero_apply x

theorem centringDilate_image_eq_normalise_zero_image (A : Set (EuclideanSpace ℝ (Fin 3))) :
    centringDilate '' A = normalise 0 '' A :=
  Set.image_congr fun x _ ↦ centringDilate_eq_normalise_zero x

/-- The normalised image of a convex body, as a convex body: the existing
`ConvexSpaceBody.homothety` at centre `0` and ratio `1/8`. -/
noncomputable def normaliseBody (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
  K.homothety 0 ((8 : ℝ)⁻¹)

theorem normaliseBody_carrier (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    (normaliseBody K).carrier = normalise 0 '' K.carrier := by
  rw [normalise_zero_image]; rfl

/-- **The Jacobian, on a convex body**: `|L(K)| = |K| / 512`. -/
theorem volume_normaliseBody (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    volume (normaliseBody K).carrier = ENNReal.ofReal (1 / 512) * volume K.carrier := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [normaliseBody, ConvexSpaceBody.volume_homothety, hfr]
  norm_num

/-- **`Δ_max` is unchanged by the normalising similarity** — `lemaffineinvariance` l.4747, at the
`m = 0` instance where `Kakeya.maxDensity_affineImage` is `Kakeya.maxDensity_homothety`. -/
theorem maxDensity_normaliseBody {α : Type*} (s : Finset α)
    (W : α → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    Kakeya.maxDensity s (fun i ↦ normaliseBody (W i)) = Kakeya.maxDensity s W :=
  Kakeya.maxDensity_homothety s W 0 (by norm_num)

/-! ## The centred representative -/

/-- **The centred representative of a member**: the canonical cover's node `W`, shaded by the
normalised image of the member's shade (l.6011).  The intersection with `W.carrier` is inert as
soon as the node covers the normalised member (`handBackRep_shade_eq`); it is written so that the
representative is a total function of `(O, W)` and needs no `dite`. -/
noncomputable def handBackRep {δ' : NNReal}
    (O : ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) (W : Tube δ' (EuclideanSpace ℝ (Fin 3))) :
    ShadedTube δ' (EuclideanSpace ℝ (Fin 3)) where
  toTube := W
  shade := (normalise 0 '' O.shade) ∩ W.carrier
  measurableSet_shade := by
    refine MeasurableSet.inter ?_ W.toConvexSpaceBody.isCompact.isClosed.measurableSet
    rw [normalise_zero_image]
    exact (Kakeya.measurableEmbedding_homothety (0 : EuclideanSpace ℝ (Fin 3))
      (by norm_num : ((8 : ℝ)⁻¹) ≠ 0)).measurableSet_image' O.measurableSet_shade
  shade_subset := Set.inter_subset_right

@[simp] theorem handBackRep_toTube {δ' : NNReal}
    (O : ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) (W : Tube δ' (EuclideanSpace ℝ (Fin 3))) :
    (handBackRep O W).toTube = W := rfl

theorem handBackRep_shade_eq {δ' : NNReal}
    (O : ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) (W : Tube δ' (EuclideanSpace ℝ (Fin 3)))
    (hcov : normalise 0 '' O.carrier ⊆ W.carrier) :
    (handBackRep O W).shade = normalise 0 '' O.shade :=
  Set.inter_eq_self_of_subset_left ((Set.image_mono O.shade_subset).trans hcov)

/-! ## The `maxDensity_le` field: `Δ_max(𝔾^) ≤ 512 · Δ_max(𝔾)`, with no fibre bound -/

/-- **, "The `maxDensity_le` route".**  Passing from the normalised members to
the containing nodes multiplies `Δ_max` by at most the volume ratio `512`: a node is a unit-core
`δ'`-tube and a normalised member is `(δ'/8)`-thick with core `1/8`, so the two have the same
number of terms in every test body's sum and the terms differ by `512`.  **The fibre never
enters** — it is what `multiplicity_le` pays, not what `maxDensity_le` pays. -/
theorem maxDensity_nodes_le {δ' : NNReal} {α : Type*} (s : Finset α)
    (O U : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hcov : ∀ i ∈ s, normalise 0 '' (O i).carrier ⊆ (U i).carrier) :
    Kakeya.maxDensity s (fun i ↦ (U i).toConvexSpaceBody)
      ≤ (512 : ENNReal) * Kakeya.maxDensity s (fun i ↦ (O i).toConvexSpaceBody) := by
  classical
  have hj : (512 : ENNReal) * ENNReal.ofReal (1 / 512) = 1 := by
    rw [show ((1 : ℝ) / 512) = (512 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
    rw [show ENNReal.ofReal (512 : ℝ) = (512 : ENNReal) by
      rw [show (512 : ℝ) = ((512 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  refine Kakeya.maxDensity_le_of_forall_sum_le ?_
  intro K
  -- (a) the node's test-body containment implies the normalised member's
  have hstep : (s.filter fun i ↦ (U i).toConvexSpaceBody ≤ K)
      ⊆ (s.filter fun i ↦ normaliseBody (O i).toConvexSpaceBody ≤ K) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    rw [← SetLike.coe_subset_coe] at hi ⊢
    refine subset_trans ?_ hi.2
    rw [show SetLike.coe (normaliseBody (O i).toConvexSpaceBody)
        = (normaliseBody (O i).toConvexSpaceBody).carrier from rfl,
      normaliseBody_carrier]
    exact hcov i hi.1
  -- (b) the node's volume is `512` times the normalised member's
  have hvol : ∀ i ∈ s, volume (U i).carrier
      ≤ (512 : ENNReal) * volume (normaliseBody (O i).toConvexSpaceBody).carrier := by
    intro i _
    rw [volume_normaliseBody, ← mul_assoc, hj, one_mul]
    exact le_of_eq (Tube.volume_carrier_eq_volume_carrier (U i).toTube (O i).toTube)
  calc ∑ i ∈ s.filter (fun i ↦ (U i).toConvexSpaceBody ≤ K), volume (U i).carrier
      ≤ ∑ i ∈ s.filter (fun i ↦ (U i).toConvexSpaceBody ≤ K),
          (512 : ENNReal) * volume (normaliseBody (O i).toConvexSpaceBody).carrier :=
        Finset.sum_le_sum fun i hi ↦ hvol i (Finset.mem_filter.mp hi).1
    _ = (512 : ENNReal) * ∑ i ∈ s.filter (fun i ↦ (U i).toConvexSpaceBody ≤ K),
          volume (normaliseBody (O i).toConvexSpaceBody).carrier := by rw [Finset.mul_sum]
    _ ≤ (512 : ENNReal) * ∑ i ∈ s.filter
          (fun i ↦ normaliseBody (O i).toConvexSpaceBody ≤ K),
          volume (normaliseBody (O i).toConvexSpaceBody).carrier := by
        exact mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset hstep)
    _ ≤ (512 : ENNReal) * (Kakeya.maxDensity s (fun i ↦ normaliseBody (O i).toConvexSpaceBody)
          * volume K.carrier) := by
        exact mul_le_mul' le_rfl
          (Kakeya.sum_volume_le_maxDensity_mul_volume s
            (fun i ↦ normaliseBody (O i).toConvexSpaceBody) K)
    _ = (512 : ENNReal) * Kakeya.maxDensity s (fun i ↦ (O i).toConvexSpaceBody)
          * volume K.carrier := by
        rw [maxDensity_normaliseBody, mul_assoc]

/-! ## The threshold `512 ≤ (δ')^{-qc}` -/

/-- **The Jacobian threshold, in the `exists_threshold_*` idiom.**  `512` is `δ`-free, so it is a
threshold on the scale and never an exponent — the same mechanism as
`Kakeya.ML2Reduction.exists_threshold_outerLoss`. -/
theorem exists_threshold_centringJacobian {qc : ℝ} (hqc : 0 < qc) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ →
      (512 : ENNReal) ≤ (δ : ENNReal) ^ (-qc) := by
  obtain ⟨δ₀, hδ₀, h⟩ :=
    Kakeya.ML2Reduction.exists_threshold_const_le_rpow_neg (C := (512 : ℝ≥0)) (by norm_num) hqc
  refine ⟨δ₀, hδ₀, fun δ hδ0 hδ ↦ ?_⟩
  have hcoe : ((δ ^ (-qc) : ℝ≥0) : ENNReal) = (δ : ENNReal) ^ (-qc) :=
    ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ0) _
  have := h δ hδ0 hδ
  calc (512 : ENNReal) = ((512 : ℝ≥0) : ENNReal) := by norm_num
    _ ≤ ((δ ^ (-qc) : ℝ≥0) : ENNReal) := by exact_mod_cast this
    _ = (δ : ENNReal) ^ (-qc) := hcoe

/-- From the single threshold `512 ≤ (δ')^{-qc}`, the Jacobian threshold
`(δ')^{2 qc} ≤ 1/512` that `Kakeya.VeryNotSticky.ledgerClauses_of_pushforward` reads. -/
theorem rpow_two_mul_le_jacobian {δ' : NNReal} (hδ0 : 0 < δ') {qc : ℝ} (_hqc : 0 ≤ qc)
    (h512 : (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc)) :
    (δ' : ENNReal) ^ (2 * qc) ≤ ENNReal.ofReal (1 / 512) := by
  have hδE0 : (δ' : ENNReal) ≠ 0 := by simpa using ne_of_gt hδ0
  have hδEt : (δ' : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hofr : ENNReal.ofReal (1 / 512) = (512 : ENNReal)⁻¹ := by
    rw [show ((1 : ℝ) / 512) = (512 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hmul : (δ' : ENNReal) ^ qc * (δ' : ENNReal) ^ (-qc) = 1 := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEt]; simp
  have hqcle : (δ' : ENNReal) ^ qc ≤ (512 : ENNReal)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le]
    calc (δ' : ENNReal) ^ qc * 512 ≤ (δ' : ENNReal) ^ qc * (δ' : ENNReal) ^ (-qc) :=
          mul_le_mul' le_rfl h512
      _ = 1 := hmul
  have hone : (δ' : ENNReal) ^ qc ≤ 1 := hqcle.trans (by
    simp only [ENNReal.inv_le_one]
    norm_num)
  have hsplit : (δ' : ENNReal) ^ (2 * qc) = (δ' : ENNReal) ^ qc * (δ' : ENNReal) ^ qc := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEt]; ring_nf
  rw [hsplit, hofr]
  calc (δ' : ENNReal) ^ qc * (δ' : ENNReal) ^ qc ≤ (δ' : ENNReal) ^ qc * 1 :=
        mul_le_mul' le_rfl hone
    _ = (δ' : ENNReal) ^ qc := mul_one _
    _ ≤ (512 : ENNReal)⁻¹ := hqcle

/-! ## The producer -/

/-- **The `CentredHandBack` producer at Lemma 9.1's geometric site, on a subfamily.**

Given the spine's outer family `(fib, outerFamily … Z')` at the rescaled scale `δ'`, this builds
the centred representatives `U'` — the nodes of the set-level canonical cover
(`Kakeya.VeryNotSticky.exists_setCanonicalCentredCover`, refined l.4774–4800) applied to the
normalised members at `r := δ'/4` — and all eleven fields of
`Kakeya.VeryNotSticky.CentredHandBack` at `m := 0`.

Everything the site does not already have is one hypothesis:

* `hthr : 512 ≤ (δ')^{-qc}` — the Jacobian, a threshold on the scale
  (`exists_threshold_centringJacobian`), never an exponent;
* `hdens`, `hfull` — `CentredHandBack`'s two **input** fields, verbatim
  (′(3): the loss exponent and the input density exponent are the same number);
* `hfullS`, `hret` — the price of retaining only `s' ⊆ fib`.  At `s' = fib` both are free; see
  `exists_centredHandBack_of_outerFamily`. -/
theorem exists_centredHandBack_of_outerFamily_subfamily
    {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (hδ'0 : 0 < δ') (hδ'20 : (δ' : ℝ) ≤ 1 / 20)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {qc : ℝ} (hqc0 : 0 < qc) (hthr : (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc))
    {α : Type u} {fib s' : Finset α} (hs' : s' ⊆ fib)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ fib, (Z' i).carrier ⊆ T₀.carrier)
    (hdens : Kakeya.maxDensity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-qc))
    (hfull : (δ' : ENNReal) ^ qc ≤ ShadedBody.fullness fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody))
    (hfullS : (δ' : ENNReal) ^ qc ≤ (ShadedBody.fullness s'
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) : ENNReal))
    (hret : ShadedBody.multiplicity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (-(3 * qc)) * ShadedBody.multiplicity s'
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)) :
    ∃ U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)),
      CentredHandBack hsit hR T₀ 0 qc fib s' Z' U' := by
  classical
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set O : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ outerFamily hsit.pos_ambient T₀ hR δ' Z' i with hO
  have hδ'1 : δ' ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hball : ∀ i ∈ fib,
      (O i).toTube.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    outerFamily_carrier_subset_closedBall hn hsit hR hτσ hsub
  obtain ⟨G, ϖ, hmem, -, hcovD, hcen, hmid, -, -⟩ :=
    exists_centredRepresentatives (E := EuclideanSpace ℝ (Fin 3)) hδ'0 hδ'20 fib
      (fun i ↦ (O i).toTube) hball
  -- the covering clause, rewritten at `normalise 0`
  have hcov : ∀ i ∈ fib, normalise 0 '' (O i).carrier ⊆ (ϖ i).carrier := by
    intro i hi
    rw [← centringDilate_image_eq_normalise_zero_image]
    exact hcovD i hi
  refine ⟨fun i ↦ handBackRep (O i) (ϖ i), ?_⟩
  have hsh : ∀ i ∈ s', (handBackRep (O i) (ϖ i)).shade = normalise 0 '' (O i).shade :=
    fun i hi ↦ handBackRep_shade_eq (O i) (ϖ i) (hcov i (hs' hi))
  -- the two pushforward clauses
  obtain ⟨hfg, -⟩ :=
    ledgerClauses_of_pushforward s' hδ'0 hδ'1 O (fun i ↦ handBackRep (O i) (ϖ i)) 0 hqc0.le hsh
      hfullS (rpow_two_mul_le_jacobian hδ'0 hqc0.le hthr)
  have hmulteq : ShadedBody.multiplicity s'
      (fun i ↦ (handBackRep (O i) (ϖ i)).toShadedBody)
      = ShadedBody.multiplicity s' (fun i ↦ (O i).toShadedBody) :=
    multiplicity_pushforward s' O (fun i ↦ handBackRep (O i) (ϖ i)) 0 hsh
  exact
    { subset := hs'
      small := hδ'20
      dens := hdens
      full := hfull
      centred := fun i hi ↦ hcen (ϖ i) (hmem i (hs' hi))
      contained := fun i hi ↦ by
        refine carrier_subset_unitBall_of_isCentred (ϖ i) (hcen (ϖ i) (hmem i (hs' hi)))
          (R₀ := 2 / 5 + (δ' : ℝ) / 4) (by positivity) (hmid (ϖ i) (hmem i (hs' hi))) ?_
        have hr0 : (0 : ℝ) < (δ' : ℝ) / 4 := by positivity
        have hr80 : (δ' : ℝ) / 4 ≤ 1 / 80 := by linarith
        have hreach := canonicalCover_reach_lt hr0 hr80
        linarith
      covers := fun i hi ↦ hcov i (hs' hi)
      maxDensity_le := by
        refine le_trans (maxDensity_nodes_le s' O (fun i ↦ handBackRep (O i) (ϖ i))
          (fun i hi ↦ hcov i (hs' hi))) ?_
        have hmono : Kakeya.maxDensity s' (fun i ↦ (O i).toConvexSpaceBody)
            ≤ (δ' : ENNReal) ^ (-qc) :=
          le_trans (Kakeya.maxDensity_mono (fun i ↦ (O i).toConvexSpaceBody) hs') hdens
        have hδE0 : (δ' : ENNReal) ≠ 0 := by simpa using ne_of_gt hδ'0
        have hδEt : (δ' : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
        calc (512 : ENNReal) * Kakeya.maxDensity s' (fun i ↦ (O i).toConvexSpaceBody)
            ≤ (δ' : ENNReal) ^ (-qc) * (δ' : ENNReal) ^ (-qc) := mul_le_mul' hthr hmono
          _ = (δ' : ENNReal) ^ (-(2 * qc)) := by
              rw [← ENNReal.rpow_add _ _ hδE0 hδEt]; ring_nf
      fullness_ge := hfg
      card_le := by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hs')
      multiplicity_le := by rw [hmulteq]; exact hret }

/-- **The producer at the site.**  `s' := fib`: the retained index set is the whole family, the
representative of `i` is the cover's node `ϖ i`, and the selection costs nothing —
`card_le` is `le_rfl` and `multiplicity_le` is the exact pushforward identity.

This is the theorem the eliminator's caller
`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover` consumes: it supplies
that theorem's `hcb` binder at `m := 0`, `s' := fib`, and — with `ηd := 3 qc`, `h3qc := le_rfl`
and `hL91` at `gain (…) + 3 qc` — leaves only `huni` and `hcnt` open. -/
theorem exists_centredHandBack_of_outerFamily
    {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (hδ'0 : 0 < δ') (hδ'20 : (δ' : ℝ) ≤ 1 / 20)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {qc : ℝ} (hqc0 : 0 < qc) (hthr : (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc))
    {α : Type u} (fib : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ fib, (Z' i).carrier ⊆ T₀.carrier)
    (hdens : Kakeya.maxDensity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-qc))
    (hfull : (δ' : ENNReal) ^ qc ≤ ShadedBody.fullness fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)) :
    ∃ U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)),
      CentredHandBack hsit hR T₀ 0 qc fib fib Z' U' := by
  have hδ'1 : δ' ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  refine exists_centredHandBack_of_outerFamily_subfamily hsit hR hτσ hδ'0 hδ'20 T₀ hqc0 hthr
    (Finset.Subset.refl fib) Z' hsub hdens hfull hfull ?_
  calc ShadedBody.multiplicity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)
      = 1 * ShadedBody.multiplicity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) := (one_mul _).symm
    _ ≤ (δ' : ENNReal) ^ (-(3 * qc)) * ShadedBody.multiplicity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) :=
        mul_le_mul' (one_le_rpow_neg hδ'0 hδ'1 (by linarith)) le_rfl


/-- **The `_data` sibling of the hand-back producer**.

Same construction as `Kakeya.VeryNotSticky.exists_centredHandBack_of_outerFamily_subfamily`,
which is byte-untouched above; the only change is that the canonical cover is taken through
`Kakeya.VeryNotSticky.exists_centredRepresentatives_data` instead of its projection, so the two
line-parameter estimates the count transport needs travel out with the hand-back **on the same
`U'`** instead of being re-derived from a second, unrelated cover.

The three exported rows are exactly the three
`Kakeya.VeryNotSticky.countTransport_of_contractedCover` asks for:

* `hmid` — `‖midpoint‖ ≤ 1` on the outer family, from
  `Kakeya.Tube.norm_midpoint_le_of_subset_ball` and `outerFamily_carrier_subset_closedBall`;
* `hfoot` — the node's midpoint within `δ'/4` of the member's line foot;
* `hdir` — the node's direction within `δ'/4` of the member's direction.

Without this sibling the site's two Props would come from two different constructions and would
have to be *asserted* to agree on `U'`; with it, they agree by construction. -/
theorem exists_centredHandBack_of_outerFamily_subfamily_data
    {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (hδ'0 : 0 < δ') (hδ'20 : (δ' : ℝ) ≤ 1 / 20)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {qc : ℝ} (hqc0 : 0 < qc) (hthr : (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc))
    {α : Type u} {fib s' : Finset α} (hs' : s' ⊆ fib)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ fib, (Z' i).carrier ⊆ T₀.carrier)
    (hdens : Kakeya.maxDensity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-qc))
    (hfull : (δ' : ENNReal) ^ qc ≤ ShadedBody.fullness fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody))
    (hfullS : (δ' : ENNReal) ^ qc ≤ (ShadedBody.fullness s'
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) : ENNReal))
    (hret : ShadedBody.multiplicity fib
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (-(3 * qc)) * ShadedBody.multiplicity s'
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)) :
    ∃ U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)),
      CentredHandBack hsit hR T₀ 0 qc fib s' Z' U' ∧
      (∀ i ∈ s', ‖(outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.midpoint‖ ≤ 1) ∧
      (∀ i ∈ s', ‖Tube.lineFoot
          (centringDilate (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.midpoint)
          ((outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.direction)
          - (U' i).toTube.midpoint‖ ≤ (δ' : ℝ) / 4) ∧
      (∀ i ∈ s', ‖(outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.direction
          - (U' i).toTube.direction‖ ≤ (δ' : ℝ) / 4) := by
  classical
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set O : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ outerFamily hsit.pos_ambient T₀ hR δ' Z' i with hO
  have hδ'1 : δ' ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hball : ∀ i ∈ fib,
      (O i).toTube.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    outerFamily_carrier_subset_closedBall hn hsit hR hτσ hsub
  obtain ⟨G, ϖ, hmem, -, hcovD, hcen, hmid, -, -, hfootD, hdirD⟩ :=
    exists_centredRepresentatives_data (E := EuclideanSpace ℝ (Fin 3)) hδ'0 hδ'20 fib
      (fun i ↦ (O i).toTube) hball
  -- the covering clause, rewritten at `normalise 0`
  have hcov : ∀ i ∈ fib, normalise 0 '' (O i).carrier ⊆ (ϖ i).carrier := by
    intro i hi
    rw [← centringDilate_image_eq_normalise_zero_image]
    exact hcovD i hi
  refine ⟨fun i ↦ handBackRep (O i) (ϖ i), ?_,
    fun i hi ↦ Tube.norm_midpoint_le_of_subset_ball hδ'0 (O i).toTube (hball i (hs' hi)),
    fun i hi ↦ hfootD i (hs' hi), fun i hi ↦ hdirD i (hs' hi)⟩
  have hsh : ∀ i ∈ s', (handBackRep (O i) (ϖ i)).shade = normalise 0 '' (O i).shade :=
    fun i hi ↦ handBackRep_shade_eq (O i) (ϖ i) (hcov i (hs' hi))
  -- the two pushforward clauses
  obtain ⟨hfg, -⟩ :=
    ledgerClauses_of_pushforward s' hδ'0 hδ'1 O (fun i ↦ handBackRep (O i) (ϖ i)) 0 hqc0.le hsh
      hfullS (rpow_two_mul_le_jacobian hδ'0 hqc0.le hthr)
  have hmulteq : ShadedBody.multiplicity s'
      (fun i ↦ (handBackRep (O i) (ϖ i)).toShadedBody)
      = ShadedBody.multiplicity s' (fun i ↦ (O i).toShadedBody) :=
    multiplicity_pushforward s' O (fun i ↦ handBackRep (O i) (ϖ i)) 0 hsh
  exact
    { subset := hs'
      small := hδ'20
      dens := hdens
      full := hfull
      centred := fun i hi ↦ hcen (ϖ i) (hmem i (hs' hi))
      contained := fun i hi ↦ by
        refine carrier_subset_unitBall_of_isCentred (ϖ i) (hcen (ϖ i) (hmem i (hs' hi)))
          (R₀ := 2 / 5 + (δ' : ℝ) / 4) (by positivity) (hmid (ϖ i) (hmem i (hs' hi))) ?_
        have hr0 : (0 : ℝ) < (δ' : ℝ) / 4 := by positivity
        have hr80 : (δ' : ℝ) / 4 ≤ 1 / 80 := by linarith
        have hreach := canonicalCover_reach_lt hr0 hr80
        linarith
      covers := fun i hi ↦ hcov i (hs' hi)
      maxDensity_le := by
        refine le_trans (maxDensity_nodes_le s' O (fun i ↦ handBackRep (O i) (ϖ i))
          (fun i hi ↦ hcov i (hs' hi))) ?_
        have hmono : Kakeya.maxDensity s' (fun i ↦ (O i).toConvexSpaceBody)
            ≤ (δ' : ENNReal) ^ (-qc) :=
          le_trans (Kakeya.maxDensity_mono (fun i ↦ (O i).toConvexSpaceBody) hs') hdens
        have hδE0 : (δ' : ENNReal) ≠ 0 := by simpa using ne_of_gt hδ'0
        have hδEt : (δ' : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
        calc (512 : ENNReal) * Kakeya.maxDensity s' (fun i ↦ (O i).toConvexSpaceBody)
            ≤ (δ' : ENNReal) ^ (-qc) * (δ' : ENNReal) ^ (-qc) := mul_le_mul' hthr hmono
          _ = (δ' : ENNReal) ^ (-(2 * qc)) := by
              rw [← ENNReal.rpow_add _ _ hδE0 hδEt]; ring_nf
      fullness_ge := hfg
      card_le := by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hs')
      multiplicity_le := by rw [hmulteq]; exact hret }

/-! ## A7 — `CountTransport` for the produced hand-back: the cheap route is CLOSED

`Kakeya.VeryNotSticky.countTransport_of_le` discharges the re-shaped `CountTransport` from the
hypothesis `∀ i ∈ s', (U' i).toConvexSpaceBody ≤ spineFamily … i` — the representative sits
*inside* the body it represents.  That hypothesis is **unavailable for the hand-back this file
produces**, and not by accident: the representative is a *container* of the normalised member, so
asking it also to be contained in the member forces the member to be `normalise`-stable, which a
body sitting away from the origin is not.

`normalise 0` contracts towards the origin by `8`, so a family every one of whose points has norm
`> 1/8` cannot contain its own normalised image. -/
theorem not_le_of_covers_of_far {δ' : NNReal}
    (O U : ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hOne : (O.carrier).Nonempty)
    (hcov : normalise 0 '' O.carrier ⊆ U.carrier)
    (hball : O.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hfar : ∀ z ∈ O.carrier, (1 : ℝ) / 8 < ‖z‖) :
    ¬ (U.toConvexSpaceBody ≤ O.toConvexSpaceBody) := by
  intro hle
  obtain ⟨z, hz⟩ := hOne
  have hzn : ‖z‖ ≤ 1 := by simpa using Metric.mem_closedBall.mp (hball hz)
  have hmem : normalise 0 z ∈ O.carrier := by
    have h1 : normalise 0 z ∈ U.carrier := hcov ⟨z, hz, rfl⟩
    have h2 : U.carrier ⊆ O.carrier := SetLike.coe_subset_coe.mpr hle
    exact h2 h1
  have hnorm : ‖normalise 0 z‖ = ‖z‖ / 8 := by
    rw [show normalise 0 z = (8 : ℝ)⁻¹ • z by simp [normalise], norm_smul, norm_inv,
      Real.norm_ofNat]
    ring
  have := hfar _ hmem
  rw [hnorm] at this
  linarith

/-! ## V-2 — the producer's hypothesis list, jointly satisfied on a two-member family -/

/-- A family shaded by the whole of itself is full.

**Name note (the estimate-1 class).**  `Kakeya.fullness_eq_one_of_shade_eq_carrier`
(`Kakeya/Factoring/ParentCountHypothesis.lean:318`) is the same fact under a `0 < ∑` / `∑ ≠ ⊤`
hypothesis pair, and it is **not reachable** from this leaf's import closure (measured: the
identifier is unknown after `import …Reduction.SpineCentringCover`).  This copy therefore carries
a different name on purpose, so that the tree never holds two spellings of one name; the right
disposition is a shared home in `Kakeya/Shading.lean`, which is a Regulator item and not this
pack's. -/
theorem fullness_eq_one_of_fullyShaded {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {ι : Type*} (s : Finset ι) (V : ι → ShadedBody F)
    (hsh : ∀ i ∈ s, (V i).shade = (V i).carrier)
    (hpos : (∑ i ∈ s, volume (V i).carrier) ≠ 0) :
    ShadedBody.fullness s V = 1 := by
  have htop : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤ := by
    refine (ENNReal.sum_lt_top.mpr fun i _ ↦ ?_).ne
    exact (V i).isCompact.measure_lt_top
  have h : ((ShadedBody.fullness s V : NNReal) : ENNReal) = 1 := by
    rw [ShadedBody.fullness_def, Finset.sum_congr rfl (fun i hi ↦ by rw [hsh i hi])]
    exact ENNReal.div_self hpos htop
  exact_mod_cast h

/-- **V-2 for `exists_centredHandBack_of_outerFamily`.**

Every hypothesis of the producer is discharged simultaneously on a **two-member, geometrically
distinct** family — two parallel `4δ'`-tubes with different midpoints inside the ambient unit
tube — and the producer then returns the hand-back.  This is the control 
requires before a condition clause is consumed: without it, "the producer compiles" is not
evidence that its hypotheses can hold together.

The two thresholds are the only scalar constraints, and both are `δ'`-thresholds:
`512 ≤ (δ')^{-qc}` (`exists_threshold_centringJacobian`) and
`(δ')^{qc} ≤ (outerLoss (C_N 3))⁻¹` (`Kakeya.ML2Reduction.exists_threshold_outerLoss`, the same
absolute-constant-as-threshold mechanism). -/
theorem exists_centredHandBack_nonvacuity {δ' : NNReal} (hδ0 : 0 < δ')
    (hδ20 : (δ' : ℝ) ≤ 1 / 20) {qc : ℝ} (hqc0 : 0 < qc)
    (hthr : (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc))
    (hδloss : (δ' : ENNReal) ^ qc
      ≤ ((Kakeya.ML2Reduction.outerLoss (Tube.normalization.C 3))⁻¹ : NNReal))
    (u v : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ Z' : Fin 2 → ShadedTube (4 * δ') (EuclideanSpace ℝ (Fin 3)),
      (Z' 0).midpoint ≠ (Z' 1).midpoint ∧
      (∀ i ∈ (Finset.univ : Finset (Fin 2)), (Z' i).carrier ⊆
        (Tube.ofMidpointDirection (1 : NNReal) 0 u hu).carrier) ∧
      Kakeya.maxDensity (Finset.univ : Finset (Fin 2))
          (fun i ↦ (outerFamily (isRescalingSituation_witness hδ0 (by linarith)).pos_ambient
            (Tube.ofMidpointDirection (1 : NNReal) 0 u hu)
            (lt_of_lt_of_le zero_lt_one (Tube.normalization.one_le_C 3)) δ' Z' i
              ).toConvexSpaceBody)
        ≤ (δ' : ENNReal) ^ (-qc) ∧
      (δ' : ENNReal) ^ qc ≤ ShadedBody.fullness (Finset.univ : Finset (Fin 2))
          (fun i ↦ (outerFamily (isRescalingSituation_witness hδ0 (by linarith)).pos_ambient
            (Tube.ofMidpointDirection (1 : NNReal) 0 u hu)
            (lt_of_lt_of_le zero_lt_one (Tube.normalization.one_le_C 3)) δ' Z' i
              ).toShadedBody) ∧
      ∃ U' : Fin 2 → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)),
        CentredHandBack (isRescalingSituation_witness hδ0 (by linarith))
          (lt_of_lt_of_le zero_lt_one (Tube.normalization.one_le_C 3))
          (Tube.ofMidpointDirection (1 : NNReal) 0 u hu) 0 qc
          (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset (Fin 2)) Z' U' := by
  classical
  have hδ4 : 4 * (δ' : ℝ) ≤ 1 := by linarith
  have hR : (0 : ℝ) < Tube.normalization.C 3 :=
    lt_of_lt_of_le zero_lt_one (Tube.normalization.one_le_C 3)
  have hR1 : (1 : ℝ) ≤ Tube.normalization.C 3 := Tube.normalization.one_le_C 3
  have h4δ0 : 0 < 4 * δ' := by positivity
  have h4δ1 : 4 * δ' ≤ 1 := by exact_mod_cast hδ4
  set hsit := isRescalingSituation_witness hδ0 hδ4 with hsitdef
  set T₀ : Tube 1 (EuclideanSpace ℝ (Fin 3)) := Tube.ofMidpointDirection 1 0 u hu with hT₀
  set c : EuclideanSpace ℝ (Fin 3) := (4 : ℝ)⁻¹ • v with hc
  set Zt : Fin 2 → Tube (4 * δ') (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ Tube.ofMidpointDirection (4 * δ') (if i = 0 then 0 else c) u hu with hZt
  set Z' : Fin 2 → ShadedTube (4 * δ') (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ fullShadeTube (Zt i) with hZ'
  have hcnorm : ‖c‖ = (4 : ℝ)⁻¹ := by
    rw [hc, norm_smul, norm_inv, Real.norm_ofNat, hv, mul_one]
  have hcne : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcnorm
    norm_num at hcnorm
  -- the two tubes sit inside the ambient one
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
  -- the density: at most the cardinality, and `2 ≤ 512 ≤ (δ')^{-qc}`
  have hdens : Kakeya.maxDensity (Finset.univ : Finset (Fin 2))
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-qc) := by
    refine le_trans (Kakeya.maxDensity_le_card _ _) (le_trans ?_ hthr)
    simp only [Finset.card_univ, Fintype.card_fin]
    norm_num
  -- the fullness: the members are fully shaded, and the outer replacement costs `outerLoss`
  have hZfull : ShadedBody.fullness (Finset.univ : Finset (Fin 2))
      (fun i ↦ (Z' i).toShadedBody) = 1 := by
    refine fullness_eq_one_of_fullyShaded _ _ (fun i _ ↦ rfl) ?_
    have h0 : volume (Zt 0).carrier ≠ 0 := (Tube.volume_pos_and_lt_top h4δ0 h4δ1 (Zt 0)).1.ne'
    intro hsum
    exact h0 ((Finset.sum_eq_zero_iff.mp hsum) 0 (Finset.mem_univ 0))
  have hfull : (δ' : ENNReal) ^ qc ≤ ShadedBody.fullness (Finset.univ : Finset (Fin 2))
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) := by
    have h := Kakeya.ML2Reduction.outerFamily_le_fullness (E := EuclideanSpace ℝ (Fin 3))
      (s := (Finset.univ : Finset (Fin 2))) (𝕋 := Z') (T₀ := T₀) (by simp) hsit hR hR1
      (by push_cast; rw [div_one]) hsub
    rw [hZfull, mul_one] at h
    exact le_trans hδloss (by exact_mod_cast h)
  refine ⟨Z', ?_, hsub, hdens, hfull, ?_⟩
  · have h0 : (Z' 0).midpoint = 0 := by
      simp [hZ', hZt]
    have h1 : (Z' 1).midpoint = c := by
      simp [hZ', hZt]
      module
    rw [h0, h1]
    exact fun h ↦ hcne h.symm
  · exact exists_centredHandBack_of_outerFamily hsit hR (by push_cast; rw [div_one]) hδ0 hδ20
      T₀ hqc0 hthr Finset.univ Z' hsub hdens hfull

end Kakeya.VeryNotSticky

end
