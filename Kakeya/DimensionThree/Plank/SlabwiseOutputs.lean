/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabwiseInputs
public import Kakeya.DimensionThree.Plank.PublicConstants
public import Kakeya.DimensionThree.Plank.AssignedSlabFamily
public import Kakeya.DimensionThree.Plank.ShadingTransport

/-!
# The symbolic multiplicity reduction, and Items 3 and 4 on the final family

The first section isolates the *algebra* of the Item 4 multiplicity reduction with purely symbolic
coefficients; the two that follow instantiate Items 3 and 4 on the final dominant/good-slab family.

Neither item needs new mathematics on the final family: both are instantiations of an already
fully symbolic theorem at the canonical data

* `τ := Plank.ThickenedPlank θ b hθ1 hb1`, `σ := Slab θ hθ1`, `repr := R₁.repr`,
* `𝒮 := R₁.indexSet.image slabOf`, the canonical slab family,
* `active := fun S => R₁.indexSet.filter (fun Q => slabOf Q = S)`, the canonical slab fibre,
* `Yθ` exactly the thickened shading that the assigned Item 2 route builds.

In both cases the coefficient comparison against the public statement — `c3 · a ^ ε ≤ cOv` for
Item 3, and the Item 4 ledger inequality for Item 4 — is taken as a *hypothesis* rather than
manufactured here, so no power of `a`, `η` or `ε` is spent in this module and the existing exponent
ledgers are preserved verbatim.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

variable {ι τ σ : Type*}

/-!
## The Item 4 multiplicity reduction, with symbolic coefficients

Item 4 of GWZ Lemma 6.13 (`Kakeya.plankReduction`) reduces the multiplicity of the input
plank family to that of the thickened per-slab family.  This section isolates the *algebra*
of that reduction with
**purely symbolic** coefficients: no power of `a` occurs anywhere below, so the
exponent ledger is instantiated once, at the very end, by the caller.

The reduction is exposed as six separate steps, so that the exponent check can be read off one
inequality at a time:

1. `Kakeya.multiplicityStep_refinementComparison` — the refinement comparison from the original
   family to the final refined family, costing `rRef⁻¹`.
2. `Kakeya.multiplicityStep_slabSelection` — the aggregate slab selection (slab mass
   decomposition), costing `cOv⁻¹` and producing one slab `S`.
3. `ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset` — the common shading-union
   denominator; the thickened union is contained in the plank union, so the denominators compare
   the right way and the mass comparison passes to the multiplicities.
4. `Kakeya.sum_le_card_mul_of_fibre_card_le` — the representative fibre-cardinality comparison:
   grouping the assigned planks by their representative bounds the numerator by
   `#(active S) · Nb · volP`.
5. `Kakeya.multiplicityStep_carrierVolumeRatio` — the carrier-volume comparison
   `ratio · volP ≤ |Q_carrier t|`, summed to `#(active S) · ratio · volP ≤ ∑_t |Q_carrier t|`.
6. `Kakeya.multiplicityStep_fullnessLower` — the thickened fullness lower bound
   `β · ∑_t |Q_carrier t| ≤ ∑_t |Y_θ t|`.

Steps 4–6 combine in `Kakeya.multiplicityStep_numeratorComparison`, and all six in
`Kakeya.multiplicityReduction_of_refinement_and_fullness`.

**Where the factor `a / (b θ)` enters.**  It enters at step 5 and nowhere else, as the symbolic
`ratio`.  Step 4 bounds the numerator by a plank-volume budget `volP` per assigned plank; step 6
converts the thickened family's mass into its *carrier* volume; and only step 5 relates the two
volumes.  Instantiated, `ratio = θ b / a` is the ratio of the thickened representative's volume
`θ b · b · 1` to the plank's volume `a · b · 1`, so the surviving factor in the final coefficient is
its reciprocal times the fibre size, namely `a N / (b θ)`.  This is genuine geometry, not
bookkeeping: it is recovered only because the numerator uses the *density* lower bound `β` on the
thickened family (step 6) rather than a density-free count.  A density-free numerator would lose
exactly this factor.

`Kakeya.multiplicityReduction_of_refinement_and_fullness_ratio` records the assembled statement in
the shape Item 4 asks for, with the coefficient
`Cgeom · rRef⁻¹ · cOv⁻¹ · β⁻¹ · ((a N) / (b θ))`.

Note that only the *upper* fibre-cardinality bound is used.  A lower bound
`N / c_N ≤ #(fibre over t)` is what the *reverse* multiplicity comparison would need; it is not a
hypothesis of any statement below.
-/

/-! ### Step 1: the refinement comparison -/

/-- **Step 1.**  A `rRef`-refinement bounds the original multiplicity by `rRef⁻¹` times the refined
one.  Named wrapper of `ShadedBody.multiplicity_le_of_isCRefinement`, exposed separately so that
the Item 4 exponent check can point at one declaration per step. -/
theorem multiplicityStep_refinementComparison {s s' : Finset ι}
    {Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {rRef : ℝ≥0} (hrRef : rRef ≠ 0)
    (href : ShadedBody.IsCRefinement s' Y' s Y rRef) :
    ShadedBody.multiplicity s Y ≤ (rRef : ENNReal)⁻¹ * ShadedBody.multiplicity s' Y' :=
  ShadedBody.multiplicity_le_of_isCRefinement (c := rRef) (hc := hrRef) (h := href)

/-! ### Step 2: the aggregate slab selection -/

/-- **Step 2.**  The aggregate slab-mass decomposition selects one slab at the cost of `cOv⁻¹`.
Named wrapper of `Kakeya.multiplicityReductionAlgebra_of_sum`. -/
theorem multiplicityStep_slabSelection {cOv : ℝ≥0} (hcOv : 0 < cOv)
    (𝒮 : Finset σ) (h𝒮 : 𝒮.Nonempty)
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (Pass : σ → Finset ι)
    (hpart : ∑ S ∈ 𝒮, (∑ i ∈ Pass S, volume (Y' i).shade) = ∑ i ∈ s', volume (Y' i).shade)
    (hov : (cOv : ENNReal) * (∑ S ∈ 𝒮, volume (⋃ i ∈ Pass S, (Y' i).shade))
      ≤ volume (⋃ i ∈ s', (Y' i).shade)) :
    ∃ S ∈ 𝒮, ShadedBody.multiplicity s' Y'
      ≤ (cOv : ENNReal)⁻¹ * ShadedBody.multiplicity (Pass S) Y' :=
  multiplicityReductionAlgebra_of_sum cOv hcOv 𝒮 h𝒮 s' Y' Pass hpart hov

/-! ### Step 4: the representative fibre-cardinality comparison -/

open scoped Classical in
/-- **Step 4.**  If `repr` maps `P` into `T`, every fibre of `repr` over `T` has at most `Nb`
elements, and `f` is bounded by `M` on `P`, then `∑_{i ∈ P} f i ≤ #T · (Nb · M)`.

Pure finite double counting: `P` is partitioned by the fibres of `repr`. -/
theorem sum_le_card_mul_of_fibre_card_le (P : Finset ι) (T : Finset τ) (repr : ι → τ)
    (f : ι → ENNReal) {M Nb : ENNReal}
    (hmaps : ∀ i ∈ P, repr i ∈ T)
    (hM : ∀ i ∈ P, f i ≤ M)
    (hfibre : ∀ t ∈ T, ((P.filter fun i => repr i = t).card : ENNReal) ≤ Nb) :
    ∑ i ∈ P, f i ≤ (T.card : ENNReal) * (Nb * M) := by
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  calc
    ∑ t ∈ T, ∑ i ∈ P with repr i = t, f i ≤ ∑ _t ∈ T, Nb * M :=
      Finset.sum_le_sum fun t ht =>
        (Finset.sum_le_sum fun i hi => hM i (Finset.mem_filter.mp hi).1).trans
          (by rw [Finset.sum_const, nsmul_eq_mul]; exact mul_le_mul_left (hfibre t ht) M)
    _ = (T.card : ENNReal) * (Nb * M) := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Step 5: the carrier-volume comparison -/

/-- **Step 5.**  The carrier-volume comparison, summed.  If every member of the thickened family
has carrier volume at least `ratio · volP`, then the total carrier volume is at least
`#T · ratio · volP`.

This is the *only* step at which the plank-volume/carrier-volume ratio enters; instantiated,
`ratio = θ b / a`, whose reciprocal is the `a / (b θ)` of Item 4. -/
theorem multiplicityStep_carrierVolumeRatio (T : Finset τ)
    (Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))) {ratio volP : ENNReal}
    (hQ : ∀ t ∈ T, ratio * volP ≤ volume (Yθ t).carrier) :
    (T.card : ENNReal) * (ratio * volP) ≤ ∑ t ∈ T, volume (Yθ t).carrier := by
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum hQ

/-! ### Step 6: the thickened fullness lower bound -/

/-- **Step 6.**  A fullness lower bound `β ≤ λ(T, Yθ)` is exactly the mass inequality
`β · ∑_t |carrier| ≤ ∑_t |shade|`. -/
theorem multiplicityStep_fullnessLower (T : Finset τ)
    (Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))) {β : ℝ≥0}
    (hfull : β ≤ ShadedBody.fullness T Yθ) :
    (β : ENNReal) * ∑ t ∈ T, volume (Yθ t).carrier ≤ ∑ t ∈ T, volume (Yθ t).shade := by
  refine (mul_le_mul_left (ENNReal.coe_le_coe.mpr hfull) _).trans ?_
  rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul]

/-! ### Steps 4–6 combined: the numerator comparison -/

open scoped Classical in
/-- **Steps 4–6.**  The numerator comparison: the total shading mass of the planks assigned to a
slab is at most `K` times the total shading mass of the thickened family over that slab, provided

* every assigned plank has shading mass at most `volP` (`hPvol`);
* every representative fibre has at most `Nb` members (`hfibre`, step 4);
* every thickened carrier has volume at least `ratio · volP` (`hQ`, step 5);
* the thickened family has fullness at least `β` (`hfull`, step 6);
* and the coefficients satisfy the multiplicative budget `Nb ≤ K · β · ratio` (`hK`).

Written multiplicatively rather than as `K ≥ Nb / (β · ratio)` to avoid all division in
`ℝ≥0∞`. -/
theorem multiplicityStep_numeratorComparison (P : Finset ι) (T : Finset τ)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))) (repr : ι → τ)
    {β : ℝ≥0} {K Nb volP ratio : ENNReal}
    (hmaps : ∀ i ∈ P, repr i ∈ T)
    (hPvol : ∀ i ∈ P, volume (Y' i).shade ≤ volP)
    (hfibre : ∀ t ∈ T, ((P.filter fun i => repr i = t).card : ENNReal) ≤ Nb)
    (hQ : ∀ t ∈ T, ratio * volP ≤ volume (Yθ t).carrier)
    (hfull : β ≤ ShadedBody.fullness T Yθ)
    (hK : Nb ≤ K * (β : ENNReal) * ratio) :
    ∑ i ∈ P, volume (Y' i).shade ≤ K * ∑ t ∈ T, volume (Yθ t).shade := by
  calc
    ∑ i ∈ P, volume (Y' i).shade ≤ (T.card : ENNReal) * (Nb * volP) :=
      sum_le_card_mul_of_fibre_card_le P T repr _ hmaps hPvol hfibre
    _ ≤ (T.card : ENNReal) * (K * (β : ENNReal) * ratio * volP) :=
      mul_le_mul_right (mul_le_mul_left hK volP) _
    _ = K * (β : ENNReal) * ((T.card : ENNReal) * (ratio * volP)) := by ring
    _ ≤ K * (β : ENNReal) * ∑ t ∈ T, volume (Yθ t).carrier :=
      mul_le_mul_right (multiplicityStep_carrierVolumeRatio T Yθ hQ) _
    _ = K * ((β : ENNReal) * ∑ t ∈ T, volume (Yθ t).carrier) := by ring
    _ ≤ K * ∑ t ∈ T, volume (Yθ t).shade :=
      mul_le_mul_right (multiplicityStep_fullnessLower T Yθ hfull) _

/-! ### The assembled reduction -/

/-- Scalar cancellation of the two refinement constants against their reciprocals. -/
private lemma ennreal_inv_inv_mul_cancel {r c : ℝ≥0} (hr : r ≠ 0) (hc : c ≠ 0) (C x : ENNReal) :
    (r : ENNReal)⁻¹ * ((c : ENNReal)⁻¹ * (C * (r : ENNReal) * (c : ENNReal) * x)) = C * x := by
  -- (extracted by Fuse golfer)
  rw [show (r : ENNReal)⁻¹ * ((c : ENNReal)⁻¹ * (C * (r : ENNReal) * (c : ENNReal) * x))
      = ((r : ENNReal)⁻¹ * (r : ENNReal)) * (((c : ENNReal)⁻¹ * (c : ENNReal)) * (C * x)) from by
      ring,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hr) ENNReal.coe_ne_top,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hc) ENNReal.coe_ne_top, one_mul, one_mul]

/-- Scalar cancellation of the two refinement constants and the fullness constant against their
reciprocals. -/
private lemma ennreal_inv_inv_inv_mul_cancel {r c β : ℝ≥0} (hr : r ≠ 0) (hc : c ≠ 0) (hβ : β ≠ 0)
    (C u v : ENNReal) :
    C * (r : ENNReal)⁻¹ * (c : ENNReal)⁻¹ * (β : ENNReal)⁻¹ * u * (r : ENNReal) * (c : ENNReal) *
      (β : ENNReal) * v = C * (u * v) := by
  -- (extracted by Fuse golfer)
  rw [show C * (r : ENNReal)⁻¹ * (c : ENNReal)⁻¹ * (β : ENNReal)⁻¹ * u * (r : ENNReal) *
        (c : ENNReal) * (β : ENNReal) * v
      = ((r : ENNReal)⁻¹ * (r : ENNReal)) * (((c : ENNReal)⁻¹ * (c : ENNReal)) *
        (((β : ENNReal)⁻¹ * (β : ENNReal)) * (C * (u * v)))) from by ring,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hr) ENNReal.coe_ne_top,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hc) ENNReal.coe_ne_top,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hβ) ENNReal.coe_ne_top, one_mul, one_mul,
    one_mul]

open scoped Classical in
/-- **The Item 4 multiplicity reduction, fully symbolic.**  Every coefficient is a bare symbol:
`rRef` is the refinement constant, `cOv` the slab-overlap constant, `β` the thickened fullness
lower bound, `volP` the per-plank shading-mass budget, `Nb` the fibre-cardinality budget, `ratio`
the carrier/plank volume ratio, and `Cfinal` the resulting coefficient, tied to the others by the
single multiplicative budget `hCfinal`.  **No power of `a` and no power of `δ` appears**; the
exponent ledger is instantiated only by the caller.

The six checked steps are `Kakeya.multiplicityStep_refinementComparison`,
`Kakeya.multiplicityStep_slabSelection`,
`ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset`,
`Kakeya.sum_le_card_mul_of_fibre_card_le`, `Kakeya.multiplicityStep_carrierVolumeRatio` and
`Kakeya.multiplicityStep_fullnessLower`. -/
theorem multiplicityReduction_of_refinement_and_fullness
    {s s' : Finset ι} {Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))} (repr : ι → τ)
    (𝒮 : Finset σ) (Pass : σ → Finset ι) (active : σ → Finset τ)
    {rRef cOv β : ℝ≥0} {Cfinal Nb volP ratio : ENNReal}
    (hrRef : rRef ≠ 0) (hcOv : 0 < cOv) (h𝒮 : 𝒮.Nonempty)
    (href : ShadedBody.IsCRefinement s' Y' s Y rRef)
    (hpart : ∑ S ∈ 𝒮, (∑ i ∈ Pass S, volume (Y' i).shade) = ∑ i ∈ s', volume (Y' i).shade)
    (hov : (cOv : ENNReal) * (∑ S ∈ 𝒮, volume (⋃ i ∈ Pass S, (Y' i).shade))
      ≤ volume (⋃ i ∈ s', (Y' i).shade))
    (hmaps : ∀ S ∈ 𝒮, ∀ i ∈ Pass S, repr i ∈ active S)
    (hunion : ∀ S ∈ 𝒮, (⋃ t ∈ active S, (Yθ t).shade) ⊆ ⋃ i ∈ Pass S, (Y' i).shade)
    (hPvol : ∀ S ∈ 𝒮, ∀ i ∈ Pass S, volume (Y' i).shade ≤ volP)
    (hfibre : ∀ S ∈ 𝒮, ∀ t ∈ active S,
      (((Pass S).filter fun i => repr i = t).card : ENNReal) ≤ Nb)
    (hcarrierVolume : ∀ S ∈ 𝒮, ∀ t ∈ active S, ratio * volP ≤ volume (Yθ t).carrier)
    (hfull : ∀ S ∈ 𝒮, β ≤ ShadedBody.fullness (active S) Yθ)
    (hCfinal : Nb ≤ Cfinal * (rRef : ENNReal) * (cOv : ENNReal) * (β : ENNReal) * ratio) :
    ∃ S ∈ 𝒮, ShadedBody.multiplicity s Y
      ≤ Cfinal * ShadedBody.multiplicity (active S) Yθ := by
  obtain ⟨S, hS, hstep2⟩ := multiplicityStep_slabSelection hcOv 𝒮 h𝒮 s' Y' Pass hpart hov
  have hmul : ShadedBody.multiplicity (Pass S) Y'
      ≤ Cfinal * (rRef : ENNReal) * (cOv : ENNReal) * ShadedBody.multiplicity (active S) Yθ :=
    ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset (Pass S) Y' (active S) Yθ _
      (hunion S hS)
      (multiplicityStep_numeratorComparison (Pass S) (active S) Y' Yθ repr (hmaps S hS)
        (hPvol S hS) (hfibre S hS) (hcarrierVolume S hS) (hfull S hS) hCfinal)
  exact ⟨S, hS, (multiplicityStep_refinementComparison hrRef href).trans
    ((mul_le_mul_right (hstep2.trans (mul_le_mul_right hmul _)) _).trans_eq
      (ennreal_inv_inv_mul_cancel hrRef hcOv.ne' _ _))⟩

/-- The scalar cancellation behind the Item 4 coefficient: the plank/carrier volume ratio
`θ b / a` cancels against the Item 4 factor `(a N) / (b θ)`, leaving the fibre size `N`. -/
theorem nnreal_thickenedRatio_mul_cancel {a b θ : ℝ≥0} (N : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ) :
    ((a * (N : ℝ≥0)) / (b * θ)) * (θ * b / a) = (N : ℝ≥0) := by
  rw [div_mul_div_comm, show a * (N : ℝ≥0) * (θ * b) = (N : ℝ≥0) * (b * θ * a) by ring,
    mul_div_assoc, div_self (by positivity : (0 : ℝ≥0) < b * θ * a).ne', mul_one]

open scoped Classical in
/-- **The Item 4 multiplicity reduction, in the shape Item 4 asks for.**  Instantiation of
`Kakeya.multiplicityReduction_of_refinement_and_fullness` at the geometric budgets
`Nb = c_N · N` and `ratio = θ b / a`, giving the coefficient
`Cgeom · rRef⁻¹ · cOv⁻¹ · β⁻¹ · ((a N) / (b θ))`.

Still fully symbolic in `a`, `b`, `θ`, `N` and every constant: no power of `a`
occurs.  The factor `(a N) / (b θ)` is the reciprocal of the step-5 carrier/plank volume ratio
times the fibre size, and enters only through `hcarrierVolume`. -/
theorem multiplicityReduction_of_refinement_and_fullness_ratio
    {s s' : Finset ι} {Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))} (repr : ι → τ)
    (𝒮 : Finset σ) (Pass : σ → Finset ι) (active : σ → Finset τ)
    {a b θ rRef cOv β cN Cgeom : ℝ≥0} {N : ℕ} {volP : ENNReal}
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ)
    (hrRef : rRef ≠ 0) (hcOv : 0 < cOv) (hβ : 0 < β) (hgeom : cN ≤ Cgeom)
    (h𝒮 : 𝒮.Nonempty)
    (href : ShadedBody.IsCRefinement s' Y' s Y rRef)
    (hpart : ∑ S ∈ 𝒮, (∑ i ∈ Pass S, volume (Y' i).shade) = ∑ i ∈ s', volume (Y' i).shade)
    (hov : (cOv : ENNReal) * (∑ S ∈ 𝒮, volume (⋃ i ∈ Pass S, (Y' i).shade))
      ≤ volume (⋃ i ∈ s', (Y' i).shade))
    (hmaps : ∀ S ∈ 𝒮, ∀ i ∈ Pass S, repr i ∈ active S)
    (hunion : ∀ S ∈ 𝒮, (⋃ t ∈ active S, (Yθ t).shade) ⊆ ⋃ i ∈ Pass S, (Y' i).shade)
    (hPvol : ∀ S ∈ 𝒮, ∀ i ∈ Pass S, volume (Y' i).shade ≤ volP)
    (hfibre : ∀ S ∈ 𝒮, ∀ t ∈ active S,
      (((Pass S).filter fun i => repr i = t).card : ENNReal) ≤ ((cN * (N : ℝ≥0) : ℝ≥0) : ENNReal))
    (hcarrierVolume : ∀ S ∈ 𝒮, ∀ t ∈ active S,
      ((θ * b / a : ℝ≥0) : ENNReal) * volP ≤ volume (Yθ t).carrier)
    (hfull : ∀ S ∈ 𝒮, β ≤ ShadedBody.fullness (active S) Yθ) :
    ∃ S ∈ 𝒮, ShadedBody.multiplicity s Y
      ≤ (Cgeom : ENNReal) * (rRef : ENNReal)⁻¹ * (cOv : ENNReal)⁻¹ * (β : ENNReal)⁻¹ *
          (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal) *
            ShadedBody.multiplicity (active S) Yθ := by
  refine multiplicityReduction_of_refinement_and_fullness repr 𝒮 Pass active hrRef hcOv h𝒮 href
    hpart hov hmaps hunion hPvol hfibre hcarrierVolume hfull ?_
  rw [ennreal_inv_inv_inv_mul_cancel hrRef hcOv.ne' hβ.ne', ← ENNReal.coe_mul,
    nnreal_thickenedRatio_mul_cancel N ha hb hθ, ← ENNReal.coe_mul]
  exact ENNReal.coe_le_coe.mpr (mul_le_mul_left hgeom _)

/-!
## Item 3 of GWZ Lemma 6.13 on the final dominant/good-slab family

Item 3 needs no new mathematics on the final family: `Plank.sum_volume_sharedSlabDilation_le` is
already generic in the representative type, already filters an arbitrary active family `𝒯` by
`slabOf`, and already leaves the right-hand union free.  Instantiating it at

* `τ := Plank.ThickenedPlank θ b hθ1 hb1`,
* `anchor := fun Q => Q.toPrismNDim`,
* `repr := R₁.repr`, `𝒯 := R₁.indexSet`, `𝒮 := R₁.indexSet.image slabOf`,
* the shading `Yθ` that `Kakeya.slabwiseRepresentativeShading` builds,

produces the public clause verbatim.  The only extra step is the coefficient: the underlying theorem
concludes at the absolute `cOv`, while the public statement asks for `c3 · a ^ ε`, so the weakening
`c3 · a ^ ε ≤ cOv` is taken as a hypothesis rather than manufactured here.  No power of `a`, `η` or
`ε` is spent inside Item 3.

The summation partition is `Plank.assignedSlabFamily`, supplied inside
`Plank.sum_volume_sharedSlabDilation_le` by
`Plank.sharedSlabThickenedShadingDilation_shade_subset_assigned`.  The geometric family
`Plank.inSlabFamilyC` is *not* used as a partition; it may only appear as the free superfamily
`Pass`, which exists so that the caller can pass the family the preassembly's aggregate slab-mass
clause happens to be phrased with.
-/

open scoped Classical in
/-- **Item 3 of GWZ Lemma 6.13 on the final dominant/good-slab family.**

The conclusion is the public Item 3 clause of `ShadedPlank.reduction_to_slab`, at the canonical
active family `𝒯 = R₁.indexSet`, the canonical slab map `slabOf`, and exactly the thickened shading
`Yθ` that the assigned Item 2 route uses — same `Cbox`, same dominant shading, same anchor.

`Pass` is the free superfamily of `Plank.sum_volume_sharedSlabDilation_le`: the exact partition of
the mass is `Plank.assignedSlabFamily`, and `Pass` only carries the aggregate hypothesis `hov` in
whatever family the preassembly states it. -/
theorem slabwiseUnionVolume
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    {ι : Type*} {cThk Cbox cOv c3 : ℝ≥0} {ε : ℝ}
    (s₁ : Finset ι) (V : ι → Plank a b hab hb1)
    (R₁ : Plank.ThickenedRepr s₁ V θ hθ1 cThk)
    (Yfinal : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    (Pass : Slab θ hθ1 → Finset ι) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hPass : ∀ S ∈ R₁.indexSet.image slabOf,
      Plank.assignedSlabFamily s₁ R₁.repr slabOf S ⊆ Pass S)
    (hov : (cOv : ENNReal) *
          ∑ S ∈ R₁.indexSet.image slabOf,
            volume (⋃ i ∈ Pass S, (Yfinal i).shade)
        ≤ volume (⋃ i ∈ s₁, (Yfinal i).shade))
    (hU : (⋃ i ∈ s₁, (Yfinal i).shade) ⊆ U)
    (hc3 : (c3 * a ^ ε : ℝ≥0) ≤ cOv) :
    ((c3 * a ^ ε : ℝ≥0) : ENNReal) *
        ∑ S ∈ R₁.indexSet.image slabOf,
          volume (⋃ Q ∈ R₁.indexSet.filter (fun Q => slabOf Q = S),
            (Plank.sharedSlabThickenedShadingDilation Cbox s₁ Yfinal
              (fun Q => Q.toPrismNDim) R₁.repr slabOf Q).shade)
      ≤ volume U := by
  have hbase :=
    Plank.sum_volume_sharedSlabDilation_le Cbox s₁ Yfinal (fun Q => Q.toPrismNDim) R₁.repr slabOf
      (Finset.image slabOf R₁.indexSet) Pass hPass cOv hov R₁.indexSet U hU
  exact (mul_le_mul_left (ENNReal.coe_le_coe.2 hc3) _).trans hbase

/-!
## Item 4 of GWZ Lemma 6.13 on the final dominant/good-slab family

`Kakeya.multiplicityReduction_of_refinement_and_fullness_ratio` is fully symbolic in the index type
`ι`, the representative type `τ` and the slab type `σ`, and it already produces the public factor
`((a N) / (b θ))`.  Threading Item 4 onto the final family is therefore an instantiation:

* `τ := Plank.ThickenedPlank θ b hθ1 hb1`, `σ := Slab θ hθ1`, `repr := R₁.repr`;
* `𝒮 := R₁.indexSet.image slabOf`, the canonical slab family;
* `Pass := Plank.assignedSlabFamily s₁ R₁.repr slabOf`, forced by the partition input
  `Plank.sum_volume_assignedSlabFamily_eq`;
* `active := fun S => R₁.indexSet.filter (fun Q => slabOf Q = S)`, the canonical slab fibre;
* `Yθ` exactly the thickened shading of Items 2 and 3.

Three hypotheses need a short argument rather than being passed through:

* `hmaps` — an assigned index's representative lies in the canonical fibre of its own slab;
* `hunion` — `Plank.sharedSlabThickenedShadingDilation_shade_subset_assigned`, the same inclusion
  Item 3 uses;
* `hfibre` — the fibre bound at the public `cN = 2`, from `Kakeya.fibre_bounds_two`
  after `Plank.filter_repr_assignedSlabFamily_eq` identifies the assigned fibre with the `s₁` fibre.
  No second pigeonhole is run.

The symbolic theorem concludes at the coefficient `Cgeom · rRef⁻¹ · cOv⁻¹ · β⁻¹`, while the public
statement asks for `c4 · a ^ (-ε) · a ^ (-(4η))`; as with Item 3 the comparison is taken as a
hypothesis, so no exponent is manufactured here and the existing ledger is preserved.
-/

open scoped Classical in
private lemma multiplicityComparison_hpart
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    {ι : Type*} {cThk : ℝ≥0} (s₁ : Finset ι) (V : ι → Plank a b hab hb1)
    (R₁ : Plank.ThickenedRepr s₁ V θ hθ1 cThk)
    (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1) (𝒮 : Finset (Slab θ hθ1))
    (hslab : ∀ i ∈ s₁, slabOf (R₁.repr i) ∈ 𝒮) :
    (∑ S ∈ 𝒮,
        (∑ i ∈ Plank.assignedSlabFamily s₁ R₁.repr slabOf S, volume (Ydom i).shade)) =
      ∑ i ∈ s₁, volume (Ydom i).shade :=
  Plank.sum_volume_assignedSlabFamily_eq s₁ Ydom R₁.repr slabOf 𝒮 hslab

open scoped Classical in
private lemma multiplicityComparison_hmaps
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    {ι : Type*} {cThk : ℝ≥0} (s₁ : Finset ι) (V : ι → Plank a b hab hb1)
    (R₁ : Plank.ThickenedRepr s₁ V θ hθ1 cThk)
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1) (𝒮 : Finset (Slab θ hθ1))
    (active : Slab θ hθ1 → Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (hactive : ∀ S, active S = R₁.indexSet.filter (fun Q => slabOf Q = S)) :
    ∀ S ∈ 𝒮, ∀ i ∈ Plank.assignedSlabFamily s₁ R₁.repr slabOf S, R₁.repr i ∈ active S := by
  intro S hS i hi
  obtain ⟨hmem, hslab⟩ := Plank.mem_assignedSlabFamily.mp hi
  rw [hactive, Finset.mem_filter]
  exact ⟨R₁.repr_mem_indexSet hmem, hslab⟩

open scoped Classical in
private lemma multiplicityComparison_hunion
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    {ι : Type*} {cThk Cbox : ℝ≥0} (s₁ : Finset ι) (V : ι → Plank a b hab hb1)
    (R₁ : Plank.ThickenedRepr s₁ V θ hθ1 cThk)
    (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (anchor : Plank.ThickenedPlank θ b hθ1 hb1 → Plank.EnsemblePrism)
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1) (𝒮 : Finset (Slab θ hθ1))
    (active : Slab θ hθ1 → Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (hactive : ∀ S, active S = R₁.indexSet.filter (fun Q => slabOf Q = S))
    (Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hYθ : Yθ = Plank.sharedSlabThickenedShadingDilation Cbox s₁ Ydom anchor R₁.repr slabOf) :
    ∀ S ∈ 𝒮, (⋃ t ∈ active S, (Yθ t).shade) ⊆
        ⋃ i ∈ Plank.assignedSlabFamily s₁ R₁.repr slabOf S, (Ydom i).shade := by
  subst hYθ
  intro S hS x hx
  rw [hactive, Set.mem_iUnion₂] at hx
  obtain ⟨Q, hQ, hxQ⟩ := hx
  rw [← (Finset.mem_filter.mp hQ).2]
  exact Plank.sharedSlabThickenedShadingDilation_shade_subset_assigned
    Cbox s₁ Ydom anchor R₁.repr slabOf Q hxQ

open scoped Classical in
private lemma multiplicityComparison_hfibre
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    {ι : Type*} {cThk cN : ℝ≥0} {N : ℕ}
    (s₁ : Finset ι) (V : ι → Plank a b hab hb1)
    (R₁ : Plank.ThickenedRepr s₁ V θ hθ1 cThk)
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1) (𝒮 : Finset (Slab θ hθ1))
    (active : Slab θ hθ1 → Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (hactive : ∀ S, active S = R₁.indexSet.filter (fun Q => slabOf Q = S))
    (hcN1 : 1 ≤ cN) (hcN2 : cN ≤ 2)
    (hfib : ∀ t ∈ R₁.indexSet,
      (N : ℝ) / (cN : ℝ) ≤ ((s₁.filter (fun i => R₁.repr i = t)).card : ℝ) ∧
        ((s₁.filter (fun i => R₁.repr i = t)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) :
    ∀ S ∈ 𝒮, ∀ t ∈ active S,
        (((Plank.assignedSlabFamily s₁ R₁.repr slabOf S).filter fun i => R₁.repr i = t).card :
            ENNReal) ≤
          ((2 * (N : ℝ≥0) : ℝ≥0) : ENNReal) := by
  intro S hS t ht
  rw [hactive, Finset.mem_filter] at ht
  rw [Plank.filter_repr_assignedSlabFamily_eq s₁ R₁.repr slabOf S ht.2]
  refine ENNReal.coe_le_coe.mpr (?_ : (_ : ℝ≥0) ≤ 2 * (N : ℝ≥0))
  exact_mod_cast (fibre_bounds_two hcN1 hcN2 hfib t ht.1).2

open scoped Classical in
/-- **Item 4 of GWZ Lemma 6.13 on the final dominant/good-slab family.**

The conclusion is the public Item 4 clause of `ShadedPlank.reduction_to_slab`: a slab of the
canonical family `R₁.indexSet.image slabOf` whose canonical fibre
`R₁.indexSet.filter (fun Q => slabOf Q = S)`, shaded by exactly the `Yθ` of Items 2 and 3, carries
the whole multiplicity of the original family up to `c4 · a ^ (-ε) · a ^ (-(4η))` and the public
ratio `(a N) / (b θ)`.

`hfull` is the Item 2 output at `β`, and `hc4` is the coefficient comparison that the exponent
ledger of the final assembly supplies; nothing here spends a power of `a`. -/
theorem slabwiseMultiplicity
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    {ι : Type*} {cThk Cbox rRef cOv β cN Cgeom c4 : ℝ≥0} {N : ℕ}
    {volP : ENNReal} {η ε : ℝ}
    (s s₁ : Finset ι) (V : ι → Plank a b hab hb1)
    (R₁ : Plank.ThickenedRepr s₁ V θ hθ1 cThk)
    (Y Yfinal : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ)
    (hrRef : rRef ≠ 0) (hcOv : 0 < cOv) (hβ : 0 < β)
    (hcN1 : 1 ≤ cN) (hcN2 : cN ≤ 2) (hgeom : (2 : ℝ≥0) ≤ Cgeom)
    (hne : (R₁.indexSet.image slabOf).Nonempty)
    (href : ShadedBody.IsCRefinement s₁ Yfinal s Y rRef)
    (hslab : ∀ i ∈ s₁, slabOf (R₁.repr i) ∈ R₁.indexSet.image slabOf)
    (hov : (cOv : ENNReal) *
          (∑ S ∈ R₁.indexSet.image slabOf,
            volume (⋃ i ∈ Plank.assignedSlabFamily s₁ R₁.repr slabOf S, (Yfinal i).shade))
        ≤ volume (⋃ i ∈ s₁, (Yfinal i).shade))
    (hPvol : ∀ S ∈ R₁.indexSet.image slabOf,
      ∀ i ∈ Plank.assignedSlabFamily s₁ R₁.repr slabOf S,
        volume (Yfinal i).shade ≤ volP)
    (hfib : ∀ t ∈ R₁.indexSet,
      (N : ℝ) / (cN : ℝ) ≤ ((s₁.filter (fun i => R₁.repr i = t)).card : ℝ) ∧
        ((s₁.filter (fun i => R₁.repr i = t)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ))
    (hcarrierVolume : ∀ S ∈ R₁.indexSet.image slabOf,
      ∀ t ∈ R₁.indexSet.filter (fun Q => slabOf Q = S),
        ((θ * b / a : ℝ≥0) : ENNReal) * volP
          ≤ volume (Plank.sharedSlabThickenedShadingDilation Cbox s₁ Yfinal
              (fun Q => Q.toPrismNDim) R₁.repr slabOf t).carrier)
    (hfull : ∀ S ∈ R₁.indexSet.image slabOf,
      β ≤ ShadedBody.fullness (R₁.indexSet.filter (fun Q => slabOf Q = S))
        (Plank.sharedSlabThickenedShadingDilation Cbox s₁ Yfinal
          (fun Q => Q.toPrismNDim) R₁.repr slabOf))
    (hc4 : (Cgeom : ENNReal) * (rRef : ENNReal)⁻¹ * (cOv : ENNReal)⁻¹ * (β : ENNReal)⁻¹
      ≤ (c4 : ENNReal) * (a : ENNReal) ^ (-ε) * (a : ENNReal) ^ (-(4 * η))) :
    ∃ S ∈ R₁.indexSet.image slabOf,
      ShadedBody.multiplicity s Y ≤
        (c4 : ENNReal) * (a : ENNReal) ^ (-ε) * (a : ENNReal) ^ (-(4 * η)) *
          (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal) *
          ShadedBody.multiplicity (R₁.indexSet.filter (fun Q => slabOf Q = S))
            (Plank.sharedSlabThickenedShadingDilation Cbox s₁ Yfinal
              (fun Q => Q.toPrismNDim) R₁.repr slabOf) := by
  classical
  set Yθ := Plank.sharedSlabThickenedShadingDilation Cbox
    s₁ Yfinal (fun Q => Q.toPrismNDim) R₁.repr slabOf with hYθ
  obtain ⟨S, hS, hle⟩ :=
    multiplicityReduction_of_refinement_and_fullness_ratio
      (s := s) (s' := s₁) (Y := Y) (Y' := Yfinal) (Yθ := Yθ)
      R₁.repr (R₁.indexSet.image slabOf)
      (Plank.assignedSlabFamily s₁ R₁.repr slabOf)
      (fun S => R₁.indexSet.filter (fun Q => slabOf Q = S))
      (cN := 2)
      ha hb hθ hrRef hcOv hβ hgeom hne href
        (multiplicityComparison_hpart s₁ V R₁ Yfinal slabOf (R₁.indexSet.image slabOf) hslab)
        hov
        (multiplicityComparison_hmaps s₁ V R₁ slabOf (R₁.indexSet.image slabOf)
          (fun S => R₁.indexSet.filter (fun Q => slabOf Q = S)) (fun _ => rfl))
        (multiplicityComparison_hunion (Cbox := Cbox) s₁ V R₁ Yfinal
          (fun Q => Q.toPrismNDim) slabOf (R₁.indexSet.image slabOf)
          (fun S => R₁.indexSet.filter (fun Q => slabOf Q = S)) (fun _ => rfl) Yθ hYθ) hPvol
        (multiplicityComparison_hfibre s₁ V R₁ slabOf (R₁.indexSet.image slabOf)
          (fun S => R₁.indexSet.filter (fun Q => slabOf Q = S)) (fun _ => rfl) hcN1 hcN2 hfib)
        hcarrierVolume hfull
  refine ⟨S, hS, hle.trans ?_⟩
  gcongr

end Kakeya

end

end
