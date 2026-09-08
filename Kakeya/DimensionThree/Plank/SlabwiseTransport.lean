/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabSelection
public import Kakeya.DimensionThree.Plank.AssignedSlabSelection
public import Kakeya.DimensionThree.Plank.TypicalAngleTransfer
public import Kakeya.DimensionThree.Plank.RelativeMultiplicity

/-!
# Transporting the preassembly hypotheses to the final family

After the slab-complete dominant/good-slab refinement the final family is

`s₁ = s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)`,
`Ydom = dominantSlabShading s' Y' repr slabOf Nov`.

Item 1 is *not* monotone under shrinking the index set — its ball-density clause has the family on
both sides — so it has to be re-run there, and its hypotheses have to be re-established.  This file
supplies exactly those transports, and nothing else; the geometry of Item 1 is untouched.

Every loss here is absolute:

* the fibre-retention rate is the `Nov⁻¹` of
  `Plank.dominantGoodSlab_assigned_fibre_retention_source`, which is what feeds
  `Plank.isTypicalPlankAngle_of_fibreRetention` (through the reserve stability scale `Nov · A`) and
  `Plank.hasCConstantMultiplicity_of_fibreRetention_real`;
* the aggregate rate is the `(2 · Nov)⁻¹` of `Plank.isCRefinement_dominantGoodSlabShading`, which is
  what converts a fullness lower bound.

No power of `a` is spent by any of them, and no representative is deleted: the prune is
slab-complete, so a surviving representative keeps its entire fibre and the preassembly's fibre
bounds are reusable verbatim.

The `cN`-widening lemma is included here too: the preassembly's internal constant satisfies
`1 ≤ cN ≤ 2`, and the public statement asks for the literal `2`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι τ σ : Type*}

/-! ## Widening the internal fibre constant to the public `2` -/

/-- **The public fibre bounds at `cN = 2`.**  The preassembly returns a two-sided fibre bound at an
internal constant `cN` with `1 ≤ cN ≤ 2`; the public statement of Lemma 6.13 asks for the literal
`2`.  Both directions are plain monotonicity, and no property of the fibre is used, so this is
stated for bare reals.

Stating it separately keeps the preassembly theorem unchanged: nothing is adjusted merely to make
the two bounds definitionally equal. -/
theorem fibre_bounds_two_of_le_two {cN N card : ℝ}
    (hcN1 : 1 ≤ cN) (hcN2 : cN ≤ 2) (hN : 0 ≤ N)
    (hlo : N / cN ≤ card) (hup : card ≤ cN * N) :
    N / 2 ≤ card ∧ card ≤ 2 * N :=
  ⟨(div_le_div_of_nonneg_left hN (zero_lt_one.trans_le hcN1) hcN2).trans hlo,
    hup.trans (mul_le_mul_of_nonneg_right hcN2 hN)⟩

/-!
## Fullness on the final family

No lemma is needed: `Plank.fullness_ge_of_isCRefinement`
(`Kakeya/DimensionThree/Plank/StableRefinement.lean:62`) already gives
`c * fullness s V ≤ fullness s' V'` from `ShadedBody.IsCRefinement s' V' s V c`, with no positivity
or finiteness side conditions, and `Plank.isCRefinement_dominantGoodSlabShading` supplies exactly
that refinement at the absolute `c = (2 · Nov)⁻¹`.
-/

/-! ## The two transports, landing on one retained assigned family -/

open scoped Classical in
/-- **The two-sided typical angle transports from the preassembly source directly to a retained
assigned dominant family, spending exactly one factor of `Nov`.**

Transporting first to the whole pruned family `s₁` and then again to `𝒜 S` would spend `Nov` twice
and demand a reserve of order `Nov ^ 2 · A`, which the preassembly does not supply.  Going directly
through
`Plank.dominantGoodSlab_assigned_fibre_retention_source` spends it once, and the reserve `Nov · A`
that `Kakeya.refinement_preassembly_uniform` publishes is then exactly enough — the budget
`A ≤ Nov⁻¹ · (Nov · A)` holds with equality. -/
theorem isTypicalPlankAngle_assigned_of_source {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1)
    (repr : ι → τ) (slabOf : τ → σ) (𝒮g : Finset σ)
    {Nov : ℕ} (hNov : 1 ≤ Nov) {S : σ} (hS : S ∈ 𝒮g) (θ C A : ℝ≥0) (hA : 1 ≤ A)
    (hstab : ∀ x ∈ ⋃ i ∈ s', (Y' i).shade, ∀ t ⊆ Kakeya.shadeFibre s' Y' x,
      (((Nov : ℝ≥0) * A : ℝ≥0) : ℝ)⁻¹ * ((Kakeya.shadeFibre s' Y' x).card : ℝ) ≤ (t.card : ℝ) →
        θ ≤ C * Kakeya.maxPlankAngle P t ∧ Kakeya.maxPlankAngle P t ≤ C * θ) :
    Kakeya.IsTypicalPlankAngle
      (assignedSlabFamily (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)) repr slabOf S)
      (dominantSlabShading s' Y' repr slabOf Nov) P θ C A := by
  have hNovpos : (0 : ℝ) < (Nov : ℝ) := Nat.cast_pos.mpr hNov
  exact isTypicalPlankAngle_of_fibreRetention s' _
    (fun i hi => Finset.mem_of_mem_filter i (assignedSlabFamily_subset _ repr slabOf S hi))
    Y' _ P θ C A ((Nov : ℝ≥0) * A) ((Nov : ℝ))⁻¹ hA
    (le_of_eq (by rw [NNReal.coe_mul, NNReal.coe_natCast, inv_mul_cancel_left₀ hNovpos.ne']))
    (fun i _ => dominantSlabShading_shade_subset s' Y' repr slabOf Nov i)
    (fun x hx => dominantGoodSlab_assigned_fibre_retention_source s' Y' repr slabOf 𝒮g hNov hS hx)
    hstab

open scoped Classical in
/-- **Constant multiplicity transports from the preassembly source directly to a retained assigned
dominant family, spending exactly one factor of `Nov`.**

The constant-multiplicity analogue of `Plank.isTypicalPlankAngle_assigned_of_source`.  A larger
constant is a weaker statement, so the single `Nov` is harmless and costs no power of `a`. -/
theorem hasCConstantMultiplicity_assigned_of_source (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮g : Finset σ)
    {Nov : ℕ} (hNov : 1 ≤ Nov) {S : σ} (hS : S ∈ 𝒮g) (C : ℝ≥0)
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' C) :
    ShadedBody.HasCConstantMultiplicity
      (assignedSlabFamily (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)) repr slabOf S)
      (dominantSlabShading s' Y' repr slabOf Nov) ((Nov : ℝ≥0) * C) := by
  have hNovne : (Nov : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine hasCConstantMultiplicity_of_fibreRetention_real (inv_pos.mpr (pos_iff_ne_zero.mpr hNovne))
    hC (fun x j hj => ?_) (fun x hx => ?_) (le_of_eq (inv_mul_cancel_left₀ hNovne C).symm)
  · rw [Kakeya.mem_shadeFibre] at hj ⊢
    exact ⟨Finset.mem_of_mem_filter j (assignedSlabFamily_subset _ repr slabOf S hj.1),
      dominantSlabShading_shade_subset s' Y' repr slabOf Nov j hj.2⟩
  · rw [NNReal.coe_inv]
    exact dominantGoodSlab_assigned_fibre_retention_source s' Y' repr slabOf 𝒮g hNov hS hx

end Plank

end

end
