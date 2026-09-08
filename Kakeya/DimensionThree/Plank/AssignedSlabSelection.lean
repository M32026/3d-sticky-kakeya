/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabSelection
public import Kakeya.DimensionThree.Plank.AssignedSlabFamily
public import Kakeya.DimensionThree.Plank.AngleDef

/-!
# From the geometric slab family to the assigned slab family, via dominant regions

Item 2 of GWZ Lemma 6.13 runs on two different index families and *must* keep them apart.

* The **geometric** family `Plank.inSlabFamilyC Cset Cang s' V S` — every plank comparable with the
  slab `S` — is what the local angular arguments need, because it is shade-fibre closed after the
  constant inflation of `Plank.shadeFibre_trimmed_inSlabFamilyC_eq`.  The assigned family is *not*
  fibre closed, and a pigeonhole over the slabs cannot make it so uniformly: the slab realising a
  fibre-retention bound moves with the point.
* The **assigned** family `Plank.assignedSlabFamily s' repr slabOf S` — the exact fibre of
  `slabOf ∘ repr` — is what the public statement must use, because it is a genuine partition of `s'`
  and it is induced by the canonical `slabOf`.

The two are not equal, and the useful inclusion runs the wrong way:
`assignedSlabFamily S ⊆ inSlabFamilyC Cset Cang s' V S`
(`Plank.assignedSlabFamily_subset_inSlabFamilyC`), so a *lower* bound on the geometric family's
shading mass says nothing about the assigned family's.

This file supplies the missing link, and it is not a comparison of index families at all — it is a
statement about *points*.  On the dominant region of `S` the assigned family carries a
`Nov⁻¹`-fraction of the whole pointwise multiplicity, and a shaded point of the assigned family
always lies in that region (`Plank.mem_dominantSlabRegion_of_mem_biUnion_assigned`), because the
dominant shading cuts each plank against the dominant region of *its own* assigned slab.  Combining
the two gives a fibre retention that *is* uniform in the point at a fixed slab, which is exactly
what the two-sided angular predicates need.

Because everything here is at the level of points and fibre cardinalities, it costs **no** power of
`a`; the entire price of the passage is the absolute `Nov` already inside the definition of the
dominant region, and `Plank.dominantGoodSlab_assigned_fibre_retention_source` spends it
exactly once.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι τ σ : Type*}

/-! ## The uniform-in-`x` fibre retention of a fixed slab

The retention is stated against the *uncut* source shading `Y'`, so the passage from the
preassembly family to a retained assigned slab costs exactly one factor of `Nov`. -/

/-- **A shaded point of the assigned family lies in that slab's dominant region.**  Immediate from
the definition of `Plank.dominantSlabShading`, which cuts each plank against the dominant region of
*its own* assigned slab: for `i` assigned to `S` that region is the one of `S`. -/
theorem mem_dominantSlabRegion_of_mem_biUnion_assigned (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (Nov : ℕ) (S : σ)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ⋃ i ∈ assignedSlabFamily s' repr slabOf S,
        (dominantSlabShading s' Y' repr slabOf Nov i).shade) :
    x ∈ dominantSlabRegion s' Y' repr slabOf Nov S := by
  obtain ⟨i₀, hi₀, hxi₀⟩ := Set.mem_iUnion₂.mp hx
  rw [dominantSlabShading_shade, (mem_assignedSlabFamily.mp hi₀).2] at hxi₀
  exact hxi₀.2

/-- **The assigned fibre of the dominant shading retains a `Nov⁻¹`-fraction of the fibre of the
original shading `Y'`.**

The dominant-region condition compares the *whole* `(s', Y')` fibre with the assigned `(𝒜 S, Y')`
fibre, and on the dominant region the latter coincides with the assigned fibre of the dominant
shading.  The bound is uniform in `x` and holds for a **fixed** slab `S`, which is what the
two-sided angular predicates need: after cutting every plank against the dominant region of its own
slab, a point of the assigned family's shading union is *by construction* a point where that slab
dominates.  No power of `a` is spent.

Stating it against `(s', Y')` matters because the passage `(s', Y') → (𝒜 S, Ydom)` then costs a
single factor `Nov`; routing through `(s₁, Ydom)` and transporting a second time would charge `Nov`
twice and demand a reserve stability scale of order `Nov ^ 2`. -/
theorem card_shadeFibre_le_mul_card_shadeFibre_assigned (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) {Nov : ℕ} (S : σ)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ⋃ i ∈ assignedSlabFamily s' repr slabOf S,
        (dominantSlabShading s' Y' repr slabOf Nov i).shade) :
    (Kakeya.shadeFibre s' Y' x).card
      ≤ Nov * (Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S)
            (dominantSlabShading s' Y' repr slabOf Nov) x).card := by
  have hxdom : x ∈ dominantSlabRegion s' Y' repr slabOf Nov S :=
    mem_dominantSlabRegion_of_mem_biUnion_assigned s' Y' repr slabOf Nov S hx
  rw [shadeFibre_assignedSlabFamily_dominantSlabShading s' Y' repr slabOf Nov S hxdom]
  simpa only [dominantSlabRegion, Set.mem_setOf_eq, ← Nat.cast_mul, Nat.cast_le] using hxdom

open scoped Classical in
/-- **The one-`Nov` fibre retention from the preassembly family to a retained assigned slab.**

The source is the preassembly's own `(s', Y')`, so this is exactly the retention hypothesis of
`Plank.isTypicalPlankAngle_of_fibreRetention` at `q = Nov⁻¹` with the preassembly's *reserve* scale
`Nov · A` as the source scale — one factor of `Nov`, no power of `a`, and no `a₀`. -/
theorem dominantGoodSlab_assigned_fibre_retention_source (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮g : Finset σ) {Nov : ℕ} (hNov : 1 ≤ Nov)
    {S : σ} (hS : S ∈ 𝒮g)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ⋃ i ∈ assignedSlabFamily (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)) repr slabOf S,
        (dominantSlabShading s' Y' repr slabOf Nov i).shade) :
    ((Nov : ℝ))⁻¹ * ((Kakeya.shadeFibre s' Y' x).card : ℝ)
      ≤ ((Kakeya.shadeFibre
            (assignedSlabFamily (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)) repr slabOf S)
            (dominantSlabShading s' Y' repr slabOf Nov) x).card : ℝ) := by
  rw [assignedSlabFamily_filter_slab_mem s' repr slabOf 𝒮g hS] at hx ⊢
  rw [inv_mul_le_iff₀ (by exact_mod_cast hNov : (0 : ℝ) < (Nov : ℝ))]
  exact_mod_cast card_shadeFibre_le_mul_card_shadeFibre_assigned s' Y' repr slabOf S hx

/-! ## The stop-scale stability clause on the assigned dominant family -/

open scoped Classical in
/-- **The stop-scale stability clause transports from the preassembly source to a retained assigned
dominant family, at the cost of exactly one factor of `Nov`.**

The source clause lives on `(s', Y')` at the reserve scale `Nov · Aout`; the target lives on the
assigned dominant family of a retained slab at the bare scale `Aout`.  The transport is
`Plank.dominantGoodSlab_assigned_fibre_retention_source`, which is the *direct* `s' → 𝒜 S`
retention: routing through the global `(s₁, Ydom)` instead would spend `Nov` twice and demand a
reserve of order `Nov ^ 2 · Aout`, which the preassembly does not supply and which no `a`-free
constant can repair.

The angular constant `K · Kakeya.plankAngleScaleB a` is carried through untouched; the conclusion is
stated in the quotient form that `Plank.localAngleConcentration_of_saturated_scaled` consumes. -/
theorem dominantGoodSlab_assigned_stopScale {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (V : ι → Plank a b hab hb1)
    (repr : ι → τ) (slabOf : τ → σ) (𝒮g : Finset σ) {Nov : ℕ} (hNov : 1 ≤ Nov)
    {S : σ} (hS : S ∈ 𝒮g) {K Aout : ℝ} (hK : 0 < K) (hAout : 0 < Aout)
    (hstop : ∀ x ∈ ⋃ i ∈ s', (Y' i).shade, ∀ t ⊆ Kakeya.shadeFibre s' Y' x,
      ((Nov : ℝ) * Aout)⁻¹ * ((Kakeya.shadeFibre s' Y' x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) ≤ K * Kakeya.plankAngleScaleB a * ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) :
    ∀ x ∈ ⋃ i ∈ assignedSlabFamily (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)) repr slabOf S,
        (dominantSlabShading s' Y' repr slabOf Nov i).shade,
      ∀ t ⊆ Kakeya.shadeFibre
          (assignedSlabFamily (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)) repr slabOf S)
          (dominantSlabShading s' Y' repr slabOf Nov) x,
        Aout⁻¹ * ((Kakeya.shadeFibre
            (assignedSlabFamily (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)) repr slabOf S)
            (dominantSlabShading s' Y' repr slabOf Nov) x).card : ℝ) ≤ (t.card : ℝ) →
          (θ : ℝ) / (K * Kakeya.plankAngleScaleB a)
            ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) := by
  intro x hx t ht hcard
  have hxs : x ∈ ⋃ i ∈ s', (Y' i).shade := by
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_of_mem_filter i
      (assignedSlabFamily_subset _ repr slabOf S hi),
      dominantSlabShading_shade_subset s' Y' repr slabOf Nov i hxi⟩
  have hsub : Kakeya.shadeFibre
      (assignedSlabFamily (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)) repr slabOf S)
      (dominantSlabShading s' Y' repr slabOf Nov) x ⊆ Kakeya.shadeFibre s' Y' x := fun j hj => by
    rw [Kakeya.mem_shadeFibre] at hj ⊢
    exact ⟨Finset.mem_of_mem_filter j (assignedSlabFamily_subset _ repr slabOf S hj.1),
      dominantSlabShading_shade_subset s' Y' repr slabOf Nov j hj.2⟩
  have hthr : ((Nov : ℝ) * Aout)⁻¹ * ((Kakeya.shadeFibre s' Y' x).card : ℝ) ≤ (t.card : ℝ) := by
    rw [mul_comm (Nov : ℝ) Aout, mul_inv, mul_assoc]
    exact (mul_le_mul_of_nonneg_left
      (dominantGoodSlab_assigned_fibre_retention_source s' Y' repr slabOf 𝒮g hNov hS hx)
      (inv_nonneg.2 hAout.le)).trans hcard
  have hpos : (0 : ℝ) < K * Kakeya.plankAngleScaleB a := mul_pos hK (Real.exp_pos _)
  rw [div_le_iff₀ hpos]
  exact (hstop x hxs t (ht.trans hsub) hthr).trans_eq (mul_comm _ _)

end Plank

end

end
