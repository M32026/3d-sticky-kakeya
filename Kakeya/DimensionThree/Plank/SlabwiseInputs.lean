/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AssignedSlabFamily

/-!
# The two aggregate inputs of Items 3 and 4 of GWZ Lemma 6.13

Items 3 and 4 of `Kakeya.plankReduction` are both stated against the *dilated* shared shading
`Plank.sharedSlabThickenedShadingDilation`, while the aggregate slab-mass bound that
`Kakeya.plankReduction_preassembly` returns is a statement about the plank shadings `Y'`.  This file
supplies the two bridges.

* `Plank.sum_volume_sharedSlabDilation_le` — Item 3.  The slab-summed mass of the dilated shading is
  bounded by the mass of the whole union, at the same `cOv` the preassembly provides.  An undilated
  analogue would proceed through the per-slab union *identity*, which needs
  `Y'_i ⊆ (repr i).carrier`; at the dilated carrier only the *inclusion*
  `Plank.sharedSlabThickenedShadingDilation_shade_subset_assigned` is available, and it is all that
  is needed, since Item 3 only ever wants the `≤` direction.
* `Plank.sum_volume_assignedSlabFamily_eq` — the `hpart` hypothesis of
  `Kakeya.multiplicityReduction_of_refinement_and_fullness_ratio`.  This is
  `Plank.sum_card_assignedSlabFamily` with `Finset.card` replaced by a sum of measures; the content
  is the same partition of `s'`.

Both are stated for an arbitrary superfamily `Pass S ⊇ assignedSlabFamily …` so that the caller may
pass the geometric family `Plank.inSlabFamilyC` that the preassembly's aggregate clause is phrased
with, without a second version of either lemma.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι τ σ : Type*}

open scoped Classical in
/-- **Item 3 at the dilated shared shading.**  The slab-local unions of the dilated shading sit
inside the assigned-family plank unions, so the aggregate slab-mass bound `hov` transfers to them
verbatim.

`U` is left free, and the intended instance is the *original* shading union
`⋃ i ∈ s, (Y i).shade`, reached from `⋃ i ∈ s', (Y' i).shade` by the refinement inclusion; that is
exactly the right-hand side of Item 3. -/
theorem sum_volume_sharedSlabDilation_le (Cbox : ℝ≥0)
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (anchor : τ → EnsemblePrism) (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (Pass : σ → Finset ι)
    (hPass : ∀ S ∈ 𝒮, assignedSlabFamily s' repr slabOf S ⊆ Pass S)
    (cOv : ℝ≥0)
    (hov : (cOv : ENNReal) * ∑ S ∈ 𝒮, volume (⋃ i ∈ Pass S, (Y' i).shade)
      ≤ volume (⋃ i ∈ s', (Y' i).shade))
    (𝒯 : Finset τ)
    (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : (⋃ i ∈ s', (Y' i).shade) ⊆ U) :
    (cOv : ENNReal) * ∑ S ∈ 𝒮,
        volume (⋃ Q ∈ 𝒯.filter (fun Q => slabOf Q = S),
          (sharedSlabThickenedShadingDilation Cbox s' Y' anchor repr slabOf Q).shade)
      ≤ volume U := by
  calc
    (cOv : ENNReal) * ∑ S ∈ 𝒮,
        volume (⋃ Q ∈ 𝒯.filter (fun Q => slabOf Q = S),
          (sharedSlabThickenedShadingDilation Cbox s' Y' anchor repr slabOf Q).shade)
        ≤ (cOv : ENNReal) * ∑ S ∈ 𝒮, volume (⋃ i ∈ assignedSlabFamily s' repr slabOf S,
            (Y' i).shade) := by
      have hsum : ∑ S ∈ 𝒮, volume (⋃ Q ∈ 𝒯.filter (fun Q => slabOf Q = S),
          (sharedSlabThickenedShadingDilation Cbox s' Y' anchor repr slabOf Q).shade) ≤
          ∑ S ∈ 𝒮, volume (⋃ i ∈ assignedSlabFamily s' repr slabOf S, (Y' i).shade) :=
        Finset.sum_le_sum (fun S hS => by
          apply measure_mono
          intro x hx
          rw [Set.mem_iUnion₂] at hx
          rcases hx with ⟨Q, hQ, hxQ⟩
          have hSlab : slabOf Q = S := (Finset.mem_filter.mp hQ).2
          have hInc : x ∈ ⋃ i ∈ assignedSlabFamily s' repr slabOf (slabOf Q), (Y' i).shade :=
            sharedSlabThickenedShadingDilation_shade_subset_assigned Cbox s' Y' anchor repr
              slabOf Q hxQ
          rw [hSlab] at hInc
          exact hInc)
      exact mul_le_mul_right hsum (cOv : ENNReal)
    _ ≤ (cOv : ENNReal) * ∑ S ∈ 𝒮, volume (⋃ i ∈ Pass S, (Y' i).shade) := by
      have hsum : ∑ S ∈ 𝒮, volume (⋃ i ∈ assignedSlabFamily s' repr slabOf S, (Y' i).shade) ≤
          ∑ S ∈ 𝒮, volume (⋃ i ∈ Pass S, (Y' i).shade) :=
        Finset.sum_le_sum (fun S hS => by
          have hsub_pass : assignedSlabFamily s' repr slabOf S ⊆ Pass S := hPass S hS
          have hunion_sub : (⋃ i ∈ assignedSlabFamily s' repr slabOf S, (Y' i).shade) ⊆
              (⋃ i ∈ Pass S, (Y' i).shade) := by
            intro x hx
            obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
            have hi_pass : i ∈ Pass S := hsub_pass hi
            exact Set.mem_iUnion₂.mpr ⟨i, hi_pass, hxi⟩
          exact measure_mono hunion_sub)
      exact mul_le_mul_right hsum (cOv : ENNReal)
    _ ≤ volume (⋃ i ∈ s', (Y' i).shade) := hov
    _ ≤ volume U := measure_mono hU

open scoped Classical in
/-- **The assigned families partition the shading mass.**  `Plank.sum_card_assignedSlabFamily` with
`Finset.card` replaced by a sum of measures.  This is the `hpart` hypothesis of
`Kakeya.multiplicityReduction_of_refinement_and_fullness_ratio`. -/
theorem sum_volume_assignedSlabFamily_eq
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) :
    ∑ S ∈ 𝒮, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).shade)
      = ∑ i ∈ s', volume (Y' i).shade := by
  calc
    ∑ S ∈ 𝒮, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).shade)
        = ∑ i ∈ 𝒮.biUnion (fun S => assignedSlabFamily s' repr slabOf S), volume (Y' i).shade := by
          rw [Finset.sum_biUnion]
          intro S hS T hT hST
          exact assignedSlabFamily_disjoint s' repr slabOf hST
    _ = ∑ i ∈ s', volume (Y' i).shade := by
          rw [biUnion_assignedSlabFamily s' repr slabOf 𝒮 h𝒮]

open scoped Classical in
/-- **The good-slab prune retains half the shading mass.**  Discard every slab whose assigned family
fails the aggregate threshold `τ`, and keep the planks assigned to the rest.  If the family's own
aggregate mass beats `2 τ` times its carrier mass — i.e. `2 τ ≤ ShadedBody.fullness s' Y'` in
ratio form — then the retained planks still carry at least half of the shading mass.

This is the ledger step that makes Item 2 of GWZ Lemma 6.13 available at *every* retained slab.  Two
points make it affordable, and both are essential.

First, the discarded mass is charged against the *carrier* sum, not against the count: a bad
slab may hold arbitrarily many planks, so no bound on the discarded cardinality is available,
and none is needed.

Second, the surviving public cardinality clause `((cP · a^η) · a^ε) · |s| ≤ |s'|` must be obtained
from the *fullness* clause at the very end, through
`Kakeya.card_le_of_isCRefinement_of_fullness`, and not by composing two mass-to-count conversions. Composing them would cost `a^η` twice and break the clause; converting once at the end costs it
once, which is exactly what the public statement allows. -/
theorem exists_goodSlabPrune (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) (τ : ℝ≥0)
    (htop : ∑ i ∈ s', volume (Y' i).shade ≠ ⊤)
    (hτ : 2 * ((τ : ENNReal) * ∑ i ∈ s', volume (Y' i).carrier)
      ≤ ∑ i ∈ s', volume (Y' i).shade) :
    ∃ 𝒮g ⊆ 𝒮,
      (∀ S ∈ 𝒮g,
        (τ : ENNReal) * ∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).carrier
          ≤ ∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).shade) ∧
      ∑ i ∈ s', volume (Y' i).shade
        ≤ 2 * ∑ i ∈ s'.filter (fun i => slabOf (repr i) ∈ 𝒮g), volume (Y' i).shade := by
  classical
  let p : σ → Prop := fun S =>
    (τ : ENNReal) * ∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).carrier
      ≤ ∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).shade
  let 𝒮g : Finset σ := 𝒮.filter p
  let Good : Finset ι := s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)
  let Mtot : ENNReal := ∑ i ∈ s', volume (Y' i).shade
  let Ctot : ENNReal := ∑ i ∈ s', volume (Y' i).carrier
  let Gtot : ENNReal := ∑ i ∈ Good, volume (Y' i).shade
  have hsubset : 𝒮g ⊆ 𝒮 := by
    simp [𝒮g]
  have hcond : ∀ S ∈ 𝒮g, p S := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  -- Step 1: the assigned families partition the shading mass over `𝒮`.
  have hMtot_eq : ∑ S ∈ 𝒮, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).shade) =
      Mtot := by
    simpa [Mtot] using sum_volume_assignedSlabFamily_eq s' Y' repr slabOf 𝒮 h𝒮
  -- The carrier analogue of Step 1.
  have hCtot_eq : ∑ S ∈ 𝒮, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).carrier) =
      Ctot := by
    simpa [Ctot] using by
      calc
        ∑ S ∈ 𝒮, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).carrier)
            = ∑ i ∈ 𝒮.biUnion (fun S => assignedSlabFamily s' repr slabOf S), volume (Y'
                i).carrier := by
              rw [Finset.sum_biUnion]
              intro S hS T hT hST
              exact assignedSlabFamily_disjoint s' repr slabOf hST
        _ = ∑ i ∈ s', volume (Y' i).carrier := by
              rw [biUnion_assignedSlabFamily s' repr slabOf 𝒮 h𝒮]
  -- Step 2: the good block is exactly the retained mass.
  have hbiUnion_good : 𝒮g.biUnion (fun S => assignedSlabFamily s' repr slabOf S) = Good := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      rw [Finset.mem_biUnion] at hi
      rcases hi with ⟨S, hS, hiS⟩
      have hi_mem : i ∈ s' := (mem_assignedSlabFamily.mp hiS).1
      have hi_eq : slabOf (repr i) = S := (mem_assignedSlabFamily.mp hiS).2
      rw [Finset.mem_filter]
      refine ⟨hi_mem, ?_⟩
      rw [hi_eq]
      exact hS
    · intro hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨hi_s', hi_good⟩
      rw [Finset.mem_biUnion]
      refine ⟨slabOf (repr i), hi_good, ?_⟩
      exact mem_assignedSlabFamily.mpr ⟨hi_s', rfl⟩
  have hgood_eq : ∑ S ∈ 𝒮g, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).shade) =
      Gtot := by
    calc
      ∑ S ∈ 𝒮g, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).shade)
          = ∑ i ∈ 𝒮g.biUnion (fun S => assignedSlabFamily s' repr slabOf S), volume (Y'
              i).shade := by
            rw [Finset.sum_biUnion]
            intro S hS T hT hST
            exact assignedSlabFamily_disjoint s' repr slabOf hST
      _ = ∑ i ∈ Good, volume (Y' i).shade := by rw [hbiUnion_good]
      _ = Gtot := by rfl
  -- Step 3: the bad block is bounded by `τ · Ctot`.
  have hbad_le : ∑ S ∈ 𝒮.filter (fun S => ¬ p S), (∑ i ∈ assignedSlabFamily s' repr slabOf S,
      volume (Y' i).shade)
      ≤ (τ : ENNReal) * Ctot := by
    calc
      ∑ S ∈ 𝒮.filter (fun S => ¬ p S), (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y'
          i).shade)
          ≤ ∑ S ∈ 𝒮.filter (fun S => ¬ p S), (τ : ENNReal) * (∑ i ∈ assignedSlabFamily s' repr
              slabOf S, volume (Y' i).carrier) := by
            exact Finset.sum_le_sum (fun S hS => by
              have hnot : ¬ p S := (Finset.mem_filter.mp hS).2
              exact le_of_lt (not_le.mp hnot))
      _ = (τ : ENNReal) * ∑ S ∈ 𝒮.filter (fun S => ¬ p S), (∑ i ∈ assignedSlabFamily s' repr
          slabOf S, volume (Y' i).carrier) := by
            rw [Finset.mul_sum]
      _ ≤ (τ : ENNReal) * ∑ S ∈ 𝒮, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y'
          i).carrier) := by
            exact mul_le_mul_right (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (τ :
                ENNReal)
      _ = (τ : ENNReal) * Ctot := by rw [hCtot_eq]
  -- Step 4: combine the good and bad blocks, then absorb half of `Mtot` against `τ · Ctot`.
  have hMtot_le : Mtot ≤ Gtot + (τ : ENNReal) * Ctot := by
    calc
      Mtot = ∑ S ∈ 𝒮, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).shade) :=
          hMtot_eq.symm
      _ = (∑ S ∈ 𝒮g, (∑ i ∈ assignedSlabFamily s' repr slabOf S, volume (Y' i).shade))
            + (∑ S ∈ 𝒮.filter (fun S => ¬ p S), (∑ i ∈ assignedSlabFamily s' repr slabOf S,
                volume (Y' i).shade)) := by
            rw [← Finset.sum_filter_add_sum_filter_not 𝒮 p (fun S => ∑ i ∈ assignedSlabFamily
                s' repr slabOf S, volume (Y' i).shade)]
      _ = Gtot + (∑ S ∈ 𝒮.filter (fun S => ¬ p S), (∑ i ∈ assignedSlabFamily s' repr slabOf S,
          volume (Y' i).shade)) := by
            rw [hgood_eq]
      _ ≤ Gtot + (τ : ENNReal) * Ctot := by
            exact add_le_add le_rfl hbad_le
  have hτle : 2 * ((τ : ENNReal) * Ctot) ≤ Mtot := by
    simpa [Mtot, Ctot] using hτ
  have h2M : 2 * Mtot ≤ 2 * Gtot + 2 * ((τ : ENNReal) * Ctot) := by
    calc
      2 * Mtot ≤ 2 * (Gtot + (τ : ENNReal) * Ctot) := mul_le_mul_right hMtot_le (2 : ENNReal)
      _ = 2 * Gtot + 2 * ((τ : ENNReal) * Ctot) := by rw [mul_add]
  have h2M' : 2 * Mtot ≤ 2 * Gtot + Mtot := by
    calc
      2 * Mtot ≤ 2 * Gtot + 2 * ((τ : ENNReal) * Ctot) := h2M
      _ ≤ 2 * Gtot + Mtot := by
        rw [add_comm (2 * Gtot) (2 * ((τ : ENNReal) * Ctot))]
        rw [add_comm (2 * Gtot) Mtot]
        exact add_le_add hτle (le_refl (2 * Gtot))
  have hMtot_plus : Mtot + Mtot ≤ 2 * Gtot + Mtot := by
    simpa [two_mul] using h2M'
  have htop' : Mtot ≠ ⊤ := by
    simpa [Mtot] using htop
  have hfinal : Mtot ≤ 2 * Gtot := by
    exact (ENNReal.add_le_add_iff_right htop').mp hMtot_plus
  refine ⟨𝒮g, hsubset, hcond, ?_⟩
  simpa [Mtot, Gtot, Good] using hfinal

end Plank

end
