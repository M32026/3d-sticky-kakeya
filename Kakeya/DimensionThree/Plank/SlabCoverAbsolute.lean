/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabIndexOverlap
public import Kakeya.DimensionThree.Plank.SlabwiseDensity
public import Kakeya.DimensionThree.Plank.ThickenedRepr
public import Kakeya.DimensionThree.Plank.FibreClassPigeonhole

/-!
# The slab cover, at an absolute angle constant

`Plank.slabwiseDensity_of_preassembly` needs a finite slab family `𝒮` together with three clauses:
a covering clause, an *index* overlap bound at the enlarged constants `(Cset', Cang')`, and a
*pointwise* overlap bound at the unenlarged `(Cset, Cang)` — all three at **one** `Nov`.

Every ingredient is already in the tree:

* `Plank.exists_thickenedRepr` produces a `Plank.ThickenedRepr` from `0 < a` and `a / b ≤ θ` alone,
  with **no** angular, fullness or multiplicity hypothesis, and in particular no reserve scale;
* `Plank.slabMassDecomposition` turns that into a `Plank.SlabAssignment` with pairwise essentially
  distinct used slabs, from `Kakeya.HasMaxPlankAngleBound s Y V θ C` and `a ≤ θ`;
* `Plank.slab_pointwise_overlap_le` and `Plank.slab_index_overlap_le` supply the two overlap
  bounds.

What was missing was not a lemma but a **constant**: `Plank.slabMassDecomposition` and
`Plank.slab_pointwise_overlap_le` both bind the one-sided angle constant `C` *before* the plank
scale `a`, and `ShadedPlank.reduction_to_slab_atTypicalAngle` supplies it only at `C ≤ δ ^ (-ε)`.
`Plank.exists_restriction_maxPlankAngle_pinned` removes that obstruction by pinning the angle to a
dyadic value at the **absolute** constant `2`, and this file is the assembly that becomes available
once it has been applied.

## `Plank.exists_slabCover_of_absoluteAngle`

All of `Cset`, `Cang`, `Cset'`, `Cang'` and `Nov` are produced **before** the configuration, and the
two enlargement inequalities that `Plank.localAngleConcentration_of_preassemblyData` asks for,

```
Cset + 4 * (2 * Cang + 4 * 2) + 8 ≤ Cset'        and        2 * Cang + 4 * 2 ≤ Cang',
```

are returned with the max-angle constant already instantiated at `2`.

## Why this collapses the route's `C`-power

`Plank.routePower_of_bounds` writes the Step-3 output constant as
`c1⁻¹ ≍ cBall⁻¹ * (Cmult * Nov * cTan / lamLower) ^ 2`, i.e. `C ^ (9 + 2 m)` with
`Nov ≤ K₅ * C ^ m`.  The trace that settled at `m = 48` — hence `k = 105` — did so because the
*index* overlap is read at `(Cset', Cang')` and those are `Θ(C)` when the max-angle constant is
`Θ(C)`: the constants `K` of `exists_refPose_constants` then contain a cross term `2 ρ Cs` that is
quadratic in `C`, and `Nov` is of order `K ^ 24`.

With the max-angle constant pinned at the absolute `2`, the two displayed inequalities make
`Cset'` and `Cang'` **absolute**, hence `K` absolute, hence **`Nov` absolute and `m = 0`**.
The same pinning
makes `cTan ≤ max 1728 (8192 * Cang' ^ 2)` absolute and, through `Ceta ∝ C * log C` at the
*max-angle* constant, `cBall⁻¹` absolute; and
`Plank.exists_restriction_hasCConstantMultiplicity_two` makes `Cmult` absolute.  The only surviving
power of `C` is `lamLower⁻¹`, forced by the leaf's own
`ShadedBody.IsCRefinement s Y'' s (bodies Y) C⁻¹` and squared by the `^ 2`, so `k = 2` for the
Step-3 outputs — which is `Plank.routePower_floor`'s irreducible part and nothing more.

That is a statement about the *route*, not a theorem proved here; what is proved here is the slab
cover with all five constants absolute, which is what makes it true.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

open scoped Classical in
/-- **The slab cover with every constant absolute, at the pinned angle constant `2`.**

Given a family whose one-sided maximal plank angle is bounded by `2 * θ` — the output of
`Plank.exists_restriction_maxPlankAngle_pinned` — this produces the slab family `𝒮` and the three
clauses `Plank.slabwiseDensity_of_preassembly` asks for, at constants fixed before the
configuration.

The hypothesis `a / b ≤ θ` is the leaf's own, and it also gives `a ≤ θ` because `b ≤ 1`; the
`Plank.exists_restriction_maxPlankAngle_pinned` angle satisfies it automatically, its value being
`(a / b) * 2 ^ j ≥ a / b`.

No fullness, no multiplicity, no cardinality and no reserve-scale hypothesis is used. -/
theorem exists_slabCover_of_absoluteAngle :
    ∃ (Cset Cang Cset' Cang' : ℝ≥0) (Nov : ℕ),
      1 ≤ Cset ∧ 1 ≤ Cang ∧ 1 ≤ Nov ∧
      Cset ≤ Cset' ∧ Cang ≤ Cang' ∧
      Cset + 4 * (2 * Cang + 4 * 2) + 8 ≤ Cset' ∧
      2 * Cang + 4 * 2 ≤ Cang' ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {θ : ℝ≥0} (hθ1 : θ ≤ 1),
        0 < a → a / b ≤ θ →
        Kakeya.HasMaxPlankAngleBound s Y V θ 2 →
        (∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∃ 𝒮 : Finset (Slab θ hθ1),
          (∀ i ∈ s, ∃ S ∈ 𝒮, i ∈ inSlabFamilyC Cset Cang s V S) ∧
          (∀ i ∈ s, (𝒮.filter fun S => i ∈ inSlabFamilyC Cset' Cang' s V S).card ≤ Nov) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3),
            (𝒮.filter fun S => x ∈ smallSlabUnion Cset Cang s V Y S).card ≤ Nov) := by
  classical
  obtain ⟨cThk, hcThk, hER⟩ := exists_thickenedRepr
  obtain ⟨cOv, Cset, Cang, hcOv, hCset, hCang, hSMD⟩ := slabMassDecomposition cThk 2 hcThk
  set Cang' : ℝ≥0 := 2 * Cang + 4 * 2 with hCang'_def
  set Cset' : ℝ≥0 := Cset + 4 * (2 * Cang + 4 * 2) + 8 with hCset'_def
  obtain ⟨Nov₁, hNov₁, hpoint⟩ := slab_pointwise_overlap_le 2 Cset Cang hCang
  have hCang_two : Cang ≤ 2 * Cang := by rw [two_mul]; exact le_add_self
  obtain ⟨Nov₂, hNov₂, hindex⟩ := slab_index_overlap_le Cset' Cang' (by
    rw [hCang'_def]
    exact (hCang.trans hCang_two).trans le_self_add)
  refine ⟨Cset, Cang, Cset', Cang', max Nov₁ Nov₂, hCset, hCang,
    le_trans hNov₁ (le_max_left _ _), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCset'_def]; exact le_self_add.trans le_self_add
  · rw [hCang'_def]
    exact hCang_two.trans le_self_add
  · rw [hCset'_def]
  · rw [hCang'_def]
  intro a b hab hb1 ι s V Y θ hθ1 ha hθa hmax hYV
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hθ0 : (0 : ℝ≥0) < θ := lt_of_lt_of_le (div_pos ha hb) hθa
  have haθ : a ≤ θ := by
    refine le_trans ?_ hθa
    rw [le_div_iff₀ hb]
    calc a * b ≤ a * 1 := by gcongr
      _ = a := mul_one a
  obtain ⟨R⟩ := hER s V θ hθ1 ha hθa
  obtain ⟨SA, hpairwise, _hagg⟩ := hSMD s V Y θ hθ1 R ha haθ hmax hYV
  refine ⟨SA.used, ?_, ?_, ?_⟩
  · exact fun i hi => ⟨SA.slabOf (R.repr i), SA.slabOf_mem i hi, SA.mem_inSlabFamily i hi⟩
  · intro i hi
    exact le_trans (hindex s V hθ1 SA.used hθ0 hθa hpairwise i hi) (le_max_right _ _)
  · intro x
    exact le_trans (hpoint s V Y hθ1 R.repr SA hθ0 hmax hYV hpairwise x) (le_max_left _ _)

end Plank

end
