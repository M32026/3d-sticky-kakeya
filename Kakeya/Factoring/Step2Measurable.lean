/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Step2

/-! # Measurability of the Step 2 level sets

This file formalizes the subsection *Measurability of the level sets* of the blueprint subsection
`subsec:step2Abstract`.

Nothing in `Kakeya/Factoring/Step2.lean` needs any measurability: the pigeonholing of
`Kakeya.MultiplicityFamily.exists_isScaleTriple_lintegral_le` is carried out for the lower integral,
which is monotone in the domain and finitely subadditive with no hypothesis on the sets integrated
over. The later steps nevertheless restrict the shading to the chosen level set and measure the
result, so we record here, still at the abstract level, exactly what has to be assumed for the level
sets `{x | IsScaleTriple t m nhd M k l l' x}` to be measurable.

The two hypotheses are, in the blueprint's notation:

* **(M1)** `∀ j ∈ t, Measurable (m j)`: each function of the family is measurable;
* **(M2)** `∀ j ∈ t, ∀ v, MeasurableSet {x | ∃ y ∈ nhd j x, m j y = v}`: each set of points whose
  `j`-th neighbourhood meets a level set of `m j` is measurable.

Neither implies the other, and (M2) is a hypothesis on the interaction of the neighbourhood
assignment with the family rather than on either separately. The `σ`-algebra on `X` is the one
already carried by the measure space of the abstract data; nothing new is assumed about `X`, and the
measure itself plays no role here, only its `σ`-algebra. Throughout, `ℕ` carries the discrete
`σ`-algebra, so every subset of `ℕ` and of `ℕ × ℕ × ℕ` is measurable.

## Main statements

* `Kakeya.MultiplicityFamily.measurable_card_dyadicLevel` and
  `Kakeya.MultiplicityFamily.measurable_sum_multiplicity` (blueprint
  `lem:step2CardDyadicLevelMeasurable`);
* `Kakeya.MultiplicityFamily.measurableSet_setOf_exists_nhd_dyadic` (blueprint
  `lem:step2NhdDyadicMeasurable`);
* `Kakeya.MultiplicityFamily.measurable_card_dyadicLevelNhd` (blueprint
  `lem:step2CardDyadicLevelNhdMeasurable`);
* `Kakeya.MultiplicityFamily.setOf_isScaleTriple_eq_preimage_scaleCountBox` (blueprint
  `lem:step2LevelSetPreimage`);
* `Kakeya.MultiplicityFamily.measurableSet_setOf_isScaleTriple` (blueprint
  `thm:step2LevelSetMeasurable`).
-/

@[expose] public section

open MeasureTheory

namespace Kakeya.MultiplicityFamily

section Defs

variable {X : Type*} {κ : Type*}

/-- **The scale-count map** (blueprint `def:scaleCountMap`, first half):
`f_k(x) = (m(x), |S_k(x)|, |S̃_k(x)|)`.

It collects the three `ℕ`-valued quantities that `IsScaleTriple` constrains at the point `x`. No
`σ`-algebra on `X` and no hypothesis on the neighbourhood assignment is involved. -/
noncomputable def scaleCountMap (t : Finset κ) (m : κ → X → ℕ) (nhd : κ → X → Set X) (k : ℕ)
    (x : X) : ℕ × ℕ × ℕ :=
  (∑ j ∈ t, m j x, (dyadicLevel t m k x).card, (dyadicLevelNhd t m nhd k x).card)

/-- **The target box of the scale-count map** (blueprint `def:scaleCountMap`, second half):
`T_M(k, l, l') ⊆ ℕ × ℕ × ℕ` is the set of triples `(a, b, c)` satisfying the nine conditions of
`IsScaleTriple` with `∑ j ∈ t, m j x`, `|S_k(x)|` and `|S̃_k(x)|` replaced by `a`, `b` and `c`,
the index set entering only through its cardinality `T`.

The three conditions of Item (a) do not mention `(a, b, c)`: they are constant conjuncts, so that
the box is empty as soon as one of them fails and is the box of the remaining six inequalities
otherwise. Carrying them inside the set is what removes any case distinction on them from
`setOf_isScaleTriple_eq_preimage_scaleCountBox` and `measurableSet_setOf_isScaleTriple`. -/
def scaleCountBox (M T k l l' : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {p | k ≤ Nat.log 2 M ∧ l ≤ l' ∧ l' ≤ Nat.log 2 T ∧
    2 ^ k * 2 ^ l ≤ p.1 ∧ p.1 ≤ scaleTripleConstant M * (2 ^ k * 2 ^ l) ∧
    2 ^ l ≤ p.2.1 ∧ p.2.1 < 2 * 2 ^ l ∧
    2 ^ l' ≤ p.2.2 ∧ p.2.2 < 2 * 2 ^ l'}

/-- **The level set is a preimage under the scale-count map** (blueprint
`lem:step2LevelSetPreimage`): `Ω_M(k, l, l') = f_k⁻¹(T_M(k, l, l'))`.

A pure unfolding of `IsScaleTriple`: no measurability, no hypothesis on `M`, on the triple, on `t`
or on the neighbourhood assignment, and no `σ`-algebra on `X`. -/
theorem setOf_isScaleTriple_eq_preimage_scaleCountBox (t : Finset κ) (m : κ → X → ℕ)
    (nhd : κ → X → Set X) (M k l l' : ℕ) :
    {x | IsScaleTriple t m nhd M k l l' x}
      = scaleCountMap t m nhd k ⁻¹' scaleCountBox M t.card k l l' := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, scaleCountMap, scaleCountBox]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩

end Defs

section Measurable

variable {X : Type*} [MeasurableSpace X] {κ : Type*}

/-- **Measurability of the dyadic level count** (blueprint
`lem:step2CardDyadicLevelMeasurable`, first assertion): under (M1), `x ↦ |S_k(x)|` is measurable.

Only (M1) is used; the neighbourhood assignment plays no role, and `t` is not assumed nonempty. -/
theorem measurable_card_dyadicLevel (t : Finset κ) (m : κ → X → ℕ) (k : ℕ)
    (hm : ∀ j ∈ t, Measurable (m j)) :
    Measurable fun x => (dyadicLevel t m k x).card := by
  classical
  have hcard : (fun x => (dyadicLevel t m k x).card) =
      fun x => ∑ j ∈ t, if 2 ^ k ≤ m j x ∧ m j x < 2 ^ (k + 1) then 1 else 0 := by
    funext x
    simp [dyadicLevel]
  rw [hcard]
  have hS : ∀ j ∈ t, MeasurableSet {x : X | 2 ^ k ≤ m j x ∧ m j x < 2 ^ (k + 1)} := by
    intro j hj
    simpa using (MeasurableSet.preimage (t := ({n : ℕ | 2 ^ k ≤ n ∧ n < 2 ^ (k + 1)} : Set ℕ))
      (by exact MeasurableSet.of_discrete) (hm j hj))
  exact Finset.measurable_sum t fun j hj =>
    Measurable.piecewise (s := {x : X | 2 ^ k ≤ m j x ∧ m j x < 2 ^ (k + 1)})
      (f := fun _ : X => (1 : ℕ)) (g := fun _ : X => (0 : ℕ))
      (hS j hj) measurable_const measurable_const

/-- **Measurability of the total function** (blueprint
`lem:step2CardDyadicLevelMeasurable`, second assertion): under (M1), `x ↦ ∑ j ∈ t, m j x` is
measurable.

This is what makes Item (b) of `IsScaleTriple` a measurable condition. It does not mention the
dyadic scale `k`. -/
theorem measurable_sum_multiplicity (t : Finset κ) (m : κ → X → ℕ)
    (hm : ∀ j ∈ t, Measurable (m j)) :
    Measurable fun x => ∑ j ∈ t, m j x := by
  exact Finset.measurable_sum t fun j hj => hm j hj

/-- **The dyadic neighbourhood condition is measurable** (blueprint
`lem:step2NhdDyadicMeasurable`): under (M2) for the single function `f`, the set
`Ã_{f,k} = {x | ∃ y ∈ nhd x, 2 ^ k ≤ f y < 2 ^ (k + 1)}` is measurable.

This is the only statement of the file that uses (M2). The blueprint states it at a single index
`j ∈ t` of the family; since only `m j` occurs, it is stated here for a bare function `f`, and is
applied at `f := m j` in `measurable_card_dyadicLevelNhd`. No index set `t` occurs. -/
theorem measurableSet_setOf_exists_nhd_dyadic (f : X → ℕ) (nhd : X → Set X) (k : ℕ)
    (hnhd : ∀ v : ℕ, MeasurableSet {x | ∃ y ∈ nhd x, f y = v}) :
    MeasurableSet {x | ∃ y ∈ nhd x, 2 ^ k ≤ f y ∧ f y < 2 ^ (k + 1)} := by
  rw [show
      {x : X | ∃ y ∈ nhd x, 2 ^ k ≤ f y ∧ f y < 2 ^ (k + 1)}
        = {x : X | ∃ v ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ∃ y ∈ nhd x, f y = v} by
      ext x
      constructor
      · rintro ⟨y, hy, hk⟩
        refine ⟨f y, Finset.mem_Ico.mpr ⟨hk.1, hk.2⟩, y, hy, rfl⟩
      · rintro ⟨v, hv, y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        exact Finset.mem_Ico.mp hv]
  convert Finset.measurableSet_biUnion (Finset.Ico (2 ^ k) (2 ^ (k + 1)))
      (fun y _ => hnhd y) using 1
  · ext x
    simp

/-- **Measurability of the neighbourhood level count** (blueprint
`lem:step2CardDyadicLevelNhdMeasurable`): under (M2), `x ↦ |S̃_k(x)|` is measurable.

Only (M2) is used: the values of the `m j` at the point `x` itself are never tested, so (M1) is not
needed here. -/
theorem measurable_card_dyadicLevelNhd (t : Finset κ) (m : κ → X → ℕ) (nhd : κ → X → Set X) (k : ℕ)
    (hnhd : ∀ j ∈ t, ∀ v : ℕ, MeasurableSet {x | ∃ y ∈ nhd j x, m j y = v}) :
    Measurable fun x => (dyadicLevelNhd t m nhd k x).card := by
  classical
  let A : κ → Set X := fun j => {x | ∃ y ∈ nhd j x, 2 ^ k ≤ m j y ∧ m j y < 2 ^ (k + 1)}
  have hsum : (fun x : X => (dyadicLevelNhd t m nhd k x).card)
      = fun x => ∑ j ∈ t, (A j).indicator (fun _ : X => 1) x := by
    funext x
    rw [dyadicLevelNhd, Finset.card_filter]
    simp [A, Set.indicator]
  rw [hsum]
  exact Finset.measurable_sum t (fun j hj =>
    measurable_const.indicator (measurableSet_setOf_exists_nhd_dyadic (m j) (nhd j) k (hnhd j hj)))

/-- **The level sets are measurable** (blueprint `thm:step2LevelSetMeasurable`): under (M1) and
(M2), the level set `Ω_M(k, l, l') = {x | IsScaleTriple t m nhd M k l l' x}` is measurable.

No hypothesis on `M`, on the triple, or on the nonemptiness of `t` or of the level set is needed.
This is what turns the lower integrals of `exists_isScaleTriple_lintegral_le` into integrals over a
measurable set. -/
theorem measurableSet_setOf_isScaleTriple (t : Finset κ) (m : κ → X → ℕ) (nhd : κ → X → Set X)
    (M k l l' : ℕ) (hm : ∀ j ∈ t, Measurable (m j))
    (hnhd : ∀ j ∈ t, ∀ v : ℕ, MeasurableSet {x | ∃ y ∈ nhd j x, m j y = v}) :
    MeasurableSet {x | IsScaleTriple t m nhd M k l l' x} := by
  rw [setOf_isScaleTriple_eq_preimage_scaleCountBox]
  have hsum : Measurable fun x : X => ∑ j ∈ t, m j x :=
    measurable_sum_multiplicity t m hm
  have hlvl : Measurable fun x : X => (dyadicLevel t m k x).card :=
    measurable_card_dyadicLevel t m k hm
  have hnh : Measurable fun x : X => (dyadicLevelNhd t m nhd k x).card :=
    measurable_card_dyadicLevelNhd t m nhd k hnhd
  have hf : Measurable (scaleCountMap t m nhd k) := by
    unfold scaleCountMap
    exact Measurable.prodMk hsum (Measurable.prodMk hlvl hnh)
  exact MeasurableSet.preimage
    (show MeasurableSet (scaleCountBox M t.card k l l') from MeasurableSet.of_discrete) hf

end Measurable

end Kakeya.MultiplicityFamily
