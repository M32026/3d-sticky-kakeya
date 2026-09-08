/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Basic

/-!
# Prescribed affine thicknesses

Throughout the development the blueprint records the shape of a convex body by a chain of
comparisons `τ₀(K) ∼ t 0`, `τ₁(K) ∼ t 1`, … of its affine thicknesses with a prescribed
sequence of scales, with an implicit constant. `Kakeya.HasThicknesses` is that statement
with the implicit constant made explicit.

The predicate is indexed by an arbitrary `Fin n`, so that it can be used in dimension-generic
statements; in a space of dimension `d` one takes `n = d` (equivalently, a vector
`![t₀, …, t_{d-1}]`), which is the only case appearing in the blueprint.
-/

@[expose] public section

namespace Kakeya

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A set `K` has affine thicknesses comparable, with constant `C`, to the prescribed
sequence `t : Fin n → ℝ`: this is the meaning of the blueprint's `τ_k(K) ∼ t k`, with the
implicit constant made explicit.

The length `n` of the sequence is arbitrary; the statements of the development instantiate
it at the dimension of the ambient space, so that a three-dimensional body is described by
`HasThicknesses K C ![t₀, t₁, t₂]`. -/
def HasThicknesses {n : ℕ} (K : Set E) (C : NNReal) (t : Fin n → ℝ) : Prop :=
  ∀ k : Fin n, (C : ℝ)⁻¹ * t k ≤ Metric.thickness ℝ K (k : ℕ) ∧
    Metric.thickness ℝ K (k : ℕ) ≤ C * t k

/-- **Thickness profiles survive a squeeze between two profiled sets** (blueprint
`lem:hasThicknessesSandwich`): a set `K` caught between `A ⊆ K ⊆ A'`, where `A` has profile `t`
with constant `C` and `A'` has profile `t` with the larger constant `C'`, has profile `t` with
constant `C'`.

Only the *lower* half of the hypothesis on `A` and the *upper* half of that on `A'` are used,
`Metric.thickness` being monotone under inclusion of bounded sets; no set need be convex, and
the two containments are all that relates the three. The hypotheses `0 < C` and `C ≤ C'` are
what let the inner lower bound be weakened to the outer constant, together with `0 ≤ t k`.

It is the set-level companion of `ConvexSpaceBody.hasThicknesses_of_between`, which squeezes
between a body and one of its closed neighbourhoods and hence *computes* the outer profile
rather than assuming it. The general form is what a consumer holding an enlargement sandwich
**after** an affine change of variables needs: an affine map does not commute with closed
neighbourhoods, so the two ends of the transported sandwich have to be compared directly. -/
theorem HasThicknesses.of_sandwich {n : ℕ} {A K A' : Set E} {C C' : NNReal} {t : Fin n → ℝ}
    (hAK : A ⊆ K) (hKA' : K ⊆ A') (hA'bdd : Bornology.IsBounded A')
    (hC : 0 < C) (hCC' : C ≤ C') (ht : ∀ k, 0 ≤ t k)
    (hA : HasThicknesses A C t) (hA' : HasThicknesses A' C' t) :
    HasThicknesses K C' t := by
  intro k
  constructor
  · -- lower bound
    have hKbdd : Bornology.IsBounded K := hA'bdd.subset hKA'
    have hmonoK : Metric.thickness ℝ A ≤ Metric.thickness ℝ K := by
      exact Metric.thickness_monotone hKbdd hAK
    have hinv : ((C' : NNReal) : ℝ)⁻¹ ≤ (C : ℝ)⁻¹ := by
      have hcpos : 0 < (C : ℝ) := by exact_mod_cast hC
      have hc'pos : 0 < (C' : ℝ) := by
        exact lt_of_lt_of_le hcpos (by exact_mod_cast hCC')
      exact (inv_le_inv₀ hc'pos hcpos).2 (by exact_mod_cast hCC')
    calc
      ((C' : NNReal) : ℝ)⁻¹ * t k ≤ (C : ℝ)⁻¹ * t k := by
        exact mul_le_mul_of_nonneg_right hinv (ht k)
      _ ≤ Metric.thickness ℝ A k := (hA k).1
      _ ≤ Metric.thickness ℝ K k := hmonoK k
  · -- upper bound
    have hmonoK' : Metric.thickness ℝ K ≤ Metric.thickness ℝ A' := by
      exact Metric.thickness_monotone hA'bdd hKA'
    calc
      Metric.thickness ℝ K k ≤ Metric.thickness ℝ A' k := hmonoK' k
      _ ≤ ((C' : NNReal) : ℝ) * t k := (hA' k).2

end Kakeya
