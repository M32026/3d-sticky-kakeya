/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AngleDef
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# Transporting the two-sided typical angle across a deletion

`Kakeya.HasMaxPlankAngleBound` is monotone under shrinking the family, so the slab layer
survives an arbitrary deletion for free.  The two-sided `Kakeya.IsTypicalPlankAngle` is
**not** monotone: deleting
planks can destroy the lower bound `θ ≤ C · M(fibre)`, and a full-fibre comparability statement
recovers only that, not the sub-fibre stability clause that `Kakeya.IsTypicalPlankAngle` also
demands.

This file supplies the missing step.  The observation is a bookkeeping one about the two stability
scales: a scale really must be *spent* on the deletion.  If the surviving fibre keeps a `q`-fraction
of the original fibre, then a sub-fibre keeping an `A⁻¹`-fraction of the *surviving* fibre
keeps only an `A⁻¹ · q`-fraction of the original one.  So the two-sided predicate at scale `A`
on the deleted family follows from the stability clause at any old scale `B` whose budget covers
the deletion,
`A ≤ q · B` — the deletion consumes `q`, and what is left is the scale of the conclusion.

`Plank.isTypicalPlankAngle_of_fibreRetention` is that general statement, with the budget written
multiplicatively on purpose: the equivalent `A ≤ B / q` would invite zero and inverse boundary
problems.

The general form is what lets a lossy deletion of retained fraction `q` be paid for out of a
*reserve* scale, instead of forcing the reserve to be exactly one factor of `A`.  Composing with
`Kakeya.IsTypicalPlankAngle.mono_scale` then delivers the conclusion at any smaller scale.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-- **The two-sided typical angle survives a deletion whose retained fraction fits the scale
budget (extra66, `note:isTypicalPlankAngleOfFibreKeep`).**

Let `(s₂, Y₂)` be obtained from `(s, Y₁)` by shrinking the index set and the shades, in such a way
that at every point of the new union the new fibre retains a `q`-fraction of the old fibre
(`hkeep`).  Let `B` be an old stability scale whose budget covers the deletion, `A ≤ q · B`
(`hbudget`).  If the old family satisfies the two-sided comparability at constant `C` for *every*
sub-fibre retaining a `B⁻¹`-fraction (`hstab`), then the new family satisfies
`Kakeya.IsTypicalPlankAngle` at `(θ, C, A)`.

Both clauses of `Kakeya.IsTypicalPlankFibre` come out of `hstab`: the full-fibre one by taking the
new fibre itself as the sub-fibre (legitimate because `1 ≤ A ≤ q · B` gives `B⁻¹ ≤ q`, so `hkeep`
already places it above the `B⁻¹`-threshold), and the sub-fibre one by composing the two fractions,
where `A ≤ q · B` is exactly `B⁻¹ ≤ A⁻¹ · q`.

The budget is stated multiplicatively rather than as `A ≤ B / q`, to keep the statement away from
the zero and inverse boundary cases.  No positivity hypothesis on `q` is imposed, since
`0 < 1 ≤ A ≤ q · B` with `0 ≤ B` already forces `0 < q` and `0 < B`. -/
theorem isTypicalPlankAngle_of_fibreRetention {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s s₂ : Finset ι) (hs₂ : s₂ ⊆ s)
    (Y₁ Y₂ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) (θ C A B : ℝ≥0) (q : ℝ) (hA : 1 ≤ A)
    (hbudget : (A : ℝ) ≤ q * (B : ℝ))
    (hshade : ∀ i ∈ s₂, (Y₂ i).shade ⊆ (Y₁ i).shade)
    (hkeep : ∀ x ∈ ⋃ i ∈ s₂, (Y₂ i).shade,
      q * ((Kakeya.shadeFibre s Y₁ x).card : ℝ)
        ≤ ((Kakeya.shadeFibre s₂ Y₂ x).card : ℝ))
    (hstab : ∀ x ∈ ⋃ i ∈ s, (Y₁ i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y₁ x,
      ((B : ℝ))⁻¹ * ((Kakeya.shadeFibre s Y₁ x).card : ℝ) ≤ (t.card : ℝ) →
        θ ≤ C * Kakeya.maxPlankAngle P t ∧ Kakeya.maxPlankAngle P t ≤ C * θ) :
    Kakeya.IsTypicalPlankAngle s₂ Y₂ P θ C A := by
  intro x hx
  set F₁ := Kakeya.shadeFibre s Y₁ x with hF₁
  set F₂ := Kakeya.shadeFibre s₂ Y₂ x with hF₂
  have hApos : 0 < (A : ℝ) := by
    have hApos_nnreal : (0 : ℝ≥0) < A := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hA
    exact_mod_cast hApos_nnreal
  have hBpos : 0 < (B : ℝ) := by
    have hB_nonneg : 0 ≤ (B : ℝ) := NNReal.coe_nonneg _
    have h1le_qB : (1 : ℝ) ≤ q * (B : ℝ) := le_trans (by exact_mod_cast hA) hbudget
    by_contra! hle
    have hBzero : (B : ℝ) = 0 := le_antisymm hle hB_nonneg
    have hzero : q * (B : ℝ) = 0 := by simp [hBzero]
    linarith
  have hBinv_le_q : (B : ℝ)⁻¹ ≤ q := by
    have h1le_qB : (1 : ℝ) ≤ q * (B : ℝ) := le_trans (by exact_mod_cast hA) hbudget
    calc
      (B : ℝ)⁻¹ = 1 * (B : ℝ)⁻¹ := by simp
      _ ≤ (q * (B : ℝ)) * (B : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h1le_qB (by positivity)
      _ = q := by field_simp [hBpos.ne.symm]
  have hBinv_le_Ainv_mul_q : (B : ℝ)⁻¹ ≤ (A : ℝ)⁻¹ * q := by
    calc
      (B : ℝ)⁻¹ = (A : ℝ)⁻¹ * ((A : ℝ) * (B : ℝ)⁻¹) := by
        field_simp [hApos.ne.symm, hBpos.ne.symm]
      _ ≤ (A : ℝ)⁻¹ * q := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc
          (A : ℝ) * (B : ℝ)⁻¹ ≤ (q * (B : ℝ)) * (B : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hbudget (by positivity)
          _ = q := by field_simp [hBpos.ne.symm]
  have hxU₁ : x ∈ ⋃ i ∈ s, (Y₁ i).shade := by
    simp only [Set.mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, hs₂ hi, hshade i hi hxi⟩
  have hsubfib : F₂ ⊆ F₁ := by
    intro j hj
    rw [Kakeya.mem_shadeFibre] at hj ⊢
    exact ⟨hs₂ hj.1, hshade j hj.1 hj.2⟩
  have hkeep_x : q * (F₁.card : ℝ) ≤ (F₂.card : ℝ) := by
    simpa [hF₁, hF₂] using hkeep x hx
  have h_full_fibre : (B : ℝ)⁻¹ * (F₁.card : ℝ) ≤ (F₂.card : ℝ) := by
    calc
      (B : ℝ)⁻¹ * (F₁.card : ℝ) ≤ q * (F₁.card : ℝ) :=
        mul_le_mul_of_nonneg_right hBinv_le_q (by positivity)
      _ ≤ (F₂.card : ℝ) := hkeep_x
  have h_comp : Kakeya.ComparableScalars C θ (Kakeya.maxPlankAngle P F₂) := by
    have htemp := hstab x hxU₁ F₂ hsubfib h_full_fibre
    rcases htemp with ⟨h1, h2⟩
    dsimp [Kakeya.ComparableScalars, Kakeya.ComparableScalarsWith]
    exact ⟨h1, h2⟩
  have h_stable : ∀ t ⊆ F₂, A⁻¹ * (F₂.card : ℝ≥0) ≤ (t.card : ℝ≥0) →
      Kakeya.ComparableScalars C θ (Kakeya.maxPlankAngle P t) := by
    intro t ht hfrac
    have hfrac_real : (A : ℝ)⁻¹ * (F₂.card : ℝ) ≤ (t.card : ℝ) := by
      have htemp := NNReal.coe_le_coe.mp hfrac
      rw [← NNReal.coe_inv A]
      exact htemp
    have hBinv_F1_le_tcard : (B : ℝ)⁻¹ * (F₁.card : ℝ) ≤ (t.card : ℝ) := by
      calc
        (B : ℝ)⁻¹ * (F₁.card : ℝ) ≤ ((A : ℝ)⁻¹ * q) * (F₁.card : ℝ) :=
          mul_le_mul_of_nonneg_right hBinv_le_Ainv_mul_q (by positivity)
        _ = (A : ℝ)⁻¹ * (q * (F₁.card : ℝ)) := by ring
        _ ≤ (A : ℝ)⁻¹ * (F₂.card : ℝ) :=
          mul_le_mul_of_nonneg_left hkeep_x (by positivity)
        _ ≤ (t.card : ℝ) := hfrac_real
    have htemp := hstab x hxU₁ t (ht.trans hsubfib) hBinv_F1_le_tcard
    rcases htemp with ⟨h1, h2⟩
    dsimp [Kakeya.ComparableScalars, Kakeya.ComparableScalarsWith]
    exact ⟨h1, h2⟩
  dsimp [Kakeya.IsTypicalPlankAngle, Kakeya.IsTypicalPlankFibre]
  exact ⟨h_comp, h_stable⟩

end Plank

end
