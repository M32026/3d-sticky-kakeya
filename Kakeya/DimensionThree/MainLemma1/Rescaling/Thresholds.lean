/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading
public import Kakeya.Mathlib.ENNReal

/-!
# Main Lemma 1, Case (ii): fullness thresholds

The three fullness lemmas of the reduction to the `b`-tubes, split out of
`Kakeya/DimensionThree/MainLemma1/Rescaling.lean` (blueprint
`GWZAdapted/section8_endgame.tex`, the subsection "Fullness thresholds"):

* `Kakeya.ml1Boot.le_fullness_of_termwise` (blueprint `lem:ml1bootFullnessSubfamilyLower`);
* `Kakeya.ml1Boot.coarse_fullness_threshold` (blueprint `lem:ml1bootCoarseFullnessThreshold`);
* `Kakeya.ml1Boot.fine_fullness_threshold` (blueprint `lem:ml1bootFineFullnessThreshold`).

Nothing here is geometric: the statements are about `ShadedBody.fullness` and `ENNReal`
arithmetic only, and the shaded families enter through their carriers' volumes. That is why
they live in their own module — they are reusable at any scale and are the arithmetic
backbone of `Kakeya.ml1Boot.normalized_le_of_coarse`.

The two threshold lemmas carry their constant as a **free parameter** `≥ 1` rather than as
`Kakeya.ml1Boot.factorOneScale.C` / `Kakeya.ml1Boot.fineFactor.C`, because the dilate chain
needs them at the larger constants `Kakeya.ml1Boot.factorOneScaleUniformDilate.C` and
`Kakeya.ml1Boot.fineNormalizeDilate.C c`, and neither instance follows from the one at the
smaller constant. Carrying the constant free is also what lets the dilation ratio `c` stay free
in the fine chain: these lemmas never see it. See blueprint `note:ml1bootArithFreeConstant`.
-/

@[expose] public section

open MeasureTheory ShadedBody

namespace Kakeya

namespace ml1Boot

section Thresholds

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A termwise density bound passes to every subfamily** (blueprint
`lem:ml1bootFullnessSubfamilyLower`).

If every member of a shaded family satisfies `λ₀ |V i| ≤ |Z i|` and the carriers have positive
finite volume, then *every* nonempty subfamily has fullness at least `λ₀`.

The hypothesis is termwise and that is the whole content: a lower bound on `λ(𝕍, Z)` alone
would not pass to a subfamily, fullness being a ratio of two sums.  This is why
`Kakeya.ml1Boot.exists_factorOneScaleUniform`(a) and (b) are stated with two-sided densities
rather than with a fullness bound.  It is the sibling of
`ShadedBody.le_fullness_of_volume_le`. -/
theorem le_fullness_of_termwise {ι : Type*} {s : Finset ι} (V : ι → ShadedBody E)
    {lam₀ : ENNReal}
    (hpos : ∀ i ∈ s, 0 < volume (V i).carrier)
    (hfin : ∀ i ∈ s, volume (V i).carrier ≠ ⊤)
    (hterm : ∀ i ∈ s, lam₀ * volume (V i).carrier ≤ volume (V i).shade)
    {S : Finset ι} (hSs : S ⊆ s) (hS : S.Nonempty) :
    lam₀ ≤ (ShadedBody.fullness S V : ENNReal) := by
  have hposOnS : ∀ i ∈ S, 0 < volume (V i).carrier := fun i hi => hpos i (hSs hi)
  have hfinOnS : ∀ i ∈ S, volume (V i).carrier ≠ ⊤ := fun i hi => hfin i (hSs hi)
  have hsum : lam₀ * (∑ i ∈ S, volume (V i).carrier) ≤ ∑ i ∈ S, volume (V i).shade := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => hterm i (hSs hi))
  have hDne0 : (∑ i ∈ S, volume (V i).carrier) ≠ 0 := by
    intro hzero
    rcases hS with ⟨i, hi⟩
    exact (ne_of_gt (hposOnS i hi)) ((Finset.sum_eq_zero_iff.mp hzero) i hi)
  have hDneTop : (∑ i ∈ S, volume (V i).carrier) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hfinOnS
  rw [ShadedBody.fullness_def]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hDne0) (Or.inl hDneTop)).2 hsum

/-- **The coarse fullness threshold** (blueprint `lem:ml1bootCoarseFullnessThreshold`).

Write `C₁ = Kakeya.ml1Boot.factorOneScale.C`.  The coarse shading density `λ_ρ` that
`Kakeya.ml1Boot.exists_factorOneScaleUniform`(b) returns is at least
`C₁⁻¹ δ̃ ^ ap' λ(𝕍, Z) ≥ C₁⁻¹ δ̃ ^ (a + ap')`, and the exponent gap left by
`a + 2 ap' ≤ ηc` absorbs the constant `C₁` once `C₁ δ̃ ^ ap' ≤ 1`.  Hence the coarse family
clears the threshold `δ̃ ^ ηc` at which the coarse bound `multTildeTb` of
`Kakeya.ml1Boot.normalized_le_of_coarse`(e) is available.

`a` is the blueprint's `η_{j-1}` and `ap'` its `η'_{j-1}`.  The blueprint's fine family
`(𝕍, Z)` enters only through its fullness, which is carried here as the bare quantity `lam`;
nothing else about it is used.

## The free constant `Cc`

The factoring constant is carried as a **parameter** `Cc ≥ 1` and not as
`Kakeya.ml1Boot.factorOneScale.C`, because the dilate chain needs the lemma at
`Cc = Kakeya.ml1Boot.factorOneScaleUniformDilate.C` and that instance does not follow from the
one at the smaller constant: `Cc` occurs in the *hypothesis* `hlamρ`, so the larger constant
gives the weaker hypothesis.  See blueprint `note:ml1bootArithFreeConstant`. -/
theorem coarse_fullness_threshold {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {Cc : NNReal} (hCc : 1 ≤ Cc)
    {a ap' ηc : ℝ} (ha : 0 ≤ a) (hap' : 0 < ap') (hηc : a + 2 * ap' ≤ ηc)
    (habsorb : (Cc : ENNReal) * (δt : ENNReal) ^ ap' ≤ 1)
    {lam lamρ : ENNReal} (hlam : (δt : ENNReal) ^ a ≤ lam)
    (hlamρ : (Cc : ENNReal)⁻¹ * (δt : ENNReal) ^ ap' * lam ≤ lamρ)
    {κ : Type*} {t'' : Finset κ} (W : κ → ShadedBody E) (ht'' : t''.Nonempty)
    (hpos : ∀ k ∈ t'', 0 < volume (W k).carrier)
    (hfin : ∀ k ∈ t'', volume (W k).carrier ≠ ⊤)
    (hterm : ∀ k ∈ t'', lamρ * volume (W k).carrier ≤ volume (W k).shade) :
    (δt : ENNReal) ^ ηc ≤ (ShadedBody.fullness t'' W : ENNReal) := by
  have hfull : lamρ ≤ (ShadedBody.fullness t'' W : ENNReal) := by
    exact le_fullness_of_termwise (s := t'') W (lam₀ := lamρ) hpos hfin hterm
      (S := t'') (by exact subset_rfl) ht''
  have hδne : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
  have hδtop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδle1 : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  have hC0 : (Cc : ENNReal) ≠ 0 := by
    have h1 : (1 : ENNReal) ≤ (Cc : ENNReal) := by exact_mod_cast hCc
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
  have hCtop : (Cc : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    (δt : ENNReal) ^ ηc ≤ (δt : ENNReal) ^ (a + 2 * ap') := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge hδle1 hηc
    _ ≤ (Cc : ENNReal)⁻¹ * (δt : ENNReal) ^ (a + ap') := by
      have hsplit : (δt : ENNReal) ^ (a + 2 * ap')
          = (δt : ENNReal) ^ ap' * (δt : ENNReal) ^ (a + ap') := by
        rw [show a + 2 * ap' = ap' + (a + ap') from by ring]
        rw [← ENNReal.rpow_add (x := (δt : ENNReal)) ap' (a + ap') hδne hδtop]
      have hmul : (Cc : ENNReal) * (δt : ENNReal) ^ (a + 2 * ap')
          ≤ (δt : ENNReal) ^ (a + ap') := by
        calc
          (Cc : ENNReal) * (δt : ENNReal) ^ (a + 2 * ap')
              = (Cc : ENNReal) *
                  ((δt : ENNReal) ^ ap' * (δt : ENNReal) ^ (a + ap')) := by
                rw [hsplit]
              _ = (Cc : ENNReal) * (δt : ENNReal) ^ ap'
                    * (δt : ENNReal) ^ (a + ap') := by
                rw [← mul_assoc]
              _ ≤ (1 : ENNReal) * (δt : ENNReal) ^ (a + ap') := by
                exact mul_le_mul_left habsorb ((δt : ENNReal) ^ (a + ap'))
              _ = (δt : ENNReal) ^ (a + ap') := by simp
      exact (ENNReal.mul_le_iff_le_inv hC0 hCtop).mp hmul
    _ ≤ lamρ := by
      calc
        (Cc : ENNReal)⁻¹ * (δt : ENNReal) ^ (a + ap')
            = (Cc : ENNReal)⁻¹ *
                ((δt : ENNReal) ^ ap' * (δt : ENNReal) ^ a) := by
              rw [show a + ap' = ap' + a from by ring]
              rw [ENNReal.rpow_add_of_nonneg (x := (δt : ENNReal)) ap' a (le_of_lt hap') ha]
            _ = (Cc : ENNReal)⁻¹ * (δt : ENNReal) ^ ap'
                * (δt : ENNReal) ^ a := by
              rw [← mul_assoc]
            _ ≤ (Cc : ENNReal)⁻¹ * (δt : ENNReal) ^ ap' * lam := by
              exact mul_le_mul_right hlam
                ((Cc : ENNReal)⁻¹ * (δt : ENNReal) ^ ap')
            _ ≤ lamρ := hlamρ
    _ ≤ (ShadedBody.fullness t'' W : ENNReal) := hfull

/-- **The fine fullness threshold** (blueprint `lem:ml1bootFineFullnessThreshold`).

Write `C₂ = Kakeya.ml1Boot.fineFactor.C`.  The fine shading density `λ_σ` that
`Kakeya.ml1Boot.exists_factorOneScaleUniform`(a) returns is at least `δ̃ ^ ap' λ(𝕍, Z)`, so
under `a + 2 ap' ≤ ηf` and `4 C₂ δ̃ ^ ap' ≤ 1` *every* nonempty subfamily of the refined fine
family clears the threshold `4 C₂ δ̃ ^ ηf` of hypothesis (b) of
`Kakeya.ml1Boot.reduceToTb_fine_bound`, the factor `4` being the `Λ²` of
`Kakeya.ml1Boot.fine_genKF` at `Λ = 2`.

The quantifier over subfamilies is what makes this usable: the fibre of the parent map over a
retained parent is such a subfamily, and it is not known in advance.  As in
`Kakeya.ml1Boot.coarse_fullness_threshold`, the family whose fullness bounds `λ_σ` from below
enters only through the bare quantity `lam`.

## The free constant `C`

The normalization constant is carried as a **parameter** `C ≥ 1` and not as
`Kakeya.ml1Boot.fineFactor.C`, because the dilate chain needs the lemma at
`C = Kakeya.ml1Boot.fineNormalizeDilate.C c` and that instance does not follow from the one at
the smaller constant: `C` occurs in the *conclusion*, so the instance at the larger constant is
the stronger statement.  See blueprint `note:ml1bootArithFreeConstant`. -/
theorem fine_fullness_threshold {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {C : NNReal} (_hC : 1 ≤ C)
    {a ap' ηf : ℝ} (ha : 0 ≤ a) (hap' : 0 < ap') (hηf : a + 2 * ap' ≤ ηf)
    (habsorb : 4 * (C : ENNReal) * (δt : ENNReal) ^ ap' ≤ 1)
    {lam lamσ : ENNReal} (hlam : (δt : ENNReal) ^ a ≤ lam)
    (hlamσ : (δt : ENNReal) ^ ap' * lam ≤ lamσ)
    {ι : Type*} {s' : Finset ι} (Z : ι → ShadedBody E)
    (hpos : ∀ i ∈ s', 0 < volume (Z i).carrier)
    (hfin : ∀ i ∈ s', volume (Z i).carrier ≠ ⊤)
    (hterm : ∀ i ∈ s', lamσ * volume (Z i).carrier ≤ volume (Z i).shade)
    {S : Finset ι} (hSs : S ⊆ s') (hS : S.Nonempty) :
    4 * (C : ENNReal) * (δt : ENNReal) ^ ηf
      ≤ (ShadedBody.fullness S Z : ENNReal) := by
  have hfull : lamσ ≤ (ShadedBody.fullness S Z : ENNReal) :=
    le_fullness_of_termwise (s := s') Z (lam₀ := lamσ) hpos hfin hterm hSs hS
  have hδne : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
  have hδtop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδle1 : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  calc
    4 * (C : ENNReal) * (δt : ENNReal) ^ ηf
        ≤ 4 * (C : ENNReal) * (δt : ENNReal) ^ (a + 2 * ap') := by
          exact mul_le_mul_right
            (ENNReal.rpow_le_rpow_of_exponent_ge hδle1 hηf) (4 * (C : ENNReal))
    _ = (4 * (C : ENNReal) * (δt : ENNReal) ^ ap') * (δt : ENNReal) ^ (a + ap') := by
        have hsplit : (δt : ENNReal) ^ (a + 2 * ap')
            = (δt : ENNReal) ^ ap' * (δt : ENNReal) ^ (a + ap') := by
          rw [show a + 2 * ap' = ap' + (a + ap') from by ring]
          rw [← ENNReal.rpow_add (x := (δt : ENNReal)) ap' (a + ap') hδne hδtop]
        rw [hsplit, ← mul_assoc]
    _ ≤ 1 * (δt : ENNReal) ^ (a + ap') := by
        exact mul_le_mul_left habsorb ((δt : ENNReal) ^ (a + ap'))
    _ = (δt : ENNReal) ^ (a + ap') := by simp
    _ ≤ lamσ := by
        calc
          (δt : ENNReal) ^ (a + ap')
              = (δt : ENNReal) ^ ap' * (δt : ENNReal) ^ a := by
                rw [show a + ap' = ap' + a from by ring]
                rw [ENNReal.rpow_add_of_nonneg (x := (δt : ENNReal)) ap' a (le_of_lt hap') ha]
            _ ≤ (δt : ENNReal) ^ ap' * lam := by
                exact mul_le_mul_right hlam ((δt : ENNReal) ^ ap')
            _ ≤ lamσ := hlamσ
    _ ≤ (ShadedBody.fullness S Z : ENNReal) := hfull

end Thresholds

end ml1Boot

end Kakeya
