/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading

/-!
# Selecting a fibre of maximal fullness

Proposition 5.1 splits the fine family over a set of outer cells and supplies its inner data
*fibrewise*, but Section 6.6(B) needs a fullness lower bound on **one** fibre.  Passing from the
global bound to a single fibre looks like it should cost a factor `1 / |cells|`, and it would if
fullness were a mass.  It is not: `ShadedBody.fullness s V` is the ratio

`(∑_{i ∈ s} |Y i|) / (∑_{i ∈ s} |carrier i|)`,

so the correct pigeonhole is the *mediant* inequality — a ratio of sums never exceeds the largest of
the ratios of its parts.  Selecting the fibre of maximal fullness therefore costs **nothing**.

The proof is the one-line mediant argument in the form the repository already has it: by
`ShadedBody.sum_volumeReal_shade_eq_fullness_mul`, each fibre's shade mass is its fullness times its
carrier mass, so summing over fibres bounds the total shade mass by `maxFullness × (total carrier
mass)`, and the same identity for `s` lets the common carrier mass be cancelled.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

/-- **Mediant fibre selection for fullness.**

If the fibres of `p` cover `s` and the total carrier mass of `s` is nonzero and finite, some fibre
is at least as full as `s` itself.  No cardinality loss: fullness is a ratio, not a mass. -/
theorem exists_fibre_fullness_le
    {ι κ : Type*} [DecidableEq κ] (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (ts : Finset κ) (p : ι → κ) (hp : ∀ i ∈ s, p i ∈ ts) (hts : ts.Nonempty)
    (hB0 : (∑ i ∈ s, volume (V i).carrier) ≠ 0)
    (hBtop : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤) :
    ∃ x ∈ ts, ShadedBody.fullness s V
      ≤ ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V := by
  classical
  let A : ENNReal := ∑ i ∈ s, volume (V i).shade
  let B : ENNReal := ∑ i ∈ s, volume (V i).carrier
  let Ax : κ → ENNReal := fun x => ∑ i ∈ {i ∈ s | p i = x}, volume (V i).shade
  let Bx : κ → ENNReal := fun x => ∑ i ∈ {i ∈ s | p i = x}, volume (V i).carrier
  have hB0' : B ≠ 0 := by simpa [B] using hB0
  have hBtop' : B ≠ ⊤ := by simpa [B] using hBtop
  obtain ⟨x₀, hx₀ts, hx₀⟩ :=
    Finset.exists_max_image ts (fun x => ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V) hts
  have hsumA : (∑ x ∈ ts, Ax x) = A := by
    simpa [Ax, A] using (Finset.sum_fiberwise_of_maps_to hp (fun i => volume (V i).shade))
  have hsumB : (∑ x ∈ ts, Bx x) = B := by
    simpa [Bx, B] using (Finset.sum_fiberwise_of_maps_to hp (fun i => volume (V i).carrier))
  have hAmul : (ShadedBody.fullness s V : ENNReal) * B = A := by
    simpa [A, B] using (ShadedBody.sum_volumeReal_shade_eq_fullness_mul s V).symm
  have hAximul : ∀ x : κ,
      Ax x = (ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V : ENNReal) * Bx x := by
    intro x
    simpa [Ax, Bx] using
      (ShadedBody.sum_volumeReal_shade_eq_fullness_mul ({i ∈ s | p i = x} : Finset ι) V)
  have hle : (ShadedBody.fullness s V : ENNReal) * B ≤
      (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ENNReal) * B := by
    calc
      (ShadedBody.fullness s V : ENNReal) * B = A := hAmul
      _ = ∑ x ∈ ts, Ax x := hsumA.symm
      _ = ∑ x ∈ ts, (ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V : ENNReal) * Bx x := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact hAximul x
      _ ≤ ∑ x ∈ ts,
          (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ENNReal) * Bx x := by
        exact Finset.sum_le_sum (fun x hx =>
          mul_le_mul_left (ENNReal.coe_le_coe.mpr (hx₀ x hx)) (Bx x))
      _ = (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ENNReal) *
          ∑ x ∈ ts, Bx x := by
        rw [← Finset.mul_sum]
      _ = (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ENNReal) * B := by
        rw [hsumB]
  have hcoe : (ShadedBody.fullness s V : ENNReal) ≤
      (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ENNReal) :=
    (ENNReal.mul_le_mul_iff_left hB0' hBtop').mp hle
  refine ⟨x₀, hx₀ts, ?_⟩
  exact ENNReal.coe_le_coe.mp hcoe

/-- **A `c`-refinement loses at most `c` in fullness.**

`ShadedBody.IsCRefinement` is a statement about shade *mass*: `c · ∑_s |Y| ≤ ∑_{s'} |Y'|`.  Fullness
is a ratio, and the refinement keeps the carriers of the indices it retains while dropping the
others, so its denominator only shrinks.  Hence the mass inequality passes to the ratio with the
same constant and no cardinality loss.

This is the step that carries the Proposition-5.1 refinement clause into the fibre selection of
Section 6.6(B). -/
theorem mul_fullness_le_of_isCRefinement
    {ι : Type*} {s' s : Finset ι} {V' V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {c : ℝ≥0}
    (h : ShadedBody.IsCRefinement s' V' s V c)
    (hB0 : (∑ i ∈ s, volume (V i).carrier) ≠ 0)
    (hBtop : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤) :
    c * ShadedBody.fullness s V ≤ ShadedBody.fullness s' V' := by
  classical
  rcases h with ⟨⟨hs's, href⟩, hmass⟩
  let A : ENNReal := ∑ i ∈ s, volume (V i).shade
  let B : ENNReal := ∑ i ∈ s, volume (V i).carrier
  let A' : ENNReal := ∑ i ∈ s', volume (V' i).shade
  let B' : ENNReal := ∑ i ∈ s', volume (V' i).carrier
  have hcar : ∀ i ∈ s', (V' i).carrier = (V i).carrier := by
    intro i hi
    exact congrArg ConvexSpaceBody.carrier (href i hi).1
  have hBmass : (∑ i ∈ s', volume (V i).carrier) ≤ ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_le_sum_of_subset hs's
  have hB'le : B' ≤ B := by
    calc
      B' = ∑ i ∈ s', volume (V i).carrier := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact congrArg volume (hcar i hi)
      _ ≤ B := by
        simpa [B] using hBmass
  have hAmass : (c : ENNReal) * A ≤ A' := by
    simpa [A, A'] using hmass
  have hB0' : B ≠ 0 := by simpa [B] using hB0
  have hBtop' : B ≠ ⊤ := by simpa [B] using hBtop
  have hfull : (c : ENNReal) * ShadedBody.fullness' s V ≤ ShadedBody.fullness' s' V' := by
    calc
      (c : ENNReal) * ShadedBody.fullness' s V = (c : ENNReal) * (A / B) := by rfl
      _ = ((c : ENNReal) * A) / B := by rw [← mul_div_assoc]
      _ ≤ A' / B := ENNReal.div_le_div hAmass le_rfl
      _ ≤ A' / B' := ENNReal.div_le_div le_rfl hB'le
  have hfull_coe : (c : ℝ≥0) * ShadedBody.fullness s V ≤ ShadedBody.fullness s' V' := by
    exact ENNReal.coe_le_coe.mp (by
      calc
        (↑(c * ShadedBody.fullness s V) : ENNReal) =
            (c : ENNReal) * (ShadedBody.fullness s V : ENNReal) := by
          rw [ENNReal.coe_mul]
        _ = (c : ENNReal) * ShadedBody.fullness' s V := by
          rw [ShadedBody.coe_fullness s V]
        _ ≤ ShadedBody.fullness' s' V' := hfull
        _ = (ShadedBody.fullness s' V' : ENNReal) :=
          (ShadedBody.coe_fullness s' V').symm)
  exact hfull_coe

end Kakeya

end

end
