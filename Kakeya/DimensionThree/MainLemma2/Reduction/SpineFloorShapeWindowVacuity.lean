/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeHwinfloor

/-!
# `hwinfloor`'s conjunct 1: the width-one degeneracy, and the clause that blocks it

 left conjunct 1 of `hwinfloor` open, with four findings called
evidence rather than a refutation.  This file measures the remaining possibility — that the
existential `∃ a b m` could be satisfied *degenerately* — and the answer is **no, but only just**.

## At a width-one window, two of the three content-bearing clauses are empty

`hwinfloor` is `∃ a b m, IsKatzTaoDividingWindowLevels … a b m ∧ FloorHypothesisAt … a b m`.  At
`b = a + 1`:

* `IsKatzTaoDividingWindowLevels.le_level_maxDensity` quantifies over the `ε_d`-inset range
  `a + ⌈ε_d (b − a)⌉ ≤ c ≤ b − ⌈ε_d (b − a)⌉`, which is **empty** for `ε_d > 0`
  (`Kakeya.ML2Core.no_inset_level_of_succ`) — so the multiplicity-free level clause, the one
  `Kakeya.ML2Core.not_levelClause_gridModel` shows is *not* a formality, says nothing;
* `Kakeya.ML2Core.FloorHypothesisAt`'s third clause — **the count floor**, source l.4076–4079, the
  statement  is about — quantifies over `a < m' < b`, also **empty**.

`Kakeya.ML2Core.floorHypothesisAt_succ_of_parentAdmissible`,
`Kakeya.ML2Core.isKatzTaoDividingWindowLevels_succ` and `Kakeya.ML2Core.hwinfloor_succ` compile that:
at width one the whole row follows from the *parent* window, the two-level band and
`ParentAdmissible 𝒰 η' a a`.

## …and the parent window forbids width one, so this is a **near miss, not a false pass**

`Kakeya.ML2Core.IsKatzTaoDividingWindow.mul_ssfGridLen_le_sub`: the parent's `scale_sep`
(`ρ_b ≤ δ^{ε_d} ρ_a`, with `Tube.gridScale δ L k = δ^{k/L}`) is exactly

```
    ε_d · ssfGridLen δ + a ≤ b,
```

and `Tube.ssfGridLen δ = ⌈log log (1/δ)⌉₊` grows without bound.  So `hwinfloor_succ`'s hypothesis
`hpar` is **eventually unsatisfiable**, the width-one window is unreachable in the filter's regime,
and conjunct 1 is *not* vacuously deliverable.

**Verdict, stated as a verdict.**  Unlike `IsFillSeparationCertificate`, `FloorPayload`'s
`S = ∅`  and `FloorDataAt`'s unconditional `(F)` (`RR3`), this one is **not** a defect: the
tree is protected, and the clause that protects it is `scale_sep` — nothing in `FloorHypothesisAt`
and nothing in the level clause.  Both halves are here so that the next hand does not
re-open the question, and so that anyone who ever weakens `scale_sep` sees what it was holding.

**One residual, measured but not :** the inset range is nonempty only when
`b − a ≥ 2⌈ε_d (b − a)⌉₊`, which needs `ε_d < 1/2`.  The width bound gives `b − a ≥ ε_d · ssfGridLen δ`,
so this holds for small `δ` **provided `ML2Spine.spineDiv ϖ ε₁ < 1/2`**; that inequality is a
parameter fact I have not checked and it belongs to whoever fixes `ϖ`, `ε₁`.
-/

@[expose] public section

open MeasureTheory Metric Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Degenerate

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}

/-- **The `ε_d`-inset range of a width-one window is empty.**  It asks
`a + k ≤ c` and `c + k ≤ a + 1` with `k = ⌈ε_d · 1⌉₊ ≥ 1`, hence `2k ≤ 1`. -/
theorem no_inset_level_of_succ {εd : ℝ} (hεd : 0 < εd) (a c : ℕ)
    (h1 : a + ⌈εd * (((a + 1 : ℕ) : ℝ) - (a : ℝ))⌉₊ ≤ c)
    (h2 : c + ⌈εd * (((a + 1 : ℕ) : ℝ) - (a : ℝ))⌉₊ ≤ a + 1) : False := by
  have hone : (((a + 1 : ℕ) : ℝ) - (a : ℝ)) = 1 := by push_cast; ring
  rw [hone, mul_one] at h1 h2
  have hk : 1 ≤ ⌈εd⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    simpa using (Nat.ceil_eq_zero.not.mpr (not_le.mpr hεd)))
  omega

variable {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The count floor is vacuous at a width-one window.**  `FloorHypothesisAt`'s first clause is
free at `p := a` (`Kakeya.ML2Core.floorHypothesisAt_of_countFloor`), its second clause is
`ParentAdmissible 𝒰 η' a a`, and its third quantifies over the empty range `a < m' < a + 1`. -/
theorem floorHypothesisAt_succ_of_parentAdmissible {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu) (a m : ℕ)
    (hpar : ParentAdmissible 𝒰 η' a a) :
    FloorHypothesisAt β ϖ ε₁ gain dens η' 𝒰 a (a + 1) m :=
  floorHypothesisAt_of_countFloor 𝒰 a (a + 1) m hpar
    (fun _ _ _ _ m' h1 h2 _ _ _ => absurd h2 (by omega))

variable {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **The level clause is vacuous at a width-one window**, so the twin costs no more than its
parent plus the two-level band. -/
theorem isKatzTaoDividingWindowLevels_succ
    {𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu}
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} (hεd : 0 < εd) {N a m : ℕ}
    (hpar : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar η εd N a (a + 1) m)
    (hband : ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
      ∀ j ∈ 𝒰.cover.indexSet p,
      Φ p c ≤ Kakeya.maxDensity
          ((Tube.coverClass u (𝒰.cover.assign p) j).image (𝒰.cover.assign c))
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity
          ((Tube.coverClass u (𝒰.cover.assign p) j).image (𝒰.cover.assign c))
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c) :
    ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a (a + 1) m where
  toIsKatzTaoDividingWindow := hpar
  le_level_maxDensity := fun c h1 h2 _ _ => absurd (no_inset_level_of_succ hεd a c h1 h2) not_false
  level_density_band := hband

open scoped Classical in
/-- **`hwinfloor`, delivered at a width-one window.**  Exactly the shape
`Kakeya.ML2Core.hfloor_of_producers` asks for, from the *parent* window, the two-level band and
`ParentAdmissible` alone — with the multiplicity-free level clause and the count floor both empty.

This is the false pass, assembled.  It is **not** used anywhere; it is the form of the
finding that `hwinfloor`'s existential over `(a, b, m)` admits a window at which the two clauses
carrying the source's content say nothing. -/
theorem hwinfloor_succ {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ}
    (𝒱 : Tube.UniformTubeSet u (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (hdiv : 0 < ML2Spine.spineDiv ϖ ε₁) (a m : ℕ)
    (hpar : ML2Reduction.IsKatzTaoDividingWindow 𝒱
      ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
      (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a (a + 1) m)
    (hband : ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
      ∀ j ∈ 𝒱.cover.indexSet p,
      Φ p c ≤ Kakeya.maxDensity
          ((Tube.coverClass u (𝒱.cover.assign p) j).image (𝒱.cover.assign c))
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity
          ((Tube.coverClass u (𝒱.cover.assign p) j).image (𝒱.cover.assign c))
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody)
          ≤ ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) * Φ p c)
    (hadm : ParentAdmissible 𝒱 η' a a) :
    ∃ a b m : ℕ,
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒱
        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m ∧
      FloorHypothesisAt β ϖ ε₁ gain dens η' 𝒱 a b m :=
  ⟨a, a + 1, m, isKatzTaoDividingWindowLevels_succ hdiv hpar hband,
    floorHypothesisAt_succ_of_parentAdmissible 𝒱 a m hadm⟩

end Degenerate

/-! ### …and why the degeneracy is nevertheless unreachable: the window is forced wide -/

section Width

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The parent window's scale separation forces a width of `ε_d · ssfGridLen δ` levels.**

`Kakeya.ML2Reduction.IsKatzTaoDividingWindow.scale_sep` is
`ρ_b ≤ δ^{ε_d} ρ_a`, and `Tube.gridScale δ L k = δ^{k/L}`, so it reads `b/L ≥ ε_d + a/L`, i.e.

```
    ε_d · ssfGridLen δ + a ≤ b.
```

Since `Tube.ssfGridLen δ = ⌈log log (1/δ)⌉₊` grows without bound, **the width-one window of this
section is unreachable at small `δ`**: `hwinfloor_succ`'s hypothesis `hpar` is eventually
unsatisfiable.  So the vacuity above is a *near miss*, not a live false pass, and the clause that
blocks it is `scale_sep` — nothing in `FloorHypothesisAt`, and nothing in the level clause.

That is the honest verdict on the conjunct 1: it is **not** vacuously deliverable, and the two
content-bearing clauses do have content at every window the parent admits. -/
theorem IsKatzTaoDividingWindow.mul_ssfGridLen_le_sub (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu}
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ}
    (hw : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar η εd N a b m) :
    εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ) ≤ (b : ℝ) := by
  have hab : a < b := hw.coarse_lt_fine
  have hbL : b ≤ Tube.ssfGridLen δ := hw.fine_le_gridLen
  have hLn : 0 < Tube.ssfGridLen δ := by omega
  have hL : 0 < (Tube.ssfGridLen δ : ℝ) := by exact_mod_cast hLn
  have hδr0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδr1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hsep := hw.scale_sep
  rw [Tube.gridScale, Tube.gridScale, NNReal.coe_rpow, NNReal.coe_rpow,
    ← Real.rpow_add hδr0] at hsep
  have hanti : StrictAnti (fun x : ℝ => (δ : ℝ) ^ x) :=
    Real.strictAnti_rpow_of_base_lt_one hδr0 hδr1
  have hmono : εd + (a : ℝ) / (Tube.ssfGridLen δ : ℝ) ≤ (b : ℝ) / (Tube.ssfGridLen δ : ℝ) :=
    (StrictAnti.le_iff_ge hanti).mp hsep
  have hmul := mul_le_mul_of_nonneg_right hmono hL.le
  rw [add_mul, div_mul_cancel₀ _ hL.ne', div_mul_cancel₀ _ hL.ne'] at hmul
  exact hmul

end Width
