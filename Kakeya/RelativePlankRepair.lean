/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Factorization
public import Kakeya.DimensionThree.Volume
public import Kakeya.PartialEstimates
public import Kakeya.DimensionThree.Plank.PlankFactorizationEstimate
public import Kakeya.StickyKakeya.Constants

/-!
# The repaired persistent-plank Proposition 6.6(A)

`Kakeya/RelativePlankRefutation.lean` shows that
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` is false as stated, and that the
missing hypothesis is pairwise essential distinctness of the fine tubes.  This file shows the
repair is **sufficient**, not merely necessary: with that clause added the statement is provable,
and the proof is short.

The mathematical content is one observation about the regime `δ ≤ ρ ≤ a ≤ b ≤ 1`, in which the
plank widths sit *above* the coarse scale:

> **In this regime the plank factorisation carries no aspect-ratio information beyond its own
> constant.**  If all inner tubes of a block lie in one `ρ`-tube `R`, then the same total inner
> mass `S` is read against `|R|` by `Kakeya.maxDensity` and against `|outerBody j|` by
> `Kakeya.PersistentPlankFactorization.maxDensity_le_mul`, and `S` cancels:
> `|outerBody j| ≤ C₀ · |R|` (`Kakeya.volume_outerBody_le_of_persistentPlankFactorization`).
> Since `|outerBody j| = 8ab` and `|R| ≤ 16 ρ² ≤ 16 a²`, this is `b ≤ 2 C₀ a`
> (`Kakeya.aspectRatio_le_of_persistentPlankFactorization`).

So `(a/b) ^ (3β/2) ≥ (2 C₀) ^ (-3β/2)`, and with `C₀ ≤ δ ^ (-η)` the whole claimed plank gain is a
`δ ^ (-ε)`-absorbable loss.  The repaired proposition therefore reduces, with no plank machinery at
all, to the canonical Frostman multiplicity estimate
`Kakeya.FrostmanEstimate.multiplicity_bound_of_mem` — which is exactly the estimate that needs the
essential-distinctness clause.

This is the mirror image of `Kakeya.b_le_two_mul_of_comparableBodyFactorization`
(`Kakeya/DimensionThree/Plank/…`), which derives `b ≤ 2ρ` in the *opposite* regime `b ≤ ρ`; there
the outer bodies are hulls of the inner family, here they are free data and the bound comes from
the density clause instead.  Neither statement implies the other, and neither regime's proof
transfers, exactly as the target's docstring warns.

This file sits *below* `Kakeya/RelativePlank.lean` in the import order, because
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` is now closed by
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation_of_essDistinct`.  The non-vacuity
certificate for the repaired hypothesis bundle needs the counterexample configuration and so lives
at the end of `Kakeya/RelativePlankRefutation.lean`, as
`Kakeya.persistentPlank_hypotheses_satisfiable`.
-/

@[expose] public section

open MeasureTheory Metric Kakeya Convexity ConvexSpaceBody
open scoped NNReal ENNReal Topology
noncomputable section

universe v

namespace Kakeya

/-- **The outer plank of a persistent factorisation is no bigger than the coarse tube.**

If every inner body of `F` lies in one `ρ`-tube `R`, then the density clause
`PersistentPlankFactorization.maxDensity_le_mul` forces `|outerBody j| ≤ C₀ · |R|` for every used
parent `j`: the same total inner mass `S` is read against `|R|` on one side and against
`|outerBody j|` on the other, and `S` cancels. -/
theorem volume_outerBody_le_of_persistentPlankFactorization
    {ι : Type*} {ρ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {C₀ : ℝ≥0}
    {F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι)}
    (hF : PersistentPlankFactorization F a b hab hb1 C₀)
    (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hin : ∀ i ∈ F.innerSet, F.innerBody i ≤ R.toConvexSpaceBody)
    (hS0 : (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) ≠ 0)
    (hSt : (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) ≠ ⊤)
    (hR0 : volume R.carrier ≠ 0) (hRt : volume R.carrier ≠ ⊤)
    {j : Finset ι} (hj : ∃ i ∈ F.innerSet, F.parent i = j)
    (hP0 : volume (F.outerBody j).carrier ≠ 0)
    (hPt : volume (F.outerBody j).carrier ≠ ⊤) :
    volume (F.outerBody j).carrier ≤ (C₀ : ENNReal) * volume R.carrier := by
  letI : DecidableEq (Finset ι) := fun x y => Classical.propDecidable (x = y)
  set S : ENNReal := ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier with hSdef
  -- lower bound on the maximal density, read on the coarse tube
  have hlow : S / volume R.carrier ≤ maxDensity F.innerSet F.innerBody := by
    refine le_trans ?_ (le_maxDensity F.innerSet F.innerBody R.toConvexSpaceBody)
    rw [densityIn_of_all_le hin]
  -- upper bound on the density inside the outer plank
  have hupp : densityIn (F.fiber j) F.innerBody (F.outerBody j)
      ≤ S / volume (F.outerBody j).carrier := by
    refine ENNReal.div_le_div_right ?_ _
    have hfs : F.fiber j ⊆ F.innerSet := by
      intro i hi
      exact (Finset.mem_filter.mp hi).1
    refine Finset.sum_le_sum_of_subset ?_
    exact (Finset.filter_subset _ _).trans hfs
  have hchain : S / volume R.carrier
      ≤ (C₀ : ENNReal) * (S / volume (F.outerBody j).carrier) :=
    hlow.trans ((hF.maxDensity_le_mul j (Finset.mem_image.mpr hj)).trans (by gcongr))
  rw [← mul_div_assoc] at hchain
  set X : ENNReal := volume R.carrier with hXdef
  set Y : ENNReal := volume (F.outerBody j).carrier with hYdef
  have hXY : (S / X) * (X * Y) = S * Y := by
    rw [← mul_assoc, ENNReal.div_mul_cancel hR0 hRt]
  have hXY2 : ((C₀ : ENNReal) * S / Y) * (X * Y) = (C₀ : ENNReal) * S * X := by
    rw [mul_comm X Y, ← mul_assoc, ENNReal.div_mul_cancel hP0 hPt]
  have h1 : S * Y ≤ (C₀ : ENNReal) * S * X := by
    rw [← hXY, ← hXY2]
    exact mul_le_mul_right' hchain _
  have h2 : Y * S ≤ ((C₀ : ENNReal) * X) * S := by
    calc Y * S = S * Y := mul_comm _ _
      _ ≤ (C₀ : ENNReal) * S * X := h1
      _ = ((C₀ : ENNReal) * X) * S := by ring
  exact (ENNReal.mul_le_mul_iff_left hS0 hSt).mp h2

/-- **The aspect-ratio bound in the regime `ρ ≤ a`** (the persistent-plank form of
`Kakeya.b_le_two_mul_of_comparableBodyFactorization`, which lives in the opposite regime).

When the inner tubes of a block all lie in one `ρ`-tube with `ρ ≤ a`, the density clause of
`Kakeya.PersistentPlankFactorization` caps the aspect ratio: `b ≤ 2 · C₀ · a`.  So the gain factor
`(a/b) ^ (3β/2)` of GWZ Proposition 6.6(A) is at least `(2 C₀) ^ (-3β/2)` — a loss of the size of
the factorisation constant, and nothing more. -/
theorem aspectRatio_le_of_persistentPlankFactorization
    {ι : Type*} {ρ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {C₀ : ℝ≥0}
    {F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι)}
    (hF : PersistentPlankFactorization F a b hab hb1 C₀)
    (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hin : ∀ i ∈ F.innerSet, F.innerBody i ≤ R.toConvexSpaceBody)
    (hS0 : (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) ≠ 0)
    (hSt : (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) ≠ ⊤)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρa : ρ ≤ a)
    {j : Finset ι} (hj : ∃ i ∈ F.innerSet, F.parent i = j) :
    b ≤ 2 * C₀ * a := by
  letI : DecidableEq (Finset ι) := fun x y => Classical.propDecidable (x = y)
  have ha0 : 0 < a := lt_of_lt_of_le hρ0 hρa
  obtain ⟨Q, hQ⟩ := hF.outer_are_planks j (Finset.mem_image.mpr hj)
  have hvolQ : volume (F.outerBody j).carrier = ((8 * a * b : ℝ≥0) : ENNReal) := by
    rw [hQ]
    change volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) = _
    rw [Prism3D.volume_carrier]
    push_cast
    ring
  have hP0 : volume (F.outerBody j).carrier ≠ 0 := by
    rw [hvolQ]
    refine ENNReal.coe_ne_zero.mpr ?_
    have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
    positivity
  have hPt : volume (F.outerBody j).carrier ≠ ⊤ := by rw [hvolQ]; exact ENNReal.coe_ne_top
  have hR0 : volume R.carrier ≠ 0 := by
    have h := Tube.le_volume R
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp] at h
    refine ne_of_gt (lt_of_lt_of_le ?_ h)
    exact pos_iff_ne_zero.mpr (mul_ne_zero
      (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne')
      (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hρ0.ne')))
  have hRt : volume R.carrier ≠ ⊤ := R.isCompact'.measure_ne_top
  have hmain := volume_outerBody_le_of_persistentPlankFactorization hF R hin hS0 hSt hR0 hRt
    hj hP0 hPt
  have hRle : volume R.carrier ≤ ((16 * ρ * ρ : ℝ≥0) : ENNReal) := by
    have h := Tube.volume_le_of_le hρ1 R
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp] at h
    refine h.trans ?_
    refine ENNReal.coe_le_coe.mpr ?_
    calc (2:ℝ≥0) ^ 3 * (1 + 1) * ρ ^ (3 - 1) = 16 * ρ * ρ := by ring
      _ ≤ 16 * ρ * ρ := le_rfl
  have hnn : (8 * a * b : ℝ≥0) ≤ 16 * C₀ * a * a := by
    have h : ((8 * a * b : ℝ≥0) : ENNReal) ≤ ((16 * C₀ * a * a : ℝ≥0) : ENNReal) := by
      calc ((8 * a * b : ℝ≥0) : ENNReal) = volume (F.outerBody j).carrier := hvolQ.symm
        _ ≤ (C₀ : ENNReal) * volume R.carrier := hmain
        _ ≤ (C₀ : ENNReal) * ((16 * ρ * ρ : ℝ≥0) : ENNReal) := by gcongr
        _ ≤ (C₀ : ENNReal) * ((16 * a * a : ℝ≥0) : ENNReal) := by
              refine mul_le_mul_left' (ENNReal.coe_le_coe.mpr ?_) _
              exact mul_le_mul' (mul_le_mul' (le_refl (16:ℝ≥0)) hρa) hρa
        _ = ((16 * C₀ * a * a : ℝ≥0) : ENNReal) := by
              rw [← ENNReal.coe_mul]; congr 1; ring
    exact_mod_cast h
  have h8a : (0:ℝ≥0) < 8 * a := by positivity
  have hfinal : (8 * a) * b ≤ (8 * a) * (2 * C₀ * a) := by
    calc (8 * a) * b = 8 * a * b := by ring
      _ ≤ 16 * C₀ * a * a := hnn
      _ = (8 * a) * (2 * C₀ * a) := by ring
  exact le_of_mul_le_mul_left hfinal h8a

/-! ### The absorption arithmetic -/

/-- **The plank gain in the regime `ρ ≤ a` is an absorbable loss.**

If `b ≤ C * a` then `(a/b) ^ (3β/2) ≥ C ^ (-3β/2)`, so any `δ`-budget that swallows `C ^ (3β/2)`
also swallows the entire gain factor of GWZ Proposition 6.6(A). -/
theorem plankGain_absorb {β ε : ℝ} (hβ : 0 < β) {δ a b C : ℝ≥0}
    (hδ0 : 0 < δ) (ha0 : 0 < a) (hab : a ≤ b) (hC1 : 1 ≤ C) (hb : b ≤ C * a)
    (hCthr : ((C : ENNReal)) ^ (3 * β / 2) ≤ (δ : ENNReal) ^ (-(ε/2))) :
    (δ : ENNReal) ^ (-(ε/2))
      ≤ (δ : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) := by
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hCE0 : (C : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hC1).ne'
  have hCEt : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hbE0 : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0.ne'
  have hbEt : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hexp : (0:ℝ) ≤ 3 * β / 2 := by positivity
  -- the aspect ratio is at least `C⁻¹`
  have hratio : (C : ENNReal)⁻¹ ≤ (a : ENNReal) / (b : ENNReal) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hbE0) (Or.inl hbEt)]
    calc (C : ENNReal)⁻¹ * (b : ENNReal) ≤ (C : ENNReal)⁻¹ * ((C : ENNReal) * (a : ENNReal)) := by
          gcongr
          exact_mod_cast hb
      _ = (a : ENNReal) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hCE0 hCEt, one_mul]
  have hpow : (δ : ENNReal) ^ (ε/2) ≤ ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) := by
    refine le_trans ?_ (ENNReal.rpow_le_rpow hratio hexp)
    rw [ENNReal.inv_rpow]
    refine le_trans ?_ (ENNReal.inv_le_inv.mpr hCthr)
    rw [← ENNReal.rpow_neg]
    exact le_of_eq (by norm_num)
  calc (δ : ENNReal) ^ (-(ε/2)) = (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (ε/2) := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hδ0.ne') ENNReal.coe_ne_top]
        congr 1
        ring
    _ ≤ (δ : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) := by gcongr

/-- **The factorisation constant fits inside a quarter of the loss budget.**

With `C₀ ≤ δ ^ (-η)`, `η ≤ ε / (6β)` and `4 ≤ δ ^ (-ε/4)`, the constant `(2 C₀) ^ (3β/2)` that
`Kakeya.plankGain_absorb` has to swallow is at most `δ ^ (-ε/2)`. -/
theorem twoMul_rpow_le_of_le_rpow_neg {β ε η : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {δ C₀ : ℝ≥0}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hC₀ : C₀ ≤ δ ^ (-η)) (hη : η * (3 * β / 2) ≤ ε / 4)
    (hthr : (4:ℝ≥0) ≤ δ ^ (-(ε/4))) :
    (((2 * C₀ : ℝ≥0)) : ENNReal) ^ (3 * β / 2) ≤ (δ : ENNReal) ^ (-(ε/2)) := by
  have hexp : (0:ℝ) ≤ 3 * β / 2 := by positivity
  have hnn : ((2 * C₀ : ℝ≥0)) ^ (3 * β / 2) ≤ δ ^ (-(ε/2)) := by
    have h1 : (2 * C₀ : ℝ≥0) ≤ 2 * δ ^ (-η) := by gcongr
    have h2 : ((2 * C₀ : ℝ≥0)) ^ (3 * β / 2) ≤ (2 * δ ^ (-η)) ^ (3 * β / 2) :=
      NNReal.rpow_le_rpow h1 hexp
    have h3 : ((2 : ℝ≥0) * δ ^ (-η)) ^ (3 * β / 2)
        = (2:ℝ≥0) ^ (3 * β / 2) * δ ^ (-η * (3 * β / 2)) := by
      rw [NNReal.mul_rpow, ← NNReal.rpow_mul]
    have h5 : ((2:ℝ≥0)) ^ (3 * β / 2) ≤ 4 := by
      have : ((2:ℝ≥0)) ^ (3 * β / 2) ≤ ((2:ℝ≥0)) ^ ((2:ℕ) : ℝ) :=
        NNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      rw [NNReal.rpow_natCast] at this
      norm_num at this
      exact this
    have h6 : δ ^ (-η * (3 * β / 2)) ≤ δ ^ (-(ε/4)) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
    calc ((2 * C₀ : ℝ≥0)) ^ (3 * β / 2) ≤ (2 * δ ^ (-η)) ^ (3 * β / 2) := h2
      _ = (2:ℝ≥0) ^ (3 * β / 2) * δ ^ (-η * (3 * β / 2)) := h3
      _ ≤ 4 * δ ^ (-(ε/4)) := by gcongr
      _ ≤ δ ^ (-(ε/4)) * δ ^ (-(ε/4)) := by gcongr
      _ = δ ^ (-(ε/2)) := by rw [← NNReal.rpow_add hδ0.ne']; congr 1; ring
  have hcoe1 : (((2 * C₀ : ℝ≥0)) : ENNReal) ^ (3 * β / 2)
      = (((2 * C₀ : ℝ≥0) ^ (3 * β / 2) : ℝ≥0) : ENNReal) := by
    rcases eq_or_ne (2 * C₀ : ℝ≥0) 0 with h | h
    · rw [h]
      rw [ENNReal.coe_zero, ENNReal.zero_rpow_of_pos (by positivity),
        NNReal.zero_rpow (by positivity)]
      simp
    · rw [ENNReal.coe_rpow_of_ne_zero h]
  have hcoe2 : (δ : ENNReal) ^ (-(ε/2)) = ((δ ^ (-(ε/2)) : ℝ≥0) : ENNReal) :=
    (ENNReal.coe_rpow_of_ne_zero hδ0.ne' _).symm
  rw [hcoe1, hcoe2]
  exact_mod_cast hnn


/-! ### The repaired proposition -/

open Classical in
/-- **GWZ Proposition 6.6(A), persistent-plank form, in the regime `δ ≤ ρ ≤ a ≤ b ≤ 1` — repaired
and proved.**

This is `Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` with the one missing clause
restored: the fine tubes are pairwise essentially distinct.  Without it the statement is false
(`Kakeya.PersistPlankCE.not_payload`); with it, the proof is three steps and no plank machinery:

1. `Kakeya.aspectRatio_le_of_persistentPlankFactorization` gives `b ≤ 2 C₀ a` — in this regime the
   factorisation carries no aspect-ratio information beyond its own constant;
2. `Kakeya.twoMul_rpow_le_of_le_rpow_neg` and `Kakeya.plankGain_absorb` turn that into
   `δ ^ (-ε/2) ≤ δ ^ (-ε) · (a/b) ^ (3β/2)`, i.e. the claimed gain is a `δ ^ (-ε)`-absorbable loss;
3. `Kakeya.FrostmanEstimate.multiplicity_bound_of_mem` at `ε/2` supplies the rest.

Two hypotheses of the original are **not needed** and have been dropped, which strengthens the
statement: the Katz--Tao estimate `K_KT(β)`, and the two-sided shaded uniformity
`ShadedTube.ShadedUniformTubeSet`.  Only `K_F(β)`, the ball and fullness clauses, the scale chain,
the parent containment and the factorisation are used.

The threshold is explicit in the ingredients: `η = min η₁ (ε / (6β))` with `η₁` from the Frostman
multiplicity estimate at `ε/2`, and `δ₀ = min (min δ₁ δ₂) (1/2)` with `δ₁` its scale threshold and
`δ₂` the threshold making `4 ≤ δ ^ (-ε/4)`. -/
theorem tubeMultiplicityOfLocalPersistentPlankFactorisation_of_essDistinct {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι : Type v} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
          {κ : Type} (r : Finset κ)
          (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ),
          δ ≤ ρ → ρ ≤ a →
          (∀ i ∈ q, assign i ∈ r ∧
            (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
          ∀ (C₀ : ℝ≥0), C₀ ≤ δ ^ (-η) →
            ∀ (F : κ → ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι)),
              (∀ k ∈ r, (F k).innerSet = {i ∈ q | assign i = k}) →
              (∀ k ∈ r, (F k).innerBody = fun i => (T i).toConvexSpaceBody) →
              (∀ k ∈ r, PersistentPlankFactorization (F k) a b hab hb1 C₀) →
          ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
            IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall CF →
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
              (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
                * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
                * (δ : ENNReal) ^ (-2 * β)
                * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2) := by
  intro ε hε
  obtain ⟨η₁, hη₁, hev⟩ :=
    FrostmanEstimate.multiplicity_bound_of_mem (E := EuclideanSpace ℝ (Fin 3))
      hβpos.le hβle (by simp) hKF (ε/2) (by positivity)
  obtain ⟨δ₁, hδ₁pos, hbase⟩ := StickyKakeya.exists_threshold_of_eventually_nhdsGT hev
  obtain ⟨δ₂, hδ₂pos, hthr4⟩ :=
    exists_threshold_le_rpow_neg 4 (by norm_num) (show (0:ℝ) < ε/4 by positivity)
  refine ⟨min η₁ (ε/(6*β)), lt_min hη₁ (by positivity),
    min (min δ₁ δ₂) (1/2), lt_min (lt_min hδ₁pos hδ₂pos) (by norm_num), ?_⟩
  intro ι q δ hδ0 T hδδ₀ hball hED hfull ρ a b hab hb1 κ r R assign hδρ hρa hassign
    C₀ hC₀ F hFinner hFbody hFz CF hCF1 hCFtop hFrost
  set η : ℝ := min η₁ (ε/(6*β)) with hηdef
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  have hηε : η ≤ ε/(6*β) := min_le_right _ _
  have hδhalf : δ ≤ 1/2 := hδδ₀.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδhalf.trans (by norm_num)
  have hδδ₁ : δ ≤ δ₁ := hδδ₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδδ₂ : δ ≤ δ₂ := hδδ₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  -- the plank-free multiplicity estimate
  have hfull₁ : ShadedBody.fullness q (fun i => (T i).toShadedBody) ≥ δ ^ η₁ :=
    le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hηη₁) hfull
  have hbaseq := hbase hδ0 hδδ₁ q T hball hED hfull₁
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp] at hbaseq
  -- pass to `CF`
  have hfrost : ConvexSpaceBody.frostmanConstant q (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ CF :=
    ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn hFrost
  have hexp : (0:ℝ) ≤ 1 - β / 2 := by linarith
  have hbase' : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      (δ : ENNReal) ^ (-(ε/2)) * CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β)
        * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2) := by
    refine hbaseq.trans ?_
    have h1 : ((q.card : ENNReal) * (δ : ENNReal) ^ (3 - 1))
        = ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) := by norm_num; ring
    rw [h1]
    gcongr
  -- the aspect ratio bound
  rcases q.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  have ha0 : 0 < a := lt_of_lt_of_le hρ0 hρa
  have hρ1 : ρ ≤ 1 := hρa.trans (hab.trans hb1)
  set k : κ := assign i₀ with hkdef
  have hk : k ∈ r := (hassign i₀ hi₀).1
  have hinner : (F k).innerSet = {i ∈ q | assign i = k} := hFinner k hk
  have hbody : (F k).innerBody = fun i => (T i).toConvexSpaceBody := hFbody k hk
  have hi₀' : i₀ ∈ (F k).innerSet := by
    rw [hinner]
    exact Finset.mem_filter.mpr ⟨hi₀, rfl⟩
  have hin : ∀ i ∈ (F k).innerSet, (F k).innerBody i ≤ (R k).toConvexSpaceBody := by
    intro i hi
    rw [hinner] at hi
    obtain ⟨hiq, hik⟩ := Finset.mem_filter.mp hi
    rw [hbody]
    have := (hassign i hiq).2
    rwa [hik] at this
  have hvol0 : ∀ i ∈ (F k).innerSet, 0 < volume ((F k).innerBody i).carrier := by
    intro i hi
    rw [hbody]
    refine lt_of_lt_of_le ?_ (Tube.le_volume (T i).toTube)
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp]
    exact pos_iff_ne_zero.mpr (mul_ne_zero
      (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne')
      (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hδ0.ne')))
  have hS0 : (∑ i ∈ (F k).innerSet, volume ((F k).innerBody i).carrier) ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le (hvol0 i₀ hi₀') ?_)
    exact Finset.single_le_sum (f := fun i => volume ((F k).innerBody i).carrier)
      (fun _ _ => bot_le) hi₀'
  have hSt : (∑ i ∈ (F k).innerSet, volume ((F k).innerBody i).carrier) ≠ ⊤ := by
    refine (ENNReal.sum_lt_top.mpr ?_).ne
    intro i _
    exact ((F k).innerBody i).isCompact'.measure_lt_top
  have hbC : b ≤ 2 * C₀ * a :=
    aspectRatio_le_of_persistentPlankFactorization (hFz k hk) (R k) hin hS0 hSt hρ0 hρ1 hρa
      ⟨i₀, hi₀', rfl⟩
  have hC1 : (1:ℝ≥0) ≤ 2 * C₀ := by
    by_contra hcon
    push_neg at hcon
    have : b < a := by
      calc b ≤ 2 * C₀ * a := hbC
        _ < 1 * a := by exact mul_lt_mul_of_pos_right hcon ha0
        _ = a := one_mul a
    exact absurd hab (not_le.mpr this)
  have hCthr : (((2 * C₀ : ℝ≥0)) : ENNReal) ^ (3 * β / 2) ≤ (δ : ENNReal) ^ (-(ε/2)) := by
    refine twoMul_rpow_le_of_le_rpow_neg hβpos hβle hδ0 hδ1 hC₀ ?_ (hthr4 δ hδ0 hδδ₂)
    have h6β : 0 < 6 * β := by linarith
    calc η * (3 * β / 2) ≤ (ε/(6*β)) * (3 * β / 2) := by
          refine mul_le_mul_of_nonneg_right hηε (by positivity)
      _ = ε / 4 := by field_simp; ring
  have habs := plankGain_absorb (β := β) (ε := ε) hβpos hδ0 ha0 hab hC1 hbC hCthr
  refine hbase'.trans ?_
  calc (δ : ENNReal) ^ (-(ε/2)) * CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β)
        * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2)
      ≤ ((δ : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2))
        * CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β)
        * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2) := by gcongr
    _ = (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
        * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β)
        * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2) := by ring

end Kakeya

