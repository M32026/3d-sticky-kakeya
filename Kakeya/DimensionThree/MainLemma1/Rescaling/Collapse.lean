/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.DensityTransfer
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Thresholds

/-!
# Main Lemma 1, Case (ii): reduction to the `b`-tubes — the two factors and their collapse

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.

The fullness thresholds of this subsection live in
`Kakeya/DimensionThree/MainLemma1/Rescaling/Thresholds.lean`:
`Kakeya.ml1Boot.le_fullness_of_termwise`, `Kakeya.ml1Boot.coarse_fullness_threshold` and
`Kakeya.ml1Boot.fine_fullness_threshold`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

section ReduceToTb

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! #### The two factors and their collapse -/

/-- **Pulling a constant out of the exponent `1 - γ/2`** (blueprint
`lem:ml1bootConstantOutOfPower`).

For `c ≥ 1` and `γ ∈ [0, 1]`, `(c² x) ^ (1 - γ/2) ≤ c² x ^ (1 - γ/2)`: split the power and
use `(c²) ^ (1 - γ/2) ≤ c²`, valid because `c² ≥ 1` and `1 - γ/2 ≤ 1`.  It is applied with
`c = C_u` and `x = δ̃² M` inside `Kakeya.ml1Boot.reduceToTb_collapse`. -/
theorem sq_mul_rpow_le {c : NNReal} (hc : 1 ≤ c) (x : ENNReal) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ((c : ENNReal) ^ 2 * x) ^ (1 - γ / 2) ≤ (c : ENNReal) ^ 2 * x ^ (1 - γ / 2) := by
  have hγhalf : 0 ≤ 1 - γ / 2 := by nlinarith
  have hγhalf1 : 1 - γ / 2 ≤ (1 : ℝ) := by nlinarith
  have hc2 : (1 : ENNReal) ≤ (c : ENNReal) ^ 2 := by
    have hcE : (1 : ENNReal) ≤ (c : ENNReal) := by exact_mod_cast hc
    simpa using one_le_pow₀ hcE
  rw [ENNReal.mul_rpow_of_nonneg ((c : ENNReal) ^ 2) x hγhalf]
  gcongr
  simpa using ENNReal.rpow_le_rpow_of_exponent_le hc2 hγhalf1

/-- **Absorbing the prefactor of `Kakeya.ml1Boot.reduceToTb_collapse`** (blueprint
`lem:ml1bootReduceToTbPrefactor`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  The absorption inequality
`4 Cc C² C_u² (2 C_T) δ̃ ^ (-ap') ≤ δ̃ ^ (-5 ap')` — hypothesis (d) of
`Kakeya.ml1Boot.normalized_le_of_coarse` — says exactly that the fixed constant is at most
`δ̃ ^ (-4 ap')`, so multiplied by the `δ̃ ^ (6 ap')` that the three factored bounds carry it
drops below `δ̃ ^ (2 ap')`, hence below `δ̃ ^ (10 a / ε)` by `10 a / ε ≤ 2 ap'`.

## The free constants `Cc` and `C`

The factoring and normalization constants are carried as **parameters** `Cc, C ≥ 1` and not as
`Kakeya.ml1Boot.factorOneScale.C` and `Kakeya.ml1Boot.fineFactor.C`, because the dilate chain
needs the lemma at `Cc = Kakeya.ml1Boot.factorOneScaleUniformDilate.C` and
`C = Kakeya.ml1Boot.fineNormalizeDilate.C 2`.  Both occur on *both* sides here, so neither
direction of the substitution follows; see blueprint `note:ml1bootArithFreeConstant`. -/
theorem reduceToTb_prefactor {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {Cc C : NNReal} (_hCc : 1 ≤ Cc) (_hC : 1 ≤ C)
    {ε a ap' : ℝ} (_hε0 : 0 < ε) (_hap' : 0 < ap') (hlink : 10 * a / ε ≤ 2 * ap')
    {Cu : NNReal} (_hCu : 1 ≤ Cu)
    (habsorb : 4 * (Cc : ENNReal) * (C : ENNReal) ^ 2
        * (Cu : ENNReal) ^ 2 * (2 * (densityTransfer.C : ENNReal)) * (δt : ENNReal) ^ (-ap')
      ≤ (δt : ENNReal) ^ (-5 * ap')) :
    4 * (Cc : ENNReal) * (C : ENNReal) ^ 2 * (Cu : ENNReal) ^ 2
        * (2 * (densityTransfer.C : ENNReal)) * (δt : ENNReal) ^ (6 * ap')
      ≤ (δt : ENNReal) ^ (10 * a / ε) := by
  let K : ENNReal := 4 * (Cc : ENNReal) * (C : ENNReal) ^ 2
    * (Cu : ENNReal) ^ 2 * (2 * (densityTransfer.C : ENNReal))
  have hDt0 : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
  have hDtTop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hDt1 : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  have hDt0' : (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ ap' = 1 := by
    rw [← ENNReal.rpow_add (-ap') ap' hDt0 hDtTop]
    simp
  have hDt2 : (δt : ENNReal) ^ (-5 * ap') * (δt : ENNReal) ^ ap'
      = (δt : ENNReal) ^ (-4 * ap') := by
    rw [← ENNReal.rpow_add (-5 * ap') ap' hDt0 hDtTop]
    have hz : -5 * ap' + ap' = -4 * ap' := by ring
    rw [hz]
  have hK : K ≤ (δt : ENNReal) ^ (-4 * ap') := by
    calc
      K = K * ((δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ ap') := by
            rw [hDt0']
            simp
      _ = (K * (δt : ENNReal) ^ (-ap')) * (δt : ENNReal) ^ ap' := by ring
      _ ≤ (δt : ENNReal) ^ (-5 * ap') * (δt : ENNReal) ^ ap' := by
            exact mul_le_mul_left habsorb ((δt : ENNReal) ^ ap')
      _ = (δt : ENNReal) ^ (-4 * ap') := by rw [hDt2]
  calc
    K * (δt : ENNReal) ^ (6 * ap')
        ≤ (δt : ENNReal) ^ (-4 * ap') * (δt : ENNReal) ^ (6 * ap') := by
          exact mul_le_mul_left hK ((δt : ENNReal) ^ (6 * ap'))
    _ = (δt : ENNReal) ^ (2 * ap') := by
      rw [← ENNReal.rpow_add (-4 * ap') (6 * ap') hDt0 hDtTop]
      have hz : -4 * ap' + 6 * ap' = 2 * ap' := by ring
      rw [hz]
    _ ≤ (δt : ENNReal) ^ (10 * a / ε) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge hDt1 hlink

/-- **Collapsing the two factors of `Kakeya.ml1Boot.normalized_le_of_coarse`** (blueprint
`lem:ml1bootReduceToTbCollapse`).

Multiplying the factoring inequality (a) with the fine bound (b) and the coarse bound (c) and
applying `Kakeya.ml1Boot.tripleCollapse` at `A = δ̃ / b`, `B = b`, `D = 1` — so `A B D = δ̃`
and all three lie in `(0, 1]` by `δ̃ ≤ b ≤ 1` — with `P₃ = 1`, `M' = C_u² M` and
`F₁ = F₂ = F₃ = 1` collects the three brackets into one at the scale `δ̃`, with the prefactor
`4 C₁ C₂² (2 C_T) δ̃ ^ (6 ap')`, the exponent `-ap' - 3 ap' + 10 ap' = 6 ap'` being the total
power of `δ̃` carried by the three hypotheses.  `Kakeya.ml1Boot.sq_mul_rpow_le` then pulls
`C_u²` out of the last bracket and `Kakeya.ml1Boot.reduceToTb_prefactor`, whose hypothesis is
(d), bounds the prefactor by `δ̃ ^ (10 a / ε)`.

`X`, `X_c` and `X_f` are the multiplicity of `(𝕋̃, Ỹ)` and those of the coarse and fine
factors; `P₁`, `P₂` are the two cardinalities and `M` is `|u|`.

## The free constants `Cc` and `C`

As in `Kakeya.ml1Boot.reduceToTb_prefactor`, the factoring and normalization constants are
**parameters** `Cc, C ≥ 1`.  The dilate chain needs the lemma at
`Cc = Kakeya.ml1Boot.factorOneScaleUniformDilate.C` and
`C = Kakeya.ml1Boot.fineNormalizeDilate.C`, and that instance does not follow from the one at
the fixed constants: both occur in the *hypotheses* (a), (b) and (d), so a fine bound with the
larger prefactor is weaker and does not supply them (blueprint
`note:ml1bootArithFreeConstant`). -/
theorem reduceToTb_collapse {δt b : NNReal} (hδt0 : 0 < δt) (hδtb : δt ≤ b) (hb1 : b ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {Cc C : NNReal} (hCc : 1 ≤ Cc) (hC : 1 ≤ C)
    {ε a ap' : ℝ} (hε0 : 0 < ε) (hap' : 0 < ap') (hlink : 10 * a / ε ≤ 2 * ap')
    {Cu : NNReal} (hCu : 1 ≤ Cu)
    {X Xc Xf P₁ P₂ M : ENNReal} (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂) (hM : 1 ≤ M)
    (hPM : P₁ * P₂ ≤ (Cu : ENNReal) ^ 2 * M)
    -- (a)
    (hprod : X ≤ (Cc : ENNReal) * (δt : ENNReal) ^ (-ap') * Xc * Xf)
    -- (b)
    (hfine : Xf ≤ 4 * (C : ENNReal) ^ 2 * (2 * (densityTransfer.C : ENNReal))
        * (δt : ENNReal) ^ (-3 * ap')
        * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
        * (P₁ * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    -- (c)
    (hcoarse : Xc ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
        * (P₂ * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    -- (d)
    (habsorb : 4 * (Cc : ENNReal) * (C : ENNReal) ^ 2
        * (Cu : ENNReal) ^ 2 * (2 * (densityTransfer.C : ENNReal)) * (δt : ENNReal) ^ (-ap')
      ≤ (δt : ENNReal) ^ (-5 * ap')) :
    X ≤ (δt : ENNReal) ^ (10 * a / ε) * (δt : ENNReal) ^ (-2 * γ)
      * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hδtb1 : δt ≤ 1 := le_trans hδtb hb1
  have hb0 : 0 < b := lt_of_lt_of_le hδt0 hδtb
  have hδtne : (δt : NNReal) ≠ 0 := ne_of_gt hδt0
  have hbne : (b : NNReal) ≠ 0 := ne_of_gt hb0
  have hDt0 : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδtne
  have hDtTop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- A := δt/b, B := b, D := 1, all in (0,1]
  have hA0 : 0 < δt / b := div_pos hδt0 hb0
  have hA1 : δt / b ≤ 1 := div_le_one_of_le₀ hδtb (le_of_lt hb0)
  have hD0 : 0 < (1 : NNReal) := by norm_num
  have hD1 : (1 : NNReal) ≤ 1 := le_rfl
  have hABD : (δt / b) * b * 1 = δt := by
    rw [mul_one, div_mul_cancel₀ _ hbne]
  -- M' := Cu^2 * M ≥ 1
  have hCuE : (1 : ENNReal) ≤ (Cu : ENNReal) := by exact_mod_cast hCu
  have hCu2 : (1 : ENNReal) ≤ (Cu : ENNReal) ^ 2 := one_le_pow₀ hCuE
  have hM' : (1 : ENNReal) ≤ (Cu : ENNReal) ^ 2 * M := one_le_mul hCu2 hM
  -- uniformity + F's
  have hPM' : P₁ * P₂ * (1 : ENNReal) ≤ (Cu : ENNReal) ^ 2 * M := by simp [hPM]
  have hF : (1 : ENNReal) * (1 : ENNReal) * (1 : ENNReal) ≤ 1 := by simp
  -- δt exponents combine: -ap' + 10 ap' + (-3 ap') = 6 ap'
  have hδpow : (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ (10 * ap')
      * (δt : ENNReal) ^ (-3 * ap') = (δt : ENNReal) ^ (6 * ap') := by
    calc
      (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ (10 * ap') * (δt : ENNReal) ^ (-3 * ap')
          = (δt : ENNReal) ^ (-ap' + 10 * ap' + (-3 * ap')) := by
            rw [← ENNReal.rpow_add (-ap') (10 * ap') hDt0 hDtTop]
            rw [← ENNReal.rpow_add (-ap' + 10 * ap') (-3 * ap') hDt0 hDtTop]
      _ = (δt : ENNReal) ^ (6 * ap') := by congr; ring
  -- the constant E
  let E : ENNReal := 4 * (Cc : ENNReal) * (C : ENNReal) ^ 2
    * (2 * (densityTransfer.C : ENNReal)) * (δt : ENNReal) ^ (6 * ap')
  -- the triple-product bound, in the form consumed by tripleCollapse
  have hX : X ≤ E
      * (1 * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * (P₁ * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * (1 * (b : ENNReal) ^ (-2 * γ)
          * (P₂ * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * (1 * (1 : ENNReal) ^ (-2 * γ)
          * (1 * (1 : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
    calc
      X ≤ (Cc : ENNReal) * (δt : ENNReal) ^ (-ap') * Xc * Xf := hprod
      _ ≤ (Cc : ENNReal) * (δt : ENNReal) ^ (-ap')
          * Xc
          * (4 * (C : ENNReal) ^ 2 * (2 * (densityTransfer.C : ENNReal))
              * (δt : ENNReal) ^ (-3 * ap')
              * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
              * (P₁ * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
            gcongr
      _ ≤ (Cc : ENNReal) * (δt : ENNReal) ^ (-ap')
          * ((δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
              * (P₂ * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
          * (4 * (C : ENNReal) ^ 2 * (2 * (densityTransfer.C : ENNReal))
              * (δt : ENNReal) ^ (-3 * ap')
              * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
              * (P₁ * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
            gcongr
      _ = ((δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ (10 * ap') * (δt : ENNReal) ^ (-3 * ap'))
          * ((Cc : ENNReal) * (4 * (C : ENNReal) ^ 2
              * (2 * (densityTransfer.C : ENNReal))))
          * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * (P₁ * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (b : ENNReal) ^ (-2 * γ)
          * (P₂ * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ring
      _ = ((δt : ENNReal) ^ (6 * ap'))
          * ((Cc : ENNReal) * (4 * (C : ENNReal) ^ 2
              * (2 * (densityTransfer.C : ENNReal))))
          * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * (P₁ * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (b : ENNReal) ^ (-2 * γ)
          * (P₂ * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by rw [hδpow]
      _ = E
          * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * (P₁ * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (b : ENNReal) ^ (-2 * γ)
          * (P₂ * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ring
      _ = E
          * (1 * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
              * (P₁ * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
          * (1 * (b : ENNReal) ^ (-2 * γ)
              * (P₂ * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
          * (1 * (1 : ENNReal) ^ (-2 * γ)
              * (1 * (1 : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by simp; ring
  -- tripleCollapse with A = δt/b, B = b, D = 1, P₃ = 1, M' = Cu^2 * M, F = 1
  have htri : X ≤ E * (δt : ENNReal) ^ (-2 * γ)
      * (((Cu : ENNReal) ^ 2 * M) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    exact tripleCollapse (A := δt / b) (B := b) (D := 1)
      (E := E) (F₁ := (1 : ENNReal)) (F₂ := (1 : ENNReal)) (F₃ := (1 : ENNReal))
      (M := (Cu : ENNReal) ^ 2 * M)
      hA0 hA1 hb0 hb1 hD0 hD1 hABD hγ0 hγ1 hP₁ hP₂ (by simp : 1 ≤ (1 : ENNReal)) hM' hPM' hF
      hX
  -- pull Cu^2 out of the last bracket
  have hCu_out : (((Cu : ENNReal) ^ 2 * M) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ (Cu : ENNReal) ^ 2 * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    calc
      (((Cu : ENNReal) ^ 2 * M) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
          = ((Cu : ENNReal) ^ 2 * (M * (δt : ENNReal) ^ (2 : ℕ))) ^ (1 - γ / 2) := by
            congr 1; ring
      _ ≤ (Cu : ENNReal) ^ 2 * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) :=
            sq_mul_rpow_le (c := Cu) (x := M * (δt : ENNReal) ^ (2 : ℕ)) hCu hγ0 hγ1
  have htri' : X ≤ E * (δt : ENNReal) ^ (-2 * γ) * (Cu : ENNReal) ^ 2
      * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    calc
      X ≤ E * (δt : ENNReal) ^ (-2 * γ)
          * (((Cu : ENNReal) ^ 2 * M) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := htri
      _ ≤ E * (δt : ENNReal) ^ (-2 * γ)
          * ((Cu : ENNReal) ^ 2 * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
            gcongr
      _ = E * (δt : ENNReal) ^ (-2 * γ) * (Cu : ENNReal) ^ 2
          * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ring
  -- the prefactor absorb
  have hpref : 4 * (Cc : ENNReal) * (C : ENNReal) ^ 2
      * (Cu : ENNReal) ^ 2 * (2 * (densityTransfer.C : ENNReal)) * (δt : ENNReal) ^ (6 * ap')
      ≤ (δt : ENNReal) ^ (10 * a / ε) :=
    reduceToTb_prefactor hδt0 hδtb1 hCc hC hε0 hap' hlink hCu habsorb
  calc
    X ≤ E * (δt : ENNReal) ^ (-2 * γ) * (Cu : ENNReal) ^ 2
        * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := htri'
    _ = (4 * (Cc : ENNReal) * (C : ENNReal) ^ 2 * (Cu : ENNReal) ^ 2
            * (2 * (densityTransfer.C : ENNReal)) * (δt : ENNReal) ^ (6 * ap'))
          * ((δt : ENNReal) ^ (-2 * γ) * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
          simp [E]
          ring
    _ ≤ (δt : ENNReal) ^ (10 * a / ε)
          * ((δt : ENNReal) ^ (-2 * γ) * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
          exact mul_le_mul hpref le_rfl (by simp) (by simp)
    _ = (δt : ENNReal) ^ (10 * a / ε) * (δt : ENNReal) ^ (-2 * γ)
          * (M * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ring

/-- **The coarse factor at the parent scale `b`** (blueprint
`lem:ml1bootReduceToTbCoarseBound`).

The bodies of `𝕎|_{t''}` are `b`-tubes, hence of positive finite volume
(`Kakeya.Tube.volume_pos_and_lt_top`), and `t''` is nonempty, so
`Kakeya.ml1Boot.coarse_fullness_threshold` gives `λ(𝕎|_{t''}, Z_ρ) ≥ δ̃ ^ ηc`; instantiating
the conditional coarse bound at `r = t''` and `Z_r = Z_ρ` is the conclusion.

The conditional coarse bound is quantified over *every* nonempty `r ⊆ t` and *every* shading
of `𝕎|_r`, not only over the ones `Kakeya.ml1Boot.exists_factorOneScaleUniform` happens to
return: the retained parent set is produced by the proof and cannot be named in advance.
`Kakeya.ml1Boot.multiplicity_coarse_le` is universally quantified in exactly this way.

The factoring constant is carried as a **parameter** `Cc ≥ 1`, for the reason recorded in
`Kakeya.ml1Boot.coarse_fullness_threshold`: the dilate chain needs the lemma at
`Cc = Kakeya.ml1Boot.factorOneScaleUniformDilate.C`, and `Cc` occurs in the hypothesis
`hlamρ`. -/
theorem reduceToTb_coarse_bound [Nontrivial E]
    {δt b : NNReal} (hδt0 : 0 < δt) (hδtb : δt ≤ b) (hb1 : b ≤ 1)
    {γ : ℝ} (_hγ0 : 0 ≤ γ) (_hγ1 : γ ≤ 1)
    {Cc : NNReal} (hCc : 1 ≤ Cc)
    {a ap' ηc : ℝ} (ha : 0 ≤ a) (hap' : 0 < ap') (hηc : a + 2 * ap' ≤ ηc)
    (habsorb : (Cc : ENNReal) * (δt : ENNReal) ^ ap' ≤ 1)
    {lam lamρ : ENNReal} (hlam : (δt : ENNReal) ^ a ≤ lam)
    (hlamρ : (Cc : ENNReal)⁻¹ * (δt : ENNReal) ^ ap' * lam ≤ lamρ)
    {κ : Type*} {t t'' : Finset κ} (W : κ → Tube b E) (Zρ : κ → ShadedTube b E)
    (ht'' : t'' ⊆ t) (ht''ne : t''.Nonempty)
    (hZρ : ∀ k ∈ t'', (Zρ k).toTube = W k)
    (hterm : ∀ k ∈ t'', lamρ * volume (W k).carrier ≤ volume (Zρ k).shade)
    (hcoarse : ∀ r ⊆ t, ∀ Zr : κ → ShadedTube b E, r.Nonempty →
      (∀ k ∈ r, (Zr k).toTube = W k) →
      (δt : ENNReal) ^ ηc ≤ (ShadedBody.fullness r (fun k => (Zr k).toShadedBody) : ENNReal) →
      ShadedBody.multiplicity r (fun k => (Zr k).toShadedBody)
        ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
          * ((r.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) :
    ShadedBody.multiplicity t'' (fun k => (Zρ k).toShadedBody)
      ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
        * ((t''.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hb0 : 0 < b := lt_of_lt_of_le hδt0 hδtb
  have hδt1 : δt ≤ 1 := le_trans hδtb hb1
  have hcar : ∀ k ∈ t'', ((Zρ k).toShadedBody).carrier = (W k).carrier := by
    intro k hk
    simpa using congrArg (fun T : Tube b E => T.carrier) (hZρ k hk)
  have hpos : ∀ k ∈ t'', 0 < volume ((Zρ k).toShadedBody).carrier := by
    intro k hk
    rw [hcar k hk]
    exact (Tube.volume_pos_and_lt_top (σ := b) hb0 hb1 (W k)).1
  have hfin : ∀ k ∈ t'', volume ((Zρ k).toShadedBody).carrier ≠ ⊤ := by
    intro k hk
    rw [hcar k hk]
    exact (Tube.volume_pos_and_lt_top (σ := b) hb0 hb1 (W k)).2.ne
  have hterm' : ∀ k ∈ t'',
      lamρ * volume ((Zρ k).toShadedBody).carrier ≤ volume ((Zρ k).toShadedBody).shade := by
    intro k hk
    rw [hcar k hk]
    exact hterm k hk
  have hfull : (δt : ENNReal) ^ ηc
      ≤ (ShadedBody.fullness t'' (fun k => (Zρ k).toShadedBody) : ENNReal) :=
    coarse_fullness_threshold (δt := δt) (hδt0 := hδt0) (hδt1 := hδt1)
      (Cc := Cc) (hCc := hCc)
      (a := a) (ap' := ap') (ηc := ηc) (ha := ha) (hap' := hap') (hηc := hηc)
      (habsorb := habsorb) (lam := lam) (lamρ := lamρ) (hlam := hlam) (hlamρ := hlamρ)
      (κ := κ) (t'' := t'') (W := fun k => (Zρ k).toShadedBody) (ht'' := ht''ne)
      (hpos := hpos) (hfin := hfin) (hterm := hterm')
  exact hcoarse t'' ht'' Zρ ht''ne hZρ hfull

/-- **The fine factor at the parent scale `b`** (blueprint
`lem:ml1bootReduceToTbFineBound`).

Write `C₂ = Kakeya.ml1Boot.fineFactor.C` and `C_T = Kakeya.ml1Boot.densityTransfer.C` and
suppose `K_F(γ)` holds in `ℝ³`.  For a loss exponent `ap' > 0`, `ηf` is the fullness threshold
that `Kakeya.ml1Boot.fine_genKF` supplies at `εs = ap'`; this lemma is that lemma applied with
`Λ = 2`, `μ₀ = λ_σ`, `b` in place of `τ` and the `δ̃`-dependent Frostman constant
`Cf = 2 C_T C₂ δ̃ ^ (-2 ap')`, which is legitimate because `Cf` is quantified *inside* the
`∀ᶠ δ̃` there.  Since `Cf ≥ 1` and `1 - γ/2 ≤ 1`, `Cf ^ (1 - γ/2) ≤ Cf` and the prefactor
`4 C₂ δ̃ ^ (-ap') · Cf` collapses to `4 C₂² (2 C_T) δ̃ ^ (-3 ap')`.

The two-sided density hypothesis is the assumed `λ_σ |T i| ≤ |Y i| ≤ 2 λ_σ |T i|`, which
implies the `Λ = 2`, `μ₀ = λ_σ` form `2⁻¹ λ_σ |T i| ≤ |Y i| ≤ 2 λ_σ |T i|` that
`Kakeya.ml1Boot.fine_genKF` consumes.  The smallness requirement falls on `δ̃`, not on
`δ̃ / b`, which is why `δ̃ ≤ b ≤ 1` suffices. -/
theorem reduceToTb_fine_bound (hdim : Module.finrank ℝ E = 3) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ ap' > (0 : ℝ), ∃ ηf > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} {u : Finset ι} (Tb : Tube b E) (T : ι → ShadedTube δt E)
        {lamσ : ENNReal}, 0 < lamσ →
        u.Nonempty →
        Tb.carrier ⊆ Metric.closedBall 0 1 →
        (∀ i ∈ u, (T i).carrier ⊆ Tb.carrier) →
        (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ u, lamσ * volume (T i).carrier ≤ volume (T i).shade ∧
          volume (T i).shade ≤ 2 * lamσ * volume (T i).carrier) →
        -- (a)
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tb.toConvexSpaceBody
          ≤ 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-2 * ap') →
        -- (b)
        4 * (fineFactor.C : ENNReal) * (δt : ENNReal) ^ ηf
          ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ 4 * (fineFactor.C : ENNReal) ^ 2 * (2 * (densityTransfer.C : ENNReal))
            * (δt : ENNReal) ^ (-3 * ap')
            * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro ap' hap'
  obtain ⟨ηf, hηf, h_genKF⟩ := fine_genKF hdim hγ0 hγ1 hKF ap' hap'
  refine ⟨ηf, hηf, ?_⟩
  let C : ENNReal := (fineFactor.C : ENNReal)
  have hC1 : 1 ≤ C := by
    have hCnn : 1 ≤ fineFactor.C := one_le_fineFactor_C
    change (1 : ENNReal) ≤ (fineFactor.C : ENNReal)
    exact_mod_cast hCnn
  have hC0 : C ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_fineFactor_C))
  have hCtop : C ≠ ⊤ := by exact ENNReal.coe_ne_top
  have one_le_volC : ∀ n : ℕ, (1 : NNReal) ≤ Metric.volume_comparison.C n := by
    intro n
    have hCval : Metric.volume_comparison.C n = ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) : ℝ) := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      push_cast
      field_simp
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) :=
      mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
    have : (1 : ℝ) ≤ (Metric.volume_comparison.C n : ℝ) := by
      rw [hCval]
      nlinarith
    exact_mod_cast this
  have hCT1 : 1 ≤ (densityTransfer.C : ENNReal) := by
    have hCnn : (1 : NNReal) ≤ densityTransfer.C := by
      dsimp [densityTransfer.C]
      have hCw : (1 : NNReal) ≤ plankPigeonhole.C := by
        dsimp [plankPigeonhole.C]
        exact one_le_mul (by norm_num : (1 : NNReal) ≤ 16) (one_le_volC 3)
      exact one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 256) (one_le_pow₀ hCw))
        (one_le_volC 3)
    exact_mod_cast hCnn
  have hCTtop : (densityTransfer.C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  filter_upwards [h_genKF 2 (by norm_num : (1 : NNReal) ≤ 2), self_mem_nhdsWithin] with δt
    hδt_aux hδt_pos
  intro b hδtb hb1 ι u Tb T lamσ hlamσ hu hTb hsub hED hdens hFa hFull
  have hδt0 : 0 < δt := hδt_pos
  have hδt1 : δt ≤ 1 := le_trans hδtb hb1
  have hδtle : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  have hδtpos : 0 < (δt : ENNReal) := ENNReal.coe_pos.mpr hδt0
  have hδtne : (δt : ENNReal) ≠ 0 := ne_of_gt hδtpos
  have hδttop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  let Cf : ENNReal := 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-2 * ap') * C
  have hpow1 : (1 : ENNReal) ≤ (δt : ENNReal) ^ (-2 * ap') := by
    have hneg : -2 * ap' < 0 := by nlinarith [hap']
    exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg hδtpos hδtle hneg
  have hCf1 : 1 ≤ Cf := by
    dsimp [Cf]
    exact one_le_mul (one_le_mul (one_le_mul (by norm_num : (1 : ENNReal) ≤ 2) hCT1) hpow1) hC1
  have hCftop : Cf ≠ ⊤ := by
    dsimp [Cf]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hCTtop)
        (ENNReal.rpow_ne_top_of_ne_zero hδtne hδttop)) hCtop
  have hCf_div : Cf / C = 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-2 * ap') := by
    dsimp [Cf]
    rw [ENNReal.mul_div_cancel_right hC0 hCtop]
  have hdens' : ∀ i ∈ u,
      (2 : ENNReal)⁻¹ * lamσ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (2 : ENNReal) * lamσ * volume (T i).carrier := by
    intro i hi
    have hdens_i := hdens i hi
    have hinv : (2 : ENNReal)⁻¹ * lamσ ≤ lamσ := by
      calc
        (2 : ENNReal)⁻¹ * lamσ ≤ 1 * lamσ := by
          exact mul_le_mul_of_nonneg_right
            (by norm_num : (2 : ENNReal)⁻¹ ≤ (1 : ENNReal)) (by positivity)
        _ = lamσ := by simp
    constructor
    · calc
        (2 : ENNReal)⁻¹ * lamσ * volume (T i).carrier
            ≤ lamσ * volume (T i).carrier := by
              exact mul_le_mul_of_nonneg_right hinv (by positivity)
        _ ≤ volume (T i).shade := hdens_i.1
    · exact hdens_i.2
  have hFa' : frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tb.toConvexSpaceBody
      ≤ Cf / C := by
    rw [hCf_div]
    exact hFa
  have hFull' : C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ ηf
      ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) := by
    calc
      C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ ηf = 4 * C * (δt : ENNReal) ^ ηf := by
        ring
      _ ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) := hFull
  have hmult : ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
      ≤ C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ (-ap')
        * Cf ^ (1 - γ / 2)
        * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
        * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    exact hδt_aux Cf hCf1 hCftop b hδtb hb1 (ι := ι) (u := u) Tb T (μ₀ := lamσ)
      ⟨hlamσ, hu, hTb, hsub, hED, hdens', hFull'⟩ hFa'
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  have hCfmono : Cf ^ (1 - γ / 2) ≤ Cf := by
    calc
      Cf ^ (1 - γ / 2) ≤ Cf ^ (1 : ℝ) := by
        exact ENNReal.rpow_le_rpow_of_exponent_le hCf1 (by nlinarith [hγ0])
      _ = Cf := by rw [ENNReal.rpow_one]
  have hrpow_add : (δt : ENNReal) ^ (-3 * ap')
      = (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ (-2 * ap') := by
    calc
      (δt : ENNReal) ^ (-3 * ap') = (δt : ENNReal) ^ (-ap' + -2 * ap') := by
        congr 1
        ring
      _ = (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ (-2 * ap') :=
            (ENNReal.rpow_add (x := (δt : ENNReal)) (-ap') (-2 * ap') hδtne hδttop)
  have hpref_equal : C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ (-ap')
      * (2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-2 * ap') * C)
      = 4 * C ^ 2 * (2 * (densityTransfer.C : ENNReal)) * (δt : ENNReal) ^ (-3 * ap') := by
    rw [hrpow_add]
    ring
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ (-ap') * Cf ^ (1 - γ / 2)
          * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := hmult
    _ ≤ C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ (-ap') * Cf
          * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          gcongr
    _ = 4 * C ^ 2 * (2 * (densityTransfer.C : ENNReal)) * (δt : ENNReal) ^ (-3 * ap')
          * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          dsimp only [Cf]
          rw [hpref_equal]

end ReduceToTb

end ml1Boot

end Kakeya
