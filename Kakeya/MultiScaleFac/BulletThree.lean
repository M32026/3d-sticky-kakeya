/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Clamp
public import Kakeya.MultiScaleFac.GapsKT

/-!
# The third bullet of half (A) from alternative (ii), with a paired band

`Kakeya.StickyKakeya.ssf_bulletThree_of_alternativeTwo` states the third bullet of the sharp
dichotomy from the terminal alternative (ii) alone, and its own docstring records why that
statement is not provable: uniformity and a majority set do not spread a lower bound obtained at
one grid node to the other nodes of the level.  What does spread it is a two-sided band indexed by
the *pair* of levels, which is exactly `Kakeya.MultiScaleFac.PairBandOn`, carried by the banded
stopping time.

This file states and proves the banded version,
`Kakeya.MultiScaleFac.bulletThree_of_alternativeTwo_banded`.  Relative to the old statement:

* the uniform hierarchy is the one induced by a `Kakeya.MultiScaleFac.GridUniform` system, since the
  witness reading consumes the clumping field;
* a paired band `PairBandOn s 𝒢 2 Φ (ssfGridLen δ)` is assumed;
* the sampling exponent is pinned to `ε = 1/√N` with `4096 ≤ N` and `3N ≤ M`, which is what the
  window arithmetic of `Kakeya.MultiScaleFac.A.window_instance` needs;
* the gap budget of the conclusion is a *new* natural number `cB` dominating the input `c`, because
  clamping the narrow window back onto the `ε`-window costs `O(⌈8√N⌉)` grid steps.

The chain is: window arithmetic, then the narrow-window witness at exponent
`e' = (1 + 2N/M)ε + 6/(b - a)`, then the clamp back onto the `ε`-window.

One step of the chain is *not* available upstream.  The witness package displays the coefficient
`32 · scaleGapLoss 1 δ · D₀` and `Kakeya.StickyKakeya.ssfA_narrow_spread_package` asks that
coefficient to be at most `A · scaleGapLoss 27 δ`; with the terminal alternative's own
`D₀ = C₂ · δ^{-27/M} = C₂ · scaleGapLoss 27 δ` the product is a `scaleGapLoss 28 δ`, one grid step
above what that lemma accepts.  `Kakeya.MultiScaleFac.A.bandedA_spread` is the same spreading
step with the extra step paid for: the surplus `scaleGapLoss 1 δ` is moved from the witness
coefficient into the packing factor's own budget, so the hypothesis reads `scaleGapLoss 28 δ` and
the conclusion asks `2n + 28 ≤ c₀` instead of `2n + 27 ≤ c₀`.  Nothing else changes.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Arithmetic of the gap losses in `ENNReal` -/

/-- **Two gap losses add their budgets, in `ENNReal`.**  The extended-real reading of
`Kakeya.MultiScaleFac.A.scaleGapLoss_add`. -/
private theorem A.bandedA_ofReal_scaleGapLoss_mul {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (c₁ c₂ : ℕ) :
    ENNReal.ofReal (scaleGapLoss c₁ δ) * ENNReal.ofReal (scaleGapLoss c₂ δ)
      = ENNReal.ofReal (scaleGapLoss (c₁ + c₂) δ) := by
  rw [← ENNReal.ofReal_mul (zero_le_one.trans (one_le_scaleGapLoss c₁ hδ hδ1)),
    MultiScaleFac.A.scaleGapLoss_add hδ c₁ c₂]

/-- **The packing coefficient of the descent, split into its factors.**  The coercion of
`V · (Λ · scaleGapLoss c δ)` to `ENNReal` is the product of the three coercions. -/
private theorem A.bandedA_coe_lambda {δ : NNReal} (_hδ : 0 < δ) (_hδ1 : δ ≤ 1) (V Lam : NNReal)
    (c : ℕ) :
    ((V * (Lam * Real.toNNReal (scaleGapLoss c δ)) : NNReal) : ENNReal)
      = (V : ENNReal) * ((Lam : ENNReal) * ENNReal.ofReal (scaleGapLoss c δ)) := by
  rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.ofReal]

/-- **Moving one grid step from the witness coefficient into the packing budget.**  The witness
coefficient of the half-(A) third bullet carries a `scaleGapLoss 28 δ`, one step more than
`Kakeya.MultiScaleFac.A.narrow_absorb` accepts; since gap losses add their budgets, the surplus
step may be moved into the packing factor `scaleGapLoss m δ` of the descent. -/
private theorem A.bandedA_shift_coeff {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {A V Lam : NNReal}
    {D Z : ENNReal} (hD : D ≤ (A : ENNReal) * ENNReal.ofReal (scaleGapLoss 28 δ)) (m : ℕ) :
    D * Z * ((V * (Lam * Real.toNNReal (scaleGapLoss m δ)) : NNReal) : ENNReal)
      ≤ (A : ENNReal) * ENNReal.ofReal (scaleGapLoss 27 δ) * Z
          * ((V * (Lam * Real.toNNReal (scaleGapLoss (m + 1) δ)) : NNReal) : ENNReal) := by
  have hkey : ENNReal.ofReal (scaleGapLoss 28 δ) * ENNReal.ofReal (scaleGapLoss m δ)
      = ENNReal.ofReal (scaleGapLoss 27 δ) * ENNReal.ofReal (scaleGapLoss (m + 1) δ) := by
    rw [MultiScaleFac.A.bandedA_ofReal_scaleGapLoss_mul hδ hδ1 28 m,
      MultiScaleFac.A.bandedA_ofReal_scaleGapLoss_mul hδ hδ1 27 (m + 1),
      show 28 + m = 27 + (m + 1) from by omega]
  rw [MultiScaleFac.A.bandedA_coe_lambda hδ hδ1 V Lam m,
    MultiScaleFac.A.bandedA_coe_lambda hδ hδ1 V Lam (m + 1)]
  calc
    D * Z * ((V : ENNReal) * ((Lam : ENNReal) * ENNReal.ofReal (scaleGapLoss m δ)))
        ≤ (A : ENNReal) * ENNReal.ofReal (scaleGapLoss 28 δ) * Z
            * ((V : ENNReal) * ((Lam : ENNReal) * ENNReal.ofReal (scaleGapLoss m δ))) := by
        gcongr
    _ = (A : ENNReal) * Z * (V : ENNReal) * (Lam : ENNReal)
          * (ENNReal.ofReal (scaleGapLoss 28 δ) * ENNReal.ofReal (scaleGapLoss m δ)) := by ring
    _ = (A : ENNReal) * Z * (V : ENNReal) * (Lam : ENNReal)
          * (ENNReal.ofReal (scaleGapLoss 27 δ) * ENNReal.ofReal (scaleGapLoss (m + 1) δ)) := by
        rw [hkey]
    _ = (A : ENNReal) * ENNReal.ofReal (scaleGapLoss 27 δ) * Z
        * ((V : ENNReal) * ((Lam : ENNReal) * ENNReal.ofReal (scaleGapLoss (m + 1) δ))) := by ring

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The coefficient of the terminal alternative, read at budget `28`.**  On the grid of length
`ssfGridLen δ` the witness package of the narrow window displays an absolute constant against a
single `Kakeya.MultiScaleFac.scaleGapLoss 28 δ`. -/
private theorem A.bandedA_hD {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (C2 Cu : NNReal) :
    ENNReal.ofReal (32 * scaleGapLoss 1 δ)
        * (((C2 : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(27 / (ssfGridLen δ : ℝ)))))
            * ((fibreFromNodeConst (E := E) : ENNReal) * ((Cu : NNReal) : ENNReal) ^ 5))
      ≤ ((32 * C2 * fibreFromNodeConst (E := E) * Cu ^ 5 : NNReal) : ENNReal)
          * ENNReal.ofReal (scaleGapLoss 28 δ) := by
  have h27 : (δ : ℝ) ^ (-(27 / (ssfGridLen δ : ℝ))) = scaleGapLoss 27 δ := by
    rw [← MultiScaleFac.A.rpow_neg_div_eq_scaleGapLoss]
    norm_num
  have hxy : ENNReal.ofReal (scaleGapLoss 1 δ) * ENNReal.ofReal (scaleGapLoss 27 δ) =
      ENNReal.ofReal (scaleGapLoss 28 δ) := by
    simpa [show (1 + 27 : ℕ) = 28 by norm_num]
      using (MultiScaleFac.A.bandedA_ofReal_scaleGapLoss_mul hδ hδ1 1 27)
  refine le_of_eq ?_
  rw [h27, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32), ENNReal.ofReal_ofNat, ← hxy]
  push_cast
  ring

/-- **The coefficient bookkeeping of one narrow-window scale, at gap budget `28`.**  Verbatim
`Kakeya.MultiScaleFac.A.narrow_absorb` except that the outer coefficient is allowed one more grid
step: `hD` reads `scaleGapLoss 28 δ` and the displayed budget is `c₁ + 28` rather than
`c₁ + 27`. -/
private theorem A.bandedA_absorb {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {Kn : ℕ} {R V₁ V₂ Lam A B : NNReal} (hB1 : 1 ≤ B)
    (hBle : (Kn : NNReal) * (2 * A) * R * V₁ * V₂ * Lam ≤ B)
    {c₁ K cL : ℕ} (hcL : c₁ + 28 ≤ cL)
    {X Y D dm Dm : ENNReal} (hdm0 : dm ≠ 0) (hdmtop : dm ≠ ⊤)
    (hDm : Dm ≤ (R : ENNReal) * dm)
    (hD : D ≤ (A : ENNReal) * ENNReal.ofReal (scaleGapLoss 28 δ))
    (h : X ≤ (V₁ : ENNReal)
        * (D * (Kn : ENNReal) / dm * ((2 : NNReal) : ENNReal) * Dm
            * ((V₂ * (Lam * Real.toNNReal (scaleGapLoss c₁ δ)) : NNReal) : ENNReal) * Y)) :
    X ≤ (B : ENNReal) * totalLoss B K cL δ * Y := by
  have hkey : D * (Kn : ENNReal) / dm * ((2 : NNReal) : ENNReal) * Dm
      * ((V₂ * (Lam * Real.toNNReal (scaleGapLoss c₁ δ)) : NNReal) : ENNReal)
      ≤ (A : ENNReal) * ENNReal.ofReal (scaleGapLoss 27 δ) * (Kn : ENNReal) / dm
          * ((2 : NNReal) : ENNReal) * Dm
          * ((V₂ * (Lam * Real.toNNReal (scaleGapLoss (c₁ + 1) δ)) : NNReal) : ENNReal) := by
    have hshift := MultiScaleFac.A.bandedA_shift_coeff hδ hδ1 hD
      (Z := (Kn : ENNReal) / dm * ((2 : NNReal) : ENNReal) * Dm) (V := V₂) (Lam := Lam) (m := c₁)
    simp only [div_eq_mul_inv] at hshift ⊢
    convert hshift using 1 <;> ring
  exact MultiScaleFac.A.narrow_absorb hδ hδ1 hB1 hBle (c₁ := c₁ + 1) (by omega) hdm0 hdmtop hDm
    (D := (A : ENNReal) * ENNReal.ofReal (scaleGapLoss 27 δ)) le_rfl
    (h.trans (mul_le_mul_right (mul_le_mul_left hkey Y) (V₁ : ENNReal)))

/-! ### The spreading step at the enlarged gap budget -/

open scoped Classical in
/-- **Spreading one witness across a narrow-window scale, at gap budget `28`.**  Verbatim
`Kakeya.StickyKakeya.ssfA_narrow_spread_package` except that the witness coefficient is allowed one
more grid step, `hD` reading `scaleGapLoss 28 δ`, and the gap budget of the conclusion is `2n + 28`
instead of `2n + 27`. -/
private theorem A.bandedA_spread {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {t : Finset ι} {T : ι → Tube δ E} {Cv : NNReal} (hCv : 1 ≤ Cv)
    (𝒢 : GridUniform t T (ssfGridLen δ) Cv) (hs : t.Nonempty)
    {Φ : ℕ → ℕ → ENNReal} (hband : PairBandOn t 𝒢 2 Φ (ssfGridLen δ))
    {c b : ℕ} (hcb : c ≤ b) (hbM : b ≤ ssfGridLen δ) (hcM : c ≤ ssfGridLen δ)
    (h2d : 2 * δ ≤ gridScale δ (ssfGridLen δ) c)
    {ρ : NNReal} (h32 : 32 * gridScale δ (ssfGridLen δ) c ≤ ρ)
    (hsharp : (ρ : ℝ) ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) c : ℝ))
    {Kn : ℕ}
    (hP : ∀ p ∈ 𝒢.toUniformTubeSet.cover.indexSet c,
      ∃ P ⊆ 𝒢.toUniformTubeSet.cover.indexSet c, P.card ≤ Kn ∧
        𝒢.toUniformTubeSet.nodesIn b ((𝒢.toUniformTubeSet.cover.tube c p).rescale
            (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody
          ⊆ P.biUnion (fun q =>
              (coverClass t (𝒢.toUniformTubeSet.cover.assign c) q).image
                (𝒢.toUniformTubeSet.cover.assign b)))
    {dm Dm : ENNReal} {R : NNReal} (hdm0 : dm ≠ 0) (hdmtop : dm ≠ ⊤)
    (hDm : Dm ≤ (R : ENNReal) * dm)
    (hdmlow : ∀ p ∈ 𝒢.toUniformTubeSet.cover.indexSet c, dm ≤ Kakeya.densityIn
        (𝒢.toUniformTubeSet.nodesIn b ((𝒢.toUniformTubeSet.cover.tube c p).rescale
            (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)
        (fun j' => (𝒢.toUniformTubeSet.cover.tube b j').toConvexSpaceBody)
        ((𝒢.toUniformTubeSet.cover.tube c p).rescale
            (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)
    (hdens : ∀ p ∈ 𝒢.toUniformTubeSet.cover.indexSet c, Kakeya.densityIn
        (𝒢.toUniformTubeSet.nodesIn b ((𝒢.toUniformTubeSet.cover.tube c p).rescale
            (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)
        (fun j' => (𝒢.toUniformTubeSet.cover.tube b j').toConvexSpaceBody)
        ((𝒢.toUniformTubeSet.cover.tube c p).rescale
            (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody ≤ Dm)
    {A B : NNReal} {K cL : ℕ} (hB1 : 1 ≤ B)
    (hBle : (Kn : NNReal) * (2 * A) * R
        * ((Tube.le_volume.c (Module.finrank ℝ E))⁻¹)
        * Tube.volume_le.C (Module.finrank ℝ E)
        * MultiScaleFac.A.narrowLambdaConst (Module.finrank ℝ E) (uniformTubeSetCuOf (E := E) Cv)
            ≤ B)
    (hcL : 2 * Module.finrank ℝ E + 28 ≤ cL)
    {zeta : ℝ} {D : ENNReal} (hD : D ≤ (A : ENNReal) * ENNReal.ofReal (scaleGapLoss 28 δ))
    {j₀ : ι} (hj₀ : j₀ ∈ 𝒢.toUniformTubeSet.cover.indexSet c)
    (hX : ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta)
      ≤ D * ConvexSpaceBody.frostmanConstant
          (𝒢.toUniformTubeSet.nodesIn b ((𝒢.toUniformTubeSet.cover.tube c j₀).rescale
              (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)
          (fun j' => (𝒢.toUniformTubeSet.cover.tube b j').toConvexSpaceBody)
          ((𝒢.toUniformTubeSet.cover.tube c j₀).rescale
              (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody) :
    ∀ j ∈ 𝒢.toUniformTubeSet.cover.indexSet b,
      ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta)
        ≤ (B : ENNReal) * totalLoss B K cL δ
            * ConvexSpaceBody.frostmanConstant
                (𝒢.toUniformTubeSet.nodesIn b
                    ((𝒢.toUniformTubeSet.cover.tube b j).rescale ρ).toConvexSpaceBody)
                (fun j' => (𝒢.toUniformTubeSet.cover.tube b j').toConvexSpaceBody)
                ((𝒢.toUniformTubeSet.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  intro j hj
  have hCu : (1 : NNReal) ≤ uniformTubeSetCuOf (E := E) Cv := hCv.trans (le_max_left _ _)
  have hbandcb := MultiScaleFac.A.band_of_pairBandOn 𝒢 hband hcM hbM
  have hgrid := MultiScaleFac.A.hgrid_of_witness 𝒢.toUniformTubeSet hcb hbM hdm0 hP hdmlow hdens
    hbandcb hj₀ hX
  have hstep := MultiScaleFac.A.narrow_descent hδ hδ1 𝒢.toUniformTubeSet hCu hs hcM hbM hcb h2d h32
    hsharp hgrid hj
  exact MultiScaleFac.A.bandedA_absorb hδ hδ1 hB1 hBle hcL hdm0 hdmtop hDm hD hstep

/-! ### The third bullet on the narrow window, from alternative (ii) -/

open scoped Classical in
/-- **The third bullet of half (A) on the narrow window, driven by alternative (ii).**  The witness
half `Kakeya.MultiScaleFac.A.narrow_witness_package`, fed with the terminal alternative, produces at
each scale of the `e'`-window a reading level `c` together with a level-`c` node carrying the lower
bound; those are then spread by `Kakeya.MultiScaleFac.A.bandedA_spread`. -/
private theorem A.bandedA_narrow_window {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδlt : δ < 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ)
    {s : Finset ι} {T : ι → Tube δ E} {Cv : NNReal} (hCv : 1 ≤ Cv) (hs : s.Nonempty)
    (𝒢 : GridUniform s T (ssfGridLen δ) Cv)
    {Φ : ℕ → ℕ → ENNReal} (hband : PairBandOn s 𝒢 2 Φ (ssfGridLen δ))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ ssfGridLen δ)
    {Kn : ℕ}
    (hcov : ∀ k : ℕ, k ≤ b → k < ssfGridLen δ →
      ∀ p ∈ 𝒢.toUniformTubeSet.cover.indexSet k,
        ∃ P ⊆ 𝒢.toUniformTubeSet.cover.indexSet k, P.card ≤ Kn ∧
          𝒢.toUniformTubeSet.nodesIn b ((𝒢.toUniformTubeSet.cover.tube k p).rescale
              (8 * gridScale δ (ssfGridLen δ) k)).toConvexSpaceBody
            ⊆ P.biUnion (fun q =>
                (coverClass s (𝒢.toUniformTubeSet.cover.assign k) q).image
                  (𝒢.toUniformTubeSet.cover.assign b)))
    (N : ℕ) (C2 : NNReal) {eps zeta zeta' : ℝ} (hepspos : 0 < eps) (heps64 : eps ≤ 1 / 64)
    (hz0 : 0 ≤ zeta) (hzz : zeta ≤ eps * zeta') (hz' : zeta' ≤ eps)
    {e' : ℝ} (hee' : (1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps ≤ e')
    (hk : (6 : ℝ) ≤ (e' - (1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps)
        * ((b : ℝ) - (a : ℝ)))
    {F : Finset ι} {j₀ : ι} (hj₀ : j₀ ∈ goodNodes 𝒢.toUniformTubeSet b F)
    (halt : ∀ r : NNReal,
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ))
            ^ ((1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps) ≤ (r : ℝ) →
      (r : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ))
            ^ ((1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps) →
      ∀ i0 ∈ F,
        ENNReal.ofReal (((r : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta')
          ≤ (C2 : ENNReal)
              * ENNReal.ofReal ((δ : ℝ) ^ (-(27 / (ssfGridLen δ : ℝ)))) *
              ConvexSpaceBody.frostmanConstant (fibreIndex s T δ r i0)
                (fibreBodies T (gridScale δ (ssfGridLen δ) b))
                ((T i0).rescale (2 * r)).toConvexSpaceBody)
    {B₀ : NNReal} {K₀ cL : ℕ} (hB1 : 1 ≤ B₀)
    (hBle : (Kn : NNReal)
        * (2 * (32 * C2 * fibreFromNodeConst (E := E)
            * uniformTubeSetCuOf (E := E) Cv ^ 5))
        * nodeDensityRatioConst (Module.finrank ℝ E) (uniformTubeSetCuOf (E := E) Cv)
        * ((Tube.le_volume.c (Module.finrank ℝ E))⁻¹)
        * Tube.volume_le.C (Module.finrank ℝ E)
        * MultiScaleFac.A.narrowLambdaConst (Module.finrank ℝ E) (uniformTubeSetCuOf (E := E) Cv)
            ≤ B₀)
    (hcL : 2 * Module.finrank ℝ E + 28 ≤ cL) :
    ∀ ρ : NNReal,
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e' ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e' →
      ∀ j ∈ 𝒢.toUniformTubeSet.cover.indexSet b,
        ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta')
          ≤ (B₀ : ENNReal) * totalLoss B₀ K₀ cL δ
              * ConvexSpaceBody.frostmanConstant
                  (𝒢.toUniformTubeSet.nodesIn b
                      ((𝒢.toUniformTubeSet.cover.tube b j).rescale ρ).toConvexSpaceBody)
                  (fun j' => (𝒢.toUniformTubeSet.cover.tube b j').toConvexSpaceBody)
                  ((𝒢.toUniformTubeSet.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  intro rho hlo hhi
  have hCur : (1 : NNReal) ≤ uniformTubeSetCuOf (E := E) Cv := hCv.trans (le_max_left _ _)
  have hzeta0 : 0 ≤ zeta' := MultiScaleFac.A.Alt.zeta_nonneg_of_mul_le hepspos hz0 hzz
  have hzeta1 : zeta' ≤ 1 := MultiScaleFac.A.Alt.zeta_le_one_of_le heps64 hz'
  have he0 : 0 ≤ (1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps :=
    MultiScaleFac.A.Alt.supplyExp_nonneg N (ssfGridLen δ) (le_of_lt hepspos)
  have hAlt := MultiScaleFac.A.Alt.hAlt_of_alternativeTwo N C2 halt
  obtain ⟨cRead, hcb, hcM, h2d, hS32, hsharp, jRead, hjRead, hX⟩ :=
    MultiScaleFac.A.narrow_witness_package hδ hδ1 hδlt hδ16 hM hCv hs 𝒢 hzeta0 hzeta1 hab hb
      he0 hee' hk hlo hhi hj₀ hAlt
  have hrho1 : rho ≤ 1 := MultiScaleFac.A.window_scale_le_one hδ hδ1 hab (le_trans he0 hee') hhi
  have hSS : 8 * gridScale δ (ssfGridLen δ) cRead ≤ 1 :=
    (mul_le_mul_of_nonneg_right (by norm_num : (8 : NNReal) ≤ 32) zero_le).trans
      (hS32.trans hrho1)
  have hcltM : cRead < ssfGridLen δ := MultiScaleFac.A.lt_of_two_mul_le_gridScale hδ hM hcM h2d
  obtain ⟨dm, Dm, hdm0, hdmtop, hDmtop, hdmlow, hdens, hDm⟩ :=
    MultiScaleFac.A.exists_density_pair hδ hδ1 𝒢.toUniformTubeSet hCur hs hcM hb hcb h2d hSS
      (branchingN_pos 𝒢.toUniformTubeSet hCur hs hb)
      (branchingN_pos 𝒢.toUniformTubeSet hCur hs hcM)
  exact MultiScaleFac.A.bandedA_spread hδ hδ1 hCv 𝒢 hs hband hcb hb hcM h2d hS32 hsharp
    (hcov cRead hcb hcltM) hdm0 hdmtop hDm hdmlow hdens hB1 hBle hcL
    (MultiScaleFac.A.bandedA_hD hδ hδ1 C2 (uniformTubeSetCuOf (E := E) Cv)) hjRead hX

/-! ### The coarse-neighbour cover, with its constant hoisted before the index type -/

open scoped Classical in
/-- **The coarse-neighbour cover, at a constant independent of the index type.**  Verbatim
`Kakeya.MultiScaleFac.exists_coarseNeighbours` except that the index type is quantified *inside*
the existential, so that the constant `⌈2 · 25^{2n} · 32^{2n} · C_u⌉` is not formally tied to one
index type. -/
private theorem A.bandedA_exists_coarseNeighbours_raw (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ Kn : ℕ, 1 ≤ Kn ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
      ∀ {M : ℕ} {s : Finset ι} {T : ι → Tube δ E} (𝒰 : UniformTubeSet s T M Cu),
      s.Nonempty →
      ∀ {a c : ℕ}, a ≤ c → c ≤ M → 2 * δ ≤ gridScale δ M a →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ∃ P ⊆ 𝒰.cover.indexSet a, P.card ≤ Kn ∧
          𝒰.nodesIn c ((𝒰.cover.tube a j).rescale
              (8 * gridScale δ M a)).toConvexSpaceBody
            ⊆ P.biUnion (fun p =>
                (coverClass s (𝒰.cover.assign a) p).image (𝒰.cover.assign c)) :=
  exists_coarseNeighbours.{u, _} (E := E) Cu hCu

open scoped Classical in
/-- **The coarse-neighbour cover on the half-(A) grid, with the constant hoisted.**

`Kakeya.MultiScaleFac.exists_coarseNeighbours` read on the half-(A) grid, with the index type
quantified inside the existential and the scale condition `2δ ≤ σ_k` discharged from `k < M` by
`Kakeya.MultiScaleFac.A.clamp_two_delta_le_gridScale`. -/
private theorem A.bandedA_exists_coarseNeighbours (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ Kn : ℕ, 1 ≤ Kn ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
        δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) → 0 < ssfGridLen δ →
      ∀ {s : Finset ι} {T : ι → Tube δ E} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu),
        s.Nonempty →
      ∀ {b : ℕ}, b ≤ ssfGridLen δ → ∀ k ≤ b, k < ssfGridLen δ →
      ∀ p ∈ 𝒰.cover.indexSet k,
        ∃ P ⊆ 𝒰.cover.indexSet k, P.card ≤ Kn ∧
          𝒰.nodesIn b (((𝒰.cover.tube k p).rescale
              (8 * gridScale δ (ssfGridLen δ) k)).toConvexSpaceBody)
            ⊆ P.biUnion (fun q =>
                (coverClass s (𝒰.cover.assign k) q).image (𝒰.cover.assign b)) := by
  obtain ⟨K, hK, hco⟩ := MultiScaleFac.A.bandedA_exists_coarseNeighbours_raw (E := E) Cu hCu
  refine ⟨K, hK, ?_⟩
  intro iota d hdpos hdle1 hd16 hM s T u hun b hb k hkb hklt p hpidx
  exact hco (M := ssfGridLen d) hdpos hdle1 (s := s) (T := T) u hun (a := k) (c := b)
    hkb hb (MultiScaleFac.A.clamp_two_delta_le_gridScale hdpos hdle1 hd16 hM hklt) (j := p) hpidx

/-! ### The banded third bullet -/

open scoped Classical in
/-- **The third bullet of the sharp dichotomy from alternative (ii), with a paired band**
(blueprint `lem:bullet3AltTwoBandedA`).  The banded replacement for
`Kakeya.StickyKakeya.ssf_bulletThree_of_alternativeTwo`: the same conclusion, read on the hierarchy
`𝒢.toUniformTubeSet` induced by a grid-uniform system carrying a paired band, and with the gap
budget of the displayed loss replaced by a budget `cB` dominating the input `c`. -/
theorem bulletThree_of_alternativeTwo_banded (_hn : Module.finrank ℝ E = 3)
    (N : ℕ) (Cv Cg C₂ C₃ : NNReal) (hCv : 1 ≤ Cv) (_hCg : 1 ≤ Cg) (_hC₂ : 1 ≤ C₂) (_hC₃ : 1 ≤ C₃)
    (Kg c K₃ : ℕ) {ε : ℝ} (hεpos : 0 < ε) (hε64 : ε ≤ 1 / 64)
    (hN : 4096 ≤ N) (hεN : ε = 1 / Real.sqrt (N : ℝ)) :
    ∃ (B : NNReal) (K cB : ℕ), 1 ≤ B ∧ Cv ≤ B ∧ Kg ≤ K ∧ c ≤ cB ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
        δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) → 16 ≤ ssfGridLen δ →
        3 * N ≤ ssfGridLen δ →
      ∀ (s : Finset ι) (T : ι → Tube δ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ 𝒢 : GridUniform s T (ssfGridLen δ) Cv,
      ∀ {Φ : ℕ → ℕ → ENNReal}, PairBandOn s 𝒢 2 Φ (ssfGridLen δ) →
      ∀ ζ ζ' : ℝ, 0 ≤ ζ → ζ ≤ ε * ζ' → ζ' ≤ ε →
      ∀ a b : ℕ, a < b → b ≤ ssfGridLen δ → IsLongBlock (ssfGridLen δ) ε a b →
      (∀ j ∈ 𝒢.toUniformTubeSet.cover.indexSet a,
        ConvexSpaceBody.frostmanConstant (𝒢.toUniformTubeSet.nodesUnder b a j)
            (fun j' => (𝒢.toUniformTubeSet.cover.tube b j').toConvexSpaceBody)
            (𝒢.toUniformTubeSet.cover.tube a j).toConvexSpaceBody
          ≤ (C₃ : ENNReal) * totalLoss C₃ K₃ c δ *
              ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
                  / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ)) →
      ∀ F ⊆ s, s.card ≤ 2 * F.card →
      (∀ ρ : NNReal,
        (gridScale δ (ssfGridLen δ) b : ℝ)
            * ((gridScale δ (ssfGridLen δ) a : ℝ)
                / (gridScale δ (ssfGridLen δ) b : ℝ))
              ^ ((1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * ε) ≤ (ρ : ℝ) →
        (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
            * ((gridScale δ (ssfGridLen δ) b : ℝ)
                / (gridScale δ (ssfGridLen δ) a : ℝ))
              ^ ((1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * ε) →
        ∀ i₀ ∈ F,
          ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
            ≤ (C₂ : ENNReal)
                * ENNReal.ofReal ((δ : ℝ) ^ (-(27 / (ssfGridLen δ : ℝ)))) *
                ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ i₀)
                  (fibreBodies T (gridScale δ (ssfGridLen δ) b))
                  ((T i₀).rescale (2 * ρ)).toConvexSpaceBody) →
      ∀ ρ : NNReal,
        (gridScale δ (ssfGridLen δ) b : ℝ)
            * ((gridScale δ (ssfGridLen δ) a : ℝ)
                / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ) →
        (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
            * ((gridScale δ (ssfGridLen δ) b : ℝ)
                / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε →
        ∀ j ∈ 𝒢.toUniformTubeSet.cover.indexSet b,
          ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
            ≤ (B : ENNReal) * totalLoss B K cB δ *
                ConvexSpaceBody.frostmanConstant
                  (𝒢.toUniformTubeSet.nodesIn b
                    ((𝒢.toUniformTubeSet.cover.tube b j).rescale ρ).toConvexSpaceBody)
                  (fun j' => (𝒢.toUniformTubeSet.cover.tube b j').toConvexSpaceBody)
                  ((𝒢.toUniformTubeSet.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  have hCu : (1 : NNReal) ≤ uniformTubeSetCuOf (E := E) Cv := hCv.trans (le_max_left _ _)
  obtain ⟨Kn, _hKn1, hcover⟩ :=
    MultiScaleFac.A.bandedA_exists_coarseNeighbours (E := E) (uniformTubeSetCuOf (E := E) Cv) hCu
  obtain ⟨B0, hB01, hB0le, _⟩ :=
    MultiScaleFac.A.exists_common_const_pair
      ((Kn : NNReal) * (2 * (32 * C₂ * fibreFromNodeConst (E := E)
            * uniformTubeSetCuOf (E := E) Cv ^ 5))
        * nodeDensityRatioConst (Module.finrank ℝ E) (uniformTubeSetCuOf (E := E) Cv)
        * ((Tube.le_volume.c (Module.finrank ℝ E))⁻¹)
        * Tube.volume_le.C (Module.finrank ℝ E)
        * MultiScaleFac.A.narrowLambdaConst (Module.finrank ℝ E) (uniformTubeSetCuOf (E := E) Cv)) 1
  obtain ⟨Bc, hBc1, hBcfine, hBccoarse⟩ :=
    MultiScaleFac.A.exists_common_const_pair
      (2 * 25 ^ (2 * Module.finrank ℝ E) * 128 ^ (2 * Module.finrank ℝ E)
          * uniformTubeSetCuOf (E := E) Cv * (Kn : NNReal) * 2
          * scaleGapVolConst (Module.finrank ℝ E))
      ((Tube.le_volume.c (Module.finrank ℝ E))⁻¹
          * (Tube.volume_le.C (Module.finrank ℝ E)
              * (2 * 25 ^ (2 * Module.finrank ℝ E) * 128 ^ (2 * Module.finrank ℝ E)
                  * uniformTubeSetCuOf (E := E) Cv ^ 6)))
  obtain ⟨Cw, K, cw, hCw1, hB0C, hBcC, hK0K, hK2K, hc0c, hCmul, hKadd, hcadd⟩ :=
    MultiScaleFac.A.exists_clamp_bulletThree_window_const (C₀ := B0) (B := Bc) hB01 hBc1
      0 0 (2 * Module.finrank ℝ E + 28) ⌈8 * Real.sqrt (N : ℝ)⌉₊ (Module.finrank ℝ E)
  obtain ⟨Bf, hBf1, hCBf, hCvBf⟩ := MultiScaleFac.A.exists_common_const_pair Cw Cv
  refine ⟨Bf, max K Kg, max cw c, hBf1, hCvBf, le_max_right K Kg, le_max_right cw c, ?_⟩
  intro iota d hd0 hd1 hd16 hM16 hNM s T hs hball G Phi hband zeta zeta' hz0 hzz hz'
    a b hab hbM hlong hC3hyp F hFsub hFcard halt rho hlo hhi
  have hdlt : d < 1 := MultiScaleFac.A.lt_one_of_sixteen_rpow_le hd16 hM16
  have hMpos : 0 < ssfGridLen d := MultiScaleFac.A.ssfGridLen_pos hM16
  obtain ⟨hablt, hepp, hee, heps, hepsba, hgap6, hstep, hnwne, hwin1⟩ :=
    MultiScaleFac.A.window_instance hd0 hd1 hdlt hMpos hN hNM hεN hbM hlong rfl rfl
  obtain ⟨j0, _hj0idx, hj0good⟩ :=
    MultiScaleFac.A.exists_goodNode hCu hs G.toUniformTubeSet hbM hFsub hFcard
  have hP := fun (k : ℕ) (hkb : k ≤ b) (hkM : k < ssfGridLen d) =>
    hcover hd0 hd1 hd16 hMpos G.toUniformTubeSet hs hbM k hkb hkM
  have hnarrow :=
    MultiScaleFac.A.bandedA_narrow_window hd0 hd1 hdlt hd16 hMpos hCv hs G hband (le_of_lt hablt)
      hbM hP
      (K₀ := 0)
      N C₂ hεpos hε64 hz0 hzz hz' hee hgap6 hj0good halt hB01 hB0le le_rfl
  have hZeta0 : 0 ≤ zeta' := MultiScaleFac.A.Alt.zeta_nonneg_of_mul_le hεpos hz0 hzz
  have hZeta1 : zeta' ≤ 1 := MultiScaleFac.A.Alt.zeta_le_one_of_le hε64 hz'
  have hclamp :=
    MultiScaleFac.A.clamp_bulletThree_window hd0 hd1 hdlt hd16 hMpos G.toUniformTubeSet hCu hs hablt
      hbM
      (le_of_lt hεpos) heps hepsba hstep hnwne hwin1 hP
      (MultiScaleFac.A.clamp_band_lower G hband hbM) (MultiScaleFac.A.clamp_band_upper G hband hbM)
      hZeta0 hZeta1 hB01 hBc1 hBcfine hBccoarse hCmul hKadd hcadd
      hnarrow rho hlo hhi
  intro j hj
  have hmax : totalLoss Cw K cw d ≤ totalLoss Bf (max K Kg) (max cw c) d :=
    totalLoss_mono hCw1 hCBf (le_max_left K Kg) (le_max_left cw c) hd0 hd1
  exact (hclamp j hj).trans (by gcongr)

end MultiScaleFac

end Kakeya

end
