/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ChainUniform
public import Kakeya.MultiScaleFac.GapKatzTao

/-!
# Frostman constants multiply along a chain of scales

This is the cancellation step of GWZ Lemma 7.7(A).  Along a chain of grid scales
`1 = σ₀ ≥ σ₁ ≥ … ≥ σ_{J+2} = δ` with consecutive ratio at least `16`, per-gap Frostman bounds
`C_F(𝕋_{σ_{m+1}∣σ_m}[i₁], T_{i₁}^{(σ_m)}) ≤ X_m` (valid for every anchor `i₁ ∈ s`) compose:

`C_F(𝕋[i₀; σ₁], T_{i₀}^{(σ₁)}) ≤ C ^ (J+2) · ∏ m, X m`

with `C` quantified before `δ` and depending only on the ambient dimension, on `J`, on the
uniformity constant `Cu` and on the fibre-comparability constant `Cf`.  Every density factor
cancels, which is what makes the loss `δ`-independent; both alternative (i) and part (ii)-1 of
Lemma 7.7(A) are read off from this statement.

## How the cancellation happens

Three multiplicities have to meet and annihilate.

* `isKatzTao_gapNode_of_isFrostmanIn` turns each per-gap Frostman bound into *node* Katz–Tao data
  `Δ_m = X_m · G · (N_{σ_m}/N_{σ_{m+1}}) · (σ_{m+1}/σ_m)^{n-1}`.  The ratio of branching numbers
  is what the node reading contributes and the leaf reading does not: it telescopes.
* `maxDensity_fibre_le_prod_of_grid_cuts_nodes` multiplies the `Δ_m` together and reinstates a
  single leaf multiplicity `N_δ`, which cancels the tail of the telescoped ratio, leaving
  `N_{σ₁} · (δ/σ₁)^{n-1}` — the anchor density, up to dimensional constants.
* `branchingN_mul_le_densityIn` identifies that quantity with `Δ(𝕋, T_{i₀}^{(σ₁)})`, the exact
  denominator of the Frostman constant being bounded.  This is the step that needs
  `ComparableFibreCounts`: without it the branching number is only comparable to the leaf count of
  the `4`-fold inflated fibre, and the inflation would not cancel.

The coarse scales above `σ₁` never enter, because the chain of
`maxDensity_fibre_le_prod_of_grid_cuts_nodes` is anchored at the fibre: its coarsest gap carries
the constant `Cu ^ 2`, not a density.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The chain of the engine, read as a bundled hierarchy

The telescoping engine and the bundled hierarchies of `Kakeya/ChainUniform.lean` both read their
chain of scales on `ℕ`, whereas the exported product lemma is stated for a chain on `Fin (J + 3)`.
`finChain` clamps a finite chain to a total function on `ℕ`, so a bundle along the clamped chain is
exactly the input the engine consumes; `chainUniformAt` in addition recovers from such a bundle the
per-scale data `Tube.IsUniformAtScale`, at the squared constant, for consumers that still read
uniformity one scale at a time. -/

/-- A chain of `J + 3` scales, extended to all of `ℕ` by clamping at the last index. -/
def finChain {J : ℕ} (σ : Fin (J + 3) → NNReal) (k : ℕ) : NNReal :=
  σ ⟨min k (J + 2), by omega⟩

/-- On the indices of the chain itself, the clamped extension is the chain. -/
theorem finChain_coe {J : ℕ} (σ : Fin (J + 3) → NNReal) (k : Fin (J + 3)) :
    finChain σ (k : ℕ) = σ k :=
  congrArg σ (Fin.ext (min_eq_left (Nat.lt_succ_iff.mp k.isLt)))

/-- The clamped extension at the first index. -/
theorem finChain_zero {J : ℕ} (σ : Fin (J + 3) → NNReal) : finChain σ 0 = σ 0 :=
  congrArg σ (Fin.ext (by simp))

/-- The clamped extension at the anchor index. -/
theorem finChain_one {J : ℕ} (σ : Fin (J + 3) → NNReal) : finChain σ 1 = σ 1 :=
  congrArg σ (Fin.ext (by simp))

/-- The clamped extension at the last index of the chain. -/
theorem finChain_last {J : ℕ} (σ : Fin (J + 3) → NNReal) :
    finChain σ (J + 2) = σ (Fin.last (J + 2)) :=
  congrArg σ (Fin.ext (by simp))

/-- Clamping preserves antitonicity, so a decreasing finite chain extends to a decreasing chain
on `ℕ`. -/
theorem finChain_antitone {J : ℕ} {σ : Fin (J + 3) → NNReal} (hanti : Antitone σ) :
    Antitone (finChain σ) :=
  fun _ _ hkl => hanti (Fin.mk_le_mk.mpr (min_le_min hkl le_rfl))

/-- A telescoping product of two families of ratios in `NNReal`.  This is the algebraic identity
behind the cancellation: the branching numbers enter as `a`, the powers of the scales as `b`. -/
private theorem prod_div_telescope {M : ℕ} (a b : Fin (M + 1) → NNReal)
    (ha : ∀ k, a k ≠ 0) (hb : ∀ k, b k ≠ 0) :
    (∏ m : Fin M, (a m.castSucc / a m.succ) * (b m.succ / b m.castSucc))
      = (a 0 / a (Fin.last M)) * (b (Fin.last M) / b 0) := by
  induction M with
  | zero => simp [ha 0, hb 0]
  | succ M ih =>
    have key := ih (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) (fun _ => ha _) (fun _ => hb _)
    simp only [Function.comp_apply, ← Fin.succ_castSucc, Fin.castSucc_zero] at key
    rw [Fin.prod_univ_castSucc, key, Fin.succ_last]
    field_simp [ha, hb]

/-- The dimensional and uniformity part of the per-gap Katz–Tao constant produced by
`isKatzTao_gapNode_of_isFrostmanIn`: two tube-volume comparison ratios, the uniformity powers of
the two counting steps, the re-anchoring count of the container inflation, and the `2 ^ n` of the
test-body thickening. -/
noncomputable abbrev gapProdConst (n : ℕ) (Cu : NNReal) : NNReal :=
  Cu ^ 4 * Tube.volume_le.C n ^ 2 * fibrePackConst n * 2 ^ n / Tube.le_volume.c n ^ 2

/-- The algebraic core of the per-gap constant of `isKatzTao_gapNode_of_isFrostmanIn`: against the
leaf multiplicity `Nb` and one tube-volume comparison factor `c`, the branching ratio `Na / Nb`
recombines and the `c ^ 2` carried by `gapProdConst` cancels down to a single `c`. -/
private lemma div_sq_mul_ratio_mul_eq (K Na Nb c σa σb : NNReal) (p : ℕ)
    (hc : c ≠ 0) (hNb : Nb ≠ 0) (hσa : σa ≠ 0) :  -- (extracted by Fuse golfer)
    K / c ^ 2 * (Na / Nb) * (σb ^ p / σa ^ p) * (Nb * c) = K * Na * σb ^ p / (c * σa ^ p) := by
  field_simp

/-- **Per-gap node Katz–Tao data straight from the per-gap Frostman bound.**  Composing
`isKatzTao_gapFibre_of_isFrostmanIn` with `isKatzTao_gapNodeIndex_of_isKatzTao_gapFibre`: the leaf
reading contributes the coarse branching number `N_{σa}` and the node reading divides by the fine
one, so the datum carries the *ratio* `N_{σa}/N_{σb}`, which is what telescopes along the chain. -/
theorem isKatzTao_gapNode_of_isFrostmanIn {ι : Type*} {δ Cu : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
    (𝒰 : ChainUniformTubeSet s T N σ Cu) (hCu : 1 ≤ Cu)
    {ka kb : ℕ} (hka : ka ≤ N) (hkb : kb ≤ N)
    (hσa : 0 < σ ka) (hδσb : δ ≤ σ kb) (hσb1 : σ kb ≤ 1) (hσb2 : 2 * σ kb ≤ σ ka)
    (hNb : 𝒰.branchingN kb ≠ 0) {X : ENNReal}
    (hFr : ∀ i₁ ∈ s, ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (σ ka) i₁)
        (fibreBodies T (σ kb)) ((T i₁).rescale (2 * σ ka)).toConvexSpaceBody X)
    {i₁ : ι} (hi₁ : i₁ ∈ s) :
    ConvexSpaceBody.IsKatzTao (gapNodeIndex 𝒰 kb i₁ (5 * σ ka))
      (fun j => (𝒰.cover.tube kb j).toConvexSpaceBody)
      (X * ((gapProdConst (Module.finrank ℝ E) (Cu ^ 2)
              * (𝒰.branchingN ka / 𝒰.branchingN kb)
              * (σ kb ^ (Module.finrank ℝ E - 1) / σ ka ^ (Module.finrank ℝ E - 1)) : NNReal)
            : ENNReal)) := by
  set σa := σ ka with hσadef
  set σb := σ kb with hσbdef
  set n := Module.finrank ℝ E with hn
  set p := n - 1 with hp
  set c := Tube.le_volume.c n with hc
  set Cv := Tube.volume_le.C n with hCv
  set PK := fibrePackConst n with hPK
  set Na := 𝒰.branchingN ka with hNa
  set Nb := 𝒰.branchingN kb with hNb'
  have hc_pos : 0 < c := Tube.le_volume.c_pos n
  have hc_nonzero_nn : c ≠ 0 := hc_pos.ne'
  have hσa_ne_zero : σa ≠ 0 := hσa.ne'
  have hA_nonzero_nn : c * σa ^ p ≠ 0 := mul_ne_zero hc_nonzero_nn (pow_ne_zero p hσa_ne_zero)
  set Y : ENNReal := X * (((Cu ^ 2) ^ 2 * Na * Cv * σb ^ p / (c * σa ^ p) : NNReal) : ENNReal)
    with hYdef
  have hY : X * (((Cu : ENNReal) ^ 2) ^ 2 * (Na : ENNReal)
      * ((Cv : ENNReal) * (σb : ENNReal) ^ p))
    ≤ Y * ((c : ENNReal) * (σa : ENNReal) ^ p) := by
    have h_eq_nn : (((Cu ^ 2) ^ 2 * Na * Cv * σb ^ p / (c * σa ^ p) : NNReal)
        * (c * σa ^ p : NNReal) : NNReal)
      = ((Cu ^ 2) ^ 2 * Na * Cv * σb ^ p : NNReal) :=
      div_mul_cancel₀ _ hA_nonzero_nn
    refine le_of_eq ?_
    calc X * (((Cu : ENNReal) ^ 2) ^ 2 * (Na : ENNReal) * ((Cv : ENNReal) * (σb : ENNReal) ^ p))
        = X * ((((Cu ^ 2) ^ 2 * Na * Cv * σb ^ p / (c * σa ^ p) : NNReal)
            * (c * σa ^ p : NNReal) : NNReal) : ENNReal) := by
          rw [h_eq_nn]
          simp only [ENNReal.coe_mul, ENNReal.coe_pow]
          ring
      _ = Y * ((c : ENNReal) * (σa : ENNReal) ^ p) := by
          rw [hYdef]
          simp only [ENNReal.coe_mul, ENNReal.coe_pow]
          ring
  have hKT : ∀ i₂ ∈ s,
      ConvexSpaceBody.IsKatzTao (fibreIndex s T σb σa i₂) (fibreBodies T σb) Y := by
    intro i₂ hi₂
    have hσbσa : σb ≤ σa := le_trans (by rw [two_mul]; exact le_add_self) hσb2
    exact isKatzTao_gapFibre_of_blockFrostman 𝒰 hCu hka hδσb hσb1 hσa hσbσa hY i₂ (hFr i₂ hi₂)
  set Δ : ENNReal :=
    X * ((gapProdConst n (Cu ^ 2) * (Na / Nb) * (σb ^ p / σa ^ p) : NNReal) : ENNReal) with hΔdef
  have h_eq_nn : (gapProdConst n (Cu ^ 2) * (Na / Nb) * (σb ^ p / σa ^ p) : NNReal)
      * (Nb * c : NNReal)
    = Cv * (Cu ^ 2) ^ 2 * PK * (2 : NNReal) ^ n
        * (((Cu ^ 2) ^ 2 * Na * Cv * σb ^ p / (c * σa ^ p)) : NNReal) := by
    rw [show (gapProdConst n (Cu ^ 2) : NNReal)
        = (Cu ^ 2) ^ 4 * Cv ^ 2 * PK * 2 ^ n / c ^ 2 from rfl,
      div_sq_mul_ratio_mul_eq _ Na Nb c σa σb p hc_nonzero_nn hNb hσa_ne_zero,
      ← mul_div_assoc]
    congr 1
    ring
  have h_eq_enn : Δ * ((Nb : ENNReal) * (c : ENNReal))
    = (Cv : ENNReal) * ((Cu : ENNReal) ^ 2) ^ 2 * (PK : ENNReal) * ((2 : ENNReal) ^ n) * Y := by
    calc
      Δ * ((Nb : ENNReal) * (c : ENNReal))
          = X * ((((gapProdConst n (Cu ^ 2) * (Na / Nb) * (σb ^ p / σa ^ p) : NNReal)
              * (Nb * c : NNReal) : NNReal) : ENNReal)) := by
        rw [hΔdef]
        simp only [ENNReal.coe_mul]
        ring
      _ = X * ((Cv * (Cu ^ 2) ^ 2 * PK * (2 : NNReal) ^ n
            * (((Cu ^ 2) ^ 2 * Na * Cv * σb ^ p / (c * σa ^ p)) : NNReal) : NNReal) : ENNReal) := by
        rw [h_eq_nn]
      _ = (Cv : ENNReal) * ((Cu : ENNReal) ^ 2) ^ 2 * (PK : ENNReal) * ((2 : ENNReal) ^ n) * Y := by
        rw [hYdef]
        simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]
        ring
  exact isKatzTao_gapNodeIndex_of_isKatzTao_gapFibre 𝒰 hCu hkb hσa hδσb hσb1 hσb2 h_eq_enn.ge hKT
    hi₁

/-- **The branching number at a scale is the anchor density there.**  Combining
`branchingN_le_mul_card_fibreIndex_of_comparable` with the count-to-density transfer
`card_fibre_mul_le_densityIn`.  This is the denominator of the Frostman constant of the fibre, and
what is left over once the telescoped product has absorbed the leaf multiplicity. -/
theorem branchingN_mul_le_densityIn {ι : Type*} {δ Cu Cf : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
    (𝒰 : ChainUniformTubeSet s T N σ Cu) (hCu : 1 ≤ Cu) {k : ℕ} (hk : k ≤ N)
    (hρ : 0 < σ k) (hδρ : 2 * δ ≤ σ k) (hρ1 : σ k ≤ 1)
    (hcmp : ∀ i₁ ∈ s, ∀ i₂ ∈ s,
      ((fibreIndex s T δ (σ k) i₁).card : NNReal)
        ≤ Cf * ((fibreIndex s T δ (σ k) i₂).card : NNReal))
    {i₀ : ι} (hi₀ : i₀ ∈ s) :
    (𝒰.branchingN k : ENNReal)
        * ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ ((fibrePackConst (Module.finrank ℝ E) * Cu ^ 2 * Cf
              * (6 * Tube.volume_le.C (Module.finrank ℝ E)) : NNReal) : ENNReal)
          * ((σ k : ENNReal) ^ (Module.finrank ℝ E - 1)
              * Kakeya.densityIn s (fun i => (T i).toConvexSpaceBody)
                  ((T i₀).rescale (σ k)).toConvexSpaceBody) := by
  set ρ := σ k with hρdef
  set n := Module.finrank ℝ E with hn
  set p := n - 1 with hp
  set c := Tube.le_volume.c n with hc
  set Cv := Tube.volume_le.C n with hCv
  set PK := fibrePackConst n with hPK
  set F := fibreIndex s T δ ρ i₀ with hF
  set D := Kakeya.densityIn s (fun i => (T i).toConvexSpaceBody)
    ((T i₀).rescale ρ).toConvexSpaceBody with hD
  have hρ5 : ρ ≤ 5 := hρ1.trans (by norm_num : (1 : NNReal) ≤ 5)
  have hcard_ENN : (𝒰.branchingN k : ENNReal)
      ≤ (PK : ENNReal) * (Cu : ENNReal) ^ 2 * (Cf : ENNReal) * ((F.card : ENNReal)) := by
    have hcard_cast : (𝒰.branchingN k : ENNReal)
        ≤ ((PK * (Cu ^ 2 * (Cf * ((F.card : NNReal)))) : NNReal) : ENNReal) := by
      exact_mod_cast branchingN_le_mul_card_fibreIndex_of_comparable 𝒰 hCu hk hρ hδρ hcmp hi₀
    refine hcard_cast.trans_eq ?_
    push_cast
    ring
  have hfibre_ENN : ((F.card : ENNReal)) * ((c : ENNReal) * ((δ : ENNReal) ^ p))
      ≤ D * (((6 * Cv : NNReal) : ENNReal) * ((ρ : ENNReal) ^ p)) :=
    card_fibre_mul_le_densityIn (s := s) (T := T) (δ := δ) hρ5 i₀
  calc
    (𝒰.branchingN k : ENNReal) * ((c : ENNReal) * ((δ : ENNReal) ^ p))
        ≤ ((PK : ENNReal) * (Cu : ENNReal) ^ 2 * (Cf : ENNReal) * ((F.card : ENNReal)))
            * ((c : ENNReal) * ((δ : ENNReal) ^ p)) := mul_le_mul_left hcard_ENN _
    _ = (PK : ENNReal) * (Cu : ENNReal) ^ 2 * (Cf : ENNReal)
        * (((F.card : ENNReal)) * ((c : ENNReal) * ((δ : ENNReal) ^ p))) := by ring
    _ ≤ (PK : ENNReal) * (Cu : ENNReal) ^ 2 * (Cf : ENNReal)
        * (D * (((6 * Cv : NNReal) : ENNReal) * ((ρ : ENNReal) ^ p))) :=
      mul_le_mul_right hfibre_ENN _
    _ = ((PK * Cu ^ 2 * Cf * (6 * Cv) : NNReal) : ENNReal)
        * (((ρ : ENNReal) ^ p) * D) := by
      push_cast
      ring

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The telescoped product of the per-gap Katz–Tao data.**  The coarsest gap contributes `Cu ^ 2`;
every other gap contributes its Frostman bound `X m` times a ratio of consecutive branching numbers
and a ratio of consecutive scale powers.  Both ratios telescope, leaving only the endpoints, which
is the whole reason the loss is `δ`-independent. -/
theorem prod_gapDelta_eq {J : ℕ} {ι : Type*} {δ Cu : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    (σ : ℕ → NNReal) (𝒰 : ChainUniformTubeSet s T (J + 2) σ Cu)
    (hN : ∀ k ≤ J + 2, 𝒰.branchingN k ≠ 0) (hσ : ∀ k ≤ J + 2, σ k ≠ 0)
    (X : Fin (J + 2) → ENNReal) :
    (∏ m : Fin (J + 2), (if m = 0 then ((Cu ^ 2 : NNReal) : ENNReal) else
        X m * ((gapProdConst (Module.finrank ℝ E) (Cu ^ 2)
          * (𝒰.branchingN (m.castSucc : ℕ) / 𝒰.branchingN (m.succ : ℕ))
          * (σ (m.succ : ℕ) ^ (Module.finrank ℝ E - 1)
              / σ (m.castSucc : ℕ) ^ (Module.finrank ℝ E - 1))
          : NNReal) : ENNReal)))
      = ((Cu ^ 2 : NNReal) : ENNReal) * (∏ m : Fin (J + 1), X m.succ)
          * ((gapProdConst (Module.finrank ℝ E) (Cu ^ 2) ^ (J + 1)
              * (𝒰.branchingN 1 / 𝒰.branchingN (J + 2))
              * (σ (J + 2) ^ (Module.finrank ℝ E - 1)
                  / σ 1 ^ (Module.finrank ℝ E - 1)) : NNReal) : ENNReal) := by
  set n := Module.finrank ℝ E with hn
  set p := n - 1 with hp
  set G := gapProdConst n (Cu ^ 2) with hG
  rw [Fin.prod_univ_succ, if_pos rfl]
  simp only [Fin.succ_ne_zero, if_false]
  rw [Finset.prod_mul_distrib, ← ENNReal.ofNNReal_finsetProd]
  set a : Fin (J + 2) → NNReal := fun k => 𝒰.branchingN ((k : ℕ) + 1) with ha
  set b : Fin (J + 2) → NNReal := fun k => σ ((k : ℕ) + 1) ^ p with hb
  have ha0 : ∀ k, a k ≠ 0 := fun k => hN ((k : ℕ) + 1) (by have := k.isLt; omega)
  have hb0 : ∀ k, b k ≠ 0 := fun k =>
    pow_ne_zero p (hσ ((k : ℕ) + 1) (by have := k.isLt; omega))
  have h_term (m : Fin (J + 1)) :
      (G * (𝒰.branchingN ((m.succ).castSucc : ℕ) / 𝒰.branchingN ((m.succ).succ : ℕ))
        * (σ ((m.succ).succ : ℕ) ^ p / σ ((m.succ).castSucc : ℕ) ^ p) : NNReal) =
      G * ((a m.castSucc / a m.succ) * (b m.succ / b m.castSucc)) := by
    simp [a, b, mul_assoc]
  rw [Finset.prod_congr rfl fun m _ => h_term m,
    Finset.prod_mul_distrib, prod_div_telescope a b ha0 hb0, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  have ha0_val : a 0 = 𝒰.branchingN 1 := by simp [a]
  have ha_last_val : a (Fin.last (J + 1)) = 𝒰.branchingN (J + 2) := by simp [a]
  have hb0_val : b 0 = σ 1 ^ p := by simp [b]
  have hb_last_val : b (Fin.last (J + 1)) = σ (J + 2) ^ p := by simp [b]
  rw [ha0_val, ha_last_val, hb0_val, hb_last_val]
  simp only [mul_assoc]

end MultiScaleFac

end Kakeya

