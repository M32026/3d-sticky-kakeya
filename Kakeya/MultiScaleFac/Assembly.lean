/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ChainUniform
public import Kakeya.MultiScaleFac.Interp
public import Kakeya.MultiScaleFac.Stopping

/-!
# Assembling the dividing-scales dichotomy (GWZ Lemma 7.7(A))

This file joins the three ingredients of GWZ Lemma 7.7(A)
(`Kakeya.MultiScaleFac.dividingScalesFrostman`, in `Kakeya.MultiScaleFac`) into its two
alternatives:

* the stopping time and its cut sets (`Kakeya.MultiScaleFac.Stopping`),
* the product bound along a cut chain
  (`MultiScaleFac.frostmanConstant_fibre_le_prod_of_cuts`, itself built on
  `MultiScaleFac.frostmanConstant_fibre_le_prod`),
* the discrete-to-arbitrary-scale interpolation (`Kakeya.MultiScaleFac.Interp`).

## Alternative (i): the telescoping branch

`prod_cutChainFactor_eq` is the arithmetic core: the per-gap factors of the chain telescope,
`∏_m (σ_m/σ_{m+1})^ζ = (σ_0/σ_{J+2})^ζ = δ^{-ζ}`.  Composed with the product bound this gives
`frostmanConstant_gridScale_le_of_cuts`, a bound at *every grid scale* `σ_k` with the sharp
exponent `(σ_k/δ)^ζ` — only the blocks below `k` telescope.  Feeding those grid-scale bounds
into `isFrostmanAtEveryScale_of_grid_bounds` (which is the interpolation of
`Kakeya.MultiScaleFac.Interp` applied along the bracketing of `gridScale_bracket`) produces
alternative (i), `isFrostmanAtEveryScale_of_cuts`.

The loss is `ζ ≤ ε` from the telescoping plus `(n-1)ε = 2ε` from the interpolation at `n = 3`,
so `3ε`, comfortably inside the `5ε` that the dichotomy asserts.

## Alternative (ii): the long-block branch

`dividingScales_of_long_block` reads the dividing scales off a long adjacent block `(a,b)` of the
cut set: `τ = σ_b`, `θ = σ_a`.  The separation `τ ≤ δ^ε θ` is the length bound
`b - a > ⌈εN⌉` of `IsLongBlock`; (ii)-1 is `frostmanConstant_cutScale_le_of_cuts` at `k = b`;
(ii)-2 is the block bound (invariant (I1)) of that very block; (ii)-3 is the negation of the
stopping test (invariant (I2)) at the grid scales, raised to arbitrary real scales by
`frostmanConstant_interp_lower`.

## The degenerate cut set

`MultiScaleFac.frostmanConstant_fibre_le_prod` consumes a chain `Fin (J+3)`, so it needs at least
three scales, whereas the stopping time may well return the two-element cut set `S = {0, N}`
(nothing was ever cut).  That case is not a gap: `adjacent_of_card_eq_two` shows `(0,N)` is then
the unique adjacent block and `isLongBlock_zero_right` shows it is long (its length `N` exceeds
`⌈εN⌉ = ⌈√N⌉` for `N ≥ 16`), so invariant (I2) forces the stopping test to fail and
`dividingScales_of_long_block` applies — with `τ = σ_N = δ`, for which (ii)-1 is vacuous.  Only
the branch that needs a chain of three or more scales ever assumes `3 ≤ S.card`.

## Interface note

`dividingScales_of_long_block` takes invariant (I1) at exponent `η m` and invariant (I2) at the
*different* exponent `η (m+1)`.  That is exactly what `MultiScaleFac.exists_maximal_cuts` delivers:
the stopping time's invariant at a stage with `m+1` blocks is the block bound at `η m`, while the
test that would condition the next split is run at `η (m+1)`.  No separate two-exponent variant is
needed.

The shortness hypothesis on `frostmanConstant_gridScale_le_of_cuts` and
`isFrostmanAtEveryScale_of_cuts` is not cosmetic.  Telescoping alone controls the fibre Frostman
constant only at the *cut* scales; a grid scale `k` lying strictly inside a block is reached by
`StickyKakeya.exists_blockFrostman_truncate`, which shrinks the block's parent from `σ_a` to
`σ_k`, and that step is affordable only when the block ratio `σ_a/σ_b` is at most `δ^{-ε}`, i.e.
when the block is short.  A long block is precisely where that fails, and that is the dichotomy:
no shortness, no alternative (i).  The residual `δ^{-εζ}` appears explicitly in the conclusion of
`frostmanConstant_gridScale_le_of_cuts`, since it is not `δ`-independent and cannot be hidden in
a constant.

## Constants

Every block bound carries an explicit multiplicative constant (`MultiScaleFac.BlockFrostman`'s
`C` argument), because the two steps that move a block bound between sub-blocks — the coarse-side
`MultiScaleFac.BlockRestrictStep` and the fine-side
`StickyKakeya.exists_blockFrostman_truncate` — each lose a `δ`-independent factor.  Throughout
this file the block constant is the parameter `Cb`, quantified before the existential error
constant `C` so that `C` may absorb it, and the stopping-time test constant is `Ct`, quantified
inside because it occurs under a negation and therefore only needs `1 ≤ Ct`.

`⪅` does not appear: every bound carries an explicit constant quantified before `δ`, as required
by.

## The parameter `N` in this file is the grid length

Every theorem below uses `N` only as the length of the scale grid `gridScale δ N ·`: it indexes
the grid, bounds the cut indices, and fixes the `16`-separation `δ ≤ 16^{-N}`.  It is *not* the
bound on the number of stopping-time steps, and it is no longer tied to the sampling exponent `ε`
by any equation.  What the proofs actually need of the pair `(ε, N)` is recorded hypothesis by
hypothesis: `0 < ε`, an upper bound on `ε` (`ε ≤ 1` or `ε ≤ 1/64`), the fineness threshold
`1 ≤ ε² N`, and `16 ≤ N`.  All of these are satisfiable with `ε` fixed and `N` taken large, which
is what lets a caller run the grid at a `δ`-dependent length while `ε = 1/√N₀` is governed by a
separate step bound `N₀`.  The classical choice `N = N₀` makes `1 ≤ ε² N` an equality.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

universe u

/-! ### Telescoping the chain factors -/

/-- **The length of a short block, as a real bound.**  A block that is not long has
`b - a ≤ ⌈εM⌉`, so an interior index `k` satisfies `k - a ≤ ⌈εM⌉ - 1 ≤ εM`, where `M` is the
grid length.  This is the only place where shortness enters the exponent accounting of
alternative (i); nothing here links `ε` to `M`. -/
theorem sub_le_of_not_isLongBlock {M : ℕ} {ε : ℝ}
    {a k b : ℕ} (hshort : ¬ IsLongBlock M ε a b)
    (hak : a < k) (hkb : k < b) :
    ((k - a : ℕ) : ℝ) ≤ ε * (M : ℝ) := by
  have hshort' : b ≤ ⌈ε * (M : ℝ)⌉₊ + a := by
    dsimp [IsLongBlock] at hshort
    exact le_of_not_gt hshort
  have hlt : (k - a : ℕ) < ⌈ε * (M : ℝ)⌉₊ := by
    omega
  exact le_of_lt (Nat.lt_ceil.mp hlt)

/-- **The deflation exponent fits the budget.**  With `n = 3`, a grid of length `M` fine enough
that `1 ≤ ε² M`, and `d ≤ εM`, the exponent `((n+1)d + 2n)/M` of
`frostmanConstant_gridScale_deflate` is at most `4ε + 6ε²`.  The classical choice `ε = 1/√M`
makes the fit exact: `4εM/M = 4ε` and `6/M = 6ε²`; a longer grid only helps. -/
theorem deflate_exponent_le {M : ℕ} (hM : 0 < M) {ε : ℝ} (hεM : 1 ≤ ε ^ 2 * (M : ℝ))
    {d : ℝ} (_hd0 : 0 ≤ d) (hd : d ≤ ε * (M : ℝ)) :
    (((3 : ℝ) + 1) * d + 2 * 3) / (M : ℝ) ≤ 4 * ε + 6 * ε ^ 2 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  norm_num
  rw [div_le_iff₀ hMpos]
  nlinarith [hd, hεM]

/-- **Every non-cut grid index lies inside a unique adjacent block.**  If `k ≤ N` is not itself a
cut, the largest cut below it and the smallest cut above it form an adjacent pair straddling `k`;
both exist because `0` and `N` are cuts. -/
theorem exists_adjacent_containing {S : Finset ℕ} {N k : ℕ} (h0 : 0 ∈ S) (hNS : N ∈ S)
    (hk : k ≤ N) (hkS : k ∉ S) :
    ∃ a ∈ S, ∃ b ∈ S, a < k ∧ k < b ∧ (∀ x ∈ S, ¬(a < x ∧ x < b)) := by
  classical
  let L : Finset ℕ := S.filter (fun x => x < k)
  let R : Finset ℕ := S.filter (fun x => k < x)
  have hk0 : k ≠ 0 := by
    intro hk0
    subst k
    exact hkS h0
  have h0k : 0 < k := by omega
  have hkN : k ≠ N := by
    intro hkN
    subst k
    exact hkS hNS
  have hkNlt : k < N := lt_of_le_of_ne hk hkN
  have hLne : L.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp [L]
    rw [Finset.mem_filter]
    exact ⟨h0, h0k⟩
  have hRne : R.Nonempty := by
    refine ⟨N, ?_⟩
    dsimp [R]
    rw [Finset.mem_filter]
    exact ⟨hNS, hkNlt⟩
  let a : ℕ := L.max' hLne
  let b : ℕ := R.min' hRne
  have haL : a ∈ L := by
    dsimp [a]
    exact Finset.max'_mem L hLne
  have hbR : b ∈ R := by
    dsimp [b]
    exact Finset.min'_mem R hRne
  have haS : a ∈ S := by
    exact (Finset.mem_filter.mp haL).1
  have hbS : b ∈ S := by
    exact (Finset.mem_filter.mp hbR).1
  have hak : a < k := by
    exact (Finset.mem_filter.mp haL).2
  have hkb : k < b := by
    exact (Finset.mem_filter.mp hbR).2
  refine ⟨a, haS, b, hbS, hak, hkb, ?_⟩
  intro x hxS hxab
  have hxk : x ≠ k := by
    intro hxk
    subst x
    exact hkS hxS
  have hxlt_or_gt : x < k ∨ k < x := by omega
  rcases hxlt_or_gt with hxlt | hkgt
  · have hxL : x ∈ L := by
      dsimp [L]
      rw [Finset.mem_filter]
      exact ⟨hxS, hxlt⟩
    have hxle : x ≤ a := by
      simpa [a] using Finset.le_max' L x hxL
    exact (not_lt_of_ge hxle) hxab.1
  · have hxR : x ∈ R := by
      dsimp [R]
      rw [Finset.mem_filter]
      exact ⟨hxS, hkgt⟩
    have hbx : b ≤ x := by
      simpa [b] using Finset.min'_le R x hxR
    exact (not_lt_of_ge hbx) hxab.2

/-- **The real ratio of two grid scales is an explicit negative power of `δ`.**  The real-valued
counterpart of `gridScale_div_gridScale`, with the exponent gap supplied in already-normalised
form. -/
private lemma coe_gridScale_div_eq {δ : NNReal} (hδ : 0 < δ) (N a b : ℕ) {c : ℝ}
    (hc : (b : ℝ) - (a : ℝ) = c) :
    (gridScale δ N a : ℝ) / (gridScale δ N b : ℝ) = (δ : ℝ) ^ (-(c / (N : ℝ))) := by
  rw [← NNReal.coe_div, gridScale_div_gridScale hδ N a b, NNReal.coe_rpow, hc]
  -- (extracted by Fuse golfer)

section Geometry

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Alternative (i): from the cut set to Frostman at every scale -/

/-- **Deflating the anchor along the grid.**  The fibre Frostman bound at the coarse grid anchor
`σ_a` implies the bound at any finer grid anchor `σ_{a+d}`, at the cost of `δ^{-((n+1)d + 2n)/N}`.
The constant is quantified *before* the grid length `N`, so a single `Cd` serves every grid
length. -/
theorem frostmanConstant_gridScale_deflate_uniform (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ Cd : NNReal, 1 ≤ Cd ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N Cu →
      ∀ a d : ℕ, a + d + 2 ≤ N → ∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N (a + d)) i₀)
            (fibreBodies T δ) ((T i₀).rescale (gridScale δ N (a + d))).toConvexSpaceBody
          ≤ (Cd : ENNReal) *
              ENNReal.ofReal ((δ : ℝ) ^
                (-(((Module.finrank ℝ E : ℝ) + 1) * (d : ℝ)
                    + 2 * (Module.finrank ℝ E : ℝ)) / (N : ℝ))) *
              ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N a) i₀)
                (fibreBodies T δ) ((T i₀).rescale (gridScale δ N a)).toConvexSpaceBody := by
  classical
  let n : ℕ := Module.finrank ℝ E
  let Cbase : NNReal := fibreFrostmanConst n * (2 * (25 : NNReal) ^ (2 * n) * (Cu ^ 2 : NNReal) ^ 3)
  let Cd : NNReal := max 1 Cbase
  have hCd1 : 1 ≤ Cd := le_max_left _ _
  have hCbase_le_Cd : Cbase ≤ Cd := le_max_right _ _
  refine ⟨Cd, hCd1, ?_⟩
  intro N hN ι δ hδ hδ1 hδ0 s T hball hu a d had i₀ hi₀
  let σ : ℕ → NNReal := fun k => gridScale δ N k
  have hδposR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδnonneg : 0 ≤ (δ : ℝ) := hδposR.le
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hn1 : 1 ≤ n := Module.finrank_pos (R := ℝ) (M := E)
  have hσpos : ∀ k, 0 < σ k := fun k => gridScale_pos hδ N k
  have hσantitone : ∀ k l, k ≤ l → σ l ≤ σ k := fun k l hkl => gridScale_antitone hδ hδ1 N hkl
  have hadN : a + d + 1 < N := by omega
  have hσad_le_σa : σ (a + d) ≤ σ a := hσantitone a (a + d) (by omega)
  have hσad1_le_σa : σ (a + d + 1) ≤ σ a := hσantitone a (a + d + 1) (by omega)
  have hδle_σad : δ ≤ σ (a + d) := by
    rw [← gridScale_self δ hN]; exact hσantitone (a + d) N (by omega)
  have hσa_le_one : σ a ≤ 1 := gridScale_le_one hδ1 N a
  have hu_base : Tube.IsUniformAtScale s T (σ (a + d + 1)) (Cu ^ 2) :=
    hu.toChain.uniformAt hCu hadN.le
  have h2δ : 2 * δ ≤ σ (a + d + 1) := by
    rw [← gridScale_self δ hN]
    exact (mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 16) zero_le).trans
      (sixteen_mul_gridScale_le hδ hδ1 hδ0 (a := a + d + 1) (b := N) hadN le_rfl)
  have h8 : 8 * σ (a + d + 1) ≤ σ (a + d) :=
    (mul_le_mul_of_nonneg_right (by norm_num : (8 : NNReal) ≤ 16) zero_le).trans
      (sixteen_mul_gridScale_succ_le hδ hδ0 (by omega : a + d < N))
  have hcard_le8 : (fibreIndex s T δ (8 * σ (a + d + 1)) i₀).card
      ≤ (fibreIndex s T δ (σ (a + d)) i₀).card :=
    Finset.card_le_card (fibreIndex_subset_of_anchor_le (s := s) (T := T) (σ := δ)
      (ρ := 8 * σ (a + d + 1)) (ρ' := σ (a + d)) h8 i₀)
  let K : ℝ := 2 * (25 : ℝ) ^ (2 * n) * ((Cu ^ 2 : NNReal) : ℝ) ^ 3
  let R1 : ℝ := (σ a : ℝ) / (σ (a + d + 1) : ℝ)
  have hKR1 : (0 : ℝ) ≤ K * R1 ^ (2 * n) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
        (pow_nonneg (Cu ^ 2 : NNReal).coe_nonneg 3))
      (pow_nonneg (div_nonneg (σ a).coe_nonneg (σ (a + d + 1)).coe_nonneg) _)
  have hcount' : ((fibreIndex s T δ (σ a) i₀).card : ℝ)
      ≤ K * R1 ^ (2 * n) * ((fibreIndex s T δ (σ (a + d)) i₀).card : ℝ) :=
    (anchorGraded_of_isUniformAtScale_atScale (E := E) (s := s) (T := T)
      (δ := δ) (σ := δ) (ρ := σ (a + d + 1)) (ρ' := σ a)
      (h := hu_base) (hρ := hσpos (a + d + 1)) (hδσ := le_rfl) (hσρ := h2δ)
      (hρρ' := hσad1_le_σa) hi₀).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard_le8) hKR1)
  have hcard_enn : ((fibreIndex s T δ (σ a) i₀).card : ENNReal)
      ≤ ENNReal.ofReal (K * R1 ^ (2 * n)) * ((fibreIndex s T δ (σ (a + d)) i₀).card : ENNReal) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hKR1]
    exact ENNReal.ofReal_le_ofReal hcount'
  let A : ENNReal := ENNReal.ofReal (K * R1 ^ (2 * n))
  let Bnn : NNReal := (σ (a + d) / σ a) ^ (n - 1)
  let Br : ℝ := (Bnn : ℝ)
  have hsharp := frostmanConstant_fibre_le_of_card_le_sharp (E := E) (ι := ι) (s := s) (T := T)
    (σ := δ) (ρ := σ (a + d)) (ρ' := σ a)
    hδ hδ1 hδle_σad hσad_le_σa hσa_le_one (A := A) ENNReal.ofReal_ne_top hi₀ hcard_enn
  let e : ℝ := -(((n : ℝ) + 1) * (d : ℝ) + 2 * (n : ℝ)) / (N : ℝ)
  let R2 : ℝ := (σ (a + d) : ℝ) / (σ a : ℝ)
  have hR1 : R1 = (δ : ℝ) ^ (-(((d : ℝ) + 1) / (N : ℝ))) :=
    coe_gridScale_div_eq hδ N a (a + d + 1) (by push_cast; ring)
  have hR2 : R2 = (δ : ℝ) ^ (-(-(d : ℝ) / (N : ℝ))) :=
    coe_gridScale_div_eq hδ N (a + d) a (by push_cast; ring)
  have hBr : Br = R2 ^ (n - 1) := rfl
  have hratio : R1 ^ (2 * n) * R2 ^ (n - 1) = (δ : ℝ) ^ e := by
    rw [← Real.rpow_natCast R1, ← Real.rpow_natCast R2, hR1, hR2,
      ← Real.rpow_mul hδnonneg, ← Real.rpow_mul hδnonneg, ← Real.rpow_add hδposR]
    congr 1
    rw [Nat.cast_pred hn1]
    dsimp only [e]
    push_cast
    field_simp
    ring
  have hCK : (Cbase : ℝ) = (fibreFrostmanConst n : ℝ) * K := by
    dsimp only [Cbase, K]
    push_cast
    ring
  have hreal : (fibreFrostmanConst n : ℝ) * (K * R1 ^ (2 * n)) * Br ≤ (Cd : ℝ) * (δ : ℝ) ^ e := by
    have hEq : (fibreFrostmanConst n : ℝ) * (K * R1 ^ (2 * n)) * Br
        = (Cbase : ℝ) * (δ : ℝ) ^ e := by
      rw [hBr, hCK, ← hratio]; ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCbase_le_Cd)
      (Real.rpow_nonneg hδnonneg e)
  have hprod :
      (fibreFrostmanConst n : ENNReal) * ENNReal.ofReal (K * R1 ^ (2 * n)) * (Bnn : ENNReal)
      ≤ (Cd : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ e) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := fibreFrostmanConst n),
      ← ENNReal.ofReal_coe_nnreal (p := Bnn), ← ENNReal.ofReal_coe_nnreal (p := Cd),
      ← ENNReal.ofReal_mul ((fibreFrostmanConst n).coe_nonneg),
      ← ENNReal.ofReal_mul (mul_nonneg (fibreFrostmanConst n).coe_nonneg
        (hKR1 : (0 : ℝ) ≤ K * R1 ^ (2 * n))),
      ← ENNReal.ofReal_mul Cd.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  exact hsharp.trans (mul_le_mul_of_nonneg_right hprod bot_le)

/-- **A grid loss `δ^{-c/N}` fits inside the `ε`-budget once the grid is fine.**  On a grid with
`1/N ≤ ε²` the exponent `c/N` never exceeds `cε²`, so the loss is at most `δ^{-cε²}`. -/
private lemma rpow_neg_div_le_rpow_neg_mul {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N ε : ℝ}
    (hεN : 1 / N ≤ ε ^ 2) {c : ℝ} (hc : 0 ≤ c) :
    δ ^ (-(c / N)) ≤ δ ^ (-(c * ε ^ 2)) :=
  Real.rpow_le_rpow_of_exponent_ge hδ hδ1 <| neg_le_neg <| by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hεN hc
  -- (extracted by Fuse golfer)

/-- **The numeric form of `isFrostmanAtEveryScale_of_grid_bounds`.**  The passage from the grid to
arbitrary scales, stated at the level of `ConvexSpaceBody.frostmanConstant`: a fibre Frostman
bound at every grid scale gives the bound at every `ρ ∈ [δ, 1]`, at the interpolation cost
`δ^{-12ε²}`.  The grid factor `L` is quantified after `δ`, the grid length `N` after `C`. -/
theorem frostmanConstant_allScale_of_grid_bounds_factor (hn : Module.finrank ℝ E = 3) (ε : ℝ)
    (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (N : ℕ), 16 ≤ N → 1 ≤ ε ^ 2 * (N : ℝ) →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N Cu →
      ComparableFibreCounts s T (gridScales δ N) Cu →
      ∀ Lgrid : ENNReal, 1 ≤ Lgrid →
      ∀ ζ : ℝ, 0 ≤ ζ →
      (∀ k ≤ N, ∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N k) i₀)
            (fibreBodies T δ) ((T i₀).rescale (gridScale δ N k)).toConvexSpaceBody
          ≤ Lgrid * ENNReal.ofReal ((δ : ℝ) ^ (-ζ))) →
      ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 → ∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ i₀) (fibreBodies T δ)
            ((T i₀).rescale ρ).toConvexSpaceBody
          ≤ (C : ENNReal) * Lgrid * ENNReal.ofReal ((δ : ℝ) ^ (-(ζ + 12 * ε ^ 2))) := by
  obtain ⟨CInt, hCInt, hInterp⟩ := frostmanConstant_interp_upper (E := E) (Cu ^ 2) (one_le_pow₀ hCu)
  let Ccrude : NNReal :=
    2 * Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)
  let C : NNReal := max CInt Ccrude
  refine ⟨C, hCInt.trans (le_max_left _ _), ?_⟩
  intro N hN hεN ι δ hδ hδ1 hδ0 s T hball huni _hcmp Lgrid hL ζ hζ0 hgrid ρ hρδ hρ1 i₀ hi₀
  have hNpos : 0 < N := Nat.lt_of_lt_of_le (by norm_num) hN
  have hδpos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hεsq : (1 : ℝ) / (N : ℝ) ≤ ε ^ 2 :=
    (div_le_iff₀ (by exact_mod_cast hNpos : (0 : ℝ) < (N : ℝ))).2 hεN
  obtain ⟨k, hkltN, hρlb, hρub⟩ := gridScale_bracket hδ hδ1 hNpos hρδ hρ1
  by_cases hk3 : k ≤ N - 3
  · -- interpolate from the grid scale `σ_k` down to `ρ`, paying `(σ_k/σ_{k+2})^{2n} ≤ δ^{-12ε²}`
    obtain ⟨hk2ltN, hk1N, hk2N, hkN⟩ : k + 2 < N ∧ k + 1 < N ∧ k + 2 ≤ N ∧ k ≤ N := by omega
    have h2σρ₀ : 2 * δ ≤ gridScale δ N (k + 2) := by
      have hsep := sixteen_mul_gridScale_le hδ hδ1 hδ0 hk2ltN le_rfl
      rw [gridScale_self δ hNpos] at hsep
      exact (mul_le_mul' (by norm_num : (2 : NNReal) ≤ 16) le_rfl).trans hsep
    have h8ρ₀ρ' : 8 * gridScale δ N (k + 2) ≤ gridScale δ N (k + 1) :=
      (mul_le_mul' (by norm_num : (8 : NNReal) ≤ 16) le_rfl).trans
        (sixteen_mul_gridScale_succ_le hδ hδ0 hk1N)
    have hb := hInterp hδ hδ1 s T hball δ (gridScale δ N (k + 2)) (gridScale δ N (k + 1)) ρ
      (gridScale δ N k) le_rfl (gridScale_pos hδ N (k + 2)) h2σρ₀ h8ρ₀ρ' hρlb hρub
      (gridScale_le_one hδ1 N k) (huni.toChain.uniformAt hCu hk2N) i₀ hi₀
    have hLle : ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N (k + 2) : ℝ)) ^
        (2 * (Module.finrank ℝ E : ℝ))) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(12 * ε ^ 2))) := by
      rw [coe_gridScale_div_eq (c := 2) hδ N k (k + 2) (by push_cast; ring),
        show (2 * (Module.finrank ℝ E : ℝ)) = 6 by rw [hn]; norm_num,
        ← Real.rpow_mul hδpos.le, show -(2 / (N : ℝ)) * 6 = -(12 / (N : ℝ)) by ring]
      exact ENNReal.ofReal_le_ofReal
        (rpow_neg_div_le_rpow_neg_mul hδpos hδ1 hεsq (by norm_num))
    have hprod : ENNReal.ofReal ((δ : ℝ) ^ (-(12 * ε ^ 2))) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ))
        = ENNReal.ofReal ((δ : ℝ) ^ (-(ζ + 12 * ε ^ 2))) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδpos.le _), ← Real.rpow_add hδpos]
      congr 1
      ring_nf
    have hCC : (CInt : ENNReal) ≤ (C : ENNReal) := ENNReal.coe_le_coe.2 (le_max_left CInt Ccrude)
    refine hb.trans ((mul_le_mul' le_rfl (hgrid k hkN i₀ hi₀)).trans ?_)
    refine (mul_le_mul' (mul_le_mul' hCC hLle) le_rfl).trans (le_of_eq ?_)
    rw [← hprod]
    ring
  · -- the two finest grid cells: the crude bound costs only `(ρ/δ)^{n-1} ≤ δ^{-4ε²}`
    obtain ⟨h2N, hNk⟩ : 2 ≤ N ∧ N - 2 ≤ k := by omega
    have hρδratio : (ρ : ℝ) / (δ : ℝ) ≤ (δ : ℝ) ^ (-(2 / (N : ℝ))) := by
      have hE := coe_gridScale_div_eq (c := 2) hδ N (N - 2) N
        (by rw [Nat.cast_sub h2N]; push_cast; ring)
      rw [gridScale_self δ hNpos] at hE
      rw [← hE]
      exact div_le_div_of_nonneg_right
        (hρub.trans (gridScale_antitone hδ hδ1 N hNk)) hδpos.le
    have hcrude_ratio : (ρ / δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ (δ : ℝ) ^ (-(4 * ε ^ 2)) := by
      rw [show (Module.finrank ℝ E - 1 : ℕ) = 2 by rw [hn]]
      calc
        ((ρ : ℝ) / (δ : ℝ)) ^ (2 : ℕ) ≤ ((δ : ℝ) ^ (-(2 / (N : ℝ)))) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (div_nonneg ρ.coe_nonneg δ.coe_nonneg) hρδratio 2
        _ = (δ : ℝ) ^ (-(4 / (N : ℝ))) := by
          rw [← Real.rpow_natCast ((δ : ℝ) ^ (-(2 / (N : ℝ)))) 2, ← Real.rpow_mul hδpos.le]
          congr 1
          ring
        _ ≤ (δ : ℝ) ^ (-(4 * ε ^ 2)) := rpow_neg_div_le_rpow_neg_mul hδpos hδ1 hεsq (by norm_num)
    have hpowle : (((ρ / δ : NNReal) ^ (Module.finrank ℝ E - 1) : NNReal) : ENNReal)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(4 * ε ^ 2))) := by
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, NNReal.coe_div]
      exact ENNReal.ofReal_le_ofReal hcrude_ratio
    have hDleB : ENNReal.ofReal ((δ : ℝ) ^ (-(4 * ε ^ 2)))
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ζ + 12 * ε ^ 2))) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδpos hδ1
        (neg_le_neg (by linarith only [hζ0, sq_nonneg ε])))
    have hCL : (Ccrude : ENNReal) ≤ (C : ENNReal) * Lgrid :=
      calc (Ccrude : ENNReal) ≤ (C : ENNReal) := ENNReal.coe_le_coe.2 (le_max_right CInt Ccrude)
        _ = (C : ENNReal) * 1 := (mul_one _).symm
        _ ≤ (C : ENNReal) * Lgrid := mul_le_mul' le_rfl hL
    refine (frostmanConstant_fibre_le_ratio_pow (σ := δ) (ρ := ρ) hδ hρδ hρ1 (i₀ := i₀) hi₀).trans
      (le_of_eq_of_le (ENNReal.coe_mul ..) ?_)
    exact (mul_le_mul' le_rfl hpowle).trans (mul_le_mul' hCL hDleB)

/-- **From grid scales to all scales: alternative (i) of GWZ Lemma 7.7(A).**

The fibre Frostman bound `C₀ · δ^{-ζ}` at every grid scale yields
`StickyKakeya.IsFrostmanAtEveryScale` with the extra interpolation loss `δ^{-12ε²}` at `n = 3`.
A caller holding the hierarchy should prefer the node reading of `MultiScaleFac/Ports.lean`. -/
theorem isFrostmanAtEveryScale_of_grid_bounds_factor (hn : Module.finrank ℝ E = 3) (ε : ℝ)
    (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (N : ℕ), 16 ≤ N → 1 ≤ ε ^ 2 * (N : ℝ) →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N Cu →
      ComparableFibreCounts s T (gridScales δ N) Cu →
      ∀ Lgrid : ENNReal, 1 ≤ Lgrid →
      ∀ ζ : ℝ, 0 ≤ ζ →
      (∀ k ≤ N, ∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N k) i₀)
            (fibreBodies T δ) ((T i₀).rescale (gridScale δ N k)).toConvexSpaceBody
          ≤ Lgrid * ENNReal.ofReal ((δ : ℝ) ^ (-ζ))) →
      StickyKakeya.IsFrostmanAtEveryScale s T
        ((C : ENNReal) * Lgrid * ENNReal.ofReal ((δ : ℝ) ^ (-(ζ + 12 * ε ^ 2)))) := by
  classical
  obtain ⟨C, hC, h⟩ :=
    frostmanConstant_allScale_of_grid_bounds_factor (E := E) hn ε Cu hCu
  refine ⟨C, hC, ?_⟩
  intro N hN hεN ι δ hδ hδ1 hδ0 s T hball huni hcmp Lgrid hL ζ hζ0 hgrid
  rw [isFrostmanAtEveryScale_iff_fibre]
  intro ρ hρδ hρ1 i₀ hi₀
  rw [← ConvexSpaceBody.frostmanConstant_le_iff]
  exact h N hN hεN hδ hδ1 hδ0 s T hball huni hcmp Lgrid hL ζ hζ0 hgrid ρ hρδ hρ1 i₀ hi₀

end Geometry

/-! ### The degenerate cut set `{0, N}` -/

section Geometry3

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Alternative (ii): the dividing scales of a long block -/

/-- **The exponent rebase, at its honest cost of three grid steps.**
`Kakeya.MultiScaleFac.ratio_rpow_le_gridScale_ratio_rpow` with the final weakening
`δ^{-3ζ'/N} ≤ δ^{-24ε²}` removed: `ε` disappears and only `ζ' ≤ 1` is needed, the residual
`δ^{-3/N}` being `Kakeya.MultiScaleFac.scaleGapLoss 3 δ`. -/
theorem ratio_rpow_le_gridScale_ratio_rpow_sharp {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1)
    {N : ℕ} (hN : 16 ≤ N) {ζ' : ℝ} (hζ'0 : 0 ≤ ζ') (hζ'1 : ζ' ≤ 1)
    {b c : ℕ} {ρ : NNReal} (hρ : 0 < ρ)
    (_hlo : (gridScale δ N c : ℝ) ≤ (ρ : ℝ)) (hhi : (ρ : ℝ) ≤ (gridScale δ N (c - 3) : ℝ)) :
    ((ρ : ℝ) / (gridScale δ N b : ℝ)) ^ ζ'
      ≤ (δ : ℝ) ^ (-(3 / (N : ℝ))) *
          (((gridScale δ N c : ℝ) / (gridScale δ N b : ℝ)) ^ ζ') := by
  have hδpos : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hδnonneg : 0 ≤ (δ : ℝ) := le_of_lt hδpos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hρℝ : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hσb_pos : 0 < (gridScale δ N b : ℝ) := by exact_mod_cast (gridScale_pos hδ N b)
  have hσc_pos : 0 < (gridScale δ N c : ℝ) := by exact_mod_cast (gridScale_pos hδ N c)
  have hσb_ne : (gridScale δ N b : ℝ) ≠ 0 := ne_of_gt hσb_pos
  have hσc_ne : (gridScale δ N c : ℝ) ≠ 0 := ne_of_gt hσc_pos
  have hρσc_nonneg : 0 ≤ (ρ : ℝ) / (gridScale δ N c : ℝ) := le_of_lt (div_pos hρℝ hσc_pos)
  have hσcσb_nonneg : 0 ≤ (gridScale δ N c : ℝ) / (gridScale δ N b : ℝ) :=
    le_of_lt (div_pos hσc_pos hσb_pos)
  have hfac :
      ((ρ : ℝ) / (gridScale δ N b : ℝ)) ^ ζ'
        = ((ρ : ℝ) / (gridScale δ N c : ℝ)) ^ ζ' *
            ((gridScale δ N c : ℝ) / (gridScale δ N b : ℝ)) ^ ζ' := by
    rw [← Real.mul_rpow hρσc_nonneg hσcσb_nonneg]
    congr 1
    field_simp [hσb_ne, hσc_ne]
  have hd : (c : ℝ) - ((c - 3 : ℕ) : ℝ) ≤ 3 := by
    have hc : (c : ℕ) ≤ c - 3 + 3 := by omega
    have hc' : (c : ℝ) ≤ ((c - 3 : ℕ) : ℝ) + 3 := by exact_mod_cast hc
    linarith
  have hratio : (ρ : ℝ) / (gridScale δ N c : ℝ) ≤
      (gridScale δ N (c - 3) : ℝ) / (gridScale δ N c : ℝ) := by
    rw [div_le_div_iff_of_pos_right hσc_pos]
    exact hhi
  have hstep : (gridScale δ N (c - 3) : ℝ) / (gridScale δ N c : ℝ) ≤
      (δ : ℝ) ^ (-(3 / (N : ℝ))) := by
    rw [← NNReal.coe_div]
    rw [gridScale_div_gridScale hδ N (c - 3) c]
    rw [NNReal.coe_rpow]
    apply Real.rpow_le_rpow_of_exponent_ge hδpos hδ1
    rw [neg_le_neg_iff]
    rw [div_le_div_iff_of_pos_right hNpos]
    exact hd
  have hrho_le : (ρ : ℝ) / (gridScale δ N c : ℝ) ≤ (δ : ℝ) ^ (-(3 / (N : ℝ))) :=
    le_trans hratio hstep
  have h3N_nonneg : 0 ≤ 3 / (N : ℝ) := by positivity
  have hexp : -(3 / (N : ℝ)) ≤ -(3 / (N : ℝ)) * ζ' := by
    rw [neg_mul, neg_le_neg_iff]
    calc
      (3 / (N : ℝ)) * ζ' ≤ (3 / (N : ℝ)) * 1 := by
        exact mul_le_mul_of_nonneg_left hζ'1 h3N_nonneg
      _ = 3 / (N : ℝ) := by rw [mul_one]
  have hpow : ((ρ : ℝ) / (gridScale δ N c : ℝ)) ^ ζ' ≤
      ((δ : ℝ) ^ (-(3 / (N : ℝ)))) ^ ζ' :=
    Real.rpow_le_rpow hρσc_nonneg hrho_le hζ'0
  have hδpow : (δ : ℝ) ^ (-(3 / (N : ℝ)) * ζ') ≤ (δ : ℝ) ^ (-(3 / (N : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hexp
  have hmain : ((ρ : ℝ) / (gridScale δ N c : ℝ)) ^ ζ' ≤ (δ : ℝ) ^ (-(3 / (N : ℝ))) := by
    calc
      ((ρ : ℝ) / (gridScale δ N c : ℝ)) ^ ζ' ≤ ((δ : ℝ) ^ (-(3 / (N : ℝ)))) ^ ζ' := hpow
      _ = (δ : ℝ) ^ (-(3 / (N : ℝ)) * ζ') := (Real.rpow_mul hδnonneg (-(3 / (N : ℝ))) ζ').symm
      _ ≤ (δ : ℝ) ^ (-(3 / (N : ℝ))) := hδpow
  have hσcσb_pow_nonneg : 0 ≤ ((gridScale δ N c : ℝ) / (gridScale δ N b : ℝ)) ^ ζ' :=
    Real.rpow_nonneg hσcσb_nonneg ζ'
  calc
    ((ρ : ℝ) / (gridScale δ N b : ℝ)) ^ ζ'
        = ((ρ : ℝ) / (gridScale δ N c : ℝ)) ^ ζ' *
            ((gridScale δ N c : ℝ) / (gridScale δ N b : ℝ)) ^ ζ' := hfac
    _ ≤ (δ : ℝ) ^ (-(3 / (N : ℝ))) *
          ((gridScale δ N c : ℝ) / (gridScale δ N b : ℝ)) ^ ζ' := by
      exact mul_le_mul_of_nonneg_right hmain hσcσb_pow_nonneg

/-- **The leaf count across a three-step grid window, at its honest cost.**
`Kakeya.MultiScaleFac.card_blockFibre_le_of_grid_window` without its final weakening
`δ^{-24/N} ≤ δ^{-24ε²}`: the loss is `Kakeya.MultiScaleFac.scaleGapLoss 24 δ`, subpolynomial on
the grid of length `⌈log log 1/δ⌉`. -/
theorem card_blockFibre_le_of_grid_window_sharp (hn : Module.finrank ℝ E = 3)
    (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ K : NNReal, 1 ≤ K ∧
      ∀ (N : ℕ), 16 ≤ N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      UniformTubeSet s T N Cu →
      ∀ b c : ℕ, c + 2 ≤ b → b ≤ N →
      ∀ ρ : NNReal, (gridScale δ N c : ℝ) ≤ (ρ : ℝ) →
        (ρ : ℝ) ≤ (gridScale δ N (c - 3) : ℝ) →
      ∀ i₀ ∈ s,
        ((fibreIndex s T δ ρ i₀).card : ENNReal)
          ≤ (K : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(24 / (N : ℝ))))
              * ((fibreIndex s T δ (gridScale δ N c) i₀).card : ENNReal) := by
  classical
  let n : ℕ := Module.finrank ℝ E
  let Kbase : NNReal := 2 * (25 : NNReal) ^ (2 * n) * (Cu ^ 2) ^ 3
  let K : NNReal := max 1 Kbase
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKbase_le_K : Kbase ≤ K := le_max_right _ _
  refine ⟨K, hK1, ?_⟩
  intro N hN ι δ hδ hδ1 hδ0 s T hu b c hcb hbN ρ hlo hhi i₀ hi₀
  have hδpos : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hδnonneg : 0 ≤ (δ : ℝ) := le_of_lt hδpos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hn3 : n = 3 := by simpa [n] using hn
  have hσc_pos_nn : 0 < gridScale δ N c := gridScale_pos hδ N c
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := lt_of_lt_of_le (by exact_mod_cast hσc_pos_nn) hlo
  have hσc1_pos_nn : 0 < gridScale δ N (c + 1) := gridScale_pos hδ N (c + 1)
  have hσc1_pos : 0 < (gridScale δ N (c + 1) : ℝ) := by exact_mod_cast hσc1_pos_nn
  have hc1N : c + 1 ≤ N := by omega
  have hcN : c < N := by omega
  have hu_base : Tube.IsUniformAtScale s T (gridScale δ N (c + 1)) (Cu ^ 2) :=
    hu.toChain.uniformAt hCu hc1N
  have h2δ : 2 * δ ≤ gridScale δ N (c + 1) := by
    refine le_trans ?_ (sixteen_mul_gridScale_succ_le hδ hδ0 (by omega : c + 1 < N))
    have hδσ : δ ≤ gridScale δ N (c + 2) := by
      simpa [gridScale_self δ (by omega : 0 < N)] using
        gridScale_antitone hδ hδ1 N (by omega : c + 2 ≤ N)
    calc (2 : NNReal) * δ ≤ 16 * δ := by gcongr; norm_num
      _ ≤ 16 * gridScale δ N (c + 2) := by gcongr
  have hσc1_le_σc : gridScale δ N (c + 1) ≤ gridScale δ N c :=
    gridScale_antitone hδ hδ1 N (by omega : c ≤ c + 1)
  have hσc_le_ρ : gridScale δ N c ≤ ρ := by exact_mod_cast hlo
  have hσc1_le_ρ : gridScale δ N (c + 1) ≤ ρ := le_trans hσc1_le_σc hσc_le_ρ
  have hcount_raw : ((fibreIndex s T δ ρ i₀).card : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * n) * ((Cu ^ 2 : NNReal) : ℝ) ^ 3
          * ((ρ : ℝ) / (gridScale δ N (c + 1) : ℝ)) ^ (2 * n)
          * ((fibreIndex s T δ (8 * gridScale δ N (c + 1)) i₀).card : ℝ) := by
    have h := anchorGraded_of_isUniformAtScale_atScale (E := E) (s := s) (T := T)
      (δ := δ) (σ := δ) (ρ := gridScale δ N (c + 1)) (ρ' := ρ)
      (h := hu_base) (hρ := hσc1_pos_nn) (hδσ := le_rfl) (hσρ := h2δ)
      (hρρ' := hσc1_le_ρ) hi₀
    simpa [n] using h
  have h8 : 8 * gridScale δ N (c + 1) ≤ gridScale δ N c :=
    le_trans (by gcongr; norm_num) (sixteen_mul_gridScale_succ_le hδ hδ0 hcN)
  have hsub8 : fibreIndex s T δ (8 * gridScale δ N (c + 1)) i₀ ⊆
      fibreIndex s T δ (gridScale δ N c) i₀ :=
    fibreIndex_subset_of_anchor_le (s := s) (T := T) (σ := δ) (ρ := 8 * gridScale δ N (c + 1))
      (ρ' := gridScale δ N c) h8 i₀
  have hcount : ((fibreIndex s T δ ρ i₀).card : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * n) * ((Cu ^ 2 : NNReal) : ℝ) ^ 3
          * ((ρ : ℝ) / (gridScale δ N (c + 1) : ℝ)) ^ (2 * n)
          * ((fibreIndex s T δ (gridScale δ N c) i₀).card : ℝ) :=
    hcount_raw.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_card hsub8) (by positivity))
  have hρσc1_nonneg : 0 ≤ (ρ : ℝ) / (gridScale δ N (c + 1) : ℝ) :=
    le_of_lt (div_pos hρ0 hσc1_pos)
  have hd' : ((c + 1 : ℕ) : ℝ) - ((c - 3 : ℕ) : ℝ) ≤ 4 := by
    have hc' : (c : ℝ) ≤ ((c - 3 : ℕ) : ℝ) + 3 := by exact_mod_cast (by omega : c ≤ c - 3 + 3)
    push_cast
    linarith
  have hratio : (ρ : ℝ) / (gridScale δ N (c + 1) : ℝ) ≤
      (gridScale δ N (c - 3) : ℝ) / (gridScale δ N (c + 1) : ℝ) := by
    rwa [div_le_div_iff_of_pos_right hσc1_pos]
  have hstep : (gridScale δ N (c - 3) : ℝ) / (gridScale δ N (c + 1) : ℝ) ≤
      (δ : ℝ) ^ (-(4 / (N : ℝ))) := by
    rw [← NNReal.coe_div, gridScale_div_gridScale hδ N (c - 3) (c + 1), NNReal.coe_rpow]
    apply Real.rpow_le_rpow_of_exponent_ge hδpos hδ1
    rwa [neg_le_neg_iff, div_le_div_iff_of_pos_right hNpos]
  have hratio_le : (ρ : ℝ) / (gridScale δ N (c + 1) : ℝ) ≤ (δ : ℝ) ^ (-(4 / (N : ℝ))) :=
    le_trans hratio hstep
  have hpack : ((ρ : ℝ) / (gridScale δ N (c + 1) : ℝ)) ^ (2 * n) ≤ (δ : ℝ) ^ (-(24 / (N : ℝ))) := by
    refine (pow_le_pow_left₀ hρσc1_nonneg hratio_le (2 * n)).trans_eq ?_
    have hn3' : (n : ℝ) = 3 := by exact_mod_cast hn3
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδnonneg]
    congr 1
    push_cast
    rw [hn3']
    field_simp [hNne]
    ring
  let Kℝ : ℝ := 2 * (25 : ℝ) ^ (2 * n) * ((Cu ^ 2 : NNReal) : ℝ) ^ 3
  let R : ℝ := (ρ : ℝ) / (gridScale δ N (c + 1) : ℝ)
  let A : ℝ := Kℝ * R ^ (2 * n)
  have hA_nonneg : 0 ≤ A := by positivity
  have hcard_enn : ((fibreIndex s T δ ρ i₀).card : ENNReal)
      ≤ ENNReal.ofReal A * ((fibreIndex s T δ (gridScale δ N c) i₀).card : ENNReal) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hA_nonneg]
    exact ENNReal.ofReal_le_ofReal (by simpa [A, Kℝ, R] using hcount)
  have hδpow_nonneg : 0 ≤ (δ : ℝ) ^ (-(24 / (N : ℝ))) := Real.rpow_nonneg hδnonneg _
  have hKℝ_le : Kℝ ≤ (K : ℝ) := by exact_mod_cast hKbase_le_K
  have hKℝ_nonneg : 0 ≤ Kℝ := by positivity
  have hA_le : ENNReal.ofReal A ≤ (K : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(24 / (N : ℝ)))) := by
    have hreal : A ≤ (K : ℝ) * (δ : ℝ) ^ (-(24 / (N : ℝ))) :=
      (mul_le_mul_of_nonneg_left hpack hKℝ_nonneg).trans
        (mul_le_mul_of_nonneg_right hKℝ_le hδpow_nonneg)
    calc
      ENNReal.ofReal A ≤ ENNReal.ofReal ((K : ℝ) * (δ : ℝ) ^ (-(24 / (N : ℝ)))) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = (K : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(24 / (N : ℝ)))) := by
          rw [ENNReal.ofReal_mul' hδpow_nonneg]
          rw [← ENNReal.ofReal_coe_nnreal]
  exact hcard_enn.trans (mul_le_mul_of_nonneg_right hA_le bot_le)

/-- **The anchor transfer, at its honest cost of four grid steps.**
`Kakeya.MultiScaleFac.frostmanConstant_fibre_lower_transfer` without the final weakening
`δ^{-24/N} ≤ δ^{-24ε²}`: the transfer costs `Kakeya.MultiScaleFac.scaleGapLoss 24 δ`, and `ε`
disappears from the statement entirely. -/
theorem frostmanConstant_fibre_lower_transfer_sharp (hn : Module.finrank ℝ E = 3)
    (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (N : ℕ), 16 ≤ N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N Cu →
      ∀ b c : ℕ, c + 2 ≤ b → b ≤ N →
      ∀ ρ : NNReal, (gridScale δ N c : ℝ) ≤ (ρ : ℝ) →
        (ρ : ℝ) ≤ (gridScale δ N (c - 3) : ℝ) →
      ∀ i₀ ∈ s,
        ENNReal.ofReal ((δ : ℝ) ^ (24 / (N : ℝ))) *
            ConvexSpaceBody.frostmanConstant
              (fibreIndex s T δ (gridScale δ N c) i₀)
              (fibreBodies T (gridScale δ N b))
              ((T i₀).rescale (2 * gridScale δ N c)).toConvexSpaceBody
          ≤ (C : ENNReal) *
              ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ i₀)
                (fibreBodies T (gridScale δ N b))
                ((T i₀).rescale (2 * ρ)).toConvexSpaceBody := by
  classical
  obtain ⟨K, hK1, hK⟩ := card_blockFibre_le_of_grid_window_sharp hn Cu hCu
  let Cr : NNReal := Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)
  let C : NNReal := max 1 (K * Cr)
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  refine ⟨C, hC1, ?_⟩
  intro N hN ι δ hδ hδ1 hδ0 s T hball hUnif b c hc2b hbN ρ hlo hhi i₀ hi₀
  have hNpos : 0 < N := by omega
  set A : ENNReal := (K : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(24 / (N : ℝ))))
  have hcard : ((fibreIndex s T δ ρ i₀).card : ENNReal)
      ≤ A * ((fibreIndex s T δ (gridScale δ N c) i₀).card : ENNReal) := by
    simpa [A] using hK N hN hδ hδ1 hδ0 s T hUnif b c hc2b hbN ρ hlo hhi i₀ hi₀
  have hδσ : δ ≤ gridScale δ N b := by
    calc
      δ = gridScale δ N N := (gridScale_self δ hNpos).symm
      _ ≤ gridScale δ N b := gridScale_antitone hδ hδ1 N hbN
  have hσ1 : gridScale δ N b ≤ 1 := gridScale_le_one hδ1 N b
  have hσρ : gridScale δ N b ≤ gridScale δ N c := gridScale_antitone hδ hδ1 N (by omega : c ≤ b)
  have hρρ' : gridScale δ N c ≤ ρ := by exact_mod_cast hlo
  have hF := frostmanConstant_blockFibre_le_of_card_le (s := s) (T := T) (δ := δ)
    (σ := gridScale δ N b) (ρ := gridScale δ N c) (ρ' := ρ)
    hδ hδσ hσ1 hσρ hρρ' hi₀ hcard
  have hδpos : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hδnonneg : 0 ≤ (δ : ℝ) := le_of_lt hδpos
  have hexp : 24 / (N:ℝ) + (-(24 / (N:ℝ))) = (0 : ℝ) := by ring
  have hprod : ENNReal.ofReal ((δ : ℝ) ^ (24 / (N : ℝ))) *
      ENNReal.ofReal ((δ : ℝ) ^ (-(24 / (N : ℝ)))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδnonneg (24 / (N : ℝ)))]
    have hmul : (δ : ℝ) ^ (24 / (N : ℝ)) * (δ : ℝ) ^ (-(24 / (N : ℝ))) = 1 := by
      calc
        (δ : ℝ) ^ (24 / (N : ℝ)) * (δ : ℝ) ^ (-(24 / (N : ℝ)))
            = (δ : ℝ) ^ (24 / (N : ℝ) + (-(24 / (N : ℝ)))) := by
              rw [← Real.rpow_add hδpos]
        _ = (δ : ℝ) ^ (0 : ℝ) := by rw [hexp]
        _ = 1 := by simp
    rw [hmul]
    simp
  have hCge : K * Cr ≤ C := by
    dsimp [C]
    exact le_max_right _ _
  have hmain : ENNReal.ofReal ((δ : ℝ) ^ (24 / (N : ℝ))) * A * (Cr : ENNReal) ≤ (C : ENNReal) := by
    calc
      ENNReal.ofReal ((δ : ℝ) ^ (24 / (N : ℝ))) * A * (Cr : ENNReal)
          = (K : ENNReal) * (ENNReal.ofReal ((δ : ℝ) ^ (24 / (N : ℝ))) *
              ENNReal.ofReal ((δ : ℝ) ^ (-(24 / (N : ℝ))))) * (Cr : ENNReal) := by
            simp [A, mul_assoc, mul_left_comm]
      _ = (K : ENNReal) * (Cr : ENNReal) := by
            rw [hprod]
            simp
      _ ≤ (C : ENNReal) := by
            exact_mod_cast hCge
  calc
    ENNReal.ofReal ((δ : ℝ) ^ (24 / (N : ℝ))) *
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N c) i₀)
          (fibreBodies T (gridScale δ N b)) ((T i₀).rescale (2 * gridScale δ N c)).toConvexSpaceBody
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (24 / (N : ℝ))) *
          (A * (Cr : ENNReal) *
            ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ i₀)
              (fibreBodies T (gridScale δ N b)) ((T i₀).rescale (2 * ρ)).toConvexSpaceBody) := by
        exact mul_le_mul' le_rfl hF
    _ = (ENNReal.ofReal ((δ : ℝ) ^ (24 / (N : ℝ))) * A * (Cr : ENNReal)) *
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ i₀)
          (fibreBodies T (gridScale δ N b)) ((T i₀).rescale (2 * ρ)).toConvexSpaceBody := by
          simp [mul_assoc]
    _ ≤ (C : ENNReal) *
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ i₀)
          (fibreBodies T (gridScale δ N b)) ((T i₀).rescale (2 * ρ)).toConvexSpaceBody := by
          exact mul_le_mul' hmain le_rfl

end Geometry3

end MultiScaleFac

end Kakeya
