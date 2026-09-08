/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.NodeAncestorSplit
public import Kakeya.MultiScaleFac.Bridge
public import Kakeya.MultiScaleFac.Loss

/-!
# Reading the terminal alternative at a grid level, half (A)

The scale bookkeeping that puts the terminal alternative's reading scale on the grid, the node
density pair it is divided by, and the narrow-window witness package the spreading step consumes.

This module is the merge of the former `Bullet3WitnessScale`, `Bullet3AssemblyA`,
`Bullet3WitnessPrep`, `Bullet3NarrowWitness`.  Each keeps its own section, so its file-level `open`s
and `variable`s stay confined to it.

## The reading scale of the half-(A) witness

`Kakeya.MultiScaleFac.exists_classImage_witness_of_le_mul_frostmanConstant_nodesIn` consumes a lower
bound on the Frostman constant of the level-`b` nodes inside the `8 ρ_c`-dilate of a *single*
level-`c` node.  The terminal alternative (ii) supplies a lower bound of a different shape: it is
about the *leaf fibre* `fibreIndex s T δ ρ i₀` at a *real* scale `ρ`, and it is available only for
`ρ` inside a window of exponent `(1 + 2κ)ε`.

The two do not meet at the same scale.  The grid rounding of
`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_rescale_of_grid_dilate` insists on `32 ρ_c ≤ ρ`,
so the witness has to be read at a grid scale a few grid steps *below* `ρ`; and if `ρ` sits at the
lower endpoint of the window, that reading scale falls outside the window, where the alternative
says nothing.

This section pays that gap.  The observation is that the lower endpoint of the window is a power of
`δ` whose exponent is affine in the window exponent, so lowering the reading scale by `k` grid
steps is the same as raising the window exponent by `k / (b - a)`:

  `scaleGapLoss k δ · winLo e ≤ winLo e'`  whenever  `k ≤ (e' - e)(b - a)`.

This is `Kakeya.MultiScaleFac.A.scaleGapLoss_mul_windowLower_le`, the mirror of
`Kakeya.MultiScaleFac.window_endpoint_le_scaleGapLoss_mul`, which bounds the endpoint at the larger
exponent from *above* and is therefore of no use here.  Consequently a scale `ρ` supplied on the
window of exponent `e'` still has its whole `scaleGapLoss k δ`-neighbourhood below it inside the
window of the smaller exponent `e`, and the reading scale `ρ_c` may be taken there.  The residual is
`k` grid steps, hence a `Kakeya.MultiScaleFac.scaleGapLoss` and not a fixed power of `δ`; with
`e' = (1 + (2 + k)κ)ε` and `e = (1 + 2κ)ε` the hypothesis `k ≤ (e' - e)(b - a)` is exactly
`k ≤ kκε(b - a)`, which the long-block bound `1 ≤ κε(b - a)` gives.

The upper endpoint costs nothing: it *shrinks* as the exponent grows
(`Kakeya.MultiScaleFac.window_upper_antitone`), so a scale below `ρ` is automatically below it.

With the reading scale inside the window, the alternative applies at `ρ_c` itself, and
`Kakeya.MultiScaleFac.frostmanConstant_fibre_le_mul_frostmanConstant_nodesIn` converts the fibre
lower bound into the node lower bound that the witness lemma wants.  The only other cost is the
rebase of the left-hand side `(ρ/σ_b)^ζ'` onto `(ρ_c/σ_b)^ζ'`, which is the factor `L` by which `ρ`
exceeds `ρ_c`, raised to `ζ' ≤ 1`.

`Kakeya.MultiScaleFac.A.witness_hX_of_alternativeTwo` assembles the three steps and displays the
coefficient `L · D₀ · (fibreFromNodeConst · C_u^5)`, where `D₀` is whatever the alternative itself
carries -- for the sharp dichotomy `C₂ · scaleGapLoss 27 δ`.

## Assembling the half-(A) third bullet

The pieces are in place: the witness reading of the terminal alternative
(`Kakeya.MultiScaleFac.A.witness_hX_of_alternativeTwo`), its spreading over a grid level by the
two-sided band (`Kakeya.MultiScaleFac.A.hgrid_of_witness`), the grid rounding
(`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_rescale_of_grid_dilate`) and the two ends of the
window (`Kakeya.MultiScaleFac.A.bulletThree_fineEnd_of_transport` and
`Kakeya.MultiScaleFac.A.bulletThree_coarseEnd_of_ancestor`).

This section supplies the two inputs those pieces still ask for and that no other file produces.

The first is the pair of density bounds `dm ≤ Δ(𝕋_b[P^{(8ρ_c)}], P^{(8ρ_c)}) ≤ Dm`, uniform in the
level-`c` node.  Neither bound is an absolute constant — a sparse hierarchy makes both small — but
the spreading lemma divides by `dm` and multiplies by `Dm`, so only their *ratio* enters, and that
ratio is absolute.  Both bounds are produced from the same branching-versus-grid-scale quantity, and
the quantity cancels.

The second is the trivial normalisation `ρ ≤ 1` of a window scale, which the sharp rounding index
needs and which the window hypotheses do not state.

## The two per-scale inputs of the half-(A) third bullet

`Kakeya.MultiScaleFac.A.witness_hX_of_alternativeTwo` reads the terminal alternative (ii) at a
grid scale and hands the result to `Kakeya.MultiScaleFac.A.hgrid_of_witness`.  Between the
alternative and that reading there are two hypotheses it does not produce itself, and both are
per-scale data rather than arithmetic:

* the witness leaf `i₀` together with the two index facts `hi₀` and `hjj'`.  The alternative is
  stated on a *majority set of leaves*; the witness lemma wants a leaf of the class of a node, plus
  the containment of that node in a node of the coarser index `c`.  The `goodNodes` translation of
  `Kakeya/MultiScaleFac/Bridge.lean` supplies the leaf, and the iterated nesting
  `Kakeya.MultiScaleFac.tube_assign_le_of_le` supplies the containment once `j'` is taken to be the
  level-`c` node *of the same leaf*, `j' = a_c(i₀)`.  This is the only choice of `j'` for which the
  containment is free: the leaf, not the node, is what the two indices have in common.

* the clumping hypothesis `hclump`.  This is the field `Kakeya.StickyKakeya.GridUniform.clumped`,
  which is why the whole chain has to carry a `Kakeya.MultiScaleFac.GridUniform` and not merely the
  `Tube.UniformTubeSet` it induces -- clumping is not a consequence of uniformity.
  The transfer is free because `Kakeya.MultiScaleFac.GridUniform.toUniformTubeSet_cover` is `rfl`.

  The field is supplied only for `c < N`, the bottom scale `ρ_N = δ` having nothing to clump into.
  That boundary is not an extra hypothesis here: the witness lemma already demands `2δ ≤ ρ_c`, and
  `ρ_N = δ`, so `2δ ≤ δ` would force `δ = 0`.  `Kakeya.MultiScaleFac.A.lt_of_two_mul_le_gridScale`
  records that implication, so no degenerate case is left open.

## The narrow-window witness of the half-(A) third bullet

The third bullet of half (A) reads the terminal alternative (ii) at a *real* scale `ρ` of the narrow
window and turns it into a lower bound on the Frostman constant of a level-`b` node family inside a
dilated level-`c` node.  Four lemmas do the work, in this order:

`Kakeya.MultiScaleFac.A.exists_round_index_sharp` chooses the reading level `c`,
`Kakeya.MultiScaleFac.A.witness_hX_of_alternativeTwo` reads the alternative there,
`Kakeya.MultiScaleFac.A.hgrid_of_witness` spreads that reading over the whole level, and
`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_rescale_of_grid_dilate` rounds the real scale to
the grid.

This section assembles the *first two* steps into a single per-scale package.  Its output is
verbatim the conclusion of `Kakeya.MultiScaleFac.A.witness_hX_of_alternativeTwo`, existentially
quantified
over the reading level `c` and the level-`c` node `j'` that the first two steps produce; the last
two steps consume it unchanged.

Three things are settled here that the two lemmas do not settle themselves.

* The scale hypotheses.  The rounding produces `32 σ_c ≤ ρ ≤ 32 Λ₁ σ_c`, where `Λ₁` is the
  one-step `Kakeya.MultiScaleFac.scaleGapLoss`; the reading wants `σ_c ≤ ρ ≤ L σ_c` with
  `L ≤ scaleGapLoss k δ` for the gap budget `k` of the window.  Taking `L = 32 Λ₁` and `k = 6`
  matches them, the factor `32` being paid by five further grid steps: consecutive grid scales are
  `16`-separated, so `Λ₁ ≥ 16` and `32 Λ₁ ≤ Λ₁^5 Λ₁ = Λ₆`.

* The window bookkeeping.  The rounding asks for `3 ≤ e' (b - a)` and the reading for
  `6 ≤ (e' - e)(b - a)`, where `e` is the exponent of the window the alternative speaks on and `e'`
  the exponent of the narrower window `ρ` lives in.  The second implies the first, since `e ≥ 0`,
  and it also implies `a < b`, which the rounding needs and the reading does not.

* The witness leaf.  The alternative is stated on a majority set `G` of leaves, so the reading's
  hypothesis `hAlt` is available only at leaves of `G`; the leaf is produced by
  `Kakeya.MultiScaleFac.A.exists_witness_leaf` from a good node `j`, and the level-`c` node `j'`
  is the level-`c` node of that same leaf.  This is why the package carries a
  `Kakeya.MultiScaleFac.GridUniform` and not merely the uniform set of tubes it induces: the
  clumping hypothesis of the reading is the field
  `Kakeya.StickyKakeya.GridUniform.clumped`, supplied by
  `Kakeya.MultiScaleFac.A.hclump_of_gridUniform`.
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
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-! ### The lower endpoint of the window, from below -/

/-- **Lowering the reading scale by `k` grid steps is raising the window exponent by
`k / (b - a)`.**  Both endpoints are `δ` raised to an affine function of the window exponent, so the
ratio of the endpoint at `e'` to the one at `e` is `δ^{-(e'-e)(b-a)/M}`, and the hypothesis
`k ≤ (e'-e)(b-a)` says that ratio is at least `Kakeya.MultiScaleFac.scaleGapLoss k δ`.  Mirror of
`window_endpoint_le_scaleGapLoss_mul`, bounding the larger-exponent endpoint from *below*. -/
theorem A.scaleGapLoss_mul_windowLower_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hM : 0 < ssfGridLen δ) {a b : ℕ} {e e' : ℝ} {k : ℕ}
    (hk : (k : ℝ) ≤ (e' - e) * ((b : ℝ) - (a : ℝ))) :
    scaleGapLoss k δ
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            * ((gridScale δ (ssfGridLen δ) a : ℝ)
                / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e)
      ≤ (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e' := by
  rw [scaleGapLoss, gridScale_mul_ratio_rpow hδ (ssfGridLen δ) a b e',
    gridScale_mul_ratio_rpow hδ (ssfGridLen δ) a b e,
    ← Real.rpow_add (NNReal.coe_pos.mpr hδ),
    show -((k : ℝ) / (ssfGridLen δ : ℝ))
        + ((b : ℝ) - e * ((b : ℝ) - (a : ℝ))) / (ssfGridLen δ : ℝ)
      = (((b : ℝ) - e * ((b : ℝ) - (a : ℝ))) - (k : ℝ)) / (ssfGridLen δ : ℝ) by ring]
  exact (rpow_div_le_rpow_div_iff hδ hδ1 hM _ _).2 (by linarith)

/-- **Dividing out a positive gap loss.**  If `L` is at most the loss, then `L · z` dominating
`loss · x` forces `x ≤ z`. -/
theorem A.le_of_scaleGapLoss_mul_le {δ : NNReal} (hδ : 0 < δ) {k : ℕ} {x y z L : ℝ}
    (hxy : scaleGapLoss k δ * x ≤ y) (hyz : y ≤ L * z) (hL : L ≤ scaleGapLoss k δ)
    (hz : 0 ≤ z) : x ≤ z :=
  le_of_mul_le_mul_left ((hxy.trans hyz).trans (mul_le_mul_of_nonneg_right hL hz))
    (Real.rpow_pos_of_pos (by exact_mod_cast hδ) _)

/-- **A reading scale within one gap loss of a window scale is still inside the wider window.**  If
`ρ` lies above the lower endpoint at exponent `e'` and `ρ ≤ L ρ_c` with `L ≤ scaleGapLoss k δ`, then
`ρ_c` lies above the lower endpoint at the smaller exponent `e`, provided `k ≤ (e'-e)(b-a)`.  This
puts the witness reading scale `ρ_c ≈ ρ/32` back inside the window of the terminal alternative. -/
theorem A.windowLower_le_gridScale {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hM : 0 < ssfGridLen δ) {a b c : ℕ} {e e' : ℝ} {k : ℕ} {L : ℝ}
    (hk : (k : ℝ) ≤ (e' - e) * ((b : ℝ) - (a : ℝ))) (hL : L ≤ scaleGapLoss k δ)
    {rho : NNReal}
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e' ≤ (rho : ℝ))
    (hup : (rho : ℝ) ≤ L * (gridScale δ (ssfGridLen δ) c : ℝ)) :
    (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e
      ≤ (gridScale δ (ssfGridLen δ) c : ℝ) :=
  A.le_of_scaleGapLoss_mul_le hδ ((A.scaleGapLoss_mul_windowLower_le hδ hδ1 hM hk).trans hlo)
    hup hL (NNReal.coe_nonneg _)

/-- **The upper endpoint costs nothing.**  It is antitone in the window exponent
(`Kakeya.MultiScaleFac.window_upper_antitone`), so a grid scale below a scale of the window at
exponent `e'` is below the upper endpoint of every window of smaller exponent `e ≤ e'`. -/
theorem A.gridScale_le_windowUpper {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {a b c : ℕ} (hab : a ≤ b) {e e' : ℝ} (he : 0 ≤ e) (hee' : e ≤ e') {rho : NNReal}
    (hhi : (rho : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e')
    (hsr : (gridScale δ (ssfGridLen δ) c : ℝ) ≤ (rho : ℝ)) :
    (gridScale δ (ssfGridLen δ) c : ℝ)
      ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e :=
  hsr.trans (hhi.trans (window_upper_antitone (M := ssfGridLen δ) hδ hδ1 hab he hee'))

/-! ### Rebasing the left-hand side -/

/-- **Rebasing the interpolation factor onto the reading scale.**

The left-hand side of the third bullet is `(ρ/σ_b)^ζ'`, and the alternative applied at the reading
scale produces `(ρ_c/σ_b)^ζ'`.  With `ρ ≤ L ρ_c` and `ζ' ≤ 1` the ratio is at most `L^{ζ'} ≤ L`, so
no power of `δ` beyond the one already inside `L` is created. -/
theorem A.rpow_ratio_le_mul_rpow_ratio {zeta : ℝ} (hz0 : 0 ≤ zeta) (hz1 : zeta ≤ 1)
    {r sc sb L : ℝ} (hsb : 0 < sb) (hsc : 0 ≤ sc) (hr0 : 0 ≤ r) (hL : 1 ≤ L)
    (hrL : r ≤ L * sc) :
    (r / sb) ^ zeta ≤ L * (sc / sb) ^ zeta := by
  have hd : (0 : ℝ) ≤ sc / sb := div_nonneg hsc hsb.le
  calc (r / sb) ^ zeta ≤ (L * (sc / sb)) ^ zeta :=
        Real.rpow_le_rpow (div_nonneg hr0 hsb.le) (by rw [← mul_div_assoc]; gcongr) hz0
    _ = L ^ zeta * (sc / sb) ^ zeta := Real.mul_rpow (zero_le_one.trans hL) hd
    _ ≤ L * (sc / sb) ^ zeta := mul_le_mul_of_nonneg_right
        (by simpa using Real.rpow_le_rpow_of_exponent_le hL hz1) (Real.rpow_nonneg hd _)

/-- The `ℝ`-to-`ENNReal` transfer of a bound with a nonnegative displayed factor. -/
theorem A.ofReal_le_ofReal_mul {x y L : ℝ} (hL : 0 ≤ L) (h : x ≤ L * y) :
    ENNReal.ofReal x ≤ ENNReal.ofReal L * ENNReal.ofReal y :=
  (ENNReal.ofReal_le_ofReal h).trans_eq (ENNReal.ofReal_mul hL)

/-! ### From the leaf fibre to the nodes of a dilate -/

/-- **A lower bound on a leaf fibre at a grid scale is a lower bound on the nodes of the
`8 ρ_c`-dilate.**  Composing the given bound with
`Kakeya.MultiScaleFac.frostmanConstant_fibre_le_mul_frostmanConstant_nodesIn`; this is the shape in
which `exists_classImage_witness_of_le_mul_frostmanConstant_nodesIn` consumes its hypothesis `hX`,
the coefficient growing by exactly the dimensional bridge constant `fibreFromNodeConst · C_u^5`. -/
theorem A.le_mul_frostmanConstant_nodesIn_of_fibre {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hNpos : 0 < N)
    (hCu : 1 ≤ Cu) (𝒰 : UniformTubeSet s T N Cu) {b c : ℕ} (hb : b ≤ N) (hc : c ≤ N)
    (hcb : c ≤ b) (h2d : 2 * δ ≤ gridScale δ N c) {j j' i0 : ι}
    (hi0 : i0 ∈ coverClass s (𝒰.cover.assign b) j)
    (hjj' : (𝒰.cover.tube b j).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody)
    (hclump : ∃ i2, coverClass s (𝒰.cover.assign c) (𝒰.cover.assign c i0)
        ⊆ fibreIndex s T δ (gridScale δ N c / 4) i2)
    {X D : ENNReal}
    (hfib : X ≤ D * ConvexSpaceBody.frostmanConstant
        (fibreIndex s T δ (gridScale δ N c) i0)
        (fibreBodies T (gridScale δ N b))
        ((T i0).rescale (2 * gridScale δ N c)).toConvexSpaceBody) :
    X ≤ D * ((fibreFromNodeConst (E := E) : ENNReal) * (Cu : ENNReal) ^ 5)
        * ConvexSpaceBody.frostmanConstant
            (𝒰.nodesIn b ((𝒰.cover.tube c j').rescale (8 * gridScale δ N c)).toConvexSpaceBody)
            (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
            ((𝒰.cover.tube c j').rescale (8 * gridScale δ N c)).toConvexSpaceBody := by
  rw [mul_assoc]
  exact hfib.trans (mul_le_mul_right (frostmanConstant_fibre_le_mul_frostmanConstant_nodesIn
    hδ hδ1 hNpos hCu 𝒰 hb hc hcb h2d hi0 hjj' hclump) D)

/-! ### The witness, read at the grid scale -/

/-- **The witness hypothesis of the half-(A) third bullet, from the terminal alternative.**  The
output is verbatim the hypothesis `hX` of
`exists_classImage_witness_of_le_mul_frostmanConstant_nodesIn` at the level-`c` node `j'`, with the
coefficient `D = L · D₀ · (fibreFromNodeConst · C_u^5)`.  The window hypotheses `hk` and `hL` say
that the factor `L` separating `ρ` from its reading scale is no wider than the exponent gap. -/
theorem A.witness_hX_of_alternativeTwo {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlt : (δ : ℝ) < 1) (hM : 0 < ssfGridLen δ) {s : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (hCu : 1 ≤ Cu) (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu)
    {zeta : ℝ} (hz0 : 0 ≤ zeta) (hz1 : zeta ≤ 1)
    {a b c : ℕ} (hab : a ≤ b) (hb : b ≤ ssfGridLen δ) (hc : c ≤ ssfGridLen δ) (hcb : c ≤ b)
    (h2d : 2 * δ ≤ gridScale δ (ssfGridLen δ) c)
    {e e' : ℝ} {k : ℕ} {L : ℝ} (he : 0 ≤ e) (hee' : e ≤ e')
    (hk : (k : ℝ) ≤ (e' - e) * ((b : ℝ) - (a : ℝ))) (hL1 : 1 ≤ L)
    (hL : L ≤ scaleGapLoss k δ)
    {rho : NNReal}
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e' ≤ (rho : ℝ))
    (hhi : (rho : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e')
    (hsr : (gridScale δ (ssfGridLen δ) c : ℝ) ≤ (rho : ℝ))
    (hrs : (rho : ℝ) ≤ L * (gridScale δ (ssfGridLen δ) c : ℝ))
    {j j' i0 : ι} (hi0 : i0 ∈ coverClass s (𝒰.cover.assign b) j)
    (hjj' : (𝒰.cover.tube b j).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody)
    (hclump : ∃ i2, coverClass s (𝒰.cover.assign c) (𝒰.cover.assign c i0)
        ⊆ fibreIndex s T δ (gridScale δ (ssfGridLen δ) c / 4) i2)
    {D0 : ENNReal}
    (hAlt : ∀ r : NNReal,
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e ≤ (r : ℝ) →
      (r : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e →
      ENNReal.ofReal (((r : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta)
        ≤ D0 * ConvexSpaceBody.frostmanConstant (fibreIndex s T δ r i0)
            (fibreBodies T (gridScale δ (ssfGridLen δ) b))
            ((T i0).rescale (2 * r)).toConvexSpaceBody) :
    ENNReal.ofReal (((rho : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta)
      ≤ ENNReal.ofReal L * (D0 * ((fibreFromNodeConst (E := E) : ENNReal) * (Cu : ENNReal) ^ 5))
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube c j').rescale
                  (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)
              (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
              ((𝒰.cover.tube c j').rescale
                  (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody := by
  have hnode := A.le_mul_frostmanConstant_nodesIn_of_fibre (j := j) (j' := j') hδ hδ1 hM hCu 𝒰
    hb hc hcb h2d hi0 hjj' hclump (hAlt (gridScale δ (ssfGridLen δ) c)
      (A.windowLower_le_gridScale hδ hδlt hM hk hL hlo hrs)
      (A.gridScale_le_windowUpper hδ hδ1 hab he hee' hhi hsr))
  rw [mul_assoc]
  exact (A.ofReal_le_ofReal_mul (zero_le_one.trans hL1)
    (A.rpow_ratio_le_mul_rpow_ratio hz0 hz1
      (NNReal.coe_pos.mpr (gridScale_pos hδ (ssfGridLen δ) b))
      (NNReal.coe_nonneg _) (NNReal.coe_nonneg rho) hL1 hrs)).trans
    (mul_le_mul_right hnode (ENNReal.ofReal L))

/-! ### The ratio of the two node densities -/

/-- **Constant in Lemma `A.exists_density_pair`.**  The ratio of the upper node-density constant to
the lower one, times the packing constant of the ancestor split and the square of the uniformity
constant.  It depends on the ambient dimension and on `C_u` alone, the branching-versus-grid-scale
quantity that both density bounds are built from cancelling between them. -/
noncomputable def nodeDensityRatioConst (n : ℕ) (Cu : NNReal) : NNReal :=
  nodeDensityUBConst n * nodeCountSplitConst n Cu * Cu ^ 2 / nodeDensityLBConst n

/-- **The two node-density bounds, with an absolute ratio.**  Each of
`le_densityIn_nodesIn_rescale_eight_of_branchingN` and its upper counterpart carries a free constant
and a branching-versus-grid-scale hypothesis; choosing that constant on both sides from
`X = branchingN c · ρ_b^{n-1} / (branchingN b · ρ_c^{n-1})` discharges both, and `X` cancels from
the ratio `Dm/dm` that the spreading lemma consumes. -/
theorem A.exists_density_pair {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : UniformTubeSet s T N Cu) (hCu : 1 ≤ Cu) (hs : s.Nonempty)
    {c b : ℕ} (hc : c ≤ N) (hb : b ≤ N) (hcb : c ≤ b)
    (h2δ : 2 * δ ≤ gridScale δ N c) (h8 : 8 * gridScale δ N c ≤ 1)
    (hbrb : 0 < 𝒰.branchingN b) (hbrc : 0 < 𝒰.branchingN c) :
    ∃ dm Dm : ENNReal, dm ≠ 0 ∧ dm ≠ ⊤ ∧ Dm ≠ ⊤ ∧
      (∀ p ∈ 𝒰.cover.indexSet c, dm ≤ Kakeya.densityIn
          (𝒰.nodesIn b (((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
          (((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody)) ∧
      (∀ p ∈ 𝒰.cover.indexSet c, Kakeya.densityIn
          (𝒰.nodesIn b (((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
          (((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody) ≤ Dm) ∧
      Dm ≤ ((nodeDensityRatioConst (Module.finrank ℝ E) Cu : NNReal) : ENNReal) * dm := by
  let n : ℕ := Module.finrank ℝ E
  let sb : NNReal := gridScale δ N b
  let sc : NNReal := gridScale δ N c
  let X : NNReal := (𝒰.branchingN c * sb ^ (n - 1)) / (𝒰.branchingN b * sc ^ (n - 1))
  let CvLow : NNReal := X / Cu ^ 2
  let CvHi : NNReal := nodeCountSplitConst n Cu * X
  let dm : ENNReal := ((nodeDensityLBConst n * CvLow : NNReal) : ENNReal)
  let Dm : ENNReal := ((nodeDensityUBConst n * CvHi : NNReal) : ENNReal)
  have hCu_pos : 0 < Cu := zero_lt_one.trans_le hCu
  have hCu2_ne : Cu ^ 2 ≠ 0 := (pow_pos hCu_pos 2).ne'
  have hden_ne : 𝒰.branchingN b * sc ^ (n - 1) ≠ 0 :=
    (mul_pos hbrb (pow_pos (gridScale_pos hδ N c) _)).ne'
  have hCvLow_ne : CvLow ≠ 0 :=
    div_ne_zero (div_ne_zero (mul_pos hbrc (pow_pos (gridScale_pos hδ N b) _)).ne' hden_ne) hCu2_ne
  have hL_ne : nodeDensityLBConst n ≠ 0 := by
    rw [nodeDensityLBConst]
    refine div_ne_zero (Tube.le_volume.c_pos n).ne' (mul_pos ?_ (pow_pos (by norm_num) _)).ne'
    unfold Tube.volume_le.C
    positivity
  have hX_identity : X * 𝒰.branchingN b * sc ^ (n - 1) =
      𝒰.branchingN c * sb ^ (n - 1) := by
    rw [mul_assoc]
    exact div_mul_cancel₀ _ hden_ne
  have hcv : (X / Cu ^ 2) * (Cu ^ 2 * 𝒰.branchingN b) * sc ^ (n - 1) =
      X * 𝒰.branchingN b * sc ^ (n - 1) := by
    rw [← mul_assoc, div_mul_cancel₀ _ hCu2_ne]
  have hscaleLow : (CvLow : ENNReal) * ((Cu ^ 2 * 𝒰.branchingN b : NNReal) : ENNReal) *
        ((sc : ENNReal) ^ (n - 1)) ≤
      ((𝒰.branchingN c : NNReal) : ENNReal) * ((sb : ENNReal) ^ (n - 1)) := by
    exact_mod_cast (hcv.trans hX_identity).le
  have hscaleHi : ((nodeCountSplitConst n Cu : NNReal) : ENNReal) *
        ((𝒰.branchingN c : NNReal) : ENNReal) * ((sb : ENNReal) ^ (n - 1)) ≤
      (CvHi : ENNReal) * ((𝒰.branchingN b : NNReal) : ENNReal) * ((sc : ENNReal) ^ (n - 1)) := by
    have hHi : nodeCountSplitConst n Cu * 𝒰.branchingN c * sb ^ (n - 1) =
        CvHi * 𝒰.branchingN b * sc ^ (n - 1) := by
      change _ = nodeCountSplitConst n Cu * X * 𝒰.branchingN b * sc ^ (n - 1)
      rw [mul_assoc, ← hX_identity]
      ring
    exact_mod_cast hHi.le
  have hratio_nn : nodeDensityUBConst n * CvHi ≤
      nodeDensityRatioConst n Cu * (nodeDensityLBConst n * CvLow) := by
    refine le_of_eq ?_
    change _ = nodeDensityUBConst n * nodeCountSplitConst n Cu * Cu ^ 2 / nodeDensityLBConst n
      * (nodeDensityLBConst n * (X / Cu ^ 2))
    rw [div_mul_eq_mul_div, mul_comm (nodeDensityLBConst n), ← mul_assoc,
      mul_div_assoc, mul_div_assoc, div_self hL_ne, mul_one,
      mul_assoc (nodeDensityUBConst n * nodeCountSplitConst n Cu),
      mul_comm (Cu ^ 2) (X / Cu ^ 2), div_mul_cancel₀ _ hCu2_ne]
  refine ⟨dm, Dm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ENNReal.coe_ne_zero.mpr (mul_ne_zero hL_ne hCvLow_ne)
  · exact ENNReal.coe_ne_top
  · exact ENNReal.coe_ne_top
  · exact fun p hp => le_densityIn_nodesIn_rescale_eight_of_branchingN hδ hδ1 𝒰 (Cv := CvLow)
      h8 hcb hb hc hp hCu_pos hbrb hscaleLow
  · exact fun p hp => densityIn_nodesIn_rescale_eight_le_of_branchingN hδ hδ1 𝒰 hCu (Cv := CvHi)
      hc hb hcb hs h2δ hbrb hscaleHi
  · dsimp only [Dm, dm]
    exact_mod_cast hratio_nn

/-! ### The normalisation of a window scale -/

/-- **A scale of the window is at most one.**

The upper endpoint of the window is `ρ_a (ρ_b/ρ_a)^ε`, which is at most `ρ_a ≤ 1`. -/
theorem A.window_scale_le_one {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M a b : ℕ} (hab : a ≤ b)
    {ε : ℝ} (hε : 0 ≤ ε) {ρ : NNReal}
    (hhi : (ρ : ℝ) ≤ (gridScale δ M a : ℝ)
        * ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ ε) :
    ρ ≤ 1 := by
  have hga : (0 : ℝ) < (gridScale δ M a : ℝ) := NNReal.coe_pos.mpr (gridScale_pos hδ M a)
  have hpow : ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ ε ≤ 1 :=
    Real.rpow_le_one (div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
      ((div_le_one hga).2 (NNReal.coe_le_coe.mpr (gridScale_antitone hδ hδ1 M hab))) hε
  have hga1 : (gridScale δ M a : ℝ) ≤ 1 := by exact_mod_cast gridScale_le_one hδ1 M a
  exact_mod_cast hhi.trans ((mul_le_of_le_one_right hga.le hpow).trans hga1)

/-! ### The witness leaf and its two index facts -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A good node has a leaf that carries both index hypotheses of the witness lemma.**  The output
is the pair `hi₀`, `hjj'` demanded by `Kakeya.MultiScaleFac.A.witness_hX_of_alternativeTwo` at the
level-`c` node `j' = a_c(i₀)`, together with `i₀ ∈ G`.  Taking `j'` to be the level-`c` node of the
witness leaf itself is what makes `hjj'` free, by the iterated nesting of the cover system. -/
private theorem A.exists_witness_leaf {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu) (hs : s.Nonempty)
    (𝒰 : UniformTubeSet s T N Cu) {b c : ℕ} (hcb : c ≤ b) (hb : b ≤ N)
    {G : Finset ι} {j : ι} (hj : j ∈ goodNodes 𝒰 b G) :
    ∃ i₀ : ι, i₀ ∈ G ∧ i₀ ∈ s ∧
      i₀ ∈ coverClass s (𝒰.cover.assign b) j ∧
      (𝒰.cover.tube b j).toConvexSpaceBody
        ≤ (𝒰.cover.tube c (𝒰.cover.assign c i₀)).toConvexSpaceBody := by
  obtain ⟨i₀, hi₀cls, hi₀G⟩ := exists_good_mem_coverClass_of_mem_goodNodes hCu hs 𝒰 hb hj
  obtain ⟨hi₀s, hjeq⟩ : i₀ ∈ s ∧ 𝒰.cover.assign b i₀ = j := by simpa [coverClass] using hi₀cls
  exact ⟨i₀, hi₀G, hi₀s, hi₀cls, hjeq ▸ tube_assign_le_of_le 𝒰.cover hcb hb hi₀s⟩

/-! ### The clumping hypothesis, and the bottom scale -/

/-- **The witness lemma's scale hypothesis already excludes the bottom of the grid.**

`ρ_N = δ` (`Tube.gridScale_self`), so `2δ ≤ ρ_c` at `c = N` reads `2δ ≤ δ`, which
forces `δ = 0`.  Hence any index admissible for the witness lemma is strictly above the bottom
scale, which is precisely the range on which `Kakeya.StickyKakeya.GridUniform.clumped` speaks. -/
theorem A.lt_of_two_mul_le_gridScale {δ : NNReal} (hδ : 0 < δ) {N c : ℕ} (hN : 0 < N)
    (hc : c ≤ N) (h2d : 2 * δ ≤ gridScale δ N c) : c < N := by
  refine hc.lt_or_eq.resolve_right fun heq => ?_
  simp [heq, gridScale_self δ hN, two_mul, hδ.ne'] at h2d

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The clumping field of a grid-uniform system, in the shape the witness lemma consumes.**
`Kakeya.StickyKakeya.GridUniform.clumped` is stated at a node `P` of the index set; the witness
lemma asks for it at the level-`c` node of the witness leaf, `P = a_c(i₀)`, which is in the index
set by `assign_mem`.  The bottom scale `c = N` is specified out by `h2δ`. -/
private theorem A.hclump_of_gridUniform {δ : NNReal} (hδ : 0 < δ) {t : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cv : NNReal} (hN : 0 < N) (𝒢 : GridUniform t T N Cv)
    {c : ℕ} (hc : c ≤ N) (h2d : 2 * δ ≤ gridScale δ N c) {i₀ : ι} (hi₀ : i₀ ∈ t) :
    ∃ i₂ : ι, coverClass t (𝒢.toUniformTubeSet.cover.assign c)
        (𝒢.toUniformTubeSet.cover.assign c i₀)
      ⊆ fibreIndex t T δ (gridScale δ N c / 4) i₂ :=
  𝒢.clumped c (A.lt_of_two_mul_le_gridScale hδ hN hc h2d) (𝒢.cover.assign c i₀)
    (𝒢.cover.assign_mem c hc i₀ hi₀)

/-! ### The factor `32` of the rounding, paid by grid steps -/

/-- **One grid step of gap loss is at least `16`.**

`Kakeya.MultiScaleFac.scaleGapLoss 1 δ` is `δ^{-1/M}` with `M = ssfGridLen δ`, and the standing
smallness `δ ≤ 16^{-M}` of the sharp dichotomy says exactly that this is at least `16`. -/
private theorem A.sixteen_le_scaleGapLoss_one {δ : NNReal} (hδ : 0 < δ)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ) :
    (16 : ℝ) ≤ scaleGapLoss 1 δ := by
  have hMR : (0 : ℝ) < (ssfGridLen δ : ℝ) := by exact_mod_cast hM
  have hd16 : (δ : ℝ) ≤ (16 : ℝ) ^ (-(ssfGridLen δ : ℝ)) := by
    simpa [NNReal.coe_rpow] using NNReal.coe_le_coe.mpr hδ16
  rw [show scaleGapLoss 1 δ = (δ : ℝ) ^ ((-1 : ℝ) / (ssfGridLen δ : ℝ)) by
    norm_num [scaleGapLoss, neg_div]]
  calc (16 : ℝ) = ((16 : ℝ) ^ (-(ssfGridLen δ : ℝ))) ^ ((-1 : ℝ) / (ssfGridLen δ : ℝ)) := by
        rw [← Real.rpow_mul (by norm_num), show -(ssfGridLen δ : ℝ) * ((-1 : ℝ) /
          (ssfGridLen δ : ℝ)) = 1 by
          rw [neg_div, mul_neg, neg_mul, neg_neg, mul_one_div, div_self hMR.ne'], Real.rpow_one]
    _ ≤ (δ : ℝ) ^ ((-1 : ℝ) / (ssfGridLen δ : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (NNReal.coe_pos.mpr hδ) hd16
          (by rw [neg_div, neg_nonpos]; exact div_nonneg zero_le_one hMR.le)

/-- **The rounding factor `32 Λ₁` fits inside the six-step gap loss.**

`Kakeya.MultiScaleFac.A.exists_round_index_sharp` returns `ρ ≤ 32 Λ₁ σ_c`, while
`Kakeya.MultiScaleFac.A.witness_hX_of_alternativeTwo` consumes `ρ ≤ L σ_c` with
`L ≤ scaleGapLoss k δ`.  Five extra grid steps pay the `32`, since each is worth at least `16`. -/
theorem A.thirtyTwo_mul_scaleGapLoss_one_le {δ : NNReal} (hδ : 0 < δ)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ) :
    32 * scaleGapLoss 1 δ ≤ scaleGapLoss 6 δ := by
  have h16 : (16 : ℝ) ≤ scaleGapLoss 1 δ := A.sixteen_le_scaleGapLoss_one hδ hδ16 hM
  have h32 : (32 : ℝ) ≤ scaleGapLoss 5 δ :=
    A.scaleGapLoss_pow hδ 1 5 ▸ le_trans (by norm_num : (32 : ℝ) ≤ (16 : ℝ) ^ 5)
      (pow_le_pow_left₀ (by norm_num) h16 5)
  calc 32 * scaleGapLoss 1 δ ≤ scaleGapLoss 5 δ * scaleGapLoss 1 δ :=
        mul_le_mul_of_nonneg_right h32 (by linarith)
    _ = scaleGapLoss 6 δ := by rw [mul_comm]; exact A.scaleGapLoss_add hδ 1 5

/-- **The rounding factor is at least `1`**, the normalisation the reading asks of `L`. -/
theorem A.one_le_thirtyTwo_mul_scaleGapLoss_one {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 : ℝ) ≤ 32 * scaleGapLoss 1 δ := by
  linarith [one_le_scaleGapLoss 1 hδ hδ1]

/-! ### The window bookkeeping -/

/-- **A nonempty gap budget forces a nondegenerate block.**

The rounding index needs the strict `a < b`, which the reading does not; it is already contained in
the gap hypothesis, since a degenerate block makes the product vanish. -/
theorem A.lt_of_six_le_window_gap {e e' : ℝ} {a b : ℕ} (hee' : e ≤ e')
    (hk : (6 : ℝ) ≤ (e' - e) * ((b : ℝ) - (a : ℝ))) : a < b := by
  by_contra! hcon
  have hba : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hcon
  linarith [mul_nonneg (sub_nonneg.2 hee') (sub_nonneg.2 hba)]

/-- **The gap budget of the two windows pays the rounding budget.**

The rounding asks `3 ≤ e' (b - a)`; the reading is given the stronger `6 ≤ (e' - e)(b - a)`, and
`e ≥ 0` makes the narrower exponent the larger one. -/
theorem A.three_le_window_exp_mul {e e' : ℝ} {a b : ℕ} (he : 0 ≤ e) (hab : a ≤ b)
    (hk : (6 : ℝ) ≤ (e' - e) * ((b : ℝ) - (a : ℝ))) :
    3 ≤ e' * ((b : ℝ) - (a : ℝ)) := by
  rw [sub_mul] at hk
  linarith [mul_nonneg he (sub_nonneg.2 (Nat.cast_le.2 hab : (a : ℝ) ≤ (b : ℝ)))]

/-! ### Two transfers of shape -/

/-- **The lower scale bound of the reading, from the rounding.**

The rounding returns `32 σ_c ≤ ρ` in `NNReal`; the reading asks for `σ_c ≤ ρ` in `ℝ`. -/
theorem A.gridScale_le_of_thirtyTwo_mul_le {δ : NNReal} {N c : ℕ} {rho : NNReal}
    (h : 32 * gridScale δ N c ≤ rho) :
    (gridScale δ N c : ℝ) ≤ (rho : ℝ) :=
  NNReal.coe_le_coe.mpr ((le_mul_of_one_le_left zero_le (by norm_num)).trans h)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The uniformity constant of the induced uniform set of tubes is at least `1`.**

`Kakeya.MultiScaleFac.uniformTubeSetCuOf` bumps the ambient constant above the tight net
multiplicity, so it dominates the ambient constant, hence `1`. -/
private theorem A.one_le_uniformTubeSetCuOf {Cv : NNReal} (hCv : 1 ≤ Cv) :
    1 ≤ uniformTubeSetCuOf (E := E) Cv :=
  hCv.trans (le_max_left _ _)

/-! ### The reading at a fixed grid level -/

/-- **The terminal alternative, read at a prescribed grid level.**  Steps two and three of the
per-scale assembly: the good node `j` yields a witness leaf `i₀` of the majority set `G`, its
level-`c` node `j' = a_c(i₀)` carries the containment `hjj'` for free, the clumping comes from the
grid-uniform structure, and `A.witness_hX_of_alternativeTwo` then reads the alternative at `σ_c`.
The membership `j' ∈ indexSet c` is returned alongside. -/
theorem A.narrow_witness_hX_at_index {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlt : (δ : ℝ) < 1) (hM : 0 < ssfGridLen δ)
    {s : Finset ι} {T : ι → Tube δ E} {Cv : NNReal} (hCv : 1 ≤ Cv) (hs : s.Nonempty)
    (𝒢 : GridUniform s T (ssfGridLen δ) Cv)
    {zeta : ℝ} (hz0 : 0 ≤ zeta) (hz1 : zeta ≤ 1)
    {a b c : ℕ} (hab : a ≤ b) (hb : b ≤ ssfGridLen δ) (hc : c ≤ ssfGridLen δ) (hcb : c ≤ b)
    (h2d : 2 * δ ≤ gridScale δ (ssfGridLen δ) c)
    {e e' : ℝ} {k : ℕ} {L : ℝ} (he : 0 ≤ e) (hee' : e ≤ e')
    (hk : (k : ℝ) ≤ (e' - e) * ((b : ℝ) - (a : ℝ))) (hL1 : 1 ≤ L)
    (hL : L ≤ scaleGapLoss k δ)
    {rho : NNReal}
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e' ≤ (rho : ℝ))
    (hhi : (rho : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e')
    (hsr : (gridScale δ (ssfGridLen δ) c : ℝ) ≤ (rho : ℝ))
    (hrs : (rho : ℝ) ≤ L * (gridScale δ (ssfGridLen δ) c : ℝ))
    {G : Finset ι} {j : ι} (hj : j ∈ goodNodes 𝒢.toUniformTubeSet b G)
    {D0 : ENNReal}
    (hAlt : ∀ i ∈ G, ∀ r : NNReal,
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e ≤ (r : ℝ) →
      (r : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e →
      ENNReal.ofReal (((r : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta)
        ≤ D0 * ConvexSpaceBody.frostmanConstant (fibreIndex s T δ r i)
            (fibreBodies T (gridScale δ (ssfGridLen δ) b))
            ((T i).rescale (2 * r)).toConvexSpaceBody) :
    ∃ j' ∈ 𝒢.toUniformTubeSet.cover.indexSet c,
      ENNReal.ofReal (((rho : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta)
        ≤ ENNReal.ofReal L * (D0 * ((fibreFromNodeConst (E := E) : ENNReal)
            * ((uniformTubeSetCuOf (E := E) Cv : NNReal) : ENNReal) ^ 5))
            * ConvexSpaceBody.frostmanConstant
                (𝒢.toUniformTubeSet.nodesIn b ((𝒢.toUniformTubeSet.cover.tube c j').rescale
                    (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)
                (fun w => (𝒢.toUniformTubeSet.cover.tube b w).toConvexSpaceBody)
                ((𝒢.toUniformTubeSet.cover.tube c j').rescale
                    (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody := by
  obtain ⟨i0, hi0G, hi0s, hi0cls, hjj'⟩ :=
    A.exists_witness_leaf (A.one_le_uniformTubeSetCuOf hCv) hs 𝒢.toUniformTubeSet hcb hb hj
  exact ⟨_, 𝒢.toUniformTubeSet.cover.assign_mem c hc i0 hi0s,
    A.witness_hX_of_alternativeTwo hδ hδ1 hδlt hM (A.one_le_uniformTubeSetCuOf hCv)
      𝒢.toUniformTubeSet hz0 hz1 hab hb hc hcb h2d he hee' hk hL1 hL hlo hhi hsr hrs hi0cls hjj'
      (A.hclump_of_gridUniform hδ hM 𝒢 hc h2d hi0s) (hAlt i0 hi0G)⟩

/-! ### The per-scale package -/

end MultiScaleFac
end Kakeya

end
