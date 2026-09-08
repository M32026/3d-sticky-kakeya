/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeNodeCount
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorBookkeeping
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale

/-!
# `R6` — the genuine parent precedes the whole middle window

(3) and §2.6.  The refined source disposes of this in the clause *"before
the whole window"* (l.4136) and never proves it;  calls it "the one quantitative
step the source compresses".  It is elementary, and this file compiles it.

## The argument, in one line

**A polynomial beats a constant.**  At the window's coarsest inset level
`m₀ = a + ⌈ε_div(b−a)⌉₊`, the twin's level clause `le_level_maxDensity` forces the level-`m₀`
maximal density up to `Θ_{m₀}^τ / C_⋆`, and `Kakeya.ML2Core.ratio_ge_of_ceil_window` (F6) gives
`Θ_{m₀} ≥ δ^{-ε_div²}`, so that density is at least `δ^{-ε_div²τ}/C_⋆` — a genuine **negative power
of `δ`**.  If the level-`m₀` cells all crossed into a single node at the level `q = m₀`, then
`Kakeya.ML2Core.card_nodesUnder_le_coverCount'` (`R6b`) would cap the same density by
`2·100^{2n}·Cu`, which carries **no `δ`-power at all**.  The two are incompatible, so `q ≠ m₀`; with
`q ≤ m₀` that is `q < m₀ = min 𝒲`. ∎

## ⚠ The binder this needs, and it is **not** the site's current one

The contradiction is `C_⋆ · 2 · 100^{2n} · Cu < δ^{-ε_div²τ}`, named `hbudget` below.  It is a
**joint** budget on the window constant and the hierarchy constant, and `ε_div²τ` is a very small
positive exponent.

**The site's existing binder is `(Cu : ℝ) ≤ δ^{-1}`, which is far too weak
for it**: at `Cu ≍ δ^{-1}` the right-hand side is beaten and no contradiction exists at any `q`.
 wrote `C_ess := 2·25^6·Cu` and then treated it as `O(1)`, which silently
assumes `Cu` is `δ`-free.  **That assumption is load-bearing and it is not in the tree.**  Carrying
it as the explicit hypothesis `hbudget` is the honest rendering: the site must supply a
subpolynomial `Cu` — anything `≤ δ^{-ε_div²τ/4}` will do, with a threshold absorbing the absolute
constant `2·100^{2n}` and the window constant `C_⋆ ≤ δ^{-ν/20}` — or `R6` has no proof.  Flagged for
 and for the site owner; nothing here hides it.

's asymmetry is unaffected and is re-raised: the tree's grid length
`Tube.ssfGridLen δ = ⌈log log(1/δ)⌉₊` **grows with `δ`**, where the source's `M` is fixed before
`δ`.  The tree can run this argument and the source cannot, so its fidelity has no external check.

## Contents

* `Kakeya.ML2Core.maxDensity_le_card_nodesUnder_of_crossing` — the crossing turns the level-`m₀`
  maximal density into a node count under `jq`.
* `Kakeya.ML2Core.not_crossing_at_window_level` — the contradiction at `q = m₀`.
* `Kakeya.ML2Core.crossing_lt_window` — **`R6`**.
* `Kakeya.ML2Core.hbudget_fails_at_polynomial_Cu` — the firing control: at `Cu = δ^{-1}` the budget
  is unsatisfiable for every small exponent, so the binder above is not decoration.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Parent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cst : NNReal} {s : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] in
/-- **The crossing, read as a node count.**  If every level-`c` cell under `jθ` lies inside the
single level-`q` node `jq`, then those cells are among the level-`c` nodes under `jq`, and the
maximal density of the former is at most the *cardinality* of the latter
(`Kakeya.maxDensity_le_card`). -/
theorem maxDensity_le_card_nodesUnder_of_crossing (𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cst)
    {a c q : ℕ} {jθ jq : ι}
    (hcross : ∀ j' ∈ 𝒰.nodesUnder c a jθ,
      (𝒰.cover.tube c j').toConvexSpaceBody ≤ (𝒰.cover.tube q jq).toConvexSpaceBody) :
    Kakeya.maxDensity (𝒰.nodesUnder c a jθ) (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ ((𝒰.nodesUnder c q jq).card : ℝ≥0∞) := by
  classical
  have hsub : 𝒰.nodesUnder c a jθ ⊆ 𝒰.nodesUnder c q jq := by
    intro j' hj'
    have hj'' := hj'
    rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff] at hj''
    rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff]
    exact ⟨hj''.1, hcross j' hj'⟩
  refine (Kakeya.maxDensity_le_card _ _).trans ?_
  exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)

open scoped Classical in
/-- The budget hypothesis yields a contradiction when `q = m₀`. -/
theorem not_crossing_at_window_level (𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cst)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hs : s.Nonempty) (hN0 : 0 < ssfGridLen δ)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N a b m m₀ : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m)
    (hεd : 0 ≤ εd) (hτ : 0 ≤ η (m + 1))
    (hm₀ : a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m₀)
    (hm₀hi : m₀ + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b)
    (hm₀N : m₀ ≤ ssfGridLen δ)
    (h2δ : 2 * δ ≤ gridScale δ (ssfGridLen δ) m₀)
    {jθ jq : ι} (hjθ : jθ ∈ 𝒰.cover.indexSet a) (hjq : jq ∈ 𝒰.cover.indexSet m₀)
    (hcross : ∀ j' ∈ 𝒰.nodesUnder m₀ a jθ,
      (𝒰.cover.tube m₀ j').toConvexSpaceBody ≤ (𝒰.cover.tube m₀ jq).toConvexSpaceBody)
    (hbudget : Cstar
        * ENNReal.ofReal (2 * (100 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cst : ℝ))
      < ENNReal.ofReal ((δ : ℝ) ^ (-(εd ^ 2 * η (m + 1))))) :
    False := by
  classical
  have hδr : (0 : ℝ) < (δ : ℝ) := hδ0
  have hρnn : 0 < gridScale δ (ssfGridLen δ) m₀ := gridScale_pos hδ0 _ _
  have hρpos : (0 : ℝ) < ((gridScale δ (ssfGridLen δ) m₀ : NNReal) : ℝ) := hρnn
  -- W1: the twin's level clause at `m₀`
  have hW1 := hwin.le_level_maxDensity m₀ hm₀ hm₀hi jθ hjθ
  -- F6: the window ratio is a genuine negative power of `δ`
  have hF6 : (δ : ℝ) ^ (-(εd ^ 2))
      ≤ ((gridScale δ (ssfGridLen δ) a : NNReal) : ℝ)
        / ((gridScale δ (ssfGridLen δ) m₀ : NNReal) : ℝ) :=
    ratio_ge_of_ceil_window hδ0 hδ1 hN0 hεd hwin.scale_sep hm₀
  have hpow : (δ : ℝ) ^ (-(εd ^ 2 * η (m + 1)))
      ≤ (((gridScale δ (ssfGridLen δ) a : NNReal) : ℝ)
          / ((gridScale δ (ssfGridLen δ) m₀ : NNReal) : ℝ)) ^ η (m + 1) := by
    have hrw : (δ : ℝ) ^ (-(εd ^ 2 * η (m + 1)))
        = ((δ : ℝ) ^ (-(εd ^ 2))) ^ η (m + 1) := by
      rw [← Real.rpow_mul hδr.le]
      ring_nf
    rw [hrw]
    exact Real.rpow_le_rpow (Real.rpow_pos_of_pos hδr _).le hF6 hτ
  -- `R6b` at `k = c = m₀`: the node count under `jq` carries no `δ`-power
  have hle4 : gridScale δ (ssfGridLen δ) m₀ ≤ 4 * gridScale δ (ssfGridLen δ) m₀ := by
    nth_rewrite 1 [← one_mul (gridScale δ (ssfGridLen δ) m₀)]
    gcongr
    norm_num
  have hR6b := card_nodesUnder_le_coverCount' 𝒰 hs hm₀N hm₀N hρnn h2δ hle4 hjq
  have hratio1 : (((gridScale δ (ssfGridLen δ) m₀ : NNReal) : ℝ)
      / ((gridScale δ (ssfGridLen δ) m₀ : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E) = 1 := by
    rw [div_self hρpos.ne']
    simp
  rw [hratio1, mul_one] at hR6b
  -- assemble in `ℝ≥0∞`
  have hcardE : ((𝒰.nodesUnder m₀ m₀ jq).card : ℝ≥0∞)
      ≤ ENNReal.ofReal (2 * (100 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cst : ℝ)) := by
    have := ENNReal.ofReal_le_ofReal hR6b
    rwa [ENNReal.ofReal_natCast] at this
  have hchain : ENNReal.ofReal ((δ : ℝ) ^ (-(εd ^ 2 * η (m + 1))))
      ≤ Cstar * ENNReal.ofReal (2 * (100 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cst : ℝ)) := by
    calc ENNReal.ofReal ((δ : ℝ) ^ (-(εd ^ 2 * η (m + 1))))
        ≤ ENNReal.ofReal ((((gridScale δ (ssfGridLen δ) a : NNReal) : ℝ)
              / ((gridScale δ (ssfGridLen δ) m₀ : NNReal) : ℝ)) ^ η (m + 1)) :=
          ENNReal.ofReal_le_ofReal hpow
      _ ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder m₀ a jθ)
              (fun j' => (𝒰.cover.tube m₀ j').toConvexSpaceBody) := hW1
      _ ≤ Cstar * ((𝒰.nodesUnder m₀ m₀ jq).card : ℝ≥0∞) := by
          gcongr
          exact maxDensity_le_card_nodesUnder_of_crossing 𝒰 hcross
      _ ≤ Cstar * ENNReal.ofReal (2 * (100 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cst : ℝ)) := by
          gcongr
  exact absurd hchain (not_le.mpr hbudget)

open scoped Classical in
/-- **`R6` — the genuine parent precedes the whole middle window.**  The crossing level of the
window's coarsest inset level is strictly coarser than that level, hence strictly coarser than every
level of `𝒲`. -/
theorem crossing_lt_window (𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cst)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hs : s.Nonempty) (hN0 : 0 < ssfGridLen δ)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N a b m m₀ q : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m)
    (hεd : 0 ≤ εd) (hτ : 0 ≤ η (m + 1))
    (hm₀ : a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m₀)
    (hm₀hi : m₀ + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b)
    (hm₀N : m₀ ≤ ssfGridLen δ)
    (h2δ : 2 * δ ≤ gridScale δ (ssfGridLen δ) m₀)
    (hqm₀ : q ≤ m₀)
    {jθ jq : ι} (hjθ : jθ ∈ 𝒰.cover.indexSet a) (hjq : jq ∈ 𝒰.cover.indexSet q)
    (hcross : ∀ j' ∈ 𝒰.nodesUnder m₀ a jθ,
      (𝒰.cover.tube m₀ j').toConvexSpaceBody ≤ (𝒰.cover.tube q jq).toConvexSpaceBody)
    (hbudget : Cstar
        * ENNReal.ofReal (2 * (100 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cst : ℝ))
      < ENNReal.ofReal ((δ : ℝ) ^ (-(εd ^ 2 * η (m + 1))))) :
    q < m₀ := by
  refine lt_of_le_of_ne hqm₀ (fun hq => ?_)
  subst hq
  exact not_crossing_at_window_level 𝒰 hδ0 hδ1 hs hN0 hwin hεd hτ hm₀ hm₀hi hm₀N h2δ
    hjθ hjq hcross hbudget

/-- **Firing control: `hbudget` is not decoration.**  At `Cu ≍ δ^{-1}` — which is exactly what the
site's existing binder permits — the budget is **unsatisfiable** for every exponent below `1`, even
with `C_⋆ = 1`: the right-hand side `δ^{-e}` is dominated by `δ^{-1}` as soon as `e ≤ 1` and
`δ < 1`.  So `R6` genuinely requires a *subpolynomial* hierarchy constant, and reading
's `C_ess` as `O(1)` was the step that hid it. -/
theorem hbudget_fails_at_polynomial_Cu {d e : ℝ} (hd0 : 0 < d) (hd1 : d < 1)
    (_he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ¬ ((1 : ℝ≥0∞) * ENNReal.ofReal (d ^ (-(1 : ℝ))) < ENNReal.ofReal (d ^ (-e))) := by
  rw [one_mul]
  refine not_lt.mpr (ENNReal.ofReal_le_ofReal ?_)
  exact Real.rpow_le_rpow_of_exponent_ge hd0 hd1.le (by linarith)

end Parent

end Kakeya.ML2Core
