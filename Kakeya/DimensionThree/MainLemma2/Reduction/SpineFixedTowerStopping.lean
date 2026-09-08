/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineWindowRestrictionTransport

/-!
# The dividing-scales stopping time, run on a **fixed** tower

**This file corrects a finding of my own.**  `SpineWindowRestrictionTransport.lean` recorded the
fixed-tower stopping engine as *"the first row of this run with no existing engine reachable by
restatement"*, on the ground that `exists_maximal_cutsKT_hoisted_blocks_core`
(`MultiScaleFac/StoppingKT.lean:517`) has **no hierarchy argument** and manufactures
`𝒢L : GridUniform tL T Mgrid Cv`.

That measurement was right about *that* declaration and **wrong about the engine**.  One layer
further down, `Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin`
(`MultiScaleFac/Stopping.lean:312`) is **fully abstract**: it quantifies over a state type `σ` and
over `Good`, `Test`, `Long`, `Rel` as bare predicates, and mentions no grid, no tower and no tube.
It is the tree's `lemabstractstopping` (source l.5254-5283), and the KT half already *"reuses that
file's combinatorial skeleton verbatim; only the tracked quantity changes"*
(`StoppingKTBase.lean` docstring).

So the grid manufacture lives in the **instantiation**, not in the engine, and the engine runs on a
fixed tower unchanged.  `exists_fixedTowerCuts` below is that run,.

## What the source does, and what is therefore left

Source l.2731-2745, part (B): put `Z(k,l) = max_{S∈𝕋_k} Δ_max(𝕋_l⟨S⟩)`, transpose to
`X̃(k,l) = Z(M-l, M-k)`, obtain submultiplicativity (H1) with constant `300^9 C_2`, the crude
exponent `d = 4` (H2) from the cardinality estimate, and the entry bound (H3) from the top-cell
estimate; apply `lemabstractstopping` and undo the indices to get
`eqdividingKfirst`-`eqdividingKwitness` (l.2695-2703).

`towerDensityArray` is `Z`, read on the fixed tower.  `exists_fixedTowerCuts` is the application of
the stopping lemma.  **What is not in this file** is the geometry that feeds it — H1, H2 and the
`hsplit` calibration — and the read-back into `ML2Reduction.IsKatzTaoDividingWindowLevels`'s three
fields; those are named as the hypotheses of `exists_fixedTowerCuts` and in
`Kakeya.ML2Core.FixedTowerStoppingObligation`.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `towerDensityArray` | the fixed tower's family `s`, cover data of `𝒰`; **no shading** | the pair `(k,l)`, both free |
| `TowerGood` | as above | the piece `(a,b)` |
| `exists_fixedTowerCuts` | as above — the tower is **fixed**: no `𝒢L`, no `.mono` onto a fresh hierarchy | the cut set `S ⊆ range (M+1)`; the window pair `(a,b)` is a maximal piece of it |

Nothing here touches a shading: the dividing-scales dichotomy is about tubes and densities only.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section FixedTowerStopping

variable {ι : Type*} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`Z(k,l) = max_{S∈𝕋_k} Δ_max(𝕋_l⟨S⟩)`** (source l.2731-2733), read on a **fixed** tower.

**The monotonicity sentence, kept here because it is the root of three of this run's findings.**
Source **l.4392-4394**:

> *"Perform all factorings and all mass-coupled pigeonholings in the window **before** testing its
> asserted lower concentration.  This order is essential: **maximal density is monotone under
> restriction, but a lower density and a cell fullness are not.**"*

That one sentence explains, and should stop the next hand from rediscovering:

1. why `le_window_maxDensity` — a **lower** bound on a `maxDensity` — does not descend to the
   inherited tower, while the two upper-bound fields do
   (`Kakeya.ML2Core.levelDensityBand_upper_of_subset`, and its witness
   `maxDensity_coverClass_image_mono`);
2. why the `(D)` trigger must be tested **after** the refinement and not before — the defect that
   `Kakeya.ML2Core.defectBranchAt_of_concentration_destroyed` fixed;
3. why `R0b` needs a genuinely **mass-weighted** selection: cell fullness is a ratio of sums and is
   not monotone under restriction either, so `Kakeya.ML2Core.goodMassSet` selects by individual
   shaded mass rather than by count.

**Family/shading:** the fixed tower's family `s` with `𝒰`'s cover; **no shading enters**.
**Level pair:** `(k,l)`, both free. -/
noncomputable def towerDensityArray
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (k l : ℕ) : ENNReal :=
  (𝒰.cover.indexSet k).sup (fun j =>
    Kakeya.maxDensity (𝒰.nodesUnder l k j)
      (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody))

/-- Piece-admissibility of the source's stopping argument (l.5286-5288: *"`X(c_{j-1},c_j) ≤
r(c_{j-1},c_j)^{-η_J}`"*), read on the fixed tower.  The bound family is supplied rather than
inlined, so that no constant of l.2621-2705 is fitted here. -/
def TowerGood (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (bound : ℕ → ℕ → ℕ → ENNReal) (j a b : ℕ) (_ : Unit) : Prop :=
  towerDensityArray 𝒰 a b ≤ bound j a b

/-- **The stopping engine with the hierarchy in the hypotheses** — `lemabstractstopping`
(l.5254-5283) run on a **supplied** tower.

The tower is fixed: no `𝒢L` is built and there is no `.mono` onto a fresh `UniformTubeSet`.  This
is the declaration whose absence was reported as the run's one row with no existing engine; the
engine was `Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin` all along, and the
state type is instantiated at `Unit` precisely *because* nothing needs refining when the tower does
not move.

Its three hypotheses are the source's, and they are exactly what remains:

* `hGood` — the entry bound, `(H3)` of l.5265, on the fixed tower;
* `hmono` — `η`-monotonicity of the piece bound, from `η_1 ≤ ⋯ ≤ η_{N+1}`;
* `hsplit` — the source's *"insert `m`"* step, l.5289-5297, whose calibration is
  `δ^{-ε²η₁/2} ≥ E`.

**Family/shading:** the fixed tower `𝒰` on `(s,T)`; no shading.  **Level pair:** the output is the
maximal admissible cut set `S`; each adjacent pair `(a,b)` in `S` is a candidate window. -/
theorem exists_fixedTowerCuts
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (M N w : ℕ) (hw : 0 < w) (hwM : w ≤ M) (hwN : M ≤ w * N)
    (bound : ℕ → ℕ → ℕ → ENNReal)
    (Test : ℕ → ℕ → ℕ → Unit → Prop) (Long : ℕ → ℕ → Prop)
    (hGood : TowerGood 𝒰 bound 0 0 M ())
    (hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b →
      TowerGood 𝒰 bound j a b () → TowerGood 𝒰 bound j' a b ())
    (hsplit : ∀ j a b : ℕ, j + 1 ≤ N → a < b → b ≤ M → Long a b →
      TowerGood 𝒰 bound j a b () → Test (j + 1) a b () →
      ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧
        TowerGood 𝒰 bound (j + 1) a c () ∧ TowerGood 𝒰 bound (j + 1) c b ()) :
    ∃ (S : Finset ℕ) (m : ℕ), m < N ∧ 0 ∈ S ∧ M ∈ S ∧
      S ⊆ Finset.range (M + 1) ∧ S.card = m + 2 ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
        TowerGood 𝒰 bound m a b () ∧ (¬ Long a b ∨ ¬ Test (m + 1) a b ()) := by
  obtain ⟨S, m, x, hmN, -, h0, hM, hsub, hcard, hpieces⟩ :=
    Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin (σ := Unit) M N w hw hwM hwN
      (fun j a b x => TowerGood 𝒰 bound j a b x) Test Long
      (fun _ _ _ => True) ()
      (fun _ => trivial) (fun _ _ _ _ _ _ _ => trivial) hGood
      (fun j j' hjj' hj'N a b hab x hg => hmono j j' hjj' hj'N a b hab hg)
      (fun _ _ _ _ _ _ _ _ hg => hg)
      (fun j a b hjN hab hbM hlong x hg htest => by
        obtain ⟨c, h1, h2, h3, h4⟩ := hsplit j a b hjN hab hbM hlong hg htest
        exact ⟨(), c, trivial, h1, h2, h3, h4⟩)
  exact ⟨S, m, hmN, h0, hM, hsub, hcard, fun a ha b hb hab hadj => hpieces a ha b hb hab hadj⟩

/-! ### Item 2, `hmono`: the source's schedule, copied -/

/-- **`hmono` from a monotone bound family.**  `TowerGood` is a bound on a fixed quantity, so the
`η`-monotonicity the stopping time needs is exactly monotonicity of the bound in `j`. -/
theorem towerGood_mono_of_bound_mono
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu} {bound : ℕ → ℕ → ℕ → ENNReal}
    (hb : ∀ j j' a b : ℕ, j ≤ j' → bound j a b ≤ bound j' a b)
    {j j' a b : ℕ} (hjj' : j ≤ j') (h : TowerGood 𝒰 bound j a b ()) :
    TowerGood 𝒰 bound j' a b () := le_trans h (hb j j' a b hjj')

/-- **The source's piece bound, `r(a,b)^{-η_J}`** (l.5288), written as `(1/r)^{η_J}` with the
inverse ratio supplied so that no scale convention is fitted here. -/
noncomputable def sourceBound (rinv : ℕ → ℕ → ℝ) (η : ℕ → ℝ) (j a b : ℕ) : ENNReal :=
  ENNReal.ofReal ((rinv a b) ^ (η j))

/-- **The schedule is monotone**, from `η_1 ≤ ⋯ ≤ η_{N+1}` (l.5257-5259) and `r(a,b) ≤ 1`, i.e.
`1 ≤ 1/r(a,b)`.  Copied, not fitted: the only inputs are the source's own `η`-ordering and the
direction of the scale ratio. -/
theorem sourceBound_mono {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ}
    (hr : ∀ a b : ℕ, 1 ≤ rinv a b) (hη : ∀ j j' : ℕ, j ≤ j' → η j ≤ η j')
    (j j' a b : ℕ) (hjj' : j ≤ j') :
    sourceBound rinv η j a b ≤ sourceBound rinv η j' a b := by
  refine ENNReal.ofReal_le_ofReal ?_
  exact Real.rpow_le_rpow_of_exponent_le (hr a b) (hη j j' hjj')

/-! ### The one obligation that is NOT numerical: a data-model divergence

Items H1, H2 and the read-back cannot be discharged by reusing the tree's existing Katz-Tao stopping
alternatives, and the obstruction is **not** effort — the tree states it at
`Kakeya/Uniform.lean:69-71`:

> *"`UniformTubeSet` is that object: the hierarchy `cover`, together with Definition 2.1(ii)-(iii)
> read directly on the classes of that hierarchy.  **Nothing bundles a per-scale
> `Tube.IsUniformAtScale`, because the containment reading of Definition 2.1(iii) cannot supply the
> lower bound on a class**: a node may contain members of other classes."*

The existing KT machinery — `MultiScaleFac.BlockKatzTao`, `BlockKatzTaoAt.mono` (documented as *"the
`hmono` hypothesis of `exists_maximal_cuts_abstract`"*), `alternativeOneKT_of_cutsKT`,
`alternativeTwoKT_of_terminal_block` — is all stated over
`u : ∀ k ≤ N, Tube.IsUniformAtScale s T (gridScale δ N k) Cu`.  A `GridUniform` carries exactly
that (`FibreCommon.lean:745` `uniformAt`, with `parent_eq`/`tube_eq` and *"the branching lower bound
on the class"*); a `UniformTubeSet` **deliberately does not**.

**That is why `dividingScalesKatzTao` builds `𝒢L`.**  It is not laziness in the producer and not a
wiring gap: the KT stopping alternatives need per-scale uniformity witnesses, and the nested model
`FloorDataAtTrichotomy` is written over cannot supply them.  Note the reason once more — a **lower**
bound (on a class) is what fails, the same direction that blocks `le_window_maxDensity`, the `(D)`
trigger's ordering, and cell fullness (see `towerDensityArray`'s docstring).

`TowerUniformAtScaleData` names the exact missing object.  It is a **design question, not a proof
obligation**: either the nested model is equipped with per-scale witnesses, or the KT alternatives
are restated over classes, or the payload row is written over `GridUniform`.  Not decided here. -/

/-- **The per-scale uniformity witnesses** that the existing Katz-Tao stopping alternatives require.

**NOT missing — see `towerUniformAtScaleData_of_uniformTubeSet` immediately below.**  This `def`
was introduced as the name of a gap; the gap does not exist.

**Family/shading:** the fixed tower's `s` and `T`; no shading.  **Level pair:** none — this is
per-scale data, one witness per grid level `k ≤ N`. -/
def TowerUniformAtScaleData (_𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (N : ℕ)
    (C : NNReal) : Prop :=
  Nonempty (∀ k, k ≤ N → Tube.IsUniformAtScale s T (Tube.gridScale δ N k) C)

/-- **The gap is not there: a bare `UniformTubeSet` supplies the per-scale witnesses.**

`Tube.UniformTubeSet.toChain` (`ChainUniform.lean:211`) followed by
`Tube.ChainUniformTubeSet.uniformAt` (`:374`) gives `Tube.IsUniformAtScale` at every grid level,
from nothing but `1 ≤ Cu`.  The route is named in the tree already
(`Plank/Prop66BUniformityShapes.lean:139`: *"is `Tube.UniformTubeSet.toChain` followed by
`Tube.ChainUniformTubeSet.uniformAt`"*).

**This refutes two things, one of them mine.**

1. My own reading, that the nested model *cannot* carry per-scale uniformity.  It can.
2. 's cost argument, that the containment **upper** bound *"is what a nested
   node cannot supply"* and *"returns under ED levels"*.  It returns **without** ED:
   `Tube.ChainUniformTubeSet.card_filter_le` (`ChainUniform.lean:247`) derives it from
   **Definition 2.1(ii), bounded overlap** — its docstring: *"a contained leaf is assigned to one
   of the at most `C` nodes that the bounded-overlap clause permits to meet that node"* — at the
   price `C → C²`.  No level essential-distinctness is used anywhere in it.

Note also that `Tube.UniformTubeSet` carries Definition 2.1(iii) **natively**, as the two fields
`card_class_le` / `le_card_class` on `coverClass` (`ChainUniform.lean:205-208`); `IsClassHomogeneousOn`
is the per-`S` version of the same band.  So both readings of 2.1(iii) are available on the nested
model, and the conversion between them costs one square of the uniformity constant.

**Consequence for routing.**  The ~40-site class-reading re-proof of the Katz-Tao chain (route (b))
is **not required** to run the stopping argument on a fixed tower: the containment reading is
reachable from the fixed tower directly.  Whether the `Cu²` is affordable at the call site, and
whether the fidelity objection to the containment reading still stands once its cost is `Cu²`
rather than ED, are source calls, not this file's.

**Family/shading:** the fixed tower's `s` and `T`; no shading.  **Level pair:** none — per-scale
data, one witness per grid level `k ≤ ssfGridLen δ`. -/
theorem towerUniformAtScaleData_of_uniformTubeSet {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) :
    TowerUniformAtScaleData 𝒰 (Tube.ssfGridLen δ) (Cu ^ 2) :=
  ⟨fun _ hk => (𝒰.toChain).uniformAt hCu hk⟩

/-! ### Items 1 and 3: the entry bound `hGood` (H3) and the split `hsplit` (l.5289-5297)

Both are hypotheses of `exists_fixedTowerCuts`, and the stopping run consumes them identically
whichever reading its downstream alternatives use — the containment chain via
`towerUniformAtScaleData_of_uniformTubeSet` at `Cu²`, or class siblings.  So they are built here
once, on the fixed tower, independent of the choice of intermediate notation. -/

/-- **`hGood`: the entry bound (H3, l.5265)** `X(0,M) ≤ r(0,M)^{-η₁}`, on the fixed tower.

`towerDensityArray` is a `Finset.sup`, so the entry bound is exactly the source's *"assumed
top-cell estimate"* (l.2694 for (B): `Δ_max(𝕋⟨S⟩) ≤ (ρ_0/δ)^{η_1}` for `S ∈ 𝕋_0`) read over the
level-`0` nodes.  Nothing is derived from geometry here: the source assumes it, and this transports
the assumption onto the array the stopping time reads.

**Family/shading:** the fixed tower's `s` and `T`; no shading.  **Level pair:** `(0, M)` — the
whole window, which is the only pair the entry bound speaks about. -/
theorem towerGood_entry_of_topCell
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu} {bound : ℕ → ℕ → ℕ → ENNReal} {M : ℕ}
    (htop : ∀ j ∈ 𝒰.cover.indexSet 0,
      Kakeya.maxDensity (𝒰.nodesUnder M 0 j)
        (fun j' => (𝒰.cover.tube M j').toConvexSpaceBody) ≤ bound 0 0 M) :
    TowerGood 𝒰 bound 0 0 M () :=
  Finset.sup_le htop

/-- **`hsplit`: the "insert `m`" step** (l.5289-5297), on the fixed tower.

The source's chain, verbatim:

> `X(a,m) ≤ E r(a,b)^{-η_J} ≤ r(a,b)^{-ε η_{J+1}} ≤ r(a,m)^{-η_{J+1}}`,
> *"The middle inequality is precisely the calibration `δ^{-ε²η₁/2} ≥ E`."*

`hcal` is that calibration, quantified once rather than re-derived per piece — **copied, not
fitted**: the theorem never inspects `E`, `ε`, `η₁` or the scale convention, so no printed constant
can drift here.  `hdata` is the test's own output: the intermediate level `m`, the `(H4)` comparison
`X(a,m) ≤ E·X(a,b)`, and the failure of the witness inequality at `m`, which **is** the second new
estimate the source cites.

**Family/shading:** the fixed tower; no shading.  **Level pair:** the piece `(a,b)` being cut, and
the inserted level `m` strictly between — the cut point, not a window. -/
theorem towerGood_split_of_calibration
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu}
    {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {Efac : ℝ} {w : ℕ}
    (hcal : ∀ j a m b : ℕ, ENNReal.ofReal Efac * sourceBound rinv η j a b
      ≤ sourceBound rinv η (j + 1) a m)
    {j a b : ℕ}
    (hold : TowerGood 𝒰 (sourceBound rinv η) j a b ())
    (hdata : ∃ m : ℕ, a + w ≤ m ∧ m + w ≤ b ∧
      towerDensityArray 𝒰 a m ≤ ENNReal.ofReal Efac * towerDensityArray 𝒰 a b ∧
      TowerGood 𝒰 (sourceBound rinv η) (j + 1) m b ()) :
    ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧
      TowerGood 𝒰 (sourceBound rinv η) (j + 1) a c () ∧
      TowerGood 𝒰 (sourceBound rinv η) (j + 1) c b () := by
  obtain ⟨m, hm1, hm2, hH4, hsecond⟩ := hdata
  refine ⟨m, hm1, hm2, ?_, hsecond⟩
  calc towerDensityArray 𝒰 a m
      ≤ ENNReal.ofReal Efac * towerDensityArray 𝒰 a b := hH4
    _ ≤ ENNReal.ofReal Efac * sourceBound rinv η j a b := mul_le_mul_left' hold _
    _ ≤ sourceBound rinv η (j + 1) a m := hcal j a m b

/-! ### `A3`: where the `Cu²` lands — measured, per site

`towerUniformAtScaleData_of_uniformTubeSet` costs `Cu → Cu²`.  Measured across the sites rather
than assumed:

* `Tube.ssfUniformConst n = max (uniformConst n) 4` (`ShadedUniform.lean:895`) is **δ-free**, so
  squaring is free at the six middle-factor sites that carry it.
* The floor sites bracket `Cu` by a **δ-free parameter** `Cu₀` with `1 ≤ Cu₀`
  (`SpineFloorTerminal.lean:127, 214`), and already carry `Cu ^ 8`
  (`:353-354`, `:373`).  A square sits strictly inside that bracket
  (`cu_sq_le_cu_pow_eight`), so it needs no row of its own.
* **No site brackets `Cu` by a `δ`-power.**  A search for `Cu ≤ … δ ^ …` across the tree returns
  nothing, so the `2η_d` cost that would tighten `` by a factor two — which `§AA` measured to
  fail — **does not arise**.  As expected, but measured.

Conclusion for source question (2): the `Cu²` is absorbed everywhere; it touches neither
`§2`'s four-loss `hexp` nor `§11`'s `C1`. -/

/-- The `Cu²` of `towerUniformAtScaleData_of_uniformTubeSet` sits inside the `Cu ^ 8` bracket the
floor sites already carry, so it costs no new row. -/
theorem cu_sq_le_cu_pow_eight {Cu : NNReal} (hCu : 1 ≤ Cu) : Cu ^ 2 ≤ Cu ^ 8 :=
  pow_le_pow_right₀ hCu (by norm_num)

end FixedTowerStopping

end Kakeya.ML2Core

end
