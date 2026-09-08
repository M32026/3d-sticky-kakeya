/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScaleSubset
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTowerArrayEstimates
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountFloor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam

/-!
# `Z(k,l)` on the source's own object: the **fibre** density array

(1): the source's array is on **thread cells**, l.2735

> `Z(k,l) = max_{S ∈ 𝕋_k} Δ_max(𝕋_l⟨S⟩)`

with `𝕋_l⟨S⟩` Definition 2.1(ii)'s thread cell (l.222-225), i.e. the **assignment fibre**
`Tube.UniformTubeSet.assignFibre` (`SpineCountFloor.lean:66`).  The existing
`Kakeya.ML2Core.towerDensityArray` (`SpineFixedTowerStopping.lean:92`) is on
`Tube.UniformTubeSet.nodesUnder`, the containment set.  This file cuts the faithful array as an
**additive sibling**;, and `towerDensityArray` is kept as the record of
Condition R's negative half.

## Why the containment array cannot feed a lower bound, and the fibre array can

`Tube.UniformTubeSet.assignFibre_subset_nodesUnder` (existing) plus `Kakeya.maxDensity_mono` give

  `Δ_max(assignFibre) ≤ Δ_max(nodesUnder)`   (`towerDensityArrayFibre_le_towerDensityArray`)

and **that is the only relation between them**.  So:

* **upper** bounds (H1, H2, H3, `TowerGood`) proved on the containment array are *stronger* and pass
  to the fibre array for free — `Condition R`'s permissive half;
* a **lower** bound on the containment array says nothing about the thread cell — Condition R's
  prohibitive half, and the reason the witness clause needs this file.

## The `Cu` disappears on the fibre — and that is Definition 2.1(ii), not an optimisation

`Kakeya.ML2Core.towerDensityArray_submultiplicative` pays a `Cu`
(`maxDensity_ancestors_le_mul_sup`) because a level-`p` ancestor of a cell *contained* in `T_a` need
not lie in `T_a`.  On a thread cell that cannot happen: Definition 2.1(ii) is
`π_{k-1} = q_k ∘ π_k`, *"so the thread cells form compatible partitions"*, and the Lean form of that
sentence is `image_coarseNode_assignFibre_subset` below — the ancestors of `𝕋_c⟨S⟩` lie in
`𝕋_p⟨S⟩`, by `Kakeya.ML2Core.coarseNode_assign` alone.  So

  **H1 on the fibre array is at `C₀'(E) ^ 2`, with no `Cu` factor at all**,

which is the shape the source prints (`300⁹C₂`; its `C₂` is the geometric-competitor constant, the
analogue of the `Cu` that only the containment reading needs).  `C₀'(E)` is
`Kakeya.ML2Core.twoScaleSubsetConst`, GWZ 7.4 at `M = 2` on an arbitrary level-`c` subfamily
(`SpineTwoScaleSubset.lean`); `twoScaleConst` is untouched.

## The boundary question, answered : **the window fields do NOT have to move**

's forward-looking note asks whether closing the chain forces
`IsKatzTaoDividingWindow.le_window_maxDensity` and the twin's `le_level_maxDensity` — lower-bound
fields currently on `nodesUnder` — onto the fibre, which would need a condition.  **It does not**, and
`le_mul_maxDensity_nodesUnder_of_lt_towerDensityArrayFibre` is the reason:

1. the fibre-array run's second alternative gives `X < Z_fib(a,c)`, i.e. **one** `S` with
   `X < Δ_max(𝕋_c⟨S⟩)` (`Finset.lt_sup_iff`) — existential, exactly as `eqdividingKwitness`
   (l.2700-2703) is, and the source says so: *"both last conclusions are existential at each
   intermediate level"*;
2. the regularization band — `IsKatzTaoDividingWindowLevels.level_density_band`, l.4032-4035,
   **which is stated on `assignFibre`** — upgrades that to **every** `j` at the cost `Cstar`,
   which is l.4051-4053's universal `∀ S ∈ 𝕊'_a`;
3. the last step is `Δ_max(assignFibre) ≤ Δ_max(nodesUnder)`, and for a **lower** bound that
   monotonicity runs the *right* way: `X ≤ Cstar * Δ_max(assignFibre c a j)`
   `≤ Cstar * Δ_max(nodesUnder c a j)`.

Step 3 is the whole answer: a fibre lower bound *implies* the containment lower bound, so the
existing field text is **weaker** and therefore derivable.  No (F)-branch interface structure moves,
nothing on §2.2's do-not-move list is touched, and **no condition is required**.  (The converse —
containment lower bound ⇒ fibre lower bound — is what does not hold, and it is why step 1 must be
run on the fibre array in the first place.)

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `towerDensityArrayFibre` | the tower's `s`, `T`; no shading | `(k,l)`, both free |
| `towerDensityArrayFibre_le_towerDensityArray` | as above | `(k,l)` |
| `image_coarseNode_assignFibre_subset` | as above | `(a,p,c)` |
| `towerDensityArrayFibre_submultiplicative` | as above | `(a,p,c)` |
| `towerDensityArrayFibre_le_of_card_le` | as above | `(k,l)` |
| `TowerGoodFibre`, `exists_fixedTowerCutsFibre` | as above | the cut set; the piece `(a,b)` |
| `le_mul_maxDensity_nodesUnder_of_lt_towerDensityArrayFibre` | as above | `(a,c)` |

## A1-a

No `GridUniformCore`; no (F)-branch interface statement is defined or altered here.  The window
structure is *consumed by shape* in the last theorem and not mentioned.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section TowerArrayFibre

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`Z(k,l) = max_{S ∈ 𝕋_k} Δ_max(𝕋_l⟨S⟩)`** (source l.2731-2733), on the source's own object:
the **thread cell** `Tube.UniformTubeSet.assignFibre`, not the containment set.

**Family/shading:** the fixed tower's `s`, cover data of `𝒰`; **no shading**.
**Level pair:** `(k,l)`, both free. -/
noncomputable def towerDensityArrayFibre
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (k l : ℕ) : ENNReal :=
  (𝒰.cover.indexSet k).sup (fun j =>
    Kakeya.maxDensity (𝒰.assignFibre l k j)
      (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody))

open scoped Classical in
/-- **The fibre array is below the containment array**, pointwise — and this is the only relation
between them.  Every upper bound proved for `towerDensityArray` therefore holds for
`towerDensityArrayFibre`; no lower bound passes the other way. -/
theorem towerDensityArrayFibre_le_towerDensityArray
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {k l : ℕ} (hkl : k ≤ l)
    (hl : l ≤ Tube.ssfGridLen δ) :
    towerDensityArrayFibre 𝒰 k l ≤ towerDensityArray 𝒰 k l := by
  classical
  refine Finset.sup_le fun j hj => ?_
  refine le_trans (Kakeya.maxDensity_mono _
    (Tube.UniformTubeSet.assignFibre_subset_nodesUnder 𝒰 hkl hl j)) ?_
  exact Finset.le_sup (f := fun j' => Kakeya.maxDensity (𝒰.nodesUnder l k j')
    (fun j'' => (𝒰.cover.tube l j'').toConvexSpaceBody)) hj

open scoped Classical in
/-- **Definition 2.1(ii), : thread cells form compatible partitions.**
`π_{k-1} = q_k ∘ π_k` (l.222-224): every level-`p` ancestor of a level-`c` cell of the thread
cell `𝕋_c⟨S⟩` is itself a cell of `𝕋_p⟨S⟩` — for **any** anchor level `a`, and needing no
relation between `a` and `p` at all.

**This is the step that removes the `Cu`** that `towerDensityArray_submultiplicative` must pay: on
the *containment* set the ancestors can stick out of `T_a` and are only capped by `boundedOverlap`;
on the thread cell they cannot stick out at all.  The proof is `coarseNode_assign` and nothing
else. -/
theorem image_coarseNode_assignFibre_subset
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {a p c : ℕ} (hpc : p ≤ c)
    (hc : c ≤ Tube.ssfGridLen δ) (S : ι) :
    (𝒰.assignFibre c a S).image (ML2Reduction.coarseNode 𝒰.cover.toChain p c)
      ⊆ 𝒰.assignFibre p a S := by
  classical
  intro jp hjp
  obtain ⟨jc, hjc, rfl⟩ := Finset.mem_image.mp hjp
  simp only [Tube.UniformTubeSet.assignFibre, Finset.mem_image] at hjc ⊢
  obtain ⟨i, hi, rfl⟩ := hjc
  refine ⟨i, hi, ?_⟩
  simp only [coverClass, Finset.mem_filter] at hi
  exact (coarseNode_assign 𝒰.cover.toChain hpc hc hi.1).symm

open scoped Classical in
/-- The thread cell is a family of genuine level-`c` nodes. -/
theorem assignFibre_subset_indexSet (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {a c : ℕ} (hc : c ≤ Tube.ssfGridLen δ) (S : ι) :
    𝒰.assignFibre c a S ⊆ 𝒰.cover.indexSet c := by
  classical
  intro jc hjc
  simp only [Tube.UniformTubeSet.assignFibre, Finset.mem_image] at hjc
  obtain ⟨i, hi, rfl⟩ := hjc
  simp only [coverClass, Finset.mem_filter] at hi
  exact 𝒰.cover.assign_mem c hc i hi.1

open scoped Classical in
/-- **H1 on the fibre array, at `C₀'(E) ^ 2` and with NO `Cu`** (source l.2735-2737, transposed).

`Z_fib(a,c) ≤ C₀'(E)² · Z_fib(a,p) · Z_fib(p,c)` for `a ≤ p ≤ c`.  Both factors of
`twoScaleSubsetConst_spec` land on the fibre array: the ancestor factor by
`image_coarseNode_assignFibre_subset` (Definition 2.1(ii) — this is where the containment reading's
`Cu` is *not* paid), the fibre factor because `twoScaleSubsetConst_spec`'s second factor is already
the `coverClass`-image sup, i.e. `assignFibre` itself.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** the triple `(a,p,c)`. -/
theorem towerDensityArrayFibre_submultiplicative (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {a p c : ℕ} (_hap : a ≤ p) (hpc : p ≤ c) (hc : c ≤ Tube.ssfGridLen δ)
    (hgap : 4 * gridScale δ (Tube.ssfGridLen δ) c ≤ gridScale δ (Tube.ssfGridLen δ) p) :
    towerDensityArrayFibre 𝒰 a c
      ≤ ENNReal.ofReal (twoScaleSubsetConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2
          * towerDensityArrayFibre 𝒰 a p * towerDensityArrayFibre 𝒰 p c := by
  classical
  have hp : p ≤ Tube.ssfGridLen δ := hpc.trans hc
  refine Finset.sup_le fun S hS => ?_
  have hmain := twoScaleSubsetConst_spec.{u, 0} hδ0 hδ1 𝒰 hs hball hpc hc
    (𝒰.assignFibre c a S) (assignFibre_subset_indexSet 𝒰 hc S) (hgap := hgap)
  refine hmain.trans ?_
  have hanc : Kakeya.maxDensity
        ((𝒰.assignFibre c a S).image (ML2Reduction.coarseNode 𝒰.cover.toChain p c))
        (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)
      ≤ towerDensityArrayFibre 𝒰 a p := by
    refine le_trans (Kakeya.maxDensity_mono _
      (image_coarseNode_assignFibre_subset 𝒰 hpc hc S)) ?_
    exact Finset.le_sup (f := fun j => Kakeya.maxDensity (𝒰.assignFibre p a j)
      (fun j' => (𝒰.cover.tube p j').toConvexSpaceBody)) hS
  have hfib : ((𝒰.assignFibre c a S).image
        (ML2Reduction.coarseNode 𝒰.cover.toChain p c)).sup
        (fun jp => Kakeya.maxDensity
          ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c))
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
      ≤ towerDensityArrayFibre 𝒰 p c := by
    refine Finset.sup_le fun jp hjp => ?_
    have hjpidx : jp ∈ 𝒰.cover.indexSet p :=
      assignFibre_subset_indexSet 𝒰 hp S (image_coarseNode_assignFibre_subset 𝒰 hpc hc S hjp)
    exact Finset.le_sup (f := fun j => Kakeya.maxDensity (𝒰.assignFibre c p j)
      (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) hjpidx
  exact mul_le_mul' (mul_le_mul' le_rfl hanc) hfib

open scoped Classical in
/-- **H2 on the fibre array.**  `Δ_max ≤ #` taken to the supremum, exactly as for the containment
array; the source's cardinality estimate (l.2679-2681) is about `#𝕋_l⟨S⟩`, a thread cell, so this
is the reading it is actually stated at. -/
theorem towerDensityArrayFibre_le_of_card_le (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {k l : ℕ} {B : ENNReal}
    (hcard : ∀ j ∈ 𝒰.cover.indexSet k, ((𝒰.assignFibre l k j).card : ENNReal) ≤ B) :
    towerDensityArrayFibre 𝒰 k l ≤ B :=
  Finset.sup_le fun j hj => (Kakeya.maxDensity_le_card _ _).trans (hcard j hj)

open scoped Classical in
/-- **H2 at the source's crude exponent `d = 4`**, on the thread cell. -/
theorem towerDensityArrayFibre_le_crude_exponent_four
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {k l : ℕ} {D : ENNReal}
    (hcard : ∀ j ∈ 𝒰.cover.indexSet k, ((𝒰.assignFibre l k j).card : ENNReal)
      ≤ D * ENNReal.ofReal
          (((gridScale δ (Tube.ssfGridLen δ) k : ℝ)
            / (gridScale δ (Tube.ssfGridLen δ) l : ℝ)) ^ (4 : ℕ))) :
    towerDensityArrayFibre 𝒰 k l
      ≤ D * ENNReal.ofReal
          (((gridScale δ (Tube.ssfGridLen δ) k : ℝ)
            / (gridScale δ (Tube.ssfGridLen δ) l : ℝ)) ^ (4 : ℕ)) :=
  towerDensityArrayFibre_le_of_card_le 𝒰 hcard

/-! ### The stopping run on the fibre array -/

open scoped Classical in
/-- Piece-admissibility (l.5286-5288) read on the **fibre** array. -/
def TowerGoodFibre (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (bound : ℕ → ℕ → ℕ → ENNReal) (j a b : ℕ) (_ : Unit) : Prop :=
  towerDensityArrayFibre 𝒰 a b ≤ bound j a b

open scoped Classical in
/-- **The containment form implies the fibre form**, so H3 and every other *upper* bound already
proved on `towerDensityArray` transfers for free (Condition R's permissive half). -/
theorem towerGoodFibre_of_towerGood {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu}
    {bound : ℕ → ℕ → ℕ → ENNReal} {j a b : ℕ} (hab : a ≤ b) (hb : b ≤ Tube.ssfGridLen δ)
    (h : TowerGood 𝒰 bound j a b ()) : TowerGoodFibre 𝒰 bound j a b () :=
  le_trans (towerDensityArrayFibre_le_towerDensityArray 𝒰 hab hb) h

open scoped Classical in
/-- **H3 on the fibre array** (source l.2683-2684, the assumed top-cell estimate), direct. -/
theorem towerGoodFibre_entry_of_topCell
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu} {bound : ℕ → ℕ → ℕ → ENNReal} {M : ℕ}
    (htop : ∀ j ∈ 𝒰.cover.indexSet 0,
      Kakeya.maxDensity (𝒰.assignFibre M 0 j)
        (fun j' => (𝒰.cover.tube M j').toConvexSpaceBody) ≤ bound 0 0 M) :
    TowerGoodFibre 𝒰 bound 0 0 M () :=
  Finset.sup_le htop

open scoped Classical in
/-- `hmono` on the fibre array: `TowerGoodFibre` is a bound on a fixed quantity. -/
theorem towerGoodFibre_mono_of_bound_mono
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu} {bound : ℕ → ℕ → ℕ → ENNReal}
    (hb : ∀ j j' a b : ℕ, j ≤ j' → bound j a b ≤ bound j' a b)
    {j j' a b : ℕ} (hjj' : j ≤ j') (h : TowerGoodFibre 𝒰 bound j a b ()) :
    TowerGoodFibre 𝒰 bound j' a b () := le_trans h (hb j j' a b hjj')

open scoped Classical in
/-- **`hsplit` on the fibre array**, the source's *"insert `m`"* step (l.5289-5297), verbatim from
`towerGood_split_of_calibration` with the array changed. -/
theorem towerGoodFibre_split_of_calibration
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu}
    {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {Efac : ℝ} {w : ℕ}
    (hcal : ∀ j a m b : ℕ, ENNReal.ofReal Efac * sourceBound rinv η j a b
      ≤ sourceBound rinv η (j + 1) a m)
    {j a b : ℕ}
    (hold : TowerGoodFibre 𝒰 (sourceBound rinv η) j a b ())
    (hdata : ∃ m : ℕ, a + w ≤ m ∧ m + w ≤ b ∧
      towerDensityArrayFibre 𝒰 a m ≤ ENNReal.ofReal Efac * towerDensityArrayFibre 𝒰 a b ∧
      TowerGoodFibre 𝒰 (sourceBound rinv η) (j + 1) m b ()) :
    ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧
      TowerGoodFibre 𝒰 (sourceBound rinv η) (j + 1) a c () ∧
      TowerGoodFibre 𝒰 (sourceBound rinv η) (j + 1) c b () := by
  obtain ⟨m, hm1, hm2, hH4, hsecond⟩ := hdata
  refine ⟨m, hm1, hm2, ?_, hsecond⟩
  calc towerDensityArrayFibre 𝒰 a m
      ≤ ENNReal.ofReal Efac * towerDensityArrayFibre 𝒰 a b := hH4
    _ ≤ ENNReal.ofReal Efac * sourceBound rinv η j a b := mul_le_mul' le_rfl hold
    _ ≤ sourceBound rinv η (j + 1) a m := hcal j a m b

open scoped Classical in
/-- **`lemabstractstopping` on a fixed tower, run on the FIBRE array** — the same one-line
instantiation of `Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin` as
`exists_fixedTowerCuts`, with `TowerGood` replaced by `TowerGoodFibre`.  The engine is abstract in
the tracked quantity, so nothing else changes.

**Family/shading:** the fixed tower `𝒰` on `(s,T)`; no shading.  **Level pair:** the maximal
admissible cut set `S`; each adjacent pair `(a,b)` is a candidate window. -/
theorem exists_fixedTowerCutsFibre
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (M N w : ℕ) (hw : 0 < w) (hwM : w ≤ M) (hwN : M ≤ w * N)
    (bound : ℕ → ℕ → ℕ → ENNReal)
    (Test : ℕ → ℕ → ℕ → Unit → Prop) (Long : ℕ → ℕ → Prop)
    (hGood : TowerGoodFibre 𝒰 bound 0 0 M ())
    (hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b →
      TowerGoodFibre 𝒰 bound j a b () → TowerGoodFibre 𝒰 bound j' a b ())
    (hsplit : ∀ j a b : ℕ, j + 1 ≤ N → a < b → b ≤ M → Long a b →
      TowerGoodFibre 𝒰 bound j a b () → Test (j + 1) a b () →
      ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧
        TowerGoodFibre 𝒰 bound (j + 1) a c () ∧ TowerGoodFibre 𝒰 bound (j + 1) c b ()) :
    ∃ (S : Finset ℕ) (m : ℕ), m < N ∧ 0 ∈ S ∧ M ∈ S ∧
      S ⊆ Finset.range (M + 1) ∧ S.card = m + 2 ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
        TowerGoodFibre 𝒰 bound m a b () ∧ (¬ Long a b ∨ ¬ Test (m + 1) a b ()) := by
  obtain ⟨S, m, x, hmN, -, h0, hM, hsub, hcard, hpieces⟩ :=
    Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin (σ := Unit) M N w hw hwM hwN
      (fun j a b x => TowerGoodFibre 𝒰 bound j a b x) Test Long
      (fun _ _ _ => True) ()
      (fun _ => trivial) (fun _ _ _ _ _ _ _ => trivial) hGood
      (fun j j' hjj' hj'N a b hab x hg => hmono j j' hjj' hj'N a b hab hg)
      (fun _ _ _ _ _ _ _ _ hg => hg)
      (fun j a b hjN hab hbM hlong x hg htest => by
        obtain ⟨c, h1, h2, h3, h4⟩ := hsplit j a b hjN hab hbM hlong hg htest
        exact ⟨(), c, trivial, h1, h2, h3, h4⟩)
  exact ⟨S, m, hmN, h0, hM, hsub, hcard, fun a ha b hb hab hadj => hpieces a ha b hb hab hadj⟩

/-! ### The read-back: existential witness ⇒ universal clause ⇒ the existing `nodesUnder` field -/

open scoped Classical in
/-- **The witness clause, delivered in the shape the existing window field already has.**

Input: an existential witness on the **fibre** array, `X < Z_fib(a,c)` — what the fibre-array
stopping run's `¬ Test` yields, and exactly the form `eqdividingKwitness` (l.2700-2703) has, the
source saying in terms that *"both last conclusions are existential at each intermediate level"*.

Input 2: the regularization band `hband`, i.e.
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` read at the pair `(a,c)` —
`Φ ≤ Δ_max(𝕋_c⟨j⟩) ≤ Cstar · Φ` for every level-`a` cell `j`.  It is stated on `assignFibre`, the
same reading as the witness, which is why the two compose.

Output: `X ≤ Cstar * Δ_max(𝒰.nodesUnder c a j)` for **every** `j` — l.4051-4053's universal `∀ S ∈
𝕊'_a`, and **the exact shape of the existing `le_window_maxDensity` / `le_level_maxDensity` fields on
`nodesUnder`**.  The last step is `Tube.UniformTubeSet.assignFibre_subset_nodesUnder` with
`Kakeya.maxDensity_mono`: for a *lower* bound that monotonicity runs the right way, so the fields do
**not** have to move to the fibre and no interface condition is needed.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** `(a,c)`. -/
theorem le_mul_maxDensity_nodesUnder_of_lt_towerDensityArrayFibre
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {a c : ℕ} (hac : a ≤ c) (hc : c ≤ Tube.ssfGridLen δ) {X Cstar Φ : ENNReal}
    (hband : ∀ j ∈ 𝒰.cover.indexSet a,
      Φ ≤ Kakeya.maxDensity (𝒰.assignFibre c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒰.assignFibre c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ)
    (hwit : X < towerDensityArrayFibre 𝒰 a c) :
    ∀ j ∈ 𝒰.cover.indexSet a,
      X ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder c a j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
  classical
  intro j hj
  obtain ⟨S, hS, hSlt⟩ := Finset.lt_sup_iff.mp hwit
  calc X ≤ Kakeya.maxDensity (𝒰.assignFibre c a S)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := hSlt.le
    _ ≤ Cstar * Φ := (hband S hS).2
    _ ≤ Cstar * Kakeya.maxDensity (𝒰.assignFibre c a j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) :=
        mul_le_mul' le_rfl (hband j hj).1
    _ ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder c a j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) :=
        mul_le_mul' le_rfl (Kakeya.maxDensity_mono _
          (Tube.UniformTubeSet.assignFibre_subset_nodesUnder 𝒰 hac hc j))

end TowerArrayFibre

end Kakeya.ML2Core

end
