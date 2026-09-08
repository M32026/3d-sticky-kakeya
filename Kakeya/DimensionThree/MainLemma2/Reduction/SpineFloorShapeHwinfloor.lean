/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapePayload
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorCount
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineWindowLevelsTripwires

/-!
# `hwinfloor`, the last floor row: its two conjuncts, measured

 reduced `FloorPayload` (post-`RR1`, post-the estimate) to the single
row `hwinfloor`, whose goal is a conjunction:

```
∃ a b m, IsKatzTaoDividingWindowLevels (refinedHierarchy …) … a b m
       ∧ FloorHypothesisAt β ϖ ε₁ gain dens η' (refinedHierarchy …) a b m
```

This file measures both conjuncts.

## Conjunct 2 — reduced to `F4a`'s rows, with **two of the three clauses free at `p := a`**

`Kakeya.ML2Core.FloorHypothesisAt` is `∃ p ≥ a` with three clauses.  At the **coarse level itself**,
`p := a`:

* clause 1 (*`p` is beyond the window band*) is `a < m'`, which is already a binder — **free**;
* clause 2 is literally `Kakeya.ML2Core.ParentAdmissible 𝒰 η' a a`, the existing `X7` row;
* clause 3 is exactly the conclusion of the existing `F4a`
  (`Kakeya.ML2Core.floor_of_windowLevels_of_fill`) at `p := a`.

`Kakeya.ML2Core.floorHypothesisAt_of_countFloor` and
`Kakeya.ML2Core.floorHypothesisAt_of_windowLevels` below make that composition explicit.  So
conjunct 2 costs, beyond the twin: `hCstar`, `hcap`, `hgap`, `hclose` (four threshold/scalar rows,
all with existing dischargers per `Reduction/SpineFloorProducer.lean:31`) and **`hfill`** — the one
row carrying geometry, `FillAt 𝒰 κ a m' jp` at every level-`a` node and every `m' ∈ (a, b]`.

## Conjunct 1 — **no producer, by design**, and the `Φ` question settled

`Reduction/SpineFloorProducer.lean:29` records that the twin on `refinedHierarchy` has *"no producer
by design (C-M1c): its failure is `(D)`"*, routed by the existing
`Kakeya.ML2Core.trialOutcomeAtGain_of_refinement_dichotomy` (`R8`).  `hwinfloor` demands the twin
for **every** refinement of **every** family at **every** scale, which is the `(F)` branch
asserted unconditionally — strictly stronger than the dichotomy the tree proves.  The level clause
is not a formality: `Kakeya.ML2Core.not_levelClause_gridModel` (existing `T1`) exhibits a family
satisfying the *parent* window and refuting the level clause.

The open question was whether the band's profile `Φ` may depend on the coarse node.  It may not —
`level_density_band` binds `Φ : ℕ → ℕ → ENNReal` outside `∀ j ∈ 𝒰.cover.indexSet p` — and
`Kakeya.ML2Core.exists_uniform_band_iff_pairwise` says exactly what that costs:

> a node-free profile exists **iff** the two-level maximal densities are pairwise comparable
> **across coarse nodes** within `Cstar`.

So the cost is a *cross-node homogeneity* of the two-level densities, at the same constant as the
window's own `Cstar`.  It is owned by the twin's only producer,
`Kakeya.ML2Reduction.exists_dichotomy_katzTaoDividingWindow` (which returns the twin on **its own**
output hierarchy `𝒰'`, not on a `refinedHierarchy`), i.e. by the dividing-scales machinery — not by
the floor hands.  See
-/

@[expose] public section

open MeasureTheory Metric Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-! ### The `Φ` measurement: a node-free band is cross-node comparability -/

section Band

variable {ι : Type*}

open scoped Classical in
/-- **A node-free two-sided profile exists iff the values are pairwise comparable within `Cstar`.**

This is the exact content of `IsKatzTaoDividingWindowLevels.level_density_band`'s quantifier order:
`Φ : ℕ → ℕ → ENNReal` is bound *outside* `∀ j ∈ 𝒰.cover.indexSet p`, so a band is not a per-node
statement but a **cross-node** comparison.  Stated on abstract data so the measurement is separable
from the window. -/
theorem exists_uniform_band_iff_pairwise {Cstar : ENNReal}
    (idx : ℕ → Finset ι) (D : ℕ → ℕ → ι → ENNReal) (N : ℕ) :
    (∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ N, ∀ c ≤ N, ∀ j ∈ idx p,
        Φ p c ≤ D p c j ∧ D p c j ≤ Cstar * Φ p c)
      ↔ (∀ p ≤ N, ∀ c ≤ N, ∀ j ∈ idx p, ∀ j' ∈ idx p, D p c j ≤ Cstar * D p c j') := by
  classical
  constructor
  · rintro ⟨Φ, hΦ⟩ p hp c hc j hj j' hj'
    exact (hΦ p hp c hc j hj).2.trans (mul_le_mul_right (hΦ p hp c hc j' hj').1 Cstar)
  · intro hpair
    refine ⟨fun p c => if h : (idx p).Nonempty then (idx p).inf' h (D p c) else 0, ?_⟩
    intro p hp c hc j hj
    have hne : (idx p).Nonempty := ⟨j, hj⟩
    simp only [dif_pos hne]
    refine ⟨Finset.inf'_le _ hj, ?_⟩
    obtain ⟨j', hj', hval⟩ := Finset.exists_mem_eq_inf' hne (D p c)
    rw [hval]
    exact hpair p hp c hc j hj j' hj'

end Band

/-! ### Conjunct 2, at the coarse level -/

section FloorAtCoarse

variable {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
  {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`FloorHypothesisAt` at `p := a`: clause 1 is free, clause 2 is `X7`, clause 3 is `F4a`.**

The three clauses of `Kakeya.ML2Core.FloorHypothesisAt` at the coarse level: the parent-position
clause degenerates to the binder `a < m'`, the density clause *is*
`Kakeya.ML2Core.ParentAdmissible 𝒰 η' a a`, and the count floor is the hypothesis `hcount`, whose
shape is the conclusion of `Kakeya.ML2Core.floor_of_windowLevels_of_fill` at `p := a`. -/
theorem floorHypothesisAt_of_countFloor {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (a b m : ℕ)
    (hpar : ParentAdmissible 𝒰 η' a a)
    (hcount : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder a a jθ, ∀ m' : ℕ, a < m' → m' < b →
      ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
        ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
      a < m' →
      ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
        ≤ ((𝒰.nodesUnder m' a jp).card : ℝ)) :
    FloorHypothesisAt β ϖ ε₁ gain dens η' 𝒰 a b m :=
  ⟨a, le_rfl, fun _ ham' _ _ _ => ham', hpar, hcount⟩

open scoped Classical in
/-- **Conjunct 2, closed from the twin.**  `F4a` at `p := a`, wrapped into
`Kakeya.ML2Core.FloorHypothesisAt` by `Kakeya.ML2Core.floorHypothesisAt_of_countFloor`.

So `hwinfloor`'s second conjunct costs exactly: the twin `hwin` (which is conjunct 1), the four
scalar/threshold rows `hCstar`, `hcap`, `hgap`, `hclose` — all with existing dischargers
(`Reduction/SpineFloorProducer.lean:31`: `F7`'s own `hCstarB`, the cap, `F6`'s gap lemma,
`F6(iv) floor_exponent_closes`) — the existing `X7` row `hpar` at `p := a`, and **`hfill`**.

`hfill` is the only row carrying geometry, and it is `R5`'s: `FillAt 𝒰 κ a m' jp` at every
level-`a` node, every cell under it and every `m' ∈ (a, b]`, whose per-node engine is the existing
`Kakeya.ML2Core.fillAt_of_biasedMaximizer`. -/
theorem floorHypothesisAt_of_windowLevels {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (hs : u.Nonempty)
    (hball : ∀ i ∈ u, ((V i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal} {a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar
      (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
      (ML2Spine.spineCount ϖ ε₁) a b m)
    (hCstar : Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)))
    (hcap : η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hgap : ∀ p c : ℕ, a ≤ p → p < c → c ≤ b →
      4 * (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ))
    (hpar : ParentAdmissible 𝒰 η' a a)
    (hfill : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder a a jθ, ∀ m' : ℕ, a < m' → m' ≤ b →
      FillAt 𝒰 κ a m' jp)
    (hclose : ∀ m' : ℕ, a + ⌈ML2Spine.spineDiv ϖ ε₁ * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m' → a < m' →
      m' ≤ b →
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
          * (Cstar ^ 2 * ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3)) ^ 2)
              * (Cu : ENNReal) * (δ : ENNReal) ^ (-(2 * η'))
              * ((Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
                : ENNReal))
        ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
          * ENNReal.ofReal κ
          * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
            : ENNReal)) :
    FloorHypothesisAt β ϖ ε₁ gain dens η' 𝒰 a b m :=
  floorHypothesisAt_of_countFloor 𝒰 a b m hpar
    (floor_of_windowLevels_of_fill hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1 𝒰 hs hball
      hwin hCstar hcap hgap le_rfl hpar hfill hclose)

end FloorAtCoarse

/-! ### A ceiling on `F4a`'s `κ`, and the tension it creates -/

section KappaCeiling

variable {ι : Type*} {δ C : NNReal} {s : Finset ι} {N : ℕ}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`FillAt` forces `κ ≤ 1`.**  `Kakeya.le_maxDensity` bounds the density in *any* container by
the maximal density, so `κ · Δ_max ≤ Δ(·, node) ≤ Δ_max` and `Δ_max` cancels.

`F4a` (`Kakeya.ML2Core.floor_of_windowLevels_of_fill`) carries only `hκ : 0 < κ`, so this is the
missing upper end of its `κ`-range, and it matters: `κ` sits on the **larger** side of `F4a`'s
`hclose`, so `hclose` wants `κ` large while `hfill` caps it at `1`.  Anybody discharging `hclose`
below `δ₀` must do it at `κ ≤ 1`. -/
theorem ofReal_le_one_of_fillAt (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ} {c k : ℕ} {j : ι}
    (hfill : FillAt 𝒰 κ k c j)
    (hpos : 0 < Kakeya.maxDensity (𝒰.nodesUnder c k j)
      (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :
    ENNReal.ofReal κ ≤ 1 := by
  classical
  have hle : ENNReal.ofReal κ * Kakeya.maxDensity (𝒰.nodesUnder c k j)
      (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ 1 * Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
    rw [one_mul]
    exact hfill.trans (Kakeya.le_maxDensity _ _ _)
  exact (ENNReal.mul_le_mul_iff_left hpos.ne' (Kakeya.maxDensity_ne_top _ _)).mp hle

/-- The real-valued form of `Kakeya.ML2Core.ofReal_le_one_of_fillAt`. -/
theorem le_one_of_fillAt (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ} {c k : ℕ} {j : ι}
    (hfill : FillAt 𝒰 κ k c j)
    (hpos : 0 < Kakeya.maxDensity (𝒰.nodesUnder c k j)
      (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :
    κ ≤ 1 :=
  ENNReal.ofReal_le_one.mp (ofReal_le_one_of_fillAt 𝒰 hfill hpos)

end KappaCeiling

/-! ### `C-M1c`, : the ambient twin does not transport to the refinement -/

section Direction

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **Restriction shrinks `nodesUnder`.**  `Tube.UniformTubeSet.restrictOccupied` keeps the
assignment and the node tubes and replaces the index set by `S.image (assign c)`, so the level-`c`
cells under a node can only be fewer. -/
theorem nodesUnder_restrictOccupied_subset
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {S : Finset ι} (hS : S ⊆ u)
    (hh : IsClassHomogeneousOn 𝒰 S) {c : ℕ} (hc : c ≤ Tube.ssfGridLen δ) (k : ℕ) (j : ι) :
    (𝒰.restrictOccupied hS hh).nodesUnder c k j ⊆ 𝒰.nodesUnder c k j := by
  classical
  intro j' hj'
  rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn,
    Tube.UniformTubeSet.mem_nodesIn_iff] at hj' ⊢
  obtain ⟨hidx, hle⟩ := hj'
  refine ⟨?_, hle⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hidx
  exact 𝒰.cover.assign_mem c hc i (hS hi)

open scoped Classical in
/-- **`C-M1c`, : the level clause's right-hand side only *shrinks* under restriction.**

`IsKatzTaoDividingWindowLevels.le_level_maxDensity` is a **lower** bound on
`Cstar · Δ_max(𝕋_c[T_j])`, and restriction can only lower `Δ_max`.  So the ambient twin gives no
information about the refined one: the implication runs the wrong way, which is exactly why
`Reduction/SpineFloorProducer.lean:29` records *"no producer by design (C-M1c)"* and routes the
failure to `(D)` through the existing
`Kakeya.ML2Core.trialOutcomeAtGain_of_refinement_dichotomy`. -/
theorem maxDensity_nodesUnder_restrictOccupied_le
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {S : Finset ι} (hS : S ⊆ u)
    (hh : IsClassHomogeneousOn 𝒰 S) {c : ℕ} (hc : c ≤ Tube.ssfGridLen δ) (k : ℕ) (j : ι) :
    Kakeya.maxDensity ((𝒰.restrictOccupied hS hh).nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) :=
  Kakeya.maxDensity_mono _ (nodesUnder_restrictOccupied_subset 𝒰 hS hh hc k j)

end Direction

end Kakeya.ML2Core

end
