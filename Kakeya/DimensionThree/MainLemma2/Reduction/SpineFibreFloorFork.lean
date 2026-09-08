/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreFillMeasure
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeParentFill

/-!
# The (F)/(P) fork: the parent `p` unlocked, and the "every `m' > p`" demand measured

the map, items 3 and 4.  The structural unlock is done and needs **no condition**; the geometric
residue is measured and reported with lines.

## The unlock: `FloorHypothesisAt` at a parent the fork chooses

`Kakeya.ML2Core.floorHypothesisAt_of_countFloor` is hard-wired at `p := a` — its proof term is
`⟨a, le_rfl, …⟩` — which is why every route so far had to take `p = a` and pay
`ParentAdmissible 𝒰 η' a a`.  But `Kakeya.ML2Core.floor_of_windowLevels_of_fill`
(`SpineFloorCount.lean:368`) **already takes `p` from outside** (`hap : a ≤ p`,
`hpar : ParentAdmissible 𝒰 η' a p`, fill at `p`), and its conclusion is `FloorHypothesisAt`'s
third conjunct at `p` verbatim.  So the general-`p` producer is a direct anonymous-constructor
build:

  `floorHypothesisAt_of_fork_parent : ⟨p, hap, hfirst, hpar, floor_of_windowLevels_of_fill …⟩`

with `hfirst` the source's *"a genuine parent level `p` satisfying `a ≤ p < m` for every
`m ∈ 𝒲`"* (l.4066-4067) — an output of the fork, as  says.  **`FloorHypothesisAt`'s body is not
touched**, so `RefinedFloorHypothesis` and the two guarded statements keep their meaning
(Condition F1) and the `Iff.rfl` compatibility is untouched.

`FloorForkAt` is the fork as one row — `(F)`-data at a chosen `p`, or `Pdata` — and
`floorHypothesisAt_or_of_fork` consumes it into `FloorHypothesisAt ∨ Pdata`, which is §RR3's
shape: the `p` of (F) and the exit to (P) are two outputs of the same fork.  `Pdata` is a
parameter, so the (P) consumer can be plugged in without re-cutting this row.

## Item 3's question, answered: the "every `m' > p`" demand does **not** follow

The demand is real and the tree's only route between levels is the existing chaining
`Kakeya.ML2Core.fillAt_trans` / `fill_binder_of_trans` (`SpineFloorShapeParentFill.lean:513, 541`).
That chaining takes

* `hfillP` — fill from `p` into **one** intermediate level `m₀`, at every level-`p` node;
* `hfillM` — fill from `m₀` into **every** `c ∈ (m₀, b]`, at every level-`m₀` node;
* `hbelow` — the finitely many levels strictly between `p` and `m₀`;

and returns exactly the binder `floor_of_windowLevels_of_fill` consumes.  So it is a genuine
**transitivity**, not an elimination: the "every level" quantifier moves from `p` down to `m₀` and
does not disappear.  `fill_binder_of_all_levels` compiles the degenerate reading that makes this
precise — at `m₀ = p`, `hfillM` **is** the conclusion, so the chaining adds nothing there.

**The obstruction, verbatim.**  The source asserts the count floor *"for every `m ∈ 𝒲` with
`m > p`"* (l.4137-4139) and identifies `p` as *"the first scale at which the transverse factor
becomes small"*.  Turning that into the tree's `hfill` binder requires *"the transverse factor
stays small above `p`"* — and in the tree's vocabulary that sentence **is** `∀ m' > p, FillAt 𝒰 κ p
m' jp`, i.e. the conclusion itself, not a hypothesis one can discharge from the factoring at the
single scale `p`.  What would close it is a monotonicity of the biased factoring's John dimensions
under refinement of the scale — *"the transverse factor of the level-`m'` factoring is at most that
of the level-`p` factoring for `m' > p`"* — and no such statement exists in the tree:
`ConvexSpaceBody.nonempty_biasedFactorization` (`Factorization.lean:1581`) is a single-scale
statement, its `simDims` field compares outer bodies **within one factoring**, and nothing relates
two factorings at different scales.  First-scale minimality (the `p` is least) gives the factor is
**not** small *below* `p`; it says nothing above.

That is the exact remaining geometric row, and it is one row: *fill at every window level above the
fork's `p`*, equivalently the cross-scale monotonicity of the factoring.  `fillAt_trans` reduces it
to two levels (`p → m₀` and `m₀ → every c`), which is a real reduction in the number of
*independent* obligations but not in the quantifier.

## What this leaf does **not** do

The (P) branch is carried as the parameter `Pdata`; its eccentric-data consumer is not reached this
pass, so the `η' → 0` and eccentricity-threshold controls have no statement to fire against here —
`hclose` was not re-cut (B19 measured that re-cutting it moves a prefactor while the row above it
stays underivable).

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `floorHypothesisAt_of_fork_parent` | the tower's `u'`; shading only through `V` | `(a,p,b,m)` |
| `FloorForkAt`, `floorHypothesisAt_or_of_fork` | as above | `(a,p,b)` |
| `fill_binder_of_all_levels` | as above | `(a,p,b)` |

## A1-a

No `GridUniformCore`; no `(F)`-branch interface statement is defined or altered; `FloorHypothesisAt`
is inhabited through its own constructor with the existing producer supplying conjunct 3.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section Fork

universe u

variable {ι : Type u} {δ Cu : NNReal} {u' : Finset ι}
  {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`FloorHypothesisAt` at a parent `p` the fork chooses.** -/
theorem floorHypothesisAt_of_fork_parent {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (𝒰 : Tube.UniformTubeSet u' (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (hs : u'.Nonempty)
    (hball : ∀ i ∈ u', ((V i).toTube).carrier
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
    {p : ℕ} (hap : a ≤ p)
    (hfirst : ∀ m' : ℕ, a < m' → m' < b →
      ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
        ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
      p < m')
    (hpar : ParentAdmissible 𝒰 η' a p)
    (hfill : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, p < m' → m' ≤ b →
      FillAt 𝒰 κ p m' jp)
    (hclose : ∀ m' : ℕ, a + ⌈ML2Spine.spineDiv ϖ ε₁ * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m' → p < m' →
      m' ≤ b →
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
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
  ⟨p, hap, hfirst, hpar,
    floor_of_windowLevels_of_fill hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1 𝒰 hs hball
      hwin hCstar hcap hgap hap hpar hfill hclose⟩

open scoped Classical in
/-- **The (F)/(P) fork, as one row.** -/
def FloorForkAt (ϖ ε₁ η' κ : ℝ) {u' : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u' (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (a b : ℕ) (Pdata : Prop) : Prop :=
  (∃ p : ℕ, a ≤ p ∧
    (∀ m' : ℕ, a < m' → m' < b →
      ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
        ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
      p < m') ∧
    ParentAdmissible 𝒰 η' a p ∧
    (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, p < m' → m' ≤ b →
      FillAt 𝒰 κ p m' jp))
  ∨ Pdata

open scoped Classical in
/-- **The fork consumed: `FloorHypothesisAt` or the (P) exit.** -/
theorem floorHypothesisAt_or_of_fork {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ} {Pdata : Prop}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (𝒰 : Tube.UniformTubeSet u' (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (hs : u'.Nonempty)
    (hball : ∀ i ∈ u', ((V i).toTube).carrier
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
    (hclose : ∀ p : ℕ, a ≤ p → ∀ m' : ℕ,
      a + ⌈ML2Spine.spineDiv ϖ ε₁ * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m' → p < m' → m' ≤ b →
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
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
            : ENNReal))
    (hfork : FloorForkAt ϖ ε₁ η' κ 𝒰 a b Pdata) :
    FloorHypothesisAt β ϖ ε₁ gain dens η' 𝒰 a b m ∨ Pdata := by
  rcases hfork with ⟨p, hap, hfirst, hpar, hfill⟩ | hP
  · exact Or.inl (floorHypothesisAt_of_fork_parent hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1
      𝒰 hs hball hwin hCstar hcap hgap hap hfirst hpar hfill (hclose p hap))
  · exact Or.inr hP

open scoped Classical in
/-- **Control: at `m₀ = p` the existing chaining is a fixpoint, not a reduction.** -/
theorem fill_binder_of_all_levels
    (𝒰 : Tube.UniformTubeSet u' (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    {κ : ℝ} {a p b : ℕ}
    (hfill : ∀ c : ℕ, p < c → c ≤ b → ∀ j ∈ 𝒰.cover.indexSet p, FillAt 𝒰 κ p c j) :
    ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ c : ℕ, p < c → c ≤ b →
      FillAt 𝒰 κ p c jp := by
  classical
  intro jθ _ jp hjp c hpc hcb
  refine hfill c hpc hcb jp ?_
  have h := hjp
  simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn,
    Finset.mem_filter] at h
  exact h.1

end Fork

end Kakeya.ML2Core

end
