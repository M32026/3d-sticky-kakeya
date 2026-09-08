/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeDichotomyGap
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWindow
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorParent

/-!
# Conjunct 2 of `hwinfloor`, assembled: three threshold rows discharged, `η'` fixed, `hfill` named

, row 3 — the one row of the four that is the floor's.

 reduced conjunct 2 at the coarse parent `p := a` to: clause 1 free (it *is* the binder
`a < m'`), clause 2 `= Kakeya.ML2Core.ParentAdmissible 𝒰 η' a a` (`X7`), clause 3 `=` the conclusion
of the existing `F4a` `Kakeya.ML2Core.floor_of_windowLevels_of_fill`, whose rows are `hCstar`, `hcap`,
`hgap`, `hclose` and `hfill`.  This file discharges the first four and names the fifth.

## `η'` is fixed, and what that costs

`hcap` is `η' ≤ e² · η_{m+1} / 64` with `e = ML2Spine.spineDiv ϖ ε₁`.  It is a free choice, and the
choice is forced to the top of its range by the *other* consumer of `η'`: clause 2 wants
`Δ_max(𝕊_a⟨S⟩) ≤ δ^{-2η'}`, which is **easier for larger `η'`**.  So take

```
    η' := ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64,
```

the largest admissible value; `hcap` is then `le_rfl`.  **The cost is a threshold, not an
inequality**: `X7` (`Kakeya.ML2Core.parentAdmissible_self`) needs `Cu ≤ δ^{-2η'}`, and the smaller
`η'` is, the smaller the `δ₀` below which that holds.  Since `η' > 0` whenever the spine is
positive, it holds eventually; nothing else in the floor reads `η'`.

## `κ ≤ 1` is respected

`Kakeya.ML2Core.le_one_of_fillAt` forces `κ ≤ 1`, and `hclose`'s discharger
`Kakeya.ML2Core.floor_exponent_closes` takes only `0 < κ` — `κ` enters its threshold through
`C₀² Cu₀ C_vol/(κ c_vol) ≤ δ^{-e²τ₁/2}`, so a smaller `κ` buys a smaller `δ₀` and nothing else.
**No room is bought by raising `κ`**, and none is needed.

## `hfill` — the one row that does not close here, and its owner

`hfill` is `FillAt 𝒰 κ a m' jp` at every level-`a` node, every cell under it and every
`m' ∈ (a, b]`.  Its engine is the existing `Kakeya.ML2Core.fillAt_of_biasedMaximizer`, whose four rows
are `hg2` (existing, `exists_biasedMaximizer_densityIn_ge`), `hκ`, `hvol` and

```
    hretain : 𝒰.nodesUnder m' a jp
      = Kakeya.familyIn (𝒰.nodesUnder m' k j) V (t.convexHull_biUnion V)
```

— *the level-`a` node's cells are **exactly** the cells inside a maximizer's hull*.  That is the row
 already measured and **refuted for its only candidate
producer**: `X2′` gives the *scale*, not the *node*, and not even a `⊇`.  The alternative route,
`Kakeya.ML2Core.fillAt_of_maximizer_witness`, replaces `hretain` by `hattain` — *the cells
under `jp` attain the maximal density of the coarser node's family* — which is likewise a property
of the cover's node selection.

**Both are statements about how the hierarchy's nodes are chosen, i.e. about the producer's
construction — the same owner as `S1`.**  So conjunct 2 closes to exactly one row, and that
row is not the floor's either.  Per instruction I stop at the boundary and do not build it.

## Family / shading / level pair

Everything in this file is about **one** family and **one** shading: the hierarchy `𝒰` on `u` with
family `fun i ↦ (V i).toTube`, no shading (`FloorHypothesisAt` and `F4a` are statements about tubes
and node counts, not about `Z`).  The level pairs are `(a, m')` for `m'` in the window's ceiling
range and `(m', a)` in the count floor's `𝒰.nodesUnder m' a jp`.  At `p := a` the parent level and
the coarse level coincide, which is why clause 1 degenerates to its own binder.
-/

@[expose] public section

open MeasureTheory Metric Tube Topology Filter
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

section ConjunctTwo

/-- **The `η'` the floor runs at**: the top of `hcap`'s range. -/
noncomputable def floorEtaPrime (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (m : ℕ) : ℝ :=
  ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64

theorem floorEtaPrime_le (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (m : ℕ) :
    floorEtaPrime β ϖ ε₁ gain dens m
      ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64 :=
  le_rfl

/-- **`hCstar`, discharged.**  `Cstar = C · totalLoss C Kl cl δ` sits under `δ^{-ν/20}` below a
threshold that depends only on `C`, `Kl`, `cl` and `ν` — 's row, from the existing
`Kakeya.ML2Reduction.exists_threshold_constMulTotalLoss_le`. -/
theorem eventually_cstar_le {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (C : NNReal) (hC : 1 ≤ C) (Kl cl : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
        ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) := by
  have hν : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ0 hϖ hε₁ hgain hdens
  obtain ⟨δ₀, hδ₀0, -, hthr⟩ :=
    ML2Reduction.exists_threshold_constMulTotalLoss_le C hC Kl cl
      (α := ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (by positivity)
  filter_upwards [Ioc_mem_nhdsGT hδ₀0] with δ hδ
  have hδ0 : 0 < δ := hδ.1
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have h := hthr hδ0 hδ.2
  rwa [← ENNReal.ofReal_rpow_of_pos hδr, ENNReal.ofReal_coe_nnreal] at h

/-- **`hgap`, discharged.**  The factor-`4` grid gap `4 ρ_c ≤ ρ_p` for `p < c`, from the existing
`Kakeya.ML2Core.four_mul_gridScale_le_of_log` below
`Kakeya.ML2Core.exists_threshold_two_mul_ssfGridLen_le_log`'s absolute threshold `e^{-8}`. -/
theorem eventually_gap :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ p c : ℕ, p < c →
        4 * (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)
          ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ) := by
  obtain ⟨δ₀, hδ₀0, hδ₀1, hthr⟩ := exists_threshold_two_mul_ssfGridLen_le_log
  obtain ⟨δ₁, hδ₁0, hδ₁1, hlen⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le (1 : ℝ) le_rfl 1 1 (1 : ℝ) one_pos
  filter_upwards [Ioc_mem_nhdsGT hδ₀0, Ioc_mem_nhdsGT hδ₁0] with δ hδ hδ'
  intro p c hpc
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2.trans hδ₀1
  have hN : 0 < Tube.ssfGridLen δ := (hlen hδ'.1 hδ'.2).1
  exact_mod_cast four_mul_gridScale_le_of_log hδ0 hδ1 hN (hthr δ hδ0 hδ.2) hpc

/-- **Conjunct 2 of `hwinfloor`, assembled.**  Below a threshold depending only on
`β, ϖ, ε₁, gain, dens, κ, C, Kl, cl, Cu₀, m` — never on the family or the scale — the twin plus `X7`
plus `hfill` give `Kakeya.ML2Core.FloorHypothesisAt` at the coarse parent `p := a` and at
`η' := Kakeya.ML2Core.floorEtaPrime`.

The three threshold rows of `F4a` are discharged inside: `hCstar` by
`Kakeya.ML2Core.eventually_cstar_le`, `hgap` by `Kakeya.ML2Core.eventually_gap`, `hclose` by the
existing `Kakeya.ML2Core.floor_exponent_closes`; `hcap` is `le_rfl` at the chosen `η'`.

**What is left is `hfill`, and only `hfill`** — see this file's module docstring for its two
candidate engines and why both reduce to a property of the producer's node selection, not of the
floor. -/
theorem eventually_floorHypothesisAt_of_window_of_fill {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {κ : ℝ} (hκ : 0 < κ) (C : NNReal) (hC : 1 ≤ C) (Kl cl : ℕ) (Cu₀ : NNReal) (m : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} {Cu : NNReal}, Cu ≤ Cu₀ →
      ∀ {u : Finset ι}, u.Nonempty →
      ∀ {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu),
        (∀ i ∈ u, ((V i).toTube).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      ∀ {a b : ℕ},
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰
          ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
          (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
          (ML2Spine.spineCount ϖ ε₁) a b m →
        ParentAdmissible 𝒰 (floorEtaPrime β ϖ ε₁ gain dens m) a a →
        (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder a a jθ, ∀ m' : ℕ, a < m' → m' ≤ b →
          FillAt 𝒰 κ a m' jp) →
        FloorHypothesisAt β ϖ ε₁ gain dens (floorEtaPrime β ϖ ε₁ gain dens m) 𝒰 a b m := by
  have hC₀ : (0 : ℝ) < twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3)) :=
    twoScaleConst_pos.{u, 0} (EuclideanSpace ℝ (Fin 3))
  have hη' : 0 < floorEtaPrime β ϖ ε₁ gain dens m := by
    have he : 0 < ML2Spine.spineDiv ϖ ε₁ := ML2Spine.spineDiv_pos hϖ hε₁
    have hτ : 0 < ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) :=
      (ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens).rung_pos (m + 1)
    unfold floorEtaPrime; positivity
  filter_upwards [eventually_cstar_le hβ0 hϖ hε₁ hgain hdens C hC Kl cl, eventually_gap,
    floor_exponent_closes hβ0 hβ1 hϖ hε₁ hgain hdens hκ Cu₀ hC₀,
    Ioo_mem_nhdsGT (zero_lt_one' NNReal)] with δ hCstar hgapδ hcloseδ hδ1
  intro ι Cu hCu u hu V 𝒰 hball a b hwin hpar hfill
  exact floorHypothesisAt_of_windowLevels hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ1.1 hδ1.2 𝒰 hu hball
    hwin hCstar (floorEtaPrime_le β ϖ ε₁ gain dens m)
    (fun p c _ hpc _ => hgapδ p c hpc) hpar hfill
    (fun m' h1 h2 _ => hcloseδ hCu hCstar hwin.coarse_lt_fine hwin.fine_le_gridLen hwin.scale_sep
      (floorEtaPrime_le β ϖ ε₁ gain dens m) le_rfl m' h1 h2)

end ConjunctTwo

/-! ### `hfill`'s own obstruction at the coarse reading node -/

section FillObstruction

variable {ι : Type*} {δ C : NNReal} {s : Finset ι} {N : ℕ}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {T : ι → Tube δ E}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- The maximizer's hull lies inside the reading node: `t` is a subfamily of the cells under
`(k, j)`, each of which is contained in that node, and the node's carrier is convex. -/
theorem convexHull_biUnion_subset_of_subset_nodesUnder (𝒰 : Tube.UniformTubeSet s T N C)
    {c k : ℕ} {j : ι} {t : Finset ι} (hne : t.Nonempty) (ht : t ⊆ 𝒰.nodesUnder c k j) :
    (t.convexHull_biUnion (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier
      ⊆ (𝒰.cover.tube k j).carrier := by
  classical
  refine (hne.convexHull_biUnion_subset_iff _
    (𝒰.cover.tube k j).toConvexSpaceBody.isConvexSet).mpr ?_
  intro j' hj'
  exact SetLike.coe_subset_coe.mpr ((𝒰.mem_nodesIn_iff c _ j').mp (ht hj')).2

omit [Nontrivial E] in
open scoped Classical in
/-- **`hfill` cannot be read at its own node.**  `fillAt_of_biasedMaximizer`'s `hvol` asks
`|T_{k,j}| ≤ |hull(t)|` while `hull(t) ⊆ T_{k,j}`, so at the *same* node the two force measure
equality — the obstruction again, now at `F4a`'s row.

Consequence for `hfill` at `F4a`'s instantiation `q := p := a`: the reading node `(k, j)` may not be
`(a, jp)`; it must be a **strictly coarser** node whose maximizer hull already has the volume of
`T_{a,jp}`.  `F4a` quantifies `hfill` at the window's own coarse level `a`, so that coarser node
lies **outside** the window — one more thing `hfill` needs that the site does not carry. -/
theorem volume_eq_of_hvol_maximizer (𝒰 : Tube.UniformTubeSet s T N C)
    {c k : ℕ} {j : ι} {t : Finset ι} (hne : t.Nonempty) (ht : t ⊆ 𝒰.nodesUnder c k j)
    (hvol : volume (𝒰.cover.tube k j).carrier
      ≤ volume (t.convexHull_biUnion
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier) :
    volume (t.convexHull_biUnion
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier
      = volume (𝒰.cover.tube k j).carrier :=
  le_antisymm (measure_mono (convexHull_biUnion_subset_of_subset_nodesUnder 𝒰 hne ht)) hvol

end FillObstruction

end Kakeya.ML2Core

end
