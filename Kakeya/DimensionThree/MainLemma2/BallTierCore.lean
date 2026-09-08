/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallJoint
public import Kakeya.DimensionThree.MainLemma2.ThinSetup

/-!
# Passing a `BallDataCore` to a tier of its segments

General-branch steps **G3**. GWZ §9.3
refines the per-ball segment families twice before running the biased maximal density
factoring of Lemma 9.2 (`gwz.txt` l.2024–2028, l.2032, l.2036–2038): first to the segments
whose shading is a `⪆ δ^{2η}` fraction of their carrier (the Markov / heavy-piece tier, the
`segs_density` clause of `Kakeya.VeryNotSticky.BallData`), then to one dyadic class of the
shade fraction `|Y_B(T_B)|/|T_B|` — the pigeonhole that turns Lemma 9.2's *carrier* retention
into *shade* retention. This file performs an arbitrary such refinement.

## The tier core

`Kakeya.VeryNotSticky.tierCore` takes a `Kakeya.VeryNotSticky.BallDataCore`, a tier
`tier B ⊆ core.segs B` in every ball, the tier's non-emptiness, and a **retention factor**
`K` with `K⁻¹ ∑_{p ∈ segs B} |Y_B(p)| ≤ ∑_{p ∈ tier B} |Y_B(p)|` per ball, and returns a
`BallDataCore` with `segs := tier` and the working shading

  `Y_g'(T) = ⋃_{B ∈ 𝔅} (Y_g(T) ∩ Z_B(T) ∩ B̂)`,  `Z_B(T) = Y_B(T_B)` for the tier parent `T_B`,

which `Kakeya.VeryNotSticky.tierYg_eq_inter` identifies with
`Y_g(T) ∩ ⋃_{B} ⋃_{p ∈ tier B, T ∈ fam p} Y_B(p)`. All forty-two fields are re-established;
the six that are not inherited by restriction are
`Kakeya.VeryNotSticky.tierYg_cover` (C2 `P_cover`),
`Kakeya.VeryNotSticky.tierYg_parent`, `Kakeya.VeryNotSticky.tierYg_into`,
`Kakeya.VeryNotSticky.tierYg_back`, `Kakeya.VeryNotSticky.tierYg_fibre` (C5) and
`Kakeya.VeryNotSticky.tierYg_mass_of_retention` (C5′ `Yg_mass`), and the loss of the working
shading is the **explicit**

  `Cg' = Cg · Cm² · K`.

The two factors of `Cm` are the fibre-count comparison, spent once in each direction by
`Kakeya.ThinCase.lift`; the amalgamation over the balls is `Kakeya.ThinCase.globalShading`.
Nothing else changes: `C₀`, `D`, `m`, `Cm`, the ball cover and the pieces are copied
(`Kakeya.VeryNotSticky.tierCore_C₀` and the other projection lemmas).

**Why `Y_g` must be intersected in.** The plan's formula for the new working shading was
`⋃_{B} ⋃_{p ∈ tier B, T ∈ fam p} Y_B(p)` without the intersection with `Y_g(T)`. That set is
**not** admissible: (C5′) `Yg_subset` asks for `Y_g'(T) ⊆ Y(T)`, and no field of
`BallDataCore` bounds a segment's shading by the shading of a *single* parent — `back` gives
only `Y_B(p) ⊆ ⋃_{T ∈ fam p} Y_g(T)`, a union over the whole parent family. For the same
reason the upper half of `fibre` would fail: on `Y_B(p)` the fibre
`{T ∈ fam p | x ∈ Y_g'(T)}` would be **all** of `fam p`, and `|fam p| ≤ Cm m` is not
available. With the intersection both hold, and the fibre is unchanged in both directions
(`Kakeya.VeryNotSticky.tierYg_fibre_filter_eq`).

## The two tiers of GWZ §9.3

* `Kakeya.VeryNotSticky.markovTier` — the segments with
  `c₁ δ^{2η} |T_B| ≤ |Y_B(T_B)|`, i.e. the `segs_density` predicate itself
  (`Kakeya.VeryNotSticky.markovTier_density`). Its mass lemma
  `Kakeya.VeryNotSticky.markovTier_retention` retains **half** the shading mass of every ball
  whose segment family is full at twice the threshold (GWZ l.2032's `λ(𝕋_B, Y_B) ⪆ δ^η`), so
  `K = 2`.
* `Kakeya.VeryNotSticky.shadeFractionClass` — the dyadic class of the shade fraction, defined
  log-free as the least `k` with `|T_B| ≤ 2^k |Y_B(T_B)|`, and
  `Kakeya.VeryNotSticky.classTier` the tier of one class, chosen per ball. Above the Markov
  threshold there are at most `⌈log₂ (1/(c₁ δ^{2η}))⌉₊ + 1` classes
  (`Kakeya.VeryNotSticky.shadeFractionClassBound`,
  `Kakeya.VeryNotSticky.shadeFractionClass_le_of_markov`),
  so the pigeonhole `Kakeya.VeryNotSticky.exists_class_retaining` gives
  `K = ⌈log₂ (1/(c₁ δ^{2η}))⌉₊ + 1`.

Composed (`Kakeya.VeryNotSticky.markovDyadicTier`,
`Kakeya.VeryNotSticky.exists_markovDyadicTier_retention`) the retention factor is
`Kakeya.VeryNotSticky.tierRetention = 2 (⌈log₂ (1/(c₁ δ^{2η}))⌉₊ + 1)` — the Markov factor
times the number of classes — and the tier core
`Kakeya.VeryNotSticky.markovDyadicTierCore` has

  `Cg' = Cg · Cm² · 2 · (⌈log₂ (1/(c₁ δ^{2η}))⌉₊ + 1)`,

**polylogarithmic in `1/δ`, never a power of `δ`** (`Kakeya.VeryNotSticky.tierRetention` is a
`Nat.ceil` of a `Real.logb`, not of `1/δ` itself), which is what lets the general branch bound
`bd.Cg ≤ δ^{-ε}` eventually. The tier delivers `segs_density`
(`Kakeya.VeryNotSticky.markovDyadicTierCore_segs_density`) — a `BallData` clause no
`BallDataCore` field provides — and, within each ball, a single dyadic shade-fraction class
(`Kakeya.VeryNotSticky.markovDyadicTier_shadeFractionClass_eq`).

## What is a hypothesis and why

`hne` (the tier is non-empty in every ball) and the retention `hret` are the tier's own data:
for an arbitrary tier neither is a theorem. `Kakeya.VeryNotSticky.tier_nonempty_of_retention`
reduces `hne` to positivity of the ball's segment shading mass, and both delivered tiers
**prove** their `hret`. The per-ball fullness input of
`Kakeya.VeryNotSticky.markovTier_retention` is GWZ's own heavy-ball hypothesis; dropping the
balls where it fails is GWZ l.2029–2030/l.2039–2041, i.e. steps G4, not this file.

Nothing here changes a existing statement.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

universe u

namespace Kakeya.VeryNotSticky

section TierCore

variable {cfg : VeryNotSticky.{u}}

open scoped Classical in
/-- The working shading a **tier** of segments carries inside one ball. -/
noncomputable def tierZ (core : BallDataCore cfg) (tier : core.bι → Finset core.σ)
    (B : core.bι) (i : cfg.ι) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ p ∈ core.segs B, if i ∈ core.fam p ∧ p ∈ tier B then (core.Y p).shade else ∅

open scoped Classical in
/-- The working shading of the tier core. -/
noncomputable def tierYg (core : BallDataCore cfg) (tier : core.bι → Finset core.σ)
    (i : cfg.ι) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ B ∈ core.bs, core.Yg i ∩ tierZ core tier B i ∩ core.P B

variable (core : BallDataCore cfg) (tier : core.bι → Finset core.σ)

/-- A segment of the tier contributes its whole shading to `tierZ`. -/
theorem shade_subset_tierZ {B : core.bι} {p : core.σ} (hp : p ∈ core.segs B)
    (hpt : p ∈ tier B) {i : cfg.ι} (hip : i ∈ core.fam p) :
    (core.Y p).shade ⊆ tierZ core tier B i := by
  classical
  intro x hx
  exact Set.mem_biUnion hp (by simp [hip, hpt, hx])

/-- `tierZ` is the shading of the (unique) parent segment of `i` in `B`, when that segment
lies in the tier. -/
theorem tierZ_eq {B : core.bι} (hB : B ∈ core.bs) {p : core.σ} (hp : p ∈ core.segs B)
    (hpt : p ∈ tier B) {i : cfg.ι} (hip : i ∈ core.fam p) :
    tierZ core tier B i = (core.Y p).shade := by
  classical
  refine Set.Subset.antisymm ?_ (shade_subset_tierZ core tier hp hpt hip)
  intro x hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hx
  by_cases hcond : i ∈ core.fam q ∧ q ∈ tier B
  · have hx' : x ∈ (core.Y q).shade := by simpa [hcond] using hxq
    have hqp : q = p := by
      by_contra hne
      exact (Finset.disjoint_left.mp (core.fam_disjoint B hB hq hp hne)) hcond.1 hip
    simpa [hqp] using hx'
  · simp [hcond] at hxq

/-- `tierZ` is empty when no segment of the ball has `i` as a parent. -/
theorem tierZ_eq_empty {B : core.bι} {i : cfg.ι}
    (hnone : ∀ p ∈ core.segs B, i ∉ core.fam p) : tierZ core tier B i = ∅ := by
  classical
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hx
  by_cases hcond : i ∈ core.fam q ∧ q ∈ tier B
  · exact hnone q hq hcond.1
  · simp [hcond] at hxq

/-- `tierZ` lies in the piece of its ball. -/
theorem tierZ_subset_piece {B : core.bι} (hB : B ∈ core.bs) (i : cfg.ι) :
    tierZ core tier B i ⊆ core.P B := by
  classical
  intro x hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hx
  by_cases hcond : i ∈ core.fam q ∧ q ∈ tier B
  · have hx' : x ∈ (core.Y q).shade := by simpa [hcond] using hxq
    exact core.Y_piece B hB q hq hx'
  · simp [hcond] at hxq

theorem measurableSet_tierZ (B : core.bι) (i : cfg.ι) :
    MeasurableSet (tierZ core tier B i) := by
  classical
  refine Finset.measurableSet_biUnion _ fun q _ => ?_
  by_cases hcond : i ∈ core.fam q ∧ q ∈ tier B
  · simpa [hcond] using (core.Y q).measurableSet_shade
  · simp [hcond]

theorem tierYg_subset (i : cfg.ι) : tierYg core tier i ⊆ core.Yg i := by
  refine Set.iUnion₂_subset fun B _ => ?_
  exact Set.inter_subset_left.trans Set.inter_subset_left

theorem measurableSet_tierYg {i : cfg.ι} (hi : i ∈ cfg.s) :
    MeasurableSet (tierYg core tier i) := by
  refine Finset.measurableSet_biUnion _ fun B hB => ?_
  exact ((core.Yg_measurable i hi).inter (measurableSet_tierZ core tier B i)).inter
    (core.P_measurable B hB)

/-- The pieces are disjoint, so the term of `tierYg` meeting `P B` is the `B`-th one. -/
theorem tierYg_inter_piece_subset {B : core.bι} (hB : B ∈ core.bs) (i : cfg.ι) :
    tierYg core tier i ∩ core.P B ⊆ tierZ core tier B i := by
  intro x hx
  obtain ⟨B', hB', hxB'⟩ := Set.mem_iUnion₂.1 hx.1
  have hBB' : B' = B := by
    by_contra hne
    exact Set.disjoint_left.mp (core.P_disjoint hB' hB hne) hxB'.2 hx.2
  exact hBB' ▸ hxB'.1.2

/-- If the (unique) parent segment of `i` in `B` is **not** in the tier, the tier shading of
`i` in `B` is empty. -/
theorem tierZ_eq_empty_of_notMem {B : core.bι} (hB : B ∈ core.bs) {p : core.σ}
    (hp : p ∈ core.segs B) {i : cfg.ι} (hip : i ∈ core.fam p) (hpt : p ∉ tier B) :
    tierZ core tier B i = ∅ := by
  classical
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hx
  by_cases hcond : i ∈ core.fam q ∧ q ∈ tier B
  · have hqp : q = p := by
      by_contra hne
      exact (Finset.disjoint_left.mp (core.fam_disjoint B hB hq hp hne)) hcond.1 hip
    exact hpt (hqp ▸ hcond.2)
  · simp [hcond] at hxq

open scoped Classical in
/-- **The mass of the tier shading.** If in every ball the tier retains a `K⁻¹` fraction of the
segment shading mass, the tier shading retains a `(Cm² K)⁻¹` fraction of the working shading
mass. The two factors of `Cm` are the fibre-count comparison spent once in each direction by
`Kakeya.ThinCase.lift`; the amalgamation over the balls is
`Kakeya.ThinCase.globalShading`. -/
theorem tierYg_mass_of_retention (htier : ∀ B, tier B ⊆ core.segs B) {K : NNReal}
    (hK : 1 ≤ K)
    (hret : ∀ B ∈ core.bs, (K : ENNReal)⁻¹ * ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
      ∑ p ∈ tier B, volume (core.Y p).shade) :
    ((core.Cm ^ 2 * K : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i) ≤
      ∑ i ∈ cfg.s, volume (tierYg core tier i) := by
  classical
  have hK0 : (K : NNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK)
  have hCm0 : (core.Cm : NNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one core.hCm)
  have hCmsq0 : ((core.Cm : ENNReal) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hCm0)
  have hCmsqtop : ((core.Cm : ENNReal) ^ 2) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.coe_ne_top (r := core.Cm))
  have hprod0 : ((core.Cm ^ 2 * K : NNReal)) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hCm0) hK0
  -- the per-ball lift
  have hlift : ∀ B ∈ core.bs,
      ((((core.Cm ^ 2 * K : NNReal))⁻¹ : NNReal) : ENNReal) *
          ∑ i ∈ cfg.s, volume (core.Yg i ∩ core.P B) ≤
        ∑ i ∈ cfg.s, volume (core.Yg i ∩ tierZ core tier B i) := by
    intro B hB
    have hY2 : ∀ p ∈ core.segs B, ∀ i ∈ core.fam p,
        core.Yg i ∩ tierZ core tier B i =
          core.Yg i ∩ (if p ∈ tier B then (core.Y p).shade else ∅) := by
      intro p hp i hi
      by_cases hpt : p ∈ tier B
      · rw [tierZ_eq core tier hB hp hpt hi, if_pos hpt]
      · rw [tierZ_eq_empty_of_notMem core tier hB hp hi hpt, if_neg hpt]
    have hY2e : ∀ i ∈ cfg.s, (∀ p ∈ core.segs B, i ∉ core.fam p) →
        core.Yg i ∩ tierZ core tier B i = ∅ := by
      intro i _ hnone
      rw [tierZ_eq_empty core tier hnone, Set.inter_empty]
    have hraw := Kakeya.ThinCase.lift cfg.s core.Yg (core.P B) (core.segs B)
      (fun p => (core.Y p).shade) (fun p => if p ∈ tier B then (core.Y p).shade else ∅)
      core.fam (fun i => core.Yg i ∩ tierZ core tier B i)
      (core.P_measurable B hB) core.Yg_measurable
      (fun p _ => (core.Y p).measurableSet_shade)
      (fun p _ => by
        by_cases hpt : p ∈ tier B
        · simpa [hpt] using (core.Y p).measurableSet_shade
        · simp [hpt])
      (fun p hp => core.fam_subset B hB p hp) (core.fam_disjoint B hB)
      (fun p _ => by
        by_cases hpt : p ∈ tier B
        · simp [hpt]
        · simp [hpt])
      (fun p hp => core.Y_piece B hB p hp)
      (fun i hi => core.parent B hB i hi) (fun p hp i hi => core.into B hB p hp i hi)
      hY2 hY2e core.hCm (core.fibre B hB)
      (c := 1) (κ := K⁻¹) (tier B) (htier B)
      (by simpa [ENNReal.coe_inv hK0] using hret B hB)
      (fun p hp => by simp [hp])
    have hraw' : ((K : ENNReal))⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i ∩ core.P B) ≤
        (core.Cm : ENNReal) ^ 2 * ∑ i ∈ cfg.s, volume (core.Yg i ∩ tierZ core tier B i) := by
      simpa [ENNReal.coe_inv hK0] using hraw
    have hcoe : ((((core.Cm ^ 2 * K : NNReal))⁻¹ : NNReal) : ENNReal) =
        ((core.Cm : ENNReal) ^ 2)⁻¹ * ((K : ENNReal))⁻¹ := by
      rw [ENNReal.coe_inv hprod0]
      push_cast
      rw [ENNReal.mul_inv (Or.inl hCmsq0) (Or.inl hCmsqtop)]
    rw [hcoe, mul_assoc]
    calc ((core.Cm : ENNReal) ^ 2)⁻¹ *
            (((K : ENNReal))⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i ∩ core.P B))
        ≤ ((core.Cm : ENNReal) ^ 2)⁻¹ *
            ((core.Cm : ENNReal) ^ 2 *
              ∑ i ∈ cfg.s, volume (core.Yg i ∩ tierZ core tier B i)) :=
          mul_le_mul_of_nonneg_left hraw' zero_le
      _ = ∑ i ∈ cfg.s, volume (core.Yg i ∩ tierZ core tier B i) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hCmsq0 hCmsqtop, one_mul]
  have hgs := Kakeya.ThinCase.globalShading cfg.s core.bs core.P core.P_disjoint
    core.P_measurable core.Yg core.Yg_measurable core.P_cover (tierZ core tier)
    (fun B hB i _ => tierZ_subset_piece core tier hB i)
    (fun B _ i _ => measurableSet_tierZ core tier B i)
    (c := (core.Cm ^ 2 * K)⁻¹) hlift (tierYg core tier) (fun i _ => rfl)
  have hmass := hgs.2.2.2
  rwa [ENNReal.coe_inv hprod0] at hmass

/-- **The tier shading is the plan's formula, cut by the working shading.** `tierYg` was
written as an amalgamation over the balls (the shape
`Kakeya.ThinCase.globalShading` consumes); this identity says it is exactly
`Y_g(T) ∩ ⋃_{B} ⋃_{p ∈ tier B, T ∈ fam p} Y_B(p)`, i.e. the union of the tier's segment
shadings **intersected with `Y_g(T)`**. The intersection is not cosmetic: see the module
docstring. -/
theorem tierYg_eq_inter (htier : ∀ B, tier B ⊆ core.segs B) (i : cfg.ι) :
    tierYg core tier i =
      core.Yg i ∩ ⋃ B ∈ core.bs, ⋃ p ∈ tier B, ⋃ (_ : i ∈ core.fam p), (core.Y p).shade := by
  classical
  refine Set.Subset.antisymm (fun x hx => ⟨tierYg_subset core tier i hx, ?_⟩) ?_
  · obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hxB.1.2
    by_cases hcond : i ∈ core.fam q ∧ q ∈ tier B
    · have hx' : x ∈ (core.Y q).shade := by simpa [hcond] using hxq
      exact Set.mem_iUnion₂.2 ⟨B, hB, Set.mem_iUnion₂.2 ⟨q, hcond.2,
        Set.mem_iUnion.2 ⟨hcond.1, hx'⟩⟩⟩
    · simp [hcond] at hxq
  · intro x hx
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx.2
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hxB
    obtain ⟨hiq, hx'⟩ := Set.mem_iUnion.1 hxq
    refine Set.mem_iUnion₂.2 ⟨B, hB, ⟨⟨hx.1, ?_⟩, ?_⟩⟩
    · exact shade_subset_tierZ core tier (htier B hq) hq hiq hx'
    · exact core.Y_piece B hB q (htier B hq) hx'

/-- (C2) `P_cover` for the tier shading. -/
theorem tierYg_cover {i : cfg.ι} (hi : i ∈ cfg.s) :
    tierYg core tier i ⊆ ⋃ B ∈ core.bs, core.P B :=
  (tierYg_subset core tier i).trans (core.P_cover i hi)

/-- (C5) `parent` for the tier shading: a tube whose tier shading meets a piece has a parent
segment **in the tier**. -/
theorem tierYg_parent {B : core.bι} (hB : B ∈ core.bs) (i : cfg.ι)
    (hne : (tierYg core tier i ∩ core.P B).Nonempty) : ∃ p ∈ tier B, i ∈ core.fam p := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hxZ : x ∈ tierZ core tier B i := tierYg_inter_piece_subset core tier hB i hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hxZ
  by_cases hcond : i ∈ core.fam q ∧ q ∈ tier B
  · exact ⟨q, hcond.2, hcond.1⟩
  · simp [hcond] at hxq

/-- (C5) `into` for the tier shading. -/
theorem tierYg_into (htier : ∀ B, tier B ⊆ core.segs B)
    {B : core.bι} (hB : B ∈ core.bs) {p : core.σ} (hp : p ∈ tier B)
    {i : cfg.ι} (hip : i ∈ core.fam p) :
    tierYg core tier i ∩ core.P B ⊆ (core.Y p).shade := by
  have hseg : p ∈ core.segs B := htier B hp
  exact (tierYg_inter_piece_subset core tier hB i).trans
    (le_of_eq (tierZ_eq core tier hB hseg hp hip))

/-- (C5) `back` for the tier shading. -/
theorem tierYg_back (htier : ∀ B, tier B ⊆ core.segs B)
    {B : core.bι} (hB : B ∈ core.bs) {p : core.σ} (hp : p ∈ tier B) :
    (core.Y p).shade ⊆ ⋃ i ∈ core.fam p, tierYg core tier i := by
  intro x hx
  have hseg : p ∈ core.segs B := htier B hp
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (core.back B hB p hseg hx)
  refine Set.mem_iUnion₂.2 ⟨i, hi, Set.mem_iUnion₂.2 ⟨B, hB, ⟨⟨hxi, ?_⟩, ?_⟩⟩⟩
  · exact shade_subset_tierZ core tier hseg hp hi hx
  · exact core.Y_piece B hB p hseg hx

open scoped Classical in
/-- On the shading of a tier segment the fibre of the tier shading is the fibre of the
original working shading — so the fibre count is unchanged in both directions. -/
theorem tierYg_fibre_filter_eq (htier : ∀ B, tier B ⊆ core.segs B)
    {B : core.bι} (hB : B ∈ core.bs) {p : core.σ} (hp : p ∈ tier B)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (core.Y p).shade) :
    {i ∈ core.fam p | x ∈ tierYg core tier i} = {i ∈ core.fam p | x ∈ core.Yg i} := by
  classical
  refine Finset.filter_congr fun i hi => ?_
  have hseg : p ∈ core.segs B := htier B hp
  constructor
  · intro hxi; exact tierYg_subset core tier i hxi
  · intro hxi
    refine Set.mem_iUnion₂.2 ⟨B, hB, ⟨⟨hxi, ?_⟩, ?_⟩⟩
    · exact shade_subset_tierZ core tier hseg hp hi hx
    · exact core.Y_piece B hB p hseg hx

open scoped Classical in
/-- (C5) `fibre` for the tier shading, at the core's own `m` and `Cm`. -/
theorem tierYg_fibre (htier : ∀ B, tier B ⊆ core.segs B)
    {B : core.bι} (hB : B ∈ core.bs) {p : core.σ} (hp : p ∈ tier B)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (core.Y p).shade) :
    (core.m : ENNReal) ≤ core.Cm * {i ∈ core.fam p | x ∈ tierYg core tier i}.card ∧
      (({i ∈ core.fam p | x ∈ tierYg core tier i}.card : ℕ) : ENNReal) ≤ core.Cm * core.m := by
  classical
  rw [tierYg_fibre_filter_eq core tier htier hB hp hx]
  exact core.fibre B hB p (htier B hp) x hx

open scoped Classical in
/-- **The tier core.** A `BallDataCore` restricted to a tier of its segments, with the working
shading cut down to what the tier carries. Only the tier's data — the tier itself, its
non-emptiness in every ball, and its shade-mass retention factor `K` — is taken as input; all
forty-two fields, in particular `parent`, `into`, `back`, `fibre`, `P_cover` and `Yg_mass`, are
re-established. The loss of the working shading is the **explicit**
`Cg' = Cg · Cm² · K`. -/
noncomputable def tierCore (core : BallDataCore cfg) (tier : core.bι → Finset core.σ)
    (htier : ∀ B, tier B ⊆ core.segs B) (hne : ∀ B ∈ core.bs, (tier B).Nonempty)
    {K : NNReal} (hK : 1 ≤ K)
    (hret : ∀ B ∈ core.bs, (K : ENNReal)⁻¹ * ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
      ∑ p ∈ tier B, volume (core.Y p).shade) :
    BallDataCore cfg where
  C₀ := core.C₀
  hC₀ := core.hC₀
  D := core.D
  Yg := tierYg core tier
  Yg_subset := fun i hi => (tierYg_subset core tier i).trans (core.Yg_subset i hi)
  Yg_measurable := fun i hi => measurableSet_tierYg core tier hi
  Cg := core.Cg * core.Cm ^ 2 * K
  hCg := by
    have h2 : (1 : NNReal) ≤ core.Cm ^ 2 := one_le_pow₀ core.hCm
    calc (1 : NNReal) = 1 * 1 * 1 := by norm_num
      _ ≤ core.Cg * core.Cm ^ 2 * K := mul_le_mul' (mul_le_mul' core.hCg h2) hK
  Yg_mass := by
    have hmass := tierYg_mass_of_retention core tier htier hK hret
    have hCg0 : (core.Cg : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one core.hCg))
    have hCgtop : (core.Cg : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hsplit : ((core.Cg * core.Cm ^ 2 * K : NNReal) : ENNReal)⁻¹ =
        ((core.Cm ^ 2 * K : NNReal) : ENNReal)⁻¹ * ((core.Cg : ENNReal))⁻¹ := by
      have hmul : ((core.Cg * core.Cm ^ 2 * K : NNReal) : ENNReal) =
          (core.Cg : ENNReal) * ((core.Cm ^ 2 * K : NNReal) : ENNReal) := by
        push_cast; ring
      rw [hmul, ENNReal.mul_inv (Or.inl hCg0) (Or.inl hCgtop), mul_comm]
    rw [hsplit, mul_assoc]
    exact le_trans (mul_le_mul_of_nonneg_left core.Yg_mass zero_le) hmass
  bι := core.bι
  σ := core.σ
  bs := core.bs
  bs_nonempty := core.bs_nonempty
  ctr := core.ctr
  P := core.P
  P_subset_ball := core.P_subset_ball
  P_disjoint := core.P_disjoint
  P_measurable := core.P_measurable
  P_cover := fun i hi => tierYg_cover core tier hi
  ballOverlap := core.ballOverlap
  segs := tier
  Y := core.Y
  fam := core.fam
  segs_nonempty := hne
  fam_subset := fun B hB p hp => core.fam_subset B hB p (htier B hp)
  fam_disjoint := fun B hB =>
    (core.fam_disjoint B hB).mono (Finset.coe_subset.2 (htier B))
  Y_piece := fun B hB p hp => core.Y_piece B hB p (htier B hp)
  segs_thickness := fun B hB p hp => core.segs_thickness B hB p (htier B hp)
  segs_dims := fun B hB p hp q hq =>
    core.segs_dims B hB p (htier B hp) q (htier B hq)
  parent := fun B hB i hi hnee => tierYg_parent core tier hB i hnee
  into := fun B hB p hp i hip => tierYg_into core tier htier hB hp hip
  back := fun B hB p hp => tierYg_back core tier htier hB hp
  segs_core := fun B hB p hp => core.segs_core B hB p (htier B hp)
  m := core.m
  Cm := core.Cm
  hCm := core.hCm
  fibre := fun B hB p hp x hx => tierYg_fibre core tier htier hB hp hx
  γ := core.γ
  cov := core.cov
  covCtr := core.covCtr
  cov_isCover := fun B hB p hp => core.cov_isCover B hB p (htier B hp)
  cov_meets := fun B hB p hp => core.cov_meets B hB p (htier B hp)
  segs_subset_ball := fun B hB p hp => core.segs_subset_ball B hB p (htier B hp)
  segs_scale := fun B hB p hp => core.segs_scale B hB p (htier B hp)

section Proj

variable (core : BallDataCore cfg) (tier : core.bι → Finset core.σ)
  (htier : ∀ B, tier B ⊆ core.segs B) (hne : ∀ B ∈ core.bs, (tier B).Nonempty)
  {K : NNReal} (hK : 1 ≤ K)
  (hret : ∀ B ∈ core.bs, (K : ENNReal)⁻¹ * ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
    ∑ p ∈ tier B, volume (core.Y p).shade)

@[simp] theorem tierCore_bs : (tierCore core tier htier hne hK hret).bs = core.bs := rfl
@[simp] theorem tierCore_segs : (tierCore core tier htier hne hK hret).segs = tier := rfl
@[simp] theorem tierCore_Y : (tierCore core tier htier hne hK hret).Y = core.Y := rfl
@[simp] theorem tierCore_fam : (tierCore core tier htier hne hK hret).fam = core.fam := rfl
@[simp] theorem tierCore_Yg :
    (tierCore core tier htier hne hK hret).Yg = tierYg core tier := rfl
@[simp] theorem tierCore_Cg :
    (tierCore core tier htier hne hK hret).Cg = core.Cg * core.Cm ^ 2 * K := rfl
@[simp] theorem tierCore_C₀ : (tierCore core tier htier hne hK hret).C₀ = core.C₀ := rfl
@[simp] theorem tierCore_D : (tierCore core tier htier hne hK hret).D = core.D := rfl
@[simp] theorem tierCore_ctr : (tierCore core tier htier hne hK hret).ctr = core.ctr := rfl
@[simp] theorem tierCore_P : (tierCore core tier htier hne hK hret).P = core.P := rfl
@[simp] theorem tierCore_m : (tierCore core tier htier hne hK hret).m = core.m := rfl
@[simp] theorem tierCore_Cm : (tierCore core tier htier hne hK hret).Cm = core.Cm := rfl

/-- **`segs_dilation` transports to the tier**: the dilation clause is a `maxDensity` over the
segment family, and the tier's family is smaller (`Kakeya.maxDensity_mono`). This is the
interface `Kakeya.VeryNotSticky.segs_dilation_capsules` (T3) is consumed through on the
tier. -/
theorem tierCore_segs_dilation {Cdil : NNReal}
    (hdil : ∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
        maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
      (Cdil : ENNReal) * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) :
    ∀ B ∈ (tierCore core tier htier hne hK hret).bs,
      (cfg.r₁ : ENNReal) ^ 2 *
          maxDensity ((tierCore core tier htier hne hK hret).segs B)
            (fun p ↦ ((tierCore core tier htier hne hK hret).Y p).toConvexSpaceBody) ≤
        (Cdil : ENNReal) * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) := by
  intro B hB
  refine le_trans (mul_le_mul_of_nonneg_left ?_ zero_le) (hdil B hB)
  exact maxDensity_mono (fun p ↦ (core.Y p).toConvexSpaceBody) (htier B)

end Proj

end TierCore

section Markov

variable {cfg : VeryNotSticky.{u}}

open scoped Classical in
/-- **The Markov tier**: the segments of a ball whose shading is a `c₁ δ^{2η}` fraction of
their carrier — exactly the predicate of `Kakeya.VeryNotSticky.BallData.segs_density`
(GWZ `gwz.txt` l.2024–2028, l.2032). -/
noncomputable def markovTier (core : BallDataCore cfg) (c₁ : NNReal) (B : core.bι) :
    Finset core.σ :=
  (core.segs B).filter fun p =>
    (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
      volume (core.Y p).shade

theorem markovTier_subset (core : BallDataCore cfg) (c₁ : NNReal) (B : core.bι) :
    markovTier core c₁ B ⊆ core.segs B := by
  classical
  exact Finset.filter_subset _ _

open scoped Classical in
/-- The Markov tier satisfies `segs_density` by construction. -/
theorem markovTier_density (core : BallDataCore cfg) (c₁ : NNReal) (B : core.bι)
    {p : core.σ} (hp : p ∈ markovTier core c₁ B) :
    (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
      volume (core.Y p).shade := by
  classical
  exact (Finset.mem_filter.1 hp).2

open scoped Classical in
/-- **The mass lemma of the Markov tier**, at the retention factor `K = 2`. The input is the
per-ball fullness of the segment family at *twice* the Markov threshold — GWZ's
`λ(𝕋_B, Y_B) ⪆ δ^η` for the retained balls (`gwz.txt` l.2032). -/
theorem markovTier_retention (core : BallDataCore cfg) (c₁ : NNReal)
    (hfull : ∀ B ∈ core.bs,
      2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ∑ p ∈ core.segs B, volume (core.Y p).shade) :
    ∀ B ∈ core.bs, ((2 : NNReal) : ENNReal)⁻¹ * ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
      ∑ p ∈ markovTier core c₁ B, volume (core.Y p).shade := by
  classical
  intro B hB
  set c : ENNReal := (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) with hc
  set Pr : core.σ → Prop := fun p => c * volume (core.Y p).carrier ≤ volume (core.Y p).shade
    with hPr
  set S : ENNReal := ∑ p ∈ core.segs B, volume (core.Y p).shade with hS
  have hStop : S ≠ ⊤ := Kakeya.sum_volume_shade_ne_top (core.segs B) core.Y
  have hsplit :
      (∑ p ∈ (core.segs B).filter Pr, volume (core.Y p).shade) +
        (∑ p ∈ (core.segs B).filter (fun p => ¬ Pr p), volume (core.Y p).shade) = S :=
    Finset.sum_filter_add_sum_filter_not (core.segs B) Pr _
  -- the light segments carry at most `c · ∑ |carrier| ≤ S / 2`
  have hlight : (∑ p ∈ (core.segs B).filter (fun p => ¬ Pr p), volume (core.Y p).shade) ≤
      (2 : ENNReal)⁻¹ * S := by
    have h1 : (∑ p ∈ (core.segs B).filter (fun p => ¬ Pr p), volume (core.Y p).shade) ≤
        ∑ p ∈ (core.segs B).filter (fun p => ¬ Pr p), c * volume (core.Y p).carrier := by
      refine Finset.sum_le_sum fun p hp => ?_
      have := (Finset.mem_filter.1 hp).2
      exact le_of_lt (not_le.1 this)
    have h2 : (∑ p ∈ (core.segs B).filter (fun p => ¬ Pr p), c * volume (core.Y p).carrier) ≤
        ∑ p ∈ core.segs B, c * volume (core.Y p).carrier :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have h3 : (∑ p ∈ core.segs B, c * volume (core.Y p).carrier) =
        c * ∑ p ∈ core.segs B, volume (core.Y p).carrier := by
      rw [Finset.mul_sum]
    have h4 : c * ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤ (2 : ENNReal)⁻¹ * S := by
      have hfb := hfull B hB
      calc c * ∑ p ∈ core.segs B, volume (core.Y p).carrier
          = (2 : ENNReal)⁻¹ * (2 * c * ∑ p ∈ core.segs B, volume (core.Y p).carrier) := by
            rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
              one_mul]
        _ ≤ (2 : ENNReal)⁻¹ * S := mul_le_mul_of_nonneg_left hfb zero_le
    exact h1.trans (h2.trans (le_of_eq h3 |>.trans h4))
  -- so the tier carries at least `S / 2`
  have hhalf : (2 : ENNReal)⁻¹ * S + (2 : ENNReal)⁻¹ * S = S := by
    rw [← add_mul]
    rw [ENNReal.inv_two_add_inv_two, one_mul]
  have hfin : (2 : ENNReal)⁻¹ * S ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hStop
  have hkey : (2 : ENNReal)⁻¹ * S + (2 : ENNReal)⁻¹ * S ≤
      (∑ p ∈ (core.segs B).filter Pr, volume (core.Y p).shade) + (2 : ENNReal)⁻¹ * S :=
    calc (2 : ENNReal)⁻¹ * S + (2 : ENNReal)⁻¹ * S = S := hhalf
      _ = (∑ p ∈ (core.segs B).filter Pr, volume (core.Y p).shade) +
            (∑ p ∈ (core.segs B).filter (fun p => ¬ Pr p), volume (core.Y p).shade) :=
          hsplit.symm
      _ ≤ (∑ p ∈ (core.segs B).filter Pr, volume (core.Y p).shade) + (2 : ENNReal)⁻¹ * S :=
          add_le_add le_rfl hlight
  have hgoal : (2 : ENNReal)⁻¹ * S ≤
      ∑ p ∈ (core.segs B).filter Pr, volume (core.Y p).shade :=
    (ENNReal.add_le_add_iff_right hfin).1 hkey
  have hcoe : ((2 : NNReal) : ENNReal) = (2 : ENNReal) := by norm_num
  rw [hcoe]
  exact hgoal

open scoped Classical in
/-- **The Markov tier core**: `Cg` is multiplied by `Cm² · 2`. -/
noncomputable def markovTierCore (core : BallDataCore cfg) (c₁ : NNReal)
    (hne : ∀ B ∈ core.bs, (markovTier core c₁ B).Nonempty)
    (hfull : ∀ B ∈ core.bs,
      2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ∑ p ∈ core.segs B, volume (core.Y p).shade) :
    BallDataCore cfg :=
  tierCore core (markovTier core c₁) (markovTier_subset core c₁) hne
    (K := 2) (by norm_num) (markovTier_retention core c₁ hfull)

open scoped Classical in
@[simp] theorem markovTierCore_Cg (core : BallDataCore cfg) (c₁ : NNReal)
    (hne : ∀ B ∈ core.bs, (markovTier core c₁ B).Nonempty)
    (hfull : ∀ B ∈ core.bs,
      2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ∑ p ∈ core.segs B, volume (core.Y p).shade) :
    (markovTierCore core c₁ hne hfull).Cg = core.Cg * core.Cm ^ 2 * 2 := rfl

open scoped Classical in
/-- The Markov tier core satisfies the `segs_density` binder of
`Kakeya.VeryNotSticky.BallDataCore.toBallData`, at the same `c₁`. -/
theorem markovTierCore_segs_density (core : BallDataCore cfg) (c₁ : NNReal)
    (hne : ∀ B ∈ core.bs, (markovTier core c₁ B).Nonempty)
    (hfull : ∀ B ∈ core.bs,
      2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ∑ p ∈ core.segs B, volume (core.Y p).shade) :
    ∀ B ∈ (markovTierCore core c₁ hne hfull).bs,
      ∀ p ∈ (markovTierCore core c₁ hne hfull).segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
            volume ((markovTierCore core c₁ hne hfull).Y p).carrier ≤
          volume ((markovTierCore core c₁ hne hfull).Y p).shade := by
  classical
  intro B _ p hp
  exact markovTier_density core c₁ B hp

end Markov

section Dyadic

variable {cfg : VeryNotSticky.{u}}

open scoped Classical in
/-- **The pigeonhole behind a class tier.** If a finite family is classified by `cl` into at
most `N + 1` classes, one class carries a `(N + 1)⁻¹` fraction of the mass. -/
theorem exists_class_retaining {σ : Type*} (s : Finset σ) (f : σ → ENNReal) (cl : σ → ℕ)
    (N : ℕ) (hcl : ∀ p ∈ s, cl p ≤ N) :
    ∃ k, (((N + 1 : ℕ) : NNReal) : ENNReal)⁻¹ * ∑ p ∈ s, f p ≤
      ∑ p ∈ s.filter (fun p => cl p = k), f p := by
  classical
  have hmaps : ∀ p ∈ s, cl p ∈ Finset.range (N + 1) := fun p hp =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (hcl p hp))
  have hfib : ∑ k ∈ Finset.range (N + 1), ∑ p ∈ s.filter (fun p => cl p = k), f p =
      ∑ p ∈ s, f p := Finset.sum_fiberwise_of_maps_to hmaps f
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range (N + 1))
    (fun k => ∑ p ∈ s.filter (fun p => cl p = k), f p) ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
  refine ⟨k, ?_⟩
  have hle : ∑ p ∈ s, f p ≤
      ((N + 1 : ℕ) : ENNReal) * ∑ p ∈ s.filter (fun p => cl p = k), f p := by
    calc ∑ p ∈ s, f p = ∑ j ∈ Finset.range (N + 1), ∑ p ∈ s.filter (fun p => cl p = j), f p :=
          hfib.symm
      _ ≤ (Finset.range (N + 1)).card • ∑ p ∈ s.filter (fun p => cl p = k), f p :=
          Finset.sum_le_card_nsmul _ _ _ (fun j hj => hmax j hj)
      _ = ((N + 1 : ℕ) : ENNReal) * ∑ p ∈ s.filter (fun p => cl p = k), f p := by
          rw [Finset.card_range, nsmul_eq_mul]
  have hcoe : (((N + 1 : ℕ) : NNReal) : ENNReal) = ((N + 1 : ℕ) : ENNReal) := by
    push_cast; ring
  have hne : ((N + 1 : ℕ) : ENNReal) ≠ 0 := by positivity
  have htop : ((N + 1 : ℕ) : ENNReal) ≠ ⊤ := by simp
  rw [hcoe]
  calc ((N + 1 : ℕ) : ENNReal)⁻¹ * ∑ p ∈ s, f p
      ≤ ((N + 1 : ℕ) : ENNReal)⁻¹ *
          (((N + 1 : ℕ) : ENNReal) * ∑ p ∈ s.filter (fun p => cl p = k), f p) :=
        mul_le_mul_of_nonneg_left hle zero_le
    _ = ∑ p ∈ s.filter (fun p => cl p = k), f p := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne htop, one_mul]

/-- **The dyadic class of a segment's shade fraction**: the least `k` with
`|carrier| ≤ 2^k |shade|`. GWZ's second pigeonhole of `gwz.txt` l.2027–2028, in log-free
form. -/
noncomputable def shadeFractionClass (core : BallDataCore cfg) (p : core.σ) : ℕ :=
  sInf {k : ℕ | volume (core.Y p).carrier ≤ 2 ^ k * volume (core.Y p).shade}

theorem shadeFractionClass_le (core : BallDataCore cfg) {p : core.σ} {N : ℕ}
    (h : volume (core.Y p).carrier ≤ 2 ^ N * volume (core.Y p).shade) :
    shadeFractionClass core p ≤ N := Nat.sInf_le h

theorem volume_carrier_le_shadeFractionClass (core : BallDataCore cfg) {p : core.σ} {N : ℕ}
    (h : volume (core.Y p).carrier ≤ 2 ^ N * volume (core.Y p).shade) :
    volume (core.Y p).carrier ≤ 2 ^ shadeFractionClass core p * volume (core.Y p).shade :=
  Nat.sInf_mem (s := {k : ℕ | volume (core.Y p).carrier ≤ 2 ^ k * volume (core.Y p).shade})
    ⟨N, h⟩

/-- Minimality of the class: below it the inequality fails, so within one class the shade
fractions are comparable up to a factor `2`. -/
theorem not_volume_carrier_le_of_lt_shadeFractionClass (core : BallDataCore cfg)
    {p : core.σ} {k : ℕ} (h : k < shadeFractionClass core p) :
    ¬ volume (core.Y p).carrier ≤ 2 ^ k * volume (core.Y p).shade := fun hk =>
  absurd (Nat.sInf_le hk) (not_le.2 h)

/-- The Markov threshold bounds the dyadic class: if `c |carrier| ≤ |shade|` and
`1 ≤ 2^N c`, then the class is at most `N`. -/
theorem shadeFractionClass_le_of_markov (core : BallDataCore cfg) {p : core.σ} {c : ENNReal} {N : ℕ}
    (hc : c * volume (core.Y p).carrier ≤ volume (core.Y p).shade)
    (hN : (1 : ENNReal) ≤ 2 ^ N * c) : shadeFractionClass core p ≤ N := by
  refine shadeFractionClass_le core ?_
  calc volume (core.Y p).carrier = 1 * volume (core.Y p).carrier := (one_mul _).symm
    _ ≤ (2 ^ N * c) * volume (core.Y p).carrier :=
        mul_le_mul_of_nonneg_right hN zero_le
    _ = 2 ^ N * (c * volume (core.Y p).carrier) := by rw [mul_assoc]
    _ ≤ 2 ^ N * volume (core.Y p).shade := mul_le_mul_of_nonneg_left hc zero_le

/-- The explicit number of dyadic classes: `⌈log₂ (1/c)⌉₊`. -/
noncomputable def shadeFractionClassBound (c : NNReal) : ℕ := ⌈Real.logb 2 ((c : ℝ))⁻¹⌉₊

theorem one_le_two_pow_shadeFractionClassBound_mul {c : NNReal} (hc : 0 < c) :
    (1 : ENNReal) ≤ 2 ^ shadeFractionClassBound c * (c : ENNReal) := by
  have hcpos : (0 : ℝ) < (c : ℝ) := hc
  have hinvpos : (0 : ℝ) < ((c : ℝ))⁻¹ := inv_pos.2 hcpos
  have hle : ((c : ℝ))⁻¹ ≤ (2 : ℝ) ^ (shadeFractionClassBound c) := by
    have h1 : ((c : ℝ))⁻¹ = (2 : ℝ) ^ (Real.logb 2 ((c : ℝ))⁻¹) :=
      (Real.rpow_logb (by norm_num) (by norm_num) hinvpos).symm
    have h2 : (2 : ℝ) ^ (Real.logb 2 ((c : ℝ))⁻¹) ≤
        (2 : ℝ) ^ ((shadeFractionClassBound c : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    have h3 : (2 : ℝ) ^ ((shadeFractionClassBound c : ℕ) : ℝ) =
        (2 : ℝ) ^ (shadeFractionClassBound c) := Real.rpow_natCast 2 _
    rw [h1, ← h3]; exact h2
  have hreal : (1 : ℝ) ≤ (2 : ℝ) ^ (shadeFractionClassBound c) * (c : ℝ) := by
    have := mul_le_mul_of_nonneg_right hle (le_of_lt hcpos)
    rwa [inv_mul_cancel₀ (ne_of_gt hcpos)] at this
  have hnn : (1 : NNReal) ≤ 2 ^ shadeFractionClassBound c * c := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hreal
  calc (1 : ENNReal) = ((1 : NNReal) : ENNReal) := by norm_num
    _ ≤ ((2 ^ shadeFractionClassBound c * c : NNReal) : ENNReal) := ENNReal.coe_le_coe.2 hnn
    _ = 2 ^ shadeFractionClassBound c * (c : ENNReal) := by push_cast; ring

open scoped Classical in
/-- **The class tier**: the segments of a tier lying in one dyadic shade-fraction class,
chosen per ball. -/
noncomputable def classTier (core : BallDataCore cfg) (base : core.bι → Finset core.σ)
    (k : core.bι → ℕ) (B : core.bι) : Finset core.σ :=
  (base B).filter fun p => shadeFractionClass core p = k B

theorem classTier_subset (core : BallDataCore cfg) (base : core.bι → Finset core.σ)
    (k : core.bι → ℕ) (B : core.bι) : classTier core base k B ⊆ base B := by
  classical
  exact Finset.filter_subset _ _

open scoped Classical in
/-- Every two segments of a class tier of the same ball have the same dyadic class, hence
comparable shade fractions. -/
theorem classTier_shadeFractionClass_eq (core : BallDataCore cfg) (base : core.bι → Finset core.σ)
    (k : core.bι → ℕ) {B : core.bι} {p q : core.σ} (hp : p ∈ classTier core base k B)
    (hq : q ∈ classTier core base k B) : shadeFractionClass core p = shadeFractionClass core q := by
  classical
  rw [(Finset.mem_filter.1 hp).2, (Finset.mem_filter.1 hq).2]

open scoped Classical in
/-- **The mass lemma of the class tier**, at the retention factor `K = N + 1`. -/
theorem exists_classTier_retention (core : BallDataCore cfg) (base : core.bι → Finset core.σ)
    (N : ℕ) (hcl : ∀ B, ∀ p ∈ base B, shadeFractionClass core p ≤ N) :
    ∃ k : core.bι → ℕ, ∀ B,
      (((N + 1 : ℕ) : NNReal) : ENNReal)⁻¹ * ∑ p ∈ base B, volume (core.Y p).shade ≤
        ∑ p ∈ classTier core base k B, volume (core.Y p).shade := by
  classical
  choose k hk using fun B => exists_class_retaining (base B)
    (fun p => volume (core.Y p).shade) (shadeFractionClass core) N (hcl B)
  exact ⟨k, hk⟩

/-- A tier that retains mass in a ball whose segment shading is not null is non-empty: the
`hne` binder of `Kakeya.VeryNotSticky.tierCore` reduces to positivity. -/
theorem tier_nonempty_of_retention (core : BallDataCore cfg) (tier : core.bι → Finset core.σ)
    {K : NNReal} {B : core.bι}
    (hpos : 0 < ∑ p ∈ core.segs B, volume (core.Y p).shade)
    (hret : (K : ENNReal)⁻¹ * ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
      ∑ p ∈ tier B, volume (core.Y p).shade) : (tier B).Nonempty := by
  rcases Finset.eq_empty_or_nonempty (tier B) with hemp | hne
  · rw [hemp] at hret
    simp only [Finset.sum_empty, nonpos_iff_eq_zero, mul_eq_zero] at hret
    rcases hret with h0 | h0
    · exact absurd h0 (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)
    · exact absurd h0 (ne_of_gt hpos)
  · exact hne

end Dyadic

section Composite

variable {cfg : VeryNotSticky.{u}}

/-- The Markov threshold as one `NNReal`. -/
noncomputable def markovConst (cfg : VeryNotSticky.{u}) (c₁ : NNReal) : NNReal :=
  c₁ * cfg.δ ^ (2 * cfg.η)

theorem coe_markovConst (cfg : VeryNotSticky.{u}) (c₁ : NNReal) :
    ((markovConst cfg c₁ : NNReal) : ENNReal) =
      (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) := by
  rw [markovConst]
  push_cast
  rw [ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ)]

theorem markovConst_pos (cfg : VeryNotSticky.{u}) {c₁ : NNReal} (hc₁ : 0 < c₁) :
    0 < markovConst cfg c₁ :=
  mul_pos hc₁ (NNReal.rpow_pos cfg.hδ)

/-- The number of dyadic shade-fraction classes above the Markov threshold, plus the Markov
factor `2`: the **explicit** retention factor of the tier of GWZ §9.3 steps 5–6. -/
noncomputable def tierRetention (cfg : VeryNotSticky.{u}) (c₁ : NNReal) : NNReal :=
  2 * ((shadeFractionClassBound (markovConst cfg c₁) + 1 : ℕ) : NNReal)

theorem one_le_tierRetention (cfg : VeryNotSticky.{u}) (c₁ : NNReal) :
    1 ≤ tierRetention cfg c₁ := by
  rw [tierRetention, show ((shadeFractionClassBound (markovConst cfg c₁) + 1 : ℕ) : NNReal) =
      ((shadeFractionClassBound (markovConst cfg c₁) : ℕ) : NNReal) + 1 by push_cast; ring]
  calc (1 : NNReal) = 1 * 1 := by norm_num
    _ ≤ 2 * (((shadeFractionClassBound (markovConst cfg c₁) : ℕ) : NNReal) + 1) :=
        mul_le_mul' (by norm_num) le_add_self

open scoped Classical in
/-- **The tier of GWZ §9.3 steps 5–6, both pigeonholes at once**: the segments above the
`segs_density` (Markov) threshold, cut down to one dyadic shade-fraction class in every ball
(`gwz.txt` l.2024–2028). -/
noncomputable def markovDyadicTier (core : BallDataCore cfg) (c₁ : NNReal)
    (k : core.bι → ℕ) (B : core.bι) : Finset core.σ :=
  classTier core (markovTier core c₁) k B

theorem markovDyadicTier_subset (core : BallDataCore cfg) (c₁ : NNReal) (k : core.bι → ℕ)
    (B : core.bι) : markovDyadicTier core c₁ k B ⊆ core.segs B :=
  (classTier_subset core (markovTier core c₁) k B).trans (markovTier_subset core c₁ B)

open scoped Classical in
/-- The tier satisfies the `segs_density` binder of
`Kakeya.VeryNotSticky.BallDataCore.toBallData`, at the same `c₁`. -/
theorem markovDyadicTier_density (core : BallDataCore cfg) (c₁ : NNReal) (k : core.bι → ℕ)
    (B : core.bι) {p : core.σ} (hp : p ∈ markovDyadicTier core c₁ k B) :
    (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
      volume (core.Y p).shade :=
  markovTier_density core c₁ B (classTier_subset core (markovTier core c₁) k B hp)

open scoped Classical in
/-- Within a ball the tier's shade fractions all lie in one dyadic class. -/
theorem markovDyadicTier_shadeFractionClass_eq (core : BallDataCore cfg) (c₁ : NNReal)
    (k : core.bι → ℕ) {B : core.bι} {p q : core.σ}
    (hp : p ∈ markovDyadicTier core c₁ k B) (hq : q ∈ markovDyadicTier core c₁ k B) :
    shadeFractionClass core p = shadeFractionClass core q :=
  classTier_shadeFractionClass_eq core (markovTier core c₁) k hp hq

open scoped Classical in
/-- **The composed mass lemma**: the two pigeonholes retain a `(2 (N+1))⁻¹` fraction of the
segment shading mass in every ball, with `N = ⌈log₂ (1/(c₁ δ^{2η}))⌉₊`. -/
theorem exists_markovDyadicTier_retention (core : BallDataCore cfg) {c₁ : NNReal}
    (hc₁ : 0 < c₁)
    (hfull : ∀ B ∈ core.bs,
      2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ∑ p ∈ core.segs B, volume (core.Y p).shade) :
    ∃ k : core.bι → ℕ, ∀ B ∈ core.bs,
      ((tierRetention cfg c₁ : NNReal) : ENNReal)⁻¹ *
          ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
        ∑ p ∈ markovDyadicTier core c₁ k B, volume (core.Y p).shade := by
  classical
  set c : NNReal := markovConst cfg c₁ with hcdef
  have hcpos : 0 < c := markovConst_pos cfg hc₁
  have hcoe : ((c : NNReal) : ENNReal) = (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) :=
    coe_markovConst cfg c₁
  set N : ℕ := shadeFractionClassBound c with hNdef
  have hNc : (1 : ENNReal) ≤ 2 ^ N * (c : ENNReal) :=
    one_le_two_pow_shadeFractionClassBound_mul hcpos
  have hcl : ∀ B, ∀ p ∈ markovTier core c₁ B, shadeFractionClass core p ≤ N := by
    intro B p hp
    refine shadeFractionClass_le_of_markov core (c := (c : ENNReal)) ?_ hNc
    rw [hcoe]
    exact markovTier_density core c₁ B hp
  obtain ⟨k, hk⟩ := exists_classTier_retention core (markovTier core c₁) N hcl
  have hmk := markovTier_retention core c₁ hfull
  refine ⟨k, fun B hB => ?_⟩
  have hNne : (((N + 1 : ℕ) : NNReal) : ENNReal) ≠ 0 := by
    simp
  have hNtop : (((N + 1 : ℕ) : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h2ne : (((2 : NNReal)) : ENNReal) ≠ 0 := by simp
  have h2top : (((2 : NNReal)) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplit : ((tierRetention cfg c₁ : NNReal) : ENNReal)⁻¹ =
      (((N + 1 : ℕ) : NNReal) : ENNReal)⁻¹ * (((2 : NNReal)) : ENNReal)⁻¹ := by
    have : ((tierRetention cfg c₁ : NNReal) : ENNReal) =
        (((2 : NNReal)) : ENNReal) * (((N + 1 : ℕ) : NNReal) : ENNReal) := by
      rw [tierRetention]; push_cast; ring
    rw [this, ENNReal.mul_inv (Or.inl h2ne) (Or.inl h2top), mul_comm]
  rw [hsplit, mul_assoc]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ zero_le) (hk B)
  exact hmk B hB

open scoped Classical in
/-- **The tier core of GWZ §9.3 steps 5–6.** The loss of the working shading is the
**explicit** `Cg' = Cg · Cm² · 2 · (⌈log₂ (1/(c₁ δ^{2η}))⌉₊ + 1)`. -/
noncomputable def markovDyadicTierCore (core : BallDataCore cfg) (c₁ : NNReal)
    (k : core.bι → ℕ) (hne : ∀ B ∈ core.bs, (markovDyadicTier core c₁ k B).Nonempty)
    (hret : ∀ B ∈ core.bs,
      ((tierRetention cfg c₁ : NNReal) : ENNReal)⁻¹ *
          ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
        ∑ p ∈ markovDyadicTier core c₁ k B, volume (core.Y p).shade) :
    BallDataCore cfg :=
  tierCore core (markovDyadicTier core c₁ k) (markovDyadicTier_subset core c₁ k) hne
    (K := tierRetention cfg c₁) (one_le_tierRetention cfg c₁) hret

variable (core : BallDataCore cfg) (c₁ : NNReal) (k : core.bι → ℕ)
  (hne : ∀ B ∈ core.bs, (markovDyadicTier core c₁ k B).Nonempty)
  (hret : ∀ B ∈ core.bs,
    ((tierRetention cfg c₁ : NNReal) : ENNReal)⁻¹ *
        ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
      ∑ p ∈ markovDyadicTier core c₁ k B, volume (core.Y p).shade)

open scoped Classical in
@[simp] theorem markovDyadicTierCore_Cg :
    (markovDyadicTierCore core c₁ k hne hret).Cg =
      core.Cg * core.Cm ^ 2 * tierRetention cfg c₁ := rfl

open scoped Classical in
@[simp] theorem markovDyadicTierCore_segs :
    (markovDyadicTierCore core c₁ k hne hret).segs = markovDyadicTier core c₁ k := rfl

open scoped Classical in
@[simp] theorem markovDyadicTierCore_bs :
    (markovDyadicTierCore core c₁ k hne hret).bs = core.bs := rfl

open scoped Classical in
@[simp] theorem markovDyadicTierCore_Y :
    (markovDyadicTierCore core c₁ k hne hret).Y = core.Y := rfl

open scoped Classical in
/-- The tier core satisfies the `segs_density` binder of
`Kakeya.VeryNotSticky.BallDataCore.toBallData` at `c₁`, which no `BallDataCore` field
provides. -/
theorem markovDyadicTierCore_segs_density :
    ∀ B ∈ (markovDyadicTierCore core c₁ k hne hret).bs,
      ∀ p ∈ (markovDyadicTierCore core c₁ k hne hret).segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
            volume ((markovDyadicTierCore core c₁ k hne hret).Y p).carrier ≤
          volume ((markovDyadicTierCore core c₁ k hne hret).Y p).shade :=
  fun B _ _p hp => markovDyadicTier_density core c₁ k B hp

end Composite

end Kakeya.VeryNotSticky
