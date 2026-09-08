/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacProducer

/-!
# `0-E`: retention, and the mass-coupled fullness selection

 §SPEC rows 20 and 23.  Two clauses of the refined source's alternative `(F)` that
the tree has no analogue of, transcribed as named statements, plus the one consequence that makes
them worth having.

## Why these two and not a cardinality row

§SPEC.3(i): the object that must carry the non-degeneracy is the **coarse fibre the gain reads**,
and it must carry it **by retention**, not by a fresh cardinality row.  With retention the existing
count floor — `Kakeya.ML2Core.FloorHypothesisAt`'s final conjunct,
`SpineFloorShapeM1.lean:128-141`, exponent `2 + 4 · (spineRung β ϖ ε₁ gain dens (m+1) / 16)` —
bounds the fibre below **at the level pair it is already printed at, with no new constant**.
`Kakeya.ML2Core.countFloor_coarseFibre_of_retention` is that, in one line of proof.

Without retention, `Kakeya.ML2Core.coarseFibre_subset_nodesUnder` is the only relation between the
two sets and it points the wrong way.

## The family / shading / level-pair column

 §SPEC.1 makes this column part of the statement, because it is invisible to
`check`, `scan`, `axioms` and `guard` and has hidden four defects.  Every declaration below carries
it in its docstring.  In this file:

* `Kakeya.ML2Core.RetentionAt`, `Kakeya.ML2Core.RetentionProportionAt` —
  **family/shading:** the hierarchy `𝒰` on `(s, V)` and a retained level-`c` node set `t`;
  **level pair:** `(p, c)`, `p` the coarse level, `c` the fine level.
* `Kakeya.ML2Core.countFloor_coarseFibre_of_retention` (and the proportional twin) —
  **family/shading:** as above, with the floor read on `𝒰.nodesUnder c p jp`;
  **level pair:** `(p, c)` — the source's `(p, m')` with `m' ∈ 𝒲`, l.4074-4079.
* `Kakeya.ML2Core.MassCoupledFullnessSelectionAt` —
  **family/shading:** `(𝕌_b, Z_b)`, a subfamily of the level-`b` cells **under one retained
  `p`-cell**, with its induced shading;
  **level pair:** `(p, b)` — l.4486-4500.

**Not `(a, b)`.**  §SPEC.3(ii): there is no source clause at `(a, b)` that lower-bounds anything;
row 7 at `(a, b)` is an *upper* bound on `Δ_max`. Nothing in this file is stated at `(a, b)`, and
nothing here repairs `hfac`, whose seam is at `coarseNode 𝒞 a b`.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ## Scalar ledger -/

/-- **The `ε_d`-inset window range is non-empty at the spine constants: `spineDiv ϖ ε₁ < 1/2`.**

Asked by the floor hand's  leaf: `no_inset_level_of_succ` /
`hwinfloor_succ` have a non-empty range only if `ε_d < 1/2`, and if that failed the level clause
would be vacuous at **every** window.  It does not fail, with room to spare —
`ML2Spine.spineDiv_le_one` already gives `≤ 1/10`.

**Family/shading:** none, this is a scalar.  **Level pair:** none; it is a condition on the
window's inset exponent.

The same bound is what `Kakeya.ML2Core.not_singletonWindow_at_spine` uses for `ε_d ≤ 1/2`, so the
two scalar facts are the same one read twice. -/
theorem spineDiv_lt_half {ϖ ε₁ : ℝ} (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) :
    ML2Spine.spineDiv ϖ ε₁ < 1 / 2 := by
  have h := ML2Spine.spineDiv_le_one hϖ hε₁
  linarith

section Retention

variable {ι : Type*} {δ Cu : NNReal}

open Classical in
/-- **Retention, the source's "retain whole tagged thread cells"** (l.4443-4444).

Every level-`c` cell of the hierarchy lying under a level-`p` cell `jp` is retained by the seam's
level-`c` node set `t`, and retained *into `jp`'s own fibre*.

**Family/shading:** hierarchy `𝒰` on `(s, V)`; `t` the seam's retained level-`c` node set.
**Level pair:** `(p, c)`.

This is the clause  §SPEC row 20 records as having **no tree analogue**, in the
direction §SPEC.3(i) rules for. -/
def RetentionAt {s : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (p c : ℕ) (t : Finset ι) : Prop :=
  ∀ jp ∈ 𝒰.cover.indexSet p,
    𝒰.nodesUnder c p jp
      ⊆ ({j ∈ t | ML2Reduction.coarseNode 𝒰.cover.toChain p c j = jp} : Finset ι)

open Classical in
/-- **Retention in its `θ₀`-proportional form** (l.4497: "*retains a proportion
`θ₀ ≥ δ^{6η_c}` of the level-`b` cells in this `p`-cell*").

The weaker clause, and the one the source actually asserts at the point of use: the seam keeps a
`θ₀`-fraction of the cells rather than all of them.

**Family/shading** and **level pair**: as `Kakeya.ML2Core.RetentionAt`. -/
def RetentionProportionAt {s : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (p c : ℕ) (t : Finset ι) (θ₀ : NNReal) : Prop :=
  ∀ jp ∈ 𝒰.cover.indexSet p,
    (θ₀ : ℝ) * ((𝒰.nodesUnder c p jp).card : ℝ)
      ≤ ((({j ∈ t | ML2Reduction.coarseNode 𝒰.cover.toChain p c j = jp} : Finset ι)).card : ℝ)

open Classical in
/-- **The full form implies the proportional form at `θ₀ = 1`.** -/
theorem retentionProportionAt_of_retentionAt {s : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu}
    {p c : ℕ} {t : Finset ι} (h : RetentionAt 𝒰 p c t) :
    RetentionProportionAt 𝒰 p c t 1 := by
  intro jp hjp
  have := Finset.card_le_card (h jp hjp)
  rw [NNReal.coe_one, one_mul]
  exact_mod_cast this

open Classical in
/-- **`0-E`'s payoff: the existing count floor descends to the seam's fibre, with NO new constant.**

The exponent is `Kakeya.ML2Core.FloorHypothesisAt`'s, copied from `SpineFloorShapeM1.lean:140` and
not re-derived: `2 + 4 · (spineRung β ϖ ε₁ gain dens (m+1) / 16)`, the source's `2 + 4ζ` at
`ζ = τ/16` (l.4074-4079, `eq:ml2-count-floor` l.4476-4482).

**Family/shading:** hierarchy `𝒰` on `(s, V)`; the floor read on `𝒰.nodesUnder c p jp`, the
conclusion on the seam's fibre.  **Level pair:** `(p, c)` throughout — the statement never leaves
the pair the floor is printed at, which is the whole point  §SPEC.3(i). -/
theorem countFloor_coarseFibre_of_retention {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {m : ℕ}
    {s : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu}
    {p c : ℕ} {t : Finset ι} {jp : ι} (hjp : jp ∈ 𝒰.cover.indexSet p)
    (hret : RetentionAt 𝒰 p c t)
    (hfloor : ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
          ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
      ≤ ((𝒰.nodesUnder c p jp).card : ℝ)) :
    ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
          ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
      ≤ ((({j ∈ t | ML2Reduction.coarseNode 𝒰.cover.toChain p c j = jp} : Finset ι)).card : ℝ) := by
  refine hfloor.trans ?_
  exact_mod_cast Finset.card_le_card (hret jp hjp)

open Classical in
/-- **The proportional twin**, at the source's own `θ₀` (l.4497).  Same exponent, same level pair;
the only difference is the `θ₀` the selection retains. -/
theorem countFloor_coarseFibre_of_retentionProportion {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {m : ℕ}
    {s : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu}
    {p c : ℕ} {t : Finset ι} {θ₀ : NNReal} {jp : ι} (hjp : jp ∈ 𝒰.cover.indexSet p)
    (hret : RetentionProportionAt 𝒰 p c t θ₀)
    (hfloor : ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
          ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
      ≤ ((𝒰.nodesUnder c p jp).card : ℝ)) :
    (θ₀ : ℝ) * ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
          ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
      ≤ ((({j ∈ t | ML2Reduction.coarseNode 𝒰.cover.toChain p c j = jp} : Finset ι)).card : ℝ) := by
  refine le_trans ?_ (hret jp hjp)
  exact mul_le_mul_of_nonneg_left hfloor (NNReal.coe_nonneg θ₀)

open Classical in
/-- **The singleton collapse is blocked by retention** — the  bar, met at the
object §SPEC.3(i) names and at the level pair §SPEC.3(ii) names.

Once the ratio's power reaches `2` — which is what `𝒲`'s two rows are for — the fibre has at least
two members and `Kakeya.ML2Core.middle_gain_nonpos_of_card_le_one`'s hypothesis is false.

**Family/shading** and **level pair**: as `Kakeya.ML2Core.countFloor_coarseFibre_of_retention`.
Note the level pair is `(p, c)`, **not** `(a, b)`: this does *not* repair `hfac`, whose seam is at
`coarseNode 𝒞 a b`.  That is `0-D`. -/
theorem not_coarseFibre_card_le_one_of_retention {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {m : ℕ}
    {s : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu}
    {p c : ℕ} {t : Finset ι} {jp : ι} (hjp : jp ∈ 𝒰.cover.indexSet p)
    (hret : RetentionAt 𝒰 p c t)
    (hfloor : ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
          ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
      ≤ ((𝒰.nodesUnder c p jp).card : ℝ))
    (hbig : (2 : ℝ) ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
          ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))) :
    ¬ (({j ∈ t | ML2Reduction.coarseNode 𝒰.cover.toChain p c j = jp} : Finset ι)).card ≤ 1 := by
  intro hcon
  have h2 := hbig.trans (countFloor_coarseFibre_of_retention hjp hret hfloor)
  have hle : ((({j ∈ t | ML2Reduction.coarseNode 𝒰.cover.toChain p c j = jp} :
      Finset ι)).card : ℝ) ≤ 1 := by exact_mod_cast hcon
  linarith

open Classical in
/-- **Non-vacuity of `Kakeya.ML2Core.RetentionAt`, and the nuance it exposes.**

The one-tube hierarchy satisfies retention at every level pair: its index sets are singletons and
its assignment is constant, so every level-`c` cell under a level-`p` cell is retained into that
cell's fibre.  So retention is satisfiable, and it is **not** by itself a non-degeneracy condition
— on this very model the fibre has one member.

What excludes the singleton is retention **together with** the existing count floor **and**
`2 ≤ (ρ_p/ρ_c)^{2+4ζ}`, which is what `𝒲`'s two rows are for
(`Kakeya.ML2Core.not_coarseFibre_card_le_one_of_retention`); on the one-tube model the floor forces
that power below `1`, so the hypothesis fails and there is no contradiction.  Recorded because
"retention kills the singleton" would be the fourth version of the same mistake.

**Family/shading:** the constant hierarchy on `({i₀}, V)`.  **Level pair:** any `(p, c)`. -/
theorem retentionAt_singleton {ι : Type*} (i₀ : ι) {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (p c : ℕ) :
    RetentionAt (singletonUniform i₀ hδ0 hδ1 (Tube.ssfGridLen δ) (fun i ↦ (V i).toTube)) p c
      ({i₀} : Finset ι) := by
  classical
  intro jp hjp j hj
  have hjp0 : jp = i₀ := Finset.mem_singleton.mp hjp
  have hj0 : j = i₀ := Finset.mem_singleton.mp (Finset.filter_subset _ _ hj)
  subst hjp0; subst hj0
  refine Finset.mem_filter.mpr ⟨Finset.mem_singleton_self j, ?_⟩
  simp only [ML2Reduction.coarseNode]
  split
  · rfl
  · rfl

end Retention

section MassCoupled

variable {ι : Type*} {δ Cu : NNReal}

open Classical in
/-- **Mass-coupled fullness selection** (source lines 4486-4500).

Fix a retained `p`-cell `Sp`. The selection returns a nonempty family
`𝕌_b ⊆ 𝕊''_b⟨S_p^*⟩` with shading `Z_b` such that

* `λ(𝕌_b, Z_b) ≥ δ^{5η_c}`;
* `Δ_max(𝕌_b) ≤ t^{-η_J}`;
* it retains a proportion `θ₀ ≥ δ^{6η_c}` of the level-`b` cells in this `p`-cell.

The family consists of level-`b` cells under one retained `p`-cell. The pair
`(p, b)` is the source's middle-factor pair, with `δ̃ = ρ_b/(2ρ_p)` (line 4506).

Tube equality `(Zb j).toTube = 𝒰.cover.tube b j` specifies the carriers: the
source induces shading from fibre masses, while this tree interface leaves the
shading to the selection. The auxiliary scale `t` in the density bound remains
a parameter; it is not identified with `δ` or a grid scale. The last conjunct
is `Kakeya.ML2Core.RetentionProportionAt` applied to `𝕌_b`. -/
def MassCoupledFullnessSelectionAt (ηc ηJ : ℝ) (tAux θ₀ : NNReal) {s : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (p b : ℕ) : Prop :=
  ∀ Sp ∈ 𝒰.cover.indexSet p,
    ∃ (Ub : Finset ι)
      (Zb : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
        (EuclideanSpace ℝ (Fin 3))),
      Ub.Nonempty ∧
      Ub ⊆ 𝒰.nodesUnder b p Sp ∧
      (∀ j, (Zb j).toTube = 𝒰.cover.tube b j) ∧
      (δ : NNReal) ^ (5 * ηc) ≤ ShadedBody.fullness Ub (fun j ↦ (Zb j).toShadedBody) ∧
      Kakeya.maxDensity Ub (fun j ↦ (Zb j).toConvexSpaceBody) ≤ (tAux : ENNReal) ^ (-ηJ) ∧
      (δ : NNReal) ^ (6 * ηc) ≤ θ₀ ∧
      (θ₀ : ℝ) * ((𝒰.nodesUnder b p Sp).card : ℝ) ≤ (Ub.card : ℝ)

open Classical in
/-- **The selection's output is nonempty and lives under one `p`-cell at level `b`.**

The only consequence available without the construction: a record that the shape is the
one a level-`b` consumer reads, and that the `p`-cell is the index.  Anything stronger needs the
pigeonholing itself, which is what `0-E`'s open half is. -/
theorem exists_nonempty_of_massCoupledFullnessSelection {ηc ηJ : ℝ} {tAux θ₀ : NNReal}
    {s : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu} {p b : ℕ}
    (h : MassCoupledFullnessSelectionAt ηc ηJ tAux θ₀ 𝒰 p b)
    {Sp : ι} (hSp : Sp ∈ 𝒰.cover.indexSet p) :
    ∃ Ub : Finset ι, Ub.Nonempty ∧ Ub ⊆ 𝒰.nodesUnder b p Sp := by
  obtain ⟨Ub, Zb, hne, hsub, _, _, _, _, _⟩ := h Sp hSp
  exact ⟨Ub, hne, hsub⟩

end MassCoupled

end Kakeya.ML2Core

end
