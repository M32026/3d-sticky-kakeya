/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinSetup
public import Kakeya.DimensionThree.MainLemma2.ThinEstimates
public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle
public import Kakeya.DimensionThree.MainLemma2.PlankConstants

/-!
# The configurations of Main Lemma 2, relative to `Kakeya.VeryNotSticky`

The Lean structure `Kakeya.VeryNotSticky` records only the *global* data of Configuration
`hyp:ml2setup`, i.e. (C1) together with the biased factoring and the distinguished pair of
working scales `a ≤ b`. It carries none of the per-ball data (C2)–(C5): the covering family
`𝔅`, the subordinate partition `(B̂)`, the tube segments `𝕋_B` with their shading `Y_B` and
parent families `𝕋(T_B)`, or the per-ball factorings `𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}`.

Every branch lemma of the thin case speaks about that per-ball data, and about the thin-case
refinement `hyp:ml2thinsetup` built on top of it. Passing those pieces as free arguments makes
the branch lemmas unsound as case-split components: nothing then ties the family of factoring
bodies to `cfg`, so instantiating it by `∅` satisfies the multiplicity hypotheses vacuously.
This file fixes that by bundling the data *relative to a fixed `cfg`*, in two layers:

* `Kakeya.VeryNotSticky.BallData` renders the per-ball part of Configuration `hyp:ml2setup`,
  i.e. (C2)–(C5), for a fixed `cfg`. All the scales it mentions are read off `cfg`: the ball
  radius is `Kakeya.VeryNotSticky.r₁ cfg = δ^{exscal}`, the tube thickness is `cfg.δ`, the
  body dimensions are `cfg.a`, `cfg.b`, and the density exponent of (C5) is `2 · cfg.η`.
* `Kakeya.VeryNotSticky.ThinConfig` renders Configuration `hyp:ml2thinsetup` over a given
  `BallData`: the global refined shading `Y'` on `𝕋`, and for each ball `B ∈ 𝔅` a
  `Kakeya.ThinCase.ThinBall` — the per-ball payload (T1)–(T6), which is *not* duplicated here
  — with one and the same comparison constant `C` for every ball, together with the two
  compatibility containments of (T1) relating `Y'` to the per-ball `Y'_B`.
* `Kakeya.VeryNotSticky.CaseScale` packages the fixed-scale thresholds needed by the
  non-slab leaves after the exponent parameters and `BallData` have been fixed, together with
  the by-choice thresholds bundled as `Kakeya.VeryNotSticky.ScaleThresholds`.

The split into two structures follows the blueprint: `hyp:ml2thinsetup` is stated as *extra
data attached to the same pair* `(𝕋, Y)` realizing `hyp:ml2setup`, not as an extra hypothesis
on it, so the two layers are separate objects and the second one is parameterized by the
first. The fields of `ThinConfig` are exactly the data and the conclusion of
`Kakeya.ThinCase.thinSetupExists`, and the fields of `BallData` are exactly its (C2)–(C5)
hypotheses; `Kakeya.VeryNotSticky.exists_thinConfig` is the `cfg`-relative form of blueprint
`lem:ml2thinsetupexists` and is intended to be deduced from `thinSetupExists`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

open scoped Classical in
/-- **The per-ball data of Configuration `hyp:ml2setup`, relative to `cfg`** (blueprint
`hyp:ml2setup`, items (C2)–(C5)).

`cfg : Kakeya.VeryNotSticky` already carries (C1) and the global factoring data of (C4) —
the working scales `a ≤ b` and the distinguished part `W` — but none of the per-ball
structure. `BallData cfg` supplies it, with every scale tied to `cfg`:

* (C2) the index type `bι` of the non-empty family `𝔅` of `r₁`-balls, with `r₁ = cfg.r₁`,
  their centres `ctr`, the subordinate partition `P B = B̂ ⊆ B` and the bounded-overlap
  bound `D`; the pieces are pairwise disjoint, measurable, and cover every `Y_g(T)`.
* (C3) the tube segments `segs B = 𝕋_B` with shading `Y = Y_B` supported in `B̂`, the parent
  families `fam p = 𝕋(T_B) ⊆ 𝕋`, pairwise disjoint, and the affine thicknesses
  `∼ (r₁, δ, δ)` of the segments.
* (C4) the bodies `bodies B = 𝕎_B` with `Wb` the body and `blk` the block map, of affine
  thicknesses `∼ (r₁, b, a)` with the *same* constant `C₀` for every ball, contained in the
  ball `B` and pairwise essentially distinct (being blocks of a factoring), together with
  the common shortest dimension `w₁ ≈ τ₂(W)` and the Frostman constant `CF` of each block
  in its body, and the biased density comparison `biasedDensity` of blueprint equation
  `factmaxmodbias` with its constant `Cbias`, which is what the factoring at bias `cfg.ϱ`
  yields inside each body.
* (C5) the per-segment density bound with constant `c₁`, the two-way compatibility of
  `Y_B` with `Y_g`, and the fibre count `|𝕋(T_B)_{Y_g}(x)| ≈ m` on `Y_B(T_B)` with comparison
  constant `Cm`.
* (C5′) the *working shading* `Yg = Y_g ⊆ Y` on which (C5) and the covering half of (C2) are
  read: GWZ's `Y` after the per-tube refinements of §9.3 steps
  6–8, which they carry "by abuse of notation" (`gwz.txt` l.2024-2041); it is a `⪆ 1`
  refinement of the uniform shading of `cfg`, with loss `Cg` (`Yg_mass`). The text of this
  block is pinned by `Kakeya.VeryNotSticky.statement_of_universal_ballData_workingShading`.

The last group of fields is the family of `δ`-ball covers `𝒞(T_B)` of Configuration
`hyp:ml2thinsetup`, which the blueprint fixes before the thin-case construction begins; it is
carried here because it is an input to `Kakeya.ThinCase.thinSetupExists`, not an output.

The bounded overlap of the balls of `𝔅` is stated in the subfamily form
`ballOverlap`: any subfamily of `𝔅` all of whose balls contain a common point has at most
`D` members. This is equivalent to the `Finset.filter` form of
`Kakeya.IsBoundedlyOverlappingCover.card_filter_le` and avoids a decidability instance in
the statement. The covering half of (C2) is `P_cover`, stated for the working shading `Y_g`,
which is the form (C2) singles out as not following from the covering of `U(𝕋_{r₁}, Y)`. -/
structure BallData (cfg : VeryNotSticky.{u}) where
  /-- The thickness comparison constant of (C3) and (C4). -/
  C₀ : NNReal
  /-- `1 ≤ C₀`. -/
  hC₀ : 1 ≤ C₀
  /-- The Frostman constant of the blocks of the factoring of (C4). -/
  CF : NNReal
  /-- `1 ≤ CF`. -/
  hCF : 1 ≤ CF
  /-- The comparison constant of the dilation clause `segs_dilation` of (C3). It is a free field, like `C₀` and `CF`: `BallData` bounds it from above
  nowhere, and it is spent exactly once, in `Kakeya.VeryNotSticky.SlabScale.final`, where the
  `δ`-free constants of the slab case are absorbed against `δ^{β/2}`. The coarse producers
  (`Kakeya.VeryNotSticky.nonempty_ballData_deleteShade`) supply `Cdil = 1`; the honest capsules
  of `Kakeya.VeryNotSticky.exists_segments` need a dimensional constant. -/
  Cdil : NNReal
  /-- `1 ≤ Cdil`. -/
  hCdil : 1 ≤ Cdil
  /-- **Constant in Lemma `lemmafactmaxbias`** (blueprint `def:factmaxbiasConstant`,
  `C_{lemmafactmaxbias}`): the comparison constant of the per-ball biased density comparison
  `Kakeya.VeryNotSticky.BallData.biasedDensity` of (C4), i.e. of blueprint equation
  `factmaxmodbias`. It is the constant `C` common to the two displayed estimates of the maximal
  density factoring lemma for the factoring it produces at bias `cfg.ϱ`: `factmaxmod1`, the
  biased density comparison that `biasedDensity` records, and `factmaxmod2` = GWZ (83), the
  anti-clustering `Δ_max(𝕎_B) ≤ C (|W|/|B|)^{-ϱ}` at `U = B`, which `bodies_antiClustering`
  records as `Cbias δ^{-2ϱ}` after the volume estimate `|W|/|B| ≳ δ²`. `C` depends only on the ambient dimension
  and the bias exponent (blueprint `def:factmaxbiasConstant`, Lean
  `ConvexSpaceBody.nonempty_biasedFactorization.C`) — not on `cfg.δ`, not on the cardinality of
  the family, and on nothing attached to a single ball: one and the same value serves every
  `B ∈ 𝔅`, every body `W ∈ 𝕎_B` and every comparison body `K ⊆ W`. It is kept separate from
  the thickness constant `C₀`, which measures a different quantity. -/
  Cbias : NNReal
  /-- `1 ≤ Cbias`. -/
  hCbias : 1 ≤ Cbias
  /-- The per-segment density constant of (C5). -/
  c₁ : NNReal
  /-- `0 < c₁`. Without it the density bound `segs_density` is vacuous, the shading `Y` may be
  everywhere empty, and the `Kakeya.ThinCase.ThinBall` demanded by
  `Kakeya.VeryNotSticky.ThinConfig` — whose fields `S_nonempty` and `denseBall` together force
  a `δ`-ball of positive shaded measure — cannot exist. -/
  hc₁ : 0 < c₁
  /-- The bounded-overlap constant of the ball cover of (C2) and of the `δ`-ball covers. -/
  D : ℕ
  /-- (C5′) the *working shading* `Y_g ⊆ Y` of GWZ §9.3: `Y` after the per-tube refinements of
  steps 6–8 (`gwz.txt` l.2024-2041, "abusing notation, we will continue to refer to this as
  `(𝕋, Y)`"), kept apart from the uniform shading of `cfg`, which is Lemma 9.1's hypothesis
  (l.1778) and is never re-established after those steps. The coarse producers take
  `Yg := (cfg.T i).shade`, `Cg := 1`. -/
  Yg : cfg.ι → Set (EuclideanSpace ℝ (Fin 3))
  /-- (C5′) `Y_g(T) ⊆ Y(T)`. -/
  Yg_subset : ∀ i ∈ cfg.s, Yg i ⊆ (cfg.T i).shade
  /-- (C5′) `Y_g` is measurable. -/
  Yg_measurable : ∀ i ∈ cfg.s, MeasurableSet (Yg i)
  /-- (C5′) the loss of the working shading against `Y`; polylogarithmic (heavy balls, Markov
  tier, Lemma 9.2's subset, the dims class), never a power of `δ`. -/
  Cg : NNReal
  /-- `1 ≤ Cg`. -/
  hCg : 1 ≤ Cg
  /-- (C5′) `(𝕋, Y_g)` is a `⪆ 1` refinement of `(𝕋, Y)` (`gwz.txt` l.2028, 2030, 2036-2038). -/
  Yg_mass : (Cg : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
    ∑ i ∈ cfg.s, volume (Yg i)
  /-- The index type of the family `𝔅` of `r₁`-balls of (C2). -/
  bι : Type u
  /-- The index type of the tube segments `𝕋_B` of (C3). -/
  σ : Type u
  /-- The index type of the factoring bodies `𝕎_B` of (C4). -/
  ω : Type u
  /-- Decidable equality on the body index type, needed to form the blocks `𝕋_{B,W}`. -/
  [decidableEqω : DecidableEq ω]
  /-- (C2) the non-empty family `𝔅` of `r₁`-balls. -/
  bs : Finset bι
  /-- (C2) `𝔅` is non-empty. -/
  bs_nonempty : bs.Nonempty
  /-- (C2) the centre of the ball `B`. -/
  ctr : bι → EuclideanSpace ℝ (Fin 3)
  /-- (C2) the piece `B̂` of the partition subordinate to `𝔅`. -/
  P : bι → Set (EuclideanSpace ℝ (Fin 3))
  /-- (C2) `B̂ ⊆ B`, the ball of radius `r₁ = δ^{exscal}` centred at `ctr B`. -/
  P_subset_ball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ)
  /-- (C2) the pieces `B̂` are pairwise disjoint. -/
  P_disjoint : (bs : Set bι).PairwiseDisjoint P
  /-- (C2) the pieces `B̂` are measurable. -/
  P_measurable : ∀ B ∈ bs, MeasurableSet (P B)
  /-- (C2) the pieces cover the *working* shading: `Y_g(T) ⊆ ⋃_{B ∈ 𝔅} B̂` for every `T ∈ 𝕋`.
  Read on `Y_g` rather than on `Y`: `bs` is GWZ's `𝔅`, the heavy
  balls of the winning class, and the shading outside their pieces has been deleted from
  `Y_g` (`gwz.txt` l.2029-2030); the uniform shading `Y` need not be covered. -/
  P_cover : ∀ i ∈ cfg.s, Yg i ⊆ ⋃ B ∈ bs, P B
  /-- (C2) the balls of `𝔅` are `D`-boundedly overlapping: no point lies in more than `D`
  of them. -/
  ballOverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
    (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ D
  /-- (C3) the family `𝕋_B` of tube segments in the ball `B`. -/
  segs : bι → Finset σ
  /-- (C3) the shading `Y_B` on the tube segments. -/
  Y : σ → ShadedBody (EuclideanSpace ℝ (Fin 3))
  /-- (C3) the family `𝕋(T_B) ⊆ 𝕋` of parent tubes of a segment. -/
  fam : σ → Finset cfg.ι
  /-- (C5) each `𝕋_B` is non-empty. -/
  segs_nonempty : ∀ B ∈ bs, (segs B).Nonempty
  /-- (C3) the parent families are subfamilies of `𝕋`. -/
  fam_subset : ∀ B ∈ bs, ∀ p ∈ segs B, fam p ⊆ cfg.s
  /-- (C3) the parent families are pairwise disjoint, so a tube has a unique parent
  segment in each ball. -/
  fam_disjoint : ∀ B ∈ bs, (segs B : Set σ).Pairwise fun p q => Disjoint (fam p) (fam q)
  /-- (C3) the shading `Y_B` is supported in the piece `B̂`. -/
  Y_piece : ∀ B ∈ bs, ∀ p ∈ segs B, (Y p).shade ⊆ P B
  /-- (C3) the segments have affine thicknesses `∼ (r₁, δ, δ)`. -/
  segs_thickness : ∀ B ∈ bs, ∀ p ∈ segs B,
    HasThicknesses (Y p).carrier C₀ ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]
  /-- (C3) the segments of a ball have *comparable* affine thicknesses, in the exact form
  `ShadedBody.factoringAndMultPropCombined` demands. It is not a consequence of
  `segs_thickness`, which only compares the thicknesses up to the constant `C₀ ^ 2`. -/
  segs_dims : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ q ∈ segs B,
    Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier
  /-- (C3) the segment families are comparable to `𝕋` in maximal density, up to the
  comparison constant `Cdil`: `r₁² Δ_max(𝕋_B) ≤ Cdil · Δ_max(𝕋)` for every `B ∈ 𝔅`, the
  division-free form of `Δ_max(𝕋_B) ≤ Cdil · r₁^{-2} Δ_max(𝕋)`, so that no positivity or
  finiteness side condition is needed in `[0, ∞]`.

  The content is a dilation comparison between the two families this item creates. A segment
  `T_B ⊆ K` is `T ∩ B` for a parent tube `T`, unique by `fam_disjoint`, and has length `∼ r₁`
  along the axis of `T` while `T` has length `1`; so `T` lies in the `r₁^{-1}`-dilate of `K`,
  of volume `r₁^{-3}|K|`, and `|T_B| ∼ r₁|T|` recovers one power of `r₁`. GWZ (`gwz.txt`
  l.2210-2212) write the comparison at constant `1` for the exact intersections `T ∩ B`, under
  the convention of their §2.2 (l.150-160) that comparisons of convex sets hold up to
  constants; the segments of this development are only `C₀`-comparable capsules
  (`segs_thickness`), for which the honest dilation bound carries a dimensional constant
  (`Kakeya.VeryNotSticky.segs_dilation_of_maxDensity_le` and its docstring). The constant is
  therefore made explicit as the field `Cdil` instead of being
  asserted away: the previous constant-`1` form was the over-strong rendering of a `⪅`.

  It is recorded as data rather than derived because both inputs of that computation are
  comparisons only in the development, and the companion of the maximal-density homothety
  comparison for a family of segments in terms of the family of their parents is not
  available. The sole consumer is `Kakeya.VeryNotSticky.slabDensity`, which now carries
  `Cdil`; the constant is discharged, together with the other `δ`-free constants of the slab
  case, in `Kakeya.VeryNotSticky.SlabScale.final`. -/
  segs_dilation : ∀ B ∈ bs,
    (cfg.r₁ : ENNReal) ^ 2 * maxDensity (segs B) (fun p ↦ (Y p).toConvexSpaceBody) ≤
      (Cdil : ENNReal) * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)
  /-- (C4) the family `𝕎_B` of factoring bodies in the ball `B`. -/
  bodies : bι → Finset ω
  /-- (C4) the body `W` attached to an index. -/
  Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- (C4) the block map of the factoring `𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}`. -/
  blk : σ → ω
  /-- (C4) the common shortest dimension `w₁ ≈ τ₂(W)` of the bodies. -/
  w₁ : NNReal
  /-- (C4) each segment belongs to a block of the ball it lies in. -/
  blk_mem : ∀ B ∈ bs, ∀ p ∈ segs B, blk p ∈ bodies B
  /-- (C4) each segment is contained in the body of its block. -/
  segs_le : ∀ B ∈ bs, ∀ p ∈ segs B, (Y p).toConvexSpaceBody ≤ Wb (blk p)
  /-- (C4) the bodies have affine thicknesses `∼ (r₁, b, a)`, with the working scales `a`,
  `b` of `cfg`, and with one constant `C₀` for all balls. -/
  bodies_thickness : ∀ B ∈ bs, ∀ j ∈ bodies B,
    HasThicknesses (Wb j).carrier C₀ ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)]
  /-- (C4) the bodies of `𝕎_B` lie in the ball `B`. -/
  bodies_subset_ball : ∀ B ∈ bs, ∀ j ∈ bodies B,
    (Wb j).carrier ⊆ closedBall (ctr B) (cfg.r₁ : ℝ)
  /-- (C4) the shortest dimension of every body is comparable to the common value `w₁`. -/
  bodies_w₁ : ∀ B ∈ bs, ∀ j ∈ bodies B,
    Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) ≤
        2 * w₁ ∧
      (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j).carrier
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)
  /-- (C4) each block is `CF`-Frostman in its body. -/
  frostman : ∀ B ∈ bs, ∀ j ∈ bodies B,
    ConvexSpaceBody.IsFrostmanIn ((segs B).filter fun p => blk p = j)
      (fun p => (Y p).toConvexSpaceBody) (Wb j) CF
  /-- (C4) the *biased* density comparison inside a factoring body (blueprint equation
  `factmaxmodbias`): for every ball `B ∈ 𝔅`, every body `W ∈ 𝕎_B` and every convex body
  `K ≤ W`,
  `Δ(𝕋_{B,W}, K) ≤ C_{lemmafactmaxbias} (|K|/|W|)^ϱ Δ(𝕋_{B,W}, W)`,
  which is the blueprint's `Δ(𝕋_{B,W}, W)/Δ(𝕋_{B,W}, K) ⪆ (|W|/|K|)^ϱ` cleared of division.

  This is the per-ball instance of `factmaxmod1`, i.e. of the field
  `ConvexSpaceBody.BiasedFactorization.densityIn_le_biased`, for the factoring
  `𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}` of (C4). The configuration carries no global factoring of `𝕋`; it is the output of the maximal density factoring lemma
  applied per ball with bias `cfg.ϱ`, and therefore data of (C4) rather than a hypothesis of
  any single case.

  The product form is deliberate: it is division-free, so no positivity or finiteness side
  condition is needed, and its right-hand side is a monotone product, so `gcongr` can rewrite
  under it. -/
  biasedDensity : ∀ B ∈ bs, ∀ j ∈ bodies B,
    ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ Wb j →
      densityIn ((segs B).filter fun p => blk p = j) (fun p => (Y p).toConvexSpaceBody) K ≤
        (Cbias : ENNReal) *
          (volume K.carrier / volume (Wb j).carrier) ^ cfg.ϱ *
          densityIn ((segs B).filter fun p => blk p = j)
            (fun p => (Y p).toConvexSpaceBody) (Wb j)
  /-- (C4) the outer family of the per-ball factoring is anti-clustered:
  `Δ_max(𝕎_B) ≤ C_bias δ^{-2ϱ}` for every `B ∈ 𝔅`, with the same constant `Cbias` as
  `biasedDensity`.

  This is the second displayed estimate of the maximal density factoring lemma, applied to the
  per-ball factoring of this item with reference body `U = B`, followed by the volume estimate
  `|W|/|B| ∼ ab/r₁² ≥ δ^{2-2 exscal} ≥ δ²` that the thicknesses of this item supply; the two
  comparison constants are absorbed into `Cbias`, which is why no constant of its own appears.
  Like `biasedDensity` it is per-ball data of (C4): the configuration carries no global
  factoring of `𝕋`, so nothing above the ball supplies it.

  The exponent is deliberately the honest `2ϱ` rather than the weakened `exscal`: the
  conversion `2ϱ ≤ exscal` costs the budget `Kakeya.VeryNotSticky.CaseParams.slabBias`
  together with a threshold on `δ`, and both are spent later, in
  `Kakeya.VeryNotSticky.SlabScale`, where the constants can be discharged at the same time.
  The bound passes to subfamilies, since each competing convex body sees a smaller sum; this is
  how `Kakeya.VeryNotSticky.slabBodiesAntiClustering` applies it to the retained family
  `𝕎'_B`. -/
  bodies_antiClustering : ∀ B ∈ bs,
    maxDensity (bodies B) Wb ≤ (Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ))
  /-- (C5) the per-segment density bound `|Y_B(T_B)| ≥ c₁ δ^{2η} |T_B|` — GWZ `gwz.txt`
  l.2032 `λ(𝕋_B, Y_B) ⪆ δ^η`, rendered as the tree renders every `⪆ δ^η` on this path
  (`Kakeya.VeryNotSticky.fullness_ge`, `Kakeya.VeryNotSticky.lam_ge`, T1's floor): `δ^{2η}`
  with a `δ`-free constant `c₁` (pinned by
  `Kakeya.VeryNotSticky.statement_of_universal_ballData_C5_density`). -/
  segs_density : ∀ B ∈ bs, ∀ p ∈ segs B,
    (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (Y p).carrier ≤
      volume (Y p).shade
  /-- (C5) a tube whose working shading `Y_g(T)` meets `B̂` has a parent segment in `B`
  ( `segs B` is GWZ's post-step-6 `𝕋_B`, the light segments being
  simply absent, their `Y_g(T) ∩ B̂` deleted). -/
  parent : ∀ B ∈ bs, ∀ i ∈ cfg.s, (Yg i ∩ P B).Nonempty → ∃ p ∈ segs B, i ∈ fam p
  /-- (C5) `Y_g(T) ∩ B̂ ⊆ Y_B(T_B)` for a parent segment `T_B` of `T` in `B`. -/
  into : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ fam p, Yg i ∩ P B ⊆ (Y p).shade
  /-- (C5) conversely `Y_B(T_B) ⊆ ⋃_{T ∈ 𝕋(T_B)} Y_g(T)`. -/
  back : ∀ B ∈ bs, ∀ p ∈ segs B, (Y p).shade ⊆ ⋃ i ∈ fam p, Yg i
  /-- (C3) the *directional* half of the comparability `T ∩ B̂ ∼ T_B`: a segment `T_B` lies in
  the `C₀δ`-neighbourhood of the core line of each of its parent tubes `T ∈ 𝕋(T_B)`.

  The remaining fields record the comparability only through volumes and thicknesses:
  `segs_thickness` says `T_B` is a `C₀`-comparable `r₁ × δ × δ` body, `into`/`back` relate the
  shadings, and `segs_dilation` compares densities. None of them constrains the *direction* of
  `T_B` relative to `T`, and without such a constraint the axis of the factoring body
  `W = W(T_B)` is unrelated to the directions of the tubes of `𝕋(T_B)`.

  This field is what makes blueprint `lem:ml2bodyAngle` usable at the configuration level: it is
  exactly the hypothesis `hST` of `Kakeya.NonSlab.lineAngle_bodyAxis_le`, whose conclusion
  `∠(T, v(W)) ≤ C_{lem:ml2bodyAngle}(C₀) · b/r₁` is the angle bound
  `Kakeya.VeryNotSticky.segAngle` feeds to the compatible refinement
  `Kakeya.NonSlab.compat`. The base point of the line is existentially quantified because
  `lineAngle_bodyAxis_le` uses only the *direction* of the line.

  Like every other field here it is supplied by `Kakeya.VeryNotSticky.exists_setup_caseSideData`,
  which constructs the only `BallData` in the development. -/
  segs_core : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ fam p,
    ∃ q : EuclideanSpace ℝ (Fin 3), (Y p).carrier ⊆
      cthickening ((C₀ : ℝ) * (cfg.δ : ℝ))
        (AffineSubspace.mk' q (Submodule.span ℝ {(cfg.T i).direction}) :
          Set (EuclideanSpace ℝ (Fin 3)))
  /-- (C5) the common fibre-count scale: `|𝕋(T_B)_Y(x)| ≈ m` on `Y_B(T_B)`, with one and the
  same `m` for every ball and every segment. -/
  m : NNReal
  /-- (C5) the comparison constant of the fibre count. -/
  Cm : NNReal
  /-- `1 ≤ Cm`. -/
  hCm : 1 ≤ Cm
  /-- (C5) the fibre count `|𝕋(T_B)_{Y_g}(x)| ≈ m` for `x ∈ Y_B(T_B)`, read on the working
  shading `Y_g`. This is what `Kakeya.ThinCase.liftFibre` and
  `Kakeya.ThinCase.lift` consume, and hence what makes the refinement conclusion of
  `Kakeya.ThinCase.thinSetupExists` true: without it a segment outside `𝒮_B` with an
  arbitrarily large parent family makes the amalgamated loss unbounded. -/
  fibre : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ x ∈ (Y p).shade,
    (m : ENNReal) ≤ Cm * {i ∈ fam p | x ∈ Yg i}.card ∧
      (({i ∈ fam p | x ∈ Yg i}.card : ℕ) : ENNReal) ≤ Cm * m
  /-- The index type of the `δ`-ball covers `𝒞(T_B)` of Configuration `hyp:ml2thinsetup`. -/
  γ : Type u
  /-- The `δ`-ball cover `𝒞(T_B)` of a segment. -/
  cov : σ → Finset γ
  /-- The centre of a `δ`-ball of a cover. -/
  covCtr : γ → EuclideanSpace ℝ (Fin 3)
  /-- Each `𝒞(T_B)` is a `D`-boundedly overlapping cover of `T_B` by `δ`-balls. -/
  cov_isCover : ∀ B ∈ bs, ∀ p ∈ segs B,
    IsBoundedlyOverlappingCover (cov p) covCtr (fun _ => (cfg.δ : ℝ)) D (Y p).carrier
  /-- Every `δ`-ball of `𝒞(T_B)` meets `T_B`. -/
  cov_meets : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ cov p,
    (ball (covCtr i) (cfg.δ : ℝ) ∩ (Y p).carrier).Nonempty

attribute [instance] BallData.decidableEqω

/-! ### The working-shading block (C5′) and the (C5) clauses on it, pinned

The `statement_of_universal_*` device (`Kakeya.VeryNotSticky.statement_of_universal_thinConfig_T7`):
the licensed text of the fields is a named `Prop`, and a theorem checks that the fields *are*
that proposition, by projection. A later change to any of the nine clauses — `Y_g` identified
to `Y`, the mass clause dropped, a (C5) clause read on a different shading — fails to elaborate
here. -/

open scoped Classical in
def statement_of_universal_ballData_workingShading (cfg : VeryNotSticky.{u}) {bι σ : Type u}
    (Yg : cfg.ι → Set (EuclideanSpace ℝ (Fin 3))) (Cg : NNReal) (bs : Finset bι)
    (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (segs : bι → Finset σ)
    (Y : σ → ShadedBody (EuclideanSpace ℝ (Fin 3))) (fam : σ → Finset cfg.ι)
    (m Cm : NNReal) : Prop :=
  (∀ i ∈ cfg.s, Yg i ⊆ (cfg.T i).shade) ∧
  (∀ i ∈ cfg.s, MeasurableSet (Yg i)) ∧
  1 ≤ Cg ∧
  ((Cg : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤ ∑ i ∈ cfg.s, volume (Yg i)) ∧
  (∀ i ∈ cfg.s, Yg i ⊆ ⋃ B ∈ bs, P B) ∧
  (∀ B ∈ bs, ∀ i ∈ cfg.s, (Yg i ∩ P B).Nonempty → ∃ p ∈ segs B, i ∈ fam p) ∧
  (∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ fam p, Yg i ∩ P B ⊆ (Y p).shade) ∧
  (∀ B ∈ bs, ∀ p ∈ segs B, (Y p).shade ⊆ ⋃ i ∈ fam p, Yg i) ∧
  (∀ B ∈ bs, ∀ p ∈ segs B, ∀ x ∈ (Y p).shade,
    (m : ENNReal) ≤ Cm * {i ∈ fam p | x ∈ Yg i}.card ∧
      (({i ∈ fam p | x ∈ Yg i}.card : ℕ) : ENNReal) ≤ Cm * m)

theorem statement_of_universal_ballData_workingShading_pinned (cfg : VeryNotSticky.{u})
    (bd : BallData cfg) :
    statement_of_universal_ballData_workingShading cfg bd.Yg bd.Cg bd.bs bd.P bd.segs bd.Y bd.fam
      bd.m bd.Cm :=
  ⟨bd.Yg_subset, bd.Yg_measurable, bd.hCg, bd.Yg_mass, bd.P_cover, bd.parent, bd.into, bd.back,
    bd.fibre⟩

/-- **The clause (C5), as a named `Prop`**: the per-segment
density at `δ^{2η}` with the free constant `c₁`, at the parameters `(cfg, c₁, bs, segs, Y)` the
field reads. -/
def statement_of_universal_ballData_C5_density (cfg : VeryNotSticky.{u}) {bι σ : Type u}
    (c₁ : NNReal) (bs : Finset bι) (segs : bι → Finset σ)
    (Y : σ → ShadedBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ B ∈ bs, ∀ p ∈ segs B,
    (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (Y p).carrier ≤
      volume (Y p).shade

/-- **The pin.** The field `Kakeya.VeryNotSticky.BallData.segs_density` is
`statement_of_universal_ballData_C5_density` by unfolding and nothing else. -/
theorem statement_of_universal_ballData_C5_density_pinned (cfg : VeryNotSticky.{u})
    (bd : BallData cfg) :
    statement_of_universal_ballData_C5_density cfg bd.c₁ bd.bs bd.segs bd.Y :=
  bd.segs_density

/-- **The ascending frame of a convex body of `ℝ³`, at the ambient dimension** (blueprint
`def:ml2bodyFrame`): `Kakeya.NonSlab.bodyFrame` with the proof `finrank_euclideanSpace_fin` of
`dim ℝ³ = 3` supplied once.

Folded for the reason recorded on `Kakeya.VeryNotSticky.bodyNormal`: written out, the `finrank`
proof and the five instance searches around it are re-elaborated at every occurrence, and two
occurrences in one statement already exhaust a declaration's heartbeat budget. Use
`Kakeya.VeryNotSticky.bodyFrame_zero` rather than `simp`/`unfold`.

It lives here, upstream of both `Kakeya.DimensionThree.MainLemma2.PlankPresentation` (which
hands it to the prescribed-frame enclosure) and
`Kakeya.DimensionThree.MainLemma2.TypicalAngle` (which reads angles off it), because those two
files are siblings and each needs the *same* folded constant; two copies would be two distinct
declarations of the same name. -/
noncomputable def bodyFrame (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  NonSlab.bodyFrame finrank_euclideanSpace_fin W

/-- The rank-`0` vector of the ascending frame is the body's normal. This is the identity that
turns `Kakeya.VeryNotSticky.PlankPresentationData.hbasis` into a statement about
`Kakeya.VeryNotSticky.axisAngle`. -/
lemma bodyFrame_zero (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    bodyFrame W 0 = NonSlab.bodyNormal finrank_euclideanSpace_fin W :=
  NonSlab.bodyFrame_zero finrank_euclideanSpace_fin W

/-- **The axis of a convex body of `ℝ³`, at the ambient dimension** (blueprint
`def:ml2bodyAxis`): `Kakeya.NonSlab.bodyAxis` with the proof `finrank_euclideanSpace_fin` of
`dim ℝ³ = 3` supplied once. Folded for the reason recorded on
`Kakeya.VeryNotSticky.bodyFrame`. -/
noncomputable def bodyAxis (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    EuclideanSpace ℝ (Fin 3) :=
  NonSlab.bodyAxis finrank_euclideanSpace_fin W

/-- **Fixed-scale thresholds for Main Lemma 2** (blueprint `hyp:ml2scale`).

All the conditions hold eventually as `δ → 0+` after the exponent parameters, the comparison
constants `bd.C₀` and `C`, and the thresholds `thr` have been fixed. Packaging them prevents
the fixed-scale case lemmas from silently absorbing constants or assuming that the dilated
scale `ρ₂*` is at most one.

The structure is indexed by:

* both threshold exponents `τ` and `τ'` of blueprint `hyp:ml2params`: the third condition is
  conditional on the thin-case hypothesis `a ≤ δ^{1-τ}`, and the fifth is the transverse
  transfer-radius threshold, which is a condition on `τ'`;
* the gain `ν`, at which blueprint `lem:ml2aScaleData` is invoked, since the threshold of
  `aScaleData_threshold` depends on it. That gain is a function of `β` and `ζ` alone, so
  unlike `C` it is fixed before `δ`, and the case split arranges the configuration at each of
  its two values at no cost. Along the non-slab chain the index is read at the transverse gain
  `τ'β/2`, that being the gain at which
  `Kakeya.VeryNotSticky.goalMult_of_theta_ge` invokes
  `Kakeya.VeryNotSticky.exists_aScaleData`; the thick gain `ϱβτ/8` reaches
  `Kakeya.VeryNotSticky.goalMult_of_a_ge_of_goalDensity` as a bare binder instead, that
  statement seeing neither `bd` nor a thin-case constant;
* the constant `C`, which the call site instantiates at `tc.C` for the ambient
  `Kakeya.VeryNotSticky.ThinConfig`. It is produced by blueprint `lem:ml2thinsetupexists`, i.e.
  *after* `δ`, which is why `transverse_ballFill` is written as a comparison of terms rather
  than as a `δ ≤ δ_*` (the latter would be circular) and why arranging that clause is an
  obligation of blueprint `lem:ml2casesplit`, at the point where `C` is produced, rather than
  of any statement of the transverse chain;
* the by-choice thresholds `thr`, for the reason given on
  `Kakeya.VeryNotSticky.ScaleThresholds`.

Apart from `C` and `thr`, every condition is an inequality between quantities determined by
`cfg`, `bd` and the exponents, so none of them mentions a constant produced later in the
development; that is what keeps the bundle satisfiable, and the two extra indices are exactly
what restores that invariant for the clauses that would otherwise break it.

All *thirteen* clauses of blueprint `hyp:ml2scale` are fields here. The tenth,
`plankCardBiasThreshold`, mentions `Kakeya.VeryNotSticky.plankEnclosureConstant`, and the
twelfth, `typicalAngleSelectionThreshold`, mentions
`Kakeya.VeryNotSticky.plankSelectionConstant`; both constants are declared in
`Kakeya.DimensionThree.MainLemma2.PlankConstants`, upstream of this file, for exactly that
reason. Neither needs an index of its own, `Cbias` being a field of `bd`. -/
structure CaseScale (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (τ τ' ν : ℝ) (C : NNReal)
    (thr : ScaleThresholds) : Prop where
  /-- The dilated non-slab angular scale is at most one. -/
  rho2Star_le_one :
    cfg.δ ^ cfg.exscal ≤ (2 * NonSlab.bodyAngleConstant bd.C₀)⁻¹
  /-- In the non-slab branch, a factoring body fits at the rescaled ball scale. -/
  body_fits_ball : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → bd.C₀ * cfg.b ≤ cfg.r₁
  /-- In the thin branch, the rescaled shortest plank dimension lies below the
  typical-angle cutoff. -/
  plank_small : cfg.a ≤ cfg.δ ^ (1 - τ) →
    ((bd.C₀ * (cfg.a / cfg.r₁) : NNReal) : ℝ) ≤ Real.exp (-1)
  /-- The multiplicity threshold used by the typical-angle lemma is at least two. -/
  multiplicity_large : 2 ≤ ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) ^ (-(16 * cfg.η))
  /-- In the transverse branch, the transfer radius `ρ = θ b / 2 ≥ δ^{-τ'} a / 2` exceeds the
  covering radius `3A = 3 C_{w₁}(C₀) a` of blueprint `def:ml2thinW1Constant`. This is the
  fixed-scale threshold that blueprint `lem:ml2transverseMassBall` discharges with the phrase
  "once `δ` is small enough": since `τ' > 0` the left-hand side is a function of `bd.C₀`
  alone while `δ^{-τ'} → ∞` as `δ → 0+`. It is consumed by
  `Kakeya.VeryNotSticky.goalMult_of_theta_ge`, which passes it to
  `Kakeya.VeryNotSticky.transverseBallFill` as the hypothesis `hsmall`. -/
  transverse_radius : 6 * ThinCase.w1Constant bd.C₀ ≤ cfg.δ ^ (-τ')
  /-- The sixth clause, blueprint `transverseFillThreshold`. It pays for the two explicit
  factors that the proof of blueprint `lem:ml2transverseFill` absorbs into its constant: the
  `3³` discarded with the dilation of the radius, and the `max(1, C₀/3)³` paid for enlarging
  the produced radius to `r ≥ θ b`. It is what lets that lemma conclude the sub-polynomial
  bound `transverseFillConstantBound`. It is stated at `η/2` rather than at `η` because the
  bound it serves is assembled from two halves, of which Section 6 supplies the other. -/
  transverse_fill : 27 * max 1 (bd.C₀ / 3) ^ 3 ≤ cfg.δ ^ (-(cfg.η / 2))
  /-- The seventh clause, blueprint `transverseBallFillThreshold`. It pays for the three
  explicit factors of blueprint `def:ml2transverseBallFillConstant` — the `2³`, the
  `c_{lem:massSubball}(3,2)⁻¹ = 5³` and the transfer constant
  `Kakeya.ThinCase.transferConstant C bd.C₀` — whose product carries the factor
  `2³ * 5³ = 1000`, and it is what lets blueprint `lem:ml2transverseBallFillConstantBound`
  conclude `transverseBallFillConstantBound`.

  This is the one clause whose left-hand side is not a function of `bd.C₀` and the exponent
  parameters alone, since `C` is produced after `δ`; the index `C` is what restores the module
  invariant. It is nevertheless arrangeable: `C` is sub-polynomial in `δ⁻¹` and
  `transferConstant` is an explicit polynomial in `C` and `bd.C₀`, so the whole left-hand side
  is sub-polynomial while the right-hand side is `δ^{-η}` with `η > 0` fixed. -/
  transverse_ballFill : 1000 * ThinCase.transferConstant C bd.C₀ ≤ cfg.δ ^ (-cfg.η)
  /-- The eighth clause, blueprint `aScaleDataThreshold`: `δ` lies below the by-choice
  threshold of blueprint `lem:ml2aScaleData` at the gain `ν`. This is what makes clause (iii)
  of that lemma provable rather than refutable — without it the assertion fails at `δ` near
  `1`, since it bounds by `δ^{-η}` a constant that is at least `1` and does not tend to `1` as
  `δ → 1`. It is the clause the transverse chain spends, in
  `Kakeya.VeryNotSticky.goalMult_of_theta_ge`, to discharge the hypothesis `hthr` of
  `Kakeya.VeryNotSticky.exists_aScaleData`; that is why the gain `ν` indexing this structure
  is read at the transverse gain `τ'β/2` all the way down the non-slab chain. See the caveat
  on `Kakeya.VeryNotSticky.ScaleThresholds`: while `thr` carries no defining property, this
  clause is trivially satisfiable and does not have that effect. -/
  aScaleData_threshold : cfg.δ ≤ thr.aScale ν
  /-- The ninth clause, blueprint `typicalAngleThreshold`: `δ` lies below the by-choice
  threshold of blueprint `lem:ml2typicalangle`. It does for `typicalAngleConstantBound` what
  the eighth clause does for clause (iii) of `lem:ml2aScaleData`. It may not mention `Cbias`,
  on pain of circularity, which is what the tenth clause `plankCard_bias` below buys. -/
  typicalAngle_threshold : cfg.δ ≤ thr.typical
  /-- The typical-angle *constant* threshold. `Kakeya.findingTypicalAngleOfIntersection_perScale`
  binds its comparison constant `C` before every geometric datum and carries no upper bound on it
  — with `C` bound after the configuration and pinched by `C ≤ δ^{-ε}` the statement is false, see
  its docstring — so the bound `C ≤ (δ')^{-η/1024}` that
  `Kakeya.VeryNotSticky.typicalAngleArith` spends is a genuine smallness condition on `δ` and has
  to be assumed here. It is of the seventh clause's shape and legitimate for the seventh clause's
  reason: the left-hand side is `Kakeya.typicalAngleScaledConst` at arguments built from `bd.C₀`,
  `bd.Cbias` and the exponent parameters, while the right-hand side is `(δ')^{-η/1024}` with
  `η > 0` fixed, and `δ' = δ^{1 - exscal} → 0`. Like the tenth clause it mentions `Cbias`, which
  is why it is a clause of its own rather than part of `typicalAngle_threshold`. -/
  typicalAngle_const :
    Kakeya.typicalAngleScaledConst.{u} (cfg.η / 1024)
        (plankCardConstant * (plankEnclosureConstant bd.C₀ * bd.Cbias *
          cfg.δ ^ (-(2 * cfg.ϱ)))) plankCardExponent ≤
      (cfg.δ / cfg.r₁ : NNReal) ^ (-(cfg.η / 1024))
  /-- The tenth clause, blueprint `plankCardBiasThreshold`:
  `C_{lem:ml2plankpresentation}(C₀) * C_bias * δ^ϱ ≤ 1`.

  It is of the seventh clause's shape and is there for the seventh clause's reason: the
  biased-factoring constant `bd.Cbias` of (C4) is, like the thin-case comparison constant
  `C`, produced *after* `δ`, and it enters the cardinality bridge that blueprint
  `lem:ml2typicalangle` feeds to `findingTypicalAngleOfIntersection` through the
  anti-clustering bound of (C4). Since the ninth clause is a `δ ≤ δ_*` for a threshold
  defined by choice, it may not mention `Cbias` on pain of circularity; this clause is what
  buys that, by paying for `Cbias` separately out of the surplus `δ^ϱ` with `ϱ > 0` fixed
  before `δ`. Being a comparison of terms and not a `δ ≤ δ_*`, it is arrangeable by the
  argument that serves blueprint `hyp:ml2slabscale` rather than the one that serves the first
  six clauses, `plankEnclosureConstant bd.C₀` being a function of `bd.C₀` alone and `Cbias`
  sub-polynomial by blueprint `lemmafactmaxbias`. -/
  plankCard_bias : plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ cfg.ϱ ≤ 1
  /-- The eleventh clause, blueprint `transverseFillPlankThreshold`: the plank-to-slab
  reduction is available at the rescaled scale `δ' = δ/r₁`, at the exponents `ε = η/256`,
  `ε' = η/2` and the cardinality data `(C_{lem:ml2plankcard}, N_{lem:ml2plankcard} + 6ϱ)` at
  which blueprint `lem:ml2transverseFill` invokes it. It is what lets that lemma apply
  `lemmaredplanktubeAtTypicalAngle` at all, that lemma being stated under a smallness
  threshold on the scale it is applied at, while the transverse case applies it at `δ/r₁`.

  It replaces the earlier reading `cfg.δ ≤ thr.fill`, which said nothing:
  `Kakeya.VeryNotSticky.ScaleThresholds.fill` carries no defining property, and the threshold
  it stands for is produced *existentially* by
  `ShadedPlank.reduction_to_slab_atTypicalAngle`, so it cannot be named in a structure
  declared upstream of that lemma's call site. Asserting the conclusion at the scale in
  question says exactly what the by-choice threshold was meant to say, and
  `Kakeya.VeryNotSticky.exists_isReductionFillAvailable` certifies that it holds below a
  threshold fixed before `δ` — so this clause is of the eighth clause's shape, a genuine
  fixed-scale condition, and is neither vacuous nor unsatisfiable.

  The cardinality exponent is `plankCardExponent + 6ϱ` and not `plankCardExponent`: the
  cardinality bridge `Kakeya.VeryNotSticky.plankCard` produces the bound with the
  `δ`-dependent factor `C(C₀) C_bias δ^{-2ϱ}`, which the tenth clause `plankCard_bias`
  converts into `δ^{-3ϱ}` and hence, by `δ^{-3ϱ} = (δ')^{-3ϱ/(1-exscal)} ≤ (δ')^{-6ϱ}` with
  `exscal < 1/2`, into a power of the rescaled scale with the `δ`-free constant
  `plankCardConstant` the reduction demands. -/
  transverseFill_threshold : IsReductionFillAvailable bd.ω (16 * cfg.η) plankCardConstant
    (plankCardExponent + 6 * cfg.ϱ) (cfg.δ / cfg.r₁)
  /-- **(O5) In the transverse case, the plank family of a thin ball is `(a')^η`-full**.

  This is the fullness hypothesis `λ(𝒫, Y) ≥ a^η` of GWZ Lemma 6.13 (`gwz.txt` l.979-980:
  "let `(𝒫, Y)` be a set of `a × b × 1` planks in the unit ball with `λ(𝒫, Y) ≥ a^η` and
  `μ(𝒫, Y) ≥ a^{-η}`"), read at the plank family `𝒫 = L_B(𝕎'_B)` of blueprint
  `lem:ml2plankpresentation` and at the selected subfamily `𝕊*`, where
  `ShadedPlank.reduction_to_slab_atTypicalAngle` consumes it.

  **It is a mathematical input and not a matter of plumbing.** The setup supplies fullness
  only through (95), `λ(𝕎'_B, Y_{𝕎'_B}) ⪆ δ^{2η}` (l.2188; (T2) in this development,
  `Kakeya.ThinCase.ThinBall.fullness_bodies`), and `a'` is not comparable to `δ`: by
  `Kakeya.VeryNotSticky.PlankPresentationData.hδa'` and `hupper` one has
  `δ^{1-exscal} ≤ a' ≤ C₀ δ^{1-τ-exscal}`, so `(a')^η ≥ δ^{(1-τ-exscal)η}`, which exceeds
  `δ^{2η}` by a positive power of `δ` — shrinking `δ` makes the gap worse, so no constant and
  no smallness hypothesis repairs it. GWZ never assert `(a')^η`-fullness of the setup: they
  apply Lemma 6.13 at an exponent for which its hypothesis follows from (95) (their `a^{3η}`
  at l.2236 is `O(η)` bookkeeping). At the exponent `cfg.η` this clause is therefore stronger
  than anything the source or the configuration supplies (see also
  `Kakeya.VeryNotSticky.TypicalAngleData.hfull`); the re-budgeting of that exponent is a
  separate, later steps, and this clause is where
  the Lean development records the debt.

  **The transverse guard.** GWZ invoke Lemma 6.13 only in the transverse case
  `θ ≥ δ^{-τ'} a/b` (l.2224: "We define the transverse case to be the case that
  `θ ≥ δ^{-τ'} a/b`"), and since the typical angle satisfies `θ ≤ 1`
  (`Kakeya.VeryNotSticky.TypicalAngleData.hθ1`) that case can occur only when
  `δ^{-τ'} a/b ≤ 1`. The clause is asserted under exactly that guard. It is vacuous when
  `δ^{-τ'} a/b > 1` — in particular at `a = b`, the regime in which
  `Kakeya.VeryNotSticky.false_of_transverseFill_fullness` refutes the unguarded clause — and
  it says what GWZ use precisely where GWZ use it. The consumer
  `Kakeya.VeryNotSticky.TypicalAngleData.hfullP` carries the guard in the form
  `δ^{-τ'} a/b ≤ θ`, and `le_trans htrans ta.hθ1` produces this one at the transverse leaf.

  **The thin guard.** The clause is a §9.5 object: `gwz.txt` l.2176 opens the thin case with
  "Now we consider the thin case when `a ∈ [δ, δ^{1-τ}]`", and the plank presentation, the
  typical angle and the transverse/tangential split all live inside that subsection (§9.4 is
  `a ≥ δ^{1-τ}`). So `cfg.a ≤ cfg.δ^{1-τ}` is a source condition of the concept, not an added
  hypothesis, and it is written in the same shape the neighbouring field
  `Kakeya.VeryNotSticky.CaseScale.plank_small` already uses. The unique consumer
  `Kakeya.VeryNotSticky.goalMult_of_multBodies_ge` carries it as its own explicit binder and
  spends it on `plank_small` two lines above, so the guard costs nothing there; for the
  producers it is a gift.

  **The pins.** The quantifiers range over an arbitrary shaded plank family, so the clause
  would be false without them. The two pins on `a'` and the pin on `b'` tie the plank
  dimensions to those of the factoring bodies at the scale `r₁`
  (`Kakeya.VeryNotSticky.PlankPresentationData.hlower`, `hupper`, `hbupper`); the *upper* pin
  on `b'` is the one that blocks the refutation of
  `Kakeya/DimensionThree/MainLemma2/CaseScaleNonslabRefute.lean` — a lower pin alone does not,
  since `b' = 1` satisfies it. The two hypotheses on `t` and on `SP` say that `t` retains a
  `(C^{sel})⁻¹` fraction of the shaded mass — which is what
  `Kakeya.VeryNotSticky.PlankPresentationData.hselRefine` supplies for the selection `𝕊*` —
  and that the shadings of `SP` are the transports of `Y_{𝕎'_B}` under the homothety `L_B`,
  which multiplies every volume by `r₁⁻³`
  (`Kakeya.VeryNotSticky.PlankPresentationData.hvol`). With all of them, the statement is
  exactly `(a')^η ≤ λ(𝒫, Y_𝒫)` in the transverse case and nothing more.

  It is stated over `Kakeya.ThinCase.ThinBall` rather than over
  `Kakeya.VeryNotSticky.ThinConfig` because that structure is declared below this one; at the
  call site it is read at `tc.thinBall hB`, whose comparison constant is the index `C`. -/
  transverseFill_fullness : cfg.a ≤ cfg.δ ^ (1 - τ) →
      cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ 1 →
      ∀ (B : bd.bι) (_hB : B ∈ bd.bs)
      (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
        cfg.δ cfg.a (2 * cfg.η))
      {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
      (t : Finset bd.ω) (SP : bd.ω → ShadedPlank a' b' hab' hb1'),
      t ⊆ tb.bodies' →
      bd.C₀⁻¹ * (cfg.a / cfg.r₁) ≤ a' → a' ≤ bd.C₀ * (cfg.a / cfg.r₁) →
      b' ≤ bd.C₀ * (cfg.b / cfg.r₁) →
      ((plankSelectionConstant bd.C₀ : ENNReal))⁻¹ *
          (∑ i ∈ tb.bodies', volume (tb.W i).shade) ≤ ∑ i ∈ t, volume (tb.W i).shade →
      (∀ i ∈ t, volume (ShadedPlank.bodies SP i).shade * ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3)
        = volume (tb.W i).shade) →
      a' ^ (16 * cfg.η) ≤ ShadedBody.fullness t (ShadedPlank.bodies SP)
  /-- The twelfth clause, blueprint `typicalAngleSelectionThreshold`:
  `C^{sel}(C₀) ≤ δ^{-exscal·η}`.

  This is the threshold that `Kakeya.VeryNotSticky.plankSubfamilyMult` consumes as its `hthr`,
  and it is what lets `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` run
  `Kakeya.findingTypicalAngleOfIntersection_perScale` on the *selected* subfamily `𝕊*` rather
  than on all of `𝕎'_B` — where the enclosing planks are not pairwise essentially distinct, so
  that lemma does not apply. It is a genuine smallness condition in `δ` and not slack: the
  left-hand side is fixed once `bd.C₀` is, hence before `δ`, and the right-hand side is a
  positive power of `δ`; and it is spent with nothing to spare, which is why its exponent is
  `exscal · η`.

  It is of the tenth clause's shape rather than of the eighth's — a comparison of terms, not a
  `δ ≤ δ_*` — and it is arrangeable for the same reason: `plankSelectionConstant bd.C₀` is a
  function of `bd.C₀` alone. -/
  typicalAngle_selection :
    (plankSelectionConstant bd.C₀ : ℝ) ≤ (cfg.δ : ℝ) ^ (-(cfg.exscal * cfg.η))
  /-- The thirteenth clause, blueprint `typicalAngleCapThreshold`: `2 ≤ (δ')^{-η/512}` at the
  rescaled scale `δ' = δ / r₁`.

  It buys the *bounded* multiplicative room in which the typicality constant
  `Kakeya.VeryNotSticky.TypicalAngleData.Ctyp` may absorb the cap of
  `Kakeya.effectivePlankAngle`. That definition floors the plank angle at `a/b` and caps it at
  `1`, so the typicality hypothesis carries no information about a pair of planks whose angle
  bound `Ctyp θ` has already reached `1`; but the field
  `Kakeya.VeryNotSticky.TypicalAngleData.hangle` asks for a bound on the *uncapped* angle
  `Kakeya.VeryNotSticky.axisAngle`, which is at most `π/2 > 1`. Enlarging `Ctyp` by the factor
  `2 ≥ π/2` closes that gap — both `Kakeya.IsTypicalPlankAngle` and
  `ShadedBody.HasCConstantMultiplicity` only weaken as the constant grows — and this clause is
  what keeps the enlarged constant inside the budget
  `Ctyp ≤ (δ')^{-η/256}` of `TypicalAngleData.hCtyp`.

  It is strictly stronger than `multiplicity_large` (whence `2 ≤ (δ')^{-η}`), which is kept as
  a separate field because it is consumed separately, as
  `Kakeya.findingTypicalAngleOfIntersection_perScale`'s hypothesis `hμ2`. Like the fourth clause
  it holds for small `δ`, `δ' = δ^{1-exscal} → 0` and `η > 0` being fixed first. -/
  typicalAngle_cap : (2 : ℝ) ≤ ((cfg.δ / cfg.r₁ : NNReal) : ℝ) ^ (-(cfg.η / 512))

/-- **Configuration `hyp:ml2thinsetup`, relative to `cfg` and to its per-ball data**
(blueprint `hyp:ml2thinsetup`).

The per-ball payload (T1)–(T6) is *not* restated here: it is
`Kakeya.ThinCase.ThinBall`, and the point of this structure is that the single comparison
constant `C` and the scales `cfg.δ`, `cfg.a`, `2 · cfg.η`, `bd.C₀` are shared by *every* ball, as
the blueprint demands ("these hold for all `B ∈ 𝔅` simultaneously"). The two genuinely global
assertions of (T1) — that `Y'` is a `⪆ 1` refinement of `Y` on `𝕋`, and the two-way
compatibility of `Y'` with the per-ball shadings `Y'_B` — are the remaining fields.

Configuration `hyp:ml2thinsetup` is extra data attached to the same pair `(𝕋, Y)`; `cfg` is
not modified and continues to realize Configuration `hyp:ml2setup`. Accordingly the thin-case
hypothesis `a ≤ δ^{1-τ}` is *not* a field: none of (T1)–(T6) uses it, and it enters the branch
lemmas as a separate hypothesis. -/
structure ThinConfig (cfg : VeryNotSticky.{u}) (bd : BallData cfg) where
  /-- The comparison constant of (T1)–(T6), one and the same for every ball `B ∈ 𝔅`. -/
  C : NNReal
  /-- (T1) the global refined shading `Y'` on `𝕋`. -/
  Y' : cfg.ι → Set (EuclideanSpace ℝ (Fin 3))
  /-- (T1) `Y'(T) ⊆ Y_g(T)`: the refined shading sits inside the *working* shading of `bd`
  (a strengthening — `Y'(T) ⊆ Y(T)` follows by
  `Kakeya.VeryNotSticky.BallData.Yg_subset`). -/
  Y'_subset : ∀ i ∈ cfg.s, Y' i ⊆ bd.Yg i
  /-- (T1) `Y'` is measurable. -/
  Y'_measurable : ∀ i ∈ cfg.s, MeasurableSet (Y' i)
  /-- (T1) `(𝕋, Y')` is a `⪆ 1` refinement of `(𝕋, Y)`. -/
  Y'_mass : (C : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
    ∑ i ∈ cfg.s, volume (Y' i)
  /-- (T1)–(T6) the thin-case data attached to each ball `B ∈ 𝔅`, with the same comparison
  constant `C` for every ball, at the density index `2η` = the exponent of (C5),
  `Kakeya.VeryNotSticky.BallData.segs_density` : `ThinBall`'s two
  `η`-fields then read `fullness_bodies : δ^{6η} ≤ C λ(𝕎'_B, Y_{𝕎'_B})` and
  `denseBall : C⁻¹ δ^{2η} |B_δ| ≤ |B_δ ∩ Y'_B(T_B)|`. -/
  tb : ∀ B ∈ bd.bs, ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
    cfg.δ cfg.a (2 * cfg.η)
  /-- (T1) the forward compatibility `Y'(T) ∩ T_B ∩ B̂ ⊆ Y'_B(T_B)` for `T ∈ 𝕋(T_B)`. -/
  compat_forward : ∀ (B : bd.bι) (hB : B ∈ bd.bs), ∀ p ∈ bd.segs B, ∀ i ∈ bd.fam p,
    Y' i ∩ (bd.Y p).carrier ∩ bd.P B ⊆ ((tb B hB).Y' p).shade
  /-- (T1) the reverse compatibility `Y'_B(T_B) ⊆ ⋃_{T ∈ 𝕋(T_B)} Y'(T)`, whence
  `U(𝕋_B, Y'_B) ⊆ U(𝕋, Y')`. -/
  compat_backward : ∀ (B : bd.bι) (hB : B ∈ bd.bs), ∀ p ∈ bd.segs B,
    ((tb B hB).Y' p).shade ⊆ ⋃ i ∈ bd.fam p, Y' i
  /-- (T7) *The retained segments account for the tubes, up to the density and the fibre
  count.*
  `δ^{2η} ∑_{T ∈ 𝕋} |T| ≤ C · Cm · m · ∑_{B ∈ 𝔅} ∑_{T_B ∈ 𝕋_B^{𝕎'}} |T_B|`, the sum on the right
  being over the segments whose block was retained by the factoring, i.e. over
  `Kakeya.VeryNotSticky.retainedSegments`.

  The restriction to the retained blocks `𝕎'_B` is what makes the inequality usable: a segment
  whose block was discarded lies in no body of `𝕎'_B` and cannot be counted on the other side
  of `Kakeya.VeryNotSticky.slabSegmentSumSplit`, so the corresponding statement for all of
  `𝕋_B` is strictly weaker and does not imply this one. The blocks `𝕎'_B` are produced by this
  configuration and not by (C3), which is why the field lives here.

  **The loss is explicit**. GWZ (`gwz.txt` l.2210-2216) pass from the
  per-ball `|𝕎'_B||W| ⪆ r₁²|𝕋_B||T_B|` to `|U(𝕋,Y)| ⪆ … r₁²|𝕋||T|` by "summing over the
  `r₁`-balls", which needs `∑_B |𝕋_B||T_B| ⪆ |𝕋||T|`. That step needs (i) each tube to meet
  `⪆ r₁^{-1}` pieces `B̂`, which holds only up to the density —
  `Kakeya.VeryNotSticky.fullness_ge` at `δ^{2η}` — and (ii) the comparability classes `𝕋(T_B)`
  (l.2022-2023) to have `⪅ 1` members, which GWZ do not establish: a bush of tubes through one
  segment has up to the fibre count `≈ m` of (C5) (`Kakeya.VeryNotSticky.BallData.fibre`,
  constant `Cm`) members, and the passage from `Y` to the refined shading `Y'` of (T1) costs the
  comparison constant `C` (`Y'_mass`, `Kakeya.ThinCase.ThinBall.shade_containment`). So the `⪆`
  at l.2215 hides `δ^{O(η)}` and the fibre scale, and the earlier constant-`1` form of this
  field was the over-strong rendering of a `⪆`. The exact cost is recorded here: `δ^{2η}` on
  the left and `C · Cm · m` on the right. Downstream, the `δ^{2η}` joins the exponent of
  `Kakeya.VeryNotSticky.slabMassBound` (`9η ↦ 11η`), `C` and `Cdil` are absorbed in
  `Kakeya.VeryNotSticky.SlabScale.final`, `Cm · m` in
  `Kakeya.VeryNotSticky.SlabScale.fibreMass` at the budget `δ^{-(η+2 exscal)}`, and the budget
  `Kakeya.VeryNotSticky.CaseParams.slab` reads `12η + 12 exscal + 3τ < β/2`, inside GWZ's
  "`τ, η, ϵ_scal ≪ β`" (l.2217).

  It is *derived*, not assumed: `Kakeya.VeryNotSticky.segment_mass_of_compat` proves it from
  `Kakeya.VeryNotSticky.fullness_ge`, `P_cover`/`P_measurable`, `parent`/`into`,
  `fam_subset`/`fam_disjoint`, `fibre`, the refinement bound `Y'_mass`, the forward
  compatibility `compat_forward` and `Kakeya.ThinCase.ThinBall.shade_containment`, and
  `Kakeya.VeryNotSticky.exists_thinConfig` populates the field with that theorem rather than
  carrying it as a hypothesis. The text is pinned by
  `Kakeya.VeryNotSticky.statement_of_universal_thinConfig_T7`. -/
  segment_mass : (cfg.δ : ENNReal) ^ (2 * cfg.η) *
      ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
    (C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) *
      ∑ B ∈ bd.bs.attach, ∑ p ∈ (bd.segs B.1).filter (fun p ↦ bd.blk p ∈ (tb B.1 B.2).bodies'),
        volume (bd.Y p).carrier

/-! ### The clause (T7), pinned

The `statement_of_universal_*` device
(`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5`,
`Kakeya.VeryNotSticky.statement_of_universal_vns_fields`): the licensed text of the field is a
named `Prop`, and a theorem checks that the field *is* that proposition. A later change to the
field in either direction — the exponent moved, a constant dropped or added, the retained-block
filter weakened — fails to elaborate here, which a plain tripwire on a consumer would not notice
when the change is made in lockstep. -/

/-- **The clause (T7), as a named `Prop`**: the density loss
`δ^{2η}` on the left, the comparison constant `C`, the fibre-count constant `Cm` and the
fibre-count scale `m` on the right, and the sum over the retained segments of every ball. It
is the text of `Kakeya.VeryNotSticky.ThinConfig.segment_mass` verbatim, at the parameters
`(cfg, bd, C, tb)` the field reads. -/
def statement_of_universal_thinConfig_T7 (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (C : NNReal)
    (tb : ∀ B ∈ bd.bs, ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η)) : Prop :=
  (cfg.δ : ENNReal) ^ (2 * cfg.η) *
      ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
    (C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) *
      ∑ B ∈ bd.bs.attach, ∑ p ∈ (bd.segs B.1).filter (fun p ↦ bd.blk p ∈ (tb B.1 B.2).bodies'),
        volume (bd.Y p).carrier

/-- **The pin.** The field `Kakeya.VeryNotSticky.ThinConfig.segment_mass` is
`statement_of_universal_thinConfig_T7` by unfolding and nothing else: the proof term is the
projection itself. -/
theorem statement_of_universal_thinConfig_T7_pinned (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} (tc : ThinConfig cfg bd) :
    statement_of_universal_thinConfig_T7 cfg bd tc.C tc.tb :=
  tc.segment_mass

/-- The thin-case data (T1)–(T6) of `Kakeya.VeryNotSticky.ThinConfig` at a ball `B ∈ 𝔅`,
with the ball itself left implicit. The branch lemmas of the thin case read their families
`𝕎'_B` and shadings `Y_{𝕎'_B}` off `tc.thinBall hB` rather than taking them as free
arguments. -/
def ThinConfig.thinBall {cfg : VeryNotSticky.{u}} {bd : BallData cfg} (tc : ThinConfig cfg bd)
    {B : bd.bι} (hB : B ∈ bd.bs) :
    ThinCase.ThinBall tc.C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η) :=
  tc.tb B hB

open scoped Classical in
/-- **The refined global shading `(𝕋, Y')` of (T1), as a family of shaded bodies.**

`Kakeya.VeryNotSticky.ThinConfig.Y'` records the refined shading as a bare family of sets,
because that is the form (T1)'s compatibility clauses are stated in. The multiplicity API and
`Kakeya.NonSlab.multSplit` speak about `ShadedBody`s instead, so the shading has to be attached
to the carriers it refines, namely the tubes of `𝕋` themselves.

Outside `cfg.s` the shading is replaced by `∅`. That is forced, not cosmetic: `Y'_subset` and
`Y'_measurable` are assumed only on `cfg.s`, so there is nothing to attach off it, and every
statement about this family quantifies over `i ∈ cfg.s`. -/
noncomputable def ThinConfig.Y'Body {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (i : cfg.ι) : ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  toConvexSpaceBody := (cfg.T i).toConvexSpaceBody
  shade := if i ∈ cfg.s then tc.Y' i else ∅
  measurableSet_shade := by
    split_ifs with hi
    · exact tc.Y'_measurable i hi
    · exact MeasurableSet.empty
  shade_subset := by
    split_ifs with hi
    · exact ((tc.Y'_subset i hi).trans (bd.Yg_subset i hi)).trans (cfg.T i).shade_subset
    · simp

/-- The shading of `Kakeya.VeryNotSticky.ThinConfig.Y'Body` on `cfg.s`. -/
@[simp] lemma ThinConfig.Y'Body_shade {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {i : cfg.ι} (hi : i ∈ cfg.s) :
    (tc.Y'Body i).shade = tc.Y' i := by
  simp [ThinConfig.Y'Body, hi]

/-- `(𝕋, Y')` is a `C⁻¹`-refinement of `(𝕋, Y)`: this is (T1), blueprint
`hyp:ml2thinsetup`, read through `Kakeya.VeryNotSticky.ThinConfig.Y'Body`. It is the `href`
argument of `Kakeya.NonSlab.multSplit`. -/
theorem ThinConfig.isCRefinement_Y'Body {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (hC : 0 < tc.C) :
    ShadedBody.IsCRefinement cfg.s tc.Y'Body cfg.s (fun i ↦ (cfg.T i).toShadedBody)
      tc.C⁻¹ := by
  constructor
  · constructor
    · exact subset_rfl
    · intro i hi
      constructor
      · rfl
      · rw [ThinConfig.Y'Body_shade tc hi]
        exact (tc.Y'_subset i hi).trans (bd.Yg_subset i hi)
  · have hCne : tc.C ≠ 0 := ne_of_gt hC
    rw [ENNReal.coe_inv hCne]
    rw [show (∑ i ∈ cfg.s, volume (tc.Y'Body i).shade) =
            ∑ i ∈ cfg.s, volume (tc.Y' i) by
        exact Finset.sum_congr rfl (fun i hi => by rw [ThinConfig.Y'Body_shade tc hi])]
    exact tc.Y'_mass

/-- **The local shaded union sits inside the global one**: `U(𝕋_B, Y'_B) ⊆ U(𝕋, Y)`.

This is the `cfg`-relative reading of blueprint `lem:ml2thinLocalToGlobal`, whose abstract
form is `Kakeya.ThinCase.localToGlobal`. Its conclusion is carried by this bundle as the
field `Kakeya.VeryNotSticky.ThinConfig.compat_backward` — a point shaded by the per-ball
`Y'_B` at a segment `T_B` is shaded by the global `Y'` at one of the parent tubes of `T_B` —
and composing it with `Kakeya.VeryNotSticky.ThinConfig.Y'_subset` and
`Kakeya.VeryNotSticky.BallData.Yg_subset`, which say that `Y'` refines the working shading
`Y_g`, which refines `Y`, gives the containment in the pair `(𝕋, Y)` that the goal currencies
speak about.

It lives here, next to the two fields it composes, rather than in the branch files that
consume it: `Kakeya.VeryNotSticky.transverseBallFill` needs it to turn the local conclusion
of `Kakeya.ThinCase.transfer_thin` into a statement about `(𝕋, Y)`. -/
theorem ThinConfig.localUnion_subset {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) :
    (tc.thinBall hB).U ⊆ ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade := by
  intro x hx
  change x ∈ ⋃ p ∈ bd.segs B, ((tc.thinBall hB).Y' p).shade at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hx⟩
  have hx' : x ∈ ⋃ i ∈ bd.fam p, tc.Y' i := tc.compat_backward B hB p hp hx
  rcases Set.mem_iUnion₂.mp hx' with ⟨i, hi, hxi⟩
  have his : i ∈ cfg.s := bd.fam_subset B hB p hp hi
  exact Set.mem_iUnion₂.mpr ⟨i, his, bd.Yg_subset i his (tc.Y'_subset i his hxi)⟩

/-- **The clause (T7) is a theorem of the configuration**.

For the refined global shading `Y'` of (T1) — `Y'(T) ⊆ Y_g(T)` inside the working shading of
`bd`, measurable, with `C⁻¹ ∑_T |Y(T)| ≤ ∑_T |Y'(T)|` — and a per-ball
`Kakeya.ThinCase.ThinBall` family `tb` at the
same constant `C`, compatible with `Y'` in the forward direction
`Y'(T) ∩ T_B ∩ B̂ ⊆ Y'_B(T_B)` for `T ∈ 𝕋(T_B)`, the retained segments account for the tubes:
`δ^{2η} ∑_{T ∈ 𝕋} |T| ≤ C · Cm · m · ∑_{B ∈ 𝔅} ∑_{T_B ∈ 𝕋_B, W(T_B) ∈ 𝕎'_B} |T_B|`.

The three factors are the three losses hidden in GWZ's "summing over the `r₁`-balls"
(`gwz.txt` l.2210-2216), each paid exactly once:
* `δ^{2η}` is the aggregate density `Kakeya.VeryNotSticky.fullness_ge`, through
  `ShadedBody.sum_volumeReal_shade_eq_fullness_mul`: `δ^{2η} ∑|T| ≤ ∑|Y(T)|`;
* `C` is the refinement loss `Y'_mass` cleared of its inverse (`C ≥ 1` by
  `Kakeya.ThinCase.ThinBall.one_le_C` at any ball, `𝔅` being non-empty): `∑|Y(T)| ≤ C ∑|Y'(T)|`;
* `Cm · m` is the fibre count `Kakeya.VeryNotSticky.BallData.fibre`: at a point `x ∈ Y_B(T_B)`
  at most `Cm · m` tubes of `𝕋(T_B)` are shaded, so
  `∑_{T ∈ 𝕋(T_B)} |Y'(T) ∩ B̂| ≤ Cm · m · |Y_B(T_B)| ≤ Cm · m · |T_B|`
  (`MeasureTheory.sum_measure_le_mul_measure_of_card_le`).

Between them the bookkeeping is exact. `P_cover` (on `Y_g ⊇ Y'`) splits `Y'(T)` over the
pieces, `|Y'(T)| ≤ ∑_B |Y'(T) ∩ B̂|`. At a ball `B`, a tube `T` with `|Y'(T) ∩ B̂| > 0` has a
parent segment `T_B` (`parent`, its working shading meeting `B̂`); its shading in `B̂` lies in
`Y_B(T_B)` (`into`), hence — by the forward
compatibility — in `Y'_B(T_B)`, so `W(T_B) ∈ 𝕎'_B` by `shade_containment`: the parent is
*retained*. `fam_disjoint` makes the parent unique, whence
`∑_T |Y'(T) ∩ B̂| ≤ ∑_{T_B retained} ∑_{T ∈ 𝕋(T_B)} |Y'(T) ∩ B̂|`. Nothing beyond the fields of
`cfg`, of `bd` and of the `ThinBall`s is used; `P_disjoint` and `compat_backward` are not
needed. -/
theorem segment_mass_of_compat (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {C : NNReal}
    (Y' : cfg.ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ cfg.s, Y' i ⊆ bd.Yg i)
    (hmeas : ∀ i ∈ cfg.s, MeasurableSet (Y' i))
    (hYm : (C : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
      ∑ i ∈ cfg.s, volume (Y' i))
    (tb : ∀ B ∈ bd.bs, ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η))
    (hcompat : ∀ (B : bd.bι) (hB : B ∈ bd.bs), ∀ p ∈ bd.segs B, ∀ i ∈ bd.fam p,
      Y' i ∩ (bd.Y p).carrier ∩ bd.P B ⊆ ((tb B hB).Y' p).shade) :
    (cfg.δ : ENNReal) ^ (2 * cfg.η) *
        ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
      (C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) *
        ∑ B ∈ bd.bs.attach, ∑ p ∈ (bd.segs B.1).filter (fun p ↦ bd.blk p ∈ (tb B.1 B.2).bodies'),
          volume (bd.Y p).carrier := by
  classical
  -- Step 1: the aggregate density `fullness_ge`: `δ^{2η} ∑|T| ≤ ∑|Y(T)|`.
  have h1 : (cfg.δ : ENNReal) ^ (2 * cfg.η) *
      ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
      ∑ i ∈ cfg.s, volume (cfg.T i).shade := by
    have hfull := cfg.fullness_ge
    have heq := ShadedBody.sum_volumeReal_shade_eq_fullness_mul cfg.s
      (fun i ↦ (cfg.T i).toShadedBody)
    have hcoe : (cfg.δ : ENNReal) ^ (2 * cfg.η) =
        ((cfg.δ ^ (2 * cfg.η) : NNReal) : ENNReal) := by
      rw [ENNReal.coe_rpow_of_nonneg _ (by linarith [cfg.hη])]
    calc (cfg.δ : ENNReal) ^ (2 * cfg.η) * ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier
        ≤ (ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) : ENNReal) *
            ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier := by
          gcongr
          rw [hcoe]
          exact ENNReal.coe_le_coe.mpr hfull
      _ = ∑ i ∈ cfg.s, volume (cfg.T i).shade := heq.symm
  -- Step 2: the refinement `Y'_mass`, cleared of the inverse: `∑|Y(T)| ≤ C ∑|Y'(T)|`.
  obtain ⟨B₀, hB₀⟩ := bd.bs_nonempty
  have hC1 : (1 : NNReal) ≤ C := (tb B₀ hB₀).one_le_C
  have hC0 : (C : ENNReal) ≠ 0 := by
    have : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC1
    exact_mod_cast this.ne'
  have hCtop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h2 : ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
      (C : ENNReal) * ∑ i ∈ cfg.s, volume (Y' i) := by
    calc ∑ i ∈ cfg.s, volume (cfg.T i).shade
        = (C : ENNReal) * ((C : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
      _ ≤ (C : ENNReal) * ∑ i ∈ cfg.s, volume (Y' i) := by gcongr
  -- Step 3: `P_cover` splits each `Y'(T)` over the pieces `B̂`.
  have h3 : ∑ i ∈ cfg.s, volume (Y' i) ≤
      ∑ i ∈ cfg.s, ∑ B ∈ bd.bs, volume (Y' i ∩ bd.P B) := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    calc volume (Y' i) ≤ volume (⋃ B ∈ bd.bs, (Y' i ∩ bd.P B)) := by
          apply measure_mono
          intro x hx
          obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp (bd.P_cover i hi (hsub i hi hx))
          exact Set.mem_iUnion₂.mpr ⟨B, hB, hx, hxB⟩
      _ ≤ ∑ B ∈ bd.bs, volume (Y' i ∩ bd.P B) := measure_biUnion_finset_le _ _
  -- Step 4: at one ball, `parent`/`into`/`compat_forward`/`shade_containment` send every
  -- tube of positive mass in `B̂` to a retained parent segment, `fam_disjoint` makes the
  -- parents unique, and `fibre` bounds the fibre over each segment by `Cm · m`.
  have h4 : ∀ (B : bd.bι) (hB : B ∈ bd.bs), ∑ i ∈ cfg.s, volume (Y' i ∩ bd.P B) ≤
      (bd.Cm : ENNReal) * (bd.m : ENNReal) *
        ∑ p ∈ (bd.segs B).filter (fun p ↦ bd.blk p ∈ (tb B hB).bodies'),
          volume (bd.Y p).carrier := by
    intro B hB
    set R := (bd.segs B).filter (fun p ↦ bd.blk p ∈ (tb B hB).bodies') with hR
    have hRsub : R ⊆ bd.segs B := Finset.filter_subset _ _
    have hkey : ∀ i ∈ cfg.s, volume (Y' i ∩ bd.P B) ≠ 0 → i ∈ R.biUnion bd.fam := by
      intro i hi hne
      obtain ⟨x, hxY, hxP⟩ := nonempty_of_measure_ne_zero hne
      have hxT : x ∈ bd.Yg i := hsub i hi hxY
      obtain ⟨p, hp, hip⟩ := bd.parent B hB i hi ⟨x, hxT, hxP⟩
      have hxYp : x ∈ (bd.Y p).shade := bd.into B hB p hp i hip ⟨hxT, hxP⟩
      have hxY'p : x ∈ ((tb B hB).Y' p).shade :=
        hcompat B hB p hp i hip ⟨⟨hxY, (bd.Y p).shade_subset hxYp⟩, hxP⟩
      have hret : bd.blk p ∈ (tb B hB).bodies' :=
        ((tb B hB).shade_containment p hp x hxY'p).1
      rw [Finset.mem_biUnion]
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hret⟩, hip⟩
    have hdisj : (R : Set bd.σ).PairwiseDisjoint bd.fam :=
      (bd.fam_disjoint B hB).mono (Finset.coe_subset.mpr hRsub)
    have hseg : ∀ p ∈ R, ∑ i ∈ bd.fam p, volume (Y' i ∩ bd.P B) ≤
        (bd.Cm : ENNReal) * (bd.m : ENNReal) * volume (bd.Y p).carrier := by
      intro p hpR
      have hp : p ∈ bd.segs B := hRsub hpR
      have hA : ∀ i ∈ bd.fam p, MeasurableSet (Y' i ∩ bd.P B) := fun i hi ↦
        (hmeas i (bd.fam_subset B hB p hp hi)).inter (bd.P_measurable B hB)
      have hAF : ∀ i ∈ bd.fam p, Y' i ∩ bd.P B ⊆ (bd.Y p).shade := fun i hi x hx ↦
        bd.into B hB p hp i hi ⟨hsub i (bd.fam_subset B hB p hp hi) hx.1, hx.2⟩
      calc ∑ i ∈ bd.fam p, volume (Y' i ∩ bd.P B)
          ≤ (bd.Cm : ENNReal) * (bd.m : ENNReal) * volume (bd.Y p).shade := by
            refine sum_measure_le_mul_measure_of_card_le volume (bd.fam p) _ hA
              (bd.Y p).measurableSet_shade hAF ?_
            intro x hx
            refine le_trans ?_ (bd.fibre B hB p hp x hx).2
            refine Nat.cast_le.mpr (Finset.card_le_card ?_)
            -- the two filters carry different `Decidable` instances (the lemma's classical
            -- one and the field's), so `Finset.mem_filter` is applied with `@` on both sides
            intro i hi
            have hi' := (@Finset.mem_filter _ _ (_) _ _).mp hi
            exact (@Finset.mem_filter _ _ (_) _ _).mpr
              ⟨hi'.1, hsub i (bd.fam_subset B hB p hp hi'.1) hi'.2.1⟩
        _ ≤ (bd.Cm : ENNReal) * (bd.m : ENNReal) * volume (bd.Y p).carrier := by
            gcongr
            exact (bd.Y p).shade_subset
    calc ∑ i ∈ cfg.s, volume (Y' i ∩ bd.P B)
        = ∑ i ∈ cfg.s with volume (Y' i ∩ bd.P B) ≠ 0, volume (Y' i ∩ bd.P B) :=
          (Finset.sum_filter_ne_zero _).symm
      _ ≤ ∑ i ∈ R.biUnion bd.fam, volume (Y' i ∩ bd.P B) := by
          apply Finset.sum_le_sum_of_subset
          intro i hi
          rw [Finset.mem_filter] at hi
          exact hkey i hi.1 hi.2
      _ = ∑ p ∈ R, ∑ i ∈ bd.fam p, volume (Y' i ∩ bd.P B) := Finset.sum_biUnion hdisj
      _ ≤ ∑ p ∈ R, (bd.Cm : ENNReal) * (bd.m : ENNReal) * volume (bd.Y p).carrier :=
          Finset.sum_le_sum hseg
      _ = (bd.Cm : ENNReal) * (bd.m : ENNReal) * ∑ p ∈ R, volume (bd.Y p).carrier := by
          rw [Finset.mul_sum]
  -- Assembly.
  calc (cfg.δ : ENNReal) ^ (2 * cfg.η) * ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier
      ≤ ∑ i ∈ cfg.s, volume (cfg.T i).shade := h1
    _ ≤ (C : ENNReal) * ∑ i ∈ cfg.s, volume (Y' i) := h2
    _ ≤ (C : ENNReal) * ∑ i ∈ cfg.s, ∑ B ∈ bd.bs, volume (Y' i ∩ bd.P B) := by gcongr
    _ = (C : ENNReal) * ∑ B ∈ bd.bs.attach, ∑ i ∈ cfg.s, volume (Y' i ∩ bd.P B.1) := by
        rw [Finset.sum_comm,
          Finset.sum_attach bd.bs (fun B ↦ ∑ i ∈ cfg.s, volume (Y' i ∩ bd.P B))]
    _ ≤ (C : ENNReal) * ∑ B ∈ bd.bs.attach, ((bd.Cm : ENNReal) * (bd.m : ENNReal) *
          ∑ p ∈ (bd.segs B.1).filter (fun p ↦ bd.blk p ∈ (tb B.1 B.2).bodies'),
            volume (bd.Y p).carrier) := by
        gcongr with B hB
        exact h4 B.1 B.2
    _ = (C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) *
        ∑ B ∈ bd.bs.attach, ∑ p ∈ (bd.segs B.1).filter (fun p ↦ bd.blk p ∈ (tb B.1 B.2).bodies'),
          volume (bd.Y p).carrier := by
        rw [← Finset.mul_sum, ← mul_assoc, ← mul_assoc]

/-- **The thin-case configuration can be arranged, relative to `cfg`** (blueprint
`lem:ml2thinsetupexists`, `cfg`-relative form).

This is the form of blueprint `lem:ml2thinsetupexists` that the case-split assembly consumes:
its hypotheses are `cfg` together with the `cfg`-relative per-ball data of Configuration
`hyp:ml2setup` (`bd`), and its conclusion is that a
`Kakeya.VeryNotSticky.ThinConfig` over that very `bd` exists. The pair `(𝕋, Y)` recorded by
`cfg` is not modified: the shading `Y'` produced is auxiliary data attached to it.

It is intended to follow from `Kakeya.ThinCase.thinSetupExists`, whose hypotheses are the
fields of `bd` and whose conclusion is the tuple of fields of `ThinConfig`, with the
comparison constant `bd.Cg * Kakeya.ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ bd.D bd.Cm`:
that lemma runs on the *working* shading `bd.Yg` (its `Yg`, `hPcov`, `hparent`, `hinto`,
`hback`, `hfibre` are the (C5′)/(C5) fields of `bd`), so its refinement bound is against
`∑_T |Y_g(T)|`, and the loss `bd.Cg` of `Kakeya.VeryNotSticky.BallData.Yg_mass` is paid once to
reach `∑_T |Y(T)|`; the per-ball data are read at the larger
constant by `Kakeya.ThinCase.ThinBall.mono`. The remaining
inputs of that lemma are supplied by `cfg`: the chain `δ ≤ a ≤ b ≤ r₁` is `cfg.hdims`
(together with `Kakeya.VeryNotSticky.r₁`, which is `δ^{exscal}` by definition), and the
dimension is three.

**No thin-case hypothesis.** The blueprint statement is prefaced by the thin-case refinement
`a ≤ δ^{1-τ}`, but that hypothesis is used by none of (T1)–(T6) — as recorded in the docstring
of `Kakeya.ThinCase.thinSetupExists` — so carrying it here would leave a binder, and with it
the exponent `τ` that exists only to type it, unreferenced in the statement. The blueprint
records the thin-case regime in the prose of `hyp:ml2thinsetup` and in the case split that
invokes this lemma; the construction itself is unconditional, and is stated as such.

The segment-mass inequality (T7) is the one clause of Configuration `hyp:ml2thinsetup` that
`Kakeya.ThinCase.thinSetupExists` does not produce. It is nevertheless a *theorem* of the data
that lemma returns: `Kakeya.VeryNotSticky.segment_mass_of_compat` derives the field
`Kakeya.VeryNotSticky.ThinConfig.segment_mass` from the refined
shading `Y'` — its containment, measurability and mass bound — the per-ball
`Kakeya.ThinCase.ThinBall` family and the forward compatibility, together with the fields
`fullness_ge`, `P_cover`, `P_measurable`, `parent`/`into`, `fam_subset`/`fam_disjoint` and
`fibre` of `cfg` and `bd`. Accordingly this statement carries no hypothesis for (T7): the
former binder `hmass`, which only relocated the clause, is gone, and since pack F14 so is the consumer-dead pass-through `{mass}`/`hsegmass` of
`Kakeya.ThinCase.thinSetupExists`, which this proof used to instantiate at `mass = 0`.

No positivity hypothesis on `cfg.δ` is carried: `Kakeya.VeryNotSticky.hδ` already asserts
`0 < cfg.δ`, so a binder `hδ : 0 < cfg.δ` would be a duplicate of a field of `cfg`. -/
theorem exists_thinConfig (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    -- the `w₁` window of the corrected Proposition 5.1. It is *not* derivable from `BallData`:
    -- `bodies_thickness` and `bodies_w₁` together give only `cfg.δ ≤ 2 * bd.C₀ * bd.w₁`, and
    -- nothing bounds `bd.w₁` above by `1`. `bd.w₁` is a free field of `BallData`, so this is
    -- arrangeable by the construction that produces the `BallData`, but it is an assumption
    -- *relocated* here rather than discharged.
    (hδw₁ : cfg.δ ≤ bd.w₁) (hw₁one : bd.w₁ ≤ 1) :
    Nonempty (ThinConfig cfg bd) := by
  -- Ball-uniformity of the core envelope: one `Ccore` for all balls, obtained as the supremum
  -- over the (finitely many) balls of the canonical envelope
  -- `Kakeya.ThinCase.factoringApplyCore` at that ball. `bd.bs` is a `Finset`, so this is
  -- mechanical, and each per-ball bound follows from
  -- `Kakeya.ThinCase.factoringApplyCore_spec` composed with `Finset.le_sup`.
  -- The fifth envelope bound of `Kakeya.ThinCase.factoringApply` mentions `CF` and no ball, so
  -- it is adjoined to the supremum rather than absorbed into it. Enlarging `Ccore` is free:
  -- all five bounds are *lower* bounds on the parameter, and `Kakeya.VeryNotSticky.ThinConfig.C`
  -- is existentially quantified data with no upper bound field. The adjoined term is
  -- `⌊log₂ ⌈CF⌉⌋ + 1`, a constant in `δ`, so the `⪅ 1` budget of
  -- `Kakeya.ThinCase.factoringApplyCore_leApprox_one` is not disturbed.
  -- The envelope is taken at the *discretization* scale `cfg.δ / bd.C₀` of the segments, not at
  -- `cfg.δ`: `Kakeya.ThinCase.factoringApply` runs the Proposition 5.1 pipeline at the scale at
  -- which `BallData.segs_thickness` discretizes the segments, and that is `cfg.δ / bd.C₀`. Both
  -- pipeline losses are antitone in the scale. Rather than rely on that antitonicity, the
  -- envelope below is the maximum of the two evaluations, which discharges the four
  -- `cfg.δ`-bounds and the two `cfg.δ / bd.C₀`-bounds from one supremum with no monotonicity
  -- lemma. Enlarging `Ccore` is free, all six bounds being *lower* bounds on the parameter.
  let Ccore : NNReal := max
    (max (max (((Nat.log 2 ⌈bd.CF⌉₊ + 1 : ℕ) : NNReal))
        (ThinCase.ballNetLoss 3 ((bd.w₁ : ℝ) / 8) 2))
      -- the strengthened `hCcoreNet` term: `Kakeya.ThinCase.thinEnvelopeTerm` prices conjuncts
      -- (iv) and (vi) of `Kakeya.ThinCase.factoringApply`, and is per-ball because
      -- `thinRetentionLoss` reads the two cardinalities
      (bd.bs.sup fun B =>
        ThinCase.thinEnvelopeTerm 3 (bd.segs B).card (bd.bodies B).card bd.CF bd.w₁))
    (bd.bs.sup fun B => max
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card cfg.δ)
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card (cfg.δ / bd.C₀)))
  have hcore_le : ∀ B ∈ bd.bs,
      ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card cfg.δ ≤ Ccore :=
    fun B hB => le_trans (le_trans (le_max_left _ _) (Finset.le_sup (f := fun B => max
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card cfg.δ)
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card (cfg.δ / bd.C₀))) hB))
      (le_max_right _ _)
  have hcore_le₀ : ∀ B ∈ bd.bs,
      ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card (cfg.δ / bd.C₀)
        ≤ Ccore :=
    fun B hB => le_trans (le_trans (le_max_right _ _) (Finset.le_sup (f := fun B => max
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card cfg.δ)
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card (cfg.δ / bd.C₀))) hB))
      (le_max_right _ _)
  have hCcoreRef₀ : ∀ B ∈ bd.bs,
      (ShadedBody.outerFactoringFamily_refinement.c 3 (bd.segs B).card (cfg.δ / bd.C₀))⁻¹
        ≤ Ccore :=
    fun B hB => le_trans (ThinCase.inv_refinement_c_le_factoringApplyCore _ _ _ _)
      (hcore_le₀ B hB)
  have hCcoreMult₀ : ∀ B ∈ bd.bs,
      ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 (bd.bodies B).card
        (cfg.δ / bd.C₀) ≤ Ccore :=
    fun B hB => le_trans (ThinCase.outerConstMultFat_c_le_factoringApplyCore _ _ _ _)
      (hcore_le₀ B hB)
  have hCcoreFrost : ((Nat.log 2 ⌈bd.CF⌉₊ + 1 : ℕ) : NNReal) ≤ Ccore :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  -- **the strengthened `hCcoreNet`, discharged by the compiler and not asserted**
  have hCcoreNet : ∀ B ∈ bd.bs,
      ThinCase.thinEnvelopeTerm 3 (bd.segs B).card (bd.bodies B).card bd.CF bd.w₁ ≤ Ccore :=
    fun B hB => le_trans
      (Finset.le_sup (f := fun B =>
        ThinCase.thinEnvelopeTerm 3 (bd.segs B).card (bd.bodies B).card bd.CF bd.w₁) hB)
      (le_trans (le_max_right _ _) (le_max_left _ _))
  have hCcore2 : (2 : NNReal) ≤ Ccore := by
    obtain ⟨B₀, hB₀⟩ := bd.bs_nonempty
    exact le_trans (ThinCase.two_le_factoringApplyCore _ _ _ _) (hcore_le B₀ hB₀)
  have hCcoreRef : ∀ B ∈ bd.bs,
      (ShadedBody.outerFactoringFamily_refinement.c 3 (bd.segs B).card cfg.δ)⁻¹ ≤ Ccore :=
    fun B hB => le_trans (ThinCase.inv_refinement_c_le_factoringApplyCore _ _ _ _)
      (hcore_le B hB)
  have hCcoreMult : ∀ B ∈ bd.bs,
      ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 (bd.bodies B).card cfg.δ ≤ Ccore :=
    fun B hB => le_trans (ThinCase.outerConstMultFat_c_le_factoringApplyCore _ _ _ _)
      (hcore_le B hB)
  have hCcoreDyad : ∀ B ∈ bd.bs,
      ((Nat.log 2 (bd.bodies B).card + 1 : ℕ) : NNReal) ≤ Ccore :=
    fun B hB => le_trans (ThinCase.natLog_le_factoringApplyCore _ _ _ _) (hcore_le B hB)
  let C : NNReal := ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ Ccore bd.D bd.Cm
  have hbr₁ : cfg.b ≤ cfg.r₁ := by simpa [r₁] using cfg.hdims.2.2
  -- The localisation of the bodies, which `Kakeya.ThinCase.factoringApply` — and hence
  -- `Kakeya.ThinCase.perBall` and `Kakeya.ThinCase.thinSetupExists` — needs and which the
  -- refutations `Kakeya.ThinCase.Refute.factoringApply_refuted` and
  -- `Kakeya.ThinCase.PerBallRefute.perBall_refuted` show cannot be dispensed with. It is
  -- *available here*: the bodies of a ball lie in that ball, whose radius `r₁ = δ^exscal` is
  -- at most `1` because `δ ≤ 1` and `exscal > 0`.
  have hr₁one : cfg.r₁ ≤ 1 := by
    rw [r₁]
    exact NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le
  have hloc : ∀ B ∈ bd.bs, ∃ z : EuclideanSpace ℝ (Fin 3),
      ∀ j ∈ bd.bodies B, (bd.Wb j).carrier ⊆ closedBall z 1 := by
    intro B hB
    refine ⟨bd.ctr B, fun j hj => ?_⟩
    refine (bd.bodies_subset_ball B hB j hj).trans (Metric.closedBall_subset_closedBall ?_)
    exact_mod_cast hr₁one
  have hD : 1 ≤ bd.D := by
    rcases bd.bs_nonempty with ⟨B, hBbs⟩
    have hr₁ : (0 : ℝ) < (cfg.r₁ : ℝ) := NNReal.coe_pos.mpr (NNReal.rpow_pos cfg.hδ)
    have hx : bd.ctr B ∈ ball (bd.ctr B) (cfg.r₁ : ℝ) := by
      rw [mem_ball, dist_self]
      exact hr₁
    have hcard := bd.ballOverlap (bd.ctr B) ({B} : Finset bd.bι)
      (by intro t ht; rw [Finset.mem_singleton] at ht; subst ht; exact hBbs)
      (by intro B' hB'; rw [Finset.mem_singleton] at hB'; subst hB'; exact hx)
    simpa using hcard
  rcases ThinCase.thinSetupExists (E := EuclideanSpace ℝ (Fin 3))
      (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
      (I := cfg.s) (Yg := bd.Yg)
      (hYgmeas := bd.Yg_measurable)
      (bs := bd.bs) (P := bd.P)
      (hPdisj := bd.P_disjoint) (hPmeas := bd.P_measurable) (hPcov := bd.P_cover)
      (segs := bd.segs) (Y := bd.Y) (fam := bd.fam)
      (hsegs := bd.segs_nonempty) (hfam := bd.fam_subset) (hfam_disj := bd.fam_disjoint)
      (hYb_piece := bd.Y_piece)
      (bodies := bd.bodies) (Wb := bd.Wb) (blk := bd.blk)
      (δ := cfg.δ) (a := cfg.a) (b := cfg.b) (r₁ := cfg.r₁) (w₁ := bd.w₁)
      (η := 2 * cfg.η) (C₀ := bd.C₀) (CF := bd.CF) (c₁ := bd.c₁) (D := bd.D)
      (hC₀ := bd.hC₀) (hCF := bd.hCF) (hc₁ := bd.hc₁) (hD := hD)
      (hδ := cfg.hδ) (hδa := cfg.hdims.1) (hab := cfg.hdims.2.1) (hbr₁ := hbr₁)
      (hδw₁ := hδw₁) (hw₁one := hw₁one) (hη := mul_nonneg (by norm_num) cfg.hη.le) (hloc := hloc)
       (Ccore := Ccore) (hCcore2 := hCcore2)
      (hCcoreRef := hCcoreRef) (hCcoreMult := hCcoreMult) (hCcoreDyad := hCcoreDyad)
      (hCcoreFrost := hCcoreFrost) (hCcoreNet := hCcoreNet)
      (hCcoreRef₀ := hCcoreRef₀) (hCcoreMult₀ := hCcoreMult₀)
      (hblk := bd.blk_mem) (hle := bd.segs_le) (hthick := bd.segs_thickness)
      (hdims := bd.segs_dims) (hbody := bd.bodies_thickness) (hw₁ := bd.bodies_w₁)
      (hFr := bd.frostman)
      (hdens := bd.segs_density) (hparent := bd.parent) (hinto := bd.into) (hback := bd.back)
      (m := bd.m) (Cm := bd.Cm) (hCm := bd.hCm) (hfibre := bd.fibre)
      (γ := bd.γ) (cov := bd.cov) (covCtr := bd.covCtr)
      (hcov := bd.cov_isCover) (hcovMeets := bd.cov_meets)
    with ⟨Y', hsub, hmeas, hYm, tb, hcompat⟩
  -- The loss `Cg` of the working shading against `Y` (`BallData.Yg_mass`) joins the comparison
  -- constant: `thinSetupExists` refines `Y_g`, and `(Cg · C)⁻¹ ∑|Y| ≤ C⁻¹ ∑|Y_g| ≤ ∑|Y'|`.
  -- The per-ball data are read at the larger constant by `ThinBall.mono`, which passes `Y'_B`
  -- and `𝕎'_B` through unchanged, so the compatibility clauses transport verbatim.
  have hCle : C ≤ bd.Cg * C := le_mul_of_one_le_left zero_le bd.hCg
  let tb' : ∀ B ∈ bd.bs, ThinCase.ThinBall (bd.Cg * C) bd.C₀ (bd.segs B) bd.Y (bd.bodies B)
      bd.Wb bd.blk cfg.δ cfg.a (2 * cfg.η) :=
    fun B hB ↦ ThinCase.ThinBall.mono hCle (tb B hB)
  have hYm' : ((bd.Cg * C : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
      ∑ i ∈ cfg.s, volume (Y' i) := by
    calc ((bd.Cg * C : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade
        = (C : ENNReal)⁻¹ * ((bd.Cg : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade) := by
          rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top)
            (Or.inl ENNReal.coe_ne_top), mul_comm (bd.Cg : ENNReal)⁻¹, mul_assoc]
      _ ≤ (C : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (bd.Yg i) := by
          gcongr
          exact bd.Yg_mass
      _ ≤ ∑ i ∈ cfg.s, volume (Y' i) := hYm
  exact ⟨⟨bd.Cg * C, Y', hsub, hmeas, hYm', tb',
      fun B hB p hp i hi ↦ (hcompat B hB).1 p hp i hi,
      fun B hB p hp ↦ (hcompat B hB).2 p hp,
      segment_mass_of_compat cfg bd Y' hsub hmeas hYm' tb'
        fun B hB p hp i hi ↦ (hcompat B hB).1 p hp i hi⟩⟩

/-! ### Positivity at a thin ball

Blueprint `lem:ml2thinBallPositivity`. Every quotient taken at a ball of the thin case —
the fullness `λ(𝕎'_B, Y_{𝕎'_B})`, the multiplicity `μ(𝕎'_B, Y_{𝕎'_B})` and their
counterparts at a refinement — needs its denominator to be positive, and the lemmas below
are where that comes from. They are stated here, with Configuration `hyp:ml2setup` and
Configuration `hyp:ml2thinsetup`, rather than in the tangential file, because they are about
the configuration alone.
-/

/-- **Every factoring body has positive volume** (blueprint `lem:ml2thinBallPositivity`(i)).

By (C4) each `W ∈ 𝕎_B` has affine thicknesses `∼ (r₁, b, a)` with the constant `bd.C₀`, and
`a ≥ δ > 0` by `cfg.hdims` and `cfg.hδ`, so `|W| ≳ r₁ b a > 0` by
`Convex.prod_thickness_le_volumeReal`. Consequently `∑_{W ∈ 𝒱} |W| > 0` for every nonempty
`𝒱 ⊆ 𝕎_B`, a finite sum of nonnegative terms with a positive one. -/
theorem volume_body_pos (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {j : bd.ω} (hj : j ∈ bd.bodies B) : 0 < volume (bd.Wb j).carrier := by
  have hthick : HasThicknesses (bd.Wb j).carrier bd.C₀ ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] :=
    bd.bodies_thickness B hB j hj
  have hconv : Convex ℝ (bd.Wb j).carrier := (bd.Wb j).convex
  have hbdd : Bornology.IsBounded (bd.Wb j).carrier := (bd.Wb j).isCompact.isBounded
  have hr₁ : (0 : ℝ) < (cfg.r₁ : ℝ) := NNReal.coe_pos.mpr (NNReal.rpow_pos cfg.hδ)
  have hapos : (0 : ℝ) < (cfg.a : ℝ) :=
    NNReal.coe_pos.mpr (lt_of_lt_of_le cfg.hδ cfg.hdims.1)
  have hbpos : (0 : ℝ) < (cfg.b : ℝ) :=
    NNReal.coe_pos.mpr (lt_of_lt_of_le (lt_of_lt_of_le cfg.hδ cfg.hdims.1) cfg.hdims.2.1)
  have hC₀pos : (0 : ℝ) < (bd.C₀ : ℝ) :=
    lt_of_lt_of_le (by norm_num) (NNReal.coe_le_coe.2 bd.hC₀)
  have hthick_ne_zero : ∀ i ∈ Finset.range (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
      Metric.ethickness ℝ (bd.Wb j).carrier i ≠ 0 := by
    intro i hi
    rw [Finset.mem_range, finrank_euclideanSpace_fin] at hi
    let k : Fin 3 := ⟨i, hi⟩
    rcases hthick k with ⟨hle, _⟩
    have h_val_pos : 0 < (![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k) := by
      match k with
      | 0 => simp [hr₁]
      | 1 => simp [hbpos]
      | 2 => simp [hapos]
    have hle' : (bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k) ≤
        Metric.thickness ℝ (bd.Wb j).carrier (k : ℕ) := by
      simpa using hle
    have hprodpos : 0 < (bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k) :=
      mul_pos (inv_pos.mpr hC₀pos) h_val_pos
    have hpos : 0 < Metric.thickness ℝ (bd.Wb j).carrier (k : ℕ) := by linarith
    rw [Metric.ethickness_thickness' hbdd k.val]
    rw [ENNReal.ofReal_ne_zero_iff]
    simpa [k] using hpos
  exact hconv.volume_pos_of_ethickness_ne_zero hthick_ne_zero

/-- **Every tube segment has positive volume.** The segment analogue of
`Kakeya.VeryNotSticky.volume_body_pos`: by (C3) each `T_B ∈ 𝕋_B` has affine thicknesses
`∼ (r₁, δ, δ)` with the constant `bd.C₀`, and `δ > 0`, so `|T_B| ≳ r₁ δ² > 0`. -/
theorem volume_segs_pos (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {p : bd.σ} (hp : p ∈ bd.segs B) : 0 < volume (bd.Y p).carrier := by
  have hthick : HasThicknesses (bd.Y p).carrier bd.C₀
      ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] := bd.segs_thickness B hB p hp
  have hconv : Convex ℝ (bd.Y p).carrier := (bd.Y p).convex
  have hbdd : Bornology.IsBounded (bd.Y p).carrier := (bd.Y p).isCompact.isBounded
  have hr₁ : (0 : ℝ) < (cfg.r₁ : ℝ) := NNReal.coe_pos.mpr (NNReal.rpow_pos cfg.hδ)
  have hδpos : (0 : ℝ) < (cfg.δ : ℝ) := NNReal.coe_pos.mpr cfg.hδ
  have hC₀pos : (0 : ℝ) < (bd.C₀ : ℝ) :=
    lt_of_lt_of_le (by norm_num) (NNReal.coe_le_coe.2 bd.hC₀)
  have hthick_ne_zero : ∀ i ∈ Finset.range (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
      Metric.ethickness ℝ (bd.Y p).carrier i ≠ 0 := by
    intro i hi
    rw [Finset.mem_range, finrank_euclideanSpace_fin] at hi
    let k : Fin 3 := ⟨i, hi⟩
    rcases hthick k with ⟨hle, _⟩
    have h_val_pos : 0 < (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) := by
      match k with
      | 0 => simp [hr₁]
      | 1 => simp [hδpos]
      | 2 => simp [hδpos]
    have hle' : (bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) ≤
        Metric.thickness ℝ (bd.Y p).carrier (k : ℕ) := by
      simpa using hle
    have hprodpos : 0 < (bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) :=
      mul_pos (inv_pos.mpr hC₀pos) h_val_pos
    have hpos : 0 < Metric.thickness ℝ (bd.Y p).carrier (k : ℕ) := by linarith
    rw [Metric.ethickness_thickness' hbdd k.val]
    rw [ENNReal.ofReal_ne_zero_iff]
    simpa [k] using hpos
  exact hconv.volume_pos_of_ethickness_ne_zero hthick_ne_zero

/-- **Every tube segment has a parent tube.** By (C5) the shading of a segment has positive
measure (`bd.segs_density` with `0 < bd.c₁`, `0 < cfg.δ` and
`Kakeya.VeryNotSticky.volume_segs_pos`), and by (C5) again it is covered by the shadings of the
tubes of its family `𝕋(T_B)`; so that family is nonempty. -/
theorem fam_nonempty (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {p : bd.σ} (hp : p ∈ bd.segs B) : (bd.fam p).Nonempty := by
  have hcar : 0 < volume (bd.Y p).carrier := volume_segs_pos cfg bd hB hp
  have hc₁ : (0 : ENNReal) < (bd.c₁ : ENNReal) := ENNReal.coe_pos.mpr bd.hc₁
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by
    simpa using (ne_of_gt cfg.hδ)
  have hrpow : (0 : ENNReal) < (cfg.δ : ENNReal) ^ (2 * cfg.η) :=
    ENNReal.rpow_pos (pos_of_ne_zero hδ0) (by exact ENNReal.coe_ne_top)
  have hprod : (0 : ENNReal) < (bd.c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
      volume (bd.Y p).carrier := by
    exact ENNReal.mul_pos (ENNReal.mul_pos hc₁.ne' hrpow.ne').ne' hcar.ne'
  have hshade : 0 < volume (bd.Y p).shade :=
    lt_of_lt_of_le hprod (bd.segs_density B hB p hp)
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hshade.ne'
  have hmem := bd.back B hB p hp hx
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨i, hi, -⟩ := hmem
  exact ⟨i, hi⟩

/-- **A ball carries at most as many segments as there are tubes.**

This is the reduction that makes the cardinality hypothesis of
`Kakeya.ThinCase.factoringApplyCore_leApprox_one` — the budget check for the repaired
`Kakeya.ThinCase.factoringApply` — available inside the configuration, *without* adding a field
to `Kakeya.ThinCase.IsBallFactoring` or to `Kakeya.VeryNotSticky.BallData`: the families
`𝕋(T_B)` are pairwise disjoint, nonempty (`Kakeya.VeryNotSticky.fam_nonempty`) and contained in
`𝕋`, so they inject the segments of the ball into the tubes.

What remains of the hypothesis `|𝕋_B| ≤ δ^{-K}` after this reduction is `|𝕋| ≤ δ^{-K}`, a
property of the `Kakeya.VeryNotSticky` tube family alone — the tubes are `δ`-separated in
directions inside the unit ball — and no longer of the per-ball factoring data. -/
theorem card_segs_le_card_tubes (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) : (bd.segs B).card ≤ cfg.s.card := by
  classical
  have hdisj : ∀ p ∈ bd.segs B, ∀ q ∈ bd.segs B, p ≠ q →
      Disjoint (bd.fam p) (bd.fam q) := fun p hp q hq hpq =>
    bd.fam_disjoint B hB hp hq hpq
  calc (bd.segs B).card = ∑ _p ∈ bd.segs B, 1 := by simp
    _ ≤ ∑ p ∈ bd.segs B, (bd.fam p).card :=
        Finset.sum_le_sum fun p hp => (fam_nonempty cfg bd hB hp).card_pos
    _ = ((bd.segs B).biUnion bd.fam).card := (Finset.card_biUnion hdisj).symm
    _ ≤ cfg.s.card := by
        refine Finset.card_le_card ?_
        intro i hi
        rw [Finset.mem_biUnion] at hi
        obtain ⟨p, hp, hip⟩ := hi
        exact bd.fam_subset B hB p hp hip

/-! #### Positivity at a `c`-refinement of `(𝕎'_B, Y_{𝕎'_B})`

Blueprint `lem:ml2thinBallPositivity`(ii)–(iii) records four separate positivity facts about a
`c`-refinement `(𝕎''_B, Y_{𝕎''_B})` of `(𝕎'_B, Y_{𝕎'_B})`, and in Lean each is its own
declaration — as for the sibling group `tangentialDenseSlabs_*` of blueprint
`lem:ml2tangentialDenseSlabs` — since the consumers use them one at a time and a conjunction
would force each to be projected out.

The four share the hypotheses `hc : 0 < c` and `href`, so they share a `variable` block. Part
(ii) of the blueprint — the same four conclusions for `(𝕎'_B, Y_{𝕎'_B})` itself — is the
instance `s' = (tc.thinBall hB).bodies'`, `W' = (tc.thinBall hB).W`, `c = 1`, where the
`c`-refinement hypothesis is the reflexive one; so parts (ii) and (iii) are the same four
statements read at two instances.

The common source of the mass bounds is (T2), `ThinCase.ThinBall.fullness_bodies`, which
bounds the fullness of `(𝕎'_B, Y_{𝕎'_B})` below by `C⁻¹ δ^{2η} > 0`: with the convention that
a quotient by `0` is `0`, a positive fullness forces both its numerator and its denominator to
be positive, and the `c`-refinement then keeps a `c`-fraction of the mass. The volume bound is
`Kakeya.VeryNotSticky.volume_body_pos`, the bodies of a refinement being bodies of `𝕎_B`.
-/

section ThinBallPositivity

variable (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι}
  (hB : B ∈ bd.bs) {c : NNReal} {s' : Finset bd.ω}
  {W' : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))}

/-- **A refinement at a thin ball is nonempty** (blueprint `lem:ml2thinBallPositivity`(ii)–(iii),
first conclusion). -/
theorem thinBallPositivity_nonempty (hc : 0 < c)
    (href : ShadedBody.IsCRefinement s' W' (tc.thinBall hB).bodies' (tc.thinBall hB).W c) :
    s'.Nonempty := by
  classical
  let tb := tc.thinBall hB
  have hδposE : (0 : ENNReal) < (cfg.δ : ENNReal) := ENNReal.coe_pos.mpr cfg.hδ
  have hδtopE : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hpowpos : (0 : ENNReal) < (cfg.δ : ENNReal) ^ (3 * (2 * cfg.η)) :=
    ENNReal.rpow_pos hδposE hδtopE
  have hCprod : (0 : ENNReal) <
      (tc.C : ENNReal) * (ShadedBody.fullness tb.bodies' tb.W : ENNReal) :=
    lt_of_lt_of_le hpowpos tb.fullness_bodies
  have hFpos : (0 : ENNReal) < (ShadedBody.fullness tb.bodies' tb.W : ENNReal) :=
    (ENNReal.mul_pos_iff.mp hCprod).2
  have hSne0 : (∑ j ∈ tb.bodies', volume (tb.W j).shade) ≠ 0 := by
    rw [ShadedBody.fullness_def tb.bodies' tb.W] at hFpos
    exact (ENNReal.div_pos_iff.mp hFpos).1
  have hcne0 : (c : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hc)
  have hcmul : (0 : ENNReal) < (c : ENNReal) * (∑ j ∈ tb.bodies', volume (tb.W j).shade) :=
    ENNReal.mul_pos hcne0 hSne0
  have hshade_pos : 0 < ∑ j ∈ s', volume (W' j).shade := lt_of_lt_of_le hcmul href.2
  by_contra hne
  have hs' : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  rw [hs'] at hshade_pos
  simp at hshade_pos

/-- **The shaded mass of a refinement at a thin ball is positive** (blueprint
`lem:ml2thinBallPositivity`(ii)–(iii), second conclusion). -/
theorem thinBallPositivity_shade_pos (hc : 0 < c)
    (href : ShadedBody.IsCRefinement s' W' (tc.thinBall hB).bodies' (tc.thinBall hB).W c) :
    0 < ∑ j ∈ s', volume (W' j).shade := by
  classical
  let tb := tc.thinBall hB
  have hδposE : (0 : ENNReal) < (cfg.δ : ENNReal) := ENNReal.coe_pos.mpr cfg.hδ
  have hδtopE : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hpowpos : (0 : ENNReal) < (cfg.δ : ENNReal) ^ (3 * (2 * cfg.η)) :=
    ENNReal.rpow_pos hδposE hδtopE
  have hCprod : (0 : ENNReal) <
      (tc.C : ENNReal) * (ShadedBody.fullness tb.bodies' tb.W : ENNReal) :=
    lt_of_lt_of_le hpowpos tb.fullness_bodies
  have hFpos : (0 : ENNReal) < (ShadedBody.fullness tb.bodies' tb.W : ENNReal) :=
    (ENNReal.mul_pos_iff.mp hCprod).2
  have hSne0 : (∑ j ∈ tb.bodies', volume (tb.W j).shade) ≠ 0 := by
    rw [ShadedBody.fullness_def tb.bodies' tb.W] at hFpos
    exact (ENNReal.div_pos_iff.mp hFpos).1
  have hcne0 : (c : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hc)
  have hcmul : (0 : ENNReal) < (c : ENNReal) * (∑ j ∈ tb.bodies', volume (tb.W j).shade) :=
    ENNReal.mul_pos hcne0 hSne0
  exact lt_of_lt_of_le hcmul href.2

/-- **The total volume of a refinement at a thin ball is positive** (blueprint
`lem:ml2thinBallPositivity`(ii)–(iii), third conclusion). -/
theorem thinBallPositivity_carrier_pos (hc : 0 < c)
    (href : ShadedBody.IsCRefinement s' W' (tc.thinBall hB).bodies' (tc.thinBall hB).W c) :
    0 < ∑ j ∈ s', volume (W' j).carrier := by
  obtain ⟨j, hj⟩ := thinBallPositivity_nonempty cfg tc hB hc href
  have hposW : 0 < volume ((tc.thinBall hB).W j).carrier :=
    (tc.thinBall hB).volume_W_pos
      (fun i hi => volume_body_pos cfg bd hB ((tc.thinBall hB).bodies'_subset hi)) j
      (href.1.1 hj)
  have hce : (W' j).carrier = ((tc.thinBall hB).W j).carrier :=
    congrArg (fun B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) => B.carrier)
      (href.1.2 j hj).1
  have hpos : 0 < volume (W' j).carrier := by
    rw [hce]
    exact hposW
  have hle : volume (W' j).carrier ≤ ∑ i ∈ s', volume (W' i).carrier :=
    Finset.single_le_sum (f := fun i => volume (W' i).carrier)
      (fun i _ => by positivity) hj
  exact lt_of_lt_of_le hpos hle

/-- **The shaded union of a refinement at a thin ball has positive measure** (blueprint
`lem:ml2thinBallPositivity`(ii)–(iii), fourth conclusion). -/
theorem thinBallPositivity_iUnionShade_pos (hc : 0 < c)
    (href : ShadedBody.IsCRefinement s' W' (tc.thinBall hB).bodies' (tc.thinBall hB).W c) :
    0 < volume (ShadedBody.iUnionShade s' W') := by
  have hshade : 0 < ∑ j ∈ s', volume (W' j).shade :=
    thinBallPositivity_shade_pos cfg tc hB hc href
  have hne : (∑ j ∈ s', volume (W' j).shade) ≠ 0 := ne_of_gt hshade
  rcases Finset.exists_ne_zero_of_sum_ne_zero (s := s')
    (f := fun j => volume (W' j).shade) hne with ⟨j, hj, hjne⟩
  have hmono : volume (W' j).shade ≤ volume (ShadedBody.iUnionShade s' W') := by
    exact measure_mono (Finset.subset_set_biUnion_of_mem (s := s')
      (f := fun j => (W' j).shade) hj)
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hjne) hmono

end ThinBallPositivity

end Kakeya.VeryNotSticky
