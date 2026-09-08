/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallDataGeneral
public import Kakeya.DimensionThree.MainLemma2.BallLossCardScale

/-!
# The general-`(a, b)` branch's producer of conjunct 1 — and the one clause it cannot reach

The target is
`Kakeya.VeryNotSticky.BallDataGeneralTarget`. This file
runs the general branch end to end from the existing API and delivers **every clause of that
target except the margin**, together with the margin under the guard the construction would
need — and with the exact geometric form of the gap compiled.

## What is delivered

`Kakeya.VeryNotSticky.eventually_ballDataGeneral_except_margin` has, character for character,
`BallDataGeneralTarget`'s hypothesis block (with `Cbias`, `CF`, `Cdil` pinned to the values
Lemma 9.2 and T3 actually produce) and `BallDataGeneralTarget`'s conclusion with its last
conjunct — the margin

```
∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
  cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆ closedBall (bd.ctr B) r₁
```

— replaced by the three conjuncts

* the **sharp localisation** `(bd.Wb j).carrier ⊆ closedBall (bd.ctr B) (11 r₁/16)`;
* the **thickness profile** `HasThicknesses (bd.Wb j).carrier C₀bd ![r₁, b, a]` at the
  *unchanged* constant `C₀bd`;
* the **guarded margin** `C₀bd · a ≤ 5 r₁/16 → (the margin)`.

The tripwire `example` below records mechanically that these are the *only* differences: fed
the margin unguarded, the statement **is** `BallDataGeneralTarget`.

## Why the guard cannot be discharged here

In the general branch `a` is the output of
the dimensions pigeonhole `Kakeya.VeryNotSticky.exists_dimsClass_core`, whose only bounds are
`δ ≤ a ≤ b ≤ r₁`; at the top of that range the guard is false for every `C₀bd ≥ 4`
(`Kakeya.VeryNotSticky.not_margin_guard_at_top_of_dims_range`).

The gap is geometric, not a missing estimate, and this file compiles its exact form:

* `Kakeya.VeryNotSticky.dist_add_scale_le_of_margin` — the margin *forces*
  `dist x (ctr B) + (Wb j).scale ≤ r₁` for **every** point `x` of the body. So the margin is
  equivalent to "circumradius about the ball's centre plus scale at most `r₁`".
* `Kakeya.VeryNotSticky.scale_le_of_subset_closedBall` — the localisation gives
  `scale ≤ 11 r₁/16`, and `11/16 > 5/16`, so the localisation alone never closes it. The
  obstruction is structural: T3's capsule (`Kakeya.VeryNotSticky.segBodyOfCover`, half-length
  `L = r₁/4`) reaches `2L = r₁/2` from the ball centre in the worst window placement, so the
  localisation radius `R = 2L + 2δ + ρ` always exceeds `r₁/2`, whence `2R > r₁` and the
  crude route `R + scale ≤ 2R ≤ r₁` is unavailable at *any* scale.
* `Kakeya.VeryNotSticky.margin_of_scale_le` — the sharp sufficient form: `scale ≤ 5 r₁/16`.

## The route, and what each step costs

1. `Kakeya.VeryNotSticky.exists_core_localised_of_cover` — `exists_core_segsDensity_of_cover`
   (GWZ §9.3 steps 5–6) with two extra conclusions the consumers need and the existing capstone
   does not expose: the localisation `Localised (11 r₁/16)` and the cardinality bound
   `#𝕋_B ≤ #𝕋`.
2. `Kakeya.VeryNotSticky.exists_ballFactoring_glued_localised` — the per-ball → global gluing
   of `exists_ballFactoring_glued`, run through
   `Kakeya.VeryNotSticky.exists_ballFactoring_core_ball_inhab` so that `bodies_subset_ball`
   comes out at the *strengthened* radius. The existing gluing runs the `r₁`-radius form and so
   cannot see the margin at all.
3. Lemma 9.2's ball-dependent loss is uniformised by
   `Kakeya.VeryNotSticky.L_le_uniformLossBound` at `N = #𝕋` and turned into shade retention by
   `Kakeya.VeryNotSticky.shade_retention_of_carrier_retention` (factor `2`); the tier is cut by
   `Kakeya.VeryNotSticky.tierCore`.
4. `Kakeya.VeryNotSticky.exists_dimsClass_core` fixes `(a, b, w₁)` and deletes balls; the loss
   is `Kakeya.VeryNotSticky.dimsClassLoss`, paid by `BallDataCore.restrictBalls`.
5. `Kakeya.VeryNotSticky.BallDataCore.withDims` transports and
   `Kakeya.VeryNotSticky.BallDataCore.toBallData` assembles.

`bd.Cg = 4 · tierRetention · uniformLossBound · dimsClassLoss` and each of the four factors is
absorbed at `εg/4` by a existing absorber, so `bd.Cg ≤ δ^{-εg}` for every `εg > 0`. The
`w₁` window comes from `three_halves_mul_lemma92Constant_le` at `ϱ ≤ 1/21`
(`caseParams_ϱ_le_one_div_21`), and `dimsConstant_eq_left_of_lemma92` is what keeps
`bd.C₀ = C₀bd`.

## Essential distinctness

Nothing in this file consumes an essential-distinctness hypothesis: the whole route is
ED-free, corroborating  G5-H6 and . The ED binder the Blueprinter
compiled (`BP264.exists_core_edSegments_of_cover`) is *not* taken here: its fibre-budget shape
`Cm · m ≤ δ^{-(η + 2 exscal)}` is now exactly the re-cut contract's SP-H, but it still needs `SharpCapsuleAlignment`, which `BallCoreEDSharpObstruction.lean`
refutes, and its `Cm` is the class multiplicity, not the contract's `bd.Cm = 1`.  The general
branch's ED-degree clause is instead produced by the canonical-capsule core
(`CanonicalCapsulesProducer.lean`, `ballDataGeneralTarget_edDegree`).

Nothing existing changes: every declaration here is new.
-/

@[expose] public section

open MeasureTheory Metric Set Filter ShadedBody
open scoped NNReal ENNReal Topology

universe u

namespace Kakeya.VeryNotSticky

open Kakeya

/-! ### The core of GWZ §9.3 steps 5–6, with the localisation and the segment count -/

open scoped Classical in
/-- **`Kakeya.VeryNotSticky.exists_core_segsDensity_of_cover` with the two conclusions the
general branch's next two steps need.**

The existing capstone hides its construction behind an existential, so neither the localisation
of T3's capsules (`Kakeya.VeryNotSticky.localised_ballDataCoreOfCover`, needed by
`Kakeya.VeryNotSticky.exists_ballFactoring_core_ball_inhab` for the margin's radius) nor the
segment count (`Kakeya.VeryNotSticky.card_segsOfCover_le`, needed by
`Kakeya.VeryNotSticky.L_le_uniformLossBound` to make Lemma 9.2's loss ball-independent) can be
recovered from it. Both survive the two cuts of the capstone — `restrictBalls` shrinks `bs`
and `tierCore` shrinks `segs`, and neither touches `Y` or `ctr` — so the pipeline is re-run
here with the two extra conclusions carried along. Everything else is verbatim the existing
proof. -/
theorem exists_core_localised_of_cover (cfg : VeryNotSticky.{u}) {bι : Type u}
    {C₀ : NNReal} (hC₀ : 4 ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
    (hbsne : bs.Nonempty)
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
    {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hc₁' : 4 * c₁ * (ballCoverConstant : NNReal) ≤ 1) :
    ∃ core : BallDataCore cfg,
      core.C₀ = C₀ ∧ core.D = D ∧ core.m = 1 ∧ core.Cm = 1 ∧
      core.Cg = 2 * tierRetention cfg c₁ ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
          volume (core.Y p).shade) ∧
      (∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
          maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (segsDilationConstant : ENNReal) *
          maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B, ∀ q ∈ core.segs B,
        shadeFractionClass core p = shadeFractionClass core q) ∧
      core.Localised (11 * (cfg.r₁ : ℝ) / 16) ∧
      (∀ B ∈ core.bs, (core.segs B).card ≤ cfg.s.card) := by
  classical
  set core₀ := ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas
    hPcov hoverlap hPne with hcore₀
  have hbs₀ : core₀.bs = bs := rfl
  have hsegs₀ : core₀.segs = segsOfCover cfg P := rfl
  have hY₀ : core₀.Y = segBodyOfCover cfg ctr P hPmeas := rfl
  have hsne : cfg.s.Nonempty := by
    obtain ⟨B, hB⟩ := hbsne
    obtain ⟨x, -, hxs⟩ := hPne B hB
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp hxs
    exact ⟨i, hi⟩
  have hSm : ∀ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade
      = ballYgMass core₀ B := by
    intro B hB
    exact sum_segShade_eq_ballYgMass_aux cfg hPmeas hδr hPball16 hB
  have hCtop : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).carrier ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (sum_sum_segCarrier_le cfg hPmeas hδr hPball16 hoverlap)
    exact ENNReal.mul_ne_top (by simp) (sum_volume_carrier_ne_top cfg)
  have hS0eq : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade
      = ∑ i ∈ cfg.s, volume (cfg.T i).shade :=
    sum_sum_segShade_eq cfg hPmeas hδr hPball16 hPdisj hPcov
  have hS0 : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade ≠ 0 := by
    rw [hS0eq]
    exact ne_of_gt (sum_volume_shade_pos_of_nonempty cfg hsne)
  have hfull : 4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
      ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).carrier ≤
      ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade := by
    rw [hbs₀, hsegs₀, hY₀]
    exact segs_fullness_of_cover cfg hPmeas hδr hPball16 hPdisj hPcov hoverlap hc₁'
  obtain ⟨bs', hsub, hne, hret, hheavy⟩ :=
    exists_heavyBalls_core core₀ hSm hCtop hS0 hfull
  set core₁ := core₀.restrictBalls bs' hsub hne (K := 2) (by norm_num) hret with hcore₁
  have hfull₁ : ∀ B ∈ core₁.bs, 2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).carrier ≤
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).shade := hheavy
  obtain ⟨k, hkne, hkret⟩ := exists_markovDyadicTier_data core₁ hc₁ hfull₁
  refine ⟨markovDyadicTierCore core₁ c₁ k hkne hkret, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hCgeq : (markovDyadicTierCore core₁ c₁ k hkne hkret).Cg
        = core₀.Cg * 2 * (1 : NNReal) ^ 2 * tierRetention cfg c₁ := rfl
    have hCg₀ : core₀.Cg = 1 := rfl
    rw [hCgeq, hCg₀]
    norm_num
  · exact markovDyadicTierCore_segs_density core₁ c₁ k hkne hkret
  · exact tierCore_segs_dilation core₁ _ _ _ _ _
      (restrictBalls_segs_dilation core₀ bs' hsub hne (by norm_num) hret
        (segs_dilation_ballDataCoreOfCover (cfg := cfg) (hC₀ := hC₀) (hD := hD) (hδr := hδr)
          (bs := bs) (ctr := ctr) (P := P) (hbsne := hbsne) (hPball16 := hPball16)
          (hPball := hPball) (hPdisj := hPdisj) (hPmeas := hPmeas) (hPcov := hPcov)
          (hoverlap := hoverlap) (hPne := hPne)))
  · intro B hB p hp q hq
    exact markovDyadicTier_shadeFractionClass_eq core₁ c₁ k hp hq
  · refine BallDataCore.Localised.tierCore ?_ _ _ _ _ _
    refine BallDataCore.Localised.restrictBalls ?_ _ _ _ _ _
    exact localised_ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj
      hPmeas hPcov hoverlap hPne
  · intro B hB
    have h1 : markovDyadicTier core₁ c₁ k B ⊆ core₁.segs B :=
      markovDyadicTier_subset core₁ c₁ k B
    have h2 : core₁.segs B = segsOfCover cfg P B := rfl
    refine le_trans (Finset.card_le_card h1) ?_
    rw [h2]
    exact card_segsOfCover_le cfg P B

/-! ### The per-ball factorings of Lemma 9.2, glued at the margin's radius -/

open scoped Classical in
/-- **`Kakeya.VeryNotSticky.exists_ballFactoring_glued` at a strengthened radius.**

Identical to the existing gluing except that the per-ball input is
`Kakeya.VeryNotSticky.exists_ballFactoring_core_ball_inhab` rather than
`Kakeya.VeryNotSticky.exists_ballFactoring_core_inhab`, so the `bodies_subset_ball` clause
comes out at `R` and not at `r₁`. This is what the margin of `BallDataGeneralTarget` reads,
and it is the reason the existing gluing cannot be used as a black box for the general branch:
its conclusion is stated at `r₁`, which the margin repair
`Kakeya.VeryNotSticky.margin_of_localised_bodies` cannot consume. -/
theorem exists_ballFactoring_glued_localised {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hdens : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
        volume (core.Y p).shade)
    {R : ℝ} (hRr : R ≤ (cfg.r₁ : ℝ)) (hloc : core.Localised R) :
    ∃ (tier : core.bι → Finset core.σ)
      (bodies : core.bι → Finset (core.bι × Finset core.σ))
      (Wb : core.bι × Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
      (blk : core.σ → core.bι × Finset core.σ),
      (∀ B ∈ core.bs, tier B ⊆ core.segs B) ∧
      (∀ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core.segs B).card
            (cfg.δ / cfg.r₁) cfg.ϱ *
          ∑ p ∈ tier B, volume (core.Y p).carrier) ∧
      (∀ B ∈ core.bs, ∀ p ∈ tier B, blk p ∈ bodies B) ∧
      (∀ B ∈ core.bs, ∀ p ∈ tier B, (core.Y p).toConvexSpaceBody ≤ Wb (blk p)) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B,
        (Wb j).carrier ⊆ closedBall (core.ctr B) R) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B,
        ConvexSpaceBody.IsFrostmanIn ((tier B).filter fun p => blk p = j)
          (fun p => (core.Y p).toConvexSpaceBody) (Wb j) (lemma92Constant cfg.ϱ)) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B,
        ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ Wb j →
          densityIn ((tier B).filter fun p => blk p = j)
              (fun p => (core.Y p).toConvexSpaceBody) K ≤
            (lemma92Bias core.C₀ cfg.ϱ : ENNReal) *
              (volume K.carrier / volume (Wb j).carrier) ^ cfg.ϱ *
              densityIn ((tier B).filter fun p => blk p = j)
                (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      (∀ B ∈ core.bs, maxDensity (bodies B) Wb ≤
        (lemma92Bias core.C₀ cfg.ϱ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ))) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B, ∀ j' ∈ bodies B,
        ethickness ℝ (Wb j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (Wb j').carrier) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B, ∃ p ∈ tier B, blk p = j) := by
  classical
  have hex : ∀ B : core.bι, B ∈ core.bs →
      ∃ (s' : Finset core.σ) (parts : Finset (Finset core.σ))
        (W : Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
        (bk : core.σ → Finset core.σ),
        s' ⊆ core.segs B ∧
        (∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
          ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core.segs B).card
              (cfg.δ / cfg.r₁) cfg.ϱ * ∑ p ∈ s', volume (core.Y p).carrier) ∧
        (∀ p ∈ s', bk p ∈ parts) ∧
        (∀ p ∈ s', (core.Y p).toConvexSpaceBody ≤ W (bk p)) ∧
        (∀ j ∈ parts, (W j).carrier ⊆ closedBall (core.ctr B) R) ∧
        (∀ j ∈ parts,
          ConvexSpaceBody.IsFrostmanIn (s'.filter fun p => bk p = j)
            (fun p => (core.Y p).toConvexSpaceBody) (W j) (lemma92Constant cfg.ϱ)) ∧
        (∀ j ∈ parts,
          ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ W j →
            densityIn (s'.filter fun p => bk p = j)
                (fun p => (core.Y p).toConvexSpaceBody) K ≤
              (lemma92Bias core.C₀ cfg.ϱ : ENNReal) *
                (volume K.carrier / volume (W j).carrier) ^ cfg.ϱ *
                densityIn (s'.filter fun p => bk p = j)
                  (fun p => (core.Y p).toConvexSpaceBody) (W j)) ∧
        maxDensity parts W ≤
          (lemma92Bias core.C₀ cfg.ϱ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) ∧
        (∀ j ∈ parts, ∀ j' ∈ parts,
          ethickness ℝ (W j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (W j').carrier) ∧
        (∀ j ∈ parts, ∃ p ∈ s', bk p = j) := by
    intro B hB
    obtain ⟨s', parts, W, bk, h1, h2, h3, h4, h5, h6, h7, h8, -, h10, h11⟩ :=
      exists_ballFactoring_core_ball_inhab cfg core hB hRr (fun p hp => hloc B hB p hp)
    exact ⟨s', parts, W, bk, h1, h2, h3, h4, h5, h6, h7, h8, h10, h11⟩
  choose! s' parts W bk h1 h2 h3 h4 h5 h6 h7 h8 h10 h11 using hex
  have htag : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, core.ballTag p = B :=
    fun B hB p hp => ballTag_eq_of_segs_density core hc₁ hdens hB hp
  have hinj : ∀ B : core.bι, Function.Injective (fun t : Finset core.σ => (B, t)) :=
    fun B a b h => (Prod.mk.injEq .. ▸ h).2
  have hfilt : ∀ B ∈ core.bs, ∀ t : Finset core.σ,
      ((s' B).filter fun p => (core.ballTag p, bk (core.ballTag p) p) = (B, t))
        = (s' B).filter fun p => bk B p = t := by
    intro B hB t
    refine Finset.filter_congr fun p hp => ?_
    have htg : core.ballTag p = B := htag B hB p (h1 B hB hp)
    simp [htg]
  refine ⟨s', fun B => (parts B).image (fun t => (B, t)), fun q => W q.1 q.2,
    fun p => (core.ballTag p, bk (core.ballTag p) p), h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB p hp
    have htg : core.ballTag p = B := htag B hB p (h1 B hB hp)
    simp only [htg]
    exact Finset.mem_image_of_mem _ (h3 B hB p hp)
  · intro B hB p hp
    have htg : core.ballTag p = B := htag B hB p (h1 B hB hp)
    simpa only [htg] using h4 B hB p hp
  · intro B hB j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    exact h5 B hB t ht
  · intro B hB j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    simpa only [hfilt B hB t] using h6 B hB t ht
  · intro B hB j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    simpa only [hfilt B hB t] using h7 B hB t ht
  · intro B hB
    rw [maxDensity_le_iff]
    intro K
    have hdi : densityIn ((parts B).image (fun t => (B, t))) (fun q => W q.1 q.2) K
        = densityIn (parts B) (W B) K := by
      unfold densityIn
      congr 1
      rw [Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj B h)]
    rw [hdi]
    exact le_trans (le_maxDensity _ _ _) (h8 B hB)
  · intro B hB j hj j' hj'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hj'
    exact h10 B hB t ht t' ht'
  · intro B hB j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    obtain ⟨p, hp, hpt⟩ := h11 B hB t ht
    refine ⟨p, hp, ?_⟩
    have htg : core.ballTag p = B := htag B hB p (h1 B hB hp)
    simp only [htg, hpt]

/-! ### The family cardinality at the absolute scale -/

/-- **`#𝕋 ≤ δ^{-4}` eventually**, the input `Kakeya.VeryNotSticky.L_le_uniformLossBound` needs
at `N = #𝕋`. `Kakeya.VeryNotSticky.eventually_card_segs_le` is the same bound read on
`bd.segs B`, which is unavailable before the `BallData` is built; the underlying count
`Kakeya.ML2Assembly.card_le_rpow_neg_four` is about `cfg.s` itself. -/
theorem eventually_card_s_le_rpow {η : ℝ} (hη1 : η ≤ 1) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}),
      cfg.δ = δ → cfg.η = η → ((cfg.s.card : ℕ) : ℝ) ≤ ((cfg.δ : ℝ))⁻¹ ^ (4 : ℝ) := by
  filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ((Kakeya.Tube.card_le_of_densityIn_le.C 3 : NNReal) : ENNReal))
      ENNReal.coe_ne_top (ν := (1 : ℝ)) one_pos] with δ hδC
  intro cfg hδeq hηeq
  have hδC' : ((Kakeya.Tube.card_le_of_densityIn_le.C 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-1 : ℝ) := by rw [hδeq]; exact hδC
  have hmax : Kakeya.maxDensity cfg.s (fun i => (cfg.T i).toConvexSpaceBody) ≤
      (cfg.δ : ENNReal) ^ (-η) := by rw [← hηeq]; exact cfg.maxDensity_le
  have hcard := Kakeya.ML2Assembly.card_le_rpow_neg_four cfg.hδ cfg.hδ1 hδC' cfg.s cfg.T
    cfg.contained hη1 hmax
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← Real.rpow_natCast ((cfg.δ : ℝ))⁻¹ 4] at *
  calc ((cfg.s.card : ℕ) : ℝ) ≤ (cfg.δ : ℝ) ^ (-4 : ℝ) := hcard
    _ = ((cfg.δ : ℝ))⁻¹ ^ ((4 : ℕ) : ℝ) := by
        rw [← Real.rpow_neg_one (cfg.δ : ℝ), ← Real.rpow_mul (cfg.δ).coe_nonneg]
        norm_num

/-- The `K⁻¹`-form of a retention bound, as `Kakeya.VeryNotSticky.tierCore` reads it. -/
private theorem inv_mul_le_of_le_mul_coe {K : NNReal} (hK : 1 ≤ K) {x y : ENNReal}
    (h : x ≤ (K : ENNReal) * y) : ((K : NNReal) : ENNReal)⁻¹ * x ≤ y := by
  have hK0 : ((K : NNReal) : ENNReal) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    exact (lt_of_lt_of_le zero_lt_one hK).ne'
  have hKt : ((K : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc ((K : NNReal) : ENNReal)⁻¹ * x
      ≤ ((K : NNReal) : ENNReal)⁻¹ * (((K : NNReal) : ENNReal) * y) := by gcongr
    _ = (((K : NNReal) : ENNReal)⁻¹ * ((K : NNReal) : ENNReal)) * y := by ring
    _ = y := by rw [ENNReal.inv_mul_cancel hK0 hKt, one_mul]

/-! ### The general-branch producer, at one configuration -/

open scoped Classical in
/-- **The general `(a, b)` branch, run end to end at one configuration.**

From `BallDataGeneralTarget`'s cover hypotheses this produces the dimensions `(a, b)` and a
`Kakeya.VeryNotSticky.BallData` over `Kakeya.VeryNotSticky.withDims` carrying every constant
the target pins, together with the sharp localisation of the bodies at `11 r₁/16` and their
thickness profile at the *unchanged* constant `C₀bd`. The four analytic inputs `hA4`, `hAT`,
`hAD`, `hAL` are the four factors of `bd.Cg` absorbed at `εg/4` each; every one of them is an
eventual fact in `δ` supplied by a existing absorber, which is what
`Kakeya.VeryNotSticky.eventually_ballDataGeneral_except_margin` does.

The margin of `BallDataGeneralTarget` is **not** among the conclusions: it needs
`C₀bd · a ≤ 5 r₁/16` on top of the last two conclusions
(`Kakeya.VeryNotSticky.margin_of_localised_bodies`), and `a` is the output of the dimensions
pigeonhole, bounded only by `δ ≤ a ≤ b ≤ r₁`. -/
theorem exists_ballData_general_of_cover (cfg : VeryNotSticky.{u}) {bι : Type u}
    {C₀bd : NNReal} (hC₀ : 4 ≤ C₀bd) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) (hϱ21 : cfg.ϱ ≤ 1 / 21)
    (hr₁1 : 2 * cfg.r₁ ≤ 1)
    (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
    (hbsne : bs.Nonempty)
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
    {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hc₁' : 4 * c₁ * (ballCoverConstant : NNReal) ≤ 1)
    {εg : ℝ}
    (hA4 : (4 : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 4)))
    (hAT : ((tierRetention cfg c₁ : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 4)))
    (hAD : ((dimsClassLoss (3 / 2) cfg.δ : ℕ) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 4)))
    (hAL : ((uniformLossBound 3 cfg.s.card (cfg.δ / cfg.r₁) cfg.ϱ : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(εg / 4))) :
    ∃ (a b : NNReal) (hdims : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal)
      (bd : BallData (withDims cfg a b hdims)),
      bd.C₀ = C₀bd ∧ bd.Cbias = lemma92Bias C₀bd cfg.ϱ ∧ bd.CF = lemma92Constant cfg.ϱ ∧
      bd.Cdil = segsDilationConstant ∧
      bd.c₁ = c₁ ∧ bd.D = D ∧ bd.Cg ≤ cfg.δ ^ (-εg) ∧ bd.m = 1 ∧ bd.Cm = 1 ∧
      cfg.δ ≤ bd.w₁ ∧ bd.w₁ ≤ 1 ∧
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        (bd.Wb j).carrier ⊆ closedBall (bd.ctr B) (11 * (cfg.r₁ : ℝ) / 16)) ∧
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        HasThicknesses (bd.Wb j).carrier C₀bd ![(cfg.r₁ : ℝ), (b : ℝ), (a : ℝ)]) := by
  classical
  obtain ⟨core₁, hC₀eq, hDeq, hmeq, hCmeq, hCgeq, hdens, hdil, hclass, hloc, hcard⟩ :=
    exists_core_localised_of_cover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj
      hPmeas hPcov hoverlap hPne hc₁ hc₁'
  have hRr : 11 * (cfg.r₁ : ℝ) / 16 ≤ (cfg.r₁ : ℝ) := by
    have : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
    linarith
  obtain ⟨tier, bodies, Wb, blk, htier, hLret, hblkmem, hsegsle, hballR, hfro, hbias,
    hanti, hsim, hinhab⟩ :=
    exists_ballFactoring_glued_localised core₁ hc₁ hdens hRr hloc
  set tier' : core₁.bι → Finset core₁.σ := fun B => tier B ∩ core₁.segs B with htier'def
  have htier'sub : ∀ B, tier' B ⊆ core₁.segs B := fun B => Finset.inter_subset_right
  have htier'le : ∀ B, tier' B ⊆ tier B := fun B => Finset.inter_subset_left
  have htier'eq : ∀ B ∈ core₁.bs, tier' B = tier B := fun B hB =>
    Finset.inter_eq_left.2 (htier B hB)
  have hr₁pos : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hdpos : (0 : NNReal) < cfg.δ / cfg.r₁ := div_pos cfg.hδ hr₁pos
  set Kbase : NNReal := uniformLossBound 3 cfg.s.card (cfg.δ / cfg.r₁) cfg.ϱ with hKbase
  have hKbase1 : 1 ≤ Kbase := one_le_uniformLossBound _ _ _ _
  set K₂ : NNReal := 2 * Kbase with hK₂def
  have hK₂1 : 1 ≤ K₂ := by
    rw [hK₂def]
    calc (1 : NNReal) = 1 * 1 := by norm_num
      _ ≤ 2 * Kbase := by
          have h2 : (1 : NNReal) ≤ 2 := by norm_num
          exact mul_le_mul' h2 hKbase1
  have hLret' : ∀ B ∈ core₁.bs, ∑ p ∈ core₁.segs B, volume (core₁.Y p).carrier ≤
      (Kbase : ENNReal) * ∑ p ∈ tier' B, volume (core₁.Y p).carrier := by
    intro B hB
    obtain ⟨p₀, hp₀⟩ := core₁.segs_nonempty B hB
    have hLb : ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core₁.segs B).card
        (cfg.δ / cfg.r₁) cfg.ϱ ≤ (Kbase : ENNReal) :=
      L_le_uniformLossBound hdpos (Finset.card_pos.2 ⟨p₀, hp₀⟩) (hcard B hB)
    calc ∑ p ∈ core₁.segs B, volume (core₁.Y p).carrier
        ≤ ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core₁.segs B).card
            (cfg.δ / cfg.r₁) cfg.ϱ * ∑ p ∈ tier B, volume (core₁.Y p).carrier := hLret B hB
      _ ≤ (Kbase : ENNReal) * ∑ p ∈ tier' B, volume (core₁.Y p).carrier := by
          rw [htier'eq B hB]; gcongr
  have htierne : ∀ B ∈ core₁.bs, (tier' B).Nonempty := fun B hB =>
    tier_nonempty_of_carrier_retention core₁ hB (hLret' B hB)
  have hret₂ : ∀ B ∈ core₁.bs, ((K₂ : NNReal) : ENNReal)⁻¹ *
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).shade ≤
      ∑ p ∈ tier' B, volume (core₁.Y p).shade := by
    intro B hB
    obtain ⟨p₀, hp₀⟩ := core₁.segs_nonempty B hB
    have hcl : ∀ p ∈ core₁.segs B,
        shadeFractionClass core₁ p = shadeFractionClass core₁ p₀ :=
      fun p hp => hclass B hB p hp p₀ hp₀
    have hmk : ∀ p ∈ core₁.segs B, ∃ N : ℕ,
        volume (core₁.Y p).carrier ≤ 2 ^ N * volume (core₁.Y p).shade := by
      intro p hp
      refine ⟨shadeFractionClassBound (markovConst cfg c₁), ?_⟩
      have hNc : (1 : ENNReal) ≤ 2 ^ (shadeFractionClassBound (markovConst cfg c₁)) *
          ((markovConst cfg c₁ : NNReal) : ENNReal) :=
        one_le_two_pow_shadeFractionClassBound_mul (markovConst_pos cfg hc₁)
      have hcoe : ((markovConst cfg c₁ : NNReal) : ENNReal) =
          (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) := coe_markovConst cfg c₁
      calc volume (core₁.Y p).carrier = 1 * volume (core₁.Y p).carrier := (one_mul _).symm
        _ ≤ (2 ^ (shadeFractionClassBound (markovConst cfg c₁)) *
              ((markovConst cfg c₁ : NNReal) : ENNReal)) * volume (core₁.Y p).carrier :=
            mul_le_mul_of_nonneg_right hNc zero_le
        _ = 2 ^ (shadeFractionClassBound (markovConst cfg c₁)) *
              (((markovConst cfg c₁ : NNReal) : ENNReal) * volume (core₁.Y p).carrier) := by
            rw [mul_assoc]
        _ ≤ 2 ^ (shadeFractionClassBound (markovConst cfg c₁)) *
              volume (core₁.Y p).shade := by
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            rw [hcoe]
            exact le_of_eq_of_le (by ring) (hdens B hB p hp)
    have hsh := shade_retention_of_carrier_retention core₁ (htier'sub B) hcl hmk (hLret' B hB)
    refine inv_mul_le_of_le_mul_coe hK₂1 ?_
    have hcast : ((K₂ : NNReal) : ENNReal) = 2 * (Kbase : ENNReal) := by
      rw [hK₂def]; push_cast; ring
    rw [hcast, mul_assoc]
    simpa [mul_assoc] using hsh
  set core₂ := tierCore core₁ tier' htier'sub htierne hK₂1 hret₂ with hcore₂
  have hbs₂ : core₂.bs = core₁.bs := rfl
  have hsegs₂ : core₂.segs = tier' := rfl
  have hbodiesne : ∀ B ∈ core₂.bs, (bodies B).Nonempty := by
    intro B hB
    obtain ⟨p, hp⟩ := htierne B hB
    exact ⟨blk p, hblkmem B hB p (htier'le B hp)⟩
  have hinhab₂ : ∀ B ∈ core₂.bs, ∀ j ∈ bodies B, ∃ p ∈ core₂.segs B, blk p = j := by
    intro B hB j hj
    obtain ⟨p, hp, hpj⟩ := hinhab B hB j hj
    exact ⟨p, by rw [hsegs₂, htier'eq B hB]; exact hp, hpj⟩
  have hsegsle₂ : ∀ B ∈ core₂.bs, ∀ p ∈ core₂.segs B,
      (core₂.Y p).toConvexSpaceBody ≤ Wb (blk p) :=
    fun B hB p hp => hsegsle B hB p (htier'le B hp)
  have hball₂ : ∀ B ∈ core₂.bs, ∀ j ∈ bodies B,
      (Wb j).carrier ⊆ closedBall (core₂.ctr B) (cfg.r₁ : ℝ) :=
    fun B hB j hj => (hballR B hB j hj).trans (closedBall_subset_closedBall hRr)
  have hsim₂ : ∀ B ∈ core₂.bs, ∀ j ∈ bodies B, ∀ j' ∈ bodies B,
      ethickness ℝ (Wb j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (Wb j').carrier :=
    hsim
  obtain ⟨a, b, w₁, hdims, bs', hsub, hne', hprof, hw, hmass⟩ :=
    exists_dimsClass_core cfg core₂ (ρ := 3 / 2) one_lt_three_halves bodies Wb blk
      (ballYgMass core₂) hbodiesne hinhab₂ hsegsle₂ hball₂ hsim₂
  set K₃ : NNReal := ((dimsClassLoss (3 / 2) cfg.δ : ℕ) : NNReal) with hK₃def
  have hK₃1 : 1 ≤ K₃ := by
    rw [hK₃def]
    have : 1 ≤ dimsClassLoss (3 / 2 : NNReal) cfg.δ := by
      unfold dimsClassLoss
      exact Nat.one_le_pow _ _ (Nat.succ_pos _)
    exact_mod_cast this
  have hK₃cast : ((K₃ : NNReal) : ENNReal) = ((dimsClassLoss (3 / 2) cfg.δ : ℕ) : ENNReal) := by
    rw [hK₃def]; push_cast; ring
  have hret₃ : ((K₃ : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core₂.Yg i) ≤
      ∑ i ∈ cfg.s, volume (restrictYg core₂ bs' i) := by
    refine restrictYg_mass_of_retention core₂ bs' hsub ?_
    rw [hK₃cast]
    exact hmass
  set core₃ := core₂.restrictBalls bs' hsub hne' hK₃1 hret₃ with hcore₃
  set core₄ := BallDataCore.withDims cfg a b hdims core₃ with hcore₄
  have hbs₄ : core₄.bs = bs' := rfl
  have hsegs₄ : core₄.segs = tier' := rfl
  have hsub₁ : bs' ⊆ core₁.bs := hsub
  have hC₀₄ : core₄.C₀ = C₀bd := hC₀eq
  have hbudget : (3 / 2 : NNReal) * lemma92Constant cfg.ϱ ≤ 4 :=
    three_halves_mul_lemma92Constant_le hϱ21
  obtain ⟨hδw₁, hw₁r, hw₁prof⟩ := hw hbudget
  have hdimsC : dimsConstant core₂.C₀ (3 / 2) (lemma92Constant cfg.ϱ) = C₀bd := by
    have h2 : core₂.C₀ = C₀bd := hC₀eq
    rw [h2]
    exact dimsConstant_eq_left_of_lemma92 hC₀ hϱ21
  refine ⟨a, b, hdims,
    core₄.toBallData (lemma92Constant cfg.ϱ) (one_le_lemma92Constant cfg.hϱ.le)
      segsDilationConstant one_le_segsDilationConstant
      (lemma92Bias C₀bd cfg.ϱ)
      (one_le_lemma92Bias (le_trans (by norm_num) hC₀) cfg.hϱ.le) c₁ hc₁
      (core₁.bι × Finset core₁.σ) bodies Wb blk w₁
      (fun B hB p hp => hblkmem B (hsub₁ hB) p (htier'le B hp))
      (fun B hB p hp => hsegsle B (hsub₁ hB) p (htier'le B hp))
      (fun B hB j hj => by
        rw [hC₀₄, ← hdimsC]; exact hprof B hB j hj)
      (fun B hB j hj => hball₂ B (hsub₁ hB) j hj)
      (fun B hB j hj => hw₁prof B hB j hj)
      (fun B hB j hj => by
        have hseq : core₄.segs B = tier B := by
          rw [hsegs₄]; exact htier'eq B (hsub₁ hB)
        rw [hseq]
        exact hfro B (hsub₁ hB) j hj)
      (fun B hB j hj => by
        have hseq : core₄.segs B = tier B := by
          rw [hsegs₄]; exact htier'eq B (hsub₁ hB)
        rw [hseq]
        have h := hbias B (hsub₁ hB) j hj
        rw [hC₀eq] at h
        exact h)
      (fun B hB => by
        have h := hanti B (hsub₁ hB)
        rw [hC₀eq] at h
        exact h)
      (fun B hB => by
        refine le_trans (mul_le_mul_of_nonneg_left ?_ zero_le) (hdil B (hsub₁ hB))
        exact maxDensity_mono (fun p ↦ (core₁.Y p).toConvexSpaceBody) (htier'sub B))
      (fun B hB p hp => hdens B (hsub₁ hB) p (htier'sub B hp)),
    hC₀eq, rfl, rfl, rfl, rfl, hDeq, ?_, hmeq, hCmeq, hδw₁, ?_, ?_, ?_⟩
  · change core₄.Cg ≤ cfg.δ ^ (-εg)
    have hCgval : core₄.Cg = core₁.Cg * core₁.Cm ^ 2 * K₂ * K₃ := rfl
    have hδ0 : ((cfg.δ : NNReal) : ENNReal) ≠ 0 := by
      simp only [ne_eq, ENNReal.coe_eq_zero]; exact cfg.hδ.ne'
    have hδt : ((cfg.δ : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hsplit : (cfg.δ : ENNReal) ^ (-(εg / 4)) * (cfg.δ : ENNReal) ^ (-(εg / 4)) *
        (cfg.δ : ENNReal) ^ (-(εg / 4)) * (cfg.δ : ENNReal) ^ (-(εg / 4)) =
        (cfg.δ : ENNReal) ^ (-εg) := by
      rw [← ENNReal.rpow_add _ _ hδ0 hδt, ← ENNReal.rpow_add _ _ hδ0 hδt,
        ← ENNReal.rpow_add _ _ hδ0 hδt]
      congr 1
      ring
    have hADc : ((K₃ : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 4)) := by
      rw [hK₃cast]; exact hAD
    rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne', hCgval, hCgeq, hCmeq,
      ← hsplit]
    have hLHS : ((2 * tierRetention cfg c₁ * (1 : NNReal) ^ 2 * K₂ * K₃ : NNReal) : ENNReal)
        = 4 * ((tierRetention cfg c₁ : NNReal) : ENNReal) * ((Kbase : NNReal) : ENNReal) *
          ((K₃ : NNReal) : ENNReal) := by
      rw [hK₂def]; push_cast; ring
    rw [hLHS]
    gcongr
  · exact le_trans hw₁r hr₁1
  · intro B hB j hj
    exact hballR B (hsub₁ hB) j hj
  · intro B hB j hj
    have h := hprof B hB j hj
    rw [hdimsC] at h
    exact h

/-! ### The producer, eventually in `δ` — everything but the margin -/

section Eventual

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The general-`(a, b)` branch delivers every clause of
`Kakeya.VeryNotSticky.BallDataGeneralTarget` except the margin, and the margin under its
guard.**

The hypothesis block is `BallDataGeneralTarget`'s, plus the three equations pinning `Cbias`,
`CF`, `Cdil` to the values Lemma 9.2 and T3 produce (`lemma92Bias C₀bd ϱ`,
`lemma92Constant ϱ`, `segsDilationConstant`); the target leaves them free, and no producer can.
The conclusion is `BallDataGeneralTarget`'s with the margin conjunct replaced by the sharp
localisation, the thickness profile, and the guarded margin — see the tripwire
`Kakeya.VeryNotSticky.ballDataGeneralTarget_is_this_plus_the_margin` for the mechanical
statement that these are the only differences.

No essential-distinctness hypothesis is used or needed. -/
theorem eventually_ballDataGeneral_except_margin (β ζ exscal ϱ η τ τ' : ℝ)
    (C₀bd Cbias CF Cdil : NNReal) (D : ℕ) (c₁ : NNReal) (εg : ℝ)
    (hCbias : Cbias = lemma92Bias C₀bd ϱ) (hCF : CF = lemma92Constant ϱ)
    (hCdil : Cdil = segsDilationConstant) :
    CaseParams β ζ exscal ϱ η τ τ' → 4 ≤ C₀bd → ballCoverConstant ≤ D →
    0 < c₁ → 4 * c₁ * (ballCoverConstant : NNReal) ≤ 1 → 0 < εg →
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) →
      ∀ {bι : Type u} (bs : Finset bι) (ctr : bι → E3) (P : bι → Set E3),
        bs.Nonempty →
        (∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) ((cfg.r₁ : ℝ) / 16)) →
        (∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) (cfg.r₁ : ℝ)) →
        (bs : Set bι).PairwiseDisjoint P →
        (∀ B, MeasurableSet (P B)) →
        (∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B) →
        (∀ (x : E3) (t : Finset bι), t ⊆ bs →
          (∀ B ∈ t, x ∈ Metric.ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant) →
        (∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) →
        ∃ (a b : NNReal) (h : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal)
          (bd : BallData (cfg.withDims a b h)),
          bd.C₀ = C₀bd ∧ bd.Cbias = Cbias ∧ bd.CF = CF ∧ bd.Cdil = Cdil ∧
          bd.c₁ = c₁ ∧ bd.D = D ∧ bd.Cg ≤ cfg.δ ^ (-εg) ∧ bd.m = 1 ∧ bd.Cm = 1 ∧
          cfg.δ ≤ bd.w₁ ∧ bd.w₁ ≤ 1 ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            (bd.Wb j).carrier ⊆ Metric.closedBall (bd.ctr B) (11 * (cfg.r₁ : ℝ) / 16)) ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            HasThicknesses (bd.Wb j).carrier C₀bd ![(cfg.r₁ : ℝ), (b : ℝ), (a : ℝ)]) ∧
          ((C₀bd : ℝ) * (a : ℝ) ≤ 5 * (cfg.r₁ : ℝ) / 16 →
            ∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
              Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
                Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) := by
  intro params hC₀ hD hc₁ hc₁' hεg
  by_cases hη0 : 0 < η
  · have hη1 : η ≤ 1 := by
      have h6 := params.slabDensity
      have hs := params.scale
      linarith
    have hex0 : (0 : ℝ) < exscal := by
      have h6 := params.slabDensity
      linarith
    have hex1 : exscal < 1 := by have := params.scale; linarith
    have hεg4 : (0 : ℝ) < εg / 4 := by linarith
    have hϱ21 : ϱ ≤ 1 / 21 := caseParams_ϱ_le_one_div_21 params
    filter_upwards [eventually_ennreal_le_rpow_neg (K := (4 : ENNReal)) (by simp) hεg4,
      eventually_tierRetention_le_rpow (c₁ := c₁) hc₁ hη0.le hεg4,
      eventually_dimsClassLoss_le_rpow (ρ := (3 / 2 : NNReal)) one_lt_three_halves hεg4,
      eventually_uniformLossBound_relScale_le_rpow_neg 3 (exscal := exscal) (ϖ := ϱ)
        (p := (4 : ℝ)) hex0.le hex1 hεg4,
      eventually_card_s_le_rpow (η := η) hη1,
      eventually_nnreal_mul_rpow_le_rpow (2 : NNReal) (p := exscal) (q := 0) hex0,
      self_mem_nhdsWithin] with δ h4 hT hDl hL hcards hr₁ hδpos
    intro cfg hδ hη hexs hϱ hδr bι bs ctr P hbsne hP16 hP hdisj hmeas hcov hover hne
    have hr₁eq : cfg.r₁ = cfg.δ ^ exscal := by rw [VeryNotSticky.r₁, hexs]
    have hr₁1 : 2 * cfg.r₁ ≤ 1 := by
      rw [hr₁eq, hδ]
      simpa using hr₁
    have hϱ21' : cfg.ϱ ≤ 1 / 21 := by rw [hϱ]; exact hϱ21
    have hA4 : (4 : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 4)) := by rw [hδ]; exact h4
    have hAT : ((tierRetention cfg c₁ : NNReal) : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(εg / 4)) := hT cfg hδ hη
    have hAD : ((dimsClassLoss (3 / 2) cfg.δ : ℕ) : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(εg / 4)) := by rw [hδ]; exact hDl
    have hAL : ((uniformLossBound 3 cfg.s.card (cfg.δ / cfg.r₁) cfg.ϱ : NNReal) : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(εg / 4)) := by
      rw [hr₁eq, hϱ, hδ]
      exact hL cfg.s.card (by rw [← hδ]; exact hcards cfg hδ hη)
    obtain ⟨a, b, hdims, bd, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
      exists_ballData_general_of_cover cfg hC₀ hD hδr hϱ21' hr₁1 bs ctr P hbsne hP16 hP
        hdisj hmeas hcov hover hne hc₁ hc₁' hA4 hAT hAD hAL
    refine ⟨a, b, hdims, bd, h1, ?_, ?_, ?_, h5, h6, h7, h8, h9, h10, h11, h12, h13, ?_⟩
    · rw [hCbias, ← hϱ]; exact h2
    · rw [hCF, ← hϱ]; exact h3
    · rw [hCdil]; exact h4'
    · intro ha B hB j hj
      exact margin_of_localised_bodies (fun j hj => h12 B hB j hj)
        (fun j hj => h13 B hB j hj) ha j hj
  · filter_upwards with δ cfg hδ hη
    exact absurd (hη ▸ cfg.hη) hη0


end Eventual

/-! ### The exact shape of the gap -/

/-- **The margin is a bound on the circumradius about the ball's centre plus the scale.**

If the closed `scale`-neighbourhood of a body stays inside `B̄(c, r₁)` then *every* point `x`
of the body satisfies `dist x c + scale ≤ r₁`: push `x` outwards along the ray from `c` by
exactly `scale`. So the margin clause of `Kakeya.VeryNotSticky.BallDataGeneralTarget` is
equivalent to `(sup over the body of dist to the centre) + scale ≤ r₁`, and nothing weaker
than a bound on the body's *scale* — i.e. on the pigeonholed `a` — can produce it. -/
theorem dist_add_scale_le_of_margin {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {c : EuclideanSpace ℝ (Fin 3)} {r₁ : ℝ}
    (hm : Metric.cthickening K.scale K.carrier ⊆ Metric.closedBall c r₁)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ K.carrier) :
    dist x c + K.scale ≤ r₁ := by
  have hs : 0 ≤ K.scale := bodyScale_nonneg K
  obtain ⟨v, hv1, hxv⟩ : ∃ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 ∧ x - c = dist x c • v := by
    by_cases hxc : x = c
    · refine ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by simp, ?_⟩
      subst hxc; simp
    · have hd : dist x c ≠ 0 := fun h => hxc (by rwa [dist_eq_zero] at h)
      refine ⟨(dist x c)⁻¹ • (x - c), ?_, ?_⟩
      · rw [norm_smul, dist_eq_norm]
        rw [dist_eq_norm] at hd
        rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
          inv_mul_cancel₀ hd]
      · rw [smul_smul, mul_inv_cancel₀ hd, one_smul]
  set y : EuclideanSpace ℝ (Fin 3) := x + K.scale • v with hy
  have hyx : dist y x ≤ K.scale := by
    rw [hy, dist_eq_norm]
    have hxx : x + K.scale • v - x = K.scale • v := by abel
    rw [hxx, norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_of_nonneg hs]
  have hmem : y ∈ Metric.cthickening K.scale K.carrier :=
    Metric.closedBall_subset_cthickening hx K.scale (Metric.mem_closedBall.2 hyx)
  have hyr := hm hmem
  rw [Metric.mem_closedBall, dist_eq_norm] at hyr
  have hyc : y - c = (dist x c + K.scale) • v := by
    rw [hy, show x + K.scale • v - c = (x - c) + K.scale • v from by abel, hxv, ← add_smul]
  rw [hyc, norm_smul, hv1, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg dist_nonneg hs)] at hyr
  exact hyr

/-- A body localised at radius `R` has scale at most `R` — the *only* bound on the scale the
general branch's localisation supplies. At `R = 11 r₁/16` this is `scale ≤ 11 r₁/16`, while
`Kakeya.VeryNotSticky.margin_of_localised_bodies` needs `scale ≤ 5 r₁/16`. -/
theorem scale_le_of_subset_closedBall {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {c : EuclideanSpace ℝ (Fin 3)} {R : ℝ} (hR : 0 ≤ R)
    (hK : K.carrier ⊆ Metric.closedBall c R) : K.scale ≤ R := by
  rw [bodyScale_eq_thickness_two]
  exact Metric.thickness_le_of_subset_closedBall hK hR 2

/-- **The sharp sufficient form of the margin**: at the localisation radius `11 r₁/16` the
margin holds as soon as the body's scale is at most the remaining `5 r₁/16`. This is
`Kakeya.VeryNotSticky.margin_of_localised_bodies` with the thickness profile bypassed — the
profile only enters there through `scale ≤ C₀ a`. -/
theorem margin_of_scale_le {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {c : EuclideanSpace ℝ (Fin 3)} {r₁ : ℝ}
    (hK : K.carrier ⊆ Metric.closedBall c (11 * r₁ / 16))
    (hs : K.scale ≤ 5 * r₁ / 16) :
    Metric.cthickening K.scale K.carrier ⊆ Metric.closedBall c r₁ := by
  have hs0 : 0 ≤ K.scale := bodyScale_nonneg K
  have hR : 0 ≤ 11 * r₁ / 16 := Metric.nonempty_closedBall.mp (K.nonempty'.mono hK)
  calc Metric.cthickening K.scale K.carrier
      ⊆ Metric.cthickening K.scale (Metric.closedBall c (11 * r₁ / 16)) :=
        Metric.cthickening_subset_of_subset _ hK
    _ = Metric.closedBall c (K.scale + 11 * r₁ / 16) := cthickening_closedBall hs0 hR c
    _ ⊆ Metric.closedBall c r₁ := Metric.closedBall_subset_closedBall (by linarith)

/-- **The guard is false at the top of the dimensions pigeonhole's range.**
`Kakeya.VeryNotSticky.exists_dimsClass_core` bounds its output only by `δ ≤ a ≤ b ≤ r₁`; at
`a = r₁` the margin guard `C₀bd · a ≤ 5 r₁/16` fails for every admissible `C₀bd` (the target
carries `4 ≤ C₀bd`) and every positive radius. So the guard is a genuinely new obligation on
the general branch, not a consequence of the dimension block. -/
theorem not_margin_guard_at_top_of_dims_range {C₀bd r₁ : ℝ} (hC₀ : 4 ≤ C₀bd) (hr : 0 < r₁) :
    ¬ (C₀bd * r₁ ≤ 5 * r₁ / 16) := by nlinarith


/-! ### The plug: `BallDataGeneralTarget` (F23″) is a theorem -/

/-- `4 ≤ edDensityConstant`, the companion of
`Kakeya.VeryNotSticky.four_le_edSegmentsConstant`: it is what turns F23″'s raised `c₁` ceiling
back into the producer's `4 * c₁ * ballCoverConstant ≤ 1`. -/
theorem four_le_edDensityConstant : 4 ≤ edDensityConstant := by
  rw [edDensityConstant]
  nth_rewrite 1 [show (4 : NNReal) = 4 * 1 by ring]
  gcongr
  exact one_le_pow₀ one_le_edDilateConstant

/-- **`Kakeya.VeryNotSticky.BallDataGeneralTarget` — F23″ — is PROVED, with no binders.**

Conjunct 1 of the general `(a, b)` branch closes from
`Kakeya.VeryNotSticky.eventually_ballDataGeneral_except_margin` alone. In particular **no
essential-distinctness hypothesis is taken**: the ED core of R31/G13 is not needed for this
target, and (see the module docstring) it would in fact obstruct the `m = Cm = 1` route that
proves the fibre budget here.

Four steps, each a weakening licensed by the F23″ cut:

* `edSegmentsConstant ≤ C₀bd → 4 ≤ C₀bd` (`four_le_edSegmentsConstant`);
* `edDensityConstant * c₁ * ballCoverConstant ≤ 1 → 4 * c₁ * ballCoverConstant ≤ 1`
  (`four_le_edDensityConstant`);
* `edRadiusConstant * δ ≤ r₁ → 16 * δ ≤ r₁`;
* the producer's `bd.m = 1 ∧ bd.Cm = 1` gives the SP-H fibre budget, because
  `1 ≤ δ^{-(η + 2 exscal)}` for `δ ≤ 1` and `0 < η + 2 exscal`.

And the guard is converted: F23″ carries the **consumer's** guard `(a : ℝ) ≤ δ^{1-τ}`, which implies the producer's compiled `C₀bd · a ≤ 5 r₁/16` eventually in
`δ` because `CaseParams.thinScale : τ + exscal < 1` makes `exscal < 1 - τ`. That conversion is
the whole content of the `eventually_nnreal_mul_rpow_le_rpow` slot below, and it is why F23″
plugs into conjunct 3 with no adapter. -/
theorem ballDataGeneralTarget (β ζ exscal ϱ η τ τ' : ℝ) (C₀bd : NNReal) (D : ℕ)
    (c₁ : NNReal) (εg : ℝ) :
    BallDataGeneralTarget.{u} β ζ exscal ϱ η τ τ' C₀bd D c₁ εg := by
  intro params hC₀ hD hc₁ hc₁' hεg
  have hC₀4 : 4 ≤ C₀bd := le_trans four_le_edSegmentsConstant hC₀
  have hc₁4 : 4 * c₁ * (ballCoverConstant : NNReal) ≤ 1 := by
    refine le_trans ?_ hc₁'
    gcongr
    exact four_le_edDensityConstant
  have hthin : exscal < 1 - τ := by have := params.thinScale; linarith
  filter_upwards [eventually_ballDataGeneral_except_margin.{u} β ζ exscal ϱ η τ τ' C₀bd
      (lemma92Bias C₀bd ϱ) (lemma92Constant ϱ) segsDilationConstant D c₁ εg rfl rfl rfl
      params hC₀4 hD hc₁ hc₁4 hεg,
    eventually_nnreal_mul_rpow_le_rpow (C₀bd * (16 / 5)) (p := 1 - τ) (q := exscal) hthin]
    with δ hprod hguard
  intro cfg hδ hη hex hϱ hrad bι bs ctr P hbsne hP16 hP hdisj hmeas hcov hover hne
  have hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) := deltaLeR₁_of_radiusFloor hrad
  obtain ⟨a, b, hdims, bd, h1, h2, h3, h4, h5, h6, h7, hm, hCm, h10, h11, hloc, hprof, hmar⟩ :=
    hprod cfg hδ hη hex hϱ hδr bs ctr P hbsne hP16 hP hdisj hmeas hcov hover hne
  refine ⟨a, b, hdims, bd, h1, h2, h3,
    h4.le.trans segsDilationConstant_le_capsuleDilationConstant, h5, h6, h7, hCm, ?_, h10, h11,
    hloc, hprof, ?_⟩
  · -- SP-H's fibre budget, from `m = Cm = 1`
    exact fibreBudget_of_pins hm hCm
  · -- the margin, from the consumer's guard
    intro ha
    refine hmar ?_
    have haN : a ≤ cfg.δ ^ (1 - τ) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
      exact ha
    have hr₁ : cfg.r₁ = cfg.δ ^ exscal := by rw [VeryNotSticky.r₁, hex]
    have hstep : C₀bd * a ≤ 5 / 16 * cfg.r₁ := by
      have hg : C₀bd * (16 / 5) * δ ^ (1 - τ) ≤ δ ^ exscal := hguard
      have hg' : (5 / 16 : NNReal) * (C₀bd * (16 / 5) * δ ^ (1 - τ)) ≤
          (5 / 16 : NNReal) * δ ^ exscal := by gcongr
      have hcancel : (5 / 16 : NNReal) * (C₀bd * (16 / 5) * δ ^ (1 - τ))
          = C₀bd * δ ^ (1 - τ) := by
        rw [show (5 / 16 : NNReal) * (C₀bd * (16 / 5) * δ ^ (1 - τ))
              = ((5 / 16 : NNReal) * (16 / 5)) * (C₀bd * δ ^ (1 - τ)) by ring,
          show ((5 / 16 : NNReal) * (16 / 5)) = 1 by norm_num, one_mul]
      rw [hcancel] at hg'
      have haN' : a ≤ δ ^ (1 - τ) := by rw [← hδ]; exact haN
      rw [hr₁, hδ]
      refine le_trans ?_ hg'
      gcongr
    have := NNReal.coe_le_coe.2 hstep
    push_cast at this ⊢
    linarith

/-! ### Why the localisation radius cannot be shrunk instead -/

section CapsuleBudget

variable {δ : NNReal}

/-- **T3's capsule half-length is pinned from below by `segs_thickness`.** The long end of
`Kakeya.VeryNotSticky.BallDataCore.segs_thickness` reads `C₀⁻¹ r₁ ≤ thickness₀`, and the capsule
sits in a ball of radius `L + δ` about the midpoint of its window
(`Kakeya.VeryNotSticky.thickness_segCarrierSet_zero_le`), so `C₀⁻¹ r₁ ≤ L + δ`. At `C₀ = 4` —
the value `Kakeya.VeryNotSticky.hasThicknesses_segCarrierSet` uses and the minimum
`BallDataGeneralTarget` allows — this is `L ≥ r₁/4 - δ`. -/
theorem le_half_length_of_segs_thickness (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) {C₀ : NNReal} {r₁ : ℝ}
    (h : HasThicknesses (segCarrierSet T c L) C₀ ![r₁, (δ : ℝ), (δ : ℝ)]) :
    (C₀ : ℝ)⁻¹ * r₁ ≤ L + (δ : ℝ) := by
  have h0 := (h 0).1
  simp only [Fin.isValue, Fin.val_zero, Matrix.cons_val_zero] at h0
  exact le_trans h0 (thickness_segCarrierSet_zero_le T c hL)

/-- **The margin cannot be made unconditional by shrinking T3's capsule — at `C₀ = 4` the two
constraints are contradictory.**

`Kakeya.VeryNotSticky.scale_le_of_subset_closedBall` says the localisation radius `R` is the only
bound on the body's scale, so an *unguarded* margin through the localisation needs `2 R ≤ r₁`,
with `R = 2L + 2δ + ρ` the sharp radius of
`Kakeya.VeryNotSticky.segCarrierSet_subset_closedBall_ctr` at the cover mesh `ρ = r₁/16`
(the `hPball16` binder of `BallDataGeneralTarget`). Together with
`Kakeya.VeryNotSticky.le_half_length_of_segs_thickness` at `C₀ = 4` this forces `r₁ ≤ 0`:
the `2ρ = r₁/8` the ball cover costs is exactly the slack that is not there.

So repairing the margin by re-cutting T3's `L` is only possible if `C₀bd` is raised above `4`
or the mesh `ρ` is shrunk below `r₁/16` — a constants re-budget, not a proof. -/
theorem no_free_margin_at_C₀_four {r₁ L d : ℝ}
    (hlong : ((4 : NNReal) : ℝ)⁻¹ * r₁ ≤ L + d)
    (hmargin : 2 * (2 * L + 2 * d + r₁ / 16) ≤ r₁) : r₁ ≤ 0 := by
  have h4 : ((4 : NNReal) : ℝ) = 4 := by norm_num
  rw [h4] at hlong
  linarith

end CapsuleBudget

/-- **Why SP-H's `bd.m = 1 ∧ bd.Cm = 1` could not be *deleted* from F23″, only added to.**

Measured at this tip, that cascade is not a
re-cut but a budget re-plan, and this is the arithmetic:

`bd.Cm = 1` is consumed at `ThinConstantProducer.lean:1071` (`rw [hCm]`) to keep the `Cm ^ 2`
factor of `Kakeya.ThinCase.thinSetupConstant` `δ`-free; that constant is what
`Kakeya.VeryNotSticky.exists_thinConfig_le_of_card_bounds_Cg_le` turns into `tc.C ≤ δ^{-ε}` at
`ε = Kakeya.VeryNotSticky.thresholdExponent β exscal η τ`, and `tc.C` is what all three
thresholds of conjunct 2 are budgeted against. Replacing `Cm = 1` by
`Cm · m ≤ δ^{-(η + 2 exscal)}` inflates that factor by `δ^{-2(η + 2 exscal)}`, so the chain needs
`2 (η + 2 exscal) < ε`. It never holds: `thresholdExponent ≤ η / 10`. -/
theorem sph_replacement_exceeds_thin_budget (β τ : ℝ) {exscal η : ℝ}
    (hη : 0 < η) (hexscal : 0 < exscal) :
    thresholdExponent β exscal η τ < 2 * (η + 2 * exscal) := by
  have h := thresholdExponent_le_eta β exscal η τ
  linarith

/-- **Tripwire: the target is a theorem, and its statement is the one this file proves.**

F23′ carried
the margin **unconditionally**, and  measured that no rearrangement of the
existing API reaches it: the margin is equivalent to `circumradius + scale ≤ r₁`
(`Kakeya.VeryNotSticky.dist_add_scale_le_of_margin` below), the branch controls the circumradius
only by `11 r₁/16` and the scale only by `C₀bd · a` with `a` free in `[δ, r₁]`, and
`2 · (9 r₁/16) > r₁`.  §I-1 restored the guard — in the non-vacuous form, i.e.
together with the two unconditional clauses this file exports — and F23″ is the result. The
target is now `Kakeya.VeryNotSticky.ballDataGeneralTarget`, with **no binders**.

This `example` is the bare application, so it stops elaborating the moment the theorem and the
`def` diverge. -/
example : ∀ (β ζ exscal ϱ η τ τ' : ℝ) (C₀bd : NNReal) (D : ℕ) (c₁ : NNReal) (εg : ℝ),
    BallDataGeneralTarget.{u} β ζ exscal ϱ η τ τ' C₀bd D c₁ εg :=
  ballDataGeneralTarget

end Kakeya.VeryNotSticky
