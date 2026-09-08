/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallGeneralGlue
public import Kakeya.DimensionThree.MainLemma2.TangentialSlabDegenerate

/-!
# Two repairs of the general-branch conjunct-1 route: the margin and the `L` loss

Nothing existing changes: every declaration here is new.

## Repair 1 — the margin clause

Conjunct 1 of `Kakeya.VeryNotSticky.SideDataObligations` asks for

```
∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
  Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆ Metric.closedBall (bd.ctr B) r₁
```

i.e. the body must sit **strictly inside** the ball, with a margin at least its own scale.
`Kakeya.VeryNotSticky.exists_ballFactoring_core` exposes only the tight containment
`(Wb j).carrier ⊆ closedBall (ctr B) r₁` (its clause 4), and no other exposed clause localises
the body: `simDims` and `bodies_antiClustering` say nothing about position. The margin is
therefore **not** derivable from Lemma 9.2's existing interface, and no guard on the thickness
parameter `a` repairs that — shrinking `scale` cannot create room inside a containment that is
already an equality in the worst case.

The repair is at the pullback: Lemma 9.2's per-ball run is pulled back along
`Kakeya.VeryNotSticky.ballHomothety`, and its clause 4 is exactly the transport of
`Kakeya.VeryNotSticky.BallDataCore.segs_subset_ball`, which holds at radius `r₁`. The capsules
of T3's core satisfy the strictly stronger localisation
`segCarrierSet (T i) (ctr B) (r₁/4) ⊆ closedBall (ctr B) (11 r₁/16)`
(`Kakeya.VeryNotSticky.segCarrierSet_subset_closedBall_ctr` at `L = r₁/4`, `ρ = r₁/16`, with
`16 δ ≤ r₁`). Feeding *that* through the same pullback gives clause 4 at the smaller radius, and
the margin then follows from the thickness profile.

* `Kakeya.VeryNotSticky.BallDataCore.Localised`: the localisation predicate, with its transports
  along `Kakeya.VeryNotSticky.BallDataCore.restrictBalls` and
  `Kakeya.VeryNotSticky.tierCore` (both keep `Y` and `ctr` and only shrink `bs`/`segs`).
* `Kakeya.VeryNotSticky.localised_ballDataCoreOfCover`: T3's core is localised at `11 r₁/16`.
* `Kakeya.VeryNotSticky.exists_ballFactoring_core_ball` and its block-inhabited form
  `Kakeya.VeryNotSticky.exists_ballFactoring_core_ball_inhab`: Lemma 9.2 per ball with clause 4
  at the strengthened radius `R`, every other clause verbatim as in
  `Kakeya.VeryNotSticky.exists_ballFactoring_core` / `_inhab` (in particular the retention is
  still read at `δ/r₁`, not at `δ/R`, because the change of variables is unchanged).
* `Kakeya.VeryNotSticky.cthickening_scale_subset_closedBall_of_radius`: the margin itself, from a
  containment at radius `R` and `C₀ a ≤ r₁ - R`. The existing
  `Kakeya.VeryNotSticky.cthickening_scale_subset_closedBall_of_half` is its `R = r₁/2` instance.
* `Kakeya.VeryNotSticky.margin_of_localised_bodies`: the composition, i.e. the margin clause of
  conjunct 1 itself, for bodies localised at `11 r₁/16` with profile `(r₁, b, a)` at `C₀` and
  `C₀ a ≤ 5 r₁/16`.
* `Kakeya.VeryNotSticky.eventually_C₀_mul_le_const_mul_r₁`: the threshold `C₀ δ ≤ c r₁` for small
  `δ`, for every fixed `c > 0` — the existing
  `Kakeya.VeryNotSticky.eventually_C₀_mul_le_half_r₁` is its `c = 1/2` instance. At `R = 11 r₁/16`
  the margin needs `c = 5/16`, which the half-ball form cannot supply.

## Repair 2 — the `L` loss is ball-dependent

`Kakeya.VeryNotSticky.exists_ballFactoring_core`'s retention is at
`ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core.segs B).card (δ/r₁) ϱ`, which depends on
the ball through `#𝕋_B`, whereas `Kakeya.VeryNotSticky.tierCore` takes a single `K : NNReal` with
`1 ≤ K`. The missing input is monotonicity of `L` in its cardinality argument.

* `ConvexSpaceBody.nonempty_biasedFactorization.L_ne_top`, `L_mono_card`: `L` is finite, and
  monotone in `card` as soon as the smaller cardinality is positive (at `card = 0` the first
  factor reads `Real.logb 2 0 = 0`, so monotonicity genuinely needs `0 < card`).
* `Kakeya.VeryNotSticky.uniformLossBound` and `L_le_uniformLossBound`: the `NNReal` packaging
  `max 1 (L 3 N (δ/r₁) ϱ).toNNReal`, a single ball-independent `K` with `1 ≤ K` dominating
  `L 3 n (δ/r₁) ϱ` for every `0 < n ≤ N`. `max 1` is what supplies `1 ≤ K` without proving
  `1 ≤ L`, which is false for small `card`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped NNReal ENNReal Topology

universe u

namespace ConvexSpaceBody.nonempty_biasedFactorization

/-- Lemma 9.2's polylogarithmic loss factor is finite: it is a product of `ENNReal.ofReal`s. -/
theorem L_ne_top (dim card : ℕ) (d : NNReal) (ϖ : ℝ) : L dim card d ϖ ≠ ⊤ := by
  unfold L
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- **Lemma 9.2's loss factor is monotone in the cardinality of the family.** This is what lets a
family of per-ball retentions, each at its own `#𝕋_B`, be read at one ball-independent
cardinality bound. The hypothesis `0 < n` is necessary and not cosmetic: at `n = 0` the first
factor reads `Real.logb 2 0 = 0`, above `1 + Real.logb 2 (n' * X)` whenever `n' * X < 1`. -/
theorem L_mono_card {dim : ℕ} {d : NNReal} (hd : 0 < d) {ϖ : ℝ} {n n' : ℕ}
    (hn : 0 < n) (hle : n ≤ n') : L dim n d ϖ ≤ L dim n' d ϖ := by
  unfold L
  gcongr ?_ * _
  refine ENNReal.ofReal_le_ofReal ?_
  have hd0 : (0 : ℝ) < (d : ℝ) := hd
  have hc0 : (0 : ℝ) < (Metric.lt_volume_convexHull.c dim : ℝ) :=
    Metric.lt_volume_convexHull.c_pos dim
  set X : ℝ := ((2 : ℝ) ^ dim / ((Metric.lt_volume_convexHull.c dim : ℝ) * (d : ℝ) ^ dim)) ^ ϖ
    with hX
  have hX0 : 0 < X := by
    rw [hX]; exact Real.rpow_pos_of_pos (by positivity) _
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnn : (n : ℝ) ≤ (n' : ℝ) := by exact_mod_cast hle
  have hlog : Real.logb 2 ((n : ℝ) * X) ≤ Real.logb 2 ((n' : ℝ) * X) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right hnn hX0.le)
  linarith

end ConvexSpaceBody.nonempty_biasedFactorization

namespace Kakeya.VeryNotSticky

open ShadedBody

/-! ### Repair 2: a ball-independent `NNReal` bound for Lemma 9.2's loss -/

/-- **The uniformised loss constant.** `Kakeya.VeryNotSticky.tierCore` and
`Kakeya.VeryNotSticky.BallDataCore.restrictBalls` take one `K : NNReal` with `1 ≤ K`; this is
that `K` for Lemma 9.2's loss, read at a cardinality bound `N` valid for every ball. The `max 1`
is what supplies `1 ≤ K`: `L` itself is **not** `≥ 1` in general (for `card * X^ϖ < 2⁻¹` the
first factor is `< 1`). -/
noncomputable def uniformLossBound (dim N : ℕ) (d : NNReal) (ϖ : ℝ) : NNReal :=
  max 1 (ConvexSpaceBody.nonempty_biasedFactorization.L dim N d ϖ).toNNReal

theorem one_le_uniformLossBound (dim N : ℕ) (d : NNReal) (ϖ : ℝ) :
    1 ≤ uniformLossBound dim N d ϖ := le_max_left _ _

/-- **The ball-dependent loss is dominated by the uniform one.** With
`Kakeya.VeryNotSticky.card_segsOfCover_le`-style cardinality bounds `#𝕋_B ≤ N` this replaces
`L 3 (core.segs B).card (δ/r₁) ϱ` by a single ball-independent constant. -/
theorem L_le_uniformLossBound {dim N n : ℕ} {d : NNReal} (hd : 0 < d) {ϖ : ℝ}
    (hn : 0 < n) (hle : n ≤ N) :
    ConvexSpaceBody.nonempty_biasedFactorization.L dim n d ϖ ≤
      (uniformLossBound dim N d ϖ : ENNReal) := by
  refine le_trans
    (ConvexSpaceBody.nonempty_biasedFactorization.L_mono_card hd hn hle) ?_
  rw [uniformLossBound]
  calc ConvexSpaceBody.nonempty_biasedFactorization.L dim N d ϖ
      = ((ConvexSpaceBody.nonempty_biasedFactorization.L dim N d ϖ).toNNReal : ENNReal) :=
        (ENNReal.coe_toNNReal
          (ConvexSpaceBody.nonempty_biasedFactorization.L_ne_top dim N d ϖ)).symm
    _ ≤ ((max 1 (ConvexSpaceBody.nonempty_biasedFactorization.L dim N d ϖ).toNNReal :
          NNReal) : ENNReal) := by
        exact_mod_cast le_max_right (1 : NNReal) _

/-! ### Repair 1: the localisation predicate and its transports -/

variable {cfg : VeryNotSticky.{u}}

/-- **The localisation predicate**: every segment body of every ball of a `BallDataCore` lies in
the closed ball of radius `R` about that ball's centre. `BallDataCore.segs_subset_ball` is
`Localised (cfg.r₁ : ℝ)`; the point of the predicate is that T3's core satisfies it at the
strictly smaller `11 r₁/16`, which is what the margin clause of conjunct 1 needs. -/
def BallDataCore.Localised (core : BallDataCore cfg) (R : ℝ) : Prop :=
  ∀ B ∈ core.bs, ∀ p ∈ core.segs B, (core.Y p).carrier ⊆ closedBall (core.ctr B) R

theorem BallDataCore.Localised.mono {core : BallDataCore cfg} {R R' : ℝ} (hRR : R ≤ R')
    (h : core.Localised R) : core.Localised R' := fun B hB p hp =>
  (h B hB p hp).trans (closedBall_subset_closedBall hRR)

/-- The localisation is inherited by the heavy-ball restriction: `restrictBalls` keeps `Y` and
`ctr` and only shrinks `bs`. -/
theorem BallDataCore.Localised.restrictBalls {core : BallDataCore cfg} {R : ℝ}
    (h : core.Localised R) (bs' : Finset core.bι) (hsub : bs' ⊆ core.bs) (hne : bs'.Nonempty)
    {K : NNReal} (hK : 1 ≤ K)
    (hret : (K : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i) ≤
      ∑ i ∈ cfg.s, volume (restrictYg core bs' i)) :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).Localised R :=
  fun B hB p hp => h B (hsub hB) p hp

/-- The localisation is inherited by the tier cut: `tierCore` keeps `Y` and `ctr` and only
shrinks `segs`. -/
theorem BallDataCore.Localised.tierCore {core : BallDataCore cfg} {R : ℝ}
    (h : core.Localised R) (tier : core.bι → Finset core.σ)
    (htier : ∀ B, tier B ⊆ core.segs B) (hne : ∀ B ∈ core.bs, (tier B).Nonempty)
    {K : NNReal} (hK : 1 ≤ K)
    (hret : ∀ B ∈ core.bs, (K : ENNReal)⁻¹ * ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
      ∑ p ∈ tier B, volume (core.Y p).shade) :
    (tierCore core tier htier hne hK hret).Localised R :=
  fun B hB p hp => h B hB p (htier B hp)

/-! ### Repair 1: T3's core is localised at `11 r₁/16` -/

section CoreOfCover

variable (cfg) {bι : Type u}
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

open scoped Classical in
/-- **The capsules of T3's core are localised at `11 r₁/16`**, not merely at `r₁`. This is the
strengthening `Kakeya.VeryNotSticky.exists_ballFactoring_core_ball` consumes, and it is where
`16 δ ≤ r₁` enters: the capsule has half-length `r₁/4` and its centre is within `δ + r₁/16` of
the ball's centre, so it lies in `B̄(ctr B, 2·(r₁/4) + 2δ + r₁/16)` and `2δ ≤ r₁/8`. -/
theorem localised_ballDataCoreOfCover :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
        hoverlap hPne).Localised (11 * (cfg.r₁ : ℝ) / 16) := by
  intro B hB p hp
  rw [ballDataCoreOfCover_segs] at hp
  rw [ballDataCoreOfCover_bs] at hB
  rw [ballDataCoreOfCover_Y, ballDataCoreOfCover_ctr]
  obtain ⟨i, -, hine, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
  obtain ⟨x, hx1, hx2⟩ := hine
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  rw [segBodyOfCover_carrier]
  refine segCarrierSet_subset_closedBall_ctr (cfg.T i).toTube (ctr B)
    (ρ := (cfg.r₁ : ℝ) / 16) (by positivity)
    ⟨x, (cfg.T i).shade_subset hx1, hPball16 B hB hx2⟩ ?_
  linarith

end CoreOfCover

/-! ### Repair 1: the ball homothety at a general radius -/

section BallHomothety

variable (ctr : EuclideanSpace ℝ (Fin 3)) (r : NNReal) (hr : 0 < r)

/-- **The ball homothety at a general radius**: `Kakeya.VeryNotSticky.ballHomothety` carries
`B̄(ctr, s)` onto `B̄(0, s/r)` for every `s`, not only for `s = r`. -/
theorem ballHomothety_image_closedBall_div (s : ℝ) :
    ballHomothety ctr r hr '' closedBall ctr s =
      closedBall (0 : EuclideanSpace ℝ (Fin 3)) (s / (r : ℝ)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall_zero_iff, ballHomothety_apply, norm_smul, norm_inv,
      Real.norm_of_nonneg hr'.le]
    calc (r : ℝ)⁻¹ * ‖x - ctr‖ ≤ (r : ℝ)⁻¹ * s := by gcongr
      _ = s / (r : ℝ) := by rw [inv_mul_eq_div]
  · intro hy
    rw [mem_closedBall_zero_iff] at hy
    refine ⟨(r : ℝ) • y + ctr, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, norm_smul,
        Real.norm_of_nonneg hr'.le]
      calc (r : ℝ) * ‖y‖ ≤ (r : ℝ) * (s / (r : ℝ)) := by gcongr
        _ = s := by field_simp
    · exact (ballHomothety ctr r hr).apply_symm_apply y

/-- The inverse ball homothety carries `B̄(0, s/r)` onto `B̄(ctr, s)`. -/
theorem ballHomothety_symm_image_closedBall_div (s : ℝ) :
    (ballHomothety ctr r hr).symm '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) (s / (r : ℝ)) =
      closedBall ctr s := by
  rw [AffineEquiv.image_symm, ← ballHomothety_image_closedBall_div ctr r hr s,
    (ballHomothety ctr r hr).injective.preimage_image]

end BallHomothety

/-! ### Repair 1: Lemma 9.2 per ball with clause 4 at the strengthened radius -/

open scoped Classical in
/-- **`Kakeya.VeryNotSticky.exists_ballFactoring_core` with `bodies_subset_ball` at a
strengthened radius `R ≤ r₁`**, from the localisation of the segments at `R`. Every other clause
is verbatim that of `Kakeya.VeryNotSticky.exists_ballFactoring_core` — in particular the
retention is still read at the loss `L 3 (core.segs B).card (δ/r₁) ϱ` and clause 8 (GWZ (91)) is
still read against `B̄(ctr B, r₁)`, because the change of variables is unchanged: only the
transported localisation `(V p).carrier ⊆ B̄(0, R/r₁)` is stronger, and the hull of the block
inherits it by convexity. This is the sole clause the margin of conjunct 1 needs. -/
theorem exists_ballFactoring_core_ball (cfg : VeryNotSticky.{u}) (core : BallDataCore cfg)
    {B : core.bι} (hB : B ∈ core.bs) {R : ℝ} (hRr : R ≤ (cfg.r₁ : ℝ))
    (hcarr : ∀ p ∈ core.segs B, (core.Y p).carrier ⊆ closedBall (core.ctr B) R) :
    ∃ (s' : Finset core.σ) (parts : Finset (Finset core.σ))
      (Wb : Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
      (blk : core.σ → Finset core.σ),
      s' ⊆ core.segs B ∧
      (∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core.segs B).card (cfg.δ / cfg.r₁)
            cfg.ϱ *
          ∑ p ∈ s', volume (core.Y p).carrier) ∧
      (∀ p ∈ s', blk p ∈ parts) ∧
      (∀ p ∈ s', (core.Y p).toConvexSpaceBody ≤ Wb (blk p)) ∧
      (∀ j ∈ parts, (Wb j).carrier ⊆ closedBall (core.ctr B) R) ∧
      (∀ j ∈ parts,
        ConvexSpaceBody.IsFrostmanIn (s'.filter fun p => blk p = j)
          (fun p => (core.Y p).toConvexSpaceBody) (Wb j) (lemma92Constant cfg.ϱ)) ∧
      (∀ j ∈ parts,
        ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ Wb j →
          densityIn (s'.filter fun p => blk p = j)
              (fun p => (core.Y p).toConvexSpaceBody) K ≤
            (lemma92Bias core.C₀ cfg.ϱ : ENNReal) *
              (volume K.carrier / volume (Wb j).carrier) ^ cfg.ϱ *
              densityIn (s'.filter fun p => blk p = j)
                (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      maxDensity parts Wb ≤
        (lemma92Bias core.C₀ cfg.ϱ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) ∧
      (∀ j ∈ parts,
        (lemma92Constant cfg.ϱ : ENNReal)⁻¹ *
            (volume (Wb j).carrier / volume (closedBall (core.ctr B) (cfg.r₁ : ℝ))) ^ cfg.ϱ *
            maxDensity s' (fun p => (core.Y p).toConvexSpaceBody) ≤
          densityIn (s'.filter fun p => blk p = j)
            (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      (∀ j ∈ parts, ∀ j' ∈ parts,
        ethickness ℝ (Wb j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (Wb j').carrier) := by
  have hr₁ : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hr₁1 : (cfg.r₁ : ℝ) ≤ 1 := r₁_le_one cfg
  have hr₁0 : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast hr₁
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  set L := ballHomothety (core.ctr B) cfg.r₁ hr₁ with hL
  set V : core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun p ↦ ((core.Y p).toConvexSpaceBody).mapAffine L with hV
  have hδ' : (0 : NNReal) < cfg.δ / cfg.r₁ := div_pos cfg.hδ hr₁
  -- the strengthened localisation, transported into the unit ball
  have h0 : ∀ p ∈ core.segs B, (V p).carrier ⊆ closedBall 0 (R / (cfg.r₁ : ℝ)) := by
    intro p hp
    simp only [hV, ConvexSpaceBody.mapAffine_carrier]
    rw [hL, ← ballHomothety_image_closedBall_div (core.ctr B) cfg.r₁ hr₁ R]
    exact Set.image_mono (hcarr p hp)
  have hRle : R / (cfg.r₁ : ℝ) ≤ 1 := by
    rw [div_le_one hr₁0]; exact hRr
  have h1 : ∀ p ∈ core.segs B, (V p).carrier ⊆ closedBall 0 1 := fun p hp =>
    (h0 p hp).trans (closedBall_subset_closedBall hRle)
  have h2 : ∀ p ∈ core.segs B,
      ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) ≤ ethickness.scale ℝ (V p).carrier := by
    intro p hp
    simp only [hV, ConvexSpaceBody.mapAffine_carrier]
    rw [hL, ethickness_scale_ballHomothety_image, ENNReal.coe_div hr₁.ne',
      ENNReal.div_eq_inv_mul]
    gcongr
    exact core.segs_scale B hB p hp
  obtain ⟨s', hs', hret, ⟨f⟩⟩ := lemma92_on_core cfg core hB L hδ' h1 h2
  rw [hfin] at hret f
  set Wb : Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun t ↦ (t.convexHull_biUnion V).mapAffine L.symm with hWbdef
  have hWb : ∀ t, (Wb t).mapAffine L = t.convexHull_biUnion V := fun t ↦
    ConvexSpaceBody.symm_mapAffine_mapAffine _ _
  have hfilter : ∀ t ∈ f.parts, s'.filter (fun p ↦ f.part p = t) = t := by
    intro t ht
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, rfl⟩
      exact f.mem_part hp
    · intro hp
      exact ⟨f.le ht hp, f.part_eq_of_mem ht hp⟩
  have hJ0 := affineJacobian_ne_zero L
  have hJtop := affineJacobian_ne_top L
  refine ⟨s', f.parts, Wb, fun p ↦ f.part p, hs', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. retention, pulled back (the Jacobian cancels)
    simp only [ConvexSpaceBody.volume_mapAffine, ← Finset.mul_sum] at hret
    rw [mul_left_comm] at hret
    exact (ENNReal.mul_le_mul_iff_right hJ0 hJtop).1 hret
  · -- 2. `blk_mem`
    intro p hp
    exact f.part_mem.2 hp
  · -- 3. `segs_le`
    intro p hp
    have h := (ConvexSpaceBody.mapAffine_le_mapAffine_iff L.symm).2
      (Finset.le_convexHull_biUnion V (f.mem_part hp))
    rwa [hV, ConvexSpaceBody.mapAffine_symm_mapAffine] at h
  · -- 4. `bodies_subset_ball`, **at the strengthened radius `R`**
    intro t ht
    have hsub : (t.convexHull_biUnion V).carrier ⊆ closedBall 0 (R / (cfg.r₁ : ℝ)) :=
      ((f.nonempty_of_mem_parts ht).convexHull_biUnion_subset_iff V
        (convex_closedBall _ _).isConvexSet).2
        fun p hp ↦ h0 p (hs' (f.le ht hp))
    calc (Wb t).carrier = L.symm '' (t.convexHull_biUnion V).carrier := rfl
      _ ⊆ L.symm '' closedBall 0 (R / (cfg.r₁ : ℝ)) := Set.image_mono hsub
      _ = closedBall (core.ctr B) R :=
          ballHomothety_symm_image_closedBall_div (core.ctr B) cfg.r₁ hr₁ R
  · -- 5. `frostman`
    intro t ht
    rw [hfilter t ht]
    refine (isFrostmanIn_mapAffine_iff t (fun p => (core.Y p).toConvexSpaceBody) (Wb t) L _).1 ?_
    rw [hWb t]
    exact f.isFrostman cfg.hϱ.le t ht
  · -- 6. `biasedDensity`, at `Cbias ≥ CF`
    intro t ht K _
    rw [hfilter t ht]
    have hC := densityIn_le_biased_of_mapAffine t (fun p => (core.Y p).toConvexSpaceBody) (Wb t) L
      (by rw [hWb t]; exact f.densityIn_le_biased t ht) K
    refine hC.trans ?_
    gcongr
    exact_mod_cast lemma92Constant_le_lemma92Bias core.hC₀ cfg.hϱ.le
  · -- 7. `bodies_antiClustering`
    rcases f.parts.eq_empty_or_nonempty with hemp | ⟨t, ht⟩
    · rw [hemp, maxDensity_empty]
      exact zero_le
    · rw [hWbdef, maxDensity_mapAffine, coe_lemma92Bias_eq core.hC₀]
      refine antiClustering_of_biasedFactorization cfg.hϱ.le f
        (ratioFloorConstant_pos core.hC₀).ne' cfg.hδ.ne' ht ?_
      obtain ⟨p, hp⟩ := f.nonempty_of_mem_parts ht
      have hp' : p ∈ core.segs B := hs' (f.le ht hp)
      calc (ratioFloorConstant core.C₀ : ENNReal) * (cfg.δ : ENNReal) ^ (2 : ℝ)
          ≤ volume (V p).carrier / volume (closedBall 0 1) :=
            volume_ratio_floor (core.ctr B) hr₁ hr₁1 _ (core.segs_thickness B hB p hp')
        _ ≤ volume (t.convexHull_biUnion V).carrier /
              volume ConvexSpaceBody.closedUnitBall.carrier := by
            rw [ConvexSpaceBody.closedUnitBall_carrier]
            exact ENNReal.div_le_div_right
              (measure_mono (Finset.le_convexHull_biUnion V hp)) _
  · -- 8. GWZ (91) at `U = B`
    intro t ht
    rw [hfilter t ht]
    refine maxDensity_le_densityIn_biased_of_mapAffine s' t
      (fun p => (core.Y p).toConvexSpaceBody) (Wb t) (closedBall (core.ctr B) (cfg.r₁ : ℝ)) L ?_
    rw [hWb t, hL, ballHomothety_image_closedBall]
    have h := f.maxDensity_le_densityIn_biased t ht
    rwa [ConvexSpaceBody.closedUnitBall_carrier] at h
  · -- 9. `simDims`
    intro t ht t' ht'
    have h := f.simDims t ht t' ht'
    rw [← hWb t, ← hWb t', ConvexSpaceBody.mapAffine_carrier,
      ConvexSpaceBody.mapAffine_carrier] at h
    exact ethickness_le_smul_of_ballHomothety_image (core.ctr B) cfg.r₁ hr₁ h

open scoped Classical in
/-- `Kakeya.VeryNotSticky.exists_ballFactoring_core_ball` with the block-inhabitation clause, by
the same pruning of uninhabited parts as
`Kakeya.VeryNotSticky.exists_ballFactoring_core_inhab`. This is the exact input the per-ball →
global gluing reads, now carrying the margin's radius. -/
theorem exists_ballFactoring_core_ball_inhab (cfg : VeryNotSticky.{u}) (core : BallDataCore cfg)
    {B : core.bι} (hB : B ∈ core.bs) {R : ℝ} (hRr : R ≤ (cfg.r₁ : ℝ))
    (hcarr : ∀ p ∈ core.segs B, (core.Y p).carrier ⊆ closedBall (core.ctr B) R) :
    ∃ (s' : Finset core.σ) (parts : Finset (Finset core.σ))
      (Wb : Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
      (blk : core.σ → Finset core.σ),
      s' ⊆ core.segs B ∧
      (∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core.segs B).card (cfg.δ / cfg.r₁)
            cfg.ϱ *
          ∑ p ∈ s', volume (core.Y p).carrier) ∧
      (∀ p ∈ s', blk p ∈ parts) ∧
      (∀ p ∈ s', (core.Y p).toConvexSpaceBody ≤ Wb (blk p)) ∧
      (∀ j ∈ parts, (Wb j).carrier ⊆ closedBall (core.ctr B) R) ∧
      (∀ j ∈ parts,
        ConvexSpaceBody.IsFrostmanIn (s'.filter fun p => blk p = j)
          (fun p => (core.Y p).toConvexSpaceBody) (Wb j) (lemma92Constant cfg.ϱ)) ∧
      (∀ j ∈ parts,
        ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ Wb j →
          densityIn (s'.filter fun p => blk p = j)
              (fun p => (core.Y p).toConvexSpaceBody) K ≤
            (lemma92Bias core.C₀ cfg.ϱ : ENNReal) *
              (volume K.carrier / volume (Wb j).carrier) ^ cfg.ϱ *
              densityIn (s'.filter fun p => blk p = j)
                (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      maxDensity parts Wb ≤
        (lemma92Bias core.C₀ cfg.ϱ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) ∧
      (∀ j ∈ parts,
        (lemma92Constant cfg.ϱ : ENNReal)⁻¹ *
            (volume (Wb j).carrier / volume (closedBall (core.ctr B) (cfg.r₁ : ℝ))) ^ cfg.ϱ *
            maxDensity s' (fun p => (core.Y p).toConvexSpaceBody) ≤
          densityIn (s'.filter fun p => blk p = j)
            (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      (∀ j ∈ parts, ∀ j' ∈ parts,
        ethickness ℝ (Wb j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (Wb j').carrier) ∧
      (∀ j ∈ parts, ∃ p ∈ s', blk p = j) := by
  classical
  obtain ⟨s', parts, Wb, blk, hs', hret, hmem, hle, hball, hfro, hbias, hanti, hdens, hsim⟩ :=
    exists_ballFactoring_core_ball cfg core hB hRr hcarr
  refine ⟨s', parts.filter fun j => ∃ p ∈ s', blk p = j, Wb, blk, hs', hret, ?_, hle,
    fun j hj => hball j (Finset.mem_filter.1 hj).1,
    fun j hj => hfro j (Finset.mem_filter.1 hj).1,
    fun j hj => hbias j (Finset.mem_filter.1 hj).1, ?_,
    fun j hj => hdens j (Finset.mem_filter.1 hj).1,
    fun j hj j' hj' => hsim j (Finset.mem_filter.1 hj).1 j' (Finset.mem_filter.1 hj').1,
    fun j hj => (Finset.mem_filter.1 hj).2⟩
  · intro p hp
    exact Finset.mem_filter.2 ⟨hmem p hp, p, hp, rfl⟩
  · exact le_trans (maxDensity_mono Wb (Finset.filter_subset _ _)) hanti

/-! ### Repair 1: the margin, at a general radius -/

/-- **The margin clause from a containment at a general radius.** A body of profile `(r₁, b, a)`
at `C₀` inside `B̄(c, R)` has `scale ≤ C₀ a`, so when `C₀ a ≤ r₁ - R` its closed
`scale`-neighbourhood stays inside `B̄(c, r₁)` — which is exactly the margin clause of
conjunct 1. The existing `Kakeya.VeryNotSticky.cthickening_scale_subset_closedBall_of_half` is the
instance `R = r₁/2`; the general radius is needed because T3's capsules are localised at
`11 r₁/16`, which no half-ball form can see. -/
theorem cthickening_scale_subset_closedBall_of_radius
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {c : EuclideanSpace ℝ (Fin 3)}
    {C₀ : NNReal} {r₁ b a R : ℝ} (hK : K.carrier ⊆ Metric.closedBall c R)
    (hthick : HasThicknesses K.carrier C₀ ![r₁, b, a]) (ha : (C₀ : ℝ) * a ≤ r₁ - R) :
    Metric.cthickening K.scale K.carrier ⊆ Metric.closedBall c r₁ := by
  have hs0 : 0 ≤ K.scale := bodyScale_nonneg K
  have hR : 0 ≤ R := Metric.nonempty_closedBall.mp (K.nonempty'.mono hK)
  have hs : K.scale ≤ r₁ - R := by
    have h2 := (hthick 2).2
    rw [bodyScale_eq_thickness_two]
    simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
    exact le_trans (by simpa using h2) ha
  calc Metric.cthickening K.scale K.carrier
      ⊆ Metric.cthickening K.scale (Metric.closedBall c R) :=
        Metric.cthickening_subset_of_subset _ hK
    _ = Metric.closedBall c (K.scale + R) := cthickening_closedBall hs0 hR c
    _ ⊆ Metric.closedBall c r₁ := Metric.closedBall_subset_closedBall (by linarith)

/-- **The margin clause of conjunct 1, closed for the localised radius `11 r₁/16`.** This is the
composition that discharges  item 2 end to end: the bodies of the per-ball factoring
delivered by `Kakeya.VeryNotSticky.exists_ballFactoring_core_ball` at `R = 11 r₁/16` (available
for T3's core by `Kakeya.VeryNotSticky.localised_ballDataCoreOfCover`), together with the
thickness profile `(r₁, b, a)` at `C₀` that `Kakeya.VeryNotSticky.BallData.bodies_thickness`
carries, satisfy the margin as soon as `C₀ a ≤ 5 r₁/16` — which
`Kakeya.VeryNotSticky.eventually_C₀_mul_le_const_mul_r₁` supplies at `c = 5/16` for small `δ`. -/
theorem margin_of_localised_bodies {ω : Type*} {parts : Finset ω}
    {Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {ctr : EuclideanSpace ℝ (Fin 3)}
    {C₀ : NNReal} {r₁ b a : ℝ}
    (hball : ∀ j ∈ parts, (Wb j).carrier ⊆ closedBall ctr (11 * r₁ / 16))
    (hthick : ∀ j ∈ parts, HasThicknesses (Wb j).carrier C₀ ![r₁, b, a])
    (ha : (C₀ : ℝ) * a ≤ 5 * r₁ / 16) :
    ∀ j ∈ parts, cthickening (Wb j).scale (Wb j).carrier ⊆ closedBall ctr r₁ := fun j hj =>
  cthickening_scale_subset_closedBall_of_radius (hball j hj) (hthick j hj) (by linarith)

/-- `C₀ δ ≤ c δ^{exscal}` for small `δ`, for every fixed `c > 0` and `exscal < 1`: the threshold
under which `Kakeya.VeryNotSticky.cthickening_scale_subset_closedBall_of_radius` supplies the
margin at `R = (1 - c) r₁`. The existing
`Kakeya.VeryNotSticky.eventually_C₀_mul_le_half_r₁` is the instance `c = 1/2`; the localisation
of T3's capsules at `11 r₁/16` needs `c = 5/16`. -/
theorem eventually_C₀_mul_le_const_mul_r₁ (C₀bd : NNReal) {exscal : ℝ} (hex1 : exscal < 1)
    {c : NNReal} (hc : 0 < c) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      (C₀bd : ℝ) * (d : ℝ) ≤ (c : ℝ) * ((d ^ exscal : NNReal) : ℝ) := by
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow (C₀bd / c) (p := 1) (q := exscal) hex1]
    with d hd
  rw [NNReal.rpow_one] at hd
  have hc0 : c ≠ 0 := hc.ne'
  have h2 : c * (C₀bd / c * d) ≤ c * d ^ exscal := by gcongr
  have hcc : c * (C₀bd / c) = C₀bd := by field_simp
  rw [← mul_assoc, hcc] at h2
  exact_mod_cast h2

end Kakeya.VeryNotSticky
