/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallConstruction

/-!
# The (C4) factoring of Configuration `hyp:ml2setup` at ball-level granularity

`Kakeya.VeryNotSticky.BallDataCore` (in `Kakeya.DimensionThree.MainLemma2.BallConstruction`)
supplies forty-two of the sixty-seven fields of `Kakeya.VeryNotSticky.BallData`, uniformly in
the configuration.  This file closes twenty-two of the remaining twenty-five, leaving only
`Kakeya.VeryNotSticky.BallData.segs_dilation` together with its comparison constant `Cdil`, which every lemma below takes as a parameter.

The point is a structural one about the *statement* of `BallData`, and it is worth stating
plainly because it decides where the mathematical content of blueprint `lem:ml2setupSideData`
actually lives:

* the four constants `CF`, `Cbias`, `c₁` and `C₀` are **free fields** of `BallData`, bounded
  only by `1 ≤ CF`, `1 ≤ Cbias`, `0 < c₁`, `1 ≤ C₀`.  Nothing in `BallData` bounds any of them
  from above;
* every clause of (C4) — `frostman`, `biasedDensity`, `bodies_antiClustering` — and the (C5)
  clause `segs_density` are *monotone* in those constants;
* the families of `BallData` are `Finset`s, so a constant may be chosen as a maximum over the
  data already constructed.

Consequently (C4) can be realized by the degenerate factoring **one body per ball, the body
being the ball itself**, at a `CF` and a `Cbias` read off the constructed segments.  The
resulting `BallData` is of course useless to the case split, whose bundle
`Kakeya.VeryNotSticky.CaseSideData` bounds each of those constants from above in terms of
`cfg.δ` (`Kakeya.VeryNotSticky.thickDensityThresholds_canonical` takes
`CP^{1+ηF} δ^{τ ηF - η} ≤ bd.c₁` and `Cbias (48 C₀^6)^3 ≤ δ^{-τϱ}`).  That is exactly the
finding: **the difficulty of `Kakeya.VeryNotSticky.exists_setup_caseSideData` is not in
`BallData` at all** — barring `segs_dilation`, whose constant `Cdil` is bounded only
downstream, in `Kakeya.VeryNotSticky.SlabScale.final` — but in the
quantitative side conditions of `CaseSideData`.

## What is proved

* `Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` — from a `BallDataCore`
  whose segments have shading of positive measure, from the single scale condition
  `r₁ ≤ C₀ a`, and from `segs_dilation` at any constant `Cdil ≥ 1`, a full
  `Kakeya.VeryNotSticky.BallData`.
* `Kakeya.VeryNotSticky.exists_shade_delete_positive` — the *null* refinement that supplies
  the positivity hypothesis: deleting one global null set from every shading leaves all
  shading volumes unchanged and makes every non-empty intersection of a shading with a piece
  of the cover have positive measure.

The positivity hypothesis is not cosmetic.  It is the exact form of the emptiness phenomenon
recorded : a configuration one of whose shadings meets a piece in a
**non-empty null set** admits no `BallData` at all, since `parent` then forces a segment whose
shade is null while `segs_thickness` forces its carrier to have positive volume, so
`segs_density` forces `c₁ = 0`.  The obstruction is measure-theoretic, not quantitative: a
crumb of small but *positive* measure is harmless, because `c₁` may be taken smaller.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

section Positivity

variable {cfg : VeryNotSticky.{u}}

/-- A segment of a `BallDataCore` lies in exactly one ball of the cover, as soon as its shading
has positive measure: two balls' pieces are disjoint, so a segment shared by two of them would
have empty — hence null — shading. -/
theorem BallDataCore.ball_unique (core : BallDataCore cfg)
    (hshade : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, 0 < volume (core.Y p).shade)
    {p : core.σ} {B B' : core.bι} (hB : B ∈ core.bs) (hB' : B' ∈ core.bs)
    (hp : p ∈ core.segs B) (hp' : p ∈ core.segs B') : B = B' := by
  by_contra hne
  have hdisj : Disjoint (core.P B) (core.P B') := core.P_disjoint hB hB' hne
  have hsub : (core.Y p).shade ⊆ core.P B ∩ core.P B' :=
    subset_inter (core.Y_piece B hB p hp) (core.Y_piece B' hB' p hp')
  rw [hdisj.inter_eq] at hsub
  have : volume (core.Y p).shade = 0 := by
    simp [Set.subset_empty_iff.mp hsub]
  exact absurd this (hshade B hB p hp).ne'

end Positivity


section Arithmetic

/-- Positivity of a finite infimum in `ℝ≥0∞`. -/
private lemma zero_lt_finset_inf {ι : Type*} (t : Finset ι) (f : ι → ENNReal) :
    (∀ i ∈ t, 0 < f i) → 0 < t.inf f := by
  classical
  induction t using Finset.induction_on with
  | empty => intro _; simp
  | insert a t ha ih =>
      intro h
      rw [Finset.inf_insert]
      exact lt_inf_iff.2 ⟨h a (Finset.mem_insert_self a t),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

/-- Finiteness of a finite supremum in `ℝ≥0∞`. -/
private lemma finset_sup_ne_top {ι : Type*} (t : Finset ι) (f : ι → ENNReal) :
    (∀ i ∈ t, f i ≠ ⊤) → t.sup f ≠ ⊤ := by
  classical
  induction t using Finset.induction_on with
  | empty => intro _; simp
  | insert a t ha ih =>
      intro h
      rw [Finset.sup_insert, ← lt_top_iff_ne_top, sup_lt_iff]
      exact ⟨lt_top_iff_ne_top.2 (h a (Finset.mem_insert_self a t)),
        lt_top_iff_ne_top.2 (ih fun i hi => h i (Finset.mem_insert_of_mem hi))⟩

/-- The arithmetic behind the choice of the free constants `CF` and `Cbias`: if the total
volume `Sv` of a family of `n` bodies is at least `n · w`, then `n` is at most
`(V/w)*κ⁻¹ * κ * (Sv/V)` for any positive finite `κ`.  Read at `κ = 1` this is the Frostman
constant; read at `κ = (w/V)^ϱ` it is the biased-density constant. -/
private lemma card_le_const_mul {V w Sv κ : ENNReal} {n : ℕ}
    (hw0 : w ≠ 0) (hwt : w ≠ ⊤) (hV0 : V ≠ 0) (hVt : V ≠ ⊤)
    (hκ0 : κ ≠ 0) (hκt : κ ≠ ⊤) (hsum : (n : ENNReal) * w ≤ Sv) :
    (n : ENNReal) ≤ V / w * κ⁻¹ * κ * (Sv / V) := by
  have key : V / w * κ⁻¹ * κ * (((n : ENNReal) * w) / V) = (n : ENNReal) := by
    have hrw : V / w * κ⁻¹ * κ * (((n : ENNReal) * w) / V)
        = (n : ENNReal) * ((V * V⁻¹) * ((w⁻¹ * w) * (κ⁻¹ * κ))) := by
      simp only [div_eq_mul_inv]
      ring
    rw [hrw, ENNReal.mul_inv_cancel hV0 hVt, ENNReal.inv_mul_cancel hw0 hwt,
      ENNReal.inv_mul_cancel hκ0 hκt, one_mul, one_mul, mul_one]
  calc (n : ENNReal) = V / w * κ⁻¹ * κ * (((n : ENNReal) * w) / V) := key.symm
    _ ≤ V / w * κ⁻¹ * κ * (Sv / V) := by gcongr

end Arithmetic

section Joint

variable {cfg : VeryNotSticky.{u}}

open scoped Classical in
/-- **From a `BallDataCore` with non-degenerate shading to a full `BallData`.**

Twenty-one of the twenty-four fields that `Kakeya.VeryNotSticky.BallDataCore` does not
supply are constructed here; the other three — the dilation constant `Cdil`, its bound
`1 ≤ Cdil` and `segs_dilation` at that constant — are the parameters `Cdil`, `hCdil` and the
hypothesis `hdil`.  It was twenty-two of twenty-five until R26 deleted
`BallData.bodies_essDistinct`, which this construction used to discharge.

The (C4) factoring is the degenerate one: **one body per ball, the body being the ball
itself**.  Its three geometric clauses are then immediate — `bodies_subset_ball` by
reflexivity, and `bodies_thickness`/`bodies_w₁` because a
closed ball of radius `r₁` has thickness exactly `r₁` at every rank below the dimension
(`Metric.thickness_closedBall_le`, `Metric.thickness_closedBall_ge`).  The two *quantitative*
clauses, `frostman` and `biasedDensity`, hold because their constants `CF` and `Cbias` are
free fields of `BallData` with no upper bound: `Kakeya.maxDensity_le_card` bounds every
density by the number of segments, while the reference density in the ball is at least
`card · w / V₁`, where `w` is the least segment volume and `V₁` the volume of an `r₁`-ball, so
`CF = V₁ / w` and `Cbias = (V₁/w)·(w/V₁)^{-ϱ}` serve.  Likewise `segs_density` holds at
`c₁ = (min shade volume)/(max carrier volume)`, which is positive exactly because of `hshade`.

The one scale condition, `hC₀a : r₁ ≤ C₀ a`, is what lets a ball of radius `r₁` be a body of
thickness profile `(r₁, b, a)` with constant `C₀`.  Since `cfg.hdims` gives `δ ≤ a`, it holds
as soon as `C₀ ≥ r₁/δ = δ^{exscal-1}`, and `Kakeya.VeryNotSticky.exists_ballDataCore` accepts
every `C₀ ≥ 4`.

**What this does and does not show.**  It shows that `BallData` is not where the difficulty of
blueprint `lem:ml2setupSideData` lies: barring `segs_dilation`, whose constant `Cdil` is free
here and bounded only in `Kakeya.VeryNotSticky.SlabScale.final`, its sixty-seven fields are all
reachable once the shading is non-degenerate.  It does *not* produce
a `BallData` usable by the case split, whose bundle `Kakeya.VeryNotSticky.CaseSideData` bounds
`c₁` from below and `Cbias`, `C₀` from above in terms of `cfg.δ`. -/
theorem BallDataCore.nonempty_ballData_of_dilation (core : BallDataCore cfg)
    (hshade : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, 0 < volume (core.Y p).shade)
    (hC₀a : (cfg.r₁ : ℝ) ≤ (core.C₀ : ℝ) * (cfg.a : ℝ))
    {Cdil : NNReal} (hCdil : 1 ≤ Cdil)
    (hdil : ∀ B ∈ core.bs,
      (cfg.r₁ : ENNReal) ^ 2 * maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (Cdil : ENNReal) * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) :
    Nonempty (BallData cfg) := by
  classical
  -- ### the scale `r₁` and the ball bodies
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by
    have h : (0 : NNReal) < cfg.r₁ := by
      simpa [VeryNotSticky.r₁] using NNReal.rpow_pos cfg.hδ
    exact_mod_cast h
  have hr₁0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := hr₁pos.le
  set Wb : core.bι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun B ↦ ConvexSpaceBody.closedBall (core.ctr B) (cfg.r₁ : ℝ) hr₁0 with hWbdef
  have hWbcarr : ∀ B, (Wb B).carrier = closedBall (core.ctr B) (cfg.r₁ : ℝ) := fun _ ↦ rfl
  set V₁ : ENNReal := volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (cfg.r₁ : ℝ)) with hV₁def
  have hWbvol : ∀ B, volume (Wb B).carrier = V₁ := by
    intro B
    rw [hWbcarr]
    exact MeasureTheory.Measure.addHaar_closedBall_center volume _ _
  have hV0 : V₁ ≠ 0 := (measure_closedBall_pos volume _ hr₁pos).ne'
  have hVt : V₁ ≠ ⊤ := measure_closedBall_lt_top.ne
  -- ### the finite set of all segments
  set S : Finset core.σ := core.bs.biUnion core.segs with hSdef
  have hmemS : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, p ∈ S := fun B hB p hp ↦
    Finset.mem_biUnion.2 ⟨B, hB, hp⟩
  have hSne : S.Nonempty := by
    obtain ⟨B, hB⟩ := core.bs_nonempty
    obtain ⟨p, hp⟩ := core.segs_nonempty B hB
    exact ⟨p, hmemS B hB p hp⟩
  have hshadeS : ∀ p ∈ S, 0 < volume (core.Y p).shade := by
    intro p hp
    obtain ⟨B, hB, hpB⟩ := Finset.mem_biUnion.1 hp
    exact hshade B hB p hpB
  have hcarrS : ∀ p ∈ S, 0 < volume (core.Y p).carrier := fun p hp ↦
    lt_of_lt_of_le (hshadeS p hp) (measure_mono (core.Y p).shade_subset)
  have hcarrTop : ∀ p : core.σ, volume (core.Y p).carrier ≠ ⊤ := fun p ↦
    ((core.Y p).toConvexSpaceBody.isCompact).measure_lt_top.ne
  have hshadeTop : ∀ p : core.σ, volume (core.Y p).shade ≠ ⊤ := fun p ↦
    ne_top_of_le_ne_top (hcarrTop p) (measure_mono (core.Y p).shade_subset)
  have hcarrV : ∀ p ∈ S, volume (core.Y p).carrier ≤ V₁ := by
    intro p hp
    obtain ⟨B, hB, hpB⟩ := Finset.mem_biUnion.1 hp
    calc volume (core.Y p).carrier
        ≤ volume (closedBall (core.ctr B) (cfg.r₁ : ℝ)) :=
          measure_mono (core.segs_subset_ball B hB p hpB)
      _ = V₁ := MeasureTheory.Measure.addHaar_closedBall_center volume _ _
  -- ### the three extremal volumes
  set w : ENNReal := S.inf (fun p ↦ volume (core.Y p).carrier) with hwdef
  set vmin : ENNReal := S.inf (fun p ↦ volume (core.Y p).shade) with hvmindef
  set wmax : ENNReal := S.sup (fun p ↦ volume (core.Y p).carrier) with hwmaxdef
  have hw0 : w ≠ 0 := (zero_lt_finset_inf S _ hcarrS).ne'
  have hwle : ∀ p ∈ S, w ≤ volume (core.Y p).carrier := fun p hp ↦
    Finset.inf_le (f := fun p ↦ volume (core.Y p).carrier) hp
  have hwt : w ≠ ⊤ := by
    obtain ⟨p, hp⟩ := hSne
    exact ne_top_of_le_ne_top (hcarrTop p) (hwle p hp)
  have hwV : w ≤ V₁ := by
    obtain ⟨p, hp⟩ := hSne
    exact le_trans (hwle p hp) (hcarrV p hp)
  have hvmin0 : vmin ≠ 0 := (zero_lt_finset_inf S _ hshadeS).ne'
  have hvminle : ∀ p ∈ S, vmin ≤ volume (core.Y p).shade := fun p hp ↦
    Finset.inf_le (f := fun p ↦ volume (core.Y p).shade) hp
  have hvminTop : vmin ≠ ⊤ := by
    obtain ⟨p, hp⟩ := hSne
    exact ne_top_of_le_ne_top (hshadeTop p) (hvminle p hp)
  have hwmaxTop : wmax ≠ ⊤ := finset_sup_ne_top S _ fun p _ ↦ hcarrTop p
  have hwmaxle : ∀ p ∈ S, volume (core.Y p).carrier ≤ wmax := fun p hp ↦
    Finset.le_sup (f := fun p ↦ volume (core.Y p).carrier) hp
  have hwmax0 : wmax ≠ 0 := by
    obtain ⟨p, hp⟩ := hSne
    exact fun h ↦ (hcarrS p hp).ne' (nonpos_iff_eq_zero.mp (h ▸ hwmaxle p hp))
  -- ### the three free constants
  have hVw1 : (1 : ENNReal) ≤ V₁ / w := by
    calc (1 : ENNReal) = w / w := (ENNReal.div_self hw0 hwt).symm
      _ ≤ V₁ / w := by gcongr
  have hVwTop : V₁ / w ≠ ⊤ := ENNReal.div_ne_top hVt hw0
  set κ : ENNReal := (w / V₁) ^ cfg.ϱ with hκdef
  have hwV0 : w / V₁ ≠ 0 := (ENNReal.div_pos hw0 hVt).ne'
  have hwVTop : w / V₁ ≠ ⊤ := ENNReal.div_ne_top hwt hV0
  have hκ0 : κ ≠ 0 := (ENNReal.rpow_pos (pos_of_ne_zero hwV0) hwVTop).ne'
  have hκt : κ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg cfg.hϱ.le hwVTop
  have hκ1 : κ ≤ 1 := by
    refine ENNReal.rpow_le_one ?_ cfg.hϱ.le
    calc w / V₁ ≤ V₁ / V₁ := by gcongr
      _ = 1 := ENNReal.div_self hV0 hVt
  set CF : NNReal := (V₁ / w).toNNReal with hCFdef
  have hCFcoe : (CF : ENNReal) = V₁ / w := ENNReal.coe_toNNReal hVwTop
  have hCF : 1 ≤ CF := by
    have : ((1 : NNReal) : ENNReal) ≤ ((CF : NNReal) : ENNReal) := by
      rw [hCFcoe]; simpa using hVw1
    exact_mod_cast this
  set Cbias : NNReal := (V₁ / w * κ⁻¹).toNNReal with hCbiasdef
  have hCbiasTop : V₁ / w * κ⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hVwTop (ENNReal.inv_ne_top.2 hκ0)
  have hCbiascoe : (Cbias : ENNReal) = V₁ / w * κ⁻¹ := ENNReal.coe_toNNReal hCbiasTop
  have hCbias : 1 ≤ Cbias := by
    have hinv1 : (1 : ENNReal) ≤ κ⁻¹ := by
      simpa using (ENNReal.inv_le_inv (a := 1) (b := κ)).2 hκ1
    have : ((1 : NNReal) : ENNReal) ≤ ((Cbias : NNReal) : ENNReal) := by
      rw [hCbiascoe]
      simpa using mul_le_mul' hVw1 hinv1
    exact_mod_cast this
  set c₁ : NNReal := (vmin / wmax).toNNReal with hc₁def
  have hc₁coe : (c₁ : ENNReal) = vmin / wmax := ENNReal.coe_toNNReal
    (ENNReal.div_ne_top hvminTop hwmax0)
  have hc₁ : 0 < c₁ := by
    have hpos : (0 : ENNReal) < vmin / wmax := ENNReal.div_pos hvmin0 hwmaxTop
    have : (0 : ENNReal) < ((c₁ : NNReal) : ENNReal) := by rw [hc₁coe]; exact hpos
    exact_mod_cast this
  -- ### the ball of a segment
  set ballOf : core.σ → core.bι := fun p ↦
    if h : ∃ B, B ∈ core.bs ∧ p ∈ core.segs B then h.choose else core.bs_nonempty.choose
    with hballOfdef
  have hballOf : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ballOf p = B := by
    intro B hB p hp
    have hex : ∃ B, B ∈ core.bs ∧ p ∈ core.segs B := ⟨B, hB, hp⟩
    have hval : ballOf p = hex.choose := by
      simp only [hballOfdef]
      exact dif_pos hex
    rw [hval]
    exact core.ball_unique hshade hex.choose_spec.1 hB hex.choose_spec.2 hp
  -- ### the segments of a ball, and their total volume
  have hfilter : ∀ B ∈ core.bs, (core.segs B).filter (fun p ↦ ballOf p = B) = core.segs B :=
    fun B hB ↦ Finset.filter_true_of_mem fun p hp ↦ hballOf B hB p hp
  have hsegle : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      (core.Y p).toConvexSpaceBody ≤ Wb B := by
    intro B hB p hp
    rw [hWbdef]
    exact core.segs_subset_ball B hB p hp
  have hdenB : ∀ B ∈ core.bs,
      densityIn (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) (Wb B)
        = (∑ p ∈ core.segs B, volume (core.Y p).carrier) / V₁ := by
    intro B hB
    rw [densityIn_of_all_le (fun p hp ↦ hsegle B hB p hp), hWbvol]
  have hcardw : ∀ B ∈ core.bs,
      ((core.segs B).card : ENNReal) * w ≤ ∑ p ∈ core.segs B, volume (core.Y p).carrier := by
    intro B hB
    have := Finset.card_nsmul_le_sum (core.segs B)
      (fun p ↦ volume (core.Y p).carrier) w (fun p hp ↦ hwle p (hmemS B hB p hp))
    simpa [nsmul_eq_mul] using this
  -- ### the (C4) clauses
  have hfrost : ∀ B ∈ core.bs, ∀ j ∈ ({B} : Finset core.bι),
      ConvexSpaceBody.IsFrostmanIn ((core.segs B).filter fun p ↦ ballOf p = j)
        (fun p ↦ (core.Y p).toConvexSpaceBody) (Wb j) CF := by
    intro B hB j hj
    rw [Finset.mem_singleton] at hj
    rw [hj, hfilter B hB]
    intro K' _
    calc densityIn (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) K'
        ≤ ((core.segs B).card : ENNReal) :=
          le_trans (le_maxDensity _ _ _) (maxDensity_le_card _ _)
      _ ≤ V₁ / w * (1 : ENNReal)⁻¹ * (1 : ENNReal) *
            ((∑ p ∈ core.segs B, volume (core.Y p).carrier) / V₁) :=
          card_le_const_mul hw0 hwt hV0 hVt one_ne_zero ENNReal.one_ne_top (hcardw B hB)
      _ = (CF : ENNReal) *
            densityIn (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) (Wb B) := by
          rw [hdenB B hB, hCFcoe]; simp
  have hbias : ∀ B ∈ core.bs, ∀ j ∈ ({B} : Finset core.bι),
      ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ Wb j →
        densityIn ((core.segs B).filter fun p ↦ ballOf p = j)
            (fun p ↦ (core.Y p).toConvexSpaceBody) K ≤
          (Cbias : ENNReal) * (volume K.carrier / volume (Wb j).carrier) ^ cfg.ϱ *
            densityIn ((core.segs B).filter fun p ↦ ballOf p = j)
              (fun p ↦ (core.Y p).toConvexSpaceBody) (Wb j) := by
    intro B hB j hj K _
    rw [Finset.mem_singleton] at hj
    rw [hj, hfilter B hB, hdenB B hB, hWbvol]
    by_cases hK : ∃ p ∈ core.segs B, (core.Y p).toConvexSpaceBody ≤ K
    · obtain ⟨p₀, hp₀, hp₀K⟩ := hK
      have hwK : w ≤ volume K.carrier :=
        le_trans (hwle p₀ (hmemS B hB p₀ hp₀)) (measure_mono hp₀K)
      have hκle : κ ≤ (volume K.carrier / V₁) ^ cfg.ϱ := by
        rw [hκdef]
        exact ENNReal.rpow_le_rpow (by gcongr) cfg.hϱ.le
      calc densityIn (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) K
          ≤ ((core.segs B).card : ENNReal) :=
            le_trans (le_maxDensity _ _ _) (maxDensity_le_card _ _)
        _ ≤ V₁ / w * κ⁻¹ * κ *
              ((∑ p ∈ core.segs B, volume (core.Y p).carrier) / V₁) :=
            card_le_const_mul hw0 hwt hV0 hVt hκ0 hκt (hcardw B hB)
        _ ≤ (Cbias : ENNReal) * (volume K.carrier / V₁) ^ cfg.ϱ *
              ((∑ p ∈ core.segs B, volume (core.Y p).carrier) / V₁) := by
            rw [hCbiascoe]; gcongr
    · push Not at hK
      have hempty : (core.segs B).filter
          (fun p ↦ (core.Y p).toConvexSpaceBody ≤ K) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 ?_
        intro p hp
        exact hK p hp
      have : densityIn (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) K = 0 := by
        simp only [densityIn, hempty, Finset.sum_empty, ENNReal.zero_div]
      rw [this]
      exact bot_le
  -- ### assembling
  refine ⟨core.toBallData CF hCF Cdil hCdil Cbias hCbias c₁ hc₁ core.bι
    (fun B ↦ ({B} : Finset core.bι)) Wb ballOf cfg.r₁ ?_ ?_ ?_ ?_ ?_ hfrost hbias ?_ hdil ?_⟩
  · -- blk_mem
    intro B hB p hp
    rw [Finset.mem_singleton]
    exact hballOf B hB p hp
  · -- segs_le
    intro B hB p hp
    rw [hballOf B hB p hp]
    exact hsegle B hB p hp
  · -- bodies_thickness
    intro B hB j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    have hC₀1 : (1 : ℝ) ≤ (core.C₀ : ℝ) := by exact_mod_cast core.hC₀
    have hC₀pos : (0 : ℝ) < (core.C₀ : ℝ) := lt_of_lt_of_le zero_lt_one hC₀1
    have hab : (cfg.a : ℝ) ≤ (cfg.b : ℝ) := by exact_mod_cast cfg.hdims.2.1
    have hbr : (cfg.b : ℝ) ≤ (cfg.r₁ : ℝ) := by
      have : cfg.b ≤ cfg.r₁ := by simpa [VeryNotSticky.r₁] using cfg.hdims.2.2
      exact_mod_cast this
    have har : (cfg.a : ℝ) ≤ (cfg.r₁ : ℝ) := le_trans hab hbr
    have hthick : ∀ k : Fin 3,
        Metric.thickness ℝ (Wb j).carrier (k : ℕ) = (cfg.r₁ : ℝ) := by
      intro k
      rw [hWbcarr]
      refine le_antisymm (Metric.thickness_closedBall_le (𝕜 := ℝ) hr₁0 _) ?_
      refine Metric.thickness_closedBall_ge hr₁0 ?_
      have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
      rw [h3]
      exact k.2
    intro k
    rw [hthick k]
    have hlow : ∀ t : ℝ, 0 ≤ t → t ≤ (cfg.r₁ : ℝ) → (core.C₀ : ℝ)⁻¹ * t ≤ (cfg.r₁ : ℝ) := by
      intro t ht htr
      calc (core.C₀ : ℝ)⁻¹ * t ≤ 1 * t := by
            gcongr
            exact inv_le_one_of_one_le₀ hC₀1
        _ = t := one_mul t
        _ ≤ (cfg.r₁ : ℝ) := htr
    fin_cases k
    · refine ⟨?_, ?_⟩
      · simpa using hlow _ hr₁0 le_rfl
      · simpa using le_mul_of_one_le_left hr₁0 hC₀1
    · refine ⟨?_, ?_⟩
      · simpa using hlow _ (cfg.b).coe_nonneg hbr
      · simpa using le_trans hC₀a (by gcongr)
    · refine ⟨?_, ?_⟩
      · simpa using hlow _ (cfg.a).coe_nonneg har
      · simpa using hC₀a
  · -- bodies_subset_ball
    intro B hB j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    rw [hWbcarr]
  · -- bodies_w₁
    intro B hB j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
    have hthick : Metric.thickness ℝ (Wb j).carrier
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) = (cfg.r₁ : ℝ) := by
      rw [hWbcarr, h3]
      refine le_antisymm (Metric.thickness_closedBall_le (𝕜 := ℝ) hr₁0 _) ?_
      refine Metric.thickness_closedBall_ge hr₁0 ?_
      rw [h3]; norm_num
    rw [hthick]
    constructor
    · linarith
    · linarith
  · -- bodies_antiClustering
    intro B hB
    have h1 : maxDensity ({B} : Finset core.bι) Wb ≤ 1 := by
      simpa using maxDensity_le_card ({B} : Finset core.bι) Wb
    refine le_trans h1 ?_
    have hδ1 : ((cfg.δ : ENNReal)) ^ (2 * cfg.ϱ) ≤ 1 := by
      refine ENNReal.rpow_le_one ?_ (by linarith [cfg.hϱ])
      exact_mod_cast cfg.hδ1
    have h2 : (1 : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by
      rw [ENNReal.rpow_neg]
      simpa using (ENNReal.inv_le_inv (a := 1) (b := (cfg.δ : ENNReal) ^ (2 * cfg.ϱ))).2 hδ1
    calc (1 : ENNReal) = 1 * 1 := (one_mul 1).symm
      _ ≤ (Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by
          gcongr
          · exact_mod_cast hCbias
  · -- segs_density
    intro B hB p hp
    have hpS : p ∈ S := hmemS B hB p hp
    have hδη : ((cfg.δ : ENNReal)) ^ (2 * cfg.η) ≤ 1 := by
      refine ENNReal.rpow_le_one ?_ (mul_nonneg (by norm_num) cfg.hη.le)
      exact_mod_cast cfg.hδ1
    calc (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier
        ≤ (c₁ : ENNReal) * 1 * wmax := by gcongr; exact hwmaxle p hpS
      _ = vmin := by rw [mul_one, hc₁coe]; exact ENNReal.div_mul_cancel hwmax0 hwmaxTop
      _ ≤ volume (core.Y p).shade := hvminle p hpS

end Joint

section MonoC

variable {cfg : VeryNotSticky.{u}}

/-- A thickness profile with a larger comparison constant. -/
private lemma hasThicknesses_mono {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin 3))} {C C' : NNReal}
    {t : Fin n → ℝ} (h : Kakeya.HasThicknesses K C t) (hC : 0 < C) (hCC' : C ≤ C')
    (ht : ∀ k, 0 ≤ t k) : Kakeya.HasThicknesses K C' t := by
  intro k
  obtain ⟨h1, h2⟩ := h k
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hle : (C : ℝ) ≤ (C' : ℝ) := by exact_mod_cast hCC'
  have hinv : ((C' : ℝ))⁻¹ ≤ ((C : ℝ))⁻¹ := by
    apply inv_anti₀ hCR hle
  refine ⟨le_trans ?_ h1, le_trans h2 ?_⟩
  · exact mul_le_mul_of_nonneg_right hinv (ht k)
  · exact mul_le_mul_of_nonneg_right hle (ht k)

/-- **The comparison constant of a `BallDataCore` may be enlarged.**

The only two fields that mention `C₀` — `segs_thickness` and `segs_core` — weaken as it grows,
so a core may always be read at a larger constant.  This is what makes the scale hypothesis
`r₁ ≤ C₀ a` of `Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` free of cost:
`Kakeya.VeryNotSticky.exists_ballDataCore` produces a core at some `C₀ ≥ 4`, and `cfg.hdims`
gives `δ ≤ a`, so raising `C₀` above `r₁ / δ = δ^{exscal - 1}` suffices. -/
def BallDataCore.monoC₀ (core : BallDataCore cfg) {C₀' : NNReal} (h : core.C₀ ≤ C₀') :
    BallDataCore cfg :=
  { core with
    C₀ := C₀'
    hC₀ := le_trans core.hC₀ h
    segs_thickness := by
      intro B hB p hp
      refine hasThicknesses_mono (core.segs_thickness B hB p hp)
        (lt_of_lt_of_le zero_lt_one core.hC₀) h ?_
      intro k
      fin_cases k <;> simp
    segs_core := by
      intro B hB p hp i hi
      obtain ⟨q, hq⟩ := core.segs_core B hB p hp i hi
      refine ⟨q, hq.trans (Metric.cthickening_mono ?_ _)⟩
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (cfg.δ).coe_nonneg }

/-- **A `BallDataCore` at a constant large enough for the ball bodies.**

The scale hypothesis of `Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` is
always arrangeable. -/
theorem exists_ballDataCore_scale (cfg : VeryNotSticky.{u})
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    ∃ core : BallDataCore cfg, (cfg.r₁ : ℝ) ≤ (core.C₀ : ℝ) * (cfg.a : ℝ) := by
  obtain ⟨core⟩ := exists_ballDataCore cfg (C₀ := 4) le_rfl (D := ballCoverConstant) le_rfl hδr
  refine ⟨core.monoC₀ (le_max_left core.C₀ (cfg.r₁ / cfg.δ)), ?_⟩
  have hδ0 : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hδa : (cfg.δ : ℝ) ≤ (cfg.a : ℝ) := by exact_mod_cast cfg.hdims.1
  have hC : ((cfg.r₁ / cfg.δ : NNReal) : ℝ) ≤ ((max core.C₀ (cfg.r₁ / cfg.δ) : NNReal) : ℝ) := by
    exact_mod_cast le_max_right core.C₀ (cfg.r₁ / cfg.δ)
  have hdiv : ((cfg.r₁ / cfg.δ : NNReal) : ℝ) = (cfg.r₁ : ℝ) / (cfg.δ : ℝ) := by
    push_cast
    rfl
  have hC₀nonneg : (0 : ℝ) ≤ ((max core.C₀ (cfg.r₁ / cfg.δ) : NNReal) : ℝ) := NNReal.coe_nonneg _
  calc (cfg.r₁ : ℝ) = (cfg.r₁ : ℝ) / (cfg.δ : ℝ) * (cfg.δ : ℝ) := by
        field_simp
    _ ≤ ((max core.C₀ (cfg.r₁ / cfg.δ) : NNReal) : ℝ) * (cfg.δ : ℝ) := by
        rw [← hdiv]; gcongr
    _ ≤ ((max core.C₀ (cfg.r₁ / cfg.δ) : NNReal) : ℝ) * (cfg.a : ℝ) := by gcongr

end MonoC

section NullRefinement

variable {cfg : VeryNotSticky.{u}}

open scoped Classical in
/-- **The null crumbs of a family of shadings relative to a finite family of pieces.**

For a family `Y` of measurable shadings indexed by the tubes of `cfg` — the uniform shading
`(cfg.T i).shade`, or the working shading `core.Yg i` of a `Kakeya.VeryNotSticky.BallDataCore` — and a finite family `P` of measurable pieces there is one *global*
null set `S` such that, after `S` is deleted from every `Y i`, each intersection of a shading
with a piece is either empty or of positive measure.

This is the exact repair of the emptiness phenomenon   What makes a
`Kakeya.VeryNotSticky.BallData` impossible is not a crumb of small positive measure — the
constant `c₁` is a free field and may be taken smaller — but a **non-empty null** intersection,
which forces `c₁ = 0` through `parent`, `into` and `segs_density`.  Deleting the null crumbs
costs *no shading mass at all*, so it disturbs neither `Kakeya.VeryNotSticky.fullness_ge` nor
`shading_lb`/`shading_ub`; and deleting one and the same set from every tube leaves every
`ShadedTube.shadeClass` unchanged at every surviving point, so it does not disturb `uniform`
either.  Contrast a *mass-costing* refinement, which `fullness_ge` — stated at exactly the
`δ^η` of the target's own binder, with no comparison constant — does not permit. -/
theorem exists_null_crumbs_family (cfg : VeryNotSticky.{u})
    (Y : cfg.ι → Set (EuclideanSpace ℝ (Fin 3))) (hY : ∀ i ∈ cfg.s, MeasurableSet (Y i))
    {bι : Type u} (bs : Finset bι)
    (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (hP : ∀ B ∈ bs, MeasurableSet (P B)) :
    ∃ S : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet S ∧ volume S = 0 ∧
      ∀ i ∈ cfg.s, ∀ B ∈ bs,
        ((Y i \ S) ∩ P B).Nonempty →
          0 < volume ((Y i \ S) ∩ P B) := by
  classical
  set bad : cfg.ι → bι → Set (EuclideanSpace ℝ (Fin 3)) := fun i B ↦
    if volume (Y i ∩ P B) = 0 then Y i ∩ P B else ∅ with hbaddef
  have hbadmeas : ∀ i ∈ cfg.s, ∀ B ∈ bs, MeasurableSet (bad i B) := by
    intro i hi B hB
    rw [hbaddef]
    by_cases h : volume (Y i ∩ P B) = 0
    · simpa [h] using ((hY i hi).inter (hP B hB))
    · simp [h]
  have hbadnull : ∀ i B, volume (bad i B) = 0 := by
    intro i B
    rw [hbaddef]
    by_cases h : volume (Y i ∩ P B) = 0 <;> simp [h]
  refine ⟨⋃ i ∈ (cfg.s : Set cfg.ι), ⋃ B ∈ (bs : Set bι), bad i B, ?_, ?_, ?_⟩
  · exact MeasurableSet.biUnion (Finset.countable_toSet _) fun i hi ↦
      MeasurableSet.biUnion (Finset.countable_toSet _) fun B hB ↦
        hbadmeas i (by simpa using hi) B (by simpa using hB)
  · refine measure_biUnion_null_iff (Finset.countable_toSet _) |>.2 fun i _ ↦ ?_
    exact measure_biUnion_null_iff (Finset.countable_toSet _) |>.2 fun B _ ↦ hbadnull i B
  · intro i hi B hB hne
    set S : Set (EuclideanSpace ℝ (Fin 3)) :=
      ⋃ i ∈ (cfg.s : Set cfg.ι), ⋃ B ∈ (bs : Set bι), bad i B with hSdef
    have hSnull : volume S = 0 := by
      refine measure_biUnion_null_iff (Finset.countable_toSet _) |>.2 fun i _ ↦ ?_
      exact measure_biUnion_null_iff (Finset.countable_toSet _) |>.2 fun B _ ↦ hbadnull i B
    by_cases h : volume (Y i ∩ P B) = 0
    · exfalso
      obtain ⟨x, hx⟩ := hne
      have hxbad : x ∈ bad i B := by
        rw [hbaddef]
        simp only [h, if_pos]
        exact ⟨hx.1.1, hx.2⟩
      have hxS : x ∈ S := by
        rw [hSdef]
        exact Set.mem_biUnion (by simpa using hi) (Set.mem_biUnion (by simpa using hB) hxbad)
      exact hx.1.2 hxS
    · have hrw : (Y i \ S) ∩ P B = (Y i ∩ P B) \ S := by
        ext x; constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
      rw [hrw, measure_sdiff_null hSnull]
      exact pos_of_ne_zero h

/-- `Kakeya.VeryNotSticky.exists_null_crumbs_family` at the shadings of the configuration. -/
theorem exists_null_crumbs (cfg : VeryNotSticky.{u}) {bι : Type u} (bs : Finset bι)
    (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (hP : ∀ B ∈ bs, MeasurableSet (P B)) :
    ∃ S : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet S ∧ volume S = 0 ∧
      ∀ i ∈ cfg.s, ∀ B ∈ bs,
        (((cfg.T i).shade \ S) ∩ P B).Nonempty →
          0 < volume (((cfg.T i).shade \ S) ∩ P B) :=
  exists_null_crumbs_family cfg (fun i ↦ (cfg.T i).shade)
    (fun i _ ↦ (cfg.T i).measurableSet_shade) bs P hP

/-- **From non-degenerate piece intersections to non-degenerate segment shadings.**

The hypothesis `hfam` — every segment has a parent tube whose working shading actually meets
the segment's piece — is what the segment construction of
`Kakeya.VeryNotSticky.exists_segments` supplies (its segments are indexed by the pairs
`(tube, ball)` whose intersection is non-empty), and it is what
`Kakeya.VeryNotSticky.BallDataCore` does not record. Both hypotheses read the working shading
`core.Yg`, which is what `into` compares with. -/
theorem BallDataCore.shade_pos (core : BallDataCore cfg)
    (hfam : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      ∃ i ∈ core.fam p, (core.Yg i ∩ core.P B).Nonempty)
    (hpos : ∀ i ∈ cfg.s, ∀ B ∈ core.bs, (core.Yg i ∩ core.P B).Nonempty →
      0 < volume (core.Yg i ∩ core.P B)) :
    ∀ B ∈ core.bs, ∀ p ∈ core.segs B, 0 < volume (core.Y p).shade := by
  intro B hB p hp
  obtain ⟨i, hi, hne⟩ := hfam B hB p hp
  have hiS : i ∈ cfg.s := core.fam_subset B hB p hp hi
  calc (0 : ENNReal) < volume (core.Yg i ∩ core.P B) := hpos i hiS B hB hne
    _ ≤ volume (core.Y p).shade := measure_mono (core.into B hB p hp i hi)

end NullRefinement

section DeleteShade

/-- Deleting a measurable set from the shading of a shaded `δ`-tube, leaving the tube itself
untouched. -/
def deleteShadeTube {δ : NNReal} (T : ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) :
    ShadedTube δ (EuclideanSpace ℝ (Fin 3)) where
  toTube := T.toTube
  shade := T.shade \ S
  measurableSet_shade := T.measurableSet_shade.diff hS
  shade_subset := Set.Subset.trans Set.sdiff_subset T.shade_subset

@[simp] lemma deleteShadeTube_shade {δ : NNReal} (T : ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) :
    (deleteShadeTube T S hS).shade = T.shade \ S := rfl

@[simp] lemma deleteShadeTube_toTube {δ : NNReal} (T : ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) :
    (deleteShadeTube T S hS).toTube = T.toTube := rfl

/-- **A global deletion does not change any shade class at a surviving point.**  This is why
the deletion of the null crumbs is invisible to `ShadedTube.ShadedUniformTubeSet`: the four
clauses of that bundle are quantified over points of the shaded union, and at a point outside
the deleted set no member of the family has lost the point. -/
lemma shadeClass_deleteShadeTube {δ : NNReal} {ι : Type*} (s : Finset ι)
    (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S)
    (assign : ι → ι) (j : ι) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ S) :
    ShadedTube.shadeClass s (fun i ↦ deleteShadeTube (V i) S hS) assign j x
      = ShadedTube.shadeClass s V assign j x := by
  classical
  simp only [ShadedTube.shadeClass]
  refine Finset.filter_congr fun i _ ↦ ?_
  simp [hx]

/-- **The uniform hierarchy survives a global deletion.** -/
def shadedUniform_deleteShadeTube {δ : NNReal} {ι : Type*} {s : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s V N C)
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) :
    ShadedTube.ShadedUniformTubeSet s (fun i ↦ deleteShadeTube (V i) S hS) N C where
  tubeUniform := 𝒱.tubeUniform
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := by
    intro x hx k hk i hi hxi
    have hxS : x ∉ S := hxi.2
    rw [shadeClass_deleteShadeTube s V S hS _ _ hxS]
    refine 𝒱.card_shadeClass_le x ?_ k hk i hi hxi.1
    exact Set.mem_biUnion hi hxi.1
  le_card_shadeClass := by
    intro x hx k hk i hi hxi
    have hxS : x ∉ S := hxi.2
    rw [shadeClass_deleteShadeTube s V S hS _ _ hxS]
    refine 𝒱.le_card_shadeClass x ?_ k hk i hi hxi.1
    exact Set.mem_biUnion hi hxi.1
  branchingN_le := by
    intro x hx k hk
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact 𝒱.branchingN_le x (Set.mem_biUnion hi hxi.1) k hk
  le_branchingN := by
    intro x hx k hk
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact 𝒱.le_branchingN x (Set.mem_biUnion hi hxi.1) k hk

/-- **A configuration with its null crumbs deleted.**

Every field of `Kakeya.VeryNotSticky` survives the deletion of a *null* set from every
shading: the carriers are untouched, so the tube-level fields are unchanged; the shading
volumes are untouched, so `fullness_ge`, `shading_lb` and `shading_ub` are unchanged; and the
deleted set is one and the same for every tube, so `uniform` is unchanged
(`Kakeya.VeryNotSticky.shadedUniform_deleteShadeTube`).

This is the refinement that a joint construction of `cfg` and `bd` may perform for free.  Its
refinement constant is `1`, so it costs nothing against the target's conjunct `δ^η ≤ c`. -/
noncomputable def deleteShade (cfg : VeryNotSticky.{u})
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) (hnull : volume S = 0) :
    VeryNotSticky.{u} :=
  { cfg with
    T := fun i ↦ deleteShadeTube (cfg.T i) S hS
    uniform := cfg.uniform.elim fun 𝒰 ↦ ⟨shadedUniform_deleteShadeTube 𝒰 S hS⟩
    fullness_ge := by
      have hnum : ∑ i ∈ cfg.s, volume (deleteShadeTube (cfg.T i) S hS).shade
          = ∑ i ∈ cfg.s, volume (cfg.T i).shade :=
        Finset.sum_congr rfl fun i _ ↦ measure_sdiff_null (s := (cfg.T i).shade) hnull
      have heq : ShadedBody.fullness cfg.s
            (fun i ↦ (deleteShadeTube (cfg.T i) S hS).toShadedBody)
          = ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) := by
        rw [← ENNReal.coe_inj, ShadedBody.fullness_def, ShadedBody.fullness_def]
        exact congrArg (fun z ↦ z / ∑ i ∈ cfg.s, volume (cfg.T i).carrier) hnum
      rw [ge_iff_le, heq]
      exact cfg.fullness_ge
    shading_lb := by
      intro i hi
      have h : volume ((cfg.T i).shade \ S) = volume (cfg.T i).shade :=
        measure_sdiff_null (s := (cfg.T i).shade) hnull
      simpa [h] using cfg.shading_lb i hi
    shading_ub := by
      intro i hi
      have h : volume ((cfg.T i).shade \ S) = volume (cfg.T i).shade :=
        measure_sdiff_null (s := (cfg.T i).shade) hnull
      simpa [h] using cfg.shading_ub i hi
    coarseLocalMass := by
      -- deleting a null set from every shade leaves the datum standing: the coarse
      -- neighbourhood and the ball intersection only shrink, while the total mass is unchanged.
      intro k hk x
      have hUeq : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S))
          = (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) \ S := by
        ext y
        simp only [Set.mem_iUnion, Set.mem_diff, exists_prop]
        tauto
      have hvol : volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) \ S)
          = volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) :=
        measure_sdiff_null (s := ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) hnull
      have hsub : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S))
          ⊆ ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade :=
        Set.iUnion₂_mono fun i _ => Set.diff_subset
      have hmass := cfg.coarseLocalMass k hk x
      show (cfg.δ : ENNReal) ^ cfg.η *
          (volume (Metric.cthickening
                (2 * (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ))
                (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S))) *
            (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S)) ∩
                  Metric.ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ)) /
              volume (Metric.ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ)))) ≤
        volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody.shade \ S))
      rw [hUeq, hvol]
      have hd : ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) \ S)
          ⊆ ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade := Set.diff_subset
      exact le_trans (mul_le_mul' le_rfl (mul_le_mul'
        (measure_mono (Metric.cthickening_subset_of_subset _ hd))
        (ENNReal.div_le_div_right (measure_mono (Set.inter_subset_inter_left _ hd)) _))) hmass }

@[simp] lemma deleteShade_shade (cfg : VeryNotSticky.{u})
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) (hnull : volume S = 0)
    (i : cfg.ι) : ((cfg.deleteShade S hS hnull).T i).shade = (cfg.T i).shade \ S := rfl

end DeleteShade

section CoreTransport

variable {cfg : VeryNotSticky.{u}}

/-- **The per-ball core survives the deletion of the null crumbs.**

The same global null set is removed from every tube shading, from the working shading `Y_g`
and from every segment shading, so `into`, `back` and `fibre` — the three clauses that read the
shadings pointwise — transport verbatim: at a surviving point no tube has lost the point, so the
fibre count is unchanged. The working shading becomes `Y_g(T) \ S`, at the same loss `Cg`,
since deleting a null set changes no volume. -/
noncomputable def BallDataCore.deleteShade (core : BallDataCore cfg)
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) (hnull : volume S = 0) :
    BallDataCore (cfg.deleteShade S hS hnull) where
  C₀ := core.C₀
  hC₀ := core.hC₀
  D := core.D
  Yg := fun i ↦ core.Yg i \ S
  Yg_subset := fun i hi ↦ Set.sdiff_subset_sdiff_left (core.Yg_subset i hi)
  Yg_measurable := fun i hi ↦ (core.Yg_measurable i hi).diff hS
  Cg := core.Cg
  hCg := core.hCg
  Yg_mass := by
    have h1 : ∀ i, volume ((cfg.T i).shade \ S) = volume (cfg.T i).shade :=
      fun i ↦ measure_sdiff_null (s := (cfg.T i).shade) hnull
    have h2 : ∀ i, volume (core.Yg i \ S) = volume (core.Yg i) :=
      fun i ↦ measure_sdiff_null (s := core.Yg i) hnull
    simp only [deleteShade_shade, h1, h2]
    exact core.Yg_mass
  bι := core.bι
  σ := core.σ
  bs := core.bs
  bs_nonempty := core.bs_nonempty
  ctr := core.ctr
  P := core.P
  P_subset_ball := core.P_subset_ball
  P_disjoint := core.P_disjoint
  P_measurable := core.P_measurable
  P_cover := fun i hi ↦ Set.Subset.trans Set.sdiff_subset (core.P_cover i hi)
  ballOverlap := core.ballOverlap
  segs := core.segs
  Y := fun p ↦ (core.Y p).restrictShade Sᶜ hS.compl
  fam := core.fam
  segs_nonempty := core.segs_nonempty
  fam_subset := core.fam_subset
  fam_disjoint := core.fam_disjoint
  Y_piece := fun B hB p hp ↦
    Set.Subset.trans Set.inter_subset_left (core.Y_piece B hB p hp)
  segs_thickness := core.segs_thickness
  segs_dims := core.segs_dims
  parent := by
    intro B hB i hi hne
    refine core.parent B hB i hi ?_
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx.1.1, hx.2⟩
  into := by
    intro B hB p hp i hi x hx
    exact ⟨core.into B hB p hp i hi ⟨hx.1.1, hx.2⟩, hx.1.2⟩
  back := by
    intro B hB p hp x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (core.back B hB p hp hx.1)
    exact Set.mem_biUnion hi ⟨hxi, hx.2⟩
  segs_core := core.segs_core
  m := core.m
  Cm := core.Cm
  hCm := core.hCm
  fibre := by
    classical
    intro B hB p hp x hx
    have hxS : x ∉ S := hx.2
    simp only [Set.mem_sdiff, hxS, not_false_eq_true, and_true]
    exact core.fibre B hB p hp x hx.1
  γ := core.γ
  cov := core.cov
  covCtr := core.covCtr
  cov_isCover := core.cov_isCover
  cov_meets := core.cov_meets
  segs_subset_ball := core.segs_subset_ball
  segs_scale := core.segs_scale

/-- **The total shading mass of a configuration is positive**: its fullness is at least
`δ^{2η} > 0` (`Kakeya.VeryNotSticky.fullness_ge`), and a fullness is a quotient with this sum
as numerator. -/
lemma sum_volume_shade_ne_zero (cfg : VeryNotSticky.{u}) :
    ∑ i ∈ cfg.s, volume (cfg.T i).shade ≠ 0 := by
  intro hzero
  have hzero' : ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade = 0 := hzero
  have hf0 : (ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) : ENNReal) = 0 := by
    rw [ShadedBody.fullness_def, hzero']
    simp
  have hf0' : ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) = 0 := by
    exact_mod_cast hf0
  have hpos : 0 < cfg.δ ^ (2 * cfg.η) := NNReal.rpow_pos cfg.hδ
  have := cfg.fullness_ge
  rw [hf0'] at this
  exact absurd this (not_le.mpr hpos)

/-- **The working shading is non-empty somewhere.** `Kakeya.VeryNotSticky.BallDataCore.Yg_mass`
bounds its total mass below by `Cg⁻¹` times the total shading mass, which is positive
(`Kakeya.VeryNotSticky.sum_volume_shade_ne_zero`), and `Cg⁻¹ ≠ 0` since `Cg` is finite. This is
what `Kakeya.VeryNotSticky.BallDataCore.prune` needs in place of
`Kakeya.VeryNotSticky.iUnionShade_nonempty` now that `P_cover` reads the working shading. -/
lemma BallDataCore.exists_Yg_nonempty (core : BallDataCore cfg) :
    ∃ i ∈ cfg.s, (core.Yg i).Nonempty := by
  by_contra h
  have h' : ∀ i ∈ cfg.s, core.Yg i = ∅ := fun i hi ↦
    Set.not_nonempty_iff_eq_empty.mp fun hne ↦ h ⟨i, hi, hne⟩
  have hzero : ∑ i ∈ cfg.s, volume (core.Yg i) = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [h' i hi, measure_empty]
  have hmass := core.Yg_mass
  rw [hzero, nonpos_iff_eq_zero, mul_eq_zero] at hmass
  rcases hmass with h0 | h0
  · exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top h0
  · exact sum_volume_shade_ne_zero cfg h0

open scoped Classical in
/-- **Discarding the balls and the segments that carry no shading.**

A segment with empty shading, and a ball all of whose segments have empty shading, may be
deleted from a `BallDataCore` without touching anything else: `parent` still holds because
`into` forces a tube whose working shading meets a piece to have a segment with non-empty
shading, and `P_cover` still holds because a point of the working shading lies in a piece of one
of the retained balls, by the same argument. The working shading itself is untouched. -/
noncomputable def BallDataCore.prune (core : BallDataCore cfg) : BallDataCore cfg where
  C₀ := core.C₀
  hC₀ := core.hC₀
  D := core.D
  Yg := core.Yg
  Yg_subset := core.Yg_subset
  Yg_measurable := core.Yg_measurable
  Cg := core.Cg
  hCg := core.hCg
  Yg_mass := core.Yg_mass
  bι := core.bι
  σ := core.σ
  bs := core.bs.filter (fun B ↦ ∃ p ∈ core.segs B, ((core.Y p).shade).Nonempty)
  bs_nonempty := by
    obtain ⟨i, hi, x, hxi⟩ := core.exists_Yg_nonempty
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 (core.P_cover i hi hxi)
    obtain ⟨p, hp, hip⟩ := core.parent B hB i hi ⟨x, hxi, hxB⟩
    exact ⟨B, Finset.mem_filter.2 ⟨hB, ⟨p, hp, ⟨x, core.into B hB p hp i hip ⟨hxi, hxB⟩⟩⟩⟩⟩
  ctr := core.ctr
  P := core.P
  P_subset_ball := fun B hB ↦ core.P_subset_ball B (Finset.mem_of_mem_filter B hB)
  P_disjoint := core.P_disjoint.subset (Finset.coe_subset.2 (Finset.filter_subset _ _))
  P_measurable := fun B hB ↦ core.P_measurable B (Finset.mem_of_mem_filter B hB)
  P_cover := by
    intro i hi x hx
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 (core.P_cover i hi hx)
    obtain ⟨p, hp, hip⟩ := core.parent B hB i hi ⟨x, hx, hxB⟩
    refine Set.mem_biUnion (Finset.mem_filter.2 ⟨hB, ⟨p, hp, ?_⟩⟩) hxB
    exact ⟨x, core.into B hB p hp i hip ⟨hx, hxB⟩⟩
  ballOverlap := by
    intro x t ht hmem
    exact core.ballOverlap x t (ht.trans (Finset.filter_subset _ _)) hmem
  segs := fun B ↦ (core.segs B).filter (fun p ↦ ((core.Y p).shade).Nonempty)
  Y := core.Y
  fam := core.fam
  segs_nonempty := by
    intro B hB
    obtain ⟨-, p, hp, hpne⟩ := Finset.mem_filter.1 hB
    exact ⟨p, Finset.mem_filter.2 ⟨hp, hpne⟩⟩
  fam_subset := fun B hB p hp ↦
    core.fam_subset B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  fam_disjoint := fun B hB ↦
    (core.fam_disjoint B (Finset.mem_of_mem_filter B hB)).mono
      (Finset.coe_subset.2 (Finset.filter_subset _ _))
  Y_piece := fun B hB p hp ↦
    core.Y_piece B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  segs_thickness := fun B hB p hp ↦
    core.segs_thickness B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  segs_dims := fun B hB p hp q hq ↦
    core.segs_dims B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
      q (Finset.mem_of_mem_filter q hq)
  parent := by
    intro B hB i hi hne
    have hB' : B ∈ core.bs := Finset.mem_of_mem_filter B hB
    obtain ⟨p, hp, hip⟩ := core.parent B hB' i hi hne
    obtain ⟨x, hx⟩ := hne
    exact ⟨p, Finset.mem_filter.2 ⟨hp, ⟨x, core.into B hB' p hp i hip hx⟩⟩, hip⟩
  into := fun B hB p hp ↦
    core.into B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  back := fun B hB p hp ↦
    core.back B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  segs_core := fun B hB p hp ↦
    core.segs_core B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  m := core.m
  Cm := core.Cm
  hCm := core.hCm
  fibre := fun B hB p hp ↦
    core.fibre B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  γ := core.γ
  cov := core.cov
  covCtr := core.covCtr
  cov_isCover := fun B hB p hp ↦
    core.cov_isCover B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  cov_meets := fun B hB p hp ↦
    core.cov_meets B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  segs_subset_ball := fun B hB p hp ↦
    core.segs_subset_ball B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)
  segs_scale := fun B hB p hp ↦
    core.segs_scale B (Finset.mem_of_mem_filter B hB) p (Finset.mem_of_mem_filter p hp)

/-- **Non-degeneracy of the segment shadings, from non-degeneracy of the piece
intersections** — of the *working* shading `core.Yg` with the pieces, which is what `into`
compares with. -/
theorem BallDataCore.shade_pos_of_null (core : BallDataCore cfg)
    (hpos : ∀ i ∈ cfg.s, ∀ B ∈ core.bs, (core.Yg i ∩ core.P B).Nonempty →
      0 < volume (core.Yg i ∩ core.P B))
    (hne : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ((core.Y p).shade).Nonempty) :
    ∀ B ∈ core.bs, ∀ p ∈ core.segs B, 0 < volume (core.Y p).shade := by
  intro B hB p hp
  obtain ⟨x, hx⟩ := hne B hB p hp
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (core.back B hB p hp hx)
  have hxB : x ∈ core.P B := core.Y_piece B hB p hp hx
  have hiS : i ∈ cfg.s := core.fam_subset B hB p hp hi
  calc (0 : ENNReal) < volume (core.Yg i ∩ core.P B) :=
        hpos i hiS B hB ⟨x, hxi, hxB⟩
    _ ≤ volume (core.Y p).shade := measure_mono (core.into B hB p hp i hi)

end CoreTransport

section Capstone

/-- **The joint construction: `cfg` and `bd` built together, `64` of `BallData`'s `67` fields.**

For every configuration with `16 δ ≤ r₁` there is a **free** refinement `cfg'` — one global
null set deleted from every shading, so the refinement constant is `1`, all shading volumes are
unchanged, and `Kakeya.VeryNotSticky.fullness_ge`, `shading_lb`, `shading_ub` and `uniform` are
untouched — and a `Kakeya.VeryNotSticky.BallDataCore cfg'` whose `segs_dilation` clause, at
any comparison constant `Cdil ≥ 1`, is the *only* remaining obligation: given it, a full
`Kakeya.VeryNotSticky.BallData cfg'` exists.

This is the compiler-checked form of the answer to "how far does the joint construction get".
The count is `64 / 67`: `Kakeya.VeryNotSticky.BallDataCore` supplies forty-two fields,
`Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` supplies twenty-two more, the
constant `Cdil` and its bound `1 ≤ Cdil` are universally quantified, and `segs_dilation` at that
constant is the hypothesis.

**Why the refinement must be null, and why that is enough.**  What obstructs a `BallData` is a
tube shading meeting a piece of the cover in a **non-empty null set**: `parent` then produces a
segment whose shading is null while `segs_thickness` forces its carrier to have positive
volume, so `segs_density` forces `c₁ = 0`, contradicting `hc₁`.  A crumb of small but positive
measure is *not* an obstruction, because `c₁` is a free field and the families are finite, so
`c₁` may be taken to be the least of the finitely many ratios.  That distinction is what makes
the repair affordable: the deletion is null, hence costs no shading mass, whereas
`Kakeya.VeryNotSticky.fullness_ge` — asserted at exactly the `δ^η` of the target's own binder,
with no comparison constant — permits no mass loss at all when the given family is flat. -/
theorem exists_deleteShade_ballData (cfg : VeryNotSticky.{u})
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    ∃ (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) (hnull : volume S = 0)
      (core : BallDataCore (cfg.deleteShade S hS hnull)),
      ∀ (Cdil : NNReal), 1 ≤ Cdil →
        (∀ B ∈ core.bs,
          ((cfg.deleteShade S hS hnull).r₁ : ENNReal) ^ 2 *
              maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
            (Cdil : ENNReal) * maxDensity (cfg.deleteShade S hS hnull).s
              (fun i ↦ ((cfg.deleteShade S hS hnull).T i).toConvexSpaceBody)) →
        Nonempty (BallData (cfg.deleteShade S hS hnull)) := by
  classical
  obtain ⟨core₀, hC₀a⟩ := exists_ballDataCore_scale cfg hδr
  -- the null crumbs of the *working* shading `core₀.Yg` against the pieces: after the deletion,
  -- `(core₀.deleteShade S hS hnull).prune` has working shading `core₀.Yg i \ S`
  obtain ⟨S, hS, hnull, hpos⟩ := exists_null_crumbs_family cfg core₀.Yg core₀.Yg_measurable
    core₀.bs core₀.P core₀.P_measurable
  refine ⟨S, hS, hnull, (core₀.deleteShade S hS hnull).prune, fun Cdil hCdil hdil ↦ ?_⟩
  refine BallDataCore.nonempty_ballData_of_dilation
    ((core₀.deleteShade S hS hnull).prune) ?_ ?_ hCdil hdil
  · refine BallDataCore.shade_pos_of_null _ (fun i hi B hB hne ↦ ?_) (fun B hB p hp ↦ ?_)
    · exact hpos i hi B (Finset.mem_of_mem_filter B hB) hne
    · exact (Finset.mem_filter.1 hp).2
  · exact hC₀a

end Capstone

section Dilation

variable {cfg : VeryNotSticky.{u}}

/-- A `δ`-tube has positive volume: it contains the `δ`-ball around its starting point. -/
lemma volume_tube_carrier_pos {δ : NNReal} (hδ : 0 < δ)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) : 0 < volume T.carrier := by
  have hsub : closedBall T.x (δ : ℝ) ⊆ T.carrier := by
    rw [T.carrier_eq]
    exact Set.subset_biUnion_of_mem (u := fun z ↦ closedBall z (δ : ℝ))
      (left_mem_segment ℝ T.x T.y)
  exact lt_of_lt_of_le
    (measure_closedBall_pos volume _ (by exact_mod_cast hδ)) (measure_mono hsub)

/-- The tube family of a configuration is non-empty: `tube_count` reads `1 ≤ δ |𝕋|`.

This duplicates `Kakeya.VeryNotSticky.s_nonempty` of
`Kakeya.DimensionThree.MainLemma2.AScaleRounding`, which this file cannot import: it sits
upstream, next to `Kakeya.DimensionThree.MainLemma2.ThinConfig`. -/
lemma nonempty_s_of_tube_count (cfg : VeryNotSticky.{u}) : cfg.s.Nonempty := by
  rcases Finset.eq_empty_or_nonempty cfg.s with h | h
  · exfalso
    have hc := cfg.tube_count
    rw [h] at hc
    simp at hc
  · exact h

/-- **`segs_dilation` reduces to a bound on the segment family alone.**

The parent family enters only through `Δ_max(𝕋) ≥ 1`, which holds for any non-empty family of
bodies of positive volume (`Kakeya.one_le_maxDensity`).  So the *absolute* bound
`Δ_max(𝕋_B) ≤ r₁^{-2}` gives the field `Kakeya.VeryNotSticky.BallData.segs_dilation` at the
comparison constant `Cdil = 1`, which is the form this lemma concludes.  Without a comparison constant, this absolute bound is the condition that the free-constant argument of
`Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` could not reach; the honest
dilation estimate available for the segments of `Kakeya.VeryNotSticky.exists_segments` is
`Δ_max(𝕋_B) ≤ C r₁^{-2}` with a dimensional `C > 1`, which the field now admits at `Cdil := C`.
That estimate is where a successor has to work. -/
theorem segs_dilation_of_maxDensity_le (core : BallDataCore cfg)
    (h : ∀ B ∈ core.bs,
      maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody)
        ≤ ((cfg.r₁ : ENNReal) ^ 2)⁻¹) :
    ∀ B ∈ core.bs,
      (cfg.r₁ : ENNReal) ^ 2 * maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) := by
  intro B hB
  have hr₁pos : (0 : NNReal) < cfg.r₁ := by
    simpa [VeryNotSticky.r₁] using NNReal.rpow_pos cfg.hδ
  have hr0 : ((cfg.r₁ : ENNReal)) ^ 2 ≠ 0 := by
    simp [pow_eq_zero_iff, ENNReal.coe_eq_zero, hr₁pos.ne']
  have hrt : ((cfg.r₁ : ENNReal)) ^ 2 ≠ ⊤ := by
    simp [ENNReal.pow_eq_top_iff]
  obtain ⟨i, hi⟩ := nonempty_s_of_tube_count cfg
  have hone : (1 : ENNReal) ≤ maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) :=
    one_le_maxDensity ⟨i, hi, volume_tube_carrier_pos cfg.hδ (cfg.T i).toTube⟩
  refine le_trans ?_ hone
  calc (cfg.r₁ : ENNReal) ^ 2 * maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody)
      ≤ (cfg.r₁ : ENNReal) ^ 2 * ((cfg.r₁ : ENNReal) ^ 2)⁻¹ := by gcongr; exact h B hB
    _ = 1 := ENNReal.mul_inv_cancel hr0 hrt

/-- **`segs_dilation` from a cardinality bound alone.**

`Kakeya.maxDensity_le_card` bounds the maximal density of the segment family of a ball by the
number of its segments, so the field `Kakeya.VeryNotSticky.BallData.segs_dilation` holds as
soon as **each ball carries at most `r₁^{-2} = δ^{-2 exscal}` segments**.

Two things follow.  First, the hypothesis `hdil` of
`Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` is *not* vacuous: it is met
by any sparse enough per-ball family, in particular whenever each piece of the cover meets the
shading of at most `δ^{-2 exscal}` tubes.  Second, this is the crispest form of the one
remaining obligation of the joint construction: a bound on how many tube shadings can meet one
piece of the `r₁`-ball cover. -/
theorem segs_dilation_of_card_le (core : BallDataCore cfg)
    (h : ∀ B ∈ core.bs, ((core.segs B).card : ENNReal) ≤ ((cfg.r₁ : ENNReal) ^ 2)⁻¹) :
    ∀ B ∈ core.bs,
      (cfg.r₁ : ENNReal) ^ 2 * maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) :=
  segs_dilation_of_maxDensity_le core fun B hB ↦
    le_trans (maxDensity_le_card _ _) (h B hB)

end Dilation

section Rigidity

/-- **A family whose aggregate fullness matches its pointwise density ceiling is rigid: the
total shading mass is determined.** -/
theorem sum_volume_shade_eq_of_fullness_ge {ι : Type*} (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {a : NNReal}
    (hfull : a ≤ ShadedBody.fullness s V)
    (hflat : ∀ i ∈ s, volume (V i).shade ≤ (a : ENNReal) * volume (V i).carrier) :
    ∑ i ∈ s, volume (V i).shade = ∑ i ∈ s, (a : ENNReal) * volume (V i).carrier := by
  refine le_antisymm (Finset.sum_le_sum hflat) ?_
  rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul, ← Finset.mul_sum]
  gcongr

/-- **`fullness_ge` is rigid: at the density ceiling, no member may lose any shading mass.**

If every member of a family has shading density at most `a` and the *aggregate* fullness is at
least `a`, then every member has density exactly `a`.

Read at `a = cfg.η`'s value `δ^η`, this is the rigidity of `Kakeya.VeryNotSticky.fullness_ge`.
`ShadedBody.IsRefinement` keeps carriers and only shrinks shadings, so a configuration refining
a family all of whose tubes have density exactly `δ^η` — which the target's binder `hfull`
permits, it asserting only the aggregate ratio `≥ δ^η` — must keep the **full shading measure**
of every tube it retains.  A joint construction of `cfg` and `bd` may therefore delete only
*null* sets from the shadings, which is exactly what `Kakeya.VeryNotSticky.deleteShade` does;
it may not delete a crumb of positive measure, however small.

`fullness_ge` is asserted at exactly the `δ^η` of the target's own binder, with no comparison
constant, and that is what makes it rigid; the same defect shape as
`Kakeya.VeryNotSticky.lam_ge` before its repair, as `BallData.segs_dilation` before its repair, and as `rho_count`. -/
theorem volume_shade_eq_of_fullness_ge {ι : Type*} (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {a : NNReal}
    (hfull : a ≤ ShadedBody.fullness s V)
    (hflat : ∀ i ∈ s, volume (V i).shade ≤ (a : ENNReal) * volume (V i).carrier) :
    ∀ i ∈ s, volume (V i).shade = (a : ENNReal) * volume (V i).carrier := by
  classical
  intro j hj
  by_contra hne
  have hlt : volume (V j).shade < (a : ENNReal) * volume (V j).carrier :=
    lt_of_le_of_ne (hflat j hj) hne
  have hsum := sum_volume_shade_eq_of_fullness_ge s V hfull hflat
  have hsplit₁ : ∑ i ∈ s, volume (V i).shade
      = volume (V j).shade + ∑ i ∈ s.erase j, volume (V i).shade :=
    (Finset.add_sum_erase s _ hj).symm
  have hsplit₂ : ∑ i ∈ s, (a : ENNReal) * volume (V i).carrier
      = (a : ENNReal) * volume (V j).carrier
        + ∑ i ∈ s.erase j, (a : ENNReal) * volume (V i).carrier :=
    (Finset.add_sum_erase s _ hj).symm
  have hBtop : ∑ i ∈ s.erase j, (a : ENNReal) * volume (V i).carrier ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top ENNReal.coe_ne_top ?_
    exact ((V i).toConvexSpaceBody.isCompact).measure_lt_top.ne
  have hAB : ∑ i ∈ s.erase j, volume (V i).shade
      ≤ ∑ i ∈ s.erase j, (a : ENNReal) * volume (V i).carrier :=
    Finset.sum_le_sum fun i hi ↦ hflat i (Finset.mem_of_mem_erase hi)
  have hcontr : ∑ i ∈ s, volume (V i).shade
      < ∑ i ∈ s, (a : ENNReal) * volume (V i).carrier := by
    rw [hsplit₁, hsplit₂]
    calc volume (V j).shade + ∑ i ∈ s.erase j, volume (V i).shade
        ≤ volume (V j).shade + ∑ i ∈ s.erase j, (a : ENNReal) * volume (V i).carrier := by
          gcongr
      _ < (a : ENNReal) * volume (V j).carrier
            + ∑ i ∈ s.erase j, (a : ENNReal) * volume (V i).carrier :=
          ENNReal.add_lt_add_right hBtop hlt
  exact absurd hsum (ne_of_lt hcontr)

end Rigidity

section Coarse

/-- **The coarse per-ball core: one "segment" per ball, and the segment *is* the ball.**

`Kakeya.VeryNotSticky.BallData.C₀` is a free field with no upper bound, and `segs_thickness`
asks the segment to have thickness profile `(r₁, δ, δ)` only *up to* `C₀`.  At `C₀ ≥ r₁/δ` the
closed ball of radius `r₁` has that profile, its thickness being exactly `r₁` at every rank
below the dimension.  So the whole of (C3) is realized by taking the segment family of a ball
to be the singleton `{B}` with `Y_B := B`, the parent family `𝕋(T_B)` being **every** tube whose
shading meets the piece `B̂`.

Three clauses that carry the geometric content of (C3) become vacuous at that choice, and that
is the point:

* `segs_dims` — a singleton family;
* `segs_core`, the *directional* clause, because a ball of radius `r₁ ≤ C₀ δ` lies in the
  `C₀δ`-neighbourhood of **every** line through its centre;
* `fibre`, because `Cm` is free and the fibre count lies between `1` and `|𝕋|`.

`segs_dilation` also becomes trivial, at `Cdil = 1`: a one-member family has `Δ_max = 1` and
`r₁ ≤ 1`.  The working shading of (C5′) is the (null-refined) uniform shading itself, at loss
`Cg = 1`.  With `Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` this closes
**all sixty-seven** fields of `BallData`; see `Kakeya.VeryNotSticky.nonempty_ballData_deleteShade`.

No threshold on `δ` is needed: `δ ≤ r₁` is `cfg.hdims`. -/
theorem exists_coarse_ballDataCore (cfg : VeryNotSticky.{u}) {D : ℕ}
    (hD : ballCoverConstant ≤ D) :
    ∃ (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) (hnull : volume S = 0)
      (core : BallDataCore (cfg.deleteShade S hS hnull)),
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B, 0 < volume (core.Y p).shade) ∧
      (∀ B ∈ core.bs, ((core.segs B).card : ENNReal) ≤ ((cfg.r₁ : ENNReal) ^ 2)⁻¹) ∧
      (cfg.r₁ : ℝ) ≤ (core.C₀ : ℝ) * (cfg.a : ℝ) := by
  classical
  -- ### scales
  have hδne : cfg.δ ≠ 0 := cfg.hδ.ne'
  have hδa : cfg.δ ≤ cfg.a := cfg.hdims.1
  have hδr₁ : cfg.δ ≤ cfg.r₁ := by
    refine le_trans hδa (le_trans cfg.hdims.2.1 ?_)
    simpa [VeryNotSticky.r₁] using cfg.hdims.2.2
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by
    have h : (0 : NNReal) < cfg.r₁ := by
      simpa [VeryNotSticky.r₁] using NNReal.rpow_pos cfg.hδ
    exact_mod_cast h
  have hr₁0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := hr₁pos.le
  have hr₁1 : cfg.r₁ ≤ 1 := r₁_le_one cfg
  have hδr₁R : (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) := by exact_mod_cast hδr₁
  -- ### the comparison constant
  have hC₀4 : (4 : NNReal) ≤ 4 + cfg.r₁ / cfg.δ := le_self_add
  have hC₀1 : (1 : NNReal) ≤ 4 + cfg.r₁ / cfg.δ := le_trans (by norm_num) hC₀4
  have hC₀δ : cfg.r₁ ≤ (4 + cfg.r₁ / cfg.δ) * cfg.δ := by
    rw [add_mul, div_mul_cancel₀ _ hδne]
    exact le_add_self
  have hC₀δR : (cfg.r₁ : ℝ) ≤ ((4 + cfg.r₁ / cfg.δ : NNReal) : ℝ) * (cfg.δ : ℝ) := by
    exact_mod_cast hC₀δ
  have hC₀1R : (1 : ℝ) ≤ ((4 + cfg.r₁ / cfg.δ : NNReal) : ℝ) := by exact_mod_cast hC₀1
  -- ### the ball cover of `cfg`, and the null crumbs
  obtain ⟨bι, bs₀, ctr, P, hbsne₀, hPball16, hPball, hPdisj, hPmeas, hPcov, hoverlap, hPne₀⟩ :=
    exists_ballCover cfg (iUnionShade_nonempty cfg)
  obtain ⟨S, hS, hnull, hcrumb⟩ := exists_null_crumbs cfg bs₀ P (fun B _ ↦ hPmeas B)
  refine ⟨S, hS, hnull, ?_⟩
  -- ### the parent family of a piece
  obtain ⟨fam, hfam⟩ : ∃ fam : bι → Finset cfg.ι, ∀ B i,
      i ∈ fam B ↔ (i ∈ cfg.s ∧ (((cfg.T i).shade \ S) ∩ P B).Nonempty) :=
    ⟨fun B ↦ cfg.s.filter (fun i ↦ (((cfg.T i).shade \ S) ∩ P B).Nonempty),
      fun B i ↦ by simp [Finset.mem_filter]⟩
  have hfam_sub : ∀ B, fam B ⊆ cfg.s := fun B i hi ↦ ((hfam B i).1 hi).1
  -- ### the coarse segment: the ball itself, shaded by what the piece retains
  obtain ⟨Y, hYcarr, hYshade⟩ :
      ∃ Y : bι → ShadedBody (EuclideanSpace ℝ (Fin 3)),
        (∀ B, (Y B).carrier = closedBall (ctr B) (cfg.r₁ : ℝ)) ∧
        (∀ B, (Y B).shade
          = (⋃ i ∈ (fam B : Set cfg.ι), (((cfg.T i).shade \ S) ∩ P B))
              ∩ closedBall (ctr B) (cfg.r₁ : ℝ)) :=
    ⟨fun B ↦
      { toConvexSpaceBody := ConvexSpaceBody.closedBall (ctr B) (cfg.r₁ : ℝ) hr₁0
        shade := (⋃ i ∈ (fam B : Set cfg.ι), (((cfg.T i).shade \ S) ∩ P B))
            ∩ closedBall (ctr B) (cfg.r₁ : ℝ)
        measurableSet_shade :=
          (MeasurableSet.biUnion (Finset.countable_toSet _) fun i _ ↦
            ((cfg.T i).measurableSet_shade.diff hS).inter (hPmeas B)).inter
              measurableSet_closedBall
        shade_subset := Set.inter_subset_right },
      fun B ↦ rfl, fun B ↦ rfl⟩
  -- `into` in raw form, and the reverse containment
  have hinto_raw : ∀ B ∈ bs₀, ∀ i ∈ fam B,
      ((cfg.T i).shade \ S) ∩ P B ⊆ (Y B).shade := by
    intro B hB i hi x hx
    rw [hYshade]
    refine ⟨Set.mem_biUnion (by simpa using hi) hx, ?_⟩
    exact hPball B hB hx.2
  have hback_raw : ∀ B, (Y B).shade ⊆ ⋃ i ∈ (fam B : Set cfg.ι), ((cfg.T i).shade \ S) := by
    intro B x hx
    rw [hYshade] at hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx.1
    exact Set.mem_biUnion hi hxi.1
  -- ### the `δ`-ball covers
  obtain ⟨γ, cov, covCtr, hcov, hmeets⟩ := exists_deltaCovers (δ := cfg.δ) cfg.hδ Y
  -- ### the retained balls
  obtain ⟨bs, hbs⟩ : ∃ bs : Finset bι, ∀ B, B ∈ bs ↔ (B ∈ bs₀ ∧ (fam B).Nonempty) :=
    ⟨bs₀.filter (fun B ↦ (fam B).Nonempty), fun B ↦ by simp [Finset.mem_filter]⟩
  have hbs_sub : ∀ B ∈ bs, B ∈ bs₀ := fun B h ↦ ((hbs B).1 h).1
  have hbs_subset : (bs : Set bι) ⊆ (bs₀ : Set bι) := by
    intro B hB
    exact Finset.mem_coe.2 (hbs_sub B (Finset.mem_coe.1 hB))
  -- ### thickness facts for the ball
  have hthick_lt : ∀ (x : EuclideanSpace ℝ (Fin 3)) {n : ℕ},
      n < 3 → Metric.thickness ℝ (closedBall x (cfg.r₁ : ℝ)) n = (cfg.r₁ : ℝ) := by
    intro x n hn
    refine le_antisymm (Metric.thickness_closedBall_le (𝕜 := ℝ) hr₁0 n) ?_
    refine Metric.thickness_closedBall_ge hr₁0 ?_
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from finrank_euclideanSpace_fin]
    exact hn
  have hthick_ge : ∀ (x : EuclideanSpace ℝ (Fin 3)) {n : ℕ},
      3 ≤ n → Metric.thickness ℝ (closedBall x (cfg.r₁ : ℝ)) n = 0 := by
    intro x n hn
    refine Metric.thickness_eq_zero_of_finrank_le (𝕜 := ℝ) ?_
    have h3 : Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
      rw [← Module.finrank_eq_rank]; simp
    rw [h3]
    exact_mod_cast Nat.cast_le.2 hn
  -- ### assembling the core
  refine ⟨{
    C₀ := 4 + cfg.r₁ / cfg.δ
    hC₀ := hC₀1
    D := D
    Yg := fun i ↦ ((cfg.deleteShade S hS hnull).T i).shade
    Yg_subset := fun _ _ ↦ subset_rfl
    Yg_measurable := fun i _ ↦ ((cfg.deleteShade S hS hnull).T i).measurableSet_shade
    Cg := 1
    hCg := le_rfl
    Yg_mass := by simp
    bι := bι
    σ := bι
    bs := bs
    bs_nonempty := ?_
    ctr := ctr
    P := P
    P_subset_ball := fun B hB ↦ hPball B (hbs_sub B hB)
    P_disjoint := hPdisj.subset hbs_subset
    P_measurable := fun B _ ↦ hPmeas B
    P_cover := ?_
    ballOverlap := fun x t ht hball ↦
      le_trans (hoverlap x t (fun B hB ↦ hbs_sub B (ht hB)) hball) hD
    segs := fun B ↦ ({B} : Finset bι)
    Y := Y
    fam := fam
    segs_nonempty := fun B _ ↦ Finset.singleton_nonempty B
    fam_subset := fun B _ p _ ↦ hfam_sub p
    fam_disjoint := fun B _ ↦ by simp
    Y_piece := ?_
    segs_thickness := ?_
    segs_dims := ?_
    parent := ?_
    into := ?_
    back := ?_
    segs_core := ?_
    m := 1
    Cm := max 1 (cfg.s.card : NNReal)
    hCm := le_max_left _ _
    fibre := ?_
    γ := γ
    cov := cov
    covCtr := covCtr
    cov_isCover := fun _ _ p _ ↦
      ⟨(hcov p).subset_iUnion, fun x ↦ le_trans ((hcov p).card_filter_le x) hD⟩
    cov_meets := fun _ _ p _ ↦ hmeets p
    segs_subset_ball := ?_
    segs_scale := ?_ }, ?_, ?_, ?_⟩
  · -- bs_nonempty
    obtain ⟨x, hx⟩ := iUnionShade_nonempty (cfg.deleteShade S hS hnull)
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    have hxi' : x ∈ (cfg.T i).shade \ S := by simpa using hxi
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 (hPcov i hi hxi'.1)
    exact ⟨B, (hbs B).2 ⟨hB, ⟨i, (hfam B i).2 ⟨hi, ⟨x, hxi', hxB⟩⟩⟩⟩⟩
  · -- P_cover
    intro i hi x hx
    have hx' : x ∈ (cfg.T i).shade \ S := by simpa using hx
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 (hPcov i hi hx'.1)
    exact Set.mem_biUnion ((hbs B).2 ⟨hB, ⟨i, (hfam B i).2 ⟨hi, ⟨x, hx', hxB⟩⟩⟩⟩) hxB
  · -- Y_piece
    intro B hB p hp
    rw [Finset.mem_singleton] at hp
    rw [hp, hYshade]
    intro x hx
    obtain ⟨i, -, hxi⟩ := Set.mem_iUnion₂.1 hx.1
    exact hxi.2
  · -- segs_thickness
    intro B hB p hp k
    rw [hYcarr]
    have hk3 : (k : ℕ) < 3 := k.2
    rw [hthick_lt (ctr p) hk3]
    have htk : (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) k ≤ (cfg.r₁ : ℝ) := by
      fin_cases k <;> simp [hδr₁R]
    have htk0 : (0 : ℝ) ≤ (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) k := by
      fin_cases k <;> simp
    have hup : (cfg.r₁ : ℝ) ≤ ((4 + cfg.r₁ / cfg.δ : NNReal) : ℝ) *
        (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) k := by
      fin_cases k
      · simpa using le_mul_of_one_le_left hr₁0 hC₀1R
      · simpa using hC₀δR
      · simpa using hC₀δR
    refine ⟨?_, hup⟩
    calc ((4 + cfg.r₁ / cfg.δ : NNReal) : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) k
        ≤ 1 * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) k := by
          gcongr
          exact inv_le_one_of_one_le₀ hC₀1R
      _ = (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) k := one_mul _
      _ ≤ (cfg.r₁ : ℝ) := htk
  · -- segs_dims
    intro B hB p hp q hq n
    have h2 : (2 • Metric.thickness ℝ (Y q).carrier) n
        = 2 * Metric.thickness ℝ (Y q).carrier n := by simp
    rw [h2, hYcarr, hYcarr]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · rw [hthick_lt (ctr p) hn, hthick_lt (ctr q) hn]
      linarith
    · rw [hthick_ge (ctr p) hn, hthick_ge (ctr q) hn]
      norm_num
  · -- parent
    intro B hB i hi hne
    have hne' : (((cfg.T i).shade \ S) ∩ P B).Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, by simpa using hx.1, hx.2⟩
    exact ⟨B, Finset.mem_singleton_self B, (hfam B i).2 ⟨hi, hne'⟩⟩
  · -- into
    intro B hB p hp i hi x hx
    rw [Finset.mem_singleton] at hp
    have hiB : i ∈ fam B := by rw [← hp]; exact hi
    rw [hp]
    exact hinto_raw B (hbs_sub B hB) i hiB ⟨by simpa using hx.1, hx.2⟩
  · -- back
    intro B hB p hp x hx
    rw [Finset.mem_singleton] at hp
    rw [hp] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hback_raw B hx)
    have hiF : i ∈ fam B := Finset.mem_coe.1 hi
    have hxi' : x ∈ ((cfg.deleteShade S hS hnull).T i).shade := hxi
    exact Set.mem_biUnion hiF hxi'
  · -- segs_core
    intro B hB p hp i hi
    refine ⟨ctr p, ?_⟩
    rw [hYcarr]
    intro x hx
    refine Metric.mem_cthickening_of_dist_le x (ctr p) _ _ ?_ ?_
    · exact AffineSubspace.self_mem_mk' _ _
    · calc dist x (ctr p) ≤ (cfg.r₁ : ℝ) := Metric.mem_closedBall.1 hx
        _ ≤ ((4 + cfg.r₁ / cfg.δ : NNReal) : ℝ) * (cfg.δ : ℝ) := hC₀δR
  · -- fibre
    intro B hB p hp x hx
    rw [Finset.mem_singleton] at hp
    rw [hp] at hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hback_raw B hx)
    set F : Finset (cfg.deleteShade S hS hnull).ι :=
      {j ∈ fam p | x ∈ ((cfg.deleteShade S hS hnull).T j).shade} with hFdef
    have hmemi : i ∈ F := by
      rw [hFdef]
      refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · rw [hp]
        exact (by simpa using hi : i ∈ fam B)
      · simpa using hxi
    have hcard1 : (1 : ENNReal) ≤ (F.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.2 ⟨i, hmemi⟩
    have hsub : F.card ≤ cfg.s.card := by
      refine Finset.card_le_card ?_
      intro j hj
      rw [hFdef] at hj
      exact hfam_sub p (Finset.mem_of_mem_filter j hj)
    have hmax1 : (1 : ENNReal) ≤ ((max 1 (cfg.s.card : NNReal) : NNReal) : ENNReal) := by
      exact_mod_cast le_max_left (1 : NNReal) (cfg.s.card : NNReal)
    have hcards : (F.card : ENNReal) ≤ ((max 1 (cfg.s.card : NNReal) : NNReal) : ENNReal) := by
      calc (F.card : ENNReal) ≤ ((cfg.s.card : ℕ) : ENNReal) := by exact_mod_cast hsub
        _ = ((cfg.s.card : NNReal) : ENNReal) := by simp
        _ ≤ ((max 1 (cfg.s.card : NNReal) : NNReal) : ENNReal) := by
            exact_mod_cast le_max_right (1 : NNReal) (cfg.s.card : NNReal)
    refine ⟨?_, ?_⟩
    · simpa using mul_le_mul' hmax1 hcard1
    · simpa using hcards
  · -- segs_subset_ball
    intro B hB p hp
    rw [Finset.mem_singleton] at hp
    rw [hp, hYcarr]
    exact subset_rfl
  · -- segs_scale
    intro B hB p hp
    rw [hYcarr, Metric.ethickness.le_scale_iff]
    intro n
    calc (cfg.δ : ENNReal) ≤ (cfg.r₁ : ENNReal) := by exact_mod_cast hδr₁
      _ ≤ Metric.ethickness ℝ (closedBall (ctr p) (cfg.r₁ : ℝ)) (n : ℕ) :=
          _root_.le_ethickness_closedBall cfg.r₁ n.2
  · -- shade positivity
    intro B hB p hp
    rw [Finset.mem_singleton] at hp
    obtain ⟨i, hi⟩ := ((hbs B).1 hB).2
    obtain ⟨hiS, hne⟩ := (hfam B i).1 hi
    have hposi : 0 < volume (((cfg.T i).shade \ S) ∩ P B) := hcrumb i hiS B (hbs_sub B hB) hne
    rw [hp]
    exact lt_of_lt_of_le hposi (measure_mono (hinto_raw B (hbs_sub B hB) i hi))
  · -- the cardinality bound
    intro B hB
    have h1 : (((({B} : Finset bι)).card : ℕ) : ENNReal) = 1 := by simp
    rw [h1]
    have hr2 : ((cfg.r₁ : ENNReal)) ^ 2 ≤ 1 := by
      have : (cfg.r₁ : ENNReal) ≤ 1 := by exact_mod_cast hr₁1
      calc ((cfg.r₁ : ENNReal)) ^ 2 ≤ (1 : ENNReal) ^ 2 := by gcongr
        _ = 1 := one_pow 2
    simpa using (ENNReal.inv_le_inv (a := 1) (b := (cfg.r₁ : ENNReal) ^ 2)).2 hr2
  · -- the scale condition
    calc (cfg.r₁ : ℝ) ≤ ((4 + cfg.r₁ / cfg.δ : NNReal) : ℝ) * (cfg.δ : ℝ) := hC₀δR
      _ ≤ ((4 + cfg.r₁ / cfg.δ : NNReal) : ℝ) * (cfg.a : ℝ) := by gcongr

/-- **All sixty-seven fields of `BallData`, for a free refinement of every configuration.**

`Kakeya.VeryNotSticky.exists_coarse_ballDataCore` supplies the forty-two core fields with a
one-member segment family per ball, so `segs_dilation` follows, at `Cdil = 1`, from
`Kakeya.VeryNotSticky.segs_dilation_of_card_le`, and
`Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` supplies the other
twenty-five.

**Read this as a fidelity finding, not as progress on `exists_setup_caseSideData`.**  What it
says is that `BallData`, as a statement, constrains almost nothing: it is satisfiable for a
free (constant-`1`, null) refinement of *every* configuration, by data in which "segments" are
balls and "bodies" are balls, at constants `C₀ ≈ r₁/δ`, `Cm ≈ |𝕋|`, `CF`, `Cbias` large and
`c₁` small.  All of the quantitative content of Configuration `hyp:ml2setup` therefore lives in
`Kakeya.VeryNotSticky.CaseSideData`, which bounds `C₀` and `Cbias` from above
(`ThickDensityThresholds.bias`) and `c₁` from below (`ThickDensityThresholds.plankF`, and
`CaseScale` through `ThinConfig.C`), and in the *statement* `segs_dilation` only through those
bounds. -/
theorem nonempty_ballData_deleteShade (cfg : VeryNotSticky.{u}) :
    ∃ (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) (hnull : volume S = 0),
      Nonempty (BallData (cfg.deleteShade S hS hnull)) := by
  obtain ⟨S, hS, hnull, core, hshade, hcard, hC₀a⟩ :=
    exists_coarse_ballDataCore cfg (D := ballCoverConstant) le_rfl
  refine ⟨S, hS, hnull, ?_⟩
  exact BallDataCore.nonempty_ballData_of_dilation core hshade hC₀a le_rfl
    (fun B hB ↦ by
      rw [ENNReal.coe_one, one_mul]
      exact segs_dilation_of_card_le core hcard B hB)

end Coarse

end Kakeya.VeryNotSticky
