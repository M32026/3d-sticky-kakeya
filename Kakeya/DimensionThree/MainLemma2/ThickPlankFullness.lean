/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickCase

/-!
# The two volume fields of the thick-case plank presentation (row G10c)

This file proves fields **15** (`fullness_ge`) and **17** (`volume_le`) of
`Kakeya.VeryNotSticky.ThickPlankPresentation` — blueprint `lem:ml2thickPlank`(iv) and (ii) —
and, as the input `Kakeya.VeryNotSticky.thickPlankSelection_of_edImages` demands of its caller,
the volume comparison `hKvol` itself (`Kakeya.VeryNotSticky.thickPlank_hKvol`).

Both fields are stated over the data the normalisation row
(`Kakeya.VeryNotSticky.exists_thickPlankNormalisation`) produces and over nothing else. The
file imports only `Kakeya.DimensionThree.MainLemma2.ThickCase`: it is deliberately independent
of `ThickPlankNormalise` and `ThickPlankSelect`, so that it can be checked, and existing, without
them.

## Field 17, `volume_le`

`|U(𝒫_sel, Y_𝒫)| |W| ≤ |B̄(0, Plank.windowRadius)| |U(𝕋_{B,W}, Y_B) ∩ W|`.

With the transported shadings `(P_p).shade = L(Y_p^{shade})` the shaded union of the selection
is contained in `L(U(𝕋_{B,W}, Y_B) ∩ W)` — each `Y_p^{shade}` lies in `Y_p` and hence in `W`
(`BallData.segs_le`) — so its volume is `|det L|` times the right-hand union's; and
`|det L| |W| = |L(W)| ≤ |B̄(0,4)|`. Both uses of `|det L|` are `Kakeya.volume_affineImage` on
the *same* affine equivalence, so the Jacobian is never evaluated and
`Plank.jacobian_eq` is not needed.

**The docstring of the field cites a lemma that does not exist.**
`ThickPlankInterface.lean:592–600` names `Kakeya/DimensionThree/Plank/NormalisedVolume.lean`
and `Kakeya.volume_preimage_thickenedNbhd_inter_le` as the source of this field; neither the
file nor the lemma is in the tree (measured; and see  §D1, which found the same
phantom block). `Kakeya.VeryNotSticky.thickPlank_volume_le` below is the replacement, proved
from `Kakeya.volume_affineImage` alone.

## Field 15, `fullness_ge`

`CP⁻¹ λ(𝕋_{B,W}, Y_B) ≤ λ(𝒫_sel, Y_𝒫)`, `λ = (∑ |shade|)/(∑ |carrier|)`.

Numerator: `∑_{sel}|P_p^{shade}| = |det L| ∑_{sel}|Y_p^{shade}| ≥ |det L| C_sel⁻¹
∑_{block}|Y_p^{shade}|`, the retention clause of
`Kakeya.VeryNotSticky.thickPlankSelection_of_edImages_shade`.

Denominator: every plank has the *same* carrier volume `8 a' b'`
(`Prism3D.volume_carrier`), and `8 a' b' ≤ C_e |L(Y_p)|` is exactly the `hKvol` hypothesis that
the selection lemma already carries, so `∑_{sel}|P_p| ≤ C_e |det L| ∑_{block}|Y_p|`.

The Jacobian cancels between the two, which is why the constant is the `δ`-free `C_sel · C_e`
and no comparison of `a'b'` with `δ²/(ab)` enters. That matters here: after
 the plank dimensions are **capped**, `a' = min (4C₀δ/r₁ / b_W) 1`, so
`a' b'` is *not* `δ²/(ab)` in general — and this proof never asks it to be.

## `hKvol`, the input `thickPlankSelection_of_edImages` demands

`8 a' b' ≤ C_e |L(Y_p)|` is *not* `Kakeya.VeryNotSticky.plankEnclosureVolume`, whose conclusion
compares a plank with the rescaled **body** `L_B(W)` at the body's own dimensions
`C₀ a/r₁, C₀ b/r₁` — a different comparison, weaker by `ab/δ²`.
`Kakeya.VeryNotSticky.thickPlank_hKvol` proves the segment-level form from
`Kakeya.VeryNotSticky.thickSegVol`, `Kakeya.VeryNotSticky.thickBodyVol` and the capped
comparabilities `a' ≤ 4 C₀ δ/b`, `b' ≤ 4 C₀ δ/a` of `ThickPlankNormalise`, at the `δ`-free
arithmetic condition `6144 C₀⁸ ≤ C_e c_W`, where `c_W` is a `δ`-free lower bound for `|L(W)|`.

## What the normalisation row still owes

Two clauses that `exists_thickPlankNormalisation` does not currently export, and that appear
here as explicit binders:

* `hLwin : L(W_j) ⊆ B̄(0, Plank.windowRadius)` — field 17. It is immediate inside that proof
  (`f '' W.carrier ⊆ B̄(0,1)` for the enclosing plank `W ⊇ L_B(W_j)`), but is discarded;
* `c_W ≤ |L(W_j)|` with `c_W` `δ`-free — `thickPlank_hKvol`, and the same binder field 18
  (`ThickPlankNonconc.lean`) already takes. `|f '' W.carrier| = 8κ³` by
  `Plank.image_carrier_eq_cube`, and the enclosure `|W| ≤ 48 C₀⁶ |L_B(W_j)|` converts it.

Neither is a mathematical gap; both are exports.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric ShadedBody

universe u

/-- The ratio step of field 15, isolated: a common factor `J` in numerator and denominator
cancels, and the two constants come out as `(C_sel C_e)⁻¹`. No positivity of `A`, `B` or of the
selected sums is needed — the degenerate cases go through the `[0,∞]` arithmetic unchanged. -/
theorem fullness_ratio_aux {A B As' Bs' J Csel Ce : ENNReal}
    (hJ0 : J ≠ 0) (hJt : J ≠ ⊤) (hCe0 : Ce ≠ 0) (hCet : Ce ≠ ⊤)
    (h1 : J * (Csel⁻¹ * A) ≤ As') (h2 : Bs' ≤ Ce * (J * B)) :
    (Csel * Ce)⁻¹ * (A / B) ≤ As' / Bs' := by
  have h2' : Bs' ≤ J * (Ce * B) := by
    refine h2.trans (le_of_eq ?_); ring
  have hkey : (J * (Csel⁻¹ * A)) / (J * (Ce * B)) ≤ As' / Bs' :=
    ENNReal.div_le_div h1 h2'
  refine le_trans (le_of_eq ?_) hkey
  rw [ENNReal.mul_div_mul_left _ _ hJ0 hJt, ENNReal.mul_inv (Or.inr hCet) (Or.inr hCe0),
    div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hCe0) (Or.inl hCet)]
  ring

open scoped Classical in
/-- **Field 17 of `Kakeya.VeryNotSticky.ThickPlankPresentation`** (blueprint
`lem:ml2thickPlank`(ii), first display), from the normalisation data.

`hPshade` and `hsel` are fields 9 and 11; `hLwin` is the clause the normalisation row owes
(see the module docstring). No selection retention, no `hKvol` and no cardinality clause is
used: **field 17 is independent of R31.** -/
theorem thickPlank_volume_le
    (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι} (hB : B ∈ bd.bs)
    {j : bd.ω}
    {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
    (P : bd.σ → ShadedPlank a' b' hab' hb1')
    (sel : Finset bd.σ) (hsel : sel ⊆ (bd.segs B).filter fun p => bd.blk p = j)
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hshade : ∀ q ∈ sel, ((P q).shade : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ⇑L '' ((bd.Y q).shade))
    (hLwin : ⇑L '' ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius) :
    volume (iUnionShade sel (fun p => (P p).toShadedBody)) *
        volume (bd.Wb j).carrier ≤
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
          Plank.windowRadius) *
        volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
          (bd.Wb j).carrier) := by
  classical
  set J : ENNReal := ENNReal.ofReal
    |LinearMap.det ((L.linear : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))| with hJdef
  have hJvol : ∀ S : Set (EuclideanSpace ℝ (Fin 3)), volume (⇑L '' S) = J * volume S := by
    intro S
    simpa [hJdef] using Kakeya.volume_affineImage L S
  set U : Set (EuclideanSpace ℝ (Fin 3)) :=
    (⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
      (bd.Wb j).carrier with hUdef
  have hsub : iUnionShade sel (fun p => (P p).toShadedBody) ⊆ ⇑L '' U := by
    intro x hx
    simp only [iUnionShade, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨q, hq, hxq⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hshade q hq hxq
    have hqblk := Finset.mem_filter.mp (hsel hq)
    refine ⟨y, ⟨?_, ?_⟩, rfl⟩
    · exact Set.mem_biUnion (hsel hq) hy
    · have h1 : y ∈ ((bd.Y q).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
        (bd.Y q).shade_subset hy
      have h2 := bd.segs_le B hB q hqblk.1
      rw [hqblk.2] at h2
      exact h2 h1
  calc volume (iUnionShade sel (fun p => (P p).toShadedBody)) * volume (bd.Wb j).carrier
      ≤ volume (⇑L '' U) * volume (bd.Wb j).carrier := by gcongr
    _ = volume U * (J * volume (bd.Wb j).carrier) := by rw [hJvol]; ring
    _ = volume U * volume (⇑L '' ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
        rw [hJvol]
    _ ≤ volume U * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
          Plank.windowRadius) := by gcongr
    _ = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius)
          * volume U := by ring

open scoped Classical in
/-- **Field 15 of `Kakeya.VeryNotSticky.ThickPlankPresentation`** (blueprint
`lem:ml2thickPlank`(iv)), from the normalisation data and the *one* selection of
`Kakeya.VeryNotSticky.thickPlankSelection_of_edImages_shade`.

`hret` is that lemma's weight-retention conjunct at `y p = |Y_p^{shade}|`; `hKvol` is its own
`hKvol` hypothesis read at `K p = L(Y_p)`, which `Kakeya.VeryNotSticky.thickPlank_hKvol`
supplies. The field holds at any `CP ≥ C_sel C_e`.

**Field 15 consumes R31**, through `hret`: the retention clause is a conclusion of the
essentially-distinct selection, and that selection needs the pairwise-ED segments of GWZ
l.2013. It does *not* consume `sel_card`. -/
theorem thickPlank_fullness_ge
    (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι}
    {j : bd.ω}
    {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
    (P : bd.σ → ShadedPlank a' b' hab' hb1')
    (sel : Finset bd.σ) (hsel : sel ⊆ (bd.segs B).filter fun p => bd.blk p = j)
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hPshade : ∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = j),
      ((P p).shade : Set (EuclideanSpace ℝ (Fin 3))) = ⇑L '' ((bd.Y p).shade))
    {Ce : NNReal} (hCe : 0 < Ce)
    (hKvol : ∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = j),
      8 * (a' : ENNReal) * (b' : ENNReal)
        ≤ (Ce : ENNReal) * volume (⇑L '' ((bd.Y p).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
    {Csel : NNReal} (hCsel : 0 < Csel)
    (hret : (Csel : ENNReal)⁻¹ * ∑ p ∈ (bd.segs B).filter (fun q => bd.blk q = j),
        volume (bd.Y p).shade ≤ ∑ p ∈ sel, volume (bd.Y p).shade)
    {CP : NNReal} (hCP : Csel * Ce ≤ CP) :
    CP⁻¹ * ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = j) bd.Y ≤
      ShadedBody.fullness sel (fun p => (P p).toShadedBody) := by
  classical
  set J : ENNReal := ENNReal.ofReal
    |LinearMap.det ((L.linear : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))| with hJdef
  have hJvol : ∀ S : Set (EuclideanSpace ℝ (Fin 3)), volume (⇑L '' S) = J * volume S := by
    intro S
    simpa [hJdef] using Kakeya.volume_affineImage L S
  have hJ0 : J ≠ 0 := by
    simpa [hJdef] using Kakeya.ofReal_abs_det_affineEquiv_ne_zero L
  have hJt : J ≠ ⊤ := ENNReal.ofReal_ne_top
  have hCe0 : (Ce : ENNReal) ≠ 0 := by simpa using hCe.ne'
  have hCet : (Ce : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- numerator
  have h1 : J * ((Csel : ENNReal)⁻¹ *
        ∑ p ∈ (bd.segs B).filter (fun q => bd.blk q = j), volume (bd.Y p).shade)
      ≤ ∑ p ∈ sel, volume ((P p).toShadedBody).shade := by
    have hEq : ∑ p ∈ sel, volume ((P p).toShadedBody).shade
        = J * ∑ p ∈ sel, volume (bd.Y p).shade := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have := hPshade p (hsel hp)
      calc volume (((P p).toShadedBody).shade : Set (EuclideanSpace ℝ (Fin 3)))
          = volume (⇑L '' ((bd.Y p).shade)) := congrArg volume this
        _ = J * volume (bd.Y p).shade := hJvol _
    rw [hEq]
    gcongr
  -- denominator
  have h2 : ∑ p ∈ sel, volume ((P p).toShadedBody).carrier
      ≤ (Ce : ENNReal) * (J *
        ∑ p ∈ (bd.segs B).filter (fun q => bd.blk q = j), volume (bd.Y p).carrier) := by
    have hstep : ∀ p ∈ sel, volume ((P p).toShadedBody).carrier
        ≤ (Ce : ENNReal) * (J * volume (bd.Y p).carrier) := by
      intro p hp
      have hv : volume (((P p).toShadedBody).carrier
          : Set (EuclideanSpace ℝ (Fin 3))) = 8 * (a' : ENNReal) * (b' : ENNReal) := by
        simpa using Prism3D.volume_carrier ((P p).toPrism3D)
      rw [hv, ← hJvol]
      exact hKvol p (hsel hp)
    calc ∑ p ∈ sel, volume ((P p).toShadedBody).carrier
        ≤ ∑ p ∈ sel, (Ce : ENNReal) * (J * volume (bd.Y p).carrier) :=
          Finset.sum_le_sum hstep
      _ = (Ce : ENNReal) * (J * ∑ p ∈ sel, volume (bd.Y p).carrier) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (Ce : ENNReal) * (J *
            ∑ p ∈ (bd.segs B).filter (fun q => bd.blk q = j), volume (bd.Y p).carrier) := by
          gcongr
  have hratio := fullness_ratio_aux hJ0 hJt hCe0 hCet h1 h2
  have hCP0 : CP ≠ 0 := by
    have : (0 : NNReal) < Csel * Ce := mul_pos hCsel hCe
    exact (lt_of_lt_of_le this hCP).ne'
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_inv hCP0, coe_fullness, coe_fullness]
  refine le_trans ?_ hratio
  have hle : ((Csel : ENNReal) * (Ce : ENNReal)) ≤ (CP : ENNReal) := by
    rw [← ENNReal.coe_mul]
    exact_mod_cast hCP
  gcongr

/-- The scalar core of `Kakeya.VeryNotSticky.thickPlank_hKvol`, in `ℝ≥0`: both sides are
`1024 C₀⁵ r₁ δ²` at the threshold, so the constant `6144 C₀⁸` is exact for this route. -/
theorem thickKvol_arith {C₀ Ce cW r₁ dl a b : NNReal} (ha : 0 < a) (hb : 0 < b)
    (hC₀ : 0 < C₀) (hCe : 6144 * C₀ ^ (8 : ℕ) ≤ Ce * cW) :
    128 * C₀ ^ (2 : ℕ) * (dl / b) * (dl / a) * (8 * C₀ ^ (3 : ℕ) * r₁ * b * a)
      ≤ Ce * cW * ((6 * C₀ ^ (3 : ℕ))⁻¹ * (r₁ * dl ^ (2 : ℕ))) := by
  have hL : 128 * C₀ ^ (2 : ℕ) * (dl / b) * (dl / a) * (8 * C₀ ^ (3 : ℕ) * r₁ * b * a)
      = 1024 * C₀ ^ (5 : ℕ) * r₁ * dl ^ (2 : ℕ) := by
    field_simp
    ring
  have hR : Ce * cW * ((6 * C₀ ^ (3 : ℕ))⁻¹ * (r₁ * dl ^ (2 : ℕ)))
      = (Ce * cW) / (6 * C₀ ^ (3 : ℕ)) * (r₁ * dl ^ (2 : ℕ)) := by
    rw [div_eq_mul_inv]; ring
  have hdiv : (1024 : NNReal) * C₀ ^ (5 : ℕ) ≤ Ce * cW / (6 * C₀ ^ (3 : ℕ)) := by
    rw [le_div_iff₀ (show (0 : NNReal) < 6 * C₀ ^ (3 : ℕ) by positivity)]
    calc (1024 : NNReal) * C₀ ^ (5 : ℕ) * (6 * C₀ ^ (3 : ℕ)) = 6144 * C₀ ^ (8 : ℕ) := by ring
      _ ≤ Ce * cW := hCe
  rw [hL, hR]
  calc (1024 : NNReal) * C₀ ^ (5 : ℕ) * r₁ * dl ^ (2 : ℕ)
      = (1024 * C₀ ^ (5 : ℕ)) * (r₁ * dl ^ (2 : ℕ)) := by ring
    _ ≤ (Ce * cW / (6 * C₀ ^ (3 : ℕ))) * (r₁ * dl ^ (2 : ℕ)) := by gcongr
open scoped Classical in
/-- **The `hKvol` input of `Kakeya.VeryNotSticky.thickPlankSelection_of_edImages`**, at
`K p = L(Y_p)`: the plank volume `8 a' b'` is at most `C_e` times the volume of the normalised
segment.

This is the obligation (2) leaves to this row, and it is *not*
`Kakeya.VeryNotSticky.plankEnclosureVolume` (see the module docstring). Inputs: the capped
comparabilities of `ThickPlankNormalise`, `thickSegVol`, `thickBodyVol`, and a `δ`-free lower
bound `c_W` for `|L(W_j)|`. -/
theorem thickPlank_hKvol
    (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι} (hB : B ∈ bd.bs)
    {j : bd.ω} (hj : j ∈ bd.bodies B)
    {a' b' : NNReal}
    (hup_a : a' ≤ 4 * bd.C₀ * (cfg.δ / cfg.b)) (hup_b : b' ≤ 4 * bd.C₀ * (cfg.δ / cfg.a))
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    {cW : NNReal}
    (hLW : (cW : ENNReal)
      ≤ volume (⇑L '' ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
    {Ce : NNReal} (hCe : 6144 * bd.C₀ ^ (8 : ℕ) ≤ Ce * cW) :
    ∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = j),
      8 * (a' : ENNReal) * (b' : ENNReal)
        ≤ (Ce : ENNReal) * volume (⇑L '' ((bd.Y p).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
  classical
  intro p hp
  have hC₀pos : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  have hapos : (0 : NNReal) < cfg.a := cfg_a_pos cfg
  have hbpos : (0 : NNReal) < cfg.b := cfg_b_pos cfg
  have hr₁pos : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  set J : ENNReal := ENNReal.ofReal
    |LinearMap.det ((L.linear : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))| with hJdef
  have hJvol : ∀ S : Set (EuclideanSpace ℝ (Fin 3)), volume (⇑L '' S) = J * volume S := by
    intro S
    simpa [hJdef] using Kakeya.volume_affineImage L S
  set T : ENNReal := ((8 * bd.C₀ ^ (3 : ℕ) * cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal) with hTdef
  have hT0 : T ≠ 0 := by
    have : (0 : NNReal) < 8 * bd.C₀ ^ (3 : ℕ) * cfg.r₁ * cfg.b * cfg.a := by positivity
    simpa [hTdef] using this.ne'
  have hTt : T ≠ ⊤ := by rw [hTdef]; exact ENNReal.coe_ne_top
  have hTle : (cW : ENNReal) ≤ J * T := by
    calc (cW : ENNReal)
        ≤ volume (⇑L '' ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := hLW
      _ = J * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := hJvol _
      _ ≤ J * T := by
          gcongr
          simpa [hTdef] using (thickBodyVol cfg bd hB hj).2
  have hV0 : (((6 * bd.C₀ ^ (3 : ℕ) : NNReal))⁻¹ * (cfg.r₁ * cfg.δ ^ (2 : ℕ)) : NNReal)
      ≤ volume ((bd.Y p).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    refine le_trans (le_of_eq ?_) (thickSegVol cfg bd hB (Finset.mem_filter.mp hp).1).1
    rw [ENNReal.coe_mul, ENNReal.coe_inv (by positivity)]
  have hup : 8 * (a' : ENNReal) * (b' : ENNReal)
      ≤ ((128 * bd.C₀ ^ (2 : ℕ) * (cfg.δ / cfg.b) * (cfg.δ / cfg.a) : NNReal) : ENNReal) := by
    calc 8 * (a' : ENNReal) * (b' : ENNReal)
        ≤ 8 * ((4 * bd.C₀ * (cfg.δ / cfg.b) : NNReal) : ENNReal)
            * ((4 * bd.C₀ * (cfg.δ / cfg.a) : NNReal) : ENNReal) := by
          gcongr
      _ = _ := by push_cast; ring
  have harith : ((128 * bd.C₀ ^ (2 : ℕ) * (cfg.δ / cfg.b) * (cfg.δ / cfg.a) : NNReal) : ENNReal)
        * T
      ≤ (Ce : ENNReal) * (cW : ENNReal)
        * ((((6 * bd.C₀ ^ (3 : ℕ) : NNReal))⁻¹ * (cfg.r₁ * cfg.δ ^ (2 : ℕ)) : NNReal)
            : ENNReal) := by
    rw [hTdef, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    exact_mod_cast thickKvol_arith hapos hbpos hC₀pos hCe
  refine le_trans hup ?_
  refine (ENNReal.mul_le_mul_iff_left hT0 hTt).mp ?_
  calc ((128 * bd.C₀ ^ (2 : ℕ) * (cfg.δ / cfg.b) * (cfg.δ / cfg.a) : NNReal) : ENNReal) * T
      ≤ (Ce : ENNReal) * (cW : ENNReal)
        * ((((6 * bd.C₀ ^ (3 : ℕ) : NNReal))⁻¹ * (cfg.r₁ * cfg.δ ^ (2 : ℕ)) : NNReal)
            : ENNReal) := harith
    _ ≤ (Ce : ENNReal) * (J * T)
        * ((((6 * bd.C₀ ^ (3 : ℕ) : NNReal))⁻¹ * (cfg.r₁ * cfg.δ ^ (2 : ℕ)) : NNReal)
            : ENNReal) := by gcongr
    _ = ((Ce : ENNReal) * (J * ((((6 * bd.C₀ ^ (3 : ℕ) : NNReal))⁻¹
          * (cfg.r₁ * cfg.δ ^ (2 : ℕ)) : NNReal) : ENNReal))) * T := by ring
    _ ≤ ((Ce : ENNReal) * (J * volume ((bd.Y p).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
          * T := by gcongr
    _ = ((Ce : ENNReal)
          * volume (⇑L '' ((bd.Y p).carrier : Set (EuclideanSpace ℝ (Fin 3))))) * T := by
        rw [hJvol]

/-! ### Fidelity tripwires

Each `example` restates the field it produces, verbatim, and discharges it by projection out of
`Kakeya.VeryNotSticky.ThickPlankPresentation`. If either field's text drifts — the constant
moved, the block replaced by `sel`, the window radius changed — the corresponding `example`
stops compiling. -/

/-- Fidelity tripwire for field 17, `volume_le`. -/
example {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι} {j : bd.ω}
    {CP Θ C_NC : NNReal} (h : ThickPlankPresentation bd B j CP Θ C_NC) :
    volume (iUnionShade h.sel (fun p => (h.P p).toShadedBody)) *
        volume (bd.Wb j).carrier ≤
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
          Plank.windowRadius) *
        volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
          (bd.Wb j).carrier) :=
  h.volume_le

/-- Fidelity tripwire for field 15, `fullness_ge`. -/
example {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι} {j : bd.ω}
    {CP Θ C_NC : NNReal} (h : ThickPlankPresentation bd B j CP Θ C_NC) :
    CP⁻¹ * ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = j) bd.Y ≤
      ShadedBody.fullness h.sel (fun p => (h.P p).toShadedBody) :=
  h.fullness_ge

end Kakeya.VeryNotSticky
