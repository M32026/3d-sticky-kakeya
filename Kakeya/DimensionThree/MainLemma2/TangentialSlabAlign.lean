/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.TangentialSlabFamily
public import Kakeya.DimensionThree.MainLemma2.SlabMultKTGeneral

/-!
# The aligned anisotropic transport: clause (A2) at a `δ`-free constant

**What this file settles.** GWZ's tangential case charges the factor `δ^{-O(τ')}` of (105)
(`gwz.txt` l.2350-2352, l.2392-2396) to the **multiplicity**: it is the number of slabs
`𝕎''_S` that one fibre `𝕎''_{Y}(x)` can meet, which (103) bounds by `δ^{-O(τ')}` because the
fibre spans the typical angle `θ ≤ δ^{-τ'} a/b` while each slab spans only the slab's own
angular width `a/b`. Inside one slab GWZ pay nothing: the linear change of variables
"converts `S` to `B₁` and converts `𝕎''_S` to a set `𝕋̃` of `ρ₂`-tubes in `B₁`" with
`λ(𝕋̃, Y_𝕋̃) = λ(𝕎''_S, Y_{𝕎''_S})` — *equality*, no fullness loss.

The tree already charges the fibre count where GWZ do: the `δ^{-2τ'}` is written out in the
statement of `Kakeya.VeryNotSticky.tangentialSlabDecomp` and budgeted at the quarter
`C_sep·τ'/4` (see `Kakeya.VeryNotSticky.slabDecompFibreConstant`'s docstring). What this file
supplies is the *other* half of GWZ's accounting: that the transport inside one slab really
is `δ`-free — i.e. that clause (A2) of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` holds
at a comparison constant that is a polynomial in `bd.C₀` and carries **no power of `δ`** —
**provided the body's normal is aligned with the slab's to within a `δ`-free multiple of the
slab's own angular width `a/b`**.

That proviso is the whole content. `Kakeya.VeryNotSticky.aniLin_rank_two_gap` and the
docstring of `Kakeya.VeryNotSticky.ethickness_aniLin_image_ge` record that the transport's
unconditional rank-`2` lower bound misses (A2) by the factor `a/b`, and
`Kakeya.VeryNotSticky.norm_aniLin_le_of_inner_le`'s docstring records that the missing input is
a tilt bound `≲ a/b`. `Kakeya.VeryNotSticky.IsDenseSlab.angle` supplies only `2θ`, and in the
tangential case `θ` may be as large as `δ^{-τ'} a/b`; the gap between the two is exactly one
factor of `δ^{-τ'}`, and it is that factor which, charged to the enclosure constant
`Kakeya.VeryNotSticky.ktRho2EnclosureConstant`, becomes the loss-to-fullness ratio of


**Why a `δ`-free constant costs nothing.** The comparison constant of
`Kakeya.VeryNotSticky.KTRho2ScaleData` enters its producer
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_nonslab` only through the four thresholds
`hT1`-`hT4`, each of the form `∀ᶠ δ, δ^{positive exponent} ≤ (a constant)⁻¹`. A larger
`δ`-free constant moves the threshold and nothing else. A factor `δ^{-cτ'}`, by contrast,
turns `hT3`/`hT4` into `c·τ' ≤ η` and `c·τ' ≤ ϱ/2`, which
`Kakeya.VeryNotSticky.enclosure_tau'_charge_refuted` below refutes outright from
`Kakeya.VeryNotSticky.CaseParams`. That asymmetry is the reason the cost must be re-sited.

## Contents

* `Kakeya.VeryNotSticky.abs_inner_middle_le_of_lineAngle_le` — the alignment estimate moved
  from the body's normal (`bodyNormal`, the rank-`2` frame vector) to the *middle* frame
  vector, which is the one the transport stretches;
* `Kakeya.VeryNotSticky.thickness_one_aniRescale_image_le_of_aligned` — the rank-`1` upper
  bound of (A2), the first of the two inequalities
  `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_two` leaves open;
* `Kakeya.VeryNotSticky.thickness_two_slabRescale_image_ge` — the rank-`2` lower bound, the
  second one, by a volume comparison: the transport multiplies every volume by the same
  factor, and it takes the slab it normalises *onto* the unit ball
  (`Kakeya.VeryNotSticky.slabRescale_image_generalSlab`), so the factor can be eliminated
  without ever computing a determinant;
* `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_aligned` — **clause (A2) in full,
  at the `δ`-free constant `Kakeya.VeryNotSticky.alignedRescaleConstant bd.C₀ κ`**;
* `Kakeya.VeryNotSticky.ktRho2_L_le_five_thirds` — the fullness clause stays where the existing
  tree puts it: `L = max 1 (10η/wη) ≤ 5/3` from `hηKT` alone, with no relation between `we`
  and `wη`;
* `Kakeya.VeryNotSticky.enclosure_tau'_charge_refuted` — and the alternative, charging the
  `δ^{-τ'}` to the enclosure constant, is refuted by `CaseParams` at every `k ≥ 1`;
* `Kakeya.VeryNotSticky.axisAngle_le_two_theta_of_le_ratio` — the tightened alignment clause
  *implies* the existing `2θ` clause, so no consumer of
  `Kakeya.VeryNotSticky.IsSlabFamily.S3` or `Kakeya.VeryNotSticky.IsDenseSlab.angle` changes
  direction under the re-cut.

Nothing in this file changes a existing statement; every declaration is new.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter
open scoped NNReal ENNReal RealInnerProductSpace

universe u

/-- Shorthand for the ambient space of the tangential case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ### The alignment estimate on the middle frame vector -/

/-- **The alignment estimate, moved to the middle frame vector.**

`Kakeya.VeryNotSticky.bodyNormal` is the rank-`2` vector `e₂` of the body's outer-prism frame;
the vector the anisotropic transport actually stretches out of shape is the *middle* one, `e₁`.
Since `e₁ ⊥ e₂`, Bessel's identity in the orthonormal frame gives
`⟪n, e₁⟫² ≤ 1 - ⟪n, e₂⟫² = sin²∠(e₂, n)`, and `sin x ≤ x` on `[0, π/2]`, where
`Kakeya.NonSlab.lineAngle` lives. So a bound on the *normal* angle is a bound on the middle
vector's component along `n`, at no loss. -/
theorem abs_inner_middle_le_of_lineAngle_le (W : ConvexSpaceBody E₃) (n : E₃) (hn : ‖n‖ = 1) {κ : ℝ}
    (h : NonSlab.lineAngle (bodyNormal W) n ≤ κ) :
    |⟪n, outerPrism.basis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3))
      W.isCompact' W.nonempty' 1⟫| ≤ κ := by
  set hfr : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin with hfr_def
  set e := outerPrism.basis hfr W.isCompact' W.nonempty' with he_def
  have he2 : e 2 = bodyNormal W := by
    rw [he_def, bodyNormal, NonSlab.bodyNormal_eq]
  have hsum : ∑ i, (⟪n, e i⟫ : ℝ) * ⟪e i, n⟫ = ⟪n, n⟫ := e.sum_inner_mul_inner n n
  rw [Fin.sum_univ_three] at hsum
  have hnn : (⟪n, n⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hsym : ∀ i, (⟪n, e i⟫ : ℝ) = ⟪e i, n⟫ := fun i => real_inner_comm _ _
  rw [hsym 0, hsym 1, hsym 2, hnn] at hsum
  -- `⟪e 1, n⟫² ≤ 1 - ⟪e 2, n⟫²`
  have hbess : (⟪e 1, n⟫ : ℝ) ^ 2 ≤ 1 - (⟪e 2, n⟫ : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (⟪e 0, n⟫ : ℝ)]
  have hne2 : ‖e 2‖ = 1 := e.norm_eq_one 2
  have hang : NonSlab.lineAngle (e 2) n = Real.arccos |(⟪e 2, n⟫ : ℝ)| :=
    NonSlab.lineAngle_eq_arccos_abs_inner hne2 hn
  have hsin : Real.sin (NonSlab.lineAngle (e 2) n) = Real.sqrt (1 - (⟪e 2, n⟫ : ℝ) ^ 2) := by
    rw [hang, Real.sin_arccos, sq_abs]
  have hle : Real.sin (NonSlab.lineAngle (e 2) n) ≤ κ := by
    refine le_trans (Real.sin_le (NonSlab.lineAngle_nonneg _ _)) ?_
    rw [he2]; exact h
  rw [hsin] at hle
  calc |(⟪n, e 1⟫ : ℝ)| = Real.sqrt ((⟪e 1, n⟫ : ℝ) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, hsym 1]
    _ ≤ Real.sqrt (1 - (⟪e 2, n⟫ : ℝ) ^ 2) := Real.sqrt_le_sqrt hbess
    _ ≤ κ := hle

/-! ### The rank-`1` upper bound of (A2), from the alignment -/

/-- **The rank-`1` upper bound of clause (A2), from the alignment** — the first of the two
inequalities that `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_two` leaves as
hypotheses.

The body is contained in the box of its own outer prism, of half-widths `τ₀, τ₁, τ₂`; the
image of that box under `Kakeya.VeryNotSticky.aniRescale` lies within
`τ₁‖L e₁‖ + τ₂‖L e₂‖` of the line through `L(centre)` in the direction `L e₀`, because the
`e₀`-component of every displacement is absorbed by moving along that line. The two norms are
`Kakeya.VeryNotSticky.norm_aniLin_le_of_inner_le` at `s` and
`Kakeya.VeryNotSticky.norm_aniLin_le_max`. **`s` is where `δ` would enter**: the `β s` term is
the tilt's price, and at `α = 1/r₁`, `β = b/(a r₁)` it is `s · b/(a r₁)`, which is `∼ 1/r₁`
exactly when `s ≲ a/b`. -/
theorem thickness_one_aniRescale_image_le_of_aligned (cc : E₃) (n : E₃) (hn : ‖n‖ = 1)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {X : Set E₃} (hXc : IsCompact X) (hXne : X.Nonempty) {t₁ t₂ s : ℝ}
    (h1 : Metric.thickness ℝ X 1 ≤ t₁) (h2 : Metric.thickness ℝ X 2 ≤ t₂)
    (hs : 0 ≤ s)
    (halign : |⟪n, outerPrism.basis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)) hXc hXne 1⟫|
      ≤ s) :
    Metric.thickness ℝ (aniRescale cc n hn hα.ne' hβ.ne' '' X) 1
      ≤ t₁ * (α + β * s) + t₂ * (α + β) := by
  have hα' : (0:ℝ) ≤ α := hα.le
  have hβ' : (0:ℝ) ≤ β := hβ.le
  set hfr : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin with hfr_def
  set e := outerPrism.basis hfr hXc hXne with he_def
  set c₀ := outerPrism.center hfr hXc hXne with hc_def
  have ht1 : (0:ℝ) ≤ t₁ := le_trans (Metric.thickness_nonneg X 1) h1
  have ht2 : (0:ℝ) ≤ t₂ := le_trans (Metric.thickness_nonneg X 2) h2
  have hR : (0:ℝ) ≤ t₁ * (α + β * s) + t₂ * (α + β) := by positivity
  set A : AffineSubspace ℝ E₃ :=
    AffineSubspace.mk' (aniRescale cc n hn hα.ne' hβ.ne' c₀) (ℝ ∙ (aniLin n α β (e 0)))
    with hA_def
  have hrank : Module.rank ℝ A.direction ≤ (1 : ℕ) := by
    rw [hA_def, AffineSubspace.direction_mk']
    simpa using rank_span_le ({aniLin n α β (e 0)} : Set E₃)
  refine Metric.thickness_le_of_cthickening hR hrank ?_
  rintro _ ⟨x, hx, rfl⟩
  set v : E₃ := x - c₀ with hv_def
  set v0 : ℝ := ⟪e 0, v⟫ with hv0
  set v1 : ℝ := ⟪e 1, v⟫ with hv1
  set v2 : ℝ := ⟪e 2, v⟫ with hv2
  have hdecomp : v = v0 • e 0 + v1 • e 1 + v2 • e 2 := by
    have := e.sum_repr v
    rw [Fin.sum_univ_three] at this
    simp only [OrthonormalBasis.repr_apply_apply] at this
    rw [← this, hv0, hv1, hv2]
  have hmemA : v0 • aniLin n α β (e 0) + aniRescale cc n hn hα.ne' hβ.ne' c₀ ∈ A := by
    rw [hA_def, AffineSubspace.mem_mk']
    have hvs : (v0 • aniLin n α β (e 0) + aniRescale cc n hn hα.ne' hβ.ne' c₀)
        -ᵥ aniRescale cc n hn hα.ne' hβ.ne' c₀ = v0 • aniLin n α β (e 0) := by simp
    rw [hvs]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine Metric.mem_cthickening_of_dist_le _ _ _ _ hmemA ?_
  have hkey : aniRescale cc n hn hα.ne' hβ.ne' x
      - (v0 • aniLin n α β (e 0) + aniRescale cc n hn hα.ne' hβ.ne' c₀)
      = v1 • aniLin n α β (e 1) + v2 • aniLin n α β (e 2) := by
    rw [aniRescale_apply, aniRescale_apply]
    have hxx : x - cc - (c₀ - cc) = v := by rw [hv_def]; abel
    have : aniLin n α β (x - cc) - aniLin n α β (c₀ - cc) = aniLin n α β v := by
      rw [← map_sub, hxx]
    rw [show aniLin n α β (x - cc) - (v0 • aniLin n α β (e 0) + aniLin n α β (c₀ - cc))
        = (aniLin n α β (x - cc) - aniLin n α β (c₀ - cc)) - v0 • aniLin n α β (e 0) by abel,
      this, hdecomp]
    simp only [map_add, map_smul]
    abel
  rw [dist_eq_norm, hkey]
  have hb1 : |v1| ≤ Metric.thickness ℝ X 1 := by
    have := outerPrism.basis_repr_le hfr hXc hXne hx 1
    simpa [hv1, hv_def, OrthonormalBasis.repr_apply_apply, inner_sub_right] using this
  have hb2 : |v2| ≤ Metric.thickness ℝ X 2 := by
    have := outerPrism.basis_repr_le hfr hXc hXne hx 2
    simpa [hv2, hv_def, OrthonormalBasis.repr_apply_apply, inner_sub_right] using this
  have hne1 : ‖e 1‖ = 1 := e.norm_eq_one 1
  have hne2 : ‖e 2‖ = 1 := e.norm_eq_one 2
  have ha1 : ‖aniLin n α β (e 1)‖ ≤ α + β * s := by
    have := norm_aniLin_le_of_inner_le n hn hα' hβ' (e 1) halign
    rwa [hne1, mul_one] at this
  have ha2 : ‖aniLin n α β (e 2)‖ ≤ α + β := by
    have := norm_aniLin_le_max n hn hα' hβ' (e 2)
    rw [hne2, mul_one] at this
    exact this.trans (by cases max_choice α β with
      | inl h => rw [h]; linarith
      | inr h => rw [h]; linarith)
  calc ‖v1 • aniLin n α β (e 1) + v2 • aniLin n α β (e 2)‖
      ≤ ‖v1 • aniLin n α β (e 1)‖ + ‖v2 • aniLin n α β (e 2)‖ := norm_add_le _ _
    _ = |v1| * ‖aniLin n α β (e 1)‖ + |v2| * ‖aniLin n α β (e 2)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ t₁ * (α + β * s) + t₂ * (α + β) := by
        have hp1 : (0:ℝ) ≤ α + β * s := by positivity
        have hp2 : (0:ℝ) ≤ α + β := by positivity
        gcongr
        · exact hb1.trans h1
        · exact hb2.trans h2

/-! ### The rank-`2` lower bound of (A2), by a volume comparison -/

/-- **Volume floor from a three-term thickness profile**, the general-profile companion of
`Kakeya.VeryNotSticky.volume_ge_of_tubeProfile`: `6` is `3!`, the reciprocal of the
inscribed-simplex constant of `Convex.prod_thickness_le_volumeReal`, and `C₀³` is one factor
of `C₀` per axis. -/
theorem volumeReal_ge_of_threeProfile {K : Set E₃} (hconv : Convex ℝ K)
    (hbdd : Bornology.IsBounded K)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀) {t0 t1 t2 : ℝ} (h0 : 0 ≤ t0) (h1 : 0 ≤ t1) (h2 : 0 ≤ t2)
    (hprof : Kakeya.HasThicknesses K C₀ ![t0, t1, t2]) :
    (t0 * t1 * t2) / (6 * (C₀ : ℝ) ^ 3) ≤ MeasureTheory.volume.real K := by
  have hC0ne : (C₀ : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hC₀))
  have e0 : (C₀ : ℝ)⁻¹ * t0 ≤ Metric.thickness ℝ K 0 := by simpa using (hprof 0).1
  have e1 : (C₀ : ℝ)⁻¹ * t1 ≤ Metric.thickness ℝ K 1 := by simpa using (hprof 1).1
  have e2 : (C₀ : ℝ)⁻¹ * t2 ≤ Metric.thickness ℝ K 2 := by simpa using (hprof 2).1
  have ha0 : 0 ≤ (C₀ : ℝ)⁻¹ * t0 := by positivity
  have ha1 : 0 ≤ (C₀ : ℝ)⁻¹ * t1 := by positivity
  have ha2 : 0 ≤ (C₀ : ℝ)⁻¹ * t2 := by positivity
  have ht0 : 0 ≤ Metric.thickness ℝ K 0 := Metric.thickness_nonneg K 0
  have ht1 : 0 ≤ Metric.thickness ℝ K 1 := Metric.thickness_nonneg K 1
  have h01 : ((C₀ : ℝ)⁻¹ * t0) * ((C₀ : ℝ)⁻¹ * t1)
      ≤ Metric.thickness ℝ K 0 * Metric.thickness ℝ K 1 := mul_le_mul e0 e1 ha1 ht0
  have hprod_lower :
      (((C₀ : ℝ)⁻¹ * t0) * ((C₀ : ℝ)⁻¹ * t1)) * ((C₀ : ℝ)⁻¹ * t2)
        ≤ Metric.thickness ℝ K 0 * Metric.thickness ℝ K 1 * Metric.thickness ℝ K 2 :=
    mul_le_mul h01 e2 ha2 (mul_nonneg ht0 ht1)
  have hvol : (6 : ℝ)⁻¹ *
      (Metric.thickness ℝ K 0 * Metric.thickness ℝ K 1 * Metric.thickness ℝ K 2) ≤
      MeasureTheory.volume.real K := by
    have hv0 := Convex.prod_thickness_le_volumeReal (E := E₃) hconv hbdd
    rw [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] at hv0
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ] at hv0
    norm_num [Metric.lt_volume_convexHull.c] at hv0
    simpa using hv0
  have hLHS : (t0 * t1 * t2) / (6 * (C₀ : ℝ) ^ 3) =
      (6 : ℝ)⁻¹ * (((C₀ : ℝ)⁻¹ * t0) * ((C₀ : ℝ)⁻¹ * t1)) * ((C₀ : ℝ)⁻¹ * t2) := by
    field_simp [hC0ne]
  rw [hLHS]
  nlinarith [hprod_lower, hvol, ha0, ha1, ha2, ht0, ht1,
    show 0 ≤ (6 : ℝ)⁻¹ by positivity]

/-- **The volume ratio identity — the determinant eliminated.**

An affine automorphism multiplies every volume by `|det|` (`Kakeya.volume_affineImage`), and
`Kakeya.VeryNotSticky.slabRescale` carries the slab it normalises *onto* the unit ball
(`Kakeya.VeryNotSticky.slabRescale_image_generalSlab`, an equality). Multiplying the two
identities crosswise cancels `|det|`, so the volume of the image of an arbitrary set is pinned
by the volume of the unit ball and the volume of the slab, and no determinant of
`Kakeya.VeryNotSticky.aniLin` ever has to be computed. -/
theorem volume_slabRescale_image_mul_volume_generalSlab (c n : E₃) (hn : ‖n‖ = 1)
    {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) (X : Set E₃) :
    volume (slabRescale c n hn hr₁ hratio '' X) *
        volume (generalSlab c n hn hr₁ hratio).carrier
      = volume (Metric.closedBall (0 : E₃) 1) * volume X := by
  set L := slabRescale c n hn hr₁ hratio with hL
  set D : ENNReal := ENNReal.ofReal |LinearMap.det (L.linear : E₃ →ₗ[ℝ] E₃)| with hD
  have hX : volume (L '' X) = D * volume X := Kakeya.volume_affineImage L X
  have hS : volume (L '' (generalSlab c n hn hr₁ hratio).carrier)
      = D * volume (generalSlab c n hn hr₁ hratio).carrier :=
    Kakeya.volume_affineImage L _
  rw [slabRescale_image_generalSlab c n hn hr₁ hratio] at hS
  rw [hX, hS]
  ring

/-- The unit ball of `ℝ³` has volume at least `1/6`, from the inscribed simplex alone: its
three affine thicknesses are all `1`. Only a positive lower bound is needed below, so the
sharp value `4π/3` is not required. -/
theorem ofReal_six_inv_le_volume_unitBall :
    ENNReal.ofReal ((1 : ℝ) / 6) ≤ volume (Metric.closedBall (0 : E₃) 1) := by
  have hprof : Kakeya.HasThicknesses (Metric.closedBall (0 : E₃) 1) 1 ![(1:ℝ), 1, 1] := by
    intro k
    have hk : (k : ℕ) < Module.finrank ℝ E₃ := by
      rw [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)]; exact k.2
    have hle := Metric.thickness_closedBall_le (𝕜 := ℝ) (x := (0 : E₃))
      (r := (1:ℝ)) zero_le_one (k : ℕ)
    have hge := Metric.thickness_closedBall_ge (x := (0 : E₃)) (r := (1:ℝ)) zero_le_one hk
    fin_cases k <;> simp_all
  have hfl := volumeReal_ge_of_threeProfile (K := Metric.closedBall (0 : E₃) 1)
    (convex_closedBall _ _) Metric.isBounded_closedBall (le_refl (1 : NNReal))
    zero_le_one zero_le_one zero_le_one hprof
  norm_num at hfl
  rw [MeasureTheory.Measure.real] at hfl
  have hne : volume (Metric.closedBall (0 : E₃) 1) ≠ ⊤ :=
    (Metric.isBounded_closedBall (x := (0:E₃)) (r := 1)).measure_lt_top.ne
  exact (ENNReal.ofReal_le_iff_le_toReal hne).mpr (by linarith)

/-- `volume s ≤ 2³ · τ₀ τ₁ τ₂`, in the form the comparison below consumes: upper bounds for
the three thicknesses give an upper bound for the volume. -/
theorem volume_le_of_thickness_bounds {s : Set E₃} (hs : Bornology.IsBounded s) {u0 u1 u2 : ℝ}
    (h0 : Metric.thickness ℝ s 0 ≤ u0) (h1 : Metric.thickness ℝ s 1 ≤ u1)
    (h2 : Metric.thickness ℝ s 2 ≤ u2) :
    volume s ≤ ENNReal.ofReal (8 * (u0 * u1 * u2)) := by
  have hv := volume_le_prod_thickness (E := E₃) hs
  rw [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] at hv
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul] at hv
  refine hv.trans ?_
  have hu0 : (0:ℝ) ≤ u0 := le_trans (Metric.thickness_nonneg s 0) h0
  have hu1 : (0:ℝ) ≤ u1 := le_trans (Metric.thickness_nonneg s 1) h1
  have hu2 : (0:ℝ) ≤ u2 := le_trans (Metric.thickness_nonneg s 2) h2
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hu0]
  gcongr
  rw [show ((8:ℝ)) = ((8:ℕ):ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num

/-- **The rank-`2` lower bound of clause (A2)** — the second inequality
`Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_two` leaves open, and the one that
`Kakeya.VeryNotSticky.aniLin_rank_two_gap` shows the transport cannot supply unconditionally.

The route is a volume comparison rather than a direct thickness transport, which is what makes
it work: the image `Y` has a volume floor (the body's own floor, transported by the ratio
identity), and `volume Y ≤ 2³ τ₀(Y) τ₁(Y) τ₂(Y)` with `τ₀(Y) ≤ 1` and `τ₁(Y) ≤ T₁` then bounds
`τ₂(Y)` from below by `ρ₂²/(2304 C₀³ T₁)`. With the aligned `T₁ ∼ C₀ ρ₂` of
`Kakeya.VeryNotSticky.thickness_one_aniRescale_image_le_of_aligned` that is `∼ ρ₂`, which is
(A2); with the unaligned `T₁ ∼ δ^{-τ'} C₀ ρ₂` it is `δ^{τ'} ρ₂`, which is not. -/
theorem thickness_two_slabRescale_image_ge (c n : E₃) (hn : ‖n‖ = 1)
    {r₁ ratio a b T₁ : ℝ} {C₀ : NNReal}
    (hr₁ : 0 < r₁) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hrb : ratio * b = a) (hC₀ : 1 ≤ C₀) (W : ConvexSpaceBody E₃)
    (hX : Kakeya.HasThicknesses W.carrier C₀ ![r₁, b, a])
    (hsub : W.carrier ⊆ (generalSlab c n hn hr₁ hratio).carrier)
    (hT₁ : Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' W.carrier) 1 ≤ T₁)
    (hT₁0 : 0 < T₁) :
    (b / r₁) ^ 2 / (2304 * (C₀ : ℝ) ^ 3 * T₁)
      ≤ Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' W.carrier) 2 := by
  have hC₀' : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀0 : (0 : ℝ) < (C₀ : ℝ) := lt_of_lt_of_le one_pos hC₀'
  set Y := slabRescale c n hn hr₁ hratio '' W.carrier with hY_def
  set t2 : ℝ := Metric.thickness ℝ Y 2 with ht2_def
  have ht20 : (0:ℝ) ≤ t2 := Metric.thickness_nonneg Y 2
  -- `Y ⊆ B₁`
  have hYball : Y ⊆ Metric.closedBall (0 : E₃) 1 :=
    slabRescale_image_subset_closedBall c n hn hr₁ hratio hsub
  have hYbdd : Bornology.IsBounded Y :=
    Metric.isBounded_closedBall.subset hYball
  have hY0 : Metric.thickness ℝ Y 0 ≤ 1 :=
    Metric.thickness_le_of_subset_closedBall hYball zero_le_one 0
  have hvolY : volume Y ≤ ENNReal.ofReal (8 * (1 * T₁ * t2)) :=
    volume_le_of_thickness_bounds hYbdd hY0 hT₁ le_rfl
  -- the slab's own volume
  have hgSprof := hasThicknesses_generalSlab c n hn hr₁ hratio hratio1 (le_refl (1 : NNReal))
  have hgS0 : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 0 ≤ r₁ := by
    simpa using (hgSprof 0).2
  have hgS1 : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 1 ≤ r₁ := by
    simpa using (hgSprof 1).2
  have hgS2 : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 2 ≤ ratio * r₁ := by
    simpa using (hgSprof 2).2
  have hvolgS : volume (generalSlab c n hn hr₁ hratio).carrier
      ≤ ENNReal.ofReal (8 * (r₁ * r₁ * (ratio * r₁))) :=
    volume_le_of_thickness_bounds
      (generalSlab c n hn hr₁ hratio).isCompact'.isBounded hgS0 hgS1 hgS2
  -- the body's volume floor
  have hvolW : ENNReal.ofReal ((r₁ * b * a) / (6 * (C₀ : ℝ) ^ 3)) ≤ volume W.carrier := by
    have h := volumeReal_ge_of_threeProfile W.convex W.isCompact'.isBounded hC₀
      hr₁.le hb.le ha.le hX
    rw [MeasureTheory.Measure.real] at h
    exact (ENNReal.ofReal_le_iff_le_toReal W.isCompact'.measure_ne_top).mpr h
  -- combine
  have hkey := volume_slabRescale_image_mul_volume_generalSlab c n hn hr₁ hratio W.carrier
  have hlow : ENNReal.ofReal ((1:ℝ)/6) * ENNReal.ofReal ((r₁ * b * a) / (6 * (C₀ : ℝ) ^ 3))
      ≤ ENNReal.ofReal (8 * (1 * T₁ * t2)) * ENNReal.ofReal (8 * (r₁ * r₁ * (ratio * r₁))) := by
    calc ENNReal.ofReal ((1:ℝ)/6) * ENNReal.ofReal ((r₁ * b * a) / (6 * (C₀ : ℝ) ^ 3))
        ≤ volume (Metric.closedBall (0 : E₃) 1) * volume W.carrier := by
          gcongr
          · exact ofReal_six_inv_le_volume_unitBall
      _ = volume Y * volume (generalSlab c n hn hr₁ hratio).carrier := hkey.symm
      _ ≤ _ := by gcongr
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)] at hlow
  have hlow' : ((1:ℝ)/6) * ((r₁ * b * a) / (6 * (C₀ : ℝ) ^ 3))
      ≤ (8 * (1 * T₁ * t2)) * (8 * (r₁ * r₁ * (ratio * r₁))) := by
    have hpos : (0:ℝ) ≤ (8 * (1 * T₁ * t2)) * (8 * (r₁ * r₁ * (ratio * r₁))) := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff hpos).mp hlow
  have hratio_eq : ratio = a / b := by field_simp [hb.ne'] at hrb ⊢; linarith [hrb]
  rw [hratio_eq] at hlow'
  rw [div_le_iff₀ (by positivity)]
  have hb' : b ≠ 0 := hb.ne'
  have hr' : r₁ ≠ 0 := hr₁.ne'
  have ha' : a ≠ 0 := ha.ne'
  field_simp at hlow' ⊢
  nlinarith [hlow', sq_nonneg (b*r₁), mul_pos hr₁ hb, mul_pos ha hb, hC₀0, hT₁0, ht20]

/-! ### Clause (A2) in full, at a `δ`-free constant -/

/-! `Kakeya.VeryNotSticky.alignedRescaleConstant` — a polynomial in the body's own comparison
constant `C₀` and in the alignment factor `κ` of the slab-membership clause, and — this is the
point — **free of `δ`** — is now declared in
`Kakeya.DimensionThree.MainLemma2.TangentialCase`, because clauses (A2)/(A2′) of
`Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` are stated at it (re-cuts R3/R4). It is the
constant at which `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_aligned` delivers
clause (A2). Being `δ`-free it is discharged by the four `∀ᶠ δ` thresholds of
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleDataAt_nonslab` and costs no exponent; contrast
`Kakeya.VeryNotSticky.enclosure_tau'_charge_refuted`. -/

set_option maxHeartbeats 1000000 in
-- The six inequalities of (A2) are assembled here from four sources at once (the two
-- unconditional transport brackets, the aligned rank-`1` bound and the volume comparison),
-- and the `field_simp`/`nlinarith` normalisation of the constant `2304 (3 + κ) C₀⁴` against
-- three different profiles exceeds the default budget; the proof is linear, not a search.
/-- **Clause (A2) of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale`, produced at a `δ`-free
constant from the alignment `∠(n(W), n(S)) ≤ κ · (a/b)`.**

All six inequalities: the four that
`Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_two` already had unconditionally,
weakened to the larger constant, plus the rank-`1` upper bound
(`Kakeya.VeryNotSticky.thickness_one_aniRescale_image_le_of_aligned`, which needs the
alignment) and the rank-`2` lower bound
(`Kakeya.VeryNotSticky.thickness_two_slabRescale_image_ge`, which needs the rank-`1` one).

**This is GWZ's transport, with GWZ's own accounting**: within one slab the change of variables
is free, and the `δ^{-O(τ')}` of (105) is charged where GWZ charge it, to the number of slabs a
fibre meets — the `δ^{-2τ'}` already written into
`Kakeya.VeryNotSticky.tangentialSlabDecomp` and paid from
`Kakeya.VeryNotSticky.CaseParams.tangential`'s `2²⁰(ϱ + τ')`. -/
theorem hasThicknesses_slabRescale_image_of_aligned (c n : E₃) (hn : ‖n‖ = 1)
    {r₁ ratio a b : ℝ} {C₀ κ : NNReal}
    (hr₁ : 0 < r₁) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hrb : ratio * b = a) (hC₀ : 1 ≤ C₀) (hκ : 1 ≤ κ) (W : ConvexSpaceBody E₃)
    (hX : Kakeya.HasThicknesses W.carrier C₀ ![r₁, b, a])
    (hsub : W.carrier ⊆ (generalSlab c n hn hr₁ hratio).carrier)
    (halign : NonSlab.lineAngle (bodyNormal W) n ≤ (κ : ℝ) * ratio) :
    Kakeya.HasThicknesses (slabRescale c n hn hr₁ hratio '' W.carrier)
      (alignedRescaleConstant C₀ κ) ![1, b / r₁, b / r₁] := by
  have hC₀' : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀0 : (0 : ℝ) < (C₀ : ℝ) := lt_of_lt_of_le one_pos hC₀'
  have hκ' : (1 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ
  set M : ℝ := 2304 * (3 + (κ : ℝ)) * (C₀ : ℝ) ^ 4 with hM_def
  have hCc : ((alignedRescaleConstant C₀ κ : NNReal) : ℝ) = M := by
    simp [alignedRescaleConstant, hM_def]
  have hMpos : (0 : ℝ) < M := by rw [hM_def]; positivity
  have hcube : (1 : ℝ) ≤ (C₀ : ℝ) ^ 3 := one_le_pow₀ hC₀'
  have hC4 : (C₀ : ℝ) ≤ (C₀ : ℝ) ^ 4 := by nlinarith
  have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := κ.coe_nonneg
  have hpow4 : (1 : ℝ) ≤ (C₀ : ℝ) ^ 4 := one_le_pow₀ hC₀'
  have hkey : ∀ x : ℝ, 0 ≤ x → x * (C₀ : ℝ) ≤ 2304 * x * (C₀ : ℝ) ^ 4 := by
    intro x hx
    calc x * (C₀ : ℝ) ≤ x * (2304 * (C₀ : ℝ) ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ hx
          nlinarith
      _ = 2304 * x * (C₀ : ℝ) ^ 4 := by ring
  have hCle : (C₀ : ℝ) ≤ M := by
    rw [hM_def]
    have := hkey (3 + (κ : ℝ)) (by linarith)
    nlinarith
  have hCinv : M⁻¹ ≤ ((C₀ : ℝ))⁻¹ := inv_anti₀ hC₀0 hCle
  set Y := slabRescale c n hn hr₁ hratio '' W.carrier with hY_def
  have hpos : (0 : ℝ) < ratio * r₁ := mul_pos hratio hr₁
  have hαpos : (0 : ℝ) < r₁⁻¹ := inv_pos.mpr hr₁
  have hαβ : r₁⁻¹ ≤ (ratio * r₁)⁻¹ := (inv_le_inv₀ hr₁ hpos).2 (by nlinarith)
  have hbr : (ratio * r₁)⁻¹ * a = b / r₁ := by rw [← hrb]; field_simp
  have hXbdd : Bornology.IsBounded W.carrier := W.isCompact'.isBounded
  have hX0 := (hX 0).1
  have hX1 := (hX 1).1
  have hX2 := (hX 2).2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hX0 hX1 hX2
  have hρ0 : (0:ℝ) ≤ b / r₁ := by positivity
  have hYball : Y ⊆ Metric.closedBall (0 : E₃) 1 :=
    slabRescale_image_subset_closedBall c n hn hr₁ hratio hsub
  have h0u : Metric.thickness ℝ Y 0 ≤ 1 :=
    Metric.thickness_le_of_subset_closedBall hYball zero_le_one 0
  have h0l : M⁻¹ * 1 ≤ Metric.thickness ℝ Y 0 := by
    have hlow := (thickness_aniRescale_image_mem c n hn hαpos hαβ hXbdd 0).1
    calc M⁻¹ * 1 ≤ r₁⁻¹ * (((C₀ : ℝ))⁻¹ * r₁) := by
          rw [mul_one]
          have he : r₁⁻¹ * (((C₀ : ℝ))⁻¹ * r₁) = ((C₀ : ℝ))⁻¹ := by field_simp
          rw [he]
          exact hCinv
      _ ≤ r₁⁻¹ * Metric.thickness ℝ W.carrier 0 := mul_le_mul_of_nonneg_left hX0 hαpos.le
      _ ≤ _ := hlow
  have h1l : M⁻¹ * (b / r₁) ≤ Metric.thickness ℝ Y 1 := by
    have hlow := (thickness_aniRescale_image_mem c n hn hαpos hαβ hXbdd 1).1
    calc M⁻¹ * (b / r₁) ≤ r₁⁻¹ * (((C₀ : ℝ))⁻¹ * b) := by
          have he : r₁⁻¹ * (((C₀ : ℝ))⁻¹ * b) = ((C₀ : ℝ))⁻¹ * (b / r₁) := by
            field_simp
          rw [he]
          exact mul_le_mul_of_nonneg_right hCinv hρ0
      _ ≤ r₁⁻¹ * Metric.thickness ℝ W.carrier 1 := mul_le_mul_of_nonneg_left hX1 hαpos.le
      _ ≤ _ := hlow
  have h2u : Metric.thickness ℝ Y 2 ≤ M * (b / r₁) := by
    have hup := (thickness_aniRescale_image_mem c n hn hαpos hαβ hXbdd 2).2
    calc Metric.thickness ℝ Y 2 ≤ (ratio * r₁)⁻¹ * Metric.thickness ℝ W.carrier 2 := hup
      _ ≤ (ratio * r₁)⁻¹ * ((C₀ : ℝ) * a) := mul_le_mul_of_nonneg_left hX2 (inv_pos.mpr hpos).le
      _ = (C₀ : ℝ) * ((ratio * r₁)⁻¹ * a) := by ring
      _ = (C₀ : ℝ) * (b / r₁) := by rw [hbr]
      _ ≤ M * (b / r₁) := mul_le_mul_of_nonneg_right hCle hρ0
  -- the aligned rank-`1` upper bound
  have halign' : |⟪n, outerPrism.basis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3))
      W.isCompact' W.nonempty' 1⟫| ≤ (κ : ℝ) * ratio :=
    abs_inner_middle_le_of_lineAngle_le W n hn halign
  have hXt1 : Metric.thickness ℝ W.carrier 1 ≤ (C₀ : ℝ) * b := by simpa using (hX 1).2
  have hXt2 : Metric.thickness ℝ W.carrier 2 ≤ (C₀ : ℝ) * a := hX2
  have hβpos : (0:ℝ) < (ratio * r₁)⁻¹ := inv_pos.mpr hpos
  have hsnn : (0:ℝ) ≤ (κ : ℝ) * ratio := by positivity
  have h1u' : Metric.thickness ℝ Y 1
      ≤ ((C₀ : ℝ) * b) * (r₁⁻¹ + (ratio * r₁)⁻¹ * ((κ : ℝ) * ratio))
        + ((C₀ : ℝ) * a) * (r₁⁻¹ + (ratio * r₁)⁻¹) :=
    thickness_one_aniRescale_image_le_of_aligned c n hn hαpos hβpos
      W.isCompact' W.nonempty' hXt1 hXt2 hsnn halign'
  have h1u : Metric.thickness ℝ Y 1 ≤ (3 + (κ : ℝ)) * (C₀ : ℝ) * (b / r₁) := by
    refine h1u'.trans ?_
    have e1 : (ratio * r₁)⁻¹ * ((κ : ℝ) * ratio) = (κ : ℝ) * r₁⁻¹ := by field_simp
    have e2 : ((C₀ : ℝ) * a) * (ratio * r₁)⁻¹ = (C₀ : ℝ) * (b / r₁) := by
      rw [mul_assoc, mul_comm a ((ratio * r₁)⁻¹), hbr]
    have hexp : ((C₀ : ℝ) * b) * (r₁⁻¹ + (κ : ℝ) * r₁⁻¹)
          + ((C₀ : ℝ) * a) * (r₁⁻¹ + (ratio * r₁)⁻¹)
        = (2 + (κ : ℝ)) * (C₀ : ℝ) * (b / r₁) + (C₀ : ℝ) * (a / r₁) := by
      have hsplit : ((C₀ : ℝ) * a) * (r₁⁻¹ + (ratio * r₁)⁻¹)
          = ((C₀ : ℝ) * a) * r₁⁻¹ + ((C₀ : ℝ) * a) * (ratio * r₁)⁻¹ := by ring
      rw [hsplit, e2]
      field_simp
      ring
    rw [e1, hexp]
    have hmono : (C₀ : ℝ) * (a / r₁) ≤ (C₀ : ℝ) * (b / r₁) := by gcongr
    nlinarith
  have hT₁0 : (0:ℝ) < (3 + (κ : ℝ)) * (C₀ : ℝ) * (b / r₁) := by positivity
  have h2l' := thickness_two_slabRescale_image_ge c n hn hr₁ hratio hratio1 ha hb hrb hC₀ W
    hX hsub h1u hT₁0
  have h2l : M⁻¹ * (b / r₁) ≤ Metric.thickness ℝ Y 2 := by
    refine le_trans (le_of_eq ?_) h2l'
    rw [hM_def]
    field_simp
  have h1uC : Metric.thickness ℝ Y 1 ≤ M * (b / r₁) := by
    refine h1u.trans (mul_le_mul_of_nonneg_right ?_ hρ0)
    rw [hM_def]
    exact hkey (3 + (κ : ℝ)) (by linarith)
  have h0uC : Metric.thickness ℝ Y 0 ≤ M * 1 := by
    rw [mul_one]
    refine h0u.trans ?_
    rw [hM_def]
    nlinarith
  intro k
  rw [hCc]
  fin_cases k
  · exact ⟨h0l, h0uC⟩
  · exact ⟨h1l, h1uC⟩
  · exact ⟨h2l, h2u⟩

/-! ### Where the `δ^{-τ'}` may and may not be charged -/

/-- **The fullness clause stays where the existing tree puts it.** The Katz–Tao parameter of
`Kakeya.VeryNotSticky.ktRho2ScaleData_of_ckt_nonslab` is `τ = δ^L` with
`L = max 1 (10 η / wη)`, and `hηKT : 3η ≤ exscal · wη` together with `exscal ≤ 1/2` already
gives `L ≤ 5/3`, from the window's *own* fields and with **no relation between `we` and `wη`**.

This is the half of `Kakeya.VeryNotSticky.ktRho2_window_loss_le` that matters here: as long as
the enclosure constant carries no power of `δ`, the fullness side needs nothing new. It is
only when a factor `δ^{-c τ'}` is charged to the enclosure that `hL2 : 10η ≤ L·wη` has to
become `10η + cτ' ≤ L·wη`, `L` grows past `5/3`, and the loss `we·L` forces a bound on
`we/wη` — 's ratio, 's accuracy-independent threshold floor. -/
theorem ktRho2_L_le_five_thirds {η exscal wη : ℝ} (hexscal12 : exscal ≤ 1 / 2) (hwη : 0 < wη)
    (hηKT : 3 * η ≤ exscal * wη) : max 1 (10 * η / wη) ≤ 5 / 3 := by
  refine max_le (by norm_num) ?_
  rw [div_le_iff₀ hwη]
  nlinarith

/-- **And the alternative is refuted.** If instead the `δ^{-O(τ')}` were charged to the
enclosure constant `Kakeya.VeryNotSticky.ktRho2EnclosureConstant`, the two thresholds `hT3`
and `hT4` of `Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_nonslab` — `K ≤ δ^{-η}` and
`K ≤ δ^{-ϱ/2}` — would demand `k τ' ≤ η` and `k τ' ≤ ϱ/2`. Both fail, at every `k ≥ 1`, from
four fields of `Kakeya.VeryNotSticky.CaseParams`: `transverse` with `β ≤ 1` gives
`τ' > 3τ + 87η`, `rhoLeTau` gives `τ' > 3ϱ`, and `densityBias` gives `ϱ > 2²⁰ η > 0`.

`τ'` is bounded **below** by `3ϱ` and the enclosure route needs it bounded **above** by `ϱ/2`:
the ordering is wrong by a factor of at least six. This is why the cost has to be re-sited to
the multiplicity, where `Kakeya.VeryNotSticky.CaseParams.tangential`'s `2²⁰(ϱ + τ')` already
budgets it — and why a `δ`-free constant such as
`Kakeya.VeryNotSticky.alignedRescaleConstant` is free while a `δ^{-τ'}` is not. -/
theorem enclosure_tau'_charge_refuted {β ζ exscal ϱ η τ τ' : ℝ}
    (params : CaseParams β ζ exscal ϱ η τ τ') (hβ1 : β ≤ 1) (hτ : 0 < τ) (hη : 0 < η)
    {k : ℝ} (hk : 1 ≤ k) : ¬ (k * τ' ≤ ϱ) ∧ ¬ (k * τ' ≤ η) := by
  have hbias := params.densityBias
  rw [parameterSeparationConstant] at hbias
  have hϱ : 0 < ϱ := by nlinarith
  have hϱη : η < ϱ := by nlinarith
  have htrans := params.transverse
  have hρτ : ϱ ≤ τ := params.rhoLeTau
  have hτ'pos : 0 < τ' := lt_trans hτ params.hτ'
  have hβ0 : 0 < β := by nlinarith
  have h1 : 3 * τ + 87 * η < τ' := by nlinarith
  have h2 : 3 * ϱ < τ' := by nlinarith
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ### The tightened alignment clause against the existing one -/

/-- **The tightened clause implies the existing one, so no consumer changes direction.**
`Kakeya.VeryNotSticky.TypicalAngleData.hθab` and `.hratio` give `a/b ≤ θ`, so an alignment
clause at `κ (a/b)` with `κ ≤ 2` is *stronger* than the existing
`Kakeya.VeryNotSticky.IsDenseSlab.angle` / `Kakeya.VeryNotSticky.IsSlabFamily.S3` clause at
`2θ`. Every consumer of the angle bound — `Kakeya.VeryNotSticky.tangentialSlabFibreCount`
among them, which reads it as an upper bound on the aperture of a cone — therefore keeps
working verbatim. -/
theorem axisAngle_le_two_theta_of_le_ratio (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    (ta : TypicalAngleData cfg tc hB τ') {κ : ℝ} (hκ2 : κ ≤ 2)
    {W S : ConvexSpaceBody E₃}
    (h : axisAngle W S ≤ κ * ((cfg.a / cfg.b : NNReal) : ℝ)) :
    axisAngle W S ≤ 2 * ((ta.θ : NNReal) : ℝ) := by
  have hab : ((cfg.a / cfg.b : NNReal) : ℝ) ≤ ((ta.θ : NNReal) : ℝ) := by
    have := ta.hθab
    rw [ta.hratio] at this
    exact_mod_cast this
  have h0 : (0:ℝ) ≤ ((cfg.a / cfg.b : NNReal) : ℝ) := (cfg.a / cfg.b).coe_nonneg
  nlinarith

/-- **The size of the gap the re-cut closes.** In the tangential case the typical angle
satisfies `θ ≤ δ^{-τ'} (a/b)`, so the existing clause allows a tilt `2 δ^{-τ'} (a/b)` where the
transport can afford only `κ (a/b)`: the two differ by exactly the factor `δ^{-τ'}/κ`, and
that factor is the one that, pushed through
`Kakeya.VeryNotSticky.thickness_one_aniRescale_image_le_of_aligned`'s `β s` term, inflates the
comparison constant of (A2) by `δ^{-τ'}` and thence the enclosure constant by `δ^{-2τ'}`. -/
theorem tilt_gap_is_delta_pow_tau' {ratio thr s r₁ : ℝ} (hratio : 0 < ratio) (hr₁ : 0 < r₁)
    (hs : s = 2 * (thr * ratio)) :
    (ratio * r₁)⁻¹ * s = thr * (2 * r₁⁻¹) := by
  rw [hs]
  field_simp

/-! ### The packaged (A2), in the binder shape of `exists_slabPackage_general` -/

/-- The aspect ratio `a/b` of the configuration, as a positive real. -/
theorem cfg_ratio_pos (cfg : VeryNotSticky.{u}) :
    (0 : ℝ) < ((cfg.a / cfg.b : NNReal) : ℝ) := by
  have hb0 : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have ha0 : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
  have : (0 : NNReal) < cfg.a / cfg.b := div_pos ha0 hb0
  exact_mod_cast this

/-- The aspect ratio is at most one, since `a ≤ b`. -/
theorem cfg_ratio_le_one (cfg : VeryNotSticky.{u}) :
    ((cfg.a / cfg.b : NNReal) : ℝ) ≤ 1 := by
  have hb0 : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have : cfg.a / cfg.b ≤ 1 := div_le_one_of_le₀ cfg.hdims.2.1 (le_of_lt hb0)
  exact_mod_cast this

/-- `(a/b) · b = a`. -/
theorem cfg_ratio_mul_b (cfg : VeryNotSticky.{u}) :
    ((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.b : ℝ) = (cfg.a : ℝ) := by
  have hb0 : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have hb' : (cfg.b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
  push_cast
  field_simp

/-- `ρ₂ = b / r₁` in the reals. -/
theorem cfg_rho2_coe (cfg : VeryNotSticky.{u}) :
    ((cfg.rho2 : NNReal) : ℝ) = (cfg.b : ℝ) / (cfg.r₁ : ℝ) := by
  rw [VeryNotSticky.rho2, NNReal.coe_div]

/-- **Clause (A2) in the exact binder shape `Kakeya.VeryNotSticky.exists_slabPackage_general`
consumes — with two changes, both `δ`-free, and nothing else.**

The binder there reads

`∀ S Wd, IsDenseSlab cfg ta 𝕊 S Wd → ∀ j ∈ Wd,
   HasThicknesses (L S '' (bd.Wb j).carrier) bd.C₀ ![1, ρ₂, ρ₂]`

and what is produced here is the same statement with

1. the comparison constant `bd.C₀` replaced by the `δ`-free
   `Kakeya.VeryNotSticky.alignedRescaleConstant bd.C₀ κ`, and
2. the alignment hypothesis `axisAngle (bd.Wb j) S ≤ κ (a/b)` in place of
   `Kakeya.VeryNotSticky.IsDenseSlab.angle`'s `2θ`,

for a family of slabs each of which *is* the normalising ellipsoid
`Kakeya.VeryNotSticky.generalSlab` about its own centre and normal — which is what
`Kakeya.VeryNotSticky.hasThicknesses_generalSlab_C₀` and
`Kakeya.VeryNotSticky.slabRescale_A1_and_A1'` already assume for (S2), (A1) and (A1′).

Neither change costs an exponent: (1) is discharged by the `∀ᶠ δ` thresholds of
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_nonslab`, and (2) is a *strengthening* of the
existing clause whenever `κ ≤ 2` (`Kakeya.VeryNotSticky.axisAngle_le_two_theta_of_le_ratio`).
Both are statement re-cuts on unprotected objects and neither is licensed here. -/
theorem hasThicknesses_slabRescale_body_of_denseSlab (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    {ta : TypicalAngleData cfg tc hB τ'}
    {𝕊 : Set (ConvexSpaceBody E₃)} {κ : NNReal} (hκ : 1 ≤ κ)
    (ctr : ConvexSpaceBody E₃ → E₃)
    (hshape : ∀ S ∈ 𝕊, S = generalSlab (ctr S) (bodyNormal S) (norm_bodyNormal S)
      (r₁_pos cfg) (cfg_ratio_pos cfg))
    {S : ConvexSpaceBody E₃} {Wd : Finset bd.ω} (hslab : IsDenseSlab cfg ta 𝕊 S Wd)
    (halign : ∀ j ∈ Wd, axisAngle (bd.Wb j) S ≤ (κ : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ))
    {j : bd.ω} (hj : j ∈ Wd) :
    Kakeya.HasThicknesses
      (slabRescale (ctr S) (bodyNormal S) (norm_bodyNormal S) (r₁_pos cfg)
        (cfg_ratio_pos cfg) '' (bd.Wb j).carrier)
      (alignedRescaleConstant bd.C₀ κ) ![1, (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)] := by
  have hb0 : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have ha0 : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
  have hb0' : (0 : ℝ) < (cfg.b : ℝ) := by exact_mod_cast hb0
  have ha0' : (0 : ℝ) < (cfg.a : ℝ) := by exact_mod_cast ha0
  have hab' : (cfg.a : ℝ) ≤ (cfg.b : ℝ) := by exact_mod_cast cfg.hdims.2.1
  have hjB : j ∈ bd.bodies B := (tc.thinBall hB).bodies'_subset (ta.hsel (hslab.subset hj))
  have hprof := bd.bodies_thickness B hB j hjB
  have hSmem := hslab.mem
  have hSshape := hshape S hSmem
  have hsub : (bd.Wb j).carrier ⊆
      (generalSlab (ctr S) (bodyNormal S) (norm_bodyNormal S) (r₁_pos cfg)
        (cfg_ratio_pos cfg)).carrier := by
    rw [← hSshape]
    exact hslab.bodies_subset j hj
  have halign' : NonSlab.lineAngle (bodyNormal (bd.Wb j)) (bodyNormal S)
      ≤ (κ : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) := halign j hj
  have hmain := hasThicknesses_slabRescale_image_of_aligned (ctr S) (bodyNormal S)
    (norm_bodyNormal S) (r₁_pos cfg) (cfg_ratio_pos cfg) (cfg_ratio_le_one cfg) ha0' hb0'
    hab' (cfg_ratio_mul_b cfg) bd.hC₀ hκ (bd.Wb j) hprof hsub halign'
  rw [cfg_rho2_coe]
  exact hmain

/-- **Clause (A2′), the primed companion, at the same `δ`-free constant.**

(A2′) is the same assertion about the *outer* carrier `N_{τ₂(W)}(W)`, and it is the same
theorem: `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_aligned` is stated for an
arbitrary `ConvexSpaceBody`, so it applies verbatim once the thickened body's own three inputs
are in hand. Two of them are already in the tree —
`Kakeya.hasThicknesses_cthickening` gives the profile at the doubled constant, and the margin
hypothesis of `Kakeya.VeryNotSticky.slabRescale_A1_and_A1'`
gives the containment. The third, the alignment of the *thickened* body's normal, is a
separate obligation: `Kakeya.NonSlab.bodyNormal` is read off the thickened body's own outer
prism, which is not the body's. It is stated here as a hypothesis rather than assumed away. -/
theorem hasThicknesses_slabRescale_cthickening_of_aligned (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} {κ Ct : NNReal} (hκ : 1 ≤ κ) (hCt : 1 ≤ Ct) (cc n : E₃)
    (hn : ‖n‖ = 1) {j : bd.ω}
    (hprof : Kakeya.HasThicknesses ((bd.Wb j).cthickening (bd.Wb j).scale).carrier Ct
      ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)])
    (hsub : ((bd.Wb j).cthickening (bd.Wb j).scale).carrier ⊆
      (generalSlab cc n hn (r₁_pos cfg) (cfg_ratio_pos cfg)).carrier)
    (halign : NonSlab.lineAngle (bodyNormal ((bd.Wb j).cthickening (bd.Wb j).scale)) n
      ≤ (κ : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ)) :
    Kakeya.HasThicknesses
      (slabRescale cc n hn (r₁_pos cfg) (cfg_ratio_pos cfg) ''
        ((bd.Wb j).cthickening (bd.Wb j).scale).carrier)
      (alignedRescaleConstant Ct κ) ![1, (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)] := by
  have hb0 : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have ha0 : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
  have hb0' : (0 : ℝ) < (cfg.b : ℝ) := by exact_mod_cast hb0
  have ha0' : (0 : ℝ) < (cfg.a : ℝ) := by exact_mod_cast ha0
  have hab' : (cfg.a : ℝ) ≤ (cfg.b : ℝ) := by exact_mod_cast cfg.hdims.2.1
  have hmain := hasThicknesses_slabRescale_image_of_aligned cc n hn (r₁_pos cfg)
    (cfg_ratio_pos cfg) (cfg_ratio_le_one cfg) ha0' hb0' hab' (cfg_ratio_mul_b cfg) hCt hκ
    ((bd.Wb j).cthickening (bd.Wb j).scale) hprof hsub halign
  rw [cfg_rho2_coe]
  exact hmain

/-- **The degenerate tripwire survives the re-cut, and not by luck.** At `a = b` the aspect
ratio is `1`, so `Kakeya.VeryNotSticky.TypicalAngleData.hθab` and `.hθ1` pin `θ = 1` and the
proposed clause `axisAngle ≤ 2 (a/b)` is *the same real number* as the existing
`axisAngle ≤ 2 θ`. The degenerate producer
`Kakeya.VeryNotSticky.exists_slabPackage_degenerate_of_margin_of_general` therefore recovers
verbatim: the re-cut is invisible at `a = b`, which is exactly the regime the existing tripwire
exercises, and it bites only where `a < b`, which is the regime GWZ's §9.5 exists for. -/
theorem typicalAngle_eq_one_of_a_eq_b (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    (ta : TypicalAngleData cfg tc hB τ') (hab : cfg.a = cfg.b) :
    ((cfg.a / cfg.b : NNReal) : ℝ) = 1 ∧ ((ta.θ : NNReal) : ℝ) = 1 := by
  have hb0 : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have hone : cfg.a / cfg.b = 1 := by rw [hab, div_self hb0.ne']
  have hθ : ta.θ = 1 := le_antisymm ta.hθ1 (by rw [← hone, ← ta.hratio]; exact ta.hθab)
  exact ⟨by rw [hone]; norm_num, by rw [hθ]; norm_num⟩

/-! ### Does the existing containment already force the alignment?  No, and by exactly `1/ρ₂` -/

/-- **What containment in a slab does give**: a chord of `X` of length `ℓ` in the direction `u`
has `|⟪n, u⟫| · ℓ ≤ 2h`, where `h` is the slab's half-thickness along `n`. This is the only
mechanism by which clause (S3)'s containment `(bd.Wb j).carrier ⊆ (slabOf j).carrier` can
constrain the body's frame at all. -/
theorem abs_inner_mul_le_of_subset_slab (n : E₃) {X : Set E₃} {c : E₃} {h : ℝ}
    (hslab : ∀ x ∈ X, |⟪n, x - c⟫| ≤ h) {x y : E₃} (hx : x ∈ X) (hy : y ∈ X)
    {u : E₃} {ℓ : ℝ} (hxy : y - x = ℓ • u) :
    |⟪n, u⟫| * |ℓ| ≤ 2 * h := by
  have hd : (⟪n, y - x⟫ : ℝ) = ℓ * ⟪n, u⟫ := by rw [hxy, real_inner_smul_right]
  have hsplit : (⟪n, y - x⟫ : ℝ) = ⟪n, y - c⟫ - ⟪n, x - c⟫ := by
    rw [← inner_sub_right]; congr 1; abel
  have h1 := hslab x hx
  have h2 := hslab y hy
  have : |(⟪n, y - x⟫ : ℝ)| ≤ 2 * h := by
    rw [hsplit]
    calc |(⟪n, y - c⟫ : ℝ) - ⟪n, x - c⟫| ≤ |(⟪n, y - c⟫ : ℝ)| + |(⟪n, x - c⟫ : ℝ)| :=
          abs_sub _ _
      _ ≤ 2 * h := by linarith
  rw [hd, abs_mul, mul_comm] at this
  exact this

/-- **The slab is thicker than the body's thin dimension by exactly the factor `1/ρ₂`.**
Clause (S2) of `Kakeya.VeryNotSticky.IsSlabFamily` gives the slab the profile
`(r₁, r₁, (a/b) r₁)`, so its thin half-width is `(a/b) r₁ = a · (r₁/b) = a / ρ₂` — **not**
`∼ a`. (The radius `C₀ · a` that appears in clause (S4′)'s overlap guard is the *thickening*
the shading sandwich reaches, `τ₂(W) ≤ C₀ a`, and is a different object.) -/
theorem slab_thin_halfwidth_eq {a b r₁ : ℝ} (hb : 0 < b) :
    (a / b) * r₁ = a * (r₁ / b) := by field_simp

/-- **Containment does NOT force the alignment, and the shortfall is exactly `1/ρ₂`.**

Feed `Kakeya.VeryNotSticky.abs_inner_mul_le_of_subset_slab` with the slab's half-thickness
`h = C₀ (a/b) r₁` and with the body's middle chord, of length `ℓ ≥ b/C₀`: the bound it returns
is `|⟪n, e₁⟫| ≤ 2 C₀² (a r₁ / b²) = 2 C₀² (a/b)/ρ₂`. Clause (A2) needs `|⟪n, e₁⟫| ≤ κ (a/b)`
(`Kakeya.VeryNotSticky.thickness_one_aniRescale_image_le_of_aligned`). The two differ by the
factor `2C₀²/(κ ρ₂)`, and since `ρ₂ ≤ δ^{exscal} → 0`
(`Kakeya.VeryNotSticky.rho2_le_rpow_exscal`) the containment bound is **strictly weaker at
every scale in play**, at every `δ`-free `κ`.

So the alignment clause is genuinely new information about the slab family and not a
consequence of (S3): the additive fields R1/R2  stand. It is
also why GWZ's own (28) (`gwz.txt` l.2341-2343), which asks only for `W ⊂ S` and
`∠(T^W, T^S) ≤ θ`, does not by itself make their next sentence — "converts `𝕎''_S` to a set
`𝕋̃` of `ρ₂`-tubes" (l.2374-2375) — true. -/
theorem containment_tilt_bound_not_enough {a b r₁ C₀ κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr₁ : 0 < r₁) (hC₀ : 1 ≤ C₀) (hκ : 0 < κ) (hρ : κ * (b / r₁) < 2 * C₀ ^ 2) :
    κ * (a / b) < 2 * C₀ ^ 2 * (a * r₁ / b ^ 2) := by
  have hab : 0 < a / b := div_pos ha hb
  have hrb : (0:ℝ) < r₁ / b := div_pos hr₁ hb
  have hid : κ * (b / r₁) * (r₁ / b) = κ := by field_simp
  have hkey : κ < 2 * C₀ ^ 2 * (r₁ / b) := by
    have h := mul_lt_mul_of_pos_right hρ hrb
    rwa [hid] at h
  have he : 2 * C₀ ^ 2 * (a * r₁ / b ^ 2) = (2 * C₀ ^ 2 * (r₁ / b)) * (a / b) := by
    field_simp
  rw [he]
  exact mul_lt_mul_of_pos_right hkey hab

/-! ### R3–R6 measured: the whole Katz–Tao chain re-run at a general `δ`-free constant

`Kakeya.VeryNotSticky.KTRho2ScaleData` hard-codes the comparison constant `2 * bd.C₀`, so
"a larger `δ`-free constant is absorbed at zero exponent cost" cannot be checked by
instantiating the existing producer — the constant is not a parameter of it. It is checked here
by **re-running the chain**: the enclosure, the estimate and its `∀ᶠ δ` form are re-proved at
an arbitrary `δ`-free `Cmp ≥ 1`, and the exponents `(4ϱ, 9η, 3ϱ)` come out **identical**.

`Kakeya.VeryNotSticky.ktRho2ScaleDataAt_at_C₀` is the tripwire: at `Cmp = bd.C₀` the
generalised predicate is the existing one, definitionally.

The three proofs below are the existing ones with `bd.C₀` replaced by `Cmp` and `bd.hC₀` by
`hCmp` throughout; `bd` is otherwise used only for its index type `bd.ω`, which is why the
generalisation is mechanical. **That is the measurement**: nothing about `bd.C₀` beyond
`1 ≤ bd.C₀` is used anywhere in the chain, so every occurrence of the comparison constant is a
`δ`-free threshold and none of them is an exponent.

`Kakeya.VeryNotSticky.KTRho2ScaleDataAt` itself is declared in
`Kakeya.DimensionThree.MainLemma2.TangentialCase`, since
`Kakeya.VeryNotSticky.SlabMultKT.estimate` reads it, and the chain that produces it at a
general `Cmp` — `ktRho2ScaleDataAt_at_C₀`, `exists_enclosing_shadedTubes_of_ktRho2_at`,
`ktRho2ScaleData_of_ckt_nonslab_at`, `eventually_ktRho2ScaleDataAt_nonslab`,
`eventually_ktRho2ScaleDataAt_aligned` — now lives in
`Kakeya.DimensionThree.MainLemma2.SlabMultKTProduce`/`SlabMultKTGeneral`, upstream of the
degenerate boundary that has to read it (conjunct 4 of
`Kakeya.VeryNotSticky.SideDataObligations`). The declarations are unchanged, byte for byte.
-/

/-- **`hA2` discharged all the way to the multiplicity bound.**

Given (i) the aligned slab-membership clause and (ii) the estimate at the `δ`-free constant
`Kakeya.VeryNotSticky.alignedRescaleConstant bd.C₀ κ` — which
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleDataAt_aligned` supplies for small `δ` at the
existing exponents — the transported family `𝕋̃ = L(𝕎''_S)` of a dense slab satisfies the
Katz–Tao multiplicity bound. **No power of `δ` is spent on the transport**, and the fullness
clause is untouched (`Kakeya.VeryNotSticky.ktRho2_L_le_five_thirds`), so no bound on `we/wη`
is required anywhere.

This is what `exists_slabPackage_general`'s binder `hA2` is *for*; the binder itself still
reads the constant `bd.C₀`, which is re-cut R3  -/
theorem multiplicity_le_of_alignedDenseSlab (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    {ta : TypicalAngleData cfg tc hB τ'}
    {𝕊 : Set (ConvexSpaceBody E₃)} {κ : NNReal} (hκ : 1 ≤ κ)
    (ctr : ConvexSpaceBody E₃ → E₃)
    (hshape : ∀ S ∈ 𝕊, S = generalSlab (ctr S) (bodyNormal S) (norm_bodyNormal S)
      (r₁_pos cfg) (cfg_ratio_pos cfg))
    {S : ConvexSpaceBody E₃} {Wd : Finset bd.ω} (hslab : IsDenseSlab cfg ta 𝕊 S Wd)
    (halign : ∀ j ∈ Wd, axisAngle (bd.Wb j) S ≤ (κ : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ))
    {ε η₁ κ' : ℝ}
    (hKT : cfg.KTRho2ScaleDataAt bd (alignedRescaleConstant bd.C₀ κ) ε η₁ κ')
    (T : bd.ω → ShadedBody E₃)
    (hcar : ∀ j ∈ Wd, (T j).carrier = slabRescale (ctr S) (bodyNormal S) (norm_bodyNormal S)
      (r₁_pos cfg) (cfg_ratio_pos cfg) '' (bd.Wb j).carrier)
    (hball : ∀ j ∈ Wd, (T j).carrier ⊆ Metric.closedBall 0 1)
    (hKTt : ConvexSpaceBody.IsKatzTao Wd (fun j ↦ (T j).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-κ')))
    (hfull : cfg.δ ^ η₁ ≤ ShadedBody.fullness Wd T) :
    ShadedBody.multiplicity Wd T ≤ (cfg.δ : ENNReal) ^ (-ε) * (Wd.card : ENNReal) ^ cfg.β := by
  refine hKT Wd T hball (fun j hj => ?_) hKTt hfull
  have hA2 := hasThicknesses_slabRescale_body_of_denseSlab cfg hκ ctr hshape hslab halign hj
  rw [hcar j hj]
  refine hasThicknesses_mono_const ?_ ?_ ?_ hA2
  · have h4 : (1 : NNReal) ≤ bd.C₀ ^ 4 := one_le_pow₀ bd.hC₀
    calc (0 : NNReal) < 1 := zero_lt_one
      _ = 1 * 1 * 1 := by norm_num
      _ ≤ 2304 * (3 + κ) * bd.C₀ ^ 4 := by
          gcongr
          · norm_num
          · exact hκ.trans le_add_self
      _ = alignedRescaleConstant bd.C₀ κ := rfl
  · exact le_mul_of_one_le_left bot_le one_le_two
  · intro k
    fin_cases k <;> simp

/-! ### R6 measured: the `δ`-free constant in `slabCard`'s absorption, at a general `Cmp` -/

/-- The numeral `48 C₀³` of `Kakeya.VeryNotSticky.slabCard` at a general comparison constant:
the unit ball's volume `8` divided by the volume floor `ρ₂²/(6 Cmp³)` of
`Kakeya.VeryNotSticky.volume_ge_of_tubeProfile`. **Nothing about `Cmp` enters but its cube.** -/
theorem slabCard_numeral_at {Cmp ρ : ℝ} (hCmp : 0 < Cmp) (hρ : 0 < ρ) :
    (8 : ℝ) / (ρ ^ 2 / (6 * Cmp ^ 3)) = 48 * Cmp ^ 3 / ρ ^ 2 := by
  field_simp
  ring

/-- **R6, measured.** `Kakeya.VeryNotSticky.IsSlabDeltamaxConstant` is already stated with the
comparison constant as a *free variable*, so the re-cut is a theorem application and not an
edit: at `alignedRescaleConstant C₀ κ` the admissibility of
`Kakeya.VeryNotSticky.degenerateCΔ` holds verbatim. -/
theorem isSlabDeltamaxConstant_aligned {C₀ Cbias κ : NNReal} (hC₀ : 1 ≤ C₀) (hκ : 1 ≤ κ)
    (hCb : 1 ≤ Cbias) :
    IsSlabDeltamaxConstant (alignedRescaleConstant C₀ κ)
      (degenerateCΔ (alignedRescaleConstant C₀ κ) Cbias) := by
  refine isSlabDeltamaxConstant_degenerateCΔ ?_ hCb
  have h4 : (1 : NNReal) ≤ C₀ ^ 4 := one_le_pow₀ hC₀
  calc (1 : NNReal) = 1 * 1 * 1 := by norm_num
    _ ≤ 2304 * (3 + κ) * C₀ ^ 4 := by
        gcongr
        · norm_num
        · exact hκ.trans le_add_self
    _ = alignedRescaleConstant C₀ κ := rfl

/-- **…and the absorption is the same fixed-scale threshold, at any `Cmp`.** `slabCard`'s
`48 Cmp³ ≤ 2^10 Cmp³ ≤ CΔ ≤ δ^{-ϱ/2}` and the exponent identity
`δ^{-5ϱ/2} · δ^{-ϱ/2} = δ^{-3ϱ}` are both independent of `Cmp`, so the conclusion exponent
`3ϱ` of `Kakeya.VeryNotSticky.slabCard` **does not move** under R3–R6. -/
theorem slabCard_absorption_at (cfg : VeryNotSticky.{u}) {Cmp CΔ : NNReal}
    (hadm : IsSlabDeltamaxConstant Cmp CΔ)
    (hCΔ : (CΔ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2))) :
    ((48 * Cmp ^ 3 : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) := by
  refine le_trans ?_ hCΔ
  have h48 : (48 * Cmp ^ 3 : NNReal) ≤ (2 : NNReal) ^ 10 * Cmp ^ 3 :=
    mul_le_mul_of_nonneg_right (by norm_num) bot_le
  exact_mod_cast h48.trans hadm.card_le

/-- The exponent identity `slabCard` closes with, unchanged at any `Cmp`. -/
theorem slabCard_exponent_identity (cfg : VeryNotSticky.{u}) :
    (cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2)) * (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2))
      = (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) := by
  have hδ : (cfg.δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr cfg.hδ).ne'
  have hδ_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rw [← ENNReal.rpow_add _ _ hδ hδ_top]
  congr 1
  ring

/-! ### The angular sub-classing, and why its count is free -/

/-- **The sub-class count is exactly the `δ^{-2τ'}` the tree already pays.**

Splitting each slab direction-class by body normal at resolution `κ (a/b)` over the typical
angle's range `thr · (a/b)` — `thr = δ^{-τ'}` in the tangential case, by
`Kakeya.VeryNotSticky.TypicalAngleData.hθab` and the tangential guard — gives `(thr/κ)²` cells
in the two angular dimensions: **the scale `a/b` cancels**, exactly as it does in
`Kakeya.VeryNotSticky.slabDecompFibreConstant`'s own derivation ("the aperture of the cone being
`3 Ctyp δ^{-τ'} a/b` and the separation of its normals `c(C₀) a/b`, so that the scale `a/b`
cancels"), and what is left is `δ^{-2τ'}` times a `δ`-free constant `κ^{-2}` of exactly the
shape `slabDecompFibreConstant` already carries. **So the angular sub-classing that makes R1
hold by construction is charged to the fibre count at the existing exponent, and costs no new
power of `δ`.** -/
theorem angular_subclass_count {ratio thr κ : ℝ} (hratio : 0 < ratio) :
    ((thr * ratio) / (κ * ratio)) ^ 2 = thr ^ 2 / κ ^ 2 := by
  rw [mul_div_mul_right _ _ hratio.ne', div_pow]

/-! ### Building `hfam`: the positional obstruction, located exactly -/

/-- The normalising ellipsoid reaches distance `r₁` from its own centre, in **every** direction
orthogonal to its normal: `c ± r₁ u ∈ generalSlab c n` for any unit `u ⊥ n`. This is the sense
in which clause (S2)'s profile `(r₁, r₁, (a/b) r₁)` is *exact* for it
(`Kakeya.VeryNotSticky.hasThicknesses_generalSlab`). -/
theorem mem_generalSlab_of_orthogonal (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) {u : E₃} (hu : ‖u‖ = 1) (hun : ⟪n, u⟫ = (0 : ℝ)) {t : ℝ}
    (ht : |t| ≤ r₁) : c + t • u ∈ (generalSlab c n hn hr₁ hratio).carrier := by
  rw [mem_generalSlab_iff]
  have hsub : c + t • u - c = t • u := by abel
  rw [hsub]
  have hinner : (⟪n, t • u⟫ : ℝ) = 0 := by rw [real_inner_smul_right, hun, mul_zero]
  have hnorm : ‖aniLin n r₁⁻¹ (ratio * r₁)⁻¹ (t • u)‖ ^ 2 = (r₁⁻¹) ^ 2 * ‖t • u‖ ^ 2 := by
    rw [norm_sq_aniLin n hn, hinner]
    ring
  have htu : ‖t • u‖ = |t| := by rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
  have hle : ‖aniLin n r₁⁻¹ (ratio * r₁)⁻¹ (t • u)‖ ^ 2 ≤ 1 ^ 2 := by
    rw [hnorm, htu, one_pow]
    have h1 : |t| ^ 2 ≤ r₁ ^ 2 := by nlinarith [abs_nonneg t]
    have h2 : (r₁⁻¹) ^ 2 * r₁ ^ 2 = 1 := by field_simp
    nlinarith [sq_nonneg (r₁⁻¹), inv_pos.mpr hr₁]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).mp hle

/-- **The positional obstruction to `hfam`, compiled: clause (S2)'s ball half at radius `r₁`
admits no off-centre slab at all.**

If the normalising ellipsoid `generalSlab c n` lies inside `B̄(z, r₁)` then `c = z`, by the
parallelogram law applied to the two points `c ± r₁ u` for a unit `u ⊥ n`, both of which the
ellipsoid contains (`Kakeya.VeryNotSticky.mem_generalSlab_of_orthogonal`):
`‖w + r₁u‖² + ‖w - r₁u‖² = 2‖w‖² + 2r₁² ≤ 2r₁²` forces `w = c - z = 0`.

**This is 's "positional conflict", made exact.** GWZ's family is "a
maximal set of essentially disjoint slabs `S ⊂ B`" and "contains `∼ b/a` parallel translates per
direction" (`gwz.txt` l.2337-2339, quoted in `IsSlabFamily.S4`'s own docstring). Clause
`S2_ball` at radius `r₁` admits **zero** translates: every slab of `𝕊` is forced to be centred
at `bd.ctr B`, so `𝕊` is a family of *concentric* ellipsoids and clause (S3)'s containment
`(bd.Wb j).carrier ⊆ (slabOf j).carrier` can only be met by bodies within `(a/b) r₁` of a plane
**through the ball's centre**. That is why three rounds of `hfam` attempts have failed, and it
is not a defect of the constructions.

Use `S2_ball` at `2 r₁`, with (A1) re-routed through `IsDenseSlab.mem`; the general branch does not even
need that re-route, since `Kakeya.VeryNotSticky.slabRescale_A1_and_A1'` gives (A1) as an
*equality* onto `B₁` for whatever centre the slab has). See
`Kakeya.VeryNotSticky.generalSlab_subset_closedBall_two`. -/
theorem center_eq_of_generalSlab_subset_closedBall (c n z : E₃) (hn : ‖n‖ = 1)
    {r₁ ratio : ℝ} (hr₁ : 0 < r₁) (hratio : 0 < ratio)
    (hsub : (generalSlab c n hn hr₁ hratio).carrier ⊆ Metric.closedBall z r₁) : c = z := by
  -- a unit vector orthogonal to `n`
  have hn0 : n ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have hrk : Module.rank ℝ (AffineSubspace.mk' c (ℝ ∙ n)).direction ≤ (1 : ℕ) := by
    rw [AffineSubspace.direction_mk']
    simpa using rank_span_le ({n} : Set E₃)
  obtain ⟨u, hu_mem, hu_norm⟩ := Metric.exists_unit_orthogonal_of_rank_lt
    (AffineSubspace.mk' c (ℝ ∙ n)) hrk (by rw [finrank_euclideanSpace_fin]; norm_num)
  rw [AffineSubspace.direction_mk'] at hu_mem
  have hun : (⟪n, u⟫ : ℝ) = 0 := hu_mem n (Submodule.mem_span_singleton_self n)
  -- the two extreme points
  have hp : c + r₁ • u ∈ Metric.closedBall z r₁ :=
    hsub (mem_generalSlab_of_orthogonal c n hn hr₁ hratio hu_norm hun (by rw [abs_of_pos hr₁]))
  have hm : c + (-r₁) • u ∈ Metric.closedBall z r₁ :=
    hsub (mem_generalSlab_of_orthogonal c n hn hr₁ hratio hu_norm hun
      (by rw [abs_of_neg (neg_neg_iff_pos.mpr hr₁)]; linarith))
  rw [Metric.mem_closedBall, dist_eq_norm] at hp hm
  set w : E₃ := c - z with hw
  have hp' : ‖w + r₁ • u‖ ≤ r₁ := by
    have : c + r₁ • u - z = w + r₁ • u := by rw [hw]; abel
    rwa [this] at hp
  have hm' : ‖w - r₁ • u‖ ≤ r₁ := by
    have : c + (-r₁) • u - z = w - r₁ • u := by rw [hw, neg_smul]; abel
    rwa [this] at hm
  have hpar : ‖w + r₁ • u‖ ^ 2 + ‖w - r₁ • u‖ ^ 2 = 2 * ‖w‖ ^ 2 + 2 * ‖r₁ • u‖ ^ 2 := by
    simpa using norm_add_sq_real w (r₁ • u) ▸ norm_sub_sq_real w (r₁ • u) ▸ (by ring :
      (‖w‖ ^ 2 + 2 * ⟪w, r₁ • u⟫ + ‖r₁ • u‖ ^ 2) + (‖w‖ ^ 2 - 2 * ⟪w, r₁ • u⟫ + ‖r₁ • u‖ ^ 2)
        = 2 * ‖w‖ ^ 2 + 2 * ‖r₁ • u‖ ^ 2)
  have hru : ‖r₁ • u‖ = r₁ := by
    rw [norm_smul, hu_norm, mul_one, Real.norm_eq_abs, abs_of_pos hr₁]
  have hw0 : ‖w‖ = 0 := by
    nlinarith [norm_nonneg (w + r₁ • u), norm_nonneg (w - r₁ • u), norm_nonneg w]
  have hz : w = 0 := norm_eq_zero.mp hw0
  rw [hw] at hz
  exact sub_eq_zero.mp hz

/-- **The licensed exit**: at radius `2 r₁` the ball half holds for every slab whose centre lies
in the ball, because the ellipsoid is inside `B̄(c, r₁)`
(`Kakeya.VeryNotSticky.generalSlab_subset_closedBall`) and the triangle inequality does the
rest. This bound also accommodates translated slabs. -/
theorem generalSlab_subset_closedBall_two (c n z : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ}
    (hr₁ : 0 < r₁) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1)
    (hcz : dist c z ≤ r₁) :
    (generalSlab c n hn hr₁ hratio).carrier ⊆ Metric.closedBall z (2 * r₁) := by
  intro x hx
  have h1 := generalSlab_subset_closedBall c n hn hr₁ hratio hratio1 hx
  rw [Metric.mem_closedBall] at h1 ⊢
  calc dist x z ≤ dist x c + dist c z := dist_triangle _ _ _
    _ ≤ r₁ + r₁ := add_le_add h1 hcz
    _ = 2 * r₁ := by ring

/-- **The obstruction in the tree's own vocabulary.** For a family of normalising ellipsoids —
which is what `Kakeya.VeryNotSticky.hasThicknesses_generalSlab_C₀` and
`Kakeya.VeryNotSticky.slabRescale_A1_and_A1'` already assume, and what
`Kakeya.VeryNotSticky.hasThicknesses_slabRescale_body_of_denseSlab` needs — a *containment*
clause `S ⊆ B̄(ctr B, r₁)` forces the slab's centre to be the ball's centre.

**This is the compiled reason clause (S2)-ball was re-cut to an intersection.** The containment
hypothesis `hball` below is the deleted field `IsDenseSlab.ball`; it is now supplied by the
caller, and no producer of the re-cut `Kakeya.VeryNotSticky.IsSlabFamily` can supply it, which
is exactly the point: the refined source's lattice slab cells are not inside the ball
(`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1680) and must not be, or the family
admits none of the "`∼ b/a` parallel translates per direction" it is built from. The theorem is
retained as the record of the obstruction that forced the re-cut. -/
-- H-L1 has since moved `IsDenseSlab.ball` to
-- `2 r₁`, so the radius-`r₁` containment is taken as an explicit hypothesis: this theorem is
-- the *record of the obstruction H-L1 removes*, and `Kakeya.VeryNotSticky.mem_generalSlab_iff`
-- plus `Kakeya.VeryNotSticky.generalSlab_subset_closedBall_two` are what replace it.
theorem denseSlab_center_forced (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    {ta : TypicalAngleData cfg tc hB τ'} {𝕊 : Set (ConvexSpaceBody E₃)}
    (ctr : ConvexSpaceBody E₃ → E₃)
    (hshape : ∀ S ∈ 𝕊, S = generalSlab (ctr S) (bodyNormal S) (norm_bodyNormal S)
      (r₁_pos cfg) (cfg_ratio_pos cfg))
    {S : ConvexSpaceBody E₃} {Wd : Finset bd.ω} (hslab : IsDenseSlab cfg ta 𝕊 S Wd)
    (hball₁ : S.carrier ⊆ Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) :
    ctr S = bd.ctr B := by
  have hS := hshape S hslab.mem
  refine center_eq_of_generalSlab_subset_closedBall (ctr S) (bodyNormal S) (bd.ctr B)
    (norm_bodyNormal S) (r₁_pos cfg) (cfg_ratio_pos cfg) ?_
  rw [← hS]
  exact hball₁

/-- **…and therefore every body of every dense slab lies within `(a/b) r₁` of a plane through
the ball's centre.** GWZ's family has `∼ b/a` parallel translates per direction
(`gwz.txt` l.2337-2339); this says the tree's `S2_ball` at `r₁` allows none of them, so no
`hfam` producing normalising ellipsoids can meet clause (S3) for a body off the central plane.
The already-licensed H-L1 removes the obstruction —
`Kakeya.VeryNotSticky.generalSlab_subset_closedBall_two`. -/
theorem denseSlab_bodies_near_center_plane (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    {ta : TypicalAngleData cfg tc hB τ'} {𝕊 : Set (ConvexSpaceBody E₃)}
    (ctr : ConvexSpaceBody E₃ → E₃)
    (hshape : ∀ S ∈ 𝕊, S = generalSlab (ctr S) (bodyNormal S) (norm_bodyNormal S)
      (r₁_pos cfg) (cfg_ratio_pos cfg))
    {S : ConvexSpaceBody E₃} {Wd : Finset bd.ω} (hslab : IsDenseSlab cfg ta 𝕊 S Wd)
    (hball₁ : S.carrier ⊆ Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ))
    {j : bd.ω} (hj : j ∈ Wd) {x : E₃} (hx : x ∈ (bd.Wb j).carrier) :
    |⟪bodyNormal S, x - bd.ctr B⟫| ≤ ((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ) := by
  have hc := denseSlab_center_forced cfg ctr hshape hslab hball₁
  have hS := hshape S hslab.mem
  have hxS : x ∈ (generalSlab (ctr S) (bodyNormal S) (norm_bodyNormal S) (r₁_pos cfg)
      (cfg_ratio_pos cfg)).carrier := by
    rw [← hS]
    exact hslab.bodies_subset j hj hx
  have := abs_inner_le_of_mem_generalSlab (ctr S) (bodyNormal S) (norm_bodyNormal S)
    (r₁_pos cfg) (cfg_ratio_pos cfg) hxS
  rwa [hc] at this

/-! ### Determinacy of `bodyNormal` on the normalising ellipsoid -/

/-- **`bodyNormal` is determined, to within the aspect ratio, on the normalising ellipsoid.**

`Kakeya.NonSlab.bodyNormal` is `outerPrism.basis … 2`, a `Classical.choose`, and the tree has
no determinacy lemma for it — which is what  recorded as the reason a
counterexample body could not be compiled, and what blocks *any* construction of a slab family
from proving clause (S4′) or the alignment clause R1, both of which are stated through
`Kakeya.VeryNotSticky.axisAngle`.

For the ellipsoid of semi-axes `(R, R, ratio · R)` the frame **is** determined up to `ratio`:
the outer prism's rank-`2` half-width is exactly `ratio · R`
(`Kakeya.VeryNotSticky.hasThicknesses_generalSlab` at comparison constant `1`), while the
ellipsoid reaches `± R` in every direction orthogonal to `n`
(`Kakeya.VeryNotSticky.mem_generalSlab_of_orthogonal`), so the component of `bodyNormal` along
any unit `u ⊥ n` is at most `ratio`. Taking `u` in the direction of `bodyNormal`'s own
orthogonal part gives `‖(n(S))_{⊥n}‖ ≤ ratio` — i.e. `sin ∠(n(S), n) ≤ ratio`. -/
theorem norm_bodyNormal_orthogonal_le (c n : E₃) (hn : ‖n‖ = 1) {R ratio : ℝ} (hR : 0 < R)
    (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) :
    ‖bodyNormal (generalSlab c n hn hR hratio)
        - (⟪n, bodyNormal (generalSlab c n hn hR hratio)⟫ : ℝ) • n‖ ≤ ratio := by
  set S := generalSlab c n hn hR hratio with hS
  set e : E₃ := bodyNormal S with he
  set w : E₃ := e - (⟪n, e⟫ : ℝ) • n with hw
  rcases eq_or_ne w 0 with h0 | h0
  · rw [h0, norm_zero]; exact hratio.le
  -- the unit vector in the direction of `w`, orthogonal to `n`
  set u : E₃ := ‖w‖⁻¹ • w with hu
  have hwpos : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr h0
  have hunorm : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwpos), inv_mul_cancel₀ hwpos.ne']
  have hnn : (⟪n, n⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hwn : (⟪n, w⟫ : ℝ) = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, hnn, mul_one, sub_self]
  have hun : (⟪n, u⟫ : ℝ) = 0 := by rw [hu, real_inner_smul_right, hwn, mul_zero]
  -- the two extreme points of the ellipsoid along `u`
  have hp : c + R • u ∈ S.carrier :=
    mem_generalSlab_of_orthogonal c n hn hR hratio hunorm hun (by rw [abs_of_pos hR])
  have hm : c + (-R) • u ∈ S.carrier :=
    mem_generalSlab_of_orthogonal c n hn hR hratio hunorm hun
      (by rw [abs_of_neg (neg_neg_iff_pos.mpr hR)]; linarith)
  -- the rank-`2` half-width of the outer prism is exactly `ratio · R`
  have hprof := hasThicknesses_generalSlab c n hn hR hratio hratio1 (le_refl (1 : NNReal))
  have hτ2 : Metric.thickness ℝ S.carrier 2 ≤ ratio * R := by
    have := (hprof 2).2
    simpa using this
  set hfr : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin with hfr_def
  have he2 : e = outerPrism.basis hfr S.isCompact' S.nonempty' 2 := by
    rw [he, bodyNormal, NonSlab.bodyNormal_eq]
  have hbp := outerPrism.basis_repr_le hfr S.isCompact' S.nonempty' hp 2
  have hbm := outerPrism.basis_repr_le hfr S.isCompact' S.nonempty' hm 2
  simp only [OrthonormalBasis.repr_apply_apply, ← he2] at hbp hbm
  -- subtract: `|⟪e, 2R u⟫| ≤ 2 ratio R`
  have hdiff : |(⟪e, (2 * R) • u⟫ : ℝ)| ≤ 2 * (ratio * R) := by
    have hex : ((2 * R) • u : E₃)
        = (c + R • u - outerPrism.center hfr S.isCompact' S.nonempty')
          - (c + (-R) • u - outerPrism.center hfr S.isCompact' S.nonempty') := by
      rw [neg_smul]
      match_scalars <;> ring
    rw [hex, inner_sub_right]
    calc |(⟪e, c + R • u - outerPrism.center hfr S.isCompact' S.nonempty'⟫ : ℝ)
            - ⟪e, c + (-R) • u - outerPrism.center hfr S.isCompact' S.nonempty'⟫|
        ≤ |(⟪e, c + R • u - outerPrism.center hfr S.isCompact' S.nonempty'⟫ : ℝ)|
          + |(⟪e, c + (-R) • u - outerPrism.center hfr S.isCompact' S.nonempty'⟫ : ℝ)| :=
          abs_sub _ _
      _ ≤ Metric.thickness ℝ S.carrier 2 + Metric.thickness ℝ S.carrier 2 := add_le_add hbp hbm
      _ ≤ 2 * (ratio * R) := by linarith
  -- `⟪e, u⟫ = ‖w‖`
  have heu : (⟪e, u⟫ : ℝ) = ‖w‖ := by
    have hee : (⟪e, e⟫ : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, he, norm_bodyNormal]; norm_num
    have hen : (⟪e, n⟫ : ℝ) = ⟪n, e⟫ := (real_inner_comm e n).symm
    have hkey : (⟪e, w⟫ : ℝ) = 1 - (⟪n, e⟫ : ℝ) ^ 2 := by
      rw [hw]
      simp only [inner_sub_right, real_inner_smul_right, hee, hen]
      ring
    have hnorm2 : ‖w‖ ^ 2 = 1 - (⟪n, e⟫ : ℝ) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hw]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hee, hnn, hen]
      ring
    have hew : (⟪e, w⟫ : ℝ) = ‖w‖ ^ 2 := by rw [hkey, hnorm2]
    rw [hu, real_inner_smul_right, hew]
    field_simp
  rw [real_inner_smul_right, heu, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * R),
    abs_of_pos hwpos] at hdiff
  nlinarith

/-- The orthogonal part of one unit vector against another has norm `sin` of the line angle. -/
theorem norm_orthogonal_eq_sin_lineAngle {u v : E₃} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - (⟪v, u⟫ : ℝ) • v‖ = Real.sin (NonSlab.lineAngle u v) := by
  have hvv : (⟪v, v⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have huu : (⟪u, u⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have huv : (⟪u, v⟫ : ℝ) = ⟪v, u⟫ := (real_inner_comm u v).symm
  have hsq : ‖u - (⟪v, u⟫ : ℝ) • v‖ ^ 2 = 1 - (⟪u, v⟫ : ℝ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      huu, hvv, huv]
    ring
  have hle : (⟪u, v⟫ : ℝ) ^ 2 ≤ 1 := by
    have := abs_real_inner_le_norm u v
    rw [hu, hv, mul_one] at this
    nlinarith [abs_nonneg (⟪u, v⟫ : ℝ), sq_abs (⟪u, v⟫ : ℝ)]
  rw [NonSlab.lineAngle_eq_arccos_abs_inner hu hv, Real.sin_arccos, sq_abs]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- **Determinacy in the form the angle clauses read it**: the slab's `bodyNormal` is within
`2 · ratio` of the slab's defining normal `n`, in `Kakeya.NonSlab.lineAngle`. With
`ratio = a/b` this is exactly the resolution at which clause R1 (`S3_ratio`) and clause (S4′)
are stated, so a family of normalising ellipsoids can prove **both by construction**.

Jordan's inequality `2/π · θ ≤ sin θ` on `[0, π/2]` turns
`Kakeya.VeryNotSticky.norm_bodyNormal_orthogonal_le`'s `sin ∠ ≤ ratio` into `∠ ≤ (π/2) ratio`,
and `π/2 ≤ 2`. -/
theorem lineAngle_bodyNormal_generalSlab_le (c n : E₃) (hn : ‖n‖ = 1) {R ratio : ℝ}
    (hR : 0 < R) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) :
    NonSlab.lineAngle (bodyNormal (generalSlab c n hn hR hratio)) n ≤ 2 * ratio := by
  set e : E₃ := bodyNormal (generalSlab c n hn hR hratio) with he
  have hene : ‖e‖ = 1 := norm_bodyNormal _
  have hsin : Real.sin (NonSlab.lineAngle e n) ≤ ratio := by
    rw [← norm_orthogonal_eq_sin_lineAngle hene hn]
    exact norm_bodyNormal_orthogonal_le c n hn hR hratio hratio1
  have h0 : 0 ≤ NonSlab.lineAngle e n := NonSlab.lineAngle_nonneg _ _
  have h2 : NonSlab.lineAngle e n ≤ Real.pi / 2 := by
    rw [NonSlab.lineAngle_eq_arccos_abs_inner hene hn]
    exact Real.arccos_le_pi_div_two.mpr (abs_nonneg _)
  have hj := Real.mul_le_sin h0 h2
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have : 2 / Real.pi * NonSlab.lineAngle e n ≤ ratio := le_trans hj hsin
  rw [div_mul_eq_mul_div, div_le_iff₀ hpipos] at this
  nlinarith

/-! ### Two transverse slabs pinch to a line — the input clause (S1) needs -/

/-- The span of two orthogonal unit vectors of `ℝ³` has a rank-`1` orthogonal complement. -/
theorem rank_orthogonal_sup_le_one {n m : E₃} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hnm : (⟪n, m⟫ : ℝ) = 0) :
    Module.rank ℝ (((ℝ ∙ n) ⊔ (ℝ ∙ m) : Submodule ℝ E₃)ᗮ : Submodule ℝ E₃) ≤ (1 : ℕ) := by
  have hn0 : n ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have hm0 : m ≠ 0 := by intro h; rw [h, norm_zero] at hm; norm_num at hm
  have hinf : (ℝ ∙ n) ⊓ (ℝ ∙ m) = (⊥ : Submodule ℝ E₃) := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx.1
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hx.2
    have hnn : (⟪n, n⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
    have : (⟪n, a • n⟫ : ℝ) = ⟪n, b • m⟫ := by rw [hb]
    rw [real_inner_smul_right, real_inner_smul_right, hnn, hnm, mul_one, mul_zero] at this
    simp [this]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ n) (ℝ ∙ m)
  rw [hinf, finrank_bot, finrank_span_singleton hn0, finrank_span_singleton hm0] at hsum
  have hsup : Module.finrank ℝ ((ℝ ∙ n) ⊔ (ℝ ∙ m) : Submodule ℝ E₃) = 2 := by omega
  have horth := Submodule.finrank_add_finrank_orthogonal
    (K := ((ℝ ∙ n) ⊔ (ℝ ∙ m) : Submodule ℝ E₃))
  have h3 : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin
  rw [hsup, h3] at horth
  rw [← Module.finrank_eq_rank]
  exact_mod_cast (by omega :
    Module.finrank ℝ (((ℝ ∙ n) ⊔ (ℝ ∙ m) : Submodule ℝ E₃)ᗮ : Submodule ℝ E₃) ≤ 1)

/-- **Two transverse slabs pinch their intersection to a line.**

If `X` lies in the slab of half-width `t` about the plane `⟪n, · - p⟫ = 0` and in the slab of
half-width `t` about `⟪n', · - q⟫ = 0`, and the two normals are separated — `σ ≤ ‖n' - ⟪n,n'⟫n‖`,
the sine of the angle between them — then `X` lies within `6t/σ` of a line.

This is the input clause (S1) of `Kakeya.VeryNotSticky.IsSlabFamily` needs: essential
distinctness of two slabs of the family is a volume comparison, and the volume of the
intersection is controlled by its rank-`1` thickness. -/
theorem thickness_one_le_of_two_slabs (n n' : E₃) (hn : ‖n‖ = 1) (hn' : ‖n'‖ = 1)
    {X : Set E₃} {p q : E₃} {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ)
    {x₀ : E₃} (hx₀ : x₀ ∈ X)
    (h1 : ∀ x ∈ X, |(⟪n, x - p⟫ : ℝ)| ≤ t) (h2 : ∀ x ∈ X, |(⟪n', x - q⟫ : ℝ)| ≤ t)
    (hσle : σ ≤ ‖n' - (⟪n, n'⟫ : ℝ) • n‖) :
    Metric.thickness ℝ X 1 ≤ 6 * t / σ := by
  set v : E₃ := n' - (⟪n, n'⟫ : ℝ) • n with hv
  have hnn : (⟪n, n⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hn'n' : (⟪n', n'⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hn']; norm_num
  have hvpos : (0:ℝ) < ‖v‖ := lt_of_lt_of_le hσ hσle
  have hv1 : ‖v‖ ≤ 1 := by
    have h := norm_orthogonal_eq_sin_lineAngle hn' hn
    rw [hv, h]
    exact Real.sin_le_one _
  set m : E₃ := ‖v‖⁻¹ • v with hm
  have hmnorm : ‖m‖ = 1 := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos),
      inv_mul_cancel₀ hvpos.ne']
  have hnv : (⟪n, v⟫ : ℝ) = 0 := by
    rw [hv, inner_sub_right, real_inner_smul_right, hnn, mul_one, sub_self]
  have hnm : (⟪n, m⟫ : ℝ) = 0 := by rw [hm, real_inner_smul_right, hnv, mul_zero]
  have hmn' : (⟪m, n'⟫ : ℝ) = ‖v‖ := by
    have hnn' : (⟪n', n⟫ : ℝ) = ⟪n, n'⟫ := (real_inner_comm n' n).symm
    have hvv : (⟪v, v⟫ : ℝ) = 1 - (⟪n, n'⟫ : ℝ) ^ 2 := by
      rw [hv]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hnn, hn'n', hnn']
      ring
    have hvn'0 : (⟪v, n'⟫ : ℝ) = 1 - (⟪n, n'⟫ : ℝ) ^ 2 := by
      rw [hv]
      simp only [inner_sub_left, real_inner_smul_left, hn'n']
      ring
    have hvn' : (⟪v, n'⟫ : ℝ) = ‖v‖ ^ 2 := by
      rw [hvn'0, ← hvv, real_inner_self_eq_norm_sq]
    rw [hm, real_inner_smul_left, hvn']
    field_simp
  -- the affine subspace: the line `x₀ + span{n, m}ᗮ`
  set A : AffineSubspace ℝ E₃ := AffineSubspace.mk' x₀ (((ℝ ∙ n) ⊔ (ℝ ∙ m) : Submodule ℝ E₃)ᗮ)
    with hA
  have hArk : Module.rank ℝ A.direction ≤ (1 : ℕ) := by
    rw [hA, AffineSubspace.direction_mk']
    exact rank_orthogonal_sup_le_one hn hmnorm hnm
  have hRpos : (0:ℝ) ≤ 6 * t / σ := by positivity
  refine Metric.thickness_le_of_cthickening hRpos hArk ?_
  intro x hx
  set d : E₃ := x - x₀ with hd
  set α : ℝ := ⟪n, d⟫ with hα
  set β : ℝ := ⟪m, d⟫ with hβ
  -- `|α| ≤ 2t`
  have hαle : |α| ≤ 2 * t := by
    have e : (⟪n, d⟫ : ℝ) = ⟪n, x - p⟫ - ⟪n, x₀ - p⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hd]; abel
    rw [hα, e]
    calc |(⟪n, x - p⟫ : ℝ) - ⟪n, x₀ - p⟫| ≤ |(⟪n, x - p⟫ : ℝ)| + |(⟪n, x₀ - p⟫ : ℝ)| := abs_sub _ _
      _ ≤ t + t := add_le_add (h1 x hx) (h1 x₀ hx₀)
      _ = 2 * t := by ring
  -- `|β| ≤ 4t/σ`
  have hβle : |β| ≤ 4 * t / σ := by
    have hun' : (⟪n', d⟫ : ℝ) = α * ⟪n, n'⟫ + β * ‖v‖ := by
      have hsplit : n' = (⟪n, n'⟫ : ℝ) • n + ‖v‖ • m := by
        rw [hm, smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul, hv]
        abel
      rw [hα, hβ]
      nth_rewrite 1 [hsplit]
      simp only [inner_add_left, real_inner_smul_left]
      ring
    have hn'd : |(⟪n', d⟫ : ℝ)| ≤ 2 * t := by
      have e : (⟪n', d⟫ : ℝ) = ⟪n', x - q⟫ - ⟪n', x₀ - q⟫ := by
        rw [← inner_sub_right]; congr 1; rw [hd]; abel
      rw [e]
      calc |(⟪n', x - q⟫ : ℝ) - ⟪n', x₀ - q⟫|
          ≤ |(⟪n', x - q⟫ : ℝ)| + |(⟪n', x₀ - q⟫ : ℝ)| := abs_sub _ _
        _ ≤ t + t := add_le_add (h2 x hx) (h2 x₀ hx₀)
        _ = 2 * t := by ring
    have hcs : |(⟪n, n'⟫ : ℝ)| ≤ 1 := by
      have := abs_real_inner_le_norm n n'
      rwa [hn, hn', mul_one] at this
    have hbv : |β| * ‖v‖ ≤ 4 * t := by
      have hbe : β * ‖v‖ = ⟪n', d⟫ - α * ⟪n, n'⟫ := by rw [hun']; ring
      calc |β| * ‖v‖ = |β * ‖v‖| := by rw [abs_mul, abs_of_pos hvpos]
        _ = |(⟪n', d⟫ : ℝ) - α * ⟪n, n'⟫| := by rw [hbe]
        _ ≤ |(⟪n', d⟫ : ℝ)| + |α * (⟪n, n'⟫ : ℝ)| := abs_sub _ _
        _ ≤ 2 * t + 2 * t * 1 := by
            refine add_le_add hn'd ?_
            rw [abs_mul]
            exact mul_le_mul hαle hcs (abs_nonneg _) (by linarith)
        _ = 4 * t := by ring
    rw [le_div_iff₀ hσ]
    nlinarith [abs_nonneg β]
  -- the nearby point of `A`
  have hmemA : x - α • n - β • m ∈ A := by
    rw [hA, AffineSubspace.mem_mk']
    have hvs : (x - α • n - β • m) -ᵥ x₀ = d - α • n - β • m := by
      simp only [vsub_eq_sub, hd]
      abel
    rw [hvs, Submodule.mem_orthogonal]
    have hmm : (⟪m, m⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hmnorm]; norm_num
    have hmn : (⟪m, n⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hnm
    have hgen : ∀ z ∈ ({n, m} : Set E₃), (⟪z, d - α • n - β • m⟫ : ℝ) = 0 := by
      intro z hz
      rcases hz with hz | hz
      · rw [hz, inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
          hnn, hnm, ← hα]
        ring
      · rw [Set.mem_singleton_iff] at hz
        rw [hz, inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
          hmm, hmn, ← hβ]
        ring
    have hspan : ((ℝ ∙ n) ⊔ (ℝ ∙ m) : Submodule ℝ E₃) = Submodule.span ℝ ({n, m} : Set E₃) := by
      rw [Submodule.span_insert]
    intro y hy
    rw [hspan] at hy
    refine Submodule.span_induction (p := fun z _ => (⟪z, d - α • n - β • m⟫ : ℝ) = 0)
      (fun z hz => hgen z hz) (by simp) (fun z₁ z₂ _ _ h₁ h₂ => by
        rw [inner_add_left, h₁, h₂]; ring)
      (fun a z _ h => by rw [real_inner_smul_left, h]; ring) hy
  refine Metric.mem_cthickening_of_dist_le _ _ _ _ hmemA ?_
  have hdist : dist x (x - α • n - β • m) = ‖α • n + β • m‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  rw [hdist]
  have hσ1 : σ ≤ 1 := le_trans hσle hv1
  calc ‖α • n + β • m‖ ≤ ‖α • n‖ + ‖β • m‖ := norm_add_le _ _
    _ = |α| + |β| := by
        rw [norm_smul, norm_smul, hn, hmnorm, mul_one, mul_one, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ 2 * t + 4 * t / σ := add_le_add hαle hβle
    _ ≤ 6 * t / σ := by
        rw [le_div_iff₀ hσ]
        have h4 : 4 * t / σ * σ = 4 * t := by field_simp
        nlinarith [h4]

/-- **Clause (S1), produced: two normalising ellipsoids with angularly separated normals are
essentially distinct.**

`IsEssentiallyDistinct U V` is `volume (U ∩ V) ≤ (1/2) max (volume U) (volume V)`. The
intersection lies in both slabs, so
`Kakeya.VeryNotSticky.thickness_one_le_of_two_slabs` pinches its rank-`1` thickness to
`6 (ratio R)/σ` while its rank-`0` and rank-`2` thicknesses are those of a single slab, `R` and
`ratio R`; `volume_le_prod_thickness` then bounds its volume by `48 ratio² R³/σ`, against the
slab's own floor `ratio R³/6` from `Convex.prod_thickness_le_volumeReal`. At
`σ ≥ 576 · ratio` — an angular separation of a `δ`-free multiple of the aspect ratio, which is
exactly the resolution clause (S4′) and clause R1 work at — the comparison closes.

**This is the last analytic input clause (S1) of `Kakeya.VeryNotSticky.IsSlabFamily` needs**, and
together with `Kakeya.VeryNotSticky.lineAngle_bodyNormal_generalSlab_le` (which makes (S4′) and
R1 hold by construction for a family of normalising ellipsoids) it reduces `hfam` to a finite
greedy selection. -/
theorem isEssentiallyDistinct_generalSlab_of_separated (c c' n n' : E₃) (hn : ‖n‖ = 1)
    (hn' : ‖n'‖ = 1) {R ratio σ : ℝ} (hR : 0 < R) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1)
    (hσ : 0 < σ) (hσle : σ ≤ ‖n' - (⟪n, n'⟫ : ℝ) • n‖) (hsep : 576 * ratio ≤ σ) :
    IsEssentiallyDistinct (generalSlab c n hn hR hratio).carrier
      (generalSlab c' n' hn' hR hratio).carrier := by
  set S := generalSlab c n hn hR hratio with hS
  set S' := generalSlab c' n' hn' hR hratio with hS'
  set Y : Set E₃ := S.carrier ∩ S'.carrier with hY
  have hSbdd : Bornology.IsBounded S.carrier := S.isCompact'.isBounded
  have hYsub : Y ⊆ S.carrier := Set.inter_subset_left
  have hYbdd : Bornology.IsBounded Y := hSbdd.subset hYsub
  have hprof := hasThicknesses_generalSlab c n hn hR hratio hratio1 (le_refl (1 : NNReal))
  have hS0 : Metric.thickness ℝ S.carrier 0 ≤ R := by simpa using (hprof 0).2
  have hS2 : Metric.thickness ℝ S.carrier 2 ≤ ratio * R := by simpa using (hprof 2).2
  have hmono := Metric.thickness_monotone (𝕜 := ℝ) hSbdd hYsub
  have hY0 : Metric.thickness ℝ Y 0 ≤ R := le_trans (hmono 0) hS0
  have hY2 : Metric.thickness ℝ Y 2 ≤ ratio * R := le_trans (hmono 2) hS2
  have htR : (0:ℝ) ≤ ratio * R := by positivity
  -- the pinch
  have hY1 : Metric.thickness ℝ Y 1 ≤ 6 * (ratio * R) / σ := by
    rcases Set.eq_empty_or_nonempty Y with hemp | ⟨x₀, hx₀⟩
    · rw [hemp]
      have hrk : Module.rank ℝ (AffineSubspace.mk' (0 : E₃) (ℝ ∙ (0 : E₃))).direction
          ≤ (1 : ℕ) := by
        rw [AffineSubspace.direction_mk']
        simpa using rank_span_le ({(0 : E₃)} : Set E₃)
      exact Metric.thickness_le_of_cthickening (by positivity) hrk (by simp)
    · refine thickness_one_le_of_two_slabs n n' hn hn' (p := c) (q := c') htR hσ hx₀ ?_ ?_ hσle
      · exact fun x hx => abs_inner_le_of_mem_generalSlab c n hn hR hratio hx.1
      · exact fun x hx => abs_inner_le_of_mem_generalSlab c' n' hn' hR hratio hx.2
  -- the volume comparison
  have hvolY : volume Y ≤ ENNReal.ofReal (8 * (R * (6 * (ratio * R) / σ) * (ratio * R))) :=
    volume_le_of_thickness_bounds hYbdd hY0 hY1 hY2
  have hvolS : ENNReal.ofReal ((R * R * (ratio * R)) / (6 * (1:ℝ) ^ 3)) ≤ volume S.carrier := by
    have h := volumeReal_ge_of_threeProfile S.convex hSbdd (le_refl (1:NNReal)) hR.le hR.le htR
      (by simpa using hprof)
    rw [MeasureTheory.Measure.real] at h
    exact (ENNReal.ofReal_le_iff_le_toReal S.isCompact'.measure_ne_top).mpr h
  refine le_trans hvolY ?_
  have hhalf : ((1:ENNReal)/2) = ENNReal.ofReal (1/2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal (8 * (R * (6 * (ratio * R) / σ) * (ratio * R)))
      ≤ ENNReal.ofReal ((1/2 : ℝ) * ((R * R * (ratio * R)) / (6 * (1:ℝ) ^ 3))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hnum : 8 * (R * (6 * (ratio * R) / σ) * (ratio * R))
            = 48 * ratio ^ 2 * R ^ 3 / σ := by field_simp; ring
        have hden : (1/2 : ℝ) * ((R * R * (ratio * R)) / (6 * (1:ℝ) ^ 3))
            = ratio * R ^ 3 / 12 := by field_simp; ring
        rw [hnum, hden, div_le_div_iff₀ hσ (by norm_num : (0:ℝ) < 12)]
        nlinarith [pow_pos hR 3, mul_pos hratio (pow_pos hR 3), hratio.le, hsep]
    _ = ((1:ENNReal)/2) * ENNReal.ofReal ((R * R * (ratio * R)) / (6 * (1:ℝ) ^ 3)) := by
        rw [ENNReal.ofReal_mul (by norm_num), hhalf]
    _ ≤ ((1:ENNReal)/2) * volume S.carrier := by gcongr
    _ ≤ ((1:ENNReal)/2) * max (volume S.carrier) (volume S'.carrier) := by
        gcongr
        exact le_max_left _ _

/-! ### The second obstruction to `hfam`: (S1) and (S3) trade off against each other -/

/-- **The separation/containment trade-off, compiled.**

A slab of half-thickness `h` about its central plane can contain a body carrying a chord of
length `L` tilted by at most `2h/L` out of that plane — that is
`Kakeya.VeryNotSticky.abs_inner_mul_le_of_subset_slab`, read as a *budget* rather than as a
consequence. Two slabs of lateral extent `R` and half-thickness `h` are essentially distinct
only once their normals are separated by `σ ≥ 576 · (h/R)` — that is
`Kakeya.VeryNotSticky.isEssentiallyDistinct_generalSlab_of_separated` at aspect ratio `h/R`.

A family that must **cover** every body (clause (S3), literal containment) *and* be **pairwise
essentially distinct** (clause (S1)) needs the covering radius to reach the separation:
`2h/L ≥ σ ≥ 576 h/R`. The half-thickness `h` cancels, and what is left is a condition on the
slab's *lateral* extent against the bodies' *length*:

  `R ≥ 288 · L`.

**The two clauses do not compete over the slab's thickness — they compete over its width.** -/
theorem slabFamily_cover_separate_forces_radius {h R L σ : ℝ} (hh : 0 < h) (hR : 0 < R)
    (hL : 0 < L) (hcov : σ ≤ 2 * h / L) (hsep : 576 * (h / R) ≤ σ) : 288 * L ≤ R := by
  have h1 : 576 * (h / R) ≤ 2 * h / L := le_trans hsep hcov
  have h2 : 576 * h * L ≤ 2 * h * R := by
    have e1 : 576 * (h / R) = (576 * h) / R := by ring
    have e2 : 2 * h / L = (2 * h) / L := by ring
    rw [e1, e2, div_le_div_iff₀ hR hL] at h1
    linarith
  nlinarith [mul_pos hh hR, mul_pos hh hL]

/-- A radius `2r₁` cannot accommodate a bound `288 C₀ r₁`.
The thickness estimate for a body allows `τ₀ ≤ C₀ r₁`. Combining
a chord of this order with the lower bound `R ≥ 288L` requires a
lateral radius proportional to `C₀ r₁`. The inequality
`288 C₀ r₁ ≤ 2r₁` fails whenever `r₁ > 0` and `C₀ ≥ 1`.
A normalization using this estimate therefore needs a radius constant
depending on `C₀`. -/
theorem slabFamily_radius_two_r₁_insufficient {r₁ C₀ : ℝ} (hr₁ : 0 < r₁) (hC₀ : 1 ≤ C₀) :
    ¬ (288 * (C₀ * r₁) ≤ 2 * r₁) := by
  intro h
  nlinarith

/-! ### The trade-off is proportional to the essential-distinctness threshold -/

/-- **The trade-off of `Kakeya.VeryNotSticky.slabFamily_cover_separate_forces_radius`, with the
essential-distinctness threshold carried as a parameter.**

`Kakeya.IsEssentiallyDistinct U V` is `volume (U ∩ V) ≤ (1/2) · max (volume U) (volume V)` — a
*pairwise* overlap condition at the **fixed** ratio `1/2`. Running the same volume comparison at
a threshold weaker by a factor `θ` weakens the separation the family needs by `θ`, and therefore
weakens the width requirement by `θ`:

`σ ≤ 2h/L` (covering) together with `1152 (h/R)/θ ≤ σ` (separating at threshold `θ`) gives
`R ≥ 576 L/θ`.

At `θ = 1` this is `Kakeya.VeryNotSticky.slabFamily_cover_separate_forces_radius`'s
`R ≥ 288 L` (the `1152 = 4 · 288` is the same constant re-parametrised). **The whole obstruction
is proportional to `θ⁻¹`.** -/
theorem slabFamily_tradeoff_at_threshold {h R L σ θ : ℝ} (hh : 0 < h) (hR : 0 < R) (hL : 0 < L)
    (hθ : 0 < θ) (hcov : σ ≤ 2 * h / L) (hsep : 1152 * (h / R) / θ ≤ σ) :
    576 * L / θ ≤ R := by
  have h1 : 1152 * (h / R) / θ ≤ 2 * h / L := le_trans hsep hcov
  have e1 : 1152 * (h / R) / θ = (1152 * h) / (R * θ) := by field_simp
  have e2 : 2 * h / L = (2 * h) / L := by ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) hL] at h1
  rw [div_le_iff₀ hθ]
  nlinarith [mul_pos hh hR, mul_pos hh hL, mul_pos hR hθ]

/-- **…and at the source's own threshold it vanishes.**

The refined proof's families are `A`-essentially distinct in the sense
`#{T : T ⊆ N_{5δ}(L)} ≤ A` for every line `L` — a family-wide *line-parameter count*, not a
pairwise volume ratio — at `A₀ = 2 · 223⁶`, and its slab families are only asked to decompose
into a **boundedly overlapping** union over *incomparable* slabs. At that threshold
`Kakeya.VeryNotSticky.slabFamily_tradeoff_at_threshold`'s conclusion `R ≥ 576 L / A₀` is implied
by the bare containment `L ≤ R`, i.e. **it says nothing**: the width requirement that blocks
`hfam` is an artefact of the fixed `1/2` in `Kakeya.IsEssentiallyDistinct`, not of the
mathematics.

**Source, and the radius difference** .  The line-parameter count is
refined l.4780–4783; the boundedly-overlapping decomposition over incomparable slabs is
l.5814–5817.  `A₀ = 2 · 223⁶` is kept as the source's own constant and is *not* interchangeable
with the tree's `Tube.tubeOverlapCoreClose.C 3`-radius readings: the refined count is taken in the
`5δ` neighbourhood of the line, the tree's line-ED notion at the two-tube radius, and the two
differ by that radius, not by a constant. -/
theorem slabFamily_tradeoff_vacuous_at_A₀ {L R : ℝ} (hL : 0 < L) (hLR : L ≤ R) :
    576 * L / (2 * 223 ^ 6) ≤ R := by
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2 * 223 ^ 6)]
  nlinarith

end

end Kakeya.VeryNotSticky
