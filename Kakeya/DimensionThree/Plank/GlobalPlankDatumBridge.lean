/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Factorization
public import Kakeya.DimensionThree.Plank.PrismGeometry
public import Kakeya.Factoring.FlatPrisms

/-!
# Reading the GWZ 6.6(B) datum in the tree's plank vocabulary

`Kakeya.GlobalPlankFactorization` (`Kakeya/DimensionThree/Plank/Factorization.lean`) is the datum
of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ Proposition 6.6(B)).  It says of each
cell hull `W`:

* `le_plank` — `W` fits inside an exact `a × b × 1` plank;
* `wide` — `W` contains a flat disc of radius `min b (1/2) / Cw`.

The rest of the development speaks a *different* dialect: `Kakeya.IsPlankOfDimensions Cw a b W`
(`Kakeya/Factoring/FlatPrisms.lean`), the two-sided bracketing of the three affine thicknesses of
`W`.  Essentially all of the reusable plank machinery — volume bounds
(`Kakeya.IsPlankOfDimensions.volume_lower`, `.volume_upper`), the exact-plank envelope
(`Kakeya.comparablePlankEnvelope`), and above all the Frostman transfers
(`Kakeya.IsPlankOfDimensions.frostmanIn_bodyPlank`, `.frostmanIn_closedUnitBall`) — is stated in
that dialect.

This file translates.  The one-sided readings are proved separately, then assembled.

## What the translation costs

`le_plank` + `wide` do **not** pin the *thin* thickness `eth₂` from below: they give only
`ρ ≤ eth₂(W) ≤ a`, whereas `IsPlankOfDimensions C a b` wants `C⁻¹ a ≤ eth₂(W) ≤ C a`.  This is not
a defect of the datum but a genuine (and harmless) weakening: a cell whose hull is *thinner* than
`a` only makes the conclusion `(a/b) ^ β` of 6.6(B) weaker than the truth.

`ConvexSpaceBody.Factorization.simDims` is what repairs it: the thin thicknesses of the cells are
comparable to one another up to `C₀`, so a *single* `a' ≤ a` works for the whole family, namely the
minimum of `eth₂` over the cells.  That is
`Kakeya.GlobalPlankFactorization.exists_isPlankFamilyOfDimensions`, and `a' ≤ a` is exactly what
lets a proof run at `a'` and be weakened to `a` at the end, since `(a'/b) ^ β ≤ (a/b) ^ β`.

## New `Prism3D` geometry

`Kakeya.Prism3D.ethickness_two_le` (`≤ a`) was already available.  The two companions
`Kakeya.Prism3D.ethickness_one_le` (`≤ a + b`) and `Kakeya.Prism3D.ethickness_zero_le`
(`≤ a + b + c`) are proved here; both are the elementary "project onto the long axis / onto the
centre" bounds, and neither existed.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody

open scoped NNReal Real ENNReal

noncomputable section

/-! ### Upper bounds for the affine thicknesses of a `Prism3D` -/

namespace Prism3D

variable {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}

/-- The long axis of a `Prism3D`, as an affine line through its centre. -/
abbrev longAxisLine (P : Prism3D a b c hab hbc) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' P.center P.longAxis

/-- The expansion of a point of a `Prism3D` in the prism's own orthonormal frame. -/
theorem sub_center_eq (P : Prism3D a b c hab hbc) (x : EuclideanSpace ℝ (Fin 3)) :
    x - P.center =
      (inner ℝ (P.basis 0) (x - P.center)) • P.basis 0 +
        (inner ℝ (P.basis 1) (x - P.center)) • P.basis 1 +
        (inner ℝ (P.basis 2) (x - P.center)) • P.basis 2 := by
  have h := (P.basis.sum_repr (x - P.center)).symm
  rw [Fin.sum_univ_three] at h
  simpa only [P.basis.repr_apply_apply] using h

/-- The three frame coordinates of a point of the carrier are bounded by the half-widths. -/
theorem abs_inner_le (P : Prism3D a b c hab hbc) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    |inner ℝ (P.basis 0) (x - P.center)| ≤ (a : ℝ) ∧
      |inner ℝ (P.basis 1) (x - P.center)| ≤ (b : ℝ) ∧
      |inner ℝ (P.basis 2) (x - P.center)| ≤ (c : ℝ) := by
  rw [P.mem_carrier_iff] at hx
  refine ⟨?_, ?_, ?_⟩
  · have := hx 0
    rw [P.basis.repr_apply_apply] at this
    simpa [P.thicknesses_eq, vsub_eq_sub] using this
  · have := hx 1
    rw [P.basis.repr_apply_apply] at this
    simpa [P.thicknesses_eq, vsub_eq_sub] using this
  · have := hx 2
    rw [P.basis.repr_apply_apply] at this
    simpa [P.thicknesses_eq, vsub_eq_sub] using this

/-- A `Prism3D` lies within `a + b` of its long axis. -/
theorem carrier_subset_cthickening_longAxisLine (P : Prism3D a b c hab hbc) :
    P.carrier ⊆ Metric.cthickening ((a : ℝ) + (b : ℝ)) P.longAxisLine := by
  intro x hx
  haveI : Nonempty P.longAxisLine := ⟨P.center, AffineSubspace.self_mem_mk' _ _⟩
  obtain ⟨ha, hb, -⟩ := P.abs_inner_le hx
  set α : ℝ := inner ℝ (P.basis 0) (x - P.center) with hα
  set β : ℝ := inner ℝ (P.basis 1) (x - P.center) with hβ
  set γ : ℝ := inner ℝ (P.basis 2) (x - P.center) with hγ
  have hexp : x - P.center = α • P.basis 0 + β • P.basis 1 + γ • P.basis 2 := P.sub_center_eq x
  have hz_mem : P.center + γ • P.basis 2 ∈ P.longAxisLine := by
    rw [AffineSubspace.mem_mk',
      show P.center + γ • P.basis 2 -ᵥ P.center = γ • P.basis 2 from by simp [vsub_eq_sub]]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine Metric.mem_cthickening_of_dist_le x (P.center + γ • P.basis 2) _ _ hz_mem ?_
  have hdiff : x - (P.center + γ • P.basis 2) = α • P.basis 0 + β • P.basis 1 := by
    rw [show x - (P.center + γ • P.basis 2) = (x - P.center) - γ • P.basis 2 from by abel, hexp]
    abel
  rw [dist_eq_norm, hdiff]
  calc ‖α • P.basis 0 + β • P.basis 1‖
      ≤ ‖α • P.basis 0‖ + ‖β • P.basis 1‖ := norm_add_le _ _
    _ = |α| + |β| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          P.basis.norm_eq_one, P.basis.norm_eq_one, mul_one, mul_one]
    _ ≤ (a : ℝ) + (b : ℝ) := by linarith

/-- The rank-`1` `ethickness` of a `Prism3D` is at most `a + b`, so for a `Plank a b` it is at
most `2 b`.  The companion of `Kakeya.Prism3D.ethickness_two_le`. -/
theorem ethickness_one_le (P : Prism3D a b c hab hbc) :
    Metric.ethickness ℝ P.carrier 1 ≤ ((a : ENNReal) + (b : ENNReal)) := by
  have hrank : Module.rank ℝ P.longAxisLine.direction ≤ (1 : ℕ) := by
    rw [AffineSubspace.direction_mk', ← Module.finrank_eq_rank, P.finrank_longAxis]
  have hle := Metric.ethickness_le_of_cthickening (𝕜 := ℝ) (s := (P.carrier : Set _))
    (n := 1) (a + b) hrank (by
      have := P.carrier_subset_cthickening_longAxisLine
      rwa [show ((a + b : ℝ≥0) : ℝ) = (a : ℝ) + (b : ℝ) from by push_cast; ring])
  rwa [ENNReal.coe_add] at hle

/-- A `Prism3D` lies in the ball of radius `a + b + c` about its centre. -/
theorem carrier_subset_closedBall_center (P : Prism3D a b c hab hbc) :
    (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall P.center ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  intro x hx
  obtain ⟨ha, hb, hc⟩ := P.abs_inner_le hx
  set α : ℝ := inner ℝ (P.basis 0) (x - P.center) with hα
  set β : ℝ := inner ℝ (P.basis 1) (x - P.center) with hβ
  set γ : ℝ := inner ℝ (P.basis 2) (x - P.center) with hγ
  have hexp : x - P.center = α • P.basis 0 + β • P.basis 1 + γ • P.basis 2 := P.sub_center_eq x
  rw [Metric.mem_closedBall, dist_eq_norm, hexp]
  calc ‖α • P.basis 0 + β • P.basis 1 + γ • P.basis 2‖
      ≤ ‖α • P.basis 0 + β • P.basis 1‖ + ‖γ • P.basis 2‖ := norm_add_le _ _
    _ ≤ (‖α • P.basis 0‖ + ‖β • P.basis 1‖) + ‖γ • P.basis 2‖ := by
        gcongr
        exact norm_add_le _ _
    _ = |α| + |β| + |γ| := by
        rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, P.basis.norm_eq_one, P.basis.norm_eq_one, P.basis.norm_eq_one,
          mul_one, mul_one, mul_one]
    _ ≤ (a : ℝ) + (b : ℝ) + (c : ℝ) := by linarith

/-- The rank-`0` `ethickness` of a `Prism3D` is at most `a + b + c`, so for a `Plank a b` it is at
most `3`. -/
theorem ethickness_zero_le (P : Prism3D a b c hab hbc) :
    Metric.ethickness ℝ P.carrier 0 ≤ ((a : ENNReal) + (b : ENNReal) + (c : ENNReal)) := by
  have hle := Metric.ethickness_le_of_subset_closedBall (𝕜 := ℝ) (s := (P.carrier : Set _))
    (x := P.center) (a + b + c) (by
      have := P.carrier_subset_closedBall_center
      rwa [show ((a + b + c : ℝ≥0) : ℝ) = (a : ℝ) + (b : ℝ) + (c : ℝ) from by push_cast; ring]) 0
  rwa [ENNReal.coe_add, ENNReal.coe_add] at hle

end Prism3D

/-! ### Reading `Kakeya.GlobalPlankFactorization` as a family of `a × b × 1` planks -/

namespace Kakeya

namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

/-- The outer body of a cell of the factorisation: the convex hull of the coarse tubes it
collects.  `ConvexSpaceBody.Factorization` fixes this choice, it is not free data. -/
abbrev cellBody (part : Finset κ) (Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) :
    ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
  part.convexHull_biUnion (fun k => (Rt k).toConvexSpaceBody)

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

/-- Every cell of the factorisation contains a coarse `ρ`-tube: the parts of a `Finpartition`
are nonempty. -/
theorem exists_tube_le {part : Finset κ} (hpart : part ∈ Fz.parts) :
    ∃ k ∈ part, (Rt k).toConvexSpaceBody ≤ cellBody part Rt := by
  obtain ⟨k, hk⟩ := Fz.nonempty_of_mem_parts hpart
  exact ⟨k, hk, Finset.le_convexHull_biUnion (fun k => (Rt k).toConvexSpaceBody) hk⟩

/-- The cell body of a cell lies in the cell's representative `a × b × 1` plank, as a subset. -/
theorem carrier_subset_plank {part : Finset κ} (hpart : part ∈ Fz.parts) :
    ∃ P : Plank a b hab hb1,
      ((cellBody part Rt).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨P, hP⟩ := Fz.le_plank part hpart
  exact ⟨P, (SetLike.coe_subset_coe (S := cellBody part Rt)
    (T := P.toConvexSpaceBody)).mp hP⟩

/-! #### The four one-sided readings -/

/-- **Longitudinal lower bound.**  Every cell body has rank-`0` affine thickness at least `1/2`:
it contains a coarse `ρ`-tube, whose core is a unit segment (`Tube.le_ethickness_zero`).
No hypothesis of the datum beyond the `Finpartition` is used. -/
theorem le_ethickness_zero {part : Finset κ} (hpart : part ∈ Fz.parts) :
    (1 / 2 : ENNReal) ≤ Metric.ethickness ℝ (cellBody part Rt).carrier 0 := by
  obtain ⟨k, -, hle⟩ := Fz.exists_tube_le hpart
  refine le_trans (Rt k).le_ethickness_zero (Metric.ethickness_monotone ?_ 0)
  exact (SetLike.coe_subset_coe (S := (Rt k).toConvexSpaceBody)
    (T := cellBody part Rt)).mp hle

/-- **Transverse lower bound at the coarse scale.**  Every cell body has rank-`2` affine
thickness at least `ρ`, because it contains a `ρ`-tube. -/
theorem le_ethickness_two {part : Finset κ} (hpart : part ∈ Fz.parts) :
    (ρ : ENNReal) ≤ Metric.ethickness ℝ (cellBody part Rt).carrier 2 := by
  obtain ⟨k, -, hle⟩ := Fz.exists_tube_le hpart
  have hk : (ρ : ENNReal) ≤ Metric.ethickness ℝ (Rt k).carrier 2 := by
    have h := (Rt k).le_ethickness_finrank_sub_one
    rwa [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 = 2 by simp] at h
  refine hk.trans (Metric.ethickness_monotone ?_ 2)
  exact (SetLike.coe_subset_coe (S := (Rt k).toConvexSpaceBody)
    (T := cellBody part Rt)).mp hle

/-- **Thin upper bound, from `le_plank`.**  Every cell body has rank-`2` affine thickness at most
`a`: it sits in an `a × b × 1` plank, whose least width is `a`
(`Kakeya.Prism3D.ethickness_two_le`). -/
theorem ethickness_two_le {part : Finset κ} (hpart : part ∈ Fz.parts) :
    Metric.ethickness ℝ (cellBody part Rt).carrier 2 ≤ (a : ENNReal) := by
  obtain ⟨P, hP⟩ := Fz.carrier_subset_plank hpart
  exact (Metric.ethickness_monotone hP 2).trans (Kakeya.Prism3D.ethickness_two_le P)

/-- **Middle upper bound, from `le_plank`.**  Every cell body has rank-`1` affine thickness at
most `a + b`, hence at most `2 b`. -/
theorem ethickness_one_le {part : Finset κ} (hpart : part ∈ Fz.parts) :
    Metric.ethickness ℝ (cellBody part Rt).carrier 1 ≤ ((a : ENNReal) + (b : ENNReal)) := by
  obtain ⟨P, hP⟩ := Fz.carrier_subset_plank hpart
  exact (Metric.ethickness_monotone hP 1).trans P.ethickness_one_le

/-- **Longitudinal upper bound, from `le_plank`.**  Every cell body has rank-`0` affine thickness
at most `a + b + 1`, hence at most `3`. -/
theorem ethickness_zero_le {part : Finset κ} (hpart : part ∈ Fz.parts) :
    Metric.ethickness ℝ (cellBody part Rt).carrier 0
      ≤ ((a : ENNReal) + (b : ENNReal) + 1) := by
  obtain ⟨P, hP⟩ := Fz.carrier_subset_plank hpart
  have h := (Metric.ethickness_monotone hP 0).trans P.ethickness_zero_le
  simpa using h

/-- **Middle lower bound, from `wide`.**  Every cell body has rank-`1` affine thickness at least
`min b (1/2) / Cw`, by `Kakeya.ContainsFlatDisc.le_ethickness_one`.  This is the *only* place the
`wide` field is used, and the only clause of the datum that keeps the eccentricity gain
`(a / b) ^ β` of GWZ 6.6(B) honest. -/
theorem le_ethickness_one {part : Finset κ} (hpart : part ∈ Fz.parts) :
    ((min b (1 / 2 : ℝ≥0) / Cw : ℝ≥0) : ENNReal)
      ≤ Metric.ethickness ℝ (cellBody part Rt).carrier 1 :=
  ContainsFlatDisc.le_ethickness_one (Fz.wide part hpart)

include Fz in
/-- **The scale relation `ρ ≤ a` of GWZ 6.6(B) is forced by the datum**, not assumed: a cell body
contains a `ρ`-tube and sits in an `a × b × 1` plank, and `Kakeya.Tube.rho_le_of_le_prism3D`
closes.  Only the nonemptiness of the coarse family is needed. -/
theorem rho_le (hr : r.Nonempty) : ρ ≤ a := by
  obtain ⟨part, hpart⟩ := Fz.parts_nonempty (Finset.nonempty_iff_ne_empty.mp hr)
  obtain ⟨k, -, hle⟩ := Fz.exists_tube_le hpart
  obtain ⟨P, hP⟩ := Fz.le_plank part hpart
  exact Tube.rho_le_of_le_prism3D (Rt k) P (hle.trans hP)

/-! #### Assembly: the datum is a family of `a' × b × 1` planks for a single `a' ≤ a` -/

end GlobalPlankFactorization

/-- The comparability constant of the plank reading of a `Kakeya.GlobalPlankFactorization`:
`3` pays for the longitudinal bracket `[1/2, 3]` and the middle upper bracket `a + b ≤ 2 b`,
`2 * Cw` pays for the middle lower bracket coming from `wide`, and `C₀` pays for the thin bracket
coming from `ConvexSpaceBody.Factorization.simDims`. -/
def plankReadingConst (Cw C₀ : ℝ≥0) : ℝ≥0 := max 3 (max (2 * Cw) C₀)

theorem three_le_plankReadingConst (Cw C₀ : ℝ≥0) : 3 ≤ plankReadingConst Cw C₀ :=
  le_max_left _ _

theorem two_mul_le_plankReadingConst (Cw C₀ : ℝ≥0) : 2 * Cw ≤ plankReadingConst Cw C₀ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem c0_le_plankReadingConst (Cw C₀ : ℝ≥0) : C₀ ≤ plankReadingConst Cw C₀ :=
  le_trans (le_max_right _ _) (le_max_right _ _)

theorem one_le_plankReadingConst (Cw C₀ : ℝ≥0) : 1 ≤ plankReadingConst Cw C₀ :=
  le_trans (by norm_num) (three_le_plankReadingConst Cw C₀)

theorem two_le_plankReadingConst (Cw C₀ : ℝ≥0) : 2 ≤ plankReadingConst Cw C₀ :=
  le_trans (by norm_num) (three_le_plankReadingConst Cw C₀)

private theorem inv_mul_le_of_le_mul {C : ℝ≥0} (hC0 : C ≠ 0) {z w : ENNReal}
    (h : z ≤ (C : ENNReal) * w) : (C : ENNReal)⁻¹ * z ≤ w := by
  have hc0 : (C : ENNReal) ≠ 0 := by simpa using hC0
  have hct : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc (C : ENNReal)⁻¹ * z ≤ (C : ENNReal)⁻¹ * ((C : ENNReal) * w) := by gcongr
    _ = w := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-- `b / 2 ≤ min b (1/2)` for `b ≤ 1`: the `min` in the `wide` field of
`Kakeya.GlobalPlankFactorization` costs at most a factor `2`. -/
theorem half_le_min_half {b : ℝ≥0} (hb1 : b ≤ 1) : b / 2 ≤ min b (1 / 2 : ℝ≥0) := by
  rw [← NNReal.coe_le_coe]
  push_cast
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := b.coe_nonneg
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  rcases le_total (b : ℝ) (1 / 2 : ℝ) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- The division-free form of the `wide` lower bound: `b ≤ 2 * Cw * (min b (1/2) / Cw)`. -/
theorem le_two_mul_mul_min_div {Cw b : ℝ≥0} (hCw : 1 ≤ Cw) (hb1 : b ≤ 1) :
    b ≤ 2 * Cw * (min b (1 / 2 : ℝ≥0) / Cw) := by
  have hCw0 : (0 : ℝ≥0) < Cw := lt_of_lt_of_le zero_lt_one hCw
  have hm : b / 2 ≤ min b (1 / 2 : ℝ≥0) := half_le_min_half hb1
  rw [← NNReal.coe_le_coe]
  push_cast
  have hCw0' : (0 : ℝ) < (Cw : ℝ) := by exact_mod_cast hCw0
  have hm' : (b : ℝ) / 2 ≤ min (b : ℝ) (1 / 2 : ℝ) := by
    have := hm
    rw [← NNReal.coe_le_coe] at this
    push_cast at this
    exact this
  have hCwne : (Cw : ℝ) ≠ 0 := ne_of_gt hCw0'
  field_simp
  nlinarith [hm', hCw0']

namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

include Fz in
/-- **Clause (ii) of the blueprint's `def:Factors`, in Frostman form — read against the cell body,
which is where `ConvexSpaceBody.Factorization` puts it.**

The blueprint (`section4.tex`, immediately after `def:Factors`) observes that
`Δ_max(𝕍) ≤ C · Δ(𝕍_t, W_t)` says exactly that `𝕍_t` is `C`-Frostman in `W_t`.  In GWZ 6.6(B)
the outer body `W_t` is *the `a × b × 1` plank*; `ConvexSpaceBody.Factorization` hard-wires it to
be the convex hull of the block instead, and this is that reading. -/
theorem isFrostmanIn_cellBody {part : Finset κ} (hpart : part ∈ Fz.parts) :
    IsFrostmanIn part (fun k => (Rt k).toConvexSpaceBody) (cellBody part Rt) (C₀ : ENNReal) := by
  refine ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le
    (le_trans ?_ (Fz.maxDensity_le_mul part hpart))
  exact maxDensity_mono _ (Fz.le hpart)

include Fz in
/-- **Frostman in the cell's representative plank, with the honest constant.**

`ConvexSpaceBody.IsFrostmanIn.change_ambient` moves the Frostman datum from the cell body to any
larger body, at the cost of the volume ratio.  So the datum *does* give the plank-Frostman clause
that `Kakeya.Section6PartBFactorisation.coarse_fibre_frostman` asks for — but with the constant
`C₀ · vol(P) / vol(W)`, and **that ratio is not bounded by the datum**.

Indeed `vol(P) = 8 a b` while, by `Kakeya.IsPlankOfDimensions.volume_lower` applied to the plank
reading `Kakeya.GlobalPlankFactorization.exists_isPlankFamilyOfDimensions`, `vol(W)` is only
bounded below by a multiple of `a' b` with `a' ≤ a`; the ratio therefore carries a factor `a / a'`,
which the datum leaves free (`a'` may be as small as `ρ`).

This is the precise, compiler-checked form of the fidelity gap between
`Kakeya.GlobalPlankFactorization` (clause (ii) against the hull) and the blueprint's `def:Factors`
(clause (ii) against the plank).  The way out is not to bound `a / a'` but to run the argument at
`a'` and weaken at the end, since `(a'/b) ^ β ≤ (a/b) ^ β`. -/
theorem exists_isFrostmanIn_plank {part : Finset κ} (hpart : part ∈ Fz.parts)
    (h0 : volume (cellBody part Rt).carrier ≠ 0) :
    ∃ P : Plank a b hab hb1,
      cellBody part Rt ≤ P.toConvexSpaceBody ∧
        IsFrostmanIn part (fun k => (Rt k).toConvexSpaceBody) P.toConvexSpaceBody
          ((C₀ : ENNReal) * (volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
            / volume (cellBody part Rt).carrier)) := by
  obtain ⟨P, hP⟩ := Fz.le_plank part hpart
  have hsub : ((cellBody part Rt).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    (SetLike.coe_subset_coe (S := cellBody part Rt) (T := P.toConvexSpaceBody)).mp hP
  have hP0 : volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 := by
    intro hzero
    exact h0 (measure_mono_null hsub hzero)
  have hWK : ∀ k ∈ part, (Rt k).toConvexSpaceBody ≤ cellBody part Rt := fun k hk =>
    Finset.le_convexHull_biUnion (fun k => (Rt k).toConvexSpaceBody) hk
  have hWL : ∀ k ∈ part, (Rt k).toConvexSpaceBody ≤ P.toConvexSpaceBody := fun k hk =>
    (hWK k hk).trans hP
  exact ⟨P, hP, (Fz.isFrostmanIn_cellBody hpart).change_ambient hWK hWL h0 hP0⟩

include Fz in
/-- **The GWZ 6.6(B) datum, read in the tree's plank vocabulary.**

Every cell body of a `Kakeya.GlobalPlankFactorization Cw a b …` is an `a' × b × 1` plank in the
sense of `Kakeya.IsPlankOfDimensions`, for a **single** thin half-width `a'` satisfying
`ρ ≤ a' ≤ a`, and with the explicit comparability constant
`Kakeya.plankReadingConst Cw C₀ = max 3 (max (2 * Cw) C₀)`.

The three brackets come from three different clauses of the datum, and nothing else is used:

* longitudinal, `[1/2, a + b + 1]` — the coarse `ρ`-tube inside the cell (lower) and `le_plank`
  (upper);
* middle, `[min b (1/2) / Cw, a + b]` — `wide` (lower) and `le_plank` (upper);
* thin, `[a', C₀ * a']` — the choice of `a'` as the minimum of the cells' rank-`2` thicknesses
  (lower) and `ConvexSpaceBody.Factorization.simDims` (upper).

**Why `a'` and not `a`.**  The datum bounds the thin thickness only from above by `a`; a cell body
may be genuinely thinner (as thin as `ρ`).  `simDims` makes all the cells comparable, so a single
`a'` works, and `a' ≤ a` is exactly what a proof of GWZ 6.6(B) needs: the conclusion at `a'`
implies the conclusion at `a`, because `(a'/b) ^ β ≤ (a/b) ^ β`. -/
theorem exists_isPlankFamilyOfDimensions (hCw : 1 ≤ Cw) (hb1' : b ≤ 1)
    (hne : Fz.parts.Nonempty) :
    ∃ a' : ℝ≥0, ρ ≤ a' ∧ a' ≤ a ∧
      IsPlankFamilyOfDimensions (plankReadingConst Cw C₀) a' b Fz.parts
        (fun part => cellBody part Rt) := by
  classical
  set C : ℝ≥0 := plankReadingConst Cw C₀ with hCdef
  have hC1 : 1 ≤ C := one_le_plankReadingConst Cw C₀
  have hC2 : 2 ≤ C := two_le_plankReadingConst Cw C₀
  have hC3 : 3 ≤ C := three_le_plankReadingConst Cw C₀
  have hCw2 : 2 * Cw ≤ C := two_mul_le_plankReadingConst Cw C₀
  have hC0' : C₀ ≤ C := c0_le_plankReadingConst Cw C₀
  have hCne : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC1)
  have hCE1 : (1 : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC1
  have hCE2 : (2 : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC2
  have hCE3 : (3 : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC3
  -- the thin half-width: the minimum of the cells' rank-`2` thicknesses
  obtain ⟨t₂, ht₂, ht₂min⟩ :=
    Fz.parts.exists_min_image
      (fun t => Metric.ethickness ℝ (cellBody t Rt).carrier 2) hne
  have hA_le_a : Metric.ethickness ℝ (cellBody t₂ Rt).carrier 2 ≤ (a : ENNReal) :=
    Fz.ethickness_two_le ht₂
  have hAne : Metric.ethickness ℝ (cellBody t₂ Rt).carrier 2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hA_le_a
  set a' : ℝ≥0 := (Metric.ethickness ℝ (cellBody t₂ Rt).carrier 2).toNNReal with ha'def
  have hcoe : ((a' : ℝ≥0) : ENNReal) = Metric.ethickness ℝ (cellBody t₂ Rt).carrier 2 :=
    ENNReal.coe_toNNReal hAne
  have hρa' : ρ ≤ a' := by
    have h := Fz.le_ethickness_two ht₂
    rw [← hcoe] at h
    exact_mod_cast h
  have ha'a : a' ≤ a := by
    have h := hA_le_a
    rw [← hcoe] at h
    exact_mod_cast h
  refine ⟨a', hρa', ha'a, ?_⟩
  intro part hpart
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  -- longitudinal lower: `C⁻¹ ≤ τ₀`
  · have hhalf : (1 / 2 : ENNReal) ≤ Metric.ethickness ℝ (cellBody part Rt).carrier 0 :=
      Fz.le_ethickness_zero hpart
    have hkey : (1 : ENNReal)
        ≤ (C : ENNReal) * Metric.ethickness ℝ (cellBody part Rt).carrier 0 := by
      calc (1 : ENNReal) = 2 * (1 / 2 : ENNReal) := by
            rw [ENNReal.mul_div_cancel'] <;> norm_num
        _ ≤ (C : ENNReal) * Metric.ethickness ℝ (cellBody part Rt).carrier 0 := by gcongr
    simpa using inv_mul_le_of_le_mul hCne hkey
  -- longitudinal upper: `τ₀ ≤ C`
  · refine (Fz.ethickness_zero_le hpart).trans ?_
    have hae : (a : ENNReal) ≤ 1 := by exact_mod_cast hab.trans hb1'
    have hbe : (b : ENNReal) ≤ 1 := by exact_mod_cast hb1'
    calc (a : ENNReal) + (b : ENNReal) + 1 ≤ 1 + 1 + 1 := by gcongr
      _ = 3 := by norm_num
      _ ≤ (C : ENNReal) := hCE3
  -- middle lower: `C⁻¹ * b ≤ τ₁`
  · refine inv_mul_le_of_le_mul hCne ?_
    have hw : ((min b (1 / 2 : ℝ≥0) / Cw : ℝ≥0) : ENNReal)
        ≤ Metric.ethickness ℝ (cellBody part Rt).carrier 1 := Fz.le_ethickness_one hpart
    have hstep : (b : ENNReal)
        ≤ ((2 * Cw : ℝ≥0) : ENNReal) * ((min b (1 / 2 : ℝ≥0) / Cw : ℝ≥0) : ENNReal) := by
      rw [← ENNReal.coe_mul]
      exact_mod_cast le_two_mul_mul_min_div hCw hb1'
    have hCwE : ((2 * Cw : ℝ≥0) : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hCw2
    calc (b : ENNReal)
        ≤ ((2 * Cw : ℝ≥0) : ENNReal) * ((min b (1 / 2 : ℝ≥0) / Cw : ℝ≥0) : ENNReal) := hstep
      _ ≤ (C : ENNReal) * Metric.ethickness ℝ (cellBody part Rt).carrier 1 := by gcongr
  -- middle upper: `τ₁ ≤ C * b`
  · refine (Fz.ethickness_one_le hpart).trans ?_
    have habE : (a : ENNReal) ≤ (b : ENNReal) := by exact_mod_cast hab
    calc (a : ENNReal) + (b : ENNReal) ≤ (b : ENNReal) + (b : ENNReal) := by gcongr
      _ = 2 * (b : ENNReal) := by rw [two_mul]
      _ ≤ (C : ENNReal) * (b : ENNReal) := by gcongr
  -- thin lower: `C⁻¹ * a' ≤ τ₂`
  · refine inv_mul_le_of_le_mul hCne ?_
    calc ((a' : ℝ≥0) : ENNReal) = Metric.ethickness ℝ (cellBody t₂ Rt).carrier 2 := hcoe
      _ ≤ Metric.ethickness ℝ (cellBody part Rt).carrier 2 := ht₂min part hpart
      _ = 1 * Metric.ethickness ℝ (cellBody part Rt).carrier 2 := by rw [one_mul]
      _ ≤ (C : ENNReal) * Metric.ethickness ℝ (cellBody part Rt).carrier 2 := by gcongr
  -- thin upper: `τ₂ ≤ C * a'`
  · have hsim : ∀ n : ℕ, Metric.ethickness ℝ (cellBody part Rt).carrier n
        ≤ (C₀ : ℝ≥0) • Metric.ethickness ℝ (cellBody t₂ Rt).carrier n :=
      Fz.simDims part hpart t₂ ht₂
    have h2 := hsim 2
    rw [ENNReal.smul_def, smul_eq_mul] at h2
    have hC0E : (C₀ : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC0'
    calc Metric.ethickness ℝ (cellBody part Rt).carrier 2
        ≤ (C₀ : ENNReal) * Metric.ethickness ℝ (cellBody t₂ Rt).carrier 2 := h2
      _ = (C₀ : ENNReal) * ((a' : ℝ≥0) : ENNReal) := by rw [hcoe]
      _ ≤ (C : ENNReal) * ((a' : ℝ≥0) : ENNReal) := by gcongr

end GlobalPlankFactorization

end Kakeya

end

end
