/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.ComparableEnvelope
public import Kakeya.Factoring.FlatPrisms

/-!
# Exact plank envelopes for bodies in a window of radius `R`

`Kakeya.comparablePlankEnvelope` (`Kakeya/DimensionThree/Plank/ComparableEnvelope.lean`) turns a
convex body `K` with `Cw`-comparable `a × b × 1` plank dimensions into an *exact* `a × b × 1`
`Kakeya.ShadedPlank`, by shrinking the scale-collar of `K` with the fixed homothety of ratio
`Kakeya.comparablePlankEnvelope.shrink Cw = (8 * Cw)⁻¹` and then enclosing the result in its
limiting outer prism.  Its hypothesis `hKball` is `K ≤ ConvexSpaceBody.closedUnitBall`.

**Part (B) cannot supply that hypothesis.**  The Part-(B) factorisation datum
(`Kakeya.Section6PartBFactorisation`) only puts its representative planks — and hence its cell
bodies — in `Metric.closedBall 0 Kakeya.plankWindowRadius`, i.e. in the ball of radius `4`, not in
the unit ball; that is exactly what its field `repr_window` says, and the field's own docstring
records that radius `1` is *not* available.

This file removes the unit-ball restriction.  The observation is that the unit ball enters
`comparablePlankEnvelope` in exactly two places, and both are cured by enlarging the comparability
constant:

* the rank-`0` (longest) thickness bound `Metric.ethickness ℝ K.carrier 0 ≤ 1`, used to keep the
  shrunk collar inside its declared long half-width `1`;
* the containment of the shrunk collar in `Metric.closedBall 0 (1/4)`, used to keep the exact
  envelope inside the fixed radius-`4` window.

Both hold verbatim for a body in `Metric.closedBall 0 R` once the shrink ratio is taken at
`Kakeya.windowPlankEnvelope.windowConst R Cw = 4 * R * Cw` instead of at `Cw`.  No new geometry is
needed: the definitions `Kakeya.comparablePlankEnvelope.scaledCollar`,
`Kakeya.comparablePlankEnvelope.raw` and `Kakeya.comparablePlankEnvelope.plank` are reused
unchanged, at the enlarged constant, and only the four lemmas that mention the unit ball are
restated.

## The point of the construction (GWZ Proposition 6.6(B), the outer presentation)

GWZ Proposition 5.1 returns its outer bodies on the *scale-collar* of the actual factor body
(`Kakeya.ShadedBody.outerThickFamilyAtScale_outerBody_toConvexSpaceBody`), while the Section-6
assembly consumes them on exact `a × b × 1` planks.  For Part (B) the collar does **not** fit into
the cell's representative plank: a `Kakeya.Plank a b` is a `Kakeya.Prism3D a b 1` whose long
half-width is exactly `1`, whereas a cell body reaching to the boundary of the window has its
`s`-collar reaching to `1 + s`.  Clipping the shade to the representative plank is not free, since
`Kakeya.ShadedBody.multiplicity` shrinks in both numerator and denominator.  The honest route is
the one this file supports: present the outer family on an exact plank *around the shrunk collar*
and transport the whole family by the single common homothety, under which multiplicity is
invariant, fullness and Katz--Tao lose only the fixed envelope volume ratio, and the shadings are
carried over **exactly**.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

namespace windowPlankEnvelope

abbrev E3 := EuclideanSpace ℝ (Fin 3)

open comparablePlankEnvelope

/-! ### The enlarged comparability constant -/

/-- The comparability constant handed to `Kakeya.comparablePlankEnvelope` for a body living in
`Metric.closedBall 0 R` rather than in the unit ball. -/
def windowConst (R Cw : ℝ≥0) : ℝ≥0 := 4 * R * Cw

theorem one_le_windowConst {R Cw : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw) :
    1 ≤ windowConst R Cw := by
  have h4 : (1 : ℝ≥0) ≤ 4 := by norm_num
  calc
    (1 : ℝ≥0) = 1 * 1 * 1 := by norm_num
    _ ≤ 4 * R * Cw := by
      exact mul_le_mul' (mul_le_mul' h4 hR) hCw

theorem windowConst_pos {R Cw : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw) :
    0 < windowConst R Cw := zero_lt_one.trans_le (one_le_windowConst hR hCw)

/-- The rank-`0` budget: twice the window radius is below `8` times the enlarged constant. -/
theorem two_mul_le_eight_mul_windowConst {R Cw : ℝ≥0} (_hR : 1 ≤ R) (hCw : 1 ≤ Cw) :
    2 * R ≤ 8 * windowConst R Cw := by
  have h : (2 : ℝ≥0) * R ≤ 32 * R * Cw := by
    calc
      (2 : ℝ≥0) * R = 2 * R * 1 := by rw [mul_one]
      _ ≤ 32 * R * Cw := by
        exact mul_le_mul' (mul_le_mul_right' (by norm_num : (2 : ℝ≥0) ≤ 32) R) hCw
  calc
    (2 : ℝ≥0) * R ≤ 32 * R * Cw := h
    _ = 8 * windowConst R Cw := by rw [windowConst]; ring

/-- The transverse budget: twice the original constant is below `8` times the enlarged one. -/
theorem two_mul_le_eight_mul_windowConst' {R Cw : ℝ≥0} (hR : 1 ≤ R) (_hCw : 1 ≤ Cw) :
    2 * Cw ≤ 8 * windowConst R Cw := by
  have h : (2 : ℝ≥0) * Cw ≤ 32 * R * Cw := by
    calc
      (2 : ℝ≥0) * Cw = 2 * 1 * Cw := by rw [mul_one]
      _ ≤ 32 * R * Cw := by
        exact mul_le_mul_right' (mul_le_mul' (by norm_num : (2 : ℝ≥0) ≤ 32) hR) Cw
  calc
    (2 : ℝ≥0) * Cw ≤ 32 * R * Cw := h
    _ = 8 * windowConst R Cw := by rw [windowConst]; ring

/-! ### The two arithmetic steps -/

/-- The shrink ratio, as an `ℝ≥0∞` inverse. -/
theorem eight_mul_ne_zero {C : ℝ≥0} (hC : 0 < C) : (8 : ℝ≥0) * C ≠ 0 :=
  mul_ne_zero (by norm_num) hC.ne'

theorem coe_shrink (C : ℝ≥0) (hC : 0 < C) :
    ((shrink C : ℝ≥0) : ENNReal) = ((8 * C : ℝ≥0) : ENNReal)⁻¹ := by
  rw [shrink, ENNReal.coe_inv (eight_mul_ne_zero hC)]

/-- The single arithmetic step behind every thickness bound below: if `x ≤ M * y` and
`2 * M ≤ 8 * C` then `(8 * C)⁻¹ * (2 * x) ≤ y`. -/
theorem shrink_mul_two_mul_le' {C M : ℝ≥0} (hC : 0 < C) {x y : ENNReal}
    (hx : x ≤ (M : ENNReal) * y) (hM : 2 * M ≤ 8 * C) :
    ((8 * C : ℝ≥0) : ENNReal)⁻¹ * (2 * x) ≤ y := by
  have hne : ((8 * C : ℝ≥0) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (eight_mul_ne_zero hC)
  have htop : ((8 * C : ℝ≥0) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hMle : (2 : ENNReal) * (M : ENNReal) ≤ ((8 * C : ℝ≥0) : ENNReal) := by
    have h := ENNReal.coe_le_coe.mpr hM
    rw [ENNReal.coe_mul, ENNReal.coe_ofNat] at h
    exact h
  calc
    ((8 * C : ℝ≥0) : ENNReal)⁻¹ * (2 * x)
        ≤ ((8 * C : ℝ≥0) : ENNReal)⁻¹ * (2 * ((M : ENNReal) * y)) := by
          exact mul_le_mul_left' (mul_le_mul_left' hx 2) _
    _ = (((8 * C : ℝ≥0) : ENNReal)⁻¹ * (2 * (M : ENNReal))) * y := by ring
    _ ≤ (((8 * C : ℝ≥0) : ENNReal)⁻¹ * ((8 * C : ℝ≥0) : ENNReal)) * y := by
          exact mul_le_mul_right' (mul_le_mul_left' hMle _) y
    _ = y := by rw [ENNReal.inv_mul_cancel hne htop, one_mul]

/-! ### The three thickness bounds -/

/-- Every affine thickness of the shrunk collar, in one place. -/
theorem ethickness_scaledCollar_le' (C : ℝ≥0) (K : ConvexSpaceBody E3) (k : ℕ) :
    Metric.ethickness ℝ (scaledCollar C K).carrier k ≤
      ((shrink C : ℝ≥0) : ENNReal) * (2 * Metric.ethickness ℝ K.carrier k) := by
  refine (ethickness_scaledCollar_le C K k).trans ?_
  gcongr
  simpa [Pi.smul_apply, two_nsmul, two_mul] using
    (ConvexSpaceBody.ethickness_cthickening_le_two K (scaleRadius K) (by simp) k)

/-- **The three upper thickness bounds of the shrunk collar, for a body in a window of
radius `R`.**  The unit-ball hypothesis of
`Kakeya.comparablePlankEnvelope.ethickness_scaledCollar_bounds` is replaced by the rank-`0`
bound `Metric.ethickness ℝ K.carrier 0 ≤ R`. -/
theorem ethickness_scaledCollar_window_bounds {R Cw a b : ℝ≥0} {K : ConvexSpaceBody E3}
    (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hK0 : Metric.ethickness ℝ K.carrier 0 ≤ (R : ENNReal))
    (hK1 : Metric.ethickness ℝ K.carrier 1 ≤ (Cw : ENNReal) * (b : ENNReal))
    (hK2 : Metric.ethickness ℝ K.carrier 2 ≤ (Cw : ENNReal) * (a : ENNReal)) :
    Metric.ethickness ℝ (scaledCollar (windowConst R Cw) K).carrier 0 ≤ 1 ∧
      Metric.ethickness ℝ (scaledCollar (windowConst R Cw) K).carrier 1 ≤ (b : ENNReal) ∧
      Metric.ethickness ℝ (scaledCollar (windowConst R Cw) K).carrier 2 ≤ (a : ENNReal) := by
  have hCpos : 0 < windowConst R Cw := windowConst_pos hR hCw
  have hcoe := coe_shrink (windowConst R Cw) hCpos
  refine ⟨?_, ?_, ?_⟩
  · refine (ethickness_scaledCollar_le' (windowConst R Cw) K 0).trans ?_
    rw [hcoe]
    refine shrink_mul_two_mul_le' (M := R) hCpos ?_ (two_mul_le_eight_mul_windowConst hR hCw)
    simpa using hK0
  · refine (ethickness_scaledCollar_le' (windowConst R Cw) K 1).trans ?_
    rw [hcoe]
    exact shrink_mul_two_mul_le' (M := Cw) hCpos hK1
      (two_mul_le_eight_mul_windowConst' hR hCw)
  · refine (ethickness_scaledCollar_le' (windowConst R Cw) K 2).trans ?_
    rw [hcoe]
    exact shrink_mul_two_mul_le' (M := Cw) hCpos hK2
      (two_mul_le_eight_mul_windowConst' hR hCw)

/-- Real-valued form of `Kakeya.windowPlankEnvelope.ethickness_scaledCollar_window_bounds`. -/
theorem thickness_scaledCollar_window_bounds {R Cw a b : ℝ≥0} {K : ConvexSpaceBody E3}
    (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hK0 : Metric.ethickness ℝ K.carrier 0 ≤ (R : ENNReal))
    (hK1 : Metric.ethickness ℝ K.carrier 1 ≤ (Cw : ENNReal) * (b : ENNReal))
    (hK2 : Metric.ethickness ℝ K.carrier 2 ≤ (Cw : ENNReal) * (a : ENNReal)) :
    Metric.thickness ℝ (scaledCollar (windowConst R Cw) K).carrier 0 ≤ 1 ∧
      Metric.thickness ℝ (scaledCollar (windowConst R Cw) K).carrier 1 ≤ (b : ℝ) ∧
      Metric.thickness ℝ (scaledCollar (windowConst R Cw) K).carrier 2 ≤ (a : ℝ) := by
  obtain ⟨hzero, hone, htwo⟩ :=
    ethickness_scaledCollar_window_bounds hR hCw hK0 hK1 hK2
  have hbdd := (scaledCollar (windowConst R Cw) K).isCompact'.isBounded
  refine ⟨?_, ?_, ?_⟩
  · rw [← Metric.toReal_ethickness hbdd 0]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hzero
  · rw [← Metric.toReal_ethickness hbdd 1]
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hone
  · rw [← Metric.toReal_ethickness hbdd 2]
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top htwo

/-! ### The exact envelope -/

/-- The limiting outer prism of the shrunk collar lies in the exact `a × b × 1` envelope. -/
theorem raw_le_plank_window {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) {K : ConvexSpaceBody E3}
    (hK0 : Metric.ethickness ℝ K.carrier 0 ≤ (R : ENNReal))
    (hK1 : Metric.ethickness ℝ K.carrier 1 ≤ (Cw : ENNReal) * (b : ENNReal))
    (hK2 : Metric.ethickness ℝ K.carrier 2 ≤ (Cw : ENNReal) * (a : ENNReal)) :
    (raw (windowConst R Cw) K).toConvexSpaceBody ≤
      (plank (windowConst R Cw) a b hab hb1 K).toConvexSpaceBody := by
  obtain ⟨hzero, hone, htwo⟩ := thickness_scaledCollar_window_bounds hR hCw hK0 hK1 hK2
  set C := windowConst R Cw with hC
  intro x hx
  change x ∈ (plank C a b hab hb1 K).carrier
  rw [(plank C a b hab hb1 K).mem_carrier_iff]
  intro i
  have hx' : x ∈ (raw C K).carrier := hx
  have hraw := ((raw C K).mem_carrier_iff x).mp hx' (Fin.revPerm.symm i)
  change
    |((raw C K).basis.reindex Fin.revPerm).repr (x - (raw C K).center) i| ≤
      (![a, b, 1] : Fin 3 → ℝ≥0) i
  rw [OrthonormalBasis.repr_reindex]
  fin_cases i <;> simp at hraw ⊢
  · exact hraw.trans htwo
  · exact hraw.trans hone
  · exact hraw.trans hzero

/-- The shrunk collar lies in the exact `a × b × 1` envelope. -/
theorem scaledCollar_le_plank_window {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) {K : ConvexSpaceBody E3}
    (hK0 : Metric.ethickness ℝ K.carrier 0 ≤ (R : ENNReal))
    (hK1 : Metric.ethickness ℝ K.carrier 1 ≤ (Cw : ENNReal) * (b : ENNReal))
    (hK2 : Metric.ethickness ℝ K.carrier 2 ≤ (Cw : ENNReal) * (a : ENNReal)) :
    scaledCollar (windowConst R Cw) K ≤
      (plank (windowConst R Cw) a b hab hb1 K).toConvexSpaceBody :=
  (outerPrism.self_subset (by simp) (scaledCollar (windowConst R Cw) K).isCompact'
    (scaledCollar (windowConst R Cw) K).nonempty').trans
      (raw_le_plank_window hR hCw hab hb1 hK0 hK1 hK2)

/-- **The shrunk collar of a body from a window of radius `R` sits in `B(0, 1/4)`.**  The
enlarged constant is exactly what buys the `1/4`: the collar is inside `Metric.closedBall 0 (2 * R)`
and `2 * R * (8 * (4 * R * Cw))⁻¹ ≤ 1/4`. -/
theorem scaledCollar_subset_closedBall_quarter_window {R Cw : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    {K : ConvexSpaceBody E3}
    (hKball : (K.carrier : Set E3) ⊆ Metric.closedBall 0 (R : ℝ)) :
    (scaledCollar (windowConst R Cw) K).carrier ⊆ Metric.closedBall 0 (1 / 4 : ℝ) := by
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := (R : ℝ≥0).coe_nonneg
  have hscale : K.scale ≤ (R : ℝ) :=
    Metric.thickness_le_of_subset_closedBall hKball hR0 _
  have hcollar : Metric.cthickening (scaleRadius K : ℝ) (K.carrier : Set E3) ⊆
      Metric.closedBall (0 : E3) (2 * (R : ℝ)) := by
    refine (Metric.cthickening_subset_of_subset _ hKball).trans ?_
    refine (Metric.cthickening_mono (show (scaleRadius K : ℝ) ≤ (R : ℝ) by
      simpa using hscale) _).trans ?_
    rw [cthickening_closedBall hR0 hR0]
    exact Metric.closedBall_subset_closedBall (by linarith)
  intro y hy
  change y ∈ AffineMap.homothety (0 : E3) ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ''
    Metric.cthickening (scaleRadius K : ℝ) (K.carrier : Set E3) at hy
  rcases hy with ⟨z, hz, rfl⟩
  have hz' : dist z (0 : E3) ≤ 2 * (R : ℝ) := Metric.mem_closedBall.mp (hcollar hz)
  have hzNorm : ‖z‖ ≤ 2 * (R : ℝ) := by simpa [dist_eq_norm] using hz'
  rw [Metric.mem_closedBall]
  have hCposR : (0 : ℝ) < (windowConst R Cw : ℝ) := by
    exact_mod_cast windowConst_pos hR hCw
  have hshrinkR : ((shrink (windowConst R Cw) : ℝ≥0) : ℝ)
      = 1 / (8 * (windowConst R Cw : ℝ)) := by
    rw [shrink, NNReal.coe_inv, NNReal.coe_mul]
    norm_num
  have hRleC : (R : ℝ) ≤ (windowConst R Cw : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Cw : ℝ) := by exact_mod_cast hCw
    have h2 : (0 : ℝ) ≤ (R : ℝ) := (R : ℝ≥0).coe_nonneg
    rw [windowConst]
    push_cast
    nlinarith
  have hkey : (2 : ℝ) * (R : ℝ) * ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ≤ 1 / 4 := by
    rw [hshrinkR]
    set u : ℝ := 1 / (8 * (windowConst R Cw : ℝ)) with hu
    have hu0 : 0 ≤ u := by rw [hu]; positivity
    have hmul : u * (8 * (windowConst R Cw : ℝ)) = 1 := by
      rw [hu]; field_simp
    nlinarith [hRleC, hu0, hmul]
  calc
    dist (AffineMap.homothety (0 : E3) ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) z) 0
        = ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) * ‖z‖ := by
      simp [AffineMap.homothety_apply, dist_eq_norm, norm_smul]
    _ ≤ ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) * (2 * (R : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hzNorm (shrink (windowConst R Cw)).coe_nonneg
    _ ≤ 1 / 4 := by
      rw [show ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) * (2 * (R : ℝ))
        = 2 * (R : ℝ) * ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) by ring]
      exact hkey

/-- **The exact envelope of a body from a window of radius `R` lies in the fixed radius-four
plank window.**  Word for word `Kakeya.comparablePlankEnvelope.plank_carrier_subset_window`, with
the unit ball replaced by the radius-`R` ball. -/
theorem plank_carrier_subset_window_of_window {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) {K : ConvexSpaceBody E3}
    (hKball : (K.carrier : Set E3) ⊆ Metric.closedBall 0 (R : ℝ)) :
    (plank (windowConst R Cw) a b hab hb1 K).carrier ⊆
      Metric.closedBall 0 (plankWindowRadius : ℝ) := by
  set C := windowConst R Cw with hC
  have hscaled := scaledCollar_subset_closedBall_quarter_window hR hCw hKball
  obtain ⟨x, hx⟩ := (scaledCollar C K).nonempty'
  have hxball : dist x (0 : E3) ≤ 1 / 4 := Metric.mem_closedBall.mp (hscaled hx)
  have hxraw : x ∈ (raw C K).carrier :=
    outerPrism.self_subset (by simp) (scaledCollar C K).isCompact'
      (scaledCollar C K).nonempty' hx
  have hthick (i : Fin 3) : ((raw C K).thicknesses i : ℝ) ≤ 1 / 4 := by
    rw [raw, outerPrism.thicknesses_eq]
    exact Metric.thickness_le_of_subset_closedBall hscaled (by norm_num) i
  have hsumRaw : (∑ i : Fin 3, ((raw C K).thicknesses i : ℝ)) ≤ 3 / 4 := by
    rw [Fin.sum_univ_three]
    linarith [hthick (0 : Fin 3), hthick (1 : Fin 3), hthick (2 : Fin 3)]
  have hxc : dist x (raw C K).center ≤ 3 / 4 :=
    (Metric.mem_closedBall.mp ((raw C K).carrier_subset_closedBall hxraw)).trans hsumRaw
  have hc0 : dist (raw C K).center (0 : E3) ≤ 1 := by
    calc
      dist (raw C K).center 0 ≤ dist (raw C K).center x + dist x 0 := dist_triangle _ _ _
      _ ≤ 1 := by rw [dist_comm (raw C K).center x]; linarith
  intro y hy
  have hyc : dist y (raw C K).center ≤ 3 := by
    have hy' : y ∈ (plank C a b hab hb1 K).toPrismNDim.carrier := hy
    have hball := Metric.mem_closedBall.mp
      ((plank C a b hab hb1 K).toPrismNDim.carrier_subset_closedBall hy')
    have hsum :
        (∑ i : Fin 3,
          (((plank C a b hab hb1 K).toPrismNDim.thicknesses i : ℝ≥0) : ℝ)) ≤ 3 := by
      rw [(plank C a b hab hb1 K).thicknesses_eq, Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      have ha1 : a ≤ 1 := hab.trans hb1
      change (a : ℝ) + (b : ℝ) + 1 ≤ 3
      have ha1R : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
      have hb1R : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
      linarith
    simpa [plank, PrismNDim.center_mk'] using hball.trans hsum
  apply Metric.mem_closedBall.mpr
  simpa [Kakeya.plankWindowRadius] using (show dist y 0 ≤ (4 : ℝ) by
    calc
      dist y 0 ≤ dist y (raw C K).center + dist (raw C K).center 0 := dist_triangle _ _ _
      _ ≤ 4 := by linarith)

/-! ### The shaded exact envelope -/

/-- **The exact `a × b × 1` shaded plank presentation of a scale-collar shading.**

`Y` is the Proposition-5.1 outer body of the cell whose actual body is `K`: its convex body is the
`Kakeya.ConvexSpaceBody.scale`-collar of `K`.  The output is an exact `a × b × 1`
`Kakeya.ShadedPlank` whose shading is the image of `Y`'s shading under the *single common*
homothety of ratio `Kakeya.comparablePlankEnvelope.shrink (windowConst R Cw)` centred at the
origin.  Nothing is clipped. -/
def shadedPlankWindow {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody E3) (Y : ShadedBody E3)
    (hY : Y.toConvexSpaceBody = K.cthickening (scaleRadius K : ℝ))
    (hK0 : Metric.ethickness ℝ K.carrier 0 ≤ (R : ENNReal))
    (hK1 : Metric.ethickness ℝ K.carrier 1 ≤ (Cw : ENNReal) * (b : ENNReal))
    (hK2 : Metric.ethickness ℝ K.carrier 2 ≤ (Cw : ENNReal) * (a : ENNReal)) :
    ShadedPlank a b hab hb1 where
  toPrism3D := plank (windowConst R Cw) a b hab hb1 K
  shade := (Y.homothety 0 (shrink_coe_ne_zero (one_le_windowConst hR hCw))).shade
  measurableSet_shade :=
    (Y.homothety 0 (shrink_coe_ne_zero (one_le_windowConst hR hCw))).measurableSet_shade
  shade_subset := by
    have hshrink : ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ≠ 0 :=
      shrink_coe_ne_zero (one_le_windowConst hR hCw)
    have hbody : (Y.homothety 0 hshrink).toConvexSpaceBody =
        scaledCollar (windowConst R Cw) K := by
      rw [ShadedBody.homothety_toConvexSpaceBody, hY]
      rfl
    exact (Y.homothety 0 hshrink).shade_subset.trans <| by
      rw [hbody]
      exact scaledCollar_le_plank_window hR hCw hab hb1 hK0 hK1 hK2

@[simp]
theorem shadedPlankWindow_shade {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody E3) (Y : ShadedBody E3)
    (hY : Y.toConvexSpaceBody = K.cthickening (scaleRadius K : ℝ))
    (hK0 : Metric.ethickness ℝ K.carrier 0 ≤ (R : ENNReal))
    (hK1 : Metric.ethickness ℝ K.carrier 1 ≤ (Cw : ENNReal) * (b : ENNReal))
    (hK2 : Metric.ethickness ℝ K.carrier 2 ≤ (Cw : ENNReal) * (a : ENNReal)) :
    (shadedPlankWindow hR hCw hab hb1 K Y hY hK0 hK1 hK2).shade =
      (Y.homothety 0 (shrink_coe_ne_zero (one_le_windowConst hR hCw))).shade := rfl

@[simp]
theorem shadedPlankWindow_toPrism3D {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody E3) (Y : ShadedBody E3)
    (hY : Y.toConvexSpaceBody = K.cthickening (scaleRadius K : ℝ))
    (hK0 : Metric.ethickness ℝ K.carrier 0 ≤ (R : ENNReal))
    (hK1 : Metric.ethickness ℝ K.carrier 1 ≤ (Cw : ENNReal) * (b : ENNReal))
    (hK2 : Metric.ethickness ℝ K.carrier 2 ≤ (Cw : ENNReal) * (a : ENNReal)) :
    (shadedPlankWindow hR hCw hab hb1 K Y hY hK0 hK1 hK2).toPrism3D =
      plank (windowConst R Cw) a b hab hb1 K := rfl

end windowPlankEnvelope

end Kakeya

end

end
