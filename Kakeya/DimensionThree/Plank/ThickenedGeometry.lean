/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Plank.ThickenedReprVolume
public import Kakeya.DimensionThree.Volume
public import Kakeya.Mathlib.Algebra.Order.Field
public import Kakeya.Mathlib.Analysis.EuclideanFrame

/-!
# Geometry supporting thickened representatives

Anisotropic intersection estimates and scale-aware two-sided dilation comparability for
equal-scale thickened planks, built on the prism volume estimates of
`Kakeya.DimensionThree.Plank.ThickenedReprVolume`.

The file keeps the visibility regime it was written with: only its `public` declarations are
exported.
-/

section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-- `ENNReal.ofReal` of the volume threshold `4θb²`, the bridge between the real-valued
anisotropic estimates and the `ENNReal`-valued volume bound. -/
theorem ofReal_four_mul_theta_mul_sq (θ b : ℝ≥0) :
    ENNReal.ofReal (4 * (θ : ℝ) * (b : ℝ) ^ 2) = 4 * (θ : ENNReal) * (b : ENNReal) ^ 2 := by
  simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow]

/-- Two non-essentially-distinct `θ`-thickenings overlap in volume more than the threshold
`4θb²`, which is half the volume `8θb²` of either one. -/
theorem four_mul_theta_mul_sq_lt_volume_inter
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim)) :
    4 * (θ : ENNReal) * (b : ENNReal) ^ 2 <
      volume (((P.thickened θ hθ1).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (P'.thickened θ hθ1).carrier) := by
  have hvol : ∀ S : ThickenedPlank θ b hθ1 hb1,
      volume S.carrier = 2 * (4 * (θ : ENNReal) * (b : ENNReal) ^ 2) := fun S => by
    rw [Prism3D.volume_carrier S]; push_cast; ring
  have h_gt := not_le.mp hnd
  rwa [hvol, hvol, max_self, ← mul_assoc, one_div,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul] at h_gt

/-- Essential distinctness of prisms is symmetric, hence so is its negation. Isolated so the reverse
containment can be obtained by swapping `P` and `P'`. -/
theorem not_essentiallyDistinct_symm
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim)) :
    ¬ PrismNDim.IsEssentiallyDistinct ((P'.thickened θ hθ1).toPrismNDim)
        ((P.thickened θ hθ1).toPrismNDim) :=
  fun h => hnd (PrismNDim.IsEssentiallyDistinct.symm h)

/-- Real-valued form of `four_mul_theta_mul_sq_lt_volume_inter`: any real upper bound `W > 0` for
the intersection volume beats the threshold `4θb²`. This is the single point at which the three
anisotropic estimates cross from `ENNReal` to `ℝ`. -/
theorem four_mul_theta_mul_sq_lt_of_volume_inter_le
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim))
    {W : ℝ} (hW : 0 < W)
    (hle : volume (((P.thickened θ hθ1).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (P'.thickened θ hθ1).carrier) ≤ ENNReal.ofReal W) :
    4 * (θ : ℝ) * (b : ℝ) ^ 2 < W := by
  rw [← ENNReal.ofReal_lt_ofReal_iff hW, ofReal_four_mul_theta_mul_sq]
  exact (four_mul_theta_mul_sq_lt_volume_inter P P' hnd).trans_le hle

/-- Two non-essentially-distinct thickenings share a point: their intersection has volume more
than `4θb² > 0`, hence is nonempty. -/
theorem exists_mem_inter_of_not_essentiallyDistinct
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim)) :
    ∃ p : EuclideanSpace ℝ (Fin 3),
      p ∈ ((P.thickened θ hθ1).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∧
        p ∈ ((P'.thickened θ hθ1).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  exact MeasureTheory.nonempty_of_measure_ne_zero fun h0 =>
    ENNReal.not_lt_zero (h0 ▸ four_mul_theta_mul_sq_lt_volume_inter P P' hnd)

/-- The three frame coordinates of a point of a `θ`-thickening, against its half-widths
`θb`, `b`, `1`. -/
theorem abs_inner_thickened_le {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0}
    {hθ1 : θ ≤ 1} (P : Plank a b hab hb1) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ ((P.thickened θ hθ1).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    |inner ℝ ((P.thickened θ hθ1).basis 0) (p -ᵥ (P.thickened θ hθ1).center)|
        ≤ (θ : ℝ) * (b : ℝ) ∧
      |inner ℝ ((P.thickened θ hθ1).basis 1) (p -ᵥ (P.thickened θ hθ1).center)| ≤ (b : ℝ) ∧
      |inner ℝ ((P.thickened θ hθ1).basis 2) (p -ᵥ (P.thickened θ hθ1).center)| ≤ (1 : ℝ) := by
  have h := (PrismNDim.mem_carrier_iff _ p).1 hp
  simp only [OrthonormalBasis.repr_apply_apply,
    Prism3D.thicknesses_eq (P.thickened θ hθ1)] at h
  exact ⟨by simpa only [Matrix.cons_val_zero, NNReal.coe_mul] using h 0,
    by simpa only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] using h 1,
    by simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      NNReal.coe_one] using h 2⟩

/-- The three frame coordinates of a point of the `r`-dilation of a `θ`-thickening. -/
theorem abs_inner_dilation_thickened_le {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0}
    {hθ1 : θ ≤ 1} (P : Plank a b hab hb1) {r : ℝ≥0} {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (((P.thickened θ hθ1).toPrismNDim.dilation r).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))) :
    |inner ℝ ((P.thickened θ hθ1).basis 0) (x -ᵥ (P.thickened θ hθ1).center)|
        ≤ (r : ℝ) * ((θ : ℝ) * (b : ℝ)) ∧
      |inner ℝ ((P.thickened θ hθ1).basis 1) (x -ᵥ (P.thickened θ hθ1).center)|
        ≤ (r : ℝ) * (b : ℝ) ∧
      |inner ℝ ((P.thickened θ hθ1).basis 2) (x -ᵥ (P.thickened θ hθ1).center)|
        ≤ (r : ℝ) * (1 : ℝ) := by
  have hx' := (PrismNDim.mem_carrier_iff _ x).1 hx
  simp only [PrismNDim.dilation_center, PrismNDim.dilation_basis, PrismNDim.dilation_thicknesses,
    OrthonormalBasis.repr_apply_apply, Prism3D.thicknesses_eq (P.thickened θ hθ1),
    NNReal.coe_mul] at hx'
  exact ⟨by simpa only [Matrix.cons_val_zero, NNReal.coe_mul] using hx' 0,
    by simpa only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] using hx' 1,
    by simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      NNReal.coe_one] using hx' 2⟩

theorem thickening_frame_coeff_lt_of_not_essentiallyDistinct {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} (hθ1 : θ ≤ 1) (hθ0 : 0 < θ) (hb0 : 0 < b) (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim)) :
    |inner ℝ ((P.thickened θ hθ1).basis 1) ((P'.thickened θ hθ1).basis 0)| < 2 * (θ : ℝ) ∧
      |inner ℝ ((P.thickened θ hθ1).basis 2) ((P'.thickened θ hθ1).basis 0)|
        < 2 * (θ : ℝ) * (b : ℝ) := by
  have hθpos : 0 < (θ : ℝ) := by exact_mod_cast hθ0
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast hb0
  have hA : (0 : ℝ) < 4 * (θ : ℝ) * (b : ℝ) ^ 2 := by positivity
  have hc : (0 : ℝ) < 2 * (θ : ℝ) * (b : ℝ) := by positivity
  set T := P.thickened θ hθ1
  set T' := P'.thickened θ hθ1
  set a₁ := inner ℝ (T.basis 1) (T'.basis 0)
  set a₂ := inner ℝ (T.basis 2) (T'.basis 0)
  set M := max (|a₁| * (b : ℝ)) (|a₂| * ((1 : ℝ≥0) : ℝ)) with hM_def
  -- `M < 2θb`: vacuous when `M = 0`; otherwise `|T ∩ T'| ≤ 8(θb)²b / M` from
  -- `volume_inter_le_weighted` against `|T ∩ T'| > 4θb²`, and the `θb²` cancels.
  have h_M_lt : M < 2 * (θ : ℝ) * (b : ℝ) :=
    lt_of_lt_mul_div hA hc
      ((le_max_of_le_left (mul_nonneg (abs_nonneg _) b.coe_nonneg)).trans_eq hM_def.symm)
      fun hMpos => four_mul_theta_mul_sq_lt_of_volume_inter_le P P' hnd
        (div_pos (mul_pos hA hc) hMpos)
        ((ThickenedReprPrism3D.volume_inter_le_weighted T T' hb0 one_pos hMpos).trans_eq
          (by rw [hM_def]; congr 1; push_cast; ring))
  exact ⟨lt_of_mul_lt_mul_right (((le_max_left _ _).trans_eq hM_def.symm).trans_lt h_M_lt)
      hbpos.le,
    by simpa using ((le_max_right _ _).trans_eq hM_def.symm).trans_lt h_M_lt⟩

/-- **In-plane rotation bound at scale `b` for non-distinct thickenings.** If the standard
`θ`-thickenings `T, T'` are *not* essentially distinct then, with `e₀, e₂` the thin and long axes of
`T` and `e₁'` the middle axis of `T'`, we have `|⟪e₂, e₁'⟫| < 2b`.

This is the **in-plane** control, at scale `b` rather than `θb`, and it is what the thin-normal
estimates provably cannot give (a rotation inside the common long plane leaves both short normals
equal). It comes from `Prism3D.volume_inter_le_weighted_mid` at `a = θb`, `c = 1`: non-distinctness
gives `|T ∩ T'| > 4θb²`, and against `8b²·(θb)·1 / max (|⟪e₀,e₁'⟫|·θb) (|⟪e₂,e₁'⟫|·1)` this forces
`max (|⟪e₀,e₁'⟫|·θb) (|⟪e₂,e₁'⟫|) < 2b`. -/
theorem thickening_inPlane_coeff_lt_of_not_essentiallyDistinct {a b : ℝ≥0} {hab : a ≤ b}
    {hb1 : b ≤ 1} {θ : ℝ≥0} (hθ1 : θ ≤ 1) (hθ0 : 0 < θ) (hb0 : 0 < b)
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim)) :
    |inner ℝ ((P.thickened θ hθ1).basis 2) ((P'.thickened θ hθ1).basis 1)| < 2 * (b : ℝ) := by
  have hθpos : 0 < (θ : ℝ) := by exact_mod_cast hθ0
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast hb0
  have hθb : (0 : ℝ) < ((θ * b : ℝ≥0) : ℝ) := by push_cast; exact mul_pos hθpos hbpos
  have hA : (0 : ℝ) < 4 * (θ : ℝ) * (b : ℝ) ^ 2 := by positivity
  have hc : (0 : ℝ) < 2 * (b : ℝ) := by positivity
  set T := P.thickened θ hθ1
  set T' := P'.thickened θ hθ1
  set m₀ := inner ℝ (T.basis 0) (T'.basis 1)
  set m₂ := inner ℝ (T.basis 2) (T'.basis 1)
  set M := max (|m₀| * ((θ * b : ℝ≥0) : ℝ)) (|m₂| * ((1 : ℝ≥0) : ℝ)) with hM_def
  -- `M < 2b`: vacuous when `M = 0`; otherwise `|T ∩ T'| ≤ 8b²(θb) / M` from
  -- `volume_inter_le_weighted_mid` against `|T ∩ T'| > 4θb²`, and the `θb²` cancels.
  have h_M_lt : M < 2 * (b : ℝ) :=
    lt_of_lt_mul_div hA hc
      ((le_max_of_le_right (mul_nonneg (abs_nonneg _) zero_le_one)).trans_eq hM_def.symm)
      fun hMpos => four_mul_theta_mul_sq_lt_of_volume_inter_le P P' hnd
        (div_pos (mul_pos hA hc) hMpos)
        ((ThickenedReprPrism3D.volume_inter_le_weighted_mid T T' hθb one_pos hMpos).trans_eq
          (by rw [hM_def]; congr 1; push_cast; ring))
  simpa using ((le_max_right _ _).trans_eq hM_def.symm).trans_lt h_M_lt

/-- **Overlap of equal-scale thickenings forces a small short-normal angle.** Two standard
`θ`-thickenings (equal-scale `θb × b × 1` prisms) of `a × b × 1` planks that are *not* essentially
distinct make short-normal angle `< 8 · θ`.

Each thickening has volume `8θb²`, so non-distinctness forces `|T ∩ T'| > 4θb²`, while
`Prism3D.volume_inter_le` bounds `|T ∩ T'| ≤ 32 (θb)² / φ`; the `b²` cancels and gives `φ < 8θ`.
This is the exact analogue of `slab_angle_lt_of_not_essentiallyDistinct`, and it is the step for
which the scale-parameterized `Prism3D.volume_inter_le` was needed: the slab-scale estimate would
only give the vacuous `φ ≲ θ/b²`. -/
public theorem thickening_angle_lt_of_not_essentiallyDistinct
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} (hθ1 : θ ≤ 1) (hθ0 : 0 < θ) (hb0 : 0 < b) (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim)) :
    Prism3D.angle (P.thickened θ hθ1) (P'.thickened θ hθ1) < 8 * (θ : ℝ) := by
  have hθpos : 0 < (θ : ℝ) := by exact_mod_cast hθ0
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast hb0
  have hA : (0 : ℝ) < 4 * (θ : ℝ) * (b : ℝ) ^ 2 := by positivity
  have hc : (0 : ℝ) < 8 * (θ : ℝ) := by positivity
  set T := P.thickened θ hθ1
  set T' := P'.thickened θ hθ1
  -- `|T ∩ T'| ≤ 32(θb)²/φ` from `volume_inter_le` against `|T ∩ T'| > 4θb²`; the `b²` cancels.
  refine lt_of_lt_mul_div hA hc (Prism3D.angle_nonneg T T') fun hφ_pos =>
    four_mul_theta_mul_sq_lt_of_volume_inter_le P P' hnd (div_pos (mul_pos hA hc) hφ_pos)
      ((ThickenedReprPrism3D.volume_inter_le T T' hφ_pos le_rfl).trans_eq ?_)
  rw [ENNReal.ofReal_div_of_pos hφ_pos,
    show 4 * (θ : ℝ) * (b : ℝ) ^ 2 * (8 * (θ : ℝ)) = ((32 * θ ^ 2 * b ^ 2 : ℝ≥0) : ℝ) by
      push_cast; ring,
    ENNReal.ofReal_coe_nnreal]
  push_cast
  rw [mul_one, mul_pow, ← mul_assoc]

-- The three `thickening_coordK_le` lemmas below share one shape: each splits
-- `⟪T.basis k, x -ᵥ T.center⟫` through a common point `p` (`abs_inner_vsub_le_split`) and expands
-- the two `T'`-referred terms over `T'`'s frame (`abs_inner_le_sum_frame`), each of the six
-- resulting products carrying its own coefficient bound.
/-- Common core of the three `thickening_coordK_le` estimates.  Splitting through a point `p` of
`T ∩ T'` and expanding the two `T'`-referred terms over `T'`'s frame, bounds `cⱼ` on the
cross-frame coefficients `⟪T.basis k, T'.basis j⟫` give `r·S` from the `x`-terms and `S` from the
`p`-terms, where `S = θb·c₀ + b·c₁ + c₂`; inflating the `p`-terms by `r ≥ 1` makes both sides
`r·S`, and the own-frame term adds the `k`-th half-width. -/
private theorem thickening_coord_le_of_cross_bounds -- (extracted by Fuse golfer)
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim))
    {r : ℝ≥0} (hr : 1 ≤ r) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (((P'.thickened θ hθ1).toPrismNDim.dilation r).carrier :
        Set (EuclideanSpace ℝ (Fin 3))))
    (k : Fin 3) {c₀ c₁ c₂ : ℝ}
    (h₀ : |inner ℝ ((P.thickened θ hθ1).basis k) ((P'.thickened θ hθ1).basis 0)| ≤ c₀)
    (h₁ : |inner ℝ ((P.thickened θ hθ1).basis k) ((P'.thickened θ hθ1).basis 1)| ≤ c₁)
    (h₂ : |inner ℝ ((P.thickened θ hθ1).basis k) ((P'.thickened θ hθ1).basis 2)| ≤ c₂) :
    |inner ℝ ((P.thickened θ hθ1).basis k) (x -ᵥ (P.thickened θ hθ1).center)|
      ≤ 2 * (r : ℝ) * ((θ : ℝ) * (b : ℝ) * c₀ + (b : ℝ) * c₁ + c₂)
        + ![(θ : ℝ) * (b : ℝ), (b : ℝ), 1] k := by
  obtain ⟨p, hpT, hpT'⟩ := exists_mem_inter_of_not_essentiallyDistinct P P' hnd
  obtain ⟨hpT0, hpT1, hpT2⟩ := abs_inner_thickened_le P hpT
  obtain ⟨hpT'0, hpT'1, hpT'2⟩ := abs_inner_thickened_le P' hpT'
  obtain ⟨hxQ0, hxQ1, hxQ2⟩ := abs_inner_dilation_thickened_le P' hx
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := NNReal.one_le_coe.2 hr
  have hθb : (0 : ℝ) ≤ (θ : ℝ) * (b : ℝ) := mul_nonneg θ.coe_nonneg b.coe_nonneg
  have hd₀ := mul_nonneg r.coe_nonneg hθb
  have hd₁ := mul_nonneg r.coe_nonneg b.coe_nonneg
  have hd₂ := mul_nonneg r.coe_nonneg zero_le_one
  have hown : |inner ℝ ((P.thickened θ hθ1).basis k) (p -ᵥ (P.thickened θ hθ1).center)|
      ≤ ![(θ : ℝ) * (b : ℝ), (b : ℝ), 1] k :=
    k.cases hpT0 (Fin.cases hpT1 (Fin.cases hpT2 fun i => i.elim0))
  -- Both the `x`-terms and the (`r`-inflated) `p`-terms give `r·(θb·c₀ + b·c₁ + c₂)`.
  exact (abs_inner_vsub_le_split _ x p _ (P'.thickened θ hθ1).center).trans
    ((add_le_add (add_le_add
      (abs_inner_le_of_frame_bounds _ _ _ hxQ0 hxQ1 hxQ2 h₀ h₁ h₂ hd₀ hd₁ hd₂)
      (abs_inner_le_of_frame_bounds _ _ _
        (hpT'0.trans (le_mul_of_one_le_left hθb hr1))
        (hpT'1.trans (le_mul_of_one_le_left b.coe_nonneg hr1))
        (hpT'2.trans (le_mul_of_one_le_left zero_le_one hr1))
        h₀ h₁ h₂ hd₀ hd₁ hd₂)) hown).trans_eq (by ring))

/-- Coordinate `0` (thin, half-width `θb`) of the one-way containment: a point of
`T'.dilation r` has `T`-frame thin coordinate at most `11·r·θ·b`.

Expanding `x -ᵥ T.center = (x -ᵥ T'.center) - (p -ᵥ T'.center) + (p -ᵥ T.center)` in `T'`'s frame,
the three `x`-terms contribute `r·θb·1 + r·b·(2θ) + r·1·(2θb) = 5rθb` (the last two coefficients are
the *swapped* frame bounds), the three `p`-terms contribute `5θb`, and the own-frame term `θb`. -/
theorem thickening_coord0_le
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} (hθ0 : 0 < θ) (hb0 : 0 < b)
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim))
    {r : ℝ≥0} (hr : 1 ≤ r) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (((P'.thickened θ hθ1).toPrismNDim.dilation r).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))) :
    |inner ℝ ((P.thickened θ hθ1).basis 0) (x -ᵥ (P.thickened θ hθ1).center)|
      ≤ 11 * (r : ℝ) * (θ : ℝ) * (b : ℝ) := by
  obtain ⟨hc1, hc2⟩ := thickening_frame_coeff_lt_of_not_essentiallyDistinct hθ1 hθ0 hb0 P' P
    (not_essentiallyDistinct_symm P P' hnd)
  have hθpos_real : 0 < (θ : ℝ) := by exact_mod_cast hθ0
  have hbpos_real : 0 < (b : ℝ) := by exact_mod_cast hb0
  have hr1_real : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  refine (thickening_coord_le_of_cross_bounds (c₀ := 1) (c₁ := 2 * (θ : ℝ))
    (c₂ := 2 * (θ : ℝ) * (b : ℝ)) P P' hnd hr hx 0 (abs_inner_basis_le_one _ _ 0 0)
    (by rw [real_inner_comm]; exact hc1.le) (by rw [real_inner_comm]; exact hc2.le)).trans ?_
  -- `10rθb + θb ≤ 11rθb` since `r ≥ 1`.
  simp only [Matrix.cons_val_zero]
  linarith only [mul_nonneg (mul_nonneg (sub_nonneg.2 hr1_real) hθpos_real.le) hbpos_real.le]

/-- Coordinate `1` (middle, half-width `b`) of the one-way containment: at most `9·r·b`.
The `x`-terms give `r·θb·1 + r·b·1 + r·1·(2b) ≤ 4rb` (using `θ ≤ 1` and the swapped in-plane bound
for the long direction), the `p`-terms `4b`, and the own-frame term `b`. -/
theorem thickening_coord1_le
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} (hθ0 : 0 < θ) (hb0 : 0 < b)
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim))
    {r : ℝ≥0} (hr : 1 ≤ r) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (((P'.thickened θ hθ1).toPrismNDim.dilation r).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))) :
    |inner ℝ ((P.thickened θ hθ1).basis 1) (x -ᵥ (P.thickened θ hθ1).center)|
      ≤ 9 * (r : ℝ) * (b : ℝ) := by
  have hc2 := (thickening_inPlane_coeff_lt_of_not_essentiallyDistinct hθ1 hθ0 hb0 P' P
    (not_essentiallyDistinct_symm P P' hnd)).le
  have hbpos_real : 0 < (b : ℝ) := by exact_mod_cast hb0
  have hθ1_real : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  have hr1_real : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  refine (thickening_coord_le_of_cross_bounds (c₀ := 1) (c₁ := 1) (c₂ := 2 * (b : ℝ))
    P P' hnd hr hx 1 (abs_inner_basis_le_one _ _ 1 0) (abs_inner_basis_le_one _ _ 1 1)
    (by rw [real_inner_comm]; exact hc2)).trans ?_
  -- `2rθb + 6rb + b ≤ 9rb` since `θ ≤ 1` and `r ≥ 1`.
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  linarith only [mul_nonneg (mul_nonneg (sub_nonneg.2 hθ1_real) hbpos_real.le) r.coe_nonneg,
    mul_nonneg (sub_nonneg.2 hr1_real) hbpos_real.le]

/-- Coordinate `2` (long, half-width `1`) of the one-way containment: at most `7·r`.
Here no frame bound is needed — Cauchy-Schwarz (`|⟪eⱼ, e'ₖ⟫| ≤ 1`) and `θb, b ≤ 1` already give
`3r` from the `x`-terms, `3` from the `p`-terms and `1` from the own-frame term. -/
theorem thickening_coord2_le
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} (hθ0 : 0 < θ) (hb0 : 0 < b)
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim))
    {r : ℝ≥0} (hr : 1 ≤ r) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (((P'.thickened θ hθ1).toPrismNDim.dilation r).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))) :
    |inner ℝ ((P.thickened θ hθ1).basis 2) (x -ᵥ (P.thickened θ hθ1).center)|
      ≤ 7 * (r : ℝ) := by
  have hθ0_real : 0 < (θ : ℝ) := by exact_mod_cast hθ0
  have hb0_real : 0 < (b : ℝ) := by exact_mod_cast hb0
  have hθ1_real : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  have hb1_real : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hr1_real : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hθb : (θ : ℝ) * (b : ℝ) ≤ 1 := mul_le_one₀ hθ1_real hb0_real.le hb1_real
  refine (thickening_coord_le_of_cross_bounds (c₀ := 1) (c₁ := 1) (c₂ := 1)
    P P' hnd hr hx 2 (abs_inner_basis_le_one _ _ 2 0) (abs_inner_basis_le_one _ _ 2 1)
    (abs_inner_basis_le_one _ _ 2 2)).trans ?_
  -- `2rθb + 2rb + 2r + 1 ≤ 7r` since `θb, b ≤ 1 ≤ r`.
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  linarith only [mul_nonneg (sub_nonneg.2 hθb) r.coe_nonneg,
    mul_nonneg (sub_nonneg.2 hb1_real) r.coe_nonneg, hr1_real, hθ0_real]

/-- The one-way containment assembled from the three coordinate estimates. -/
theorem thickening_dilation_subset_of_not_essentiallyDistinct
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} (hθ0 : 0 < θ) (hb0 : 0 < b)
    (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P'.thickened θ hθ1).toPrismNDim))
    {r : ℝ≥0} (hr : 1 ≤ r) :
    (((P'.thickened θ hθ1).toPrismNDim.dilation r).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) ⊆
      ((P.thickened θ hθ1).toPrismNDim.dilation (256 * r)).carrier := by
  intro x hx
  -- The three coordinate lemmas.
  have hx0 := thickening_coord0_le hθ0 hb0 P P' hnd hr hx
  have hx1 := thickening_coord1_le hθ0 hb0 P P' hnd hr hx
  have hx2 := thickening_coord2_le hθ0 hb0 P P' hnd hr hx
  rw [PrismNDim.mem_carrier_iff]
  intro k
  rw [OrthonormalBasis.repr_apply_apply, PrismNDim.dilation_basis, PrismNDim.dilation_center,
    PrismNDim.dilation_thicknesses, Prism3D.thicknesses_eq (P.thickened θ hθ1)]
  push_cast
  -- `11rθb, 9rb, 7r` are all below `256r` times the corresponding half-width.
  fin_cases k <;>
    simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, NNReal.coe_mul, NNReal.coe_one,
      mul_one] <;>
    linarith only [hx0, hx1, hx2, mul_nonneg (mul_nonneg r.coe_nonneg θ.coe_nonneg) b.coe_nonneg,
      mul_nonneg r.coe_nonneg b.coe_nonneg, r.coe_nonneg]

/-- **Two-sided dilation comparability of non-distinct equal-scale thickenings**, in *scale-aware*
form (`lem:thickenedReprFixedScaleComparable`). There is an absolute `Ceq ≥ 1`, quantified before
the configuration, such that any two equal-scale `θb × b × 1` prisms `T, T'` (standard
`θ`-thickenings of `a × b × 1` planks) which are *not* essentially distinct satisfy,
**for every** `r ≥ 1`,
`T'.dilation r ⊆ T.dilation (Ceq * r)` and symmetrically.

The scale-awareness (the `∀ r`) is essential and is *not* a convenience: for non-concentric prisms
`A ⊆ B` never implies `A.dilation c ⊆ B.dilation c`, so a plain two-sided containment cannot be
chained through later dilations. The coordinate proof gives the `∀ r` form for free, because the
centre offset contributes `O(1)` half-widths while the frame mismatch contributes `O(r)` of them.

Proof route (see the blueprint note retracting the old per-axis chain): the short-normal angle is
bounded at scale `θ` by `Prism3D.volume_inter_le` (`|T ∩ T'| ≤ 32 (θb)² / φ` against
`|T ∩ T'| > 4θb²` from non-distinctness, giving `φ < 8θ`); the *in-plane* rotation is bounded at
scale `b`, not `θb`; and the centre offset is read off from any point of the (positive-volume, hence
nonempty) intersection. -/
public theorem equalScaleThickening_twoSidedDilation :
    ∃ Ceq : ℝ≥0, 1 ≤ Ceq ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} (hθ1 : θ ≤ 1)
        (_hθ0 : 0 < θ) (_hb0 : 0 < b) (P P' : Plank a b hab hb1),
        ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
            ((P'.thickened θ hθ1).toPrismNDim) →
        ∀ r : ℝ≥0, 1 ≤ r →
          ((((P'.thickened θ hθ1).toPrismNDim.dilation r).carrier :
              Set (EuclideanSpace ℝ (Fin 3))) ⊆
              ((P.thickened θ hθ1).toPrismNDim.dilation (Ceq * r)).carrier ∧
            ((((P.thickened θ hθ1).toPrismNDim.dilation r).carrier :
              Set (EuclideanSpace ℝ (Fin 3))) ⊆
              ((P'.thickened θ hθ1).toPrismNDim.dilation (Ceq * r)).carrier)) := by
  refine ⟨256, by norm_num, ?_⟩
  intro a b hab hb1 θ hθ1 _hθ0 _hb0 P P' hnd r hr
  exact ⟨thickening_dilation_subset_of_not_essentiallyDistinct _hθ0 _hb0 P P' hnd hr,
    thickening_dilation_subset_of_not_essentiallyDistinct _hθ0 _hb0 P' P
      (not_essentiallyDistinct_symm P P' hnd) hr⟩

/-! ### Plank-level corollaries: a plank is its own thickening at `θ = a/b`

`Plank a b = Prism3D a b 1` and `P.thickened θ = Prism3D (θ·b) b 1`, so at `θ = a/b` (which is
`≤ 1` because `a ≤ b`) the two coincide.  Every equal-scale thickening result therefore specialises
to planks *for free*, with `θ` replaced by `a/b`.  This is the plank analogue of the thickening
comparability that the fibre-packing argument needs on its `¬ED` side. -/

/-- At `θ = a/b` the thickening of a plank has the same carrier as the plank itself. -/
public theorem plank_thickened_self_carrier {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (hb0 : 0 < b) (hab1 : a / b ≤ 1) (P : Plank a b hab hb1) :
    ((P.thickened (a / b) hab1).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  ext x
  rw [(P.thickened (a / b) hab1).mem_carrier_iff, P.mem_carrier_iff]
  refine forall_congr' fun j => ?_
  rw [show ((P.thickened (a / b) hab1).thicknesses j : ℝ) = (P.thicknesses j : ℝ) from by
    rw [(P.thickened (a / b) hab1).thicknesses_eq, P.thicknesses_eq,
      div_mul_cancel₀ a hb0.ne']]
  rfl

/-- At `θ = a/b` the thickening of a plank has the same dilated carriers as the plank itself. -/
public theorem plank_thickened_self_dilation_carrier {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (hb0 : 0 < b) (hab1 : a / b ≤ 1) (P : Plank a b hab hb1) (r : ℝ≥0) :
    (((P.thickened (a / b) hab1).toPrismNDim.dilation r).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))
      = (P.toPrismNDim.dilation r).carrier := by
  have hthk : (P.thickened (a / b) hab1).toPrismNDim.thicknesses = P.toPrismNDim.thicknesses := by
    rw [(P.thickened (a / b) hab1).thicknesses_eq, P.thicknesses_eq, div_mul_cancel₀ a hb0.ne']
  ext x
  rw [((P.thickened (a / b) hab1).toPrismNDim.dilation r).mem_carrier_iff,
    (P.toPrismNDim.dilation r).mem_carrier_iff]
  refine forall_congr' fun i => ?_
  rw [show ((P.thickened (a / b) hab1).toPrismNDim.dilation r).thicknesses i
      = (P.toPrismNDim.dilation r).thicknesses i from by
    rw [PrismNDim.dilation_thicknesses, PrismNDim.dilation_thicknesses, hthk]]
  rfl

/-- **Essentially indistinct planks have a small plane angle.**  If two `a × b × 1` planks fail
to be essentially distinct their long planes meet at angle `< 8 a/b`.  Instance of
`thickening_angle_lt_of_not_essentiallyDistinct` at `θ = a/b`; the angle is unchanged because
thickening preserves the frame. -/
theorem plank_angle_lt_of_not_essentiallyDistinct {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha0 : 0 < a) (hb0 : 0 < b) (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct P.toPrismNDim P'.toPrismNDim) :
    Prism3D.angle P P' < 8 * ((a / b : ℝ≥0) : ℝ) := by
  have hab1 : a / b ≤ 1 := (div_le_one hb0).2 hab
  have hnd' : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened (a / b) hab1).toPrismNDim)
      ((P'.thickened (a / b) hab1).toPrismNDim) := by
    unfold PrismNDim.IsEssentiallyDistinct at hnd ⊢
    rwa [plank_thickened_self_carrier hb0 hab1 P, plank_thickened_self_carrier hb0 hab1 P']
  -- The frame — hence the short-normal angle — is unchanged by thickening, so this is `rfl`.
  exact thickening_angle_lt_of_not_essentiallyDistinct hab1 (div_pos ha0 hb0) hb0 P P' hnd'

/-- **Two-sided scale-aware comparability of essentially indistinct planks.**  If two `a × b × 1`
planks fail to be essentially distinct then each `r`-dilation of one sits inside the `256r`-dilation
of the other, for every `r ≥ 1`.  Instance of `equalScaleThickening_twoSidedDilation` at
`θ = a/b`.

This is the plank-level `¬ED ⟹ comparable` statement.  Its contrapositive — pairwise essentially
distinct planks are pose-separated — is the input the fibre-packing bound
(`lem:thickenedReprPhiPackingBound`) needs; see the run notes for why the *converse* direction
("close poses ⟹ ¬ED"), which is what a counting argument consumes, is a separate development at
three distinct scales. -/
theorem plank_twoSidedDilation_of_not_essentiallyDistinct {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha0 : 0 < a) (hb0 : 0 < b) (P P' : Plank a b hab hb1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct P.toPrismNDim P'.toPrismNDim)
    (r : ℝ≥0) (hr : 1 ≤ r) :
    ((P'.toPrismNDim.dilation r).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (P.toPrismNDim.dilation (256 * r)).carrier ∧
      ((P.toPrismNDim.dilation r).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (P'.toPrismNDim.dilation (256 * r)).carrier := by
  have hab1 : a / b ≤ 1 := (div_le_one hb0).2 hab
  have hnd' : ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened (a / b) hab1).toPrismNDim)
      ((P'.thickened (a / b) hab1).toPrismNDim) := fun hED => hnd <| by
    simpa [PrismNDim.IsEssentiallyDistinct, _root_.IsEssentiallyDistinct,
      plank_thickened_self_carrier hb0 hab1 P, plank_thickened_self_carrier hb0 hab1 P'] using hED
  have hδ0 : 0 < a / b := div_pos ha0 hb0
  have hfwd := thickening_dilation_subset_of_not_essentiallyDistinct hδ0 hb0 P P' hnd' hr
  have hbwd := thickening_dilation_subset_of_not_essentiallyDistinct hδ0 hb0 P' P
    (not_essentiallyDistinct_symm P P' hnd') hr
  rw [plank_thickened_self_dilation_carrier hb0 hab1 P' r,
    plank_thickened_self_dilation_carrier hb0 hab1 P (256 * r)] at hfwd
  rw [plank_thickened_self_dilation_carrier hb0 hab1 P r,
    plank_thickened_self_dilation_carrier hb0 hab1 P' (256 * r)] at hbwd
  exact ⟨hfwd, hbwd⟩

/-- The concentric `q`-shrunk copy of a plank, as a genuine `Prism3D`.  Used as the common
sub-prism witnessing failure of essential distinctness for planks with close poses. -/
def shrunk {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (P : Plank a b hab hb1) (q : ℝ≥0) :
    Prism3D (q * a) (q * b) (q * 1) (mul_le_mul_right hab q) (mul_le_mul_right hb1 q) where
  toPrismNDim := PrismNDim.mk' P.center P.basis ![q * a, q * b, q * 1]
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

@[simp] theorem shrunk_center {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : Plank a b hab hb1) (q : ℝ≥0) : (P.shrunk q).center = P.center := rfl

@[simp] theorem shrunk_basis {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : Plank a b hab hb1) (q : ℝ≥0) : (P.shrunk q).basis = P.basis := rfl

/-- Coordinate description of the shrunk prism, in terms of inner products with `P`'s frame. -/
theorem mem_shrunk_iff {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : Plank a b hab hb1) (q : ℝ≥0) (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ ((P.shrunk q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ↔ ∀ j : Fin 3, |inner ℝ (P.basis j) (x -ᵥ P.center)|
          ≤ (q : ℝ) * ((![a, b, 1] j : ℝ≥0) : ℝ) := by
  rw [(P.shrunk q).mem_carrier_iff]
  refine forall_congr' fun j => ?_
  rw [(P.shrunk q).thicknesses_eq, OrthonormalBasis.repr_apply_apply, shrunk_basis, shrunk_center,
    show ((![q * a, q * b, q * 1] j : ℝ≥0) : ℝ) = (q : ℝ) * ((![a, b, 1] j : ℝ≥0) : ℝ) from by
      fin_cases j <;> simp]

/-- Coordinate description of a plank's own carrier. -/
theorem mem_plank_iff {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : Plank a b hab hb1) (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ↔ ∀ j : Fin 3, |inner ℝ (P.basis j) (x -ᵥ P.center)|
          ≤ ((![a, b, 1] j : ℝ≥0) : ℝ) := by
  rw [P.mem_carrier_iff]
  refine forall_congr' fun j => ?_
  rw [P.thicknesses_eq, OrthonormalBasis.repr_apply_apply]

/-- **The pose-closeness coordinate estimate** (the analytic core of
`plank_not_essentiallyDistinct_of_pose_close`).  If a displacement `v` is `⅞`-inside `P`'s box and
the two poses are close in the anisotropic sense, then `v` shifted by the centre offset is inside
`P'`'s box.

Diagonal `⅞wₖ` + two off-diagonal `wₖ/32` + centre `wₖ/16` = `wₖ` exactly. -/
lemma plank_pose_close_coord {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P P' : Plank a b hab hb1) (hfrm : ∀ j k : Fin 3, j ≠ k →
      ((![a, b, 1] j : ℝ≥0) : ℝ) * |inner ℝ (P.basis j) (P'.basis k)|
        ≤ ((![a, b, 1] k : ℝ≥0) : ℝ) / 32)
    (hcen : ∀ k : Fin 3,
      |inner ℝ (P'.basis k) (P.center -ᵥ P'.center)| ≤ ((![a, b, 1] k : ℝ≥0) : ℝ) / 16)
    (v : EuclideanSpace ℝ (Fin 3))
    (hv : ∀ j : Fin 3, |inner ℝ (P.basis j) v| ≤ (7/8 : ℝ) * ((![a, b, 1] j : ℝ≥0) : ℝ))
    (k : Fin 3) :
    |inner ℝ (P'.basis k) (v + (P.center -ᵥ P'.center))| ≤ ((![a, b, 1] k : ℝ≥0) : ℝ) := by
  -- the sum of a diagonal value and two off-diagonal ones, over `Fin 3`
  have hsum : ∀ (A B : ℝ) (i : Fin 3), (if (0 : Fin 3) = i then A else B)
      + (if (1 : Fin 3) = i then A else B) + (if (2 : Fin 3) = i then A else B) = A + 2 * B := by
    intro A B i
    match i with
    | 0 => rw [if_pos rfl, if_neg (by decide), if_neg (by decide)]; ring
    | 1 => rw [if_neg (by decide), if_pos rfl, if_neg (by decide)]; ring
    | 2 => rw [if_neg (by decide), if_neg (by decide), if_pos rfl]; ring
  -- termwise bound in the expansion of `v` in `P`'s frame
  have hbound : ∀ j : Fin 3, |inner ℝ (P.basis j) v| * |inner ℝ (P'.basis k) (P.basis j)|
      ≤ (if j = k then (7/8 : ℝ) * ((![a, b, 1] k : ℝ≥0) : ℝ)
          else ((![a, b, 1] k : ℝ≥0) : ℝ) / 32) := fun j => by
    by_cases hjk : j = k
    · rw [if_pos hjk, ← hjk]
      exact (mul_le_of_le_one_right (abs_nonneg _)
        (abs_inner_basis_le_one P'.basis P.basis _ _)).trans (hv j)
    · rw [if_neg hjk, real_inner_comm (P.basis j) (P'.basis k)]
      exact (mul_le_mul_of_nonneg_right ((hv j).trans
        (mul_le_of_le_one_left (NNReal.coe_nonneg _) (by norm_num))) (abs_nonneg _)).trans
          (hfrm j k hjk)
  -- the frame expansion, summed, plus the centre offset
  have key : |inner ℝ (P'.basis k) v| ≤ (7/8 : ℝ) * ((![a, b, 1] k : ℝ≥0) : ℝ)
      + 2 * (((![a, b, 1] k : ℝ≥0) : ℝ) / 32) :=
    (abs_inner_le_sum_frame P.basis (P'.basis k) v).trans
      ((add_le_add (add_le_add (hbound 0) (hbound 1)) (hbound 2)).trans_eq (hsum _ _ k))
  rw [inner_add_right]
  exact (abs_add_le _ _).trans ((add_le_add key (hcen k)).trans (le_of_eq (by ring)))

/-- **Planks with close poses are not essentially distinct** (three distinct scales `a ≤ b ≤ 1`).

If, measured in the *anisotropic* way appropriate to the plank half-widths `w = (a, b, 1)`,
* every off-diagonal frame entry satisfies `wⱼ·|⟪eⱼ, e'ₖ⟫| ≤ wₖ/32`, and
* every centre offset satisfies `|⟪e'ₖ, c − c'⟫| ≤ wₖ/16`,

then `|P ∩ P'| > ½·max(|P|,|P'|)`, i.e. `P` and `P'` are *not* essentially distinct.

The witness is the concentric `⅞`-shrunk prism `R` of `P`: it lies in `P` trivially, and in `P'`
because expanding `⟪e'ₖ, x − c'⟫` in `P`'s frame contributes `⅞wₖ` on the diagonal, at most
`2·wₖ/32 = wₖ/16` off the diagonal and at most `wₖ/16` from the centre offset, totalling exactly
`wₖ`.  Since `|R| = (7/8)³·8ab = (343/512)·8ab > ½·8ab = ½|P|`, essential distinctness fails.

This is the direction a *counting* argument consumes (its contrapositive says pairwise essentially
distinct planks are pose-separated), and it is the plank analogue of
`not_essentiallyDistinct_of_ref_coords_close`, which is stated only for slabs `θ × 1 × 1` (two equal
scales) and so does not apply here.  Together with a confinement statement it gives the fibre
packing bound `lem:thickenedReprPhiPackingBound`. -/
public theorem plank_not_essentiallyDistinct_of_pose_close
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha0 : 0 < a) (hb0 : 0 < b) (P P' : Plank a b hab hb1)
    (hfrm : ∀ j k : Fin 3, j ≠ k →
      ((![a, b, 1] j : ℝ≥0) : ℝ) * |inner ℝ (P.basis j) (P'.basis k)|
        ≤ ((![a, b, 1] k : ℝ≥0) : ℝ) / 32)
    (hcen : ∀ k : Fin 3,
      |inner ℝ (P'.basis k) (P.center -ᵥ P'.center)| ≤ ((![a, b, 1] k : ℝ≥0) : ℝ) / 16) :
    ¬ PrismNDim.IsEssentiallyDistinct P.toPrismNDim P'.toPrismNDim := by
  set R := P.shrunk (7/8 : ℝ≥0)
  have hq : ((7/8 : ℝ≥0) : ℝ) = 7/8 := by norm_num
  -- the shrunk prism lies in both planks
  have hRP : (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ P.carrier := fun x hx =>
    (mem_plank_iff P x).2 fun j => ((mem_shrunk_iff P (7/8 : ℝ≥0) x).1 hx j).trans
      (mul_le_of_le_one_left (NNReal.coe_nonneg _) (by rw [hq]; norm_num))
  have hRP' : (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ P'.carrier := fun x hx =>
    (mem_plank_iff P' x).2 fun k => by
      rw [← vsub_add_vsub_cancel x P.center P'.center]
      exact plank_pose_close_coord P P' hfrm hcen (x -ᵥ P.center)
        (fun j => hq ▸ (mem_shrunk_iff P (7/8 : ℝ≥0) x).1 hx j) k
  -- volumes, all written as coercions of `ℝ≥0` so the final step is `ℝ≥0` arithmetic
  have hvol : ∀ Q : Plank a b hab hb1,
      volume (Q.toPrismNDim.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = ((8 * a * b : ℝ≥0) : ENNReal) := fun Q => by
    rw [Prism3D.volume_carrier Q, ENNReal.coe_one, mul_one, ENNReal.coe_mul, ENNReal.coe_mul,
      ENNReal.coe_ofNat]
  have hvolR : volume (R.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((343/512 * (8 * a * b) : ℝ≥0) : ENNReal) := by
    rw [Prism3D.volume_carrier R, ← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
      ← ENNReal.coe_mul]
    exact congrArg _ (NNReal.eq (by push_cast; ring))
  -- conclude: `R ⊆ P ∩ P'` has more than half the volume
  intro hED
  simp only [PrismNDim.IsEssentiallyDistinct, _root_.IsEssentiallyDistinct, hvol P, hvol P',
    max_self] at hED
  have hchain := (measure_mono (Set.subset_inter hRP hRP')).trans hED
  rw [hvolR, show (1/2 : ENNReal) = ((1/2 : ℝ≥0) : ENNReal) from by norm_num, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe] at hchain
  exact absurd (le_of_mul_le_mul_right hchain
    (mul_pos (mul_pos (show (0 : ℝ≥0) < 8 by norm_num) ha0) hb0))
    (by rw [← NNReal.coe_le_coe]; norm_num)

end Plank

end

end
