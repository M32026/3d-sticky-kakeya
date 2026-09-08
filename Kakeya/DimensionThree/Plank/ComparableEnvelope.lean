/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.CThickening
public import Kakeya.Homothety
public import Kakeya.Thickness.Homothety
public import Kakeya.Thickness.OuterPrism
public import Kakeya.DimensionThree.Plank
public import Kakeya.DimensionThree.Plank.Geometry

/-!
# Exact plank envelopes for bodies with comparable plank dimensions

The public statement of Proposition 6.6(A) describes its actual factor bodies by their three
affine thicknesses.  GWZ Lemma 6.4, however, consumes exact `Plank` carriers.  This file supplies
the honest bridge: first shrink the scale-collar by the fixed homothety of ratio `(8 * C)⁻¹`, then
enclose the result in the limiting outer prism and reverse its axes.  The factor `C⁻¹` ensures that
the exact envelope has the original dimensions `a × b × 1`, so the analytic `a / b` gain is
unchanged.  The additional factor `1 / 8` keeps the envelope in the fixed Section 6 window.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

namespace comparablePlankEnvelope

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ### An unscaled envelope for the inner fibre

The outer application of Lemma 6.4 uses the common homothetic envelope below, since multiplicity
of the *whole* outer family is invariant under one common homothety.  The inner application has a
different need: its normalisation theorem only asks for an exact plank containing one actual
factor body, and does not ask that input plank to lie in the fixed window.  For that purpose no
homothety is necessary. -/

/-- The thin half-width of the unscaled envelope. -/
def bodyThin (C a : NNReal) : NNReal := C * a

/-- The wide half-width of the unscaled envelope, capped at the unit longitudinal width. -/
def bodyWide (C b : NNReal) : NNReal := min (C * b) 1

theorem bodyThin_le_bodyWide {C a b : NNReal} (hab : a ≤ b) (hCa : C * a ≤ 1) :
    bodyThin C a ≤ bodyWide C b := by
  rw [bodyThin, bodyWide, le_min_iff]
  exact ⟨mul_le_mul_left' hab C, hCa⟩

theorem bodyWide_le_one (C b : NNReal) : bodyWide C b ≤ 1 := by
  exact min_le_right _ _

theorem bodyWide_le_mul (C b : NNReal) : bodyWide C b ≤ C * b := by
  exact min_le_left _ _

theorem le_bodyWide {C b : NNReal} (hC : 1 ≤ C) (hb1 : b ≤ 1) :
    b ≤ bodyWide C b := by
  rw [bodyWide, le_min_iff]
  exact ⟨by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC b.2, hb1⟩

/-- The limiting outer prism of an actual (unscaled) factor body. -/
def bodyRaw (K : ConvexSpaceBody E3) : PrismNDim 3 E3 E3 :=
  outerPrism (by simp) K.isCompact' K.nonempty'

/-- Exact plank containing an actual factor body with comparable plank dimensions. -/
def bodyPlank (C a b : NNReal) (hab : a ≤ b) (hCa : C * a ≤ 1)
    (K : ConvexSpaceBody E3) :
    Plank (bodyThin C a) (bodyWide C b) (bodyThin_le_bodyWide hab hCa)
      (bodyWide_le_one C b) where
  toPrismNDim := PrismNDim.mk' (bodyRaw K).center
    ((bodyRaw K).basis.reindex Fin.revPerm)
    ![bodyThin C a, bodyWide C b, 1]
  thicknesses_eq := by
    simpa using PrismNDim.thicknesses_mk' (bodyRaw K).center
      ((bodyRaw K).basis.reindex Fin.revPerm) ![bodyThin C a, bodyWide C b, 1]

private theorem thickness_le_of_ethickness_le {K : ConvexSpaceBody E3} {k : ℕ} {r : NNReal}
    (h : Metric.ethickness ℝ K.carrier k ≤ (r : ENNReal)) :
    Metric.thickness ℝ K.carrier k ≤ r := by
  rw [← Metric.toReal_ethickness K.isCompact'.isBounded k]
  simpa using ENNReal.toReal_mono ENNReal.coe_ne_top h

/-- The actual body lies in its unscaled exact envelope.

The long width comes from the ambient unit ball, while the other two widths come from the upper
halves of `IsPlankOfDimensions`.  The cap in `bodyWide` is harmless because both available upper
bounds hold. -/
theorem body_le_bodyPlank {C a b : NNReal} (hab : a ≤ b)
    (hCa : C * a ≤ 1) {K : ConvexSpaceBody E3}
    (hKone : Metric.ethickness ℝ K.carrier 1 ≤ (C : ENNReal) * b)
    (hKtwo : Metric.ethickness ℝ K.carrier 2 ≤ (C : ENNReal) * a)
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall) :
    K ≤ (bodyPlank C a b hab hCa K).toConvexSpaceBody := by
  have hball : K.carrier ⊆ Metric.closedBall (0 : E3) 1 := by
    exact hKball
  have hzero : Metric.thickness ℝ K.carrier 0 ≤ 1 :=
    Metric.thickness_le_of_subset_closedBall hball (by norm_num) 0
  have honeC : Metric.thickness ℝ K.carrier 1 ≤ C * b :=
    thickness_le_of_ethickness_le hKone
  have hone1 : Metric.thickness ℝ K.carrier 1 ≤ 1 :=
    Metric.thickness_le_of_subset_closedBall hball (by norm_num) 1
  have hone : Metric.thickness ℝ K.carrier 1 ≤ bodyWide C b := by
    rw [bodyWide, NNReal.coe_min, le_min_iff]
    exact ⟨honeC, hone1⟩
  have htwo : Metric.thickness ℝ K.carrier 2 ≤ bodyThin C a := by
    exact thickness_le_of_ethickness_le hKtwo
  have hself : K.carrier ⊆ (bodyRaw K).carrier := by
    exact outerPrism.self_subset (by simp : Module.finrank ℝ E3 = 3)
      K.isCompact' K.nonempty'
  refine hself.trans ?_
  intro x hx
  change x ∈ (bodyPlank C a b hab hCa K).carrier
  rw [(bodyPlank C a b hab hCa K).mem_carrier_iff]
  intro i
  have hraw := ((bodyRaw K).mem_carrier_iff x).mp hx (Fin.revPerm.symm i)
  change
    |((bodyRaw K).basis.reindex Fin.revPerm).repr (x - (bodyRaw K).center) i| ≤
      (![bodyThin C a, bodyWide C b, 1] : Fin 3 → NNReal) i
  rw [OrthonormalBasis.repr_reindex]
  fin_cases i <;> simp [bodyRaw, outerPrism.thicknesses_eq] at hraw ⊢
  · exact hraw.trans htwo
  · exact hraw.trans hone
  · exact hraw.trans hzero

/-- Fixed homothety ratio used to turn `C`-comparable dimensions into the exact dimensions
`a × b × 1`. -/
def shrink (C : NNReal) : NNReal := (8 * C)⁻¹

theorem shrink_pos {C : NNReal} (hC : 1 ≤ C) : 0 < shrink C := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  exact inv_pos.mpr (mul_pos (by norm_num) hCpos)

theorem shrink_coe_ne_zero {C : NNReal} (hC : 1 ≤ C) : (shrink C : ℝ) ≠ 0 := by
  exact_mod_cast (shrink_pos hC).ne'

theorem shrink_le_eighth {C : NNReal} (hC : 1 ≤ C) : shrink C ≤ 1 / 8 := by
  have h8 : (8 : NNReal) ≤ 8 * C := by simpa using mul_le_mul_left' hC 8
  rw [shrink]
  simpa only [div_eq_mul_inv, one_mul] using
    ((inv_le_inv₀ (by positivity : (0 : NNReal) < 8 * C) (by norm_num : (0 : NNReal) < 8)).2 h8)

/-- The real-valued shortest scale, packaged as a nonnegative radius. -/
noncomputable def scaleRadius (K : ConvexSpaceBody E3) : NNReal :=
  ⟨K.scale, Metric.thickness_nonneg K.carrier _⟩

@[simp]
theorem coe_scaleRadius (K : ConvexSpaceBody E3) : (scaleRadius K : ℝ) = K.scale := rfl

/-- The scale-collar, shrunk by the fixed factor `(8 * C)⁻¹`. -/
def scaledCollar (C : NNReal) (K : ConvexSpaceBody E3) : ConvexSpaceBody E3 :=
  (K.cthickening (scaleRadius K : ℝ)).homothety 0 (shrink C : ℝ)

/-- The fixed shrink puts the scale-collar of a body from the unit ball into `B(0,1/4)`. -/
theorem scaledCollar_subset_closedBall_quarter {C : NNReal} (hC : 1 ≤ C)
    {K : ConvexSpaceBody E3}
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall) :
    (scaledCollar C K).carrier ⊆ Metric.closedBall 0 (1 / 4 : ℝ) := by
  have hsub : K.carrier ⊆ Metric.closedBall (0 : E3) (1 : ℝ) := by
    simpa only [ConvexSpaceBody.closedUnitBall_carrier] using
      (show K.carrier ⊆ ConvexSpaceBody.closedUnitBall.carrier from hKball)
  have hscale : K.scale ≤ 1 :=
    Metric.thickness_le_of_subset_closedBall hsub (by norm_num) _
  have hcollar : Metric.cthickening (scaleRadius K : ℝ) K.carrier ⊆
      Metric.closedBall (0 : E3) 2 := by
    calc
      Metric.cthickening (scaleRadius K : ℝ) K.carrier ⊆
          Metric.cthickening (scaleRadius K : ℝ) (Metric.closedBall (0 : E3) 1) :=
        Metric.cthickening_subset_of_subset _ hsub
      _ ⊆ Metric.cthickening 1 (Metric.closedBall (0 : E3) 1) :=
        Metric.cthickening_mono (by simpa using hscale) _
      _ = Metric.closedBall (0 : E3) 2 := by
        rw [cthickening_closedBall (by norm_num : (0 : ℝ) ≤ 1)
          (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num
  intro y hy
  change y ∈ AffineMap.homothety (0 : E3) (shrink C : ℝ) ''
    Metric.cthickening (scaleRadius K : ℝ) K.carrier at hy
  rcases hy with ⟨z, hz, rfl⟩
  have hz' : dist z (0 : E3) ≤ 2 := Metric.mem_closedBall.mp (hcollar hz)
  have hzNorm : ‖z‖ ≤ 2 := by simpa [dist_eq_norm] using hz'
  rw [Metric.mem_closedBall]
  calc
    dist (AffineMap.homothety (0 : E3) (shrink C : ℝ) z) 0 = (shrink C : ℝ) * ‖z‖ := by
      simp [AffineMap.homothety_apply, dist_eq_norm, norm_smul]
    _ ≤ 1 / 4 := by
      have hs : (shrink C : ℝ) ≤ 1 / 8 := by exact_mod_cast shrink_le_eighth hC
      nlinarith [norm_nonneg z, (shrink C).2]

/-- The limiting outer prism of the shrunk scale-collar. -/
def raw (C : NNReal) (K : ConvexSpaceBody E3) : PrismNDim 3 E3 E3 :=
  outerPrism (by simp) (scaledCollar C K).isCompact' (scaledCollar C K).nonempty'

/-- Shrinking the scale-collar by `1 / 8` shrinks each affine thickness by at most that factor. -/
theorem ethickness_scaledCollar_le (C : NNReal) (K : ConvexSpaceBody E3) (k : ℕ) :
    Metric.ethickness ℝ (scaledCollar C K).carrier k ≤
      (shrink C : ENNReal) *
        Metric.ethickness ℝ (K.cthickening (scaleRadius K : ℝ)).carrier k := by
  change Metric.ethickness ℝ
      (AffineMap.homothety 0 (shrink C : ℝ) ''
        (K.cthickening (scaleRadius K : ℝ)).carrier) k ≤ _
  simpa using
    (Metric.ethickness_homothety_image_le (0 : E3) (shrink C : ℝ)
      (K.cthickening (scaleRadius K : ℝ)).carrier k)

private theorem shrink_mul_two_mul_le {C x y : ENNReal} (hC : 1 ≤ C) (hCtop : C ≠ ⊤)
    (hx : x ≤ C * y) : ((8 * C)⁻¹) * (2 * x) ≤ y := by
  calc
    (8 * C)⁻¹ * (2 * x) ≤ (8 * C)⁻¹ * (2 * (C * y)) := by gcongr
    _ = (1 / 4) * y := by
      rw [ENNReal.mul_inv (Or.inl (by norm_num : (8 : ENNReal) ≠ 0))
        (Or.inl (by norm_num : (8 : ENNReal) ≠ ⊤))]
      calc
        8⁻¹ * C⁻¹ * (2 * (C * y)) = (8⁻¹ * 2) * (C⁻¹ * C) * y := by ac_rfl
        _ = (1 / 4) * y := by
          rw [ENNReal.inv_mul_cancel (by positivity : C ≠ 0) hCtop, mul_one]
          congr 1
          calc
            (8 : ENNReal)⁻¹ * 2 = (2 * 4 : ENNReal)⁻¹ * 2 := by norm_num
            _ = (2⁻¹ * 4⁻¹) * 2 := by
              rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
                (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤))]
            _ = (2⁻¹ * 2) * 4⁻¹ := by ac_rfl
            _ = 4⁻¹ := by
              rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
            _ = 1 / 4 := by simp [div_eq_mul_inv]
    _ ≤ y := by
      calc
        (1 / 4) * y ≤ 1 * y := by gcongr; norm_num
        _ = y := one_mul y

/-- The three upper thickness bounds needed by the exact common envelope.  Rank zero uses the
ambient unit-ball hypothesis; ranks one and two use the corresponding plank-dimension bounds. -/
theorem ethickness_scaledCollar_bounds {C a b : NNReal} {K : ConvexSpaceBody E3}
    (hC : 1 ≤ C)
    (hKone : Metric.ethickness ℝ K.carrier 1 ≤ (C : ENNReal) * b)
    (hKtwo : Metric.ethickness ℝ K.carrier 2 ≤ (C : ENNReal) * a)
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall) :
    Metric.ethickness ℝ (scaledCollar C K).carrier 0 ≤ 1 ∧
      Metric.ethickness ℝ (scaledCollar C K).carrier 1 ≤ b ∧
      Metric.ethickness ℝ (scaledCollar C K).carrier 2 ≤ a := by
  have hcollar : ∀ k : ℕ,
      Metric.ethickness ℝ (K.cthickening (scaleRadius K : ℝ)).carrier k ≤
        2 * Metric.ethickness ℝ K.carrier k := by
    intro k
    simpa [Pi.smul_apply, two_nsmul, two_mul] using
      (ConvexSpaceBody.ethickness_cthickening_le_two K (scaleRadius K) (by simp) k)
  have hzero : Metric.ethickness ℝ K.carrier 0 ≤ 1 := by
    have hsub : K.carrier ⊆ Metric.closedBall (0 : E3) (1 : ℝ) := by
      simpa only [ConvexSpaceBody.closedUnitBall_carrier] using
        (show K.carrier ⊆ ConvexSpaceBody.closedUnitBall.carrier from hKball)
    simpa using
      (Metric.ethickness_le_of_subset_closedBall (𝕜 := ℝ) (x := (0 : E3)) (1 : NNReal)
        hsub 0)
  refine ⟨?_, ?_, ?_⟩
  · calc
      Metric.ethickness ℝ (scaledCollar C K).carrier 0
          ≤ (shrink C : ENNReal) *
              Metric.ethickness ℝ (K.cthickening (scaleRadius K : ℝ)).carrier 0 :=
            ethickness_scaledCollar_le C K 0
      _ ≤ (shrink C : ENNReal) * (2 * Metric.ethickness ℝ K.carrier 0) := by
        gcongr
        exact hcollar 0
      _ ≤ Metric.ethickness ℝ K.carrier 0 := by
        have hs : (shrink C : ENNReal) ≤ 1 / 2 := by
          exact (ENNReal.coe_le_coe.mpr (shrink_le_eighth hC)).trans (by norm_num)
        calc
          (shrink C : ENNReal) * (2 * Metric.ethickness ℝ K.carrier 0)
              ≤ (1 / 2) * (2 * Metric.ethickness ℝ K.carrier 0) := by gcongr
          _ = Metric.ethickness ℝ K.carrier 0 := by
            have hhalf : (1 / 2 : ENNReal) * 2 = 1 := by
              simp only [div_eq_mul_inv, one_mul]
              exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
            rw [← mul_assoc, hhalf, one_mul]
      _ ≤ 1 := hzero
  · calc
      Metric.ethickness ℝ (scaledCollar C K).carrier 1
          ≤ (shrink C : ENNReal) *
              Metric.ethickness ℝ (K.cthickening (scaleRadius K : ℝ)).carrier 1 :=
            ethickness_scaledCollar_le C K 1
      _ ≤ (shrink C : ENNReal) * (2 * Metric.ethickness ℝ K.carrier 1) := by
        gcongr
        exact hcollar 1
      _ ≤ b := by
        have hshrink : (shrink C : ENNReal) = (8 * (C : ENNReal))⁻¹ := by
          rw [shrink, ENNReal.coe_inv (by positivity : 8 * C ≠ 0), ENNReal.coe_mul]
          norm_num
        rw [hshrink]
        exact shrink_mul_two_mul_le (C := (C : ENNReal))
          (x := Metric.ethickness ℝ K.carrier 1) (y := (b : ENNReal))
          (by exact_mod_cast hC) ENNReal.coe_ne_top hKone
  · calc
      Metric.ethickness ℝ (scaledCollar C K).carrier 2
          ≤ (shrink C : ENNReal) *
              Metric.ethickness ℝ (K.cthickening (scaleRadius K : ℝ)).carrier 2 :=
            ethickness_scaledCollar_le C K 2
      _ ≤ (shrink C : ENNReal) * (2 * Metric.ethickness ℝ K.carrier 2) := by
        gcongr
        exact hcollar 2
      _ ≤ a := by
        have hshrink : (shrink C : ENNReal) = (8 * (C : ENNReal))⁻¹ := by
          rw [shrink, ENNReal.coe_inv (by positivity : 8 * C ≠ 0), ENNReal.coe_mul]
          norm_num
        rw [hshrink]
        exact shrink_mul_two_mul_le (C := (C : ENNReal))
          (x := Metric.ethickness ℝ K.carrier 2) (y := (a : ENNReal))
          (by exact_mod_cast hC) ENNReal.coe_ne_top hKtwo

/-- Real-valued form of `ethickness_scaledCollar_bounds`, matching the coordinates used by
`outerPrism`. -/
theorem thickness_scaledCollar_bounds {C a b : NNReal} {K : ConvexSpaceBody E3}
    (hC : 1 ≤ C)
    (hKone : Metric.ethickness ℝ K.carrier 1 ≤ (C : ENNReal) * b)
    (hKtwo : Metric.ethickness ℝ K.carrier 2 ≤ (C : ENNReal) * a)
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall) :
    Metric.thickness ℝ (scaledCollar C K).carrier 0 ≤ 1 ∧
      Metric.thickness ℝ (scaledCollar C K).carrier 1 ≤ b ∧
      Metric.thickness ℝ (scaledCollar C K).carrier 2 ≤ a := by
  obtain ⟨hzero, hone, htwo⟩ :=
    ethickness_scaledCollar_bounds hC hKone hKtwo hKball
  have hbdd := (scaledCollar C K).isCompact'.isBounded
  refine ⟨?_, ?_, ?_⟩
  · rw [← Metric.toReal_ethickness hbdd 0]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hzero
  · rw [← Metric.toReal_ethickness hbdd 1]
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hone
  · rw [← Metric.toReal_ethickness hbdd 2]
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top htwo

/-- Reverse the axes of the limiting outer prism and enlarge them to the common dimensions
`a × b × 1`. -/
def plank (C a b : NNReal) (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody E3) : Plank a b hab hb1 where
  toPrismNDim := PrismNDim.mk' (raw C K).center
    ((raw C K).basis.reindex Fin.revPerm)
    ![a, b, 1]
  thicknesses_eq := by
    simpa using PrismNDim.thicknesses_mk' (raw C K).center
      ((raw C K).basis.reindex Fin.revPerm) ![a, b, 1]

/-- The limiting outer prism of the scaled collar is contained in the common exact plank. -/
theorem raw_le_plank {C a b : NNReal} (hC : 1 ≤ C) (hab : a ≤ b) (hb1 : b ≤ 1)
    {K : ConvexSpaceBody E3}
    (hKone : Metric.ethickness ℝ K.carrier 1 ≤ (C : ENNReal) * b)
    (hKtwo : Metric.ethickness ℝ K.carrier 2 ≤ (C : ENNReal) * a)
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall) :
    (raw C K).toConvexSpaceBody ≤ (plank C a b hab hb1 K).toConvexSpaceBody := by
  obtain ⟨hzero, hone, htwo⟩ := thickness_scaledCollar_bounds hC hKone hKtwo hKball
  intro x hx
  change x ∈ (plank C a b hab hb1 K).carrier
  rw [(plank C a b hab hb1 K).mem_carrier_iff]
  intro i
  have hx' : x ∈ (raw C K).carrier := hx
  have hraw := ((raw C K).mem_carrier_iff x).mp hx' (Fin.revPerm.symm i)
  change
    |((raw C K).basis.reindex Fin.revPerm).repr (x - (raw C K).center) i| ≤
      (![a, b, 1] : Fin 3 → NNReal) i
  rw [OrthonormalBasis.repr_reindex]
  fin_cases i <;> simp at hraw ⊢
  · exact hraw.trans htwo
  · exact hraw.trans hone
  · exact hraw.trans hzero

/-- The shrunk scale-collar is contained in its common exact plank envelope. -/
theorem scaledCollar_le_plank {C a b : NNReal} (hC : 1 ≤ C) (hab : a ≤ b) (hb1 : b ≤ 1)
    {K : ConvexSpaceBody E3}
    (hKone : Metric.ethickness ℝ K.carrier 1 ≤ (C : ENNReal) * b)
    (hKtwo : Metric.ethickness ℝ K.carrier 2 ≤ (C : ENNReal) * a)
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall) :
    scaledCollar C K ≤ (plank C a b hab hb1 K).toConvexSpaceBody :=
  (outerPrism.self_subset (by simp) (scaledCollar C K).isCompact'
    (scaledCollar C K).nonempty').trans
      (raw_le_plank hC hab hb1 hKone hKtwo hKball)

/-- Every common exact envelope lies in the fixed radius-four plank window. -/
theorem plank_carrier_subset_window {C a b : NNReal} (hC : 1 ≤ C)
    (hab : a ≤ b) (hb1 : b ≤ 1) {K : ConvexSpaceBody E3}
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall) :
    (plank C a b hab hb1 K).carrier ⊆
      Metric.closedBall 0 (plankWindowRadius : ℝ) := by
  have hscaled := scaledCollar_subset_closedBall_quarter hC hKball
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
          (((plank C a b hab hb1 K).toPrismNDim.thicknesses i : NNReal) : ℝ)) ≤ 3 := by
      rw [(plank C a b hab hb1 K).thicknesses_eq, Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        NNReal.coe_one]
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

/-- Re-carrier the homothetically shrunken shading by the common exact plank envelope. -/
def shadedPlank {C a b : NNReal} (hC : 1 ≤ C) (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody E3) (Y : ShadedBody E3)
    (hY : Y.toConvexSpaceBody = K.cthickening (scaleRadius K : ℝ))
    (hKone : Metric.ethickness ℝ K.carrier 1 ≤ (C : ENNReal) * b)
    (hKtwo : Metric.ethickness ℝ K.carrier 2 ≤ (C : ENNReal) * a)
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall) : ShadedPlank a b hab hb1 where
  toPrism3D := plank C a b hab hb1 K
  shade := (Y.homothety 0 (shrink_coe_ne_zero hC)).shade
  measurableSet_shade :=
    (Y.homothety 0 (shrink_coe_ne_zero hC)).measurableSet_shade
  shade_subset := by
    let hshrink : (shrink C : ℝ) ≠ 0 := shrink_coe_ne_zero hC
    have hbody : (Y.homothety 0 hshrink).toConvexSpaceBody = scaledCollar C K := by
      rw [ShadedBody.homothety_toConvexSpaceBody, hY]
      rfl
    exact (Y.homothety 0 hshrink).shade_subset.trans <| by
      rw [hbody]
      exact scaledCollar_le_plank hC hab hb1 hKone hKtwo hKball

@[simp]
theorem shadedPlank_shade {C a b : NNReal} (hC : 1 ≤ C) (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody E3) (Y : ShadedBody E3)
    (hY : Y.toConvexSpaceBody = K.cthickening (scaleRadius K : ℝ))
    (hKone : Metric.ethickness ℝ K.carrier 1 ≤ (C : ENNReal) * b)
    (hKtwo : Metric.ethickness ℝ K.carrier 2 ≤ (C : ENNReal) * a)
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall) :
    (shadedPlank hC hab hb1 K Y hY hKone hKtwo hKball).shade =
      (Y.homothety 0 (shrink_coe_ne_zero hC)).shade := rfl

end comparablePlankEnvelope

end Kakeya

end

end
