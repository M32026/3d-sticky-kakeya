/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PlankEnvelopeWindow
public import Kakeya.Tube.Rescale

/-!
# Presenting a scale-collar outer family on exact `a × b × 1` planks

GWZ Proposition 5.1 returns its outer bodies on the **scale-collar** of the actual factor body:
`ShadedBody.FactoringAndMultPropCoreAtScale.outer_carrier` says

`(O.outerBody j).toConvexSpaceBody = (F.outerBody j).cthickening ((F.outerBody j).scale)`.

The Section-6 assembly, on the other hand, consumes the outer family as exact `a × b × 1`
`Kakeya.ShadedPlank`s: fullness, Katz--Tao, the outer window, and GWZ Lemma 6.1 at the master
scale are all stated for planks.  This file bridges that gap, for a body family living in a window
of any radius `R ≥ 1` — which is the Part-(B) situation, since
`Kakeya.Section6PartBFactorisation.repr_window` puts the cell bodies in
`Metric.closedBall 0 Kakeya.plankWindowRadius` and *not* in the unit ball.

## Why a rescaling is unavoidable

The naive presentation — take the cell's representative plank — does not work, and the failure is
in the long axis and is quantitative.  A `Kakeya.Plank a b` is a `Kakeya.Prism3D a b 1`, whose long
half-width is exactly `1`.  A cell body reaching the boundary of the working window has its
`s`-collar reaching to `1 + s` along that axis, so no `Kakeya.Plank a b` contains the collar.
Transversally there is no problem at all (`(a + s, b + s) ⊆ (2a, 2b)` for `s ≤ a ≤ b`); it is only
the pinned long half-width that overflows.

Clipping the shading back to the representative plank is **not** free.
`Kakeya.ShadedBody.multiplicity` is `(∑ |Y|) / |U(Y)|`: clipping shrinks the denominator, which
helps, *and* the numerator, which does not, and no constant-mass bound for the clipped shading
holds in general.

The honest route, and the one taken here, is a **single common homothety**.  Shrink every
scale-collar by the one fixed ratio `Kakeya.comparablePlankEnvelope.shrink` at the enlarged
constant `Kakeya.windowPlankEnvelope.windowConst R Cw`, and enclose each shrunk collar in its
exact `a × b × 1` envelope.  Under one common homothety

* `Kakeya.ShadedBody.multiplicity` is **exactly invariant**
  (`Kakeya.ShadedBody.multiplicity_homothety`) — nothing is lost in the multiplicity split;
* `Kakeya.ShadedBody.fullness` is exactly invariant
  (`Kakeya.ShadedBody.fullness_homothety`), so the only fullness loss is the fixed envelope
  volume ratio `Kakeya.flatPrismEnvelopeVolumeRatio.C`;
* `Kakeya.ConvexSpaceBody.IsKatzTao` is exactly invariant
  (`Kakeya.ConvexSpaceBody.IsKatzTao.homothety`), so the only Katz--Tao loss is the collar
  doubling constant times that same envelope ratio;
* the shadings are transported **exactly**: the shading of the presented plank *is* the homothety
  image of the Proposition-5.1 outer shading (`Kakeya.collarPlank_shade`).

## Main results

* `Kakeya.collarPlank` — the presented `Kakeya.ShadedPlank`, and `Kakeya.collarPlank_shade`;
* `Kakeya.collarPlank_carrier_subset_window` — it lies in the fixed radius-`4` window;
* `Kakeya.multiplicity_collarPlank` — the multiplicity is unchanged;
* `Kakeya.le_fullness_collarPlank` — the fullness drops by at most the envelope ratio;
* `Kakeya.isKatzTao_collarPlank` — Katz--Tao with the two explicit fixed losses.

Every loss constant is absolute: it depends only on `R`, on the plank comparability constant `Cw`
and on the ambient dimension.  In particular none of them sees the scale `δ`, so all of them are
absorbed by the same sub-polynomial budget that already carries `Cw`.
-/

@[expose] public section

open MeasureTheory Metric Convexity
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

open comparablePlankEnvelope windowPlankEnvelope

section Collar

variable {X : Type*}

/-- The four side conditions of the presentation, at a single body. -/
def IsCollarPresentable (R Cw a b : ℝ≥0) (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : ShadedBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  Y.toConvexSpaceBody = K.cthickening K.scale ∧
    Metric.ethickness ℝ K.carrier 0 ≤ (R : ENNReal) ∧
    Metric.ethickness ℝ K.carrier 1 ≤ (Cw : ENNReal) * (b : ENNReal) ∧
    Metric.ethickness ℝ K.carrier 2 ≤ (Cw : ENNReal) * (a : ENNReal)

/-- **The side conditions come for free from plank-comparable dimensions in a window.**
Nothing beyond `Kakeya.IsPlankOfDimensions` and the window containment is needed. -/
theorem isCollarPresentable_of_isPlankOfDimensions {R Cw a b : ℝ≥0}
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {Y : ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (hY : Y.toConvexSpaceBody = K.cthickening K.scale)
    (hKball : (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 (R : ℝ))
    (hK : IsPlankOfDimensions Cw a b K) :
    IsCollarPresentable R Cw a b K Y := by
  refine ⟨hY, ?_, hK.2.1.2, hK.2.2.2⟩
  simpa using Metric.ethickness_le_of_subset_closedBall (𝕜 := ℝ) (x := (0 : EuclideanSpace ℝ (Fin 3)))
    R hKball 0

open Classical in
/-- **The exact `a × b × 1` plank presentation of one scale-collar shading.**

The underlying plank is the exact envelope of the shrunk collar; the shading is the image of `Y`'s
shading under the *single common* homothety of ratio
`Kakeya.comparablePlankEnvelope.shrink (Kakeya.windowPlankEnvelope.windowConst R Cw)` centred at
the origin.  Off the side conditions the shading is empty, which is what makes this a total
function of the body; every statement below is conditioned on
`Kakeya.IsCollarPresentable`. -/
def collarPlank {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : ShadedBody (EuclideanSpace ℝ (Fin 3))) : ShadedPlank a b hab hb1 where
  toPrism3D := plank (windowConst R Cw) a b hab hb1 K
  shade := if _h : IsCollarPresentable R Cw a b K Y then
      (Y.homothety 0 (shrink_coe_ne_zero (one_le_windowConst hR hCw))).shade
    else ∅
  measurableSet_shade := by
    by_cases h : IsCollarPresentable R Cw a b K Y
    · simp only [dif_pos h]
      exact (Y.homothety 0 (shrink_coe_ne_zero (one_le_windowConst hR hCw))).measurableSet_shade
    · simp only [dif_neg h]
      exact MeasurableSet.empty
  shade_subset := by
    by_cases h : IsCollarPresentable R Cw a b K Y
    · simp only [dif_pos h]
      obtain ⟨hY, hK0, hK1, hK2⟩ := h
      have hshrink : ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ≠ 0 :=
        shrink_coe_ne_zero (one_le_windowConst hR hCw)
      have hbody : (Y.homothety 0 hshrink).toConvexSpaceBody =
          scaledCollar (windowConst R Cw) K := by
        rw [ShadedBody.homothety_toConvexSpaceBody, hY]
        rfl
      exact (Y.homothety 0 hshrink).shade_subset.trans <| by
        rw [hbody]
        exact scaledCollar_le_plank_window hR hCw hab hb1 hK0 hK1 hK2
    · simp only [dif_neg h]
      exact Set.empty_subset _

@[simp]
theorem collarPlank_toPrism3D {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    (collarPlank hR hCw hab hb1 K Y).toPrism3D = plank (windowConst R Cw) a b hab hb1 K := rfl

/-- **The shading is transported exactly, with no clipping.** -/
theorem collarPlank_shade {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {Y : ShadedBody (EuclideanSpace ℝ (Fin 3))} (h : IsCollarPresentable R Cw a b K Y) :
    (collarPlank hR hCw hab hb1 K Y).shade =
      (Y.homothety 0 (shrink_coe_ne_zero (one_le_windowConst hR hCw))).shade := by
  classical
  simp only [collarPlank, dif_pos h]

/-- The presented plank lies in the fixed radius-`4` Section-6 window. -/
theorem collarPlank_carrier_subset_window {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (Y : ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hKball : (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 (R : ℝ)) :
    ((collarPlank hR hCw hab hb1 K Y).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall 0 (plankWindowRadius : ℝ) :=
  plank_carrier_subset_window_of_window hR hCw hab hb1 hKball

/-- The presented plank contains the shrunk collar of the body. -/
theorem scaledCollar_le_collarPlank {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {Y : ShadedBody (EuclideanSpace ℝ (Fin 3))} (h : IsCollarPresentable R Cw a b K Y) :
    scaledCollar (windowConst R Cw) K ≤ (collarPlank hR hCw hab hb1 K Y).toConvexSpaceBody :=
  scaledCollar_le_plank_window hR hCw hab hb1 h.2.1 h.2.2.1 h.2.2.2

/-- `Kakeya.ShadedBody.multiplicity` depends only on the shadings.  Proved locally rather than
imported, because the two library copies of this fact live in files this one does not both see. -/
private theorem multiplicityCongrShade {ι' : Type*} (s : Finset ι')
    (V W : ι' → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (h : ∀ i ∈ s, (V i).shade = (W i).shade) :
    ShadedBody.multiplicity s V = ShadedBody.multiplicity s W := by
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div]
  have hsum : (∑ i ∈ s, volume (V i).shade) = ∑ i ∈ s, volume (W i).shade :=
    Finset.sum_congr rfl fun i hi => by rw [h i hi]
  have hun : (⋃ i ∈ s, (V i).shade) = ⋃ i ∈ s, (W i).shade :=
    Set.iUnion₂_congr fun i hi => by rw [h i hi]
  rw [hsum, hun]

/-! ### The three family-level transports -/

variable {R Cw a b : ℝ≥0}

/-- **Multiplicity is exactly invariant under the presentation.**

The presented shadings are the images of the Proposition-5.1 outer shadings under one common
homothety, and `Kakeya.ShadedBody.multiplicity` depends only on the shadings and is invariant
under a homothety. -/
theorem multiplicity_collarPlank (hR : 1 ≤ R) (hCw : 1 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ts : Finset X) (K : X → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : X → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hpres : ∀ x ∈ ts, IsCollarPresentable R Cw a b (K x) (Y x)) :
    ShadedBody.multiplicity ts (fun x => (collarPlank hR hCw hab hb1 (K x) (Y x)).toShadedBody)
      = ShadedBody.multiplicity ts Y := by
  have hshr : ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ≠ 0 :=
    shrink_coe_ne_zero (one_le_windowConst hR hCw)
  have hcongr : ShadedBody.multiplicity ts
      (fun x => (collarPlank hR hCw hab hb1 (K x) (Y x)).toShadedBody)
      = ShadedBody.multiplicity ts (fun x => (Y x).homothety 0 hshr) := by
    refine multiplicityCongrShade ts _ _ ?_
    intro x hx
    exact collarPlank_shade hR hCw hab hb1 (hpres x hx)
  rw [hcongr, ShadedBody.multiplicity_homothety ts Y 0 hshr]

/-- **The fullness loss of the presentation is the fixed envelope volume ratio.**

`Kakeya.ShadedBody.fullness` is invariant under the common homothety, so the only loss is the
volume of the exact envelope against the volume of the shrunk collar, which
`Kakeya.IsPlankOfDimensions.volume_plank_le_mul_scaledCollar` bounds by the absolute constant
`Kakeya.flatPrismEnvelopeVolumeRatio.C (Kakeya.windowPlankEnvelope.windowConst R Cw)`. -/
theorem le_fullness_collarPlank (hR : 1 ≤ R) (hCw : 1 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ha : 0 < a) (hb : 0 < b)
    (ts : Finset X) (K : X → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : X → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hpres : ∀ x ∈ ts, IsCollarPresentable R Cw a b (K x) (Y x))
    (hdim : ∀ x ∈ ts, IsPlankOfDimensions Cw a b (K x)) :
    (flatPrismEnvelopeVolumeRatio.C (windowConst R Cw))⁻¹ * ShadedBody.fullness ts Y ≤
      ShadedBody.fullness ts
        (fun x => (collarPlank hR hCw hab hb1 (K x) (Y x)).toShadedBody) := by
  have hshr : ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ≠ 0 :=
    shrink_coe_ne_zero (one_le_windowConst hR hCw)
  set M : ℝ≥0 := flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) with hM
  have hM1 : 1 ≤ M := flatPrismEnvelopeVolumeRatio.one_le _
  have hstep := _root_.Tube.le_fullness_of_volume_le hM1 ts
    (fun x => (Y x).homothety 0 hshr)
    (fun x => (collarPlank hR hCw hab hb1 (K x) (Y x)).toShadedBody)
    (fun x hx => (collarPlank_shade hR hCw hab hb1 (hpres x hx)))
    (fun x hx => by
      have hKdim : IsPlankOfDimensions (windowConst R Cw) a b (K x) :=
        (hdim x hx).mono_constant (le_trans (by
          calc
            Cw = 1 * Cw := by rw [one_mul]
            _ ≤ 4 * R * Cw := by
              exact mul_le_mul_right' (by
                calc
                  (1 : ℝ≥0) = 1 * 1 := by norm_num
                  _ ≤ 4 * R := mul_le_mul' (by norm_num) hR) Cw) (le_of_eq rfl))
      have henv := hKdim.volume_plank_le_mul_scaledCollar
        (one_le_windowConst hR hCw) ha hb hab hb1
      have hbody : ((Y x).homothety 0 hshr).carrier =
          (scaledCollar (windowConst R Cw) (K x)).carrier := by
        have h1 : ((Y x).homothety 0 hshr).toConvexSpaceBody =
            scaledCollar (windowConst R Cw) (K x) := by
          rw [ShadedBody.homothety_toConvexSpaceBody, (hpres x hx).1]
          rfl
        exact congrArg (fun B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) => B.carrier) h1
      rw [hbody]
      exact henv)
  rwa [ShadedBody.fullness_homothety ts Y 0 hshr] at hstep

/-- The presented shading volumes are the scaled Proposition-5.1 outer shading volumes. -/
theorem sum_volume_shade_collarPlank (hR : 1 ≤ R) (hCw : 1 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ts : Finset X) (K : X → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : X → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hpres : ∀ x ∈ ts, IsCollarPresentable R Cw a b (K x) (Y x)) :
    ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).shade)
      = ENNReal.ofReal
            |((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ^
              Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| *
          ∑ x ∈ ts, volume (Y x).shade := by
  have hshr : ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ≠ 0 :=
    shrink_coe_ne_zero (one_le_windowConst hR hCw)
  have hstep : ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).shade)
      = ∑ x ∈ ts, volume (((Y x).homothety 0 hshr).shade) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [collarPlank_shade hR hCw hab hb1 (hpres x hx)]
  rw [hstep, ShadedBody.sum_volume_shade_homothety ts Y 0 hshr]

/-- The presented carriers cost at most the envelope ratio against the scaled Proposition-5.1
outer carriers. -/
theorem sum_volume_carrier_collarPlank_le (hR : 1 ≤ R) (hCw : 1 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ha : 0 < a) (hb : 0 < b)
    (ts : Finset X) (K : X → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : X → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hpres : ∀ x ∈ ts, IsCollarPresentable R Cw a b (K x) (Y x))
    (hdim : ∀ x ∈ ts, IsPlankOfDimensions Cw a b (K x)) :
    ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier)
      ≤ (flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) : ENNReal) *
          (ENNReal.ofReal
            |((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ^
              Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| *
          ∑ x ∈ ts, volume (Y x).carrier) := by
  have hshr : ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ≠ 0 :=
    shrink_coe_ne_zero (one_le_windowConst hR hCw)
  have hCwle : Cw ≤ windowConst R Cw := by
    calc
      Cw = 1 * Cw := by rw [one_mul]
      _ ≤ 4 * R * Cw := by
        exact mul_le_mul_right' (by
          calc
            (1 : ℝ≥0) = 1 * 1 := by norm_num
            _ ≤ 4 * R := mul_le_mul' (by norm_num) hR) Cw
  have hterm : ∀ x ∈ ts,
      volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier) ≤
        (flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) : ENNReal) *
          (ENNReal.ofReal
            |((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ^
              Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| * volume (Y x).carrier) := by
    intro x hx
    have hKdim : IsPlankOfDimensions (windowConst R Cw) a b (K x) :=
      (hdim x hx).mono_constant hCwle
    have henv := hKdim.volume_plank_le_mul_scaledCollar
      (one_le_windowConst hR hCw) ha hb hab hb1
    have hcollarvol : volume (scaledCollar (windowConst R Cw) (K x)).carrier
        = ENNReal.ofReal
            |((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ^
              Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| * volume (Y x).carrier := by
      have h1 : scaledCollar (windowConst R Cw) (K x)
          = (Y x).toConvexSpaceBody.homothety 0 ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) := by
        rw [scaledCollar, (hpres x hx).1]
        rfl
      rw [h1, ConvexSpaceBody.volume_homothety]
    calc
      volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier)
          = volume (plank (windowConst R Cw) a b hab hb1 (K x)).carrier := rfl
      _ ≤ (flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) : ENNReal) *
            volume (scaledCollar (windowConst R Cw) (K x)).carrier := henv
      _ = _ := by rw [hcollarvol]
  calc
    ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier)
        ≤ ∑ x ∈ ts, (flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) : ENNReal) *
            (ENNReal.ofReal
              |((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ^
                Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| * volume (Y x).carrier) :=
          Finset.sum_le_sum hterm
    _ = (flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) : ENNReal) *
          (ENNReal.ofReal
            |((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ^
              Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| *
            ∑ x ∈ ts, volume (Y x).carrier) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- **The summed (Proposition-5.1-shaped) fullness bound transports to the presentation.**

This is the exact Part-(B) analogue of Part (A)'s
`Kakeya.Section6PartAFactorData.Prop51Output.plank_fullness`: the same inequality, with the
representative-plank volume loss `Cdim` replaced by the envelope ratio, and with the common
homothety factor cancelling between the two sides. -/
theorem collarPlank_sum_fullness_transport (hR : 1 ≤ R) (hCw : 1 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ha : 0 < a) (hb : 0 < b)
    (ts : Finset X) (K : X → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : X → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hpres : ∀ x ∈ ts, IsCollarPresentable R Cw a b (K x) (Y x))
    (hdim : ∀ x ∈ ts, IsPlankOfDimensions Cw a b (K x))
    {c : ENNReal}
    (hfull : c * (∑ x ∈ ts, volume (Y x).carrier) ≤ ∑ x ∈ ts, volume (Y x).shade) :
    c * (∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier))
      ≤ (flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) : ENNReal) *
          ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).shade) := by
  set M : ENNReal := (flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) : ENNReal) with hM
  set κ : ENNReal := ENNReal.ofReal
      |((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ^
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| with hκ
  calc
    c * (∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier))
        ≤ c * (M * (κ * ∑ x ∈ ts, volume (Y x).carrier)) := by
          gcongr
          exact sum_volume_carrier_collarPlank_le hR hCw hab hb1 ha hb ts K Y hpres hdim
    _ = M * (κ * (c * ∑ x ∈ ts, volume (Y x).carrier)) := by ring
    _ ≤ M * (κ * ∑ x ∈ ts, volume (Y x).shade) := by gcongr
    _ = M * ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).shade) := by
          rw [sum_volume_shade_collarPlank hR hCw hab hb1 ts K Y hpres]

/-- **A summed fullness bound converts to a `Kakeya.ShadedBody.fullness` lower bound.**

`Kakeya.ShadedBody.fullness` is the ratio of the two sums, so the summed form
`c * ∑ |W| ≤ ∑ |Y(W)|` — which is the shape GWZ Proposition 5.1 delivers
(`Kakeya.ShadedBody.FactoringAndMultPropCoreAtScale.thick_fullness`) — is exactly `c ≤ λ`, as
soon as the denominator is nonzero. -/
theorem le_fullness_of_mul_sum_carrier_le {ι' : Type*} (s : Finset ι')
    (V : ι' → ShadedBody (EuclideanSpace ℝ (Fin 3))) {c : ℝ≥0}
    (h : (c : ENNReal) * (∑ i ∈ s, volume (V i).carrier) ≤ ∑ i ∈ s, volume (V i).shade)
    (hne : (∑ i ∈ s, volume (V i).carrier) ≠ 0) :
    c ≤ ShadedBody.fullness s V := by
  have htop : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤ := ShadedBody.sum_volume_carrier_ne_top s V
  refine ENNReal.coe_le_coe.mp ?_
  rw [ShadedBody.coe_fullness]
  show (c : ENNReal) ≤ (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl htop)]
  exact h

/-- **Katz--Tao for the presented plank family.**

Two explicit fixed losses and nothing else: the collar doubling constant
`Metric.volume_comparison.C 3` (the volume of the `scale`-collar against the body, from
`Kakeya.ConvexSpaceBody.volume_cthickening_le`, which applies exactly because the collar radius
*is* the body's scale) and the envelope ratio
`Kakeya.flatPrismEnvelopeVolumeRatio.C (Kakeya.windowPlankEnvelope.windowConst R Cw)`.  Neither
sees the scale. -/
theorem isKatzTao_collarPlank (hR : 1 ≤ R) (hCw : 1 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ha : 0 < a) (hb : 0 < b)
    (ts : Finset X) (K : X → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : X → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hpres : ∀ x ∈ ts, IsCollarPresentable R Cw a b (K x) (Y x))
    (hdim : ∀ x ∈ ts, IsPlankOfDimensions Cw a b (K x))
    {C₀ : ENNReal} (hKT : ConvexSpaceBody.IsKatzTao ts K C₀) :
    ConvexSpaceBody.IsKatzTao ts
      (fun x => (collarPlank hR hCw hab hb1 (K x) (Y x)).toConvexSpaceBody)
      ((flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) : ENNReal) *
        ((Metric.volume_comparison.C 3 : ENNReal) * C₀)) := by
  classical
  have hshr : ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ≠ 0 :=
    shrink_coe_ne_zero (one_le_windowConst hR hCw)
  -- step 1: the scale-collar family
  have hcollarKT : ConvexSpaceBody.IsKatzTao ts
      (fun x => (K x).cthickening ((scaleRadius (K x) : ℝ)))
      ((Metric.volume_comparison.C 3 : ENNReal) * C₀) := by
    refine ConvexSpaceBody.IsKatzTao.of_envelope hKT
      (fun x _ => ConvexSpaceBody.self_le_cthickening (K x) _) (fun x _ => ?_)
    have h := ConvexSpaceBody.volume_cthickening_le (K x) (scaleRadius (K x)) (by simp)
    simpa [finrank_euclideanSpace_fin] using h
  -- step 2: the shrunk collar family, by homothety invariance
  have hscaledKT : ConvexSpaceBody.IsKatzTao ts
      (fun x => scaledCollar (windowConst R Cw) (K x))
      ((Metric.volume_comparison.C 3 : ENNReal) * C₀) :=
    hcollarKT.homothety 0 hshr
  -- step 3: the exact envelope family
  refine ConvexSpaceBody.IsKatzTao.of_envelope hscaledKT
    (fun x hx => scaledCollar_le_collarPlank hR hCw hab hb1 (hpres x hx)) (fun x hx => ?_)
  have hKdim : IsPlankOfDimensions (windowConst R Cw) a b (K x) :=
    (hdim x hx).mono_constant (by
      calc
        Cw = 1 * Cw := by rw [one_mul]
        _ ≤ 4 * R * Cw := by
          exact mul_le_mul_right' (by
            calc
              (1 : ℝ≥0) = 1 * 1 := by norm_num
              _ ≤ 4 * R := mul_le_mul' (by norm_num) hR) Cw)
  exact hKdim.volume_plank_le_mul_scaledCollar (one_le_windowConst hR hCw) ha hb hab hb1

end Collar

/-! ### The bridge to GWZ Proposition 5.1

`Kakeya.ShadedBody.FactoringAndMultPropCoreAtScale.outer_carrier` says that the outer bodies of the
constructed Proposition-5.1 output *are* the `Kakeya.ConvexSpaceBody.scale`-collars of the input
outer bodies.  So the presentation applies to a Proposition-5.1 output as soon as the input outer
bodies live in a window and have comparable plank dimensions — and nothing else is required. -/

section Prop51

variable {ι κ' : Type*} [DecidableEq κ']

/-- **The Proposition-5.1 output is collar-presentable.**

This is the whole content of the bridge: with it, the four transports above
(`Kakeya.collarPlank_carrier_subset_window`, `Kakeya.multiplicity_collarPlank`,
`Kakeya.le_fullness_collarPlank`, `Kakeya.isKatzTao_collarPlank`, and the summed form
`Kakeya.collarPlank_sum_fullness_transport`) apply verbatim at
`K := F.outerBody`, `Y := (outerThickFamilyAtScale …).outerBody`,
`ts := (outerThickFamilyAtScale …).outerSet`. -/
theorem isCollarPresentable_outerThickFamilyAtScale
    (F : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι κ')
    {C : ENNReal} {δ' : ℝ≥0} (hδ' : 0 < δ')
    (hdisc : F.InnerIsDiscretizedAtScale δ') (Dvr : ShadedBody.OuterInnerVolumeRatio F)
    (w₁ : ℝ≥0) (hw₁ : 0 < w₁)
    (P : ShadedBody.FactoringAndMultPropCoreAtScale (C := C) F hδ' hdisc Dvr w₁ hw₁)
    {R Cw a b : ℝ≥0}
    (hwin : ∀ j ∈ F.outerSet,
      ((F.outerBody j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 (R : ℝ))
    (hdimK : ∀ j ∈ F.outerSet, IsPlankOfDimensions Cw a b (F.outerBody j)) :
    ∀ j ∈ (ShadedBody.outerThickFamilyAtScale F hδ' hdisc Dvr w₁ hw₁).outerSet,
      IsCollarPresentable R Cw a b (F.outerBody j)
        ((ShadedBody.outerThickFamilyAtScale F hδ' hdisc Dvr w₁ hw₁).outerBody j) := by
  intro j hj
  exact isCollarPresentable_of_isPlankOfDimensions (P.outer_carrier j)
    (hwin j (P.outerSet_subset hj)) (hdimK j (P.outerSet_subset hj))

/-- Plank-comparable dimensions of the *presented* outer family, restricted to the retained
indices — the form `Kakeya.le_fullness_collarPlank` and `Kakeya.isKatzTao_collarPlank` want. -/
theorem isPlankOfDimensions_outerBody_of_mem_outerThickFamilyAtScale
    (F : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι κ')
    {C : ENNReal} {δ' : ℝ≥0} (hδ' : 0 < δ')
    (hdisc : F.InnerIsDiscretizedAtScale δ') (Dvr : ShadedBody.OuterInnerVolumeRatio F)
    (w₁ : ℝ≥0) (hw₁ : 0 < w₁)
    (P : ShadedBody.FactoringAndMultPropCoreAtScale (C := C) F hδ' hdisc Dvr w₁ hw₁)
    {Cw a b : ℝ≥0}
    (hdimK : ∀ j ∈ F.outerSet, IsPlankOfDimensions Cw a b (F.outerBody j)) :
    ∀ j ∈ (ShadedBody.outerThickFamilyAtScale F hδ' hdisc Dvr w₁ hw₁).outerSet,
      IsPlankOfDimensions Cw a b (F.outerBody j) :=
  fun j hj => hdimK j (P.outerSet_subset hj)


/-! ### The fibres of the Proposition-5.1 output sit inside the input fibres

Needed by the wiring: the cardinality clause `|𝒲'| · |𝒯_W| ≤ Ccard · |𝒯|` is proved for the
*input* block system (that is what a block pigeonhole can see), so it has to be read down along
the refinement.  Both steps are inclusions of `Finset.filter`s. -/

omit [DecidableEq κ'] in
/-- Membership in a fibre, with no instance bookkeeping. -/
theorem mem_fiber_iff' (F : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι κ')
    (j : κ') (i : ι) : i ∈ F.fiber j ↔ i ∈ F.innerSet ∧ F.parent i = j := by
  classical
  simp [ShadedBody.FactorFamily.fiber]

omit [DecidableEq κ'] in
/-- Membership in a shaded fibre, with no instance bookkeeping. -/
theorem mem_shadedFiber_iff' (F : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι κ')
    (j : κ') (i : ι) : i ∈ F.fiber j ↔ i ∈ F.innerSet ∧ F.parent i = j := by
  classical
  simp [ShadedBody.ShadedFactorFamily.fiber]

/-- Restricting the outer index set shrinks every fibre. -/
theorem fiber_restrictOuter_subset (F : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι κ')
    (t : Finset κ') (j : κ') : (F.restrictOuter t).fiber j ⊆ F.fiber j := by
  classical
  intro i hi
  rw [mem_fiber_iff'] at hi
  rw [mem_fiber_iff']
  refine ⟨?_, hi.2⟩
  have h := hi.1
  rw [show (F.restrictOuter t).innerSet
      = ({i ∈ F.innerSet | F.parent i ∈ t} : Finset ι) from rfl] at h
  exact (Finset.mem_filter.mp h).1

/-- **The Proposition-5.1 output's fibres are inside the input family's fibres.** -/
theorem fiber_outerThickFamilyAtScale_subset
    (F : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι κ')
    {C : ENNReal} {δ' : ℝ≥0} (hδ' : 0 < δ')
    (hdisc : F.InnerIsDiscretizedAtScale δ') (Dvr : ShadedBody.OuterInnerVolumeRatio F)
    (w₁ : ℝ≥0) (hw₁ : 0 < w₁)
    (P : ShadedBody.FactoringAndMultPropCoreAtScale (C := C) F hδ' hdisc Dvr w₁ hw₁)
    (j : κ') :
    (ShadedBody.outerThickFamilyAtScale F hδ' hdisc Dvr w₁ hw₁).fiber j ⊆ F.fiber j := by
  classical
  intro i hi
  rw [mem_shadedFiber_iff'] at hi
  obtain ⟨hiO, hpar⟩ := hi
  rw [P.innerSet_eq] at hiO
  rw [mem_fiber_iff']
  refine ⟨(Finset.mem_filter.mp hiO).1, ?_⟩
  rw [← hpar, P.parent_eq]

end Prop51


end Kakeya

end

end
