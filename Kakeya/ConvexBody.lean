/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Convex.Body
public import Kakeya.Mathlib.MeasureTheory.Action
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
  In this file we collect facts about convex bodies.
-/

open MeasureTheory ENNReal

variable
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

@[expose] public section
namespace ConvexSpaceBody
/-- The unit ball is a convex body -/
@[simps]
def closedUnitBall : ConvexSpaceBody E where
  carrier := Metric.closedBall 0 1
  convex' := (convex_closedBall _ _).isConvexSet
  isCompact' := isCompact_closedBall _ _
  nonempty' := Metric.nonempty_closedBall.mpr zero_le_one

lemma mem_closedUnitBall {x : E} :
    x ∈ (closedUnitBall : ConvexSpaceBody E) ↔ x ∈ Metric.closedBall (0 : E) 1 := Iff.rfl

lemma closedUnitBall_volume_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    0 < volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
  Metric.measure_closedBall_pos volume 0 one_pos

/-- The closed ball of nonneg radius `r` centred at the origin, as a convex body. -/
@[simps]
def closedBall (x : E) (r : ℝ) (hr : 0 ≤ r) : ConvexSpaceBody E where
  carrier := Metric.closedBall x r
  convex' := (convex_closedBall _ _).isConvexSet
  isCompact' := isCompact_closedBall _ _
  nonempty' := Metric.nonempty_closedBall.mpr hr

/-- The closed neighborhood of a convex body is a convex body -/
@[simps]
def cthickening (r : ℝ) (K : ConvexSpaceBody E) : ConvexSpaceBody E where
  carrier := Metric.cthickening r K.carrier
  convex' := (K.convex.cthickening _).isConvexSet
  isCompact' := K.isCompact.cthickening
  nonempty' := K.nonempty.mono (Metric.self_subset_cthickening _)

theorem self_le_cthickening (K : ConvexSpaceBody E) (r : ℝ) : K ≤ K.cthickening r :=
  SetLike.coe_subset_coe.mp (Metric.self_subset_cthickening K.carrier)

theorem cthickening_mono {K L : ConvexSpaceBody E} (r : ℝ) (h : K ≤ L) :
    K.cthickening r ≤ L.cthickening r :=
  SetLike.coe_subset_coe.mp (Metric.cthickening_subset_of_subset r (SetLike.coe_subset_coe.mpr h))

/-- The intersection of two convex bodies whose carriers meet is a convex body. -/
@[simps]
def inter [T2Space E] (K L : ConvexSpaceBody E)
    (hne : (K.carrier ∩ L.carrier).Nonempty) : ConvexSpaceBody E where
  carrier := K.carrier ∩ L.carrier
  convex' := (K.convex.inter L.convex).isConvexSet
  isCompact' := K.isCompact.inter L.isCompact
  nonempty' := hne
end ConvexSpaceBody

/-- Two measurable sets U, V in E are essentially distinct
    if `|U ∩ V| ≤ (1/2) · max(|U|, |V|)`.
    [Wang–Zahl, "Volume estimates for unions of convex sets"] -/
def IsEssentiallyDistinct {E : Type*} [MeasureSpace E] (U V : Set E) : Prop :=
  volume (U ∩ V) ≤ (1 / 2) * max (volume U) (volume V)

/-- Essential distinctness of sets is symmetric. -/
theorem isEssentiallyDistinct_symm {E : Type*} [MeasureSpace E] {U W : Set E}
    (h : IsEssentiallyDistinct U W) : IsEssentiallyDistinct W U := by
  rwa [IsEssentiallyDistinct, Set.inter_comm, max_comm]

/-- A set of positive finite measure is not essentially distinct from itself. -/
theorem not_isEssentiallyDistinct_self {E : Type*} [MeasureSpace E] {U : Set E}
    (h0 : volume U ≠ 0) (htop : volume U ≠ ⊤) : ¬ IsEssentiallyDistinct U U := by
  rw [IsEssentiallyDistinct, Set.inter_self, max_self, one_div, ← ENNReal.div_eq_inv_mul]
  exact not_le.2 (ENNReal.half_lt_self h0 htop)

namespace Kakeya

/-- The carrier of `cthickening r closedUnitBall` is `closedBall 0 (r + 1)`. -/
lemma cthickening_closedUnitBall_carrier
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (r : ℝ) (hr : 0 ≤ r) :
    (ConvexSpaceBody.cthickening r (ConvexSpaceBody.closedUnitBall (E := E))).carrier =
      Metric.closedBall (0 : E) (r + 1) := by
  change Metric.cthickening r (Metric.closedBall (0 : E) 1) = _
  rw [cthickening_closedBall hr (by norm_num : (0 : ℝ) ≤ 1)]

/-- For `r > 0`, `volume.real (closedBall 0 r)` is positive.
TODO: get rid of `volume.real`; use only `volume`. -/
lemma volume_real_closedBall_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {r : ℝ} (hr : 0 < r) :
    0 < volume.real (Metric.closedBall (0 : E) r) :=
  ENNReal.toReal_pos
    (Metric.measure_closedBall_pos volume 0 hr).ne'
    MeasureTheory.measure_closedBall_lt_top.ne

/-- Essential distinctness is invariant under translation: `(v + ·)` preserves the relation. -/
lemma isEssentiallyDistinct_translate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (A B : Set E) (v : E) :
    IsEssentiallyDistinct ((fun x => v + x) '' A) ((fun x => v + x) '' B) ↔
      IsEssentiallyDistinct A B := by
  have hinv_fun : Set.image (fun x : E => v + x) = Set.preimage (fun x : E => -v + x) :=
    Set.image_eq_preimage_of_inverse (fun x => by simp) (fun x => by simp)
  have hinv : ∀ S : Set E, (fun x => v + x) '' S = (fun x => -v + x) ⁻¹' S := by
    intro S
    exact congrFun hinv_fun S
  have hvol : ∀ S : Set E, volume ((fun x => v + x) '' S) = volume S := by
    intro S
    rw [hinv S]
    rw [MeasureTheory.measure_preimage_add]
  have hinter : (fun x => v + x) '' (A ∩ B) =
      ((fun x => v + x) '' A) ∩ ((fun x => v + x) '' B) := by
    rw [hinv (A ∩ B), hinv A, hinv B, Set.preimage_inter]
  unfold IsEssentiallyDistinct
  rw [← hinter, hvol A, hvol B, hvol (A ∩ B)]

end Kakeya

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

open scoped Pointwise in
/-- The translation `v +ᵥ K` of a convex body `K` by a vector `v`, as a convex body. -/
@[simps]
def ConvexSpaceBody.vadd (K : ConvexSpaceBody E) (v : E) : ConvexSpaceBody E where
  carrier := v +ᵥ K.carrier
  convex' := (K.convex.vadd _).isConvexSet
  isCompact' := K.isCompact'.image (continuous_const_vadd v)
  nonempty' := K.nonempty'.image _

open scoped Pointwise in
@[simp]
lemma ConvexSpaceBody.coe_vadd (K : ConvexSpaceBody E) (v : E) :
    SetLike.coe (K.vadd v) = v +ᵥ K.carrier := rfl

open scoped Pointwise in
@[simp]
lemma ConvexSpaceBody.vadd_zero (K : ConvexSpaceBody E) : K.vadd 0 = K := by
  simp [ConvexSpaceBody.vadd]

open scoped Pointwise in
lemma ConvexSpaceBody.vadd_vadd (K : ConvexSpaceBody E) (v₁ v₂ : E) :
    ConvexSpaceBody.vadd (ConvexSpaceBody.vadd K v₂) v₁ = ConvexSpaceBody.vadd K (v₁ + v₂) := by
  ext1; simp [_root_.vadd_vadd]

/-- Translation of a convex body by a vector. -/
@[simps]
def ConvexSpaceBody.translate (K : ConvexSpaceBody E) (v : E) : ConvexSpaceBody E where
  __ := K.vadd v
  carrier := (v + ·) '' K.carrier

@[simp]
lemma ConvexSpaceBody.translate_zero (K : ConvexSpaceBody E) : ConvexSpaceBody.translate K 0 = K :=
  K.vadd_zero

@[simp]
lemma ConvexSpaceBody.coe_translate (K : ConvexSpaceBody E) (v : E) :
    SetLike.coe (ConvexSpaceBody.translate K v) = (v + ·) '' K.carrier := rfl

@[simp]
lemma ConvexSpaceBody.mem_translate (K : ConvexSpaceBody E) (v : E) (x : E) :
    x ∈ ConvexSpaceBody.translate K v ↔ ∃ y ∈ K.carrier, v + y = x := Iff.rfl

lemma translate_le_translate {K L : ConvexSpaceBody E} (v : E) (h : K ≤ L) :
    ConvexSpaceBody.translate K v ≤ ConvexSpaceBody.translate L v := Set.image_mono h

lemma le_of_translate_le_translate {K L : ConvexSpaceBody E} {v : E}
    (h : ConvexSpaceBody.translate K v ≤ ConvexSpaceBody.translate L v) : K ≤ L := by
  intro x hx
  have : v + x ∈ (ConvexSpaceBody.translate K v).carrier := ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hy_eq⟩ := h this
  have : y = x := add_left_cancel hy_eq
  exact this ▸ hy

@[simp]
lemma translate_le_translate_iff {K L : ConvexSpaceBody E} (v : E) :
    ConvexSpaceBody.translate K v ≤ ConvexSpaceBody.translate L v ↔ K ≤ L :=
  ⟨le_of_translate_le_translate, translate_le_translate v⟩

lemma ConvexSpaceBody.translate_translate {K : ConvexSpaceBody E} {v₁ v₂ : E} :
    ConvexSpaceBody.translate (ConvexSpaceBody.translate K v₂) v₁
      = ConvexSpaceBody.translate K (v₁ + v₂) := by
  ext1; simp [-Set.image_add_left, Set.image_image, add_assoc]

lemma ConvexSpaceBody.translate_neg_cancel {K : ConvexSpaceBody E} {v : E} :
    ConvexSpaceBody.translate (ConvexSpaceBody.translate K (-v)) v = K := by
  rw [K.translate_translate, add_neg_cancel, K.translate_zero]

lemma ConvexSpaceBody.neg_translate_cancel {K : ConvexSpaceBody E} {v : E} :
    ConvexSpaceBody.translate (ConvexSpaceBody.translate K v) (-v) = K := by
  rw [K.translate_translate, neg_add_cancel, K.translate_zero]

lemma ConvexSpaceBody.le_translate_iff {K L : ConvexSpaceBody E} (v : E) :
    K ≤ ConvexSpaceBody.translate L v ↔ K.translate (-v) ≤ L := by
  nth_rw 1 [← K.translate_neg_cancel (v := v), translate_le_translate_iff]

end


section IsEssentiallyDistinctTranslation

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `IsEssentiallyDistinct` is invariant under simultaneous left-translation
    of both sets by the same vector. The measure `volume` is left-invariant
    on a finite-dimensional inner product space (via the canonical Haar
    measure synthesised by `measureSpaceOfInnerProductSpace`). -/
lemma IsEssentiallyDistinct.image_add_left {U V : Set E} (v : E)
    (h : IsEssentiallyDistinct U V) :
    IsEssentiallyDistinct ((v + ·) '' U) ((v + ·) '' V) := by
  unfold IsEssentiallyDistinct at *
  have h_inj : Function.Injective ((v + ·) : E → E) := add_right_injective v
  rw [← Set.image_inter h_inj,
      MeasureTheory.measure_image_add, MeasureTheory.measure_image_add,
      MeasureTheory.measure_image_add]
  exact h

/-- Translation invariance of `IsEssentiallyDistinct` lifted to translated
    convex bodies. -/
lemma IsEssentiallyDistinct.translate_convexBody {K L : ConvexSpaceBody E} (v : E)
    (h : IsEssentiallyDistinct K.carrier L.carrier) :
    IsEssentiallyDistinct (ConvexSpaceBody.translate K v).carrier
      (ConvexSpaceBody.translate L v).carrier := by
  change IsEssentiallyDistinct ((v + ·) '' K.carrier) ((v + ·) '' L.carrier)
  exact IsEssentiallyDistinct.image_add_left v h

/-- Cross-shift translation invariance of `IsEssentiallyDistinct` on
convex body carriers. If `K` is essentially distinct from
`L + (w - v)`, then translating by `v` on the left and `w` on the right
yields essentially distinct sets. -/
lemma IsEssentiallyDistinct.translate_cross {K L : ConvexSpaceBody E}
    (v w : E)
    (h : IsEssentiallyDistinct K.carrier
      (ConvexSpaceBody.translate L (w - v)).carrier) :
    IsEssentiallyDistinct (ConvexSpaceBody.translate K v).carrier
      (ConvexSpaceBody.translate L w).carrier := by
  have h' := IsEssentiallyDistinct.translate_convexBody v h
  -- Rewrite the RHS via `translate_translate` and `add_sub_cancel`.
  have hLeq : ConvexSpaceBody.translate (ConvexSpaceBody.translate L (w - v)) v
      = ConvexSpaceBody.translate L w := by
    rw [ConvexSpaceBody.translate_translate, add_sub_cancel]
  rw [hLeq] at h'
  exact h'

end IsEssentiallyDistinctTranslation
@[expose] public section AffineImage

variable
  {V P : Type*} [TopologicalSpace P] [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
  {W Q : Type*} [TopologicalSpace Q] [AddCommGroup W] [Module ℝ W] [AddTorsor W Q]

@[expose] public section

/-- The image of a convex body under a continuous affine map of real affine spaces is a convex
body. This applies to affine subspaces (e.g. the codomain of an affine orthogonal projection), not
only vector spaces. -/
@[simps]
def ConvexSpaceBody.affineImage (f : P →ᵃ[ℝ] Q) (hf : Continuous f)
    (K : ConvexSpaceBody P) : ConvexSpaceBody Q where
  carrier := f '' K.carrier
  convex' := K.convex'.affineMap_image f
  isCompact' := K.isCompact'.image hf
  nonempty' := K.nonempty'.image f

@[simp]
lemma ConvexSpaceBody.coe_affineImage (f : P →ᵃ[ℝ] Q) (hf : Continuous f)
    (K : ConvexSpaceBody P) :
    SetLike.coe (K.affineImage f hf) = f '' K.carrier := rfl

end

end AffineImage
