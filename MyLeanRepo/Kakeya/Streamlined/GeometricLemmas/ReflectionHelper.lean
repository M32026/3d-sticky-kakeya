import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Coordinate reflection isometry

A linear isometry that negates a single coordinate. Used to reduce
negative-direction tubes to positive-direction ones before applying
axis-aligned packing bounds.
-/

noncomputable section

open Kakeya.Streamlined MeasureTheory

namespace Kakeya.Streamlined.GeometricLemmas

/-- Negate coordinate `i`, leaving all other coordinates unchanged.

Constructed as `x ↦ x - 2 • e_i * x_i`, where `e_i` is the `i`-th standard
basis vector. -/
def reflectCoord (i : Fin 3) : Point3 ≃ₗᵢ[ℝ] Point3 :=
  let f : Point3 → Point3 := fun x => x - (2 : ℝ) • EuclideanSpace.single i (x i)
  have h_invol : ∀ (x : Point3), f (f x) = x := by
    intro x
    apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;> simp [f, EuclideanSpace.single_apply] <;> ring
  have h_add : ∀ (x y : Point3), f (x + y) = f x + f y := by
    intro x y
    apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;> simp [f, EuclideanSpace.single_apply, Pi.add_apply] <;> ring
  have h_smul : ∀ (c : ℝ) (x : Point3), f (c • x) = c • f x := by
    intro c x
    apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;> simp [f, EuclideanSpace.single_apply, Pi.smul_apply] <;> ring
  have h_norm : ∀ (x : Point3), ‖f x‖ = ‖x‖ := by
    intro x
    have h1 : ∀ (j : Fin 3), (f x j) ^ 2 = (x j) ^ 2 := by
      intro j
      fin_cases i <;> fin_cases j <;> simp [f, EuclideanSpace.single_apply] <;> ring
    have h_real : ∀ (r : ℝ), ‖r‖ ^ 2 = r ^ 2 := by
      intro r
      have h : ‖r‖ = |r| := Real.norm_eq_abs r
      rw [h, sq_abs]
    have h3 : ‖f x‖ ^ 2 = ∑ j : Fin 3, ‖f x j‖ ^ 2 := EuclideanSpace.norm_sq_eq (f x)
    have h4 : ‖x‖ ^ 2 = ∑ j : Fin 3, ‖x j‖ ^ 2 := EuclideanSpace.norm_sq_eq x
    have h5 : ∑ j : Fin 3, ‖f x j‖ ^ 2 = ∑ j : Fin 3, ‖x j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h_real (f x j), h_real (x j), h1 j]
    have h6 : ‖f x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [h3, h4, h5]
    have h7 : 0 ≤ ‖f x‖ := by positivity
    have h8 : 0 ≤ ‖x‖ := by positivity
    nlinarith
  { toFun := f
    invFun := f
    left_inv := h_invol
    right_inv := h_invol
    map_add' := h_add
    map_smul' := h_smul
    norm_map' := h_norm }

/-- Reflection is an involution. -/
lemma reflectCoord_involution (i : Fin 3) (x : Point3) :
    reflectCoord i (reflectCoord i x) = x :=
  (reflectCoord i).left_inv x

/-- Coordinate-wise action of the reflection. -/
lemma reflectCoord_apply (i : Fin 3) (x : Point3) (j : Fin 3) :
    (reflectCoord i x) j = if j = i then -(x j) else x j := by
  have h : (reflectCoord i x) j = (x - (2 : ℝ) • EuclideanSpace.single i (x i)) j := by rfl
  rw [h]
  have h2 : (x - (2 : ℝ) • EuclideanSpace.single i (x i)) j =
      x j - 2 * (EuclideanSpace.single i (x i) j) := by
    simp [Pi.sub_apply, Pi.smul_apply]
    <;> ring
  rw [h2, EuclideanSpace.single_apply i (x i) j]
  by_cases h3 : j = i
  · have h4 : x j = x i := by rw [h3]
    simp [h3, h4] <;> ring
  · simp [h3] <;> ring

/-- Reflection preserves absolute values of all coordinates. -/
lemma reflectCoord_abs (i : Fin 3) (x : Point3) (j : Fin 3) :
    |(reflectCoord i x) j| = |x j| := by
  rw [reflectCoord_apply i x j]
  by_cases h : j = i
  · rw [if_pos h, abs_neg]
  · rw [if_neg h]

/-- Reflection preserves the symmetric axis box. -/
lemma reflectCoord_preserves_axisBox (i : Fin 3) (a b c : ℝ) :
    reflectCoord i '' axisBox a b c = axisBox a b c := by
  ext z
  simp only [Set.mem_image, axisBox, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h0 := reflectCoord_abs i x 0
    have h1 := reflectCoord_abs i x 1
    have h2 := reflectCoord_abs i x 2
    rw [h0, h1, h2] at * <;> exact hx
  · intro hz
    refine ⟨reflectCoord i z, ?_, ?_⟩
    · have h0 := reflectCoord_abs i z 0
      have h1 := reflectCoord_abs i z 1
      have h2 := reflectCoord_abs i z 2
      rw [h0, h1, h2] at * <;> exact hz
    · exact reflectCoord_involution i z

/-- Apply a linear isometry to a delta-tube: map base and direction. -/
def mapTube (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    Kakeya.DeltaTube δ where
  base := e T.base
  direction := e T.direction
  direction_unit := by
    have h : ‖e T.direction‖ = ‖T.direction‖ := e.norm_map T.direction
    rw [h, T.direction_unit]

/-- The carrier of a mapped tube is the image of the original carrier. -/
lemma mapTube_carrier (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    (T : Kakeya.DeltaTube δ) :
    (mapTube e T).carrier = e '' T.carrier := by
  simp only [mapTube, Kakeya.DeltaTube.carrier]
  have h_lin : ∀ (t : ℝ), e (T.base + t • T.direction) = e T.base + t • e T.direction := by
    intro t
    have h1 : e (T.base + t • T.direction) = e T.base + e (t • T.direction) := by
      exact e.toLinearEquiv.map_add T.base (t • T.direction)
    have h2 : e (t • T.direction) = t • e T.direction := by
      exact e.toLinearEquiv.map_smul t T.direction
    rw [h1, h2]
  have h_seg : e '' Kakeya.unitSegment T.base T.direction =
      Kakeya.unitSegment (e T.base) (e T.direction) := by
    dsimp only [Kakeya.unitSegment]
    rw [Set.image_image]
    apply Set.image_congr
    intro t _
    exact h_lin t
  have h_comm : ∀ (r : ℝ) (s : Set Point3),
      e '' Metric.cthickening r s = Metric.cthickening r (e '' s) := by
    intro r s
    ext z
    simp only [Set.mem_image, Metric.mem_cthickening_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_inf : Metric.infEDist (e x) (e '' s) ≤ ENNReal.ofReal r := by
        have h : Metric.infEDist (e x) (e '' s) = Metric.infEDist x s :=
          Metric.infEDist_image (hΦ := e.isometry)
        rw [h]
        exact hx
      exact h_inf
    · intro hz
      refine ⟨e.symm z, ?_, ?_⟩
      · have h : Metric.infEDist (e.symm z) s ≤ ENNReal.ofReal r := by
          have h21 : Metric.infEDist (e (e.symm z)) (e '' s) = Metric.infEDist (e.symm z) s :=
            Metric.infEDist_image (hΦ := e.isometry)
          have h22 : e (e.symm z) = z := e.apply_symm_apply z
          rw [h22] at h21
          rw [←h21]
          exact hz
        exact h
      · have h3 : e (e.symm z) = z := e.apply_symm_apply z
        rw [h3]
  rw [h_comm δ (Kakeya.unitSegment T.base T.direction), h_seg]

/-- A linear isometry preserves tube volume. -/
lemma mapTube_volume (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    (T : Kakeya.DeltaTube δ) :
    (mapTube e T).volume = T.volume := by
  rw [Kakeya.DeltaTube.volume, mapTube_carrier e T, Kakeya.DeltaTube.volume]
  have h_meas : MeasurableSet T.carrier := Metric.isClosed_cthickening.measurableSet
  have h_mp_symm : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  have h_image_eq : e '' T.carrier = e.symm ⁻¹' T.carrier := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h9 : e.symm (e x) = x := e.symm_apply_apply x
      simpa [h9] using hx
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
  rw [h_image_eq]
  exact MeasureTheory.MeasurePreserving.measure_preimage h_mp_symm h_meas.nullMeasurableSet

/-- A linear isometry preserves essential distinctness of tubes. -/
lemma mapTube_essentiallyDistinct (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    (T U : Kakeya.DeltaTube δ) :
    T.EssentiallyDistinct U ↔ (mapTube e T).EssentiallyDistinct (mapTube e U) := by
  simp only [Kakeya.DeltaTube.EssentiallyDistinct]
  have h_inter_img : e '' (T.carrier ∩ U.carrier) = (e '' T.carrier) ∩ (e '' U.carrier) := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, ⟨hxT, hxU⟩, rfl⟩
      exact ⟨⟨x, hxT, rfl⟩, ⟨x, hxU, rfl⟩⟩
    · rintro ⟨⟨x, hxT, rfl⟩, ⟨y, hyU, hy⟩⟩
      have h_eq : x = y := e.injective hy.symm
      have hyU' : x ∈ U.carrier := by
        exact h_eq.symm ▸ hyU
      exact ⟨x, ⟨hxT, hyU'⟩, rfl⟩
  have h_inter : (mapTube e T).carrier ∩ (mapTube e U).carrier = e '' (T.carrier ∩ U.carrier) := by
    rw [mapTube_carrier e T, mapTube_carrier e U]
    exact h_inter_img.symm
  have h_meas : MeasurableSet (T.carrier ∩ U.carrier) :=
    Metric.isClosed_cthickening.measurableSet.inter Metric.isClosed_cthickening.measurableSet
  have h_mp_symm : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  have h_image_eq : e '' (T.carrier ∩ U.carrier) = e.symm ⁻¹' (T.carrier ∩ U.carrier) := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h9 : e.symm (e x) = x := e.symm_apply_apply x
      simpa [h9] using hx
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
  have h_vol_inter : volume ((mapTube e T).carrier ∩ (mapTube e U).carrier) =
      volume (T.carrier ∩ U.carrier) := by
    rw [h_inter, h_image_eq]
    exact MeasureTheory.MeasurePreserving.measure_preimage h_mp_symm h_meas.nullMeasurableSet
  have h_volT : (mapTube e T).volume = T.volume := mapTube_volume e T
  have h_volU : (mapTube e U).volume = U.volume := mapTube_volume e U
  rw [h_vol_inter, h_volT, h_volU]

end Kakeya.Streamlined.GeometricLemmas
