import MyLeanRepo.Kakeya.Geometry.OuterJohnEllipsoid
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.EllipsoidProps
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Transport of John ellipsoids under linear isometries

This module proves that the outer John ellipsoid of a convex body transports
naturally under a linear isometry equivalence: if `e : E n ≃ₗᵢ[ℝ] E n` is a
linear isometry and `K` is a convex body, then the outer John ellipsoid of
`e '' K` is exactly `e ''` (outer John ellipsoid of `K`).

The key steps are:
1. `IsConvexBody` is preserved by linear isometries.
2. The image of an ellipsoid under `e` is an ellipsoid with conjugated linear map.
3. The `IsOuterJohnEllipsoid` minimality property transports by pulling back
   candidate ellipsoids through `e.symm`.
4. The uniqueness theorem for outer John ellipsoids gives set-level equality.
-/

noncomputable section

open JohnEllipsoid MeasureTheory

namespace JohnEllipsoid

variable {n : ℕ} {K : Set (E n)} (e : E n ≃ₗᵢ[ℝ] E n)

/-- The conjugate linear equivalence `e ∘ A ∘ e.symm`. -/
def conj (A : E n ≃ₗ[ℝ] E n) : E n ≃ₗ[ℝ] E n :=
  e.toLinearEquiv.symm.trans A |>.trans e.toLinearEquiv

theorem conj_apply (A : E n ≃ₗ[ℝ] E n) (x : E n) :
    (conj e A) x = e (A (e.symm x)) := by
  rfl

/-- A linear isometry maps an ellipsoid to an ellipsoid. -/
theorem image_ellipsoid (c : E n) (A : E n ≃ₗ[ℝ] E n) :
    e '' JohnEllipsoid.ellipsoid c A =
    JohnEllipsoid.ellipsoid (e c) (conj e A) := by
  let ball : Set (E n) := Metric.closedBall (0 : E n) 1
  have hmem : ∀ (z : E n), z ∈ ball ↔ ‖z‖ ≤ 1 := by
    intro z; simp [ball, Metric.mem_closedBall]
  have hball : e.symm '' ball = ball := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h' : ‖e.symm y‖ = ‖y‖ := e.symm.norm_map y
      have h : ‖e.symm y‖ ≤ 1 := by rw [h']; exact (hmem y).mp hy
      exact (hmem (e.symm y)).mpr h
    · intro hx
      have h' : ‖e x‖ = ‖x‖ := e.norm_map x
      have h : ‖e x‖ ≤ 1 := by rw [h']; exact (hmem x).mp hx
      exact ⟨e x, (hmem (e x)).mpr h, by simp⟩
  have h1 : e '' ((fun x : E n => c + x) '' (A '' ball)) =
      (fun y : E n => e c + y) '' (e '' (A '' ball)) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨e w, ⟨w, hw, rfl⟩, by simp [map_add]⟩
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨c + x, ⟨x, hx, rfl⟩, by simp [map_add]⟩
  have h2 : e '' (A '' ball) = (e ∘ A) '' ball := by
    rw [Set.image_image]
    ; rfl
  have h3 : (e ∘ A) '' ball = (conj e A) '' ball := by
    ext z
    simp only [Set.mem_image, conj_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h' : ‖e x‖ = ‖x‖ := e.norm_map x
      have h : ‖e x‖ ≤ 1 := by rw [h']; exact (hmem x).mp hx
      exact ⟨e x, (hmem (e x)).mpr h, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      have h' : ‖e.symm w‖ = ‖w‖ := e.symm.norm_map w
      have h : ‖e.symm w‖ ≤ 1 := by rw [h']; exact (hmem w).mp hw
      exact ⟨e.symm w, (hmem (e.symm w)).mpr h, by simp⟩
  have h_main : e '' JohnEllipsoid.ellipsoid c A =
      (fun y : E n => e c + y) '' ((conj e A) '' ball) := by
    calc
      e '' JohnEllipsoid.ellipsoid c A
        = e '' ((fun x : E n => c + x) '' (A '' ball)) := by rfl
      _ = (fun y : E n => e c + y) '' (e '' (A '' ball)) := h1
      _ = (fun y : E n => e c + y) '' ((e ∘ A) '' ball) := by rw [h2]
      _ = (fun y : E n => e c + y) '' ((conj e A) '' ball) := by rw [h3]
  rw [h_main]
  ; rfl

/-- Linear isometries preserve the convex body property. -/
theorem IsConvexBody_image
    (hK : JohnEllipsoid.IsConvexBody K) :
    JohnEllipsoid.IsConvexBody (e '' K) := by
  rcases hK with ⟨hconv, hcompact, hinterior⟩
  have hconv' : Convex ℝ (e '' K) :=
    hconv.linear_image (e : E n →ₗ[ℝ] E n)
  have hcompact' : IsCompact (e '' K) :=
    hcompact.image e.continuous
  have h_int : (e '' interior K) = interior (e '' K) :=
    e.toHomeomorph.image_interior K
  have h' : (e '' interior K).Nonempty := hinterior.image e
  have hinterior' : (interior (e '' K)).Nonempty := by
    rw [← h_int]
    exact h'
  exact ⟨hconv', hcompact', hinterior'⟩

/-- Volume of image of an ellipsoid under a linear isometry. -/
theorem volume_image_ellipsoid (c : E n) (A : E n ≃ₗ[ℝ] E n) :
    volume (e '' JohnEllipsoid.ellipsoid c A) =
    volume (JohnEllipsoid.ellipsoid c A) := by
  have hpres : MeasurePreserving e volume volume :=
    LinearIsometryEquiv.measurePreserving e
  have hmap : Measure.map e volume = volume := hpres.map_eq
  have hc : IsCompact (JohnEllipsoid.ellipsoid c A) := ellipsoid_compact
  have hms : MeasurableSet (JohnEllipsoid.ellipsoid c A) := hc.measurableSet
  have hms2 : MeasurableSet (e '' JohnEllipsoid.ellipsoid c A) :=
    hc.image e.continuous |>.measurableSet
  have h_inj : e ⁻¹' (e '' JohnEllipsoid.ellipsoid c A) =
      JohnEllipsoid.ellipsoid c A := by
    ext x
    simp [e.injective]
  have h_eq1 : volume (e '' JohnEllipsoid.ellipsoid c A) =
      Measure.map e volume (e '' JohnEllipsoid.ellipsoid c A) := by
    rw [hmap]
  have h_eq2 : Measure.map e volume (e '' JohnEllipsoid.ellipsoid c A) =
      volume (e ⁻¹' (e '' JohnEllipsoid.ellipsoid c A)) :=
    Measure.map_apply e.continuous.measurable hms2
  rw [h_eq1, h_eq2, h_inj]

/-- The `IsOuterJohnEllipsoid` property transports under linear isometries. -/
theorem IsOuterJohnEllipsoid_image
    {c : E n} {A : E n ≃ₗ[ℝ] E n}
    (h : JohnEllipsoid.IsOuterJohnEllipsoid K c A) :
    JohnEllipsoid.IsOuterJohnEllipsoid (e '' K) (e c) (conj e A) := by
  have h1 : e '' K ⊆ e '' JohnEllipsoid.ellipsoid c A := by
    intro x hx
    rcases hx with ⟨x', hx', rfl⟩
    exact ⟨x', h.1 hx', rfl⟩
  rw [image_ellipsoid e c A] at h1
  constructor
  · exact h1
  · intro c' A' hsub
    have hsub1 : K ⊆ e.symm '' JohnEllipsoid.ellipsoid c' A' := by
      intro x hx
      have h4 : e x ∈ e '' K := ⟨x, hx, rfl⟩
      have h5 : e x ∈ JohnEllipsoid.ellipsoid c' A' := hsub h4
      exact ⟨e x, h5, by simp⟩
    have hellip : e.symm '' JohnEllipsoid.ellipsoid c' A' =
        JohnEllipsoid.ellipsoid (e.symm c') (conj e.symm A') :=
      image_ellipsoid e.symm c' A'
    have hsub2 : K ⊆ JohnEllipsoid.ellipsoid (e.symm c') (conj e.symm A') := by
      rw [← hellip]
      exact hsub1
    have h2 := h.2 (e.symm c') (conj e.symm A') hsub2
    have hvol1 : volume (JohnEllipsoid.ellipsoid (e c) (conj e A)) =
        volume (JohnEllipsoid.ellipsoid c A) := by
      rw [← image_ellipsoid e c A, volume_image_ellipsoid e c A]
    have hvol2 : volume (JohnEllipsoid.ellipsoid (e.symm c') (conj e.symm A')) =
        volume (JohnEllipsoid.ellipsoid c' A') := by
      rw [← image_ellipsoid e.symm c' A', volume_image_ellipsoid e.symm c' A']
    calc
      volume (JohnEllipsoid.ellipsoid (e c) (conj e A))
        = volume (JohnEllipsoid.ellipsoid c A) := hvol1
      _ ≤ volume (JohnEllipsoid.ellipsoid (e.symm c') (conj e.symm A')) := h2
      _ = volume (JohnEllipsoid.ellipsoid c' A') := hvol2

/-- The outer John ellipsoid set transports under linear isometries. -/
theorem outerJohnEllipsoid_image
    (hK : JohnEllipsoid.IsConvexBody K) :
    (IsConvexBody_image e hK).outerJohnEllipsoid = e '' hK.outerJohnEllipsoid := by
  let hImg : JohnEllipsoid.IsConvexBody (e '' K) := IsConvexBody_image e hK
  have hspec : JohnEllipsoid.IsOuterJohnEllipsoid K
      hK.outerJohnEllipsoidCenter hK.outerJohnEllipsoidMap :=
    hK.outerJohnEllipsoid_spec
  have htrans : JohnEllipsoid.IsOuterJohnEllipsoid (e '' K)
      (e hK.outerJohnEllipsoidCenter)
      (conj e hK.outerJohnEllipsoidMap) :=
    IsOuterJohnEllipsoid_image e hspec
  have h_unique : JohnEllipsoid.ellipsoid (e hK.outerJohnEllipsoidCenter)
        (conj e hK.outerJohnEllipsoidMap) =
      hImg.outerJohnEllipsoid :=
    JohnEllipsoid.IsConvexBody.outerJohnEllipsoid_unique hImg _ _ htrans
  have h_final : hImg.outerJohnEllipsoid =
      e '' hK.outerJohnEllipsoid := by
    rw [← h_unique]
    exact (image_ellipsoid e hK.outerJohnEllipsoidCenter hK.outerJohnEllipsoidMap).symm
  exact h_final

end JohnEllipsoid

end
