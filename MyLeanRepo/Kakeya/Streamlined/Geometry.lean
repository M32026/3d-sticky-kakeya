import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Geometric objects for the streamlined three-dimensional Kakeya proof

This file contains data definitions only.  In particular, it does not assert
the existence of John ellipsoids or any Kakeya estimate.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- The ambient Euclidean space. -/
abbrev Point3 := Kakeya.Point3

/-- An axis-parallel box centered at the origin, with the displayed side lengths. -/
def axisBox (a b c : ℝ) : Set Point3 :=
  {x |
    |x (0 : Fin 3)| ≤ a / 2 ∧
    |x (1 : Fin 3)| ≤ b / 2 ∧
    |x (2 : Fin 3)| ≤ c / 2}

/--
A geometric body is represented by its carrier.  Measurability and convexity
are predicates rather than fields, so the same indexed-family API can also be
used for intermediate measurable sets that are not convex.
-/
structure Body where
  carrier : Set Point3

namespace Body

/-- The body is Lebesgue measurable. -/
def IsMeasurable (K : Body) : Prop :=
  MeasurableSet K.carrier

/-- The body is convex. -/
def IsConvex (K : Body) : Prop :=
  Convex ℝ K.carrier

/-- Lebesgue volume of a body. -/
def volume (K : Body) : ENNReal :=
  MeasureTheory.volume K.carrier

/--
`K` has dimensions `a × b × c` in the specified rigid frame, up to the
multiplicative enlargement `A`.
-/
def HasDimensionsInFrame (K : Body) (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (a b c A : ℝ) : Prop :=
  0 < a ∧ a ≤ b ∧ b ≤ c ∧ 1 ≤ A ∧
    frame '' axisBox a b c ⊆ K.carrier ∧
    K.carrier ⊆ frame '' axisBox (A * a) (A * b) (A * c)

/--
`K` has Euclidean dimensions `a × b × c` up to factor `A`.  Only affine
isometries are allowed, so the numerical dimensions cannot be changed by an
arbitrary linear rescaling.
-/
def HasDimensions (K : Body) (a b c A : ℝ) : Prop :=
  ∃ frame : Point3 ≃ᵃⁱ[ℝ] Point3,
    HasDimensionsInFrame K frame a b c A

/-- A body comparable to an `a × b × 1` plank. -/
def IsPlank (K : Body) (a b A : ℝ) : Prop :=
  HasDimensions K a b 1 A

/-- A body comparable to a `θ × 1 × 1` slab. -/
def IsSlab (K : Body) (θ A : ℝ) : Prop :=
  HasDimensions K θ 1 1 A

/--
The rigid frame obtained after isotropic scaling by `r > 0`.

Its linear isometry is unchanged; only the frame center is multiplied by `r`.
-/
def scaledFrame (frame : Point3 ≃ᵃⁱ[ℝ] Point3) (r : ℝ) (hr : 0 < r) :
    Point3 ≃ᵃⁱ[ℝ] Point3 :=
  AffineIsometryEquiv.mk'
    (fun x : Point3 => frame.linearIsometryEquiv x + r • frame 0)
    frame.linearIsometryEquiv
    (0 : Point3)
    (by intro x; simp [vadd_eq_add])

/-- Scaling an axisBox by `r > 0`. -/
lemma axisBox_scale (e : Point3 → Point3) {r a b c : ℝ} (hr : 0 < r)
    (h_e : ∀ x, e x = r • x) :
    e '' axisBox a b c = axisBox (r * a) (r * b) (r * c) := by
  ext y
  simp only [Set.mem_image, axisBox, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨h1, h2, h3⟩, rfl⟩
    have h4 : ∀ (i : Fin 3) (v : ℝ), |x i| ≤ v / 2 → |(e x) i| ≤ (r * v) / 2 := by
      intro i v hv
      have h5 : (e x) i = r * (x i) := by rw [h_e x] <;> rfl
      rw [h5, abs_mul, abs_of_pos hr]
      have h6 : r * |x i| ≤ r * (v / 2) := mul_le_mul_of_nonneg_left hv hr.le
      have h7 : r * (v / 2) = (r * v) / 2 := by ring
      rw [h7] at h6; exact h6
    exact ⟨h4 0 a h1, h4 1 b h2, h4 2 c h3⟩
  · rintro ⟨h1, h2, h3⟩
    let x : Point3 := (1 / r) • y
    have hx1 : |x 0| ≤ a / 2 := by
      have h : x 0 = (1 / r) * y 0 := by simp [x] <;> rfl
      rw [h]
      have h5 : |(1 / r) * y 0| = (1 / r) * |y 0| := by
        rw [abs_mul, abs_of_pos (show 0 < 1 / r by positivity)]
      rw [h5]
      have h6 : (1 / r) * |y 0| ≤ (1 / r) * ((r * a) / 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      have h7 : (1 / r) * ((r * a) / 2) = a / 2 := by field_simp [hr.ne'] <;> ring
      rw [h7] at h6; exact h6
    have hx2 : |x 1| ≤ b / 2 := by
      have h : x 1 = (1 / r) * y 1 := by simp [x] <;> rfl
      rw [h]
      have h5 : |(1 / r) * y 1| = (1 / r) * |y 1| := by
        rw [abs_mul, abs_of_pos (show 0 < 1 / r by positivity)]
      rw [h5]
      have h6 : (1 / r) * |y 1| ≤ (1 / r) * ((r * b) / 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      have h7 : (1 / r) * ((r * b) / 2) = b / 2 := by field_simp [hr.ne'] <;> ring
      rw [h7] at h6; exact h6
    have hx3 : |x 2| ≤ c / 2 := by
      have h : x 2 = (1 / r) * y 2 := by simp [x] <;> rfl
      rw [h]
      have h5 : |(1 / r) * y 2| = (1 / r) * |y 2| := by
        rw [abs_mul, abs_of_pos (show 0 < 1 / r by positivity)]
      rw [h5]
      have h6 : (1 / r) * |y 2| ≤ (1 / r) * ((r * c) / 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
      have h7 : (1 / r) * ((r * c) / 2) = c / 2 := by field_simp [hr.ne'] <;> ring
      rw [h7] at h6; exact h6
    have h9 : e x = y := by
      rw [h_e x]
      have h10 : r • x = y := by
        have h11 : r • x = r • ((1 / r) • y) := by rfl
        rw [h11, smul_smul]
        have h12 : r * (1 / r) = 1 := by field_simp [hr.ne'] <;> ring
        rw [h12, one_smul]
      exact h10
    exact ⟨x, ⟨hx1, hx2, hx3⟩, h9⟩

/--
Transport `HasDimensionsInFrame` under isotropic scaling by `r > 0`.

If `K` has dimensions `a × b × c` in frame `frame`, then `e '' K` has
dimensions `r*a × r*b × r*c` in `scaledFrame frame r hr`, where `e x = r • x`.
-/
lemma HasDimensionsInFrame.scale
    {K : Body} {frame : Point3 ≃ᵃⁱ[ℝ] Point3}
    {a b c A r : ℝ} (hr : 0 < r)
    (e : Point3 → Point3) (h_e : ∀ x, e x = r • x)
    (h : K.HasDimensionsInFrame frame a b c A) :
    Body.HasDimensionsInFrame
      (⟨e '' K.carrier⟩)
      (scaledFrame frame r hr)
      (r * a) (r * b) (r * c) A := by
  let frame' := scaledFrame frame r hr
  let K' : Body := ⟨e '' K.carrier⟩
  have h_e_apply : ∀ x, e x = r • x := h_e
  have h_decomp : ∀ x : Point3, frame x = frame.linearIsometryEquiv x + frame 0 := by
    intro x
    let e_aff : Point3 ≃ᵃ[ℝ] Point3 := frame
    have h_map : e_aff (x +ᵥ (0 : Point3)) = e_aff.linear x +ᵥ e_aff 0 :=
      AffineEquiv.map_vadd e_aff (0 : Point3) x
    have h1 : x +ᵥ (0 : Point3) = x := by ext i; simp
    have h2 : e_aff.linear x +ᵥ e_aff 0 = e_aff.linear x + e_aff 0 := by ext i; simp
    have h3 : e_aff.linear x = frame.linearIsometryEquiv x := by rfl
    rw [h1, h2, h3] at h_map
    exact h_map
  have h_frame'_apply : ∀ y : Point3, frame' y = frame.linearIsometryEquiv y + r • frame 0 := by
    intro y; rfl
  have h_comm : ∀ x : Point3, e (frame x) = frame' (e x) := by
    intro x
    calc
      e (frame x) = r • frame x := by rw [h_e_apply]
      _ = r • (frame.linearIsometryEquiv x + frame 0) := by rw [h_decomp x]
      _ = frame.linearIsometryEquiv (r • x) + r • frame 0 := by
        rw [smul_add, ← frame.linearIsometryEquiv.map_smul r x]
        <;> rfl
      _ = frame' (e x) := by
        rw [h_frame'_apply, h_e_apply] <;> rfl
  have h_axisBox_scaling : e '' axisBox a b c = axisBox (r * a) (r * b) (r * c) := by
    ext y
    simp only [Set.mem_image, axisBox, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨h1, h2, h3⟩, rfl⟩
      have h4 : ∀ (i : Fin 3) (v : ℝ), |x i| ≤ v / 2 → |(e x) i| ≤ (r * v) / 2 := by
        intro i v hv
        have h5 : (e x) i = r * (x i) := by
          simp [h_e_apply]
        rw [h5, abs_mul, abs_of_pos hr]
        have h6 : r * |x i| ≤ r * (v / 2) := mul_le_mul_of_nonneg_left hv hr.le
        have h7 : r * (v / 2) = (r * v) / 2 := by ring
        rw [h7] at h6; exact h6
      exact ⟨h4 0 a h1, h4 1 b h2, h4 2 c h3⟩
    · rintro ⟨h1, h2, h3⟩
      let x : Point3 := (1 / r) • y
      have hx1 : |x 0| ≤ a / 2 := by
        simp only [x, smul_eq_mul] at *
        <;> have h : x 0 = (1 / r) * y 0 := by simp [x] <;> rfl
        rw [h]
        have h5 : |y 0| ≤ (r * a) / 2 := h1
        have h6 : (1 / r) * |y 0| ≤ (1 / r) * ((r * a) / 2) := mul_le_mul_of_nonneg_left h5 (by positivity)
        have h7 : |(1 / r) * y 0| = (1 / r) * |y 0| := by
          rw [abs_mul, abs_of_pos (show 0 < 1 / r by positivity)]
        rw [h7]
        have h8 : (1 / r) * ((r * a) / 2) = a / 2 := by
          field_simp [hr.ne'] <;> ring
        rw [h8] at h6; exact h6
      have hx2 : |x 1| ≤ b / 2 := by
        simp only [x, smul_eq_mul] at *
        <;> have h : x 1 = (1 / r) * y 1 := by simp [x] <;> rfl
        rw [h]
        have h5 : |y 1| ≤ (r * b) / 2 := h2
        have h6 : (1 / r) * |y 1| ≤ (1 / r) * ((r * b) / 2) := mul_le_mul_of_nonneg_left h5 (by positivity)
        have h7 : |(1 / r) * y 1| = (1 / r) * |y 1| := by
          rw [abs_mul, abs_of_pos (show 0 < 1 / r by positivity)]
        rw [h7]
        have h8 : (1 / r) * ((r * b) / 2) = b / 2 := by
          field_simp [hr.ne'] <;> ring
        rw [h8] at h6; exact h6
      have hx3 : |x 2| ≤ c / 2 := by
        simp only [x, smul_eq_mul] at *
        <;> have h : x 2 = (1 / r) * y 2 := by simp [x] <;> rfl
        rw [h]
        have h5 : |y 2| ≤ (r * c) / 2 := h3
        have h6 : (1 / r) * |y 2| ≤ (1 / r) * ((r * c) / 2) := mul_le_mul_of_nonneg_left h5 (by positivity)
        have h7 : |(1 / r) * y 2| = (1 / r) * |y 2| := by
          rw [abs_mul, abs_of_pos (show 0 < 1 / r by positivity)]
        rw [h7]
        have h8 : (1 / r) * ((r * c) / 2) = c / 2 := by
          field_simp [hr.ne'] <;> ring
        rw [h8] at h6; exact h6
      have h9 : e x = y := by
        have h10 : e x = r • x := h_e_apply x
        rw [h10]
        have h11 : r • x = y := by
          simp [x]
          <;> ext i
          <;> simp [smul_smul]
          <;> field_simp [hr.ne'] <;> ring
        exact h11
      exact ⟨x, ⟨hx1, hx2, hx3⟩, h9⟩
  have h_inner : frame '' axisBox a b c ⊆ K.carrier := h.2.2.2.2.1
  have h_outer : K.carrier ⊆ frame '' axisBox (A * a) (A * b) (A * c) := h.2.2.2.2.2
  have h_func1 : (frame' ∘ e) = (e ∘ frame) :=
    Eq.symm (Function.Semiconj.comp_eq h_comm)
  have h_func2 : (e ∘ frame) = (frame' ∘ e) :=
    Function.Semiconj.comp_eq h_comm
  have h_img1 : ∀ (s : Set Point3), frame' '' (e '' s) = (frame' ∘ e) '' s :=
    fun s => Set.image_image frame' e s
  have h_img2 : ∀ (s : Set Point3), e '' (frame '' s) = (e ∘ frame) '' s :=
    fun s => Set.image_image e frame s
  have h_axisBox_outer0 : e '' axisBox (A * a) (A * b) (A * c) =
      axisBox (r * (A * a)) (r * (A * b)) (r * (A * c)) :=
    axisBox_scale e (r := r) (a := A * a) (b := A * b) (c := A * c) hr h_e_apply
  have h_axisBox_outer : e '' axisBox (A * a) (A * b) (A * c) =
      axisBox (A * (r * a)) (A * (r * b)) (A * (r * c)) := by
    rw [h_axisBox_outer0]
    have h1 : r * (A * a) = A * (r * a) := by ring
    have h2 : r * (A * b) = A * (r * b) := by ring
    have h3 : r * (A * c) = A * (r * c) := by ring
    rw [h1, h2, h3]
  have h_inner' : frame' '' axisBox (r * a) (r * b) (r * c) ⊆ K'.carrier := by
    have h_eq : frame' '' axisBox (r * a) (r * b) (r * c) = e '' (frame '' axisBox a b c) := by
      calc
        frame' '' axisBox (r * a) (r * b) (r * c)
          = frame' '' (e '' axisBox a b c) := by rw [h_axisBox_scaling]
        _ = (frame' ∘ e) '' axisBox a b c := by rw [h_img1]
        _ = (e ∘ frame) '' axisBox a b c := by rw [h_func1]
        _ = e '' (frame '' axisBox a b c) := by rw [h_img2]
    rw [h_eq]
    exact Set.image_mono h_inner
  have h_outer' : K'.carrier ⊆ frame' '' axisBox (A * (r * a)) (A * (r * b)) (A * (r * c)) := by
    have h_eq : e '' (frame '' axisBox (A * a) (A * b) (A * c)) =
        frame' '' axisBox (A * (r * a)) (A * (r * b)) (A * (r * c)) := by
      calc
        e '' (frame '' axisBox (A * a) (A * b) (A * c))
          = (e ∘ frame) '' axisBox (A * a) (A * b) (A * c) := by rw [h_img2]
        _ = (frame' ∘ e) '' axisBox (A * a) (A * b) (A * c) := by rw [h_func2]
        _ = frame' '' (e '' axisBox (A * a) (A * b) (A * c)) := by rw [h_img1]
        _ = frame' '' axisBox (A * (r * a)) (A * (r * b)) (A * (r * c)) := by rw [h_axisBox_outer]
    have h : e '' K.carrier ⊆ e '' (frame '' axisBox (A * a) (A * b) (A * c)) :=
      Set.image_mono h_outer
    rw [h_eq] at h
    exact h
  exact ⟨mul_pos hr h.1,
    mul_le_mul_of_nonneg_left h.2.1 hr.le,
    mul_le_mul_of_nonneg_left h.2.2.1 hr.le,
    h.2.2.2.1,
    h_inner',
    h_outer'⟩

/--
Transport `HasDimensionsInFrame` under translation then isotropic scaling.

If `K` has dimensions `a × b × c` in frame `frame`, then `c0 + r • K` has
dimensions `r*a × r*b × r*c` in a frame obtained by scaling `frame` by `r`
and translating by `c0`.
-/
lemma HasDimensionsInFrame.translateScale
    {K : Body} {frame : Point3 ≃ᵃⁱ[ℝ] Point3}
    {a b c A r : ℝ} (hr : 0 < r) (c0 : Point3)
    (h : K.HasDimensionsInFrame frame a b c A) :
    Body.HasDimensionsInFrame
      (⟨(fun x : Point3 => c0 + r • x) '' K.carrier⟩)
      (AffineIsometryEquiv.mk'
        (fun y : Point3 => c0 + frame.linearIsometryEquiv y + r • frame 0)
        frame.linearIsometryEquiv (0 : Point3)
        (by intro y; simp [vadd_eq_add] <;> abel))
      (r * a) (r * b) (r * c) A := by
  let e : Point3 → Point3 := fun x => r • x
  have h_e : ∀ x, e x = r • x := by intro x; rfl
  let K1 : Body := ⟨e '' K.carrier⟩
  let frame1 := scaledFrame frame r hr
  have h1 : K1.HasDimensionsInFrame frame1 (r * a) (r * b) (r * c) A :=
    h.scale hr e h_e
  let trans : Point3 ≃ᵃⁱ[ℝ] Point3 :=
    AffineIsometryEquiv.mk' (fun x : Point3 => c0 + x)
      (LinearIsometryEquiv.refl ℝ Point3) (0 : Point3)
      (by intro x; simp [vadd_eq_add]; abel)
  let K2 : Body := ⟨trans '' K1.carrier⟩
  let frame2 : Point3 ≃ᵃⁱ[ℝ] Point3 :=
    AffineIsometryEquiv.mk'
      (fun y : Point3 => c0 + frame.linearIsometryEquiv y + r • frame 0)
      frame.linearIsometryEquiv (0 : Point3)
      (by intro y; simp [vadd_eq_add]; abel)
  have h_frame2_apply : ∀ y, frame2 y = c0 + frame1 y := by
    intro y
    have h1 : frame1 y = frame.linearIsometryEquiv y + r • frame 0 := by rfl
    simp [frame2, h1, add_assoc] <;> abel
  have h_image : ∀ (S : Set Point3), frame2 '' S = trans '' (frame1 '' S) := by
    intro S
    ext z
    simp only [Set.mem_image, h_frame2_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨frame1 y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have h_inner : frame2 '' axisBox (r * a) (r * b) (r * c) ⊆ K2.carrier := by
    rw [h_image]
    exact Set.image_mono h1.2.2.2.2.1
  have h_outer : K2.carrier ⊆ frame2 '' axisBox (A * (r * a)) (A * (r * b)) (A * (r * c)) := by
    have h_mono : trans '' K1.carrier ⊆ trans '' (frame1 '' axisBox (A * (r * a)) (A * (r * b)) (A * (r * c))) :=
      Set.image_mono h1.2.2.2.2.2
    have h_eq : trans '' (frame1 '' axisBox (A * (r * a)) (A * (r * b)) (A * (r * c))) =
        frame2 '' axisBox (A * (r * a)) (A * (r * b)) (A * (r * c)) :=
      (h_image _).symm
    rw [h_eq] at h_mono
    exact h_mono
  have hK2_eq : K2.carrier = (fun x : Point3 => c0 + r • x) '' K.carrier := by
    ext y
    simp only [K2, K1, Set.mem_image, trans]
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by simp [add_assoc] <;> abel⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨r • z, ⟨z, hz, rfl⟩, by simp [add_assoc] <;> abel⟩
  have h_main : K2.HasDimensionsInFrame frame2 (r * a) (r * b) (r * c) A :=
    ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h_inner, h_outer⟩
  have h_carrier_eq : ((fun x : Point3 => c0 + r • x) '' K.carrier) = K2.carrier :=
    hK2_eq.symm
  have h_target_eq : (⟨(fun x : Point3 => c0 + r • x) '' K.carrier⟩ : Body) = K2 := by
    exact (Body.mk.injEq _ _).mpr h_carrier_eq
  rw [h_target_eq]
  exact h_main

end Body

/-- A tube viewed as a geometric body. -/
def tubeBody {δ : ℝ} (T : Kakeya.DeltaTube δ) : Body :=
  ⟨T.carrier⟩

/-- The closed unit ball used throughout the paper. -/
def unitBall : Body :=
  ⟨Kakeya.DeltaTube.unitBall⟩

end Kakeya.Streamlined
