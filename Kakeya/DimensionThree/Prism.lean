/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Diam
public import Kakeya.DimensionN.Prism
public import Kakeya.Mathlib.Analysis.EuclideanFrame
public import Kakeya.Mathlib.Analysis.ProjectiveNormal
public import Kakeya.Mathlib.Analysis.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Prism in dimension three

Specialize prism to dimension three.
-/


open Metric

@[expose] public section

noncomputable section

/-- A `Prism3D a b c` is an Prism in `EuclideanSpace ℝ (Fin 3)` (i.e. `ℝ³`).
where the thicknesses are a ≤ b ≤ c.
-/
structure Prism3D (a b c : NNReal) (a_le_b : a ≤ b) (b_le_c : b ≤ c) extends
    PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) where
  thicknesses_eq : thicknesses = ![a, b, c]

namespace Prism3D

variable {a b c : NNReal} {a_le_b : a ≤ b} {b_le_c : b ≤ c}

/--
The 1-dimensional "long axis" direction of the Prism:
-/
abbrev longAxis (P : Prism3D a b c a_le_b b_le_c) :
    Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (Submodule.span ℝ {P.basis 2})

/--
This is the 2-dimensional linear subspace of `ℝ³` spanning the two longest axes.
-/
abbrev longPlane (P : Prism3D a b c a_le_b b_le_c) :
    Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (Submodule.span ℝ {P.basis 1, P.basis 2})

theorem finrank_span_normals (P : Prism3D a b c a_le_b b_le_c) :
    Module.finrank ℝ (Submodule.span ℝ {(P.basis 1), (P.basis 2)}) = 2 := by
  rw [← Matrix.range_cons_cons_empty (P.basis 1) (P.basis 2) ![],
    finrank_span_eq_card (P.toPrismNDim.linearIndependent_pair_basis 1 2 (by decide))]
  simp

theorem finrank_longAxis (P : Prism3D a b c a_le_b b_le_c) :
    Module.finrank ℝ P.longAxis = 1 :=
  finrank_span_singleton (P.basis_ne_zero 2)

theorem finrank_longPlane (P : Prism3D a b c a_le_b b_le_c) :
    Module.finrank ℝ P.longPlane = 2 :=
  P.finrank_span_normals

/-- The spanning plane is the orthogonal complement of `basis 0`. -/
theorem longPlane_eq_orthocomp (P : Prism3D a b c a_le_b b_le_c) :
    P.longPlane = (Submodule.span ℝ ({P.basis 0} : Set _))ᗮ := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro v (rfl | hv)
    · rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact P.basis.inner_eq_zero (show 1 ≠ 0 by decide)
    · rw [Set.mem_singleton_iff] at hv; subst hv
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact P.basis.inner_eq_zero (show 2 ≠ 0 by decide)
  · rw [P.finrank_longPlane]
    refine (Submodule.finrank_add_finrank_orthogonal'
      (K := Submodule.span ℝ ({P.basis 0} : Set _)) ?_).symm
    rw [finrank_span_singleton (P.basis_ne_zero 0), finrank_euclideanSpace_fin]

/-- The tangent plane `TP` of the Prism:
a 2-dimensional affine subspace of `ℝ³` through `center` with direction `longPlane`. -/
abbrev tangentPlane (P : Prism3D a b c a_le_b b_le_c) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' P.center P.longPlane

/-- The Prism3D lies within `c` of its tangent plane. -/
theorem carrier_subset_cthickening_tangentPlane (P : Prism3D a b c a_le_b b_le_c) :
    P.carrier ⊆ Metric.cthickening a P.tangentPlane := by
  intro x hx
  rw [P.mem_carrier_iff] at hx
  have hb := hx 0
  rw [P.basis.repr_apply_apply, real_inner_comm] at hb
  haveI : Nonempty P.tangentPlane := ⟨P.center, AffineSubspace.self_mem_mk' _ _⟩
  set β : ℝ := inner ℝ (x - P.center) (P.basis 0)
  refine Metric.mem_cthickening_of_dist_le x
    (EuclideanGeometry.orthogonalProjection P.tangentPlane x) _ _
    (EuclideanGeometry.orthogonalProjection_mem _) ?_
  rw [EuclideanGeometry.dist_orthogonalProjection_eq_infDist]
  have hz_mem : P.center + ((x - P.center) - β • P.basis 0) ∈ P.tangentPlane := by
    rw [AffineSubspace.mem_mk',
      show P.center + ((x - P.center) - β • P.basis 0) -ᵥ P.center
        = (x - P.center) - β • P.basis 0 from by simp [vsub_eq_sub],
      P.longPlane_eq_orthocomp,
      Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left, inner_smul_left,
      real_inner_self_eq_norm_sq, P.basis.norm_eq_one 0]
    simp [β]
  refine (Metric.infDist_le_dist_of_mem hz_mem).trans ?_
  rw [dist_eq_norm,
    show x - (P.center + ((x - P.center) - β • P.basis 0)) = β • P.basis 0 from by abel,
    norm_smul, Real.norm_eq_abs, P.basis.norm_eq_one 0, mul_one,
    show ((a : NNReal) : ℝ) = P.thicknesses 0 by rw [P.thicknesses_eq]; rfl]
  exact hb

/-- The long axis of the Prism3D contains a unit vector. -/
theorem exists_unit_in_longAxis (P : Prism3D a b c a_le_b b_le_c) :
    ∃ e : EuclideanSpace ℝ (Fin 3), e ∈ P.longAxis ∧ ‖e‖ = 1 := by
  have hdir_ne_bot : P.longAxis ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff, P.finrank_longAxis]
  obtain ⟨w, hw_dir, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdir_ne_bot
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  refine ⟨(‖w‖⁻¹ : ℝ) • w, P.longAxis.smul_mem _ hw_dir, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (ne_of_gt hw_pos)]

lemma inner_mem_longAxisA (P : Prism3D a b c a_le_b b_le_c)
    (e : EuclideanSpace ℝ (Fin 3)) (he : e ∈ P.longAxis) :
    inner ℝ e (P.basis 0) = (0 : ℝ) := by
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp he
  rw [inner_smul_left, P.basis.inner_eq_zero (show 2 ≠ 0 by decide), mul_zero]

lemma inner_mem_longAxisB (P : Prism3D a b c a_le_b b_le_c)
    (e : EuclideanSpace ℝ (Fin 3)) (he : e ∈ P.longAxis) :
    inner ℝ e (P.basis 1) = (0 : ℝ) := by
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp he
  rw [inner_smul_left, P.basis.inner_eq_zero (show 2 ≠ 1 by decide), mul_zero]

lemma mem_add_smul_mem_longAxis (P : Prism3D a b c a_le_b b_le_c)
    (e : EuclideanSpace ℝ (Fin 3))
    (he1 : ‖e‖ = 1) (he2 : e ∈ P.longAxis) (ε : ℝ) (hε : |ε| ≤ (c : ℝ)) :
    P.center + ε • e ∈ P.carrier := by
  rw [P.mem_carrier_iff]
  intro i
  rw [P.basis.repr_apply_apply, real_inner_comm]
  fin_cases i
  · simp [inner_smul_left, inner_mem_longAxisA _ _ he2]
  · simp [inner_smul_left, inner_mem_longAxisB _ _ he2]
  · rw [vsub_eq_sub, add_sub_cancel_left]
    refine (abs_real_inner_le_norm _ _).trans ?_
    simp [norm_smul, Real.norm_eq_abs, he1, P.basis.norm_eq_one, P.thicknesses_eq, hε]

lemma mem_add_mem_longAxis (P : Prism3D a b c a_le_b b_le_c)
    (e : EuclideanSpace ℝ (Fin 3))
    (he1 : ‖e‖ = 1) (he2 : e ∈ P.longAxis) :
    P.center + (c : ℝ) • e ∈ P.carrier :=
  mem_add_smul_mem_longAxis P e he1 he2 c (by rw [abs_of_nonneg c.coe_nonneg])

lemma mem_sub_mem_longAxis (P : Prism3D a b c a_le_b b_le_c)
    (e : EuclideanSpace ℝ (Fin 3))
    (he1 : ‖e‖ = 1) (he2 : e ∈ P.longAxis) :
    P.center - (c : ℝ) • e ∈ P.carrier := by
  simpa [sub_eq_add_neg] using mem_add_smul_mem_longAxis P e he1 he2 (-c)
    (by rw [abs_neg, abs_of_nonneg c.coe_nonneg])

/-- The Prism3D has extent at least `c`. -/
theorem c_le_ethickness_zero (P : Prism3D a b c a_le_b b_le_c) :
    (c : ENNReal) ≤ Metric.ethickness ℝ P.carrier 0 := by
  obtain ⟨e, he_dir, he_norm⟩ := P.exists_unit_in_longAxis
  have h_dist : dist (P.center + (c : ℝ) • e) (P.center - (c : ℝ) • e) = 2 * c := by
    rw [dist_eq_norm,
      show (P.center + (c : ℝ) • e) - (P.center - (c : ℝ) • e) = (2 : ℝ) • ((c : ℝ) • e) from by
        rw [two_smul]; abel,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos two_pos, abs_of_nonneg c.coe_nonneg, he_norm, mul_one]
  have := Metric.half_dist_le_ethickness_zero (𝕜 := ℝ)
    (mem_add_mem_longAxis P e he_norm he_dir)
    (mem_sub_mem_longAxis P e he_norm he_dir)
  rwa [h_dist, show (2 * (c : ℝ)) / 2 = c by ring, ENNReal.ofReal_coe_nnreal] at this

-- TODO: Show any convex body with certain thicknesses
-- is contained in a Prism3D with similar thicknesses.

/-! ### Angles between three-dimensional prisms -/

/-- The unoriented angle between the long planes of two `Prism3D`s.

The long plane is the orthogonal complement of `basis 0`, so we use
`arccos |⟪P₁.basis 0, P₂.basis 0⟫|`. -/
def angle {a₁ b₁ c₁ a₂ b₂ c₂ : NNReal}
    {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P₁ : Prism3D a₁ b₁ c₁ h₁ h₁') (P₂ : Prism3D a₂ b₂ c₂ h₂ h₂') : ℝ :=
  Real.arccos |inner ℝ (P₁.basis 0) (P₂.basis 0)|

/-- The unoriented angle between the long axes of two `Prism3D`s. -/
def axisAngle {a₁ b₁ c₁ a₂ b₂ c₂ : NNReal}
    {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P₁ : Prism3D a₁ b₁ c₁ h₁ h₁') (P₂ : Prism3D a₂ b₂ c₂ h₂ h₂') : ℝ :=
  Real.arccos |inner ℝ (P₁.basis 2) (P₂.basis 2)|

section AngleAPI

variable {a₁ b₁ c₁ a₂ b₂ c₂ : NNReal}
  {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
  (P₁ : Prism3D a₁ b₁ c₁ h₁ h₁') (P₂ : Prism3D a₂ b₂ c₂ h₂ h₂')

lemma angle_def :
    P₁.angle P₂ = Real.arccos |inner ℝ (P₁.basis 0) (P₂.basis 0)| := rfl

lemma axisAngle_def :
    P₁.axisAngle P₂ = Real.arccos |inner ℝ (P₁.basis 2) (P₂.basis 2)| := rfl

/-- `|⟨basis i, basis j⟩| ≤ 1` for orthonormal bases of unit vectors. -/
lemma abs_inner_basis_le_one (i j : Fin 3) :
    |inner ℝ (P₁.basis i) (P₂.basis j)| ≤ 1 :=
  _root_.abs_inner_basis_le_one P₁.basis P₂.basis i j

/-- `cos (angle P₁ P₂) = |⟨basis 0, basis 0⟩|`. -/
lemma cos_angle :
    Real.cos (P₁.angle P₂) = |inner ℝ (P₁.basis 0) (P₂.basis 0)| := by
  rw [angle_def]
  refine Real.cos_arccos ?_ (abs_inner_basis_le_one P₁ P₂ 0 0)
  linarith [abs_nonneg (inner ℝ (P₁.basis 0) (P₂.basis 0))]

/-- `cos (axisAngle P₁ P₂) = |⟨basis 2, basis 2⟩|`. -/
lemma cos_axisAngle :
    Real.cos (P₁.axisAngle P₂) = |inner ℝ (P₁.basis 2) (P₂.basis 2)| := by
  rw [axisAngle_def]
  refine Real.cos_arccos ?_ (abs_inner_basis_le_one P₁ P₂ 2 2)
  linarith [abs_nonneg (inner ℝ (P₁.basis 2) (P₂.basis 2))]

@[simp] lemma angle_nonneg : 0 ≤ P₁.angle P₂ := Real.arccos_nonneg _

@[simp] lemma axisAngle_nonneg : 0 ≤ P₁.axisAngle P₂ := Real.arccos_nonneg _

lemma angle_le_pi_div_two : P₁.angle P₂ ≤ Real.pi / 2 := by
  rw [angle_def]
  exact Real.arccos_le_pi_div_two.mpr (abs_nonneg _)

lemma axisAngle_le_pi_div_two : P₁.axisAngle P₂ ≤ Real.pi / 2 := by
  rw [axisAngle_def]
  exact Real.arccos_le_pi_div_two.mpr (abs_nonneg _)

lemma angle_le_pi : P₁.angle P₂ ≤ Real.pi :=
  (angle_le_pi_div_two P₁ P₂).trans (by linarith [Real.pi_pos])

lemma axisAngle_le_pi : P₁.axisAngle P₂ ≤ Real.pi :=
  (axisAngle_le_pi_div_two P₁ P₂).trans (by linarith [Real.pi_pos])

/-- The angle between two long planes is symmetric. -/
lemma angle_comm : P₁.angle P₂ = P₂.angle P₁ := by
  rw [angle_def, angle_def, real_inner_comm]

/-- The axis angle is symmetric. -/
lemma axisAngle_comm : P₁.axisAngle P₂ = P₂.axisAngle P₁ := by
  rw [axisAngle_def, axisAngle_def, real_inner_comm]

end AngleAPI

/-- The angle of a prism's long plane with itself is `0`. -/
@[simp] lemma angle_self {a b c : NNReal} {h : a ≤ b} {h' : b ≤ c}
    (P : Prism3D a b c h h') : P.angle P = 0 := by
  rw [angle_def, real_inner_self_eq_norm_sq, P.basis.norm_eq_one,
    one_pow, abs_one, Real.arccos_one]

/-- The axis angle of a prism with itself is `0`. -/
@[simp] lemma axisAngle_self {a b c : NNReal} {h : a ≤ b} {h' : b ≤ c}
    (P : Prism3D a b c h h') : P.axisAngle P = 0 := by
  rw [axisAngle_def, real_inner_self_eq_norm_sq, P.basis.norm_eq_one,
    one_pow, abs_one, Real.arccos_one]

/-! ### The plane angle against the projective distance of the short normals -/

/-- **Projective chord bounded by the plane angle.**  For two prisms the projective distance of
their short normals is at most the (projective) plane angle `Prism3D.angle`, via
`‖nᵢ - nⱼ‖² = 2 - 2⟪nᵢ,nⱼ⟫` and `2 - 2 cos φ ≤ φ²`. -/
theorem projNormalDist_basis0_le_angle
    {a₁ b₁ c₁ a₂ b₂ c₂ : NNReal} {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P : Prism3D a₁ b₁ c₁ h₁ h₁') (Q : Prism3D a₂ b₂ c₂ h₂ h₂') :
    projNormalDist (P.basis 0) (Q.basis 0) ≤ Prism3D.angle P Q := by
  have hn₁ : ‖P.basis 0‖ = 1 := P.basis.norm_eq_one 0
  have hn₂ : ‖Q.basis 0‖ = 1 := Q.basis.norm_eq_one 0
  have habs1 : |(inner ℝ (P.basis 0) (Q.basis 0) : ℝ)| ≤ 1 := by
    have := abs_real_inner_le_norm (P.basis 0) (Q.basis 0); rwa [hn₁, hn₂, mul_one] at this
  rw [Prism3D.angle_def]
  exact chord_le_arccos (abs_nonneg _) habs1 (projNormalDist_sq _ _ hn₁ hn₂)

/-- **Plane angle bounded by the projective chord**, the converse of
`projNormalDist_basis0_le_angle` up to the absolute factor `2`. Writing `φ = angle P Q ∈ [0, π/2]`,
the projective chord equals `2 sin (φ/2)`, and Jordan's inequality `(2/π) x ≤ sin x` on `[0, π/2]`
gives `2 sin (φ/2) ≥ 2φ/π ≥ φ/2`. -/
theorem angle_le_two_mul_projNormalDist
    {a₁ b₁ c₁ a₂ b₂ c₂ : NNReal} {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P : Prism3D a₁ b₁ c₁ h₁ h₁') (Q : Prism3D a₂ b₂ c₂ h₂ h₂') :
    Prism3D.angle P Q ≤ 2 * projNormalDist (P.basis 0) (Q.basis 0) := by
  have hn₁ : ‖P.basis 0‖ = 1 := P.basis.norm_eq_one 0
  have hn₂ : ‖Q.basis 0‖ = 1 := Q.basis.norm_eq_one 0
  have habs1 : |(inner ℝ (P.basis 0) (Q.basis 0) : ℝ)| ≤ 1 := by
    have := abs_real_inner_le_norm (P.basis 0) (Q.basis 0); rwa [hn₁, hn₂, mul_one] at this
  rw [Prism3D.angle_def]
  exact arccos_le_two_mul_chord (projNormalDist_nonneg _ _) (abs_nonneg _) habs1
    (projNormalDist_sq _ _ hn₁ hn₂)

/-- **Quasi-triangle inequality for the prism plane angle.** `Prism3D.angle` is the projective
angle between short normals, hence a genuine metric on projective space; but the repository only
has the two one-sided comparisons with `projNormalDist`, so chaining them costs an absolute
factor `2`. This is exactly what is needed to transfer an `inSlabFamilyC` angle bound from a
candidate slab to a comparable selected slab. -/
theorem angle_le_two_mul_add_angle
    {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : NNReal}
    {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂} {h₃ : a₃ ≤ b₃} {h₃' : b₃ ≤ c₃}
    (P : Prism3D a₁ b₁ c₁ h₁ h₁') (Q : Prism3D a₂ b₂ c₂ h₂ h₂') (R : Prism3D a₃ b₃ c₃ h₃ h₃') :
    Prism3D.angle P R ≤ 2 * (Prism3D.angle P Q + Prism3D.angle Q R) := by
  calc Prism3D.angle P R ≤ 2 * projNormalDist (P.basis 0) (R.basis 0) :=
        angle_le_two_mul_projNormalDist P R
    _ ≤ 2 * (projNormalDist (P.basis 0) (Q.basis 0) + projNormalDist (Q.basis 0) (R.basis 0)) := by
        have := projNormalDist_triangle (P.basis 0) (Q.basis 0) (R.basis 0)
        linarith
    _ ≤ 2 * (Prism3D.angle P Q + Prism3D.angle Q R) := by
        have h1 := projNormalDist_basis0_le_angle P Q
        have h2 := projNormalDist_basis0_le_angle Q R
        linarith

end Prism3D

end
