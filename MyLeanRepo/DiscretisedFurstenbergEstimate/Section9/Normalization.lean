module

/-
  Normalization wrapper for Section 9 Step 5.

  Maps P ⊆ closedBall 0 1 to P_norm ⊆ [0,1)² via
    φ(p) = p/4 + (1/2, 1/2)

  This maps coordinates in [-1,1] into [1/4, 3/4] ⊂ [0,1).

  Key properties:
  - P_norm ⊆ [0,1)²
  - S-set transfers: scale δ→δ/4, constant C→C·4^t
  - AffineLine map is bi-Lipschitz: U = 1+√2/2, K = 4
  - Ncover upper: Ncover(U·δ, φ_line '' S) ≤ Ncover(δ, S)

  Whiteprint node: section9 / normalization_wrapper
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.RescaleSsetEuclidean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9.Normalization

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

abbrev Plane := EuclideanPlane

/-- Scaling factor for normalization. -/
def c : ℝ := 1 / 4

/-- The constant vector (1/2, 1/2). -/
def halfVec : Plane :=
  WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun _ => 1 / 2

lemma halfVec_apply (i : Fin 2) : halfVec i = 1 / 2 := by
  simp [halfVec]

lemma halfVec_norm : ‖halfVec‖ = Real.sqrt 2 / 2 := by
  have h5 : ‖halfVec‖ ^ 2 = 1 / 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [halfVec_apply] <;> norm_num
  have h6 : 0 ≤ ‖halfVec‖ := by positivity
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

lemma halfVec_norm_le_one : ‖halfVec‖ ≤ 1 := by
  rw [halfVec_norm]
  have h : Real.sqrt 2 / 2 ≤ 1 := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  exact h

/-- Normalization function: φ(p) = c • p + halfVec where c = 1/4. -/
def φ (p : Plane) : Plane := c • p + halfVec

/-- φ as an AffineMap. -/
def φAffine : Plane →ᵃ[ℝ] Plane :=
  AffineMap.mk' φ (c • LinearMap.id) (0 : Plane)
    (by intro p; ext i; simp [φ, c, halfVec_apply] <;> ring)

lemma φAffine_linear : φAffine.linear = c • LinearMap.id := by
  rw [φAffine, AffineMap.mk'_linear]

lemma c_pos : 0 < c := by norm_num [c]
lemma c_ne_zero : c ≠ 0 := by norm_num [c]

/-- Coordinate bound from norm: |p i| ≤ ‖p‖. -/
lemma coord_bound_norm (p : Plane) (i : Fin 2) : |p i| ≤ ‖p‖ := by
  have h2 : (p i)^2 ≤ ‖p‖^2 := by
    have h3 : ‖p‖^2 = ∑ j : Fin 2, (p j)^2 := EuclideanSpace.real_norm_sq_eq p
    rw [h3]
    have h4 : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (p j)^2 := by
      intro j _; positivity
    exact Finset.single_le_sum h4 (Finset.mem_univ i)
  have h5 : |p i| ^ 2 = (p i)^2 := by rw [sq_abs]
  have h6 : |p i| ^ 2 ≤ ‖p‖ ^ 2 := by rw [h5]; exact h2
  have h7 : 0 ≤ |p i| := by positivity
  have h8 : 0 ≤ ‖p‖ := by positivity
  nlinarith

/-! ### 1. Image in unit square -/

/-- φ maps closedBall 0 1 into [0,1)². In fact into [1/4, 3/4]². -/
lemma φ_image_unit {P : Set Plane} (hP : P ⊆ Metric.closedBall 0 1) :
    φ '' P ⊆ {p : Plane | p 0 ∈ Set.Ico (0 : ℝ) 1 ∧ p 1 ∈ Set.Ico (0 : ℝ) 1} := by
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  have h1 : ‖p‖ ≤ 1 := by
    have h11 : p ∈ Metric.closedBall (0 : Plane) 1 := hP hp
    simpa [Metric.mem_closedBall] using h11
  have h2 : |p 0| ≤ 1 := by
    have h3 : |p 0| ≤ ‖p‖ := coord_bound_norm p 0
    linarith
  have h3 : |p 1| ≤ 1 := by
    have h4 : |p 1| ≤ ‖p‖ := coord_bound_norm p 1
    linarith
  have h41 : -1 ≤ p 0 := (abs_le.mp h2).1
  have h42 : p 0 ≤ 1 := (abs_le.mp h2).2
  have h51 : -1 ≤ p 1 := (abs_le.mp h3).1
  have h52 : p 1 ≤ 1 := (abs_le.mp h3).2
  have h6 : 0 ≤ φ p 0 := by
    simp [φ, c, halfVec_apply] <;> linarith
  have h7 : φ p 0 < 1 := by
    simp [φ, c, halfVec_apply] <;> linarith
  have h8 : 0 ≤ φ p 1 := by
    simp [φ, c, halfVec_apply] <;> linarith
  have h9 : φ p 1 < 1 := by
    simp [φ, c, halfVec_apply] <;> linarith
  exact ⟨⟨h6, h7⟩, ⟨h8, h9⟩⟩

/-- φ maps closedBall 0 1 into closedBall 0 1.
    By triangle inequality: ‖φ(p)‖ ≤ ‖p‖/4 + ‖halfVec‖ ≤ 1/4 + √2/2 < 1. -/
lemma φ_image_unit_ball {P : Set Plane} (hP : P ⊆ Metric.closedBall 0 1) :
    φ '' P ⊆ Metric.closedBall 0 1 := by
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  have h1 : ‖p‖ ≤ 1 := by
    have h11 : p ∈ Metric.closedBall (0 : Plane) 1 := hP hp
    simpa [Metric.mem_closedBall] using h11
  have h2 : ‖φ p‖ ≤ ‖p‖ / 4 + ‖halfVec‖ := by
    have h_eq : φ p = (c : ℝ) • p + halfVec := by rfl
    rw [h_eq]
    calc ‖(c : ℝ) • p + halfVec‖
      ≤ ‖(c : ℝ) • p‖ + ‖halfVec‖ := norm_add_le _ _
    _ = c * ‖p‖ + ‖halfVec‖ := by simp [norm_smul, c] <;> ring
    _ = ‖p‖ / 4 + ‖halfVec‖ := by simp [c] <;> ring
  have h3 : ‖halfVec‖ = Real.sqrt 2 / 2 := halfVec_norm
  rw [h3] at h2
  have h4 : ‖p‖ / 4 + Real.sqrt 2 / 2 ≤ 1 := by
    have h5 : ‖p‖ ≤ 1 := h1
    have h6 : Real.sqrt 2 / 2 < 3 / 4 := by
      have h7 : Real.sqrt 2 < 3 / 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    linarith
  have h5 : ‖φ p‖ ≤ 1 := by linarith
  simpa [Metric.mem_closedBall] using h5

/-! ### 2. S-set transfer -/

/-- S-set transfers under φ: scale δ → δ/4, constant C → C · 4^t. -/
lemma normalize_sset {δ t C : ℝ} {P : Set Plane}
    (h : IsDeltaSSet δ t C P) :
    IsDeltaSSet (δ / 4) t (C * 4 ^ t) (φ '' P) := by
  let scale : Plane → Plane := fun x => c • x
  let transl : Plane → Plane := fun x => x + halfVec
  have h1 : IsDeltaSSet (c * δ) t (C * c ^ (-t)) (scale '' P) :=
    rescale_sset_euclidean (hc_pos := c_pos) h
  have h_cδ : c * δ = δ / 4 := by
    simp [c] <;> ring
  have h_const : C * c ^ (-t) = C * (4 : ℝ) ^ t := by
    have h11 : c = (4 : ℝ) ^ (-1 : ℝ) := by
      simp [c] <;> norm_num
    have h12 : c ^ (-t) = (4 : ℝ) ^ t := by
      rw [h11]
      have h13 : ((4 : ℝ) ^ (-1 : ℝ)) ^ (-t) = (4 : ℝ) ^ ((-1 : ℝ) * (-t)) := by
        exact (Real.rpow_mul (by norm_num) (-1 : ℝ) (-t)).symm
      rw [h13]
      have h14 : (-1 : ℝ) * (-t) = t := by ring
      rw [h14]
    rw [h12]
  rw [h_cδ, h_const] at h1
  have h2 : IsDeltaSSet (δ / 4) t (C * (4 : ℝ) ^ t) (transl '' (scale '' P)) :=
    translate_sset_euclidean (v := halfVec) h1
  have h3 : transl '' (scale '' P) = φ '' P := by
    ext z
    simp only [φ, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [transl, scale] <;> abel⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨scale x, ⟨x, hx, rfl⟩, by simp [transl, scale] <;> abel⟩
  rw [h3] at h2
  exact h2

/-! ### 3. AffineLine normalization -/

/-- Scaling a submodule by c ≠ 0 gives the same submodule. -/
lemma submodule_scale_eq {p : Submodule ℝ Plane} :
    Submodule.map (c • LinearMap.id) p = p := by
  ext x
  simp only [Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact p.smul_mem c hy
  · intro hx
    refine ⟨(c⁻¹ : ℝ) • x, p.smul_mem (c⁻¹) hx, ?_⟩
    have h : c • ((c⁻¹ : ℝ) • x) = x := by
      rw [smul_smul]
      have h2 : c * c⁻¹ = 1 := by field_simp [c_ne_zero] <;> ring
      rw [h2, one_smul]
    exact h

/-- Normalize an AffineLine by mapping its affine subspace through φ. -/
def φ_line (ℓ : AffineLine) : AffineLine :=
  let img := AffineSubspace.map φAffine ℓ.1
  have h_finrank : Module.finrank ℝ img.direction = 1 := by
    have h_dir : img.direction = Submodule.map φAffine.linear ℓ.1.direction := by
      rw [AffineSubspace.map_direction]
    rw [h_dir, φAffine_linear, submodule_scale_eq]
    exact ℓ.2
  ⟨img, h_finrank⟩

/-- Direction is preserved under φ_line. -/
lemma φ_line_direction_eq (ℓ : AffineLine) :
    (φ_line ℓ).1.direction = ℓ.1.direction := by
  have h1 : (φ_line ℓ).1.direction =
      Submodule.map φAffine.linear ℓ.1.direction := by
    have h2 : (φ_line ℓ).1 = AffineSubspace.map φAffine ℓ.1 := by
      simp [φ_line]
    rw [h2, AffineSubspace.map_direction]
  rw [h1, φAffine_linear, submodule_scale_eq]

/-- For any p in affine subspace S with direction D, offset(S) = p - D.starProjection p. -/
lemma offset_via_starProjection {S : AffineSubspace ℝ Plane} [Nonempty S]
    [S.direction.HasOrthogonalProjection] {p : Plane} (hp : p ∈ S) :
    EuclideanGeometry.orthogonalProjection S 0 = p - S.direction.starProjection p := by
  let D := S.direction
  let q := p - D.starProjection p
  have h1 : D.starProjection p ∈ D := Submodule.starProjection_apply_mem D p
  have h2 : -D.starProjection p ∈ D := D.neg_mem h1
  have hq1 : q ∈ S := by
    have h3 : (-D.starProjection p) +ᵥ p ∈ S :=
      (S.vadd_mem_iff_mem_direction (-D.starProjection p) hp).mpr h2
    have h4 : (-D.starProjection p) +ᵥ p = p - D.starProjection p := by
      simp [vadd_eq_add] <;> abel
    rw [h4] at h3; exact h3
  have hq2 : q ∈ Dᗮ := D.sub_starProjection_mem_orthogonal p
  have h_bot : D ⊓ Dᗮ = ⊥ := Submodule.inf_orthogonal_eq_bot D
  have h_unique : ∀ (x : Plane), x ∈ S → x ∈ Dᗮ → x = q := by
    intro x hx1 hx2
    have h : x - q ∈ D := S.vsub_mem_direction hx1 hq1
    have h' : x - q ∈ Dᗮ := Dᗮ.sub_mem hx2 hq2
    have h'' : x - q ∈ (D ⊓ Dᗮ) := ⟨h, h'⟩
    have h_zero : x - q = 0 := by
      have h_in_bot : x - q ∈ (⊥ : Submodule ℝ Plane) := by
        rw [h_bot] at h''; exact h''
      simpa using h_in_bot
    exact sub_eq_zero.mp h_zero
  have hq2' : (0 : Plane) -ᵥ q ∈ Dᗮ := by
    have h : (0 : Plane) -ᵥ q = -q := by simp
    rw [h]
    exact Dᗮ.neg_mem hq2
  have h_main : EuclideanGeometry.orthogonalProjection S 0 = q := by
    rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
    exact ⟨hq1, hq2'⟩
  exact h_main

/-- Offset formula: offset(φ_line ℓ) = c • offset(ℓ) + halfVec - D.starProjection halfVec. -/
lemma φ_line_offset_formula (ℓ : AffineLine) :
    (φ_line ℓ).offset =
      c • ℓ.offset + halfVec - ℓ.1.direction.starProjection halfVec := by
  let D := ℓ.1.direction
  let q := ℓ.offset
  have hq_mem : q ∈ ℓ.1 := ℓ.offset_mem
  have hq_orth : q ∈ Dᗮ := by
    have h : (0 : Plane) -ᵥ q ∈ Dᗮ := by
      exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal ℓ.1 (0 : Plane)
    simpa using h
  have h_proj_q : D.starProjection q = 0 := by
    have h_eq : D.starProjection q = (D.orthogonalProjectionOnto q : Plane) := by
      rw [Submodule.starProjection_apply]
    rw [h_eq]
    have h : D.orthogonalProjectionOnto q = 0 := by
      rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
      exact hq_orth
    exact_mod_cast h
  have h_fq_mem : φ q ∈ (φ_line ℓ).1 := by
    have h_img2 : ((φ_line ℓ).1 : Set Plane) = φAffine '' (ℓ.1 : Set Plane) := by rfl
    have h : φ q ∈ ((φ_line ℓ).1 : Set Plane) := by
      rw [h_img2]; exact ⟨q, hq_mem, rfl⟩
    exact h
  have h_dir_eq : (φ_line ℓ).1.direction = D := φ_line_direction_eq ℓ
  have h_goal : (φ_line ℓ).offset =
      φ q - (φ_line ℓ).1.direction.starProjection (φ q) := by
    simp [AffineLine.offset]
    exact offset_via_starProjection h_fq_mem
  have h12 : D.starProjection (φ q) = D.starProjection halfVec := by
    have h11 : φ q = c • q + halfVec := by rfl
    rw [h11]
    have h_add : D.starProjection (c • q + halfVec) =
        D.starProjection (c • q) + D.starProjection halfVec :=
      D.starProjection.map_add (c • q) halfVec
    rw [h_add]
    have h_smul : D.starProjection (c • q) = c • D.starProjection q :=
      D.starProjection.map_smul c q
    rw [h_smul, h_proj_q] <;> simp
  calc (φ_line ℓ).offset
    = φ q - (φ_line ℓ).1.direction.starProjection (φ q) := h_goal
  _ = φ q - D.starProjection (φ q) := by rw [h_dir_eq]
  _ = φ q - D.starProjection halfVec := by rw [h12]
  _ = c • q + halfVec - D.starProjection halfVec := by
    have h13 : φ q = c • q + halfVec := by rfl
    rw [h13]
  _ = c • ℓ.offset + halfVec - D.starProjection halfVec := by rfl

/-! ### 4. Bi-Lipschitz constants -/

/-- φ_line is bi-Lipschitz on AffineLine.dist.
    Upper constant U = 1 + √2/2
    Lower constant K = 4 -/
lemma φ_line_bilipschitz :
    ∃ (U K : ℝ), 0 < U ∧ 0 < K ∧
      (∀ ℓ₁ ℓ₂ : AffineLine,
        dist (φ_line ℓ₁) (φ_line ℓ₂) ≤ U * dist ℓ₁ ℓ₂) ∧
      (∀ ℓ₁ ℓ₂ : AffineLine,
        dist ℓ₁ ℓ₂ ≤ K * dist (φ_line ℓ₁) (φ_line ℓ₂)) := by
  let U : ℝ := 1 + Real.sqrt 2 / 2
  let K : ℝ := 4
  have hU_pos : 0 < U := by positivity
  have hK_pos : 0 < K := by norm_num
  have h_main_upper : ∀ (ℓ₁ ℓ₂ : AffineLine),
      dist (φ_line ℓ₁) (φ_line ℓ₂) ≤ U * dist ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂
    let D₁ := ℓ₁.1.direction
    let D₂ := ℓ₂.1.direction
    let dir_diff := ‖D₁.starProjection - D₂.starProjection‖
    let off_diff := ‖ℓ₁.offset - ℓ₂.offset‖
    let off_diff' := ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖
    have h_dir : ‖(φ_line ℓ₁).1.direction.starProjection - (φ_line ℓ₂).1.direction.starProjection‖ = dir_diff := by
      rw [φ_line_direction_eq ℓ₁, φ_line_direction_eq ℓ₂]
    set E := (D₂.starProjection - D₁.starProjection) halfVec with hE_def
    have h_off_bound : off_diff' ≤ c * off_diff + ‖halfVec‖ * dir_diff := by
      have h_eq : (φ_line ℓ₁).offset - (φ_line ℓ₂).offset =
          c • (ℓ₁.offset - ℓ₂.offset) + E := by
        rw [φ_line_offset_formula ℓ₁, φ_line_offset_formula ℓ₂]
        ext i
        simp [hE_def, sub_smul] <;> ring
      have h3 : ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖ ≤
          ‖c • (ℓ₁.offset - ℓ₂.offset)‖ + ‖E‖ := by
        rw [h_eq]
        exact norm_add_le _ _
      have h4 : ‖c • (ℓ₁.offset - ℓ₂.offset)‖ = c * off_diff := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos c_pos] <;> rfl
      have h5 : ‖E‖ ≤ ‖(D₂.starProjection - D₁.starProjection)‖ * ‖halfVec‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have h6 : ‖(D₂.starProjection - D₁.starProjection)‖ = dir_diff := by
        have h : D₂.starProjection - D₁.starProjection = -(D₁.starProjection - D₂.starProjection) := by
          ext v; simp
        rw [h, norm_neg]
      simpa [off_diff'] using calc
        off_diff'
          = ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖ := by rfl
        _ ≤ ‖c • (ℓ₁.offset - ℓ₂.offset)‖ + ‖E‖ := h3
        _ = c * off_diff + ‖E‖ := by rw [h4]
        _ ≤ c * off_diff + ‖(D₂.starProjection - D₁.starProjection)‖ * ‖halfVec‖ := by gcongr
        _ = c * off_diff + ‖halfVec‖ * dir_diff := by rw [h6, mul_comm dir_diff ‖halfVec‖] <;> ring
    have h_dist : dist (φ_line ℓ₁) (φ_line ℓ₂) =
        ‖(φ_line ℓ₁).1.direction.starProjection - (φ_line ℓ₂).1.direction.starProjection‖ +
        off_diff' := by
      change ‖(φ_line ℓ₁).1.direction.starProjection - (φ_line ℓ₂).1.direction.starProjection‖ +
        ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖ = _
      rw [h_dir] <;> rfl
    have h_orig : dist ℓ₁ ℓ₂ = dir_diff + off_diff := by
      change ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
        ‖ℓ₁.offset - ℓ₂.offset‖ = _
      <;> rfl
    have h9 : ‖halfVec‖ = Real.sqrt 2 / 2 := halfVec_norm
    have hU_eq : U = 1 + ‖halfVec‖ := by
      dsimp only [U]
      rw [h9] <;> ring
    have h_c_le_U : c ≤ U := by
      rw [hU_eq]
      have h10 : 0 ≤ ‖halfVec‖ := by positivity
      simp [c] <;> linarith
    have hdir_nonneg : 0 ≤ dir_diff := norm_nonneg _
    have hoff_nonneg : 0 ≤ off_diff := norm_nonneg _
    rw [h_dist, h_orig, h_dir]
    calc
      dir_diff + off_diff'
        ≤ dir_diff + (c * off_diff + ‖halfVec‖ * dir_diff) := by gcongr
      _ = (1 + ‖halfVec‖) * dir_diff + c * off_diff := by ring
      _ ≤ U * dir_diff + U * off_diff := by
        have h11 : (1 + ‖halfVec‖) * dir_diff ≤ U * dir_diff := by
          have h12 : U = 1 + ‖halfVec‖ := hU_eq
          rw [h12] <;> rfl
        have h13 : c * off_diff ≤ U * off_diff := by
          gcongr <;> linarith [h_c_le_U]
        linarith
      _ = U * (dir_diff + off_diff) := by ring
  have h_main_lower : ∀ (ℓ₁ ℓ₂ : AffineLine),
      dist ℓ₁ ℓ₂ ≤ K * dist (φ_line ℓ₁) (φ_line ℓ₂) := by
    intro ℓ₁ ℓ₂
    let D₁ := ℓ₁.1.direction
    let D₂ := ℓ₂.1.direction
    let dir_diff := ‖D₁.starProjection - D₂.starProjection‖
    let off_diff := ‖ℓ₁.offset - ℓ₂.offset‖
    let off_diff' := ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖
    have h_dir : ‖(φ_line ℓ₁).1.direction.starProjection - (φ_line ℓ₂).1.direction.starProjection‖ = dir_diff := by
      rw [φ_line_direction_eq ℓ₁, φ_line_direction_eq ℓ₂]
    set E := (D₂.starProjection - D₁.starProjection) halfVec with hE_def
    have h_E_bound : ‖E‖ ≤ ‖halfVec‖ * dir_diff := by
      have h7 : ‖E‖ ≤ ‖(D₂.starProjection - D₁.starProjection)‖ * ‖halfVec‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have h8 : ‖(D₂.starProjection - D₁.starProjection)‖ = dir_diff := by
        have h : D₂.starProjection - D₁.starProjection = -(D₁.starProjection - D₂.starProjection) := by
          ext v; simp
        rw [h, norm_neg]
      rw [h8] at h7
      rw [mul_comm] at h7
      exact h7
    have h1 : off_diff ≤ c⁻¹ * off_diff' + c⁻¹ * ‖halfVec‖ * dir_diff := by
      have h2 : ℓ₁.offset - ℓ₂.offset =
          c⁻¹ • ((φ_line ℓ₁).offset - (φ_line ℓ₂).offset) - c⁻¹ • E := by
        rw [φ_line_offset_formula ℓ₁, φ_line_offset_formula ℓ₂]
        ext i
        simp [hE_def, sub_smul] <;> field_simp [c_ne_zero] <;> ring
      have h3 : ‖ℓ₁.offset - ℓ₂.offset‖ ≤
          ‖c⁻¹ • ((φ_line ℓ₁).offset - (φ_line ℓ₂).offset)‖ + ‖c⁻¹ • E‖ := by
        rw [h2]
        exact norm_sub_le _ _
      have h_cinv_pos : 0 < c⁻¹ := inv_pos.mpr c_pos
      have h4 : ‖c⁻¹ • ((φ_line ℓ₁).offset - (φ_line ℓ₂).offset)‖ = c⁻¹ * off_diff' := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos h_cinv_pos] <;> ring
      have h5 : ‖c⁻¹ • E‖ = c⁻¹ * ‖E‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos h_cinv_pos] <;> ring
      simpa [off_diff'] using calc
        off_diff
          = ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
        _ ≤ ‖c⁻¹ • ((φ_line ℓ₁).offset - (φ_line ℓ₂).offset)‖ + ‖c⁻¹ • E‖ := h3
        _ = c⁻¹ * off_diff' + c⁻¹ * ‖E‖ := by rw [h4, h5] <;> ring
        _ ≤ c⁻¹ * off_diff' + c⁻¹ * (‖halfVec‖ * dir_diff) := by
          gcongr <;> exact inv_pos.mpr c_pos
        _ = c⁻¹ * off_diff' + c⁻¹ * ‖halfVec‖ * dir_diff := by ring
    have h_dist : dist (φ_line ℓ₁) (φ_line ℓ₂) = dir_diff + off_diff' := by
      change ‖(φ_line ℓ₁).1.direction.starProjection - (φ_line ℓ₂).1.direction.starProjection‖ +
        ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖ = _
      rw [h_dir] <;> rfl
    have h_orig : dist ℓ₁ ℓ₂ = dir_diff + off_diff := by
      change ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
        ‖ℓ₁.offset - ℓ₂.offset‖ = _
      <;> rfl
    have hdir_nonneg : 0 ≤ dir_diff := norm_nonneg _
    have hoff'_nonneg : 0 ≤ off_diff' := norm_nonneg _
    have h_c_inv : c⁻¹ = 4 := by
      simp [c] <;> norm_num
    have h_halfVec_sqrt2 : ‖halfVec‖ = Real.sqrt 2 / 2 := halfVec_norm
    rw [h_orig, h_dist]
    have h_bound1 : 1 + c⁻¹ * ‖halfVec‖ ≤ (K : ℝ) := by
      rw [h_c_inv, h_halfVec_sqrt2]
      have h : 1 + (4 : ℝ) * (Real.sqrt 2 / 2) ≤ 4 := by
        have h2 : Real.sqrt 2 ≤ 3 / 2 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        linarith
      exact h
    have h_bound2 : c⁻¹ ≤ (K : ℝ) := by
      rw [h_c_inv] <;> norm_num
    calc
      dir_diff + off_diff
        ≤ dir_diff + (c⁻¹ * off_diff' + c⁻¹ * ‖halfVec‖ * dir_diff) := by gcongr
      _ = (1 + c⁻¹ * ‖halfVec‖) * dir_diff + c⁻¹ * off_diff' := by ring
      _ ≤ (K : ℝ) * dir_diff + (K : ℝ) * off_diff' := by
        have h13 : (1 + c⁻¹ * ‖halfVec‖) * dir_diff ≤ (K : ℝ) * dir_diff := by
          gcongr <;> linarith
        have h14 : c⁻¹ * off_diff' ≤ (K : ℝ) * off_diff' := by
          gcongr <;> linarith
        linarith
      _ = (K : ℝ) * (dir_diff + off_diff') := by ring
  exact ⟨U, K, hU_pos, hK_pos, h_main_upper, h_main_lower⟩

/-! ### 5. Ncover upper transfer for line families -/

/-- Ncover upper bound: Ncover(U*δ, φ_line '' S) ≤ Ncover(δ, S). -/
lemma ncover_line_upper :
    ∃ (U : ℝ), 0 < U ∧
      ∀ (δ : ℝ) (S : Set AffineLine), 0 < δ →
        Metric.externalCoveringNumber (U * δ).toNNReal (φ_line '' S) ≤
          Metric.externalCoveringNumber δ.toNNReal S := by
  rcases φ_line_bilipschitz with ⟨U, K, hU_pos, hK_pos, h_lip, h_antilip⟩
  let U' : NNReal := ⟨U, by linarith⟩
  have hU'_coe : (U' : ℝ) = U := by exact_mod_cast rfl
  have h_lip' : LipschitzWith U' φ_line :=
    LipschitzWith.of_dist_le_mul h_lip
  have h1 : ∀ (δ : ℝ) (S : Set AffineLine), 0 < δ →
      Metric.externalCoveringNumber (U * δ).toNNReal (φ_line '' S) ≤
        Metric.externalCoveringNumber δ.toNNReal S := by
    intro δ S hδ
    have h_eq : U' * δ.toNNReal = (U * δ).toNNReal := by
      apply NNReal.coe_injective
      simp [hU'_coe, Real.toNNReal_of_nonneg hδ.le,
            Real.toNNReal_of_nonneg (mul_pos hU_pos hδ).le] <;> ring
    rw [← h_eq]
    exact DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_lipschitz (hf := h_lip')
  exact ⟨U, hU_pos, h1⟩

/-- Explicit Lipschitz constant for φ_line: U = 1 + √2/2 < 2. -/
lemma φ_line_lipschitz_explicit :
  ∀ (ℓ₁ ℓ₂ : AffineLine),
    dist (φ_line ℓ₁) (φ_line ℓ₂) ≤ (1 + Real.sqrt 2 / 2) * dist ℓ₁ ℓ₂ := by
  intro ℓ₁ ℓ₂
  let U : ℝ := 1 + Real.sqrt 2 / 2
  let D₁ := ℓ₁.1.direction
  let D₂ := ℓ₂.1.direction
  let dir_diff := ‖D₁.starProjection - D₂.starProjection‖
  let off_diff := ‖ℓ₁.offset - ℓ₂.offset‖
  let off_diff' := ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖
  have h_dir : ‖(φ_line ℓ₁).1.direction.starProjection - (φ_line ℓ₂).1.direction.starProjection‖ = dir_diff := by
    rw [φ_line_direction_eq ℓ₁, φ_line_direction_eq ℓ₂]
  set E := (D₂.starProjection - D₁.starProjection) halfVec with hE_def
  have h_off_bound : off_diff' ≤ c * off_diff + ‖halfVec‖ * dir_diff := by
    have h_eq : (φ_line ℓ₁).offset - (φ_line ℓ₂).offset =
        c • (ℓ₁.offset - ℓ₂.offset) + E := by
      rw [φ_line_offset_formula ℓ₁, φ_line_offset_formula ℓ₂]
      ext i
      simp [hE_def, sub_smul] <;> ring
    have h3 : ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖ ≤
        ‖c • (ℓ₁.offset - ℓ₂.offset)‖ + ‖E‖ := by
      rw [h_eq]; exact norm_add_le _ _
    have h4 : ‖c • (ℓ₁.offset - ℓ₂.offset)‖ = c * off_diff := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos c_pos] <;> rfl
    have h5 : ‖E‖ ≤ ‖(D₂.starProjection - D₁.starProjection)‖ * ‖halfVec‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h6 : ‖(D₂.starProjection - D₁.starProjection)‖ = dir_diff := by
      have h : D₂.starProjection - D₁.starProjection = -(D₁.starProjection - D₂.starProjection) := by
        ext v; simp
      rw [h, norm_neg]
    simpa [off_diff'] using calc
      off_diff'
        = ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖ := by rfl
      _ ≤ ‖c • (ℓ₁.offset - ℓ₂.offset)‖ + ‖E‖ := h3
      _ = c * off_diff + ‖E‖ := by rw [h4]
      _ ≤ c * off_diff + ‖(D₂.starProjection - D₁.starProjection)‖ * ‖halfVec‖ := by gcongr
      _ = c * off_diff + ‖halfVec‖ * dir_diff := by rw [h6, mul_comm dir_diff ‖halfVec‖] <;> ring
  have h_dist : dist (φ_line ℓ₁) (φ_line ℓ₂) =
      ‖(φ_line ℓ₁).1.direction.starProjection - (φ_line ℓ₂).1.direction.starProjection‖ + off_diff' := by
    change ‖(φ_line ℓ₁).1.direction.starProjection - (φ_line ℓ₂).1.direction.starProjection‖ +
      ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖ = _
    rw [h_dir] <;> rfl
  have h_orig : dist ℓ₁ ℓ₂ = dir_diff + off_diff := by
    change ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
      ‖ℓ₁.offset - ℓ₂.offset‖ = _
    <;> rfl
  have h9 : ‖halfVec‖ = Real.sqrt 2 / 2 := halfVec_norm
  have hU_eq : U = 1 + ‖halfVec‖ := by
    dsimp only [U]; rw [h9] <;> ring
  have h_c_le_U : c ≤ U := by
    rw [hU_eq]
    have h10 : 0 ≤ ‖halfVec‖ := by positivity
    have h11 : c = 1 / 4 := by rfl
    rw [h11]
    <;> linarith
  have hdir_nonneg : 0 ≤ dir_diff := norm_nonneg _
  have hoff_nonneg : 0 ≤ off_diff := norm_nonneg _
  rw [h_dist, h_orig, h_dir]
  calc
    dir_diff + off_diff'
      ≤ dir_diff + (c * off_diff + ‖halfVec‖ * dir_diff) := by gcongr
    _ = (1 + ‖halfVec‖) * dir_diff + c * off_diff := by ring
    _ ≤ U * dir_diff + U * off_diff := by
      have h11 : (1 + ‖halfVec‖) * dir_diff ≤ U * dir_diff := by
        have h12 : U = 1 + ‖halfVec‖ := hU_eq; rw [h12] <;> rfl
      have h13 : c * off_diff ≤ U * off_diff := by gcongr <;> linarith [h_c_le_U]
      linarith
    _ = U * (dir_diff + off_diff) := by ring

/-- Explicit version: U = 1 + √2/2 < 2, and Ncover(U*δ, φ_line '' S) ≤ Ncover(δ, S). -/
lemma ncover_line_upper_explicit :
  ∃ (U : ℝ), 0 < U ∧ U < 2 ∧
    ∀ (δ : ℝ) (S : Set AffineLine), 0 < δ →
      Metric.externalCoveringNumber (U * δ).toNNReal (φ_line '' S) ≤
        Metric.externalCoveringNumber δ.toNNReal S := by
  let U : ℝ := 1 + Real.sqrt 2 / 2
  have hU_pos : 0 < U := by positivity
  have hU_lt_2 : U < 2 := by
    have h : Real.sqrt 2 < 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    dsimp only [U] <;> linarith
  have h_main_upper : ∀ (ℓ₁ ℓ₂ : AffineLine),
      dist (φ_line ℓ₁) (φ_line ℓ₂) ≤ U * dist ℓ₁ ℓ₂ :=
    φ_line_lipschitz_explicit
  let U' : NNReal := ⟨U, by linarith⟩
  have hU'_coe : (U' : ℝ) = U := by exact_mod_cast rfl
  have h_lip' : LipschitzWith U' φ_line :=
    LipschitzWith.of_dist_le_mul h_main_upper
  have h1 : ∀ (δ : ℝ) (S : Set AffineLine), 0 < δ →
      Metric.externalCoveringNumber (U * δ).toNNReal (φ_line '' S) ≤
        Metric.externalCoveringNumber δ.toNNReal S := by
    intro δ S hδ
    have h_eq : U' * δ.toNNReal = (U * δ).toNNReal := by
      apply NNReal.coe_injective
      simp [hU'_coe, Real.toNNReal_of_nonneg hδ.le,
            Real.toNNReal_of_nonneg (mul_pos hU_pos hδ).le] <;> ring
    rw [← h_eq]
    exact DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_lipschitz (hf := h_lip')
  exact ⟨U, hU_pos, hU_lt_2, h1⟩

/-! ### 6. Offset bound after normalization -/

/-- If the original offset is bounded by 2, the normalized offset is also bounded by 2.
    In fact ‖normalized offset‖ ≤ 1/2 + √2 < 2. -/
lemma normalized_offset_bound {ℓ : AffineLine} (h : ℓ.offset ∈ Metric.closedBall (0 : Plane) 2) :
    (φ_line ℓ).offset ∈ Metric.closedBall (0 : Plane) 2 := by
  have h1 : ‖ℓ.offset‖ ≤ 2 := by simpa [Metric.mem_closedBall] using h
  let D := ℓ.1.direction
  have h2 : ‖D.starProjection halfVec‖ ≤ ‖halfVec‖ := by
    have h_eq : D.starProjection halfVec = D.orthogonalProjectionOnto halfVec := by
      rw [Submodule.starProjection_apply]
    rw [h_eq]
    exact Submodule.norm_orthogonalProjectionOnto_apply_le D halfVec
  have h3 : ‖(φ_line ℓ).offset‖ ≤ c * ‖ℓ.offset‖ + ‖halfVec‖ + ‖D.starProjection halfVec‖ := by
    rw [φ_line_offset_formula ℓ]
    have h31 : ‖c • ℓ.offset + halfVec - D.starProjection halfVec‖ ≤
        ‖c • ℓ.offset + halfVec‖ + ‖D.starProjection halfVec‖ := norm_sub_le _ _
    have h32 : ‖c • ℓ.offset + halfVec‖ ≤ ‖c • ℓ.offset‖ + ‖halfVec‖ := norm_add_le _ _
    have h33 : ‖c • ℓ.offset‖ = c * ‖ℓ.offset‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos c_pos] <;> ring
    linarith
  have h4 : ‖(φ_line ℓ).offset‖ ≤ c * 2 + 2 * ‖halfVec‖ := by
    calc ‖(φ_line ℓ).offset‖
      ≤ c * ‖ℓ.offset‖ + ‖halfVec‖ + ‖D.starProjection halfVec‖ := h3
    _ ≤ c * 2 + ‖halfVec‖ + ‖halfVec‖ := by
      have h41 : c * ‖ℓ.offset‖ ≤ c * 2 := by gcongr <;> exact c_pos.le
      linarith
    _ = c * 2 + 2 * ‖halfVec‖ := by ring
  have h5 : c * 2 + 2 * ‖halfVec‖ < 2 := by
    rw [halfVec_norm]
    simp [c] <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h6 : ‖(φ_line ℓ).offset‖ ≤ 2 := by linarith
  simpa [Metric.mem_closedBall] using h6

end DirecretisedFurstenbergEstimate.Section9.Normalization
