module

/-
  S-set transfer for line normalization φ(p) = p/4 + (1/2,1/2).

  If S is a (δ, s, C)-S-set of AffineLines, then φ_line '' S is a
  (δ/4, s, C · 4^s · Kpack³)-S-set.

  Key steps:
  1. φ_line is bijective on AffineLine (surjectivity via inverse offset formula)
  2. Inverse map is 4-Lipschitz → Ncover δ S ≤ Ncover (δ/4) (φ_line '' S)
  3. Upper Lipschitz U=1+√2/2 < 2, so 4U < 8 = 2³
  4. 3 doubling steps bridge δ/(4U) → δ with constant Kpack³
  5. Preimage of B(y,r) ⊆ B(x,4r) by surjectivity + lower Lipschitz

  Whiteprint node: section9 / line_normalization_sset
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnappingSSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9.LineNormalizationSSet

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CoveringUtils
open DirecretisedFurstenbergEstimate.Snapping
open DirecretisedFurstenbergEstimate.MainAppendix

abbrev Plane := EuclideanPlane
abbrev Ncover {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

/-! ### Basic definitions -/

def c : ℝ := 1 / 4
def halfVec : Plane := WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun _ => 1 / 2

lemma halfVec_norm : ‖halfVec‖ = Real.sqrt 2 / 2 := by
  have h5 : ‖halfVec‖ ^ 2 = 1 / 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [halfVec] <;> norm_num
  have h6 : 0 ≤ ‖halfVec‖ := by positivity
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

def φ (p : Plane) : Plane := c • p + halfVec

def φAffine : AffineMap ℝ Plane Plane :=
  { toFun := φ,
    linear := c • LinearMap.id,
    map_vadd' := fun (v : Plane) (p : Plane) => by
      ext i
      simp [φ, halfVec, vadd_eq_add] <;> ring }

lemma c_pos : 0 < c := by norm_num [c]
lemma c_ne_zero : c ≠ 0 := by norm_num [c]

/-! ### Helper lemmas -/

/-- Membership in an affine subspace through a base point. -/
lemma affine_mem_iff {S : AffineSubspace ℝ Plane} {p z : Plane} (hp : p ∈ S) :
    z ∈ S ↔ z - p ∈ S.direction := by
  constructor
  · intro hz
    exact S.vsub_mem_direction hz hp
  · intro h
    have h' : (z - p) +ᵥ p ∈ S := by exact (AffineSubspace.vadd_mem_iff_mem_of_mem_direction h).mpr hp
    have h'' : (z - p) +ᵥ p = z := by
      simp [vadd_eq_add] <;> abel
    rw [h''] at h'
    exact h'

lemma submodule_scale_eq {p : Submodule ℝ Plane} :
    Submodule.map (c • LinearMap.id) p = p := by
  ext x
  simp only [Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact p.smul_mem c hy
  · intro hx
    refine ⟨(c⁻¹ : ℝ) • x, p.smul_mem (c⁻¹) hx, ?_⟩
    have h : c • ((c⁻¹ : ℝ) • x) = x := by
      rw [smul_smul]; have h2 : c * c⁻¹ = 1 := by field_simp [c_ne_zero] <;> ring
      rw [h2, one_smul]
    exact h

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
      have h_in_bot : x - q ∈ (⊥ : Submodule ℝ Plane) := by rw [h_bot] at h''; exact h''
      simpa using h_in_bot
    exact sub_eq_zero.mp h_zero
  have h_main : EuclideanGeometry.orthogonalProjection S 0 = q := by
    rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
    exact ⟨hq1, by simpa using hq2⟩
  exact h_main

/-! ### φ_line definition and properties -/

def φ_line (ℓ : AffineLine) : AffineLine :=
  let img := AffineSubspace.map φAffine ℓ.1
  have h_dir1 : img.direction = Submodule.map φAffine.linear ℓ.1.direction := by
    simp [img, AffineSubspace.map_direction]
  have h_dir2 : Submodule.map φAffine.linear ℓ.1.direction = ℓ.1.direction := by
    have hlin : φAffine.linear = c • LinearMap.id := by rfl
    rw [hlin, submodule_scale_eq]
  have h_finrank : Module.finrank ℝ img.direction = 1 := by
    rw [h_dir1, h_dir2]; exact ℓ.2
  ⟨img, h_finrank⟩

lemma φ_line_direction_eq (ℓ : AffineLine) :
    (φ_line ℓ).1.direction = ℓ.1.direction := by
  have h1 : (φ_line ℓ).1.direction = Submodule.map φAffine.linear ℓ.1.direction := by
    simp [φ_line, AffineSubspace.map_direction]
  have hlin : φAffine.linear = c • LinearMap.id := by rfl
  rw [h1, hlin, submodule_scale_eq]

lemma φ_line_offset_formula (ℓ : AffineLine) :
    (φ_line ℓ).offset = c • ℓ.offset + halfVec - ℓ.1.direction.starProjection halfVec := by
  let D := ℓ.1.direction
  let q := ℓ.offset
  have hq_mem : q ∈ ℓ.1 := ℓ.offset_mem
  have hq_orth : q ∈ Dᗮ := by
    have h : (0 : Plane) -ᵥ q ∈ Dᗮ :=
      EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal ℓ.1 (0 : Plane)
    simpa using h
  have h_proj_q : D.starProjection q = 0 := by
    have h2 : D.orthogonalProjectionOnto q = 0 :=
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hq_orth
    have h1 : (D.starProjection q : Plane) = D.orthogonalProjectionOnto q :=
      Submodule.starProjection_apply D q
    have h3 : (D.starProjection q : Plane) = (0 : Plane) := by
      rw [h1, h2] <;> simp
    exact h3
  have h_fq_mem : φ q ∈ (φ_line ℓ).1 := by
    have h_img2 : ((φ_line ℓ).1 : Set Plane) = φAffine '' (ℓ.1 : Set Plane) := by rfl
    have h : φ q ∈ φAffine '' (ℓ.1 : Set Plane) := ⟨q, hq_mem, rfl⟩
    rw [h_img2] at *
    exact h
  have h_dir_eq : (φ_line ℓ).1.direction = D := φ_line_direction_eq ℓ
  have h_goal : (φ_line ℓ).offset = φ q - (φ_line ℓ).1.direction.starProjection (φ q) := by
    simp [AffineLine.offset]; exact offset_via_starProjection h_fq_mem
  have h10 : D.starProjection (φ q) = D.starProjection halfVec := by
    have h11 : φ q = c • q + halfVec := by rfl
    rw [h11]
    have h12 : D.starProjection (c • q + halfVec) = c • D.starProjection q + D.starProjection halfVec := by
      rw [D.starProjection.map_add, D.starProjection.map_smul]
    rw [h12, h_proj_q] <;> simp
  calc (φ_line ℓ).offset
    = φ q - (φ_line ℓ).1.direction.starProjection (φ q) := h_goal
  _ = φ q - D.starProjection (φ q) := by rw [h_dir_eq]
  _ = φ q - D.starProjection halfVec := by rw [h10]
  _ = c • q + halfVec - D.starProjection halfVec := by
    have h13 : φ q = c • q + halfVec := by rfl
    rw [h13]
  _ = c • ℓ.offset + halfVec - D.starProjection halfVec := by rfl

def bilip_U : ℝ := 1 + Real.sqrt 2 / 2
def bilip_K : ℝ := 4

lemma φ_line_upper_bound : ∀ (ℓ₁ ℓ₂ : AffineLine),
    dist (φ_line ℓ₁) (φ_line ℓ₂) ≤ bilip_U * dist ℓ₁ ℓ₂ := by
  intro ℓ₁ ℓ₂
  let D₁ := ℓ₁.1.direction; let D₂ := ℓ₂.1.direction
  let dir_diff := ‖D₁.starProjection - D₂.starProjection‖
  let off_diff := ‖ℓ₁.offset - ℓ₂.offset‖
  let off_diff' := ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖
  have h_dir : ‖(φ_line ℓ₁).1.direction.starProjection -
      (φ_line ℓ₂).1.direction.starProjection‖ = dir_diff := by
    rw [φ_line_direction_eq ℓ₁, φ_line_direction_eq ℓ₂]
  let E := (D₂.starProjection - D₁.starProjection) halfVec
  have h_eq : (φ_line ℓ₁).offset - (φ_line ℓ₂).offset = c • (ℓ₁.offset - ℓ₂.offset) + E := by
    rw [φ_line_offset_formula ℓ₁, φ_line_offset_formula ℓ₂]
    ext i; simp [E, sub_smul] <;> ring
  have h_off_bound : off_diff' ≤ c * off_diff + ‖halfVec‖ * dir_diff := by
    have h3 : ‖c • (ℓ₁.offset - ℓ₂.offset) + E‖ ≤ ‖c • (ℓ₁.offset - ℓ₂.offset)‖ + ‖E‖ := norm_add_le _ _
    have h4 : ‖c • (ℓ₁.offset - ℓ₂.offset)‖ = c * off_diff := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos c_pos] <;> rfl
    have h5 : ‖E‖ ≤ ‖(D₂.starProjection - D₁.starProjection)‖ * ‖halfVec‖ := ContinuousLinearMap.le_opNorm _ _
    have h6 : ‖(D₂.starProjection - D₁.starProjection)‖ = dir_diff := by
      have h : D₂.starProjection - D₁.starProjection = -(D₁.starProjection - D₂.starProjection) := by ext v; simp
      rw [h, norm_neg]
    have h7 : off_diff' = ‖c • (ℓ₁.offset - ℓ₂.offset) + E‖ := by
      rw [show off_diff' = ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖ from by rfl, h_eq]
    rw [h7]
    calc ‖c • (ℓ₁.offset - ℓ₂.offset) + E‖
      ≤ ‖c • (ℓ₁.offset - ℓ₂.offset)‖ + ‖E‖ := h3
    _ = c * off_diff + ‖E‖ := by rw [h4]
    _ ≤ c * off_diff + ‖(D₂.starProjection - D₁.starProjection)‖ * ‖halfVec‖ := by gcongr
    _ = c * off_diff + dir_diff * ‖halfVec‖ := by rw [h6] <;> ring
    _ = c * off_diff + ‖halfVec‖ * dir_diff := by ring
  have h_dist : dist (φ_line ℓ₁) (φ_line ℓ₂) = dir_diff + off_diff' := by
    have h : ∀ (x y : AffineLine), dist x y = AffineLine.dist x y := by intro x y; rfl
    rw [h (φ_line ℓ₁) (φ_line ℓ₂)]; dsimp only [AffineLine.dist]; rw [h_dir] <;> ring
  have h_orig : dist ℓ₁ ℓ₂ = dir_diff + off_diff := by
    have h : ∀ (x y : AffineLine), dist x y = AffineLine.dist x y := by intro x y; rfl
    rw [h ℓ₁ ℓ₂]; dsimp only [AffineLine.dist] <;> ring
  rw [h_dist, h_orig]
  have h9 : (1 + ‖halfVec‖) = bilip_U := by
    dsimp only [bilip_U]; rw [halfVec_norm] <;> ring
  have h10 : c ≤ bilip_U := by
    dsimp only [bilip_U, c]
    have h11 : 0 ≤ Real.sqrt 2 / 2 := by positivity
    linarith
  calc dir_diff + off_diff'
      ≤ dir_diff + (c * off_diff + ‖halfVec‖ * dir_diff) := by gcongr
    _ = (1 + ‖halfVec‖) * dir_diff + c * off_diff := by ring
    _ = bilip_U * dir_diff + c * off_diff := by rw [h9]
    _ ≤ bilip_U * dir_diff + bilip_U * off_diff := by gcongr
    _ = bilip_U * (dir_diff + off_diff) := by ring

lemma φ_line_lower_bound : ∀ (ℓ₁ ℓ₂ : AffineLine),
    dist ℓ₁ ℓ₂ ≤ bilip_K * dist (φ_line ℓ₁) (φ_line ℓ₂) := by
  intro ℓ₁ ℓ₂
  let D₁ := ℓ₁.1.direction; let D₂ := ℓ₂.1.direction
  let dir_diff := ‖D₁.starProjection - D₂.starProjection‖
  let off_diff := ‖ℓ₁.offset - ℓ₂.offset‖
  let off_diff' := ‖(φ_line ℓ₁).offset - (φ_line ℓ₂).offset‖
  have h_dir : ‖(φ_line ℓ₁).1.direction.starProjection -
      (φ_line ℓ₂).1.direction.starProjection‖ = dir_diff := by
    rw [φ_line_direction_eq ℓ₁, φ_line_direction_eq ℓ₂]
  let E := (D₂.starProjection - D₁.starProjection) halfVec
  have h_eq : (φ_line ℓ₁).offset - (φ_line ℓ₂).offset = c • (ℓ₁.offset - ℓ₂.offset) + E := by
    rw [φ_line_offset_formula ℓ₁, φ_line_offset_formula ℓ₂]
    ext i; simp [E, sub_smul] <;> ring
  have h_E_bound : ‖E‖ ≤ ‖halfVec‖ * dir_diff := by
    have h7 : ‖E‖ ≤ ‖(D₂.starProjection - D₁.starProjection)‖ * ‖halfVec‖ := ContinuousLinearMap.le_opNorm _ _
    have h8 : ‖(D₂.starProjection - D₁.starProjection)‖ = dir_diff := by
      have h : D₂.starProjection - D₁.starProjection = -(D₁.starProjection - D₂.starProjection) := by ext v; simp
      rw [h, norm_neg]
    have h9 : ‖E‖ ≤ dir_diff * ‖halfVec‖ := by
      rw [h8] at h7; exact h7
    linarith
  have h1 : off_diff ≤ c⁻¹ * off_diff' + c⁻¹ * ‖halfVec‖ * dir_diff := by
    have h2 : ℓ₁.offset - ℓ₂.offset = c⁻¹ • ((φ_line ℓ₁).offset - (φ_line ℓ₂).offset) - c⁻¹ • E := by
      rw [φ_line_offset_formula ℓ₁, φ_line_offset_formula ℓ₂]
      ext i; simp [E, sub_smul] <;> field_simp [c_ne_zero] <;> ring
    have h3 : ‖ℓ₁.offset - ℓ₂.offset‖ ≤ ‖c⁻¹ • ((φ_line ℓ₁).offset - (φ_line ℓ₂).offset)‖ + ‖c⁻¹ • E‖ := by
      rw [h2]; exact norm_sub_le _ _
    have h_cinv_pos : 0 < c⁻¹ := inv_pos.mpr c_pos
    have h4 : ‖c⁻¹ • ((φ_line ℓ₁).offset - (φ_line ℓ₂).offset)‖ = c⁻¹ * off_diff' := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos h_cinv_pos] <;> ring
    have h5 : ‖c⁻¹ • E‖ = c⁻¹ * ‖E‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos h_cinv_pos] <;> ring
    calc _ ≤ ‖c⁻¹ • _‖ + ‖c⁻¹ • E‖ := h3
      _ = c⁻¹ * off_diff' + c⁻¹ * ‖E‖ := by rw [h4, h5] <;> ring
      _ ≤ c⁻¹ * off_diff' + c⁻¹ * (‖halfVec‖ * dir_diff) := by
        have hcinv_nonneg : 0 ≤ c⁻¹ := by positivity
        have h_bound : c⁻¹ * ‖E‖ ≤ c⁻¹ * (‖halfVec‖ * dir_diff) :=
          mul_le_mul_of_nonneg_left h_E_bound hcinv_nonneg
        linarith
      _ = c⁻¹ * off_diff' + c⁻¹ * ‖halfVec‖ * dir_diff := by ring
  have h_dist : dist (φ_line ℓ₁) (φ_line ℓ₂) = dir_diff + off_diff' := by
    have h : ∀ (x y : AffineLine), dist x y = AffineLine.dist x y := by intro x y; rfl
    rw [h (φ_line ℓ₁) (φ_line ℓ₂)]; dsimp only [AffineLine.dist]; rw [h_dir] <;> ring
  have h_orig : dist ℓ₁ ℓ₂ = dir_diff + off_diff := by
    have h : ∀ (x y : AffineLine), dist x y = AffineLine.dist x y := by intro x y; rfl
    rw [h ℓ₁ ℓ₂]; dsimp only [AffineLine.dist] <;> ring
  rw [h_orig, h_dist]
  have h_c_inv : c⁻¹ = 4 := by simp [c] <;> norm_num
  have h_bound1 : 1 + c⁻¹ * ‖halfVec‖ ≤ bilip_K := by
    dsimp only [bilip_K]
    rw [h_c_inv, halfVec_norm]
    have h : 1 + (4 : ℝ) * (Real.sqrt 2 / 2) ≤ 4 := by
      have h2 : Real.sqrt 2 ≤ 3 / 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    exact h
  have h_bound2 : c⁻¹ ≤ bilip_K := by
    dsimp only [bilip_K]; rw [h_c_inv] <;> norm_num
  calc dir_diff + off_diff
      ≤ dir_diff + (c⁻¹ * off_diff' + c⁻¹ * ‖halfVec‖ * dir_diff) := by gcongr
    _ = (1 + c⁻¹ * ‖halfVec‖) * dir_diff + c⁻¹ * off_diff' := by ring
    _ ≤ bilip_K * dir_diff + bilip_K * off_diff' := by gcongr
    _ = bilip_K * (dir_diff + off_diff') := by ring

/-! ### Surjectivity and inverse -/

/-- φ_line is surjective: for any ℓ', construct ℓ with φ_line ℓ = ℓ'. -/
lemma φ_line_surjective (ℓ' : AffineLine) : ∃ (ℓ : AffineLine), φ_line ℓ = ℓ' := by
  let D := ℓ'.1.direction
  let q' := ℓ'.offset
  have hq'_orth : q' ∈ Dᗮ := by
    have h : (0 : Plane) -ᵥ q' ∈ Dᗮ :=
      EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal ℓ'.1 (0 : Plane)
    simpa using h
  let h_proj := D.starProjection halfVec
  let q : Plane := 4 • (q' - halfVec + h_proj)
  have h1 : halfVec - h_proj ∈ Dᗮ := D.sub_starProjection_mem_orthogonal halfVec
  have h2 : q' - (halfVec - h_proj) ∈ Dᗮ := Dᗮ.sub_mem hq'_orth h1
  have hq_eq : q = (4 : ℝ) • (q' - (halfVec - h_proj)) := by
    have h3 : q' - halfVec + h_proj = q' - (halfVec - h_proj) := by abel
    dsimp only [q]
    have h4 : (4 : ℕ) • (q' - halfVec + h_proj) = (4 : ℝ) • (q' - (halfVec - h_proj)) := by
      rw [h3]
      norm_cast
    exact h4
  have hq_orth : q ∈ Dᗮ := by
    rw [hq_eq]
    exact Dᗮ.smul_mem (4 : ℝ) h2
  let S : AffineSubspace ℝ Plane := AffineSubspace.mk' q D
  have hq_in_S : q ∈ S := AffineSubspace.self_mem_mk' q D
  letI : Nonempty S := ⟨q, hq_in_S⟩
  have hS_dir : S.direction = D := AffineSubspace.direction_mk' q D
  have hS_offset : EuclideanGeometry.orthogonalProjection S 0 = q := by
    have h' : D.starProjection q = 0 := by
      have h2 : D.orthogonalProjectionOnto q = 0 :=
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hq_orth
      have h1 : (D.starProjection q : Plane) = D.orthogonalProjectionOnto q :=
        Submodule.starProjection_apply D q
      have h3 : (D.starProjection q : Plane) = (0 : Plane) := by
        rw [h1, h2] <;> simp
      exact h3
    have h_main : EuclideanGeometry.orthogonalProjection S 0 = q - S.direction.starProjection q :=
      offset_via_starProjection hq_in_S
    rw [h_main, hS_dir, h'] <;> simp
  let ℓ : AffineLine := ⟨S, by rw [hS_dir]; exact ℓ'.2⟩
  have h1 : (φ_line ℓ).1.direction = D := by
    rw [φ_line_direction_eq ℓ, hS_dir]
  have h_loff : ℓ.offset = q := by
    exact hS_offset
  have h2 : (φ_line ℓ).offset = q' := by
    rw [φ_line_offset_formula ℓ]
    have hℓ_dir : ℓ.1.direction = D := hS_dir
    rw [hℓ_dir]
    have h4 : c • ℓ.offset + halfVec - D.starProjection halfVec = q' := by
      rw [h_loff]
      have h5 : c • q + halfVec - D.starProjection halfVec = q' := by
        have h6 : c = 1 / 4 := by norm_num [c]
        rw [h6, hq_eq]
        have h7 : h_proj = D.starProjection halfVec := by rfl
        rw [h7]
        have h8 : (1 / 4 : ℝ) • ((4 : ℝ) • (q' - (halfVec - D.starProjection halfVec))) =
            q' - (halfVec - D.starProjection halfVec) := by
          rw [smul_smul] <;> norm_num <;> simp
        rw [h8] <;> abel
      exact h5
    exact h4
  have h_main : φ_line ℓ = ℓ' := by
    apply Subtype.ext
    ext z
    have h51 : z ∈ (φ_line ℓ).1 ↔ z - (φ_line ℓ).offset ∈ (φ_line ℓ).1.direction :=
      affine_mem_iff (AffineLine.offset_mem _)
    have h52 : z ∈ ℓ'.1 ↔ z - ℓ'.offset ∈ ℓ'.1.direction :=
      affine_mem_iff (AffineLine.offset_mem _)
    rw [h51, h52, h2, h1]
  exact ⟨ℓ, h_main⟩

/-- Inverse of φ_line, defined globally using surjectivity. -/
noncomputable def φ_line_inverse (ℓ' : AffineLine) : AffineLine :=
  Classical.choose (φ_line_surjective ℓ')

lemma φ_line_inverse_spec (ℓ' : AffineLine) : φ_line (φ_line_inverse ℓ') = ℓ' :=
  Classical.choose_spec (φ_line_surjective ℓ')

/-- φ_line is injective. -/
lemma φ_line_injective {ℓ₁ ℓ₂ : AffineLine} (h : φ_line ℓ₁ = φ_line ℓ₂) : ℓ₁ = ℓ₂ := by
  have hdir : ℓ₁.1.direction = ℓ₂.1.direction := by
    have h1 := congr_arg (fun (x : AffineLine) => x.1.direction) h
    rw [φ_line_direction_eq ℓ₁, φ_line_direction_eq ℓ₂] at h1
    exact h1
  have hoff : ℓ₁.offset = ℓ₂.offset := by
    have h2 := congr_arg (fun (x : AffineLine) => x.offset) h
    rw [φ_line_offset_formula ℓ₁, φ_line_offset_formula ℓ₂] at h2
    rw [hdir] at h2
    simpa [c_ne_zero] using h2
  apply Subtype.ext
  ext z
  have h51 : z ∈ ℓ₁.1 ↔ z - ℓ₁.offset ∈ ℓ₁.1.direction :=
      affine_mem_iff (AffineLine.offset_mem _)
  have h52 : z ∈ ℓ₂.1 ↔ z - ℓ₂.offset ∈ ℓ₂.1.direction :=
      affine_mem_iff (AffineLine.offset_mem _)
  rw [h51, h52, hoff, hdir]

/-- The inverse map is 4-Lipschitz. -/
lemma φ_line_inverse_lipschitz :
    LipschitzWith (4 : NNReal) φ_line_inverse := by
  have h_main : ∀ (x y : AffineLine), dist (φ_line_inverse x) (φ_line_inverse y) ≤ (4 : ℝ) * dist x y := by
    intro x y
    have h1 : φ_line (φ_line_inverse x) = x := φ_line_inverse_spec x
    have h2 : φ_line (φ_line_inverse y) = y := φ_line_inverse_spec y
    have h3 : dist (φ_line_inverse x) (φ_line_inverse y) ≤ bilip_K * dist (φ_line (φ_line_inverse x)) (φ_line (φ_line_inverse y)) :=
      φ_line_lower_bound (φ_line_inverse x) (φ_line_inverse y)
    have hK : bilip_K = 4 := by rfl
    rw [hK, h1, h2] at h3
    exact h3
  exact LipschitzWith.of_dist_le_mul h_main

/-! ### S-set transfer theorem -/

/-- If S is a (δ, s, C)-S-set of AffineLines, then φ_line '' S is a
    (δ/4, s, C · 4^s · Kpack³)-S-set. -/
theorem line_normalization_sset_transfer
    {δ s C : ℝ} {S : Set AffineLine}
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    (hS : IsDeltaSSet δ s C S) :
    IsDeltaSSet (δ / 4) s (C * (4 : ℝ) ^ s * (MainAppendix.affineLine_packing_constant : ℝ) ^ 3)
      (φ_line '' S) := by
  let Kpack : ℕ := MainAppendix.affineLine_packing_constant
  have hKpack_pos : 0 < (Kpack : ℝ) := by
    exact_mod_cast affineLine_packing_constant_pos'
  let A : Set AffineLine := φ_line '' S
  have hA_nonempty : A.Nonempty := hS.1.image φ_line
  have hδ4_pos : 0 < δ / 4 := by positivity
  let C' : ℝ := C * (4 : ℝ) ^ s * (Kpack : ℝ) ^ 3
  have hC'_pos : 0 < C' := by positivity

  -- Backward cover: Ncover δ S ≤ Ncover (δ/4) A
  have h_backward : Ncover δ S ≤ Ncover (δ / 4) A := by
    have h_lip : LipschitzWith (4 : NNReal) φ_line_inverse := φ_line_inverse_lipschitz
    let ε4 : NNReal := (δ / 4).toNNReal
    have h1 : Metric.externalCoveringNumber ((4 : NNReal) * ε4) (φ_line_inverse '' A) ≤
        Metric.externalCoveringNumber ε4 A :=
      externalCoveringNumber_image_lipschitz (hf := h_lip) (ε := ε4)
    have h2 : (4 : NNReal) * ε4 = δ.toNNReal := by
      apply NNReal.coe_injective
      simp [ε4, hδ4_pos.le, hδ_pos.le] <;> ring
    rw [h2] at h1
    have h3 : φ_line_inverse '' A = S := by
      ext z
      simp only [A, Set.mem_image]
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        have h4 : φ_line (φ_line_inverse (φ_line x)) = φ_line x := φ_line_inverse_spec (φ_line x)
        have h5 : φ_line_inverse (φ_line x) = x := φ_line_injective h4
        rw [h5]; exact hx
      · intro hz
        refine ⟨φ_line z, ⟨z, hz, rfl⟩, ?_⟩
        have h6 : φ_line (φ_line_inverse (φ_line z)) = φ_line z := φ_line_inverse_spec (φ_line z)
        exact φ_line_injective h6
    rw [h3] at h1
    simpa [Ncover] using h1

  -- Upper Lipschitz constant
  let U' : NNReal := ⟨bilip_U, by dsimp only [bilip_U]; positivity⟩
  have hU'_coe : (U' : ℝ) = bilip_U := by exact_mod_cast rfl
  have h_lip_upper : LipschitzWith U' φ_line := LipschitzWith.of_dist_le_mul φ_line_upper_bound

  have hU_lt_2 : bilip_U < 2 := by
    dsimp only [bilip_U]
    have h1 : Real.sqrt 2 / 2 < 1 := by
      have h2 : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    linarith

  refine' ⟨hA_nonempty, hδ4_pos, hC'_pos, hs_nonneg, _⟩
  intro y r hr
  have hr_pos : 0 ≤ r := by linarith

  by_cases h_empty : (A ∩ Metric.closedBall y r).Nonempty
  · rcases h_empty with ⟨T1, hT1_in⟩

    -- Since φ_line is surjective, find x with φ_line x = y
    let x : AffineLine := φ_line_inverse y
    have hφx : φ_line x = y := φ_line_inverse_spec y

    -- Preimage of B(y, r) is contained in B(x, 4r)
    have h_preimage : A ∩ Metric.closedBall y r ⊆ φ_line '' (S ∩ Metric.closedBall x (4 * r)) := by
      intro T hT
      rcases hT.1 with ⟨ℓ, hℓ_in_S, rfl⟩
      have h_dist : dist (φ_line ℓ) y ≤ r := Metric.mem_closedBall.mp hT.2
      have h_dist' : dist ℓ x ≤ 4 * r := by
        have h4 : dist ℓ x ≤ bilip_K * dist (φ_line ℓ) (φ_line x) := φ_line_lower_bound ℓ x
        have hK : bilip_K = 4 := by rfl
        rw [hK, hφx] at h4
        exact h4.trans (by gcongr)
      exact ⟨ℓ, ⟨hℓ_in_S, Metric.mem_closedBall.mpr h_dist'⟩, rfl⟩

    let ε_src : ℝ := δ / (4 * bilip_U)
    have hU_pos : 0 < bilip_U := by dsimp only [bilip_U]; positivity
    have hε_src_pos : 0 < ε_src := by
      dsimp only [ε_src]
      apply div_pos hδ_pos
      positivity

    -- Upper Lipschitz: Ncover (δ/4) (φ_line '' B) ≤ Ncover ε_src B
    have h_forward : ∀ (B : Set AffineLine),
        Ncover (δ / 4) (φ_line '' B) ≤ Ncover ε_src B := by
      intro B
      have h_eq : bilip_U * ε_src = δ / 4 := by
        dsimp only [ε_src]
        have hU_ne : bilip_U ≠ 0 := hU_pos.ne'
        field_simp [hU_ne] <;> ring
      have h_eq' : U' * ε_src.toNNReal = (δ / 4).toNNReal := by
        apply NNReal.coe_injective
        have h51 : (ε_src.toNNReal : ℝ) = ε_src := by simp [hε_src_pos.le]
        simp [hU'_coe, h51, h_eq, hδ4_pos.le] <;> ring
      have h := externalCoveringNumber_image_lipschitz (hf := h_lip_upper) (ε := ε_src.toNNReal) (A := B)
      rw [h_eq'] at h
      simpa [Ncover] using h

    have hε_gt_delta8 : ε_src > δ / 8 := by
      dsimp only [ε_src]
      have h1 : 4 * bilip_U < 8 := by linarith [hU_lt_2]
      have h2 : δ / (4 * bilip_U) > δ / 8 := by
        apply div_lt_div_of_pos_left hδ_pos <;> linarith
      exact h2

    have h_anti : ∀ (B : Set AffineLine), Ncover ε_src B ≤ Ncover (δ / 8) B := by
      intro B
      have h_le : (δ / 8).toNNReal ≤ ε_src.toNNReal := by
        have h : δ / 8 ≤ ε_src := hε_gt_delta8.le
        exact Real.toNNReal_mono h
      have h : Metric.externalCoveringNumber ε_src.toNNReal B ≤
          Metric.externalCoveringNumber (δ / 8).toNNReal B :=
        Metric.externalCoveringNumber_anti h_le
      simpa [Ncover] using h

    have h_doubling : ∀ (B : Set AffineLine),
        Ncover (δ / 8) B ≤ (Kpack : ENNReal) ^ 3 * Ncover δ B := by
      intro B
      have hδ8_pos : 0 < δ / 8 := by positivity
      have h1 := affineLine_doubling_iter (δ / 8) hδ8_pos 3 (S := B)
      have h2 : (((2^3 : ℕ) : ℝ) * (δ / 8)) = δ := by norm_num <;> ring
      rw [h2] at h1
      simpa [Ncover] using h1

    have h4r_geδ : δ ≤ 4 * r := by linarith
    have h_sset : Ncover δ (S ∩ Metric.closedBall x (4 * r)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (4 * r)) ^ s * Ncover δ S :=
      hS.2.2.2.2 x (4 * r) h4r_geδ

    have h_mono1 : Ncover (δ / 4) (A ∩ Metric.closedBall y r) ≤
        Ncover (δ / 4) (φ_line '' (S ∩ Metric.closedBall x (4 * r))) := by
      have h : Metric.externalCoveringNumber (δ / 4).toNNReal (A ∩ Metric.closedBall y r) ≤
          Metric.externalCoveringNumber (δ / 4).toNNReal (φ_line '' (S ∩ Metric.closedBall x (4 * r))) :=
        Metric.externalCoveringNumber_mono_set h_preimage
      simpa [Ncover] using h

    have h_final : Ncover (δ / 4) (A ∩ Metric.closedBall y r) ≤
        (Kpack : ENNReal) ^ 3 * ENNReal.ofReal C * ((4 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) * Ncover (δ / 4) A := by
      calc Ncover (δ / 4) (A ∩ Metric.closedBall y r)
        ≤ Ncover (δ / 4) (φ_line '' (S ∩ Metric.closedBall x (4 * r))) := h_mono1
      _ ≤ Ncover ε_src (S ∩ Metric.closedBall x (4 * r)) := h_forward _
      _ ≤ Ncover (δ / 8) (S ∩ Metric.closedBall x (4 * r)) := h_anti _
      _ ≤ (Kpack : ENNReal) ^ 3 * Ncover δ (S ∩ Metric.closedBall x (4 * r)) := h_doubling _
      _ ≤ (Kpack : ENNReal) ^ 3 * (ENNReal.ofReal C * (ENNReal.ofReal (4 * r)) ^ s * Ncover δ S) := by gcongr
      _ = (Kpack : ENNReal) ^ 3 * ENNReal.ofReal C * ((4 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) * Ncover δ S := by
        have h_pos4 : 0 ≤ (4 : ℝ) := by norm_num
        have h1 : ENNReal.ofReal (4 * r) = (4 : ENNReal) * ENNReal.ofReal r := by
          rw [ENNReal.ofReal_mul h_pos4] <;> simp
        rw [h1]
        have h2 : ((4 : ENNReal) * ENNReal.ofReal r) ^ s = (4 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s :=
          ENNReal.mul_rpow_of_nonneg (4 : ENNReal) (ENNReal.ofReal r) hs_nonneg
        rw [h2] <;> ring
      _ ≤ (Kpack : ENNReal) ^ 3 * ENNReal.ofReal C * ((4 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) * Ncover (δ / 4) A := by
        gcongr <;> exact h_backward

    have h_final' : Ncover (δ / 4) (A ∩ Metric.closedBall y r) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Ncover (δ / 4) A := by
      have h_posC : 0 ≤ C := hC_pos.le
      have h_pos4s : 0 ≤ (4 : ℝ) ^ s := by positivity
      have h_posK3 : 0 ≤ (Kpack : ℝ) ^ 3 := by positivity
      have h_eq1 : ENNReal.ofReal C' =
          (Kpack : ENNReal) ^ 3 * (4 : ENNReal) ^ s * ENNReal.ofReal C := by
        have h : C' = (Kpack : ℝ) ^ 3 * ((4 : ℝ) ^ s * C) := by
          simp only [C'] <;> ring
        rw [h]
        rw [ENNReal.ofReal_mul h_posK3, ENNReal.ofReal_mul h_pos4s]
        have h5 : ENNReal.ofReal ((4 : ℝ) ^ s) = (4 : ENNReal) ^ s := by
          have h6 : (ENNReal.ofReal (4 : ℝ)) ^ s = ENNReal.ofReal ((4 : ℝ) ^ s) :=
            ENNReal.ofReal_rpow_of_pos (by norm_num)
          have h7 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by simp
          rw [h7]; exact h6.symm
        have h6 : ENNReal.ofReal ((Kpack : ℝ) ^ 3) = (Kpack : ENNReal) ^ 3 := by
          simp [ENNReal.ofReal_pow] <;> rfl
        rw [h5, h6] <;> ring
      rw [h_eq1]
      convert h_final using 1
      <;> simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    exact h_final'

  · have h_empty' : A ∩ Metric.closedBall y r = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h_empty
    rw [h_empty']
    simp

end DirecretisedFurstenbergEstimate.Section9.LineNormalizationSSet
