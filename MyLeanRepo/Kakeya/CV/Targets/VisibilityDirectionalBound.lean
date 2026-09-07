import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Complete proof of visibility_directional_surface_bound

This scratch file assembles all pieces into a complete proof.
-/

noncomputable section

open BigOperators Matrix MeasureTheory

namespace Kakeya.CV

-- ============================================================================
-- Algebraic pieces
-- ============================================================================

/-- Scaling each row of a 3x3 matrix by `(s i)⁻¹` scales the determinant
by the product of those scalars. -/
lemma det_row_scaling (v : Fin 3 → Point 3) (s : Fin 3 → ℝ) :
    Matrix.det (fun i j : Fin 3 => (s i)⁻¹ * v i j) =
      (∏ i : Fin 3, (s i)⁻¹) * Matrix.det (fun i j : Fin 3 => v i j) :=
  Matrix.det_mul_column (fun i : Fin 3 => (s i)⁻¹) (of (fun i j : Fin 3 => v i j))

/-- The triple volume of scaled vectors `u i := (s i)⁻¹ • v i`. -/
lemma tripleVolume_scaling (v : Fin 3 → Point 3) (s : Fin 3 → ℝ)
    (hs : ∀ i, 0 < s i) :
    tripleVolume (fun i => (s i)⁻¹ • v i) =
      (∏ i : Fin 3, (s i)⁻¹) * tripleVolume v := by
  have h1 : Matrix.det (fun i j : Fin 3 => ((s i)⁻¹ • v i) j) =
      (∏ i : Fin 3, (s i)⁻¹) * Matrix.det (fun i j : Fin 3 => v i j) :=
    det_row_scaling v s
  have hpos : 0 < ∏ i : Fin 3, (s i)⁻¹ := by
    apply Finset.prod_pos
    intro i _
    have hsi : 0 < s i := hs i
    positivity
  rw [tripleVolume, h1]
  rw [abs_mul, abs_of_pos hpos]
  rfl

/-- A convex body has positive Lebesgue volume. -/
lemma convexBody_volume_pos {K : Set (Point 3)}
    (hK : JohnEllipsoid.IsConvexBody K) :
    0 < (volume K).toReal := by
  have h_int : (interior K).Nonempty := hK.2.2
  have h_vol_pos : 0 < volume K :=
    MeasureTheory.Measure.measure_pos_of_nonempty_interior volume h_int
  have h_compact : IsCompact K := hK.2.1
  have h_lt_top : volume K < ⊤ := h_compact.measure_lt_top
  exact ENNReal.toReal_pos_iff.mpr ⟨h_vol_pos, h_lt_top⟩

/-- Algebraic rearrangement: from `tv ≤ (27/8) * sprod * vol`. -/
lemma cube_root_rearrangement (tv vol sprod : ℝ)
    (htv : 0 ≤ tv) (hvol : 0 < vol) (hsprod : 0 < sprod)
    (h : tv ≤ (27 / 8 : ℝ) * sprod * vol) :
    Real.rpow tv (1 / 3 : ℝ) * Real.rpow vol (-1 / 3 : ℝ) ≤
      (3 / 2 : ℝ) * Real.rpow sprod (1 / 3 : ℝ) := by
  set a : ℝ := (27 / 8 : ℝ) with ha_def
  have ha_pos : 0 < a := by norm_num
  have h1 : 0 ≤ a * sprod * vol := by positivity
  have h2 : Real.rpow tv (1 / 3 : ℝ) ≤ Real.rpow (a * sprod * vol) (1 / 3 : ℝ) :=
    Real.rpow_le_rpow htv h (by norm_num)
  have h3 : Real.rpow (a * sprod * vol) (1 / 3 : ℝ) =
      Real.rpow a (1 / 3 : ℝ) * Real.rpow sprod (1 / 3 : ℝ) * Real.rpow vol (1 / 3 : ℝ) := by
    have h31 : Real.rpow (a * sprod * vol) (1 / 3 : ℝ) =
        Real.rpow (a * sprod) (1 / 3 : ℝ) * Real.rpow vol (1 / 3 : ℝ) :=
      Real.mul_rpow (by positivity) (by positivity)
    have h32 : Real.rpow (a * sprod) (1 / 3 : ℝ) =
        Real.rpow a (1 / 3 : ℝ) * Real.rpow sprod (1 / 3 : ℝ) :=
      Real.mul_rpow (by positivity) (by positivity)
    rw [h31, h32]
  have h4 : Real.rpow a (1 / 3 : ℝ) = (3 / 2 : ℝ) := by
    have h41 : a = (3 / 2 : ℝ) ^ 3 := by norm_num
    rw [h41]
    have h_pos : 0 ≤ (3 / 2 : ℝ) := by norm_num
    have h_nat3 : ((3 / 2 : ℝ) ^ 3) = Real.rpow (3 / 2 : ℝ) (3 : ℝ) := by
      simp [Real.rpow_ofNat]
      <;> norm_num
    rw [h_nat3]
    have h_mul : Real.rpow (Real.rpow (3 / 2 : ℝ) (3 : ℝ)) (1 / 3 : ℝ) =
        Real.rpow (3 / 2 : ℝ) ((3 : ℝ) * (1 / 3 : ℝ)) := by
      exact (Real.rpow_mul h_pos (3 : ℝ) (1 / 3 : ℝ)).symm
    rw [h_mul]
    have h5 : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
    rw [h5]
    simp
  rw [h3, h4] at h2
  set b : ℝ := Real.rpow vol (1 / 3 : ℝ) with hb_def
  have hb_pos : 0 < b := Real.rpow_pos_of_pos hvol _
  set c : ℝ := Real.rpow vol (-1 / 3 : ℝ) with hc_def
  have hbc : b * c = 1 := by
    simp only [hb_def, hc_def]
    have h_add : Real.rpow vol ((1 / 3 : ℝ) + (-1 / 3 : ℝ)) =
        Real.rpow vol (1 / 3 : ℝ) * Real.rpow vol (-1 / 3 : ℝ) :=
      Real.rpow_add hvol (1 / 3) (-1 / 3)
    have h_sum : (1 / 3 : ℝ) + (-1 / 3 : ℝ) = 0 := by norm_num
    have h_zero : Real.rpow vol 0 = 1 := Real.rpow_zero vol
    rw [h_sum] at h_add
    rw [h_zero] at h_add
    exact h_add.symm
  have h5 : Real.rpow tv (1 / 3 : ℝ) ≤ (3 / 2 : ℝ) * Real.rpow sprod (1 / 3 : ℝ) * b := h2
  have h6 : Real.rpow tv (1 / 3 : ℝ) * c ≤ ((3 / 2 : ℝ) * Real.rpow sprod (1 / 3 : ℝ) * b) * c :=
    mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg (le_of_lt hvol) _)
  have h7 : ((3 / 2 : ℝ) * Real.rpow sprod (1 / 3 : ℝ) * b) * c =
      (3 / 2 : ℝ) * Real.rpow sprod (1 / 3 : ℝ) := by
    have h71 : ((3 / 2 : ℝ) * Real.rpow sprod (1 / 3 : ℝ) * b) * c =
        (3 / 2 : ℝ) * Real.rpow sprod (1 / 3 : ℝ) * (b * c) := by ring
    rw [h71, hbc]
    <;> ring
  rw [h7] at h6
  exact h6

-- ============================================================================
-- Geometric pieces
-- ============================================================================

/-- The linear map sending the i-th standard basis vector to u i. -/
def linearMapOfVectors (u : Fin 3 → Point 3) : Point 3 →ₗ[ℝ] Point 3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr ℝ u

/-- The cube [-1/3, 1/3]^3 in Point 3. -/
def thirdCube : Set (Point 3) :=
  {x | ∀ i : Fin 3, -1 / 3 ≤ x i ∧ x i ≤ 1 / 3}

/-- If K is convex and centrally symmetric, and u i ∈ K for each i, then
the image of the cube [-1/3, 1/3]^3 under the linear map e_i ↦ u i is
contained in K. -/
lemma cube_image_subset (K : Set (Point 3))
    (hK : Convex ℝ K)
    (h_symm : ∀ x, x ∈ K → -x ∈ K)
    (u : Fin 3 → Point 3) (hu : ∀ i, u i ∈ K) :
    (linearMapOfVectors u) '' thirdCube ⊆ K := by
  let T := linearMapOfVectors u
  have h0 : (0 : Point 3) ∈ K := by
    have h1 : u 0 ∈ K := hu 0
    have h2 : -u 0 ∈ K := h_symm (u 0) h1
    have h3 : (1 / 2 : ℝ) • u 0 + (1 / 2 : ℝ) • (-u 0) ∈ K :=
      hK h1 h2 (by norm_num) (by norm_num) (by norm_num)
    simpa using h3
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx1 : ∀ i : Fin 3, -1 / 3 ≤ x i := fun i => (hx i).1
  have hx2 : ∀ i : Fin 3, x i ≤ 1 / 3 := fun i => (hx i).2
  have h_abs : ∀ i : Fin 3, |x i| ≤ 1 / 3 := by
    intro i
    rw [abs_le]
    constructor
    · linarith [hx1 i]
    · linarith [hx2 i]
  let p : Fin 3 → Point 3 := fun i => if 0 ≤ x i then u i else -u i
  have hpK : ∀ i, p i ∈ K := by
    intro i
    have hpi : p i = if 0 ≤ x i then u i else -u i := by rfl
    rw [hpi]
    by_cases h : 0 ≤ x i
    · rw [if_pos h]; exact hu i
    · rw [if_neg h]; exact h_symm (u i) (hu i)
  have h_decomp : ∀ i, x i • u i = |x i| • p i := by
    intro i
    have hpi : p i = if 0 ≤ x i then u i else -u i := by rfl
    rw [hpi]
    by_cases h : 0 ≤ x i
    · rw [if_pos h, abs_of_nonneg h]
    · have h' : x i < 0 := by linarith
      rw [if_neg h, abs_of_neg h']
      simp [smul_neg, neg_smul]
  have hT : T x = ∑ i : Fin 3, x i • u i := by
    simp only [T, linearMapOfVectors]
    exact Module.Basis.constr_apply_fintype ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis u x
  rw [hT]
  set S : ℝ := ∑ i : Fin 3, |x i| with hS
  have hS_le1 : S ≤ 1 := by
    have h : ∑ i : Fin 3, |x i| ≤ ∑ i : Fin 3, (1 / 3 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact h_abs i
    simpa [hS] using h
  let w : Fin 4 → ℝ := fun j =>
    match j with
    | 0 => 1 - S
    | 1 => |x 0|
    | 2 => |x 1|
    | 3 => |x 2|
  let z : Fin 4 → Point 3 := fun j =>
    match j with
    | 0 => 0
    | 1 => p 0
    | 2 => p 1
    | 3 => p 2
  have h_nonneg : ∀ j : Fin 4, 0 ≤ w j := by
    intro j
    fin_cases j <;> simp [w, hS_le1]
  have h_sum1 : ∑ j : Fin 4, w j = 1 := by
    have h_sum4 : ∑ j : Fin 4, w j = w 0 + w 1 + w 2 + w 3 := by
      rw [Fin.sum_univ_four]
    rw [h_sum4]
    have hS' : S = |x 0| + |x 1| + |x 2| := by
      simp [hS, Fin.sum_univ_succ]
      <;> abel
    simp [w, hS']
    <;> linarith
  have hzK : ∀ j : Fin 4, z j ∈ K := by
    intro j
    fin_cases j <;> simp [z, h0, hpK]
  have h_final : ∑ j : Fin 4, w j • z j ∈ K :=
    hK.sum_mem (fun j _ => h_nonneg j) h_sum1 (fun j _ => hzK j)
  have h_eq : ∑ j : Fin 4, w j • z j = ∑ i : Fin 3, x i • u i := by
    have h_sum4 : ∑ j : Fin 4, w j • z j =
        (1 - S) • (0 : Point 3) + |x 0| • p 0 + |x 1| • p 1 + |x 2| • p 2 := by
      simp [w, z, Fin.sum_univ_four]
    rw [h_sum4]
    have h4 : (1 - S) • (0 : Point 3) = 0 := by simp
    rw [h4, zero_add]
    have h5 : |x 0| • p 0 + |x 1| • p 1 + |x 2| • p 2 = ∑ i : Fin 3, |x i| • p i := by
      simp [Fin.sum_univ_succ]
      <;> abel
    rw [h5]
    apply Finset.sum_congr rfl
    intro i _
    exact (h_decomp i).symm
  rw [← h_eq]
  exact h_final

-- ============================================================================
-- Volume of the cube
-- ============================================================================

/-- The volume of `thirdCube` is `8/27`. -/
lemma volume_thirdCube : volume thirdCube = ENNReal.ofReal (8 / 27 : ℝ) := by
  let e : Point 3 → (Fin 3 → ℝ) := WithLp.ofLp
  have hmp : MeasurePreserving e := PiLp.volume_preserving_ofLp (ι := Fin 3)
  let B' : Set (Fin 3 → ℝ) := Set.Icc (fun _ : Fin 3 => -(1 / 3 : ℝ)) (fun _ : Fin 3 => (1 / 3 : ℝ))
  have h_eq : thirdCube = e ⁻¹' B' := by
    ext x
    simp only [thirdCube, B', Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · intro h
      constructor
      · rw [Pi.le_def]
        intro i
        have h6 : (-(1 / 3 : ℝ)) = (-1 / 3 : ℝ) := by norm_num
        rw [h6]
        exact (h i).1
      · rw [Pi.le_def]
        intro i
        exact (h i).2
    · rintro ⟨h1, h2⟩
      intro i
      have h1' : -(1 / 3 : ℝ) ≤ x i := by
        rw [Pi.le_def] at h1
        exact h1 i
      have h1'' : -1 / 3 ≤ x i := by
        have h_eq : -(1 / 3 : ℝ) = -1 / 3 := by norm_num
        rw [h_eq] at h1'
        exact h1'
      have h2' : x i ≤ 1 / 3 := by
        rw [Pi.le_def] at h2
        exact h2 i
      exact ⟨h1'', h2'⟩
  have h_vol : volume thirdCube = volume B' := by
    rw [h_eq]
    exact hmp.measure_preimage (by measurability)
  rw [h_vol]
  rw [Real.volume_Icc_pi]
  have h4 : ∏ i : Fin 3, ENNReal.ofReal ((1 / 3 : ℝ) - (-(1 / 3 : ℝ))) =
      ENNReal.ofReal ((2 / 3 : ℝ) ^ 3) := by
    have h5 : ∀ i : Fin 3, ENNReal.ofReal ((1 / 3 : ℝ) - (-(1 / 3 : ℝ))) = ENNReal.ofReal (2 / 3 : ℝ) := by
      intro i <;> norm_num
    rw [Finset.prod_congr rfl (fun i _ => h5 i)]
    rw [Finset.prod_const, Finset.card_fin]
    rw [← ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 / 3 : ℝ)) 3]
  rw [h4]
  <;> norm_num

-- ============================================================================
-- Determinant of linearMapOfVectors
-- ============================================================================

/-- The determinant of `linearMapOfVectors u` equals the matrix determinant
with rows `u i`. -/
lemma det_linearMapOfVectors (u : Fin 3 → Point 3) :
    LinearMap.det (linearMapOfVectors u) = Matrix.det (fun i j : Fin 3 => u i j) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let T := linearMapOfVectors u
  have h1 : (LinearMap.toMatrix b b T).det = LinearMap.det T :=
    LinearMap.det_toMatrix b T
  have h2 : ∀ (i j : Fin 3), (LinearMap.toMatrix b b T) i j = u j i := by
    intro i j
    have h21 : T (b j) = u j := by
      simp only [T, linearMapOfVectors]
      exact Module.Basis.constr_basis b ℝ u j
    have h22 : (LinearMap.toMatrix b b T) i j = b.repr (T (b j)) i := by
      exact LinearMap.toMatrix_apply b b T i j
    rw [h22, h21]
    have h23 : b.repr (u j) i = (u j) i := by
      simpa [b, EuclideanSpace.basisFun_repr] using rfl
    exact h23
  have h3 : LinearMap.toMatrix b b T = Matrix.transpose (fun i j : Fin 3 => u i j) := by
    ext i j
    rw [h2, Matrix.transpose_apply]
    <;> rfl
  rw [← h1, h3, Matrix.det_transpose]

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem visibility_directional_surface_bound :
    VisibilityDirectionalBoundStatement := by
  use (3 / 2 : ℝ)
  constructor
  · norm_num
  · intro K hK h_symm v s hv hs hmem
    set u : Fin 3 → Point 3 := fun i => (s i)⁻¹ • v i with hu_def
    have huK : ∀ i, u i ∈ K := hmem
    let T : Point 3 →ₗ[ℝ] Point 3 := linearMapOfVectors u
    have h_cube : T '' thirdCube ⊆ K := cube_image_subset K hK.1 h_symm u huK
    have h_vol_mono : volume (T '' thirdCube) ≤ volume K := measure_mono h_cube
    have h_det : LinearMap.det T = Matrix.det (fun i j : Fin 3 => u i j) :=
      det_linearMapOfVectors u
    have h_vol_image : volume (T '' thirdCube) =
        ENNReal.ofReal |LinearMap.det T| * volume thirdCube :=
      MeasureTheory.Measure.addHaar_image_linearMap volume T thirdCube
    have h_vol_cube : volume thirdCube = ENNReal.ofReal (8 / 27 : ℝ) :=
      volume_thirdCube
    have hpos1 : 0 < ∏ i : Fin 3, (s i)⁻¹ := by
      apply Finset.prod_pos
      intro i _
      have hsi : 0 < s i := hs i
      exact inv_pos.mpr hsi
    have h_abs_det : |LinearMap.det T| = (∏ i : Fin 3, (s i)⁻¹) * tripleVolume v := by
      rw [h_det]
      exact tripleVolume_scaling v s hs
    set tv : ℝ := tripleVolume v with htv_def
    set vol : ℝ := (volume K).toReal with hvol_def
    set sprod : ℝ := ∏ i : Fin 3, s i with hsprod_def
    have htv : 0 ≤ tv := by
      simp [tv, tripleVolume, abs_nonneg]
    have hvol_pos : 0 < vol := convexBody_volume_pos hK
    have hsprod_pos : 0 < sprod := by
      simp [sprod]
      apply Finset.prod_pos
      intro i _
      exact hs i
    have h_compact : IsCompact K := hK.2.1
    have h_lt_top : volume K < ⊤ := h_compact.measure_lt_top
    have h_mul_nonneg : 0 ≤ (8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv := by positivity
    rw [h_vol_image, h_vol_cube] at h_vol_mono
    rw [h_abs_det] at h_vol_mono
    have h_nonneg2 : 0 ≤ (∏ i : Fin 3, (s i)⁻¹) * tv := by positivity
    have h_simp : ENNReal.ofReal ((∏ i : Fin 3, (s i)⁻¹) * tv) * ENNReal.ofReal (8 / 27 : ℝ) =
          ENNReal.ofReal (((∏ i : Fin 3, (s i)⁻¹) * tv) * (8 / 27 : ℝ)) := by
      rw [← ENNReal.ofReal_mul h_nonneg2]
      <;> rfl
    have h_simp2 : ((∏ i : Fin 3, (s i)⁻¹) * tv) * (8 / 27 : ℝ) = (8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv := by ring
    rw [h_simp, h_simp2] at h_vol_mono
    have h_ennreal : ENNReal.ofReal ((8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv) ≤ volume K := h_vol_mono
    have h_real : (8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv ≤ vol := by
      have h_a_ne_top : ENNReal.ofReal ((8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv) ≠ ⊤ := by simp
      have h5 : (ENNReal.ofReal ((8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv)).toReal ≤ (volume K).toReal :=
        (ENNReal.toReal_le_toReal h_a_ne_top h_lt_top.ne).mpr h_ennreal
      have h6 : (ENNReal.ofReal ((8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv)).toReal =
          (8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv := by
        rw [ENNReal.toReal_ofReal h_mul_nonneg]
      rw [h6] at h5
      exact h5
    have h_prod_inv : (∏ i : Fin 3, (s i)⁻¹) * sprod = 1 := by
      have h : (∏ i : Fin 3, (s i)⁻¹) * sprod = ∏ i : Fin 3, ((s i)⁻¹ * s i) := by
        rw [Finset.prod_mul_distrib] <;> rfl
      rw [h]
      apply Finset.prod_eq_one
      intro i _
      have hsi_ne : s i ≠ 0 := ne_of_gt (hs i)
      field_simp [hsi_ne] <;> ring
    have h_main : tv ≤ (27 / 8 : ℝ) * sprod * vol := by
      have h6 : (8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv ≤ vol := h_real
      have h7 : (27 / 8 : ℝ) * sprod * ((8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv) = tv := by
        have h8 : (27 / 8 : ℝ) * (8 / 27 : ℝ) = 1 := by norm_num
        calc
          (27 / 8 : ℝ) * sprod * ((8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv)
            = ((27 / 8 : ℝ) * (8 / 27 : ℝ)) * (sprod * (∏ i : Fin 3, (s i)⁻¹)) * tv := by ring
          _ = 1 * (sprod * (∏ i : Fin 3, (s i)⁻¹)) * tv := by rw [h8]
          _ = (sprod * (∏ i : Fin 3, (s i)⁻¹)) * tv := by ring
          _ = ((∏ i : Fin 3, (s i)⁻¹) * sprod) * tv := by ring
          _ = 1 * tv := by rw [h_prod_inv]
          _ = tv := by ring
      have h9 : tv ≤ (27 / 8 : ℝ) * sprod * vol := by
        calc tv
          = (27 / 8 : ℝ) * sprod * ((8 / 27 : ℝ) * (∏ i : Fin 3, (s i)⁻¹) * tv) := h7.symm
        _ ≤ (27 / 8 : ℝ) * sprod * vol := by gcongr <;> positivity
      exact h9
    exact cube_root_rearrangement tv vol sprod htv hvol_pos hsprod_pos h_main

end Kakeya.CV
