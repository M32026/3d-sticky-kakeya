/-
# General Fritz John conditions (augmented, non-symmetric case)

This module proves the general augmented Fritz John conditions for the minimal
enclosing ellipsoid (normalized to the unit ball).

## Proof route

1. **Contradiction lemma**: If `quadForm C u + 2⟨b,u⟩ < α` for all contact points
   and `n*α - trace(C) < 0`, then there exists a smaller-volume ellipsoid containing K.
   (Uses `K_subset_augmented_perturbation` and `augmented_perturbation_volume_less`.)

2. **Pair identity**: By contradiction via strict separation in `E(n) × Mat(n)`.
   If `(0, I/n) ∉ conv{(u, u⊗u)}`, separate to get `(C, b, α)` violating the
   contradiction lemma, contradicting volume minimality.

3. **Extraction**: From convex hull membership, extract finite contact points
   and weights satisfying the five Fritz John conditions.

## Whiteprint node
general_fritz_john_augmented
-/

import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Perturbation
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Separation
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.ConvexHullUtils
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.AugmentedPerturbation
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.AugmentedContradiction
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

noncomputable section


open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

variable {n : ℕ} {K : Set (E n)}

/-- Normed group structure for matrices (Frobenius norm). -/
local instance matNormedAddCommGroup {n : ℕ} : NormedAddCommGroup (Mat n) :=
  Matrix.normedAddCommGroup

/-- Normed space structure for matrices (Frobenius norm). -/
local instance matNormedSpace {n : ℕ} : NormedSpace ℝ (Mat n) :=
  Matrix.normedSpace

/-- Outer product matrix u u^T. -/
def outerProduct (u : E n) : Mat n := Matrix.vecMulVec u u

/-- The contact set K ∩ {‖x‖ = 1}. -/
def contactSet (K : Set (E n)) : Set (E n) := K ∩ {x | ‖x‖ = 1}

/-- Product-space contact set: {(u, u⊗u) : u ∈ contactSet K}. -/
def pairContactSet (K : Set (E n)) : Set (E n × Mat n) :=
  Set.image (fun u : E n => (u, outerProduct u)) (contactSet K)

lemma outerProduct_symm (u : E n) : (outerProduct u).IsSymm := by
  ext i j
  simp [outerProduct, Matrix.vecMulVec, Matrix.transpose_apply] <;> ring

lemma outerProduct_continuous : Continuous (outerProduct : E n → Mat n) := by
  have h1 : Continuous (fun p : E n × E n => Matrix.vecMulVec p.1 p.2) := by fun_prop
  have h2 : Continuous (fun u : E n => (u, u)) := by fun_prop
  exact h1.comp h2

lemma pairContactSet_compact (hK : IsConvexBody K) :
    IsCompact (pairContactSet K) := by
  have h1 : IsCompact K := hK.2.1
  have h2 : IsClosed {x : E n | ‖x‖ = 1} := isClosed_eq continuous_norm continuous_const
  have h3 : IsCompact (contactSet K) := h1.inter_right h2
  have h4 : Continuous (fun u : E n => (u, outerProduct u)) :=
    Continuous.prodMk continuous_id outerProduct_continuous
  exact h3.image h4

/-- Frobenius pairing with scaled identity equals c * trace. -/
lemma frobenius_identity (M : Mat n) (c : ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, M i j * (c • (1 : Mat n)) i j = c * M.trace := by
  have h1 : ∀ (i : Fin n), ∑ j : Fin n, M i j * (c • (1 : Mat n)) i j = c * M i i := by
    intro i
    have h2 : ∀ (j : Fin n), M i j * (c • (1 : Mat n)) i j = if j = i then c * M i i else 0 := by
      intro j
      have hsmul : (c • (1 : Mat n)) i j = c * (if i = j then (1 : ℝ) else 0) := by
        simp [Matrix.smul_apply, Matrix.one_apply] <;> ring
      rw [hsmul]
      by_cases h : i = j
      · subst h; simp [if_pos] <;> ring
      · have hji : j ≠ i := by tauto
        rw [if_neg h, if_neg hji] <;> ring
    rw [Finset.sum_congr rfl (fun j _ => h2 j)]
    have h4 : ∑ j : Fin n, (if j = i then c * M i i else 0) = c * M i i := by
      rw [Finset.sum_ite_eq'] <;> simp
    exact h4
  calc
    ∑ i, ∑ j, M i j * (c • (1 : Mat n)) i j
      = ∑ i, (c * M i i) := by apply Finset.sum_congr rfl; intro i _; exact h1 i
    _ = c * ∑ i, M i i := by rw [Finset.mul_sum]
    _ = c * M.trace := by simp [Matrix.trace]

/-- If contact set is empty, K is strictly inside unit ball, contradicting minimality. -/
lemma contactSet_nonempty (hn : 0 < n) (hK : IsConvexBody K)
    (h_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (h_min : ∀ (c : E n) (A : E n ≃ₗ[ℝ] E n),
        K ⊆ ellipsoid c A →
        volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c A)) :
    (contactSet K).Nonempty := by
  by_contra h_empty
  have h1 : ∀ x ∈ K, ‖x‖ < 1 := by
    intro x hx
    have h2 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall] using h_sub hx
    by_contra h3
    have h4 : ‖x‖ = 1 := by linarith
    have h5 : x ∈ contactSet K := ⟨hx, h4⟩
    exact h_empty ⟨x, h5⟩
  have hK_comp : IsCompact K := hK.2.1
  have hK_nonempty : K.Nonempty := by
    rcases hK.2.2 with ⟨x, hx⟩
    exact ⟨x, interior_subset hx⟩
  have h_exists : ∃ (x0 : E n), x0 ∈ K ∧ ∀ (x : E n), x ∈ K → ‖x‖ ≤ ‖x0‖ :=
    hK_comp.exists_isMaxOn hK_nonempty continuous_norm.continuousOn
  rcases h_exists with ⟨x0, hx0, hmax⟩
  let r := ‖x0‖
  have hr_lt_one : r < 1 := h1 x0 hx0
  have hr_pos : 0 < r := by
    by_cases h : r = 0
    · have hK0 : K ⊆ {0} := by
        intro x hx
        have h9 : ‖x‖ ≤ r := hmax x hx
        rw [h] at h9
        have h10 : ‖x‖ = 0 := by linarith [norm_nonneg x]
        have h11 : x = 0 := by simpa [norm_eq_zero] using h10
        exact Set.mem_singleton_iff.mpr h11
      have h_int : (interior K).Nonempty := hK.2.2
      rcases h_int with ⟨y, hy⟩
      have h_mono : interior K ⊆ interior ({0} : Set (E n)) := interior_mono hK0
      have h_y_in0 : y ∈ interior ({0} : Set (E n)) := h_mono hy
      have h_finrank_pos : 0 < Module.finrank ℝ (E n) := by
        have h : Module.finrank ℝ (E n) = n := by
          simpa [finrank_euclideanSpace] using rfl
        rw [h]; exact hn
      have h_nontriv : Nontrivial (E n) := by
        let i : Fin n := ⟨0, hn⟩
        let b : E n := (EuclideanSpace.basisFun (Fin n) ℝ) i
        have h_ind : LinearIndependent ℝ (EuclideanSpace.basisFun (Fin n) ℝ) :=
          (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.linearIndependent
        have hb : b ≠ 0 := h_ind.ne_zero i
        exact ⟨0, b, Ne.symm hb⟩
      have h_empty_int : interior ({0} : Set (E n)) = ∅ := by
        simpa [interior_singleton] using rfl
      have h_false : False := by
        rw [h_empty_int] at h_y_in0
        exact h_y_in0
      exact False.elim h_false
    · have h_r_nonneg : 0 ≤ r := by positivity
      exact lt_of_le_of_ne h_r_nonneg (Ne.symm h)
  have hK_sub_ball : K ⊆ Metric.closedBall (0 : E n) r := by
    intro x hx
    have h11 : ‖x‖ ≤ r := hmax x hx
    simpa [Metric.mem_closedBall] using h11
  let A_scaled : E n ≃ₗ[ℝ] E n := LinearEquiv.smulOfNeZero ℝ (E n) r hr_pos.ne'
  have hA_apply : ∀ (x : E n), A_scaled x = r • x := by
    intro x
    exact LinearEquiv.smulOfNeZero_apply ℝ (E n) r hr_pos.ne' x
  have h_ellipsoid : ellipsoid (0 : E n) A_scaled = Metric.closedBall (0 : E n) r := by
    ext z
    simp only [ellipsoid, Set.mem_vadd_set, Set.mem_image, zero_vadd, Metric.mem_closedBall]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_norm : ‖A_scaled x‖ = r * ‖x‖ := by
        rw [hA_apply x, norm_smul]
        have h_abs : ‖r‖ = r := abs_of_pos hr_pos
        rw [h_abs] <;> ring
      have h2 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hx
      have h3 : dist (A_scaled x) 0 ≤ r := by
        simpa [dist_zero_right, h_norm] using mul_le_mul_of_nonneg_left h2 (by linarith)
      exact h3
    · intro hz
      have h4 : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall] using hz
      let x : E n := r⁻¹ • z
      have h52 : 0 < r⁻¹ := by positivity
      have hx_norm : ‖x‖ ≤ 1 := by
        have h51 : ‖x‖ = ‖r⁻¹‖ * ‖z‖ := by
          simpa [x, norm_smul] using rfl
        have h_abs : ‖r⁻¹‖ = r⁻¹ := by
          have h1 : ‖r⁻¹‖ = |r⁻¹| := Real.norm_eq_abs r⁻¹
          rw [h1, abs_of_pos h52]
        rw [h51, h_abs]
        have h6 : r⁻¹ * ‖z‖ ≤ 1 := by
          calc r⁻¹ * ‖z‖ ≤ r⁻¹ * r := by gcongr
            _ = 1 := by field_simp [hr_pos.ne'] <;> ring
        exact h6
      refine ⟨x, by simpa [Metric.mem_closedBall] using hx_norm, ?_⟩
      have h7 : A_scaled x = z := by
        rw [hA_apply x]
        have h71 : r • (r⁻¹ • z) = z := by
          rw [smul_smul]
          have h72 : r * r⁻¹ = 1 := by field_simp [hr_pos.ne'] <;> ring
          rw [h72, one_smul]
        exact h71
      exact h7
  have h_det_scaled : LinearMap.det (A_scaled : E n →ₗ[ℝ] E n) = r ^ n := by
    have h_finrank : Module.finrank ℝ (E n) = n := by
      simpa [finrank_euclideanSpace] using rfl
    have h : (A_scaled : E n →ₗ[ℝ] E n) = r • (LinearMap.id : E n →ₗ[ℝ] E n) := by
      ext z; simpa [hA_apply] using rfl
    rw [h, LinearMap.det_smul, h_finrank]
    simp [LinearMap.det_id] <;> ring
  have h3 : r ^ n < 1 := by
    have h4 : 0 ≤ r := by positivity
    have h5 : r < 1 := hr_lt_one
    have h6 : ∀ (k : ℕ), 0 < k → r ^ k < 1 := by
      intro k hk
      induction' hk with k hk ih
      · simpa using h5
      · rw [pow_succ]
        have h7 : r ^ k > 0 := by positivity
        nlinarith
    exact h6 n hn
  have h_det_lt : |LinearMap.det (A_scaled : E n →ₗ[ℝ] E n)| <
      |LinearMap.det ((1 : E n ≃ₗ[ℝ] E n) : E n →ₗ[ℝ] E n)| := by
    rw [h_det_scaled]
    have h4 : |(r ^ n)| = r ^ n := abs_of_nonneg (by positivity)
    rw [h4]
    simpa using h3
  have h_vol_lt : volume (ellipsoid (0 : E n) A_scaled) <
      volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) := by
    have h_iff := volume_ellipsoid_le_iff (0 : E n) (1 : E n ≃ₗ[ℝ] E n) (0 : E n) A_scaled
    have h_not_le : ¬ volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤
        volume (ellipsoid (0 : E n) A_scaled) := by
      rw [h_iff]
      exact not_le.mpr h_det_lt
    exact lt_of_not_ge h_not_le
  have h_contra := h_min (0 : E n) A_scaled (by rw [h_ellipsoid] <;> exact hK_sub_ball)
  exact not_le.mpr h_vol_lt h_contra

/-- Helper: from separation, extract C, b, α violating Fritz John conditions. -/
lemma fritz_john_separation_violation
    (hn : 0 < n) (hK : IsConvexBody K)
    (h_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (h_min : ∀ (c : E n) (A : E n ≃ₗ[ℝ] E n),
        K ⊆ ellipsoid c A →
        volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c A))
    (h : ((0 : E n), (1 / (n : ℝ)) • (1 : Mat n)) ∉ convexHull ℝ (pairContactSet K)) :
    ∃ (C : Mat n) (b : E n) (α : ℝ),
      C.IsSymm ∧
      ((n : ℝ) * α - C.trace < 0) ∧
      (∀ u ∈ K, ‖u‖ = 1 → quadForm C u + 2 * inner ℝ b u < α) := by
  let C_hull := convexHull ℝ (pairContactSet K)
  have hC_compact : IsCompact C_hull :=
    convexHull_compact_of_compact (pairContactSet_compact hK)
  have hC_conv : Convex ℝ C_hull := convex_convexHull ℝ (pairContactSet K)
  have hcn : (contactSet K).Nonempty := contactSet_nonempty hn hK h_sub h_min
  have hC_nonempty : C_hull.Nonempty := by
    rcases hcn with ⟨u, hu⟩
    have h1 : (u, outerProduct u) ∈ pairContactSet K := ⟨u, hu, rfl⟩
    exact ⟨(u, outerProduct u), subset_convexHull ℝ (pairContactSet K) h1⟩
  rcases strict_separation_generic hC_conv hC_compact hC_nonempty h with
    ⟨f, _hf_ne_zero, hf_lt⟩
  let f1 : (E n) →L[ℝ] ℝ :=
    f.comp (ContinuousLinearMap.inl ℝ (E n) (Mat n))
  let f2 : (Mat n) →L[ℝ] ℝ :=
    f.comp (ContinuousLinearMap.inr ℝ (E n) (Mat n))
  have h_add : ∀ (x : E n) (M : Mat n), f (x, M) = f1 x + f2 M := by
    intro x M
    have h : (x, M) = (x, (0 : Mat n)) + ((0 : E n), M) := by ext <;> simp
    rw [h, f.map_add] <;> rfl
  have h_riesz : ∃ (b0 : E n), ∀ x, f1 x = inner ℝ b0 x := by
    let toDual : (E n) ≃ₗᵢ⋆[ℝ] (StrongDual ℝ (E n)) :=
      InnerProductSpace.toDual ℝ (E n)
    let b0 : E n := toDual.symm f1
    refine ⟨b0, fun x => ?_⟩
    have h2 : toDual b0 = f1 := by simp [toDual, b0]
    have h3 : (toDual b0) x = inner ℝ b0 x := by rfl
    rw [h2] at h3; exact h3
  rcases h_riesz with ⟨b0, hb0⟩
  rcases matrix_dual_symmetric f2 with ⟨Cmat, hC_symm, hC_rep⟩
  let b : E n := (2 : ℝ)⁻¹ • b0
  have hb : ∀ x, f1 x = 2 * inner ℝ b x := by
    intro x
    have h : inner ℝ b0 x = 2 * inner ℝ b x := by
      simp [b, inner_smul_left] <;> ring
    rw [hb0 x, h]
  have h_ineq : ∀ u ∈ contactSet K,
      quadForm Cmat u + 2 * inner ℝ b u < Cmat.trace / (n : ℝ) := by
    intro u hu
    have h1 : (u, outerProduct u) ∈ C_hull :=
      subset_convexHull ℝ (pairContactSet K) ⟨u, hu, rfl⟩
    have h2 : f (u, outerProduct u) <
        f ((0 : E n), (1 / (n : ℝ)) • (1 : Mat n)) := hf_lt (u, outerProduct u) h1
    have h3 : f (u, outerProduct u) = quadForm Cmat u + 2 * inner ℝ b u := by
      rw [h_add u (outerProduct u), hb u]
      have h4 : f2 (outerProduct u) = quadForm Cmat u := by
        rw [hC_rep (outerProduct u) (outerProduct_symm u)]
        have h_eq1 : ∑ i : Fin n, ∑ j : Fin n, Cmat i j * (outerProduct u) i j =
            ∑ i : Fin n, ∑ j : Fin n, u i * Cmat i j * u j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          have h_op : (outerProduct u) i j = u i * u j := by
            simp [outerProduct, Matrix.vecMulVec]
          rw [h_op] <;> ring
        rw [h_eq1]
        have h8 : quadForm Cmat u = ∑ i : Fin n, ∑ j : Fin n, u i * Cmat i j * u j := by
          simp [quadForm] <;> rfl
        exact h8.symm
      rw [h4] <;> ring
    have h4 : f ((0 : E n), (1 / (n : ℝ)) • (1 : Mat n)) =
        Cmat.trace / (n : ℝ) := by
      rw [h_add (0 : E n) ((1 / (n : ℝ)) • (1 : Mat n))]
      have h5 : f1 (0 : E n) = 0 := by rw [hb 0] <;> simp
      rw [h5]
      have h6 : f2 ((1 / (n : ℝ)) • (1 : Mat n)) = Cmat.trace / (n : ℝ) := by
        have h_symm : ((1 / (n : ℝ)) • (1 : Mat n)).IsSymm := by
          have h_one_symm : (1 : Mat n).IsSymm := Matrix.isSymm_one
          exact h_one_symm.smul (1 / (n : ℝ))
        rw [hC_rep ((1 / (n : ℝ)) • (1 : Mat n)) h_symm]
        have h_frob : ∑ i : Fin n, ∑ j : Fin n, Cmat i j * ((1 / (n : ℝ)) • (1 : Mat n)) i j =
            (1 / (n : ℝ)) * Cmat.trace := frobenius_identity Cmat ((1 / (n : ℝ)))
        rw [h_frob]
        <;> ring
      rw [h6] <;> ring
    rw [h3, h4] at h2
    exact h2
  have h_contact_compact : IsCompact (contactSet K) := by
    have h1 : IsCompact K := hK.2.1
    have h2 : IsClosed {x : E n | ‖x‖ = 1} := isClosed_eq continuous_norm continuous_const
    exact h1.inter_right h2
  let g : E n → ℝ := fun u => quadForm Cmat u + 2 * inner ℝ b u
  have hg_cont : Continuous g := by
    have h1 : Continuous (fun u : E n => quadForm Cmat u) := quadForm_continuous Cmat
    have h2 : Continuous (fun u : E n => inner ℝ b u) :=
      continuous_const.inner continuous_id
    exact h1.add (continuous_const.mul h2)
  have h_exists2 : ∃ (u0 : E n), u0 ∈ contactSet K ∧ ∀ (u : E n), u ∈ contactSet K → g u ≤ g u0 :=
    h_contact_compact.exists_isMaxOn hcn hg_cont.continuousOn
  rcases h_exists2 with ⟨u0, hu0, h_max⟩
  let β := g u0
  have hβ_lt : β < Cmat.trace / (n : ℝ) := h_ineq u0 hu0
  let α := (β + Cmat.trace / (n : ℝ)) / 2
  have hα1 : ∀ u ∈ contactSet K, g u < α := by
    intro u hu
    have h5 : g u ≤ β := h_max u hu
    have h6 : β < α := by
      dsimp only [α]
      have h7 : β < Cmat.trace / (n : ℝ) := hβ_lt
      have hn' : (n : ℝ) > 0 := by exact_mod_cast hn
      linarith
    have h7 : g u < α := by linarith
    exact h7
  have hα2 : (n : ℝ) * α - Cmat.trace < 0 := by
    dsimp only [α]
    have hn' : (n : ℝ) > 0 := by exact_mod_cast hn
    have h_mult : (n : ℝ) * β < Cmat.trace := by
      have h9 : β < Cmat.trace / (n : ℝ) := hβ_lt
      calc (n : ℝ) * β < (n : ℝ) * (Cmat.trace / (n : ℝ)) := by gcongr
        _ = Cmat.trace := by field_simp [hn'] <;> ring
    have h_eq : (n : ℝ) * ((β + Cmat.trace / (n : ℝ)) / 2) - Cmat.trace =
        ((n : ℝ) * β - Cmat.trace) / 2 := by
      field_simp [hn'.ne'] <;> ring
    rw [h_eq]
    have h_neg : (n : ℝ) * β - Cmat.trace < 0 := by linarith
    exact div_neg_of_neg_of_pos h_neg (by norm_num)
  have hS_strict : ∀ u ∈ K, ‖u‖ = 1 →
      quadForm Cmat u + 2 * inner ℝ b u < α := by
    intro u hu hnorm
    have h6 : u ∈ contactSet K := ⟨hu, hnorm⟩
    exact hα1 u h6
  exact ⟨Cmat, b, α, hC_symm, hα2, hS_strict⟩

/-- General Fritz John pair identity:
`(0, I/n) ∈ conv{(u, u⊗u) : u ∈ contactSet K}`. -/
theorem general_fritz_john_pair_identity
    (hn : 0 < n)
    (hK : IsConvexBody K)
    (h_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (h_min : ∀ (c : E n) (A : E n ≃ₗ[ℝ] E n),
        K ⊆ ellipsoid c A →
        volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c A)) :
    ((0 : E n), (1 / (n : ℝ)) • (1 : Mat n)) ∈
      convexHull ℝ (pairContactSet K) := by
  by_contra h
  rcases fritz_john_separation_violation hn hK h_sub h_min h with
    ⟨C, b, α, hC_symm, hα2, hS_strict⟩
  rcases augmented_perturbation_contradiction' hK h_sub C hC_symm b α hα2 hS_strict
    with ⟨c, A, hK_sub, h_vol_lt⟩
  have h_contra := h_min c A hK_sub
  have h_not : ¬ volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤
      volume (ellipsoid c A) := not_le.mpr h_vol_lt
  exact h_not h_contra

/-- Weighted sum identity: given `∑ w y • outerProduct y = (1/n) • I`,
then `∑ (n * w y * inner y x) • y = x`. -/
private lemma pair_weighted_identity
    {t : Finset (E n)} {w : E n → ℝ}
    (hw_sum_smul : ∑ y ∈ t, w y • outerProduct y = (1 / (n : ℝ)) • (1 : Mat n))
    (hn : 0 < n) (x : E n) :
    ∑ y ∈ t, ((n : ℝ) * w y * inner ℝ y x) • y = x := by
  let s_t : Type _ := {y : E n // y ∈ t}
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let mulVecE (M : Mat n) (x : E n) : E n := WithLp.toLp 2 (M.mulVec x.ofLp)
  have h_step1 : ∑ y ∈ t, ((n : ℝ) * w y * inner ℝ y x) • y =
      (n : ℝ) • ∑ y ∈ t, (w y * inner ℝ y x) • y := by
    have h2 : ∀ y ∈ t, ((n : ℝ) * w y * inner ℝ y x) • y =
        (n : ℝ) • ((w y * inner ℝ y x) • y) := by
      intro y _
      have h_assoc : (n : ℝ) * w y * inner ℝ y x =
          (n : ℝ) * (w y * inner ℝ y x) := by ring
      rw [h_assoc, smul_smul]
    have h3 : ∑ y ∈ t, ((n : ℝ) * w y * inner ℝ y x) • y =
        ∑ y ∈ t, (n : ℝ) • ((w y * inner ℝ y x) • y) := by
      apply Finset.sum_congr rfl; intro y _; exact h2 y ‹_›
    have h4 : ∑ y ∈ t, (n : ℝ) • ((w y * inner ℝ y x) • y) =
        (n : ℝ) • ∑ y ∈ t, ((w y * inner ℝ y x) • y) := by
      rw [Finset.smul_sum]
    rw [h3, h4]
  rw [h_step1]
  have h_step2 : ∑ y ∈ t, (w y * inner ℝ y x) • y =
      ∑ y ∈ t, w y • mulVecE (outerProduct y) x := by
    apply Finset.sum_congr rfl
    intro y _
    have h4 : (w y * inner ℝ y x) • y =
        w y • ((inner ℝ y x) • y) := by
      rw [smul_smul] <;> ring
    rw [h4]
    have h5 : ((inner ℝ y x) • y) = mulVecE (outerProduct y) x := by
      apply (WithLp.equiv 2 (Fin n → ℝ)).injective
      have h_goal : ((inner ℝ y x) • y).ofLp =
          (outerProduct y).mulVec x.ofLp := by
        ext i
        have h_inner : inner ℝ y x = ∑ j : Fin n, y.ofLp j * x.ofLp j := by
          have h : inner ℝ y x = ∑ j : Fin n, x.ofLp j * y.ofLp j := by
            simp [inner, PiLp.inner_apply] <;> rfl
          rw [h]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [h_inner]
        have h_lhs : ((∑ j : Fin n, y.ofLp j * x.ofLp j) • y).ofLp i =
            (∑ j : Fin n, y.ofLp j * x.ofLp j) * y.ofLp i := by
          simp [smul_eq_mul] <;> rfl
        rw [h_lhs]
        have h_rhs : (outerProduct y).mulVec x.ofLp i =
            ∑ j : Fin n, y.ofLp i * y.ofLp j * x.ofLp j := by
          simp [outerProduct, Matrix.vecMulVec, Matrix.mulVec] <;> rfl
        rw [h_rhs]
        have h_sum : ∑ j : Fin n, y.ofLp i * y.ofLp j * x.ofLp j =
            y.ofLp i * ∑ j : Fin n, y.ofLp j * x.ofLp j := by
          have h_assoc : ∑ j : Fin n, y.ofLp i * y.ofLp j * x.ofLp j =
              ∑ j : Fin n, y.ofLp i * (y.ofLp j * x.ofLp j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          rw [h_assoc, Finset.mul_sum]
        rw [h_sum] <;> ring
      simpa [mulVecE, WithLp.equiv] using h_goal
    rw [h5]
  rw [h_step2]
  have h_step3 : ∑ y ∈ t, w y • mulVecE (outerProduct y) x =
      mulVecE (∑ y ∈ t, w y • outerProduct y) x := by
    apply (WithLp.equiv 2 (Fin n → ℝ)).injective
    have h_eq1 : (WithLp.equiv 2 (Fin n → ℝ)) (∑ y ∈ t, w y • mulVecE (outerProduct y) x) =
        ∑ y ∈ t, w y • (outerProduct y).mulVec x.ofLp := by
      simp [mulVecE, WithLp.equiv, map_sum, map_smul] <;> rfl
    rw [h_eq1]
    have h_eq2 : ∑ y ∈ t, w y • (outerProduct y).mulVec x.ofLp =
        ∑ y ∈ t, (w y • outerProduct y).mulVec x.ofLp := by
      apply Finset.sum_congr rfl
      intro y _
      exact Eq.symm (Matrix.smul_mulVec (w y) (outerProduct y) x.ofLp)
    rw [h_eq2]
    have h_eq3 : ∑ y ∈ t, (w y • outerProduct y).mulVec x.ofLp =
        (∑ y ∈ t, w y • outerProduct y).mulVec x.ofLp := by
      rw [← Matrix.sum_mulVec]
    rw [h_eq3] <;> simp [mulVecE, WithLp.equiv] <;> rfl
  rw [h_step3]
  rw [hw_sum_smul]
  have h_step5 : mulVecE ((1 / (n : ℝ)) • (1 : Mat n)) x = (1 / (n : ℝ)) • x := by
    ext i
    have h_dot : (fun j : Fin n => if i = j then (1 / (n : ℝ)) else 0) ⬝ᵥ x.ofLp =
        (1 / (n : ℝ)) * x.ofLp i := by
      have h1 : (fun j : Fin n => if i = j then (1 / (n : ℝ)) else 0) ⬝ᵥ x.ofLp =
          ∑ j : Fin n, (if i = j then (1 / (n : ℝ)) else 0) * x.ofLp j := by rfl
      rw [h1]
      have h2 : ∀ j : Fin n, (if i = j then (1 / (n : ℝ)) else 0) * x.ofLp j =
          if i = j then (1 / (n : ℝ)) * x.ofLp j else 0 := by
        intro j; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun j _ => h2 j)]
      have h3 : ∑ j : Fin n, (if i = j then (1 / (n : ℝ)) * x.ofLp j else 0) =
          (1 / (n : ℝ)) * x.ofLp i := by
        have h4 : ∀ (j : Fin n), j ≠ i → (if i = j then (1 / (n : ℝ)) * x.ofLp j else 0) = 0 := by
          intro j hne
          have hne' : i ≠ j := Ne.symm hne
          rw [if_neg hne'] <;> rfl
        have h5 := Finset.sum_eq_single (s := Finset.univ) (a := i)
          (f := fun j : Fin n => (if i = j then (1 / (n : ℝ)) * x.ofLp j else 0)) (fun j _ => h4 j)
        rw [h5] <;> simp
      rw [h3] <;> ring
    simpa [mulVecE, Matrix.mulVec, Matrix.one_apply, smul_eq_mul] using h_dot
  rw [h_step5]
  have h_step6 : (n : ℝ) • ((1 / (n : ℝ)) • x) = x := by
    rw [smul_smul]
    have h9 : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp [hn'] <;> ring
    rw [h9, one_smul]
  exact h_step6

/-- Extract finite contact points and weights from the pair convex hull membership. -/
lemma general_fritz_john_extract_pair
    (hn : 0 < n)
    (h_main : ((0 : E n), (1 / (n : ℝ)) • (1 : Mat n)) ∈
      convexHull ℝ (Set.image (fun u : E n => (u, outerProduct u)) (contactSet K))) :
    ∃ (m : ℕ) (u : Fin m → E n) (c : Fin m → ℝ),
      (∀ i, u i ∈ K ∧ ‖u i‖ = 1) ∧
      (∀ i, 0 ≤ c i) ∧
      (∑ i, c i = (n : ℝ)) ∧
      (∑ i, c i • u i = 0) ∧
      (∀ x : E n, ∑ i, (c i * inner ℝ x (u i)) • u i = x) := by
  have h_decomp := ConvexHullUtils.convexHull_graph_decomp h_main
  rcases h_decomp with ⟨t, w, htS, hw₀, hw₁, h_sum1, h_sum2⟩
  let s_t : Type _ := {y : E n // y ∈ t}
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let m := t.card
  let e : s_t ≃ Fin m := Finset.equivFin t
  let u' : Fin m → E n := fun i => (e.symm i).val
  let c : Fin m → ℝ := fun i => (n : ℝ) * w (e.symm i).val

  refine ⟨m, u', c, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h_y_in_contact : (e.symm i).val ∈ contactSet K := htS (e.symm i).property
    exact h_y_in_contact
  · intro i
    have h1 : 0 ≤ w (e.symm i).val := hw₀ (e.symm i).val (e.symm i).property
    positivity
  · have h_sum_c : ∑ i : Fin m, c i = (n : ℝ) * ∑ i : Fin m, w (e.symm i).val := by
      rw [Finset.mul_sum] <;> rfl
    rw [h_sum_c]
    have h2 : ∑ i : Fin m, w (e.symm i).val = ∑ y ∈ t, w y := by
      have h21 : ∑ i : Fin m, w (e.symm i).val = ∑ hy : s_t, w hy.val := by
        exact Fintype.sum_equiv e.symm (fun i => w (e.symm i).val) (fun hy => w hy.val) (fun _ => rfl)
      rw [h21]
      exact Finset.sum_attach t w
    rw [h2, hw₁] <;> ring
  · have h3 : ∑ i : Fin m, c i • u' i =
        (n : ℝ) • ∑ i : Fin m, w (e.symm i).val • (e.symm i).val := by
      have h4 : ∀ i : Fin m, c i • u' i =
          (n : ℝ) • (w (e.symm i).val • (e.symm i).val) := by
        intro i
        dsimp only [c, u']
        rw [smul_smul] <;> ring
      rw [Finset.sum_congr rfl (fun i _ => h4 i)]
      rw [← Finset.smul_sum]
    rw [h3]
    have h5 : ∑ i : Fin m, w (e.symm i).val • (e.symm i).val = ∑ y ∈ t, w y • y := by
      have h51 : ∑ i : Fin m, w (e.symm i).val • (e.symm i).val =
          ∑ hy : s_t, w hy.val • hy.val := by
        exact Fintype.sum_equiv e.symm
          (fun i => w (e.symm i).val • (e.symm i).val)
          (fun hy => w hy.val • hy.val)
          (fun _ => rfl)
      rw [h51]
      exact Finset.sum_attach t (fun y => w y • y)
    rw [h5, h_sum1] <;> simp
  · intro x
    have h6 : ∑ i : Fin m, (c i * inner ℝ x (u' i)) • u' i =
        ∑ y ∈ t, ((n : ℝ) * w y * inner ℝ x y) • y := by
      have h7 : ∑ i : Fin m, (c i * inner ℝ x (u' i)) • u' i =
          ∑ hy : s_t, ((n : ℝ) * w hy.val * inner ℝ x hy.val) • hy.val := by
        exact Fintype.sum_equiv e.symm
          (fun i => (c i * inner ℝ x (u' i)) • u' i)
          (fun hy => ((n : ℝ) * w hy.val * inner ℝ x hy.val) • hy.val)
          (fun i => by dsimp only [c, u'] <;> rfl)
      rw [h7]
      have h8 : ∑ hy : s_t, ((n : ℝ) * w hy.val * inner ℝ x hy.val) • hy.val =
          ∑ y ∈ t, ((n : ℝ) * w y * inner ℝ x y) • y := by
        exact Finset.sum_attach t (fun y => ((n : ℝ) * w y * inner ℝ x y) • y)
      exact h8
    rw [h6]
    have h_comm : ∑ y ∈ t, ((n : ℝ) * w y * inner ℝ x y) • y =
        ∑ y ∈ t, ((n : ℝ) * w y * inner ℝ y x) • y := by
      apply Finset.sum_congr rfl
      intro y _
      have h9 : inner ℝ x y = inner ℝ y x := (real_inner_comm x y).symm
      rw [h9]
    rw [h_comm]
    exact pair_weighted_identity h_sum2 hn x

/-- **General augmented Fritz John conditions**: from the minimal enclosing ellipsoid
(normalized to unit ball), extract finite contact points `u i` and weights `c i` satisfying:
- contact: `u i ∈ K` and `‖u i‖ = 1`
- nonnegativity: `0 ≤ c i`
- sum: `∑ c i = n`
- centering: `∑ c i • u i = 0`
- tensor identity: `∑ (c i * inner x (u i)) • u i = x` for all `x` -/
theorem general_fritz_john_augmented (hn : 0 < n) {K : Set (E n)}
    (hK : IsConvexBody K)
    (h_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (h_min : ∀ (c : E n) (A : E n ≃ₗ[ℝ] E n),
        K ⊆ ellipsoid c A →
        volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c A)) :
    ∃ (m : ℕ) (u : Fin m → E n) (c : Fin m → ℝ),
      (∀ i, u i ∈ K ∧ ‖u i‖ = 1) ∧
      (∀ i, 0 ≤ c i) ∧
      (∑ i, c i = (n : ℝ)) ∧
      (∑ i, c i • u i = 0) ∧
      (∀ x, ∑ i, (c i * inner ℝ x (u i)) • u i = x) := by
  have h_pair : ((0 : E n), (1 / (n : ℝ)) • (1 : Mat n)) ∈
      convexHull ℝ (pairContactSet K) :=
    general_fritz_john_pair_identity hn hK h_sub h_min
  have h_main : ((0 : E n), (1 / (n : ℝ)) • (1 : Mat n)) ∈
      convexHull ℝ (Set.image (fun u : E n => (u, outerProduct u)) (contactSet K)) := by
    simpa [pairContactSet] using h_pair
  exact general_fritz_john_extract_pair hn h_main

/-- Variant of `general_fritz_john_augmented` with `inner ℝ (u i) x` instead of
`inner ℝ x (u i)`. Used by Uniqueness.lean. -/
theorem general_fritz_john_conditions (hn : 0 < n) {K : Set (E n)}
    (hK : IsConvexBody K)
    (h_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (h_min : ∀ (c : E n) (A : E n ≃ₗ[ℝ] E n),
        K ⊆ ellipsoid c A →
        volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c A)) :
    ∃ (m : ℕ) (u : Fin m → E n) (c : Fin m → ℝ),
      (∀ i, u i ∈ K ∧ ‖u i‖ = 1) ∧
      (∀ i, 0 ≤ c i) ∧
      (∑ i, c i = (n : ℝ)) ∧
      (∑ i, c i • u i = 0) ∧
      (∀ x, ∑ i, (c i * inner ℝ (u i) x) • u i = x) := by
  rcases general_fritz_john_augmented hn hK h_sub h_min with
    ⟨m, u, c, h_contact, h_nonneg, h_sum, h_center, h_tensor⟩
  refine ⟨m, u, c, h_contact, h_nonneg, h_sum, h_center, fun x => ?_⟩
  have h_comm : ∑ i : Fin m, (c i * inner ℝ (u i) x) • u i =
      ∑ i : Fin m, (c i * inner ℝ x (u i)) • u i := by
    apply Finset.sum_congr rfl
    intro i _
    have h9 : inner ℝ (u i) x = inner ℝ x (u i) := (real_inner_comm (u i) x).symm
    rw [h9]
  rw [h_comm]
  exact h_tensor x

end JohnEllipsoid
