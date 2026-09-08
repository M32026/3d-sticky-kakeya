import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TightDistinctness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnisotropicPacking
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import Mathlib.Tactic

set_option linter.constructorNameAsVariable false

/-!
# Generalized cell-pack for conflict degree

Parametric version of `shifted_copy_cell_pack` with configurable midpoint
transverse and longitudinal bounds.

Given direction transverse ≤ 10ρ₀, midpoint transverse ≤ C·A·ρ₀,
midpoint longitudinal ≤ D·A, and z-component sign, pack 5D parameters
with cell sizes ρ₀/200 (direction & midpoint transverse) and 1/6400
(midpoint longitudinal).

Bound: 2 · 4001² · (2·⌈200·C·A⌉+1)² · (2·⌈6400·D·A⌉+1)
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined Metric Set InnerProductSpace
open Kakeya.Streamlined.GeometricLemmas

/-- Reflection function: negate z-coordinate. -/
def shiftedZReflectFun (p : Point3) : Point3 :=
  p - (2 * (p 2)) • (EuclideanSpace.single 2 1)

@[simp] lemma shiftedZReflectFun_0 (p : Point3) : (shiftedZReflectFun p) 0 = p 0 := by
  simp [shiftedZReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring
@[simp] lemma shiftedZReflectFun_1 (p : Point3) : (shiftedZReflectFun p) 1 = p 1 := by
  simp [shiftedZReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring
@[simp] lemma shiftedZReflectFun_2 (p : Point3) : (shiftedZReflectFun p) 2 = - (p 2) := by
  simp [shiftedZReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring

/-- Reflection in the z-axis as a linear isometry. -/
def shiftedZReflect : Point3 ≃ₗᵢ[ℝ] Point3 :=
  { toFun := shiftedZReflectFun
    invFun := shiftedZReflectFun
    left_inv := by intro p; ext i; fin_cases i <;> simp <;> ring
    right_inv := by intro p; ext i; fin_cases i <;> simp <;> ring
    map_add' := by intro p q; ext i; fin_cases i <;> simp [Pi.add_apply] <;> ring
    map_smul' := by intro c p; ext i; fin_cases i <;> simp [Pi.smul_apply] <;> ring
    norm_map' := by
      intro p
      have h1 : ‖shiftedZReflectFun p‖ ^ 2 = ∑ i : Fin 3, (shiftedZReflectFun p i)^2 :=
        EuclideanSpace.real_norm_sq_eq _
      have h2 : ‖p‖ ^ 2 = ∑ i : Fin 3, (p i)^2 := EuclideanSpace.real_norm_sq_eq _
      have h3 : ∑ i : Fin 3, (shiftedZReflectFun p i)^2 = ∑ i : Fin 3, (p i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        fin_cases i <;> simp <;> ring
      have h4 : ‖shiftedZReflectFun p‖ ^ 2 = ‖p‖ ^ 2 := by rw [h1, h2, h3]
      have h5 : 0 ≤ ‖shiftedZReflectFun p‖ := by positivity
      have h6 : 0 ≤ ‖p‖ := by positivity
      have h7 : ‖shiftedZReflectFun p‖ = ‖p‖ := by
        nlinarith [sq_nonneg (‖shiftedZReflectFun p‖ - ‖p‖),
          sq_nonneg (‖shiftedZReflectFun p‖ + ‖p‖)]
      exact h7 }

/-- Generalized cell-pack: parametric midpoint transverse C and longitudinal D. -/
lemma generalized_cell_pack
    {ρ₀ A : ℝ} (hρ₀ : 0 < ρ₀) (hA : 1 ≤ A)
    (hρ₀_small : ρ₀ ≤ 1 / (200 * A))
    (C_midtrans C_midlong : ℝ)
    (hC_pos : 0 < C_midtrans) (hD_pos : 0 < C_midlong)
    {n : ℕ} {T : Fin n → Kakeya.DeltaTube ρ₀}
    (indices : Finset (Fin n))
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (m u : Fin n → Point3)
    (hm : ∀ j, m j = frame.symm (wz2PaperTubeMidpoint (T j)))
    (hu : ∀ j, u j = frame.symm.linearIsometryEquiv (T j).direction)
    (h_dir : ∀ j ∈ indices, |u j 0| ≤ 10 * ρ₀ ∧ |u j 1| ≤ 10 * ρ₀)
    (h_z : ∀ j ∈ indices, u j 2 ≥ 1 / 2 ∨ u j 2 ≤ -1 / 2)
    (h_m_trans : ∀ j ∈ indices, |(m j) 0| ≤ C_midtrans * A * ρ₀ ∧ |(m j) 1| ≤ C_midtrans * A * ρ₀)
    (h_m_long : ∀ j ∈ indices, |(m j) 2| ≤ C_midlong * A)
    (h_distinct : ∀ i j, i ∈ indices → j ∈ indices → i ≠ j → (T i).EssentiallyDistinct (T j)) :
    indices.card ≤ 2 * 4001^2 *
      (2 * Nat.ceil (200 * C_midtrans * A) + 1)^2 *
      (2 * Nat.ceil (6400 * C_midlong * A) + 1) := by
  have hρ₀1 : ρ₀ ≤ 1 / 100 := by
    have h : 1 / (200 * A) ≤ 1 / 100 := by
      have h_pos : 0 < 200 * A := by positivity
      have h' : 200 * A ≥ 200 := by nlinarith
      have h'' : 1 / (200 * A) ≤ 1 / 200 := by
        apply one_div_le_one_div_of_le <;> linarith
      linarith
    linarith [hρ₀_small]
  have h_capsule_lower : CapsuleLowerBound := capsule_lower_bound_instantiation
  have h_capsule_upper : CapsuleUpperBound := capsule_upper_bound_instantiation

  let posIndices := indices.filter (fun j => u j 2 ≥ 1 / 2)
  let negIndices := indices.filter (fun j => u j 2 ≤ -1 / 2)

  have h_cover : indices ⊆ posIndices ∪ negIndices := by
    intro j hj
    have hz := h_z j hj
    by_cases hpos : u j 2 ≥ 1 / 2
    · have h_in : j ∈ posIndices := by
        rw [Finset.mem_filter] <;> exact ⟨hj, hpos⟩
      exact Finset.mem_union_left _ h_in
    · have hneg : u j 2 ≤ -1 / 2 := by tauto
      have h_in : j ∈ negIndices := by
        rw [Finset.mem_filter] <;> exact ⟨hj, hneg⟩
      exact Finset.mem_union_right _ h_in

  let s : Fin 5 → ℝ := ![ρ₀ / 200, ρ₀ / 200, ρ₀ / 200, ρ₀ / 200, 1 / 6400]
  let R : Fin 5 → ℝ := ![10 * ρ₀, 10 * ρ₀, C_midtrans * A * ρ₀, C_midtrans * A * ρ₀, C_midlong * A]

  have hs : ∀ i, 0 < s i := by
    intro i; fin_cases i <;> simp [s] <;> positivity
  have hR : ∀ i, 0 ≤ R i := by
    intro i; fin_cases i <;> simp [R] <;> positivity

  let params : Fin n → (Fin 5 → ℝ) := fun j =>
    ![u j 0, u j 1, m j 0, m j 1, m j 2]

  have hball : ∀ (idx : Finset (Fin n)), (∀ j ∈ idx, j ∈ indices) →
      ∀ j ∈ idx, ∀ i : Fin 5, |(params j) i| ≤ R i := by
    intro idx hsub j hj i
    have hj' : j ∈ indices := hsub j hj
    have hdir := h_dir j hj'
    have hmt := h_m_trans j hj'
    have hml := h_m_long j hj'
    fin_cases i
    · simpa [params, R] using hdir.1
    · simpa [params, R] using hdir.2
    · simpa [params, R] using hmt.1
    · simpa [params, R] using hmt.2
    · simpa [params, R] using hml

  have hball_pos_idx := hball posIndices (fun j hj => (Finset.mem_filter.mp hj).1)

  have h_sep : ∀ (idx : Finset (Fin n)), (∀ j ∈ idx, u j 2 ≥ 1 / 2) →
      (∀ j ∈ idx, j ∈ indices) →
      ∀ (v : Fin 5 → ℝ), v ∈ Finset.image params idx →
      ∀ (w : Fin 5 → ℝ), w ∈ Finset.image params idx →
        v ≠ w → ∃ i : Fin 5, |v i - w i| ≥ s i := by
    intro idx hzpos hsub v hv w hw hne
    rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨k, hk, h_eq⟩
    have h_jk : j ≠ k := by
      intro h
      have h_contra : params j = w := by
        calc params j = params k := by rw [h]
          _ = w := h_eq
      exact hne h_contra
    have h_dist : (T j).EssentiallyDistinct (T k) :=
      h_distinct j k (hsub j hj) (hsub k hk) h_jk
    by_contra h
    push_neg at h
    have h' : ∀ i : Fin 5, |(params j) i - (params k) i| ≤ s i := by
      intro i
      have h_i : |(params j) i - w i| < s i := h i
      rw [←h_eq] at h_i
      exact h_i.le
    have h_close : ¬ (T j).EssentiallyDistinct (T k) :=
      close_params_not_distinct_coarse hρ₀ hρ₀1 frame
        (m j) (m k) (u j) (u k)
        (hm j) (hm k) (hu j) (hu k)
        (hzpos j hj) (hzpos k hk)
        (h_dir k (hsub k hk)).1
        (h_dir k (hsub k hk)).2
        (by simpa [params, s] using h' 2)
        (by simpa [params, s] using h' 3)
        (by simpa [params, s] using h' 4)
        (by simpa [params, s] using h' 0)
        (by simpa [params, s] using h' 1)
        h_capsule_lower h_capsule_upper
    exact h_close h_dist

  have h_sep_pos := h_sep posIndices
    (fun j hj => (Finset.mem_filter.mp hj).2)
    (fun j hj => (Finset.mem_filter.mp hj).1)

  -- Negative case: use z-reflected frame and parameters
  let u' j := shiftedZReflect (u j)
  let m' j := shiftedZReflect (m j)
  let frame' : Point3 ≃ᵃⁱ[ℝ] Point3 :=
    shiftedZReflect.toAffineIsometryEquiv.trans frame

  have h_frame'_symm : ∀ x, frame'.symm x = shiftedZReflect (frame.symm x) := by
    intro x; rfl

  have h_frame'_symm_linear : ∀ (x : Point3),
      frame'.symm.linearIsometryEquiv x = shiftedZReflect (frame.symm.linearIsometryEquiv x) := by
    intro x; rfl

  have hm' : ∀ j, m' j = frame'.symm (wz2PaperTubeMidpoint (T j)) := by
    intro j
    have h1 : frame'.symm (wz2PaperTubeMidpoint (T j)) = shiftedZReflect (frame.symm (wz2PaperTubeMidpoint (T j))) :=
      h_frame'_symm _
    rw [h1, ←hm j] <;> rfl

  have hu' : ∀ j, u' j = frame'.symm.linearIsometryEquiv (T j).direction := by
    intro j
    have h1 : frame'.symm.linearIsometryEquiv (T j).direction =
        shiftedZReflect (frame.symm.linearIsometryEquiv (T j).direction) :=
      h_frame'_symm_linear (T j).direction
    rw [h1, ←hu j] <;> rfl

  let params' : Fin n → (Fin 5 → ℝ) := fun j =>
    ![u' j 0, u' j 1, m' j 0, m' j 1, m' j 2]

  have h_z'_pos : ∀ j ∈ negIndices, u' j 2 ≥ 1 / 2 := by
    intro j hj
    have hneg : u j 2 ≤ -1 / 2 := (Finset.mem_filter.mp hj).2
    have h1 : u' j 2 = -(u j 2) := by
      dsimp only [u']
      exact shiftedZReflectFun_2 (u j)
    rw [h1]; linarith

  have h_sub_neg : ∀ j ∈ negIndices, j ∈ indices :=
    fun j hj => (Finset.mem_filter.mp hj).1

  have h_dir' : ∀ j ∈ negIndices, |u' j 0| ≤ 10 * ρ₀ ∧ |u' j 1| ≤ 10 * ρ₀ := by
    intro j hj
    have h0 : u' j 0 = u j 0 := by dsimp only [u']; exact shiftedZReflectFun_0 (u j)
    have h1 : u' j 1 = u j 1 := by dsimp only [u']; exact shiftedZReflectFun_1 (u j)
    have h_orig := h_dir j (h_sub_neg j hj)
    rw [←h0, ←h1] at h_orig <;> exact h_orig

  have h_m_trans' : ∀ j ∈ negIndices, |(m' j) 0| ≤ C_midtrans * A * ρ₀ ∧ |(m' j) 1| ≤ C_midtrans * A * ρ₀ := by
    intro j hj
    have h0 : (m' j) 0 = (m j) 0 := by dsimp only [m']; exact shiftedZReflectFun_0 (m j)
    have h1 : (m' j) 1 = (m j) 1 := by dsimp only [m']; exact shiftedZReflectFun_1 (m j)
    have h_orig := h_m_trans j (h_sub_neg j hj)
    rw [←h0, ←h1] at h_orig <;> exact h_orig

  have h_m_long' : ∀ j ∈ negIndices, |(m' j) 2| ≤ C_midlong * A := by
    intro j hj
    have h0 : (m' j) 2 = -(m j) 2 := by dsimp only [m']; exact shiftedZReflectFun_2 (m j)
    have h1 : |(m' j) 2| = |(m j) 2| := by rw [h0, abs_neg]
    rw [h1]; exact h_m_long j (h_sub_neg j hj)

  have hball_neg'_idx : ∀ j ∈ negIndices, ∀ i : Fin 5, |(params' j) i| ≤ R i := by
    intro j hj i
    have hdir := h_dir' j hj
    have hmt := h_m_trans' j hj
    have hml := h_m_long' j hj
    fin_cases i
    · simpa [params', R] using hdir.1
    · simpa [params', R] using hdir.2
    · simpa [params', R] using hmt.1
    · simpa [params', R] using hmt.2
    · simpa [params', R] using hml

  have h_sep_neg' : ∀ (v : Fin 5 → ℝ), v ∈ Finset.image params' negIndices →
      ∀ (w : Fin 5 → ℝ), w ∈ Finset.image params' negIndices →
        v ≠ w → ∃ i : Fin 5, |v i - w i| ≥ s i := by
    intro v hv w hw hne
    rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨k, hk, h_eq⟩
    have h_jk : j ≠ k := by
      intro h
      have h_contra : params' j = w := by
        calc params' j = params' k := by rw [h]
          _ = w := h_eq
      exact hne h_contra
    have h_dist : (T j).EssentiallyDistinct (T k) :=
      h_distinct j k (h_sub_neg j hj) (h_sub_neg k hk) h_jk
    by_contra h
    push_neg at h
    have h' : ∀ i : Fin 5, |(params' j) i - (params' k) i| ≤ s i := by
      intro i
      have h_i : |(params' j) i - w i| < s i := h i
      rw [←h_eq] at h_i
      exact h_i.le
    have h_m0 : |(m' j - m' k) 0| ≤ ρ₀ / 200 := by
      have h_eq2 : (m' j - m' k) 0 = (params' j) 2 - (params' k) 2 := by
        simp [params', Pi.sub_apply] <;> rfl
      rw [h_eq2]; exact h' 2
    have h_m1 : |(m' j - m' k) 1| ≤ ρ₀ / 200 := by
      have h_eq2 : (m' j - m' k) 1 = (params' j) 3 - (params' k) 3 := by
        simp [params', Pi.sub_apply] <;> rfl
      rw [h_eq2]; exact h' 3
    have h_m2 : |(m' j - m' k) 2| ≤ 1 / 6400 := by
      have h_eq2 : (m' j - m' k) 2 = (params' j) 4 - (params' k) 4 := by
        simp [params', Pi.sub_apply] <;> rfl
      rw [h_eq2]; exact h' 4
    have h_u0 : |(u' j - u' k) 0| ≤ ρ₀ / 200 := by
      have h_eq2 : (u' j - u' k) 0 = (params' j) 0 - (params' k) 0 := by
        simp [params', Pi.sub_apply] <;> rfl
      rw [h_eq2]; exact h' 0
    have h_u1 : |(u' j - u' k) 1| ≤ ρ₀ / 200 := by
      have h_eq2 : (u' j - u' k) 1 = (params' j) 1 - (params' k) 1 := by
        simp [params', Pi.sub_apply] <;> rfl
      rw [h_eq2]; exact h' 1
    have h_close : ¬ (T j).EssentiallyDistinct (T k) :=
      close_params_not_distinct_coarse hρ₀ hρ₀1 frame'
        (m' j) (m' k) (u' j) (u' k)
        (hm' j) (hm' k) (hu' j) (hu' k)
        (h_z'_pos j hj) (h_z'_pos k hk)
        (h_dir' k hk).1
        (h_dir' k hk).2
        h_m0 h_m1 h_m2 h_u0 h_u1
        h_capsule_lower h_capsule_upper
    exact h_close h_dist

  let V_pos := Finset.image params posIndices
  let V_neg := Finset.image params' negIndices

  have hball_pos' : ∀ v ∈ V_pos, ∀ i, |v i| ≤ R i := by
    intro v hv i
    rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    exact hball_pos_idx j hj i

  have hball_neg' : ∀ v ∈ V_neg, ∀ i, |v i| ≤ R i := by
    intro v hv i
    rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    exact hball_neg'_idx j hj i

  have h_card_pos : V_pos.card ≤ ∏ i : Fin 5, (2 * Nat.ceil (R i / s i) + 1) :=
    anisotropic_cell_pack hs hR hball_pos' h_sep_pos
  have h_card_neg : V_neg.card ≤ ∏ i : Fin 5, (2 * Nat.ceil (R i / s i) + 1) :=
    anisotropic_cell_pack hs hR hball_neg' h_sep_neg'

  -- Injectivity of params on posIndices
  have h_inj_pos : Set.InjOn params posIndices := by
    intro j hj k hk h_eq
    by_cases h : j = k
    · exact h
    · have h_dist := h_distinct j k (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hk).1 h
      have h_all : ∀ i, |(params j) i - (params k) i| ≤ s i := by
        intro i
        have h_eq_i : (params j) i = (params k) i := by rw [h_eq]
        have h_sub : (params j) i - (params k) i = 0 := by rw [h_eq_i] <;> ring
        rw [h_sub]; have h_abs : |(0 : ℝ)| = 0 := abs_zero
        rw [h_abs]; exact (hs i).le
      have h_m0 : |(m j - m k) 0| ≤ ρ₀ / 200 := by
        have h_eq2 : (m j - m k) 0 = (params j) 2 - (params k) 2 := by
          simp [params, Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 2
      have h_m1 : |(m j - m k) 1| ≤ ρ₀ / 200 := by
        have h_eq2 : (m j - m k) 1 = (params j) 3 - (params k) 3 := by
          simp [params, Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 3
      have h_m2 : |(m j - m k) 2| ≤ 1 / 6400 := by
        have h_eq2 : (m j - m k) 2 = (params j) 4 - (params k) 4 := by
          simp [params, Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 4
      have h_u0 : |(u j - u k) 0| ≤ ρ₀ / 200 := by
        have h_eq2 : (u j - u k) 0 = (params j) 0 - (params k) 0 := by
          simp [params, Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 0
      have h_u1 : |(u j - u k) 1| ≤ ρ₀ / 200 := by
        have h_eq2 : (u j - u k) 1 = (params j) 1 - (params k) 1 := by
          simp [params, Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 1
      have h_close : ¬ (T j).EssentiallyDistinct (T k) :=
        close_params_not_distinct_coarse hρ₀ hρ₀1 frame
          (m j) (m k) (u j) (u k)
          (hm j) (hm k) (hu j) (hu k)
          (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
          (h_dir k (Finset.mem_filter.mp hk).1).1
          (h_dir k (Finset.mem_filter.mp hk).1).2
          h_m0 h_m1 h_m2 h_u0 h_u1
          h_capsule_lower h_capsule_upper
      exact False.elim (h_close h_dist)

  -- Injectivity of params' on negIndices
  have h_inj_neg : Set.InjOn params' negIndices := by
    intro j hj k hk h_eq
    by_cases h : j = k
    · exact h
    · have h_dist := h_distinct j k (h_sub_neg j hj) (h_sub_neg k hk) h
      have h_all : ∀ i, |(params' j) i - (params' k) i| ≤ s i := by
        intro i
        have h_eq_i : (params' j) i = (params' k) i := by rw [h_eq]
        have h_sub : (params' j) i - (params' k) i = 0 := by rw [h_eq_i] <;> ring
        rw [h_sub]; have h_abs : |(0 : ℝ)| = 0 := abs_zero
        rw [h_abs]; exact (hs i).le
      have h_m0 : |(m' j - m' k) 0| ≤ ρ₀ / 200 := by
        have h_eq2 : (m' j - m' k) 0 = (params' j) 2 - (params' k) 2 := by
          simp [params', Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 2
      have h_m1 : |(m' j - m' k) 1| ≤ ρ₀ / 200 := by
        have h_eq2 : (m' j - m' k) 1 = (params' j) 3 - (params' k) 3 := by
          simp [params', Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 3
      have h_m2 : |(m' j - m' k) 2| ≤ 1 / 6400 := by
        have h_eq2 : (m' j - m' k) 2 = (params' j) 4 - (params' k) 4 := by
          simp [params', Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 4
      have h_u0 : |(u' j - u' k) 0| ≤ ρ₀ / 200 := by
        have h_eq2 : (u' j - u' k) 0 = (params' j) 0 - (params' k) 0 := by
          simp [params', Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 0
      have h_u1 : |(u' j - u' k) 1| ≤ ρ₀ / 200 := by
        have h_eq2 : (u' j - u' k) 1 = (params' j) 1 - (params' k) 1 := by
          simp [params', Pi.sub_apply] <;> rfl
        rw [h_eq2]; exact h_all 1
      have h_close : ¬ (T j).EssentiallyDistinct (T k) :=
        close_params_not_distinct_coarse hρ₀ hρ₀1 frame'
          (m' j) (m' k) (u' j) (u' k)
          (hm' j) (hm' k) (hu' j) (hu' k)
          (h_z'_pos j hj) (h_z'_pos k hk)
          (h_dir' k hk).1
          (h_dir' k hk).2
          h_m0 h_m1 h_m2 h_u0 h_u1
          h_capsule_lower h_capsule_upper
      exact False.elim (h_close h_dist)

  have h_pos_card : posIndices.card = V_pos.card := by
    rw [Finset.card_image_of_injOn h_inj_pos]
  have h_neg_card : negIndices.card = V_neg.card := by
    rw [Finset.card_image_of_injOn h_inj_neg]

  have h_main : indices.card ≤ posIndices.card + negIndices.card := by
    have h : indices.card ≤ (posIndices ∪ negIndices).card := Finset.card_le_card h_cover
    have h2 : (posIndices ∪ negIndices).card ≤ posIndices.card + negIndices.card :=
      Finset.card_union_le _ _
    linarith

  have h0 : 10 * ρ₀ / (ρ₀ / 200) = (2000 : ℝ) := by
    field_simp [hρ₀.ne'] <;> ring
  have h2 : C_midtrans * A * ρ₀ / (ρ₀ / 200) = 200 * C_midtrans * A := by
    field_simp [hρ₀.ne'] <;> ring
  have h4 : C_midlong * A / (1 / 6400 : ℝ) = 6400 * C_midlong * A := by
    field_simp <;> ring
  have h_ceil2000 : Nat.ceil (2000 : ℝ) = 2000 := by
    rw [Nat.ceil_eq_iff] <;> norm_num
  have h_product : ∏ i : Fin 5, (2 * Nat.ceil (R i / s i) + 1) =
      4001^2 * (2 * Nat.ceil (200 * C_midtrans * A) + 1)^2 *
      (2 * Nat.ceil (6400 * C_midlong * A) + 1) := by
    simp [R, s, Fin.prod_univ_succ, h0, h2, h4, h_ceil2000] <;> ring

  rw [h_pos_card, h_neg_card] at h_main
  rw [h_product] at h_card_pos h_card_neg
  linarith

end Kakeya.Assouad

end
