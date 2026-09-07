import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.GeometryHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DilationExt
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CloseAxialTubes
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Tight constant conflict-degree bound for paper-distinct selection
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined Metric Set InnerProductSpace
open Kakeya.Streamlined.GeometricLemmas

attribute [local instance] Classical.propDecidable

/-- Given a unit vector v, construct an affine isometry frame where v maps to
the z-axis (coordinate 2) in frame coordinates. -/
lemma frame_of_axis (v : Point3) (hv : ‖v‖ = 1) :
    ∃ (e1 e2 : Point3) (frame : Point3 ≃ᵃⁱ[ℝ] Point3),
      (frame.symm.linearIsometryEquiv v) 2 = 1 ∧
      (frame.symm.linearIsometryEquiv v) 0 = 0 ∧
      (frame.symm.linearIsometryEquiv v) 1 = 0 := by
  rcases orthonormal_basis3 v hv with ⟨e1, e2, h_orth⟩
  let b_orig : Fin 3 → Point3 := ![v, e1, e2]
  have h_orth_orig : Orthonormal ℝ b_orig := h_orth
  letI : Fact (Module.finrank ℝ Point3 = 3) := ⟨by simp [Point3]⟩
  have h_span : Submodule.span ℝ (Set.range b_orig) = ⊤ := by
    have h3 : Module.finrank ℝ Point3 = 3 := by simp [Point3]
    rw [h3] at *
    exact h_orth_orig.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)
  have h_compl : (Submodule.span ℝ (Set.range b_orig))ᗮ = ⊥ := by
    rw [h_span]
    simp
  let b : OrthonormalBasis (Fin 3) ℝ Point3 :=
    OrthonormalBasis.mkOfOrthogonalEqBot h_orth_orig h_compl
  let std : OrthonormalBasis (Fin 3) ℝ Point3 :=
    EuclideanSpace.basisFun (Fin 3) ℝ
  -- σ: 0→2, 1→0, 2→1 (cycle)
  let σ : Fin 3 ≃ Fin 3 :=
    (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 2)
  let e : Point3 ≃ₗᵢ[ℝ] Point3 := b.equiv std σ
  let frame : Point3 ≃ᵃⁱ[ℝ] Point3 := e.symm.toAffineIsometryEquiv
  have h_b_eq : (b : Fin 3 → Point3) = b_orig :=
    OrthonormalBasis.coe_of_orthogonal_eq_bot_mk h_orth_orig h_compl
  have h_b0 : b 0 = v := by
    rw [h_b_eq] <;> rfl
  have h_sigma0 : σ 0 = 2 := by
    simp [σ, Equiv.swap_apply_def] <;> decide
  have h_ev : e v = std 2 := by
    have h_eq : e (b 0) = std (σ 0) :=
      OrthonormalBasis.equiv_apply_basis b std σ 0
    rw [h_b0, h_sigma0] at h_eq
    exact h_eq
  refine ⟨e1, e2, frame, ?_⟩
  have h2 : frame.symm.linearIsometryEquiv = e := by
    have h3 : frame = e.symm.toAffineIsometryEquiv := by rfl
    rw [h3]
    have h4 : (e.symm.toAffineIsometryEquiv).symm.linearIsometryEquiv = e := by
      rfl
    exact h4
  rw [h2, h_ev]
  have h_std2 : (std 2) 2 = 1 := by
    simp [std, EuclideanSpace.basisFun, EuclideanSpace.single]
    <;> aesop
  have h_std0 : (std 2) 0 = 0 := by
    simp [std, EuclideanSpace.basisFun, EuclideanSpace.single]
    <;> aesop
  have h_std1 : (std 2) 1 = 0 := by
    simp [std, EuclideanSpace.basisFun, EuclideanSpace.single]
    <;> aesop
  exact ⟨h_std2, h_std0, h_std1⟩

/--
### Core lemma: two tubes with close frame parameters are not essentially distinct.

Given a frame where both directions have z-component ≥ 1/2, and midpoint/direction
differences bounded by the anisotropic grid cell sizes, apply
`close_axial_tubes_not_distinct` with a common axial plane at tube 1's midpoint.
-/
lemma close_params_not_distinct
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    {T1 T2 : Kakeya.DeltaTube δ}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (m1 m2 u1 u2 : Point3)
    (hm1 : m1 = frame.symm (T1.base + (1 / 2 : ℝ) • T1.direction))
    (hm2 : m2 = frame.symm (T2.base + (1 / 2 : ℝ) • T2.direction))
    (hu1 : u1 = frame.symm.linearIsometryEquiv T1.direction)
    (hu2 : u2 = frame.symm.linearIsometryEquiv T2.direction)
    (hu1_pos : u1 2 ≥ 1 / 2)
    (hu2_pos : u2 2 ≥ 1 / 2)
    (h_u2_0 : |u2 0| ≤ 8 * δ)
    (h_u2_1 : |u2 1| ≤ 8 * δ)
    (h_m0 : |(m1 - m2) 0| ≤ δ / 200)
    (h_m1 : |(m1 - m2) 1| ≤ δ / 200)
    (h_m2 : |(m1 - m2) 2| ≤ 1 / 3200)
    (h_u0 : |(u1 - u2) 0| ≤ δ / 200)
    (h_u1 : |(u1 - u2) 1| ≤ δ / 200)
    (h_capsule_lower : CapsuleLowerBound)
    (h_capsule_upper : CapsuleUpperBound) :
    ¬ T1.EssentiallyDistinct T2 := by
  let b1 := m1 - (1 / 2 : ℝ) • u1
  let b2 := m2 - (1 / 2 : ℝ) • u2
  let z0 := m1 2
  let t1 : ℝ := 1 / 2
  let t2 : ℝ := (z0 - b2 2) / u2 2
  let q1 := b1 + t1 • u1
  let q2 := b2 + t2 • u2

  have h_u2_pos' : 0 < u2 2 := by linarith
  let e := frame.symm
  have h_affine1 : e (T1.base + (1 / 2 : ℝ) • T1.direction) =
      e T1.base + (1 / 2 : ℝ) • e.linearIsometryEquiv T1.direction := by
    have h_vadd := e.map_vadd T1.base ((1 / 2 : ℝ) • T1.direction)
    have h1 : ((1 / 2 : ℝ) • T1.direction +ᵥ T1.base) = T1.base + (1 / 2 : ℝ) • T1.direction := by
      simp [vadd_eq_add] <;> abel
    have h_smul : e.linearIsometryEquiv ((1 / 2 : ℝ) • T1.direction) =
        (1 / 2 : ℝ) • e.linearIsometryEquiv T1.direction :=
      e.linearIsometryEquiv.map_smul (1 / 2 : ℝ) T1.direction
    simpa [h1, vadd_eq_add, h_smul, add_comm] using h_vadd
  have h_affine2 : e (T2.base + (1 / 2 : ℝ) • T2.direction) =
      e T2.base + (1 / 2 : ℝ) • e.linearIsometryEquiv T2.direction := by
    have h_vadd := e.map_vadd T2.base ((1 / 2 : ℝ) • T2.direction)
    have h1 : ((1 / 2 : ℝ) • T2.direction +ᵥ T2.base) = T2.base + (1 / 2 : ℝ) • T2.direction := by
      simp [vadd_eq_add] <;> abel
    have h_smul : e.linearIsometryEquiv ((1 / 2 : ℝ) • T2.direction) =
        (1 / 2 : ℝ) • e.linearIsometryEquiv T2.direction :=
      e.linearIsometryEquiv.map_smul (1 / 2 : ℝ) T2.direction
    simpa [h1, vadd_eq_add, h_smul, add_comm] using h_vadd
  have hb1 : b1 = frame.symm T1.base := by
    have h : m1 = e T1.base + (1 / 2 : ℝ) • u1 := by
      have h_step1 : m1 = e (T1.base + (1 / 2 : ℝ) • T1.direction) := hm1
      rw [h_step1, h_affine1, hu1]
    have h2 : b1 = m1 - (1 / 2 : ℝ) • u1 := by rfl
    rw [h2, h] <;> abel
  have hb2 : b2 = frame.symm T2.base := by
    have h : m2 = e T2.base + (1 / 2 : ℝ) • u2 := by
      have h_step1 : m2 = e (T2.base + (1 / 2 : ℝ) • T2.direction) := hm2
      rw [h_step1, h_affine2, hu2]
    have h2 : b2 = m2 - (1 / 2 : ℝ) • u2 := by rfl
    rw [h2, h] <;> abel
  have hq1_eq : q1 = m1 := by
    have h2 : q1 = b1 + (1 / 2 : ℝ) • u1 := by rfl
    have h3 : b1 = m1 - (1 / 2 : ℝ) • u1 := by rfl
    rw [h2, h3] <;> abel
  have h_b22 : b2 2 = m2 2 - (1 / 2 : ℝ) * u2 2 := by
    have h : b2 = m2 - (1 / 2 : ℝ) • u2 := by rfl
    rw [h]
    simp [Pi.sub_apply, Pi.smul_apply] <;> ring
  have h_z0 : z0 = m1 2 := by rfl
  have h_t2_form : t2 = (m1 2 - m2 2) / u2 2 + 1 / 2 := by
    have h : t2 = (z0 - b2 2) / u2 2 := by rfl
    rw [h, h_z0, h_b22]
    field_simp [h_u2_pos'.ne'] <;> ring
  have h_q2_2 : q2 2 = z0 := by
    have h : q2 2 = b2 2 + t2 * u2 2 := by
      have hq : q2 = b2 + t2 • u2 := by rfl
      rw [hq]
      simp [Pi.add_apply, Pi.smul_apply] <;> ring
    have h2 : t2 * u2 2 = z0 - b2 2 := by
      have h3 : t2 = (z0 - b2 2) / u2 2 := by rfl
      rw [h3]
      field_simp [h_u2_pos'.ne'] <;> ring
    linarith [h, h2]
  have h_tdiff_eq : t2 - 1 / 2 = (m1 2 - m2 2) / u2 2 := by
    rw [h_t2_form] <;> ring
  have h_m2' : |m1 2 - m2 2| ≤ 1 / 3200 := by
    have h_eq : m1 2 - m2 2 = (m1 - m2) 2 := by
      simp [Pi.sub_apply] <;> ring
    rw [h_eq]
    exact h_m2
  have h_tdiff_bound : |t2 - 1 / 2| ≤ 1 / 1600 := by
    rw [h_tdiff_eq]
    have h_abs : |(m1 2 - m2 2) / u2 2| = |m1 2 - m2 2| / |u2 2| := by rw [abs_div]
    rw [h_abs]
    have h3 : |u2 2| = u2 2 := by rw [abs_of_pos] <;> linarith
    rw [h3]
    have h4 : 0 < u2 2 := h_u2_pos'
    have h5 : |m1 2 - m2 2| / u2 2 ≤ (1 / 3200 : ℝ) / u2 2 := by
      apply div_le_div_of_nonneg_right h_m2' (by linarith)
    have h6 : (1 / 3200 : ℝ) / u2 2 ≤ (1 / 3200 : ℝ) / (1 / 2 : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    linarith
  have h_tdiff : |t1 - t2| ≤ 1 / 8 := by
    have h : |t1 - t2| = |t2 - 1 / 2| := by
      have h4 : t1 = (1 / 2 : ℝ) := by rfl
      rw [h4, abs_sub_comm]
    rw [h]
    linarith [h_tdiff_bound]
  have h2_abs : |(m1 2 - m2 2) / u2 2| ≤ 1 / 1600 := by
    have h_eq : (m1 2 - m2 2) / u2 2 = t2 - 1 / 2 := h_tdiff_eq.symm
    simpa [h_eq] using h_tdiff_bound
  have ht2_in : t2 ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : t2 = 1 / 2 + (m1 2 - m2 2) / u2 2 := by linarith [h_t2_form]
    rw [h1]
    have h_bounds := abs_le.mp h2_abs
    have h_pos : -1 / 1600 ≤ (m1 2 - m2 2) / u2 2 := by linarith [h_bounds.1]
    have h_neg : (m1 2 - m2 2) / u2 2 ≤ 1 / 1600 := by linarith [h_bounds.2]
    constructor <;> linarith
  have hq2_eq : q2 = m2 + (t2 - 1 / 2 : ℝ) • u2 := by
    have h1 : q2 = b2 + t2 • u2 := by rfl
    have h2 : b2 = m2 - (1 / 2 : ℝ) • u2 := by rfl
    rw [h1, h2]
    ext i
    fin_cases i <;> simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] <;> ring
  have h_q2_0 : |(q1 - q2) 0| ≤ δ / 100 := by
    have h_eq : (q1 - q2) 0 = (m1 - m2) 0 - (t2 - 1 / 2) * u2 0 := by
      rw [hq1_eq, hq2_eq]
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h_eq]
    have h_tri : |(m1 - m2) 0 - (t2 - 1 / 2) * u2 0| ≤
        |(m1 - m2) 0| + |(t2 - 1 / 2) * u2 0| := by
      calc
        |(m1 - m2) 0 - (t2 - 1 / 2) * u2 0|
          ≤ |(m1 - m2) 0| + |-((t2 - 1 / 2) * u2 0)| := by
            simpa only [abs_neg] using
              abs_sub ((m1 - m2) 0) ((t2 - 1 / 2) * u2 0)
        _ = |(m1 - m2) 0| + |(t2 - 1 / 2) * u2 0| := by rw [abs_neg]
    have h_abs_mul : |(t2 - 1 / 2) * u2 0| = |t2 - 1 / 2| * |u2 0| := by rw [abs_mul]
    rw [h_abs_mul] at h_tri
    have h_main : |(m1 - m2) 0| + |t2 - 1 / 2| * |u2 0| ≤ δ / 200 + (1 / 1600 : ℝ) * (8 * δ) := by
      gcongr <;> linarith
    linarith [h_tri, h_main]
  have h_q2_1 : |(q1 - q2) 1| ≤ δ / 100 := by
    have h_eq : (q1 - q2) 1 = (m1 - m2) 1 - (t2 - 1 / 2) * u2 1 := by
      rw [hq1_eq, hq2_eq]
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h_eq]
    have h_tri : |(m1 - m2) 1 - (t2 - 1 / 2) * u2 1| ≤
        |(m1 - m2) 1| + |(t2 - 1 / 2) * u2 1| := by
      calc
        |(m1 - m2) 1 - (t2 - 1 / 2) * u2 1|
          ≤ |(m1 - m2) 1| + |-((t2 - 1 / 2) * u2 1)| := by
            simpa only [abs_neg] using
              abs_sub ((m1 - m2) 1) ((t2 - 1 / 2) * u2 1)
        _ = |(m1 - m2) 1| + |(t2 - 1 / 2) * u2 1| := by rw [abs_neg]
    have h_abs_mul : |(t2 - 1 / 2) * u2 1| = |t2 - 1 / 2| * |u2 1| := by rw [abs_mul]
    rw [h_abs_mul] at h_tri
    have h_main : |(m1 - m2) 1| + |t2 - 1 / 2| * |u2 1| ≤ δ / 200 + (1 / 1600 : ℝ) * (8 * δ) := by
      gcongr <;> linarith
    linarith [h_tri, h_main]
  have h_dir0' : |(u1 - u2) 0| ≤ δ / 100 := by
    calc
      |(u1 - u2) 0| ≤ δ / 200 := h_u0
      _ ≤ δ / 100 := by linarith
  have h_dir1' : |(u1 - u2) 1| ≤ δ / 100 := by
    calc
      |(u1 - u2) 1| ≤ δ / 200 := h_u1
      _ ≤ δ / 100 := by linarith
  have h_plane : q1 2 = q2 2 := by
    have h_q1_2 : q1 2 = z0 := by
      rw [hq1_eq, h_z0]
    rw [h_q1_2, h_q2_2]
  exact close_axial_tubes_not_distinct hδ (by linarith) frame
    b1 u1 b2 u2 q1 q2 t1 t2
    hb1 hu1 hb2 hu2
    (by norm_num) ht2_in
    (by simp [q1, b1]) (by simp [q2, b2])
    h_plane h_q2_0 h_q2_1 h_tdiff h_dir0' h_dir1'
    hu1_pos hu2_pos h_capsule_lower h_capsule_upper

/-- Helper: if 0 ≤ c and x^2 ≤ c^2, then |x| ≤ c. -/
private lemma abs_le_of_sq_le {x c : ℝ} (hc : 0 ≤ c) (h : x^2 ≤ c^2) : |x| ≤ c := by
  have h1 : |x|^2 = x^2 := by simp [abs_pow]
  have h2 : |x|^2 ≤ c^2 := by rw [h1] <;> exact h
  have h3 : 0 ≤ |x| := abs_nonneg _
  by_contra h4
  have h5 : c < |x| := by linarith
  have h6 : c^2 < |x|^2 := by
    gcongr
    <;> linarith
  linarith

/-- Helper: apply affine isometry to p + t•v. -/
private lemma affine_apply_vadd_smul
    (e : Point3 ≃ᵃⁱ[ℝ] Point3) (p : Point3) (t : ℝ) (v : Point3) :
    e (p + t • v) = e p + t • e.linearIsometryEquiv v := by
  calc
    e (p + t • v)
      = e ((t • v) +ᵥ p) := by rw [vadd_eq_add] <;> abel
    _ = e.linearIsometryEquiv (t • v) +ᵥ e p := e.toAffineMap.map_vadd p (t • v)
    _ = (t • e.linearIsometryEquiv v) +ᵥ e p := by
      rw [e.linearIsometryEquiv.map_smul t v]
    _ = e p + t • e.linearIsometryEquiv v := by
      rw [vadd_eq_add] <;> abel

/-- Helper: if |x| ≥ 1/2, then x ≥ 1/2 or x ≤ -1/2. -/
private lemma sign_from_abs_half {x : ℝ} (h : |x| ≥ 1 / 2) : x ≥ 1 / 2 ∨ x ≤ -1 / 2 := by
  by_cases hcase : 0 ≤ x
  · left
    have h_eq : |x| = x := abs_eq_self.mpr hcase
    rw [h_eq] at h
    exact h
  · right
    have h_neg : x < 0 := lt_of_not_ge hcase
    have h_pos : 0 ≤ -x := by exact neg_nonneg.mpr (le_of_lt h_neg)
    have h1 : |-x| = -x := abs_eq_self.mpr h_pos
    have h2 : |x| = |-x| := by rw [abs_neg]
    have h_eq : |x| = -x := by rw [h2, h1]
    rw [h_eq] at h
    linarith

/-- Helper: norm squared of Point3 equals sum of component squares. -/
private lemma norm_sq_point3 (y : Point3) : ‖y‖^2 = (y 0)^2 + (y 1)^2 + (y 2)^2 := by
  have h1 : ‖y‖^2 = ∑ i : Fin 3, (y i)^2 := EuclideanSpace.real_norm_sq_eq y
  rw [h1]
  have h2 : ∑ i : Fin 3, (y i)^2 = (y 0)^2 + (y 1)^2 + (y 2)^2 := by
    simp [Fin.sum_univ_succ]
    <;> ring
  exact h2

/-- Helper: each component's absolute value is at most the norm. -/
private lemma component_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h_nonneg : ∀ j : Fin 3, 0 ≤ (x j)^2 := fun j => sq_nonneg (x j)
  have h1 : (x i)^2 ≤ ∑ j : Fin 3, (x j)^2 :=
    Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)
  have h2 : (x i)^2 ≤ ‖x‖^2 := by
    have h3 : ‖x‖^2 = ∑ j : Fin 3, (x j)^2 := EuclideanSpace.real_norm_sq_eq x
    rw [h3]
    exact h1
  have h4 : 0 ≤ ‖x‖ := norm_nonneg _
  exact abs_le_of_sq_le h4 h2

/-- Helper: derive transverse and longitudinal bounds from midpoint distance. -/
private lemma bounds_from_midpoint
    {δ : ℝ} (hδ : 0 < δ)
    {p_i v m_j : Point3} {sm : ℝ}
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hv2 : v 2 = 1)
    (h_mid_dist : dist m_j (p_i + sm • v) ≤ 2 * δ)
    (hsm_lower : -1 / 2 ≤ sm) (hsm_upper : sm ≤ 3 / 2) :
    (|(m_j - p_i) 0| ≤ 2 * δ) ∧
    (|(m_j - p_i) 1| ≤ 2 * δ) ∧
    (-1 / 2 - 2 * δ ≤ (m_j - p_i) 2) ∧
    ((m_j - p_i) 2 ≤ 3 / 2 + 2 * δ) := by
  let x_mid := m_j - (p_i + sm • v)
  have h_xmid_norm : ‖x_mid‖ ≤ 2 * δ := by
    have h : ‖x_mid‖ = dist m_j (p_i + sm • v) := by
      rw [dist_eq_norm] <;> rfl
    rw [h]
    exact h_mid_dist
  have h_comp0 : |x_mid 0| ≤ ‖x_mid‖ := component_le_norm x_mid 0
  have h_comp1 : |x_mid 1| ≤ ‖x_mid‖ := component_le_norm x_mid 1
  have h_comp2 : |x_mid 2| ≤ ‖x_mid‖ := component_le_norm x_mid 2
  have h_xmid0_eq : x_mid 0 = (m_j - p_i) 0 := by
    have h : x_mid 0 = (m_j - (p_i + sm • v)) 0 := by rfl
    rw [h]
    have h2 : (m_j - (p_i + sm • v)) 0 = (m_j - p_i) 0 - sm * v 0 := by
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h2, hv0] <;> ring
  have h_xmid1_eq : x_mid 1 = (m_j - p_i) 1 := by
    have h : x_mid 1 = (m_j - (p_i + sm • v)) 1 := by rfl
    rw [h]
    have h2 : (m_j - (p_i + sm • v)) 1 = (m_j - p_i) 1 - sm * v 1 := by
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h2, hv1] <;> ring
  have h_xmid2_eq : x_mid 2 = (m_j - p_i) 2 - sm := by
    have h : x_mid 2 = (m_j - (p_i + sm • v)) 2 := by rfl
    rw [h]
    have h2 : (m_j - (p_i + sm • v)) 2 = (m_j - p_i) 2 - sm * v 2 := by
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h2, hv2] <;> ring
  have h_trans0 : |(m_j - p_i) 0| ≤ 2 * δ := by
    rw [←h_xmid0_eq]
    exact h_comp0.trans h_xmid_norm
  have h_trans1 : |(m_j - p_i) 1| ≤ 2 * δ := by
    rw [←h_xmid1_eq]
    exact h_comp1.trans h_xmid_norm
  have h_abs2 : -|x_mid 2| ≤ x_mid 2 ∧ x_mid 2 ≤ |x_mid 2| := abs_le.mp (le_refl |x_mid 2|)
  have h_xmid2_abs : |x_mid 2| ≤ 2 * δ := h_comp2.trans h_xmid_norm
  have h_long_lower : -1 / 2 - 2 * δ ≤ (m_j - p_i) 2 := by
    have h : (m_j - p_i) 2 = x_mid 2 + sm := by linarith [h_xmid2_eq]
    rw [h]
    linarith [h_abs2.1, h_xmid2_abs, hsm_lower]
  have h_long_upper : (m_j - p_i) 2 ≤ 3 / 2 + 2 * δ := by
    have h : (m_j - p_i) 2 = x_mid 2 + sm := by linarith [h_xmid2_eq]
    rw [h]
    linarith [h_abs2.2, h_xmid2_abs, hsm_upper]
  exact ⟨h_trans0, h_trans1, h_long_lower, h_long_upper⟩

/-- Helper: derive sign of u_j2 from difference bounds. -/
private lemma sign_from_diff_bounds {δ : ℝ} (hδ1 : δ ≤ 1 / 16)
    {u_j2 s1 s0 : ℝ}
    (h_s_diff_bound : |s1 - s0| ≥ 1 - 4 * δ)
    (h11 : |u_j2 - (s1 - s0)| ≤ 4 * δ) :
    u_j2 ≥ 1 / 2 ∨ u_j2 ≤ -1 / 2 := by
  have h_tri : |s1 - s0| ≤ |u_j2| + |u_j2 - (s1 - s0)| := by
    have h : |u_j2 - (u_j2 - (s1 - s0))| ≤ |u_j2| + |u_j2 - (s1 - s0)| := abs_sub _ _
    have h_eq : u_j2 - (u_j2 - (s1 - s0)) = s1 - s0 := by ring
    rw [h_eq] at h
    exact h
  have h_lower : |u_j2| ≥ 1 - 8 * δ := by linarith [h_s_diff_bound, h11, h_tri]
  have h_half : |u_j2| ≥ 1 / 2 := by linarith [hδ1]
  exact sign_from_abs_half h_half

/-- Helper: prove midpoint distance bound using affine isometry. -/
private lemma midpoint_dist_bound
    {δ : ℝ} {T_i T_j : Kakeya.DeltaTube δ}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (p_i v p_j u_j m_j : Point3) (sm : ℝ)
    (hpi : p_i = frame.symm T_i.base)
    (hv : v = frame.symm.linearIsometryEquiv T_i.direction)
    (hpj : p_j = frame.symm T_j.base)
    (huj : u_j = frame.symm.linearIsometryEquiv T_j.direction)
    (hmj : m_j = p_j + (1 / 2 : ℝ) • u_j)
    (hzm_dist : dist (T_j.base + (1 / 2 : ℝ) • T_j.direction)
        (T_i.base + sm • T_i.direction) ≤ 2 * δ) :
    dist m_j (p_i + sm • v) ≤ 2 * δ := by
  let m_j_orig := T_j.base + (1 / 2 : ℝ) • T_j.direction
  have h_map_j := affine_apply_vadd_smul frame.symm T_j.base (1 / 2 : ℝ) T_j.direction
  have h_map_i := affine_apply_vadd_smul frame.symm T_i.base sm T_i.direction
  have h_mj : frame.symm m_j_orig = m_j := by
    have h1 : frame.symm m_j_orig = frame.symm T_j.base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv T_j.direction := by
      exact h_map_j
    have h2 : frame.symm T_j.base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv T_j.direction =
        p_j + (1 / 2 : ℝ) • u_j := by
      calc
        frame.symm T_j.base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv T_j.direction
          = p_j + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv T_j.direction := by rw [hpj]
        _ = p_j + (1 / 2 : ℝ) • u_j := by rw [huj]
    calc
      frame.symm m_j_orig
        = frame.symm T_j.base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv T_j.direction := h1
      _ = p_j + (1 / 2 : ℝ) • u_j := h2
      _ = m_j := hmj.symm
  have h_i : frame.symm (T_i.base + sm • T_i.direction) = p_i + sm • v := by
    calc
      frame.symm (T_i.base + sm • T_i.direction)
        = frame.symm T_i.base + sm • frame.symm.linearIsometryEquiv T_i.direction := h_map_i
      _ = p_i + sm • frame.symm.linearIsometryEquiv T_i.direction := by rw [hpi]
      _ = p_i + sm • v := by rw [hv]
  have h_dist_map : dist (frame.symm m_j_orig) (frame.symm (T_i.base + sm • T_i.direction)) =
      dist m_j_orig (T_i.base + sm • T_i.direction) := frame.symm.dist_map _ _
  rw [h_mj, h_i] at h_dist_map
  rw [h_dist_map]
  exact hzm_dist

/-- Geometric extraction: if T_j ⊆ 2*T_i, then in a frame aligned with T_i,
T_j's direction is nearly axial and its midpoint is close to T_i's axis. -/
lemma conflict_geometric_bounds
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 16)
    {T_i T_j : Kakeya.DeltaTube δ}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (p_i v p_j u_j m_j : Point3)
    (hpi : p_i = frame.symm T_i.base)
    (hv : v = frame.symm.linearIsometryEquiv T_i.direction)
    (hv2 : v 2 = 1) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
    (hpj : p_j = frame.symm T_j.base)
    (huj : u_j = frame.symm.linearIsometryEquiv T_j.direction)
    (hmj : m_j = p_j + (1 / 2 : ℝ) • u_j)
    (h : T_j.carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) T_i) :
    (|u_j 0| ≤ 4 * δ) ∧ (|u_j 1| ≤ 4 * δ) ∧
    ((u_j 2 ≥ 1 / 2) ∨ (u_j 2 ≤ -1 / 2)) ∧
    (|(m_j - p_i) 0| ≤ 2 * δ) ∧ (|(m_j - p_i) 1| ≤ 2 * δ) ∧
    (-1 / 2 - 2 * δ ≤ (m_j - p_i) 2) ∧
    ((m_j - p_i) 2 ≤ 3 / 2 + 2 * δ) := by
  let S_ext_orig : Set Point3 := extendedSegment T_i
  have hS_cp : IsCompact S_ext_orig := by
    simp [S_ext_orig, extendedSegment]
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hS_nonempty : S_ext_orig.Nonempty :=
    ⟨T_i.base, ⟨0, by norm_num, by simp⟩⟩
  have h_carrier_def : T_j.carrier = Metric.cthickening δ (unitSegment T_j.base T_j.direction) := by rfl
  have h_dist_self : ∀ (x : Point3), dist x x ≤ δ := by
    intro x
    have h : dist x x = 0 := dist_self x
    rw [h] <;> linarith
  have h_pj_in : T_j.base ∈ T_j.carrier := by
    rw [h_carrier_def]
    exact Metric.mem_cthickening_of_dist_le T_j.base T_j.base δ _
      ⟨0, by norm_num, by simp⟩ (h_dist_self T_j.base)
  have h_puj_in : T_j.base + T_j.direction ∈ T_j.carrier := by
    rw [h_carrier_def]
    exact Metric.mem_cthickening_of_dist_le (T_j.base + T_j.direction) (T_j.base + T_j.direction) δ _
      ⟨1, by norm_num, by simp⟩ (h_dist_self _)
  have h_mj_in : T_j.base + (1 / 2 : ℝ) • T_j.direction ∈ T_j.carrier := by
    rw [h_carrier_def]
    exact Metric.mem_cthickening_of_dist_le (T_j.base + (1 / 2 : ℝ) • T_j.direction)
      (T_j.base + (1 / 2 : ℝ) • T_j.direction) δ _
      ⟨1 / 2, by norm_num, by simp⟩ (h_dist_self _)
  have h1 : Metric.infDist T_j.base S_ext_orig ≤ 2 * δ :=
    dilation_infDist_extended hδ.le T_i T_j.base (h h_pj_in)
  have h2 : Metric.infDist (T_j.base + T_j.direction) S_ext_orig ≤ 2 * δ :=
    dilation_infDist_extended hδ.le T_i (T_j.base + T_j.direction) (h h_puj_in)
  have h3 : Metric.infDist (T_j.base + (1 / 2 : ℝ) • T_j.direction) S_ext_orig ≤ 2 * δ :=
    dilation_infDist_extended hδ.le T_i (T_j.base + (1 / 2 : ℝ) • T_j.direction) (h h_mj_in)
  rcases hS_cp.exists_infDist_eq_dist hS_nonempty T_j.base with ⟨z0, hz0, hz0_eq⟩
  rcases hS_cp.exists_infDist_eq_dist hS_nonempty (T_j.base + T_j.direction) with ⟨z1, hz1, hz1_eq⟩
  rcases hS_cp.exists_infDist_eq_dist hS_nonempty (T_j.base + (1 / 2 : ℝ) • T_j.direction) with ⟨zm, hzm, hzm_eq⟩
  have hz0_dist : dist T_j.base z0 ≤ 2 * δ := by rw [←hz0_eq]; exact h1
  have hz1_dist : dist (T_j.base + T_j.direction) z1 ≤ 2 * δ := by rw [←hz1_eq]; exact h2
  have hzm_dist : dist (T_j.base + (1 / 2 : ℝ) • T_j.direction) zm ≤ 2 * δ := by rw [←hzm_eq]; exact h3
  rcases hz0 with ⟨s0, hs0, rfl⟩
  rcases hz1 with ⟨s1, hs1, rfl⟩
  rcases hzm with ⟨sm, hsm, rfl⟩
  have h_dir_dist : dist T_j.direction ((s1 - s0) • T_i.direction) ≤ 4 * δ := by
    have h_eq1 : T_j.direction = (T_j.base + T_j.direction) - T_j.base := by abel
    have h_eq2 : (s1 - s0) • T_i.direction =
        (T_i.base + s1 • T_i.direction) - (T_i.base + s0 • T_i.direction) := by
      have h : (T_i.base + s1 • T_i.direction) - (T_i.base + s0 • T_i.direction) =
          s1 • T_i.direction - s0 • T_i.direction := by abel
      rw [h]
      have h2 : s1 • T_i.direction - s0 • T_i.direction = (s1 - s0) • T_i.direction := by
        rw [←sub_smul] <;> ring
      exact h2.symm
    rw [h_eq1, h_eq2]
    have h : dist ((T_j.base + T_j.direction) - T_j.base)
        (((T_i.base + s1 • T_i.direction) - (T_i.base + s0 • T_i.direction))) ≤
        dist (T_j.base + T_j.direction) (T_i.base + s1 • T_i.direction) +
        dist T_j.base (T_i.base + s0 • T_i.direction) := by
      have h_norm : ‖((T_j.base + T_j.direction) - T_j.base) -
          ((T_i.base + s1 • T_i.direction) - (T_i.base + s0 • T_i.direction))‖ ≤
          ‖(T_j.base + T_j.direction) - (T_i.base + s1 • T_i.direction)‖ +
          ‖T_j.base - (T_i.base + s0 • T_i.direction)‖ := by
        have h_eq : ((T_j.base + T_j.direction) - T_j.base) -
            ((T_i.base + s1 • T_i.direction) - (T_i.base + s0 • T_i.direction)) =
            ((T_j.base + T_j.direction) - (T_i.base + s1 • T_i.direction)) -
            (T_j.base - (T_i.base + s0 • T_i.direction)) := by abel
        rw [h_eq]
        exact norm_sub_le _ _
      simpa [dist_eq_norm] using h_norm
    have h_final : dist (T_j.base + T_j.direction) (T_i.base + s1 • T_i.direction) +
        dist T_j.base (T_i.base + s0 • T_i.direction) ≤ 4 * δ := by
      linarith [hz1_dist, hz0_dist]
    linarith
  have h_uj_norm : ‖u_j‖ = 1 := by
    rw [huj]
    have h := frame.symm.linearIsometryEquiv.norm_map T_j.direction
    rw [h, T_j.direction_unit]
  have h_frame_dir_dist : dist u_j ((s1 - s0) • v) ≤ 4 * δ := by
    have h1 : u_j = frame.symm.linearIsometryEquiv T_j.direction := huj
    have h2 : (s1 - s0) • v = frame.symm.linearIsometryEquiv ((s1 - s0) • T_i.direction) := by
      have h21 : v = frame.symm.linearIsometryEquiv T_i.direction := hv
      rw [h21]
      rw [map_smul]
      <;> rfl
    rw [h1, h2]
    have h3 : dist (frame.symm.linearIsometryEquiv T_j.direction)
        (frame.symm.linearIsometryEquiv ((s1 - s0) • T_i.direction)) =
        dist T_j.direction ((s1 - s0) • T_i.direction) :=
      frame.symm.linearIsometryEquiv.dist_map _ _
    rw [h3]
    exact h_dir_dist
  have h_comp0 : (u_j - (s1 - s0) • v) 0 = u_j 0 := by
    simp [Pi.sub_apply, Pi.smul_apply, hv0] <;> ring
  have h_comp1 : (u_j - (s1 - s0) • v) 1 = u_j 1 := by
    simp [Pi.sub_apply, Pi.smul_apply, hv1] <;> ring
  have h_comp2 : (u_j - (s1 - s0) • v) 2 = u_j 2 - (s1 - s0) := by
    simp [Pi.sub_apply, Pi.smul_apply, hv2] <;> ring
  have h_norm_sq : ‖u_j - (s1 - s0) • v‖^2 = (u_j 0)^2 + (u_j 1)^2 + (u_j 2 - (s1 - s0))^2 := by
    have h : ∀ (x : Point3), ‖x‖^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
      intro x
      have h1 : ‖x‖ = Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;> ring
      rw [h1]
      rw [Real.sq_sqrt (by positivity)]
    rw [h (u_j - (s1 - s0) • v), h_comp0, h_comp1, h_comp2] <;> ring
  have h_dist2 : (u_j 0)^2 + (u_j 1)^2 + (u_j 2 - (s1 - s0))^2 ≤ (4 * δ)^2 := by
    have h : dist u_j ((s1 - s0) • v) = ‖u_j - (s1 - s0) • v‖ := by rw [dist_eq_norm]
    rw [h] at h_frame_dir_dist
    have h6 : 0 ≤ ‖u_j - (s1 - s0) • v‖ := norm_nonneg _
    have h7 : ‖u_j - (s1 - s0) • v‖ ≤ 4 * δ := h_frame_dir_dist
    have h5 : ‖u_j - (s1 - s0) • v‖^2 ≤ (4 * δ)^2 := by nlinarith
    rw [h_norm_sq] at h5
    exact h5
  have h_uj0_sq : (u_j 0)^2 ≤ (4 * δ)^2 := by
    have h_nonneg : 0 ≤ (u_j 1)^2 + (u_j 2 - (s1 - s0))^2 := by positivity
    nlinarith [h_dist2]
  have h_uj0 : |u_j 0| ≤ 4 * δ := by
    have h_pos : 0 ≤ 4 * δ := by linarith
    exact abs_le_of_sq_le h_pos h_uj0_sq
  have h_uj1_sq : (u_j 1)^2 ≤ (4 * δ)^2 := by
    have h_nonneg : 0 ≤ (u_j 0)^2 + (u_j 2 - (s1 - s0))^2 := by positivity
    nlinarith [h_dist2]
  have h_uj1 : |u_j 1| ≤ 4 * δ := by
    have h_pos : 0 ≤ 4 * δ := by linarith
    exact abs_le_of_sq_le h_pos h_uj1_sq
  have h_s_diff_bound : |s1 - s0| ≥ 1 - 4 * δ := by
    have h9 : ‖(s1 - s0) • T_i.direction‖ = |s1 - s0| := by
      rw [norm_smul, T_i.direction_unit] <;> simp
    have h10 : ‖T_j.direction‖ ≤ ‖(s1 - s0) • T_i.direction‖ + ‖T_j.direction - (s1 - s0) • T_i.direction‖ := by
      calc
        ‖T_j.direction‖
          = ‖(s1 - s0) • T_i.direction + (T_j.direction - (s1 - s0) • T_i.direction)‖ := by
            have h_sum : (s1 - s0) • T_i.direction + (T_j.direction - (s1 - s0) • T_i.direction) = T_j.direction := by abel
            rw [h_sum]
        _ ≤ ‖(s1 - s0) • T_i.direction‖ + ‖T_j.direction - (s1 - s0) • T_i.direction‖ := norm_add_le _ _
    have h11 : ‖T_j.direction - (s1 - s0) • T_i.direction‖ = dist T_j.direction ((s1 - s0) • T_i.direction) := by
      rw [dist_eq_norm] <;> rfl
    rw [h11] at h10
    rw [T_j.direction_unit, h9] at h10
    linarith
  have h_s_diff_upper : |s1 - s0| ≤ 1 + 4 * δ := by
    have h9 : ‖(s1 - s0) • T_i.direction‖ = |s1 - s0| := by
      rw [norm_smul, T_i.direction_unit] <;> simp
    have h10 : ‖(s1 - s0) • T_i.direction‖ ≤ ‖T_j.direction‖ + ‖(s1 - s0) • T_i.direction - T_j.direction‖ := by
      calc
        ‖(s1 - s0) • T_i.direction‖
          = ‖T_j.direction + ((s1 - s0) • T_i.direction - T_j.direction)‖ := by
            have h_sum : T_j.direction + ((s1 - s0) • T_i.direction - T_j.direction) = (s1 - s0) • T_i.direction := by abel
            rw [h_sum]
        _ ≤ ‖T_j.direction‖ + ‖(s1 - s0) • T_i.direction - T_j.direction‖ := norm_add_le _ _
    have h11 : ‖(s1 - s0) • T_i.direction - T_j.direction‖ = dist T_j.direction ((s1 - s0) • T_i.direction) := by
      have h12 : ‖(s1 - s0) • T_i.direction - T_j.direction‖ = ‖T_j.direction - (s1 - s0) • T_i.direction‖ := by
        have h13 : (s1 - s0) • T_i.direction - T_j.direction = -(T_j.direction - (s1 - s0) • T_i.direction) := by abel
        rw [h13, norm_neg]
      rw [h12, dist_eq_norm] <;> rfl
    rw [h11] at h10
    rw [h9, T_j.direction_unit] at h10
    linarith
  have h11 : |u_j 2 - (s1 - s0)| ≤ 4 * δ := by
    have h_nonneg : 0 ≤ (u_j 0)^2 + (u_j 1)^2 := by positivity
    have h12 : (u_j 2 - (s1 - s0))^2 ≤ (4 * δ)^2 := by linarith [h_dist2, h_nonneg]
    have h_pos : 0 ≤ 4 * δ := by linarith
    exact abs_le_of_sq_le h_pos h12
  have h_sign : (u_j 2 ≥ 1 / 2) ∨ (u_j 2 ≤ -1 / 2) :=
    sign_from_diff_bounds hδ1 h_s_diff_bound h11
  have h_mid_dist : dist m_j (p_i + sm • v) ≤ 2 * δ :=
    midpoint_dist_bound frame p_i v p_j u_j m_j sm hpi hv hpj huj hmj hzm_dist
  have h_sm_lower : -1 / 2 ≤ sm := hsm.1
  have h_sm_upper : sm ≤ 3 / 2 := hsm.2
  have h_final := bounds_from_midpoint hδ hv0 hv1 hv2 h_mid_dist h_sm_lower h_sm_upper
  exact ⟨h_uj0, h_uj1, h_sign, h_final.1, h_final.2.1, h_final.2.2.1, h_final.2.2.2⟩

/--
Variant of `close_params_not_distinct` for coarse conflict degree:
allows larger transverse direction bound (10δ) in exchange for tighter
longitudinal midpoint bound (1/6400 instead of 1/3200).
-/
lemma close_params_not_distinct_coarse
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    {T1 T2 : Kakeya.DeltaTube δ}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (m1 m2 u1 u2 : Point3)
    (hm1 : m1 = frame.symm (T1.base + (1 / 2 : ℝ) • T1.direction))
    (hm2 : m2 = frame.symm (T2.base + (1 / 2 : ℝ) • T2.direction))
    (hu1 : u1 = frame.symm.linearIsometryEquiv T1.direction)
    (hu2 : u2 = frame.symm.linearIsometryEquiv T2.direction)
    (hu1_pos : u1 2 ≥ 1 / 2)
    (hu2_pos : u2 2 ≥ 1 / 2)
    (h_u2_0 : |u2 0| ≤ 10 * δ)
    (h_u2_1 : |u2 1| ≤ 10 * δ)
    (h_m0 : |(m1 - m2) 0| ≤ δ / 200)
    (h_m1 : |(m1 - m2) 1| ≤ δ / 200)
    (h_m2 : |(m1 - m2) 2| ≤ 1 / 6400)
    (h_u0 : |(u1 - u2) 0| ≤ δ / 200)
    (h_u1 : |(u1 - u2) 1| ≤ δ / 200)
    (h_capsule_lower : CapsuleLowerBound)
    (h_capsule_upper : CapsuleUpperBound) :
    ¬ T1.EssentiallyDistinct T2 := by
  let b1 := m1 - (1 / 2 : ℝ) • u1
  let b2 := m2 - (1 / 2 : ℝ) • u2
  let z0 := m1 2
  let t1 : ℝ := 1 / 2
  let t2 : ℝ := (z0 - b2 2) / u2 2
  let q1 := b1 + t1 • u1
  let q2 := b2 + t2 • u2

  have h_u2_pos' : 0 < u2 2 := by linarith
  let e := frame.symm
  have h_affine1 : e (T1.base + (1 / 2 : ℝ) • T1.direction) =
      e T1.base + (1 / 2 : ℝ) • e.linearIsometryEquiv T1.direction := by
    have h_vadd := e.map_vadd T1.base ((1 / 2 : ℝ) • T1.direction)
    have h1 : ((1 / 2 : ℝ) • T1.direction +ᵥ T1.base) = T1.base + (1 / 2 : ℝ) • T1.direction := by
      simp [vadd_eq_add] <;> abel
    have h_smul : e.linearIsometryEquiv ((1 / 2 : ℝ) • T1.direction) =
        (1 / 2 : ℝ) • e.linearIsometryEquiv T1.direction :=
      e.linearIsometryEquiv.map_smul (1 / 2 : ℝ) T1.direction
    simpa [h1, vadd_eq_add, h_smul, add_comm] using h_vadd
  have h_affine2 : e (T2.base + (1 / 2 : ℝ) • T2.direction) =
      e T2.base + (1 / 2 : ℝ) • e.linearIsometryEquiv T2.direction := by
    have h_vadd := e.map_vadd T2.base ((1 / 2 : ℝ) • T2.direction)
    have h1 : ((1 / 2 : ℝ) • T2.direction +ᵥ T2.base) = T2.base + (1 / 2 : ℝ) • T2.direction := by
      simp [vadd_eq_add] <;> abel
    have h_smul : e.linearIsometryEquiv ((1 / 2 : ℝ) • T2.direction) =
        (1 / 2 : ℝ) • e.linearIsometryEquiv T2.direction :=
      e.linearIsometryEquiv.map_smul (1 / 2 : ℝ) T2.direction
    simpa [h1, vadd_eq_add, h_smul, add_comm] using h_vadd
  have hb1 : b1 = frame.symm T1.base := by
    have h : m1 = e T1.base + (1 / 2 : ℝ) • u1 := by
      have h_step1 : m1 = e (T1.base + (1 / 2 : ℝ) • T1.direction) := hm1
      rw [h_step1, h_affine1, hu1]
    have h2 : b1 = m1 - (1 / 2 : ℝ) • u1 := by rfl
    rw [h2, h] <;> abel
  have hb2 : b2 = frame.symm T2.base := by
    have h : m2 = e T2.base + (1 / 2 : ℝ) • u2 := by
      have h_step1 : m2 = e (T2.base + (1 / 2 : ℝ) • T2.direction) := hm2
      rw [h_step1, h_affine2, hu2]
    have h2 : b2 = m2 - (1 / 2 : ℝ) • u2 := by rfl
    rw [h2, h] <;> abel
  have hq1_eq : q1 = m1 := by
    have h2 : q1 = b1 + (1 / 2 : ℝ) • u1 := by rfl
    have h3 : b1 = m1 - (1 / 2 : ℝ) • u1 := by rfl
    rw [h2, h3] <;> abel
  have h_b22 : b2 2 = m2 2 - (1 / 2 : ℝ) * u2 2 := by
    have h : b2 = m2 - (1 / 2 : ℝ) • u2 := by rfl
    rw [h]
    simp [Pi.sub_apply, Pi.smul_apply] <;> ring
  have h_z0 : z0 = m1 2 := by rfl
  have h_t2_form : t2 = (m1 2 - m2 2) / u2 2 + 1 / 2 := by
    have h : t2 = (z0 - b2 2) / u2 2 := by rfl
    rw [h, h_z0, h_b22]
    field_simp [h_u2_pos'.ne'] <;> ring
  have h_q2_2 : q2 2 = z0 := by
    have h : q2 2 = b2 2 + t2 * u2 2 := by
      have hq : q2 = b2 + t2 • u2 := by rfl
      rw [hq]
      simp [Pi.add_apply, Pi.smul_apply] <;> ring
    have h2 : t2 * u2 2 = z0 - b2 2 := by
      have h3 : t2 = (z0 - b2 2) / u2 2 := by rfl
      rw [h3]
      field_simp [h_u2_pos'.ne'] <;> ring
    linarith [h, h2]
  have h_tdiff_eq : t2 - 1 / 2 = (m1 2 - m2 2) / u2 2 := by
    rw [h_t2_form] <;> ring
  have h_m2' : |m1 2 - m2 2| ≤ 1 / 6400 := by
    have h_eq : m1 2 - m2 2 = (m1 - m2) 2 := by
      simp [Pi.sub_apply] <;> ring
    rw [h_eq]
    exact h_m2
  have h_tdiff_bound : |t2 - 1 / 2| ≤ 1 / 3200 := by
    rw [h_tdiff_eq]
    have h_abs : |(m1 2 - m2 2) / u2 2| = |m1 2 - m2 2| / |u2 2| := by rw [abs_div]
    rw [h_abs]
    have h3 : |u2 2| = u2 2 := by rw [abs_of_pos] <;> linarith
    rw [h3]
    have h4 : 0 < u2 2 := h_u2_pos'
    have h5 : |m1 2 - m2 2| / u2 2 ≤ (1 / 6400 : ℝ) / u2 2 := by
      apply div_le_div_of_nonneg_right h_m2' (by linarith)
    have h6 : (1 / 6400 : ℝ) / u2 2 ≤ (1 / 6400 : ℝ) / (1 / 2 : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    linarith
  have h_tdiff : |t1 - t2| ≤ 1 / 8 := by
    have h : |t1 - t2| = |t2 - 1 / 2| := by
      have h4 : t1 = (1 / 2 : ℝ) := by rfl
      rw [h4, abs_sub_comm]
    rw [h]
    linarith [h_tdiff_bound]
  have h2_abs : |(m1 2 - m2 2) / u2 2| ≤ 1 / 3200 := by
    have h_eq : (m1 2 - m2 2) / u2 2 = t2 - 1 / 2 := h_tdiff_eq.symm
    simpa [h_eq] using h_tdiff_bound
  have ht2_in : t2 ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : t2 = 1 / 2 + (m1 2 - m2 2) / u2 2 := by linarith [h_t2_form]
    rw [h1]
    have h_bounds := abs_le.mp h2_abs
    have h_pos : -1 / 3200 ≤ (m1 2 - m2 2) / u2 2 := by linarith [h_bounds.1]
    have h_neg : (m1 2 - m2 2) / u2 2 ≤ 1 / 3200 := by linarith [h_bounds.2]
    constructor <;> linarith
  have hq2_eq : q2 = m2 + (t2 - 1 / 2 : ℝ) • u2 := by
    have h1 : q2 = b2 + t2 • u2 := by rfl
    have h2 : b2 = m2 - (1 / 2 : ℝ) • u2 := by rfl
    rw [h1, h2]
    ext i
    fin_cases i <;> simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] <;> ring
  have h_q2_0 : |(q1 - q2) 0| ≤ δ / 100 := by
    have h_eq : (q1 - q2) 0 = (m1 - m2) 0 - (t2 - 1 / 2) * u2 0 := by
      rw [hq1_eq, hq2_eq]
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h_eq]
    have h_tri : |(m1 - m2) 0 - (t2 - 1 / 2) * u2 0| ≤
        |(m1 - m2) 0| + |(t2 - 1 / 2) * u2 0| := by
      calc
        |(m1 - m2) 0 - (t2 - 1 / 2) * u2 0|
          ≤ |(m1 - m2) 0| + |-((t2 - 1 / 2) * u2 0)| := by
            simpa only [abs_neg] using
              abs_sub ((m1 - m2) 0) ((t2 - 1 / 2) * u2 0)
        _ = |(m1 - m2) 0| + |(t2 - 1 / 2) * u2 0| := by rw [abs_neg]
    have h_abs_mul : |(t2 - 1 / 2) * u2 0| = |t2 - 1 / 2| * |u2 0| := by rw [abs_mul]
    rw [h_abs_mul] at h_tri
    have h_main : |(m1 - m2) 0| + |t2 - 1 / 2| * |u2 0| ≤ δ / 200 + (1 / 3200 : ℝ) * (10 * δ) := by
      gcongr <;> linarith
    have h_final : δ / 200 + (1 / 3200 : ℝ) * (10 * δ) ≤ δ / 100 := by
      ring_nf
      <;> linarith
    linarith [h_tri, h_main, h_final]
  have h_q2_1 : |(q1 - q2) 1| ≤ δ / 100 := by
    have h_eq : (q1 - q2) 1 = (m1 - m2) 1 - (t2 - 1 / 2) * u2 1 := by
      rw [hq1_eq, hq2_eq]
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h_eq]
    have h_tri : |(m1 - m2) 1 - (t2 - 1 / 2) * u2 1| ≤
        |(m1 - m2) 1| + |(t2 - 1 / 2) * u2 1| := by
      calc
        |(m1 - m2) 1 - (t2 - 1 / 2) * u2 1|
          ≤ |(m1 - m2) 1| + |-((t2 - 1 / 2) * u2 1)| := by
            simpa only [abs_neg] using
              abs_sub ((m1 - m2) 1) ((t2 - 1 / 2) * u2 1)
        _ = |(m1 - m2) 1| + |(t2 - 1 / 2) * u2 1| := by rw [abs_neg]
    have h_abs_mul : |(t2 - 1 / 2) * u2 1| = |t2 - 1 / 2| * |u2 1| := by rw [abs_mul]
    rw [h_abs_mul] at h_tri
    have h_main : |(m1 - m2) 1| + |t2 - 1 / 2| * |u2 1| ≤ δ / 200 + (1 / 3200 : ℝ) * (10 * δ) := by
      gcongr <;> linarith
    have h_final : δ / 200 + (1 / 3200 : ℝ) * (10 * δ) ≤ δ / 100 := by
      ring_nf <;> linarith
    linarith [h_tri, h_main, h_final]
  have h_dir0' : |(u1 - u2) 0| ≤ δ / 100 := by
    calc
      |(u1 - u2) 0| ≤ δ / 200 := h_u0
      _ ≤ δ / 100 := by linarith
  have h_dir1' : |(u1 - u2) 1| ≤ δ / 100 := by
    calc
      |(u1 - u2) 1| ≤ δ / 200 := h_u1
      _ ≤ δ / 100 := by linarith
  have h_plane : q1 2 = q2 2 := by
    have h_q1_2 : q1 2 = z0 := by
      rw [hq1_eq, h_z0]
    rw [h_q1_2, h_q2_2]
  exact close_axial_tubes_not_distinct hδ (by linarith) frame
    b1 u1 b2 u2 q1 q2 t1 t2
    hb1 hu1 hb2 hu2
    (by norm_num) ht2_in
    (by simp [q1, b1]) (by simp [q2, b2])
    h_plane h_q2_0 h_q2_1 h_tdiff h_dir0' h_dir1'
    hu1_pos hu2_pos h_capsule_lower h_capsule_upper

end Kakeya.Assouad

end
