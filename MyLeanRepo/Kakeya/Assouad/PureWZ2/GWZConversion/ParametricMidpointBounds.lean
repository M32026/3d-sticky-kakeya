import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DirectionConstraint
import Mathlib.Tactic

set_option linter.constructorNameAsVariable false

/-!
# Parametric midpoint bounds for conflict degree

Generalizes the midpoint bound to take an arbitrary direction transverse bound
`D_dir`. When directions are tightly clustered (D_dir = O(ρ₀)), the midpoint
transverse bound becomes O(Bρ₀) instead of O(B²ρ₀).

This is the key geometric lemma enabling the O(B⁵) conflict degree bound
via direction partition: O(B²) blocks × O(B³) per block = O(B⁵).
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined Metric Set InnerProductSpace

/-- Helper: |component i of x| ≤ ‖x‖. -/
private lemma component_abs_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h1 : ‖x‖ ^ 2 = ∑ j : Fin 3, (x j)^2 := EuclideanSpace.real_norm_sq_eq x
  have h2 : (x i)^2 ≤ ∑ j : Fin 3, (x j)^2 := by
    apply Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have h3 : (x i)^2 ≤ ‖x‖ ^ 2 := by linarith
  have h4 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
    have h5 : |x i| ^ 2 = (x i)^2 := by simp [sq_abs]
    rw [h5]; exact h3
  have h6 : 0 ≤ |x i| := by positivity
  have h7 : 0 ≤ ‖x‖ := by positivity
  nlinarith

/-- Helper: affine map applied to p + t•v. -/
private lemma affine_apply (e : Point3 ≃ᵃⁱ[ℝ] Point3) (p : Point3) (t : ℝ) (v : Point3) :
    e (p + t • v) = e p + t • e.linearIsometryEquiv v := by
  have h_vadd := e.toAffineMap.map_vadd p (t • v)
  have h1 : (t • v) +ᵥ p = p + t • v := by simp [vadd_eq_add] <;> abel
  have h_smul : e.linearIsometryEquiv (t • v) = t • e.linearIsometryEquiv v :=
    e.linearIsometryEquiv.map_smul t v
  simpa [h1, vadd_eq_add, h_smul, add_comm] using h_vadd

/-- If x ∈ B-dilated carrier of T, there exists a point on the B-extended segment
within distance B*ρ of x. -/
lemma general_dilation_closest_point
    {ρ : ℝ} (hρ : 0 ≤ ρ) {B : ℝ} (hB : 0 < B) (T : Kakeya.DeltaTube ρ) (x : Point3)
    (hx : x ∈ wz2PaperCenteredDilatedCarrier B T) :
    ∃ (t : ℝ), t ∈ Set.Icc (1 / 2 - B / 2) (1 / 2 + B / 2) ∧
      dist x (T.base + t • T.direction) ≤ B * ρ := by
  let m := T.base + (1 / 2 : ℝ) • T.direction
  let h_hom : Point3 → Point3 := AffineMap.homothety m B
  let S_unit := (fun s : ℝ => T.base + s • T.direction) '' Set.Icc (0 : ℝ) 1
  rcases hx with ⟨y, hy, rfl⟩
  have h_ne : S_unit.Nonempty := ⟨T.base, ⟨0, by norm_num, by simp⟩⟩
  have hy_dist : Metric.infDist y S_unit ≤ ρ := by
    have h1 : Metric.infEDist y S_unit ≤ ENNReal.ofReal ρ := Metric.mem_cthickening_iff.mp hy
    have h2 : Metric.infDist y S_unit = ENNReal.toReal (Metric.infEDist y S_unit) := by rfl
    rw [h2]
    exact ENNReal.toReal_le_of_le_ofReal hρ h1
  have h_cp : IsCompact S_unit := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  rcases h_cp.exists_infDist_eq_dist h_ne y with ⟨z, hz, hz_eq⟩
  have h_yz : dist y z ≤ ρ := by rw [←hz_eq]; exact hy_dist
  rcases hz with ⟨t, ht, rfl⟩
  let t' := B * t - B / 2 + 1 / 2
  have ht'_range : t' ∈ Set.Icc (1 / 2 - B / 2) (1 / 2 + B / 2) := by
    have h_t_nonneg : 0 ≤ t := ht.1
    have h_t_le_one : t ≤ 1 := ht.2
    have h1 : 1 / 2 - B / 2 ≤ B * t - B / 2 + 1 / 2 := by nlinarith
    have h2 : B * t - B / 2 + 1 / 2 ≤ 1 / 2 + B / 2 := by nlinarith
    exact ⟨h1, h2⟩
  have h_hom_eq : ∀ (x : Point3), h_hom x = B • (x - m) + m := by
    intro x; simpa [vadd_eq_add, vsub_eq_sub] using AffineMap.homothety_apply m B x
  have h_z'_form : h_hom (T.base + t • T.direction) = T.base + t' • T.direction := by
    rw [h_hom_eq]
    have h2 : (T.base + t • T.direction) - m = (t - 1 / 2 : ℝ) • T.direction := by
      have hm : m = T.base + (1 / 2 : ℝ) • T.direction := by rfl
      rw [hm]; simp [sub_smul] <;> abel
    rw [h2, smul_smul]
    have hm : m = T.base + (1 / 2 : ℝ) • T.direction := by rfl
    rw [hm]
    have h4 : (B * (t - 1 / 2)) • T.direction + (T.base + (1 / 2 : ℝ) • T.direction) =
        T.base + ((B * (t - 1 / 2) + 1 / 2) • T.direction) := by
      rw [add_comm, add_assoc, ←add_smul] <;> abel
    rw [h4]
    have h5 : B * (t - 1 / 2) + 1 / 2 = t' := by simp [t'] <;> ring
    rw [h5]
  have h_hom_dist : dist (h_hom y) (h_hom (T.base + t • T.direction)) =
      B * dist y (T.base + t • T.direction) := by
    let vdiff : Point3 := y - (T.base + t • T.direction)
    have h1 : h_hom y - h_hom (T.base + t • T.direction) = B • vdiff := by
      have h_eq1 : h_hom y = B • (y - m) + m := h_hom_eq y
      have h_eq2 : h_hom (T.base + t • T.direction) = B • ((T.base + t • T.direction) - m) + m := h_hom_eq (T.base + t • T.direction)
      rw [h_eq1, h_eq2]
      have h_sub : (B • (y - m) + m) - (B • ((T.base + t • T.direction) - m) + m) =
          B • (y - m) - B • ((T.base + t • T.direction) - m) := by abel
      rw [h_sub]
      have h_smul : B • (y - m) - B • ((T.base + t • T.direction) - m) =
          B • ((y - m) - ((T.base + t • T.direction) - m)) := by
        rw [←smul_sub] <;> rfl
      rw [h_smul]
      have h_abel : (y - m) - ((T.base + t • T.direction) - m) = y - (T.base + t • T.direction) := by abel
      rw [h_abel] <;> rfl
    calc
      dist (h_hom y) (h_hom (T.base + t • T.direction))
        = ‖h_hom y - h_hom (T.base + t • T.direction)‖ := by rw [dist_eq_norm]
      _ = ‖B • vdiff‖ := by rw [h1]
      _ = |B| * ‖vdiff‖ := by rw [norm_smul] <;> rfl
      _ = B * ‖vdiff‖ := by rw [abs_of_pos hB]
      _ = B * dist y (T.base + t • T.direction) := by rw [dist_eq_norm] <;> rfl
  have h_xz' : dist (h_hom y) (h_hom (T.base + t • T.direction)) ≤ B * ρ := by
    rw [h_hom_dist]; exact mul_le_mul_of_nonneg_left h_yz (by linarith)
  rw [h_z'_form] at h_xz'
  exact ⟨t', ht'_range, h_xz'⟩

/-- Parametric midpoint bounds: given direction transverse bound D_dir,
bound midpoint difference transverse by (B/2)*D_dir + 2Bρ₀ and
longitudinal by B + 2Bρ₀. -/
lemma parametric_midpoint_bounds
    {δ ρ₀ B : ℝ} (hδ : 0 < δ) (hρ₀ : 0 < ρ₀)
    (hB : 1 ≤ B) (hBρ : B * ρ₀ ≤ 1 / 4)
    (hBδ_le : δ ≤ B * ρ₀)
    {S : Kakeya.DeltaTube δ}
    {T_i T_j : Kakeya.DeltaTube ρ₀}
    (hS_i : S.carrier ⊆ wz2PaperCenteredDilatedCarrier B T_i)
    (hS_j : S.carrier ⊆ wz2PaperCenteredDilatedCarrier B T_j)
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (p_i v m_i u_j m_j : Point3)
    (hpi : p_i = frame.symm T_i.base)
    (hv : v = frame.symm.linearIsometryEquiv T_i.direction)
    (hv2 : v 2 = 1) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
    (hmi : m_i = p_i + (1 / 2 : ℝ) • v)
    (huj : u_j = frame.symm.linearIsometryEquiv T_j.direction)
    (hmj : m_j = frame.symm T_j.base + (1 / 2 : ℝ) • u_j)
    (D_dir : ℝ) (hD_dir_nonneg : 0 ≤ D_dir)
    (h_uj0 : |u_j 0| ≤ D_dir)
    (h_uj1 : |u_j 1| ≤ D_dir) :
    (|(m_j - m_i) 0| ≤ (B / 2) * D_dir + 2 * B * ρ₀) ∧
    (|(m_j - m_i) 1| ≤ (B / 2) * D_dir + 2 * B * ρ₀) ∧
    (|(m_j - m_i) 2| ≤ B + 2 * B * ρ₀) := by
  let mS := wz2PaperTubeMidpoint S
  have hmS_in_S : mS ∈ S.carrier := wz2_paper_tubeMidpoint_mem_carrier S hδ.le
  have h1 : mS ∈ wz2PaperCenteredDilatedCarrier B T_i := hS_i hmS_in_S
  have h2 : mS ∈ wz2PaperCenteredDilatedCarrier B T_j := hS_j hmS_in_S

  have hB_pos : 0 < B := by linarith
  rcases general_dilation_closest_point hρ₀.le hB_pos T_i mS h1 with ⟨t_i, hti_range, hdist_i⟩
  rcases general_dilation_closest_point hρ₀.le hB_pos T_j mS h2 with ⟨t_j, htj_range, hdist_j⟩

  let z_i : Point3 := T_i.base + t_i • T_i.direction
  let z_j : Point3 := T_j.base + t_j • T_j.direction
  have h_dist_ij : dist z_i z_j ≤ 2 * B * ρ₀ := by
    calc dist z_i z_j ≤ dist z_i mS + dist mS z_j := dist_triangle z_i mS z_j
      _ = dist mS z_i + dist mS z_j := by rw [dist_comm z_i mS]
      _ ≤ B * ρ₀ + B * ρ₀ := by gcongr
      _ = 2 * B * ρ₀ := by ring

  let z_i' : Point3 := frame.symm z_i
  let z_j' : Point3 := frame.symm z_j
  have h_z_i'_eq : z_i' = p_i + t_i • v := by
    dsimp only [z_i']
    have h := affine_apply frame.symm T_i.base t_i T_i.direction
    rw [h, hpi, hv]
  have h_z_j'_eq : z_j' = frame.symm T_j.base + t_j • u_j := by
    dsimp only [z_j']
    have h := affine_apply frame.symm T_j.base t_j T_j.direction
    rw [h, huj]
  have h_dist' : dist z_i' z_j' ≤ 2 * B * ρ₀ := by
    have h : dist z_i' z_j' = dist z_i z_j := frame.symm.dist_map _ _
    rw [h]; exact h_dist_ij
  have h_diff_norm : ‖z_j' - z_i'‖ ≤ 2 * B * ρ₀ := by
    have h : dist z_i' z_j' = ‖z_j' - z_i'‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    rw [h] at h_dist'; exact h_dist'

  have h_tj_diff : |1 / 2 - t_j| ≤ B / 2 := by
    have h1 : 1 / 2 - B / 2 ≤ t_j := htj_range.1
    have h2 : t_j ≤ 1 / 2 + B / 2 := htj_range.2
    rw [abs_le] <;> constructor <;> linarith
  have h_ti_diff : |t_i - 1 / 2| ≤ B / 2 := by
    have h1 : 1 / 2 - B / 2 ≤ t_i := hti_range.1
    have h2 : t_i ≤ 1 / 2 + B / 2 := hti_range.2
    rw [abs_le] <;> constructor <;> linarith

  have h_decomp : m_j - m_i = (1 / 2 - t_j) • u_j + (z_j' - z_i') + (t_i - 1 / 2) • v := by
    have h1 : m_j - z_j' = (1 / 2 - t_j) • u_j := by
      rw [hmj, h_z_j'_eq] <;> simp [sub_smul, add_smul] <;> abel
    have h2 : z_i' - m_i = (t_i - 1 / 2) • v := by
      rw [hmi, h_z_i'_eq] <;> simp [sub_smul, add_smul] <;> abel
    have h3 : m_j - m_i = (m_j - z_j') + (z_j' - z_i') + (z_i' - m_i) := by abel
    rw [h3, h1, h2] <;> abel

  have h_uj2_abs : |u_j 2| ≤ 1 := by
    have h : |u_j 2| ≤ ‖u_j‖ := component_abs_le_norm u_j 2
    have h2 : ‖u_j‖ = 1 := by
      rw [huj]
      have h3 := frame.symm.linearIsometryEquiv.norm_map T_j.direction
      rw [h3, T_j.direction_unit]
    rw [h2] at h; exact h

  have h_component0 : (m_j - m_i) 0 = (1 / 2 - t_j) * u_j 0 + (z_j' - z_i') 0 := by
    rw [h_decomp]
    simp [Pi.add_apply, Pi.smul_apply, hv0] <;> ring
  have h_component1 : (m_j - m_i) 1 = (1 / 2 - t_j) * u_j 1 + (z_j' - z_i') 1 := by
    rw [h_decomp]
    simp [Pi.add_apply, Pi.smul_apply, hv1] <;> ring
  have h_component2 : (m_j - m_i) 2 = (1 / 2 - t_j) * u_j 2 + (z_j' - z_i') 2 + (t_i - 1 / 2) := by
    rw [h_decomp]
    simp [Pi.add_apply, Pi.smul_apply, hv2] <;> ring

  have h_diff0 : |(z_j' - z_i') 0| ≤ 2 * B * ρ₀ := (component_abs_le_norm (z_j' - z_i') 0).trans h_diff_norm
  have h_diff1 : |(z_j' - z_i') 1| ≤ 2 * B * ρ₀ := (component_abs_le_norm (z_j' - z_i') 1).trans h_diff_norm
  have h_diff2 : |(z_j' - z_i') 2| ≤ 2 * B * ρ₀ := (component_abs_le_norm (z_j' - z_i') 2).trans h_diff_norm

  have h_m0 : |(m_j - m_i) 0| ≤ (B / 2) * D_dir + 2 * B * ρ₀ := by
    rw [h_component0]
    have h : |(1 / 2 - t_j) * u_j 0 + (z_j' - z_i') 0| ≤ |(1 / 2 - t_j) * u_j 0| + |(z_j' - z_i') 0| :=
      abs_add_le _ _
    have h4 : |(1 / 2 - t_j) * u_j 0| ≤ (B / 2) * D_dir := by
      rw [abs_mul]
      have h5 : |1 / 2 - t_j| ≤ B / 2 := h_tj_diff
      have h6 : |u_j 0| ≤ D_dir := h_uj0
      exact mul_le_mul h5 h6 (by positivity) (by linarith)
    linarith
  have h_m1 : |(m_j - m_i) 1| ≤ (B / 2) * D_dir + 2 * B * ρ₀ := by
    rw [h_component1]
    have h : |(1 / 2 - t_j) * u_j 1 + (z_j' - z_i') 1| ≤ |(1 / 2 - t_j) * u_j 1| + |(z_j' - z_i') 1| :=
      abs_add_le _ _
    have h4 : |(1 / 2 - t_j) * u_j 1| ≤ (B / 2) * D_dir := by
      rw [abs_mul]
      have h5 : |1 / 2 - t_j| ≤ B / 2 := h_tj_diff
      have h6 : |u_j 1| ≤ D_dir := h_uj1
      exact mul_le_mul h5 h6 (by positivity) (by linarith)
    linarith
  have h_m2 : |(m_j - m_i) 2| ≤ B + 2 * B * ρ₀ := by
    rw [h_component2]
    have h : |(1 / 2 - t_j) * u_j 2 + (z_j' - z_i') 2 + (t_i - 1 / 2)| ≤
        |(1 / 2 - t_j) * u_j 2| + |(z_j' - z_i') 2| + |t_i - 1 / 2| := by
      calc |(1 / 2 - t_j) * u_j 2 + (z_j' - z_i') 2 + (t_i - 1 / 2)|
        ≤ |(1 / 2 - t_j) * u_j 2 + (z_j' - z_i') 2| + |t_i - 1 / 2| := abs_add_le _ _
      _ ≤ |(1 / 2 - t_j) * u_j 2| + |(z_j' - z_i') 2| + |t_i - 1 / 2| := by
        have h5 : |(1 / 2 - t_j) * u_j 2 + (z_j' - z_i') 2| ≤ |(1 / 2 - t_j) * u_j 2| + |(z_j' - z_i') 2| :=
          abs_add_le _ _
        linarith
    have h4 : |(1 / 2 - t_j) * u_j 2| ≤ B / 2 := by
      rw [abs_mul]
      calc |1 / 2 - t_j| * |u_j 2| ≤ (B / 2) * 1 := by gcongr <;> linarith
        _ = B / 2 := by ring
    linarith
  exact ⟨h_m0, h_m1, h_m2⟩

end Kakeya.Assouad

end
