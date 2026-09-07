import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TightDistinctness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DirectionConstraint
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DilationExt
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnisotropicPacking
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import Mathlib.Tactic

set_option linter.constructorNameAsVariable false

/-!
# Shifted-copy conflict degree bound O(A⁵)

Given an essentially distinct family of ρ₀-tubes and a fixed δ-tube,
bound the number of coarse tubes whose A-dilated carriers contain the fine tube.

The bound is O(A⁵), independent of δ.

## Proof route

1. **Direction net**: In a frame aligned with the fine tube, each coarse direction
   has transverse components ≤ 2Aρ₀. Partition the 2D transverse direction space
   into blocks of size 2ρ₀. Number of blocks: O(A²).

2. **Within each block**: Pick a representative direction and realign the frame.
   All directions in the block have transverse components ≤ 10ρ₀ (constant).
   - Midpoint transverse: ≤ 2Aρ₀ + (A/2)·10ρ₀ = O(A)·ρ₀
   - Midpoint longitudinal: ≤ A + 2Aρ₀ = O(A)

3. **Cell packing**: Within each block, pack 5D parameters (direction transverse
   × midpoint transverse × longitudinal) with cell sizes ρ₀/200 and 1/6400.
   Two tubes in the same cell violate essential distinctness.
   Count per block: O(A³).

4. **Total**: O(A²) blocks × O(A³) = O(A⁵).

## Key lemmas

- `shifted_direction_net_bound`: direction transverse bound in fine frame
- `shifted_within_block_bounds`: geometric bounds within a direction block
- `shifted_copy_conflict_degree`: final O(A⁵) bound
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined Metric Set InnerProductSpace
open Kakeya.Streamlined.GeometricLemmas

/-- Extended segment of a tube for dilation A (length A, centered at midpoint). -/
def shiftedExtendedSegment {δ : ℝ} (A : ℝ) (T : Kakeya.DeltaTube δ) : Set Point3 :=
  (fun s : ℝ => T.base + s • T.direction) '' Set.Icc (-(A - 1) / 2) ((A + 1) / 2)

/-- Points in the A-dilation are within Aδ of the A-extended segment. -/
lemma shifted_dilation_infDist_extended
    {δ : ℝ} (hδ : 0 ≤ δ) {A : ℝ} (hA : 1 ≤ A)
    (T : Kakeya.DeltaTube δ) (x : Point3)
    (hx : x ∈ wz2PaperCenteredDilatedCarrier A T) :
    Metric.infDist x (shiftedExtendedSegment A T) ≤ A * δ := by
  let m := T.base + (1 / 2 : ℝ) • T.direction
  let h_hom : Point3 → Point3 := AffineMap.homothety m A
  let S_ext := shiftedExtendedSegment A T
  let S_unit := (fun s : ℝ => T.base + s • T.direction) '' Set.Icc (0 : ℝ) 1
  rcases hx with ⟨y, hy, rfl⟩
  have h_ne : S_unit.Nonempty := ⟨T.base, ⟨0, by norm_num, by simp⟩⟩
  have hy_dist : Metric.infDist y S_unit ≤ δ := by
    have h1 : Metric.infEDist y S_unit ≤ ENNReal.ofReal δ := Metric.mem_cthickening_iff.mp hy
    have h2 : Metric.infDist y S_unit = ENNReal.toReal (Metric.infEDist y S_unit) := by rfl
    rw [h2]
    exact ENNReal.toReal_le_of_le_ofReal hδ h1
  have h_cp : IsCompact S_unit := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  rcases h_cp.exists_infDist_eq_dist h_ne y with ⟨z, hz, hz_eq⟩
  have h_yz : dist y z ≤ δ := by rw [←hz_eq]; exact hy_dist
  rcases hz with ⟨t, ht, rfl⟩
  have h_hom_eq : ∀ (x : Point3), h_hom x = A • (x - m) + m := by
    intro x; simpa [vadd_eq_add, vsub_eq_sub] using AffineMap.homothety_apply m A x
  have h_z'_form : h_hom (T.base + t • T.direction) =
      T.base + (A * t - (A - 1) / 2) • T.direction := by
    rw [h_hom_eq]
    have h2 : (T.base + t • T.direction) - m = (t - 1 / 2 : ℝ) • T.direction := by
      have hm : m = T.base + (1 / 2 : ℝ) • T.direction := by rfl
      rw [hm]; simp [sub_smul] <;> abel
    rw [h2, smul_smul]
    have h6 : A * (t - 1 / 2) = A * t - A / 2 := by ring
    rw [h6]
    have hm : m = T.base + (1 / 2 : ℝ) • T.direction := by rfl
    rw [hm]
    have h7 : (A * t - A / 2) • T.direction + (T.base + (1 / 2 : ℝ) • T.direction) =
        T.base + ((A * t - A / 2 + 1 / 2) • T.direction) := by
      rw [add_comm, add_assoc, ←add_smul] <;> abel
    rw [h7]
    have h8 : A * t - A / 2 + 1 / 2 = A * t - (A - 1) / 2 := by ring
    rw [h8]
  have h_z'_in : h_hom (T.base + t • T.direction) ∈ S_ext := by
    rw [h_z'_form]
    have h_t0 : 0 ≤ t := ht.1
    have h_t1 : t ≤ 1 := ht.2
    have h_lower : -(A - 1) / 2 ≤ A * t - (A - 1) / 2 := by
      have h : A * t ≥ 0 := by positivity
      linarith
    have h_upper : A * t - (A - 1) / 2 ≤ (A + 1) / 2 := by
      have h : A * t ≤ A := by
        exact mul_le_of_le_one_right (by linarith) h_t1
      linarith
    exact ⟨A * t - (A - 1) / 2, ⟨h_lower, h_upper⟩, rfl⟩
  have h_hom_dist : dist (h_hom y) (h_hom (T.base + t • T.direction)) = A * dist y (T.base + t • T.direction) := by
    have h1 : h_hom y - h_hom (T.base + t • T.direction) = A • (y - (T.base + t • T.direction)) := by
      rw [h_hom_eq y, h_hom_eq (T.base + t • T.direction)]
      simp [smul_sub] <;> abel
    calc
      dist (h_hom y) (h_hom (T.base + t • T.direction))
        = ‖h_hom y - h_hom (T.base + t • T.direction)‖ := by rw [dist_eq_norm]
      _ = ‖A • (y - (T.base + t • T.direction))‖ := by rw [h1]
      _ = ‖A‖ * ‖y - (T.base + t • T.direction)‖ := by rw [norm_smul]
      _ = |A| * ‖y - (T.base + t • T.direction)‖ := by simp
      _ = A * ‖y - (T.base + t • T.direction)‖ := by
        have hApos : 0 ≤ A := by linarith
        rw [abs_of_nonneg hApos]
      _ = A * dist y (T.base + t • T.direction) := by rw [dist_eq_norm] <;> ring
  have h_xz' : dist (h_hom y) (h_hom (T.base + t • T.direction)) ≤ A * δ := by
    rw [h_hom_dist]; exact mul_le_mul_of_nonneg_left h_yz (by linarith)
  exact (Metric.infDist_le_dist_of_mem h_z'_in).trans h_xz'

/-- If infDist from a point to shiftedExtendedSegment is bounded, there exists
t ∈ [-A/2, A/2] realizing the bound. -/
lemma shifted_infDist_attained
    {δ A : ℝ} {T : Kakeya.DeltaTube δ} {p : Point3}
    (hA : 1 ≤ A) (h : Metric.infDist p (shiftedExtendedSegment A T) ≤ A * δ) :
    ∃ (t : ℝ), t ∈ Set.Icc (-(A / 2)) (A / 2) ∧
      dist p (wz2PaperTubeMidpoint T + t • T.direction) ≤ A * δ := by
  have h_compact : IsCompact (shiftedExtendedSegment A T) := by
    apply IsCompact.image isCompact_Icc
    continuity
  have h_nonempty : (shiftedExtendedSegment A T).Nonempty := by
    refine ⟨wz2PaperTubeMidpoint T, ?_⟩
    have h10 : (1 / 2 : ℝ) ∈ Set.Icc (-(A - 1) / 2) ((A + 1) / 2) := by
      have h11 : -(A - 1) / 2 ≤ 1 / 2 := by linarith
      have h12 : 1 / 2 ≤ (A + 1) / 2 := by linarith
      exact ⟨h11, h12⟩
    exact ⟨1 / 2, h10, by simp [wz2PaperTubeMidpoint]⟩
  rcases h_compact.exists_infDist_eq_dist h_nonempty p with ⟨q, hq, h_eq⟩
  have h_dist : dist p q ≤ A * δ := by rw [←h_eq]; exact h
  rcases hq with ⟨s, hs, rfl⟩
  set t : ℝ := s - 1 / 2 with ht_def
  have h11 : -(A - 1) / 2 ≤ s := hs.1
  have h12 : s ≤ (A + 1) / 2 := hs.2
  have h13 : -(A / 2) ≤ t := by rw [ht_def]; linarith
  have h14 : t ≤ A / 2 := by rw [ht_def]; linarith
  have ht : t ∈ Set.Icc (-(A / 2)) (A / 2) := ⟨h13, h14⟩
  have h_eq2 : T.base + s • T.direction = wz2PaperTubeMidpoint T + t • T.direction := by
    have h15 : t = s - 1 / 2 := ht_def
    have h16 : wz2PaperTubeMidpoint T = T.base + (1 / 2 : ℝ) • T.direction := by rfl
    rw [h16, h15]
    have h17 : (1 / 2 : ℝ) • T.direction + (s - 1 / 2) • T.direction = s • T.direction := by
      rw [←add_smul] <;> congr <;> ring
    have h18 : (T.base + (1 / 2 : ℝ) • T.direction) + (s - 1 / 2) • T.direction = T.base + s • T.direction := by
      calc (T.base + (1 / 2 : ℝ) • T.direction) + (s - 1 / 2) • T.direction
        = T.base + ((1 / 2 : ℝ) • T.direction + (s - 1 / 2) • T.direction) := by rw [add_assoc]
      _ = T.base + s • T.direction := by rw [h17]
    exact h18.symm
  have h_dist2 : dist p (wz2PaperTubeMidpoint T + t • T.direction) ≤ A * δ := by
    rw [←h_eq2]; exact h_dist
  exact ⟨t, ht, h_dist2⟩

/-- Component absolute value ≤ norm. -/
private lemma shifted_component_abs_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h_i2_le : (x i)^2 ≤ ‖x‖^2 := by
    have h2 : ‖x‖^2 = ∑ j : Fin 3, (x j)^2 := EuclideanSpace.real_norm_sq_eq x
    rw [h2]
    have h3 : (x i)^2 ≤ ∑ j : Fin 3, (x j)^2 := by
      apply Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
    exact h3
  have h4 : |x i|^2 ≤ ‖x‖^2 := by
    have h5 : |x i|^2 = (x i)^2 := by rw [sq_abs]
    rw [h5]; exact h_i2_le
  have h6 : 0 ≤ |x i| := by positivity
  have h7 : 0 ≤ ‖x‖ := by positivity
  nlinarith

/-- Helper: point3 norm squared. -/
private lemma shifted_point3_norm_sq (x : Point3) :
    ‖x‖^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
  have h2 : ‖x‖^2 = ∑ j : Fin 3, (x j)^2 := EuclideanSpace.real_norm_sq_eq x
  rw [h2]
  have h3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [h3]
  simp [Finset.sum_insert, Finset.sum_singleton] <;> ring

/-- Direction transverse bound in fine frame for dilation A. -/
lemma shifted_direction_bound
    {δ ρ₀ A : ℝ} (hδ : 0 < δ) (hρ₀ : 0 < ρ₀) (hA : 1 ≤ A)
    (hρ₀_small : ρ₀ ≤ 1 / (200 * A))
    (hδle : δ ≤ A * ρ₀)
    {fineTube : Kakeya.DeltaTube δ} {coarseTube : Kakeya.DeltaTube ρ₀}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (v u : Point3)
    (hv : v = frame.symm.linearIsometryEquiv fineTube.direction)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0)
    (hu : u = frame.symm.linearIsometryEquiv coarseTube.direction)
    (h : fineTube.carrier ⊆ wz2PaperCenteredDilatedCarrier A coarseTube) :
    |u 0| ≤ 2 * A * ρ₀ ∧ |u 1| ≤ 2 * A * ρ₀ ∧
    ((u 2 ≥ 1 / 2) ∨ (u 2 ≤ -1 / 2)) := by
  have h_perp_fine : ‖fineTube.direction -
      inner ℝ fineTube.direction coarseTube.direction • coarseTube.direction‖ ≤
      2 * (A * ρ₀ - δ) :=
    gwz_direction_constraint hδ hρ₀ hA hδle fineTube coarseTube h
  let a := inner ℝ coarseTube.direction fineTube.direction
  have h_symm : ‖coarseTube.direction - a • fineTube.direction‖ =
      ‖fineTube.direction - a • coarseTube.direction‖ := by
    have h1 : ‖fineTube.direction - a • coarseTube.direction‖^2 = 1 - a^2 := by
      have h_expand : ‖fineTube.direction - a • coarseTube.direction‖^2 =
          ‖fineTube.direction‖^2 - 2 * inner ℝ fineTube.direction (a • coarseTube.direction) +
          ‖a • coarseTube.direction‖^2 :=
        norm_sub_sq_real (F := Point3) fineTube.direction (a • coarseTube.direction)
      rw [h_expand]
      have h_inner : inner ℝ fineTube.direction (a • coarseTube.direction) = a^2 := by
        have h_comm : inner ℝ fineTube.direction coarseTube.direction = a := by
          exact real_inner_comm coarseTube.direction fineTube.direction
        rw [inner_smul_right, h_comm] <;> ring
      have h_norm_smul : ‖a • coarseTube.direction‖^2 = a^2 := by
        rw [norm_smul, coarseTube.direction_unit] <;> simp [Real.norm_eq_abs] <;> ring
      rw [h_inner, h_norm_smul, fineTube.direction_unit] <;> ring
    have h2 : ‖coarseTube.direction - a • fineTube.direction‖^2 = 1 - a^2 := by
      have h_expand : ‖coarseTube.direction - a • fineTube.direction‖^2 =
          ‖coarseTube.direction‖^2 - 2 * inner ℝ coarseTube.direction (a • fineTube.direction) +
          ‖a • fineTube.direction‖^2 :=
        norm_sub_sq_real (F := Point3) coarseTube.direction (a • fineTube.direction)
      rw [h_expand]
      have h_inner : inner ℝ coarseTube.direction (a • fineTube.direction) = a^2 := by
        have h_comm : inner ℝ coarseTube.direction fineTube.direction = a := by rfl
        rw [inner_smul_right, h_comm] <;> ring
      have h_norm_smul : ‖a • fineTube.direction‖^2 = a^2 := by
        rw [norm_smul, fineTube.direction_unit] <;> simp [Real.norm_eq_abs] <;> ring
      rw [h_inner, h_norm_smul, coarseTube.direction_unit] <;> ring
    have h3 : 0 ≤ ‖fineTube.direction - a • coarseTube.direction‖ := by positivity
    have h4 : 0 ≤ ‖coarseTube.direction - a • fineTube.direction‖ := by positivity
    nlinarith
  have h_eq_a : inner ℝ fineTube.direction coarseTube.direction = a :=
    real_inner_comm coarseTube.direction fineTube.direction
  have h_perp : ‖coarseTube.direction - a • fineTube.direction‖ ≤ 2 * (A * ρ₀ - δ) := by
    have h5 : ‖fineTube.direction - inner ℝ fineTube.direction coarseTube.direction • coarseTube.direction‖ ≤ 2 * (A * ρ₀ - δ) := h_perp_fine
    rw [h_eq_a] at h5
    rw [h_symm]
    exact h5
  have h_le : 2 * (A * ρ₀ - δ) ≤ 2 * A * ρ₀ := by linarith
  have h_dir_bound : ‖coarseTube.direction - a • fineTube.direction‖ ≤ 2 * A * ρ₀ :=
    h_perp.trans h_le
  let u_perp : Point3 := u - inner ℝ u v • v
  have h_inner_eq : inner ℝ u v = inner ℝ coarseTube.direction fineTube.direction := by
    rw [hu, hv]
    exact frame.symm.linearIsometryEquiv.inner_map_map coarseTube.direction fineTube.direction
  have h_u_perp_eq : u_perp = frame.symm.linearIsometryEquiv
      (coarseTube.direction - inner ℝ coarseTube.direction fineTube.direction • fineTube.direction) := by
    have h_step1 : u_perp = u - (inner ℝ coarseTube.direction fineTube.direction) • v := by
      dsimp only [u_perp]
      rw [h_inner_eq] <;> rfl
    rw [h_step1, hu, hv]
    have h_map : frame.symm.linearIsometryEquiv coarseTube.direction -
        (inner ℝ coarseTube.direction fineTube.direction) • frame.symm.linearIsometryEquiv fineTube.direction =
        frame.symm.linearIsometryEquiv (coarseTube.direction -
          inner ℝ coarseTube.direction fineTube.direction • fineTube.direction) := by
      rw [map_sub, map_smul] <;> rfl
    exact h_map
  have h_u_perp_norm : ‖u_perp‖ ≤ 2 * A * ρ₀ := by
    rw [h_u_perp_eq]
    have h2 : ‖frame.symm.linearIsometryEquiv (coarseTube.direction - inner ℝ coarseTube.direction fineTube.direction • fineTube.direction)‖ =
        ‖coarseTube.direction - inner ℝ coarseTube.direction fineTube.direction • fineTube.direction‖ :=
      frame.symm.linearIsometryEquiv.norm_map _
    rw [h2]; exact h_dir_bound
  have h_u0 : |u 0| ≤ 2 * A * ρ₀ := by
    have h_eq : u_perp 0 = u 0 := by
      simp [u_perp, Pi.sub_apply, Pi.smul_apply, hv0] <;> ring
    rw [←h_eq]; exact (shifted_component_abs_le_norm u_perp 0).trans h_u_perp_norm
  have h_u1 : |u 1| ≤ 2 * A * ρ₀ := by
    have h_eq : u_perp 1 = u 1 := by
      simp [u_perp, Pi.sub_apply, Pi.smul_apply, hv1] <;> ring
    rw [←h_eq]; exact (shifted_component_abs_le_norm u_perp 1).trans h_u_perp_norm
  have h_u_norm : ‖u‖ = 1 := by
    rw [hu]
    have h := frame.symm.linearIsometryEquiv.norm_map coarseTube.direction
    rw [h, coarseTube.direction_unit]
  have h1 : ‖u‖^2 = (u 0)^2 + (u 1)^2 + (u 2)^2 := shifted_point3_norm_sq u
  have h4 : (u 0)^2 ≤ (2 * A * ρ₀)^2 := by
    have h5 : |u 0| ≤ 2 * A * ρ₀ := h_u0
    have h6 : (u 0)^2 = |u 0|^2 := by rw [sq_abs]
    rw [h6]; gcongr
  have h7 : (u 1)^2 ≤ (2 * A * ρ₀)^2 := by
    have h8 : |u 1| ≤ 2 * A * ρ₀ := h_u1
    have h9 : (u 1)^2 = |u 1|^2 := by rw [sq_abs]
    rw [h9]; gcongr
  have h_u2_sq : (u 2)^2 ≥ 1 - 2 * (2 * A * ρ₀)^2 := by
    have h_eq : (u 0)^2 + (u 1)^2 + (u 2)^2 = 1 := by
      linarith [h1, show ‖u‖^2 = 1 from by rw [h_u_norm] <;> norm_num]
    linarith
  have h10 : 2 * (2 * A * ρ₀)^2 ≤ 3 / 4 := by
    have h11 : 2 * A * ρ₀ ≤ 1 / 2 := by
      have h12 : ρ₀ ≤ 1 / (4 * A) := by
        have h13 : 1 / (200 * A) ≤ 1 / (4 * A) := by
          have h14 : 0 < A := by linarith
          have h15 : 4 * A ≤ 200 * A := by linarith
          exact one_div_le_one_div_of_le (by positivity) h15
        linarith [hρ₀_small, h13]
      have h14 : 0 < A := by linarith
      calc 2 * A * ρ₀
        ≤ 2 * A * (1 / (4 * A)) := by gcongr
      _ = 1 / 2 := by
        field_simp [h14.ne'] <;> ring
    nlinarith
  have h12 : (u 2)^2 ≥ 1 / 4 := by linarith
  have h13 : |u 2| ≥ 1 / 2 := by
    have h14 : |u 2|^2 ≥ (1 / 2 : ℝ)^2 := by
      have h15 : |u 2|^2 = (u 2)^2 := by rw [sq_abs]
      rw [h15]; linarith
    have h16 : 0 ≤ |u 2| := by positivity
    nlinarith
  have h17 : u 2 ≥ 1 / 2 ∨ u 2 ≤ -1 / 2 := by
    by_cases hpos : 0 ≤ u 2
    · have h' : |u 2| = u 2 := abs_of_nonneg hpos
      rw [h'] at h13; exact Or.inl h13
    · have hneg : u 2 < 0 := by linarith
      have h' : |u 2| = -u 2 := abs_of_neg hneg
      rw [h'] at h13; exact Or.inr (by linarith)
  exact ⟨h_u0, h_u1, h17⟩

/-- Reflection function: negate z-coordinate. -/
private def shiftedZReflectFun (p : Point3) : Point3 :=
  p - (2 * (p 2)) • (EuclideanSpace.single 2 1)

@[simp] private lemma shiftedZReflectFun_0 (p : Point3) : (shiftedZReflectFun p) 0 = p 0 := by
  simp [shiftedZReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring
@[simp] private lemma shiftedZReflectFun_1 (p : Point3) : (shiftedZReflectFun p) 1 = p 1 := by
  simp [shiftedZReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring
@[simp] private lemma shiftedZReflectFun_2 (p : Point3) : (shiftedZReflectFun p) 2 = - (p 2) := by
  simp [shiftedZReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring

/-- Reflection in the z-axis as a linear isometry. -/
private def shiftedZReflect : Point3 ≃ₗᵢ[ℝ] Point3 :=
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

/--
Cell-packing lemma for shifted-copy conflict degree within a direction block.

Given a set of essentially distinct ρ₀-tubes whose parameters in a fixed frame satisfy:
- Direction transverse ≤ 10ρ₀
- Midpoint transverse ≤ 6Aρ₀
- Midpoint longitudinal ≤ A

Then the cardinality is bounded by O(A³).

This is the key sub-lemma for the O(A⁵) shifted-copy conflict degree.
-/
lemma shifted_copy_cell_pack
    {ρ₀ A : ℝ} (hρ₀ : 0 < ρ₀) (hA : 1 ≤ A)
    (hρ₀_small : ρ₀ ≤ 1 / (200 * A))
    {n : ℕ} {T : Fin n → Kakeya.DeltaTube ρ₀}
    (indices : Finset (Fin n))
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (m u : Fin n → Point3)
    (hm : ∀ j, m j = frame.symm (wz2PaperTubeMidpoint (T j)))
    (hu : ∀ j, u j = frame.symm.linearIsometryEquiv (T j).direction)
    (h_dir : ∀ j ∈ indices, |u j 0| ≤ 10 * ρ₀ ∧ |u j 1| ≤ 10 * ρ₀)
    (h_z : ∀ j ∈ indices, u j 2 ≥ 1 / 2 ∨ u j 2 ≤ -1 / 2)
    (h_m_trans : ∀ j ∈ indices, |(m j) 0| ≤ 6 * A * ρ₀ ∧ |(m j) 1| ≤ 6 * A * ρ₀)
    (h_m_long : ∀ j ∈ indices, |(m j) 2| ≤ A)
    (h_distinct : ∀ i j, i ∈ indices → j ∈ indices → i ≠ j → (T i).EssentiallyDistinct (T j)) :
    indices.card ≤ 2 * 4001^2 * (2 * Nat.ceil (1200 * A) + 1)^2 * (2 * Nat.ceil (6400 * A) + 1) := by
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
  let R : Fin 5 → ℝ := ![10 * ρ₀, 10 * ρ₀, 6 * A * ρ₀, 6 * A * ρ₀, A]

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
    intro x
    rfl

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

  have h_m_trans' : ∀ j ∈ negIndices, |(m' j) 0| ≤ 6 * A * ρ₀ ∧ |(m' j) 1| ≤ 6 * A * ρ₀ := by
    intro j hj
    have h0 : (m' j) 0 = (m j) 0 := by dsimp only [m']; exact shiftedZReflectFun_0 (m j)
    have h1 : (m' j) 1 = (m j) 1 := by dsimp only [m']; exact shiftedZReflectFun_1 (m j)
    have h_orig := h_m_trans j (h_sub_neg j hj)
    rw [←h0, ←h1] at h_orig <;> exact h_orig

  have h_m_long' : ∀ j ∈ negIndices, |(m' j) 2| ≤ A := by
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
  have h2 : 6 * A * ρ₀ / (ρ₀ / 200) = 1200 * A := by
    field_simp [hρ₀.ne'] <;> ring
  have h4 : A / (1 / 6400 : ℝ) = 6400 * A := by
    field_simp <;> ring
  have h_ceil2000 : Nat.ceil (2000 : ℝ) = 2000 := by
    rw [Nat.ceil_eq_iff] <;> norm_num
  have h_product : ∏ i : Fin 5, (2 * Nat.ceil (R i / s i) + 1) =
      4001^2 * (2 * Nat.ceil (1200 * A) + 1)^2 * (2 * Nat.ceil (6400 * A) + 1) := by
    simp [R, s, Fin.prod_univ_succ, h0, h2, h4, h_ceil2000] <;> ring

  rw [h_pos_card, h_neg_card] at h_main
  rw [h_product] at h_card_pos h_card_neg
  linarith

end Kakeya.Assouad

end
