import MyLeanRepo.Kakeya.Assouad.WZ1.LocalGrainCubeCountStatements
import Mathlib.Tactic

/-!
# Direction bound for coarse tubes via cell normal
-/

namespace Kakeya.Assouad

open Kakeya.Streamlined Metric

/-- refined.union ⊆ Y.union from carrier-wise subshading. -/
lemma union_subset_of_subshading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y refined : Kakeya.Streamlined.TubeShading F}
    (hsub : ∀ i, refined.carrier i ⊆ Y.carrier i) :
    refined.union ⊆ Y.union := by
  intro x hx
  rcases hx with ⟨i, hi⟩
  exact ⟨i, hsub i hi⟩

/-- refined.union ⊆ coarseShading.union via point_compatibility. -/
private lemma refined_union_subset_coarse
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon) U Y rho) :
    first.refined.union ⊆ first.coarseShading.union := by
  intro x hx
  rcases hx with ⟨i, hi⟩
  have h : x ∈ first.coarseShading.carrier ((U.cover rho).parent i) :=
    first.point_compatibility i x hi
  exact ⟨(U.cover rho).parent i, h⟩

/-- Direction-plane incidence bound at a cell representative: ≤ 10 * rho.1. -/
lemma cell_representative_incidence
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon) U Y rho)
    (plane : WZ1PlaneMapData Y)
    (hrho_pos : 0 < rho.1)
    {j : Fin (U.coarse rho).card}
    {p : Point3}
    (hp : p ∈ first.coarseShading.carrier j) :
    |inner ℝ ((U.coarse rho).tube j).direction
        (plane.planeMap (first.representative (first.cell p)))| ≤ 10 * rho.1 := by
  set r_p : Point3 := first.representative (first.cell p) with hrp_def
  have hdelta_le_rho : delta ≤ rho.1 := rho.2.1
  have h_assoc : ∃ (i : Fin F.card),
      (U.cover rho).parent i = j ∧ r_p ∈ first.refined.carrier i :=
    first.representative_associated j p hp
  rcases h_assoc with ⟨i, hparent, hri⟩
  have hY : r_p ∈ Y.carrier i := first.subshading i hri
  have h_inc : |inner ℝ (F.tube i).direction (plane.planeMap r_p)| ≤ 6 * delta :=
    plane.incidence i r_p hY
  have hdelta_nonneg : 0 ≤ delta := by
    have h : 0 ≤ |inner ℝ (F.tube i).direction (plane.planeMap r_p)| := abs_nonneg _
    linarith
  rcases first.direction_alignment i with ⟨sign, hsign1, h_align⟩
  have hsign_abs : |sign| = 1 := by
    rcases hsign1 with (rfl | rfl) <;> norm_num
  have h_refined_union : r_p ∈ first.refined.union := ⟨i, hri⟩
  have hY_union : r_p ∈ Y.union := union_subset_of_subshading first.subshading h_refined_union
  have h_unit : ‖plane.planeMap r_p‖ = 1 := plane.unit r_p hY_union
  have h1 : ((U.coarse rho).tube j).direction =
      ((U.coarse rho).tube ((U.cover rho).parent i)).direction := by rw [hparent]
  have h_abs1 : |inner ℝ ((U.coarse rho).tube j).direction (plane.planeMap r_p)| ≤
      4 * rho.1 + 6 * delta := by
    rw [h1]
    have h2 : inner ℝ ((U.coarse rho).tube ((U.cover rho).parent i)).direction (plane.planeMap r_p) =
        inner ℝ (((U.coarse rho).tube ((U.cover rho).parent i)).direction - sign • (F.tube i).direction)
          (plane.planeMap r_p) + sign * inner ℝ (F.tube i).direction (plane.planeMap r_p) := by
      simp [inner_sub_left, inner_smul_left]
    rw [h2]
    have h3 : |inner ℝ (((U.coarse rho).tube ((U.cover rho).parent i)).direction - sign • (F.tube i).direction)
          (plane.planeMap r_p)| ≤
        ‖((U.coarse rho).tube ((U.cover rho).parent i)).direction - sign • (F.tube i).direction‖ *
        ‖plane.planeMap r_p‖ := abs_real_inner_le_norm _ _
    have h4 : |sign * inner ℝ (F.tube i).direction (plane.planeMap r_p)| =
        |sign| * |inner ℝ (F.tube i).direction (plane.planeMap r_p)| := by rw [abs_mul]
    have h5 : |inner ℝ (((U.coarse rho).tube ((U.cover rho).parent i)).direction - sign • (F.tube i).direction)
          (plane.planeMap r_p) + sign * inner ℝ (F.tube i).direction (plane.planeMap r_p)| ≤
        |inner ℝ (((U.coarse rho).tube ((U.cover rho).parent i)).direction - sign • (F.tube i).direction)
          (plane.planeMap r_p)| + |sign * inner ℝ (F.tube i).direction (plane.planeMap r_p)| :=
      abs_add_le _ _
    calc
      _ ≤ _ := h5
      _ ≤ ‖((U.coarse rho).tube ((U.cover rho).parent i)).direction - sign • (F.tube i).direction‖ *
              ‖plane.planeMap r_p‖ + |sign| * |inner ℝ (F.tube i).direction (plane.planeMap r_p)| := by
            rw [h4]; linarith
      _ ≤ 4 * rho.1 * 1 + 1 * (6 * delta) := by
            gcongr <;> linarith [h_unit, hsign_abs, h_align, h_inc]
      _ = 4 * rho.1 + 6 * delta := by ring
  linarith [hdelta_le_rho]

/-- Distance between cell representatives: ≤ dist(p,q) + 4*rho.1. -/
lemma cell_representative_distance
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon) U Y rho)
    {p q : Point3}
    (hp : p ∈ first.coarseShading.union)
    (hq : q ∈ first.coarseShading.union) :
    dist (first.representative (first.cell p))
         (first.representative (first.cell q)) ≤
      dist p q + 4 * rho.1 := by
  set r_p := first.representative (first.cell p) with hrp
  set r_q := first.representative (first.cell q) with hrq
  have hrp_refined : r_p ∈ first.refined.union := first.cell_fine_witness p hp |>.1
  have hrp_union : r_p ∈ first.coarseShading.union := refined_union_subset_coarse first hrp_refined
  have hrq_refined : r_q ∈ first.refined.union := first.cell_fine_witness q hq |>.1
  have hrq_union : r_q ∈ first.coarseShading.union := refined_union_subset_coarse first hrq_refined
  have hcell_p : first.cell r_p = first.cell p := first.cell_fine_witness p hp |>.2
  have hcell_q : first.cell r_q = first.cell q := first.cell_fine_witness q hq |>.2
  have hdist_p : dist p r_p ≤ 2 * rho.1 := first.cell_diameter p hp r_p hrp_union hcell_p.symm
  have hdist_q : dist q r_q ≤ 2 * rho.1 := first.cell_diameter q hq r_q hrq_union hcell_q.symm
  calc
    dist r_p r_q
      ≤ dist r_p p + dist p q + dist q r_q := by
        calc dist r_p r_q
          ≤ dist r_p q + dist q r_q := dist_triangle _ _ _
        _ ≤ dist r_p p + dist p q + dist q r_q := by
            have h : dist r_p q ≤ dist r_p p + dist p q := dist_triangle _ _ _
            linarith
    _ = dist p r_p + dist p q + dist q r_q := by rw [dist_comm r_p p]
    _ ≤ 2 * rho.1 + dist p q + 2 * rho.1 := by linarith
    _ = dist p q + 4 * rho.1 := by ring

/-- Full direction bound with respect to the cell normal at q. -/
lemma direction_bound_with_cell_normal
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon) U Y rho)
    (plane : WZ1PlaneMapData Y)
    (hrho_pos : 0 < rho.1)
    {j : Fin (U.coarse rho).card}
    {p q : Point3}
    (hp_carrier : p ∈ first.coarseShading.carrier j)
    (hq_union : q ∈ first.coarseShading.union) :
    |inner ℝ ((U.coarse rho).tube j).direction
        (plane.planeMap (first.representative (first.cell q)))| ≤
      10 * rho.1 + (plane.lipschitzConstant : ℝ) * (dist p q + 4 * rho.1) := by
  set r_p := first.representative (first.cell p) with hrp
  set r_q := first.representative (first.cell q) with hrq
  set L : ℝ := (plane.lipschitzConstant : ℝ) with hL
  have hL_nonneg : 0 ≤ L := by exact_mod_cast plane.lipschitzConstant.prop
  have hp_union : p ∈ first.coarseShading.union := ⟨j, hp_carrier⟩
  have hrp_refined : r_p ∈ first.refined.union := first.cell_fine_witness p hp_union |>.1
  have hrp_Y : r_p ∈ Y.union := union_subset_of_subshading first.subshading hrp_refined
  have hrq_refined : r_q ∈ first.refined.union := first.cell_fine_witness q hq_union |>.1
  have hrq_Y : r_q ∈ Y.union := union_subset_of_subshading first.subshading hrq_refined
  have h_inc : |inner ℝ ((U.coarse rho).tube j).direction (plane.planeMap r_p)| ≤ 10 * rho.1 :=
    cell_representative_incidence first plane hrho_pos hp_carrier
  have h_lip_dist : dist (plane.planeMap r_q) (plane.planeMap r_p) ≤ L * dist r_q r_p :=
    (lipschitzOnWith_iff_dist_le_mul.mp plane.lipschitz) r_q hrq_Y r_p hrp_Y
  have h_dist : dist r_p r_q ≤ dist p q + 4 * rho.1 :=
    cell_representative_distance first hp_union hq_union
  have h_dist' : dist r_q r_p ≤ dist p q + 4 * rho.1 := by
    rw [dist_comm]; exact h_dist
  have hdir_norm : ‖((U.coarse rho).tube j).direction‖ = 1 := (U.coarse rho).tube j |>.direction_unit
  have h_var : |inner ℝ ((U.coarse rho).tube j).direction (plane.planeMap r_q - plane.planeMap r_p)| ≤
      L * (dist p q + 4 * rho.1) := by
    calc
      |inner ℝ ((U.coarse rho).tube j).direction (plane.planeMap r_q - plane.planeMap r_p)|
        ≤ ‖((U.coarse rho).tube j).direction‖ * ‖plane.planeMap r_q - plane.planeMap r_p‖ :=
          abs_real_inner_le_norm _ _
      _ = dist (plane.planeMap r_q) (plane.planeMap r_p) := by
            simp [dist_eq_norm, hdir_norm]
      _ ≤ L * dist r_q r_p := h_lip_dist
      _ ≤ L * (dist p q + 4 * rho.1) := by gcongr
  have h_eq : plane.planeMap r_q = plane.planeMap r_p + (plane.planeMap r_q - plane.planeMap r_p) := by abel
  have h_final : |inner ℝ ((U.coarse rho).tube j).direction (plane.planeMap r_q)| ≤
      10 * rho.1 + L * (dist p q + 4 * rho.1) := by
    rw [h_eq, inner_add_right]
    have h6 : |inner ℝ ((U.coarse rho).tube j).direction (plane.planeMap r_p) +
          inner ℝ ((U.coarse rho).tube j).direction (plane.planeMap r_q - plane.planeMap r_p)| ≤
        |inner ℝ ((U.coarse rho).tube j).direction (plane.planeMap r_p)| +
        |inner ℝ ((U.coarse rho).tube j).direction (plane.planeMap r_q - plane.planeMap r_p)| :=
      abs_add_le _ _
    linarith
  exact h_final

end Kakeya.Assouad
