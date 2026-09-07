import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeCordobaStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.DirectionBound
import Mathlib.Tactic

/-!
# Root-relative cell-normal direction control
-/

namespace Kakeya.Assouad

open Kakeya.Streamlined Metric

lemma root_refined_union_subset_coarse
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {refined : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (scale : WZ1RootRelativeScaleCoverData
      (sigma := sigma) (epsilon := epsilon) U refined rho) :
    refined.union ⊆ scale.coarseShading.union := by
  intro x hx
  rcases hx with ⟨i, hi⟩
  exact
    ⟨(U.cover rho).parent i,
      scale.point_compatibility i x hi⟩

lemma root_cell_representative_incidence
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y refined : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (scale : WZ1RootRelativeScaleCoverData
      (sigma := sigma) (epsilon := epsilon) U refined rho)
    (subshading : IsSubshading refined Y)
    (plane : WZ1PlaneMapData Y)
    (hrho_pos : 0 < rho.1)
    {j : Fin (U.coarse rho).card}
    {p : Point3}
    (hp : p ∈ scale.coarseShading.carrier j) :
    |inner ℝ ((U.coarse rho).tube j).direction
        (plane.planeMap
          (scale.representative (scale.cell p)))| ≤
      10 * rho.1 := by
  set representative : Point3 :=
    scale.representative (scale.cell p)
  have hdelta_le_rho : delta ≤ rho.1 := rho.2.1
  rcases scale.representative_associated j p hp with
    ⟨i, hparent, hi⟩
  have hY : representative ∈ Y.carrier i :=
    subshading i hi
  have h_incidence :
      |inner ℝ (F.tube i).direction
          (plane.planeMap representative)| ≤
        6 * delta :=
    plane.incidence i representative hY
  have hdelta_nonneg : 0 ≤ delta := by
    have hnonneg :
        0 ≤
          |inner ℝ (F.tube i).direction
            (plane.planeMap representative)| :=
      abs_nonneg _
    linarith
  rcases scale.direction_alignment i with
    ⟨sign, hsign, halign⟩
  have hsign_abs : |sign| = 1 := by
    rcases hsign with (rfl | rfl) <;> norm_num
  have hrepresentative_refined :
      representative ∈ refined.union := ⟨i, hi⟩
  have hrepresentative_Y :
      representative ∈ Y.union :=
    union_subset_of_subshading
      subshading hrepresentative_refined
  have hnormal_unit :
      ‖plane.planeMap representative‖ = 1 :=
    plane.unit representative hrepresentative_Y
  have hdirection :
      ((U.coarse rho).tube j).direction =
        ((U.coarse rho).tube
          ((U.cover rho).parent i)).direction := by
    rw [hparent]
  have hbound :
      |inner ℝ ((U.coarse rho).tube j).direction
          (plane.planeMap representative)| ≤
        4 * rho.1 + 6 * delta := by
    rw [hdirection]
    have hsplit :
        inner ℝ
            ((U.coarse rho).tube
                ((U.cover rho).parent i)).direction
            (plane.planeMap representative) =
          inner ℝ
              (((U.coarse rho).tube
                    ((U.cover rho).parent i)).direction -
                sign • (F.tube i).direction)
              (plane.planeMap representative) +
            sign *
              inner ℝ (F.tube i).direction
                (plane.planeMap representative) := by
      simp [inner_sub_left, inner_smul_left]
    rw [hsplit]
    have htriangle :=
      abs_add_le
        (inner ℝ
          (((U.coarse rho).tube
                ((U.cover rho).parent i)).direction -
            sign • (F.tube i).direction)
          (plane.planeMap representative))
        (sign *
          inner ℝ (F.tube i).direction
            (plane.planeMap representative))
    have hinner :
        |inner ℝ
            (((U.coarse rho).tube
                  ((U.cover rho).parent i)).direction -
              sign • (F.tube i).direction)
            (plane.planeMap representative)| ≤
          ‖((U.coarse rho).tube
                ((U.cover rho).parent i)).direction -
              sign • (F.tube i).direction‖ *
            ‖plane.planeMap representative‖ :=
      abs_real_inner_le_norm _ _
    have hsign_mul :
        |sign *
            inner ℝ (F.tube i).direction
              (plane.planeMap representative)| =
          |sign| *
            |inner ℝ (F.tube i).direction
              (plane.planeMap representative)| := by
      rw [abs_mul]
    calc
      _ ≤
          |inner ℝ
              (((U.coarse rho).tube
                    ((U.cover rho).parent i)).direction -
                sign • (F.tube i).direction)
              (plane.planeMap representative)| +
            |sign *
              inner ℝ (F.tube i).direction
                (plane.planeMap representative)| :=
        htriangle
      _ ≤
          ‖((U.coarse rho).tube
                ((U.cover rho).parent i)).direction -
              sign • (F.tube i).direction‖ *
              ‖plane.planeMap representative‖ +
            |sign| *
              |inner ℝ (F.tube i).direction
                (plane.planeMap representative)| := by
        rw [hsign_mul]
        linarith
      _ ≤ 4 * rho.1 * 1 + 1 * (6 * delta) := by
        gcongr <;>
          linarith
            [hnormal_unit, hsign_abs, halign,
              h_incidence]
      _ = 4 * rho.1 + 6 * delta := by ring
  linarith [hdelta_le_rho]

lemma root_cell_representative_distance
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {refined : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (scale : WZ1RootRelativeScaleCoverData
      (sigma := sigma) (epsilon := epsilon) U refined rho)
    {p q : Point3}
    (hp : p ∈ scale.coarseShading.union)
    (hq : q ∈ scale.coarseShading.union) :
    dist
        (scale.representative (scale.cell p))
        (scale.representative (scale.cell q)) ≤
      dist p q + 4 * rho.1 := by
  set representativeP :=
    scale.representative (scale.cell p)
  set representativeQ :=
    scale.representative (scale.cell q)
  have hrepresentativeP_refined :
      representativeP ∈ refined.union :=
    (scale.cell_fine_witness p hp).1
  have hrepresentativeP_coarse :
      representativeP ∈ scale.coarseShading.union :=
    root_refined_union_subset_coarse
      scale hrepresentativeP_refined
  have hrepresentativeQ_refined :
      representativeQ ∈ refined.union :=
    (scale.cell_fine_witness q hq).1
  have hrepresentativeQ_coarse :
      representativeQ ∈ scale.coarseShading.union :=
    root_refined_union_subset_coarse
      scale hrepresentativeQ_refined
  have hcellP :
      scale.cell representativeP = scale.cell p :=
    (scale.cell_fine_witness p hp).2
  have hcellQ :
      scale.cell representativeQ = scale.cell q :=
    (scale.cell_fine_witness q hq).2
  have hdistP :
      dist p representativeP ≤ 2 * rho.1 :=
    scale.cell_diameter p hp representativeP
      hrepresentativeP_coarse hcellP.symm
  have hdistQ :
      dist q representativeQ ≤ 2 * rho.1 :=
    scale.cell_diameter q hq representativeQ
      hrepresentativeQ_coarse hcellQ.symm
  calc
    dist representativeP representativeQ
        ≤ dist representativeP p +
            dist p q +
            dist q representativeQ := by
      calc
        dist representativeP representativeQ
            ≤ dist representativeP q +
                dist q representativeQ :=
          dist_triangle _ _ _
        _ ≤ dist representativeP p +
              dist p q +
              dist q representativeQ := by
          have htriangle :
              dist representativeP q ≤
                dist representativeP p + dist p q :=
            dist_triangle _ _ _
          linarith
    _ =
        dist p representativeP +
          dist p q +
          dist q representativeQ := by
      rw [dist_comm representativeP p]
    _ ≤
        2 * rho.1 + dist p q + 2 * rho.1 := by
      linarith
    _ = dist p q + 4 * rho.1 := by ring

theorem wz1_root_relative_direction_bound :
    WZ1RootRelativeDirectionBoundStatement := by
  intro delta sigma epsilon F U Y refined rho
    scale subshading plane hrho_pos j p q
    hp hq
  set representativeP :=
    scale.representative (scale.cell p)
  set representativeQ :=
    scale.representative (scale.cell q)
  set L : ℝ := (plane.lipschitzConstant : ℝ)
  have hL_nonneg : 0 ≤ L := by
    exact_mod_cast plane.lipschitzConstant.prop
  have hp_union :
      p ∈ scale.coarseShading.union := ⟨j, hp⟩
  have hrepresentativeP_refined :
      representativeP ∈ refined.union :=
    (scale.cell_fine_witness p hp_union).1
  have hrepresentativeP_Y :
      representativeP ∈ Y.union :=
    union_subset_of_subshading
      subshading hrepresentativeP_refined
  have hrepresentativeQ_refined :
      representativeQ ∈ refined.union :=
    (scale.cell_fine_witness q hq).1
  have hrepresentativeQ_Y :
      representativeQ ∈ Y.union :=
    union_subset_of_subshading
      subshading hrepresentativeQ_refined
  have hincidence :
      |inner ℝ ((U.coarse rho).tube j).direction
          (plane.planeMap representativeP)| ≤
        10 * rho.1 :=
    root_cell_representative_incidence
      scale subshading plane hrho_pos hp
  have hlipschitz :
      dist
          (plane.planeMap representativeQ)
          (plane.planeMap representativeP) ≤
        L * dist representativeQ representativeP :=
    (lipschitzOnWith_iff_dist_le_mul.mp plane.lipschitz)
      representativeQ hrepresentativeQ_Y
      representativeP hrepresentativeP_Y
  have hdistance :
      dist representativeP representativeQ ≤
        dist p q + 4 * rho.1 :=
    root_cell_representative_distance scale hp_union hq
  have hdistance' :
      dist representativeQ representativeP ≤
        dist p q + 4 * rho.1 := by
    rw [dist_comm]
    exact hdistance
  have hdirection_unit :
      ‖((U.coarse rho).tube j).direction‖ = 1 :=
    ((U.coarse rho).tube j).direction_unit
  have hvariation :
      |inner ℝ ((U.coarse rho).tube j).direction
          (plane.planeMap representativeQ -
            plane.planeMap representativeP)| ≤
        L * (dist p q + 4 * rho.1) := by
    calc
      _ ≤
          ‖((U.coarse rho).tube j).direction‖ *
            ‖plane.planeMap representativeQ -
              plane.planeMap representativeP‖ :=
        abs_real_inner_le_norm _ _
      _ =
          dist
            (plane.planeMap representativeQ)
            (plane.planeMap representativeP) := by
        simp [dist_eq_norm, hdirection_unit]
      _ ≤ L * dist representativeQ representativeP :=
        hlipschitz
      _ ≤ L * (dist p q + 4 * rho.1) := by
        gcongr
  have hnormal :
      plane.planeMap representativeQ =
        plane.planeMap representativeP +
          (plane.planeMap representativeQ -
            plane.planeMap representativeP) := by
    abel
  rw [hnormal, inner_add_right]
  have htriangle :=
    abs_add_le
      (inner ℝ ((U.coarse rho).tube j).direction
        (plane.planeMap representativeP))
      (inner ℝ ((U.coarse rho).tube j).direction
        (plane.planeMap representativeQ -
          plane.planeMap representativeP))
  linarith

end Kakeya.Assouad
