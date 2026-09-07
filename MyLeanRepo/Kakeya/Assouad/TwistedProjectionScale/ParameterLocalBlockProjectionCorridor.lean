import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalBlockProjectionCorridorStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.AmplifiedGeometricContainment

/-!
# One local parameter block in a cinematic corridor

Place every subshading of one selected local parameter block inside one
explicit bounded-slope cinematic corridor.
-/

namespace Kakeya.Assouad

theorem parameter_local_block_projection_corridor :
    ParameterLocalBlockProjectionCorridorStatement := by
  intro h_contain h_transfer delta hdelta_pos hdelta_le_one F hF_vertical
    hF_c_bound Y hY_slab C lambda clustered epsilon localBlock f hf_ns hf0 Z hZ_sub

  let indices := parameterLocalBlockIndices clustered localBlock.sourcePoints
  let F_local := parameterLocalBlockFamily clustered localBlock.sourcePoints
  let Y_local := parameterLocalBlockShading clustered localBlock.sourcePoints
  let g_central := halfParameterSlopeCurve f localBlock.localCenter
  let c0 := localBlock.windowCenter
  let w := 300 * localBlock.blockScale

  have hw_pos : 0 < w := mul_pos (by norm_num) localBlock.blockScale_pos
  have hblock_pos : 0 < localBlock.blockScale := localBlock.blockScale_pos

  have hF_local_vertical : IsInVerticalChart F_local :=
    selectedTubeFamily_isInVerticalChart F indices hF_vertical

  have hZ_union_slab : Z.union ⊆ horizontalSlab 0 1 := by
    have h1 : Z.union ⊆ Y_local.union := by
      intro p hp
      rcases hp with ⟨j, hj⟩
      exact ⟨j, hZ_sub j hj⟩
    have h2 : Y_local.union ⊆ Y.union := localBlock.local_union_subset
    exact h1.trans (h2.trans hY_slab)

  have h_main_bound : ∀ (j : Fin F_local.card), Z.carrier j ≠ ∅ →
      |(tubeParams j).c - c0| ≤ w / 2 ∧
      Kakeya.Cinematic.c2Distance
        (slopeCurve f (tubeParams j).a (tubeParams j).b (tubeParams j).d)
        g_central ≤ w := by
    intro j hZj
    let i : Fin F.card := (indices.equivFin.symm j).1
    have hi_mem : i ∈ indices := (indices.equivFin.symm j).2
    have hYlocal_j : Y_local.carrier j ≠ ∅ := by
      intro h
      have hsub : Z.carrier j ⊆ Y_local.carrier j := hZ_sub j
      rw [h] at hsub
      have h' : Z.carrier j = ∅ := by simpa using hsub
      exact hZj h'
    have h_cwindow : |(tubeParams i).c - c0| ≤ delta / 2 :=
      localBlock.local_window j hYlocal_j
    have h_clustered_shading_nonempty : clustered.shading.carrier i ≠ ∅ := by
      simpa [Y_local, parameterLocalBlockShading, selectedTubeShading] using hYlocal_j
    have h_assign_close : dist (tubeParameterPoint3 i) (clustered.assign i) ≤ delta :=
      clustered.assign_close i h_clustered_shading_nonempty
    have h_assign_mem : clustered.assign i ∈ localBlock.sourcePoints := by
      simpa [indices, parameterLocalBlockIndices, Finset.mem_filter] using hi_mem
    have h_center_close : dist (clustered.assign i) localBlock.localCenter ≤
        localBlock.blockScale / 10 :=
      localBlock.source_containment (clustered.assign i) h_assign_mem
    have h_dist : dist (tubeParameterPoint3 i) localBlock.localCenter ≤
        11 * localBlock.blockScale / 10 := by
      calc
        dist (tubeParameterPoint3 i) localBlock.localCenter
          ≤ dist (tubeParameterPoint3 i) (clustered.assign i) +
              dist (clustered.assign i) localBlock.localCenter := dist_triangle _ _ _
        _ ≤ delta + localBlock.blockScale / 10 := by linarith
        _ ≤ localBlock.blockScale + localBlock.blockScale / 10 := by
          linarith [localBlock.fine_le_block]
        _ = 11 * localBlock.blockScale / 10 := by ring
    have h_c2 : Kakeya.Cinematic.c2Distance
        (halfParameterSlopeCurve f (tubeParameterPoint3 i)) g_central ≤
        286 * localBlock.blockScale := by
      have h := halfParameterSlopeCurve_c2Distance_le f hf_ns hf0
        (tubeParameterPoint3 i) localBlock.localCenter
      calc
        Kakeya.Cinematic.c2Distance
            (halfParameterSlopeCurve f (tubeParameterPoint3 i)) g_central
          ≤ 260 * dist (tubeParameterPoint3 i) localBlock.localCenter := h
        _ ≤ 260 * (11 * localBlock.blockScale / 10) := by gcongr
        _ = 286 * localBlock.blockScale := by ring
    have h_c2_le : Kakeya.Cinematic.c2Distance
        (halfParameterSlopeCurve f (tubeParameterPoint3 i)) g_central ≤ w := by
      dsimp only [w]
      linarith
    have h_tube_curve_eq : slopeCurve f (tubeParams j).a (tubeParams j).b (tubeParams j).d =
        halfParameterSlopeCurve f (tubeParameterPoint3 i) := by
      have h_eq : (tubeParams j).a = (tubeParams i).a ∧
          (tubeParams j).b = (tubeParams i).b ∧
          (tubeParams j).d = (tubeParams i).d := by
        exact ⟨rfl, rfl, rfl⟩
      rw [h_eq.1, h_eq.2.1, h_eq.2.2]
      exact (halfParameterSlopeCurve_tubeParameterPoint3 f i).symm
    have h_cwindow2 : |(tubeParams j).c - c0| ≤ w / 2 := by
      have h4 : (tubeParams j).c = (tubeParams i).c := by rfl
      rw [h4]
      calc
        |(tubeParams i).c - c0| ≤ delta / 2 := h_cwindow
        _ ≤ localBlock.blockScale / 2 := by linarith [localBlock.fine_le_block]
        _ ≤ w / 2 := by
          dsimp only [w]
          linarith
    exact ⟨h_cwindow2, by rw [h_tube_curve_eq]; exact h_c2_le⟩

  let assign : Fin F_local.card → Kakeya.Cinematic.C2Function := fun _ => g_central

  have h_containment_per_j : ∀ (j : Fin F_local.card), Z.carrier j ≠ ∅ →
      cinematicShear c0 '' (twistedProjection f '' Z.carrier j) ⊆
        Kakeya.Cinematic.graphNeighborhood g_central (20 * (delta + w)) :=
    h_contain hdelta_pos hdelta_le_one hw_pos F_local hF_local_vertical
      Z hZ_union_slab f hf_ns hf0 c0 assign h_main_bound

  have h_containment_all : cinematicShear c0 '' twistedUnion Z f ⊆
      Kakeya.Cinematic.graphNeighborhood g_central (20 * (delta + w)) := by
    intro q hq
    rcases hq with ⟨y, hy, rfl⟩
    -- y : Point2, hy : y ∈ twistedUnion Z f
    rcases hy with ⟨x, hx, rfl⟩
    -- x : Point3, hx : x ∈ Z.union
    rcases hx with ⟨j, hj⟩
    have hne : Z.carrier j ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨x, hj⟩
    have h_img : cinematicShear c0 (twistedProjection f x) ∈
        cinematicShear c0 '' (twistedProjection f '' Z.carrier j) := by
      apply Set.mem_image_of_mem
      apply Set.mem_image_of_mem
      exact hj
    exact h_containment_per_j j hne h_img

  let r := 6020 * localBlock.blockScale
  have hr_nonneg : 0 ≤ r := by positivity
  have h_radius_bound : 20 * (delta + w) ≤ r := by
    dsimp only [w, r]
    linarith [localBlock.fine_le_block]

  have h_graph_mono : Kakeya.Cinematic.graphNeighborhood g_central (20 * (delta + w)) ⊆
      Kakeya.Cinematic.graphNeighborhood g_central r := by
    intro x hx
    rcases Metric.mem_thickening_iff.mp hx with ⟨y, hy, hdist⟩
    have hdist' : dist x y < r := hdist.trans_le h_radius_bound
    exact Metric.mem_thickening_iff.mpr ⟨y, hy, hdist'⟩

  have h_mass_pos : 0 < Y_local.mass := by
    have h1 : 0 < localBlock.sourcePoints.card :=
      Finset.card_pos.mpr localBlock.sourcePoints_nonempty
    have hne1 : localBlock.sourcePoints.enncard ≠ 0 := by
      have h : localBlock.sourcePoints.enncard = ↑(localBlock.sourcePoints.card) := by
        rfl
      rw [h]
      exact Nat.cast_ne_zero.mpr h1.ne'
    have hne2 : clustered.clusterMass ≠ 0 := ne_of_gt clustered.clusterMass_pos
    have hmul : localBlock.sourcePoints.enncard * clustered.clusterMass ≠ 0 :=
      mul_ne_zero hne1 hne2
    have hpos : 0 < localBlock.sourcePoints.enncard * clustered.clusterMass := by
      have hle : 0 ≤ localBlock.sourcePoints.enncard * clustered.clusterMass := by positivity
      exact lt_of_le_of_ne hle hmul.symm
    exact hpos.trans_le localBlock.local_mass_lower

  have h_exists_active : ∃ (j : Fin F_local.card), Y_local.carrier j ≠ ∅ := by
    by_contra h
    push Not at h
    have h4 : Y_local.mass = 0 := by
      have h5 : ∀ (j : Fin F_local.card), MeasureTheory.volume (Y_local.carrier j) = 0 := by
        intro j
        have h6 : Y_local.carrier j = ∅ := h j
        rw [h6]
        <;> simp
      have h6 : Y_local.mass = ∑ i : Fin F_local.card, MeasureTheory.volume (Y_local.carrier i) := by rfl
      rw [h6, Finset.sum_congr rfl (fun i _ => h5 i)]
      <;> simp
    rw [h4] at h_mass_pos
    <;> simpa using h_mass_pos

  have h_c0_bound : |c0| ≤ 3 := by
    rcases h_exists_active with ⟨j, hj⟩
    let i : Fin F.card := (indices.equivFin.symm j).1
    have h_cwindow : |(tubeParams i).c - c0| ≤ delta / 2 :=
      localBlock.local_window j hj
    have h_c_bound : |(tubeParams i).c| ≤ 2 := hF_c_bound i
    have h_triangle : |c0| ≤ |(tubeParams i).c| + |(tubeParams i).c - c0| := by
      have h_eq1 : (tubeParams i).c - ((tubeParams i).c - c0) = c0 := by ring
      have h_abs : |((tubeParams i).c) - ((tubeParams i).c - c0)| ≤
          |(tubeParams i).c| + |(tubeParams i).c - c0| :=
        abs_sub ((tubeParams i).c) ((tubeParams i).c - c0)
      rw [h_eq1] at h_abs
      exact h_abs
    linarith [hdelta_le_one]

  have h_center_bounds : |localBlock.localCenter 1| ≤ 2 ∧
      |localBlock.localCenter 2| ≤ 2 := by
    rcases localBlock.sourcePoints_nonempty with ⟨p, hp⟩
    have hp_points : p ∈ clustered.points := localBlock.sourcePoints_subset hp
    have hp_unit : dist p (0 : Point 3) ≤ 1 :=
      clustered.points_in_unitBall p hp_points
    have hdist : dist p localBlock.localCenter ≤ localBlock.blockScale / 10 :=
      localBlock.source_containment p hp
    have h_center_dist : dist localBlock.localCenter (0 : Point 3) ≤ 2 := by
      calc
        dist localBlock.localCenter (0 : Point 3)
          ≤ dist localBlock.localCenter p + dist p (0 : Point 3) := dist_triangle _ _ _
        _ = dist p localBlock.localCenter + dist p (0 : Point 3) := by rw [dist_comm]
        _ ≤ localBlock.blockScale / 10 + 1 := by gcongr
        _ ≤ 2 := by linarith [localBlock.blockScale_small]
    have h1 : |localBlock.localCenter 1| ≤ 2 := by
      have hcoord : |localBlock.localCenter 1| ≤
          dist localBlock.localCenter (0 : Point 3) := by
        have h := PiLp.dist_apply_le localBlock.localCenter (0 : Point 3) (1 : Fin 3)
        simpa [Real.dist_eq, sub_zero] using h
      exact hcoord.trans h_center_dist
    have h2 : |localBlock.localCenter 2| ≤ 2 := by
      have hcoord : |localBlock.localCenter 2| ≤
          dist localBlock.localCenter (0 : Point 3) := by
        have h := PiLp.dist_apply_le localBlock.localCenter (0 : Point 3) (2 : Fin 3)
        simpa [Real.dist_eq, sub_zero] using h
      exact hcoord.trans h_center_dist
    exact ⟨h1, h2⟩

  have hlipschitz : LipschitzOnWith (128 : NNReal) g_central.extension
      (Set.Icc (0 : ℝ) 1) :=
    halfParameterSlopeCurve_lipschitzOn_Icc01 f hf_ns hf0
      localBlock.localCenter h_center_bounds.1 h_center_bounds.2

  have h_transfer_result := h_transfer g_central c0 (3 : NNReal) (128 : NNReal)
    h_c0_bound hlipschitz r hr_nonneg

  have h_final_containment : twistedUnion Z f ⊆
      Metric.cthickening (30100 * localBlock.blockScale)
        (cinematicExtensionGraph (parameterLocalBlockCentralCurve localBlock f)) := by
    have h1 : twistedUnion Z f ⊆
        {q : Point2 | cinematicShear c0 q ∈ Kakeya.Cinematic.graphNeighborhood g_central r} := by
      intro q hq
      have h2 : cinematicShear c0 q ∈
          Kakeya.Cinematic.graphNeighborhood g_central (20 * (delta + w)) :=
        h_containment_all ⟨q, hq, rfl⟩
      exact h_graph_mono h2
    have h3 : (30100 * localBlock.blockScale) = (2 + (3 : ℝ)) * r := by
      dsimp only [r] <;> ring
    rw [h3]
    exact h1.trans h_transfer_result.1

  have h_final_lipschitz : LipschitzOnWith (131 : NNReal)
      (parameterLocalBlockCentralCurve localBlock f).extension
      (Set.Icc (0 : ℝ) 1) := by
    have h4 : (128 + 3 : NNReal) = (131 : NNReal) := by norm_num
    rw [h4] at h_transfer_result
    exact h_transfer_result.2

  exact ⟨h_final_containment, h_final_lipschitz⟩

end Kakeya.Assouad
