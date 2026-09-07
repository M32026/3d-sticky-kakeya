import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CubicGridRefinedCells
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingProfileThreshold

/-!
# A concrete occupied cell at the selected spacing scale
-/

noncomputable section

namespace Kakeya.Assouad

lemma parameterSpacing_selected_scale_separation
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10) :
    Real.rpow delta (1 - epsilon ^ 2) <
      9 * (profile.tree.base : ℝ) *
        Real.rpow (profile.tree.base : ℝ)
          (-(profile.selected.selectedLevel.val : ℝ)) := by
  let exponent : ℝ := 1 - epsilon ^ 2
  have hexponent_pos : 0 < exponent := by
    dsimp only [exponent]
    nlinarith [sq_nonneg epsilon]
  have hexponent_one : exponent ≤ 1 := by
    dsimp only [exponent]
    nlinarith [sq_nonneg epsilon]
  have hbase_pos : (0 : ℝ) < profile.tree.base := by
    exact_mod_cast
      (show 0 < profile.tree.base from
        lt_of_lt_of_le (by norm_num)
          profile.tree.base_ge_three)
  have hbase_one : (1 : ℝ) ≤ profile.tree.base := by
    exact_mod_cast
      (show 1 ≤ profile.tree.base from
        (by omega : 1 ≤ 3).trans
          profile.tree.base_ge_three)
  have hlevels_pos : (0 : ℝ) < profile.tree.levels := by
    exact_mod_cast profile.tree.levels_pos
  have hselected_normalized :
      (profile.selected.selectedLevel.val : ℝ) /
          (profile.tree.levels : ℝ) <
        exponent := by
    simpa [scaleWeight, exponent] using
      profile.selected.selected_early
  have hselected_index :
      (profile.selected.selectedLevel.val : ℝ) <
        (profile.tree.levels : ℝ) * exponent := by
    simpa [mul_comm] using
      (div_lt_iff₀ hlevels_pos).mp
        hselected_normalized
  have hmesh_compare :
      Real.rpow (profile.tree.base : ℝ)
            (-((profile.tree.levels : ℝ) * exponent)) <
        Real.rpow (profile.tree.base : ℝ)
          (-(profile.selected.selectedLevel.val : ℝ)) := by
    exact Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast
        (show 1 < profile.tree.base from
          (by omega : 1 < 3).trans_le
            profile.tree.base_ge_three))
      (by linarith)
  have hterminal_eq :
      Real.rpow (profile.tree.base : ℝ)
          (-(profile.tree.levels : ℝ)) =
        (profile.tree.base ^ profile.tree.levels : ℝ)⁻¹ := by
    calc
      Real.rpow (profile.tree.base : ℝ)
          (-(profile.tree.levels : ℝ)) =
          (Real.rpow (profile.tree.base : ℝ)
            (profile.tree.levels : ℝ))⁻¹ :=
        Real.rpow_neg hbase_pos.le _
      _ = (profile.tree.base ^ profile.tree.levels : ℝ)⁻¹ := by
        exact congrArg Inv.inv
          (Real.rpow_natCast
            (profile.tree.base : ℝ)
            profile.tree.levels)
  have hterminal_power :
      Real.rpow
          ((profile.tree.base ^ profile.tree.levels : ℝ)⁻¹)
          exponent =
        Real.rpow (profile.tree.base : ℝ)
          (-((profile.tree.levels : ℝ) * exponent)) := by
    rw [← hterminal_eq]
    calc
      Real.rpow
          (Real.rpow (profile.tree.base : ℝ)
            (-(profile.tree.levels : ℝ)))
          exponent =
          Real.rpow (profile.tree.base : ℝ)
            ((-(profile.tree.levels : ℝ)) * exponent) := by
        exact (Real.rpow_mul hbase_pos.le _ _).symm
      _ = Real.rpow (profile.tree.base : ℝ)
          (-((profile.tree.levels : ℝ) * exponent)) := by
        congr 1
        ring
  have hdelta_scaled :
      Real.rpow
          (delta / (3 * (profile.tree.base : ℝ)))
          exponent ≤
        Real.rpow
          ((profile.tree.base ^ profile.tree.levels : ℝ)⁻¹)
          exponent :=
    Real.rpow_le_rpow (by positivity)
      profile.tree.terminal_mesh_lower
      hexponent_pos.le
  have hfactor :
      Real.rpow (3 * (profile.tree.base : ℝ))
          exponent ≤
        3 * (profile.tree.base : ℝ) := by
    exact Real.rpow_le_self_of_one_le
      (by nlinarith [hbase_one]) hexponent_one
  have hdelta_factor :
      Real.rpow delta exponent =
        Real.rpow (3 * (profile.tree.base : ℝ))
            exponent *
          Real.rpow
            (delta / (3 * (profile.tree.base : ℝ)))
            exponent := by
    have hproduct :
        (3 * (profile.tree.base : ℝ)) *
            (delta / (3 * (profile.tree.base : ℝ))) =
          delta := by
      field_simp [hbase_pos.ne']
    calc
      Real.rpow delta exponent =
          Real.rpow
            ((3 * (profile.tree.base : ℝ)) *
              (delta / (3 * (profile.tree.base : ℝ))))
            exponent := by
        exact congrArg
          (fun value : ℝ => Real.rpow value exponent)
          hproduct.symm
      _ =
          Real.rpow (3 * (profile.tree.base : ℝ))
              exponent *
            Real.rpow
              (delta / (3 * (profile.tree.base : ℝ)))
              exponent :=
        Real.mul_rpow (by positivity) (by positivity)
  rw [hdelta_factor]
  calc
    Real.rpow (3 * (profile.tree.base : ℝ)) exponent *
          Real.rpow
            (delta / (3 * (profile.tree.base : ℝ)))
            exponent
        ≤ (3 * (profile.tree.base : ℝ)) *
          Real.rpow
            ((profile.tree.base ^ profile.tree.levels : ℝ)⁻¹)
            exponent := by
      gcongr
      exact Real.rpow_nonneg (by positivity) _
    _ = (3 * (profile.tree.base : ℝ)) *
          Real.rpow (profile.tree.base : ℝ)
            (-((profile.tree.levels : ℝ) * exponent)) := by
      rw [hterminal_power]
    _ < (3 * (profile.tree.base : ℝ)) *
          Real.rpow (profile.tree.base : ℝ)
            (-(profile.selected.selectedLevel.val : ℝ)) := by
      gcongr
    _ < 9 * (profile.tree.base : ℝ) *
          Real.rpow (profile.tree.base : ℝ)
            (-(profile.selected.selectedLevel.val : ℝ)) := by
      have hmesh_pos :
          0 < Real.rpow (profile.tree.base : ℝ)
            (-(profile.selected.selectedLevel.val : ℝ)) :=
        Real.rpow_pos_of_pos hbase_pos _
      nlinarith

structure ParameterSpacingSelectedCellData
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered) where
  cell : DiscreteSet 3
  cell_mem :
    cell ∈ profile.tree.partition
      profile.selected.selectedLevel.val
  points : DiscreteSet 3
  points_eq :
    points =
      profile.tree.refinedPoints ∩ cell
  points_nonempty : points.Nonempty
  points_subset :
    points ⊆ clustered.points
  center : Point 3
  center_mem : center ∈ points
  blockScale : ℝ
  blockScale_eq :
    blockScale =
      90 * (profile.tree.base : ℝ) *
        Real.rpow (profile.tree.base : ℝ)
          (-(profile.selected.selectedLevel.val : ℝ))
  blockScale_pos : 0 < blockScale
  ten_delta_lt : 10 * delta < blockScale
  blockScale_small : 100 * blockScale ≤ 1
  separated_scale :
    Real.rpow delta (1 - epsilon ^ 2) <
      blockScale / 10
  points_containment :
    ∀ p ∈ points,
      dist p center ≤ blockScale / 10

theorem parameter_spacing_selected_cell
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10)
    (hdelta : 0 < delta)
    (hdelta_small : delta < 1)
    (hseparated :
      Real.rpow delta (1 - epsilon ^ 2) <
        9 * (profile.tree.base : ℝ) *
          Real.rpow (profile.tree.base : ℝ)
            (-(profile.selected.selectedLevel.val : ℝ))) :
    Nonempty
      (ParameterSpacingSelectedCellData profile) := by
  let level := profile.selected.selectedLevel.val
  let occupied :=
    occupiedPartitionCells
      profile.tree.refinedPoints
      profile.tree.partition level
  have hoccupied_nonempty : occupied.Nonempty := by
    rcases profile.tree.refined_nonempty with ⟨point, hpoint⟩
    have hpoint_clustered :=
      profile.tree.refined_subset hpoint
    have hcover :=
      (profile.tree.partition_tree level
        profile.selected.selectedLevel.is_lt.le).2.2
        hpoint_clustered
    rcases Finset.mem_biUnion.mp hcover with
      ⟨cell, hcell, hpoint_cell⟩
    refine ⟨cell, Finset.mem_filter.mpr
      ⟨hcell, ?_⟩⟩
    exact ⟨point, Finset.mem_inter.mpr
      ⟨hpoint, hpoint_cell⟩⟩
  let cell := Classical.choose hoccupied_nonempty
  have hcell_occupied : cell ∈ occupied :=
    Classical.choose_spec hoccupied_nonempty
  have hcell :
      cell ∈ profile.tree.partition level :=
    (Finset.mem_filter.mp hcell_occupied).1
  let points : DiscreteSet 3 :=
    profile.tree.refinedPoints ∩ cell
  have hpoints_nonempty :
      points.Nonempty :=
    (Finset.mem_filter.mp hcell_occupied).2
  let center := Classical.choose hpoints_nonempty
  have hcenter : center ∈ points :=
    Classical.choose_spec hpoints_nonempty
  let blockScale : ℝ :=
    90 * (profile.tree.base : ℝ) *
      Real.rpow (profile.tree.base : ℝ)
        (-(level : ℝ))
  have hbase_pos : (0 : ℝ) < profile.tree.base := by
    exact_mod_cast
      (show 0 < profile.tree.base from
        lt_of_lt_of_le (by norm_num)
          profile.tree.base_ge_three)
  have hscale_pos : 0 < blockScale := by
    dsimp only [blockScale]
    exact mul_pos
      (mul_pos (by norm_num) hbase_pos)
      (Real.rpow_pos_of_pos hbase_pos _)
  have hmesh_eq :
      Real.rpow (profile.tree.base : ℝ)
          (-(level : ℝ)) =
        (profile.tree.base ^ level : ℝ)⁻¹ := by
    calc
      Real.rpow (profile.tree.base : ℝ)
          (-(level : ℝ)) =
          (Real.rpow (profile.tree.base : ℝ)
            (level : ℝ))⁻¹ :=
        Real.rpow_neg hbase_pos.le _
      _ = (profile.tree.base ^ level : ℝ)⁻¹ := by
        exact congrArg Inv.inv
          (Real.rpow_natCast
            (profile.tree.base : ℝ) level)
  have hlevel_le :
      level ≤ profile.tree.levels := by
    simpa [level] using
      profile.selected.selectedLevel.is_lt.le
  have hpow_mono :
      (profile.tree.base ^ level : ℝ) ≤
        (profile.tree.base ^
          profile.tree.levels : ℝ) := by
    exact_mod_cast
      pow_le_pow_right₀
        (show 1 ≤ profile.tree.base from
          (by omega : 1 ≤ 3).trans
            profile.tree.base_ge_three)
        hlevel_le
  have hinv_mono :
      (profile.tree.base ^
          profile.tree.levels : ℝ)⁻¹ ≤
        (profile.tree.base ^ level : ℝ)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2
      hpow_mono
  have hdelta_mesh :
      delta /
          (3 * (profile.tree.base : ℝ)) ≤
        Real.rpow (profile.tree.base : ℝ)
          (-(level : ℝ)) := by
    rw [hmesh_eq]
    exact profile.tree.terminal_mesh_lower.trans
      hinv_mono
  have hten_delta :
      10 * delta < blockScale := by
    dsimp only [blockScale]
    have hbase_ge : (3 : ℝ) ≤ profile.tree.base := by
      exact_mod_cast profile.tree.base_ge_three
    have hthirty :
        30 * delta ≤
          90 * (profile.tree.base : ℝ) *
            Real.rpow (profile.tree.base : ℝ)
              (-(level : ℝ)) := by
      have h :=
        mul_le_mul_of_nonneg_left hdelta_mesh
          (show (0 : ℝ) ≤
            90 * profile.tree.base by positivity)
      have hcancel :
          90 * (profile.tree.base : ℝ) *
              (delta /
                (3 * (profile.tree.base : ℝ))) =
            30 * delta := by
        field_simp [hbase_pos.ne']
        ring
      rwa [hcancel] at h
    exact (by nlinarith : 10 * delta < 30 * delta).trans_le
      hthirty
  have hstart_le :
      parameterSpacingStartIndex ≤ level := by
    dsimp only [level]
    rw [← profile.start.level_val,
      ← profile.selected_starts_at_start]
    exact profile.selected.start_le_selected
  have hscale_small :
      Real.rpow (profile.tree.base : ℝ)
          (-(level : ℝ)) ≤
        Real.rpow (profile.tree.base : ℝ)
          (-(parameterSpacingStartIndex : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le
      (by
        have : (1 : ℝ) ≤ profile.tree.base := by
          exact_mod_cast
            (show 1 ≤ profile.tree.base from
              (by omega : 1 ≤ 3).trans
                profile.tree.base_ge_three)
        exact this)
      (by
        have hcast :
            (parameterSpacingStartIndex : ℝ) ≤
              (level : ℝ) := by
          exact_mod_cast hstart_le
        linarith)
  have hstart_numeric :
      100 * 90 * (profile.tree.base : ℝ) *
          Real.rpow (profile.tree.base : ℝ)
            (-(parameterSpacingStartIndex : ℝ)) ≤ 1 := by
    have hbase_ge : (3 : ℝ) ≤ profile.tree.base := by
      exact_mod_cast profile.tree.base_ge_three
    have hrewrite :
        (profile.tree.base : ℝ) *
            Real.rpow (profile.tree.base : ℝ)
              (-(parameterSpacingStartIndex : ℝ)) =
          Real.rpow (profile.tree.base : ℝ)
            (1 - parameterSpacingStartIndex) := by
      have hone :
          (profile.tree.base : ℝ) =
            Real.rpow (profile.tree.base : ℝ) 1 := by
        exact (Real.rpow_one _).symm
      calc
        (profile.tree.base : ℝ) *
            Real.rpow (profile.tree.base : ℝ)
              (-(parameterSpacingStartIndex : ℝ)) =
            Real.rpow (profile.tree.base : ℝ) 1 *
              Real.rpow (profile.tree.base : ℝ)
                (-(parameterSpacingStartIndex : ℝ)) := by rw [← hone]
        _ = Real.rpow (profile.tree.base : ℝ)
              (1 + -(parameterSpacingStartIndex : ℝ)) :=
          (Real.rpow_add hbase_pos _ _).symm
        _ = Real.rpow (profile.tree.base : ℝ)
              (1 - parameterSpacingStartIndex) := by congr 1 <;> ring
    rw [mul_assoc, hrewrite]
    norm_num [parameterSpacingStartIndex]
    have hmono :
        Real.rpow (profile.tree.base : ℝ) (-11) ≤
          Real.rpow 3 (-11) :=
      Real.rpow_le_rpow_of_nonpos
        (show (0 : ℝ) < 3 by norm_num)
        hbase_ge (show (-11 : ℝ) ≤ 0 by norm_num)
    norm_num [Real.rpow_neg (show (0 : ℝ) ≤ 3 by norm_num),
      Real.rpow_natCast] at hmono ⊢
    nlinarith
  have hblock_small :
      100 * blockScale ≤ 1 := by
    dsimp only [blockScale]
    calc
      100 *
            (90 * (profile.tree.base : ℝ) *
              Real.rpow (profile.tree.base : ℝ)
                (-(level : ℝ))) =
          100 * 90 * (profile.tree.base : ℝ) *
            Real.rpow (profile.tree.base : ℝ)
              (-(level : ℝ)) := by ring
      _ ≤
          100 * 90 * (profile.tree.base : ℝ) *
            Real.rpow (profile.tree.base : ℝ)
              (-(parameterSpacingStartIndex : ℝ)) := by
        gcongr
      _ ≤ 1 := hstart_numeric
  have hcontain :
      ∀ p ∈ points,
        dist p center ≤ blockScale / 10 := by
    intro p hp
    have hcell_grid :
        cell ∈
          cubicGridPartition profile.tree.base level
            clustered.points := by
      simpa [profile.tree.partition_eq] using hcell
    have hp_cell : p ∈ cell :=
      (Finset.mem_inter.mp hp).2
    have hcenter_cell : center ∈ cell :=
      (Finset.mem_inter.mp hcenter).2
    have hdist :=
      cubicGridPartition_cell_dist_lt
        (profile.tree.base_ge_three.trans' (by omega))
        hcell_grid hp_cell hcenter_cell
    have hdist' :
        dist p center <
          3 * Real.rpow (profile.tree.base : ℝ)
            (-(level : ℝ)) := by
      simpa [one_div, hmesh_eq] using hdist
    dsimp only [blockScale]
    have hbase_ge : (1 : ℝ) ≤ profile.tree.base := by
      exact_mod_cast
        (show 1 ≤ profile.tree.base from
          (by omega : 1 ≤ 3).trans
            profile.tree.base_ge_three)
    nlinarith
  have hpoints_subset :
      points ⊆ clustered.points := by
    intro point hpoint
    exact profile.tree.refined_subset
      (Finset.mem_inter.mp hpoint).1
  refine ⟨{
    cell := cell
    cell_mem := hcell
    points := points
    points_eq := rfl
    points_nonempty := hpoints_nonempty
    points_subset := hpoints_subset
    center := center
    center_mem := hcenter
    blockScale := blockScale
    blockScale_eq := rfl
    blockScale_pos := hscale_pos
    ten_delta_lt := hten_delta
    blockScale_small := hblock_small
    separated_scale := ?_
    points_containment := hcontain
  }⟩
  dsimp only [blockScale]
  convert hseparated using 1 <;> ring

end Kakeya.Assouad
