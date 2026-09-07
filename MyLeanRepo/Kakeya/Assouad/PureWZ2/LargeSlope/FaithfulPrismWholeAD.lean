import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulPrismRawCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulPrismLocalAD
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening

/-!
# Local AD for the whole-cell faithful prism pieces

The local grain estimate is applied on genuine common-y companions.  Its
occupied anchor may lie in a positive-thickness neighbourhood of that slice;
points of the three-dimensional whole-cell piece are then compared with
same-label companions and transferred through a controlled thickening.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Common-y companions localised to the ball belonging to one faithful
prism. -/
def pureWZ2FaithfulPrismCommonCore
    {sigma loss delta rho : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    {common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope}
    (raw : PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common rho)
    (j : Fin raw.prismCount) : Set Point3 :=
  {point | point ∈ common.F2.union ∧
    pureWZ2HorizontalRotation frameSlope point 1 = common.y0} ∩
      Metric.closedBall (raw.sourcePoint j).1 (Real.sqrt (rho / 16))

private lemma pureWZ2_faithful_piece_subset_cfg
    {sigma loss delta rho : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    {common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope}
    (raw : PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common rho)
    (i : Fin cfg.family.card) (j : Fin raw.prismCount) :
    raw.piece i j ⊆ cfg.shading.union := by
  intro point hpoint
  have hF2 : point ∈ common.F2.carrier i := by
    rw [raw.piece_eq i j] at hpoint
    exact hpoint.1
  have hslab : point ∈ scaleData.slabShading.carrier i := by
    rw [common.F2_eq] at hF2
    exact wz2RefinedShading_subshading i hF2
  exact ⟨i, scaleData.slab_subshading i hslab⟩

private lemma pureWZ2_faithful_core_subset_cfg
    {sigma loss delta rho : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    {common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope}
    (raw : PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common rho)
    (j : Fin raw.prismCount) :
    pureWZ2FaithfulPrismCommonCore raw j ⊆ cfg.shading.union := by
  intro point hpoint
  rcases hpoint.1.1 with ⟨i, hF2⟩
  have hslab : point ∈ scaleData.slabShading.carrier i := by
    rw [common.F2_eq] at hF2
    exact wz2RefinedShading_subshading i hF2
  exact ⟨i, scaleData.slab_subshading i hslab⟩

private lemma pureWZ2_faithful_companion_mem_core
    {sigma loss delta rho : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    {common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope}
    (raw : PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common rho)
    (hrhoPos : 0 < rho)
    (hsqrtRho : Real.sqrt rho = 8 * scale.1)
    (hsmall : 256 * delta ≤ scale.1)
    (hscaleSmall : scale.1 ≤ 1 / 32)
    (j : Fin raw.prismCount) {point : Point3}
    (hpointF2 : point ∈ common.F2.union)
    (hpointPrism : point ∈ raw.prism j) :
    ∃ companion ∈ pureWZ2FaithfulPrismCommonCore raw j,
      ∃ label ∈ common.selectedLabels,
        point ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
        companion ∈ pureWZ2WeightedCroppedLabelRegion popular label := by
  rcases common.exists_common_slice_companion hpointF2 with
    ⟨label, hlabel, hpointLabel, companion, hcompanionLabel, hcompanionY⟩
  have hcompanionF2 : companion ∈ common.F2.union := by
    rw [common.F2_union_eq, common.selectedCells_eq]
    rw [pureWZ2WeightedCroppedLabelRegion_eq] at hcompanionLabel
    rcases Set.mem_iUnion₂.mp hcompanionLabel with ⟨cell, hfiber, hcell⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, Finset.mem_biUnion.mpr ⟨label, hlabel, hfiber⟩, hcell⟩
  have hsame := pureWZ2_weightedLabel_rotated_xz_diameter popular
    (common.selectedLabels_subset hlabel)
    raw.frameGap_nonneg
    (raw.selected_label_frame_close label hlabel)
    hpointLabel hcompanionLabel
  have hsourceNear := raw.source_near_prism j point hpointPrism
  let rotation := pureWZ2HorizontalRotation frameSlope
  have hx : |rotation companion 0 - rotation (raw.sourcePoint j).1 0| ≤
      scale.1 + 16 * delta + 4 * raw.frameGap := by
    calc
      |rotation companion 0 - rotation (raw.sourcePoint j).1 0| ≤
          |rotation companion 0 - rotation point 0| +
            |rotation point 0 - rotation (raw.sourcePoint j).1 0| := by
        simpa only [show rotation companion 0 - rotation (raw.sourcePoint j).1 0 =
            (rotation companion 0 - rotation point 0) +
              (rotation point 0 - rotation (raw.sourcePoint j).1 0) by ring]
          using abs_add_le _ _
      _ ≤ (8 * delta + 2 * raw.frameGap) +
          (scale.1 + (8 * delta + 2 * raw.frameGap)) := by
        exact add_le_add (by
          change |pureWZ2HorizontalRotation frameSlope companion 0 -
            pureWZ2HorizontalRotation frameSlope point 0| ≤
              8 * delta + 2 * raw.frameGap
          have hsame' := hsame.1
          rw [abs_sub_comm] at hsame'
          simpa using hsame')
          (by simpa [rotation, abs_sub_comm] using hsourceNear.1)
      _ = scale.1 + 16 * delta + 4 * raw.frameGap := by ring
  have hz : |rotation companion 2 - rotation (raw.sourcePoint j).1 2| ≤
      scale.1 + 16 * delta := by
    calc
      |rotation companion 2 - rotation (raw.sourcePoint j).1 2| ≤
          |rotation companion 2 - rotation point 2| +
            |rotation point 2 - rotation (raw.sourcePoint j).1 2| := by
        simpa only [show rotation companion 2 - rotation (raw.sourcePoint j).1 2 =
            (rotation companion 2 - rotation point 2) +
              (rotation point 2 - rotation (raw.sourcePoint j).1 2) by ring]
          using abs_add_le _ _
      _ ≤ 8 * delta + (scale.1 + 8 * delta) := by
        exact add_le_add (by
          change |pureWZ2HorizontalRotation frameSlope companion 2 -
            pureWZ2HorizontalRotation frameSlope point 2| ≤ 8 * delta
          simpa [abs_sub_comm] using hsame.2)
          (by simpa [rotation, abs_sub_comm] using hsourceNear.2)
      _ = scale.1 + 16 * delta := by ring
  have hy : |rotation companion 1 - rotation (raw.sourcePoint j).1 1| ≤
      scale.1 := by
    rw [hcompanionY]
    simpa [abs_sub_comm, rotation] using raw.source_near_common_y j
  have hnormSq :
      ‖rotation companion - rotation (raw.sourcePoint j).1‖ ^ 2 =
        (rotation companion 0 - rotation (raw.sourcePoint j).1 0) ^ 2 +
        (rotation companion 1 - rotation (raw.sourcePoint j).1 1) ^ 2 +
        (rotation companion 2 - rotation (raw.sourcePoint j).1 2) ^ 2 := by
    rw [point3_coord_norm_sq]
    rfl
  have hnorm :
      ‖rotation companion - rotation (raw.sourcePoint j).1‖ ≤ 2 * scale.1 := by
    have hdelta16 : 16 * delta ≤ scale.1 / 16 := by
      linarith [hsmall]
    have hgap4 : 4 * raw.frameGap ≤ scale.1 / 4 :=
      raw.frameGap_small
    have hx' : |rotation companion 0 - rotation (raw.sourcePoint j).1 0| ≤
        (21 / 16 : ℝ) * scale.1 :=
      hx.trans (by linarith)
    have hz' : |rotation companion 2 - rotation (raw.sourcePoint j).1 2| ≤
        (17 / 16 : ℝ) * scale.1 :=
      hz.trans (by linarith)
    have hxBounds := abs_le.mp hx'
    have hyBounds := abs_le.mp hy
    have hzBounds := abs_le.mp hz'
    have hscalePos : 0 < scale.1 :=
      cfg.extremal.delta_pos.trans_le scale.2.1
    have hsq :
        ‖rotation companion - rotation (raw.sourcePoint j).1‖ ^ 2 ≤
          (2 * scale.1) ^ 2 := by
      rw [hnormSq]
      nlinarith [sq_nonneg
        (rotation companion 0 - rotation (raw.sourcePoint j).1 0),
        sq_nonneg
          (rotation companion 1 - rotation (raw.sourcePoint j).1 1),
        sq_nonneg
          (rotation companion 2 - rotation (raw.sourcePoint j).1 2),
        hscalePos]
    nlinarith [norm_nonneg
      (rotation companion - rotation (raw.sourcePoint j).1)]
  have hsqrtBase : Real.sqrt (rho / 16) = 2 * scale.1 := by
    rw [Real.sqrt_div hrhoPos.le, hsqrtRho]
    norm_num
    ring
  have hball : companion ∈
      Metric.closedBall (raw.sourcePoint j).1 (Real.sqrt (rho / 16)) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← rotation.norm_map,
      rotation.map_sub, hsqrtBase]
    exact hnorm
  refine ⟨companion, ⟨⟨hcompanionF2, hcompanionY⟩, hball⟩,
    label, hlabel, hpointLabel, hcompanionLabel⟩

/-- Whole three-dimensional faithful pieces inherit local AD from their
common-y companions. -/
theorem PureWZ2FaithfulRawPrismCover.piece_local_ad_of_frame_lower
    {sigma loss delta rho eta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    {common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope}
    (raw : PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common rho)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hrhoPos : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaBase : delta ≤ rho / 16)
    (hsqrtRho : Real.sqrt rho = 8 * scale.1)
    (hsmall : 256 * delta ≤ scale.1)
    (hscaleSmall : scale.1 ≤ 1 / 32)
    (hconstant :
      (36 : ENNReal) * (20 * Kakeya.realRpowENN delta (-loss)) ≤
        Kakeya.realRpowENN delta (-(12 * eta)))
    (i : Fin cfg.family.card) (j : Fin raw.prismCount) :
    IsADSet1 (scalarProjection (raw.prismNormal j) (raw.piece i j))
      rho (1 - sigma) (Kakeya.realRpowENN delta (-(12 * eta))) := by
  have hsourceFrame :
      |cfg.globalGrains.slope ((raw.sourcePoint j).1 2) - frameSlope| ≤
        1 / 25 := by
    have hclose :=
      common.selected_source_frame_close_of_gap
        raw.selected_label_frame_close (raw.sourceLabel j).2
        (raw.source_mem_label j)
    have hraw : delta / 2 + raw.frameGap ≤ 1 / 25 := by
      have hdeltaHalf : delta / 2 ≤ scale.1 / 512 := by
        linarith [hsmall]
      have hgap : raw.frameGap ≤ scale.1 / 16 := by
        linarith [raw.frameGap_small]
      linarith [hscaleSmall]
    exact hclose.trans hraw
  have hframeLower := raw.source_frame_projected_lower j
  have hframePos : 0 < ‖pureWZ2FrameProjectedNormal frameSlope
      (cfg.localGrains.planeMap (raw.sourcePoint j))‖ :=
    lt_of_lt_of_le (by norm_num) hframeLower
  have hnormalUnit : ‖raw.prismNormal j‖ = 1 := by
    rw [raw.prismNormal_eq j]
    exact pureWZ2NormalizedFrameProjectedNormal_unit hframePos
  have hnormalY : pureWZ2HorizontalRotation frameSlope
      (raw.prismNormal j) 1 = 0 := by
    rw [raw.prismNormal_eq j]
    exact pureWZ2FrameProjectedNormal_rotated_y_zero _ _
  let core := pureWZ2FaithfulPrismCommonCore raw j
  have hcoreAD : IsADSet1
      (scalarProjection (raw.prismNormal j) core) rho (1 - sigma)
        (20 * Kakeya.realRpowENN delta (-loss)) := by
    have hrawAD := pureWZ2_common_rotated_slice_local_ad_of_frame_lower cfg
      (raw.sourcePoint j).1 (raw.sourcePoint j).2 hframeLower
      hrhoPos hrhoOne hdeltaBase core
      (pureWZ2_faithful_core_subset_cfg raw j)
      (by intro point hpoint; exact hpoint.2)
      (by intro point hpoint; exact hpoint.1.2)
    simpa [core, raw.prismNormal_eq j] using hrawAD
  let thickness : ℝ := 16 * delta + 2 * raw.frameGap
  have hthick : scalarProjection (raw.prismNormal j) (raw.piece i j) ⊆
      Metric.cthickening thickness
        (scalarProjection (raw.prismNormal j) core) := by
    rintro value ⟨point, hpoint, rfl⟩
    have hpointF2 : point ∈ common.F2.union := by
      rw [raw.piece_eq i j] at hpoint
      exact ⟨i, hpoint.1⟩
    have hpointPrism : point ∈ raw.prism j := by
      rw [raw.piece_eq i j] at hpoint
      exact hpoint.2
    rcases pureWZ2_faithful_companion_mem_core raw hrhoPos hsqrtRho hsmall
        hscaleSmall j hpointF2 hpointPrism with
      ⟨companion, hcompanionCore, label, hlabel, hpointLabel,
        hcompanionLabel⟩
    have hprojection := pureWZ2_weightedLabel_projection_diameter popular
      (common.selectedLabels_subset hlabel)
      raw.frameGap_nonneg
      (raw.selected_label_frame_close label hlabel)
      hnormalUnit hnormalY hpointLabel hcompanionLabel
    have hcompanionProjection : inner ℝ companion (raw.prismNormal j) ∈
        scalarProjection (raw.prismNormal j) core :=
      ⟨companion, hcompanionCore, rfl⟩
    exact Metric.mem_cthickening_of_dist_le _ _ _ _ hcompanionProjection
      (by
        rw [Real.dist_eq]
        dsimp only [thickness]
        convert hprojection using 1 <;> ring)
  have hpieceBounded : scalarProjection (raw.prismNormal j)
      (raw.piece i j) ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hcfg := pureWZ2_faithful_piece_subset_cfg raw i j hpoint
    rcases hcfg with ⟨index, hcarrier⟩
    have hbox := (cfg.shading.subset_body index hcarrier).2
    have hpointNorm : ‖point‖ ≤ Real.sqrt 3 := by
      have hnormSq := point3_coord_norm_sq point
      have hx : |point 0| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.1
      have hy : |point 1| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      have hz : |point 2| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
      have hsq : ‖point‖ ^ 2 ≤ 3 := by
        rw [hnormSq]
        nlinarith [sq_abs (point 0), sq_abs (point 1), sq_abs (point 2),
          abs_nonneg (point 0), abs_nonneg (point 1), abs_nonneg (point 2)]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3, norm_nonneg point]
    have hinner := abs_real_inner_le_norm point (raw.prismNormal j)
    rw [hnormalUnit, mul_one] at hinner
    have hfour : Real.sqrt 3 ≤ 4 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    exact abs_le.mp (hinner.trans (hpointNorm.trans hfour))
  have hthickAD := hcoreAD.generalized_thickening hthick hpieceBounded
    hrhoPos (by
      dsimp only [thickness]
      exact add_pos_of_pos_of_nonneg
        (mul_pos (by norm_num) cfg.extremal.delta_pos)
        (mul_nonneg (by norm_num) raw.frameGap_nonneg))
  have hrhoEq : rho = 64 * scale.1 ^ 2 := by
    have hsqrtSq := Real.sq_sqrt hrhoPos.le
    nlinarith
  have hceil : Nat.ceil (thickness / rho) ≤ 2 := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hrhoPos).2
    dsimp only [thickness]
    calc
      16 * delta + 2 * raw.frameGap ≤ rho + rho := by
        apply add_le_add
        · nlinarith [hdeltaBase]
        · exact raw.frameGap_le_rho
      _ = 2 * rho := by ring
  have hfactor :
      (2 * (Nat.ceil (thickness / rho) + 1) : ENNReal) ^ 2 ≤ 36 := by
    have hlinearNat :
        2 * (Nat.ceil (thickness / rho) + 1) ≤ 6 := by omega
    have hlinear :
        (2 * (Nat.ceil (thickness / rho) + 1) : ENNReal) ≤ 6 := by
      exact_mod_cast hlinearNat
    calc
      (2 * (Nat.ceil (thickness / rho) + 1) : ENNReal) ^ 2 ≤
          (6 : ENNReal) ^ 2 := by gcongr
      _ = 36 := by norm_num
  apply IsADSet1.mono_constant hthickAD
  exact (mul_le_mul_right' hfactor
    (20 * Kakeya.realRpowENN delta (-loss))).trans hconstant

/-- Compatibility wrapper retaining the previous public signature. -/
theorem PureWZ2FaithfulRawPrismCover.piece_local_ad
    {sigma loss delta rho eta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    {common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope}
    (raw : PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common rho)
    (_compatibility : PureWZ2LocalGlobalCompatibility cfg)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hrhoPos : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaBase : delta ≤ rho / 16)
    (hsqrtRho : Real.sqrt rho = 8 * scale.1)
    (hsmall : 256 * delta ≤ scale.1)
    (hscaleSmall : scale.1 ≤ 1 / 32)
    (hconstant :
      (36 : ENNReal) * (20 * Kakeya.realRpowENN delta (-loss)) ≤
        Kakeya.realRpowENN delta (-(12 * eta)))
    (i : Fin cfg.family.card) (j : Fin raw.prismCount) :
    IsADSet1 (scalarProjection (raw.prismNormal j) (raw.piece i j))
      rho (1 - sigma) (Kakeya.realRpowENN delta (-(12 * eta))) :=
  raw.piece_local_ad_of_frame_lower hdeltaSmall hrhoPos hrhoOne hdeltaBase
    hsqrtRho hsmall hscaleSmall hconstant i j

end Kakeya.Assouad

end
