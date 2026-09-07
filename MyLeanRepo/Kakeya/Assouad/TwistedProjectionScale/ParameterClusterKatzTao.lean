import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanToKatzTaoNoSep
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Bounds
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFrostmanStatement

/-!
# Katz--Tao extraction from weighted parameter clusters

This conditional adapter consumes the replication-invariant weighted cluster
package.  It extracts a Katz--Tao subset and restricts the same source shading
to exactly those clusters, retaining mass by the two-sided cluster weights.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Restrict a clustered shading to tubes assigned to selected centers. -/
def parameterClusterRestrictedShading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal} {w : ℝ}
    (data : TubeParameterClusterFrostmanData F Y C lambda w)
    (selected : DiscreteSet 3) :
    Kakeya.Streamlined.TubeShading F where
  carrier i :=
    if data.assign i ∈ selected then data.shading.carrier i else ∅
  measurable_carrier i := by
    by_cases hi : data.assign i ∈ selected
    · simp [hi, data.shading.measurable_carrier]
    · simp [hi]
  subset_body i := by
    by_cases hi : data.assign i ∈ selected
    · simpa [hi] using data.shading.subset_body i
    · simp [hi]

lemma parameterClusterRestrictedShading_subshading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal} {w : ℝ}
    (data : TubeParameterClusterFrostmanData F Y C lambda w)
    (selected : DiscreteSet 3) :
    IsSubshading
      (parameterClusterRestrictedShading data selected)
      data.shading := by
  intro i
  by_cases hi : data.assign i ∈ selected
  · simp [parameterClusterRestrictedShading, hi]
  · simp [parameterClusterRestrictedShading, hi]

private lemma restricted_mass_eq_cluster_sum
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal} {w : ℝ}
    (data : TubeParameterClusterFrostmanData F Y C lambda w)
    (selected : DiscreteSet 3) :
    (parameterClusterRestrictedShading data selected).mass =
      ∑ p ∈ selected,
        tubeParameterAssignedClusterMass
          data.shading data.assign p := by
  classical
  simp only [Kakeya.Streamlined.Shading.mass,
    parameterClusterRestrictedShading,
    tubeParameterAssignedClusterMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : data.assign i ∈ selected
  · simp [hi]
  · simp [hi]

private lemma clustered_mass_eq_cluster_sum
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal} {w : ℝ}
    (data : TubeParameterClusterFrostmanData F Y C lambda w) :
    data.shading.mass =
      ∑ p ∈ data.points,
        tubeParameterAssignedClusterMass
          data.shading data.assign p := by
  classical
  simp only [Kakeya.Streamlined.Shading.mass,
    tubeParameterAssignedClusterMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : data.shading.carrier i = ∅
  · have hvol : MeasureTheory.volume (data.shading.carrier i) = 0 := by
      rw [hi]
      simp
    simp [hvol]
  · have hassign : data.assign i ∈ data.points :=
      data.assign_mem i hi
    simp [hassign]

/-- The extracted Katz--Tao subset together with its retained source shading. -/
structure TubeParameterClusterKatzTaoData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal} {clusterScale cinematicScale s : ℝ}
    (clustered :
      TubeParameterClusterFrostmanData F Y C lambda clusterScale) where
  extractionConstant : ENNReal
  extractionConstant_one : 1 ≤ extractionConstant
  extractionConstant_ne_top : extractionConstant ≠ ⊤
  points : DiscreteSet 3
  points_nonempty : points.Nonempty
  points_subset : points ⊆ clustered.points
  points_katzTao : points.IsKatzTao cinematicScale 1 100
  points_card_lower :
    Kakeya.realRpowENN cinematicScale (-s) ≤
      extractionConstant *
        ENNReal.ofReal (1 + Real.log cinematicScale⁻¹) *
        tubeParameterClusterFrostmanConstant
          C clustered.regularizationLoss lambda *
        points.enncard
  shading : Kakeya.Streamlined.TubeShading F
  shading_eq :
    shading = parameterClusterRestrictedShading clustered points
  subshading : IsSubshading shading Y
  mass_retention :
    points.enncard * clustered.shading.mass ≤
      2 * clustered.points.enncard * shading.mass
  assign_mem :
    ∀ i, shading.carrier i ≠ ∅ → clustered.assign i ∈ points
  assign_close :
    ∀ i, shading.carrier i ≠ ∅ →
      dist (tubeParameterPoint3 i) (clustered.assign i) ≤ clusterScale
  selected_source :
    ∀ p ∈ points,
      ∃ i : Fin F.card,
        shading.carrier i ≠ ∅ ∧
          clustered.assign i = p ∧
          dist (tubeParameterPoint3 i) p ≤ clusterScale
  center_source :
    ∀ p ∈ points,
      ∃ i : Fin F.card, tubeParameterPoint3 i = p

private lemma cluster_points_large_enough
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal} {clusterScale cinematicScale s : ℝ}
    (data :
      TubeParameterClusterFrostmanData F Y C lambda clusterScale)
    (hcluster : 0 < clusterScale)
    (hC_zero : C ≠ 0)
    (hC_top : C ≠ ⊤)
    (hL_zero : data.regularizationLoss ≠ 0)
    (hscale :
      100000 * data.regularizationLoss * C *
          Kakeya.realRpowENN clusterScale 2 *
          Kakeya.realRpowENN cinematicScale (-s) ≤ lambda) :
    Kakeya.realRpowENN cinematicScale (-s) ≤
      data.points.enncard := by
  let factor : ENNReal :=
    100000 * data.regularizationLoss * C *
      Kakeya.realRpowENN clusterScale 2
  have hcluster2_zero :
      Kakeya.realRpowENN clusterScale 2 ≠ 0 := by
    simp [Kakeya.realRpowENN, hcluster.ne']
  have hcluster2_top :
      Kakeya.realRpowENN clusterScale 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hfactor_zero : factor ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hL_zero) hC_zero)
      hcluster2_zero
  have hfactor_top : factor ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          data.regularizationLoss_ne_top) hC_top)
      hcluster2_top
  have hchain :
      factor * Kakeya.realRpowENN cinematicScale (-s) ≤
        factor * data.points.enncard := by
    calc
      factor * Kakeya.realRpowENN cinematicScale (-s) =
          100000 * data.regularizationLoss * C *
            Kakeya.realRpowENN clusterScale 2 *
            Kakeya.realRpowENN cinematicScale (-s) := by
        simp [factor, mul_assoc]
      _ ≤ lambda := hscale
      _ ≤ factor * data.points.enncard := by
        simpa [factor, mul_assoc] using data.points_card_lower
  exact
    (ENNReal.mul_le_mul_iff_left hfactor_zero hfactor_top).mp
      (by simpa [mul_comm] using hchain)

/--
Extract a fixed-constant Katz--Tao set and restrict the same source shading to
the selected clusters.
-/
theorem tube_parameter_cluster_katz_tao
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal} {clusterScale cinematicScale s : ℝ}
    (clustered :
      TubeParameterClusterFrostmanData F Y C lambda clusterScale)
    (hcluster : 0 < clusterScale)
    (hcinematic : 0 < cinematicScale)
    (hcinematic_one : cinematicScale < 1)
    (hscale_order : clusterScale ≤ cinematicScale)
    (hs : 0 < s) (hs_one : s ≤ 1)
    (hC_zero : C ≠ 0) (hC_top : C ≠ ⊤)
    (hscale :
      100000 * clustered.regularizationLoss * C *
          Kakeya.realRpowENN clusterScale 2 *
          Kakeya.realRpowENN cinematicScale (-s) ≤ lambda) :
    Nonempty
      (TubeParameterClusterKatzTaoData
        (cinematicScale := cinematicScale) (s := s) clustered) := by
  have hL_zero : clustered.regularizationLoss ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num)
      clustered.regularizationLoss_one)
  have hlarge :
      Kakeya.realRpowENN cinematicScale (-s) ≤
        clustered.points.enncard :=
    cluster_points_large_enough clustered hcluster
      hC_zero hC_top hL_zero hscale
  have hfrostman_cinematic :
      clustered.points.IsFrostman cinematicScale 1
        (tubeParameterClusterFrostmanConstant
          C clustered.regularizationLoss lambda) := by
    intro x r hcin_r hr_one
    exact clustered.points_frostman x r
      (hscale_order.trans hcin_r) hr_one
  have hfrostman_s :
      clustered.points.IsFrostman cinematicScale s
        (tubeParameterClusterFrostmanConstant
          C clustered.regularizationLoss lambda) :=
    frostman_exponent_reduction hfrostman_cinematic
      hcinematic hs.le hs_one
  rcases frostman_to_katz_tao_no_sep 3 s hs
      (hs_one.trans (by norm_num)) with
    ⟨D, hD_one, hD_top, hExtract⟩
  rcases hExtract cinematicScale
      (tubeParameterClusterFrostmanConstant
        C clustered.regularizationLoss lambda)
      hcinematic hcinematic_one clustered.frostmanConstant_one
      clustered.frostmanConstant_ne_top clustered.points
      clustered.points_nonempty clustered.points_in_unitBall
      hfrostman_s hlarge with
    ⟨points, hpoints_nonempty, hpoints_subset, hpoints_kt, hpoints_card⟩
  have hpoints_kt_one :
      points.IsKatzTao cinematicScale 1 100 := by
    intro x r hwr hr_one
    have hcount := hpoints_kt x r hwr hr_one
    have hbase : 1 ≤ r / cinematicScale :=
      (le_div_iff₀ hcinematic).mpr (by simpa using hwr)
    have hpow :
        Kakeya.realRpowENN (r / cinematicScale) s ≤
          Kakeya.realRpowENN (r / cinematicScale) 1 := by
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_mono
        (Real.rpow_le_rpow_of_exponent_le hbase hs_one)
    exact hcount.trans (by gcongr)
  let shading := parameterClusterRestrictedShading clustered points
  have hshading_sub_clustered :
      IsSubshading shading clustered.shading :=
    parameterClusterRestrictedShading_subshading clustered points
  have hshading_sub_Y : IsSubshading shading Y := by
    intro i
    exact (hshading_sub_clustered i).trans (clustered.subshading i)
  have hrestricted_mass :
      shading.mass =
        ∑ p ∈ points,
          tubeParameterAssignedClusterMass
            clustered.shading clustered.assign p :=
    restricted_mass_eq_cluster_sum clustered points
  have hclustered_mass :
      clustered.shading.mass =
        ∑ p ∈ clustered.points,
          tubeParameterAssignedClusterMass
            clustered.shading clustered.assign p :=
    clustered_mass_eq_cluster_sum clustered
  have hnew_lower :
      points.enncard * clustered.clusterMass ≤ shading.mass := by
    rw [hrestricted_mass]
    have hsum :
        ∑ p ∈ points, clustered.clusterMass ≤
          ∑ p ∈ points,
            tubeParameterAssignedClusterMass
              clustered.shading clustered.assign p :=
      Finset.sum_le_sum fun p hp =>
        clustered.cluster_mass_lower p (hpoints_subset hp)
    simpa [DiscreteSet.enncard, Finset.sum_const, nsmul_eq_mul,
      mul_comm] using hsum
  have hold_upper :
      clustered.shading.mass ≤
        2 * clustered.clusterMass * clustered.points.enncard := by
    rw [hclustered_mass]
    have hsum :
        ∑ p ∈ clustered.points,
            tubeParameterAssignedClusterMass
              clustered.shading clustered.assign p ≤
          ∑ p ∈ clustered.points, 2 * clustered.clusterMass :=
      Finset.sum_le_sum fun p hp =>
        clustered.cluster_mass_upper p hp
    simpa [DiscreteSet.enncard, Finset.sum_const, nsmul_eq_mul,
      mul_comm, mul_assoc] using hsum
  have hmass :
      points.enncard * clustered.shading.mass ≤
        2 * clustered.points.enncard * shading.mass := by
    calc
      points.enncard * clustered.shading.mass ≤
          points.enncard *
            (2 * clustered.clusterMass * clustered.points.enncard) := by
        gcongr
      _ = 2 * clustered.points.enncard *
          (points.enncard * clustered.clusterMass) := by ring
      _ ≤ 2 * clustered.points.enncard * shading.mass := by
        gcongr
  have hassign_mem :
      ∀ i, shading.carrier i ≠ ∅ → clustered.assign i ∈ points := by
    intro i hi
    by_contra hnot
    have hempty : shading.carrier i = ∅ := by
      simp [shading, parameterClusterRestrictedShading, hnot]
    exact hi hempty
  have hsource :
      ∀ p ∈ points,
        ∃ i : Fin F.card,
          shading.carrier i ≠ ∅ ∧
            clustered.assign i = p ∧
            dist (tubeParameterPoint3 i) p ≤ clusterScale := by
    intro p hp
    have hcluster_pos :
        0 <
          tubeParameterAssignedClusterMass
            clustered.shading clustered.assign p :=
      clustered.clusterMass_pos.trans_le
        (clustered.cluster_mass_lower p (hpoints_subset hp))
    simp only [tubeParameterAssignedClusterMass] at hcluster_pos
    rcases Finset.sum_pos_iff.mp hcluster_pos with
      ⟨i, _, hi_pos⟩
    have hassign_eq : clustered.assign i = p := by
      by_contra hne
      simp [hne] at hi_pos
    have hi : clustered.shading.carrier i ≠ ∅ := by
      intro hempty
      rw [hempty] at hi_pos
      simp at hi_pos
    have hcarrier : shading.carrier i = clustered.shading.carrier i := by
      simp [shading, parameterClusterRestrictedShading, hassign_eq, hp]
    exact
      ⟨i, by rwa [hcarrier], hassign_eq,
        by simpa [hassign_eq] using clustered.assign_close i hi⟩
  have hassign_close :
      ∀ i, shading.carrier i ≠ ∅ →
        dist (tubeParameterPoint3 i) (clustered.assign i) ≤
          clusterScale := by
    intro i hi
    have hmem : clustered.assign i ∈ points := hassign_mem i hi
    have hcarrier :
        shading.carrier i = clustered.shading.carrier i := by
      simp [shading, parameterClusterRestrictedShading, hmem]
    have hi_clustered : clustered.shading.carrier i ≠ ∅ := by
      rwa [← hcarrier]
    exact clustered.assign_close i hi_clustered
  have hcenter_source :
      ∀ p ∈ points,
        ∃ i : Fin F.card, tubeParameterPoint3 i = p := by
    intro p hp
    rcases clustered.point_source p (hpoints_subset hp) with
      ⟨i, _, _, hpi⟩
    exact ⟨i, hpi⟩
  exact ⟨{
    extractionConstant := D
    extractionConstant_one := hD_one
    extractionConstant_ne_top := hD_top
    points := points
    points_nonempty := hpoints_nonempty
    points_subset := hpoints_subset
    points_katzTao := hpoints_kt_one
    points_card_lower := hpoints_card
    shading := shading
    shading_eq := rfl
    subshading := hshading_sub_Y
    mass_retention := hmass
    assign_mem := hassign_mem
    assign_close := hassign_close
    selected_source := hsource
    center_source := hcenter_source
  }⟩

end Kakeya.Assouad
