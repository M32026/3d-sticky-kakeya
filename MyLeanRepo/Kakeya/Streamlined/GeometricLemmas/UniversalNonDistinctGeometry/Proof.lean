import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.UniversalNonDistinctGeometry

namespace Kakeya.Streamlined

theorem universal_non_distinct_geometry :
    UniversalNonDistinctGeometryStatement := by
  intro rho hrho hrho1 T1 T2 h_non_ed
  let v : Point3 := -GeometricLemmas.tubeMidpoint T2
  let T1' := RandomTranslation.translateTube T1 v
  let T2' := RandomTranslation.translateTube T2 v
  have h_mid2 : GeometricLemmas.tubeMidpoint T2' = 0 := by
    simp [T2', RandomTranslation.translateTube,
      GeometricLemmas.tubeMidpoint, v]
  have h_m2 : ‖GeometricLemmas.tubeMidpoint T2'‖ ≤ 3 := by
    rw [h_mid2]
    norm_num
  have h_dist :
      dist (GeometricLemmas.tubeMidpoint T1)
          (GeometricLemmas.tubeMidpoint T2) ≤
        1 + 2 * rho :=
    GeneralizedFrostman.non_ed_midpoint_dist_le hrho hrho1 h_non_ed
  have h_mid1 :
      GeometricLemmas.tubeMidpoint T1' =
        GeometricLemmas.tubeMidpoint T1 -
          GeometricLemmas.tubeMidpoint T2 := by
    simp [T1', RandomTranslation.translateTube,
      GeometricLemmas.tubeMidpoint, v]
    abel
  have h_m1 : ‖GeometricLemmas.tubeMidpoint T1'‖ ≤ 3 := by
    rw [h_mid1]
    have h2 :
        ‖GeometricLemmas.tubeMidpoint T1 -
            GeometricLemmas.tubeMidpoint T2‖ ≤
          1 + 2 * rho := by
      simpa [dist_eq_norm] using h_dist
    linarith
  have h_non_ed' : ¬ T1'.EssentiallyDistinct T2' := by
    have h_iff :
        T1.EssentiallyDistinct T2 ↔ T1'.EssentiallyDistinct T2' :=
      rigidMoveTube_essentiallyDistinct T1 T2
        (1 : Point3 ≃ₗᵢ[ℝ] Point3) v
    exact h_iff.not.mp h_non_ed
  have h_result :=
    GeometricLemmas.non_distinct_local_geometry
      hrho hrho1 T1' T2' h_m1 h_m2 h_non_ed'
  have h_eq1 :
      GeometricLemmas.tubeMidpoint T1' -
          GeometricLemmas.tubeMidpoint T2' =
        GeometricLemmas.tubeMidpoint T1 -
          GeometricLemmas.tubeMidpoint T2 := by
    rw [h_mid1, h_mid2]
    abel
  have h_dir2 : T2'.direction = T2.direction := rfl
  have h_dir1 : T1'.direction = T1.direction := rfl
  have h_transverse :
      ‖(GeometricLemmas.tubeMidpoint T1 -
              GeometricLemmas.tubeMidpoint T2) -
          inner ℝ
              (GeometricLemmas.tubeMidpoint T1 -
                GeometricLemmas.tubeMidpoint T2)
              T2.direction • T2.direction‖ ≤
        1000 * rho := by
    rw [← h_eq1, ← h_dir2]
    exact h_result.1
  have h_direction :
      ‖T1.direction - T2.direction‖ ≤ 1000 * rho ∨
        ‖T1.direction + T2.direction‖ ≤ 1000 * rho := by
    rcases h_result.2.1 with h | h
    · left
      rw [h_dir1, h_dir2] at h
      exact h
    · right
      rw [h_dir1, h_dir2] at h
      exact h
  have h_containment' :
      T1'.carrier ⊆ dilatedTubeCarrier 1000 T2' :=
    h_result.2.2
  have h_car1 :
      T1'.carrier = RandomTranslation.translateSet T1.carrier v :=
    RandomTranslation.translateTube_carrier T1 v
  have h_car2 :
      dilatedTubeCarrier 1000 T2' =
        RandomTranslation.translateSet
          (dilatedTubeCarrier 1000 T2) v :=
    GeneralizedFrostman.dilatedTubeCarrier_translate T2 1000 v
  have h_subset :
      RandomTranslation.translateSet T1.carrier v ⊆
        RandomTranslation.translateSet
          (dilatedTubeCarrier 1000 T2) v := by
    rw [h_car1, h_car2] at h_containment'
    exact h_containment'
  have h_containment :
      T1.carrier ⊆ dilatedTubeCarrier 1000 T2 := by
    intro x hx
    have h1 : x + v ∈ RandomTranslation.translateSet T1.carrier v :=
      ⟨x, hx, by abel⟩
    have h2 :
        x + v ∈
          RandomTranslation.translateSet
            (dilatedTubeCarrier 1000 T2) v :=
      h_subset h1
    rcases h2 with ⟨y, hy, h_eq⟩
    have h3 : y = x := by
      simpa [add_left_inj] using h_eq
    exact h3 ▸ hy
  exact ⟨h_transverse, h_direction, h_containment⟩

end Kakeya.Streamlined
