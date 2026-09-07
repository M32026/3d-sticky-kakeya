import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves

/-!
# Normalized Katz--Tao cardinality inside one coarse tube

This target converts the quadratic-volume convex container from the
paper-faithful (B.32) grouping into the local cardinality bound consumed by
the low hair-density branch.
-/

namespace Kakeya.Assouad

theorem hairbrush_coarse_tube_katz_tao_cardinality :
    HairbrushCoarseTubeKatzTaoCardinalityStatement := by
  intro δ eta stopLoss katzTaoConstant hδ hK F Y hKT angular coarse hvol j
  let G := coarse.grouping.family j
  let W := coarse.container j
  have hG_subset : G ⊆ F := coarse.grouping.family_subset j
  have h_contain : ∀ T ∈ G, T.carrier ⊆ W :=
    fun T hT => coarse.container_containment j T hT
  classical
  let filtered := F.filter (fun T : Kakeya.DeltaTube δ => T.carrier ⊆ W)
  have h1 : G ⊆ filtered := by
    intro T hT
    exact Finset.mem_filter.mpr ⟨hG_subset hT, h_contain T hT⟩
  have h_card : G.card ≤ filtered.card := Finset.card_le_card h1
  have h2 : G.enncard ≤ F.containedCount W := by
    simpa [Kakeya.TubeFamily.enncard, Kakeya.TubeFamily.containedCount] using h_card
  have h3 : F.containedCount W ≤
      ENNReal.ofReal katzTaoConstant * MeasureTheory.volume W * (Kakeya.deltaTubeVolume δ)⁻¹ :=
    hKT W (coarse.container_convex j)
  have h4 : MeasureTheory.volume W ≤ ENNReal.ofReal (1000000 * angular.capRadius ^ 2) :=
    coarse.container_volume j
  have hcap_pos : 0 < angular.capRadius := by
    have h : angular.theta ≤ angular.capRadius := angular.theta_le_capRadius
    have h' : 0 < angular.theta := by linarith [angular.delta_le_theta]
    linarith
  have h5 : angular.capRadius ≤ 6 * angular.theta := angular.capRadius_le_six_theta
  have h6 : 1000000 * angular.capRadius ^ 2 ≤ 36000000 * angular.theta ^ 2 := by
    have h7 : angular.capRadius ^ 2 ≤ (6 * angular.theta) ^ 2 := by gcongr
    linarith
  have h8 : MeasureTheory.volume W ≤ ENNReal.ofReal (36000000 * angular.theta ^ 2) :=
    h4.trans (ENNReal.ofReal_mono h6)
  have hδ2_pos : 0 < δ ^ 2 := by positivity
  have h9 : (Kakeya.deltaTubeVolume δ)⁻¹ ≤ (ENNReal.ofReal (δ ^ 2))⁻¹ :=
    ENNReal.inv_le_inv.mpr hvol
  have h101 : (δ ^ 2)⁻¹ = 1 / δ ^ 2 := by field_simp
  have h10 : (ENNReal.ofReal (δ ^ 2))⁻¹ = ENNReal.ofReal (1 / δ ^ 2) := by
    have h : (ENNReal.ofReal (δ ^ 2))⁻¹ = ENNReal.ofReal ((δ ^ 2)⁻¹) :=
      Eq.symm (ENNReal.ofReal_inv_of_pos hδ2_pos)
    rw [h, h101]
  have h11 : (Kakeya.deltaTubeVolume δ)⁻¹ ≤ ENNReal.ofReal (1 / δ ^ 2) :=
    h9.trans (le_of_eq h10)
  have h_main : G.enncard ≤
      ENNReal.ofReal katzTaoConstant * ENNReal.ofReal (36000000 * angular.theta ^ 2) *
        ENNReal.ofReal (1 / δ ^ 2) := by
    calc
      G.enncard ≤ F.containedCount W := h2
      _ ≤ ENNReal.ofReal katzTaoConstant * MeasureTheory.volume W *
            (Kakeya.deltaTubeVolume δ)⁻¹ := h3
      _ ≤ ENNReal.ofReal katzTaoConstant * ENNReal.ofReal (36000000 * angular.theta ^ 2) *
            ENNReal.ofReal (1 / δ ^ 2) := by
        gcongr
  have htheta_pos : 0 < angular.theta := by linarith [angular.delta_le_theta]
  have h_vol2 : 0 ≤ 36000000 * angular.theta ^ 2 := by positivity
  have h14 : 36000000 * angular.theta ^ 2 * (1 / δ ^ 2) ≤
      100000000 * ((angular.theta / δ) ^ 2) := by
    have h15 : (angular.theta / δ) ^ 2 = angular.theta ^ 2 / δ ^ 2 := by field_simp
    rw [h15]
    have h16 : 36000000 * angular.theta ^ 2 * (1 / δ ^ 2) =
        36000000 * (angular.theta ^ 2 / δ ^ 2) := by field_simp
    rw [h16]
    have h17 : 0 ≤ angular.theta ^ 2 / δ ^ 2 := by positivity
    nlinarith
  have h18 : ENNReal.ofReal (36000000 * angular.theta ^ 2) * ENNReal.ofReal (1 / δ ^ 2) ≤
      ENNReal.ofReal 100000000 * ENNReal.ofReal ((angular.theta / δ) ^ 2) := by
    have h19 : ENNReal.ofReal (36000000 * angular.theta ^ 2) * ENNReal.ofReal (1 / δ ^ 2) =
        ENNReal.ofReal (36000000 * angular.theta ^ 2 * (1 / δ ^ 2)) := by
      rw [← ENNReal.ofReal_mul h_vol2]
    have h20 : ENNReal.ofReal 100000000 * ENNReal.ofReal ((angular.theta / δ) ^ 2) =
        ENNReal.ofReal (100000000 * ((angular.theta / δ) ^ 2)) := by
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 100000000 by norm_num)]
    rw [h19, h20]
    exact ENNReal.ofReal_mono h14
  have h21 : ENNReal.ofReal katzTaoConstant *
        (ENNReal.ofReal (36000000 * angular.theta ^ 2) * ENNReal.ofReal (1 / δ ^ 2)) ≤
      ENNReal.ofReal katzTaoConstant *
        (ENNReal.ofReal 100000000 * ENNReal.ofReal ((angular.theta / δ) ^ 2)) := by
    gcongr
  have h22 : ENNReal.ofReal katzTaoConstant * ENNReal.ofReal (36000000 * angular.theta ^ 2) *
        ENNReal.ofReal (1 / δ ^ 2) =
      ENNReal.ofReal katzTaoConstant *
        (ENNReal.ofReal (36000000 * angular.theta ^ 2) * ENNReal.ofReal (1 / δ ^ 2)) := by
    simp [mul_assoc]
  rw [h22] at h_main
  have h24 : G.enncard ≤ ENNReal.ofReal katzTaoConstant *
        (ENNReal.ofReal 100000000 * ENNReal.ofReal ((angular.theta / δ) ^ 2)) :=
    h_main.trans h21
  have h25 : ENNReal.ofReal katzTaoConstant *
        (ENNReal.ofReal 100000000 * ENNReal.ofReal ((angular.theta / δ) ^ 2)) =
      ENNReal.ofReal 100000000 * ENNReal.ofReal katzTaoConstant *
        ENNReal.ofReal ((angular.theta / δ) ^ 2) := by
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [h25] at h24
  exact h24

end Kakeya.Assouad
