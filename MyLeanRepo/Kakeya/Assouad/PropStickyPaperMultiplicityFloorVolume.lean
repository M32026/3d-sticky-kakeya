import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolumeStatements

/-!
# Union-volume upper bound from a multiplicity floor

The integral of point multiplicity is the total shaded mass.  Therefore a
uniform multiplicity floor on the shaded union converts a mass upper bound
into an upper bound for the union volume.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

lemma lintegral_pointMultiplicity_eq_setLIntegral
    {BF : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading BF) :
    (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) =
      ∫⁻ p in Y.union, (Y.pointMultiplicity p : ENNReal) := by
  have h_zero_outside :
      ∀ p, p ∉ Y.union → (Y.pointMultiplicity p : ENNReal) = 0 := by
    intro p hp
    have h_i : ∀ (i : Fin BF.card), p ∉ Y.carrier i := by
      intro i h_in
      have h_in_union : p ∈ Y.union := by
        simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
        exact ⟨i, h_in⟩
      exact hp h_in_union
    have h_sum :
        (∑ i : Fin BF.card,
          (Y.carrier i).indicator
            (fun _ : Point3 => (1 : ENNReal)) p) = 0 := by
      classical
      apply Finset.sum_eq_zero
      intro i _
      have h_ind :
          (Y.carrier i).indicator
              (fun _ : Point3 => (1 : ENNReal)) p =
            0 := by
        simp [h_i i]
      exact h_ind
    have h_eq2 :
        (Y.pointMultiplicity p : ENNReal) =
          ∑ i : Fin BF.card,
            (Y.carrier i).indicator
              (fun _ : Point3 => (1 : ENNReal)) p :=
      coe_pointMultiplicity_eq_sum_indicator Y p
    rw [h_eq2, h_sum]
  have h_indicator :
      ∀ p : Point3,
        (Y.pointMultiplicity p : ENNReal) =
          (Y.union).indicator
            (fun p : Point3 =>
              (Y.pointMultiplicity p : ENNReal)) p := by
    intro p
    by_cases hmem : p ∈ Y.union
    · simp [hmem]
    · have hz :
          (Y.pointMultiplicity p : ENNReal) = 0 :=
        h_zero_outside p hmem
      simp [hmem, hz]
  rw [lintegral_congr h_indicator]
  rw [lintegral_indicator (measurableSet_shading_union Y)]

lemma multiplicity_floor_le_mass
    {BF : Kakeya.Streamlined.BodyFamily}
    {Y : Kakeya.Streamlined.Shading BF}
    {multiplicityFloor : ENNReal}
    (h :
      ∀ p ∈ Y.union,
        multiplicityFloor ≤
          (Y.pointMultiplicity p : ENNReal)) :
    multiplicityFloor * volume Y.union ≤ Y.mass := by
  have h_set_eq :
      (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) =
        ∫⁻ p in Y.union,
          (Y.pointMultiplicity p : ENNReal) :=
    lintegral_pointMultiplicity_eq_setLIntegral Y
  have h_main :
      multiplicityFloor * volume Y.union ≤
        ∫⁻ p in Y.union,
          (Y.pointMultiplicity p : ENNReal) := by
    have h5 :
        ∫⁻ p in Y.union, multiplicityFloor ≤
          ∫⁻ p in Y.union,
            (Y.pointMultiplicity p : ENNReal) :=
      setLIntegral_mono' (measurableSet_shading_union Y) h
    have h6 :
        ∫⁻ p in Y.union, multiplicityFloor =
          multiplicityFloor * volume Y.union := by
      rw [setLIntegral_const]
    rw [h6] at h5
    exact h5
  have h_eq :
      (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) = Y.mass :=
    lintegral_pointMultiplicity Y
  rw [h_set_eq] at h_eq
  rw [h_eq] at h_main
  exact h_main

lemma mass_le_of_pointMultiplicity_le
    {BF : Kakeya.Streamlined.BodyFamily}
    {Y : Kakeya.Streamlined.Shading BF}
    {multiplicityCap : ENNReal}
    (h :
      ∀ point ∈ Y.union,
        (Y.pointMultiplicity point : ENNReal) ≤ multiplicityCap) :
    Y.mass ≤ multiplicityCap * volume Y.union := by
  have h_set_eq :
      (∫⁻ point, (Y.pointMultiplicity point : ENNReal)) =
        ∫⁻ point in Y.union,
          (Y.pointMultiplicity point : ENNReal) :=
    lintegral_pointMultiplicity_eq_setLIntegral Y
  have h_main :
      (∫⁻ point in Y.union,
          (Y.pointMultiplicity point : ENNReal)) ≤
        ∫⁻ _point in Y.union, multiplicityCap :=
    setLIntegral_mono' (measurableSet_shading_union Y) h
  rw [setLIntegral_const] at h_main
  have h_mass :
      (∫⁻ point, (Y.pointMultiplicity point : ENNReal)) = Y.mass :=
    lintegral_pointMultiplicity Y
  rw [h_set_eq] at h_mass
  rwa [h_mass] at h_main

lemma one_le_pointMultiplicity_on_union
    {BF : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading BF) :
    ∀ point ∈ Y.union,
      (1 : ENNReal) ≤ (Y.pointMultiplicity point : ENNReal) := by
  classical
  intro point point_mem
  rcases point_mem with ⟨index, point_carrier⟩
  have index_mem :
      index ∈
        Finset.univ.filter fun candidate : Fin BF.card =>
          point ∈ Y.carrier candidate := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact point_carrier
  have positive : 0 < Y.pointMultiplicity point := by
    rw [Kakeya.Streamlined.Shading.pointMultiplicity]
    exact Finset.card_pos.mpr ⟨index, index_mem⟩
  exact_mod_cast Nat.succ_le_iff.mpr positive

lemma mass_eq_union_volume_of_pointMultiplicity_le_one
    {BF : Kakeya.Streamlined.BodyFamily}
    {Y : Kakeya.Streamlined.Shading BF}
    (h :
      ∀ point,
        (Y.pointMultiplicity point : ENNReal) ≤ 1) :
    Y.mass = volume Y.union := by
  apply le_antisymm
  · simpa using
      mass_le_of_pointMultiplicity_le
        (fun point _ => h point)
  · simpa using
      multiplicity_floor_le_mass
        (one_le_pointMultiplicity_on_union Y)

lemma mass_zero_implies_union_volume_zero
    {BF : Kakeya.Streamlined.BodyFamily}
    {Y : Kakeya.Streamlined.Shading BF}
    (h : Y.mass = 0) :
    volume Y.union = 0 := by
  have h_ge_one :
      ∀ p ∈ Y.union,
        (1 : ENNReal) ≤
          (Y.pointMultiplicity p : ENNReal) := by
    intro p hp
    have h_exists :
        ∃ (i : Fin BF.card), p ∈ Y.carrier i := by
      have h_union_eq :
          Y.union = ⋃ i : Fin BF.card, Y.carrier i := by
        ext x
        simp [Kakeya.Streamlined.Shading.union]
      rw [h_union_eq] at hp
      simpa using hp
    rcases h_exists with ⟨i, hi⟩
    classical
    have h_in_filter :
        i ∈ Finset.filter
          (fun j => p ∈ Y.carrier j) Finset.univ := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    have h_pos : 0 < Y.pointMultiplicity p := by
      rw [Kakeya.Streamlined.Shading.pointMultiplicity]
      exact Finset.card_pos.mpr ⟨i, h_in_filter⟩
    exact_mod_cast Nat.succ_le_iff.mpr h_pos
  have h_set_eq :
      (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) =
        ∫⁻ p in Y.union,
          (Y.pointMultiplicity p : ENNReal) :=
    lintegral_pointMultiplicity_eq_setLIntegral Y
  have h_lint :
      (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) = 0 := by
    rw [lintegral_pointMultiplicity Y, h]
  have h_lower :
      volume Y.union ≤
        ∫⁻ p in Y.union,
          (Y.pointMultiplicity p : ENNReal) := by
    have h7 :
        ∫⁻ p in Y.union, (1 : ENNReal) ≤
          ∫⁻ p in Y.union,
            (Y.pointMultiplicity p : ENNReal) :=
      setLIntegral_mono' (measurableSet_shading_union Y) h_ge_one
    have h8 :
        ∫⁻ p in Y.union, (1 : ENNReal) =
          1 * volume Y.union := by
      rw [setLIntegral_const]
    have h9 :
        (1 : ENNReal) * volume Y.union =
          volume Y.union := by
      simp
    rw [h8, h9] at h7
    exact h7
  rw [h_set_eq] at h_lint
  rw [h_lint] at h_lower
  simpa using h_lower

theorem wz2_paper_multiplicity_floor_volume :
    WZ2PaperMultiplicityFloorVolumeStatement := by
  intro delta family shading multiplicityFloor massUpper volumeUpper
    h1 h2 h3
  have h4 :
      multiplicityFloor * volume shading.union ≤ shading.mass :=
    multiplicity_floor_le_mass h1
  have h5 :
      multiplicityFloor * volume shading.union ≤
        multiplicityFloor * volumeUpper :=
    le_trans h4 (le_trans h2 h3)
  by_cases h0 : multiplicityFloor = 0
  · have h_mass_upper_zero : massUpper = 0 := by
      rw [h0] at h3
      simpa using h3
    have h_mass_zero : shading.mass = 0 := by
      rw [h_mass_upper_zero] at h2
      simpa using h2
    have h_volume_zero : volume shading.union = 0 :=
      mass_zero_implies_union_volume_zero h_mass_zero
    rw [h_volume_zero]
    simp
  · by_cases htop : multiplicityFloor = ⊤
    · have h_no_points : ∀ p, p ∉ shading.union := by
        intro p hp
        have h_eq_top :
            (shading.pointMultiplicity p : ENNReal) = ⊤ := by
          rw [htop] at h1
          exact top_le_iff.mp (h1 p hp)
        have h_ne_top :
            (shading.pointMultiplicity p : ENNReal) ≠ ⊤ :=
          ENNReal.natCast_ne_top
            (shading.pointMultiplicity p)
        exact h_ne_top h_eq_top
      have h_union_empty : shading.union = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        exact h_no_points p
      rw [h_union_empty]
      simp
    · have h5' :
          volume shading.union * multiplicityFloor ≤
            volumeUpper * multiplicityFloor := by
        have h_comm1 :
            multiplicityFloor * volume shading.union =
              volume shading.union * multiplicityFloor :=
          mul_comm _ _
        have h_comm2 :
            multiplicityFloor * volumeUpper =
              volumeUpper * multiplicityFloor :=
          mul_comm _ _
        rw [h_comm1, h_comm2] at h5
        exact h5
      exact
        (ENNReal.mul_le_mul_iff_left h0 htop).mp h5'

end Kakeya.Assouad

end
