import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers

/-!
# Standalone extremality restoration lemma

Given a WZ1-extremal shading Y with constant multiplicity [m, M], and a
subshading Z retaining at least a fraction L of Y's aggregate mass, restore
WZ1 extremality at a weaker exponent outputLoss.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

lemma restore_extremality_from_mass
    {delta sigma fineLoss outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y Z : Kakeya.Streamlined.TubeShading F}
    {m M : ℕ}
    {L : ENNReal}
    (hY : WZ1ExtremalPair sigma fineLoss F U Y)
    (h_mult : Y.HasConstantMultiplicity m M)
    (hsub : IsSubshading Z Y)
    (hmass : L * Y.mass ≤ Z.mass)
    (hfine_le : fineLoss ≤ outputLoss)
    (hm_pos : 0 < m)
    (_hL_ne_top : L ≠ ⊤)
    (h_absorb : L * (m : ENNReal) ≥
        (M : ENNReal) * Kakeya.realRpowENN delta (outputLoss - fineLoss)) :
    WZ1ExtremalPair sigma outputLoss F U Z := by
  classical
  rcases hY with
    ⟨hdelta, hdelta_one, hF_nonempty, hY_ball, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, hY_upper, hY_lower⟩
  have hY_union_nonempty : Y.union.Nonempty := by
    have hpos : 0 < Kakeya.realRpowENN delta (sigma + fineLoss) := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_pos, Real.rpow_pos_of_pos hdelta]
    have hvol : 0 < MeasureTheory.volume Y.union := hpos.trans_le hY_lower
    by_contra h
    have h' : Y.union = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h'] at hvol
    simp at hvol
  rcases hY_union_nonempty with ⟨p, hp⟩
  have hm_le_M : m ≤ M := (h_mult p hp).1.trans (h_mult p hp).2
  have hM_pos : (M : ENNReal) ≠ 0 := by
    exact_mod_cast (hm_pos.trans_le hm_le_M).ne'
  have hM_ne_top : (M : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top M
  have h_uniform' :
      U.uniformity ≤ Kakeya.realRpowENN delta (-outputLoss) :=
    hU_uniform.trans (realRpowENN_antitone hdelta hdelta_one (by linarith))
  have h_frostman' :
      U.IsFrostmanAtEveryScale (Kakeya.realRpowENN delta (-outputLoss)) := by
    intro rho j K hK_convex hK_subset
    have h_old := hU_frostman rho j K hK_convex hK_subset
    have h_mon : Kakeya.realRpowENN delta (-fineLoss) ≤
          Kakeya.realRpowENN delta (-outputLoss) :=
      realRpowENN_antitone hdelta hdelta_one (by linarith)
    exact h_old.trans (by gcongr)
  have hZ_ball : Z.union ⊆ Metric.closedBall (0 : Point3) 1 :=
    hsub.union_subset.trans hY_ball
  have h_vol_upper_power :
      Kakeya.realRpowENN delta (sigma - fineLoss) ≤
        Kakeya.realRpowENN delta (sigma - outputLoss) :=
    realRpowENN_antitone hdelta hdelta_one (by linarith)
  have hZ_upper :
      MeasureTheory.volume Z.union ≤
        Kakeya.realRpowENN delta (sigma - outputLoss) := by
    calc
      MeasureTheory.volume Z.union ≤ MeasureTheory.volume Y.union :=
        measure_mono hsub.union_subset
      _ ≤ Kakeya.realRpowENN delta (sigma - fineLoss) := hY_upper
      _ ≤ Kakeya.realRpowENN delta (sigma - outputLoss) := h_vol_upper_power
  have hY_meas : MeasurableSet Y.union := measurableSet_shading_union Y
  have hZ_meas : MeasurableSet Z.union := measurableSet_shading_union Z

  have hY_mult_zero_outside : ∀ p, p ∉ Y.union → Y.pointMultiplicity p = 0 := by
    intro p hp
    have h_empty : (Finset.univ.filter fun i => p ∈ Y.carrier i) = ∅ := by
      ext i
      have h9 : p ∉ Y.carrier i := by
        intro h10
        exact hp ⟨i, h10⟩
      simp [h9]
    simpa [Kakeya.Streamlined.Shading.pointMultiplicity] using h_empty
  have hZ_mult_zero_outside : ∀ p, p ∉ Z.union → Z.pointMultiplicity p = 0 := by
    intro p hp
    have h_empty : (Finset.univ.filter fun i => p ∈ Z.carrier i) = ∅ := by
      ext i
      have h9 : p ∉ Z.carrier i := by
        intro h10
        exact hp ⟨i, h10⟩
      simp [h9]
    simpa [Kakeya.Streamlined.Shading.pointMultiplicity] using h_empty

  have hY_mass_lintegral : Y.mass = ∫⁻ p, (Y.pointMultiplicity p : ENNReal) :=
    (lintegral_pointMultiplicity Y).symm
  have hZ_mass_lintegral : Z.mass = ∫⁻ p, (Z.pointMultiplicity p : ENNReal) :=
    (lintegral_pointMultiplicity Z).symm

  have hY_mass_lower_mult :
      (m : ENNReal) * MeasureTheory.volume Y.union ≤ Y.mass := by
    rw [hY_mass_lintegral]
    let f : Point3 → ENNReal := fun p =>
      Set.indicator Y.union (fun _ => (m : ENNReal)) p
    have h1 : ∀ p, f p ≤ (Y.pointMultiplicity p : ENNReal) := by
      intro p
      by_cases hp : p ∈ Y.union
      · simpa [f, hp, Set.indicator_of_mem] using (h_mult p hp).1
      · have h2 : Y.pointMultiplicity p = 0 := hY_mult_zero_outside p hp
        simp [f, hp, h2]
    have h2 : ∫⁻ p, f p = (m : ENNReal) * MeasureTheory.volume Y.union := by
      simp [f, lintegral_indicator hY_meas, lintegral_const]
    calc
      (m : ENNReal) * MeasureTheory.volume Y.union = ∫⁻ p, f p := h2.symm
      _ ≤ ∫⁻ p, (Y.pointMultiplicity p : ENNReal) := lintegral_mono h1

  have hZ_mult_upper_all : ∀ p, (Z.pointMultiplicity p : ENNReal) ≤
      Set.indicator Z.union (fun _ => (M : ENNReal)) p := by
    intro p
    by_cases hp : p ∈ Z.union
    · have hpY : p ∈ Y.union := hsub.union_subset hp
      have h1 : Z.pointMultiplicity p ≤ Y.pointMultiplicity p := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hsub i hi
      have h2 : (Z.pointMultiplicity p : ENNReal) ≤ (Y.pointMultiplicity p : ENNReal) := by
        exact_mod_cast h1
      have h3 : (Y.pointMultiplicity p : ENNReal) ≤ (M : ENNReal) := by
        exact_mod_cast (h_mult p hpY).2
      simpa [hp, Set.indicator_of_mem] using h2.trans h3
    · have h4 : Z.pointMultiplicity p = 0 := hZ_mult_zero_outside p hp
      simp [hp, h4]
  have hZ_mass_upper_mult :
      Z.mass ≤ (M : ENNReal) * MeasureTheory.volume Z.union := by
    rw [hZ_mass_lintegral]
    let g : Point3 → ENNReal := fun p =>
      Set.indicator Z.union (fun _ => (M : ENNReal)) p
    have h1 : ∀ p, (Z.pointMultiplicity p : ENNReal) ≤ g p := hZ_mult_upper_all
    have h2 : ∫⁻ p, g p = (M : ENNReal) * MeasureTheory.volume Z.union := by
      simp [g, lintegral_indicator hZ_meas, lintegral_const]
    calc
      ∫⁻ p, (Z.pointMultiplicity p : ENNReal) ≤ ∫⁻ p, g p := lintegral_mono h1
      _ = (M : ENNReal) * MeasureTheory.volume Z.union := h2

  have h1 : L * (m : ENNReal) * MeasureTheory.volume Y.union ≤ Z.mass := by
    have h_assoc : L * (m : ENNReal) * MeasureTheory.volume Y.union =
        L * ((m : ENNReal) * MeasureTheory.volume Y.union) := by
      simp [mul_assoc]
    rw [h_assoc]
    have h : L * ((m : ENNReal) * MeasureTheory.volume Y.union) ≤ L * Y.mass := by
      gcongr
    exact h.trans hmass
  have h4 : L * (m : ENNReal) * MeasureTheory.volume Y.union ≤
        (M : ENNReal) * MeasureTheory.volume Z.union :=
    h1.trans hZ_mass_upper_mult
  have h5 : (L * (m : ENNReal)) / (M : ENNReal) * MeasureTheory.volume Y.union ≤
        MeasureTheory.volume Z.union := by
    have h61 : (L * (m : ENNReal)) / (M : ENNReal) * MeasureTheory.volume Y.union =
          (L * (m : ENNReal) * MeasureTheory.volume Y.union) / (M : ENNReal) := by
      have h_div : (L * (m : ENNReal)) / (M : ENNReal) =
          (L * (m : ENNReal)) * (M : ENNReal)⁻¹ := by
        rw [div_eq_mul_inv]
      rw [h_div]
      have h_ring : (L * (m : ENNReal)) * (M : ENNReal)⁻¹ * MeasureTheory.volume Y.union =
          ((L * (m : ENNReal)) * MeasureTheory.volume Y.union) * (M : ENNReal)⁻¹ := by
        ring
      rw [h_ring]
      rw [← div_eq_mul_inv]
    rw [h61]
    have h62 : (L * (m : ENNReal) * MeasureTheory.volume Y.union) / (M : ENNReal) ≤
          ((M : ENNReal) * MeasureTheory.volume Z.union) / (M : ENNReal) := by
      exact ENNReal.div_le_div_right h4 (M : ENNReal)
    have h7 : ((M : ENNReal) * MeasureTheory.volume Z.union) / (M : ENNReal) =
          MeasureTheory.volume Z.union := by
      have hcomm : (M : ENNReal) * MeasureTheory.volume Z.union =
          MeasureTheory.volume Z.union * (M : ENNReal) := by ring
      rw [hcomm]
      exact ENNReal.mul_div_cancel_right hM_pos hM_ne_top
    rw [h7] at h62
    exact h62

  have h_ratio_ge :
      Kakeya.realRpowENN delta (outputLoss - fineLoss) ≤
        (L * (m : ENNReal)) / (M : ENNReal) := by
    have h6 : (M : ENNReal) * Kakeya.realRpowENN delta (outputLoss - fineLoss) ≤
          L * (m : ENNReal) := h_absorb
    have h7 : ((M : ENNReal) * Kakeya.realRpowENN delta (outputLoss - fineLoss)) / (M : ENNReal) ≤
          (L * (m : ENNReal)) / (M : ENNReal) := by
      apply ENNReal.div_le_div_right h6
    have h8 : ((M : ENNReal) * Kakeya.realRpowENN delta (outputLoss - fineLoss)) / (M : ENNReal) =
          Kakeya.realRpowENN delta (outputLoss - fineLoss) := by
      have hcomm : (M : ENNReal) * Kakeya.realRpowENN delta (outputLoss - fineLoss) =
          Kakeya.realRpowENN delta (outputLoss - fineLoss) * (M : ENNReal) := by ring
      rw [hcomm]
      exact ENNReal.mul_div_cancel_right hM_pos hM_ne_top
    rw [h8] at h7
    exact h7

  have h_rpow_add : ∀ (a b : ℝ),
      Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b =
      Kakeya.realRpowENN delta (a + b) := by
    intro a b
    simp only [Kakeya.realRpowENN]
    have h_pos1 : 0 ≤ Real.rpow delta a := Real.rpow_nonneg hdelta.le _
    rw [← ENNReal.ofReal_mul h_pos1]
    congr 1
    exact (Real.rpow_add hdelta a b).symm

  have hZ_lower :
      Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        MeasureTheory.volume Z.union := by
    calc
      Kakeya.realRpowENN delta (sigma + outputLoss)
        = Kakeya.realRpowENN delta (outputLoss - fineLoss) *
            Kakeya.realRpowENN delta (sigma + fineLoss) := by
        rw [h_rpow_add (outputLoss - fineLoss) (sigma + fineLoss)]
        <;> ring_nf
      _ ≤ ((L * (m : ENNReal)) / (M : ENNReal)) *
            Kakeya.realRpowENN delta (sigma + fineLoss) := by gcongr
      _ ≤ ((L * (m : ENNReal)) / (M : ENNReal)) *
            MeasureTheory.volume Y.union := by gcongr
      _ ≤ MeasureTheory.volume Z.union := h5

  have h_m_le_M : (m : ENNReal) ≤ (M : ENNReal) := by exact_mod_cast hm_le_M
  have h9 : (m : ENNReal) / (M : ENNReal) ≤ 1 := by
    calc
      (m : ENNReal) / (M : ENNReal) ≤ (M : ENNReal) / (M : ENNReal) := by gcongr
      _ = 1 := by
        rw [ENNReal.div_self hM_pos hM_ne_top]
  have h10 : L * ((m : ENNReal) / (M : ENNReal)) ≤ L := by
    calc
      L * ((m : ENNReal) / (M : ENNReal)) ≤ L * 1 := by gcongr
      _ = L := by simp
  have h11 : L * ((m : ENNReal) / (M : ENNReal)) =
        (L * (m : ENNReal)) / (M : ENNReal) := by
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  have h : (L * (m : ENNReal)) / (M : ENNReal) ≤ L := by
    rw [← h11]
    exact h10
  have h_density_le :
      Kakeya.realRpowENN delta (outputLoss - fineLoss) ≤ L :=
    h_ratio_ge.trans h

  have hZ_dense :
      Z.IsLambdaDense (Kakeya.realRpowENN delta outputLoss) := by
    have h2 : Kakeya.realRpowENN delta outputLoss =
          Kakeya.realRpowENN delta (outputLoss - fineLoss) *
          Kakeya.realRpowENN delta fineLoss := by
      rw [h_rpow_add (outputLoss - fineLoss) fineLoss] <;> ring_nf
    rw [h2]
    calc
      (Kakeya.realRpowENN delta (outputLoss - fineLoss) *
          Kakeya.realRpowENN delta fineLoss) * F.toBodyFamily.mass
        = Kakeya.realRpowENN delta (outputLoss - fineLoss) *
            (Kakeya.realRpowENN delta fineLoss * F.toBodyFamily.mass) := by
          simp [mul_assoc]
      _ ≤ Kakeya.realRpowENN delta (outputLoss - fineLoss) * Y.mass := by
        gcongr
        exact hY_dense
      _ ≤ L * Y.mass := by gcongr
      _ ≤ Z.mass := hmass

  exact
    ⟨hdelta, hdelta_one, hF_nonempty, hZ_ball, hF_distinct,
      h_uniform', h_frostman', hZ_dense, hZ_upper, hZ_lower⟩

end Kakeya.Assouad
