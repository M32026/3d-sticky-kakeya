import MyLeanRepo.Kakeya.Assouad.Hairbrush.AcuteAngleHelpers

/-!
# Transverse multiplicity lower bound

Given a point on a hair, two-broadness at scale `theta` removes the near-parallel
ambient tubes (angle at most `angleScale`), leaving at least a fixed fraction of
the ambient multiplicity at angle strictly greater than `angleScale`.
-/

noncomputable section

open scoped Classical

open MeasureTheory Metric Set Finset Real

namespace Kakeya.Assouad

lemma transverse_multiplicity_lower
    {δ theta eta angleScale : ℝ}
    {F : Kakeya.TubeFamily δ} {layer : Kakeya.Shading F}
    (heta : 0 < eta) (theta_pos : 0 < theta)
    (h_angleScale_pos : 0 < angleScale)
    (h_two_angleScale : 2 * angleScale ≤ theta)
    (h_rpow : Real.rpow (2 * angleScale / theta) eta ≤ 1 / 4)
    (mu : ℕ) (hmu_pos : 0 < mu)
    (h_mult : ∀ x ∈ layer.union,
        mu ≤ (F.filter fun T => x ∈ layer.carrier T).card)
    (h_two_broad : IsTwoBroadAtScale layer theta eta)
    {H : Kakeya.TubeFamily δ}
    (hHinF : H ⊆ F)
    (hairShading : Kakeya.Shading H)
    (h_subset : ∀ T ∈ H, hairShading.carrier T ⊆ layer.carrier T)
    (hδ_le_angleScale : δ ≤ angleScale)
    (T : Kakeya.DeltaTube δ) (hT : T ∈ H)
    (x : Point3) (hx : x ∈ hairShading.carrier T) :
    (F.filter fun U =>
        x ∈ layer.carrier U ∧
        angleScale ≤ hairbrushAcuteAngle T U).card ≥
    (mu + 1) / 2 := by
  have hT_F : T ∈ F := hHinF hT
  have hx_layer : x ∈ layer.carrier T := h_subset T hT hx
  have hx_union : x ∈ layer.union := by
    exact ⟨T, hT_F, hx_layer⟩

  rcases h_two_broad x hx_union with
    ⟨thetaLocal, hδ_le_tl, htheta_half_le_tl, htl_le_theta, h_broad⟩

  have h_as_le_tl : angleScale ≤ thetaLocal := by linarith
  have h_tl_pos : 0 < thetaLocal := by linarith

  let through : Finset (Kakeya.DeltaTube δ) :=
    F.filter fun U => x ∈ layer.carrier U
  let near : Finset (Kakeya.DeltaTube δ) :=
    through.filter fun U =>
      hairbrushAcuteDirectionAngle U.direction T.direction ≤ angleScale

  have h_bound : (near.card : ℝ) ≤
      Real.rpow (angleScale / thetaLocal) eta * (through.card : ℝ) := by
    simpa [through, near] using
      h_broad T.direction T.direction_unit angleScale hδ_le_angleScale h_as_le_tl

  have h_ratio1 : angleScale / thetaLocal ≤ 2 * angleScale / theta := by
    have h1 : 0 < thetaLocal := h_tl_pos
    calc angleScale / thetaLocal
      ≤ angleScale / (theta / 2) := by gcongr
    _ = 2 * angleScale / theta := by
      field_simp [theta_pos.ne']

  have h_rpow2 : Real.rpow (angleScale / thetaLocal) eta ≤
      Real.rpow (2 * angleScale / theta) eta := by
    apply Real.rpow_le_rpow
    · positivity
    · exact h_ratio1
    · linarith

  have h_bound2 : (near.card : ℝ) ≤ (1 / 4 : ℝ) * (through.card : ℝ) := by
    calc (near.card : ℝ)
      ≤ Real.rpow (angleScale / thetaLocal) eta * (through.card : ℝ) := h_bound
    _ ≤ Real.rpow (2 * angleScale / theta) eta * (through.card : ℝ) := by
      gcongr
    _ ≤ (1 / 4 : ℝ) * (through.card : ℝ) := by
      gcongr

  have h4 : 4 * near.card ≤ through.card := by
    have h5 : (4 : ℝ) * (near.card : ℝ) ≤ (through.card : ℝ) := by linarith
    exact_mod_cast h5

  have h_through_ge_mu : mu ≤ through.card := h_mult x hx_union

  let strict_transverse : Finset (Kakeya.DeltaTube δ) := through \ near
  have h_near_sub : near ⊆ through := Finset.filter_subset _ _

  have h_st_card : strict_transverse.card = through.card - near.card := by
    have h : (through \ near).card = through.card - (near ∩ through).card :=
      Finset.card_sdiff
    rw [h]
    have h2 : near ∩ through = near := by
      apply Finset.inter_eq_left.mpr
      exact h_near_sub
    rw [h2]

  have h6 : near.card ≤ through.card / 4 := by omega
  have h7 : through.card - near.card ≥ (through.card + 1) / 2 := by omega
  have h8 : (through.card + 1) / 2 ≥ (mu + 1) / 2 := by omega

  have h11 : strict_transverse.card ≥ (mu + 1) / 2 := by
    rw [h_st_card]
    omega

  let target : Finset (Kakeya.DeltaTube δ) := F.filter fun U =>
    x ∈ layer.carrier U ∧ angleScale ≤ hairbrushAcuteAngle T U

  have h12 : strict_transverse ⊆ target := by
    intro U hU
    have hU_in_through : U ∈ through := by
      simpa [strict_transverse] using (Finset.mem_sdiff).mp hU |>.1
    have hU_not_near : U ∉ near := by
      simpa [strict_transverse] using (Finset.mem_sdiff).mp hU |>.2
    have hU_in_F : U ∈ F := (Finset.mem_filter.mp hU_in_through).1
    have hxU : x ∈ layer.carrier U := (Finset.mem_filter.mp hU_in_through).2
    have h_angle_gt : ¬(hairbrushAcuteDirectionAngle U.direction T.direction ≤ angleScale) := by
      intro h
      have h9 : U ∈ near := by
        rw [Finset.mem_filter]
        exact ⟨hU_in_through, h⟩
      exact hU_not_near h9
    have h_angle_gt' : angleScale < hairbrushAcuteDirectionAngle U.direction T.direction :=
      by linarith
    have h_symm : hairbrushAcuteAngle T U = hairbrushAcuteDirectionAngle U.direction T.direction :=
      hairbrushAcuteAngle_symm' T U
    have h_goal : angleScale ≤ hairbrushAcuteAngle T U := by
      rw [h_symm]
      linarith
    simp only [target, Finset.mem_filter]
    exact ⟨hU_in_F, ⟨hxU, h_goal⟩⟩

  have h13 : target.card ≥ strict_transverse.card :=
    Finset.card_le_card h12

  exact le_trans h11 h13

end Kakeya.Assouad
