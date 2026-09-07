import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMultiplicityFloorStatements

/-!
# Multiplicity floor on a literal cubical image

Use the source-image witness of each target carrier point, the existing
pointwise image multiplicity transfer, and cubical same-cell invariance.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_literal_image_multiplicity_floor :
    WZ2PaperLiteralImageMultiplicityFloorStatement := by
  intro h_mult delta rho sourceFamily anchor hrho
    familyData sourceShading shadingData multiplicityFloor
    h_floor targetPoint htarget
  let rescaling := wz2PaperLiteralUnitRescalingMap anchor hrho
  have h_main :
      familyData.targetFamily.enncard = sourceFamily.enncard ∧
      ∀ point,
        (sourceShading.pointMultiplicity point : ENNReal) ≤
          (shadingData.targetShading.pointMultiplicity
            (rescaling point) : ENNReal) :=
    h_mult (familyData := familyData) (sourceShading := sourceShading)
      (shadingData := shadingData)
  rcases h_main with ⟨_, hmult⟩
  have htarget' : ∃ (target : Fin familyData.targetFamily.card),
      targetPoint ∈ shadingData.targetShading.carrier target := by
    have h : targetPoint ∈ shadingData.targetShading.union := htarget
    simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq] at h
    exact h
  rcases htarget' with ⟨target, htargetCarrier⟩
  have h1 : targetPoint ∈
      wz1PaperCubicalSaturation (delta / rho)
        (rescaling '' sourceShading.carrier (familyData.sourceIndex target)) := by
    rw [shadingData.target_carrier_eq target] at htargetCarrier
    exact htargetCarrier
  rcases h1 with ⟨witnessPoint, hwitness, hgrid⟩
  have h_image : ∃ (sourcePoint : Point3),
      sourcePoint ∈ sourceShading.carrier (familyData.sourceIndex target) ∧
      rescaling sourcePoint = witnessPoint := by
    simpa [Set.mem_image] using hwitness
  rcases h_image with ⟨sourcePoint, hsourceCarrier, h_eq⟩
  have hsourceUnion : sourcePoint ∈ sourceShading.union := by
    simp [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
    exact ⟨familyData.sourceIndex target, hsourceCarrier⟩
  have h2 : multiplicityFloor ≤
      (sourceShading.pointMultiplicity sourcePoint : ENNReal) :=
    h_floor sourcePoint hsourceUnion
  have h3 : (sourceShading.pointMultiplicity sourcePoint : ENNReal) ≤
      (shadingData.targetShading.pointMultiplicity
        (rescaling sourcePoint) : ENNReal) :=
    hmult sourcePoint
  have hgrid' : wz1PaperGridIndex (delta / rho) (rescaling sourcePoint) =
      wz1PaperGridIndex (delta / rho) targetPoint := by
    rw [h_eq]
    exact hgrid.symm
  have h4 : shadingData.targetShading.pointMultiplicity
        (rescaling sourcePoint) =
      shadingData.targetShading.pointMultiplicity targetPoint :=
    shadingData.target_cubical.pointMultiplicity_eq_of_same_cell hgrid'
  rw [h4] at h3
  exact le_trans h2 h3

end Kakeya.Assouad

end
