import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMeasureStatements

/-! # Measure lower bounds for the literal-paper image shading -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2_paper_literal_image_measure :
    WZ2PaperLiteralImageMeasureStatement := by
  intro hvolume delta rho sourceFamily anchor hrho
    familyData sourceShading shadingData
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho : ℝ) ^ 2)
  let rescaling : Point3 → Point3 :=
    wz2PaperLiteralUnitRescalingMap anchor hrho
  have hcubicalSubset :
      ∀ (scale : ℝ) (source : Set Point3),
        source ⊆ wz1PaperCubicalSaturation scale source := by
    intro scale source point hpoint
    exact ⟨point, hpoint, rfl⟩
  have hperTube :
      ∀ target,
        jacobian *
              volume
                (sourceShading.carrier
                  (familyData.sourceIndex target)) ≤
            volume (shadingData.targetShading.carrier target) := by
    intro target
    let sourceCarrier :=
      sourceShading.carrier (familyData.sourceIndex target)
    have hsubset :
        rescaling '' sourceCarrier ⊆
          shadingData.targetShading.carrier target := by
      rw [shadingData.target_carrier_eq target]
      exact hcubicalSubset (delta / rho) _
    have hmeasure :
        volume (rescaling '' sourceCarrier) ≤
          volume (shadingData.targetShading.carrier target) :=
      measure_mono hsubset
    have himage :
        volume (rescaling '' sourceCarrier) =
          jacobian * volume sourceCarrier :=
      hvolume anchor hrho sourceCarrier
        (sourceShading.measurable_carrier
          (familyData.sourceIndex target))
    rwa [himage] at hmeasure
  have hmass :
      jacobian * sourceShading.mass ≤
        shadingData.targetShading.mass := by
    have hsum :
        ∑ target : Fin familyData.targetFamily.card,
              volume
                (sourceShading.carrier
                  (familyData.sourceIndex target)) =
            sourceShading.mass := by
      let equivalence :
          Fin familyData.targetFamily.card ≃
            Fin sourceFamily.card :=
        Equiv.ofBijective
          familyData.sourceIndex familyData.sourceIndex_bijective
      have hsum' :
          ∑ target : Fin familyData.targetFamily.card,
                volume
                  (sourceShading.carrier
                    (familyData.sourceIndex target)) =
              ∑ source : Fin sourceFamily.card,
                volume (sourceShading.carrier source) :=
        Finset.sum_equiv equivalence (by simp) (fun _ _ => rfl)
      rw [hsum']
      rfl
    calc
      shadingData.targetShading.mass =
          ∑ target : Fin familyData.targetFamily.card,
            volume (shadingData.targetShading.carrier target) := by
        rfl
      _ ≥ ∑ target : Fin familyData.targetFamily.card,
            jacobian *
              volume
                (sourceShading.carrier
                  (familyData.sourceIndex target)) := by
        apply Finset.sum_le_sum
        intro target _
        exact hperTube target
      _ = jacobian *
            ∑ target : Fin familyData.targetFamily.card,
              volume
                (sourceShading.carrier
                  (familyData.sourceIndex target)) := by
        rw [Finset.mul_sum]
      _ = jacobian * sourceShading.mass := by
        rw [hsum]
  have hunionImage :
      rescaling '' sourceShading.union ⊆
        shadingData.targetShading.union := by
    rintro _ ⟨point, ⟨source, hsource⟩, rfl⟩
    rcases familyData.sourceIndex_bijective.surjective source with
      ⟨target, htarget⟩
    have himage :
        rescaling point ∈
          rescaling '' sourceShading.carrier source :=
      ⟨point, hsource, rfl⟩
    have htargetCarrier :
        rescaling point ∈
          shadingData.targetShading.carrier target := by
      rw [shadingData.target_carrier_eq target, htarget]
      exact hcubicalSubset (delta / rho) _ himage
    exact ⟨target, htargetCarrier⟩
  have hunion :
      jacobian * volume sourceShading.union ≤
        volume shadingData.targetShading.union := by
    have hmeasure :
        volume (rescaling '' sourceShading.union) ≤
          volume shadingData.targetShading.union :=
      measure_mono hunionImage
    have himage :
        volume (rescaling '' sourceShading.union) =
          jacobian * volume sourceShading.union :=
      hvolume anchor hrho sourceShading.union
        sourceShading.union_measurable
    rwa [himage] at hmeasure
  exact ⟨hperTube, hmass, hunion⟩

end Kakeya.Assouad

end
