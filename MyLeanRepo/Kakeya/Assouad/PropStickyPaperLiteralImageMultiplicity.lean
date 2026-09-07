import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageTransportStatements

/-!
# Cardinality and multiplicity transport for the literal image

The target family is indexed bijectively by the source family.  Each complete
source carrier maps into its target cubical saturation, so source point
multiplicity is bounded by target multiplicity at the affine image point.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_literal_image_multiplicity :
    WZ2PaperLiteralImageMultiplicityStatement := by
  intro delta rho sourceFamily anchor hrho
    familyData sourceShading shadingData
  let rescaling :=
    wz2PaperLiteralUnitRescalingMap anchor hrho
  let sourcePiece :
      Fin familyData.targetFamily.card → Set Point3 :=
    fun target =>
      sourceShading.carrier (familyData.sourceIndex target)
  have hbijective :
      Function.Bijective familyData.sourceIndex :=
    familyData.sourceIndex_bijective
  have hcard :
      Fintype.card (Fin familyData.targetFamily.card) =
        Fintype.card (Fin sourceFamily.card) :=
    Fintype.card_of_bijective hbijective
  have hcardEq :
      familyData.targetFamily.card = sourceFamily.card := by
    simpa [Fintype.card_fin] using hcard
  have henncard :
      familyData.targetFamily.enncard =
        sourceFamily.enncard := by
    simp [Kakeya.Streamlined.TubeFamily.enncard, hcardEq]
  have hsurjective :
      Function.Surjective familyData.sourceIndex :=
    hbijective.surjective
  have hcover :
      ∀ source : Fin sourceFamily.card,
        sourceShading.carrier source ⊆
          ⋃ target : Fin familyData.targetFamily.card,
            if familyData.sourceIndex target = source then
              sourcePiece target
            else ∅ := by
    intro source point hpoint
    rcases hsurjective source with ⟨target, htarget⟩
    have hpiece :
        sourcePiece target =
          sourceShading.carrier source := by
      dsimp only [sourcePiece]
      rw [htarget]
    have :
        point ∈
          if familyData.sourceIndex target = source then
            sourcePiece target
          else ∅ := by
      rw [if_pos htarget, hpiece]
      exact hpoint
    exact Set.mem_iUnion.mpr ⟨target, this⟩
  have hself :
      ∀ scale : ℝ, ∀ source : Set Point3,
        source ⊆ wz1PaperCubicalSaturation scale source := by
    intro scale source point hpoint
    exact ⟨point, hpoint, rfl⟩
  have himage :
      ∀ target : Fin familyData.targetFamily.card,
        rescaling '' sourcePiece target ⊆
          shadingData.targetShading.carrier target := by
    intro target
    rw [shadingData.target_carrier_eq target]
    change
      rescaling ''
          sourceShading.carrier
            (familyData.sourceIndex target) ⊆
        wz1PaperCubicalSaturation (delta / rho)
          (rescaling ''
            sourceShading.carrier
              (familyData.sourceIndex target))
    exact hself (delta / rho) _
  have hmultiplicity :
      ∀ point : Point3,
        (sourceShading.pointMultiplicity point : ENNReal) ≤
          (shadingData.targetShading.pointMultiplicity
            (rescaling point) : ENNReal) :=
    pullback_multiplicity_injective
      sourceShading shadingData.targetShading
      familyData.sourceIndex sourcePiece rescaling
      hcover himage
  exact ⟨henncard, hmultiplicity⟩

end Kakeya.Assouad

end
