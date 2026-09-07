import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCWATransferStatements

/-! # Generic indexed normalized Convex-Wolff transfer -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2_paper_indexed_convex_wolff_transfer :
    WZ2PaperIndexedConvexWolffTransferStatement := by
  intro sourceScale targetScale sourceFamily targetFamily
    C envelopeConstant indexEquiv hEnvelope hSourceCWA
  dsimp only [WZ2PaperConvexWolffBound] at hSourceCWA ⊢
  intro targetConvexSet htargetConvex
  rcases hEnvelope targetConvexSet htargetConvex with
    ⟨sourceConvexSet, hsourceConvex, hvolume, hcontainment⟩
  let targetBody := wz1PaperBodyFamily targetFamily
  let sourceBody := wz1PaperBodyFamily sourceFamily
  let targetContained :=
    targetBody.containedIndices targetConvexSet
  let sourceContained :=
    sourceBody.containedIndices sourceConvexSet
  have hmap :
      ∀ target : Fin targetFamily.card,
        target ∈ targetContained →
          indexEquiv target ∈ sourceContained := by
    intro target htarget
    have htargetCarrier :
        wz1PaperTubeCarrier (targetFamily.tube target) ⊆
          targetConvexSet :=
      (Streamlined.BodyFamily.mem_containedIndices_iff).mp
        htarget
    have hsourceCarrier :
        wz1PaperTubeCarrier
            (sourceFamily.tube (indexEquiv target)) ⊆
          sourceConvexSet :=
      hcontainment target htargetCarrier
    exact
      (Streamlined.BodyFamily.mem_containedIndices_iff).mpr
        hsourceCarrier
  have himage :
      Finset.image indexEquiv targetContained ⊆
        sourceContained := by
    intro sourceIndex hsourceIndex
    rcases Finset.mem_image.mp hsourceIndex with
      ⟨target, htarget, rfl⟩
    exact hmap target htarget
  have hcardNat :
      targetContained.card ≤ sourceContained.card := by
    have himageCard :
        (Finset.image indexEquiv targetContained).card =
          targetContained.card :=
      Finset.card_image_of_injective
        targetContained indexEquiv.injective
    have hsubsetCard :
        (Finset.image indexEquiv targetContained).card ≤
          sourceContained.card :=
      Finset.card_le_card himage
    rwa [himageCard] at hsubsetCard
  have hcard :
      (targetContained.card : ENNReal) ≤
        (sourceContained.card : ENNReal) := by
    exact_mod_cast hcardNat
  have henncard :
      sourceFamily.enncard = targetFamily.enncard := by
    have hcards :
        targetFamily.card = sourceFamily.card := by
      simpa using Fintype.card_congr indexEquiv
    simp [Kakeya.Streamlined.TubeFamily.enncard, hcards]
  have hsourceBound :
      (sourceContained.card : ENNReal) ≤
        C * volume sourceConvexSet * sourceFamily.enncard :=
    hSourceCWA sourceConvexSet hsourceConvex
  calc
    (targetContained.card : ENNReal)
        ≤ (sourceContained.card : ENNReal) := hcard
    _ ≤ C * volume sourceConvexSet * sourceFamily.enncard :=
      hsourceBound
    _ ≤ C * (envelopeConstant * volume targetConvexSet) *
          targetFamily.enncard := by
      rw [henncard]
      gcongr
    _ =
        (envelopeConstant * C) *
          volume targetConvexSet * targetFamily.enncard := by
      ring

end Kakeya.Assouad

end
