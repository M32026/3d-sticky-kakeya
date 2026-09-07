import MyLeanRepo.Kakeya.Assouad.PropStickyPaperConvexWolffCardinalityStatements

/-!
# Finite cardinality core from normalized Convex-Wolff

Apply the normalized Convex-Wolff inequality to one nonempty member's convex
carrier and use the supplied common carrier-volume upper bound.
-/

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2_paper_convex_wolff_cardinality_core :
    WZ2PaperConvexWolffCardinalityCoreStatement := by
  intro delta family C V h_nonempty h_bound h_convex h_vol
  have h_card_pos : 0 < family.card := h_nonempty
  let bodyFamily : Streamlined.BodyFamily :=
    wz1PaperBodyFamily family
  have hbody_card : bodyFamily.card = family.card := by rfl
  have hbody_card_pos : 0 < bodyFamily.card := by
    rw [hbody_card]
    exact h_card_pos
  let bodyIndex : Fin bodyFamily.card :=
    ⟨0, hbody_card_pos⟩
  let tubeIndex : Fin family.card :=
    ⟨bodyIndex.val, by
      rw [← hbody_card]
      exact bodyIndex.isLt⟩
  let carrier : Set Point3 :=
    wz1PaperTubeCarrier (family.tube tubeIndex)
  have hcarrier_convex : Convex ℝ carrier :=
    h_convex tubeIndex
  have hbody_carrier :
      (bodyFamily.body bodyIndex).carrier = carrier := by
    simp [bodyFamily, bodyIndex, tubeIndex, carrier,
      wz1PaperBodyFamily]
  have hbody_mem :
      bodyIndex ∈ bodyFamily.containedIndices carrier := by
    rw [
      Streamlined.BodyFamily.mem_containedIndices_iff,
      hbody_carrier
    ]
  have hcount_nat :
      (1 : ℕ) ≤ (bodyFamily.containedIndices carrier).card :=
    Finset.one_le_card.mpr ⟨bodyIndex, hbody_mem⟩
  have hcount :
      (1 : ENNReal) ≤ bodyFamily.containedCount carrier := by
    change
      (1 : ENNReal) ≤
        ((bodyFamily.containedIndices carrier).card : ENNReal)
    exact Nat.one_le_cast.mpr hcount_nat
  have hbound :
      bodyFamily.containedCount carrier ≤
        C * volume carrier * family.enncard :=
    h_bound carrier hcarrier_convex
  have hvolume : volume carrier ≤ V :=
    h_vol tubeIndex
  calc
    (1 : ENNReal) ≤
        C * volume carrier * family.enncard :=
      hcount.trans hbound
    _ ≤ C * V * family.enncard := by
      gcongr

end Kakeya.Assouad
