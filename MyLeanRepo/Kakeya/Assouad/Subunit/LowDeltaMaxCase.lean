import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Low deltaMax case for probabilistic Katz-Tao subfamily

When the original family already satisfies the Katz-Tao deltaMax bound,
the identity subfamily (all tubes) satisfies all required properties.
-/

noncomputable section

open Kakeya.Streamlined

namespace Kakeya.Assouad.Subunit

/-- For `0 < δ ≤ 1`, `a ≤ b` implies `realRpowENN δ b ≤ realRpowENN δ a`. -/
lemma realRpowENN_antitone {δ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : a ≤ b) :
    Kakeya.realRpowENN δ b ≤ Kakeya.realRpowENN δ a := by
  simp only [Kakeya.realRpowENN]
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 h

/-- The identity subfamily: select every tube with `family = F` definitionally. -/
def idSubfamily {δ : ℝ} (F : Kakeya.Streamlined.TubeFamily δ) :
    Kakeya.Streamlined.TubeSubfamily F where
  family := F
  embedding := Function.Embedding.refl (Fin F.card)
  tube_eq _ := rfl

namespace idSubfamily

@[simp]
lemma family_eq {δ : ℝ} (F : Kakeya.Streamlined.TubeFamily δ) :
    (idSubfamily F).family = F := by
  rfl

@[simp]
lemma enncard_eq {δ : ℝ} (F : Kakeya.Streamlined.TubeFamily δ) :
    (idSubfamily F).family.enncard = F.enncard := by
  rfl

lemma restrictShading_union_eq {δ : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ)
    (Y : Kakeya.Streamlined.TubeShading F) :
    ((idSubfamily F).restrictShading Y).union = Y.union := by
  ext x
  simp [idSubfamily, TubeSubfamily.restrictShading]
  ; tauto

lemma restrictShading_mass_eq {δ : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ)
    (Y : Kakeya.Streamlined.TubeShading F) :
    ((idSubfamily F).restrictShading Y).mass = Y.mass := by
  dsimp only [idSubfamily, TubeSubfamily.restrictShading, Shading.mass]
  ; rfl

end idSubfamily

/--
Low-deltaMax case: if the family already has small deltaMax, take all tubes.
-/
lemma low_deltaMax_case
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hF_nonempty : F.Nonempty)
    (hF_ball : F.IsInUnitBall)
    (hF_distinct : F.IsEssentiallyDistinct)
    {Y : Kakeya.Streamlined.TubeShading F}
    (inputEta densityEta cardLoss ktEta η' : ℝ)
    (h_input_lt_density : inputEta < densityEta)
    (h_η'_lt_kt : η' < ktEta)
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN δ inputEta))
    (hD_small : F.toBodyFamily.deltaMax ≤ Kakeya.realRpowENN δ (-η'))
    (h_card_lower : Kakeya.realRpowENN δ (-2 + cardLoss) ≤ F.enncard) :
    ∃ S : Kakeya.Streamlined.TubeSubfamily F,
      S.family.Nonempty ∧
      S.family.IsInUnitBall ∧
      S.family.IsEssentiallyDistinct ∧
      (S.restrictShading Y).union ⊆ Y.union ∧
      (S.restrictShading Y).IsLambdaDense (Kakeya.realRpowENN δ densityEta) ∧
      S.family.toBodyFamily.IsCKatzTao (Kakeya.realRpowENN δ (-ktEta)) ∧
      Kakeya.realRpowENN δ (-2 + cardLoss) ≤ S.family.enncard := by
  let S : Kakeya.Streamlined.TubeSubfamily F := idSubfamily F
  have h_family_eq : S.family = F := by rfl
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Nonempty
    rw [h_family_eq]
    exact hF_nonempty
  · -- IsInUnitBall
    rw [h_family_eq]
    exact hF_ball
  · -- IsEssentiallyDistinct
    exact TubeSubfamily.isEssentiallyDistinct S hF_distinct
  · -- Union containment
    rw [idSubfamily.restrictShading_union_eq F Y]
  · -- Density
    have h_density_le : Kakeya.realRpowENN δ densityEta ≤ Kakeya.realRpowENN δ inputEta :=
      realRpowENN_antitone hδ hδ1 h_input_lt_density.le
    have h_mass_eq : (S.restrictShading Y).mass = Y.mass :=
      idSubfamily.restrictShading_mass_eq F Y
    have h_family_mass_eq : S.family.toBodyFamily.mass = F.toBodyFamily.mass := by
      rw [h_family_eq]
    have h_goal : Kakeya.realRpowENN δ densityEta * S.family.toBodyFamily.mass ≤
        (S.restrictShading Y).mass := by
      rw [h_mass_eq, h_family_mass_eq]
      have h1 : Kakeya.realRpowENN δ densityEta * F.toBodyFamily.mass ≤
          Kakeya.realRpowENN δ inputEta * F.toBodyFamily.mass := by
        gcongr
      exact le_trans h1 hY_dense
    exact h_goal
  · -- Katz-Tao
    have h_kt : Kakeya.realRpowENN δ (-η') ≤ Kakeya.realRpowENN δ (-ktEta) :=
      realRpowENN_antitone hδ hδ1 (by linarith)
    have h_deltaMax_le : F.toBodyFamily.deltaMax ≤ Kakeya.realRpowENN δ (-ktEta) :=
      le_trans hD_small h_kt
    have h_body_eq : S.family.toBodyFamily = F.toBodyFamily := by
      rw [h_family_eq]
    rw [h_body_eq]
    exact h_deltaMax_le
  · -- Cardinality
    rw [idSubfamily.enncard_eq F]
    exact h_card_lower

end Kakeya.Assouad.Subunit
