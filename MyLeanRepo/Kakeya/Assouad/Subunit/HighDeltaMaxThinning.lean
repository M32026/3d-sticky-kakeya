import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.GeneralizedKatzTao.ProbabilisticThinning
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.Proof
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# High deltaMax thinning lemma

Given a streamlined tube family with large deltaMax, apply Bernoulli thinning
to extract a Katz--Tao subfamily with retained shading density and near-critical
cardinality.
-/

noncomputable section

open MeasureTheory Finset
open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Assouad

/--
High deltaMax case: Bernoulli thinning produces a Katz--Tao subfamily.
-/
lemma high_deltaMax_thinning
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hF_nonempty : F.Nonempty) (hF_ball : F.IsInUnitBall)
    (hF_distinct : F.IsEssentiallyDistinct)
    {Y : Kakeya.Streamlined.TubeShading F}
    (η' ktEta densityEta cardLoss inputEta : ℝ)
    (hη'_pos : 0 < η')
    (D : ENNReal) (hD : F.toBodyFamily.deltaMax ≤ D) (hD_ne_top : D ≠ ⊤)
    (h_thin : Kakeya.realRpowENN δ (-η') ≤ D)
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN δ inputEta))
    (net : TubeDensityTestNet δ)
    (h_kt_bound : net.lossFactor * (10 : ENNReal) * Kakeya.realRpowENN δ (-η') ≤
        Kakeya.realRpowENN δ (-ktEta))
    (h_density_bound : (4 : ENNReal) * Kakeya.realRpowENN δ densityEta ≤
        Kakeya.realRpowENN δ inputEta)
    (h_card_bound : Kakeya.realRpowENN δ (-2 + cardLoss) ≤
        (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
        Kakeya.realRpowENN δ inputEta * F.enncard)
    (h_mu_ge_V : Kakeya.deltaTubeVolume δ ≤
        (Kakeya.realRpowENN δ (-η') / D) * Y.mass)
    (h_union_bound :
      let p := (Kakeya.realRpowENN δ (-η')).toReal / D.toReal
      (net.testSets.card : ℝ) * Real.exp (-(11 - Real.exp 1) * (Kakeya.realRpowENN δ (-η')).toReal) +
      Real.exp (-(3 - Real.exp 1) * p * (F.card : ℝ)) < 1 / 8)
    :
    ∃ (S : Kakeya.Streamlined.TubeSubfamily F),
      S.family.Nonempty ∧
      S.family.IsInUnitBall ∧
      S.family.IsEssentiallyDistinct ∧
      (S.restrictShading Y).union ⊆ Y.union ∧
      (S.restrictShading Y).IsLambdaDense (Kakeya.realRpowENN δ densityEta) ∧
      S.family.toBodyFamily.IsCKatzTao (Kakeya.realRpowENN δ (-ktEta)) ∧
      Kakeya.realRpowENN δ (-2 + cardLoss) ≤ S.family.enncard := by
  have h_main := Kakeya.Streamlined.ProbabilisticThinning.probabilistic_thinning
    (hδ := hδ) (hδ1 := hδ1) (hT_nonempty := hF_nonempty) (hT_ball := hF_ball)
    (Z := Y) (D := D) (hD := hD) (hD_ne_top := hD_ne_top)
    (η' := η') (hη'_pos := hη'_pos) (h_thin := h_thin)
    (net := net) (h_mu_ge_V := h_mu_ge_V) (h_union_bound := h_union_bound)
  rcases h_main with ⟨S, h_deltaMax, h_card_upper, h_mass⟩
  have h_ball : S.family.IsInUnitBall := by
    intro i
    have h_eq : S.family.tube i = F.tube (S.embedding i) := S.tube_eq i
    rw [h_eq]
    exact hF_ball (S.embedding i)
  have h_distinct : S.family.IsEssentiallyDistinct :=
    Kakeya.Streamlined.TubeSubfamily.isEssentiallyDistinct S hF_distinct
  have h_union : (S.restrictShading Y).union ⊆ Y.union := by
    intro x hx
    rcases hx with ⟨i, hi⟩
    exact ⟨S.embedding i, hi⟩
  have h_kt_le : S.family.toBodyFamily.deltaMax ≤ Kakeya.realRpowENN δ (-ktEta) :=
    h_deltaMax.trans h_kt_bound
  have hV_nonneg : 0 ≤ Kakeya.deltaTubeVolume δ := by positivity
  have h_S_mass_upper : S.family.toBodyFamily.mass ≤
      (2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) * F.toBodyFamily.mass := by
    have h2 : S.family.toBodyFamily.mass = S.family.enncard * Kakeya.deltaTubeVolume δ :=
      tubeFamily_mass_eq_nominal S.family
    have h3 : F.toBodyFamily.mass = F.enncard * Kakeya.deltaTubeVolume δ :=
      tubeFamily_mass_eq_nominal F
    rw [h2, h3]
    have h4 : S.family.enncard * Kakeya.deltaTubeVolume δ ≤
        ((2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) * F.enncard) * Kakeya.deltaTubeVolume δ :=
      mul_le_mul_of_nonneg_right h_card_upper hV_nonneg
    simpa [mul_assoc] using h4
  have h_mass_retention : (S.restrictShading Y).mass ≥
      (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
      Kakeya.realRpowENN δ inputEta * F.toBodyFamily.mass := by
    have h4 : (S.restrictShading Y).mass ≥
        (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) * Y.mass := h_mass
    have h5 : Y.mass ≥ Kakeya.realRpowENN δ inputEta * F.toBodyFamily.mass := hY_dense
    calc (S.restrictShading Y).mass
      ≥ (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) * Y.mass := h4
    _ ≥ (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
          (Kakeya.realRpowENN δ inputEta * F.toBodyFamily.mass) := by
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
          Kakeya.realRpowENN δ inputEta * F.toBodyFamily.mass := by simp [mul_assoc, mul_comm, mul_left_comm]
  set X : ENNReal := (Kakeya.realRpowENN δ (-η') / D) * F.toBodyFamily.mass with hX_def
  have h_S_mass_upper' : S.family.toBodyFamily.mass ≤ (2 : ENNReal) * X := by
    have h_eq : (2 : ENNReal) * X =
        (2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) * F.toBodyFamily.mass := by
      simp [hX_def, mul_assoc]
    rw [h_eq]
    exact h_S_mass_upper
  have h2 : (2 : ENNReal) * Kakeya.realRpowENN δ densityEta ≤
      (1/2 : ENNReal) * Kakeya.realRpowENN δ inputEta := by
    have h3 : (4 : ENNReal) * Kakeya.realRpowENN δ densityEta ≤ Kakeya.realRpowENN δ inputEta := h_density_bound
    have h4 : (1/2 : ENNReal) * ((4 : ENNReal) * Kakeya.realRpowENN δ densityEta) ≤
        (1/2 : ENNReal) * Kakeya.realRpowENN δ inputEta :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (1/2 : ENNReal) * ((4 : ENNReal) * Kakeya.realRpowENN δ densityEta) =
        (2 : ENNReal) * Kakeya.realRpowENN δ densityEta := by
      have h6 : (1/2 : ENNReal) * (4 : ENNReal) = (2 : ENNReal) := by
        have h7 : (1/2 : ENNReal) = (2 : ENNReal)⁻¹ := by simp
        rw [h7]
        have h8 : (4 : ENNReal) = (2 : ENNReal) * (2 : ENNReal) := by norm_num
        rw [h8, ←mul_assoc, ENNReal.inv_mul_cancel] <;> norm_num
      rw [←mul_assoc, h6]
    rw [h5] at h4
    exact h4
  have h_mass_retention' : (1/2 : ENNReal) * Kakeya.realRpowENN δ inputEta * X ≤
      (S.restrictShading Y).mass := by
    have h_eq : (1/2 : ENNReal) * Kakeya.realRpowENN δ inputEta * X =
        (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
        Kakeya.realRpowENN δ inputEta * F.toBodyFamily.mass := by
      simp [hX_def, mul_assoc, mul_comm, mul_left_comm]
    rw [h_eq]
    exact h_mass_retention
  have h_density_goal : Kakeya.realRpowENN δ densityEta * S.family.toBodyFamily.mass ≤
      (S.restrictShading Y).mass := by
    have h1 : Kakeya.realRpowENN δ densityEta * S.family.toBodyFamily.mass ≤
        (2 : ENNReal) * Kakeya.realRpowENN δ densityEta * X := by
      calc Kakeya.realRpowENN δ densityEta * S.family.toBodyFamily.mass
        ≤ Kakeya.realRpowENN δ densityEta * ((2 : ENNReal) * X) :=
          mul_le_mul_of_nonneg_left h_S_mass_upper' (by positivity)
      _ = (2 : ENNReal) * Kakeya.realRpowENN δ densityEta * X := by
          simp [mul_assoc, mul_comm]
    have h5 : (2 : ENNReal) * Kakeya.realRpowENN δ densityEta * X ≤
        (1/2 : ENNReal) * Kakeya.realRpowENN δ inputEta * X :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    exact le_trans (le_trans h1 h5) h_mass_retention'
  have hV_pos : 0 < Kakeya.deltaTubeVolume δ := by
    have h1 : ENNReal.ofReal (2 * δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
      tube_volume_ge_two_delta_sq δ hδ
    have h2 : 0 < ENNReal.ofReal (2 * δ ^ 2) := by
      apply ENNReal.ofReal_pos.mpr; positivity
    exact lt_of_lt_of_le h2 h1
  have hV_ne_top : Kakeya.deltaTubeVolume δ ≠ ⊤ := by
    have h1 : Kakeya.deltaTubeVolume δ ≤
        ENNReal.ofReal (Real.pi * δ ^ 2 + (8 / 3 : ℝ) * Real.pi * δ ^ 3) :=
      GeometricLemmas.capsule_upper_bound_instantiation δ hδ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have h_mass_le : (S.restrictShading Y).mass ≤ S.family.toBodyFamily.mass := by
    dsimp only [Shading.mass, BodyFamily.mass]
    apply Finset.sum_le_sum
    intro i _
    exact measure_mono ((S.restrictShading Y).subset_body i)
  have h_S_mass_eq : S.family.toBodyFamily.mass = S.family.enncard * Kakeya.deltaTubeVolume δ :=
    tubeFamily_mass_eq_nominal S.family
  have h_F_mass_eq : F.toBodyFamily.mass = F.enncard * Kakeya.deltaTubeVolume δ :=
    tubeFamily_mass_eq_nominal F
  have h_card_from_mass : S.family.enncard ≥
      (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
      Kakeya.realRpowENN δ inputEta * F.enncard := by
    have h9 : S.family.enncard * Kakeya.deltaTubeVolume δ ≥
        (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
        Kakeya.realRpowENN δ inputEta * F.enncard * Kakeya.deltaTubeVolume δ := by
      rw [h_S_mass_eq] at h_mass_le
      rw [h_F_mass_eq] at h_mass_retention
      have h10 : (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
          Kakeya.realRpowENN δ inputEta * (F.enncard * Kakeya.deltaTubeVolume δ) ≤
          S.family.enncard * Kakeya.deltaTubeVolume δ := h_mass_retention.trans h_mass_le
      have h11 : (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
          Kakeya.realRpowENN δ inputEta * (F.enncard * Kakeya.deltaTubeVolume δ) =
          (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
          Kakeya.realRpowENN δ inputEta * F.enncard * Kakeya.deltaTubeVolume δ := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h11] at h10
      exact h10
    have hV_pos' : Kakeya.deltaTubeVolume δ ≠ 0 := hV_pos.ne'
    have h_cancel : ∀ (a b : ENNReal), a * Kakeya.deltaTubeVolume δ ≤ b * Kakeya.deltaTubeVolume δ → a ≤ b := by
      intro a b h
      have h12 : a * Kakeya.deltaTubeVolume δ * (Kakeya.deltaTubeVolume δ)⁻¹ ≤
          b * Kakeya.deltaTubeVolume δ * (Kakeya.deltaTubeVolume δ)⁻¹ :=
        mul_le_mul_of_nonneg_right h (by positivity)
      have h13 : Kakeya.deltaTubeVolume δ * (Kakeya.deltaTubeVolume δ)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel hV_pos' hV_ne_top
      have h14 : (a * Kakeya.deltaTubeVolume δ) * (Kakeya.deltaTubeVolume δ)⁻¹ = a := by
        rw [mul_assoc, h13, mul_one]
      have h15 : (b * Kakeya.deltaTubeVolume δ) * (Kakeya.deltaTubeVolume δ)⁻¹ = b := by
        rw [mul_assoc, h13, mul_one]
      rw [h14, h15] at h12
      exact h12
    exact h_cancel _ _ h9
  have h_card_lower : Kakeya.realRpowENN δ (-2 + cardLoss) ≤ S.family.enncard :=
    h_card_bound.trans h_card_from_mass
  have h_nonempty : S.family.Nonempty := by
    dsimp only [TubeFamily.Nonempty]
    have h_pos : 0 < Kakeya.realRpowENN δ (-2 + cardLoss) := by
      simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hδ]
    have h11 : (0 : ENNReal) < S.family.enncard := h_pos.trans_le h_card_lower
    have h12 : 0 < S.family.card := by
      by_contra h
      have h13 : S.family.card = 0 := by omega
      have h14 : S.family.enncard = 0 := by
        simp [Kakeya.Streamlined.TubeFamily.enncard, h13]
      rw [h14] at h11
      exact False.elim (lt_irrefl 0 h11)
    exact h12
  refine' ⟨S, h_nonempty, h_ball, h_distinct, h_union, _ , _ , h_card_lower⟩
  · exact h_density_goal
  · unfold Kakeya.Streamlined.BodyFamily.IsCKatzTao
    exact h_kt_le

end Kakeya.Assouad
