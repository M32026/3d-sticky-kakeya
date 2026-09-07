module

public import MyLeanRepo.robust_kaufman_projection.Refinement
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Generic refinement energy bound

Given finite sets S' ⊆ S and a measurable kernel K : X → X → ENNReal,
the double integral of K against the uniform measure on S' is bounded by
(|S|/|S'|)² times the double integral against the uniform measure on S.

This is the generic-kernel analogue of `Refinement.energy_bound_of_le_smul`.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Measure Set Finset

namespace RobustKaufmanProjection.GenericRefinement

variable {X : Type*} [MeasurableSpace X] [DecidableEq X] [MeasurableSingletonClass X]

/-- For finite sets S' ⊆ S, the uniform measure on S' is bounded by
    (|S|/|S'|) times the uniform measure on S. -/
lemma refinement_measure_le_generic {S S' : Finset X}
    (hS'_sub : S' ⊆ S) (hS'_nonempty : S'.Nonempty) :
    (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set X) ≤
    ((S.card : ENNReal) / (S'.card : ENNReal)) •
      ((S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set X)) := by
  let c : ENNReal := (S.card : ENNReal) / (S'.card : ENNReal)
  have hS'_pos : (S'.card : ENNReal) ≠ 0 := by
    exact_mod_cast hS'_nonempty.card_pos.ne'
  have hS'_top : (S'.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hS_nonempty : S.Nonempty := hS'_nonempty.mono hS'_sub
  have hS_pos : (S.card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS_nonempty).ne'
  have hS_top : (S.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h1 : Measure.count.restrict (S' : Set X) ≤ Measure.count.restrict (S : Set X) :=
    Measure.restrict_mono hS'_sub le_rfl
  have h21 : (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set X) ≤
      (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set X) :=
    smul_le_smul_left (S'.card : ENNReal)⁻¹ h1
  have h22 : (S'.card : ENNReal)⁻¹ = c * (S.card : ENNReal)⁻¹ := by
    have hdiv : c = (S.card : ENNReal) * (S'.card : ENNReal)⁻¹ := by
      simp [c, div_eq_mul_inv] <;> rfl
    rw [hdiv]
    have h3 : (S.card : ENNReal) * (S'.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ =
        (S'.card : ENNReal)⁻¹ := by
      have h4 : (S.card : ENNReal) * (S.card : ENNReal)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel hS_pos hS_top
      calc
        (S.card : ENNReal) * (S'.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹
          = (S'.card : ENNReal)⁻¹ * ((S.card : ENNReal) * (S.card : ENNReal)⁻¹) := by
            rw [mul_left_comm, ←mul_assoc]
        _ = (S'.card : ENNReal)⁻¹ * 1 := by rw [h4]
        _ = (S'.card : ENNReal)⁻¹ := by rw [mul_one]
    exact h3.symm
  calc
    (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set X)
      ≤ (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set X) := h21
    _ = (c * (S.card : ENNReal)⁻¹) • Measure.count.restrict (S : Set X) := by
        rw [h22]
    _ = c • ((S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set X)) := by
        rw [smul_smul] <;> rfl

/-- Generic refinement bound for any measurable kernel K.

    If S' ⊆ S are finite nonempty sets and μ, μ' are their uniform probability
    measures, then for any measurable kernel K:
    ∫∫ K dμ' dμ' ≤ (|S|/|S'|)² · ∫∫ K dμ dμ.
-/
lemma finset_refinement_bound
    {S S' : Finset X} (hS'_sub : S' ⊆ S) (hS'_nonempty : S'.Nonempty)
    {K : X → X → ENNReal} (hK : Measurable (fun p : X × X => K p.1 p.2)) :
    let μ : Measure X := (S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set X)
    let μ' : Measure X := (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set X)
    (∫⁻ x, ∫⁻ y, K x y ∂μ' ∂μ') ≤
      ((S.card : ENNReal) / (S'.card : ENNReal)) ^ 2 * (∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ) := by
  let μ : Measure X := (S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set X)
  let μ' : Measure X := (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set X)
  let c : ENNReal := (S.card : ENNReal) / (S'.card : ENNReal)
  letI : SFinite (Measure.count.restrict (S : Set X)) :=
    RobustKaufmanProjection.Refinement.sfinite_count_restrict_finset S
  letI : SFinite (Measure.count.restrict (S' : Set X)) :=
    RobustKaufmanProjection.Refinement.sfinite_count_restrict_finset S'
  letI : SFinite μ := instSFiniteHSMulENNRealMeasure (S.card : ENNReal)⁻¹
  letI : SFinite μ' := instSFiniteHSMulENNRealMeasure (S'.card : ENNReal)⁻¹
  have h_le : μ' ≤ c • μ := refinement_measure_le_generic hS'_sub hS'_nonempty
  have h_prod : μ'.prod μ' ≤ c ^ 2 • μ.prod μ :=
    RobustKaufmanProjection.Refinement.prod_mono_smul h_le
  have h3 : ∫⁻ (p : X × X), K p.1 p.2 ∂(μ'.prod μ') ≤
      ∫⁻ (p : X × X), K p.1 p.2 ∂(c ^ 2 • μ.prod μ) :=
    lintegral_mono' h_prod le_rfl
  have h4 : ∫⁻ (p : X × X), K p.1 p.2 ∂(c ^ 2 • μ.prod μ) =
      c ^ 2 * ∫⁻ (p : X × X), K p.1 p.2 ∂(μ.prod μ) := by
    simpa [lintegral_smul_measure] using rfl
  have hK_ae : AEMeasurable (fun p : X × X => K p.1 p.2) (μ'.prod μ') :=
    hK.aemeasurable
  have hK_ae2 : AEMeasurable (fun p : X × X => K p.1 p.2) (μ.prod μ) :=
    hK.aemeasurable
  have h5 : ∫⁻ (p : X × X), K p.1 p.2 ∂(μ'.prod μ') =
      ∫⁻ x, ∫⁻ y, K x y ∂μ' ∂μ' :=
    MeasureTheory.lintegral_prod (fun p : X × X => K p.1 p.2) hK_ae
  have h6 : ∫⁻ (p : X × X), K p.1 p.2 ∂(μ.prod μ) =
      ∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ :=
    MeasureTheory.lintegral_prod (fun p : X × X => K p.1 p.2) hK_ae2
  calc
    (∫⁻ x, ∫⁻ y, K x y ∂μ' ∂μ')
      = ∫⁻ (p : X × X), K p.1 p.2 ∂(μ'.prod μ') := h5.symm
    _ ≤ ∫⁻ (p : X × X), K p.1 p.2 ∂(c ^ 2 • μ.prod μ) := h3
    _ = c ^ 2 * ∫⁻ (p : X × X), K p.1 p.2 ∂(μ.prod μ) := h4
    _ = c ^ 2 * (∫⁻ x, ∫⁻ y, K x y ∂μ ∂μ) := by rw [h6]

end RobustKaufmanProjection.GenericRefinement
