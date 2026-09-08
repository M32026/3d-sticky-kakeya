module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- The actual fine refinement already defines a next retained state. Paying
the additional selector denominator changes its recorded retention coefficient. -/
theorem exists_paid_retained_state_from_trial_lift_w100
    {iota : Type uI} {delta d : NNReal}
    {B : Finset iota} {V : iota -> ShadedTube delta E}
    (current : RetainedStateW94 B V)
    (hd : 0 < delta) (hdd : delta <= d) (hd1 : d < 1)
    (M CM Ktr : Nat) (Cpass : NNReal) (hCpass : 1 <= Cpass)
    (G : Finset iota) (Z : iota -> ShadedTube delta E)
    (hGne : G.Nonempty) (hGsub : G ⊆ current.active)
    (hZ : ∀ i ∈ G, (Z i).toTube = (current.shading i).toTube ∧
      (Z i).shade ⊆ (current.shading i).shade)
    (hret : trialRetainedFractionW94 d Ktr *
      (∑ i ∈ current.active, volume (current.shading i).shade) <=
        ∑ i ∈ G, volume (Z i).shade) :
    ∃ next : RetainedStateW94 B V,
      next.active = G ∧ next.shading = Z ∧
      next.retained = current.retained / actualPaidPassCostW94 delta d M CM Ktr Cpass ∧
      next.active ⊆ G ∧
      (∀ i ∈ next.active, (next.shading i).shade ⊆ (Z i).shade) ∧
      ((Cpass : ENNReal) * fullPassDenominatorW87 delta M CM)⁻¹ *
        (∑ i ∈ G, volume (Z i).shade) <=
          ∑ i ∈ next.active, volume (next.shading i).shade ∧
      current.retained / uniformPaidPassCostW95 delta M CM Ktr Cpass <= next.retained := by
  have hdelta1 : delta < 1 := hdd.trans_lt hd1
  have hdp : 0 < d := hd.trans_le hdd
  have hlog (x : NNReal) (hx : 0 < x) (hx1 : x <= 1) :
      0 <= Real.log (1 / (x : Real)) :=
    Real.log_nonneg ((le_div_iff₀ (show (0 : Real) < x from hx)).mpr
      (by simpa only [one_mul] using (show (x : Real) <= 1 from hx1)))
  have hlogDelta := hlog delta hd hdelta1.le
  have hlogD := hlog d hdp hd1.le
  have hL1 : 1 <= 2 + Real.log (1 / (delta : Real)) / Real.log 2 := by
    have h := div_nonneg hlogDelta (Real.log_pos (by norm_num : (1 : Real) < 2)).le
    linarith
  have hceil : (1 : ENNReal) <=
      Nat.ceil ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ CM) := by
    have h : (1 : Real) <=
        Nat.ceil ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ CM) :=
      (one_le_pow₀ hL1).trans (Nat.le_ceil _)
    exact_mod_cast h
  have hden : 1 <= fullPassDenominatorW87 delta M CM := by
    unfold fullPassDenominatorW87 sourceLambdaMNatW87 sourceLambdaINatW87 sourceLambdaBalNatW87
    exact one_le_mul (one_le_mul (one_le_mul
      (one_le_mul (by norm_num) (by exact_mod_cast (Nat.le_add_left 1 M))) hceil) hceil) hceil
  let selector : ENNReal := (Cpass : ENNReal) * fullPassDenominatorW87 delta M CM
  have hselector : 1 <= selector := one_le_mul (by exact_mod_cast hCpass) hden
  have hselectorPos : 0 < selector := zero_lt_one.trans_le hselector
  have hselectorTop : selector < ⊤ := by
    dsimp [selector, fullPassDenominatorW87]
    finiteness
  have htrialPos : 0 < trialRetainedFractionW94 d Ktr :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
  have htrialTop : trialRetainedFractionW94 d Ktr < ⊤ := ENNReal.ofReal_lt_top
  let r : ENNReal := selector⁻¹ * trialRetainedFractionW94 d Ktr
  have hr : 0 < r := ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hselectorTop.ne) htrialPos.ne'
  have hrTop : r < ⊤ := ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hselectorPos.ne')) htrialTop
  have hinv : selector⁻¹ <= 1 := ENNReal.inv_le_one.mpr hselector
  have hnextMass : r * (∑ i ∈ current.active, volume (current.shading i).shade) <=
      ∑ i ∈ G, volume (Z i).shade := by
    dsimp only [r]
    rw [mul_assoc]
    exact (mul_le_mul_left' hret _).trans
      ((mul_le_mul_right' hinv _).trans_eq (one_mul _))
  let next : RetainedStateW94 B V :=
    { active := G
      shading := Z
      active_nonempty := hGne
      active_subset := hGsub.trans current.active_subset
      same_tube := fun i hi => (hZ i hi).1.trans (current.same_tube i (hGsub hi))
      subshade := fun i hi => (hZ i hi).2.trans (current.subshade i (hGsub hi))
      retained := r * current.retained
      retained_pos := ENNReal.mul_pos hr.ne' current.retained_pos.ne'
      retained_finite := ENNReal.mul_lt_top hrTop current.retained_finite
      mass_retention := by
        rw [mul_assoc]
        exact (mul_le_mul_left' current.mass_retention r).trans hnextMass }
  have hpaid : next.retained =
      current.retained / actualPaidPassCostW94 delta d M CM Ktr Cpass := by
    change (selector⁻¹ * trialRetainedFractionW94 d Ktr) * current.retained =
      current.retained / (selector / trialRetainedFractionW94 d Ktr)
    rw [div_eq_mul_inv, ENNReal.inv_div (Or.inr hselectorTop.ne) (Or.inr hselectorPos.ne'),
      div_eq_mul_inv]
    ac_rfl
  refine ⟨next, rfl, rfl, hpaid, Finset.Subset.refl _, (fun i hi => Set.Subset.refl _), ?_, ?_⟩
  · exact (mul_le_mul_right' hinv _).trans_eq (one_mul _)
  · rw [hpaid]
    apply ENNReal.div_le_div_left
    unfold uniformPaidPassCostW95 actualPaidPassCostW94
    apply ENNReal.div_le_div_left
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 1 + Real.log (1 / (d : Real)))
    · apply add_le_add_right
      apply Real.log_le_log (by positivity)
      exact one_div_le_one_div_of_le (show (0 : Real) < delta from hd) (show (delta : Real) <= d from hdd)
    · exact neg_nonpos.mpr (Nat.cast_nonneg _)

end

end Kakeya.ml1Boot.TrialRestartW94
