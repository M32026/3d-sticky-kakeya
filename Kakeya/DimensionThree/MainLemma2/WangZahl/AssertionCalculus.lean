module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- Assertion `D` is monotone in the loss exponent: increasing `omega` weakens
the estimate. The `delta > 1` branch is vacuous for a nonempty family because
the canonical Katz--Tao constant is at least one. -/
theorem assertionD_mono_omega {sigma omega omega' : ℝ}
    (homega : omega ≤ omega') :
    AssertionD.{u} sigma omega → AssertionD.{u} sigma omega' := by
  intro hD epsilon hepsilon
  obtain ⟨kappa, eta, hkappa, heta, hDall⟩ := hD epsilon hepsilon
  refine ⟨kappa, eta, hkappa, heta, ?_⟩
  intro delta hdelta iota s T hfamily hdense hm hell
  by_cases hs : s.Nonempty
  · by_cases hdelta1 : delta ≤ 1
    · have hpow : (delta : ENNReal) ^ (omega' + epsilon) ≤
          (delta : ENNReal) ^ (omega + epsilon) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hdelta1)
          (by linarith)
      calc
        (kappa : ENNReal) * (delta : ENNReal) ^ (omega' + epsilon) *
              (s.card : ENNReal) * tubeVolume delta *
              (((s.card : ENNReal) * tubeVolume delta ^ (1 / 2 : ℝ)) ^ (-sigma)) ≤
            (kappa : ENNReal) * (delta : ENNReal) ^ (omega + epsilon) *
              (s.card : ENNReal) * tubeVolume delta *
              (((s.card : ENNReal) * tubeVolume delta ^ (1 / 2 : ℝ)) ^ (-sigma)) := by
                gcongr
        _ ≤ volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) :=
          hDall delta hdelta s T hfamily hdense hm hell
    · have hm1 : 1 ≤ katzTaoConvexWolffConstant s T :=
        one_le_katzTaoConvexWolffConstant_of_nonempty hdelta s T hs
      have hdelta_gt : (1 : ENNReal) < delta := by
        exact_mod_cast lt_of_not_ge hdelta1
      have hpow_lt : (delta : ENNReal) ^ (-eta) < 1 :=
        ENNReal.rpow_lt_one_of_one_lt_of_neg hdelta_gt (by linarith)
      exact ((not_lt_of_ge (hm1.trans hm)) hpow_lt).elim
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp [iUnionShade_empty]

/-- Assertion `D` is closed from above in `omega`; the gap to a larger exponent
is absorbed by half of the requested accuracy. -/
theorem assertionD_of_forall_gt {sigma omega : ℝ}
    (hD : ∀ omega' > omega, AssertionD.{u} sigma omega') :
    AssertionD.{u} sigma omega := by
  intro epsilon hepsilon
  have homega_lt : omega < omega + epsilon / 2 := by linarith
  obtain ⟨kappa, eta, hkappa, heta, hDall⟩ :=
    hD (omega + epsilon / 2) homega_lt (epsilon / 2) (by linarith)
  refine ⟨kappa, eta, hkappa, heta, ?_⟩
  intro delta hdelta iota s T hfamily hdense hm hell
  simpa only [show omega + epsilon / 2 + epsilon / 2 = omega + epsilon by ring] using
    hDall delta hdelta s T hfamily hdense hm hell

/-- Assertion `E` has the same closure-from-above property. -/
theorem assertionE_of_forall_gt {sigma omega : ℝ}
    (hE : ∀ omega' > omega, AssertionE.{u} sigma omega') :
    AssertionE.{u} sigma omega := by
  intro epsilon hepsilon
  have homega_lt : omega < omega + epsilon / 2 := by linarith
  obtain ⟨kappa, eta, hkappa, heta, hEall⟩ :=
    hE (omega + epsilon / 2) homega_lt (epsilon / 2) (by linarith)
  refine ⟨kappa, eta, hkappa, heta, ?_⟩
  intro delta hdelta iota s T hfamily hdense
  simpa only [show omega + epsilon / 2 + epsilon / 2 = omega + epsilon by ring] using
    hEall delta hdelta s T hfamily hdense

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.assertionD_mono_omega
#print axioms Kakeya.WangZahl.assertionD_of_forall_gt
#print axioms Kakeya.WangZahl.assertionE_of_forall_gt
