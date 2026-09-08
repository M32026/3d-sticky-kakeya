module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.AssertionCalculus

@[expose] public section

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- Increasing the loss exponent weakens Assertion E.  The difference is
absorbed into the freely quantified accuracy parameter, so no scale split is
needed. -/
theorem assertionE_mono_omega {sigma omega omega' : ℝ}
    (homega : omega ≤ omega') :
    AssertionE.{u} sigma omega → AssertionE.{u} sigma omega' := by
  intro hE epsilon hepsilon
  have hacc : 0 < epsilon + (omega' - omega) := by linarith
  obtain ⟨kappa, eta, hkappa, heta, hEall⟩ :=
    hE (epsilon + (omega' - omega)) hacc
  refine ⟨kappa, eta, hkappa, heta, ?_⟩
  intro delta hdelta iota s T hfamily hdense
  simpa only [show omega + (epsilon + (omega' - omega)) = omega' + epsilon by ring]
    using hEall delta hdelta s T hfamily hdense

/-- Iterate one fixed improvement step.  The hypotheses only request the step
at the exponents that occur before the final iterate. -/
theorem assertionE_iterate_sub {sigma target start alpha : ℝ}
    (hstep : ∀ x, target ≤ x →
      AssertionE.{u} sigma x → AssertionE.{u} sigma (x - alpha)) :
    ∀ n : ℕ,
      (∀ k < n, target ≤ start - (k : ℝ) * alpha) →
      AssertionE.{u} sigma start →
      AssertionE.{u} sigma (start - (n : ℝ) * alpha) := by
  intro n
  induction n with
  | zero =>
      intro _ hstart
      simpa using hstart
  | succ n ih =>
      intro hbefore hstart
      have hprefix : ∀ k < n, target ≤ start - (k : ℝ) * alpha := by
        intro k hk
        exact hbefore k (Nat.lt_succ_of_lt hk)
      have hn : target ≤ start - (n : ℝ) * alpha := hbefore n (Nat.lt_succ_self n)
      have hprev := ih hprefix hstart
      convert hstep (start - (n : ℝ) * alpha) hn hprev using 1 <;>
        push_cast <;> ring

/-- A fixed positive decrement reaches any lower target in finitely many
steps, while every preceding iterate stays above the target. -/
theorem exists_first_sub_iterate_below {target start alpha : ℝ}
    (halpha : 0 < alpha) :
    ∃ n : ℕ,
      start - (n : ℝ) * alpha ≤ target ∧
      ∀ k < n, target ≤ start - (k : ℝ) * alpha := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((start - target) / alpha)
  have hcross : start - (N : ℝ) * alpha < target := by
    have hmul : start - target < (N : ℝ) * alpha := by
      apply (div_lt_iff₀ halpha).mp
      simpa [mul_comm] using hN
    linarith
  have hex : ∃ n : ℕ, start - (n : ℝ) * alpha ≤ target :=
    ⟨N, le_of_lt hcross⟩
  let n : ℕ := Nat.find hex
  refine ⟨n, Nat.find_spec hex, ?_⟩
  intro k hk
  exact le_of_not_ge (Nat.find_min hex hk)

/-- The exact iteration wrapper used in the source proof of Proposition 1.6.
Once the elementary exponent-two bound and the uniform weak reverse step are
available, all remaining iteration and endpoint bookkeeping is automatic. -/
theorem assertionD_implies_assertionE_of_uniform_reverse_step
    {sigma omega start : ℝ}
    (hbase : AssertionE.{u} sigma start)
    (hD : AssertionD.{u} sigma omega)
    (hweak : ∀ t > 0, ∃ alpha > 0,
      ∀ omega', omega + t ≤ omega' →
        AssertionD.{u} sigma omega →
        AssertionE.{u} sigma omega' →
        AssertionE.{u} sigma (omega' - alpha)) :
    AssertionE.{u} sigma omega := by
  apply assertionE_of_forall_gt
  intro target htarget
  have ht : 0 < target - omega := by linarith
  obtain ⟨alpha, halpha, hstep⟩ := hweak (target - omega) ht
  by_cases hstart_target : start ≤ target
  · exact assertionE_mono_omega hstart_target hbase
  · obtain ⟨n, hnle, hnbefore⟩ :=
      exists_first_sub_iterate_below (target := target) (start := start) halpha
    have hit : AssertionE.{u} sigma (start - (n : ℝ) * alpha) := by
      apply assertionE_iterate_sub
        (target := target) (start := start) (alpha := alpha)
      · intro x hx hEx
        apply hstep x
        · linarith
        · exact hD
        · exact hEx
      · exact hnbefore
      · exact hbase
    exact assertionE_mono_omega hnle hit

/-- Proposition 1.6 is reduced to its genuine geometric reverse step and the
elementary exponent-two base estimate. -/
theorem assertions_equivalent_of_uniform_reverse_step
    {sigma omega start : ℝ}
    (hsigma : 0 ≤ sigma)
    (hbase : AssertionE.{u} sigma start)
    (hweak : ∀ t > 0, ∃ alpha > 0,
      ∀ omega', omega + t ≤ omega' →
        AssertionD.{u} sigma omega →
        AssertionE.{u} sigma omega' →
        AssertionE.{u} sigma (omega' - alpha)) :
    AssertionE.{u} sigma omega ↔ AssertionD.{u} sigma omega := by
  constructor
  · exact assertionE_implies_assertionD_sameUniverse hsigma
  · intro hD
    exact assertionD_implies_assertionE_of_uniform_reverse_step
      hbase hD hweak

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.assertionE_mono_omega
#print axioms Kakeya.WangZahl.assertionE_iterate_sub
#print axioms Kakeya.WangZahl.exists_first_sub_iterate_below
#print axioms Kakeya.WangZahl.assertionD_implies_assertionE_of_uniform_reverse_step
#print axioms Kakeya.WangZahl.assertions_equivalent_of_uniform_reverse_step
