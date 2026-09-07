module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.EasyCaseMLtN
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.EasyCaseMEqN
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.HardCase
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.PositiveRank
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.StratumImage
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.FlatTaylorEstimate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard.General

open MeasureTheory Module
open scoped ContDiff

lemma case_n_zero (m : ℕ) (f : E m → E 0) :
    volume (f '' {x | IsCriticalPoint f x}) = 0 := by
  have h1 : ∀ (x : E m), ¬ IsCriticalPoint f x := by
    intro x hx
    have h2 : fderivRank f x < (0 : ℕ) := hx.2
    exact Nat.not_lt_zero _ h2
  have h_set : {x : E m | IsCriticalPoint f x} = ∅ := by
    simpa [Set.ext_iff] using h1
  rw [h_set]
  simp

lemma finrank_E (k : ℕ) : Module.finrank ℝ (E k) = k := by
  simp [E]

lemma case_m_lt_n (m n : ℕ) (h : m < n) (f : E m → E n) (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | IsCriticalPoint f x}) = 0 := by
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have h_finrank : Module.finrank ℝ (E m) = m := finrank_E m
  have h2 : dimH (Set.range f) ≤ (Module.finrank ℝ (E m) : ENNReal) := ContDiff.dimH_range_le h1
  have h2' : dimH (Set.range f) ≤ (m : ENNReal) := by
    rw [h_finrank] at h2
    exact h2
  have h3 : dimH (Set.range f) < (n : ENNReal) := by
    exact h2'.trans_lt (by exact_mod_cast h)
  have h4 : (MeasureTheory.Measure.hausdorffMeasure (n : NNReal)) (Set.range f) = 0 :=
    hausdorffMeasure_of_dimH_lt h3
  have h5 : (μHE[n] : Measure (E n)) = volume := EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  have h_def : (μHE[n] : Measure (E n)) = _ := MeasureTheory.Measure.euclideanHausdorffMeasure_def n
  have h6 : (μHE[n] : Measure (E n)) (Set.range f) = 0 := by
    rw [h_def]
    rw [Measure.smul_apply]
    exact mul_eq_zero.mpr (Or.inr h4)
  have h_volume : volume (Set.range f) = 0 := by
    rw [← h5]
    exact h6
  have h7 : f '' {x | IsCriticalPoint f x} ⊆ Set.range f := by
    intro y hy
    rcases hy with ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have h8 : volume (f '' {x | IsCriticalPoint f x}) ≤ volume (Set.range f) := measure_mono h7
  rw [h_volume] at h8
  simpa using h8

lemma case_m_eq_n (m n : ℕ) (h : m = n) (f : E m → E n) (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | IsCriticalPoint f x}) = 0 := by
  subst h
  let s : Set (E m) := {x | IsCriticalPoint f x}
  have h_diff : ∀ (x : E m), DifferentiableAt ℝ f x := fun x =>
    hf.differentiable (by simp) x
  have h_fderiv : ∀ (x : E m), HasFDerivAt f (fderiv ℝ f x) x := fun x =>
    (h_diff x).hasFDerivAt
  have h_fderivWithin : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x := by
    intro x hx
    exact (h_fderiv x).hasFDerivWithinAt
  have h_main : ∀ x ∈ s, (fderiv ℝ f x).toLinearMap.det = 0 := by
    intro x hx
    have h1 : fderivRank f x < m := hx.1
    let T := (fderiv ℝ f x).toLinearMap
    have h2 : Module.finrank ℝ (LinearMap.range T) < m := h1
    have h3 : LinearMap.range T ≠ ⊤ := by
      by_contra h4
      rw [h4] at h2
      have h5 : Module.finrank ℝ ( (⊤ : Submodule ℝ (E m)) ) = m := by
        simp [finrank_E m]
      rw [h5] at h2
      linarith
    have h_iff : LinearMap.ker T = ⊥ ↔ LinearMap.range T = ⊤ :=
      LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank rfl
    have h4 : LinearMap.ker T ≠ ⊥ := by
      intro h6
      have h7 : LinearMap.range T = ⊤ := h_iff.mp h6
      exact h3 h7
    exact LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h4
  exact MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume h_fderivWithin h_main

/-- Lemma 18 (Full induction).
    Prove Sard's theorem by well-founded induction on m, with n quantified.
    Base cases:
      - n = 0: trivial
      - m < n: Hausdorff dimension argument
      - m = n: equal-dimension Sard lemma
    Inductive step (0 < n < m): apply hard_case_sard, providing
      the induction hypothesis plus PositiveRank, StratumImage, and
      FlatTaylorEstimate results. -/
theorem sard_induction (m n : ℕ) :
    ∀ (f : E m → E n), ContDiff ℝ ∞ f →
    volume (f '' {x | IsCriticalPoint f x}) = 0 := by
  have h_main : ∀ (m : ℕ), ∀ (n : ℕ), ∀ (f : E m → E n), ContDiff ℝ ∞ f →
      volume (f '' {x | IsCriticalPoint f x}) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro n f hf
      by_cases hnm : n < m
      · -- Hard case: 0 < n < m
        by_cases hn_pos : 0 < n
        · -- 0 < n < m: apply hard_case_sard
          have hnm' : 0 < n ∧ n < m := ⟨hn_pos, hnm⟩
          have h_local_fact : ∀ (x : E m), x ∈ {x : E m | 0 < fderivRank f x ∧ fderivRank f x < n} →
              ∃ (U : Set (E m)), IsOpen U ∧ x ∈ U ∧
                volume (f '' ({x : E m | 0 < fderivRank f x ∧ fderivRank f x < n} ∩ U)) = 0 :=
            positive_rank_local_fact hnm' f hf (fun k hk j g hg => ih k hk j g hg)
          exact hard_case_sard hnm' f
            (positive_rank_critical_null f h_local_fact)
            (fun j hj => stratum_image_null hnm' (by linarith) f hf j hj
              (fun k hk t g hg => ih k hk t g hg))
            (flat_set_image_null hnm' f hf)
        · -- n = 0, contradiction with hn_pos
          have h0 : n = 0 := by omega
          subst h0
          exact case_n_zero m f
      · -- ¬ (n < m), so m ≤ n
        by_cases h0 : n = 0
        · subst h0
          exact case_n_zero m f
        · by_cases h1 : m < n
          · exact case_m_lt_n m n h1 f hf
          · have h2 : m = n := by omega
            exact case_m_eq_n m n h2 f hf
  exact h_main m n

end ForMathlib.Analysis.Calculus.Sard.General
