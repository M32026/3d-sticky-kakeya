/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Multiplicity

/-!
# The core envelope of the thin-case factoring constant

`Kakeya.ThinCase.factoringApply` — the thin-case application of the corrected Proposition 5.1 —
cannot hold with a comparison constant depending on the Frostman constant `CF` and the fullness
constant `Cfull` alone. The reason is the dyadic pigeonholing that Items 1 and 3 of Proposition
5.1 perform: the retained mass fraction of the pipeline is `(⌊log₂ N⌋ + 1)^{-O(1)}` in the
cardinality `N` of the family, and the outer multiplicity band costs a further
`(⌊log₂ M⌋ + 1)^{-1}` in the number `M` of bodies. A family split into `K` dyadic mass classes
therefore forces a comparison constant `≳ √K`, and `K` may be taken arbitrarily large at fixed
`CF`, `Cfull`, `δ`, `η` and `w₁`. (GWZ Proposition 5.1 states its items with `⪆`/`⪅`, i.e. with
`Kakeya.LEApprox`, which absorbs exactly this logarithmic loss; a Lean statement that pins the
constant to `CF` and `Cfull` asserts something strictly stronger, and false.)

This file introduces the third argument that repairs the statement:
`Kakeya.ThinCase.factoringApplyCore`, an explicit *envelope* for the pipeline losses of
Proposition 5.1 at a family of `Nsegs` segments in `Nbodies` bodies at scale `δ`, together with
the two facts that make the repair safe:

* `Kakeya.ThinCase.factoringApplyCore_spec` — the envelope satisfies the four bounds that the
  repaired `factoringApply` demands of its `Ccore` argument, unconditionally. So the repaired
  statement is not vacuous: its constant bundle is inhabited for every input. * `Kakeya.ThinCase.factoringApplyCore_leApprox_one` — for cardinalities polynomially bounded in
  `δ⁻¹` the envelope is `⪅ 1`, i.e. sub-polynomial in `δ⁻¹`. This is the *budget* check. The theorem below rules this out: every
  cardinality of the envelope enters inside a logarithm.
-/

@[expose] public section

namespace Kakeya.ThinCase

open scoped NNReal
open Kakeya ShadedBody

/-! ### The envelope -/

/-- **The core envelope of the thin-case factoring constant.**

The smallest quantity that dominates all four dyadic-pigeonhole losses of the corrected
Proposition 5.1 at a family of `Nsegs` segments in `Nbodies` bodies at scale `δ`:

* the constant `2` (a bare `Ccore ≥ 2`, which is what rules out the degenerate
  `Cfull → 0`, `factoringApplyConstant → 1` collapse of the un-repaired statement);
* the reciprocal `(c(n, Nsegs, δ))⁻¹` of the retained mass fraction of Item 1
  (`ShadedBody.outerFactoringFamily_refinement.c`);
* the retained fraction of the extra outer dyadic band of Item 3
  (`ShadedBody.outerFactoringFamily_outerConstMultFat.c`);
* the number `⌊log₂ Nbodies⌋ + 1` of dyadic multiplicity bands of the outer family.

It is a *parameter* of the repaired `Kakeya.ThinCase.factoringApply` rather than being inlined
into `Kakeya.ThinCase.factoringApplyConstant`, so that this formula may change without touching
any downstream statement, and so that ball-uniformity is achieved by quantification. -/
noncomputable def factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : NNReal) : NNReal :=
  max 2 (max (ShadedBody.outerFactoringFamily_refinement.c n Nsegs δ)⁻¹
    (max (ShadedBody.outerFactoringFamily_outerConstMultFat.c n Nbodies δ)
      ((Nat.log 2 Nbodies + 1 : ℕ) : NNReal)))

lemma two_le_factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : NNReal) :
    2 ≤ factoringApplyCore n Nsegs Nbodies δ := le_max_left _ _

lemma one_le_factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : NNReal) :
    1 ≤ factoringApplyCore n Nsegs Nbodies δ :=
  le_trans (by norm_num) (two_le_factoringApplyCore n Nsegs Nbodies δ)

lemma inv_refinement_c_le_factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : NNReal) :
    (ShadedBody.outerFactoringFamily_refinement.c n Nsegs δ)⁻¹ ≤
      factoringApplyCore n Nsegs Nbodies δ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

lemma outerConstMultFat_c_le_factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : NNReal) :
    ShadedBody.outerFactoringFamily_outerConstMultFat.c n Nbodies δ ≤
      factoringApplyCore n Nsegs Nbodies δ :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)

lemma natLog_le_factoringApplyCore (n Nsegs Nbodies : ℕ) (δ : NNReal) :
    ((Nat.log 2 Nbodies + 1 : ℕ) : NNReal) ≤ factoringApplyCore n Nsegs Nbodies δ :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

/-- **Existence: the constant bundle of the repaired `factoringApply` is inhabited.**

The four envelope bounds that the repaired `Kakeya.ThinCase.factoringApply` demands of its
`Ccore` argument all hold for `Kakeya.ThinCase.factoringApplyCore`, with no hypothesis on the
data whatsoever: each named quantity is a finite `NNReal`, so their maximum is one too. This is
what makes the repair a genuine statement rather than a vacuous one. -/
theorem factoringApplyCore_spec (n Nsegs Nbodies : ℕ) (δ : NNReal) :
    2 ≤ factoringApplyCore n Nsegs Nbodies δ ∧
    (ShadedBody.outerFactoringFamily_refinement.c n Nsegs δ)⁻¹ ≤
      factoringApplyCore n Nsegs Nbodies δ ∧
    ShadedBody.outerFactoringFamily_outerConstMultFat.c n Nbodies δ ≤
      factoringApplyCore n Nsegs Nbodies δ ∧
    ((Nat.log 2 Nbodies + 1 : ℕ) : NNReal) ≤ factoringApplyCore n Nsegs Nbodies δ :=
  ⟨two_le_factoringApplyCore _ _ _ _, inv_refinement_c_le_factoringApplyCore _ _ _ _,
    outerConstMultFat_c_le_factoringApplyCore _ _ _ _, natLog_le_factoringApplyCore _ _ _ _⟩

/-! ### The budget: the envelope is sub-polynomial in `δ⁻¹` -/

/-- The maximum of two functions that are each `⪅ 1` is `⪅ 1`. -/
lemma leApprox_one_max {X Y : NNReal → NNReal} (hX : X ⪅ fun _ : NNReal => (1 : NNReal))
    (hY : Y ⪅ fun _ : NNReal => (1 : NNReal)) :
    (fun ρ : NNReal => max (X ρ) (Y ρ)) ⪅ fun _ : NNReal => (1 : NNReal) := by
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := hX ε hε
  obtain ⟨C₂, hC₂⟩ := hY ε hε
  refine ⟨max C₁ C₂, fun ρ hρ hρ1 => ?_⟩
  simp only [mul_one] at hC₁ hC₂ ⊢
  exact max_le ((hC₁ ρ hρ hρ1).trans (by gcongr; exact le_max_left _ _))
    ((hC₂ ρ hρ hρ1).trans (by gcongr; exact le_max_right _ _))

/-- `⌊log₂ m⌋ ≤ log₂ m` as reals, including the degenerate `m = 0`. -/
lemma natLog_le_logb (m : ℕ) : ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.logb 2 (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · have hpow : (2 : ℕ) ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm.ne'
    have hpowr : ((2 : ℝ)) ^ Nat.log 2 m ≤ (m : ℝ) := by
      exact_mod_cast hpow
    have hposr : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 m := by positivity
    have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num) hposr hpowr
    have hval : Real.logb 2 ((2 : ℝ) ^ Nat.log 2 m) = ((Nat.log 2 m : ℕ) : ℝ) := by
      rw [Real.logb_pow (2 : ℝ) (2 : ℝ) (Nat.log 2 m)]
      simp
    rwa [hval] at hmono

/-- **The dyadic band count is sub-polynomial**: if the cardinality `N ρ` is bounded by a fixed
power of `ρ⁻¹`, then `⌊log₂ (N ρ)⌋ + 1 ⪅ 1`. -/
lemma natLog_succ_leApprox_one {K : ℕ} {N : NNReal → ℕ}
    (hN : ∀ ρ : NNReal, 0 < ρ → ρ ≤ 1 → ((N ρ : ℕ) : NNReal) ≤ (ρ⁻¹) ^ K) :
    (fun ρ : NNReal => ((Nat.log 2 (N ρ) + 1 : ℕ) : NNReal)) ⪅
      fun _ : NNReal => (1 : NNReal) := by
  have hratio : (fun ρ : NNReal => ((N ρ : ℕ) : NNReal) / 1) ≲ fun ρ : NNReal => (ρ⁻¹) ^ K := by
    refine ⟨1, fun ρ hρ hρ1 => ?_⟩
    simpa using hN ρ hρ hρ1
  refine Kakeya.LEApprox.mono_left
    (X' := fun ρ : NNReal => 1 + Real.toNNReal
      (Real.logb 2 ((((N ρ : ℕ) : NNReal) : ℝ) / ((1 : NNReal) : ℝ))))
    ((ShadedBody.toNNReal_logb_div_leApprox_one_pow hratio).const_add_one 1)
    fun ρ _ _ => ?_
  have hcast : ((Nat.log 2 (N ρ) + 1 : ℕ) : NNReal)
      = 1 + Real.toNNReal ((Nat.log 2 (N ρ) : ℕ) : ℝ) := by
    simp [add_comm]
  change ((Nat.log 2 (N ρ) + 1 : ℕ) : NNReal) ≤
    1 + Real.toNNReal (Real.logb 2 ((((N ρ : ℕ) : NNReal) : ℝ) / ((1 : NNReal) : ℝ)))
  rw [hcast]
  refine add_le_add le_rfl (Real.toNNReal_mono ?_)
  simpa using natLog_le_logb (N ρ)

/-- **The Item 1 loss is sub-polynomial** for polynomially bounded cardinalities: the reciprocal
of the retained mass fraction `ShadedBody.outerFactoringFamily_refinement.c` factors as the
product of the Step 1, Steps 2–3 and Step 5 losses, and in each of the three the cardinality and
the scale enter only inside a logarithm. -/
lemma inv_refinement_c_leApprox_one (n K : ℕ) {N : NNReal → ℕ}
    (hN : ∀ ρ : NNReal, 0 < ρ → ρ ≤ 1 → ((N ρ : ℕ) : NNReal) ≤ (ρ⁻¹) ^ K) :
    (fun ρ : NNReal => (ShadedBody.outerFactoringFamily_refinement.c n (N ρ) ρ)⁻¹) ⪅
      fun _ : NNReal => (1 : NNReal) := by
  -- the three factors
  have hstep1 : (fun ρ : NNReal => Kakeya.factoringStep1AtScaleConstant n (N ρ) ρ) ⪅
      fun _ : NNReal => (1 : NNReal) := by
    have hratio : (fun ρ : NNReal => Kakeya.step1UpperBdAtScale n (N ρ) /
        Kakeya.step1LowerBdAtScale n ρ) ≲ fun ρ : NNReal => (ρ⁻¹) ^ (K + n) := by
      refine ⟨2 ^ n * (n.factorial : NNReal), fun ρ hρ hρ1 => ?_⟩
      change Kakeya.step1UpperBdAtScale n (N ρ) / Kakeya.step1LowerBdAtScale n ρ ≤
        2 ^ n * (n.factorial : NNReal) * (ρ⁻¹) ^ (K + n)
      rw [Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (N ρ) hρ]
      have hinv : ((ρ : NNReal) ^ n)⁻¹ = (ρ⁻¹) ^ n := (inv_pow ρ n).symm
      rw [hinv, pow_add]
      calc 2 ^ n * (n.factorial : NNReal) * ((N ρ : ℕ) : NNReal) * (ρ⁻¹) ^ n
          ≤ 2 ^ n * (n.factorial : NNReal) * ((ρ⁻¹) ^ K) * (ρ⁻¹) ^ n := by
            gcongr
            exact hN ρ hρ hρ1
        _ = 2 ^ n * (n.factorial : NNReal) * ((ρ⁻¹) ^ K * (ρ⁻¹) ^ n) := by ring
    simpa [Kakeya.factoringStep1AtScaleConstant_def] using
      ShadedBody.factoringStep1PigeonholeConstant_leApprox_one_pow hratio
  have hband : (fun ρ : NNReal => ((Nat.log 2 (N ρ) + 1 : ℕ) : NNReal)) ⪅
      fun _ : NNReal => (1 : NNReal) := natLog_succ_leApprox_one hN
  have hstep23 : (fun ρ : NNReal =>
      ((Kakeya.factoringStep2Step3Constant (N ρ) : ℕ) : NNReal)) ⪅
      fun _ : NNReal => (1 : NNReal) := by
    refine Kakeya.LEApprox.mono_left
      (X' := fun ρ : NNReal => 4 * (((((Nat.log 2 (N ρ) + 1 : ℕ) : NNReal) *
        ((Nat.log 2 (N ρ) + 1 : ℕ) : NNReal)) * ((Nat.log 2 (N ρ) + 1 : ℕ) : NNReal)) *
        ((Nat.log 2 (N ρ) + 1 : ℕ) : NNReal)))
      ((ShadedBody.leApprox_one_mul (ShadedBody.leApprox_one_mul
        (ShadedBody.leApprox_one_mul hband hband) hband) hband).const_mul_one 4)
      fun ρ _ _ => ?_
    rw [Kakeya.factoringStep2Step3Constant_eq]
    push_cast
    ring_nf
    exact le_rfl
  have hstep5 : (fun ρ : NNReal => ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
      (ShadedBody.step5PackingRatio n (N ρ) ρ)) ⪅ fun _ : NNReal => (1 : NNReal) := by
    have hratio : (fun ρ : NNReal => ShadedBody.step5PackingRatio n (N ρ) ρ / 1) ≲
        fun ρ : NNReal => (ρ⁻¹) ^ (K + n) := by
      refine ⟨2 ^ n * (2 ^ n * (n.factorial : NNReal)), fun ρ hρ hρ1 => ?_⟩
      have hone : (1 : NNReal) ≤ (ρ⁻¹) ^ K := by
        refine one_le_pow₀ ?_
        rw [one_le_inv_iff₀]
        exact ⟨hρ, hρ1⟩
      have hmax : ((max 1 (N ρ) : ℕ) : NNReal) ≤ (ρ⁻¹) ^ K := by
        rw [Nat.cast_max]
        exact max_le (by exact_mod_cast hone) (hN ρ hρ hρ1)
      change ShadedBody.step5PackingRatio n (N ρ) ρ / 1 ≤
        2 ^ n * (2 ^ n * (n.factorial : NNReal)) * (ρ⁻¹) ^ (K + n)
      rw [div_one, ShadedBody.step5PackingRatio, mul_div_assoc,
        Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 (N ρ)) hρ]
      have hinv : ((ρ : NNReal) ^ n)⁻¹ = (ρ⁻¹) ^ n := (inv_pow ρ n).symm
      rw [hinv, pow_add]
      calc (2 : NNReal) ^ n * (2 ^ n * (n.factorial : NNReal) *
              ((max 1 (N ρ) : ℕ) : NNReal) * (ρ⁻¹) ^ n)
          ≤ 2 ^ n * (2 ^ n * (n.factorial : NNReal) * ((ρ⁻¹) ^ K) * (ρ⁻¹) ^ n) := by
            gcongr
        _ = 2 ^ n * (2 ^ n * (n.factorial : NNReal)) * ((ρ⁻¹) ^ K * (ρ⁻¹) ^ n) := by ring
    have hpig := ShadedBody.factoringStep1PigeonholeConstant_leApprox_one_pow
      (a := fun _ : NNReal => (1 : NNReal))
      (b := fun ρ : NNReal => ShadedBody.step5PackingRatio n (N ρ) ρ) hratio
    refine Kakeya.LEApprox.mono_left
      (X' := fun ρ : NNReal => (4 * ((Kakeya.factoringStep5OverlapConstant n : ℕ) : NNReal)) *
        Kakeya.factoringStep1PigeonholeConstant 1 (ShadedBody.step5PackingRatio n (N ρ) ρ))
      (hpig.const_mul_one _) fun ρ _ _ => ?_
    simp only [ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant,
      Kakeya.factoringStep1PigeonholeConstant_eq]
    ring_nf
    exact le_rfl
  -- assemble
  have hprod := ShadedBody.leApprox_one_mul (ShadedBody.leApprox_one_mul hstep1 hstep23) hstep5
  refine Kakeya.LEApprox.mono_left hprod fun ρ _ _ => ?_
  rw [ShadedBody.outerFactoringFamily_refinement.c,
    ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant]
  simp only [mul_inv, inv_inv]
  exact le_rfl

/-- **The budget check.**

For cardinalities bounded by a fixed power of `δ⁻¹`, the core envelope is `⪅ 1`: sub-polynomial
in `δ⁻¹`, in the sense of `Kakeya.LEApprox`. So the repaired thin-case constant still satisfies
the `δ ^ (-η)` threshold that `Kakeya.VeryNotSticky.CaseScale.transverse_ballFill` asks for at a
small fixed `η`, and the repair does not silently make `CaseScale` unsatisfiable.

Every cardinality of the envelope enters inside a logarithm: this is the whole content, and it
is exactly the reason no packing bound of the shape `w₁ ^ (-n)` may be imported into the
envelope unexamined. Such a factor is harmless *here* — the Step 5 packing number `M` enters
`ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant` only through
`Kakeya.factoringStep1FiberPigeonholeConstant 1 M = (1 + log₂ M)₊` — and that is why the
hypotheses below need only a polynomial bound on the cardinalities. -/
theorem factoringApplyCore_leApprox_one (n K : ℕ) {Nsegs Nbodies : NNReal → ℕ}
    (hNsegs : ∀ ρ : NNReal, 0 < ρ → ρ ≤ 1 → ((Nsegs ρ : ℕ) : NNReal) ≤ (ρ⁻¹) ^ K)
    (hNbodies : ∀ ρ : NNReal, 0 < ρ → ρ ≤ 1 → ((Nbodies ρ : ℕ) : NNReal) ≤ (ρ⁻¹) ^ K) :
    (fun ρ : NNReal => factoringApplyCore n (Nsegs ρ) (Nbodies ρ) ρ) ⪅
      fun _ : NNReal => (1 : NNReal) := by
  have h2 : (fun _ : NNReal => (2 : NNReal)) ⪅ fun _ : NNReal => (1 : NNReal) :=
    ShadedBody.leApprox_one_const 2
  have hfat : (fun ρ : NNReal =>
      ShadedBody.outerFactoringFamily_outerConstMultFat.c n (Nbodies ρ) ρ) ⪅
      fun _ : NNReal => (1 : NNReal) := by
    refine Kakeya.LEApprox.mono_left (X' := fun _ : NNReal => (1 : NNReal))
      (ShadedBody.leApprox_one_const 1) fun ρ _ _ => ?_
    simp only [ShadedBody.outerFactoringFamily_outerConstMultFat.c]
    rw [inv_le_one₀]
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    · exact_mod_cast Nat.succ_pos _
  exact leApprox_one_max h2 (leApprox_one_max (inv_refinement_c_leApprox_one n K hNsegs)
    (leApprox_one_max hfat (natLog_succ_leApprox_one hNbodies)))

end Kakeya.ThinCase

end
