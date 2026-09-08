/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.FrostmanEstimateMono
public import Kakeya.PartialEstimates

/-!
# The monotone envelope of the admissible step sizes

The proof of GWZ Main Lemma 1 is a bootstrapping argument: from `K_KT(β)` one
shows that `K_F(γ)` can always be improved to `K_F(γ - c)` for some step size
`c > 0` which is *uniform* for `γ` in a fixed interval `[γ₀, 1]`.

This file records the elementary bookkeeping that turns such uniform steps into a
single monotone step function `ν`.  We introduce the set

```
S(β, γ₀) = {c ∈ (0,1] : ∀ γ ∈ [γ₀,1], K_KT(β) → K_F(γ) → K_F(γ - c)}
```

of admissible step sizes (`Kakeya.frostmanStepSet`), show that it is downward
closed in `c` and increasing in `γ₀`, and deduce that `ν γ = (sSup S(β,γ))/2` is
a monotone, strictly positive, *admissible* step function
(`Kakeya.exists_monotoneOn_frostmanStep`).

The main point of the definition is that `S(β, γ₀)` is defined *without* assuming
`K_KT(β)`: the hypothesis `K_KT(β)` sits inside the defining condition.  This is
what allows `ν` to be produced before any family of tubes is given, as the
bootstrapping lemma requires.
-/

@[expose] public section

namespace Kakeya

universe u

variable (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The set `S(β, γ₀)` of **admissible step sizes** at base exponent `β` above the
threshold `γ₀`: those `c ∈ (0,1]` such that, for every `γ ∈ [γ₀, 1]`, the partial
Katz–Tao estimate `K_KT(β)` together with the partial Frostman estimate `K_F(γ)`
implies the improved partial Frostman estimate `K_F(γ - c)`.

Note that this is defined *without* assuming `KatzTaoEstimate E β`: that
hypothesis is a fixed proposition placed inside the defining condition.  This is
what allows the step function of `Kakeya.exists_monotoneOn_frostmanStep` to be
produced before any family of tubes is given. -/
def frostmanStepSet (β γ₀ : ℝ) : Set ℝ :=
  {c | c ∈ Set.Ioc (0 : ℝ) 1 ∧ ∀ γ ∈ Set.Icc γ₀ 1,
    KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E γ → FrostmanEstimate.{u} E (γ - c)}

variable {E}

/-- `S(β, γ₀)` is downward closed: shrinking an admissible step size keeps it
admissible, since a smaller step lands at a larger exponent and
`Kakeya.FrostmanEstimate.mono` is monotone in the exponent.

The dimension hypothesis `Module.finrank ℝ E = 3` is exactly that of
`Kakeya.FrostmanEstimate.mono`, which supplies the `Nontrivial E` instance itself. -/
theorem frostmanStepSet_downwardClosed (hE : Module.finrank ℝ E = 3)
    {β γ₀ c c' : ℝ} (hc : c ∈ frostmanStepSet.{u} E β γ₀) (hc'_pos : 0 < c')
    (hc'_le : c' ≤ c) : c' ∈ frostmanStepSet.{u} E β γ₀ := by
  rcases hc with ⟨hc_Ioc, hc_forall⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hc'_pos, ?_⟩
    exact hc'_le.trans hc_Ioc.2
  · intro γ hγ hKT hKF
    have hFc : FrostmanEstimate.{u} E (γ - c) := hc_forall γ hγ hKT hKF
    have hsub : γ - c ≤ γ - c' := sub_le_sub_left hc'_le γ
    exact FrostmanEstimate.mono hE hsub hFc

/-- `S(β, γ₀)` is increasing in the threshold `γ₀`: the defining condition for
`S(β, γ₁)` quantifies over the smaller interval `[γ₁, 1] ⊆ [γ₀, 1]`. -/
theorem frostmanStepSet_subset {β γ₀ γ₁ : ℝ} (hγ : γ₀ ≤ γ₁) :
    frostmanStepSet.{u} E β γ₀ ⊆ frostmanStepSet.{u} E β γ₁ := by
  intro c hc
  rcases hc with ⟨hc_Ioc, hc_forall⟩
  refine ⟨hc_Ioc, ?_⟩
  intro γ hγ_icc
  apply hc_forall γ
  exact Set.Icc_subset_Icc hγ le_rfl hγ_icc

/-- **The monotone envelope, membership form.**  Suppose that for every threshold
`γ₀ ∈ (β, 1]` there is at least one admissible step size.  Then there is a single
step function `ν : ℝ → ℝ` which is monotone and strictly positive on `(β, 1]` and
whose value at `γ` is itself an admissible step size at threshold `γ`.

The witness produced by the intended proof is `ν γ = sSup (frostmanStepSet E β γ) / 2`
for `γ ∈ (β, 1]`, extended by `0` outside that interval; halving the supremum is
what makes the value attained, via `Kakeya.frostmanStepSet_downwardClosed`.

The blueprint's standing hypotheses `0 ≤ β` and `β < 1` are omitted: both are inert
here, since every clause of the conclusion is quantified over `Set.Ioc β 1`, which is
empty when `1 ≤ β`.  A consumer that carries them, such as GWZ Lemma 8.1, can apply
this lemma unchanged. -/
theorem exists_monotoneOn_mem_frostmanStepSet
    (hE : Module.finrank ℝ E = 3) {β : ℝ}
    (hne : ∀ γ₀ ∈ Set.Ioc β 1, (frostmanStepSet.{u} E β γ₀).Nonempty) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc β 1) ∧ (∀ γ ∈ Set.Ioc β 1, 0 < ν γ) ∧
      (∀ γ ∈ Set.Ioc β 1, ν γ ∈ frostmanStepSet.{u} E β γ) := by
  set ν := fun γ : ℝ => sSup (frostmanStepSet.{u} E β γ) / 2 with hν_def
  refine ⟨ν, ?_, ?_, ?_⟩
  · -- MonotoneOn ν (Set.Ioc β 1)
    intro γ₁ hγ₁ γ₂ hγ₂ hγ₁₂
    have hsub : frostmanStepSet.{u} E β γ₁ ⊆ frostmanStepSet.{u} E β γ₂ :=
      frostmanStepSet_subset hγ₁₂
    have hnonempty₁ : (frostmanStepSet.{u} E β γ₁).Nonempty := hne γ₁ hγ₁
    have hbdd₂ : BddAbove (frostmanStepSet.{u} E β γ₂) := by
      refine ⟨1, fun c hc => hc.1.2⟩
    have hcsSup : sSup (frostmanStepSet.{u} E β γ₁) ≤ sSup (frostmanStepSet.{u} E β γ₂) :=
      csSup_le_csSup hbdd₂ hnonempty₁ hsub
    unfold ν
    nlinarith
  · -- ∀ γ ∈ Set.Ioc β 1, 0 < ν γ
    intro γ hγ
    rcases hne γ hγ with ⟨c, hc⟩
    have hbdd : BddAbove (frostmanStepSet.{u} E β γ) := by
      refine ⟨1, fun c' hc' => hc'.1.2⟩
    have hcpos : 0 < c := hc.1.1
    have hle : c ≤ sSup (frostmanStepSet.{u} E β γ) := le_csSup hbdd hc
    have hsup_pos : 0 < sSup (frostmanStepSet.{u} E β γ) := by linarith
    unfold ν
    nlinarith
  · -- ∀ γ ∈ Set.Ioc β 1, ν γ ∈ frostmanStepSet.{u} E β γ
    intro γ hγ
    have hnonempty : (frostmanStepSet.{u} E β γ).Nonempty := hne γ hγ
    have hbdd : BddAbove (frostmanStepSet.{u} E β γ) := by
      refine ⟨1, fun c' hc' => hc'.1.2⟩
    have hc : ∃ c, c ∈ frostmanStepSet.{u} E β γ := hnonempty
    rcases hc with ⟨c, hc⟩
    have hcpos : 0 < c := hc.1.1
    have hle_c_sup : c ≤ sSup (frostmanStepSet.{u} E β γ) := le_csSup hbdd hc
    have hsup_pos : 0 < sSup (frostmanStepSet.{u} E β γ) := by linarith
    have hsup_le_one : sSup (frostmanStepSet.{u} E β γ) ≤ 1 := by
      refine csSup_le hnonempty (fun c' hc' => hc'.1.2)
    set M := sSup (frostmanStepSet.{u} E β γ) with hM
    have hM_half_lt_M : M / 2 < M := by
      nlinarith
    -- By definition of supremum, there exists c' ∈ frostmanStepSet with M/2 < c'
    have h_exists : ∃ c' ∈ frostmanStepSet.{u} E β γ, M / 2 < c' := by
      by_contra! h
      -- h: ∀ c' ∈ frostmanStepSet, c' ≤ M/2, so M/2 is an upper bound
      have hUb : M / 2 ∈ upperBounds (frostmanStepSet.{u} E β γ) := by
        intro c' hc'
        exact h c' hc'
      have h_sup_le : sSup (frostmanStepSet.{u} E β γ) ≤ M / 2 :=
        csSup_le hnonempty hUb
      rw [hM] at h_sup_le
      nlinarith
    rcases h_exists with ⟨c', hc', hlt⟩
    have hpos : 0 < M / 2 := by nlinarith
    have hle : M / 2 ≤ c' := by linarith
    have hmem : M / 2 ∈ frostmanStepSet.{u} E β γ :=
      frostmanStepSet_downwardClosed hE hc' hpos hle
    simpa [hM, hν_def]

/-- **The monotone envelope.**  This is the form that GWZ Lemma 8.1
(`lemmain1boot`) consumes: from the uniform steps supplied by
`hne` it produces a single monotone, strictly positive step function `ν` such that
`K_KT(β)` and `K_F(γ)` imply `K_F(γ - ν γ)` for every `γ ∈ (β, 1]`.

It is the "in particular" clause of the blueprint's item (iii), obtained from
`Kakeya.exists_monotoneOn_mem_frostmanStepSet` by unfolding
`Kakeya.frostmanStepSet` at the admissible value `γ ∈ [γ, 1]`. -/
theorem exists_monotoneOn_frostmanStep (hE : Module.finrank ℝ E = 3)
    {β : ℝ}
    (hne : ∀ γ₀ ∈ Set.Ioc β 1, (frostmanStepSet.{u} E β γ₀).Nonempty) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc β 1) ∧ (∀ γ ∈ Set.Ioc β 1, 0 < ν γ) ∧
      ∀ γ ∈ Set.Ioc β 1, KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E γ →
        FrostmanEstimate.{u} E (γ - ν γ) := by
  rcases exists_monotoneOn_mem_frostmanStepSet hE hne with ⟨ν, hmono, hpos, hmem⟩
  refine ⟨ν, hmono, hpos, ?_⟩
  intro γ hγ hkt hkf
  have hmemγ : ν γ ∈ frostmanStepSet.{u} E β γ := hmem γ hγ
  rcases hmemγ with ⟨⟨hposc, hle1⟩, hcond⟩
  have hγicc : γ ∈ Set.Icc γ 1 := by
    refine ⟨le_rfl, ?_⟩
    exact hγ.2
  exact hcond γ hγicc hkt hkf

end Kakeya
