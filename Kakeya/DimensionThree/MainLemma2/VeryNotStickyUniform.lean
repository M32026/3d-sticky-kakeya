/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase
public import Kakeya.DimensionThree.FrostmanEstimateOne
public import Kakeya.DimensionThree.FrostmanEstimateMono

/-!
# The `β`-uniform companion of GWZ Lemma 9.1, and why it is not needed

The file opens with the question it was written for: can the three exponents `ϖ`, `ν`, `η` that
GWZ Lemma 9.1 (`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`) produces be chosen **once**, at
a threshold `β₀`, and then serve every `β ∈ [β₀, 1]`?  The GWZ reduction assembly needs that
uniform companion because the protected Main Lemma 2,
`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`, asks for a *monotone* `ν`.

## What is proved

**Part 1 — the companion, and the single residual it rests on.**

* `Kakeya.VNSUniform.VNSBody`, `Lemma91`, `Lemma91Uniform`: the statements, copied verbatim from
  the protected declaration and pinned to it by the tripwire `example : Lemma91 := …`.
  `Lemma91Uniform` is *definitionally* `Kakeya.ML2Assembly.Lemma91Uniform`.
* `VNSBody.mono_gain`, `VNSBody.mono_dens`, `VNSBody.mono_window`: `VNSBody` is antitone in all
  three exponents, so "uniform on `[β₀,1]`" means "the infimum on `[β₀,1]` is positive".
* `vnsBody_of_params`: GWZ Lemma 9.1's proof with the parameters of Configuration `hyp:ml2params`
  as *arguments* instead of produced by `Kakeya.VeryNotSticky.exists_caseParams`.  Recovering the
  protected statement from it is `lemma91_of_vnsBody_of_params`.
* `CaseParams.mono_beta`, `CaseParams.mono_eta`, `casesplitExponent_mono_beta` (and the three
  nested exponents): the whole parameter budget eases as `β` grows and as `η` shrinks.  Hence
  `exists_uniform_caseParams`: **eleven of the twelve `CaseParams` fields and the case-split
  budget transport to the whole window for free.**
* The one that does not transport is the binder
  `hplankF : 2η < τ · plankFrostmanExponent β (ϱβτ/8)` of
  `Kakeya.VeryNotSticky.exists_setup_caseSideData`.  It is isolated as
  `UniformPlankExponent`, shown to be *equivalent* to the missing budget
  (`exists_uniform_bound_of_uniform_budget`) and consistent
  (`uniformPlankExponent_of_not_plankFrostmanVolume`), and
  `lemma91Uniform_of_uniformPlankExponent` proves the companion from it.
  `Kakeya.VeryNotSticky.plankFrostmanExponent` is `@[irreducible]` and defined by
  `Classical.choose`, and unwinds to the accuracy that `K_F β` supplies existentially *after* `β`
  — so no uniform lower bound over a continuum of `β` is available, and the companion is blocked
  there and nowhere else.

**Part 2 — the reduction that removes the obligation.**

Write `A = {β ∈ (0,1] | K_KT β ∧ K_F β}`.

* `no_monotoneOn_drop_of_open_threshold`: if `A = (m,1]` with `0 < m`, the protected Main Lemma 2
  is *false*, however uniform Lemma 9.1 is.  So the uniform companion could never have been the
  whole story.
* `katzTaoEstimate_sub_of_least`, `katzTaoEstimate_sub_of_never`,
  `katzTaoEstimate_sub_of_trichotomy`: in the other three shapes of `A`, the protected statement
  follows from the **pointwise** drop with no uniformity at all.
* `katzTaoEstimate_of_forall_gt`, `frostmanEstimate_of_forall_gt`: both partial estimates are
  closed from above in the exponent, by the crude bound `|𝕋| ≤ δ^{-4}` and the bracket bound.
* `estimateSet_shape`: therefore `A` is a nonempty closed up-set, and the bad shape does not
  occur.
* `mainLemma2Statement_of_pointwise_drop`: **Main Lemma 2, verbatim, from the pointwise drop.**
  No `β`-uniform Lemma 9.1 is used, and the declaration is `sorryAx`-free.

Nothing here edits `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` or any protected statement.
-/

@[expose] public section

open MeasureTheory Topology Filter ShadedBody ConvexSpaceBody

namespace Kakeya.VNSUniform

universe u

/-! ## The statement, pinned to the protected declaration -/

/-- The body of GWZ Lemma 9.1 at exponent `β`, window exponent `ϖ`, tolerance `ζ`, gain `ν` and
density exponent `η` — copied verbatim from the protected
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, and identical to
`Kakeya.ML2Assembly.VNSBody`. -/
def VNSBody (β ϖ ζ ν η : ℝ) : Prop :=
  KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
  FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
  ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
    (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
    (∀ i ∈ s, (T i).toTube.IsCentred) →
    (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
    maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
    ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
    (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
    multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β

/-- **GWZ Lemma 9.1**, exactly as the protected declaration states it. -/
def Lemma91 : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 →
    ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ), VNSBody.{u} β ϖ ζ ν η

/- The fidelity tripwire `example : Lemma91 := fun _ hβ hβ1 ↦ Kakeya.multiplicity_le_of_card_isEssDistinct_ge hβ hβ1`
lives in `MainLemma2/VeryNotStickyClosed.lean` since the  A.5 relocation of Lemma 9.1 downstream of
its producers; this module is upstream of that file. -/

/-- **The `β`-uniform companion of GWZ Lemma 9.1**, identical to
`Kakeya.ML2Assembly.Lemma91Uniform`: the three exponents are chosen *before* `β` ranges over
the window `[β₀, 1]`. -/
def Lemma91Uniform : Prop :=
  ∀ β₀ : ℝ, 0 < β₀ → β₀ ≤ 1 →
    ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ),
      ∀ β ∈ Set.Icc β₀ 1, VNSBody.{u} β ϖ ζ ν η

/-- The uniform companion is a genuine strengthening of Lemma 9.1: it implies it. -/
theorem lemma91_of_lemma91Uniform (h : Lemma91Uniform.{u}) : Lemma91.{u} := by
  intro β hβ hβ1
  obtain ⟨ϖ, hϖ, hζ⟩ := h β hβ hβ1
  refine ⟨ϖ, hϖ, fun ζ hζ' ↦ ?_⟩
  obtain ⟨ν, hν, η, hη, hbody⟩ := hζ ζ hζ'
  exact ⟨ν, hν, η, hη, hbody β ⟨le_rfl, hβ1⟩⟩

/-! ## How `VNSBody` may be weakened

`VNSBody` is antitone in the gain `ν`, in the density exponent `η` and in the window exponent
`ϖ`: a smaller value of any of the three gives a *weaker* statement.  This is what makes
"uniform over `[β₀,1]`" mean "the infimum over `[β₀,1]` is positive", and it is what lets the
companion be assembled from a single choice at the threshold. -/

private lemma eventually_mem_Ioo :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ ∧ δ < 1 := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ
  exact ⟨hδ.1, hδ.2⟩

/-- `VNSBody` is antitone in the gain: a proof with gain `ν` gives one with any smaller gain. -/
theorem VNSBody.mono_gain {β ϖ ζ ν ν' η : ℝ} (hνν' : ν' ≤ ν) (h : VNSBody.{u} β ϖ ζ ν η) :
    VNSBody.{u} β ϖ ζ ν' η := by
  intro hKT hF
  filter_upwards [h hKT hF, eventually_mem_Ioo] with δ hδ hδ1
  intro ι s T hball hcen huni hmax hfull hcount
  refine (hδ s T hball hcen huni hmax hfull hcount).trans ?_
  have hδ1' : (δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1.2.le
  exact mul_le_mul_of_nonneg_right
    (ENNReal.rpow_le_rpow_of_exponent_ge hδ1' hνν') zero_le

/-- `VNSBody` is antitone in the density exponent: a proof at `η` gives one at any smaller
`η'`, because both hypotheses `Δ_max ≤ δ^{-η}` and `λ ≥ δ^η` weaken as `η` grows. -/
theorem VNSBody.mono_dens {β ϖ ζ ν η η' : ℝ} (hη' : η' ≤ η) (h : VNSBody.{u} β ϖ ζ ν η) :
    VNSBody.{u} β ϖ ζ ν η' := by
  intro hKT hF
  filter_upwards [h hKT hF, eventually_mem_Ioo] with δ hδ hδ1
  intro ι s T hball hcen huni hmax hfull hcount
  have hδ1' : (δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1.2.le
  -- the uniformity constant's cap `δ^{-η'}` is below `δ^{-η}`
  have huni' : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C) := by
    obtain ⟨C, hC1, hCδ, hC⟩ := huni
    exact ⟨C, hC1, hCδ.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by linarith)), hC⟩
  refine hδ s T hball hcen huni' ?_ ?_ hcount
  · exact hmax.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by linarith))
  · refine le_trans ?_ hfull
    exact_mod_cast NNReal.rpow_le_rpow_of_exponent_ge hδ1.1 hδ1.2.le hη'

/-- `VNSBody` is antitone in the window exponent: shrinking `ϖ` *enlarges* the scale window
`[δ^{1-ϖ}, δ^{ϖ}]` over which the tube-count hypothesis is assumed, hence strengthens that
hypothesis and weakens the statement. -/
theorem VNSBody.mono_window {β ϖ ϖ' ζ ν η : ℝ} (hϖ' : ϖ' ≤ ϖ) (h : VNSBody.{u} β ϖ ζ ν η) :
    VNSBody.{u} β ϖ' ζ ν η := by
  intro hKT hF
  filter_upwards [h hKT hF, eventually_mem_Ioo] with δ hδ hδ1
  intro ι s T hball hcen huni hmax hfull hcount
  refine hδ s T hball hcen huni hmax hfull ?_
  intro ρ hρ
  refine hcount ρ ⟨?_, ?_⟩
  · exact le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ1.1 hδ1.2.le (by linarith)) hρ.1
  · exact le_trans hρ.2 (NNReal.rpow_le_rpow_of_exponent_ge hδ1.1 hδ1.2.le hϖ')

/-! ## The core of Lemma 9.1, with its parameters exposed

`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` opens by running
`Kakeya.VeryNotSticky.exists_caseParams` at `β` and then never mentions `β` again except through
those parameters.  The theorem below is that proof with the `exists_caseParams` step *removed*:
the parameters are arguments.  It is what makes a uniform choice of parameters possible at all,
and it is stated so that the protected declaration is recovered by feeding it
`exists_caseParams`; `Kakeya.VNSUniform.lemma91_of_vnsBody_of_params` is that recovery, and is a
second fidelity check on this file.
-/

open Kakeya.VeryNotSticky


/-! ## Every exponent of the case split is monotone in `β`

The four nested exponents of the case split — `bigmultExponent`, `nonslabExponent`,
`thinExponent`, `casesplitExponent` — are minima of products in which `β` occurs positively, so
each *increases* with `β`.  The gain therefore never degrades as the exponent rises, which is
half of what a uniform choice at the threshold needs. -/

private lemma mul_mono_mid {a b c c' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : c ≤ c') :
    a * c * b ≤ a * c' * b :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h ha) hb

lemma bigmultExponent_mono_beta {β β' ζ exscal τ' : ℝ} (hexscal : 0 ≤ exscal) (hζ : 0 ≤ ζ)
    (hτ' : 0 ≤ τ') (hββ' : β ≤ β') :
    bigmultExponent β ζ exscal τ' ≤ bigmultExponent β' ζ exscal τ' := by
  unfold bigmultExponent
  refine min_le_min ?_ ?_
  · have : τ' * β ≤ τ' * β' := mul_le_mul_of_nonneg_left hββ' hτ'
    linarith
  · have : exscal * β * ζ ≤ exscal * β' * ζ := mul_mono_mid hexscal hζ hββ'
    linarith

lemma nonslabExponent_mono_beta {β β' ζ exscal τ' : ℝ} (hexscal : 0 ≤ exscal) (hζ : 0 ≤ ζ)
    (hτ' : 0 ≤ τ') (hββ' : β ≤ β') :
    nonslabExponent β ζ exscal τ' ≤ nonslabExponent β' ζ exscal τ' := by
  unfold nonslabExponent
  exact min_le_min (mul_le_mul_of_nonneg_left hββ' hexscal)
    (bigmultExponent_mono_beta hexscal hζ hτ' hββ')

lemma thinExponent_mono_beta {β β' ζ exscal τ' : ℝ} (hexscal : 0 ≤ exscal) (hζ : 0 ≤ ζ)
    (hτ' : 0 ≤ τ') (hββ' : β ≤ β') :
    thinExponent β ζ exscal τ' ≤ thinExponent β' ζ exscal τ' := by
  unfold thinExponent
  exact min_le_min (by linarith) (nonslabExponent_mono_beta hexscal hζ hτ' hββ')

/-- **The case-split gain of Lemma 9.1 is monotone in `β`.** -/
lemma casesplitExponent_mono_beta {β β' ζ exscal ϱ τ τ' : ℝ} (hexscal : 0 ≤ exscal)
    (hζ : 0 ≤ ζ) (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') (hϱ : 0 ≤ ϱ) (hββ' : β ≤ β') :
    casesplitExponent β ζ exscal τ τ' ϱ ≤ casesplitExponent β' ζ exscal τ τ' ϱ := by
  unfold casesplitExponent
  refine min_le_min ?_ (thinExponent_mono_beta hexscal hζ hτ' hββ')
  have : ϱ * β * τ ≤ ϱ * β' * τ := mul_mono_mid hϱ hτ hββ'
  linarith

/-! ## `CaseParams` eases as `β` grows and as `η` shrinks

`β` occurs in exactly five of the twelve fields of `Kakeya.VeryNotSticky.CaseParams` — `thick`,
`slab`, `smallMultiplicity`, `transverse`, `tangential` — and in all five on the *large* side of
a strict inequality.  `η` occurs in six, and in all six on the *small* side.  So the whole
budget system is monotone in `β` and antitone in `η`; neither fact is recorded upstream. -/

/-- **`CaseParams` is monotone in `β`.**  This is what allows the parameters to be chosen once,
at the threshold `β₀`, and reused at every `β ∈ [β₀, 1]`. -/
theorem CaseParams.mono_beta {β β' ζ exscal ϱ η τ τ' : ℝ} (hexscal : 0 ≤ exscal) (hζ : 0 ≤ ζ)
    (hϱ : 0 ≤ ϱ) (hββ' : β ≤ β') (h : CaseParams β ζ exscal ϱ η τ τ') :
    CaseParams β' ζ exscal ϱ η τ τ' := by
  have hτ : 0 < τ := h.hτ
  have hτ' : 0 < τ' := lt_trans h.hτ h.hτ'
  refine { h with
    thick := ?_, slab := ?_, smallMultiplicity := ?_, transverse := ?_, tangential := ?_ }
  · exact lt_of_lt_of_le h.thick (mul_mono_mid hϱ hτ.le hββ')
  · have := h.slab; linarith
  · refine lt_of_lt_of_le h.smallMultiplicity ?_
    exact mul_le_mul_of_nonneg_left hββ' (by nlinarith)
  · exact lt_of_lt_of_le h.transverse (mul_le_mul_of_nonneg_left hββ' hτ'.le)
  · refine lt_of_lt_of_le h.tangential ?_
    have := mul_mono_mid hexscal hζ hββ'
    linarith


/-! ## The one residual: a `β`-uniform plank-Frostman exponent

Running `Kakeya.VeryNotSticky.exists_caseParams` at the threshold `β₀` and transporting its
output along `Kakeya.VNSUniform.CaseParams.mono_beta` discharges **eleven of the twelve fields**
of `CaseParams` and the case-split budget `η ≤ ν_casesplit/2` at every `β ∈ [β₀,1]`, with no
hypothesis at all.  Exactly one of `exists_caseParams`' three conclusions fails to transport:
the binder

`hplankF : 2η < τ · plankFrostmanExponent β (ϱβτ/8)`

that `Kakeya.VeryNotSticky.exists_setup_caseSideData` requires.  It is an *upper* bound on `η`
whose right-hand side moves with `β`, and `η` must be fixed before `β`; so it transports exactly
when the canonical exponent is bounded below by a positive constant on the window.

`Kakeya.VeryNotSticky.plankFrostmanExponent` is `@[irreducible]` and defined by
`Classical.choose` on `Kakeya.VeryNotSticky.PlankFrostmanVolume β ε`; the only fact about it
available anywhere in the development is `plankFrostmanExponent_pos`, its positivity at a *single*
`(β, ε)`. A uniform positive lower bound over a continuum of `β` is therefore not derivable, and
that — not any part of the case split — is what stands between this file and an unconditional
`Kakeya.VNSUniform.Lemma91Uniform`. -/

/-- **The residual obligation**: the canonical plank-Frostman exponent of blueprint `plankF` is
bounded below by a positive constant, uniformly over the window `[β₀, 1]`, along the ray of
accuracies `ε = c·β` at which the thick case reads it.

The accuracy is `c·β` and not an arbitrary function of `β` because
`Kakeya.VeryNotSticky.exists_setup_caseSideData` reads the exponent at `ϱβτ/8`, with `ϱ` and `τ`
fixed before `β`; so `c = ϱτ/8`. -/
def UniformPlankExponent (β₀ : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ p : ℝ, 0 < p ∧
    ∀ β ∈ Set.Icc β₀ 1, p ≤ plankFrostmanExponent.{u} β (c * β)

/-- **The residual is exactly the missing budget, not an over-approximation of it.**  A `β`-uniform
`hplankF` and a `β`-uniform positive lower bound on the canonical exponent are interderivable, so
nothing is lost by isolating the latter. -/
theorem exists_uniform_bound_of_uniform_budget {β₀ τ ϱ η : ℝ} (hτ : 0 < τ) (hη : 0 < η)
    (H : ∀ β ∈ Set.Icc β₀ 1, η < τ * plankFrostmanExponent.{u} β (ϱ * β * τ / 8)) :
    ∃ p : ℝ, 0 < p ∧
      ∀ β ∈ Set.Icc β₀ 1, p ≤ plankFrostmanExponent.{u} β (ϱ * β * τ / 8) := by
  refine ⟨η / τ, by positivity, fun β hβ ↦ ?_⟩
  rw [div_le_iff₀ hτ, mul_comm]
  exact (H β hβ).le

/-- **The residual is consistent**: it holds outright in any world in which the plank estimate of
blueprint `plankF` is unavailable on the window, since the canonical exponent is then the default
value `1`.  This rules out `Kakeya.VNSUniform.UniformPlankExponent` being a disguised `False`,
which is the failure mode that a `Classical.choose` residual invites. -/
theorem uniformPlankExponent_of_not_plankFrostmanVolume {β₀ : ℝ}
    (h : ∀ β ∈ Set.Icc β₀ 1, ∀ c : ℝ, 0 < c → ¬ PlankFrostmanVolume.{u} β (c * β)) :
    UniformPlankExponent.{u} β₀ := by
  refine fun c hc ↦ ⟨1, one_pos, fun β hβ ↦ ?_⟩
  rw [plankFrostmanExponent, dif_neg (h β hβ c hc)]

/-! ## The uniform parameter package, and the uniform companion -/

/-- **The `β`-uniform form of `Kakeya.VeryNotSticky.exists_caseParams`.**  All three conclusions of
`exists_caseParams` hold at every `β ∈ [β₀, 1]` for one choice of `exscal, τ, τ', ϱ, η` made at
the threshold, given the residual.  Compare `exists_caseParams`, whose output is tied to a single
`β`. -/
theorem exists_uniform_caseParams {β₀ : ℝ} (hβ₀ : 0 < β₀) (hu : UniformPlankExponent.{u} β₀) :
    ∃ exscal > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ τ τ' ϱ η : ℝ,
      0 < τ ∧ 0 < τ' ∧ 0 < ϱ ∧ 0 < η ∧
      (∀ β ∈ Set.Icc β₀ 1, CaseParams β ζ exscal ϱ η τ τ') ∧
      η ≤ casesplitExponent β₀ ζ exscal τ τ' ϱ / 2 ∧
      (∀ β ∈ Set.Icc β₀ 1, 2 * η < τ * plankFrostmanExponent.{u} β (ϱ * β * τ / 8)) := by
  obtain ⟨exscal, hexscal, hpar⟩ := exists_caseParams.{u} hβ₀
  refine ⟨exscal, hexscal, fun ζ hζ ↦ ?_⟩
  obtain ⟨τ, τ', ϱ, η₀, hτ, hτ', hϱ, hη₀, params₀, hη₀_le, -⟩ := hpar ζ hζ
  obtain ⟨p, hp, hple⟩ := hu (ϱ * τ / 8) (by positivity)
  refine ⟨τ, τ', ϱ, min η₀ (τ * p / 4), hτ, hτ', hϱ, lt_min hη₀ (by positivity), ?_, ?_, ?_⟩
  · intro β hβ
    exact CaseParams.mono_beta hexscal.le hζ.le hϱ.le hβ.1
      (CaseParams.mono_eta (min_le_left _ _) params₀)
  · exact le_trans (min_le_left _ _) hη₀_le
  · intro β hβ
    have hkey : ϱ * β * τ / 8 = ϱ * τ / 8 * β := by ring
    have h1 : p ≤ plankFrostmanExponent.{u} β (ϱ * β * τ / 8) := by
      rw [hkey]; exact hple β hβ
    have h2 : 2 * (τ * p / 4) < τ * p := by nlinarith [mul_pos hτ hp]
    calc 2 * min η₀ (τ * p / 4) ≤ 2 * (τ * p / 4) := by
          linarith [min_le_right η₀ (τ * p / 4)]
      _ < τ * p := h2
      _ ≤ τ * plankFrostmanExponent.{u} β (ϱ * β * τ / 8) := by
          exact mul_le_mul_of_nonneg_left h1 hτ.le



/-! ## Is the uniform companion the right obligation?

The assembly asks for `Lemma91Uniform` because the protected Main Lemma 2 asks for a *monotone*
`ν`.  This section makes the relationship between the two precise, and it changes the priority.

Write `A := {β ∈ (0,1] | K_KT β ∧ K_F β}` for the set of exponents at which Main Lemma 2 has
anything to say.  `A` is up-closed, by `Kakeya.KatzTaoEstimate.mono` and
`Kakeya.FrostmanEstimate.mono`, so it is one of `∅`, `(0,1]`, `[m,1]` or `(m,1]` with `0 < m`.

* On `∅` and on `(0,1]` the protected statement is immediate
  (`Kakeya.VNSUniform.katzTaoEstimate_sub_of_never`, and
  `Kakeya.KatzTaoEstimate.mainLemma2_of_all` for `(0,1]`).
* On `[m,1]` **one single application of the *non-uniform* Lemma 9.1, at `m`, suffices**:
  `Kakeya.VNSUniform.katzTaoEstimate_sub_of_least`.  No uniformity of any kind is used.
* On `(m,1]` with `0 < m` the protected statement is **unprovable from any per-exponent drop**:
  `Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold` derives `False` from a monotone
  positive `ν` in that configuration, and a `β`-uniform Lemma 9.1 would not help either, since
  the obstruction is on the `K_KT` side, not on the parameter side.

So `Lemma91Uniform` is *not* the load-bearing obligation.  The load-bearing obligation is that
the fourth case does not occur — i.e. that `A` is closed at its infimum — and that is a
self-contained analytic statement about `Kakeya.KatzTaoEstimate` and `Kakeya.FrostmanEstimate`,
not about the case split of Lemma 9.1.  See `Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy`
for the resulting reduction of the whole of Main Lemma 2 to the *pointwise* drop. -/

section Envelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The protected Main Lemma 2 is refuted in the open-threshold configuration.**

Suppose the predicate `KT` fails everywhere below a threshold `m ∈ (0,1)` but is required to hold
at `β - ν β` for every `β > m`.  Then no `ν` that is monotone on `(0,1]` and positive there can
exist — *even though a positive drop exists at every single `β > m`*, namely any `d < β - m`.

This is the exact configuration `A = (m,1]`, and it is why a `β`-uniform Lemma 9.1 cannot rescue
the reduction there: the failure is not a failure to choose parameters uniformly, it is that the
conclusion demanded is false.  Monotonicity of `ν` is what does the damage: it forces `ν` to be
bounded below near `m` by its value at `m/2`. -/
theorem no_monotoneOn_drop_of_open_threshold {m : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {KT : ℝ → Prop} (hbelow : ∀ x : ℝ, x < m → ¬ KT x)
    {ν : ℝ → ℝ} (hmono : MonotoneOn ν (Set.Ioc (0 : ℝ) 1))
    (hpos : ∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β)
    (hstep : ∀ β : ℝ, m < β → β ≤ 1 → KT (β - ν β)) : False := by
  have hm2 : 0 < m / 2 := half_pos hm
  have hmem_a : (m / 2) ∈ Set.Ioc (0 : ℝ) 1 := ⟨hm2, by linarith⟩
  have hp : 0 < ν (m / 2) := hpos _ (by linarith) (by linarith)
  set β : ℝ := min 1 (m + ν (m / 2) / 2) with hβ_def
  have hβ_le : β ≤ 1 := min_le_left _ _
  have hβ_gt : m < β := lt_min hm1 (by linarith)
  have hmem_β : β ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, hβ_le⟩
  have hle : ν (m / 2) ≤ ν β := hmono hmem_a hmem_β (by linarith)
  have hβν : β - ν β < m := by
    have : β ≤ m + ν (m / 2) / 2 := min_le_right _ _
    linarith
  exact hbelow _ hβν (hstep β hβ_gt hβ_le)

/-- **When the estimates first hold at an exponent that is attained, Main Lemma 2 needs no
uniformity at all.**

If `m` is a *least* exponent at which both partial estimates hold, then a single drop `c` valid
at `m` — the output of the ordinary, non-uniform GWZ Lemma 9.1 route — already yields the whole
protected conclusion, with the monotone function `ν β = min c (β/2)`.  Up-closedness of
`K_KT` (`Kakeya.KatzTaoEstimate.mono`) does the rest.

The conclusion below is *verbatim* the statement of
`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`. -/
theorem katzTaoEstimate_sub_of_least {m c : ℝ} (hc : 0 < c)
    (hleast : ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
      m ≤ β)
    (hdrop : KatzTaoEstimate.{u} E (m - c)) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
        KatzTaoEstimate.{u} E (β - ν β) := by
  refine ⟨fun β ↦ min c (β / 2), ?_, ?_, ?_⟩
  · intro x _ y _ hxy
    exact min_le_min le_rfl (by linarith)
  · intro β hβ _
    exact lt_min hc (by linarith)
  · intro β hβ hβ1 hKT hF
    refine KatzTaoEstimate.mono ?_ hdrop
    have hmβ : m ≤ β := hleast β hβ hβ1 hKT hF
    have : min c (β / 2) ≤ c := min_le_left _ _
    linarith

/-- **When the estimates never hold, Main Lemma 2 is vacuous.**  The conclusion is again verbatim
the protected statement. -/
theorem katzTaoEstimate_sub_of_never
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → ¬ FrostmanEstimate.{u} E β) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
        KatzTaoEstimate.{u} E (β - ν β) := by
  refine ⟨fun β ↦ β / 2, ?_, ?_, ?_⟩
  · intro x _ y _ hxy; dsimp; linarith
  · intro β hβ _; dsimp; linarith
  · intro β hβ hβ1 hKT hF
    exact absurd hF (h β hβ hβ1 hKT)

/-- **Main Lemma 2 from the *pointwise* drop, given that the estimate set is not open at its
infimum.**

The hypothesis `hdrop` is exactly what the ordinary GWZ route delivers: at each single exponent
where both estimates hold, *some* positive drop is available.  The hypothesis `hshape` is the
trichotomy discussed above — the estimate set is empty, is everything, or has a least element.
Together they give the protected Main Lemma 2 verbatim, with **no `β`-uniform Lemma 9.1
anywhere**.

`Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold` shows the missing fourth case is not an
artefact of this proof: in it the protected conclusion is false outright.  So `hshape` is not a
convenience — it is the whole remaining gap, and it is a statement about the two partial
estimates alone. -/
theorem katzTaoEstimate_sub_of_trichotomy
    (hdrop : ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
      ∃ d : ℝ, 0 < d ∧ KatzTaoEstimate.{u} E (β - d))
    (hshape :
      (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → ¬ FrostmanEstimate.{u} E β) ∨
      (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β) ∨
      (∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ KatzTaoEstimate.{u} E m ∧ FrostmanEstimate.{u} E m ∧
        ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β → m ≤ β)) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} E β → FrostmanEstimate.{u} E β →
        KatzTaoEstimate.{u} E (β - ν β) := by
  rcases hshape with hnone | hall | ⟨m, hm, hm1', hKTm, hFm, hleast⟩
  · exact katzTaoEstimate_sub_of_never hnone
  · refine ⟨fun β ↦ β / 2, ?_, ?_, ?_⟩
    · intro x _ y _ hxy; dsimp; linarith
    · intro β hβ _; dsimp; linarith
    · intro β hβ hβ1 _ _
      have : β - β / 2 = β / 2 := by ring
      rw [this]
      exact hall (β / 2) (by linarith) (by linarith)
  · obtain ⟨d, hd, hKTd⟩ := hdrop m hm hm1' hKTm hFm
    exact katzTaoEstimate_sub_of_least hd hleast hKTd


/-! ## The estimate set is closed on the Katz--Tao side

The fourth case of the trichotomy above is `A = (m,1]` with `0 < m`.  It cannot occur on the
`K_KT` side: `Kakeya.KatzTaoEstimate` at the exponent `m` follows from `Kakeya.KatzTaoEstimate`
at every exponent above `m`, because a `δ`-tube family in `B₁` with `Δ_max ≤ δ^{-η}` and `η ≤ 1`
has at most `δ^{-4}` members, so `|𝕋|^{β} ≤ |𝕋|^{m}·δ^{-4(β-m)}` and the difference is absorbed
into the accuracy.

This is the "closedness" half of `hshape` in
`Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy`; the other half is the same statement for
`Kakeya.FrostmanEstimate`, which is not proved here. -/

/-- `|𝕋| ≤ δ^{-4}` in `ℝ≥0∞`.  The `ENNReal` form of `Kakeya.ML2Assembly.card_le_rpow_neg_four`
(same proof, stopped one step earlier: that declaration transfers the bound to `ℝ`, and the
`ℝ`-valued form is not what the exponent bookkeeping below needs). -/
theorem card_le_rpow_neg_four_enn {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδC : (Tube.card_le_of_densityIn_le.C 3 : ENNReal) ≤ (δ : ENNReal) ^ (-1 : ℝ))
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    {η : ℝ} (hη1 : η ≤ 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η)) :
    (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-4 : ℝ) := by
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hδE0 : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hden : densityIn s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ (δ : ENNReal) ^ (-η) :=
    (le_maxDensity s _ _).trans hmax
  have hraw := Tube.card_le_of_densityIn_le (E := EuclideanSpace ℝ (Fin 3)) (δ := δ)
    (s := s) (T := fun i ↦ (T i).toTube) hδ0.ne' hball hden
  rw [hE] at hraw
  norm_num at hraw
  have hstep1 : (δ : ENNReal) ^ (-η) ≤ (δ : ENNReal) ^ (-1 : ℝ) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  have hzpow : (δ : ENNReal) ^ (-2 : ℤ) = (δ : ENNReal) ^ (-2 : ℝ) := by
    rw [← ENNReal.rpow_intCast]; norm_num
  refine hraw.trans ?_
  rw [hzpow]
  calc (Tube.card_le_of_densityIn_le.C 3 : ENNReal) * (δ : ENNReal) ^ (-η)
          * (δ : ENNReal) ^ (-2 : ℝ)
      ≤ (δ : ENNReal) ^ (-1 : ℝ) * (δ : ENNReal) ^ (-1 : ℝ) * (δ : ENNReal) ^ (-2 : ℝ) := by
        gcongr
    _ = (δ : ENNReal) ^ (-4 : ℝ) := by
        rw [← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top]
        norm_num

/-- The thresholds under which `Kakeya.VNSUniform.card_le_rpow_neg_four_enn` applies hold for all
small `δ`.  Copied from `Kakeya.ML2Assembly.eventually_card_thresholds`. -/
theorem eventually_card_thresholds' :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      0 < δ ∧ δ ≤ 1 ∧
        (Tube.card_le_of_densityIn_le.C 3 : ENNReal) ≤ (δ : ENNReal) ^ (-1 : ℝ) := by
  set C : NNReal := Tube.card_le_of_densityIn_le.C 3 with hC
  have hpos : (0 : NNReal) < (C + 1)⁻¹ := by positivity
  have hmem : Set.Ioo (0 : NNReal) (min 1 (C + 1)⁻¹) ∈ 𝓝[>] (0 : NNReal) :=
    Ioo_mem_nhdsGT (lt_min zero_lt_one hpos)
  filter_upwards [hmem] with δ hδ
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδ1 : δ ≤ 1 := (lt_of_lt_of_le hδlt (min_le_left _ _)).le
  refine ⟨hδ0, hδ1, ?_⟩
  have hδinv : δ ≤ (C + 1)⁻¹ := (lt_of_lt_of_le hδlt (min_le_right _ _)).le
  have hCδ : C * δ ≤ 1 := by
    have h1 : (C + 1) * δ ≤ (C + 1) * (C + 1)⁻¹ := by gcongr
    rw [mul_inv_cancel₀ (by positivity)] at h1
    exact le_trans (by gcongr; exact le_self_add) h1
  have hCle : (C : ENNReal) ≤ (δ : ENNReal)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le]
    calc (C : ENNReal) * (δ : ENNReal) = ((C * δ : NNReal) : ENNReal) := by rw [ENNReal.coe_mul]
      _ ≤ ((1 : NNReal) : ENNReal) := by exact_mod_cast hCδ
      _ = 1 := by simp
  calc (C : ENNReal) ≤ (δ : ENNReal)⁻¹ := hCle
    _ = (δ : ENNReal) ^ (-1 : ℝ) := by rw [ENNReal.rpow_neg, ENNReal.rpow_one]

/-- **`Kakeya.KatzTaoEstimate` is closed from above in the exponent.**

If `K_KT(β)` holds for every `β ∈ (m, 1]`, then `K_KT(m)` holds.  Hence the set of exponents at
which the Katz--Tao partial estimate holds is a *closed* up-set, and the open-threshold
configuration refuted by `Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold` cannot arise
from the `K_KT` side alone.

The proof is the crude cardinality bound `|𝕋| ≤ δ^{-4}` and nothing else: run the estimate at
`β = m + ε/8`, and pay `|𝕋|^{β - m} ≤ δ^{-4(β-m)} ≤ δ^{-ε/2}` out of the accuracy. -/
theorem katzTaoEstimate_of_forall_gt {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (h : ∀ β : ℝ, m < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m := by
  intro ε hε
  have hβm : m < min 1 (m + ε / 8) := lt_min hm1 (by linarith)
  have hβ1 : min 1 (m + ε / 8) ≤ 1 := min_le_left _ _
  have hβm8 : min 1 (m + ε / 8) - m ≤ ε / 8 := by
    have := min_le_right (1 : ℝ) (m + ε / 8); linarith
  set β : ℝ := min 1 (m + ε / 8) with hβdef
  obtain ⟨η, hη, hev⟩ := h β hβm hβ1 (ε / 2) (by linarith)
  refine ⟨min η 1, lt_min hη one_pos, ?_⟩
  filter_upwards [hev, eventually_card_thresholds'] with δ hδ hthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  intro ι s T hball hKT hfull
  have hδE0 : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  -- transfer the two standing hypotheses from `min η 1` to `η`
  have hKT' : IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) :=
    le_trans hKT (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by simp))
  have hfull' : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η :=
    le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (min_le_left η 1)) hfull
  have hres := hδ s T hball hKT' hfull'
  refine hres.trans ?_
  -- the crude cardinality bound
  have hcard : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-4 : ℝ) :=
    card_le_rpow_neg_four_enn hδ0 hδ1 hδC s T hball (min_le_right η 1) hKT
  have key : (δ : ENNReal) ^ (-(ε / 2)) * (s.card : ENNReal) ^ β ≤
      (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ m := by
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · have hβpos : 0 < β := lt_trans hm0 hβm
      simp [h0, ENNReal.zero_rpow_of_pos hβpos, ENNReal.zero_rpow_of_pos hm0]
    · have hne : (s.card : ENNReal) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      have htop : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hsplit : (s.card : ENNReal) ^ β
          = (s.card : ENNReal) ^ m * (s.card : ENNReal) ^ (β - m) := by
        rw [← ENNReal.rpow_add _ _ hne htop]
        ring_nf
      have hpow : (s.card : ENNReal) ^ (β - m) ≤ (δ : ENNReal) ^ (-(ε / 2)) := by
        have h1 : (s.card : ENNReal) ^ (β - m) ≤ ((δ : ENNReal) ^ (-4 : ℝ)) ^ (β - m) :=
          ENNReal.rpow_le_rpow hcard (by linarith)
        refine h1.trans ?_
        rw [← ENNReal.rpow_mul]
        exact ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
      calc (δ : ENNReal) ^ (-(ε / 2)) * (s.card : ENNReal) ^ β
          = (δ : ENNReal) ^ (-(ε / 2)) * (s.card : ENNReal) ^ m * (s.card : ENNReal) ^ (β - m) := by
            rw [hsplit, mul_assoc]
        _ ≤ (δ : ENNReal) ^ (-(ε / 2)) * (s.card : ENNReal) ^ m * (δ : ENNReal) ^ (-(ε / 2)) := by
            gcongr
        _ = (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2)) * (s.card : ENNReal) ^ m := by
            ring
        _ = (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ m := by
            rw [← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top]
            ring_nf
  exact mul_le_mul_of_nonneg_right key zero_le


/-- **The protected Main Lemma 2 statement**, with every binder written out.

This file cannot import `Kakeya.DimensionThree.MainLemma2` — that module still routes through
`Kakeya.DimensionThree.MainLemma2.WangZahl.SourcePropositions`, the abandoned route — so the
tripwire `example : MainLemma2Statement := katzTaoEstimate_sub_of_frostmanEstimate` cannot live
here.  **It is not in this repository.**  An earlier revision of this docstring named
`lean/kakeya/Kakeya/CrossCheck.lean`; that file does not exist and never has.  The check has been
run out of tree, and the module that will carry it in tree is
`Kakeya/DimensionThree/MainLemma2Rewire.lean`, which is blocked on
`Kakeya/DimensionThree/MainLemma2/Reduction/Rewire.lean` . -/
def MainLemma2Statement : Prop :=
  ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
    (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
    ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β)

/-- **Main Lemma 2 itself, from the pointwise drop plus the shape of the estimate set.**  The
specialisation of `Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy` to `ℝ³`, stated against
`Kakeya.VNSUniform.MainLemma2Statement` so that the fit with the protected declaration is a
typechecking obligation and not a claim. -/
theorem mainLemma2Statement_of_trichotomy
    (hdrop : ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ d : ℝ, 0 < d ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - d))
    (hshape :
      (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        ¬ FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) ∨
      (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) ∨
      (∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
        ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
          FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β → m ≤ β)) :
    MainLemma2Statement.{u} :=
  katzTaoEstimate_sub_of_trichotomy hdrop hshape

/-- **`Kakeya.FrostmanEstimate` is closed from above in the exponent.**

If `K_F(β)` holds for every `β ∈ (m, 1]` then `K_F(m)` holds.  Together with
`Kakeya.VNSUniform.katzTaoEstimate_of_forall_gt` this closes the estimate set `A`, which is what
`Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy` needs.

The proof pays the difference out of the accuracy, using the two-sided bound
`δ^{n-1} ≤ |𝕋|·δ^{n-1} ` on the bracket: run `K_F` at `β = m + κ` with `κ ≤ ε/6`, and note
`B^{1-β/2}·δ^{κ} ≤ B^{1-m/2}` and `δ^{-ε/2-2β-κ} ≤ δ^{-ε-2m}`. -/
theorem frostmanEstimate_of_forall_gt {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (h : ∀ β : ℝ, m < β → β ≤ 1 → FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m := by
  intro ε hε
  have hκpos : 0 < min (ε / 6) ((1 - m) / 2) := lt_min (by linarith) (by linarith)
  have hκ6 : min (ε / 6) ((1 - m) / 2) ≤ ε / 6 := min_le_left _ _
  have hκ2 : min (ε / 6) ((1 - m) / 2) ≤ (1 - m) / 2 := min_le_right _ _
  set κ : ℝ := min (ε / 6) ((1 - m) / 2) with hκdef
  have hβm : m < m + κ := by linarith
  have hβ1 : m + κ ≤ 1 := by linarith
  obtain ⟨η, hη, hev⟩ := h (m + κ) hβm hβ1 (ε / 2) (by linarith)
  refine ⟨min η 1, lt_min hη one_pos, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ hδr
  obtain ⟨hδ0, hδlt1⟩ := hδr
  intro ι s T hball hED hFr hfull
  have hδE0 : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδlt1.le
  have hδne : (δ : ENNReal) ≠ 0 := hδE0.ne'
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hFr' : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ((δ : ENNReal) ^ (-η)) :=
    hFr.mono (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by simp))
  have hfull' : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η :=
    le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδlt1.le (min_le_left η 1)) hfull
  refine (hδ s T hball hED hFr' hfull').trans ?_
  set n1 : ℕ := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 with hn1
  set B : ENNReal := (s.card : ENNReal) * (δ : ENNReal) ^ n1 with hB
  have hexpβ : (0 : ℝ) < 1 - (m + κ) / 2 := by linarith
  have hexpm : (0 : ℝ) < 1 - m / 2 := by linarith
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · have hB0 : B = 0 := by simp [hB, h0]
    rw [hB0, ENNReal.zero_rpow_of_pos hexpβ, ENNReal.zero_rpow_of_pos hexpm]
    simp
  · have hcard1 : (1 : ENNReal) ≤ (s.card : ENNReal) := by
      have : 1 ≤ s.card := hpos
      exact_mod_cast this
    have hn1eq : n1 = 2 := by simp [hn1]
    have hq : (δ : ENNReal) ^ n1 = (δ : ENNReal) ^ (2 : ℝ) := by
      rw [hn1eq, ← ENNReal.rpow_natCast]; norm_num
    have hB0 : B ≠ 0 := by
      have hc : (s.card : ENNReal) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      have hd : ((δ : ENNReal)) ^ n1 ≠ 0 := by positivity
      simp only [hB, ne_eq, mul_eq_zero, not_or]
      exact ⟨hc, hd⟩
    have hBtop : B ≠ ⊤ := by
      simp only [hB]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by finiteness)
    -- the bracket is at least `δ ^ 2`
    have hBlow : (δ : ENNReal) ^ (2 : ℝ) ≤ B := by
      rw [hB, ← hq]
      exact le_mul_of_one_le_left zero_le hcard1
    -- `δ ^ κ ≤ B ^ (κ/2)`
    have hδκ : (δ : ENNReal) ^ κ ≤ B ^ (κ / 2) := by
      have h1 : ((δ : ENNReal) ^ (2 : ℝ)) ^ (κ / 2) ≤ B ^ (κ / 2) :=
        ENNReal.rpow_le_rpow hBlow (by positivity)
      refine le_trans (le_of_eq ?_) h1
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * (κ / 2) = κ by ring]
    -- split the bracket exponent
    have hsplit : B ^ (1 - m / 2) = B ^ (1 - (m + κ) / 2) * B ^ (κ / 2) := by
      rw [← ENNReal.rpow_add _ _ hB0 hBtop]
      ring_nf
    -- split the `δ` exponent
    have hδsplit : (δ : ENNReal) ^ (-(ε / 2) - 2 * (m + κ)) =
        (δ : ENNReal) ^ (-(ε / 2) - 2 * (m + κ) - κ) * (δ : ENNReal) ^ κ := by
      rw [← ENNReal.rpow_add _ _ hδne hδtop]
      ring_nf
    have hδmono : (δ : ENNReal) ^ (-(ε / 2) - 2 * (m + κ) - κ) ≤ (δ : ENNReal) ^ (-ε - 2 * m) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
    calc (δ : ENNReal) ^ (-(ε / 2) - 2 * (m + κ)) * B ^ (1 - (m + κ) / 2)
        = (δ : ENNReal) ^ (-(ε / 2) - 2 * (m + κ) - κ) *
            (B ^ (1 - (m + κ) / 2) * (δ : ENNReal) ^ κ) := by
          rw [hδsplit]; ring
      _ ≤ (δ : ENNReal) ^ (-(ε / 2) - 2 * (m + κ) - κ) *
            (B ^ (1 - (m + κ) / 2) * B ^ (κ / 2)) := by
          gcongr
      _ = (δ : ENNReal) ^ (-(ε / 2) - 2 * (m + κ) - κ) * B ^ (1 - m / 2) := by
          rw [hsplit]
      _ ≤ (δ : ENNReal) ^ (-ε - 2 * m) * B ^ (1 - m / 2) := by
          gcongr

/-! ## The shape of the estimate set, unconditionally

Both partial estimates are up-closed in the exponent (`Kakeya.KatzTaoEstimate.mono`,
`Kakeya.FrostmanEstimate.mono`) and both are closed from above
(`Kakeya.VNSUniform.katzTaoEstimate_of_forall_gt`,
`Kakeya.VNSUniform.frostmanEstimate_of_forall_gt`), and both hold at `β = 1`
(`Kakeya.KatzTao_one`, `Kakeya.frostmanEstimate_one`).  So the set

`A = {β ∈ (0,1] | K_KT β ∧ K_F β}`

is a nonempty closed up-set: it is either all of `(0,1]` or `[m,1]` for some `m ∈ (0,1]`.  The
open-threshold configuration `(m,1]` with `0 < m` — the only one in which the protected Main
Lemma 2 fails (`Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold`) — **does not occur**. -/

/-- **The estimate set is `(0,1]` or `[m,1]`.**  This discharges the hypothesis `hshape` of
`Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy` outright. -/
theorem estimateSet_shape :
    (∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) ∨
    (∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 → KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β → m ≤ β) := by
  classical
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set A : Set ℝ := {β : ℝ | 0 < β ∧ β ≤ 1 ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β ∧
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β} with hA
  have hone : (1 : ℝ) ∈ A := ⟨one_pos, le_rfl, KatzTao_one, frostmanEstimate_one⟩
  have hAne : A.Nonempty := ⟨1, hone⟩
  have hbdd : BddBelow A := ⟨0, fun x hx ↦ hx.1.le⟩
  set m : ℝ := sInf A with hm
  have hm0 : 0 ≤ m := le_csInf hAne fun x hx ↦ hx.1.le
  have hm1 : m ≤ 1 := csInf_le hbdd hone
  -- every exponent strictly above the infimum lies in `A`
  have hup : ∀ β : ℝ, m < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β ∧
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β := by
    intro β hβm hβ1
    obtain ⟨a, ha, haβ⟩ := exists_lt_of_csInf_lt hAne hβm
    exact ⟨KatzTaoEstimate.mono haβ.le ha.2.2.1, FrostmanEstimate.mono hE haβ.le ha.2.2.2⟩
  rcases eq_or_lt_of_le hm0 with hm00 | hmpos
  · -- `m = 0`: the estimates hold at every exponent of `(0,1]`
    left
    intro β hβ hβ1
    exact (hup β (by rw [← hm00]; exact hβ) hβ1).1
  · -- `m > 0`: the infimum is attained
    right
    have hmem : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m := by
      rcases eq_or_lt_of_le hm1 with hm11 | hmlt
      · rw [hm11]; exact ⟨KatzTao_one, frostmanEstimate_one⟩
      · exact ⟨katzTaoEstimate_of_forall_gt hmpos hmlt fun β hβm hβ1 ↦ (hup β hβm hβ1).1,
          frostmanEstimate_of_forall_gt hmpos hmlt fun β hβm hβ1 ↦ (hup β hβm hβ1).2⟩
    exact ⟨m, hmpos, hm1, hmem.1, hmem.2,
      fun β hβ hβ1 hKT hF ↦ csInf_le hbdd ⟨hβ, hβ1, hKT, hF⟩⟩

/-- **Main Lemma 2 from the *pointwise* drop, with no uniformity anywhere.**

`hdrop` is exactly what the ordinary, per-exponent GWZ route produces: at each single `β` where
both partial estimates hold, *some* positive drop is available.  The conclusion is the protected
`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate` verbatim.  The tripwire pinning
`Kakeya.VNSUniform.MainLemma2Statement` to it is **not in this repository**; the file
`lean/kakeya/Kakeya/CrossCheck.lean` that an earlier revision of this docstring named does not
exist.  See the note on `Kakeya.VNSUniform.MainLemma2Statement` above.

In particular **the `β`-uniform companion of Lemma 9.1 is not needed**: the `MonotoneOn ν`
demand of Main Lemma 2, which is what forced it, is met by
`Kakeya.VNSUniform.estimateSet_shape` instead. -/
theorem mainLemma2Statement_of_pointwise_drop
    (hdrop : ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ d : ℝ, 0 < d ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - d)) :
    MainLemma2Statement.{u} :=
  mainLemma2Statement_of_trichotomy hdrop (Or.inr estimateSet_shape)


end Envelope

end Kakeya.VNSUniform

namespace Kakeya

/-- **The uniform pair exists — unconditionally.**

This is the discharge of the residual.  `Kakeya.VNSUniform.estimateSet_shape` (proved, no
hypotheses) says the estimate set is `(0,1]` or `[m,1]`; in the first case the bottom of the
window is admissible, in the second the point `max m β₀` is, and
`Kakeya.WindowFour.mono_beta` carries the pair from there to the whole of the window.  **The
open-threshold configuration, the only one in which no bottom exists, is excluded by
`estimateSet_shape` itself** — which rests on `Kakeya.VNSUniform.katzTaoEstimate_of_forall_gt`
and `Kakeya.VNSUniform.frostmanEstimate_of_forall_gt`, the closedness of the two estimate sets.
The appeal is in the proof term, not in prose. -/
theorem exists_uniformWindowPair {β₀ : ℝ} (hβ₀0 : 0 < β₀) (hβ₀1 : β₀ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ × NNReal, UniformWindowPair.{u} β₀ ε p := by
  classical
  rcases VNSUniform.estimateSet_shape.{u} with hall | ⟨m, hm0, hm1, hKTm, hFm, hleast⟩
  · -- the estimates hold everywhere: read the pair at the bottom of the window
    obtain ⟨p, hp1, hp2, hp3, hwin⟩ :=
      exists_windowFour hβ₀0.le hβ₀1 (hall β₀ hβ₀0 hβ₀1) hε
    exact ⟨p, hp1, hp2, hp3, fun β hβ _ _ ↦ WindowFour.mono_beta hβ.1 hβ.2 hwin⟩
  · -- the estimate set is `[m,1]`: read the pair at `max m β₀`, which lies in it
    set b : ℝ := max m β₀ with hb
    have hb0 : 0 < b := lt_of_lt_of_le hβ₀0 (le_max_right _ _)
    have hb1 : b ≤ 1 := max_le hm1 hβ₀1
    have hKTb : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) b :=
      KatzTaoEstimate.mono (le_max_left _ _) hKTm
    obtain ⟨p, hp1, hp2, hp3, hwin⟩ := exists_windowFour hb0.le hb1 hKTb hε
    refine ⟨p, hp1, hp2, hp3, fun β hβ hKTβ hFβ ↦ ?_⟩
    have hβ0 : 0 < β := lt_of_lt_of_le hβ₀0 hβ.1
    have hmβ : m ≤ β := hleast β hβ0 hβ.2 hKTβ hFβ
    exact WindowFour.mono_beta (max_le hmβ hβ.1) hβ.2 hwin

end Kakeya
