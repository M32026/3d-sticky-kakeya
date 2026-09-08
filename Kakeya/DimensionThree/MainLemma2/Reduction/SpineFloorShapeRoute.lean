/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapePayloadNonempty
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeDefectExit
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeFullness

/-!
# The floor and defect alternatives on a refined family

The refined source's `lem:ml2-window-refinement` gives alternative outputs;
an unconditional floor conclusion would select one disjunct without justification.
`DefectBranchAt` states the defect alternative and obtains fullness retention
from `IsShadedRefinementOf.fullness'_le`. `FloorDataAtTrichotomy` combines the
floor and defect alternatives after choosing the window indices `a`, `b`, `m`.
The consumers split on these alternatives.

The identity refinement cannot destroy concentration, as
`lt_pairProfile_of_identity` shows. In the surviving branch, a supplied gain
already yields the conclusion through `trialOutcomeAtGain_of_gain_of_absorb`.
Thus choosing the identity refinement does not produce the required gain;
that gain must be obtained from the floor construction.
-/

@[expose] public section

open MeasureTheory Metric Tube Topology Filter
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ### Route (a): the identity refinement cannot destroy the concentration -/

section RouteA

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- **`(D)` cannot fire at the identity refinement.**  `Kakeya.ML2Core.pairProfile` does not move
when `S' = S`, and `trialOutcomeAtGain_of_refinement_dichotomy`'s own hypotheses `hbefore` and
`hΘ2 : 2 ≤ Θ^{τ/2}` put it strictly above the survival threshold `Θ^{τ/2}/2`, because
`Θ^τ = (Θ^{τ/2})²` and `x ≥ 2` gives `x/2 < x²/2`.

So the dichotomy always takes the surviving branch there, and `hgain` is needed unconditionally. -/
theorem lt_pairProfile_of_identity {Θ τ : ℝ} (hΘ0 : 0 < Θ) (hΘ2 : 2 ≤ Θ ^ (τ / 2))
    {S : Finset ι} {a m : ℕ}
    (hbefore : ENNReal.ofReal (Θ ^ τ / 2) ≤ pairProfile 𝒰 S a m) :
    ENNReal.ofReal (Θ ^ (τ / 2) / 2) < pairProfile 𝒰 S a m := by
  have hsq : Θ ^ τ = (Θ ^ (τ / 2)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (Θ ^ (τ / 2)) 2, ← Real.rpow_mul hΘ0.le]
    norm_num
  have hx : (2 : ℝ) ≤ Θ ^ (τ / 2) := hΘ2
  have hlt : Θ ^ (τ / 2) / 2 < Θ ^ τ / 2 := by
    rw [hsq]; nlinarith
  have hpos : 0 < Θ ^ τ / 2 := by rw [hsq]; nlinarith
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hpos).mpr hlt) hbefore

/-- **The surviving branch's hypothesis already implies the conclusion.**  `hgain` is
`TrialOutcomeAtGain`'s own second disjunct at the exponent `g'`, and `habs` with `1 ≤ Λ` transports
it to `g`.  Together with `Kakeya.ML2Core.lt_pairProfile_of_identity` this is the circularity of
route (a) at the identity refinement. -/
theorem trialOutcomeAtGain_of_gain_of_absorb {h ε₀ g g' β : ℝ} {Λ : ℝ≥0∞} {lam : NNReal}
    {S : Finset ι} {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hΛ : 1 ≤ Λ) (habs : Λ * (δ : ℝ≥0∞) ^ g' ≤ (δ : ℝ≥0∞) ^ g)
    (hgain : ∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ g' * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade)) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z := by
  have hpow : (δ : ℝ≥0∞) ^ g' ≤ (δ : ℝ≥0∞) ^ g := by
    refine le_trans ?_ habs
    calc (δ : ℝ≥0∞) ^ g' = 1 * (δ : ℝ≥0∞) ^ g' := (one_mul _).symm
      _ ≤ Λ * (δ : ℝ≥0∞) ^ g' := by gcongr
  exact Or.inr (Or.inl (hgain.trans (by gcongr)))

end RouteA

/-! ### Route (b), at source shape: a **named** `(D)` branch -/

section RouteB

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The source's `(D)` output, named.**

`lem:ml2-window-refinement`, item `(D)` (l.4093–4097):

> *there are a nonempty `𝕊* ⊂ 𝕊'` and a subshading `Z*` for which `Φ_h(𝕊*) ≤ Φ_h(𝕊') − 1`*

together with the clause shared by all three outputs (l.4100–4108): the `Λf⁻¹` mass retention, the
inherited tower, and *"its shading is a restriction of `Z`"*.  Conjuncts 1 and 2 below are exactly
that: `Kakeya.ML2Core.IsShadedRefinementOf` already packages nonemptiness, the sub-shading, the same
tubes, the `Λf` mass retention and the inherited tower
(`Kakeya.ML2Core.IsClassHomogeneousOn`), and `potential h 𝒰 S' + 1 ≤ potential h 𝒰 S` is
`Φ_h(𝕊*) ≤ Φ_h(𝕊') − 1`.

Conjunct 3 is **not** in the source's `(D)`; it is the dense-shading transfer that the tree's existing
`Kakeya.ML2Core.TrialOutcomeAtGain` carries in its third disjunct.  It is included so that the
branch is consumable with **no new obligation at the consumer**, and
`Kakeya.ML2Core.DefectBranchAt.sourceForm` projects back onto the source's own two conjuncts so the
excess stays auditable.

The `fullness'` retention that the tree's third disjunct also carries is **not** a conjunct here:
`SRC-A`'s `Kakeya.ML2Core.IsShadedRefinementOf.fullness'_le` derives it from clause 5 of the
refinement, so asking for it would have been a fourth excess over the source. -/
def DefectBranchAt (h : ℝ) (Λf : ℝ≥0∞) (lam : NNReal)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (S : Finset ι) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
    IsShadedRefinementOf 𝒰 Λf S Z S' W ∧
    potential h 𝒰 S' + 1 ≤ potential h 𝒰 S ∧
    ∃ lam' : NNReal, 0 < lam' ∧ lam ≤ Λf * lam' ∧
      ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody)

/-- The source's own `(D)`, projected out of `Kakeya.ML2Core.DefectBranchAt`: a refinement with a
potential drop, and nothing else.  Kept so that the two tree-only conjuncts stay visible as an
excess over `lem:ml2-window-refinement` (D). -/
theorem DefectBranchAt.sourceForm {h : ℝ} {Λf : ℝ≥0∞} {lam : NNReal}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    {S : Finset ι} {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hD : DefectBranchAt h Λf lam 𝒰 S Z) :
    ∃ (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      IsShadedRefinementOf 𝒰 Λf S Z S' W ∧ potential h 𝒰 S' + 1 ≤ potential h 𝒰 S := by
  obtain ⟨S', W, href, hdrop, -⟩ := hD
  exact ⟨S', W, href, hdrop⟩

/-- **The `(D)` branch is consumable with no new obligation**: it *is* the third disjunct of the
existing `Kakeya.ML2Core.TrialOutcomeAtGain`. -/
theorem trialOutcomeAtGain_of_defectBranch {h ε₀ g β : ℝ} {Λf : ℝ≥0∞} {lam : NNReal}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    {S : Finset ι} {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hD : DefectBranchAt h Λf lam 𝒰 S Z) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λf lam S Z := by
  obtain ⟨S', W, href, hdrop, lam', hlam'0, hlam', hdense⟩ := hD
  exact Or.inr (Or.inr ⟨S', href.subset, W, href.nonempty, href.2.2.1, href.2.2.2.1,
    href.retention, href.fullness'_le, hdrop, href.classHomogeneous, lam', hlam'0, hlam',
    hdense⟩)

/-- **Route (b)'s payload, at source shape.**   §RR3.3 branch 1: *"State it as a
named `def` per branch … and let `FloorDataAt` conclude `∃ a b m, FBranch … ∨ DBranch …`"*.

`(P)` is deliberately absent: the tree splits it into a separate supplier
(`Kakeya.ML2Core.htrial_of_eccentricData`), which  §RR3.3 records as a faithful
rendering choice and not a dropped disjunct.

The whole price of route (b) is visible in the signature: one extra parameter `h` (the potential
exponent, which the source's `(D)` mentions and the `(F)` branch does not) and one extra binder
`lam`.  The `RR1` binder `S.Nonempty` is kept, since `RR1` lands first and the two do not
interact. -/
def FloorDataAtTrichotomy (β ϖ ε₁ η' h : ℝ) (gain dens : ℝ → ℝ)
    {C : NNReal} {Kl cl : ℕ} (Λf : ℝ≥0∞)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
    ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S) (lam : NNReal),
      ∃ a b m : ℕ,
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
            η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m
        ∨ DefectBranchAt h Λf lam 𝒰 S Z

/-- Route (b) over the whole filter. -/
def FloorPayloadTrichotomy.{w} (β ϖ ε₁ η' h : ℝ) (gain dens : ℝ → ℝ)
    {C : NNReal} {Kl cl : ℕ} (Λf : NNReal → ℝ≥0∞) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu : NNReal)
      (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu),
      FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens (Λf δ) 𝒰

/-- **Control: route (b) is a genuine weakening.**  The `(F)`-only payload implies it; the converse
is the whole point.  With `Kakeya.ML2Core.floorDataAt_toNonempty` this chains from the existing
`FloorDataAt` as well, so nothing that holds today is lost by the re-cut. -/
theorem floorDataAtNonempty_toTrichotomy {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hF : FloorDataAtNonempty (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 := by
  intro S hS hne Z ht hh _
  obtain ⟨a, b, m, hf⟩ := hF S hS hne Z ht hh
  exact ⟨a, b, m, Or.inl hf⟩

end RouteB
/-! ### Route (b)'s consumer check: **both** consumers, each at one `rcases`

 §RR3.3 makes the check a condition of the re-cut.  `FloorDataAt` has exactly two
consumers tree-wide (grep at tip `1d9ffa4cb`):

| consumer | file:line | what it must do |
|---|---|---|
| `Kakeya.ML2Core.htrial_of_floorData` | `Reduction/SpineSiteProducer2.lean:118` | one `rcases`; `(F)` → the existing `hF7` application, `(D)` → `trialOutcomeAtGain_of_defectBranch` |
| `Kakeya.ML2Core.trialSupplier_of_floorRoute` | `Reduction/SpineSiteClosure.lean:557` (through `FloorPayload`) | the same, inside `filter_upwards` |

Both are re-proved below at the trichotomy payload, so the cost is paid visibly and is exactly one
`rcases` plus one `exact` in each.  Nothing else in the tree reads `FloorDataAt` or `FloorPayload`.
-/

section RouteBConsumers

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **Route (b), consumer 1** — `Kakeya.ML2Core.htrial_of_floorData` at the trichotomy payload. -/
theorem htrial_of_floorDataTrichotomy {β ϖ ε₁ η' h ηin : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hF7 : ∀ (a b m : ℕ) (S : Finset ι) (hS : S ⊆ u)
      (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (lam : NNReal),
      S.Nonempty →
      ∀ (ht : ∀ i, (Z i).toTube = (T i).toTube),
      (∀ i, (Z i).shade ⊆ (T i).shade) →
      ∀ (hh : IsClassHomogeneousOn 𝒰 S),
      (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
      ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
      (δ : NNReal) ^ ηin / 2 ≤ lam →
      (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
      Λf * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + 2 * defectMargin β ϖ ε₁ gain dens)
          ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + defectMargin β ϖ ε₁ gain dens) →
      RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
        η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
      ∀ Λ' : ℝ≥0∞, TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
        (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ' lam S Z)
    (hΛf : Λf * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
          + 2 * defectMargin β ϖ ε₁ gain dens)
        ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
          + defectMargin β ϖ ε₁ gain dens))
    (hfloor : FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl)
      β ϖ ε₁ η' h gain dens Λf 𝒰) :
    IsTrialAtGain (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β h ηin 𝒰 Λf := by
  intro S hS Z lam hne ht hs hh hb hmx hd hc hl hcard
  obtain ⟨a, b, m, hbr⟩ := hfloor S hS hne Z ht hh lam
  rcases hbr with hf | hD
  · exact hF7 a b m S hS Z lam hne ht hs hh hb hmx hd hc hl hcard hΛf hf Λf
  · exact trialOutcomeAtGain_of_defectBranch hD

open scoped Classical in
/-- **Route (b), consumer 2** — `Kakeya.ML2Core.trialSupplier_of_floorRoute` at the trichotomy
payload.  This is the endpoint the descent composes into the closure's third row. -/
theorem trialSupplier_of_floorRouteTrichotomy.{w} {β ϖ ε₁ ηin η' h : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Cu₀ : NNReal} {Λf : NNReal → ℝ≥0∞}
    (hF7 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type w} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu : NNReal) (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (a b m : ℕ) (S : Finset ι) (hS : S ⊆ u)
        (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (lam : NNReal),
        S.Nonempty →
        ∀ (ht : ∀ i, (Z i).toTube = (T i).toTube),
        (∀ i, (Z i).shade ⊆ (T i).shade) →
        ∀ (hh : IsClassHomogeneousOn 𝒰 S),
        (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
        Cu ≤ Cu₀ →
        Λf δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + 2 * defectMargin β ϖ ε₁ gain dens)
            ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + defectMargin β ϖ ε₁ gain dens) →
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' (Λf δ) ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
        ∀ Λ : ℝ≥0∞, TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
          (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z)
    (hΛf : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      Λf δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + 2 * defectMargin β ϖ ε₁ gain dens)
          ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + defectMargin β ϖ ε₁ gain dens))
    (hfloor : FloorPayloadTrichotomy.{w} (C := C) (Kl := Kl) (cl := cl)
      β ϖ ε₁ η' h gain dens Λf) :
    TrialSupplier.{w} β ϖ ε₁ ηin h gain dens Cu₀ Λf := by
  filter_upwards [hF7, hΛf, hfloor] with δ hδ hΛ hfl
  intro ι u T Cu 𝒰 hCu hcard S hS Z lam hne ht hs hh hb hmx hd hc hl hcard'
  obtain ⟨a, b, m, hbr⟩ := hfl u T Cu 𝒰 S hS hne Z ht hh lam
  rcases hbr with hf | hD
  · exact hδ u T Cu 𝒰 a b m S hS Z lam hne ht hs hh hb hmx hd hc hl hcard' hCu hΛ hf (Λf δ)
  · exact trialOutcomeAtGain_of_defectBranch hD

end RouteBConsumers

/-! ### the first horn, upgraded from argument to proof -/

section RefinementLoss

/-- **The two dimensional tube-volume constants are ordered.**  A unit-radius tube in `E₃` has
`c₃ ≤ |T| ≤ C₃`, so `c₃ ≤ C₃`.  Taken at `δ = 1` so the `δ^{n-1}` factor is `1` and no cancellation
is needed. -/
theorem le_volume_c_le_volume_le_C :
    Tube.le_volume.c 3 ≤ Tube.volume_le.C 3 := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have h1 := Tube.le_volume (redTube (1 : NNReal))
  have h2 := Tube.volume_le (E := EuclideanSpace ℝ (Fin 3)) (le_refl (1 : NNReal))
    (redTube (1 : NNReal))
  rw [hfr] at h1 h2
  simp only [ENNReal.coe_one, one_pow, mul_one] at h1 h2
  exact_mod_cast h1.trans h2

/-- `1 ≤ Kakeya.ML2Core.tubeVolRatio 3`. -/
theorem one_le_tubeVolRatio_three : 1 ≤ tubeVolRatio 3 := by
  rw [tubeVolRatio, le_div_iff₀ (Tube.le_volume.c_pos 3), one_mul]
  exact le_volume_c_le_volume_le_C

/-- **`R0′`'s loss inherits every `δ`-power in its comparability factor** — the form 's first horn.  `Kakeya.ML2Core.refinementLoss K 3 Cu δ` is at least `K`, so if `K` is a genuine
`δ`-power (at the trial's floor `δ^{ηin}/2 ≤ lam` and `K = lam⁻¹` it is, up to `2 δ^{-ηin}`) then so
is the loss, and the existing `Kakeya.ML2Core.not_eventually_rpow_pow_potentialCeil_le` forbids it in
the `Λf` slot.

the **second** horn — that `StickyKakeya.gridLoss Cu 6 δ`'s exponent `6 (ssfGridLen δ + 1)²`
grows and so escapes every fixed `(1 − log δ)^{K'}` — is **still not **; it needs
`ssfGridLen δ → ∞` asymptotics and it is not load-bearing anywhere ( §RR3.2 closes route
(a) independently, and  makes `hdev` free).  Recorded as prose, deliberately. -/
theorem le_refinementLoss (K : NNReal) {Cu δ : NNReal} (h1Cu : 1 ≤ Cu) (hδ1 : δ ≤ 1) :
    (K : ℝ≥0∞) ≤ refinementLoss K 3 Cu δ := by
  have hgrid : (1 : ℝ) ≤ StickyKakeya.gridLoss Cu 6 δ :=
    StickyKakeya.one_le_gridLoss Cu h1Cu 6 hδ1
  calc (K : ℝ≥0∞) = ((K : NNReal) : ℝ≥0∞) * 1 := (mul_one _).symm
    _ ≤ ((K * tubeVolRatio 3 : NNReal) : ℝ≥0∞) * ENNReal.ofReal (StickyKakeya.gridLoss Cu 6 δ) := by
        gcongr
        · exact_mod_cast le_mul_of_one_le_right (zero_le : (0:NNReal) ≤ K) one_le_tubeVolRatio_three
        · rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hgrid
    _ = refinementLoss K 3 Cu δ := rfl

end RefinementLoss

end Kakeya.ML2Core

end
