/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreFloorFork
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteProducer2

/-!
# The per-level factoring route, and the one `` row

the alternative, built.  No pigeonhole, no body change: `FloorHypothesisAt`'s count-floor row is
untouched, and the fill is obtained **at each pair separately**, from that level's own factoring.

## The route

B19 that the density-to-count bridge (†) and `FillAt` are equivalent **at a pair**.  the reading follows: nothing forces one body across levels, so at each window level `m > p` run the
biased factoring on the level-`m` cells inside the surviving `p`-cell `T_p(jp)` and use *that*
body.  Two rows come out of one factoring:

* **capture** (`FactoringCaptureAt`) — `Δ_max(𝕊_m⟨T_p⟩) ≤ C_f · Δ(𝕍_{W_m}, W_m)`, which is
  `lemmafactmax`(ii) l.735 (*"𝕍_W is Frostman in W … Δ(𝕍_W, W) ∼ Δ_max(𝕍')"*) read at the level-`m`
  cells; `Kakeya.densityIn` already restricts to the members inside `W_m`, so the containment
  `𝕍_{W_m} ⊆ nodesUnder` is carried by the statement and no separate row is needed;
* **volume** (`FactoringVolumeAt`) — `v · |T_p| ≤ |W_m|`.

`fillAt_of_factoring_body` turns the pair into `FillAt 𝒰 κ p m jp` whenever `κ·C_f ≤ v`, and
`fillFamily_of_perLevelFactoring` / `fillBinder_of_perLevelFactoring` lift it to the binder
`floor_of_windowLevels_of_fill` consumes — which `SpineFibreFloorFork.lean`'s
`floorHypothesisAt_of_fork_parent` then turns into `FloorHypothesisAt` at the fork's `p`.  The
`δ^{O(η')}` price lives entirely in `v`, and is absorbed by `hclose` exactly as l.4142-4147
absorbs the prefactor into `4ζ`.

**The proof spends nothing else.**  `maxDensity_mul_volume_le_sum_of_body` is `densityIn`'s own
definition (`Δ(A,W)·|W| ≤ Σ_A |V|`), and `fillAt_of_factoring_body` is that inequality against
`densityIn_nodesUnder_self`; no dimensional constant, no `Cu`, no band.

## The one `` row, named

> **`FactoringVolumeAt 𝒰 v p b jp W` : `∀ m, p < m → m ≤ b → v · |T_p(jp)| ≤ |W_m|`.**

**Status: ``.**  It interpolates between l.4137-4139 (*"for every `m ∈ 𝒲` with `m > p`"*)
and l.4084-4091 (the non-eccentric John-dimension conditions at the scale where `p` was
determined).  What the source states is that at the **first** scale where the transverse factor
becomes small the factor body is comparable to `T_p` up to `δ^{η'}`; the row above asserts the same
comparison **at every later level `m`**, with the same `v`.  That is not a transcription of any
single sentence — it is the cross-level extension  already identified as the thin step, now
isolated to one inequality between two volumes, with everything else on the route proved.

`factoringVolume_vacuous_at_zero` and `kappa_zero_of_volume_zero` are the firing controls: the row
holds trivially at `v = 0`, and at `v = 0` the `κ` it yields is `0`, i.e. the row carries the entire
strength of the conclusion and cannot be weakened away.

## The (P) branch: the slot is already parametric

`Kakeya.ML2Core.htrial_of_eccentricData` (`SpineSiteProducer2.lean:127`) takes its eccentric data
as a bare `Prop` parameter `EccData` and consumes it through `hecc`.  So `FloorForkAt`'s `Pdata`
slot **instantiates to `EccData` directly** — no shape work is needed on the fork's side, and
`forkPdata_feeds_htrial` compiles that instantiation.  What a (P)-producing fork owes is `hecc`,
the per-family implication from the eccentric data to `TrialOutcomeAtGain`; the John-dimension
conditions of l.4084-4091 are the *content* a caller chooses for `EccData`, and the tree fixes
neither, which is why the existing consumer is parametric.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `maxDensity_mul_volume_le_sum_of_body`, `fillAt_of_factoring_body` | the tower | `(p,m)` at `jp` |
| `FactoringCaptureAt`, `FactoringVolumeAt` | the tower; no shading | every `(p,m)` |
| `fillFamily_of_perLevelFactoring`, `fillBinder_of_perLevelFactoring` | the tower | `(a,p,b)` |
| `forkPdata_feeds_htrial` | `u'` with shading `V` | none |

## A1-a

No `GridUniformCore`; no `(F)`-branch interface statement is defined or altered; no existing line is
modified.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section PerLevel

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **The maximising body's own inequality, before any count.** -/
theorem maxDensity_mul_volume_le_sum_of_body
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {p m : ℕ} {jp : ι}
    (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) {Cf : ENNReal}
    (hcap : Kakeya.maxDensity (𝒰.nodesUnder m p jp)
        (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody)
      ≤ Cf * Kakeya.densityIn (𝒰.nodesUnder m p jp)
          (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody) W) :
    Kakeya.maxDensity (𝒰.nodesUnder m p jp)
        (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody) * volume W.carrier
      ≤ Cf * ∑ j' ∈ 𝒰.nodesUnder m p jp, volume (𝒰.cover.tube m j').carrier := by
  classical
  set A := 𝒰.nodesUnder m p jp with hA
  set V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j' => (𝒰.cover.tube m j').toConvexSpaceBody with hV
  have hsum : Kakeya.densityIn A V W * volume W.carrier
      ≤ ∑ j' ∈ A, volume (V j').carrier := by
    unfold Kakeya.densityIn
    refine le_trans (ENNReal.mul_le_of_le_div le_rfl) ?_
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc Kakeya.maxDensity A V * volume W.carrier
      ≤ (Cf * Kakeya.densityIn A V W) * volume W.carrier := mul_le_mul' hcap le_rfl
    _ = Cf * (Kakeya.densityIn A V W * volume W.carrier) := by ring
    _ ≤ Cf * ∑ j' ∈ A, volume (V j').carrier := mul_le_mul' le_rfl hsum

open scoped Classical in
/-- **`FillAt` at one pair, from that pair's own factoring body.** -/
theorem fillAt_of_factoring_body
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {κ : ℝ} {p m : ℕ} {jp : ι}
    (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) {Cf v : ENNReal}
    (hCf0 : Cf ≠ 0) (hCftop : Cf ≠ ⊤)
    (hk0 : volume (𝒰.cover.tube p jp).carrier ≠ 0)
    (hktop : volume (𝒰.cover.tube p jp).carrier ≠ ⊤)
    (hcap : Kakeya.maxDensity (𝒰.nodesUnder m p jp)
        (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody)
      ≤ Cf * Kakeya.densityIn (𝒰.nodesUnder m p jp)
          (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody) W)
    (hvol : v * volume (𝒰.cover.tube p jp).carrier ≤ volume W.carrier)
    (hnum : ENNReal.ofReal κ * Cf ≤ v) :
    FillAt 𝒰 κ p m jp := by
  classical
  set A := 𝒰.nodesUnder m p jp with hA
  set X := Kakeya.maxDensity A (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody) with hX
  unfold FillAt
  rw [densityIn_nodesUnder_self 𝒰 m p jp, ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop)]
  refine (ENNReal.mul_le_mul_iff_right hCf0 hCftop).mp ?_
  calc Cf * (ENNReal.ofReal κ * X * volume (𝒰.cover.tube p jp).carrier)
      = X * (ENNReal.ofReal κ * Cf) * volume (𝒰.cover.tube p jp).carrier := by ring
    _ ≤ X * v * volume (𝒰.cover.tube p jp).carrier := mul_le_mul' (mul_le_mul' le_rfl hnum) le_rfl
    _ = X * (v * volume (𝒰.cover.tube p jp).carrier) := by ring
    _ ≤ X * volume W.carrier := mul_le_mul' le_rfl hvol
    _ ≤ Cf * ∑ j' ∈ A, volume (𝒰.cover.tube m j').carrier :=
        maxDensity_mul_volume_le_sum_of_body 𝒰 W hcap

open scoped Classical in
/-- **The capture row**, transcribed from `lemmafactmax`(ii) (l.735). -/
def FactoringCaptureAt (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (Cf : ENNReal) (p b : ℕ) (jp : ι)
    (W : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ m : ℕ, p < m → m ≤ b →
    Kakeya.maxDensity (𝒰.nodesUnder m p jp)
        (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody)
      ≤ Cf * Kakeya.densityIn (𝒰.nodesUnder m p jp)
          (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody) (W m)

open scoped Classical in
/-- **The volume row — ``.** -/
def FactoringVolumeAt (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (v : ENNReal) (p b : ℕ) (jp : ι)
    (W : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ m : ℕ, p < m → m ≤ b →
    v * volume (𝒰.cover.tube p jp).carrier ≤ volume (W m).carrier

open scoped Classical in
/-- **The fill family at the fork's parent, from the per-level factorings.** -/
theorem fillFamily_of_perLevelFactoring
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {κ : ℝ} {p b : ℕ} {jp : ι}
    {Cf v : ENNReal} (hCf0 : Cf ≠ 0) (hCftop : Cf ≠ ⊤)
    (hk0 : volume (𝒰.cover.tube p jp).carrier ≠ 0)
    (hktop : volume (𝒰.cover.tube p jp).carrier ≠ ⊤)
    {W : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hcap : FactoringCaptureAt 𝒰 Cf p b jp W)
    (hvol : FactoringVolumeAt 𝒰 v p b jp W)
    (hnum : ENNReal.ofReal κ * Cf ≤ v) :
    ∀ m : ℕ, p < m → m ≤ b → FillAt 𝒰 κ p m jp :=
  fun m hpm hmb =>
    fillAt_of_factoring_body 𝒰 (W m) hCf0 hCftop hk0 hktop (hcap m hpm hmb)
      (hvol m hpm hmb) hnum

open scoped Classical in
/-- **The binder `floor_of_windowLevels_of_fill` consumes**, from per-cell factoring data. -/
theorem fillBinder_of_perLevelFactoring
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {κ : ℝ} {a p b : ℕ}
    {Cf v : ENNReal} (hCf0 : Cf ≠ 0) (hCftop : Cf ≠ ⊤)
    (hk0 : ∀ jp : ι, volume (𝒰.cover.tube p jp).carrier ≠ 0)
    (hktop : ∀ jp : ι, volume (𝒰.cover.tube p jp).carrier ≠ ⊤)
    {W : ι → ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hcap : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ,
      FactoringCaptureAt 𝒰 Cf p b jp (W jp))
    (hvol : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ,
      FactoringVolumeAt 𝒰 v p b jp (W jp))
    (hnum : ENNReal.ofReal κ * Cf ≤ v) :
    ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m : ℕ, p < m → m ≤ b →
      FillAt 𝒰 κ p m jp :=
  fun jθ hjθ jp hjp => fillFamily_of_perLevelFactoring 𝒰 hCf0 hCftop (hk0 jp) (hktop jp)
    (hcap jθ hjθ jp hjp) (hvol jθ hjθ jp hjp) hnum

open scoped Classical in
/-- **Firing control: the volume row is the whole content.** -/
theorem factoringVolume_vacuous_at_zero
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {p b : ℕ} {jp : ι}
    {W : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} :
    FactoringVolumeAt 𝒰 0 p b jp W := by
  intro m _ _
  rw [zero_mul]
  simp

open scoped Classical in
/-- **Firing control: at `v = 0` the produced `κ` collapses.** -/
theorem kappa_zero_of_volume_zero {κ : ℝ} {Cf : ENNReal}
    (hCf0 : Cf ≠ 0) (hnum : ENNReal.ofReal κ * Cf ≤ 0) : ENNReal.ofReal κ = 0 := by
  rw [nonpos_iff_eq_zero, mul_eq_zero] at hnum
  exact hnum.resolve_right hCf0

end PerLevel

section PBranch

universe u

variable {ι : Type u} {δ Cu : NNReal} {u' : Finset ι}
  {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **Match control: the fork's `Pdata` slot is `htrial_of_eccentricData`'s `EccData`.** -/
theorem forkPdata_feeds_htrial {β ϖ ε₁ h ηin : ℝ} {gain dens : ℝ → ℝ}
    {𝒰 : Tube.UniformTubeSet u' (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu} {Λ : ℝ≥0∞}
    {EccData : Prop}
    (hecc : ∀ S ⊆ u', ∀ Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam : NNReal,
      S.Nonempty →
      (∀ i, (Z i).toTube = (V i).toTube) →
      (∀ i, (Z i).shade ⊆ (V i).shade) →
      IsClassHomogeneousOn 𝒰 S →
      (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
      ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
      (δ : NNReal) ^ ηin / 2 ≤ lam →
      (u'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
      EccData →
      TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
        (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z)
    (hdata : EccData) :
    IsTrialAtGain (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β h ηin 𝒰 Λ :=
  htrial_of_eccentricData hecc hdata

end PBranch

end Kakeya.ML2Core

end
