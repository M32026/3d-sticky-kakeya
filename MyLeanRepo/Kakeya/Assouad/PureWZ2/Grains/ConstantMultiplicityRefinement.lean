import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityBand
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityHelpers
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Constant-multiplicity refinement for paper tube shadings

Given a cubical paper shading, extract a subshading with point multiplicity
in a constant-ratio band `[μ₀, 2μ₀)` and polylog mass retention.

This wraps `paperDyadicBandPigeonhole` with explicit `μ₀` bounds and shows
preservation of key properties (line class, CWA, cubical).

## Key application

With constant multiplicity, `μ₀` **cancels** in the `h_absorb` condition of
the broad mass budget:

```
2 · M · C · (δ²·N)^(3/2) ≤ √(Q·τ) · mass
M = 2μ₀,  mass ≈ μ₀ · |union|
⟹ 4 · C · (δ²·N)^(3/2) ≤ √(Q·τ) · |union|
```

The resulting condition is purely geometric and independent of multiplicity.

## Whiteprint

This lemma is the key piece for the `outputLoss ≤ 1` case of
`pure_wz2_node04_grains`, enabling the broad mass budget without requiring
an L² estimate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal Finset
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Constant-multiplicity refinement.

Given a cubical paper shading, extract a subshading with multiplicity
in `[μ₀, 2μ₀)` and mass retention `≥ mass / (log₂ N + 1)`.

The subshading uses the same tube family, so line class and CWA are
preserved automatically. -/
lemma constant_multiplicity_refinement
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S) :
    ∃ (level : ℕ) (S' : WZ1PaperTubeShading F),
      let μ₀ : ENNReal := (2 ^ level : ENNReal)
      PaperIsSubshading S' S ∧
      WZ1PaperIsCubicalShading S' ∧
      (∀ p ∈ S'.union, μ₀ ≤ (S'.pointMultiplicity p : ENNReal)) ∧
      (∀ p ∈ S'.union, (S'.pointMultiplicity p : ENNReal) < 2 * μ₀) ∧
      S.mass / ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) ≤ S'.mass := by
  rcases paperDyadicBandPigeonhole hcubical with ⟨level, hcubical', hmass, hmult⟩
  let S' := wz1PaperDyadicBandSubshading S level
  let μ₀ : ENNReal := (2 ^ level : ENNReal)
  have hsub : PaperIsSubshading S' S := by
    intro i
    exact Set.inter_subset_left
  have hlower : ∀ p ∈ S'.union, μ₀ ≤ (S'.pointMultiplicity p : ENNReal) := by
    intro p hp
    exact (hmult p hp).1
  have hupper : ∀ p ∈ S'.union, (S'.pointMultiplicity p : ENNReal) < 2 * μ₀ := by
    intro p hp
    have h : (S'.pointMultiplicity p : ENNReal) < ((2 ^ (level + 1) : ENNReal)) :=
      (hmult p hp).2
    have h2 : ((2 ^ (level + 1) : ENNReal)) = 2 * μ₀ := by
      simp [μ₀, pow_succ]
      ring
    rw [h2] at h
    exact h
  exact ⟨level, S', hsub, hcubical', hlower, hupper, hmass⟩

/-- Multiplicity upper bound `M = 2μ₀` for the refined shading. -/
lemma constant_multiplicity_refinement_upper_bound
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S' : WZ1PaperTubeShading F} {level : ℕ}
    (hmult_upper : ∀ p ∈ S'.union,
      (S'.pointMultiplicity p : ENNReal) < 2 * (2 ^ level : ENNReal)) :
    ∀ p ∈ S'.union, (S'.pointMultiplicity p : ENNReal) ≤ 2 * (2 ^ level : ENNReal) := by
  intro p hp
  exact (hmult_upper p hp).le

/-- High-multiplicity refinement at level ≥ 4 (the m ≥ 12 fix).

Given `hT_mass` with `k_min = 5` (i.e. `S.mass ≥ 64 · volume(S.union)`),
select a dyadic multiplicity band at `level ≥ 4` so that the band
multiplicity lower bound `m = 2^level` satisfies `m ≥ 16 ≥ 12`.

This guarantees the narrow-pruning pipeline constraint `hR : 12 * R ≤ m`
with `R ≥ 1`.

Mass retention is polylogarithmic:
`S.mass ≤ 2 · (log₂ N + 1) · S'.mass`,
so `S'.mass ≥ S.mass / (2(log₂ N+1)) ≥ 32 · V / (log₂ N+1)`,
which is `Ω(V / log N)` and absorbable by the polylog absorption theorem.

Uses `high_multiplicity_dyadic_band` with threshold 4; the stronger
`k_min = 5` mass hypothesis implies the `k_min = 4` requirement. -/
lemma high_multiplicity_refinement_level4
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (hF_nonempty : F.Nonempty)
    (hS_finite : S.mass ≠ ⊤)
    (hT_mass5 : (2 ^ 5 : ENNReal) * volume S.union ≤ S.mass / 2) :
    ∃ (level : ℕ), 4 ≤ level ∧
      let S_k := wz1PaperDyadicBandSubshading S level
      WZ1PaperIsCubicalShading S_k ∧
      (∀ p ∈ S_k.union,
        (2 ^ level : ENNReal) ≤ (S_k.pointMultiplicity p : ENNReal) ∧
        (S_k.pointMultiplicity p : ENNReal) < (2 ^ (level + 1) : ENNReal)) ∧
      S.mass ≤ (2 * (Nat.log 2 F.card + 1 : ENNReal)) * S_k.mass := by
  have hT_mass4 : (2 ^ 4 : ENNReal) * volume S.union ≤ S.mass / 2 := by
    calc
      (2 ^ 4 : ENNReal) * volume S.union
        ≤ (2 ^ 5 : ENNReal) * volume S.union := by
          gcongr
          <;> norm_num
      _ ≤ S.mass / 2 := hT_mass5
  exact high_multiplicity_dyadic_band hcubical hF_nonempty 4 hS_finite hT_mass4

/-- Convenience wrapper returning the subshading directly. -/
lemma high_multiplicity_refinement_level4'
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (hF_nonempty : F.Nonempty)
    (hS_finite : S.mass ≠ ⊤)
    (hT_mass5 : (2 ^ 5 : ENNReal) * volume S.union ≤ S.mass / 2) :
    ∃ (level : ℕ) (S' : WZ1PaperTubeShading F),
      4 ≤ level ∧
      PaperIsSubshading S' S ∧
      WZ1PaperIsCubicalShading S' ∧
      (∀ p ∈ S'.union, (2 ^ level : ENNReal) ≤ (S'.pointMultiplicity p : ENNReal)) ∧
      (∀ p ∈ S'.union, (S'.pointMultiplicity p : ENNReal) < (2 ^ (level + 1) : ENNReal)) ∧
      S.mass ≤ (2 * (Nat.log 2 F.card + 1 : ENNReal)) * S'.mass := by
  rcases high_multiplicity_refinement_level4 hcubical hF_nonempty hS_finite hT_mass5
    with ⟨level, h4, hcubical', hmult, hret⟩
  let S' := wz1PaperDyadicBandSubshading S level
  have hsub : PaperIsSubshading S' S := by
    intro i
    exact Set.inter_subset_left
  exact ⟨level, S', h4, hsub, hcubical',
    fun p hp => (hmult p hp).1, fun p hp => (hmult p hp).2, hret⟩

end Kakeya.Assouad
