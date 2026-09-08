/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ShadeClassBandDense
public import Kakeya.Tube.CoverCountComparable

/-!
# Assembling `Kakeya.VeryNotSticky.exists_setup_caseSideData` from its pieces

This file assembles GWZ §9.3 — the setup of Lemma 9.1, rendered as
`Kakeya.VeryNotSticky.exists_setup_caseSideData` — from the pieces the tree already holds, and
isolates **exactly two residues**, stated as named hypotheses:

* `Kakeya.VeryNotSticky.LocalMassRefinementResidue` — the class-dense refinement of
  `Kakeya.VeryNotSticky.eventually_bandUniformRefinement_of_card` **together with GWZ (87)**
  (`Kakeya.VeryNotSticky.LocalMassAt`, the field `Kakeya.VeryNotSticky.coarseLocalMass`) at every
  grid scale, and with its mass-retention clause read at `δ^{η/2}` (the slack the proof of
  `eventually_exists_classDenseRefinement` has: it retains `δ^{5η'/4}/8` with `8η' < η`).
  GWZ obtain (87) by applying Lemma 5.11 for each `a = δ^{ηj}` *as a further `≈ 1` refinement*
  (§9.3 p. 36); no field of `Kakeya.VeryNotSticky.BandUniformRefinement` implies it, and no
  declaration in the tree performs that refinement jointly with the class-dense one.
* `Kakeya.VeryNotSticky.SideDataResidue` — GWZ §9.3's side data, blueprint
  `lem:ml2setupSideData`: given a configuration with the prescribed parameters comparing to the
  given family at a constant `≥ δ^{η/2}`, a (possibly further refined) configuration with the same
  parameters, comparing at `≥ δ^η`, carrying `Kakeya.VeryNotSticky.BallData` **and**
  `Kakeya.VeryNotSticky.CaseSideData`. None of the four content structures of `CaseSideData`
  (`ThickDensityThresholds`, `SlabScale`, `CaseScale`, `TangentialInputs`) has a producer
  anywhere in the tree; `ThinConfig` has one (`exists_thinConfig`) which is routed through
  the still-open `Kakeya.ThinCase.factoringApply` and carries (T7) as a hypothesis. The
  refinement freedom is **necessary**: `Kakeya.VeryNotSticky.caseSideData_pieceMass` forbids
  light isolated islands at scale `r₁`, which no field of `Kakeya.VeryNotSticky` forbids, so a
  residue quantified over every configuration *without* refinement would be false.

Everything else is proved here, kernel-clean:

* `Kakeya.VeryNotSticky.eventually_card_of_count` — the cardinality binder
  `1 ≤ δ^{1+2η} |𝕋|` that `eventually_bandUniformRefinement_of_card` consumes, **derived** from
  the repaired count clause at the finest window scale `ρ = δ^{1-exscal}`: an
  essentially distinct all-used `ρ`-family of size `≥ ρ^{-2-ζ}` has at most
  `Tube.coverCountLoss 3 · |𝕋|` members (`Tube.card_le_mul_card_of_chordCover` against the
  trivial cover by the rescaled tubes), and the exponent margin
  `(1-exscal)(2+ζ) - (1+2η) > 0` is `Kakeya.VeryNotSticky.card_margin_of_caseParams`, from
  `CaseParams.slab`, `CaseParams.rhoLeTau` and `β ≤ 1`.
* `Kakeya.VeryNotSticky.rhoCountParent_of_count` — the derived form
  `Kakeya.VeryNotSticky.RhoCountParent` from the repaired count clause, at any constant
  `≥ Tube.coverCountLoss 3` (`Tube.count_of_canonicalCover_shadedTube`). The field `Kakeya.VeryNotSticky.rho_count` is `Kakeya.VeryNotSticky.RhoParentData`,
  produced by `Kakeya.VeryNotSticky.rhoParentData_of_binders` from Lemma 9.1's binders (the
  bounded uniformity `huni` and the fullness `hfull` now among the producers' binders) and the
  retention `Kakeya.VeryNotSticky.card_retention_of_mass`.
* `Kakeya.VeryNotSticky.exists_veryNotSticky_of_rhoCount` — the producer
  `Kakeya.VeryNotSticky.exists_veryNotSticky_of_data` with the old `∀`-over-covers count binder
  replaced by the field it fed, and the refinement constant free.
* `Kakeya.VeryNotSticky.eventually_exists_veryNotSticky_of_localMass` — the configuration from
  the target's binders and the local-mass refinement (the constant `C₀` is enlarged to
  `max C₀ (Tube.coverCountLoss 3)` by `ShadedTube.ShadedUniformTubeSet.mono`, still below the
  cap `δ^{-η'}` for small `δ`).
* `Kakeya.VeryNotSticky.exists_setup_caseSideData_of_residues` — the target's statement from
  the two residues; the `example` after it pins the conclusion to the target's, character for
  character.

The target `exists_setup_caseSideData` itself is **not** touched: its open proof stays until the two
residues are discharged.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

open Produce

/-! ### The exponent margin and the cardinality binder -/

/-- **The cardinality margin of the count clause.** At the finest window scale
`ρ = δ^{1-exscal}` the count clause gives `|𝕋| ≳ ρ^{-2-ζ} = δ^{-(1-exscal)(2+ζ)}`, and the binder
`eventually_bandUniformRefinement_of_card` consumes is `|𝕋| ≥ δ^{-1-2η}`. The margin is
positive because `CaseParams.slab` (`12η + 12 exscal + 3τ < β/2`) with `β ≤ 1` and `τ > 0`
(`CaseParams.rhoLeTau`, `0 < ϱ`) forces `2 exscal + 2η < 1`. -/
theorem card_margin_of_caseParams {β ζ exscal ϱ η τ τ' : ℝ} (hβ1 : β ≤ 1) (hζ : 0 ≤ ζ)
    (hexscal : 0 ≤ exscal) (hϱ : 0 < ϱ) (hη : 0 ≤ η)
    (params : CaseParams β ζ exscal ϱ η τ τ') :
    1 + 2 * η < (1 - exscal) * (2 + ζ) := by
  have h1 := params.slab
  have h2 := params.rhoLeTau
  have hexscal1 : exscal ≤ 1 := le_of_lt (lt_trans params.scale (by norm_num))
  have hτ : 0 < τ := lt_of_lt_of_le hϱ h2
  have hζe : 0 ≤ ζ * (1 - exscal) := mul_nonneg hζ (sub_nonneg.mpr hexscal1)
  nlinarith

open Classical in
/-- **The cardinality binder from the repaired count clause.** For all small `δ`, a family
whose `ρ`-count clause holds has
`|𝕋| ≥ δ^{-1-2η}`, provided the exponent margin `1 + 2η < (1-exscal)(2+ζ)` is positive.

Read at `ρ = δ^{1-exscal}`: `Tube.card_le_mul_card_of_chordCover` against the trivial cover
`fun i ↦ (T i).toTube.rescale ρ` bounds the essentially distinct all-used family by
`Tube.coverCountLoss 3 · |𝕋|`, so `δ^{-(1-exscal)(2+ζ)} ≤ C |𝕋|`, and the constant is absorbed by
the margin once `C ≤ δ^{-margin}`. -/
theorem eventually_card_of_count {ζ exscal η : ℝ} (hexscal0 : 0 ≤ exscal)
    (hexscal : exscal ≤ 1 / 2) (hm : 1 + 2 * η < (1 - exscal) * (2 + ζ)) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        (1 : ENNReal) ≤ (δ : ENNReal) ^ (1 + 2 * η) * (s.card : ENNReal) := by
  set m : ℝ := (1 - exscal) * (2 + ζ) - (1 + 2 * η) with hm_def
  have hmpos : 0 < m := by rw [hm_def]; linarith
  set L : NNReal := Tube.coverCountLoss 3 with hL_def
  have hsmall : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd
    exact hd.2.le
  filter_upwards [self_mem_nhdsWithin, hsmall, eventually_real_le_rpow_neg L hmpos] with
    δ hδ0 hδ1 hLδ
  intro ι s T hcount
  have hδpos : (0 : NNReal) < δ := hδ0
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hfr : Module.finrank ℝ E3 = 3 := by simp
  -- the finest window scale
  set ρ : NNReal := δ ^ (1 - exscal) with hρ_def
  have hmem : ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) :=
    coarseScale_mem_window hδpos hδ1 hexscal
  have hδρ : δ ≤ ρ := by
    calc δ = δ ^ (1 : ℝ) := (NNReal.rpow_one δ).symm
      _ ≤ δ ^ (1 - exscal) := NNReal.rpow_le_rpow_of_exponent_ge hδpos hδ1 (by linarith)
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδpos hδρ
  have hρ1 : ρ ≤ 1 := NNReal.rpow_le_one hδ1 (by linarith)
  obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := hcount ρ hmem
  -- ED ∧ all-used ⟹ `|tρ| ≤ L |𝕋|`, against the trivial cover by the rescaled tubes
  have hcmp := Tube.card_le_mul_card_of_chordCover (E := E3) hρ0 hρ1 (K := 1) le_rfl
    (fun i => (T i).toConvexSpaceBody) s tρ Tρ s (fun i => (T i).toTube.rescale ρ)
    (fun i _ => by simpa using Tube.exists_chord_of_shadedTube (T i)) hED hused
    (fun i hi => ⟨i, hi, by
      have h := Tube.rescale_le_rescale_of_radius_le (T i).toTube hδρ
      rwa [Tube.toConvexSpaceBody_rescale_self] at h⟩)
  rw [hfr] at hcmp
  -- `ρ^{-2-ζ} = δ^{-(1-exscal)(2+ζ)}`
  have hρR : ((ρ : NNReal) : ℝ) = (δ : ℝ) ^ (1 - exscal) := NNReal.coe_rpow _ _
  have hrw : ((ρ : NNReal) : ℝ) ^ (-2 - ζ) = (δ : ℝ) ^ (-((1 - exscal) * (2 + ζ))) := by
    rw [hρR, ← Real.rpow_mul hδR.le]; congr 1; ring
  rw [hrw] at hcard
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    rw [hL_def]; exact Tube.one_le_coverCountLossAt_real 3 1
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le one_pos hL1
  -- `δ^{-(1+2η)} = δ^m · δ^{-(1-exscal)(2+ζ)} ≤ δ^m · L · |𝕋| ≤ |𝕋|`
  have hsplit : (δ : ℝ) ^ (-(1 + 2 * η)) =
      (δ : ℝ) ^ m * (δ : ℝ) ^ (-((1 - exscal) * (2 + ζ))) := by
    rw [← Real.rpow_add hδR]; congr 1; rw [hm_def]; ring
  have hδmL : (δ : ℝ) ^ m * (L : ℝ) ≤ 1 := by
    have hδm : (0 : ℝ) < (δ : ℝ) ^ m := Real.rpow_pos_of_pos hδR m
    have hinv : (δ : ℝ) ^ (-m) = ((δ : ℝ) ^ m)⁻¹ := Real.rpow_neg hδR.le m
    rw [hinv] at hLδ
    calc (δ : ℝ) ^ m * (L : ℝ) ≤ (δ : ℝ) ^ m * ((δ : ℝ) ^ m)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hδm.ne'
  have hfin : (δ : ℝ) ^ (-(1 + 2 * η)) ≤ (s.card : ℝ) := by
    calc (δ : ℝ) ^ (-(1 + 2 * η))
        = (δ : ℝ) ^ m * (δ : ℝ) ^ (-((1 - exscal) * (2 + ζ))) := hsplit
      _ ≤ (δ : ℝ) ^ m * ((tρ.card : ℝ)) := by
          gcongr
      _ ≤ (δ : ℝ) ^ m * ((L : ℝ) * (s.card : ℝ)) := by gcongr
      _ = ((δ : ℝ) ^ m * (L : ℝ)) * (s.card : ℝ) := by ring
      _ ≤ 1 * (s.card : ℝ) := mul_le_mul_of_nonneg_right hδmL (Nat.cast_nonneg _)
      _ = (s.card : ℝ) := one_mul _
  have hmulR : (1 : ℝ) ≤ (δ : ℝ) ^ (1 + 2 * η) * (s.card : ℝ) := by
    have hpos : (0 : ℝ) < (δ : ℝ) ^ (1 + 2 * η) := Real.rpow_pos_of_pos hδR _
    have hinv : (δ : ℝ) ^ (-(1 + 2 * η)) = ((δ : ℝ) ^ (1 + 2 * η))⁻¹ :=
      Real.rpow_neg hδR.le _
    rw [hinv] at hfin
    calc (1 : ℝ) = (δ : ℝ) ^ (1 + 2 * η) * ((δ : ℝ) ^ (1 + 2 * η))⁻¹ :=
          (mul_inv_cancel₀ hpos.ne').symm
      _ ≤ (δ : ℝ) ^ (1 + 2 * η) * (s.card : ℝ) := by gcongr
  have hN : (1 : NNReal) ≤ δ ^ (1 + 2 * η) * (s.card : NNReal) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hmulR
  calc (1 : ENNReal) = ((1 : NNReal) : ENNReal) := by simp
    _ ≤ ((δ ^ (1 + 2 * η) * (s.card : NNReal) : NNReal) : ENNReal) := by exact_mod_cast hN
    _ = (δ : ENNReal) ^ (1 + 2 * η) * (s.card : ENNReal) := by
        rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδpos.ne', ENNReal.coe_natCast]

/-! ### The `ρ`-count field from the repaired count clause -/

/-- **The field `Kakeya.VeryNotSticky.rho_count` from the repaired count clause**, at any constant
`≥ Tube.coverCountLoss 3`.

The parent family is the given family `s` itself. Against an arbitrary essentially distinct
cover of `s` by `ρ`-tubes, the essentially distinct all-used family the clause supplies has at
most `Tube.coverCountLoss 3` times as many members (`Tube.count_of_canonicalCover_shadedTube`),
so `ρ^{-2-ζ} ≤ Tube.coverCountLoss 3 · |cover|`. This is the dimensional constant GWZ's `ζ`-slack
pays for; here it is absorbed into the configuration's uniformity constant `C₀`, which is why
the producer below enlarges `C₀` to `max C₀ (Tube.coverCountLoss 3)`. -/
theorem rhoCountParent_of_count {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ζ exscal η : ℝ}
    (hexscal0 : 0 ≤ exscal) {ι : Type u} {s s' : Finset ι}
    {T T' : ι → ShadedTube δ E3} {Ccount : NNReal}
    (hL : Tube.coverCountLoss 3 ≤ Ccount) (hsub : s' ⊆ s)
    (hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
    (hcount : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) :
    RhoCountParent δ ζ exscal η s' T' Ccount := by
  have hcarset : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  refine ⟨s, hsub, ?_, ?_, ?_⟩
  · intro i hi; rw [hcarset i]; exact hball i hi
  · rw [maxDensity_congr (fun i _ => hbody i)]; exact hmax
  · intro ρ hρ κ' tρ' Tρ' hcov hED'
    obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := hcount ρ hρ
    have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hδ) hρ.1
    have hρ1 : ρ ≤ 1 := hρ.2.trans (NNReal.rpow_le_one hδ1 hexscal0)
    have hfr : Module.finrank ℝ E3 = 3 := by simp
    set L : NNReal := Tube.coverCountLoss 3 with hL_def
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
      rw [hL_def]; exact Tube.one_le_coverCountLossAt_real 3 1
    have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le one_pos hL1
    set c : ℝ := (ρ : ℝ) ^ (-2 - ζ) / (L : ℝ) with hc_def
    have hlow : (L : ℝ) * c ≤ (tρ.card : ℝ) := by
      rw [hc_def, mul_div_cancel₀ _ hLpos.ne']; exact hcard
    have hcov' : ∀ i ∈ s, ∃ j ∈ tρ', (T i).toConvexSpaceBody ≤ (Tρ' j).toConvexSpaceBody := by
      intro i hi
      obtain ⟨j, hj, hle⟩ := hcov i hi
      exact ⟨j, hj, by rwa [hbody i] at hle⟩
    have h := Tube.count_of_canonicalCover_shadedTube (E := E3) hρ0 hρ1 T s tρ Tρ hED hused
      (by rw [hfr]; exact hlow) tρ' Tρ' hcov'
    have hLC : (L : ℝ) ≤ (Ccount : ℝ) := by exact_mod_cast hL
    calc (ρ : ℝ) ^ (-2 - ζ) = (L : ℝ) * c := by
          rw [hc_def, mul_div_cancel₀ _ hLpos.ne']
      _ ≤ (L : ℝ) * (tρ'.card : ℝ) := by gcongr
      _ ≤ (Ccount : ℝ) * (tρ'.card : ℝ) := by gcongr

/-! ### The local-mass clause and the refinement carrying it -/

/-- **GWZ (87) at every grid scale**, for a family `(s, T)`: the clause of the field
`Kakeya.VeryNotSticky.coarseLocalMass`, stated on a bare family so that it can be demanded of a
refinement before the configuration exists. -/
def LocalMassAt {ι : Type u} (δ : NNReal) (η : ℝ) (s : Finset ι) (T : ι → ShadedTube δ E3) :
    Prop :=
  ∀ k : ℕ, k ≤ Tube.ssfGridLen δ → ∀ x : E3,
    (δ : ENNReal) ^ η *
        (volume (Metric.cthickening
              (2 * (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ))
              (⋃ i ∈ s, (T i).toShadedBody.shade)) *
          (volume ((⋃ i ∈ s, (T i).toShadedBody.shade) ∩
                Metric.ball x (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)) /
            volume (Metric.ball x (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)))) ≤
      volume (⋃ i ∈ s, (T i).toShadedBody.shade)

/-- **The band-uniform refinement carrying GWZ (87)**: `Kakeya.VeryNotSticky.BandUniformRefinement`
with its mass-retention clause read at `δ^{η/2}` and one further clause, the local-mass clause
`Kakeya.VeryNotSticky.LocalMassAt` of the refined family.

The retention exponent `η/2` (rather than the `η` of `BandUniformRefinement`) is the slack the
proof of `Kakeya.VeryNotSticky.eventually_exists_classDenseRefinement` has (it retains
`δ^{5η'/4}/8` with `8η' < η`), and it is what leaves the side-data construction
(`Kakeya.VeryNotSticky.SideDataResidue`) room for one further `⪆ 1` refinement inside the
target's budget `δ^η ≤ c`. -/
def BandUniformRefinementLocalMass {ι : Type u} (δ : NNReal) (η η' : ℝ) (s : Finset ι)
    (T : ι → ShadedTube δ E3) : Prop :=
  ∃ (s' : Finset ι) (T' : ι → ShadedTube δ E3), s' ⊆ s ∧
    (∀ i, (T' i).toTube = (T i).toTube) ∧
    (∀ i, (T' i).shade ⊆ (T i).shade) ∧
    (∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀)) ∧
    (∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤ volume (T' i).shade) ∧
    (1 : ENNReal) ≤ (δ : ENNReal) * (s'.card : ENNReal) ∧
    (δ : ENNReal) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s', volume (T' i).shade ∧
    LocalMassAt δ η s' T'

/-- The local-mass refinement is a strengthening of `Kakeya.VeryNotSticky.BandUniformRefinement`:
dropping the local-mass clause and weakening the retention from `δ^{η/2}` to `δ^η`. -/
theorem BandUniformRefinementLocalMass.toBandUniformRefinement {ι : Type u} {δ : NNReal}
    (hδ1 : δ ≤ 1) {η η' : ℝ} (hη : 0 ≤ η) {s : Finset ι}
    {T : ι → ShadedTube δ E3} (h : BandUniformRefinementLocalMass δ η η' s T) :
    BandUniformRefinement δ η η' s T := by
  obtain ⟨s', T', hs', htube, hsh, huni, hpt, htc, hmass, -⟩ := h
  refine ⟨s', T', hs', htube, hsh, huni, hpt, htc, le_trans ?_ hmass⟩
  exact mul_le_mul_left
    (ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.coe_le_one_iff.mpr hδ1) (by linarith)) _

/-! ### The producer, with the count field as a binder -/

/-- **Configuration `hyp:ml2setup` from its data, with the `ρ`-count field as a binder.**

`Kakeya.VeryNotSticky.exists_veryNotSticky_of_data` with the refinement constant `c` of the
mass-retention binder free (the original fixes it at `δ^η`); the `ρ`-count field
`Kakeya.VeryNotSticky.RhoParentData` is the binder `hrho` in both.
Every other binder and every other field are as in the original. -/
theorem exists_veryNotSticky_of_rhoCount {β ζ exscal ϱ η : ℝ} {δ : NNReal}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal)
    (hwδ : 6 * δ ^ (exscal - η) ≤ w.wρ)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hgrid : 1 ≤ η * (Tube.ssfGridLen δ : ℝ))
    (habs : (aScaleDataConstant C₀ 1 : ENNReal) ^ 2
      ≤ (δ : ENNReal) ^ (-η))
    {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ E3}
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
    {s' : Finset ι} (hs' : s' ⊆ s) {T' : ι → ShadedTube δ E3}
    (htube : ∀ i, (T' i).toTube = (T i).toTube)
    (hsh : ∀ i, (T' i).shade ⊆ (T i).shade)
    (hrho : RhoParentData δ ζ exscal η s' T')
    (huni : Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀))
    (hpt : ∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).toShadedBody.carrier
      ≤ volume (T' i).toShadedBody.shade)
    (htc : (1 : ENNReal) ≤ (δ : ENNReal) * (s'.card : ENNReal))
    (hloss : ((_root_.ShadedBody.rhoTubesSection9Loss 3 s'.card δ : NNReal) : ENNReal)
      ≤ (δ : ENNReal) ^ (-η))
    (hindloss : ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)
      ≤ (δ : ENNReal) ^ (-η))
    (hclm : LocalMassAt δ η s' T')
    {c : NNReal}
    (hmass : (c : ENNReal) * ∑ i ∈ s, volume (T i).shade
      ≤ ∑ i ∈ s', volume (T' i).shade)
    {a b : NNReal}
    (hdims : δ ≤ a ∧ a ≤ b ∧ b ≤ δ ^ exscal) :
    ∃ (cfg : VeryNotSticky.{u}) (e : cfg.ι ≃ ι),
      (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧ cfg.η = η) ∧
      ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
        (fun i ↦ (cfg.T (e.symm i)).toShadedBody) s (fun i ↦ (T i).toShadedBody) c := by
  classical
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  have hcarset : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi; rw [hcarset i]; exact hball i hi
  have hmax' : maxDensity s (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) := by
    rw [maxDensity_congr (fun i _ => hbody i)]; exact hmax
  have hmaxs' : maxDensity s' (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) :=
    le_trans (maxDensity_mono _ hs') hmax'
  obtain ⟨lam, Cd, hCd, hlam, hlb, hub⟩ :=
    exists_band_of_pointwise_two_eta hδ hδ1 hη T' hpt
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with h | h
    · rw [h] at htc; simp at htc
    · exact h
  obtain ⟨i₀, hi₀⟩ := hs'ne
  have hvpos : 0 < volume (T' i₀).carrier := by
    refine lt_of_lt_of_le ?_ (Tube.le_volume (T' i₀).toTube)
    have hc : ((Tube.le_volume.c (Module.finrank ℝ E3) : NNReal) : ENNReal) ≠ 0 := by
      simpa using (Tube.le_volume.c_pos (Module.finrank ℝ E3)).ne'
    have hd : ((δ : ENNReal) ^ (Module.finrank ℝ E3 - 1)) ≠ 0 :=
      pow_ne_zero _ (by simpa using hδ.ne')
    exact pos_iff_ne_zero.mpr (mul_ne_zero hc hd)
  have hsumne : ∑ i ∈ s', volume (T' i).toShadedBody.carrier ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le hvpos ?_)
    exact Finset.single_le_sum (f := fun i => volume (T' i).toShadedBody.carrier)
      (fun i _ => bot_le) hi₀
  have hfull : (δ ^ (2 * η) : NNReal) ≤ ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) := by
    refine le_fullness_of_pointwise hsumne (fun i hi => ?_)
    rw [ENNReal.coe_rpow_of_ne_zero hδ0]
    exact hpt i hi
  refine ⟨{ β := β, hβ := hβ, hβ1 := hβ1, ζ := ζ, hζ := hζ, δ := δ, hδ := hδ, hδ1 := hδ1,
            exscalb := exscal, hexscalb := hexscal, exscal := exscal, hexscal := hexscal,
            hscale := rfl, η := η, hη := hη, ι := ι, decidableEq := inferInstance,
            s := s', T := T',
            contained := fun i hi => hball' i (hs' hi),
            C₀ := C₀,
            hC₀ := hC₀,
            D₀ := 1, hD₀ := le_rfl, ckt := w.toData hwδ,
            uniform := huni,
            maxDensity_le := hmaxs',
            fullness_ge := hfull,
            lam := lam, Cd := Cd, hCd := hCd, lam_ge := hlam,
            shading_lb := hlb, shading_ub := hub,
            rho_count := hrho,
            ktEstimate := hKT, fEstimate := hF,
            ϱ := ϱ, hϱ := hϱ, a := a, b := b, hdims := hdims,
            tube_count := htc,
            aScaleData_absorb := habs,
            coarseLoss_absorb := hloss,
            inducedFullnessLoss_absorb := hindloss,
            coarseLocalMass := hclm,
            gridFine := hgrid },
    Equiv.refl ι, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  simp only [Equiv.refl_toEmbedding, Finset.map_refl, Equiv.refl_symm, Equiv.refl_apply]
  exact ⟨⟨hs', fun i _ => ⟨hbody i, hsh i⟩⟩, hmass⟩

/-- **Configuration `hyp:ml2setup` from the target's binders and the local-mass refinement**,
for all small `δ`, with the refinement constant `≥ δ^{η/2}`.

This is `Kakeya.VeryNotSticky.eventually_exists_veryNotSticky` with three changes: the count
binder is the repaired `∃`-form and, together with Lemma 9.1's bounded uniformity
`huni` and fullness `hfull`, feeds the datum `rho_count` through
`Kakeya.VeryNotSticky.rhoParentData_of_binders` with the retention
`Kakeya.VeryNotSticky.card_retention_of_mass` — the configuration's own constant is
`max C₀ (Tube.coverCountLoss 3)`, to which the uniformity bundle is transported by
`ShadedTube.ShadedUniformTubeSet.mono` and which is still below the cap `δ^{-η'}` for small `δ`;
the local-mass field is read off the refinement
(`Kakeya.VeryNotSticky.BandUniformRefinementLocalMass`) instead of being demanded of every
sub-shading; and the retention is `δ^{η/2}`. -/
theorem eventually_exists_veryNotSticky_of_localMass {β ζ exscal ϱ η η' τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (hη' : 0 < η') (h8 : 8 * η' < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        BandUniformRefinementLocalMass δ η η' s T →
        ∃ (cfg : VeryNotSticky.{u}) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
            (fun i ↦ (cfg.T (e.symm i)).toShadedBody) s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ (η / 2) ≤ (c : ENNReal) := by
  classical
  have hη1 : η ≤ 1 := by
    have h1 := params.slabDensity
    have h2 := params.scale
    linarith
  have hexscal1 : exscal ≤ 1 := le_of_lt (lt_trans params.scale (by norm_num))
  set L : NNReal := Tube.coverCountLoss 3 with hL_def
  filter_upwards [eventually_gridFine hη,
      eventually_aScaleData_absorb_of_le 1 h8,
      eventually_coarseLoss_absorb (η := η) (K := (4 : ℝ)) hη (by norm_num),
      Kakeya.ML2Assembly.eventually_card_thresholds,
      Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
        (K := ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal))
        ENNReal.coe_ne_top hη,
      Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg (K := ((L : NNReal) : ENNReal))
        ENNReal.coe_ne_top hη',
      w.eventually_radius (by linarith [params.slabDensity, hη] : (0:ℝ) < exscal - η)] with
    δ hgrid habs hcoarse hthr hindloss hLcap hwδ
  obtain ⟨hδ, hδ1, hδC⟩ := hthr
  intro ι s T hball huni hmax hfull hcount hband
  letI : DecidableEq ι := Classical.decEq ι
  obtain ⟨s', T', hs', htube, hsh, ⟨C₀, hC₀, hcap, ⟨𝒱⟩⟩, hpt, htc, hmass, hclm⟩ := hband
  -- the enlarged uniformity constant
  set C₁ : NNReal := max C₀ L with hC₁_def
  have hC₁ : 1 ≤ C₁ := le_trans hC₀ (le_max_left _ _)
  have hcap₁ : (C₁ : ENNReal) ≤ (δ : ENNReal) ^ (-η') := by
    rw [hC₁_def, ENNReal.coe_max]
    exact max_le hcap hLcap
  have huni₁ : Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₁) :=
    ⟨𝒱.mono (le_max_left _ _)⟩
  -- carriers are unchanged
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  have hcarset : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi; rw [hcarset i]; exact hball i hi
  have hmax' : maxDensity s (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) := by
    rw [maxDensity_congr (fun i _ => hbody i)]; exact hmax
  have hmaxs' : maxDensity s' (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) :=
    le_trans (maxDensity_mono _ hs') hmax'
  -- the `ρ`-count datum: the count on the parent `s` itself, with the parent's hierarchy at
  -- Lemma 9.1's constant and the retention `δ^{2η}|s| ≤ |s'|`
  have hret : (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) ≤ (s'.card : ENNReal) :=
    card_retention_of_mass hδ hδ1 hs' htube hfull
      (ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.coe_le_one_iff.mpr hδ1) (by linarith)) hmass
  have hrho : RhoParentData δ ζ exscal η s' T' :=
    rhoParentData_of_binders hs' htube hball hmax huni hcount hret
  -- the cardinality budget, from the binders
  have hcardR : (s'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) :=
    Kakeya.ML2Assembly.card_le_rpow_neg_four hδ hδ1 hδC s' T'
      (fun i hi => hball' i (hs' hi)) hη1 hmaxs'
  have hcardN : ((s'.card : NNReal)) ≤ δ ^ (-(4 : ℝ)) := by
    have h : ((s'.card : NNReal) : ℝ) ≤ ((δ ^ (-(4 : ℝ)) : NNReal) : ℝ) := by
      rw [NNReal.coe_natCast, NNReal.coe_rpow]; exact hcardR
    exact_mod_cast h
  -- `s'` is nonempty
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with h | h
    · rw [h] at htc; simp at htc
    · exact h
  obtain ⟨i₀, hi₀⟩ := hs'ne
  have hloss := hcoarse s'.card (Finset.card_pos.mpr ⟨i₀, hi₀⟩) hcardN
  -- the working dimensions, at `a = b = δ`
  have hdd : δ ≤ δ ^ exscal := by
    have h := NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 hexscal1
    simpa using h
  -- the retention constant
  have hmass' : (((δ ^ (η / 2) : NNReal)) : ENNReal) * ∑ i ∈ s, volume (T i).shade
      ≤ ∑ i ∈ s', volume (T' i).shade := by
    rw [ENNReal.coe_rpow_of_ne_zero hδ.ne']; exact hmass
  obtain ⟨cfg, e, hexp, href⟩ := exists_veryNotSticky_of_rhoCount hβ hβ1 hζ hexscal hϱ hη hδ hδ1
    hKT hF w hwδ hC₁ hgrid (habs C₁ hC₁ hcap₁)
    hball hmax hs' htube hsh hrho huni₁ hpt htc hloss hindloss hclm
    hmass' ⟨le_rfl, le_rfl, hdd⟩
  refine ⟨cfg, e, δ ^ (η / 2), hexp, href, ?_⟩
  rw [ENNReal.coe_rpow_of_ne_zero hδ.ne']

/-! ### The two residues, named -/

/-- **Residue 1 — the local-mass refinement** (GWZ §9.3 p. 36: the `⪆ 1` refinement obtained by
applying Lemma 5.11 at each `a = δ^{ηj}`, on top of the class-dense refinement of
`Kakeya.VeryNotSticky.eventually_exists_classDenseRefinement`).

From the target's binders `hball`, `hmax`, `hfull` and the cardinality binder — which
`Kakeya.VeryNotSticky.eventually_card_of_count` derives from the count clause — a
`Kakeya.VeryNotSticky.BandUniformRefinementLocalMass` exists. Without the local-mass clause and
with retention `δ^η` this is `Kakeya.VeryNotSticky.eventually_bandUniformRefinement_of_card`,
proved. -/
def LocalMassRefinementResidue (η η' : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
      δ ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
      (1 : ENNReal) ≤ (δ : ENNReal) ^ (1 + 2 * η) * (s.card : ENNReal) →
      BandUniformRefinementLocalMass δ η η' s T

/-- **Residue 2 — the side data of the case split** (blueprint `lem:ml2setupSideData`, GWZ §9.3
after (87)).

Given the parameter budgets `Kakeya.VeryNotSticky.CaseParams` and the plank-Frostman budget
`Kakeya.VeryNotSticky.PlankFrostmanBudget` (which the fields `budget` and `plankF` of
`Kakeya.VeryNotSticky.ThickDensityThresholds` spend), the target's binders on `(𝕋, Y)`, and a
configuration with the prescribed parameters
comparing to `(𝕋, Y)` at a constant `≥ δ^{η/2}`, there is a configuration with the same
parameters — a further `⪆ 1` refinement is permitted, the total comparison staying `≥ δ^η` —
together with per-ball data `Kakeya.VeryNotSticky.BallData` and the side data
`Kakeya.VeryNotSticky.CaseSideData`. The refinement freedom is necessary:
`Kakeya.VeryNotSticky.caseSideData_pieceMass` forbids light isolated islands at scale `r₁`,
which no field of `Kakeya.VeryNotSticky` forbids. -/
def SideDataResidue (β ζ exscal ϱ η τ τ' : ℝ) : Prop :=
  CaseParams β ζ exscal ϱ η τ τ' →
  PlankFrostmanBudget.{u} β ϱ τ η →
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (∀ i ∈ s, (T i).toTube.IsCentred) →
      (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
      maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
        ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
          (tρ : Set κ).Pairwise
            (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
          (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
          (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
      ∀ (cfg : VeryNotSticky.{u}) (e : cfg.ι ≃ ι) (c : NNReal),
        (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
            cfg.η = η) →
        ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
          (fun i ↦ (cfg.T (e.symm i)).toShadedBody) s (fun i ↦ (T i).toShadedBody) c →
        (δ : ENNReal) ^ (η / 2) ≤ (c : ENNReal) →
        ∃ (cfg' : VeryNotSticky.{u}) (bd : BallData cfg') (e' : cfg'.ι ≃ ι) (c' : NNReal),
          (cfg'.β = β ∧ cfg'.ζ = ζ ∧ cfg'.δ = δ ∧ cfg'.exscal = exscal ∧ cfg'.ϱ = ϱ ∧
              cfg'.η = η) ∧
          ShadedBody.IsCRefinement (cfg'.s.map e'.toEmbedding)
              (fun i ↦ (cfg'.T (e'.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c' ∧
          (δ : ENNReal) ^ η ≤ (c' : ENNReal) ∧
          Nonempty (CaseSideData cfg' bd τ τ')

/-! ### The assembly -/

/-- **`Kakeya.VeryNotSticky.exists_setup_caseSideData` from its two residues.**

The binder list and the conclusion are the target's, character for character (the `example`
below pins this); the two extra hypotheses are `Kakeya.VeryNotSticky.LocalMassRefinementResidue`
at an exponent `η'` with `8η' < η` and `Kakeya.VeryNotSticky.SideDataResidue`. Everything else —
the cardinality binder from the count clause, the `ρ`-count field, the configuration — is proved
here. -/
theorem exists_setup_caseSideData_of_residues {β ζ exscal ϱ η τ τ' : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal)
    {η' : ℝ} (hη' : 0 < η') (h8 : 8 * η' < η)
    (hRef : LocalMassRefinementResidue.{u} η η')
    (hSide : SideDataResidue.{u} β ζ exscal ϱ η τ τ') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (CaseSideData cfg bd τ τ') := by
  have hexscal1 : exscal ≤ 1 / 2 := le_of_lt params.scale
  have hm : 1 + 2 * η < (1 - exscal) * (2 + ζ) :=
    card_margin_of_caseParams hβ1 hζ.le hexscal.le hϱ hη.le params
  filter_upwards [hRef, hSide params hplankF,
    eventually_exists_veryNotSticky_of_localMass.{u} hβ hβ1 hζ hexscal hϱ hη hη' h8 params hKT hF w,
    eventually_card_of_count.{u} hexscal.le hexscal1 hm] with
    δ hRefδ hSideδ hcfgδ hcardδ
  intro ι s T hball hcen huni hmax hfull hcount
  have hcard : (1 : ENNReal) ≤ (δ : ENNReal) ^ (1 + 2 * η) * (s.card : ENNReal) :=
    hcardδ s T hcount
  have hband : BandUniformRefinementLocalMass δ η η' s T := hRefδ s T hball hmax hfull hcard
  obtain ⟨cfg, e, c, hexp, href, hc⟩ := hcfgδ s T hball huni hmax hfull hcount hband
  exact hSideδ s T hball hcen huni hmax hfull hcount cfg e c hexp href hc

/-- **Tripwire**: the conclusion of `exists_setup_caseSideData_of_residues` is the statement of
`Kakeya.VeryNotSticky.exists_setup_caseSideData`, character for character, once the two residues
are supplied at some `η'` with `8η' < η`. If the target's statement moves, this stops
typechecking. -/
example {β ζ exscal ϱ η τ τ' : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal)
    (hRef : LocalMassRefinementResidue.{u} η (η / 9))
    (hSide : SideDataResidue.{u} β ζ exscal ϱ η τ τ') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (CaseSideData cfg bd τ τ') :=
  exists_setup_caseSideData_of_residues hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
    (by positivity) (by linarith) hRef hSide

end Kakeya.VeryNotSticky
