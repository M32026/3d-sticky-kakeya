/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Topology.CoveringNumber

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Local nets in Euclidean spaces and on direction caps

`Kakeya.EuclideanNet.exists_sphere_net` produces an `ε`-net of the *whole* unit
sphere, so its cardinality is `≍ ε^(-(n-1))`. When the set to be covered is
already confined to a cap of radius `R`, that global count is wasteful: at the
scale `ε ≍ δ` used by essentially-distinct (ED) packing it contributes a
spurious `δ^(-(n-1))` factor.

This file provides the *local* replacement. All statements are parametric in the
cap radius `R` and the target scale `ε ≤ R`, and every cardinality bound has the
shape

  `|N| ≤ 4 ^ n * (R / ε) ^ n`,   `n = finrank ℝ E`,

depending on `R` and `ε` only through the ratio `R / ε`. Consequently, when both
are proportional to the same parameter `δ` (the ED packing regime `R = A * δ`,
`ε = a * δ`), the bound is an absolute constant `4 ^ n * (A / a) ^ n` with no
`δ` in it. `exists_projective_cap_net_scaled` records that specialisation.

* `exists_local_net_subset` — the core statement: a separated `ε`-net of an
  arbitrary bounded subset of a ball of radius `R`.
* `exists_local_ball_net` — the case of the ball itself.
* `exists_sphere_cap_net` — a net of unit vectors inside a spherical cap.
* `exists_projective_cap_net` — the antipodally symmetric (projective) cap,
  separated and covering for `min ‖u - v‖ ‖u + v‖`.
* `exists_projective_cap_net_scaled` — the `R = A * δ`, `ε = a * δ` form, whose
  cardinality bound is independent of `δ`.

Nets are obtained as maximal `ε`-separated subsets
(`Metric.maximalSeparatedSet`, packaged as
`Bornology.IsBounded.exists_finset_isSeparated_isCover_closedBall`): maximality
gives the covering property and the volume packing bound
`Metric.card_le_of_isSeparated_subset_closedBall` gives the count. The separation
obtained is the full `ε`, which is stronger than the `ε / 2` a greedy
construction would naively guarantee.
-/

@[expose] public section

open Metric MeasureTheory

namespace Kakeya

namespace EuclideanNet

section Local

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The dimensional constant in the local net cardinality bounds: a maximal
`ε`-separated subset of a ball of radius `R ≥ ε` has at most
`localNetConstant E * (R / ε) ^ finrank ℝ E` elements. It depends only on the
dimension, never on `R` or `ε`. -/
noncomputable def localNetConstant (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : ℝ :=
  4 ^ Module.finrank ℝ E

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- The local net cardinality constant is positive. -/
lemma localNetConstant_pos : 0 < localNetConstant E := by
  unfold localNetConstant
  positivity

/-- **Local separated net of a bounded set.**

Let `s` be a bounded set contained in the closed ball of radius `R` about `x`,
and let `0 < ε ≤ R`. Then `s` carries a finite `ε`-net `N ⊆ s` which is
`ε`-separated and has cardinality at most
`localNetConstant E * (R / ε) ^ finrank ℝ E`.

The bound sees `R` and `ε` only through their ratio, so no factor of the ambient
scale is lost. -/
theorem exists_local_net_subset {s : Set E} (hs : Bornology.IsBounded s)
    {x : E} {R ε : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (hsub : s ⊆ Metric.closedBall x R) :
    ∃ N : Finset E,
      (N : Set E) ⊆ s ∧
      (∀ y ∈ s, ∃ c ∈ N, dist y c ≤ ε) ∧
      (∀ c ∈ N, ∀ c' ∈ N, c ≠ c' → ε ≤ dist c c') ∧
      (N.card : ℝ) ≤ localNetConstant E * (R / ε) ^ Module.finrank ℝ E := by
  let w : NNReal := ε.toNNReal
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  have hw_coe : (w : ℝ) = ε := by
    dsimp [w]
    exact Real.coe_toNNReal ε hε_nonneg
  have hw_pos : 0 < w := by
    rw [← NNReal.coe_pos]
    rw [hw_coe]
    exact hε
  have hR_pos : 0 < R := lt_of_lt_of_le hε hεR
  obtain ⟨T, hTsub, hTsep, hTcover, _⟩ :=
    Bornology.IsBounded.exists_finset_isSeparated_isCover_closedBall hs (w := w) hw_pos
  refine ⟨T, hTsub, ?_, ?_, ?_⟩
  · intro y hy
    have hycov := hTcover hy
    rcases Set.mem_iUnion₂.mp hycov with ⟨c, hcT, hcball⟩
    refine ⟨c, Finset.mem_coe.mp hcT, ?_⟩
    have hdist : dist y c ≤ (w : ℝ) := by
      simpa [Metric.mem_closedBall, dist_comm] using hcball
    simpa [hw_coe] using hdist
  · intro c hc c' hc' hne
    have hsep : (w : ENNReal) < edist c c' :=
      hTsep (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hc') hne
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := w)] at hsep
    have hdist_gt : (w : ℝ) < dist c c' :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg w.coe_nonneg).mp hsep
    rw [hw_coe] at hdist_gt
    exact le_of_lt hdist_gt
  · have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
    have hTsubX : (T : Set E) ⊆ Metric.closedBall x R := hTsub.trans hsub
    have hcard : (T.card : ℝ) ≤
        ((2 * (R + (w : ℝ)) / (w : ℝ)) ^ Module.finrank ℝ E) :=
      Metric.card_le_of_isSeparated_subset_closedBall hw_pos hR_nonneg hTsubX hTsep
    calc
      (T.card : ℝ) ≤ ((2 * (R + (w : ℝ)) / (w : ℝ)) ^ Module.finrank ℝ E) := hcard
      _ = ((2 * (R + ε)) / ε) ^ Module.finrank ℝ E := by rw [hw_coe]
      _ ≤ (4 * R / ε) ^ Module.finrank ℝ E := by
        refine pow_le_pow_left₀ ?_ ?_ (Module.finrank ℝ E)
        · positivity
        · exact div_le_div_of_nonneg_right (by nlinarith [hεR]) (by positivity)
      _ = (4 * (R / ε)) ^ Module.finrank ℝ E := by
        congr 1
        ring
      _ = 4 ^ Module.finrank ℝ E * (R / ε) ^ Module.finrank ℝ E := by rw [mul_pow]
      _ = localNetConstant E * (R / ε) ^ Module.finrank ℝ E := rfl

/-- **Local separated net of a ball.** The closed ball of radius `R` about `x`
admits, for every `0 < ε ≤ R`, an `ε`-separated `ε`-net contained in it, of
cardinality at most `localNetConstant E * (R / ε) ^ finrank ℝ E`. -/
theorem exists_local_ball_net (x : E) {R ε : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    ∃ N : Finset E,
      (N : Set E) ⊆ Metric.closedBall x R ∧
      (∀ y ∈ Metric.closedBall x R, ∃ c ∈ N, dist y c ≤ ε) ∧
      (∀ c ∈ N, ∀ c' ∈ N, c ≠ c' → ε ≤ dist c c') ∧
      (N.card : ℝ) ≤ localNetConstant E * (R / ε) ^ Module.finrank ℝ E := by
  exact exists_local_net_subset (s := Metric.closedBall x R) Metric.isBounded_closedBall
    hε hεR subset_rfl

/-- **Local net of a spherical cap.**

For a cap `{u | ‖u‖ = 1 ∧ ‖u - d₀‖ ≤ R}` of chordal radius `R` and a scale
`0 < ε ≤ R`, there is a finite set `N` of unit vectors *inside the cap* such
that every point of the cap is within `ε` of a point of `N`, distinct points of
`N` are at distance at least `ε`, and
`|N| ≤ localNetConstant E * (R / ε) ^ finrank ℝ E`.

Following the convention of this development, directions are unit vectors of `E`
with the ambient (chordal) distance rather than points of a quotient. -/
theorem exists_sphere_cap_net (d₀ : E) {R ε : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    ∃ N : Finset E,
      (∀ c ∈ N, ‖c‖ = 1 ∧ ‖c - d₀‖ ≤ R) ∧
      (∀ u : E, ‖u‖ = 1 → ‖u - d₀‖ ≤ R → ∃ c ∈ N, ‖u - c‖ ≤ ε) ∧
      (∀ c ∈ N, ∀ c' ∈ N, c ≠ c' → ε ≤ ‖c - c'‖) ∧
      (N.card : ℝ) ≤ localNetConstant E * (R / ε) ^ Module.finrank ℝ E := by
  let s : Set E := {u : E | ‖u‖ = 1 ∧ ‖u - d₀‖ ≤ R}
  have hs_sub : s ⊆ Metric.closedBall d₀ R := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hu.2
  have hs_bdd : Bornology.IsBounded s :=
    Metric.isBounded_closedBall.subset hs_sub
  rcases exists_local_net_subset hs_bdd hε hεR hs_sub with
    ⟨N, hNsub, hNcover, hNsep, hNcard⟩
  refine ⟨N, ?_, ?_, ?_, hNcard⟩
  · intro c hc
    exact hNsub hc
  · intro u hu1 huR
    rcases hNcover u ⟨hu1, huR⟩ with ⟨c, hc, hd⟩
    refine ⟨c, hc, ?_⟩
    rwa [dist_eq_norm] at hd
  · intro c hc c' hc' hne
    have hsep : ε ≤ dist c c' := hNsep c hc c' hc' hne
    rwa [dist_eq_norm] at hsep

/-- **Local net of a projective direction cap.**

Here the cap `{u | ‖u‖ = 1 ∧ min ‖u - d₀‖ ‖u + d₀‖ ≤ R}` is antipodally
symmetric and the relevant distance on directions is
`min ‖u - v‖ ‖u + v‖` (`Kakeya.projNormalDist`). For `0 < ε ≤ R ≤ 1 / 2` the cap
admits a finite net `N` of unit vectors which covers it and is `ε`-separated for
that symmetric distance, with
`|N| ≤ localNetConstant E * (R / ε) ^ finrank ℝ E`.

The hypothesis `R ≤ 1 / 2` keeps the cap away from its own antipode, which is
what makes the symmetric separation follow from the ordinary one; it is harmless
in the intended regime `R = A * δ` with `δ` small. -/
theorem exists_projective_cap_net (d₀ : E) (hd₀ : ‖d₀‖ = 1) {R ε : ℝ}
    (hε : 0 < ε) (hεR : ε ≤ R) (hR : R ≤ 1 / 2) :
    ∃ N : Finset E,
      (∀ c ∈ N, ‖c‖ = 1) ∧
      (∀ u : E, ‖u‖ = 1 → min ‖u - d₀‖ ‖u + d₀‖ ≤ R →
        ∃ c ∈ N, min ‖u - c‖ ‖u + c‖ ≤ ε) ∧
      (∀ c ∈ N, ∀ c' ∈ N, c ≠ c' → ε ≤ min ‖c - c'‖ ‖c + c'‖) ∧
      (N.card : ℝ) ≤ localNetConstant E * (R / ε) ^ Module.finrank ℝ E := by
  rcases exists_sphere_cap_net d₀ hε hεR with ⟨N, hN₁, hN₂, hN₃, hN₄⟩
  refine ⟨N, ?_unit, ?_cover, ?_sep, hN₄⟩
  · intro c hc
    exact (hN₁ c hc).1
  · intro u hu hmin
    rcases min_le_iff.mp hmin with hle | hle
    · rcases hN₂ u hu hle with ⟨c, hcN, huc⟩
      refine ⟨c, hcN, ?_⟩
      exact le_trans (min_le_left _ _) huc
    · have hneg_unit : ‖-u‖ = 1 := by rw [norm_neg, hu]
      have hneg_le : ‖-u - d₀‖ ≤ R := by
        rw [show ‖-u - d₀‖ = ‖u + d₀‖ by
          rw [← norm_neg]
          congr 1
          abel]
        exact hle
      rcases hN₂ (-u) hneg_unit hneg_le with ⟨c, hcN, huc⟩
      refine ⟨c, hcN, ?_⟩
      have hsym : ‖-u - c‖ = ‖u + c‖ := by
        rw [← norm_neg]
        congr 1
        abel
      exact le_trans (min_le_right _ _) (by simpa [hsym] using huc)
  · intro c hc c' hc' hne
    have hsep : ε ≤ ‖c - c'‖ := hN₃ c hc c' hc' hne
    have hcz : ‖c - d₀‖ ≤ R := (hN₁ c hc).2
    have hc'z : ‖c' - d₀‖ ≤ R := (hN₁ c' hc').2
    have hnorm2 : ‖(2 : ℝ) • d₀‖ = 2 := by
      rw [norm_smul, hd₀]
      norm_num
    have htri : ‖(2 : ℝ) • d₀‖ ≤ ‖c + c'‖ + ‖c - d₀‖ + ‖c' - d₀‖ := by
      calc
        ‖(2 : ℝ) • d₀‖ = ‖(c + c') - (c - d₀) - (c' - d₀)‖ := by
          congr 1
          rw [two_smul]
          abel
        _ ≤ ‖(c + c') - (c - d₀)‖ + ‖c' - d₀‖ := by
          exact norm_sub_le ((c + c') - (c - d₀)) (c' - d₀)
        _ ≤ ‖c + c'‖ + ‖c - d₀‖ + ‖c' - d₀‖ := by
          exact add_le_add (norm_sub_le (c + c') (c - d₀)) le_rfl
    have hlower : ε ≤ ‖c + c'‖ := by
      linarith
    exact le_min hsep hlower

/-- **Scale-invariant form for ED packing.**

Taking cap radius `R = A * δ` and target scale `ε = a * δ` with `0 < a ≤ A`, the
projective cap net has cardinality at most
`localNetConstant E * (A / a) ^ finrank ℝ E`, an absolute number with no
dependence on `δ`: the two scales cancel in the ratio `R / ε = A / a`. This is
the form ED packing consumes, with `A` the plank-geometry constant and `a` the
sliding constant `c_slide`. -/
theorem exists_projective_cap_net_scaled (d₀ : E) (hd₀ : ‖d₀‖ = 1) {A a δ : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hδ : 0 < δ) (hAδ : A * δ ≤ 1 / 2) :
    ∃ N : Finset E,
      (∀ c ∈ N, ‖c‖ = 1) ∧
      (∀ u : E, ‖u‖ = 1 → min ‖u - d₀‖ ‖u + d₀‖ ≤ A * δ →
        ∃ c ∈ N, min ‖u - c‖ ‖u + c‖ ≤ a * δ) ∧
      (∀ c ∈ N, ∀ c' ∈ N, c ≠ c' → a * δ ≤ min ‖c - c'‖ ‖c + c'‖) ∧
      (N.card : ℝ) ≤ localNetConstant E * (A / a) ^ Module.finrank ℝ E := by
  obtain ⟨N, hN₁, hN₂, hN₃, hNcard⟩ :=
    exists_projective_cap_net d₀ hd₀ (R := A * δ) (ε := a * δ) (mul_pos ha hδ)
      (mul_le_mul_of_nonneg_right haA hδ.le) hAδ
  refine ⟨N, hN₁, hN₂, hN₃, ?_⟩
  calc
    (N.card : ℝ) ≤ localNetConstant E * ((A * δ) / (a * δ)) ^ Module.finrank ℝ E := hNcard
    _ = localNetConstant E * (A / a) ^ Module.finrank ℝ E := by
      rw [mul_div_mul_right A a hδ.ne']

end Local

end EuclideanNet

end Kakeya
