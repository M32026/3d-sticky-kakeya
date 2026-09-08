/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupAssembly
public import Kakeya.Factoring.RhoTubesSection9
public import Kakeya.Covers
public import Kakeya.BallDense

/-!
# GWZ (87) at one grid scale from Lemma 5.11, and its interpolation between grid scales

The residue `Kakeya.VeryNotSticky.LocalMassRefinementResidue` asks for the clause
`Kakeya.VeryNotSticky.LocalMassAt` — GWZ (87), the field `Kakeya.VeryNotSticky.coarseLocalMass` —
on a refinement, at every index of the grid `ρ_k = δ^{k/M}`, `M = ⌈log log 1/δ⌉`. This file
supplies the two mechanical pieces of the route priced in  (B1 and B2); the
multi-scale chaining B3 is not attempted here.

* `Kakeya.VeryNotSticky.LocalMassClauseAt δ N k g s T` — the clause of `LocalMassAt` at a single
  grid index `k` of the grid of length `N`, at an explicit gain `g` in place of `δ^η`;
  `Kakeya.VeryNotSticky.localMassAt_iff_forall_clause` pins it to the field's clause verbatim.
* `Kakeya.VeryNotSticky.localMassAt_clause_of_rhoTubesSection9` — **the one-scale bridge (B1)**:
  from GWZ Lemma 5.11 at a grid index `k` (`ShadedBody.exists_rhoTubesSection9_gridScale`, with
  its exposed `2ρ`-thick outer shading), a refinement `(s', T')` of `(s, T)` — an index selection
  with the shading cut, tubes unchanged, a `L⁻¹`-refinement in the sense of
  `ShadedBody.IsCRefinement` — satisfying the clause at index `k` **for every `x`**, at the gain
  `(K₃ · L)⁻¹` with `L = ShadedBody.rhoTubesSection9Loss 3 |s| δ` the honest loss of Lemma 5.11
  and `K₃ = 9261 = 343 · 27` a closed numeral: `343 = 7³` is the Vitali constant of
  `Kakeya.VeryNotSticky.volume_cthickening_le_of_core_balls`
  (`|N_{2ρ}(U')| ≤ 343 |⋃ outer shades|`,  "`≲`") and `27 = 3³` the packing constant
  of `Kakeya.VeryNotSticky.clause_forall_of_clause_on`.
* `Kakeya.VeryNotSticky.localMassAt_clause_mono_index` — **interpolation (B2)**: the clause at
  index `j` at gain `g` implies the clause at every index `k ≥ j` at gain `g · (ρ_k/ρ_j)³`, and
  `localMassAt_clause_mono_index_rpow` reads the cost off the exponents: when
  `(k - j)/N ≤ η/s` the factor is at least `δ^{3η/s}` ((c): every grid instance
  follows from `O(s/η)` chained scales spaced `δ^{η/s}` at cost `δ^{-3η/s}` each).

## Where the `2ρ`-thickness argument needs `Tube.carrier_eq`

In `localMassClause_of_thick_factorFamily`: a point `y` of an inner shade lies in the carrier of
the parent `ρ`-tube `W j`, which by `Tube.carrier_eq` is `⋃_{z ∈ segment} closedBall z ρ`; the
core point `z` with `dist y z ≤ ρ` gives `closedBall z ρ ⊆ W j ∩ N_{2ρ}(Y'(T_i))`, and the exposed
conjunct of Lemma 5.11 puts that ball inside the outer shade. This is the only place the tube
geometry enters; everything else is Vitali covering and packing in `ℝ³`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody
open scoped NNReal ENNReal
open Produce

/-! ### The clause at a single grid index -/

/-- **GWZ (87) at one grid index, at an explicit gain.** The clause of
`Kakeya.VeryNotSticky.LocalMassAt` (the field `Kakeya.VeryNotSticky.coarseLocalMass`) at the
single index `k` of the grid `ρ_k = δ^{k/N}`, with the gain `g` in place of `δ^η`: for every `x`,
`g · |N_{2ρ_k}(U)| · |U ∩ B(x, ρ_k)| / |B(x, ρ_k)| ≤ |U|`, `U = ⋃_{i ∈ s} Y(T_i)`. -/
def LocalMassClauseAt {ι : Type*} (δ : ℝ≥0) (N k : ℕ) (g : ℝ≥0∞) (s : Finset ι)
    (T : ι → ShadedTube δ E3) : Prop :=
  ∀ x : E3,
    g * (volume (cthickening (2 * (Tube.gridScale δ N k : ℝ))
          (⋃ i ∈ s, (T i).toShadedBody.shade)) *
        (volume ((⋃ i ∈ s, (T i).toShadedBody.shade) ∩ ball x (Tube.gridScale δ N k : ℝ)) /
          volume (ball x (Tube.gridScale δ N k : ℝ)))) ≤
      volume (⋃ i ∈ s, (T i).toShadedBody.shade)

/-- **Tripwire: the field's clause is the single-index clause at every grid index, at the gain
`δ^η`.** Definitional; if `LocalMassAt` moves, this stops typechecking. -/
theorem localMassAt_iff_forall_clause {ι : Type u} (δ : ℝ≥0) (η : ℝ) (s : Finset ι)
    (T : ι → ShadedTube δ E3) :
    LocalMassAt δ η s T ↔
      ∀ k : ℕ, k ≤ Tube.ssfGridLen δ →
        LocalMassClauseAt δ (Tube.ssfGridLen δ) k ((δ : ℝ≥0∞) ^ η) s T :=
  Iff.rfl

/-- The clause is monotone in the gain: a smaller gain is a weaker demand. -/
theorem LocalMassClauseAt.mono_gain {ι : Type*} {δ : ℝ≥0} {N k : ℕ} {g g' : ℝ≥0∞}
    {s : Finset ι} {T : ι → ShadedTube δ E3} (hg : g' ≤ g)
    (h : LocalMassClauseAt δ N k g s T) : LocalMassClauseAt δ N k g' s T :=
  fun x => le_trans (mul_le_mul_left hg _) (h x)

/-- **The exponent is a parameter.** For `δ ≤ 1` a smaller exponent is a larger gain, so the
clause at gain `δ^{ε'}` gives the clause at gain `δ^{ε}` for every `ε ≥ ε'`: the B3 chaining may
deliver the clause at any slack exponent and read the field's
exponent off it. -/
theorem LocalMassClauseAt.rpow_of_exponent_le {ι : Type*} {δ : ℝ≥0} (hδ1 : δ ≤ 1) {N k : ℕ}
    {ε' ε : ℝ} (hε : ε' ≤ ε) {s : Finset ι} {T : ι → ShadedTube δ E3}
    (h : LocalMassClauseAt δ N k ((δ : ℝ≥0∞) ^ ε') s T) :
    LocalMassClauseAt δ N k ((δ : ℝ≥0∞) ^ ε) s T :=
  h.mono_gain (ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.coe_le_one_iff.mpr hδ1) hε)

/-- **The field's clause from the single-index clause at a slack exponent.** If the clause holds
at every grid index at gain `δ^{ε'}` with `ε' ≤ η`, then `Kakeya.VeryNotSticky.LocalMassAt δ η`
holds: this is how a chain run at exponent `η/2` discharges the field at exponent `η`. -/
theorem localMassAt_of_forall_clause_rpow {ι : Type u} {δ : ℝ≥0} (hδ1 : δ ≤ 1) {ε' η : ℝ}
    (hε : ε' ≤ η) {s : Finset ι} {T : ι → ShadedTube δ E3}
    (h : ∀ k : ℕ, k ≤ Tube.ssfGridLen δ →
      LocalMassClauseAt δ (Tube.ssfGridLen δ) k ((δ : ℝ≥0∞) ^ ε') s T) :
    LocalMassAt δ η s T :=
  (localMassAt_iff_forall_clause δ η s T).mpr fun k hk =>
    (h k hk).rpow_of_exponent_le hδ1 hε

/-! ### Vitali covering and packing in `ℝ³` -/

/-- **The `2ρ`-neighbourhood of a set every point of which has a core `ρ`-ball inside `W` within
distance `ρ` is at most `7³ = 343` times `W` in volume.**

A maximal `4ρ`-separated net `P ⊆ U` covers `N_{2ρ}(U)` by the balls `B̄(p, 7ρ)`, while the core
balls `B̄(z_p, ρ)` are pairwise disjoint (`dist z_p z_q > 4ρ - 2ρ = 2ρ`) and lie in `W`; the ratio
of the two ball volumes is `7³`. -/
theorem volume_cthickening_le_of_core_balls {U W : Set E3} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : Bornology.IsBounded U)
    (hcore : ∀ y ∈ U, ∃ z : E3, dist y z ≤ ρ ∧ closedBall z ρ ⊆ W) :
    volume (cthickening (2 * ρ) U) ≤ 343 * volume W := by
  classical
  rcases U.eq_empty_or_nonempty with hUe | hUne
  · simp [hUe]
  obtain ⟨P, hPU, -, hsep, hcov⟩ :=
    exists_finset_separated_cover hUne hU (by positivity : (0 : ℝ) < 4 * ρ)
  choose! z hz using hcore
  have hcov2 : cthickening (2 * ρ) U ⊆ ⋃ p ∈ P, closedBall p (7 * ρ) := by
    intro x hx
    have hx' := cthickening_subset_iUnion_closedBall_of_lt U
      (by positivity : (0 : ℝ) < 3 * ρ) (by linarith) hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx'
    obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp (hcov hy)
    refine Set.mem_iUnion₂.mpr ⟨p, hp, mem_closedBall.mpr ?_⟩
    have hxy' := mem_closedBall.mp hxy
    have hyp' := mem_closedBall.mp hyp
    calc dist x p ≤ dist x y + dist y p := dist_triangle _ _ _
      _ ≤ 3 * ρ + 4 * ρ := add_le_add hxy' hyp'
      _ = 7 * ρ := by ring
  have hdisj : (↑P : Set E3).PairwiseDisjoint fun p => closedBall (z p) ρ := by
    intro p hp q hq hpq
    apply closedBall_disjoint_closedBall
    have h1 := hsep p hp q hq hpq
    have h2 := (hz p (hPU hp)).1
    have h3 := (hz q (hPU hq)).1
    have h4 := dist_triangle4 p (z p) (z q) q
    have h5 := dist_comm (z q) q
    linarith
  have hsum : ∑ p ∈ P, volume (closedBall (z p) ρ) ≤ volume W := by
    rw [← measure_biUnion_finset hdisj (fun p _ => measurableSet_closedBall)]
    exact measure_mono (Set.iUnion₂_subset fun p hp => (hz p (hPU hp)).2)
  have hball : ∀ p : E3, volume (closedBall p (7 * ρ)) = 343 * volume (closedBall (z p) ρ) := by
    intro p
    rw [Measure.addHaar_closedBall_mul volume p (by norm_num : (0 : ℝ) ≤ 7) hρ.le,
      Measure.addHaar_closedBall_center volume (z p) ρ, finrank_euclideanSpace_fin]
    norm_num
  calc volume (cthickening (2 * ρ) U) ≤ volume (⋃ p ∈ P, closedBall p (7 * ρ)) :=
        measure_mono hcov2
    _ ≤ ∑ p ∈ P, volume (closedBall p (7 * ρ)) := measure_biUnion_finset_le _ _
    _ = ∑ p ∈ P, 343 * volume (closedBall (z p) ρ) := Finset.sum_congr rfl fun p _ => hball p
    _ = 343 * ∑ p ∈ P, volume (closedBall (z p) ρ) := (Finset.mul_sum _ _ _).symm
    _ ≤ 343 * volume W := by gcongr

/-- **From `x` in the coarse union to every `x`, at the packing cost `3³ = 27`.**

If the local-mass inequality holds at every centre of `W ⊇ U`, it holds at every centre at a
`27`-fold weaker gain: `U ∩ B(x, ρ)` is covered by at most `(1 + 2ρ/ρ)³ = 27` balls `B(p, ρ)` with
centres `p ∈ U ∩ B(x, ρ) ⊆ W` (`Kakeya.finite_and_card_le_of_separated`), and all `ρ`-balls have
the same volume. -/
theorem clause_forall_of_clause_on {U W : Set E3} {ρ : ℝ} (hρ : 0 < ρ) (hUW : U ⊆ W)
    (hU : Bornology.IsBounded U) (c : ℝ≥0∞)
    (h : ∀ x ∈ W, c * volume W * (volume (U ∩ ball x ρ) / volume (ball x ρ)) ≤ volume U)
    (x : E3) :
    (27 : ℝ≥0∞)⁻¹ * (c * volume W * (volume (U ∩ ball x ρ) / volume (ball x ρ))) ≤ volume U := by
  classical
  rcases (U ∩ ball x ρ).eq_empty_or_nonempty with hAe | hAne
  · simp [hAe]
  obtain ⟨P, hPA, hsep, hcov⟩ :=
    exists_maximal_separated (hU.subset Set.inter_subset_left) hρ
  have hPball : (↑P : Set E3) ⊆ ball x ρ := fun p hp => (hPA hp).2
  have hcard : (P.card : ℝ≥0∞) ≤ 27 := by
    have h1 := (finite_and_card_le_of_separated hρ hρ.le x hsep hPball).2
    rw [Set.ncard_coe_finset, finrank_euclideanSpace_fin] at h1
    have h27 : (1 + 2 * ρ / ρ) ^ 3 = (27 : ℝ) := by
      rw [mul_div_assoc, div_self hρ.ne']; norm_num
    rw [h27] at h1
    have h2 : P.card ≤ 27 := by exact_mod_cast h1
    exact_mod_cast h2
  have hAcov : U ∩ ball x ρ ⊆ ⋃ p ∈ P, (U ∩ ball p ρ) := by
    intro a ha
    obtain ⟨p, hp, hap⟩ := hcov a ha
    exact Set.mem_iUnion₂.mpr ⟨p, hp, ha.1, mem_ball.mpr hap⟩
  have hvb : ∀ p : E3, volume (ball p ρ) = volume (ball x ρ) := fun p => by
    rw [Measure.addHaar_ball_center, Measure.addHaar_ball_center volume x]
  have hsum : volume (U ∩ ball x ρ) ≤ ∑ p ∈ P, volume (U ∩ ball p ρ) :=
    (measure_mono hAcov).trans (measure_biUnion_finset_le _ _)
  have key : c * volume W * (volume (U ∩ ball x ρ) / volume (ball x ρ)) ≤ 27 * volume U := by
    calc c * volume W * (volume (U ∩ ball x ρ) / volume (ball x ρ))
        ≤ c * volume W * ((∑ p ∈ P, volume (U ∩ ball p ρ)) / volume (ball x ρ)) := by gcongr
      _ = ∑ p ∈ P, c * volume W * (volume (U ∩ ball p ρ) / volume (ball p ρ)) := by
          simp_rw [hvb, ENNReal.div_eq_inv_mul, Finset.mul_sum]
      _ ≤ ∑ p ∈ P, volume U := Finset.sum_le_sum fun p hp => h p (hUW (hPA hp).1)
      _ = P.card * volume U := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 27 * volume U := by gcongr
  calc (27 : ℝ≥0∞)⁻¹ * (c * volume W * (volume (U ∩ ball x ρ) / volume (ball x ρ)))
      ≤ 27⁻¹ * (27 * volume U) := by gcongr
    _ = volume U := ENNReal.inv_mul_cancel_left (by norm_num) ENNReal.ofNat_ne_top

/-! ### The one-scale bridge -/

/-- **The clause for the output of Lemma 5.11, from its exposed `2ρ`-thick outer shading.**

For a shaded factor family `G` whose outer bodies are `ρ`-tubes, whose inner carriers lie in the
unit ball, which satisfies the `boundVolumeAcrossTwoScales` estimate at the centres of the outer
union at loss `L`, and whose outer shading contains `W_j ∩ N_{2ρ}(Y'(T_i))` for every `i` in the
fibre of `j` (the conjunct exposed in `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate`),
the field's clause holds at **every** centre at gain `(9261 · L)⁻¹`:
`|N_{2ρ}(U')| ≤ 343 |⋃ outer|` by `volume_cthickening_le_of_core_balls` (the core point comes from
`Tube.carrier_eq` of the parent tube), and the passage from `x ∈ ⋃ outer` to all `x` costs `27`
(`clause_forall_of_clause_on`). -/
theorem localMassClause_of_thick_factorFamily {ι κ : Type*} {ρ : ℝ≥0} (hρ : 0 < ρ) (L : ℝ≥0)
    (G : ShadedFactorFamily E3 ι κ) (W : κ → Tube ρ E3)
    (houter : ∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = (W j).toConvexSpaceBody)
    (hball : ∀ i ∈ G.innerSet, (G.innerBody i).carrier ⊆ closedBall (0 : E3) 1)
    (hvol : ∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (L : ℝ≥0∞)⁻¹ * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ))
              / volume (ball x (ρ : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
    (hthick : ∀ j ∈ G.outerSet, ∀ i ∈ G.innerSet, G.parent i = j →
          (G.outerBody j).carrier ∩ cthickening (2 * (ρ : ℝ)) (G.innerBody i).shade
            ⊆ (G.outerBody j).shade) (x : E3) :
    ((9261 * L : ℝ≥0) : ℝ≥0∞)⁻¹ *
        (volume (cthickening (2 * (ρ : ℝ)) (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) *
          (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
            volume (ball x (ρ : ℝ)))) ≤
      volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade) := by
  classical
  set U : Set E3 := ⋃ i ∈ G.innerSet, (G.innerBody i).shade with hUdef
  set Wu : Set E3 := ⋃ j ∈ G.outerSet, (G.outerBody j).shade with hWdef
  have hρr : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hUW : U ⊆ Wu := by
    refine Set.iUnion₂_subset fun i hi => ?_
    exact (G.shade_subset_parent i hi).trans
      (Set.subset_iUnion₂_of_subset (G.parent i) (G.parent_mem i hi) subset_rfl)
  have hUb : Bornology.IsBounded U := by
    refine (isBounded_closedBall (x := (0 : E3)) (r := 1)).subset
      (Set.iUnion₂_subset fun i hi => ?_)
    exact (G.innerBody i).shade_subset.trans (hball i hi)
  -- the core ball: `Tube.carrier_eq` of the parent tube, then the exposed thickness conjunct
  have hcore : ∀ y ∈ U, ∃ z : E3, dist y z ≤ ρ ∧ closedBall z ρ ⊆ Wu := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
    have hj := G.parent_mem i hi
    have hcar : (G.outerBody (G.parent i)).carrier = (W (G.parent i)).carrier :=
      congrArg ConvexSpaceBody.carrier (houter _ hj)
    have hyW : y ∈ (W (G.parent i)).carrier := by
      rw [← hcar]
      exact (G.inner_le_parent i hi) ((G.innerBody i).shade_subset hyi)
    rw [(W (G.parent i)).carrier_eq] at hyW
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hyW
    refine ⟨z, mem_closedBall.mp hyz, ?_⟩
    have hzW : closedBall z ρ ⊆ (G.outerBody (G.parent i)).carrier := by
      rw [hcar, (W (G.parent i)).carrier_eq]
      exact Set.subset_iUnion₂_of_subset z hz subset_rfl
    have hzth : closedBall z ρ ⊆ cthickening (2 * (ρ : ℝ)) (G.innerBody i).shade := by
      refine (closedBall_subset_closedBall' ?_).trans (closedBall_subset_cthickening hyi _)
      have := mem_closedBall.mp hyz
      rw [dist_comm] at this
      linarith
    refine ((Set.subset_inter hzW hzth).trans (hthick _ hj i hi rfl)).trans ?_
    exact Set.subset_iUnion₂_of_subset (G.parent i) hj subset_rfl
  have hN := volume_cthickening_le_of_core_balls hρr hUb hcore
  have hall := clause_forall_of_clause_on hρr hUW hUb (L : ℝ≥0∞)⁻¹ hvol x
  have h9261 : (9261 : ℝ≥0∞)⁻¹ * 343 = 27⁻¹ := by
    rw [show (9261 : ℝ≥0∞) = 27 * 343 by norm_num,
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl ENNReal.ofNat_ne_top), mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top, mul_one]
  have hcoe : (((9261 * L : ℝ≥0) : ℝ≥0∞))⁻¹ = (9261 : ℝ≥0∞)⁻¹ * (L : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by simp))]
    norm_num
  calc ((9261 * L : ℝ≥0) : ℝ≥0∞)⁻¹ *
        (volume (cthickening (2 * (ρ : ℝ)) U) * (volume (U ∩ ball x (ρ : ℝ)) /
          volume (ball x (ρ : ℝ))))
      ≤ (9261 : ℝ≥0∞)⁻¹ * (L : ℝ≥0∞)⁻¹ *
        (343 * volume Wu * (volume (U ∩ ball x (ρ : ℝ)) / volume (ball x (ρ : ℝ)))) := by
        rw [hcoe]; gcongr
    _ = 27⁻¹ * ((L : ℝ≥0∞)⁻¹ * volume Wu *
        (volume (U ∩ ball x (ρ : ℝ)) / volume (ball x (ρ : ℝ)))) := by
        rw [← h9261]; ring
    _ ≤ volume U := hall

/-- **The one-scale bridge.** From GWZ Lemma 5.11 at the grid index `k`
(`ShadedBody.exists_rhoTubesSection9_gridScale`, with its exposed `2ρ`-thick outer shading), for a
family `(s, T)` of shaded `δ`-tubes in the unit ball with a parent map `p` into the `ρ_k`-tubes
`W`: a refinement `(s', T')` — an index selection with the shading cut, tubes unchanged, an
`L⁻¹`-refinement — satisfying the field's clause at index `k` for **every** `x`, at gain
`(9261 · L)⁻¹`, `L = ShadedBody.rhoTubesSection9Loss 3 |s| δ`.

No density hypothesis is needed: Lemma 5.11 is applied at the density parameter `lam = 0`, whose
fullness conclusion is discarded. -/
theorem localMassAt_clause_of_rhoTubesSection9 {ι κ : Type*} {δ : ℝ≥0} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {N k : ℕ} (hk : k ≤ N) {s : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E3) (W : κ → Tube (Tube.gridScale δ N k) E3) (p : ι → κ)
    (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E3) 1) :
    ∃ (s' : Finset ι) (T' : ι → ShadedTube δ E3), s' ⊆ s ∧
      (∀ i, (T' i).toTube = (T i).toTube) ∧
      (∀ i, (T' i).shade ⊆ (T i).shade) ∧
      IsCRefinement s' (fun i ↦ (T' i).toShadedBody) s (fun i ↦ (T i).toShadedBody)
        (rhoTubesSection9Loss 3 s.card δ)⁻¹ ∧
      LocalMassClauseAt δ N k
        ((9261 * rhoTubesSection9Loss 3 s.card δ : ℝ≥0) : ℝ≥0∞)⁻¹ s' T' := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    refine ⟨∅, T, subset_rfl, fun _ => rfl, fun _ => subset_rfl, ⟨⟨subset_rfl, ?_⟩, ?_⟩, ?_⟩
    · intro i hi
      exact absurd hi (Finset.notMem_empty i)
    · simp
    · intro x
      simp
  have hs0 : ∑ i ∈ s, volume (T i).carrier ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hs
    refine ne_of_gt (lt_of_lt_of_le ?_
      (Finset.single_le_sum (f := fun i => volume (T i).carrier) (fun _ _ => by positivity) hi₀))
    have h := Tube.le_volume (T i₀).toTube
    have hc : (0 : ℝ≥0∞) <
        ((Tube.le_volume.c (Module.finrank ℝ E3) : ℝ≥0) : ℝ≥0∞) *
          (δ : ℝ≥0∞) ^ (Module.finrank ℝ E3 - 1) :=
      ENNReal.mul_pos (ne_of_gt (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)))
        (ne_of_gt (ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) _))
    exact lt_of_lt_of_le hc (by simpa using h)
  obtain ⟨G, -, -, -, h4, h5, -, -, href, -, -, hvol, hthick⟩ :=
    exists_rhoTubesSection9_gridScale (E := E3) (Cd := 1) (lam := 0) hδ hδ1 one_ne_zero hk
      T W p hmaps hle hball hs0 (fun i _ => by simp)
  have hfr : Module.finrank ℝ E3 = 3 := by simp
  rw [hfr] at href hvol
  have hsub : G.innerSet ⊆ s := href.1.1
  have hcarG : ∀ i ∈ G.innerSet, (G.innerBody i).carrier = (T i).carrier := fun i hi =>
    congrArg ConvexSpaceBody.carrier (h5 i (hsub hi))
  let T' : ι → ShadedTube δ E3 := fun i =>
    if hi : i ∈ G.innerSet then
      { toTube := (T i).toTube
        shade := (G.innerBody i).shade
        measurableSet_shade := (G.innerBody i).measurableSet_shade
        shade_subset := by
          rw [← hcarG i hi]
          exact (G.innerBody i).shade_subset }
    else T i
  have hT'shade : ∀ i ∈ G.innerSet, (T' i).shade = (G.innerBody i).shade := fun i hi => by
    simp [T', hi]
  have hU : (⋃ i ∈ G.innerSet, (T' i).toShadedBody.shade) =
      ⋃ i ∈ G.innerSet, (G.innerBody i).shade :=
    Set.iUnion₂_congr fun i hi => hT'shade i hi
  refine ⟨G.innerSet, T', hsub, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · by_cases hi : i ∈ G.innerSet <;> simp [T', hi]
  · by_cases hi : i ∈ G.innerSet
    · rw [hT'shade i hi]
      exact (href.1.2 i hi).2
    · simp [T', hi]
  · refine ⟨⟨hsub, fun i hi => ⟨?_, ?_⟩⟩, ?_⟩
    · simp [T', hi]
    · change (T' i).shade ⊆ (T i).shade
      rw [hT'shade i hi]
      exact (href.1.2 i hi).2
    · refine href.2.trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun i hi => by rw [show (T' i).toShadedBody.shade = (T' i).shade
        from rfl, hT'shade i hi]
  · intro x
    rw [hU]
    exact localMassClause_of_thick_factorFamily (Tube.gridScale_pos hδ N k) _ G W h4
      (fun i hi => (hcarG i hi).symm ▸ hball i (hsub hi)) hvol hthick x

/-- **The one-scale bridge for a family carrying a uniform hierarchy** (GWZ Definition 2.1):
`localMassAt_clause_of_rhoTubesSection9` with the `ρ_k`-tubes the nodes `𝒰.cover.tube k` and the
parent map the hierarchy's assignment `𝒰.cover.assign k`. -/
theorem localMassAt_clause_of_uniformTubeSet {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {N : ℕ} {C : ℝ≥0} {s : Finset ι} {T : ι → ShadedTube δ E3}
    (𝒰 : Tube.UniformTubeSet s (fun i => (T i).toTube) N C) {k : ℕ} (hk : k ≤ N)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E3) 1) :
    ∃ (s' : Finset ι) (T' : ι → ShadedTube δ E3), s' ⊆ s ∧
      (∀ i, (T' i).toTube = (T i).toTube) ∧
      (∀ i, (T' i).shade ⊆ (T i).shade) ∧
      IsCRefinement s' (fun i ↦ (T' i).toShadedBody) s (fun i ↦ (T i).toShadedBody)
        (rhoTubesSection9Loss 3 s.card δ)⁻¹ ∧
      LocalMassClauseAt δ N k
        ((9261 * rhoTubesSection9Loss 3 s.card δ : ℝ≥0) : ℝ≥0∞)⁻¹ s' T' :=
  localMassAt_clause_of_rhoTubesSection9 hδ hδ1 hk T (𝒰.cover.tube k) (𝒰.cover.assign k)
    (𝒰.cover.assign_mem k hk) (fun i hi => 𝒰.cover.le_tube_assign k hk i hi) hball

/-- **The one-scale bridge for a shaded-uniform family** (GWZ Definition 2.2), read off the
underlying tube hierarchy `𝒱.tubeUniform`. -/
theorem localMassAt_clause_of_shadedUniformTubeSet {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {N : ℕ} {C : ℝ≥0} {s : Finset ι} {T : ι → ShadedTube δ E3}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E3) 1) :
    ∃ (s' : Finset ι) (T' : ι → ShadedTube δ E3), s' ⊆ s ∧
      (∀ i, (T' i).toTube = (T i).toTube) ∧
      (∀ i, (T' i).shade ⊆ (T i).shade) ∧
      IsCRefinement s' (fun i ↦ (T' i).toShadedBody) s (fun i ↦ (T i).toShadedBody)
        (rhoTubesSection9Loss 3 s.card δ)⁻¹ ∧
      LocalMassClauseAt δ N k
        ((9261 * rhoTubesSection9Loss 3 s.card δ : ℝ≥0) : ℝ≥0∞)⁻¹ s' T' :=
  localMassAt_clause_of_uniformTubeSet hδ hδ1 𝒱.tubeUniform hk hball

/-! ### Interpolation between grid scales -/

/-- **Interpolation.** The clause at grid index `j` at gain `g` implies the
clause at every finer index `k ≥ j` at gain `g · (ρ_k/ρ_j)³`: `N_{2ρ_k}(U) ⊆ N_{2ρ_j}(U)`,
`U ∩ B(x, ρ_k) ⊆ U ∩ B(x, ρ_j)`, and `|B(x, ρ_k)| = (ρ_k/ρ_j)³ |B(x, ρ_j)|`. -/
theorem localMassAt_clause_mono_index {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {N j k : ℕ} (hjk : j ≤ k) {g : ℝ≥0∞} {s : Finset ι} {T : ι → ShadedTube δ E3}
    (h : LocalMassClauseAt δ N j g s T) :
    LocalMassClauseAt δ N k
      (g * ((Tube.gridScale δ N k / Tube.gridScale δ N j : ℝ≥0) : ℝ≥0∞) ^ 3) s T := by
  intro x
  set U : Set E3 := ⋃ i ∈ s, (T i).toShadedBody.shade with hU
  set ρ : ℝ≥0 := Tube.gridScale δ N k with hρ
  set σ : ℝ≥0 := Tube.gridScale δ N j with hσ
  have hρpos : 0 < ρ := Tube.gridScale_pos hδ N k
  have hσpos : 0 < σ := Tube.gridScale_pos hδ N j
  have hρσ : ρ ≤ σ := Tube.gridScale_antitone hδ hδ1 N hjk
  set r : ℝ≥0 := ρ / σ with hrdef
  have hr : (ρ : ℝ) = (r : ℝ) * (σ : ℝ) := by
    rw [hrdef, NNReal.coe_div, div_mul_cancel₀]
    exact_mod_cast hσpos.ne'
  have hvb : volume (ball x (ρ : ℝ)) = (r : ℝ≥0∞) ^ 3 * volume (ball x (σ : ℝ)) := by
    rw [hr, Measure.addHaar_ball_mul volume x r.coe_nonneg, finrank_euclideanSpace_fin,
      Measure.addHaar_ball_center volume x, ENNReal.ofReal_pow r.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
  have hr0 : (r : ℝ≥0∞) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (div_pos hρpos hσpos).ne'
  have hrtop : (r : ℝ≥0∞) ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hρσr : (ρ : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hρσ
  have hN : cthickening (2 * (ρ : ℝ)) U ⊆ cthickening (2 * (σ : ℝ)) U :=
    cthickening_mono (by linarith) U
  have hB : U ∩ ball x (ρ : ℝ) ⊆ U ∩ ball x (σ : ℝ) :=
    Set.inter_subset_inter_right _ (ball_subset_ball hρσr)
  have hx := h x
  rw [ENNReal.div_eq_inv_mul] at hx
  calc g * ((r : ℝ≥0∞) ^ 3) *
        (volume (cthickening (2 * (ρ : ℝ)) U) *
          (volume (U ∩ ball x (ρ : ℝ)) / volume (ball x (ρ : ℝ))))
      = g * (volume (cthickening (2 * (ρ : ℝ)) U) *
          ((volume (ball x (σ : ℝ)))⁻¹ * volume (U ∩ ball x (ρ : ℝ)))) *
          ((r : ℝ≥0∞) ^ 3 * ((r : ℝ≥0∞) ^ 3)⁻¹) := by
        rw [hvb, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hr0) (Or.inl hrtop)]
        ring
    _ = g * (volume (cthickening (2 * (ρ : ℝ)) U) *
          ((volume (ball x (σ : ℝ)))⁻¹ * volume (U ∩ ball x (ρ : ℝ)))) := by
        rw [ENNReal.mul_inv_cancel hr0 hrtop, mul_one]
    _ ≤ g * (volume (cthickening (2 * (σ : ℝ)) U) *
          ((volume (ball x (σ : ℝ)))⁻¹ * volume (U ∩ ball x (σ : ℝ)))) := by
        gcongr
    _ ≤ volume U := hx

/-- **The interpolation cost in the exponent currency.** Along the grid `ρ_k = δ^{k/N}`, if the
index gap satisfies `(k - j)/N ≤ η/s` then `(ρ_k/ρ_j)³ = δ^{3(k-j)/N} ≥ δ^{3η/s}`. -/
theorem rpow_le_gridScale_div_pow_three {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N j k : ℕ}
    {η s : ℝ} (hgap : ((k : ℝ) - j) / N ≤ η / s) :
    δ ^ (3 * η / s) ≤ (Tube.gridScale δ N k / Tube.gridScale δ N j) ^ 3 := by
  rw [Tube.gridScale_div_gridScale hδ, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  apply NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1
  have : -(((j : ℝ) - k) / N) * ((3 : ℕ) : ℝ) = 3 * (((k : ℝ) - j) / N) := by push_cast; ring
  rw [this, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hgap (by norm_num)

/-- **Interpolation with the cost read in the exponent currency** ((c)): the clause
at index `j` at gain `g` gives the clause at every `k ≥ j` with `(k - j)/N ≤ η/s` at gain
`g · δ^{3η/s}`. Hence every grid index follows from the instances at `⌈s/η⌉ + 1` chained indices
spaced `⌊ηN/s⌋` apart, each costing one factor `δ^{3η/s}`. -/
theorem localMassAt_clause_mono_index_rpow {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {N j k : ℕ} (hjk : j ≤ k) {η s : ℝ} (hgap : ((k : ℝ) - j) / N ≤ η / s)
    {g : ℝ≥0∞} {s' : Finset ι} {T : ι → ShadedTube δ E3}
    (h : LocalMassClauseAt δ N j g s' T) :
    LocalMassClauseAt δ N k (g * ((δ ^ (3 * η / s) : ℝ≥0) : ℝ≥0∞)) s' T := by
  refine (localMassAt_clause_mono_index hδ hδ1 hjk h).mono_gain ?_
  rw [← ENNReal.coe_pow]
  exact mul_le_mul_right (ENNReal.coe_le_coe.mpr (rpow_le_gridScale_div_pow_three hδ hδ1 hgap)) _

end Kakeya.VeryNotSticky
