/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupLocalMassFinal
public import Kakeya.DimensionThree.MainLemma2.BallJoint

/-!
# The island cut of the §9.3 setup: deleting the light `r₁`-pieces

GWZ §9 (the paragraph after (89)) divides the shaded union into boundedly overlapping balls `B`
of radius `r₁ = δ^{ε_scal}` and keeps only the balls in which the shading is full enough:
*"We let `𝔅` be the set of balls `B` with `λ(𝕋_B, Y_B) ⪆ λ(𝕋, Y)`. Then we refine `Y` by
removing the parts of `Y(T)` that are not in the balls of `𝔅`. Again this is a `⪆ 1`
refinement."* This file performs that cut on a **bare family** `(s', T')` — before any
configuration exists — so that the side-data construction (`Kakeya.VeryNotSticky.SideDataResidue`)
can consume it together with the local-mass refinement
`Kakeya.VeryNotSticky.BandUniformRefinementLocalMassSlack` of residue 1.

* `Kakeya.VeryNotSticky.exists_ballCover_family` — the `r₁`-ball cover of a bare family: the
  proof of `Kakeya.VeryNotSticky.exists_ballCover` (item (C2) of Configuration `hyp:ml2setup`)
  generalised from a configuration `cfg` to an arbitrary shaded family in the unit ball, at an
  arbitrary radius `r₁ > 0`, with one further conjunct: every centre is a point of the shaded
  union (the centres are the points of a maximal separated net of that union). * `Kakeya.VeryNotSticky.eventually_exists_lightPieceCut` — **the island cut.** Cover the shaded
  union `U'` of `(s', T')` at radius `r₁ = δ^{ε_scal}`; call a piece `P_B` *light* when
  `|P_B ∩ U'| < 2δ^{2η}|B(0, δ)|`, and let `Light` be the union of the light pieces. For all small
  `δ`, deleting `Light` from every shading
  (i) leaves a cover of the cut family by the heavy pieces alone, each heavy piece carrying
      `≥ 2δ^{2η}|B(0,δ)|` of the cut shaded union — exported with the full geometry of the
      ball cover (pieces in `B(ctr B, r₁/16)`, every piece measurable, every heavy piece meeting
      the cut union), i.e. the eight cover hypotheses of
      `Kakeya.VeryNotSticky.exists_ballDataCore_of_cover`;
  (ii) keeps the per-tube floor at the producer's exponent, `δ^{2η}|T| ≤ |Y'(i) \ Light|`
      (from the doubled floor `2δ^{2η}|T| ≤ |Y'(i)|` of the slack interface);
  (iii) retains half of the total shading mass;
  (iv) keeps GWZ (87) — `Kakeya.VeryNotSticky.LocalMassAt` — at exponent `η` for the cut family,
      from exponent `η/2` for the input.

## The arithmetic

With `D = Kakeya.VeryNotSticky.ballCoverConstant` and `κ = |B(0, 1)|`:

* the balls `B(ctr B, r₁)` lie in `B(0, 2)` and overlap at most `D` times, so
  `#𝔅₀ · |B(0, r₁)| ≤ D · |B(0, 2)|`, i.e. `#𝔅₀ · δ^{3 ε_scal} κ ≤ 8 D κ`
  (`MeasureTheory.sum_measure_le_mul_measure_of_card_le`, `MeasureTheory.Measure.addHaar_ball`);
* the total loss is `|U' ∩ Light| ≤ #𝔅₀ · 2δ^{2η}|B(0, δ)| = #𝔅₀ · 2δ^{2η} δ³ κ`, hence
  `≤ δ^{2η} · δ² · (16 D κ δ^{1 - 3ε_scal})`;
* the threshold `16 D κ δ^{1 - 3 ε_scal} ≤ c₃` (`c₃ = Tube.le_volume.c 3`, so `c₃ δ² ≤ |T|` by
  `Tube.le_volume`) holds for all small `δ` because `3 ε_scal < 1`
  (`Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const`); so the loss is at most
  `δ^{2η}|T|` for every tube of the family, which is half of every tube's shading;
* (ii) and (iii) follow by `|Y'| = |Y' \ Light| + |Y' ∩ Light|`; for (iv), `|U'| ≤ |U''| + loss
  ≤ 2|U''|`, so `Kakeya.VeryNotSticky.LocalMassClauseAt.transport` at `Λ = 2` turns the gain
  `δ^{η/2}` into `2⁻¹ δ^{η/2} ≥ δ^η` once `2δ^{η/2} ≤ 1`.

Nothing here uses the uniform hierarchy, the tube count or the index type beyond `Type u`; the
cut is a `⪆ 1` refinement in the sense of GWZ, with the retention constant `1/2` in place of
`1 - δ^{η/2}`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal
open Produce

universe u

set_option linter.unusedVariables false in
/-- **The `r₁`-ball cover with its subordinate partition, for a bare family** (blueprint
`hyp:ml2setup` (C2), via `lem:separatedNetCover` and `lem:subordinatePartition`).

The proof of `Kakeya.VeryNotSticky.exists_ballCover` with the configuration replaced by an
arbitrary family `(s, T)` of shaded `δ`-tubes in the unit ball and the radius `cfg.r₁` by an
arbitrary `r₁ > 0`. The conclusions are those of the original — non-empty `𝔅`, pieces inside
`B(ctr B, r₁/16)` and inside `B̄(ctr B, r₁)`, pairwise disjoint and measurable, covering every
shading, `ballCoverConstant`-bounded overlap of the balls `B(ctr B, r₁)`, every piece meeting the
shaded union — together with one further clause the construction gives for free: **every centre
lies in the shaded union**, because the centres are the points of a maximal `r₁/16`-separated
subset of it (`Kakeya.exists_maximal_separated`). That clause is what places every ball
`B(ctr B, r₁)` inside `B(0, 1 + r₁)`, hence bounds the number of balls.

The binder `hδ : 0 < δ` is the statement of  (it mirrors `cfg.hδ`, from
which the original derives `0 < cfg.r₁`); the proof needs only `hr₁`, so the unused-variable
linter is silenced for this declaration rather than the interface changed. -/
theorem exists_ballCover_family {δ : NNReal} (hδ : 0 < δ) {r₁ : NNReal} (hr₁ : 0 < r₁)
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hne : (⋃ i ∈ s, (T i).shade).Nonempty) :
    ∃ (bι : Type u) (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
      (P : bι → Set (EuclideanSpace ℝ (Fin 3))),
      bs.Nonempty ∧
      (∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) ((r₁ : ℝ) / 16)) ∧
      (∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) (r₁ : ℝ)) ∧
      (bs : Set bι).PairwiseDisjoint P ∧ (∀ B, MeasurableSet (P B)) ∧
      (∀ i ∈ s, (T i).shade ⊆ ⋃ B ∈ bs, P B) ∧
      (∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
          (∀ B ∈ t, x ∈ Metric.ball (ctr B) (r₁ : ℝ)) → t.card ≤ ballCoverConstant) ∧
      (∀ B ∈ bs, (P B ∩ ⋃ i ∈ s, (T i).shade).Nonempty) ∧
      (∀ B ∈ bs, ctr B ∈ ⋃ i ∈ s, (T i).shade) := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ s, (T i).shade with hSdef
  have hr₁pos : (0 : ℝ) < (r₁ : ℝ) := by exact_mod_cast hr₁
  have hr : (0 : ℝ) < (r₁ : ℝ) / 16 := by positivity
  have hSbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 3))) (r := 1)).subset ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact hball i hi ((T i).shade_subset hxi)
  obtain ⟨N, hNS, hsep, hmax⟩ := Kakeya.exists_maximal_separated hSbdd hr
  set bs₀ : Finset (ULift.{u} (EuclideanSpace ℝ (Fin 3))) :=
    N.map ⟨ULift.up, ULift.up_injective⟩ with hbs₀
  have hmem₀ : ∀ B : ULift.{u} (EuclideanSpace ℝ (Fin 3)), B ∈ bs₀ ↔ ULift.down B ∈ N := by
    intro B
    simp [hbs₀]
  obtain ⟨P₀, hP₀sub, hP₀meas, hP₀disj, hP₀union⟩ :=
    Kakeya.exists_subordinatePartition (E := EuclideanSpace ℝ (Fin 3)) bs₀
      (fun B => ball (ULift.down B) ((r₁ : ℝ) / 16)) (fun B _ => measurableSet_ball)
  -- make the partition measurable at *every* index, by zeroing it off the cover
  set P : ULift.{u} (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)) :=
    fun B => if B ∈ bs₀ then P₀ B else ∅ with hPdef
  have hPeq : ∀ B ∈ bs₀, P B = P₀ B := by
    intro B hB; simp [hPdef, hB]
  have hPsub : ∀ B ∈ bs₀, P B ⊆ ball (ULift.down B) ((r₁ : ℝ) / 16) := by
    intro B hB; rw [hPeq B hB]; exact hP₀sub B hB
  have hPmeas : ∀ B, MeasurableSet (P B) := by
    intro B
    by_cases hB : B ∈ bs₀
    · rw [hPeq B hB]; exact hP₀meas B hB
    · simp [hPdef, hB]
  have hPdisj : (bs₀ : Set (ULift.{u} (EuclideanSpace ℝ (Fin 3)))).PairwiseDisjoint P := by
    intro a ha b hb hab
    have ha' : a ∈ bs₀ := by simpa using ha
    have hb' : b ∈ bs₀ := by simpa using hb
    change Disjoint (P a) (P b)
    rw [hPeq a ha', hPeq b hb']
    exact hP₀disj ha hb hab
  have hPunion : ⋃ B ∈ bs₀, P B = ⋃ B ∈ bs₀, ball (ULift.down B) ((r₁ : ℝ) / 16) := by
    rw [← hP₀union]
    refine Set.iUnion₂_congr ?_
    intro B hB
    exact hPeq B (by simpa using hB)
  set bs : Finset (ULift.{u} (EuclideanSpace ℝ (Fin 3))) :=
    bs₀.filter (fun B => (P B ∩ S).Nonempty) with hbs
  have hbssub : bs ⊆ bs₀ := Finset.filter_subset _ _
  -- the cover of `S` by the retained pieces
  have hScov : S ⊆ ⋃ B ∈ bs, P B := by
    intro x hx
    have hx₀ : x ∈ ⋃ B ∈ bs₀, ball (ULift.down B) ((r₁ : ℝ) / 16) := by
      obtain ⟨y, hy, hxy⟩ := hmax x hx
      exact Set.mem_biUnion ((hmem₀ ⟨y⟩).2 hy) (by simpa [Metric.mem_ball] using hxy)
    rw [← hPunion] at hx₀
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp hx₀
    exact Set.mem_biUnion (Finset.mem_filter.2 ⟨hB, ⟨x, hxB, hx⟩⟩) hxB
  refine ⟨ULift.{u} (EuclideanSpace ℝ (Fin 3)), bs, ULift.down, P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- `bs` is non-empty
    obtain ⟨x, hx⟩ := hne
    have hxS : x ∈ S := hx
    obtain ⟨B, hB, _⟩ := Set.mem_iUnion₂.mp (hScov hxS)
    exact ⟨B, hB⟩
  · exact fun B hB => hPsub B (hbssub hB)
  · intro B hB
    exact (hPsub B (hbssub hB)).trans
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)))
  · exact hPdisj.subset (by exact_mod_cast hbssub)
  · exact hPmeas
  · intro i hi
    exact (Set.subset_biUnion_of_mem (u := fun i => (T i).shade) hi).trans hScov
  · -- bounded overlap
    intro x t hts hball
    have hsepN : ∀ y ∈ (↑(t.image ULift.down) : Set (EuclideanSpace ℝ (Fin 3))),
        ∀ z ∈ (↑(t.image ULift.down) : Set (EuclideanSpace ℝ (Fin 3))), y ≠ z →
          (r₁ : ℝ) / 16 ≤ dist y z := by
      intro y hy z hz hyz
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy hz
      obtain ⟨B, hB, rfl⟩ := hy
      obtain ⟨B', hB', rfl⟩ := hz
      exact hsep _ ((hmem₀ B).1 (hbssub (hts hB))) _ ((hmem₀ B').1 (hbssub (hts hB'))) hyz
    have hball' : (↑(t.image ULift.down) : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        ball x (r₁ : ℝ) := by
      intro y hy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
      obtain ⟨B, hB, rfl⟩ := hy
      have := hball B hB
      rw [Metric.mem_ball] at this ⊢
      rw [dist_comm]
      exact this
    have hcard := (Kakeya.finite_and_card_le_of_separated (E := EuclideanSpace ℝ (Fin 3))
      hr hr₁pos.le x hsepN hball').2
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
      simp
    rw [Set.ncard_coe_finset, hfr] at hcard
    have harith : (1 + 2 * (r₁ : ℝ) / ((r₁ : ℝ) / 16)) ^ 3 = 35937 := by
      have h32 : (2 * (r₁ : ℝ) / ((r₁ : ℝ) / 16)) = 32 := by
        field_simp
        ring
      rw [h32]; norm_num
    rw [harith] at hcard
    have hcard' : t.card = (t.image ULift.down).card := by
      rw [Finset.card_image_of_injective _ (fun a b h => by
        cases a; cases b; simpa using h)]
    rw [hcard'] at *
    have hfin : ((t.image ULift.down).card : ℝ) ≤ (35937 : ℝ) := hcard
    exact_mod_cast hfin
  · intro B hB
    exact (Finset.mem_filter.1 hB).2
  · -- every centre is a net point, hence a point of the shaded union
    intro B hB
    exact hNS ((hmem₀ B).1 (hbssub hB))

/-- **The island cut** (GWZ §9, the `⪆ 1` refinement *"removing the parts of `Y(T)` that are not
in the balls of `𝔅`"*; ).

For all small `δ` and every family `(s', T')` of shaded `δ`-tubes in the unit ball with the
doubled per-tube floor `2δ^{2η}|T| ≤ |Y'(i)|`, the tube count `1 ≤ δ|s'|` and GWZ (87) at exponent
`η/2` (the four clauses of `Kakeya.VeryNotSticky.BandUniformRefinementLocalMassSlack` the cut
needs), there is a measurable set `Light` — the union of the light pieces of the
`δ^{ε_scal}`-ball cover of the shaded union — such that
(i) the heavy pieces alone cover every cut shading `Y'(i) \ Light`, with the cover's geometry
    (pieces in `B̄(ctr B, δ^{ε_scal})`, disjoint, measurable, `ballCoverConstant`-bounded overlap
    of the balls) and every heavy piece carrying `≥ 2δ^{2η}|B(0, δ)|` of the cut shaded union;
    together with the three further clauses of `Kakeya.VeryNotSticky.exists_ballCover_family`'s
    cover that the segment producer `Kakeya.VeryNotSticky.exists_ballDataCore_of_cover` reads —
    pieces inside the open balls `B(ctr B, δ^{ε_scal}/16)`, measurability of *every* piece
    `P B` (not only the heavy ones), and every heavy piece meeting the cut shaded union — so
    that (i) exports exactly its eight cover hypotheses, for the cut family;
(ii) the per-tube floor survives at the producer's exponent: `δ^{2η}|T| ≤ |Y'(i) \ Light|`;
(iii) at least half of the total shading mass is retained;
(iv) GWZ (87) holds at exponent `η` for the cut family
     `fun i ↦ Kakeya.VeryNotSticky.deleteShadeTube (T' i) Light hL`.

Only `0 < η`, `0 < ε_scal` and `3 ε_scal < 1` are needed (`Kakeya.VeryNotSticky.CaseParams.slab`
gives `ε_scal < 1/24`). -/
theorem eventually_exists_lightPieceCut {η exscal : ℝ} (hη : 0 < η) (hexscal : 0 < exscal)
    (hex3 : 3 * exscal < 1) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s' : Finset ι) (T' : ι → ShadedTube δ E3),
        (∀ i ∈ s', (T' i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s', 2 * (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤ volume (T' i).shade) →
        (1 : ENNReal) ≤ (δ : ENNReal) * (s'.card : ENNReal) →
        LocalMassAt δ (η / 2) s' T' →
        ∃ (Light : Set E3) (hL : MeasurableSet Light)
          (bι : Type u) (bs : Finset bι) (ctr : bι → E3) (P : bι → Set E3),
          -- (i) the cover of the CUT family, every piece heavy
          bs.Nonempty ∧
          (∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) ((δ ^ exscal : NNReal) : ℝ)) ∧
          (bs : Set bι).PairwiseDisjoint P ∧ (∀ B ∈ bs, MeasurableSet (P B)) ∧
          (∀ i ∈ s', (T' i).shade \ Light ⊆ ⋃ B ∈ bs, P B) ∧
          (∀ (x : E3) (t : Finset bι), t ⊆ bs →
              (∀ B ∈ t, x ∈ Metric.ball (ctr B) ((δ ^ exscal : NNReal) : ℝ)) →
              t.card ≤ ballCoverConstant) ∧
          (∀ B ∈ bs, 2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ)) ≤
              volume (P B ∩ ⋃ i ∈ s', ((T' i).shade \ Light))) ∧
          -- (i′) the remaining cover clauses of `exists_ballCover_family`, so that the heavy
          -- cover feeds `exists_ballDataCore_of_cover` unmodified: pieces inside
          -- `B(ctr B, δ^{ε_scal}/16)`, every piece measurable, every heavy piece meets the
          -- cut shaded union
          (∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) (((δ ^ exscal : NNReal) : ℝ) / 16)) ∧
          (∀ B, MeasurableSet (P B)) ∧
          (∀ B ∈ bs, (P B ∩ ⋃ i ∈ s', ((T' i).shade \ Light)).Nonempty) ∧
          -- (ii) the per-tube floor survives at the producer's exponent
          (∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤
              volume ((T' i).shade \ Light)) ∧
          -- (iii) mass retention 1/2
          (2 : ENNReal)⁻¹ * ∑ i ∈ s', volume (T' i).shade ≤
              ∑ i ∈ s', volume ((T' i).shade \ Light) ∧
          -- (iv) GWZ (87) at exponent η for the cut family
          LocalMassAt δ η s' (fun i ↦ deleteShadeTube (T' i) Light hL) := by
  classical
  -- the dimensional constants
  set κ : ENNReal := volume (Metric.ball (0 : E3) 1) with hκ
  have hκtop : κ ≠ ⊤ := measure_ball_lt_top.ne
  have hc₃pos : 0 < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
  have hν : 0 < 1 - 3 * exscal := by linarith
  have hfr : Module.finrank ℝ E3 = 3 := by simp
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' NNReal),
    eventually_nnreal_mul_rpow_le_const (16 * (ballCoverConstant : NNReal) * κ.toNNReal)
      (Tube.le_volume.c 3) hc₃pos hν,
    eventually_nnreal_mul_rpow_le_const 2 1 one_pos (half_pos hη)] with δ hδ hthr hhalf
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s' T' hball hfloor hcard hlm
  -- basic facts about `δ`
  have hδE0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hd2η_pos : 0 < (δ : ENNReal) ^ (2 * η) := ENNReal.rpow_pos (by exact_mod_cast hδ0) hδEtop
  have hd2η_top : (δ : ENNReal) ^ (2 * η) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hδEtop
  -- the radius `r₁ = δ^{exscal}`
  set r₁ : NNReal := δ ^ exscal with hr₁def
  have hr₁pos : 0 < r₁ := NNReal.rpow_pos hδ0
  have hr₁le1 : r₁ ≤ 1 := NNReal.rpow_le_one hδ1.le hexscal.le
  -- the shaded union
  set U : Set E3 := ⋃ i ∈ s', (T' i).shade with hU
  have hUsub : U ⊆ Metric.closedBall 0 1 := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact hball i hi ((T' i).shade_subset hxi)
  -- `s'` is non-empty
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with h | h
    · rw [h] at hcard; simp at hcard
    · exact h
  obtain ⟨i₀, hi₀⟩ := hs'ne
  -- carriers: the volume floor `c₃ δ² ≤ |T|` and finiteness
  have hcar : ∀ i, ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ (2 : ℕ) ≤
      volume (T' i).carrier := by
    intro i
    have h := Tube.le_volume (T' i).toTube
    rw [hfr] at h
    exact h
  have hcartop : ∀ i ∈ s', volume (T' i).carrier ≠ ⊤ := fun i hi =>
    ((measure_mono (hball i hi)).trans_lt measure_closedBall_lt_top).ne
  have hcarpos : ∀ i, 0 < volume (T' i).carrier := fun i =>
    lt_of_lt_of_le (ENNReal.mul_pos (by exact_mod_cast hc₃pos.ne') (pow_ne_zero 2 hδE0)) (hcar i)
  -- the shaded union is non-empty
  have hUne : U.Nonempty := by
    have hpos : 0 < volume (T' i₀).shade :=
      lt_of_lt_of_le (ENNReal.mul_pos (mul_ne_zero two_ne_zero hd2η_pos.ne') (hcarpos i₀).ne')
        (hfloor i₀ hi₀)
    exact nonempty_of_measure_ne_zero
      (ne_of_gt (lt_of_lt_of_le hpos
        (measure_mono (Set.subset_biUnion_of_mem (u := fun i => (T' i).shade) hi₀))))
  -- the ball cover of the shaded union at radius `r₁`
  obtain ⟨bι, bs₀, ctr, P, -, hPcb16, hPcb, hPdisj, hPmeas, hPcov, hover, -, hctr⟩ :=
    exists_ballCover_family hδ0 hr₁pos s' T' hball hUne
  -- light and heavy pieces
  set light : bι → Prop := fun B =>
    volume (P B ∩ U) < 2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ))
    with hlight
  set ls : Finset bι := bs₀.filter light with hls
  set bs : Finset bι := bs₀.filter (fun B => ¬ light B) with hbs
  have hbs_sub : bs ⊆ bs₀ := Finset.filter_subset _ _
  set Light : Set E3 := ⋃ B ∈ ls, P B with hLight
  have hL : MeasurableSet Light := Finset.measurableSet_biUnion _ fun B _ => hPmeas B
  /- **The number of balls.** `#𝔅₀ · |B(0, r₁)| ≤ D · |B(0, 2)|`. -/
  have hsub2 : ∀ B ∈ bs₀, Metric.ball (ctr B) (r₁ : ℝ) ⊆ Metric.ball (0 : E3) 2 := by
    intro B hB
    apply Metric.ball_subset_ball'
    have h1 : dist (ctr B) 0 ≤ 1 := Metric.mem_closedBall.mp (hUsub (hctr B hB))
    have h2 : (r₁ : ℝ) ≤ 1 := by exact_mod_cast hr₁le1
    linarith
  have hsum : ∑ B ∈ bs₀, volume (Metric.ball (ctr B) (r₁ : ℝ)) ≤
      (ballCoverConstant : ENNReal) * volume (Metric.ball (0 : E3) 2) :=
    MeasureTheory.sum_measure_le_mul_measure_of_card_le volume bs₀
      (fun B => Metric.ball (ctr B) (r₁ : ℝ)) (fun B _ => measurableSet_ball) measurableSet_ball
      hsub2 (fun x _ => by
        exact_mod_cast hover x _ (Finset.filter_subset _ _)
          (fun B hB => (Finset.mem_filter.mp hB).2))
  have hsum' : (bs₀.card : ENNReal) * volume (Metric.ball (0 : E3) (r₁ : ℝ)) ≤
      (ballCoverConstant : ENNReal) * volume (Metric.ball (0 : E3) 2) := by
    calc (bs₀.card : ENNReal) * volume (Metric.ball (0 : E3) (r₁ : ℝ))
        = ∑ B ∈ bs₀, volume (Metric.ball (ctr B) (r₁ : ℝ)) := by
          rw [Finset.sum_congr rfl
            (fun B _ => Measure.addHaar_ball_center volume (ctr B) (r₁ : ℝ)),
            Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := hsum
  /- **Ball volumes** in terms of `κ = |B(0, 1)|`. -/
  have hball_r : ∀ r : NNReal,
      volume (Metric.ball (0 : E3) (r : ℝ)) = ((r : NNReal) : ENNReal) ^ (3 : ℕ) * κ := by
    intro r
    rw [Measure.addHaar_ball volume (0 : E3) r.coe_nonneg, hfr, ENNReal.ofReal_pow r.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
  have hball_2 : volume (Metric.ball (0 : E3) 2) = 8 * κ := by
    rw [Measure.addHaar_ball volume (0 : E3) (by norm_num : (0 : ℝ) ≤ 2), hfr, ← hκ]
    congr 1
    norm_num
  have hr₁3 : ((r₁ : NNReal) : ENNReal) ^ (3 : ℕ) = (δ : ENNReal) ^ (3 * exscal) := by
    rw [hr₁def, ENNReal.coe_rpow_of_nonneg _ hexscal.le, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have hsplit3 : (δ : ENNReal) ^ (3 : ℕ) = (δ : ENNReal) ^ (3 * exscal) *
      ((δ : ENNReal) ^ (2 : ℕ) * (δ : ENNReal) ^ (1 - 3 * exscal)) := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_add _ _ hδE0 hδEtop, ← ENNReal.rpow_add _ _ hδE0 hδEtop,
      ← ENNReal.rpow_natCast]
    congr 1
    push_cast
    ring
  /- **The threshold** `16 D κ δ^{1 - 3 exscal} ≤ c₃`, in `ℝ≥0∞`. -/
  have hthrE : 16 * (ballCoverConstant : ENNReal) * κ * (δ : ENNReal) ^ (1 - 3 * exscal) ≤
      ((Tube.le_volume.c 3 : NNReal) : ENNReal) := by
    have h := ENNReal.coe_le_coe.mpr hthr
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hκtop,
      ENNReal.coe_rpow_of_ne_zero hδ0.ne', ENNReal.coe_natCast, ENNReal.coe_ofNat] at h
    exact h
  /- **The total loss** `|U ∩ Light| ≤ #𝔅₀ · 2δ^{2η}|B(0, δ)| ≤ δ^{2η} · c₃ δ²`. -/
  have hloss : volume (U ∩ Light) ≤ (bs₀.card : ENNReal) *
      (2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ))) := by
    calc volume (U ∩ Light) = volume (⋃ B ∈ ls, (P B ∩ U)) := by
            rw [Set.inter_comm, hLight, Set.iUnion₂_inter]
      _ ≤ ∑ B ∈ ls, volume (P B ∩ U) := measure_biUnion_finset_le _ _
      _ ≤ ∑ B ∈ ls, 2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ)) :=
            Finset.sum_le_sum fun B hB => ((Finset.mem_filter.mp hB).2).le
      _ = (ls.card : ENNReal) *
            (2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (bs₀.card : ENNReal) *
            (2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ))) := by
            gcongr
            exact Finset.filter_subset _ _
  have hkey : (bs₀.card : ENNReal) *
      (2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ))) ≤
      (δ : ENNReal) ^ (2 * η) *
        (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) := by
    have hA : (bs₀.card : ENNReal) * ((δ : ENNReal) ^ (3 * exscal) * κ) ≤
        (ballCoverConstant : ENNReal) * (8 * κ) := by
      rw [← hr₁3, ← hball_r r₁, ← hball_2]; exact hsum'
    calc (bs₀.card : ENNReal) *
          (2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ)))
        = (bs₀.card : ENNReal) * (2 * (δ : ENNReal) ^ (2 * η) * ((δ : ENNReal) ^ (3 : ℕ) * κ)) := by
          rw [hball_r δ]
      _ = ((bs₀.card : ENNReal) * ((δ : ENNReal) ^ (3 * exscal) * κ)) *
            (2 * (δ : ENNReal) ^ (2 * η) *
              ((δ : ENNReal) ^ (2 : ℕ) * (δ : ENNReal) ^ (1 - 3 * exscal))) := by
          rw [hsplit3]; ring
      _ ≤ ((ballCoverConstant : ENNReal) * (8 * κ)) *
            (2 * (δ : ENNReal) ^ (2 * η) *
              ((δ : ENNReal) ^ (2 : ℕ) * (δ : ENNReal) ^ (1 - 3 * exscal))) := by
          gcongr
      _ = (δ : ENNReal) ^ (2 * η) * ((δ : ENNReal) ^ (2 : ℕ) *
            (16 * (ballCoverConstant : ENNReal) * κ * (δ : ENNReal) ^ (1 - 3 * exscal))) := by
          ring
      _ ≤ (δ : ENNReal) ^ (2 * η) * ((δ : ENNReal) ^ (2 : ℕ) *
            ((Tube.le_volume.c 3 : NNReal) : ENNReal)) := by
          gcongr
      _ = _ := by ring
  have hlossU : ∀ i, volume (U ∩ Light) ≤ (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier :=
    fun i => (hloss.trans hkey).trans (mul_le_mul' le_rfl (hcar i))
  have hlossi : ∀ i ∈ s', volume ((T' i).shade ∩ Light) ≤
      (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier := fun i hi =>
    (measure_mono (Set.inter_subset_inter_left _
      (Set.subset_biUnion_of_mem (u := fun i => (T' i).shade) hi))).trans (hlossU i)
  -- the loss is at most half of every shading
  have hhalfT : ∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤
      (2 : ENNReal)⁻¹ * volume (T' i).shade := by
    intro i hi
    calc (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier
        = (2 : ENNReal)⁻¹ * (2 * (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier) := by
          rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
            one_mul]
      _ ≤ (2 : ENNReal)⁻¹ * volume (T' i).shade := by gcongr; exact hfloor i hi
  /- **(ii)** the per-tube floor survives. -/
  have hii : ∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤
      volume ((T' i).shade \ Light) := by
    intro i hi
    have hfin : (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≠ ⊤ :=
      ENNReal.mul_ne_top hd2η_top (hcartop i hi)
    rw [← ENNReal.add_le_add_iff_right hfin]
    calc (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier +
          (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier
        = 2 * (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier := by ring
      _ ≤ volume (T' i).shade := hfloor i hi
      _ = volume ((T' i).shade \ Light) + volume ((T' i).shade ∩ Light) :=
          (measure_sdiff_add_inter _ hL).symm
      _ ≤ volume ((T' i).shade \ Light) + (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier := by
          gcongr; exact hlossi i hi
  /- **(iii)** half of every shading, hence of the total mass, survives. -/
  have hiii_i : ∀ i ∈ s', (2 : ENNReal)⁻¹ * volume (T' i).shade ≤
      volume ((T' i).shade \ Light) := by
    intro i hi
    have hshtop : volume (T' i).shade ≠ ⊤ :=
      ((measure_mono (T' i).shade_subset).trans_lt (lt_top_iff_ne_top.mpr (hcartop i hi))).ne
    have hfin : (2 : ENNReal)⁻¹ * volume (T' i).shade ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero) hshtop
    rw [← ENNReal.add_le_add_iff_right hfin]
    calc (2 : ENNReal)⁻¹ * volume (T' i).shade + (2 : ENNReal)⁻¹ * volume (T' i).shade
        = volume (T' i).shade := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
      _ = volume ((T' i).shade \ Light) + volume ((T' i).shade ∩ Light) :=
          (measure_sdiff_add_inter _ hL).symm
      _ ≤ volume ((T' i).shade \ Light) + (2 : ENNReal)⁻¹ * volume (T' i).shade := by
          gcongr
          exact (hlossi i hi).trans (hhalfT i hi)
  have hiii : (2 : ENNReal)⁻¹ * ∑ i ∈ s', volume (T' i).shade ≤
      ∑ i ∈ s', volume ((T' i).shade \ Light) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hiii_i
  /- **(i)** the heavy pieces cover the cut shadings, and each is heavy for the cut union. -/
  have hcov'' : ∀ i ∈ s', (T' i).shade \ Light ⊆ ⋃ B ∈ bs, P B := by
    intro i hi x hx
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp (hPcov i hi hx.1)
    refine Set.mem_biUnion (Finset.mem_filter.mpr ⟨hB, fun hlB => hx.2 ?_⟩) hxB
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hB, hlB⟩) hxB
  have hbsne : bs.Nonempty := by
    have hpos : 0 < volume ((T' i₀).shade \ Light) :=
      lt_of_lt_of_le (ENNReal.mul_pos hd2η_pos.ne' (hcarpos i₀).ne') (hii i₀ hi₀)
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    obtain ⟨B, hB, -⟩ := Set.mem_iUnion₂.mp (hcov'' i₀ hi₀ hx)
    exact ⟨B, hB⟩
  have hheavy : ∀ B ∈ bs,
      2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ)) ≤
        volume (P B ∩ ⋃ i ∈ s', ((T' i).shade \ Light)) := by
    intro B hB
    have hB' := Finset.mem_filter.mp hB
    have hnl : 2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ)) ≤
        volume (P B ∩ U) := not_lt.mp hB'.2
    refine hnl.trans (measure_mono ?_)
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx.2
    refine ⟨hx.1, Set.mem_biUnion hi ⟨hxi, fun hxL => ?_⟩⟩
    -- a point of a heavy piece is in no light piece: the pieces are disjoint
    obtain ⟨B', hB'ls, hxB'⟩ := Set.mem_iUnion₂.mp hxL
    have hB'' := Finset.mem_filter.mp hB'ls
    have hne : B ≠ B' := fun h => hB'.2 (h ▸ hB''.2)
    exact Set.disjoint_left.mp
      (hPdisj (Finset.mem_coe.mpr hB'.1) (Finset.mem_coe.mpr hB''.1) hne) hx.1 hxB'
  -- every heavy piece meets the cut shaded union (its heaviness is a positive lower bound)
  have hne' : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ s', ((T' i).shade \ Light)).Nonempty := by
    intro B hB
    have hpos : 0 < 2 * (δ : ENNReal) ^ (2 * η) * volume (Metric.ball (0 : E3) (δ : ℝ)) :=
      ENNReal.mul_pos (mul_ne_zero two_ne_zero hd2η_pos.ne')
        (Metric.measure_ball_pos volume (0 : E3) (by exact_mod_cast hδ0)).ne'
    exact nonempty_of_measure_ne_zero (lt_of_lt_of_le hpos (hheavy B hB)).ne'
  /- **(iv)** GWZ (87) transports to the cut family at `Λ = 2`. -/
  have hU'' : (⋃ i ∈ s', (deleteShadeTube (T' i) Light hL).toShadedBody.shade) ⊆
      ⋃ i ∈ s', (T' i).toShadedBody.shade :=
    Set.iUnion₂_mono fun i _ => Set.sdiff_subset
  have hvol2 : volume (⋃ i ∈ s', (T' i).toShadedBody.shade) ≤
      ((2 : NNReal) : ENNReal) *
        volume (⋃ i ∈ s', (deleteShadeTube (T' i) Light hL).toShadedBody.shade) := by
    have hUdiff : U \ Light ⊆ ⋃ i ∈ s', (deleteShadeTube (T' i) Light hL).toShadedBody.shade := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx.1
      exact Set.mem_biUnion hi ⟨hxi, hx.2⟩
    have hi₀sub : (T' i₀).shade \ Light ⊆
        ⋃ i ∈ s', (deleteShadeTube (T' i) Light hL).toShadedBody.shade :=
      Set.subset_biUnion_of_mem (u := fun i => (deleteShadeTube (T' i) Light hL).toShadedBody.shade)
        hi₀
    rw [ENNReal.coe_ofNat, two_mul]
    calc volume U = volume (U \ Light) + volume (U ∩ Light) := (measure_sdiff_add_inter U hL).symm
      _ ≤ volume (⋃ i ∈ s', (deleteShadeTube (T' i) Light hL).toShadedBody.shade) +
            volume ((T' i₀).shade \ Light) :=
          add_le_add (measure_mono hUdiff)
            (((hlossU i₀).trans (hhalfT i₀ hi₀)).trans (hiii_i i₀ hi₀))
      _ ≤ volume (⋃ i ∈ s', (deleteShadeTube (T' i) Light hL).toShadedBody.shade) +
            volume (⋃ i ∈ s', (deleteShadeTube (T' i) Light hL).toShadedBody.shade) :=
          add_le_add le_rfl (measure_mono hi₀sub)
  have hhalfE : (δ : ENNReal) ^ (η / 2) ≤ (2 : ENNReal)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le]
    have h := ENNReal.coe_le_coe.mpr hhalf
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδ0.ne', ENNReal.coe_one,
      ENNReal.coe_ofNat] at h
    rwa [mul_comm]
  have hiv : LocalMassAt δ η s' (fun i ↦ deleteShadeTube (T' i) Light hL) := by
    rw [localMassAt_iff_forall_clause]
    intro k hk
    have h1 := (localMassAt_iff_forall_clause δ (η / 2) s' T').mp hlm k hk
    refine (h1.transport hU'' (Λ := 2) hvol2).mono_gain ?_
    calc (δ : ENNReal) ^ η = (δ : ENNReal) ^ (η / 2) * (δ : ENNReal) ^ (η / 2) := by
          rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
      _ ≤ (2 : ENNReal)⁻¹ * (δ : ENNReal) ^ (η / 2) := by gcongr
      _ = ((2 : NNReal) : ENNReal)⁻¹ * (δ : ENNReal) ^ (η / 2) := by rw [ENNReal.coe_ofNat]
  exact ⟨Light, hL, bι, bs, ctr, P, hbsne, fun B hB => hPcb B (hbs_sub hB),
    hPdisj.subset (by exact_mod_cast hbs_sub), fun B _ => hPmeas B, hcov'',
    fun x t hts hxt => hover x t (hts.trans hbs_sub) hxt, hheavy,
    fun B hB => hPcb16 B (hbs_sub hB), hPmeas, hne', hii, hiii, hiv⟩

end Kakeya.VeryNotSticky
