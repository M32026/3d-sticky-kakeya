/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinConfig

/-!
# The construction of the per-ball data of Configuration `hyp:ml2setup`

`Kakeya.VeryNotSticky.BallData` bundles items (C2)–(C5) of Configuration `hyp:ml2setup`.
Its only intended producer is `Kakeya.VeryNotSticky.exists_setup_caseSideData`, whose
construction the blueprint leaves informal. This file builds that construction group by
group, each group as a standalone existential lemma about an arbitrary
`cfg : Kakeya.VeryNotSticky`, so that the pieces can be assembled independently of one
another and so that partial progress is checkable.

* `Kakeya.VeryNotSticky.exists_ballCover` is item **(C2)**: the family `𝔅` of `r₁`-balls,
  their centres, the subordinate measurable partition `B̂`, the covering of the shadings and
  the bounded-overlap bound. It supplies the nine `BallData` fields `bι`, `bs`,
  `bs_nonempty`, `ctr`, `P`, `P_subset_ball`, `P_disjoint`, `P_measurable`, `P_cover`,
  `ballOverlap`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

/-- **The overlap constant of the `r₁`-ball cover of (C2)**.

The centres of the cover are a maximal `r₁/16`-separated subset of the shaded union, so at most
`(1 + 2 r₁ / (r₁/16)) ^ 3 = 33 ^ 3` of the balls `B(ctr B, r₁)` contain a common point. The value
is recorded as a numeral rather than through `Kakeya.separatedNetCoverConstant`, whose overlap
bound is stated only for radii at most twice the separation and hence does not cover the
factor `4` by which the pieces of the partition are shrunk. -/
def ballCoverConstant : ℕ := 35937

/-- **The `r₁`-ball cover with its subordinate partition** (blueprint `hyp:ml2setup` (C2),
via `lem:separatedNetCover` and `lem:subordinatePartition`).

Given a configuration whose shaded union is non-empty, there is a family `𝔅` of balls of
radius `r₁ = δ^{exscal}` and a measurable partition `B̂` subordinate to it such that

* the pieces are pairwise disjoint, measurable, and contained in the *quarter* ball
  `B(ctr B, r₁/4)` — a strengthening of the field
  `Kakeya.VeryNotSticky.BallData.P_subset_ball`, which is what item (C3) needs in order to
  produce segments of length comparable to `r₁` that still fit inside the full ball;
* every shading `Y(T)`, `T ∈ 𝕋`, is covered by the pieces;
* the balls are `ballCoverConstant`-boundedly overlapping;
* every piece meets the shaded union, which is what makes the segment family of a ball
  non-empty, and `𝔅` itself is non-empty.

The construction is the standard one: a maximal `r₁/16`-separated subset of the shaded union
covers it at radius `r₁/16` (`Kakeya.exists_maximal_separated`), the pieces are the
disjointification of those balls (`Kakeya.exists_subordinatePartition`), and the balls that
retain no mass are discarded. -/
theorem exists_ballCover (cfg : VeryNotSticky.{u})
    (hne : (⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) :
    ∃ (bι : Type u) (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
      (P : bι → Set (EuclideanSpace ℝ (Fin 3))),
      bs.Nonempty ∧
      (∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16)) ∧
      (∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ)) ∧
      (bs : Set bι).PairwiseDisjoint P ∧
      (∀ B, MeasurableSet (P B)) ∧
      (∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B) ∧
      (∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
          (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant) ∧
      (∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ cfg.s, (cfg.T i).shade with hSdef
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by
    exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hr : (0 : ℝ) < (cfg.r₁ : ℝ) / 16 := by positivity
  have hSbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 3))) (r := 1)).subset ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact cfg.contained i hi ((cfg.T i).shade_subset hxi)
  obtain ⟨N, hNS, hsep, hmax⟩ := Kakeya.exists_maximal_separated hSbdd hr
  set bs₀ : Finset (ULift.{u} (EuclideanSpace ℝ (Fin 3))) :=
    N.map ⟨ULift.up, ULift.up_injective⟩ with hbs₀
  have hmem₀ : ∀ B : ULift.{u} (EuclideanSpace ℝ (Fin 3)), B ∈ bs₀ ↔ ULift.down B ∈ N := by
    intro B
    simp [hbs₀]
  obtain ⟨P₀, hP₀sub, hP₀meas, hP₀disj, hP₀union⟩ :=
    Kakeya.exists_subordinatePartition (E := EuclideanSpace ℝ (Fin 3)) bs₀
      (fun B => ball (ULift.down B) ((cfg.r₁ : ℝ) / 16)) (fun B _ => measurableSet_ball)
  -- make the partition measurable at *every* index, by zeroing it off the cover
  set P : ULift.{u} (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)) :=
    fun B => if B ∈ bs₀ then P₀ B else ∅ with hPdef
  have hPeq : ∀ B ∈ bs₀, P B = P₀ B := by
    intro B hB; simp [hPdef, hB]
  have hPsub : ∀ B ∈ bs₀, P B ⊆ ball (ULift.down B) ((cfg.r₁ : ℝ) / 16) := by
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
  have hPunion : ⋃ B ∈ bs₀, P B = ⋃ B ∈ bs₀, ball (ULift.down B) ((cfg.r₁ : ℝ) / 16) := by
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
    have hx₀ : x ∈ ⋃ B ∈ bs₀, ball (ULift.down B) ((cfg.r₁ : ℝ) / 16) := by
      obtain ⟨y, hy, hxy⟩ := hmax x hx
      exact Set.mem_biUnion ((hmem₀ ⟨y⟩).2 hy) (by simpa [Metric.mem_ball] using hxy)
    rw [← hPunion] at hx₀
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp hx₀
    exact Set.mem_biUnion (Finset.mem_filter.2 ⟨hB, ⟨x, hxB, hx⟩⟩) hxB
  refine ⟨ULift.{u} (EuclideanSpace ℝ (Fin 3)), bs, ULift.down, P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    exact (Set.subset_biUnion_of_mem (u := fun i => (cfg.T i).shade) hi).trans hScov
  · -- bounded overlap
    intro x t hts hball
    have hsepN : ∀ y ∈ (↑(t.image ULift.down) : Set (EuclideanSpace ℝ (Fin 3))),
        ∀ z ∈ (↑(t.image ULift.down) : Set (EuclideanSpace ℝ (Fin 3))), y ≠ z →
          (cfg.r₁ : ℝ) / 16 ≤ dist y z := by
      intro y hy z hz hyz
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy hz
      obtain ⟨B, hB, rfl⟩ := hy
      obtain ⟨B', hB', rfl⟩ := hz
      exact hsep _ ((hmem₀ B).1 (hbssub (hts hB))) _ ((hmem₀ B').1 (hbssub (hts hB'))) hyz
    have hball' : (↑(t.image ULift.down) : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        ball x (cfg.r₁ : ℝ) := by
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
    have harith : (1 + 2 * (cfg.r₁ : ℝ) / ((cfg.r₁ : ℝ) / 16)) ^ 3 = 35937 := by
      have h32 : (2 * (cfg.r₁ : ℝ) / ((cfg.r₁ : ℝ) / 16)) = 32 := by
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

/-- **The `δ`-ball covers of the segments** (blueprint `hyp:ml2thinsetup`, the family
`𝒞(T_B)` carried by `Kakeya.VeryNotSticky.BallData`).

For an arbitrary family of shaded bodies indexed by `σ` there is a single index type `γ` and a
single centre map `covCtr` carrying, for each member, a `ballCoverConstant`-boundedly
overlapping cover of its carrier by balls of radius `δ`, each of which meets the carrier.

This supplies the four `BallData` fields `γ`, `cov`, `covCtr`, `cov_isCover`, `cov_meets`
whatever the segment family turns out to be, at the *same* overlap constant as
`Kakeya.VeryNotSticky.exists_ballCover`, which is what lets one value of the field `D` serve
both covers. The covers are those of a maximal `δ`-separated subset of each carrier
(`Kakeya.exists_separatedNetCover`); `γ = σ × ℝ³` keeps the covers of distinct members
disjointly indexed, which is what a single global centre map requires. -/
theorem exists_deltaCovers {σ : Type u} {δ : NNReal} (hδ : 0 < δ)
    (Y : σ → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ∃ (γ : Type u) (cov : σ → Finset γ) (covCtr : γ → EuclideanSpace ℝ (Fin 3)),
      (∀ p : σ, Kakeya.IsBoundedlyOverlappingCover (cov p) covCtr (fun _ => (δ : ℝ))
          ballCoverConstant (Y p).carrier) ∧
      (∀ p : σ, ∀ j ∈ cov p, (ball (covCtr j) (δ : ℝ) ∩ (Y p).carrier).Nonempty) := by
  classical
  have hδ' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hchoice : ∀ p : σ, ∃ N : Finset (EuclideanSpace ℝ (Fin 3)),
      ↑N ⊆ (Y p).carrier ∧
      (∀ y ∈ N, ∀ z ∈ N, y ≠ z → (δ : ℝ) ≤ dist y z) ∧
      ∀ x ∈ (Y p).carrier, ∃ y ∈ N, dist x y < (δ : ℝ) := by
    intro p
    exact Kakeya.exists_maximal_separated (Y p).isCompact'.isBounded hδ'
  choose N hNsub hNsep hNmax using hchoice
  refine ⟨σ × EuclideanSpace ℝ (Fin 3), fun p => (N p).image (fun x => (p, x)), Prod.snd,
    ?_, ?_⟩
  · intro p
    constructor
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := hNmax p x hx
      refine Set.mem_biUnion (Finset.mem_image.2 ⟨y, hy, rfl⟩) ?_
      simpa [Metric.mem_ball] using hxy
    · intro x
      have hsub : {j ∈ (N p).image (fun x => (p, x)) | x ∈ ball (Prod.snd j) (δ : ℝ)} ⊆
          ({y ∈ N p | x ∈ ball y (δ : ℝ)}.image (fun x => (p, x))) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_image] at hj ⊢
        obtain ⟨⟨y, hy, rfl⟩, hx⟩ := hj
        exact ⟨y, ⟨hy, hx⟩, rfl⟩
      refine le_trans (Finset.card_le_card hsub) ?_
      refine le_trans (Finset.card_image_le) ?_
      have hb := Kakeya.card_filter_ball_le (E := EuclideanSpace ℝ (Fin 3))
        hδ' (le_of_lt (by linarith : (δ : ℝ) < 2 * (δ : ℝ))) (hNsep p) x
      have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
      rw [hfr] at hb
      exact hb.trans (by norm_num [Kakeya.separatedNetCoverConstant, ballCoverConstant])
  · intro p j hj
    simp only [Finset.mem_image] at hj
    obtain ⟨y, hy, rfl⟩ := hj
    exact ⟨y, Metric.mem_ball_self hδ', hNsub p hy⟩

/-! ### (C3): the tube segments and their thickness profile -/

/-- **A tube meeting the quarter ball crosses the ball in a segment of length `r/2`.**

If the `δ`-tube `T` meets `B(x₀, r/4)` and `δ ≤ r/8 ≤ 1/8`, then its core segment contains two
points `z`, `z'` at distance exactly `r/2` whose whole `δ`-neighbourhood — in particular the
ball `B(z, δ)` — lies inside `T ∩ B̄(x₀, r)`.

This is the geometric content behind the field
`Kakeya.VeryNotSticky.BallData.segs_thickness`: the *lower* half of the thickness profile
`∼ (r₁, δ, δ)` of a segment is not automatic from `T ∩ B̄` being an intersection, and it is
what forces the pieces `B̂` of (C2) to be shrunk to the quarter ball. -/
theorem exists_core_pair_of_tube_meets_ball {δ : NNReal}
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) {x₀ : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hδr : (δ : ℝ) ≤ r / 8)
    (hmeet : (T.carrier ∩ ball x₀ (r / 4)).Nonempty) :
    ∃ z z' : EuclideanSpace ℝ (Fin 3), dist z z' = r / 2 ∧
      closedBall z (δ : ℝ) ⊆ T.carrier ∩ closedBall x₀ r ∧
      z' ∈ T.carrier ∩ closedBall x₀ r := by
  classical
  obtain ⟨w, hwT, hwB⟩ := hmeet
  -- a core point `z` within `δ` of `w`
  rw [T.carrier_eq] at hwT
  obtain ⟨z, hzseg, hwz'⟩ := Set.mem_iUnion₂.mp hwT
  have hwz : dist w z ≤ (δ : ℝ) := by
    exact Metric.mem_closedBall.1 hwz'
  have hzx₀ : dist z x₀ ≤ r / 4 + (δ : ℝ) := by
    have h1 : dist w x₀ < r / 4 := Metric.mem_ball.1 hwB
    calc dist z x₀ ≤ dist z w + dist w x₀ := dist_triangle _ _ _
      _ ≤ (δ : ℝ) + r / 4 := by rw [dist_comm z w]; linarith
      _ = r / 4 + (δ : ℝ) := by ring
  -- the second core point, at distance `r/2` from `z`
  have hzseg' := hzseg
  rw [segment_eq_image' ℝ T.x T.y] at hzseg'
  obtain ⟨t, ht, hzt⟩ := hzseg'
  simp only [Set.mem_Icc] at ht
  have hnorm : ‖T.y - T.x‖ = 1 := by
    simpa [dist_eq_norm_sub'] using T.dist_eq_one
  have hL : r / 2 ≤ 1 / 2 := by linarith
  have hcase : (t + r / 2 ≤ 1) ∨ (0 ≤ t - r / 2) := by
    by_contra h
    rw [not_or] at h
    obtain ⟨h1, h2⟩ := h
    rw [not_le] at h1 h2
    linarith [ht.1, ht.2]
  obtain ⟨t', ht'mem, ht'dist⟩ : ∃ t' : ℝ, t' ∈ Set.Icc (0 : ℝ) 1 ∧ |t' - t| = r / 2 := by
    rcases hcase with h | h
    · exact ⟨t + r / 2, ⟨by linarith [ht.1], by linarith⟩, by
        rw [show t + r / 2 - t = r / 2 by ring, abs_of_nonneg (by linarith)]⟩
    · exact ⟨t - r / 2, ⟨by linarith, by linarith [ht.2]⟩, by
        rw [show t - r / 2 - t = -(r / 2) by ring, abs_neg, abs_of_nonneg (by linarith)]⟩
  have hz'seg : T.x + t' • (T.y - T.x) ∈ segment ℝ T.x T.y := by
    rw [segment_eq_image' ℝ T.x T.y]
    exact Set.mem_image_of_mem _ ht'mem
  have hd : dist (T.x + t' • (T.y - T.x)) z = r / 2 := by
    simp only at hzt
    rw [← hzt, dist_eq_norm]
    have hmod : T.x + t' • (T.y - T.x) - (T.x + t • (T.y - T.x)) = (t' - t) • (T.y - T.x) := by
      module
    rw [hmod, norm_smul, hnorm, mul_one, Real.norm_eq_abs, ht'dist]
  refine ⟨z, T.x + t' • (T.y - T.x), ?_, ?_, ?_⟩
  · rw [dist_comm]; exact hd
  · -- the ball around `z`
    intro u hu
    have huT : u ∈ T.carrier := by
      rw [T.carrier_eq_cthickening]
      exact Metric.closedBall_subset_cthickening hzseg (δ : ℝ) hu
    refine ⟨huT, ?_⟩
    rw [Metric.mem_closedBall]
    calc dist u x₀ ≤ dist u z + dist z x₀ := dist_triangle _ _ _
      _ ≤ (δ : ℝ) + (r / 4 + (δ : ℝ)) := by
          exact add_le_add (Metric.mem_closedBall.1 hu) hzx₀
      _ ≤ r := by linarith
  · refine ⟨?_, ?_⟩
    · rw [T.carrier_eq_cthickening]
      exact Metric.self_subset_cthickening _ hz'seg
    · rw [Metric.mem_closedBall]
      calc dist (T.x + t' • (T.y - T.x)) x₀
          ≤ dist (T.x + t' • (T.y - T.x)) z + dist z x₀ := dist_triangle _ _ _
        _ ≤ r / 2 + (r / 4 + (δ : ℝ)) := by rw [hd]; linarith [hzx₀]
        _ ≤ r := by linarith

/-- **The thickness profile of a tube segment** (blueprint `hyp:ml2setup` (C3); the field
`Kakeya.VeryNotSticky.BallData.segs_thickness`).

The intersection of a `δ`-tube with a ball of radius `r` it enters *deeply* — i.e. whose
quarter ball it meets — has affine thicknesses comparable to `(r, δ, δ)` with the absolute
constant `4`. Both halves are needed and neither is formal: the upper half at rank `0` is the
ball, the upper half at ranks `1, 2` is the tube, the lower half at ranks `1, 2` is the
`δ`-ball around a core point, and the lower half at rank `0` is the pair of core points at
distance `r/2` produced by `Kakeya.VeryNotSticky.exists_core_pair_of_tube_meets_ball`.

The constant is absolute, so the `BallData` field `C₀` may be taken to be `4` as far as (C3)
is concerned. -/
theorem hasThicknesses_tube_inter_closedBall {δ : NNReal}
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) {x₀ : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hδr : (δ : ℝ) ≤ r / 8)
    (hmeet : (T.carrier ∩ ball x₀ (r / 4)).Nonempty) :
    Kakeya.HasThicknesses (T.carrier ∩ closedBall x₀ r) 4 ![r, (δ : ℝ), (δ : ℝ)] := by
  classical
  obtain ⟨z, z', hzz', hball, hz'⟩ :=
    exists_core_pair_of_tube_meets_ball T hr hr1 hδr hmeet
  set K : Set (EuclideanSpace ℝ (Fin 3)) := T.carrier ∩ closedBall x₀ r with hKdef
  have hKsub : K ⊆ closedBall x₀ r := Set.inter_subset_right
  have hKbdd : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKsub
  have hzK : z ∈ K := hball (Metric.mem_closedBall_self δ.coe_nonneg)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  -- conversions between `ethickness` and `thickness`
  have hconvup : ∀ (n : ℕ) (c : ℝ), 0 ≤ c →
      Metric.ethickness ℝ K n ≤ ENNReal.ofReal c → Metric.thickness ℝ K n ≤ c := by
    intro n c hc h
    rw [Metric.ethickness_thickness' hKbdd n] at h
    exact (ENNReal.ofReal_le_ofReal_iff hc).1 h
  have hconvlow : ∀ (n : ℕ) (c : ℝ),
      ENNReal.ofReal c ≤ Metric.ethickness ℝ K n → c ≤ Metric.thickness ℝ K n := by
    intro n c h
    rw [Metric.ethickness_thickness' hKbdd n] at h
    exact (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).1 h
  -- lower bound `δ` at every rank below `3`
  have hlowδ : ∀ n : ℕ, n < 3 → (δ : ℝ) ≤ Metric.thickness ℝ K n := by
    intro n hn
    refine hconvlow n _ ?_
    have h1 : ((δ : NNReal) : ENNReal) ≤ Metric.ethickness ℝ (closedBall z (δ : ℝ)) n :=
      le_ethickness_closedBall (V := EuclideanSpace ℝ (Fin 3)) δ (by rw [hfr]; exact hn)
    have h2 : Metric.ethickness ℝ (closedBall z (δ : ℝ)) n ≤ Metric.ethickness ℝ K n :=
      Metric.ethickness_monotone hball n
    calc ENNReal.ofReal (δ : ℝ) = ((δ : NNReal) : ENNReal) := ENNReal.ofReal_coe_nnreal
      _ ≤ _ := h1.trans h2
  -- upper bound `δ` at ranks `1` and `2`
  have hupδ : ∀ n : ℕ, 1 ≤ n → Metric.thickness ℝ K n ≤ (δ : ℝ) := by
    intro n hn
    refine hconvup n _ hδ0 ?_
    have h1 : Metric.ethickness ℝ K n ≤ Metric.ethickness ℝ T.carrier n :=
      Metric.ethickness_monotone Set.inter_subset_left n
    have h2 : Metric.ethickness ℝ T.carrier n ≤ Metric.ethickness ℝ T.carrier 1 :=
      Metric.ethickness_antitone hn
    calc Metric.ethickness ℝ K n ≤ Metric.ethickness ℝ T.carrier 1 := h1.trans h2
      _ ≤ ((δ : NNReal) : ENNReal) := T.ethickness_one_le
      _ = ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_coe_nnreal.symm
  -- rank-zero bounds
  have hup0 : Metric.thickness ℝ K 0 ≤ r :=
    Metric.thickness_le_of_subset_closedBall hKsub hr.le 0
  have hlow0 : r / 4 ≤ Metric.thickness ℝ K 0 := by
    refine hconvlow 0 _ ?_
    have h := Metric.half_dist_le_ethickness_zero (𝕜 := ℝ) hzK hz'
    rwa [hzz', show r / 2 / 2 = r / 4 by ring] at h
  intro k
  have hc4 : ((4 : NNReal) : ℝ) = 4 := by norm_num
  have h1 := hlowδ 1 (by norm_num)
  have h2 := hlowδ 2 (by norm_num)
  have h3 := hupδ 1 (by norm_num)
  have h4 := hupδ 2 (by norm_num)
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl <;> refine ⟨?_, ?_⟩ <;>
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, hc4] <;>
    linarith [hlow0, hup0, hδ0, hr.le]

/-! ### The core-line parametrization of a tube -/

section Core

variable {δ : NNReal}

/-- The point of the core line of a `δ`-tube at parameter `t`: `T.x + t·(T.y - T.x)`. The core
segment of the tube is the image of `[0,1]`. -/
noncomputable def corePt (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (t : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  T.x + t • T.direction

lemma dist_corePt (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (t u : ℝ) :
    dist (corePt T t) (corePt T u) = |t - u| := by
  have hsub : corePt T t - corePt T u = (t - u) • T.direction := by
    simp only [corePt]; module
  rw [dist_eq_norm, hsub, norm_smul, T.norm_direction, mul_one, Real.norm_eq_abs]

lemma corePt_mem_core (T : Tube δ (EuclideanSpace ℝ (Fin 3))) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : corePt T t ∈ segment ℝ T.x T.y := by
  rw [segment_eq_image' ℝ T.x T.y]
  exact ⟨t, ht, rfl⟩

lemma exists_corePt_of_mem_core (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ segment ℝ T.x T.y) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, corePt T t = z := by
  rw [segment_eq_image' ℝ T.x T.y] at hz
  obtain ⟨t, ht, htz⟩ := hz
  exact ⟨t, ht, htz⟩

lemma corePt_image_subset_segment (T : Tube δ (EuclideanSpace ℝ (Fin 3))) {u v : ℝ}
    (huv : u ≤ v) : corePt T '' Set.Icc u v ⊆ segment ℝ (corePt T u) (corePt T v) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [segment_eq_image' ℝ (corePt T u) (corePt T v)]
  rcases eq_or_lt_of_le huv with rfl | hlt
  · refine ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩
    have hsu : s = u := le_antisymm hs.2 hs.1
    simp [hsu]
  · have hvu : v - u ≠ 0 := by linarith
    refine ⟨(s - u) / (v - u), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [hs.1]) (by linarith)
    · rw [div_le_one (by linarith)]; linarith [hs.2]
    · have hq : corePt T v - corePt T u = (v - u) • T.direction := by
        simp only [corePt]; module
      show corePt T u + ((s - u) / (v - u)) • (corePt T v - corePt T u) = corePt T s
      rw [hq, smul_smul, div_mul_cancel₀ _ hvu]
      simp only [corePt]
      module

/-- A parameter of the core segment realizing the distance to a point `c`. -/
lemma exists_coreParam (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u ∈ Set.Icc (0 : ℝ) 1, dist (corePt T t) c ≤ dist (corePt T u) c := by
  have hcont : ContinuousOn (fun t : ℝ => dist (corePt T t) c) (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    unfold corePt
    fun_prop
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) hcont
  exact ⟨t, ht, fun u hu => hmin hu⟩

open Classical in
/-- The parameter of a core point of `T` nearest to `c`. -/
noncomputable def coreParam (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) : ℝ := (exists_coreParam T c).choose

lemma coreParam_mem (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) :
    coreParam T c ∈ Set.Icc (0 : ℝ) 1 := (exists_coreParam T c).choose_spec.1

lemma coreParam_min (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    dist (corePt T (coreParam T c)) c ≤ dist (corePt T u) c :=
  (exists_coreParam T c).choose_spec.2 u hu

/-- The left endpoint parameter of the window of half-length `L` around the nearest core point,
slid so as to stay inside `[0,1]`. -/
noncomputable def segStart (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : ℝ :=
  min (max (coreParam T c - L) 0) (1 - 2 * L)

lemma segStart_nonneg (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3))
    {L : ℝ} (hL1 : 2 * L ≤ 1) : 0 ≤ segStart T c L :=
  le_min (le_max_right _ _) (by linarith)

lemma segStart_add_le_one (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} : segStart T c L + 2 * L ≤ 1 := by
  have := min_le_right (max (coreParam T c - L) 0) (1 - 2 * L)
  simp only [segStart]
  linarith

lemma segStart_le_coreParam (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    segStart T c L ≤ coreParam T c := by
  refine min_le_of_left_le (max_le (by linarith) (coreParam_mem T c).1)

/-- **The window covers the core points near the nearest one.** -/
lemma mem_window (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3))
    {L s : ℝ} (hL : 0 ≤ L) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hd : |s - coreParam T c| ≤ L) :
    s ∈ Set.Icc (segStart T c L) (segStart T c L + 2 * L) := by
  rw [abs_le] at hd
  have hmax : max (coreParam T c - L) 0 ≤ s :=
    max_le (by linarith [hd.1]) hs.1
  constructor
  · exact le_trans (min_le_left _ _) hmax
  · have h1 : coreParam T c - L ≤ max (coreParam T c - L) 0 := le_max_left _ _
    rcases min_cases (max (coreParam T c - L) 0) (1 - 2 * L) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      simp only [segStart, he] <;> linarith [hd.2, hs.2]

end Core

/-! ### (C3): the tube segments -/

section SegBody

variable {δ : NNReal}

/-- **The carrier of the tube segment of `T` in the ball centred at `c`**: the closed
`δ`-neighbourhood of the sub-segment of the core of `T` of length `2L` around the core point
nearest to `c`, slid so as to stay inside the core.

Three properties make this the right choice, and none of them holds for the naive intersection
`T ∩ B̄(c, r₁)`:

* it is contained in `T` itself (the window is a sub-segment of the core), so the segment is
  literally a piece of its parent tube;
* its length is *exactly* `2L` whatever the tube and the ball, so any two segments have
  `2`-comparable thickness profiles — the field
  `Kakeya.VeryNotSticky.BallData.segs_dims`, which asks for the constant `2` and which the
  naive intersection misses by a factor `4`;
* it is a `δ`-neighbourhood of a segment of the core *line*, which is verbatim the field
  `Kakeya.VeryNotSticky.BallData.segs_core`, the one the blueprint assumes rather than
  proves. -/
noncomputable def segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  cthickening (δ : ℝ)
    (segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)))

lemma segment_subset_corePt_image (T : Tube δ (EuclideanSpace ℝ (Fin 3))) {u v : ℝ}
    (huv : u ≤ v) : segment ℝ (corePt T u) (corePt T v) ⊆ corePt T '' Set.Icc u v := by
  intro z hz
  rw [segment_eq_image' ℝ _ _] at hz
  obtain ⟨θ, hθ, hzθ⟩ := hz
  refine ⟨u + θ * (v - u), ⟨by nlinarith [hθ.1, hθ.2], by nlinarith [hθ.1, hθ.2]⟩, ?_⟩
  have hq : corePt T v - corePt T u = (v - u) • T.direction := by
    simp only [corePt]; module
  rw [← hzθ]
  show corePt T (u + θ * (v - u)) = corePt T u + θ • (corePt T v - corePt T u)
  rw [hq, smul_smul]
  simp only [corePt]
  module

lemma isClosed_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : IsClosed (segCarrierSet T c L) :=
  isClosed_cthickening

lemma segCarrierSet_subset_tube (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) :
    segCarrierSet T c L ⊆ T.carrier := by
  have hseg : segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) ⊆
      segment ℝ T.x T.y := by
    refine (convex_segment (𝕜 := ℝ) T.x T.y).segment_subset
      (corePt_mem_core T ⟨segStart_nonneg T c hL1, ?_⟩)
      (corePt_mem_core T ⟨by linarith [segStart_nonneg T c hL1], segStart_add_le_one T c⟩)
    have := segStart_add_le_one (T := T) (c := c) (L := L)
    linarith
  rw [T.carrier_eq_cthickening]
  exact Metric.cthickening_subset_of_subset (δ : ℝ) hseg

lemma corePt_coreParam_mem_window (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    corePt T (coreParam T c) ∈
      segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) := by
  have hmem := mem_window T c hL (coreParam_mem T c) (by simp [hL])
  exact corePt_image_subset_segment T (by linarith) ⟨_, hmem, rfl⟩

lemma closedBall_subset_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    closedBall (corePt T (coreParam T c)) (δ : ℝ) ⊆ segCarrierSet T c L :=
  Metric.closedBall_subset_cthickening (corePt_coreParam_mem_window T c hL) (δ : ℝ)

lemma segCarrierSet_nonempty (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    (segCarrierSet T c L).Nonempty :=
  ⟨corePt T (coreParam T c),
    closedBall_subset_segCarrierSet T c hL (Metric.mem_closedBall_self δ.coe_nonneg)⟩

lemma segCarrierSet_eq_biUnion (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) :
    segCarrierSet T c L =
      ⋃ w ∈ segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)),
        closedBall w (δ : ℝ) :=
  isClosed_segment.cthickening_eq_biUnion_closedBall δ.coe_nonneg

lemma segCarrierSet_subset_closedBall (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    segCarrierSet T c L ⊆ closedBall (corePt T (segStart T c L + L)) (L + (δ : ℝ)) := by
  rw [segCarrierSet_eq_biUnion]
  intro z hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨u, hu, rfl⟩ := segment_subset_corePt_image T (by linarith) hw
  have hdu : dist (corePt T u) (corePt T (segStart T c L + L)) ≤ L := by
    rw [dist_corePt]
    rw [abs_le]
    constructor <;> [linarith [hu.1]; linarith [hu.2]]
  rw [Metric.mem_closedBall]
  calc dist z (corePt T (segStart T c L + L))
      ≤ dist z (corePt T u) + dist (corePt T u) (corePt T (segStart T c L + L)) :=
        dist_triangle _ _ _
    _ ≤ (δ : ℝ) + L := add_le_add (Metric.mem_closedBall.1 hzw) hdu
    _ = L + (δ : ℝ) := by ring

/-- **The segment carrier lies on the core line of every parent tube** — verbatim the field
`Kakeya.VeryNotSticky.BallData.segs_core`. -/
lemma segCarrierSet_subset_cthickening_line (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) {C : ℝ} (hC : (δ : ℝ) ≤ C) :
    segCarrierSet T c L ⊆ cthickening C
      (AffineSubspace.mk' (corePt T (segStart T c L)) (Submodule.span ℝ {T.direction}) :
        Set (EuclideanSpace ℝ (Fin 3))) := by
  have hline : segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) ⊆
      (AffineSubspace.mk' (corePt T (segStart T c L)) (Submodule.span ℝ {T.direction}) :
        Set (EuclideanSpace ℝ (Fin 3))) := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := segment_subset_corePt_image T (by linarith) hz
    have : corePt T u = (u - segStart T c L) • T.direction +ᵥ corePt T (segStart T c L) := by
      simp only [corePt, vadd_eq_add]; module
    rw [this]
    exact AffineSubspace.vadd_mem_mk' _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  refine subset_trans ?_ (Metric.cthickening_mono hC _)
  exact Metric.cthickening_subset_of_subset (δ : ℝ) hline

/-- **The segment carrier contains the part of the tube inside the shrunken ball.** -/
lemma tube_inter_ball_subset_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L ρ : ℝ} (hL : 0 ≤ L)
    (hLρ : 2 * ((δ : ℝ) + ρ) ≤ L) :
    T.carrier ∩ ball c ρ ⊆ segCarrierSet T c L := by
  intro u hu
  obtain ⟨huT, huB⟩ := hu
  rw [T.carrier_eq] at huT
  obtain ⟨w, hw, huw⟩ := Set.mem_iUnion₂.mp huT
  obtain ⟨sw, hsw, rfl⟩ := exists_corePt_of_mem_core T hw
  have hwu : dist (corePt T sw) u ≤ (δ : ℝ) := by
    rw [dist_comm]; exact Metric.mem_closedBall.1 huw
  have hwc : dist (corePt T sw) c ≤ (δ : ℝ) + ρ := by
    calc dist (corePt T sw) c ≤ dist (corePt T sw) u + dist u c := dist_triangle _ _ _
      _ ≤ (δ : ℝ) + ρ := add_le_add hwu (le_of_lt (Metric.mem_ball.1 huB))
  have hac : dist (corePt T (coreParam T c)) c ≤ (δ : ℝ) + ρ :=
    le_trans (coreParam_min T c hsw) hwc
  have hdiff : |sw - coreParam T c| ≤ L := by
    have := dist_corePt T sw (coreParam T c)
    rw [← this]
    calc dist (corePt T sw) (corePt T (coreParam T c))
        ≤ dist (corePt T sw) c + dist c (corePt T (coreParam T c)) := dist_triangle _ _ _
      _ ≤ ((δ : ℝ) + ρ) + ((δ : ℝ) + ρ) := by
          rw [dist_comm c]; exact add_le_add hwc hac
      _ ≤ L := by linarith
  have hmem := mem_window T c hL hsw hdiff
  rw [segCarrierSet_eq_biUnion]
  exact Set.mem_biUnion
    (corePt_image_subset_segment T (by linarith) ⟨sw, hmem, rfl⟩) huw

/-! #### The thickness profile of a segment -/

lemma le_thickness_segCarrierSet_zero (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) :
    L ≤ Metric.thickness ℝ (segCarrierSet T c L) 0 := by
  have hbdd : Bornology.IsBounded (segCarrierSet T c L) :=
    Metric.isBounded_closedBall.subset (segCarrierSet_subset_closedBall T c hL)
  have hmemL : corePt T (segStart T c L) ∈ segCarrierSet T c L := by
    rw [segCarrierSet_eq_biUnion]
    exact Set.mem_biUnion (left_mem_segment ℝ _ _) (Metric.mem_closedBall_self δ.coe_nonneg)
  have hmemR : corePt T (segStart T c L + 2 * L) ∈ segCarrierSet T c L := by
    rw [segCarrierSet_eq_biUnion]
    exact Set.mem_biUnion (right_mem_segment ℝ _ _) (Metric.mem_closedBall_self δ.coe_nonneg)
  have hd : dist (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) = 2 * L := by
    rw [dist_corePt, show segStart T c L - (segStart T c L + 2 * L) = -(2 * L) by ring,
      abs_neg, abs_of_nonneg (by linarith)]
  have h := Metric.half_dist_le_ethickness_zero (𝕜 := ℝ) hmemL hmemR
  rw [hd, Metric.ethickness_thickness' hbdd 0] at h
  have := (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).1 h
  linarith

lemma thickness_segCarrierSet_zero_le (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    Metric.thickness ℝ (segCarrierSet T c L) 0 ≤ L + (δ : ℝ) :=
  Metric.thickness_le_of_subset_closedBall (segCarrierSet_subset_closedBall T c hL)
    (by positivity) 0

lemma le_thickness_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : n < 3) :
    (δ : ℝ) ≤ Metric.thickness ℝ (segCarrierSet T c L) n := by
  have hbdd : Bornology.IsBounded (segCarrierSet T c L) :=
    Metric.isBounded_closedBall.subset (segCarrierSet_subset_closedBall T c hL)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have h1 : ((δ : NNReal) : ENNReal) ≤
      Metric.ethickness ℝ (closedBall (corePt T (coreParam T c)) (δ : ℝ)) n :=
    le_ethickness_closedBall (V := EuclideanSpace ℝ (Fin 3)) δ (by rw [hfr]; exact hn)
  have h2 : Metric.ethickness ℝ (closedBall (corePt T (coreParam T c)) (δ : ℝ)) n ≤
      Metric.ethickness ℝ (segCarrierSet T c L) n :=
    Metric.ethickness_monotone (closedBall_subset_segCarrierSet T c hL) n
  have h3 : ENNReal.ofReal (δ : ℝ) ≤ Metric.ethickness ℝ (segCarrierSet T c L) n := by
    calc ENNReal.ofReal (δ : ℝ) = ((δ : NNReal) : ENNReal) := ENNReal.ofReal_coe_nnreal
      _ ≤ _ := h1.trans h2
  rw [Metric.ethickness_thickness' hbdd n] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).1 h3

lemma thickness_segCarrierSet_le (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    Metric.thickness ℝ (segCarrierSet T c L) n ≤ (δ : ℝ) := by
  have hbdd : Bornology.IsBounded (segCarrierSet T c L) :=
    Metric.isBounded_closedBall.subset (segCarrierSet_subset_closedBall T c hL)
  have hrank : Module.rank ℝ
      (AffineSubspace.mk' (corePt T (segStart T c L))
        (Submodule.span ℝ {T.direction})).direction ≤ (n : Cardinal) := by
    rw [AffineSubspace.direction_mk']
    refine le_trans (rank_span_le _) ?_
    simp only [Cardinal.mk_fintype, Cardinal.mk_singleton]
    exact_mod_cast Nat.one_le_cast.2 hn
  have h1 : Metric.thickness ℝ (segCarrierSet T c L) n ≤ (δ : ℝ) :=
    Metric.thickness_le_of_cthickening δ.coe_nonneg hrank
      (segCarrierSet_subset_cthickening_line T c hL (le_refl (δ : ℝ)))
  exact h1

lemma thickness_segCarrierSet_eq_zero (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) {n : ℕ} (hn : 3 ≤ n) :
    Metric.thickness ℝ (segCarrierSet T c L) n = 0 := by
  refine Metric.thickness_eq_zero_of_finrank_le (𝕜 := ℝ) ?_
  have : Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    rw [← Module.finrank_eq_rank]
    simp
  rw [this]
  exact_mod_cast Nat.cast_le.2 hn

/-- **The thickness profile of a tube segment**, at the absolute constant `4`: the field
`Kakeya.VeryNotSticky.BallData.segs_thickness` with `r₁ = 4L`. -/
lemma hasThicknesses_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1)
    (hδL : (δ : ℝ) ≤ L) :
    Kakeya.HasThicknesses (segCarrierSet T c L) 4 ![4 * L, (δ : ℝ), (δ : ℝ)] := by
  have h0l := le_thickness_segCarrierSet_zero T c hL hL1
  have h0u := thickness_segCarrierSet_zero_le T c hL
  have h1l := le_thickness_segCarrierSet T c hL (n := 1) (by norm_num)
  have h1u := thickness_segCarrierSet_le T c hL (n := 1) (by norm_num)
  have h2l := le_thickness_segCarrierSet T c hL (n := 2) (by norm_num)
  have h2u := thickness_segCarrierSet_le T c hL (n := 2) (by norm_num)
  have hc4 : ((4 : NNReal) : ℝ) = 4 := by norm_num
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  intro k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl <;> refine ⟨?_, ?_⟩ <;>
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, hc4] <;>
    linarith

/-- **Any two segments have `2`-comparable thickness profiles**: the field
`Kakeya.VeryNotSticky.BallData.segs_dims`. It is a consequence of the segments all being
`δ`-neighbourhoods of core sub-segments of one and the same length `2L`; the naive
intersection `T ∩ B̄` misses it. -/
lemma thickness_segCarrierSet_le_two_nsmul (T T' : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c c' : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1)
    (hδL : (δ : ℝ) ≤ L) :
    Metric.thickness ℝ (segCarrierSet T c L) ≤ 2 • Metric.thickness ℝ (segCarrierSet T' c' L) := by
  intro n
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hsm : (2 • Metric.thickness ℝ (segCarrierSet T' c' L)) n =
      2 * Metric.thickness ℝ (segCarrierSet T' c' L) n := by
    simp
  rw [hsm]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · have h0u := thickness_segCarrierSet_zero_le T c hL
      have h0l := le_thickness_segCarrierSet_zero T' c' hL hL1
      linarith
    · have h1u := thickness_segCarrierSet_le T c hL (n := 1) (by norm_num)
      have h1l := le_thickness_segCarrierSet T' c' hL (n := 1) (by norm_num)
      linarith
    · have h2u := thickness_segCarrierSet_le T c hL (n := 2) (by norm_num)
      have h2l := le_thickness_segCarrierSet T' c' hL (n := 2) (by norm_num)
      linarith
  · rw [thickness_segCarrierSet_eq_zero T c L hn, thickness_segCarrierSet_eq_zero T' c' L hn]
    norm_num

lemma dist_corePt_coreParam_le (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {ρ : ℝ} (hmeet : (T.carrier ∩ ball c ρ).Nonempty) :
    dist (corePt T (coreParam T c)) c ≤ (δ : ℝ) + ρ := by
  obtain ⟨u, huT, huB⟩ := hmeet
  rw [T.carrier_eq] at huT
  obtain ⟨w, hw, huw⟩ := Set.mem_iUnion₂.mp huT
  obtain ⟨sw, hsw, rfl⟩ := exists_corePt_of_mem_core T hw
  have hwu : dist (corePt T sw) u ≤ (δ : ℝ) := by
    rw [dist_comm]; exact Metric.mem_closedBall.1 huw
  refine le_trans (coreParam_min T c hsw) ?_
  calc dist (corePt T sw) c ≤ dist (corePt T sw) u + dist u c := dist_triangle _ _ _
    _ ≤ (δ : ℝ) + ρ := add_le_add hwu (le_of_lt (Metric.mem_ball.1 huB))

/-- **The segment stays inside the ball of radius `4L` it was cut out of**, which is what
makes `Kakeya.VeryNotSticky.BallData.bodies_subset_ball` compatible with
`Kakeya.VeryNotSticky.BallData.segs_le`. -/
lemma segCarrierSet_subset_closedBall_ctr (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L ρ R : ℝ} (hL : 0 ≤ L)
    (hmeet : (T.carrier ∩ ball c ρ).Nonempty)
    (hR : 2 * L + 2 * (δ : ℝ) + ρ ≤ R) :
    segCarrierSet T c L ⊆ closedBall c R := by
  have hmid : dist (corePt T (segStart T c L + L)) c ≤ L + ((δ : ℝ) + ρ) := by
    have h1 : dist (corePt T (segStart T c L + L)) (corePt T (coreParam T c)) ≤ L := by
      rw [dist_corePt, abs_le]
      have hw := mem_window T c hL (coreParam_mem T c) (by simp [hL])
      constructor <;> [linarith [hw.2]; linarith [hw.1]]
    exact le_trans (dist_triangle _ _ _)
      (add_le_add h1 (dist_corePt_coreParam_le T c hmeet))
  intro z hz
  have hz' := segCarrierSet_subset_closedBall T c hL hz
  rw [Metric.mem_closedBall] at hz' ⊢
  calc dist z c ≤ dist z (corePt T (segStart T c L + L)) + dist (corePt T (segStart T c L + L)) c :=
        dist_triangle _ _ _
    _ ≤ (L + (δ : ℝ)) + (L + ((δ : ℝ) + ρ)) := add_le_add hz' hmid
    _ ≤ R := by linarith

/-- **The tube segment as a shaded body**: the carrier is
`Kakeya.VeryNotSticky.segCarrierSet` and the shading is the part of the tube's shading that
lies in the piece `B̂`. Intersecting the shading with the carrier as well makes the definition
total — no hypothesis relating `Pset` to the ball is needed for it to typecheck — and is
harmless, because `Kakeya.VeryNotSticky.tube_inter_ball_subset_segCarrierSet` says the
intersection is vacuous exactly when the segment is the right one. -/
noncomputable def segShadedBody (T : ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L)
    (Pset : Set (EuclideanSpace ℝ (Fin 3))) (hP : MeasurableSet Pset) :
    ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  carrier := segCarrierSet T.toTube c L
  convex' := by
    unfold segCarrierSet
    exact ((convex_segment _ _).cthickening _).isConvexSet
  isCompact' := by
    unfold segCarrierSet
    exact isCompact_segment.cthickening
  nonempty' := segCarrierSet_nonempty T.toTube c hL
  shade := T.shade ∩ Pset ∩ segCarrierSet T.toTube c L
  measurableSet_shade :=
    (T.measurableSet_shade.inter hP).inter (isClosed_segCarrierSet _ _ _).measurableSet
  shade_subset := Set.inter_subset_right

@[simp] lemma segShadedBody_carrier (T : ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L)
    (Pset : Set (EuclideanSpace ℝ (Fin 3))) (hP : MeasurableSet Pset) :
    (segShadedBody T c hL Pset hP).carrier = segCarrierSet T.toTube c L := rfl

@[simp] lemma segShadedBody_shade (T : ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L)
    (Pset : Set (EuclideanSpace ℝ (Fin 3))) (hP : MeasurableSet Pset) :
    (segShadedBody T c hL Pset hP).shade =
      T.shade ∩ Pset ∩ segCarrierSet T.toTube c L := rfl

/-- **The segment's thickness scale is at least `δ`**, which is the hypothesis `h2` of
`Kakeya.ConvexSpaceBody.nonempty_biasedFactorization`.

Together with `Kakeya.VeryNotSticky.BallDataCore.segs_subset_ball` — the segments of a ball lie
in that ball — this is exactly what a producer of the (C4) factoring needs in order to run the
biased maximal density factoring on the segment family of a ball, after rescaling the ball to
the unit ball. -/
lemma le_ethickness_scale_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (segCarrierSet T c L) := by
  have hbdd : Bornology.IsBounded (segCarrierSet T c L) :=
    Metric.isBounded_closedBall.subset (segCarrierSet_subset_closedBall T c hL)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [Metric.ethickness.scale_eq, hfr]
  have h2 := le_thickness_segCarrierSet T c hL (n := 2) (by norm_num)
  rw [show (3 - 1 : ℕ) = 2 from rfl, Metric.ethickness_thickness' hbdd,
    ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal h2

end SegBody

open scoped Classical in
/-- **The segment family of (C3) together with the compatibility clauses of (C5)**.

Given the `r₁`-ball cover of `Kakeya.VeryNotSticky.exists_ballCover` — pieces inside the
`r₁/16`-ball, measurable, each meeting the shaded union — and the two scale conditions
`16δ ≤ r₁ ≤ 1`, there is a segment family realizing **seventeen** fields of
`Kakeya.VeryNotSticky.BallData` at once:

`σ`, `segs`, `Y`, `fam`, `segs_nonempty`, `fam_subset`, `fam_disjoint`, `Y_piece`,
`segs_thickness`, `segs_dims`, `parent`, `into`, `back`, `segs_core`, `m`, `Cm`, `hCm`,
`fibre` — the last four at `m = Cm = 1`, the fibre count being *exact* because the parent
family of a segment is a singleton.

The last conjunct, `(Y p).carrier ⊆ B̄(ctr B, r₁)`, is not a field of `BallData` but is what
makes the (C4) fields `bodies_subset_ball` and `segs_le` simultaneously satisfiable.

The construction takes one segment per pair (tube, ball) whose shading actually meets the
piece: `σ = 𝕋 × 𝔅`. That is the honest reading of (C3) for a family with no further
refinement, and it is what makes `fam_disjoint` and the fibre count hold on the nose. -/
theorem exists_segments (cfg : VeryNotSticky.{u}) {bι : Type u} (bs : Finset bι)
    (ctr : bι → EuclideanSpace ℝ (Fin 3)) (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPball : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) (hr1 : (cfg.r₁ : ℝ) ≤ 1) :
    ∃ (σ : Type u) (segs : bι → Finset σ)
      (Y : σ → ShadedBody (EuclideanSpace ℝ (Fin 3))) (fam : σ → Finset cfg.ι),
      (∀ B ∈ bs, (segs B).Nonempty) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B, fam p ⊆ cfg.s) ∧
      (∀ B ∈ bs, (segs B : Set σ).Pairwise fun p q => Disjoint (fam p) (fam q)) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B, (Y p).shade ⊆ P B) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B,
        Kakeya.HasThicknesses (Y p).carrier 4 ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B, ∀ q ∈ segs B,
        Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier) ∧
      (∀ B ∈ bs, ∀ i ∈ cfg.s, ((cfg.T i).shade ∩ P B).Nonempty → ∃ p ∈ segs B, i ∈ fam p) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ fam p, (cfg.T i).shade ∩ P B ⊆ (Y p).shade) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B, (Y p).shade ⊆ ⋃ i ∈ fam p, (cfg.T i).shade) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ fam p, ∃ q : EuclideanSpace ℝ (Fin 3),
        (Y p).carrier ⊆ cthickening ((4 : ℝ) * (cfg.δ : ℝ))
          (AffineSubspace.mk' q (Submodule.span ℝ {(cfg.T i).direction}) :
            Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B, ∀ x ∈ (Y p).shade,
        ((1 : NNReal) : ENNReal) ≤ ((1 : NNReal) : ENNReal) *
            (({i ∈ fam p | x ∈ (cfg.T i).shade}.card : ℕ) : ENNReal) ∧
          (({i ∈ fam p | x ∈ (cfg.T i).shade}.card : ℕ) : ENNReal) ≤
            ((1 : NNReal) : ENNReal) * ((1 : NNReal) : ENNReal)) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B, (Y p).carrier ⊆ closedBall (ctr B) (cfg.r₁ : ℝ)) ∧
      (∀ B ∈ bs, ∀ p ∈ segs B,
        (cfg.δ : ENNReal) ≤ Metric.ethickness.scale ℝ (Y p).carrier) := by
  classical
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  set L : ℝ := (cfg.r₁ : ℝ) / 4 with hLdef
  have hL : (0 : ℝ) ≤ L := by positivity
  have hL1 : 2 * L ≤ 1 := by rw [hLdef]; linarith
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hδL : (cfg.δ : ℝ) ≤ L := by rw [hLdef]; linarith
  have hL4 : (4 : ℝ) * L = (cfg.r₁ : ℝ) := by rw [hLdef]; ring
  have hcover : 2 * ((cfg.δ : ℝ) + (cfg.r₁ : ℝ) / 16) ≤ L := by rw [hLdef]; linarith
  refine ⟨cfg.ι × bι,
    fun B => (cfg.s.filter (fun i => ((cfg.T i).shade ∩ P B).Nonempty)).image (fun i => (i, B)),
    fun p => segShadedBody (cfg.T p.1) (ctr p.2) hL (P p.2) (hPmeas p.2),
    fun p => {p.1}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- segs_nonempty
    intro B hB
    obtain ⟨x, hxP, hxS⟩ := hPne B hB
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxS
    exact ⟨(i, B), Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, ⟨x, hxi, hxP⟩⟩, rfl⟩⟩
  · -- fam_subset
    intro B hB p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    simpa using (Finset.mem_filter.1 hi).1
  · -- fam_disjoint
    intro B hB p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
    have hij : i ≠ j := fun h => hpq (by rw [h])
    simpa using hij
  · -- Y_piece
    intro B hB p hp x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact hx.1.2
  · -- segs_thickness
    intro B hB p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    have hth := hasThicknesses_segCarrierSet (cfg.T i).toTube (ctr B) hL hL1 hδL
    rw [hL4] at hth
    exact hth
  · -- segs_dims
    intro B hB p hp q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
    exact thickness_segCarrierSet_le_two_nsmul (cfg.T i).toTube (cfg.T j).toTube
      (ctr B) (ctr B) hL hL1 hδL
  · -- parent
    intro B hB i hi hne
    exact ⟨(i, B), Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩, rfl⟩,
      Finset.mem_singleton_self i⟩
  · -- into
    intro B hB p hp i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    have hij : i = j := Finset.mem_singleton.1 hi
    subst hij
    intro x hx
    exact ⟨⟨hx.1, hx.2⟩,
      tube_inter_ball_subset_segCarrierSet (cfg.T i).toTube (ctr B) hL hcover
        ⟨(cfg.T i).shade_subset hx.1, hPball B hB hx.2⟩⟩
  · -- back
    intro B hB p hp x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact Set.mem_biUnion (Finset.mem_singleton_self i) hx.1.1
  · -- segs_core
    intro B hB p hp i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    have hij : i = j := Finset.mem_singleton.1 hi
    subst hij
    exact ⟨corePt (cfg.T i).toTube (segStart (cfg.T i).toTube (ctr B) L),
      segCarrierSet_subset_cthickening_line (cfg.T i).toTube (ctr B) hL (by linarith)⟩
  · -- fibre, at `m = Cm = 1`
    intro B hB p hp x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    have hcard : {j ∈ ({i} : Finset cfg.ι) | x ∈ (cfg.T j).shade} = {i} := by
      refine Finset.filter_true_of_mem ?_
      intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      exact hx.1.1
    rw [hcard]
    simp
  · -- the segments fit inside the ball
    intro B hB p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨_, hine⟩ := Finset.mem_filter.1 hi
    obtain ⟨x, hx1, hx2⟩ := hine
    refine segCarrierSet_subset_closedBall_ctr (cfg.T i).toTube (ctr B)
      (ρ := (cfg.r₁ : ℝ) / 16) hL ⟨x, (cfg.T i).shade_subset hx1, hPball B hB hx2⟩ ?_
    rw [hLdef]; linarith
  · -- the segments have thickness scale at least `δ`
    intro B hB p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact le_ethickness_scale_segCarrierSet (cfg.T i).toTube (ctr B) hL

/-! ### The core of `BallData`, and the reduction of `BallData` to the (C4) factoring -/

open scoped Classical in
/-- **The part of `Kakeya.VeryNotSticky.BallData` that the ball cover and the segment family
already supply.**

Its fields are, verbatim, forty-two of the sixty-seven fields of
`Kakeya.VeryNotSticky.BallData` — everything of (C2), (C3) except `segs_dilation`, the working-shading block (C5′) (`Yg`, `Yg_subset`, `Yg_measurable`, `Cg`,
`hCg`, `Yg_mass`), the compatibility and fibre clauses of (C5) read on `Yg`, and the `δ`-ball
covers — together with one extra
clause, `segs_subset_ball`, which is not a `BallData` field but is what makes the (C4) fields
`bodies_subset_ball` and `segs_le` simultaneously satisfiable.

That the field statements really are verbatim is not asserted in prose: it is checked by the
Lean elaborator, since `Kakeya.VeryNotSticky.BallDataCore.toBallData` below builds a
`BallData` out of a `BallDataCore` and the remaining twenty-five fields, and would not
typecheck otherwise; the working-shading block is moreover pinned by
`Kakeya.VeryNotSticky.statement_of_universal_ballData_workingShading`. -/
structure BallDataCore (cfg : VeryNotSticky.{u}) where
  /-- The thickness comparison constant of (C3). -/
  C₀ : NNReal
  /-- `1 ≤ C₀`. -/
  hC₀ : 1 ≤ C₀
  /-- The bounded-overlap constant. -/
  D : ℕ
  /-- (C5′) the *working shading* `Y_g ⊆ Y` of GWZ §9.3: `Y` after the per-tube refinements of
  steps 6–8 (`gwz.txt` l.2024-2041, "abusing notation, we will continue to refer to this as
  `(𝕋, Y)`"), kept apart from the uniform shading of `cfg`, which is Lemma 9.1's hypothesis
  (l.1778) and is never re-established after those steps. The coarse producers take
  `Yg := (cfg.T i).shade`, `Cg := 1`. -/
  Yg : cfg.ι → Set (EuclideanSpace ℝ (Fin 3))
  /-- (C5′) `Y_g(T) ⊆ Y(T)`. -/
  Yg_subset : ∀ i ∈ cfg.s, Yg i ⊆ (cfg.T i).shade
  /-- (C5′) `Y_g` is measurable. -/
  Yg_measurable : ∀ i ∈ cfg.s, MeasurableSet (Yg i)
  /-- (C5′) the loss of the working shading against `Y`; polylogarithmic (heavy balls, Markov
  tier, Lemma 9.2's subset, the dims class), never a power of `δ`. -/
  Cg : NNReal
  /-- `1 ≤ Cg`. -/
  hCg : 1 ≤ Cg
  /-- (C5′) `(𝕋, Y_g)` is a `⪆ 1` refinement of `(𝕋, Y)` (`gwz.txt` l.2028, 2030, 2036-2038). -/
  Yg_mass : (Cg : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
    ∑ i ∈ cfg.s, volume (Yg i)
  /-- The index type of the ball family `𝔅`. -/
  bι : Type u
  /-- The index type of the tube segments. -/
  σ : Type u
  /-- (C2) the family `𝔅`. -/
  bs : Finset bι
  /-- (C2) `𝔅` is non-empty. -/
  bs_nonempty : bs.Nonempty
  /-- (C2) the centres. -/
  ctr : bι → EuclideanSpace ℝ (Fin 3)
  /-- (C2) the subordinate partition. -/
  P : bι → Set (EuclideanSpace ℝ (Fin 3))
  /-- (C2) `B̂ ⊆ B`. -/
  P_subset_ball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ)
  /-- (C2) the pieces are disjoint. -/
  P_disjoint : (bs : Set bι).PairwiseDisjoint P
  /-- (C2) the pieces are measurable. -/
  P_measurable : ∀ B ∈ bs, MeasurableSet (P B)
  /-- (C2) the pieces cover the working shading `Y_g`. -/
  P_cover : ∀ i ∈ cfg.s, Yg i ⊆ ⋃ B ∈ bs, P B
  /-- (C2) bounded overlap. -/
  ballOverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
    (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ D
  /-- (C3) the segments. -/
  segs : bι → Finset σ
  /-- (C3) the shading. -/
  Y : σ → ShadedBody (EuclideanSpace ℝ (Fin 3))
  /-- (C3) the parent families. -/
  fam : σ → Finset cfg.ι
  /-- (C5) each `𝕋_B` is non-empty. -/
  segs_nonempty : ∀ B ∈ bs, (segs B).Nonempty
  /-- (C3) the parent families lie in `𝕋`. -/
  fam_subset : ∀ B ∈ bs, ∀ p ∈ segs B, fam p ⊆ cfg.s
  /-- (C3) the parent families are disjoint. -/
  fam_disjoint : ∀ B ∈ bs, (segs B : Set σ).Pairwise fun p q => Disjoint (fam p) (fam q)
  /-- (C3) the shading lies in the piece. -/
  Y_piece : ∀ B ∈ bs, ∀ p ∈ segs B, (Y p).shade ⊆ P B
  /-- (C3) the thickness profile. -/
  segs_thickness : ∀ B ∈ bs, ∀ p ∈ segs B,
    HasThicknesses (Y p).carrier C₀ ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]
  /-- (C3) comparable thicknesses. -/
  segs_dims : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ q ∈ segs B,
    Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier
  /-- (C5) every tube whose working shading meets a piece has a parent segment. -/
  parent : ∀ B ∈ bs, ∀ i ∈ cfg.s, (Yg i ∩ P B).Nonempty → ∃ p ∈ segs B, i ∈ fam p
  /-- (C5) `Y_g(T) ∩ B̂ ⊆ Y_B(T_B)`. -/
  into : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ fam p, Yg i ∩ P B ⊆ (Y p).shade
  /-- (C5) `Y_B(T_B) ⊆ ⋃ Y_g(T)`. -/
  back : ∀ B ∈ bs, ∀ p ∈ segs B, (Y p).shade ⊆ ⋃ i ∈ fam p, Yg i
  /-- (C3) the segment lies along the core line of each parent. -/
  segs_core : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ fam p,
    ∃ q : EuclideanSpace ℝ (Fin 3), (Y p).carrier ⊆
      cthickening ((C₀ : ℝ) * (cfg.δ : ℝ))
        (AffineSubspace.mk' q (Submodule.span ℝ {(cfg.T i).direction}) :
          Set (EuclideanSpace ℝ (Fin 3)))
  /-- (C5) the fibre-count scale. -/
  m : NNReal
  /-- (C5) the fibre-count comparison constant. -/
  Cm : NNReal
  /-- `1 ≤ Cm`. -/
  hCm : 1 ≤ Cm
  /-- (C5) the fibre count, on the working shading. -/
  fibre : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ x ∈ (Y p).shade,
    (m : ENNReal) ≤ Cm * {i ∈ fam p | x ∈ Yg i}.card ∧
      (({i ∈ fam p | x ∈ Yg i}.card : ℕ) : ENNReal) ≤ Cm * m
  /-- The index type of the `δ`-ball covers. -/
  γ : Type u
  /-- The `δ`-ball cover of a segment. -/
  cov : σ → Finset γ
  /-- The centre of a `δ`-ball of a cover. -/
  covCtr : γ → EuclideanSpace ℝ (Fin 3)
  /-- Each cover is a `D`-boundedly overlapping cover of the segment. -/
  cov_isCover : ∀ B ∈ bs, ∀ p ∈ segs B,
    IsBoundedlyOverlappingCover (cov p) covCtr (fun _ => (cfg.δ : ℝ)) D (Y p).carrier
  /-- Every `δ`-ball of a cover meets the segment. -/
  cov_meets : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ cov p,
    (ball (covCtr i) (cfg.δ : ℝ) ∩ (Y p).carrier).Nonempty
  /-- **Not a `BallData` field**: the segments fit inside their ball. It is what makes the
  (C4) fields `bodies_subset_ball` and `segs_le` simultaneously satisfiable, and the
  construction supplies it. -/
  segs_subset_ball : ∀ B ∈ bs, ∀ p ∈ segs B,
    (Y p).carrier ⊆ closedBall (ctr B) (cfg.r₁ : ℝ)
  /-- **Not a `BallData` field**: the thickness scale of a segment is at least `δ`. With
  `segs_subset_ball` this is what lets the (C4) factoring be run on the segment family of a
  ball by `Kakeya.ConvexSpaceBody.nonempty_biasedFactorization`. -/
  segs_scale : ∀ B ∈ bs, ∀ p ∈ segs B,
    (cfg.δ : ENNReal) ≤ Metric.ethickness.scale ℝ (Y p).carrier

open scoped Classical in
/-- **`BallData` is exactly `BallDataCore` plus the (C4) factoring, `segs_dilation` (with its
constant `Cdil`) and `segs_density`.**

The twenty-five explicit arguments are the twenty-five fields of
`Kakeya.VeryNotSticky.BallData` that `Kakeya.VeryNotSticky.exists_ballDataCore` does *not*
supply. Their statements are copied verbatim from the structure, so this definition is a
compiler-checked check of the split: `BallData` has sixty-seven fields, `BallDataCore` gives
forty-two of them (the six of the working-shading block (C5′) among them), and these are the
other twenty-five. -/
def BallDataCore.toBallData {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    (CF : NNReal) (hCF : 1 ≤ CF) (Cdil : NNReal) (hCdil : 1 ≤ Cdil)
    (Cbias : NNReal) (hCbias : 1 ≤ Cbias)
    (c₁ : NNReal) (hc₁ : 0 < c₁)
    (ω : Type u) [decidableEqω : DecidableEq ω]
    (bodies : core.bι → Finset ω)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (blk : core.σ → ω) (w₁ : NNReal)
    (blk_mem : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, blk p ∈ bodies B)
    (segs_le : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, (core.Y p).toConvexSpaceBody ≤ Wb (blk p))
    (bodies_thickness : ∀ B ∈ core.bs, ∀ j ∈ bodies B,
      HasThicknesses (Wb j).carrier core.C₀ ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)])
    (bodies_subset_ball : ∀ B ∈ core.bs, ∀ j ∈ bodies B,
      (Wb j).carrier ⊆ closedBall (core.ctr B) (cfg.r₁ : ℝ))
    (bodies_w₁ : ∀ B ∈ core.bs, ∀ j ∈ bodies B,
      Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) ≤
          2 * w₁ ∧
        (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j).carrier
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1))
    (frostman : ∀ B ∈ core.bs, ∀ j ∈ bodies B,
      ConvexSpaceBody.IsFrostmanIn ((core.segs B).filter fun p => blk p = j)
        (fun p => (core.Y p).toConvexSpaceBody) (Wb j) CF)
    (biasedDensity : ∀ B ∈ core.bs, ∀ j ∈ bodies B,
      ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ Wb j →
        densityIn ((core.segs B).filter fun p => blk p = j)
            (fun p => (core.Y p).toConvexSpaceBody) K ≤
          (Cbias : ENNReal) *
            (volume K.carrier / volume (Wb j).carrier) ^ cfg.ϱ *
            densityIn ((core.segs B).filter fun p => blk p = j)
              (fun p => (core.Y p).toConvexSpaceBody) (Wb j))
    (bodies_antiClustering : ∀ B ∈ core.bs,
      maxDensity (bodies B) Wb ≤ (Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)))
    (segs_dilation : ∀ B ∈ core.bs,
      (cfg.r₁ : ENNReal) ^ 2 * maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (Cdil : ENNReal) * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody))
    (segs_density : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
        volume (core.Y p).shade) :
    BallData cfg where
  C₀ := core.C₀
  hC₀ := core.hC₀
  CF := CF
  hCF := hCF
  Cdil := Cdil
  hCdil := hCdil
  Cbias := Cbias
  hCbias := hCbias
  c₁ := c₁
  hc₁ := hc₁
  D := core.D
  Yg := core.Yg
  Yg_subset := core.Yg_subset
  Yg_measurable := core.Yg_measurable
  Cg := core.Cg
  hCg := core.hCg
  Yg_mass := core.Yg_mass
  bι := core.bι
  σ := core.σ
  ω := ω
  decidableEqω := decidableEqω
  bs := core.bs
  bs_nonempty := core.bs_nonempty
  ctr := core.ctr
  P := core.P
  P_subset_ball := core.P_subset_ball
  P_disjoint := core.P_disjoint
  P_measurable := core.P_measurable
  P_cover := core.P_cover
  ballOverlap := core.ballOverlap
  segs := core.segs
  Y := core.Y
  fam := core.fam
  segs_nonempty := core.segs_nonempty
  fam_subset := core.fam_subset
  fam_disjoint := core.fam_disjoint
  Y_piece := core.Y_piece
  segs_thickness := core.segs_thickness
  segs_dims := core.segs_dims
  segs_dilation := segs_dilation
  bodies := bodies
  Wb := Wb
  blk := blk
  w₁ := w₁
  blk_mem := blk_mem
  segs_le := segs_le
  bodies_thickness := bodies_thickness
  bodies_subset_ball := bodies_subset_ball
  bodies_w₁ := bodies_w₁
  frostman := frostman
  biasedDensity := biasedDensity
  bodies_antiClustering := bodies_antiClustering
  segs_density := segs_density
  parent := core.parent
  into := core.into
  back := core.back
  segs_core := core.segs_core
  m := core.m
  Cm := core.Cm
  hCm := core.hCm
  fibre := core.fibre
  γ := core.γ
  cov := core.cov
  covCtr := core.covCtr
  cov_isCover := core.cov_isCover
  cov_meets := core.cov_meets

/-- **The shaded union of a configuration is non-empty**, since its fullness is at least the
positive number `δ^η`. -/
lemma iUnionShade_nonempty (cfg : VeryNotSticky.{u}) :
    (⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hzero : ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hemp : ((cfg.T i).toShadedBody).shade = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hmem : x ∈ (⋃ i ∈ cfg.s, (cfg.T i).shade) := Set.mem_biUnion hi hx
      rw [h] at hmem
      exact hmem
    rw [hemp]
    simp
  have hf0 : (ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) : ENNReal) = 0 := by
    rw [ShadedBody.fullness_def, hzero]
    simp
  have hf0' : ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) = 0 := by
    exact_mod_cast hf0
  have hpos : 0 < cfg.δ ^ (2 * cfg.η) := NNReal.rpow_pos cfg.hδ
  have := cfg.fullness_ge
  rw [hf0'] at this
  exact absurd (le_antisymm this hpos.le) (ne_of_gt hpos)

/-- **The ball radius is at most one.** -/
lemma r₁_le_one (cfg : VeryNotSticky.{u}) : (cfg.r₁ : ℝ) ≤ 1 := by
  have : cfg.r₁ ≤ 1 := NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le
  exact_mod_cast this

/-- **Forty-two of the sixty-seven fields of `Kakeya.VeryNotSticky.BallData` are constructible
for every configuration**, at the single scale condition `16δ ≤ r₁` — which is an eventual
condition in `δ` whenever `exscal < 1`, and in particular under
`Kakeya.VeryNotSticky.CaseParams.scale`.

This is the (C2) ball cover of `Kakeya.VeryNotSticky.exists_ballCover`, the segment family of
`Kakeya.VeryNotSticky.exists_segments` and the `δ`-ball covers of
`Kakeya.VeryNotSticky.exists_deltaCovers`, assembled at the common overlap constant
`Kakeya.VeryNotSticky.ballCoverConstant`, the thickness constant `C₀ = 4` and the *exact*
fibre count `m = Cm = 1`.

The two constants that (C4) also reads, the thickness constant `C₀` and the overlap constant
`D`, are left **free** above their construction values `4` and
`Kakeya.VeryNotSticky.ballCoverConstant`: both clauses only weaken as the constants grow, so a
producer of the (C4) factoring may enlarge them to whatever its bodies need without redoing
any of this.

What is left is `Kakeya.VeryNotSticky.BallDataCore.toBallData`'s twenty-five arguments: the
(C4) factoring, `segs_dilation` with its constant `Cdil`, and `segs_density`. The last of these
is *not* uniform in
`cfg`: by `Kakeya.VeryNotSticky.volume_segCarrierSet_le` it demands
`|Y(T) ∩ B̂| ≳ c₁ δ^η L δ²` for **every** piece the shading of `T` meets — and `parent` allows
no piece to be dropped — so a configuration whose shading has an isolated component of tiny
positive measure admits no `BallData` at all. That is the structural reason the construction
has to produce `cfg` and `bd` together rather than `bd` from a given `cfg`, and it is why the
forty-two fields here are exactly the ones that *are* uniform in `cfg`. The working shading
of (C5′) is the uniform shading itself, `Yg := (cfg.T i).shade` at loss `Cg := 1`. -/
theorem exists_ballDataCore (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 4 ≤ C₀)
    {D : ℕ} (hD : ballCoverConstant ≤ D)
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) : Nonempty (BallDataCore cfg) := by
  classical
  have hC₀1 : (1 : NNReal) ≤ C₀ := le_trans (by norm_num) hC₀
  have hC₀R : (4 : ℝ) ≤ ((C₀ : NNReal) : ℝ) := by exact_mod_cast hC₀
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hr₁0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
  obtain ⟨bι, bs, ctr, P, hbsne, hPball16, hPball, hPdisj, hPmeas, hPcov, hoverlap, hPne⟩ :=
    exists_ballCover cfg (iUnionShade_nonempty cfg)
  obtain ⟨σ, segs, Y, fam, hsne, hfsub, hfdisj, hYp, hth, hdims, hpar, hinto, hback,
      hcore, hfib, hball, hscale⟩ :=
    exists_segments cfg bs ctr P hPmeas hPball16 hPne hδr (r₁_le_one cfg)
  obtain ⟨γ, cov, covCtr, hcov, hmeets⟩ := exists_deltaCovers (δ := cfg.δ) cfg.hδ Y
  refine ⟨{
    C₀ := C₀
    hC₀ := hC₀1
    D := D
    Yg := fun i ↦ (cfg.T i).shade
    Yg_subset := fun _ _ ↦ subset_rfl
    Yg_measurable := fun i _ ↦ (cfg.T i).measurableSet_shade
    Cg := 1
    hCg := le_rfl
    Yg_mass := by simp
    bι := bι
    σ := σ
    bs := bs
    bs_nonempty := hbsne
    ctr := ctr
    P := P
    P_subset_ball := hPball
    P_disjoint := hPdisj
    P_measurable := fun B _ => hPmeas B
    P_cover := hPcov
    ballOverlap := fun x t hts hball => le_trans (hoverlap x t hts hball) hD
    segs := segs
    Y := Y
    fam := fam
    segs_nonempty := hsne
    fam_subset := hfsub
    fam_disjoint := hfdisj
    Y_piece := hYp
    segs_thickness := ?_
    segs_dims := hdims
    parent := hpar
    into := hinto
    back := hback
    segs_core := ?_
    m := 1
    Cm := 1
    hCm := le_refl 1
    fibre := hfib
    γ := γ
    cov := cov
    covCtr := covCtr
    cov_isCover := fun _ _ p _ =>
      ⟨(hcov p).subset_iUnion, fun x => le_trans ((hcov p).card_filter_le x) hD⟩
    cov_meets := fun _ _ p _ => hmeets p
    segs_subset_ball := hball
    segs_scale := hscale }⟩
  · -- `segs_thickness`, weakened from the absolute constant `4` to `C₀ ≥ 4`
    intro B hB p hp
    intro k
    obtain ⟨hlo, hhi⟩ := hth B hB p hp k
    have htk : 0 ≤ (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) k := by
      have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
      rcases hk with rfl | rfl | rfl <;> simpa using by assumption
    have h4pos : (0 : ℝ) < 4 := by norm_num
    have hinv : ((C₀ : NNReal) : ℝ)⁻¹ ≤ (((4 : NNReal) : ℝ))⁻¹ := by
      have h4' : ((4 : NNReal) : ℝ) = 4 := by norm_num
      rw [h4']
      exact inv_anti₀ h4pos hC₀R
    constructor
    · exact le_trans (mul_le_mul_of_nonneg_right hinv htk) hlo
    · refine le_trans hhi (mul_le_mul_of_nonneg_right ?_ htk)
      have h4' : ((4 : NNReal) : ℝ) = 4 := by norm_num
      rw [h4']
      exact hC₀R
  · -- `segs_core`, at the larger constant
    intro B hB p hp i hi
    obtain ⟨q, hq⟩ := hcore B hB p hp i hi
    refine ⟨q, subset_trans hq (Metric.cthickening_mono ?_ _)⟩
    exact mul_le_mul_of_nonneg_right hC₀R hδ0

/-- **The scale hypothesis of `Kakeya.VeryNotSticky.exists_ballDataCore` holds eventually.**

`16δ ≤ δ^{exscal}` for all small `δ` as soon as `exscal < 1`, which
`Kakeya.VeryNotSticky.CaseParams.scale` gives with room (`exscal < 1/2`). So the construction
of the forty-two fields costs the producer only a threshold on `δ`, of the same kind as every
other clause of `Kakeya.VeryNotSticky.CaseScale`. -/
theorem eventually_sixteen_mul_le_rpow {exscal : ℝ} (hex1 : exscal < 1) :
    ∀ᶠ δ : NNReal in nhdsWithin 0 (Set.Ioi 0), 16 * (δ : ℝ) ≤ ((δ ^ exscal : NNReal) : ℝ) := by
  have hgap : (0 : ℝ) < 1 - exscal := by linarith
  filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos hgap
      (show (0 : ENNReal) < (16 : ENNReal)⁻¹ by simp), self_mem_nhdsWithin] with d hd hd0
  have hdpos : (0 : NNReal) < d := by simpa using hd0
  have hdne : (d : ENNReal) ≠ 0 := by simpa using hdpos.ne'
  have hdtop : (d : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- `16 * d ≤ d ^ exscal` in `ℝ≥0∞`
  have key : (16 : ENNReal) * (d : ENNReal) ≤ (d : ENNReal) ^ exscal := by
    have hsplit : (d : ENNReal) ^ exscal
        = (d : ENNReal) * ((d : ENNReal) ^ (1 - exscal))⁻¹ := by
      rw [← ENNReal.rpow_neg]
      nth_rewrite 2 [← ENNReal.rpow_one (d : ENNReal)]
      rw [← ENNReal.rpow_add _ _ hdne hdtop]
      congr 1
      ring
    rw [hsplit]
    have hinv : (16 : ENNReal) ≤ ((d : ENNReal) ^ (1 - exscal))⁻¹ := by
      have := ENNReal.inv_le_inv.2 hd
      simpa using this
    calc (16 : ENNReal) * (d : ENNReal) = (d : ENNReal) * 16 := by ring
      _ ≤ (d : ENNReal) * ((d : ENNReal) ^ (1 - exscal))⁻¹ := by gcongr
  -- transfer to `ℝ`
  have keyN : (16 : NNReal) * d ≤ d ^ exscal := by
    have hcoe : ((16 * d : NNReal) : ENNReal) ≤ ((d ^ exscal : NNReal) : ENNReal) := by
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hdpos.ne']
      simpa using key
    exact_mod_cast hcoe
  have := NNReal.coe_le_coe.2 keyN
  simpa using this

/-! ### The `ρ`-count of a covering family, and why cardinality cannot supply `rho_count` -/

set_option maxHeartbeats 1000000 in
/-- **The mass of a family is at most its maximal density times the mass of any covering
family**: if every body of `s'` sits inside some member of `t`, then
`∑_{i ∈ s'} |V i| ≤ Δ_max(𝕍') ∑_{j ∈ t} |K j|`.

Neither essential distinctness of the cover nor any geometric hypothesis is used: the sum is
split over a choice of covering index and each fibre is bounded by
`Kakeya.sum_volume_le_maxDensity_mul_volume`.

This is the sharpest lower bound on `|t|` that *counting* supplies, and
`Kakeya.VeryNotSticky.card_cover_ge_of_cover` below turns it into one. -/
theorem sum_volume_le_maxDensity_mul_sum_cover {ι κ : Type*} (s' : Finset ι) (t : Finset κ)
    (V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (K : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hcov : ∀ i ∈ s', ∃ j ∈ t, V i ≤ K j) :
    ∑ i ∈ s', volume (V i).carrier ≤
      maxDensity s' V * ∑ j ∈ t, volume (K j).carrier := by
  classical
  rcases Finset.eq_empty_or_nonempty s' with rfl | hs'
  · simp
  obtain ⟨i₀, hi₀⟩ := hs'
  obtain ⟨j₀, hj₀, -⟩ := hcov i₀ hi₀
  haveI : Nonempty κ := ⟨j₀⟩
  choose! f hf hfle using hcov
  have hmaps : ∀ i ∈ s', f i ∈ t := hf
  have hstep : ∑ i ∈ s', volume (V i).carrier
      = ∑ j ∈ t, ∑ i ∈ s' with f i = j, volume (V i).carrier :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hstep2 : ∀ j ∈ t, (∑ i ∈ s' with f i = j, volume (V i).carrier) ≤
      ∑ i ∈ s' with V i ≤ K j, volume (V i).carrier := by
    intro j _
    refine Finset.sum_le_sum_of_subset ?_
    intro i hi
    obtain ⟨hi', hij⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨hi', hij ▸ hfle i hi'⟩
  calc ∑ i ∈ s', volume (V i).carrier
      = ∑ j ∈ t, ∑ i ∈ s' with f i = j, volume (V i).carrier := hstep
    _ ≤ ∑ j ∈ t, ∑ i ∈ s' with V i ≤ K j, volume (V i).carrier :=
        Finset.sum_le_sum hstep2
    _ ≤ ∑ j ∈ t, maxDensity s' V * volume (K j).carrier :=
        Finset.sum_le_sum fun j _ => sum_volume_le_maxDensity_mul_volume s' V (K j)
    _ = maxDensity s' V * ∑ j ∈ t, volume (K j).carrier := by
        rw [Finset.mul_sum]

/-- **The cardinality lower bound a covering family obeys.**

If every body of `s'` has volume at least `v` and every member of the cover has volume at most
`w`, then `v · |s'| ≤ Δ_max(𝕍') · w · |t|`.

This is the *whole* of what counting gives about the size of a `ρ`-tube family covering a
`δ`-tube family, and it is why the field `Kakeya.VeryNotSticky.rho_count` cannot be recovered
for a refined family from cardinality: with `v ≍ δ²`, `w ≍ ρ²` and
`Δ_max ≤ δ^{-η}` it reads `|t| ≳ |s'| δ² ρ^{-2} δ^{η}`, and `|s'| δ² ≤ Δ_max |B_1| ≤ δ^{-η}`
by the same inequality applied with the unit ball as a one-member cover — so the bound never
exceeds `ρ^{-2}`, whereas `rho_count` asserts `ρ^{-2-ζ}`. The gain `ρ^{-ζ}` is exactly the
non-trivial content of the hypothesis and has to be *inherited* from the unrefined family, not
recomputed. -/
theorem card_cover_ge_of_cover {ι κ : Type*} (s' : Finset ι) (t : Finset κ)
    (V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (K : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hcov : ∀ i ∈ s', ∃ j ∈ t, V i ≤ K j)
    {v w : ENNReal} (hv : ∀ i ∈ s', v ≤ volume (V i).carrier)
    (hw : ∀ j ∈ t, volume (K j).carrier ≤ w) :
    v * (s'.card : ENNReal) ≤ maxDensity s' V * (w * (t.card : ENNReal)) := by
  calc v * (s'.card : ENNReal) = ∑ _i ∈ s', v := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ s', volume (V i).carrier := Finset.sum_le_sum hv
    _ ≤ maxDensity s' V * ∑ j ∈ t, volume (K j).carrier :=
        sum_volume_le_maxDensity_mul_sum_cover s' t V K hcov
    _ ≤ maxDensity s' V * (w * (t.card : ENNReal)) := by
        gcongr
        calc ∑ j ∈ t, volume (K j).carrier ≤ ∑ _j ∈ t, w := Finset.sum_le_sum hw
          _ = w * (t.card : ENNReal) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ### The volume of a segment, for `segs_density` -/

section SegVolume

variable {δ : NNReal}

/-- The segment contains a `δ`-ball, so its volume is bounded below by that of a `δ`-ball. -/
lemma volume_closedBall_le_volume_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    volume (closedBall (corePt T (coreParam T c)) (δ : ℝ)) ≤ volume (segCarrierSet T c L) :=
  measure_mono (closedBall_subset_segCarrierSet T c hL)

/-- **The volume of a segment is at most `8(L+δ)δ²`**, by the flag-box estimate
`Kakeya.volume_le_prod_ethickness` applied to the thickness profile of the segment.

Together with `Kakeya.VeryNotSticky.volume_closedBall_le_volume_segCarrierSet` this pins the
segment's volume to `≍ Lδ²` and turns the field
`Kakeya.VeryNotSticky.BallData.segs_density` into the concrete demand
`|Y(T) ∩ B̂| ≳ c₁ δ^{2η} L δ²` on the shading — which is the demand that forces the *shading*, and
hence `cfg` itself, to be refined alongside `bd`. -/
lemma volume_segCarrierSet_le (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    volume (segCarrierSet T c L) ≤
      8 * (ENNReal.ofReal (L + (δ : ℝ)) * (δ : ENNReal) * (δ : ENNReal)) := by
  have hbdd : Bornology.IsBounded (segCarrierSet T c L) :=
    Metric.isBounded_closedBall.subset (segCarrierSet_subset_closedBall T c hL)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hprod := _root_.volume_le_prod_ethickness (E := EuclideanSpace ℝ (Fin 3))
    (segCarrierSet T c L)
  rw [hfr] at hprod
  have he0 : Metric.ethickness ℝ (segCarrierSet T c L) 0 ≤ ENNReal.ofReal (L + (δ : ℝ)) := by
    rw [Metric.ethickness_thickness' hbdd]
    exact ENNReal.ofReal_le_ofReal (thickness_segCarrierSet_zero_le T c hL)
  have hen : ∀ n : ℕ, 1 ≤ n →
      Metric.ethickness ℝ (segCarrierSet T c L) n ≤ (δ : ENNReal) := by
    intro n hn
    rw [Metric.ethickness_thickness' hbdd, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (thickness_segCarrierSet_le T c hL hn)
  refine hprod.trans ?_
  have hexp : ∏ i ∈ Finset.range 3, Metric.ethickness ℝ (segCarrierSet T c L) i =
      Metric.ethickness ℝ (segCarrierSet T c L) 0 *
        Metric.ethickness ℝ (segCarrierSet T c L) 1 *
        Metric.ethickness ℝ (segCarrierSet T c L) 2 := by
    simp [Finset.prod_range_succ, mul_assoc]
  rw [hexp]
  have h8 : (2 : ENNReal) ^ 3 = 8 := by norm_num
  rw [h8]
  exact mul_le_mul_left'
    (mul_le_mul' (mul_le_mul' he0 (hen 1 (by norm_num))) (hen 2 (by norm_num))) 8


end SegVolume
