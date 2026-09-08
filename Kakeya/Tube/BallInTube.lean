/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Topology.CoveringNumber
public import Kakeya.Thickening
public import Kakeya.Tube.Basic

/-!
# Balls inside capsules, and thickenings of subsets of a tube

A *capsule* is a closed neighbourhood `Metric.cthickening s S` of a compact set `S`; the carrier
of a `δ`-tube is the capsule of radius `δ` around its core segment
(`Tube.carrier_eq_cthickening`), and so is the carrier of a dilate of a tube
(`Kakeya.Tube.dilate_carrier_eq_cthickening`). This file collects the two facts about capsules
that drive the "fullness" estimate of GWZ Lemma 5.11:

* `Kakeya.exists_ball_subset_cthickening_inter_ball`: every point `x` of a capsule of radius `s`
  admits, at every scale `r ≤ 2 * s`, a ball of radius `r / 8` contained in the capsule *and* in
  `Metric.ball x r`. The capsule is "non-degenerate at every one of its points at every scale
  below its own width".
* `Kakeya.volume_cthickening_le_mul_volume_inter_cthickening` (GWZ Lemma 5.8 in the capsule
  case): for `A` inside a capsule `K` and `r ≤ 2 * s`, the whole `r`-neighbourhood of `A` has
  volume comparable to the part of it lying inside `K`.

It also records the lower bound on the volume of an `r`-neighbourhood of a subset of a tube:

* `Tube.le_volume_cthickening`: the `2ρ`-neighbourhood of `Y ⊆ T.carrier` has volume at least a
  dimensional constant times `(|Y| / |T|) * ρ ^ (n - 1)`.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya

section BallInCapsule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A small ball inside a capsule, near a prescribed point.** Let `K = cthickening s S` be the
closed `s`-neighbourhood of a compact set `S`, let `x ∈ K` and let `0 < r ≤ 2 * s`. Then some ball
of radius `r / 8` is contained in `K ∩ Metric.ball x r`.

The point `x` may sit on the boundary of `K`, so the ball has to be pushed inwards: one takes a
point `z ∈ S` with `dist x z ≤ s` and slides from `x` towards `z` by `r / 4` (or lands on `z`
itself, if it is already that close). -/
theorem exists_ball_subset_cthickening_inter_ball {S : Set E} (hS : IsCompact S) {s r : ℝ}
    (hr : 0 < r) (hrs : r ≤ 2 * s) {x : E} (hx : x ∈ Metric.cthickening s S) :
    ∃ p : E, Metric.ball p (r / 8) ⊆ Metric.cthickening s S ∩ Metric.ball x r := by
  have hs : 0 < s := by linarith
  rw [hS.cthickening_eq_biUnion_closedBall hs.le] at hx
  simp only [Set.mem_iUnion₂] at hx
  rcases hx with ⟨z, hz, hxm⟩
  have hxz : dist x z ≤ s := (Metric.mem_closedBall.mp hxm)
  have key1 : ∀ p : E, dist p z + r / 8 ≤ s → Metric.ball p (r / 8) ⊆ Metric.cthickening s S := by
    intro p hp w hw
    have hwp : dist w p < r / 8 := Metric.mem_ball.mp hw
    have hwz : dist w z < s := by
      linarith [dist_triangle w p z, hwp, hp]
    exact Metric.closedBall_subset_cthickening hz s (Metric.mem_closedBall.mpr (le_of_lt hwz))
  have key2 : ∀ p : E, dist p x + r / 8 ≤ r → Metric.ball p (r / 8) ⊆ Metric.ball x r := by
    intro p hp w hw
    have hwp : dist w p < r / 8 := Metric.mem_ball.mp hw
    exact Metric.mem_ball.mpr (by
      linarith [dist_triangle w p x, hwp, hp])
  have hord := le_or_gt (dist x z) (r / 4)
  rcases hord with hxz_le | hzx_gt
  · refine ⟨z, Set.subset_inter (key1 z ?_) (key2 z ?_)⟩
    · simpa [dist_self] using (show r / 8 ≤ s by linarith)
    · have hzx2 : dist z x ≤ r / 4 := by
        simpa [dist_comm] using hxz_le
      linarith
  · let t : ℝ := (r / 4) / ‖z - x‖
    let q : E := x + t • (z - x)
    have hr4 : 0 < r / 4 := by positivity
    have hzxn : r / 4 < ‖z - x‖ := by
      rwa [← dist_eq_norm, dist_comm]
    have hnz : 0 < ‖z - x‖ := lt_trans hr4 hzxn
    have ht_pos : 0 < t := by
      dsimp [t]
      exact div_pos hr4 hnz
    have ht_lt : t < 1 := by
      dsimp [t]
      rw [div_lt_iff₀ hnz]
      simpa using hzxn
    have hqx : q - x = t • (z - x) := by
      dsimp [q]
      abel
    have hqz : q - z = (t - 1) • (z - x) := by
      calc
        q - z = (q - x) - (z - x) := by abel
        _ = t • (z - x) - (z - x) := by rw [hqx]
        _ = (t - 1) • (z - x) := by rw [sub_smul, one_smul]
    have ht_norm : t * ‖z - x‖ = r / 4 := by
      dsimp [t]
      exact div_mul_cancel₀ (r / 4) (ne_of_gt hnz)
    have ht1 : t - 1 < 0 := by linarith
    have hnorm_qz : ‖q - z‖ = ‖z - x‖ - r / 4 := by
      rw [hqz, norm_smul]
      rw [Real.norm_eq_abs, abs_of_neg ht1, neg_sub]
      rw [← ht_norm]
      ring
    have hdqz : dist q z = dist x z - r / 4 := by
      calc
        dist q z = ‖q - z‖ := by rw [dist_eq_norm]
        _ = ‖z - x‖ - r / 4 := hnorm_qz
        _ = dist x z - r / 4 := by
          have hzx : ‖z - x‖ = dist x z := by
            simpa [dist_comm] using (dist_eq_norm z x).symm
          rw [hzx]
    have hnorm_qx : ‖q - x‖ = r / 4 := by
      rw [hqx, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos ht_pos]
      exact ht_norm
    have hdqx : dist q x = r / 4 := by
      rw [dist_eq_norm]
      exact hnorm_qx
    have hq_s : dist q z + r / 8 ≤ s := by
      rw [hdqz]
      linarith
    have hq_r : dist q x + r / 8 ≤ r := by
      rw [hdqx]
      linarith
    exact ⟨q, Set.subset_inter (key1 q hq_s) (key2 q hq_r)⟩

end BallInCapsule

section VolumeInCapsule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The dimensional constant `48 ^ n` in
`Kakeya.volume_cthickening_le_mul_volume_inter_cthickening`.**

It comes from comparing balls of radius `6 * r` (which cover the `r`-neighbourhood of `A` once
centred at a maximal `4 * r`-separated net in `A`) with the disjoint balls of radius `r / 8`
supplied by `Kakeya.exists_ball_subset_cthickening_inter_ball`. -/
@[nolint defsWithUnderscore]
def volume_cthickening_le_mul_volume_inter_cthickening.C (n : ℕ) : ℕ := 48 ^ n

/-- The dimensional constant of
`Kakeya.volume_cthickening_le_mul_volume_inter_cthickening` is positive. -/
theorem volume_cthickening_le_mul_volume_inter_cthickening.C_pos (n : ℕ) : 0 < C n := by
  unfold C
  exact pow_pos (by norm_num) n

/-- **GWZ Lemma 5.8, capsule case.** Let `K = cthickening s S` be the closed `s`-neighbourhood of
a compact set `S`, let `A ⊆ K` and let `0 < r ≤ 2 * s`. Then the full `r`-neighbourhood of `A` has
volume at most a dimensional constant times the volume of the part of that neighbourhood lying
inside `K`.

No measurability of `A` is needed: the upper bound is subadditivity of the outer measure over a
finite cover, and the lower bound only uses disjoint balls contained in the intersection. -/
theorem volume_cthickening_le_mul_volume_inter_cthickening {S : Set E} (hS : IsCompact S)
    {s r : ℝ} (hr : 0 < r) (hrs : r ≤ 2 * s) {A : Set E} (hA : A ⊆ Metric.cthickening s S) :
    volume (Metric.cthickening r A) ≤
      (volume_cthickening_le_mul_volume_inter_cthickening.C (Module.finrank ℝ E) : ENNReal) *
        volume (Metric.cthickening s S ∩ Metric.cthickening r A) := by
  classical
  set K : Set E := Metric.cthickening s S with hKdef
  set Theta : Set E := Metric.cthickening r A with hTheta
  set v1 : ENNReal := volume (Metric.ball (0 : E) 1) with hv1
  have hAbdd : Bornology.IsBounded A := (hS.cthickening (r := s)).isBounded.subset hA
  let w : NNReal := ⟨3 * r, by positivity⟩
  have hw : 0 < w := by
    exact_mod_cast (show (0 : ℝ) < 3 * r by positivity)
  obtain ⟨N, hNA, hNsep', hNcover, _⟩ :=
    hAbdd.exists_finset_isSeparated_isCover_closedBall hw
  have hNsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → 2 * r ≤ dist y z := by
    intro y hy z hz hyz
    have hyz' := hNsep' (Finset.mem_coe.mpr hy) (Finset.mem_coe.mpr hz) hyz
    change (w : ENNReal) < edist y z at hyz'
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := w)] at hyz'
    have hdist : (w : ℝ) < dist y z :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg w.coe_nonneg).mp hyz'
    change 3 * r < dist y z at hdist
    simpa [w] using (show 2 * r ≤ dist y z by linarith)
  have hNmax : ∀ x ∈ A, ∃ y ∈ N, dist x y < 4 * r := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hNcover hx) with ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    have hxy' : dist x y ≤ (w : ℝ) := Metric.mem_closedBall.mp hxy
    change dist x y ≤ 3 * r at hxy'
    linarith
  have hex : ∀ y : E, ∃ q : E, y ∈ N → Metric.ball q (r / 8) ⊆ K ∩ Metric.ball y r := by
    intro y
    by_cases hy : y ∈ N
    · obtain ⟨q, hq⟩ := exists_ball_subset_cthickening_inter_ball hS hr hrs (hA (hNA hy))
      exact ⟨q, fun _ => hq⟩
    · exact ⟨y, fun h => absurd h hy⟩
  choose p hp using hex
  -- (1) balls of radius 6*r at the net cover the r-neighbourhood
  have hcover : Theta ⊆ ⋃ y ∈ N, Metric.ball y (6 * r) := by
    intro x hx
    have hx' : x ∈ Metric.thickening (2 * r) A :=
      (Metric.cthickening_subset_thickening' (by positivity) (by linarith) A) hx
    obtain ⟨a, haA, hxa⟩ := Metric.mem_thickening_iff.mp hx'
    obtain ⟨y, hyN, hay⟩ := hNmax a haA
    refine Set.mem_biUnion hyN (Metric.mem_ball.mpr ?_)
    calc dist x y ≤ dist x a + dist a y := dist_triangle _ _ _
      _ < 2 * r + 4 * r := add_lt_add hxa hay
      _ = 6 * r := by ring
  -- (2) upper bound
  have hup : volume Theta ≤
      (N.card : ENNReal) * (ENNReal.ofReal ((6 * r) ^ Module.finrank ℝ E) * v1) := by
    calc volume Theta ≤ volume (⋃ y ∈ N, Metric.ball y (6 * r)) := measure_mono hcover
      _ ≤ ∑ y ∈ N, volume (Metric.ball y (6 * r)) := measure_biUnion_finset_le _ _
      _ = ∑ _y ∈ N, (ENNReal.ofReal ((6 * r) ^ Module.finrank ℝ E) * v1) := by
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [Measure.addHaar_ball_of_pos (μ := volume) y (by positivity)]
      _ = (N.card : ENNReal) * (ENNReal.ofReal ((6 * r) ^ Module.finrank ℝ E) * v1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  -- (3) the small balls sit inside K ∩ Θ and are pairwise disjoint
  have hsub' : ∀ y : E, y ∈ N → Metric.ball (p y) (r / 8) ⊆ K ∩ Theta := by
    intro y hy
    have hball : Metric.ball y r ⊆ Theta :=
      Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_cthickening (hNA hy) r)
    exact (hp y hy).trans (Set.inter_subset_inter_right K hball)
  -- (4) lower bound in the disjoint case
  have hdisj : (↑N : Set E).PairwiseDisjoint (fun y => Metric.ball (p y) (r / 8)) := by
    intro y hy z hz hyz
    have hyN : y ∈ N := by exact_mod_cast hy
    have hzN : z ∈ N := by exact_mod_cast hz
    have h1 : Metric.ball (p y) (r / 8) ⊆ Metric.ball y r :=
      (hp y hyN).trans Set.inter_subset_right
    have h2 : Metric.ball (p z) (r / 8) ⊆ Metric.ball z r :=
      (hp z hzN).trans Set.inter_subset_right
    exact (Metric.ball_disjoint_ball (by linarith [hNsep y hyN z hzN hyz])).mono h1 h2
  -- (4) lower bound on the volume of the disjoint small balls
  have hfd : (N.card : ENNReal) * (ENNReal.ofReal ((r / 8) ^ Module.finrank ℝ E) * v1)
      ≤ volume (K ∩ Theta) := by
    calc (N.card : ENNReal) * (ENNReal.ofReal ((r / 8) ^ Module.finrank ℝ E) * v1)
        = ∑ y ∈ N, volume (Metric.ball (p y) (r / 8)) := by
          rw [Finset.sum_congr rfl fun y _ =>
            Measure.addHaar_ball_of_pos (μ := volume) (p y) (by positivity),
          Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ y ∈ N, Metric.ball (p y) (r / 8)) :=
          (measure_biUnion_finset hdisj (fun y _ => measurableSet_ball)).symm
      _ ≤ volume (K ∩ Theta) := measure_mono (Set.iUnion₂_subset hsub')
  -- (5) arithmetic: (6*r)^n = 48^n * (r/8)^n
  have harith : ENNReal.ofReal ((6 * r) ^ Module.finrank ℝ E)
      = ((48 ^ Module.finrank ℝ E : ℕ) : ENNReal) *
          ENNReal.ofReal ((r / 8) ^ Module.finrank ℝ E) := by
    rw [show (6 : ℝ) * r = 48 * (r / 8) by ring, mul_pow,
      ENNReal.ofReal_mul (by positivity),
      show ((48 : ℝ) ^ Module.finrank ℝ E) = ((48 ^ Module.finrank ℝ E : ℕ) : ℝ) by
        push_cast
        ring,
      ENNReal.ofReal_natCast]
  calc
    volume Theta ≤ (N.card : ENNReal) *
        (ENNReal.ofReal ((6 * r) ^ Module.finrank ℝ E) * v1) := hup
    _ = ((48 ^ Module.finrank ℝ E : ℕ) : ENNReal) *
          ((N.card : ENNReal) * (ENNReal.ofReal ((r / 8) ^ Module.finrank ℝ E) * v1)) := by
        rw [harith]
        ring
    _ ≤ ((48 ^ Module.finrank ℝ E : ℕ) : ENNReal) * volume (K ∩ Theta) := by
        gcongr
    _ = _ := by
        simp [volume_cthickening_le_mul_volume_inter_cthickening.C, hKdef, hTheta]

end VolumeInCapsule

end Kakeya

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The dimensional constant in `Tube.le_volume_cthickening`.**

It is the product of the density-transfer constant of
`Convexity.IsConvexSet.volume_cthickening_ge_of_volume_ge` with the tube volume lower-bound
constant of `Tube.le_volume`. -/
@[nolint defsWithUnderscore]
noncomputable def le_volume_cthickening.c (n : ℕ) : NNReal :=
  Convexity.IsConvexSet.volume_cthickening_ge_of_volume_ge.c n * Tube.le_volume.c n

/-- The dimensional constant in `Tube.le_volume_cthickening` is positive. -/
theorem le_volume_cthickening.c_pos (n : ℕ) : 0 < c n := by
  unfold c
  exact mul_pos (Convexity.IsConvexSet.volume_cthickening_ge_of_volume_ge.c_pos n)
    (Tube.le_volume.c_pos n)

/-- **Thickening lower bound for a subset of a tube.** For a `δ`-tube `T` with `δ > 0` and any
`Y ⊆ T.carrier`, the closed `2ρ`-neighbourhood of `Y` has volume at least
`c(n) * (|Y| / |T.carrier|) * ρ ^ (n - 1)`, i.e. morally `≳ (|Y| / |T.carrier|) * ρ ^ (n - 1)`.

Thickening `Y` to scale `ρ` therefore recovers the full `ρ`-scale cross-section `ρ ^ (n - 1)`,
degraded only by the density of `Y` in `T`. -/
theorem le_volume_cthickening {δ : NNReal} (hδ : 0 < δ) (T : Tube δ E) (ρ : NNReal) {Y : Set E}
    (hY : Y ⊆ T.carrier) :
    (le_volume_cthickening.c (Module.finrank ℝ E) : ENNReal) *
        (volume Y / volume T.carrier) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)
      ≤ volume (Metric.cthickening (2 * (ρ : ℝ)) Y) := by
  set n := Module.finrank ℝ E
  -- Dimensional constants.
  let c1 : NNReal := Convexity.IsConvexSet.volume_cthickening_ge_of_volume_ge.c n
  let c2 : NNReal := Tube.le_volume.c n
  -- `T.carrier` is convex, bounded, and of positive finite volume.
  have hconv : Convexity.IsConvexSet ℝ T.carrier := T.convex'
  have hbdd : Bornology.IsBounded T.carrier := T.isCompact.isBounded
  have htoptop : volume T.carrier ≠ ⊤ := T.isCompact.measure_lt_top.ne
  have hVpos : 0 < volume T.carrier := by
    have hle := Tube.le_volume T
    have hzero : (0 : ENNReal) < ↑c2 * ↑δ ^ (n - 1) := by
      exact_mod_cast (mul_pos (Tube.le_volume.c_pos n) (pow_pos hδ (n - 1)))
    exact lt_of_lt_of_le hzero hle
  have hVne0 : volume T.carrier ≠ 0 := ne_of_gt hVpos
  let a : ENNReal := volume Y / volume T.carrier
  have hYa : a * volume T.carrier ≤ volume Y := by
    dsimp [a]
    rw [ENNReal.div_mul_cancel hVne0 htoptop]
  -- Lower bound on the volume of the `2ρ`-thickening of `T.carrier`.
  have hρ_le : (ρ : ℝ) ≤ (δ : ℝ) + 2 * (ρ : ℝ) := by
    nlinarith [NNReal.coe_nonneg δ, NNReal.coe_nonneg ρ]
  have hVol : (↑c2 : ENNReal) * ↑ρ ^ (n - 1) ≤
      volume (Metric.cthickening (((2 * ρ : NNReal) : ℝ)) T.carrier) := by
    rw [Tube.cthickening_carrier T (2 * ρ)]
    calc
      (↑c2 : ENNReal) * ↑ρ ^ (n - 1)
          ≤ (↑c2 : ENNReal) * ↑(δ + 2 * ρ) ^ (n - 1) := by
            gcongr
            exact_mod_cast hρ_le
      _ ≤ volume (T.rescale (δ + 2 * ρ)).carrier :=
          Tube.le_volume (T.rescale (δ + 2 * ρ))
  -- The big-piece inequality from the convex-body thickening lemma.
  have hC : (↑c1 : ENNReal) * a * volume (Metric.cthickening (((2 * ρ : NNReal) : ℝ)) T.carrier) ≤
      volume (Metric.cthickening (((2 * ρ : NNReal) : ℝ)) Y) := by
    exact Convexity.IsConvexSet.volume_cthickening_ge_of_volume_ge (hV := hconv)
      (hVb := hbdd) (hVvol := hVpos) (hY := hY) (r := 2 * ρ) (a := a) (h := hYa)
  -- Assemble the pieces.
  calc
    ((le_volume_cthickening.c n : NNReal) : ENNReal) * a * ↑ρ ^ (n - 1)
        = (↑c1 : ENNReal) * (↑c2 : ENNReal) * a * ↑ρ ^ (n - 1) := by
          rw [le_volume_cthickening.c, ENNReal.coe_mul]
    _ = (↑c1 : ENNReal) * (a * (↑c2 * ↑ρ ^ (n - 1))) := by ring
    _ ≤ (↑c1 : ENNReal) *
        (a * volume (Metric.cthickening (((2 * ρ : NNReal) : ℝ)) T.carrier)) := by
          exact mul_le_mul_right (mul_le_mul_right hVol a) (↑c1 : ENNReal)
    _ = (↑c1 : ENNReal) * a *
        volume (Metric.cthickening (((2 * ρ : NNReal) : ℝ)) T.carrier) := by ring
    _ ≤ volume (Metric.cthickening (((2 * ρ : NNReal) : ℝ)) Y) := by
          simpa [mul_assoc] using hC

end Tube

end
