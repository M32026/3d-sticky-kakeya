/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Tube.EDPacking.BadAgainstSet
public import Kakeya.Mathlib.Analysis.ProjectivePacking

/-!
# Coarse parent systems and leaf-mediated overlap

`ExternalParentSystem` describes a coarse family of `ρ`-tubes covering a fine
`δ`-tube family, with bounded overlap measured through the occupied leaves.
Two geometric ingredients control this overlap at `δ ≤ ρ ≤ 1`.

First, `Tube.endpoints_close_of_subset` uses the unit core to show that the
endpoints of a contained tube are within `3 * ρ` of the container's endpoints,
up to exchanging their orientation. Second, `card_le_of_separated_in_ball`
bounds a separated family in a ball by the volume ratio
`((R + r/2)/(r/2)) ^ n`. Applying this packing estimate to centers and
directions gives an absolute overlap bound for suitably separated parents.
The exported property measures overlap through fine leaves; it does not assert
pairwise essential distinctness of the coarse family.
-/

@[expose] public section

open MeasureTheory Metric Set Convexity ConvexSpaceBody
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace Kakeya

/-! ### Volume packing -/

/-- **Volume packing bound.**  An `r`-separated finite subset of the ball of radius `R` about `c`
has cardinality at most `((R + r/2)/(r/2)) ^ n`, by comparing the volume of the disjoint balls of
`r/2` about its points with the volume of the ball of radius `R + r/2` about `c`.

This is the reusable form of the packing step inlined in
`Kakeya.card_le_of_projective_separated_in_cap`. -/
theorem card_le_of_separated_in_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    (s : Finset E) (c : E) {R r : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hin : ∀ v ∈ s, ‖v - c‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ ((R + r / 2) / (r / 2)) ^ Module.finrank ℝ E := by
  classical
  set n : ℕ := Module.finrank ℝ E
  let μ : Measure E := volume
  have hr2pos : (0 : ℝ) < r / 2 := by linarith
  have hRr2pos : (0 : ℝ) < R + r / 2 := by linarith
  -- Balls of radius r/2 about the points are pairwise disjoint.
  have hD : Set.Pairwise (s : Set E) (fun x y => Disjoint (ball x (r / 2)) (ball y (r / 2))) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    have hxy' : r ≤ ‖x - y‖ := hsep x hx y hy hxy
    have heq : r / 2 + r / 2 = r := by ring
    rw [heq, dist_eq_norm]
    exact hxy'
  -- Each such ball lies inside the ball about c of radius R + r/2.
  have hsub : (⋃ v ∈ s, ball v (r / 2)) ⊆ ball c (R + r / 2) := by
    refine Set.iUnion₂_subset (fun v hv => ?_)
    refine ball_subset_ball' ?_
    have hvc : ‖v - c‖ ≤ R := hin v hv
    have hvd : dist v c ≤ R := by rw [dist_eq_norm]; exact hvc
    linarith
  -- The volume of a small ball is (r/2)^n · vol(ball 0 1).
  have hμball : ∀ v : E, μ (ball v (r / 2)) = ENNReal.ofReal ((r / 2) ^ n) * μ (ball (0 : E) 1) :=
    fun v => MeasureTheory.Measure.addHaar_ball_of_pos μ v hr2pos
  have hvol_eq : μ (⋃ v ∈ s, ball v (r / 2))
      = (s.card : ℝ≥0∞) * (ENNReal.ofReal ((r / 2) ^ n) * μ (ball (0 : E) 1)) := by
    have hpwd : (s : Set E).PairwiseDisjoint (fun v : E => ball v (r / 2)) := hD
    rw [measure_biUnion_finset hpwd (fun v _ => measurableSet_ball (x := v))]
    simp only [hμball, Finset.sum_const, nsmul_eq_mul]
  have hvol_target : μ (ball c (R + r / 2))
      = ENNReal.ofReal ((R + r / 2) ^ n) * μ (ball (0 : E) 1) :=
    MeasureTheory.Measure.addHaar_ball_of_pos μ c hRr2pos
  have hle : (s.card : ℝ≥0∞) * (ENNReal.ofReal ((r / 2) ^ n) * μ (ball (0 : E) 1))
      ≤ ENNReal.ofReal ((R + r / 2) ^ n) * μ (ball (0 : E) 1) := by
    calc (s.card : ℝ≥0∞) * (ENNReal.ofReal ((r / 2) ^ n) * μ (ball (0 : E) 1))
        = μ (⋃ v ∈ s, ball v (r / 2)) := hvol_eq.symm
      _ ≤ μ (ball c (R + r / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((R + r / 2) ^ n) * μ (ball (0 : E) 1) := hvol_target
  -- Cancel the unit-ball volume.
  have hμunit_pos : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ _ zero_lt_one).ne'
  have hμunit_lt : μ (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hle2 : (s.card : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ n) * μ (ball (0 : E) 1)
      ≤ ENNReal.ofReal ((R + r / 2) ^ n) * μ (ball (0 : E) 1) := by
    rw [mul_assoc]; exact hle
  have hle' : (s.card : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ n)
      ≤ ENNReal.ofReal ((R + r / 2) ^ n) :=
    (ENNReal.mul_le_mul_iff_left hμunit_pos hμunit_lt).1 hle2
  -- Convert to real numbers and divide.
  have hr2n_pos : (0 : ℝ) < (r / 2) ^ n := pow_pos hr2pos n
  have hRr2n_nonneg : (0 : ℝ) ≤ (R + r / 2) ^ n := pow_nonneg hRr2pos.le n
  have hcard_nonneg : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  have hcard_real : (s.card : ℝ) * (r / 2) ^ n ≤ (R + r / 2) ^ n := by
    have h_lhs : (s.card : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ n)
        = ENNReal.ofReal ((s.card : ℝ) * (r / 2) ^ n) := by
      rw [ENNReal.ofReal_mul hcard_nonneg]
      congr 1
      exact (ENNReal.ofReal_natCast s.card).symm
    rw [h_lhs] at hle'
    exact (ENNReal.ofReal_le_ofReal_iff hRr2n_nonneg).mp hle'
  have hcard_real' : (s.card : ℝ) ≤ (R + r / 2) ^ n / (r / 2) ^ n := by
    rw [le_div_iff₀ hr2n_pos]
    exact hcard_real
  rw [div_pow]
  exact hcard_real'

/-! ### Longitudinal rigidity of tubes -/

/-- A point of a tube's carrier is within the radius of a point of its core segment, written in the
affine parametrisation `V.x + s • V.direction` with `s ∈ [0, 1]`. -/
theorem Tube.exists_param_dist_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {r : ℝ≥0} (V : Tube r E) {x : E} (hx : x ∈ (V.carrier : Set E)) :
    ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ dist x (V.x + s • V.direction) ≤ (r : ℝ) := by
  rw [V.carrier_eq] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨z, hz, hxz⟩
  have hzd : dist x z ≤ (r : ℝ) := Metric.mem_closedBall.mp hxz
  rw [segment_eq_image'] at hz
  rcases hz with ⟨s, hs, hz_eq⟩
  refine ⟨s, hs, ?_⟩
  have hz_eq' : V.x + s • (V.y - V.x) = z := by simpa using hz_eq
  rw [show V.direction = V.y - V.x by rfl, hz_eq']
  exact hzd

/-- **Longitudinal rigidity.**  A `Tube` is the neighbourhood of a segment of length exactly `1`, so
a `δ`-tube contained in an `r`-tube has its endpoints within `3r` of the containing tube's
endpoints, in one of the two orientations.

The mechanism: the two endpoints of the inner tube are within `r` of core points at parameters
`s₁, s₂`, and they are at distance `1` from each other, so `|s₁ - s₂| ≥ 1 - 2r`.  Since
`s₁, s₂ ∈ [0, 1]` this forces one of them within `2r` of `0` and the other within `2r` of `1`.

This is what the previous "essentially distinct coarse parents" language was standing in for, and
unlike that language it is available at every scale. -/
theorem Tube.endpoints_close_of_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ r : ℝ≥0} (T : Tube δ E) (V : Tube r E)
    (hsub : (T.carrier : Set E) ⊆ (V.carrier : Set E)) (_hr : (r : ℝ) ≤ 1 / 4) :
    (dist T.x V.x ≤ 3 * (r : ℝ) ∧ dist T.y V.y ≤ 3 * (r : ℝ)) ∨
      (dist T.x V.y ≤ 3 * (r : ℝ) ∧ dist T.y V.x ≤ 3 * (r : ℝ)) := by
  have hTx : T.x ∈ (T.carrier : Set E) := by
    rw [T.carrier_eq]
    refine Set.mem_iUnion₂.mpr
      ⟨T.x, left_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self δ.coe_nonneg⟩
  have hTy : T.y ∈ (T.carrier : Set E) := by
    rw [T.carrier_eq]
    refine Set.mem_iUnion₂.mpr
      ⟨T.y, right_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self δ.coe_nonneg⟩
  obtain ⟨s₁, hs₁, hd₁⟩ := Tube.exists_param_dist_le V (hsub hTx)
  obtain ⟨s₂, hs₂, hd₂⟩ := Tube.exists_param_dist_le V (hsub hTy)
  have hVy : V.y = V.x + (1 : ℝ) • V.direction := by
    rw [show V.direction = V.y - V.x by rfl]
    simp
  have hparam (s t : ℝ) :
      dist (V.x + s • V.direction) (V.x + t • V.direction) = |s - t| := by
    rw [dist_eq_norm]
    rw [show (V.x + s • V.direction) - (V.x + t • V.direction) = (s - t) • V.direction
      by module]
    rw [norm_smul, V.norm_direction, mul_one, Real.norm_eq_abs]
  have hdVx (s : ℝ) : dist (V.x + s • V.direction) V.x = |s| := by
    simpa using hparam s 0
  have hdVy (s : ℝ) : dist (V.x + s • V.direction) V.y = |s - (1 : ℝ)| := by
    simpa [← hVy] using hparam s 1
  have hbig : dist T.x T.y ≤ (r : ℝ) + |s₁ - s₂| + (r : ℝ) := by
    have h1 := dist_triangle T.x (V.x + s₁ • V.direction) T.y
    have h2 := dist_triangle (V.x + s₁ • V.direction) (V.x + s₂ • V.direction) T.y
    have hd2c : dist (V.x + s₂ • V.direction) T.y = dist T.y (V.x + s₂ • V.direction) :=
      dist_comm _ _
    nlinarith [h1, h2, hd₁, hd₂, hparam s₁ s₂, hd2c]
  have hcore : (1 : ℝ) - 2 * (r : ℝ) ≤ |s₁ - s₂| := by
    have hcco : (1 : ℝ) ≤ (r : ℝ) + |s₁ - s₂| + (r : ℝ) := by
      simpa [T.dist_eq_one] using hbig
    linarith
  rcases le_total s₁ s₂ with h12 | h21
  · left
    have hsep_abs : |s₁ - s₂| = s₂ - s₁ := by
      rw [abs_of_nonpos (sub_nonpos.mpr h12)]
      ring
    have hsep1 : (1 : ℝ) - 2 * (r : ℝ) ≤ s₂ - s₁ := by
      rwa [hsep_abs] at hcore
    have hs1le : s₁ ≤ 2 * (r : ℝ) := by linarith [hsep1, hs₂.2]
    have hs2hi : 1 - s₂ ≤ 2 * (r : ℝ) := by linarith [hsep1, hs₁.1]
    have hdx : dist T.x V.x ≤ 3 * (r : ℝ) := by
      calc
        dist T.x V.x ≤ dist T.x (V.x + s₁ • V.direction) + dist (V.x + s₁ • V.direction) V.x :=
          dist_triangle T.x (V.x + s₁ • V.direction) V.x
        _ ≤ (r : ℝ) + |s₁| := by
          rw [hdVx s₁]
          linarith
        _ ≤ (r : ℝ) + 2 * (r : ℝ) := by
          rw [abs_of_nonneg hs₁.1]
          linarith
        _ = 3 * (r : ℝ) := by ring
    have hdy : dist T.y V.y ≤ 3 * (r : ℝ) := by
      calc
        dist T.y V.y ≤ dist T.y (V.x + s₂ • V.direction) + dist (V.x + s₂ • V.direction) V.y :=
          dist_triangle T.y (V.x + s₂ • V.direction) V.y
        _ ≤ (r : ℝ) + |s₂ - (1 : ℝ)| := by
          rw [hdVy s₂]
          linarith
        _ ≤ (r : ℝ) + 2 * (r : ℝ) := by
          rw [show |s₂ - (1 : ℝ)| = (1 : ℝ) - s₂ by
            rw [abs_of_nonpos (sub_nonpos.mpr hs₂.2)]
            ring]
          linarith
        _ = 3 * (r : ℝ) := by linarith
    exact ⟨hdx, hdy⟩
  · right
    have hsep_abs : |s₁ - s₂| = s₁ - s₂ := by
      rw [abs_of_nonneg (sub_nonneg.mpr h21)]
    have hsep2 : (1 : ℝ) - 2 * (r : ℝ) ≤ s₁ - s₂ := by
      rwa [hsep_abs] at hcore
    have hs2le : s₂ ≤ 2 * (r : ℝ) := by linarith [hsep2, hs₁.2]
    have hs1hi : 1 - s₁ ≤ 2 * (r : ℝ) := by linarith [hsep2, hs₂.1]
    have hdy2 : dist T.y V.x ≤ 3 * (r : ℝ) := by
      calc
        dist T.y V.x ≤ dist T.y (V.x + s₂ • V.direction) + dist (V.x + s₂ • V.direction) V.x :=
          dist_triangle T.y (V.x + s₂ • V.direction) V.x
        _ ≤ (r : ℝ) + |s₂| := by
          rw [hdVx s₂]
          linarith
        _ ≤ (r : ℝ) + 2 * (r : ℝ) := by
          rw [abs_of_nonneg hs₂.1]
          linarith
        _ = 3 * (r : ℝ) := by linarith
    have hdx2 : dist T.x V.y ≤ 3 * (r : ℝ) := by
      calc
        dist T.x V.y ≤ dist T.x (V.x + s₁ • V.direction) + dist (V.x + s₁ • V.direction) V.y :=
          dist_triangle T.x (V.x + s₁ • V.direction) V.y
        _ ≤ (r : ℝ) + |s₁ - (1 : ℝ)| := by
          rw [hdVy s₁]
          linarith
        _ ≤ (r : ℝ) + 2 * (r : ℝ) := by
          rw [show |s₁ - (1 : ℝ)| = (1 : ℝ) - s₁ by
            rw [abs_of_nonpos (sub_nonpos.mpr hs₁.2)]
            ring]
          linarith
        _ = 3 * (r : ℝ) := by linarith
    exact ⟨hdx2, hdy2⟩

/-- **Whole-leaf containment from endpoint closeness.**

If the endpoints of a `δ`-tube are within `r` of the endpoints of a `ρ`-tube and `δ + r ≤ ρ`, the
whole `δ`-tube lies in the `ρ`-tube.  Convexity does the work: the *same* affine parameter on the
two core segments moves by at most `r`, so every core point of `T` is within `r` of one of `V`,
and every point of `T` is within `δ` of `T`'s core. -/
theorem Tube.carrier_subset_of_endpoints_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : NNReal} (T : Tube δ E) (V : Tube ρ E) {r : ℝ}
    (hx : dist T.x V.x ≤ r) (hy : dist T.y V.y ≤ r)
    (hr : (δ : ℝ) + r ≤ (ρ : ℝ)) :
    T.carrier ⊆ V.carrier := by
  intro w hw
  rw [T.carrier_eq] at hw
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.mp hw
  rw [V.carrier_eq]
  rcases hz with ⟨s, t, hs, ht, hst, hz_eq⟩
  let z' : E := s • V.x + t • V.y
  have hzz' : dist z z' ≤ r := by
    dsimp [z']
    rw [← hz_eq]
    rw [dist_eq_norm]
    calc
      ‖(s • T.x + t • T.y) - (s • V.x + t • V.y)‖
          = ‖s • (T.x - V.x) + t • (T.y - V.y)‖ := by
            congr 1
            module
      _ ≤ ‖s • (T.x - V.x)‖ + ‖t • (T.y - V.y)‖ := norm_add_le _ _
      _ ≤ s * r + t * r := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        rw [abs_of_nonneg hs, abs_of_nonneg ht]
        rw [← dist_eq_norm, ← dist_eq_norm]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hx hs
        · exact mul_le_mul_of_nonneg_left hy ht
      _ = r := by
        rw [← add_mul, hst]
        ring
  refine Set.mem_iUnion₂.mpr ⟨z', ?_, ?_⟩
  · dsimp [z']
    exact ⟨s, t, hs, ht, hst, rfl⟩
  · have hdist : dist w z' ≤ (ρ : ℝ) := by
      calc
        dist w z' ≤ dist w z + dist z z' := dist_triangle w z z'
        _ ≤ (δ : ℝ) + r := by
          nlinarith [Metric.mem_closedBall.mp hwz, hzz']
        _ ≤ (ρ : ℝ) := hr
    exact Metric.mem_closedBall.mpr hdist

/-- Whole-tube containment from endpoint closeness in the *reversed* orientation.  The carrier of a
tube depends on its endpoints only through their segment, which is symmetric, so the companion of
`Kakeya.Tube.carrier_subset_of_endpoints_close` with the roles of `V.x` and `V.y` exchanged also
holds. -/
theorem Tube.carrier_subset_of_endpoints_close_flip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : ℝ≥0} (T : Tube δ E) (V : Tube ρ E) {c : ℝ}
    (hx : dist T.x V.y ≤ c) (hy : dist T.y V.x ≤ c) (hc : (δ : ℝ) + c ≤ (ρ : ℝ)) :
    (T.carrier : Set E) ⊆ (V.carrier : Set E) := by
  intro w hw
  rw [T.carrier_eq] at hw
  obtain ⟨z, hz, hw⟩ := Set.mem_iUnion₂.mp hw
  rw [V.carrier_eq]
  rcases hz with ⟨s, t, hs, ht, hst, hz_eq⟩
  let z' : E := s • V.y + t • V.x
  have hzz' : dist z z' ≤ c := by
    dsimp [z']
    rw [← hz_eq]
    rw [dist_eq_norm]
    calc
      ‖(s • T.x + t • T.y) - (s • V.y + t • V.x)‖
          = ‖s • (T.x - V.y) + t • (T.y - V.x)‖ := by
            congr 1
            module
      _ ≤ ‖s • (T.x - V.y)‖ + ‖t • (T.y - V.x)‖ := norm_add_le _ _
      _ ≤ s * c + t * c := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        rw [abs_of_nonneg hs, abs_of_nonneg ht]
        rw [← dist_eq_norm, ← dist_eq_norm]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hx hs
        · exact mul_le_mul_of_nonneg_left hy ht
      _ = c := by
        rw [← add_mul, hst]
        ring
  refine Set.mem_iUnion₂.mpr ⟨z', ?_, ?_⟩
  · have hzmem : z' ∈ segment ℝ V.y V.x := by
      dsimp [z']
      exact ⟨s, t, hs, ht, hst, rfl⟩
    simpa [segment_symm] using hzmem
  · have hdist : dist w z' ≤ (ρ : ℝ) := by
      calc
        dist w z' ≤ dist w z + dist z z' := dist_triangle w z z'
        _ ≤ (δ : ℝ) + c := by nlinarith [Metric.mem_closedBall.mp hw, hzz']
        _ ≤ (ρ : ℝ) := hc
    exact Metric.mem_closedBall.mpr hdist

/-- **Two leaves inside one tube are mutually close.**  If two `δ`-tubes lie in a common `r`-tube
then each lies in the other's rescale to any radius at least `δ + 6r`.  Rigidity pins both to the
containing tube's endpoints, so their endpoints agree to within `6r` in one of the two
orientations. -/
theorem Tube.carrier_subset_rescale_of_common_tube
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ r : ℝ≥0} (T₁ T₂ : Tube δ E) (V : Tube r E)
    (h₁ : (T₁.carrier : Set E) ⊆ (V.carrier : Set E))
    (h₂ : (T₂.carrier : Set E) ⊆ (V.carrier : Set E)) (hr : (r : ℝ) ≤ 1 / 4)
    {s : ℝ≥0} (hs : (δ : ℝ) + 6 * (r : ℝ) ≤ (s : ℝ)) :
    (T₁.carrier : Set E) ⊆ ((T₂.rescale s).carrier : Set E) := by
  rcases endpoints_close_of_subset T₁ V h₁ hr with h₁m | h₁f
  · rcases endpoints_close_of_subset T₂ V h₂ hr with h₂m | h₂f
    · -- matched / matched
      have hxx : dist T₁.x T₂.x ≤ 6 * (r : ℝ) := by
        calc
          dist T₁.x T₂.x ≤ dist T₁.x V.x + dist V.x T₂.x := dist_triangle T₁.x V.x T₂.x
          _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by
            have : dist V.x T₂.x ≤ 3 * (r : ℝ) := by simpa [dist_comm] using h₂m.1
            linarith
          _ = 6 * (r : ℝ) := by ring
      have hyy : dist T₁.y T₂.y ≤ 6 * (r : ℝ) := by
        calc
          dist T₁.y T₂.y ≤ dist T₁.y V.y + dist V.y T₂.y := dist_triangle T₁.y V.y T₂.y
          _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by
            have : dist V.y T₂.y ≤ 3 * (r : ℝ) := by simpa [dist_comm] using h₂m.2
            linarith
          _ = 6 * (r : ℝ) := by ring
      exact Tube.carrier_subset_of_endpoints_close (T := T₁) (V := T₂.rescale s)
        (r := 6 * (r : ℝ))
        (show dist T₁.x (T₂.rescale s).x ≤ 6 * (r : ℝ) by simpa [Tube.rescale] using hxx)
        (show dist T₁.y (T₂.rescale s).y ≤ 6 * (r : ℝ) by simpa [Tube.rescale] using hyy)
        hs
    · -- matched / flipped
      have hxy : dist T₁.x T₂.y ≤ 6 * (r : ℝ) := by
        calc
          dist T₁.x T₂.y ≤ dist T₁.x V.x + dist V.x T₂.y := dist_triangle T₁.x V.x T₂.y
          _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by
            have : dist V.x T₂.y ≤ 3 * (r : ℝ) := by simpa [dist_comm] using h₂f.2
            linarith
          _ = 6 * (r : ℝ) := by ring
      have hyx : dist T₁.y T₂.x ≤ 6 * (r : ℝ) := by
        calc
          dist T₁.y T₂.x ≤ dist T₁.y V.y + dist V.y T₂.x := dist_triangle T₁.y V.y T₂.x
          _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by
            have : dist V.y T₂.x ≤ 3 * (r : ℝ) := by simpa [dist_comm] using h₂f.1
            linarith
          _ = 6 * (r : ℝ) := by ring
      exact Tube.carrier_subset_of_endpoints_close_flip (T := T₁) (V := T₂.rescale s)
        (c := 6 * (r : ℝ))
        (show dist T₁.x (T₂.rescale s).y ≤ 6 * (r : ℝ) by simpa [Tube.rescale] using hxy)
        (show dist T₁.y (T₂.rescale s).x ≤ 6 * (r : ℝ) by simpa [Tube.rescale] using hyx)
        hs
  · rcases endpoints_close_of_subset T₂ V h₂ hr with h₂m | h₂f
    · -- flipped / matched
      have hxy : dist T₁.x T₂.y ≤ 6 * (r : ℝ) := by
        calc
          dist T₁.x T₂.y ≤ dist T₁.x V.y + dist V.y T₂.y := dist_triangle T₁.x V.y T₂.y
          _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by
            have : dist V.y T₂.y ≤ 3 * (r : ℝ) := by simpa [dist_comm] using h₂m.2
            linarith
          _ = 6 * (r : ℝ) := by ring
      have hyx : dist T₁.y T₂.x ≤ 6 * (r : ℝ) := by
        calc
          dist T₁.y T₂.x ≤ dist T₁.y V.x + dist V.x T₂.x := dist_triangle T₁.y V.x T₂.x
          _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by
            have : dist V.x T₂.x ≤ 3 * (r : ℝ) := by simpa [dist_comm] using h₂m.1
            linarith
          _ = 6 * (r : ℝ) := by ring
      exact Tube.carrier_subset_of_endpoints_close_flip (T := T₁) (V := T₂.rescale s)
        (c := 6 * (r : ℝ))
        (show dist T₁.x (T₂.rescale s).y ≤ 6 * (r : ℝ) by simpa [Tube.rescale] using hxy)
        (show dist T₁.y (T₂.rescale s).x ≤ 6 * (r : ℝ) by simpa [Tube.rescale] using hyx)
        hs
    · -- flipped / flipped
      have hxx : dist T₁.x T₂.x ≤ 6 * (r : ℝ) := by
        calc
          dist T₁.x T₂.x ≤ dist T₁.x V.y + dist V.y T₂.x := dist_triangle T₁.x V.y T₂.x
          _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by
            have : dist V.y T₂.x ≤ 3 * (r : ℝ) := by simpa [dist_comm] using h₂f.1
            linarith
          _ = 6 * (r : ℝ) := by ring
      have hyy : dist T₁.y T₂.y ≤ 6 * (r : ℝ) := by
        calc
          dist T₁.y T₂.y ≤ dist T₁.y V.x + dist V.x T₂.y := dist_triangle T₁.y V.x T₂.y
          _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by
            have : dist V.x T₂.y ≤ 3 * (r : ℝ) := by simpa [dist_comm] using h₂f.2
            linarith
          _ = 6 * (r : ℝ) := by ring
      exact Tube.carrier_subset_of_endpoints_close (T := T₁) (V := T₂.rescale s)
        (r := 6 * (r : ℝ))
        (show dist T₁.x (T₂.rescale s).x ≤ 6 * (r : ℝ) by simpa [Tube.rescale] using hxx)
        (show dist T₁.y (T₂.rescale s).y ≤ 6 * (r : ℝ) by simpa [Tube.rescale] using hyy)
        hs

/-! ### Maximal separated subfamilies -/

/-- **A maximum-cardinality `Rel`-separated subset is saturating.**  Among the `Rel`-separated
subsets of a finite set, pick one of largest cardinality.  Maximality says exactly that every
element of the ambient set is *either* selected *or* fails to be separated from something
selected — which is the covering property a greedy construction needs.

Stated for a symmetric `Rel`, which is how all the separation relations below arise. -/
theorem exists_max_card_separated {α : Type*} (s : Finset α)
    (Rel : α → α → Prop) (hsymm : ∀ i j, Rel i j → Rel j i) :
    ∃ S : Finset α, S ⊆ s ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Rel i j) ∧
      (∀ j ∈ s, ∃ i ∈ S, i = j ∨ ¬ Rel i j) := by
  classical
  let C : Finset (Finset α) := s.powerset.filter fun A =>
    ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Rel i j
  have hempty : (∅ : Finset α) ∈ C := by
    dsimp [C]
    exact Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset s, by simp⟩
  have hCnonempty : C.Nonempty := ⟨∅, hempty⟩
  obtain ⟨S, hSC, hSmax⟩ := C.exists_max_image Finset.card hCnonempty
  have hSCmem : S ∈ s.powerset ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Rel i j := by
    dsimp [C] at hSC
    exact Finset.mem_filter.mp hSC
  have hSsub : S ⊆ s := Finset.mem_powerset.mp hSCmem.1
  have hSsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Rel i j := hSCmem.2
  refine ⟨S, hSsub, hSsep, ?_⟩
  intro j hj
  by_cases hjS : j ∈ S
  · exact ⟨j, hjS, Or.inl rfl⟩
  · by_contra hnot
    push Not at hnot
    let T : Finset α := insert j S
    have hTsub : T ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp (by simpa [T] using hx) with hxeq | hxS
      · rw [hxeq]
        exact hj
      · exact hSsub hxS
    have hsepT : ∀ i ∈ T, ∀ i' ∈ T, i ≠ i' → Rel i i' := by
      intro i hii i' hi'i' hne
      rcases Finset.mem_insert.mp (by simpa [T] using hii) with heq | hiS
      · rcases Finset.mem_insert.mp (by simpa [T] using hi'i') with heq' | hi'S
        · exfalso
          exact hne (heq.trans heq'.symm)
        · rw [heq]
          exact hsymm i' j (hnot i' hi'S).2
      · rcases Finset.mem_insert.mp (by simpa [T] using hi'i') with heq' | hi'S
        · rw [heq']
          exact (hnot i hiS).2
        · exact hSsep i hiS i' hi'S hne
    have hCT : T ∈ C := by
      dsimp [C]
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTsub, hsepT⟩
    have hmax : T.card ≤ S.card := hSmax T hCT
    have hgt : S.card < T.card := by
      dsimp [T]
      rw [Finset.card_insert_of_notMem hjS]
      omega
    exact (not_lt_of_ge hmax) hgt

/-! ### Centre and direction coordinates of a tube -/

/-- A tube's initial endpoint in centre/direction coordinates. -/
theorem Tube.x_eq_center_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : ℝ≥0} (T : Tube δ E) : T.x = T.center - (2⁻¹ : ℝ) • T.direction := by
  simp only [Tube.center, Tube.direction, midpoint_eq_smul_add, invOf_eq_inv]
  module

/-- A tube's terminal endpoint in centre/direction coordinates. -/
theorem Tube.y_eq_center_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : ℝ≥0} (T : Tube δ E) : T.y = T.center + (2⁻¹ : ℝ) • T.direction := by
  simp only [Tube.center, Tube.direction, midpoint_eq_smul_add, invOf_eq_inv]
  module

/-- **Rigidity in centre/direction coordinates.**  A `δ`-tube inside an `r`-tube has its centre
within `3r` of the containing tube's centre and its direction within `6r` of the containing tube's
direction *up to sign*.

Both coordinates are orientation-free — the centre because `midpoint` is symmetric in the endpoints,
the direction because the sign is quotiented out — so unlike
`Kakeya.Tube.endpoints_close_of_subset` there is no dichotomy left to case on.  This is what lets
the parent count factor as (midpoint packing) × (projective direction packing). -/
theorem Tube.center_dir_close_of_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ r : ℝ≥0} (T : Tube δ E) (V : Tube r E)
    (hsub : (T.carrier : Set E) ⊆ (V.carrier : Set E)) (hr : (r : ℝ) ≤ 1 / 4) :
    dist T.center V.center ≤ 3 * (r : ℝ) ∧
      min ‖T.direction - V.direction‖ ‖T.direction + V.direction‖ ≤ 6 * (r : ℝ) := by
  -- The midpoint difference in centre coordinates is half the coordinatewise sum.
  have hmid (a b c d : E) :
      ‖midpoint ℝ a b - midpoint ℝ c d‖ = ‖(2⁻¹ : ℝ) • ((a - c) + (b - d))‖ := by
    rw [show midpoint ℝ a b = (2⁻¹ : ℝ) • (a + b) by exact midpoint_eq_smul_add (R := ℝ) a b]
    rw [show midpoint ℝ c d = (2⁻¹ : ℝ) • (c + d) by exact midpoint_eq_smul_add (R := ℝ) c d]
    congr 1
    module
  -- A coordinatewise `3r` bound gives the `3r` midpoint bound.
  have hnorm (a b c d : E) (ha : dist a c ≤ 3 * (r : ℝ)) (hb : dist b d ≤ 3 * (r : ℝ)) :
      ‖(2⁻¹ : ℝ) • ((a - c) + (b - d))‖ ≤ 3 * (r : ℝ) := by
    calc
      ‖(2⁻¹ : ℝ) • ((a - c) + (b - d))‖ ≤ (2⁻¹ : ℝ) * (‖a - c‖ + ‖b - d‖) := by
        rw [norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2⁻¹ : ℝ))]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num : (0 : ℝ) ≤ (2⁻¹ : ℝ))
      _ = (2⁻¹ : ℝ) * (dist a c + dist b d) := by
        rw [dist_eq_norm, dist_eq_norm]
      _ ≤ 3 * (r : ℝ) := by
        have hsum : dist a c + dist b d ≤ 6 * (r : ℝ) := by nlinarith
        have hle2 : (2⁻¹ : ℝ) * (dist a c + dist b d) ≤ (2⁻¹ : ℝ) * (6 * (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        have hnn : (2⁻¹ : ℝ) = (1 : ℝ) / 2 := by norm_num
        nlinarith
  rcases Tube.endpoints_close_of_subset T V hsub hr with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · constructor
    · rw [dist_eq_norm]
      calc
        ‖T.center - V.center‖ = ‖(2⁻¹ : ℝ) • ((T.x - V.x) + (T.y - V.y))‖ := by
          exact hmid T.x T.y V.x V.y
        _ ≤ 3 * (r : ℝ) := hnorm T.x T.y V.x V.y hxx hyy
    · apply min_le_of_left_le
      rw [show T.direction - V.direction = (T.y - V.y) - (T.x - V.x) by module]
      calc
        ‖(T.y - V.y) - (T.x - V.x)‖ ≤ ‖T.y - V.y‖ + ‖T.x - V.x‖ := norm_sub_le _ _
        _ = dist T.y V.y + dist T.x V.x := by rw [dist_eq_norm, dist_eq_norm]
        _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by exact add_le_add hyy hxx
        _ = 6 * (r : ℝ) := by linarith
  · constructor
    · rw [dist_eq_norm]
      calc
        ‖T.center - V.center‖ = ‖(2⁻¹ : ℝ) • ((T.x - V.y) + (T.y - V.x))‖ := by
          change ‖midpoint ℝ T.x T.y - midpoint ℝ V.x V.y‖ =
            ‖(2⁻¹ : ℝ) • ((T.x - V.y) + (T.y - V.x))‖
          rw [midpoint_comm (R := ℝ) V.x V.y]
          exact hmid T.x T.y V.y V.x
        _ ≤ 3 * (r : ℝ) := hnorm T.x T.y V.y V.x hxy hyx
    · apply min_le_of_right_le
      rw [show T.direction + V.direction = (T.y - V.x) + (V.y - T.x) by module]
      calc
        ‖(T.y - V.x) + (V.y - T.x)‖ ≤ ‖T.y - V.x‖ + ‖V.y - T.x‖ := norm_add_le _ _
        _ = dist T.y V.x + dist V.y T.x := by rw [dist_eq_norm, dist_eq_norm]
        _ ≤ 3 * (r : ℝ) + 3 * (r : ℝ) := by
          have hb : dist V.y T.x ≤ 3 * (r : ℝ) := by simpa [dist_comm] using hxy
          exact add_le_add hyx hb
        _ = 6 * (r : ℝ) := by linarith

/-- **The converse of `Kakeya.Tube.center_dir_close_of_subset`.**  Two `δ`-tubes whose centres are
within `c` and whose directions agree within `c` up to sign have endpoints within `c + c/2`, so each
lies in the other's rescale to any radius at least `δ + 3c/2`. -/
theorem Tube.carrier_subset_rescale_of_center_dir_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : ℝ≥0} (T₁ T₂ : Tube δ E) {c : ℝ} (hc0 : 0 ≤ c)
    (hm : dist T₁.center T₂.center ≤ c)
    (hd : min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ ≤ c)
    {s : ℝ≥0} (hs : (δ : ℝ) + 3 * c / 2 ≤ (s : ℝ)) :
    (T₁.carrier : Set E) ⊆ ((T₂.rescale s).carrier : Set E) := by
  have hmc : ‖T₁.center - T₂.center‖ ≤ c := by
    simpa [dist_eq_norm] using hm
  rcases min_le_iff.mp hd with hd₁ | hd₂
  · -- aligned directions
    have hbd : ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖ ≤ c / 2 := by
      calc
        ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖
            ≤ ‖(2⁻¹ : ℝ)‖ * ‖T₁.direction - T₂.direction‖ := norm_smul_le _ _
        _ = (1 / 2 : ℝ) * ‖T₁.direction - T₂.direction‖ := by
            norm_num
        _ ≤ c / 2 := by
            nlinarith [hd₁, hc0]
    have hxx : dist T₁.x T₂.x ≤ 3 * c / 2 := by
      rw [dist_eq_norm, Tube.x_eq_center_sub T₁, Tube.x_eq_center_sub T₂]
      rw [show T₁.center - (2⁻¹ : ℝ) • T₁.direction - (T₂.center - (2⁻¹ : ℝ) • T₂.direction)
          = (T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction - T₂.direction) by module]
      calc
        ‖(T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖
            ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖ :=
              norm_sub_le _ _
        _ ≤ c + c / 2 := by
              exact add_le_add hmc hbd
        _ = 3 * c / 2 := by ring
    have hyy : dist T₁.y T₂.y ≤ 3 * c / 2 := by
      rw [dist_eq_norm, Tube.y_eq_center_add T₁, Tube.y_eq_center_add T₂]
      rw [show T₁.center + (2⁻¹ : ℝ) • T₁.direction - (T₂.center + (2⁻¹ : ℝ) • T₂.direction)
          = (T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction - T₂.direction) by module]
      calc
        ‖(T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖
            ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖ :=
              norm_add_le _ _
        _ ≤ c + c / 2 := by
              exact add_le_add hmc hbd
        _ = 3 * c / 2 := by ring
    exact Tube.carrier_subset_of_endpoints_close (T := T₁) (V := T₂.rescale s)
      (r := 3 * c / 2)
      (show dist T₁.x (T₂.rescale s).x ≤ 3 * c / 2 by simpa [Tube.rescale] using hxx)
      (show dist T₁.y (T₂.rescale s).y ≤ 3 * c / 2 by simpa [Tube.rescale] using hyy)
      hs
  · -- anti-aligned : ‖T₁.direction + T₂.direction‖ ≤ c
    have hbd : ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖ ≤ c / 2 := by
      calc
        ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖
            ≤ ‖(2⁻¹ : ℝ)‖ * ‖T₁.direction + T₂.direction‖ := norm_smul_le _ _
        _ = (1 / 2 : ℝ) * ‖T₁.direction + T₂.direction‖ := by
            norm_num
        _ ≤ c / 2 := by
            nlinarith [hd₂, hc0]
    have hxy : dist T₁.x T₂.y ≤ 3 * c / 2 := by
      rw [dist_eq_norm, Tube.x_eq_center_sub T₁, Tube.y_eq_center_add T₂]
      rw [show T₁.center - (2⁻¹ : ℝ) • T₁.direction - (T₂.center + (2⁻¹ : ℝ) • T₂.direction)
          = (T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction + T₂.direction) by module]
      calc
        ‖(T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖
            ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖ :=
              norm_sub_le _ _
        _ ≤ c + c / 2 := by
              exact add_le_add hmc hbd
        _ = 3 * c / 2 := by ring
    have hyx : dist T₁.y T₂.x ≤ 3 * c / 2 := by
      rw [dist_eq_norm, Tube.y_eq_center_add T₁, Tube.x_eq_center_sub T₂]
      rw [show T₁.center + (2⁻¹ : ℝ) • T₁.direction - (T₂.center - (2⁻¹ : ℝ) • T₂.direction)
          = (T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction + T₂.direction) by module]
      calc
        ‖(T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖
            ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖ :=
              norm_add_le _ _
        _ ≤ c + c / 2 := by
          exact add_le_add hmc hbd
        _ = 3 * c / 2 := by ring
    exact Tube.carrier_subset_of_endpoints_close_flip (T := T₁) (V := T₂.rescale s)
      (c := 3 * c / 2)
      (show dist T₁.x (T₂.rescale s).y ≤ 3 * c / 2 by simpa [Tube.rescale] using hxy)
      (show dist T₁.y (T₂.rescale s).x ≤ 3 * c / 2 by simpa [Tube.rescale] using hyx)
      hs

/-! ### The tube parameter distance -/

/-- **Triangle inequality for the projective distance on directions.**

`d(u, w) := min ‖u - w‖ ‖u + w‖` identifies antipodes, and it is a pseudometric: whichever signs
achieve the two minima on the right, composing them gives a sign achieving a bound for the left.
Four cases, e.g. `u + w = (u - v) + (v + w)` and `u + w = (u + v) - (v - w)`. -/
theorem projDist_triangle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u v w : E) :
    min ‖u - w‖ ‖u + w‖ ≤ min ‖u - v‖ ‖u + v‖ + min ‖v - w‖ ‖v + w‖ := by
  rcases le_total ‖u - v‖ ‖u + v‖ with h1 | h1
  · rcases le_total ‖v - w‖ ‖v + w‖ with h2 | h2
    · calc
        min ‖u - w‖ ‖u + w‖ ≤ ‖u - w‖ := min_le_left _ _
        _ = ‖(u - v) + (v - w)‖ := by congr 1; module
        _ ≤ ‖u - v‖ + ‖v - w‖ := norm_add_le _ _
        _ = min ‖u - v‖ ‖u + v‖ + min ‖v - w‖ ‖v + w‖ := by
          rw [min_eq_left h1, min_eq_left h2]
    · calc
        min ‖u - w‖ ‖u + w‖ ≤ ‖u + w‖ := min_le_right _ _
        _ = ‖(u - v) + (v + w)‖ := by congr 1; module
        _ ≤ ‖u - v‖ + ‖v + w‖ := norm_add_le _ _
        _ = min ‖u - v‖ ‖u + v‖ + min ‖v - w‖ ‖v + w‖ := by
          rw [min_eq_left h1, min_eq_right h2]
  · rcases le_total ‖v - w‖ ‖v + w‖ with h2 | h2
    · calc
        min ‖u - w‖ ‖u + w‖ ≤ ‖u + w‖ := min_le_right _ _
        _ = ‖(u + v) - (v - w)‖ := by congr 1; module
        _ ≤ ‖u + v‖ + ‖v - w‖ := norm_sub_le _ _
        _ = min ‖u - v‖ ‖u + v‖ + min ‖v - w‖ ‖v + w‖ := by
          rw [min_eq_right h1, min_eq_left h2]
    · calc
        min ‖u - w‖ ‖u + w‖ ≤ ‖u - w‖ := min_le_left _ _
        _ = ‖(u + v) - (v + w)‖ := by congr 1; module
        _ ≤ ‖u + v‖ + ‖v + w‖ := norm_sub_le _ _
        _ = min ‖u - v‖ ‖u + v‖ + min ‖v - w‖ ‖v + w‖ := by
          rw [min_eq_right h1, min_eq_right h2]

/-- **Fibered cardinality bound.**  If every element of `A` is sent into `B` and each fibre has at
most `m` elements, then `A.card ≤ B.card * m`.  This is the combinatorial half of the packing count:
the contributing parents are fibered over a separated set of their centres. -/
theorem card_le_mul_of_fibered {α β : Type*} [DecidableEq β] (A : Finset α) (B : Finset β)
    (f : α → β) (hf : ∀ a ∈ A, f a ∈ B) {m : ℕ}
    (hm : ∀ b ∈ B, (A.filter fun a => f a = b).card ≤ m) :
    A.card ≤ B.card * m := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise hf]
  calc
    ∑ b ∈ B, (A.filter fun a => f a = b).card ≤ ∑ _b ∈ B, m := Finset.sum_le_sum hm
    _ = B.card * m := by simp [Finset.sum_const]

/-- **The tube parameter distance**: the larger of the centre distance and the projective distance
between directions.  Two `δ`-tubes at parameter distance `≤ c` lie in each other's rescale to radius
`δ + 3c/2` (`Kakeya.Tube.carrier_subset_rescale_of_center_dir_close`); conversely containment in a
common `r`-tube bounds the parameter distance by `12 r`
(`Kakeya.tubeParamDist_le_of_subset_common`).  Using `max` rather than two separate conditions is
what makes the separation relation of the parent construction a single inequality. -/
def tubeParamDist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : ℝ≥0} (T₁ T₂ : Tube δ E) : ℝ :=
  max (dist T₁.center T₂.center)
    (min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖)

/-- The parameter distance is symmetric. -/
theorem tubeParamDist_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : ℝ≥0} (T₁ T₂ : Tube δ E) : tubeParamDist T₁ T₂ = tubeParamDist T₂ T₁ := by
  unfold tubeParamDist
  rw [show dist T₁.center T₂.center = dist T₂.center T₁.center by exact dist_comm _ _]
  rw [show min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ =
        min ‖T₂.direction - T₁.direction‖ ‖T₂.direction + T₁.direction‖ by
    rw [norm_sub_rev]
    rw [add_comm]]

/-- The parameter distance is nonnegative. -/
theorem tubeParamDist_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : ℝ≥0} (T₁ T₂ : Tube δ E) : 0 ≤ tubeParamDist T₁ T₂ := by
  unfold tubeParamDist
  exact le_trans dist_nonneg (le_max_left _ _)

/-- The centre distance is bounded by the parameter distance. -/
theorem dist_center_le_tubeParamDist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {δ : ℝ≥0} (T₁ T₂ : Tube δ E) :
    dist T₁.center T₂.center ≤ tubeParamDist T₁ T₂ := le_max_left _ _

/-- The projective direction distance is bounded by the parameter distance. -/
theorem projDist_le_tubeParamDist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {δ : ℝ≥0} (T₁ T₂ : Tube δ E) :
    min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ ≤ tubeParamDist T₁ T₂ :=
  le_max_right _ _

/-- The parameter distance satisfies the triangle inequality: it is the max of two pseudometrics. -/
theorem tubeParamDist_triangle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {δ : ℝ≥0} (T₁ T₂ T₃ : Tube δ E) :
    tubeParamDist T₁ T₃ ≤ tubeParamDist T₁ T₂ + tubeParamDist T₂ T₃ := by
  simp only [tubeParamDist]
  refine max_le ?_ ?_
  · calc
      dist T₁.center T₃.center ≤ dist T₁.center T₂.center + dist T₂.center T₃.center :=
        dist_triangle _ _ _
      _ ≤ _ := add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc
      min ‖T₁.direction - T₃.direction‖ ‖T₁.direction + T₃.direction‖ ≤
          min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ +
          min ‖T₂.direction - T₃.direction‖ ‖T₂.direction + T₃.direction‖ :=
        projDist_triangle _ _ _
      _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)

/-- **Parameter distance from a common containing tube.**  Two `δ`-tubes inside a common `r`-tube
are at parameter distance at most `12 r`: rigidity puts each within `3r` in centre and `6r` in
projective direction of the containing tube, and both coordinates then compose. -/
theorem tubeParamDist_le_of_subset_common
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ r : ℝ≥0} (T₁ T₂ : Tube δ E) (V : Tube r E)
    (h₁ : (T₁.carrier : Set E) ⊆ (V.carrier : Set E))
    (h₂ : (T₂.carrier : Set E) ⊆ (V.carrier : Set E)) (hr : (r : ℝ) ≤ 1 / 4) :
    tubeParamDist T₁ T₂ ≤ 12 * (r : ℝ) := by
  obtain ⟨hc1, hd1⟩ := Tube.center_dir_close_of_subset T₁ V h₁ hr
  obtain ⟨hc2, hd2⟩ := Tube.center_dir_close_of_subset T₂ V h₂ hr
  simp only [tubeParamDist]
  refine max_le ?_ ?_
  · calc
      dist T₁.center T₂.center ≤ dist T₁.center V.center + dist V.center T₂.center :=
        dist_triangle _ _ _
      _ ≤ 3 * (r:ℝ) + 3 * (r:ℝ) := by
        rw [dist_comm V.center T₂.center]
        exact add_le_add hc1 hc2
      _ ≤ 12 * (r:ℝ) := by nlinarith [NNReal.coe_nonneg r]
  · -- directions
    calc
      min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ ≤
          min ‖T₁.direction - V.direction‖ ‖T₁.direction + V.direction‖ +
          min ‖V.direction - T₂.direction‖ ‖V.direction + T₂.direction‖ :=
        projDist_triangle _ _ _
      _ ≤ 6 * (r:ℝ) + 6 * (r:ℝ) := by
        refine add_le_add hd1 ?_
        rw [show ‖V.direction - T₂.direction‖ = ‖T₂.direction - V.direction‖
          from norm_sub_rev _ _]
        rw [show ‖V.direction + T₂.direction‖ = ‖T₂.direction + V.direction‖ by rw [add_comm]]
        exact hd2
      _ = 12 * (r:ℝ) := by ring

/-- Containment in a rescale from a parameter-distance bound: the `Kakeya.tubeParamDist` form of
`Kakeya.Tube.carrier_subset_rescale_of_center_dir_close`. -/
theorem carrier_subset_rescale_of_tubeParamDist_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : ℝ≥0} (T₁ T₂ : Tube δ E) {c : ℝ} (hc0 : 0 ≤ c) (h : tubeParamDist T₁ T₂ ≤ c)
    {s : ℝ≥0} (hs : (δ : ℝ) + 3 * c / 2 ≤ (s : ℝ)) :
    (T₁.carrier : Set E) ⊆ ((T₂.rescale s).carrier : Set E) :=
  Tube.carrier_subset_rescale_of_center_dir_close T₁ T₂ hc0
    (le_trans (dist_center_le_tubeParamDist T₁ T₂) h)
    (le_trans (projDist_le_tubeParamDist T₁ T₂) h) hs

/-- A tube is at parameter distance `0` from itself. -/
theorem tubeParamDist_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : ℝ≥0} (T : Tube δ E) : tubeParamDist T T = 0 := by
  unfold tubeParamDist
  rw [dist_self, sub_self, norm_zero,
    min_eq_left (show (0 : ℝ) ≤ ‖T.direction + T.direction‖ from norm_nonneg _)]
  rw [max_eq_left le_rfl]

/-- The absolute constant in `Kakeya.card_le_of_tubeParamDist_separated`.  Its value is immaterial —
only that it depends on nothing — so it is taken generously rather than optimised: the centre
packing contributes `4001 ^ 3` and the direction packing `250 * 1000 ^ 3 + 250`. -/
noncomputable def tubeParamPackingConst : ℝ := 10 ^ 30

/-- **Packing bound for a parameter-separated family of tubes.**

A family of `δ`-tubes pairwise `sep`-separated in `Kakeya.tubeParamDist`, all within parameter
distance `R ≤ 1000 * sep` of one base tube, has absolutely bounded cardinality.

The count factors, and this is exactly why `tubeParamDist` is a `max`: fiber the family over a
maximal `sep/2`-separated set of *centres* (bounded by `Kakeya.card_le_of_separated_in_ball`, since
centre distance is dominated by parameter distance); inside one fibre two members have centres
within `sep`, so separation forces their *directions* `sep`-projectively separated, which is bounded
by `Kakeya.card_le_of_projective_separated_in_cap`.  `Kakeya.card_le_mul_of_fibered` multiplies the
two. -/
theorem card_le_of_tubeParamDist_separated
    {ι : Type*} {δ : ℝ≥0} (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (A : Finset ι) {sep R : ℝ} (hsep : 0 < sep) (hRsep : R ≤ 1000 * sep)
    (hAsep : ∀ k ∈ A, ∀ k' ∈ A, k ≠ k' → sep < tubeParamDist (T k) (T k'))
    (k₀ : ι) (hA : ∀ k ∈ A, tubeParamDist (T k) (T k₀) ≤ R) :
    (A.card : ℝ) ≤ tubeParamPackingConst := by
  classical
  by_cases hA0 : A.card = 0
  · rw [hA0]
    norm_num [tubeParamPackingConst]
  · have hAnon : ∃ k : ι, k ∈ A := by
      rcases A.eq_empty_or_nonempty with hAe | hAnon
      · exfalso
        rw [hAe] at hA0
        exact hA0 rfl
      · exact hAnon
    obtain ⟨ka, hka⟩ := hAnon
    have hRge : 0 ≤ R := le_trans (tubeParamDist_nonneg (T ka) (T k₀)) (hA ka hka)
    by_cases hRpos : 0 < R
    · -- MAIN case: positive radius.
      -- STEP 1: maximal sep/2-separated set of centres.
      obtain ⟨S, hSsub, hSsep, hSsat⟩ :=
        exists_max_card_separated A (fun k k' => sep / 2 < dist (T k).center (T k').center)
          (by intro i j h
              rwa [dist_comm])
      have hs_sat : ∀ k ∈ A, ∃ i ∈ S, i = k ∨ dist (T i).center (T k).center ≤ sep / 2 := by
        intro k hk
        rcases hSsat k hk with ⟨i, hi, h⟩
        refine ⟨i, hi, ?_⟩
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (not_lt.mp h)
      -- The assignment map (fibres A over S).
      let f : ι → ι := fun k =>
        if h : ∃ i ∈ S, (i = k ∨ dist (T i).center (T k).center ≤ sep / 2) then Classical.choose h
        else k
      have hf_mem : ∀ k ∈ A, f k ∈ S := by
        intro k hk
        dsimp [f]
        rw [dif_pos (hs_sat k hk)]
        exact (Classical.choose_spec (hs_sat k hk)).1
      have hf_prop : ∀ k ∈ A, (f k = k ∨ dist (T (f k)).center (T k).center ≤ sep / 2) := by
        intro k hk
        dsimp [f]
        rw [dif_pos (hs_sat k hk)]
        exact (Classical.choose_spec (hs_sat k hk)).2
      -- STEP 2: bound S by the centre packing.
      let V : Finset (EuclideanSpace ℝ (Fin 3)) := S.image fun k => (T k).center
      have hV_in : ∀ v ∈ V, ‖v - (T k₀).center‖ ≤ R := by
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨k, hkS, hkv⟩
        have hkA : k ∈ A := hSsub hkS
        rw [← hkv, ← dist_eq_norm]
        exact le_trans (dist_center_le_tubeParamDist (T k) (T k₀)) (hA k hkA)
      have hsep2 : 0 < sep / 2 := by positivity
      have hV_sep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → sep / 2 ≤ ‖x - y‖ := by
        intro x hx y hy hxy
        rcases Finset.mem_image.mp hx with ⟨i, hi, hxi⟩
        rcases Finset.mem_image.mp hy with ⟨j, hj, hyj⟩
        by_cases hij : i = j
        · subst hij
          exfalso
          exact hxy (by rw [← hxi, ← hyj])
        · have hsi := hSsep i hi j hj hij
          rw [← hxi, ← hyj, ← dist_eq_norm]
          exact le_of_lt hsi
      have hmap_inj : Set.InjOn (fun k : ι => (T k).center) (S : Set ι) := by
        intro i hi j hj hc
        by_contra hij
        have hsi := hSsep i hi j hj hij
        have hd0 : dist (T i).center (T j).center = 0 := by
          have hc' : (T i).center = (T j).center := by simpa using hc
          rw [← hc', dist_self]
        nlinarith
      have hVcard : V.card = S.card := by
        dsimp [V]
        exact Finset.card_image_of_injOn hmap_inj
      have hfin : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) = 3 :=
        finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
      let base : ℝ := (R + (sep / 2) / 2) / ((sep / 2) / 2)
      have hratio : base = (R + sep / 4) / (sep / 4) := by
        dsimp [base]
        ring
      have hS3 : (S.card : ℝ) ≤ ((R + sep / 4) / (sep / 4)) ^ 3 := by
        rw [← hVcard]
        calc
          (V.card : ℝ) ≤ base ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
            card_le_of_separated_in_ball (s := V) (c := (T k₀).center) (R := R) (r := sep / 2)
              (hr := hsep2) (hR := hRge) hV_in hV_sep
          _ = base ^ 3 := by rw [hfin]
          _ = ((R + sep / 4) / (sep / 4)) ^ 3 := by rw [hratio]
      have hSbound : (S.card : ℝ) ≤ (4001 : ℝ) ^ 3 := by
        have hbase0 : 0 ≤ (R + sep / 4) / (sep / 4) := by positivity
        have hbase : (R + sep / 4) / (sep / 4) ≤ (4001 : ℝ) := by
          have hspos : (0 : ℝ) < sep / 4 := by positivity
          rw [div_le_iff₀ hspos]
          nlinarith [hRsep]
        exact hS3.trans (pow_le_pow_left₀ hbase0 hbase 3)
      -- STEP 3: bound each fibre by direction packing.
      let fibB : ℝ := 250 * (1000 ^ 3 : ℝ) + 250
      let dproj : ι → ι → ℝ := fun a b => min ‖(T a).direction - (T b).direction‖
        ‖(T a).direction + (T b).direction‖
      have hFibReal : ∀ b ∈ S, ((A.filter fun k => f k = b).card : ℝ) ≤ fibB := by
        intro b hb
        let Fib : Finset ι := A.filter fun k => f k = b
        let D : Finset (EuclideanSpace ℝ (Fin 3)) := Fib.image fun k => (T k).direction
        have hFib_memA : ∀ k ∈ Fib, k ∈ A := by
          intro k hk
          exact (Finset.mem_filter.mp hk).1
        have hFib_center : ∀ k ∈ Fib, dist (T b).center (T k).center ≤ sep / 2 := by
          intro k hk
          have hkA : k ∈ A := hFib_memA k hk
          have hkeq : f k = b := (Finset.mem_filter.mp hk).2
          have hprop := hf_prop k hkA
          rw [hkeq] at hprop
          rcases hprop with hbk | hck
          · rw [← hbk]
            simpa using show (0 : ℝ) ≤ sep / 2 by positivity
          · exact hck
        have hFib_pair_c : ∀ k₁ ∈ Fib, ∀ k₂ ∈ Fib, k₁ ≠ k₂ →
            dist (T k₁).center (T k₂).center ≤ sep := by
          intro k₁ hk₁ k₂ hk₂ hk₁₂
          calc
            dist (T k₁).center (T k₂).center
                ≤ dist (T k₁).center (T b).center + dist (T b).center (T k₂).center :=
              dist_triangle _ _ _
            _ ≤ sep / 2 + sep / 2 := by
              exact add_le_add
                (by simpa [dist_comm] using hFib_center k₁ hk₁) (hFib_center k₂ hk₂)
            _ = sep := by ring
        have hFib_dirsep : ∀ k₁ ∈ Fib, ∀ k₂ ∈ Fib, k₁ ≠ k₂ → sep ≤ dproj k₁ k₂ := by
          intro k₁ hk₁ k₂ hk₂ hk₁₂
          have hsep_lt := hAsep k₁ (hFib_memA k₁ hk₁) k₂ (hFib_memA k₂ hk₂) hk₁₂
          have hmk : sep < max (dist (T k₁).center (T k₂).center) (dproj k₁ k₂) := by
            simpa [tubeParamDist, dproj] using hsep_lt
          have hc_le : dist (T k₁).center (T k₂).center ≤ sep := hFib_pair_c k₁ hk₁ k₂ hk₂ hk₁₂
          by_contra h
          have hmin_le : dproj k₁ k₂ ≤ sep := le_of_lt (lt_of_not_ge h)
          have hmax_le : max (dist (T k₁).center (T k₂).center) (dproj k₁ k₂) ≤ sep :=
            max_le hc_le hmin_le
          linarith
        have hdir_inj : Set.InjOn (fun k : ι => (T k).direction) (Fib : Set ι) := by
          intro k₁ hk₁ k₂ hk₂ hd
          by_contra hk₁₂
          have hsepdir := hFib_dirsep k₁ hk₁ k₂ hk₂ hk₁₂
          have hmm : dproj k₁ k₂ = 0 := by
            have hd' : (T k₁).direction = (T k₂).direction := by simpa using hd
            dsimp [dproj]
            rw [hd']
            simp
          have hgone : sep ≤ 0 := by simpa [hmm] using hsepdir
          nlinarith
        have hDcard_eq : D.card = Fib.card := by
          dsimp [D]
          exact Finset.card_image_of_injOn hdir_inj
        have hV_sepD : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → sep ≤ min ‖x - y‖ ‖x + y‖ := by
          intro x hx y hy hxy
          rcases Finset.mem_image.mp hx with ⟨k₁, hk₁F, hx1⟩
          rcases Finset.mem_image.mp hy with ⟨k₂, hk₂F, hy2⟩
          have hk₁₂ : k₁ ≠ k₂ := by
            intro hkeq
            subst hkeq
            apply hxy
            rw [← hx1, ← hy2]
          have hdsep := hFib_dirsep k₁ hk₁F k₂ hk₂F hk₁₂
          rw [← hx1, ← hy2]
          exact hdsep
        have hD_unit : ∀ x ∈ D, ‖x‖ = 1 := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨k, hkF, hxk⟩
          rw [← hxk]
          exact Tube.norm_direction (T k)
        have hD_cap : ∀ x ∈ D, min ‖x - (T k₀).direction‖ ‖x + (T k₀).direction‖ ≤ R := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨k, hkF, hxk⟩
          rw [← hxk]
          exact le_trans (projDist_le_tubeParamDist (T k) (T k₀)) (hA k (hFib_memA k hkF))
        have hproj := card_le_of_projective_separated_in_cap (V := D) (e := (T k₀).direction)
            (_he_unit := Tube.norm_direction (T k₀)) (_hV_unit := hD_unit)
            (R := R) (r := sep) (_hr_pos := hsep) (_hR_pos := hRpos)
            (_hV_sep := hV_sepD) (_hV_cap := hD_cap)
        have hDbound : (D.card : ℝ) ≤ (250 : ℝ) * (R / sep) ^ 3 + 250 := by
          have hc : projectiveCapPackingConstant (EuclideanSpace ℝ (Fin 3)) = 250 := by
            rw [projectiveCapPackingConstant, hfin]
            norm_num
          have hn : (R / sep) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = (R / sep) ^ 3 := by
            rw [hfin]
          calc
            (D.card : ℝ) ≤ projectiveCapPackingConstant (EuclideanSpace ℝ (Fin 3)) *
                (R / sep) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) +
                projectiveCapPackingConstant (EuclideanSpace ℝ (Fin 3)) := hproj
            _ = 250 * (R / sep) ^ 3 + 250 := by rw [hc, hn]
        have hFibcard : (Fib.card : ℝ) ≤ (250 : ℝ) * (R / sep) ^ 3 + 250 := by
          rw [← hDcard_eq]
          exact hDbound
        have hFratio : R / sep ≤ 1000 := by
          rw [div_le_iff₀ hsep]
          exact hRsep
        have hFratio0 : 0 ≤ R / sep := by positivity
        have hF324 : (250 : ℝ) * (R / sep) ^ 3 + 250 ≤ 250 * (1000 ^ 3 : ℝ) + 250 := by
          have hFpow : (R / sep) ^ 3 ≤ (1000 : ℝ) ^ 3 := pow_le_pow_left₀ hFratio0 hFratio 3
          nlinarith
        have hRbound : (Fib.card : ℝ) ≤ 250 * (1000 ^ 3 : ℝ) + 250 :=
          hFibcard.trans hF324
        simpa [Fib] using hRbound
      have hFibNat : ∀ b ∈ S, (A.filter fun k => f k = b).card ≤ (250 * (1000 ^ 3) + 250 : ℕ) := by
        intro b hb
        have hc : ((250 * (1000 ^ 3) + 250 : ℕ) : ℝ) = fibB := by
          dsimp [fibB]
          norm_num
        have href : ((A.filter fun k => f k = b).card : ℝ)
            ≤ (((250 * (1000 ^ 3) + 250 : ℕ) : ℝ)) := by
          rw [hc]
          exact hFibReal b hb
        exact_mod_cast href
      have hfib := card_le_mul_of_fibered (A := A) (B := S) (f := f) hf_mem
        (m := 250 * (1000 ^ 3) + 250) hFibNat
      -- STEP 4: combine.
      have h4001 : (4001 : ℝ) ^ 3 ≤ 10 ^ 11 := by norm_num
      have hbig : (250 * (1000 ^ 3) + 250 : ℝ) ≤ 10 ^ 12 := by norm_num
      calc
        (A.card : ℝ) ≤ (S.card : ℝ) * (250 * (1000 ^ 3) + 250 : ℝ) := by exact_mod_cast hfib
        _ ≤ (4001 : ℝ) ^ 3 * (250 * (1000 ^ 3) + 250 : ℝ) := by
          exact mul_le_mul_of_nonneg_right hSbound (by positivity)
        _ ≤ 10 ^ 11 * 10 ^ 12 := by
          gcongr
        _ ≤ 10 ^ 23 := by norm_num
        _ ≤ 10 ^ 30 := by norm_num
        _ ≤ tubeParamPackingConst := by norm_num [tubeParamPackingConst]
    · -- degenerate case R ≤ 0
      have hRle0 : R ≤ 0 := le_of_not_gt hRpos
      have hA1 : A.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        by_contra hab
        have hd : tubeParamDist (T a) (T b) ≤ 0 := by
          calc
            tubeParamDist (T a) (T b) ≤ tubeParamDist (T a) (T k₀) + tubeParamDist (T k₀) (T b) :=
              tubeParamDist_triangle (T a) (T k₀) (T b)
            _ ≤ R + R := by
              exact add_le_add (hA a ha) (by simpa [tubeParamDist_comm] using hA b hb)
            _ ≤ 0 := by
              nlinarith
        have hd0 : tubeParamDist (T a) (T b) = 0 :=
          le_antisymm hd (tubeParamDist_nonneg (T a) (T b))
        have : sep < tubeParamDist (T a) (T b) := hAsep a ha b hb hab
        nlinarith
      calc
        (A.card : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hA1
        _ ≤ tubeParamPackingConst := by norm_num [tubeParamPackingConst]

/-! ### The external parent system -/

open Classical in
/-- **The external coarse parent system of GWZ Proposition 6.6(A).**

The raw tuple `(r, R, assign, hover)` of the previous signature, packaged.  The coarse tubes have
the exact radius `ρ` that the local plank factorisation expects, and the *test* radius carries fixed
dilation `8`, which is where the geometry of the confinement step lands (the contributing actual
factor bodies lie within `≈ 2b` of a thickened plank's long axis, and the derived scale relation is
`b ≤ 2ρ`, so `4b ≤ 8ρ`).

`boundedOverlapThroughLeaves` is the *only* quantitative property, and it is leaf-mediated: it
counts coarse indices that own a fine leaf inside the test tube.  It is deliberately **not**
pairwise essential distinctness of `parentTube`, a strictly stronger and unnecessary demand, and it
makes no reference to the sticky hierarchy. -/
structure ExternalParentSystem {ι : Type*} (q : Finset ι) {δ : ℝ≥0}
    (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))) (ρ Cu : ℝ≥0) where
  /-- Index type of the coarse parents. -/
  Parent : Type
  /-- The coarse parents actually used. -/
  parents : Finset Parent
  /-- The coarse tube of each parent, at the exact scale `ρ`. -/
  parentTube : Parent → Tube ρ (EuclideanSpace ℝ (Fin 3))
  /-- The coarse parent of each fine leaf. -/
  assign : ι → Parent
  /-- Every fine leaf is assigned to a parent in use. -/
  assign_mem : ∀ i ∈ q, assign i ∈ parents
  /-- Every fine leaf lies in its coarse parent. -/
  leaf_le_parent : ∀ i ∈ q,
    (T i).toConvexSpaceBody ≤ (parentTube (assign i)).toConvexSpaceBody
  /-- **Leaf-mediated bounded overlap.**  For every test tube of radius `8 * ρ`, at most `Cu` coarse
  parents own a fine leaf lying inside it. -/
  boundedOverlapThroughLeaves : ∀ V : Tube (8 * ρ) (EuclideanSpace ℝ (Fin 3)),
    (((parents.filter fun k => ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : ℝ≥0) ≤ Cu

/-! ### Construction of the parent system away from the leaf scale

The construction below covers every `ρ` with `4 * δ ≤ ρ ≤ 1`, in a single theorem: the *same*
separated family serves the middle and the coarse regime, and only the way its overlap is counted
differs.

* the parents are a maximum-cardinality subfamily of the leaves, pairwise `ρ/8`-separated in
  `Kakeya.tubeParamDist`, each rescaled to radius exactly `ρ`;
* `assign` sends a leaf to a selected leaf within parameter distance `ρ/8`, which exists by
  saturation of a maximum-cardinality separated family (`Kakeya.exists_max_card_separated`);
* containment of a leaf in its parent is `Kakeya.carrier_subset_rescale_of_tubeParamDist_le`, whose
  budget `δ + 3ρ/16 ≤ ρ` is exactly what `4 * δ ≤ ρ` buys;
* bounded overlap is `Kakeya.card_le_of_tubeParamDist_separated`, applied with `sep = ρ/8` and a
  diameter bound `R` obtained in two different ways:
  - if `32 * ρ ≤ 1`, longitudinal rigidity applies to the test tube of radius `8 * ρ`, so any two
    contributing parents are within `R = 97 * ρ` (`12 * 8ρ` for the two witness leaves, plus `ρ/8`
    at each end);
  - otherwise `ρ > 1/32`, rigidity is unavailable but unnecessary: the whole family lies in `B₁`, so
    `R = 2` works, and `2 ≤ 1000 * (ρ/8)` because `ρ > 1/32`.

No uniformity, no hierarchy, no essential distinctness of the coarse family, and no `δ`-dependent
loss: `Cu` is the absolute constant `Kakeya.tubeParamPackingConst`. -/

/-! ### The projective direction distance, as a pseudometric

`Kakeya.projDist_triangle` is the substantive half; symmetry and vanishing on the diagonal are
recorded here so that `dproj u v := min ‖u - v‖ ‖u + v‖` is available as a genuine pseudometric on
directions, without quotienting by `±`. -/

/-- The projective direction distance is symmetric. -/
theorem projDist_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u v : E) :
    min ‖u - v‖ ‖u + v‖ = min ‖v - u‖ ‖v + u‖ := by
  rw [norm_sub_rev u v, show u + v = v + u from add_comm u v]

/-- The projective direction distance vanishes on the diagonal. -/
theorem projDist_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E) :
    min ‖u - u‖ ‖u + u‖ = 0 := by
  rw [sub_self, norm_zero]
  exact min_eq_left (norm_nonneg _)

/-- The projective direction distance is nonnegative. -/
theorem projDist_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u v : E) :
    0 ≤ min ‖u - v‖ ‖u + v‖ := le_min (norm_nonneg _) (norm_nonneg _)

/-! ### The near-scale regime: fine-family ED packing inside an `O(δ)` tube

At the leaf scale there is no radius slack: a parent tube of radius `ρ ≈ δ` contains a leaf only if
it nearly coincides with it, so the parents must be the leaves themselves and bounded overlap
becomes the statement that boundedly many leaves fit in a test tube of radius `8ρ < 32δ`.  That is
false
without a leaf-packing hypothesis — take many equal leaves — so the near regime genuinely needs
**pairwise essential distinctness of the fine family**, which is threaded in explicitly.

The count is supplied by the repository's Córdoba/Wolff machinery,
`Kakeya.badAgainstSet_count_le_of_ED_thinBox`, whose bound `⌈C_dim * M ^ 2 / c ^ n⌉₊` is absolute.
Applying it needs three bridges, proved below: a positive-volume set is never essentially distinct
from itself, so containment alone makes a leaf "bad" against the reference set; the reference set
`cthickening (99 * δ) (V.rescale δ).carrier` is the `100δ`-rescale of `V` and therefore contains `V`
whenever `8ρ ≤ 100δ`; and its volume is `O(δ ^ (n-1))`, giving an absolute `M`. -/

/-- A tube is never essentially distinct from itself: its carrier has positive finite volume, and
`IsEssentiallyDistinct A A` would force `volume A ≤ volume A / 2`. -/
theorem Tube.not_isEssentiallyDistinct_self
    {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (T : Tube δ (EuclideanSpace ℝ (Fin 3))) :
    ¬ IsEssentiallyDistinct (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  have hc : (0 : ENNReal) <
      (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) := by
    exact_mod_cast Tube.le_volume.c_pos _
  have hd_ne : (δ : ENNReal) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast hδ0.ne.symm)
  have hbdd : (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) *
      (δ : ENNReal) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) ≤
      volume (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    simpa using (Tube.le_volume (T := T))
  have hc_ne : (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ≠ 0 :=
    by exact_mod_cast (ne_of_gt (Tube.le_volume.c_pos _))
  have hV0 : volume (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.mul_pos hc_ne hd_ne) hbdd)
  have hVtop : volume (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ := by
    have hleup : volume (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≤
        ((Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) *
          δ ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) : NNReal) : ENNReal) := by
      simpa [ENNReal.coe_mul, ENNReal.coe_pow] using (Tube.volume_le hδ1 T)
    have hneup : ((Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) *
        δ ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) : NNReal) : ENNReal) ≠ ⊤ :=
      ENNReal.coe_ne_top
    exact ne_of_lt (lt_of_le_of_lt hleup (lt_top_iff_ne_top.mpr hneup))
  exact _root_.not_isEssentiallyDistinct_self hV0 hVtop

/-- **Containment makes a tube bad against a set**, at the canonical density threshold
`c_vol / (2 * C_vol)` used by `Kakeya.badAgainstSet_count_le_of_ED_thinBox`.  The
`δ ^ (n-1)` factors in the two tube-volume bounds cancel in the ratio, which is why the threshold
is scale-free. -/
theorem badAgainstSet_of_subset
    {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hsub : (T.carrier : Set _) ⊆ K) :
    BadAgainstSet T K
      (((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal) : ℝ) /
        (2 * ((Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal) : ℝ))) := by
  let n := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
  have hn : n = 3 := by
    dsimp [n]
    exact finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
  let c_low : ℝ := ((Tube.le_volume.c n : NNReal) : ℝ) * (δ : ℝ) ^ (n - 1)
  let c_up : ℝ := ((Tube.volume_le.C n : NNReal) : ℝ) * (δ : ℝ) ^ (n - 1)
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have ofReal_c (r : NNReal) (c : ℝ) (hr : 0 ≤ (r : ℝ)) :
      ENNReal.ofReal ((r : ℝ) * c) = (r : ENNReal) * ENNReal.ofReal c := by
    rw [ENNReal.ofReal_mul hr, ENNReal.ofReal_coe_nnreal]
  have ofReal_powδ : ENNReal.ofReal ((δ : ℝ) ^ (n - 1)) = (δ : ENNReal) ^ (n - 1) := by
    rw [ENNReal.ofReal_pow hδr.le (n - 1), ENNReal.ofReal_coe_nnreal]
  have hcl : 0 < c_low := by
    dsimp [c_low]
    exact mul_pos (NNReal.coe_pos.mpr (Tube.le_volume.c_pos n)) (pow_pos hδr _)
  have hcu : 0 < c_up := by
    dsimp [c_up]
    exact mul_pos (NNReal.coe_pos.mpr (Tube.volume_le.C_pos n)) (pow_pos hδr _)
  have hc_low_eq : ENNReal.ofReal c_low =
      (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) := by
    dsimp [c_low]
    rw [ofReal_c (Tube.le_volume.c n) ((δ : ℝ) ^ (n - 1))
      (NNReal.coe_pos.mpr (Tube.le_volume.c_pos n)).le]
    rw [ofReal_powδ]
  have hc_up_eq : ENNReal.ofReal c_up =
      (Tube.volume_le.C n : ENNReal) * (δ : ENNReal) ^ (n - 1) := by
    dsimp [c_up]
    calc
      ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * (δ : ℝ) ^ (n - 1))
          = ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) * ENNReal.ofReal ((δ : ℝ) ^ (n - 1)) := by
              rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (n + 1))]
      _ = (2 : ENNReal) ^ (n + 1) * ENNReal.ofReal ((δ : ℝ) ^ (n - 1)) := by
              rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2) (n + 1)]
              norm_num
      _ = (2 : ENNReal) ^ (n + 1) * (δ : ENNReal) ^ (n - 1) := by
              rw [ofReal_powδ]
  have hvol_low : ENNReal.ofReal c_low ≤ volume (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [hc_low_eq, hn]
    simpa using (Tube.le_volume (T := T))
  have hvol_up : volume (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≤ ENNReal.ofReal c_up := by
    rw [hc_up_eq, hn]
    simpa using (Tube.volume_le hδ1 T)
  have hED : ¬ IsEssentiallyDistinct (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    Tube.not_isEssentiallyDistinct_self hδ0 hδ1 T
  have hbad := badAgainstSet_of_notED_subset_cthickening hδ0 T T K c_low c_up hcl hcu
    hvol_low hvol_up hsub hED
  have hcoef : c_low / (2 * c_up) =
      ((Tube.le_volume.c n : NNReal) : ℝ) / (2 * ((Tube.volume_le.C n : NNReal) : ℝ)) := by
    dsimp [c_low, c_up]
    have hr : (δ : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hδr)
    have hb : ((Tube.volume_le.C n : NNReal) : ℝ) ≠ 0 :=
      ne_of_gt (NNReal.coe_pos.mpr (Tube.volume_le.C_pos n))
    field_simp [hr, hb]
  rw [hcoef] at hbad
  simpa [n] using hbad

/-- Rescaling only remembers a tube's endpoints, so a rescale of a rescale is a rescale. -/
theorem Tube.rescale_rescale_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {δ : ℝ≥0} (T : Tube δ E) (a b : ℝ≥0) :
    (T.rescale a).rescale b = T.rescale b := rfl

/-- The `b`-thickening of the `a`-rescale of a tube is its `(a + b)`-rescale. -/
theorem Tube.cthickening_rescale_carrier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {δ : ℝ≥0} (T : Tube δ E) (a b : ℝ≥0) :
    Metric.cthickening (b : ℝ) ((T.rescale a).carrier : Set E)
      = ((T.rescale (a + b)).carrier : Set E) := by
  have h := Tube.cthickening_carrier (T.rescale a) b
  rw [Tube.rescale_rescale_eq] at h
  exact h

/-- **The reference tube of the near-scale count sits in a bounded ball.**

If a leaf `T` of the family lies both in the test tube `V` and in the unit ball, then longitudinal
rigidity pins `V`'s endpoints to within `3r` of `T`'s, so any rescale of `V` to radius `s` lies in
the ball of radius `1 + 3r + s`.  With `r = 8ρ`, `s = δ`, `ρ < 4δ` and `δ ≤ 1/128` this is `≤ 7/2`,
the containment `Kakeya.badAgainstSet_count_le_of_ED_thinBox` requires of its reference tube. -/
theorem Tube.rescale_carrier_subset_closedBall_of_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ r s : ℝ≥0} (T : Tube δ E) (V : Tube r E)
    (hTV : (T.carrier : Set E) ⊆ (V.carrier : Set E))
    (hTB : (T.carrier : Set E) ⊆ Metric.closedBall (0 : E) 1)
    (hr : (r : ℝ) ≤ 1 / 4) :
    ((V.rescale s).carrier : Set E)
      ⊆ Metric.closedBall (0 : E) (1 + 3 * (r : ℝ) + (s : ℝ)) := by
  have hTx : T.x ∈ (T.carrier : Set E) := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T.x, left_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self δ.coe_nonneg⟩
  have hTy : T.y ∈ (T.carrier : Set E) := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T.y, right_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self δ.coe_nonneg⟩
  have hTxn : ‖T.x‖ ≤ 1 := by simpa [dist_zero_right] using hTB hTx
  have hTyn : ‖T.y‖ ≤ 1 := by simpa [dist_zero_right] using hTB hTy
  -- V's endpoints are within 1 + 3r of the origin, in either orientation
  have key : ∀ (p w : E), ‖p‖ ≤ 1 → dist p w ≤ 3 * (r : ℝ) → ‖w‖ ≤ 1 + 3 * (r : ℝ) := by
    intro p w hp hd
    calc
      ‖w‖ = dist w (0 : E) := by simp
      _ ≤ dist w p + dist p (0 : E) := dist_triangle _ _ _
      _ ≤ 3 * (r : ℝ) + 1 := by
        rw [dist_comm w p]
        simpa [dist_zero_right] using add_le_add hd hp
      _ = 1 + 3 * (r : ℝ) := by ring
  have hV : ‖V.x‖ ≤ 1 + 3 * (r : ℝ) ∧ ‖V.y‖ ≤ 1 + 3 * (r : ℝ) := by
    rcases Tube.endpoints_close_of_subset T V hTV hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨key T.x V.x hTxn h1, key T.y V.y hTyn h2⟩
    · exact ⟨key T.y V.x hTyn h2, key T.x V.y hTxn h1⟩
  intro x hx
  rw [show ((V.rescale s).carrier : Set E)
      = ⋃ z ∈ segment ℝ V.x V.y, Metric.closedBall z (s : ℝ) from rfl] at hx
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
  have hzball : z ∈ Metric.closedBall (0 : E) (1 + 3 * (r : ℝ)) := by
    refine (convex_closedBall (0 : E) (1 + 3 * (r : ℝ))).segment_subset ?_ ?_ hz
    · simpa [dist_zero_right] using hV.1
    · simpa [dist_zero_right] using hV.2
  have hd : dist x z ≤ (s : ℝ) := Metric.mem_closedBall.mp hxz
  have hzball' : ‖z‖ ≤ 1 + 3 * (r : ℝ) := by
    simpa [dist_zero_right] using Metric.mem_closedBall.mp hzball
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖x‖ = dist x (0 : E) := by simp
    _ ≤ dist x z + dist z (0 : E) := dist_triangle _ _ _
    _ ≤ (s : ℝ) + (1 + 3 * (r : ℝ)) := by simpa [dist_zero_right] using add_le_add hd hzball'
    _ = 1 + 3 * (r : ℝ) + (s : ℝ) := by ring

/-- **Near-scale ED packing.**  For `δ ≤ ρ < 4 * δ`, boundedly many pairwise essentially distinct
leaves fit inside a test tube of radius `8 * ρ`, with an absolute constant.

Two regimes inside: below a threshold `δ₁` the Córdoba/Wolff count
`Kakeya.badAgainstSet_count_le_of_ED_thinBox` applies; above it `δ` is bounded below by an absolute
constant and `Tube.card_le_of_EssDistinct` bounds the whole family at once. -/
theorem exists_card_le_of_ED_in_tube :
    ∃ Cnear : ℝ, 0 < Cnear ∧
      ∀ {ι : Type} {δ ρ : ℝ≥0}, 0 < δ → δ ≤ ρ → ρ < 4 * δ →
      ∀ (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (q : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ∀ (V : Tube (8 * ρ) (EuclideanSpace ℝ (Fin 3))) (A : Finset ι), A ⊆ q →
        (∀ i ∈ A, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) →
        (A.card : ℝ) ≤ Cnear := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  let n := Module.finrank ℝ E
  have hn : n = 3 := by
    dsimp [n]
    exact finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
  obtain ⟨C_dim, δ₀, hC_dim, hδ₀, hδ₀1, hcount⟩ :=
    badAgainstSet_count_le_of_ED_thinBox (E := E)
      (by rw [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)]; norm_num)
  let δ₁ : ℝ := min δ₀ (1 / 128)
  have hδ₁pos : 0 < δ₁ := by
    dsimp [δ₁]
    exact lt_min hδ₀ (by norm_num)
  have hδ₁δ₀ : δ₁ ≤ δ₀ := by
    dsimp [δ₁]
    exact min_le_left _ _
  have hδ₁128 : δ₁ ≤ 1 / 128 := by
    dsimp [δ₁]
    exact min_le_right _ _
  let c : ℝ := ↑(Tube.le_volume.c n) / (2 * ↑(Tube.volume_le.C n))
  let M : ℝ := 160000
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos (NNReal.coe_pos.mpr (Tube.le_volume.c_pos n))
      (mul_pos (by norm_num) (NNReal.coe_pos.mpr (Tube.volume_le.C_pos n)))
  have hMpos : 0 < M := by
    dsimp [M]
    norm_num
  let Cnear : ℝ := max (⌈(C_dim : ℝ) * M ^ 2 / c ^ n⌉₊ : ℝ)
    (Tube.card_le_of_EssDistinct.C n * (1 / δ₁) ^ (2 * n))
  have hCnear_pos : 0 < Cnear := by
    dsimp [Cnear]
    have h2 : 0 < Tube.card_le_of_EssDistinct.C n * (1 / δ₁) ^ (2 * n) := by
      exact mul_pos (Tube.card_le_of_EssDistinct.C_pos (n := n))
        (pow_pos (one_div_pos.mpr hδ₁pos) _)
    exact lt_of_lt_of_le h2 (le_max_right _ _)
  refine ⟨Cnear, hCnear_pos, ?_⟩
  intro ι δ ρ hδ0 hδρ hρδ q T hball hEDq V A hAq hAV
  by_cases hsmall : (δ : ℝ) ≤ δ₁
  · -- SMALL branch
    rcases A.eq_empty_or_nonempty with hAe | hAnon
    · subst hAe
      simp only [Finset.card_empty, Nat.cast_zero]
      exact hCnear_pos.le
    · obtain ⟨i₁, hi₁⟩ := hAnon
      have hi₁q : i₁ ∈ q := hAq hi₁
      have hδ1 : δ ≤ 1 := by
        rw [← NNReal.coe_le_coe]
        exact le_trans hsmall (le_trans hδ₁128 (by norm_num))
      have hρd : (ρ : ℝ) < 4 * (δ : ℝ) := by exact_mod_cast hρδ
      have h8ρ14 : ((8 * ρ : ℝ≥0) : ℝ) ≤ (1 / 4 : ℝ) := by
        rw [NNReal.coe_mul]
        norm_num
        nlinarith
      have h100nn : (8 * ρ : ℝ≥0) ≤ (100 * δ : ℝ≥0) := by
        rw [← NNReal.coe_le_coe]
        rw [NNReal.coe_mul, NNReal.coe_mul]
        norm_num
        nlinarith [NNReal.coe_nonneg δ]
      have h100le1 : (100 * δ : ℝ≥0) ≤ 1 := by
        rw [← NNReal.coe_le_coe]
        rw [NNReal.coe_mul]
        norm_num
        nlinarith
      let T₀' : Tube δ E := V.rescale δ
      let K : Set E := Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier
      have hKeq : K = (V.rescale (100 * δ)).carrier := by
        have hthick := Tube.cthickening_carrier (δ := δ) T₀' (99 * δ)
        have h100δ : δ + 99 * δ = 100 * δ := by ring
        have hstep : (T₀'.rescale (100 * δ)).carrier = (V.rescale (100 * δ)).carrier := by
          dsimp [T₀']
          rfl
        calc
          K = Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier := rfl
          _ = Metric.cthickening (↑(99 * δ : ℝ≥0)) T₀'.carrier := by
              rw [show (↑(99 * δ : ℝ≥0) : ℝ) = 99 * (δ : ℝ) by
                norm_num [NNReal.coe_mul]]
          _ = (T₀'.rescale (δ + 99 * δ)).carrier := hthick
          _ = (T₀'.rescale (100 * δ)).carrier := by rw [h100δ]
          _ = (V.rescale (100 * δ)).carrier := hstep
      have hVc8 : V.carrier = (V.rescale (8 * ρ)).carrier := by
        rw [V.carrier_eq, (V.rescale (8 * ρ)).carrier_eq]
        simp [Tube.rescale]
      have hVcar8 : (V.rescale (8 * ρ)).toConvexSpaceBody ≤
          (V.rescale (100 * δ)).toConvexSpaceBody :=
        Tube.rescale_le_rescale_of_radius_le (T := V) (ρ₁ := 8 * ρ) (ρ₂ := 100 * δ) h100nn
      have hVK : (V.carrier : Set E) ⊆ K := by
        intro x hx
        have hx8 : x ∈ (V.rescale (8 * ρ)).carrier := by
          rwa [← hVc8]
        rw [hKeq]
        exact hVcar8 hx8
      have hsub_i1 : ((T i₁).carrier : Set E) ⊆ (V.carrier : Set E) := by
        change (((T i₁).toConvexSpaceBody : Set E) ⊆ (V.toConvexSpaceBody : Set E))
        exact (SetLike.coe_subset_coe (A := ConvexSpaceBody E) (S := (T i₁).toConvexSpaceBody)
          (T := V.toConvexSpaceBody)).mpr (hAV i₁ hi₁)
      have hend := Tube.endpoints_close_of_subset (T := T i₁) (V := V) (δ := δ) (r := 8 * ρ)
        hsub_i1 h8ρ14
      let R : ℝ := 1 + 3 * (8 * (ρ : ℝ))
      have hTx0 : dist (T i₁).x (0 : E) ≤ 1 := by
        have hmem : (T i₁).x ∈ (T i₁).carrier := by
          rw [(T i₁).carrier_eq]
          exact Set.mem_iUnion₂.mpr ⟨(T i₁).x, left_mem_segment ℝ (T i₁).x (T i₁).y,
            Metric.mem_closedBall_self (NNReal.coe_nonneg _)⟩
        exact Metric.mem_closedBall.mp (hball i₁ hi₁q hmem)
      have hTy0 : dist (T i₁).y (0 : E) ≤ 1 := by
        have hmem : (T i₁).y ∈ (T i₁).carrier := by
          rw [(T i₁).carrier_eq]
          exact Set.mem_iUnion₂.mpr ⟨(T i₁).y, right_mem_segment ℝ (T i₁).x (T i₁).y,
            Metric.mem_closedBall_self (NNReal.coe_nonneg _)⟩
        exact Metric.mem_closedBall.mp (hball i₁ hi₁q hmem)
      have hρcoef : ((8 * ρ : ℝ≥0) : ℝ) = 8 * (ρ : ℝ) := by
        norm_num [NNReal.coe_mul]
      have hVx0 : dist V.x (0 : E) ≤ R := by
        rcases hend with h | h
        · rw [hρcoef] at h
          calc
            dist V.x (0 : E) ≤ dist V.x (T i₁).x + dist (T i₁).x (0 : E) := dist_triangle _ _ _
            _ = dist (T i₁).x V.x + dist (T i₁).x (0 : E) := by rw [dist_comm]
            _ ≤ 3 * (8 * (ρ : ℝ)) + 1 := by nlinarith [h.1, hTx0]
            _ = R := by dsimp [R]; ring
        · rw [hρcoef] at h
          calc
            dist V.x (0 : E) ≤ dist V.x (T i₁).y + dist (T i₁).y (0 : E) := dist_triangle _ _ _
            _ = dist (T i₁).y V.x + dist (T i₁).y (0 : E) := by rw [dist_comm]
            _ ≤ 3 * (8 * (ρ : ℝ)) + 1 := by nlinarith [h.2, hTy0]
            _ = R := by dsimp [R]; ring
      have hVy0 : dist V.y (0 : E) ≤ R := by
        rcases hend with h | h
        · rw [hρcoef] at h
          calc
            dist V.y (0 : E) ≤ dist V.y (T i₁).y + dist (T i₁).y (0 : E) := dist_triangle _ _ _
            _ = dist (T i₁).y V.y + dist (T i₁).y (0 : E) := by rw [dist_comm]
            _ ≤ 3 * (8 * (ρ : ℝ)) + 1 := by nlinarith [h.2, hTy0]
            _ = R := by dsimp [R]; ring
        · rw [hρcoef] at h
          calc
            dist V.y (0 : E) ≤ dist V.y (T i₁).x + dist (T i₁).x (0 : E) := dist_triangle _ _ _
            _ = dist (T i₁).x V.y + dist (T i₁).x (0 : E) := by rw [dist_comm]
            _ ≤ 3 * (8 * (ρ : ℝ)) + 1 := by nlinarith [h.1, hTx0]
            _ = R := by dsimp [R]; ring
      have hseg : segment ℝ V.x V.y ⊆ Metric.closedBall (0 : E) R :=
        (convex_closedBall (0 : E) R).segment_subset
          (by rw [Metric.mem_closedBall]; exact hVx0)
          (by rw [Metric.mem_closedBall]; exact hVy0)
      have hcarrier' : T₀'.carrier ⊆ Metric.closedBall (0 : E) (R + (δ : ℝ)) := by
        intro x hx
        rw [T₀'.carrier_eq] at hx
        rcases Set.mem_iUnion₂.mp hx with ⟨z, hz, hxz⟩
        have hzV : z ∈ segment ℝ V.x V.y := by
          simpa [T₀', Tube.rescale] using hz
        rw [Metric.mem_closedBall]
        have hz0 : dist z (0 : E) ≤ R := Metric.mem_closedBall.mp (hseg hzV)
        have hxz0 : dist x z ≤ (δ : ℝ) := Metric.mem_closedBall.mp hxz
        calc
          dist x (0 : E) ≤ dist x z + dist z (0 : E) := dist_triangle x z 0
          _ ≤ R + (δ : ℝ) := by nlinarith
      have hRle : R + (δ : ℝ) ≤ 7 / 2 := by
        dsimp [R]
        nlinarith [hρd, hsmall, hδ₁128]
      have hK_in_B2 : T₀'.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) := by
        intro x hx
        exact Metric.mem_closedBall.mpr
          (le_trans (Metric.mem_closedBall.mp (hcarrier' hx)) hRle)
      have hM_le : ((Tube.volume_le.C n : ENNReal) *
          ((100 * δ : ℝ≥0) : ENNReal) ^ (n - 1)) ≤
          ENNReal.ofReal M * (δ : ENNReal) ^ (n - 1) := by
        rw [hn, show (3 - 1 : ℕ) = 2 by norm_num]
        have hC3 : Tube.volume_le.C 3 = 16 := by norm_num [Tube.volume_le.C]
        rw [hC3]
        have hMcoef : ENNReal.ofReal M = (160000 : ENNReal) := by
          norm_num [M, ENNReal.ofReal_natCast]
        rw [hMcoef]
        have have_eq : (16 : ENNReal) * ((100 * δ : ℝ≥0) : ENNReal) ^ 2
            = (160000 : ENNReal) * (δ : ENNReal) ^ 2 := by
          norm_num [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_natCast]
          ring
        exact le_of_eq have_eq
      have hM : volume K ≤ ENNReal.ofReal M * (δ : ENNReal) ^ (n - 1) := by
        rw [hKeq]
        exact (Tube.volume_le h100le1 (T := V.rescale (100 * δ))).trans hM_le
      have hbad : ∀ i ∈ A, BadAgainstSet ((T i).translate 0) K c := by
        intro i hi
        have hsub_i : (T i).carrier ⊆ K := by
          have hTV : (T i).carrier ⊆ V.carrier := by
            change ((T i).toConvexSpaceBody : Set E) ⊆ (V.toConvexSpaceBody : Set E)
            exact (SetLike.coe_subset_coe (A := ConvexSpaceBody E) (S := (T i).toConvexSpaceBody)
              (T := V.toConvexSpaceBody)).mpr (hAV i hi)
          intro x hx
          exact hVK (hTV hx)
        have htr : ((T i).translate 0).carrier = (T i).carrier := by
          change (((T i).translate 0).toConvexSpaceBody : Set E) = ((T i).toConvexSpaceBody : Set E)
          simp [Tube.translate]
        have hb0 := badAgainstSet_of_subset hδ0 hδ1 (T i) (hsub := hsub_i)
        have hc_eq : c = (↑(Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) /
            (2 * (↑(Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ)) := by
          simp [c, n]
        rw [hc_eq]
        simpa [BadAgainstSet, htr, E] using hb0
      have hED_A : (A : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) := by
        intro i hi j hj hij
        exact hEDq (show i ∈ (q : Set ι) from by simpa using hAq hi)
          (show j ∈ (q : Set ι) from by simpa using hAq hj) hij
      have hcountA : (A.filter fun i => BadAgainstSet ((T i).translate 0) K c).card ≤
          ⌈(C_dim : ℝ) * M ^ 2 / c ^ n⌉₊ := by
        simpa [c, n] using
          (hcount (ι := ι) hδ0 (le_trans hsmall hδ₁δ₀) A T T₀' hK_in_B2 M hMpos hM (0 : E)
            hED_A)
      have hfilter : A.filter (fun i => BadAgainstSet ((T i).translate 0) K c) = A := by
        apply Finset.ext
        intro x
        constructor
        · intro hx
          exact (Finset.mem_filter.mp hx).1
        · intro hx
          exact Finset.mem_filter.mpr ⟨hx, hbad x hx⟩
      have hAcard : A.card ≤ ⌈(C_dim : ℝ) * M ^ 2 / c ^ n⌉₊ := by
        simpa [hfilter] using hcountA
      have hA_real : (A.card : ℝ) ≤ ((⌈(C_dim : ℝ) * M ^ 2 / c ^ n⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast hAcard
      have hterm1 : ((⌈(C_dim : ℝ) * M ^ 2 / c ^ n⌉₊ : ℕ) : ℝ) ≤ Cnear := by
        dsimp [Cnear]
        exact le_max_left _ _
      exact hA_real.trans hterm1
  · -- LARGE branch
    have hbig : δ₁ < (δ : ℝ) := lt_of_not_ge hsmall
    have hAleq : (A.card : ℝ) ≤ (q.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hAq)
    have hq1 : (q.card : ℝ) ≤ Tube.card_le_of_EssDistinct.C n * (1 / (δ : ℝ)) ^ (2 * n) := by
      have hh := Tube.card_le_of_EssDistinct (δ := δ) hδ0 (r := 1) (s := q) (T := T) hball hEDq
      dsimp [n] at hh ⊢
      exact hh
    have hrecip : (1 / (δ : ℝ)) ^ (2 * n) ≤ (1 / δ₁) ^ (2 * n) := by
      have hδ1pos : 0 < (δ : ℝ) := by exact_mod_cast hδ0
      have hle : 1 / (δ : ℝ) ≤ 1 / δ₁ := by
        exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hδ₁pos (le_of_lt hbig)
      exact pow_le_pow_left₀ ((one_div_pos.mpr hδ1pos).le) hle (2 * n)
    have hq2 : (q.card : ℝ) ≤ Tube.card_le_of_EssDistinct.C n * (1 / δ₁) ^ (2 * n) := by
      have hcrec_nonneg : 0 ≤ Tube.card_le_of_EssDistinct.C n :=
        (Tube.card_le_of_EssDistinct.C_pos (n := n)).le
      exact le_trans hq1 (mul_le_mul_of_nonneg_left hrecip hcrec_nonneg)
    have h2leC : Tube.card_le_of_EssDistinct.C n * (1 / δ₁) ^ (2 * n) ≤ Cnear := by
      dsimp [Cnear]
      exact le_max_right _ _
    exact (hAleq.trans hq2).trans h2leC

/-- **Monotonicity in the overlap constant.**  A parent system with overlap bound `Cu` is also one
with any larger bound, since `boundedOverlapThroughLeaves` only gets weaker. -/
def ExternalParentSystem.monoConst {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ Cu Cu' : ℝ≥0}
    (PS : ExternalParentSystem q T ρ Cu) (h : Cu ≤ Cu') :
    ExternalParentSystem q T ρ Cu' where
  Parent := PS.Parent
  parents := PS.parents
  parentTube := PS.parentTube
  assign := PS.assign
  assign_mem := PS.assign_mem
  leaf_le_parent := PS.leaf_le_parent
  boundedOverlapThroughLeaves := fun V => le_trans (PS.boundedOverlapThroughLeaves V) h

/-- The centre of a tube lies in its carrier: it is a point of the core segment. -/
theorem Tube.center_mem_carrier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {δ : ℝ≥0} (T : Tube δ E) : T.center ∈ (T.carrier : Set E) := by
  rw [T.carrier_eq]
  refine Set.mem_iUnion₂.mpr
    ⟨T.center, midpoint_mem_segment T.x T.y, Metric.mem_closedBall_self δ.coe_nonneg⟩

/-- Two tubes whose carriers lie in the closed unit ball are at parameter distance at most `2`. -/
theorem tubeParamDist_le_two_of_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {δ : ℝ≥0} (T₁ T₂ : Tube δ E)
    (h₁ : (T₁.carrier : Set E) ⊆ Metric.closedBall (0 : E) 1)
    (h₂ : (T₂.carrier : Set E) ⊆ Metric.closedBall (0 : E) 1) :
    tubeParamDist T₁ T₂ ≤ 2 := by
  simp only [tubeParamDist]
  refine max_le ?_ ?_
  · have hc1 : ‖T₁.center‖ ≤ 1 := by
      have hT1' : dist T₁.center (0 : E) ≤ 1 :=
        Metric.mem_closedBall.mp (h₁ (Tube.center_mem_carrier T₁))
      simpa [dist_eq_norm] using hT1'
    have hc2 : ‖T₂.center‖ ≤ 1 := by
      have hT2' : dist T₂.center (0 : E) ≤ 1 :=
        Metric.mem_closedBall.mp (h₂ (Tube.center_mem_carrier T₂))
      simpa [dist_eq_norm] using hT2'
    calc
      dist T₁.center T₂.center ≤ ‖T₁.center‖ + ‖T₂.center‖ := by
        rw [dist_eq_norm]
        exact norm_sub_le _ _
      _ ≤ 1 + 1 := by exact add_le_add hc1 hc2
      _ = 2 := by norm_num
  · have hd : ‖T₁.direction - T₂.direction‖ ≤ 2 := by
      calc
        ‖T₁.direction - T₂.direction‖ ≤ ‖T₁.direction‖ + ‖T₂.direction‖ := norm_sub_le _ _
        _ = 1 + 1 := by
          rw [Tube.norm_direction T₁, Tube.norm_direction T₂]
        _ = 2 := by norm_num
    calc
      min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ ≤
          ‖T₁.direction - T₂.direction‖ := min_le_left _ _
      _ ≤ 2 := hd.trans (by norm_num)

/-! ### Packing, leafwise covering and overlap at an enlarged test radius

The `boundedOverlapThroughLeaves` field of `Kakeya.ExternalParentSystem` controls test tubes of
radius `8 ρ` only.  GWZ Proposition 6.6(A) needs the same control at a larger test radius
`Ctest * ρ`, because the `C_NC`-dilated plank test body of the corrected GWZ Lemma 6.4 confines the
contributing actual bodies only to a tube of that radius.

The parent scale is **not** enlarged.  Instead the large test tube is covered *leafwise* by a
bounded number of radius-`8 ρ` test tubes: a maximal `4 ρ`-separated subfamily of the
leaves inside `V` is selected, and each such selected leaf is inflated to radius `8 ρ`.
Every leaf inside `V` then sits inside one of the inflated tubes by
`Kakeya.carrier_subset_rescale_of_tubeParamDist_le` (budget `δ + 3·(4ρ)/2 ≤ 8 ρ`, which `δ ≤ ρ`
gives).  This is a genuine leafwise cover: it is *not* the false inference that a whole
leaf inside a union of carriers lies inside one member of the union. -/

/-- The packing constant at a general parameter-distance ratio `N`.  The two factors are the centre
packing `(4N+1)^3` of `Kakeya.card_le_of_separated_in_ball` and the direction packing
`250 N^3 + 250` of `Kakeya.card_le_of_projective_separated_in_cap`. -/
def tubeParamPackingConstOf (N : ℕ) : ℝ≥0 := ((4 * N + 1) ^ 3 * (250 * N ^ 3 + 250) : ℕ)

theorem one_le_tubeParamPackingConstOf (N : ℕ) : 1 ≤ tubeParamPackingConstOf N := by
  rw [tubeParamPackingConstOf]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)

/-- **Packing bound for a parameter-separated family of tubes, at a general ratio.**

`Kakeya.card_le_of_tubeParamDist_separated` is the special case `N = 1000`; the proof is identical
with `1000` replaced by `N`, and it is the only place where the ratio enters. -/
theorem card_le_of_tubeParamDist_separated_of_ratio
    {ι : Type*} {δ : ℝ≥0} (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (A : Finset ι) {sep R : ℝ} {N : ℕ} (hN : 1 ≤ N) (hsep : 0 < sep)
    (hRsep : R ≤ (N : ℝ) * sep)
    (hAsep : ∀ k ∈ A, ∀ k' ∈ A, k ≠ k' → sep < tubeParamDist (T k) (T k'))
    (k₀ : ι) (hA : ∀ k ∈ A, tubeParamDist (T k) (T k₀) ≤ R) :
    (A.card : ℝ) ≤ (tubeParamPackingConstOf N : ℝ) := by
  classical
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  by_cases hA0 : A.card = 0
  · rw [hA0]
    simpa only [Nat.cast_zero] using (NNReal.coe_nonneg (tubeParamPackingConstOf N))
  · have hAnon : ∃ k : ι, k ∈ A := by
      rcases A.eq_empty_or_nonempty with hAe | hAnon
      · exfalso
        rw [hAe] at hA0
        exact hA0 rfl
      · exact hAnon
    obtain ⟨ka, hka⟩ := hAnon
    have hRge : 0 ≤ R := le_trans (tubeParamDist_nonneg (T ka) (T k₀)) (hA ka hka)
    by_cases hRpos : 0 < R
    · -- MAIN case: positive radius.
      -- STEP 1: maximal sep/2-separated set of centres.
      obtain ⟨S, hSsub, hSsep, hSsat⟩ :=
        exists_max_card_separated A (fun k k' => sep / 2 < dist (T k).center (T k').center)
          (by intro i j h
              rwa [dist_comm])
      have hs_sat : ∀ k ∈ A, ∃ i ∈ S, i = k ∨ dist (T i).center (T k).center ≤ sep / 2 := by
        intro k hk
        rcases hSsat k hk with ⟨i, hi, h⟩
        refine ⟨i, hi, ?_⟩
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (not_lt.mp h)
      -- The assignment map (fibres A over S).
      let f : ι → ι := fun k =>
        if h : ∃ i ∈ S, (i = k ∨ dist (T i).center (T k).center ≤ sep / 2) then Classical.choose h
        else k
      have hf_mem : ∀ k ∈ A, f k ∈ S := by
        intro k hk
        dsimp [f]
        rw [dif_pos (hs_sat k hk)]
        exact (Classical.choose_spec (hs_sat k hk)).1
      have hf_prop : ∀ k ∈ A, (f k = k ∨ dist (T (f k)).center (T k).center ≤ sep / 2) := by
        intro k hk
        dsimp [f]
        rw [dif_pos (hs_sat k hk)]
        exact (Classical.choose_spec (hs_sat k hk)).2
      -- STEP 2: bound S by the centre packing.
      let V : Finset (EuclideanSpace ℝ (Fin 3)) := S.image fun k => (T k).center
      have hV_in : ∀ v ∈ V, ‖v - (T k₀).center‖ ≤ R := by
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨k, hkS, hkv⟩
        have hkA : k ∈ A := hSsub hkS
        rw [← hkv, ← dist_eq_norm]
        exact le_trans (dist_center_le_tubeParamDist (T k) (T k₀)) (hA k hkA)
      have hsep2 : 0 < sep / 2 := by positivity
      have hV_sep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → sep / 2 ≤ ‖x - y‖ := by
        intro x hx y hy hxy
        rcases Finset.mem_image.mp hx with ⟨i, hi, hxi⟩
        rcases Finset.mem_image.mp hy with ⟨j, hj, hyj⟩
        by_cases hij : i = j
        · subst hij
          exfalso
          exact hxy (by rw [← hxi, ← hyj])
        · have hsi := hSsep i hi j hj hij
          rw [← hxi, ← hyj, ← dist_eq_norm]
          exact le_of_lt hsi
      have hmap_inj : Set.InjOn (fun k : ι => (T k).center) (S : Set ι) := by
        intro i hi j hj hc
        by_contra hij
        have hsi := hSsep i hi j hj hij
        have hd0 : dist (T i).center (T j).center = 0 := by
          have hc' : (T i).center = (T j).center := by simpa using hc
          rw [← hc', dist_self]
        nlinarith
      have hVcard : V.card = S.card := by
        dsimp [V]
        exact Finset.card_image_of_injOn hmap_inj
      have hfin : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) = 3 :=
        finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
      let base : ℝ := (R + (sep / 2) / 2) / ((sep / 2) / 2)
      have hratio : base = (R + sep / 4) / (sep / 4) := by
        dsimp [base]
        ring
      have hS3 : (S.card : ℝ) ≤ ((R + sep / 4) / (sep / 4)) ^ 3 := by
        rw [← hVcard]
        calc
          (V.card : ℝ) ≤ base ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
            card_le_of_separated_in_ball (s := V) (c := (T k₀).center) (R := R) (r := sep / 2)
              (hr := hsep2) (hR := hRge) hV_in hV_sep
          _ = base ^ 3 := by rw [hfin]
          _ = ((R + sep / 4) / (sep / 4)) ^ 3 := by rw [hratio]
      have hSbound : (S.card : ℝ) ≤ (4 * (N : ℝ) + 1) ^ 3 := by
        have hbase0 : 0 ≤ (R + sep / 4) / (sep / 4) := by positivity
        have hbase : (R + sep / 4) / (sep / 4) ≤ (4 * (N : ℝ) + 1) := by
          have hspos : (0 : ℝ) < sep / 4 := by positivity
          rw [div_le_iff₀ hspos]
          nlinarith [hRsep, hsep, hN']
        exact hS3.trans (pow_le_pow_left₀ hbase0 hbase 3)
      -- STEP 3: bound each fibre by direction packing.
      let fibB : ℝ := 250 * ((N : ℝ) ^ 3) + 250
      let dproj : ι → ι → ℝ := fun a b => min ‖(T a).direction - (T b).direction‖
        ‖(T a).direction + (T b).direction‖
      have hFibReal : ∀ b ∈ S, ((A.filter fun k => f k = b).card : ℝ) ≤ fibB := by
        intro b hb
        let Fib : Finset ι := A.filter fun k => f k = b
        let D : Finset (EuclideanSpace ℝ (Fin 3)) := Fib.image fun k => (T k).direction
        have hFib_memA : ∀ k ∈ Fib, k ∈ A := by
          intro k hk
          exact (Finset.mem_filter.mp hk).1
        have hFib_center : ∀ k ∈ Fib, dist (T b).center (T k).center ≤ sep / 2 := by
          intro k hk
          have hkA : k ∈ A := hFib_memA k hk
          have hkeq : f k = b := (Finset.mem_filter.mp hk).2
          have hprop := hf_prop k hkA
          rw [hkeq] at hprop
          rcases hprop with hbk | hck
          · rw [← hbk]
            simpa using show (0 : ℝ) ≤ sep / 2 by positivity
          · exact hck
        have hFib_pair_c : ∀ k₁ ∈ Fib, ∀ k₂ ∈ Fib, k₁ ≠ k₂ →
            dist (T k₁).center (T k₂).center ≤ sep := by
          intro k₁ hk₁ k₂ hk₂ hk₁₂
          calc
            dist (T k₁).center (T k₂).center
                ≤ dist (T k₁).center (T b).center + dist (T b).center (T k₂).center :=
              dist_triangle _ _ _
            _ ≤ sep / 2 + sep / 2 := by
              exact add_le_add
                (by simpa [dist_comm] using hFib_center k₁ hk₁) (hFib_center k₂ hk₂)
            _ = sep := by ring
        have hFib_dirsep : ∀ k₁ ∈ Fib, ∀ k₂ ∈ Fib, k₁ ≠ k₂ → sep ≤ dproj k₁ k₂ := by
          intro k₁ hk₁ k₂ hk₂ hk₁₂
          have hsep_lt := hAsep k₁ (hFib_memA k₁ hk₁) k₂ (hFib_memA k₂ hk₂) hk₁₂
          have hmk : sep < max (dist (T k₁).center (T k₂).center) (dproj k₁ k₂) := by
            simpa [tubeParamDist, dproj] using hsep_lt
          have hc_le : dist (T k₁).center (T k₂).center ≤ sep := hFib_pair_c k₁ hk₁ k₂ hk₂ hk₁₂
          by_contra h
          have hmin_le : dproj k₁ k₂ ≤ sep := le_of_lt (lt_of_not_ge h)
          have hmax_le : max (dist (T k₁).center (T k₂).center) (dproj k₁ k₂) ≤ sep :=
            max_le hc_le hmin_le
          linarith
        have hdir_inj : Set.InjOn (fun k : ι => (T k).direction) (Fib : Set ι) := by
          intro k₁ hk₁ k₂ hk₂ hd
          by_contra hk₁₂
          have hsepdir := hFib_dirsep k₁ hk₁ k₂ hk₂ hk₁₂
          have hmm : dproj k₁ k₂ = 0 := by
            have hd' : (T k₁).direction = (T k₂).direction := by simpa using hd
            dsimp [dproj]
            rw [hd']
            simp
          have hgone : sep ≤ 0 := by simpa [hmm] using hsepdir
          nlinarith
        have hDcard_eq : D.card = Fib.card := by
          dsimp [D]
          exact Finset.card_image_of_injOn hdir_inj
        have hV_sepD : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → sep ≤ min ‖x - y‖ ‖x + y‖ := by
          intro x hx y hy hxy
          rcases Finset.mem_image.mp hx with ⟨k₁, hk₁F, hx1⟩
          rcases Finset.mem_image.mp hy with ⟨k₂, hk₂F, hy2⟩
          have hk₁₂ : k₁ ≠ k₂ := by
            intro hkeq
            subst hkeq
            exact hxy (by rw [← hx1, ← hy2])
          have hdsep := hFib_dirsep k₁ hk₁F k₂ hk₂F hk₁₂
          rw [← hx1, ← hy2]
          exact hdsep
        have hD_unit : ∀ x ∈ D, ‖x‖ = 1 := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨k, hkF, hxk⟩
          rw [← hxk]
          exact Tube.norm_direction (T k)
        have hD_cap : ∀ x ∈ D, min ‖x - (T k₀).direction‖ ‖x + (T k₀).direction‖ ≤ R := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨k, hkF, hxk⟩
          rw [← hxk]
          exact le_trans (projDist_le_tubeParamDist (T k) (T k₀)) (hA k (hFib_memA k hkF))
        have hproj := card_le_of_projective_separated_in_cap (V := D) (e := (T k₀).direction)
            (_he_unit := Tube.norm_direction (T k₀)) (_hV_unit := hD_unit)
            (R := R) (r := sep) (_hr_pos := hsep) (_hR_pos := hRpos)
            (_hV_sep := hV_sepD) (_hV_cap := hD_cap)
        have hDbound : (D.card : ℝ) ≤ (250 : ℝ) * (R / sep) ^ 3 + 250 := by
          have hc : projectiveCapPackingConstant (EuclideanSpace ℝ (Fin 3)) = 250 := by
            rw [projectiveCapPackingConstant, hfin]
            norm_num
          have hn : (R / sep) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = (R / sep) ^ 3 := by
            rw [hfin]
          calc
            (D.card : ℝ) ≤ projectiveCapPackingConstant (EuclideanSpace ℝ (Fin 3)) *
                (R / sep) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) +
                projectiveCapPackingConstant (EuclideanSpace ℝ (Fin 3)) := hproj
            _ = 250 * (R / sep) ^ 3 + 250 := by rw [hc, hn]
        have hFibcard : (Fib.card : ℝ) ≤ (250 : ℝ) * (R / sep) ^ 3 + 250 := by
          rw [← hDcard_eq]
          exact hDbound
        have hFratio : R / sep ≤ (N : ℝ) := by
          rw [div_le_iff₀ hsep]
          exact hRsep
        have hFratio0 : 0 ≤ R / sep := by positivity
        have hF324 : (250 : ℝ) * (R / sep) ^ 3 + 250 ≤ 250 * ((N : ℝ) ^ 3) + 250 := by
          have hFpow : (R / sep) ^ 3 ≤ ((N : ℝ) ^ 3) := pow_le_pow_left₀ hFratio0 hFratio 3
          nlinarith
        have hRbound1 : (Fib.card : ℝ) ≤ 250 * ((N : ℝ) ^ 3) + 250 :=
          hFibcard.trans hF324
        simpa [Fib] using hRbound1
      have hFibNat : ∀ b ∈ S, (A.filter fun k => f k = b).card ≤ (250 * N ^ 3 + 250 : ℕ) := by
        intro b hb
        have hc : ((250 * N ^ 3 + 250 : ℕ) : ℝ) = fibB := by
          dsimp [fibB]
          push_cast
          ring
        have href : ((A.filter fun k => f k = b).card : ℝ)
            ≤ (((250 * N ^ 3 + 250 : ℕ) : ℝ)) := by
          rw [hc]
          exact hFibReal b hb
        exact_mod_cast href
      have hfib := card_le_mul_of_fibered (A := A) (B := S) (f := f) hf_mem
        (m := 250 * N ^ 3 + 250) hFibNat
      -- STEP 4: combine.
      calc
        (A.card : ℝ) ≤ (S.card : ℝ) * ((250 * N ^ 3 + 250 : ℕ) : ℝ) := by exact_mod_cast hfib
        _ ≤ (4 * (N : ℝ) + 1) ^ 3 * ((250 * N ^ 3 + 250 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hSbound (by positivity)
        _ = (tubeParamPackingConstOf N : ℝ) := by
          rw [tubeParamPackingConstOf]
          push_cast
          ring
    · -- degenerate case R ≤ 0
      have hRle0 : R ≤ 0 := le_of_not_gt hRpos
      have hA1 : A.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        by_contra hab
        have hd : tubeParamDist (T a) (T b) ≤ 0 := by
          calc
            tubeParamDist (T a) (T b) ≤ tubeParamDist (T a) (T k₀) + tubeParamDist (T k₀) (T b) :=
              tubeParamDist_triangle (T a) (T k₀) (T b)
            _ ≤ R + R := by
              exact add_le_add (hA a ha) (by simpa [tubeParamDist_comm] using hA b hb)
            _ ≤ 0 := by
              nlinarith
        have hd0 : tubeParamDist (T a) (T b) = 0 :=
          le_antisymm hd (tubeParamDist_nonneg (T a) (T b))
        have : sep < tubeParamDist (T a) (T b) := hAsep a ha b hb hab
        nlinarith
      calc
        (A.card : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hA1
        _ ≤ (tubeParamPackingConstOf N : ℝ) := by
          exact_mod_cast NNReal.coe_le_coe.mpr (one_le_tubeParamPackingConstOf N)

/-- **The leafwise cover of a large test tube by radius-`8 ρ` test tubes.**

Every leaf of `q` contained in the test tube `V` of radius `Ctest * ρ` is contained in one of at
most `tubeParamPackingConstOf N` tubes of radius `8 ρ`, each of which is an inflation of a leaf.
The selection is a maximal `4 ρ`-separated subfamily in `Kakeya.tubeParamDist`. -/
theorem exists_leafwise_cover_of_test_tube
    {ι : Type*} {δ ρ Ctest : ℝ≥0} (hδ0 : 0 < δ) (hδρ : δ ≤ ρ)
    {N : ℕ} (hN1 : 1 ≤ N) (hN3 : 3 * (Ctest : ℝ) ≤ (N : ℝ)) (hN2 : 2 * (Ctest : ℝ) ≤ (N : ℝ))
    (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (V : Tube (Ctest * ρ) (EuclideanSpace ℝ (Fin 3))) :
    ∃ S : Finset ι, S ⊆ q ∧ ((S.card : ℝ≥0)) ≤ tubeParamPackingConstOf N ∧
      ∀ i ∈ q, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody →
        ∃ m ∈ S, (T i).toConvexSpaceBody ≤ ((T m).rescale (8 * ρ)).toConvexSpaceBody := by
  classical
  let sep : ℝ := 4 * (ρ : ℝ)
  have hρ0 : 0 < (ρ : ℝ) := by
    have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    exact lt_of_lt_of_le hδ0' (by exact_mod_cast hδρ)
  have hsep0 : 0 < sep := by
    dsimp [sep]
    positivity
  have hsep00 : 0 ≤ sep := le_of_lt hsep0
  have hδρ' : (δ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hδρ
  have hcoef8 : ((8 * ρ : ℝ≥0) : ℝ) = 8 * (ρ : ℝ) := by
    rw [NNReal.coe_mul]
    norm_num
  have hbudget : (δ : ℝ) + 3 * sep / 2 ≤ ((8 * ρ : ℝ≥0) : ℝ) := by
    rw [hcoef8]
    dsimp [sep]
    nlinarith [hδρ', NNReal.coe_nonneg ρ]
  let A : Finset ι := q.filter (fun t => (T t).toConvexSpaceBody ≤ V.toConvexSpaceBody)
  obtain ⟨S, hSsubA, hSsep, hSsat⟩ :=
    exists_max_card_separated A (fun i j => sep < tubeParamDist (T i) (T j))
      (by intro i j h; simpa [tubeParamDist_comm] using h)
  have hSsubq : S ⊆ q := by
    exact subset_trans hSsubA (by dsimp [A]; exact Finset.filter_subset _ _)
  have hcardReal : (S.card : ℝ) ≤ (tubeParamPackingConstOf N : ℝ) := by
    rcases S.eq_empty_or_nonempty with hSe | ⟨k0, hk0S⟩
    · rw [hSe]
      simp
    · by_cases hreg : ((Ctest * ρ : ℝ≥0) : ℝ) ≤ 1 / 4
      · -- Regime 1: rigidity through the common containing tube V.
        have h12 : 12 * (Ctest : ℝ) ≤ 4 * (N : ℝ) := by
          nlinarith [hN3]
        have hmul := mul_le_mul_of_nonneg_right h12 (NNReal.coe_nonneg ρ)
        have hRsep0 : 12 * ((Ctest : ℝ) * (ρ : ℝ)) ≤ (N : ℝ) * (4 * (ρ : ℝ)) := by
          calc
            12 * ((Ctest : ℝ) * (ρ : ℝ)) = (12 * (Ctest : ℝ)) * (ρ : ℝ) := by ring
            _ ≤ (4 * (N : ℝ)) * (ρ : ℝ) := hmul
            _ = (N : ℝ) * (4 * (ρ : ℝ)) := by ring
        let R : ℝ := 12 * ((Ctest * ρ : ℝ≥0) : ℝ)
        have hRsep : R ≤ (N : ℝ) * sep := by
          dsimp [R, sep]
          exact hRsep0
        have hA_R : ∀ t ∈ S, tubeParamDist (T t) (T k0) ≤ R := by
          intro t ht
          have htA : t ∈ A := hSsubA ht
          have hk0A : k0 ∈ A := hSsubA hk0S
          have htV : (T t).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
            have htF : t ∈ q.filter (fun s => (T s).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
              exact htA
            exact (Finset.mem_filter.mp htF).2
          have hk0V : (T k0).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
            have hk0F : k0 ∈ q.filter (fun s => (T s).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
              exact hk0A
            exact (Finset.mem_filter.mp hk0F).2
          have hcark : ((T t).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              (V.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
            change (((T t).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              (V.toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))))
            exact (SetLike.coe_subset_coe (S := (T t).toConvexSpaceBody)
              (T := V.toConvexSpaceBody)).mpr htV
          have hcark0 : ((T k0).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              (V.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
            change (((T k0).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              (V.toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))))
            exact (SetLike.coe_subset_coe (S := (T k0).toConvexSpaceBody)
              (T := V.toConvexSpaceBody)).mpr hk0V
          have hd := tubeParamDist_le_of_subset_common (T t) (T k0) V hcark hcark0 hreg
          simpa [R] using hd
        exact card_le_of_tubeParamDist_separated_of_ratio (T := T) (A := S) (sep := sep)
          (R := R) hN1 hsep0 hRsep hSsep k0 hA_R
      · -- Regime 2: `1/4 < Ctest * ρ`; the whole family lies in the unit ball.
        have hgt : (1 / 4 : ℝ) < ((Ctest * ρ : ℝ≥0) : ℝ) := lt_of_not_ge hreg
        have hgt' : (1 / 4 : ℝ) < (Ctest : ℝ) * (ρ : ℝ) := by
          simpa using hgt
        have h2lt : (2 : ℝ) < 8 * (Ctest : ℝ) * (ρ : ℝ) := by
          nlinarith [hgt']
        have hN2mul : 8 * (Ctest : ℝ) * (ρ : ℝ) ≤ 4 * (N : ℝ) * (ρ : ℝ) := by
          have hm := mul_le_mul_of_nonneg_right hN2 (by positivity : 0 ≤ 4 * (ρ : ℝ))
          calc
            8 * (Ctest : ℝ) * (ρ : ℝ) = (2 * (Ctest : ℝ)) * (4 * (ρ : ℝ)) := by ring
            _ ≤ (N : ℝ) * (4 * (ρ : ℝ)) := hm
            _ = 4 * (N : ℝ) * (ρ : ℝ) := by ring
        have h2le : (2 : ℝ) ≤ 4 * (N : ℝ) * (ρ : ℝ) :=
          le_trans (le_of_lt h2lt) hN2mul
        let R : ℝ := 2
        have hRsep : R ≤ (N : ℝ) * sep := by
          dsimp [R, sep]
          nlinarith [h2le]
        have hA_R : ∀ t ∈ S, tubeParamDist (T t) (T k0) ≤ R := by
          intro t ht
          have hballt : (T t).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
            hball t (hSsubq ht)
          have hballk0 : (T k0).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
            hball k0 (hSsubq hk0S)
          have hd := tubeParamDist_le_two_of_ball (T t) (T k0) hballt hballk0
          simpa [R] using hd
        exact card_le_of_tubeParamDist_separated_of_ratio (T := T) (A := S) (sep := sep)
          (R := R) hN1 hsep0 hRsep hSsep k0 hA_R
  refine ⟨S, hSsubq, ?_, ?_⟩
  · exact NNReal.coe_le_coe.mp hcardReal
  · intro i hiq hTiV
    have hiA : i ∈ A := by
      dsimp [A]
      exact Finset.mem_filter.mpr ⟨hiq, hTiV⟩
    rcases hSsat i hiA with ⟨m, hmS, hmi⟩
    refine ⟨m, hmS, ?_⟩
    have hclose : tubeParamDist (T i) (T m) ≤ sep := by
      rcases hmi with rfl | hlt
      · rw [tubeParamDist_self]
        exact hsep00
      · rw [tubeParamDist_comm]
        exact not_lt.mp hlt
    have hinc : ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((T m).rescale (8 * ρ)).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      carrier_subset_rescale_of_tubeParamDist_le (T₁ := T i) (T₂ := T m) (c := sep) (s := 8 * ρ)
        hsep00 hclose hbudget
    exact (SetLike.coe_subset_coe (A := ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
      (S := (T i).toConvexSpaceBody) (T := ((T m).rescale (8 * ρ)).toConvexSpaceBody)).mp hinc

open Classical in
/-- **Bounded overlap at an enlarged test radius, for a parent system at the original scale `ρ`.**

The parent scale, `PS.parentTube`, `PS.assign` and `PS.parents` are untouched: only the *test* tube
is enlarged.  Every leaf inside the large test tube `V` lies in one of at most
`tubeParamPackingConstOf N` radius-`8 ρ` tubes
(`Kakeya.exists_leafwise_cover_of_test_tube`), each of which the structure's own
`boundedOverlapThroughLeaves` field controls by `Cu`; a plain union bound over the cover finishes.
No parent label is identified across cover tubes. -/
theorem ExternalParentSystem.boundedOverlapThroughLeaves_large
    {ι : Type*} {q : Finset ι} {δ ρ Cu Ctest : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu)
    (hδ0 : 0 < δ) (hδρ : δ ≤ ρ)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {N : ℕ} (hN1 : 1 ≤ N) (hN3 : 3 * (Ctest : ℝ) ≤ (N : ℝ)) (hN2 : 2 * (Ctest : ℝ) ≤ (N : ℝ))
    (V : Tube (Ctest * ρ) (EuclideanSpace ℝ (Fin 3))) :
    (((PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody).card : ℝ≥0))
      ≤ tubeParamPackingConstOf N * Cu := by
  classical
  obtain ⟨S, hSq, hScard, hcov⟩ :=
    exists_leafwise_cover_of_test_tube hδ0 hδρ hN1 hN3 hN2 q T hball V
  let P : Finset PS.Parent := PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
      (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody
  let Pm : ι → Finset PS.Parent := fun m => PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
      (T i).toConvexSpaceBody ≤ ((T m).rescale (8 * ρ)).toConvexSpaceBody
  have hPom : ∀ m ∈ S, ((Pm m).card : ℝ≥0) ≤ Cu := by
    intro m hm
    dsimp [Pm]
    exact PS.boundedOverlapThroughLeaves ((T m).rescale (8 * ρ))
  have hP_sub : P ⊆ S.biUnion (fun m => Pm m) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkpar, hkprop⟩
    rcases hkprop with ⟨i, hiq, hassign, hTle⟩
    have hcov' : ∃ m ∈ S, (T i).toConvexSpaceBody ≤ ((T m).rescale (8 * ρ)).toConvexSpaceBody :=
      hcov i hiq hTle
    obtain ⟨m, hmS, hmi⟩ := hcov'
    rw [Finset.mem_biUnion]
    exact ⟨m, hmS, by
      dsimp [Pm]
      exact Finset.mem_filter.mpr ⟨hkpar, ⟨i, hiq, hassign, hmi⟩⟩⟩
  have hcard1 : ((P.card : ℝ≥0)) ≤ ((S.biUnion fun m => Pm m).card : ℝ≥0) := by
    exact_mod_cast (Finset.card_le_card hP_sub)
  have hcard2 : ((S.biUnion fun m => Pm m).card : ℝ≥0) ≤ (∑ m ∈ S, (Pm m).card : ℝ≥0) := by
    exact_mod_cast (Finset.card_biUnion_le)
  have hsum : (∑ m ∈ S, (Pm m).card : ℝ≥0) ≤ (∑ m ∈ S, Cu) := by
    exact Finset.sum_le_sum (fun m hm => hPom m hm)
  have hsum_const : (∑ m ∈ S, Cu) = (S.card : ℝ≥0) * Cu := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hfinal : (S.card : ℝ≥0) * Cu ≤ tubeParamPackingConstOf N * Cu :=
    mul_le_mul_of_nonneg_right hScard (by positivity)
  change ((P.card : ℝ≥0)) ≤ tubeParamPackingConstOf N * Cu
  exact (hcard1.trans hcard2).trans (hsum.trans (by rw [hsum_const]; exact hfinal))

/-- **The leafwise cover of the whole unit ball by radius-`8 ρ` test tubes.**

The companion of `Kakeya.exists_leafwise_cover_of_test_tube` with no ambient test tube: *every* leaf
of `q` — not only those inside a prescribed large tube — lies in one of at most
`tubeParamPackingConstOf N` tubes of radius `8 ρ`, each an inflation of a leaf.  The selection is
again a maximal `4 ρ`-separated subfamily in `Kakeya.tubeParamDist`; what replaces the containment
in a test tube is the crude diameter bound `tubeParamDist ≤ 2` valid for any two tubes in `B₁`
(`Kakeya.tubeParamDist_le_two_of_ball`).  The hypothesis `2 ≤ 4 N ρ` makes that bound usable, so
`N` is forced to grow like `ρ⁻¹`: the statement is useful exactly when `ρ` is bounded below by an
absolute constant, which in GWZ Proposition 6.6(A) is the large-`b` regime `b₀ < b ≤ 2 ρ`. -/
theorem exists_leafwise_cover_of_ball
    {ι : Type*} {δ ρ : ℝ≥0} (hδ0 : 0 < δ) (hδρ : δ ≤ ρ)
    {N : ℕ} (hN1 : 1 ≤ N) (hNρ : (2 : ℝ) ≤ 4 * (N : ℝ) * (ρ : ℝ))
    (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ S : Finset ι, S ⊆ q ∧ ((S.card : ℝ≥0)) ≤ tubeParamPackingConstOf N ∧
      ∀ i ∈ q, ∃ m ∈ S, (T i).toConvexSpaceBody ≤ ((T m).rescale (8 * ρ)).toConvexSpaceBody := by
  classical
  let sep : ℝ := 4 * (ρ : ℝ)
  have hρ0 : 0 < (ρ : ℝ) := by
    have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    exact lt_of_lt_of_le hδ0' (by exact_mod_cast hδρ)
  have hsep0 : 0 < sep := by
    dsimp [sep]
    positivity
  have hsep00 : 0 ≤ sep := le_of_lt hsep0
  have hδρ' : (δ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hδρ
  have hcoef8 : ((8 * ρ : ℝ≥0) : ℝ) = 8 * (ρ : ℝ) := by
    rw [NNReal.coe_mul]
    norm_num
  have hbudget : (δ : ℝ) + 3 * sep / 2 ≤ ((8 * ρ : ℝ≥0) : ℝ) := by
    rw [hcoef8]
    dsimp [sep]
    nlinarith [hδρ', NNReal.coe_nonneg ρ]
  obtain ⟨S, hSsubq, hSsep, hSsat⟩ :=
    exists_max_card_separated q (fun i j => sep < tubeParamDist (T i) (T j))
      (by intro i j h; simpa [tubeParamDist_comm] using h)
  have hcardReal : (S.card : ℝ) ≤ (tubeParamPackingConstOf N : ℝ) := by
    rcases S.eq_empty_or_nonempty with hSe | ⟨k0, hk0S⟩
    · rw [hSe]
      simp
    · let R : ℝ := 2
      have hRsep : R ≤ (N : ℝ) * sep := by
        dsimp [R, sep]
        nlinarith [hNρ]
      have hA_R : ∀ t ∈ S, tubeParamDist (T t) (T k0) ≤ R := by
        intro t ht
        have hballt : (T t).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
          hball t (hSsubq ht)
        have hballk0 : (T k0).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
          hball k0 (hSsubq hk0S)
        have hd := tubeParamDist_le_two_of_ball (T t) (T k0) hballt hballk0
        simpa [R] using hd
      exact card_le_of_tubeParamDist_separated_of_ratio (T := T) (A := S) (sep := sep)
        (R := R) hN1 hsep0 hRsep hSsep k0 hA_R
  refine ⟨S, hSsubq, ?_, ?_⟩
  · exact NNReal.coe_le_coe.mp hcardReal
  · intro i hiq
    rcases hSsat i hiq with ⟨m, hmS, hmi⟩
    refine ⟨m, hmS, ?_⟩
    have hclose : tubeParamDist (T i) (T m) ≤ sep := by
      rcases hmi with rfl | hlt
      · rw [tubeParamDist_self]
        exact hsep00
      · rw [tubeParamDist_comm]
        exact not_lt.mp hlt
    have hinc : ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((T m).rescale (8 * ρ)).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      carrier_subset_rescale_of_tubeParamDist_le (T₁ := T i) (T₂ := T m) (c := sep) (s := 8 * ρ)
        hsep00 hclose hbudget
    exact (SetLike.coe_subset_coe (A := ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
      (S := (T i).toConvexSpaceBody) (T := ((T m).rescale (8 * ρ)).toConvexSpaceBody)).mp hinc

open Classical in
/-- **The total number of occupied parents, for a parent system at a scale bounded below.**

`ExternalParentSystem.boundedOverlapThroughLeaves` counts the parents owning a leaf inside *one*
radius-`8 ρ` test tube.  Covering the unit ball leafwise by at most `tubeParamPackingConstOf N` such
tubes (`Kakeya.exists_leafwise_cover_of_ball`) and union-bounding over the cover controls the number
of parents owning a leaf *at all*.  The cover is finite only because `ρ` is bounded below — the
hypothesis `2 ≤ 4 N ρ` — which is exactly what the large-`b` regime of GWZ Proposition 6.6(A)
provides through `b₀ < b ≤ 2 ρ`; no parent labels are identified across cover tubes. -/
theorem ExternalParentSystem.card_occupiedParents_le
    {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu)
    (hδ0 : 0 < δ) (hδρ : δ ≤ ρ)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {N : ℕ} (hN1 : 1 ≤ N) (hNρ : (2 : ℝ) ≤ 4 * (N : ℝ) * (ρ : ℝ)) :
    (((PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k).card : ℝ≥0))
      ≤ tubeParamPackingConstOf N * Cu := by
  classical
  obtain ⟨S, hSq, hScard, hcov⟩ :=
    exists_leafwise_cover_of_ball hδ0 hδρ hN1 hNρ q T hball
  let P : Finset PS.Parent := PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k
  let Pm : ι → Finset PS.Parent := fun m => PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
      (T i).toConvexSpaceBody ≤ ((T m).rescale (8 * ρ)).toConvexSpaceBody
  have hPom : ∀ m ∈ S, ((Pm m).card : ℝ≥0) ≤ Cu := by
    intro m hm
    dsimp [Pm]
    exact PS.boundedOverlapThroughLeaves ((T m).rescale (8 * ρ))
  have hP_sub : P ⊆ S.biUnion (fun m => Pm m) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkpar, hkprop⟩
    rcases hkprop with ⟨i, hiq, hassign⟩
    have hcov' : ∃ m ∈ S, (T i).toConvexSpaceBody ≤ ((T m).rescale (8 * ρ)).toConvexSpaceBody :=
      hcov i hiq
    obtain ⟨m, hmS, hmi⟩ := hcov'
    rw [Finset.mem_biUnion]
    exact ⟨m, hmS, by
      dsimp [Pm]
      exact Finset.mem_filter.mpr ⟨hkpar, ⟨i, hiq, hassign, hmi⟩⟩⟩
  have hcard1 : ((P.card : ℝ≥0)) ≤ ((S.biUnion fun m => Pm m).card : ℝ≥0) := by
    exact_mod_cast (Finset.card_le_card hP_sub)
  have hcard2 : ((S.biUnion fun m => Pm m).card : ℝ≥0) ≤ (∑ m ∈ S, (Pm m).card : ℝ≥0) := by
    exact_mod_cast (Finset.card_biUnion_le)
  have hsum : (∑ m ∈ S, (Pm m).card : ℝ≥0) ≤ (∑ m ∈ S, Cu) := by
    exact Finset.sum_le_sum (fun m hm => hPom m hm)
  have hsum_const : (∑ m ∈ S, Cu) = (S.card : ℝ≥0) * Cu := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hfinal : (S.card : ℝ≥0) * Cu ≤ tubeParamPackingConstOf N * Cu :=
    mul_le_mul_of_nonneg_right hScard (by positivity)
  change ((P.card : ℝ≥0)) ≤ tubeParamPackingConstOf N * Cu
  exact (hcard1.trans hcard2).trans (hsum.trans (by rw [hsum_const]; exact hfinal))

/-- The absolute overlap constant of the constructed parent system. -/
noncomputable def parentOverlapConst : ℝ≥0 := 10 ^ 30

/-- **The separated subfamily and the assignment.**

A maximum-cardinality `ρ/8`-separated subfamily of the leaves, together with a map sending each leaf
to a selected leaf within parameter distance `ρ/8`.  Saturation of a maximum-cardinality separated
family (`Kakeya.exists_max_card_separated`) is what makes the assignment total on `q`. -/
theorem exists_separatedAssignment
    {ι : Type*} {δ ρ : ℝ≥0} (hρ0 : 0 < ρ) (q : Finset ι) (hq : q.Nonempty)
    (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))) :
    ∃ (S : Finset ι) (assign : ι → ι),
      S ⊆ q ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → (ρ : ℝ) / 8 < tubeParamDist (T i) (T j)) ∧
      (∀ i ∈ q, assign i ∈ S) ∧
      (∀ i ∈ q, tubeParamDist (T (assign i)) (T i) ≤ (ρ : ℝ) / 8) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hq
  have hρ0' : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hsep0 : (0 : ℝ) < (ρ : ℝ) / 8 := by linarith
  let Rel : ι → ι → Prop := fun i j => (ρ : ℝ) / 8 < tubeParamDist (T i) (T j)
  have hsymm : ∀ i j, Rel i j → Rel j i := by
    intro i j h
    simpa [Rel, tubeParamDist_comm] using h
  obtain ⟨S, hSq, hSsep, hSsat⟩ := exists_max_card_separated q Rel hsymm
  have hchoose : ∀ i ∈ q, ∃ k, k ∈ S ∧ tubeParamDist (T k) (T i) ≤ (ρ : ℝ) / 8 := by
    intro i hi
    obtain ⟨k, hkS, hk⟩ := hSsat i hi
    refine ⟨k, hkS, ?_⟩
    rcases hk with rfl | hk
    · rw [tubeParamDist_self]
      exact hsep0.le
    · exact not_lt.mp hk
  let assign : ι → ι := fun i =>
    if h : ∃ k, k ∈ S ∧ tubeParamDist (T k) (T i) ≤ (ρ : ℝ) / 8 then
      h.choose
    else
      i₀
  have hassign : ∀ i ∈ q, assign i ∈ S ∧
      tubeParamDist (T (assign i)) (T i) ≤ (ρ : ℝ) / 8 := by
    intro i hi
    dsimp [assign]
    rw [dif_pos (hchoose i hi)]
    exact (hchoose i hi).choose_spec
  exact ⟨S, assign, hSq, hSsep, fun i hi => (hassign i hi).1, fun i hi => (hassign i hi).2⟩

open Classical in
/-- **The overlap count for the separated family.**

Given the separated subfamily and assignment of `Kakeya.exists_separatedAssignment`, the number of
selected leaves owning a leaf inside a test tube of radius `8 * ρ` is absolutely bounded.  Two
regimes, both feeding `Kakeya.card_le_of_tubeParamDist_separated` with `sep = ρ/8`:

* `32 * ρ ≤ 1`: longitudinal rigidity bounds the mutual parameter distance of the contributing
  parents by `97 * ρ`;
* `1 < 32 * ρ`: rigidity is unavailable but unnecessary, since the whole family lies in `B₁` and `2`
  works as the diameter bound. -/
theorem card_contributingParents_le
    {ι : Type*} {δ ρ : ℝ≥0} (hδ0 : 0 < δ) (hδρ : 4 * δ ≤ ρ)
    (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (S : Finset ι) (assign : ι → ι) (hSq : S ⊆ q)
    (hSsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (ρ : ℝ) / 8 < tubeParamDist (T i) (T j))
    (hclose : ∀ i ∈ q, tubeParamDist (T (assign i)) (T i) ≤ (ρ : ℝ) / 8)
    (V : Tube (8 * ρ) (EuclideanSpace ℝ (Fin 3)))
    (A : Finset ι) (hAS : A ⊆ S)
    (hAwit : ∀ k ∈ A, ∃ i ∈ q, assign i = k ∧
      (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    (A.card : ℝ≥0) ≤ parentOverlapConst := by
  classical
  have hρ0 : 0 < ρ := by
    have h4δ : 0 < 4 * δ := by positivity
    exact lt_of_lt_of_le h4δ hδρ
  have hsep0 : (0 : ℝ) < (ρ : ℝ) / 8 := by positivity
  have hAsep : ∀ k ∈ A, ∀ k' ∈ A, k ≠ k' → (ρ : ℝ) / 8 < tubeParamDist (T k) (T k') := by
    intro k hk k' hk' hne
    exact hSsep k (hAS hk) k' (hAS hk') hne
  have hcount : (A.card : ℝ) ≤ (10 : ℝ) ^ 30 := by
    rcases A.eq_empty_or_nonempty with hAempty | ⟨k₁, hk₁⟩
    · rw [hAempty]
      norm_num
    · have hk₁S : k₁ ∈ S := hAS hk₁
      rcases hAwit k₁ hk₁ with ⟨i₁, hi₁q, hi₁assign, hi₁V⟩
      by_cases h32 : 32 * (ρ : ℝ) ≤ 1
      · -- Regime 1: `32 * ρ ≤ 1`, longitudinal rigidity gives a `97 * ρ` diameter.
        have hc8 : ((8 * ρ : ℝ≥0) : ℝ) = 8 * (ρ : ℝ) := by norm_cast
        have hVr : ((8 * ρ : ℝ≥0) : ℝ) ≤ 1 / 4 := by
          rw [hc8]
          nlinarith
        have hRsep : (97 * (ρ : ℝ)) ≤ 1000 * ((ρ : ℝ) / 8) := by
          nlinarith [NNReal.coe_nonneg ρ]
        have hA_R : ∀ k ∈ A, tubeParamDist (T k) (T k₁) ≤ 97 * (ρ : ℝ) := by
          intro k hk
          have hkS : k ∈ S := hAS hk
          rcases hAwit k hk with ⟨i, hiq, hassign, hiV⟩
          have hki : tubeParamDist (T k) (T i) ≤ (ρ : ℝ) / 8 := by
            simpa [hassign] using hclose i hiq
          have hcari : ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              (V.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
            change (((T i).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              (V.toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))))
            exact (SetLike.coe_subset_coe (A := ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
              (S := (T i).toConvexSpaceBody) (T := V.toConvexSpaceBody)).mpr hiV
          have hcar₁ : ((T i₁).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              (V.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
            change (((T i₁).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              (V.toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))))
            exact (SetLike.coe_subset_coe (A := ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
              (S := (T i₁).toConvexSpaceBody) (T := V.toConvexSpaceBody)).mpr hi₁V
          have hii₁ : tubeParamDist (T i) (T i₁) ≤ 12 * ((8 * ρ : ℝ≥0) : ℝ) :=
            tubeParamDist_le_of_subset_common (T i) (T i₁) V hcari hcar₁ hVr
          rw [hc8] at hii₁
          have hk₁i₁ : tubeParamDist (T k₁) (T i₁) ≤ (ρ : ℝ) / 8 := by
            simpa [hi₁assign] using hclose i₁ hi₁q
          have hik₁ : tubeParamDist (T i₁) (T k₁) ≤ (ρ : ℝ) / 8 := by
            simpa [tubeParamDist_comm] using hk₁i₁
          have ht₁ : tubeParamDist (T k) (T k₁) ≤
              tubeParamDist (T k) (T i) + tubeParamDist (T i) (T k₁) :=
            tubeParamDist_triangle (T k) (T i) (T k₁)
          have ht₂ : tubeParamDist (T i) (T k₁) ≤
              tubeParamDist (T i) (T i₁) + tubeParamDist (T i₁) (T k₁) :=
            tubeParamDist_triangle (T i) (T i₁) (T k₁)
          nlinarith [ht₁, ht₂, hki, hik₁, hii₁, NNReal.coe_nonneg ρ]
        have hpack := card_le_of_tubeParamDist_separated T A hsep0 hRsep hAsep k₁ hA_R
        simpa [tubeParamPackingConst] using hpack
      · -- Regime 2: `1 < 32 * ρ`; the whole family lies in `B₁`, so `R = 2` works.
        have hgt : 1 < 32 * (ρ : ℝ) := lt_of_not_ge h32
        have hRsep : (2 : ℝ) ≤ 1000 * ((ρ : ℝ) / 8) := by nlinarith
        have hballA : ∀ k ∈ A, (T k).carrier ⊆
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
          intro k hk
          exact hball k (hSq (hAS hk))
        have hA_R : ∀ k ∈ A, tubeParamDist (T k) (T k₁) ≤ 2 := by
          intro k hk
          exact tubeParamDist_le_two_of_ball (T k) (T k₁) (hballA k hk) (hballA k₁ hk₁)
        have hpack := card_le_of_tubeParamDist_separated (T := T) (A := A) (R := 2)
          hsep0 hRsep hAsep k₁ hA_R
        simpa [tubeParamPackingConst] using hpack
  have hcc : (A.card : ℝ) ≤ (parentOverlapConst : ℝ) := by
    simpa [parentOverlapConst] using hcount
  exact NNReal.coe_le_coe.mp hcc

/-- **Arbitrary-scale external parent system, away from the leaf scale.**

For every `ρ` with `4 * δ ≤ ρ ≤ 1` a coarse parent system exists with an *absolute* overlap
constant.  This is the corrected replacement for the sorried `Kakeya.Tube.IsUniform.spread`: it
needs no uniformity input, and the constant is independent of `δ`, of `ρ` and of the family.

The hypothesis `4 * δ ≤ ρ` is genuinely needed and is not an artefact.  At `ρ = δ` a parent tube of
radius `ρ` contains a leaf only if it nearly coincides with it (longitudinal rigidity), so parents
are forced to be the leaves themselves and bounded overlap becomes a statement about how many leaves
fit in a `8δ`-tube — which is false without a leaf-packing hypothesis (take many equal leaves).  The
regime `δ ≤ ρ < 4 * δ` therefore requires fine-scale essential distinctness and is treated
separately.

**Universe note.**  The parents are indexed by `Fin S.card` rather than by the selected leaves
themselves.  The `Parent` field of `Kakeya.ExternalParentSystem` lives in `Type`, whose universe is
fixed by the caller, so indexing parents by a subtype of `ι` would force `ι : Type`; going through
`Finset.equivFin` keeps the construction available for `ι : Type*`, which is what Proposition 6.6(A)
needs. -/
theorem exists_externalParentSystem_of_four_mul_le
    {ι : Type*} {δ ρ : ℝ≥0} (hδ0 : 0 < δ) (hδρ : 4 * δ ≤ ρ)
    (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (ExternalParentSystem q T ρ parentOverlapConst) := by
  classical
  rcases q.eq_empty_or_nonempty with hempty | hq
  · subst hempty
    obtain ⟨a0, ha0⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 3))
    let e : EuclideanSpace ℝ (Fin 3) := (‖a0‖⁻¹ : ℝ) • a0
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg a0))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha0)
    let x0 : EuclideanSpace ℝ (Fin 3) := -((1 / 2 : ℝ) • e)
    let y0 : EuclideanSpace ℝ (Fin 3) := (1 / 2 : ℝ) • e
    have hd0 : dist x0 y0 = 1 := by
      rw [dist_eq_norm]
      calc
        ‖x0 - y0‖ = ‖(-1 : ℝ) • e‖ := by
          congr 1
          dsimp [x0, y0]
          module
        _ = 1 := by simp [he]
    have hmem (i : ι) : i ∈ (∅ : Finset ι) → False := by simp
    let hEx : ExternalParentSystem ∅ T ρ parentOverlapConst :=
      { Parent := Unit
        parents := (∅ : Finset Unit)
        parentTube := fun _ => Tube.mk' ρ (x := x0) (y := y0) hd0
        assign := fun _ => ()
        assign_mem := by intro i hi; exact False.elim (hmem i hi)
        leaf_le_parent := by intro i hi; exact False.elim (hmem i hi)
        boundedOverlapThroughLeaves := by
          intro V
          simp }
    exact ⟨hEx⟩
  · have hρ0 : 0 < ρ := by
      have h4δ : (0 : ℝ≥0) < 4 * δ := by positivity
      exact lt_of_lt_of_le h4δ hδρ
    have hδρ' : 4 * (δ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hδρ
    have hsep : 0 < (ρ : ℝ) / 8 := by positivity
    have hsep0 : 0 ≤ (ρ : ℝ) / 8 := le_of_lt hsep
    obtain ⟨S, σ, hS, hSep, hMem, hClose⟩ :=
      exists_separatedAssignment (hρ0 := hρ0) (q := q) (hq := hq) (T := T)
    obtain ⟨i0, hi0⟩ := hq
    have hbudget : (δ : ℝ) + 3 * ((ρ : ℝ) / 8) / 2 ≤ (ρ : ℝ) := by
      nlinarith [hδρ', NNReal.coe_nonneg ρ]
    let em : {x : ι // x ∈ S} ≃ Fin (S.card) := Finset.equivFin S
    let rep : Fin (S.card) → ι := fun k => (em.symm k).1
    let assignP : ι → Fin (S.card) := fun k =>
      if hk : k ∈ q then em ⟨σ k, hMem k hk⟩ else em ⟨σ i0, hMem i0 hi0⟩
    have hcar (i : ι) (hi : i ∈ q) :
        (T i).carrier ⊆ (((T (σ i)).rescale ρ).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
      have hclone : tubeParamDist (T i) (T (σ i)) ≤ (ρ : ℝ) / 8 := by
        rw [tubeParamDist_comm]
        exact hClose i hi
      exact carrier_subset_rescale_of_tubeParamDist_le (T i) (T (σ i)) hsep0 hclone hbudget
    have hb (i : ι) (hi : i ∈ q) :
        (T i).toConvexSpaceBody ≤ ((T (σ i)).rescale ρ).toConvexSpaceBody := by
      exact (SetLike.coe_subset_coe (A := ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
        (S := (T i).toConvexSpaceBody)
        (T := ((T (σ i)).rescale ρ).toConvexSpaceBody)).mp (hcar i hi)
    have hrep (i : ι) (hi : i ∈ q) : rep (assignP i) = σ i := by
      dsimp [rep, assignP]
      rw [dif_pos hi]
      exact congrArg Subtype.val (em.symm_apply_apply ⟨σ i, hMem i hi⟩)
    have hleaf (i : ι) (hi : i ∈ q) :
        (T i).toConvexSpaceBody ≤ ((T (rep (assignP i))).rescale ρ).toConvexSpaceBody := by
      rw [hrep i hi]
      exact hb i hi
    let Bparent : Finset (Fin (S.card)) := Finset.univ
    let Bassign : ι → Fin (S.card) := assignP
    let Btub : Fin (S.card) → Tube ρ (EuclideanSpace ℝ (Fin 3)) :=
      fun k : Fin (S.card) => (T (rep k)).rescale ρ
    have hassign_mem : ∀ i ∈ q, Bassign i ∈ Bparent :=
      fun i hi => Finset.mem_univ (Bassign i)
    have hleaf2 : ∀ i ∈ q,
        (T i).toConvexSpaceBody ≤ (Btub (Bassign i)).toConvexSpaceBody := by
      intro i hi
      dsimp [Bassign, Btub]
      exact hleaf i hi
    have hbounded2 :
        ∀ (V : Tube (8 * ρ) (EuclideanSpace ℝ (Fin 3))) (B : Finset (Fin (S.card))),
          (∀ k ∈ B, ∃ i ∈ q, Bassign i = k ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) →
          ((B.card : ℝ≥0)) ≤ parentOverlapConst := by
      intro V B hBwit
      let A0 : Finset ι := S.filter (fun k : ι => ∃ i ∈ q, σ i = k ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
      let idxF : ι → Fin (S.card) := fun k =>
        if hk : k ∈ S then em ⟨k, hk⟩ else em ⟨σ i0, hMem i0 hi0⟩
      have hAbound : (A0.card : ℝ≥0) ≤ parentOverlapConst := by
        refine card_contributingParents_le hδ0 hδρ q T hball S σ hS hSep hClose V A0 ?_ ?_
        · exact Finset.filter_subset _ _
        · intro k hk
          exact (Finset.mem_filter.mp hk).2
      have hKsub : B ⊆ A0.image idxF := by
        intro k hkB
        rcases hBwit k hkB with ⟨i, hiq, hkP, hh⟩
        have hMem_i : σ i ∈ S := hMem i hiq
        have hAi : σ i ∈ A0 := Finset.mem_filter.mpr ⟨hMem_i, ⟨i, hiq, rfl, hh⟩⟩
        have hkidx : idxF (σ i) = k := by
          rw [← hkP]
          dsimp [idxF, Bassign, assignP]
          rw [dif_pos hMem_i, dif_pos hiq]
        exact Finset.mem_image.mpr ⟨σ i, hAi, hkidx⟩
      have hBle : (B.card : ℝ≥0) ≤ (A0.card : ℝ≥0) := by
        have hnat : B.card ≤ A0.card :=
          le_trans (Finset.card_le_card hKsub) Finset.card_image_le
        exact_mod_cast hnat
      exact le_trans hBle hAbound
    let hEx : ExternalParentSystem q T ρ parentOverlapConst :=
      { Parent := Fin (S.card)
        parents := Bparent
        parentTube := Btub
        assign := Bassign
        assign_mem := hassign_mem
        leaf_le_parent := hleaf2
        boundedOverlapThroughLeaves := by
          intro V
          refine hbounded2 V _ (fun k hk => ?_)
          simp only [Finset.mem_filter] at hk
          exact hk.2 }
    exact ⟨hEx⟩

/-- **Middle-scale regime**, `4 * δ ≤ ρ` and `32 * ρ ≤ 1`: the named specialisation of
`Kakeya.exists_externalParentSystem_of_four_mul_le`.  In this regime the overlap count runs through
longitudinal rigidity, which bounds the mutual parameter distance of the contributing parents by
`97 * ρ`. -/
theorem exists_externalParentSystem_middle
    {ι : Type*} {δ ρ : ℝ≥0} (hδ0 : 0 < δ) (hδρ : 4 * δ ≤ ρ) (_hρ : 32 * ρ ≤ 1)
    (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (ExternalParentSystem q T ρ parentOverlapConst) :=
  exists_externalParentSystem_of_four_mul_le hδ0 hδρ q T hball

/-- **Large-scale regime**, `1 < 32 * ρ` and `ρ ≤ 1`, with radius slack `4 * δ ≤ ρ`: the named
specialisation of `Kakeya.exists_externalParentSystem_of_four_mul_le`.  Here `ρ` is bounded below by
an absolute constant, rigidity is unavailable, and the overlap count instead uses that the whole
family lies in `B₁`, so the mutual parameter distance of the parents is at most `2`. -/
theorem exists_externalParentSystem_large
    {ι : Type*} {δ ρ : ℝ≥0} (hδ0 : 0 < δ) (hδρ : 4 * δ ≤ ρ) (_hρlo : 1 < 32 * ρ) (_hρ1 : ρ ≤ 1)
    (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (ExternalParentSystem q T ρ parentOverlapConst) :=
  exists_externalParentSystem_of_four_mul_le hδ0 hδρ q T hball

/-- **Near-scale regime**, `δ ≤ ρ < 4 * δ`.

There is no radius slack here, so the parents are the leaves themselves — reindexed through
`Finset.equivFin` to keep the construction available for `ι : Type*` — each rescaled to radius `ρ`.
Leaf containment is then immediate from `δ ≤ ρ`, and the whole content is bounded overlap, which is
the fine-family ED packing count `Kakeya.exists_card_le_of_ED_in_tube`.

This is the one regime that genuinely consumes **pairwise essential distinctness of the fine
family**: with many equal leaves the overlap of a single `8ρ`-tube is unbounded. -/
theorem exists_externalParentSystem_near :
    ∃ Cnear : ℝ≥0, 1 ≤ Cnear ∧
      ∀ {ι : Type*} {δ ρ : ℝ≥0}, 0 < δ → δ ≤ ρ → ρ < 4 * δ →
      ∀ (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (q : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        Nonempty (ExternalParentSystem q T ρ Cnear) := by
  classical
  obtain ⟨C, hCpos, hcount⟩ := exists_card_le_of_ED_in_tube
  refine ⟨max 1 C.toNNReal, le_max_left _ _, ?_⟩
  intro ι δ ρ hδ0 hδρ hρδ q T hball hED
  rcases q.eq_empty_or_nonempty with hempty | hq
  · subst hempty
    obtain ⟨a0, ha0⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 3))
    let e : EuclideanSpace ℝ (Fin 3) := (‖a0‖⁻¹ : ℝ) • a0
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg a0))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha0)
    let x0 : EuclideanSpace ℝ (Fin 3) := -((1 / 2 : ℝ) • e)
    let y0 : EuclideanSpace ℝ (Fin 3) := (1 / 2 : ℝ) • e
    have hd0 : dist x0 y0 = 1 := by
      rw [dist_eq_norm]
      calc
        ‖x0 - y0‖ = ‖(-1 : ℝ) • e‖ := by
          congr 1
          dsimp [x0, y0]
          module
        _ = 1 := by simp [he]
    have hmem (i : ι) : i ∈ (∅ : Finset ι) → False := by simp
    let hEx : ExternalParentSystem ∅ T ρ (max 1 C.toNNReal) :=
      { Parent := Unit
        parents := (∅ : Finset Unit)
        parentTube := fun _ => Tube.mk' ρ (x := x0) (y := y0) hd0
        assign := fun _ => ()
        assign_mem := by intro i hi; exact False.elim (hmem i hi)
        leaf_le_parent := by intro i hi; exact False.elim (hmem i hi)
        boundedOverlapThroughLeaves := by
          intro V
          simp }
    exact ⟨hEx⟩
  · obtain ⟨i0, hi0mem⟩ := hq
    let m : ℕ := q.card
    let em : {x : ι // x ∈ q} ≃ Fin m := Finset.equivFin q
    let rep : Fin m → ι := fun k => (em.symm k).1
    have hrep_mem : ∀ k, rep k ∈ q := fun k => (em.symm k).2
    let par : ι → Fin m := fun i => if h : i ∈ q then em ⟨i, h⟩ else em ⟨i0, hi0mem⟩
    have hrep_par : ∀ i ∈ q, rep (par i) = i := by
      intro i hi
      dsimp [rep, par]
      rw [dif_pos hi]
      exact congrArg Subtype.val (em.symm_apply_apply ⟨i, hi⟩)
    have hrep_inj : Function.Injective rep := by
      intro k l hkl
      apply em.symm.injective
      apply Subtype.ext
      simpa [rep] using hkl
    let T' : Fin m → Tube δ (EuclideanSpace ℝ (Fin 3)) := fun k => T (rep k)
    have hball' : ∀ k ∈ (Finset.univ : Finset (Fin m)), (T' k).carrier ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      intro k hk
      change (T (rep k)).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1
      exact hball (rep k) (hrep_mem k)
    have hED' : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).Pairwise
        (fun k l => IsEssentiallyDistinct (T' k).carrier (T' l).carrier) := by
      intro k hk l hl hkl
      have hrep_ne : rep k ≠ rep l := by
        intro h
        exact hkl (hrep_inj h)
      change IsEssentiallyDistinct (T (rep k)).carrier (T (rep l)).carrier
      exact hED (by simpa using hrep_mem k) (by simpa using hrep_mem l) hrep_ne
    have hbnn : ∀ (V : Tube (8 * ρ) (EuclideanSpace ℝ (Fin 3)))
        (B : Finset (Fin m)),
        (∀ k ∈ B, ∃ i ∈ q, par i = k ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) →
        (B.card : ℝ≥0) ≤ max 1 C.toNNReal := by
      intro V B hBwit
      have hB : (B.card : ℝ) ≤ C := by
        refine hcount (ι := Fin m) hδ0 hδρ hρδ (Finset.univ : Finset (Fin m)) T' hball'
          hED' V B (Finset.subset_univ B) ?_
        intro k hk
        rcases hBwit k hk with ⟨i, hi, hpar, hle⟩
        change (T (rep k)).toConvexSpaceBody ≤ V.toConvexSpaceBody
        calc
          (T (rep k)).toConvexSpaceBody ≤ (T (rep (par i))).toConvexSpaceBody := by
            rw [hpar.symm]
          _ = (T i).toConvexSpaceBody := by rw [hrep_par i hi]
          _ ≤ V.toConvexSpaceBody := hle
      have hcast : (B.card : ℝ).toNNReal = (B.card : ℝ≥0) := by
        simp
      have hBnn : (B.card : ℝ≥0) ≤ C.toNNReal := by
        rw [← hcast]
        exact Real.toNNReal_mono hB
      exact hBnn.trans (le_max_right _ _)
    let hEx : ExternalParentSystem q T ρ (max 1 C.toNNReal) :=
      { Parent := Fin m
        parents := (Finset.univ : Finset (Fin m))
        parentTube := fun k => (T' k).rescale ρ
        assign := par
        assign_mem := fun i hi => Finset.mem_univ (par i)
        leaf_le_parent := by
          intro i hi
          dsimp [T']
          rw [hrep_par i hi]
          exact (T i).le_rescale hδρ
        boundedOverlapThroughLeaves := by
          intro V
          refine hbnn V _ (fun k hk => ?_)
          simp only [Finset.mem_filter] at hk
          exact hk.2 }
    exact ⟨hEx⟩

/-- **The arbitrary-scale external parent system.**

For every `0 < δ ≤ ρ ≤ 1` a coarse parent system exists with an absolute overlap constant, given
pairwise essential distinctness of the fine family.  Two regimes, glued on `4 * δ ≤ ρ`:

* `4 * δ ≤ ρ` — the maximal-separated construction in centre × projective-direction parameter space,
  counted either by rigidity (`32 * ρ ≤ 1`) or by `B₁` containment (`1 < 32 * ρ`);
* `ρ < 4 * δ` — the leaves themselves as parents, counted by fine-family ED packing.

**Uniformity is not used.**  No field of `StickyKakeya.UniformTubeSet` or
`StickyKakeya.ShadedUniformTubeSet` enters, and there is no `δ ^ (-η)` loss: `Cparent` depends on
nothing but the dimension.  What the near regime does consume is pairwise ED of the *fine* family —
not of the coarse parents, and not any hierarchy datum. -/
theorem exists_externalParentSystem :
    ∃ Cparent : ℝ≥0, 1 ≤ Cparent ∧
      ∀ {ι : Type*} {δ ρ : ℝ≥0}, 0 < δ → δ ≤ ρ → ρ ≤ 1 →
      ∀ (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (q : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        Nonempty (ExternalParentSystem q T ρ Cparent) := by
  obtain ⟨Cnear, hCnear1, hnear⟩ := exists_externalParentSystem_near
  refine ⟨max parentOverlapConst Cnear, le_trans hCnear1 (le_max_right _ _), ?_⟩
  intro ι δ ρ hδ0 hδρ hρ1 q T hball hED
  by_cases h4 : 4 * δ ≤ ρ
  · obtain ⟨PS⟩ := exists_externalParentSystem_of_four_mul_le hδ0 h4 q T hball
    exact ⟨PS.monoConst (le_max_left _ _)⟩
  · have h4' : ρ < 4 * δ := not_le.mp h4
    obtain ⟨PS⟩ := hnear hδ0 hδρ h4' q T hball hED
    exact ⟨PS.monoConst (le_max_right _ _)⟩

end Kakeya

end

end
