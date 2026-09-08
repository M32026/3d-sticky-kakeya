import MyLeanRepo.Kakeya.Streamlined.PlankFrostman.PairCollision

/-!
# Measure-theoretic infrastructure for random rigid-motion sampling

Provides:
1. Normalized probability measure on rigid motions (rotation × translation).
2. Product measure for `J` independent motions with `IsProbabilityMeasure`.
3. Union bound over finite index sets.
4. Conflict probability bounds via `pair_collision_single_motion` + normalization.
-/

noncomputable section

open MeasureTheory Metric Set Classical Finset ProbabilityTheory
open Kakeya.Streamlined
open Kakeya.Streamlined.GeneralizedFrostman
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.GeneralizedFrostman

/-! ### Normalized probability measure on rigid motions -/

/-- Volume of the unit ball in `Point3`. -/
def unitBallVolume : ENNReal := volume (closedBall (0 : Point3) 1)

lemma unitBallVolume_pos : 0 < unitBallVolume :=
  Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)

lemma unitBallVolume_ne_top : unitBallVolume ≠ ⊤ :=
  IsCompact.measure_lt_top (isCompact_closedBall (0 : Point3) 1) |>.ne

/-- Normalized translation measure: uniform probability on the closed unit ball. -/
def translationProbMeasure : Measure Point3 :=
  unitBallVolume⁻¹ • volume.restrict (closedBall (0 : Point3) 1)

instance : IsProbabilityMeasure translationProbMeasure := by
  rw [MeasureTheory.isProbabilityMeasure_iff]
  have h1 : translationProbMeasure Set.univ =
      unitBallVolume⁻¹ * volume (closedBall (0 : Point3) 1) := by
    simp [translationProbMeasure, Measure.smul_apply]
  rw [h1]
  have h2 : unitBallVolume⁻¹ * unitBallVolume = 1 :=
    ENNReal.inv_mul_cancel unitBallVolume_pos.ne' unitBallVolume_ne_top
  exact h2

/-- Probability measure on a single rigid motion: rotation × normalized translation. -/
def rigidMotionProbMeasure (data : DirectionalAntiConcData) :
    Measure ((sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) × Point3) :=
  data.μ.prod translationProbMeasure

-- Product of probability measures is automatically a probability measure.

/-- Product measure for `J` independent rigid motions. -/
def rigidMotionsProductMeasure (data : DirectionalAntiConcData) (J : ℕ) :
    Measure (Fin J → (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) × Point3) :=
  Measure.pi (fun _ : Fin J => rigidMotionProbMeasure data)

-- Pi measure of probability measures is automatically a probability measure.

/-- Relate normalized and unnormalized single-motion measures. -/
lemma rigidMotionProbMeasure_apply (data : DirectionalAntiConcData)
    (s : Set ((sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) × Point3)) :
    rigidMotionProbMeasure data s =
      (data.μ.prod (volume.restrict (closedBall (0 : Point3) 1))) s / unitBallVolume := by
  have h_smul_prod : data.μ.prod (unitBallVolume⁻¹ • volume.restrict (closedBall (0 : Point3) 1)) =
      unitBallVolume⁻¹ • data.μ.prod (volume.restrict (closedBall (0 : Point3) 1)) :=
    Measure.prod_smul_right unitBallVolume⁻¹
  have h1 : rigidMotionProbMeasure data =
      unitBallVolume⁻¹ • data.μ.prod (volume.restrict (closedBall (0 : Point3) 1)) := by
    simp [rigidMotionProbMeasure, translationProbMeasure, h_smul_prod]
  rw [h1]
  have h2 : (unitBallVolume⁻¹ • data.μ.prod (volume.restrict (closedBall (0 : Point3) 1))) s =
      unitBallVolume⁻¹ * (data.μ.prod (volume.restrict (closedBall (0 : Point3) 1))) s := by
    rw [Measure.smul_apply]
    <;> rfl
  rw [h2]
  have h_div : unitBallVolume⁻¹ * (data.μ.prod (volume.restrict (closedBall (0 : Point3) 1))) s =
      (data.μ.prod (volume.restrict (closedBall (0 : Point3) 1))) s / unitBallVolume := by
    rw [div_eq_mul_inv]
    <;> ring
  exact h_div

/-! ### Union bound (works for arbitrary sets via outer measure) -/

/-- Finite union bound: measure of union ≤ sum of measures. -/
lemma finite_union_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} [Fintype ι] {A : ι → Set Ω} :
    μ (⋃ i : ι, A i) ≤ ∑ i : ι, μ (A i) := by
  exact measure_iUnion_fintype_le μ A

/-! ### Conflict probability for normalized measure -/

/-- Probability that a random rigid copy of tube `T` is non-ED with fixed `T0`,
using the normalized probability measure. -/
lemma non_ed_probability_normalized
    {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ ≤ 1 / 1000)
    (data : DirectionalAntiConcData)
    (T T0 : Kakeya.DeltaTube δ)
    (hT_ball : T.carrier ⊆ unitBall.carrier)
    (hT0_ball : T0.carrier ⊆ unitBall.carrier)
    (V : ENNReal) (hV_T0 : T0.volume = V) :
    rigidMotionProbMeasure data
      {p | p.2 ∈ closedBall (0 : Point3) 1 ∧
        ¬(translateTube (rigidMoveTube T (data.rotation p.1) 0) p.2).EssentiallyDistinct T0}
    ≤ (2 * V * data.C_dir * ENNReal.ofReal ((1000 * δ)^2)) / unitBallVolume := by
  rw [rigidMotionProbMeasure_apply]
  let B1 := closedBall (0 : Point3) 1
  let ν := volume.restrict B1
  let badSet : Set ((sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) × Point3) :=
    {p | p.2 ∈ B1 ∧
      ¬(translateTube (rigidMoveTube T (data.rotation p.1) 0) p.2).EssentiallyDistinct T0}
  have h_pair : (data.μ.prod ν) badSet ≤ 2 * T0.volume * data.C_dir * ENNReal.ofReal ((1000 * δ)^2) :=
    pair_collision_single_motion data hδ hδ_small T T0 hT_ball hT0_ball
  have h_pair' : (data.μ.prod ν) badSet ≤ 2 * V * data.C_dir * ENNReal.ofReal ((1000 * δ)^2) := by
    rw [hV_T0] at h_pair
    exact h_pair
  gcongr

/-- Probability that a random rigid copy of family `T` has at least one tube
non-ED with fixed `T0`. Bound: |T| * O(V * δ²) / unitBallVolume. -/
lemma any_conflict_probability_normalized
    {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ ≤ 1 / 1000)
    {T : TubeFamily δ} (hT_ball : T.IsInUnitBall)
    (data : DirectionalAntiConcData)
    (V : ENNReal) (hV : ∀ i, (T.tube i).volume = V)
    (T0 : Kakeya.DeltaTube δ) (hT0_ball : T0.carrier ⊆ unitBall.carrier)
    (hV_T0 : T0.volume = V) :
    rigidMotionProbMeasure data
      {p | p.2 ∈ closedBall (0 : Point3) 1 ∧
        ∃ i : Fin T.card,
          ¬(translateTube (rigidMoveTube (T.tube i) (data.rotation p.1) 0) p.2).EssentiallyDistinct T0}
    ≤ (T.card : ENNReal) * (2 * V * data.C_dir * ENNReal.ofReal ((1000 * δ)^2)) / unitBallVolume := by
  let bad_union := ⋃ i : Fin T.card, {p : _ × Point3 |
      p.2 ∈ closedBall (0 : Point3) 1 ∧
      ¬(translateTube (rigidMoveTube (T.tube i) (data.rotation p.1) 0) p.2).EssentiallyDistinct T0}

  have h_sub : {p : _ × Point3 | p.2 ∈ closedBall (0 : Point3) 1 ∧
      ∃ i : Fin T.card,
        ¬(translateTube (rigidMoveTube (T.tube i) (data.rotation p.1) 0) p.2).EssentiallyDistinct T0}
      ⊆ bad_union := by
    intro p hp
    rcases hp.2 with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨hp.1, hi⟩⟩

  calc
    rigidMotionProbMeasure data _
      ≤ rigidMotionProbMeasure data bad_union := measure_mono h_sub
    _ ≤ ∑ i : Fin T.card, rigidMotionProbMeasure data {p |
          p.2 ∈ closedBall (0 : Point3) 1 ∧
          ¬(translateTube (rigidMoveTube (T.tube i) (data.rotation p.1) 0) p.2).EssentiallyDistinct T0} :=
        finite_union_bound
    _ ≤ ∑ i : Fin T.card, (2 * V * data.C_dir * ENNReal.ofReal ((1000 * δ)^2)) / unitBallVolume := by
        apply Finset.sum_le_sum
        intro i _
        exact non_ed_probability_normalized hδ hδ_small data (T.tube i) T0
          (hT_ball i) hT0_ball V hV_T0
    _ = (T.card : ENNReal) * ((2 * V * data.C_dir * ENNReal.ofReal ((1000 * δ)^2)) / unitBallVolume) := by
        simp [Finset.sum_const] <;> ring
    _ = (T.card : ENNReal) * (2 * V * data.C_dir * ENNReal.ofReal ((1000 * δ)^2)) / unitBallVolume := by
        simpa [mul_div_assoc] using rfl

end Kakeya.Streamlined.GeneralizedFrostman
