import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Geometric probability estimates for random translations

Key lemma: for a random translation v uniform on B_ρ,
P(translate(T, v) ⊆ K) ≤ |K| / |B_ρ|.

If K ⊆ T_ρ (a ρ-tube), then |K| ≤ |T_ρ| ≲ ρ²,
while |B_ρ| ≈ ρ³, so P ≲ 1/ρ.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

open Kakeya.Streamlined

/-- Translate a set by vector v. -/
def translateSet (s : Set Point3) (v : Point3) : Set Point3 :=
  (fun x => x + v) '' s

/-- The set of translations that put a specified point `x` into `K`. -/
def translationsTakingPointTo (x : Point3) (K : Set Point3) : Set Point3 :=
  {v | x + v ∈ K}

/-- If a translated tube is contained in K, then any specified point of the tube
is also translated into K. -/
lemma containment_implies_point_in_K {δ : ℝ} (T : Kakeya.DeltaTube δ)
    (K : Set Point3) (x : Point3) (hx : x ∈ T.carrier) :
    {v : Point3 | translateSet T.carrier v ⊆ K} ⊆ translationsTakingPointTo x K := by
  intro v hv
  have h1 : x + v ∈ translateSet T.carrier v := by
    exact ⟨x, hx, rfl⟩
  exact hv h1

/-- `translationsTakingPointTo x K` is the image of K under w ↦ w - x. -/
lemma translationsTakingPointTo_eq (x : Point3) (K : Set Point3) :
    translationsTakingPointTo x K = (fun w : Point3 => w - x) '' K := by
  ext v
  simp only [translationsTakingPointTo, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h
    refine ⟨x + v, h, ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    simpa [sub_eq_add_neg, add_comm] using hy

/-- `translationsTakingPointTo x K` is the preimage of K under v ↦ x + v. -/
lemma translationsTakingPointTo_eq_preimage (x : Point3) (K : Set Point3) :
    translationsTakingPointTo x K = (fun v : Point3 => x + v) ⁻¹' K := by
  ext v
  simp [translationsTakingPointTo]

/-- Volume of translation set equals volume of K, by translation invariance. -/
lemma volume_translationsTakingPointTo {x : Point3} {K : Set Point3}
    (hK : MeasurableSet K) :
    MeasureTheory.volume (translationsTakingPointTo x K) = MeasureTheory.volume K := by
  rw [translationsTakingPointTo_eq_preimage]
  have h_mp : MeasurePreserving (fun v : Point3 => x + v) := by
    have h : MeasurePreserving (fun v : Point3 => v + x) := measurePreserving_add_right volume x
    have h_eq : (fun v : Point3 => x + v) = (fun v : Point3 => v + x) := by
      funext v; simp [add_comm]
    rw [h_eq]
    exact h
  exact h_mp.measure_preimage hK.nullMeasurableSet

/-- The base point of a tube is in its carrier. -/
lemma base_in_tube_carrier {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    T.base ∈ T.carrier := by
  have h0 : T.base ∈ unitSegment T.base T.direction := by
    refine ⟨0, by norm_num, ?_⟩
    simp
  have h1 : T.base ∈ Metric.cthickening δ (unitSegment T.base T.direction) := by
    rw [Metric.mem_cthickening_iff]
    have h2 : Metric.infEDist T.base (unitSegment T.base T.direction) = 0 := by
      apply le_antisymm
      · have h3 : Metric.infEDist T.base (unitSegment T.base T.direction) ≤
            edist T.base T.base := Metric.infEDist_le_edist_of_mem h0
        simpa using h3
      · simp
    rw [h2]
    simp
  exact h1

/-- Volume of translations v with translate(T, v) ⊆ K is at most volume K. -/
lemma volume_containment_translations_le {δ : ℝ}
    (T : Kakeya.DeltaTube δ) (K : Set Point3) (hK : MeasurableSet K) :
    MeasureTheory.volume {v : Point3 | translateSet T.carrier v ⊆ K} ≤
      MeasureTheory.volume K := by
  have h_base_in : T.base ∈ T.carrier := base_in_tube_carrier T
  have h_sub : {v : Point3 | translateSet T.carrier v ⊆ K} ⊆
      translationsTakingPointTo T.base K :=
    containment_implies_point_in_K T K T.base h_base_in
  have h_vol : MeasureTheory.volume (translationsTakingPointTo T.base K) =
      MeasureTheory.volume K := volume_translationsTakingPointTo hK
  calc MeasureTheory.volume {v : Point3 | translateSet T.carrier v ⊆ K}
    ≤ MeasureTheory.volume (translationsTakingPointTo T.base K) :=
      measure_mono h_sub
  _ = MeasureTheory.volume K := h_vol

/-- Volume of translations v ∈ B_ρ with translate(T, v) ⊆ K is at most
min(volume K, volume B_ρ). -/
lemma volume_containment_translations_ball_le {δ : ℝ}
    (T : Kakeya.DeltaTube δ) (K : Set Point3) (hK : MeasurableSet K)
    {rho : ℝ} (_hrho : 0 ≤ rho) :
    MeasureTheory.volume ({v : Point3 | translateSet T.carrier v ⊆ K} ∩
      Metric.closedBall (0 : Point3) rho)
    ≤ min (MeasureTheory.volume K)
        (MeasureTheory.volume (Metric.closedBall (0 : Point3) rho)) := by
  let S := {v : Point3 | translateSet T.carrier v ⊆ K}
  let B := Metric.closedBall (0 : Point3) rho
  have h1 : S ∩ B ⊆ S := by simp
  have h2 : S ∩ B ⊆ B := by simp
  have h3 : MeasureTheory.volume (S ∩ B) ≤ MeasureTheory.volume K := by
    calc MeasureTheory.volume (S ∩ B)
      ≤ MeasureTheory.volume S := measure_mono h1
    _ ≤ MeasureTheory.volume K := volume_containment_translations_le T K hK
  have h4 : MeasureTheory.volume (S ∩ B) ≤ MeasureTheory.volume B :=
    measure_mono h2
  exact le_min h3 h4

/-- Probability estimate: volume of good translations ≤ |K| / |B_ρ| * |B_ρ|.

This is the ENNReal way of saying P ≤ |K| / |B_ρ|. -/
lemma containment_probability_estimate {δ : ℝ}
    (T : Kakeya.DeltaTube δ) (K : Set Point3) (hK : MeasurableSet K)
    {rho : ℝ} (hrho : 0 < rho) :
    MeasureTheory.volume ({v : Point3 | translateSet T.carrier v ⊆ K} ∩
      Metric.closedBall (0 : Point3) rho)
    ≤ MeasureTheory.volume K / MeasureTheory.volume (Metric.closedBall (0 : Point3) rho)
      * MeasureTheory.volume (Metric.closedBall (0 : Point3) rho) := by
  let B := Metric.closedBall (0 : Point3) rho
  have h_ball_pos : 0 < MeasureTheory.volume B :=
    Metric.measure_closedBall_pos volume 0 hrho
  have h_ball_compact : IsCompact B := isCompact_closedBall 0 rho
  have h_ball_lt_top : MeasureTheory.volume B < ⊤ := measure_closedBall_lt_top
  have h_ball_ne_top : MeasureTheory.volume B ≠ ⊤ := h_ball_lt_top.ne
  have h5 : MeasureTheory.volume K / MeasureTheory.volume B * MeasureTheory.volume B =
      MeasureTheory.volume K :=
    ENNReal.div_mul_cancel h_ball_pos.ne' h_ball_ne_top
  have h_all := volume_containment_translations_ball_le T K hK (le_of_lt hrho)
  have h_main : MeasureTheory.volume (_ ∩ B) ≤ MeasureTheory.volume K :=
    (le_min_iff.mp h_all).1
  rw [h5]
  exact h_main

/-- If K ⊆ T_ρ, then volume K ≤ volume T_ρ. -/
lemma volume_subset_tube {ρ : ℝ} (T_ρ : Kakeya.DeltaTube ρ)
    (K : Set Point3) (h_sub : K ⊆ T_ρ.carrier) :
    MeasureTheory.volume K ≤ T_ρ.volume := by
  exact measure_mono h_sub

/-- Volume of B_ρ in R³ is proportional to ρ³. -/
lemma ball_volume_formula {rho : ℝ} :
    MeasureTheory.volume (Metric.closedBall (0 : Point3) rho) =
      ENNReal.ofReal rho ^ 3 *
        ENNReal.ofReal (Real.sqrt Real.pi ^ 3 / Real.Gamma (5 / 2)) := by
  have h := EuclideanSpace.volume_closedBall (Fin 3) (0 : Point3) rho
  have h5 : (Fintype.card (Fin 3) : ℝ) = 3 := by norm_num
  rw [h5] at h
  have h6 : (3 : ℝ) / 2 + 1 = 5 / 2 := by norm_num
  rw [h6] at h
  exact h

end Kakeya.Streamlined.RandomTranslation
