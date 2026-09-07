import MyLeanRepo.Kakeya.Assouad.Targets.TubeVolumeScaling
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lower bound for δ-tube volume

Every δ-tube has volume at least δ².

The canonical δ-tube contains the axis-aligned box
`[0,1] × [-δ/2,δ/2] × [-δ/2,δ/2]`, whose volume is δ².
The volume equality from `TubeVolumeScaling` transfers this bound
to every δ-tube.
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Assouad

/-- The canonical δ-tube contains the box `[0,1] × [-δ/2,δ/2] × [-δ/2,δ/2]`. -/
private lemma canonical_tube_contains_box
    {δ : ℝ} (hδ : 0 < δ) :
    (WithLp.toLp 2) '' Set.Icc
        (fun i : Fin 3 =>
          match i with
          | 0 => 0
          | 1 => -δ / 2
          | 2 => -δ / 2)
        (fun i : Fin 3 =>
          match i with
          | 0 => 1
          | 1 => δ / 2
          | 2 => δ / 2) ⊆
      Metric.cthickening δ
        (Kakeya.unitSegment 0
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := by
  intro x hx
  rcases hx with ⟨v, hv, rfl⟩
  let t : ℝ := v 0
  have hlo : ∀ i, (match i with
    | 0 => (0 : ℝ)
    | 1 => -δ / 2
    | 2 => -δ / 2) ≤ v i := hv.1
  have hhi : ∀ i, v i ≤ (match i with
    | 0 => (1 : ℝ)
    | 1 => δ / 2
    | 2 => δ / 2) := hv.2
  have ht0 : 0 ≤ t := hlo 0
  have ht1 : t ≤ 1 := hhi 0
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  let q : Point3 := t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have hq : q ∈ Kakeya.unitSegment 0 (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) :=
    ⟨t, ht, by simp [q]⟩
  have h1 : |v 1| ≤ δ / 2 := by
    have hlo1 : -δ / 2 ≤ v 1 := hlo 1
    have hhi1 : v 1 ≤ δ / 2 := hhi 1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h2 : |v 2| ≤ δ / 2 := by
    have hlo2 : -δ / 2 ≤ v 2 := hlo 2
    have hhi2 : v 2 ≤ δ / 2 := hhi 2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h1sq : (v 1) ^ 2 ≤ (δ / 2) ^ 2 := by
    have h : |v 1| ^ 2 ≤ (δ / 2) ^ 2 := by gcongr
    have h' : |v 1| ^ 2 = (v 1) ^ 2 := by
      rw [sq_abs]
    rw [h'] at h
    exact h
  have h2sq : (v 2) ^ 2 ≤ (δ / 2) ^ 2 := by
    have h : |v 2| ^ 2 ≤ (δ / 2) ^ 2 := by gcongr
    have h' : |v 2| ^ 2 = (v 2) ^ 2 := by
      rw [sq_abs]
    rw [h'] at h
    exact h
  have hsum : (v 1) ^ 2 + (v 2) ^ 2 ≤ δ ^ 2 := by
    nlinarith
  have hdist : dist (WithLp.toLp 2 v) q ≤ δ := by
    let w : Fin 3 → ℝ := fun i =>
        match i with
        | 0 => 0
        | 1 => v 1
        | 2 => v 2
    have hdiff : (WithLp.toLp 2 v) - q = WithLp.toLp 2 w := by
      ext i
      fin_cases i <;> simp [q, w, t]
    rw [dist_eq_norm, hdiff]
    rw [PiLp.norm_eq_of_L2]
    have hsum2 : ∑ i : Fin 3, ‖(WithLp.toLp 2 w) i‖ ^ 2 = (v 1) ^ 2 + (v 2) ^ 2 := by
      simp [w, Fin.sum_univ_succ]
    rw [hsum2]
    have hsqrt : Real.sqrt ((v 1) ^ 2 + (v 2) ^ 2) ≤ δ := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · exact hsum
    exact hsqrt
  exact Metric.mem_cthickening_of_dist_le (WithLp.toLp 2 v) q δ _ hq hdist

/-- Lower bound: the canonical δ-tube has volume at least δ². -/
lemma canonical_volume_lower {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ 2) ≤ Kakeya.deltaTubeVolume δ := by
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 0
    | 1 => -δ / 2
    | 2 => -δ / 2
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 1
    | 1 => δ / 2
    | 2 => δ / 2
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    fin_cases i <;> dsimp [lo, hi] <;> linarith
  have hbox :
      volume ((WithLp.toLp 2) '' Set.Icc lo hi) ≤
        volume (Metric.cthickening δ
          (Kakeya.unitSegment 0
            (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))) :=
    measure_mono (canonical_tube_contains_box hδ)
  have hvol :
      volume ((WithLp.toLp 2) '' Set.Icc lo hi) =
        ENNReal.ofReal (δ ^ 2) := by
    rw [volume_rectBox lo hi hlohi]
    have h : (1 - 0) * (δ / 2 - (-δ / 2)) * (δ / 2 - (-δ / 2)) = δ ^ 2 := by
      ring
    rw [h]
  rw [hvol] at hbox
  simpa [Kakeya.deltaTubeVolume] using hbox

/-- Every δ-tube has volume at least δ². -/
lemma tube_volume_lower_bound {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1 / 2)
    (T : Kakeya.DeltaTube δ) :
    ENNReal.ofReal (δ ^ 2) ≤ T.volume := by
  have hvol_scaling : TubeVolumeScalingStatement := tube_volume_scaling
  have hT : T.volume = Kakeya.deltaTubeVolume δ := hvol_scaling.1 δ T
  rw [hT]
  exact canonical_volume_lower hδ

end Kakeya.Assouad
