import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.SelfDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Thickening growth for convex sets with an inball

If a convex set contains a closed ball of radius `delta`, its closed
`rho`-neighborhood lies in a homothetic image with factor
`1 + 2 * rho / delta`.  The factor `2` avoids any closedness or nearest-point
assumption on the original convex set.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- Lebesgue volume under a homothety in `Point3`. -/
lemma volume_homothety_image
    (p : Point3) (c : ℝ) (hc : c ≠ 0)
    (S : Set Point3) :
    volume (AffineMap.homothety p c '' S) =
      ENNReal.ofReal (|c| ^ 3) * volume S := by
  have h :=
    MeasureTheory.euclideanHausdorffMeasure_homothety_image
      3 p hc S
  have heq : (μHE[3] : Measure Point3) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume 3
  rw [heq] at h
  simpa [NNReal.smul_def, NNReal.coe_pow, ENNReal.smul_def] using h

/-- The volume of a homothetically dilated tube carrier. -/
lemma volume_dilatedTubeCarrier
    {rho A : ℝ} (hA : A ≠ 0)
    (T : Kakeya.DeltaTube rho) :
    volume (dilatedTubeCarrier A T) =
      ENNReal.ofReal (|A| ^ 3) *
        Kakeya.deltaTubeVolume rho := by
  rw [dilatedTubeCarrier]
  rw [volume_homothety_image _ _ hA]
  congr 1
  exact RandomTranslation.tube_volume_eq_deltaTubeVolume T

/-- Equal-radius dilated tube carriers have equal volume. -/
lemma volume_dilatedTubeCarrier_eq
    {rho A : ℝ} (hA : A ≠ 0)
    (T U : Kakeya.DeltaTube rho) :
    volume (dilatedTubeCarrier A T) =
      volume (dilatedTubeCarrier A U) := by
  rw [volume_dilatedTubeCarrier hA T,
    volume_dilatedTubeCarrier hA U]

/--
The closed `rho`-neighborhood of a convex set containing
`closedBall p delta` lies in its dilation about `p` by
`1 + 2 * rho / delta`.
-/
lemma cthickening_subset_homothety_of_closedBall_subset
    {K : Set Point3} (hK : Convex ℝ K)
    {p : Point3} {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hball : Metric.closedBall p delta ⊆ K) :
    Metric.cthickening rho K ⊆
      AffineMap.homothety p (1 + 2 * rho / delta) '' K := by
  intro x hx
  have hcover :=
    Metric.cthickening_subset_iUnion_closedBall_of_lt
      K (show 0 < 2 * rho by positivity) (by linarith)
  rcases Set.mem_iUnion₂.mp (hcover hx) with
    ⟨y, hyK, hxy⟩
  let t := 1 + 2 * rho / delta
  have hratio : 0 < 2 * rho / delta := by
    positivity
  have ht : 1 < t := by
    dsimp only [t]
    linarith
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  let w := p + (1 / (t - 1)) • (x - y)
  have hwball : w ∈ Metric.closedBall p delta := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖x - y‖ ≤ 2 * rho := by
      simpa [dist_eq_norm] using hxy
    have htminus : t - 1 = 2 * rho / delta := by
      dsimp only [t]
      ring
    rw [show w - p = (1 / (t - 1)) • (x - y) by
      dsimp only [w]
      abel]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / (t - 1))]
    rw [htminus]
    calc
      (1 / (2 * rho / delta)) * ‖x - y‖
          ≤ (1 / (2 * rho / delta)) * (2 * rho) := by
        gcongr
      _ = delta := by
        field_simp [hdelta.ne', hrho.ne']
  have hwK : w ∈ K := hball hwball
  let a := 1 / t
  let b := (t - 1) / t
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hab : a + b = 1 := by
    dsimp only [a, b]
    field_simp [ht0.ne']
    ring
  let q := a • y + b • w
  have hqK : q ∈ K :=
    hK hyK hwK ha hb hab
  refine ⟨q, hqK, ?_⟩
  rw [AffineMap.homothety_apply]
  have htminus : t - 1 ≠ 0 := by
    linarith
  have hta : t * a = 1 := by
    dsimp only [a]
    field_simp [ht0.ne']
  have htb : t * b = t - 1 := by
    dsimp only [b]
    field_simp [ht0.ne']
  have htc : (t - 1) * (1 / (t - 1)) = 1 := by
    field_simp [htminus]
  change t • (q - p) + p = x
  dsimp only [q]
  rw [smul_sub, smul_add, smul_smul, smul_smul,
    hta, htb, one_smul]
  dsimp only [w]
  rw [smul_add, smul_smul, htc, one_smul]
  module

/--
Three-dimensional volume growth of a convex set with a radius-`delta`
inball.
-/
lemma volume_cthickening_le_of_closedBall_subset
    {K : Set Point3} (hK : Convex ℝ K)
    {p : Point3} {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hball : Metric.closedBall p delta ⊆ K) :
    volume (Metric.cthickening rho K) ≤
      ENNReal.ofReal ((1 + 2 * rho / delta) ^ 3) *
        volume K := by
  let t := 1 + 2 * rho / delta
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have hsubset :=
    cthickening_subset_homothety_of_closedBall_subset
      hK hdelta hrho hball
  calc
    volume (Metric.cthickening rho K)
        ≤ volume (AffineMap.homothety p t '' K) :=
      measure_mono hsubset
    _ = ENNReal.ofReal (|t| ^ 3) * volume K :=
      volume_homothety_image p t ht.ne' K
    _ = ENNReal.ofReal (t ^ 3) * volume K := by
      rw [abs_of_pos ht]
    _ = ENNReal.ofReal ((1 + 2 * rho / delta) ^ 3) *
        volume K := by
      rfl

/-- A tube contains the radius-`delta` closed ball about its midpoint. -/
lemma closedBall_midpoint_subset_tube
    {delta : ℝ} (T : Kakeya.DeltaTube delta) :
    Metric.closedBall
        (GeometricLemmas.tubeMidpoint T) delta ⊆
      T.carrier := by
  exact Metric.closedBall_subset_cthickening
    (by
      refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      simp [GeometricLemmas.tubeMidpoint])
    delta

/--
If a convex set contains a positive-radius tube, its `rho`-neighborhood has
the same homothetic volume-growth bound.
-/
lemma volume_cthickening_le_of_tube_subset
    {K : Set Point3} (hK : Convex ℝ K)
    {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (T : Kakeya.DeltaTube delta)
    (hTK : T.carrier ⊆ K) :
    volume (Metric.cthickening rho K) ≤
      ENNReal.ofReal ((1 + 2 * rho / delta) ^ 3) *
        volume K := by
  exact volume_cthickening_le_of_closedBall_subset
    hK hdelta hrho
    ((closedBall_midpoint_subset_tube T).trans hTK)

/--
For `delta ≤ rho`, the growth factor is at most
`27 * (rho / delta)^3`.
-/
lemma volume_cthickening_le_of_tube_subset'
    {K : Set Point3} (hK : Convex ℝ K)
    {delta rho : ℝ}
    (hdelta : 0 < delta) (hdelta_rho : delta ≤ rho)
    (T : Kakeya.DeltaTube delta)
    (hTK : T.carrier ⊆ K) :
    volume (Metric.cthickening rho K) ≤
      ENNReal.ofReal (27 * (rho / delta) ^ 3) *
        volume K := by
  have hrho : 0 < rho := lt_of_lt_of_le hdelta hdelta_rho
  have hbase :
      1 + 2 * rho / delta ≤ 3 * (rho / delta) := by
    have hone : 1 ≤ rho / delta := by
      exact (le_div_iff₀ hdelta).2 (by simpa using hdelta_rho)
    have hrewrite :
        2 * rho / delta = 2 * (rho / delta) := by
      ring
    rw [hrewrite]
    linarith
  have hnonneg : 0 ≤ 1 + 2 * rho / delta := by
    positivity
  have hpow :
      (1 + 2 * rho / delta) ^ 3 ≤
        27 * (rho / delta) ^ 3 := by
    calc
      (1 + 2 * rho / delta) ^ 3
          ≤ (3 * (rho / delta)) ^ 3 := by
        gcongr
      _ = 27 * (rho / delta) ^ 3 := by
        ring
  calc
    volume (Metric.cthickening rho K)
        ≤ ENNReal.ofReal ((1 + 2 * rho / delta) ^ 3) *
            volume K :=
      volume_cthickening_le_of_tube_subset
        hK hdelta hrho T hTK
    _ ≤ ENNReal.ofReal (27 * (rho / delta) ^ 3) *
        volume K := by
      gcongr

end Kakeya.Streamlined
