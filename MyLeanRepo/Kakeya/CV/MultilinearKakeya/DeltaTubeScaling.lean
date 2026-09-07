import MyLeanRepo.Kakeya.CV.MultilinearKakeya
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Scale unit-line multilinear Kakeya to delta-tubes

The geometric and measure-theoretic rescaling bridge from project delta-tubes
to unit neighborhoods of affine lines.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.CV

private lemma unitSegment_isCompact (base direction : Point 3) :
    IsCompact (Kakeya.unitSegment base direction) := by
  exact isCompact_Icc.image
    (continuous_const.add (continuous_id.smul continuous_const))

private lemma unitSegment_nonempty (base direction : Point 3) :
    (Kakeya.unitSegment base direction).Nonempty := by
  refine ⟨base, 0, by simp, ?_⟩
  simp

private lemma deltaTube_scaled_mem_unitTube {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ) (y : Point 3)
    (hy : δ • y ∈ T.carrier) :
    y ∈ unitTube (δ⁻¹ • T.base) T.direction := by
  have hcompact : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    unitSegment_isCompact T.base T.direction
  have hnonempty : (Kakeya.unitSegment T.base T.direction).Nonempty :=
    unitSegment_nonempty T.base T.direction
  obtain ⟨z, hz, hdist_eq⟩ :=
    hcompact.exists_infEDist_eq_edist hnonempty (δ • y)
  have hdist_enn : edist (δ • y) z ≤ ENNReal.ofReal δ := by
    rw [← hdist_eq]
    exact hy
  have hdist : dist (δ • y) z ≤ δ := by
    rw [edist_dist] at hdist_enn
    exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp hdist_enn
  rcases hz with ⟨t, ht, rfl⟩
  let z' : Point 3 := δ⁻¹ • (T.base + t • T.direction)
  have hz' : z' ∈ affineLine (δ⁻¹ • T.base) T.direction := by
    refine ⟨δ⁻¹ * t, ?_⟩
    dsimp only [z']
    module
  have hscale : δ • z' = T.base + t • T.direction := by
    dsimp only [z']
    rw [smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
  have hdist' : dist y z' ≤ 1 := by
    have hscaled : δ * dist y z' ≤ δ := by
      calc
        δ * dist y z' = dist (δ • y) (δ • z') := by
          rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hδ]
        _ = dist (δ • y) (T.base + t • T.direction) := by
          rw [hscale]
        _ ≤ δ := hdist
    nlinarith
  exact (Metric.infDist_le_dist_of_mem hz').trans hdist'

private lemma deltaTube_indicator_scaled_le {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ) (y : Point 3) :
    setIndicator T.carrier (δ • y) ≤
      setIndicator (unitTube (δ⁻¹ • T.base) T.direction) y := by
  by_cases hy : δ • y ∈ T.carrier
  · have hy' := deltaTube_scaled_mem_unitTube hδ T y hy
    simp [setIndicator, hy, hy']
  · simp [setIndicator, hy]

private lemma lintegral_eq_ofReal_cube_mul_lintegral_comp_smul
    (f : Point 3 → ENNReal) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ x : Point 3, f x ∂volume) =
      ENNReal.ofReal (δ ^ 3) * ∫⁻ y : Point 3, f (δ • y) ∂volume := by
  let e : Point 3 ≃ᵐ Point 3 :=
    (Homeomorph.smul
      (isUnit_iff_ne_zero.2 (inv_ne_zero hδ.ne')).unit).toMeasurableEquiv
  have he_apply : ∀ x : Point 3, e x = δ⁻¹ • x := by
    intro x
    rfl
  have hmap : Measure.map e volume = ENNReal.ofReal (δ ^ 3) • volume := by
    change Measure.map (δ⁻¹ • ·) volume = _
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hδ.ne')]
    have hfinrank : Module.finrank ℝ (Point 3) = 3 :=
      finrank_euclideanSpace_fin
    rw [hfinrank, inv_pow, inv_inv, abs_of_pos (pow_pos hδ 3)]
  calc
    (∫⁻ x : Point 3, f x ∂volume) =
        ∫⁻ x : Point 3, f (δ • e x) ∂volume := by
          apply lintegral_congr
          intro x
          rw [he_apply]
          simp [hδ.ne']
    _ = ∫⁻ y : Point 3, f (δ • y) ∂Measure.map e volume := by
          exact
            (MeasureTheory.lintegral_map_equiv
              (fun y : Point 3 => f (δ • y)) e).symm
    _ = ∫⁻ y : Point 3, f (δ • y)
          ∂(ENNReal.ofReal (δ ^ 3) • volume) := by
          rw [hmap]
    _ = ENNReal.ofReal (δ ^ 3) *
        ∫⁻ y : Point 3, f (δ • y) ∂volume := by
          rw [lintegral_smul_measure]
          rfl

private lemma scaling_rhs_identity (C N : ENNReal)
    {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ 3) *
        (C * (N * N * N) ^ (1 / 2 : ℝ)) =
      C * (ENNReal.ofReal (δ ^ 2) * N) ^ (3 / 2 : ℝ) := by
  have hδ0 : 0 ≤ δ := hδ.le
  rw [ENNReal.ofReal_pow hδ0 3, ENNReal.ofReal_pow hδ0 2]
  rw [ENNReal.mul_rpow_of_nonneg _ _
    (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hD : ((ENNReal.ofReal δ) ^ 2 : ENNReal) ^ (3 / 2 : ℝ) =
      (ENNReal.ofReal δ) ^ 3 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hN : (N * N * N) ^ (1 / 2 : ℝ) =
      N ^ (3 / 2 : ℝ) := by
    rw [show N * N * N = N ^ 3 by ring]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hD, hN]
  ring

private lemma scaled_deltaTube_multiplicity_le {δ : ℝ} (hδ : 0 < δ)
    (F : Kakeya.Streamlined.TubeFamily δ) (y : Point 3) :
    deltaTubeTrilinearMultiplicity F (δ • y) ≤
      unitScaleTrilinearMultiplicity
        { card := F.card
          base := fun i => δ⁻¹ • (F.tube i).base
          direction := fun i => (F.tube i).direction
          direction_unit := fun i => (F.tube i).direction_unit }
        { card := F.card
          base := fun i => δ⁻¹ • (F.tube i).base
          direction := fun i => (F.tube i).direction
          direction_unit := fun i => (F.tube i).direction_unit }
        { card := F.card
          base := fun i => δ⁻¹ • (F.tube i).base
          direction := fun i => (F.tube i).direction
          direction_unit := fun i => (F.tube i).direction_unit }
        y := by
  dsimp only [deltaTubeTrilinearMultiplicity,
    unitScaleTrilinearMultiplicity, UnitLineFamily.tube]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  have hi := deltaTube_indicator_scaled_le hδ (F.tube i) y
  have hj := deltaTube_indicator_scaled_le hδ (F.tube j) y
  have hk := deltaTube_indicator_scaled_le hδ (F.tube k) y
  gcongr

theorem deltaTube_multilinear_kakeya_scaling :
    DeltaTubeMultilinearKakeyaScalingStatement := by
  rintro ⟨C, hC, hUnit⟩
  refine ⟨C, hC, ?_⟩
  intro δ hδ _ F
  let UF : UnitLineFamily :=
    { card := F.card
      base := fun i => δ⁻¹ • (F.tube i).base
      direction := fun i => (F.tube i).direction
      direction_unit := fun i => (F.tube i).direction_unit }
  have hpoint : ∀ y : Point 3,
      (deltaTubeTrilinearMultiplicity F (δ • y)) ^ (1 / 2 : ℝ) ≤
        (unitScaleTrilinearMultiplicity UF UF UF y) ^ (1 / 2 : ℝ) := by
    intro y
    apply ENNReal.rpow_le_rpow
    · simpa [UF] using scaled_deltaTube_multiplicity_le hδ F y
    · norm_num
  calc
    (∫⁻ x : Point 3,
        (deltaTubeTrilinearMultiplicity F x) ^ (1 / 2 : ℝ) ∂volume) =
      ENNReal.ofReal (δ ^ 3) *
        ∫⁻ y : Point 3,
          (deltaTubeTrilinearMultiplicity F (δ • y)) ^
            (1 / 2 : ℝ) ∂volume :=
            lintegral_eq_ofReal_cube_mul_lintegral_comp_smul _ hδ
    _ ≤ ENNReal.ofReal (δ ^ 3) *
        ∫⁻ y : Point 3,
          (unitScaleTrilinearMultiplicity UF UF UF y) ^
            (1 / 2 : ℝ) ∂volume :=
          mul_le_mul_right (lintegral_mono hpoint) _
    _ ≤ ENNReal.ofReal (δ ^ 3) *
        (C * ((F.enncard * F.enncard * F.enncard) ^
          (1 / 2 : ℝ))) := by
          apply mul_le_mul_right
          simpa [UF, Kakeya.Streamlined.TubeFamily.enncard] using
            hUnit UF UF UF
    _ = C * (ENNReal.ofReal (δ ^ 2) * F.enncard) ^
        (3 / 2 : ℝ) :=
      scaling_rhs_identity C F.enncard hδ

end Kakeya.CV
