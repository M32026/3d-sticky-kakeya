import MyLeanRepo.Kakeya.Assouad.CoveringInfrastructure
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Global AD-set measure bounds for the WZ2 large-slope argument

This module converts the external covering-number convention in `IsADSet1`
to one-dimensional Lebesgue-measure bounds.
-/

noncomputable section

open MeasureTheory Set Metric

namespace Kakeya.Assouad

/--
An external cover of a subset of `ℝ` by radius-`delta` balls bounds its
Lebesgue measure by `2 delta` times the external covering number.
-/
lemma volume_le_externalCoveringNumber_mul_two_delta
    {E : Set ℝ} {delta : ℝ} (hdelta : 0 < delta)
    {N : ENNReal} (hN : N ≠ ⊤)
    (hcover :
      (↑(Metric.externalCoveringNumber ⟨delta, hdelta.le⟩ E) : ENNReal) ≤ N) :
    MeasureTheory.volume E ≤ N * ENNReal.ofReal (2 * delta) := by
  have hfinite :
      Metric.externalCoveringNumber ⟨delta, hdelta.le⟩ E ≠ ⊤ := by
    intro htop
    rw [htop] at hcover
    exact hN (top_le_iff.mp hcover)
  obtain ⟨centers, hcenters_finite, hcenters_cover, hcenters_card⟩ :=
    exists_set_encard_eq_externalCoveringNumber hfinite
  let centersFinset : Finset ℝ := hcenters_finite.toFinset
  have hsubset :
      E ⊆ ⋃ x ∈ centersFinset, Metric.closedBall x delta := by
    intro y hy
    have hy_cover := hcenters_cover.subset_iUnion_closedBall hy
    simp only [Set.mem_iUnion] at hy_cover
    obtain ⟨x, hx_centers, hy_ball⟩ := hy_cover
    have hx_finset : x ∈ centersFinset := by
      have : x ∈ (centersFinset : Set ℝ) := by
        simpa [centersFinset, hcenters_finite.coe_toFinset] using hx_centers
      exact this
    have hy_dist : dist y x ≤ delta := by
      exact_mod_cast hy_ball
    exact Set.mem_iUnion₂.mpr
      ⟨x, hx_finset, by simpa [Metric.mem_closedBall] using hy_dist⟩
  have hvolume :
      MeasureTheory.volume E ≤
        ∑ x ∈ centersFinset,
          MeasureTheory.volume (Metric.closedBall x delta) := by
    exact (MeasureTheory.measure_mono hsubset).trans
      (MeasureTheory.measure_biUnion_finset_le centersFinset
        (fun x => Metric.closedBall x delta))
  have hcard_enat :
      (↑centersFinset.card : ℕ∞) =
        Metric.externalCoveringNumber ⟨delta, hdelta.le⟩ E := by
    calc
      (↑centersFinset.card : ℕ∞)
          = centers.encard := by
              simpa [centersFinset] using
                hcenters_finite.encard_eq_coe_toFinset_card.symm
      _ = Metric.externalCoveringNumber
          ⟨delta, hdelta.le⟩ E := hcenters_card
  have hcard :
      (centersFinset.card : ENNReal) =
        (↑(Metric.externalCoveringNumber
          ⟨delta, hdelta.le⟩ E) : ENNReal) := by
    exact_mod_cast hcard_enat
  calc
    MeasureTheory.volume E
        ≤ ∑ x ∈ centersFinset,
          MeasureTheory.volume (Metric.closedBall x delta) := hvolume
    _ = ∑ _x ∈ centersFinset, ENNReal.ofReal (2 * delta) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Real.volume_closedBall]
    _ = (centersFinset.card : ENNReal) *
        ENNReal.ofReal (2 * delta) := by simp
    _ = (↑(Metric.externalCoveringNumber
          ⟨delta, hdelta.le⟩ E) : ENNReal) *
        ENNReal.ofReal (2 * delta) := by rw [hcard]
    _ ≤ N * ENNReal.ofReal (2 * delta) := by
          exact mul_le_mul_right' hcover _

/--
An `IsADSet1 E delta (1-sigma) C` set has one-dimensional measure at most
`8 C delta^sigma`.
-/
lemma IsADSet1.volume_le
    {E : Set ℝ} {delta sigma : ℝ} {C : ENNReal}
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hC_top : C ≠ ⊤)
    (hAD : IsADSet1 E delta (1 - sigma) C) :
    MeasureTheory.volume E ≤
      8 * C * Kakeya.realRpowENN delta sigma := by
  rcases hAD with
    ⟨_, _halpha, _halpha_one, hC_one, hE_bounded, hAD_cover⟩
  let centers : Finset ℝ := {-3, -1, 1, 3}
  have hinterval_cover :
      Set.Icc (-4 : ℝ) 4 ⊆
        ⋃ c ∈ centers, Metric.closedBall c 1 := by
    intro x hx
    by_cases hx₁ : x ≤ -2
    · exact Set.mem_iUnion₂.mpr
        ⟨-3, by simp [centers], by
          rw [Metric.mem_closedBall, Real.dist_eq]
          apply abs_le.mpr
          constructor <;> linarith [hx.1]⟩
    · by_cases hx₂ : x ≤ 0
      · exact Set.mem_iUnion₂.mpr
          ⟨-1, by simp [centers], by
            rw [Metric.mem_closedBall, Real.dist_eq]
            apply abs_le.mpr
            constructor <;> linarith⟩
      · by_cases hx₃ : x ≤ 2
        · exact Set.mem_iUnion₂.mpr
            ⟨1, by simp [centers], by
              rw [Metric.mem_closedBall, Real.dist_eq]
              apply abs_le.mpr
              constructor <;> linarith⟩
        · exact Set.mem_iUnion₂.mpr
            ⟨3, by simp [centers], by
              rw [Metric.mem_closedBall, Real.dist_eq]
              apply abs_le.mpr
              constructor <;> linarith [hx.2]⟩
  have hE_cover :
      E ⊆ ⋃ c ∈ centers, E ∩ Metric.closedBall c 1 := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hinterval_cover (hE_bounded hx)) with
      ⟨c, hc, hxc⟩
    exact Set.mem_iUnion₂.mpr ⟨c, hc, hx, hxc⟩
  have hpiece :
      ∀ c ∈ centers,
        MeasureTheory.volume (E ∩ Metric.closedBall c 1) ≤
          2 * C * Kakeya.realRpowENN delta sigma := by
    intro c _
    by_cases hdelta_one : delta ≤ 1
    · have hcover :
          (↑(Metric.externalCoveringNumber ⟨delta, hdelta.le⟩
            (E ∩ Metric.closedBall c 1)) : ENNReal) ≤
            C * Kakeya.realRpowENN (1 / delta) (1 - sigma) :=
        hAD_cover delta hdelta.le le_rfl hdelta_one c 1
          (by linarith) le_rfl
      have hN_top :
          C * Kakeya.realRpowENN (1 / delta) (1 - sigma) ≠ ⊤ :=
        ENNReal.mul_ne_top hC_top (by simp [Kakeya.realRpowENN])
      have hvolume :=
        volume_le_externalCoveringNumber_mul_two_delta hdelta hN_top hcover
      have hrpow :
          Kakeya.realRpowENN (1 / delta) (1 - sigma) *
              ENNReal.ofReal (2 * delta) =
            2 * Kakeya.realRpowENN delta sigma := by
        simp only [Kakeya.realRpowENN]
        have hleft :
            Real.rpow (1 / delta) (1 - sigma) *
                (2 * delta) =
              2 * Real.rpow delta sigma := by
          have hinv :
              Real.rpow (1 / delta) (1 - sigma) =
                (Real.rpow delta (1 - sigma))⁻¹ := by
            rw [show 1 / delta = delta⁻¹ by field_simp]
            exact Real.inv_rpow hdelta.le (1 - sigma)
          rw [hinv]
          have hadd :=
            Real.rpow_add hdelta (-(1 - sigma)) 1
          rw [Real.rpow_one] at hadd
          have hexp : -(1 - sigma) + 1 = sigma := by ring
          rw [hexp] at hadd
          have hneg :
              (Real.rpow delta (1 - sigma))⁻¹ =
                Real.rpow delta (-(1 - sigma)) :=
            (Real.rpow_neg hdelta.le (1 - sigma)).symm
          calc
            (Real.rpow delta (1 - sigma))⁻¹ * (2 * delta)
                = 2 * (Real.rpow delta (-(1 - sigma)) * delta) := by
                    rw [hneg]
                    ring
            _ = 2 * Real.rpow delta sigma :=
              congrArg (fun x : ℝ => 2 * x) hadd.symm
        have hnonneg :
            0 ≤ Real.rpow (1 / delta) (1 - sigma) :=
          Real.rpow_nonneg (by positivity) _
        rw [← ENNReal.ofReal_mul hnonneg, hleft]
        simp
      calc
        MeasureTheory.volume (E ∩ Metric.closedBall c 1)
            ≤ (C * Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
                ENNReal.ofReal (2 * delta) := hvolume
        _ = C *
            (Kakeya.realRpowENN (1 / delta) (1 - sigma) *
              ENNReal.ofReal (2 * delta)) := by ring
        _ = C * (2 * Kakeya.realRpowENN delta sigma) := by rw [hrpow]
        _ = 2 * C * Kakeya.realRpowENN delta sigma := by ring
    · have hvolume :
          MeasureTheory.volume (E ∩ Metric.closedBall c 1) ≤ 2 := by
        calc
          MeasureTheory.volume (E ∩ Metric.closedBall c 1)
              ≤ MeasureTheory.volume (Metric.closedBall c 1) :=
                MeasureTheory.measure_mono Set.inter_subset_right
          _ = 2 := by simp [Real.volume_closedBall]
      have hdelta_ge : 1 ≤ delta := le_of_not_ge hdelta_one
      have hrpow_one :
          (1 : ENNReal) ≤ Kakeya.realRpowENN delta sigma := by
        simp only [Kakeya.realRpowENN]
        have hreal : (1 : ℝ) ≤ Real.rpow delta sigma :=
          Real.one_le_rpow hdelta_ge hsigma.le
        simpa using ENNReal.ofReal_mono hreal
      calc
        MeasureTheory.volume (E ∩ Metric.closedBall c 1) ≤ 2 := hvolume
        _ = 2 * 1 * 1 := by norm_num
        _ ≤ 2 * C * Kakeya.realRpowENN delta sigma := by gcongr
  calc
    MeasureTheory.volume E
        ≤ ∑ c ∈ centers,
          MeasureTheory.volume (E ∩ Metric.closedBall c 1) := by
          exact (MeasureTheory.measure_mono hE_cover).trans
            (MeasureTheory.measure_biUnion_finset_le centers
              (fun c => E ∩ Metric.closedBall c 1))
    _ ≤ ∑ _c ∈ centers,
          (2 * C * Kakeya.realRpowENN delta sigma) := by
          exact Finset.sum_le_sum fun c hc => hpiece c hc
    _ = (centers.card : ENNReal) *
        (2 * C * Kakeya.realRpowENN delta sigma) := by simp
    _ = 8 * C * Kakeya.realRpowENN delta sigma := by
          have hcard : centers.card = 4 := by
            norm_num [centers]
          rw [hcard]
          norm_num
          ring

/--
If a planar set is contained in the radius-`R` Euclidean disk and `v` is a
unit vector, its area is at most `2 R` times the measure of its projection
onto `v`.
-/
lemma area_le_two_projection {S : Set (Fin 2 → ℝ)} {v : Fin 2 → ℝ}
    (hv : v 0 ^ 2 + v 1 ^ 2 = 1) {R : ℝ} (hR : 0 ≤ R)
    (hS : ∀ x ∈ S, x 0 ^ 2 + x 1 ^ 2 ≤ R ^ 2) :
    volume S ≤
      ENNReal.ofReal (2 * R) *
        volume ((fun x : Fin 2 → ℝ => x 0 * v 0 + x 1 * v 1) '' S) := by
  let basis : Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
    Pi.basisFun ℝ (Fin 2)
  let matrix : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![v 0, v 1], ![-v 1, v 0]]
  let rotate : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    Matrix.toLin basis basis matrix

  have hmatrix00 : matrix 0 0 = v 0 := by simp [matrix]
  have hmatrix01 : matrix 0 1 = v 1 := by simp [matrix]
  have hmatrix10 : matrix 1 0 = -v 1 := by simp [matrix]
  have hmatrix11 : matrix 1 1 = v 0 := by simp [matrix]
  have hdet : LinearMap.det rotate = 1 := by
    have h : LinearMap.det rotate = matrix.det :=
      LinearMap.det_toLin basis matrix
    rw [h, Matrix.det_fin_two, hmatrix00, hmatrix11,
      hmatrix01, hmatrix10]
    nlinarith

  have hbasis0 : basis 0 = ![1, 0] := by
    simp [basis, Pi.basisFun]
    ext i
    fin_cases i <;> simp
  have hbasis1 : basis 1 = ![0, 1] := by
    simp [basis, Pi.basisFun]
    ext i
    fin_cases i <;> simp
  have hbasis00 : (basis 0) 0 = 1 := by rw [hbasis0] <;> simp
  have hbasis01 : (basis 0) 1 = 0 := by rw [hbasis0] <;> simp
  have hbasis10 : (basis 1) 0 = 0 := by rw [hbasis1] <;> simp
  have hbasis11 : (basis 1) 1 = 1 := by rw [hbasis1] <;> simp

  have hrotate_basis0 : rotate (basis 0) = ![v 0, -v 1] := by
    have hsum :
        rotate (basis 0) =
          matrix 0 0 • basis 0 + matrix 1 0 • basis 1 := by
      rw [Matrix.toLin_self basis basis matrix 0, Fin.sum_univ_two]
    rw [hsum, hmatrix00, hmatrix10, hbasis0, hbasis1]
    ext i
    fin_cases i <;> simp [hbasis0, hbasis1] <;> ring
  have hrotate_basis1 : rotate (basis 1) = ![v 1, v 0] := by
    have hsum :
        rotate (basis 1) =
          matrix 0 1 • basis 0 + matrix 1 1 • basis 1 := by
      rw [Matrix.toLin_self basis basis matrix 1, Fin.sum_univ_two]
    rw [hsum, hmatrix01, hmatrix11, hbasis0, hbasis1]
    ext i
    fin_cases i <;> simp [hbasis0, hbasis1] <;> ring
  have hrotate_basis00 : (rotate (basis 0)) 0 = v 0 := by
    rw [hrotate_basis0]
    simp
  have hrotate_basis01 : (rotate (basis 0)) 1 = -v 1 := by
    rw [hrotate_basis0]
    simp
  have hrotate_basis10 : (rotate (basis 1)) 0 = v 1 := by
    rw [hrotate_basis1]
    simp
  have hrotate_basis11 : (rotate (basis 1)) 1 = v 0 := by
    rw [hrotate_basis1]
    simp

  have hrotate0 :
      ∀ x, (rotate x) 0 = x 0 * v 0 + x 1 * v 1 := by
    intro x
    have hx : x = x 0 • basis 0 + x 1 • basis 1 := by
      ext i
      fin_cases i <;>
        simp [hbasis00, hbasis01, hbasis10, hbasis11] <;> ring
    have h₂ : rotate x = rotate (x 0 • basis 0 + x 1 • basis 1) :=
      congrArg rotate hx
    have h₃ :
        rotate (x 0 • basis 0 + x 1 • basis 1) =
          rotate (x 0 • basis 0) + rotate (x 1 • basis 1) :=
      LinearMap.map_add rotate _ _
    have h₄ : rotate (x 0 • basis 0) = x 0 • rotate (basis 0) :=
      LinearMap.map_smul rotate _ _
    have h₅ : rotate (x 1 • basis 1) = x 1 • rotate (basis 1) :=
      LinearMap.map_smul rotate _ _
    have h₆ :
        rotate x = x 0 • rotate (basis 0) + x 1 • rotate (basis 1) := by
      rw [h₂, h₃, h₄, h₅]
    rw [h₆]
    simp [hrotate_basis00, hrotate_basis10]
  have hrotate1 :
      ∀ x, (rotate x) 1 = x 0 * (-v 1) + x 1 * v 0 := by
    intro x
    have hx : x = x 0 • basis 0 + x 1 • basis 1 := by
      ext i
      fin_cases i <;>
        simp [hbasis00, hbasis01, hbasis10, hbasis11] <;> ring
    have h₂ : rotate x = rotate (x 0 • basis 0 + x 1 • basis 1) :=
      congrArg rotate hx
    have h₃ :
        rotate (x 0 • basis 0 + x 1 • basis 1) =
          rotate (x 0 • basis 0) + rotate (x 1 • basis 1) :=
      LinearMap.map_add rotate _ _
    have h₄ : rotate (x 0 • basis 0) = x 0 • rotate (basis 0) :=
      LinearMap.map_smul rotate _ _
    have h₅ : rotate (x 1 • basis 1) = x 1 • rotate (basis 1) :=
      LinearMap.map_smul rotate _ _
    have h₆ :
        rotate x = x 0 • rotate (basis 0) + x 1 • rotate (basis 1) := by
      rw [h₂, h₃, h₄, h₅]
    rw [h₆]
    simp [hrotate_basis01, hrotate_basis11]
  have hnorm :
      ∀ x : Fin 2 → ℝ,
        (rotate x) 0 ^ 2 + (rotate x) 1 ^ 2 =
          x 0 ^ 2 + x 1 ^ 2 := by
    intro x
    rw [hrotate0 x, hrotate1 x]
    nlinarith

  have hvolume : volume (rotate '' S) = volume S := by
    have h :
        volume (rotate '' S) =
          ENNReal.ofReal |LinearMap.det rotate| * volume S :=
      MeasureTheory.Measure.addHaar_image_linearMap
        (volume : Measure (Fin 2 → ℝ)) rotate S
    rw [h, hdet]
    simp

  let projection : (Fin 2 → ℝ) → ℝ :=
    fun x => x 0 * v 0 + x 1 * v 1
  let projected : Set ℝ := projection '' S
  let coordinateSet : Fin 2 → Set ℝ :=
    fun i => if i = 0 then projected else Set.Icc (-R) R
  let box : Set (Fin 2 → ℝ) := Set.univ.pi coordinateSet

  have hrotate_subset : rotate '' S ⊆ box := by
    rintro y ⟨x, hx, rfl⟩
    have hnorm_le : (rotate x) 0 ^ 2 + (rotate x) 1 ^ 2 ≤ R ^ 2 := by
      rw [hnorm x]
      exact hS x hx
    have hsecond : |(rotate x) 1| ≤ R := by
      have hsquare : |(rotate x) 1| ^ 2 ≤ R ^ 2 := by
        simpa [sq_abs] using
          (show (rotate x) 1 ^ 2 ≤ R ^ 2 by nlinarith [sq_nonneg ((rotate x) 0)])
      nlinarith [abs_nonneg ((rotate x) 1)]
    intro i
    fin_cases i <;>
      simp [box, coordinateSet, projected, projection,
        hrotate0, hx, abs_le.mp hsecond] <;> tauto

  have hbox_volume :
      volume box =
        volume projected * volume (Set.Icc (-R) R) := by
    rw [MeasureTheory.volume_pi_pi coordinateSet, Fin.prod_univ_two]
    simp [coordinateSet]

  calc
    volume S = volume (rotate '' S) := hvolume.symm
    _ ≤ volume box := measure_mono hrotate_subset
    _ = volume projected * volume (Set.Icc (-R) R) := hbox_volume
    _ = volume projected * ENNReal.ofReal (2 * R) := by
          rw [Real.volume_Icc]
          congr 2
          ring
    _ = ENNReal.ofReal (2 * R) * volume projected := by ring

end Kakeya.Assouad
