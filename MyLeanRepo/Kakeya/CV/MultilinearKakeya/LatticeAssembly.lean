import MyLeanRepo.Kakeya.CV.MultilinearKakeya
import MyLeanRepo.Kakeya.CV.Targets.PreliminaryReduction
import MyLeanRepo.Kakeya.CV.Targets.UnitCubeEllipsoidPacking.VolumeLemmas
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Assemble finite lattice-cube estimates into the unit-scale theorem

This module contains the discrete-to-continuous part of CV Proposition 2.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators NNReal

namespace Kakeya.CV

lemma mem_lattice_unitCube (x : Point 3) :
    ∃ q : UnitLatticeCube, x ∈ unitCube (latticeCubeCenter q) := by
  let q : UnitLatticeCube := fun i => ⌊x i + 1 / 2⌋
  refine ⟨q, ?_⟩
  intro i
  have hlow : (q i : ℝ) ≤ x i + 1 / 2 := Int.floor_le _
  have hhigh : x i + 1 / 2 < (q i : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hcoord : latticeCubeCenter q i = (q i : ℝ) := by
    simp [latticeCubeCenter]
  rw [hcoord, abs_le]
  constructor <;> linarith

lemma iUnion_lattice_unitCube :
    (⋃ q : UnitLatticeCube, unitCube (latticeCubeCenter q)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases mem_lattice_unitCube x with ⟨q, hx⟩
  exact mem_iUnion.mpr ⟨q, hx⟩

lemma unitScale_multiplicity_le_cubeWeight
    (F₁ F₂ F₃ : UnitLineFamily) (q : UnitLatticeCube)
    (x : Point 3) (hx : x ∈ unitCube (latticeCubeCenter q)) :
    unitScaleTrilinearMultiplicity F₁ F₂ F₃ x ≤
      (↑(∑ i, ∑ j, ∑ k,
        unitScaleCubeWeight F₁ F₂ F₃ q i j k) : ENNReal) := by
  dsimp only [unitScaleTrilinearMultiplicity]
  push_cast
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  by_cases hi : x ∈ F₁.tube i
  · have hmeet1 : unitLineMeetsLatticeCube F₁ i q := ⟨x, hi, hx⟩
    by_cases hj : x ∈ F₂.tube j
    · have hmeet2 : unitLineMeetsLatticeCube F₂ j q := ⟨x, hj, hx⟩
      by_cases hk : x ∈ F₃.tube k
      · have hmeet3 : unitLineMeetsLatticeCube F₃ k q := ⟨x, hk, hx⟩
        simp [setIndicator, hi, hj, hk, unitScaleCubeWeight,
          hmeet1, hmeet2, hmeet3, tripleVolumeNNReal,
          Real.toNNReal_of_nonneg (abs_nonneg _), tripleVolume]
      · simp [setIndicator, hk]
    · simp [setIndicator, hj]
  · simp [setIndicator, hi]

lemma unitScale_cube_lintegral_le
    (F₁ F₂ F₃ : UnitLineFamily) (q : UnitLatticeCube) :
    (∫⁻ x : Point 3 in unitCube (latticeCubeCenter q),
        (unitScaleTrilinearMultiplicity F₁ F₂ F₃ x) ^ (1 / 2 : ℝ)
      ∂volume) ≤
      (↑(∑ i, ∑ j, ∑ k,
        unitScaleCubeWeight F₁ F₂ F₃ q i j k) : ENNReal) ^
          (1 / 2 : ℝ) := by
  calc
    _ ≤ ∫⁻ _x : Point 3 in unitCube (latticeCubeCenter q),
        (↑(∑ i, ∑ j, ∑ k,
          unitScaleCubeWeight F₁ F₂ F₃ q i j k) : ENNReal) ^
            (1 / 2 : ℝ) ∂volume := by
      apply setLIntegral_mono measurable_const
      intro x hx
      exact ENNReal.rpow_le_rpow
        (unitScale_multiplicity_le_cubeWeight F₁ F₂ F₃ q x hx)
        (by norm_num)
    _ = (↑(∑ i, ∑ j, ∑ k,
        unitScaleCubeWeight F₁ F₂ F₃ q i j k) : ENNReal) ^
          (1 / 2 : ℝ) * volume (unitCube (latticeCubeCenter q)) := by
      rw [setLIntegral_const]
    _ = _ := by rw [volume_unitCube]; simp

lemma finite_lattice_cube_sqrt_sum_le
    (hPreliminary : PreliminaryReductionStatement.{0, 0, 0, 0})
    (hFactorization : UnitScaleLatticeFactorizationStatement) :
    ∃ A : NNReal, 0 < A ∧
      ∀ F₁ F₂ F₃ : UnitLineFamily,
        ∀ cubes : Finset UnitLatticeCube,
          (∑ q : cubes,
              NNReal.sqrt
                (∑ i, ∑ j, ∑ k,
                  unitScaleCubeWeight F₁ F₂ F₃ q.1 i j k)) ≤
            NNReal.sqrt A *
              NNReal.sqrt
                ((F₁.card * F₂.card * F₃.card : ℕ) : NNReal) := by
  rcases hFactorization with ⟨A, hA, hFactorization⟩
  refine ⟨A, hA, ?_⟩
  intro F₁ F₂ F₃ cubes
  let weight :
      cubes → Fin F₁.card → Fin F₂.card → Fin F₃.card → NNReal :=
    fun q i j k => A⁻¹ * unitScaleCubeWeight F₁ F₂ F₃ q.1 i j k
  have hnormalized :
      ∀ M : cubes → NNReal, (∑ q, M q ^ 3) = 1 →
        ∃ (S₁ : cubes → Fin F₁.card → NNReal)
            (S₂ : cubes → Fin F₂.card → NNReal)
            (S₃ : cubes → Fin F₃.card → NNReal),
          (∀ q i j k,
            weight q i j k * M q ^ 3 ≤
              S₁ q i * S₂ q j * S₃ q k) ∧
          (∀ i, ∑ q, S₁ q i ≤ 1) ∧
          (∀ j, ∑ q, S₂ q j ≤ 1) ∧
          (∀ k, ∑ q, S₃ q k ≤ 1) := by
    intro M hM
    simpa [weight] using hFactorization F₁ F₂ F₃ cubes M hM
  have hpre := hPreliminary cubes (Fin F₁.card) (Fin F₂.card)
    (Fin F₃.card) weight hnormalized
  have hsqrtA : 0 < NNReal.sqrt A := NNReal.sqrt_pos.mpr hA
  have hsqrt : ∀ W : NNReal,
      NNReal.sqrt W = NNReal.sqrt A * NNReal.sqrt (A⁻¹ * W) := by
    intro W
    rw [NNReal.sqrt_mul, NNReal.sqrt_inv]
    calc
      NNReal.sqrt W =
          (NNReal.sqrt A * (NNReal.sqrt A)⁻¹) * NNReal.sqrt W := by
            rw [mul_inv_cancel₀ hsqrtA.ne', one_mul]
      _ = NNReal.sqrt A * ((NNReal.sqrt A)⁻¹ * NNReal.sqrt W) := by
            rw [mul_assoc]
  calc
    (∑ q : cubes,
        NNReal.sqrt
          (∑ i, ∑ j, ∑ k,
            unitScaleCubeWeight F₁ F₂ F₃ q.1 i j k)) =
      NNReal.sqrt A *
        ∑ q : cubes,
          NNReal.sqrt
            (∑ i, ∑ j, ∑ k, weight q i j k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [hsqrt]
        congr 2
        simp [weight, Finset.mul_sum]
    _ ≤ NNReal.sqrt A *
        NNReal.sqrt
          ((Fintype.card (Fin F₁.card) * Fintype.card (Fin F₂.card) *
            Fintype.card (Fin F₃.card) : ℕ) : NNReal) := by
      gcongr
    _ = NNReal.sqrt A *
        NNReal.sqrt
          ((F₁.card * F₂.card * F₃.card : ℕ) : NNReal) := by simp

theorem unitScale_multilinear_kakeya_of_lattice_factorization
    (hPreliminary : PreliminaryReductionStatement.{0, 0, 0, 0})
    (hFactorization : UnitScaleLatticeFactorizationStatement) :
    UnitScaleMultilinearKakeyaStatement := by
  rcases finite_lattice_cube_sqrt_sum_le hPreliminary hFactorization with
    ⟨A, hA, hfinite⟩
  refine ⟨(NNReal.sqrt A : ENNReal), by simp, ?_⟩
  intro F₁ F₂ F₃
  let cubeBound : UnitLatticeCube → NNReal := fun q =>
    NNReal.sqrt
      (∑ i, ∑ j, ∑ k, unitScaleCubeWeight F₁ F₂ F₃ q i j k)
  have hfinite' : ∀ cubes : Finset UnitLatticeCube,
      ∑ q ∈ cubes, (cubeBound q : ENNReal) ≤
        ((NNReal.sqrt A *
          NNReal.sqrt
            ((F₁.card * F₂.card * F₃.card : ℕ) : NNReal) : NNReal) :
              ENNReal) := by
    intro cubes
    have h := hfinite F₁ F₂ F₃ cubes
    have h' :
        ∑ q : cubes, cubeBound q.1 ≤
          NNReal.sqrt A *
            NNReal.sqrt
              ((F₁.card * F₂.card * F₃.card : ℕ) : NNReal) := by
      simpa [cubeBound] using h
    have hsum :
        (∑ q : cubes, cubeBound q.1) =
          ∑ q ∈ cubes, cubeBound q := by
      rw [← cubes.sum_attach cubeBound, Finset.attach_eq_univ]
    calc
      ∑ q ∈ cubes, (cubeBound q : ENNReal) =
          (↑(∑ q ∈ cubes, cubeBound q) : ENNReal) := by
            simp
      _ = (↑(∑ q : cubes, cubeBound q.1) : ENNReal) := by
            rw [hsum]
      _ ≤ ↑(NNReal.sqrt A *
          NNReal.sqrt
            ((F₁.card * F₂.card * F₃.card : ℕ) : NNReal)) :=
        ENNReal.coe_le_coe.mpr h'
  have htsum :
      ∑' q : UnitLatticeCube, (cubeBound q : ENNReal) ≤
        ((NNReal.sqrt A *
          NNReal.sqrt
            ((F₁.card * F₂.card * F₃.card : ℕ) : NNReal) : NNReal) :
              ENNReal) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    exact hfinite'
  calc
    (∫⁻ x : Point 3,
        (unitScaleTrilinearMultiplicity F₁ F₂ F₃ x) ^ (1 / 2 : ℝ)
      ∂volume) =
      ∫⁻ x : Point 3 in
        (⋃ q : UnitLatticeCube, unitCube (latticeCubeCenter q)),
        (unitScaleTrilinearMultiplicity F₁ F₂ F₃ x) ^ (1 / 2 : ℝ)
      ∂volume := by rw [iUnion_lattice_unitCube, setLIntegral_univ]
    _ ≤ ∑' q : UnitLatticeCube,
        ∫⁻ x : Point 3 in unitCube (latticeCubeCenter q),
          (unitScaleTrilinearMultiplicity F₁ F₂ F₃ x) ^ (1 / 2 : ℝ)
        ∂volume :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' q : UnitLatticeCube, (cubeBound q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro q
      simpa [cubeBound, NNReal.sqrt_eq_rpow,
        ENNReal.coe_rpow_of_nonneg] using
        unitScale_cube_lintegral_le F₁ F₂ F₃ q
    _ ≤ ((NNReal.sqrt A *
        NNReal.sqrt
          ((F₁.card * F₂.card * F₃.card : ℕ) : NNReal) : NNReal) :
            ENNReal) := htsum
    _ = (NNReal.sqrt A : ENNReal) *
        ((F₁.card : ENNReal) * (F₂.card : ENNReal) *
          (F₃.card : ENNReal)) ^ (1 / 2 : ℝ) := by
      simp [NNReal.sqrt_eq_rpow, ENNReal.coe_rpow_of_nonneg,
        Nat.cast_mul]

end Kakeya.CV
