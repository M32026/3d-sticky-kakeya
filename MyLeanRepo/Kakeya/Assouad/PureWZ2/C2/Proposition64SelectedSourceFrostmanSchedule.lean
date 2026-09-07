import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64SelectedSourceFrostman
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Pre-runtime selected-source Frostman absorption for Proposition 6.4

The selected short slab has total height `delta^(3 * epsilon₂)` and density
loss `5 * epsilon₂`.  Together with a source input loss at most `epsilon₂`,
the inverse selected-source weight costs at most `delta^(-9 * epsilon₂)`.
This file absorbs the remaining fixed paper-carrier constant before the
runtime scale and family are selected.
-/

noncomputable section

namespace Kakeya.Assouad

open PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

/-- The fixed coefficient left after expanding the exact short-slab weight. -/
noncomputable def pureWZ2Proposition64SelectedSourceFrostmanCoefficient :
    ENNReal :=
  3200 * (6 * selectedSourceRetention)

theorem pureWZ2Proposition64SelectedSourceFrostmanCoefficient_ne_top :
    pureWZ2Proposition64SelectedSourceFrostmanCoefficient ≠ ⊤ := by
  unfold pureWZ2Proposition64SelectedSourceFrostmanCoefficient
    selectedSourceRetention
  exact ENNReal.mul_ne_top (by norm_num) <|
    ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.mul_ne_top (by norm_num) <|
        ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top

/-- One cutoff, selected before runtime data, paying the exact inverse weight
of the paper's short-slab source selection. -/
structure PureWZ2Proposition64SelectedSourceFrostmanSchedule
    (levelCount : ℕ) (epsilon₂ densityLoss workLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorption :
    ∀ {sourceDelta inputLoss halfHeight : ℝ},
      0 < sourceDelta → sourceDelta ≤ delta₀ →
      inputLoss ≤ epsilon₂ →
      halfHeight =
        pureWZ2Proposition64HalfHeight sourceDelta levelCount →
      3200 *
          ((ENNReal.ofReal (2 * halfHeight) *
                (ENNReal.ofReal (1 / 6) *
                  Kakeya.realRpowENN sourceDelta densityLoss))⁻¹ *
              selectedSourceRetention *
            Kakeya.realRpowENN sourceDelta (-inputLoss)) ≤
        Kakeya.realRpowENN sourceDelta (-workLoss)

/-- Choose the selected-source cutoff after the losses and hierarchy depth,
but before the runtime source scale or hierarchy witness. -/
theorem exists_pureWZ2Proposition64SelectedSourceFrostmanSchedule
    {levelCount : ℕ} {epsilon₂ densityLoss workLoss : ℝ}
    (hlevelCount : 0 < levelCount)
    (hepsilon₂ : 0 < epsilon₂)
    (hepsilon₂_eq : epsilon₂ = 1 / (levelCount : ℝ))
    (hdensityLoss : densityLoss = 5 * epsilon₂)
    (hbudget : 10 * epsilon₂ < workLoss) :
    Nonempty (PureWZ2Proposition64SelectedSourceFrostmanSchedule
      levelCount epsilon₂ densityLoss workLoss) := by
  let gap := workLoss - 9 * epsilon₂
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith
  rcases exists_delta_realRpowENN_bound
      pureWZ2Proposition64SelectedSourceFrostmanCoefficient
      pureWZ2Proposition64SelectedSourceFrostmanCoefficient_ne_top hgap with
    ⟨delta₀, hdelta₀, hdelta₀One, hconstant⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := hdelta₀
    delta₀_le_one := hdelta₀One
    absorption := ?_ }⟩
  intro sourceDelta inputLoss halfHeight hsourceDelta hsourceSmall
    hinputLoss hhalfHeight
  have hsourceOne : sourceDelta ≤ 1 :=
    hsourceSmall.trans hdelta₀One
  have hhalfHeightExpanded :
      ENNReal.ofReal (2 * halfHeight) =
        Kakeya.realRpowENN sourceDelta (3 * epsilon₂) := by
    rw [hhalfHeight]
    unfold pureWZ2Proposition64HalfHeight
    have hNreal : (0 : ℝ) < (levelCount : ℝ) := by exact_mod_cast hlevelCount
    have hexponent : 3 / (levelCount : ℝ) = 3 * epsilon₂ := by
      rw [hepsilon₂_eq]
      field_simp
    rw [show 2 * (Real.rpow sourceDelta (3 / (levelCount : ℝ)) / 2) =
        Real.rpow sourceDelta (3 / (levelCount : ℝ)) by ring, hexponent]
    rfl
  have hsixth : (ENNReal.ofReal (1 / 6 : ℝ))⁻¹ = 6 := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
    norm_num
  have hrpowInv : ∀ exponent : ℝ,
      (Kakeya.realRpowENN sourceDelta exponent)⁻¹ =
        Kakeya.realRpowENN sourceDelta (-exponent) := by
    intro exponent
    simp only [Kakeya.realRpowENN]
    have hpositive : 0 < Real.rpow sourceDelta exponent :=
      Real.rpow_pos_of_pos hsourceDelta _
    calc
      (ENNReal.ofReal (Real.rpow sourceDelta exponent))⁻¹ =
          ENNReal.ofReal ((Real.rpow sourceDelta exponent)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos hpositive).symm
      _ = ENNReal.ofReal (Real.rpow sourceDelta (-exponent)) := by
        exact congrArg ENNReal.ofReal
          (Real.rpow_neg hsourceDelta.le exponent).symm
  have hhalfHeightZero : ENNReal.ofReal (2 * halfHeight) ≠ 0 := by
    rw [hhalfHeightExpanded]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hsourceDelta _)).ne'
  have hweightInv :
      (ENNReal.ofReal (2 * halfHeight) *
          (ENNReal.ofReal (1 / 6) *
            Kakeya.realRpowENN sourceDelta densityLoss))⁻¹ =
        6 * Kakeya.realRpowENN sourceDelta
          (-(3 * epsilon₂ + densityLoss)) := by
    rw [ENNReal.mul_inv (Or.inl hhalfHeightZero)
        (Or.inl ENNReal.ofReal_ne_top),
      ENNReal.mul_inv (Or.inl (by norm_num))
        (Or.inl ENNReal.ofReal_ne_top),
      hhalfHeightExpanded, hsixth, hrpowInv, hrpowInv]
    calc
      Kakeya.realRpowENN sourceDelta (-(3 * epsilon₂)) *
          (6 * Kakeya.realRpowENN sourceDelta (-densityLoss)) =
        6 * (Kakeya.realRpowENN sourceDelta (-(3 * epsilon₂)) *
          Kakeya.realRpowENN sourceDelta (-densityLoss)) := by ring
      _ = 6 * Kakeya.realRpowENN sourceDelta
          (-(3 * epsilon₂ + densityLoss)) := by
        rw [← realRpowENN_add hsourceDelta]
        congr 2
        ring
  have hdensityExponent : 3 * epsilon₂ + densityLoss = 8 * epsilon₂ := by
    rw [hdensityLoss]
    ring
  have hvariablePower :
      Kakeya.realRpowENN sourceDelta
          (-(3 * epsilon₂ + densityLoss)) *
          Kakeya.realRpowENN sourceDelta (-inputLoss) ≤
        Kakeya.realRpowENN sourceDelta (-9 * epsilon₂) := by
    rw [← realRpowENN_add hsourceDelta, hdensityExponent]
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hsourceDelta hsourceOne (by linarith)
  have hconstantBound := hconstant sourceDelta hsourceDelta hsourceSmall
  rw [hweightInv]
  calc
    3200 *
          (6 * Kakeya.realRpowENN sourceDelta
              (-(3 * epsilon₂ + densityLoss)) *
            selectedSourceRetention *
            Kakeya.realRpowENN sourceDelta (-inputLoss)) =
        pureWZ2Proposition64SelectedSourceFrostmanCoefficient *
          (Kakeya.realRpowENN sourceDelta
              (-(3 * epsilon₂ + densityLoss)) *
            Kakeya.realRpowENN sourceDelta (-inputLoss)) := by
      unfold pureWZ2Proposition64SelectedSourceFrostmanCoefficient
      ring
    _ ≤ pureWZ2Proposition64SelectedSourceFrostmanCoefficient *
          Kakeya.realRpowENN sourceDelta (-9 * epsilon₂) := by gcongr
    _ ≤ Kakeya.realRpowENN sourceDelta (-gap) *
          Kakeya.realRpowENN sourceDelta (-9 * epsilon₂) := by gcongr
    _ = Kakeya.realRpowENN sourceDelta (-workLoss) := by
      rw [← realRpowENN_add hsourceDelta]
      congr 2
      dsimp only [gap]
      ring

end Kakeya.Assouad

end
