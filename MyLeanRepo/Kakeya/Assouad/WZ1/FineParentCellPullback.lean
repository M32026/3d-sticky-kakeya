import MyLeanRepo.Kakeya.Assouad.WZ1.FineParentCellPullbackCounting
import MyLeanRepo.Kakeya.Assouad.WZ1.RestoreExtremality

/-!
# Fine parent-cell pullback for WZ1 Lemma 17

This module assembles the whole-cell pullback, the quantitative parent-cell
count, and the explicit paper scale-window absorption into the requested
fine extremal subshading.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Closed provider for the corrected fine parent-cell pullback statement.

The explicit absorption premise is the quantitative content of the outer
Lemma 17 scale window.  Smallness of `rho` alone would not imply it.
-/
theorem fineParentCellPullback_statement :
    WZ1Lemma17FineParentCellPullbackStatement := by
  intro epsilon₁ epsilon₂
    hepsilon₁ hepsilon₂ hepsilon₁₂ _hepsilonSum
  let rho₀ : ℝ := 1 / 1000
  have hrho₀Pos : 0 < rho₀ := by
    norm_num [rho₀]
  have hrho₀Upper : rho₀ ≤ 1 / 1000 := by
    rfl
  refine ⟨rho₀, hrho₀Pos, hrho₀Upper, ?_⟩
  intro delta sigma F U Y rho first propertyThree
    _hsigma _hsigmaOne hrho _hrhoSmall hpullbackAbsorb
    hpropertyThreeSub hpropertyThreeExtremal
  let fineShading :=
    fineParentCellPullbackShading first propertyThree
  let retention : ENNReal :=
    Kakeya.realRpowENN rho.1 epsilon₂ / 32000000
  have hfineSub :
      IsSubshading fineShading first.refined :=
    fineParentCellPullbackShading_subshading first propertyThree
  have hmass :
      retention * first.refined.mass ≤ fineShading.mass := by
    exact
      fineParentCellPullback_mass_retention
        first propertyThree hpropertyThreeSub
          hpropertyThreeExtremal hrho
  have hdelta : 0 < delta := first.refined_extremal.1
  let deltaPower : ENNReal :=
    Kakeya.realRpowENN delta (epsilon₂ - epsilon₁)
  have hratio :
      (2 : ENNReal) * deltaPower ≤ retention := by
    apply
      (ENNReal.le_div_iff_mul_le
        (Or.inl (by norm_num))
        (Or.inl (by norm_num))).mpr
    have hconstant :
        (2 : ENNReal) * 32000000 =
          wz1Lemma17FinePullbackAbsorptionConstant := by
      norm_num [wz1Lemma17FinePullbackAbsorptionConstant]
    calc
      ((2 : ENNReal) * deltaPower) * 32000000 =
          wz1Lemma17FinePullbackAbsorptionConstant *
            deltaPower := by
        calc
          ((2 : ENNReal) * deltaPower) * 32000000 =
              ((2 : ENNReal) * 32000000) * deltaPower := by
            simp [mul_assoc, mul_comm]
          _ = wz1Lemma17FinePullbackAbsorptionConstant *
                deltaPower := by rw [hconstant]
      _ ≤ Kakeya.realRpowENN rho.1 epsilon₂ := by
        simpa [deltaPower] using hpullbackAbsorb
  have habsorb :
      (2 * first.fineMultiplicity : ENNReal) * deltaPower ≤
        retention * (first.fineMultiplicity : ENNReal) := by
    calc
      (2 * first.fineMultiplicity : ENNReal) * deltaPower =
          ((2 : ENNReal) * deltaPower) *
            (first.fineMultiplicity : ENNReal) := by
        ring
      _ ≤ retention * (first.fineMultiplicity : ENNReal) := by
        gcongr
  have hretentionTop : retention ≠ ⊤ := by
    exact
      ENNReal.div_ne_top
        (by simp [retention, Kakeya.realRpowENN])
        (by norm_num)
  have hfineExtremal :
      WZ1ExtremalPair sigma epsilon₂ F U fineShading := by
    exact
      restore_extremality_from_mass
        (hY := first.refined_extremal)
        (h_mult := first.fine_constant_multiplicity)
        (hsub := hfineSub)
        (hmass := hmass)
        (hfine_le := hepsilon₁₂.le)
        (hm_pos := first.fineMultiplicity_pos)
        (_hL_ne_top := hretentionTop)
        (h_absorb := by
          simpa [deltaPower] using habsorb)
  exact
    ⟨{
      fineShading := fineShading
      fine_subshading := hfineSub
      fine_extremal := hfineExtremal
      fine_supported_on_propertyThree_cell :=
        fineParentCellPullbackShading_support first propertyThree
    }⟩

end Kakeya.Assouad
