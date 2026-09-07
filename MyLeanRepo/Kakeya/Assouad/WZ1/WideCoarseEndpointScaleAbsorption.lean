import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointParameterGap
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarsePreparationLemmas

/-!
# Fixed-constant absorption at the wide endpoint coarse scale
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
Turn the generic small-`tau` fixed-constant absorption into a `delta₀`
provider using the wide-branch relation

`tau = delta / width < delta^(epsilon / 10)`.
-/
lemma wideCoarseEndpoint_exists_delta_absorb_tau_constant
    (D : ENNReal) (hD : D ≠ ⊤)
    {epsilon loss targetLoss : ℝ}
    (hepsilon : 0 < epsilon)
    (hloss : 0 ≤ loss)
    (hgap : loss < targetLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta width : ℝ},
        0 < delta → delta ≤ delta₀ →
        0 < width →
        Real.rpow delta (1 - epsilon / 10) < width →
        D * Kakeya.realRpowENN
            (delta / width) (-loss) ≤
          Kakeya.realRpowENN
            (delta / width) (-targetLoss) := by
  rcases
      exists_scale_absorb_constant
        D hD hloss hgap with
    ⟨tau₀, htau₀, htau₀One, habsorb⟩
  let delta₀ : ℝ := Real.rpow tau₀ (10 / epsilon)
  have hexponent : 0 < 10 / epsilon := by
    positivity
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    exact Real.rpow_pos_of_pos htau₀ _
  have hdelta₀One : delta₀ ≤ 1 := by
    dsimp only [delta₀]
    exact Real.rpow_le_one htau₀.le htau₀One hexponent.le
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta width hdelta hdeltaSmall hwidth hwidthLarge
  have htau :
      0 < delta / width :=
    div_pos hdelta hwidth
  have htauPower :
      delta / width <
        Real.rpow delta (epsilon / 10) :=
    wideCoarseScaleBound
      hdelta hwidth hepsilon hwidthLarge
  have hpowerMonotone :
      Real.rpow delta (epsilon / 10) ≤
        Real.rpow delta₀ (epsilon / 10) :=
    Real.rpow_le_rpow
      hdelta.le hdeltaSmall (by positivity)
  have hdelta₀Power :
      Real.rpow delta₀ (epsilon / 10) = tau₀ := by
    dsimp only [delta₀]
    calc
      Real.rpow
          (Real.rpow tau₀ (10 / epsilon))
          (epsilon / 10) =
        Real.rpow tau₀
          ((10 / epsilon) * (epsilon / 10)) := by
            exact
              (Real.rpow_mul
                htau₀.le (10 / epsilon) (epsilon / 10)).symm
      _ = Real.rpow tau₀ 1 := by
            congr 1
            field_simp [hepsilon.ne']
      _ = tau₀ := by simp
  have htauSmall : delta / width ≤ tau₀ := by
    exact
      (calc
        delta / width <
            Real.rpow delta (epsilon / 10) := htauPower
        _ ≤ Real.rpow delta₀ (epsilon / 10) := hpowerMonotone
        _ = tau₀ := hdelta₀Power).le
  exact habsorb (delta / width) htau htauSmall

/--
Absorb a positive real constant between arbitrary coarse-scale powers
`tau^sourceExponent` and `tau^targetExponent`, provided the target exponent
is strictly smaller.  Unlike the loss-specialized wrapper above, this form
also retains positive powers coming from a Frostman ball radius.
-/
lemma wideCoarseEndpoint_exists_delta_absorb_tau_power
    (constant : ℝ) (hconstant : 0 < constant)
    {epsilon targetExponent sourceExponent : ℝ}
    (hepsilon : 0 < epsilon)
    (hgap : targetExponent < sourceExponent) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta width : ℝ},
        0 < delta → delta ≤ delta₀ →
        0 < width →
        Real.rpow delta (1 - epsilon / 10) < width →
        ENNReal.ofReal constant *
            Kakeya.realRpowENN
              (delta / width) sourceExponent ≤
          Kakeya.realRpowENN
            (delta / width) targetExponent := by
  rcases
      exists_delta₀_const_mul_rpow_le
        constant hconstant
        targetExponent sourceExponent hgap with
    ⟨tau₀, htau₀, htau₀One, habsorb⟩
  let delta₀ : ℝ := Real.rpow tau₀ (10 / epsilon)
  have hexponent : 0 < 10 / epsilon := by
    positivity
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    exact Real.rpow_pos_of_pos htau₀ _
  have hdelta₀One : delta₀ ≤ 1 := by
    dsimp only [delta₀]
    exact Real.rpow_le_one htau₀.le htau₀One hexponent.le
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta width hdelta hdeltaSmall hwidth hwidthLarge
  have htau :
      0 < delta / width :=
    div_pos hdelta hwidth
  have htauPower :
      delta / width <
        Real.rpow delta (epsilon / 10) :=
    wideCoarseScaleBound
      hdelta hwidth hepsilon hwidthLarge
  have hpowerMonotone :
      Real.rpow delta (epsilon / 10) ≤
        Real.rpow delta₀ (epsilon / 10) :=
    Real.rpow_le_rpow
      hdelta.le hdeltaSmall (by positivity)
  have hdelta₀Power :
      Real.rpow delta₀ (epsilon / 10) = tau₀ := by
    dsimp only [delta₀]
    calc
      Real.rpow
          (Real.rpow tau₀ (10 / epsilon))
          (epsilon / 10) =
        Real.rpow tau₀
          ((10 / epsilon) * (epsilon / 10)) := by
            exact
              (Real.rpow_mul
                htau₀.le (10 / epsilon) (epsilon / 10)).symm
      _ = Real.rpow tau₀ 1 := by
            congr 1
            field_simp [hepsilon.ne']
      _ = tau₀ := by simp
  have htauSmall : delta / width ≤ tau₀ := by
    exact
      (calc
        delta / width <
            Real.rpow delta (epsilon / 10) := htauPower
        _ ≤ Real.rpow delta₀ (epsilon / 10) := hpowerMonotone
        _ = tau₀ := hdelta₀Power).le
  exact
    habsorb (delta / width) htau htauSmall

end Kakeya.Assouad
