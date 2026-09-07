import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionExponent

/-!
# Fixed-constant absorption at the selected Lemma 7.10 scale
-/

noncomputable section

namespace Kakeya.Assouad

/--
Every fixed finite constant can be absorbed into the exponent gap between the
effective Lemma 7.12 exponent and the requested one-scale exponent.
-/
lemma exists_parameterBlockProjection_absorption
    (constant : ENNReal)
    (hconstant_top : constant ≠ ⊤)
    {epsilon eta : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 100)
    (heta : 0 < eta)
    (heta_small : 1000 * eta < epsilon ^ 3) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ delta blockScale : ℝ,
        0 < delta →
        delta ≤ delta₀ →
        0 < blockScale →
        delta ≤ blockScale →
        Real.rpow delta (1 - epsilon ^ 2) <
          blockScale / 10 →
        constant *
            Kakeya.realRpowENN
              (delta / blockScale) epsilon ≤
          Kakeya.realRpowENN
            (delta / blockScale)
            (parameterBlockProjectionEffectiveExponent epsilon eta) := by
  let effective :=
    parameterBlockProjectionEffectiveExponent epsilon eta
  let gap := epsilon - effective
  have heffective_lt : effective < epsilon := by
    exact parameterBlockProjection_effectiveExponent_lt
      hepsilon hepsilon_small heta heta_small
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith
  have hepsilon_sq : 0 < epsilon ^ 2 :=
    sq_pos_of_pos hepsilon
  have hgamma : 0 < epsilon ^ 2 * gap := by positivity
  rcases exists_delta_realRpowENN_bound
      constant hconstant_top hgamma with
    ⟨delta₀, hdelta₀, hdelta₀_one, hconstant⟩
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro delta blockScale hdelta hdelta_le
    hblockScale hdelta_block hseparated
  have hdelta_one : delta ≤ 1 :=
    hdelta_le.trans hdelta₀_one
  have hratio : 0 < delta / blockScale := by positivity
  have hratio_one : delta / blockScale ≤ 1 := by
    exact (div_le_one hblockScale).2 hdelta_block
  have hten :
      10 * Real.rpow delta (1 - epsilon ^ 2) <
        blockScale := by
    linarith
  have hdelta_split :
      delta =
        Real.rpow delta (1 - epsilon ^ 2) *
          Real.rpow delta (epsilon ^ 2) := by
    calc
      delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
      _ = Real.rpow delta
          ((1 - epsilon ^ 2) + epsilon ^ 2) := by
        congr 1
        ring
      _ =
          Real.rpow delta (1 - epsilon ^ 2) *
            Real.rpow delta (epsilon ^ 2) :=
        Real.rpow_add hdelta _ _
  have hratio_delta :
      delta / blockScale ≤
        Real.rpow delta (epsilon ^ 2) := by
    have hdenom :
        0 < Real.rpow delta (1 - epsilon ^ 2) := by
      exact Real.rpow_pos_of_pos hdelta _
    calc
      delta / blockScale ≤
          delta /
            (Real.rpow delta (1 - epsilon ^ 2)) := by
        apply div_le_div_of_nonneg_left hdelta.le hdenom
        linarith
      _ = Real.rpow delta (epsilon ^ 2) := by
        apply
          (div_eq_iff hdenom.ne').2
        simpa [mul_comm] using hdelta_split
  have hgap_nonneg : 0 ≤ gap := hgap.le
  have hratio_gap :
      Kakeya.realRpowENN (delta / blockScale) gap ≤
        Kakeya.realRpowENN delta (epsilon ^ 2 * gap) := by
    simp only [Kakeya.realRpowENN]
    apply ENNReal.ofReal_mono
    calc
      Real.rpow (delta / blockScale) gap ≤
          Real.rpow (Real.rpow delta (epsilon ^ 2)) gap :=
        Real.rpow_le_rpow hratio.le hratio_delta hgap_nonneg
      _ = Real.rpow delta (epsilon ^ 2 * gap) :=
        (Real.rpow_mul hdelta.le (epsilon ^ 2) gap).symm
  have hconstant_bound :
      constant ≤
        Kakeya.realRpowENN delta (-(epsilon ^ 2 * gap)) :=
    hconstant delta hdelta hdelta_le
  have hconstant_gap :
      constant *
          Kakeya.realRpowENN (delta / blockScale) gap ≤ 1 := by
    calc
      constant *
            Kakeya.realRpowENN (delta / blockScale) gap ≤
          Kakeya.realRpowENN delta (-(epsilon ^ 2 * gap)) *
            Kakeya.realRpowENN delta (epsilon ^ 2 * gap) := by
        gcongr
      _ = Kakeya.realRpowENN delta 0 := by
        rw [← realRpowENN_add hdelta]
        congr 1
        ring
      _ = 1 := by simp [Kakeya.realRpowENN]
  have hexponent :
      epsilon = effective + gap := by
    dsimp only [gap]
    ring
  calc
    constant *
          Kakeya.realRpowENN
            (delta / blockScale) epsilon =
        Kakeya.realRpowENN
            (delta / blockScale) effective *
          (constant *
            Kakeya.realRpowENN
              (delta / blockScale) gap) := by
      rw [hexponent, realRpowENN_add hratio]
      ring
    _ ≤
        Kakeya.realRpowENN
          (delta / blockScale) effective * 1 := by
      gcongr
    _ =
        Kakeya.realRpowENN
          (delta / blockScale) effective := by
      ring

end Kakeya.Assouad
