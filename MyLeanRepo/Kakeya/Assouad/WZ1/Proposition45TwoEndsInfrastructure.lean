import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition45TwoEndsStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.TwoEndsReduction
import MyLeanRepo.Kakeya.Assouad.WZ1.TwoEndsToNonConcentration
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Two-ends infrastructure for WZ1 Proposition 8.9

This module records the literal output of the paper's Lemma 8.10 before any
anisotropic rescaling.  The selected set has strip nonconcentration with
constant `width⁻ᶻᵉᵗᵃ`.  Conversion to the scale-normalized line
nonconcentration used by Proposition 8.5 is valid only when
`delta^lambda ≤ width`.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Convert a nonnegative real cardinality retention bound to `ENNReal`. -/
lemma real_card_retention_to_ennreal
    {factor : ℝ} {ambient selected : DiscreteSet 2}
    (hfactor : 0 ≤ factor)
    (hretention :
      factor * (ambient.card : ℝ) ≤
        (selected.card : ℝ)) :
    ENNReal.ofReal factor * ambient.enncard ≤
      selected.enncard := by
  have hconverted :=
    ENNReal.ofReal_le_ofReal hretention
  have hleft :
      ENNReal.ofReal
          (factor * (ambient.card : ℝ)) =
        ENNReal.ofReal factor * ambient.enncard := by
    rw [ENNReal.ofReal_mul hfactor]
    simp [DiscreteSet.enncard]
  have hright :
      ENNReal.ofReal (selected.card : ℝ) =
        selected.enncard := by
    simp [DiscreteSet.enncard]
  rwa [hleft, hright] at hconverted

/--
Compose an active-projection retention bound with the strip retention from
Lemma 8.10.
-/
lemma two_ends_selected_retention
    {delta eta zeta width : ℝ}
    {coefficient : ENNReal}
    {ambient active selected : DiscreteSet 2}
    (hdelta : 0 < delta)
    (hzeta : 0 < zeta)
    (hdeltaWidth : delta ≤ width)
    (hactive :
      coefficient *
          Kakeya.realRpowENN delta eta *
          ambient.enncard ≤
        active.enncard)
    (hstrip :
      ENNReal.ofReal (Real.rpow width zeta) *
          active.enncard ≤
        selected.enncard) :
    coefficient *
        Kakeya.realRpowENN delta (eta + zeta) *
        ambient.enncard ≤
      selected.enncard := by
  have hdeltaNonneg : 0 ≤ delta := hdelta.le
  have hwidth : 0 < width := hdelta.trans_le hdeltaWidth
  have hpower :
      Kakeya.realRpowENN delta zeta ≤
        ENNReal.ofReal (Real.rpow width zeta) := by
    simp only [Kakeya.realRpowENN]
    exact
      ENNReal.ofReal_mono
        (Real.rpow_le_rpow
          hdeltaNonneg hdeltaWidth hzeta.le)
  have hcombined :
      coefficient *
          Kakeya.realRpowENN delta eta *
          Kakeya.realRpowENN delta zeta *
          ambient.enncard ≤
        ENNReal.ofReal (Real.rpow width zeta) *
          active.enncard := by
    calc
      coefficient *
          Kakeya.realRpowENN delta eta *
          Kakeya.realRpowENN delta zeta *
          ambient.enncard
          =
        Kakeya.realRpowENN delta zeta *
          (coefficient *
            Kakeya.realRpowENN delta eta *
            ambient.enncard) := by
            ac_rfl
      _ ≤
        Kakeya.realRpowENN delta zeta *
          active.enncard := by
            exact mul_le_mul_left' hactive _
      _ ≤
        ENNReal.ofReal (Real.rpow width zeta) *
          active.enncard := by
            exact mul_le_mul_right' hpower _
  calc
    coefficient *
        Kakeya.realRpowENN delta (eta + zeta) *
        ambient.enncard
        =
      coefficient *
        Kakeya.realRpowENN delta eta *
        Kakeya.realRpowENN delta zeta *
        ambient.enncard := by
          have hadd :
              Real.rpow delta (eta + zeta) =
                Real.rpow delta eta *
                  Real.rpow delta zeta :=
            Real.rpow_add hdelta eta zeta
          simp only [Kakeya.realRpowENN]
          rw [hadd]
          have hofReal :
              ENNReal.ofReal
                  (Real.rpow delta eta *
                    Real.rpow delta zeta) =
                ENNReal.ofReal (Real.rpow delta eta) *
                  ENNReal.ofReal (Real.rpow delta zeta) := by
            exact
              ENNReal.ofReal_mul
                (Real.rpow_nonneg hdelta.le eta)
          rw [hofReal]
          ac_rfl
    _ ≤
        ENNReal.ofReal (Real.rpow width zeta) *
          active.enncard := hcombined
    _ ≤ selected.enncard := hstrip

/--
Package the selected strip from `two_ends_reduction` as a nonempty set with
raw strip nonconcentration.
-/
lemma two_ends_to_raw_strip_nonconcentration
    {set : DiscreteSet 2}
    {delta zeta width retention : ℝ}
    (normal : Point2) (level : ℝ)
    (hnormal : ‖normal‖ = 1)
    (hdelta : 0 < delta) (hzeta : 0 < zeta)
    (hdeltaWidth : delta ≤ width)
    (hwidthOne : width ≤ 1)
    (hset : set.Nonempty)
    (hretention : 0 < retention)
    (hdensity :
      retention * Real.rpow width zeta * (set.card : ℝ) ≤
        ((set.filter fun point =>
          |inner ℝ point normal - level| ≤ width).card : ℝ))
    (hnonconcentration :
      ∀ otherNormal : Point2, ∀ otherLevel radius : ℝ,
        ‖otherNormal‖ = 1 →
        delta ≤ radius → radius ≤ width →
          ((set.filter fun point =>
            |inner ℝ point normal - level| ≤ width ∧
            |inner ℝ point otherNormal - otherLevel| ≤ radius).card :
              ℝ) ≤
            Real.rpow (radius / width) zeta *
              ((set.filter fun point =>
                |inner ℝ point normal - level| ≤ width).card : ℝ)) :
    let selected :=
      set.filter fun point =>
        |inner ℝ point normal - level| ≤ width
    selected.Nonempty ∧
      WZ1RawStripNonconcentration delta zeta width selected := by
  let selected :=
    set.filter fun point =>
      |inner ℝ point normal - level| ≤ width
  have hwidth : 0 < width := hdelta.trans_le hdeltaWidth
  have hselected : selected.Nonempty := by
    have hleft :
        0 <
          retention * Real.rpow width zeta * (set.card : ℝ) := by
      have hcard : 0 < (set.card : ℝ) := by
        exact_mod_cast hset.card_pos
      exact
        mul_pos
          (mul_pos hretention (Real.rpow_pos_of_pos hwidth zeta))
          hcard
    have : 0 < (selected.card : ℝ) := hleft.trans_le hdensity
    exact Finset.card_pos.mp (by exact_mod_cast this)
  have hraw :
      WZ1RawStripNonconcentration delta zeta width selected := by
    intro otherNormal hotherNormal otherLevel radius hdeltaRadius
    have hmain :=
      two_ends_to_strip_nonconcentration
        hdelta hzeta normal level width hnormal
        hdeltaWidth hwidthOne hnonconcentration
        selected rfl
        otherNormal hotherNormal otherLevel radius hdeltaRadius
    simpa [WZ1RawStripNonconcentration, selected,
      DiscreteSet.enncard] using hmain
  exact ⟨hselected, hraw⟩

/--
Convert the raw two-ends constant to the line-nonconcentration convention
when the selected strip is wide enough.
-/
lemma WZ1RawStripNonconcentration.toLineNonconcentration
    {delta lambda zeta width : ℝ}
    {set : DiscreteSet 2}
    (hraw :
      WZ1RawStripNonconcentration delta zeta width set)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta)
    (hwidth : 0 < width)
    (hwide : Real.rpow delta lambda ≤ width) :
    WZ1LineNonConcentration delta lambda zeta set := by
  intro normal hnormal level radius hdeltaRadius hradiusOne
  have hradius : 0 < radius := hdelta.trans_le hdeltaRadius
  have hdeltaPower : 0 < Real.rpow delta lambda :=
    Real.rpow_pos_of_pos hdelta _
  have hconstant :
      (Real.rpow width zeta)⁻¹ ≤
        Real.rpow (Real.rpow delta (-lambda)) zeta := by
    have hnegative :
        Real.rpow width (-zeta) ≤
          Real.rpow (Real.rpow delta lambda) (-zeta) :=
      Real.rpow_le_rpow_of_nonpos hdeltaPower hwide (by linarith)
    have hinv :
        (Real.rpow width zeta)⁻¹ =
          Real.rpow width (-zeta) :=
      (Real.rpow_neg hwidth.le zeta).symm
    have hleft :
        Real.rpow (Real.rpow delta lambda) (-zeta) =
          Real.rpow delta (lambda * (-zeta)) :=
      (Real.rpow_mul hdelta.le lambda (-zeta)).symm
    have hright :
        Real.rpow (Real.rpow delta (-lambda)) zeta =
          Real.rpow delta ((-lambda) * zeta) :=
      (Real.rpow_mul hdelta.le (-lambda) zeta).symm
    rw [hinv]
    calc
      Real.rpow width (-zeta)
          ≤ Real.rpow (Real.rpow delta lambda) (-zeta) :=
        hnegative
      _ = Real.rpow delta (lambda * (-zeta)) := hleft
      _ = Real.rpow delta ((-lambda) * zeta) := by ring
      _ = Real.rpow (Real.rpow delta (-lambda)) zeta :=
        hright.symm
  have hrpow :
      Real.rpow (Real.rpow delta (-lambda) * radius) zeta =
        Real.rpow (Real.rpow delta (-lambda)) zeta *
          Real.rpow radius zeta := by
    exact
      Real.mul_rpow
        (Real.rpow_nonneg hdelta.le _)
        hradius.le
  calc
    ((set.filter fun point =>
        |inner ℝ point normal - level| ≤ radius).card : ENNReal)
        ≤ ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
            set.enncard :=
      hraw normal hnormal level radius hdeltaRadius
    _ ≤ ENNReal.ofReal
          (Real.rpow (Real.rpow delta (-lambda)) zeta *
            Real.rpow radius zeta) *
          set.enncard := by
      have hreal :
          (Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta ≤
            Real.rpow (Real.rpow delta (-lambda)) zeta *
              Real.rpow radius zeta :=
        mul_le_mul_of_nonneg_right
          hconstant (Real.rpow_nonneg hradius.le zeta)
      exact
        mul_le_mul_right'
          (ENNReal.ofReal_mono hreal)
          set.enncard
    _ =
        Kakeya.realRpowENN
            (Real.rpow delta (-lambda) * radius) zeta *
          set.enncard := by
      rw [Kakeya.realRpowENN, hrpow]

/--
Restrict raw strip nonconcentration to a quantitatively retained subset.
The reciprocal retention factor is the only loss.
-/
lemma WZ1RawStripNonconcentration.restrict
    {delta zeta width : ℝ}
    {ambient selected : DiscreteSet 2}
    {retention : ENNReal}
    (hraw :
      WZ1RawStripNonconcentration
        delta zeta width ambient)
    (hselected : selected ⊆ ambient)
    (hretention :
      retention * ambient.enncard ≤ selected.enncard)
    (hretentionPos : 0 < retention)
    (hretentionTop : retention ≠ ⊤) :
    WZ1WeightedRawStripNonconcentration
      delta zeta width retention⁻¹ selected := by
  intro normal hnormal level radius hdeltaRadius
  have hcount :
      ((selected.filter fun point =>
          |inner ℝ point normal - level| ≤ radius).card :
          ENNReal) ≤
        ((ambient.filter fun point =>
          |inner ℝ point normal - level| ≤ radius).card :
          ENNReal) := by
    exact_mod_cast
      Finset.card_le_card
        (Finset.filter_subset_filter
          (fun point =>
            |inner ℝ point normal - level| ≤ radius)
          hselected)
  have hambient :
      ambient.enncard ≤ retention⁻¹ * selected.enncard := by
    have hscaled :=
      mul_le_mul_left' hretention retention⁻¹
    rw [← mul_assoc,
      ENNReal.inv_mul_cancel
        hretentionPos.ne' hretentionTop,
      one_mul] at hscaled
    exact hscaled
  calc
    ((selected.filter fun point =>
        |inner ℝ point normal - level| ≤ radius).card :
        ENNReal)
        ≤
      ((ambient.filter fun point =>
        |inner ℝ point normal - level| ≤ radius).card :
        ENNReal) := hcount
    _ ≤
        ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          ambient.enncard :=
      hraw normal hnormal level radius hdeltaRadius
    _ ≤
        ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          (retention⁻¹ * selected.enncard) := by
      exact mul_le_mul_left' hambient _
    _ =
        retention⁻¹ *
          ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          selected.enncard := by
      ac_rfl

/--
The explicit `(8.30)` loss after two `1/16` graph refinements.
-/
lemma WZ1RawStripNonconcentration.restrict_two_refinements
    {delta eta zeta width : ℝ}
    {ambient selected : DiscreteSet 2}
    (hdelta : 0 < delta)
    (hraw :
      WZ1RawStripNonconcentration
        delta zeta width ambient)
    (hselected : selected ⊆ ambient)
    (hretention :
      (1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta *
          ambient.enncard ≤
        selected.enncard) :
    WZ1WeightedRawStripNonconcentration
      delta zeta width
      ((256 : ENNReal) *
        Kakeya.realRpowENN delta (-eta))
      selected := by
  let retention : ENNReal :=
    (1 / 256 : ENNReal) *
      Kakeya.realRpowENN delta eta
  have hretentionPos : 0 < retention := by
    dsimp only [retention]
    apply ENNReal.mul_pos
    · norm_num
    · simp [Kakeya.realRpowENN, ENNReal.ofReal_eq_zero,
        Real.rpow_pos_of_pos hdelta]
  have hretentionTop : retention ≠ ⊤ := by
    exact
      ENNReal.mul_ne_top
        (by simp)
        (by simp [Kakeya.realRpowENN])
  have hinverse :
      retention⁻¹ =
        (256 : ENNReal) *
          Kakeya.realRpowENN delta (-eta) := by
    have hpowPos :
        Kakeya.realRpowENN delta eta ≠ 0 := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_eq_zero,
        Real.rpow_pos_of_pos hdelta]
    have hpowTop :
        Kakeya.realRpowENN delta eta ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    dsimp only [retention]
    rw [ENNReal.mul_inv (by simp) (Or.inl (by simp))]
    have hconstant :
        (1 / 256 : ENNReal)⁻¹ = 256 := by
      norm_num
    rw [hconstant]
    congr 1
    simp only [Kakeya.realRpowENN]
    have hnegative :
        Real.rpow delta (-eta) =
          (Real.rpow delta eta)⁻¹ :=
      Real.rpow_neg hdelta.le eta
    rw [hnegative]
    exact
      (ENNReal.ofReal_inv_of_pos
        (Real.rpow_pos_of_pos hdelta eta)).symm
  have hrestricted :=
    hraw.restrict hselected
      (show retention * ambient.enncard ≤
          selected.enncard by
        simpa [retention, mul_assoc] using hretention)
      hretentionPos hretentionTop
  simpa [hinverse] using hrestricted

end Kakeya.Assouad
