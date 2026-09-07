import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Arithmetic for repaired wide snapped covering transport
-/

namespace Kakeya.Assouad

open scoped ENNReal

lemma wide_snapped_radius_ratio_bound
    {delta width scale error radius : ℝ}
    (hdelta : 0 < delta) (hwidth : 0 < width)
    (hscale : 0 < scale)
    (hscale_le_one : scale ≤ 1)
    (herror : error ≤ 4800 * width * scale)
    (hwidthScale : width * scale ≤ 4 * delta)
    (hradius : radius = 2 * width + error) :
    2 * radius / delta ≤ 38416 / scale := by
  have herrorWidth : error ≤ 4800 * width := by
    calc
      error ≤ 4800 * width * scale := herror
      _ ≤ 4800 * width * 1 := by
        gcongr
      _ = 4800 * width := by ring
  have hradiusWidth : radius ≤ 4802 * width := by
    rw [hradius]
    linarith
  have hdouble : 2 * radius ≤ 9604 * width := by
    linarith
  have hfirst :
      2 * radius / delta ≤ 9604 * width / delta :=
    (div_le_div_iff_of_pos_right hdelta).2 hdouble
  have hwidthRatio : width / delta ≤ 4 / scale := by
    apply (div_le_iff₀ hdelta).2
    calc
      width ≤ 4 * delta / scale := by
        apply (le_div_iff₀ hscale).2
        nlinarith
      _ = (4 / scale) * delta := by ring
  calc
    2 * radius / delta ≤ 9604 * width / delta := hfirst
    _ = 9604 * (width / delta) := by ring
    _ ≤ 9604 * (4 / scale) := by gcongr
    _ = 38416 / scale := by ring

lemma realRpowENN_one_div_positive
    {base exponent : ℝ} (hbase : 0 < base) :
    Kakeya.realRpowENN (1 / base) exponent =
      Kakeya.realRpowENN base (-exponent) := by
  simp only [Kakeya.realRpowENN]
  congr 1
  calc
    Real.rpow (1 / base) exponent =
        Real.rpow 1 exponent / Real.rpow base exponent :=
      Real.div_rpow (by norm_num) hbase.le exponent
    _ = (Real.rpow base exponent)⁻¹ := by simp
    _ = Real.rpow base (-exponent) :=
      (Real.rpow_neg hbase.le exponent).symm

lemma wide_snapped_covering_exponent_bound
    {delta scale epsilon B : ℝ} {C : ℕ}
    (hdelta : 0 < delta) (hscale : 0 < scale)
    (hepsilon : 0 < epsilon)
    (hB : 0 < B) (hC : 0 < C)
    (hscaleUpper :
      scale ≤ Real.rpow delta (epsilon / 10))
    (hsmall :
      Real.rpow delta (epsilon ^ 2 / 20) ≤
        1 / ((C : ℝ) * Real.rpow B (1 - epsilon))) :
    Kakeya.realRpowENN (B / scale) (1 - epsilon) ≤
      Kakeya.realRpowENN scale (epsilon / 2 - 1) /
        (C : ENNReal) := by
  have hhalf : 0 < epsilon / 2 := by positivity
  have hbasePower :
      Real.rpow scale (epsilon / 2) ≤
        Real.rpow delta (epsilon ^ 2 / 20) := by
    calc
      Real.rpow scale (epsilon / 2) ≤
          Real.rpow (Real.rpow delta (epsilon / 10))
            (epsilon / 2) :=
        Real.rpow_le_rpow hscale.le hscaleUpper hhalf.le
      _ =
          Real.rpow delta
            ((epsilon / 10) * (epsilon / 2)) := by
        exact (Real.rpow_mul hdelta.le _ _).symm
      _ = Real.rpow delta (epsilon ^ 2 / 20) := by
        congr 1
        ring
  have hdenPos :
      0 < (C : ℝ) * Real.rpow B (1 - epsilon) := by
    exact
      mul_pos (by exact_mod_cast hC)
        (Real.rpow_pos_of_pos hB _)
  have hbaseSmall :
      Real.rpow scale (epsilon / 2) ≤
        1 / ((C : ℝ) * Real.rpow B (1 - epsilon)) :=
    hbasePower.trans hsmall
  have hproduct :
      ((C : ℝ) * Real.rpow B (1 - epsilon)) *
          Real.rpow scale (epsilon / 2) ≤ 1 := by
    have := (le_div_iff₀ hdenPos).1 hbaseSmall
    nlinarith
  have hscalePowerPos :
      0 < Real.rpow scale (epsilon / 2) :=
    Real.rpow_pos_of_pos hscale _
  have hreal :
      (C : ℝ) * Real.rpow B (1 - epsilon) ≤
        Real.rpow scale (-epsilon / 2) := by
    have hneg :
        Real.rpow scale (-epsilon / 2) =
          (Real.rpow scale (epsilon / 2))⁻¹ := by
      calc
        Real.rpow scale (-epsilon / 2) =
            Real.rpow scale (-(epsilon / 2)) := by
          congr 1
          ring
        _ = (Real.rpow scale (epsilon / 2))⁻¹ :=
          Real.rpow_neg hscale.le (epsilon / 2)
    rw [hneg]
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hscalePowerPos).2
    simpa [mul_comm] using hproduct
  have henn :
      (C : ENNReal) *
          Kakeya.realRpowENN B (1 - epsilon) ≤
        Kakeya.realRpowENN scale (-epsilon / 2) := by
    have hof := ENNReal.ofReal_mono hreal
    simpa [Kakeya.realRpowENN,
      ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul
        (show (0 : ℝ) ≤ (C : ℝ) by positivity)] using hof
  have hquotient :
      Kakeya.realRpowENN (B / scale) (1 - epsilon) =
        Kakeya.realRpowENN B (1 - epsilon) *
          Kakeya.realRpowENN scale (-(1 - epsilon)) := by
    calc
      Kakeya.realRpowENN (B / scale) (1 - epsilon) =
          Kakeya.realRpowENN (B * (1 / scale))
            (1 - epsilon) := by
        congr 2
        ring
      _ =
          Kakeya.realRpowENN B (1 - epsilon) *
            Kakeya.realRpowENN (1 / scale)
              (1 - epsilon) :=
        realRpowENN_mul hB (by positivity) _
      _ =
          Kakeya.realRpowENN B (1 - epsilon) *
            Kakeya.realRpowENN scale (-(1 - epsilon)) := by
        rw [realRpowENN_one_div_positive hscale]
  have htarget :
      Kakeya.realRpowENN scale (epsilon / 2 - 1) =
        Kakeya.realRpowENN scale (-epsilon / 2) *
          Kakeya.realRpowENN scale (-(1 - epsilon)) := by
    have hexponent :
        epsilon / 2 - 1 =
          (-epsilon / 2) + (-(1 - epsilon)) := by ring
    rw [hexponent]
    exact realRpowENN_add hscale _ _
  rw [hquotient, htarget]
  apply
    (ENNReal.le_div_iff_mul_le
      (Or.inl (by positivity : (C : ENNReal) ≠ 0))
      (Or.inl (by simp : (C : ENNReal) ≠ ⊤))).2
  calc
    (Kakeya.realRpowENN B (1 - epsilon) *
          Kakeya.realRpowENN scale (-(1 - epsilon))) *
        (C : ENNReal) =
      ((C : ENNReal) *
          Kakeya.realRpowENN B (1 - epsilon)) *
        Kakeya.realRpowENN scale (-(1 - epsilon)) := by
      ac_rfl
    _ ≤
      Kakeya.realRpowENN scale (-epsilon / 2) *
        Kakeya.realRpowENN scale (-(1 - epsilon)) := by
      gcongr

lemma wide_snapped_transport_small_scales
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Real.rpow delta (epsilon ^ 2 / 20) ≤
            1 / ((3840201 : ℝ) *
              Real.rpow 38416 (1 - epsilon)) ∧
          Real.rpow delta (epsilon / 20) ≤ 1 / 25 := by
  have hfirstExponent : 0 < epsilon ^ 2 / 20 := by positivity
  have hsecondExponent : 0 < epsilon / 20 := by positivity
  have hBPower : 1 < Real.rpow 38416 (1 - epsilon) := by
    apply Real.one_lt_rpow
    · norm_num
    · linarith
  have hden :
      1 < (3840201 : ℝ) *
        Real.rpow 38416 (1 - epsilon) := by
    nlinarith
  have hfirstConstant :
      0 < 1 / ((3840201 : ℝ) *
        Real.rpow 38416 (1 - epsilon)) := by
    positivity
  have hfirstConstantOne :
      1 / ((3840201 : ℝ) *
        Real.rpow 38416 (1 - epsilon)) < 1 := by
    exact (div_lt_one (by positivity)).2 hden
  rcases
      exists_delta_rpow_le_single
        (epsilon ^ 2 / 20)
        (1 / ((3840201 : ℝ) *
          Real.rpow 38416 (1 - epsilon)))
        hfirstExponent hfirstConstant hfirstConstantOne with
    ⟨firstScale, hfirstScale, hfirstScaleOne, hfirst⟩
  rcases
      exists_delta_rpow_le_single
        (epsilon / 20) (1 / 25)
        hsecondExponent (by norm_num) (by norm_num) with
    ⟨secondScale, hsecondScale,
      hsecondScaleOne, hsecond⟩
  let delta₀ := min firstScale secondScale
  refine
    ⟨delta₀, by positivity,
      (min_le_left _ _).trans hfirstScaleOne, ?_⟩
  intro delta hdelta hdeltaSmall
  exact
    ⟨hfirst delta hdelta
        (hdeltaSmall.trans (min_le_left _ _)),
      hsecond delta hdelta
        (hdeltaSmall.trans (min_le_right _ _))⟩

end Kakeya.Assouad
