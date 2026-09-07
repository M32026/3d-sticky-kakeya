import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.NearbyProjectionADTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening

/-!
# Finite unions of paper one-dimensional AD sets

The paper-literal interval formulation of one-dimensional AD control is
stable under finite unions.  This is used when one target grid slice pulls
back to a bounded number of source height cells during the final rescaling.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- A nonempty finite union of paper AD sets has the same exponent and base
scale, with its constant multiplied by the number of pieces. -/
lemma PureWZ2PaperADSet1.finite_iUnion
    {ι : Type*} {indices : Finset ι} {pieces : ι → Set ℝ}
    {delta alpha : ℝ} {C : ENNReal}
    (hindices : indices.Nonempty)
    (hpieces : ∀ index ∈ indices,
      PureWZ2PaperADSet1 (pieces index) delta alpha C) :
    PureWZ2PaperADSet1
      (⋃ index ∈ indices, pieces index) delta alpha
      ((indices.card : ENNReal) * C) := by
  classical
  rcases hindices with ⟨first, hfirst⟩
  rcases hpieces first hfirst with
    ⟨hdelta, halpha, halphaOne, hCOne, hCTop, _⟩
  have hcardOne : (1 : ENNReal) ≤ indices.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨first, hfirst⟩
  have hconstantOne : (1 : ENNReal) ≤ indices.card * C := by
    calc
      (1 : ENNReal) ≤ indices.card := hcardOne
      _ ≤ indices.card * C := le_mul_of_one_le_right' hCOne
  have hconstantTop : (indices.card : ENNReal) * C ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hCTop
  refine ⟨hdelta, halpha, halphaOne, hconstantOne, hconstantTop, ?_⟩
  intro rho hrho hdeltaRho left length hrhoLength
  let localPieces : ι → Set ℝ := fun index =>
    pieces index ∩ Set.Icc left (left + length)
  have hlocalUnion :
      (⋃ index ∈ indices, pieces index) ∩
          Set.Icc left (left + length) =
        ⋃ index ∈ indices, localPieces index := by
    ext value
    simp only [localPieces, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨hvalue, hinterval⟩
      rcases hvalue with ⟨index, hindex, hpiece⟩
      exact ⟨index, hindex, hpiece, hinterval⟩
    · rintro ⟨index, hindex, hpiece, hinterval⟩
      exact ⟨⟨index, hindex, hpiece⟩, hinterval⟩
  rw [hlocalUnion]
  have hcover := externalCoveringNumber_biUnion_le_card
    (ε := ⟨rho, hrho⟩) (s := indices) (A := localPieces)
    (B := C * Kakeya.realRpowENN (length / rho) alpha) (by
      intro index hindex
      exact (hpieces index hindex).2.2.2.2.2 rho hrho hdeltaRho
        left length hrhoLength)
  simpa [mul_assoc] using hcover

/-- A set whose points lie uniformly near one of finitely many paper AD sets
inherits paper AD control.  The loss separates cleanly into the finite-union
factor and the one-dimensional thickening factor. -/
lemma PureWZ2PaperADSet1.of_finite_nearby_witness
    {ι : Type*} {indices : Finset ι} {pieces : ι → Set ℝ}
    {target : Set ℝ} {D delta alpha : ℝ} {C : ENNReal}
    (hindices : indices.Nonempty)
    (hpieces : ∀ index ∈ indices,
      PureWZ2PaperADSet1 (pieces index) delta alpha C)
    (hwitness : ∀ value ∈ target,
      ∃ index ∈ indices, ∃ source ∈ pieces index,
        dist value source ≤ D)
    (hDNonnegative : 0 ≤ D) (hDDelta : D ≤ delta) :
    PureWZ2PaperADSet1 target delta alpha
      (6 * ((indices.card : ENNReal) * C)) := by
  let source := ⋃ index ∈ indices, pieces index
  have hsource : PureWZ2PaperADSet1 source delta alpha
      ((indices.card : ENNReal) * C) :=
    PureWZ2PaperADSet1.finite_iUnion hindices hpieces
  apply hsource.of_subset_cthickening
    (D := D) (T := target) (S := source)
  · intro value hvalue
    rcases hwitness value hvalue with
      ⟨index, hindex, sourceValue, hsourceValue, hdist⟩
    have hsourceUnion : sourceValue ∈ source := by
      exact Set.mem_iUnion.mpr ⟨index,
        Set.mem_iUnion.mpr ⟨hindex, hsourceValue⟩⟩
    exact ⟨sourceValue, hsourceUnion, hdist⟩
  · exact hDNonnegative
  · exact hDDelta

/-- General thickening transfer for the paper interval AD predicate.  The
explicit factor depends only on the ratio between the witness radius and the
base scale. -/
lemma PureWZ2PaperADSet1.of_subset_cthickening_general
    {source target : Set ℝ} {epsilon delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 source delta alpha C)
    (hwitness : ∀ value ∈ target,
      ∃ sourceValue ∈ source, dist value sourceValue ≤ epsilon)
    (hepsilon : 0 < epsilon) :
    PureWZ2PaperADSet1 target delta alpha
      ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 3 * C) := by
  rcases hAD with ⟨hdelta, halpha, halphaOne, hCOne, hCTop, hcover⟩
  let factor : ENNReal :=
    (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 3
  have hfactorOne : (1 : ENNReal) ≤ factor := by
    dsimp only [factor]
    have hnat : 0 < 2 * (Nat.ceil (epsilon / delta) + 1) := by omega
    have hcoe : (1 : ENNReal) ≤
        (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) := by
      exact_mod_cast hnat
    exact one_le_pow₀ hcoe
  have hconstantOne : (1 : ENNReal) ≤ factor * C :=
    hfactorOne.trans (le_mul_of_one_le_right' hCOne)
  have hconstantTop : factor * C ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · dsimp only [factor]
      apply ENNReal.pow_ne_top
      exact ENNReal.mul_ne_top (by norm_num) <|
        (ENNReal.add_ne_top).2 ⟨ENNReal.natCast_ne_top _, by norm_num⟩
    · exact hCTop
  refine ⟨hdelta, halpha, halphaOne, hconstantOne,
    hconstantTop, ?_⟩
  intro rho hrho hdeltaRho left length hrhoLength
  let localSource := source ∩
    Set.Icc (left - epsilon) (left + length + epsilon)
  have hlocalTarget : target ∩ Set.Icc left (left + length) ⊆
      Metric.cthickening epsilon localSource := by
    intro value hvalue
    rcases hwitness value hvalue.1 with
      ⟨sourceValue, hsourceValue, hdist⟩
    have hdistAbs : |value - sourceValue| ≤ epsilon := by
      simpa [Real.dist_eq] using hdist
    have hsourceInterval : sourceValue ∈
        Set.Icc (left - epsilon) (left + length + epsilon) := by
      have hleftDifference : value - sourceValue ≤ epsilon :=
        (le_abs_self _).trans hdistAbs
      have hrightDifference : sourceValue - value ≤ epsilon := by
        calc
          sourceValue - value ≤ |sourceValue - value| := le_abs_self _
          _ = |value - sourceValue| := by
            rw [show sourceValue - value = -(value - sourceValue) by ring,
              abs_neg]
          _ ≤ epsilon := hdistAbs
      exact ⟨by linarith [hvalue.2.1], by linarith [hvalue.2.2]⟩
    exact Metric.mem_cthickening_of_dist_le value sourceValue epsilon
      localSource ⟨hsourceValue, hsourceInterval⟩ hdist
  have hsourceCover :
      (Metric.externalCoveringNumber ⟨rho, hrho⟩ localSource : ENNReal) ≤
        C * Kakeya.realRpowENN ((length + 2 * epsilon) / rho) alpha := by
    have hrhoLengthExpanded : rho ≤ length + 2 * epsilon := by
      have hepsilonNonnegative : 0 ≤ epsilon := hepsilon.le
      linarith
    have hendpoint : (left - epsilon) + (length + 2 * epsilon) =
        left + length + epsilon := by ring
    rw [show localSource = source ∩
        Set.Icc (left - epsilon)
          ((left - epsilon) + (length + 2 * epsilon)) by
      simp [localSource, hendpoint]]
    exact hcover rho hrho hdeltaRho (left - epsilon)
      (length + 2 * epsilon) hrhoLengthExpanded
  have hthick := externalCoveringNumber_cthickening_general
    hepsilon (hdelta.trans_le hdeltaRho) (S := localSource)
  have hmono :
      (Metric.externalCoveringNumber ⟨rho, hrho⟩
        (target ∩ Set.Icc left (left + length)) : ENNReal) ≤
      (Metric.externalCoveringNumber ⟨rho, hrho⟩
        (Metric.cthickening epsilon localSource) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hlocalTarget
  have hceilMono : Nat.ceil (epsilon / rho) ≤
      Nat.ceil (epsilon / delta) := by
    apply Nat.ceil_le.mpr
    exact (div_le_div_of_nonneg_left hepsilon.le
      hdelta hdeltaRho).trans
      (Nat.le_ceil (epsilon / delta))
  have hlengthNonnegative : 0 ≤ length :=
    (hdelta.trans_le hdeltaRho).le.trans hrhoLength
  have hratio :
      Kakeya.realRpowENN ((length + 2 * epsilon) / rho) alpha ≤
        ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 *
          Kakeya.realRpowENN (length / rho) alpha) := by
    have hfactorReal : length + 2 * epsilon ≤
        (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) * length := by
      have hepsilonBound : epsilon ≤
          (Nat.ceil (epsilon / delta) : ℝ) * delta := by
        calc
          epsilon = (epsilon / delta) * delta := by
            field_simp [hdelta.ne']
          _ ≤ (Nat.ceil (epsilon / delta) : ℝ) * delta := by
            gcongr
            exact Nat.le_ceil (epsilon / delta)
      have hdeltaLength : delta ≤ length :=
        hdeltaRho.trans hrhoLength
      have hepsilonLength : epsilon ≤
          (Nat.ceil (epsilon / delta) : ℝ) * length :=
        hepsilonBound.trans <| mul_le_mul_of_nonneg_left hdeltaLength
          (Nat.cast_nonneg _)
      nlinarith
    have hbaseNonnegative : 0 ≤ length / rho := by positivity
    have hscaled : (length + 2 * epsilon) / rho ≤
        (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) *
          (length / rho) := by
      calc
        (length + 2 * epsilon) / rho ≤
            ((2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) * length) /
              rho := by gcongr
        _ = _ := by ring
    have hrpow := Real.rpow_le_rpow
      (div_nonneg (add_nonneg hlengthNonnegative (by positivity)) hrho)
      hscaled halpha.le
    have hfactorRpow : Real.rpow
        (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) alpha ≤
        (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) ^ 2 := by
      have hfactorBase : (1 : ℝ) ≤
          2 * (Nat.ceil (epsilon / delta) + 1) := by
        exact_mod_cast show 1 ≤ 2 * (Nat.ceil (epsilon / delta) + 1) by omega
      calc
        Real.rpow (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) alpha ≤
            Real.rpow (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) 1 :=
          Real.rpow_le_rpow_of_exponent_le hfactorBase halphaOne
        _ = (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) :=
          Real.rpow_one _
        _ ≤ (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) ^ 2 := by
          nlinarith
    dsimp only [Kakeya.realRpowENN]
    rw [Real.mul_rpow (by positivity) hbaseNonnegative] at hrpow
    calc
      ENNReal.ofReal (Real.rpow ((length + 2 * epsilon) / rho) alpha) ≤
          ENNReal.ofReal
            (Real.rpow (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) alpha *
              Real.rpow (length / rho) alpha) :=
        ENNReal.ofReal_le_ofReal hrpow
      _ = ENNReal.ofReal
            (Real.rpow (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) alpha) *
          ENNReal.ofReal (Real.rpow (length / rho) alpha) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) alpha)
      _ ≤ ENNReal.ofReal
            ((2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) ^ 2) *
          ENNReal.ofReal (Real.rpow (length / rho) alpha) := by
        exact mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal hfactorRpow) bot_le
      _ = (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 *
          ENNReal.ofReal (Real.rpow (length / rho) alpha) := by
        rw [ENNReal.ofReal_pow (by positivity)]
        congr 2
        have hreal : (2 * (Nat.ceil (epsilon / delta) + 1) : ℝ) =
            ((2 * (Nat.ceil (epsilon / delta) + 1) : ℕ) : ℝ) := by
          norm_cast
        rw [hreal, ENNReal.ofReal_natCast]
        norm_cast
  calc
    (Metric.externalCoveringNumber ⟨rho, hrho⟩
        (target ∩ Set.Icc left (left + length)) : ENNReal)
        ≤ (Metric.externalCoveringNumber ⟨rho, hrho⟩
          (Metric.cthickening epsilon localSource) : ENNReal) := hmono
    _ ≤ (2 * Nat.ceil (epsilon / rho) + 2 : ENNReal) *
          (Metric.externalCoveringNumber ⟨rho, hrho⟩ localSource : ENNReal) := by
      exact_mod_cast hthick
    _ ≤ (2 * Nat.ceil (epsilon / delta) + 2 : ENNReal) *
          (C * Kakeya.realRpowENN ((length + 2 * epsilon) / rho) alpha) := by
      have hcoefficient :
          (2 * Nat.ceil (epsilon / rho) + 2 : ENNReal) ≤
            (2 * Nat.ceil (epsilon / delta) + 2 : ENNReal) := by
        exact_mod_cast show
          2 * Nat.ceil (epsilon / rho) + 2 ≤
            2 * Nat.ceil (epsilon / delta) + 2 by omega
      exact mul_le_mul' hcoefficient hsourceCover
    _ ≤ (2 * Nat.ceil (epsilon / delta) + 2 : ENNReal) *
          (C * ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 *
            Kakeya.realRpowENN (length / rho) alpha)) := by
      gcongr
    _ = factor * C * Kakeya.realRpowENN (length / rho) alpha := by
      dsimp only [factor]
      have hsame : (2 * Nat.ceil (epsilon / delta) + 2 : ENNReal) =
          (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) := by
        norm_cast
      rw [hsame]
      change
        (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) *
            (C * ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 *
              Kakeya.realRpowENN (length / rho) alpha)) =
          factor * C * Kakeya.realRpowENN (length / rho) alpha
      dsimp only [factor]
      ring

end Kakeya.Assouad

end
