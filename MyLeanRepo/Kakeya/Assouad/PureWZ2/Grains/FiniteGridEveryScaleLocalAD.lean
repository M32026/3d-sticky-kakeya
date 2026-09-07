import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RelaxedLocalGrainData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LowCaseTrivialAD

/-!
# Fixed-shading finite-grid interpolation for local AD

This module isolates the closed interpolation and fine-scale absorption part
of the preliminary Lemma 4.12 argument.  Its geometric input is an internal
AD estimate at every point of one fixed shading and every scale in a finite
power grid.  It neither invokes sticky nor changes the shading or plane map.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- The power grid used in the Lemma 4.12 finite-scale argument. -/
def finiteGridScaleVal (delta : ℝ) (N k : ℕ) : ℝ :=
  Real.rpow delta (1 - (k : ℝ) / (N : ℝ))

/-- The nearest grid scale above a query scale costs at most one grid step,
apart from the lower endpoint where the fine scale `delta` is used. -/
lemma finiteGridScale_interpolation_factor_bound
    {delta midLoss : ℝ} {N kMin kMax k : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hN : 0 < (N : ℝ)) (hmidLoss : 0 < midLoss)
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkRange : kMin ≤ k ∧ k ≤ kMax)
    (queryScale : ℝ) (hquery : 0 < queryScale)
    (hdeltaQuery : delta ≤ queryScale)
    (hqueryGrid : queryScale ≤ finiteGridScaleVal delta N k)
    (hprevious : k > kMin →
      queryScale > finiteGridScaleVal delta N (k - 1)) :
    (10 : ℝ) * finiteGridScaleVal delta N k / queryScale ≤
      (10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by
  have hgridPos : ∀ j : ℕ, 0 < finiteGridScaleVal delta N j := by
    intro j
    exact Real.rpow_pos_of_pos hdelta _
  have hrpowDiv : ∀ a b : ℝ,
      Real.rpow delta a / Real.rpow delta b =
        Real.rpow delta (a - b) := by
    intro a b
    exact (Real.rpow_sub hdelta a b).symm
  have hkMinBound : (kMin : ℝ) / (N : ℝ) ≤
      midLoss + 1 / (N : ℝ) := by
    have hceil : (kMin : ℝ) < (N : ℝ) * midLoss + 1 := by
      rw [hkMin]
      exact Nat.ceil_lt_add_one (by positivity)
    calc
      (kMin : ℝ) / (N : ℝ)
          ≤ ((N : ℝ) * midLoss + 1) / (N : ℝ) := by
            exact div_le_div_of_nonneg_right hceil.le hN.le
      _ = midLoss + 1 / (N : ℝ) := by
        field_simp [hN.ne'] <;> ring
  by_cases hk : k = kMin
  · have hquotient : finiteGridScaleVal delta N kMin / queryScale ≤
        finiteGridScaleVal delta N kMin / delta := by
      exact div_le_div_of_nonneg_left
        (hgridPos kMin).le hdelta hdeltaQuery
    have hgridDelta : finiteGridScaleVal delta N kMin / delta =
        Real.rpow delta (-(kMin : ℝ) / (N : ℝ)) := by
      dsimp only [finiteGridScaleVal]
      have h : Real.rpow delta (1 - (kMin : ℝ) / (N : ℝ)) /
          Real.rpow delta 1 =
            Real.rpow delta ((1 - (kMin : ℝ) / (N : ℝ)) - 1) := by
        rw [hrpowDiv]
      have hone : Real.rpow delta 1 = delta := Real.rpow_one delta
      rw [hone] at h
      have hexponent : (1 - (kMin : ℝ) / (N : ℝ)) - 1 =
          -(kMin : ℝ) / (N : ℝ) := by ring
      rw [hexponent] at h
      exact h
    have hfirst : finiteGridScaleVal delta N k / queryScale ≤
        Real.rpow delta (-(kMin : ℝ) / (N : ℝ)) := by
      rw [hk]
      exact hquotient.trans hgridDelta.le
    have hexponent : -(kMin : ℝ) / (N : ℝ) ≥
        -midLoss - 1 / (N : ℝ) := by
      have hneg : -((kMin : ℝ) / (N : ℝ)) ≥
          -(midLoss + 1 / (N : ℝ)) := neg_le_neg hkMinBound
      have hleft : -((kMin : ℝ) / (N : ℝ)) =
          -(kMin : ℝ) / (N : ℝ) := by ring
      have hright : -(midLoss + 1 / (N : ℝ)) =
          -midLoss - 1 / (N : ℝ) := by ring
      rw [hleft, hright] at hneg
      exact hneg
    have hrpow : Real.rpow delta (-(kMin : ℝ) / (N : ℝ)) ≤
        Real.rpow delta (-midLoss - 1 / (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hexponent
    calc
      (10 : ℝ) * finiteGridScaleVal delta N k / queryScale =
          10 * (finiteGridScaleVal delta N k / queryScale) := by ring
      _ ≤ 10 * Real.rpow delta (-(kMin : ℝ) / (N : ℝ)) := by gcongr
      _ ≤ 10 * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by gcongr
  · have hkGreater : k > kMin := by omega
    have hprevious' : finiteGridScaleVal delta N (k - 1) < queryScale :=
      hprevious hkGreater
    have hquotient : finiteGridScaleVal delta N k / queryScale <
        finiteGridScaleVal delta N k /
          finiteGridScaleVal delta N (k - 1) :=
      div_lt_div_of_pos_left (hgridPos k) (hgridPos (k - 1)) hprevious'
    have hstep : finiteGridScaleVal delta N k /
        finiteGridScaleVal delta N (k - 1) =
          Real.rpow delta (-(1 / (N : ℝ))) := by
      dsimp only [finiteGridScaleVal]
      have hkOne : 1 ≤ k := by omega
      have hexponent :
          (1 - (k : ℝ) / (N : ℝ)) -
              (1 - ((k - 1 : ℕ) : ℝ) / (N : ℝ)) =
            -(1 / (N : ℝ)) := by
        simp [Nat.cast_sub hkOne] <;> field_simp [hN.ne'] <;> ring
      rw [hrpowDiv, hexponent]
    have hfirst : finiteGridScaleVal delta N k / queryScale ≤
        Real.rpow delta (-(1 / (N : ℝ))) := by
      rw [hstep] at hquotient
      exact hquotient.le
    have hexponent : -(1 / (N : ℝ)) ≥
        -midLoss - 1 / (N : ℝ) := by linarith
    have hrpow : Real.rpow delta (-(1 / (N : ℝ))) ≤
        Real.rpow delta (-midLoss - 1 / (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hexponent
    calc
      (10 : ℝ) * finiteGridScaleVal delta N k / queryScale =
          10 * (finiteGridScaleVal delta N k / queryScale) := by ring
      _ ≤ 10 * Real.rpow delta (-(1 / (N : ℝ))) := by gcongr
      _ ≤ 10 * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by gcongr

/-- Above the last grid scale, the trivial diameter bound is absorbed by the
final loss budget. -/
lemma finiteGridScale_fine_absorption_bound
    {delta midLoss outputLoss : ℝ} {N kMax : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hN : 0 < (N : ℝ))
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
    (habsorb :
      (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss))
    (queryScale : ℝ) (hquery : 0 < queryScale)
    (hqueryGrid : finiteGridScaleVal delta N kMax < queryScale) :
    (10 : ℝ) / queryScale ≤ Real.rpow delta (-outputLoss) / 10 := by
  have hgridPos : 0 < finiteGridScaleVal delta N kMax :=
    Real.rpow_pos_of_pos hdelta _
  have hinv : 1 / queryScale < 1 / finiteGridScaleVal delta N kMax :=
    one_div_lt_one_div_of_lt hgridPos hqueryGrid
  have hgridInv : 1 / finiteGridScaleVal delta N kMax =
      Real.rpow delta (-(1 - (kMax : ℝ) / (N : ℝ))) := by
    dsimp only [finiteGridScaleVal]
    rw [one_div]
    exact (Real.rpow_neg hdelta.le _).symm
  have hkBound : (kMax : ℝ) / (N : ℝ) ≥
      1 - midLoss - 1 / (N : ℝ) := by
    calc
      (kMax : ℝ) / (N : ℝ) ≥
          ((N : ℝ) * (1 - midLoss) - 1) / (N : ℝ) := by
            exact div_le_div_of_nonneg_right hkMaxLower hN.le
      _ = 1 - midLoss - 1 / (N : ℝ) := by
        field_simp [hN.ne'] <;> ring
  have hexponent : -(1 - (kMax : ℝ) / (N : ℝ)) ≥
      -midLoss - 1 / (N : ℝ) := by linarith
  have hrpow :
      Real.rpow delta (-(1 - (kMax : ℝ) / (N : ℝ))) ≤
        Real.rpow delta (-midLoss - 1 / (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hexponent
  have hinvBound : 1 / queryScale ≤
      Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by
    calc
      1 / queryScale ≤ 1 / finiteGridScaleVal delta N kMax := hinv.le
      _ = Real.rpow delta (-(1 - (kMax : ℝ) / (N : ℝ))) := hgridInv
      _ ≤ Real.rpow delta (-midLoss - 1 / (N : ℝ)) := hrpow
  have hten : (10 : ℝ) / queryScale ≤
      10 * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by
    calc
      (10 : ℝ) / queryScale = 10 * (1 / queryScale) := by ring
      _ ≤ 10 * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by gcongr
  have hfinal : 10 * Real.rpow delta
        (-midLoss - 1 / (N : ℝ)) ≤
      Real.rpow delta (-outputLoss) / 10 := by
    calc
      10 * Real.rpow delta (-midLoss - 1 / (N : ℝ)) =
          (100 * Real.rpow delta (-midLoss - 1 / (N : ℝ))) / 10 := by ring
      _ ≤ Real.rpow delta (-outputLoss) / 10 := by gcongr
  exact hten.trans hfinal

/-- Finite-grid internal AD estimates on one fixed shading interpolate to the
paper AD estimate at every admissible query scale, without further pruning.
This analytic conclusion is independent of the incidence tolerance carried by
the plane map. -/
noncomputable def finite_grid_isAD_every_scale_local_ad
    {delta sigma gridLoss midLoss outputLoss : ℝ}
    {N kMin kMax : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {L : NNReal}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hlipschitz : LipschitzWith L planeMap)
    (hunit : ∀ point, ‖planeMap point‖ = 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hgridLoss : 0 < gridLoss)
    (hmidLoss : 0 < midLoss)
    (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      delta ≤ finiteGridScaleVal delta N k ∧
        finiteGridScaleVal delta N k ≤ 1)
    (hfinite : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      ∀ point : {point : Point3 // point ∈ shading.union},
        IsADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt (finiteGridScaleVal delta N k))))
          (finiteGridScaleVal delta N k) (1 - sigma)
          (Kakeya.realRpowENN delta (-gridLoss)))
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow delta
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss)) :
    ∀ queryScale : ℝ, delta ≤ queryScale → queryScale ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)))
          queryScale (1 - sigma)
          (Kakeya.realRpowENN delta (-outputLoss)) := by
  let C : ENNReal := Kakeya.realRpowENN delta (-outputLoss)
  have hlocalInternal : ∀ queryScale : ℝ,
      delta ≤ queryScale → queryScale ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        IsADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)))
          queryScale (1 - sigma) (C / 10) := by
    intro queryScale hdeltaQuery hqueryOne point
    let E := scalarProjection (planeMap point)
      (shading.union ∩ Metric.closedBall (point : Point3)
        (Real.sqrt queryScale))
    have hquery : 0 < queryScale := hdelta.trans_le hdeltaQuery
    have hEbounded : E ⊆ Set.Icc (-4 : ℝ) 4 := by
      apply scalarProjection_bounded (hunit point) E
      rintro value ⟨other, hother, rfl⟩
      exact ⟨other, hother.1, rfl⟩
    by_cases hqueryLast : queryScale ≤
        finiteGridScaleVal delta N kMax
    · let candidates : Finset ℕ :=
        (Finset.Icc kMin kMax).filter
          (fun k => queryScale ≤ finiteGridScaleVal delta N k)
      have hcandidates : candidates.Nonempty := by
        refine ⟨kMax, Finset.mem_filter.mpr ⟨?_, hqueryLast⟩⟩
        simp [Finset.mem_Icc, hkMinMax]
      let k : ℕ := candidates.min' hcandidates
      have hkMem : k ∈ candidates := Finset.min'_mem candidates hcandidates
      have hkRange : kMin ≤ k ∧ k ≤ kMax := by
        simpa [candidates, Finset.mem_filter] using
          (Finset.mem_filter.mp hkMem).1
      have hqueryGrid : queryScale ≤ finiteGridScaleVal delta N k :=
        (Finset.mem_filter.mp hkMem).2
      have hball : Metric.closedBall (point : Point3)
          (Real.sqrt queryScale) ⊆
          Metric.closedBall (point : Point3)
            (Real.sqrt (finiteGridScaleVal delta N k)) := by
        intro other hother
        exact hother.trans (Real.sqrt_le_sqrt hqueryGrid)
      have hset : E ⊆
          scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt (finiteGridScaleVal delta N k))) := by
        rintro value ⟨other, hother, rfl⟩
        exact ⟨other, ⟨hother.1, hball hother.2⟩, rfl⟩
      have hweaken :=
        ((hfinite k hkRange point).mono hset).weaken_scale
          hquery hqueryGrid (hgridAdmissible k hkRange).2
      have hprevious : k > kMin →
          queryScale > finiteGridScaleVal delta N (k - 1) := by
        intro hkGreater
        have hnotMem : k - 1 ∉ candidates := by
          intro hmem
          have hminimum := Finset.min'_le candidates (k - 1) hmem
          omega
        have hrange : k - 1 ∈ Finset.Icc kMin kMax := by
          simp [Finset.mem_Icc] <;> omega
        have hnot : ¬ queryScale ≤
            finiteGridScaleVal delta N (k - 1) := by
          intro hle
          exact hnotMem (Finset.mem_filter.mpr ⟨hrange, hle⟩)
        exact not_le.mp hnot
      have hfactor := finiteGridScale_interpolation_factor_bound
        hdelta hdeltaOne hN hmidLoss hkMin hkRange queryScale hquery
        hdeltaQuery hqueryGrid hprevious
      have hrpowAdd :
          Real.rpow delta (-gridLoss) *
              Real.rpow delta (-midLoss - 1 / (N : ℝ)) =
            Real.rpow delta
              (-gridLoss - midLoss - 1 / (N : ℝ)) := by
        have h : Real.rpow delta
              ((-gridLoss) + (-midLoss - 1 / (N : ℝ))) =
            Real.rpow delta (-gridLoss) *
              Real.rpow delta (-midLoss - 1 / (N : ℝ)) :=
          Real.rpow_add hdelta (-gridLoss)
            (-midLoss - 1 / (N : ℝ))
        have hexponent :
            (-gridLoss) + (-midLoss - 1 / (N : ℝ)) =
              -gridLoss - midLoss - 1 / (N : ℝ) := by ring
        rw [hexponent] at h
        exact h.symm
      have hfactorNonnegative : 0 ≤
          (10 : ℝ) * finiteGridScaleVal delta N k / queryScale := by
        exact div_nonneg
          (mul_nonneg (by norm_num)
            (Real.rpow_pos_of_pos hdelta _).le)
          hquery.le
      have hreal :
          Real.rpow delta (-gridLoss) *
              ((10 : ℝ) * finiteGridScaleVal delta N k / queryScale) ≤
            Real.rpow delta (-outputLoss) / 10 := by
        have hintermediate :
            10 * Real.rpow delta
                (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
              Real.rpow delta (-outputLoss) / 10 := by
          calc
            10 * Real.rpow delta
                (-gridLoss - midLoss - 1 / (N : ℝ)) =
                (100 * Real.rpow delta
                  (-gridLoss - midLoss - 1 / (N : ℝ))) / 10 := by ring
            _ ≤ Real.rpow delta (-outputLoss) / 10 := by gcongr
        calc
          Real.rpow delta (-gridLoss) *
                ((10 : ℝ) * finiteGridScaleVal delta N k / queryScale)
              ≤ Real.rpow delta (-gridLoss) *
                  (10 * Real.rpow delta
                    (-midLoss - 1 / (N : ℝ))) := by
                    exact mul_le_mul_of_nonneg_left hfactor
                      (Real.rpow_pos_of_pos hdelta _).le
          _ = 10 * Real.rpow delta
                (-gridLoss - midLoss - 1 / (N : ℝ)) := by
                  rw [← hrpowAdd]
                  ring
          _ ≤ Real.rpow delta (-outputLoss) / 10 := hintermediate
      have hconstant :
          Kakeya.realRpowENN delta (-gridLoss) *
              ENNReal.ofReal
                ((10 : ℝ) * finiteGridScaleVal delta N k / queryScale) ≤
            C / 10 := by
        simp only [Kakeya.realRpowENN, C]
        have hmul :
            ENNReal.ofReal (Real.rpow delta (-gridLoss)) *
                ENNReal.ofReal
                  ((10 : ℝ) * finiteGridScaleVal delta N k / queryScale) =
              ENNReal.ofReal
                (Real.rpow delta (-gridLoss) *
                  ((10 : ℝ) * finiteGridScaleVal delta N k / queryScale)) := by
          exact (ENNReal.ofReal_mul
            (Real.rpow_nonneg hdelta.le (-gridLoss))).symm
        rw [hmul]
        have hdiv : ENNReal.ofReal
              (Real.rpow delta (-outputLoss) / 10) =
            ENNReal.ofReal (Real.rpow delta (-outputLoss)) / 10 :=
          (ofReal_div10 (Real.rpow_nonneg hdelta.le _)).symm
        rw [← hdiv]
        exact ENNReal.ofReal_le_ofReal hreal
      exact hweaken.mono_constant hconstant
    · have hqueryGrid : finiteGridScaleVal delta N kMax < queryScale :=
        lt_of_not_ge hqueryLast
      have htrivial : IsADSet1 E queryScale (1 - sigma)
          (ENNReal.ofReal (10 / queryScale)) :=
        IsADSet1.trivial_bound hEbounded hquery hqueryOne
          (by linarith) (by linarith)
      have hbound : (10 : ℝ) / queryScale ≤
          Real.rpow delta (-outputLoss) / 10 :=
        finiteGridScale_fine_absorption_bound
          hdelta hdeltaOne hN hkMaxLower habsorbFine
          queryScale hquery hqueryGrid
      have hconstant : ENNReal.ofReal ((10 : ℝ) / queryScale) ≤
          C / 10 := by
        simp only [Kakeya.realRpowENN, C]
        have hdiv : ENNReal.ofReal
              (Real.rpow delta (-outputLoss) / 10) =
            ENNReal.ofReal (Real.rpow delta (-outputLoss)) / 10 :=
          (ofReal_div10 (Real.rpow_nonneg hdelta.le _)).symm
        rw [← hdiv]
        exact ENNReal.ofReal_le_ofReal hbound
      exact htrivial.mono_constant hconstant
  have houtputNonnegative : 0 ≤ Real.rpow delta (-outputLoss) :=
    (Real.rpow_pos_of_pos hdelta _).le
  have hCReal : C = ENNReal.ofReal (Real.rpow delta (-outputLoss)) := rfl
  have hCDiv : C / 10 =
      ENNReal.ofReal (Real.rpow delta (-outputLoss) / 10) := by
    rw [hCReal]
    exact ofReal_div10 houtputNonnegative
  have hCFinite : C / 10 ≠ ⊤ := by
    rw [hCDiv]
    exact ENNReal.ofReal_ne_top
  have hcancel : (10 : ENNReal) * (C / 10) = C := by
    rw [hCDiv]
    let x : ℝ := Real.rpow delta (-outputLoss) / 10
    have hx : 0 ≤ x := by positivity
    have hmul : (10 : ENNReal) * ENNReal.ofReal x =
        ENNReal.ofReal ((10 : ℝ) * x) := by
      have hten : (10 : ENNReal) = ENNReal.ofReal (10 : ℝ) := by norm_cast
      rw [hten, ENNReal.ofReal_mul (by norm_num)]
    rw [hmul]
    have hreal : (10 : ℝ) * x = Real.rpow delta (-outputLoss) := by
      dsimp only [x]
      ring
    rw [hreal, hCReal]
  intro queryScale hdeltaQuery hqueryOne point
  have hinternal := hlocalInternal queryScale hdeltaQuery hqueryOne point
  have hpaper := pure_wz2_paper_ad_bridge.2
    _ queryScale (1 - sigma) (C / 10)
    (hdelta.trans_le hdeltaQuery) hqueryOne hCFinite hinternal
  simpa [hcancel] using hpaper

/-- Compatibility wrapper for consumers whose incidence tolerance is exactly
the fine tube scale. -/
noncomputable def finite_grid_isAD_to_relaxed_local_grain
    {delta sigma gridLoss midLoss outputLoss : ℝ}
    {N kMin kMax : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {L : NNReal}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hlipschitz : LipschitzWith L planeMap)
    (hunit : ∀ point, ‖planeMap point‖ = 1)
    (hincidence : ∀ index point, ∀ hpoint : point ∈ shading.carrier index,
      |inner ℝ (family.tube index).direction
        (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hgridLoss : 0 < gridLoss)
    (hmidLoss : 0 < midLoss)
    (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      delta ≤ finiteGridScaleVal delta N k ∧
        finiteGridScaleVal delta N k ≤ 1)
    (hfinite : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      ∀ point : {point : Point3 // point ∈ shading.union},
        IsADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt (finiteGridScaleVal delta N k))))
          (finiteGridScaleVal delta N k) (1 - sigma)
          (Kakeya.realRpowENN delta (-gridLoss)))
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow delta
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss)) :
    PureWZ2RelaxedLocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss)) L where
  planeMap := planeMap
  planeMap_lipschitz := hlipschitz
  planeMap_unit := hunit
  planeMap_incidence := hincidence
  local_ad := finite_grid_isAD_every_scale_local_ad
    planeMap hlipschitz hunit hdelta hdeltaOne hsigma hsigmaOne hgridLoss
    hmidLoss hN hkMin hkMinMax hkMaxLower hgridAdmissible hfinite
    habsorbInterpolation habsorbFine

/-- Combine the paper's LOW trivial estimate and a caller-supplied HIGH
Córdoba estimate at every finite grid scale.  The shading and plane map stay
fixed throughout; the two explicit absorption hypotheses are the complete
constant bookkeeping before interpolation. -/
noncomputable def finite_grid_low_high_every_scale_local_ad
    {delta sigma coarseScale gridLoss midLoss outputLoss : ℝ}
    {N kMin kMax : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {L : NNReal}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hlipschitz : LipschitzWith L planeMap)
    (hunit : ∀ point, ‖planeMap point‖ = 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hcoarse : 0 < coarseScale)
    (hcoarseSmall : coarseScale ≤ 1 / 10000)
    (hgridLoss : 0 < gridLoss)
    (hmidLoss : 0 < midLoss)
    (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      delta ≤ finiteGridScaleVal delta N k ∧
        finiteGridScaleVal delta N k ≤ 1)
    (highConstant : ENNReal)
    (hhigh : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      finiteGridScaleVal delta N k < 5 * coarseScale ^ 2 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt (finiteGridScaleVal delta N k))))
          (finiteGridScaleVal delta N k) (1 - sigma) highConstant)
    (hlowAbsorb : Kakeya.realRpowENN coarseScale (-1) ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (hhighAbsorb : 10 * highConstant ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow delta
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss)) :
    ∀ queryScale : ℝ, delta ≤ queryScale → queryScale ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)))
          queryScale (1 - sigma)
          (Kakeya.realRpowENN delta (-outputLoss)) := by
  apply finite_grid_isAD_every_scale_local_ad
    planeMap hlipschitz hunit hdelta hdeltaOne hsigma
    hsigmaOne hgridLoss hmidLoss hN hkMin hkMinMax hkMaxLower
    hgridAdmissible
  · intro k hk point
    let queryScale := finiteGridScaleVal delta N k
    let E := scalarProjection (planeMap point)
      (shading.union ∩ Metric.closedBall (point : Point3)
        (Real.sqrt queryScale))
    have hquery : 0 < queryScale := Real.rpow_pos_of_pos hdelta _
    have hEbounded : E ⊆ Set.Icc (-4 : ℝ) 4 := by
      apply scalarProjection_bounded (hunit point) E
      rintro value ⟨other, hother, rfl⟩
      exact ⟨other, hother.1, rfl⟩
    by_cases hlow : 5 * coarseScale ^ 2 ≤ queryScale
    · have hcenter : ∃ center : ℝ,
          E ⊆ Set.Icc (center - Real.sqrt queryScale)
            (center + Real.sqrt queryScale) := by
        let center : ℝ := inner ℝ (point : Point3) (planeMap point)
        refine ⟨center, ?_⟩
        rintro value ⟨other, hother, rfl⟩
        have hdist : ‖other - (point : Point3)‖ ≤
            Real.sqrt queryScale := by
          simpa [dist_eq_norm] using hother.2
        have hinner :
            |inner ℝ other (planeMap point) - center| ≤
              Real.sqrt queryScale := by
          have hrewrite : inner ℝ other (planeMap point) - center =
              inner ℝ (other - (point : Point3)) (planeMap point) := by
            simp [center, inner_sub_left]
          rw [hrewrite]
          calc
            |inner ℝ (other - (point : Point3)) (planeMap point)|
                ≤ ‖other - (point : Point3)‖ * ‖planeMap point‖ :=
                  abs_real_inner_le_norm _ _
            _ = ‖other - (point : Point3)‖ := by rw [hunit point]; ring
            _ ≤ Real.sqrt queryScale := hdist
        rcases abs_le.mp hinner with ⟨hleft, hright⟩
        exact ⟨by linarith, by linarith⟩
      exact (low_case_trivial_ad_v2 hsigma hsigmaOne hcoarse
        hcoarseSmall hquery hlow E hEbounded hcenter).mono_constant
          hlowAbsorb
    · have hpaper := hhigh k hk (lt_of_not_ge hlow) point
      have hinternal :=
        pure_wz2_paper_ad_bridge.1 E queryScale (1 - sigma)
          highConstant hEbounded hpaper
      exact hinternal.mono_constant hhighAbsorb
  · exact habsorbInterpolation
  · exact habsorbFine

/-- Compatibility wrapper for the fine-incidence relaxed package. -/
noncomputable def finite_grid_low_high_to_relaxed_local_grain
    {delta sigma coarseScale gridLoss midLoss outputLoss : ℝ}
    {N kMin kMax : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {L : NNReal}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hlipschitz : LipschitzWith L planeMap)
    (hunit : ∀ point, ‖planeMap point‖ = 1)
    (hincidence : ∀ index point, ∀ hpoint : point ∈ shading.carrier index,
      |inner ℝ (family.tube index).direction
        (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hcoarse : 0 < coarseScale)
    (hcoarseSmall : coarseScale ≤ 1 / 10000)
    (hgridLoss : 0 < gridLoss)
    (hmidLoss : 0 < midLoss)
    (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      delta ≤ finiteGridScaleVal delta N k ∧
        finiteGridScaleVal delta N k ≤ 1)
    (highConstant : ENNReal)
    (hhigh : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      finiteGridScaleVal delta N k < 5 * coarseScale ^ 2 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt (finiteGridScaleVal delta N k))))
          (finiteGridScaleVal delta N k) (1 - sigma) highConstant)
    (hlowAbsorb : Kakeya.realRpowENN coarseScale (-1) ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (hhighAbsorb : 10 * highConstant ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow delta
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss)) :
    PureWZ2RelaxedLocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss)) L where
  planeMap := planeMap
  planeMap_lipschitz := hlipschitz
  planeMap_unit := hunit
  planeMap_incidence := hincidence
  local_ad := finite_grid_low_high_every_scale_local_ad
    planeMap hlipschitz hunit hdelta hdeltaOne hsigma hsigmaOne hcoarse
    hcoarseSmall hgridLoss hmidLoss hN hkMin hkMinMax hkMaxLower
    hgridAdmissible highConstant hhigh hlowAbsorb hhighAbsorb
    habsorbInterpolation habsorbFine

end Kakeya.Assouad.PureWZ2

end
