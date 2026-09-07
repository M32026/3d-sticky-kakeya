import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgCombination
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HardRegimeHelper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaLogAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DirectionalPointPacking
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Canonical Property-(P) parameters on one coarse family

This module chooses the high-multiplicity Property-(P) parameters directly
on an arbitrary sufficiently small cropped extremal family.  In particular,
it does not require a surviving Section 6 fine cover after a coarse-family
regularization.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- All Property-(P) inputs used by the same-family canonical grain
assembler, with the quantitative choices recorded explicitly. -/
structure CanonicalCoarsePropertyPParameters
    {sigma loss L : ℝ}
    {family : Kakeya.Streamlined.TubeFamily L}
    (shading : WZ1PaperTubeShading family) where
  epsilon₁ : ℝ
  epsilon₃ : ℝ
  tau : ℝ
  K : ℕ
  multiplicity : ℕ
  propP : PureWZ2PropertyPData
    (sigma := sigma) (L := L) (tau := tau)
    (coarseShading := shading) epsilon₁ epsilon₃
  tau_def : tau = L * Real.sqrt 3
  tau_pos : 0 < tau
  tau_le_twenty : tau ≤ 20 * L
  scale_le_tau : L ≤ tau
  tau_sq : tau ^ 2 ≤ 4 * L
  tau_le_one : tau ≤ 1
  epsilon₁_pos : 0 < epsilon₁
  epsilon₃_pos : 0 < epsilon₃
  epsilon_sum : epsilon₁ + epsilon₃ < 1
  logScale : ℝ
  scale_le_logScale : L ≤ logScale
  log_absorption :
    0 < epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108
  propertyThree_full :
    ∀ parent : Fin family.card, ∀ point : Point3,
      point ∈ propP.propertyThree.carrier parent →
        Kakeya.realRpowENN L (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau ≤
          volume (propP.propertyThree.carrier parent ∩
            Metric.closedBall point tau)
  ax_condition :
    4 * (6 * L) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃)) ^ 2

/-- A fixed loss below `sigma / 4` admits uniform canonical Property-(P)
parameters on every sufficiently small cropped extremal family, provided the
canonical close-direction count is available.  This is the ordinary-family
entry point used after Proposition 6.3 rescaling. -/
theorem exists_canonical_coarse_property_p_parameters_of_close_count
    (sigma loss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hloss : 0 < loss) (hlossQuarter : loss < sigma / 4) :
    ∃ scale0 : ℝ, 0 < scale0 ∧ scale0 ≤ 1 / 10000 ∧
      ∀ {L : ℝ}
        {family : Kakeya.Streamlined.TubeFamily L}
        {shading : WZ1PaperTubeShading family},
        WZ2PaperCroppedIsExtremal sigma loss family shading →
        WZ1PaperIsLineClass family →
        (∀ (K : ℕ),
          K = Nat.ceil (Real.rpow L
            (-2 * ((sigma - 2 * loss) / 20))) →
          1 ≤ K → (K : ℝ) * L ≤ 1 / 2 →
          ∀ (point : Point3), point ∈ shading.union →
            ∀ (index : Fin family.card),
              point ∈ shading.carrier index →
                (paperCloseDirectionCount shading point index
                    ((K : ℝ) * L) : ENNReal) ≤
                  ((proposition63DirectionalPointPackingConstant *
                    K ^ 2 : ℕ) : ENNReal)) →
        0 < L → L ≤ scale0 →
        Nonempty (CanonicalCoarsePropertyPParameters
          (sigma := sigma) (loss := loss) shading) := by
  let epsilon₁ : ℝ := (sigma - 2 * loss) / 20
  let epsilon₃ : ℝ := 1 - 2 * epsilon₁
  have hepsilon₁ : 0 < epsilon₁ := by
    dsimp only [epsilon₁]
    linarith
  have hepsilon₁Half : epsilon₁ < 1 / 2 := by
    dsimp only [epsilon₁]
    linarith
  have hepsilon₃ : 0 < epsilon₃ := by
    dsimp only [epsilon₃]
    linarith
  have hepsilonSum : epsilon₁ + epsilon₃ < 1 := by
    dsimp only [epsilon₃]
    linarith
  rcases proposition63_directional_multiplicity_exponent_arithmetic
      sigma loss hsigma hloss hlossQuarter with
    ⟨averageScale, haverageScale, haverageScaleOne, haverage⟩
  rcases cordoba_log_absorption_exists hepsilon₁ with
    ⟨logScale, hlogScale, hlogScaleOne, hlog⟩
  rcases cordoba_ax_condition_exists hepsilon₁ hepsilon₁Half with
    ⟨axisScale, haxisScale, haxisScaleOne, haxis⟩
  let cellScale : ℝ := Real.rpow 3 (-(20 / sigma))
  have hcellScale : 0 < cellScale := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  let scale0 : ℝ :=
    min (1 / 10000)
      (min averageScale (min logScale (min axisScale cellScale)))
  have hscale0 : 0 < scale0 := by
    dsimp only [scale0]
    positivity
  have hscale0Small : scale0 ≤ 1 / 10000 := min_le_left _ _
  refine ⟨scale0, hscale0, hscale0Small, ?_⟩
  intro L family shading hextremal hline hclose hL hLBound
  have hLSmall : L ≤ 1 / 10000 := hLBound.trans hscale0Small
  have hLOne : L ≤ 1 := hLSmall.trans (by norm_num)
  have hLAverage : L ≤ averageScale := by
    exact hLBound.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have hLLog : L ≤ logScale := by
    exact hLBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have hLAxis : L ≤ axisScale := by
    exact hLBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  have hLCell : L ≤ cellScale := by
    exact hLBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_right _ _)
  let tau : ℝ := L * Real.sqrt 3
  let K : ℕ := Nat.ceil (Real.rpow L (-2 * epsilon₁))
  let multiplicity : ℕ :=
    12 * max (2 * 4 * 601 ^ 3 * 12001 ^ 3)
      (proposition63DirectionalPointPackingConstant * K ^ 2) + 12
  have htau : tau = L * Real.sqrt 3 := rfl
  have htauPos : 0 < tau := by
    dsimp only [tau]
    positivity
  have hLtau : L ≤ tau := by
    dsimp only [tau]
    have hsqrt : 1 ≤ Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    nlinarith
  have htauTwenty : tau ≤ 20 * L := by
    dsimp only [tau]
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    nlinarith
  have htauSq : tau ^ 2 ≤ 4 * L := by
    dsimp only [tau]
    have hsqrt : (Real.sqrt 3) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    rw [mul_pow, hsqrt]
    nlinarith
  have htauOne : tau ≤ 1 := by
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    dsimp only [tau]
    nlinarith
  have hKOne : 1 ≤ K := by
    have hexponentNonpositive : -2 * epsilon₁ ≤ 0 := by linarith
    have hone : 1 ≤ Real.rpow L (-2 * epsilon₁) := by
      have hpower : Real.rpow L 0 ≤ Real.rpow L (-2 * epsilon₁) :=
        Real.rpow_le_rpow_of_exponent_ge hL hLOne
          hexponentNonpositive
      simpa using hpower
    have hcast : (1 : ℝ) ≤ (K : ℝ) :=
      hone.trans (Nat.le_ceil _)
    exact_mod_cast hcast
  have hKLSmall : (K : ℝ) * L ≤ 1 / 2 := by
    have hKUpper : (K : ℝ) ≤ Real.rpow L (-2 * epsilon₁) + 1 := by
      dsimp only [K]
      exact (Nat.ceil_lt_add_one (Real.rpow_nonneg hL.le _)).le
    have hpower :
        Real.rpow L (-2 * epsilon₁) * L =
          Real.rpow L epsilon₃ := by
      have hadd :
          Real.rpow L (-2 * epsilon₁) * Real.rpow L 1 =
            Real.rpow L ((-2 * epsilon₁) + 1) :=
        (Real.rpow_add hL (-2 * epsilon₁) 1).symm
      have hone : Real.rpow L 1 = L := Real.rpow_one L
      have hadd' :
          Real.rpow L (-2 * epsilon₁) * L =
            Real.rpow L ((-2 * epsilon₁) + 1) := by
        rw [hone] at hadd
        exact hadd
      rw [hadd']
      congr 1
      dsimp only [epsilon₃]
      ring
    have hepsilon₃Lower : 9 / 10 ≤ epsilon₃ := by
      dsimp only [epsilon₃, epsilon₁]
      linarith
    have hpowerSmall : Real.rpow L epsilon₃ ≤ 1 / 4 := by
      calc
        Real.rpow L epsilon₃ ≤ Real.rpow L (9 / 10 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hL hLOne hepsilon₃Lower
        _ ≤ Real.rpow (1 / 10000 : ℝ) (9 / 10 : ℝ) :=
          Real.rpow_le_rpow hL.le hLSmall (by norm_num)
        _ ≤ Real.rpow (1 / 10000 : ℝ) (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
            (by norm_num)
        _ = 1 / 100 := by
          calc
            Real.rpow (1 / 10000 : ℝ) (1 / 2 : ℝ) =
                Real.sqrt (1 / 10000 : ℝ) :=
              (Real.sqrt_eq_rpow _).symm
            _ = 1 / 100 := by
              rw [Real.sqrt_eq_cases] <;> norm_num
        _ ≤ 1 / 4 := by norm_num
    calc
      (K : ℝ) * L ≤ (Real.rpow L (-2 * epsilon₁) + 1) * L := by
        gcongr
      _ = Real.rpow L epsilon₃ + L := by rw [add_mul, hpower, one_mul]
      _ ≤ 1 / 4 + 1 / 10000 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hmPos : 0 < multiplicity := by
    dsimp only [multiplicity]
    positivity
  have hmPacking :
      (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) <
        (multiplicity : ENNReal) := by
    exact_mod_cast (show
      (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ℕ) < multiplicity by
        dsimp only [multiplicity]
        omega)
  have hmGeneral :
      ((proposition63DirectionalPointPackingConstant * K ^ 2 : ℕ) :
          ENNReal) <
      (multiplicity : ENNReal) := by
    exact_mod_cast (show
      proposition63DirectionalPointPackingConstant * K ^ 2 < multiplicity by
      dsimp only [multiplicity]
      omega)
  have hmDef : multiplicity =
      proposition63DirectionalMultiplicity sigma loss L := by
    rfl
  have hmBound :
      (multiplicity : ℝ) * L ^ (sigma - 3 * loss) < 1 / 8 := by
    rw [hmDef]
    exact haverage L hL hLAverage
  have hvolumeTop : volume shading.union ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Kakeya.realRpowENN])
      hextremal.volume_upper
  have hmassTop : shading.mass ≠ ⊤ := by
    change (∑ index : Fin family.card, volume (shading.carrier index)) ≠ ⊤
    apply ENNReal.sum_ne_top.2
    intro index _
    have hcarrier : volume (shading.carrier index) ≤
        volume (Kakeya.Streamlined.axisBox 2 2 2) :=
      measure_mono <| (shading.subset_body index).trans
        Set.inter_subset_right
    exact ne_top_of_le_ne_top (by
      rw [Kakeya.Streamlined.volume_axisBox
        2 2 2 (by norm_num) (by norm_num) (by norm_num)]
      exact ENNReal.ofReal_ne_top) hcarrier
  have haverageMass :
      (multiplicity : ENNReal) * volume shading.union <
        (1 / 2 : ENNReal) * shading.mass :=
    h_avg_from_extremal_line_class hextremal hline multiplicity hL
      (hLSmall.trans (by norm_num)) hmBound
  have hKappa : Real.rpow L epsilon₃ ≤ (K : ℝ) * L := by
    have hpower :
        Real.rpow L epsilon₃ = Real.rpow L (-2 * epsilon₁) * L := by
      have hadd :
          Real.rpow L (-2 * epsilon₁) * Real.rpow L 1 =
            Real.rpow L ((-2 * epsilon₁) + 1) :=
        (Real.rpow_add hL (-2 * epsilon₁) 1).symm
      have hone : Real.rpow L 1 = L := Real.rpow_one L
      have hadd' :
          Real.rpow L (-2 * epsilon₁) * L =
            Real.rpow L ((-2 * epsilon₁) + 1) := by
        rw [hone] at hadd
        exact hadd
      rw [hadd']
      congr 1
      dsimp only [epsilon₃]
      ring
    rw [hpower]
    gcongr
    exact Nat.le_ceil _
  let cellConstant : ℝ := Real.rpow 3 (20 / sigma)
  have hcellIdentity : 1 / cellConstant = cellScale := by
    dsimp only [cellConstant, cellScale]
    have honeDiv :
        1 / Real.rpow 3 (20 / sigma) =
          (Real.rpow 3 (20 / sigma))⁻¹ := by simp
    rw [honeDiv]
    exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)
      (20 / sigma)).symm
  have hcellReal :
      Real.rpow L (2 + 2 * epsilon₁) * tau ≤
        Real.rpow L 3 := by
    apply cell_full_real_ineq L tau sigma loss epsilon₁ cellConstant
      hL (by simpa [hcellIdentity] using hLCell) (by linarith) hsigma
      rfl rfl htau
  have hcell :
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
        Kakeya.realRpowENN L 3 := by
    rw [show Kakeya.realRpowENN L (2 + 2 * epsilon₁) *
        ENNReal.ofReal tau =
      ENNReal.ofReal (Real.rpow L (2 + 2 * epsilon₁) * tau) by
        simp only [Kakeya.realRpowENN]
        exact (ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)).symm]
    exact ENNReal.ofReal_mono hcellReal
  let propP : PureWZ2PropertyPData
      (sigma := sigma) (L := L) (tau := tau)
      (coarseShading := shading) epsilon₁ epsilon₃ :=
    pureWz2_propertyP_refinement_general_of_close_count_lt hextremal hline
      epsilon₁ epsilon₃ hepsilon₁ hepsilon₃ hepsilonSum
      hL hLSmall htauPos hLtau (by rw [htau]) htauSq htauOne
      K hKOne hKLSmall multiplicity
      (fun point hpoint index hindex =>
        (hclose K rfl hKOne hKLSmall point hpoint index hindex).trans_lt
          hmGeneral)
      hmPos hmPacking
      hmassTop hvolumeTop haverageMass hKappa hcell
  have hpropertyFull :
      ∀ parent : Fin family.card, ∀ point : Point3,
        point ∈ propP.propertyThree.carrier parent →
          Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau) := by
    exact propP.propertyOne_full
  have haxisCondition := haxis L hL hLAxis epsilon₃ (by rfl)
  exact ⟨{
    epsilon₁ := epsilon₁
    epsilon₃ := epsilon₃
    tau := tau
    K := K
    multiplicity := multiplicity
    propP := propP
    tau_def := htau
    tau_pos := htauPos
    tau_le_twenty := htauTwenty
    scale_le_tau := hLtau
    tau_sq := htauSq
    tau_le_one := htauOne
    epsilon₁_pos := hepsilon₁
    epsilon₃_pos := hepsilon₃
    epsilon_sum := hepsilonSum
    logScale := logScale
    scale_le_logScale := hLLog
    log_absorption := fun _ => hlog
    propertyThree_full := hpropertyFull
    ax_condition := haxisCondition
  }⟩

/-- Cropped top-level CWA supplies the close-direction input needed by the
canonical Property-(P) construction.  The displayed inequality is the one
power-loss absorption left to the outer small-scale argument. -/
theorem exists_canonical_coarse_property_p_parameters_of_cwa
    (sigma loss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hloss : 0 < loss) (hlossQuarter : loss < sigma / 4) :
    ∃ scale0 : ℝ, 0 < scale0 ∧ scale0 ≤ 1 / 10000 ∧
      ∀ {L : ℝ}
        {family : Kakeya.Streamlined.TubeFamily L}
        {shading : WZ1PaperTubeShading family}
        {C : ENNReal},
        WZ2PaperCroppedIsExtremal sigma loss family shading →
        WZ1PaperIsLineClass family →
        WZ2PaperConvexWolffBound family C →
        (let epsilon₁ := (sigma - 2 * loss) / 20
         let K := Nat.ceil (Real.rpow L (-2 * epsilon₁))
         C * ENNReal.ofReal (10000 * ((K : ℝ) * L) ^ 2) *
              family.enncard ≤
            ((proposition63DirectionalPointPackingConstant * K ^ 2 : ℕ) :
              ENNReal)) →
        0 < L → L ≤ scale0 →
        Nonempty (CanonicalCoarsePropertyPParameters
          (sigma := sigma) (loss := loss) shading) := by
  rcases exists_canonical_coarse_property_p_parameters_of_close_count
      sigma loss hsigma hsigmaOne hloss hlossQuarter with
    ⟨scale0, hscale0, hscale0Small, hparameters⟩
  refine ⟨scale0, hscale0, hscale0Small, ?_⟩
  intro L family shading C hextremal hline hCWA hcloseAbsorb hL hLBound
  apply hparameters hextremal hline
      (fun K hKDef hKOne hKLSmall => ?_) hL hLBound
  intro point _hpoint index hpoint
  have hkappaPos : 0 < (K : ℝ) * L := by
    positivity
  have hkappaOne : (K : ℝ) * L ≤ 1 :=
    hKLSmall.trans (by norm_num)
  have hkappaGe : L ≤ (K : ℝ) * L := by
    have hKReal : (1 : ℝ) ≤ K := by
      exact_mod_cast hKOne
    nlinarith
  exact (paper_cwa_close_direction_count hCWA hL
      (hLBound.trans hscale0Small) ((K : ℝ) * L) hkappaPos hkappaOne
      hkappaGe
      point index hpoint).trans (by
        rw [hKDef]
        simpa only using hcloseAbsorb)

/-- Backwards-compatible entry point using historical full-line
essential-distinctness to prove the close-direction count. -/
theorem exists_canonical_coarse_property_p_parameters
    (sigma loss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hloss : 0 < loss) (hlossQuarter : loss < sigma / 4) :
    ∃ scale0 : ℝ, 0 < scale0 ∧ scale0 ≤ 1 / 10000 ∧
      ∀ {L : ℝ}
        {family : Kakeya.Streamlined.TubeFamily L}
        {shading : WZ1PaperTubeShading family},
        WZ2PaperCroppedIsExtremal sigma loss family shading →
        WZ1PaperIsEssentiallyDistinct family →
        WZ1PaperIsLineClass family →
        0 < L → L ≤ scale0 →
        Nonempty (CanonicalCoarsePropertyPParameters
          (sigma := sigma) (loss := loss) shading) := by
  rcases exists_canonical_coarse_property_p_parameters_of_close_count
      sigma loss hsigma hsigmaOne hloss hlossQuarter with
    ⟨scale0, hscale0, hscale0Small, hparameters⟩
  refine ⟨scale0, hscale0, hscale0Small, ?_⟩
  intro L family shading hextremal hdistinct hline hL hLBound
  apply hparameters hextremal hline
      (fun K _hKDef hKOne hKLSmall => ?_) hL hLBound
  intro point _hpoint index hpoint
  exact_mod_cast proposition63_close_direction_count_quadratic
    (rho := L) (K := K) hdistinct hline hL
    (hLBound.trans hscale0Small) hKOne hKLSmall point index hpoint

end Kakeya.Assouad.PureWZ2

end
