import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCWABoundaryMass

/-!
# Normalized coefficient for fixed-origin boundary pruning

Choose the slow/fast cutoff
`speed = rho * sqrt (delta / rho)`.  The slow CWA loss and the fast slab
loss are then both bounded by a fixed multiple of `sqrt (delta / rho)` times
the natural quadratic tube-mass scale.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def wz2PaperBoundaryGeometryConstant : ENNReal :=
  55296 * Kakeya.deltaTubeVolume 1

def wz2PaperBoundarySpeed (delta rho : ℝ) : ℝ :=
  rho * Real.sqrt (delta / rho)

def wz2PaperBoundaryMassCoefficient
    (delta rho speed : ℝ) (C : ENNReal) : ENNReal :=
  let boundaryCount : ENNReal :=
    (wz2PaperBoundaryIndicesInWindow rho).card
  let slowWidth : ENNReal :=
    ENNReal.ofReal (16 * (4 * speed + 49 * delta))
  let fastLoss : ENNReal :=
    ENNReal.ofReal
      (4000000 * delta ^ 3 *
        ((1 / rho) + (1 / speed)))
  (3 : ENNReal) *
    ((boundaryCount * slowWidth) *
          (C * wz2PaperBoundaryGeometryConstant) *
          Kakeya.realRpowENN delta 2 +
      fastLoss)

theorem wz2_paper_boundary_indices_in_window_card
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) :
    ((wz2PaperBoundaryIndicesInWindow rho).card : ℝ) ≤
      5 / rho := by
  let ceiling : ℤ := ⌈1 / rho⌉
  have hceilNonneg : 0 ≤ ceiling := by
    apply Int.ceil_nonneg
    positivity
  have hcardReal :
      ((Finset.Icc (-ceiling) ceiling).card : ℝ) =
        2 * (ceiling : ℝ) + 1 := by
    have hcardInt :
        ((Finset.Icc (-ceiling) ceiling).card : ℤ) =
          ceiling + 1 - (-ceiling) :=
      Int.card_Icc_of_le (-ceiling) ceiling (by omega)
    have hcardInt' :
        ((Finset.Icc (-ceiling) ceiling).card : ℤ) =
          2 * ceiling + 1 := by
      calc
        ((Finset.Icc (-ceiling) ceiling).card : ℤ) =
            ceiling + 1 - (-ceiling) := hcardInt
        _ = 2 * ceiling + 1 := by ring
    exact_mod_cast hcardInt'
  have hceilUpper :
      (ceiling : ℝ) < 1 / rho + 1 :=
    Int.ceil_lt_add_one _
  have hinvOne : 1 ≤ 1 / rho := by
    apply one_le_one_div
    · exact hrho
    · exact hrhoOne
  rw [wz2PaperBoundaryIndicesInWindow, hcardReal]
  have : 2 * (ceiling : ℝ) + 1 ≤ 5 / rho := by
    exact le_of_lt <| calc
      2 * (ceiling : ℝ) + 1 <
          2 * (1 / rho + 1) + 1 := by linarith
      _ ≤ 5 / rho := by
        field_simp [hrho.ne']
        nlinarith
  exact this

theorem wz2_paper_boundary_speed_properties
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdeltaRho : delta ≤ rho) :
    let ratio := delta / rho
    let root := Real.sqrt ratio
    let speed := wz2PaperBoundarySpeed delta rho
    0 < root ∧ root ≤ 1 ∧ 0 < speed ∧
      delta ≤ speed ∧
      delta / rho = root ^ 2 ∧
      delta / speed = root := by
  dsimp only [wz2PaperBoundarySpeed]
  let ratio := delta / rho
  let root := Real.sqrt ratio
  have hratioPos : 0 < ratio := div_pos hdelta hrho
  have hratioOne : ratio ≤ 1 :=
    (div_le_one hrho).mpr hdeltaRho
  have hrootPos : 0 < root := Real.sqrt_pos.2 hratioPos
  have hrootOne : root ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_le_sqrt hratioOne
  have hrootSq : root ^ 2 = ratio :=
    Real.sq_sqrt hratioPos.le
  have hdeltaEq : delta = rho * root ^ 2 := by
    rw [hrootSq]
    dsimp only [ratio]
    field_simp [hrho.ne']
  have hspeedPos : 0 < rho * root := mul_pos hrho hrootPos
  have hdeltaSpeed : delta ≤ rho * root := by
    rw [hdeltaEq]
    have hrootSqLe : root ^ 2 ≤ root := by
      nlinarith
    exact mul_le_mul_of_nonneg_left hrootSqLe hrho.le
  have hquotient : delta / (rho * root) = root := by
    rw [hdeltaEq]
    field_simp [hrho.ne', hrootPos.ne']
  exact
    ⟨hrootPos, hrootOne, hspeedPos, hdeltaSpeed,
      hrootSq.symm, hquotient⟩

theorem wz2_paper_boundary_mass_coefficient_normalized
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (C : ENNReal) :
    wz2PaperBoundaryMassCoefficient
        delta rho (wz2PaperBoundarySpeed delta rho) C ≤
      (24000000 : ENNReal) *
        (C * wz2PaperBoundaryGeometryConstant + 1) *
        Kakeya.realRpowENN delta 2 *
        ENNReal.ofReal (Real.sqrt (delta / rho)) := by
  let root := Real.sqrt (delta / rho)
  let speed := wz2PaperBoundarySpeed delta rho
  rcases
      wz2_paper_boundary_speed_properties
        hdelta hrho hdeltaRho with
    ⟨hrootPos, hrootOne, hspeedPos, hdeltaSpeed,
      hratioRoot, hdeltaSpeedEq⟩
  have hcardReal :=
    wz2_paper_boundary_indices_in_window_card hrho hrhoOne
  have hwidthNonneg :
      0 ≤ 16 * (4 * speed + 49 * delta) := by
    dsimp only [speed, wz2PaperBoundarySpeed]
    positivity
  have hcardWidthReal :
      ((wz2PaperBoundaryIndicesInWindow rho).card : ℝ) *
          (16 * (4 * speed + 49 * delta)) ≤
        4240 * root := by
    have hwidth :
        16 * (4 * speed + 49 * delta) ≤
          848 * speed := by
      nlinarith
    have hspeedEq : speed = rho * root := rfl
    calc
      ((wz2PaperBoundaryIndicesInWindow rho).card : ℝ) *
            (16 * (4 * speed + 49 * delta))
          ≤
        (5 / rho) * (848 * speed) := by
          gcongr
      _ = 4240 * root := by
        rw [hspeedEq]
        field_simp [hrho.ne']
        ring
  have hcardWidth :
      ((wz2PaperBoundaryIndicesInWindow rho).card : ENNReal) *
          ENNReal.ofReal
            (16 * (4 * speed + 49 * delta)) ≤
        (4240 : ENNReal) * ENNReal.ofReal root := by
    calc
      ((wz2PaperBoundaryIndicesInWindow rho).card : ENNReal) *
            ENNReal.ofReal
              (16 * (4 * speed + 49 * delta)) =
          ENNReal.ofReal
            (((wz2PaperBoundaryIndicesInWindow rho).card : ℝ) *
              (16 * (4 * speed + 49 * delta))) := by
        rw [show
          ((wz2PaperBoundaryIndicesInWindow rho).card : ENNReal) =
            ENNReal.ofReal
              ((wz2PaperBoundaryIndicesInWindow rho).card : ℝ) by
                exact (ENNReal.ofReal_natCast
                  (wz2PaperBoundaryIndicesInWindow rho).card).symm]
        exact
          (ENNReal.ofReal_mul
            (Nat.cast_nonneg
              (wz2PaperBoundaryIndicesInWindow rho).card)).symm
      _ ≤ ENNReal.ofReal (4240 * root) :=
        ENNReal.ofReal_mono hcardWidthReal
      _ = (4240 : ENNReal) * ENNReal.ofReal root := by
        rw [← ENNReal.ofReal_ofNat (n := 4240),
          ENNReal.ofReal_mul (by norm_num)]
  have hfastReal :
      4000000 * delta ^ 3 *
            ((1 / rho) + (1 / speed)) ≤
        8000000 * delta ^ 2 * root := by
    have hratioLeRoot : delta / rho ≤ root := by
      rw [hratioRoot]
      nlinarith
    have hdeltaTerm :
        delta * ((1 / rho) + (1 / speed)) ≤
          2 * root := by
      calc
        delta * ((1 / rho) + (1 / speed)) =
            delta / rho + delta / speed := by ring
        _ = delta / rho + root := by rw [hdeltaSpeedEq]
        _ ≤ root + root := by gcongr
        _ = 2 * root := by ring
    calc
      4000000 * delta ^ 3 *
            ((1 / rho) + (1 / speed)) =
          4000000 * delta ^ 2 *
            (delta * ((1 / rho) + (1 / speed))) := by ring
      _ ≤ 4000000 * delta ^ 2 * (2 * root) := by
        gcongr
      _ = 8000000 * delta ^ 2 * root := by ring
  have hdeltaSq :
      Kakeya.realRpowENN delta 2 =
        ENNReal.ofReal (delta ^ 2) := by
    simp [Kakeya.realRpowENN, Real.rpow_two]
  have hfast :
      ENNReal.ofReal
          (4000000 * delta ^ 3 *
            ((1 / rho) + (1 / speed))) ≤
        (8000000 : ENNReal) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal root := by
    calc
      ENNReal.ofReal
          (4000000 * delta ^ 3 *
            ((1 / rho) + (1 / speed)))
          ≤ ENNReal.ofReal (8000000 * delta ^ 2 * root) :=
        ENNReal.ofReal_mono hfastReal
      _ =
          (8000000 : ENNReal) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal root := by
        rw [hdeltaSq]
        calc
          ENNReal.ofReal (8000000 * delta ^ 2 * root) =
              ENNReal.ofReal (8000000 * delta ^ 2) *
                ENNReal.ofReal root := by
            exact ENNReal.ofReal_mul
              (mul_nonneg (by norm_num) (sq_nonneg delta))
          _ =
              (8000000 : ENNReal) *
                ENNReal.ofReal (delta ^ 2) *
                ENNReal.ofReal root := by
            rw [show
              ENNReal.ofReal (8000000 * delta ^ 2) =
                (8000000 : ENNReal) *
                  ENNReal.ofReal (delta ^ 2) by
              rw [← ENNReal.ofReal_ofNat (n := 8000000)]
              exact ENNReal.ofReal_mul (by norm_num)]
  let geometry := wz2PaperBoundaryGeometryConstant
  have hslow :
      (((wz2PaperBoundaryIndicesInWindow rho).card : ENNReal) *
            ENNReal.ofReal
              (16 * (4 * speed + 49 * delta))) *
          (C * geometry) *
          Kakeya.realRpowENN delta 2 ≤
        (4240 : ENNReal) * (C * geometry) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal root := by
    calc
      (((wz2PaperBoundaryIndicesInWindow rho).card : ENNReal) *
            ENNReal.ofReal
              (16 * (4 * speed + 49 * delta))) *
          (C * geometry) *
          Kakeya.realRpowENN delta 2
          ≤
        ((4240 : ENNReal) * ENNReal.ofReal root) *
          (C * geometry) *
          Kakeya.realRpowENN delta 2 := by
            gcongr
      _ =
        (4240 : ENNReal) * (C * geometry) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal root := by ring
  dsimp only [wz2PaperBoundaryMassCoefficient]
  change
    (3 : ENNReal) *
        (((((wz2PaperBoundaryIndicesInWindow rho).card : ENNReal) *
              ENNReal.ofReal
                (16 * (4 * speed + 49 * delta))) *
            (C * geometry) *
            Kakeya.realRpowENN delta 2) +
          ENNReal.ofReal
            (4000000 * delta ^ 3 *
              ((1 / rho) + (1 / speed)))) ≤ _
  calc
    (3 : ENNReal) *
        (((((wz2PaperBoundaryIndicesInWindow rho).card : ENNReal) *
              ENNReal.ofReal
                (16 * (4 * speed + 49 * delta))) *
            (C * geometry) *
            Kakeya.realRpowENN delta 2) +
          ENNReal.ofReal
            (4000000 * delta ^ 3 *
              ((1 / rho) + (1 / speed))))
        ≤
      (3 : ENNReal) *
        (((4240 : ENNReal) * (C * geometry) +
            8000000) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal root) := by
      gcongr
      calc
        (((((wz2PaperBoundaryIndicesInWindow rho).card : ENNReal) *
              ENNReal.ofReal
                (16 * (4 * speed + 49 * delta))) *
            (C * geometry) *
            Kakeya.realRpowENN delta 2) +
          ENNReal.ofReal
            (4000000 * delta ^ 3 *
              ((1 / rho) + (1 / speed))))
            ≤
          (4240 : ENNReal) * (C * geometry) *
              Kakeya.realRpowENN delta 2 *
              ENNReal.ofReal root +
            (8000000 : ENNReal) *
              Kakeya.realRpowENN delta 2 *
              ENNReal.ofReal root :=
          add_le_add hslow hfast
        _ =
          (((4240 : ENNReal) * (C * geometry) +
              8000000) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal root) := by ring
    _ ≤
      (24000000 : ENNReal) *
        (C * geometry + 1) *
        Kakeya.realRpowENN delta 2 *
        ENNReal.ofReal root := by
      have hcoefficient :
        (3 : ENNReal) *
            ((4240 : ENNReal) * (C * geometry) + 8000000)
            ≤
          (24000000 : ENNReal) * (C * geometry + 1) := by
        calc
          (3 : ENNReal) *
              ((4240 : ENNReal) * (C * geometry) + 8000000)
              =
          (12720 : ENNReal) * (C * geometry) + 24000000 := by
            ring
        _ ≤
          (24000000 : ENNReal) * (C * geometry) + 24000000 := by
            gcongr <;> norm_num
        _ =
          (24000000 : ENNReal) * (C * geometry + 1) := by
            ring
      calc
        (3 : ENNReal) *
            (((4240 : ENNReal) * (C * geometry) + 8000000) *
              Kakeya.realRpowENN delta 2 *
              ENNReal.ofReal root) =
          ((3 : ENNReal) *
              ((4240 : ENNReal) * (C * geometry) + 8000000)) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal root := by ring
        _ ≤
          ((24000000 : ENNReal) * (C * geometry + 1)) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal root := by
              gcongr
        _ =
          (24000000 : ENNReal) *
            (C * geometry + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal root := by ring

theorem wz2_paper_grid_boundary_mass_normalized
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hperiodicScale : 50 * delta ≤ rho)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho)) ≤
      family.enncard *
        ((24000000 : ENNReal) *
          (C * wz2PaperBoundaryGeometryConstant + 1) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal (Real.sqrt (delta / rho))) := by
  let speed := wz2PaperBoundarySpeed delta rho
  have hdeltaRho : delta ≤ rho := by linarith
  have hspeed :
      0 < speed :=
    (wz2_paper_boundary_speed_properties
      hdelta hrho hdeltaRho).2.2.1
  have hexact :=
    wz2_paper_grid_boundary_mass
      hdelta hdeltaSmall hrho hperiodicScale hspeed
      hline shading hcwa
  have hfactor :
      (∑ _coordinate : Fin 3,
          ((wz2PaperBoundaryIndicesInWindow rho).card *
              ((C *
                  ENNReal.ofReal
                    (16 * (4 * speed + 49 * delta)) *
                  family.enncard) *
                (55296 * Kakeya.deltaTubeVolume 1 *
                  Kakeya.realRpowENN delta 2)) +
            family.enncard *
              ENNReal.ofReal
                (4000000 * delta ^ 3 *
                  ((1 / rho) + (1 / speed))))) =
        family.enncard *
          wz2PaperBoundaryMassCoefficient
            delta rho speed C := by
    simp [wz2PaperBoundaryMassCoefficient,
      wz2PaperBoundaryGeometryConstant, Finset.sum_const]
    ring
  rw [hfactor] at hexact
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho))
        ≤
      family.enncard *
        wz2PaperBoundaryMassCoefficient delta rho speed C := hexact
    _ ≤
      family.enncard *
        ((24000000 : ENNReal) *
          (C * wz2PaperBoundaryGeometryConstant + 1) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal (Real.sqrt (delta / rho))) := by
      gcongr
      exact
        wz2_paper_boundary_mass_coefficient_normalized
          hdelta hrho hrhoOne hdeltaRho C

end Kakeya.Assouad

end
