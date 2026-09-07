import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropBoundaryMass

/-!
# Normalized aggregate crop-boundary mass

The six-face slow/fast decomposition is compressed to the scale-invariant
form needed by the `prop: sticky` absorption argument.  The numerical
constant is deliberately generous; the significant factors are the ambient
top-level CWA constant, `delta^2`, and `sqrt rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def wz2PaperCropBoundaryMassConstant : ENNReal :=
  (20000000 : ENNReal) *
    ((55296 * Kakeya.deltaTubeVolume 1) + 1)

theorem wz2_paper_subfamily_crop_boundary_mass_normalized
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (shading : WZ1PaperTubeShading selected.family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin selected.family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      wz2PaperCropBoundaryMassConstant *
        (C + 1) *
        Kakeya.realRpowENN delta 2 *
        ENNReal.ofReal (Real.sqrt rho) *
        family.enncard := by
  let root : ℝ := Real.sqrt rho
  let rootENN : ENNReal := ENNReal.ofReal root
  let geometry : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  have hrootPos : 0 < root := Real.sqrt_pos.mpr hrho
  have hrootSq : root ^ 2 = rho := by
    dsimp only [root]
    exact Real.sq_sqrt hrho.le
  have hrhoRoot : rho ≤ root := by
    have hrootOne : root ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
      exact Real.sqrt_le_sqrt hrhoOne
    nlinarith
  have hdeltaRoot : delta ≤ root :=
    hdeltaRho.trans hrhoRoot
  have hwidth :
      16 * (4 * root + 48 * delta + rho) ≤
        1600 * root := by
    nlinarith
  have hWidthENN :
      ENNReal.ofReal
          (16 * (4 * root + 48 * delta + rho)) ≤
        (1600 : ENNReal) * rootENN := by
    calc
      ENNReal.ofReal
            (16 * (4 * root + 48 * delta + rho)) ≤
          ENNReal.ofReal (1600 * root) :=
        ENNReal.ofReal_mono hwidth
      _ = (1600 : ENNReal) * rootENN := by
        dsimp only [rootENN]
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have hfraction :
      (2 * rho + 2 * (24 * delta)) / root +
          2 * (24 * delta) ≤
        100 * root := by
    have hnumerator :
        2 * rho + 2 * (24 * delta) ≤ 50 * rho := by
      nlinarith
    have hdiv :
        (2 * rho + 2 * (24 * delta)) / root ≤
          50 * root := by
      rw [div_le_iff₀ hrootPos]
      nlinarith
    nlinarith
  have hFastReal :
      4 *
          (Real.pi * (24 * delta) ^ 2 *
            (((2 * rho + 2 * (24 * delta)) / root) +
              2 * (24 * delta))) ≤
        1000000 * delta ^ 2 * root := by
    have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
    have hnonneg :
        0 ≤
          ((2 * rho + 2 * (24 * delta)) / root) +
            2 * (24 * delta) := by
      positivity
    calc
      4 *
          (Real.pi * (24 * delta) ^ 2 *
            (((2 * rho + 2 * (24 * delta)) / root) +
              2 * (24 * delta)))
          ≤
        4 *
          (4 * (24 * delta) ^ 2 *
            (((2 * rho + 2 * (24 * delta)) / root) +
              2 * (24 * delta))) := by
        gcongr
      _ ≤
        4 * (4 * (24 * delta) ^ 2 * (100 * root)) := by
        gcongr
      _ ≤ 1000000 * delta ^ 2 * root := by
        ring_nf
        nlinarith [sq_nonneg delta, hrootPos.le]
  have hFastENN :
      (4 : ENNReal) *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              (((2 * rho + 2 * (24 * delta)) / root) +
                2 * (24 * delta))) ≤
        (1000000 : ENNReal) *
          Kakeya.realRpowENN delta 2 * rootENN := by
    have h := ENNReal.ofReal_mono hFastReal
    have hleft :
        ENNReal.ofReal
            (4 *
              (Real.pi * (24 * delta) ^ 2 *
                (((2 * rho + 2 * (24 * delta)) / root) +
                  2 * (24 * delta)))) =
          (4 : ENNReal) *
            ENNReal.ofReal
              (Real.pi * (24 * delta) ^ 2 *
                (((2 * rho + 2 * (24 * delta)) / root) +
                  2 * (24 * delta))) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    have hright :
        ENNReal.ofReal
            (1000000 * delta ^ 2 * root) =
          (1000000 : ENNReal) *
            Kakeya.realRpowENN delta 2 * rootENN := by
      calc
        ENNReal.ofReal
              (1000000 * delta ^ 2 * root) =
            ENNReal.ofReal (1000000 * delta ^ 2) *
              ENNReal.ofReal root := by
          rw [ENNReal.ofReal_mul
            (mul_nonneg (by norm_num) (sq_nonneg delta))]
        _ =
            (ENNReal.ofReal 1000000 *
                ENNReal.ofReal (delta ^ 2)) *
              rootENN := by
          rw [ENNReal.ofReal_mul (by norm_num)]
        _ =
            (1000000 : ENNReal) *
              Kakeya.realRpowENN delta 2 * rootENN := by
          simp [Kakeya.realRpowENN, rootENN, Real.rpow_two]
    rw [hleft, hright] at h
    exact h
  have hRaw :=
    wz2_paper_subfamily_crop_boundary_mass
      hdelta hdeltaSmall hrho hrootPos hline selected shading hcwa
  have hSlow :
      (C *
            ENNReal.ofReal
              (16 * (4 * root + 48 * delta + rho)) *
            family.enncard) *
          (geometry * Kakeya.realRpowENN delta 2) ≤
        ((1600 : ENNReal) * geometry) *
          (C + 1) *
          Kakeya.realRpowENN delta 2 *
          rootENN *
          family.enncard := by
    calc
      (C *
            ENNReal.ofReal
              (16 * (4 * root + 48 * delta + rho)) *
            family.enncard) *
          (geometry * Kakeya.realRpowENN delta 2) ≤
        (C * ((1600 : ENNReal) * rootENN) *
            family.enncard) *
          (geometry * Kakeya.realRpowENN delta 2) := by
        gcongr
      _ =
        ((1600 : ENNReal) * geometry) *
          C * Kakeya.realRpowENN delta 2 *
          rootENN * family.enncard := by ring
      _ ≤
        ((1600 : ENNReal) * geometry) *
          (C + 1) * Kakeya.realRpowENN delta 2 *
          rootENN * family.enncard := by
        gcongr
        exact le_add_right le_rfl
  have hFast :
      family.enncard *
          ((4 : ENNReal) *
            ENNReal.ofReal
              (Real.pi * (24 * delta) ^ 2 *
                (((2 * rho + 2 * (24 * delta)) / root) +
                  2 * (24 * delta)))) ≤
        (1000000 : ENNReal) *
          (C + 1) *
          Kakeya.realRpowENN delta 2 *
          rootENN * family.enncard := by
    calc
      family.enncard *
          ((4 : ENNReal) *
            ENNReal.ofReal
              (Real.pi * (24 * delta) ^ 2 *
                (((2 * rho + 2 * (24 * delta)) / root) +
                  2 * (24 * delta)))) ≤
        family.enncard *
          ((1000000 : ENNReal) *
            Kakeya.realRpowENN delta 2 * rootENN) := by
        gcongr
      _ =
        (1000000 : ENNReal) *
          Kakeya.realRpowENN delta 2 *
          rootENN * family.enncard := by ring
      _ ≤
        (1000000 : ENNReal) *
          (C + 1) *
          Kakeya.realRpowENN delta 2 *
          rootENN * family.enncard := by
        have hOne : (1 : ENNReal) ≤ C + 1 := by
          simpa [add_comm] using
            (le_add_right (1 : ENNReal) C)
        calc
          (1000000 : ENNReal) *
                Kakeya.realRpowENN delta 2 *
                rootENN * family.enncard =
              1000000 * 1 *
                Kakeya.realRpowENN delta 2 *
                rootENN * family.enncard := by simp
          _ ≤
              1000000 * (C + 1) *
                Kakeya.realRpowENN delta 2 *
                rootENN * family.enncard := by
            gcongr
  have hCoefficient :
      (6 : ENNReal) *
          (((1600 : ENNReal) * geometry) + 1000000) ≤
        wz2PaperCropBoundaryMassConstant := by
    dsimp only [wz2PaperCropBoundaryMassConstant]
    calc
      (6 : ENNReal) *
          (((1600 : ENNReal) * geometry) + 1000000) =
        9600 * geometry + 6000000 := by ring
      _ ≤
        20000000 * geometry + 20000000 := by
        exact add_le_add
          (mul_le_mul_right' (by norm_num) geometry)
          (by norm_num)
      _ = 20000000 * (geometry + 1) := by ring
  calc
    (∑ index : Fin selected.family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      6 *
        ((C *
            ENNReal.ofReal
              (16 * (4 * root + 48 * delta + rho)) *
            family.enncard) *
          (geometry * Kakeya.realRpowENN delta 2) +
          family.enncard *
            (4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  (((2 * rho + 2 * (24 * delta)) / root) +
                    2 * (24 * delta))))) := by
      simpa [root] using hRaw
    _ ≤
      6 *
        ((((1600 : ENNReal) * geometry) *
            (C + 1) *
            Kakeya.realRpowENN delta 2 *
            rootENN * family.enncard) +
          ((1000000 : ENNReal) *
            (C + 1) *
            Kakeya.realRpowENN delta 2 *
            rootENN * family.enncard)) := by
      gcongr
    _ =
      (6 * (((1600 : ENNReal) * geometry) + 1000000)) *
        (C + 1) *
        Kakeya.realRpowENN delta 2 *
        rootENN * family.enncard := by ring
    _ ≤
      wz2PaperCropBoundaryMassConstant *
        (C + 1) *
        Kakeya.realRpowENN delta 2 *
        rootENN * family.enncard := by
      gcongr

end Kakeya.Assouad

end
