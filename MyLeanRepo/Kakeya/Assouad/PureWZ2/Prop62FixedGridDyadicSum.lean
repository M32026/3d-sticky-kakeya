import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedGridDirectionBand
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
# Proposition 6.2 fixed-grid boundary: dyadic direction sum

This is the finite dyadic direction decomposition in the proof of
`WZ2_prop62.tex`, Lemma `prop62-fixed-grid`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62DirectionLevelCount (delta : ℝ) : ℕ :=
  Nat.floor (Real.log (1 / delta) / Real.log 2) + 1

def pureWZ2Prop62DirectionScale (delta : ℝ) (level : ℕ) : ℝ :=
  max (delta / 2) ((1 / 2 : ℝ) ^ (level + 1))

def pureWZ2Prop62FixedGridBandConstant : ENNReal :=
  2000000000

def pureWZ2Prop62FixedGridSlowConstant : ENNReal :=
  46891008 * Kakeya.deltaTubeVolume 1

def pureWZ2Prop62FixedGridPlaneConstant : ENNReal :=
  pureWZ2Prop62FixedGridSlowConstant +
    pureWZ2Prop62FixedGridBandConstant

lemma pureWZ2_prop62_direction_scale_pos
    {delta : ℝ} (level : ℕ) :
    0 < pureWZ2Prop62DirectionScale delta level := by
  exact lt_of_lt_of_le (pow_pos (by norm_num) _)
    (le_max_right _ _)

lemma pureWZ2_prop62_delta_le_two_direction_scale
    {delta : ℝ} (hdelta : 0 < delta) (level : ℕ) :
    delta ≤ 2 * pureWZ2Prop62DirectionScale delta level := by
  calc
    delta = 2 * (delta / 2) := by ring
    _ ≤ 2 * pureWZ2Prop62DirectionScale delta level := by
      gcongr
      exact le_max_left _ _

lemma pureWZ2_prop62_direction_scale_le_one
    {delta : ℝ} (hdeltaOne : delta ≤ 1) (level : ℕ) :
    pureWZ2Prop62DirectionScale delta level ≤ 1 := by
  apply max_le
  · linarith
  · exact pow_le_one₀ (by norm_num) (by norm_num)

private lemma pureWZ2_prop62_direction_band_real_coefficient
    {delta scale : ℝ}
    (hdelta : 0 < delta)
    (hscale : 0 < scale)
    (hdeltaScale : delta ≤ 2 * scale)
    (hscaleOne : scale ≤ 1) :
    (16 * (8 * scale + 49 * delta)) *
        (4 * (Real.pi * (24 * delta) ^ 2 *
          ((50 * delta) / scale + 48 * delta))) ≤
      2000000000 * delta ^ 3 := by
  have hwidth : 8 * scale + 49 * delta ≤ 106 * scale := by
    linarith
  have hbracketNonneg :
      0 ≤ (50 * delta) / scale + 48 * delta := by
    positivity
  have hscaledBracket :
      scale * ((50 * delta) / scale + 48 * delta) ≤
        98 * delta := by
    have heq :
        scale * ((50 * delta) / scale + 48 * delta) =
          50 * delta + 48 * scale * delta := by
      field_simp [hscale.ne']
    rw [heq]
    nlinarith
  have hproduct :
      (8 * scale + 49 * delta) *
          ((50 * delta) / scale + 48 * delta) ≤
        10388 * delta := by
    calc
      (8 * scale + 49 * delta) *
            ((50 * delta) / scale + 48 * delta) ≤
          (106 * scale) *
            ((50 * delta) / scale + 48 * delta) := by
              gcongr
      _ =
          106 *
            (scale * ((50 * delta) / scale + 48 * delta)) := by
        ring
      _ ≤ 106 * (98 * delta) := by
        gcongr
      _ = 10388 * delta := by ring
  calc
    (16 * (8 * scale + 49 * delta)) *
        (4 * (Real.pi * (24 * delta) ^ 2 *
          ((50 * delta) / scale + 48 * delta))) =
      64 * Real.pi * (24 * delta) ^ 2 *
        ((8 * scale + 49 * delta) *
          ((50 * delta) / scale + 48 * delta)) := by
            ring
    _ ≤ 64 * 4 * (24 * delta) ^ 2 * (10388 * delta) := by
      gcongr
      exact Real.pi_le_four
    _ = 1531772928 * delta ^ 3 := by ring
    _ ≤ 2000000000 * delta ^ 3 := by
      have hcube : 0 ≤ delta ^ 3 := by positivity
      nlinarith

lemma pureWZ2_prop62_direction_band_coefficient
    {delta scale : ℝ}
    (hdelta : 0 < delta)
    (hscale : 0 < scale)
    (hdeltaScale : delta ≤ 2 * scale)
    (hscaleOne : scale ≤ 1) :
    ENNReal.ofReal (16 * (8 * scale + 49 * delta)) *
        (4 * ENNReal.ofReal
          (Real.pi * (24 * delta) ^ 2 *
            ((50 * delta) / scale + 48 * delta))) ≤
      pureWZ2Prop62FixedGridBandConstant *
        Kakeya.realRpowENN delta 3 := by
  have hfirst : 0 ≤ 16 * (8 * scale + 49 * delta) := by
    positivity
  have hreal :=
    pureWZ2_prop62_direction_band_real_coefficient
      hdelta hscale hdeltaScale hscaleOne
  have hleft :
      ENNReal.ofReal (16 * (8 * scale + 49 * delta)) *
          (4 * ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((50 * delta) / scale + 48 * delta))) =
        ENNReal.ofReal
          ((16 * (8 * scale + 49 * delta)) *
            (4 * (Real.pi * (24 * delta) ^ 2 *
              ((50 * delta) / scale + 48 * delta)))) := by
    rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [← ENNReal.ofReal_mul hfirst]
  rw [hleft]
  calc
    ENNReal.ofReal
          ((16 * (8 * scale + 49 * delta)) *
            (4 * (Real.pi * (24 * delta) ^ 2 *
              ((50 * delta) / scale + 48 * delta)))) ≤
        ENNReal.ofReal (2000000000 * delta ^ 3) :=
      ENNReal.ofReal_mono hreal
    _ =
        pureWZ2Prop62FixedGridBandConstant *
          Kakeya.realRpowENN delta 3 := by
      calc
        ENNReal.ofReal (2000000000 * delta ^ 3) =
            ENNReal.ofReal (2000000000 : ℝ) *
              ENNReal.ofReal (delta ^ 3) := by
                exact ENNReal.ofReal_mul (by norm_num)
        _ =
            pureWZ2Prop62FixedGridBandConstant *
              Kakeya.realRpowENN delta 3 := by
          norm_num [pureWZ2Prop62FixedGridBandConstant,
            Kakeya.realRpowENN, Real.rpow_natCast]

lemma pureWZ2_prop62_slow_coefficient
    {delta : ℝ} (hdelta : 0 < delta) :
    ENNReal.ofReal (16 * (4 * delta + 49 * delta)) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) =
      pureWZ2Prop62FixedGridSlowConstant *
        Kakeya.realRpowENN delta 3 := by
  rw [show
    16 * (4 * delta + 49 * delta) = 848 * delta by ring]
  rw [show
    ENNReal.ofReal (848 * delta) =
        (848 : ENNReal) * ENNReal.ofReal delta by
      rw [← ENNReal.ofReal_ofNat (n := 848)]
      exact ENNReal.ofReal_mul (by norm_num)]
  simp [pureWZ2Prop62FixedGridSlowConstant,
    Kakeya.realRpowENN, ENNReal.ofReal_pow hdelta.le]
  ring

theorem pureWZ2_prop62_one_plane_dyadic_sum
    {delta boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    let levels :=
      Finset.range (pureWZ2Prop62DirectionLevelCount delta)
    let slow :=
      wz2PaperSlowBoundaryTubeIndices
        family coordinate boundary delta
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - delta) (boundary + delta))) ≤
      (C *
          ENNReal.ofReal (16 * (4 * delta + 49 * delta)) *
          family.enncard) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) +
      ∑ level ∈ levels,
        (C *
            ENNReal.ofReal
              (16 *
                (8 * pureWZ2Prop62DirectionScale delta level +
                  49 * delta)) *
            family.enncard) *
          (4 *
            ENNReal.ofReal
              (Real.pi * (24 * delta) ^ 2 *
                ((50 * delta) /
                    pureWZ2Prop62DirectionScale delta level +
                  48 * delta))) := by
  dsimp only
  let levels :=
    Finset.range (pureWZ2Prop62DirectionLevelCount delta)
  let slow :=
    wz2PaperSlowBoundaryTubeIndices
      family coordinate boundary delta
  let band : ℕ → Finset (Fin family.card) := fun level =>
    pureWZ2Prop62DirectionBandIndices family coordinate boundary
      (pureWZ2Prop62DirectionScale delta level)
  let weight : Fin family.card → ENNReal := fun index =>
    volume
      (shading.carrier index ∩
        coordinateSlab coordinate
          (boundary - delta) (boundary + delta))
  have hdeltaOne : delta ≤ 1 := by linarith
  have hpointwise :
      ∀ index : Fin family.card,
        weight index ≤
          (if index ∈ slow then weight index else 0) +
            ∑ level ∈ levels,
              if index ∈ band level then weight index else 0 := by
    intro index
    let tubeSection :=
      shading.carrier index ∩
        coordinateSlab coordinate
          (boundary - delta) (boundary + delta)
    by_cases hsection : tubeSection.Nonempty
    · let speed :=
        |wz1PaperDirection (family.tube index) coordinate|
      have hspeedOne : speed ≤ 1 := by
        calc
          speed ≤ ‖wz1PaperDirection (family.tube index)‖ :=
            coord_abs_le_norm _ coordinate
          _ = 1 := wz1PaperDirection_norm _
      by_cases hslow : speed ≤ delta
      · have hslowMem : index ∈ slow := by
          have hsection' :
              (wz1PaperTubeCarrier (family.tube index) ∩
                coordinateSlab coordinate
                  (boundary - delta) (boundary + delta)).Nonempty := by
            rcases hsection with ⟨point, hpointShading, hpointSlab⟩
            exact
              ⟨point, shading.subset_body index hpointShading,
                hpointSlab⟩
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hslow, hsection'⟩
        simp only [if_pos hslowMem]
        exact le_add_right le_rfl
      · have hdeltaSpeed : delta ≤ speed :=
          (lt_of_not_ge hslow).le
        rcases
            dyadic_coverage hdelta hdeltaOne hdeltaSpeed hspeedOne
          with ⟨level, hlevel, hlower, hupper⟩
        have hlevelMem : level ∈ levels := by
          simp only [levels, pureWZ2Prop62DirectionLevelCount,
            Finset.mem_range]
          omega
        have hscalePos :
            0 < pureWZ2Prop62DirectionScale delta level := by
          exact lt_of_lt_of_le (pow_pos (by norm_num) _)
            (le_max_right _ _)
        have hscaleLower :
            pureWZ2Prop62DirectionScale delta level ≤ speed := by
          apply max_le
          · linarith
          · exact hlower
        have hscaleUpper :
            speed ≤
              2 * pureWZ2Prop62DirectionScale delta level := by
          calc
            speed ≤ (1 / 2 : ℝ) ^ level := hupper
            _ =
                2 * (1 / 2 : ℝ) ^ (level + 1) := by
              rw [pow_succ]
              ring
            _ ≤
                2 * pureWZ2Prop62DirectionScale delta level := by
              gcongr
              exact le_max_right _ _
        have hbandMem : index ∈ band level := by
          have hsection' :
              (wz1PaperTubeCarrier (family.tube index) ∩
                coordinateSlab coordinate
                  (boundary - delta) (boundary + delta)).Nonempty := by
            rcases hsection with ⟨point, hpointShading, hpointSlab⟩
            exact
              ⟨point, shading.subset_body index hpointShading,
                hpointSlab⟩
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hscaleLower, hscaleUpper, hsection'⟩
        have hsingle :
            (if index ∈ band level then weight index else 0) ≤
              ∑ current ∈ levels,
                if index ∈ band current then weight index else 0 :=
          Finset.single_le_sum
            (f := fun current =>
              if index ∈ band current then weight index else 0)
            (fun _ _ => bot_le) hlevelMem
        rw [if_pos hbandMem] at hsingle
        exact hsingle.trans (le_add_left le_rfl)
    · have hempty : tubeSection = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hsection
      have hweight : weight index = 0 := by
        simp only [weight, tubeSection] at hempty ⊢
        rw [hempty]
        simp
      rw [hweight]
      exact bot_le
  have hdecomposition :
      (∑ index : Fin family.card, weight index) ≤
        (∑ index ∈ slow, weight index) +
          ∑ level ∈ levels, ∑ index ∈ band level, weight index := by
    calc
      (∑ index : Fin family.card, weight index) ≤
          ∑ index : Fin family.card,
            ((if index ∈ slow then weight index else 0) +
              ∑ level ∈ levels,
                if index ∈ band level then weight index else 0) := by
            exact Finset.sum_le_sum fun index _ => hpointwise index
      _ =
          (∑ index ∈ slow, weight index) +
            ∑ level ∈ levels,
              ∑ index ∈ band level, weight index := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro level hlevel
          simp
  have hslowBound :=
    wz2_paper_slow_boundary_shading_mass
      hdelta hdeltaSmall hdelta hline shading coordinate hcwa
      (boundary := boundary)
  have hslowSectionBound :
      (∑ index ∈ slow, weight index) ≤
        (C *
            ENNReal.ofReal (16 * (4 * delta + 49 * delta)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) := by
    calc
      (∑ index ∈ slow, weight index) ≤
          ∑ index ∈ slow, volume (shading.carrier index) := by
        exact Finset.sum_le_sum fun index hindex =>
          measure_mono Set.inter_subset_left
      _ ≤
          (C *
              ENNReal.ofReal (16 * (4 * delta + 49 * delta)) *
              family.enncard) *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2) := by
        simpa only [slow] using hslowBound
  have hbandBound :
      ∀ level ∈ levels,
        (∑ index ∈ band level, weight index) ≤
          (C *
              ENNReal.ofReal
                (16 *
                  (8 * pureWZ2Prop62DirectionScale delta level +
                    49 * delta)) *
              family.enncard) *
            (4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  ((50 * delta) /
                      pureWZ2Prop62DirectionScale delta level +
                    48 * delta))) := by
    intro level hlevel
    have hscalePos :
        0 < pureWZ2Prop62DirectionScale delta level := by
      exact lt_of_lt_of_le (pow_pos (by norm_num) _)
        (le_max_right _ _)
    simpa only [band, weight] using
      pureWZ2_prop62_direction_band_boundary_mass
        hdelta hdeltaSmall hscalePos hline shading coordinate hcwa
        (boundary := boundary)
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - delta) (boundary + delta))) =
        ∑ index : Fin family.card, weight index := rfl
    _ ≤
        (∑ index ∈ slow, weight index) +
          ∑ level ∈ levels, ∑ index ∈ band level, weight index :=
      hdecomposition
    _ ≤
        (C *
            ENNReal.ofReal (16 * (4 * delta + 49 * delta)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) +
        ∑ level ∈ levels,
          (C *
              ENNReal.ofReal
                (16 *
                  (8 * pureWZ2Prop62DirectionScale delta level +
                    49 * delta)) *
              family.enncard) *
            (4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  ((50 * delta) /
                      pureWZ2Prop62DirectionScale delta level +
                    48 * delta))) := by
      exact add_le_add hslowSectionBound <|
        Finset.sum_le_sum fun level hlevel =>
          hbandBound level hlevel

theorem pureWZ2_prop62_one_plane_boundary_mass
    {delta boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - delta) (boundary + delta))) ≤
      C *
        ((pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
          pureWZ2Prop62FixedGridPlaneConstant) *
        Kakeya.realRpowENN delta 3 *
        family.enncard := by
  let levels :=
    Finset.range (pureWZ2Prop62DirectionLevelCount delta)
  have hraw :=
    pureWZ2_prop62_one_plane_dyadic_sum
      hdelta hdeltaSmall hline shading coordinate hcwa
      (boundary := boundary)
  have hdeltaOne : delta ≤ 1 := by linarith
  let common : ENNReal :=
    C * pureWZ2Prop62FixedGridBandConstant *
      Kakeya.realRpowENN delta 3 * family.enncard
  have hband :
      ∀ level ∈ levels,
        (C *
            ENNReal.ofReal
              (16 *
                (8 * pureWZ2Prop62DirectionScale delta level +
                  49 * delta)) *
            family.enncard) *
          (4 *
            ENNReal.ofReal
              (Real.pi * (24 * delta) ^ 2 *
                ((50 * delta) /
                    pureWZ2Prop62DirectionScale delta level +
                  48 * delta))) ≤
          common := by
    intro level hlevel
    have hcoefficient :=
      pureWZ2_prop62_direction_band_coefficient
        hdelta
        (pureWZ2_prop62_direction_scale_pos (delta := delta) level)
        (pureWZ2_prop62_delta_le_two_direction_scale hdelta level)
        (pureWZ2_prop62_direction_scale_le_one hdeltaOne level)
    dsimp only [common]
    calc
      (C *
          ENNReal.ofReal
            (16 *
              (8 * pureWZ2Prop62DirectionScale delta level +
                49 * delta)) *
          family.enncard) *
        (4 *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((50 * delta) /
                  pureWZ2Prop62DirectionScale delta level +
                48 * delta))) =
        C *
          (ENNReal.ofReal
              (16 *
                (8 * pureWZ2Prop62DirectionScale delta level +
                  49 * delta)) *
            (4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  ((50 * delta) /
                      pureWZ2Prop62DirectionScale delta level +
                    48 * delta)))) *
          family.enncard := by ring
      _ ≤
        C *
          (pureWZ2Prop62FixedGridBandConstant *
            Kakeya.realRpowENN delta 3) *
          family.enncard := by
        gcongr
      _ =
        C * pureWZ2Prop62FixedGridBandConstant *
          Kakeya.realRpowENN delta 3 * family.enncard := by ring
  have hslow :
      (C *
          ENNReal.ofReal (16 * (4 * delta + 49 * delta)) *
          family.enncard) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) =
      C * pureWZ2Prop62FixedGridSlowConstant *
        Kakeya.realRpowENN delta 3 * family.enncard := by
    rw [show
      (C *
          ENNReal.ofReal (16 * (4 * delta + 49 * delta)) *
          family.enncard) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) =
        C *
          (ENNReal.ofReal (16 * (4 * delta + 49 * delta)) *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2)) *
          family.enncard by ring]
    rw [pureWZ2_prop62_slow_coefficient hdelta]
    ring
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - delta) (boundary + delta))) ≤
      (C *
          ENNReal.ofReal (16 * (4 * delta + 49 * delta)) *
          family.enncard) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) +
      ∑ level ∈ levels,
        (C *
            ENNReal.ofReal
              (16 *
                (8 * pureWZ2Prop62DirectionScale delta level +
                  49 * delta)) *
            family.enncard) *
          (4 *
            ENNReal.ofReal
              (Real.pi * (24 * delta) ^ 2 *
                ((50 * delta) /
                    pureWZ2Prop62DirectionScale delta level +
                  48 * delta))) := by
        simpa only [levels] using hraw
    _ ≤
      C * pureWZ2Prop62FixedGridSlowConstant *
          Kakeya.realRpowENN delta 3 * family.enncard +
        ∑ _level ∈ levels, common := by
      exact add_le_add hslow.le <|
        Finset.sum_le_sum fun level hlevel =>
          hband level hlevel
    _ =
      C * pureWZ2Prop62FixedGridSlowConstant *
          Kakeya.realRpowENN delta 3 * family.enncard +
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
          common := by
      simp [levels, Finset.sum_const, common]
    _ ≤
      C *
        ((pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
          pureWZ2Prop62FixedGridPlaneConstant) *
        Kakeya.realRpowENN delta 3 *
        family.enncard := by
      dsimp only [common, pureWZ2Prop62FixedGridPlaneConstant]
      have hlevels :
          (1 : ENNReal) ≤
            (pureWZ2Prop62DirectionLevelCount delta : ENNReal) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
      calc
        C * pureWZ2Prop62FixedGridSlowConstant *
              Kakeya.realRpowENN delta 3 * family.enncard +
            (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              (C * pureWZ2Prop62FixedGridBandConstant *
                Kakeya.realRpowENN delta 3 * family.enncard) ≤
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              (C * pureWZ2Prop62FixedGridSlowConstant *
                Kakeya.realRpowENN delta 3 * family.enncard) +
            (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              (C * pureWZ2Prop62FixedGridBandConstant *
                Kakeya.realRpowENN delta 3 * family.enncard) := by
          have hslowScaled :
              C * pureWZ2Prop62FixedGridSlowConstant *
                    Kakeya.realRpowENN delta 3 * family.enncard ≤
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
                  (C * pureWZ2Prop62FixedGridSlowConstant *
                    Kakeya.realRpowENN delta 3 * family.enncard) := by
            simpa only [one_mul] using
              (mul_le_mul_right'
                hlevels
                (C * pureWZ2Prop62FixedGridSlowConstant *
                  Kakeya.realRpowENN delta 3 * family.enncard))
          exact add_le_add hslowScaled le_rfl
        _ =
          C *
            ((pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              (pureWZ2Prop62FixedGridSlowConstant +
                pureWZ2Prop62FixedGridBandConstant)) *
            Kakeya.realRpowENN delta 3 *
            family.enncard := by ring

end Kakeya.Assouad

end
