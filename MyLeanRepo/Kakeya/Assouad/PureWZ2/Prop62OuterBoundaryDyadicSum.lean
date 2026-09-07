import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62OuterBoundaryDirectionBand

/-!
# Proposition 6.2 outer boundary: dyadic direction sum

This proves the one-face estimate in `WZ2_prop62.tex`,
Lemma `prop62-fixed-grid`, before summing over the six faces.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62OuterDirectionLevelCount (rho : ℝ) : ℕ :=
  Nat.floor (Real.log (1 / rho) / Real.log 2) + 1

def pureWZ2Prop62OuterDirectionScale (rho : ℝ) (level : ℕ) : ℝ :=
  max (rho / 2) ((1 / 2 : ℝ) ^ (level + 1))

def pureWZ2Prop62OuterSlowIndices
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (coordinate : Fin 3)
    (boundary rho : ℝ) : Finset (Fin family.card) :=
  Finset.univ.filter fun index =>
    |wz1PaperDirection (family.tube index) coordinate| ≤ rho ∧
      (wz1PaperTubeCarrier (family.tube index) ∩
        coordinateSlab coordinate
          (boundary - rho) (boundary + rho)).Nonempty

def pureWZ2Prop62OuterBandConstant : ENNReal :=
  4000000000

def pureWZ2Prop62OuterSlowConstant : ENNReal :=
  46891008 * Kakeya.deltaTubeVolume 1

def pureWZ2Prop62OuterFaceConstant : ENNReal :=
  pureWZ2Prop62OuterSlowConstant +
    pureWZ2Prop62OuterBandConstant

lemma pureWZ2_prop62_outer_direction_scale_pos
    {rho : ℝ} (level : ℕ) :
    0 < pureWZ2Prop62OuterDirectionScale rho level := by
  exact lt_of_lt_of_le (pow_pos (by norm_num) _)
    (le_max_right _ _)

lemma pureWZ2_prop62_rho_le_two_outer_direction_scale
    {rho : ℝ} (hrho : 0 < rho) (level : ℕ) :
    rho ≤ 2 * pureWZ2Prop62OuterDirectionScale rho level := by
  calc
    rho = 2 * (rho / 2) := by ring
    _ ≤ 2 * pureWZ2Prop62OuterDirectionScale rho level := by
      gcongr
      exact le_max_left _ _

lemma pureWZ2_prop62_outer_direction_scale_le_one
    {rho : ℝ} (hrhoOne : rho ≤ 1) (level : ℕ) :
    pureWZ2Prop62OuterDirectionScale rho level ≤ 1 := by
  apply max_le
  · linarith
  · exact pow_le_one₀ (by norm_num) (by norm_num)

private lemma pureWZ2_prop62_outer_band_real_coefficient
    {delta rho scale : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdeltaRho : delta ≤ rho)
    (hscale : 0 < scale)
    (hrhoScale : rho ≤ 2 * scale)
    (hscaleOne : scale ≤ 1) :
    (16 * (8 * scale + 48 * delta + rho)) *
        (4 * (Real.pi * (24 * delta) ^ 2 *
          ((2 * rho + 48 * delta) / scale +
            48 * delta))) ≤
      4000000000 * rho * delta ^ 2 := by
  have hwidth :
      8 * scale + 48 * delta + rho ≤ 106 * scale := by
    linarith
  have hbracketNonneg :
      0 ≤ (2 * rho + 48 * delta) / scale + 48 * delta := by
    positivity
  have hscaledBracket :
      scale *
          ((2 * rho + 48 * delta) / scale + 48 * delta) ≤
        98 * rho := by
    have heq :
        scale *
            ((2 * rho + 48 * delta) / scale + 48 * delta) =
          2 * rho + 48 * delta + 48 * scale * delta := by
      field_simp [hscale.ne']
    rw [heq]
    nlinarith
  have hproduct :
      (8 * scale + 48 * delta + rho) *
          ((2 * rho + 48 * delta) / scale + 48 * delta) ≤
        10388 * rho := by
    calc
      (8 * scale + 48 * delta + rho) *
            ((2 * rho + 48 * delta) / scale + 48 * delta) ≤
          (106 * scale) *
            ((2 * rho + 48 * delta) / scale + 48 * delta) := by
              gcongr
      _ =
          106 *
            (scale *
              ((2 * rho + 48 * delta) / scale + 48 * delta)) := by
        ring
      _ ≤ 106 * (98 * rho) := by
        gcongr
      _ = 10388 * rho := by ring
  calc
    (16 * (8 * scale + 48 * delta + rho)) *
        (4 * (Real.pi * (24 * delta) ^ 2 *
          ((2 * rho + 48 * delta) / scale +
            48 * delta))) =
      64 * Real.pi * (24 * delta) ^ 2 *
        ((8 * scale + 48 * delta + rho) *
          ((2 * rho + 48 * delta) / scale +
            48 * delta)) := by
      ring
    _ ≤ 64 * 4 * (24 * delta) ^ 2 * (10388 * rho) := by
      gcongr
      exact Real.pi_le_four
    _ = 1531772928 * rho * delta ^ 2 := by ring
    _ ≤ 4000000000 * rho * delta ^ 2 := by
      have hnonnegative : 0 ≤ rho * delta ^ 2 := by positivity
      nlinarith

lemma pureWZ2_prop62_outer_band_coefficient
    {delta rho scale : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdeltaRho : delta ≤ rho)
    (hscale : 0 < scale)
    (hrhoScale : rho ≤ 2 * scale)
    (hscaleOne : scale ≤ 1) :
    ENNReal.ofReal
          (16 * (8 * scale + 48 * delta + rho)) *
        (4 * ENNReal.ofReal
          (Real.pi * (24 * delta) ^ 2 *
            ((2 * rho + 48 * delta) / scale +
              48 * delta))) ≤
      pureWZ2Prop62OuterBandConstant *
        ENNReal.ofReal rho *
        Kakeya.realRpowENN delta 2 := by
  have hfirst :
      0 ≤ 16 * (8 * scale + 48 * delta + rho) := by
    positivity
  have hreal :=
    pureWZ2_prop62_outer_band_real_coefficient
      hdelta hrho hdeltaRho hscale hrhoScale hscaleOne
  have hleft :
      ENNReal.ofReal
            (16 * (8 * scale + 48 * delta + rho)) *
          (4 * ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((2 * rho + 48 * delta) / scale +
                48 * delta))) =
        ENNReal.ofReal
          ((16 * (8 * scale + 48 * delta + rho)) *
            (4 * (Real.pi * (24 * delta) ^ 2 *
              ((2 * rho + 48 * delta) / scale +
                48 * delta)))) := by
    rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [← ENNReal.ofReal_mul hfirst]
  rw [hleft]
  calc
    ENNReal.ofReal
          ((16 * (8 * scale + 48 * delta + rho)) *
            (4 * (Real.pi * (24 * delta) ^ 2 *
              ((2 * rho + 48 * delta) / scale +
                48 * delta)))) ≤
        ENNReal.ofReal (4000000000 * rho * delta ^ 2) :=
      ENNReal.ofReal_mono hreal
    _ =
        pureWZ2Prop62OuterBandConstant *
          ENNReal.ofReal rho *
          Kakeya.realRpowENN delta 2 := by
      calc
        ENNReal.ofReal (4000000000 * rho * delta ^ 2) =
            ENNReal.ofReal (4000000000 * rho) *
              ENNReal.ofReal (delta ^ 2) := by
          exact ENNReal.ofReal_mul (mul_nonneg (by norm_num) hrho.le)
        _ =
            ENNReal.ofReal (4000000000 : ℝ) *
              ENNReal.ofReal rho *
              ENNReal.ofReal (delta ^ 2) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4000000000)]
        _ =
            pureWZ2Prop62OuterBandConstant *
              ENNReal.ofReal rho *
              Kakeya.realRpowENN delta 2 := by
          norm_num [pureWZ2Prop62OuterBandConstant,
            Kakeya.realRpowENN, Real.rpow_two]

theorem pureWZ2_prop62_outer_slow_boundary_mass
    {delta rho boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hdeltaRho : delta ≤ rho)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    let slow :=
      pureWZ2Prop62OuterSlowIndices
        family coordinate boundary rho
    (∑ index ∈ slow,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho))) ≤
      C * pureWZ2Prop62OuterSlowConstant *
        ENNReal.ofReal rho *
        Kakeya.realRpowENN delta 2 *
        family.enncard := by
  dsimp only
  let slow :=
    pureWZ2Prop62OuterSlowIndices
      family coordinate boundary rho
  let container :=
    pureWZ2Prop62OuterBoundaryContainer
      delta rho boundary rho coordinate
  have hcontained :
      ∀ index ∈ slow,
        wz1PaperTubeCarrier (family.tube index) ⊆ container := by
    intro index hindex
    have hdata := (Finset.mem_filter.mp hindex).2
    exact
      pureWZ2_prop62_outer_slow_tube_contained
        hdelta hrho.le hrho.le
        (family.tube index) (hline index) coordinate
        hdata.1 hdata.2
  have hslowCard :
      (slow.card : ENNReal) ≤
        C * ENNReal.ofReal (16 * (5 * rho + 48 * delta)) *
          family.enncard := by
    have hcount :=
      hcwa container
        (convex_pureWZ2Prop62OuterBoundaryContainer
          delta rho boundary rho coordinate)
    have hsubset :
        slow ⊆
          (Finset.univ : Finset (Fin family.card)).filter fun index =>
            wz1PaperTubeCarrier (family.tube index) ⊆ container := by
      intro index hindex
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hcontained index hindex⟩
    have hcard :
        (slow.card : ENNReal) ≤
          (((Finset.univ : Finset (Fin family.card)).filter fun index =>
            wz1PaperTubeCarrier (family.tube index) ⊆ container).card :
              ENNReal) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hvolume :
        volume container ≤
          ENNReal.ofReal (16 * (5 * rho + 48 * delta)) := by
      simpa only [container, show
        4 * rho + 48 * delta + rho =
          5 * rho + 48 * delta by ring] using
        volume_pureWZ2Prop62OuterBoundaryContainer_le
          (delta := delta) (rho := rho) (boundary := boundary)
          (speed := rho) (by positivity) coordinate
    exact hcard.trans <| hcount.trans <| by
      gcongr
  have hterm :
      ∀ index ∈ slow,
        volume
            (shading.carrier index ∩
              coordinateSlab coordinate
                (boundary - rho) (boundary + rho)) ≤
          55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2 := by
    intro index hindex
    exact
      (measure_mono <| Set.inter_subset_left.trans <|
        shading.subset_body index).trans
        (wz2PaperTubeCarrier_convex_and_volume_quadratic
          wz2_paper_tube_carrier_geometry
          hdelta hdeltaSmall (family.tube index)
          (hline index)).2
  have hcoefficient :
      ENNReal.ofReal (16 * (5 * rho + 48 * delta)) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) ≤
        pureWZ2Prop62OuterSlowConstant *
          ENNReal.ofReal rho *
          Kakeya.realRpowENN delta 2 := by
    have hreal :
        16 * (5 * rho + 48 * delta) ≤ 848 * rho := by
      linarith
    have hwidth :
        ENNReal.ofReal (16 * (5 * rho + 48 * delta)) ≤
          (848 : ENNReal) * ENNReal.ofReal rho := by
      calc
        ENNReal.ofReal (16 * (5 * rho + 48 * delta)) ≤
            ENNReal.ofReal (848 * rho) :=
          ENNReal.ofReal_mono hreal
        _ = (848 : ENNReal) * ENNReal.ofReal rho := by
          rw [← ENNReal.ofReal_ofNat (n := 848)]
          exact ENNReal.ofReal_mul (by norm_num)
    dsimp only [pureWZ2Prop62OuterSlowConstant]
    calc
      ENNReal.ofReal (16 * (5 * rho + 48 * delta)) *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2) ≤
          ((848 : ENNReal) * ENNReal.ofReal rho) *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2) := by
        gcongr
      _ =
          46891008 * Kakeya.deltaTubeVolume 1 *
            ENNReal.ofReal rho *
            Kakeya.realRpowENN delta 2 := by ring
  calc
    (∑ index ∈ slow,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho))) ≤
      ∑ _index ∈ slow,
        55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2 := by
      exact Finset.sum_le_sum fun index hindex =>
        hterm index hindex
    _ =
      (slow.card : ENNReal) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) := by
      simp [Finset.sum_const]
    _ ≤
      (C * ENNReal.ofReal (16 * (5 * rho + 48 * delta)) *
        family.enncard) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) := by
      gcongr
    _ =
      C *
        (ENNReal.ofReal (16 * (5 * rho + 48 * delta)) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2)) *
        family.enncard := by ring
    _ ≤
      C * pureWZ2Prop62OuterSlowConstant *
        ENNReal.ofReal rho *
        Kakeya.realRpowENN delta 2 *
        family.enncard := by
      calc
        C *
              (ENNReal.ofReal (16 * (5 * rho + 48 * delta)) *
                (55296 * Kakeya.deltaTubeVolume 1 *
                  Kakeya.realRpowENN delta 2)) *
              family.enncard ≤
            C *
              (pureWZ2Prop62OuterSlowConstant *
                ENNReal.ofReal rho *
                Kakeya.realRpowENN delta 2) *
              family.enncard := by
          gcongr
        _ =
            C * pureWZ2Prop62OuterSlowConstant *
              ENNReal.ofReal rho *
              Kakeya.realRpowENN delta 2 *
              family.enncard := by ring

theorem pureWZ2_prop62_outer_face_boundary_mass
    {delta rho boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
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
              (boundary - rho) (boundary + rho))) ≤
      C *
        ((pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
          pureWZ2Prop62OuterFaceConstant) *
        ENNReal.ofReal rho *
        Kakeya.realRpowENN delta 2 *
        family.enncard := by
  let levels :=
    Finset.range (pureWZ2Prop62OuterDirectionLevelCount rho)
  let slow :=
    pureWZ2Prop62OuterSlowIndices
      family coordinate boundary rho
  let band : ℕ → Finset (Fin family.card) := fun level =>
    pureWZ2Prop62OuterDirectionBandIndices
      family coordinate boundary rho
        (pureWZ2Prop62OuterDirectionScale rho level)
  let weight : Fin family.card → ENNReal := fun index =>
    volume
      (shading.carrier index ∩
        coordinateSlab coordinate
          (boundary - rho) (boundary + rho))
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
          (boundary - rho) (boundary + rho)
    by_cases hsection : tubeSection.Nonempty
    · let speed :=
        |wz1PaperDirection (family.tube index) coordinate|
      have hspeedOne : speed ≤ 1 := by
        calc
          speed ≤ ‖wz1PaperDirection (family.tube index)‖ :=
            coord_abs_le_norm _ coordinate
          _ = 1 := wz1PaperDirection_norm _
      by_cases hslow : speed ≤ rho
      · have hsection' :
            (wz1PaperTubeCarrier (family.tube index) ∩
              coordinateSlab coordinate
                (boundary - rho) (boundary + rho)).Nonempty := by
          rcases hsection with ⟨point, hpointShading, hpointSlab⟩
          exact
            ⟨point, shading.subset_body index hpointShading,
              hpointSlab⟩
        have hslowMem : index ∈ slow :=
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hslow, hsection'⟩
        simp only [if_pos hslowMem]
        exact le_add_right le_rfl
      · have hrhoSpeed : rho ≤ speed :=
          (lt_of_not_ge hslow).le
        rcases
            dyadic_coverage hrho hrhoOne hrhoSpeed hspeedOne
          with ⟨level, hlevel, hlower, hupper⟩
        have hlevelMem : level ∈ levels := by
          simp only [levels, pureWZ2Prop62OuterDirectionLevelCount,
            Finset.mem_range]
          omega
        have hscaleLower :
            pureWZ2Prop62OuterDirectionScale rho level ≤ speed := by
          apply max_le
          · linarith
          · exact hlower
        have hscaleUpper :
            speed ≤
              2 * pureWZ2Prop62OuterDirectionScale rho level := by
          calc
            speed ≤ (1 / 2 : ℝ) ^ level := hupper
            _ = 2 * (1 / 2 : ℝ) ^ (level + 1) := by
              rw [pow_succ]
              ring
            _ ≤
                2 * pureWZ2Prop62OuterDirectionScale rho level := by
              gcongr
              exact le_max_right _ _
        have hsection' :
            (wz1PaperTubeCarrier (family.tube index) ∩
              coordinateSlab coordinate
                (boundary - rho) (boundary + rho)).Nonempty := by
          rcases hsection with ⟨point, hpointShading, hpointSlab⟩
          exact
            ⟨point, shading.subset_body index hpointShading,
              hpointSlab⟩
        have hbandMem : index ∈ band level :=
          Finset.mem_filter.mpr
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
  have hslowBound :
      (∑ index ∈ slow, weight index) ≤
        C * pureWZ2Prop62OuterSlowConstant *
          ENNReal.ofReal rho *
          Kakeya.realRpowENN delta 2 *
          family.enncard := by
    simpa only [slow, weight] using
      pureWZ2_prop62_outer_slow_boundary_mass
        hdelta hdeltaSmall hrho hdeltaRho
        hline shading coordinate hcwa
        (boundary := boundary)
  let common : ENNReal :=
    C * pureWZ2Prop62OuterBandConstant *
      ENNReal.ofReal rho *
      Kakeya.realRpowENN delta 2 *
      family.enncard
  have hbandBound :
      ∀ level ∈ levels,
        (∑ index ∈ band level, weight index) ≤ common := by
    intro level hlevel
    let scale := pureWZ2Prop62OuterDirectionScale rho level
    have hraw :=
      pureWZ2_prop62_outer_direction_band_boundary_mass
        hdelta hdeltaSmall hrho
        (pureWZ2_prop62_outer_direction_scale_pos
          (rho := rho) level)
        hline shading coordinate hcwa
        (boundary := boundary) (scale := scale)
    have hcoefficient :=
      pureWZ2_prop62_outer_band_coefficient
        hdelta hrho hdeltaRho
        (pureWZ2_prop62_outer_direction_scale_pos
          (rho := rho) level)
        (pureWZ2_prop62_rho_le_two_outer_direction_scale
          hrho level)
        (pureWZ2_prop62_outer_direction_scale_le_one
          hrhoOne level)
    calc
      (∑ index ∈ band level, weight index) ≤
          (C *
              ENNReal.ofReal
                (16 *
                  (8 * scale + 48 * delta + rho)) *
              family.enncard) *
            (4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  ((2 * rho + 48 * delta) / scale +
                    48 * delta))) := by
        simpa only [band, weight, scale] using hraw
      _ =
          C *
            (ENNReal.ofReal
                (16 * (8 * scale + 48 * delta + rho)) *
              (4 *
                ENNReal.ofReal
                  (Real.pi * (24 * delta) ^ 2 *
                    ((2 * rho + 48 * delta) / scale +
                      48 * delta)))) *
            family.enncard := by ring
      _ ≤
          C *
            (pureWZ2Prop62OuterBandConstant *
              ENNReal.ofReal rho *
              Kakeya.realRpowENN delta 2) *
            family.enncard := by
        gcongr
      _ = common := by
        dsimp only [common]
        ring
  have hlevels :
      (1 : ENNReal) ≤
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho))) =
      ∑ index : Fin family.card, weight index := rfl
    _ ≤
      (∑ index ∈ slow, weight index) +
        ∑ level ∈ levels, ∑ index ∈ band level, weight index :=
      hdecomposition
    _ ≤
      C * pureWZ2Prop62OuterSlowConstant *
          ENNReal.ofReal rho *
          Kakeya.realRpowENN delta 2 *
          family.enncard +
        ∑ _level ∈ levels, common :=
      add_le_add hslowBound <|
        Finset.sum_le_sum fun level hlevel =>
          hbandBound level hlevel
    _ =
      C * pureWZ2Prop62OuterSlowConstant *
          ENNReal.ofReal rho *
          Kakeya.realRpowENN delta 2 *
          family.enncard +
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
          common := by
      simp [levels, Finset.sum_const]
    _ ≤
      (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
          (C * pureWZ2Prop62OuterSlowConstant *
            ENNReal.ofReal rho *
            Kakeya.realRpowENN delta 2 *
            family.enncard) +
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
          common := by
      exact add_le_add
        (by
          simpa only [one_mul] using
            (mul_le_mul_right' hlevels
              (C * pureWZ2Prop62OuterSlowConstant *
                ENNReal.ofReal rho *
                Kakeya.realRpowENN delta 2 *
                family.enncard)))
        le_rfl
    _ =
      C *
        ((pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
          pureWZ2Prop62OuterFaceConstant) *
        ENNReal.ofReal rho *
        Kakeya.realRpowENN delta 2 *
        family.enncard := by
      dsimp only [common, pureWZ2Prop62OuterFaceConstant]
      ring

end Kakeya.Assouad

end
