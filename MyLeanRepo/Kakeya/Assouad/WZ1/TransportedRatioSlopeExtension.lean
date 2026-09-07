import MyLeanRepo.Kakeya.Assouad.WZ1.RatioLipschitzPoint3
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredSlopeConstruction
import MyLeanRepo.Kakeya.Assouad.WZ1.DistinguishedTubeSlopeExtension
import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Basic

/-!
# A scale-sharp transported normal-ratio slope

The two horizontal coordinates of the inverse-transpose normal are multiplied
by the same factor `100 * rho`.  Their ratio therefore has no `rho⁻¹` loss.
This module records the first-chart version of that cancellation.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The transported normal ratio is scale-sharp: within one fixed chart its
variation is controlled by the source plane-map variation, with no `rho⁻¹`
loss. -/
lemma slopeAtNormal_transported_pair_bound
    {sourceDelta rho : ℝ}
    (hrho : 0 < rho)
    (anchor : Kakeya.DeltaTube sourceDelta)
    (chart : WZ1HorizontalChart)
    {source : Set Point3}
    (planeMap : Point3 → Point3)
    (L : NNReal)
    (hplaneLipschitz : LipschitzOnWith L planeMap source)
    (hplaneUnit : ∀ point ∈ source, ‖planeMap point‖ = 1)
    (hNvStrong : ∀ point ∈ source,
      50 * rho ≤ ‖wz1AnchoredUnitRescalingNormalLinear
        anchor rho (planeMap point)‖)
    (hchart : ∀ point ∈ source,
      let normal := transportedNormal anchor rho hrho planeMap point
      match chart with
      | WZ1HorizontalChart.first => 1 / 3 ≤ |normal 0|
      | WZ1HorizontalChart.second => 1 / 3 ≤ |normal 1|)
    (first : Point3) (hfirst : first ∈ source)
    (second : Point3) (hsecond : second ∈ source) :
    |slopeAtNormal chart
        (transportedNormal anchor rho hrho planeMap first) -
      slopeAtNormal chart
        (transportedNormal anchor rho hrho planeMap second)| ≤
      (72 * (L : ℝ)) * dist first second := by
  let reflection := householderToE3 anchor.direction anchor.direction_unit
  let reflected : Point3 → Point3 := fun point => reflection (planeMap point)
  let raw : Point3 → Point3 := fun point =>
    wz1AnchoredUnitRescalingNormalLinear anchor rho (planeMap point)
  let normal : Point3 → Point3 := fun point =>
    transportedNormal anchor rho hrho planeMap point
  have hreflectedUnit : ∀ point ∈ source, ‖reflected point‖ = 1 := by
    intro point hpoint
    exact (reflection.norm_map (planeMap point)).trans
      (hplaneUnit point hpoint)
  have hreflectedLipschitz : ∀ p ∈ source, ∀ q ∈ source,
      dist (reflected p) (reflected q) ≤
        (L : ℝ) * dist p q := by
    intro p hp q hq
    have hsource := hplaneLipschitz.dist_le_mul p hp q hq
    have heq : dist (reflected p) (reflected q) =
        dist (planeMap p) (planeMap q) := by
      simp only [reflected, dist_eq_norm, ← map_sub]
      exact reflection.norm_map _
    rwa [heq]
  have hrelations : ∀ point ∈ source,
      let scale : ℝ := 100 * rho / ‖raw point‖
      normal point 0 = scale * reflected point 0 ∧
      normal point 1 = scale * reflected point 1 ∧
      0 < scale := by
    intro point hpoint
    let scale : ℝ := 100 * rho / ‖raw point‖
    have hnormPos : 0 < ‖raw point‖ :=
      lt_of_lt_of_le (by positivity) (hNvStrong point hpoint)
    have hraw0 : raw point 0 = 100 * rho * reflected point 0 := by
      change
        (wz1AnchoredUnitRescalingNormalLinear
          anchor rho (planeMap point)) 0 = _
      rw [show wz1AnchoredUnitRescalingNormalLinear
          anchor rho (planeMap point) =
          transverseScaleLin (1 / (100 * rho)) (reflected point) by rfl]
      rw [transverseScaleLin_coord0]
      field_simp [hrho.ne']
    have hraw1 : raw point 1 = 100 * rho * reflected point 1 := by
      change
        (wz1AnchoredUnitRescalingNormalLinear
          anchor rho (planeMap point)) 1 = _
      rw [show wz1AnchoredUnitRescalingNormalLinear
          anchor rho (planeMap point) =
          transverseScaleLin (1 / (100 * rho)) (reflected point) by rfl]
      rw [transverseScaleLin_coord1]
      field_simp [hrho.ne']
    have hnormal0 : normal point 0 = scale * reflected point 0 := by
      change ((1 / ‖raw point‖) • raw point) 0 = _
      rw [PiLp.smul_apply, smul_eq_mul, hraw0]
      dsimp only [scale]
      field_simp [hnormPos.ne']
    have hnormal1 : normal point 1 = scale * reflected point 1 := by
      change ((1 / ‖raw point‖) • raw point) 1 = _
      rw [PiLp.smul_apply, smul_eq_mul, hraw1]
      dsimp only [scale]
      field_simp [hnormPos.ne']
    exact ⟨hnormal0, hnormal1, by positivity⟩
  have hreflectedChart : ∀ point ∈ source,
      match chart with
      | WZ1HorizontalChart.first => 1 / 6 ≤ |reflected point 0|
      | WZ1HorizontalChart.second => 1 / 6 ≤ |reflected point 1| := by
    intro point hpoint
    have hrel := hrelations point hpoint
    have hnormPos : 0 < ‖raw point‖ :=
      lt_of_lt_of_le (by positivity) (hNvStrong point hpoint)
    cases chart with
    | first =>
        have hscaled : |normal point 0| * ‖raw point‖ =
            100 * rho * |reflected point 0| := by
          rw [hrel.1, abs_mul, abs_of_pos hrel.2.2]
          field_simp [hnormPos.ne']
        have hproduct : (1 / 3 : ℝ) * (50 * rho) ≤
            |normal point 0| * ‖raw point‖ :=
          mul_le_mul (hchart point hpoint) (hNvStrong point hpoint)
            (by positivity) (by positivity)
        have hmultiplied : (1 / 6 : ℝ) * (100 * rho) ≤
            |reflected point 0| * (100 * rho) := by
          rw [show (1 / 6 : ℝ) * (100 * rho) =
              (1 / 3 : ℝ) * (50 * rho) by ring]
          rw [mul_comm |reflected point 0| (100 * rho), ← hscaled]
          exact hproduct
        exact le_of_mul_le_mul_right hmultiplied (by positivity)
    | second =>
        have hscaled : |normal point 1| * ‖raw point‖ =
            100 * rho * |reflected point 1| := by
          rw [hrel.2.1, abs_mul, abs_of_pos hrel.2.2]
          field_simp [hnormPos.ne']
        have hproduct : (1 / 3 : ℝ) * (50 * rho) ≤
            |normal point 1| * ‖raw point‖ :=
          mul_le_mul (hchart point hpoint) (hNvStrong point hpoint)
            (by positivity) (by positivity)
        have hmultiplied : (1 / 6 : ℝ) * (100 * rho) ≤
            |reflected point 1| * (100 * rho) := by
          rw [show (1 / 6 : ℝ) * (100 * rho) =
              (1 / 3 : ℝ) * (50 * rho) by ring]
          rw [mul_comm |reflected point 1| (100 * rho), ← hscaled]
          exact hproduct
        exact le_of_mul_le_mul_right hmultiplied (by positivity)
  have hcoord0Upper : ∀ point ∈ source, |reflected point 0| ≤ 1 := by
    intro point hpoint
    exact (PiLp.norm_apply_le (reflected point) 0).trans_eq
      (hreflectedUnit point hpoint)
  have hcoord1Upper : ∀ point ∈ source, |reflected point 1| ≤ 1 := by
    intro point hpoint
    exact (PiLp.norm_apply_le (reflected point) 1).trans_eq
      (hreflectedUnit point hpoint)
  have hratioEq : ∀ point ∈ source,
      slopeAtNormal chart (normal point) =
        match chart with
        | WZ1HorizontalChart.first =>
            reflected point 1 / reflected point 0
        | WZ1HorizontalChart.second =>
            reflected point 0 / reflected point 1 := by
    intro point hpoint
    have hrel := hrelations point hpoint
    cases chart with
    | first =>
        have hdenom : reflected point 0 ≠ 0 := by
          have : 0 < |reflected point 0| :=
            lt_of_lt_of_le (by norm_num) (hreflectedChart point hpoint)
          exact abs_ne_zero.mp this.ne'
        have hrawNorm : ‖raw point‖ ≠ 0 := by
          have hpos : 0 < ‖raw point‖ :=
            lt_of_lt_of_le (by positivity) (hNvStrong point hpoint)
          exact hpos.ne'
        have hscale :
            100 * rho / ‖raw point‖ ≠ 0 := by
          exact div_ne_zero (by positivity) hrawNorm
        change normal point 1 / normal point 0 = _
        rw [hrel.1, hrel.2.1]
        field_simp [hscale, hdenom, hrawNorm]
    | second =>
        have hdenom : reflected point 1 ≠ 0 := by
          have : 0 < |reflected point 1| :=
            lt_of_lt_of_le (by norm_num) (hreflectedChart point hpoint)
          exact abs_ne_zero.mp this.ne'
        have hrawNorm : ‖raw point‖ ≠ 0 := by
          have hpos : 0 < ‖raw point‖ :=
            lt_of_lt_of_le (by positivity) (hNvStrong point hpoint)
          exact hpos.ne'
        have hscale :
            100 * rho / ‖raw point‖ ≠ 0 := by
          exact div_ne_zero (by positivity) hrawNorm
        change normal point 0 / normal point 1 = _
        rw [hrel.1, hrel.2.1]
        field_simp [hscale, hdenom, hrawNorm]
  cases chart with
  | first =>
      have hratio := ratio_lipschitz_on_point3
        (n := reflected) (L := (L : ℝ)) (c := 1 / 6) (s := source)
        (by positivity) hreflectedLipschitz (by norm_num)
        (by simpa using hreflectedChart) hcoord0Upper hcoord1Upper
        first hfirst second hsecond
      rw [hratioEq first hfirst, hratioEq second hsecond]
      convert hratio using 1 <;> ring
  | second =>
      let swapped : Point3 → Point3 := fun point =>
        wz1Swap01 (reflected point)
      have hswappedDist : ∀ p q, dist (swapped p) (swapped q) =
          dist (reflected p) (reflected q) := by
        intro p q
        change dist (wz1Swap01 (reflected p))
          (wz1Swap01 (reflected q)) = _
        rw [dist_eq_norm, dist_eq_norm, ← wz1Swap01.map_sub,
          wz1Swap01.norm_map]
      have hswappedLip : ∀ p ∈ source, ∀ q ∈ source,
          dist (swapped p) (swapped q) ≤ (L : ℝ) * dist p q := by
        intro p hp q hq
        rw [hswappedDist]
        exact hreflectedLipschitz p hp q hq
      have hswappedLower : ∀ point ∈ source,
          1 / 6 ≤ |swapped point 0| := by
        intro point hpoint
        simpa [swapped, wz1Swap01_apply, point3, PiLp.single_apply] using
          hreflectedChart point hpoint
      have hswapped0Upper : ∀ point ∈ source, |swapped point 0| ≤ 1 := by
        intro point hpoint
        simpa [swapped, wz1Swap01_apply, point3, PiLp.single_apply] using
          hcoord1Upper point hpoint
      have hswapped1Upper : ∀ point ∈ source, |swapped point 1| ≤ 1 := by
        intro point hpoint
        simpa [swapped, wz1Swap01_apply, point3, PiLp.single_apply] using
          hcoord0Upper point hpoint
      have hratio := ratio_lipschitz_on_point3
        (n := swapped) (L := (L : ℝ)) (c := 1 / 6) (s := source)
        (by positivity) hswappedLip (by norm_num) hswappedLower
        hswapped0Upper hswapped1Upper first hfirst second hsecond
      have hfirst0 : swapped first 0 = reflected first 1 := by
        simp [swapped, wz1Swap01_apply, point3, PiLp.single_apply]
      have hfirst1 : swapped first 1 = reflected first 0 := by
        simp [swapped, wz1Swap01_apply, point3, PiLp.single_apply]
      have hsecond0 : swapped second 0 = reflected second 1 := by
        simp [swapped, wz1Swap01_apply, point3, PiLp.single_apply]
      have hsecond1 : swapped second 1 = reflected second 0 := by
        simp [swapped, wz1Swap01_apply, point3, PiLp.single_apply]
      rw [hratioEq first hfirst, hratioEq second hsecond]
      change
        |reflected first 0 / reflected first 1 -
          reflected second 0 / reflected second 1| ≤
          (72 * (L : ℝ)) * dist first second
      rw [hfirst0, hfirst1, hsecond0, hsecond1] at hratio
      convert hratio using 1 <;> ring

/-- On retained approximate height samples from the distinguished source
tube, the first-chart transported normal ratio extends with a fixed multiple
of the source plane-map Lipschitz constant. -/
theorem transported_first_ratio_slope_extension
    {sourceDelta rho heightError : ℝ}
    (hsourceDelta : 0 ≤ sourceDelta)
    (hrho : 0 < rho)
    (hheightError : 0 ≤ heightError)
    (anchor : Kakeya.DeltaTube sourceDelta)
    {heights : Set ℝ}
    (sample : ℝ → Point3)
    (hsampleCarrier : ∀ z ∈ heights, sample z ∈ anchor.carrier)
    (hsampleHeight : ∀ z ∈ heights,
      |distinguishedTubeHeight anchor (sample z) - z| ≤ heightError)
    (hheightSeparated :
      ∀ first ∈ heights, ∀ second ∈ heights, first ≠ second →
        4 * sourceDelta + 2 * heightError ≤ |first - second|)
    (source : Set Point3)
    (hsampleSource : ∀ z ∈ heights, sample z ∈ source)
    (planeMap : Point3 → Point3)
    (L : NNReal)
    (hplaneLipschitz : LipschitzOnWith L planeMap source)
    (hplaneUnit : ∀ z ∈ heights, ‖planeMap (sample z)‖ = 1)
    (hNvStrong : ∀ z ∈ heights,
      50 * rho ≤ ‖wz1AnchoredUnitRescalingNormalLinear
        anchor rho (planeMap (sample z))‖)
    (hchart : ∀ z ∈ heights,
      1 / 3 ≤ |(transportedNormal anchor rho hrho planeMap (sample z)) 0|) :
    ∃ slope : ℝ → ℝ,
      LipschitzWith (144 * L) slope ∧
      (∀ z, |slope z| ≤ 3) ∧
      Set.EqOn
        (fun z =>
          (transportedNormal anchor rho hrho planeMap (sample z)) 1 /
            (transportedNormal anchor rho hrho planeMap (sample z)) 0)
        slope heights := by
  let reflection := householderToE3 anchor.direction anchor.direction_unit
  let reflected : ℝ → Point3 := fun z => reflection (planeMap (sample z))
  let rawNormal : ℝ → Point3 := fun z =>
    wz1AnchoredUnitRescalingNormalLinear anchor rho (planeMap (sample z))
  let normal : ℝ → Point3 := fun z =>
    transportedNormal anchor rho hrho planeMap (sample z)
  have hreflectedUnit : ∀ z ∈ heights, ‖reflected z‖ = 1 := by
    intro z hz
    exact (householderToE3_norm anchor.direction anchor.direction_unit
      (planeMap (sample z))).trans (hplaneUnit z hz)
  have hsampleDistance : ∀ first ∈ heights, ∀ second ∈ heights,
      dist (sample first) (sample second) ≤ 2 * dist first second := by
    intro first hfirst second hsecond
    by_cases heq : first = second
    · subst second
      simp
    · have hdistance := same_tube_dist_le_height_add_four_delta
        hsourceDelta anchor (hsampleCarrier first hfirst)
          (hsampleCarrier second hsecond)
      have hfirstError := hsampleHeight first hfirst
      have hsecondError := hsampleHeight second hsecond
      have hheightDifference :
          |distinguishedTubeHeight anchor (sample first) -
              distinguishedTubeHeight anchor (sample second)| ≤
            |first - second| + 2 * heightError := by
        calc
          |distinguishedTubeHeight anchor (sample first) -
              distinguishedTubeHeight anchor (sample second)|
              = |(distinguishedTubeHeight anchor (sample first) - first) +
                  (first - second) +
                  (second - distinguishedTubeHeight anchor (sample second))| := by
                congr 1
                ring
          _ ≤ |distinguishedTubeHeight anchor (sample first) - first| +
                |first - second| +
                |second - distinguishedTubeHeight anchor (sample second)| := by
              calc
                _ ≤ |(distinguishedTubeHeight anchor (sample first) - first) +
                      (first - second)| +
                    |second - distinguishedTubeHeight anchor (sample second)| :=
                  abs_add_le _ _
                _ ≤ (|distinguishedTubeHeight anchor (sample first) - first| +
                      |first - second|) +
                    |second - distinguishedTubeHeight anchor (sample second)| := by
                  gcongr
                  exact abs_add_le _ _
          _ ≤ heightError + |first - second| + heightError := by
              have hsecondError' :
                  |second - distinguishedTubeHeight anchor (sample second)| ≤
                    heightError := by
                rw [abs_sub_comm]
                exact hsecondError
              linarith
          _ = |first - second| + 2 * heightError := by ring
      rw [Real.dist_eq]
      calc
        dist (sample first) (sample second)
            ≤ |distinguishedTubeHeight anchor (sample first) -
                  distinguishedTubeHeight anchor (sample second)| +
                4 * sourceDelta := hdistance
        _ ≤ (|first - second| + 2 * heightError) +
              4 * sourceDelta := by gcongr
        _ ≤ 2 * |first - second| := by
          have hsep := hheightSeparated first hfirst second hsecond heq
          linarith
  have hreflectedLipschitz : ∀ first ∈ heights, ∀ second ∈ heights,
      dist (reflected first) (reflected second) ≤
        (2 * (L : ℝ)) * |first - second| := by
    intro first hfirst second hsecond
    have hplane := hplaneLipschitz.dist_le_mul
      (sample first) (hsampleSource first hfirst)
      (sample second) (hsampleSource second hsecond)
    have hreflect : dist (reflected first) (reflected second) =
        dist (planeMap (sample first)) (planeMap (sample second)) := by
      simp only [reflected, dist_eq_norm, ← map_sub]
      exact householderToE3_norm anchor.direction anchor.direction_unit _
    rw [hreflect]
    calc
      dist (planeMap (sample first)) (planeMap (sample second))
          ≤ (L : ℝ) * dist (sample first) (sample second) := hplane
      _ ≤ (L : ℝ) * (2 * dist first second) := by
        gcongr
        exact hsampleDistance first hfirst second hsecond
      _ = (2 * (L : ℝ)) * |first - second| := by
        rw [Real.dist_eq]
        ring
  have hcoordinateRelations : ∀ z ∈ heights,
      let scale : ℝ := 100 * rho / ‖rawNormal z‖
      normal z 0 = scale * reflected z 0 ∧
      normal z 1 = scale * reflected z 1 ∧
      0 < scale := by
    intro z hz
    let scale : ℝ := 100 * rho / ‖rawNormal z‖
    have hnormPos : 0 < ‖rawNormal z‖ :=
      lt_of_lt_of_le (by positivity) (hNvStrong z hz)
    have hraw0 : rawNormal z 0 = 100 * rho * reflected z 0 := by
      change
        (wz1AnchoredUnitRescalingNormalLinear
          anchor rho (planeMap (sample z))) 0 = _
      rw [show wz1AnchoredUnitRescalingNormalLinear
          anchor rho (planeMap (sample z)) =
          transverseScaleLin (1 / (100 * rho)) (reflected z) by rfl]
      rw [transverseScaleLin_coord0]
      field_simp [hrho.ne']
    have hraw1 : rawNormal z 1 = 100 * rho * reflected z 1 := by
      change
        (wz1AnchoredUnitRescalingNormalLinear
          anchor rho (planeMap (sample z))) 1 = _
      rw [show wz1AnchoredUnitRescalingNormalLinear
          anchor rho (planeMap (sample z)) =
          transverseScaleLin (1 / (100 * rho)) (reflected z) by rfl]
      rw [transverseScaleLin_coord1]
      field_simp [hrho.ne']
    have hnormal0 : normal z 0 = scale * reflected z 0 := by
      change ((1 / ‖rawNormal z‖) • rawNormal z) 0 = _
      rw [PiLp.smul_apply, smul_eq_mul, hraw0]
      dsimp only [scale]
      field_simp [hnormPos.ne']
    have hnormal1 : normal z 1 = scale * reflected z 1 := by
      change ((1 / ‖rawNormal z‖) • rawNormal z) 1 = _
      rw [PiLp.smul_apply, smul_eq_mul, hraw1]
      dsimp only [scale]
      field_simp [hnormPos.ne']
    exact ⟨hnormal0, hnormal1, by positivity⟩
  have hreflected0 : ∀ z ∈ heights, 1 / 6 ≤ |reflected z 0| := by
    intro z hz
    let scale : ℝ := 100 * rho / ‖rawNormal z‖
    have hrelations := hcoordinateRelations z hz
    change 1 / 6 ≤ |reflected z 0|
    have hnormPos : 0 < ‖rawNormal z‖ :=
      lt_of_lt_of_le (by positivity) (hNvStrong z hz)
    have hscaled : |normal z 0| * ‖rawNormal z‖ =
        100 * rho * |reflected z 0| := by
      rw [hrelations.1, abs_mul, abs_of_pos hrelations.2.2]
      dsimp only [scale]
      field_simp [hnormPos.ne']
    have hproduct : (1 / 3 : ℝ) * (50 * rho) ≤
        |normal z 0| * ‖rawNormal z‖ := by
      exact mul_le_mul (hchart z hz) (hNvStrong z hz)
        (by positivity) (by positivity)
    have hmultiplied :
        (1 / 6 : ℝ) * (100 * rho) ≤
          |reflected z 0| * (100 * rho) := by
      rw [show (1 / 6 : ℝ) * (100 * rho) =
          (1 / 3 : ℝ) * (50 * rho) by ring]
      rw [mul_comm |reflected z 0| (100 * rho), ← hscaled]
      exact hproduct
    exact le_of_mul_le_mul_right hmultiplied (by positivity)
  have hreflected0Upper : ∀ z ∈ heights, |reflected z 0| ≤ 1 := by
    intro z hz
    exact (PiLp.norm_apply_le (reflected z) 0).trans_eq
      (hreflectedUnit z hz)
  have hreflected1Upper : ∀ z ∈ heights, |reflected z 1| ≤ 1 := by
    intro z hz
    exact (PiLp.norm_apply_le (reflected z) 1).trans_eq
      (hreflectedUnit z hz)
  let rawSlope : ℝ → ℝ := fun z => reflected z 1 / reflected z 0
  have hrawSlopeLipschitz : LipschitzOnWith (144 * L) rawSlope heights := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro first hfirst second hsecond
    have hratio := ratio_lipschitz_on_real
      (n := reflected) (L := 2 * (L : ℝ)) (c := 1 / 6)
      (s := heights) (by positivity) hreflectedLipschitz
      (by norm_num) hreflected0 hreflected0Upper hreflected1Upper
      first hfirst second hsecond
    rw [Real.dist_eq, Real.dist_eq]
    change |reflected first 1 / reflected first 0 -
      reflected second 1 / reflected second 0| ≤
        ((144 * L : NNReal) : ℝ) * |first - second|
    convert hratio using 1 <;> push_cast <;> ring
  let slope := extendAndClip rawSlope heights (144 * L) hrawSlopeLipschitz
  have hslopeLipschitz : LipschitzWith (144 * L) slope :=
    extendAndClip_lipschitz rawSlope heights (144 * L) hrawSlopeLipschitz
  have hslopeBound : ∀ z, |slope z| ≤ 3 :=
    extendAndClip_bound rawSlope heights (144 * L) hrawSlopeLipschitz
  have hslopeEq : Set.EqOn
      (fun z => normal z 1 / normal z 0) slope heights := by
    intro z hz
    have hrelations := hcoordinateRelations z hz
    have hreflected0Ne : reflected z 0 ≠ 0 := by
      have : 0 < |reflected z 0| :=
        lt_of_lt_of_le (by norm_num) (hreflected0 z hz)
      exact abs_ne_zero.mp this.ne'
    have hnormPos : 0 < ‖rawNormal z‖ :=
      lt_of_lt_of_le (by positivity) (hNvStrong z hz)
    have hscaleNe :
        (100 * rho / ‖rawNormal z‖) ≠ 0 := by positivity
    have hratioEq : normal z 1 / normal z 0 = rawSlope z := by
      dsimp only [rawSlope]
      rw [hrelations.1, hrelations.2.1]
      field_simp [hscaleNe, hreflected0Ne, hnormPos.ne']
    change normal z 1 / normal z 0 = slope z
    rw [hratioEq]
    let extension : ℝ → ℝ :=
      Classical.choose hrawSlopeLipschitz.extend_real
    have hextensionEq : rawSlope z = extension z :=
      (Classical.choose_spec hrawSlopeLipschitz.extend_real).2 hz
    have hrawBound : |rawSlope z| ≤ 3 := by
      rw [← hratioEq]
      have hnormalUnit : ‖normal z‖ = 1 := by
        change ‖(1 / ‖rawNormal z‖) • rawNormal z‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp [hnormPos.ne']
      have hcoordinate : |normal z 1| ≤ 1 :=
        (PiLp.norm_apply_le (normal z) 1).trans_eq hnormalUnit
      rw [abs_div]
      calc
        |normal z 1| / |normal z 0| ≤ 1 / |normal z 0| := by gcongr
        _ ≤ 1 / (1 / 3 : ℝ) := by
          gcongr
          exact hchart z hz
        _ = 3 := by norm_num
    have hleft : -3 ≤ rawSlope z := (abs_le.mp hrawBound).1
    have hright : rawSlope z ≤ 3 := (abs_le.mp hrawBound).2
    change rawSlope z = max (min (extension z) 3) (-3)
    rw [← hextensionEq]
    simp [min_eq_left hright, max_eq_left hleft]
  exact ⟨slope, hslopeLipschitz, hslopeBound, hslopeEq⟩

/-- The second-chart version follows by conjugating the source normal field
with Householder reflection and the horizontal coordinate swap. -/
theorem transported_second_ratio_slope_extension
    {sourceDelta rho heightError : ℝ}
    (hsourceDelta : 0 ≤ sourceDelta)
    (hrho : 0 < rho)
    (hheightError : 0 ≤ heightError)
    (anchor : Kakeya.DeltaTube sourceDelta)
    {heights : Set ℝ}
    (sample : ℝ → Point3)
    (hsampleCarrier : ∀ z ∈ heights, sample z ∈ anchor.carrier)
    (hsampleHeight : ∀ z ∈ heights,
      |distinguishedTubeHeight anchor (sample z) - z| ≤ heightError)
    (hheightSeparated :
      ∀ first ∈ heights, ∀ second ∈ heights, first ≠ second →
        4 * sourceDelta + 2 * heightError ≤ |first - second|)
    (source : Set Point3)
    (hsampleSource : ∀ z ∈ heights, sample z ∈ source)
    (planeMap : Point3 → Point3)
    (L : NNReal)
    (hplaneLipschitz : LipschitzOnWith L planeMap source)
    (hplaneUnit : ∀ z ∈ heights, ‖planeMap (sample z)‖ = 1)
    (hNvStrong : ∀ z ∈ heights,
      50 * rho ≤ ‖wz1AnchoredUnitRescalingNormalLinear
        anchor rho (planeMap (sample z))‖)
    (hchart : ∀ z ∈ heights,
      1 / 3 ≤ |(transportedNormal anchor rho hrho planeMap (sample z)) 1|) :
    ∃ slope : ℝ → ℝ,
      LipschitzWith (144 * L) slope ∧
      (∀ z, |slope z| ≤ 3) ∧
      Set.EqOn
        (fun z =>
          (transportedNormal anchor rho hrho planeMap (sample z)) 0 /
            (transportedNormal anchor rho hrho planeMap (sample z)) 1)
        slope heights := by
  let reflection := householderToE3 anchor.direction anchor.direction_unit
  let swappedPlaneMap : Point3 → Point3 := fun point =>
    reflection (wz1Swap01 (reflection (planeMap point)))
  have hreflectionSwapped : ∀ point,
      reflection (swappedPlaneMap point) =
        wz1Swap01 (reflection (planeMap point)) := by
    intro point
    simp only [swappedPlaneMap]
    exact householderToE3_involution anchor.direction
      anchor.direction_unit _
  have hswappedLipschitz :
      LipschitzOnWith L swappedPlaneMap source := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    have hsource := hplaneLipschitz.dist_le_mul
      first hfirst second hsecond
    have heq :
        dist (swappedPlaneMap first) (swappedPlaneMap second) =
          dist (planeMap first) (planeMap second) := by
      simp only [swappedPlaneMap, dist_eq_norm, ← map_sub]
      rw [reflection.norm_map, wz1Swap01.norm_map, reflection.norm_map]
    rw [heq]
    exact hsource
  have hswappedUnit : ∀ z ∈ heights,
      ‖swappedPlaneMap (sample z)‖ = 1 := by
    intro z hz
    calc
      ‖swappedPlaneMap (sample z)‖
          = ‖wz1Swap01 (reflection (planeMap (sample z)))‖ :=
        reflection.norm_map _
      _ = ‖reflection (planeMap (sample z))‖ := wz1Swap01.norm_map _
      _ = ‖planeMap (sample z)‖ := reflection.norm_map _
      _ = 1 := hplaneUnit z hz
  have hrawSwap : ∀ point,
      wz1AnchoredUnitRescalingNormalLinear anchor rho
          (swappedPlaneMap point) =
        wz1Swap01
          (wz1AnchoredUnitRescalingNormalLinear anchor rho
            (planeMap point)) := by
    intro point
    have hreflect := hreflectionSwapped point
    rw [show wz1AnchoredUnitRescalingNormalLinear anchor rho
          (swappedPlaneMap point) =
        transverseScaleLin (1 / (100 * rho))
          (reflection (swappedPlaneMap point)) by rfl]
    rw [show wz1AnchoredUnitRescalingNormalLinear anchor rho
          (planeMap point) =
        transverseScaleLin (1 / (100 * rho))
          (reflection (planeMap point)) by rfl]
    rw [hreflect]
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [wz1Swap01_apply, point3, PiLp.single_apply,
        transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2] <;>
      field_simp [hrho.ne']
  have hnormalSwap : ∀ point,
      transportedNormal anchor rho hrho swappedPlaneMap point =
        wz1Swap01 (transportedNormal anchor rho hrho planeMap point) := by
    intro point
    let raw := wz1AnchoredUnitRescalingNormalLinear anchor rho
      (planeMap point)
    have hraw := hrawSwap point
    have hnorm :
        ‖wz1AnchoredUnitRescalingNormalLinear anchor rho
            (swappedPlaneMap point)‖ = ‖raw‖ := by
      rw [hraw]
      exact wz1Swap01.norm_map raw
    change
      (1 / ‖wz1AnchoredUnitRescalingNormalLinear anchor rho
          (swappedPlaneMap point)‖) •
          wz1AnchoredUnitRescalingNormalLinear anchor rho
            (swappedPlaneMap point) =
        wz1Swap01 ((1 / ‖raw‖) • raw)
    rw [hnorm, hraw, wz1Swap01.map_smul]
  have hswappedStrong : ∀ z ∈ heights,
      50 * rho ≤ ‖wz1AnchoredUnitRescalingNormalLinear
        anchor rho (swappedPlaneMap (sample z))‖ := by
    intro z hz
    rw [hrawSwap, wz1Swap01.norm_map]
    exact hNvStrong z hz
  have hswappedChart : ∀ z ∈ heights,
      1 / 3 ≤
        |(transportedNormal anchor rho hrho
          swappedPlaneMap (sample z)) 0| := by
    intro z hz
    rw [hnormalSwap, wz1Swap01_apply]
    simpa [point3, PiLp.single_apply] using hchart z hz
  rcases transported_first_ratio_slope_extension
      hsourceDelta hrho hheightError anchor sample hsampleCarrier
      hsampleHeight hheightSeparated source hsampleSource swappedPlaneMap L
      hswappedLipschitz hswappedUnit hswappedStrong hswappedChart with
    ⟨slope, hslopeLipschitz, hslopeBound, hslopeEq⟩
  refine ⟨slope, hslopeLipschitz, hslopeBound, ?_⟩
  intro z hz
  have heq := hslopeEq hz
  change
    (transportedNormal anchor rho hrho
      swappedPlaneMap (sample z)) 1 /
      (transportedNormal anchor rho hrho
        swappedPlaneMap (sample z)) 0 = slope z at heq
  rw [hnormalSwap, wz1Swap01_apply] at heq
  simpa [point3, PiLp.single_apply] using heq

end Kakeya.Assouad
