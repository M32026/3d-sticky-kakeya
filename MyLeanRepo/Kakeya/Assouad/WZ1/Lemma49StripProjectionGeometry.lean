import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49RadialConeDiameter
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49UnitCircleFrostman
import Mathlib.Data.Finset.Basic

/-!
# Strip radial-projection geometry for WZ1 Lemma 8.13

These are the geometric consequences of the closed partial cone-diameter
estimate used in Step 2 of the paper proof.
-/

namespace Kakeya.Assouad

noncomputable section

/--
Angular separation lower bound from the cone-diameter contrapositive.
-/
lemma strip_angular_separation_lower_bound
    {base direction viewpoint first second : Point2}
    {width side bound u : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hwidth : 0 < width)
    (hside : 0 < side)
    (hbound : 0 < bound)
    (hfirstStrip :
      |inner ℝ (first - base) (wz1Perp2 direction)| ≤ width / 2)
    (hsecondStrip :
      |inner ℝ (second - base) (wz1Perp2 direction)| ≤ width / 2)
    (hfirstSide :
      side / 2 ≤ inner ℝ (first - viewpoint) (wz1Perp2 direction))
    (hsecondSide :
      side / 2 ≤ inner ℝ (second - viewpoint) (wz1Perp2 direction))
    (hfirstBound : ‖first - viewpoint‖ ≤ bound)
    (hsecondBound : ‖second - viewpoint‖ ≤ bound)
    (hu : u ≤ dist first second)
    (h_threshold : width + 2 * bound * width / side < u) :
    (u - width - 2 * bound * width / side) /
          (bound + 2 * bound ^ 2 / side) ≤
      ‖wz1Lemma49RadialDirection viewpoint first -
        wz1Lemma49RadialDirection viewpoint second‖ := by
  let angularConstant : ℝ :=
    bound + 2 * bound ^ 2 / side
  let widthError : ℝ :=
    width + 2 * bound * width / side
  have hangularConstant : 0 < angularConstant := by
    dsimp only [angularConstant]
    positivity
  have hnumerator : 0 < u - widthError := by
    dsimp only [widthError]
    linarith
  let target : ℝ := (u - widthError) / angularConstant
  have htarget : 0 < target := by
    dsimp only [target]
    positivity
  have h_target_eq :
      target =
        (u - width - 2 * bound * width / side) /
          angularConstant := by
    simp [target, widthError]
    ring
  let angularDistance : ℝ :=
    ‖wz1Lemma49RadialDirection viewpoint first -
      wz1Lemma49RadialDirection viewpoint second‖
  by_contra hnot
  have hangular_lt : angularDistance < target := by
    have :
        ¬ target ≤ angularDistance := by
      simpa [angularDistance, h_target_eq] using hnot
    exact lt_of_not_ge this
  let aperture : ℝ := max angularDistance (target / 2)
  have haperture : 0 < aperture := by
    exact lt_max_of_lt_right (by
      dsimp only [target] at htarget ⊢
      linarith)
  have hangular_le : angularDistance ≤ aperture :=
    le_max_left _ _
  have haperture_lt : aperture < target :=
    max_lt hangular_lt (by linarith)
  have hdiameter :
      dist first second ≤
        bound * aperture +
          2 * bound ^ 2 * aperture / side +
          width + 2 * bound * width / side :=
    wz1_lemma49_partial_cone_diameter_bounded
      hdirection hwidth hside hbound
      hfirstStrip hsecondStrip hfirstSide hsecondSide
      haperture hangular_le hfirstBound hsecondBound
  have hrhs :
      bound * aperture +
          2 * bound ^ 2 * aperture / side +
          width + 2 * bound * width / side < u := by
    have hlinear :
        bound * aperture +
            2 * bound ^ 2 * aperture / side =
          angularConstant * aperture := by
      dsimp only [angularConstant]
      ring
    rw [hlinear]
    have hmul :
        angularConstant * aperture <
          angularConstant * target :=
      mul_lt_mul_of_pos_left haperture_lt hangularConstant
    have hcancel :
        angularConstant * target = u - widthError := by
      dsimp only [target]
      field_simp [hangularConstant.ne']
    dsimp only [widthError] at hcancel ⊢
    linarith
  exact (not_lt_of_ge hu) (hdiameter.trans_lt hrhs)

/-- Unit-ball specialization, where every source-to-viewpoint distance is at
most two. -/
lemma strip_angular_separation_lower_bound_unitBall
    {base direction viewpoint first second : Point2}
    {width side u : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hwidth : 0 < width)
    (hside : 0 < side)
    (hfirstStrip :
      |inner ℝ (first - base) (wz1Perp2 direction)| ≤ width / 2)
    (hsecondStrip :
      |inner ℝ (second - base) (wz1Perp2 direction)| ≤ width / 2)
    (hfirstSide :
      side / 2 ≤ inner ℝ (first - viewpoint) (wz1Perp2 direction))
    (hsecondSide :
      side / 2 ≤ inner ℝ (second - viewpoint) (wz1Perp2 direction))
    (hfirstBall : ‖first‖ ≤ 1)
    (hsecondBall : ‖second‖ ≤ 1)
    (hviewpointBall : ‖viewpoint‖ ≤ 1)
    (hu : u ≤ dist first second)
    (h_threshold : width + 4 * width / side < u) :
    (u - width - 4 * width / side) / (2 + 8 / side) ≤
      ‖wz1Lemma49RadialDirection viewpoint first -
        wz1Lemma49RadialDirection viewpoint second‖ := by
  have hfirstBound : ‖first - viewpoint‖ ≤ 2 := by
    calc
      ‖first - viewpoint‖ ≤ ‖first‖ + ‖viewpoint‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  have hsecondBound : ‖second - viewpoint‖ ≤ 2 := by
    calc
      ‖second - viewpoint‖ ≤ ‖second‖ + ‖viewpoint‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  have h_threshold' :
      width + 2 * (2 : ℝ) * width / side < u := by
    convert h_threshold using 1 <;> ring
  convert
    strip_angular_separation_lower_bound
      hdirection hwidth hside (by norm_num)
      hfirstStrip hsecondStrip hfirstSide hsecondSide
      hfirstBound hsecondBound hu h_threshold'
    using 1 <;> ring

/-- If all radial directions of a source set lie in one angular cap, then the
source has the corresponding Euclidean diameter bound. -/
lemma cone_source_diameter_bound
    {source : Finset Point2}
    {base direction viewpoint : Point2}
    {width side bound aperture : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hwidth : 0 < width)
    (hside : 0 < side)
    (hbound : 0 < bound)
    (haperture : 0 < aperture)
    (hsourceStrip : ∀ point ∈ source,
      |inner ℝ (point - base) (wz1Perp2 direction)| ≤ width / 2)
    (hsourceSide : ∀ point ∈ source,
      side / 2 ≤
        inner ℝ (point - viewpoint) (wz1Perp2 direction))
    (hsourceBound : ∀ point ∈ source,
      ‖point - viewpoint‖ ≤ bound)
    (hsourceAngular : ∀ first ∈ source, ∀ second ∈ source,
      ‖wz1Lemma49RadialDirection viewpoint first -
          wz1Lemma49RadialDirection viewpoint second‖ ≤ aperture) :
    ∀ first ∈ source, ∀ second ∈ source,
      dist first second ≤
        bound * aperture +
          2 * bound ^ 2 * aperture / side +
          width + 2 * bound * width / side := by
  intro first hfirst second hsecond
  exact
    wz1_lemma49_partial_cone_diameter_bounded
      hdirection hwidth hside hbound
      (hsourceStrip first hfirst)
      (hsourceStrip second hsecond)
      (hsourceSide first hfirst)
      (hsourceSide second hsecond)
      haperture
      (hsourceAngular first hfirst second hsecond)
      (hsourceBound first hfirst)
      (hsourceBound second hsecond)

/-- Unit-ball specialization of `cone_source_diameter_bound`. -/
lemma cone_source_diameter_bound_unitBall
    {source : Finset Point2}
    {base direction viewpoint : Point2}
    {width side aperture : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hwidth : 0 < width)
    (hside : 0 < side)
    (haperture : 0 < aperture)
    (hsourceStrip : ∀ point ∈ source,
      |inner ℝ (point - base) (wz1Perp2 direction)| ≤ width / 2)
    (hsourceSide : ∀ point ∈ source,
      side / 2 ≤
        inner ℝ (point - viewpoint) (wz1Perp2 direction))
    (hsourceBall : ∀ point ∈ source, ‖point‖ ≤ 1)
    (hviewpointBall : ‖viewpoint‖ ≤ 1)
    (hsourceAngular : ∀ first ∈ source, ∀ second ∈ source,
      ‖wz1Lemma49RadialDirection viewpoint first -
          wz1Lemma49RadialDirection viewpoint second‖ ≤ aperture) :
    ∀ first ∈ source, ∀ second ∈ source,
      dist first second ≤
        2 * aperture + 8 * aperture / side +
          width + 4 * width / side := by
  have hsourceBound :
      ∀ point ∈ source, ‖point - viewpoint‖ ≤ 2 := by
    intro point hpoint
    calc
      ‖point - viewpoint‖ ≤ ‖point‖ + ‖viewpoint‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 := by
        linarith [hsourceBall point hpoint]
      _ = 2 := by norm_num
  have h :=
    cone_source_diameter_bound
      hdirection hwidth hside (by norm_num) haperture
      hsourceStrip hsourceSide hsourceBound hsourceAngular
  intro first hfirst second hsecond
  convert h first hfirst second hsecond using 1 <;> ring

/--
A separated source in one one-sided strip produces a separated Frostman set
of radial directions once the angular scale lies below the geometric
separation supplied by `strip_angular_separation_lower_bound_unitBall`.
-/
theorem strip_radial_projection_frostman
    {source : DiscreteSet 2}
    {base direction viewpoint : Point2}
    {width side sourceScale angularScale kappa : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hwidth : 0 < width)
    (hside : 0 < side)
    (hsourceScale : 0 < sourceScale)
    (hangularScale : 0 < angularScale)
    (hangularScaleHalf : angularScale ≤ 1 / 2)
    (hkappa : 0 < kappa)
    (hsourceNonempty : source.Nonempty)
    (hsourceSeparated : source.IsDeltaSeparated sourceScale)
    (hsourceStrip : ∀ point ∈ source,
      |inner ℝ (point - base) (wz1Perp2 direction)| ≤ width / 2)
    (hsourceSide : ∀ point ∈ source,
      side / 2 ≤
        inner ℝ (point - viewpoint) (wz1Perp2 direction))
    (hsourceBall : source.IsInUnitBall)
    (hviewpointBall : ‖viewpoint‖ ≤ 1)
    (hthreshold :
      width + 4 * width / side < sourceScale)
    (hangularBound :
      angularScale ≤
        (sourceScale - width - 4 * width / side) /
          (2 + 8 / side))
    (hcardinality :
      kappa / angularScale ≤ (source.card : ℝ)) :
    Nonempty
      (WZ1Lemma49RadialProjectionData
        source viewpoint angularScale
        (2 + (4 / Real.sqrt 3 + 1) / kappa)) := by
  classical
  let radial := wz1Lemma49RadialDirection viewpoint
  let directions : DiscreteSet 2 := source.image radial
  have hpointNe :
      ∀ point ∈ source, point - viewpoint ≠ 0 := by
    intro point hpoint heq
    have hpositive := hsourceSide point hpoint
    rw [heq] at hpositive
    simp at hpositive
    linarith
  have hunitSource :
      ∀ point ∈ source, ‖radial point‖ = 1 := by
    intro point hpoint
    have hnorm : 0 < ‖point - viewpoint‖ :=
      norm_pos_iff.mpr (hpointNe point hpoint)
    simp only [radial, wz1Lemma49RadialDirection, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    field_simp [hnorm.ne']
  have hradialSeparation :
      ∀ first ∈ source, ∀ second ∈ source, first ≠ second →
        angularScale ≤ dist (radial first) (radial second) := by
    intro first hfirst second hsecond hne
    have hfirstBall : ‖first‖ ≤ 1 := by
      simpa [dist_zero_right] using hsourceBall first hfirst
    have hsecondBall : ‖second‖ ≤ 1 := by
      simpa [dist_zero_right] using hsourceBall second hsecond
    have hsourceSep :
        sourceScale ≤ dist first second :=
      hsourceSeparated hfirst hsecond hne
    have hgeometry :=
      strip_angular_separation_lower_bound_unitBall
        hdirection hwidth hside
        (hsourceStrip first hfirst)
        (hsourceStrip second hsecond)
        (hsourceSide first hfirst)
        (hsourceSide second hsecond)
        hfirstBall hsecondBall hviewpointBall
        hsourceSep hthreshold
    calc
      angularScale
          ≤ (sourceScale - width - 4 * width / side) /
              (2 + 8 / side) := hangularBound
      _ ≤
          ‖radial first - radial second‖ := hgeometry
      _ = dist (radial first) (radial second) := by
        rw [dist_eq_norm]
  have hinjective : Set.InjOn radial (source : Set Point2) := by
    intro first hfirst second hsecond heq
    by_contra hne
    have hsep :=
      hradialSeparation first hfirst second hsecond hne
    rw [heq, dist_self] at hsep
    linarith
  have hcard : directions.card = source.card :=
    Finset.card_image_of_injOn hinjective
  have hdirectionsNonempty : directions.Nonempty := by
    rcases hsourceNonempty with ⟨point, hpoint⟩
    exact
      ⟨radial point,
        Finset.mem_image.mpr ⟨point, hpoint, rfl⟩⟩
  have hunit :
      ∀ value ∈ directions, ‖value‖ = 1 := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨point, hpoint, rfl⟩
    exact hunitSource point hpoint
  have hseparated :
      directions.IsDeltaSeparated angularScale := by
    intro firstValue hfirstValue secondValue hsecondValue hne
    rcases Finset.mem_image.mp hfirstValue with
      ⟨first, hfirst, rfl⟩
    rcases Finset.mem_image.mp hsecondValue with
      ⟨second, hsecond, rfl⟩
    have hneSource : first ≠ second := by
      intro heq
      subst second
      exact hne rfl
    exact
      hradialSeparation first hfirst second hsecond hneSource
  have hdirectionCardinality :
      kappa / angularScale ≤ (directions.card : ℝ) := by
    rw [hcard]
    exact hcardinality
  have hfrostman :
      directions.IsFrostman angularScale 1
        (ENNReal.ofReal
          (2 + (4 / Real.sqrt 3 + 1) / kappa)) :=
    wz1_lemma49_unit_circle_frostman
      hangularScale hangularScaleHalf hkappa
      hunit hseparated hdirectionCardinality
  exact
    ⟨{ directions := directions
       directions_nonempty := hdirectionsNonempty
       unit := hunit
       separated := hseparated
       frostman := hfrostman
       source_image := rfl }⟩

end

end Kakeya.Assouad
