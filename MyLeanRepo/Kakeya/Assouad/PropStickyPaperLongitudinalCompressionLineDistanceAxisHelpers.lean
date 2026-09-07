import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLongitudinalCompressionEnvelopeHelpers

/-!
# Axis geometry for longitudinal-compression line distance
-/

noncomputable section

namespace Kakeya.Assouad

/--
If two tube axis lines are equal as sets, their direction vectors are nonzero
scalar multiples of one another.
-/
lemma axisLine_eq_iff_direction_parallel
    {δ1 δ2 : ℝ} {T1 : Kakeya.DeltaTube δ1} {T2 : Kakeya.DeltaTube δ2}
    (h : tubeAxisLine T1 = tubeAxisLine T2) :
    ∃ c : ℝ, c ≠ 0 ∧ T2.direction = c • T1.direction := by
  have h1 : T1.base ∈ tubeAxisLine T1 :=
    ⟨0, by simp⟩
  have h1' : T1.base ∈ tubeAxisLine T2 := by
    rw [h] at h1
    exact h1
  rcases h1' with ⟨s1, hs1⟩
  have h2 : T1.base + T1.direction ∈ tubeAxisLine T1 :=
    ⟨1, by simp⟩
  have h2' : T1.base + T1.direction ∈ tubeAxisLine T2 := by
    rw [h] at h2
    exact h2
  rcases h2' with ⟨s2, hs2⟩
  have hdir : T1.direction = (s2 - s1) • T2.direction := by
    calc
      T1.direction =
          (T1.base + T1.direction) - T1.base := by abel
      _ =
          (T2.base + s2 • T2.direction) -
            (T2.base + s1 • T2.direction) := by
        rw [hs2, hs1]
      _ = (s2 - s1) • T2.direction := by module
  have hne : s2 - s1 ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hdir
    have hunit : ‖T1.direction‖ = 1 := T1.direction_unit
    rw [hdir] at hunit
    simp at hunit
  refine ⟨(s2 - s1)⁻¹, inv_ne_zero hne, ?_⟩
  have hinverse :
      (s2 - s1)⁻¹ • T1.direction = T2.direction := by
    rw [hdir, smul_smul, inv_mul_cancel₀ hne]
    exact one_smul ℝ T2.direction
  exact hinverse.symm

/--
Longitudinal compression `(x,y,z) ↦ (x,y,z/100)` fixes every point with
`z = 0`.
-/
lemma wz2PaperLongitudinalCompression_fixes_z_zero
    {point : Point3} (hpoint : point (2 : Fin 3) = 0) :
    wz2PaperLongitudinalCompression point = point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [wz2PaperLongitudinalCompression, hpoint]

/--
The zero point is preserved when the literal axis is the compressed image of
the historical axis.
-/
lemma longitudinalCompression_zeroPoint_eq
    {δ1 δ2 : ℝ}
    {historicalTube : Kakeya.DeltaTube δ1}
    {literalTube : Kakeya.DeltaTube δ2}
    (hhistorical : WZ1PaperTubeInLineClass historicalTube)
    (hliteral : WZ1PaperTubeInLineClass literalTube)
    (haxis :
      tubeAxisLine literalTube =
        wz2PaperLongitudinalCompression ''
          tubeAxisLine historicalTube) :
    wz1TubeAxisZeroPoint literalTube =
      wz1TubeAxisZeroPoint historicalTube := by
  let zeroPoint := wz1TubeAxisZeroPoint historicalTube
  have hzero_mem : zeroPoint ∈ tubeAxisLine historicalTube :=
    wz1TubeAxisZeroPoint_mem_axis historicalTube
  have hzero_two : zeroPoint (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two historicalTube
      hhistorical.vertical
  have hfix :
      wz2PaperLongitudinalCompression zeroPoint = zeroPoint :=
    wz2PaperLongitudinalCompression_fixes_z_zero hzero_two
  have hliteral_mem : zeroPoint ∈ tubeAxisLine literalTube := by
    rw [haxis]
    exact ⟨zeroPoint, hzero_mem, hfix⟩
  exact
    wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      hliteral.vertical hliteral_mem hzero_two

/--
The paper direction of the literal tube is the normalized compressed paper
direction of the historical tube.
-/
lemma longitudinalCompression_direction_eq
    {δ1 δ2 : ℝ}
    {historicalTube : Kakeya.DeltaTube δ1}
    {literalTube : Kakeya.DeltaTube δ2}
    (hhistorical : WZ1PaperTubeInLineClass historicalTube)
    (hliteral : WZ1PaperTubeInLineClass literalTube)
    (haxis :
      tubeAxisLine literalTube =
        wz2PaperLongitudinalCompression ''
          tubeAxisLine historicalTube) :
    wz1PaperDirection literalTube =
      NormedSpace.normalize
        (wz2PaperLongitudinalCompression
          (wz1PaperDirection historicalTube)) := by
  set historicalDirection :=
    wz1PaperDirection historicalTube with hHistoricalDirection
  set literalDirection :=
    wz1PaperDirection literalTube with hLiteralDirection
  set rawHistorical := historicalTube.direction with hRawHistorical
  set rawLiteral := literalTube.direction with hRawLiteral
  have hmap_add :
      ∀ first second : Point3,
        wz2PaperLongitudinalCompression (first + second) =
          wz2PaperLongitudinalCompression first +
            wz2PaperLongitudinalCompression second := by
    intro first second
    ext coordinate
    fin_cases coordinate <;>
      simp [wz2PaperLongitudinalCompression, PiLp.add_apply] <;>
      ring
  have hmap_neg :
      ∀ point : Point3,
        wz2PaperLongitudinalCompression (-point) =
          -wz2PaperLongitudinalCompression point := by
    intro point
    ext coordinate
    fin_cases coordinate <;>
      simp [wz2PaperLongitudinalCompression] <;>
      ring
  have hbase_mem :
      wz2PaperLongitudinalCompression historicalTube.base ∈
        tubeAxisLine literalTube := by
    rw [haxis]
    exact ⟨historicalTube.base, ⟨0, by simp⟩, rfl⟩
  rcases hbase_mem with ⟨firstParameter, hfirstParameter⟩
  have hdirection_point_mem :
      wz2PaperLongitudinalCompression
          (historicalTube.base + historicalTube.direction) ∈
        tubeAxisLine literalTube := by
    rw [haxis]
    have hsource :
        historicalTube.base + historicalTube.direction ∈
          tubeAxisLine historicalTube :=
      ⟨1, by simp⟩
    exact
      ⟨historicalTube.base + historicalTube.direction,
        hsource, rfl⟩
  rcases hdirection_point_mem with
    ⟨secondParameter, hsecondParameter⟩
  let scalar := secondParameter - firstParameter
  have hadd :
      wz2PaperLongitudinalCompression
          (historicalTube.base + historicalTube.direction) =
        wz2PaperLongitudinalCompression historicalTube.base +
          wz2PaperLongitudinalCompression historicalTube.direction :=
    hmap_add _ _
  have hsum :
      wz2PaperLongitudinalCompression historicalTube.base +
          wz2PaperLongitudinalCompression historicalTube.direction =
        literalTube.base + secondParameter • rawLiteral := by
    rw [← hadd]
    exact hsecondParameter
  have hmap_direction :
      wz2PaperLongitudinalCompression rawHistorical =
        scalar • rawLiteral := by
    simp only [hRawHistorical, hRawLiteral]
    calc
      wz2PaperLongitudinalCompression historicalTube.direction =
          (wz2PaperLongitudinalCompression historicalTube.base +
              wz2PaperLongitudinalCompression
                historicalTube.direction) -
            wz2PaperLongitudinalCompression historicalTube.base := by
        abel
      _ =
          (literalTube.base +
              secondParameter • literalTube.direction) -
            (literalTube.base +
              firstParameter • literalTube.direction) := by
        rw [hsum, hfirstParameter]
      _ = scalar • literalTube.direction := by module
  have hscalar_ne : scalar ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hmap_direction
    have hmap_zero :
        wz2PaperLongitudinalCompression rawHistorical = 0 :=
      hmap_direction
    have hraw_zero : rawHistorical = 0 := by
      ext coordinate
      fin_cases coordinate
      · have hcoordinate :
            (wz2PaperLongitudinalCompression rawHistorical) 0 =
              0 := by
          rw [hmap_zero]
          simp
        simpa [wz2PaperLongitudinalCompression] using hcoordinate
      · have hcoordinate :
            (wz2PaperLongitudinalCompression rawHistorical) 1 =
              0 := by
          rw [hmap_zero]
          simp
        simpa [wz2PaperLongitudinalCompression] using hcoordinate
      · have hcoordinate :
            (wz2PaperLongitudinalCompression rawHistorical) 2 =
              0 := by
          rw [hmap_zero]
          simp
        have hdiv : rawHistorical 2 / 100 = 0 := by
          simpa [wz2PaperLongitudinalCompression] using hcoordinate
        have hraw_two : rawHistorical 2 = 0 := by linarith
        exact hraw_two
    have hunit : ‖rawHistorical‖ = 1 :=
      historicalTube.direction_unit
    rw [hraw_zero] at hunit
    simp at hunit
  have hHistorical_two :
      0 < historicalDirection 2 := by
    linarith [hhistorical.1]
  have hmap_two :
      0 <
        (wz2PaperLongitudinalCompression
          historicalDirection) 2 := by
    simp [wz2PaperLongitudinalCompression, hHistorical_two] <;>
      positivity
  have hHistorical_cases :
      historicalDirection = rawHistorical ∨
        historicalDirection = -rawHistorical := by
    have h :
        historicalDirection =
          wz1PaperDirection historicalTube :=
      hHistoricalDirection
    rw [h]
    unfold wz1PaperDirection
    split_ifs <;>
      simp [hRawHistorical] <;>
      tauto
  have hmain :
      ∀ (coefficient : ℝ), coefficient ≠ 0 →
        wz2PaperLongitudinalCompression historicalDirection =
            coefficient • rawLiteral →
          literalDirection =
            NormedSpace.normalize
              (wz2PaperLongitudinalCompression
                historicalDirection) := by
    intro coefficient hcoefficient_ne hcoefficient
    have hsign : coefficient * rawLiteral 2 > 0 := by
      have h :
          (wz2PaperLongitudinalCompression
            historicalDirection) 2 =
              coefficient * rawLiteral 2 := by
        rw [hcoefficient]
        simp
      rw [h] at hmap_two
      exact hmap_two
    by_cases hLiteral_nonneg : 0 ≤ rawLiteral 2
    · have hLiteral_pos : 0 < rawLiteral 2 := by
        by_contra h
        have hzero : rawLiteral 2 = 0 := by linarith
        rw [hzero] at hsign
        linarith
      have hcoefficient_pos : 0 < coefficient := by
        nlinarith
      have hrawLiteral_nonneg :
          0 ≤ literalTube.direction 2 := by
        simpa [hRawLiteral] using hLiteral_nonneg
      have hLiteralDirection_eq :
          literalDirection = rawLiteral := by
        have h :
            literalDirection =
              wz1PaperDirection literalTube :=
          hLiteralDirection
        rw [h]
        unfold wz1PaperDirection
        rw [if_pos hrawLiteral_nonneg]
        <;> simp [hRawLiteral]
      have hnormalize :
          NormedSpace.normalize
              (coefficient • rawLiteral) =
            rawLiteral := by
        rw [NormedSpace.normalize_smul_of_pos hcoefficient_pos]
        rw [NormedSpace.normalize_eq_self_of_norm_eq_one
          literalTube.direction_unit]
      have hfinal :
          rawLiteral =
            NormedSpace.normalize
              (wz2PaperLongitudinalCompression
                historicalDirection) := by
        have h :
            NormedSpace.normalize
                (wz2PaperLongitudinalCompression
                  historicalDirection) =
              rawLiteral := by
          rw [hcoefficient]
          exact hnormalize
        exact h.symm
      rw [hLiteralDirection_eq]
      exact hfinal
    · have hLiteral_neg : rawLiteral 2 < 0 := by
        linarith
      have hcoefficient_neg : coefficient < 0 := by
        nlinarith
      have hrawLiteral_neg :
          ¬0 ≤ literalTube.direction 2 := by
        simpa [hRawLiteral] using hLiteral_nonneg
      have hLiteralDirection_eq :
          literalDirection = -rawLiteral := by
        have h :
            literalDirection =
              wz1PaperDirection literalTube :=
          hLiteralDirection
        rw [h]
        unfold wz1PaperDirection
        rw [if_neg hrawLiteral_neg]
        <;> simp [hRawLiteral]
      rw [hLiteralDirection_eq]
      have hpositive : 0 < -coefficient := by linarith
      have hrewrite :
          coefficient • rawLiteral =
            (-coefficient) • (-rawLiteral) := by
        simp [smul_neg] <;> ring
      have hnormalize :
          NormedSpace.normalize (-rawLiteral) = -rawLiteral := by
        rw [NormedSpace.normalize_eq_self_of_norm_eq_one]
        simpa using literalTube.direction_unit
      have hfinal :
          -rawLiteral =
            NormedSpace.normalize
              (wz2PaperLongitudinalCompression
                historicalDirection) := by
        have h :
            NormedSpace.normalize
                (wz2PaperLongitudinalCompression
                  historicalDirection) =
              -rawLiteral := by
          rw [hcoefficient, hrewrite]
          rw [NormedSpace.normalize_smul_of_pos hpositive]
          exact hnormalize
        exact h.symm
      exact hfinal
  rcases hHistorical_cases with
    hHistorical_eq | hHistorical_eq
  · exact
      hmain scalar hscalar_ne
        (by
          rw [hHistorical_eq]
          exact hmap_direction)
  · have hmap :
        wz2PaperLongitudinalCompression historicalDirection =
          (-scalar) • rawLiteral := by
      rw [hHistorical_eq]
      have h :
          wz2PaperLongitudinalCompression (-rawHistorical) =
            -wz2PaperLongitudinalCompression rawHistorical :=
        hmap_neg rawHistorical
      rw [h, hmap_direction]
      simp
    have hnegative_ne : -scalar ≠ 0 := by
      simpa using hscalar_ne
    exact hmain (-scalar) hnegative_ne hmap

/--
If the literal tube is in the paper line class, the historical projective
transverse slope is bounded by `3 / 10000`.
-/
lemma longitudinalCompression_transverseBound
    {δ1 δ2 : ℝ}
    {historicalTube : Kakeya.DeltaTube δ1}
    {literalTube : Kakeya.DeltaTube δ2}
    (hhistorical : WZ1PaperTubeInLineClass historicalTube)
    (hliteral : WZ1PaperTubeInLineClass literalTube)
    (hdirection_eq :
      wz1PaperDirection literalTube =
        NormedSpace.normalize
          (wz2PaperLongitudinalCompression
            (wz1PaperDirection historicalTube))) :
    ‖transversePart
        (wz1PaperProjectiveDirection
          (wz1PaperDirection historicalTube))‖ ^ 2 ≤
      3 / 10000 := by
  let compression := wz2PaperLongitudinalCompression
  let historicalDirection := wz1PaperDirection historicalTube
  let literalDirection := wz1PaperDirection literalTube
  have hHistorical_norm : ‖historicalDirection‖ = 1 :=
    wz1PaperDirection_norm historicalTube
  have hHistorical_two : 0 < historicalDirection 2 := by
    linarith [hhistorical.1]
  have hHistorical_two_ne : historicalDirection 2 ≠ 0 :=
    hHistorical_two.ne'
  have hLiteral_two : 1 / 2 ≤ literalDirection 2 :=
    hliteral.1
  have hcompression_norm :
      ‖compression historicalDirection‖ ^ 2 =
        1 -
          (9999 / 10000 : ℝ) *
            (historicalDirection 2) ^ 2 := by
    have hcoord_zero :
        (compression historicalDirection) 0 =
          historicalDirection 0 := by
      simp [compression, wz2PaperLongitudinalCompression]
    have hcoord_one :
        (compression historicalDirection) 1 =
          historicalDirection 1 := by
      simp [compression, wz2PaperLongitudinalCompression]
    have hcoord_two :
        (compression historicalDirection) 2 =
          historicalDirection 2 / 100 := by
      have h :
          (compression historicalDirection) 2 =
            (1 / 100 : ℝ) * historicalDirection 2 := by
        simp [compression, wz2PaperLongitudinalCompression]
      rw [h]
      ring
    have hcompression_coordinates :
        ‖compression historicalDirection‖ ^ 2 =
          ((compression historicalDirection) 0) ^ 2 +
            ((compression historicalDirection) 1) ^ 2 +
              ((compression historicalDirection) 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ]
      ring
    have hHistorical_coordinates :
        ‖historicalDirection‖ ^ 2 =
          (historicalDirection 0) ^ 2 +
            (historicalDirection 1) ^ 2 +
              (historicalDirection 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ]
      ring
    have hHistorical_norm_sq :
        ‖historicalDirection‖ ^ 2 = 1 := by
      rw [hHistorical_norm]
      norm_num
    have htransverse_coordinates :
        (historicalDirection 0) ^ 2 +
            (historicalDirection 1) ^ 2 =
          1 - (historicalDirection 2) ^ 2 := by
      linarith
    rw [hcompression_coordinates, hcoord_zero, hcoord_one, hcoord_two]
    linarith
  have hcompression_two :
      (compression historicalDirection) 2 =
        historicalDirection 2 / 100 := by
    simp [compression, wz2PaperLongitudinalCompression]
    ring
  have hcompression_norm_pos :
      0 < ‖compression historicalDirection‖ := by
    have hne : compression historicalDirection ≠ 0 := by
      intro hzero
      have hcoordinate :
          (compression historicalDirection) 2 = 0 := by
        rw [hzero]
        simp
      rw [hcompression_two] at hcoordinate
      linarith
    exact norm_pos_iff.mpr hne
  have hnormalize_eq :
      NormedSpace.normalize (compression historicalDirection) =
        (‖compression historicalDirection‖)⁻¹ •
          compression historicalDirection := by
    have hnorm :
        ‖compression historicalDirection‖ •
            NormedSpace.normalize (compression historicalDirection) =
          compression historicalDirection :=
      NormedSpace.norm_smul_normalize
        (compression historicalDirection)
    have hscaled :
        (‖compression historicalDirection‖)⁻¹ •
            (‖compression historicalDirection‖ •
              NormedSpace.normalize
                (compression historicalDirection)) =
          (‖compression historicalDirection‖)⁻¹ •
            compression historicalDirection := by
      rw [hnorm]
    have hcancel :
        (‖compression historicalDirection‖)⁻¹ •
            (‖compression historicalDirection‖ •
              NormedSpace.normalize
                (compression historicalDirection)) =
          NormedSpace.normalize
            (compression historicalDirection) := by
      rw [smul_smul]
      have hcoefficient :
          (‖compression historicalDirection‖)⁻¹ *
              ‖compression historicalDirection‖ =
            1 := by
        field_simp [hcompression_norm_pos.ne'] <;> ring
      rw [hcoefficient, one_smul]
    rw [hcancel] at hscaled
    exact hscaled.symm
  have hLiteral_eq :
      literalDirection =
        (‖compression historicalDirection‖)⁻¹ •
          compression historicalDirection :=
    hdirection_eq.trans hnormalize_eq
  have hLiteral_two_eq :
      literalDirection 2 =
        (historicalDirection 2 / 100) /
          ‖compression historicalDirection‖ := by
    have h :
        literalDirection 2 =
          ((‖compression historicalDirection‖)⁻¹ •
            compression historicalDirection) 2 :=
      congrArg (fun point : Point3 => point 2) hLiteral_eq
    rw [h]
    simp [PiLp.smul_apply, smul_eq_mul, hcompression_two] <;>
      field_simp [hcompression_norm_pos.ne'] <;> ring
  have hvertical :
      (historicalDirection 2) ^ 2 ≥ 10000 / 10003 := by
    have h :
        (historicalDirection 2 / 100) /
            ‖compression historicalDirection‖ ≥
          1 / 2 := by
      rw [← hLiteral_two_eq]
      exact hLiteral_two
    have hlinear :
        historicalDirection 2 / 100 ≥
          (1 / 2 : ℝ) *
            ‖compression historicalDirection‖ := by
      calc
        historicalDirection 2 / 100 =
            ((historicalDirection 2 / 100) /
                ‖compression historicalDirection‖) *
              ‖compression historicalDirection‖ := by
          field_simp [hcompression_norm_pos.ne'] <;> ring
        _ ≥
            (1 / 2 : ℝ) *
              ‖compression historicalDirection‖ := by
          gcongr
    have hsquare :
        (historicalDirection 2 / 100) ^ 2 ≥
          ((1 / 2 : ℝ) *
            ‖compression historicalDirection‖) ^ 2 := by
      gcongr <;>
        linarith [norm_nonneg
          (compression historicalDirection)]
    nlinarith [hcompression_norm]
  have hprojective :
      wz1PaperProjectiveDirection historicalDirection =
        (historicalDirection 2)⁻¹ • historicalDirection := rfl
  have htransverse_smul :
      transversePart
          ((historicalDirection 2)⁻¹ • historicalDirection) =
        (historicalDirection 2)⁻¹ •
          transversePart historicalDirection := by
    ext coordinate
    fin_cases coordinate <;>
      simp [transversePart_coord0, transversePart_coord1,
        transversePart_coord2, PiLp.smul_apply, smul_eq_mul] <;>
      ring
  rw [hprojective, htransverse_smul]
  have hnorm_smul :
      ‖(historicalDirection 2)⁻¹ •
          transversePart historicalDirection‖ ^ 2 =
        ((historicalDirection 2)⁻¹) ^ 2 *
          ‖transversePart historicalDirection‖ ^ 2 := by
    rw [norm_smul]
    simp [Real.norm_eq_abs, abs_of_pos hHistorical_two]
    ring
  rw [hnorm_smul]
  have htransverse_norm :
      ‖transversePart historicalDirection‖ ^ 2 =
        1 - (historicalDirection 2) ^ 2 := by
    rw [transversePart_norm_sq historicalDirection,
      hHistorical_norm]
    ring
  rw [htransverse_norm]
  have hresult :
      ((historicalDirection 2)⁻¹) ^ 2 *
          (1 - (historicalDirection 2) ^ 2) ≤
        3 / 10000 := by
    have hpositive : 0 < (historicalDirection 2) ^ 2 := by
      positivity
    field_simp [hpositive.ne']
    nlinarith
  exact hresult

end Kakeya.Assouad

end
