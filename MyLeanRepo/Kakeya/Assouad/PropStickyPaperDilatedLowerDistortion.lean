import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalDilatedDirection

/-!
# Dilated lower distortion for paper unit rescaling

Adaptation of the lower-distortion machinery in
`PropStickyPaperUnitRescalingBasics.lean` from strict `WZ1PaperTubeCovers`
to `WZ2PaperDilatedTubeCovers 2`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Dilated version of `wz1PaperUnitRescaling_projective_direction_sub_norm_eq`.
-/
lemma wz1PaperUnitRescaling_dilated_projective_direction_sub_norm_eq
    {delta rho : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ2PaperDilatedTubeCovers 2 source₁ coarse)
    (hcover₂ : WZ2PaperDilatedTubeCovers 2 source₂ coarse) :
    ‖wz1PaperProjectiveDirection
          (householderToE3
            (wz1PaperDirection coarse)
            (wz1PaperDirection_norm coarse)
            (wz1PaperDirection source₁)) -
        wz1PaperProjectiveDirection
          (householderToE3
            (wz1PaperDirection coarse)
            (wz1PaperDirection_norm coarse)
            (wz1PaperDirection source₂))‖ =
      (100 * rho) *
        ‖wz1PaperProjectiveDirection
            (wz1PaperUnitRescalingLinear coarse
              (wz1PaperDirection source₁)) -
          wz1PaperProjectiveDirection
            (wz1PaperUnitRescalingLinear coarse
              (wz1PaperDirection source₂))‖ := by
  let rotation :=
    householderToE3
      (wz1PaperDirection coarse)
      (wz1PaperDirection_norm coarse)
  let sourceDirection₁ := wz1PaperDirection source₁
  let sourceDirection₂ := wz1PaperDirection source₂
  let imageDirection₁ :=
    wz1PaperUnitRescalingLinear coarse sourceDirection₁
  let imageDirection₂ :=
    wz1PaperUnitRescalingLinear coarse sourceDirection₂
  have hrotation_coord_two :
      ∀ sourceDirection : Point3,
        (rotation sourceDirection) (2 : Fin 3) =
          inner ℝ sourceDirection (wz1PaperDirection coarse) := by
    intro sourceDirection
    calc
      (rotation sourceDirection) (2 : Fin 3) =
          inner ℝ (rotation sourceDirection) e3 :=
        coord2_eq_inner_e3 _
      _ = inner ℝ sourceDirection (rotation e3) := by
        exact householderToE3_symmetric
          (wz1PaperDirection coarse)
          (wz1PaperDirection_norm coarse)
          sourceDirection e3
      _ = inner ℝ sourceDirection (wz1PaperDirection coarse) := by
        rw [householderToE3_sends_e3_to_d]
  have hsource_inner₁ :
      0 < inner ℝ sourceDirection₁ (wz1PaperDirection coarse) := by
    have h := hcover₁.inner_direction_ge_half hrho_one
    linarith
  have hsource_inner₂ :
      0 < inner ℝ sourceDirection₂ (wz1PaperDirection coarse) := by
    have h := hcover₂.inner_direction_ge_half hrho_one
    linarith
  have hrotation_vertical₁ :
      0 < (rotation sourceDirection₁) (2 : Fin 3) := by
    rw [hrotation_coord_two] <;> exact hsource_inner₁
  have hrotation_vertical₂ :
      0 < (rotation sourceDirection₂) (2 : Fin 3) := by
    rw [hrotation_coord_two] <;> exact hsource_inner₂
  have hprojective₁ :
      wz1PaperProjectiveDirection (rotation sourceDirection₁) =
        e3 + (100 * rho) •
          transversePart
            (wz1PaperProjectiveDirection imageDirection₁) := by
    have h :=
      wz1PaperProjectiveDirection_transverseScaleLin
        (scale := 100 * rho) (by positivity)
        hrotation_vertical₁
    simpa [imageDirection₁, sourceDirection₁, rotation,
      wz1PaperUnitRescalingLinear, unitRescalingLinear] using h
  have hprojective₂ :
      wz1PaperProjectiveDirection (rotation sourceDirection₂) =
        e3 + (100 * rho) •
          transversePart
            (wz1PaperProjectiveDirection imageDirection₂) := by
    have h :=
      wz1PaperProjectiveDirection_transverseScaleLin
        (scale := 100 * rho) (by positivity)
        hrotation_vertical₂
    simpa [imageDirection₂, sourceDirection₂, rotation,
      wz1PaperUnitRescalingLinear, unitRescalingLinear] using h
  rw [hprojective₁, hprojective₂]
  have hcoord₂₁ :
      wz1PaperProjectiveDirection imageDirection₁ (2 : Fin 3) = 1 := by
    apply wz1PaperProjectiveDirection_coord_two
    rw [wz1PaperUnitRescalingLinear_coord2]
    exact hsource_inner₁.ne'
  have hcoord₂₂ :
      wz1PaperProjectiveDirection imageDirection₂ (2 : Fin 3) = 1 := by
    apply wz1PaperProjectiveDirection_coord_two
    rw [wz1PaperUnitRescalingLinear_coord2]
    exact hsource_inner₂.ne'
  have hdiff :
      (e3 + (100 * rho) •
            transversePart
              (wz1PaperProjectiveDirection imageDirection₁)) -
          (e3 + (100 * rho) •
            transversePart
              (wz1PaperProjectiveDirection imageDirection₂)) =
        (100 * rho) •
          (wz1PaperProjectiveDirection imageDirection₁ -
            wz1PaperProjectiveDirection imageDirection₂) := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [transversePart_coord0, transversePart_coord1,
        transversePart_coord2, hcoord₂₁, hcoord₂₂,
        PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul] <;> ring
  rw [hdiff, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 100 * rho)]

/--
Dilated version of `wz1PaperUnitRescaling_source_angle_le`.
-/
lemma wz1PaperUnitRescaling_dilated_source_angle_le
    {delta rho : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ2PaperDilatedTubeCovers 2 source₁ coarse)
    (hcover₂ : WZ2PaperDilatedTubeCovers 2 source₂ coarse) :
    InnerProductGeometry.angle
        (wz1PaperDirection source₁)
        (wz1PaperDirection source₂) ≤
      1050 * rho *
        InnerProductGeometry.angle
          (wz1PaperUnitRescalingLinear coarse
            (wz1PaperDirection source₁))
          (wz1PaperUnitRescalingLinear coarse
            (wz1PaperDirection source₂)) := by
  let rotation :=
    householderToE3
      (wz1PaperDirection coarse)
      (wz1PaperDirection_norm coarse)
  let sourceDirection₁ := wz1PaperDirection source₁
  let sourceDirection₂ := wz1PaperDirection source₂
  let imageDirection₁ :=
    wz1PaperUnitRescalingLinear coarse sourceDirection₁
  let imageDirection₂ :=
    wz1PaperUnitRescalingLinear coarse sourceDirection₂
  have hrotation_unit₁ : ‖rotation sourceDirection₁‖ = 1 := by
    rw [rotation.norm_map] <;> exact wz1PaperDirection_norm source₁
  have hrotation_unit₂ : ‖rotation sourceDirection₂‖ = 1 := by
    rw [rotation.norm_map] <;> exact wz1PaperDirection_norm source₂
  have hrotation_vertical₁ :
      1 / 2 ≤ (rotation sourceDirection₁) (2 : Fin 3) := by
    calc
      (1 / 2 : ℝ) ≤ inner ℝ sourceDirection₁ (wz1PaperDirection coarse) := by
        have h := hcover₁.inner_direction_ge_half hrho_one
        linarith
      _ = (rotation sourceDirection₁) (2 : Fin 3) := by
        calc
          inner ℝ sourceDirection₁ (wz1PaperDirection coarse) =
              inner ℝ sourceDirection₁ (rotation e3) := by
            rw [householderToE3_sends_e3_to_d]
          _ = inner ℝ (rotation sourceDirection₁) e3 := by
            symm
            exact householderToE3_symmetric
              (wz1PaperDirection coarse)
              (wz1PaperDirection_norm coarse)
              sourceDirection₁ e3
          _ = (rotation sourceDirection₁) (2 : Fin 3) := by
            rw [coord2_eq_inner_e3]
  have hrotation_vertical₂ :
      1 / 2 ≤ (rotation sourceDirection₂) (2 : Fin 3) := by
    calc
      (1 / 2 : ℝ) ≤ inner ℝ sourceDirection₂ (wz1PaperDirection coarse) := by
        have h := hcover₂.inner_direction_ge_half hrho_one
        linarith
      _ = (rotation sourceDirection₂) (2 : Fin 3) := by
        calc
          inner ℝ sourceDirection₂ (wz1PaperDirection coarse) =
              inner ℝ sourceDirection₂ (rotation e3) := by
            rw [householderToE3_sends_e3_to_d]
          _ = inner ℝ (rotation sourceDirection₂) e3 := by
            symm
            exact householderToE3_symmetric
              (wz1PaperDirection coarse)
              (wz1PaperDirection_norm coarse)
              sourceDirection₂ e3
          _ = (rotation sourceDirection₂) (2 : Fin 3) := by
            rw [coord2_eq_inner_e3]
  have himage_ne₁ : imageDirection₁ ≠ 0 :=
    rescaled_direction_ne_zero hrho
  have himage_ne₂ : imageDirection₂ ≠ 0 :=
    rescaled_direction_ne_zero hrho
  have hnormalized₁ :
      1 / 2 ≤ (NormedSpace.normalize imageDirection₁) (2 : Fin 3) :=
    wz1PaperDilatedUnitRescaling_normalized_direction_vertical
      hrho hrho_one hcover₁
  have hnormalized₂ :
      1 / 2 ≤ (NormedSpace.normalize imageDirection₂) (2 : Fin 3) :=
    wz1PaperDilatedUnitRescaling_normalized_direction_vertical
      hrho hrho_one hcover₂
  have hprojective :=
    wz1PaperUnitRescaling_dilated_projective_direction_sub_norm_eq
      hrho hrho_one hcover₁ hcover₂
  have himage_projective :
      ‖wz1PaperProjectiveDirection imageDirection₁ -
          wz1PaperProjectiveDirection imageDirection₂‖ ≤
        (21 / 4 : ℝ) *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖ := by
    have h :=
      wz1PaperProjectiveDirection_sub_norm_le
        (NormedSpace.norm_normalize himage_ne₁)
        (NormedSpace.norm_normalize himage_ne₂)
        hnormalized₁ hnormalized₂
    simpa only [
      wz1PaperProjectiveDirection_normalize himage_ne₁,
      wz1PaperProjectiveDirection_normalize himage_ne₂] using h
  have hrotation_chord :
      ‖rotation sourceDirection₁ - rotation sourceDirection₂‖ =
        ‖sourceDirection₁ - sourceDirection₂‖ := by
    rw [← map_sub] <;> exact rotation.norm_map _
  have hsource_from_projective :
      ‖rotation sourceDirection₁ - rotation sourceDirection₂‖ ≤
        ‖wz1PaperProjectiveDirection (rotation sourceDirection₁) -
          wz1PaperProjectiveDirection (rotation sourceDirection₂)‖ := by
    have hnormalize₁ :=
      normalize_wz1PaperProjectiveDirection
        hrotation_unit₁ (by linarith : 0 < (rotation sourceDirection₁) (2 : Fin 3))
    have hnormalize₂ :=
      normalize_wz1PaperProjectiveDirection
        hrotation_unit₂ (by linarith : 0 < (rotation sourceDirection₂) (2 : Fin 3))
    have h :=
      norm_normalize_sub_normalize_le_norm_sub
        (first := wz1PaperProjectiveDirection (rotation sourceDirection₁))
        (second := wz1PaperProjectiveDirection (rotation sourceDirection₂))
        (one_le_norm_wz1PaperProjectiveDirection
          (by linarith : (rotation sourceDirection₁) (2 : Fin 3) ≠ 0))
        (one_le_norm_wz1PaperProjectiveDirection
          (by linarith : (rotation sourceDirection₂) (2 : Fin 3) ≠ 0))
    rw [hnormalize₁, hnormalize₂] at h
    exact h
  have hsource_chord :
      ‖sourceDirection₁ - sourceDirection₂‖ ≤
        525 * rho *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖ := by
    rw [← hrotation_chord]
    calc
      ‖rotation sourceDirection₁ - rotation sourceDirection₂‖
        ≤ ‖wz1PaperProjectiveDirection (rotation sourceDirection₁) -
              wz1PaperProjectiveDirection (rotation sourceDirection₂)‖ :=
          hsource_from_projective
      _ = 100 * rho *
            ‖wz1PaperProjectiveDirection imageDirection₁ -
              wz1PaperProjectiveDirection imageDirection₂‖ := by
          rw [hprojective]
      _ ≤ 100 * rho * ((21 / 4 : ℝ) *
            ‖NormedSpace.normalize imageDirection₁ -
              NormedSpace.normalize imageDirection₂‖) := by
          gcongr
      _ = 525 * rho *
            ‖NormedSpace.normalize imageDirection₁ -
              NormedSpace.normalize imageDirection₂‖ := by ring
  have hsource_angle :=
    angle_le_pi_div_two_mul_unit_norm_sub
      (wz1PaperDirection_norm source₁)
      (wz1PaperDirection_norm source₂)
  have himage_chord_angle :=
    unit_norm_sub_le_angle
      (NormedSpace.norm_normalize himage_ne₁)
      (NormedSpace.norm_normalize himage_ne₂)
  have hpi : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]
  have himage_angle :
      InnerProductGeometry.angle imageDirection₁ imageDirection₂ =
        InnerProductGeometry.angle
          (NormedSpace.normalize imageDirection₁)
          (NormedSpace.normalize imageDirection₂) := by
    simp
  change
    InnerProductGeometry.angle sourceDirection₁ sourceDirection₂ ≤
      1050 * rho *
        InnerProductGeometry.angle imageDirection₁ imageDirection₂
  rw [himage_angle]
  calc
    InnerProductGeometry.angle sourceDirection₁ sourceDirection₂
      ≤ (Real.pi / 2) * ‖sourceDirection₁ - sourceDirection₂‖ :=
        hsource_angle
    _ ≤ 2 * (525 * rho *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖) := by
        have hfactor_nonneg :
            0 ≤ 525 * rho *
              ‖NormedSpace.normalize imageDirection₁ -
                NormedSpace.normalize imageDirection₂‖ := by positivity
        calc
          (Real.pi / 2) * ‖sourceDirection₁ - sourceDirection₂‖
            ≤ (Real.pi / 2) * (525 * rho *
                  ‖NormedSpace.normalize imageDirection₁ -
                    NormedSpace.normalize imageDirection₂‖) := by
              gcongr
          _ ≤ 2 * (525 * rho *
                ‖NormedSpace.normalize imageDirection₁ -
                  NormedSpace.normalize imageDirection₂‖) := by
              gcongr
    _ = 1050 * rho *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖ := by ring
    _ ≤ 1050 * rho *
          InnerProductGeometry.angle
            (NormedSpace.normalize imageDirection₁)
            (NormedSpace.normalize imageDirection₂) := by
        gcongr

/--
Dilated version of `wz1PaperUnitRescalingLinear_paperDirection_eq_pos_smul`.
-/
lemma wz1PaperUnitRescalingLinear_dilated_paperDirection_eq_pos_smul
    {delta rho targetDelta : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source coarse)
    (htarget : WZ1PaperTubeInLineClass target)
    (haxis :
      tubeAxisLine target =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source) :
    ∃ scale : ℝ, 0 < scale ∧
      wz1PaperUnitRescalingLinear coarse
          (wz1PaperDirection source) =
        scale • wz1PaperDirection target := by
  let sourceZero := wz1TubeAxisZeroPoint source
  let sourceDirection := wz1PaperDirection source
  have hsourceZero : sourceZero ∈ tubeAxisLine source :=
    wz1TubeAxisZeroPoint_mem_axis source
  have hsourceOne :
      sourceZero + sourceDirection ∈ tubeAxisLine source :=
    wz1TubeAxisZeroPoint_add_paperDirection_mem_axis source
  have htargetZero :
      wz1PaperUnitRescalingMap coarse hrho sourceZero ∈
        tubeAxisLine target := by
    rw [haxis] <;> exact ⟨sourceZero, hsourceZero, rfl⟩
  have htargetOne :
      wz1PaperUnitRescalingMap coarse hrho
          (sourceZero + sourceDirection) ∈
        tubeAxisLine target := by
    rw [haxis] <;> exact ⟨sourceZero + sourceDirection, hsourceOne, rfl⟩
  rcases htargetZero with ⟨parameterZero, hparameterZero⟩
  rcases htargetOne with ⟨parameterOne, hparameterOne⟩
  let rawScale := parameterOne - parameterZero
  have hraw :
      wz1PaperUnitRescalingLinear coarse sourceDirection =
        rawScale • target.direction := by
    have hadd :=
      wz1PaperUnitRescalingMap_add coarse hrho sourceZero sourceDirection
    have hdifference :
        wz1PaperUnitRescalingLinear coarse sourceDirection =
          wz1PaperUnitRescalingMap coarse hrho
              (sourceZero + sourceDirection) -
            wz1PaperUnitRescalingMap coarse hrho sourceZero := by
      rw [hadd] <;> abel
    rw [hdifference, hparameterOne, hparameterZero]
    simp only [rawScale] <;> module
  have hinner_pos :
      0 < inner ℝ sourceDirection (wz1PaperDirection coarse) := by
    have h := hcover.inner_direction_ge_half hrho_one
    linarith
  have hlinear_coord_pos :
      0 < (wz1PaperUnitRescalingLinear coarse sourceDirection) (2 : Fin 3) := by
    rw [wz1PaperUnitRescalingLinear_coord2] <;> exact hinner_pos
  by_cases htargetSign : 0 ≤ target.direction (2 : Fin 3)
  · refine ⟨rawScale, ?_, ?_⟩
    · have hcoord :=
        congrArg (fun point : Point3 => point (2 : Fin 3)) hraw
      simp only [PiLp.smul_apply, smul_eq_mul] at hcoord
      have htargetCoord : (1 / 2 : ℝ) ≤ target.direction (2 : Fin 3) := by
        simpa [wz1PaperDirection, htargetSign] using htarget.1
      nlinarith
    · simpa [sourceDirection, wz1PaperDirection, htargetSign] using hraw
  · have htargetNeg : target.direction (2 : Fin 3) < 0 := by
      linarith
    refine ⟨-rawScale, ?_, ?_⟩
    · have hcoord :=
        congrArg (fun point : Point3 => point (2 : Fin 3)) hraw
      simp only [PiLp.smul_apply, smul_eq_mul] at hcoord
      nlinarith
    · rw [hraw]
      simp [sourceDirection, wz1PaperDirection, htargetSign]

/--
Dilated version: target paper direction is normalized linear image.
-/
lemma wz1PaperUnitRescaledDilatedTargetDirection_eq_normalize
    {delta rho targetDelta : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source coarse)
    (htarget : WZ1PaperTubeInLineClass target)
    (haxis :
      tubeAxisLine target =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source) :
    wz1PaperDirection target =
      NormedSpace.normalize
        (wz1PaperUnitRescalingLinear coarse
          (wz1PaperDirection source)) := by
  rcases wz1PaperUnitRescalingLinear_dilated_paperDirection_eq_pos_smul
      hrho hrho_one hcover htarget haxis with
    ⟨scale, hscale, hrelation⟩
  rw [hrelation, NormedSpace.normalize_smul_of_pos hscale]
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one
    (wz1PaperDirection_norm target)]

/--
Dilated version of angular lower distortion for two target tubes.
-/
lemma wz1PaperUnitRescaling_dilated_source_angle_le_target_angle
    {delta rho targetDelta : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target₁ target₂ : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ2PaperDilatedTubeCovers 2 source₁ coarse)
    (hcover₂ : WZ2PaperDilatedTubeCovers 2 source₂ coarse)
    (htarget₁ : WZ1PaperTubeInLineClass target₁)
    (htarget₂ : WZ1PaperTubeInLineClass target₂)
    (haxis₁ :
      tubeAxisLine target₁ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₁)
    (haxis₂ :
      tubeAxisLine target₂ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₂) :
    InnerProductGeometry.angle
        (wz1PaperDirection source₁)
        (wz1PaperDirection source₂) ≤
      1050 * rho *
        InnerProductGeometry.angle
          (wz1PaperDirection target₁)
          (wz1PaperDirection target₂) := by
  have hsource :=
    wz1PaperUnitRescaling_dilated_source_angle_le
      hrho hrho_one hcover₁ hcover₂
  rw [
    wz1PaperUnitRescaledDilatedTargetDirection_eq_normalize
      hrho hrho_one hcover₁ htarget₁ haxis₁,
    wz1PaperUnitRescaledDilatedTargetDirection_eq_normalize
      hrho hrho_one hcover₂ htarget₂ haxis₂]
  simpa using hsource

/--
Dilated version: orthogonal section parameter bound.
-/
lemma abs_wz1PaperOrthogonalSectionParameter_le_dilated
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    |wz1PaperOrthogonalSectionParameter source anchor| ≤ 2 * rho := by
  have hinner :
      1 / 2 ≤ inner ℝ
          (wz1PaperDirection source)
          (wz1PaperDirection anchor) :=
    hcover.inner_direction_ge_half hrhoOne
  have hinnerPos :
      0 < inner ℝ
          (wz1PaperDirection source)
          (wz1PaperDirection anchor) := by linarith
  have hzero :
      dist
          (wz1TubeAxisZeroPoint source)
          (wz1TubeAxisZeroPoint anchor) ≤ rho :=
    hcover.components.1
  have hnumerator :
      |inner ℝ
          (wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint anchor)
          (wz1PaperDirection anchor)| ≤ rho := by
    calc
      |inner ℝ
          (wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint anchor)
          (wz1PaperDirection anchor)|
        ≤ ‖wz1TubeAxisZeroPoint source -
              wz1TubeAxisZeroPoint anchor‖ *
            ‖wz1PaperDirection anchor‖ :=
          abs_real_inner_le_norm _ _
      _ = dist
            (wz1TubeAxisZeroPoint source)
            (wz1TubeAxisZeroPoint anchor) := by
          rw [wz1PaperDirection_norm, mul_one, dist_eq_norm]
      _ ≤ rho := hzero
  unfold wz1PaperOrthogonalSectionParameter
  rw [abs_div, abs_neg, abs_of_pos hinnerPos]
  exact (div_le_iff₀ hinnerPos).mpr (by nlinarith)

/--
Dilated version of positional lower distortion.
-/
lemma wz1PaperUnitRescaling_dilated_source_zero_dist_le_target
    {delta rho targetDelta : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target₁ target₂ : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ2PaperDilatedTubeCovers 2 source₁ coarse)
    (hcover₂ : WZ2PaperDilatedTubeCovers 2 source₂ coarse)
    (hsource₁ : WZ1PaperTubeInLineClass source₁)
    (hsource₂ : WZ1PaperTubeInLineClass source₂)
    (htarget₁ : WZ1PaperTubeInLineClass target₁)
    (htarget₂ : WZ1PaperTubeInLineClass target₂)
    (haxis₁ :
      tubeAxisLine target₁ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₁)
    (haxis₂ :
      tubeAxisLine target₂ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₂) :
    dist
        (wz1TubeAxisZeroPoint source₁)
        (wz1TubeAxisZeroPoint source₂) ≤
      300 * rho *
          dist
            (wz1TubeAxisZeroPoint target₁)
            (wz1TubeAxisZeroPoint target₂) +
        6 * rho *
          InnerProductGeometry.angle
            (wz1PaperDirection source₁)
            (wz1PaperDirection source₂) := by
  let sourcePoint₁ :=
    wz1PaperOrthogonalSectionPoint source₁ coarse
  let sourcePoint₂ :=
    wz1PaperOrthogonalSectionPoint source₂ coarse
  let parameter₁ :=
    wz1PaperOrthogonalSectionParameter source₁ coarse
  let parameter₂ :=
    wz1PaperOrthogonalSectionParameter source₂ coarse
  have hinner₁ :
      1 / 2 ≤ inner ℝ
          (wz1PaperDirection source₁)
          (wz1PaperDirection coarse) :=
    hcover₁.inner_direction_ge_half hrho_one
  have hinner₂ :
      1 / 2 ≤ inner ℝ
          (wz1PaperDirection source₂)
          (wz1PaperDirection coarse) :=
    hcover₂.inner_direction_ge_half hrho_one
  have hinner₁_ne :
      inner ℝ
          (wz1PaperDirection source₁)
          (wz1PaperDirection coarse) ≠ 0 := by linarith
  have hinner₂_ne :
      inner ℝ
          (wz1PaperDirection source₂)
          (wz1PaperDirection coarse) ≠ 0 := by linarith
  have hsourcePoint₁ :
      sourcePoint₁ ∈ tubeAxisLine source₁ :=
    wz1PaperOrthogonalSectionPoint_mem_axis source₁ coarse
  have hsourcePoint₂ :
      sourcePoint₂ ∈ tubeAxisLine source₂ :=
    wz1PaperOrthogonalSectionPoint_mem_axis source₂ coarse
  have hsourcePoint₁_perp :
      inner ℝ
          (sourcePoint₁ - wz1TubeAxisZeroPoint coarse)
          (wz1PaperDirection coarse) = 0 :=
    wz1PaperOrthogonalSectionPoint_perp hinner₁_ne
  have hsourcePoint₂_perp :
      inner ℝ
          (sourcePoint₂ - wz1TubeAxisZeroPoint coarse)
          (wz1PaperDirection coarse) = 0 :=
    wz1PaperOrthogonalSectionPoint_perp hinner₂_ne
  have htarget_dist :
      dist
          (wz1TubeAxisZeroPoint target₁)
          (wz1TubeAxisZeroPoint target₂) =
        dist sourcePoint₁ sourcePoint₂ / (100 * rho) :=
    wz1PaperUnitRescaledAxisZeroPoint_dist_eq
      hrho htarget₁ htarget₂ haxis₁ haxis₂
      hsourcePoint₁ hsourcePoint₂
      hsourcePoint₁_perp hsourcePoint₂_perp
  have hparameter₂ : |parameter₂| ≤ 2 * rho :=
    abs_wz1PaperOrthogonalSectionParameter_le_dilated
      hrho hrho_one hcover₂
  have hzero_reintersection :
      ‖wz1TubeAxisZeroPoint source₁ -
          wz1TubeAxisZeroPoint source₂‖ ≤
        3 * ‖sourcePoint₁ - sourcePoint₂‖ +
          3 * (2 * rho) *
            ‖wz1PaperDirection source₁ -
              wz1PaperDirection source₂‖ := by
    exact zero_section_reintersection_dist_le
      (rho := 2 * rho)
      (parameter₁ := parameter₁)
      (parameter₂ := parameter₂)
      (zero₁ := wz1TubeAxisZeroPoint source₁)
      (zero₂ := wz1TubeAxisZeroPoint source₂)
      (direction₁ := wz1PaperDirection source₁)
      (direction₂ := wz1PaperDirection source₂)
      (section₁ := sourcePoint₁)
      (section₂ := sourcePoint₂)
      (by positivity)
      (wz1PaperDirection_norm source₁)
      hsource₁.1
      (wz1TubeAxisZeroPoint_coord_two source₁ hsource₁.vertical)
      (wz1TubeAxisZeroPoint_coord_two source₂ hsource₂.vertical)
      rfl rfl hparameter₂
  have hsource_chord :
      ‖wz1PaperDirection source₁ -
          wz1PaperDirection source₂‖ ≤
        InnerProductGeometry.angle
          (wz1PaperDirection source₁)
          (wz1PaperDirection source₂) :=
    unit_norm_sub_le_angle
      (wz1PaperDirection_norm source₁)
      (wz1PaperDirection_norm source₂)
  have hsection_distance :
      ‖sourcePoint₁ - sourcePoint₂‖ =
        100 * rho *
          dist
            (wz1TubeAxisZeroPoint target₁)
            (wz1TubeAxisZeroPoint target₂) := by
    rw [htarget_dist, dist_eq_norm]
    field_simp [hrho.ne'] <;> ring
  rw [dist_eq_norm]
  have hmain :
      ‖wz1TubeAxisZeroPoint source₁ -
          wz1TubeAxisZeroPoint source₂‖ ≤
        3 * ‖sourcePoint₁ - sourcePoint₂‖ +
          6 * rho *
            ‖wz1PaperDirection source₁ -
              wz1PaperDirection source₂‖ := by
    calc
      ‖wz1TubeAxisZeroPoint source₁ -
          wz1TubeAxisZeroPoint source₂‖
        ≤ 3 * ‖sourcePoint₁ - sourcePoint₂‖ +
              3 * (2 * rho) *
                ‖wz1PaperDirection source₁ -
                  wz1PaperDirection source₂‖ := hzero_reintersection
      _ = 3 * ‖sourcePoint₁ - sourcePoint₂‖ +
            6 * rho *
              ‖wz1PaperDirection source₁ -
                wz1PaperDirection source₂‖ := by ring
  rw [hsection_distance] at hmain
  have hfinal :
      3 * (100 * rho * dist (wz1TubeAxisZeroPoint target₁) (wz1TubeAxisZeroPoint target₂)) +
          6 * rho * ‖wz1PaperDirection source₁ - wz1PaperDirection source₂‖ ≤
        300 * rho * dist (wz1TubeAxisZeroPoint target₁) (wz1TubeAxisZeroPoint target₂) +
          6 * rho * InnerProductGeometry.angle (wz1PaperDirection source₁) (wz1PaperDirection source₂) := by
    have h : ‖wz1PaperDirection source₁ - wz1PaperDirection source₂‖ ≤
        InnerProductGeometry.angle (wz1PaperDirection source₁) (wz1PaperDirection source₂) :=
      hsource_chord
    nlinarith
  exact le_trans hmain hfinal

/--
Dilated full lower distortion of the paper line metric.
-/
lemma wz1PaperUnitRescaling_dilated_source_lineDistance_le_target
    {delta rho targetDelta : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target₁ target₂ : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ2PaperDilatedTubeCovers 2 source₁ coarse)
    (hcover₂ : WZ2PaperDilatedTubeCovers 2 source₂ coarse)
    (hsource₁ : WZ1PaperTubeInLineClass source₁)
    (hsource₂ : WZ1PaperTubeInLineClass source₂)
    (htarget₁ : WZ1PaperTubeInLineClass target₁)
    (htarget₂ : WZ1PaperTubeInLineClass target₂)
    (haxis₁ :
      tubeAxisLine target₁ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₁)
    (haxis₂ :
      tubeAxisLine target₂ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₂) :
    wz1PaperLineDistance source₁ source₂ ≤
      7350 * rho *
        wz1PaperLineDistance target₁ target₂ := by
  have hposition :=
    wz1PaperUnitRescaling_dilated_source_zero_dist_le_target
      hrho hrho_one hcover₁ hcover₂
      hsource₁ hsource₂ htarget₁ htarget₂
      haxis₁ haxis₂
  have hangle :=
    wz1PaperUnitRescaling_dilated_source_angle_le_target_angle
      hrho hrho_one hcover₁ hcover₂
      htarget₁ htarget₂ haxis₁ haxis₂
  have hsource_angle_nonneg :
      0 ≤ InnerProductGeometry.angle
        (wz1PaperDirection source₁)
        (wz1PaperDirection source₂) :=
    InnerProductGeometry.angle_nonneg _ _
  have htarget_angle_nonneg :
      0 ≤ InnerProductGeometry.angle
        (wz1PaperDirection target₁)
        (wz1PaperDirection target₂) :=
    InnerProductGeometry.angle_nonneg _ _
  have htarget_dist_nonneg :
      0 ≤ dist
        (wz1TubeAxisZeroPoint target₁)
        (wz1TubeAxisZeroPoint target₂) :=
    dist_nonneg
  dsimp only [wz1PaperLineDistance] at *
  nlinarith

end Kakeya.Assouad

end
