import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CoupledProjectedNormalCancellation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.InverseTransposeNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ADTransfer

/-!
# A nondegenerate common-slice normal for the coupled Section-6 map

The fixed-frame projected normal has the correct common-slice projection, but
need not be incident to an unrelated tube in the same global-grain label.  We
instead add the fixed rotated transverse unit vector before normalizing.  On a
fixed rotated-y slice this only adds a constant to every scalar projection.
After the triangular inverse transpose, the added component supplies the
large `1 / (m * (d-c))` norm which cancels the corresponding operator norm.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Complete the fixed-frame projection by a unit transverse component. -/
def pureWZ2FrameCompletedNormal (frameSlope : ℝ) (normal : Point3) : Point3 :=
  pureWZ2FrameProjectedNormal frameSlope normal +
    pureWZ2RotatedYAxis frameSlope

/-- The normalized completed normal. -/
def pureWZ2NormalizedFrameCompletedNormal
    (frameSlope : ℝ) (normal : Point3) : Point3 :=
  let completed := pureWZ2FrameCompletedNormal frameSlope normal
  (‖completed‖⁻¹ : ℝ) • completed

@[simp] theorem pureWZ2HorizontalRotation_completed_coord_one
    (frameSlope : ℝ) (normal : Point3) :
    pureWZ2HorizontalRotation frameSlope
        (pureWZ2FrameCompletedNormal frameSlope normal) 1 = 1 := by
  simp [pureWZ2FrameCompletedNormal, pureWZ2FrameProjectedNormal,
    pureWZ2RotatedYAxis, xzProjectedNormal]

theorem pureWZ2FrameCompletedNormal_norm_lower
    (frameSlope : ℝ) (normal : Point3) :
    1 ≤ ‖pureWZ2FrameCompletedNormal frameSlope normal‖ := by
  have hcoord := PiLp.norm_apply_le
    (pureWZ2HorizontalRotation frameSlope
      (pureWZ2FrameCompletedNormal frameSlope normal)) (1 : Fin 3)
  rw [pureWZ2HorizontalRotation_completed_coord_one,
    (pureWZ2HorizontalRotation frameSlope).norm_map] at hcoord
  simpa using hcoord

theorem pureWZ2FrameCompletedNormal_ne_zero
    (frameSlope : ℝ) (normal : Point3) :
    pureWZ2FrameCompletedNormal frameSlope normal ≠ 0 := by
  intro hzero
  have hlower := pureWZ2FrameCompletedNormal_norm_lower frameSlope normal
  rw [hzero, norm_zero] at hlower
  norm_num at hlower

theorem pureWZ2NormalizedFrameCompletedNormal_unit
    (frameSlope : ℝ) (normal : Point3) :
    ‖pureWZ2NormalizedFrameCompletedNormal frameSlope normal‖ = 1 := by
  exact norm_smul_inv_norm
    (pureWZ2FrameCompletedNormal_ne_zero frameSlope normal)

theorem pureWZ2FrameCompletedNormal_sub
    (frameSlope : ℝ) (first second : Point3) :
    pureWZ2FrameCompletedNormal frameSlope first -
        pureWZ2FrameCompletedNormal frameSlope second =
      pureWZ2FrameProjectedNormal frameSlope first -
        pureWZ2FrameProjectedNormal frameSlope second := by
  simp [pureWZ2FrameCompletedNormal]

/-- Completion and normalization cost at most two in Lipschitz norm. -/
theorem pureWZ2NormalizedFrameCompletedNormal_sub_norm_le
    (frameSlope : ℝ) (first second : Point3) :
    ‖pureWZ2NormalizedFrameCompletedNormal frameSlope first -
        pureWZ2NormalizedFrameCompletedNormal frameSlope second‖ ≤
      2 * ‖first - second‖ := by
  let firstCompleted := pureWZ2FrameCompletedNormal frameSlope first
  let secondCompleted := pureWZ2FrameCompletedNormal frameSlope second
  have hnormalize := normalization_lipschitz
    (x := firstCompleted) (y := secondCompleted) (m := (1 : ℝ))
    (by norm_num)
    (pureWZ2FrameCompletedNormal_norm_lower frameSlope first)
    (pureWZ2FrameCompletedNormal_norm_lower frameSlope second)
  have hproject := pureWZ2FrameProjectedNormal_sub_norm_le
    frameSlope first second
  rw [pureWZ2FrameCompletedNormal_sub] at hnormalize
  simpa [firstCompleted, secondCompleted,
    pureWZ2NormalizedFrameCompletedNormal] using
      hnormalize.trans (mul_le_mul_of_nonneg_left hproject (by norm_num))

/-- On one fixed rotated-y slice, completion changes the original scalar
projection only by a constant; normalization is a positive dilation. -/
theorem scalarProjection_normalizedFrameCompleted_eq_affine
    (frameSlope y0 : ℝ) (normal : Point3) (E : Set Point3)
    (hEslice : ∀ point ∈ E,
      pureWZ2HorizontalRotation frameSlope point 1 = y0) :
    let completed := pureWZ2FrameCompletedNormal frameSlope normal
    let a := ‖completed‖⁻¹
    scalarProjection
        (pureWZ2NormalizedFrameCompletedNormal frameSlope normal) E =
      (fun value : ℝ => a * value +
        a * y0 *
          (1 - pureWZ2HorizontalRotation frameSlope normal 1)) ''
        scalarProjection normal E := by
  dsimp only
  let rotation := pureWZ2HorizontalRotation frameSlope
  let completed := pureWZ2FrameCompletedNormal frameSlope normal
  let a := ‖completed‖⁻¹
  have hpoint : ∀ point ∈ E,
      inner ℝ point
          (pureWZ2NormalizedFrameCompletedNormal frameSlope normal) =
        a * inner ℝ point normal +
          a * y0 * (1 - rotation normal 1) := by
    intro point hp
    have hprojected :
        inner ℝ point (pureWZ2FrameProjectedNormal frameSlope normal) =
          inner ℝ point normal - y0 * rotation normal 1 := by
      rw [pureWZ2FrameProjectedNormal,
        ← rotation.inner_map_map point
          (rotation.symm (xzProjectedNormal (rotation normal)))]
      simp only [rotation.apply_symm_apply]
      have hfull := rotation.inner_map_map point normal
      have hdelete :
          inner ℝ (rotation point) (xzProjectedNormal (rotation normal)) =
            inner ℝ (rotation point) (rotation normal) -
              (rotation point) 1 * (rotation normal) 1 := by
        rw [PiLp.inner_apply, PiLp.inner_apply]
        simp [xzProjectedNormal, Fin.sum_univ_succ, RCLike.inner_apply]
        ring
      rw [hdelete, hfull, hEslice point hp]
    have htransverse :
        inner ℝ point (pureWZ2RotatedYAxis frameSlope) = y0 := by
      rw [pureWZ2HorizontalRotation_inner_y]
      exact hEslice point hp
    rw [pureWZ2NormalizedFrameCompletedNormal, inner_smul_right,
      pureWZ2FrameCompletedNormal, inner_add_right, hprojected, htransverse]
    dsimp only [a, completed, rotation]
    unfold pureWZ2FrameCompletedNormal
    ring
  ext value
  constructor
  · rintro ⟨point, hp, rfl⟩
    refine ⟨inner ℝ point normal, ⟨point, hp, rfl⟩, ?_⟩
    exact (hpoint point hp).symm
  · rintro ⟨source, ⟨point, hp, rfl⟩, rfl⟩
    exact ⟨point, hp, hpoint point hp⟩

/-- The completed unit normal keeps at least half of its fixed transverse
component.  The coarse constant avoids square-root arithmetic downstream. -/
theorem normalizedFrameCompleted_rotated_one_lower
    (frameSlope : ℝ) (normal : Point3) (hunit : ‖normal‖ = 1) :
    (1 / 2 : ℝ) ≤
      pureWZ2HorizontalRotation frameSlope
        (pureWZ2NormalizedFrameCompletedNormal frameSlope normal) 1 := by
  let projected := pureWZ2FrameProjectedNormal frameSlope normal
  let transverse := pureWZ2RotatedYAxis frameSlope
  let completed := pureWZ2FrameCompletedNormal frameSlope normal
  have hprojectedNorm : ‖projected‖ ≤ 1 := by
    dsimp only [projected]
    rw [pureWZ2FrameProjectedNormal_norm]
    exact (norm_xzProjected_le_norm
      (pureWZ2HorizontalRotation frameSlope normal)).trans_eq <| by
        rw [(pureWZ2HorizontalRotation frameSlope).norm_map, hunit]
  have hcompletedUpper : ‖completed‖ ≤ 2 := by
    dsimp only [completed, pureWZ2FrameCompletedNormal]
    calc
      ‖projected + transverse‖ ≤ ‖projected‖ + ‖transverse‖ := norm_add_le _ _
      _ ≤ 1 + 1 := add_le_add hprojectedNorm
        (le_of_eq (pureWZ2RotatedYAxis_unit frameSlope))
      _ = 2 := by norm_num
  have hcompletedPos : 0 < ‖completed‖ :=
    lt_of_lt_of_le (by norm_num)
      (pureWZ2FrameCompletedNormal_norm_lower frameSlope normal)
  have hinvLower : (1 / 2 : ℝ) ≤ ‖completed‖⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ (by norm_num) hcompletedPos).2 hcompletedUpper
  change (1 / 2 : ℝ) ≤
    pureWZ2HorizontalRotation frameSlope
      ((‖completed‖⁻¹ : ℝ) • completed) 1
  rw [map_smul, PiLp.smul_apply,
    show pureWZ2HorizontalRotation frameSlope completed 1 = 1 by
      exact pureWZ2HorizontalRotation_completed_coord_one frameSlope normal]
  simpa using hinvLower

/-- The completed normal's transverse coordinate survives a nearby-frame
inverse transpose.  The explicit quarter-gap is the place where the
`O(rho)` frame error is paid; it is not hidden in a local-AD radius. -/
theorem dPhiInvT_normalizedFrameCompleted_norm_lower_of_close
    (g : SlopeFunction) {c d m frameSlope : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (hclose : |frameSlope - g (c + (d - c) / 2)| ≤ 1 / 4)
    (normal : Point3)
    (hunit : ‖normal‖ = 1) :
    1 / (2 * (m * (d - c))) ≤
      ‖dPhiInvT g c d m
        (pureWZ2NormalizedFrameCompletedNormal
          frameSlope normal)‖ := by
  let mapSlope := g (c + (d - c) / 2)
  let completed := pureWZ2NormalizedFrameCompletedNormal frameSlope normal
  let b := m * (d - c) / 2
  have hb : 0 < b := by dsimp only [b] <;> positivity
  have hcompletedUnit : ‖completed‖ = 1 := by
    exact pureWZ2NormalizedFrameCompletedNormal_unit frameSlope normal
  have hrotated := normalizedFrameCompleted_rotated_one_lower
    frameSlope normal hunit
  have hframeNumerator :
      pureWZ2HorizontalNorm frameSlope / 2 ≤
        -frameSlope * completed 0 + completed 1 := by
    rw [pureWZ2HorizontalRotation_coord_one] at hrotated
    simpa [div_eq_mul_inv, mul_comm] using
      (le_div_iff₀ (pureWZ2HorizontalNorm_pos frameSlope)).mp hrotated
  have hframeNumeratorOne : (1 / 2 : ℝ) ≤
      -frameSlope * completed 0 + completed 1 := by
    have hnormOne : (1 : ℝ) ≤ pureWZ2HorizontalNorm frameSlope := by
      have hsquare := pureWZ2HorizontalNorm_sq frameSlope
      nlinarith [pureWZ2HorizontalNorm_pos frameSlope, sq_nonneg frameSlope]
    linarith
  have hcompletedZero : |completed 0| ≤ 1 := by
    have hcoord := PiLp.norm_apply_le completed (0 : Fin 3)
    simpa [Real.norm_eq_abs, hcompletedUnit] using hcoord
  have herror :
      |(frameSlope - mapSlope) * completed 0| ≤ 1 / 4 := by
    rw [abs_mul]
    calc
      |frameSlope - mapSlope| * |completed 0| ≤ (1 / 4 : ℝ) * 1 := by
        gcongr
      _ = 1 / 4 := by norm_num
  have hmapNumerator : (1 / 4 : ℝ) ≤
      -mapSlope * completed 0 + completed 1 := by
    have hidentity :
        -mapSlope * completed 0 + completed 1 =
          (-frameSlope * completed 0 + completed 1) +
            (frameSlope - mapSlope) * completed 0 := by ring
    rw [hidentity]
    nlinarith [neg_abs_le ((frameSlope - mapSlope) * completed 0)]
  have hcoord :
      dPhiInvT g c d m completed 1 =
        (-mapSlope * completed 0 + completed 1) / b := by
    simp [dPhiInvT, mapSlope, b, point3]
    ring
  have hcoordLower : 1 / (4 * b) ≤
      |dPhiInvT g c d m completed 1| := by
    rw [hcoord, abs_of_pos (div_pos (lt_of_lt_of_le (by norm_num)
      hmapNumerator) hb)]
    calc
      1 / (4 * b) = (1 / 4) / b := by field_simp [hb.ne']
      _ ≤ (-mapSlope * completed 0 + completed 1) / b :=
        div_le_div_of_nonneg_right hmapNumerator hb.le
  have hnorm := PiLp.norm_apply_le (dPhiInvT g c d m completed) (1 : Fin 3)
  have heq : 4 * b = 2 * (m * (d - c)) := by dsimp only [b] <;> ring
  rw [heq] at hcoordLower
  exact hcoordLower.trans (by simpa [Real.norm_eq_abs] using hnorm)

/-- Exact-frame specialization of the nearby-frame lower bound. -/
theorem dPhiInvT_normalizedFrameCompleted_norm_lower
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (normal : Point3)
    (hunit : ‖normal‖ = 1) :
    1 / (m * (d - c)) ≤
      ‖dPhiInvT g c d m
        (pureWZ2NormalizedFrameCompletedNormal
          (g (c + (d - c) / 2)) normal)‖ := by
  -- Keep the sharper exact-frame estimate for compatibility.
  let frameSlope := g (c + (d - c) / 2)
  let completed := pureWZ2NormalizedFrameCompletedNormal frameSlope normal
  let b := m * (d - c) / 2
  have hb : 0 < b := by dsimp only [b] <;> positivity
  have hrotated := normalizedFrameCompleted_rotated_one_lower
    frameSlope normal hunit
  have hnumeratorOne : (1 / 2 : ℝ) ≤
      -frameSlope * completed 0 + completed 1 := by
    rw [pureWZ2HorizontalRotation_coord_one] at hrotated
    have hnormOne : (1 : ℝ) ≤ pureWZ2HorizontalNorm frameSlope := by
      have hsquare := pureWZ2HorizontalNorm_sq frameSlope
      nlinarith [pureWZ2HorizontalNorm_pos frameSlope, sq_nonneg frameSlope]
    have := (le_div_iff₀ (pureWZ2HorizontalNorm_pos frameSlope)).mp hrotated
    nlinarith
  have hcoord : dPhiInvT g c d m completed 1 =
      (-frameSlope * completed 0 + completed 1) / b := by
    simp [dPhiInvT, frameSlope, b, point3]
    ring
  have hcoordLower : 1 / (2 * b) ≤
      |dPhiInvT g c d m completed 1| := by
    rw [hcoord, abs_of_pos (div_pos (lt_of_lt_of_le (by norm_num)
      hnumeratorOne) hb)]
    calc
      1 / (2 * b) = (1 / 2) / b := by field_simp [hb.ne']
      _ ≤ (-frameSlope * completed 0 + completed 1) / b :=
        div_le_div_of_nonneg_right hnumeratorOne hb.le
  have hnorm := PiLp.norm_apply_le (dPhiInvT g c d m completed) (1 : Fin 3)
  have heq : 2 * b = m * (d - c) := by dsimp only [b] <;> ring
  rw [heq] at hcoordLower
  exact hcoordLower.trans (by simpa [Real.norm_eq_abs] using hnorm)

/-- Algebraic cancellation of the coupled transverse parameter in the
pre-normalization Lipschitz coefficient. -/
private theorem coupled_completed_coefficient_eq
    {c d m : ℝ} (hcd : c < d) (hm : 0 < m) :
    let b := m * (d - c) / 2
    (2 / (1 / (m * (d - c)))) * (Real.sqrt 6 / b) * 2 =
      8 * Real.sqrt 6 := by
  dsimp only
  field_simp [hm.ne', sub_ne_zero.mpr hcd.ne']
  ring

/-- The weaker nearby-frame denominator still cancels the transverse scale,
at the cost of one further factor two. -/
private theorem coupled_completed_coefficient_eq_of_close
    {c d m : ℝ} (hcd : c < d) (hm : 0 < m) :
    let b := m * (d - c) / 2
    (2 / (1 / (2 * (m * (d - c))))) * (Real.sqrt 6 / b) * 2 =
      16 * Real.sqrt 6 := by
  dsimp only
  field_simp [hm.ne', sub_ne_zero.mpr hcd.ne']
  ring

/-- Nearby-frame version of the normalized inverse-transpose Lipschitz
estimate. -/
theorem normalized_dPhiInvT_completed_lipschitz_of_close
    {sourceDelta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) {c d m frameSlope : ℝ}
    (hcd : c < d) (hm : 0 < m) (hmOne : m ≤ 1)
    (hdc : d - c ≤ 1 / 25) (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hclose : |frameSlope - g (c + (d - c) / 2)| ≤ 1 / 4) :
    LipschitzWith 48 (fun point =>
      let completed := pureWZ2NormalizedFrameCompletedNormal
        frameSlope (sourceLocal.planeMap point)
      (‖dPhiInvT g c d m completed‖⁻¹ : ℝ) •
        dPhiInvT g c d m completed) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm]
  let firstCompleted := pureWZ2NormalizedFrameCompletedNormal
    frameSlope (sourceLocal.planeMap first)
  let secondCompleted := pureWZ2NormalizedFrameCompletedNormal
    frameSlope (sourceLocal.planeMap second)
  have hnormalFirst : 1 / (2 * (m * (d - c))) ≤
      ‖dPhiInvT g c d m firstCompleted‖ := by
    simpa only [firstCompleted] using
      dPhiInvT_normalizedFrameCompleted_norm_lower_of_close
        g hcd hm hclose (sourceLocal.planeMap first)
          (sourceLocal.planeMap_unit first)
  have hnormalSecond : 1 / (2 * (m * (d - c))) ≤
      ‖dPhiInvT g c d m secondCompleted‖ := by
    simpa only [secondCompleted] using
      dPhiInvT_normalizedFrameCompleted_norm_lower_of_close
        g hcd hm hclose (sourceLocal.planeMap second)
          (sourceLocal.planeMap_unit second)
  have hlower : 0 < 1 / (2 * (m * (d - c))) := by positivity
  have hnormalize := normalization_lipschitz hlower hnormalFirst hnormalSecond
  have hlinear :
      ‖dPhiInvT g c d m firstCompleted -
          dPhiInvT g c d m secondCompleted‖ ≤
        (Real.sqrt 6 / (m * (d - c) / 2)) *
          ‖firstCompleted - secondCompleted‖ := by
    rw [← dPhiInvT_sub]
    exact dPhiInvT_opNorm_bound g c d m hcd hm hmOne hdc hg hsub _
  have hcompleted : ‖firstCompleted - secondCompleted‖ ≤
      2 * ‖sourceLocal.planeMap first - sourceLocal.planeMap second‖ := by
    simpa only [firstCompleted, secondCompleted] using
      pureWZ2NormalizedFrameCompletedNormal_sub_norm_le frameSlope
        (sourceLocal.planeMap first) (sourceLocal.planeMap second)
  have hsource := sourceLocal.planeMap_lipschitz.dist_le_mul first second
  rw [dist_eq_norm] at hsource
  have hsqrtSix : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
      Real.sqrt_nonneg 6]
  calc
    _ ≤ (2 / (1 / (2 * (m * (d - c))))) *
        ‖dPhiInvT g c d m firstCompleted -
          dPhiInvT g c d m secondCompleted‖ := hnormalize
    _ ≤ (2 / (1 / (2 * (m * (d - c))))) *
        ((Real.sqrt 6 / (m * (d - c) / 2)) *
          ‖firstCompleted - secondCompleted‖) := by
      exact mul_le_mul_of_nonneg_left hlinear (by positivity)
    _ ≤ (2 / (1 / (2 * (m * (d - c))))) *
        ((Real.sqrt 6 / (m * (d - c) / 2)) *
          (2 * ‖sourceLocal.planeMap first -
            sourceLocal.planeMap second‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcompleted (by positivity)
    _ = 16 * Real.sqrt 6 *
        ‖sourceLocal.planeMap first - sourceLocal.planeMap second‖ := by
      rw [← coupled_completed_coefficient_eq_of_close hcd hm]
      ring
    _ ≤ 48 * ‖sourceLocal.planeMap first - sourceLocal.planeMap second‖ := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
    _ ≤ 48 * dist first second :=
      mul_le_mul_of_nonneg_left (by simpa using hsource) (by norm_num)

/-- On unit source normals, the normalized completed inverse-transpose field
has a Lipschitz bound independent of the coupled transverse scale. -/
theorem normalized_dPhiInvT_completed_sub_norm_le
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (hmOne : m ≤ 1)
    (hdc : d - c ≤ 1 / 25) (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (first second : Point3) (hfirst : ‖first‖ = 1)
    (hsecond : ‖second‖ = 1) :
    let firstCompleted := pureWZ2NormalizedFrameCompletedNormal
      (g (c + (d - c) / 2)) first
    let secondCompleted := pureWZ2NormalizedFrameCompletedNormal
      (g (c + (d - c) / 2)) second
    ‖(‖dPhiInvT g c d m firstCompleted‖⁻¹ : ℝ) •
          dPhiInvT g c d m firstCompleted -
        (‖dPhiInvT g c d m secondCompleted‖⁻¹ : ℝ) •
          dPhiInvT g c d m secondCompleted‖ ≤
      24 * ‖first - second‖ := by
  dsimp only
  let firstCompleted := pureWZ2NormalizedFrameCompletedNormal
    (g (c + (d - c) / 2)) first
  let secondCompleted := pureWZ2NormalizedFrameCompletedNormal
    (g (c + (d - c) / 2)) second
  have hnormalFirst : 1 / (m * (d - c)) ≤
      ‖dPhiInvT g c d m firstCompleted‖ :=
    by simpa only [firstCompleted] using
      dPhiInvT_normalizedFrameCompleted_norm_lower g hcd hm first hfirst
  have hnormalSecond : 1 / (m * (d - c)) ≤
      ‖dPhiInvT g c d m secondCompleted‖ :=
    by simpa only [secondCompleted] using
      dPhiInvT_normalizedFrameCompleted_norm_lower g hcd hm second hsecond
  have hlower : 0 < 1 / (m * (d - c)) := by positivity
  have hnormalize :
      ‖(‖dPhiInvT g c d m firstCompleted‖⁻¹ : ℝ) •
            dPhiInvT g c d m firstCompleted -
          (‖dPhiInvT g c d m secondCompleted‖⁻¹ : ℝ) •
            dPhiInvT g c d m secondCompleted‖ ≤
        (2 / (1 / (m * (d - c)))) *
          ‖dPhiInvT g c d m firstCompleted -
            dPhiInvT g c d m secondCompleted‖ :=
    normalization_lipschitz hlower hnormalFirst hnormalSecond
  have hlinear :
      ‖dPhiInvT g c d m firstCompleted -
          dPhiInvT g c d m secondCompleted‖ ≤
        (Real.sqrt 6 / (m * (d - c) / 2)) *
          ‖firstCompleted - secondCompleted‖ := by
    rw [← dPhiInvT_sub]
    exact dPhiInvT_opNorm_bound g c d m hcd hm hmOne hdc hg hsub _
  have hcompleted : ‖firstCompleted - secondCompleted‖ ≤
      2 * ‖first - second‖ := by
    simpa only [firstCompleted, secondCompleted] using
      pureWZ2NormalizedFrameCompletedNormal_sub_norm_le
        (g (c + (d - c) / 2)) first second
  have hsqrtSix : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
      Real.sqrt_nonneg 6]
  have hcoefficient :
      (2 / (1 / (m * (d - c)))) *
          (Real.sqrt 6 / (m * (d - c) / 2)) * 2 =
        8 * Real.sqrt 6 := by
    exact coupled_completed_coefficient_eq hcd hm
  calc
    _ ≤ (2 / (1 / (m * (d - c)))) *
        ‖dPhiInvT g c d m firstCompleted -
          dPhiInvT g c d m secondCompleted‖ := hnormalize
    _ ≤ (2 / (1 / (m * (d - c)))) *
        ((Real.sqrt 6 / (m * (d - c) / 2)) *
          ‖firstCompleted - secondCompleted‖) := by
      exact mul_le_mul_of_nonneg_left hlinear (by positivity)
    _ ≤ (2 / (1 / (m * (d - c)))) *
        ((Real.sqrt 6 / (m * (d - c) / 2)) *
          (2 * ‖first - second‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcompleted (by positivity)
    _ = 8 * Real.sqrt 6 * ‖first - second‖ := by
      rw [← hcoefficient]
      ring
    _ ≤ 24 * ‖first - second‖ := by
      have hnormNonneg : 0 ≤ ‖first - second‖ := norm_nonneg _
      nlinarith

/-- The height expansion in the triangular map gives a direction lower bound
that is independent of its transverse parameter. -/
theorem dPhiLin_norm_lower_of_vertical
    (g : SlopeFunction) {c d m : ℝ} (hcd : c < d)
    (direction : Point3) (hvertical : (1 / 2 : ℝ) ≤ |direction 2|) :
    1 / (d - c) ≤ ‖dPhiLin g c d m direction‖ := by
  have hcoord := PiLp.norm_apply_le (dPhiLin g c d m direction) (2 : Fin 3)
  have hcoordEq :
      dPhiLin g c d m direction 2 = (2 / (d - c)) * direction 2 := by
    simp [dPhiLin, point3]
  rw [hcoordEq, Real.norm_eq_abs, abs_mul,
    abs_of_pos (div_pos (by norm_num) (sub_pos.mpr hcd))] at hcoord
  have hfactor : 0 ≤ 2 / (d - c) := by positivity
  calc
    1 / (d - c) = (2 / (d - c)) * (1 / 2) := by
      field_simp [sub_ne_zero.mpr hcd.ne']
    _ ≤ (2 / (d - c)) * |direction 2| :=
      mul_le_mul_of_nonneg_left hvertical hfactor
    _ ≤ ‖dPhiLin g c d m direction‖ := hcoord

/-- A common slice taken in a nearby fixed frame is still uniformly
noncontracted by the triangular linear map.  The frame error is paid here,
as a fixed factor two, rather than inserted into the source local-AD radius. -/
theorem dPhiLin_norm_ge_half_of_same_rotated_y
    (g : SlopeFunction) {c d m frameSlope : ℝ}
    (hcd : c < d) (hdc : d - c ≤ 2)
    (hframe : |frameSlope| ≤ 1)
    (hclose : |frameSlope - g (c + (d - c) / 2)| ≤ 1 / 4)
    (first second : Point3)
    (hsame : pureWZ2HorizontalRotation frameSlope first 1 =
      pureWZ2HorizontalRotation frameSlope second 1) :
    ‖first - second‖ ≤ 2 * ‖dPhiLin g c d m (first - second)‖ := by
  let mapSlope := g (c + (d - c) / 2)
  let difference := first - second
  let heightFactor := 2 / (d - c)
  have hlengthPos : 0 < d - c := sub_pos.mpr hcd
  have hheightOne : 1 ≤ heightFactor := by
    dsimp only [heightFactor]
    exact (le_div_iff₀ hlengthPos).2 (by simpa using hdc)
  have hrotated : pureWZ2HorizontalRotation frameSlope difference 1 = 0 := by
    rw [show difference = first - second by rfl,
      (pureWZ2HorizontalRotation frameSlope).map_sub, PiLp.sub_apply, hsame,
      sub_self]
  have hy : difference 1 = frameSlope * difference 0 := by
    rw [pureWZ2HorizontalRotation_coord_one] at hrotated
    have hnorm : pureWZ2HorizontalNorm frameSlope ≠ 0 :=
      (pureWZ2HorizontalNorm_pos _).ne'
    rcases div_eq_zero_iff.mp hrotated with hzero | hzero
    · linarith
    · exact (hnorm hzero).elim
  have hcoefficient : (3 / 4 : ℝ) ≤ 1 + mapSlope * frameSlope := by
    have herror : |(mapSlope - frameSlope) * frameSlope| ≤ 1 / 4 := by
      rw [abs_mul]
      have hgap : |mapSlope - frameSlope| ≤ 1 / 4 := by
        simpa [mapSlope, abs_sub_comm] using hclose
      calc
        |mapSlope - frameSlope| * |frameSlope| ≤ (1 / 4 : ℝ) * 1 := by
          gcongr
        _ = 1 / 4 := by norm_num
    have hidentity : 1 + mapSlope * frameSlope =
        1 + frameSlope ^ 2 + (mapSlope - frameSlope) * frameSlope := by ring
    rw [hidentity]
    nlinarith [sq_nonneg frameSlope,
      neg_abs_le ((mapSlope - frameSlope) * frameSlope)]
  have hcoefficientAbs : (3 / 4 : ℝ) ≤
      |1 + mapSlope * frameSlope| :=
    hcoefficient.trans (le_abs_self _)
  have hsourceSq := point3_coord_norm_sq difference
  have htargetSq := point3_coord_norm_sq (dPhiLin g c d m difference)
  have htargetZero : dPhiLin g c d m difference 0 =
      (1 + mapSlope * frameSlope) * difference 0 := by
    simp [dPhiLin, mapSlope, point3, hy]
    ring
  have htargetTwo : dPhiLin g c d m difference 2 =
      heightFactor * difference 2 := by
    simp [dPhiLin, heightFactor, point3]
  have hframeSq : frameSlope ^ 2 ≤ 1 := by
    rw [← sq_abs frameSlope]
    simpa only [one_pow] using
      (sq_le_sq₀ (abs_nonneg frameSlope) (by norm_num)).2 hframe
  have hxy : difference 0 ^ 2 + difference 1 ^ 2 ≤
      4 * (dPhiLin g c d m difference 0) ^ 2 := by
    rw [hy, htargetZero]
    have hsourceBound : difference 0 ^ 2 +
        (frameSlope * difference 0) ^ 2 ≤
      2 * difference 0 ^ 2 := by
      have hproduct : frameSlope ^ 2 * difference 0 ^ 2 ≤
          1 * difference 0 ^ 2 :=
        mul_le_mul_of_nonneg_right hframeSq (sq_nonneg (difference 0))
      rw [mul_pow]
      nlinarith
    have htargetLower : (9 / 16 : ℝ) * difference 0 ^ 2 ≤
        ((1 + mapSlope * frameSlope) * difference 0) ^ 2 := by
      have hsquare : (3 / 4 : ℝ) ^ 2 ≤
          |1 + mapSlope * frameSlope| ^ 2 := by gcongr
      rw [sq_abs] at hsquare
      nlinarith [sq_nonneg (difference 0),
        mul_le_mul_of_nonneg_right hsquare (sq_nonneg (difference 0))]
    nlinarith
  have hz : difference 2 ^ 2 ≤
      (dPhiLin g c d m difference 2) ^ 2 := by
    rw [htargetTwo]
    have hheightSq : 1 ≤ heightFactor ^ 2 := by
      nlinarith [sq_nonneg heightFactor]
    nlinarith [sq_nonneg (difference 2),
      mul_le_mul_of_nonneg_right hheightSq (sq_nonneg (difference 2))]
  have hsquares : ‖difference‖ ^ 2 ≤
      (2 * ‖dPhiLin g c d m difference‖) ^ 2 := by
    have htargetOneNonnegative :
        0 ≤ (dPhiLin g c d m difference 1) ^ 2 := sq_nonneg _
    have htargetTwoNonnegative :
        0 ≤ (dPhiLin g c d m difference 2) ^ 2 := sq_nonneg _
    calc
      ‖difference‖ ^ 2 =
          difference 0 ^ 2 + difference 1 ^ 2 + difference 2 ^ 2 := hsourceSq
      _ = (difference 0 ^ 2 + difference 1 ^ 2) + difference 2 ^ 2 := by ring
      _ ≤ 4 * (dPhiLin g c d m difference 0) ^ 2 +
          (dPhiLin g c d m difference 2) ^ 2 := add_le_add hxy hz
      _ ≤ 4 * ((dPhiLin g c d m difference 0) ^ 2 +
          (dPhiLin g c d m difference 1) ^ 2 +
          (dPhiLin g c d m difference 2) ^ 2) := by
        linarith
      _ = 4 * ‖dPhiLin g c d m difference‖ ^ 2 := by rw [htargetSq]
      _ = (2 * ‖dPhiLin g c d m difference‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg difference)
    (mul_nonneg (by norm_num) (norm_nonneg _))).mp hsquares

/-- The normalized image of any vertical-chart direction has small
incidence with the completed transported normal.  This estimate is tube-wise
without requiring the common-slice companion to belong to that tube. -/
theorem normalized_dPhi_completed_incidence_le
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (direction normal : Point3) (hdirection : ‖direction‖ = 1)
    (hvertical : (1 / 2 : ℝ) ≤ |direction 2|)
    (hnormal : ‖normal‖ = 1) :
    |inner ℝ
        ((‖dPhiLin g c d m direction‖⁻¹ : ℝ) •
          dPhiLin g c d m direction)
        ((‖dPhiInvT g c d m
            (pureWZ2NormalizedFrameCompletedNormal
              (g (c + (d - c) / 2)) normal)‖⁻¹ : ℝ) •
          dPhiInvT g c d m
            (pureWZ2NormalizedFrameCompletedNormal
              (g (c + (d - c) / 2)) normal))| ≤
      m * (d - c) ^ 2 := by
  let completed := pureWZ2NormalizedFrameCompletedNormal
    (g (c + (d - c) / 2)) normal
  have hdirectionNe : direction ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hdirection
    norm_num at hdirection
  have hcompletedUnit : ‖completed‖ = 1 := by
    exact pureWZ2NormalizedFrameCompletedNormal_unit _ _
  have hcompletedNe : completed ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hcompletedUnit
    norm_num at hcompletedUnit
  have hidentity := incidence_preservation g c d m hcd hm
    direction completed hdirectionNe hcompletedNe
  have hdirLower : 1 / (d - c) ≤ ‖dPhiLin g c d m direction‖ :=
    dPhiLin_norm_lower_of_vertical g hcd direction hvertical
  have hnormalLower : 1 / (m * (d - c)) ≤
      ‖dPhiInvT g c d m completed‖ := by
    simpa only [completed] using
      dPhiInvT_normalizedFrameCompleted_norm_lower g hcd hm normal hnormal
  have hdcPos : 0 < d - c := sub_pos.mpr hcd
  have hdenomPos : 0 <
      ‖dPhiLin g c d m direction‖ * ‖dPhiInvT g c d m completed‖ := by
    exact mul_pos (lt_of_lt_of_le (by positivity) hdirLower)
      (lt_of_lt_of_le (by positivity) hnormalLower)
  have hdenomLower : 1 / (m * (d - c) ^ 2) ≤
      ‖dPhiLin g c d m direction‖ * ‖dPhiInvT g c d m completed‖ := by
    calc
      1 / (m * (d - c) ^ 2) =
          (1 / (d - c)) * (1 / (m * (d - c))) := by
        field_simp [hm.ne', hdcPos.ne']
      _ ≤ ‖dPhiLin g c d m direction‖ *
          ‖dPhiInvT g c d m completed‖ :=
        mul_le_mul hdirLower hnormalLower (by positivity) (norm_nonneg _)
  have hinner : |inner ℝ direction completed| ≤ 1 := by
    calc
      |inner ℝ direction completed| ≤ ‖direction‖ * ‖completed‖ :=
        abs_real_inner_le_norm direction completed
      _ = 1 := by rw [hdirection, hcompletedUnit, one_mul]
  rw [show pureWZ2NormalizedFrameCompletedNormal
      (g (c + (d - c) / 2)) normal = completed by rfl]
  rw [hidentity, abs_div, abs_of_pos hdenomPos]
  calc
    |inner ℝ direction completed| /
          (‖dPhiLin g c d m direction‖ *
            ‖dPhiInvT g c d m completed‖) ≤
        1 / (1 / (m * (d - c) ^ 2)) := by
      rw [div_le_div_iff₀ hdenomPos (by positivity)]
      calc
        |inner ℝ direction completed| * (1 / (m * (d - c) ^ 2)) ≤
            1 * (1 / (m * (d - c) ^ 2)) :=
          mul_le_mul_of_nonneg_right hinner (by positivity)
        _ = 1 / (m * (d - c) ^ 2) := one_mul _
        _ ≤ ‖dPhiLin g c d m direction‖ *
            ‖dPhiInvT g c d m completed‖ := hdenomLower
        _ = 1 * (‖dPhiLin g c d m direction‖ *
            ‖dPhiInvT g c d m completed‖) := by ring
    _ = m * (d - c) ^ 2 := by
      field_simp [hm.ne', hdcPos.ne']

/-- Nearby-frame version of the completed-normal incidence estimate.  The
quarter-frame gap weakens the inverse-transpose lower bound by a factor two,
which is recorded explicitly in the incidence budget. -/
theorem normalized_dPhi_completed_incidence_le_of_close
    (g : SlopeFunction) {c d m frameSlope : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (hclose : |frameSlope - g (c + (d - c) / 2)| ≤ 1 / 4)
    (direction normal : Point3) (hdirection : ‖direction‖ = 1)
    (hvertical : (1 / 2 : ℝ) ≤ |direction 2|)
    (hnormal : ‖normal‖ = 1) :
    |inner ℝ
        ((‖dPhiLin g c d m direction‖⁻¹ : ℝ) •
          dPhiLin g c d m direction)
        ((‖dPhiInvT g c d m
            (pureWZ2NormalizedFrameCompletedNormal
              frameSlope normal)‖⁻¹ : ℝ) •
          dPhiInvT g c d m
            (pureWZ2NormalizedFrameCompletedNormal
              frameSlope normal))| ≤
      2 * m * (d - c) ^ 2 := by
  let completed := pureWZ2NormalizedFrameCompletedNormal frameSlope normal
  have hdirectionNe : direction ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hdirection
    norm_num at hdirection
  have hcompletedUnit : ‖completed‖ = 1 := by
    exact pureWZ2NormalizedFrameCompletedNormal_unit _ _
  have hcompletedNe : completed ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hcompletedUnit
    norm_num at hcompletedUnit
  have hidentity := incidence_preservation g c d m hcd hm
    direction completed hdirectionNe hcompletedNe
  have hdirLower : 1 / (d - c) ≤ ‖dPhiLin g c d m direction‖ :=
    dPhiLin_norm_lower_of_vertical g hcd direction hvertical
  have hnormalLower : 1 / (2 * (m * (d - c))) ≤
      ‖dPhiInvT g c d m completed‖ := by
    simpa only [completed] using
      dPhiInvT_normalizedFrameCompleted_norm_lower_of_close
        g hcd hm hclose normal hnormal
  have hdcPos : 0 < d - c := sub_pos.mpr hcd
  have hdenomPos : 0 <
      ‖dPhiLin g c d m direction‖ * ‖dPhiInvT g c d m completed‖ := by
    exact mul_pos (lt_of_lt_of_le (by positivity) hdirLower)
      (lt_of_lt_of_le (by positivity) hnormalLower)
  have hdenomLower : 1 / (2 * m * (d - c) ^ 2) ≤
      ‖dPhiLin g c d m direction‖ * ‖dPhiInvT g c d m completed‖ := by
    calc
      1 / (2 * m * (d - c) ^ 2) =
          (1 / (d - c)) * (1 / (2 * (m * (d - c)))) := by
        field_simp [hm.ne', hdcPos.ne']
        <;> ring
      _ ≤ ‖dPhiLin g c d m direction‖ *
          ‖dPhiInvT g c d m completed‖ :=
        mul_le_mul hdirLower hnormalLower (by positivity) (norm_nonneg _)
  have hinner : |inner ℝ direction completed| ≤ 1 := by
    calc
      |inner ℝ direction completed| ≤ ‖direction‖ * ‖completed‖ :=
        abs_real_inner_le_norm direction completed
      _ = 1 := by rw [hdirection, hcompletedUnit, one_mul]
  rw [show pureWZ2NormalizedFrameCompletedNormal frameSlope normal =
      completed by rfl]
  rw [hidentity, abs_div, abs_of_pos hdenomPos]
  calc
    |inner ℝ direction completed| /
          (‖dPhiLin g c d m direction‖ *
            ‖dPhiInvT g c d m completed‖) ≤
        1 / (1 / (2 * m * (d - c) ^ 2)) := by
      rw [div_le_div_iff₀ hdenomPos (by positivity)]
      calc
        |inner ℝ direction completed| *
              (1 / (2 * m * (d - c) ^ 2)) ≤
            1 * (1 / (2 * m * (d - c) ^ 2)) :=
          mul_le_mul_of_nonneg_right hinner (by positivity)
        _ = 1 / (2 * m * (d - c) ^ 2) := one_mul _
        _ ≤ ‖dPhiLin g c d m direction‖ *
            ‖dPhiInvT g c d m completed‖ := hdenomLower
        _ = 1 * (‖dPhiLin g c d m direction‖ *
            ‖dPhiInvT g c d m completed‖) := by ring
    _ = 2 * m * (d - c) ^ 2 := by
      field_simp [hm.ne', hdcPos.ne']
      <;> ring

/-- The completed source field is two-Lipschitz. -/
theorem normalizedFrameCompleted_lipschitz
    {sourceDelta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (frameSlope : ℝ) :
    LipschitzWith 2 (fun point =>
      pureWZ2NormalizedFrameCompletedNormal frameSlope
        (sourceLocal.planeMap point)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm]
  have hcompleted := pureWZ2NormalizedFrameCompletedNormal_sub_norm_le
    frameSlope (sourceLocal.planeMap first) (sourceLocal.planeMap second)
  have hsource := sourceLocal.planeMap_lipschitz.dist_le_mul first second
  rw [dist_eq_norm] at hsource
  calc
    _ ≤ 2 * ‖sourceLocal.planeMap first - sourceLocal.planeMap second‖ :=
      hcompleted
    _ ≤ 2 * dist first second :=
      mul_le_mul_of_nonneg_left (by simpa using hsource) (by norm_num)

/-- After the triangular inverse transpose and normalization, the completed
field remains uniformly Lipschitz; in particular its constant is independent
of the coupled parameter `m`. -/
theorem normalized_dPhiInvT_completed_lipschitz
    {sourceDelta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (hmOne : m ≤ 1)
    (hdc : d - c ≤ 1 / 25) (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1) :
    LipschitzWith 48 (fun point =>
      let completed := pureWZ2NormalizedFrameCompletedNormal
        (g (c + (d - c) / 2)) (sourceLocal.planeMap point)
      (‖dPhiInvT g c d m completed‖⁻¹ : ℝ) •
        dPhiInvT g c d m completed) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm]
  have htransport := normalized_dPhiInvT_completed_sub_norm_le
    g hcd hm hmOne hdc hg hsub
      (sourceLocal.planeMap first) (sourceLocal.planeMap second)
      (sourceLocal.planeMap_unit first) (sourceLocal.planeMap_unit second)
  have hsource := sourceLocal.planeMap_lipschitz.dist_le_mul first second
  rw [dist_eq_norm] at hsource
  calc
    _ ≤ 24 * ‖sourceLocal.planeMap first -
          sourceLocal.planeMap second‖ := htransport
    _ ≤ 24 * dist first second :=
      mul_le_mul_of_nonneg_left (by simpa using hsource) (by norm_num)
    _ ≤ 48 * dist first second := by
      have hdist : 0 ≤ dist first second := dist_nonneg
      nlinarith

/-- On a genuine common rotated-y slice, the completed source normal has the
same paper local-AD bound as the original plane map. -/
theorem completed_common_slice_paper_local_ad
    {sourceDelta sigma rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (frameSlope y0 : ℝ)
    (sourcePoint : {point : Point3 // point ∈ sourceShading.union})
    (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1)
    (hsourceBase : sourceDelta ≤ rho)
    (E : Set Point3) (hEsource : E ⊆ sourceShading.union)
    (hEball : E ⊆ Metric.closedBall (sourcePoint : Point3) (Real.sqrt rho))
    (hEslice : ∀ point ∈ E,
      pureWZ2HorizontalRotation frameSlope point 1 = y0) :
    PureWZ2PaperADSet1
      (scalarProjection
        (pureWZ2NormalizedFrameCompletedNormal frameSlope
          (sourceLocal.planeMap sourcePoint)) E)
      rho (1 - sigma) C := by
  let normal := sourceLocal.planeMap sourcePoint
  let completed := pureWZ2FrameCompletedNormal frameSlope normal
  let a : ℝ := ‖completed‖⁻¹
  have hsource := sourceLocal.local_ad rho hsourceBase hrhoOne sourcePoint
  have hrestricted : PureWZ2PaperADSet1
      (scalarProjection normal E) rho (1 - sigma) C :=
    hsource.weaken_subset (Set.image_mono fun point hpoint =>
      ⟨hEsource hpoint, hEball hpoint⟩)
  have haPos : 0 < a := by
    dsimp only [a]
    exact inv_pos.mpr (norm_pos_iff.mpr
      (pureWZ2FrameCompletedNormal_ne_zero frameSlope normal))
  have haOne : a ≤ 1 := by
    dsimp only [a]
    exact inv_le_one_of_one_le₀
      (pureWZ2FrameCompletedNormal_norm_lower frameSlope normal)
  have haScale : a * rho ≤ rho := by
    exact mul_le_of_le_one_left hrhoPos.le haOne
  rw [scalarProjection_normalizedFrameCompleted_eq_affine
    frameSlope y0 normal E hEslice]
  exact (hrestricted.affine_transfer haPos).weaken_scale hrhoPos haScale

end Kakeya.Assouad

end
