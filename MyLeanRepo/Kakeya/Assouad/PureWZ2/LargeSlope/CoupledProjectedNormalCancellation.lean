import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FrameProjectedNormalLipschitz
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer

/-!
# Cancellation of the coupled transverse scale on projected normals

The inverse transpose of the Section-6 triangular map contains a formally
large `1 / m` term.  On the fixed-frame projected normal used by the faithful
prism argument, its numerator is exactly zero.  This is the algebraic reason
that choosing `m = slopeScale / lambda` does not create a circular local-normal
budget after the final similarity.
-/

noncomputable section

namespace Kakeya.Assouad

/-- If a normal has zero second coordinate in the horizontal frame at the
midpoint slope, the dangerous second coordinate of `DΦ⁻ᵀ` vanishes exactly. -/
theorem dPhiInvT_coord_one_eq_zero_of_rotated_y_zero
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (normal : Point3)
    (hrotated : pureWZ2HorizontalRotation
      (g (c + (d - c) / 2)) normal 1 = 0) :
    dPhiInvT g c d m normal 1 = 0 := by
  have hhorizontal :
      -g (c + (d - c) / 2) * normal 0 + normal 1 = 0 := by
    rw [pureWZ2HorizontalRotation_coord_one] at hrotated
    have hnorm : pureWZ2HorizontalNorm
        (g (c + (d - c) / 2)) ≠ 0 :=
      (pureWZ2HorizontalNorm_pos _).ne'
    rcases div_eq_zero_iff.mp hrotated with hzero | hzero
    · simpa only [neg_mul] using hzero
    · exact (hnorm hzero).elim
  let denominator := m * (d - c) / 2
  have hvalue : dPhiInvT g c d m normal = point3
      (normal 0)
      ((-g (c + (d - c) / 2) * normal 0 + normal 1) / denominator)
      (normal 2 / (2 / (d - c))) := by
    ext coordinate
    fin_cases coordinate <;> simp [dPhiInvT, denominator, point3] <;> ring
  rw [hvalue]
  simpa [point3] using (show
    (-g (c + (d - c) / 2) * normal 0 + normal 1) / denominator = 0
      from div_eq_zero_iff.mpr (Or.inl hhorizontal))

/-- The inverse-transpose image of the canonical projected normal is
independent of the transverse scale `m`. -/
theorem dPhiInvT_normalizedFrameProjected_eq
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (normal : Point3) :
    dPhiInvT g c d m
        (pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) normal) =
      point3
        ((pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) normal) 0)
        0
        ((pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) normal) 2 /
            (2 / (d - c))) := by
  let projected := pureWZ2NormalizedFrameProjectedNormal
    (g (c + (d - c) / 2)) normal
  have hrotated : pureWZ2HorizontalRotation
      (g (c + (d - c) / 2)) projected 1 = 0 := by
    exact pureWZ2FrameProjectedNormal_rotated_y_zero _ _
  ext coordinate
  fin_cases coordinate
  · simp [dPhiInvT, projected, point3]
  · have hy := dPhiInvT_coord_one_eq_zero_of_rotated_y_zero
      g hcd hm projected hrotated
    simpa [projected, point3] using hy
  · simp [dPhiInvT, projected, point3]

/-- Consequently the normalized transported projected normal is literally
unchanged when the coupled transverse parameter is changed. -/
theorem normalized_dPhiInvT_projected_independent_of_scale
    (g : SlopeFunction) {c d firstScale secondScale : ℝ}
    (hcd : c < d) (hfirst : 0 < firstScale) (hsecond : 0 < secondScale)
    (normal : Point3) :
    let projected := pureWZ2NormalizedFrameProjectedNormal
      (g (c + (d - c) / 2)) normal
    (‖dPhiInvT g c d firstScale projected‖⁻¹ : ℝ) •
        dPhiInvT g c d firstScale projected =
      (‖dPhiInvT g c d secondScale projected‖⁻¹ : ℝ) •
        dPhiInvT g c d secondScale projected := by
  dsimp only
  rw [dPhiInvT_normalizedFrameProjected_eq g hcd hfirst normal,
    dPhiInvT_normalizedFrameProjected_eq g hcd hsecond normal]

/-- The projected-normal transport is also quantitatively stable: after the
dangerous transverse coordinate cancels, only the vertical contraction
`(d-c)/2` remains, so the unnormalized transport is nonexpanding. -/
theorem dPhiInvT_normalizedFrameProjected_sub_norm_le
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (hdc : d - c ≤ 2)
    (first second : Point3) :
    ‖dPhiInvT g c d m
          (pureWZ2NormalizedFrameProjectedNormal
            (g (c + (d - c) / 2)) first) -
        dPhiInvT g c d m
          (pureWZ2NormalizedFrameProjectedNormal
            (g (c + (d - c) / 2)) second)‖ ≤
      ‖pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) first -
        pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) second‖ := by
  let firstProjected := pureWZ2NormalizedFrameProjectedNormal
    (g (c + (d - c) / 2)) first
  let secondProjected := pureWZ2NormalizedFrameProjectedNormal
    (g (c + (d - c) / 2)) second
  rw [dPhiInvT_normalizedFrameProjected_eq g hcd hm first,
    dPhiInvT_normalizedFrameProjected_eq g hcd hm second]
  have hfactor : 0 ≤ (d - c) / 2 ∧ (d - c) / 2 ≤ 1 := by
    constructor <;> linarith
  have hsourceSq := point3_coord_norm_sq (firstProjected - secondProjected)
  have htargetSq := point3_coord_norm_sq
    (point3 (firstProjected 0) 0 (firstProjected 2 / (2 / (d - c))) -
      point3 (secondProjected 0) 0 (secondProjected 2 / (2 / (d - c))))
  have hdenom : 2 / (d - c) ≠ 0 :=
    div_ne_zero (by norm_num) (sub_ne_zero.mpr hcd.ne')
  have htwo :
      (firstProjected 2 / (2 / (d - c)) -
          secondProjected 2 / (2 / (d - c))) =
        ((d - c) / 2) * (firstProjected 2 - secondProjected 2) := by
    field_simp [hdenom, sub_ne_zero.mpr hcd.ne']
  have hfirstPoint : ∀ i : Fin 3,
      point3 (firstProjected 0) 0
          (firstProjected 2 / (2 / (d - c))) i =
        if i = 0 then firstProjected 0 else
          if i = 1 then 0 else firstProjected 2 / (2 / (d - c)) := by
    intro i
    fin_cases i <;> simp [point3]
  have hsecondPoint : ∀ i : Fin 3,
      point3 (secondProjected 0) 0
          (secondProjected 2 / (2 / (d - c))) i =
        if i = 0 then secondProjected 0 else
          if i = 1 then 0 else secondProjected 2 / (2 / (d - c)) := by
    intro i
    fin_cases i <;> simp [point3]
  have htargetSqLe :
      ‖point3 (firstProjected 0) 0
            (firstProjected 2 / (2 / (d - c))) -
          point3 (secondProjected 0) 0
            (secondProjected 2 / (2 / (d - c)))‖ ^ 2 ≤
        ‖firstProjected - secondProjected‖ ^ 2 := by
    rw [htargetSq, hsourceSq]
    simp [hfirstPoint, hsecondPoint, point3, PiLp.sub_apply]
    rw [htwo]
    have hz : (((d - c) / 2) *
          (firstProjected 2 - secondProjected 2)) ^ 2 ≤
        (firstProjected 2 - secondProjected 2) ^ 2 := by
      have hfactorAbs : |(d - c) / 2| ≤ 1 := by
        rw [abs_of_nonneg hfactor.1]
        exact hfactor.2
      have habs :
          |(d - c) / 2 * (firstProjected 2 - secondProjected 2)| ≤
            |firstProjected 2 - secondProjected 2| := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) hfactorAbs
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 habs
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp htargetSqLe

/-- A lower bound for one source-frame coordinate survives the inverse
transpose unchanged.  This auxiliary lemma is useful when a caller has a
coordinate-level compatibility certificate. -/
theorem dPhiInvT_normalizedFrameProjected_norm_lower
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (normal : Point3)
    (hfirst : (1 / 16 : ℝ) ≤
      |(pureWZ2NormalizedFrameProjectedNormal
        (g (c + (d - c) / 2)) normal) 0|) :
    (1 / 16 : ℝ) ≤
      ‖dPhiInvT g c d m
        (pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) normal)‖ := by
  let projected := pureWZ2NormalizedFrameProjectedNormal
    (g (c + (d - c) / 2)) normal
  have hcoordinate := PiLp.norm_apply_le
    (dPhiInvT g c d m projected) (0 : Fin 3)
  have hcoordinateEq : dPhiInvT g c d m projected 0 = projected 0 := by
    simp [dPhiInvT, point3]
  rw [hcoordinateEq] at hcoordinate
  exact hfirst.trans (by
    simpa only [Real.norm_eq_abs, projected] using hcoordinate)

/-- If the projected normal is a unit vector and the fixed frame has bounded
slope, its inverse-transpose image has norm at least half the selected height
length.  Unlike a whole-space operator-norm bound, this estimate has no
dependence on the transverse parameter `m`. -/
theorem dPhiInvT_normalizedFrameProjected_norm_lower_of_unit
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (hdc : d - c ≤ 1)
    (hframe : |g (c + (d - c) / 2)| ≤ 1) (normal : Point3)
    (hunit : ‖pureWZ2NormalizedFrameProjectedNormal
      (g (c + (d - c) / 2)) normal‖ = 1) :
    (d - c) / 2 ≤
      ‖dPhiInvT g c d m
        (pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) normal)‖ := by
  let frameSlope := g (c + (d - c) / 2)
  let projected := pureWZ2NormalizedFrameProjectedNormal frameSlope normal
  let heightFactor := (d - c) / 2
  have hheightPos : 0 < heightFactor := by
    dsimp only [heightFactor]
    linarith
  have hheightLe : heightFactor ≤ 1 / 2 := by
    dsimp only [heightFactor]
    linarith
  have hframeSq : frameSlope ^ 2 ≤ 1 := by
    dsimp only [frameSlope]
    nlinarith [sq_abs (g (c + (d - c) / 2)), abs_nonneg
      (g (c + (d - c) / 2))]
  have hrotated : pureWZ2HorizontalRotation frameSlope projected 1 = 0 := by
    exact pureWZ2FrameProjectedNormal_rotated_y_zero _ _
  have hhorizontal : -frameSlope * projected 0 + projected 1 = 0 := by
    rw [pureWZ2HorizontalRotation_coord_one] at hrotated
    have hnorm : pureWZ2HorizontalNorm frameSlope ≠ 0 :=
      (pureWZ2HorizontalNorm_pos _).ne'
    rcases div_eq_zero_iff.mp hrotated with hzero | hzero
    · exact hzero
    · exact (hnorm hzero).elim
  have hy : projected 1 = frameSlope * projected 0 := by
    linarith
  have hsourceSq := point3_coord_norm_sq projected
  have hsourceUnit : ‖projected‖ = 1 := by
    simpa only [projected, frameSlope] using hunit
  rw [hsourceUnit] at hsourceSq
  have htargetEq := dPhiInvT_normalizedFrameProjected_eq
    g hcd hm normal
  change dPhiInvT g c d m projected =
      point3 (projected 0) 0 (projected 2 / (2 / (d - c))) at htargetEq
  have hdenom : 2 / (d - c) ≠ 0 :=
    div_ne_zero (by norm_num) (sub_ne_zero.mpr hcd.ne')
  have htwo : projected 2 / (2 / (d - c)) =
      heightFactor * projected 2 := by
    dsimp only [heightFactor]
    field_simp [hdenom, sub_ne_zero.mpr hcd.ne']
  have hcoefficient : heightFactor ^ 2 * (1 + frameSlope ^ 2) ≤ 1 := by
    have hheightSq : heightFactor ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg heightFactor]
    nlinarith [sq_nonneg heightFactor, sq_nonneg frameSlope]
  have hcoefficientX := mul_le_mul_of_nonneg_right hcoefficient
    (sq_nonneg (projected 0))
  have hcoordZero :
      point3 (projected 0) 0 (heightFactor * projected 2) 0 = projected 0 := by
    simp [point3]
  have hcoordOne :
      point3 (projected 0) 0 (heightFactor * projected 2) 1 = 0 := by
    simp [point3]
  have hcoordTwo :
      point3 (projected 0) 0 (heightFactor * projected 2) 2 =
        heightFactor * projected 2 := by
    simp [point3]
  have hlowerSq : heightFactor ^ 2 ≤
      ‖dPhiInvT g c d m projected‖ ^ 2 := by
    rw [htargetEq, point3_coord_norm_sq]
    rw [htwo, hcoordZero, hcoordOne, hcoordTwo]
    rw [hy] at hsourceSq
    nlinarith [sq_nonneg (projected 0), sq_nonneg (projected 2),
      sq_nonneg heightFactor, sq_nonneg frameSlope]
  exact (sq_le_sq₀ hheightPos.le
    (norm_nonneg (dPhiInvT g c d m projected))).mp hlowerSq

/-- Normalizing the transported unit projected normals costs only the inverse
selected height length.  In particular, the bound is independent of `m`. -/
theorem normalized_dPhiInvT_projected_sub_norm_le_of_unit
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (hdc : d - c ≤ 1)
    (hframe : |g (c + (d - c) / 2)| ≤ 1)
    (first second : Point3)
    (hfirstUnit : ‖pureWZ2NormalizedFrameProjectedNormal
      (g (c + (d - c) / 2)) first‖ = 1)
    (hsecondUnit : ‖pureWZ2NormalizedFrameProjectedNormal
      (g (c + (d - c) / 2)) second‖ = 1) :
    let firstProjected := pureWZ2NormalizedFrameProjectedNormal
      (g (c + (d - c) / 2)) first
    let secondProjected := pureWZ2NormalizedFrameProjectedNormal
      (g (c + (d - c) / 2)) second
    ‖(‖dPhiInvT g c d m firstProjected‖⁻¹ : ℝ) •
          dPhiInvT g c d m firstProjected -
        (‖dPhiInvT g c d m secondProjected‖⁻¹ : ℝ) •
          dPhiInvT g c d m secondProjected‖ ≤
      (4 / (d - c)) * ‖firstProjected - secondProjected‖ := by
  dsimp only
  let firstProjected := pureWZ2NormalizedFrameProjectedNormal
    (g (c + (d - c) / 2)) first
  let secondProjected := pureWZ2NormalizedFrameProjectedNormal
    (g (c + (d - c) / 2)) second
  have hheightPos : 0 < (d - c) / 2 := by linarith
  have hfirstLower : (d - c) / 2 ≤
      ‖dPhiInvT g c d m firstProjected‖ := by
    exact dPhiInvT_normalizedFrameProjected_norm_lower_of_unit
      g hcd hm hdc hframe first hfirstUnit
  have hsecondLower : (d - c) / 2 ≤
      ‖dPhiInvT g c d m secondProjected‖ := by
    exact dPhiInvT_normalizedFrameProjected_norm_lower_of_unit
      g hcd hm hdc hframe second hsecondUnit
  have hnormalize := normalization_lipschitz hheightPos
    hfirstLower hsecondLower
  have hmap := dPhiInvT_normalizedFrameProjected_sub_norm_le
    g hcd hm (hdc.trans (by norm_num)) first second
  change ‖dPhiInvT g c d m firstProjected -
      dPhiInvT g c d m secondProjected‖ ≤
    ‖firstProjected - secondProjected‖ at hmap
  have hcoefficient : 2 / ((d - c) / 2) = 4 / (d - c) := by
    field_simp [sub_ne_zero.mpr hcd.ne'] <;> norm_num
  rw [hcoefficient] at hnormalize
  exact hnormalize.trans (mul_le_mul_of_nonneg_left hmap (by positivity))

/-- Composing the preceding transport estimate with the fixed-frame
projected-normal field gives a `128 / (d-c)` Lipschitz bound.  The constant
depends on the selected height interval, as it must, but not on the coupled
transverse scale `m`. -/
theorem normalized_dPhiInvT_projected_lipschitz_of_unit
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData shading sigma C)
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (hdc : d - c ≤ 1)
    (hframe : |g (c + (d - c) / 2)| ≤ 1)
    (hprojected : LipschitzWith 32
      (fun point => pureWZ2NormalizedFrameProjectedNormal
        (g (c + (d - c) / 2)) (sourceLocal.planeMap point)))
    (hunit : ∀ point, ‖pureWZ2NormalizedFrameProjectedNormal
      (g (c + (d - c) / 2)) (sourceLocal.planeMap point)‖ = 1) :
    LipschitzWith (⟨128 / (d - c), by positivity⟩ : NNReal)
      (fun point =>
        let projected := pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) (sourceLocal.planeMap point)
        (‖dPhiInvT g c d m projected‖⁻¹ : ℝ) •
          dPhiInvT g c d m projected) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm]
  have htransport := normalized_dPhiInvT_projected_sub_norm_le_of_unit
    g hcd hm hdc hframe (sourceLocal.planeMap first)
      (sourceLocal.planeMap second) (hunit first) (hunit second)
  have hsource := hprojected.dist_le_mul first second
  rw [dist_eq_norm] at hsource
  calc
    _ ≤ (4 / (d - c)) *
        ‖pureWZ2NormalizedFrameProjectedNormal
            (g (c + (d - c) / 2)) (sourceLocal.planeMap first) -
          pureWZ2NormalizedFrameProjectedNormal
            (g (c + (d - c) / 2)) (sourceLocal.planeMap second)‖ :=
      htransport
    _ ≤ (4 / (d - c)) * (32 * dist first second) := by
      exact mul_le_mul_of_nonneg_left (by simpa using hsource) (by positivity)
    _ = ((⟨128 / (d - c), by positivity⟩ : NNReal) : ℝ) *
        dist first second := by
      change (4 / (d - c)) * (32 * dist first second) =
        (128 / (d - c)) * dist first second
      ring

/-- A fixed positive lower bound on the first coordinate also makes the
normalization of the transported projected field uniformly Lipschitz.  The
constant has no dependence on the transverse scale `m`. -/
theorem normalized_dPhiInvT_projected_sub_norm_le
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (hdc : d - c ≤ 2)
    (first second : Point3)
    (hfirst : (1 / 16 : ℝ) ≤
      |(pureWZ2NormalizedFrameProjectedNormal
        (g (c + (d - c) / 2)) first) 0|)
    (hsecond : (1 / 16 : ℝ) ≤
      |(pureWZ2NormalizedFrameProjectedNormal
        (g (c + (d - c) / 2)) second) 0|) :
    let firstProjected := pureWZ2NormalizedFrameProjectedNormal
      (g (c + (d - c) / 2)) first
    let secondProjected := pureWZ2NormalizedFrameProjectedNormal
      (g (c + (d - c) / 2)) second
    ‖(‖dPhiInvT g c d m firstProjected‖⁻¹ : ℝ) •
          dPhiInvT g c d m firstProjected -
        (‖dPhiInvT g c d m secondProjected‖⁻¹ : ℝ) •
          dPhiInvT g c d m secondProjected‖ ≤
      32 * ‖firstProjected - secondProjected‖ := by
  dsimp only
  let firstProjected := pureWZ2NormalizedFrameProjectedNormal
    (g (c + (d - c) / 2)) first
  let secondProjected := pureWZ2NormalizedFrameProjectedNormal
    (g (c + (d - c) / 2)) second
  have hfirstNorm : (1 / 16 : ℝ) ≤
      ‖dPhiInvT g c d m firstProjected‖ :=
    dPhiInvT_normalizedFrameProjected_norm_lower g hcd hm first hfirst
  have hsecondNorm : (1 / 16 : ℝ) ≤
      ‖dPhiInvT g c d m secondProjected‖ :=
    dPhiInvT_normalizedFrameProjected_norm_lower g hcd hm second hsecond
  have hnormalize := normalization_lipschitz
    (m := (1 / 16 : ℝ)) (by norm_num) hfirstNorm hsecondNorm
  have hmap := dPhiInvT_normalizedFrameProjected_sub_norm_le
    g hcd hm hdc first second
  change ‖dPhiInvT g c d m firstProjected -
      dPhiInvT g c d m secondProjected‖ ≤
    ‖firstProjected - secondProjected‖ at hmap
  calc
    _ ≤ (2 / (1 / 16 : ℝ)) *
        ‖dPhiInvT g c d m firstProjected -
          dPhiInvT g c d m secondProjected‖ := hnormalize
    _ ≤ 32 * ‖firstProjected - secondProjected‖ := by
      norm_num only [div_eq_mul_inv, inv_div, one_div] at *
      exact mul_le_mul_of_nonneg_left hmap (by norm_num : (0 : ℝ) ≤ 32)

/-- The full projected-normal transport, from the original unit normal to the
normalized target normal, is uniformly `1024`-Lipschitz and independent of
the coupled transverse scale. -/
theorem normalized_dPhiInvT_projected_lipschitz
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData shading sigma C)
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (hdc : d - c ≤ 2)
    (hprojected : LipschitzWith 32
      (fun point => pureWZ2NormalizedFrameProjectedNormal
        (g (c + (d - c) / 2)) (sourceLocal.planeMap point)))
    (hfirst : ∀ point, (1 / 16 : ℝ) ≤
      |(pureWZ2NormalizedFrameProjectedNormal
        (g (c + (d - c) / 2)) (sourceLocal.planeMap point)) 0|) :
    LipschitzWith 1024
      (fun point =>
        let projected := pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) (sourceLocal.planeMap point)
        (‖dPhiInvT g c d m projected‖⁻¹ : ℝ) •
          dPhiInvT g c d m projected) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm]
  have htransport := normalized_dPhiInvT_projected_sub_norm_le
    g hcd hm hdc (sourceLocal.planeMap first)
      (sourceLocal.planeMap second) (hfirst first) (hfirst second)
  have hsource := hprojected.dist_le_mul first second
  rw [dist_eq_norm] at hsource
  calc
    _ ≤ 32 * ‖pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) (sourceLocal.planeMap first) -
        pureWZ2NormalizedFrameProjectedNormal
          (g (c + (d - c) / 2)) (sourceLocal.planeMap second)‖ := htransport
    _ ≤ 32 * (32 * dist first second) := by
      exact mul_le_mul_of_nonneg_left (by simpa using hsource) (by norm_num)
    _ = (1024 : NNReal) * dist first second := by
      change (32 : ℝ) * (32 * dist first second) = 1024 * dist first second
      ring

end Kakeya.Assouad

end
