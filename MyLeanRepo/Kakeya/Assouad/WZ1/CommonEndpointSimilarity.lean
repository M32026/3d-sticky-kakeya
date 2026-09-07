import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointParameterBudget

/-!
# Positive similarities for the final common-endpoint reduction
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

private lemma realRpowENN_one (x : ℝ) :
    Kakeya.realRpowENN x 1 = ENNReal.ofReal x := by
  exact congr_arg ENNReal.ofReal (Real.rpow_one x)

/-- A translated positive homothety of the plane. -/
def wz1PositiveSimilarity
    (center : Point2) (scale : ℝ) (point : Point2) : Point2 :=
  scale • (point - center)

/-- Its explicit inverse. -/
def wz1PositiveSimilarityInv
    (center : Point2) (scale : ℝ) (point : Point2) : Point2 :=
  scale⁻¹ • point + center

lemma wz1PositiveSimilarity_dist
    {center : Point2} {scale : ℝ} (hscale : 0 < scale)
    (first second : Point2) :
    dist (wz1PositiveSimilarity center scale first)
        (wz1PositiveSimilarity center scale second) =
      scale * dist first second := by
  have hdiff :
      wz1PositiveSimilarity center scale first -
          wz1PositiveSimilarity center scale second =
        scale • (first - second) := by
    simp [wz1PositiveSimilarity, smul_sub]
  rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
  rw [dist_eq_norm]

lemma wz1PositiveSimilarity_injective
    {center : Point2} {scale : ℝ} (hscale : 0 < scale) :
    Function.Injective (wz1PositiveSimilarity center scale) := by
  intro first second heq
  have hdist :
      scale * dist first second = 0 := by
    rw [← wz1PositiveSimilarity_dist hscale first second, heq, dist_self]
  exact dist_eq_zero.mp
    ((mul_eq_zero.mp hdist).resolve_left hscale.ne')

@[simp] lemma wz1PositiveSimilarityInv_apply
    {center : Point2} {scale : ℝ} (hscale : 0 < scale)
    (point : Point2) :
    wz1PositiveSimilarityInv center scale
        (wz1PositiveSimilarity center scale point) = point := by
  simp [wz1PositiveSimilarityInv, wz1PositiveSimilarity,
    smul_smul, hscale.ne']

@[simp] lemma wz1PositiveSimilarity_apply_inv
    {center : Point2} {scale : ℝ} (hscale : 0 < scale)
    (point : Point2) :
    wz1PositiveSimilarity center scale
        (wz1PositiveSimilarityInv center scale point) = point := by
  have hcancel : scale * scale⁻¹ = 1 := by
    field_simp [hscale.ne']
  simp [wz1PositiveSimilarityInv, wz1PositiveSimilarity,
    smul_smul, hcancel]

lemma wz1PositiveSimilarity_image_card
    {center : Point2} {scale : ℝ} (hscale : 0 < scale)
    (A : DiscreteSet 2) :
    (A.image (wz1PositiveSimilarity center scale)).card = A.card :=
  Finset.card_image_of_injective _
    (wz1PositiveSimilarity_injective hscale)

lemma wz1PositiveSimilarity_image_enncard
    {center : Point2} {scale : ℝ} (hscale : 0 < scale)
    (A : DiscreteSet 2) :
    DiscreteSet.enncard
        (A.image (wz1PositiveSimilarity center scale)) = A.enncard := by
  simp [DiscreteSet.enncard, wz1PositiveSimilarity_image_card hscale A]

lemma wz1PositiveSimilarity_ballCount
    {center : Point2} {scale : ℝ} (hscale : 0 < scale)
    (A : DiscreteSet 2) (point : Point2) (radius : ℝ) :
    DiscreteSet.ballCount
        (A.image (wz1PositiveSimilarity center scale)) point radius =
      A.ballCount (wz1PositiveSimilarityInv center scale point)
        (radius / scale) := by
  let map := wz1PositiveSimilarity center scale
  let inv := wz1PositiveSimilarityInv center scale
  have hfilter :
      (A.image map).filter (fun image => dist image point ≤ radius) =
        (A.filter fun source =>
          dist source (inv point) ≤ radius / scale).image map := by
    ext image
    constructor
    · intro himage
      rcases Finset.mem_filter.mp himage with ⟨hmem, hdist⟩
      rcases Finset.mem_image.mp hmem with ⟨source, hsource, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨source, Finset.mem_filter.mpr ⟨hsource, ?_⟩, rfl⟩
      have heq : map (inv point) = point := by
        exact wz1PositiveSimilarity_apply_inv hscale point
      rw [← heq, wz1PositiveSimilarity_dist hscale] at hdist
      exact (le_div_iff₀ hscale).2 (by simpa [mul_comm] using hdist)
    · intro himage
      rcases Finset.mem_image.mp himage with ⟨source, hsource, rfl⟩
      have hmem := (Finset.mem_filter.mp hsource).1
      have hdist := (Finset.mem_filter.mp hsource).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨source, hmem, rfl⟩, ?_⟩
      have heq : map (inv point) = point := by
        exact wz1PositiveSimilarity_apply_inv hscale point
      rw [← heq, wz1PositiveSimilarity_dist hscale]
      simpa [mul_comm] using (le_div_iff₀ hscale).1 hdist
  simp only [DiscreteSet.ballCount]
  rw [hfilter, Finset.card_image_of_injective _
    (wz1PositiveSimilarity_injective hscale)]

/-- A subset of a delta-separated set is delta-separated. -/
lemma DiscreteSet.IsDeltaSeparated.mono
    {A B : DiscreteSet 2} {delta : ℝ}
    (hA : A.IsDeltaSeparated delta) (hsub : B ⊆ A) :
    B.IsDeltaSeparated delta := by
  intro first hfirst second hsecond hne
  exact hA (hsub hfirst) (hsub hsecond) hne

/-- A subset of a Katz--Tao set retains the absolute bound. -/
lemma DiscreteSet.IsKatzTao.mono_set
    {A B : DiscreteSet 2} {delta exponent : ℝ} {C : ENNReal}
    (hA : A.IsKatzTao delta exponent C) (hsub : B ⊆ A) :
    B.IsKatzTao delta exponent C := by
  intro center radius hdeltaRadius hradiusOne
  calc
    B.ballCount center radius ≤ A.ballCount center radius := by
      simp only [DiscreteSet.ballCount]
      exact_mod_cast Finset.card_le_card
        (Finset.filter_subset_filter
          (fun point => dist point center ≤ radius) hsub)
    _ ≤ C * Kakeya.realRpowENN (radius / delta) exponent :=
      hA center radius hdeltaRadius hradiusOne

/-- A delta-separated set has at most one point in a ball of diameter
strictly below delta. -/
lemma separated_ballCount_le_one
    {A : DiscreteSet 2} {delta radius : ℝ}
    (hsep : A.IsDeltaSeparated delta)
    (hdiameter : 2 * radius < delta) (center : Point2) :
    A.ballCount center radius ≤ 1 := by
  change ((A.filter fun point => dist point center ≤ radius).card : ENNReal) ≤ 1
  norm_cast
  rw [Finset.card_le_one]
  intro first hfirst second hsecond
  have hfirstA := (Finset.mem_filter.mp hfirst).1
  have hsecondA := (Finset.mem_filter.mp hsecond).1
  by_contra hne
  have hsep' := hsep hfirstA hsecondA hne
  have htriangle :
      dist first second ≤ dist first center + dist center second :=
    dist_triangle first center second
  have hfirstBall := (Finset.mem_filter.mp hfirst).2
  have hsecondBall := (Finset.mem_filter.mp hsecond).2
  have hsecondBall' : dist center second ≤ radius := by
    simpa [dist_comm] using hsecondBall
  linarith

/-- A positive similarity with scale at least one half sends a unit-ball
one-dimensional Katz--Tao set at scale `delta` to a Katz--Tao set at the
common smaller scale `delta/2`, without changing its constant. -/
theorem DiscreteSet.IsKatzTao.image_positiveSimilarity_halfScale
    {A : DiscreteSet 2} {delta scale : ℝ} {C : ENNReal}
    {center : Point2}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hscale : 0 < scale) (hscaleHalf : 1 / 2 ≤ scale)
    (hC : 1 ≤ C)
    (hunit : A.IsInUnitBall)
    (hsep : A.IsDeltaSeparated delta)
    (hKT : A.IsKatzTao delta 1 C) :
    DiscreteSet.IsKatzTao
      (A.image (wz1PositiveSimilarity center scale))
      (delta / 2) 1 C := by
  intro imageCenter radius hhalfRadius hradiusOne
  have hradius : 0 < radius := (by linarith : 0 < delta / 2).trans_le hhalfRadius
  rw [wz1PositiveSimilarity_ballCount hscale]
  let sourceCenter := wz1PositiveSimilarityInv center scale imageCenter
  let sourceRadius := radius / scale
  by_cases hsourceLower : delta ≤ sourceRadius
  · by_cases hsourceUpper : sourceRadius ≤ 1
    · have hraw := hKT sourceCenter sourceRadius hsourceLower hsourceUpper
      have hratio : sourceRadius / delta ≤ radius / (delta / 2) := by
        dsimp only [sourceRadius]
        have hscaleInv : scale⁻¹ ≤ 2 := by
          have h := one_div_le_one_div_of_le
            (by norm_num : 0 < (1 / 2 : ℝ)) hscaleHalf
          norm_num at h
          simpa [one_div] using h
        have hdeltaPos : 0 < delta := hdelta
        calc
          radius / scale / delta = radius * scale⁻¹ / delta := by ring
          _ ≤ radius * 2 / delta := by gcongr
          _ = radius / (delta / 2) := by field_simp [hdelta.ne'] <;> ring
      calc
        A.ballCount sourceCenter sourceRadius
            ≤ C * Kakeya.realRpowENN (sourceRadius / delta) 1 := hraw
        _ ≤ C * Kakeya.realRpowENN (radius / (delta / 2)) 1 := by
          gcongr
          rw [realRpowENN_one, realRpowENN_one]
          exact ENNReal.ofReal_mono hratio
    · have hsourceLarge : 1 < sourceRadius := lt_of_not_ge hsourceUpper
      have htotal :
          A.enncard ≤ C * Kakeya.realRpowENN (1 / delta) 1 :=
        katzTao_unit_ball_card hdelta hdeltaOne hunit hKT
      have honeRatio : 1 / delta ≤ radius / (delta / 2) := by
        have hradiusScale : scale < radius := by
          simpa using (lt_div_iff₀ hscale).1 hsourceLarge
        have hradiusHalf : 1 / 2 < radius := hscaleHalf.trans_lt hradiusScale
        have htwoRadius : 1 ≤ 2 * radius := by linarith
        calc
          1 / delta ≤ (2 * radius) / delta :=
            (div_le_div_iff_of_pos_right hdelta).2 htwoRadius
          _ = radius / (delta / 2) := by
            field_simp [hdelta.ne'] <;> ring
      calc
        A.ballCount sourceCenter sourceRadius ≤ A.enncard := by
          change ((A.filter fun point =>
            dist point sourceCenter ≤ sourceRadius).card : ENNReal) ≤
              (A.card : ENNReal)
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ C * Kakeya.realRpowENN (1 / delta) 1 := htotal
        _ ≤ C * Kakeya.realRpowENN (radius / (delta / 2)) 1 := by
          gcongr
          rw [realRpowENN_one, realRpowENN_one]
          exact ENNReal.ofReal_mono honeRatio
  · have hsourceSmall : sourceRadius < delta := lt_of_not_ge hsourceLower
    have hraw := hKT sourceCenter delta (le_rfl) hdeltaOne
    have hballMono :
        A.ballCount sourceCenter sourceRadius ≤ A.ballCount sourceCenter delta := by
      change
        ((A.filter fun point =>
          dist point sourceCenter ≤ sourceRadius).card : ENNReal) ≤
        ((A.filter fun point =>
          dist point sourceCenter ≤ delta).card : ENNReal)
      exact_mod_cast Finset.card_le_card <| by
        intro point hpoint
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hpoint).1,
            (Finset.mem_filter.mp hpoint).2.trans hsourceSmall.le⟩
    have hratioTwo : 1 ≤ radius / (delta / 2) := by
      apply (le_div_iff₀ (by linarith : 0 < delta / 2)).2
      simpa using hhalfRadius
    calc
      A.ballCount sourceCenter sourceRadius ≤ A.ballCount sourceCenter delta := hballMono
      _ ≤ C * Kakeya.realRpowENN (delta / delta) 1 := hraw
      _ = C := by simp [Kakeya.realRpowENN, hdelta.ne']
      _ ≤ C * Kakeya.realRpowENN (radius / (delta / 2)) 1 := by
        have : (1 : ENNReal) ≤
            Kakeya.realRpowENN (radius / (delta / 2)) 1 := by
          simp [Kakeya.realRpowENN, Real.rpow_one, hratioTwo]
        simpa using mul_le_mul_left' this C

end

end Kakeya.Assouad
