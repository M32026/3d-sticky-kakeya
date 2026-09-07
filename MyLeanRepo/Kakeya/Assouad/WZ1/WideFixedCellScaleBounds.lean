import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellNormalizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCenter
import MyLeanRepo.Kakeya.Assouad.WZ1.AffineNormalization

/-!
# Scale choices and geometric bounds for wide fixed cell normalization

Given `fixed : WZ1Proposition8_9WideFixedCellData coarse`, defines:
- `firstScale := min 5 (1 / (‖fixed.centerF‖ + 1 / 100))`
- `endpointScale := min 5 (1 / (1 / 100 + dist fixed.centerG₁ fixed.centerG₂ / 2))`
- `endpointTranslation := -(1/2 : ℝ) • (endpointScale • (centerG₁ + centerG₂))`

Proves all scale bounds, unit ball containment, and standard separation.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal
open Classical

variable {delta epsilon eta : ℝ}
variable {parameters : WZ1Proposition8_9Parameters epsilon}
variable {F G₁ G₂ : DiscreteSet 2}
variable {H : Finset (Point2 × Point2 × Point2)}
variable {data : WZ1Proposition8_9CommonStripData delta epsilon eta parameters F G₁ G₂ H}
variable {coarse : WZ1Proposition8_9WideCoarseData delta epsilon eta parameters F G₁ G₂ H data}
variable (fixed : WZ1Proposition8_9WideFixedCellData coarse)

namespace WideFixedCellScaleBounds

/-- `centerF` is within 1/100 of a point in `coarseF` bounded by 3, so ‖centerF‖ ≤ 3 + 1/100. -/
lemma centerF_norm_upper : ‖fixed.centerF‖ ≤ 3 + 1 / 100 := by
  rcases fixed.cellF_nonempty with ⟨p, hp⟩
  have h1 : p ∈ fixed.ambientCellF := fixed.cellF_subset hp
  have h2 : p ∈ coarse.coarseF := by
    rw [fixed.ambientCellF_eq] at h1
    exact (Finset.mem_filter.mp h1).1
  have h3 : dist p 0 ≤ 3 := coarse.coarseF_bounded p h2
  have h4 : gridCenter (1 / 100) p = fixed.centerF := by
    rw [fixed.ambientCellF_eq] at h1
    exact (Finset.mem_filter.mp h1).2
  have h5 : dist p (gridCenter (1 / 100) p) ≤ 1 / 100 :=
    gridCenter_rho_close (1 / 100) (by norm_num) p
  rw [h4] at h5
  have h6 : dist fixed.centerF 0 ≤ dist fixed.centerF p + dist p 0 := dist_triangle _ _ _
  have h7 : dist fixed.centerF p = dist p fixed.centerF := dist_comm _ _
  rw [h7] at h6
  have h8 : ‖fixed.centerF‖ = dist fixed.centerF 0 := by rw [dist_eq_norm] <;> simp
  rw [h8]
  linarith

/-- `centerG₁` is bounded by 3 + 1/100. -/
lemma centerG₁_norm_upper : ‖fixed.centerG₁‖ ≤ 3 + 1 / 100 := by
  rcases fixed.cellG₁_nonempty with ⟨p, hp⟩
  have h1 : p ∈ fixed.ambientCellG₁ := fixed.cellG₁_subset hp
  have h2 : p ∈ coarse.coarseG₁ := by
    rw [fixed.ambientCellG₁_eq] at h1
    exact (Finset.mem_filter.mp h1).1
  have h3 : dist p 0 ≤ 3 := coarse.coarseG₁_bounded p h2
  have h4 : gridCenter (1 / 100) p = fixed.centerG₁ := by
    rw [fixed.ambientCellG₁_eq] at h1
    exact (Finset.mem_filter.mp h1).2
  have h5 : dist p (gridCenter (1 / 100) p) ≤ 1 / 100 :=
    gridCenter_rho_close (1 / 100) (by norm_num) p
  rw [h4] at h5
  have h6 : dist fixed.centerG₁ 0 ≤ dist fixed.centerG₁ p + dist p 0 := dist_triangle _ _ _
  have h7 : dist fixed.centerG₁ p = dist p fixed.centerG₁ := dist_comm _ _
  rw [h7] at h6
  have h8 : ‖fixed.centerG₁‖ = dist fixed.centerG₁ 0 := by rw [dist_eq_norm] <;> simp
  rw [h8]
  linarith

/-- `centerG₂` is bounded by 3 + 1/100. -/
lemma centerG₂_norm_upper : ‖fixed.centerG₂‖ ≤ 3 + 1 / 100 := by
  rcases fixed.cellG₂_nonempty with ⟨p, hp⟩
  have h1 : p ∈ fixed.ambientCellG₂ := fixed.cellG₂_subset hp
  have h2 : p ∈ coarse.coarseG₂ := by
    rw [fixed.ambientCellG₂_eq] at h1
    exact (Finset.mem_filter.mp h1).1
  have h3 : dist p 0 ≤ 3 := coarse.coarseG₂_bounded p h2
  have h4 : gridCenter (1 / 100) p = fixed.centerG₂ := by
    rw [fixed.ambientCellG₂_eq] at h1
    exact (Finset.mem_filter.mp h1).2
  have h5 : dist p (gridCenter (1 / 100) p) ≤ 1 / 100 :=
    gridCenter_rho_close (1 / 100) (by norm_num) p
  rw [h4] at h5
  have h6 : dist fixed.centerG₂ 0 ≤ dist fixed.centerG₂ p + dist p 0 := dist_triangle _ _ _
  have h7 : dist fixed.centerG₂ p = dist p fixed.centerG₂ := dist_comm _ _
  rw [h7] at h6
  have h8 : ‖fixed.centerG₂‖ = dist fixed.centerG₂ 0 := by rw [dist_eq_norm] <;> simp
  rw [h8]
  linarith

/-- `centerF` is at least `1/3 - 1/100` from the origin. -/
lemma centerF_norm_lower : ‖fixed.centerF‖ ≥ 1 / 3 - 1 / 100 := by
  rcases fixed.cellH_nonempty with ⟨edge, hedge⟩
  have hsep := fixed.quantitative_separation edge hedge
  have h1 : dist edge.1 0 ≥ 1 / 3 := hsep.1
  have h2 : edge.1 ∈ fixed.cellF := (fixed.cellH_support edge hedge).1
  have h3 : dist edge.1 fixed.centerF ≤ 1 / 100 := fixed.cellF_ball edge.1 h2
  have h4 : dist edge.1 0 ≤ dist edge.1 fixed.centerF + dist fixed.centerF 0 := dist_triangle _ _ _
  have h5 : ‖fixed.centerF‖ = dist fixed.centerF 0 := by rw [dist_eq_norm] <;> simp
  rw [h5]
  linarith

/-- Distance between `centerG₁` and `centerG₂` is at least `2/5 - 2/100`. -/
lemma centerG_dist_lower : dist fixed.centerG₁ fixed.centerG₂ ≥ 2 / 5 - 2 / 100 := by
  rcases fixed.cellH_nonempty with ⟨edge, hedge⟩
  have hsep := fixed.quantitative_separation edge hedge
  have h1 : dist edge.2.1 edge.2.2 ≥ 2 / 5 := hsep.2
  have hsupport := fixed.cellH_support edge hedge
  have h2 : edge.2.1 ∈ fixed.cellG₁ := hsupport.2.1
  have h3 : edge.2.2 ∈ fixed.cellG₂ := hsupport.2.2
  have h4 : dist edge.2.1 fixed.centerG₁ ≤ 1 / 100 := fixed.cellG₁_ball edge.2.1 h2
  have h5 : dist edge.2.2 fixed.centerG₂ ≤ 1 / 100 := fixed.cellG₂_ball edge.2.2 h3
  have h6 : dist edge.2.1 edge.2.2 ≤
      dist edge.2.1 fixed.centerG₁ + dist fixed.centerG₁ fixed.centerG₂ + dist fixed.centerG₂ edge.2.2 := by
    calc
      dist edge.2.1 edge.2.2
        ≤ dist edge.2.1 fixed.centerG₁ + dist fixed.centerG₁ edge.2.2 := dist_triangle _ _ _
      _ ≤ dist edge.2.1 fixed.centerG₁ + (dist fixed.centerG₁ fixed.centerG₂ + dist fixed.centerG₂ edge.2.2) := by
          gcongr
          exact dist_triangle _ _ _
      _ = dist edge.2.1 fixed.centerG₁ + dist fixed.centerG₁ fixed.centerG₂ + dist fixed.centerG₂ edge.2.2 := by ring
  have h7 : dist fixed.centerG₂ edge.2.2 = dist edge.2.2 fixed.centerG₂ := dist_comm _ _
  rw [h7] at h6
  linarith

/-- Distance between `centerG₁` and `centerG₂` is at most `6 + 2/100`. -/
lemma centerG_dist_upper : dist fixed.centerG₁ fixed.centerG₂ ≤ 6 + 2 / 100 := by
  have h1 : dist fixed.centerG₁ fixed.centerG₂ ≤ dist fixed.centerG₁ 0 + dist fixed.centerG₂ 0 := by
    calc
      dist fixed.centerG₁ fixed.centerG₂
        ≤ dist fixed.centerG₁ 0 + dist 0 fixed.centerG₂ := dist_triangle _ _ _
      _ = dist fixed.centerG₁ 0 + dist fixed.centerG₂ 0 := by
        have h : dist 0 fixed.centerG₂ = dist fixed.centerG₂ 0 := dist_comm _ _
        rw [h]
  have h4 : ‖fixed.centerG₁‖ = dist fixed.centerG₁ 0 := by rw [dist_eq_norm] <;> simp
  have h5 : ‖fixed.centerG₂‖ = dist fixed.centerG₂ 0 := by rw [dist_eq_norm] <;> simp
  have h6 : ‖fixed.centerG₁‖ ≤ 3 + 1 / 100 := centerG₁_norm_upper fixed
  have h7 : ‖fixed.centerG₂‖ ≤ 3 + 1 / 100 := centerG₂_norm_upper fixed
  have h8 : dist fixed.centerG₁ 0 ≤ 3 + 1 / 100 := by rw [←h4] <;> exact h6
  have h9 : dist fixed.centerG₂ 0 ≤ 3 + 1 / 100 := by rw [←h5] <;> exact h7
  linarith

/-- The first coordinate scale factor. -/
def firstScale : ℝ := min 5 (1 / (‖fixed.centerF‖ + 1 / 100))

/-- The endpoint scale factor. -/
def endpointScale : ℝ := min 5 (1 / (1 / 100 + dist fixed.centerG₁ fixed.centerG₂ / 2))

/-- The endpoint translation. -/
def endpointTranslation : Point2 :=
  -(1 / 2 : ℝ) • (endpointScale fixed • (fixed.centerG₁ + fixed.centerG₂))

/-- `1/4 ≤ firstScale ≤ 5`. -/
lemma firstScale_bounds : 1 / 4 ≤ firstScale fixed ∧ firstScale fixed ≤ 5 := by
  have h_norm_upper : ‖fixed.centerF‖ + 1 / 100 ≤ 4 := by
    have h := centerF_norm_upper fixed
    linarith
  have h_pos : 0 < ‖fixed.centerF‖ + 1 / 100 := by positivity
  have h_lower1 : 1 / (‖fixed.centerF‖ + 1 / 100) ≥ 1 / 4 := by
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  have h_lower : 1 / 4 ≤ firstScale fixed := by
    dsimp only [firstScale]
    exact le_min (by norm_num) h_lower1
  have h_upper : firstScale fixed ≤ 5 := by
    dsimp only [firstScale]
    exact min_le_left _ _
  exact ⟨h_lower, h_upper⟩

/-- `1/4 ≤ endpointScale ≤ 5`. -/
lemma endpointScale_bounds : 1 / 4 ≤ endpointScale fixed ∧ endpointScale fixed ≤ 5 := by
  set D := dist fixed.centerG₁ fixed.centerG₂ with hD
  have hD_upper : D ≤ 6 + 2 / 100 := centerG_dist_upper fixed
  have h_pos : 0 < 1 / 100 + D / 2 := by positivity
  have h_arg_upper : 1 / 100 + D / 2 ≤ 4 := by linarith
  have h_lower1 : 1 / (1 / 100 + D / 2) ≥ 1 / 4 := by
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  have h_lower : 1 / 4 ≤ endpointScale fixed := by
    dsimp only [endpointScale]
    exact le_min (by norm_num) h_lower1
  have h_upper : endpointScale fixed ≤ 5 := by
    dsimp only [endpointScale]
    exact min_le_left _ _
  exact ⟨h_lower, h_upper⟩

/-- Product bound: `1/16 ≤ firstScale * endpointScale`. -/
lemma scale_product_lower : 1 / 16 ≤ firstScale fixed * endpointScale fixed := by
  have h1 : 1 / 4 ≤ firstScale fixed := (firstScale_bounds fixed).1
  have h2 : 1 / 4 ≤ endpointScale fixed := (endpointScale_bounds fixed).1
  have h3 : 0 ≤ firstScale fixed := by linarith [h1]
  have h4 : 0 ≤ endpointScale fixed := by linarith [h2]
  nlinarith

/-- Product upper bound: `firstScale * endpointScale ≤ 100`. -/
lemma scale_product_upper : firstScale fixed * endpointScale fixed ≤ 100 := by
  have h1 : firstScale fixed ≤ 5 := (firstScale_bounds fixed).2
  have h2 : endpointScale fixed ≤ 5 := (endpointScale_bounds fixed).2
  have h3 : 0 ≤ firstScale fixed := by linarith [(firstScale_bounds fixed).1]
  have h4 : 0 ≤ endpointScale fixed := by linarith [(endpointScale_bounds fixed).1]
  nlinarith

/-- `firstScale * (‖centerF‖ + 1/100) ≤ 1`. -/
lemma firstScale_norm_bound : firstScale fixed * (‖fixed.centerF‖ + 1 / 100) ≤ 1 := by
  dsimp only [firstScale]
  by_cases h : (1 / (‖fixed.centerF‖ + 1 / 100)) ≤ 5
  · have hmin : min 5 (1 / (‖fixed.centerF‖ + 1 / 100)) = 1 / (‖fixed.centerF‖ + 1 / 100) := by
      rw [min_eq_right h]
    rw [hmin]
    have hpos : 0 < ‖fixed.centerF‖ + 1 / 100 := by positivity
    have h : (1 / (‖fixed.centerF‖ + 1 / 100)) * (‖fixed.centerF‖ + 1 / 100) = 1 := by
      field_simp
      <;> ring
    rw [h]
    <;> norm_num
  · have h5 : 5 ≤ 1 / (‖fixed.centerF‖ + 1 / 100) := by linarith
    have hmin : min 5 (1 / (‖fixed.centerF‖ + 1 / 100)) = 5 := by
      rw [min_eq_left] <;> linarith
    rw [hmin]
    have hpos : 0 < ‖fixed.centerF‖ + 1 / 100 := by positivity
    have h6 : 5 * (‖fixed.centerF‖ + 1 / 100) ≤ 1 := by
      have h7 : 5 * (‖fixed.centerF‖ + 1 / 100) ≤ (1 / (‖fixed.centerF‖ + 1 / 100)) * (‖fixed.centerF‖ + 1 / 100) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
      have h8 : (1 / (‖fixed.centerF‖ + 1 / 100)) * (‖fixed.centerF‖ + 1 / 100) = 1 := by
        field_simp <;> ring
      rw [h8] at h7
      exact h7
    exact h6

/-- `endpointScale * (1/100 + dist/2) ≤ 1`. -/
lemma endpointScale_dist_bound :
    endpointScale fixed * (1 / 100 + dist fixed.centerG₁ fixed.centerG₂ / 2) ≤ 1 := by
  dsimp only [endpointScale]
  set D := dist fixed.centerG₁ fixed.centerG₂ with hD
  by_cases h : (1 / (1 / 100 + D / 2)) ≤ 5
  · have hmin : min 5 (1 / (1 / 100 + D / 2)) = 1 / (1 / 100 + D / 2) := by
      rw [min_eq_right h]
    rw [hmin]
    have hpos : 0 < 1 / 100 + D / 2 := by positivity
    have hne : (1 / 100 + D / 2) ≠ 0 := by linarith
    have h : (1 / (1 / 100 + D / 2)) * (1 / 100 + D / 2) = 1 := by
      have h9 : (1 / (1 / 100 + D / 2)) * (1 / 100 + D / 2) = (1 / 100 + D / 2) / (1 / 100 + D / 2) := by ring
      rw [h9]
      rw [div_self hne]
    rw [h] <;> norm_num
  · have h5 : 5 ≤ 1 / (1 / 100 + D / 2) := by linarith
    have hmin : min 5 (1 / (1 / 100 + D / 2)) = 5 := by
      rw [min_eq_left] <;> linarith
    rw [hmin]
    have hpos : 0 < 1 / 100 + D / 2 := by positivity
    have hne : (1 / 100 + D / 2) ≠ 0 := by linarith
    have h8 : (1 / (1 / 100 + D / 2)) * (1 / 100 + D / 2) = 1 := by
      have h9 : (1 / (1 / 100 + D / 2)) * (1 / 100 + D / 2) = (1 / 100 + D / 2) / (1 / 100 + D / 2) := by ring
      rw [h9, div_self hne]
    have h6 : 5 * (1 / 100 + D / 2) ≤ 1 := by
      have h7 : 5 * (1 / 100 + D / 2) ≤ (1 / (1 / 100 + D / 2)) * (1 / 100 + D / 2) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
      rw [h8] at h7
      exact h7
    exact h6

/-- Normalized F is contained in the unit ball. -/
lemma normalizedF_unit_ball :
    ∀ p ∈ fixed.cellF.image (fun point => firstScale fixed • point), dist p 0 ≤ 1 := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
  have h1 : dist x fixed.centerF ≤ 1 / 100 := fixed.cellF_ball x hx
  have h2 : dist x 0 ≤ ‖fixed.centerF‖ + 1 / 100 := by
    calc
      dist x 0 ≤ dist x fixed.centerF + dist fixed.centerF 0 := dist_triangle _ _ _
      _ ≤ 1 / 100 + ‖fixed.centerF‖ := by
        gcongr
        <;> rw [dist_eq_norm] <;> simp
      _ = ‖fixed.centerF‖ + 1 / 100 := by ring
  have h_pos : 0 ≤ firstScale fixed := by linarith [firstScale_bounds fixed]
  have h3 : dist (firstScale fixed • x) 0 = firstScale fixed * dist x 0 := by
    rw [dist_eq_norm]
    simp [norm_smul, abs_of_nonneg h_pos, dist_eq_norm]
    <;> ring
  rw [h3]
  have h9 : firstScale fixed * dist x 0 ≤ firstScale fixed * (‖fixed.centerF‖ + 1 / 100) := by
    gcongr <;> linarith
  have h10 := firstScale_norm_bound fixed
  linarith

/-- Normalized G₁ is contained in the unit ball. -/
lemma normalizedG₁_unit_ball :
    ∀ p ∈ fixed.cellG₁.image (fun point => endpointScale fixed • point + endpointTranslation fixed),
      dist p 0 ≤ 1 := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
  have h1 : dist x fixed.centerG₁ ≤ 1 / 100 := fixed.cellG₁_ball x hx
  set midpoint := (1 / 2 : ℝ) • (fixed.centerG₁ + fixed.centerG₂) with hmid
  have h_eq : endpointScale fixed • x + endpointTranslation fixed =
      endpointScale fixed • (x - midpoint) := by
    simp only [endpointTranslation, hmid]
    ext i
    fin_cases i <;> simp [smul_sub, sub_smul] <;> ring
  rw [h_eq]
  have h2 : dist (x - midpoint) 0 ≤ 1 / 100 + dist fixed.centerG₁ fixed.centerG₂ / 2 := by
    have h3 : dist (x - midpoint) 0 = dist x midpoint := by
      simp [dist_eq_norm] <;> ring_nf
    rw [h3]
    have h4 : dist x midpoint ≤ dist x fixed.centerG₁ + dist fixed.centerG₁ midpoint := dist_triangle _ _ _
    have h5 : dist fixed.centerG₁ midpoint = dist fixed.centerG₁ fixed.centerG₂ / 2 := by
      have h6 : fixed.centerG₁ - midpoint = (1 / 2 : ℝ) • (fixed.centerG₁ - fixed.centerG₂) := by
        ext i; fin_cases i <;> simp [hmid, smul_sub, sub_smul] <;> ring
      have h7 : dist fixed.centerG₁ midpoint = ‖fixed.centerG₁ - midpoint‖ := by
        rw [dist_eq_norm] <;> simp
      rw [h7, h6]
      have h8 : ‖(1 / 2 : ℝ) • (fixed.centerG₁ - fixed.centerG₂)‖ = (1 / 2 : ℝ) * ‖fixed.centerG₁ - fixed.centerG₂‖ := by
        rw [norm_smul] <;> norm_num
      rw [h8]
      have h9 : ‖fixed.centerG₁ - fixed.centerG₂‖ = dist fixed.centerG₁ fixed.centerG₂ := by
        rw [dist_eq_norm] <;> simp
      rw [h9] <;> ring
    linarith
  have h_pos : 0 ≤ endpointScale fixed := by linarith [endpointScale_bounds fixed]
  have h3 : dist (endpointScale fixed • (x - midpoint)) 0 =
      endpointScale fixed * dist (x - midpoint) 0 := by
    rw [dist_eq_norm]
    simp [norm_smul, abs_of_nonneg h_pos, dist_eq_norm] <;> ring
  rw [h3]
  have h9 : endpointScale fixed * dist (x - midpoint) 0 ≤
      endpointScale fixed * (1 / 100 + dist fixed.centerG₁ fixed.centerG₂ / 2) := by
    gcongr <;> linarith
  have h10 := endpointScale_dist_bound fixed
  linarith

/-- Normalized G₂ is contained in the unit ball. -/
lemma normalizedG₂_unit_ball :
    ∀ p ∈ fixed.cellG₂.image (fun point => endpointScale fixed • point + endpointTranslation fixed),
      dist p 0 ≤ 1 := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
  have h1 : dist x fixed.centerG₂ ≤ 1 / 100 := fixed.cellG₂_ball x hx
  set midpoint := (1 / 2 : ℝ) • (fixed.centerG₁ + fixed.centerG₂) with hmid
  have h_eq : endpointScale fixed • x + endpointTranslation fixed =
      endpointScale fixed • (x - midpoint) := by
    simp only [endpointTranslation, hmid]
    ext i
    fin_cases i <;> simp [smul_sub, sub_smul] <;> ring
  rw [h_eq]
  have h2 : dist (x - midpoint) 0 ≤ 1 / 100 + dist fixed.centerG₁ fixed.centerG₂ / 2 := by
    have h3 : dist (x - midpoint) 0 = dist x midpoint := by
      simp [dist_eq_norm] <;> ring_nf
    rw [h3]
    have h4 : dist x midpoint ≤ dist x fixed.centerG₂ + dist fixed.centerG₂ midpoint := dist_triangle _ _ _
    have h5 : dist fixed.centerG₂ midpoint = dist fixed.centerG₁ fixed.centerG₂ / 2 := by
      have h6 : fixed.centerG₂ - midpoint = (1 / 2 : ℝ) • (fixed.centerG₂ - fixed.centerG₁) := by
        ext i; fin_cases i <;> simp [hmid, smul_sub, sub_smul] <;> ring
      have h7 : dist fixed.centerG₂ midpoint = ‖fixed.centerG₂ - midpoint‖ := by
        rw [dist_eq_norm] <;> simp
      rw [h7, h6]
      have h8 : ‖(1 / 2 : ℝ) • (fixed.centerG₂ - fixed.centerG₁)‖ = (1 / 2 : ℝ) * ‖fixed.centerG₂ - fixed.centerG₁‖ := by
        rw [norm_smul] <;> norm_num
      rw [h8]
      have h9 : ‖fixed.centerG₂ - fixed.centerG₁‖ = dist fixed.centerG₂ fixed.centerG₁ := by
        rw [dist_eq_norm] <;> simp
      have h10 : dist fixed.centerG₂ fixed.centerG₁ = dist fixed.centerG₁ fixed.centerG₂ := dist_comm _ _
      rw [h9, h10] <;> ring
    linarith
  have h_pos : 0 ≤ endpointScale fixed := by linarith [endpointScale_bounds fixed]
  have h3 : dist (endpointScale fixed • (x - midpoint)) 0 =
      endpointScale fixed * dist (x - midpoint) 0 := by
    rw [dist_eq_norm]
    simp [norm_smul, abs_of_nonneg h_pos, dist_eq_norm] <;> ring
  rw [h3]
  have h9 : endpointScale fixed * dist (x - midpoint) 0 ≤
      endpointScale fixed * (1 / 100 + dist fixed.centerG₁ fixed.centerG₂ / 2) := by
    gcongr <;> linarith
  have h10 := endpointScale_dist_bound fixed
  linarith

/-- Diameter of normalized F ≤ 1/10. -/
lemma normalizedF_diameter :
    ∀ x ∈ fixed.cellF.image (fun point => firstScale fixed • point),
      ∀ y ∈ fixed.cellF.image (fun point => firstScale fixed • point),
        dist x y ≤ 1 / 10 := by
  intro x hx y hy
  rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨y0, hy0, rfl⟩
  have h1 : dist x0 y0 ≤ 2 / 100 := by
    have h2 : dist x0 y0 ≤ dist x0 fixed.centerF + dist fixed.centerF y0 := dist_triangle _ _ _
    have h3 : dist fixed.centerF y0 = dist y0 fixed.centerF := dist_comm _ _
    rw [h3] at h2
    have h4 : dist x0 fixed.centerF ≤ 1 / 100 := fixed.cellF_ball x0 hx0
    have h5 : dist y0 fixed.centerF ≤ 1 / 100 := fixed.cellF_ball y0 hy0
    linarith
  have h_pos : 0 ≤ firstScale fixed := by linarith [firstScale_bounds fixed]
  have h6 : dist (firstScale fixed • x0) (firstScale fixed • y0) =
      firstScale fixed * dist x0 y0 := by
    rw [dist_smul_real, abs_of_nonneg h_pos]
  rw [h6]
  have h7 : firstScale fixed ≤ 5 := (firstScale_bounds fixed).2
  nlinarith

/-- Diameter of normalized G₁ ≤ 1/10. -/
lemma normalizedG₁_diameter :
    ∀ x ∈ fixed.cellG₁.image (fun point => endpointScale fixed • point + endpointTranslation fixed),
      ∀ y ∈ fixed.cellG₁.image (fun point => endpointScale fixed • point + endpointTranslation fixed),
        dist x y ≤ 1 / 10 := by
  intro x hx y hy
  rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
  have h1 : dist x1 y1 ≤ 2 / 100 := by
    have h2 : dist x1 y1 ≤ dist x1 fixed.centerG₁ + dist fixed.centerG₁ y1 := dist_triangle _ _ _
    have h3 : dist fixed.centerG₁ y1 = dist y1 fixed.centerG₁ := dist_comm _ _
    rw [h3] at h2
    have h4 : dist x1 fixed.centerG₁ ≤ 1 / 100 := fixed.cellG₁_ball x1 hx1
    have h5 : dist y1 fixed.centerG₁ ≤ 1 / 100 := fixed.cellG₁_ball y1 hy1
    linarith
  have h_pos : 0 ≤ endpointScale fixed := by linarith [endpointScale_bounds fixed]
  have h6 : dist (endpointScale fixed • x1 + endpointTranslation fixed)
        (endpointScale fixed • y1 + endpointTranslation fixed) =
      endpointScale fixed * dist x1 y1 := by
    rw [dist_add_right, dist_smul_real, abs_of_nonneg h_pos]
  rw [h6]
  have h7 : endpointScale fixed ≤ 5 := (endpointScale_bounds fixed).2
  nlinarith

/-- Diameter of normalized G₂ ≤ 1/10. -/
lemma normalizedG₂_diameter :
    ∀ x ∈ fixed.cellG₂.image (fun point => endpointScale fixed • point + endpointTranslation fixed),
      ∀ y ∈ fixed.cellG₂.image (fun point => endpointScale fixed • point + endpointTranslation fixed),
        dist x y ≤ 1 / 10 := by
  intro x hx y hy
  rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
  have h1 : dist x1 y1 ≤ 2 / 100 := by
    have h2 : dist x1 y1 ≤ dist x1 fixed.centerG₂ + dist fixed.centerG₂ y1 := dist_triangle _ _ _
    have h3 : dist fixed.centerG₂ y1 = dist y1 fixed.centerG₂ := dist_comm _ _
    rw [h3] at h2
    have h4 : dist x1 fixed.centerG₂ ≤ 1 / 100 := fixed.cellG₂_ball x1 hx1
    have h5 : dist y1 fixed.centerG₂ ≤ 1 / 100 := fixed.cellG₂_ball y1 hy1
    linarith
  have h_pos : 0 ≤ endpointScale fixed := by linarith [endpointScale_bounds fixed]
  have h6 : dist (endpointScale fixed • x1 + endpointTranslation fixed)
        (endpointScale fixed • y1 + endpointTranslation fixed) =
      endpointScale fixed * dist x1 y1 := by
    rw [dist_add_right, dist_smul_real, abs_of_nonneg h_pos]
  rw [h6]
  have h7 : endpointScale fixed ≤ 5 := (endpointScale_bounds fixed).2
  nlinarith

/-- Mutual separation between normalized G₁ and G₂ ≥ 1/2. -/
lemma normalizedG_mutual_separation :
    WZ1MutuallySeparated
      (fixed.cellG₁.image (fun point => endpointScale fixed • point + endpointTranslation fixed))
      (fixed.cellG₂.image (fun point => endpointScale fixed • point + endpointTranslation fixed))
      (1 / 2) := by
  intro x hx y hy
  rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨y0, hy0, rfl⟩
  set D := dist fixed.centerG₁ fixed.centerG₂ with hD
  have h1 : dist x0 y0 ≥ D - 2 / 100 := by
    have h2 : D ≤ dist fixed.centerG₁ x0 + dist x0 y0 + dist y0 fixed.centerG₂ := by
      calc
        D = dist fixed.centerG₁ fixed.centerG₂ := rfl
        _ ≤ dist fixed.centerG₁ x0 + dist x0 fixed.centerG₂ := dist_triangle _ _ _
        _ ≤ dist fixed.centerG₁ x0 + (dist x0 y0 + dist y0 fixed.centerG₂) := by
          gcongr
          exact dist_triangle _ _ _
        _ = dist fixed.centerG₁ x0 + dist x0 y0 + dist y0 fixed.centerG₂ := by ring
    have h3 : dist fixed.centerG₁ x0 ≤ 1 / 100 := by
      have h4 : dist x0 fixed.centerG₁ ≤ 1 / 100 := fixed.cellG₁_ball x0 hx0
      have h5 : dist fixed.centerG₁ x0 = dist x0 fixed.centerG₁ := dist_comm _ _
      rw [h5]; exact h4
    have h6 : dist y0 fixed.centerG₂ ≤ 1 / 100 := fixed.cellG₂_ball y0 hy0
    linarith
  have h_pos : 0 ≤ endpointScale fixed := by linarith [endpointScale_bounds fixed]
  have h7 : dist (endpointScale fixed • x0 + endpointTranslation fixed)
        (endpointScale fixed • y0 + endpointTranslation fixed) =
      endpointScale fixed * dist x0 y0 := by
    rw [dist_add_right, dist_smul_real, abs_of_nonneg h_pos]
  rw [h7]
  have h8 : endpointScale fixed * dist x0 y0 ≥ endpointScale fixed * (D - 2 / 100) := by
    gcongr <;> linarith
  have hD_lower : D ≥ 2 / 5 - 2 / 100 := centerG_dist_lower fixed
  dsimp only [endpointScale]
  by_cases hcase : (1 / (1 / 100 + D / 2)) ≤ 5
  · rw [min_eq_right hcase]
    have hpos : 0 < 1 / 100 + D / 2 := by positivity
    have h9 : (D - 2 / 100) / (1 / 100 + D / 2) ≥ 1 / 2 := by
      have h10 : 2 * (D - 2 / 100) ≥ 1 / 100 + D / 2 := by linarith
      have h11 : 0 < 1 / 100 + D / 2 := hpos
      have h12 : (D - 2 / 100) / (1 / 100 + D / 2) ≥ 1 / 2 := by
        calc
          (D - 2 / 100) / (1 / 100 + D / 2)
            = (2 * (D - 2 / 100)) / (2 * (1 / 100 + D / 2)) := by field_simp [h11.ne'] <;> ring
          _ ≥ ((1 / 100 + D / 2)) / (2 * (1 / 100 + D / 2)) := by gcongr
          _ = 1 / 2 := by field_simp [h11.ne'] <;> ring
      exact h12
    calc
      (1 / (1 / 100 + D / 2)) * dist x0 y0
        ≥ (1 / (1 / 100 + D / 2)) * (D - 2 / 100) := by gcongr
      _ = (D - 2 / 100) / (1 / 100 + D / 2) := by ring
      _ ≥ 1 / 2 := h9
  · rw [min_eq_left (by linarith)]
    have h9 : 5 * (D - 2 / 100) ≥ 1 / 2 := by linarith
    calc
      5 * dist x0 y0 ≥ 5 * (D - 2 / 100) := by gcongr
      _ ≥ 1 / 2 := h9

/-- Normalized F points are at distance ≥ 1/2 from origin. -/
lemma normalizedF_dist_origin :
    ∀ x ∈ fixed.cellF.image (fun point => firstScale fixed • point),
      1 / 2 ≤ dist x 0 := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
  have h1 : dist x0 0 ≥ ‖fixed.centerF‖ - 1 / 100 := by
    have h2 : dist fixed.centerF 0 ≤ dist fixed.centerF x0 + dist x0 0 := dist_triangle _ _ _
    have h3 : dist fixed.centerF x0 ≤ 1 / 100 := by
      have h4 : dist x0 fixed.centerF ≤ 1 / 100 := fixed.cellF_ball x0 hx0
      have h5 : dist fixed.centerF x0 = dist x0 fixed.centerF := dist_comm _ _
      rw [h5]; exact h4
    have h6 : ‖fixed.centerF‖ = dist fixed.centerF 0 := by rw [dist_eq_norm] <;> simp
    linarith [h2, h3, h6]
  have h_pos : 0 ≤ firstScale fixed := by linarith [firstScale_bounds fixed]
  have h3 : dist (firstScale fixed • x0) 0 = firstScale fixed * dist x0 0 := by
    rw [dist_eq_norm]
    simp [norm_smul, abs_of_nonneg h_pos, dist_eq_norm] <;> ring
  rw [h3]
  have h4 : firstScale fixed * dist x0 0 ≥ firstScale fixed * (‖fixed.centerF‖ - 1 / 100) := by
    gcongr <;> linarith
  have h_center_lower : ‖fixed.centerF‖ ≥ 1 / 3 - 1 / 100 := centerF_norm_lower fixed
  dsimp only [firstScale]
  by_cases hcase : (1 / (‖fixed.centerF‖ + 1 / 100)) ≤ 5
  · rw [min_eq_right hcase]
    have hpos : 0 < ‖fixed.centerF‖ + 1 / 100 := by positivity
    have h9 : (‖fixed.centerF‖ - 1 / 100) / (‖fixed.centerF‖ + 1 / 100) ≥ 1 / 2 := by
      have h10 : 2 * (‖fixed.centerF‖ - 1 / 100) ≥ ‖fixed.centerF‖ + 1 / 100 := by linarith
      have h11 : 0 < ‖fixed.centerF‖ + 1 / 100 := hpos
      calc
        (‖fixed.centerF‖ - 1 / 100) / (‖fixed.centerF‖ + 1 / 100)
          = (2 * (‖fixed.centerF‖ - 1 / 100)) / (2 * (‖fixed.centerF‖ + 1 / 100)) := by field_simp [h11.ne'] <;> ring
        _ ≥ ((‖fixed.centerF‖ + 1 / 100)) / (2 * (‖fixed.centerF‖ + 1 / 100)) := by gcongr
        _ = 1 / 2 := by field_simp [h11.ne'] <;> ring
    calc
      (1 / (‖fixed.centerF‖ + 1 / 100)) * dist x0 0
        ≥ (1 / (‖fixed.centerF‖ + 1 / 100)) * (‖fixed.centerF‖ - 1 / 100) := by gcongr
      _ = (‖fixed.centerF‖ - 1 / 100) / (‖fixed.centerF‖ + 1 / 100) := by ring
      _ ≥ 1 / 2 := h9
  · rw [min_eq_left (by linarith)]
    have h9 : 5 * (‖fixed.centerF‖ - 1 / 100) ≥ 1 / 2 := by linarith
    calc
      5 * dist x0 0 ≥ 5 * (‖fixed.centerF‖ - 1 / 100) := by gcongr
      _ ≥ 1 / 2 := h9

/-- Standard separation for the normalized sets. -/
lemma normalized_standard_separation :
    WZ1StandardSeparation
      (fixed.cellF.image (fun point => firstScale fixed • point))
      (fixed.cellG₁.image (fun point => endpointScale fixed • point + endpointTranslation fixed))
      (fixed.cellG₂.image (fun point => endpointScale fixed • point + endpointTranslation fixed)) := by
  exact ⟨
    normalizedF_diameter fixed,
    normalizedG₁_diameter fixed,
    normalizedG₂_diameter fixed,
    normalizedG_mutual_separation fixed,
    normalizedF_dist_origin fixed
  ⟩

end WideFixedCellScaleBounds

end Kakeya.Assouad
