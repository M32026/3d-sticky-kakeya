module

/-
# Four-Sector Pigeonhole Selection

Given a finite bad-direction set with Frostman mass, remove the pole neighborhood
(retaining ≥ 1/2 mass), partition the remainder into four disjoint coefficient
sectors by half-open intervals, and select one sector carrying ≥ 1/4 of the
remaining mass (hence ≥ 1/8 of the original).

The four sectors are:
  S1: 0 ≤ x(y) ≤ 1      (Icc 0 1)
  S2: 1 < x(y)          (Ioi 1)
  S3: -1 ≤ x(y) < 0     (Ico -1 0)
  S4: x(y) < -1         (Iio -1)

These are pairwise disjoint and cover all of ℝ.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.PoleRemovalHelper
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Metric

namespace ProductLikeIncidence.ProductReduction

/-- Predicate: y belongs to sector i based on cross-ratio x(y). -/
def sectorPredicate (i : Fin 4) (x : ℝ → ℝ) (y : ℝ) : Prop :=
  match i with
  | 0 => x y ∈ Set.Icc (0 : ℝ) 1
  | 1 => x y ∈ Set.Ioi (1 : ℝ)
  | 2 => x y ∈ Set.Ico (-1 : ℝ) 0
  | 3 => x y ∈ Set.Iio (-1 : ℝ)

/-- The four half-open intervals cover ℝ. -/
lemma four_halfopen_intervals_cover (z : ℝ) :
    z ∈ Set.Icc (0 : ℝ) 1 ∨ z ∈ Set.Ioi (1 : ℝ) ∨
    z ∈ Set.Ico (-1 : ℝ) 0 ∨ z ∈ Set.Iio (-1 : ℝ) := by
  by_cases h1 : 0 ≤ z
  · by_cases h2 : z ≤ 1
    · exact Or.inl ⟨h1, h2⟩
    · have h2' : 1 < z := by linarith
      exact Or.inr (Or.inl h2')
  · have h3 : z < 0 := by linarith
    by_cases h4 : -1 ≤ z
    · exact Or.inr (Or.inr (Or.inl ⟨h4, h3⟩))
    · have h4' : z < -1 := by linarith
      exact Or.inr (Or.inr (Or.inr h4'))

/-- Normalized coefficient t for each sector. -/
def sectorTMap (i : Fin 4) (x_val : ℝ) : ℝ :=
  match i with
  | 0 => x_val
  | 1 => 1 / x_val
  | 2 => -x_val
  | 3 => -1 / x_val

/-- Signed/swap coordinate map (a,b) for each sector, preserving Cartesian products. -/
def sectorCoordMap (i : Fin 4) (U V : ℝ) : ℝ × ℝ :=
  match i with
  | 0 => (V, U)
  | 1 => (U, V)
  | 2 => (-V, U)
  | 3 => (-U, V)

/-- t ∈ [0,1] in each sector. -/
lemma sector_t_bounds (i : Fin 4) (x : ℝ → ℝ) {y : ℝ}
    (h : sectorPredicate i x y) :
    sectorTMap i (x y) ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i
  · simpa [sectorPredicate, sectorTMap] using h
  · have h1 : 1 < x y := by simpa [sectorPredicate] using h
    have hpos : 0 < x y := by linarith
    simp only [sectorTMap]
    have h_le : 1 / x y ≤ 1 := by
      have h7 : 1 ≤ x y := by linarith
      have h8 : 1 / x y ≤ 1 / (1 : ℝ) := one_div_le_one_div_of_le (by norm_num) h7
      simpa using h8
    exact ⟨by positivity, h_le⟩
  · have h2 : -1 ≤ x y ∧ x y < 0 := by simpa [sectorPredicate] using h
    simp only [sectorTMap]
    exact ⟨by linarith, by linarith⟩
  · have h3 : x y < -1 := by simpa [sectorPredicate] using h
    have hneg : x y < 0 := by linarith
    simp only [sectorTMap]
    have h4 : -1 / (x y) = 1 / (-(x y)) := by
      field_simp [hneg.ne]
    rw [h4]
    have h5 : 0 < -(x y) := by linarith
    have h6 : 1 ≤ -(x y) := by linarith
    have h_le : 1 / (-(x y)) ≤ 1 := by
      have h7 : 1 ≤ -(x y) := by linarith
      have h8 : 1 / (-(x y)) ≤ 1 / (1 : ℝ) := one_div_le_one_div_of_le (by norm_num) h7
      simpa using h8
    exact ⟨by positivity, h_le⟩

/-- Projection identity: t*a + b equals U + x*V (sectors 0,2)
    or (1/x)*(U + x*V) (sectors 1,3). -/
lemma sector_projection_identity (i : Fin 4) (x : ℝ → ℝ) {y : ℝ}
    (h : sectorPredicate i x y) (U V : ℝ) :
    sectorTMap i (x y) * (sectorCoordMap i U V).1 +
      (sectorCoordMap i U V).2 =
    if i = 0 ∨ i = 2 then U + x y * V
    else (1 / (x y)) * (U + x y * V) := by
  fin_cases i
  · simp [sectorTMap, sectorCoordMap]; ring
  · have hx_ne_zero : x y ≠ 0 := by
      have h1 : 1 < x y := by simpa [sectorPredicate] using h
      linarith
    simp [sectorTMap, sectorCoordMap]; field_simp [hx_ne_zero]
  · simp [sectorTMap, sectorCoordMap]; ring
  · have hx_ne_zero : x y ≠ 0 := by
      have h3 : x y < -1 := by simpa [sectorPredicate] using h
      linarith
    simp [sectorTMap, sectorCoordMap]; field_simp [hx_ne_zero]

/-- Pole removal followed by four-sector pigeonhole. -/
lemma four_sector_pigeonhole
    {δ κ0 C_Y q : ℝ}
    {νY : Measure ℝ} [IsProbabilityMeasure νY]
    (hνY_frost : IsDirectionFrostman δ κ0 C_Y νY)
    {Theta_bad' : Set ℝ}
    [Finite Theta_bad']
    (hTheta_mass : νY Theta_bad' ≥ ENNReal.ofReal (δ ^ q))
    (theta2 : ℝ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hκ0_pos : 0 < κ0)
    (hC_Y_pos : 0 < C_Y)
    (hq_pos : 0 < q)
    (h_absorb : C_Y * δ ^ κ0 ≤ δ ^ q / 2)
    (x : ℝ → ℝ) :
    ∃ (r : ℝ), 0 < r ∧ δ ≤ r ∧ r ^ κ0 = δ ^ q / (2 * C_Y) ∧
      ∃ (i : Fin 4) (Theta_sec : Set ℝ),
        Theta_sec ⊆ Theta_bad' \ ball theta2 r ∧
        Set.Finite Theta_sec ∧
        IsClosed Theta_sec ∧
        νY Theta_sec ≥ (1 / 8 : ENNReal) * νY Theta_bad' ∧
        (∀ y ∈ Theta_sec, sectorPredicate i x y) ∧
        (∀ y ∈ Theta_sec, sectorTMap i (x y) ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ y ∈ Theta_sec, ∀ (U V : ℝ),
          sectorTMap i (x y) * (sectorCoordMap i U V).1 +
            (sectorCoordMap i U V).2 =
          if i = 0 ∨ i = 2 then U + x y * V
          else (1 / (x y)) * (U + x y * V)) := by
  -- Step 1: Pole removal
  have h_pole : ∃ (r : ℝ), 0 < r ∧ δ ≤ r ∧ r ^ κ0 = δ ^ q / (2 * C_Y) ∧
      νY (Theta_bad' \ ball theta2 r) ≥ (1 / 2 : ENNReal) * νY Theta_bad' :=
    frostman_pole_removal hνY_frost hTheta_mass theta2 hδ_pos hδ_lt_one
      hκ0_pos hC_Y_pos hq_pos h_absorb
  rcases h_pole with ⟨r, hr_pos, hδ_le_r, h_r_pow, h_rem_mass⟩
  let Theta_rem := Theta_bad' \ ball theta2 r

  have hTheta_rem_sub : Theta_rem ⊆ Theta_bad' := by
    intro z hz; exact hz.1
  have hTheta_finite : Set.Finite Theta_bad' := Set.toFinite _
  have hRem_finite : Set.Finite Theta_rem := hTheta_finite.subset hTheta_rem_sub

  -- Step 2: Define four disjoint sectors
  let I1 : Set ℝ := Set.Icc (0 : ℝ) 1
  let I2 : Set ℝ := Set.Ioi (1 : ℝ)
  let I3 : Set ℝ := Set.Ico (-1 : ℝ) 0
  let I4 : Set ℝ := Set.Iio (-1 : ℝ)

  let S1 := Theta_rem ∩ x ⁻¹' I1
  let S2 := Theta_rem ∩ x ⁻¹' I2
  let S3 := Theta_rem ∩ x ⁻¹' I3
  let S4 := Theta_rem ∩ x ⁻¹' I4

  have hS1_sub : S1 ⊆ Theta_rem := by
    intro z hz; exact hz.1
  have hS2_sub : S2 ⊆ Theta_rem := by
    intro z hz; exact hz.1
  have hS3_sub : S3 ⊆ Theta_rem := by
    intro z hz; exact hz.1
  have hS4_sub : S4 ⊆ Theta_rem := by
    intro z hz; exact hz.1

  have h1_finite : Set.Finite S1 := hRem_finite.subset hS1_sub
  have h2_finite : Set.Finite S2 := hRem_finite.subset hS2_sub
  have h3_finite : Set.Finite S3 := hRem_finite.subset hS3_sub
  have h4_finite : Set.Finite S4 := hRem_finite.subset hS4_sub

  have h1_sub_bad : S1 ⊆ Theta_bad' := Set.Subset.trans hS1_sub hTheta_rem_sub
  have h2_sub_bad : S2 ⊆ Theta_bad' := Set.Subset.trans hS2_sub hTheta_rem_sub
  have h3_sub_bad : S3 ⊆ Theta_bad' := Set.Subset.trans hS3_sub hTheta_rem_sub
  have h4_sub_bad : S4 ⊆ Theta_bad' := Set.Subset.trans hS4_sub hTheta_rem_sub

  -- Step 3: Disjointness of interval pairs
  have h_disj_I12 : Disjoint I1 I2 := by
    rw [Set.disjoint_left]; intro z h1 h2; simp [I1, I2] at h1 h2; linarith
  have h_disj_I13 : Disjoint I1 I3 := by
    rw [Set.disjoint_left]; intro z h1 h2; simp [I1, I3] at h1 h2; linarith
  have h_disj_I14 : Disjoint I1 I4 := by
    rw [Set.disjoint_left]; intro z h1 h2; simp [I1, I4] at h1 h2; linarith
  have h_disj_I23 : Disjoint I2 I3 := by
    rw [Set.disjoint_left]; intro z h1 h2; simp [I2, I3] at h1 h2; linarith
  have h_disj_I24 : Disjoint I2 I4 := by
    rw [Set.disjoint_left]; intro z h1 h2; simp [I2, I4] at h1 h2; linarith
  have h_disj_I34 : Disjoint I3 I4 := by
    rw [Set.disjoint_left]; intro z h1 h2; simp [I3, I4] at h1 h2; linarith

  -- Disjointness of sector sets
  have h_disj12 : Disjoint S1 S2 := by
    rw [Set.disjoint_left]; intro y hy1 hy2
    exact Set.disjoint_left.mp h_disj_I12 hy1.2 hy2.2
  have h_disj13 : Disjoint S1 S3 := by
    rw [Set.disjoint_left]; intro y hy1 hy2
    exact Set.disjoint_left.mp h_disj_I13 hy1.2 hy2.2
  have h_disj14 : Disjoint S1 S4 := by
    rw [Set.disjoint_left]; intro y hy1 hy2
    exact Set.disjoint_left.mp h_disj_I14 hy1.2 hy2.2
  have h_disj23 : Disjoint S2 S3 := by
    rw [Set.disjoint_left]; intro y hy1 hy2
    exact Set.disjoint_left.mp h_disj_I23 hy1.2 hy2.2
  have h_disj24 : Disjoint S2 S4 := by
    rw [Set.disjoint_left]; intro y hy1 hy2
    exact Set.disjoint_left.mp h_disj_I24 hy1.2 hy2.2
  have h_disj34 : Disjoint S3 S4 := by
    rw [Set.disjoint_left]; intro y hy1 hy2
    exact Set.disjoint_left.mp h_disj_I34 hy1.2 hy2.2

  -- Step 4: Union covers Theta_rem
  have h_cover : Theta_rem ⊆ S1 ∪ S2 ∪ S3 ∪ S4 := by
    intro y hy
    have hxy_cases := four_halfopen_intervals_cover (x y)
    rcases hxy_cases with (h | h | h | h)
    · have h5 : y ∈ S1 := ⟨hy, h⟩
      have h6 : y ∈ S1 ∪ S2 := Or.inl h5
      have h7 : y ∈ (S1 ∪ S2) ∪ S3 := Or.inl h6
      exact Or.inl h7
    · have h5 : y ∈ S2 := ⟨hy, h⟩
      have h6 : y ∈ S1 ∪ S2 := Or.inr h5
      have h7 : y ∈ (S1 ∪ S2) ∪ S3 := Or.inl h6
      exact Or.inl h7
    · have h5 : y ∈ S3 := ⟨hy, h⟩
      have h7 : y ∈ (S1 ∪ S2) ∪ S3 := Or.inr h5
      exact Or.inl h7
    · have h5 : y ∈ S4 := ⟨hy, h⟩
      exact Or.inr h5

  -- Step 5: Measure of union equals sum
  have h_meas1 : MeasurableSet S1 := h1_finite.measurableSet
  have h_meas2 : MeasurableSet S2 := h2_finite.measurableSet
  have h_meas3 : MeasurableSet S3 := h3_finite.measurableSet
  have h_meas4 : MeasurableSet S4 := h4_finite.measurableSet

  have h_union_meas :
      νY (S1 ∪ S2 ∪ S3 ∪ S4) = νY S1 + νY S2 + νY S3 + νY S4 := by
    have h1234 : Disjoint ((S1 ∪ S2) ∪ S3) S4 := by
      rw [Set.disjoint_union_left, Set.disjoint_union_left]
      exact ⟨⟨h_disj14, h_disj24⟩, h_disj34⟩
    have h123 : Disjoint (S1 ∪ S2) S3 := by
      rw [Set.disjoint_union_left]
      exact And.intro h_disj13 h_disj23
    have h_assoc : (S1 ∪ S2 ∪ S3 ∪ S4) = ((S1 ∪ S2) ∪ S3) ∪ S4 := by ext z; simp
    rw [h_assoc]
    rw [measure_union h1234 h_meas4]
    rw [measure_union h123 h_meas3]
    rw [measure_union h_disj12 h_meas2]

  have h_sum_ge : νY S1 + νY S2 + νY S3 + νY S4 ≥ νY Theta_rem := by
    have h : νY Theta_rem ≤ νY (S1 ∪ S2 ∪ S3 ∪ S4) := measure_mono h_cover
    rw [h_union_meas] at *
    exact h

  -- Step 6: Pigeonhole
  have h_pigeonhole :
      νY S1 ≥ νY Theta_rem / 4 ∨
      νY S2 ≥ νY Theta_rem / 4 ∨
      νY S3 ≥ νY Theta_rem / 4 ∨
      νY S4 ≥ νY Theta_rem / 4 := by
    by_contra h
    push Not at h
    have h1 : νY S1 < νY Theta_rem / 4 := h.1
    have h2 : νY S2 < νY Theta_rem / 4 := h.2.1
    have h3 : νY S3 < νY Theta_rem / 4 := h.2.2.1
    have h4 : νY S4 < νY Theta_rem / 4 := h.2.2.2
    have h_quarter_sum : ∀ (z : ENNReal), z / 4 + z / 4 + z / 4 + z / 4 = z := by
      intro z
      let x := z / 4
      have h_add2 : x + x = (2 : ENNReal) * x := by
        have h : (2 : ENNReal) * x = x + x := two_mul x
        exact h.symm
      have h5 : x + x + x + x = (4 : ENNReal) * x := by
        have h51 : x + x + x + x = (x + x) + (x + x) := by
          rw [add_assoc, add_assoc]
        rw [h51]
        have h52 : (x + x) + (x + x) = (2 : ENNReal) * x + (2 : ENNReal) * x := by
          congr 1
        rw [h52]
        have h53 : (2 : ENNReal) * x + (2 : ENNReal) * x = (4 : ENNReal) * x := by
          rw [← add_mul]
          norm_num
        exact h53
      have h6 : (4 : ENNReal) * x = z :=
        ENNReal.mul_div_cancel (by norm_num) (by norm_num)
      exact Eq.trans h5 h6
    have h_sum_lt : νY S1 + νY S2 + νY S3 + νY S4 < νY Theta_rem := by
      have h12 : νY S1 + νY S2 < νY Theta_rem / 4 + νY Theta_rem / 4 :=
        ENNReal.add_lt_add h1 h2
      have h123 : (νY S1 + νY S2) + νY S3 <
          (νY Theta_rem / 4 + νY Theta_rem / 4) + νY Theta_rem / 4 :=
        ENNReal.add_lt_add h12 h3
      have h5 : νY S1 + νY S2 + νY S3 + νY S4 <
          νY Theta_rem / 4 + νY Theta_rem / 4 + νY Theta_rem / 4 + νY Theta_rem / 4 := by
        have h_assoc1 : νY S1 + νY S2 + νY S3 + νY S4 =
            (νY S1 + νY S2) + νY S3 + νY S4 := by rw [add_assoc]
        have h_assoc2 : νY Theta_rem / 4 + νY Theta_rem / 4 + νY Theta_rem / 4 + νY Theta_rem / 4 =
            (νY Theta_rem / 4 + νY Theta_rem / 4) + νY Theta_rem / 4 + νY Theta_rem / 4 := by rw [add_assoc]
        rw [h_assoc1, h_assoc2]
        exact ENNReal.add_lt_add h123 h4
      rw [h_quarter_sum (νY Theta_rem)] at h5
      exact h5
    exact not_le.mpr h_sum_lt h_sum_ge

  -- Step 7: Mass bound helper
  have h_eighth : ∀ (z : ENNReal),
      (1 / 4 : ENNReal) * ((1 / 2 : ENNReal) * z) = (1 / 8 : ENNReal) * z := by
    intro z
    have h9 : (1 / 4 : ENNReal) * (1 / 2 : ENNReal) = (1 / 8 : ENNReal) := by
      have h91 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4 : ℝ) := by simp
      have h92 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
      have h93 : (1 / 8 : ENNReal) = ENNReal.ofReal (1 / 8 : ℝ) := by simp
      rw [h91, h92, h93]
      have h94 : ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (1 / 2 : ℝ) =
          ENNReal.ofReal ((1 / 4 : ℝ) * (1 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / 4 by norm_num)]
      rw [h94]
      norm_num
    have h10 : (1 / 4 : ENNReal) * ((1 / 2 : ENNReal) * z) =
        ((1 / 4 : ENNReal) * (1 / 2 : ENNReal)) * z := by
      rw [mul_assoc]
    rw [h10, h9]

  have h_mass_bound : ∀ (S : Set ℝ), νY S ≥ νY Theta_rem / 4 →
      νY S ≥ (1 / 8 : ENNReal) * νY Theta_bad' := by
    intro S hS
    calc νY S
      ≥ νY Theta_rem / 4 := hS
    _ = (1 / 4 : ENNReal) * νY Theta_rem := by
      have hdiv : νY Theta_rem / 4 = (1 / 4 : ENNReal) * νY Theta_rem := by
        have h1 : νY Theta_rem / 4 = νY Theta_rem * (1 / 4 : ENNReal) := by
          simp [div_eq_mul_inv]
        rw [h1, mul_comm]
      exact hdiv
    _ ≥ (1 / 4 : ENNReal) * ((1 / 2 : ENNReal) * νY Theta_bad') := by
      gcongr
    _ = (1 / 8 : ENNReal) * νY Theta_bad' := h_eighth (νY Theta_bad')

  rcases h_pigeonhole with (hS | hS | hS | hS)

  -- Sector 1
  · exact ⟨r, hr_pos, hδ_le_r, h_r_pow, 0, S1, hS1_sub, h1_finite, h1_finite.isClosed,
      h_mass_bound S1 hS, fun y hy => hy.2,
      fun y hy => sector_t_bounds 0 x hy.2,
      fun y hy U V => sector_projection_identity 0 x hy.2 U V⟩
  -- Sector 2
  · exact ⟨r, hr_pos, hδ_le_r, h_r_pow, 1, S2, hS2_sub, h2_finite, h2_finite.isClosed,
      h_mass_bound S2 hS, fun y hy => hy.2,
      fun y hy => sector_t_bounds 1 x hy.2,
      fun y hy U V => sector_projection_identity 1 x hy.2 U V⟩
  -- Sector 3
  · exact ⟨r, hr_pos, hδ_le_r, h_r_pow, 2, S3, hS3_sub, h3_finite, h3_finite.isClosed,
      h_mass_bound S3 hS, fun y hy => hy.2,
      fun y hy => sector_t_bounds 2 x hy.2,
      fun y hy U V => sector_projection_identity 2 x hy.2 U V⟩
  -- Sector 4
  · exact ⟨r, hr_pos, hδ_le_r, h_r_pow, 3, S4, hS4_sub, h4_finite, h4_finite.isClosed,
      h_mass_bound S4 hS, fun y hy => hy.2,
      fun y hy => sector_t_bounds 3 x hy.2,
      fun y hy U V => sector_projection_identity 3 x hy.2 U V⟩

end ProductLikeIncidence.ProductReduction
