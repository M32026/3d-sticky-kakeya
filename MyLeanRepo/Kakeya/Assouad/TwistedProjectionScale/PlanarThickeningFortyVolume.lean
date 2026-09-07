import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
WZ2 Section 7: absorb the factor-forty planar enlargement used by the
parameter-certificate relation-induced projection geometry.

An `83 × 83` grid of `r`-spaced translation vectors covers every displacement
of norm at most `40r` with residual norm at most `r`.  Finite subadditivity
and translation invariance of planar Lebesgue measure then give the explicit
`6889 = 83^2` volume loss.
-/


namespace Kakeya.Assouad

private noncomputable def mkPoint2 (x y : ℝ) : Point2 :=
  x • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
  y • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

private lemma mkPoint2_coord (x y : ℝ) :
    (mkPoint2 x y) 0 = x ∧ (mkPoint2 x y) 1 = y := by
  have h0 : (mkPoint2 x y) 0 = x := by simp [mkPoint2]
  have h1 : (mkPoint2 x y) 1 = y := by simp [mkPoint2]
  exact ⟨h0, h1⟩

private lemma mul_abs_le_half {r x : ℝ} (hr : 0 < r) (hx : |x| ≤ 1 / 2) :
    r * |x| ≤ r / 2 := by
  calc
    r * |x| ≤ r * (1 / 2) := mul_le_mul_of_nonneg_left hx hr.le
    _ = r / 2 := by ring

private lemma nonneg_le_of_sq_le_half {x r : ℝ}
    (hx : 0 ≤ x) (hr : 0 < r) (hxr : x ^ 2 ≤ r ^ 2 / 2) :
    x ≤ r := by
  nlinarith

private abbrev GridIndex := Fin 83 × Fin 83

private def gridCoord (i : Fin 83) : ℤ :=
  (i : ℤ) - 41

private noncomputable def gridPoint (r : ℝ) (p : GridIndex) : Point2 :=
  mkPoint2 ((gridCoord p.1 : ℝ) * r) ((gridCoord p.2 : ℝ) * r)

private noncomputable def translatedThickening
    (E : Set Point2) (r : ℝ) (p : GridIndex) : Set Point2 :=
  (fun z : Point2 => gridPoint r p + z) '' Metric.cthickening r E

private noncomputable def nearestGridInteger (x : ℝ) : ℤ :=
  Int.floor (x + 1 / 2)

private noncomputable def translatedCover (E : Set Point2) (r : ℝ) : Set Point2 :=
  ⋃ p : GridIndex, translatedThickening E r p

private lemma mem_translatedCover {E : Set Point2} {r : ℝ} {p : GridIndex} {x : Point2}
    (hx : x ∈ translatedThickening E r p) :
    x ∈ translatedCover E r := by
  change x ∈ ⋃ q : GridIndex, translatedThickening E r q
  exact Set.mem_iUnion_of_mem p hx

private lemma nearest_grid_integer (x : ℝ) (hx : |x| ≤ 40) :
    -41 ≤ nearestGridInteger x ∧ nearestGridInteger x ≤ 41 ∧
      |x - (nearestGridInteger x : ℤ)| ≤ 1 / 2 := by
  let i : ℤ := nearestGridInteger x
  have h1 : (i : ℝ) ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
  have h2 : x + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one (x + 1 / 2)
  have hdist : |x - (i : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hi_abs : |(i : ℝ)| ≤ 40 + 1 / 2 := by
    have hi_eq : (i : ℝ) = x + ((i : ℝ) - x) := by ring
    rw [hi_eq]
    have hsum : |x + ((i : ℝ) - x)| ≤ |x| + |(i : ℝ) - x| :=
      abs_add_le x ((i : ℝ) - x)
    have hsymm : |(i : ℝ) - x| = |x - (i : ℝ)| := by
      rw [show (i : ℝ) - x = -(x - (i : ℝ)) by ring, abs_neg]
    rw [hsymm] at hsum
    linarith
  have hi_upper : (i : ℝ) ≤ 40 + 1 / 2 := (abs_le.mp hi_abs).2
  have hi_lower : -(40 + 1 / 2 : ℝ) ≤ (i : ℝ) := (abs_le.mp hi_abs).1
  have hi_min : -41 ≤ i := by
    by_contra h
    have hi : i ≤ -42 := by omega
    have hi_real : (i : ℝ) ≤ -42 := by exact_mod_cast hi
    linarith
  have hi_max : i ≤ 41 := by
    by_contra h
    have hi : i ≥ 42 := by omega
    have hi_real : (i : ℝ) ≥ 42 := by exact_mod_cast hi
    linarith
  exact ⟨hi_min, hi_max, hdist⟩

private def boundedGridIndex (i : ℤ) (hlo : -41 ≤ i) (hhi : i ≤ 41) : Fin 83 :=
  ⟨(i + 41).toNat, by omega⟩

private lemma gridCoord_boundedGridIndex (i : ℤ) (hlo : -41 ≤ i) (hhi : i ≤ 41) :
    gridCoord (boundedGridIndex i hlo hhi) = i := by
  simp only [gridCoord, boundedGridIndex, Fin.val_mk]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

private lemma exists_nearby_grid_index (x : ℝ) (hx : |x| ≤ 40) :
    ∃ i : Fin 83, |x - (gridCoord i : ℤ)| ≤ 1 / 2 := by
  obtain ⟨hlo, hhi, hdist⟩ := nearest_grid_integer x hx
  let i : Fin 83 := boundedGridIndex (nearestGridInteger x) hlo hhi
  refine ⟨i, ?_⟩
  rw [show gridCoord i = nearestGridInteger x from
    gridCoord_boundedGridIndex (nearestGridInteger x) hlo hhi]
  exact hdist

private lemma coordinate_div_bound (r : ℝ) (hr : 0 < r) (v : Point2)
    (hv : ‖v‖ ≤ 40 * r) (k : Fin 2) :
    |v k / r| ≤ 40 := by
  have hvk : |v k| ≤ 40 * r := by
    have h : ‖v k‖ ≤ ‖v‖ := PiLp.norm_apply_le v k
    simpa [Real.norm_eq_abs] using h.trans hv
  rw [abs_div, abs_of_pos hr]
  calc
    |v k| / r ≤ (40 * r) / r := div_le_div_of_nonneg_right hvk hr.le
    _ = 40 := by field_simp [hr.ne']

private lemma exists_close_grid_point (r : ℝ) (hr : 0 < r) (v : Point2)
    (hv : ‖v‖ ≤ 40 * r) :
    ∃ p : GridIndex, ‖v - gridPoint r p‖ ≤ r := by
  obtain ⟨i, hi⟩ := exists_nearby_grid_index (v 0 / r)
    (coordinate_div_bound r hr v hv 0)
  obtain ⟨j, hj⟩ := exists_nearby_grid_index (v 1 / r)
    (coordinate_div_bound r hr v hv 1)
  refine ⟨(i, j), ?_⟩
  have hg0 : (gridPoint r (i, j)) 0 = (gridCoord i : ℝ) * r := by
    simp [gridPoint, mkPoint2_coord]
  have hg1 : (gridPoint r (i, j)) 1 = (gridCoord j : ℝ) * r := by
    simp [gridPoint, mkPoint2_coord]
  have hcoord0 : |v 0 - (gridPoint r (i, j)) 0| ≤ |r / 2| := by
    rw [hg0, abs_of_pos (by positivity : 0 < r / 2)]
    have hscale : v 0 - (gridCoord i : ℝ) * r =
        r * (v 0 / r - (gridCoord i : ℝ)) := by
      field_simp [hr.ne'] <;> ring
    rw [hscale, abs_mul, abs_of_pos hr]
    exact mul_abs_le_half hr hi
  have hcoord1 : |v 1 - (gridPoint r (i, j)) 1| ≤ |r / 2| := by
    rw [hg1, abs_of_pos (by positivity : 0 < r / 2)]
    have hscale : v 1 - (gridCoord j : ℝ) * r =
        r * (v 1 / r - (gridCoord j : ℝ)) := by
      field_simp [hr.ne'] <;> ring
    rw [hscale, abs_mul, abs_of_pos hr]
    exact mul_abs_le_half hr hj
  have hnorm_sq : ‖v - gridPoint r (i, j)‖ ^ 2 ≤ r ^ 2 / 2 := by
    have hcoords : ‖v - gridPoint r (i, j)‖ ^ 2 =
        (v 0 - (gridPoint r (i, j)) 0) ^ 2 +
          (v 1 - (gridPoint r (i, j)) 1) ^ 2 := by
      have h := EuclideanSpace.real_norm_sq_eq (v - gridPoint r (i, j))
      rw [h, Fin.sum_univ_two] <;> rfl
    rw [hcoords]
    have hsq0 : (v 0 - (gridPoint r (i, j)) 0) ^ 2 ≤ (r / 2) ^ 2 :=
      sq_le_sq.mpr hcoord0
    have hsq1 : (v 1 - (gridPoint r (i, j)) 1) ^ 2 ≤ (r / 2) ^ 2 :=
      sq_le_sq.mpr hcoord1
    nlinarith
  have hnorm : ‖v - gridPoint r (i, j)‖ ≤ r :=
    nonneg_le_of_sq_le_half (norm_nonneg _) hr hnorm_sq
  exact hnorm

private lemma infEDist_translate (a x : Point2) (A : Set Point2) :
    Metric.infEDist x ((fun y : Point2 => a + y) '' A) =
      Metric.infEDist (x - a) A := by
  have h_iso : Isometry (fun y : Point2 => a + y) := by
    intro y z
    simp [edist_dist, dist_eq_norm]
  have h := Metric.infEDist_image h_iso (x := x - a) (t := A)
  have h_sum : a + (x - a) = x := by abel
  rw [h_sum] at h
  exact h

private lemma cthickening_closure_eq (r : ℝ) (A : Set Point2) :
    Metric.cthickening r (closure A) = Metric.cthickening r A := by
  ext x
  simp only [Metric.mem_cthickening_iff]
  rw [Metric.infEDist_closure]

private lemma cthickening_translate (r : ℝ) (a : Point2) (A : Set Point2) :
    Metric.cthickening r ((fun y : Point2 => a + y) '' A) =
      (fun y : Point2 => a + y) '' Metric.cthickening r A := by
  ext z
  simp only [Set.mem_image, Metric.mem_cthickening_iff, infEDist_translate]
  constructor
  · intro h
    refine ⟨z - a, h, ?_⟩
    abel
  · rintro ⟨w, hw, rfl⟩
    simpa [sub_add_cancel] using hw

private lemma forty_thickening_subset_translates (E : Set Point2) (r : ℝ) (hr : 0 < r) :
    Metric.cthickening (40 * r) E ⊆ translatedCover E r := by
  intro x hx
  have hr40 : 0 ≤ 40 * r := by positivity
  have h_union : Metric.cthickening (40 * r) E =
      ⋃ y ∈ closure E, Metric.closedBall y (40 * r) :=
    Metric.cthickening_eq_biUnion_closedBall E hr40
  rw [h_union] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨y, hy_closed, hball⟩
  have hdist : dist x y ≤ 40 * r := by
    simpa [Metric.mem_closedBall] using hball
  have hv : ‖x - y‖ ≤ 40 * r := by
    simpa [dist_eq_norm] using hdist
  obtain ⟨p, hnorm⟩ := exists_close_grid_point r hr (x - y) hv
  have himage : x ∈ translatedThickening E r p := by
    change x ∈ (fun z : Point2 => gridPoint r p + z) '' Metric.cthickening r E
    have hcenter :
        y + gridPoint r p ∈
          closure ((fun z : Point2 => gridPoint r p + z) '' E) := by
      have hclosure : (fun z : Point2 => gridPoint r p + z) '' closure E ⊆
          closure ((fun z : Point2 => gridPoint r p + z) '' E) :=
        image_closure_subset_closure_image (continuous_const.add continuous_id)
      exact hclosure ⟨y, hy_closed, by simp [add_comm]⟩
    have hcenter_dist : dist x (y + gridPoint r p) ≤ r := by
      have h_eq : x - (y + gridPoint r p) = x - y - gridPoint r p := by abel
      simpa [dist_eq_norm, h_eq] using hnorm
    have hthick :
        x ∈ Metric.cthickening r
          (closure ((fun z : Point2 => gridPoint r p + z) '' E)) :=
      Metric.mem_cthickening_of_dist_le x (y + gridPoint r p) r
        (closure ((fun z : Point2 => gridPoint r p + z) '' E)) hcenter hcenter_dist
    rw [cthickening_closure_eq,
      cthickening_translate r (gridPoint r p) E] at hthick
    exact hthick
  exact mem_translatedCover himage

private lemma volume_translate (a : Point2) (S : Set Point2) :
    MeasureTheory.volume ((fun x : Point2 => a + x) '' S) =
      MeasureTheory.volume S := by
  have h_eq :
      (fun x : Point2 => a + x) '' S = (fun y : Point2 => -a + y) ⁻¹' S := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      refine ⟨-a + z, hz, ?_⟩
      abel
  rw [h_eq]
  have h : MeasureTheory.MeasurePreserving
      (fun y : Point2 => -a + y) MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_add_left MeasureTheory.volume (-a)
  have hme : MeasurableEmbedding (fun y : Point2 => -a + y) :=
    measurableEmbedding_addLeft (-a)
  exact h.measure_preimage_emb hme S

theorem planar_thickening_forty_volume :
    PlanarThickeningFortyVolumeStatement := by
  intro E r hr
  calc
    MeasureTheory.volume (Metric.cthickening (40 * r) E)
        ≤ MeasureTheory.volume (translatedCover E r) :=
      MeasureTheory.measure_mono (forty_thickening_subset_translates E r hr)
    _ ≤ ∑ p : GridIndex,
          MeasureTheory.volume (translatedThickening E r p) :=
      MeasureTheory.measure_iUnion_fintype_le MeasureTheory.volume
        (translatedThickening E r)
    _ = ∑ _ : GridIndex, MeasureTheory.volume (Metric.cthickening r E) := by
      apply Finset.sum_congr rfl
      intro p _
      change MeasureTheory.volume
        ((fun z : Point2 => gridPoint r p + z) '' Metric.cthickening r E) =
          MeasureTheory.volume (Metric.cthickening r E)
      exact volume_translate (gridPoint r p) (Metric.cthickening r E)
    _ = (Fintype.card GridIndex : ENNReal) *
          MeasureTheory.volume (Metric.cthickening r E) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (6889 : ENNReal) * MeasureTheory.volume (Metric.cthickening r E) := by
      have hcard_nat : Fintype.card GridIndex = 6889 := by
        simp [GridIndex]
      have hcard : (Fintype.card GridIndex : ENNReal) = 6889 := by
        exact_mod_cast hcard_nat
      rw [hcard]

end Kakeya.Assouad
