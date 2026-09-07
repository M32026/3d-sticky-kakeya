import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectionFrostmanHelpers
import MyLeanRepo.Kakeya.Cinematic.Section5.MaximalSeparatedCover

/-!
# Cluster cover and packing bound for collapsed parameter points

Given active tubes with bounded parameters, construct a maximal w-separated
center set of their collapsed parameter points, assign each active tube to a
nearby center, and prove the explicit O(w^-3) packing bound.

Whiteprint node: cluster_cover_packing.
-/

noncomputable section

namespace Kakeya.Assouad

/--
If two real numbers have the same floor, their absolute difference is < 1.
-/
private lemma same_floor_abs_lt_one (x y : ℝ) (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  let n : ℤ := ⌊x⌋
  have h1 : (n : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
  have hy : ⌊y⌋ = n := h.symm
  have h3 : (n : ℝ) ≤ y := by
    have h4 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    rw [hy] at h4
    exact h4
  have h4 : y < (n : ℝ) + 1 := by
    have h5 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [hy] at h5
    exact h5
  have h5 : x - y < 1 := by linarith
  have h6 : y - x < 1 := by linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/--
For one coordinate: if `⌊x * scale⌋ = ⌊y * scale⌋` and `scale > 0`,
then `|x - y| < 1 / scale`.
-/
private lemma same_floor_coord_lt (x y scale : ℝ) (hscale_pos : 0 < scale)
    (h : ⌊x * scale⌋ = ⌊y * scale⌋) : |x - y| < 1 / scale := by
  have h1 : |x * scale - y * scale| < 1 := same_floor_abs_lt_one (x * scale) (y * scale) h
  have h2 : |x - y| * scale < 1 := by
    have h3 : |x * scale - y * scale| = |x - y| * scale := by
      calc |x * scale - y * scale|
          = |(x - y) * scale| := by ring_nf
        _ = |x - y| * |scale| := by rw [abs_mul]
        _ = |x - y| * scale := by rw [abs_of_pos hscale_pos]
    rw [h3] at h1
    exact h1
  have h4 : |x - y| < 1 / scale := by
    calc |x - y|
        = (|x - y| * scale) / scale := by
          field_simp [hscale_pos.ne']
      _ < 1 / scale := by gcongr
  exact h4

/--
Grid packing bound: any w-separated subset of [-1/2,1/2]^3 in `ℝ^3`
has cardinality at most `64 / w^3`.

Uses a grid of side `w/2`: each cell has diameter `w√3/2 < w`, so at most
one separated point per cell. There are at most `(4/w)^3 = 64/w^3` cells.
-/
lemma separated3_packing_bound {w : ℝ} (hw_pos : 0 < w) (hw_le_one : w ≤ 1)
    {A : DiscreteSet 3}
    (h_sep : DiscreteSet.IsDeltaSeparated A w)
    (h_box : ∀ p ∈ A, |p 0| ≤ 1 / 2 ∧ |p 1| ≤ 1 / 2 ∧ |p 2| ≤ 1 / 2) :
    A.enncard ≤ 64 * Kakeya.realRpowENN w (-3) := by
  let scale : ℝ := 2 / w
  have hscale_pos : 0 < scale := by positivity
  let gridCell : Point 3 → ℤ × ℤ × ℤ := fun p =>
    (⌊p 0 * scale⌋, ⌊p 1 * scale⌋, ⌊p 2 * scale⌋)
  have h_side : 1 / scale = w / 2 := by
    dsimp only [scale]
    field_simp [hw_pos.ne']
  have h_dist_lt : ∀ (p q : Point 3), gridCell p = gridCell q → dist p q < w := by
    intro p q h_eq
    have h0 : ⌊p 0 * scale⌋ = ⌊q 0 * scale⌋ := by
      simp [gridCell] at h_eq <;> tauto
    have h1 : ⌊p 1 * scale⌋ = ⌊q 1 * scale⌋ := by
      simp [gridCell] at h_eq <;> tauto
    have h2 : ⌊p 2 * scale⌋ = ⌊q 2 * scale⌋ := by
      simp [gridCell] at h_eq <;> tauto
    have d0 : |p 0 - q 0| < w / 2 := by
      have h := same_floor_coord_lt (p 0) (q 0) scale hscale_pos h0
      rw [h_side] at h
      exact h
    have d1 : |p 1 - q 1| < w / 2 := by
      have h := same_floor_coord_lt (p 1) (q 1) scale hscale_pos h1
      rw [h_side] at h
      exact h
    have d2 : |p 2 - q 2| < w / 2 := by
      have h := same_floor_coord_lt (p 2) (q 2) scale hscale_pos h2
      rw [h_side] at h
      exact h
    have h_norm_sq : ‖p - q‖ ^ 2 < 3 * (w / 2) ^ 2 := by
      have h4 : ‖p - q‖ ^ 2 = ∑ i : Fin 3, ((p - q) i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq (p - q)
      rw [h4]
      simp [Fin.sum_univ_succ]
      have h5 : (p 0 - q 0) ^ 2 < (w / 2) ^ 2 := by
        have h51 : |p 0 - q 0| < w / 2 := d0
        have h : |p 0 - q 0| ^ 2 < (w / 2) ^ 2 := by gcongr
        rw [sq_abs] at h; exact h
      have h6 : (p 1 - q 1) ^ 2 < (w / 2) ^ 2 := by
        have h61 : |p 1 - q 1| < w / 2 := d1
        have h : |p 1 - q 1| ^ 2 < (w / 2) ^ 2 := by gcongr
        rw [sq_abs] at h; exact h
      have h7 : (p 2 - q 2) ^ 2 < (w / 2) ^ 2 := by
        have h71 : |p 2 - q 2| < w / 2 := d2
        have h : |p 2 - q 2| ^ 2 < (w / 2) ^ 2 := by gcongr
        rw [sq_abs] at h; exact h
      linarith
    have h_norm : ‖p - q‖ < w := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        norm_nonneg (p - q)]
    simpa [dist_eq_norm] using h_norm
  have h_inj : Set.InjOn gridCell (A : Set (Point 3)) := by
    intro p hp q hq h_eq
    by_cases hne : p ≠ q
    · have h_sep' : w ≤ dist p q := h_sep hp hq hne
      have h_contra : dist p q < w := h_dist_lt p q h_eq
      linarith
    · have h_eq_pq : p = q := by tauto
      exact h_eq_pq
  let range_k : Finset ℤ := Finset.Icc (⌊-1 / w⌋) (⌊1 / w⌋)
  have h_neg_le_pos : -1 / w ≤ 1 / w := by
    have h_pos : 0 < w := hw_pos
    have h : (-1 : ℝ) ≤ 1 := by norm_num
    exact div_le_div_of_nonneg_right h h_pos.le
  have h_a_le_b : ⌊-1 / w⌋ ≤ ⌊1 / w⌋ := Int.floor_le_floor h_neg_le_pos
  have h_int_card_formula : ∀ (a b : ℤ), a ≤ b →
      ((Finset.Icc a b).card : ℝ) = (b : ℝ) - (a : ℝ) + 1 := by
    intro a b h
    have h2 : (Finset.Icc a b).card = (b + 1 - a).toNat := by
      simp
    rw [h2]
    have h3 : 0 ≤ b + 1 - a := by linarith
    have h41 : ((b + 1 - a).toNat : ℤ) = (b + 1 - a) := Int.toNat_of_nonneg h3
    have h4 : ((b + 1 - a).toNat : ℝ) = ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast h41
    rw [h4]
    simp [Int.cast_add, Int.cast_sub, Int.cast_one]
    <;> ring
  have h_range_k_card : (range_k.card : ℝ) ≤ 4 / w := by
    rw [h_int_card_formula ⌊-1 / w⌋ ⌊1 / w⌋ h_a_le_b]
    have h2 : (⌊1 / w⌋ : ℝ) ≤ 1 / w := Int.floor_le (1 / w)
    have h3 : (⌊-1 / w⌋ : ℝ) ≥ -1 / w - 1 := by
      have h4 : -1 / w - 1 < (⌊-1 / w⌋ : ℝ) := Int.sub_one_lt_floor (-1 / w)
      exact h4.le
    have h5 : 2 ≤ 2 / w := by
      have h6 : 0 < w := hw_pos
      have h7 : w ≤ 1 := hw_le_one
      calc 2 = 2 / 1 := by norm_num
           _ ≤ 2 / w := by gcongr
    calc
      (⌊1 / w⌋ : ℝ) - (⌊-1 / w⌋ : ℝ) + 1
        ≤ (1 / w) - (-1 / w - 1) + 1 := by gcongr
      _ = 2 / w + 2 := by ring
      _ ≤ 2 / w + 2 / w := by gcongr
      _ = 4 / w := by ring
  let range : Finset (ℤ × ℤ × ℤ) := range_k ×ˢ range_k ×ˢ range_k
  have h_range_card : (range.card : ℝ) ≤ (4 / w) ^ 3 := by
    have h1 : range.card = (range_k.card) ^ 3 := by
      simp [range, Finset.card_product] <;> ring
    rw [h1]
    have h2 : (range_k.card : ℝ) ≤ 4 / w := h_range_k_card
    have h3 : ((range_k.card : ℝ) ^ 3) ≤ (4 / w) ^ 3 := by gcongr
    exact_mod_cast h3
  have h_scale_pos2 : (1 / 2 : ℝ) * scale = 1 / w := by
    dsimp only [scale]; field_simp [hw_pos.ne'] <;> ring
  have h_scale_neg2 : (-1 / 2 : ℝ) * scale = -1 / w := by
    dsimp only [scale]; field_simp [hw_pos.ne'] <;> ring
  have h_coord_in_range : ∀ (p : Point 3),
      (|p 0| ≤ 1 / 2 ∧ |p 1| ≤ 1 / 2 ∧ |p 2| ≤ 1 / 2) →
      ∀ k : Fin 3, ⌊p k * scale⌋ ∈ range_k := by
    intro p hbox k
    have h_abs : |p k| ≤ 1 / 2 := by fin_cases k <;> tauto
    have h_bounds := abs_le.mp h_abs
    have h_lower : -1 / w ≤ p k * scale := by
      have h' : (-1 / 2 : ℝ) * scale ≤ p k * scale := by
        gcongr <;> linarith [h_bounds.1]
      rw [h_scale_neg2] at h'; exact h'
    have h_upper : p k * scale ≤ 1 / w := by
      have h' : p k * scale ≤ (1 / 2 : ℝ) * scale := by
        gcongr <;> linarith [h_bounds.2]
      rw [h_scale_pos2] at h'; exact h'
    simp only [range_k, Finset.mem_Icc]
    constructor
    · exact Int.floor_le_floor h_lower
    · exact Int.floor_le_floor h_upper
  have h_image_subset : A.image gridCell ⊆ range := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    have hbox := h_box p hp
    have h0 := h_coord_in_range p hbox 0
    have h1 := h_coord_in_range p hbox 1
    have h2 := h_coord_in_range p hbox 2
    simp only [range, Finset.mem_product]
    exact ⟨h0, h1, h2⟩
  have h_card_image : (A.image gridCell).card = A.card :=
    Finset.card_image_of_injOn h_inj
  have h_card_le : A.card ≤ range.card := by
    rw [←h_card_image]
    exact Finset.card_le_card h_image_subset
  have h_card_real : (A.card : ℝ) ≤ 64 / w ^ 3 := by
    have h4 : (A.card : ℝ) ≤ (range.card : ℝ) := by exact_mod_cast h_card_le
    have h5 : (range.card : ℝ) ≤ (4 / w) ^ 3 := h_range_card
    have h6 : (4 / w) ^ 3 = 64 / w ^ 3 := by
      field_simp [hw_pos.ne'] <;> norm_num
    rw [h6] at h5
    linarith
  have h_main_real : (A.card : ℝ) ≤ 64 / w ^ 3 := h_card_real
  have h_rpow : Kakeya.realRpowENN w (-3) = ENNReal.ofReal (1 / w ^ 3) := by
    simp [Kakeya.realRpowENN]
    <;> field_simp [hw_pos.ne']
  rw [h_rpow]
  have h_pos : 0 < 1 / w ^ 3 := by positivity
  have h9 : (A.card : ENNReal) ≤ ENNReal.ofReal (64 / w ^ 3) := by
    have h10 : (A.card : ENNReal) = ENNReal.ofReal (A.card : ℝ) := by
      simp
    rw [h10]
    apply ENNReal.ofReal_le_ofReal
    exact h_main_real
  have h11 : (64 / w ^ 3 : ℝ) = 64 * (1 / w ^ 3) := by
    field_simp [hw_pos.ne'] <;> ring
  have h12 : ENNReal.ofReal (64 / w ^ 3) =
      64 * ENNReal.ofReal (1 / w ^ 3) := by
    rw [h11]
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 64 by norm_num)]
    <;> norm_cast
  rw [h12] at h9
  exact h9

/--
Output of the cluster cover construction: active tubes, maximal w-separated
centers, and an assignment of each active tube to a nearby center.
-/
structure ParameterClusterCoverData
    {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (w : ℝ) where
  active : Finset (Fin F.card)
  centers : DiscreteSet 3
  assign : Fin F.card → Point 3
  active_positiveMass : ∀ i, i ∈ active ↔ Y.carrier i ≠ ∅
  centers_separated : DiscreteSet.IsDeltaSeparated centers w
  centers_in_unitBall : DiscreteSet.IsInUnitBall centers
  centers_card_upper : centers.enncard ≤ 100000 * Kakeya.realRpowENN w (-3)
  assign_mem : ∀ i, i ∈ active → assign i ∈ centers
  assign_close : ∀ i, i ∈ active → dist (tubeParameterPoint3 i) (assign i) ≤ w
  assign_self : ∀ i, i ∈ active → tubeParameterPoint3 i ∈ centers → assign i = tubeParameterPoint3 i
  centers_subset_image : centers ⊆ active.image tubeParameterPoint3

/--
Construct a maximal w-separated cover of the collapsed parameter points of
active tubes, with packing bound and assignment.
-/
def parameter_cluster_cover
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (h_params : ∀ i : Fin F.card,
      |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
      |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2)
    (w : ℝ) (hw_pos : 0 < w) (hw_small : 100 * w ≤ 1) :
    ParameterClusterCoverData F Y w := by
  classical
  let active : Finset (Fin F.card) :=
    Finset.univ.filter (fun i => Y.carrier i ≠ ∅)
  let S : Finset (Point 3) := active.image tubeParameterPoint3
  have h_w_le_one : w ≤ 1 := by linarith
  let h_main := Kakeya.Cinematic.exists_maximal_separated_cover (S := S) (t := w) hw_pos
  let centers : Finset (Point 3) := Classical.choose h_main
  have h_centers_subset : centers ⊆ S := (Classical.choose_spec h_main).1
  have h_strict_sep : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → w < dist c d :=
    (Classical.choose_spec h_main).2.1
  have h_cover : ∀ x ∈ S, ∃ c ∈ centers, dist x c ≤ w :=
    (Classical.choose_spec h_main).2.2
  let centers' : DiscreteSet 3 := centers
  have h_sep : DiscreteSet.IsDeltaSeparated centers' w := by
    intro x hx y hy hne
    have h : w < dist x y := h_strict_sep x hx y hy hne
    exact h.le
  have h_centers_in_S : centers' ⊆ S := h_centers_subset
  have h_box : ∀ p ∈ centers', |p 0| ≤ 1 / 2 ∧ |p 1| ≤ 1 / 2 ∧ |p 2| ≤ 1 / 2 := by
    intro p hp
    have h_p_in_S : p ∈ S := h_centers_in_S hp
    rcases Finset.mem_image.mp h_p_in_S with ⟨i, hi, rfl⟩
    have hpa := h_params i
    dsimp only [tubeParameterPoint3, point3]
    have ha : |(tubeParams i).a / 24| ≤ 1 / 2 := by
      have h : |(tubeParams i).a| ≤ 12 := hpa.1
      calc |(tubeParams i).a / 24|
          = |(tubeParams i).a| / 24 := by simp [abs_div]
        _ ≤ 12 / 24 := by gcongr
        _ = 1 / 2 := by norm_num
    have hb : |(tubeParams i).b / 24| ≤ 1 / 2 := by
      have h : |(tubeParams i).b| ≤ 12 := hpa.2.1
      calc |(tubeParams i).b / 24|
          = |(tubeParams i).b| / 24 := by simp [abs_div]
        _ ≤ 12 / 24 := by gcongr
        _ = 1 / 2 := by norm_num
    have hd : |(tubeParams i).d / 4| ≤ 1 / 2 := by
      have h : |(tubeParams i).d| ≤ 2 := hpa.2.2.2
      calc |(tubeParams i).d / 4|
          = |(tubeParams i).d| / 4 := by simp [abs_div]
        _ ≤ 2 / 4 := by gcongr
        _ = 1 / 2 := by norm_num
    have h_coord0 : |(tubeParameterPoint3 i) 0| ≤ 1 / 2 := by
      simpa [tubeParameterPoint3, point3] using ha
    have h_coord1 : |(tubeParameterPoint3 i) 1| ≤ 1 / 2 := by
      simpa [tubeParameterPoint3, point3] using hb
    have h_coord2 : |(tubeParameterPoint3 i) 2| ≤ 1 / 2 := by
      simpa [tubeParameterPoint3, point3] using hd
    exact ⟨h_coord0, h_coord1, h_coord2⟩
  have h_unitBall : DiscreteSet.IsInUnitBall centers' := by
    intro p hp
    have hbox := h_box p hp
    exact half_coords_implies_unitBall p hbox
  have h_packing64 : centers'.enncard ≤ 64 * Kakeya.realRpowENN w (-3) :=
    separated3_packing_bound hw_pos h_w_le_one h_sep h_box
  have h_packing : centers'.enncard ≤ 100000 * Kakeya.realRpowENN w (-3) := by
    have h64 : (64 : ENNReal) ≤ 100000 := by norm_num
    calc
      centers'.enncard ≤ 64 * Kakeya.realRpowENN w (-3) := h_packing64
      _ ≤ 100000 * Kakeya.realRpowENN w (-3) := by gcongr
  let assign_fun (i : Fin F.card) (hi : i ∈ active) : Point 3 :=
    if h : tubeParameterPoint3 i ∈ centers then tubeParameterPoint3 i
    else Classical.choose (h_cover (tubeParameterPoint3 i)
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have h_assign_mem : ∀ (i : Fin F.card) (hi : i ∈ active), assign_fun i hi ∈ centers' := by
    intro i hi
    dsimp only [assign_fun]
    by_cases h : tubeParameterPoint3 i ∈ centers
    · rw [dif_pos h] <;> exact h
    · rw [dif_neg h]
      exact (Classical.choose_spec (h_cover (tubeParameterPoint3 i)
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩))).1
  have h_assign_close : ∀ (i : Fin F.card) (hi : i ∈ active),
      dist (tubeParameterPoint3 i) (assign_fun i hi) ≤ w := by
    intro i hi
    dsimp only [assign_fun]
    by_cases h : tubeParameterPoint3 i ∈ centers
    · rw [dif_pos h, dist_self] <;> exact hw_pos.le
    · rw [dif_neg h]
      exact (Classical.choose_spec (h_cover (tubeParameterPoint3 i)
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩))).2
  let assign : Fin F.card → Point 3 := fun i =>
    if hi : i ∈ active then assign_fun i hi else 0
  have h_assign_mem' : ∀ i, i ∈ active → assign i ∈ centers' := by
    intro i hi
    have h : assign i = assign_fun i hi := by
      dsimp only [assign]
      rw [dif_pos hi]
    rw [h]
    exact h_assign_mem i hi
  have h_assign_close' : ∀ i, i ∈ active → dist (tubeParameterPoint3 i) (assign i) ≤ w := by
    intro i hi
    have h : assign i = assign_fun i hi := by
      dsimp only [assign]
      rw [dif_pos hi]
    rw [h]
    exact h_assign_close i hi
  have h_assign_self' : ∀ i, i ∈ active → tubeParameterPoint3 i ∈ centers' → assign i = tubeParameterPoint3 i := by
    intro i hi hcent
    have h1 : assign i = assign_fun i hi := by
      dsimp only [assign]
      rw [dif_pos hi]
    rw [h1]
    dsimp only [assign_fun]
    rw [dif_pos hcent]
  exact {
    active := active
    centers := centers'
    assign := assign
    active_positiveMass := by
      intro i
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    centers_separated := h_sep
    centers_in_unitBall := h_unitBall
    centers_card_upper := h_packing
    assign_mem := h_assign_mem'
    assign_close := h_assign_close'
    assign_self := h_assign_self'
    centers_subset_image := h_centers_in_S
  }

end Kakeya.Assouad
