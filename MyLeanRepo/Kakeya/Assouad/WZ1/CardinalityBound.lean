import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.ParameterAndExtremal
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Tactic

/-!
# Cardinality bound for WZ1 Proposition 5 Fiber Refinement

Self-contained module providing:
1. `finset_card_bound_general`: packing bound for finset of tubes with bounded bases
2. `active_tube_base_bound`: active tubes have bases in ball(0, 3)
3. `wz1_poly_card_bound`: F.card ≤ 99^6 · δ^(-6-η) via active packing + density transfer
4. `log_bound_from_poly`: small-δ threshold for logarithmic bound
5. `cardinality_bound_from_poly`: polynomial → ENNReal log bound for fine refinement
-/

noncomputable section

open MeasureTheory Metric Set Finset

namespace Kakeya.Assouad

/-! ### Grid geometry helpers -/

private def grid3 (r : ℝ) (p : Point3) : Fin 3 → ℤ :=
  fun i => ⌊(p i) / r⌋

private lemma grid3_eq_imp_dist_lt {r : ℝ} (hr : 0 < r) {p q : Point3}
    (h : grid3 r p = grid3 r q) : ‖p - q‖ < Real.sqrt 3 * r := by
  have h1 : ∀ i : Fin 3, |(p - q) i| < r := by
    intro i
    have h2 : ⌊(p i) / r⌋ = ⌊(q i) / r⌋ := congr_fun h i
    have h3 : |(p i) / r - (q i) / r| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor h2
    have h4 : |((p i) - (q i)) / r| < 1 := by
      have h5 : ((p i) - (q i)) / r = (p i) / r - (q i) / r := by ring
      rw [h5]; exact h3
    have h6 : |(p i) - (q i)| < r := by
      have h7 : |((p i) - (q i)) / r| = |(p i) - (q i)| / r := by
        rw [abs_div] <;> simp [abs_of_pos hr]
      rw [h7] at h4
      calc
        |(p i) - (q i)| = (|(p i) - (q i)| / r) * r := by field_simp [hr.ne'] <;> ring
        _ < 1 * r := by gcongr
        _ = r := by ring
    simpa using h6
  have h2 : ∑ i : Fin 3, ((p - q) i)^2 < 3 * r^2 := by
    have h4 : ∀ i : Fin 3, ((p - q) i)^2 < r^2 := by
      intro i
      have h5 : |(p - q) i| < r := h1 i
      have h6 : |(p - q) i|^2 < r^2 := by
        have h7 : 0 ≤ r := by positivity
        nlinarith [abs_nonneg ((p - q) i)]
      have h8 : |(p - q) i|^2 = ((p - q) i)^2 := by rw [sq_abs]
      rw [h8] at h6; exact h6
    have h5 : ∑ i : Fin 3, ((p - q) i)^2 < ∑ i : Fin 3, r^2 := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨0, by simp⟩
      · intro i _; exact h4 i
    simpa using h5
  have h_sum_eq : ∑ i : Fin 3, ‖(p - q) i‖ ^ 2 = ∑ i : Fin 3, ((p - q) i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h1 : ‖(p - q) i‖ = |(p - q) i| := by simp [Real.norm_eq_abs]
    rw [h1, sq_abs]
  have h_pos : 0 ≤ ∑ i : Fin 3, ((p - q) i)^2 := by positivity
  have h_norm2 : ‖p - q‖ ^ 2 = ∑ i : Fin 3, ((p - q) i)^2 := by
    have h : ‖p - q‖ = Real.sqrt (∑ i : Fin 3, ‖(p - q) i‖ ^ 2) := by
      rw [PiLp.norm_eq_of_L2] <;> rfl
    rw [h, h_sum_eq, Real.sq_sqrt h_pos]
  have h6 : ‖p - q‖ ^ 2 < 3 * r^2 := by rw [h_norm2]; exact h2
  have h7 : 0 ≤ ‖p - q‖ := by positivity
  have h8 : 0 ≤ Real.sqrt 3 * r := by positivity
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private lemma coord_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h_pos : 0 ≤ ∑ j : Fin 3, (x j)^2 := by positivity
  have h_sum_eq : ∑ j : Fin 3, ‖x j‖ ^ 2 = ∑ j : Fin 3, (x j)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    have h1 : ‖x j‖ = |x j| := by simp [Real.norm_eq_abs]
    rw [h1, sq_abs]
  have h_norm : ‖x‖ = Real.sqrt (∑ j : Fin 3, (x j)^2) := by
    rw [PiLp.norm_eq_of_L2, h_sum_eq]
  have h2 : (x i)^2 ≤ ∑ j : Fin 3, (x j)^2 := by
    have h3 : ∀ j ∈ Finset.univ, 0 ≤ (x j)^2 := by intro j _; positivity
    exact Finset.single_le_sum h3 (Finset.mem_univ i)
  have h4 : |x i|^2 ≤ ‖x‖^2 := by
    rw [sq_abs, h_norm]
    rw [Real.sq_sqrt h_pos]
    exact h2
  have h5 : 0 ≤ |x i| := by positivity
  have h6 : 0 ≤ ‖x‖ := by positivity
  nlinarith

/-! ### Finset cardinality bound -/

/-- Polynomial cardinality bound for a finset of essentially distinct tubes
whose bases lie in a ball of radius `R`. -/
lemma finset_card_bound_general
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) (hδ_small : δ < 1 / 16)
    {F : Kakeya.Streamlined.TubeFamily δ} {R : ℝ} (hR : 1 ≤ R)
    (s : Finset (Fin F.card))
    (h_bases : ∀ i ∈ s, ‖(F.tube i).base‖ ≤ R)
    (hF_distinct : F.IsEssentiallyDistinct) :
    (s.card : ℝ) ≤ (32 * R + 3)^6 * δ^(-6 : ℝ) := by
  set r : ℝ := δ / 16 with hr_def
  have hr_pos : 0 < r := by positivity
  have hsqrt3_lt_2 : Real.sqrt 3 < 2 := by
    have h : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h2 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
    linarith
  let baseEncode (i : Fin F.card) : ℤ × ℤ × ℤ :=
    (grid3 r (F.tube i).base 0, grid3 r (F.tube i).base 1, grid3 r (F.tube i).base 2)
  let dirEncode (i : Fin F.card) : ℤ × ℤ × ℤ :=
    (grid3 r (F.tube i).direction 0, grid3 r (F.tube i).direction 1, grid3 r (F.tube i).direction 2)
  let encode6 (i : Fin F.card) : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) :=
    (baseEncode i, dirEncode i)
  have h_inj : Set.InjOn encode6 s := by
    intro i _ j _ h_eq
    by_contra h_ne
    have h_be : baseEncode i = baseEncode j := congr_arg Prod.fst h_eq
    have h_de : dirEncode i = dirEncode j := congr_arg Prod.snd h_eq
    have h_be' : grid3 r (F.tube i).base 0 = grid3 r (F.tube j).base 0 ∧
        grid3 r (F.tube i).base 1 = grid3 r (F.tube j).base 1 ∧
        grid3 r (F.tube i).base 2 = grid3 r (F.tube j).base 2 := by
      simpa [baseEncode, Prod.ext_iff] using h_be
    rcases h_be' with ⟨h_be1, h_be2, h_be3⟩
    have h_base_grid : grid3 r (F.tube i).base = grid3 r (F.tube j).base := by
      funext k; fin_cases k <;> tauto
    have h_de' : grid3 r (F.tube i).direction 0 = grid3 r (F.tube j).direction 0 ∧
        grid3 r (F.tube i).direction 1 = grid3 r (F.tube j).direction 1 ∧
        grid3 r (F.tube i).direction 2 = grid3 r (F.tube j).direction 2 := by
      simpa [dirEncode, Prod.ext_iff] using h_de
    rcases h_de' with ⟨h_de1, h_de2, h_de3⟩
    have h_dir_grid : grid3 r (F.tube i).direction = grid3 r (F.tube j).direction := by
      funext k; fin_cases k <;> tauto
    have h_base : ‖(F.tube i).base - (F.tube j).base‖ < δ / 8 := by
      have h9 : ‖(F.tube i).base - (F.tube j).base‖ < Real.sqrt 3 * r :=
        grid3_eq_imp_dist_lt hr_pos h_base_grid
      have h10 : Real.sqrt 3 * r < δ / 8 := by rw [hr_def]; nlinarith [hsqrt3_lt_2, hδ]
      linarith
    have h_dir : ‖(F.tube i).direction - (F.tube j).direction‖ < δ / 8 := by
      have h9 : ‖(F.tube i).direction - (F.tube j).direction‖ < Real.sqrt 3 * r :=
        grid3_eq_imp_dist_lt hr_pos h_dir_grid
      have h10 : Real.sqrt 3 * r < δ / 8 := by rw [hr_def]; nlinarith [hsqrt3_lt_2, hδ]
      linarith
    have h_not_distinct : ¬ (F.tube i).EssentiallyDistinct (F.tube j) :=
      close_tubes_not_essentially_distinct hδ hδ_small h_base.le h_dir.le
    have h_distinct : (F.tube i).EssentiallyDistinct (F.tube j) := hF_distinct i j h_ne
    exact h_not_distinct h_distinct
  let N : ℤ := ⌈R / r⌉
  have hN1 : R / r ≤ (N : ℝ) := Int.le_ceil _
  have hN2 : (N : ℝ) ≤ R / r + 1 := (Int.ceil_lt_add_one (R / r)).le
  let S : Finset ℤ := Finset.Icc (-N) N
  let S3 : Finset (ℤ × ℤ × ℤ) := S ×ˢ S ×ˢ S
  let S6 : Finset ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) := S3 ×ˢ S3
  have h_coord_in_S : ∀ (p : Point3), ‖p‖ ≤ R → ∀ i : Fin 3, grid3 r p i ∈ S := by
    intro p hp i
    have h1 : |p i| ≤ R := coord_le_norm p i |>.trans hp
    have h2 : -R ≤ p i := by linarith [abs_le.mp h1]
    have h3 : p i ≤ R := by linarith [abs_le.mp h1]
    have h4 : -R / r ≤ (p i) / r := by gcongr
    have h5 : (p i) / r ≤ R / r := by gcongr
    have hN_neg : (↑(-N) : ℝ) ≤ -R / r := by
      have hN1' : (R / r : ℝ) ≤ (N : ℝ) := hN1
      have h2 : (↑(-N) : ℝ) = -(N : ℝ) := by simp
      rw [h2]
      have h4 : -(N : ℝ) ≤ -(R / r) := by gcongr
      have h5 : -(R / r) = -R / r := by ring
      rw [h5] at h4; exact h4
    have h6 : (↑(-N) : ℝ) ≤ (p i) / r := by linarith
    have h7 : -N ≤ ⌊(p i) / r⌋ := Int.le_floor.mpr h6
    have h8 : ⌊(p i) / r⌋ ≤ N := by
      have h9 : (⌊(p i) / r⌋ : ℝ) ≤ (p i) / r := Int.floor_le _
      have h10 : (p i) / r ≤ (N : ℝ) := by linarith
      exact_mod_cast h9.trans h10
    exact Finset.mem_Icc.mpr ⟨h7, h8⟩
  have h_dir_unit : ∀ i : Fin F.card, ‖(F.tube i).direction‖ = 1 :=
    fun i => (F.tube i).direction_unit
  have h_encode3_in_S3 : ∀ (p : Point3), ‖p‖ ≤ R → (grid3 r p 0, grid3 r p 1, grid3 r p 2) ∈ S3 := by
    intro p hp
    have h1 : grid3 r p 0 ∈ S := h_coord_in_S p hp 0
    have h2 : grid3 r p 1 ∈ S := h_coord_in_S p hp 1
    have h3 : grid3 r p 2 ∈ S := h_coord_in_S p hp 2
    simp only [S3, Finset.mem_product]; exact ⟨h1, h2, h3⟩
  have h_image_subset : Finset.image encode6 s ⊆ S6 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have h1 : ‖(F.tube i).base‖ ≤ R := h_bases i hi
    have h2 : ‖(F.tube i).direction‖ ≤ R := by
      have h3 : ‖(F.tube i).direction‖ = 1 := h_dir_unit i
      rw [h3]; exact hR
    simp only [encode6, S6, Finset.mem_product]
    exact ⟨h_encode3_in_S3 (F.tube i).base h1, h_encode3_in_S3 (F.tube i).direction h2⟩
  have h_card_S6 : S6.card = S.card ^ 6 := by
    simp [S6, S3, Finset.card_product] <;> ring
  have hN_nonneg : 0 ≤ N := by
    have h1 : 0 < R / r := by positivity
    have h2 : 0 < N := Int.ceil_pos.mpr h1
    linarith
  have hN_bound : (N : ℝ) ≤ (16 * R + 1) / δ := by
    have h1 : (N : ℝ) ≤ R / r + 1 := hN2
    have h2 : R / r = 16 * R / δ := by
      rw [hr_def] <;> field_simp [hδ.ne'] <;> ring
    rw [h2] at h1
    have h3 : (N : ℝ) ≤ 16 * R / δ + 1 := h1
    have h4 : 16 * R / δ + 1 ≤ (16 * R + 1) / δ := by
      have h5 : 0 < δ := hδ
      field_simp [h5.ne'] <;> nlinarith
    exact h3.trans h4
  have h_card_S : (S.card : ℝ) = 2 * (N : ℝ) + 1 := by
    have h : (-N : ℤ) ≤ N + 1 := by linarith
    have h' : (↑(Finset.Icc (-N) N).card : ℤ) = N + 1 - (-N) := Int.card_Icc_of_le (-N) N h
    have h_eq : (S.card : ℤ) = ↑(Finset.Icc (-N) N).card := by simp [S]
    have h4 : (S.card : ℤ) = N + 1 - (-N) := by rw [h_eq, h']
    have h5 : (S.card : ℝ) = ↑(S.card : ℤ) := by simp
    rw [h5, h4] <;> simp [hN_nonneg] <;> norm_cast <;> ring
  have h_S_bound : (S.card : ℝ) ≤ (32 * R + 3) / δ := by
    rw [h_card_S]
    have h3 : (N : ℝ) ≤ (16 * R + 1) / δ := hN_bound
    have h_posδ : 0 < δ := hδ
    have h6 : 2 * (N : ℝ) + 1 ≤ 2 * ((16 * R + 1) / δ) + 1 := by gcongr
    have h7 : 2 * ((16 * R + 1) / δ) + 1 ≤ (32 * R + 3) / δ := by
      have h8 : 0 < δ := hδ
      field_simp [h8.ne'] <;> nlinarith
    exact h6.trans h7
  have h_final : (Finset.image encode6 s).card = s.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_card_image : (Finset.image encode6 s).card ≤ S6.card :=
    Finset.card_le_card h_image_subset
  rw [h_final] at h_card_image
  have h_main : (s.card : ℝ) ≤ (S6.card : ℝ) := by exact_mod_cast h_card_image
  have h_S6_eq : (S6.card : ℝ) = (S.card : ℝ)^6 := by
    rw [h_card_S6] <;> norm_cast
  have h_main2 : (s.card : ℝ) ≤ (S.card : ℝ)^6 := by
    rw [h_S6_eq] at h_main; exact h_main
  have h6 : (S.card : ℝ)^6 ≤ ((32 * R + 3) / δ)^6 := by gcongr <;> linarith [h_S_bound]
  have h7 : (s.card : ℝ) ≤ ((32 * R + 3) / δ)^6 := by
    calc (s.card : ℝ) ≤ (S.card : ℝ)^6 := h_main2
      _ ≤ ((32 * R + 3) / δ)^6 := h6
  have h8 : ((32 * R + 3) / δ)^6 = (32 * R + 3)^6 * δ^(-6 : ℝ) := by
    have h_posδ : 0 < δ := hδ
    have h9 : ((32 * R + 3) / δ)^6 = (32 * R + 3)^6 / δ^6 := by
      field_simp [h_posδ.ne'] <;> ring
    have h10 : (32 * R + 3)^6 * δ^(-6 : ℝ) = (32 * R + 3)^6 / δ^6 := by
      have h11 : δ^(-6 : ℝ) = (δ^6)⁻¹ := by
        have h12 : 0 ≤ δ := by linarith
        rw [Real.rpow_neg h12] <;> norm_cast <;> field_simp
      rw [h11] <;> field_simp
    rw [h9, h10]
  rw [h8] at h7
  exact h7

/-! ### Active tube base bound -/

/-- Active tubes (nonempty shaded carrier) have bases in `closedBall 0 3`. -/
lemma active_tube_base_bound
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hY_ball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    {i : Fin F.card} (hi_active : Y.carrier i ≠ ∅) :
    ‖(F.tube i).base‖ ≤ 3 := by
  have h1 : ∃ p, p ∈ Y.carrier i := Set.nonempty_iff_ne_empty.mpr hi_active
  rcases h1 with ⟨p, hp⟩
  have h2 : p ∈ Y.union := ⟨i, hp⟩
  have h3 : p ∈ Metric.closedBall (0 : Point3) 1 := hY_ball h2
  have h4 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using h3
  have h5 : p ∈ (F.tube i).carrier := Y.subset_body i hp
  have h_seg_cont : Continuous (fun t : ℝ => (F.tube i).base + t • (F.tube i).direction) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h_seg_closed : IsClosed (Kakeya.unitSegment (F.tube i).base (F.tube i).direction) := by
    apply IsCompact.isClosed
    exact IsCompact.image isCompact_Icc h_seg_cont
  have h5' : p ∈ Metric.cthickening δ (Kakeya.unitSegment (F.tube i).base (F.tube i).direction) := by
    simpa [Kakeya.DeltaTube.carrier] using h5
  have h6 : ∃ q, q ∈ Kakeya.unitSegment (F.tube i).base (F.tube i).direction ∧
      dist p q ≤ δ := by
    have h_eq : Metric.cthickening δ (Kakeya.unitSegment (F.tube i).base (F.tube i).direction) =
        ⋃ x ∈ (Kakeya.unitSegment (F.tube i).base (F.tube i).direction), Metric.closedBall x δ := by
      rw [Metric.cthickening_eq_biUnion_closedBall _ hδ.le]
      <;> rw [h_seg_closed.closure_eq]
    rw [h_eq] at h5'
    rcases Set.mem_iUnion₂.mp h5' with ⟨q, hq_seg, hq_ball⟩
    exact ⟨q, hq_seg, by simpa [Metric.mem_closedBall] using hq_ball⟩
  rcases h6 with ⟨q, hq_seg, hdist⟩
  rcases hq_seg with ⟨t, ht, rfl⟩
  set q' : Point3 := (F.tube i).base + t • (F.tube i).direction with hq'
  have h7 : ‖(F.tube i).base - q'‖ ≤ 1 := by
    have h8 : (F.tube i).base - q' = (-t) • (F.tube i).direction := by
      simp [hq'] <;> abel
    rw [h8]
    have h9 : ‖(-t) • (F.tube i).direction‖ = |(-t)| * ‖(F.tube i).direction‖ := norm_smul _ _
    rw [h9]
    have h10 : |(-t)| = |t| := by simp [abs_neg]
    rw [h10, (F.tube i).direction_unit]
    have h11 : |t| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h12 : |t| * (1 : ℝ) ≤ 1 := by
      calc |t| * (1 : ℝ) = |t| := by ring
        _ ≤ 1 := h11
    exact h12
  have h13 : ‖q' - p‖ ≤ δ := by
    have h131 : ‖q' - p‖ = ‖p - q'‖ := by rw [norm_sub_rev]
    rw [h131]
    exact hdist
  have h14 : ‖(F.tube i).base - p‖ ≤ ‖(F.tube i).base - q'‖ + ‖q' - p‖ := by
    calc
      ‖(F.tube i).base - p‖ = ‖((F.tube i).base - q') + (q' - p)‖ := by abel
      _ ≤ ‖(F.tube i).base - q'‖ + ‖q' - p‖ := norm_add_le _ _
  have h15 : ‖(F.tube i).base - p‖ ≤ 1 + δ := by
    calc ‖(F.tube i).base - p‖
      ≤ ‖(F.tube i).base - q'‖ + ‖q' - p‖ := h14
    _ ≤ 1 + δ := by linarith
  have h16 : ‖(F.tube i).base‖ ≤ ‖p‖ + ‖(F.tube i).base - p‖ := by
    calc
      ‖(F.tube i).base‖ = ‖p + ((F.tube i).base - p)‖ := by abel
      _ ≤ ‖p‖ + ‖(F.tube i).base - p‖ := norm_add_le _ _
  calc
    ‖(F.tube i).base‖ ≤ ‖p‖ + ‖(F.tube i).base - p‖ := h16
    _ ≤ 1 + (1 + δ) := by linarith
    _ ≤ 3 := by linarith [hδ_one]

/-! ### Density transfer and polynomial bound -/

/-- Density transfer: if `active` contains all tubes with nonempty shaded carrier,
then `F.card ≤ active.card · δ^(-η)`. -/
lemma density_transfer
    {delta eta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (active : Finset (Fin F.card))
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN delta eta))
    (h_inactive : ∀ i ∉ active, Y.carrier i = ∅) :
    (F.card : ℝ) ≤ (active.card : ℝ) * Real.rpow delta (-eta) := by
  have hvolume : TubeVolumeScalingStatement := tube_volume_scaling
  set V : ENNReal := Kakeya.deltaTubeVolume delta with hV_def
  have hV_pos : 0 < V := (hvolume.2.1 delta hdelta hdelta_one).1
  have hV_ne_top : V ≠ ⊤ := (hvolume.2.1 delta hdelta hdelta_one).2
  have h_tube_vol : ∀ i, (F.toBodyFamily.body i).volume = V := by
    intro i
    have h1 : (F.toBodyFamily.body i).volume = (F.tube i).volume := by rfl
    have h2 : (F.tube i).volume = Kakeya.deltaTubeVolume delta := hvolume.1 delta (F.tube i)
    exact h1.trans h2
  have hF_mass : F.toBodyFamily.mass = (F.card : ENNReal) * V := by
    have h1 : F.toBodyFamily.mass = ∑ i, (F.toBodyFamily.body i).volume := by rfl
    rw [h1]
    have h2 : ∑ i, (F.toBodyFamily.body i).volume = ∑ i : Fin F.card, V := by
      apply Finset.sum_congr rfl; intro i _; exact h_tube_vol i
    rw [h2]
    simp [Finset.sum_const, Finset.card_fin] <;> ring
  have hY_mass : Y.mass ≤ (active.card : ENNReal) * V := by
    have h1 : Y.mass = ∑ i ∈ active, MeasureTheory.volume (Y.carrier i) := by
      have h2 : Y.mass = ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i) := by rfl
      rw [h2]
      rw [Finset.sum_subset (show active ⊆ Finset.univ from Finset.subset_univ _)]
      intro i _ hni
      rw [h_inactive i hni] <;> simp
    rw [h1]
    have h3 : ∀ i ∈ active, MeasureTheory.volume (Y.carrier i) ≤ V := by
      intro i hi
      have h4 : Y.carrier i ⊆ (F.tube i).carrier := Y.subset_body i
      have h5 : MeasureTheory.volume (Y.carrier i) ≤ MeasureTheory.volume (F.tube i).carrier :=
        measure_mono h4
      have h6 : (F.tube i).volume = V := hvolume.1 delta (F.tube i)
      simpa using h5.trans (le_of_eq h6)
    calc
      (∑ i ∈ active, MeasureTheory.volume (Y.carrier i))
        ≤ ∑ i ∈ active, V := Finset.sum_le_sum h3
      _ = (active.card : ENNReal) * V := by
        simp [Finset.sum_const] <;> ring
  have h_dense : Kakeya.realRpowENN delta eta * F.toBodyFamily.mass ≤ Y.mass := hY_dense
  rw [hF_mass] at h_dense
  set a : ENNReal := Kakeya.realRpowENN delta eta * (F.card : ENNReal) with ha_def
  set b : ENNReal := (active.card : ENNReal) with hb_def
  have h_ineq : a * V ≤ b * V := by
    simpa [ha_def, mul_assoc] using h_dense.trans hY_mass
  have hV_real_pos : 0 < ENNReal.toReal V :=
    ENNReal.toReal_pos hV_pos.ne' hV_ne_top
  have ha_ne_top : a ≠ ⊤ := by
    have h1 : Kakeya.realRpowENN delta eta ≠ ⊤ := by
      simp [Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
    have h2 : (F.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    exact ENNReal.mul_ne_top h1 h2
  have hb_ne_top : b ≠ ⊤ := by
    simp [hb_def] <;> exact ENNReal.natCast_ne_top _
  have hav_ne_top : a * V ≠ ⊤ := ENNReal.mul_ne_top ha_ne_top hV_ne_top
  have hbv_ne_top : b * V ≠ ⊤ := ENNReal.mul_ne_top hb_ne_top hV_ne_top
  have h_real_ineq : ENNReal.toReal (a * V) ≤ ENNReal.toReal (b * V) :=
    (ENNReal.toReal_le_toReal hav_ne_top hbv_ne_top).mpr h_ineq
  have h_left : ENNReal.toReal (a * V) = ENNReal.toReal a * ENNReal.toReal V := by
    rw [ENNReal.toReal_mul]
  have h_right : ENNReal.toReal (b * V) = ENNReal.toReal b * ENNReal.toReal V := by
    rw [ENNReal.toReal_mul]
  rw [h_left, h_right] at h_real_ineq
  have h_final : ENNReal.toReal a ≤ ENNReal.toReal b := by
    have h_pos : 0 < ENNReal.toReal V := hV_real_pos
    have h : ENNReal.toReal a * ENNReal.toReal V ≤ ENNReal.toReal b * ENNReal.toReal V := h_real_ineq
    have h_div_a : (ENNReal.toReal a * ENNReal.toReal V) / ENNReal.toReal V = ENNReal.toReal a := by
      field_simp [h_pos.ne'] <;> ring
    have h_div_b : (ENNReal.toReal b * ENNReal.toReal V) / ENNReal.toReal V = ENNReal.toReal b := by
      field_simp [h_pos.ne'] <;> ring
    have h' : (ENNReal.toReal a * ENNReal.toReal V) / ENNReal.toReal V ≤
        (ENNReal.toReal b * ENNReal.toReal V) / ENNReal.toReal V := by gcongr
    rw [h_div_a, h_div_b] at h'
    exact h'
  have ha_real : ENNReal.toReal a = Real.rpow delta eta * (F.card : ℝ) := by
    have h1 : ENNReal.toReal a =
        ENNReal.toReal (Kakeya.realRpowENN delta eta) * ENNReal.toReal (F.card : ENNReal) := by
      rw [ha_def]
      rw [ENNReal.toReal_mul]
    rw [h1]
    have h2 : ENNReal.toReal (Kakeya.realRpowENN delta eta) = Real.rpow delta eta := by
      rw [Kakeya.realRpowENN]
      exact ENNReal.toReal_ofReal (Real.rpow_nonneg hdelta.le eta)
    have h3 : ENNReal.toReal (F.card : ENNReal) = (F.card : ℝ) := by
      simp <;> norm_cast
    rw [h2, h3] <;> ring
  have hb_real : ENNReal.toReal b = (active.card : ℝ) := by
    have h1 : b = (active.card : ENNReal) := by simp [hb_def]
    rw [h1]
    simp <;> norm_cast
  rw [ha_real, hb_real] at h_final
  have h_final2 : Real.rpow delta eta * (F.card : ℝ) ≤ (active.card : ℝ) := h_final
  have h5 : 0 < Real.rpow delta eta := Real.rpow_pos_of_pos hdelta _
  have h_nonneg_neg : 0 ≤ Real.rpow delta (-eta) := Real.rpow_nonneg hdelta.le (-eta)
  have h_mul_inv : Real.rpow delta eta * Real.rpow delta (-eta) = 1 := by
    have h1 : Real.rpow delta eta * Real.rpow delta (-eta) = Real.rpow delta (eta + (-eta)) :=
      (Real.rpow_add hdelta eta (-eta)).symm
    rw [h1]
    have h2 : eta + (-eta) = (0 : ℝ) := by ring
    rw [h2]
    simp
  have h_rewrite : (Real.rpow delta eta * (F.card : ℝ)) * Real.rpow delta (-eta) = (F.card : ℝ) := by
    have h : (Real.rpow delta eta * (F.card : ℝ)) * Real.rpow delta (-eta) =
        (Real.rpow delta eta * Real.rpow delta (-eta)) * (F.card : ℝ) := by ring
    rw [h, h_mul_inv] <;> ring
  have h6 : (F.card : ℝ) ≤ (active.card : ℝ) * Real.rpow delta (-eta) := by
    calc (F.card : ℝ)
      = (Real.rpow delta eta * (F.card : ℝ)) * Real.rpow delta (-eta) := h_rewrite.symm
    _ ≤ (active.card : ℝ) * Real.rpow delta (-eta) :=
      mul_le_mul_of_nonneg_right h_final2 h_nonneg_neg
  exact h6

/-- Full WZ1 polynomial cardinality bound:
`F.card ≤ 99^6 · δ^(-6-η)` via active-tube packing + density transfer. -/
lemma wz1_poly_card_bound
    {delta sigma eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) (hdelta_small : delta < 1 / 16)
    (hExt : WZ1ExtremalPair sigma eta F U Y) :
    (F.card : ℝ) ≤ (99 : ℝ)^6 * Real.rpow delta (-6 - eta) := by
  let active : Finset (Fin F.card) :=
    (Finset.univ : Finset (Fin F.card)).filter (fun i => Y.carrier i ≠ ∅)
  have hY_ball : Y.union ⊆ Metric.closedBall (0 : Point3) 1 := hExt.2.2.2.1
  have hF_distinct : F.IsEssentiallyDistinct := hExt.2.2.2.2.1
  have hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN delta eta) :=
    hExt.2.2.2.2.2.2.2.1
  have h_bases : ∀ i ∈ active, ‖(F.tube i).base‖ ≤ 3 := by
    intro i hi
    have h_ne : Y.carrier i ≠ ∅ := (Finset.mem_filter.mp hi).2
    exact active_tube_base_bound hdelta hdelta_one hY_ball h_ne
  have h_active_bound_raw : (active.card : ℝ) ≤ (32 * (3 : ℝ) + 3)^6 * delta ^ (-6 : ℝ) :=
    finset_card_bound_general hdelta hdelta_one hdelta_small (R := (3 : ℝ)) (by norm_num) active h_bases hF_distinct
  have h_active_bound : (active.card : ℝ) ≤ (99 : ℝ)^6 * Real.rpow delta (-6 : ℝ) := by
    convert h_active_bound_raw using 1
    · norm_num
  have h_inactive : ∀ i ∉ active, Y.carrier i = ∅ := by
    intro i hni
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hni
    tauto
  have h_transfer : (F.card : ℝ) ≤ (active.card : ℝ) * Real.rpow delta (-eta) :=
    density_transfer hdelta hdelta_one active hY_dense h_inactive
  calc
    (F.card : ℝ)
      ≤ (active.card : ℝ) * Real.rpow delta (-eta) := h_transfer
    _ ≤ ((99 : ℝ)^6 * Real.rpow delta (-6 : ℝ)) * Real.rpow delta (-eta) :=
      mul_le_mul_of_nonneg_right h_active_bound (Real.rpow_nonneg hdelta.le (-eta))
    _ = (99 : ℝ)^6 * Real.rpow delta (-6 - eta) := by
      have h_add : Real.rpow delta (-6 - eta) =
          Real.rpow delta (-6 : ℝ) * Real.rpow delta (-eta) := by
        have h1 : Real.rpow delta ((-6 : ℝ) + (-eta)) =
            Real.rpow delta (-6 : ℝ) * Real.rpow delta (-eta) :=
          Real.rpow_add hdelta (-6) (-eta)
        have h2 : (-6 : ℝ) + (-eta) = -6 - eta := by ring
        rw [h2] at h1
        exact h1
      have h_assoc : ((99 : ℝ)^6 * Real.rpow delta (-6 : ℝ)) * Real.rpow delta (-eta) =
          (99 : ℝ)^6 * (Real.rpow delta (-6 : ℝ) * Real.rpow delta (-eta)) := by ring
      rw [h_assoc, h_add.symm]

/-! ### Log conversion lemmas -/

/-- Given `C ≥ 1`, `N ≥ 0`, `b > 0`, there exists `0 < δ₀ ≤ 1` such that
for all `0 < δ ≤ δ₀`,
`2 · (log₂(C · δ^(-N)) + 1) ≤ δ^(-b)`. -/
lemma log_bound_from_poly
    {C N b : ℝ} (hC_ge_one : 1 ≤ C) (hN_nonneg : 0 ≤ N) (hb_pos : 0 < b) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        2 * (Real.log (C * Real.rpow δ (-N)) / Real.log 2 + 1) ≤
          Real.rpow δ (-b) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC_nonneg : 0 ≤ Real.log C := Real.log_nonneg hC_ge_one
  set C1 : ℝ := 2 * (1 + Real.log C / Real.log 2) with hC1_def
  set C2 : ℝ := 2 * N / Real.log 2 with hC2_def
  have hC1_nonneg : 0 ≤ C1 := by positivity
  have hC2_nonneg : 0 ≤ C2 := by positivity
  rcases @log_poly_bound C1 C2 b hC1_nonneg hC2_nonneg hb_pos with
    ⟨δ₀, hδ₀_pos, hδ₀_one, h_main⟩
  refine' ⟨δ₀, hδ₀_pos, hδ₀_one, _⟩
  intro δ hδ hδ_le
  have h_pos1 : 0 < C := by linarith
  have h_pos2 : 0 < Real.rpow δ (-N) := Real.rpow_pos_of_pos hδ _
  have h_pos1' : C ≠ 0 := by linarith
  have h_pos2' : Real.rpow δ (-N) ≠ 0 := h_pos2.ne'
  have h_expand : Real.log (C * Real.rpow δ (-N)) =
      Real.log C + N * Real.log (1 / δ) := by
    have h1 : Real.log (C * Real.rpow δ (-N)) =
        Real.log C + Real.log (Real.rpow δ (-N)) := by
      rw [Real.log_mul h_pos1' h_pos2']
    rw [h1]
    have h2 : Real.log (Real.rpow δ (-N)) = -N * Real.log δ := by
      have h21 : 0 ≤ δ := by linarith
      have h22 : Real.log (δ ^ (-N)) = (-N : ℝ) * Real.log δ := by
        rw [Real.log_rpow hδ]
      exact h22
    rw [h2]
    have h3 : -N * Real.log δ = N * Real.log (1 / δ) := by
      have h4 : Real.log (1 / δ) = -Real.log δ := by
        rw [Real.log_div (by norm_num) (ne_of_gt hδ), Real.log_one, zero_sub]
      rw [h4] <;> ring
    rw [h3]
  have h_goal : 2 * (Real.log (C * Real.rpow δ (-N)) / Real.log 2 + 1) =
      C1 + C2 * Real.log (1 / δ) := by
    rw [h_expand, hC1_def, hC2_def] <;> ring
  rw [h_goal]
  exact h_main δ hδ hδ_le

/-- Convert polynomial cardinality bound `F.card ≤ C · δ^(-N)` to the
ENNReal logarithmic bound required by fine multiplicity refinement. -/
lemma cardinality_bound_from_poly
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {C N eta epsilon_ref : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hF_nonempty : F.Nonempty)
    (hC_ge_one : 1 ≤ C) (hN_nonneg : 0 ≤ N)
    (h_card : (F.card : ℝ) ≤ C * Real.rpow delta (-N))
    (h_log_bound : 2 * (Real.log (C * Real.rpow delta (-N)) / Real.log 2 + 1) ≤
        Real.rpow delta (eta - epsilon_ref)) :
    2 * (Nat.log 2 F.card + 1 : ENNReal) ≤
      Kakeya.realRpowENN delta (eta - epsilon_ref) := by
  have hF_card_pos : 0 < F.card := hF_nonempty
  have hF_card_ne_zero : F.card ≠ 0 := hF_card_pos.ne'
  have h1 : (2 : ℕ) ^ Nat.log 2 F.card ≤ F.card := Nat.pow_log_le_self 2 hF_card_ne_zero
  have h1' : (2 : ℝ) ^ (Nat.log 2 F.card) ≤ (F.card : ℝ) := by exact_mod_cast h1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_nat_log_le : (Nat.log 2 F.card : ℝ) ≤ Real.log (F.card : ℝ) / Real.log 2 := by
    have h2 : Real.log ((2 : ℝ) ^ (Nat.log 2 F.card)) ≤ Real.log (F.card : ℝ) :=
      Real.log_le_log (by positivity) h1'
    have h3 : Real.log ((2 : ℝ) ^ (Nat.log 2 F.card)) =
        (Nat.log 2 F.card : ℝ) * Real.log 2 := by
      rw [Real.log_pow] <;> ring
    rw [h3] at h2
    have h4 : (Nat.log 2 F.card : ℝ) * Real.log 2 ≤ Real.log (F.card : ℝ) := h2
    calc
      (Nat.log 2 F.card : ℝ)
        = ((Nat.log 2 F.card : ℝ) * Real.log 2) / Real.log 2 := by field_simp [hlog2_pos.ne'] <;> ring
      _ ≤ Real.log (F.card : ℝ) / Real.log 2 := by gcongr
  have hC_pos : 0 < C := by linarith
  have h_log_arg_pos : 0 < C * Real.rpow delta (-N) := by
    have h_pos2 : 0 < Real.rpow delta (-N) := Real.rpow_pos_of_pos hdelta _
    exact mul_pos hC_pos h_pos2
  have h_log_card_le : Real.log (F.card : ℝ) ≤ Real.log (C * Real.rpow delta (-N)) :=
    Real.log_le_log (by exact_mod_cast hF_card_pos) h_card
  set L : ℝ := Real.log (C * Real.rpow delta (-N)) / Real.log 2 + 1 with hL_def
  have hL_nonneg : 0 ≤ L := by
    have h1 : C * Real.rpow delta (-N) ≥ 1 := by
      have h2 : Real.rpow delta (-N) ≥ 1 := by
        have h3 : Real.rpow delta N ≤ 1 := by
          apply Real.rpow_le_one hdelta.le hdelta_one <;> linarith
        have h4 : 0 < Real.rpow delta N := Real.rpow_pos_of_pos hdelta N
        have h5 : Real.rpow delta (-N) = (Real.rpow delta N)⁻¹ := Real.rpow_neg hdelta.le N
        rw [h5]
        have h6 : (Real.rpow delta N)⁻¹ ≥ 1 := by
          calc
            (Real.rpow delta N)⁻¹ ≥ (1 : ℝ)⁻¹ := by gcongr
            _ = 1 := by simp
        exact h6
      nlinarith
    have h7 : 0 ≤ Real.log (C * Real.rpow delta (-N)) := Real.log_nonneg h1
    have h8 : 0 ≤ Real.log (C * Real.rpow delta (-N)) / Real.log 2 := by
      apply div_nonneg h7 hlog2_pos.le
    linarith
  have h_div_log : Real.log (F.card : ℝ) / Real.log 2 ≤
      Real.log (C * Real.rpow delta (-N)) / Real.log 2 := by gcongr
  have h_ineq : (Nat.log 2 F.card + 1 : ℝ) ≤ L := by
    dsimp only [L]
    have h7 : (Nat.log 2 F.card : ℝ) ≤ Real.log (F.card : ℝ) / Real.log 2 := h_nat_log_le
    linarith [h_div_log, h7]
  have h_coe : ENNReal.ofReal ((Nat.log 2 F.card + 1 : ℝ)) =
      (Nat.log 2 F.card + 1 : ENNReal) := by
    simpa using ENNReal.ofReal_natCast (Nat.log 2 F.card + 1)
  have h8 : (Nat.log 2 F.card + 1 : ENNReal) ≤ ENNReal.ofReal L := by
    have h_main : ENNReal.ofReal ((Nat.log 2 F.card + 1 : ℝ)) ≤ ENNReal.ofReal L :=
      ENNReal.ofReal_mono h_ineq
    rw [h_coe] at h_main
    exact h_main
  have h9 : (2 : ENNReal) * (Nat.log 2 F.card + 1 : ENNReal) ≤
      (2 : ENNReal) * ENNReal.ofReal L := by gcongr
  have h10 : (2 : ENNReal) * ENNReal.ofReal L = ENNReal.ofReal (2 * L) := by
    have h101 : 0 ≤ (2 : ℝ) := by norm_num
    have h : ENNReal.ofReal (2 * L) = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal L :=
      ENNReal.ofReal_mul h101
    rw [h]
    have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_cast
    rw [h2] <;> ring
  rw [h10] at h9
  have h11 : ENNReal.ofReal (2 * L) ≤ Kakeya.realRpowENN delta (eta - epsilon_ref) := by
    dsimp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono h_log_bound
  exact h9.trans h11

end Kakeya.Assouad
