import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import Mathlib.Tactic

/-!
# WZ2 ordinary essential-distinctness separation lemma

If two tubes at scale `δ` are WZ2 ordinary-ED, then their bases or directions
must differ by more than `δ / 16`.

## Key lemma

`close_tubes_contained_in_dilation`: if base difference `≤ δ/16` and direction
difference `≤ δ/16`, then the first carrier is contained in the centered 2-fold
dilation of the second, violating WZ2-ED.

`wz2_ed_separation`: WZ2-ED implies base separation `> δ/16` OR direction
separation `> δ/16`.

This is a building block for WZ2 packing bounds.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/--
Geometric lemma: if two tubes at scale δ have close bases and close directions,
then the first carrier is contained in the centered 2-fold dilation of the second.
-/
lemma close_tubes_contained_in_dilation
    {δ : ℝ} (hδ : 0 < δ)
    {T U : Kakeya.DeltaTube δ}
    (hbase : ‖T.base - U.base‖ ≤ δ / 16)
    (hdir : ‖T.direction - U.direction‖ ≤ δ / 16) :
    T.carrier ⊆ wz2PaperCenteredDilatedCarrier 2 U := by
  let m_U : Point3 := U.base + (1 / 2 : ℝ) • U.direction
  have hmid : wz2PaperTubeMidpoint U = m_U := by rfl
  intro x hx
  have hcarrier_T : T.carrier = cthickening δ (unitSegment T.base T.direction) := by
    simp [Kakeya.DeltaTube.carrier]
  rw [hcarrier_T] at hx
  have hδ' : 0 ≤ δ := hδ.le
  have hcompact : IsCompact (unitSegment T.base T.direction) := by
    exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have h_eq : cthickening δ (unitSegment T.base T.direction) =
      ⋃ y ∈ unitSegment T.base T.direction, closedBall y δ :=
    hcompact.cthickening_eq_biUnion_closedBall hδ'
  rw [h_eq] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨y_T, hy_T_seg, hy_ball⟩
  rcases hy_T_seg with ⟨t, ht, rfl⟩
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  let y_U : Point3 := U.base + t • U.direction
  have hy_U_seg : y_U ∈ unitSegment U.base U.direction := ⟨t, ht, rfl⟩
  have h_diff1 : (T.base + t • T.direction) - y_U =
      (T.base - U.base) + t • (T.direction - U.direction) := by
    ext i
    simp [y_U, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] <;> ring
  have h1_smul : ‖t • (T.direction - U.direction)‖ = ‖t‖ * ‖T.direction - U.direction‖ :=
    norm_smul t (T.direction - U.direction)
  have h2_abs : ‖t‖ = |t| := by simp [Real.norm_eq_abs]
  have h3_abs : |t| = t := abs_of_nonneg ht0
  have h_nd : ‖t • (T.direction - U.direction)‖ = t * ‖T.direction - U.direction‖ := by
    rw [h1_smul, h2_abs, h3_abs]
  have hdist1 : ‖(T.base + t • T.direction) - y_U‖ ≤ δ / 8 := by
    rw [h_diff1]
    have h1 : ‖(T.base - U.base) + t • (T.direction - U.direction)‖ ≤
        ‖T.base - U.base‖ + ‖t • (T.direction - U.direction)‖ := norm_add_le _ _
    rw [h_nd] at h1
    have h4 : ‖T.base - U.base‖ + t * ‖T.direction - U.direction‖ ≤ δ / 16 + t * (δ / 16) := by
      gcongr
    have h5 : δ / 16 + t * (δ / 16) ≤ δ / 8 := by
      have h6 : t ≤ 1 := ht1
      calc
        δ / 16 + t * (δ / 16) ≤ δ / 16 + 1 * (δ / 16) := by gcongr
        _ = δ / 8 := by ring
    exact h1.trans (h4.trans h5)
  have hball' : dist x (T.base + t • T.direction) ≤ δ := by
    simpa [Metric.mem_closedBall] using hy_ball
  have hdist2 : dist x y_U ≤ 9 * δ / 8 := by
    calc dist x y_U
      ≤ dist x (T.base + t • T.direction) + dist (T.base + t • T.direction) y_U :=
        dist_triangle _ _ _
    _ ≤ δ + δ / 8 := add_le_add hball' hdist1
    _ = 9 * δ / 8 := by ring
  let z : Point3 := (1 / 2 : ℝ) • (x + m_U)
  let y_mid : Point3 := (1 / 2 : ℝ) • (y_U + m_U)
  have h_y_mid_eq : y_mid = U.base + ((t + 1 / 2) / 2) • U.direction := by
    ext i
    simp [y_mid, y_U, m_U, PiLp.add_apply, PiLp.smul_apply]
    <;> ring
  have h_smid0 : 0 ≤ (t + 1 / 2) / 2 := by
    have h : 0 ≤ t := ht0
    have h2 : 0 ≤ t + 1 / 2 := by linarith
    exact div_nonneg h2 (by norm_num)
  have h_smid1 : (t + 1 / 2) / 2 ≤ 1 := by
    have h : t ≤ 1 := ht1
    have h2 : t + 1 / 2 ≤ 3 / 2 := by linarith
    have h3 : (t + 1 / 2) / 2 ≤ (3 / 2 : ℝ) / 2 := by gcongr
    linarith
  have hymid_seg : y_mid ∈ unitSegment U.base U.direction := by
    rw [h_y_mid_eq]
    exact ⟨(t + 1 / 2) / 2, ⟨h_smid0, h_smid1⟩, by simp [add_smul] <;> rfl⟩
  have h_z_sub : z - y_mid = (1 / 2 : ℝ) • (x - y_U) := by
    simp [z, y_mid, smul_sub, sub_smul]
    <;> ext i <;> simp [PiLp.sub_apply, PiLp.smul_apply] <;> ring
  have h1_half : ‖(1 / 2 : ℝ) • (x - y_U)‖ = ‖(1 / 2 : ℝ)‖ * ‖x - y_U‖ :=
    norm_smul (1 / 2 : ℝ) (x - y_U)
  have h2_half : ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) := by
    simp [Real.norm_eq_abs] <;> norm_num
  have h_half_norm : ‖(1 / 2 : ℝ) • (x - y_U)‖ = (1 / 2 : ℝ) * dist x y_U := by
    rw [h1_half, h2_half] <;> rfl
  have hdist3 : dist z y_mid ≤ 9 * δ / 16 := by
    have h_dist_eq : dist z y_mid = ‖z - y_mid‖ := by
      rw [dist_eq_norm]
    rw [h_dist_eq, h_z_sub, h_half_norm]
    have h : (1 / 2 : ℝ) * dist x y_U ≤ (1 / 2 : ℝ) * (9 * δ / 8) := by
      gcongr <;> exact hdist2
    have h2 : (1 / 2 : ℝ) * (9 * δ / 8) = 9 * δ / 16 := by ring
    rw [h2] at h
    exact h
  have h9 : 9 * δ / 16 ≤ δ := by linarith
  have hz_in_carrier : z ∈ U.carrier := by
    have hcarrier_U : U.carrier = cthickening δ (unitSegment U.base U.direction) := by
      simp [Kakeya.DeltaTube.carrier]
    rw [hcarrier_U]
    have h10 : z ∈ cthickening (9 * δ / 16) (unitSegment U.base U.direction) :=
      Metric.mem_cthickening_of_dist_le (x := z) (y := y_mid) (δ := 9 * δ / 16)
        (E := unitSegment U.base U.direction) hymid_seg hdist3
    have h11 : cthickening (9 * δ / 16) (unitSegment U.base U.direction) ⊆
        cthickening δ (unitSegment U.base U.direction) :=
      Metric.cthickening_mono h9 (unitSegment U.base U.direction)
    exact h11 h10
  have h6 : x = m_U + (2 : ℝ) • (z - m_U) := by
    simp [z, smul_sub, sub_smul]
    <;> ext i <;> simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] <;> ring
  have h_homothety_eq : (AffineMap.homothety m_U (2 : ℝ)) z = m_U + (2 : ℝ) • (z - m_U) := by
    simp [AffineMap.homothety_apply] <;> abel
  have h7 : x ∈ AffineMap.homothety m_U (2 : ℝ) '' U.carrier := by
    refine ⟨z, hz_in_carrier, ?_⟩
    rw [h_homothety_eq]
    exact h6.symm
  simpa [wz2PaperCenteredDilatedCarrier, hmid] using h7

/-- WZ2-ED implies base or direction separation. -/
lemma wz2_ed_separation
    {δ : ℝ} (hδ : 0 < δ)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hed : WZ2PaperOrdinaryIsEssentiallyDistinct F)
    {i j : Fin F.card} (hne : i ≠ j) :
    ‖(F.tube i).base - (F.tube j).base‖ > δ / 16 ∨
    ‖(F.tube i).direction - (F.tube j).direction‖ > δ / 16 := by
  by_contra h
  push Not at h
  have h1 : (F.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (F.tube j) :=
    close_tubes_contained_in_dilation hδ h.1 h.2
  have h2 := hed i j hne
  exact h2.1 h1

/-- Helper: norm squared of a Point3 equals sum of coordinate squares. -/
private lemma point3_norm_sq (v : Point3) : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
  have h1 : ‖v‖ ^ 2 = ∑ k : Fin 3, (v k)^2 := EuclideanSpace.real_norm_sq_eq v
  rw [h1]
  simp [Fin.sum_univ_succ] <;> ring

/-- Helper: if all three coordinates have absolute value less than c,
    and 3*c^2 ≤ (δ/16)^2, then the norm is less than δ/16. -/
private lemma coord_abs_lt_implies_norm_lt {v : Point3} {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (h0 : |v 0| < c) (h1 : |v 1| < c) (h2 : |v 2| < c)
    (h3 : 3 * c^2 ≤ (δ / 16)^2) : ‖v‖ < δ / 16 := by
  have hs0 : (v 0)^2 < c^2 := by
    have hsq : (v 0)^2 = |v 0|^2 := by rw [sq_abs]
    rw [hsq]; have h_nonneg : 0 ≤ |v 0| := abs_nonneg _; nlinarith
  have hs1 : (v 1)^2 < c^2 := by
    have hsq : (v 1)^2 = |v 1|^2 := by rw [sq_abs]
    rw [hsq]; have h_nonneg : 0 ≤ |v 1| := abs_nonneg _; nlinarith
  have hs2 : (v 2)^2 < c^2 := by
    have hsq : (v 2)^2 = |v 2|^2 := by rw [sq_abs]
    rw [hsq]; have h_nonneg : 0 ≤ |v 2| := abs_nonneg _; nlinarith
  have h_norm_sq : ‖v‖^2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := point3_norm_sq v
  have h4 : ‖v‖^2 < 3 * c^2 := by rw [h_norm_sq]; nlinarith
  have h5 : ‖v‖^2 < (δ / 16)^2 := by linarith
  have h6 : 0 ≤ ‖v‖ := norm_nonneg v
  have h7 : 0 ≤ δ / 16 := by positivity
  nlinarith

/-- Polynomial cardinality bound for a WZ2-ED family with bounded bases. -/
lemma wz2_ed_packing_bound
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hed : WZ2PaperOrdinaryIsEssentiallyDistinct F)
    (hbase : ∀ i, ‖(F.tube i).base‖ ≤ 3) :
    (F.card : ℝ) ≤ (195 : ℝ)^3 * (67 : ℝ)^3 * δ^(-6 : ℝ) := by
  let c : ℝ := δ / 32
  have hc_pos : 0 < c := by positivity
  let encode : Fin F.card → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun i =>
    (fun k => ⌊(F.tube i).base k / c⌋, fun k => ⌊(F.tube i).direction k / c⌋)
  have h_floor_lt {x y : ℝ} (h : ⌊x / c⌋ = ⌊y / c⌋) : |x - y| < c := by
    set k : ℤ := ⌊x / c⌋ with hk
    have h1 : (k : ℝ) ≤ x / c := Int.floor_le _
    have h2 : x / c < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have h_eq : (k : ℝ) = (⌊y / c⌋ : ℝ) := by exact_mod_cast (Eq.trans hk h)
    have h3 : (k : ℝ) ≤ y / c := by
      have h31 : (⌊y / c⌋ : ℝ) ≤ y / c := Int.floor_le _
      linarith [h_eq]
    have h4 : y / c < (k : ℝ) + 1 := by
      have h41 : y / c < (⌊y / c⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      linarith [h_eq]
    have h5 : |x / c - y / c| < 1 := by rw [abs_lt]; constructor <;> linarith
    have h6 : |x - y| / c = |x / c - y / c| := by
      have h7 : x - y = c * (x / c - y / c) := by field_simp [hc_pos.ne'] <;> ring
      rw [h7, abs_mul, abs_of_pos hc_pos] <;> field_simp [hc_pos.ne'] <;> ring
    have h8 : |x - y| / c < 1 := by rw [h6]; exact h5
    calc |x - y| = (|x - y| / c) * c := by field_simp [hc_pos.ne'] <;> ring
      _ < 1 * c := by gcongr
      _ = c := by ring
  have h_inj : Function.Injective encode := by
    intro i j h
    by_cases hne : i = j
    · exact hne
    · have h_eq1 : (encode i).1 = (encode j).1 := by rw [h]
      have h_eq2 : (encode i).2 = (encode j).2 := by rw [h]
      have hb0 : |(F.tube i).base 0 - (F.tube j).base 0| < c :=
        h_floor_lt (congr_fun h_eq1 0)
      have hb1 : |(F.tube i).base 1 - (F.tube j).base 1| < c :=
        h_floor_lt (congr_fun h_eq1 1)
      have hb2 : |(F.tube i).base 2 - (F.tube j).base 2| < c :=
        h_floor_lt (congr_fun h_eq1 2)
      have hd0 : |(F.tube i).direction 0 - (F.tube j).direction 0| < c :=
        h_floor_lt (congr_fun h_eq2 0)
      have hd1 : |(F.tube i).direction 1 - (F.tube j).direction 1| < c :=
        h_floor_lt (congr_fun h_eq2 1)
      have hd2 : |(F.tube i).direction 2 - (F.tube j).direction 2| < c :=
        h_floor_lt (congr_fun h_eq2 2)
      set v : Point3 := (F.tube i).base - (F.tube j).base with hv
      set w : Point3 := (F.tube i).direction - (F.tube j).direction with hw
      have h4 : 3 * c^2 ≤ (δ / 16)^2 := by dsimp only [c]; nlinarith
      have hbase_norm : ‖v‖ < δ / 16 := coord_abs_lt_implies_norm_lt hc_pos hδ hb0 hb1 hb2 h4
      have hdir_norm : ‖w‖ < δ / 16 := coord_abs_lt_implies_norm_lt hc_pos hδ hd0 hd1 hd2 h4
      have h_contain : (F.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (F.tube j) :=
        close_tubes_contained_in_dilation hδ hbase_norm.le hdir_norm.le
      have h_ed := hed i j hne
      exact False.elim (h_ed.1 h_contain)
  let Nbase : ℤ := ⌈3 / c⌉
  let Ndir : ℤ := ⌈1 / c⌉
  let baseRange : Finset ℤ := Finset.Icc (-Nbase) Nbase
  let dirRange : Finset ℤ := Finset.Icc (-Ndir) Ndir
  let baseCodes : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => baseRange)
  let dirCodes : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => dirRange)
  let allCodes : Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) := baseCodes ×ˢ dirCodes
  have h_mem : ∀ i, encode i ∈ allCodes := by
    intro i
    have hb : ∀ k : Fin 3, |(F.tube i).base k| ≤ 3 := by
      intro k
      have h1 : ‖(F.tube i).base k‖ ≤ ‖(F.tube i).base‖ := PiLp.norm_apply_le (F.tube i).base k
      have h2 : |(F.tube i).base k| = ‖(F.tube i).base k‖ := by simp [Real.norm_eq_abs]
      rw [h2]; exact h1.trans (hbase i)
    have hd : ∀ k : Fin 3, |(F.tube i).direction k| ≤ 1 := by
      intro k
      have h1 : ‖(F.tube i).direction k‖ ≤ ‖(F.tube i).direction‖ := PiLp.norm_apply_le (F.tube i).direction k
      have h2 : |(F.tube i).direction k| = ‖(F.tube i).direction k‖ := by simp [Real.norm_eq_abs]
      rw [h2]; rw [(F.tube i).direction_unit] at h1; exact h1
    have hb' : ∀ k : Fin 3, ⌊(F.tube i).base k / c⌋ ∈ baseRange := by
      intro k
      have h1 : -3 ≤ (F.tube i).base k := by linarith [abs_le.mp (hb k)]
      have h2 : (F.tube i).base k ≤ 3 := by linarith [abs_le.mp (hb k)]
      have h3 : -3 / c ≤ (F.tube i).base k / c := by gcongr
      have h4 : (F.tube i).base k / c ≤ 3 / c := by gcongr
      have h5 : ⌊-3 / c⌋ ≤ ⌊(F.tube i).base k / c⌋ := Int.floor_le_floor h3
      have h6 : ⌊(F.tube i).base k / c⌋ ≤ ⌊3 / c⌋ := Int.floor_le_floor h4
      have h7 : ⌊-3 / c⌋ = -Nbase := by
        have h8 : ⌊-3 / c⌋ = -⌈3 / c⌉ := by
          have h9 : -3 / c = -(3 / c) := by ring
          rw [h9, Int.floor_neg]
        rw [h8] <;> rfl
      have h9 : ⌊3 / c⌋ ≤ Nbase := by simp [Nbase, Int.floor_le_ceil]
      simp only [baseRange, Finset.mem_Icc]
      exact ⟨by linarith [h7, h5], by linarith [h6, h9]⟩
    have hd' : ∀ k : Fin 3, ⌊(F.tube i).direction k / c⌋ ∈ dirRange := by
      intro k
      have h1 : -1 ≤ (F.tube i).direction k := by linarith [abs_le.mp (hd k)]
      have h2 : (F.tube i).direction k ≤ 1 := by linarith [abs_le.mp (hd k)]
      have h3 : -1 / c ≤ (F.tube i).direction k / c := by gcongr
      have h4 : (F.tube i).direction k / c ≤ 1 / c := by gcongr
      have h5 : ⌊-1 / c⌋ ≤ ⌊(F.tube i).direction k / c⌋ := Int.floor_le_floor h3
      have h6 : ⌊(F.tube i).direction k / c⌋ ≤ ⌊1 / c⌋ := Int.floor_le_floor h4
      have h7 : ⌊-1 / c⌋ = -Ndir := by
        have h8 : ⌊-1 / c⌋ = -⌈1 / c⌉ := by
          have h9 : -1 / c = -(1 / c) := by ring
          rw [h9, Int.floor_neg]
        rw [h8] <;> rfl
      have h9 : ⌊1 / c⌋ ≤ Ndir := by simp [Ndir, Int.floor_le_ceil]
      simp only [dirRange, Finset.mem_Icc]
      exact ⟨by linarith [h7, h5], by linarith [h6, h9]⟩
    have h1 : (encode i).1 ∈ baseCodes := by
      rw [Fintype.mem_piFinset]
      exact hb'
    have h2 : (encode i).2 ∈ dirCodes := by
      rw [Fintype.mem_piFinset]
      exact hd'
    simp only [allCodes, Finset.mem_product]
    exact ⟨h1, h2⟩
  have h_card : F.card ≤ allCodes.card := by
    have h1 : (Finset.univ.image encode).card = F.card := by
      rw [Finset.card_image_of_injective _ h_inj] <;> simp
    have h2 : (Finset.univ.image encode) ⊆ allCodes := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact h_mem i
    have h3 : (Finset.univ.image encode).card ≤ allCodes.card := Finset.card_le_card h2
    rw [h1] at h3
    exact h3
  have hNbase_nonneg : 0 ≤ Nbase := by simp [Nbase, Int.ceil_nonneg] <;> positivity
  have hNdir_nonneg : 0 ≤ Ndir := by simp [Ndir, Int.ceil_nonneg] <;> positivity
  have h_base_card : (baseRange.card : ℝ) ≤ 2 * (3 / c) + 3 := by
    have h1 : baseRange.card = (2 * Nbase + 1).toNat := by
      simp [baseRange, Int.card_Icc] <;> omega
    rw [h1]
    have h2 : 0 ≤ 2 * Nbase + 1 := by linarith
    have h3 : ((2 * Nbase + 1).toNat : ℝ) = (2 * (Nbase : ℝ) + 1) := by
      have h4 : ((2 * Nbase + 1).toNat : ℤ) = 2 * Nbase + 1 := Int.toNat_of_nonneg h2
      exact_mod_cast h4
    rw [h3]
    have h5 : (Nbase : ℝ) < 3 / c + 1 := Int.ceil_lt_add_one (3 / c)
    linarith
  have h_dir_card : (dirRange.card : ℝ) ≤ 2 * (1 / c) + 3 := by
    have h1 : dirRange.card = (2 * Ndir + 1).toNat := by
      simp [dirRange, Int.card_Icc] <;> omega
    rw [h1]
    have h2 : 0 ≤ 2 * Ndir + 1 := by linarith
    have h3 : ((2 * Ndir + 1).toNat : ℝ) = (2 * (Ndir : ℝ) + 1) := by
      have h4 : ((2 * Ndir + 1).toNat : ℤ) = 2 * Ndir + 1 := Int.toNat_of_nonneg h2
      exact_mod_cast h4
    rw [h3]
    have h5 : (Ndir : ℝ) < 1 / c + 1 := Int.ceil_lt_add_one (1 / c)
    linarith
  have h_base_codes_card : (baseCodes.card : ℝ) = (baseRange.card : ℝ)^3 := by
    have h : baseCodes.card = ∏ k : Fin 3, baseRange.card := by
      rw [Fintype.card_piFinset] <;> rfl
    rw [h]
    simp [Fin.prod_univ_succ] <;> ring
  have h_dir_codes_card : (dirCodes.card : ℝ) = (dirRange.card : ℝ)^3 := by
    have h : dirCodes.card = ∏ k : Fin 3, dirRange.card := by
      rw [Fintype.card_piFinset] <;> rfl
    rw [h]
    simp [Fin.prod_univ_succ] <;> ring
  have h_all_card : (allCodes.card : ℝ) = (baseCodes.card : ℝ) * (dirCodes.card : ℝ) := by
    simp [allCodes, Finset.card_product] <;> ring
  have h_bound1 : 2 * (3 / c) + 3 ≤ 195 / δ := by
    dsimp only [c]
    have h5 : 2 * (3 / (δ / 32)) + 3 = 192 / δ + 3 := by field_simp [hδ.ne'] <;> ring
    rw [h5]
    have h6 : 3 ≤ 3 / δ := by
      have h7 : 3 * δ ≤ 3 := by nlinarith
      calc 3 = 3 * δ / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ 3 / δ := by gcongr
    calc 192 / δ + 3
      ≤ 192 / δ + 3 / δ := by gcongr
    _ = 195 / δ := by field_simp [hδ.ne'] <;> ring
  have h_bound2 : 2 * (1 / c) + 3 ≤ 67 / δ := by
    dsimp only [c]
    have h5 : 2 * (1 / (δ / 32)) + 3 = 64 / δ + 3 := by field_simp [hδ.ne'] <;> ring
    rw [h5]
    have h6 : 3 ≤ 3 / δ := by
      have h7 : 3 * δ ≤ 3 := by nlinarith
      calc 3 = 3 * δ / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ 3 / δ := by gcongr
    calc 64 / δ + 3
      ≤ 64 / δ + 3 / δ := by gcongr
    _ = 67 / δ := by field_simp [hδ.ne'] <;> ring
  have h_main : (F.card : ℝ) ≤ (195 / δ)^3 * (67 / δ)^3 := by
    calc (F.card : ℝ)
      ≤ (allCodes.card : ℝ) := by exact_mod_cast h_card
    _ = (baseCodes.card : ℝ) * (dirCodes.card : ℝ) := h_all_card
    _ = (baseRange.card : ℝ)^3 * (dirRange.card : ℝ)^3 := by
      rw [h_base_codes_card, h_dir_codes_card] <;> ring
    _ ≤ (2 * (3 / c) + 3)^3 * (2 * (1 / c) + 3)^3 := by gcongr <;> linarith
    _ ≤ (195 / δ)^3 * (67 / δ)^3 := by gcongr <;> linarith
  have h_rpow : δ^(-6 : ℝ) = 1 / δ^6 := by
    have h_neg : (-6 : ℝ) = -(6 : ℝ) := by norm_num
    have h1 : δ^(-6 : ℝ) = δ^(-(6 : ℝ)) := by rw [h_neg]
    have h2 : δ^(-(6 : ℝ)) = (δ^(6 : ℝ))⁻¹ := Real.rpow_neg hδ.le (6 : ℝ)
    have h3 : (δ^(6 : ℝ))⁻¹ = 1 / δ^(6 : ℝ) := by simp
    have h4 : δ^(6 : ℝ) = δ^6 := by norm_cast
    calc δ^(-6 : ℝ)
      = δ^(-(6 : ℝ)) := h1
    _ = (δ^(6 : ℝ))⁻¹ := h2
    _ = 1 / δ^(6 : ℝ) := h3
    _ = 1 / δ^6 := by rw [h4]
  have h_final : (195 / δ)^3 * (67 / δ)^3 = (195 : ℝ)^3 * (67 : ℝ)^3 * δ^(-6 : ℝ) := by
    have h3 : (195 / δ)^3 * (67 / δ)^3 = (195 : ℝ)^3 * (67 : ℝ)^3 / δ^6 := by ring
    rw [h3, h_rpow] <;> ring
  rw [h_final] at h_main
  exact h_main

/-- Logarithmic cardinality bound: Nat.log 2 F.card is O(log(1/δ)).

This follows from the polynomial packing bound and is used for polylog absorption. -/
lemma wz2_ed_log_bound
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hed : WZ2PaperOrdinaryIsEssentiallyDistinct F)
    (hbase : ∀ i, ‖(F.tube i).base‖ ≤ 3) :
    (Nat.log 2 F.card : ℝ) ≤
      (Real.log ((195 : ℝ)^3 * (67 : ℝ)^3) + 6 * Real.log (1 / δ)) / Real.log 2 := by
  set C : ℝ := (195 : ℝ)^3 * (67 : ℝ)^3 with hC
  have hC_pos : 0 < C := by positivity
  have h_main : (F.card : ℝ) ≤ C * δ^(-6 : ℝ) :=
    wz2_ed_packing_bound hδ hδ_one hed hbase
  by_cases h0 : F.card = 0
  · have h_log0 : Nat.log 2 0 = 0 := by decide
    rw [h0, h_log0]
    have hC_gt_one : 1 < C := by
      dsimp only [C]
      <;> norm_num
    have h1 : 0 < Real.log C := Real.log_pos hC_gt_one
    have h_one_le_inv : 1 ≤ 1 / δ := by
      have hδ_le_one : δ ≤ 1 := hδ_one
      have h : 1 / δ ≥ 1 := by
        calc 1 / δ ≥ 1 / 1 := by gcongr
             _ = 1 := by norm_num
      exact h
    have h3 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg h_one_le_inv
    have h4 : 0 < Real.log 2 := by positivity
    have h5 : 0 ≤ Real.log C + 6 * Real.log (1 / δ) := by positivity
    have h6 : (0 : ℝ) ≤ (Real.log C + 6 * Real.log (1 / δ)) / Real.log 2 := div_nonneg h5 h4.le
    exact_mod_cast h6
  · have h_pos : 0 < F.card := Nat.pos_of_ne_zero h0
    have h1_nat : 2 ^ Nat.log 2 F.card ≤ F.card := Nat.pow_log_le_self 2 h0
    have h1 : (2 : ℝ)^(Nat.log 2 F.card) ≤ (F.card : ℝ) := by exact_mod_cast h1_nat
    have h2 : (2 : ℝ)^(Nat.log 2 F.card) ≤ C * δ^(-6 : ℝ) := h1.trans h_main
    have h3 : Real.log ((2 : ℝ)^(Nat.log 2 F.card)) ≤ Real.log (C * δ^(-6 : ℝ)) :=
      Real.log_le_log (by positivity) h2
    have h4 : Real.log ((2 : ℝ)^(Nat.log 2 F.card)) =
        (Nat.log 2 F.card : ℝ) * Real.log 2 := by
      rw [Real.log_pow] <;> norm_cast
    have h5 : Real.log (C * δ^(-6 : ℝ)) = Real.log C + Real.log (δ^(-6 : ℝ)) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have h6 : Real.log (δ^(-6 : ℝ)) = (-6 : ℝ) * Real.log δ := by
      rw [Real.log_rpow (by linarith)] <;> ring
    have h7 : Real.log (1 / δ) = -Real.log δ := by
      have h71 : Real.log (1 / δ) = Real.log 1 - Real.log δ := by
        rw [Real.log_div (by norm_num) (ne_of_gt hδ)]
      rw [h71, Real.log_one] <;> ring
    have h8 : Real.log (C * δ^(-6 : ℝ)) = Real.log C + 6 * Real.log (1 / δ) := by
      rw [h5, h6, h7] <;> ring
    rw [h4, h8] at h3
    have h9 : 0 < Real.log 2 := by positivity
    calc (Nat.log 2 F.card : ℝ)
      = ((Nat.log 2 F.card : ℝ) * Real.log 2) / Real.log 2 := by field_simp [h9.ne'] <;> ring
    _ ≤ (Real.log C + 6 * Real.log (1 / δ)) / Real.log 2 := by gcongr

end Kakeya.Assouad.PureWZ2

end
