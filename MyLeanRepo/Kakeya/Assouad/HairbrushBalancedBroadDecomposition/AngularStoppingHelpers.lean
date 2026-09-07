import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.Hairbrush.AcuteAngleHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DirectionPacking2D
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Helper lemmas for hairbrush labeled angular stopping

Provides:
1. Triangle inequality for `hairbrushAcuteDirectionAngle`
2. Maximal separated subset existence
3. Constant packing bound for theta-separated vectors in a cap
-/

noncomputable section

open Metric Finset InnerProductGeometry Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-! ### Lemma 1: Triangle inequality for acute direction angle -/

/-- For unit vectors, Euclidean angle equals arccos of inner product. -/
private lemma unit_angle_eq_arccos' {v u : Point3} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    angle v u = Real.arccos (inner ℝ v u) := by
  have h1 : Real.cos (angle v u) * (‖v‖ * ‖u‖) = inner ℝ v u :=
    cos_angle_mul_norm_mul_norm v u
  have h2 : Real.cos (angle v u) = inner ℝ v u := by
    rw [hv, hu] at h1 <;> norm_num at h1 ⊢ <;> exact h1
  have h3 : 0 ≤ angle v u := angle_nonneg v u
  have h4 : angle v u ≤ Real.pi := angle_le_pi v u
  have h5 : Real.arccos (Real.cos (angle v u)) = angle v u := Real.arccos_cos h3 h4
  rw [h2] at h5
  exact h5.symm

/-- Acute angle invariant under negating left argument. -/
private lemma acute_angle_neg_left {u v : Point3} :
    hairbrushAcuteDirectionAngle (-u) v = hairbrushAcuteDirectionAngle u v := by
  have h : inner ℝ (-u) v = -inner ℝ u v := by simp [inner_smul_left]
  dsimp only [hairbrushAcuteDirectionAngle]
  rw [h]
  have h2 : Real.arccos (-inner ℝ u v) = Real.pi - Real.arccos (inner ℝ u v) :=
    Real.arccos_neg _
  rw [h2]
  have h3 : Real.pi - (Real.pi - Real.arccos (inner ℝ u v)) = Real.arccos (inner ℝ u v) := by ring
  rw [h3]
  exact min_comm _ _

/-- Acute angle invariant under negating right argument. -/
private lemma acute_angle_neg_right {u v : Point3} :
    hairbrushAcuteDirectionAngle u (-v) = hairbrushAcuteDirectionAngle u v := by
  have h : inner ℝ u (-v) = -inner ℝ u v := by simp [inner_smul_right]
  dsimp only [hairbrushAcuteDirectionAngle]
  rw [h]
  have h2 : Real.arccos (-inner ℝ u v) = Real.pi - Real.arccos (inner ℝ u v) :=
    Real.arccos_neg _
  rw [h2]
  have h3 : Real.pi - (Real.pi - Real.arccos (inner ℝ u v)) = Real.arccos (inner ℝ u v) := by ring
  rw [h3]
  exact min_comm _ _

/-- For unit vectors, angle with negated left vector. -/
private lemma angle_neg_left' {u v : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    angle (-u) v = Real.pi - angle u v := by
  have h1 : angle (-u) v = Real.arccos (inner ℝ (-u) v) :=
    unit_angle_eq_arccos' (by simp [hu]) hv
  have h2 : angle u v = Real.arccos (inner ℝ u v) := unit_angle_eq_arccos' hu hv
  rw [h1, h2]
  have h3 : inner ℝ (-u) v = -inner ℝ u v := by simp [inner_smul_left]
  rw [h3]
  have h4 : Real.arccos (-inner ℝ u v) = Real.pi - Real.arccos (inner ℝ u v) :=
    Real.arccos_neg _
  rw [h4] <;> ring

/-- For unit vectors, angle with negated right vector. -/
private lemma angle_neg_right' {u v : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    angle u (-v) = Real.pi - angle u v := by
  have h1 : angle u (-v) = Real.arccos (inner ℝ u (-v)) :=
    unit_angle_eq_arccos' hu (by simp [hv])
  have h2 : angle u v = Real.arccos (inner ℝ u v) := unit_angle_eq_arccos' hu hv
  rw [h1, h2]
  have h3 : inner ℝ u (-v) = -inner ℝ u v := by simp [inner_smul_right]
  rw [h3]
  have h4 : Real.arccos (-inner ℝ u v) = Real.pi - Real.arccos (inner ℝ u v) :=
    Real.arccos_neg _
  rw [h4] <;> ring

/-- For unit vectors, angle invariant under negating both arguments. -/
private lemma angle_both_neg {u v : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    angle (-u) (-v) = angle u v := by
  have h1 : angle (-u) (-v) = Real.arccos (inner ℝ (-u) (-v)) :=
    unit_angle_eq_arccos' (by simp [hu]) (by simp [hv])
  have h2 : angle u v = Real.arccos (inner ℝ u v) := unit_angle_eq_arccos' hu hv
  have h3 : inner ℝ (-u) (-v) = inner ℝ u v := by simp [inner_smul_left, inner_smul_right]
  rw [h1, h2, h3]

/-- Triangle inequality for the acute direction angle on the projective sphere. -/
lemma acute_direction_angle_triangle {u v w : Point3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    hairbrushAcuteDirectionAngle u w ≤
    hairbrushAcuteDirectionAngle u v + hairbrushAcuteDirectionAngle v w := by
  set a : ℝ := angle u v with ha_def
  set b : ℝ := angle v w with hb_def
  set c : ℝ := angle u w with hc_def
  have ha_le_pi : a ≤ Real.pi := angle_le_pi u v
  have hb_le_pi : b ≤ Real.pi := angle_le_pi v w
  have hc_le_pi : c ≤ Real.pi := angle_le_pi u w
  let x := min a (Real.pi - a)
  let y := min b (Real.pi - b)
  let z := min c (Real.pi - c)
  have h_acute_uv : hairbrushAcuteDirectionAngle u v = x := by
    have h : a = Real.arccos (inner ℝ u v) := unit_angle_eq_arccos' hu hv
    dsimp only [hairbrushAcuteDirectionAngle, x]
    rw [h]
  have h_acute_vw : hairbrushAcuteDirectionAngle v w = y := by
    have h : b = Real.arccos (inner ℝ v w) := unit_angle_eq_arccos' hv hw
    dsimp only [hairbrushAcuteDirectionAngle, y]
    rw [h]
  have h_acute_uw : hairbrushAcuteDirectionAngle u w = z := by
    have h : c = Real.arccos (inner ℝ u w) := unit_angle_eq_arccos' hu hw
    dsimp only [hairbrushAcuteDirectionAngle, z]
    rw [h]
  have h1 : c ≤ a + b := angle_le_angle_add_angle u v w
  have h2 : c ≥ a - b := by
    have h : angle (-u) w ≤ angle (-u) v + angle v w := angle_le_angle_add_angle (-u) v w
    have h21 : angle (-u) w = Real.pi - c := angle_neg_left' hu hw
    have h22 : angle (-u) v = Real.pi - a := angle_neg_left' hu hv
    rw [h21, h22] at h
    linarith
  have h3 : c ≥ b - a := by
    have h : angle u (-w) ≤ angle u v + angle v (-w) := angle_le_angle_add_angle u v (-w)
    have h31 : angle u (-w) = Real.pi - c := angle_neg_right' hu hw
    have h32 : angle v (-w) = Real.pi - b := angle_neg_right' hv hw
    rw [h31, h32] at h
    linarith
  have h4 : c ≤ (Real.pi - a) + (Real.pi - b) := by
    have h : angle (-u) (-w) ≤ angle (-u) v + angle v (-w) := angle_le_angle_add_angle (-u) v (-w)
    have h41 : angle (-u) (-w) = c := angle_both_neg hu hw
    have h42 : angle (-u) v = Real.pi - a := angle_neg_left' hu hv
    have h43 : angle v (-w) = Real.pi - b := angle_neg_right' hv hw
    rw [h41, h42, h43] at h
    exact h
  have hz_le_c : z ≤ c := min_le_left _ _
  have hz_le_pic : z ≤ Real.pi - c := min_le_right _ _
  by_cases h_a : a ≤ Real.pi / 2
  · have hx : x = a := by dsimp only [x]; rw [min_eq_left] <;> linarith
    by_cases h_b : b ≤ Real.pi / 2
    · have hy : y = b := by dsimp only [y]; rw [min_eq_left] <;> linarith
      have h_goal : z ≤ x + y := by rw [hx, hy]; exact hz_le_c.trans h1
      rw [h_acute_uv, h_acute_vw, h_acute_uw]; exact h_goal
    · have hy : y = Real.pi - b := by dsimp only [y]; rw [min_eq_right] <;> linarith
      have h3' : Real.pi - c ≤ a + (Real.pi - b) := by linarith
      have h_goal : z ≤ x + y := by rw [hx, hy]; exact hz_le_pic.trans h3'
      rw [h_acute_uv, h_acute_vw, h_acute_uw]; exact h_goal
  · have hx : x = Real.pi - a := by dsimp only [x]; rw [min_eq_right] <;> linarith
    by_cases h_b : b ≤ Real.pi / 2
    · have hy : y = b := by dsimp only [y]; rw [min_eq_left] <;> linarith
      have h2' : Real.pi - c ≤ (Real.pi - a) + b := by linarith
      have h_goal : z ≤ x + y := by rw [hx, hy]; exact hz_le_pic.trans h2'
      rw [h_acute_uv, h_acute_vw, h_acute_uw]; exact h_goal
    · have hy : y = Real.pi - b := by dsimp only [y]; rw [min_eq_right] <;> linarith
      have h_goal : z ≤ x + y := by rw [hx, hy]; exact hz_le_c.trans h4
      rw [h_acute_uv, h_acute_vw, h_acute_uw]; exact h_goal

/-! ### Lemma 2: Maximal separated subset -/

/-- Existence of a maximal `sep`-separated subset of a finite set of unit vectors. -/
lemma maximal_acute_separated_subset {s : Finset Point3} {sep : ℝ}
    (hsep : 0 < sep) (hs1 : ∀ v ∈ s, ‖v‖ = 1) :
    ∃ (N : Finset Point3), N ⊆ s ∧
      (∀ v ∈ N, ∀ w ∈ N, v ≠ w → sep ≤ hairbrushAcuteDirectionAngle v w) ∧
      (∀ v ∈ s, ∃ n ∈ N, hairbrushAcuteDirectionAngle v n < sep) := by
  let separated (N : Finset Point3) : Prop :=
    ∀ v ∈ N, ∀ w ∈ N, v ≠ w → sep ≤ hairbrushAcuteDirectionAngle v w
  let candidates : Finset (Finset Point3) := s.powerset.filter separated
  have h_empty_in : (∅ : Finset Point3) ∈ candidates := by
    simp [candidates, separated]
  have h_nonempty : candidates.Nonempty := ⟨∅, h_empty_in⟩
  rcases Finset.exists_max_image candidates (fun N : Finset Point3 => N.card) h_nonempty
    with ⟨N, hN_in, hN_max⟩
  have hN_sub : N ⊆ s := by
    have h1 : N ∈ s.powerset := (Finset.mem_filter.mp hN_in).1
    exact Finset.mem_powerset.mp h1
  have hN_sep : separated N := (Finset.mem_filter.mp hN_in).2
  refine ⟨N, hN_sub, hN_sep, ?_⟩
  intro v hv
  by_cases h_v_in : v ∈ N
  · refine ⟨v, h_v_in, ?_⟩
    have h_self : hairbrushAcuteDirectionAngle v v = 0 :=
      hairbrushAcuteDirectionAngle_self (hs1 v hv)
    rw [h_self] <;> linarith
  · by_contra h
    push Not at h
    let N' := insert v N
    have hN'_sub : N' ⊆ s := by
      intro x hx
      simp only [N', Finset.mem_insert] at hx
      rcases hx with (rfl | hx2) <;> tauto
    have hN'_sep : separated N' := by
      intro x hx y hy hne
      simp only [N', Finset.mem_insert] at hx hy
      rcases hx with (rfl | hx2)
      · rcases hy with (rfl | hy2)
        · contradiction
        · exact h y hy2
      · rcases hy with (rfl | hy2)
        · have h_goal : sep ≤ hairbrushAcuteDirectionAngle x y := by
            have h_symm : hairbrushAcuteDirectionAngle x y = hairbrushAcuteDirectionAngle y x := by
              simp [hairbrushAcuteDirectionAngle, real_inner_comm]
            rw [h_symm]
            exact h x hx2
          exact h_goal
        · exact hN_sep x hx2 y hy2 hne
    have hN'_in : N' ∈ candidates := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr hN'_sub, hN'_sep⟩
    have h_card : N'.card = N.card + 1 := by
      exact Finset.card_insert_of_notMem h_v_in
    have h_contra : N'.card ≤ N.card := hN_max N' hN'_in
    rw [h_card] at h_contra
    <;> omega

/-! ### Lemma 3: Constant packing bound -/

/-- Euclidean distance lower bound from acute angle separation. -/
private lemma acute_to_dist_lower {v w : Point3}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {theta : ℝ} (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (h : theta ≤ hairbrushAcuteDirectionAngle v w) :
    2 * Real.sin (theta / 2) ≤ dist v w := by
  set ang : ℝ := angle v w with hang_def
  have h_ang_nonneg : 0 ≤ ang := angle_nonneg v w
  have h_ang_le_pi : ang ≤ Real.pi := angle_le_pi v w
  have h_dist : dist v w = 2 * Real.sin (ang / 2) := by
    have h1 : dist v w = ‖v - w‖ := by rfl
    rw [h1]
    have h2 : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner ℝ v w + ‖w‖ ^ 2 := norm_sub_sq_real v w
    have h3 : inner ℝ v w = Real.cos ang := by
      have h4 : ang = Real.arccos (inner ℝ v w) := unit_angle_eq_arccos' hv hw
      rw [h4]
      have h5 : -1 ≤ inner ℝ v w ∧ inner ℝ v w ≤ 1 := by
        have h6 : |inner ℝ v w| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
        rw [hv, hw] at h6
        exact ⟨by linarith [abs_le.mp h6], by linarith [abs_le.mp h6]⟩
      rw [Real.cos_arccos h5.1 h5.2]
    have h6 : Real.cos ang = 1 - 2 * Real.sin (ang / 2) ^ 2 := by
      have h7 : Real.cos (2 * (ang / 2)) = 2 * Real.cos (ang / 2) ^ 2 - 1 := Real.cos_two_mul (ang / 2)
      have h8 : 2 * (ang / 2) = ang := by ring
      rw [h8] at h7
      have h9 : Real.cos (ang / 2) ^ 2 = 1 - Real.sin (ang / 2) ^ 2 := by
        rw [Real.sin_sq] <;> ring
      rw [h9] at h7 <;> linarith
    have h10 : 0 ≤ Real.sin (ang / 2) := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
    have h11 : ‖v - w‖ ^ 2 = (2 * Real.sin (ang / 2)) ^ 2 := by
      rw [h2, hv, hw, h3, h6] <;> ring
    have h12 : 0 ≤ ‖v - w‖ := by positivity
    nlinarith
  by_cases h_case : ang ≤ Real.pi / 2
  · have h_acute_eq : hairbrushAcuteDirectionAngle v w = ang := by
      have h_arccos : ang = Real.arccos (inner ℝ v w) := unit_angle_eq_arccos' hv hw
      dsimp only [hairbrushAcuteDirectionAngle]
      rw [h_arccos]
      rw [min_eq_left] <;> linarith
    have h_ang_ge : theta ≤ ang := by rw [h_acute_eq] at h; exact h
    have h_sin_ge : Real.sin (theta / 2) ≤ Real.sin (ang / 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [Real.pi_pos]) (by linarith)
    rw [h_dist]
    gcongr
  · have h_gt : Real.pi / 2 < ang := by linarith
    have h_sin_gt : Real.sin (ang / 2) > Real.sqrt 2 / 2 := by
      have h1 : ang / 2 > Real.pi / 4 := by linarith [Real.pi_pos]
      have h2 : ang / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      have h3 : Real.sin (Real.pi / 4) < Real.sin (ang / 2) :=
        Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) h2 h1
      have h4 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [Real.sin_pi_div_four]
        <;> field_simp
      rw [h4] at h3
      exact h3
    have h_sin_le : 2 * Real.sin (theta / 2) ≤ theta := by
      have h5 : Real.sin (theta / 2) ≤ theta / 2 := Real.sin_le (by linarith)
      linarith
    have h_theta_le : theta ≤ 1 := htheta1
    have h_main : 2 * Real.sin (theta / 2) < 2 * Real.sin (ang / 2) := by
      have h6 : 2 * Real.sin (theta / 2) ≤ theta := h_sin_le
      have h7 : theta ≤ 1 := h_theta_le
      have h8 : (1 : ℝ) < Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h9 : 2 * Real.sin (theta / 2) < Real.sqrt 2 := by linarith
      have h10 : Real.sqrt 2 < 2 * Real.sin (ang / 2) := by linarith [h_sin_gt]
      linarith
    rw [h_dist]
    exact h_main.le

/-- Constant packing bound: theta-separated unit vectors within 2*theta of v0
have cardinality at most 1000, for 0 < theta ≤ 1/4. -/
lemma constant_direction_packing {theta : ℝ} (htheta : 0 < theta) (htheta1 : theta ≤ 1 / 4)
    {s : Finset Point3} (hs1 : ∀ v ∈ s, ‖v‖ = 1)
    (hs2 : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → theta ≤ hairbrushAcuteDirectionAngle v w)
    (v0 : Point3) (hv0 : ‖v0‖ = 1)
    (hcap : ∀ v ∈ s, hairbrushAcuteDirectionAngle v v0 ≤ 2 * theta) :
    s.card ≤ 1000 := by
  set theta_cap : ℝ := 2 * theta with htheta_cap_def
  have hcap_pos : 0 < theta_cap := by linarith
  have hcap_half : theta_cap ≤ 1 / 2 := by linarith
  set δ_pack : ℝ := Real.pi * Real.sin (theta / 2) with hδ_def
  have hδ_pos : 0 < δ_pack := by
    have h1 : 0 < theta / 2 := by linarith
    have h2 : theta / 2 < Real.pi := by
      have h3 : theta ≤ 1 / 4 := htheta1
      have h4 : Real.pi > 3 := Real.pi_gt_three
      linarith
    have h3 : 0 < Real.sin (theta / 2) := Real.sin_pos_of_pos_of_lt_pi h1 h2
    positivity
  have hδ_le_cap : δ_pack ≤ theta_cap := by
    have h1 : Real.sin (theta / 2) ≤ theta / 2 := Real.sin_le (by linarith)
    have h2 : Real.pi < 4 := Real.pi_lt_four
    have h3 : Real.pi / 2 ≤ 2 := by linarith
    calc δ_pack
      = Real.pi * Real.sin (theta / 2) := by rfl
    _ ≤ Real.pi * (theta / 2) := by gcongr
    _ = (Real.pi / 2) * theta := by ring
    _ ≤ 2 * theta := by gcongr
  have h_dist_sep : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → (2 * δ_pack / Real.pi) ≤ dist v w := by
    intro v hv w hw hne
    have h1 : (2 * δ_pack / Real.pi) = 2 * Real.sin (theta / 2) := by
      rw [hδ_def]
      field_simp [Real.pi_ne_zero] <;> ring
    rw [h1]
    exact acute_to_dist_lower (hs1 v hv) (hs1 w hw) htheta (by linarith) (hs2 v hv w hw hne)
  let sPos : Finset Point3 := s.filter (fun v => 0 ≤ inner ℝ v v0)
  let sNeg : Finset Point3 := s.filter (fun v => inner ℝ v v0 < 0)
  have h_sub_pos : sPos ⊆ s := Finset.filter_subset _ _
  have h_sub_neg : sNeg ⊆ s := Finset.filter_subset _ _
  have h_disj : Disjoint sPos sNeg := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    have h1 : 0 ≤ inner ℝ v v0 := (Finset.mem_filter.mp hv1).2
    have h2 : inner ℝ v v0 < 0 := (Finset.mem_filter.mp hv2).2
    linarith
  have h_union : sPos ∪ sNeg = s := by
    ext v
    simp only [sPos, sNeg, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hv
      by_cases h : 0 ≤ inner ℝ v v0
      · left; exact ⟨hv, h⟩
      · right; exact ⟨hv, by linarith⟩
  have h_card_sum : s.card = sPos.card + sNeg.card := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union]
  have h_side_pos : ∀ v ∈ sPos, 0 ≤ inner ℝ v v0 := by
    intro v hv; exact (Finset.mem_filter.mp hv).2
  have h_side_neg : ∀ v ∈ sNeg, 0 ≤ inner ℝ v (-v0) := by
    intro v hv
    have h : inner ℝ v v0 < 0 := (Finset.mem_filter.mp hv).2
    have h2 : inner ℝ v (-v0) = -inner ℝ v v0 := by
      simp
    rw [h2] <;> linarith
  have hcap_neg : ∀ v ∈ sNeg, hairbrushAcuteDirectionAngle v (-v0) ≤ theta_cap := by
    intro v hv
    have h1 : hairbrushAcuteDirectionAngle v (-v0) = hairbrushAcuteDirectionAngle v v0 :=
      acute_angle_neg_right
    rw [h1]
    exact hcap v (h_sub_neg hv)
  have h_pos_bound : (sPos.card : ℝ) ≤
      16 * (theta_cap / ((2 * δ_pack / Real.pi) / Real.sqrt 3))^2 :=
    same_side_direction_packing hδ_pos hδ_le_cap hcap_half
      (fun v hv => hs1 v (h_sub_pos hv))
      (fun v hv w hw hne => h_dist_sep v (h_sub_pos hv) w (h_sub_pos hw) hne)
      v0 hv0 h_side_pos
      (fun v hv => hcap v (h_sub_pos hv))
  have h_neg_bound : (sNeg.card : ℝ) ≤
      16 * (theta_cap / ((2 * δ_pack / Real.pi) / Real.sqrt 3))^2 :=
    same_side_direction_packing hδ_pos hδ_le_cap hcap_half
      (fun v hv => hs1 v (h_sub_neg hv))
      (fun v hv w hw hne => h_dist_sep v (h_sub_neg hv) w (h_sub_neg hw) hne)
      (-v0) (by simp [hv0])
      h_side_neg hcap_neg
  have h_sum : (s.card : ℝ) = (sPos.card : ℝ) + (sNeg.card : ℝ) := by
    exact_mod_cast h_card_sum
  have h_main : (s.card : ℝ) ≤
      32 * (theta_cap / ((2 * δ_pack / Real.pi) / Real.sqrt 3))^2 := by
    linarith [h_pos_bound, h_neg_bound, h_sum]
  have h_ε : (2 * δ_pack / Real.pi) = 2 * Real.sin (theta / 2) := by
    rw [hδ_def]
    field_simp [Real.pi_ne_zero] <;> ring
  rw [h_ε] at h_main
  have h_sin_bound : Real.sin (theta / 2) > (theta / 2) - (theta / 2)^3 / 4 :=
    Real.sin_gt_sub_cube (by linarith) (by linarith)
  have h_sin_lower : Real.sin (theta / 2) ≥ (theta / 2) * (255 / 256 : ℝ) := by
    have h_x2 : (theta / 2) ^ 2 ≤ 1 / 64 := by
      have h2 : theta ≤ 1 / 4 := htheta1
      nlinarith
    have h3 : (theta / 2) ^ 3 / 4 ≤ (theta / 2) * (1 / 256 : ℝ) := by
      have h4 : (theta / 2) ^ 2 ≤ 1 / 64 := h_x2
      nlinarith [htheta]
    have h5 : (theta / 2) - (theta / 2)^3 / 4 ≥ (theta / 2) * (255 / 256 : ℝ) := by nlinarith
    linarith [h_sin_bound]
  have h4 : 2 * Real.sin (theta / 2) ≥ theta * (255 / 256 : ℝ) := by
    calc 2 * Real.sin (theta / 2)
      ≥ 2 * ((theta / 2) * (255 / 256 : ℝ)) := by gcongr
    _ = theta * (255 / 256 : ℝ) := by ring
  set R : ℝ := theta_cap / ((2 * Real.sin (theta / 2)) / Real.sqrt 3) with hR_def
  have h_sin_pos : 0 < 2 * Real.sin (theta / 2) := by
    have h1 : 0 < theta / 2 := by linarith
    have h2 : theta / 2 < Real.pi := by
      have h3 : theta ≤ 1 / 4 := htheta1
      have h4 : Real.pi > 3 := Real.pi_gt_three
      linarith
    have h5 : 0 < Real.sin (theta / 2) := Real.sin_pos_of_pos_of_lt_pi h1 h2
    positivity
  have h_sqrt3_pos : 0 < Real.sqrt 3 := by positivity
  have hR_nonneg : 0 ≤ R := by positivity
  have h_eq : R = theta_cap * Real.sqrt 3 / (2 * Real.sin (theta / 2)) := by
    simp only [hR_def]
    field_simp [h_sin_pos.ne', h_sqrt3_pos.ne'] <;> ring
  have h5 : R ≤ (2 * Real.sqrt 3 * 256) / 255 := by
    rw [h_eq]
    have h_ineq : theta_cap * Real.sqrt 3 / (2 * Real.sin (theta / 2)) ≤
        (2 * theta) * Real.sqrt 3 / (theta * (255 / 256 : ℝ)) := by
      gcongr
      <;> linarith
    have h_final : (2 * theta) * Real.sqrt 3 / (theta * (255 / 256 : ℝ)) =
        (2 * Real.sqrt 3 * 256) / 255 := by
      field_simp [htheta.ne'] <;> ring
    rw [h_final] at h_ineq
    exact h_ineq
  have h6 : 32 * ((2 * Real.sqrt 3 * 256) / 255)^2 ≤ 1000 := by
    have h7 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3, h7]
  have h8 : 32 * R ^ 2 ≤ 1000 := by
    calc 32 * R ^ 2
      ≤ 32 * ((2 * Real.sqrt 3 * 256) / 255) ^ 2 := by gcongr
    _ ≤ 1000 := h6
  have h9 : 32 * (theta_cap / ((2 * Real.sin (theta / 2)) / Real.sqrt 3))^2 = 32 * R ^ 2 := by
    simp only [hR_def]
  rw [h9] at h_main
  exact_mod_cast h_main.trans h8

/-- Constant packing bound for theta ≤ 1/2: theta-separated unit vectors within
2*theta of v0 have cardinality at most 1000. Uses direction_cap_packing_2d. -/
lemma constant_direction_packing_half {theta : ℝ} (htheta : 0 < theta) (htheta1 : theta ≤ 1 / 2)
    {s : Finset Point3} (hs1 : ∀ v ∈ s, ‖v‖ = 1)
    (hs2 : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → theta ≤ hairbrushAcuteDirectionAngle v w)
    (v0 : Point3) (hv0 : ‖v0‖ = 1)
    (hcap : ∀ v ∈ s, hairbrushAcuteDirectionAngle v v0 ≤ 2 * theta) :
    s.card ≤ 1000 := by
  set δ : ℝ := Real.pi * Real.sin (theta / 2) with hδ_def
  have hδ_pos : 0 < δ := by
    have h1 : 0 < theta / 2 := by linarith
    have h2 : theta / 2 < Real.pi := by
      have h3 : theta ≤ 1 / 2 := htheta1
      have h4 : Real.pi > 3 := Real.pi_gt_three
      linarith
    have h3 : 0 < Real.sin (theta / 2) := Real.sin_pos_of_pos_of_lt_pi h1 h2
    positivity
  have hδ1 : δ ≤ 1 := by
    have h1 : Real.sin (theta / 2) ≤ theta / 2 := Real.sin_le (by linarith)
    have h2 : Real.pi < 4 := Real.pi_lt_four
    calc δ
      = Real.pi * Real.sin (theta / 2) := by rfl
    _ ≤ Real.pi * (theta / 2) := by gcongr
    _ = (Real.pi / 2) * theta := by ring
    _ ≤ (Real.pi / 2) * (1 / 2) := by gcongr
    _ ≤ 1 := by linarith [Real.pi_lt_four]
  have htheta_cap : δ ≤ 2 * theta := by
    have h1 : Real.sin (theta / 2) ≤ theta / 2 := Real.sin_le (by linarith)
    calc δ
      = Real.pi * Real.sin (theta / 2) := by rfl
    _ ≤ Real.pi * (theta / 2) := by gcongr
    _ = (Real.pi / 2) * theta := by ring
    _ ≤ 2 * theta := by
      have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
      exact mul_le_mul_of_nonneg_right hpi (by linarith)
  have htheta_cap1 : 2 * theta ≤ 1 := by linarith
  have h_dist_sep : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → (2 * δ / Real.pi) ≤ dist v w := by
    intro v hv w hw hne
    have h1 : (2 * δ / Real.pi) = 2 * Real.sin (theta / 2) := by
      rw [hδ_def]
      field_simp [Real.pi_ne_zero] <;> ring
    rw [h1]
    exact acute_to_dist_lower (hs1 v hv) (hs1 w hw) htheta (by linarith) (hs2 v hv w hw hne)
  have h_main : (s.card : ℝ) ≤ 300 * ((2 * theta) / δ)^2 :=
    direction_cap_packing_2d hδ_pos hδ1 htheta_cap htheta_cap1 hs1 h_dist_sep v0 hv0 hcap
  have h_sin_lower : Real.sin (theta / 2) ≥ (theta / 2) * (63 / 64 : ℝ) := by
    have h_x_le : theta / 2 ≤ 1 / 4 := by linarith
    have h_sin_gt : Real.sin (theta / 2) > (theta / 2) - (theta / 2)^3 / 4 :=
      Real.sin_gt_sub_cube (by linarith) (by linarith)
    have h_x2 : (theta / 2)^2 ≤ 1 / 16 := by nlinarith
    have h3 : (theta / 2) - (theta / 2)^3 / 4 ≥ (theta / 2) * (63 / 64 : ℝ) := by
      have h4 : (theta / 2)^2 ≤ 1 / 16 := h_x2
      nlinarith [htheta]
    linarith [h_sin_gt]
  have h4 : δ ≥ theta * (63 / 64 : ℝ) * Real.pi / 2 := by
    calc δ
      = Real.pi * Real.sin (theta / 2) := by rfl
    _ ≥ Real.pi * ((theta / 2) * (63 / 64 : ℝ)) := by gcongr
    _ = theta * (63 / 64 : ℝ) * Real.pi / 2 := by ring
  have h5 : (2 * theta) / δ ≤ (256 : ℝ) / (63 * Real.pi) := by
    have hδ_pos' : 0 < δ := hδ_pos
    calc (2 * theta) / δ
      ≤ (2 * theta) / (theta * (63 / 64 : ℝ) * Real.pi / 2) := by gcongr
    _ = (256 : ℝ) / (63 * Real.pi) := by
      field_simp [htheta.ne', Real.pi_ne_zero] <;> ring
  have h6 : 300 * (((256 : ℝ) / (63 * Real.pi))^2) ≤ 1000 := by
    have h7 : Real.pi ^ 2 > 9 := by nlinarith [Real.pi_gt_three]
    have h8 : 19660800 ≤ 3969000 * Real.pi ^ 2 := by
      have h9 : 3969000 * Real.pi ^ 2 > 3969000 * (9 : ℝ) := by gcongr
      have h10 : 3969000 * (9 : ℝ) = 35721000 := by norm_num
      have h11 : (19660800 : ℝ) ≤ 35721000 := by norm_num
      linarith
    have h13 : 0 < 3969 * Real.pi ^ 2 := by positivity
    have h14 : 300 * (((256 : ℝ) / (63 * Real.pi))^2) =
        (19660800 : ℝ) / (3969 * Real.pi ^ 2) := by
      field_simp [Real.pi_ne_zero] <;> ring
    rw [h14]
    have h15 : (19660800 : ℝ) / (3969 * Real.pi ^ 2) ≤ 1000 := by
      calc (19660800 : ℝ) / (3969 * Real.pi ^ 2)
        ≤ (19660800 : ℝ) / (3969 * (9 : ℝ)) := by gcongr <;> nlinarith [Real.pi_gt_three]
      _ = (19660800 : ℝ) / 35721 := by norm_num
      _ ≤ 1000 := by norm_num
    exact h15
  have h8 : 300 * ((2 * theta) / δ)^2 ≤ 1000 := by
    calc 300 * ((2 * theta) / δ)^2
      ≤ 300 * (((256 : ℝ) / (63 * Real.pi))^2) := by gcongr
    _ ≤ 1000 := h6
  exact_mod_cast h_main.trans h8

end Kakeya.Assouad
