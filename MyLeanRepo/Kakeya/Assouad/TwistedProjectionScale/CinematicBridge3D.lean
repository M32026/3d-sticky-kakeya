import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CinematicFiniteFamily
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ExtendedCinematicFamily
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.UpperBound
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.LowerBound
import MyLeanRepo.Kakeya.Assouad.Inputs
import MyLeanRepo.Kakeya.Cinematic.Definitions

/-!
# Cinematic bridge at scale w (3D parameter version)

Maps a 3D discrete set with Katz-Tao bound (exponent 1) at scale w to a
cinematic family, transfers the bound, selects a w-separated subfamily,
and applies the PYZ maximal estimate.

Returns both the full family and the selected subfamily with a covering
property, so the assembly can relate their multiplicities.
-/

noncomputable section

open Kakeya.Cinematic Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Map a 3D discrete set to cinematic curves with denormalized coordinates.
Normalized p ∈ unit ball maps to raw parameters (12*p0, 12*p1, 2*p2). -/
def discreteSet3ToCinematicFamily (f : SlopeFunction)
    (A : DiscreteSet 3) : FiniteFunctionFamily :=
  let img : Finset C2Function :=
    A.image (fun p : Point 3 => slopeCurve f (12 * p 0) (12 * p 1) (2 * p 2))
  ⟨(img : Set C2Function), Finset.finite_toSet img⟩

/-- Coordinate bound from unit ball membership. -/
lemma coord_bound_from_unitBall3 {n : ℕ} {p : Point n} {i : Fin n}
    (h : dist p 0 ≤ 1) : |p i| ≤ 1 := by
  have h_norm : ‖p‖ ≤ 1 := by simpa [dist_eq_norm] using h
  have h1 : (p i)^2 ≤ ‖p‖^2 := by
    have h2 : ‖p‖^2 = ∑ j : Fin n, (p j)^2 := EuclideanSpace.real_norm_sq_eq p
    rw [h2]
    apply Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  have h3 : 0 ≤ ‖p‖ := by positivity
  have h4 : (|p i|)^2 = (p i)^2 := by simp [sq_abs]
  have h5 : |p i| ≤ ‖p‖ := by nlinarith [abs_nonneg (p i)]
  linarith

/-- Every curve from a unit-ball 3D discrete set belongs to the extended family
after denormalization: |12*p0|≤12, |12*p1|≤12, |2*p2|≤2. -/
lemma discreteSet3ToExtendedFamily_mem
    (f : SlopeFunction) (A : DiscreteSet 3)
    (hA_unit : A.IsInUnitBall) :
    (discreteSet3ToCinematicFamily f A).carrier ⊆ extendedSlopeCurveFamily f := by
  intro g hg
  have h_img : ∃ (p : Point 3), p ∈ A ∧
      slopeCurve f (12 * p 0) (12 * p 1) (2 * p 2) = g := by
    simpa [discreteSet3ToCinematicFamily, Finset.mem_image, eq_comm] using hg
  rcases h_img with ⟨p, hp, rfl⟩
  have h_unit : dist p 0 ≤ 1 := hA_unit p hp
  have h1 : |p 0| ≤ 1 := coord_bound_from_unitBall3 h_unit
  have h2 : |p 1| ≤ 1 := coord_bound_from_unitBall3 h_unit
  have h3 : |p 2| ≤ 1 := coord_bound_from_unitBall3 h_unit
  have h1' : |12 * p 0| ≤ 12 := by
    have h : |12 * p 0| = 12 * |p 0| := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 12 by norm_num)]
    rw [h] <;> linarith
  have h2' : |12 * p 1| ≤ 12 := by
    have h : |12 * p 1| = 12 * |p 1| := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 12 by norm_num)]
    rw [h] <;> linarith
  have h3' : |2 * p 2| ≤ 2 := by
    have h : |2 * p 2| = 2 * |p 2| := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    rw [h] <;> linarith
  let q : Fin 3 → ℝ := fun i =>
    if i = 0 then 12 * p 0
    else if i = 1 then 12 * p 1
    else 2 * p 2
  have hq0 : q 0 = 12 * p 0 := by simp [q]
  have hq1 : q 1 = 12 * p 1 := by simp [q]
  have hq2 : q 2 = 2 * p 2 := by simp [q]
  have hq : q ∈ extendedParamBox := by
    simp only [extendedParamBox, Set.mem_setOf_eq]
    exact ⟨h1', h2', h3'⟩
  have h_eq : slopeCurve f (q 0) (q 1) (q 2) = slopeCurve f (12 * p 0) (12 * p 1) (2 * p 2) := by
    rw [hq0, hq1, hq2]
  exact ⟨q, hq, h_eq⟩

/-- Lower bound: cinematic C² distance controls parameter L¹ distance. -/
lemma slopeCurve_c2Distance_ge3 (f : SlopeFunction)
    (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (a₁ b₁ d₁ a₂ b₂ d₂ : ℝ) :
    (11 / 2500 : ℝ) * (|a₁ - a₂| + |b₁ - b₂| + |d₁ - d₂|) ≤
    c2Distance (slopeCurve f a₁ b₁ d₁) (slopeCurve f a₂ b₂ d₂) := by
  let g1 := slopeCurve f a₁ b₁ d₁
  let g2 := slopeCurve f a₂ b₂ d₂
  have hrep1 := slopeCurve_represents f a₁ b₁ d₁
  have hrep2 := slopeCurve_represents f a₂ b₂ d₂
  have h_lower : (99 / 7500 : ℝ) * (|a₁ - a₂| + |b₁ - b₂| + |d₁ - d₂|) ≤
      jetGap g1 g2 midpoint :=
    slopeCurve_jetGap_ge f h_ns h0 g1 g2 a₁ b₁ d₁ a₂ b₂ d₂ hrep1 hrep2 midpoint
  have h_upper : jetGap g1 g2 midpoint ≤ 3 * c2Distance g1 g2 :=
    jetGap_le_three_mul_c2Distance g1 g2 midpoint
  have h_main : (99 / 7500 : ℝ) * (|a₁ - a₂| + |b₁ - b₂| + |d₁ - d₂|) ≤
      3 * c2Distance g1 g2 := by linarith
  have h : (99 / 7500 : ℝ) = 3 * (11 / 2500 : ℝ) := by norm_num
  rw [h] at h_main
  linarith

/-- L2 distance ≤ L1 distance for 3D points. -/
lemma dist3_le_L1 (p q : Point 3) :
    dist p q ≤ |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| := by
  set L := |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| with hL
  have h1 : (dist p q)^2 = (p 0 - q 0)^2 + (p 1 - q 1)^2 + (p 2 - q 2)^2 := by
    have h11 : (dist p q)^2 = ‖p - q‖^2 := by simp [dist_eq_norm]
    rw [h11]
    have h12 : ‖p - q‖^2 = ∑ i : Fin 3, ((p - q) i)^2 := EuclideanSpace.real_norm_sq_eq (p - q)
    rw [h12]
    simp [Fin.sum_univ_three] <;> ring
  set a := |p 0 - q 0| with ha
  set b := |p 1 - q 1| with hb
  set c := |p 2 - q 2| with hc
  have ha2 : (p 0 - q 0)^2 = a^2 := by simp [ha, sq_abs]
  have hb2 : (p 1 - q 1)^2 = b^2 := by simp [hb, sq_abs]
  have hc2 : (p 2 - q 2)^2 = c^2 := by simp [hc, sq_abs]
  have hLdef : L = a + b + c := by
    simp [hL, ha, hb, hc] <;> ring
  have h2 : (dist p q)^2 ≤ L^2 := by
    rw [h1, ha2, hb2, hc2, hLdef]
    have ha_pos : 0 ≤ a := by positivity
    have hb_pos : 0 ≤ b := by positivity
    have hc_pos : 0 ≤ c := by positivity
    nlinarith [mul_nonneg ha_pos hb_pos, mul_nonneg ha_pos hc_pos,
      mul_nonneg hb_pos hc_pos]
  have h3 : 0 ≤ dist p q := by positivity
  have h4 : 0 ≤ L := by positivity
  nlinarith

/-- Greedy ε-separated subset of a finite set, with covering property. -/
lemma exists_greedy_separated3 {X : Type*} [MetricSpace X] {ε : ℝ} (hε : 0 < ε)
    (S : Finset X) :
    ∃ (S' : Finset X), S' ⊆ S ∧
      (∀ x ∈ S', ∀ y ∈ S', x ≠ y → ε ≤ dist x y) ∧
      (∀ x ∈ S, ∃ y ∈ S', dist x y < ε) := by
  let P : Finset X → Prop := fun T =>
    T ⊆ S ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ε ≤ dist x y
  let candidates := (Finset.powerset S).filter P
  have hP_empty : P (∅ : Finset X) := by
    exact ⟨by simp, by simp⟩
  have h_nonempty : candidates.Nonempty := by
    exact ⟨(∅ : Finset X), by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset, hP_empty] <;> simp⟩
  rcases Finset.exists_max_image candidates (fun T : Finset X => T.card) h_nonempty with
    ⟨S', hS'_in, h_max⟩
  have hP : P S' := by
    have h : S' ∈ candidates := hS'_in
    simp only [candidates, Finset.mem_filter] at h
    exact h.2
  refine' ⟨S', hP.1, hP.2, _⟩
  intro x hx
  by_contra h
  push Not at h
  let T := insert x S'
  have h_x_notin : x ∉ S' := by
    intro hxin
    have h' : ε ≤ dist x x := h x hxin
    have h0 : dist x x = 0 := dist_self x
    rw [h0] at h'
    linarith
  have hT_sub : T ⊆ S := by
    intro z hz
    simp only [T, Finset.mem_insert] at hz
    rcases hz with (rfl | hz) <;> tauto
  have hT_sep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ε ≤ dist a b := by
    intro a ha b hb hne
    have ha' : a = x ∨ a ∈ S' := by simpa [T, Finset.mem_insert] using ha
    have hb' : b = x ∨ b ∈ S' := by simpa [T, Finset.mem_insert] using hb
    rcases ha' with (h_a_eq | ha_in)
    · rcases hb' with (h_b_eq | hb_in)
      · exfalso; exact hne (by rw [h_a_eq, h_b_eq])
      · rw [h_a_eq]; exact h b hb_in
    · rcases hb' with (h_b_eq | hb_in)
      · have h1 : ε ≤ dist x a := h a ha_in
        rw [h_b_eq]
        have h_sym : dist a x = dist x a := dist_comm a x
        rw [h_sym]; exact h1
      · exact hP.2 a ha_in b hb_in hne
  have hPT : P T := ⟨hT_sub, hT_sep⟩
  have h_card : T.card = S'.card + 1 := by
    have h : T = insert x S' := by rfl
    rw [h]
    simp [h_x_notin]
  have hT_in : T ∈ candidates := by
    simp only [candidates, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr hPT.1, hPT⟩
  have h_contra : T.card ≤ S'.card := h_max T hT_in
  rw [h_card] at h_contra
  linarith


/-- Global cardinality bound from unit-ball KT at radius 1. -/
lemma unitBall_global_card (A : DiscreteSet 3) (w : ℝ) (hw : 0 < w) (hw_le1 : w ≤ 1)
    (hKT : A.IsKatzTao w 1 100) (hA_unit : A.IsInUnitBall) :
    (A.card : ℝ) ≤ 100 / w := by
  have h1 : A.filter (fun p : Point 3 => dist p 0 ≤ 1) = A := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, _⟩; exact hp
    · intro hp; exact ⟨hp, hA_unit p hp⟩
  have hKT' := hKT 0 1 hw_le1 (by norm_num)
  have h_eq : A.ballCount 0 1 = (A.card : ENNReal) := by
    rw [DiscreteSet.ballCount, h1]
    <;> rfl
  rw [h_eq] at hKT'
  have h_rpow : Kakeya.realRpowENN (1 / w) 1 = ENNReal.ofReal (1 / w) := by
    simp [Kakeya.realRpowENN, Real.rpow_one]
  rw [h_rpow] at hKT'
  have h_mul : (100 : ENNReal) * ENNReal.ofReal (1 / w) = ENNReal.ofReal (100 / w) := by
    have h_w_pos : 0 < w := hw
    have h : (100 : ENNReal) = ENNReal.ofReal (100 : ℝ) := by simp
    rw [h]
    have h2 : ENNReal.ofReal (100 : ℝ) * ENNReal.ofReal (1 / w) =
        ENNReal.ofReal ((100 : ℝ) * (1 / w)) := by
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (100 : ℝ) by norm_num)]
    rw [h2]
    have h3 : (100 : ℝ) * (1 / w) = 100 / w := by
      field_simp [h_w_pos.ne'] <;> ring
    rw [h3]
  rw [h_mul] at hKT'
  have h_card_cast : (A.card : ENNReal) = ENNReal.ofReal (A.card : ℝ) := by simp
  rw [h_card_cast] at hKT'
  have h_y_pos : 0 ≤ 100 / w := by positivity
  have h_iff : (ENNReal.ofReal (A.card : ℝ) ≤ ENNReal.ofReal (100 / w)) ↔ (A.card : ℝ) ≤ 100 / w :=
    ENNReal.ofReal_le_ofReal_iff h_y_pos
  exact h_iff.mp hKT'

/-- Transfer Katz-Tao (exponent 1) from normalized 3D parameter space to cinematic space.

Uses denormalized curves slopeCurve f (12*p0) (12*p1) (2*p2).
The c2Distance lower bound gives:
  c2Distance >= (11/2500) * (12|dp0| + 12|dp1| + 2|dp2|) >= (22/2500) * dist(p,p0)
So a cinematic r-ball preimage is a normalized ball of radius R = 250*r.
Constant C_KT = 25000. -/
lemma cinematicKatzTao_transfer3
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (A : DiscreteSet 3) (w : ℝ) (hw : 0 < w) (hw_le1 : w ≤ 1)
    (hKT : A.IsKatzTao w 1 100)
    (hA_unit : A.IsInUnitBall) :
    HasCinematicKatzTaoBound (discreteSet3ToCinematicFamily f A) w 25000 := by
  let φ : Point 3 → C2Function := fun p => slopeCurve f (12 * p 0) (12 * p 1) (2 * p 2)
  let F := discreteSet3ToCinematicFamily f A
  let C_KT : ℝ := 25000
  have hF_def : F.carrier = φ '' A := by
    simp [F, discreteSet3ToCinematicFamily, φ] <;> rfl
  have hA_card_le : (A.card : ℝ) ≤ 100 / w :=
    unitBall_global_card A w hw hw_le1 hKT hA_unit
  have hF_card_le_A : F.card ≤ A.card := by
    have h_eq1 : φ '' (A : Set (Point 3)) = (A.image φ : Set C2Function) := by
      ext x; simp [Set.mem_image, Finset.mem_image] <;> tauto
    have h3 : F.carrier.ncard = (A.image φ).card := by
      rw [hF_def, h_eq1]
      exact ncard_coe_finset (A.image φ)
    have h4 : F.card = F.carrier.ncard := by rfl
    rw [h4, h3]
    have h_card_le : (A.image φ).card ≤ A.card := Finset.card_image_le
    exact h_card_le
  have h_global : (F.card : ℝ) ≤ C_KT / w := by
    have h4 : (F.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hF_card_le_A
    have h5 : (A.card : ℝ) ≤ 100 / w := hA_card_le
    have h6 : (100 : ℝ) / w ≤ C_KT / w := by gcongr <;> norm_num
    linarith
  have h_local : ∀ (center : C2Function) (r : ℝ), w ≤ r → r ≤ 1 →
      ((F.carrier ∩ c2Ball center r).ncard : ℝ) ≤ C_KT * (r / w) := by
    intro center r hr_ge hr_le
    let P : Finset (Point 3) := A.filter (fun p => φ p ∈ c2Ball center r)
    have hP_sub : P ⊆ A := Finset.filter_subset _ _
    have h_image : F.carrier ∩ c2Ball center r = φ '' P := by
      rw [hF_def]
      ext y
      simp only [P, Set.mem_image, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨p, hpA, rfl⟩, hball⟩
        exact ⟨p, ⟨hpA, hball⟩, rfl⟩
      · rintro ⟨p, ⟨hpA, hball⟩, rfl⟩
        exact ⟨⟨p, hpA, rfl⟩, hball⟩
    have h_ncard_le : (F.carrier ∩ c2Ball center r).ncard ≤ P.card := by
      rw [h_image]
      have h_eq1 : φ '' (P : Set (Point 3)) = (P.image φ : Set C2Function) := by
        ext x; simp [Set.mem_image, Finset.mem_image] <;> tauto
      rw [h_eq1]
      have h4 : ((P.image φ : Set C2Function).ncard) = (P.image φ).card := by
        exact ncard_coe_finset (P.image φ)
      rw [h4]
      have h_card_le : (P.image φ).card ≤ P.card := Finset.card_image_le
      exact h_card_le
    by_cases hP_empty : P = ∅
    · have h_card0 : P.card = 0 := by rw [hP_empty] <;> simp
      have h_eq0 : (F.carrier ∩ c2Ball center r).ncard = 0 := by
        have h_le : (F.carrier ∩ c2Ball center r).ncard ≤ 0 := by
          rw [h_card0] at h_ncard_le <;> exact h_ncard_le
        omega
      have h_goal : ((F.carrier ∩ c2Ball center r).ncard : ℝ) ≤ C_KT * (r / w) := by
        rw [h_eq0] <;> simp
        have h_r_nonneg : 0 ≤ r := by linarith [hw, hr_ge]
        have h_CKT_nonneg : 0 ≤ C_KT := by positivity
        positivity
      exact h_goal
    · rcases Finset.nonempty_iff_ne_empty.mpr hP_empty with ⟨p0, hp0⟩
      have hr_pos : 0 < r := by linarith [hw, hr_ge]
      let R : ℝ := 250 * r
      have hR_pos : 0 < R := by
        dsimp only [R] <;> exact mul_pos (by norm_num) hr_pos
      have h_ball : ∀ p ∈ P, dist p p0 ≤ R := by
        intro p hp
        have h_pb : φ p ∈ c2Ball center r := (Finset.mem_filter.mp hp).2
        have h_p0b : φ p0 ∈ c2Ball center r := (Finset.mem_filter.mp hp0).2
        have h_dist_c2 : c2Distance (φ p) (φ p0) ≤ 2 * r := by
          have h1 : c2Distance (φ p) center ≤ r := h_pb
          have h2 : c2Distance (φ p0) center ≤ r := h_p0b
          have h3 : c2Distance (φ p) (φ p0) ≤ c2Distance (φ p) center + c2Distance center (φ p0) :=
            dist_triangle _ _ _
          have h4 : c2Distance center (φ p0) = c2Distance (φ p0) center := dist_comm _ _
          rw [h4] at h3 <;> linarith
        have h_lower_raw : (11 / 2500 : ℝ) *
            (|12 * p 0 - 12 * p0 0| + |12 * p 1 - 12 * p0 1| + |2 * p 2 - 2 * p0 2|) ≤
            c2Distance (φ p) (φ p0) :=
          slopeCurve_c2Distance_ge3 f h_ns h0
            (12 * p 0) (12 * p 1) (2 * p 2)
            (12 * p0 0) (12 * p0 1) (2 * p0 2)
        have h_abs1 : |12 * p 0 - 12 * p0 0| = 12 * |p 0 - p0 0| := by
          have h : (12 * p 0 - 12 * p0 0) = 12 * (p 0 - p0 0) := by ring
          rw [h, abs_mul, abs_of_pos (show (0 : ℝ) < 12 by norm_num)]
        have h_abs2 : |12 * p 1 - 12 * p0 1| = 12 * |p 1 - p0 1| := by
          have h : (12 * p 1 - 12 * p0 1) = 12 * (p 1 - p0 1) := by ring
          rw [h, abs_mul, abs_of_pos (show (0 : ℝ) < 12 by norm_num)]
        have h_abs3 : |2 * p 2 - 2 * p0 2| = 2 * |p 2 - p0 2| := by
          have h : (2 * p 2 - 2 * p0 2) = 2 * (p 2 - p0 2) := by ring
          rw [h, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        have h_lower : (11 / 2500 : ℝ) *
            (12 * |p 0 - p0 0| + 12 * |p 1 - p0 1| + 2 * |p 2 - p0 2|) ≤
            c2Distance (φ p) (φ p0) := by
          rw [h_abs1, h_abs2, h_abs3] at h_lower_raw
          exact h_lower_raw
        have hL1 : dist p p0 ≤ |p 0 - p0 0| + |p 1 - p0 1| + |p 2 - p0 2| :=
          dist3_le_L1 p p0
        have h_sum : 12 * |p 0 - p0 0| + 12 * |p 1 - p0 1| + 2 * |p 2 - p0 2| ≥
            2 * dist p p0 := by
          have h4 : 2 * dist p p0 ≤ 2 * (|p 0 - p0 0| + |p 1 - p0 1| + |p 2 - p0 2|) := by
            gcongr
          have h5 : 2 * (|p 0 - p0 0| + |p 1 - p0 1| + |p 2 - p0 2|) ≤
              12 * |p 0 - p0 0| + 12 * |p 1 - p0 1| + 2 * |p 2 - p0 2| := by
            simp [mul_add] <;> linarith [abs_nonneg (p 0 - p0 0), abs_nonneg (p 1 - p0 1), abs_nonneg (p 2 - p0 2)]
          linarith
        have h_main : 2 * dist p p0 ≤ (2500 / 11 : ℝ) * (2 * r) := by
          linarith [h_lower, h_sum]
        have h_final : dist p p0 ≤ R := by
          dsimp only [R]
          linarith
        exact h_final
      have hP_filter : P ⊆ A.filter (fun y => dist y p0 ≤ R) := by
        intro p hp
        have h1 : p ∈ A := (Finset.mem_filter.mp hp).1
        have h2 : dist p p0 ≤ R := h_ball p hp
        simp only [Finset.mem_filter] <;> exact ⟨h1, h2⟩
      have h_card_le : P.card ≤ (A.filter (fun y => dist y p0 ≤ R)).card :=
        Finset.card_le_card hP_filter
      by_cases hR_le1 : R ≤ 1
      · have hR_ge_w : w ≤ R := by dsimp only [R] <;> nlinarith
        have hKT' := hKT p0 R hR_ge_w hR_le1
        have h_ballCount_eq : A.ballCount p0 R =
            ((A.filter (fun y => dist y p0 ≤ R)).card : ENNReal) := by rfl
        rw [h_ballCount_eq] at hKT'
        have h_rpow : Kakeya.realRpowENN (R / w) 1 = ENNReal.ofReal (R / w) := by
          simp [Kakeya.realRpowENN, Real.rpow_one]
        rw [h_rpow] at hKT'
        have h_mul : (100 : ENNReal) * ENNReal.ofReal (R / w) =
            ENNReal.ofReal (100 * R / w) := by
          have h : (100 : ENNReal) = ENNReal.ofReal (100 : ℝ) := by simp
          rw [h]
          rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (100 : ℝ) by norm_num)]
          <;> ring_nf
        rw [h_mul] at hKT'
        have h_card_ofReal : ((A.filter (fun y => dist y p0 ≤ R)).card : ENNReal) =
            ENNReal.ofReal ((A.filter (fun y => dist y p0 ≤ R)).card : ℝ) := by simp
        rw [h_card_ofReal] at hKT'
        have h_y_pos : 0 ≤ 100 * R / w := by positivity
        have h_iff := @ENNReal.ofReal_le_ofReal_iff
          ((A.filter (fun y => dist y p0 ≤ R)).card : ℝ) (100 * R / w) h_y_pos
        have h_card_real : ((A.filter (fun y => dist y p0 ≤ R)).card : ℝ) ≤ 100 * R / w :=
          h_iff.mp hKT'
        have h_card_le' : (P.card : ℝ) ≤ ((A.filter (fun y => dist y p0 ≤ R)).card : ℝ) := by
          exact_mod_cast h_card_le
        have h_final : (P.card : ℝ) ≤ 100 * R / w := le_trans h_card_le' h_card_real
        dsimp only [R] at h_final
        have h : 100 * (250 * r) / w ≤ C_KT * (r / w) := by
          have hpos : 0 < w := hw
          have h9 : (100 * 250 : ℝ) ≤ C_KT := by norm_num [C_KT]
          have h10 : 100 * (250 * r) / w = (100 * 250 : ℝ) * (r / w) := by
            field_simp [hpos.ne'] <;> ring
          rw [h10] <;> gcongr
        have h_main : ((F.carrier ∩ c2Ball center r).ncard : ℝ) ≤ (P.card : ℝ) := by
          exact_mod_cast h_ncard_le
        linarith
      · have hR_gt1 : 1 < R := by linarith
        have h_final : (P.card : ℝ) ≤ 100 / w := by
          have h1 : (P.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hP_sub
          linarith [hA_card_le]
        have h_r_gt : r > 1 / 250 := by
          dsimp only [R] at hR_gt1 <;> nlinarith
        have h_ineq : (100 : ℝ) / w ≤ C_KT * (r / w) := by
          have hpos : 0 < w := hw
          have h : (100 : ℝ) ≤ C_KT * r := by nlinarith
          have h2 : (100 : ℝ) / w ≤ (C_KT * r) / w := by gcongr
          have h3 : (C_KT * r) / w = C_KT * (r / w) := by ring
          rw [h3] at h2 <;> exact h2
        have h_main : ((F.carrier ∩ c2Ball center r).ncard : ℝ) ≤ (P.card : ℝ) := by
          exact_mod_cast h_ncard_le
        linarith
  exact ⟨h_global, h_local⟩

/-- Main cinematic bridge (3D version): produce PYZ threshold and apply at any scale w ≤ it.

Returns the full cinematic family F_full, a w-separated subfamily F_sel,
the covering property (every F_full curve is within w of some F_sel curve),
the KT bound on F_full, and the PYZ multiplicity bound on F_sel. -/
theorem cinematic_bridge_pyz_3d
    (pyz : PYZInput)
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (epsilon_PYZ : ℝ) (hepsilon : 0 < epsilon_PYZ)
    (lambda : ℝ) (hlambda : 1 ≤ lambda) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 / lambda ∧
      ∀ (w : ℝ), 0 < w → w ≤ delta₀ →
        ∀ (A : DiscreteSet 3), A.IsKatzTao w 1 100 →
          A.IsInUnitBall →
          ∃ (family : Set C2Function) (K D C_KT : ℝ),
            1 ≤ K ∧ 1 ≤ D ∧ 1 ≤ C_KT ∧
            IsCinematicFamily family K D ∧
            ∃ (F_full F_sel : FiniteFunctionFamily),
              F_full.carrier ⊆ family ∧
              F_sel.carrier ⊆ F_full.carrier ∧
              IsCinematicDeltaSeparated F_sel w ∧
              HasCinematicKatzTaoBound F_full w C_KT ∧
              (∀ g ∈ F_full.carrier, ∃ h ∈ F_sel.carrier, c2Distance g h ≤ w) ∧
              MeasureTheory.eLpNorm
                (Kakeya.Cinematic.multiplicity F_sel (lambda * w))
                (3 / 2 : ENNReal) MeasureTheory.volume ≤
                ENNReal.ofReal (Real.rpow w (-epsilon_PYZ)) := by
  let C_KT : ℝ := 25000
  have hC_KT_ge1 : 1 ≤ C_KT := by norm_num
  let K : ℝ := 37500 / 99
  let D : ℝ := (216 ^ 12 : ℝ)
  let M : ℝ := 40
  have hK1 : 1 ≤ K := by norm_num [K]
  have hD1 : 1 ≤ D := by norm_num [D]
  have hM0 : 0 ≤ M := by norm_num [M]
  let family : Set C2Function := extendedSlopeCurveFamily f
  have h_cinematic : IsCinematicFamily family K D := extended_cinematic_family' f h_ns h0
  have h_jet_bound :
      ∀ g ∈ family, ∀ x : UnitPoint,
        |g x| ≤ M ∧
          |g.firstDeriv x| ≤ M ∧
          |g.secondDeriv x| ≤ M := by
    simpa [family, M] using
      extendedSlopeCurveFamily_jet_bound f h_ns h0
  have h_pyz :=
    pyz K D C_KT lambda M hK1 hD1 hC_KT_ge1 hlambda hM0
      epsilon_PYZ hepsilon
  rcases h_pyz with ⟨delta₀, hdelta₀_pos, hdelta₀_le, h_pyz_main⟩
  refine' ⟨delta₀, hdelta₀_pos, hdelta₀_le, _⟩
  intro w hw hw_le A hKT hA_unit
  have hw_le1 : w ≤ 1 := by
    have h1 : w ≤ delta₀ := hw_le
    have h2 : delta₀ ≤ 1 / lambda := hdelta₀_le
    have h3 : 1 / lambda ≤ 1 := by
      have h4 : 1 ≤ lambda := hlambda
      exact (div_le_one (by linarith)).mpr h4
    linarith
  let F_full := discreteSet3ToCinematicFamily f A
  have hKT_full : HasCinematicKatzTaoBound F_full w C_KT :=
    cinematicKatzTao_transfer3 f h_ns h0 A w hw hw_le1 hKT hA_unit
  have h_mem_full : F_full.carrier ⊆ family :=
    discreteSet3ToExtendedFamily_mem f A hA_unit
  rcases exists_greedy_separated3 hw F_full.toFinset with ⟨S', hS'_sub, hS'_sep, hS'_cover⟩
  let F_sel : FiniteFunctionFamily :=
    ⟨(S' : Set C2Function), Finset.finite_toSet S'⟩
  have h_sel_sub : F_sel.carrier ⊆ F_full.carrier := by
    have h : (S' : Set C2Function) ⊆ (F_full.toFinset : Set C2Function) := by
      exact_mod_cast hS'_sub
    have h2 : F_sel.carrier = (S' : Set C2Function) := by rfl
    have h3 : F_full.carrier = (F_full.toFinset : Set C2Function) := by
      exact (Set.Finite.coe_toFinset F_full.finite).symm
    rw [h2, h3]
    exact h
  have h_sel_family : F_sel.carrier ⊆ family :=
    Set.Subset.trans h_sel_sub h_mem_full
  have h_sel_sep : IsCinematicDeltaSeparated F_sel w := by
    intro g hg h hh hne
    exact hS'_sep g hg h hh hne
  have h_cover : ∀ g ∈ F_full.carrier, ∃ h ∈ F_sel.carrier, c2Distance g h ≤ w := by
    intro g hg
    have h1 : g ∈ F_full.toFinset := by
      have h2 : F_full.carrier = (F_full.toFinset : Set C2Function) :=
        (Set.Finite.coe_toFinset F_full.finite).symm
      rw [h2] at hg
      exact_mod_cast hg
    rcases hS'_cover g h1 with ⟨h, hh_in, h_dist⟩
    have h3 : h ∈ F_sel.carrier := by
      have h4 : F_sel.carrier = (S' : Set C2Function) := by rfl
      rw [h4]
      exact_mod_cast hh_in
    have h_dist' : c2Distance g h < w := by
      rw [c2Distance_eq_dist]
      exact h_dist
    have h5 : c2Distance g h ≤ w := by linarith
    exact ⟨h, h3, h5⟩
  have h_sel_KT : HasCinematicKatzTaoBound F_sel w C_KT := by
    have h_sel_card : F_sel.card ≤ F_full.card := by
      have h2 : F_sel.card = S'.card := by
        have h21 : F_sel.card = F_sel.carrier.ncard := by rfl
        rw [h21]
        have h22 : F_sel.carrier = (S' : Set C2Function) := by rfl
        rw [h22]
        simp [Set.ncard]
      have h3 : F_full.card = F_full.toFinset.card := by
        have h31 : F_full.card = F_full.carrier.ncard := by rfl
        rw [h31]
        have h32 : F_full.carrier = (F_full.toFinset : Set C2Function) := by
          exact (Set.Finite.coe_toFinset F_full.finite).symm
        rw [h32]
        simp [Set.ncard]
      rw [h2, h3]
      exact Finset.card_le_card hS'_sub
    constructor
    · have h1 : (F_sel.card : ℝ) ≤ (F_full.card : ℝ) := by exact_mod_cast h_sel_card
      have h2 := hKT_full.1
      linarith
    · intro center r hr_ge hr_le
      have h_sub : (F_sel.carrier ∩ c2Ball center r) ⊆ (F_full.carrier ∩ c2Ball center r) := by
        intro x hx
        exact ⟨h_sel_sub hx.1, hx.2⟩
      have h_sub_sel : (F_sel.carrier ∩ c2Ball center r) ⊆ F_sel.carrier := Set.inter_subset_left
      have h_fin_sel : Set.Finite (F_sel.carrier ∩ c2Ball center r) :=
        Set.Finite.subset F_sel.finite h_sub_sel
      have h_sub_full : (F_full.carrier ∩ c2Ball center r) ⊆ F_full.carrier := Set.inter_subset_left
      have h_fin_full : Set.Finite (F_full.carrier ∩ c2Ball center r) :=
        Set.Finite.subset F_full.finite h_sub_full
      let S1 := h_fin_sel.toFinset
      let S2 := h_fin_full.toFinset
      have hS1 : (S1 : Set C2Function) = F_sel.carrier ∩ c2Ball center r :=
        Set.Finite.coe_toFinset h_fin_sel
      have hS2 : (S2 : Set C2Function) = F_full.carrier ∩ c2Ball center r :=
        Set.Finite.coe_toFinset h_fin_full
      have h_sub' : S1 ⊆ S2 := by
        intro x hx
        have h_x_in1 : x ∈ (S1 : Set C2Function) := by exact_mod_cast hx
        rw [hS1] at h_x_in1
        have h_x_in2 : x ∈ (F_full.carrier ∩ c2Ball center r) := h_sub h_x_in1
        have h_x_in_S2 : x ∈ (S2 : Set C2Function) := by
          rw [hS2]
          exact h_x_in2
        simpa using h_x_in_S2
      have h_card : S1.card ≤ S2.card := Finset.card_le_card h_sub'
      have h_ncard1 : (F_sel.carrier ∩ c2Ball center r).ncard = S1.card := by
        have h_eq : (F_sel.carrier ∩ c2Ball center r) = (S1 : Set C2Function) := hS1.symm
        rw [h_eq]
        simp
      have h_ncard2 : (F_full.carrier ∩ c2Ball center r).ncard = S2.card := by
        have h_eq : (F_full.carrier ∩ c2Ball center r) = (S2 : Set C2Function) := hS2.symm
        rw [h_eq]
        simp
      have h5 : (F_sel.carrier ∩ c2Ball center r).ncard ≤ (F_full.carrier ∩ c2Ball center r).ncard := by
        rw [h_ncard1, h_ncard2]; exact h_card
      have h4 : ((F_full.carrier ∩ c2Ball center r).ncard : ℝ) ≤ C_KT * (r / w) :=
        hKT_full.2 center r hr_ge hr_le
      have h6 : ((F_sel.carrier ∩ c2Ball center r).ncard : ℝ) ≤
          ((F_full.carrier ∩ c2Ball center r).ncard : ℝ) := by
        exact_mod_cast h5
      exact le_trans h6 h4
  have h_bound :=
    h_pyz_main w hw hw_le family h_cinematic h_jet_bound
      F_sel h_sel_family h_sel_sep h_sel_KT
  exact ⟨family, K, D, C_KT, hK1, hD1, hC_KT_ge1, h_cinematic,
    F_full, F_sel, h_mem_full, h_sel_sub, h_sel_sep, hKT_full, h_cover, h_bound⟩

end Kakeya.Assouad
