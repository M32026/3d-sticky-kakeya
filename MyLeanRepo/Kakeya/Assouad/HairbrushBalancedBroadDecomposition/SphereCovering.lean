import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MaxScoreTubesWitness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.ENNReal.Basic

/-!
# Sphere covering and cardinality lower bound

Three caps of radius 1 centered at the standard basis vectors cover the unit
sphere. Combined with the maximality property of the max-score witness, this
gives a lower bound on the retained cardinality.
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

section SphereCovering

variable {δ eta : ℝ}

/-- Standard basis vectors in Point3. -/
def stdBasis3 (i : Fin 3) : Point3 := EuclideanSpace.single i (1 : ℝ)

lemma stdBasis3_norm (i : Fin 3) : ‖stdBasis3 i‖ = 1 := by
  simp [stdBasis3, EuclideanSpace.norm_eq] <;> norm_num

lemma stdBasis3_inner (v : Point3) (i : Fin 3) :
    inner ℝ v (stdBasis3 i) = v i := by
  simp [stdBasis3, EuclideanSpace.inner_single_right] <;> ring

/-- Norm squared equals sum of coordinate squares. -/
private lemma norm_sq_eq_sum (v : Point3) : ‖v‖ ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
  have h : ‖v‖ = Real.sqrt (∑ i : Fin 3, ‖v i‖ ^ 2) := EuclideanSpace.norm_eq v
  rw [h]
  have h2 : ∑ i : Fin 3, ‖v i‖ ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h3 : ‖v i‖ = |v i| := Real.norm_eq_abs (v i)
    rw [h3]; simp [abs_pow]
  rw [h2]
  rw [Real.sq_sqrt] <;> positivity

/-- Coordinate bound: |v i| ≤ ‖v‖. -/
private lemma coord_le_norm (v : Point3) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  let f : Fin 3 → ℝ := fun j => v j ^ 2
  have h1 : f i ≤ ∑ j : Fin 3, f j :=
    Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : ‖v‖ ^ 2 = ∑ j : Fin 3, f j := norm_sq_eq_sum v
  have h3 : v i ^ 2 ≤ ‖v‖ ^ 2 := by simpa [f, h2] using h1
  have h4 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    have h5 : |v i| ^ 2 = v i ^ 2 := by simp [abs_pow]
    rw [h5]; exact h3
  have h6 : 0 ≤ ‖v‖ := by positivity
  nlinarith

/-- For any unit vector v, some coordinate has |v i| > cos 1. -/
private lemma some_coord_gt_cos1 (v : Point3) (hv : ‖v‖ = 1) :
    ∃ i : Fin 3, |v i| > Real.cos 1 := by
  have h_norm_sq : ‖v‖ ^ 2 = ∑ j : Fin 3, v j ^ 2 := norm_sq_eq_sum v
  have h_sum : ∑ j : Fin 3, v j ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    simp [Fin.sum_univ_succ] <;> ring
  have h1 : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    rw [←h_sum, ←h_norm_sq, hv] <;> norm_num
  have h_cos1_lt : Real.cos 1 < 1 / Real.sqrt 3 := by
    have h11 : Real.cos 1 ≤ 5 / 9 := Real.cos_one_le
    have h13 : 0 < 1 / Real.sqrt 3 := by positivity
    have h14 : (5 / 9 : ℝ) ^ 2 < (1 / Real.sqrt 3) ^ 2 := by
      have h15 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
        have h16 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
        field_simp [h16.ne'] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      nlinarith
    have h17 : (5 / 9 : ℝ) < 1 / Real.sqrt 3 := by nlinarith [h13]
    linarith
  set a := |v 0| with ha_def
  set b := |v 1| with hb_def
  set c := |v 2| with hc_def
  have ha_nonneg : 0 ≤ a := by positivity
  have hb_nonneg : 0 ≤ b := by positivity
  have hc_nonneg : 0 ≤ c := by positivity
  have h_sq_sum : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
    simp only [ha_def, hb_def, hc_def]
    have h_abs : ∀ i : Fin 3, |v i| ^ 2 = v i ^ 2 := by intro i; simp [abs_pow]
    rw [h_abs 0, h_abs 1, h_abs 2]; exact h1
  have h_inv_sq3 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
    have h16 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
    field_simp [h16.ne'] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h4 : max a (max b c) ≥ 1 / Real.sqrt 3 := by
    by_contra h5
    have h_lt : max a (max b c) < 1 / Real.sqrt 3 := by linarith
    have ha_lt : a < 1 / Real.sqrt 3 := (le_max_left a (max b c)).trans_lt h_lt
    have hbc_lt : max b c < 1 / Real.sqrt 3 := (le_max_right a (max b c)).trans_lt h_lt
    have hb_lt : b < 1 / Real.sqrt 3 := (le_max_left b c).trans_lt hbc_lt
    have hc_lt : c < 1 / Real.sqrt 3 := (le_max_right b c).trans_lt hbc_lt
    have ha2 : a ^ 2 < (1 / Real.sqrt 3) ^ 2 := by gcongr
    have hb2 : b ^ 2 < (1 / Real.sqrt 3) ^ 2 := by gcongr
    have hc2 : c ^ 2 < (1 / Real.sqrt 3) ^ 2 := by gcongr
    rw [h_inv_sq3] at ha2 hb2 hc2
    nlinarith
  have h_gt : max a (max b c) > Real.cos 1 := lt_of_lt_of_le h_cos1_lt h4
  have h5 : a > Real.cos 1 ∨ b > Real.cos 1 ∨ c > Real.cos 1 := by
    simpa [max_lt_iff] using h_gt
  rcases h5 with (h5 | h5 | h5)
  · exact ⟨0, by simpa [ha_def] using h5⟩
  · exact ⟨1, by simpa [hb_def] using h5⟩
  · exact ⟨2, by simpa [hc_def] using h5⟩

/-- Given |v i| > cos 1, prove the acute angle bound. -/
private lemma angle_bound_from_abs (v : Point3) (i : Fin 3) (hv : ‖v‖ = 1)
    (h_abs : |v i| > Real.cos 1) :
    hairbrushAcuteDirectionAngle v (stdBasis3 i) < 1 := by
  have h_inner : inner ℝ v (stdBasis3 i) = v i := stdBasis3_inner v i
  have h_coord : |v i| ≤ ‖v‖ := coord_le_norm v i
  have h_coord1 : |v i| ≤ 1 := by rw [hv] at h_coord; exact h_coord
  have h_bound1 : -1 ≤ v i := (abs_le.mp h_coord1).1
  have h_bound2 : v i ≤ 1 := (abs_le.mp h_coord1).2
  by_cases h_sign : 0 ≤ v i
  · -- v i ≥ 0
    have h9 : |v i| = v i := abs_of_nonneg h_sign
    have hvi_gt : Real.cos 1 < v i := by
      rw [h9] at h_abs; exact h_abs
    have h_cos1_bounds : -1 ≤ Real.cos 1 := by
      have h : -1 ≤ Real.cos 1 := Real.neg_one_le_cos 1
      exact h
    have h12 : Real.arccos (v i) < Real.arccos (Real.cos 1) :=
      Real.arccos_lt_arccos h_cos1_bounds hvi_gt h_bound2
    have h13 : Real.arccos (Real.cos 1) = 1 :=
      Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])
    have h14 : Real.arccos (v i) < 1 := by
      rw [h13] at h12; exact h12
    have h15 : hairbrushAcuteDirectionAngle v (stdBasis3 i) ≤ Real.arccos (inner ℝ v (stdBasis3 i)) := by
      simp [hairbrushAcuteDirectionAngle, h_inner] <;> exact min_le_left _ _
    rw [h_inner] at h15
    exact h15.trans_lt h14
  · -- v i < 0
    have hvi_neg : v i < 0 := by linarith
    have h9 : |v i| = -v i := abs_of_neg hvi_neg
    have hvi_lt : v i < -Real.cos 1 := by
      rw [h9] at h_abs; linarith
    have h_cos1_ge_neg1 : -1 ≤ Real.cos 1 := Real.neg_one_le_cos 1
    have h_neg_cos1_le_one : -Real.cos 1 ≤ 1 := by linarith
    have h12 : Real.arccos (-(Real.cos 1)) < Real.arccos (v i) :=
      Real.arccos_lt_arccos h_bound1 hvi_lt h_neg_cos1_le_one
    have h13 : Real.arccos (-(Real.cos 1)) = Real.pi - Real.arccos (Real.cos 1) := by
      rw [Real.arccos_neg] <;> linarith
    have h14 : Real.arccos (Real.cos 1) = 1 :=
      Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])
    have h15 : Real.pi - 1 < Real.arccos (v i) := by
      rw [h13, h14] at h12; exact h12
    have h16 : Real.pi - Real.arccos (v i) < 1 := by linarith
    have h17 : hairbrushAcuteDirectionAngle v (stdBasis3 i) ≤ Real.pi - Real.arccos (inner ℝ v (stdBasis3 i)) := by
      simp [hairbrushAcuteDirectionAngle, h_inner] <;> exact min_le_right _ _
    rw [h_inner] at h17
    exact h17.trans_lt h16

/-- For any unit vector v, some standard basis vector is within acute angle 1. -/
lemma sphere_covered_by_three_caps (v : Point3) (hv : ‖v‖ = 1) :
    ∃ i : Fin 3, hairbrushAcuteDirectionAngle v (stdBasis3 i) < 1 := by
  rcases some_coord_gt_cos1 v hv with ⟨i, h_i⟩
  exact ⟨i, angle_bound_from_abs v i hv h_i⟩

/-- Cardinality lower bound from the max-score witness.
    The three caps of radius 1 cover the sphere, so the original family
    is contained in the union of three caps, each of size ≤ (1/r)^η * W.card.
    Hence W.card ≥ (1/3) * r^η * through.card. -/
lemma witness_cardinality_bound
    (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta)
    {through : Finset (Kakeya.DeltaTube δ)} (hthrough : through.Nonempty)
    (w : Point3) (r : ℝ) (W : Finset (Kakeya.DeltaTube δ))
    (hw_norm : ‖w‖ = 1) (hrδ : δ ≤ r) (hr1 : r ≤ 1)
    (hW_eq : W = through.filter (fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r))
    (h_max : ∀ (v' : Point3), ‖v'‖ = 1 → ∀ r' : ℝ, δ ≤ r' → r' ≤ 1 →
      ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
      Real.rpow (r' / r) eta * (W.card : ℝ)) :
    (W.card : ℝ) ≥ (1 / 3 : ℝ) * Real.rpow r eta * (through.card : ℝ) := by
  have hr_pos : 0 < r := by linarith [hδ]
  let cap (i : Fin 3) : Finset (Kakeya.DeltaTube δ) :=
    through.filter (fun T => hairbrushAcuteDirectionAngle T.direction (stdBasis3 i) ≤ 1)
  let U12 := cap 1 ∪ cap 2
  let U := cap 0 ∪ U12
  have h_cover : through ⊆ U := by
    intro T hT
    have h_dir_unit : ‖T.direction‖ = 1 := T.direction_unit
    rcases sphere_covered_by_three_caps T.direction h_dir_unit with ⟨i, h_i⟩
    have h_i_le : hairbrushAcuteDirectionAngle T.direction (stdBasis3 i) ≤ 1 := by linarith
    have hT_in_cap : T ∈ cap i := by
      simp only [cap, Finset.mem_filter]
      exact ⟨hT, h_i_le⟩
    have hT_in_U : T ∈ U := by
      simp only [U, U12, Finset.mem_union]
      fin_cases i <;> tauto
    exact hT_in_U
  have h_card_cover : through.card ≤ U.card := Finset.card_le_card h_cover
  have h_union_card : U.card ≤ (cap 0).card + (cap 1).card + (cap 2).card := by
    have h1 : U.card ≤ (cap 0).card + U12.card := Finset.card_union_le (cap 0) U12
    have h2 : U12.card ≤ (cap 1).card + (cap 2).card := Finset.card_union_le (cap 1) (cap 2)
    dsimp only [U, U12] at h1 h2
    linarith
  have h_each : ∀ i : Fin 3, ((cap i).card : ℝ) ≤ Real.rpow (1 / r) eta * (W.card : ℝ) := by
    intro i
    have h1 : ‖stdBasis3 i‖ = 1 := stdBasis3_norm i
    have h2 : δ ≤ (1 : ℝ) := by linarith
    exact h_max (stdBasis3 i) h1 (1 : ℝ) h2 (by norm_num)
  have h3 : ((cap 0).card : ℝ) + ((cap 1).card : ℝ) + ((cap 2).card : ℝ) ≤
      3 * (Real.rpow (1 / r) eta * (W.card : ℝ)) := by
    have h4 := h_each 0
    have h5 := h_each 1
    have h6 := h_each 2
    linarith
  have h7 : (through.card : ℝ) ≤ 3 * (Real.rpow (1 / r) eta * (W.card : ℝ)) := by
    have h8 : (through.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast h_card_cover
    have h9 : (U.card : ℝ) ≤ ((cap 0).card : ℝ) + ((cap 1).card : ℝ) + ((cap 2).card : ℝ) := by
      exact_mod_cast h_union_card
    linarith
  have h10 : Real.rpow (1 / r) eta = 1 / Real.rpow r eta := by
    have h11 : Real.rpow (1 / r) eta = Real.rpow 1 eta / Real.rpow r eta :=
      Real.div_rpow (by norm_num) (by linarith) eta
    rw [h11]
    have h12 : Real.rpow 1 eta = 1 := by simp
    rw [h12] <;> ring
  rw [h10] at h7
  have h11 : 0 < Real.rpow r eta := Real.rpow_pos_of_pos hr_pos _
  have h12 : (through.card : ℝ) ≤ 3 * ((1 / Real.rpow r eta) * (W.card : ℝ)) := h7
  have h13 : (1 / Real.rpow r eta) * (W.card : ℝ) ≥ (1 / 3 : ℝ) * (through.card : ℝ) := by linarith
  have h14 : (W.card : ℝ) ≥ (1 / 3 : ℝ) * Real.rpow r eta * (through.card : ℝ) := by
    have h15 : (W.card : ℝ) = (Real.rpow r eta) * ((1 / Real.rpow r eta) * (W.card : ℝ)) := by
      have h16 : (Real.rpow r eta) * ((1 / Real.rpow r eta) * (W.card : ℝ)) = (W.card : ℝ) := by
        field_simp [h11.ne'] <;> ring
      exact h16.symm
    rw [h15]
    have h17 : (Real.rpow r eta) * ((1 / Real.rpow r eta) * (W.card : ℝ)) ≥
        (Real.rpow r eta) * ((1 / 3 : ℝ) * (through.card : ℝ)) := by
      gcongr <;> linarith
    have h18 : (Real.rpow r eta) * ((1 / 3 : ℝ) * (through.card : ℝ)) =
        (1 / 3 : ℝ) * Real.rpow r eta * (through.card : ℝ) := by ring
    rw [h18] at h17
    exact h17
  exact h14

/-- ENNReal version of the cardinality bound. -/
lemma witness_cardinality_bound_ENNReal
    (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta)
    {through : Finset (Kakeya.DeltaTube δ)} (hthrough : through.Nonempty)
    (w : Point3) (r : ℝ) (W : Finset (Kakeya.DeltaTube δ))
    (hw_norm : ‖w‖ = 1) (hrδ : δ ≤ r) (hr1 : r ≤ 1)
    (hW_eq : W = through.filter (fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r))
    (h_max : ∀ (v' : Point3), ‖v'‖ = 1 → ∀ r' : ℝ, δ ≤ r' → r' ≤ 1 →
      ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
      Real.rpow (r' / r) eta * (W.card : ℝ)) :
    (W.card : ENNReal) ≥ (1 / 3 : ENNReal) * ENNReal.ofReal (Real.rpow r eta) * (through.card : ENNReal) := by
  have h_real := witness_cardinality_bound hδ hδ_le1 heta hthrough w r W hw_norm hrδ hr1 hW_eq h_max
  have hr_pos : 0 < r := by linarith [hδ]
  have h_rpow_pos : 0 < Real.rpow r eta := Real.rpow_pos_of_pos hr_pos eta
  have h_rpow_nonneg : 0 ≤ Real.rpow r eta := h_rpow_pos.le
  set x : ℝ := (1 / 3 : ℝ) * Real.rpow r eta * (through.card : ℝ) with hx_def
  have hx_nonneg : 0 ≤ x := by positivity
  have h_enn : ENNReal.ofReal (W.card : ℝ) ≥ ENNReal.ofReal x :=
    ENNReal.ofReal_le_ofReal h_real
  have h_card_eq : ENNReal.ofReal (W.card : ℝ) = (W.card : ENNReal) := by simp
  have h_through_nonneg : 0 ≤ (through.card : ℝ) := by positivity
  have h_third_nonneg : 0 ≤ (1 / 3 : ℝ) := by norm_num
  have h_ab_nonneg : 0 ≤ (1 / 3 : ℝ) * Real.rpow r eta := by positivity
  have h_mul1 : ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r eta) =
      ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (Real.rpow r eta) :=
    ENNReal.ofReal_mul h_third_nonneg
  have h_mul2 : ENNReal.ofReal x =
      ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r eta) * ENNReal.ofReal (through.card : ℝ) := by
    rw [hx_def]
    exact ENNReal.ofReal_mul h_ab_nonneg
  have h_third_eq : ENNReal.ofReal (1 / 3 : ℝ) = (1 / 3 : ENNReal) := by
    norm_cast <;> simp
  have h_through_eq : ENNReal.ofReal (through.card : ℝ) = (through.card : ENNReal) := by simp
  have h_final : ENNReal.ofReal x =
      (1 / 3 : ENNReal) * ENNReal.ofReal (Real.rpow r eta) * (through.card : ENNReal) := by
    calc ENNReal.ofReal x
      = ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r eta) * ENNReal.ofReal (through.card : ℝ) := h_mul2
    _ = (ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (Real.rpow r eta)) * ENNReal.ofReal (through.card : ℝ) := by rw [h_mul1]
    _ = (1 / 3 : ENNReal) * ENNReal.ofReal (Real.rpow r eta) * (through.card : ENNReal) := by
      rw [h_third_eq, h_through_eq] <;> ring
  rw [h_card_eq] at h_enn
  rw [h_final] at h_enn
  exact h_enn

end SphereCovering

end Kakeya.Assouad
