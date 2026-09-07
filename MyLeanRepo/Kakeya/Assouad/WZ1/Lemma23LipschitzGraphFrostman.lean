import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Frostman control for the Lipschitz graphs in WZ1 Lemma 23

The two vertex classes used in the projection theorem are bounded linear
images of graphs of one-Lipschitz functions.  This file isolates the finite
counting fact needed after their cardinalities have been established.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
A nonempty separated finite subset of a real interval has the expected
packing bound.
-/
lemma lemma23_separated_real_finset_card_le
    {S : Finset ℝ} {a b d : ℝ} (hd : 0 < d)
    (hne : S.Nonempty)
    (h1 : ∀ x ∈ S, a ≤ x ∧ x ≤ b)
    (h2 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|) :
    (S.card : ℝ) ≤ (b - a) / d + 1 := by
  have h_ab : a ≤ b := by
    rcases hne with ⟨x, hx⟩
    exact (h1 x hx).1.trans (h1 x hx).2
  have h_ba_nonneg : 0 ≤ (b - a) / d := by positivity
  classical
  let f : ℝ → ℕ := fun x => Nat.floor ((x - a) / d)
  have h_nonneg : ∀ x ∈ S, 0 ≤ (x - a) / d := by
    intro x hx
    have hxa : a ≤ x := (h1 x hx).1
    positivity
  have h_inj : Set.InjOn f S := by
    intro x hx y hy h_eq
    by_cases hxy : x ≠ y
    · have h_sep : d ≤ |x - y| := h2 x hx y hy hxy
      have h_fy : f y = f x := h_eq.symm
      have h1x : (f x : ℝ) ≤ (x - a) / d :=
        Nat.floor_le (h_nonneg x hx)
      have h2x : (x - a) / d < (f x : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h1y : (f x : ℝ) ≤ (y - a) / d := by
        rw [← h_fy]
        exact Nat.floor_le (h_nonneg y hy)
      have h2y : (y - a) / d < (f x : ℝ) + 1 := by
        rw [← h_fy]
        exact Nat.lt_floor_add_one _
      have h3 : |(x - a) / d - (y - a) / d| < 1 := by
        rw [abs_sub_lt_iff]
        constructor <;> linarith
      have h4 : |x - y| / d < 1 := by
        have h5 :
            (x - a) / d - (y - a) / d = (x - y) / d := by
          field_simp [hd.ne']
          ring
        rw [h5, abs_div, abs_of_pos hd] at h3
        exact h3
      have h7 : |x - y| < d := by
        calc
          |x - y| = |x - y| / d * d := by
            field_simp [hd.ne']
          _ < 1 * d := by gcongr
          _ = d := by ring
      linarith
    · exact Classical.not_not.mp hxy
  have h_bound :
      ∀ x ∈ S, f x ≤ Nat.floor ((b - a) / d) := by
    intro x hx
    have hxb : x ≤ b := (h1 x hx).2
    exact Nat.floor_mono (by gcongr)
  let S' := S.image f
  have h_card_img : S'.card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_sub :
      S' ⊆ Finset.range (Nat.floor ((b - a) / d) + 1) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have hx_bound :
        f x ≤ Nat.floor ((b - a) / d) := h_bound x hx
    simp only [Finset.mem_range]
    omega
  have h_card_le :
      S'.card ≤ Nat.floor ((b - a) / d) + 1 := by
    simpa using Finset.card_le_card h_sub
  have h9 :
      (S.card : ℝ) ≤
        (Nat.floor ((b - a) / d) + 1 : ℝ) := by
    rw [← h_card_img]
    exact_mod_cast h_card_le
  have h10 :
      (Nat.floor ((b - a) / d) : ℝ) ≤ (b - a) / d :=
    Nat.floor_le h_ba_nonneg
  calc
    (S.card : ℝ)
        ≤ (Nat.floor ((b - a) / d) + 1 : ℝ) := h9
    _ = (Nat.floor ((b - a) / d) : ℝ) + 1 := by simp
    _ ≤ (b - a) / d + 1 := by gcongr

/--
For two separated points on a one-Lipschitz graph, their first coordinates
are separated up to the absolute factor `sqrt 2`.
-/
lemma lemma23_graph_xcoord_sep
    {delta : ℝ} (hdelta_pos : 0 < delta)
    {p q : Point2} (f : ℝ → ℝ)
    (hf : LipschitzOnWith 1 f Set.univ)
    (hp_graph : p 1 = f (p 0))
    (hq_graph : q 1 = f (q 0))
    (h_sep : delta ≤ dist p q) :
    delta / Real.sqrt 2 ≤ |p 0 - q 0| := by
  have h_lip : |f (p 0) - f (q 0)| ≤ |p 0 - q 0| := by
    have h :=
      hf.dist_le_mul (p 0) (by simp) (q 0) (by simp)
    simpa [Real.dist_eq] using h
  have h1 : p 1 - q 1 = f (p 0) - f (q 0) := by
    rw [hp_graph, hq_graph]
  have h2 : |p 1 - q 1| ≤ |p 0 - q 0| := by
    rw [h1]
    exact h_lip
  let v : Point2 := p - q
  have h_sum_nonneg : 0 ≤ v 0 ^ 2 + v 1 ^ 2 := by positivity
  have h3 : dist p q ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    have h4 : dist p q = ‖v‖ := by rfl
    rw [h4]
    have h5 : ‖v‖ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [h5, Real.sq_sqrt h_sum_nonneg]
  have h4 : dist p q ^ 2 ≤ 2 * (p 0 - q 0) ^ 2 := by
    rw [h3]
    have h5 : v 1 = p 1 - q 1 := by rfl
    have h6 : v 0 = p 0 - q 0 := by rfl
    rw [h5, h6]
    have h7 : (p 1 - q 1) ^ 2 ≤ (p 0 - q 0) ^ 2 :=
      sq_le_sq.mpr h2
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num)
  by_contra h
  have h6 : |p 0 - q 0| < delta / Real.sqrt 2 := by
    linarith
  have h7 : (p 0 - q 0) ^ 2 < delta ^ 2 / 2 := by
    have h8 :
        |p 0 - q 0| ^ 2 < (delta / Real.sqrt 2) ^ 2 := by
      gcongr
    rw [sq_abs] at h8
    have h10 :
        (delta / Real.sqrt 2) ^ 2 = delta ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
    rw [h10] at h8
    exact h8
  have h11 : delta ^ 2 ≤ dist p q ^ 2 := by
    nlinarith
  nlinarith

/--
A sufficiently large separated subset of a one-Lipschitz graph satisfies the
normalized one-dimensional Frostman condition.

The cardinality hypothesis is the non-vacuity input.  It is proved from the
popular-height and local-grain counts in the geometric part of Lemma 23.
-/
lemma lemma23_lipschitz_graph_frostman
    {delta eta : ℝ} (hdelta_pos : 0 < delta)
    {A : DiscreteSet 2}
    (f : ℝ → ℝ) (hf : LipschitzOnWith 1 f Set.univ)
    (hA_graph : ∀ p ∈ A, p 1 = f (p 0))
    (h_sep : A.IsDeltaSeparated delta)
    (h_card : (A.card : ℝ) ≥ 4 * Real.rpow delta (eta - 1)) :
    A.IsFrostman delta 1 (Kakeya.realRpowENN delta (-eta)) := by
  intro x r hr_ge_delta hr_le_one
  let B : Finset Point2 := A.filter fun y => dist y x ≤ r
  have hB_sub : B ⊆ A := Finset.filter_subset _ _
  have hr_nonneg : 0 ≤ r := by linarith
  by_cases hB_empty : B = ∅
  · simp [DiscreteSet.ballCount, B, hB_empty]
  · have hB_nonempty : B.Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty] using hB_empty
    have h_xcoord_range :
        ∀ p ∈ B, x 0 - r ≤ p 0 ∧ p 0 ≤ x 0 + r := by
      intro p hp
      have h_dist : dist p x ≤ r := (Finset.mem_filter.mp hp).2
      let v := p - x
      have h_sum_nonneg : 0 ≤ ∑ i : Fin 2, v i ^ 2 := by
        positivity
      have h1 : ‖v‖ ^ 2 = ∑ i : Fin 2, v i ^ 2 := by
        have h21 :
            ‖v‖ = Real.sqrt (∑ i : Fin 2, ‖v i‖ ^ 2) := by
          rw [EuclideanSpace.norm_eq]
        have h22 :
            (∑ i : Fin 2, ‖v i‖ ^ 2) =
              ∑ i : Fin 2, v i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp
        rw [h21, h22, Real.sq_sqrt h_sum_nonneg]
      have h2 : |v 0| ^ 2 ≤ ‖v‖ ^ 2 := by
        rw [h1, sq_abs]
        rw [Fin.sum_univ_two]
        exact le_add_of_nonneg_right (by positivity)
      have h6 : |v 0| ≤ ‖v‖ := by
        nlinarith [abs_nonneg (v 0), norm_nonneg v]
      have hv0 : v 0 = p 0 - x 0 := by rfl
      have h7 : |p 0 - x 0| ≤ dist p x := by
        simpa [dist_eq_norm, ← hv0] using h6
      have h9 : |p 0 - x 0| ≤ r := h7.trans h_dist
      exact ⟨by linarith [abs_le.mp h9], by linarith [abs_le.mp h9]⟩
    have h_xcoord_sep :
        ∀ p ∈ B, ∀ q ∈ B, p ≠ q →
          delta / Real.sqrt 2 ≤ |p 0 - q 0| := by
      intro p hp q hq hpq
      have hpA : p ∈ A := hB_sub hp
      have hqA : q ∈ A := hB_sub hq
      exact
        lemma23_graph_xcoord_sep hdelta_pos f hf
          (hA_graph p hpA) (hA_graph q hqA)
          (h_sep hpA hqA hpq)
    let projection : Point2 → ℝ := fun p => p 0
    let S : Finset ℝ := B.image projection
    have hS_nonempty : S.Nonempty := hB_nonempty.image projection
    have hS_in :
        ∀ y ∈ S, x 0 - r ≤ y ∧ y ≤ x 0 + r := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
      exact h_xcoord_range p hp
    have hS_sep :
        ∀ y₁ ∈ S, ∀ y₂ ∈ S, y₁ ≠ y₂ →
          delta / Real.sqrt 2 ≤ |y₁ - y₂| := by
      intro y₁ hy₁ y₂ hy₂ hy
      rcases Finset.mem_image.mp hy₁ with ⟨p₁, hp₁, rfl⟩
      rcases Finset.mem_image.mp hy₂ with ⟨p₂, hp₂, rfl⟩
      have hp : p₁ ≠ p₂ := by
        intro h
        apply hy
        rw [h]
      exact h_xcoord_sep p₁ hp₁ p₂ hp₂ hp
    have hd_pos : 0 < delta / Real.sqrt 2 := by positivity
    have h_card_S :
        (S.card : ℝ) ≤ 2 * r / (delta / Real.sqrt 2) + 1 := by
      have h :=
        lemma23_separated_real_finset_card_le
          hd_pos hS_nonempty hS_in hS_sep
      convert h using 1 <;> ring
    have h_projection_inj : Set.InjOn projection B := by
      intro p hp q hq h_eq
      by_contra hpq
      have hsep := h_xcoord_sep p hp q hq hpq
      have : |p 0 - q 0| = 0 := by
        change p 0 = q 0 at h_eq
        rw [h_eq]
        simp
      rw [this] at hsep
      linarith
    have h_card_B : B.card = S.card := by
      rw [Finset.card_image_of_injOn h_projection_inj]
    have h_card_bound : (B.card : ℝ) ≤ 4 * r / delta := by
      rw [h_card_B]
      have h9 :
          (S.card : ℝ) ≤ 2 * Real.sqrt 2 * r / delta + 1 := by
        have hsqrt_pos : 0 < Real.sqrt 2 :=
          Real.sqrt_pos.mpr (by norm_num)
        have h10 :
            2 * r / (delta / Real.sqrt 2) =
              2 * Real.sqrt 2 * r / delta := by
          field_simp [hdelta_pos.ne', hsqrt_pos.ne']
        rw [h10] at h_card_S
        exact h_card_S
      have h12 : 1 ≤ r / delta := by
        calc
          1 = delta / delta := by field_simp [hdelta_pos.ne']
          _ ≤ r / delta := by gcongr
      have h13 : 2 * Real.sqrt 2 ≤ 3 := by
        nlinarith [Real.sqrt_nonneg 2,
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      calc
        (S.card : ℝ) ≤ 2 * Real.sqrt 2 * r / delta + 1 := h9
        _ ≤ 3 * r / delta + r / delta := by
          gcongr
        _ = 4 * r / delta := by ring
    have h_rpow1 :
        Real.rpow delta (-eta) * Real.rpow delta (eta - 1) =
          Real.rpow delta (-1) := by
      have h :
          Real.rpow delta ((-eta) + (eta - 1)) =
            Real.rpow delta (-eta) * Real.rpow delta (eta - 1) :=
        Real.rpow_add hdelta_pos (-eta) (eta - 1)
      have h2 : (-eta) + (eta - 1) = -1 := by ring
      rw [h2] at h
      exact h.symm
    have h_rpow2 : Real.rpow delta (-1) = 1 / delta := by
      have hneg :
          Real.rpow delta (-1) = (Real.rpow delta 1)⁻¹ :=
        Real.rpow_neg hdelta_pos.le 1
      rw [hneg]
      have h1 : Real.rpow delta 1 = delta := by simp
      rw [h1]
      field_simp [hdelta_pos.ne']
    have h_frostman_real :
        (B.card : ℝ) ≤
          Real.rpow delta (-eta) * r * (A.card : ℝ) := by
      have h16 :
          Real.rpow delta (-eta) * r *
                (4 * Real.rpow delta (eta - 1)) ≤
            Real.rpow delta (-eta) * r * (A.card : ℝ) := by
        exact
          mul_le_mul_of_nonneg_left h_card
            (mul_nonneg
              (Real.rpow_nonneg hdelta_pos.le _) hr_nonneg)
      have h17 :
          Real.rpow delta (-eta) * r *
              (4 * Real.rpow delta (eta - 1)) =
            4 * r / delta := by
        calc
          Real.rpow delta (-eta) * r *
                (4 * Real.rpow delta (eta - 1))
              = r * (Real.rpow delta (-eta) *
                  (4 * Real.rpow delta (eta - 1))) := by ring
          _ = r * (4 / delta) := by
            rw [show
              Real.rpow delta (-eta) *
                    (4 * Real.rpow delta (eta - 1)) =
                  4 / delta by
                calc
                  Real.rpow delta (-eta) *
                        (4 * Real.rpow delta (eta - 1))
                      = 4 * (Real.rpow delta (-eta) *
                          Real.rpow delta (eta - 1)) := by ring
                  _ = 4 * Real.rpow delta (-1) := by rw [h_rpow1]
                  _ = 4 * (1 / delta) := by rw [h_rpow2]
                  _ = 4 / delta := by ring]
          _ = 4 * r / delta := by ring
      exact h_card_bound.trans (h17 ▸ h16)
    have h_rpow_nonneg : 0 ≤ Real.rpow delta (-eta) :=
      Real.rpow_nonneg (le_of_lt hdelta_pos) _
    have h1 : Kakeya.realRpowENN r 1 = ENNReal.ofReal r := by
      simp [Kakeya.realRpowENN]
    have h2 : A.enncard = ENNReal.ofReal (A.card : ℝ) := by
      simp [DiscreteSet.enncard]
    have h3 :
        Kakeya.realRpowENN delta (-eta) * ENNReal.ofReal r *
              ENNReal.ofReal (A.card : ℝ) =
          ENNReal.ofReal
            (Real.rpow delta (-eta) * r * (A.card : ℝ)) := by
      rw [Kakeya.realRpowENN]
      have h31 :
          ENNReal.ofReal (Real.rpow delta (-eta)) *
                ENNReal.ofReal r =
              ENNReal.ofReal (Real.rpow delta (-eta) * r) := by
        rw [← ENNReal.ofReal_mul h_rpow_nonneg]
      rw [h31]
      have h32 :
          ENNReal.ofReal (Real.rpow delta (-eta) * r) *
                ENNReal.ofReal (A.card : ℝ) =
              ENNReal.ofReal
                ((Real.rpow delta (-eta) * r) * (A.card : ℝ)) := by
        rw [← ENNReal.ofReal_mul
          (show 0 ≤ Real.rpow delta (-eta) * r by positivity)]
      rw [h32]
    have hB_card_eq :
        (B.card : ENNReal) = ENNReal.ofReal (B.card : ℝ) := by
      norm_cast
    have h4 :
        (B.card : ENNReal) ≤
          Kakeya.realRpowENN delta (-eta) *
            Kakeya.realRpowENN r 1 * A.enncard := by
      rw [hB_card_eq, h1, h2, h3]
      exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr
        h_frostman_real
    simpa [DiscreteSet.ballCount, B] using h4

end Kakeya.Assouad
