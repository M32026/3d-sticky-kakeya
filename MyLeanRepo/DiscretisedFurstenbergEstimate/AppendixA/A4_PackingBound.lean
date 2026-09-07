module

/-
  A4 helper: Packing bound for separated sets in EuclideanPlane.

  Proves that a finite ε-separated set in a ball of radius 2ε has at most 81 points,
  then derives: externalCoveringNumber(ε, P) ≥ |P| / 81.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4Plane
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical

namespace DirecretisedFurstenbergEstimate.AppendixA4

/-- Any finite ε-separated subset of a ball of radius 2ε in EuclideanPlane
    has at most 81 points. -/
lemma ball_separated_card_le81
    {P : Finset Plane} {ε : ℝ} (hε_pos : 0 < ε)
    (hsep : (P : Set Plane).Pairwise fun x y => ε ≤ dist x y)
    (c : Plane) :
    (P.filter (fun p => p ∈ Metric.closedBall c (2 * ε))).card ≤ 81 := by
  classical
  let cell : Plane → ℤ × ℤ := fun p =>
    (⌊(p 0 - c 0) / (ε / 2)⌋, ⌊(p 1 - c 1) / (ε / 2)⌋)
  have hε2_pos : 0 < ε / 2 := by linarith
  let Q := P.filter (fun p => p ∈ Metric.closedBall c (2 * ε))
  have hQ_mem : ∀ p ∈ Q, p ∈ P ∧ p ∈ Metric.closedBall c (2 * ε) := by
    intro p hp; simp only [Q, Finset.mem_filter] at hp; exact ⟨hp.1, hp.2⟩
  have h_coord : ∀ (v : Plane) (i : Fin 2), |v i| ≤ ‖v‖ := by
    intro v i
    have h1 : (v i)^2 ≤ ‖v‖^2 := by
      have h2 : ‖v‖^2 = ∑ j : Fin 2, (v j)^2 := by
        rw [EuclideanSpace.real_norm_sq_eq] <;> rfl
      rw [h2]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have h4 : 0 ≤ |v i| := by positivity
    have h5 : 0 ≤ ‖v‖ := by positivity
    nlinarith [sq_abs (v i), sq_abs ‖v‖]
  have h_inj : Set.InjOn cell (Q : Set Plane) := by
    intro p hp q hq hcell
    by_contra hne
    have h_pball : p ∈ Metric.closedBall c (2 * ε) := (hQ_mem p hp).2
    have h_qball : q ∈ Metric.closedBall c (2 * ε) := (hQ_mem q hq).2
    have h1 : |p 0 - c 0| ≤ 2 * ε := by
      have hnorm : ‖p - c‖ ≤ 2 * ε := h_pball
      have h : |(p - c) 0| ≤ ‖p - c‖ := h_coord (p - c) 0
      simpa using h.trans hnorm
    have h2 : |p 1 - c 1| ≤ 2 * ε := by
      have hnorm : ‖p - c‖ ≤ 2 * ε := h_pball
      have h : |(p - c) 1| ≤ ‖p - c‖ := h_coord (p - c) 1
      simpa using h.trans hnorm
    have hfa1 : ⌊(p 0 - c 0) / (ε / 2)⌋ = ⌊(q 0 - c 0) / (ε / 2)⌋ :=
      congr_arg Prod.fst hcell
    have hfa2 : ⌊(p 1 - c 1) / (ε / 2)⌋ = ⌊(q 1 - c 1) / (ε / 2)⌋ :=
      congr_arg Prod.snd hcell
    have hdx1 : |(p 0 - c 0) / (ε / 2) - (q 0 - c 0) / (ε / 2)| < 1 := by exact Int.abs_sub_lt_one_of_floor_eq_floor hfa1
    have hdx2 : |(p 1 - c 1) / (ε / 2) - (q 1 - c 1) / (ε / 2)| < 1 := by exact Int.abs_sub_lt_one_of_floor_eq_floor hfa2
    have hdx : |p 0 - q 0| < ε / 2 := by
      have h_eq : (p 0 - c 0) / (ε / 2) - (q 0 - c 0) / (ε / 2) = (p 0 - q 0) / (ε / 2) := by
        ring
      rw [h_eq] at hdx1
      have h : |(p 0 - q 0) / (ε / 2)| = |p 0 - q 0| / (ε / 2) := by
        rw [abs_div] <;> rw [abs_of_pos hε2_pos]
      rw [h] at hdx1
      have h' : |p 0 - q 0| / (ε / 2) < 1 := hdx1
      have h'' : |p 0 - q 0| < ε / 2 := by
        calc |p 0 - q 0|
          = |p 0 - q 0| / (ε / 2) * (ε / 2) := by field_simp [hε2_pos.ne'] <;> ring
        _ < 1 * (ε / 2) := by gcongr
        _ = ε / 2 := by ring
      exact h''
    have hdy : |p 1 - q 1| < ε / 2 := by
      have h_eq : (p 1 - c 1) / (ε / 2) - (q 1 - c 1) / (ε / 2) = (p 1 - q 1) / (ε / 2) := by ring
      rw [h_eq] at hdx2
      have h : |(p 1 - q 1) / (ε / 2)| = |p 1 - q 1| / (ε / 2) := by
        rw [abs_div] <;> rw [abs_of_pos hε2_pos]
      rw [h] at hdx2
      have h' : |p 1 - q 1| / (ε / 2) < 1 := hdx2
      have h'' : |p 1 - q 1| < ε / 2 := by
        calc |p 1 - q 1|
          = |p 1 - q 1| / (ε / 2) * (ε / 2) := by field_simp [hε2_pos.ne'] <;> ring
        _ < 1 * (ε / 2) := by gcongr
        _ = ε / 2 := by ring
      exact h''
    have h_dist : dist p q < ε := by
      have hdx_sq : (p 0 - q 0)^2 < (ε / 2)^2 := by
        have h : |p 0 - q 0| < ε / 2 := hdx
        have h_nonneg1 : 0 ≤ |p 0 - q 0| := by positivity
        have h_pos2 : 0 < ε / 2 := hε2_pos
        have h' : |p 0 - q 0|^2 < (ε / 2)^2 := by
          gcongr
        have h'' : (p 0 - q 0)^2 = |p 0 - q 0|^2 := by simp [sq_abs]
        rw [h'']
        exact h'
      have hdy_sq : (p 1 - q 1)^2 < (ε / 2)^2 := by
        have h : |p 1 - q 1| < ε / 2 := hdy
        have h_nonneg1 : 0 ≤ |p 1 - q 1| := by positivity
        have h_pos2 : 0 < ε / 2 := hε2_pos
        have h' : |p 1 - q 1|^2 < (ε / 2)^2 := by gcongr
        have h'' : (p 1 - q 1)^2 = |p 1 - q 1|^2 := by simp [sq_abs]
        rw [h'']
        exact h'
      have h1 : (p 0 - q 0)^2 + (p 1 - q 1)^2 < ε^2 := by
        calc (p 0 - q 0)^2 + (p 1 - q 1)^2
          < (ε / 2)^2 + (ε / 2)^2 := by linarith
        _ = ε^2 / 2 := by ring
        _ < ε^2 := by nlinarith
      have h2 : ‖p - q‖ = Real.sqrt ((p 0 - q 0)^2 + (p 1 - q 1)^2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> rfl
      rw [dist_eq_norm, h2]
      rw [Real.sqrt_lt] <;> nlinarith
    have h_pP : p ∈ P := (hQ_mem p hp).1
    have h_qP : q ∈ P := (hQ_mem q hq).1
    have h_sep' : ε ≤ dist p q := hsep h_pP h_qP hne
    linarith
  let S : Finset (ℤ × ℤ) := Finset.Icc (-4) 4 ×ˢ Finset.Icc (-4) 4
  have hS_card : S.card = 81 := by
    simp [S, Finset.card_product] <;> decide
  have h_sub : Q.image cell ⊆ S := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    have h_pball : p ∈ Metric.closedBall c (2 * ε) := (hQ_mem p hp).2
    have h1 : |p 0 - c 0| ≤ 2 * ε := by
      have hnorm : ‖p - c‖ ≤ 2 * ε := h_pball
      have h : |(p - c) 0| ≤ ‖p - c‖ := h_coord (p - c) 0
      simpa using h.trans hnorm
    have h2 : |p 1 - c 1| ≤ 2 * ε := by
      have hnorm : ‖p - c‖ ≤ 2 * ε := h_pball
      have h : |(p - c) 1| ≤ ‖p - c‖ := h_coord (p - c) 1
      simpa using h.trans hnorm
    have h3 : -4 ≤ (cell p).1 := by
      have h4 : (-4 : ℝ) ≤ (p 0 - c 0) / (ε / 2) := by
        have h5 : -2 * ε ≤ p 0 - c 0 := by linarith [abs_le.mp h1]
        have h6 : (-2 * ε) / (ε / 2) ≤ (p 0 - c 0) / (ε / 2) := by gcongr
        have h7 : (-2 * ε) / (ε / 2) = -4 := by field_simp [hε2_pos.ne'] <;> ring
        linarith
      have h_iff : (-4 : ℤ) ≤ ⌊(p 0 - c 0) / (ε / 2)⌋ ↔ ((-4 : ℤ) : ℝ) ≤ (p 0 - c 0) / (ε / 2) := Int.le_floor
      exact h_iff.mpr (by norm_num <;> exact h4)
    have h4 : (cell p).1 ≤ 4 := by
      have h5 : (p 0 - c 0) / (ε / 2) < (5 : ℝ) := by
        have h6 : p 0 - c 0 ≤ 2 * ε := by linarith [abs_le.mp h1]
        have h7 : (p 0 - c 0) / (ε / 2) ≤ (2 * ε) / (ε / 2) := by gcongr
        have h8 : (2 * ε) / (ε / 2) = 4 := by field_simp [hε2_pos.ne'] <;> ring
        linarith
      have h_iff : ⌊(p 0 - c 0) / (ε / 2)⌋ < (5 : ℤ) ↔ (p 0 - c 0) / (ε / 2) < (↑(5 : ℤ) : ℝ) := Int.floor_lt
      have hlt : ⌊(p 0 - c 0) / (ε / 2)⌋ < (5 : ℤ) := h_iff.mpr (by exact_mod_cast h5)
      exact Int.lt_add_one_iff.mp hlt
    have h5 : -4 ≤ (cell p).2 := by
      have h6 : (-4 : ℝ) ≤ (p 1 - c 1) / (ε / 2) := by
        have h7 : -2 * ε ≤ p 1 - c 1 := by linarith [abs_le.mp h2]
        have h8 : (-2 * ε) / (ε / 2) ≤ (p 1 - c 1) / (ε / 2) := by gcongr
        have h9 : (-2 * ε) / (ε / 2) = -4 := by field_simp [hε2_pos.ne'] <;> ring
        linarith
      have h_iff : (-4 : ℤ) ≤ ⌊(p 1 - c 1) / (ε / 2)⌋ ↔ ((-4 : ℤ) : ℝ) ≤ (p 1 - c 1) / (ε / 2) := Int.le_floor
      exact h_iff.mpr (by norm_num <;> exact h6)
    have h6 : (cell p).2 ≤ 4 := by
      have h7 : (p 1 - c 1) / (ε / 2) < (5 : ℝ) := by
        have h8 : p 1 - c 1 ≤ 2 * ε := by linarith [abs_le.mp h2]
        have h9 : (p 1 - c 1) / (ε / 2) ≤ (2 * ε) / (ε / 2) := by gcongr
        have h10 : (2 * ε) / (ε / 2) = 4 := by field_simp [hε2_pos.ne'] <;> ring
        linarith
      have h_iff : ⌊(p 1 - c 1) / (ε / 2)⌋ < (5 : ℤ) ↔ (p 1 - c 1) / (ε / 2) < (↑(5 : ℤ) : ℝ) := Int.floor_lt
      have hlt : ⌊(p 1 - c 1) / (ε / 2)⌋ < (5 : ℤ) := h_iff.mpr (by exact_mod_cast h7)
      exact Int.lt_add_one_iff.mp hlt
    simp only [S, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨h3, h4⟩, ⟨h5, h6⟩⟩
  have h_image : (Q.image cell).card ≤ 81 := by
    calc (Q.image cell).card ≤ S.card := Finset.card_le_card h_sub
    _ = 81 := hS_card
  have h_card : Q.card = (Q.image cell).card := by
    rw [Finset.card_image_of_injOn h_inj]
  rw [h_card]
  exact h_image

/-- For a finite ε-separated set P in EuclideanPlane,
    externalCoveringNumber(ε, P) ≥ |P| / 81. -/
lemma ncover_lower_bound_separated81
    {P : Finset Plane} {ε : ℝ} (hε_pos : 0 < ε)
    (hsep : (P : Set Plane).Pairwise fun x y => ε ≤ dist x y) :
    ENNReal.ofReal (1 / 81 : ℝ) * ↑(P.card) ≤
      (Metric.externalCoveringNumber ε.toNNReal (P : Set Plane) : ENNReal) := by
  classical
  let ε' : NNReal := ε.toNNReal
  have hε'_coe : (ε' : ℝ) = ε := by
    rw [Real.coe_toNNReal] <;> linarith
  let B_set : Set Plane := Metric.maximalSeparatedSet (2 * ε') (P : Set Plane)
  have hB_sub : B_set ⊆ (P : Set Plane) := Metric.maximalSeparatedSet_subset
  have hB_finite : B_set.Finite := Set.Finite.subset P.finite_toSet hB_sub
  let B : Finset Plane := hB_finite.toFinset
  have hB_eq : (B : Set Plane) = B_set := Set.Finite.coe_toFinset _
  have h_pack_ne_top : Metric.packingNumber (2 * ε') (P : Set Plane) ≠ ⊤ := by
    have h1 : Metric.packingNumber (2 * ε') (P : Set Plane) ≤ (P : Set Plane).encard :=
      Metric.packingNumber_le_encard_self (A := (P : Set Plane))
    have h2 : (P : Set Plane).encard ≠ ⊤ := by simpa using P.finite_toSet
    exact ne_top_of_le_ne_top h2 h1
  have h_encard_B : B_set.encard = Metric.packingNumber (2 * ε') (P : Set Plane) :=
    Metric.encard_maximalSeparatedSet h_pack_ne_top
  have h_card_B : (B.card : ENNReal) = Metric.packingNumber (2 * ε') (P : Set Plane) := by
    have h3 : B_set.encard = ↑(B.card) := by
      have h4 : B_set = (B : Set Plane) := hB_eq.symm
      rw [h4] <;> simp
    rw [h3] at h_encard_B
    exact_mod_cast h_encard_B
  have h_cover : Metric.IsCover (2 * ε') (P : Set Plane) B_set :=
    Metric.isCover_maximalSeparatedSet h_pack_ne_top
  have h_main : ∀ b ∈ B, (P.filter (fun p => p ∈ Metric.closedBall b (2 * ε))).card ≤ 81 := by
    intro b _
    exact ball_separated_card_le81 hε_pos hsep b
  have h9 : P ⊆ B.biUnion (fun b => P.filter (fun p => p ∈ Metric.closedBall b (2 * ε))) := by
    intro p hp
    have h5 : p ∈ (P : Set Plane) := hp
    have h6 : ∃ b ∈ B_set, edist p b ≤ 2 * ε' := h_cover h5
    rcases h6 with ⟨b, hb, hdist⟩
    have h7 : b ∈ B := by
      rw [← Finset.mem_coe, hB_eq]
      exact hb
    have h8 : dist p b ≤ 2 * ε := by
      have h9 : edist p b ≤ ↑(2 * ε') := hdist
      have h10 : edist p b = ENNReal.ofReal (dist p b) := by rw [edist_dist]
      rw [h10] at h9
      have h11 : (↑(2 * ε') : ENNReal) = ENNReal.ofReal (2 * ε) := by
        simp [ε', hε'_coe] <;> norm_cast
      rw [h11] at h9
      have h12 : ENNReal.ofReal (dist p b) ≤ ENNReal.ofReal (2 * ε) := h9
      have h15 : dist p b ≤ 2 * ε := by
        exact (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ 2 * ε by linarith)).mp h12
      exact h15
    have h91 : p ∈ P.filter (fun p => p ∈ Metric.closedBall b (2 * ε)) := by
      simp only [Finset.mem_filter]
      exact ⟨hp, h8⟩
    exact Finset.mem_biUnion.mpr ⟨b, h7, h91⟩
  have h10 : P.card ≤ ∑ b ∈ B, (P.filter (fun p => p ∈ Metric.closedBall b (2 * ε))).card := by
    calc P.card
      ≤ (B.biUnion (fun b => P.filter (fun p => p ∈ Metric.closedBall b (2 * ε)))).card :=
        Finset.card_le_card h9
    _ ≤ ∑ b ∈ B, (P.filter (fun p => p ∈ Metric.closedBall b (2 * ε))).card :=
      Finset.card_biUnion_le
  have h11 : ∑ b ∈ B, (P.filter (fun p => p ∈ Metric.closedBall b (2 * ε))).card ≤ 81 * B.card := by
    calc ∑ b ∈ B, (P.filter (fun p => p ∈ Metric.closedBall b (2 * ε))).card
      ≤ ∑ _ ∈ B, 81 := Finset.sum_le_sum fun i _ => h_main i ‹_›
    _ = 81 * B.card := by simp [mul_comm] <;> ring
  have h12 : (P.card : ℝ) ≤ 81 * (B.card : ℝ) := by
    exact_mod_cast calc P.card
      ≤ ∑ b ∈ B, (P.filter (fun p => p ∈ Metric.closedBall b (2 * ε))).card := h10
    _ ≤ 81 * B.card := h11
  have h13 : (P.card : ℝ) / 81 ≤ (B.card : ℝ) := by linarith
  have h14 : (B.card : ENNReal) ≤ Metric.externalCoveringNumber ε' (P : Set Plane) := by
    rw [h_card_B]
    exact_mod_cast Metric.packingNumber_two_mul_le_externalCoveringNumber ε' (P : Set Plane)
  have h15 : ENNReal.ofReal ((P.card : ℝ) / 81) ≤ Metric.externalCoveringNumber ε' (P : Set Plane) := by
    calc ENNReal.ofReal ((P.card : ℝ) / 81)
      ≤ (B.card : ENNReal) := by exact_mod_cast h13
    _ ≤ Metric.externalCoveringNumber ε' (P : Set Plane) := h14
  have h16 : ENNReal.ofReal (1 / 81 : ℝ) * (P.card : ENNReal) = ENNReal.ofReal ((P.card : ℝ) / 81) := by
    have h17 : (P.card : ENNReal) = ENNReal.ofReal (P.card : ℝ) := by simp
    rw [h17]
    have h18 : ENNReal.ofReal (1 / 81 : ℝ) * ENNReal.ofReal (P.card : ℝ) =
        ENNReal.ofReal ((1 / 81 : ℝ) * (P.card : ℝ)) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h18]
    have h19 : (1 / 81 : ℝ) * (P.card : ℝ) = (P.card : ℝ) / 81 := by ring
    rw [h19]
  rw [h16]
  exact h15

end DirecretisedFurstenbergEstimate.AppendixA4
