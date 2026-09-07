module

/-
  Retention cover comparison lemmas.

  1. `squares_card_le_nine_times_ncover`: if every square in a finset meets P,
     then card(squares) ≤ 9 * Ncover(P).
  2. `retention_cover_comparison`: Ncover(config.pointSet) ≤ 9 * Ncover(P_common).

  Whiteprint node: section9 / retention_cover_comparison
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- A finset of integers all lying in (a, a+3] has cardinality at most 3. -/
lemma int_count_le_three (a : ℝ) {S : Finset ℤ}
    (h : ∀ i ∈ S, a < (i : ℝ) ∧ (i : ℝ) ≤ a + 3) : S.card ≤ 3 := by
  by_cases hS : S = ∅
  · rw [hS]; simp
  · let lower : ℤ := ⌊a⌋ + 1
    have h_floor1 : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
    have h_floor2 : a < (⌊a⌋ : ℝ) + 1 := Int.lt_floor_add_one a
    have h1 : ∀ i ∈ S, lower ≤ i := by
      intro i hi
      have h2 : a < (i : ℝ) := (h i hi).1
      have h3 : (⌊a⌋ : ℝ) < (i : ℝ) := by linarith
      have h4 : ⌊a⌋ < i := by exact_mod_cast h3
      have h5 : ⌊a⌋ + 1 ≤ i := by omega
      simpa [lower] using h5
    have h2 : ∀ i ∈ S, i ≤ lower + 2 := by
      intro i hi
      have h3 : (i : ℝ) ≤ a + 3 := (h i hi).2
      have h4 : (i : ℝ) < (⌊a⌋ : ℝ) + 4 := by linarith
      have h5 : i < ⌊a⌋ + 4 := by exact_mod_cast h4
      have h6 : i ≤ ⌊a⌋ + 3 := by omega
      have h7 : lower + 2 = ⌊a⌋ + 3 := by
        simp [lower] <;> omega
      rw [h7]
      exact h6
    have h3 : S ⊆ Finset.Icc lower (lower + 2) := by
      intro i hi
      have h5 : lower ≤ i := h1 i hi
      have h6 : i ≤ lower + 2 := h2 i hi
      simpa [Finset.mem_Icc] using ⟨h5, h6⟩
    have h4 : S.card ≤ (Finset.Icc lower (lower + 2)).card := Finset.card_le_card h3
    have h5 : (Finset.Icc lower (lower + 2)).card = 3 := by
      simp [Finset.Icc_eq_empty_of_lt] <;> omega
    rw [h5] at h4
    exact h4

/-- A δ_k-ball around c intersects at most 9 dyadic squares of level k. -/
lemma ball_squares_bound {k : ℕ} (c : EuclideanPlane)
    (Q : Finset (DyadicSquare k))
    (hQ : ∀ q ∈ Q, (q.toSet ∩ Metric.closedBall c (dyadicDelta k)).Nonempty) :
    Q.card ≤ 9 := by
  let δ := dyadicDelta k
  have hδ_pos : 0 < δ := dyadicDelta_pos k

  have hdist_eq : ∀ (x : EuclideanPlane), dist x c = Real.sqrt ((x 0 - c 0)^2 + (x 1 - c 1)^2) := by
    intro x
    have h1 : dist x c = ((x 0 - c 0)^2 + (x 1 - c 1)^2) ^ (2⁻¹ : ℝ) := by
      simp [dist, EuclideanSpace.dist_eq, Fin.sum_univ_two] <;> ring
    rw [h1]
    have h21 : (2⁻¹ : ℝ) = 1 / 2 := by norm_num
    rw [h21]
    rw [Real.sqrt_eq_rpow] <;> positivity

  have h1 : ∀ q ∈ Q, (c 0) / δ - 2 < (q.i : ℝ) ∧ (q.i : ℝ) ≤ (c 0) / δ + 1 ∧
      (c 1) / δ - 2 < (q.j : ℝ) ∧ (q.j : ℝ) ≤ (c 1) / δ + 1 := by
    intro q hq
    rcases hQ q hq with ⟨x, hxq, hxc⟩
    have h_dist : dist x c ≤ δ := hxc
    have hdeq : dist x c = Real.sqrt ((x 0 - c 0)^2 + (x 1 - c 1)^2) := hdist_eq x

    have h_coord0 : |x 0 - c 0| ≤ dist x c := by
      have h_sq : (x 0 - c 0)^2 ≤ (x 0 - c 0)^2 + (x 1 - c 1)^2 := by
        have h_pos2 : 0 ≤ (x 1 - c 1)^2 := by positivity
        linarith
      have h_sqrt : Real.sqrt ((x 0 - c 0)^2) ≤ Real.sqrt ((x 0 - c 0)^2 + (x 1 - c 1)^2) :=
        Real.sqrt_le_sqrt h_sq
      have h_abs : Real.sqrt ((x 0 - c 0)^2) = |x 0 - c 0| := by
        have hsq2 : (x 0 - c 0)^2 = |x 0 - c 0|^2 := by rw [sq_abs]
        rw [hsq2, Real.sqrt_sq (abs_nonneg (x 0 - c 0))]
      rw [h_abs] at h_sqrt
      have h_goal : |x 0 - c 0| ≤ dist x c := by
        rw [hdeq]
        exact h_sqrt
      exact h_goal

    have h_coord1 : |x 1 - c 1| ≤ dist x c := by
      have h_sq : (x 1 - c 1)^2 ≤ (x 0 - c 0)^2 + (x 1 - c 1)^2 := by
        have h_pos2 : 0 ≤ (x 0 - c 0)^2 := by positivity
        linarith
      have h_sqrt : Real.sqrt ((x 1 - c 1)^2) ≤ Real.sqrt ((x 0 - c 0)^2 + (x 1 - c 1)^2) :=
        Real.sqrt_le_sqrt h_sq
      have h_abs : Real.sqrt ((x 1 - c 1)^2) = |x 1 - c 1| := by
        have hsq2 : (x 1 - c 1)^2 = |x 1 - c 1|^2 := by rw [sq_abs]
        rw [hsq2, Real.sqrt_sq (abs_nonneg (x 1 - c 1))]
      rw [h_abs] at h_sqrt
      have h_goal : |x 1 - c 1| ≤ dist x c := by
        rw [hdeq]
        exact h_sqrt
      exact h_goal

    have hx0 : |x 0 - c 0| ≤ δ := h_coord0.trans h_dist
    have hx1 : |x 1 - c 1| ≤ δ := h_coord1.trans h_dist
    have hx0_ge : (q.i : ℝ) * δ ≤ x 0 := hxq.1
    have hx0_lt : x 0 < ((q.i : ℝ) + 1) * δ := hxq.2.1
    have hx1_ge : (q.j : ℝ) * δ ≤ x 1 := hxq.2.2.1
    have hx1_lt : x 1 < ((q.j : ℝ) + 1) * δ := hxq.2.2.2
    have h_abs01 : c 0 - δ ≤ x 0 := by
      have h : -δ ≤ x 0 - c 0 := (abs_le.mp hx0).1; linarith
    have h_abs02 : x 0 ≤ c 0 + δ := by
      have h : x 0 - c 0 ≤ δ := (abs_le.mp hx0).2; linarith
    have h_abs11 : c 1 - δ ≤ x 1 := by
      have h : -δ ≤ x 1 - c 1 := (abs_le.mp hx1).1; linarith
    have h_abs12 : x 1 ≤ c 1 + δ := by
      have h : x 1 - c 1 ≤ δ := (abs_le.mp hx1).2; linarith

    constructor
    · have h : c 0 - δ < ((q.i : ℝ) + 1) * δ := by linarith
      have h2 : (c 0 - δ) / δ < (q.i : ℝ) + 1 := by
        have h3 : (c 0 - δ) < ((q.i : ℝ) + 1) * δ := h
        have h4 : (c 0 - δ) / δ < (((q.i : ℝ) + 1) * δ) / δ := by gcongr
        have h5 : (((q.i : ℝ) + 1) * δ) / δ = (q.i : ℝ) + 1 := by
          field_simp [hδ_pos.ne'] <;> ring
        rw [h5] at h4; exact h4
      have h6 : (c 0 - δ) / δ = (c 0) / δ - 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h6] at h2; linarith
    · constructor
      · have h : (q.i : ℝ) * δ ≤ c 0 + δ := by linarith
        have h2 : (q.i : ℝ) ≤ (c 0 + δ) / δ := by
          have h3 : (q.i : ℝ) * δ ≤ c 0 + δ := h
          have h4 : ((q.i : ℝ) * δ) / δ ≤ (c 0 + δ) / δ := by gcongr
          have h5 : ((q.i : ℝ) * δ) / δ = (q.i : ℝ) := by
            field_simp [hδ_pos.ne'] <;> ring
          rw [h5] at h4; exact h4
        have h6 : (c 0 + δ) / δ = (c 0) / δ + 1 := by
          field_simp [hδ_pos.ne'] <;> ring
        rw [h6] at h2; exact h2
      · constructor
        · have h : c 1 - δ < ((q.j : ℝ) + 1) * δ := by linarith
          have h2 : (c 1 - δ) / δ < (q.j : ℝ) + 1 := by
            have h3 : (c 1 - δ) < ((q.j : ℝ) + 1) * δ := h
            have h4 : (c 1 - δ) / δ < (((q.j : ℝ) + 1) * δ) / δ := by gcongr
            have h5 : (((q.j : ℝ) + 1) * δ) / δ = (q.j : ℝ) + 1 := by
              field_simp [hδ_pos.ne'] <;> ring
            rw [h5] at h4; exact h4
          have h6 : (c 1 - δ) / δ = (c 1) / δ - 1 := by
            field_simp [hδ_pos.ne'] <;> ring
          rw [h6] at h2; linarith
        · have h : (q.j : ℝ) * δ ≤ c 1 + δ := by linarith
          have h2 : (q.j : ℝ) ≤ (c 1 + δ) / δ := by
            have h3 : (q.j : ℝ) * δ ≤ c 1 + δ := h
            have h4 : ((q.j : ℝ) * δ) / δ ≤ (c 1 + δ) / δ := by gcongr
            have h5 : ((q.j : ℝ) * δ) / δ = (q.j : ℝ) := by
              field_simp [hδ_pos.ne'] <;> ring
            rw [h5] at h4; exact h4
          have h6 : (c 1 + δ) / δ = (c 1) / δ + 1 := by
            field_simp [hδ_pos.ne'] <;> ring
          rw [h6] at h2; exact h2

  by_cases hQ_empty : Q = ∅
  · rw [hQ_empty]; simp
  · have hQ_ne : Q.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; exact hQ_empty
    let q0 := Classical.choose hQ_ne
    have hq0 : q0 ∈ Q := Classical.choose_spec hQ_ne
    let I : Finset ℤ := Q.image (fun q => q.i)
    let J : Finset ℤ := Q.image (fun q => q.j)
    have hI_nonempty : I.Nonempty := by
      refine ⟨q0.i, Finset.mem_image.mpr ⟨q0, hq0, rfl⟩⟩
    have hJ_nonempty : J.Nonempty := by
      refine ⟨q0.j, Finset.mem_image.mpr ⟨q0, hq0, rfl⟩⟩
    have hI_card : I.card ≤ 3 := int_count_le_three ((c 0) / δ - 2)
        (fun i hi =>
          have h_exists : ∃ (q : DyadicSquare k), q ∈ Q ∧ q.i = i := Finset.mem_image.mp hi
          let ⟨q, hq, heq⟩ := h_exists
          have h_lower : (c 0) / δ - 2 < (q.i : ℝ) := (h1 q hq).1
          have h_upper : (q.i : ℝ) ≤ (c 0) / δ + 1 := (h1 q hq).2.1
          have h_final_lower : (c 0) / δ - 2 < (i : ℝ) := by exact_mod_cast (heq ▸ h_lower)
          have h_final_upper : (i : ℝ) ≤ (c 0) / δ - 2 + 3 := by
            have h1 : (i : ℝ) = (q.i : ℝ) := by exact_mod_cast heq.symm
            have h2 : (q.i : ℝ) ≤ (c 0) / δ + 1 := h_upper
            have h3 : (c 0) / δ + 1 = (c 0) / δ - 2 + 3 := by ring
            linarith
          ⟨h_final_lower, h_final_upper⟩)
    have hJ_card : J.card ≤ 3 := int_count_le_three ((c 1) / δ - 2)
        (fun j hj =>
          have h_exists : ∃ (q : DyadicSquare k), q ∈ Q ∧ q.j = j := Finset.mem_image.mp hj
          let ⟨q, hq, heq⟩ := h_exists
          have h_lower : (c 1) / δ - 2 < (q.j : ℝ) := (h1 q hq).2.2.1
          have h_upper : (q.j : ℝ) ≤ (c 1) / δ + 1 := (h1 q hq).2.2.2
          have h_final_lower : (c 1) / δ - 2 < (j : ℝ) := by exact_mod_cast (heq ▸ h_lower)
          have h_final_upper : (j : ℝ) ≤ (c 1) / δ - 2 + 3 := by
            have h1 : (j : ℝ) = (q.j : ℝ) := by exact_mod_cast heq.symm
            have h2 : (q.j : ℝ) ≤ (c 1) / δ + 1 := h_upper
            have h3 : (c 1) / δ + 1 = (c 1) / δ - 2 + 3 := by ring
            linarith
          ⟨h_final_lower, h_final_upper⟩)
    have h_inj : Set.InjOn (fun q : DyadicSquare k => (q.i, q.j)) (Q : Set (DyadicSquare k)) := by
      intro q1 _ q2 _ h; cases q1 <;> cases q2 <;> simp_all
    have h_card_image : (Q.image (fun q => (q.i, q.j))).card = Q.card :=
      Finset.card_image_of_injOn h_inj
    have h_sub : Q.image (fun q => (q.i, q.j)) ⊆ I ×ˢ J := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      have h_i_in : q.i ∈ I := Finset.mem_image.mpr ⟨q, hq, rfl⟩
      have h_j_in : q.j ∈ J := Finset.mem_image.mpr ⟨q, hq, rfl⟩
      exact Finset.mem_product.mpr ⟨h_i_in, h_j_in⟩
    have h_prod : (I ×ˢ J).card = I.card * J.card := Finset.card_product I J
    calc Q.card
      = (Q.image (fun q => (q.i, q.j))).card := h_card_image.symm
    _ ≤ (I ×ˢ J).card := Finset.card_le_card h_sub
    _ = I.card * J.card := h_prod
    _ ≤ 3 * 3 := by gcongr <;> omega
    _ = 9 := by norm_num

/-- If every square in a finset meets P, then card(squares) ≤ 9 * Ncover(P). -/
lemma squares_card_le_nine_times_ncover
    {k : ℕ} {P : Set EuclideanPlane} {squares : Finset (DyadicSquare k)}
    (h_intersect : ∀ q ∈ squares, (q.toSet ∩ P).Nonempty) :
    (squares.card : ENNReal) ≤ 9 * Metric.externalCoveringNumber (dyadicDelta k).toNNReal P := by
  let δ := dyadicDelta k
  have hδ_pos : 0 < δ := dyadicDelta_pos k

  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal P = ⊤
  · rw [h_top] <;> simp

  · have h_exists : ∃ (C : Set EuclideanPlane), C.Finite ∧ Metric.IsCover δ.toNNReal P C ∧
        C.encard = Metric.externalCoveringNumber δ.toNNReal P := by
      have h_univ : Metric.IsCover δ.toNNReal P Set.univ := by
        intro x _; exact ⟨x, by simp, by simp⟩
      let S' := {C : Set EuclideanPlane // Metric.IsCover δ.toNNReal P C}
      have hne : Nonempty S' := ⟨⟨Set.univ, h_univ⟩⟩
      let f : S' → ℕ∞ := fun C => (C : Set EuclideanPlane).encard
      have h_exists2 : ∃ (C : S'), f C = iInf f := ENat.exists_eq_iInf (f := f)
      rcases h_exists2 with ⟨C, hC⟩
      have h_inf : iInf f = Metric.externalCoveringNumber δ.toNNReal P := by
        unfold f Metric.externalCoveringNumber
        rw [iInf_subtype] <;> congr
      have h_val : (C : Set EuclideanPlane).encard = Metric.externalCoveringNumber δ.toNNReal P := by
        have h_fC : (C : Set EuclideanPlane).encard = f C := by rfl
        rw [h_fC, hC, h_inf]
      have h_ne : (C : Set EuclideanPlane).encard ≠ ⊤ := by rw [h_val]; exact h_top
      have h_lt : (C : Set EuclideanPlane).encard < ⊤ := by exact Ne.lt_top' (id (Ne.symm h_ne))
      have h_fin : (C : Set EuclideanPlane).Finite := Set.encard_lt_top_iff.mp h_lt
      exact ⟨(C : Set EuclideanPlane), h_fin, C.2, h_val⟩
    rcases h_exists with ⟨C, hC_fin, hC_cover, hC_encard⟩
    let C_finset : Finset EuclideanPlane := hC_fin.toFinset
    have hC_coe : (C_finset : Set EuclideanPlane) = C := hC_fin.coe_toFinset
    have hC_cover' : ∀ (p : EuclideanPlane), p ∈ P → ∃ (c : EuclideanPlane), c ∈ C ∧ edist p c ≤ ↑δ.toNNReal := by
      intro p hp
      exact hC_cover hp

    let squares_hit : EuclideanPlane → Finset (DyadicSquare k) := fun c =>
      squares.filter (fun q => (q.toSet ∩ Metric.closedBall c δ).Nonempty)

    have h_hit_bound : ∀ c ∈ C_finset, (squares_hit c).card ≤ 9 := by
      intro c _
      exact ball_squares_bound c (squares_hit c)
        (fun q hq => (Finset.mem_filter.mp hq).2)

    have h_cover : squares ⊆ C_finset.biUnion squares_hit := by
      intro q hq
      rcases h_intersect q hq with ⟨p, hpq, hpP⟩
      rcases hC_cover' p hpP with ⟨c, hcC, hdist⟩
      have hc_in : c ∈ C_finset := by
        have h1 : c ∈ (C_finset : Set EuclideanPlane) := by
          rw [hC_coe]
          exact hcC
        exact h1
      have h3 : p ∈ Metric.closedBall c δ := by
        have h4 : edist p c ≤ ↑δ.toNNReal := hdist
        have h5 : dist p c ≤ δ := by
          rw [edist_dist] at h4
          have hδ_nn : 0 ≤ δ := hδ_pos.le
          have h_toNNReal : (δ.toNNReal : ℝ) = δ := by
            simp [NNReal.coe_mk, hδ_nn] <;> linarith
          have h6 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
            rw [←ENNReal.ofReal_coe_nnreal, h_toNNReal]
          rw [h6] at h4
          have h7 : ENNReal.ofReal (dist p c) ≤ ENNReal.ofReal δ := h4
          have h8 : dist p c ≤ δ := by
            exact (edist_le_ofReal hδ_nn).mp hdist
          exact h8
        simpa [Metric.mem_closedBall] using h5
      have h4 : (q.toSet ∩ Metric.closedBall c δ).Nonempty := ⟨p, hpq, h3⟩
      have h5 : q ∈ squares_hit c := by
        simp only [squares_hit, Finset.mem_filter] <;> exact ⟨hq, h4⟩
      exact Finset.mem_biUnion.mpr ⟨c, hc_in, h5⟩

    have h_squares_card : squares.card ≤ 9 * C_finset.card := by
      calc squares.card
        ≤ (C_finset.biUnion squares_hit).card := Finset.card_le_card h_cover
      _ ≤ ∑ c ∈ C_finset, (squares_hit c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ C_finset, 9 := Finset.sum_le_sum h_hit_bound
      _ = 9 * C_finset.card := by simp [Finset.sum_const] <;> ring

    calc (squares.card : ENNReal)
      ≤ (9 * C_finset.card : ENNReal) := by exact_mod_cast h_squares_card
    _ = (9 : ENNReal) * (C_finset.card : ENNReal) := by simp [mul_comm] <;> ring
    _ = (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P := by
      have h9 : (C_finset.card : ENNReal) = C.encard := by
        have h10 : (C_finset.card : ENNReal) = (C_finset : Set EuclideanPlane).encard := by
          simp
        rw [h10]
        have h11 : (C_finset : Set EuclideanPlane).encard = C.encard := by
          rw [hC_coe]
        rw [h11]
      rw [h9, hC_encard] <;> ring

/-- If P ⊆ ⋃_{q ∈ squares} q.toSet, then Ncover(P) ≤ card(squares).
    Each dyadic square is covered by one δ-ball at its center. -/
lemma ncover_le_card_squares
    {k : ℕ} {P : Set EuclideanPlane} {squares : Finset (DyadicSquare k)}
    (hP_sub : P ⊆ ⋃ q ∈ squares, (q.toSet : Set EuclideanPlane)) :
    Metric.externalCoveringNumber (dyadicDelta k).toNNReal P ≤ (squares.card : ENNReal) := by
  let δ := dyadicDelta k
  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδ_nn : 0 ≤ δ := hδ_pos.le
  let center_of_square (q : DyadicSquare k) : EuclideanPlane :=
    TubesAndSlopes.mkPlane (((q.i : ℝ) + 1 / 2) * δ) (((q.j : ℝ) + 1 / 2) * δ)
  have h_cover_one : ∀ (q : DyadicSquare k), (q.toSet : Set EuclideanPlane) ⊆ Metric.closedBall (center_of_square q) δ := by
    intro q x hx
    have h1 : (q.i : ℝ) * δ ≤ x 0 := hx.1
    have h2 : x 0 < ((q.i : ℝ) + 1) * δ := hx.2.1
    have h3 : (q.j : ℝ) * δ ≤ x 1 := hx.2.2.1
    have h4 : x 1 < ((q.j : ℝ) + 1) * δ := hx.2.2.2
    set ctr := center_of_square q with hctr_def
    have hctr0 : ctr 0 = ((q.i : ℝ) + 1 / 2) * δ := by simp [center_of_square, hctr_def, TubesAndSlopes.mkPlane_apply0]
    have hctr1 : ctr 1 = ((q.j : ℝ) + 1 / 2) * δ := by simp [center_of_square, hctr_def, TubesAndSlopes.mkPlane_apply1]
    have h5 : |x 0 - ctr 0| ≤ δ / 2 := by
      rw [hctr0]; have h51 : -(δ / 2) ≤ x 0 - ((q.i : ℝ) + 1 / 2) * δ := by linarith
      have h52 : x 0 - ((q.i : ℝ) + 1 / 2) * δ ≤ δ / 2 := by linarith
      exact abs_le.mpr ⟨h51, h52⟩
    have h6 : |x 1 - ctr 1| ≤ δ / 2 := by
      rw [hctr1]; have h61 : -(δ / 2) ≤ x 1 - ((q.j : ℝ) + 1 / 2) * δ := by linarith
      have h62 : x 1 - ((q.j : ℝ) + 1 / 2) * δ ≤ δ / 2 := by linarith
      exact abs_le.mpr ⟨h61, h62⟩
    have hdist_eq : dist x ctr = Real.sqrt ((x 0 - ctr 0)^2 + (x 1 - ctr 1)^2) := by
      have h1 : dist x ctr = ((x 0 - ctr 0)^2 + (x 1 - ctr 1)^2) ^ (2⁻¹ : ℝ) := by
        simp [dist, EuclideanSpace.dist_eq, Fin.sum_univ_two] <;> ring
      rw [h1]; have h21 : (2⁻¹ : ℝ) = 1 / 2 := by norm_num
      rw [h21]; rw [Real.sqrt_eq_rpow] <;> positivity
    have hdist : dist x ctr ≤ δ := by
      rw [hdist_eq]
      have h5' : (x 0 - ctr 0)^2 ≤ (δ / 2)^2 := by
        have h_abs1 : -(δ / 2) ≤ x 0 - ctr 0 := (abs_le.mp h5).1
        have h_abs2 : x 0 - ctr 0 ≤ δ / 2 := (abs_le.mp h5).2
        nlinarith
      have h6' : (x 1 - ctr 1)^2 ≤ (δ / 2)^2 := by
        have h_abs1 : -(δ / 2) ≤ x 1 - ctr 1 := (abs_le.mp h6).1
        have h_abs2 : x 1 - ctr 1 ≤ δ / 2 := (abs_le.mp h6).2
        nlinarith
      have h3 : (x 0 - ctr 0)^2 + (x 1 - ctr 1)^2 ≤ δ^2 := by nlinarith
      have h4 : Real.sqrt ((x 0 - ctr 0)^2 + (x 1 - ctr 1)^2) ≤ Real.sqrt (δ^2) := Real.sqrt_le_sqrt h3
      have h5_sqrt : Real.sqrt (δ^2) = δ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hδ_nn]
      rw [h5_sqrt] at h4; exact h4
    simpa [Metric.mem_closedBall] using hdist
  have h_pointSet_cover : Metric.IsCover δ.toNNReal P (squares.image center_of_square : Set EuclideanPlane) := by
    intro x hx
    have h_in_union : x ∈ ⋃ q ∈ squares, (q.toSet : Set EuclideanPlane) := hP_sub hx
    rcases Set.mem_iUnion₂.mp h_in_union with ⟨q, hq, hxq⟩
    let ctr := center_of_square q
    have hctr_in : ctr ∈ (squares.image center_of_square : Set EuclideanPlane) := Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have h_in_ball : x ∈ Metric.closedBall ctr δ := h_cover_one q hxq
    have h_edist : edist x ctr ≤ ↑δ.toNNReal := by
      have hdist : dist x ctr ≤ δ := by simpa [Metric.mem_closedBall] using h_in_ball
      rw [edist_dist]
      have h_toNNReal : (δ.toNNReal : ℝ) = δ := by simp [NNReal.coe_mk, hδ_nn] <;> linarith
      have h2 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by rw [←ENNReal.ofReal_coe_nnreal, h_toNNReal]
      rw [h2]; exact ENNReal.ofReal_le_ofReal hdist
    exact ⟨ctr, hctr_in, h_edist⟩
  have h_inj : Set.InjOn center_of_square (squares : Set (DyadicSquare k)) := by
    intro q1 _ q2 _ h
    have h0 : (center_of_square q1) 0 = (center_of_square q2) 0 := by rw [h]
    have h1 : (center_of_square q1) 1 = (center_of_square q2) 1 := by rw [h]
    have hctr0_1 : (center_of_square q1) 0 = ((q1.i : ℝ) + 1 / 2) * δ := by simp [center_of_square, TubesAndSlopes.mkPlane_apply0]
    have hctr0_2 : (center_of_square q2) 0 = ((q2.i : ℝ) + 1 / 2) * δ := by simp [center_of_square, TubesAndSlopes.mkPlane_apply0]
    have hctr1_1 : (center_of_square q1) 1 = ((q1.j : ℝ) + 1 / 2) * δ := by simp [center_of_square, TubesAndSlopes.mkPlane_apply1]
    have hctr1_2 : (center_of_square q2) 1 = ((q2.j : ℝ) + 1 / 2) * δ := by simp [center_of_square, TubesAndSlopes.mkPlane_apply1]
    have h_eq_i : ((q1.i : ℝ) + 1 / 2) * δ = ((q2.i : ℝ) + 1 / 2) * δ := by
      calc ((q1.i : ℝ) + 1 / 2) * δ = (center_of_square q1) 0 := hctr0_1.symm
      _ = (center_of_square q2) 0 := h0
      _ = ((q2.i : ℝ) + 1 / 2) * δ := hctr0_2
    have h_eq_j : ((q1.j : ℝ) + 1 / 2) * δ = ((q2.j : ℝ) + 1 / 2) * δ := by
      calc ((q1.j : ℝ) + 1 / 2) * δ = (center_of_square q1) 1 := hctr1_1.symm
      _ = (center_of_square q2) 1 := h1
      _ = ((q2.j : ℝ) + 1 / 2) * δ := hctr1_2
    have hi : (q1.i : ℝ) = (q2.i : ℝ) := by apply mul_left_cancel₀ hδ_pos.ne'; linarith
    have hj : (q1.j : ℝ) = (q2.j : ℝ) := by apply mul_left_cancel₀ hδ_pos.ne'; linarith
    have hi' : q1.i = q2.i := by exact_mod_cast hi
    have hj' : q1.j = q2.j := by exact_mod_cast hj
    cases q1 <;> cases q2 <;> simp_all
  have hNcover_le : Metric.externalCoveringNumber δ.toNNReal P ≤ (squares.image center_of_square : Set EuclideanPlane).encard :=
    h_pointSet_cover.externalCoveringNumber_le_encard
  have h_encard_card : (squares.image center_of_square : Set EuclideanPlane).encard = ↑squares.card := by
    have hcard : (squares.image center_of_square).card = squares.card := Finset.card_image_of_injOn h_inj
    have h1 : (squares.image center_of_square : Set EuclideanPlane).encard = ↑((squares.image center_of_square).card) :=
      Set.encard_coe_eq_coe_finsetCard (squares.image center_of_square)
    rw [h1, hcard]
    <;> simp
  have hNcover_le_card : Metric.externalCoveringNumber δ.toNNReal P ≤ ↑squares.card := by
    rw [h_encard_card] at hNcover_le
    exact hNcover_le
  have h_goal : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤ (squares.card : ENNReal) := by
    exact_mod_cast hNcover_le_card
  exact h_goal

/-- Retention cover comparison: if every config square meets P_common, then
    Ncover(config.pointSet) ≤ 9 * Ncover(P_common). -/
lemma retention_cover_comparison
    {k : ℕ} {s C : ℝ} {M : ℕ}
    {config : NiceConfiguration k s C M}
    {P_common : Set EuclideanPlane}
    (h_intersect : ∀ q ∈ config.P₀, (q.toSet ∩ P_common).Nonempty) :
    Metric.externalCoveringNumber (dyadicDelta k).toNNReal config.pointSet ≤
      (9 : ENNReal) * Metric.externalCoveringNumber (dyadicDelta k).toNNReal P_common := by
  let δ := dyadicDelta k
  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδ_nn : 0 ≤ δ := hδ_pos.le

  let center_of_square (q : DyadicSquare k) : EuclideanPlane :=
    TubesAndSlopes.mkPlane (((q.i : ℝ) + 1 / 2) * δ) (((q.j : ℝ) + 1 / 2) * δ)

  have h_cover_one : ∀ (q : DyadicSquare k), (q.toSet : Set EuclideanPlane) ⊆
      Metric.closedBall (center_of_square q) δ := by
    intro q x hx
    have h1 : (q.i : ℝ) * δ ≤ x 0 := hx.1
    have h2 : x 0 < ((q.i : ℝ) + 1) * δ := hx.2.1
    have h3 : (q.j : ℝ) * δ ≤ x 1 := hx.2.2.1
    have h4 : x 1 < ((q.j : ℝ) + 1) * δ := hx.2.2.2
    set ctr := center_of_square q with hctr_def
    have hctr0 : ctr 0 = ((q.i : ℝ) + 1 / 2) * δ := by
      simp [center_of_square, hctr_def, TubesAndSlopes.mkPlane_apply0]
    have hctr1 : ctr 1 = ((q.j : ℝ) + 1 / 2) * δ := by
      simp [center_of_square, hctr_def, TubesAndSlopes.mkPlane_apply1]
    have h5 : |x 0 - ctr 0| ≤ δ / 2 := by
      rw [hctr0]
      have h51 : -(δ / 2) ≤ x 0 - ((q.i : ℝ) + 1 / 2) * δ := by linarith
      have h52 : x 0 - ((q.i : ℝ) + 1 / 2) * δ ≤ δ / 2 := by linarith
      exact abs_le.mpr ⟨h51, h52⟩
    have h6 : |x 1 - ctr 1| ≤ δ / 2 := by
      rw [hctr1]
      have h61 : -(δ / 2) ≤ x 1 - ((q.j : ℝ) + 1 / 2) * δ := by linarith
      have h62 : x 1 - ((q.j : ℝ) + 1 / 2) * δ ≤ δ / 2 := by linarith
      exact abs_le.mpr ⟨h61, h62⟩
    have hdist : dist x ctr ≤ δ := by
      have hdist_eq : dist x ctr = Real.sqrt ((x 0 - ctr 0)^2 + (x 1 - ctr 1)^2) := by
        have h : dist x ctr = Real.sqrt (dist (x 0) (ctr 0) ^ 2 + dist (x 1) (ctr 1) ^ 2) := by
          simp [EuclideanSpace.dist_eq, Fin.sum_univ_two] <;> rfl
        rw [h]
        have h1 : dist (x 0) (ctr 0) = |x 0 - ctr 0| := by rw [Real.dist_eq]
        have h2 : dist (x 1) (ctr 1) = |x 1 - ctr 1| := by rw [Real.dist_eq]
        rw [h1, h2, sq_abs, sq_abs]
      rw [hdist_eq]
      have h3 : (x 0 - ctr 0)^2 + (x 1 - ctr 1)^2 ≤ δ^2 := by
        have h5' : (x 0 - ctr 0)^2 ≤ (δ / 2)^2 := by
          calc (x 0 - ctr 0)^2
            ≤ |x 0 - ctr 0|^2 := by rw [sq_abs]
          _ ≤ (δ / 2)^2 := by gcongr
        have h6' : (x 1 - ctr 1)^2 ≤ (δ / 2)^2 := by
          calc (x 1 - ctr 1)^2
            ≤ |x 1 - ctr 1|^2 := by rw [sq_abs]
          _ ≤ (δ / 2)^2 := by gcongr
        have h7 : (δ / 2)^2 + (δ / 2)^2 ≤ δ^2 := by
          have h8 : (δ / 2)^2 + (δ / 2)^2 = δ^2 / 2 := by ring
          rw [h8]
          have h9 : 0 ≤ δ^2 := by positivity
          linarith
        linarith
      have h4 : Real.sqrt ((x 0 - ctr 0)^2 + (x 1 - ctr 1)^2) ≤ Real.sqrt (δ^2) := Real.sqrt_le_sqrt h3
      have h5 : Real.sqrt (δ^2) = δ := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hδ_nn]
      rw [h5] at h4
      exact h4
    simpa [Metric.mem_closedBall] using hdist

  have h_pointSet_cover : Metric.IsCover δ.toNNReal config.pointSet
      (config.P₀.image center_of_square : Set EuclideanPlane) := by
    intro x hx
    have h_pointSet_def : config.pointSet = ⋃ p ∈ config.P₀, (p.toSet : Set EuclideanPlane) := by rfl
    rw [h_pointSet_def] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨q, hq, hxq⟩
    let ctr := center_of_square q
    have hctr_in : ctr ∈ (config.P₀.image center_of_square : Set EuclideanPlane) :=
      Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have h_in_ball : x ∈ Metric.closedBall ctr δ := h_cover_one q hxq
    have h_edist : edist x ctr ≤ ↑δ.toNNReal := by
      have hdist : dist x ctr ≤ δ := by simpa [Metric.mem_closedBall] using h_in_ball
      rw [edist_dist]
      have h_toNNReal : (δ.toNNReal : ℝ) = δ := by
        simp [NNReal.coe_mk, hδ_nn] <;> linarith
      have h2 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
        rw [←ENNReal.ofReal_coe_nnreal, h_toNNReal]
      rw [h2]
      exact ENNReal.ofReal_le_ofReal hdist
    exact ⟨ctr, hctr_in, h_edist⟩

  have hNcover_le := h_pointSet_cover.externalCoveringNumber_le_encard

  have h_inj : Set.InjOn center_of_square (config.P₀ : Set (DyadicSquare k)) := by
    intro q1 _ q2 _ h
    have h0 : (center_of_square q1) 0 = (center_of_square q2) 0 := by rw [h]
    have h1 : (center_of_square q1) 1 = (center_of_square q2) 1 := by rw [h]
    have hctr0_1 : (center_of_square q1) 0 = ((q1.i : ℝ) + 1 / 2) * δ := by
      simp [center_of_square, TubesAndSlopes.mkPlane_apply0]
    have hctr0_2 : (center_of_square q2) 0 = ((q2.i : ℝ) + 1 / 2) * δ := by
      simp [center_of_square, TubesAndSlopes.mkPlane_apply0]
    have hctr1_1 : (center_of_square q1) 1 = ((q1.j : ℝ) + 1 / 2) * δ := by
      simp [center_of_square, TubesAndSlopes.mkPlane_apply1]
    have hctr1_2 : (center_of_square q2) 1 = ((q2.j : ℝ) + 1 / 2) * δ := by
      simp [center_of_square, TubesAndSlopes.mkPlane_apply1]
    have h_eq_i : ((q1.i : ℝ) + 1 / 2) * δ = ((q2.i : ℝ) + 1 / 2) * δ := by
      calc ((q1.i : ℝ) + 1 / 2) * δ
        = (center_of_square q1) 0 := hctr0_1.symm
      _ = (center_of_square q2) 0 := h0
      _ = ((q2.i : ℝ) + 1 / 2) * δ := hctr0_2
    have h_eq_j : ((q1.j : ℝ) + 1 / 2) * δ = ((q2.j : ℝ) + 1 / 2) * δ := by
      calc ((q1.j : ℝ) + 1 / 2) * δ
        = (center_of_square q1) 1 := hctr1_1.symm
      _ = (center_of_square q2) 1 := h1
      _ = ((q2.j : ℝ) + 1 / 2) * δ := hctr1_2
    have hi : (q1.i : ℝ) = (q2.i : ℝ) := by
      apply mul_left_cancel₀ hδ_pos.ne'
      linarith
    have hj : (q1.j : ℝ) = (q2.j : ℝ) := by
      apply mul_left_cancel₀ hδ_pos.ne'
      linarith
    have hi' : q1.i = q2.i := by exact_mod_cast hi
    have hj' : q1.j = q2.j := by exact_mod_cast hj
    cases q1 <;> cases q2 <;> simp_all
  have h_encard_card : (↑(config.P₀.image center_of_square : Set EuclideanPlane).encard : ENNReal) = (config.P₀.card : ENNReal) := by
    have hfin : (config.P₀.image center_of_square : Set EuclideanPlane).Finite := by exact Finset.finite_toSet (Finset.image center_of_square config.P₀)
    have hcard : (config.P₀.image center_of_square).card = config.P₀.card :=
      Finset.card_image_of_injOn h_inj
    have h1 : (config.P₀.image center_of_square : Set EuclideanPlane).encard = ↑((config.P₀.image center_of_square).card) := by
      exact Set.encard_coe_eq_coe_finsetCard (Finset.image center_of_square config.P₀)
    have h2 : (↑(config.P₀.image center_of_square : Set EuclideanPlane).encard : ENNReal) = ↑((config.P₀.image center_of_square).card) := by
      rw [h1] <;> norm_cast
    rw [h2, hcard] <;> norm_cast

  have h_squares_le : (config.P₀.card : ENNReal) ≤
      (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P_common :=
    squares_card_le_nine_times_ncover h_intersect

  calc Metric.externalCoveringNumber δ.toNNReal config.pointSet
    ≤ (↑(config.P₀.image center_of_square : Set EuclideanPlane).encard : ENNReal) := by exact_mod_cast hNcover_le
  _ = (config.P₀.card : ENNReal) := h_encard_card
  _ ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P_common := h_squares_le

end DirecretisedFurstenbergEstimate.Section9
