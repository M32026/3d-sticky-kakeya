module

/-
  Main theorem for DeltasSet extraction, decomposed into 4 obligations.

  Imports the verified core and states 4 helper lemmas with sorry,
  then uses them to prove the main theorem.

  Whiteprint node: fine_point_thinning
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.DeltasSetTreeExtractionCore
public import MyLeanRepo.RobustKaufmanProjection.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate

lemma dyadicCap_nonneg (n j : ℕ) (u : ℝ) : 0 ≤ dyadicCap n j u := by
  have h1 : 0 < dyadicDelta j := dyadicDelta_pos j
  have h2 : 0 < dyadicDelta n := dyadicDelta_pos n
  have h3 : 0 ≤ dyadicDelta j / dyadicDelta n := by positivity
  have h4 : dyadicCap n j u = (dyadicDelta j / dyadicDelta n)^u := by rfl
  rw [h4]
  exact Real.rpow_nonneg h3 u

lemma nat_floor_le_dyadicCap (n j : ℕ) (u : ℝ) :
    (Nat.floor (dyadicCap n j u) : ℝ) ≤ dyadicCap n j u := by
  have h5 : 0 ≤ dyadicCap n j u := dyadicCap_nonneg n j u
  exact Nat.floor_le h5

/-- ENNReal arithmetic helper for the S-set inheritance ball bound. -/
lemma ball_bound_ennreal_arithmetic (δ C r u : ℝ) (card : ℕ) (ncover : ENNReal)
    (h_posC : 0 ≤ 10000 * C) (h_posr : 0 ≤ r) (h_posu : 0 ≤ u)
    (h10 : 25 * (r / δ)^u ≤ (10000 * C) * r^u * (card : ℝ))
    (h_ncover_eq : ncover = (↑card : ENNReal)) :
    ENNReal.ofReal (25 * (r / δ)^u) ≤
      ENNReal.ofReal (10000 * C) * (ENNReal.ofReal r)^u * ncover := by
  rw [h_ncover_eq]
  have h_pos1 : 0 ≤ r^u := Real.rpow_nonneg h_posr u
  have h_poscard : 0 ≤ (card : ℝ) := Nat.cast_nonneg _
  have h_pos2 : 0 ≤ r^u * (card : ℝ) := mul_nonneg h_pos1 h_poscard
  set a : ℝ := 10000 * C with ha
  set b : ℝ := r^u with hb
  set c : ℝ := (card : ℝ) with hc
  have ha_nonneg : 0 ≤ a := h_posC
  have hb_nonneg : 0 ≤ b := h_pos1
  have hc_nonneg : 0 ≤ c := h_poscard
  have h_assoc : a * b * c = a * (b * c) := by ring
  have h_eq1 : ENNReal.ofReal (a * b * c) =
      ENNReal.ofReal a * ENNReal.ofReal (b * c) := by
    rw [h_assoc]
    exact ENNReal.ofReal_mul ha_nonneg
  have h_eq2 : ENNReal.ofReal (b * c) =
      ENNReal.ofReal b * ENNReal.ofReal c :=
    ENNReal.ofReal_mul hb_nonneg
  have h_eq3 : ENNReal.ofReal c = (↑card : ENNReal) := by
    simp [hc] <;> norm_cast
  have h_rpow : (ENNReal.ofReal r)^u = ENNReal.ofReal b := by
    rw [hb]
    exact ENNReal.ofReal_rpow_of_nonneg h_posr h_posu
  have h_main_eq : ENNReal.ofReal (a * b * c) =
      ENNReal.ofReal a * ENNReal.ofReal b * (↑card : ENNReal) := by
    calc ENNReal.ofReal (a * b * c)
      = ENNReal.ofReal a * ENNReal.ofReal (b * c) := h_eq1
    _ = ENNReal.ofReal a * (ENNReal.ofReal b * ENNReal.ofReal c) := by rw [h_eq2]
    _ = ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c := by rw [mul_assoc]
    _ = ENNReal.ofReal a * ENNReal.ofReal b * (↑card : ENNReal) := by rw [h_eq3]
  calc ENNReal.ofReal (25 * (r / δ)^u)
    ≤ ENNReal.ofReal (a * b * c) := ENNReal.ofReal_le_ofReal h10
  _ = ENNReal.ofReal a * ENNReal.ofReal b * (↑card : ENNReal) := h_main_eq
  _ = ENNReal.ofReal a * (ENNReal.ofReal r)^u * (↑card : ENNReal) := by rw [h_rpow]

/-- Helper: 1 ≤ ENNReal.ofReal(10000*C) * (ENNReal.ofReal r)^u when C ≥ 1/7200 and r > 1. -/
lemma one_le_ennreal_mul_rpow (C r u : ℝ) (hC_pos : 0 < C) (h_C_lower : C ≥ 1 / 7200)
    (h_r_gt_one : 1 < r) (h_posu : 0 ≤ u) :
    (1 : ENNReal) ≤ ENNReal.ofReal (10000 * C) * (ENNReal.ofReal r)^u := by
  have h4 : 1 ≤ 10000 * C := by
    have h5 : (10000 : ℝ) * (1 / 7200 : ℝ) ≥ 1 := by norm_num
    have h6 : (10000 : ℝ) * C ≥ (10000 : ℝ) * (1 / 7200 : ℝ) := by gcongr
    linarith
  have hA : (1 : ENNReal) ≤ ENNReal.ofReal (10000 * C) := by
    have hA1 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (10000 * C) := ENNReal.ofReal_le_ofReal h4
    simpa using hA1
  have h_posr : 0 ≤ r := by linarith
  have hB1 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
    have hB1' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal (by linarith)
    simpa using hB1'
  have hB : (1 : ENNReal) ≤ (ENNReal.ofReal r)^u := by
    have h : (1 : ENNReal)^u ≤ (ENNReal.ofReal r)^u := ENNReal.rpow_le_rpow hB1 h_posu
    have h3 : (1 : ENNReal)^u = (1 : ENNReal) := by simp
    rw [h3] at h
    exact h
  calc (1 : ENNReal)
    = (1 : ENNReal) * (1 : ENNReal) := by simp
  _ ≤ ENNReal.ofReal (10000 * C) * (ENNReal.ofReal r)^u := by gcongr

/-- Obligation 1: Ball count via level-j ancestors.

Given a capacity-respecting subset and representative points, a ball of radius r
(δ ≤ r ≤ 1) contains at most 25 * (r/δ)^u selected points. -/
lemma level_j_ball_count {n : ℕ} {u δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_eq : δ = dyadicDelta n)
    (hu_pos : 0 < u)
    {Pbar_sq Pbar_sq_c : Finset (DyadicSquare n)}
    (hPbar_cap : ∀ (j : ℕ) (hj : j ≤ n) (A : DyadicSquare j),
      (leavesInCube j hj A Pbar_sq).card ≤ Nat.floor (dyadicCap n j u))
    (hPbar_sub : Pbar_sq_c ⊆ Pbar_sq)
    (p : DyadicSquare n → EuclideanPlane)
    (h_points_in : ∀ Q ∈ Pbar_sq, p Q ∈ Q.toSet)
    (x : EuclideanPlane) (r : ℝ) (hr : δ ≤ r) (hr_le_one : r ≤ 1) :
    (Pbar_sq_c.filter (fun Q => p Q ∈ Metric.closedBall x r)).card ≤
      25 * (r / δ)^u := by
  have hr' : dyadicDelta n ≤ r := by rw [←hδ_eq]; exact hr
  rcases exists_dyadic_level_for_ball hr' hr_le_one with ⟨j, hj_le_n, hside_le_r, hr_le_2side⟩
  rcases ball_intersects_dyadic_squares_25 (by linarith) hside_le_r hr_le_2side with
    ⟨I, hI_card, hI_cover⟩
  let S : Finset (DyadicSquare n) :=
    Pbar_sq_c.filter (fun Q => p Q ∈ Metric.closedBall x r)
  have h_ancestor_in_I : ∀ Q' ∈ S, dyadicAncestor j hj_le_n Q' ∈ I := by
    intro Q' hQ'
    have hQ'_in_c : Q' ∈ Pbar_sq_c := (Finset.mem_filter.mp hQ').1
    have hQ'_in : Q' ∈ Pbar_sq := hPbar_sub hQ'_in_c
    have hp_in_ball : p Q' ∈ Metric.closedBall x r := (Finset.mem_filter.mp hQ').2
    have hpQ_in_square : p Q' ∈ Q'.toSet := h_points_in Q' hQ'_in
    let A := dyadicAncestor j hj_le_n Q'
    have h_subset : Q'.toSet ⊆ A.toSet :=
      dyadicAncestor_toSet_subset (n - j) j hj_le_n (by omega) Q' A rfl
    have h_inter : (A.toSet ∩ Metric.closedBall x r).Nonempty :=
      ⟨p Q', h_subset hpQ_in_square, hp_in_ball⟩
    exact hI_cover A h_inter
  have hS_sub : S ⊆ I.biUnion (fun A : DyadicSquare j => leavesInCube j hj_le_n A Pbar_sq_c) := by
    intro Q' hQ'
    let A := dyadicAncestor j hj_le_n Q'
    have hA_in_I : A ∈ I := h_ancestor_in_I Q' hQ'
    have hQ'_in_leaves : Q' ∈ leavesInCube j hj_le_n A Pbar_sq_c := by
      simpa [leavesInCube, Finset.mem_filter] using ⟨(Finset.mem_filter.mp hQ').1, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨A, hA_in_I, hQ'_in_leaves⟩
  have h_sum : S.card ≤ ∑ A ∈ I, (leavesInCube j hj_le_n A Pbar_sq_c).card := by
    calc S.card
        ≤ (I.biUnion (fun A => leavesInCube j hj_le_n A Pbar_sq_c)).card :=
          Finset.card_le_card hS_sub
      _ ≤ ∑ A ∈ I, (leavesInCube j hj_le_n A Pbar_sq_c).card :=
        Finset.card_biUnion_le
  have h_cap : ∀ A ∈ I, (leavesInCube j hj_le_n A Pbar_sq_c).card ≤ (dyadicCap n j u : ℝ) := by
    intro A _
    have h_sub2 : leavesInCube j hj_le_n A Pbar_sq_c ⊆ leavesInCube j hj_le_n A Pbar_sq := by
      intro Q hQ
      have hQ_c : Q ∈ Pbar_sq_c := (Finset.mem_filter.mp hQ).1
      have hQ_sq : Q ∈ Pbar_sq := hPbar_sub hQ_c
      have hQ_anc : dyadicAncestor j hj_le_n Q = A := (Finset.mem_filter.mp hQ).2
      exact Finset.mem_filter.mpr ⟨hQ_sq, hQ_anc⟩
    have h1 : (leavesInCube j hj_le_n A Pbar_sq_c).card ≤
        (leavesInCube j hj_le_n A Pbar_sq).card := Finset.card_le_card h_sub2
    have h2 : (leavesInCube j hj_le_n A Pbar_sq).card ≤ Nat.floor (dyadicCap n j u) :=
      hPbar_cap j hj_le_n A
    have h3 : (Nat.floor (dyadicCap n j u) : ℝ) ≤ dyadicCap n j u :=
      nat_floor_le_dyadicCap n j u
    have h4 : ((leavesInCube j hj_le_n A Pbar_sq_c).card : ℝ) ≤ (Nat.floor (dyadicCap n j u) : ℝ) := by
      exact_mod_cast le_trans h1 h2
    exact le_trans h4 h3
  have h_ball_bound : (S.card : ℝ) ≤ 25 * (r / δ)^u := by
    calc (S.card : ℝ)
        ≤ ∑ A ∈ I, ((leavesInCube j hj_le_n A Pbar_sq_c).card : ℝ) := by exact_mod_cast h_sum
      _ ≤ ∑ A ∈ I, (dyadicCap n j u : ℝ) := Finset.sum_le_sum h_cap
      _ = (I.card : ℝ) * (dyadicCap n j u : ℝ) := by rw [Finset.sum_const] <;> ring
      _ ≤ 25 * (dyadicCap n j u : ℝ) := by
        have h4 : (I.card : ℝ) ≤ 25 := by exact_mod_cast hI_card
        have h_nonneg2 : 0 ≤ dyadicCap n j u := dyadicCap_nonneg n j u
        exact mul_le_mul_of_nonneg_right h4 h_nonneg2
      _ = 25 * ((dyadicDelta j) / δ)^u := by
        have h5 : dyadicCap n j u = ((dyadicDelta j) / δ)^u := by
          simpa [dyadicCap, hδ_eq] using rfl
        rw [h5]
      _ ≤ 25 * (r / δ)^u := by
        have h6 : (dyadicDelta j) / δ ≤ r / δ := by gcongr
        have h7 : 0 < (dyadicDelta j) / δ := div_pos (dyadicDelta_pos j) hδ_pos
        gcongr
  exact h_ball_bound

/-- Obligation 2: Strict >2δ separation and Ncover equality from mod-3 coloring.

Given a monochromatic color class Pbar_sq_c with representative points p,
all pairs of distinct image points are strictly >2δ separated, and the
δ-covering number equals the cardinality. -/
lemma strict_separation_ncover {n : ℕ} {δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_eq : δ = dyadicDelta n)
    {Pbar_sq_c : Finset (DyadicSquare n)}
    (p : DyadicSquare n → EuclideanPlane)
    (h_points_in : ∀ Q ∈ Pbar_sq_c, p Q ∈ Q.toSet)
    (h_inj : Set.InjOn p (Pbar_sq_c : Set (DyadicSquare n)))
    (h_same_color : ∀ Q1 ∈ Pbar_sq_c, ∀ Q2 ∈ Pbar_sq_c, colorOf Q1 = colorOf Q2) :
    (∀ (p1 : EuclideanPlane), p1 ∈ (Pbar_sq_c.image p : Set EuclideanPlane) →
      ∀ (p2 : EuclideanPlane), p2 ∈ (Pbar_sq_c.image p : Set EuclideanPlane) →
        p1 ≠ p2 → 2 * δ < dist p1 p2) ∧
    Metric.externalCoveringNumber δ.toNNReal (Pbar_sq_c.image p : Set EuclideanPlane) =
      ↑(Pbar_sq_c.image p).card := by
  have h_sep : ∀ (p1 : EuclideanPlane), p1 ∈ (Pbar_sq_c.image p : Set EuclideanPlane) →
      ∀ (p2 : EuclideanPlane), p2 ∈ (Pbar_sq_c.image p : Set EuclideanPlane) →
        p1 ≠ p2 → 2 * δ < dist p1 p2 := by
    intro p1 hp1 p2 hp2 hne
    rcases Finset.mem_image.mp hp1 with ⟨Q1, hQ1, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨Q2, hQ2, rfl⟩
    have hQ1_ne_Q2 : Q1 ≠ Q2 := by
      intro h; rw [h] at hne; exact hne rfl
    have hcolor_eq : colorOf Q1 = colorOf Q2 := h_same_color Q1 hQ1 Q2 hQ2
    have hdiv := color_eq_implies_div3 hcolor_eq
    have h_strict : 2 * dyadicDelta n < dist (p Q1) (p Q2) :=
      mod3_color_separation_corrected (le_of_eq hδ_eq) hQ1_ne_Q2 hdiv.1 hdiv.2
        (h_points_in Q1 hQ1) (h_points_in Q2 hQ2)
    have h_goal : 2 * δ < dist (p Q1) (p Q2) := by
      have h_eq : 2 * δ = 2 * dyadicDelta n := by rw [hδ_eq]
      rw [h_eq]
      exact h_strict
    exact h_goal
  have h_ncover : Metric.externalCoveringNumber δ.toNNReal (Pbar_sq_c.image p : Set EuclideanPlane) =
      ↑(Pbar_sq_c.image p).card :=
    ncover_eq_card_of_twoδ_separated hδ_pos h_sep
  exact ⟨h_sep, h_ncover⟩

/-- Obligation 3: Mass lower bound, nonemptiness, and cardinality upper bound.

Uses the maximality certificate, leaf specification, and root condition
to construct the half-cap cover and derive the mass lower bound. -/
lemma mass_and_cardinality_bounds {n : ℕ} {u C δ : ℝ}
    {P : Set EuclideanPlane}
    {leaves Pbar_sq Pbar_sq_c : Finset (DyadicSquare n)}
    (hP : IsDeltaSSet δ u C P)
    (hP_bounded : Bornology.IsBounded P)
    (hP_subset : P ⊆ Metric.closedBall 0 1)
    (hδ_pos : 0 < δ) (hδ_eq : δ = dyadicDelta n) (hδ_le_one : δ ≤ 1)
    (hu_pos : 0 < u) (hu_lt_two : u ≤ 2) (hC_pos : 0 < C)
    (hPbar_sub : Pbar_sq ⊆ leaves)
    (hPbar_cap : CapacityRespecting n u Pbar_sq)
    (hPbar_max : ∀ (p : DyadicSquare n), p ∈ leaves → p ∉ Pbar_sq →
      ∃ (j : ℕ) (hjn : j ≤ n) (Q : DyadicSquare j),
        dyadicAncestor j hjn p = Q ∧
          (leavesInCube j hjn Q Pbar_sq).card = Nat.floor (dyadicCap n j u))
    (h_root : ∀ (L : DyadicSquare n), L ∈ leaves →
      dyadicAncestor 0 (by linarith) L ∈ rootSquares)
    (h_leaves_spec : ∀ Q ∈ leaves, (Q.toSet ∩ P).Nonempty)
    (hP_cover : P ⊆ ⋃ L ∈ (leaves : Set (DyadicSquare n)), L.toSet)
    (hPbar_lower9 : Pbar_sq_c.card * 9 ≥ Pbar_sq.card)
    (hPbar_c_sub : Pbar_sq_c ⊆ Pbar_sq) :
    (Pbar_sq.card : ℝ) ≥ (1 / (8 * C)) * δ^(-u) ∧
    0 < Pbar_sq_c.card ∧
    (Pbar_sq_c.card : ℝ) ≤ 100 * δ^(-u) := by
  let cover : Finset SomeDyadicSquare := halfCapCover u Pbar_sq
  let Qfun : SomeDyadicSquare → Set EuclideanPlane := fun i => i.square.toSet

  have hcover : P ⊆ ⋃ i ∈ (cover : Set SomeDyadicSquare), Qfun i := by
    intro x hx
    have h_x_in_leaves : x ∈ ⋃ L ∈ (leaves : Set (DyadicSquare n)), L.toSet := hP_cover hx
    rcases Set.mem_iUnion₂.mp h_x_in_leaves with ⟨L, hL_in_leaves, hxL⟩
    have h_main := halfCapCover_covers_all hu_pos hPbar_sub hPbar_cap hPbar_max h_root L hL_in_leaves
    rcases h_main with ⟨Q, hQ_in, hlev, hQ_anc⟩
    have h_sub : L.toSet ⊆ Q.square.toSet :=
      dyadicAncestor_toSet_subset (n - Q.level) Q.level hlev (by omega) L Q.square hQ_anc
    exact Set.mem_iUnion₂.mpr ⟨Q, hQ_in, h_sub hxL⟩

  have h_half_cap : ∀ (Q : SomeDyadicSquare), Q ∈ cover →
      ∃ (h : Q.level ≤ n), ((leavesInCube Q.level h Q.square Pbar_sq).card : ℝ) ≥
        (dyadicCap n Q.level u) / 2 := by
    intro Q hQ
    exact halfCapCover_halfCap Q hQ

  let S : SomeDyadicSquare → Finset (DyadicSquare n) := fun Q =>
    if hQ : Q ∈ cover then
      leavesInCube Q.level ((h_half_cap Q hQ).choose) Q.square Pbar_sq
    else ∅

  have hS_def : ∀ (Q : SomeDyadicSquare), ∀ hQ : Q ∈ cover,
      S Q = leavesInCube Q.level ((h_half_cap Q hQ).choose) Q.square Pbar_sq := by
    intro Q hQ
    simp [S, hQ]

  have hS_half_cap : ∀ Q ∈ cover, ((S Q).card : ℝ) ≥ (dyadicCap n Q.level u) / 2 := by
    intro Q hQ
    rcases h_half_cap Q hQ with ⟨hlev, hcap⟩
    have h_eq : S Q = leavesInCube Q.level hlev Q.square Pbar_sq := by
      rw [hS_def Q hQ] <;> rfl
    rw [h_eq]
    exact hcap

  have h_disj : ∀ (Q1 : SomeDyadicSquare), Q1 ∈ cover →
      ∀ (Q2 : SomeDyadicSquare), Q2 ∈ cover → Q1 ≠ Q2 →
        Disjoint (Q1.square.toSet) (Q2.square.toSet) :=
    halfCapCover_disjoint

  have hS_disj : ∀ Q1 ∈ cover, ∀ Q2 ∈ cover, Q1 ≠ Q2 → Disjoint (S Q1) (S Q2) := by
    intro Q1 hQ1 Q2 hQ2 hne
    rw [Finset.disjoint_left]
    intro L hL1 hL2
    have hS1 : S Q1 = leavesInCube Q1.level ((h_half_cap Q1 hQ1).choose) Q1.square Pbar_sq := hS_def Q1 hQ1
    have hS2 : S Q2 = leavesInCube Q2.level ((h_half_cap Q2 hQ2).choose) Q2.square Pbar_sq := hS_def Q2 hQ2
    rw [hS1] at hL1
    rw [hS2] at hL2
    have h_anc1 : dyadicAncestor Q1.level _ L = Q1.square := (Finset.mem_filter.mp hL1).2
    have h_anc2 : dyadicAncestor Q2.level _ L = Q2.square := (Finset.mem_filter.mp hL2).2
    have h_sub1 : L.toSet ⊆ Q1.square.toSet :=
      dyadicAncestor_toSet_subset (n - Q1.level) Q1.level _ (by omega) L Q1.square h_anc1
    have h_sub2 : L.toSet ⊆ Q2.square.toSet :=
      dyadicAncestor_toSet_subset (n - Q2.level) Q2.level _ (by omega) L Q2.square h_anc2
    have h_nonempty : L.toSet.Nonempty := by exact DyadicSquare.toSet_nonempty L
    have h_inter : (Q1.square.toSet ∩ Q2.square.toSet).Nonempty :=
      h_nonempty.mono (fun x hx => ⟨h_sub1 hx, h_sub2 hx⟩)
    have h_disj' : Disjoint (Q1.square.toSet) (Q2.square.toSet) := h_disj Q1 hQ1 Q2 hQ2 hne
    have h_empty : Q1.square.toSet ∩ Q2.square.toSet = ∅ := h_disj'.inter_eq
    rw [h_empty] at h_inter
    exact Set.not_nonempty_empty h_inter

  have h_sum_card : ∑ Q ∈ cover, (S Q).card ≤ Pbar_sq.card := by
    have h_union : (cover.biUnion S) ⊆ Pbar_sq := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨Q, hQ, hxQ⟩
      rw [hS_def Q hQ] at hxQ
      exact Finset.filter_subset _ _ hxQ
    have h_disj' : Set.PairwiseDisjoint (cover : Set SomeDyadicSquare) S := by
      intro Q1 hQ1 Q2 hQ2 hne
      exact hS_disj Q1 hQ1 Q2 hQ2 hne
    have h_card : (cover.biUnion S).card = ∑ Q ∈ cover, (S Q).card :=
      Finset.card_biUnion h_disj'
    rw [←h_card]
    exact Finset.card_le_card h_union

  have h_half_cap_sum : (Pbar_sq.card : ℝ) ≥ (1 / 2 : ℝ) * δ^(-u) * ∑ Q ∈ cover, (Q.side)^u := by
    have h1 : ∑ Q ∈ cover, ((S Q).card : ℝ) ≥ (1 / 2 : ℝ) * ∑ Q ∈ cover, (dyadicCap n Q.level u) := by
      have h2 : ∀ Q ∈ cover, ((S Q).card : ℝ) ≥ (dyadicCap n Q.level u) / 2 := hS_half_cap
      have h3 : ∑ Q ∈ cover, ((S Q).card : ℝ) ≥ ∑ Q ∈ cover, ((dyadicCap n Q.level u) / 2) :=
        Finset.sum_le_sum h2
      have h4 : ∑ Q ∈ cover, ((dyadicCap n Q.level u) / 2) = (1 / 2 : ℝ) * ∑ Q ∈ cover, (dyadicCap n Q.level u) := by
        rw [Finset.mul_sum] <;> ring_nf
      rw [h4] at h3
      exact h3
    have h5 : ∀ Q ∈ cover, dyadicCap n Q.level u = (Q.side / δ)^u := by
      intro Q _
      have h1 : dyadicCap n Q.level u = (dyadicDelta Q.level / dyadicDelta n)^u := by rfl
      have h2 : dyadicDelta n = δ := hδ_eq.symm
      rw [h1, h2]
      have h4 : Q.side = dyadicDelta Q.level := by simp [SomeDyadicSquare.side]
      rw [h4]
    have h6 : ∑ Q ∈ cover, (dyadicCap n Q.level u) = ∑ Q ∈ cover, ((Q.side / δ)^u) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact h5 Q hQ
    rw [h6] at h1
    have h7 : ∑ Q ∈ cover, ((Q.side / δ)^u) = δ^(-u) * ∑ Q ∈ cover, (Q.side)^u := by
      have h8 : ∀ Q ∈ cover, (Q.side / δ)^u = δ^(-u) * (Q.side)^u := by
        intro Q _
        have h10 : 0 ≤ Q.side := by
          have h11 : Q.side = dyadicDelta Q.level := by simp [SomeDyadicSquare.side]
          rw [h11]
          exact (dyadicDelta_pos Q.level).le
        have h14 : (Q.side / δ)^u = (Q.side)^u * (δ⁻¹)^u := by
          have h15 : Q.side / δ = Q.side * δ⁻¹ := by ring
          rw [h15, Real.mul_rpow h10 (by positivity)]
        have h16 : (δ⁻¹)^u = δ^(-u) := by
          have h17 : (δ⁻¹)^u = (δ^u)⁻¹ := Real.inv_rpow hδ_pos.le u
          have h18 : δ^(-u) = (δ^u)⁻¹ := Real.rpow_neg hδ_pos.le u
          rw [h17, ←h18]
        rw [h14, h16] <;> ring
      rw [Finset.sum_congr rfl h8, Finset.mul_sum] <;> ring
    rw [h7] at h1
    have h9 : (Pbar_sq.card : ℝ) ≥ ∑ Q ∈ cover, ((S Q).card : ℝ) := by
      exact_mod_cast h_sum_card
    linarith

  have hQ_in_ball : ∀ (Q : SomeDyadicSquare), Q ∈ cover →
      ∃ (c : EuclideanPlane), Q.square.toSet ⊆ Metric.closedBall c (2 * Q.side) := by
    intro Q _
    have h_nonempty : Q.square.toSet.Nonempty := by exact DyadicSquare.toSet_nonempty Q.square
    let c : EuclideanPlane := h_nonempty.some
    have hc : c ∈ Q.square.toSet := h_nonempty.some_mem
    refine' ⟨c, _⟩
    intro x hx
    have h1 : |x 0 - c 0| ≤ Q.side := by
      have hxi1 : (Q.square.i : ℝ) * Q.side ≤ x 0 := hx.1
      have hxi2 : x 0 < ((Q.square.i : ℝ) + 1) * Q.side := hx.2.1
      have hci1 : (Q.square.i : ℝ) * Q.side ≤ c 0 := hc.1
      have hci2 : c 0 < ((Q.square.i : ℝ) + 1) * Q.side := hc.2.1
      rw [abs_le] <;> constructor <;> linarith
    have h2 : |x 1 - c 1| ≤ Q.side := by
      have hxi1 : (Q.square.j : ℝ) * Q.side ≤ x 1 := hx.2.2.1
      have hxi2 : x 1 < ((Q.square.j : ℝ) + 1) * Q.side := hx.2.2.2
      have hci1 : (Q.square.j : ℝ) * Q.side ≤ c 1 := hc.2.2.1
      have hci2 : c 1 < ((Q.square.j : ℝ) + 1) * Q.side := hc.2.2.2
      rw [abs_le] <;> constructor <;> linarith
    have h3 : dist x c ≤ |x 0 - c 0| + |x 1 - c 1| := by
      have h5 : ‖x - c‖ ^ 2 = (x 0 - c 0)^2 + (x 1 - c 1)^2 := by
        have h51 : ‖x - c‖ = Real.sqrt (∑ i : Fin 2, ((x - c) i)^2) := by
          rw [EuclideanSpace.norm_eq]
          apply congr_arg Real.sqrt
          apply Finset.sum_congr rfl
          intro i _
          have h_abs : ‖(x - c) i‖ = |(x - c) i| := by simp
          rw [h_abs, sq_abs]
          <;> ring
        rw [h51]
        have h52 : 0 ≤ ∑ i : Fin 2, ((x - c) i)^2 := by positivity
        rw [Real.sq_sqrt h52]
        simp [Fin.sum_univ_two] <;> ring
      have h4 : ‖x - c‖ ^ 2 ≤ (|x 0 - c 0| + |x 1 - c 1|) ^ 2 := by
        rw [h5]
        have hsq1 : (x 0 - c 0)^2 = |x 0 - c 0|^2 := by rw [sq_abs]
        have hsq2 : (x 1 - c 1)^2 = |x 1 - c 1|^2 := by rw [sq_abs]
        rw [hsq1, hsq2]
        nlinarith [abs_nonneg (x 0 - c 0), abs_nonneg (x 1 - c 1)]
      have h8 : 0 ≤ ‖x - c‖ := by positivity
      have h9 : 0 ≤ |x 0 - c 0| + |x 1 - c 1| := by positivity
      have h10 : ‖x - c‖ ≤ |x 0 - c 0| + |x 1 - c 1| := by nlinarith
      simpa [dist_eq_norm] using h10
    calc dist x c
        ≤ |x 0 - c 0| + |x 1 - c 1| := h3
      _ ≤ Q.side + Q.side := by linarith
      _ = 2 * Q.side := by ring

  have hside_pos : ∀ Q ∈ cover, 0 < Q.side := by
    intro Q _
    have h : Q.side = dyadicDelta Q.level := by simp [SomeDyadicSquare.side]
    rw [h]
    exact dyadicDelta_pos Q.level

  have hside_ge_halfδ : ∀ Q ∈ cover, δ / 2 ≤ Q.side := by
    intro Q hQ
    have h_leaf : Q.level ≤ n := (h_half_cap Q hQ).choose
    have h : Q.side = dyadicDelta Q.level := by simp [SomeDyadicSquare.side]
    rw [h]
    have h4 : dyadicDelta Q.level ≥ dyadicDelta n := dyadicDelta_antitone h_leaf
    have h5 : dyadicDelta n = δ := hδ_eq.symm
    rw [h5] at h4
    linarith

  have h_mass : (Pbar_sq.card : ℝ) ≥ (1 / (8 * C)) * δ^(-u) :=
    mass_lower_bound_half_cap hP hP_bounded hδ_pos hδ_le_one hu_pos hu_lt_two
      hδ_pos (by linarith)
      cover Qfun (fun Q => Q.side)
      hcover hside_pos hside_ge_halfδ hQ_in_ball
      (Pbar_sq.card : ℝ) (by positivity) h_half_cap_sum

  have h_root_cap : ∀ R ∈ rootSquares, (leavesInCube 0 (by linarith) R Pbar_sq).card ≤ Nat.floor (dyadicCap n 0 u) :=
    fun R _ => hPbar_cap 0 (by linarith) R
  have h_card1 : Pbar_sq.card ≤ ∑ R ∈ rootSquares, (leavesInCube 0 (by linarith) R Pbar_sq).card := by
    have h2 : Pbar_sq ⊆ rootSquares.biUnion (fun R => leavesInCube 0 (by linarith) R Pbar_sq) := by
      intro L hL
      have hL_in_leaves : L ∈ leaves := hPbar_sub hL
      have hR_in : dyadicAncestor 0 (by linarith) L ∈ rootSquares := h_root L hL_in_leaves
      let R := dyadicAncestor 0 (by linarith) L
      have hR_in' : R ∈ rootSquares := hR_in
      have hL_in_cube : L ∈ leavesInCube 0 (by linarith) R Pbar_sq := by
        simpa [leavesInCube, Finset.mem_filter] using ⟨hL, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨R, hR_in', hL_in_cube⟩
    calc Pbar_sq.card
        ≤ (rootSquares.biUnion (fun R => leavesInCube 0 (by linarith) R Pbar_sq)).card :=
          Finset.card_le_card h2
      _ ≤ ∑ R ∈ rootSquares, (leavesInCube 0 (by linarith) R Pbar_sq).card :=
        Finset.card_biUnion_le
  have h_root9 : rootSquares.card = 9 := by
    rw [rootSquares]
    have h_disj : Set.PairwiseDisjoint (Finset.Icc (-1 : ℤ) 1 : Set ℤ)
        (fun i : ℤ => (Finset.Icc (-1 : ℤ) 1).image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare 0))) := by
      intro i1 _ i2 _ hne
      have h : ∀ (x : DyadicSquare 0), x ∈ (Finset.Icc (-1 : ℤ) 1).image (fun j : ℤ => (⟨i1, j⟩ : DyadicSquare 0)) →
          x ∉ (Finset.Icc (-1 : ℤ) 1).image (fun j : ℤ => (⟨i2, j⟩ : DyadicSquare 0)) := by
        intro x hx1 hx2
        rcases Finset.mem_image.mp hx1 with ⟨j1, _, h_eq1⟩
        rcases Finset.mem_image.mp hx2 with ⟨j2, _, h_eq2⟩
        have h_i1 : x.i = i1 := (congr_arg (fun y : DyadicSquare 0 => y.i) h_eq1).symm
        have h_i2 : x.i = i2 := (congr_arg (fun y : DyadicSquare 0 => y.i) h_eq2).symm
        have h_eq : i1 = i2 := by linarith
        exact hne h_eq
      exact Finset.disjoint_left.mpr h
    rw [Finset.card_biUnion h_disj]
    have h_img : ∀ i ∈ (Finset.Icc (-1 : ℤ) 1),
        ((Finset.Icc (-1 : ℤ) 1).image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare 0))).card = 3 := by
      intro i _
      rw [Finset.card_image_of_injective]
      · simp
      · intro j1 j2 h
        injection h
    rw [Finset.sum_congr rfl h_img]
    simp [Finset.sum_const] <;> norm_num
  have h_floor_le : (Nat.floor (dyadicCap n 0 u) : ℝ) ≤ dyadicCap n 0 u :=
    Nat.floor_le (dyadicCap_nonneg n 0 u)
  have h_cap0_eq : dyadicCap n 0 u = δ^(-u) := by
    have h1 : dyadicCap n 0 u = (dyadicDelta 0 / dyadicDelta n)^u := by rfl
    rw [h1]
    have h2 : dyadicDelta 0 = 1 := by simp [dyadicDelta]
    have h3 : dyadicDelta n = δ := hδ_eq.symm
    rw [h2, h3]
    have h4 : (1 / δ)^u = δ^(-u) := by
      have h5 : (1 / δ) = δ⁻¹ := by ring
      rw [h5]
      have h6 : (δ⁻¹)^u = (δ^u)⁻¹ := Real.inv_rpow hδ_pos.le u
      have h7 : δ^(-u) = (δ^u)⁻¹ := Real.rpow_neg hδ_pos.le u
      exact h6.trans h7.symm
    exact h4
  have hPbar_sq_upper9 : (Pbar_sq.card : ℝ) ≤ 9 * δ^(-u) := by
    calc (Pbar_sq.card : ℝ)
        ≤ ∑ R ∈ rootSquares, ((leavesInCube 0 (by linarith) R Pbar_sq).card : ℝ) := by
          exact_mod_cast h_card1
      _ ≤ ∑ R ∈ rootSquares, (Nat.floor (dyadicCap n 0 u) : ℝ) := by
        apply Finset.sum_le_sum
        intro R _
        exact_mod_cast h_root_cap R ‹_›
      _ = (rootSquares.card : ℝ) * (Nat.floor (dyadicCap n 0 u) : ℝ) := by
        rw [Finset.sum_const] <;> simp [h_root9] <;> ring
      _ ≤ 9 * dyadicCap n 0 u := by
        rw [h_root9]
        have h_floor' : (Nat.floor (dyadicCap n 0 u) : ℝ) ≤ dyadicCap n 0 u := h_floor_le
        have h : 9 * (Nat.floor (dyadicCap n 0 u) : ℝ) ≤ 9 * dyadicCap n 0 u := by gcongr
        exact h
      _ = 9 * δ^(-u) := by rw [h_cap0_eq]

  have h_card_upper : (Pbar_sq_c.card : ℝ) ≤ 100 * δ^(-u) := by
    have h7 : (Pbar_sq_c.card : ℝ) ≤ (Pbar_sq.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hPbar_c_sub
    calc (Pbar_sq_c.card : ℝ)
        ≤ (Pbar_sq.card : ℝ) := h7
      _ ≤ 9 * δ^(-u) := hPbar_sq_upper9
      _ ≤ 100 * δ^(-u) := by
        have h_pos : 0 < δ^(-u) := by positivity
        gcongr <;> norm_num

  have h_nonempty : 0 < Pbar_sq_c.card := by
    have h_pos1 : 0 < (1 / (8 * C)) * δ^(-u) := by positivity
    have h' : 0 < (Pbar_sq.card : ℝ) := by linarith [h_mass, h_pos1]
    have h9 : (Pbar_sq_c.card : ℝ) * (9 : ℝ) ≥ (Pbar_sq.card : ℝ) := by exact_mod_cast hPbar_lower9
    have h'' : 0 < (Pbar_sq_c.card : ℝ) := by nlinarith
    exact_mod_cast h''

  exact ⟨h_mass, h_nonempty, h_card_upper⟩

/-- Obligation 4: Final IsDeltaSSet assembly and Ncover lower bound.

Given all pieces, assemble the IsDeltaSSet property with constant 10000*C
and the Ncover lower bound. -/
lemma final_isDeltaSSet_and_ncover {n : ℕ} {u C δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_eq : δ = dyadicDelta n)
    (hu_pos : 0 < u) (hu_lt_two : u ≤ 2) (hC_pos : 0 < C)
    {Pbar : Finset EuclideanPlane}
    (hPbar_nonempty : 0 < Pbar.card)
    (h_card_upper : (Pbar.card : ℝ) ≤ 100 * δ^(-u))
    (h_mass_lower : (Pbar.card : ℝ) ≥ (1 / (72 * C)) * δ^(-u))
    (h_ball_count : ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r → r ≤ 1 →
      (Pbar.filter (fun p => p ∈ Metric.closedBall x r)).card ≤ 25 * (r / δ)^u)
    (h_strict_sep : ∀ p ∈ (Pbar : Set EuclideanPlane), ∀ q ∈ (Pbar : Set EuclideanPlane),
      p ≠ q → 2 * δ < dist p q)
    (h_ncover_eq : Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) = ↑(Pbar.card)) :
    IsDeltaSSet δ u (10000 * C) (Pbar : Set EuclideanPlane) ∧
    Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) ≥
      ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * δ^(-u)) := by
  have hPbar_nonempty' : (Pbar : Set EuclideanPlane).Nonempty := by
    have h1 : 0 < Pbar.card := hPbar_nonempty
    exact Finset.card_pos.mp h1

  have h_C_lower : C ≥ 1 / 7200 := by
    have h_pos : 0 < δ^(-u) := by positivity
    have h6 : (1 / (72 * C)) * δ^(-u) ≤ 100 * δ^(-u) := by
      linarith [h_mass_lower, h_card_upper]
    have h7 : 1 / (72 * C) ≤ 100 := by
      calc 1 / (72 * C)
        = ((1 / (72 * C)) * δ^(-u)) / δ^(-u) := by field_simp [h_pos.ne'] <;> ring
      _ ≤ (100 * δ^(-u)) / δ^(-u) := by gcongr
      _ = 100 := by field_simp [h_pos.ne'] <;> ring
    have h9 : 0 < C := hC_pos
    calc C
      = 1 / (72 * (1 / (72 * C))) := by field_simp [h9.ne'] <;> ring
    _ ≥ 1 / (72 * 100) := by gcongr
    _ = 1 / 7200 := by norm_num

  have h4 : 1 ≤ 10000 * C := by
    have h5 : C ≥ 1 / 7200 := h_C_lower
    nlinarith

  have h_sset : IsDeltaSSet δ u (10000 * C) (Pbar : Set EuclideanPlane) := by
    refine' ⟨hPbar_nonempty', hδ_pos, by positivity, by linarith, _⟩
    intro x r hr
    by_cases h_r_le_one : r ≤ 1
    · -- Case r ≤ 1
      have h_ball_bound' : (Pbar.filter (fun p => p ∈ Metric.closedBall x r)).card ≤ 25 * (r / δ)^u :=
        h_ball_count x r hr h_r_le_one
      have h_set_eq : (Pbar : Set EuclideanPlane) ∩ Metric.closedBall x r =
          ↑(Pbar.filter (fun p => p ∈ Metric.closedBall x r)) := by
        ext z; simp [Finset.mem_filter]
      have h_ncover_ball : (Metric.externalCoveringNumber δ.toNNReal ((Pbar : Set EuclideanPlane) ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal ((Pbar.filter (fun p => p ∈ Metric.closedBall x r)).card : ℝ) := by
        rw [h_set_eq]
        let S' := Pbar.filter (fun p => p ∈ Metric.closedBall x r)
        have h1' : Metric.externalCoveringNumber δ.toNNReal (↑S' : Set EuclideanPlane) ≤
            (↑S' : Set EuclideanPlane).encard := Metric.externalCoveringNumber_le_encard_self _
        have h2 : (↑S' : Set EuclideanPlane).encard = ↑(S'.card) := by simp
        have h1 : (Metric.externalCoveringNumber δ.toNNReal (↑S' : Set EuclideanPlane) : ENNReal) ≤ (↑(S'.card) : ENNReal) := by
          exact_mod_cast (le_trans h1' (le_of_eq h2))
        have h3 : (↑(S'.card) : ENNReal) = ENNReal.ofReal ((S'.card : ℝ)) := by simp
        rw [h3] at h1
        exact h1
      have h_main1 : (Metric.externalCoveringNumber δ.toNNReal ((Pbar : Set EuclideanPlane) ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal (25 * (r / δ)^u) := by
        calc (Metric.externalCoveringNumber δ.toNNReal _ : ENNReal)
            ≤ ENNReal.ofReal ((Pbar.filter (fun p => p ∈ Metric.closedBall x r)).card : ℝ) := h_ncover_ball
          _ ≤ ENNReal.ofReal (25 * (r / δ)^u) := by
            apply ENNReal.ofReal_le_ofReal
            exact h_ball_bound'
      have h_r_nonneg : 0 ≤ r := le_trans hδ_pos.le hr
      have h_posu : 0 ≤ u := by linarith
      have h_rdivδ_eq : (r / δ)^u = r^u * δ^(-u) := by
        have h1 : r / δ = r * δ⁻¹ := by ring
        rw [h1]
        have h2 : (r * δ⁻¹)^u = r^u * (δ⁻¹)^u := Real.mul_rpow h_r_nonneg (by positivity)
        rw [h2]
        have h3 : (δ⁻¹)^u = δ^(-u) := by
          have h4 : (δ⁻¹)^u = (δ^u)⁻¹ := Real.inv_rpow hδ_pos.le u
          have h5 : δ^(-u) = (δ^u)⁻¹ := Real.rpow_neg hδ_pos.le u
          exact h4.trans h5.symm
        rw [h3] <;> ring
      have hCinv : C * C⁻¹ = 1 := by
        field_simp [hC_pos.ne'] <;> ring
      have h10 : 25 * (r / δ)^u ≤ (10000 * C) * r^u * (Pbar.card : ℝ) := by
        rw [h_rdivδ_eq]
        calc 25 * (r^u * δ^(-u))
            ≤ (10000 / 72 : ℝ) * (r^u * δ^(-u)) := by
              have h13 : (25 : ℝ) ≤ 10000 / 72 := by norm_num
              have h14 : 0 ≤ r^u * δ^(-u) := by positivity
              exact mul_le_mul_of_nonneg_right h13 h14
        _ = (10000 * C) * r^u * ((1 / (72 * C)) * δ^(-u)) := by
          have h12 : (10000 * C) * (1 / (72 * C)) = (10000 / 72 : ℝ) := by
            field_simp [hC_pos.ne'] <;> ring
          have h : (10000 / 72 : ℝ) * (r^u * δ^(-u)) =
              (10000 * C) * r^u * ((1 / (72 * C)) * δ^(-u)) := by
            have h12' : (10000 / 72 : ℝ) = (10000 * C) * (1 / (72 * C)) := h12.symm
            rw [h12'] <;> ring
          exact h
        _ ≤ (10000 * C) * r^u * (Pbar.card : ℝ) := by
          have h_pos2 : 0 ≤ (10000 * C) * r^u := by positivity
          exact mul_le_mul_of_nonneg_left h_mass_lower h_pos2
      have h_ncover_eq' : (Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) : ENNReal) = (↑(Pbar.card) : ENNReal) := by
        exact_mod_cast h_ncover_eq
      have h_main2 := ball_bound_ennreal_arithmetic δ C r u Pbar.card
        (Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) : ENNReal)
        (by positivity) h_r_nonneg h_posu h10 h_ncover_eq'
      exact le_trans h_main1 h_main2
    · -- Case r > 1
      have h_r_gt_one : 1 < r := by linarith
      have h_sub : (Pbar : Set EuclideanPlane) ∩ Metric.closedBall x r ⊆ (Pbar : Set EuclideanPlane) :=
        Set.inter_subset_left
      have h_mono : Metric.externalCoveringNumber δ.toNNReal ((Pbar : Set EuclideanPlane) ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) :=
        Metric.externalCoveringNumber_mono_set h_sub
      have h1 : (Metric.externalCoveringNumber δ.toNNReal ((Pbar : Set EuclideanPlane) ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) : ENNReal) := by
        exact_mod_cast h_mono
      have h_posu : 0 ≤ u := by linarith
      have h2 : (1 : ENNReal) ≤ ENNReal.ofReal (10000 * C) * (ENNReal.ofReal r)^u :=
        one_le_ennreal_mul_rpow C r u hC_pos h_C_lower h_r_gt_one h_posu
      calc (Metric.externalCoveringNumber δ.toNNReal ((Pbar : Set EuclideanPlane) ∩ Metric.closedBall x r) : ENNReal)
          ≤ (Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) : ENNReal) := h1
        _ = (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) : ENNReal) := by
          simp [mul_one]
        _ ≤ ENNReal.ofReal (10000 * C) * (ENNReal.ofReal r)^u * (Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) : ENNReal) := by
          gcongr

  have h_ncover_lower : (Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) : ENNReal) ≥
      ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * δ^(-u)) := by
    have h_ncover_eq' : (Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) : ENNReal) = (↑(Pbar.card) : ENNReal) := by
      exact_mod_cast h_ncover_eq
    rw [h_ncover_eq']
    have h11 : (↑(Pbar.card) : ENNReal) = ENNReal.ofReal ((Pbar.card : ℝ)) := by simp
    rw [h11]
    have h9 : (Pbar.card : ℝ) ≥ (1 / (72 * C)) * δ^(-u) := h_mass_lower
    have h10 : (1 / (72 * C)) * δ^(-u) ≥ (1 / 10000 : ℝ) * C⁻¹ * δ^(-u) := by
      have h11 : 0 < δ^(-u) := by positivity
      have h12 : (1 / 72 : ℝ) ≥ (1 / 10000 : ℝ) := by norm_num
      have h13 : (1 / (72 * C)) = (1 / 72 : ℝ) * C⁻¹ := by
        field_simp [hC_pos.ne'] <;> ring
      rw [h13]
      gcongr
    have h14 : (Pbar.card : ℝ) ≥ (1 / 10000 : ℝ) * C⁻¹ * δ^(-u) := by
      calc (Pbar.card : ℝ)
          ≥ (1 / (72 * C)) * δ^(-u) := h9
        _ ≥ (1 / 10000 : ℝ) * C⁻¹ * δ^(-u) := h10
    exact ENNReal.ofReal_le_ofReal h14

  exact ⟨h_sset, h_ncover_lower⟩

/-- Core theorem at dyadic scale δ = dyadicDelta n. -/
theorem deltasSet_extraction_dyadic_main {n : ℕ} {u C : ℝ}
    {P : Set EuclideanPlane}
    (hP : IsDeltaSSet (dyadicDelta n) u C P)
    (hP_bounded : Bornology.IsBounded P)
    (hP_subset : P ⊆ Metric.closedBall 0 1)
    (hu_pos : 0 < u) (hu_lt_two : u ≤ 2) :
    ∃ (Pbar : Finset EuclideanPlane),
      (Pbar : Set EuclideanPlane) ⊆ P ∧
      (∀ p ∈ (Pbar : Set EuclideanPlane), ∀ q ∈ (Pbar : Set EuclideanPlane),
        p ≠ q → dyadicDelta n ≤ dist p q) ∧
      IsDeltaSSet (dyadicDelta n) u (10000 * C) (Pbar : Set EuclideanPlane) ∧
      (Pbar.card : ℝ) ≤ 100 * (dyadicDelta n) ^ (-u) ∧
      (Metric.externalCoveringNumber (dyadicDelta n).toNNReal (Pbar : Set EuclideanPlane) : ENNReal) ≥
        ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * (dyadicDelta n) ^ (-u)) := by
  set δ : ℝ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : δ = dyadicDelta n := by rfl
  have hδ_le_one : δ ≤ 1 := by
    have h : ∀ m : ℕ, (1 : ℝ) ≤ (2 : ℝ)^m := by
      intro m; induction m with
      | zero => norm_num
      | succ m ih => simp [pow_succ] at * <;> linarith
    have h_pos : 0 < (2 : ℝ)^n := by positivity
    exact (div_le_one h_pos).mpr (h n)
  have hC_pos : 0 < C := hP.2.2.1

  -- Step 1: Candidate leaf squares
  let allSquares : Finset (DyadicSquare n) :=
    (Finset.Icc (-(2 ^ n + 1 : ℤ)) (2 ^ n + 1 : ℤ)).biUnion fun i =>
    (Finset.Icc (-(2 ^ n + 1 : ℤ)) (2 ^ n + 1 : ℤ)).image fun j => (⟨i, j⟩ : DyadicSquare n)
  let leaves : Finset (DyadicSquare n) :=
    allSquares.filter (fun Q => (Q.toSet ∩ P).Nonempty)
  have h_leaves_spec : ∀ Q ∈ leaves, (Q.toSet ∩ P).Nonempty := by
    intro Q hQ; exact (Finset.mem_filter.mp hQ).2

  -- Step 2: Maximal capacity-respecting subset
  rcases exists_maximal_capacity_respecting leaves hu_pos with ⟨Pbar_sq, hPbar_sub, hPbar_cap, h_max⟩

  -- Root square condition for leaves
  have h_root : ∀ (L : DyadicSquare n), L ∈ leaves →
      dyadicAncestor 0 (by linarith) L ∈ rootSquares := by
    intro L hL
    have h_nonempty : (L.toSet ∩ P).Nonempty := h_leaves_spec L hL
    have h' : (L.toSet ∩ Metric.closedBall (0 : EuclideanPlane) 1).Nonempty := by
      rcases h_nonempty with ⟨x, hxL, hxP⟩
      exact ⟨x, hxL, hP_subset hxP⟩
    exact leaf_meets_unitBall_has_root L h'

  -- Cover: every point of P lies in some leaf square
  have hP_cover : P ⊆ ⋃ L ∈ (leaves : Set (DyadicSquare n)), L.toSet := by
    intro x hx
    have hx_ball : x ∈ Metric.closedBall (0 : EuclideanPlane) 1 := hP_subset hx
    have hx_norm : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hx_ball
    have hx0_abs : |x 0| ≤ 1 := by
      calc |x 0| ≤ ‖x‖ := abs_coord_le_norm x 0
        _ ≤ 1 := hx_norm
    have hx1_abs : |x 1| ≤ 1 := by
      calc |x 1| ≤ ‖x‖ := abs_coord_le_norm x 1
        _ ≤ 1 := hx_norm
    have hx0_bounds : -1 ≤ x 0 ∧ x 0 ≤ 1 := by
      have h := abs_le.mp hx0_abs
      exact ⟨h.1, h.2⟩
    have hx1_bounds : -1 ≤ x 1 ∧ x 1 ≤ 1 := by
      have h := abs_le.mp hx1_abs
      exact ⟨h.1, h.2⟩
    let i : ℤ := Int.floor (x 0 / δ)
    let j : ℤ := Int.floor (x 1 / δ)
    have hi1 : (i : ℝ) ≤ x 0 / δ := Int.floor_le (x 0 / δ)
    have hi2 : x 0 / δ < (i : ℝ) + 1 := Int.lt_floor_add_one (x 0 / δ)
    have hj1 : (j : ℝ) ≤ x 1 / δ := Int.floor_le (x 1 / δ)
    have hj2 : x 1 / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (x 1 / δ)
    have hδ_pos' : 0 < δ := hδ_pos
    have hxi1 : (i : ℝ) * δ ≤ x 0 := by
      calc (i : ℝ) * δ ≤ (x 0 / δ) * δ := by gcongr
        _ = x 0 := by field_simp [hδ_pos'.ne'] <;> ring
    have hxi2 : x 0 < ((i : ℝ) + 1) * δ := by
      calc x 0 = (x 0 / δ) * δ := by field_simp [hδ_pos'.ne'] <;> ring
        _ < ((i : ℝ) + 1) * δ := by gcongr
    have hxj1 : (j : ℝ) * δ ≤ x 1 := by
      calc (j : ℝ) * δ ≤ (x 1 / δ) * δ := by gcongr
        _ = x 1 := by field_simp [hδ_pos'.ne'] <;> ring
    have hxj2 : x 1 < ((j : ℝ) + 1) * δ := by
      calc x 1 = (x 1 / δ) * δ := by field_simp [hδ_pos'.ne'] <;> ring
        _ < ((j : ℝ) + 1) * δ := by gcongr
    let Q : DyadicSquare n := ⟨i, j⟩
    have hxQ : x ∈ Q.toSet := by
      simp only [Q, DyadicSquare.toSet]
      exact ⟨hxi1, hxi2, hxj1, hxj2⟩
    have h_invδ : 1 / δ = (2 ^ n : ℝ) := by
      simp [hδ_def, dyadicDelta] <;> field_simp <;> ring
    have h_neg_invδ : -1 / δ = -(2 ^ n : ℝ) := by
      have h : -1 / δ = -(1 / δ) := by ring
      rw [h, h_invδ]
    have h_i0 : -(2 ^ n : ℝ) ≤ x 0 / δ := by
      have h : -1 ≤ x 0 := hx0_bounds.1
      have h' : x 0 / δ ≥ -1 / δ := by gcongr
      rw [h_neg_invδ] at h'
      exact h'
    have h_i1 : x 0 / δ ≤ (2 ^ n : ℝ) := by
      have h : x 0 ≤ 1 := hx0_bounds.2
      have h' : x 0 / δ ≤ 1 / δ := by gcongr
      rw [h_invδ] at h'
      exact h'
    have h_i_le : (i : ℝ) ≤ (2 ^ n : ℝ) := by linarith
    have h_i_gt : (i : ℝ) > -((2 ^ n : ℝ) + 1) := by linarith
    have h_i_int_le : i ≤ (2 ^ n : ℤ) := by exact_mod_cast h_i_le
    have h_i_int_ge : i ≥ -(2 ^ n : ℤ) := by
      by_contra h
      have h' : i < -(2 ^ n : ℤ) := by omega
      have h2 : i ≤ -(2 ^ n : ℤ) - 1 := by omega
      have h3 : (i : ℝ) ≤ ↑(-(2 ^ n : ℤ) - 1) := by exact_mod_cast h2
      have h4 : (↑(-(2 ^ n : ℤ) - 1) : ℝ) = -((2 ^ n : ℝ) + 1) := by
        simp <;> ring
      rw [h4] at h3
      linarith
    have h_i_range : -(2 ^ n + 1 : ℤ) ≤ i ∧ i ≤ (2 ^ n + 1 : ℤ) := by
      constructor <;> omega
    have h_j0 : -(2 ^ n : ℝ) ≤ x 1 / δ := by
      have h : -1 ≤ x 1 := hx1_bounds.1
      have h' : x 1 / δ ≥ -1 / δ := by gcongr
      rw [h_neg_invδ] at h'
      exact h'
    have h_j1 : x 1 / δ ≤ (2 ^ n : ℝ) := by
      have h : x 1 ≤ 1 := hx1_bounds.2
      have h' : x 1 / δ ≤ 1 / δ := by gcongr
      rw [h_invδ] at h'
      exact h'
    have h_j_le : (j : ℝ) ≤ (2 ^ n : ℝ) := by linarith
    have h_j_gt : (j : ℝ) > -((2 ^ n : ℝ) + 1) := by linarith
    have h_j_int_le : j ≤ (2 ^ n : ℤ) := by exact_mod_cast h_j_le
    have h_j_int_ge : j ≥ -(2 ^ n : ℤ) := by
      by_contra h
      have h' : j < -(2 ^ n : ℤ) := by omega
      have h2 : j ≤ -(2 ^ n : ℤ) - 1 := by omega
      have h3 : (j : ℝ) ≤ ↑(-(2 ^ n : ℤ) - 1) := by exact_mod_cast h2
      have h4 : (↑(-(2 ^ n : ℤ) - 1) : ℝ) = -((2 ^ n : ℝ) + 1) := by
        simp <;> ring
      rw [h4] at h3
      linarith
    have h_j_range : -(2 ^ n + 1 : ℤ) ≤ j ∧ j ≤ (2 ^ n + 1 : ℤ) := by
      constructor <;> omega
    have hQ_in_all : Q ∈ allSquares := by
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_Icc.mpr h_i_range, ?_⟩
      rw [Finset.mem_image]
      refine ⟨j, Finset.mem_Icc.mpr h_j_range, ?_⟩
      simp [Q]
    have hQ_nonempty : (Q.toSet ∩ P).Nonempty := ⟨x, hxQ, hx⟩
    have hQ_in_leaves : Q ∈ leaves := by
      rw [Finset.mem_filter]
      exact ⟨hQ_in_all, hQ_nonempty⟩
    exact Set.mem_iUnion₂.mpr ⟨Q, hQ_in_leaves, hxQ⟩

  -- Step 3: Mod-3 coloring
  rcases exists_large_fiber_9 (S := Pbar_sq) (f := colorOf) with ⟨c, hc⟩
  let Pbar_sq_c : Finset (DyadicSquare n) := Pbar_sq.filter (fun Q => colorOf Q = c)
  have hPbar_lower9 : Pbar_sq_c.card * 9 ≥ Pbar_sq.card := hc

  -- Obligation 3: mass, nonemptiness, card upper
  have h_bounds := mass_and_cardinality_bounds
    hP hP_bounded hP_subset hδ_pos hδ_eq hδ_le_one hu_pos hu_lt_two hC_pos
    (hPbar_sub := hPbar_sub) (hPbar_cap := hPbar_cap) (hPbar_max := h_max)
    (h_root := h_root) (h_leaves_spec := h_leaves_spec) (hP_cover := hP_cover)
    (hPbar_lower9 := hPbar_lower9) (hPbar_c_sub := Finset.filter_subset _ _)
  have h_mass : (Pbar_sq.card : ℝ) ≥ (1 / (8 * C)) * δ^(-u) := h_bounds.1
  have h_nonempty : 0 < Pbar_sq_c.card := h_bounds.2.1
  have h_card_upper_sq : (Pbar_sq_c.card : ℝ) ≤ 100 * δ^(-u) := h_bounds.2.2

  -- Step 4: Representative points
  have h_choose : ∀ (Q : DyadicSquare n), Q ∈ Pbar_sq → ∃ (p : EuclideanPlane), p ∈ Q.toSet ∧ p ∈ P := by
    intro Q hQ
    have hQ_in_leaves : Q ∈ leaves := hPbar_sub hQ
    have h_nonempty : (Q.toSet ∩ P).Nonempty := h_leaves_spec Q hQ_in_leaves
    rcases h_nonempty with ⟨p, hpQ, hpP⟩
    exact ⟨p, hpQ, hpP⟩
  let p : DyadicSquare n → EuclideanPlane := fun Q =>
    if hQ : Q ∈ Pbar_sq then Classical.choose (h_choose Q hQ) else 0
  have h_points_in : ∀ Q ∈ Pbar_sq, p Q ∈ Q.toSet ∧ p Q ∈ P := by
    intro Q hQ
    have hpe : p Q = Classical.choose (h_choose Q hQ) := by simp [p, hQ]
    rw [hpe]; exact Classical.choose_spec (h_choose Q hQ)
  have h_inj : Set.InjOn p (Pbar_sq : Set (DyadicSquare n)) := by
    intro Q1 hQ1 Q2 hQ2 h
    have h1 : p Q1 ∈ Q1.toSet := (h_points_in Q1 hQ1).1
    have h2 : p Q2 ∈ Q2.toSet := (h_points_in Q2 hQ2).1
    rw [h] at h1
    have h3 : (Q1.toSet ∩ Q2.toSet).Nonempty := ⟨p Q2, h1, h2⟩
    by_cases h4 : Q1 = Q2
    · exact h4
    · have h_disj : Disjoint (Q1.toSet) (Q2.toSet) := dyadicSquare_toSet_disjoint h4
      simpa [h_disj.inter_eq] using h3

  let Pbar : Finset EuclideanPlane := Pbar_sq_c.image p
  have hPbar_card : Pbar.card = Pbar_sq_c.card := by
    rw [Finset.card_image_of_injOn]; exact h_inj.mono (Finset.filter_subset _ _)
  have hPbar_subset : (Pbar : Set EuclideanPlane) ⊆ P := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨Q, hQ, rfl⟩
    exact (h_points_in Q (Finset.mem_filter.mp hQ).1).2

  have h_same_color : ∀ Q1 ∈ Pbar_sq_c, ∀ Q2 ∈ Pbar_sq_c, colorOf Q1 = colorOf Q2 := by
    intro Q1 hQ1 Q2 hQ2
    have h1 : colorOf Q1 = c := (Finset.mem_filter.mp hQ1).2
    have h2 : colorOf Q2 = c := (Finset.mem_filter.mp hQ2).2
    rw [h1, h2]

  -- Obligation 2: strict separation + Ncover equality
  have h_sep_ncover := strict_separation_ncover hδ_pos hδ_eq p
    (fun Q hQ => (h_points_in Q (Finset.mem_filter.mp hQ).1).1)
    (h_inj.mono (Finset.filter_subset _ _)) h_same_color
  have h_strict_sep : ∀ p1 ∈ (Pbar : Set EuclideanPlane), ∀ p2 ∈ (Pbar : Set EuclideanPlane),
      p1 ≠ p2 → 2 * δ < dist p1 p2 := h_sep_ncover.1
  have h_ncover_eq : Metric.externalCoveringNumber δ.toNNReal (Pbar : Set EuclideanPlane) =
      ↑(Pbar.card) :=
    h_sep_ncover.2

  -- Obligation 1: ball count
  have h_ball_count : ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r → r ≤ 1 →
      (Pbar.filter (fun p => p ∈ Metric.closedBall x r)).card ≤ 25 * (r / δ)^u := by
    intro x r hr hr_le_one
    have hS_eq : (Pbar_sq_c.filter (fun Q => p Q ∈ Metric.closedBall x r)).image p =
        Pbar.filter (fun p => p ∈ Metric.closedBall x r) := by
      ext z
      simp only [Finset.mem_image, Finset.mem_filter, Pbar]
      constructor
      · rintro ⟨Q, ⟨hQ_in, hQ_ball⟩, rfl⟩
        exact ⟨⟨Q, hQ_in, rfl⟩, hQ_ball⟩
      · rintro ⟨⟨Q, hQ_in, rfl⟩, hQ_ball⟩
        exact ⟨Q, ⟨hQ_in, hQ_ball⟩, rfl⟩
    have h_card : (Pbar.filter (fun p => p ∈ Metric.closedBall x r)).card =
        (Pbar_sq_c.filter (fun Q => p Q ∈ Metric.closedBall x r)).card := by
      rw [←hS_eq, Finset.card_image_of_injOn]
      have h_sub1 : (Pbar_sq_c.filter (fun Q => p Q ∈ Metric.closedBall x r)) ⊆ Pbar_sq_c := Finset.filter_subset _ _
      have h_sub2 : Pbar_sq_c ⊆ Pbar_sq := Finset.filter_subset _ _
      have h_sub3 : (Pbar_sq_c.filter (fun Q => p Q ∈ Metric.closedBall x r)) ⊆ Pbar_sq := Finset.Subset.trans h_sub1 h_sub2
      exact h_inj.mono (Finset.coe_subset.mpr h_sub3)
    rw [h_card]
    exact level_j_ball_count hδ_pos hδ_eq hu_pos hPbar_cap
      (Finset.filter_subset _ _) p (fun Q hQ => (h_points_in Q hQ).1) x r hr hr_le_one

  have hPbar_nonempty : 0 < Pbar.card := by
    rw [hPbar_card]; exact_mod_cast h_nonempty
  have h_card_upper : (Pbar.card : ℝ) ≤ 100 * δ^(-u) := by
    rw [hPbar_card]; exact h_card_upper_sq
  have h_mass_lower : (Pbar.card : ℝ) ≥ (1 / (72 * C)) * δ^(-u) := by
    rw [hPbar_card]
    have h : (Pbar_sq_c.card : ℝ) ≥ (Pbar_sq.card : ℝ) / 9 := by
      have h9' : (Pbar_sq_c.card : ℝ) * 9 ≥ (Pbar_sq.card : ℝ) := by exact_mod_cast hPbar_lower9
      linarith
    calc (Pbar_sq_c.card : ℝ)
      ≥ (Pbar_sq.card : ℝ) / 9 := h
    _ ≥ ((1 / (8 * C)) * δ^(-u)) / 9 := by gcongr
    _ = (1 / (72 * C)) * δ^(-u) := by ring

  -- Obligation 4: final S-set + Ncover lower
  have h_final := final_isDeltaSSet_and_ncover hδ_pos hδ_eq hu_pos hu_lt_two hC_pos
    hPbar_nonempty h_card_upper h_mass_lower h_ball_count h_strict_sep h_ncover_eq
  have h_sset : IsDeltaSSet δ u (10000 * C) (Pbar : Set EuclideanPlane) := h_final.1
  have h_ncover_lower := h_final.2

  -- Weak separation from strict
  have h_weak_sep : ∀ p1 ∈ (Pbar : Set EuclideanPlane), ∀ p2 ∈ (Pbar : Set EuclideanPlane),
      p1 ≠ p2 → δ ≤ dist p1 p2 := by
    intro p1 hp1 p2 hp2 hne
    have h : 2 * δ < dist p1 p2 := h_strict_sep p1 hp1 p2 hp2 hne
    have h2 : δ < 2 * δ := by linarith [hδ_pos]
    linarith

  exact ⟨Pbar, hPbar_subset, h_weak_sep, h_sset, h_card_upper, h_ncover_lower⟩

end DirecretisedFurstenbergEstimate.FrontEndLemmas

end
