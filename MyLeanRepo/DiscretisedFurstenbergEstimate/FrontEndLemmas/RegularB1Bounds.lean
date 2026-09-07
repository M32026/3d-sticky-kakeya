module

/-
  Regular B1 Quantitative Bounds.

  Provides helper lemmas for the B1 bridge decomposition:
  - Covering number movement under δ-matching
  - Dyadic square count vs covering number (factor 9)
  - Coarse cardinality upper bound
  - Fine cardinality lower bound from covering number
  - Constant absorption lemma

  Whiteprint node: front_end_lemmas / regular_b1_bounds
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.RobustKaufmanProjection.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open RobustKaufmanProjection

/-! ### Helper: coordinate bound by Euclidean norm -/

lemma abs_coord_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h1 : (x i)^2 ≤ ‖x‖^2 := by
    have h2 : ‖x‖^2 = ∑ j : Fin n, (x j)^2 := by
      have h21 : ‖x‖ = Real.sqrt (∑ j : Fin n, (x j)^2) := by
        simp [EuclideanSpace.norm_eq]
      rw [h21]
      have h22 : 0 ≤ ∑ j : Fin n, (x j)^2 := by positivity
      rw [Real.sq_sqrt h22]
    rw [h2]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have h3 : 0 ≤ ‖x‖ := by positivity
  nlinarith [sq_abs (x i)]

/-! ### Covering number movement upper bound -/

/-- Transfer lemma: if every ε-cover of A is an ε'-cover of A', then
    `externalCoveringNumber ε' A' ≤ externalCoveringNumber ε A`. -/
lemma externalCoveringNumber_transfer {X : Type*} [PseudoMetricSpace X] {ε ε' : NNReal} {A A' : Set X}
    (h : ∀ C, Metric.IsCover ε A C → Metric.IsCover ε' A' C) :
    Metric.externalCoveringNumber ε' A' ≤ Metric.externalCoveringNumber ε A := by
  have h_main : ∀ (C : Set X), Metric.IsCover ε A C →
      Metric.externalCoveringNumber ε' A' ≤ C.encard := by
    intro C hC
    have hC' : Metric.IsCover ε' A' C := h C hC
    exact Metric.IsCover.externalCoveringNumber_le_encard hC'
  have h_final : Metric.externalCoveringNumber ε' A' ≤ Metric.externalCoveringNumber ε A := by
    unfold Metric.externalCoveringNumber
    rw [le_iInf_iff]
    intro C
    rw [le_iInf_iff]
    intro hC
    exact h_main C hC
  exact h_final

/-- If `Pfin` and `P` are δ-close (backward matching), and `δ ≤ Δ`, then
    `Ncover(Δ, Pfin) ≤ 9 * Ncover(Δ, P)`. -/
lemma ncover_match_upper
    {Δ δ : ℝ} (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    {P : Set EuclideanPlane} {Pfin : Finset EuclideanPlane}
    (h_match_backward : ∀ q ∈ Pfin, ∃ p ∈ P, dist q p ≤ δ) :
    Metric.externalCoveringNumber Δ.toNNReal (Pfin : Set EuclideanPlane) ≤
      9 * Metric.externalCoveringNumber Δ.toNNReal P := by
  let twoΔ : NNReal := ⟨2 * Δ, by linarith⟩
  have h_twoΔ_coe : (twoΔ : ℝ) = 2 * Δ := by
    exact Subtype.coe_mk (2 * Δ) _
  have hΔ_coe : (Δ.toNNReal : ℝ) = Δ := Real.coe_toNNReal Δ hΔ_pos.le

  -- Step 1: Ncover(2Δ, Pfin) ≤ Ncover(Δ, P) by transfer
  have h1 : Metric.externalCoveringNumber twoΔ (Pfin : Set EuclideanPlane) ≤
      Metric.externalCoveringNumber Δ.toNNReal P := by
    apply externalCoveringNumber_transfer
    intro C hC
    intro q hq
    rcases h_match_backward q hq with ⟨p, hp, hdist_qp⟩
    rcases hC hp with ⟨c, hc, hdist_edist⟩
    have hdist_edist' : edist p c ≤ ↑Δ.toNNReal := by simpa using hdist_edist
    have hdist_pc : dist p c ≤ Δ := by
      have h_eq : (↑Δ.toNNReal : ENNReal) = ENNReal.ofReal (↑Δ.toNNReal : ℝ) := by exact Eq.symm ENNReal.ofReal_coe_nnreal
      rw [edist_dist] at hdist_edist'
      rw [h_eq, hΔ_coe] at hdist_edist'
      exact (ENNReal.ofReal_le_ofReal_iff hΔ_pos.le).mp hdist_edist'
    have hdist_qc : dist q c ≤ 2 * Δ := by
      calc dist q c ≤ dist q p + dist p c := dist_triangle q p c
           _ ≤ δ + Δ := by linarith
           _ ≤ 2 * Δ := by linarith
    have h_edist : edist q c ≤ ↑twoΔ := by
      rw [edist_dist]
      have h3 : (↑twoΔ : ENNReal) = ENNReal.ofReal (↑twoΔ : ℝ) := by exact ENNReal.coe_nnreal_eq twoΔ
      rw [h3, h_twoΔ_coe]
      exact ENNReal.ofReal_le_ofReal hdist_qc
    exact ⟨c, hc, h_edist⟩

  -- Step 2: Ncover(Δ, Pfin) ≤ 9 * Ncover(2Δ, Pfin) by doubling
  have h_half : twoΔ / 2 = Δ.toNNReal := by
    apply Subtype.ext
    have h_coe_div : ((twoΔ / 2 : NNReal) : ℝ) = (↑twoΔ : ℝ) / 2 := by exact Real.ext_cauchy rfl
    have h1 : ((twoΔ / 2 : NNReal) : ℝ) = Δ := by
      rw [h_coe_div, h_twoΔ_coe] <;> ring
    have h2 : ((Δ.toNNReal : NNReal) : ℝ) = Δ := hΔ_coe
    exact h1.trans h2.symm
  have h2 : Metric.externalCoveringNumber Δ.toNNReal (Pfin : Set EuclideanPlane) ≤
      9 * Metric.externalCoveringNumber twoΔ (Pfin : Set EuclideanPlane) := by
    have h2' := externalCoveringNumber_half_le_plane (Pfin : Set EuclideanPlane) twoΔ
    rw [h_half] at h2'
    exact h2'

  -- Step 3: Combine
  calc Metric.externalCoveringNumber Δ.toNNReal (Pfin : Set EuclideanPlane)
    ≤ 9 * Metric.externalCoveringNumber twoΔ (Pfin : Set EuclideanPlane) := h2
  _ ≤ 9 * Metric.externalCoveringNumber Δ.toNNReal P := by gcongr

/-! ### Dyadic square count vs covering number -/

/-- A ball of radius δ intersects at most 9 dyadic squares of side δ. -/
lemma ball_intersects_at_most_9_squares_simple
    {n : ℕ} (c : EuclideanPlane) :
    ∃ (I : Finset (DyadicSquare n)), I.card ≤ 9 ∧
      ∀ (p : DyadicSquare n),
        ((p.toSet : Set EuclideanPlane) ∩ Metric.closedBall c (dyadicDelta n)).Nonempty → p ∈ I := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let i0 : ℤ := Int.floor (c 0 / δ)
  let j0 : ℤ := Int.floor (c 1 / δ)
  let I : Finset (DyadicSquare n) :=
    (Finset.Icc (i0 - 1) (i0 + 1)).biUnion fun i =>
      (Finset.Icc (j0 - 1) (j0 + 1)).image fun j => ⟨i, j⟩
  have hI_card : I.card ≤ 9 := by
    let J := Finset.Icc (i0 - 1) (i0 + 1)
    let K := Finset.Icc (j0 - 1) (j0 + 1)
    let f : ℤ × ℤ → DyadicSquare n := fun p => ⟨p.1, p.2⟩
    have hJ : J.card = 3 := by simp [J, Finset.Icc_eq_empty_of_lt] <;> omega
    have hK : K.card = 3 := by simp [K, Finset.Icc_eq_empty_of_lt] <;> omega
    have h_sub : I ⊆ (J.product K).image f := by
      intro p hp
      simp only [I, Finset.mem_biUnion] at hp
      rcases hp with ⟨i, hi, hmem⟩
      simp only [Finset.mem_image] at hmem
      rcases hmem with ⟨j, hj, h_eq⟩
      have h_pair : (i, j) ∈ J.product K := Finset.mem_product.mpr ⟨hi, hj⟩
      have h_goal : p ∈ (J.product K).image f := by
        apply Finset.mem_image.mpr
        exact ⟨(i, j), h_pair, by simp [f, h_eq]⟩
      exact h_goal
    have h_card_img : ((J.product K).image f).card ≤ (J.product K).card := Finset.card_image_le
    have h_JK_card : (J.product K).card = 9 := by
      have h : (J.product K).card = J.card * K.card := by
        simpa [Finset.card_product] using rfl
      rw [h, hJ, hK] <;> norm_num
    have h3 : I.card ≤ ((J.product K).image f).card := Finset.card_le_card h_sub
    linarith
  refine ⟨I, hI_card, ?_⟩
  intro p hp
  rcases hp with ⟨x, hxp, hxc⟩
  have hdist : dist x c ≤ δ := hxc
  have hx0 : |x 0 - c 0| ≤ δ := by
    have h : |(x - c) 0| ≤ ‖x - c‖ := abs_coord_le_norm (x - c) 0
    have h4 : (x - c) 0 = x 0 - c 0 := by simp
    rw [h4] at h
    have h5 : ‖x - c‖ = dist x c := by rfl
    rw [h5] at h
    exact le_trans h hdist
  have hx1 : |x 1 - c 1| ≤ δ := by
    have h : |(x - c) 1| ≤ ‖x - c‖ := abs_coord_le_norm (x - c) 1
    have h4 : (x - c) 1 = x 1 - c 1 := by simp
    rw [h4] at h
    have h5 : ‖x - c‖ = dist x c := by rfl
    rw [h5] at h
    exact le_trans h hdist
  have hpi1 : (p.i : ℝ) * δ ≤ x 0 := hxp.1
  have hpi2 : x 0 < ((p.i : ℝ) + 1) * δ := hxp.2.1
  have hpj1 : (p.j : ℝ) * δ ≤ x 1 := hxp.2.2.1
  have hpj2 : x 1 < ((p.j : ℝ) + 1) * δ := hxp.2.2.2
  have h_i_lower : i0 - 1 ≤ p.i := by
    have h1 : c 0 - δ ≤ x 0 := by linarith [abs_le.mp hx0]
    have h2 : (p.i : ℝ) * δ > c 0 - 2 * δ := by linarith
    have h3 : (p.i : ℝ) > c 0 / δ - 2 := by
      have h4 : (p.i : ℝ) * δ / δ > (c 0 - 2 * δ) / δ := by gcongr
      have h5 : (p.i : ℝ) * δ / δ = (p.i : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
      rw [h5] at h4
      have h6 : (c 0 - 2 * δ) / δ = c 0 / δ - 2 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h6] at h4; exact h4
    have h7 : (p.i : ℝ) > (i0 : ℝ) - 2 := by linarith [Int.floor_le (c 0 / δ)]
    by_contra h9
    have h10 : p.i ≤ i0 - 2 := by linarith
    have h11 : (p.i : ℝ) ≤ (i0 : ℝ) - 2 := by exact_mod_cast h10
    linarith
  have h_i_upper : p.i ≤ i0 + 1 := by
    have h1 : x 0 ≤ c 0 + δ := by linarith [abs_le.mp hx0]
    have h2 : (p.i : ℝ) * δ ≤ c 0 + δ := by linarith
    have h3 : (p.i : ℝ) ≤ c 0 / δ + 1 := by
      have h4 : (p.i : ℝ) * δ / δ ≤ (c 0 + δ) / δ := by gcongr
      have h5 : (p.i : ℝ) * δ / δ = (p.i : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
      rw [h5] at h4
      have h6 : (c 0 + δ) / δ = c 0 / δ + 1 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h6] at h4; exact h4
    have h7 : c 0 / δ < (i0 : ℝ) + 1 := Int.lt_floor_add_one (c 0 / δ)
    have h8 : (p.i : ℝ) < (i0 : ℝ) + 2 := by linarith
    by_contra h9
    have h10 : p.i ≥ i0 + 2 := by linarith
    have h11 : (p.i : ℝ) ≥ (i0 : ℝ) + 2 := by exact_mod_cast h10
    linarith
  have h_j_lower : j0 - 1 ≤ p.j := by
    have h1 : c 1 - δ ≤ x 1 := by linarith [abs_le.mp hx1]
    have h2 : (p.j : ℝ) * δ > c 1 - 2 * δ := by linarith
    have h3 : (p.j : ℝ) > c 1 / δ - 2 := by
      have h4 : (p.j : ℝ) * δ / δ > (c 1 - 2 * δ) / δ := by gcongr
      have h5 : (p.j : ℝ) * δ / δ = (p.j : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
      rw [h5] at h4
      have h6 : (c 1 - 2 * δ) / δ = c 1 / δ - 2 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h6] at h4; exact h4
    have h7 : (p.j : ℝ) > (j0 : ℝ) - 2 := by linarith [Int.floor_le (c 1 / δ)]
    by_contra h9
    have h10 : p.j ≤ j0 - 2 := by linarith
    have h11 : (p.j : ℝ) ≤ (j0 : ℝ) - 2 := by exact_mod_cast h10
    linarith
  have h_j_upper : p.j ≤ j0 + 1 := by
    have h1 : x 1 ≤ c 1 + δ := by linarith [abs_le.mp hx1]
    have h2 : (p.j : ℝ) * δ ≤ c 1 + δ := by linarith
    have h3 : (p.j : ℝ) ≤ c 1 / δ + 1 := by
      have h4 : (p.j : ℝ) * δ / δ ≤ (c 1 + δ) / δ := by gcongr
      have h5 : (p.j : ℝ) * δ / δ = (p.j : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
      rw [h5] at h4
      have h6 : (c 1 + δ) / δ = c 1 / δ + 1 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h6] at h4; exact h4
    have h7 : c 1 / δ < (j0 : ℝ) + 1 := Int.lt_floor_add_one (c 1 / δ)
    have h8 : (p.j : ℝ) < (j0 : ℝ) + 2 := by linarith
    by_contra h9
    have h10 : p.j ≥ j0 + 2 := by linarith
    have h11 : (p.j : ℝ) ≥ (j0 : ℝ) + 2 := by exact_mod_cast h10
    linarith
  have h_i_in : p.i ∈ Finset.Icc (i0 - 1) (i0 + 1) := by
    simp only [Finset.mem_Icc] <;> omega
  have h_j_in : p.j ∈ Finset.Icc (j0 - 1) (j0 + 1) := by
    simp only [Finset.mem_Icc] <;> omega
  have h_goal : p ∈ I := by
    rw [Finset.mem_biUnion]
    exact ⟨p.i, h_i_in, by
      rw [Finset.mem_image]
      exact ⟨p.j, h_j_in, by simp⟩⟩
  exact h_goal

/-- Number of dyadic squares intersecting a set ≤ 9 × covering number. -/
lemma dyadic_squares_card_le_9_ncover
    {m : ℕ} {S : Set EuclideanPlane} {squares : Finset (DyadicSquare m)}
    (h_intersect : ∀ Q ∈ squares, (S ∩ (Q.toSet : Set EuclideanPlane)).Nonempty) :
    (squares.card : ℕ∞) ≤
      9 * Metric.externalCoveringNumber (dyadicDelta m).toNNReal S := by
  let δ := dyadicDelta m
  have hδ_pos : 0 < δ := dyadicDelta_pos m
  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal S = ⊤
  · rw [h_top] <;> simp
  · have hfin : ∃ (n : ℕ), Metric.externalCoveringNumber δ.toNNReal S = ↑n := by exact Option.ne_none_iff_exists'.mp h_top
    rcases hfin with ⟨n, hn⟩
    have h1 : (↑n : ℕ∞) < ↑(n + 1) := by exact_mod_cast Nat.lt_succ_self n
    have h2 : ¬ (↑(n + 1) : ℕ∞) ≤ Metric.externalCoveringNumber δ.toNNReal S := by
      rw [hn]; exact not_le.mpr h1
    have h3 : ∃ (C : Set EuclideanPlane), Metric.IsCover δ.toNNReal S C ∧
        ¬ (↑(n + 1) : ℕ∞) ≤ C.encard := by
      simpa [Metric.externalCoveringNumber, le_iInf_iff] using h2
    rcases h3 with ⟨C, hC, hlt⟩
    have h4 : C.encard < ↑(n + 1) := by exact Std.not_le.mp hlt
    have h5 : Metric.externalCoveringNumber δ.toNNReal S ≤ C.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC
    have h6 : (↑n : ℕ∞) ≤ C.encard := by rw [hn] at h5; exact h5
    have h_encard_n : C.encard = ↑n := by
      have h_ne_top : C.encard ≠ ⊤ := by
        intro h_top2; rw [h_top2] at h4; simp at h4
      have h_exists : ∃ (m2 : ℕ), C.encard = ↑m2 := by exact Option.ne_none_iff_exists'.mp h_ne_top
      rcases h_exists with ⟨m2, hm2⟩
      rw [hm2] at h6 h4
      have hmn : n ≤ m2 := by exact_mod_cast h6
      have hmn2 : m2 < n + 1 := by exact_mod_cast h4
      have hmeq : m2 = n := by omega
      rw [hmeq] at hm2; exact hm2
    have hCfin : Set.Finite C := by
      by_contra h
      have h' : Set.Infinite C := by exact Set.not_finite.mp h
      have h_top : C.encard = ⊤ := by exact Set.encard_eq_top_iff.mpr h
      rw [h_top] at h_encard_n
      simp at h_encard_n
    let Cfin := hCfin.toFinset
    have h2eq : (Cfin : Set EuclideanPlane) = C := Set.Finite.coe_toFinset _
    let Q_c (c : EuclideanPlane) : Finset (DyadicSquare m) :=
      squares.filter (fun Q => (Q.toSet : Set EuclideanPlane) ∩ Metric.closedBall c δ ≠ ∅)
    have h3 : ∀ c ∈ Cfin, (Q_c c).card ≤ 9 := by
      intro c _
      rcases ball_intersects_at_most_9_squares_simple (n := m) c with ⟨I, hI9, hI_mem⟩
      have h4 : Q_c c ⊆ I := by
        intro p hp
        have h51 : p ∈ squares := (Finset.mem_filter.mp hp).1
        have h52 : (p.toSet : Set EuclideanPlane) ∩ Metric.closedBall c δ ≠ ∅ :=
          (Finset.mem_filter.mp hp).2
        have h53 : ((p.toSet : Set EuclideanPlane) ∩ Metric.closedBall c δ).Nonempty := by
          simpa [Set.nonempty_iff_ne_empty] using h52
        exact hI_mem p h53
      have h5 : (Q_c c).card ≤ I.card := Finset.card_le_card h4
      exact le_trans h5 hI9
    have h4 : squares ⊆ Cfin.biUnion Q_c := by
      intro Q hQ
      rcases h_intersect Q hQ with ⟨p, hpS, hpQ⟩
      have h6 : ∃ (c : EuclideanPlane), c ∈ Cfin ∧ p ∈ Metric.closedBall c δ := by
        have h7 : p ∈ S := hpS
        rcases hC h7 with ⟨c, hc, hdist⟩
        have hdist' : edist p c ≤ ↑δ.toNNReal := by simpa using hdist
        have h8 : dist p c ≤ δ := by
          rw [edist_dist] at hdist'
          have h_coe : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
          rw [h_coe] at hdist'
          exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hdist'
        have h9 : c ∈ Cfin := by
          have h10 : c ∈ C := hc
          have h11 : c ∈ (Cfin : Set EuclideanPlane) := by
            rw [h2eq] <;> exact h10
          exact h11
        exact ⟨c, h9, h8⟩
      rcases h6 with ⟨c, hc, hball⟩
      have h_ne : ((Q.toSet : Set EuclideanPlane) ∩ Metric.closedBall c δ).Nonempty := ⟨p, hpQ, hball⟩
      have h_ne' : (Q.toSet : Set EuclideanPlane) ∩ Metric.closedBall c δ ≠ ∅ :=
        Set.nonempty_iff_ne_empty.mp h_ne
      have h10 : Q ∈ Q_c c := by
        apply Finset.mem_filter.mpr
        exact ⟨hQ, h_ne'⟩
      exact Finset.mem_biUnion.mpr ⟨c, hc, h10⟩
    have h5 : squares.card ≤ (Cfin.biUnion Q_c).card := Finset.card_le_card h4
    have h6 : (Cfin.biUnion Q_c).card ≤ ∑ c ∈ Cfin, (Q_c c).card := Finset.card_biUnion_le
    have h_sum_bound : ∑ c ∈ Cfin, (Q_c c).card ≤ 9 * Cfin.card := by
      calc ∑ c ∈ Cfin, (Q_c c).card
        ≤ ∑ c ∈ Cfin, 9 := Finset.sum_le_sum fun i _ => h3 i ‹_›
      _ = 9 * Cfin.card := by simp [Finset.sum_const] <;> ring
    have h8 : squares.card ≤ 9 * Cfin.card := by linarith
    have h9 : (Cfin.card : ℕ∞) = C.encard := by
      have h10 : (Cfin.card : ℕ∞) = C.encard := by
        simp [← h2eq]
      exact h10
    calc (squares.card : ℕ∞)
      ≤ 9 * (Cfin.card : ℕ∞) := by exact_mod_cast h8
    _ = 9 * C.encard := by rw [h9]
    _ = 9 * (↑n : ℕ∞) := by rw [h_encard_n]
    _ = 9 * Metric.externalCoveringNumber δ.toNNReal S := by rw [hn]

/-- Coarse cardinality upper bound: `|coarseP₀| ≤ 81 * Ncover(Δ, P)`. -/
lemma coarse_card_upper
    {m : ℕ} {Δ δ : ℝ} (hΔ_eq : Δ = dyadicDelta m)
    (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    {P : Set EuclideanPlane} {Pfin : Finset EuclideanPlane}
    {coarseP₀ : Finset (DyadicSquare m)}
    (h_match_backward : ∀ q ∈ Pfin, ∃ p ∈ P, dist q p ≤ δ)
    (h_intersect : ∀ Q ∈ coarseP₀,
      ((Pfin : Set EuclideanPlane) ∩ (Q.toSet : Set EuclideanPlane)).Nonempty) :
    (coarseP₀.card : ℕ∞) ≤
      81 * Metric.externalCoveringNumber Δ.toNNReal P := by
  have h1 : (coarseP₀.card : ℕ∞) ≤
      9 * Metric.externalCoveringNumber Δ.toNNReal (Pfin : Set EuclideanPlane) := by
    have h1' : (coarseP₀.card : ℕ∞) ≤
        9 * Metric.externalCoveringNumber (dyadicDelta m).toNNReal (Pfin : Set EuclideanPlane) :=
      dyadic_squares_card_le_9_ncover h_intersect
    simpa [hΔ_eq] using h1'
  have h2 : Metric.externalCoveringNumber Δ.toNNReal (Pfin : Set EuclideanPlane) ≤
      9 * Metric.externalCoveringNumber Δ.toNNReal P :=
    ncover_match_upper hΔ_pos hδ_pos hδ_le_Δ h_match_backward
  calc (coarseP₀.card : ℕ∞)
    ≤ 9 * Metric.externalCoveringNumber Δ.toNNReal (Pfin : Set EuclideanPlane) := h1
  _ ≤ 9 * (9 * Metric.externalCoveringNumber Δ.toNNReal P) := by gcongr
  _ = 81 * Metric.externalCoveringNumber Δ.toNNReal P := by ring

/-! ### Fine cardinality lower bound -/

/-- `Ncover(δ, pointSet) ≤ |P₀|` when pointSet is covered by the squares. -/
lemma fine_card_lower_ncover
    {n : ℕ} {P₀ : Finset (DyadicSquare n)}
    {pointSet : Set EuclideanPlane}
    (h_pointSet_sub : pointSet ⊆
      ⋃ p ∈ (P₀ : Set (DyadicSquare n)), (p.toSet : Set EuclideanPlane)) :
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal pointSet ≤ (P₀.card : ℕ∞) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h_square_cover : ∀ (p : DyadicSquare n), ∃ (c : EuclideanPlane),
      (p.toSet : Set EuclideanPlane) ⊆ Metric.closedBall c δ := by
    intro p
    let c : EuclideanPlane := WithLp.toLp (2 : ENNReal) fun i : Fin 2 =>
      if i = 0 then ((p.i : ℝ) + 1 / 2) * δ else ((p.j : ℝ) + 1 / 2) * δ
    refine ⟨c, ?_⟩
    intro x hx
    have h4 : |x 0 - c 0| ≤ δ / 2 := by
      dsimp only [c]
      have h5 : x 0 - (((p.i : ℝ) + 1 / 2) * δ) ≤ δ / 2 := by linarith [hx.1, hx.2.1]
      have h6 : -(δ / 2) ≤ x 0 - (((p.i : ℝ) + 1 / 2) * δ) := by linarith [hx.1, hx.2.1]
      exact abs_le.mpr ⟨h6, h5⟩
    have h7 : |x 1 - c 1| ≤ δ / 2 := by
      dsimp only [c]
      have h8 : x 1 - (((p.j : ℝ) + 1 / 2) * δ) ≤ δ / 2 := by linarith [hx.2.2.1, hx.2.2.2]
      have h9 : -(δ / 2) ≤ x 1 - (((p.j : ℝ) + 1 / 2) * δ) := by linarith [hx.2.2.1, hx.2.2.2]
      exact abs_le.mpr ⟨h9, h8⟩
    have h10 : ‖x - c‖ ^ 2 = (x 0 - c 0)^2 + (x 1 - c 1)^2 := by
      have h121 : ‖x - c‖ = Real.sqrt ((x 0 - c 0)^2 + (x 1 - c 1)^2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
      rw [h121]
      have h122 : 0 ≤ (x 0 - c 0)^2 + (x 1 - c 1)^2 := by positivity
      rw [Real.sq_sqrt h122]
    have h11 : ‖x - c‖ ≤ δ := by
      have h12 : ‖x - c‖ ^ 2 ≤ δ^2 := by
        rw [h10]
        nlinarith [abs_le.mp h4, abs_le.mp h7]
      have h13 : 0 ≤ ‖x - c‖ := by positivity
      nlinarith
    exact h11
  let centers : Finset EuclideanPlane := P₀.image (fun p => Classical.choose (h_square_cover p))
  have hcenters_card : centers.card ≤ P₀.card := Finset.card_image_le
  have hcover2 : pointSet ⊆ ⋃ c ∈ (centers : Set EuclideanPlane), Metric.closedBall c δ := by
    intro x hx
    have h5 : x ∈ (⋃ p ∈ (P₀ : Set (DyadicSquare n)), (p.toSet : Set EuclideanPlane)) := h_pointSet_sub hx
    rcases Set.mem_iUnion₂.mp h5 with ⟨p, hp, hxp⟩
    let c := Classical.choose (h_square_cover p)
    have hc : c ∈ centers := by
      apply Finset.mem_image.mpr
      exact ⟨p, hp, rfl⟩
    have h6 : x ∈ Metric.closedBall c δ := (Classical.choose_spec (h_square_cover p)) hxp
    exact Set.mem_iUnion₂.mpr ⟨c, hc, h6⟩
  have hIsCover : Metric.IsCover δ.toNNReal pointSet (centers : Set EuclideanPlane) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hcover2 hx) with ⟨c, hc, hball⟩
    have h_edist : edist x c ≤ ↑δ.toNNReal := by
      rw [edist_dist]
      have h7 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
        exact ENNReal.ofNNReal_toNNReal δ
      rw [h7]
      exact ENNReal.ofReal_le_ofReal hball
    exact ⟨c, hc, h_edist⟩
  have h : Metric.externalCoveringNumber δ.toNNReal pointSet ≤ (centers : Set EuclideanPlane).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hIsCover
  have h2 : (centers : Set EuclideanPlane).encard = ↑(centers.card) := by simp
  rw [h2] at h
  exact le_trans h (by exact_mod_cast hcenters_card)

/-! ### Constant absorption -/

/-- For sufficiently small Δ, `C ≤ Δ^{-a}`. -/
lemma absorb_const_delta (C a : ℝ) (hC_pos : 0 < C) (ha_pos : 0 < a) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ Δ, 0 < Δ → Δ ≤ δ₀ → C ≤ Real.rpow Δ (-a) := by
  let δ₀ : ℝ := min 1 (Real.rpow (1 / C) (1 / a))
  have hδ₀_pos : 0 < δ₀ := by
    have h1 : 0 < (1 : ℝ) := by norm_num
    have h2 : 0 < Real.rpow (1 / C) (1 / a) := Real.rpow_pos_of_pos (by positivity) (1 / a)
    have h3 : 0 < min (1 : ℝ) (Real.rpow (1 / C) (1 / a)) := by
      apply lt_min h1 h2
    exact h3
  have hδ₀_le_one : δ₀ ≤ 1 := min_le_left _ _
  have hδ₀_rpow : Real.rpow δ₀ a ≤ 1 / C := by
    have h1 : δ₀ ≤ Real.rpow (1 / C) (1 / a) := min_le_right _ _
    have h2 : Real.rpow δ₀ a ≤ Real.rpow (Real.rpow (1 / C) (1 / a)) a :=
      Real.rpow_le_rpow (by linarith) h1 (by linarith)
    have h_pos : 0 ≤ (1 / C) := by positivity
    have h3 : Real.rpow (Real.rpow (1 / C) (1 / a)) a = Real.rpow (1 / C) ((1 / a) * a) :=
      (Real.rpow_mul h_pos (1 / a) a).symm
    have h5 : (1 / a) * a = 1 := by field_simp [ha_pos.ne'] <;> ring
    have h6 : Real.rpow (1 / C) ((1 / a) * a) = 1 / C := by
      rw [h5]
      simp
    rw [h3, h6] at h2
    exact h2
  refine ⟨δ₀, hδ₀_pos, fun Δ hΔ_pos hΔ_le => ?_⟩
  have h4 : Real.rpow Δ a ≤ Real.rpow δ₀ a :=
    Real.rpow_le_rpow (by linarith) hΔ_le (by linarith)
  have h5 : Real.rpow Δ a ≤ 1 / C := le_trans h4 hδ₀_rpow
  have h6 : 0 < Real.rpow Δ a := Real.rpow_pos_of_pos hΔ_pos a
  have h7 : Real.rpow Δ (-a) = (Real.rpow Δ a)⁻¹ := by
    have h_sum : Real.rpow Δ (-a) * Real.rpow Δ a = 1 := by
      have h9 : Real.rpow Δ (-a) * Real.rpow Δ a = Real.rpow Δ ((-a) + a) :=
        (Real.rpow_add hΔ_pos (-a) a).symm
      rw [h9]
      have h10 : (-a) + a = 0 := by ring
      rw [h10]
      simp
    field_simp [h6.ne'] at h_sum ⊢ <;> linarith
  rw [h7]
  have h9 : (Real.rpow Δ a)⁻¹ ≥ (1 / C)⁻¹ := by gcongr
  have h10 : (1 / C)⁻¹ = C := by field_simp [hC_pos.ne'] <;> ring
  rw [h10] at h9
  exact h9

end DirecretisedFurstenbergEstimate.FrontEndLemmas
