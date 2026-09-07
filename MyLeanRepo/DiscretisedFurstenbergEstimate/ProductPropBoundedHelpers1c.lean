module

/-
  Bounded productProp from A.7 axiom — Helpers part 1c.

  Contains: S-set perturbation lemma for ℝ×ℝ under small 1-Lipschitz shifts.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Translation
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RealAnalysis
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers1a
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers1b
public import MyLeanRepo.DiscretisedFurstenbergEstimate.H7cCoveringBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

open DiscretisedFurstenbergEstimate.CoveringUtils
open DiscretisedFurstenbergEstimate.Translation

noncomputable section

namespace DirecretisedFurstenbergEstimate

open DiscretisedFurstenbergEstimate.CoveringUtils

/-! ### Covering refinement and S-set perturbation -/

/-- The δ-covering number of a 1-Lipschitz image is at most that of the original set. -/
lemma externalCovering_number_lipschitz_image
    {X : Type*} [PseudoMetricSpace X] {ε : NNReal} {f : X → X}
    (hf : LipschitzWith 1 f) {S : Set X} :
    Metric.externalCoveringNumber ε (f '' S) ≤ Metric.externalCoveringNumber ε S := by
  by_cases h_top : Metric.externalCoveringNumber ε S = ⊤
  · rw [h_top] <;> exact le_top
  · have h_ne : Metric.externalCoveringNumber ε S ≠ ⊤ := h_top
    have h_fin : Metric.externalCoveringNumber ε S < ⊤ := by
      exact Ne.lt_top' (id (Ne.symm h_ne))
    rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq h_fin with ⟨C, hC, hC_eq⟩
    have hC' : Metric.IsCover ε (f '' S) (f '' C) := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rcases hC hx with ⟨c, hc, hed⟩
      have h_ed : edist (f x) (f c) ≤ edist x c := by
        have h := hf.edist_le_mul x c
        simpa using h
      exact ⟨f c, Set.mem_image_of_mem f hc, h_ed.trans hed⟩
    have h4 : Metric.externalCoveringNumber ε (f '' S) ≤ (f '' C).encard :=
      hC'.externalCoveringNumber_le_encard
    have h5 : (f '' C).encard ≤ C.encard := Set.encard_image_le f C
    have h6 : C.encard = Metric.externalCoveringNumber ε S := hC_eq
    rw [h6] at h5
    exact h4.trans h5

/-- If `A ⊆ ℝ×ℝ` and `f` is 1-Lipschitz moving points by at most `K*δ`, then
    the δ-covering number of `A` is at most `N` times that of `f '' A`,
    where `N = (ceil(2*(K+1))+1)^2`. -/
lemma covering_estimate_perturbation_prod
    {δ : ℝ} (hδ : 0 < δ) {K : ℝ} (hK : 0 ≤ K)
    {A : Set (ℝ × ℝ)} (hA_bdd : Bornology.IsBounded A)
    {f : ℝ × ℝ → ℝ × ℝ} (hf_lip : LipschitzWith 1 f)
    (h_move : ∀ x ∈ A, dist x (f x) ≤ K * δ) :
    (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
      ((Nat.ceil (2 * (K + 1)) + 1)^2 : ENNReal) *
      (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal) := by
  let N : ℕ := (Nat.ceil (2 * (K + 1)) + 1)^2
  have hN_eq : (N : ENNReal) = ((Nat.ceil (2 * (K + 1)) + 1)^2 : ENNReal) := by
    simp [N]
  have h_image_bdd : Bornology.IsBounded (f '' A) :=
    hf_lip.isBounded_image hA_bdd
  have h_fin_image : Metric.externalCoveringNumber δ.toNNReal (f '' A) < ⊤ :=
    externalCoveringNumber_bounded_prod (by positivity) h_image_bdd
  rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq h_fin_image with ⟨C_f, hC_f_cover, hC_f_eq⟩
  have hC_f_fin : Set.Finite C_f := by
    have h : C_f.encard < ⊤ := by
      rw [hC_f_eq]; exact h_fin_image
    exact Set.encard_lt_top_iff.mp h
  let C_fin := hC_f_fin.toFinset
  have hC_fin_eq : (C_fin : Set (ℝ × ℝ)) = C_f := by
    ext x; simp [C_fin]
  let D_c : ℝ × ℝ → Finset (ℝ × ℝ) := fun c =>
    (ball_cover_prod (K + 1) δ (by linarith) hδ c).choose
  have hD_c_cover : ∀ c : ℝ × ℝ,
      Metric.closedBall c ((K + 1) * δ) ⊆ ⋃ d ∈ (D_c c : Set (ℝ × ℝ)), Metric.closedBall d δ := by
    intro c
    exact (ball_cover_prod (K + 1) δ (by linarith) hδ c).choose_spec.1
  have hD_c_card : ∀ c : ℝ × ℝ, (D_c c).card ≤ N := by
    intro c
    exact (ball_cover_prod (K + 1) δ (by linarith) hδ c).choose_spec.2
  let D : Finset (ℝ × ℝ) := Finset.biUnion C_fin D_c
  have hD_cover : Metric.IsCover δ.toNNReal A (D : Set (ℝ × ℝ)) := by
    intro x hx
    have hfx_in : f x ∈ f '' A := ⟨x, hx, rfl⟩
    rcases hC_f_cover hfx_in with ⟨c, hc, h_edist⟩
    have h_c_in_Cfin : c ∈ C_fin := by
      simpa [C_fin, hC_fin_eq] using hc
    have h_dist_fc : dist (f x) c ≤ δ := by
      have h : nndist (f x) c ≤ δ.toNNReal := edist_le_coe.mp h_edist
      have h2 : dist (f x) c ≤ (δ.toNNReal : ℝ) := dist_le_coe.mpr h
      have h3 : (δ.toNNReal : ℝ) = δ := by
        rw [Real.coe_toNNReal', max_eq_left (by linarith)]
      rw [h3] at h2; exact h2
    have h_dist_xc : dist x c ≤ (K + 1) * δ := by
      have h6 : dist x (f x) ≤ K * δ := h_move x hx
      calc dist x c
        ≤ dist x (f x) + dist (f x) c := dist_triangle _ _ _
      _ ≤ K * δ + δ := by linarith
      _ = (K + 1) * δ := by ring
    have h_x_in_ball : x ∈ Metric.closedBall c ((K + 1) * δ) := h_dist_xc
    have h4 : x ∈ ⋃ d ∈ (D_c c : Set (ℝ × ℝ)), Metric.closedBall d δ :=
      hD_c_cover c h_x_in_ball
    rcases Set.mem_iUnion₂.mp h4 with ⟨d, hd_in_Dc, h_dist_xd⟩
    have h_d_in_D : d ∈ D := by
      exact Finset.mem_biUnion.mpr ⟨c, h_c_in_Cfin, hd_in_Dc⟩
    have h_edist2 : edist x d ≤ ↑δ.toNNReal := by
      rw [edist_dist]
      have h_pos : 0 ≤ δ := by linarith
      have h_coe : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
        exact ENNReal.ofNNReal_toNNReal δ
      rw [h_coe]
      exact (ENNReal.ofReal_le_ofReal_iff h_pos).mpr h_dist_xd
    exact ⟨d, h_d_in_D, h_edist2⟩
  have h1 : Metric.externalCoveringNumber δ.toNNReal A ≤ (D : Set (ℝ × ℝ)).encard :=
    hD_cover.externalCoveringNumber_le_encard
  have h2 : D.card ≤ N * C_fin.card := by
    calc D.card
      ≤ ∑ c ∈ C_fin, (D_c c).card := Finset.card_biUnion_le
    _ ≤ ∑ c ∈ C_fin, N := by gcongr <;> exact hD_c_card c
    _ = N * C_fin.card := by simp [Finset.sum_const] <;> ring
  have h3 : (D : Set (ℝ × ℝ)).encard ≤ (N : ENat) * ↑C_fin.card := by
    have h4 : (D : Set (ℝ × ℝ)).encard = ↑D.card := by simp
    rw [h4]
    have h5 : ↑D.card ≤ (↑N : ENat) * ↑C_fin.card := by exact_mod_cast h2
    exact h5
  have h6 : (↑C_fin.card : ENat) = C_f.encard := by
    have h61 : (C_fin : Set (ℝ × ℝ)).encard = ↑C_fin.card := by
      simp
    have h62 : (C_fin : Set (ℝ × ℝ)) = C_f := hC_fin_eq
    rw [←h62, h61]
  have h7 : (D : Set (ℝ × ℝ)).encard ≤ (N : ENat) * C_f.encard := by
    calc (D : Set (ℝ × ℝ)).encard
      ≤ (N : ENat) * ↑C_fin.card := h3
    _ = (N : ENat) * C_f.encard := by rw [h6]
  have h8 : ENat.toENNReal (D : Set (ℝ × ℝ)).encard ≤
      (N : ENNReal) * ENat.toENNReal C_f.encard := by
    exact_mod_cast h7
  have h9 : ENat.toENNReal C_f.encard = (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal) := by
    rw [hC_f_eq] <;> rfl
  have h10 : ENat.toENNReal (Metric.externalCoveringNumber δ.toNNReal A) ≤
      ENat.toENNReal (D : Set (ℝ × ℝ)).encard := by
    exact_mod_cast h1
  have h11 : ENat.toENNReal (D : Set (ℝ × ℝ)).encard ≤
      ((Nat.ceil (2 * (K + 1)) + 1)^2 : ENNReal) *
      (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal) := by
    have h12 : ENat.toENNReal (D : Set (ℝ × ℝ)).encard ≤
        (N : ENNReal) * ENat.toENNReal C_f.encard := by exact_mod_cast h7
    rw [h9] at h12
    simpa [hN_eq] using h12
  exact h10.trans h11

/-- If `A` is a `(δ, s, C)`-set in `ℝ×ℝ` and `f` is 1-Lipschitz moving every
    point by at most `K*δ`, then `f '' A` is a `(δ, s, C')`-set with
    `C' = C * N * (K+2)` where `N = (ceil(2*(K+1))+1)^2`. -/
lemma IsDeltaSSet.perturbation_prod
    {δ s C : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 < C)
    {A : Set (ℝ × ℝ)} (hA_bdd : Bornology.IsBounded A)
    (hA : IsDeltaSSet δ s C A)
    {f : ℝ × ℝ → ℝ × ℝ} (hf_lip : LipschitzWith 1 f)
    {K : ℝ} (hK_nonneg : 0 ≤ K)
    (h_move : ∀ x ∈ A, dist x (f x) ≤ K * δ) :
    IsDeltaSSet δ s (C * ((Nat.ceil (2 * (K + 1)) + 1)^2 : ℝ) * (K + 2)) (f '' A) := by
  let N : ℕ := (Nat.ceil (2 * (K + 1)) + 1)^2
  have hN_eq : (N : ENNReal) = ((Nat.ceil (2 * (K + 1)) + 1)^2 : ENNReal) := by simp [N]
  have hC'_pos : 0 < C * (N : ℝ) * (K + 2) := by positivity
  have h_image_nonempty : (f '' A).Nonempty := hA.1.image f

  have h_covering_A : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
      ((Nat.ceil (2 * (K + 1)) + 1)^2 : ENNReal) *
      (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal) :=
    covering_estimate_perturbation_prod hδ hK_nonneg hA_bdd hf_lip h_move

  have h_lip_cover : ∀ (S : Set (ℝ × ℝ)),
      (Metric.externalCoveringNumber δ.toNNReal (f '' S) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
    intro S
    exact_mod_cast externalCovering_number_lipschitz_image hf_lip

  have h_main : ∀ (x : ℝ × ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal ((f '' A) ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal (C * (N : ℝ) * (K + 2)) *
        (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal) := by
    intro x r hδ_le_r
    have h_r_pos : 0 < r := by linarith
    have hKδ_nonneg : 0 ≤ K * δ := by positivity
    have h1 : (f '' A) ∩ Metric.closedBall x r ⊆ f '' (A ∩ Metric.closedBall x (r + K * δ)) := by
      intro y hy
      rcases hy with ⟨⟨a, ha, rfl⟩, hball⟩
      have h_dist : dist a x ≤ r + K * δ := by
        have h6 : dist a (f a) ≤ K * δ := h_move a ha
        have h7 : dist (f a) x ≤ r := hball
        calc dist a x
          ≤ dist a (f a) + dist (f a) x := dist_triangle _ _ _
        _ ≤ K * δ + r := by linarith
        _ = r + K * δ := by ring
      exact ⟨a, ⟨ha, h_dist⟩, rfl⟩
    have h2 : (Metric.externalCoveringNumber δ.toNNReal ((f '' A) ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x (r + K * δ)) : ENNReal) := by
      have h_mono : (Metric.externalCoveringNumber δ.toNNReal ((f '' A) ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal (f '' (A ∩ Metric.closedBall x (r + K * δ))) : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set h1
      calc (Metric.externalCoveringNumber δ.toNNReal ((f '' A) ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber δ.toNNReal (f '' (A ∩ Metric.closedBall x (r + K * δ))) : ENNReal) := h_mono
      _ ≤ (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x (r + K * δ)) : ENNReal) :=
          h_lip_cover (A ∩ Metric.closedBall x (r + K * δ))
    have h4 : δ ≤ r + K * δ := by
      have h5 : 0 ≤ K * δ := hKδ_nonneg
      have h6 : δ ≤ r := hδ_le_r
      linarith
    have h5 : (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x (r + K * δ)) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (r + K * δ)) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) :=
      hA.2.2.2.2 x (r + K * δ) h4
    have h6 : (ENNReal.ofReal (r + K * δ)) ^ s ≤ ENNReal.ofReal ((K + 2) * r ^ s) := by
      have h7 : r + K * δ ≤ (K + 1) * r := by
        have h8 : δ ≤ r := hδ_le_r
        nlinarith
      have h9 : 0 ≤ r + K * δ := by positivity
      have h10 : ENNReal.ofReal (r + K * δ) ^ s ≤ ENNReal.ofReal ((K + 1) * r) ^ s := by
        gcongr <;> exact h7
      have h11 : ENNReal.ofReal ((K + 1) * r) ^ s = ENNReal.ofReal (((K + 1) * r) ^ s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hs]
      rw [h11] at h10
      have h12 : ((K + 1) * r) ^ s ≤ (K + 2) * r ^ s := by
        have h13 : 0 ≤ K + 1 := by linarith
        have h14 : (K + 1) ^ s ≤ K + 2 := by
          have h15 : (K + 1) ^ s ≤ (K + 1) ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le <;> linarith
          have h16 : (K + 1) ^ (1 : ℝ) = K + 1 := by simp
          rw [h16] at h15
          linarith
        have h17 : ((K + 1) * r) ^ s = (K + 1) ^ s * r ^ s := by
          rw [Real.mul_rpow (by linarith) (by linarith)]
        rw [h17]
        have h18 : 0 ≤ r ^ s := by positivity
        nlinarith
      exact h10.trans (ENNReal.ofReal_le_ofReal h12)
    have h_posC : 0 ≤ C := by linarith
    have h_posr : 0 ≤ r := by linarith
    have h_eq1 : ENNReal.ofReal C * ENNReal.ofReal ((K + 2) * r ^ s) * (N : ENNReal) =
        ENNReal.ofReal (C * (N : ℝ) * (K + 2)) * (ENNReal.ofReal r) ^ s := by
      calc
        ENNReal.ofReal C * ENNReal.ofReal ((K + 2) * r ^ s) * (N : ENNReal)
          = ENNReal.ofReal C * ENNReal.ofReal ((K + 2) * r ^ s) * ENNReal.ofReal (N : ℝ) := by
            rw [show (N : ENNReal) = ENNReal.ofReal (N : ℝ) by simp]
        _ = ENNReal.ofReal (C * ((K + 2) * r ^ s) * (N : ℝ)) := by
            rw [← ENNReal.ofReal_mul h_posC, ← ENNReal.ofReal_mul (by positivity)] <;> ring
        _ = ENNReal.ofReal (C * (N : ℝ) * (K + 2) * r ^ s) := by ring_nf
        _ = ENNReal.ofReal (C * (N : ℝ) * (K + 2)) * ENNReal.ofReal (r ^ s) := by
            rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
        _ = ENNReal.ofReal (C * (N : ℝ) * (K + 2)) * (ENNReal.ofReal r) ^ s := by
            rw [ENNReal.ofReal_rpow_of_nonneg h_posr hs]
    calc (Metric.externalCoveringNumber δ.toNNReal ((f '' A) ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x (r + K * δ)) : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (r + K * δ)) ^ s * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := h5
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((K + 2) * r ^ s) * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
        gcongr <;> exact h6
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((K + 2) * r ^ s) *
          (((Nat.ceil (2 * (K + 1)) + 1)^2 : ENNReal) *
          (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal)) := by
        gcongr <;> exact h_covering_A
    _ = ENNReal.ofReal (C * (N : ℝ) * (K + 2)) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal) := by
        have h_comm : ENNReal.ofReal C * ENNReal.ofReal ((K + 2) * r ^ s) *
            (((Nat.ceil (2 * (K + 1)) + 1)^2 : ENNReal) *
            (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal)) =
            (ENNReal.ofReal C * ENNReal.ofReal ((K + 2) * r ^ s) * (N : ENNReal)) *
            (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal) := by
          rw [hN_eq] <;> ring
        rw [h_comm, h_eq1] <;> ring
  have hC'_pos2 : 0 < C * ((Nat.ceil (2 * (K + 1)) + 1)^2 : ℝ) * (K + 2) := by
    have h_eq : C * ((Nat.ceil (2 * (K + 1)) + 1)^2 : ℝ) * (K + 2) = C * (N : ℝ) * (K + 2) := by
      simp [N] <;> ring
    rw [h_eq]
    exact hC'_pos
  have h_main2 : ∀ (x : ℝ × ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal ((f '' A) ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal (C * ((Nat.ceil (2 * (K + 1)) + 1)^2 : ℝ) * (K + 2)) *
        (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal (f '' A) : ENNReal) := by
    intro x r hδ_le_r
    have h_goal := h_main x r hδ_le_r
    have h_eq_const : C * (N : ℝ) * (K + 2) = C * ((Nat.ceil (2 * (K + 1)) + 1)^2 : ℝ) * (K + 2) := by
      simp [N] <;> ring
    simpa [h_eq_const] using h_goal
  exact ⟨h_image_nonempty, hδ, hC'_pos2, hs, h_main2⟩

end DirecretisedFurstenbergEstimate
