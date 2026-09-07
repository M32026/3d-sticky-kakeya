module

/-
  Common coarse tubes bound.

  Given a (Δ,s,C)-set C_Q of Δ-separated affine lines, and two points p,q at
  distance r ∈ (0,2], the number of tubes in C_Q passing within δ of both p
  and q is bounded by:

    K_pack * C * 600^s * (Δ/r)^s * |C_Q|

  Proof:
    1. Geometric lemma: any tube near both p,q lies within 200*(δ+δ/r) of the
       unique line ℓ₀ through p,q.
    2. Since δ ≤ Δ and r ≤ 2, this radius is ≤ 600*Δ/r.
    3. S-set property: Ncover_Δ(C_Q ∩ B(ℓ₀,ρ)) ≤ C * ρ^s * Ncover_Δ(C_Q).
    4. Packing bound: |S| ≤ K_pack * Ncover_Δ(S).
    5. Combine: |S| ≤ K_pack * C * (600*Δ/r)^s * |C_Q|.

  This is the key input to the Cauchy-Schwarz step in the 2s incidence bound.

  Whiteprint node: appendix_a_alternative / common_coarse_tubes_bound
  Dependencies: PackingBound, CommonTubeGeometricLemma
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeGeometricLemma
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.H2_Migration_Adapters
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.CommonCoarseTubesBound

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MainAppendix
open DirecretisedFurstenbergEstimate.Phase2

/-- Common coarse tubes bound: number of tubes in C_Q near both p and q
    at near scale δ ≤ Δ. Constant is 600^s. -/
lemma common_coarse_tubes_bound
    {Δ δ s C : ℝ} {C_Q : Finset AffineLine}
    (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hs_pos : 0 < s) (hC_pos : 0 < C)
    (hC_Q_sset : IsDeltaSSet Δ s C (C_Q : Set AffineLine))
    (hC_Q_sep : SeparatedAt Δ (C_Q : Set AffineLine))
    (p q : EuclideanPlane)
    (hr_pos : 0 < dist p q)
    (hr_le_2 : dist p q ≤ 2)
    (hp_bound : ‖p‖ ≤ 2) (hq_bound : ‖q‖ ≤ 2) :
    ((C_Q.filter (fun (c : AffineLine) =>
        p ∈ Metric.cthickening δ (c.1 : Set EuclideanPlane) ∧
        q ∈ Metric.cthickening δ (c.1 : Set EuclideanPlane))).card : ℝ)
    ≤ (affineLine_packing_constant : ℝ) * C * (600 : ℝ)^s *
        (Δ / dist p q)^s * (C_Q.card : ℝ) := by
  let P_pred : AffineLine → Prop := fun (c : AffineLine) =>
    p ∈ Metric.cthickening δ (c.1 : Set EuclideanPlane) ∧
    q ∈ Metric.cthickening δ (c.1 : Set EuclideanPlane)
  let S : Finset AffineLine := C_Q.filter P_pred
  let r : ℝ := dist p q
  have h_goal : (S.card : ℝ) ≤ (affineLine_packing_constant : ℝ) * C * (600 : ℝ)^s *
      (Δ / r)^s * (C_Q.card : ℝ) := by
    by_cases hS_empty : S = ∅
    · have h : (S.card : ℝ) = 0 := by
        rw [hS_empty]; simp
      rw [h]
      positivity
    · -- S nonempty
      have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
      rcases hS_nonempty with ⟨ℓstar, hℓstar⟩
      have hℓstar_near_p : p ∈ Metric.cthickening δ (ℓstar.1 : Set EuclideanPlane) :=
        (Finset.mem_filter.mp hℓstar).2.1
      have hℓstar_near_q : q ∈ Metric.cthickening δ (ℓstar.1 : Set EuclideanPlane) :=
        (Finset.mem_filter.mp hℓstar).2.2
      have h_mono1 : Metric.cthickening δ (ℓstar.1 : Set EuclideanPlane) ⊆
          Metric.cthickening (2 * δ) (ℓstar.1 : Set EuclideanPlane) :=
        Metric.cthickening_mono (by linarith) (ℓstar.1 : Set EuclideanPlane)
      have hℓstar_near_p2 : p ∈ Metric.cthickening (2 * δ) (ℓstar.1 : Set EuclideanPlane) :=
        h_mono1 hℓstar_near_p
      have hℓstar_near_q2 : q ∈ Metric.cthickening (2 * δ) (ℓstar.1 : Set EuclideanPlane) :=
        h_mono1 hℓstar_near_q
      rcases common_tube_geometric_lemma_bounded δ hδ_pos p q hr_pos
          hp_bound hq_bound ℓstar hℓstar_near_p2 hℓstar_near_q2
        with ⟨ℓ₀, hp_in, hq_in, _⟩
      let ρ : ℝ := 200 * (δ + δ / r)
      have h_r_pos : 0 < r := hr_pos
      have h_r_le2 : r ≤ 2 := hr_le_2
      have h1_le : 1 ≤ 2 / r := by
        have h : r ≤ 2 := h_r_le2
        have h' : 0 < r := h_r_pos
        calc 1 = r / r := by field_simp [h'.ne'] <;> ring
             _ ≤ 2 / r := by gcongr
      have h_sum_le : 1 + 1 / r ≤ 3 / r := by
        calc 1 + 1 / r ≤ 2 / r + 1 / r := by gcongr
                     _ = 3 / r := by ring
      have hρ_bound : ρ ≤ 600 * Δ / r := by
        dsimp only [ρ]
        calc 200 * (δ + δ / r)
          ≤ 200 * (Δ + Δ / r) := by gcongr <;> linarith
        _ = 200 * Δ * (1 + 1 / r) := by ring
        _ ≤ 200 * Δ * (3 / r) := by gcongr
        _ = 600 * Δ / r := by ring
      let ρ' : ℝ := max ρ Δ
      have hρ'_ge_D : Δ ≤ ρ' := le_max_right _ _
      have hρ'_bound : ρ' ≤ 600 * Δ / r := by
        have h1 : ρ ≤ 600 * Δ / r := hρ_bound
        have h2 : Δ ≤ 600 * Δ / r := by
          have h5 : 1 ≤ 600 / r := by
            calc 1 ≤ 2 / r := h1_le
                 _ ≤ 600 / r := by gcongr <;> norm_num
          calc Δ = Δ * 1 := by ring
               _ ≤ Δ * (600 / r) := by gcongr
               _ = 600 * Δ / r := by ring
        exact max_le h1 h2
      have h_contain_all : (S : Set AffineLine) ⊆ Metric.closedBall ℓ₀ ρ' := by
        intro c hc
        have hc_near_p : p ∈ Metric.cthickening δ (c.1 : Set EuclideanPlane) :=
          (Finset.mem_filter.mp hc).2.1
        have hc_near_q : q ∈ Metric.cthickening δ (c.1 : Set EuclideanPlane) :=
          (Finset.mem_filter.mp hc).2.2
        have h_mono2 : Metric.cthickening δ (c.1 : Set EuclideanPlane) ⊆
            Metric.cthickening (2 * δ) (c.1 : Set EuclideanPlane) :=
          Metric.cthickening_mono (by linarith) (c.1 : Set EuclideanPlane)
        have hc_near_p2 : p ∈ Metric.cthickening (2 * δ) (c.1 : Set EuclideanPlane) :=
          h_mono2 hc_near_p
        have hc_near_q2 : q ∈ Metric.cthickening (2 * δ) (c.1 : Set EuclideanPlane) :=
          h_mono2 hc_near_q
        rcases common_tube_geometric_lemma_bounded δ hδ_pos p q hr_pos
            hp_bound hq_bound c hc_near_p2 hc_near_q2
          with ⟨ℓ₁, hp1, hq1, hdist⟩
        have hne : p ≠ q := dist_pos.mp hr_pos
        have h_eq : ℓ₁ = ℓ₀ := affineLine_unique_of_two_points hne hp1 hq1 hp_in hq_in
        rw [h_eq] at hdist
        have h6 : dist c ℓ₀ ≤ ρ := by simpa [ρ] using hdist
        exact le_trans h6 (le_max_left _ _)
      let δnn : NNReal := Δ.toNNReal
      have hδnn_eq : (δnn : ℝ) = Δ := by
        simp [δnn, Real.toNNReal_of_nonneg hΔ_pos.le]
      have hS_sub_CQ : (S : Set AffineLine) ⊆ (C_Q : Set AffineLine) := by
        intro c hc; exact (Finset.mem_filter.mp hc).1
      have hS_sep : Set.Pairwise (S : Set AffineLine) (fun x y => (δnn : ℝ) ≤ dist x y) := by
        simpa [hδnn_eq] using hC_Q_sep.mono hS_sub_CQ
      have h_pack' : ∀ (z : AffineLine) (T : Set AffineLine),
          Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
          T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
          T.Finite ∧ T.encard ≤ (affineLine_packing_constant : ENat) := by
        intro z T hT_sep hT_sub
        have hT_sep' : Set.Pairwise T (fun x y => Δ ≤ dist x y) := by
          simpa [hδnn_eq] using hT_sep
        have hT_sub' : T ⊆ Metric.closedBall z (2 * Δ) := by
          simpa [hδnn_eq] using hT_sub
        exact affineLine_packing_bound Δ hΔ_pos hT_sep' z hT_sub'
      have hS_sub : (S : Set AffineLine) ⊆ (C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ' := by
        intro c hc
        exact ⟨hS_sub_CQ hc, h_contain_all hc⟩
      have h_cov_mono : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) ≤
          Metric.externalCoveringNumber δnn ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ') := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set hS_sub
      have h_sset' := hC_Q_sset.2.2.2.2 ℓ₀ ρ' hρ'_ge_D
      have h_cov_CQ : (Metric.externalCoveringNumber δnn (C_Q : Set AffineLine) : ENNReal) ≤
          (C_Q.card : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_le_encard_self (C_Q : Set AffineLine)
      have hcov_fin : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) < ⊤ := by
        have h1 : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) ≤
            (S.card : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_le_encard_self (S : Set AffineLine)
        have h2 : (S.card : ENNReal) < ⊤ := by simp
        exact lt_of_le_of_lt h1 h2
      have h_card : (S.card : ENNReal) ≤
          (affineLine_packing_constant : ENNReal) *
            (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) := by
        have h : ((S : Set AffineLine).encard : ENNReal) ≤ (affineLine_packing_constant : ENNReal) *
            (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) :=
          separated_set_card_le_covering hS_sep affineLine_packing_constant h_pack' hcov_fin
        have h_eq : ((S : Set AffineLine).encard : ENNReal) = (S.card : ENNReal) := by simp
        rw [h_eq] at h
        exact h
      have hs_nonneg : 0 ≤ s := by linarith
      have hρ'_nonneg : 0 ≤ ρ' := by positivity
      have h_rpow : (ENNReal.ofReal ρ') ^ s = ENNReal.ofReal (ρ' ^ s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hρ'_nonneg hs_nonneg]
      have h4 : ρ' ^ s ≤ (600 * Δ / r) ^ s := by
        gcongr <;> linarith
      have h_main : (S.card : ENNReal) ≤
          ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * (600 : ℝ)^s *
            (Δ / r)^s * (C_Q.card : ℝ)) := by
        calc (S.card : ENNReal)
          ≤ (affineLine_packing_constant : ENNReal) *
              (Metric.externalCoveringNumber δnn (S : Set AffineLine)) := h_card
        _ ≤ (affineLine_packing_constant : ENNReal) *
              (Metric.externalCoveringNumber δnn
                ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ')) := by gcongr
        _ ≤ (affineLine_packing_constant : ENNReal) *
              (ENNReal.ofReal C * (ENNReal.ofReal ρ') ^ s *
                Metric.externalCoveringNumber δnn (C_Q : Set AffineLine)) := by gcongr
        _ = (affineLine_packing_constant : ENNReal) *
              (ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) *
                Metric.externalCoveringNumber δnn (C_Q : Set AffineLine)) := by
          rw [h_rpow]
        _ ≤ (affineLine_packing_constant : ENNReal) *
              (ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) * (C_Q.card : ENNReal)) := by gcongr
        _ = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s * (C_Q.card : ℝ)) := by
          have h_pos_a : 0 ≤ (affineLine_packing_constant : ℝ) := by positivity
          have h_pos_b : 0 ≤ C := hC_pos.le
          have h_pos_c : 0 ≤ ρ' ^ s := by positivity
          have h_pos_d : 0 ≤ (C_Q.card : ℝ) := by positivity
          have h_eq1 : (affineLine_packing_constant : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) * (C_Q.card : ENNReal)) =
              (affineLine_packing_constant : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) * (C_Q.card : ENNReal) := by ring
          rw [h_eq1]
          have h_step1 : (affineLine_packing_constant : ENNReal) = ENNReal.ofReal (affineLine_packing_constant : ℝ) := by simp
          have h_step2 : (C_Q.card : ENNReal) = ENNReal.ofReal (C_Q.card : ℝ) := by simp
          rw [h_step1, h_step2]
          have h1 : ENNReal.ofReal (affineLine_packing_constant : ℝ) * ENNReal.ofReal C = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C) := by
            rw [← ENNReal.ofReal_mul h_pos_a]
          have h2 : 0 ≤ (affineLine_packing_constant : ℝ) * C := by positivity
          have h3 : ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C) * ENNReal.ofReal (ρ' ^ s) = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s) := by
            rw [← ENNReal.ofReal_mul h2]
          have h4 : 0 ≤ (affineLine_packing_constant : ℝ) * C * ρ' ^ s := by positivity
          have h5 : ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s) * ENNReal.ofReal (C_Q.card : ℝ) = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s * (C_Q.card : ℝ)) := by
            rw [← ENNReal.ofReal_mul h4]
          rw [h1, h3, h5] <;> ring
        _ ≤ ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * (600 : ℝ)^s *
              (Δ / r)^s * (C_Q.card : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          have h_pos1 : 0 ≤ (affineLine_packing_constant : ℝ) := by positivity
          have h_pos2 : 0 ≤ C := hC_pos.le
          have h_pos3 : 0 ≤ (C_Q.card : ℝ) := by positivity
          have h : (affineLine_packing_constant : ℝ) * C * ρ' ^ s * (C_Q.card : ℝ) ≤
              (affineLine_packing_constant : ℝ) * C * ((600 * Δ / r) ^ s) * (C_Q.card : ℝ) := by
            gcongr
          have h5 : (600 * Δ / r) ^ s = (600 : ℝ)^s * (Δ / r)^s := by
            have h6 : 0 ≤ Δ / r := by positivity
            have h7 : (600 * (Δ / r)) ^ s = (600 : ℝ)^s * (Δ / r)^s := by
              exact Real.mul_rpow (by positivity) h6
            have h8 : 600 * Δ / r = 600 * (Δ / r) := by ring
            rw [h8]; exact h7
          rw [h5] at h
          have h9 : (affineLine_packing_constant : ℝ) * C * ((600 : ℝ)^s * (Δ / r)^s) * (C_Q.card : ℝ) =
              (affineLine_packing_constant : ℝ) * C * (600 : ℝ)^s * (Δ / r)^s * (C_Q.card : ℝ) := by ring
          rw [h9] at h; exact h
      have h_product_nonneg : 0 ≤ (affineLine_packing_constant : ℝ) * C *
          (600 : ℝ)^s * (Δ / r)^s * (C_Q.card : ℝ) := by positivity
      have h_main' : ENNReal.ofReal (S.card : ℝ) ≤ ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * (600 : ℝ)^s * (Δ / r)^s * (C_Q.card : ℝ)) := by
        exact_mod_cast h_main
      exact (ENNReal.ofReal_le_ofReal_iff h_product_nonneg).mp h_main'
  simpa [S, P_pred] using h_goal

/-- Common coarse tubes bound with near scale 2Δ (e.g. point within δ of a fine
    tube which is within Δ of the coarse tube). Constant is 1200^s. -/
lemma common_coarse_tubes_bound_2Δ
    {Δ s C : ℝ} {C_Q : Finset AffineLine}
    (hΔ_pos : 0 < Δ)
    (hs_pos : 0 < s) (hC_pos : 0 < C)
    (hC_Q_sset : IsDeltaSSet Δ s C (C_Q : Set AffineLine))
    (hC_Q_sep : SeparatedAt Δ (C_Q : Set AffineLine))
    (p q : EuclideanPlane)
    (hr_pos : 0 < dist p q)
    (hr_le_2 : dist p q ≤ 2)
    (hp_bound : ‖p‖ ≤ 2) (hq_bound : ‖q‖ ≤ 2) :
    ((C_Q.filter (fun (c : AffineLine) =>
        p ∈ Metric.cthickening (2 * Δ) (c.1 : Set EuclideanPlane) ∧
        q ∈ Metric.cthickening (2 * Δ) (c.1 : Set EuclideanPlane))).card : ℝ)
    ≤ (affineLine_packing_constant : ℝ) * C * (1200 : ℝ)^s *
        (Δ / dist p q)^s * (C_Q.card : ℝ) := by
  let P_pred : AffineLine → Prop := fun (c : AffineLine) =>
    p ∈ Metric.cthickening (2 * Δ) (c.1 : Set EuclideanPlane) ∧
    q ∈ Metric.cthickening (2 * Δ) (c.1 : Set EuclideanPlane)
  let S : Finset AffineLine := C_Q.filter P_pred
  let r : ℝ := dist p q
  have h_goal : (S.card : ℝ) ≤ (affineLine_packing_constant : ℝ) * C * (1200 : ℝ)^s *
      (Δ / r)^s * (C_Q.card : ℝ) := by
    by_cases hS_empty : S = ∅
    · have h : (S.card : ℝ) = 0 := by rw [hS_empty]; simp
      rw [h]; positivity
    · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
      rcases hS_nonempty with ⟨ℓstar, hℓstar⟩
      have hℓstar_near_p : p ∈ Metric.cthickening (2 * Δ) (ℓstar.1 : Set EuclideanPlane) :=
        (Finset.mem_filter.mp hℓstar).2.1
      have hℓstar_near_q : q ∈ Metric.cthickening (2 * Δ) (ℓstar.1 : Set EuclideanPlane) :=
        (Finset.mem_filter.mp hℓstar).2.2
      have h_mono1 : Metric.cthickening (2 * Δ) (ℓstar.1 : Set EuclideanPlane) ⊆
          Metric.cthickening (2 * (2 * Δ)) (ℓstar.1 : Set EuclideanPlane) :=
        Metric.cthickening_mono (by linarith) (ℓstar.1 : Set EuclideanPlane)
      have hℓstar_near_p2 : p ∈ Metric.cthickening (2 * (2 * Δ)) (ℓstar.1 : Set EuclideanPlane) :=
        h_mono1 hℓstar_near_p
      have hℓstar_near_q2 : q ∈ Metric.cthickening (2 * (2 * Δ)) (ℓstar.1 : Set EuclideanPlane) :=
        h_mono1 hℓstar_near_q
      rcases common_tube_geometric_lemma_bounded (2 * Δ) (by positivity) p q hr_pos
          hp_bound hq_bound ℓstar hℓstar_near_p2 hℓstar_near_q2
        with ⟨ℓ₀, hp_in, hq_in, _⟩
      let ρ : ℝ := 200 * (2 * Δ + (2 * Δ) / r)
      have h_r_pos : 0 < r := hr_pos
      have h_r_le2 : r ≤ 2 := hr_le_2
      have h1_le : 1 ≤ 2 / r := by
        have h' : 0 < r := h_r_pos
        calc 1 = r / r := by field_simp [h'.ne'] <;> ring
             _ ≤ 2 / r := by gcongr
      have h_sum_le : 1 + 1 / r ≤ 3 / r := by
        calc 1 + 1 / r ≤ 2 / r + 1 / r := by gcongr
                     _ = 3 / r := by ring
      have hρ_bound : ρ ≤ 1200 * Δ / r := by
        dsimp only [ρ]
        calc 200 * (2 * Δ + (2 * Δ) / r)
          = 400 * Δ * (1 + 1 / r) := by ring
        _ ≤ 400 * Δ * (3 / r) := by gcongr
        _ = 1200 * Δ / r := by ring
      let ρ' : ℝ := max ρ Δ
      have hρ'_ge_D : Δ ≤ ρ' := le_max_right _ _
      have hρ'_bound : ρ' ≤ 1200 * Δ / r := by
        have h1 : ρ ≤ 1200 * Δ / r := hρ_bound
        have h2 : Δ ≤ 1200 * Δ / r := by
          have h5 : 1 ≤ 1200 / r := by
            calc 1 ≤ 2 / r := h1_le
                 _ ≤ 1200 / r := by gcongr <;> norm_num
          calc Δ = Δ * 1 := by ring
               _ ≤ Δ * (1200 / r) := by gcongr
               _ = 1200 * Δ / r := by ring
        exact max_le h1 h2
      have h_contain_all : (S : Set AffineLine) ⊆ Metric.closedBall ℓ₀ ρ' := by
        intro c hc
        have hc_near_p : p ∈ Metric.cthickening (2 * Δ) (c.1 : Set EuclideanPlane) :=
          (Finset.mem_filter.mp hc).2.1
        have hc_near_q : q ∈ Metric.cthickening (2 * Δ) (c.1 : Set EuclideanPlane) :=
          (Finset.mem_filter.mp hc).2.2
        have h_mono2 : Metric.cthickening (2 * Δ) (c.1 : Set EuclideanPlane) ⊆
            Metric.cthickening (2 * (2 * Δ)) (c.1 : Set EuclideanPlane) :=
          Metric.cthickening_mono (by linarith) (c.1 : Set EuclideanPlane)
        have hc_near_p2 : p ∈ Metric.cthickening (2 * (2 * Δ)) (c.1 : Set EuclideanPlane) :=
          h_mono2 hc_near_p
        have hc_near_q2 : q ∈ Metric.cthickening (2 * (2 * Δ)) (c.1 : Set EuclideanPlane) :=
          h_mono2 hc_near_q
        rcases common_tube_geometric_lemma_bounded (2 * Δ) (by positivity) p q hr_pos
            hp_bound hq_bound c hc_near_p2 hc_near_q2
          with ⟨ℓ₁, hp1, hq1, hdist⟩
        have hne : p ≠ q := dist_pos.mp hr_pos
        have h_eq : ℓ₁ = ℓ₀ := affineLine_unique_of_two_points hne hp1 hq1 hp_in hq_in
        rw [h_eq] at hdist
        have h6 : dist c ℓ₀ ≤ ρ := by simpa [ρ] using hdist
        exact le_trans h6 (le_max_left _ _)
      let δnn : NNReal := Δ.toNNReal
      have hδnn_eq : (δnn : ℝ) = Δ := by
        simp [δnn, Real.toNNReal_of_nonneg hΔ_pos.le]
      have hS_sub_CQ : (S : Set AffineLine) ⊆ (C_Q : Set AffineLine) := by
        intro c hc; exact (Finset.mem_filter.mp hc).1
      have hS_sep : Set.Pairwise (S : Set AffineLine) (fun x y => (δnn : ℝ) ≤ dist x y) := by
        simpa [hδnn_eq] using hC_Q_sep.mono hS_sub_CQ
      have h_pack' : ∀ (z : AffineLine) (T : Set AffineLine),
          Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
          T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
          T.Finite ∧ T.encard ≤ (affineLine_packing_constant : ENat) := by
        intro z T hT_sep hT_sub
        have hT_sep' : Set.Pairwise T (fun x y => Δ ≤ dist x y) := by
          simpa [hδnn_eq] using hT_sep
        have hT_sub' : T ⊆ Metric.closedBall z (2 * Δ) := by
          simpa [hδnn_eq] using hT_sub
        exact affineLine_packing_bound Δ hΔ_pos hT_sep' z hT_sub'
      have hS_sub : (S : Set AffineLine) ⊆ (C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ' := by
        intro c hc
        exact ⟨hS_sub_CQ hc, h_contain_all hc⟩
      have h_cov_mono : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) ≤
          Metric.externalCoveringNumber δnn ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ') := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set hS_sub
      have h_sset' := hC_Q_sset.2.2.2.2 ℓ₀ ρ' hρ'_ge_D
      have h_cov_CQ : (Metric.externalCoveringNumber δnn (C_Q : Set AffineLine) : ENNReal) ≤
          (C_Q.card : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_le_encard_self (C_Q : Set AffineLine)
      have hcov_fin : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) < ⊤ := by
        have h1 : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) ≤
            (S.card : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_le_encard_self (S : Set AffineLine)
        have h2 : (S.card : ENNReal) < ⊤ := by simp
        exact lt_of_le_of_lt h1 h2
      have h_card : (S.card : ENNReal) ≤
          (affineLine_packing_constant : ENNReal) *
            (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) := by
        have h : ((S : Set AffineLine).encard : ENNReal) ≤ (affineLine_packing_constant : ENNReal) *
            (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) :=
          separated_set_card_le_covering hS_sep affineLine_packing_constant h_pack' hcov_fin
        have h_eq : ((S : Set AffineLine).encard : ENNReal) = (S.card : ENNReal) := by simp
        rw [h_eq] at h
        exact h
      have hs_nonneg : 0 ≤ s := by linarith
      have hρ'_nonneg : 0 ≤ ρ' := by positivity
      have h_rpow : (ENNReal.ofReal ρ') ^ s = ENNReal.ofReal (ρ' ^ s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hρ'_nonneg hs_nonneg]
      have h4 : ρ' ^ s ≤ (1200 * Δ / r) ^ s := by gcongr <;> linarith
      have h_main : (S.card : ENNReal) ≤
          ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * (1200 : ℝ)^s *
            (Δ / r)^s * (C_Q.card : ℝ)) := by
        calc (S.card : ENNReal)
          ≤ (affineLine_packing_constant : ENNReal) *
              (Metric.externalCoveringNumber δnn (S : Set AffineLine)) := h_card
        _ ≤ (affineLine_packing_constant : ENNReal) *
              (Metric.externalCoveringNumber δnn
                ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ')) := by gcongr
        _ ≤ (affineLine_packing_constant : ENNReal) *
              (ENNReal.ofReal C * (ENNReal.ofReal ρ') ^ s *
                Metric.externalCoveringNumber δnn (C_Q : Set AffineLine)) := by gcongr
        _ = (affineLine_packing_constant : ENNReal) *
              (ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) *
                Metric.externalCoveringNumber δnn (C_Q : Set AffineLine)) := by
          rw [h_rpow]
        _ ≤ (affineLine_packing_constant : ENNReal) *
              (ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) * (C_Q.card : ENNReal)) := by gcongr
        _ = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s * (C_Q.card : ℝ)) := by
          have h_pos_a : 0 ≤ (affineLine_packing_constant : ℝ) := by positivity
          have h_pos_b : 0 ≤ C := hC_pos.le
          have h_pos_c : 0 ≤ ρ' ^ s := by positivity
          have h_pos_d : 0 ≤ (C_Q.card : ℝ) := by positivity
          have h_eq1 : (affineLine_packing_constant : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) * (C_Q.card : ENNReal)) =
              (affineLine_packing_constant : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) * (C_Q.card : ENNReal) := by ring
          rw [h_eq1]
          have h_step1 : (affineLine_packing_constant : ENNReal) = ENNReal.ofReal (affineLine_packing_constant : ℝ) := by simp
          have h_step2 : (C_Q.card : ENNReal) = ENNReal.ofReal (C_Q.card : ℝ) := by simp
          rw [h_step1, h_step2]
          have h1 : ENNReal.ofReal (affineLine_packing_constant : ℝ) * ENNReal.ofReal C = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C) := by
            rw [← ENNReal.ofReal_mul h_pos_a]
          have h2 : 0 ≤ (affineLine_packing_constant : ℝ) * C := by positivity
          have h3 : ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C) * ENNReal.ofReal (ρ' ^ s) = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s) := by
            rw [← ENNReal.ofReal_mul h2]
          have h4 : 0 ≤ (affineLine_packing_constant : ℝ) * C * ρ' ^ s := by positivity
          have h5 : ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s) * ENNReal.ofReal (C_Q.card : ℝ) = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s * (C_Q.card : ℝ)) := by
            rw [← ENNReal.ofReal_mul h4]
          rw [h1, h3, h5] <;> ring
        _ ≤ ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * (1200 : ℝ)^s *
              (Δ / r)^s * (C_Q.card : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          have h_pos1 : 0 ≤ (affineLine_packing_constant : ℝ) := by positivity
          have h_pos2 : 0 ≤ C := hC_pos.le
          have h_pos3 : 0 ≤ (C_Q.card : ℝ) := by positivity
          have h : (affineLine_packing_constant : ℝ) * C * ρ' ^ s * (C_Q.card : ℝ) ≤
              (affineLine_packing_constant : ℝ) * C * ((1200 * Δ / r) ^ s) * (C_Q.card : ℝ) := by
            gcongr
          have h5 : (1200 * Δ / r) ^ s = (1200 : ℝ)^s * (Δ / r)^s := by
            have h6 : 0 ≤ Δ / r := by positivity
            have h7 : (1200 * (Δ / r)) ^ s = (1200 : ℝ)^s * (Δ / r)^s := by
              exact Real.mul_rpow (by positivity) h6
            have h8 : 1200 * Δ / r = 1200 * (Δ / r) := by ring
            rw [h8]; exact h7
          rw [h5] at h
          have h9 : (affineLine_packing_constant : ℝ) * C * ((1200 : ℝ)^s * (Δ / r)^s) * (C_Q.card : ℝ) =
              (affineLine_packing_constant : ℝ) * C * (1200 : ℝ)^s * (Δ / r)^s * (C_Q.card : ℝ) := by ring
          rw [h9] at h; exact h
      have h_product_nonneg : 0 ≤ (affineLine_packing_constant : ℝ) * C *
          (1200 : ℝ)^s * (Δ / r)^s * (C_Q.card : ℝ) := by positivity
      have h_main' : ENNReal.ofReal (S.card : ℝ) ≤ ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * (1200 : ℝ)^s * (Δ / r)^s * (C_Q.card : ℝ)) := by
        exact_mod_cast h_main
      exact (ENNReal.ofReal_le_ofReal_iff h_product_nonneg).mp h_main'
  simpa [S, P_pred] using h_goal

/-- Generalized common coarse tubes bound with near scale k·Δ.
    Requires dist(p,q) ≤ 3. Constant is (800*k)^s. -/
lemma common_coarse_tubes_bound_kΔ
    {Δ s C : ℝ} {C_Q : Finset AffineLine}
    {k : ℝ} (hk : 1 ≤ k)
    (hΔ_pos : 0 < Δ)
    (hs_pos : 0 < s) (hC_pos : 0 < C)
    (hC_Q_sset : IsDeltaSSet Δ s C (C_Q : Set AffineLine))
    (hC_Q_sep : SeparatedAt Δ (C_Q : Set AffineLine))
    (p q : EuclideanPlane)
    (hr_pos : 0 < dist p q)
    (hr_le_3 : dist p q ≤ 3)
    (hp_bound : ‖p‖ ≤ 2) (hq_bound : ‖q‖ ≤ 2) :
    ((C_Q.filter (fun (c : AffineLine) =>
        p ∈ Metric.cthickening (k * Δ) (c.1 : Set EuclideanPlane) ∧
        q ∈ Metric.cthickening (k * Δ) (c.1 : Set EuclideanPlane))).card : ℝ)
    ≤ (affineLine_packing_constant : ℝ) * C * ((800 * k) : ℝ)^s *
        (Δ / dist p q)^s * (C_Q.card : ℝ) := by
  let P_pred : AffineLine → Prop := fun (c : AffineLine) =>
    p ∈ Metric.cthickening (k * Δ) (c.1 : Set EuclideanPlane) ∧
    q ∈ Metric.cthickening (k * Δ) (c.1 : Set EuclideanPlane)
  let S : Finset AffineLine := C_Q.filter P_pred
  let r : ℝ := dist p q
  have h_k_nonneg : 0 ≤ k := by linarith
  have h_goal : (S.card : ℝ) ≤ (affineLine_packing_constant : ℝ) * C * ((800 * k) : ℝ)^s *
      (Δ / r)^s * (C_Q.card : ℝ) := by
    by_cases hS_empty : S = ∅
    · have h : (S.card : ℝ) = 0 := by rw [hS_empty]; simp
      rw [h]; positivity
    · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
      rcases hS_nonempty with ⟨ℓstar, hℓstar⟩
      have hℓstar_near_p : p ∈ Metric.cthickening (k * Δ) (ℓstar.1 : Set EuclideanPlane) :=
        (Finset.mem_filter.mp hℓstar).2.1
      have hℓstar_near_q : q ∈ Metric.cthickening (k * Δ) (ℓstar.1 : Set EuclideanPlane) :=
        (Finset.mem_filter.mp hℓstar).2.2
      have h_scale1 : k * Δ ≤ 2 * (k * Δ) := by
        have h : 0 ≤ k * Δ := mul_nonneg h_k_nonneg hΔ_pos.le
        linarith
      have h_mono1 : Metric.cthickening (k * Δ) (ℓstar.1 : Set EuclideanPlane) ⊆
          Metric.cthickening (2 * (k * Δ)) (ℓstar.1 : Set EuclideanPlane) :=
        Metric.cthickening_mono h_scale1 (ℓstar.1 : Set EuclideanPlane)
      have hℓstar_near_p2 : p ∈ Metric.cthickening (2 * (k * Δ)) (ℓstar.1 : Set EuclideanPlane) :=
        h_mono1 hℓstar_near_p
      have hℓstar_near_q2 : q ∈ Metric.cthickening (2 * (k * Δ)) (ℓstar.1 : Set EuclideanPlane) :=
        h_mono1 hℓstar_near_q
      rcases common_tube_geometric_lemma_bounded (k * Δ) (by positivity) p q hr_pos
          hp_bound hq_bound ℓstar hℓstar_near_p2 hℓstar_near_q2
        with ⟨ℓ₀, hp_in, hq_in, _⟩
      let ρ : ℝ := 200 * (k * Δ + (k * Δ) / r)
      have h_r_pos : 0 < r := hr_pos
      have h1_le : 1 ≤ 3 / r := by
        have h' : 0 < r := h_r_pos
        calc 1 = r / r := by field_simp [h'.ne'] <;> ring
             _ ≤ 3 / r := by gcongr <;> linarith
      have h_sum_le : 1 + 1 / r ≤ 4 / r := by
        calc 1 + 1 / r ≤ 3 / r + 1 / r := by gcongr
             _ = 4 / r := by ring
      have hρ_bound : ρ ≤ (800 * k) * Δ / r := by
        dsimp only [ρ]
        calc 200 * (k * Δ + (k * Δ) / r)
          = 200 * k * Δ * (1 + 1 / r) := by ring
        _ ≤ 200 * k * Δ * (4 / r) := by gcongr
        _ = (800 * k) * Δ / r := by ring
      let ρ' : ℝ := max ρ Δ
      have hρ'_ge_D : Δ ≤ ρ' := le_max_right _ _
      have hρ'_bound : ρ' ≤ (800 * k) * Δ / r := by
        have h1 : ρ ≤ (800 * k) * Δ / r := hρ_bound
        have h2 : Δ ≤ (800 * k) * Δ / r := by
          have h5 : 1 ≤ (800 * k) / r := by
            calc 1 ≤ 3 / r := h1_le
                 _ ≤ (800 * k) / r := by gcongr <;> nlinarith
          calc Δ = Δ * 1 := by ring
               _ ≤ Δ * ((800 * k) / r) := by gcongr
               _ = (800 * k) * Δ / r := by ring
        exact max_le h1 h2
      have h_contain_all : (S : Set AffineLine) ⊆ Metric.closedBall ℓ₀ ρ' := by
        intro c hc
        have hc_near_p : p ∈ Metric.cthickening (k * Δ) (c.1 : Set EuclideanPlane) :=
          (Finset.mem_filter.mp hc).2.1
        have hc_near_q : q ∈ Metric.cthickening (k * Δ) (c.1 : Set EuclideanPlane) :=
          (Finset.mem_filter.mp hc).2.2
        have h_mono2 : Metric.cthickening (k * Δ) (c.1 : Set EuclideanPlane) ⊆
            Metric.cthickening (2 * (k * Δ)) (c.1 : Set EuclideanPlane) :=
          Metric.cthickening_mono h_scale1 (c.1 : Set EuclideanPlane)
        have hc_near_p2 : p ∈ Metric.cthickening (2 * (k * Δ)) (c.1 : Set EuclideanPlane) :=
          h_mono2 hc_near_p
        have hc_near_q2 : q ∈ Metric.cthickening (2 * (k * Δ)) (c.1 : Set EuclideanPlane) :=
          h_mono2 hc_near_q
        rcases common_tube_geometric_lemma_bounded (k * Δ) (by positivity) p q hr_pos
            hp_bound hq_bound c hc_near_p2 hc_near_q2
          with ⟨ℓ₁, hp1, hq1, hdist⟩
        have hne : p ≠ q := dist_pos.mp hr_pos
        have h_eq : ℓ₁ = ℓ₀ := affineLine_unique_of_two_points hne hp1 hq1 hp_in hq_in
        rw [h_eq] at hdist
        have h6 : dist c ℓ₀ ≤ ρ := by simpa [ρ] using hdist
        exact le_trans h6 (le_max_left _ _)
      let δnn : NNReal := Δ.toNNReal
      have hδnn_eq : (δnn : ℝ) = Δ := by
        simp [δnn, Real.toNNReal_of_nonneg hΔ_pos.le]
      have hS_sub_CQ : (S : Set AffineLine) ⊆ (C_Q : Set AffineLine) := by
        intro c hc; exact (Finset.mem_filter.mp hc).1
      have hS_sep : Set.Pairwise (S : Set AffineLine) (fun x y => (δnn : ℝ) ≤ dist x y) := by
        simpa [hδnn_eq] using hC_Q_sep.mono hS_sub_CQ
      have h_pack' : ∀ (z : AffineLine) (T : Set AffineLine),
          Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
          T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
          T.Finite ∧ T.encard ≤ (affineLine_packing_constant : ENat) := by
        intro z T hT_sep hT_sub
        have hT_sep' : Set.Pairwise T (fun x y => Δ ≤ dist x y) := by
          simpa [hδnn_eq] using hT_sep
        have hT_sub' : T ⊆ Metric.closedBall z (2 * Δ) := by
          simpa [hδnn_eq] using hT_sub
        exact affineLine_packing_bound Δ hΔ_pos hT_sep' z hT_sub'
      have hS_sub : (S : Set AffineLine) ⊆ (C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ' := by
        intro c hc
        exact ⟨hS_sub_CQ hc, h_contain_all hc⟩
      have h_cov_mono : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) ≤
          Metric.externalCoveringNumber δnn ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ') := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set hS_sub
      have h_sset' := hC_Q_sset.2.2.2.2 ℓ₀ ρ' hρ'_ge_D
      have h_cov_CQ : (Metric.externalCoveringNumber δnn (C_Q : Set AffineLine) : ENNReal) ≤
          (C_Q.card : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_le_encard_self (C_Q : Set AffineLine)
      have hcov_fin : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) < ⊤ := by
        have h1 : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) ≤
            (S.card : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_le_encard_self (S : Set AffineLine)
        have h2 : (S.card : ENNReal) < ⊤ := by simp
        exact lt_of_le_of_lt h1 h2
      have h_card : (S.card : ENNReal) ≤
          (affineLine_packing_constant : ENNReal) *
            (Metric.externalCoveringNumber δnn (S : Set AffineLine)) := by
        have h : ((S : Set AffineLine).encard : ENNReal) ≤ (affineLine_packing_constant : ENNReal) *
            (Metric.externalCoveringNumber δnn (S : Set AffineLine)) :=
          separated_set_card_le_covering hS_sep affineLine_packing_constant h_pack' hcov_fin
        have h_eq : ((S : Set AffineLine).encard : ENNReal) = (S.card : ENNReal) := by simp
        rw [h_eq] at h
        exact h
      have hs_nonneg : 0 ≤ s := by linarith
      have hρ'_nonneg : 0 ≤ ρ' := by positivity
      have h_rpow : (ENNReal.ofReal ρ') ^ s = ENNReal.ofReal (ρ' ^ s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hρ'_nonneg hs_nonneg]
      have h4 : ρ' ^ s ≤ ((800 * k) * Δ / r) ^ s := by gcongr <;> linarith
      have h_main : (S.card : ENNReal) ≤
          ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ((800 * k) : ℝ)^s *
            (Δ / r)^s * (C_Q.card : ℝ)) := by
        calc (S.card : ENNReal)
          ≤ (affineLine_packing_constant : ENNReal) *
              (Metric.externalCoveringNumber δnn (S : Set AffineLine)) := h_card
        _ ≤ (affineLine_packing_constant : ENNReal) *
              (Metric.externalCoveringNumber δnn
                ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ')) := by gcongr
        _ ≤ (affineLine_packing_constant : ENNReal) *
              (ENNReal.ofReal C * (ENNReal.ofReal ρ') ^ s *
                Metric.externalCoveringNumber δnn (C_Q : Set AffineLine)) := by gcongr
        _ = (affineLine_packing_constant : ENNReal) *
              (ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) *
                Metric.externalCoveringNumber δnn (C_Q : Set AffineLine)) := by
          rw [h_rpow]
        _ ≤ (affineLine_packing_constant : ENNReal) *
              (ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) * (C_Q.card : ENNReal)) := by gcongr
        _ = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s * (C_Q.card : ℝ)) := by
          have h_pos_a : 0 ≤ (affineLine_packing_constant : ℝ) := by positivity
          have h_pos_b : 0 ≤ C := hC_pos.le
          have h_pos_c : 0 ≤ ρ' ^ s := by positivity
          have h_pos_d : 0 ≤ (C_Q.card : ℝ) := by positivity
          have h_eq1 : (affineLine_packing_constant : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) * (C_Q.card : ENNReal)) =
              (affineLine_packing_constant : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (ρ' ^ s) * (C_Q.card : ENNReal) := by ring
          rw [h_eq1]
          have h_step1 : (affineLine_packing_constant : ENNReal) = ENNReal.ofReal (affineLine_packing_constant : ℝ) := by simp
          have h_step2 : (C_Q.card : ENNReal) = ENNReal.ofReal (C_Q.card : ℝ) := by simp
          rw [h_step1, h_step2]
          have h1 : ENNReal.ofReal (affineLine_packing_constant : ℝ) * ENNReal.ofReal C = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C) := by
            rw [← ENNReal.ofReal_mul h_pos_a]
          have h2 : 0 ≤ (affineLine_packing_constant : ℝ) * C := by positivity
          have h3 : ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C) * ENNReal.ofReal (ρ' ^ s) = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s) := by
            rw [← ENNReal.ofReal_mul h2]
          have h4 : 0 ≤ (affineLine_packing_constant : ℝ) * C * ρ' ^ s := by positivity
          have h5 : ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s) * ENNReal.ofReal (C_Q.card : ℝ) = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ρ' ^ s * (C_Q.card : ℝ)) := by
            rw [← ENNReal.ofReal_mul h4]
          rw [h1, h3, h5] <;> ring
        _ ≤ ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ((800 * k) : ℝ)^s *
              (Δ / r)^s * (C_Q.card : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          have h_pos1 : 0 ≤ (affineLine_packing_constant : ℝ) := by positivity
          have h_pos2 : 0 ≤ C := hC_pos.le
          have h_pos3 : 0 ≤ (C_Q.card : ℝ) := by positivity
          have h : (affineLine_packing_constant : ℝ) * C * ρ' ^ s * (C_Q.card : ℝ) ≤
              (affineLine_packing_constant : ℝ) * C * ((800 * k) * Δ / r) ^ s * (C_Q.card : ℝ) := by
            gcongr
          have h5 : (800 * k) * Δ / r = (800 * k) * (Δ / r) := by ring
          have h6 : 0 ≤ Δ / r := by positivity
          have h7 : ((800 * k) * (Δ / r)) ^ s = ((800 * k) : ℝ)^s * (Δ / r)^s := by
            exact Real.mul_rpow (by positivity) h6
          rw [h5, h7] at h
          have h9 : (affineLine_packing_constant : ℝ) * C * (((800 * k) : ℝ)^s * (Δ / r)^s) * (C_Q.card : ℝ) =
              (affineLine_packing_constant : ℝ) * C * ((800 * k) : ℝ)^s * (Δ / r)^s * (C_Q.card : ℝ) := by ring
          rw [h9] at h; exact h
      have h_product_nonneg : 0 ≤ (affineLine_packing_constant : ℝ) * C *
          ((800 * k) : ℝ)^s * (Δ / r)^s * (C_Q.card : ℝ) := by positivity
      have h_main' : ENNReal.ofReal (S.card : ℝ) ≤ ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C * ((800 * k) : ℝ)^s * (Δ / r)^s * (C_Q.card : ℝ)) := by
        exact_mod_cast h_main
      exact (ENNReal.ofReal_le_ofReal_iff h_product_nonneg).mp h_main'
  simpa [S, P_pred] using h_goal

end DirecretisedFurstenbergEstimate.AppendixA.CommonCoarseTubesBound

namespace DirecretisedFurstenbergEstimate.AppendixA3

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MainAppendix
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter point_in_square_close_to_center)
open DirecretisedFurstenbergEstimate.AppendixA.CommonCoarseTubesBound

/-- Distance transfer: if p is within δ of fine tube T, and T is within Δ of
    coarse tube boldT in AffineLine metric, with ‖p‖ ≤ √2 and δ ≤ Δ ≤ 1/2,
    then p is within 5Δ of boldT. -/
lemma point_near_coarse_from_fine
    {Δ δ : ℝ} (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hΔ_le_half : Δ ≤ 1 / 2)
    {p : EuclideanPlane} (hp_bound : ‖p‖ ≤ Real.sqrt 2)
    {T boldT : AffineLine}
    (hp_near_T : p ∈ Metric.cthickening (2 * δ) (T.1 : Set EuclideanPlane))
    (C : ℝ) (hC_pos : 0 < C)
    (hT_near_boldT : dist T boldT ≤ C * Δ) :
    p ∈ Metric.cthickening ((5 * C + 2) * Δ) (boldT.1 : Set EuclideanPlane) := by
  let p_T : EuclideanPlane := EuclideanGeometry.orthogonalProjection T.1 p
  have hpT_mem : p_T ∈ T.1 := EuclideanGeometry.orthogonalProjection_mem p
  have h_edist : Metric.infEDist p (T.1 : Set EuclideanPlane) ≤ ENNReal.ofReal (2 * δ) :=
    Metric.mem_cthickening_iff.mp hp_near_T
  have h_dist_pT : dist p p_T ≤ 2 * δ := by
    have h_eq : dist p p_T = Metric.infDist p (T.1 : Set EuclideanPlane) :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist T.1 p
    rw [h_eq]
    have h_conv : Metric.infDist p (T.1 : Set EuclideanPlane) = ENNReal.toReal (Metric.infEDist p (T.1 : Set EuclideanPlane)) := by rfl
    rw [h_conv]
    have h_mono : ENNReal.toReal (Metric.infEDist p (T.1 : Set EuclideanPlane)) ≤ ENNReal.toReal (ENNReal.ofReal (2 * δ)) :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h_edist
    rw [ENNReal.toReal_ofReal (show 0 ≤ 2 * δ by linarith)] at h_mono
    exact h_mono
  have h_norm_diff : ‖p - p_T‖ ≤ 2 * δ := by simpa [dist_eq_norm] using h_dist_pT
  have h_pT_norm : ‖p_T‖ ≤ Real.sqrt 2 + 2 * δ := by
    calc ‖p_T‖ ≤ ‖p‖ + ‖p - p_T‖ := norm_le_insert _ _
         _ ≤ Real.sqrt 2 + 2 * δ := by
           have hpb : ‖p‖ ≤ Real.sqrt 2 := hp_bound
           linarith [hpb, h_norm_diff]
  have h_offset_norm : ‖T.offset‖ ≤ ‖p_T‖ := by
    have h1 : dist (0 : EuclideanPlane) T.offset = Metric.infDist (0 : EuclideanPlane) (T.1 : Set EuclideanPlane) :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist T.1 0
    have h2 : Metric.infDist (0 : EuclideanPlane) (T.1 : Set EuclideanPlane) ≤ dist (0 : EuclideanPlane) p_T := by
      have h3 : dist (0 : EuclideanPlane) p_T ∈ {d : ℝ | ∃ (y : EuclideanPlane), y ∈ (T.1 : Set EuclideanPlane) ∧ dist (0 : EuclideanPlane) y ≤ d} := by
        exact ⟨p_T, hpT_mem, by rfl⟩
      exact Metric.infDist_le_dist_of_mem hpT_mem
    have h4 : dist (0 : EuclideanPlane) T.offset ≤ dist (0 : EuclideanPlane) p_T := by
      rw [h1]; exact h2
    simpa [dist_eq_norm] using h4
  let v := p_T - T.offset
  have hv_in_dir : v ∈ T.1.direction :=
    AffineSubspace.vsub_mem_direction hpT_mem T.offset_mem
  have hv_norm : ‖v‖ ≤ 4 := by
    -- p - p_T is orthogonal to T.direction
    have h_orth1 : p - p_T ∈ T.1.directionᗮ := by
      have h_proj : EuclideanGeometry.orthogonalProjection T.1 p = p_T := rfl
      exact (EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem.mp h_proj).2
    -- T.offset is orthogonal to T.direction (since 0 - T.offset is)
    have h_orth2 : (0 : EuclideanPlane) - T.offset ∈ T.1.directionᗮ := by
      have h_proj : EuclideanGeometry.orthogonalProjection T.1 (0 : EuclideanPlane) = T.offset := rfl
      exact (EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem.mp h_proj).2
    have h_orth2' : T.offset ∈ T.1.directionᗮ := by
      have h3 : (0 : EuclideanPlane) - T.offset = -T.offset := by simp
      rw [h3] at h_orth2
      have h4 : -(-T.offset) ∈ T.1.directionᗮ := T.1.directionᗮ.neg_mem h_orth2
      have h5 : -(-T.offset) = T.offset := by simp
      rw [h5] at h4
      exact h4
    -- inner v (p - p_T) = 0 and inner v T.offset = 0
    have h_inner1 : inner ℝ v (p - p_T) = 0 := by
      rw [Submodule.mem_orthogonal'] at h_orth1
      have h := h_orth1 v hv_in_dir
      have h_comm : inner ℝ (p - p_T) v = inner ℝ v (p - p_T) := real_inner_comm v (p - p_T)
      rw [h_comm] at h
      exact h
    have h_inner2 : inner ℝ v T.offset = 0 := by
      rw [Submodule.mem_orthogonal'] at h_orth2'
      have h := h_orth2' v hv_in_dir
      have h_comm : inner ℝ T.offset v = inner ℝ v T.offset := real_inner_comm v T.offset
      rw [h_comm] at h
      exact h
    let w := T.offset + (p - p_T)
    have h_inner_w : inner ℝ v w = 0 := by
      simp [w, inner_add_right, h_inner2, h_inner1] <;> ring
    have h_eq : p = w + v := by
      simp [w, v, p_T] <;> abel
    have h_pyth : ‖p‖ * ‖p‖ = ‖w‖ * ‖w‖ + ‖v‖ * ‖v‖ := by
      rw [h_eq]
      have h_symm : inner ℝ w v = 0 := by
        have h_comm : inner ℝ v w = inner ℝ w v := real_inner_comm w v
        rw [h_comm] at h_inner_w
        exact h_inner_w
      exact norm_add_sq_eq_norm_sq_add_norm_sq_real h_symm
    have h9 : ‖v‖ * ‖v‖ ≤ ‖p‖ * ‖p‖ := by
      linarith [h_pyth, show 0 ≤ ‖w‖ * ‖w‖ from by positivity]
    have h10 : ‖v‖ ≤ ‖p‖ := by
      nlinarith [norm_nonneg v, norm_nonneg p]
    have h11 : ‖v‖ ≤ Real.sqrt 2 := by
      calc ‖v‖ ≤ ‖p‖ := h10
           _ ≤ Real.sqrt 2 := hp_bound
    have h12 : Real.sqrt 2 ≤ 4 := by
      have h13 : Real.sqrt 2 ≤ Real.sqrt 16 := Real.sqrt_le_sqrt (by norm_num)
      have h14 : Real.sqrt 16 = 4 := by rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    linarith
  let P_T := T.1.direction.starProjection
  let P_C := boldT.1.direction.starProjection
  have hT_sum : ‖P_T - P_C‖ + ‖T.offset - boldT.offset‖ ≤ C * Δ := by
    have h : dist T boldT ≤ C * Δ := hT_near_boldT
    have h_def : dist T boldT = ‖P_T - P_C‖ + ‖T.offset - boldT.offset‖ := by
      simp [AffineLine.dist, P_T, P_C] <;> rfl
    rw [h_def] at h
    exact h
  have h_dir_diff : ‖P_T - P_C‖ ≤ C * Δ := by
    have h_nonneg : 0 ≤ ‖T.offset - boldT.offset‖ := norm_nonneg _
    have h_le : ‖P_T - P_C‖ ≤ ‖P_T - P_C‖ + ‖T.offset - boldT.offset‖ :=
      le_add_of_nonneg_right h_nonneg
    exact le_trans h_le hT_sum
  let v_C := P_C v
  have hvC_in_dir : v_C ∈ boldT.1.direction :=
    Submodule.starProjection_apply_mem boldT.1.direction v
  let q := boldT.offset + v_C
  have hq_mem : q ∈ boldT.1 := by
    have h : v_C +ᵥ boldT.offset ∈ boldT.1 :=
      AffineSubspace.vadd_mem_of_mem_direction hvC_in_dir boldT.offset_mem
    have h_eq : v_C +ᵥ boldT.offset = boldT.offset + v_C := by
      simpa using add_comm v_C boldT.offset
    rw [h_eq] at h
    exact h
  have h_v_diff : ‖v - v_C‖ ≤ 4 * C * Δ := by
    have h1 : v - v_C = (P_T - P_C) v := by
      have h2 : P_T v = v := by
        rw [Submodule.starProjection_eq_self_iff]
        exact hv_in_dir
      simp [v_C, h2] <;> abel
    rw [h1]
    calc ‖(P_T - P_C) v‖ ≤ ‖P_T - P_C‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
         _ ≤ (C * Δ) * ‖v‖ := by gcongr
         _ ≤ (C * Δ) * 4 := by gcongr <;> exact hv_norm
         _ = 4 * C * Δ := by ring
  have h_off_diff : ‖T.offset - boldT.offset‖ ≤ C * Δ := by
    have h_nonneg : 0 ≤ ‖P_T - P_C‖ := norm_nonneg _
    have h_le : ‖T.offset - boldT.offset‖ ≤ ‖P_T - P_C‖ + ‖T.offset - boldT.offset‖ :=
      le_add_of_nonneg_left h_nonneg
    exact le_trans h_le hT_sum
  have h_pT_q : ‖p_T - q‖ ≤ 5 * C * Δ := by
    have h_eq : p_T - q = (T.offset - boldT.offset) + (v - v_C) := by
      simp [p_T, v, q, v_C] <;> abel
    rw [h_eq]
    calc ‖(T.offset - boldT.offset) + (v - v_C)‖
      ≤ ‖T.offset - boldT.offset‖ + ‖v - v_C‖ := norm_add_le _ _
    _ ≤ C * Δ + 4 * C * Δ := by gcongr
    _ = 5 * C * Δ := by ring
  have h_main : Metric.infDist p (boldT.1 : Set EuclideanPlane) ≤ (5 * C + 2) * Δ := by
    have h_infDist_le : Metric.infDist p (boldT.1 : Set EuclideanPlane) ≤ dist p q :=
      Metric.infDist_le_dist_of_mem hq_mem
    calc Metric.infDist p (boldT.1 : Set EuclideanPlane)
      ≤ dist p q := h_infDist_le
    _ = ‖p - q‖ := by rfl
    _ ≤ ‖p - p_T‖ + ‖p_T - q‖ := by
      have h_eq : p - q = (p - p_T) + (p_T - q) := by abel
      rw [h_eq]
      exact norm_add_le _ _
    _ ≤ 2 * δ + 5 * C * Δ := by gcongr
    _ ≤ (5 * C + 2) * Δ := by
      have hδ2 : 2 * δ ≤ 2 * Δ := by gcongr <;> linarith
      linarith
  have h_ne_top : Metric.infEDist p (boldT.1 : Set EuclideanPlane) ≠ ⊤ :=
    Metric.infEDist_ne_top (AffineLine.nonempty boldT)
  have h_edist : Metric.infEDist p (boldT.1 : Set EuclideanPlane) ≤ ENNReal.ofReal ((5 * C + 2) * Δ) := by
    have h_eq : Metric.infEDist p (boldT.1 : Set EuclideanPlane) =
        ENNReal.ofReal (Metric.infDist p (boldT.1 : Set EuclideanPlane)) := by
      simp [Metric.infDist, ENNReal.ofReal_toReal h_ne_top]
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h_main
  exact Metric.mem_cthickening_iff.mpr h_edist

/-- Every coarse tube in C_Q is within 53Δ of the square center.

    Uses H2 pointFiber/InParent: fine tube in same parent cell is within 10Δ
    (inParent_dist_lt_tenDelta), and point_near_coarse_from_fine with C=10
    gives 52Δ, plus ≤Δ center distance. -/
lemma coarse_tube_near_square_center
    {Δ δ s t ε : ℝ} {Q : CoarseSquare Δ}
    (sd : A2_SquareData Δ δ s t ε Q)
    (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hΔ_le_half : Δ ≤ 1 / 2) :
    ∀ (boldT : CoarseTube), boldT ∈ sd.C_Q →
      squareCenter Δ Q ∈ Metric.cthickening (53 * Δ) (boldT.1 : Set EuclideanPlane) := by
  intro boldT hboldT
  have hH2 : (sd.H_Q : ℝ) ≤ ∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ) := by
    have h_orig := sd.hH2 boldT hboldT
    have h_cast : (↑(∑ p ∈ sd.P_Q, (pointFiber Δ hΔ_pos sd.T_Q p boldT).card) : ℝ) =
        ∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ) := by
      rw [Nat.cast_sum]
    rw [h_cast] at h_orig
    exact h_orig
  have hH_Q_ge_one : (1 : ℝ) ≤ sd.H_Q := sd.hH_Q_ge_one
  have h_sum_pos : 0 < ∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ) := by
    have h : (1 : ℝ) ≤ (∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ)) := by
      calc (1 : ℝ) ≤ sd.H_Q := hH_Q_ge_one
           _ ≤ (∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ)) := hH2
    exact lt_of_lt_of_le (by norm_num) h
  have h_exists : ∃ (p : EuclideanPlane), p ∈ sd.P_Q ∧
      (pointFiber Δ hΔ_pos sd.T_Q p boldT).Nonempty := by
    by_contra h
    push Not at h
    have h_sum_zero : ∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have h9 : pointFiber Δ hΔ_pos sd.T_Q p boldT = ∅ := h p hp
      rw [h9] <;> simp
    rw [h_sum_zero] at h_sum_pos
    simpa using h_sum_pos
  rcases h_exists with ⟨p, hp_in_PQ, h_fiber_nonempty⟩
  rcases h_fiber_nonempty with ⟨T, hT_in_fiber⟩
  have hT_in_Tp : T ∈ sd.T_Q p := (Finset.mem_filter.mp hT_in_fiber).1
  have hInParent : InParent Δ hΔ_pos T boldT := (Finset.mem_filter.mp hT_in_fiber).2
  have h_bounds_T := sd.h_slope_bound p hp_in_PQ T hT_in_Tp
  have h_bounds_boldT : (LemmaE.getDirV boldT) 1 ≠ 0 ∧ |tubeSlope boldT| ≤ 1 ∧ |tubeIntercept boldT| ≤ 3 :=
    ⟨sd.hC_Q_v boldT hboldT, sd.hC_Q_slope_bound boldT hboldT, sd.hC_Q_b boldT hboldT⟩
  have h_dist_T : dist T boldT < 10 * Δ :=
    H2Migration.inParent_dist_lt_tenDelta Δ hΔ_pos T boldT hInParent
      h_bounds_T.1 h_bounds_boldT.1 h_bounds_T.2.1 h_bounds_boldT.2.1
      h_bounds_T.2.2 h_bounds_boldT.2.2
  have h_dist_T_le : dist T boldT ≤ 10 * Δ := h_dist_T.le
  have hp_near_T : p ∈ Metric.cthickening (2 * δ) (T.1 : Set EuclideanPlane) :=
    sd.h_inc p hp_in_PQ T hT_in_Tp
  have hp_in_square : p ∈ squareSet Δ Q := sd.hP_Q_in_square hp_in_PQ
  have hp_in_ball : ‖p‖ ≤ Real.sqrt 2 := by
    have h1 : p ∈ Metric.closedBall (0 : EuclideanPlane) (Real.sqrt 2) := sd.hP_Q_in_ball hp_in_PQ
    simpa [Metric.mem_closedBall] using h1
  have hp_near_boldT : p ∈ Metric.cthickening ((5 * (10 : ℝ) + 2) * Δ) (boldT.1 : Set EuclideanPlane) :=
    point_near_coarse_from_fine hΔ_pos hδ_pos hδ_le_Δ hΔ_le_half hp_in_ball
      hp_near_T (10 : ℝ) (by norm_num) h_dist_T_le
  have hp_near_boldT' : p ∈ Metric.cthickening (52 * Δ) (boldT.1 : Set EuclideanPlane) := by
    have h_eq : (5 * (10 : ℝ) + 2) * Δ = 52 * Δ := by ring
    rw [h_eq] at hp_near_boldT
    exact hp_near_boldT
  have h_center_dist : dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 :=
    point_in_square_close_to_center hΔ_pos Q p hp_in_square
  have h_sqrt_le : Real.sqrt 2 * Δ / 2 ≤ Δ := by
    have h1 : Real.sqrt 2 ≤ 2 := by
      have h2 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      have h3 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    have h4 : 0 ≤ Δ := by linarith
    nlinarith
  have h_center_near : Metric.infDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane) ≤ 53 * Δ := by
    have h_infDist_p : Metric.infDist p (boldT.1 : Set EuclideanPlane) ≤ 52 * Δ := by
      have h_edist : Metric.infEDist p (boldT.1 : Set EuclideanPlane) ≤ ENNReal.ofReal (52 * Δ) :=
        Metric.mem_cthickening_iff.mp hp_near_boldT'
      have h_ne_top : Metric.infEDist p (boldT.1 : Set EuclideanPlane) ≠ ⊤ :=
        Metric.infEDist_ne_top (AffineLine.nonempty boldT)
      have h_conv : Metric.infDist p (boldT.1 : Set EuclideanPlane) =
          ENNReal.toReal (Metric.infEDist p (boldT.1 : Set EuclideanPlane)) := by rfl
      rw [h_conv]
      have h_mono : ENNReal.toReal (Metric.infEDist p (boldT.1 : Set EuclideanPlane)) ≤ ENNReal.toReal (ENNReal.ofReal (52 * Δ)) :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h_edist
      rw [ENNReal.toReal_ofReal (show 0 ≤ 52 * Δ from by positivity)] at h_mono
      exact h_mono
    calc Metric.infDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane)
      ≤ Metric.infDist p (boldT.1 : Set EuclideanPlane) + dist (squareCenter Δ Q) p :=
        Metric.infDist_le_infDist_add_dist
    _ ≤ 52 * Δ + Real.sqrt 2 * Δ / 2 := add_le_add h_infDist_p (by rwa [dist_comm])
    _ ≤ 52 * Δ + Δ := by gcongr <;> exact h_sqrt_le
    _ = 53 * Δ := by ring
  have h_ne_top2 : Metric.infEDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane) ≠ ⊤ :=
    Metric.infEDist_ne_top (AffineLine.nonempty boldT)
  have h_edist2 : Metric.infEDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane) ≤ ENNReal.ofReal (53 * Δ) := by
    have h_eq : Metric.infEDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane) =
        ENNReal.ofReal (Metric.infDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane)) := by
      simp [Metric.infDist, ENNReal.ofReal_toReal h_ne_top2]
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h_center_near
  exact Metric.mem_cthickening_iff.mpr h_edist2

/-- Intersection format common tubes bound for coarse scale. -/
lemma coarse_intersection_common_tubes_bound
    {Δ s C_T M k : ℝ} (hk : 1 ≤ k)
    (hΔ_pos : 0 < Δ) (hs_pos : 0 < s)
    (hC_T_pos : 0 < C_T) (hM_pos : 0 < M)
    {Q R : CoarseSquare Δ}
    (hQ_bound : ‖squareCenter Δ Q‖ ≤ 2)
    (hR_bound : ‖squareCenter Δ R‖ ≤ 2)
    (hd : Δ ≤ dist (squareCenter Δ Q) (squareCenter Δ R))
    (hr_le_3 : dist (squareCenter Δ Q) (squareCenter Δ R) ≤ 3)
    (Tp : CoarseSquare Δ → Finset CoarseTube)
    (hTpQ_sset : IsDeltaSSet Δ s C_T (Tp Q : Set CoarseTube))
    (hTpQ_near : ∀ ℓ ∈ Tp Q,
      squareCenter Δ Q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane))
    (hTpQ_card : (Tp Q).card ≤ M)
    (hTpQ_sep : SeparatedAt Δ (Tp Q : Set CoarseTube))
    (hTpR_near : ∀ ℓ ∈ Tp R,
      squareCenter Δ R ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane)) :
    ((Tp Q) ∩ (Tp R)).card ≤
      (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * M *
        (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := by
  let p := squareCenter Δ Q
  let q := squareCenter Δ R
  have h_subset : (Tp Q) ∩ (Tp R) ⊆
      (Tp Q).filter (fun ℓ => q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane)) := by
    intro ℓ hℓ
    have hℓQ : ℓ ∈ Tp Q := (Finset.mem_inter.mp hℓ).1
    have hℓR : ℓ ∈ Tp R := (Finset.mem_inter.mp hℓ).2
    have h_near_q : q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane) :=
      hTpR_near ℓ hℓR
    exact Finset.mem_filter.mpr ⟨hℓQ, h_near_q⟩
  have h_card_le : ((Tp Q) ∩ (Tp R)).card ≤
      ((Tp Q).filter (fun ℓ => q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane))).card :=
    Finset.card_le_card h_subset
  have h_card_le' : (((Tp Q) ∩ (Tp R)).card : ℝ) ≤
      (((Tp Q).filter (fun ℓ => q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane))).card : ℝ) := by
    exact_mod_cast h_card_le
  have h_near_p : ∀ ℓ ∈ (Tp Q).filter (fun ℓ => q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane)),
      p ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane) := by
    intro ℓ hℓ
    have hℓQ : ℓ ∈ Tp Q := (Finset.mem_filter.mp hℓ).1
    exact hTpQ_near ℓ hℓQ
  let F := (Tp Q).filter (fun ℓ =>
    p ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane) ∧
    q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane))
  have hF_eq : F = (Tp Q).filter (fun ℓ => q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane)) := by
    ext ℓ
    simp only [F, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h_near_p ℓ (Finset.mem_filter.mpr ⟨h1, h2⟩), h2⟩
  have h_ne : p ≠ q := by
    intro h
    have h_dist : dist p q = 0 := by rw [h] <;> simp
    have h_contra : Δ ≤ dist p q := hd
    rw [h_dist] at h_contra
    linarith [hΔ_pos]
  have h_bound_F : (F.card : ℝ) ≤
      (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s *
        (Δ / dist p q)^s * ((Tp Q).card : ℝ) := by
    simpa [F] using common_coarse_tubes_bound_kΔ hk hΔ_pos hs_pos hC_T_pos
      hTpQ_sset hTpQ_sep p q (dist_pos.mpr h_ne) hr_le_3 hQ_bound hR_bound
  have h_card_Q : ((Tp Q).card : ℝ) ≤ M := hTpQ_card
  have h_bound_M : (((Tp Q).filter (fun ℓ => q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane))).card : ℝ) ≤
      (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * M *
        (Δ / dist p q)^s := by
    have h1 : (F.card : ℝ) = (((Tp Q).filter (fun ℓ => q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set EuclideanPlane))).card : ℝ) := by
      rw [hF_eq]
    rw [← h1]
    calc (F.card : ℝ)
      ≤ (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * (Δ / dist p q)^s * ((Tp Q).card : ℝ) := h_bound_F
    _ = (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * ((Tp Q).card : ℝ) * (Δ / dist p q)^s := by ring
    _ ≤ (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * M * (Δ / dist p q)^s := by
      gcongr <;> linarith
  exact le_trans h_card_le' h_bound_M

end DirecretisedFurstenbergEstimate.AppendixA3
