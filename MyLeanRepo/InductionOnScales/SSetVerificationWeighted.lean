module

public import MyLeanRepo.InductionOnScales.SSetVerification
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Weighted SSet Verification

Variant of `coarse_sset_verification` that supports per-point variable
multiplicity lower bounds `m₁(p)` and weighted popularity `L`.

The weighted popularity of a coarse tube U is:
  wpop(U) = ∑_{p : U ∈ coarseFamily(p)} m₁(p)

The proof selects p₀ to maximize m₁(p₀) * |coarseFamily(p₀) ∩ B|,
and the relation is simply `L ≥ M * |P| / (K * |TΔ|)`.

This eliminates the need for a uniform m₁, reducing the polylog exponent.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

/-- Weighted version of coarse SSet verification. Supports per-point variable
multiplicity lower bounds via weighted popularity. -/
theorem coarse_sset_verification_weighted
    {n m : ℕ} (hnm : m ≤ n)
    {α : Type*} [DecidableEq α]
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM_pos : 0 < M)
    (TΔ : Finset (DyadicTube m)) (hTΔ_nonempty : TΔ.Nonempty)
    (P : Finset α) (hP_nonempty : P.Nonempty)
    (coarseFamily : α → Finset (DyadicTube m))
    (fineFamily : α → Finset (DyadicTube n))
    (m₁ : α → ℕ) (hm₁_pos : ∀ p ∈ P, 0 < m₁ p)
    (L : ℕ) (hL_pos : 0 < L)
    (K : ℝ) (hK : 1 ≤ K)
    (h_coarse_sub : ∀ p ∈ P, coarseFamily p ⊆ TΔ)
    (h_wpop : ∀ U ∈ TΔ,
        ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), (m₁ p : ℝ) ≥ (L : ℝ))
    (h_fine_per_coarse : ∀ p ∈ P, ∀ U ∈ coarseFamily p,
        ((fineFamily p).filter (fun T => T.toSet ⊆ U.toSet)).card ≥ m₁ p)
    (h_fine_sset : ∀ p ∈ P, IsFiniteTubeSSet s C₁ (fineFamily p))
    (h_fine_size : ∀ p ∈ P, (fineFamily p).card = M)
    (h_relation : (L : ℝ) ≥ (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))) :
    IsFiniteTubeSSet s (K * 2 * C₁) TΔ := by
  have h_const : 1 ≤ K * 2 * C₁ := by
    have h1 : 1 ≤ K := hK
    have h2 : 1 ≤ C₁ := hC₁
    nlinarith
  have h_sep : ∀ U ∈ TΔ, ∀ V ∈ TΔ, U ≠ V → dyadicDelta m ≤ tubeParamDist U V := by
    intro U _ V _ hne
    exact coarse_tubes_separation U V hne
  have h_ball : ∀ (center : DyadicTube m) (r : ℝ), dyadicDelta m ≤ r →
      ((TΔ.filter fun T => tubeParamDist T center ≤ r).card : ℝ) ≤
        (K * 2 * C₁) * Real.rpow r s * (TΔ.card : ℝ) := by
    intro center r hr
    let B : Finset (DyadicTube m) := TΔ.filter fun T => tubeParamDist T center ≤ r
    have hB_def : B = TΔ.filter fun T => tubeParamDist T center ≤ r := by rfl
    by_cases hB_empty : B = ∅
    · have hB_card : (B.card : ℝ) = 0 := by
        rw [hB_empty] <;> simp
      rw [hB_card]
      have hr_pos : 0 ≤ r := by linarith [dyadicDelta_pos m]
      have h_rpow : 0 ≤ Real.rpow r s := Real.rpow_nonneg hr_pos s
      have h_pos : 0 ≤ (K * 2 * C₁) * Real.rpow r s * (TΔ.card : ℝ) := by positivity
      exact h_pos
    · have hB_nonempty : B.Nonempty := by
        simpa [hB_def, Finset.nonempty_iff_ne_empty] using hB_empty
      set V' := embedCoarseTube hnm center with hV'_def
      set R := r + dyadicDelta m with hR_def

      -- Weighted popularity for each U ∈ B
      have h_each_wpop : ∀ U ∈ B, (L : ℝ) ≤
          ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), (m₁ p : ℝ) := by
        intro U hU
        have hU_in_TΔ : U ∈ TΔ := (Finset.mem_filter.mp hU).1
        exact h_wpop U hU_in_TΔ

      -- Total weighted incidence: ∑_{U ∈ B} wpop(U)
      have h_total_wpop : (B.card : ℝ) * (L : ℝ) ≤
          ∑ U ∈ B, ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), (m₁ p : ℝ) := by
        have h1 : (B.card : ℝ) * (L : ℝ) = ∑ U ∈ B, (L : ℝ) := by
          simp [Finset.sum_const] <;> ring
        rw [h1]
        apply Finset.sum_le_sum
        exact h_each_wpop

      -- Swap sums: ∑_{U ∈ B} ∑_{p ∈ P.filter(...)} m₁(p) = ∑_{p ∈ P} m₁(p) * |B ∩ coarseFamily(p)|
      have h_swap : ∑ U ∈ B, ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), (m₁ p : ℝ) =
          ∑ p ∈ P, (m₁ p : ℝ) * ((B.filter (fun U => U ∈ coarseFamily p)).card : ℝ) := by
        have h1 : ∀ (U : DyadicTube m),
            ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), (m₁ p : ℝ) =
            ∑ p ∈ P, (if U ∈ coarseFamily p then (m₁ p : ℝ) else 0) := by
          intro U
          rw [Finset.sum_filter]
          <;> rfl
        have h2 : ∑ U ∈ B, ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), (m₁ p : ℝ) =
            ∑ U ∈ B, ∑ p ∈ P, (if U ∈ coarseFamily p then (m₁ p : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro U _
          exact h1 U
        rw [h2]
        have h3 : ∑ U ∈ B, ∑ p ∈ P, (if U ∈ coarseFamily p then (m₁ p : ℝ) else 0) =
            ∑ p ∈ P, ∑ U ∈ B, (if U ∈ coarseFamily p then (m₁ p : ℝ) else 0) := by
          rw [Finset.sum_comm]
        rw [h3]
        apply Finset.sum_congr rfl
        intro p _
        have h4 : ∑ U ∈ B, (if U ∈ coarseFamily p then (m₁ p : ℝ) else 0) =
            (m₁ p : ℝ) * ((B.filter (fun U => U ∈ coarseFamily p)).card : ℝ) := by
          have h5 : ∑ U ∈ B, (if U ∈ coarseFamily p then (m₁ p : ℝ) else 0) =
              ∑ U ∈ B.filter (fun U => U ∈ coarseFamily p), (m₁ p : ℝ) := by
            rw [Finset.sum_ite]
            <;> simp
          rw [h5]
          simp [Finset.sum_const] <;> ring
        rw [h4]

      -- Weighted averaging: exists p₀ with m₁(p₀) * |Bp| ≥ |B| * L / |P|
      have h_avg : ∃ p₀ ∈ P, (m₁ p₀ : ℝ) * ((B.filter (fun U => U ∈ coarseFamily p₀)).card : ℝ) ≥
          (B.card : ℝ) * (L : ℝ) / (P.card : ℝ) := by
        by_contra h
        push Not at h
        have h_sum : ∑ p ∈ P, (m₁ p : ℝ) * ((B.filter (fun U => U ∈ coarseFamily p)).card : ℝ) <
            (B.card : ℝ) * (L : ℝ) := by
          calc ∑ p ∈ P, (m₁ p : ℝ) * ((B.filter (fun U => U ∈ coarseFamily p)).card : ℝ)
            < ∑ p ∈ P, ((B.card : ℝ) * (L : ℝ) / (P.card : ℝ)) :=
              Finset.sum_lt_sum_of_nonempty hP_nonempty (fun p hp => h p hp)
          _ = (P.card : ℝ) * ((B.card : ℝ) * (L : ℝ) / (P.card : ℝ)) := by
            simp [Finset.sum_const] <;> ring
          _ = (B.card : ℝ) * (L : ℝ) := by
            have hP_pos : 0 < (P.card : ℝ) := by exact_mod_cast hP_nonempty.card_pos
            field_simp [hP_pos.ne'] <;> ring
        have h_sum' : ∑ U ∈ B, ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), (m₁ p : ℝ) < (B.card : ℝ) * (L : ℝ) := by
          rw [h_swap]
          exact h_sum
        exact not_le.mpr h_sum' h_total_wpop

      rcases h_avg with ⟨p₀, hp₀, h_p₀_bound⟩

      let Bp : Finset (DyadicTube m) := B.filter (fun U => U ∈ coarseFamily p₀)
      set fineInB : Finset (DyadicTube n) :=
        Finset.biUnion Bp (fun U => (fineFamily p₀).filter (fun T => T.toSet ⊆ U.toSet))
        with hfineInB_def

      have hBp_nonempty : Bp.Nonempty := by
        by_contra h
        have h' : Bp = ∅ := by simpa using h
        have h_empty : (Bp.card : ℝ) = 0 := by
          rw [h'] <;> simp
        rw [h_empty] at h_p₀_bound
        have hB_pos : 0 < (B.card : ℝ) := by exact_mod_cast hB_nonempty.card_pos
        have hP_pos : 0 < (P.card : ℝ) := by exact_mod_cast hP_nonempty.card_pos
        have h_pos : 0 < (B.card : ℝ) * (L : ℝ) / (P.card : ℝ) := by positivity
        linarith

      have h_disj : ∀ U₁ ∈ Bp, ∀ U₂ ∈ Bp, U₁ ≠ U₂ →
          Disjoint ((fineFamily p₀).filter (fun T => T.toSet ⊆ U₁.toSet))
                   ((fineFamily p₀).filter (fun T => T.toSet ⊆ U₂.toSet)) := by
        intro U₁ hU₁ U₂ hU₂ hne
        rw [Finset.disjoint_left]
        intro T hT1 hT2
        have h1 : T.toSet ⊆ U₁.toSet := (Finset.mem_filter.mp hT1).2
        have h2 : T.toSet ⊆ U₂.toSet := (Finset.mem_filter.mp hT2).2
        exact fine_tubes_in_distinct_coarse_disjoint hnm U₁ U₂ hne T h1 h2

      have h_card_union : (fineInB.card : ℝ) =
          ∑ U ∈ Bp, (((fineFamily p₀).filter (fun T => T.toSet ⊆ U.toSet)).card : ℝ) := by
        rw [hfineInB_def, Finset.card_biUnion h_disj] <;> norm_cast

      have h_each : ∀ U ∈ Bp, (((fineFamily p₀).filter (fun T => T.toSet ⊆ U.toSet)).card : ℝ) ≥ (m₁ p₀ : ℝ) := by
        intro U hU
        have hU_in_coarse : U ∈ coarseFamily p₀ := (Finset.mem_filter.mp hU).2
        exact_mod_cast h_fine_per_coarse p₀ hp₀ U hU_in_coarse

      have h_lower : (fineInB.card : ℝ) ≥ (m₁ p₀ : ℝ) * (Bp.card : ℝ) := by
        rw [h_card_union]
        have h : ∑ U ∈ Bp, (((fineFamily p₀).filter (fun T => T.toSet ⊆ U.toSet)).card : ℝ) ≥
            ∑ U ∈ Bp, (m₁ p₀ : ℝ) := Finset.sum_le_sum h_each
        have h2 : ∑ U ∈ Bp, (m₁ p₀ : ℝ) = (m₁ p₀ : ℝ) * (Bp.card : ℝ) := by
          simp [Finset.sum_const] <;> ring
        linarith

      have h_subset : fineInB ⊆ (fineFamily p₀).filter (fun T => tubeParamDist T V' ≤ R) := by
        intro T hT
        rcases Finset.mem_biUnion.mp hT with ⟨U, hU, hT_in⟩
        have hT_in_fine : T ∈ fineFamily p₀ := (Finset.mem_filter.mp hT_in).1
        have hT_cont : T.toSet ⊆ U.toSet := (Finset.mem_filter.mp hT_in).2
        have hU_in_B : U ∈ B := (Finset.mem_filter.mp hU).1
        have hU_dist : tubeParamDist U center ≤ r := (Finset.mem_filter.mp hU_in_B).2
        have hT_dist : tubeParamDist T V' ≤ R :=
          contained_tube_paramDist_bound hnm T U center hT_cont r hU_dist
        exact Finset.mem_filter.mpr ⟨hT_in_fine, hT_dist⟩

      have h1 : dyadicDelta n ≤ dyadicDelta m := by
        have h2 : (n : ℝ) ≥ (m : ℝ) := by exact_mod_cast hnm
        have h3 : (-(n : ℝ)) ≤ (-(m : ℝ)) := by linarith
        have h4 : Real.rpow 2 (-(n : ℝ)) ≤ Real.rpow 2 (-(m : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 from by norm_num) h3
        simpa [dyadicDelta] using h4
      have hR_ge : dyadicDelta n ≤ R := by
        have h3 : dyadicDelta n ≤ dyadicDelta m := h1
        have h4 : dyadicDelta m ≤ R := by
          simp [hR_def] <;> linarith [dyadicDelta_pos m]
        linarith

      rcases h_fine_sset p₀ hp₀ with ⟨_, _, _, _, h_frostman⟩
      have h_sset := h_frostman V' R hR_ge

      have h_upper : (fineInB.card : ℝ) ≤
          C₁ * Real.rpow R s * ((fineFamily p₀).card : ℝ) := by
        have h5 : (fineInB.card : ℝ) ≤
            (((fineFamily p₀).filter (fun T => tubeParamDist T V' ≤ R)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card h_subset
        have h6 := h_sset
        rw [h_fine_size p₀ hp₀] at h6
        linarith

      have h_M : ((fineFamily p₀).card : ℝ) = (M : ℝ) := by
        rw [h_fine_size p₀ hp₀] <;> norm_cast
      rw [h_M] at h_upper

      have h_rpow : Real.rpow R s ≤ 2 * Real.rpow r s := by
        have h7 : R ≤ 2 * r := by
          dsimp only [R]
          have h_le : dyadicDelta m ≤ r := hr
          linarith
        have h8 : 0 ≤ R := by
          dsimp only [R]
          have h9 : 0 ≤ r := by linarith [dyadicDelta_pos m]
          have h10 : 0 ≤ dyadicDelta m := (dyadicDelta_pos m).le
          linarith
        have h9 : Real.rpow R s ≤ Real.rpow (2 * r) s :=
          Real.rpow_le_rpow h8 h7 hs
        have h10 : Real.rpow (2 * r) s = Real.rpow 2 s * Real.rpow r s :=
          Real.mul_rpow (show (0 : ℝ) ≤ 2 from by norm_num) (show 0 ≤ r from by linarith)
        have h11 : Real.rpow R s ≤ Real.rpow 2 s * Real.rpow r s := by
          calc Real.rpow R s ≤ Real.rpow (2 * r) s := h9
               _ = Real.rpow 2 s * Real.rpow r s := h10
        have h12 : Real.rpow 2 s ≤ 2 := by
          have h13 : s ≤ 1 := hs_one
          have h14 : Real.rpow 2 s ≤ Real.rpow 2 1 :=
            Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 from by norm_num) h13
          simpa using h14
        have h15 : Real.rpow R s ≤ 2 * Real.rpow r s := by
          calc Real.rpow R s
            ≤ Real.rpow 2 s * Real.rpow r s := h11
          _ ≤ 2 * Real.rpow r s := by
            have h16 : 0 ≤ Real.rpow r s := Real.rpow_nonneg (by linarith) s
            nlinarith
        exact h15

      have h_final : (B.card : ℝ) ≤ (K * 2 * C₁) * Real.rpow r s * (TΔ.card : ℝ) := by
        have h1 : (m₁ p₀ : ℝ) * (Bp.card : ℝ) ≤ (fineInB.card : ℝ) := h_lower
        have h2 : (m₁ p₀ : ℝ) * (Bp.card : ℝ) ≥
            (B.card : ℝ) * (L : ℝ) / (P.card : ℝ) := h_p₀_bound
        have h3 : (B.card : ℝ) * (L : ℝ) / (P.card : ℝ) ≤ (fineInB.card : ℝ) := by
          calc (B.card : ℝ) * (L : ℝ) / (P.card : ℝ)
            ≤ (m₁ p₀ : ℝ) * (Bp.card : ℝ) := h2
          _ ≤ (fineInB.card : ℝ) := h1
        have h4 : (fineInB.card : ℝ) ≤ C₁ * Real.rpow R s * (M : ℝ) := h_upper
        have h5 : (L : ℝ) ≥ (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ)) := h_relation
        have hP_pos : 0 < (P.card : ℝ) := by exact_mod_cast hP_nonempty.card_pos
        have hT_pos : 0 < (TΔ.card : ℝ) := by exact_mod_cast hTΔ_nonempty.card_pos
        have hM_pos' : 0 < (M : ℝ) := by exact_mod_cast hM_pos
        have h6 : (B.card : ℝ) * (L : ℝ) ≤ C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ) := by
          calc (B.card : ℝ) * (L : ℝ)
            = ((B.card : ℝ) * (L : ℝ) / (P.card : ℝ)) * (P.card : ℝ) := by field_simp [hP_pos.ne'] <;> ring
          _ ≤ (fineInB.card : ℝ) * (P.card : ℝ) := by gcongr
          _ ≤ (C₁ * Real.rpow R s * (M : ℝ)) * (P.card : ℝ) := by gcongr
          _ = C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ) := by ring
        have h7 : (B.card : ℝ) * ((M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))) ≤ (B.card : ℝ) * (L : ℝ) := by
          gcongr
        have h8 : (B.card : ℝ) * (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ)) ≤ C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ) := by
          calc (B.card : ℝ) * (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))
            = (B.card : ℝ) * ((M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))) := by ring
          _ ≤ (B.card : ℝ) * (L : ℝ) := h7
          _ = (B.card : ℝ) * (L : ℝ) := by ring
          _ ≤ C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ) := h6
        have h9 : 0 < (M : ℝ) * (P.card : ℝ) := by positivity
        have h10 : (B.card : ℝ) / (K * (TΔ.card : ℝ)) ≤ C₁ * Real.rpow R s := by
          calc (B.card : ℝ) / (K * (TΔ.card : ℝ))
            = ((B.card : ℝ) * (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))) / ((M : ℝ) * (P.card : ℝ)) := by field_simp [h9.ne'] <;> ring
          _ ≤ (C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ)) / ((M : ℝ) * (P.card : ℝ)) := by gcongr
          _ = C₁ * Real.rpow R s := by field_simp [h9.ne'] <;> ring
        have h11 : (B.card : ℝ) ≤ (K * (TΔ.card : ℝ)) * (C₁ * Real.rpow R s) := by
          have h_pos : 0 < K * (TΔ.card : ℝ) := by positivity
          have h_eq : (K * (TΔ.card : ℝ)) * ((B.card : ℝ) / (K * (TΔ.card : ℝ))) = (B.card : ℝ) := by
            have h_ne : (K * (TΔ.card : ℝ)) ≠ 0 := h_pos.ne'
            calc (K * (TΔ.card : ℝ)) * ((B.card : ℝ) / (K * (TΔ.card : ℝ)))
              = (B.card : ℝ) * ((K * (TΔ.card : ℝ)) / (K * (TΔ.card : ℝ))) := by ring
            _ = (B.card : ℝ) * 1 := by rw [div_self h_ne]
            _ = (B.card : ℝ) := by ring
          calc (B.card : ℝ)
            = (K * (TΔ.card : ℝ)) * ((B.card : ℝ) / (K * (TΔ.card : ℝ))) := h_eq.symm
          _ ≤ (K * (TΔ.card : ℝ)) * (C₁ * Real.rpow R s) := by gcongr
        have h12 : Real.rpow R s ≤ 2 * Real.rpow r s := h_rpow
        calc (B.card : ℝ)
          ≤ (K * (TΔ.card : ℝ)) * (C₁ * Real.rpow R s) := h11
        _ ≤ (K * (TΔ.card : ℝ)) * (C₁ * (2 * Real.rpow r s)) := by gcongr
        _ = (K * 2 * C₁) * Real.rpow r s * (TΔ.card : ℝ) := by ring

      exact h_final

  exact ⟨hTΔ_nonempty, h_const, hs, h_sep, h_ball⟩

end InductionOnScales

end
