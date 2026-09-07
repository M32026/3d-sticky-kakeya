module

/-
  Coarse bound for m≥2 good first scale.

  Constructs S-sets at exponents s and min(t_j,1) from the good regularity
  in CombiningConfig, geometric data from B1 bridge, absorption from explicit
  polylog lemmas, and dispatches to coarse_bound_from_combined_v2.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSourceData
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
attribute [local instance] Classical.decEq

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- Coarse bound for m≥2, good first scale, using improved incidence. -/
lemma coarse_source_good_only
    {n k m M MΔ : ℕ}
    {s t τ ε_G η ε_N ε_inc C_P C_P_coarse lam δ Δ_coarse : ℝ}
    {K CΔ C'_coarse K_p5 C_coarse : ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {scaleClass : Fin n → ScaleClass}
    {j0 : Fin n}
    {Δ : Fin (n + 1) → ℝ}
    {C_between : Fin n → ℝ}
    {N : Fin n → ℕ}
    (t_j : ℝ)
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (P : Finset (DyadicSquare k))
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty' : P.Nonempty)
    (hnm : m ≤ k)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K * coarseConfig.P₀.card)
    (hj0 : j0.val = 0)
    (h_good : scaleClass j0 = ScaleClass.good t_j)
    (h_tj_ge_t : ∀ (j : Fin n) (t_j' : ℝ), scaleClass j = ScaleClass.good t_j' → t ≤ t_j')
    (hΔ0 : Δ 0 = 1)
    (hΔ1 : Δ 1 = Δ_coarse)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    (hCP_coarse_ge1 : 1 ≤ C_P_coarse)
    (hCP_coarse_pos : 0 < C_P_coarse)
    (hCP_coarse_weaken : C_P_coarse ≥ 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2))
    (h_improved_incidence_coarse : (coarseConfig.T₀.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow Δ_coarse (-(2 * s + ε_inc))))
    (h_exp_condition_v2 : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t)
    (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hε_inc : 0 < ε_inc)
    (hτ_pos : 0 < τ) (hCP : 1 ≤ C_P)
    (hlam : 0 < lam)
    (hK_ge1 : 1 ≤ K) (hK_pos : 0 < K)
    (hCΔ_pos : 0 < CΔ) (hCΔ_ge1 : 1 ≤ CΔ)
    (hCΔ_le : CΔ ≤ K * Real.rpow δ (-lam))
    (hC_coarse_ge : C_coarse ≥ K_p5 + 1)
    (hC_coarse_pos : 0 < C_coarse)
    -- Good branch absorption (for large-M case)
    (h_good_absorb : ∀ (t_j' : ℝ), scaleClass j0 = ScaleClass.good t_j' →
        Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
          K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse (2 * ε_G + ε_N))
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hK_p5_pos : 0 < K_p5) (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_spec : ∀ (t' : ℝ), s ≤ t' → t' ≤ 1 →
      ∀ (C_P' C_T' M' : ℝ), 0 < C_P' → 1 ≤ C_P' → 0 < C_T' → 1 ≤ C_T' → 1 ≤ M' → 2 ≤ m →
        ∀ (P' : Finset (DSquare m)), P'.Nonempty →
          IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) t' C_P' P' →
          (∀ (x y : DSquare m), x ∈ P' → y ∈ P' → dist x y ≤ 3) →
          (∀ p ∈ P', ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
          ∀ (Tp : TubeFamily m),
            (∀ p ∈ P', ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
            (∀ p ∈ P', ∀ T ∈ Tp p, |T.slope| ≤ 1) →
            (∀ p ∈ P', IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T' (Tp p)) →
            (∀ p ∈ P', (M' : ℝ) / 2 < (Tp p).card ∧ (Tp p).card ≤ M') →
              let T := P'.biUnion fun p => Tp p
              (T.card : ℝ) ≥ (1 / K_p5) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K_p5) *
                (1 / (C_P' * C_T')) * M' * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                  (M' * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((t' - s) / (1 - s)))
    (hm_ge2 : 2 ≤ m)
    (hΔ_coarse_pos : 0 < Δ_coarse) (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_le_delta : δ ≤ Δ_coarse)
    (hLbar_ge1 : 1 ≤ Real.log (1 / Δ_coarse))
    (hMΔ_pos : 0 < MΔ)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    (hδ_eq_dyadic : δ = dyadicDelta k)
    (PΔ : ℝ)
    (hPΔ_def : PΔ =
      (∏ j ∈ ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood),
         Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
      (∏ j ∈ ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad),
         Δ (Fin.succ j) / Δ j.castSucc)) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
  have hP_sub_unit : config.pointSet ⊆ dyadicSquare 1 0 0 :=
    pointSet_sub_dyadicSquare1 hB1.h_squares_unit
  have hpointSet_nonempty : config.pointSet.Nonempty := hcfg.h_uniform.1
  -- Scale equalities
  have h_Delta_succ : Δ (Fin.succ j0) = Δ_coarse := by
    have h : (Fin.succ j0 : Fin (n + 1)) = 1 := by
      apply Fin.ext
      have h1 : (Fin.succ j0).val = j0.val + 1 := by simp [Fin.val_succ]
      have h2 : (1 : Fin (n + 1)).val = 1 := by
        simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
      rw [h1, h2, hj0] <;> ring
    rw [h, hΔ1]
  have h_Delta_cast : Δ j0.castSucc = 1 := by
    have h : (j0.castSucc : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.castSucc, hj0] <;> omega
    rw [h, hΔ0]
  have hbet_regular := hcfg.h_good j0 t_j h_good
  have hbet_tj0 : IsSetBetweenScales config.pointSet (Δ (Fin.succ j0)) (Δ j0.castSucc) t_j (C_between j0) :=
    hbet_regular.1
  have hbet_tj : IsSetBetweenScales config.pointSet Δ_coarse 1 t_j (C_between j0) := by
    convert hbet_tj0 using 1
    · exact h_Delta_succ.symm
    · exact h_Delta_cast.symm
  have hC_between_pos : 0 < C_between j0 := hbet_tj.2.2.2.2.1
  let C_max : ℝ := max (C_between j0) 1
  have hC_max_pos : 0 < C_max := by positivity
  have hC_max_ge1 : 1 ≤ C_max := le_max_right _ _
  have hC_between_le_max : C_between j0 ≤ C_max := le_max_left _ _
  have h_tj_ge_t_local : t ≤ t_j := h_tj_ge_t j0 t_j h_good
  have h_tj_ge_s : s ≤ t_j := by linarith [hst]
  have h0s : 0 ≤ s := by linarith [hs]
  have hbet_s : IsSetBetweenScales config.pointSet Δ_coarse 1 s C_max := by
    refine' ⟨hbet_tj.1, hbet_tj.2.1, hbet_tj.2.2.1, by linarith, hC_max_pos, _⟩
    intro i j hnonempty
    let A : Set (EuclideanSpace ℝ (Fin 2)) := homothetyS 1 i j '' (config.pointSet ∩ dyadicSquare 1 i j)
    have h_main : ∀ (i j : ℤ), (config.pointSet ∩ dyadicSquare 1 i j).Nonempty →
        IsDeltaSSet (Δ_coarse / 1) t_j (C_between j0) (homothetyS 1 i j '' (config.pointSet ∩ dyadicSquare 1 i j)) :=
      hbet_tj.2.2.2.2.2
    have h_orig : IsDeltaSSet (Δ_coarse / 1) t_j (C_between j0) A := by
      simpa [A] using h_main i j hnonempty
    have h_mono : IsDeltaSSet (Δ_coarse / 1) t_j C_max A :=
      IsDeltaSSet.weaken_constant' h_orig hC_between_le_max hC_max_pos
    exact IsDeltaSSet.weaken_exponent h_mono h0s h_tj_ge_s hC_max_ge1
  have hsset_s : IsDeltaSSet Δ_coarse s C_max config.pointSet :=
    isSetBetweenScales_to_isDeltaSSet_unit hbet_s hP_sub_unit hpointSet_nonempty
  rw [hΔ_coarse_eq] at hsset_s
  rcases coarse_corners_sset_from_fine_pointset hnm config P hP_sub coarseConfig
      hcoarse_P_eq h_card_bound hsset_s (by linarith [hs]) hC_max_pos hK_pos hP_nonempty'
    with ⟨C_conv_s, hC_conv_s_eq, hC_conv_s_pos, hsset_conv_s⟩
  have h_sqrt2_ge1 : 1 ≤ Real.sqrt 2 := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have h_base_ge1 : 1 ≤ 2 * Real.sqrt 2 := by linarith
  have h_exp_le_s : (2 * Real.sqrt 2) ^ s ≤ 2 * Real.sqrt 2 := by
    have h1 : (2 * Real.sqrt 2) ^ s ≤ (2 * Real.sqrt 2) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h_base_ge1 (by linarith [hs1])
    have h2 : (2 * Real.sqrt 2) ^ (1 : ℝ) = (2 * Real.sqrt 2) := Real.rpow_one _
    rw [h2] at h1
    exact h1
  have h_pos_factor : 0 ≤ 81 * K * C_max := by positivity
  have h_main_s : 81 * K * C_max * (2 * Real.sqrt 2) ^ s ≤ 81 * K * C_max * (2 * Real.sqrt 2) :=
    mul_le_mul_of_nonneg_left h_exp_le_s h_pos_factor
  have h_le_s : C_conv_s ≤ C_P_coarse := by
    rw [hC_conv_s_eq]
    have h_final : 81 * K * C_max * (2 * Real.sqrt 2) ≤ C_P_coarse := hCP_coarse_weaken
    exact le_trans h_main_s h_final
  have hP_set_coarse : IsFinsetDeltaSSet (dyadicDelta m) s C_P_coarse
      (finsetDyadicToDSquare coarseConfig.P₀) :=
    IsDeltaSSet.weaken_constant' hsset_conv_s h_le_s hCP_coarse_pos
  let u : ℝ := min t_j 1
  have h1_strict : s < t_j := lt_of_lt_of_le hst h_tj_ge_t_local
  have hus : s ≤ u := by
    have h2 : s < 1 := hs1
    exact le_min (by linarith) (by linarith)
  have hu1 : u ≤ 1 := min_le_right _ _
  have hu_tj : u ≤ t_j := min_le_left _ _
  have h0u : 0 ≤ u := by linarith [hus]
  have hbet_u : IsSetBetweenScales config.pointSet Δ_coarse 1 u C_max := by
    refine' ⟨hbet_tj.1, hbet_tj.2.1, hbet_tj.2.2.1, by linarith, hC_max_pos, _⟩
    intro i j hnonempty
    let A : Set (EuclideanSpace ℝ (Fin 2)) := homothetyS 1 i j '' (config.pointSet ∩ dyadicSquare 1 i j)
    have h_main : ∀ (i j : ℤ), (config.pointSet ∩ dyadicSquare 1 i j).Nonempty →
        IsDeltaSSet (Δ_coarse / 1) t_j (C_between j0) (homothetyS 1 i j '' (config.pointSet ∩ dyadicSquare 1 i j)) :=
      hbet_tj.2.2.2.2.2
    have h_orig : IsDeltaSSet (Δ_coarse / 1) t_j (C_between j0) A := by
      simpa [A] using h_main i j hnonempty
    have h_mono_u : IsDeltaSSet (Δ_coarse / 1) t_j C_max A :=
      IsDeltaSSet.weaken_constant' h_orig hC_between_le_max hC_max_pos
    exact IsDeltaSSet.weaken_exponent h_mono_u h0u hu_tj hC_max_ge1
  have hsset_u : IsDeltaSSet Δ_coarse u C_max config.pointSet :=
    isSetBetweenScales_to_isDeltaSSet_unit hbet_u hP_sub_unit hpointSet_nonempty
  rw [hΔ_coarse_eq] at hsset_u
  rcases coarse_corners_sset_from_fine_pointset hnm config P hP_sub coarseConfig
      hcoarse_P_eq h_card_bound hsset_u (by linarith [hs]) hC_max_pos hK_pos hP_nonempty'
    with ⟨C_conv_u, hC_conv_u_eq, hC_conv_u_pos, hsset_conv_u⟩
  have h_exp_le_u : (2 * Real.sqrt 2) ^ u ≤ 2 * Real.sqrt 2 := by
    have h1 : (2 * Real.sqrt 2) ^ u ≤ (2 * Real.sqrt 2) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h_base_ge1 (by linarith [hu1])
    have h2 : (2 * Real.sqrt 2) ^ (1 : ℝ) = (2 * Real.sqrt 2) := Real.rpow_one _
    rw [h2] at h1
    exact h1
  have h_main_u : 81 * K * C_max * (2 * Real.sqrt 2) ^ u ≤ 81 * K * C_max * (2 * Real.sqrt 2) :=
    mul_le_mul_of_nonneg_left h_exp_le_u h_pos_factor
  have h_le_u : C_conv_u ≤ C_P_coarse := by
    rw [hC_conv_u_eq]
    have h_final : 81 * K * C_max * (2 * Real.sqrt 2) ≤ C_P_coarse := hCP_coarse_weaken
    exact le_trans h_main_u h_final
  have hP_set_u : IsFinsetDeltaSSet (dyadicDelta m) u C_P_coarse
      (finsetDyadicToDSquare coarseConfig.P₀) :=
    IsDeltaSSet.weaken_constant' hsset_conv_u h_le_u hCP_coarse_pos
  have hP_set_tj_coarse : ∀ (t_j' : ℝ), scaleClass j0 = ScaleClass.good t_j' →
      IsFinsetDeltaSSet (dyadicDelta m) (min t_j' 1) C_P_coarse
        (finsetDyadicToDSquare coarseConfig.P₀) := by
    intro t_j' h_good'
    have h1 : scaleClass j0 = ScaleClass.good t_j := h_good
    rw [h1] at h_good'
    injection h_good' with h2
    have h_eq : t_j' = t_j := h2.symm
    rw [h_eq]
    exact hP_set_u
  have h_full_unit : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1 :=
    coarse_full_unit_bound_from_B1 hnm hB1 hP_sub hcoarse_P_eq
  have h_unit_coarse : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1 :=
    coarse_unit_coarse_from_full h_full_unit
  have h_diam_coarse : ∀ (p q : DSquare m),
      p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      q ∈ finsetDyadicToDSquare coarseConfig.P₀ → dist p q ≤ 3 :=
    coarse_diam_from_full_unit h_full_unit
  have hcoarse_P_nonempty : coarseConfig.P₀.Nonempty := by
    rw [hcoarse_P_eq]
    exact hP_nonempty'.image _
  exact coarse_bound_from_combined_v2
    (hj0 := hj0)
    (hδ_eq_dyadic := hδ_eq_dyadic)
    (C_between := C_between)
    (N := N)
    (hcfg := hcfg)
    (h_tj_ge_t_extra := h_tj_ge_t)
    (h_exp_condition_v2 := h_exp_condition_v2)
    (h_scale_not_normal := by
      intro h
      rw [h_good] at h
      contradiction)
    (hcoarse_P_nonempty := hcoarse_P_nonempty)
    (h_slope_coarse := h_slope_coarse)
    (h_diam_coarse := h_diam_coarse)
    (h_unit_coarse := h_unit_coarse)
    (hΔ0 := hΔ0)
    (hΔ1 := hΔ1)
    (hΔ_coarse_eq := hΔ_coarse_eq)
    (hP_set_coarse := hP_set_coarse)
    (hP_set_tj_coarse := hP_set_tj_coarse)
    (h_improved_incidence_coarse := fun _ _ => h_improved_incidence_coarse)
    (h_good_absorb := h_good_absorb)
    (hs := hs) (hs1 := hs1) (hst := hst)
    (hεG := hεG) (hη := hη) (hεN := hεN)
    (hε_inc := hε_inc)
    (hτ_pos := hτ_pos) (hCP_coarse := hCP_coarse_ge1)
    (hlam := hlam)
    (hK_ge1 := hK_ge1) (hK_pos := hK_pos)
    (hCΔ_pos := hCΔ_pos) (hCΔ_ge1 := hCΔ_ge1)
    (hCΔ_le := hCΔ_le)
    (hC_coarse_ge := hC_coarse_ge)
    (hC_coarse_pos := hC_coarse_pos)
    (hC'_coarse_ge1 := hC'_coarse_ge1)
    (hK_p5_pos := hK_p5_pos) (hK_p5_ge1 := hK_p5_ge1)
    (hK_p5_spec := hK_p5_spec)
    (hm_ge2 := hm_ge2)
    (hΔ_coarse_pos := hΔ_coarse_pos) (hΔ_coarse_lt_one := hΔ_coarse_lt_one)
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hδ_le_delta := hδ_le_delta)
    (hLbar_ge1 := hLbar_ge1)
    (hMΔ_pos := hMΔ_pos)
    (PΔ := PΔ)
    (hPΔ_def := hPΔ_def)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
