module

/-
  Coarse bound from combined inductive step context (v2 with ε_inc).

  Provides:
  - construct_good_gamma_v2: derives γ from h_exp_condition_v2
  - coarse_bound_from_combined_v2: consumer lemma calling generalized dispatcher
  - coarse_source_from_config_v2: producer skeleton (constructs from CombiningConfig)

  Whiteprint node: combining_theorem_genuine / coarse_source_data
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseBoundDispatcher
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSsetConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BetweenScalesToSset
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseGeometricData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
attribute [local instance] Classical.decEq

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-! ========================================================================
    Good branch gamma construction (v2 with ε_inc)
    ======================================================================== -/

/-- Construct gamma for good branch (v2 with ε_inc).

    Given t_j ≥ t, set u = min t_j 1 and γ = (η + 2*ε_G) * (1-s) / (u-s).
    Then γ * ((u-s)/(1-s)) = η + 2*ε_G.
    v2: γ + η ≤ ε_inc follows from h_exp_condition_v2 when u ≥ min t 1. -/
lemma construct_good_gamma_v2
    (s t ε_G η ε_inc : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t)
    (hεG : 0 < ε_G) (hη : 0 < η)
    (h_exp_condition_v2 : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc)
    (t_j : ℝ) (h_tj_ge_t : t ≤ t_j) :
    ∃ (γ : ℝ), 0 < γ ∧
      γ * ((min t_j 1 - s) / (1 - s)) = η + 2 * ε_G ∧
      γ + η ≤ ε_inc := by
  let u : ℝ := min t_j 1
  have hus : s < u := by
    dsimp only [u]
    have h1 : s < t_j := lt_of_lt_of_le hst h_tj_ge_t
    exact lt_min h1 hs1
  have h_denom_pos : 0 < u - s := by linarith
  have h_one_minus_s_pos : 0 < 1 - s := by linarith
  let γ : ℝ := (η + 2 * ε_G) * (1 - s) / (u - s)
  have hγ_pos : 0 < γ := by
    dsimp only [γ]
    have h1 : 0 < η + 2 * ε_G := by linarith
    positivity
  have hγα : γ * ((u - s) / (1 - s)) = η + 2 * ε_G := by
    dsimp only [γ]
    field_simp [h_denom_pos.ne', h_one_minus_s_pos.ne'] <;> ring
  have h_u_ge_mint1 : u ≥ min t 1 := by
    dsimp only [u]
    have h2 : min t 1 ≤ min t_j 1 := by gcongr <;> linarith
    exact h2
  have hγ_le : γ ≤ (η + 2 * ε_G) * (1 - s) / (min t 1 - s) := by
    dsimp only [γ]
    have h_mint1_pos : 0 < min t 1 - s := by
      have h1 : s < min t 1 := lt_min hst hs1
      linarith
    have h3 : u - s ≥ min t 1 - s := by linarith
    have h4 : 0 < η + 2 * ε_G := by linarith
    have h5 : 0 < 1 - s := by linarith
    gcongr
  have h6 : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc := h_exp_condition_v2
  have h7 : γ + η ≤ ε_inc := by linarith
  exact ⟨γ, hγ_pos, by simpa [u] using hγα, h7⟩

/-! ========================================================================
    v2 consumer: coarse bound with ε_inc from regular incidence

    Uses the generalized dispatcher where good-small branch takes abstract
    ε_imp and budget condition ε_N + ε_imp ≥ γ + η.
    For v2: set ε_imp := ε_inc. Budget follows from γ+η ≤ ε_inc + ε_N.
    ======================================================================== -/

/-- Produce the coarse tube count lower bound from the inductive step context (v2).

    v2 version: uses ε_inc from regular incidence instead of old ε_G contract.
    Constructs ε_imp := ε_inc, budget ε_N + ε_inc ≥ γ + η from hextra.
    All other data (S-sets, improved incidence, absorption) taken as hypotheses. -/
lemma coarse_bound_from_combined_v2
    {n k m M MΔ : ℕ}
    {s t τ ε_G η ε_N C_P C_P_coarse ε_inc lam δ Δ_coarse : ℝ}
    {K CΔ C'_coarse K_p5 C_coarse : ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {scaleClass : Fin n → ScaleClass}
    {j0 : Fin n}
    {Δ : Fin (n + 1) → ℝ}
    -- Scale identity
    (hj0 : j0.val = 0)
    (hδ_eq_dyadic : δ = dyadicDelta k)
    -- CombiningConfig
    (C_between : Fin n → ℝ) (N : Fin n → ℕ)
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    -- Extra hypotheses (v2)
    (h_tj_ge_t_extra : ∀ (j : Fin n) (t_j : ℝ), scaleClass j = ScaleClass.good t_j → t ≤ t_j)
    (h_exp_condition_v2 : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc)
    -- Scale is known to be good (not normal/bad)
    (h_scale_not_normal : scaleClass j0 ≠ ScaleClass.normal)
    -- B1 bridge output
    (hcoarse_P_nonempty : coarseConfig.P₀.Nonempty)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    -- Geometric data
    (h_diam_coarse : ∀ (p q : DSquare m),
      p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      q ∈ finsetDyadicToDSquare coarseConfig.P₀ → dist p q ≤ 3)
    (h_unit_coarse : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1)
    -- Scale equalities
    (hΔ0 : Δ 0 = 1)
    (hΔ1 : Δ 1 = Δ_coarse)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    -- S-set conversion (from onyx)
    (hP_set_coarse : IsFinsetDeltaSSet (dyadicDelta m) s C_P_coarse
        (finsetDyadicToDSquare coarseConfig.P₀))
    (hP_set_tj_coarse : ∀ (t_j : ℝ), scaleClass j0 = ScaleClass.good t_j →
        IsFinsetDeltaSSet (dyadicDelta m) (min t_j 1) C_P_coarse
          (finsetDyadicToDSquare coarseConfig.P₀))
    -- Improved incidence at ε_inc (coarse scale), conditional on good first scale
    (h_improved_incidence_coarse : ∀ (t_j : ℝ), scaleClass j0 = ScaleClass.good t_j →
      (coarseConfig.T₀.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow Δ_coarse (-(2 * s + ε_inc))))
    -- Good branch absorption (for large-M case)
    (h_good_absorb : ∀ (t_j : ℝ), scaleClass j0 = ScaleClass.good t_j →
      Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
        K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse (2 * ε_G + ε_N))
    -- Common parameters
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t)
    (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hε_inc : 0 < ε_inc)
    (hτ_pos : 0 < τ) (hCP_coarse : 1 ≤ C_P_coarse)
    (hlam : 0 < lam)
    (hK_ge1 : 1 ≤ K) (hK_pos : 0 < K)
    (hCΔ_pos : 0 < CΔ) (hCΔ_ge1 : 1 ≤ CΔ)
    (hCΔ_le : CΔ ≤ K * Real.rpow δ (-lam))
    (hC_coarse_ge : C_coarse ≥ K_p5 + 1)
    (hC_coarse_pos : 0 < C_coarse)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hK_p5_pos : 0 < K_p5) (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_spec : ∀ (t : ℝ), s ≤ t → t ≤ 1 →
      ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ m →
        ∀ (P : Finset (DSquare m)), P.Nonempty →
          IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) t C_P P →
          (∀ (x y : DSquare m), x ∈ P → y ∈ P → dist x y ≤ 3) →
          (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
          ∀ (Tp : TubeFamily m),
            (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
            (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
            (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T (Tp p)) →
            (∀ p ∈ P, (M : ℝ) / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
              let T := P.biUnion fun p => Tp p
              (T.card : ℝ) ≥ (1 / K_p5) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K_p5) *
                (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                  (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((t - s) / (1 - s)))
    (hm_ge2 : 2 ≤ m)
    (hΔ_coarse_pos : 0 < Δ_coarse) (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_le_delta : δ ≤ Δ_coarse)
    (hLbar_ge1 : 1 ≤ Real.log (1 / Δ_coarse))
    (hMΔ_pos : 0 < MΔ)
    -- PΔ definition
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
  let scaleClass0 := scaleClass j0

  -- Fin equalities from hj0
  have h_cast0 : (j0.castSucc : Fin (n + 1)) = 0 := by
    apply Fin.ext
    simp [Fin.castSucc, hj0] <;> omega
  have h_n_pos : 0 < n := by
    have h : j0.val < n := j0.is_lt
    rw [hj0] at h
    omega
  have h_cast1 : (Fin.succ j0 : Fin (n + 1)) = 1 := by
    apply Fin.ext
    have h1 : (Fin.succ j0).val = j0.val + 1 := by simp [Fin.val_succ]
    have h2 : (1 : Fin (n + 1)).val = 1 := by
      simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
    rw [h1, h2, hj0] <;> ring

  -- PΔ equalities
  have hPΔ_bad : scaleClass0 = ScaleClass.bad → PΔ = Δ_coarse := by
    intro hscale
    have hsc : scaleClass j0 = ScaleClass.bad := by simpa [scaleClass0] using hscale
    rw [hPΔ_def]
    have hG : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood) = ∅ := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isGood]
    have hB : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad) = {j0} := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isBad]
    rw [hG, hB, Finset.prod_singleton, h_cast0, h_cast1, hΔ0, hΔ1] <;> simp
  have hPΔ_normal : scaleClass0 = ScaleClass.normal → PΔ = 1 := by
    intro hscale
    have hsc : scaleClass j0 = ScaleClass.normal := by simpa [scaleClass0] using hscale
    rw [hPΔ_def]
    have hG : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood) = ∅ := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isGood]
    have hB : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad) = ∅ := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isBad]
    rw [hG, hB] <;> simp
  have hPΔ_good : ∀ (t_j : ℝ), scaleClass0 = ScaleClass.good t_j → PΔ = Real.rpow Δ_coarse (-η) := by
    intro t_j hscale
    have hsc : scaleClass j0 = ScaleClass.good t_j := by simpa [scaleClass0] using hscale
    rw [hPΔ_def]
    have hG : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood) = {j0} := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isGood]
    have hB : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad) = ∅ := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isBad]
    rw [hG, hB, Finset.prod_singleton, h_cast0, h_cast1, hΔ0, hΔ1]
    have h_pos1 : 0 < 1 / Δ_coarse := by positivity
    have h2 : Real.rpow (1 / Δ_coarse) η = Real.exp (η * Real.log (1 / Δ_coarse)) := by
      have h := Real.rpow_def_of_pos h_pos1 η
      exact h.trans (congr_arg Real.exp (by ring))
    have h3 : Real.rpow Δ_coarse (-η) = Real.exp ((-η) * Real.log Δ_coarse) := by
      have h := Real.rpow_def_of_pos hΔ_coarse_pos (-η)
      exact h.trans (congr_arg Real.exp (by ring))
    have h4 : Real.log (1 / Δ_coarse) = -Real.log Δ_coarse := by
      rw [Real.log_div (by norm_num) hΔ_coarse_pos.ne'] <;> simp
    rw [h2, h3, h4, Finset.prod_empty]
    simp
    <;> apply congr_arg Real.exp <;> ring

  -- Normal branch data (unused in good case: scaleClass0 ≠ normal)
  have h_normal_data : scaleClass0 = ScaleClass.normal →
      ∃ (C_P_coarse : ℝ), 1 ≤ C_P_coarse ∧ 0 < C_P_coarse ∧
        IsFinsetDeltaSSet (dyadicDelta m) s C_P_coarse (finsetDyadicToDSquare coarseConfig.P₀) ∧
        C_coarse ≥ K_p5 ∧
        Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
          K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse ε_N := by
    intro h
    have h_contra : scaleClass j0 ≠ ScaleClass.normal := h_scale_not_normal
    have h_eq : scaleClass j0 = ScaleClass.normal := by simpa [scaleClass0] using h
    exact False.elim (h_contra h_eq)

  -- Good branch data (with ε_imp := ε_inc)
  have h_good_data : ∀ (t_j : ℝ), scaleClass0 = ScaleClass.good t_j →
      ∃ (u C_P_coarse γ ε_imp : ℝ), u = min t_j 1 ∧ s < u ∧ u ≤ 1 ∧
        1 ≤ C_P_coarse ∧ 0 < C_P_coarse ∧
        IsFinsetDeltaSSet (dyadicDelta m) u C_P_coarse (finsetDyadicToDSquare coarseConfig.P₀) ∧
        0 < γ ∧ γ * ((u - s) / (1 - s)) = η + 2 * ε_G ∧
        0 < ε_imp ∧ ε_N + ε_imp ≥ γ + η ∧
        C_coarse ≥ K_p5 ∧
        Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
          K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse (2 * ε_G + ε_N) ∧
        (coarseConfig.T₀.card : ENNReal) ≥
          ENNReal.ofReal (Real.rpow Δ_coarse (-(2 * s + ε_imp))) := by
    intro t_j hgood
    have hsc : scaleClass j0 = ScaleClass.good t_j := by simpa [scaleClass0] using hgood
    have h_tj_ge_t' : t ≤ t_j := h_tj_ge_t_extra j0 t_j hsc
    rcases construct_good_gamma_v2 s t ε_G η ε_inc hs hs1 hst hεG hη
        h_exp_condition_v2 t_j h_tj_ge_t' with ⟨γ, hγ_pos, hγα, hγ_η_le⟩
    let u := min t_j 1
    have hus : s < u := by
      dsimp only [u]
      have h1 : s < t_j := lt_of_lt_of_le hst h_tj_ge_t'
      exact lt_min h1 hs1
    have hu1 : u ≤ 1 := by dsimp only [u] <;> exact min_le_right _ _
    have h_budget : ε_N + ε_inc ≥ γ + η := by linarith
    refine ⟨u, C_P_coarse, γ, ε_inc, by rfl, hus, hu1, hCP_coarse, by linarith,
      hP_set_tj_coarse t_j hsc, hγ_pos, ?_, hε_inc, h_budget, by linarith,
      h_good_absorb t_j hsc, h_improved_incidence_coarse t_j hsc⟩
    simpa [u] using hγα

  -- Call the generalized dispatcher
  exact coarse_bound_dispatcher
    scaleClass0 PΔ
    hs hs1 hεG hη hεN hlam hK_ge1 hK_pos
    hCΔ_pos hCΔ_ge1 hCΔ_le
    hC_coarse_pos hC'_coarse_ge1
    hm_ge2 hΔ_coarse_eq hΔ_coarse_pos hΔ_coarse_lt_one
    hδ_pos hδ_lt_one hδ_le_delta hLbar_ge1
    hcoarse_P_nonempty hMΔ_pos
    h_slope_coarse h_diam_coarse h_unit_coarse
    hPΔ_bad hPΔ_normal hPΔ_good
    K_p5 hK_p5_pos hK_p5_ge1 hK_p5_spec
    h_normal_data h_good_data


/-- Explicit polylog absorption for the normal branch. -/
lemma coarse_normal_absorb_explicit
    {Δ_coarse C_P K_p5 C_coarse s ε_N : ℝ}
    (hK_p5_ge1 : 1 ≤ K_p5)
    (hCP : 1 ≤ C_P)
    (hs : 0 < s)
    (hεN : 0 < ε_N)
    (hC_coarse_ge : C_coarse ≥ K_p5 + C_P + 1)
    (hΔ_pos : 0 < Δ_coarse)
    (hΔ_lt_one : Δ_coarse < 1)
    (hL_threshold : Real.log (1 / Δ_coarse) ≥ K_p5 * C_P * 13 * (2 : ℝ) ^ s) :
    Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
      K_p5 * C_P * 13 * (2 : ℝ) ^ s * Real.rpow Δ_coarse ε_N := by
  set L : ℝ := Real.log (1 / Δ_coarse) with hL_def
  set C0 : ℝ := K_p5 * C_P * 13 * (2 : ℝ) ^ s with hC0_def
  set e : ℝ := C_coarse - K_p5 with he_def
  have hL_pos : 0 < L := by
    rw [hL_def]; apply Real.log_pos; exact one_lt_one_div hΔ_pos hΔ_lt_one
  have hC0_pos : 0 < C0 := by
    rw [hC0_def]; have h1 : 0 < K_p5 := by linarith
    have h2 : 0 < C_P := by linarith
    have h3 : (0 : ℝ) < 13 := by norm_num
    have h4 : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    positivity
  have h2pow_ge1 : 1 ≤ (2 : ℝ) ^ s :=
    Real.one_le_rpow (by norm_num) (show 0 ≤ s from le_of_lt hs)
  have hC0_ge13 : 13 ≤ C0 := by
    rw [hC0_def]
    have h1 : 1 ≤ K_p5 := hK_p5_ge1
    have h2 : 1 ≤ C_P := hCP
    have h3 : 1 ≤ (2 : ℝ) ^ s := h2pow_ge1
    calc (13 : ℝ)
      = 1 * 1 * 13 * 1 := by norm_num
    _ ≤ K_p5 * C_P * 13 * (2 : ℝ) ^ s := by gcongr <;> linarith
  have hL_ge_C0 : L ≥ C0 := hL_threshold
  have hL_ge1 : 1 ≤ L := by linarith [hC0_ge13]
  have he_ge1 : 1 ≤ e := by rw [he_def]; linarith
  have hΔ_pow_lt_one : Real.rpow Δ_coarse ε_N < 1 :=
    Real.rpow_lt_one (by linarith) hΔ_lt_one hεN
  have hRHS_lt_C0 : C0 * Real.rpow Δ_coarse ε_N < C0 := by
    have h : Real.rpow Δ_coarse ε_N < 1 := hΔ_pow_lt_one
    have h5 : C0 * Real.rpow Δ_coarse ε_N < C0 * 1 := mul_lt_mul_of_pos_left h hC0_pos
    simpa using h5
  have hL_pow_ge_L : Real.rpow L e ≥ L := by
    have h6 : Real.rpow L e ≥ Real.rpow L 1 :=
      Real.rpow_le_rpow_of_exponent_le hL_ge1 he_ge1
    have h7 : Real.rpow L 1 = L := by simp
    rw [h7] at h6; exact h6
  have h_main : Real.rpow L e > C0 * Real.rpow Δ_coarse ε_N := by
    calc Real.rpow L e
      ≥ L := hL_pow_ge_L
    _ ≥ C0 := hL_ge_C0
    _ > C0 * Real.rpow Δ_coarse ε_N := hRHS_lt_C0
  exact le_of_lt h_main

/-- Explicit polylog absorption for the good branch. -/
lemma coarse_good_absorb_explicit
    {Δ_coarse C_P K_p5 C_coarse s ε_G ε_N : ℝ}
    (hK_p5_ge1 : 1 ≤ K_p5)
    (hCP : 1 ≤ C_P)
    (hs : 0 < s)
    (hεG : 0 < ε_G)
    (hεN : 0 < ε_N)
    (hC_coarse_ge : C_coarse ≥ K_p5 + C_P + 1)
    (hΔ_pos : 0 < Δ_coarse)
    (hΔ_lt_one : Δ_coarse < 1)
    (hL_threshold : Real.log (1 / Δ_coarse) ≥ K_p5 * C_P * 13 * (2 : ℝ) ^ s) :
    Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
      K_p5 * C_P * 13 * (2 : ℝ) ^ s * Real.rpow Δ_coarse (2 * ε_G + ε_N) := by
  set L : ℝ := Real.log (1 / Δ_coarse) with hL_def
  set C0 : ℝ := K_p5 * C_P * 13 * (2 : ℝ) ^ s with hC0_def
  set e : ℝ := C_coarse - K_p5 with he_def
  have hL_pos : 0 < L := by
    rw [hL_def]; apply Real.log_pos; exact one_lt_one_div hΔ_pos hΔ_lt_one
  have hC0_pos : 0 < C0 := by
    rw [hC0_def]; have h1 : 0 < K_p5 := by linarith
    have h2 : 0 < C_P := by linarith
    have h3 : (0 : ℝ) < 13 := by norm_num
    have h4 : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    positivity
  have h2pow_ge1 : 1 ≤ (2 : ℝ) ^ s :=
    Real.one_le_rpow (by norm_num) (show 0 ≤ s from le_of_lt hs)
  have hC0_ge13 : 13 ≤ C0 := by
    rw [hC0_def]
    have h1 : 1 ≤ K_p5 := hK_p5_ge1
    have h2 : 1 ≤ C_P := hCP
    have h3 : 1 ≤ (2 : ℝ) ^ s := h2pow_ge1
    calc (13 : ℝ)
      = 1 * 1 * 13 * 1 := by norm_num
    _ ≤ K_p5 * C_P * 13 * (2 : ℝ) ^ s := by gcongr <;> linarith
  have hL_ge_C0 : L ≥ C0 := hL_threshold
  have hL_ge1 : 1 ≤ L := by linarith [hC0_ge13]
  have he_ge1 : 1 ≤ e := by rw [he_def]; linarith
  have h_exp_pos : 0 < 2 * ε_G + ε_N := by linarith
  have hΔ_pow_lt_one : Real.rpow Δ_coarse (2 * ε_G + ε_N) < 1 :=
    Real.rpow_lt_one (by linarith) hΔ_lt_one h_exp_pos
  have hRHS_lt_C0 : C0 * Real.rpow Δ_coarse (2 * ε_G + ε_N) < C0 := by
    have h : Real.rpow Δ_coarse (2 * ε_G + ε_N) < 1 := hΔ_pow_lt_one
    have h5 : C0 * Real.rpow Δ_coarse (2 * ε_G + ε_N) < C0 * 1 := mul_lt_mul_of_pos_left h hC0_pos
    simpa using h5
  have hL_pow_ge_L : Real.rpow L e ≥ L := by
    have h6 : Real.rpow L e ≥ Real.rpow L 1 :=
      Real.rpow_le_rpow_of_exponent_le hL_ge1 he_ge1
    have h7 : Real.rpow L 1 = L := by simp
    rw [h7] at h6; exact h6
  have h_main : Real.rpow L e > C0 * Real.rpow Δ_coarse (2 * ε_G + ε_N) := by
    calc Real.rpow L e
      ≥ L := hL_pow_ge_L
    _ ≥ C0 := hL_ge_C0
    _ > C0 * Real.rpow Δ_coarse (2 * ε_G + ε_N) := hRHS_lt_C0
  exact le_of_lt h_main

/-! ========================================================================
    Helper lemmas for internal S-set construction
    ======================================================================== -/

/-- If all dyadic squares have indices in the unit range, then the point set
    is contained in the unit dyadic square at scale 1. -/
lemma pointSet_sub_dyadicSquare1
    {k : ℕ} {s C : ℝ} {M : ℕ}
    {config : CTNiceConfiguration k s C M}
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ k : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ k : ℤ)) :
    config.pointSet ⊆ dyadicSquare 1 0 0 := by
  intro x hx
  simp only [NiceConfiguration.pointSet, Set.mem_iUnion] at hx
  rcases hx with ⟨p, hp, hxp⟩
  have h_bounds := h_squares_unit p hp
  let δ := dyadicDelta k
  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδ_sum : (2 ^ k : ℝ) * δ = 1 := by
    have h1 : δ = dyadicDelta k := by rfl
    rw [h1]
    have h2 : dyadicDelta k = 1 / (2 : ℝ)^k := by exact Eq.symm (Real.ext_cauchy rfl)
    rw [h2]
    field_simp
    <;> ring
  have h_i_nonneg : 0 ≤ (p.i : ℝ) := by exact_mod_cast h_bounds.1
  have h_j_nonneg : 0 ≤ (p.j : ℝ) := by exact_mod_cast h_bounds.2.2.1
  have h_i_add1_le : (p.i : ℝ) + 1 ≤ (2 ^ k : ℝ) := by
    have h : p.i + 1 ≤ (2 ^ k : ℤ) := by omega
    exact_mod_cast h
  have h_j_add1_le : (p.j : ℝ) + 1 ≤ (2 ^ k : ℝ) := by
    have h : p.j + 1 ≤ (2 ^ k : ℤ) := by omega
    exact_mod_cast h
  simp only [DyadicSquare.toSet, Set.mem_setOf_eq] at hxp
  rcases hxp with ⟨h1, h2, h3, h4⟩
  have hx0_ge : 0 ≤ x 0 := by
    have h5 : 0 ≤ (p.i : ℝ) * δ := by positivity
    linarith
  have hx0_lt : x 0 < 1 := by
    have h5 : ((p.i : ℝ) + 1) * δ ≤ 1 := by
      have h6 : ((p.i : ℝ) + 1) * δ ≤ (2 ^ k : ℝ) * δ := by gcongr
      linarith [hδ_sum]
    linarith
  have hx1_ge : 0 ≤ x 1 := by
    have h5 : 0 ≤ (p.j : ℝ) * δ := by positivity
    linarith
  have hx1_lt : x 1 < 1 := by
    have h5 : ((p.j : ℝ) + 1) * δ ≤ 1 := by
      have h6 : ((p.j : ℝ) + 1) * δ ≤ (2 ^ k : ℝ) * δ := by gcongr
      linarith [hδ_sum]
    linarith
  simp only [dyadicSquare, Set.mem_setOf_eq]
  <;> simp [hx0_ge, hx0_lt, hx1_ge, hx1_lt] <;> norm_num

/-- Any nonempty finset is a trivial S-set at constant C when C * δ^s ≥ 1. -/
lemma finset_trivial_sset
    {X : Type*} [MetricSpace X] {δ s C : ℝ} {P : Finset X}
    (hδ_pos : 0 < δ) (hs : 0 ≤ s) (hP_nonempty : P.Nonempty)
    (hC_pos : 0 < C) (hC_ge : C * δ ^ s ≥ 1) :
    IsFinsetDeltaSSet δ s C P := by
  refine ⟨hP_nonempty, hδ_pos, hC_pos, hs, fun x r hr => ?_⟩
  have h_sub : (P : Set X) ∩ Metric.closedBall x r ⊆ (P : Set X) := by
    exact Set.inter_subset_left
  have h_mono : Metric.externalCoveringNumber δ.toNNReal
        ((P : Set X) ∩ Metric.closedBall x r) ≤
      Metric.externalCoveringNumber δ.toNNReal (P : Set X) :=
    Metric.externalCoveringNumber_mono_set h_sub
  have hr_pos : 0 < r := by linarith
  have h_rpow_ge : C * r ^ s ≥ 1 := by
    have h1 : δ ^ s ≤ r ^ s := Real.rpow_le_rpow (by linarith) (by linarith) hs
    have h2 : C * δ ^ s ≤ C * r ^ s := by gcongr
    linarith
  have h3 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s := by
    have h4 : 0 ≤ C * r ^ s := by positivity
    have h5 : ENNReal.ofReal (C * r ^ s) =
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hs] <;> rfl
    rw [←h5]
    have h6 : (1 : ENNReal) ≤ ENNReal.ofReal (C * r ^ s) := by
      exact ENNReal.one_le_ofReal.mpr h_rpow_ge
    exact h6
  have h_main : (Metric.externalCoveringNumber δ.toNNReal ((P : Set X) ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal (P : Set X) : ENNReal) := by
    have h_mono' : (Metric.externalCoveringNumber δ.toNNReal ((P : Set X) ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal (P : Set X) : ENNReal) := by
      exact_mod_cast h_mono
    calc
      (Metric.externalCoveringNumber δ.toNNReal ((P : Set X) ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber δ.toNNReal (P : Set X) : ENNReal) := h_mono'
      _ = (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P : Set X) : ENNReal) := by simp
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δ.toNNReal (P : Set X) : ENNReal) := by gcongr
  exact h_main

/-- Constant weakening for IsDeltaSSet. -/
lemma IsDeltaSSet.weaken_constant'
    {X : Type*} [PseudoMetricSpace X] {δ s C C' : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C P) (hC : C ≤ C') (hC'_pos : 0 < C') :
    IsDeltaSSet δ s C' P := by
  rcases h with ⟨hne, hδ, hC_pos, hs, hmain⟩
  refine ⟨hne, hδ, hC'_pos, hs, fun x r hr => ?_⟩
  have h6 := hmain x r hr
  calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
    ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h6
  _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    have hC' : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC
    have h1 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s := by
      gcongr <;> positivity
    gcongr

/-- TRUE PRODUCER: construct coarse S-sets from CombiningConfig + B1 bridge.

    Constructs internally:
    - hP_set_coarse (normal/good/bad branches) using onyx's conversion
    - hP_set_tj_coarse (good branch at min(t_j,1)) using generalized conversion
    - h_unit_coarse, h_diam_coarse from B1 bridge via CoarseGeometricData

    Still parameters:
    - h_improved_incidence_coarse (needs kestrel incidence bridge wiring)
    - h_slope_coarse (needs coarse B1 bridge or direct slope bound lemma) -/
lemma coarse_source_from_config_v2
    {n k m M MΔ : ℕ}
    {s t τ ε_G η ε_N C_P C_P_coarse ε_inc lam δ Δ_coarse : ℝ}
    {K CΔ C'_coarse K_p5 C_coarse : ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {scaleClass : Fin n → ScaleClass}
    {Δ : Fin (n + 1) → ℝ}
    (j0 : Fin n) (hj0 : j0.val = 0)
    (hδ_eq_dyadic : δ = dyadicDelta k)
    (C_between : Fin n → ℝ) (N : Fin n → ℕ)
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (h_exp_condition : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc)
    (hε_inc_pos : 0 < ε_inc)
    (h_tj_ge_t : ∀ (j : Fin n) (t_j : ℝ), scaleClass j = ScaleClass.good t_j → t ≤ t_j)
    -- First scale is not normal (good or bad)
    (h_scale_not_normal : scaleClass j0 ≠ ScaleClass.normal)
    -- Coarse S-set at exponent s (provided by caller; constructed from global input assumptions)
    (hP_set_coarse : IsFinsetDeltaSSet (dyadicDelta m) s C_P_coarse
        (finsetDyadicToDSquare coarseConfig.P₀))
    -- Coarse S-set at exponent min(t_j,1), conditional on good first scale
    (hP_set_tj_coarse : ∀ (t_j : ℝ), scaleClass j0 = ScaleClass.good t_j →
        IsFinsetDeltaSSet (dyadicDelta m) (min t_j 1) C_P_coarse
          (finsetDyadicToDSquare coarseConfig.P₀))
    -- Coarse scale identity
    (hnm : m ≤ k)
    -- B1 bridge output
    (P : Finset (DyadicSquare k))
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty' : P.Nonempty)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K * coarseConfig.P₀.card)
    (hB1 : B1BridgeHypotheses k config)
    (hΔ0 : Δ 0 = 1)
    (hΔ1 : Δ 1 = Δ_coarse)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    -- Incidence (constructed separately via kestrel adapter)
    -- Only needed for the good branch; made conditional so normal branch can use a vacuous proof.
    (h_improved_incidence_coarse : ∀ (t_j : ℝ), scaleClass j0 = ScaleClass.good t_j →
      (coarseConfig.T₀.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow Δ_coarse (-(2 * s + ε_inc))))
    -- Good-branch constant bound for S-set at exponent min t_j 1
    (hCP_coarse_tj_ge : ∀ (t_j : ℝ), scaleClass j0 = ScaleClass.good t_j →
        C_P_coarse ≥ 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ min t_j 1)
    -- Slope bound for coarse tubes (needs coarse B1 bridge or separate derivation)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    -- Constant bounds for S-set construction
    (hCP_coarse_ge : C_P_coarse ≥ 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s)
    (hCP_coarse_trivial : C_P_coarse * (dyadicDelta m) ^ s ≥ 1)
    -- Common parameters
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t)
    (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hτ_pos : 0 < τ) (hCP : 1 ≤ C_P) (hCP_coarse : 1 ≤ C_P_coarse)
    (hlam : 0 < lam)
    (hK_ge1 : 1 ≤ K) (hK_pos : 0 < K)
    (hCΔ_pos : 0 < CΔ) (hCΔ_ge1 : 1 ≤ CΔ)
    (hCΔ_le : CΔ ≤ K * Real.rpow δ (-lam))
    (hC_coarse_ge : C_coarse ≥ K_p5 + 1)
    (hC_coarse_pos : 0 < C_coarse)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hK_p5_pos : 0 < K_p5) (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_spec : ∀ (t : ℝ), s ≤ t → t ≤ 1 →
      ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ m →
        ∀ (P : Finset (DSquare m)), P.Nonempty →
          IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) t C_P P →
          (∀ (x y : DSquare m), x ∈ P → y ∈ P → dist x y ≤ 3) →
          (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
          ∀ (Tp : TubeFamily m),
            (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
            (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
            (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T (Tp p)) →
            (∀ p ∈ P, (M : ℝ) / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
              let T := P.biUnion fun p => Tp p
              (T.card : ℝ) ≥ (1 / K_p5) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K_p5) *
                (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                  (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((t - s) / (1 - s)))
    (hm_ge2 : 2 ≤ m)
    (hΔ_coarse_pos : 0 < Δ_coarse) (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_le_delta : δ ≤ Δ_coarse)
    (hLbar_ge1 : 1 ≤ Real.log (1 / Δ_coarse))
    (hMΔ_pos : 0 < MΔ)
    -- Absorption threshold (bacon's explicit lemmas derive absorption from this)
    (hL_threshold : Real.log (1 / Δ_coarse) ≥ K_p5 * C_P_coarse * 13 * (2 : ℝ) ^ s)
    -- PΔ definition
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
  -- Construct geometric data from B1 bridge
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
  -- Good branch absorption from threshold
  have h_good_absorb : ∀ (t_j : ℝ), scaleClass j0 = ScaleClass.good t_j →
      Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
        K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse (2 * ε_G + ε_N) := by
    intro t_j _
    set L : ℝ := Real.log (1 / Δ_coarse) with hL_def
    have hL_pos : 0 < L := by
      rw [hL_def]; apply Real.log_pos; exact one_lt_one_div hΔ_coarse_pos hΔ_coarse_lt_one
    have hL_ge1 : 1 ≤ L := hLbar_ge1
    have he_ge1 : 1 ≤ C_coarse - K_p5 := by linarith [hC_coarse_ge]
    have h_exp_pos : 0 < 2 * ε_G + ε_N := by linarith
    have hΔ_pow_lt_one : Real.rpow Δ_coarse (2 * ε_G + ε_N) < 1 :=
      Real.rpow_lt_one (by linarith) hΔ_coarse_lt_one h_exp_pos
    have h_main : Real.rpow L (C_coarse - K_p5) ≥ L := by
      have h6 : Real.rpow L (C_coarse - K_p5) ≥ Real.rpow L 1 :=
        Real.rpow_le_rpow_of_exponent_le hL_ge1 he_ge1
      have h7 : Real.rpow L 1 = L := by simp
      rw [h7] at h6; exact h6
    have hRHS : K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse (2 * ε_G + ε_N) <
        K_p5 * C_P_coarse * 13 * Real.rpow 2 s := by
      have h_pos : 0 < K_p5 * C_P_coarse * 13 * Real.rpow 2 s := by
        have h1 : 0 < K_p5 := hK_p5_pos
        have h2 : 0 < C_P_coarse := by linarith [hCP_coarse]
        have h3 : (0 : ℝ) < 13 := by norm_num
        have h4 : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
        positivity
      have h_pow : Real.rpow Δ_coarse (2 * ε_G + ε_N) < 1 := hΔ_pow_lt_one
      nlinarith
    have hL_threshold' : L ≥ K_p5 * C_P_coarse * 13 * Real.rpow 2 s := hL_threshold
    linarith [h_main, hRHS, hL_threshold']
  -- PΔ equalities
  have hPΔ_bad : scaleClass j0 = ScaleClass.bad → PΔ = Δ_coarse := by
    intro hsc
    rw [hPΔ_def]
    have hG : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood) = ∅ := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isGood]
    have hB : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad) = {j0} := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isBad]
    rw [hG, hB, Finset.prod_singleton]
    have h_cast0 : (j0.castSucc : Fin (n + 1)) = 0 := by
      apply Fin.ext; simp [Fin.castSucc, hj0] <;> omega
    have h_cast1 : (Fin.succ j0 : Fin (n + 1)) = 1 := by
      apply Fin.ext
      have h1 : (Fin.succ j0).val = j0.val + 1 := by simp [Fin.val_succ]
      have h2 : (1 : Fin (n + 1)).val = 1 := by
        simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
      rw [h1, h2, hj0] <;> ring
    rw [h_cast0, h_cast1, hΔ0, hΔ1] <;> simp
  have hPΔ_normal : scaleClass j0 = ScaleClass.normal → PΔ = 1 := by
    intro hsc
    rw [hPΔ_def]
    have hG : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood) = ∅ := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isGood]
    have hB : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad) = ∅ := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isBad]
    rw [hG, hB] <;> simp
  have hPΔ_good : ∀ (t_j : ℝ), scaleClass j0 = ScaleClass.good t_j → PΔ = Real.rpow Δ_coarse (-η) := by
    intro t_j hsc
    rw [hPΔ_def]
    have hG : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood) = {j0} := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isGood]
    have hB : ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad) = ∅ := by
      rw [Finset.filter_singleton, hsc] <;> simp [ScaleClass.isBad]
    rw [hG, hB, Finset.prod_singleton]
    have h_cast0 : (j0.castSucc : Fin (n + 1)) = 0 := by
      apply Fin.ext; simp [Fin.castSucc, hj0] <;> omega
    have h_cast1 : (Fin.succ j0 : Fin (n + 1)) = 1 := by
      apply Fin.ext
      have h1 : (Fin.succ j0).val = j0.val + 1 := by simp [Fin.val_succ]
      have h2 : (1 : Fin (n + 1)).val = 1 := by
        simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
      rw [h1, h2, hj0] <;> ring
    rw [h_cast0, h_cast1, hΔ0, hΔ1]
    have h_pos1 : 0 < 1 / Δ_coarse := by positivity
    have h2 : Real.rpow (1 / Δ_coarse) η = Real.exp (η * Real.log (1 / Δ_coarse)) := by
      have h := Real.rpow_def_of_pos h_pos1 η
      exact h.trans (congr_arg Real.exp (by ring))
    have h3 : Real.rpow Δ_coarse (-η) = Real.exp ((-η) * Real.log Δ_coarse) := by
      have h := Real.rpow_def_of_pos hΔ_coarse_pos (-η)
      exact h.trans (congr_arg Real.exp (by ring))
    have h4 : Real.log (1 / Δ_coarse) = -Real.log Δ_coarse := by
      rw [Real.log_div (by norm_num) hΔ_coarse_pos.ne'] <;> simp
    rw [h2, h3, h4, Finset.prod_empty]
    simp
    <;> apply congr_arg Real.exp <;> ring
  -- Call coarse_bound_from_combined_v2
  exact coarse_bound_from_combined_v2
    (hj0 := hj0)
    (hδ_eq_dyadic := hδ_eq_dyadic)
    (C_between := C_between)
    (N := N)
    (hcfg := hcfg)
    (h_tj_ge_t_extra := h_tj_ge_t)
    (h_exp_condition_v2 := h_exp_condition)
    (h_scale_not_normal := h_scale_not_normal)
    (hcoarse_P_nonempty := hcoarse_P_nonempty)
    (h_slope_coarse := h_slope_coarse)
    (h_diam_coarse := h_diam_coarse)
    (h_unit_coarse := h_unit_coarse)
    (hΔ0 := hΔ0)
    (hΔ1 := hΔ1)
    (hΔ_coarse_eq := hΔ_coarse_eq)
    (hP_set_coarse := hP_set_coarse)
    (hP_set_tj_coarse := hP_set_tj_coarse)
    (h_improved_incidence_coarse := h_improved_incidence_coarse)
    (h_good_absorb := h_good_absorb)
    (hs := hs)
    (hs1 := hs1)
    (hst := hst)
    (hεG := hεG)
    (hη := hη)
    (hεN := hεN)
    (hε_inc := hε_inc_pos)
    (hτ_pos := hτ_pos)
    (hCP_coarse := hCP_coarse)
    (hlam := hlam)
    (hK_ge1 := hK_ge1)
    (hK_pos := hK_pos)
    (hCΔ_pos := hCΔ_pos)
    (hCΔ_ge1 := hCΔ_ge1)
    (hCΔ_le := hCΔ_le)
    (hC_coarse_ge := hC_coarse_ge)
    (hC_coarse_pos := hC_coarse_pos)
    (hC'_coarse_ge1 := hC'_coarse_ge1)
    (hK_p5_pos := hK_p5_pos)
    (hK_p5_ge1 := hK_p5_ge1)
    (hK_p5_spec := hK_p5_spec)
    (hm_ge2 := hm_ge2)
    (hΔ_coarse_pos := hΔ_coarse_pos)
    (hΔ_coarse_lt_one := hΔ_coarse_lt_one)
    (hδ_pos := hδ_pos)
    (hδ_lt_one := hδ_lt_one)
    (hδ_le_delta := hδ_le_delta)
    (hLbar_ge1 := hLbar_ge1)
    (hMΔ_pos := hMΔ_pos)
    (PΔ := PΔ)
    (hPΔ_def := hPΔ_def)

/-! ========================================================================
    Normal-only variant (no improved incidence required)

    Used by InductiveStepCore_v2 for the m≥2 normal first-scale sub-case.
    ======================================================================== -/

/-- Coarse bound for m≥2, normal first scale, without improved incidence.

    Constructs S-set conversion, geometric data, and absorption from the
    available config/B1 bridge output, then calls coarse_bound_normal.

    The caller supplies C_P_coarse (must be large enough for S-set weakening),
    hC_coarse_ge (must include C_P_coarse), and hL_threshold (log absorption).
    These follow from the global smallness conditions chosen by the outer theorem. -/
lemma coarse_source_normal_only
    {n k m M MΔ : ℕ}
    {s t τ ε_G η ε_N C_P C_P_coarse lam δ Δ_coarse : ℝ}
    {K CΔ C'_coarse K_p5 C_coarse : ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {scaleClass : Fin n → ScaleClass}
    {j0 : Fin n}
    {Δ : Fin (n + 1) → ℝ}
    {C_between : Fin n → ℝ}
    {N : Fin n → ℕ}
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (P : Finset (DyadicSquare k))
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty' : P.Nonempty)
    (hnm : m ≤ k)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K * coarseConfig.P₀.card)
    (hj0 : j0.val = 0)
    (h_normal : scaleClass j0 = ScaleClass.normal)
    (hΔ0 : Δ 0 = 1)
    (hΔ1 : Δ 1 = Δ_coarse)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    -- C_P_coarse and bounds
    (hCP_coarse_ge1 : 1 ≤ C_P_coarse)
    (hCP_coarse_pos : 0 < C_P_coarse)
    (hCP_coarse_weaken : C_P_coarse ≥ 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s)
    -- Common parameters
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t)
    (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hτ_pos : 0 < τ) (hCP : 1 ≤ C_P)
    (hlam : 0 < lam)
    (hK_ge1 : 1 ≤ K) (hK_pos : 0 < K)
    (hCΔ_pos : 0 < CΔ) (hCΔ_ge1 : 1 ≤ CΔ)
    (hCΔ_le : CΔ ≤ K * Real.rpow δ (-lam))
    (hC_coarse_ge : C_coarse ≥ K_p5 + 1)
    (hC_coarse_pos : 0 < C_coarse)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hK_p5_pos : 0 < K_p5) (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_spec : ∀ (t : ℝ), s ≤ t → t ≤ 1 →
      ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ m →
        ∀ (P : Finset (DSquare m)), P.Nonempty →
          IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) t C_P P →
          (∀ (x y : DSquare m), x ∈ P → y ∈ P → dist x y ≤ 3) →
          (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
          ∀ (Tp : TubeFamily m),
            (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
            (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
            (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T (Tp p)) →
            (∀ p ∈ P, (M : ℝ) / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
              let T := P.biUnion fun p => Tp p
              (T.card : ℝ) ≥ (1 / K_p5) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K_p5) *
                (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                  (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((t - s) / (1 - s)))
    (hm_ge2 : 2 ≤ m)
    (hΔ_coarse_pos : 0 < Δ_coarse) (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_le_delta : δ ≤ Δ_coarse)
    (hLbar_ge1 : 1 ≤ Real.log (1 / Δ_coarse))
    (hMΔ_pos : 0 < MΔ)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    -- Absorption (proved by caller from exponential Δ^ε_N decay vs polynomial C_P_coarse growth)
    (h_absorb : Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
      K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse ε_N) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) := by
  classical
  -- Point set contained in unit square
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
  -- Construct coarse S-set at exponent s
  have hbet0 := hcfg.h_normal j0 h_normal
  have hbet : IsSetBetweenScales config.pointSet Δ_coarse 1 s (C_between j0) := by
    simpa [h_Delta_succ, h_Delta_cast] using hbet0
  have hC_between_pos : 0 < C_between j0 := hbet.2.2.2.2.1
  have hsset : IsDeltaSSet Δ_coarse s (C_between j0) config.pointSet :=
    isSetBetweenScales_to_isDeltaSSet_unit hbet hP_sub_unit hpointSet_nonempty
  rw [hΔ_coarse_eq] at hsset
  rcases coarse_corners_sset_from_fine_pointset hnm config P hP_sub coarseConfig
      hcoarse_P_eq h_card_bound hsset (by linarith) hC_between_pos hK_pos hP_nonempty'
    with ⟨C_conv, hC_conv_eq, hC_conv_pos, hsset_conv⟩
  have h_le : C_conv ≤ C_P_coarse := by
    rw [hC_conv_eq]
    have h1 : 81 * K * (C_between j0) * (2 * Real.sqrt 2) ^ s ≤
        81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s := by
      have h2 : C_between j0 ≤ max (C_between j0) 1 := le_max_left _ _
      gcongr
    linarith [hCP_coarse_weaken]
  have hP_set_coarse : IsFinsetDeltaSSet (dyadicDelta m) s C_P_coarse
      (finsetDyadicToDSquare coarseConfig.P₀) :=
    IsDeltaSSet.weaken_constant' hsset_conv h_le hCP_coarse_pos
  -- Construct geometric data
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
  -- Coarse P nonempty
  have hcoarse_P_nonempty : coarseConfig.P₀.Nonempty := by
    rw [hcoarse_P_eq]
    exact hP_nonempty'.image _
  -- Specialize K_p5_spec to t=s
  have hK_p5_spec_s := hK_p5_spec s (by linarith) (by linarith)
  -- Call coarse_bound_normal
  exact coarse_bound_normal
    (hK_p5_pos := hK_p5_pos)
    (hK_p5_ge1 := hK_p5_ge1)
    (hK_p5_spec := hK_p5_spec_s)
    (hK_B1_ge1 := hK_ge1)
    (hCΔ_pos := hCΔ_pos)
    (hCΔ_ge1 := hCΔ_ge1)
    (hCΔ_le := hCΔ_le)
    (hC_coarse_ge := by linarith)
    (hC'_coarse_ge1 := hC'_coarse_ge1)
    (hm_ge2 := hm_ge2)
    (hΔ_coarse_eq := hΔ_coarse_eq)
    (hΔ_coarse_pos := hΔ_coarse_pos)
    (hΔ_coarse_lt_one := hΔ_coarse_lt_one)
    (hδ_pos := hδ_pos)
    (hδ_lt_one := hδ_lt_one)
    (hlam := hlam)
    (hs := hs)
    (hεN := hεN)
    (hCP_coarse_pos := hCP_coarse_pos)
    (hCP_coarse_ge1 := hCP_coarse_ge1)
    (hP_nonempty := hcoarse_P_nonempty)
    (hMΔ_pos := hMΔ_pos)
    (hP_set_coarse := hP_set_coarse)
    (h_slope_coarse := h_slope_coarse)
    (h_diam_coarse := h_diam_coarse)
    (h_unit_coarse := h_unit_coarse)
    (h_absorb := h_absorb)

/-- Helper: derive `1 ≤ CΔ` from the B1 bridge cardinality bounds.

    Given `Poly ≤ C₁ ≤ K * CΔ` and `K ≤ Poly`, with `Poly > 0`, we get
    `Poly ≤ K * CΔ ≤ Poly * CΔ`, hence `1 ≤ CΔ`. -/
lemma coarse_CDelta_ge_one
    {K CΔ Poly C1 : ℝ}
    (hPoly_pos : 0 < Poly)
    (hC1_pos : 0 < C1)
    (h1 : Poly ≤ C1)
    (h2 : C1 ≤ K * CΔ)
    (h3 : K ≤ Poly)
    (hK_pos : 0 < K) :
    1 ≤ CΔ := by
  have h4 : Poly ≤ K * CΔ := le_trans h1 h2
  have hCΔ_pos : 0 < CΔ := by
    have h5 : 0 < K * CΔ := lt_of_lt_of_le hC1_pos h2
    by_contra h6
    have h7 : CΔ ≤ 0 := by linarith
    have h8 : K * CΔ ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) h7
    linarith
  have h9 : K * CΔ ≤ Poly * CΔ := by
    gcongr
    <;> linarith
  have h10 : Poly ≤ Poly * CΔ := le_trans h4 h9
  have h11 : 1 ≤ CΔ := by
    calc (1 : ℝ)
      = Poly / Poly := by field_simp [hPoly_pos.ne'] <;> ring
    _ ≤ (Poly * CΔ) / Poly := by gcongr
    _ = CΔ := by field_simp [hPoly_pos.ne'] <;> ring
  exact h11

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
