module

/-
  FineBranchHcfgFine — Construct fine CombiningConfig via thinning route.

  Adapts FineConfigConstruction.lean to work with B1 bridge's thinned
  subset P instead of assuming full config.P₀.filter.

  Whiteprint node: combining_theorem_rework / fine_branch_hcfg_fine
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineConfigThinning
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FinePointsetGlue
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CBetweenGlue
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BetweenScalesTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DiscretisedFurstenbergEstimate.BasicUniformization
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- Local dyadicDelta_le_iff. -/
lemma dyadicDelta_le_iff''' {m k : ℕ} :
    dyadicDelta k ≤ dyadicDelta m ↔ m ≤ k := by
  constructor
  · intro h
    by_contra h'
    have h'' : k < m := by omega
    have h3 : (2 : ℝ)^k < (2 : ℝ)^m := by gcongr <;> norm_num
    have h41 : 0 < (2 : ℝ)^k := by positivity
    have h42 : 0 < (2 : ℝ)^m := by positivity
    have h4 : (1 : ℝ) / (2 : ℝ)^m < (1 : ℝ) / (2 : ℝ)^k := by
      calc (1 : ℝ) / (2 : ℝ)^m
        = (2 : ℝ)^k / ((2 : ℝ)^m * (2 : ℝ)^k) := by field_simp [h41.ne', h42.ne'] <;> ring
      _ < (2 : ℝ)^m / ((2 : ℝ)^m * (2 : ℝ)^k) := by gcongr
      _ = (1 : ℝ) / (2 : ℝ)^k := by field_simp [h41.ne', h42.ne'] <;> ring
    have h5 : ¬ (1 : ℝ) / (2 : ℝ)^k ≤ (1 : ℝ) / (2 : ℝ)^m := by linarith
    simpa [dyadicDelta] using h5 h
  · intro h
    have h3 : (2 : ℝ)^m ≤ (2 : ℝ)^k := by gcongr <;> norm_num
    have h41 : 0 < (2 : ℝ)^m := by positivity
    have h42 : 0 < (2 : ℝ)^k := by positivity
    have h4 : (1 : ℝ) / (2 : ℝ)^k ≤ (1 : ℝ) / (2 : ℝ)^m := by gcongr
    simpa [dyadicDelta] using h4

/-- Construct fine CombiningConfig via thinning from B1 bridge data. -/
lemma fine_branch_hcfg_fine
    {n_fine k m : ℕ} (hn_fine_pos : 0 < n_fine) (hm_pos : 0 < m) (hmk : m ≤ k)
    {s t τ ε_G η ε_N C_P C_P_fine : ℝ}
    {M MΔ : ℕ} {CΔ : ℝ}
    {lam lam_tail δ_tail : ℝ}
    (hlam : 0 < lam) (hlam_tail_pos : 0 < lam_tail)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (hs_nonneg : 0 ≤ s)
    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (Δ : Fin (n_fine + 2) → ℝ)
    (scaleClass : Fin (n_fine + 1) → ScaleClass)
    (N : Fin (n_fine + 1) → ℕ)
    (C_between : Fin (n_fine + 1) → ℝ)
    (hcfg : CombiningConfig s t τ (n_fine + 1) ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (K : ℝ) (hK_pos : 0 < K) (hK_ge1 : 1 ≤ K)
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.P₀)
    (P : Finset (DyadicSquare k)) (hP_sub : P ⊆ config.P₀)
    (MQ : DyadicSquare m → ℕ)
    (hMQ : 0 < MQ Q)
    (fineConfig : CTNiceConfiguration (k - m) s (Real.rpow (dyadicDelta (k - m)) (-lam_tail)) (MQ Q))
    (fineConfig_B1 : B1BridgeHypotheses (k - m) fineConfig)
    (hfine_P_eq : fineConfig.P₀ =
      (P.filter (fun p => squareContained hmk p Q)).image
        (fun p => InductionConfigurations.squareHomothety hmk Q p))
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hmk))
    (h_card_density : ((config.P₀.filter (fun p => squareContained hmk p Q)).card : ℝ) ≤
      K * ((P.filter (fun p => squareContained hmk p Q)).card : ℝ))
    (hΔ1_eq : Δ 1 = dyadicDelta m)
    (Δ' : Fin (n_fine + 1) → ℝ)
    (hΔ'_def : ∀ i, Δ' i = Δ (Fin.succ i) / Δ 1)
    (scaleClass' : Fin n_fine → ScaleClass)
    (hscaleClass'_def : ∀ j, scaleClass' j = scaleClass (Fin.succ j))
    (C_between' : Fin n_fine → ℝ)
    (hC_between'_def : ∀ j, C_between' j = C_between (Fin.succ j))
    (δ_tail : ℝ) (hδ_tail_pos : 0 < δ_tail)
    (hδbar_le_dtail : dyadicDelta (k - m) ≤ δ_tail)
    (h_absorb_normal : ∀ (j : Fin n_fine), scaleClass' j = ScaleClass.normal →
      9 * (C_between' j : ℝ) * 2 * K * (24 * Real.log (1 / dyadicDelta (k - m)) / (n_fine : ℝ)) ^ n_fine * (4 : ℝ)^n_fine ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_N)
    (h_absorb_good : ∀ (j : Fin n_fine) (t_j : ℝ), scaleClass' j = ScaleClass.good t_j →
      9 * (C_between' j : ℝ) * 2 * K * (24 * Real.log (1 / dyadicDelta (k - m)) / (n_fine : ℝ)) ^ n_fine * (4 : ℝ)^n_fine ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_G)
    (C_n : ℝ) (hCn_ge1 : 1 ≤ C_n)
    (h_small : Real.log (1 / dyadicDelta (k - m)) ≥ Real.rpow τ (-(C_P + C_n)))
    (hCP : 1 ≤ C_P)
    (hCP_fine_eq : C_P_fine = C_P + 2 * C_n)
    (hεG_pos : 0 < ε_G) (hεN_pos : 0 < ε_N)
    (hk_pos : 0 < k) (hm_lt_k : m < k)
    (h_scale_sep : dyadicDelta (k - m) ≤ (dyadicDelta k)^τ) :
    ∃ (config'' : CTNiceConfiguration (k - m) s (Real.rpow (dyadicDelta (k - m)) (-lam_tail)) (MQ Q))
      (C_between'' : Fin n_fine → ℝ)
      (N'' : Fin n_fine → ℕ),
      CombiningConfig s t τ n_fine ε_G η lam_tail ε_N C_P_fine C_between''
        (k - m) (MQ Q) config'' Δ' scaleClass' N'' ∧
      B1BridgeHypotheses (k - m) config'' ∧
      config''.T₀ = fineConfig.T₀ := by
  let δbar := dyadicDelta (k - m)
  have hδbar_pos : 0 < δbar := dyadicDelta_pos (k - m)
  have hδbar_lt_one : δbar < 1 := by
    have h5 : 0 < k - m := by omega
    have h6 : (1 : ℝ) < (2 : ℝ)^(k - m) := one_lt_pow₀ (by norm_num) h5.ne'
    have h7 : (1 : ℝ) / (2 : ℝ)^(k - m) < 1 := (div_lt_one (by positivity)).mpr h6
    simpa [δbar, dyadicDelta, one_div] using h7

  have hΔ'_pos : ∀ i, 0 < Δ' i := by
    intro i; rw [hΔ'_def]; exact div_pos (hcfg.hΔ_pos _) (hcfg.hΔ_pos 1)
  have hΔ'_strict : ∀ j : Fin n_fine, Δ' (Fin.succ j) < Δ' j.castSucc := by
    intro j
    rw [hΔ'_def (Fin.succ j), hΔ'_def j.castSucc]
    have h : Δ (Fin.succ (Fin.succ j)) < Δ (Fin.succ j).castSucc := hcfg.hΔ_strict (Fin.succ j)
    exact div_lt_div_of_pos_right h (hcfg.hΔ_pos 1)
  have hΔ'_start : Δ' 0 = 1 := by
    rw [hΔ'_def 0]
    have h_succ0 : (Fin.succ (0 : Fin (n_fine + 1)) : Fin (n_fine + 2)) = 1 := by
      apply Fin.ext <;> simp
    rw [h_succ0] <;> field_simp [(hcfg.hΔ_pos 1).ne'] <;> ring
  have hΔ'_end : Δ' (Fin.last n_fine) = δbar := by
    rw [hΔ'_def (Fin.last n_fine)]
    have h_succ_last : Fin.succ (Fin.last n_fine) = Fin.last (n_fine + 1) := by
      apply Fin.ext; simp [Fin.last] <;> omega
    rw [h_succ_last, hcfg.hΔ_end, hΔ1_eq]
    have h7 : dyadicDelta k / dyadicDelta m = dyadicDelta (k - m) := by
      have h8 : m + (k - m) = k := by omega
      have h91 : (2 : ℝ)^m * (2 : ℝ)^(k - m) = (2 : ℝ)^k := by
        rw [← pow_add] <;> rw [h8]
      have h9 : dyadicDelta k = dyadicDelta m * dyadicDelta (k - m) := by
        simp only [dyadicDelta]; field_simp <;> rw [h91] <;> ring
      rw [h9]; have h10 : 0 < dyadicDelta m := dyadicDelta_pos m
      field_simp [h10.ne'] <;> ring
    exact h7
  have hΔ'_dyadic : ∀ i, Δ' i ∈ dyadicScales := by
    intro i
    have h4 : Δ' i ≤ 1 := (delta_chain_start_property hΔ'_strict i).trans hΔ'_start.le
    have h4' : Δ (Fin.succ i) ≤ Δ 1 := by
      rw [hΔ'_def i] at h4; exact (div_le_one (hcfg.hΔ_pos 1)).mp h4
    have h5 : Δ (Fin.succ i) / Δ 1 ∈ dyadicScales := dyadic_quotient (hcfg.hΔ_dyadic (Fin.succ i))
      (by rw [hΔ1_eq]; simp [dyadicScales]; exact ⟨m, by simp [dyadicDelta]⟩)
      h4' (hcfg.hΔ_pos (Fin.succ i))
    have h6 : Δ' i = Δ (Fin.succ i) / Δ 1 := hΔ'_def i
    rw [h6]; exact h5

  let a : Fin (n_fine + 1) → ℕ := fun i => Classical.choose (hΔ'_dyadic i)
  have ha_spec : ∀ i, Δ' i = dyadicDelta (a i) := by
    intro i; dsimp only [a]
    have h := Classical.choose_spec (hΔ'_dyadic i)
    simpa [dyadicDelta, zpow_neg] using h
  have ha_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j) := by
    intro j
    have h1 : Δ' (Fin.succ j) < Δ' j.castSucc := hΔ'_strict j
    rw [ha_spec (Fin.succ j), ha_spec j.castSucc] at h1
    have h2 : ¬ dyadicDelta (a j.castSucc) ≤ dyadicDelta (a (Fin.succ j)) := not_le.mpr h1
    have h3 : ¬ (a (Fin.succ j) ≤ a j.castSucc) := by rwa [dyadicDelta_le_iff'''] at h2
    omega
  have h_a_last : a (Fin.last n_fine) = k - m := by
    have h1 : Δ' (Fin.last n_fine) = dyadicDelta (a (Fin.last n_fine)) := ha_spec (Fin.last n_fine)
    have h_eq : dyadicDelta (a (Fin.last n_fine)) = δbar := h1.symm.trans hΔ'_end
    have h4 : (2 : ℝ)^(a (Fin.last n_fine)) = (2 : ℝ)^(k - m) := by
      have h5 : dyadicDelta (a (Fin.last n_fine)) = dyadicDelta (k - m) := by simpa [δbar] using h_eq
      simpa [dyadicDelta] using h5
    have h4' : (2 : ℕ)^(a (Fin.last n_fine)) = (2 : ℕ)^(k - m) := by exact_mod_cast h4
    exact Nat.pow_right_injective (a := 2) (by norm_num) h4'
  have ha_last_max : ∀ i, a i ≤ a (Fin.last n_fine) := by
    intro i
    have h6 : Δ' (Fin.last n_fine) ≤ Δ' i := delta_chain_property hΔ'_strict hΔ'_start i
    have h4 : dyadicDelta (a (Fin.last n_fine)) ≤ dyadicDelta (a i) := by
      rw [←ha_spec (Fin.last n_fine), ←ha_spec i]; exact h6
    exact dyadicDelta_le_iff'''.mp h4
  have h_nfine_le_km : n_fine ≤ k - m := by
    have ha0 : a 0 = 0 := by
      have h1 : Δ' 0 = dyadicDelta (a 0) := ha_spec 0
      have h_eq : dyadicDelta (a 0) = 1 := h1.symm.trans hΔ'_start
      have h3 : (2 : ℝ)^(a 0) = 1 := by simpa [dyadicDelta] using h_eq
      by_cases h4 : a 0 = 0
      · exact h4
      · have h5 : 0 < a 0 := Nat.pos_of_ne_zero h4
        have h6 : (1 : ℝ) < (2 : ℝ)^(a 0) := one_lt_pow₀ (by norm_num) h5.ne'
        linarith
    have ha_strict_mono : ∀ j : Fin n_fine, a j.castSucc < a (Fin.succ j) := by
      intro j
      have h1 : Δ' (Fin.succ j) < Δ' j.castSucc := hΔ'_strict j
      rw [ha_spec (Fin.succ j), ha_spec j.castSucc] at h1
      have h2 : ¬ dyadicDelta (a j.castSucc) ≤ dyadicDelta (a (Fin.succ j)) := not_le.mpr h1
      have h3 : ¬ (a (Fin.succ j) ≤ a j.castSucc) := by rwa [dyadicDelta_le_iff'''] at h2
      omega
    have ha_ge_val : ∀ i : Fin (n_fine + 1), a i ≥ i.val := by
      intro i
      induction i using Fin.induction with
      | zero => simp [ha0] <;> omega
      | succ i ih =>
        have h_strict : a i.castSucc < a (Fin.succ i) := ha_strict_mono i
        have h_ih : a i.castSucc ≥ i.val := by exact_mod_cast ih
        have h9 : a (Fin.succ i) ≥ a i.castSucc + 1 := by omega
        have h10 : a i.castSucc + 1 ≥ i.val + 1 := by omega
        have h11 : (Fin.succ i).val = i.val + 1 := by simp
        omega
    have h1 : a (Fin.last n_fine) ≥ (Fin.last n_fine).val := ha_ge_val (Fin.last n_fine)
    have h2 : (Fin.last n_fine).val = n_fine := by simp [Fin.last]
    rw [h_a_last] at h1; omega

  let P_full_Q := config.P₀.filter (fun p => squareContained hmk p Q)
  let S_full : Finset (ℤ × ℤ) := P_full_Q.image (fun p =>
    ((InductionConfigurations.squareHomothety hmk Q p).i,
     (InductionConfigurations.squareHomothety hmk Q p).j))
  let S' : Finset (ℤ × ℤ) := fineConfig.P₀.image (fun p => (p.i, p.j))

  have hS'_sub : S' ⊆ S_full := by
    intro idx hidx
    rcases Finset.mem_image.mp hidx with ⟨p', hp', rfl⟩
    rw [hfine_P_eq] at hp'
    rcases Finset.mem_image.mp hp' with ⟨p, hp, rfl⟩
    have hpf := Finset.mem_filter.mp hp
    have hp_full : p ∈ P_full_Q := by
      simp only [P_full_Q, Finset.mem_filter]
      exact ⟨hP_sub hpf.1, hpf.2⟩
    exact Finset.mem_image.mpr ⟨p, hp_full, by simp [InductionConfigurations.squareHomothety]⟩

  have h_inj1 : Function.Injective (fun (p : DyadicSquare (k - m)) => (p.i, p.j)) := by
    intro p1 p2 h
    have h' : (p1.i, p1.j) = (p2.i, p2.j) := h
    have hi : p1.i = p2.i := congrArg Prod.fst h'
    have hj : p1.j = p2.j := congrArg Prod.snd h'
    cases p1 <;> cases p2 <;> simp [hi, hj] <;> tauto
  have h_inj_homothety : Function.Injective
      (fun (p : DyadicSquare k) => InductionConfigurations.squareHomothety hmk Q p) := by
    intro p1 p2 h
    have hi : (InductionConfigurations.squareHomothety hmk Q p1).i =
               (InductionConfigurations.squareHomothety hmk Q p2).i := by
      exact congrArg (fun (q : DyadicSquare (k - m)) => q.i) h
    have hj : (InductionConfigurations.squareHomothety hmk Q p1).j =
               (InductionConfigurations.squareHomothety hmk Q p2).j := by
      exact congrArg (fun (q : DyadicSquare (k - m)) => q.j) h
    have h_i : p1.i = p2.i := by
      simp [InductionConfigurations.squareHomothety] at hi
      linarith
    have h_j : p1.j = p2.j := by
      simp [InductionConfigurations.squareHomothety] at hj
      linarith
    cases p1 <;> cases p2 <;> simp [h_i, h_j] <;> tauto
  have h_inj2 : Function.Injective (fun (p : DyadicSquare k) =>
      ((InductionConfigurations.squareHomothety hmk Q p).i,
       (InductionConfigurations.squareHomothety hmk Q p).j)) := by
    intro p1 p2 h
    have h' : ((InductionConfigurations.squareHomothety hmk Q p1).i,
                (InductionConfigurations.squareHomothety hmk Q p1).j) =
               ((InductionConfigurations.squareHomothety hmk Q p2).i,
                (InductionConfigurations.squareHomothety hmk Q p2).j) := h
    have hi : (InductionConfigurations.squareHomothety hmk Q p1).i =
               (InductionConfigurations.squareHomothety hmk Q p2).i := congrArg Prod.fst h'
    have hj : (InductionConfigurations.squareHomothety hmk Q p1).j =
               (InductionConfigurations.squareHomothety hmk Q p2).j := congrArg Prod.snd h'
    have h_i : p1.i = p2.i := by
      simp [InductionConfigurations.squareHomothety] at hi <;> linarith
    have h_j : p1.j = p2.j := by
      simp [InductionConfigurations.squareHomothety] at hj <;> linarith
    cases p1 <;> cases p2 <;> simp [h_i, h_j] <;> tauto
  have h_density' : (S'.card : ℝ) ≥ (S_full.card : ℝ) / K := by
    have h1 : S'.card = fineConfig.P₀.card := Finset.card_image_of_injective _ h_inj1
    have h2 : S_full.card = P_full_Q.card := Finset.card_image_of_injective _ h_inj2
    have h3 : fineConfig.P₀.card = (P.filter (fun p => squareContained hmk p Q)).card := by
      rw [hfine_P_eq]
      rw [Finset.card_image_of_injective _ h_inj_homothety]
    have h4 : (P_full_Q.card : ℝ) ≤ K * ((P.filter (fun p => squareContained hmk p Q)).card : ℝ) :=
      h_card_density
    have h6 : 0 < K := hK_pos
    rw [h1, h2, h3]
    have h7 : (P_full_Q.card : ℝ) / K ≤ ((P.filter (fun p => squareContained hmk p Q)).card : ℝ) := by
      calc (P_full_Q.card : ℝ) / K
        ≤ (K * ((P.filter (fun p => squareContained hmk p Q)).card : ℝ)) / K := by gcongr
      _ = ((P.filter (fun p => squareContained hmk p Q)).card : ℝ) := by
        have h9 : K * ((P.filter (fun p => squareContained hmk p Q)).card : ℝ) / K =
            ((P.filter (fun p => squareContained hmk p Q)).card : ℝ) := by
          calc K * ((P.filter (fun p => squareContained hmk p Q)).card : ℝ) / K
            = (K / K) * ((P.filter (fun p => squareContained hmk p Q)).card : ℝ) := by ring
          _ = 1 * ((P.filter (fun p => squareContained hmk p Q)).card : ℝ) := by rw [div_self h6.ne']
          _ = ((P.filter (fun p => squareContained hmk p Q)).card : ℝ) := by ring
        exact h9
    exact h7

  have h_unit_S' : ∀ idx ∈ S', 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)) := by
    intro idx hidx
    rcases Finset.mem_image.mp hidx with ⟨p, hp, rfl⟩
    have h := fineConfig_B1.h_squares_unit p hp
    rw [h_a_last]
    exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  have h_unit_S_full : ∀ idx ∈ S_full, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)) := by
    intro idx hidx
    rcases Finset.mem_image.mp hidx with ⟨p, hp, rfl⟩
    have hpc : squareContained hmk p Q := (Finset.mem_filter.mp hp).2
    let q := InductionConfigurations.squareHomothety hmk Q p
    have hqi : q.i = p.i - Q.i * (InductionConfigurations.refinementFactor k m) := by rfl
    have hqj : q.j = p.j - Q.j * (InductionConfigurations.refinementFactor k m) := by rfl
    have hcrf : (InductionConfigurations.refinementFactor k m : ℤ) = (2 : ℤ)^(k - m) := by
      simp [InductionConfigurations.refinementFactor] <;> norm_cast <;> omega
    have h1 : (Q.i : ℤ) * InductionConfigurations.refinementFactor k m ≤ p.i := hpc.1
    have h2 : p.i < (Q.i + 1) * InductionConfigurations.refinementFactor k m := hpc.2.1
    have h3 : (Q.j : ℤ) * InductionConfigurations.refinementFactor k m ≤ p.j := hpc.2.2.1
    have h4 : p.j < (Q.j + 1) * InductionConfigurations.refinementFactor k m := hpc.2.2.2
    have h_qi_nonneg : 0 ≤ q.i := by rw [hqi]; exact sub_nonneg.mpr h1
    have h_qj_nonneg : 0 ≤ q.j := by rw [hqj]; exact sub_nonneg.mpr h3
    have h_qi_lt : q.i < (2 : ℤ)^(k - m) := by
      rw [hqi]; have h5 : p.i < Q.i * InductionConfigurations.refinementFactor k m + InductionConfigurations.refinementFactor k m := by linarith
      rw [hcrf] at * <;> linarith
    have h_qj_lt : q.j < (2 : ℤ)^(k - m) := by
      rw [hqj]; have h5 : p.j < Q.j * InductionConfigurations.refinementFactor k m + InductionConfigurations.refinementFactor k m := by linarith
      rw [hcrf] at * <;> linarith
    rw [h_a_last]; exact ⟨h_qi_nonneg, h_qj_nonneg, h_qi_lt, h_qj_lt⟩

  let S_global : Finset (ℤ × ℤ) := P_full_Q.image (fun p : DyadicSquare k => (p.i, p.j))
  have h_pointSet_eq : config.pointSet ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j =
      setFromIndices (dyadicDelta k) S_global := by
    have h : config.pointSet ∩ CombiningTheorem.dyadicSquare (dyadicDelta m) Q.i Q.j =
        setFromIndices (dyadicDelta k) S_global :=
      pointSet_inter_coarseSquare hmk config Q
    have h5 : CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j =
               CombiningTheorem.dyadicSquare (dyadicDelta m) Q.i Q.j := by
      rw [hΔ1_eq]
    rw [h5]; exact h
  let offset := DiscretisedFurstenbergEstimate.CombiningTheoremRework.offset
  let setFromIndices_homothety := DiscretisedFurstenbergEstimate.CombiningTheoremRework.setFromIndices_homothety (m := m) (a_last := k - m)
  have h_Sglobal_eq : S_global = S_full.image (offset (k - m) (Q.i, Q.j)) := by
    ext idx
    simp only [S_global, S_full, Finset.mem_image, offset]
    constructor
    · rintro ⟨p, hp, rfl⟩
      let q := InductionConfigurations.squareHomothety hmk Q p
      have hqi : q.i = p.i - Q.i * (InductionConfigurations.refinementFactor k m) := by rfl
      have hqj : q.j = p.j - Q.j * (InductionConfigurations.refinementFactor k m) := by rfl
      have hrf : (InductionConfigurations.refinementFactor k m : ℤ) = (2 : ℤ)^(k - m) := by
        simp [InductionConfigurations.refinementFactor] <;> norm_cast <;> omega
      refine ⟨(q.i, q.j), ⟨p, hp, by simp [q] <;> rfl⟩, ?_⟩
      have h6 : Q.i * (2 : ℤ)^(k - m) + q.i = p.i := by
        rw [hqi, hrf] <;> ring
      have h7 : Q.j * (2 : ℤ)^(k - m) + q.j = p.j := by
        rw [hqj, hrf] <;> ring
      exact Prod.ext h6 h7
    · rintro ⟨q, ⟨p, hp, hq_eq⟩, rfl⟩
      have hq_eq' : ((InductionConfigurations.squareHomothety hmk Q p).i,
                      (InductionConfigurations.squareHomothety hmk Q p).j) = q := hq_eq
      have hqi : q.1 = (InductionConfigurations.squareHomothety hmk Q p).i := (congrArg Prod.fst hq_eq').symm
      have hqj : q.2 = (InductionConfigurations.squareHomothety hmk Q p).j := (congrArg Prod.snd hq_eq').symm
      have h_qi2 : (InductionConfigurations.squareHomothety hmk Q p).i = p.i - Q.i * (2 : ℤ)^(k - m) := by
        simpa [InductionConfigurations.squareHomothety, InductionConfigurations.refinementFactor] using rfl
      have h_qj2 : (InductionConfigurations.squareHomothety hmk Q p).j = p.j - Q.j * (2 : ℤ)^(k - m) := by
        simpa [InductionConfigurations.squareHomothety, InductionConfigurations.refinementFactor] using rfl
      have h_off1 : (p.i, p.j) = offset (k - m) (Q.i, Q.j) q := by
        have h1 : Q.i * (2 : ℤ)^(k - m) + q.1 = p.i := by
          rw [hqi, h_qi2] <;> ring
        have h2 : Q.j * (2 : ℤ)^(k - m) + q.2 = p.j := by
          rw [hqj, h_qj2] <;> ring
        exact Prod.ext h1.symm h2.symm
      exact ⟨p, hp, h_off1⟩
  have hP_Q_eq : homothetyS (Δ 1) Q.i Q.j ''
      (config.pointSet ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j) =
      setFromIndices δbar S_full := by
    rw [h_pointSet_eq, h_Sglobal_eq, hΔ1_eq]
    have h_k_eq : k = m + (k - m) := by omega
    exact setFromIndices_homothety k h_k_eq Q S_full

  have hP_full_Q_nonempty : P_full_Q.Nonempty := by
    have h1 : (config.P₀.filter (fun p => squareContained hmk p Q)).Nonempty := by
      have h2 : Q ∈ coarseConfig.P₀ := hQ
      rw [hcoarse_P_eq] at h2
      rcases Finset.mem_image.mp h2 with ⟨p, hp, h_eq⟩
      have h3 : squareContained hmk p Q := by
        exact (containingSquare_iff hmk p Q).mp h_eq
      exact ⟨p, Finset.mem_filter.mpr ⟨hP_sub hp, h3⟩⟩
    exact h1

  let N_full : Fin n_fine → ℕ := fun j => N (Fin.succ j)
  have h_unif_full : RangeUniformityProp n_fine a S_full N_full :=
    isUniformAtScales_to_rangeUniformity_Q
      (by omega) config.pointSet Δ N hcfg.h_uniform m Q hΔ1_eq hcfg.hΔ_end
      a (fun i => Eq.trans (hΔ'_def i).symm (ha_spec i))
      ha_mono ha_last_max S_full
      (hP_full_Q_nonempty.image _)
      (by have h6 : a (Fin.last n_fine) = k - m := h_a_last
          simpa [h6] using hP_Q_eq)
      h_unit_S_full

  let Δ_r : Fin (n_fine + 1) → ℝ := fun i => Δ (Fin.succ i)
  let scaleClass_r : Fin n_fine → ScaleClass := fun j => scaleClass (Fin.succ j)
  let C_between_r : Fin n_fine → ℝ := fun j => C_between (Fin.succ j)
  have hΔ_r_pos : ∀ i, 0 < Δ_r i := by intro i; exact hcfg.hΔ_pos (Fin.succ i)
  have hΔ_r_dyadic : ∀ i, Δ_r i ∈ dyadicScales := by intro i; exact hcfg.hΔ_dyadic (Fin.succ i)
  have hΔ_r_decreasing : ∀ j : Fin n_fine, Δ_r (Fin.succ j) ≤ Δ_r j.castSucc := by
    intro j
    have h : Δ (Fin.succ (Fin.succ j)) < Δ (Fin.succ j).castSucc := hcfg.hΔ_strict (Fin.succ j)
    exact h.le
  have hΔ_r_j_le_Δ1 : ∀ j : Fin n_fine, Δ_r j.castSucc ≤ Δ 1 := by
    intro j
    have h4 : Δ' j.castSucc ≤ Δ' 0 := delta_chain_start_property hΔ'_strict j.castSucc
    have h4' : Δ' j.castSucc ≤ 1 := by rw [hΔ'_start] at *; exact h4
    rw [hΔ'_def j.castSucc] at h4'
    exact (div_le_one (hcfg.hΔ_pos 1)).mp h4'
  have h_normal_r : ∀ (j : Fin n_fine), scaleClass_r j = ScaleClass.normal →
      IsSetBetweenScales config.pointSet (Δ_r (Fin.succ j)) (Δ_r j.castSucc) s (C_between_r j) := by
    intro j hj
    have h1 : scaleClass (Fin.succ j) = ScaleClass.normal := by simpa [scaleClass_r] using hj
    exact hcfg.h_normal (Fin.succ j) h1
  have h_good_r : ∀ (j : Fin n_fine) (t_j : ℝ), scaleClass_r j = ScaleClass.good t_j →
      IsRegularBetweenScales config.pointSet (Δ_r (Fin.succ j)) (Δ_r j.castSucc) t_j
        (C_between_r j) (C_between_r j) := by
    intro j t_j hj
    have h1 : scaleClass (Fin.succ j) = ScaleClass.good t_j := by simpa [scaleClass_r] using hj
    exact hcfg.h_good (Fin.succ j) t_j h1
  have h_between := between_scales_transfer_all
      (P := config.pointSet) (Δ₁ := Δ 1) (i₀ := Q.i) (j₀ := Q.j)
      (hcfg.hΔ_pos 1) (hcfg.hΔ_dyadic 1)
      n_fine Δ_r hΔ_r_dyadic hΔ_r_pos hΔ_r_decreasing hΔ_r_j_le_Δ1
      scaleClass_r s C_between_r h_normal_r h_good_r

  have h_between_normal_full : ∀ (j : Fin n_fine), scaleClass' j = ScaleClass.normal →
      IsSetBetweenScales (setFromIndices δbar S_full)
        (Δ' (Fin.succ j)) (Δ' j.castSucc) s (C_between' j) := by
    intro j hj
    have h1 : scaleClass_r j = ScaleClass.normal := by simpa [scaleClass_r, hscaleClass'_def] using hj
    have h2 := h_between.1 j h1
    have h3 : (Δ_r (Fin.succ j) / Δ 1) = Δ' (Fin.succ j) := by rw [hΔ'_def (Fin.succ j)] <;> rfl
    have h4 : (Δ_r j.castSucc / Δ 1) = Δ' j.castSucc := by rw [hΔ'_def j.castSucc] <;> rfl
    have h5 : C_between_r j = C_between' j := by simp [C_between_r, hC_between'_def]
    rw [h3, h4, h5] at h2
    rw [hP_Q_eq] at *; exact h2
  have h_between_good_full : ∀ (j : Fin n_fine) (t_j : ℝ), scaleClass' j = ScaleClass.good t_j →
      IsRegularBetweenScales (setFromIndices δbar S_full)
        (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j (C_between' j) (C_between' j) := by
    intro j t_j hj
    have h1 : scaleClass_r j = ScaleClass.good t_j := by simpa [scaleClass_r, hscaleClass'_def] using hj
    have h2 := h_between.2 j t_j h1
    have h3 : (Δ_r (Fin.succ j) / Δ 1) = Δ' (Fin.succ j) := by rw [hΔ'_def (Fin.succ j)] <;> rfl
    have h4 : (Δ_r j.castSucc / Δ 1) = Δ' j.castSucc := by rw [hΔ'_def j.castSucc] <;> rfl
    have h5 : C_between_r j = C_between' j := by simp [C_between_r, hC_between'_def]
    rw [h3, h4, h5] at h2
    rw [hP_Q_eq] at *; exact h2

  let M_amp : ℝ := K * (24 * Real.log (1 / δbar) / (n_fine : ℝ)) ^ n_fine
  have hM_amp_ge : K * (24 * Real.log (1 / δbar) / (n_fine : ℝ)) ^ n_fine ≤ M_amp := by rfl
  have hM_amp_ge1 : 1 ≤ M_amp := by
    have h_log_eq : Real.log (1 / δbar) = ((k - m : ℝ)) * Real.log 2 := by
      have h_cast : ((k - m : ℕ) : ℝ) = (k : ℝ) - (m : ℝ) := by
        rw [Nat.cast_sub hmk]
      simp [δbar, dyadicDelta, Real.log_div, Real.log_pow, h_cast] <;> ring
    have h_log2_gt : (1 : ℝ) < 24 * Real.log 2 := by
      have h1 : Real.log 4 > 1 := by
        have h2 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_three]
        have h3 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h2
        have h4 : Real.log (Real.exp 1) = 1 := by simp
        rw [h4] at h3; exact h3
      have h5 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] <;> norm_num
      linarith
    have h_nfine_le_24log : (n_fine : ℝ) ≤ 24 * Real.log (1 / δbar) := by
      rw [h_log_eq]
      have h3 : (n_fine : ℝ) ≤ (k - m : ℝ) := by exact_mod_cast h_nfine_le_km
      have h4 : 0 ≤ (k - m : ℝ) := by exact_mod_cast (show 0 ≤ k - m from by omega)
      nlinarith
    have h_nfine_pos' : 0 < (n_fine : ℝ) := by exact_mod_cast hn_fine_pos
    have h3 : 1 ≤ 24 * Real.log (1 / δbar) / (n_fine : ℝ) := by
      calc 1
        = (n_fine : ℝ) / (n_fine : ℝ) := by field_simp [h_nfine_pos'.ne'] <;> ring
      _ ≤ (24 * Real.log (1 / δbar)) / (n_fine : ℝ) := by gcongr
    have h4 : 1 ≤ (24 * Real.log (1 / δbar) / (n_fine : ℝ)) ^ n_fine := by
      have h5 : ∀ (n : ℕ), 1 ≤ (24 * Real.log (1 / δbar) / (n_fine : ℝ)) ^ n := by
        intro n; induction n with
        | zero => norm_num
        | succ n ih => simp [pow_succ] at * <;> nlinarith
      exact h5 n_fine
    have h5 : 1 ≤ K := hK_ge1
    have h6 : 1 ≤ K * (24 * Real.log (1 / δbar) / (n_fine : ℝ)) ^ n_fine := by
      calc 1
        = 1 * 1 := by ring
      _ ≤ K * (24 * Real.log (1 / δbar) / (n_fine : ℝ)) ^ n_fine := by gcongr <;> linarith
    exact h6

  have hδ_le_δbar : dyadicDelta k ≤ δbar := by
    have h : k - m ≤ k := by omega
    exact dyadicDelta_le_iff'''.mpr h
  have h_scale_ratio' : ∀ (j : Fin n_fine), ¬(scaleClass' j).isBad →
      Δ' (Fin.succ j) / Δ' j.castSucc ≤ Real.rpow δbar τ := by
    intro j hnotbad
    have h_ratio_simp : Δ' (Fin.succ j) / Δ' j.castSucc =
        Δ (Fin.succ (Fin.succ j)) / Δ ((Fin.succ j).castSucc) := by
      rw [hΔ'_def (Fin.succ j), hΔ'_def j.castSucc]
      have h_eq1 : Fin.succ (j.castSucc) = (Fin.succ j).castSucc := by
        apply Fin.ext <;> simp
      rw [h_eq1] <;> field_simp [(hcfg.hΔ_pos 1).ne'] <;> ring
    rw [h_ratio_simp]
    have h : ¬(scaleClass (Fin.succ j)).isBad := by
      rw [hscaleClass'_def j] at *; exact hnotbad
    have h2 : Δ (Fin.succ (Fin.succ j)) / Δ (Fin.succ j).castSucc ≤ Real.rpow (dyadicDelta k) τ :=
      hcfg.h_scale_ratio (Fin.succ j) h
    have h5 : Real.rpow (dyadicDelta k) τ ≤ Real.rpow δbar τ :=
      Real.rpow_le_rpow (by linarith [dyadicDelta_pos k]) hδ_le_δbar (by linarith)
    exact le_trans h2 h5

  rcases thin_and_transfer
      (hn_fine_pos := hn_fine_pos)
      (hδbar_pos := hδbar_pos)
      (hδbar_lt_one := hδbar_lt_one)
      (hδbar_eq := by rfl)
      (hΔ'_pos := hΔ'_pos)
      (hΔ'_dyadic := hΔ'_dyadic)
      (hΔ'_strict := hΔ'_strict)
      (hΔ'_end := hΔ'_end)
      (hΔ'_start := hΔ'_start)
      (ha_spec := ha_spec)
      (ha_mono := ha_mono)
      (ha_last_max := ha_last_max)
      (ha_last_eq := h_a_last)
      (h_unif_full := h_unif_full)
      (hS'_sub := hS'_sub)
      (h_unit_full := h_unit_S_full)
      (h_unit_S' := h_unit_S')
      (K := K)
      (hK_pos := hK_pos)
      (hK_ge1 := hK_ge1)
      (h_density := h_density')
      (s := s)
      (t := t)
      (hs_nonneg := hs_nonneg)
      (h_between_normal := h_between_normal_full)
      (h_between_good := h_between_good_full)
      (M_amp := M_amp)
      (hM_amp_ge := hM_amp_ge)
      (hM_amp_ge1 := hM_amp_ge1)
    with ⟨S'', N'', hS''_sub, h_unif_S'', h_bet_norm'', h_bet_good''⟩

  let P₀'' : Finset (DyadicSquare (k - m)) :=
    fineConfig.P₀.filter (fun p => (p.i, p.j) ∈ S'')
  let config'' : CTNiceConfiguration (k - m) s (Real.rpow (dyadicDelta (k - m)) (-lam_tail)) (MQ Q) :=
    { P₀ := P₀''
    , T₀ := fineConfig.T₀
    , tubeFamily := fun p hp => fineConfig.tubeFamily p (Finset.mem_filter.mp hp).1
    , h_subset := fun p hp => fineConfig.h_subset p (Finset.mem_filter.mp hp).1
    , h_size := fun p hp => fineConfig.h_size p (Finset.mem_filter.mp hp).1
    , h_delta_s_set := fun p hp => by
        have h_orig := fineConfig.h_delta_s_set p (Finset.mem_filter.mp hp).1
        exact h_orig
    , h_intersect := fun p hp => fineConfig.h_intersect p (Finset.mem_filter.mp hp).1
    , h_tube_parameters := fineConfig.h_tube_parameters
    , h_bounded := by
        have h_sub : P₀'' ⊆ fineConfig.P₀ := Finset.filter_subset _ _
        have h_set_sub : (⋃ p, Set.iUnion (fun (h : p ∈ (P₀'' : Set (DyadicSquare (k - m)))) => p.toSet)) ⊆
            (⋃ p, Set.iUnion (fun (h : p ∈ (fineConfig.P₀ : Set (DyadicSquare (k - m)))) => p.toSet)) := by
          intro x hx
          rcases Set.mem_iUnion.mp hx with ⟨p, hp⟩
          rcases Set.mem_iUnion.mp hp with ⟨hP, hx2⟩
          exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨h_sub hP, hx2⟩⟩
        exact fineConfig.h_bounded.subset h_set_sub }
  have hT0_eq : config''.T₀ = fineConfig.T₀ := by simp [config'']

  let C_between'' : Fin n_fine → ℝ := fun j =>
    9 * C_between' j * 2 * M_amp * (4 : ℝ)^n_fine

  have hP''_eq : config''.pointSet = setFromIndices δbar S'' := by
    have h1 : config''.pointSet = setFromIndices δbar
        (config''.P₀.image (fun p : DyadicSquare (k - m) => (p.i, p.j))) :=
      config_pointSet_eq_setFromIndices config''
    rw [h1]
    have h2 : config''.P₀.image (fun p : DyadicSquare (k - m) => (p.i, p.j)) = S'' := by
      ext ⟨i, j⟩
      simp only [config'', P₀'', Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨p, ⟨hp1, hp2⟩, hpeq⟩
        have hpeq' : (p.i, p.j) = (i, j) := hpeq
        rw [hpeq'] at hp2
        exact hp2
      · intro h
        have h_in_S' : (i, j) ∈ S' := hS''_sub h
        rcases Finset.mem_image.mp h_in_S' with ⟨p, hp, hpeq⟩
        have h' : (p.i, p.j) ∈ S'' := by
          rw [hpeq]; exact h
        exact ⟨p, ⟨hp, h'⟩, hpeq⟩
    rw [h2]

  have hcfg_fine'' : CombiningConfig s t τ n_fine ε_G η lam_tail ε_N C_P_fine C_between''
      (k - m) (MQ Q) config'' Δ' scaleClass' N'' :=
    { hM_pos := hMQ
      hΔ_strict := hΔ'_strict
      hΔ_end := hΔ'_end
      hΔ_start := hΔ'_start
      hΔ_pos := hΔ'_pos
      hΔ_dyadic := hΔ'_dyadic
      h_scale_ratio := h_scale_ratio'
      h_uniform := rangeUniformity_to_isUniformAtScales h_unif_S''
          (hδ_pos := hδbar_pos) (by rw [h_a_last]) hP''_eq ha_spec ha_mono ha_last_max
      h_normal := fun j hj => by
        have h := h_bet_norm'' j hj
        rw [hP''_eq] at *; exact h
      h_good := fun j t_j hj => by
        have h := h_bet_good'' j t_j hj
        rw [hP''_eq] at *; exact h
      h_C_between_normal := fun j hj => by
        have h := h_absorb_normal j hj
        have h_eq : (9 * (C_between' j : ℝ) * 2 * K *
            (24 * Real.log (1 / dyadicDelta (k - m)) / (n_fine : ℝ)) ^ n_fine * (4 : ℝ)^n_fine) =
            (9 * (C_between' j : ℝ) * 2 * M_amp * (4 : ℝ)^n_fine) := by
          dsimp only [M_amp, δbar] <;> ring
        rw [h_eq] at h
        simpa [δbar] using h
      h_C_between_good := fun j t_j hj => by
        have h := h_absorb_good j t_j hj
        have h_eq : (9 * (C_between' j : ℝ) * 2 * K *
            (24 * Real.log (1 / dyadicDelta (k - m)) / (n_fine : ℝ)) ^ n_fine * (4 : ℝ)^n_fine) =
            (9 * (C_between' j : ℝ) * 2 * M_amp * (4 : ℝ)^n_fine) := by
          dsimp only [M_amp, δbar] <;> ring
        rw [h_eq] at h
        simpa [δbar] using h }

  have hB1_fine'' : B1BridgeHypotheses (k - m) config'' :=
    { h_squares_unit := fun p hp =>
        fineConfig_B1.h_squares_unit p (Finset.mem_filter.mp hp).1
      h_tubes_strip := fineConfig_B1.h_tubes_strip
      h_tubes_bounded := fineConfig_B1.h_tubes_bounded }

  exact ⟨config'', C_between'', N'', hcfg_fine'', hB1_fine'', hT0_eq⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
