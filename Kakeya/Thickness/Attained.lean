/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Basic

/-!
# Thickness is attained

For a compact nonempty set `K` in a finite-dimensional inner product space, the infimum in the
definition of `Metric.thickness` is attained: there is an affine subspace of rank `≤ j` realising
it exactly. The hard part is `_thickness_attained_extract_limit`, which extracts a limit
projection from the approximating sequence of affine-subspace witnesses.

TODO: Break up the proof of `_thickness_attained_extract_limit`
-/

@[expose] public section

open scoped InnerProductSpace

namespace Metric

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for `thickness_attained`: from the approximating sequence
`hwit` of affine-subspace witnesses, extract a basepoint `q : E` and an
operator `P : E →L[ℝ] E` with rank `≤ j` such that for every `x ∈ K`,
`‖x - q - P (x - q)‖ ≤ t`.

Conceptually `P` is the orthogonal projection onto a limit subspace
`W := range P`, obtained by extracting a convergent subsequence of the
orthogonal projections `P_k` onto `(A_k).direction`. The basepoint `q` is
the limit of closest points `q_k ∈ A_k` to the origin.

The genuinely-hard part of the proof of `thickness_attained` is concentrated
here: extracting a convergent subsequence in the operator-norm topology on
`E →L[ℝ] E`, showing the limit is a self-adjoint idempotent (closed
conditions), passing the rank bound to the limit (upper-semicontinuity of
rank for projections via Gram-determinant continuity), and passing the
covering inequality to the limit by continuity of operator application
and norm. -/
private lemma _thickness_attained_extract_limit
    {K : Set E} (hK_bdd : Bornology.IsBounded K) (hK_ne : K.Nonempty)
    (j : ℕ) {t : ℝ} (ht_nn : 0 ≤ t)
    (hwit : ∀ k : ℕ, ∃ A : AffineSubspace ℝ E,
        Module.finrank ℝ A.direction ≤ j ∧
        K ⊆ cthickening (t + 1 / (k + 1 : ℝ)) A) :
    ∃ (q : E) (P : E →L[ℝ] E),
      Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤ j ∧
      ∀ x ∈ K, ‖x - q - P (x - q)‖ ≤ t := by
  classical
  choose A hA_rank hA_cover using hwit
  have hA_closed : ∀ k, IsClosed (A k : Set E) := by
    intro k
    have : FiniteDimensional ℝ (A k).direction :=
      FiniteDimensional.finiteDimensional_submodule _
    exact AffineSubspace.closed_of_finiteDimensional _
  have hA_ne : ∀ k, (A k : Set E).Nonempty := by
    intro k
    obtain ⟨x₀, hx₀⟩ := hK_ne
    have hx₀_mem : x₀ ∈ cthickening (t + 1 / (k + 1 : ℝ)) (A k) := hA_cover k hx₀
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [show ((A k : Set E)) = (∅ : Set E) from hempty,
        cthickening_empty] at hx₀_mem
    exact (Set.notMem_empty _) hx₀_mem
  have hq_choose : ∀ k, ∃ q ∈ (A k : Set E), infDist 0 (A k : Set E) = dist 0 q :=
    fun k => (hA_closed k).exists_infDist_eq_dist (hA_ne k) 0
  choose q hq_mem hq_dist using hq_choose
  have hW_hop : ∀ k, ((A k).direction).HasOrthogonalProjection := by
    intro k
    haveI : FiniteDimensional ℝ ((A k).direction) :=
      FiniteDimensional.finiteDimensional_submodule _
    haveI : CompleteSpace ((A k).direction) := FiniteDimensional.complete ℝ _
    infer_instance
  let P : ℕ → (E →L[ℝ] E) := fun k => ((A k).direction).starProjection
  obtain ⟨x₀, hx₀_mem⟩ := hK_ne
  obtain ⟨R, hKR⟩ := hK_bdd.subset_closedBall (0 : E)
  have hbnd_q : ∀ k, ‖q k‖ ≤ R + t + 1 := by
    intro k
    have hk_bound : (1 : ℝ) / (k + 1 : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (k + 1 : ℝ) := by
        have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
        linarith
      exact this
    have hx₀_cover : x₀ ∈ cthickening (t + 1 / (k + 1 : ℝ)) (A k) := hA_cover k hx₀_mem
    have htk_nn : 0 ≤ t + 1 / (k + 1 : ℝ) := by
      have : (0 : ℝ) ≤ 1 / (k + 1 : ℝ) := by positivity
      linarith
    rw [(hA_closed k).cthickening_eq_biUnion_closedBall htk_nn] at hx₀_cover
    simp only [Set.mem_iUnion, mem_closedBall] at hx₀_cover
    obtain ⟨a, ha_mem, hax₀⟩ := hx₀_cover
    have ha_le : dist x₀ a ≤ t + 1 := by
      calc dist x₀ a ≤ t + 1 / (k + 1 : ℝ) := hax₀
        _ ≤ t + 1 := by linarith
    have hq_le : dist 0 (q k) ≤ dist 0 a := by
      rw [← hq_dist k]
      exact infDist_le_dist_of_mem ha_mem
    have hx₀_norm : ‖x₀‖ ≤ R := by
      have hxR := hKR hx₀_mem
      rw [mem_closedBall, dist_zero_right] at hxR
      exact hxR
    have ha_norm : ‖a‖ ≤ R + t + 1 := by
      have step1 : ‖a‖ ≤ ‖x₀‖ + ‖x₀ - a‖ := by
        have : ‖a‖ = ‖x₀ - (x₀ - a)‖ := by congr 1; abel
        rw [this]
        exact norm_sub_le _ _
      have step2 : ‖x₀ - a‖ = dist x₀ a := (dist_eq_norm _ _).symm
      linarith [step1, step2.symm ▸ ha_le, hx₀_norm]
    have hq_norm : ‖q k‖ ≤ ‖a‖ := by
      have h1 : ‖q k‖ = dist 0 (q k) := by rw [dist_zero_left]
      have h2 : ‖a‖ = dist 0 a := by rw [dist_zero_left]
      rw [h1, h2]; exact hq_le
    linarith
  have hbnd_P : ∀ k, ‖P k‖ ≤ 1 := fun k => Submodule.starProjection_norm_le _
  let qP : ℕ → E × (E →L[ℝ] E) := fun k => (q k, P k)
  haveI : FiniteDimensional ℝ (E →L[ℝ] E) := ContinuousLinearMap.finiteDimensional
  haveI : ProperSpace (E →L[ℝ] E) := FiniteDimensional.proper ℝ (E →L[ℝ] E)
  haveI : ProperSpace (E × (E →L[ℝ] E)) := FiniteDimensional.proper ℝ (E × (E →L[ℝ] E))
  set S : Set (E × (E →L[ℝ] E)) :=
    closedBall (0 : E) (R + t + 1) ×ˢ closedBall (0 : E →L[ℝ] E) 1 with hS_def
  have hS_compact : IsCompact S :=
    (ProperSpace.isCompact_closedBall (0 : E) (R + t + 1)).prod
      (ProperSpace.isCompact_closedBall (0 : E →L[ℝ] E) 1)
  have hqP_in_S : ∀ k, qP k ∈ S := by
    intro k
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      exact hbnd_q k
    · rw [mem_closedBall, dist_zero_right]
      exact hbnd_P k
  obtain ⟨lim, _hlim_in, φ, hφ_mono, hφ_tendsto⟩ :=
    hS_compact.tendsto_subseq hqP_in_S
  set q_lim : E := lim.1
  set P_lim : E →L[ℝ] E := lim.2
  have hq_tendsto : Filter.Tendsto (fun i => q (φ i)) Filter.atTop (nhds q_lim) :=
    hφ_tendsto.fst_nhds
  have hP_tendsto : Filter.Tendsto (fun i => P (φ i)) Filter.atTop (nhds P_lim) :=
    hφ_tendsto.snd_nhds
  have h_rank_P : ∀ k, Module.finrank ℝ (LinearMap.range (P k).toLinearMap) ≤ j := by
    intro k
    have h_range_eq : LinearMap.range (P k).toLinearMap = (A k).direction := by
      ext v
      simp only [LinearMap.mem_range]
      constructor
      · rintro ⟨w, rfl⟩
        exact Submodule.starProjection_apply_mem _ _
      · intro hv
        refine ⟨v, ?_⟩
        change ((A k).direction).starProjection v = v
        rw [Submodule.starProjection_eq_self_iff]
        exact hv
    rw [h_range_eq]
    exact hA_rank k
  have h_rank_lim : Module.finrank ℝ (LinearMap.range P_lim.toLinearMap) ≤ j := by
    by_contra h_lt
    have h_le : (j + 1 : ℕ) ≤ Module.finrank ℝ (LinearMap.range P_lim.toLinearMap) :=
      Nat.lt_iff_add_one_le.mp (Nat.lt_of_not_le h_lt)
    haveI : FiniteDimensional ℝ (LinearMap.range P_lim.toLinearMap) :=
      FiniteDimensional.finiteDimensional_submodule _
    have h_rank_eq : ((Module.finrank ℝ (LinearMap.range P_lim.toLinearMap) : ℕ) : Cardinal)
        = Module.rank ℝ (LinearMap.range P_lim.toLinearMap) :=
      Module.finrank_eq_rank ℝ _
    have h_card_le : ((j + 1 : ℕ) : Cardinal) ≤ P_lim.toLinearMap.rank := by
      change ((j + 1 : ℕ) : Cardinal) ≤ Module.rank ℝ (LinearMap.range P_lim.toLinearMap)
      rw [← h_rank_eq]
      exact_mod_cast h_le
    rw [LinearMap.le_rank_iff_exists_linearIndependent_finset] at h_card_le
    obtain ⟨s, hs_card, hs_indep⟩ := h_card_le
    have hcontF : Continuous (fun (Q : E →L[ℝ] E) => fun (x : s) => Q x.val) := by
      refine continuous_pi (fun x => ?_)
      exact (ContinuousLinearMap.apply ℝ E x.val).continuous
    have h_target_indep :
        LinearIndependent ℝ (fun (x : s) => P_lim x.val) := by
      have h_eq : (fun x : s => P_lim x.val) = (fun (x : s) => P_lim x) := by rfl
      rw [h_eq]; exact hs_indep
    have h_isOpen :
        IsOpen { f : s → E | LinearIndependent ℝ f } :=
      isOpen_setOf_linearIndependent
    have h_evtl : ∀ᶠ i in Filter.atTop,
        LinearIndependent ℝ (fun (x : s) => P (φ i) x.val) := by
      have hPlim_indep : (fun (x : s) => P_lim x.val) ∈
          { f : s → E | LinearIndependent ℝ f } := h_target_indep
      have h_seq_tendsto :
          Filter.Tendsto (fun i (x : s) => P (φ i) x.val)
              Filter.atTop (nhds (fun x : s => P_lim x.val)) := by
        exact (hcontF.tendsto _).comp hP_tendsto
      exact h_seq_tendsto.eventually (h_isOpen.mem_nhds hPlim_indep)
    obtain ⟨i, hi_indep⟩ := h_evtl.exists
    have h_sub_le :
        ∀ x : s, P (φ i) x.val ∈ LinearMap.range (P (φ i)).toLinearMap := by
      intro x
      exact ⟨x.val, rfl⟩
    have h_indep_finrank :
        s.card ≤ Module.finrank ℝ (LinearMap.range (P (φ i)).toLinearMap) := by
      let W : Submodule ℝ E := LinearMap.range (P (φ i)).toLinearMap
      let v : s → W := fun x => ⟨P (φ i) x.val, h_sub_le x⟩
      have hsub_eq : (W.subtype : W →ₗ[ℝ] E) ∘ v = (fun x : s => P (φ i) x.val) := by
        funext x; simp [v]
      have hi_indep_lifted : LinearIndependent ℝ ((W.subtype : W →ₗ[ℝ] E) ∘ v) := by
        rw [hsub_eq]; exact hi_indep
      have hv_indep : LinearIndependent ℝ v :=
        LinearIndependent.of_comp (W.subtype : W →ₗ[ℝ] E) hi_indep_lifted
      have := hv_indep.fintype_card_le_finrank (R := ℝ)
      simpa [W] using this
    have := h_rank_P (φ i)
    omega
  refine ⟨q_lim, P_lim, h_rank_lim, ?_⟩
  intro x hxK
  have h_seq_le : ∀ i, ‖x - q (φ i) - P (φ i) (x - q (φ i))‖ ≤
                  t + 1 / (φ i + 1 : ℝ) := by
    intro i
    set k := φ i
    have h_eq : infDist x (A k : Set E) = ‖x - q k - P k (x - q k)‖ := by
      apply le_antisymm
      · have ha_mem : q k + P k (x - q k) ∈ (A k : Set E) := by
          have h_qk_mem : q k ∈ A k := hq_mem k
          have h_proj_mem : P k (x - q k) ∈ (A k).direction :=
            Submodule.starProjection_apply_mem _ _
          have h_vadd : P k (x - q k) +ᵥ q k ∈ A k :=
            AffineSubspace.vadd_mem_of_mem_direction h_proj_mem h_qk_mem
          have heq : (P k (x - q k) +ᵥ q k : E) = q k + P k (x - q k) := by
            simp [add_comm]
          exact heq ▸ h_vadd
        have h_d : dist x (q k + P k (x - q k)) = ‖x - q k - P k (x - q k)‖ := by
          rw [dist_eq_norm]; congr 1; abel
        calc infDist x (A k : Set E)
            ≤ dist x (q k + P k (x - q k)) := infDist_le_dist_of_mem ha_mem
          _ = ‖x - q k - P k (x - q k)‖ := h_d
      · haveI hAk_ne_inst : Nonempty (A k : Set E) := (hA_ne k).to_subtype
        rw [infDist_eq_iInf]
        apply le_ciInf
        rintro ⟨y, hyA⟩
        rw [dist_eq_norm]
        have h_yqk : y - q k ∈ (A k).direction :=
          AffineSubspace.vsub_mem_direction hyA (hq_mem k)
        have h_orth : x - q k - P k (x - q k) ∈ ((A k).direction)ᗮ :=
          Submodule.sub_starProjection_mem_orthogonal _
        have h_decomp : x - y = (x - q k - P k (x - q k)) + (P k (x - q k) - (y - q k)) := by
          abel
        have h_in_W : P k (x - q k) - (y - q k) ∈ (A k).direction := by
          refine Submodule.sub_mem _ ?_ h_yqk
          exact Submodule.starProjection_apply_mem _ _
        have h_inner : ⟪x - q k - P k (x - q k), P k (x - q k) - (y - q k)⟫_ℝ = 0 := by
          have hh := h_orth (P k (x - q k) - (y - q k)) h_in_W
          rw [real_inner_comm]
          simpa using hh
        have h_pyth : ‖x - y‖^2 = ‖x - q k - P k (x - q k)‖^2 +
                                  ‖P k (x - q k) - (y - q k)‖^2 := by
          rw [h_decomp, @norm_add_sq_real]
          rw [h_inner]; ring
        nlinarith [sq_nonneg ‖P k (x - q k) - (y - q k)‖,
                   sq_nonneg ‖x - q k - P k (x - q k)‖,
                   norm_nonneg (x - q k - P k (x - q k)),
                   norm_nonneg (x - y)]
    have h_inf_le : infDist x (A k : Set E) ≤ t + 1 / (k + 1 : ℝ) := by
      have hxk_cover := hA_cover k hxK
      have htk_nn : 0 ≤ t + 1 / (k + 1 : ℝ) := by
        have : (0 : ℝ) ≤ 1 / (k + 1 : ℝ) := by positivity
        linarith
      rw [mem_cthickening_iff] at hxk_cover
      have h_ne_top : infEDist x (A k : Set E) ≠ ⊤ :=
        infEDist_ne_top (hA_ne k)
      have h_eq_ofReal : infEDist x (A k : Set E)
          = ENNReal.ofReal (infDist x (A k : Set E)) := by
        rw [infDist, ENNReal.ofReal_toReal h_ne_top]
      rw [h_eq_ofReal] at hxk_cover
      exact (ENNReal.ofReal_le_ofReal_iff htk_nn).mp hxk_cover
    rw [← h_eq]; exact h_inf_le
  have h_cont : Continuous (fun (qP' : E × (E →L[ℝ] E)) =>
        ‖x - qP'.1 - qP'.2 (x - qP'.1)‖) := by
    refine continuous_norm.comp ?_
    refine Continuous.sub ?_ ?_
    · refine Continuous.sub continuous_const continuous_fst
    · have h1 : Continuous (fun qP' : E × (E →L[ℝ] E) => x - qP'.1) :=
        continuous_const.sub continuous_fst
      have h2 : Continuous (fun qP' : E × (E →L[ℝ] E) => qP'.2) := continuous_snd
      have h_ev : Continuous (fun (pv : (E →L[ℝ] E) × E) => pv.1 pv.2) :=
        isBoundedBilinearMap_apply.continuous
      exact h_ev.comp (h2.prodMk h1)
  have h_seq_to_lim :
      Filter.Tendsto (fun i => ‖x - q (φ i) - P (φ i) (x - q (φ i))‖)
          Filter.atTop (nhds ‖x - q_lim - P_lim (x - q_lim)‖) := by
    have h_pair : Filter.Tendsto (fun i => qP (φ i)) Filter.atTop (nhds (q_lim, P_lim)) := by
      change Filter.Tendsto (fun i => qP (φ i)) Filter.atTop (nhds lim)
      exact hφ_tendsto
    have := (h_cont.tendsto _).comp h_pair
    convert this
    exact Eq.symm (Real.ext_cauchy rfl)
  have h_seq_tendsto_t : Filter.Tendsto (fun i => t + 1 / (φ i + 1 : ℝ))
      Filter.atTop (nhds t) := by
    have h_phi_inf : Filter.Tendsto (fun i => (φ i : ℝ) + 1) Filter.atTop Filter.atTop := by
      have h_phi_inf' : Filter.Tendsto (fun i => φ i) Filter.atTop Filter.atTop :=
        hφ_mono.tendsto_atTop
      have hcast : Filter.Tendsto (fun i => (φ i : ℝ)) Filter.atTop Filter.atTop := by
        exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp h_phi_inf'
      exact hcast.atTop_add tendsto_const_nhds
    have h_inv : Filter.Tendsto (fun i => 1 / (φ i + 1 : ℝ)) Filter.atTop (nhds 0) := by
      have h := h_phi_inf.inv_tendsto_atTop
      refine h.congr (fun i => ?_)
      simp [Pi.inv_apply, one_div]
    have h_t_const : Filter.Tendsto (fun _ : ℕ => t) Filter.atTop (nhds t) :=
      tendsto_const_nhds
    have h_sum := h_t_const.add h_inv
    simpa using h_sum
  exact le_of_tendsto_of_tendsto h_seq_to_lim h_seq_tendsto_t
    (Filter.Eventually.of_forall h_seq_le)

omit [FiniteDimensional ℝ E] in
/-- A variant of `exists_cthickening_of_ethickness_lt`. -/
theorem exists_cthickening_thickness_add {K : Set E} (hK_bdd : Bornology.IsBounded K)
  (j : ℕ) (k : ℕ) : ∃ A : AffineSubspace ℝ E,
      Module.finrank ℝ A.direction ≤ j ∧
        K ⊆ cthickening (thickness ℝ K j + 1 / (k + 1 : ℝ)) A := by
  set t := thickness ℝ K j
  have ht_nn : 0 ≤ t := thickness_nonneg _ _
  have hε_pos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
  have hlt : ethickness ℝ K j < ((t + 1 / (k + 1 : ℝ)).toNNReal : ENNReal) := by
    have he : ethickness ℝ K j = ENNReal.ofReal (thickness ℝ K j) :=
      congrFun (ethickness_thickness (𝕜 := ℝ) hK_bdd) j
    rw [he, show ((t + 1 / (k + 1 : ℝ)).toNNReal : ENNReal)
        = ENNReal.ofReal (t + 1 / (k + 1 : ℝ)) from rfl]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht_nn).mpr (by linarith)
  obtain ⟨A, hA_rank, hA_sub⟩ := exists_cthickening_of_ethickness_lt hlt
  refine ⟨A, Module.finrank_le_of_rank_le hA_rank, ?_⟩
  rwa [Real.coe_toNNReal _ (by positivity)] at hA_sub

/-- For compact nonempty K, the infimum in the definition of thickness is attained:
    there exists an affine subspace A of finrank ≤ j with
    K ⊆ cthickening(thickness K j, A). -/
theorem exists_subset_cthickening_thickness
    {K : Set E} (hK_bdd : Bornology.IsBounded K) (j : ℕ) :
    ∃ A : AffineSubspace ℝ E,
      Module.finrank ℝ A.direction ≤ j ∧
        K ⊆ cthickening (thickness ℝ K j) A := by
  by_cases hKe : K = ∅
  · rw [hKe]
    use ⊥
    constructor
    · rw [AffineSubspace.direction_bot]
      rw [finrank_bot]
      apply zero_le
    · apply Set.empty_subset
  push Not at hKe
  by_cases hj : Module.finrank ℝ E ≤ j
  · refine ⟨⊤, ?_, ?_⟩
    · rw [AffineSubspace.direction_top]
      rw [finrank_top]
      exact hj
    · have hrank : (Module.rank ℝ E) ≤ (j : Cardinal) := by
        rw [← Module.finrank_eq_rank]
        exact_mod_cast hj
      have ht_zero : thickness ℝ K j = 0 :=
        thickness_eq_zero_of_finrank_le (𝕜 := ℝ) (V := E) hrank
      rw [ht_zero]
      intro x _
      have h_top_coe : (⊤ : AffineSubspace ℝ E) = (Set.univ : Set E) := by
        rw [AffineSubspace.top_coe]
      rw [h_top_coe]
      simp
  rw [not_le] at hj
  set t : ℝ := thickness ℝ K j with ht_def
  have ht_nn : 0 ≤ t := thickness_nonneg _ _
  have hwit : ∀ k : ℕ, ∃ A : AffineSubspace ℝ E,
      Module.finrank ℝ A.direction ≤ j ∧
      K ⊆ cthickening (t + 1 / (k + 1 : ℝ)) A := by
    intro k
    apply exists_cthickening_thickness_add hK_bdd
  obtain ⟨q, P, hP_rank, hP_cover⟩ :=
    _thickness_attained_extract_limit hK_bdd hKe j ht_nn hwit
  let W : Submodule ℝ E := LinearMap.range P.toLinearMap
  refine ⟨AffineSubspace.mk' q W, ?_, ?_⟩
  · rw [AffineSubspace.direction_mk']
    exact hP_rank
  · intro x hxK
    set a : E := P (x - q) +ᵥ q with ha_def
    have ha_mem : a ∈ AffineSubspace.mk' q W := by
      rw [AffineSubspace.mem_mk']
      have hvsub : a -ᵥ q = P (x - q) := by
        simp [ha_def]
      rw [hvsub]
      exact LinearMap.mem_range_self P.toLinearMap (x - q)
    have hdist_eq : dist x a = ‖x - q - P (x - q)‖ := by
      rw [dist_eq_norm, ha_def]
      change ‖x - (P (x - q) + q)‖ = ‖x - q - P (x - q)‖
      congr 1
      abel
    have hdist_le : dist x a ≤ t := by
      rw [hdist_eq]
      exact hP_cover x hxK
    exact mem_cthickening_of_dist_le x a t _ ha_mem hdist_le

/-- **Attained thickness in a fixed dimension** (blueprint
`lem:exists_subset_cthickening_thickness_finrank_eq`).

Strengthening of `exists_subset_cthickening_thickness`: when `j ≤ finrank ℝ E`, the attained affine
subspace can be taken nonempty and of dimension *exactly* `j`, obtained by enlarging the
dimension-`≤ j` witness inside `E` while preserving the containment. This is the form the projection
step needs, since the shadow lives in a genuinely `j`-dimensional Euclidean subspace. -/
theorem exists_subset_cthickening_thickness_finrank_eq
    {K : Set E} (hK_bdd : Bornology.IsBounded K) (hK_ne : K.Nonempty)
    {j : ℕ} (hj : j ≤ Module.finrank ℝ E) :
    ∃ A : AffineSubspace ℝ E,
      (A : Set E).Nonempty ∧ Module.finrank ℝ A.direction = j ∧
        K ⊆ cthickening (thickness ℝ K j) A := by
  obtain ⟨A₀, hA₀_rank, hA₀_cover⟩ := exists_subset_cthickening_thickness hK_bdd j
  have hA₀_ne : (A₀ : Set E).Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hK_ne
    have hx₀_mem : x₀ ∈ cthickening (thickness ℝ K j) A₀ := hA₀_cover hx₀
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [show ((A₀ : Set E)) = (∅ : Set E) from hempty, cthickening_empty] at hx₀_mem
    exact (Set.notMem_empty _) hx₀_mem
  obtain ⟨p, hp_mem⟩ := hA₀_ne
  obtain ⟨W, hW₀_le_W, hW_finrank⟩ :=
    FiniteDimensional.exists_le_finrank_eq_of_le_finrank (N := A₀.direction) hA₀_rank hj
  let A : AffineSubspace ℝ E := AffineSubspace.mk' p W
  refine ⟨A, ?_, ?_, ?_⟩
  · exact ⟨p, AffineSubspace.self_mem_mk' p W⟩
  · rw [AffineSubspace.direction_mk']
    exact hW_finrank
  · intro x hxK
    have hA₀_sub_A : (A₀ : Set E) ⊆ (A : Set E) := by
      intro y hy
      change y ∈ AffineSubspace.mk' p W
      rw [AffineSubspace.mem_mk']
      have hy_mem : y -ᵥ p ∈ A₀.direction := by
        have hy_mk : y ∈ AffineSubspace.mk' p A₀.direction := by
          rwa [AffineSubspace.mk'_eq hp_mem]
        rwa [AffineSubspace.mem_mk'] at hy_mk
      exact hW₀_le_W hy_mem
    exact Metric.cthickening_subset_of_subset (thickness ℝ K j) hA₀_sub_A (hA₀_cover hxK)

end Metric
