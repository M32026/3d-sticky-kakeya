/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform.ParentBodyDensity.Telescope
public import Kakeya.Tube.Chains
public import Kakeya.Uniform
public import Kakeya.KatzTao

/-!
# Parent-level density bound for a chain of node families

The Kakeya argument needs to bound the leaf-level `maxDensity` of a family of `δ`-tubes by a
product of per-scale Katz–Tao constants.  This file carries out that reduction for an abstract
chain of node families `κ : Fin (M+1) → Type u`, tube-valued at every scale by
`tb k : κ k → Tube (ρ k) E` and linked by a functional projection
`proj m : κ m.succ → κ m.castSucc`.

Three steps, from the bottom up:

* `card_filter_chain_le_aux` runs the iterated argmax pigeonhole (GWZ Lemma 7.4) along
  the chain: it pins one ancestor per scale and bounds the number of leaves under a convex body
  `K` by `C_cover · ∏ B_m / c^M`.
* `card_le_prod_density_volume_div_parent_level` packages the constants of that telescope
  into a single `C ^ M`.
* `maxDensity_le_prod_of_uniform_at_scales` feeds a Frostman-full uniform construction into
  the engine and converts the leaf count into a density bound.

The material was split out of `Kakeya/Uniform.lean`, whose refine-to-uniform pigeonholing is
independent of it.  Its consumers are GWZ Lemma 7.5
(`Kakeya.StickyKakeya.subStickyFrostmanLemma`) and the chain-fibre bound of Lemma 7.7
(`Kakeya.MultiScaleFac.ChainFibre`).
-/

@[expose] public section

namespace Tube.ParentBodyDensity

open MeasureTheory Real Metric ConvexSpaceBody Kakeya

universe u

open scoped Classical in
/-- Auxiliary iterated-pigeonhole bound used inside the proof of
`card_le_prod_density_volume_div_parent_level`; the argmax chain `par` is existential in the
conclusion.  Given a parent chain with a functional chain projection, a parent-level Katz–Tao input
on the fibre of `proj` and a nonempty `F_K`, it packages the iterated GWZ Lemma 7.4 telescope at
parent level via an argmax chain `par_0, …, par_{M-1}` built over chain-projection fibres. -/
private theorem card_filter_chain_le_aux
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (R : ℝ) (_hR_pos : 0 < R)
    (c : ℝ) (hc_pos : 0 < c)
    (C_cover : ℝ) (hC_cover_pos : 0 < C_cover)
    (hc_le_cV : c ≤ (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))
    {δ : NNReal} (_hδ_pos : 0 < δ)
    (M : ℕ) (hM_pos : 0 < M) (ρ : Fin (M + 1) → NNReal)
    (_hρ_0 : 1 ≤ ρ 0) (_hρ_M : ρ (Fin.last M) = δ) (_hρ_anti : Antitone ρ)
    (hρ_pos : ∀ k : Fin (M + 1), 0 < ρ k)
    {κ : Fin (M + 1) → Type u} (tb : ∀ k : Fin (M + 1), κ k → Tube (ρ k) E)
    (P : ∀ k : Fin (M + 1), Finset (κ k))
    (proj : ∀ m : Fin M, κ m.succ → κ m.castSucc)
    (hproj_mem : ∀ m : Fin M, ∀ w ∈ P m.succ, proj m w ∈ P m.castSucc)
    (hproj_le : ∀ m : Fin M, ∀ w ∈ P m.succ,
        (tb m.succ w).toConvexSpaceBody ≤ (tb m.castSucc (proj m w)).toConvexSpaceBody)
    (hP0_count : ((P 0).card : ℝ) ≤ C_cover)
    (P_in_ball : ∀ k : Fin (M + 1), ∀ t ∈ P k,
        (tb k t).carrier ⊆ Metric.closedBall (0 : E) (R + 3))
    (Δ : Fin M → ENNReal) (hΔ_top : ∀ m : Fin M, Δ m ≠ ⊤)
    (h_local : ∀ m : Fin M, ∀ p ∈ P m.castSucc,
        IsKatzTao ((P m.succ).filter (fun w => proj m w = p))
          (fun w => (tb m.succ w).toConvexSpaceBody) (Δ m))
    (K : ConvexSpaceBody E)
    (w0 : κ (Fin.last M)) (hw0_in_P : w0 ∈ P (Fin.last M))
    (_hw0_le_K : (tb (Fin.last M) w0).toConvexSpaceBody ≤ K) :
    let F_K : Finset (κ (Fin.last M)) :=
      (P (Fin.last M)).filter (fun w => (tb (Fin.last M) w).toConvexSpaceBody ≤ K)
    ∃ par : ∀ m : Fin M, κ m.castSucc,
      (∀ m, par m ∈ P m.castSucc) ∧
      (∀ m, (tb m.castSucc (par m)).carrier ⊆ Metric.closedBall (0 : E) (R + 3)) ∧
      (F_K.card : ℝ) ≤ C_cover *
        (∏ m : Fin M, (Δ m).toReal * volume.real
          ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).carrier
            ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc (par m)).carrier)
          / (((ρ m.succ : NNReal) : ℝ) ^ (Module.finrank ℝ E - 1)))
        / c ^ M := by
  classical
  intro F_K
  set n := Module.finrank ℝ E with hn_def
  set ρr : Fin (M + 1) → ℝ := fun k => ((ρ k : NNReal) : ℝ) with hρr_def
  have hρr_pos : ∀ k : Fin (M + 1), (0 : ℝ) < ρr k := fun k => by exact_mod_cast hρ_pos k
  set cV : ℝ := (Tube.le_volume.c n : ℝ) with hcV_def
  have hcV_pos : 0 < cV := by
    rw [hcV_def]; exact_mod_cast Tube.le_volume.c_pos n
  have hcV : ∀ {δ' : NNReal}, 0 < δ' → ∀ T : Tube δ' E,
      cV * (δ' : ℝ) ^ (n - 1) ≤ volume.real T.carrier := by
    intro δ' _ T'
    have hreal :=
      ENNReal.toReal_mono T'.isCompact.measure_lt_top.ne (Tube.le_volume (δ := δ') T')
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hreal
    exact hreal
  have hc_LB : ∀ {δ' : NNReal}, 0 < δ' → ∀ T : Tube δ' E,
      c * (δ' : ℝ) ^ (n - 1) ≤ volume.real T.carrier := by
    intro δ' hδ' T'
    have hρpow_nn : (0 : ℝ) ≤ (δ' : ℝ) ^ (n - 1) :=
      pow_nonneg (by exact_mod_cast hδ'.le) _
    exact (mul_le_mul_of_nonneg_right hc_le_cV hρpow_nn).trans (hcV hδ' T')
  rcases Nat.eq_zero_or_pos M with hM0 | _hM_pos'
  · exact absurd hM_pos (by simp [hM0])
  · have hρ_succ_pos : ∀ m : Fin M, 0 < ρ m.succ := fun m => hρ_pos m.succ
    have hρ_castSucc_pos : ∀ m : Fin M, 0 < ρ m.castSucc := fun m => hρ_pos m.castSucc
    set par_seed : ∀ m : Fin M, κ m.castSucc :=
      fun m => Tube.chainFun proj m.castSucc w0 with hpar_seed_def
    have hpar_seed_mem : ∀ m : Fin M, par_seed m ∈ P m.castSucc := fun m =>
      Tube.chainFun_mem proj (fun k => (P k : Set (κ k))) hproj_mem m.castSucc w0 hw0_in_P
    have hpar_seed_ball : ∀ m : Fin M,
        (tb m.castSucc (par_seed m)).carrier ⊆ Metric.closedBall (0 : E) (R + 3) := fun m =>
      P_in_ball m.castSucc (par_seed m) (hpar_seed_mem m)
    let B : ∀ m : Fin M, κ m.castSucc → ℝ := fun m pm =>
      (Δ m).toReal * volume.real
        ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).carrier
          ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc pm).carrier)
        / (ρr m.succ ^ (n - 1))
    have hB_nn_any : ∀ m : Fin M, ∀ pm : κ m.castSucc, 0 ≤ B m pm := by
      intro m pm
      apply div_nonneg
      · exact mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg
      · exact pow_nonneg (le_of_lt (hρr_pos _)) _
    have hchainFun_last : ∀ (w : κ (Fin.last M)), Tube.chainFun proj (Fin.last M) w = w :=
      Tube.chainFun_last proj
    have hFK_memP : ∀ w ∈ F_K, w ∈ P (Fin.last M) := fun w hw =>
      (Finset.mem_filter.mp hw).1
    have hFK_le_K : ∀ w ∈ F_K, (tb (Fin.last M) w).toConvexSpaceBody ≤ K := fun w hw =>
      (Finset.mem_filter.mp hw).2
    let Anc : ∀ k : Fin (M + 1), κ (Fin.last M) → κ k := fun k w => Tube.chainFun proj k w
    have hAnc_mem : ∀ (k : Fin (M + 1)), ∀ w ∈ F_K, Anc k w ∈ P k := fun k w hw => by
      apply Tube.chainFun_mem proj (fun k => (P k : Set (κ k))) hproj_mem k w
      exact hFK_memP w hw
    have hAnc_last : ∀ w ∈ F_K, Anc (Fin.last M) w = w := fun w hw => by
      simp [Anc, Tube.chainFun_last]
    have hAnc_castSucc : ∀ (m : Fin M), ∀ w : κ (Fin.last M),
        Anc m.castSucc w = proj m (Anc m.succ w) := fun m w => by
      simp [Anc, Tube.chainFun_castSucc]
    have hAnc_step : ∀ (m : Fin M), ∀ w ∈ F_K,
        (tb m.succ (Anc m.succ w)).toConvexSpaceBody
        ≤ (tb m.castSucc (Anc m.castSucc w)).toConvexSpaceBody :=
      fun m w hw => by
      rw [hAnc_castSucc m w]
      exact hproj_le m (Anc m.succ w) (hAnc_mem m.succ w hw)
    have hAnc_ge : ∀ (k : Fin (M + 1)), ∀ w ∈ F_K,
        (tb (Fin.last M) w).toConvexSpaceBody
        ≤ (tb k (Anc k w)).toConvexSpaceBody := fun k w hw => by
      have hwP : w ∈ P (Fin.last M) := hFK_memP w hw
      apply Tube.chainFun_le proj (fun k => (P k : Set (κ k))) hproj_mem
        (fun k n => (tb k n).toConvexSpaceBody) ?_ k w hwP
      intro m n hn
      exact hproj_le m n hn
    have branch_bound : ∀ (m : Fin M) (G : Finset (κ (Fin.last M)))
        (q : κ m.castSucc), G ⊆ F_K →
        (∀ w ∈ G, Anc m.castSucc w = q) →
        ((G.image (Anc m.succ)).card : ℝ) ≤ B m q / c := by
      intro m G q hG_sub hG_pin
      set S : Finset (κ m.succ) := G.image (Anc m.succ) with hS_def
      have hS_mem : ∀ t ∈ S, ∃ w ∈ G, Anc m.succ w = t := by
        intro t ht; rw [hS_def, Finset.mem_image] at ht; exact ht
      have hS_inP : ∀ t ∈ S, t ∈ P m.succ := by
        intro t ht; obtain ⟨w, hwG, hwt⟩ := hS_mem t ht
        rw [← hwt]; exact hAnc_mem m.succ w (hG_sub hwG)
      have hS_le_q : ∀ t ∈ S, (tb m.succ t).toConvexSpaceBody
            ≤ (tb m.castSucc q).toConvexSpaceBody := by
        intro t ht; obtain ⟨w, hwG, hwt⟩ := hS_mem t ht
        rw [← hwt, ← hG_pin w hwG]; exact hAnc_step m w (hG_sub hwG)
      have hS_body_K : ∀ t ∈ S,
          (tb m.succ t).toConvexSpaceBody ≤ K.cthickening (4 * (ρ m.succ : ℝ)) := by
        intro t ht; obtain ⟨w, hwG, hwt⟩ := hS_mem t ht
        rw [← hwt]
        exact Tube.ancestor_body_subset_cthickening_of_le (tb (Fin.last M) w)
            (tb m.succ (Anc m.succ w))
          (hAnc_ge m.succ w (hG_sub hwG)) K (hFK_le_K w (hG_sub hwG))
      have hS_body_q : ∀ t ∈ S,
          (tb m.succ t).carrier ⊆ Metric.cthickening (4 * (ρ m.succ : ℝ))
                (tb m.castSucc q).carrier := by
        intro t ht
        have h1 : (tb m.succ t).carrier ⊆ (tb m.castSucc q).carrier := hS_le_q t ht
        exact h1.trans (Metric.self_subset_cthickening _)
      have hS_body_inter : ∀ t ∈ S,
          (tb m.succ t).carrier ⊆ (ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).carrier
            ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc q).carrier := by
        intro t ht
        exact Set.subset_inter (hS_body_K t ht) (hS_body_q t ht)
      have hKT_S : IsKatzTao S (fun t : κ m.succ => (tb m.succ t).toConvexSpaceBody) (Δ m) := by
        by_cases hq_mem : q ∈ P m.castSucc
        · refine (h_local m q hq_mem).subset ?_
          intro t ht
          have hS_inP' : t ∈ P m.succ := hS_inP t ht
          obtain ⟨w, hwG, hwt⟩ := hS_mem t ht
          refine Finset.mem_filter.mpr ⟨hS_inP', ?_⟩
          calc proj m t = proj m (Anc m.succ w) := by rw [hwt]
            _ = Anc m.castSucc w := by rw [hAnc_castSucc m w]
            _ = q := hG_pin w hwG
        · have hS_empty : S = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro t ht
            obtain ⟨w, hwG, _⟩ := hS_mem t ht
            exact hq_mem (hG_pin w hwG ▸ hAnc_mem m.castSucc w (hG_sub hwG))
          rw [hS_empty]
          exact (h_local m (par_seed m) (hpar_seed_mem m)).subset
            (Finset.empty_subset _)
      have hv_pos : (0 : ℝ) < c * ((ρ m.succ : NNReal) : ℝ) ^ (n - 1) :=
        mul_pos hc_pos (pow_pos (by exact_mod_cast hρ_succ_pos m) _)
      by_cases hS_ne : S.Nonempty
      · obtain ⟨t₀, ht₀⟩ := hS_ne
        have ht₀_body_ne : ((tb m.succ t₀).toConvexSpaceBody.carrier).Nonempty :=
          (tb m.succ t₀).toConvexSpaceBody.nonempty
        let K_inter : ConvexSpaceBody E := {
          carrier := (ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).carrier
            ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc q).carrier
          convex' := (Convex.inter
            (ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).convex
            ((tb m.castSucc q).toConvexSpaceBody.convex.cthickening _)).isConvexSet
          isCompact' := IsCompact.inter
            (ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).isCompact
            ((tb m.castSucc q).toConvexSpaceBody.isCompact.cthickening)
          nonempty' := by
            obtain ⟨z, hz⟩ := ht₀_body_ne
            exact ⟨z, hS_body_inter t₀ ht₀ hz⟩ }
        have h_sub : ∀ t ∈ S, (tb m.succ t).toConvexSpaceBody ≤ K_inter := by
          intro t ht; exact hS_body_inter t ht
        have h_vol_lb : ∀ t ∈ S, c * ((ρ m.succ : NNReal) : ℝ) ^ (n - 1) ≤
            volume.real ((tb m.succ t).toConvexSpaceBody).carrier := by
          intro t _; exact hc_LB (hρ_succ_pos m) (tb m.succ t)
        have hcard := ConvexSpaceBody.IsKatzTao.card_le_div_real
          hKT_S (hΔ_top m) hv_pos
          h_sub h_vol_lb
        have hρpow_pos : (0 : ℝ) < ((ρ m.succ : NNReal) : ℝ) ^ (n - 1) :=
          pow_pos (by exact_mod_cast hρ_succ_pos m) _
        refine hcard.trans (le_of_eq ?_)
        have hBeq : B m q = (Δ m).toReal * volume.real K_inter.carrier
              / (((ρ m.succ : NNReal) : ℝ) ^ (n - 1)) := by
          change (Δ m).toReal * volume.real
              ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).carrier
                ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc q).carrier)
              / (ρr m.succ ^ (n - 1)) = _
          rw [hρr_def]
        rw [hBeq, div_div]
        congr 1
        rw [mul_comm c]
      · rw [Finset.not_nonempty_iff_eq_empty] at hS_ne
        rw [hS_ne]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact div_nonneg (hB_nn_any m q) hc_pos.le
    have scale0_bound : ((F_K.image (Anc 0)).card : ℝ) ≤ C_cover := by
      set S0 : Finset (κ 0) := F_K.image (Anc 0) with hS0_def
      have hS0_inP : ∀ t ∈ S0, t ∈ P 0 := by
        intro t ht; rw [hS0_def, Finset.mem_image] at ht
        obtain ⟨w, hwF, hwt⟩ := ht; rw [← hwt]; exact hAnc_mem 0 w hwF
      have hS0_sub : S0 ⊆ P 0 := fun t ht => hS0_inP t ht
      calc ((S0).card : ℝ) ≤ ((P 0).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hS0_sub
        _ ≤ C_cover := hP0_count
    rcases Finset.eq_empty_or_nonempty F_K with hFK_empty | hFK_ne
    · refine ⟨par_seed, hpar_seed_mem, hpar_seed_ball, ?_⟩
      rw [hFK_empty]
      simp only [Finset.card_empty, Nat.cast_zero]
      refine mul_nonneg (mul_nonneg hC_cover_pos.le
        (Finset.prod_nonneg fun m _ => ?_)) (by positivity)
      exact hB_nn_any m _
    · obtain ⟨w₀G, hw₀G_F, hw₀G_max⟩ := Finset.exists_max_image F_K
        (fun w => (F_K.filter (fun u => Anc 0 u = Anc 0 w)).card) hFK_ne
      set G : Finset (κ (Fin.last M)) :=
        F_K.filter (fun w => Anc 0 w = Anc 0 w₀G) with hG_def
      have hG_sub : G ⊆ F_K := Finset.filter_subset _ _
      have hFK_le_G : (F_K.card : ℝ) ≤ C_cover * (G.card : ℝ) := by
        have hcover : F_K ⊆ (F_K.image (Anc 0)).biUnion
            (fun t => F_K.filter (fun u => Anc 0 u = t)) := by
          intro w hw
          refine Finset.mem_biUnion.mpr ⟨Anc 0 w, Finset.mem_image_of_mem _ hw,
            Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
        have hnat : F_K.card ≤ (F_K.image (Anc 0)).card * G.card := by
          calc F_K.card
              ≤ ((F_K.image (Anc 0)).biUnion
                  (fun t => F_K.filter (fun u => Anc 0 u = t))).card :=
                Finset.card_le_card hcover
            _ ≤ ∑ t ∈ F_K.image (Anc 0), (F_K.filter (fun u => Anc 0 u = t)).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ _t ∈ F_K.image (Anc 0), G.card := by
                refine Finset.sum_le_sum ?_
                intro t ht
                rw [Finset.mem_image] at ht
                obtain ⟨w, hwF, hwt⟩ := ht
                rw [hG_def]
                have := hw₀G_max w hwF
                rwa [← hwt]
            _ = (F_K.image (Anc 0)).card * G.card := by
                rw [Finset.sum_const, smul_eq_mul]
        calc (F_K.card : ℝ)
            ≤ ((F_K.image (Anc 0)).card : ℝ) * (G.card : ℝ) := by exact_mod_cast hnat
          _ ≤ C_cover * (G.card : ℝ) :=
              mul_le_mul_of_nonneg_right scale0_bound (Nat.cast_nonneg _)
      have telescope : ∀ i : ℕ, i ≤ M → ∃ w' ∈ G,
          (G.card : ℝ) ≤
            (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i),
              B m (Anc m.castSucc w') / c)
            * ((G.filter (fun w => ∀ m : Fin M, m.val < i →
                Anc m.succ w = Anc m.succ w')).card : ℝ) := by
        intro i
        induction i with
        | zero =>
            intro _
            refine ⟨w₀G, ?_, ?_⟩
            · rw [hG_def]; exact Finset.mem_filter.mpr ⟨hw₀G_F, rfl⟩
            · have hprod : (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < 0),
                  B m (Anc m.castSucc w₀G) / c) = 1 := by
                rw [Finset.filter_eq_empty_iff.mpr (by intro m _; exact Nat.not_lt_zero _),
                  Finset.prod_empty]
              have hfilt : G.filter (fun w => ∀ m : Fin M, m.val < 0 →
                  Anc m.succ w = Anc m.succ w₀G) = G := by
                apply Finset.filter_true_of_mem
                intro w _ m hm; exact absurd hm (Nat.not_lt_zero _)
              rw [hprod, hfilt, one_mul]
        | succ i ih =>
            intro hi_le
            have hi_lt : i < M := hi_le
            obtain ⟨w', hw'G, hw'_bound⟩ := ih (le_of_lt hi_lt)
            set m₀ : Fin M := ⟨i, hi_lt⟩ with hm₀_def
            set Gcell : Finset (κ (Fin.last M)) :=
              G.filter (fun w => ∀ m : Fin M, m.val < i → Anc m.succ w = Anc m.succ w')
              with hGcell_def
            have hGcell_sub_G : Gcell ⊆ G := Finset.filter_subset _ _
            have hGcell_sub_F : Gcell ⊆ F_K := hGcell_sub_G.trans hG_sub
            have hpin_cast : ∀ w ∈ Gcell, Anc m₀.castSucc w = Anc m₀.castSucc w' := by
              intro w hw
              by_cases hi0 : i = 0
              · have hwG : w ∈ G := hGcell_sub_G hw
                have hw'G' : w' ∈ G := hw'G
                rw [hG_def, Finset.mem_filter] at hwG hw'G'
                have h0 : (m₀.castSucc : Fin (M + 1)) = (0 : Fin (M + 1)) := by
                  apply Fin.ext
                  simp only [Fin.val_castSucc, hm₀_def, hi0, Fin.val_zero]
                rw [h0, hwG.2, hw'G'.2]
              · have hi1 : i - 1 < M := by omega
                have hidx : (⟨i - 1, hi1⟩ : Fin M).val < i := by
                  change i - 1 < i; omega
                have hmem := (Finset.mem_filter.mp hw).2 ⟨i - 1, hi1⟩ hidx
                have heq : (m₀.castSucc : Fin (M + 1)) = (⟨i - 1, hi1⟩ : Fin M).succ := by
                  apply Fin.ext
                  simp only [Fin.val_castSucc, Fin.val_succ, hm₀_def]; omega
                rw [heq]; exact hmem
            set q : κ m₀.castSucc := Anc m₀.castSucc w' with hq_def
            have hpin_q : ∀ w ∈ Gcell, Anc m₀.castSucc w = q := by
              intro w hw; rw [hq_def]; exact hpin_cast w hw
            by_cases hGcell_ne : Gcell.Nonempty
            · obtain ⟨v', hv'_cell, hv'_max⟩ := Finset.exists_max_image Gcell
                (fun w => (Gcell.filter (fun u => Anc m₀.succ u = Anc m₀.succ w)).card)
                hGcell_ne
              set Gnext : Finset (κ (Fin.last M)) :=
                Gcell.filter (fun u => Anc m₀.succ u = Anc m₀.succ v') with hGnext_def
              have hcover2 : Gcell ⊆ (Gcell.image (Anc m₀.succ)).biUnion
                  (fun t => Gcell.filter (fun u => Anc m₀.succ u = t)) := by
                intro w hw
                refine Finset.mem_biUnion.mpr ⟨Anc m₀.succ w,
                  Finset.mem_image_of_mem _ hw, Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
              have hnat2 : Gcell.card ≤ (Gcell.image (Anc m₀.succ)).card * Gnext.card := by
                calc Gcell.card
                    ≤ ((Gcell.image (Anc m₀.succ)).biUnion
                        (fun t => Gcell.filter (fun u => Anc m₀.succ u = t))).card :=
                      Finset.card_le_card hcover2
                  _ ≤ ∑ t ∈ Gcell.image (Anc m₀.succ),
                        (Gcell.filter (fun u => Anc m₀.succ u = t)).card :=
                      Finset.card_biUnion_le
                  _ ≤ ∑ _t ∈ Gcell.image (Anc m₀.succ), Gnext.card := by
                      refine Finset.sum_le_sum ?_
                      intro t ht
                      rw [Finset.mem_image] at ht
                      obtain ⟨w, hwc, hwt⟩ := ht
                      rw [hGnext_def]
                      have := hv'_max w hwc
                      rwa [← hwt]
                  _ = (Gcell.image (Anc m₀.succ)).card * Gnext.card := by
                      rw [Finset.sum_const, smul_eq_mul]
              have hbranch : ((Gcell.image (Anc m₀.succ)).card : ℝ) ≤ B m₀ q / c :=
                branch_bound m₀ Gcell q hGcell_sub_F hpin_q
              have hGcell_le : (Gcell.card : ℝ) ≤ (B m₀ q / c) * (Gnext.card : ℝ) := by
                calc (Gcell.card : ℝ)
                    ≤ ((Gcell.image (Anc m₀.succ)).card : ℝ) * (Gnext.card : ℝ) := by
                      exact_mod_cast hnat2
                  _ ≤ (B m₀ q / c) * (Gnext.card : ℝ) :=
                      mul_le_mul_of_nonneg_right hbranch (Nat.cast_nonneg _)
              refine ⟨v', hGcell_sub_G hv'_cell, ?_⟩
              have hcell_eq : Gnext =
                  G.filter (fun w => ∀ m : Fin M, m.val < i + 1 →
                    Anc m.succ w = Anc m.succ v') := by
                ext w
                simp only [hGnext_def, hGcell_def, Finset.mem_filter]
                constructor
                · rintro ⟨⟨hwG, hwcell⟩, hwlast⟩
                  refine ⟨hwG, ?_⟩
                  intro m hm
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm'
                  · have hv'mem := (Finset.mem_filter.mp hv'_cell).2 m hm'
                    rw [hwcell m hm', hv'mem]
                  · have hmm : m = m₀ := by
                      apply Fin.ext; rw [hm₀_def]; exact hm'
                    subst hmm; exact hwlast
                · rintro ⟨hwG, hw_all⟩
                  refine ⟨⟨hwG, ?_⟩, ?_⟩
                  · intro m hm
                    have h1 := hw_all m (Nat.lt_succ_of_lt hm)
                    have hv'mem := (Finset.mem_filter.mp hv'_cell).2 m hm
                    rw [h1, hv'mem]
                  · have hmm : (m₀ : Fin M).val < i + 1 := by
                      change i < i + 1; omega
                    exact hw_all m₀ hmm
              have hq_v' : q = Anc m₀.castSucc v' := (hpin_q v' hv'_cell).symm
              have hprod_match : ∀ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i),
                  B m (Anc m.castSucc w') / c = B m (Anc m.castSucc v') / c := by
                intro m hm
                rw [Finset.mem_filter] at hm
                have hmi : m.val < i := hm.2
                have key : Anc m.castSucc w' = Anc m.castSucc v' := by
                  by_cases hm0 : m.val = 0
                  · have hv'G : v' ∈ G := hGcell_sub_G hv'_cell
                    have hw'G' : w' ∈ G := hw'G
                    rw [hG_def, Finset.mem_filter] at hv'G hw'G'
                    have h0 : (m.castSucc : Fin (M + 1)) = (0 : Fin (M + 1)) := by
                      apply Fin.ext; simp only [Fin.val_castSucc, hm0, Fin.val_zero]
                    rw [h0, hw'G'.2, hv'G.2]
                  · have hmpred : m.val - 1 < M := by omega
                    have hcast2 : (m.castSucc : Fin (M + 1))
                        = (⟨m.val - 1, hmpred⟩ : Fin M).succ := by
                      apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_succ]; omega
                    have hlt : (⟨m.val - 1, hmpred⟩ : Fin M).val < i := by
                      change m.val - 1 < i; omega
                    have hv'mem2 := (Finset.mem_filter.mp hv'_cell).2 ⟨m.val - 1, hmpred⟩ hlt
                    rw [hcast2]; exact hv'mem2.symm
                rw [key]
              have hprod_eq : (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i + 1),
                    B m (Anc m.castSucc v') / c)
                  = (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i),
                      B m (Anc m.castSucc v') / c) * (B m₀ (Anc m₀.castSucc v') / c) := by
                have hm₀v : (m₀ : Fin M).val = i := by simp [hm₀_def]
                have hmem_m₀ : m₀ ∈ Finset.univ.filter (fun m : Fin M => m.val < i + 1) := by
                  rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hm₀v]; omega⟩
                rw [← Finset.prod_erase_mul _ _ hmem_m₀]
                congr 1
                apply Finset.prod_congr
                · ext m
                  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · rintro ⟨hne, hlt⟩
                    have hmval : m.val ≠ i := fun h => hne (Fin.ext (h.trans hm₀v.symm))
                    omega
                  · intro hlt
                    exact ⟨fun h => by rw [h, hm₀v] at hlt; omega, by omega⟩
                · intro m _; rfl
              calc (G.card : ℝ)
                  ≤ (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i),
                      B m (Anc m.castSucc w') / c) * (Gcell.card : ℝ) := hw'_bound
                _ ≤ (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i),
                      B m (Anc m.castSucc w') / c) * ((B m₀ q / c) * (Gnext.card : ℝ)) := by
                    refine mul_le_mul_of_nonneg_left hGcell_le ?_
                    exact Finset.prod_nonneg fun m _ =>
                      div_nonneg (hB_nn_any m _) hc_pos.le
                _ = (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i + 1),
                      B m (Anc m.castSucc v') / c) * (Gnext.card : ℝ) := by
                    have hPeq : (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i),
                          B m (Anc m.castSucc w') / c)
                        = (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i),
                          B m (Anc m.castSucc v') / c) :=
                      Finset.prod_congr rfl hprod_match
                    have hBq : B m₀ q / c = B m₀ (Anc m₀.castSucc v') / c := by rw [hq_v']
                    rw [hprod_eq, hPeq, hBq]; ring
                _ = (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < i + 1),
                      B m (Anc m.castSucc v') / c)
                    * ((G.filter (fun w => ∀ m : Fin M, m.val < i + 1 →
                        Anc m.succ w = Anc m.succ v')).card : ℝ) := by
                    rw [hcell_eq]
            · rw [Finset.not_nonempty_iff_eq_empty] at hGcell_ne
              refine ⟨w', hw'G, ?_⟩
              have hGcard0 : (Gcell.card : ℝ) = 0 := by rw [hGcell_ne]; simp
              have hG0 : (G.card : ℝ) ≤ 0 := by
                rw [hGcard0, mul_zero] at hw'_bound; exact hw'_bound
              calc (G.card : ℝ) ≤ 0 := hG0
                _ ≤ _ := by
                    refine mul_nonneg (Finset.prod_nonneg fun m _ =>
                      div_nonneg (hB_nn_any m _) hc_pos.le) (Nat.cast_nonneg _)
      obtain ⟨wS, hwS_G, hwS_bound⟩ := telescope M (le_refl M)
      set Glast : Finset (κ (Fin.last M)) :=
        G.filter (fun w => ∀ m : Fin M, m.val < M → Anc m.succ w = Anc m.succ wS)
        with hGlast_def
      have hGlast_sub : Glast ⊆ {wS} := by
        intro w hw
        rw [hGlast_def, Finset.mem_filter] at hw
        obtain ⟨hwG, hw_all⟩ := hw
        have hwF : w ∈ F_K := hG_sub hwG
        have hm_last : (⟨M - 1, by omega⟩ : Fin M).val < M := by omega
        have h1 := hw_all ⟨M - 1, by omega⟩ hm_last
        have hlast_eq : ((⟨M - 1, by omega⟩ : Fin M).succ : Fin (M + 1)) = Fin.last M := by
          apply Fin.ext; simp only [Fin.val_succ, Fin.val_last]; omega
        rw [hlast_eq] at h1
        have hw'F : wS ∈ F_K := hG_sub hwS_G
        rw [hAnc_last w hwF, hAnc_last wS hw'F] at h1
        rw [Finset.mem_singleton]; exact h1
      have hGlast_card : (Glast.card : ℝ) ≤ 1 := by
        have := Finset.card_le_card hGlast_sub
        rw [Finset.card_singleton] at this
        exact_mod_cast this
      have hfull : Finset.univ.filter (fun m : Fin M => m.val < M) = Finset.univ := by
        ext m; simp
      have hG_final : (G.card : ℝ) ≤
          (∏ m : Fin M, B m (Anc m.castSucc wS) / c) := by
        have hp_nn : 0 ≤ ∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < M),
            B m (Anc m.castSucc wS) / c :=
          Finset.prod_nonneg fun m _ => div_nonneg (hB_nn_any m _) hc_pos.le
        calc (G.card : ℝ)
            ≤ (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < M),
                B m (Anc m.castSucc wS) / c) * (Glast.card : ℝ) := hwS_bound
          _ ≤ (∏ m ∈ Finset.univ.filter (fun m : Fin M => m.val < M),
                B m (Anc m.castSucc wS) / c) * 1 :=
              mul_le_mul_of_nonneg_left hGlast_card hp_nn
          _ = (∏ m : Fin M, B m (Anc m.castSucc wS) / c) := by
              rw [mul_one, hfull]
      have hwS_F : wS ∈ F_K := hG_sub hwS_G
      refine ⟨fun m => Anc m.castSucc wS,
        fun m => hAnc_mem m.castSucc wS hwS_F,
        fun m => P_in_ball m.castSucc (Anc m.castSucc wS) (hAnc_mem m.castSucc wS hwS_F), ?_⟩
      have hfinal : (F_K.card : ℝ) ≤ C_cover * (∏ m : Fin M, B m (Anc m.castSucc wS) / c) :=
        le_trans hFK_le_G (mul_le_mul_of_nonneg_left hG_final hC_cover_pos.le)
      refine hfinal.trans (le_of_eq ?_)
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        mul_div_assoc]

open scoped Classical in
/-- Parent-chain leaf-count bound, indexed by an abstract node family `κ` and a tube-valued map
`tb`.  The same telescope as `card_filter_chain_le_aux`, but with the constant `C` hoisted out as a
single `∃ C, ∀ …` and the coarsest-scale count bookkeeping hidden inside.  The Katz–Tao input is on
the fibre of the functional projection `proj`, not on the body-containment filter. -/
private theorem card_le_prod_density_volume_div_parent_level
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] :
    ∀ (R : ℝ), 1 ≤ R → ∀ (C_box : ℝ), 0 < C_box →
    ∃ C : ℝ, 0 < C ∧
      ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      ∀ (M : ℕ), 0 < M → ∀ (ρ : Fin (M + 1) → NNReal),
      1 ≤ ρ 0 → ρ 0 ≤ 4 → ρ (Fin.last M) = δ → Antitone ρ →
      (∀ m : Fin M, 4 * (ρ m.succ : ℝ) ≤ (ρ m.castSucc : ℝ)) →
      ∀ {κ : Fin (M + 1) → Type*} (tb : ∀ k : Fin (M + 1), κ k → Tube (ρ k) E),
      ∀ (P : ∀ k : Fin (M + 1), Finset (κ k)),
      ∀ (proj : ∀ m : Fin M, κ m.succ → κ m.castSucc),
      (∀ m : Fin M, ∀ w ∈ P m.succ, proj m w ∈ P m.castSucc) →
      (∀ m : Fin M, ∀ w ∈ P m.succ,
          (tb m.succ w).toConvexSpaceBody ≤ (tb m.castSucc (proj m w)).toConvexSpaceBody) →
      (((P (0 : Fin (M + 1))).card : ℝ)
          ≤ C_box * (R + 3) ^ (2 * Module.finrank ℝ E)) →
      (∀ k : Fin (M + 1), ∀ t ∈ P k,
          (tb k t).carrier ⊆ Metric.closedBall (0 : E) (R + 3)) →
      (∀ m : Fin M, (P m.castSucc).Nonempty) →
      ∀ (Δ : Fin M → ENNReal), (∀ m : Fin M, Δ m ≠ ⊤) →
      (∀ m : Fin M, ∀ p ∈ P m.castSucc,
          IsKatzTao ((P m.succ).filter (fun w => proj m w = p))
            (fun w => (tb m.succ w).toConvexSpaceBody) (Δ m)) →
      ∀ K : ConvexSpaceBody E,
      ∃ par : ∀ m : Fin M, κ m.castSucc,
        (∀ m : Fin M, par m ∈ P m.castSucc) ∧
        (∀ m : Fin M, (tb m.castSucc (par m)).carrier ⊆ Metric.closedBall (0 : E) (R + 3)) ∧
        (((P (Fin.last M)).filter
            (fun w => (tb (Fin.last M) w).toConvexSpaceBody ≤ K)).card : ℝ) ≤
          C ^ M * ∏ m : Fin M,
            (Δ m).toReal * volume.real
              ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).carrier
                ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc (par m)).carrier)
            / ((ρ m.succ : ℝ) ^ (Module.finrank ℝ E - 1)) := by
  intro R hR_ge_one C_box hC_box_pos
  classical
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  set c : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
  have hc_pos : 0 < c := by exact_mod_cast Tube.le_volume.c_pos (Module.finrank ℝ E)
  set C_crude : ℝ := C_box with hC_crude_def
  have hC_crude_pos : 0 < C_crude := hC_box_pos
  set n := Module.finrank ℝ E with hn_def
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_ge_one
  have hR3_pos : 0 < R + 3 := by linarith
  set C_cover : ℝ := C_crude * (R + 3) ^ (2 * n) with hC_cover_def
  have hC_cover_pos : 0 < C_cover := mul_pos hC_crude_pos (by positivity)
  set C_max : ℝ := max C_cover 1 with hC_max_def
  have hC_max_ge_cover : C_cover ≤ C_max := le_max_left _ _
  have hC_max_ge_one : 1 ≤ C_max := le_max_right _ _
  set Cfinal : ℝ := C_max / c + 1 with hCfinal_def
  have hCfinal_ge_one : 1 ≤ Cfinal := by
    linarith [div_nonneg (lt_of_lt_of_le zero_lt_one hC_max_ge_one).le hc_pos.le]
  have hCfinal_pos : 0 < Cfinal := lt_of_lt_of_le zero_lt_one hCfinal_ge_one
  refine ⟨Cfinal, hCfinal_pos, ?_⟩
  intro δ hδ_pos hδ_le_one M hM_pos ρ hρ0_ge_one hρ0_le_four hρ_M hρ_anti _hscale_gap κ tb
        P proj hproj_mem hproj_le P_count P_in_ball P_ne Δ hΔ_top h_local K
  have hρ_pos : ∀ k : Fin (M + 1), 0 < ρ k := fun k => by
    have hle : ρ (Fin.last M) ≤ ρ k := hρ_anti (Fin.le_last k)
    rw [hρ_M] at hle; exact lt_of_lt_of_le hδ_pos hle
  have hρ_succ_pos : ∀ m : Fin M, 0 < ρ m.succ := fun m => hρ_pos m.succ
  have hρ_castSucc_pos : ∀ m : Fin M, 0 < ρ m.castSucc := fun m => hρ_pos m.castSucc
  set ρr : Fin (M + 1) → ℝ := fun k => ((ρ k : NNReal) : ℝ) with hρr_def
  have hρr_pos : ∀ k : Fin (M + 1), (0 : ℝ) < ρr k := fun k => by exact_mod_cast hρ_pos k
  have hc : ∀ {δ' : NNReal}, 0 < δ' → ∀ T : Tube δ' E,
      c * (δ' : ℝ) ^ (n - 1) ≤ volume.real T.carrier := by
    intro δ' _ T'
    have hreal :=
      ENNReal.toReal_mono T'.isCompact.measure_lt_top.ne (Tube.le_volume (δ := δ') T')
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hreal
    exact hreal
  set F_K : Finset (κ (Fin.last M)) :=
    (P (Fin.last M)).filter (fun w => (tb (Fin.last M) w).toConvexSpaceBody ≤ K) with hF_K_def
  have hc_le_cV : c ≤ (Tube.le_volume.c n : ℝ) := le_refl _
  by_cases hne : F_K.Nonempty
  · obtain ⟨w0, hw0_mem⟩ := hne
    have hw0_in_P : w0 ∈ P (Fin.last M) :=
      (Finset.mem_filter.mp hw0_mem).1
    have hw0_le_K : (tb (Fin.last M) w0).toConvexSpaceBody ≤ K :=
      (Finset.mem_filter.mp hw0_mem).2
    have hP0_count : ((P 0).card : ℝ) ≤ C_cover := by
      rw [hC_cover_def, hC_crude_def, hn_def]
      exact P_count
    obtain ⟨par, hpar_mem, hpar_ball, h_card_sub_claim⟩ :=
      card_filter_chain_le_aux (E := E) (tb := tb) (κ := κ) R hR_pos c hc_pos
        C_cover hC_cover_pos
        hc_le_cV hδ_pos M hM_pos ρ hρ0_ge_one hρ_M hρ_anti hρ_pos
        P proj hproj_mem hproj_le hP0_count P_in_ball Δ hΔ_top h_local K w0 hw0_in_P hw0_le_K
    refine ⟨par, hpar_mem, hpar_ball, ?_⟩
    set B : Fin M → ℝ := fun m =>
      (Δ m).toReal * volume.real
        ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).carrier
          ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc (par m)).carrier)
        / (ρr m.succ ^ (n - 1)) with hB_def
    have hB_m_nn : ∀ m : Fin M, 0 ≤ B m := fun m => by
      apply div_nonneg
      · exact mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg
      · exact pow_nonneg (le_of_lt (hρr_pos _)) _
    have h_prod_B_nn : (0 : ℝ) ≤ ∏ m : Fin M, B m :=
      Finset.prod_nonneg (fun m _ => hB_m_nn m)
    have h_card_le_C_prod : (F_K.card : ℝ) ≤ C_cover * (∏ m : Fin M, B m) / c ^ M := by
      simpa [F_K, B, ρr, n] using h_card_sub_claim
    have hCfinal_c : C_max ≤ Cfinal * c := by
      have : Cfinal * c = C_max + c := by
        change (C_max / c + 1) * c = C_max + c; field_simp
      linarith [this, hc_pos]
    have hC_cover_over_c_pow_M : C_cover / c ^ M ≤ Cfinal ^ M := by
      have h_cover_le : C_cover ≤ Cfinal ^ M * c ^ M := by
        rw [← mul_pow]
        linarith [hC_max_ge_cover, hCfinal_c.trans <|
          (pow_one (Cfinal * c)).symm.le.trans <|
            pow_le_pow_right₀ (by linarith [hC_max_ge_one]) hM_pos]
      rw [div_le_iff₀ (pow_pos hc_pos M)]
      linarith
    have hc_pow_M_pos : (0 : ℝ) < c ^ M := pow_pos hc_pos M
    calc (F_K.card : ℝ)
        ≤ C_cover * (∏ m : Fin M, B m) / c ^ M := h_card_le_C_prod
      _ = C_cover / c ^ M * ∏ m : Fin M, B m := by ring
      _ ≤ Cfinal ^ M * ∏ m : Fin M, B m :=
          mul_le_mul_of_nonneg_right hC_cover_over_c_pow_M h_prod_B_nn
  · have hzero : (F_K.card : ℝ) = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty] at hne; rw [hne]; simp
    refine ⟨fun m => (P_ne m).choose,
      fun m => (P_ne m).choose_spec,
      fun m => P_in_ball m.castSucc (P_ne m).choose (P_ne m).choose_spec, ?_⟩
    rw [show (((P (Fin.last M)).filter
        (fun w => (tb (Fin.last M) w).toConvexSpaceBody ≤ K)).card : ℝ)
        = (F_K.card : ℝ) from rfl]
    rw [hzero]
    refine mul_nonneg (pow_nonneg hCfinal_pos.le _) ?_
    refine Finset.prod_nonneg fun m _ => ?_
    refine div_nonneg (mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg) ?_
    exact pow_nonneg (le_of_lt (by exact_mod_cast hρ_succ_pos m : (0 : ℝ) < (ρ m.succ : ℝ))) _


/-- Iterating `convexBody_cthickening_volume_le_2pow_of_ball`: if a convex
compact set `K` contains a closed `δ`-ball, then the `(j·δ)`-cthickening has
volume `≤ (2^n)^j · vol K`. -/
private lemma cth_nat_mul_le_pow_of_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : Set E) (hK_conv : Convex ℝ K) (hK_compact : IsCompact K)
    (p : E) {δ : ℝ} (hδ_nn : 0 ≤ δ) (hp_ball : Metric.closedBall p δ ⊆ K) :
    ∀ j : ℕ, volume (Metric.cthickening ((j : ℝ) * δ) K)
      ≤ (ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E)) ^ j * volume K := by
  intro j
  induction j with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero, one_mul]
    rw [Metric.cthickening_zero, hK_compact.isClosed.closure_eq]
  | succ k IH =>
    have hkδ_nn : (0 : ℝ) ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ_nn
    have hball_sub : Metric.closedBall p δ ⊆ Metric.cthickening ((k : ℝ) * δ) K :=
      hp_ball.trans (Metric.self_subset_cthickening _)
    have hConv' : Convex ℝ (Metric.cthickening ((k : ℝ) * δ) K) := hK_conv.cthickening _
    have hCompact' : IsCompact (Metric.cthickening ((k : ℝ) * δ) K) :=
      hK_compact.cthickening
    have hstep :=
      Kakeya.convexBody_cthickening_volume_le_2pow_of_ball
        (Metric.cthickening ((k : ℝ) * δ) K) hConv' hCompact' p hδ_nn hball_sub
    have heq : Metric.cthickening (((k : ℝ) + 1) * δ) K
        = Metric.cthickening δ (Metric.cthickening ((k : ℝ) * δ) K) := by
      rw [cthickening_cthickening hδ_nn hkδ_nn]
      congr 1; ring
    have hcast : ((k + 1 : ℕ) : ℝ) * δ = ((k : ℝ) + 1) * δ := by push_cast; ring
    rw [hcast, heq]
    calc volume (Metric.cthickening δ (Metric.cthickening ((k : ℝ) * δ) K))
        ≤ ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E)
            * volume (Metric.cthickening ((k : ℝ) * δ) K) := hstep
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E)
            * ((ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E)) ^ k * volume K) :=
          mul_le_mul_right IH _
      _ = (ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E)) ^ (k + 1) * volume K := by
          rw [pow_succ]; ring

open scoped Classical in
/-- Bounds leaf-level `maxDensity` by a product of the per-scale parent-level Katz–Tao
constants `Δ m` (GWZ Lemma 7.4).  The hypotheses package a Frostman-full uniform
construction: leaf-ED at scale `δ`, an all-scales chain `Q` with the engine's structural
hypotheses, a leaf→finest-cover map landing in `Q (Fin.last M)`, and the parent-level
Katz–Tao input phrased on the fibre of `proj`. -/
theorem maxDensity_le_prod_of_uniform_at_scales
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] :
    ∀ (R : ℝ), 1 ≤ R → ∀ (C_box : ℝ), 0 < C_box →
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) R) →
      ∀ (M : ℕ), 0 < M → ∀ (ρ : Fin (M + 1) → NNReal),
      1 ≤ ρ 0 → ρ 0 ≤ 4 → ρ (Fin.last M) = δ → Antitone ρ →
      (∀ m : Fin M, 4 * ρ m.succ ≤ ρ m.castSucc) →
      ∀ {κ : Fin (M + 1) → Type*} (tb : ∀ k : Fin (M + 1), κ k → Tube (ρ k) E),
      ∀ (Q : ∀ k : Fin (M + 1), Finset (κ k)),
      ∀ (proj : ∀ m : Fin M, κ m.succ → κ m.castSucc),
      (∀ m : Fin M, ∀ w ∈ Q m.succ, proj m w ∈ Q m.castSucc) →
      (∀ m : Fin M, ∀ w ∈ Q m.succ,
          (tb m.succ w).toConvexSpaceBody ≤ (tb m.castSucc (proj m w)).toConvexSpaceBody) →
      (((Q (0 : Fin (M + 1))).card : ℝ)
          ≤ C_box * (R + 3) ^ (2 * Module.finrank ℝ E)) →
      (∀ k : Fin (M + 1), ∀ t ∈ Q k,
          (tb k t).carrier ⊆ Metric.closedBall (0 : E) (R + 3)) →
      (∀ m : Fin M, (Q m.castSucc).Nonempty) →
      ∀ (cover : ι → κ (Fin.last M)),
      (∀ i ∈ s, cover i ∈ Q (Fin.last M)) →
      (∀ i ∈ s, (T i).toConvexSpaceBody ≤ (tb (Fin.last M) (cover i)).toConvexSpaceBody) →
      Set.InjOn cover (↑s : Set ι) →
      ∀ (Δ : Fin M → ENNReal), (∀ m : Fin M, Δ m ≠ ⊤) →
      (∀ m : Fin M, ∀ p ∈ Q m.castSucc,
          IsKatzTao ((Q m.succ).filter (fun w => proj m w = p))
            (fun w => (tb m.succ w).toConvexSpaceBody) (Δ m)) →
      maxDensity s (fun i => (T i).toConvexSpaceBody)
        ≤ ENNReal.ofReal C ^ M * ∏ m, Δ m := by
  intro R hR_ge_one C_box hC_box_pos
  classical
  set n := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_ge_one
  obtain ⟨Cengine, hCengine_pos, hCengine⟩ :=
    card_le_prod_density_volume_div_parent_level
      (E := E) R hR_ge_one C_box hC_box_pos
  obtain ⟨Cdim, hCdim_pos, h_telescope_four⟩ :=
    Tube.volume_thickening_telescope_paper_four (E := E)
  set μ : ℕ := 1 with hμ_def
  have hμ_pos : 0 < μ := one_pos
  set Cvol : ℝ := (Tube.volume_le.C n : ℝ) with hCvol_def
  have hCvol_pos : 0 < Cvol := by
    change (0 : ℝ) < ((Tube.volume_le.C n : NNReal) : ℝ)
    unfold Tube.volume_le.C
    push_cast
    positivity
  set vU : ℝ := volume.real (Metric.closedBall (0 : E) 1) with hvU_def
  have hvU_pos : 0 < vU := by
    rw [hvU_def, show volume.real (Metric.closedBall (0 : E) 1)
      = (volume (Metric.closedBall (0 : E) 1)).toReal from rfl]
    have hne : volume (Metric.closedBall (0 : E) 1) ≠ 0 := by
      rw [InnerProductSpace.volume_closedBall]
      simp only [ENNReal.ofReal_one, one_pow, one_mul, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hfin : volume (Metric.closedBall (0 : E) 1) ≠ ⊤ :=
      (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
    rw [ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hne, hfin.lt_top⟩
  set Kslack : ℝ := ((2 : ℝ) ^ n) ^ 8 * Cvol / vU with hKslack_def
  set Cprod : ℝ := (μ : ℝ) * Cengine * Cdim * max Kslack 1 * 4 ^ (n - 1) with hCprod_def
  have hKslack_nn : 0 ≤ Kslack :=
    div_nonneg (mul_nonneg (by positivity) hCvol_pos.le) hvU_pos.le
  have hslack_pos : 0 < max Kslack 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hμR_pos : (0 : ℝ) < (μ : ℝ) := by exact_mod_cast hμ_pos
  have hCprod_pos : 0 < Cprod := by
    rw [hCprod_def]
    positivity
  refine ⟨Cprod, hCprod_pos, ?_⟩
  intro ι δ hδ_pos hδr_le_one s T hT_sub M hM_pos ρ hρ0_ge_one hρ0_le_4 hρ_M hρ_anti hscale_gap
    κ tb Q proj hproj_mem hproj_le Q_count Q_in_ball Q_ne cover hcover_mem hcover_eq h_cover_inj
    Δ hΔ_top h_local
  have h_prod_ne_top : (∏ m, Δ m) ≠ ⊤ := ENNReal.prod_ne_top fun m _ => hΔ_top m
  rw [← ENNReal.ofReal_toReal (Kakeya.maxDensity_ne_top s _),
    ← ENNReal.ofReal_toReal h_prod_ne_top, ← ENNReal.ofReal_pow hCprod_pos.le,
    ← ENNReal.ofReal_mul (pow_nonneg hCprod_pos.le M)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hscale_gap_real : ∀ m : Fin M, 4 * (ρ m.succ : ℝ) ≤ (ρ m.castSucc : ℝ) :=
    fun m => by exact_mod_cast hscale_gap m
  set W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody with hW_def
  set Smax : Finset ι := density_maximizer s W with hSmax_def
  set K_max : ConvexSpaceBody E := Smax.convexHull_biUnion W with hKmax_def
  have h_rewrite :
      (maxDensity s W).toReal = (densityIn s W K_max).toReal :=
    congrArg ENNReal.toReal (densityIn_self_maximizer_eq s W).symm
  rw [h_rewrite]
  by_cases hSmax_ne : Smax.Nonempty
  · have hConv : Convexity.IsConvexSet ℝ (Metric.closedBall (0 : E) R) :=
      (ConvexSpaceBody.closedBall_carrier (0 : E) R (by positivity)) ▸
        (ConvexSpaceBody.closedBall (0 : E) R (by positivity)).isConvexSet
    have hKmax_sub_R : K_max.carrier ⊆ Metric.closedBall (0 : E) R := by
      rw [hKmax_def, hSmax_ne.convexHull_biUnion_subset_iff W hConv]
      intro i hi
      have hi_s : i ∈ s := density_maximizer_subset s W hi
      exact hT_sub i hi_s
    set δr : ℝ := (δ : ℝ) with hδr_def
    set ρr : Fin (M + 1) → ℝ := fun k => ((ρ k : NNReal) : ℝ) with hρr_def
    have hδr_pos : (0 : ℝ) < δr := by exact_mod_cast hδ_pos
    have hρ_pos : ∀ k : Fin (M + 1), 0 < ρ k := fun k => by
      have hle : ρ (Fin.last M) ≤ ρ k := hρ_anti (Fin.le_last k)
      rw [hρ_M] at hle; exact lt_of_lt_of_le hδ_pos hle
    have hρr_pos : ∀ k : Fin (M + 1), (0 : ℝ) < ρr k := fun k => by exact_mod_cast hρ_pos k
    have hρr0_ge_one : 1 ≤ ρr 0 := by
      simp only [hρr_def]; exact_mod_cast hρ0_ge_one
    have hρr0_le_4 : ρr 0 ≤ 4 := by
      simp only [hρr_def]; exact_mod_cast hρ0_le_4
    have hρr_M : ρr (Fin.last M) = δr := by
      simp only [hρr_def, hδr_def]; exact_mod_cast hρ_M
    have hδ_pow_pos : (0 : ℝ) < δr ^ (n - 1) := pow_pos hδr_pos _
    obtain ⟨i₀, hi₀_Smax⟩ := hSmax_ne
    have hi₀_s : i₀ ∈ s := density_maximizer_subset s W hi₀_Smax
    have hW_i₀_sub_K_max : W i₀ ≤ K_max := by
      rw [hKmax_def]; exact Finset.le_convexHull_biUnion W hi₀_Smax
    set c : ℝ := (Tube.le_volume.c n : ℝ) with hc_def
    have hc_pos : 0 < c := by exact_mod_cast Tube.le_volume.c_pos n
    have hW_i₀_vol_lb : c * δr ^ (n - 1) ≤ volume.real (W i₀).carrier := by
      have h := Tube.le_volume (E := E) (δ := δ) (T i₀)
      have hreal := ENNReal.toReal_mono (T i₀).isCompact.measure_lt_top.ne h
      change c * δr ^ (n - 1) ≤ volume.real (T i₀).carrier
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
        ENNReal.coe_toReal] at hreal
      exact hreal
    have hW_i₀_vol_pos : 0 < volume.real (W i₀).carrier :=
      lt_of_lt_of_le (mul_pos hc_pos hδ_pow_pos) hW_i₀_vol_lb
    have hK_max_vol_lb : c * δr ^ (n - 1) ≤ volume.real K_max.carrier :=
      hW_i₀_vol_lb.trans
        (measureReal_mono hW_i₀_sub_K_max K_max.isCompact.measure_lt_top.ne)
    have hK_max_vol_pos : 0 < volume.real K_max.carrier :=
      lt_of_lt_of_le (mul_pos hc_pos hδ_pow_pos) hK_max_vol_lb
    have hK_max_vol_ne : volume K_max.carrier ≠ 0 := by
      intro h
      have hreal : volume.real K_max.carrier = 0 := by
        unfold MeasureTheory.Measure.real; rw [h]; simp
      linarith [hK_max_vol_pos]
    have hK_max_vol_top : volume K_max.carrier ≠ ⊤ := K_max.isCompact.measure_lt_top.ne
    have h_ball_left : Metric.closedBall (T i₀).x (δ : ℝ) ⊆ (T i₀).carrier := by
      rw [(T i₀).carrier_eq]
      exact Set.subset_iUnion₂_of_subset (T i₀).x
        (left_mem_segment ℝ (T i₀).x (T i₀).y) le_rfl
    have h_ball_in_Kmax : Metric.closedBall (T i₀).x (δ : ℝ) ⊆ K_max.carrier :=
      h_ball_left.trans hW_i₀_sub_K_max
    set F_K : Finset ι := s.filter (fun i => (T i).toConvexSpaceBody ≤ K_max) with hF_K_def
    set K' : ConvexSpaceBody E := K_max.cthickening (4 * (ρ (Fin.last M) : ℝ)) with hK'_def
    set G_K : Finset (κ (Fin.last M)) :=
      (Q (Fin.last M)).filter (fun w => (tb (Fin.last M) w).toConvexSpaceBody ≤ K') with hG_K_def
    have h_cover_mapsTo : Set.MapsTo cover (↑F_K) (↑G_K) := by
      intro i hi
      rw [Finset.mem_coe, hF_K_def, Finset.mem_filter] at hi
      obtain ⟨hi_s, hi_le⟩ := hi
      rw [Finset.mem_coe, hG_K_def, Finset.mem_filter]
      refine ⟨hcover_mem i hi_s, ?_⟩
      exact Tube.ancestor_body_subset_cthickening_of_le (T i) (tb (Fin.last M) (cover i))
        (hcover_eq i hi_s) K_max hi_le
    have h_fiber : ∀ b ∈ Finset.image cover F_K,
        {a ∈ F_K | cover a = b}.card ≤ μ := by
      intro b _hb
      have hle1 : ({a ∈ F_K | cover a = b}).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha a' ha'
        rw [Finset.mem_filter] at ha ha'
        have has : a ∈ s := by
          rw [hF_K_def, Finset.mem_filter] at ha; exact ha.1.1
        have ha's : a' ∈ s := by
          rw [hF_K_def, Finset.mem_filter] at ha'; exact ha'.1.1
        exact h_cover_inj (Finset.mem_coe.mpr has) (Finset.mem_coe.mpr ha's)
          (ha.2.trans ha'.2.symm)
      exact le_trans hle1 hμ_pos
    have h_card_le_image : F_K.card ≤ μ * (Finset.image cover F_K).card :=
      Finset.card_le_mul_card_image F_K μ h_fiber
    have h_image_sub_G : Finset.image cover F_K ⊆ G_K := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      exact h_cover_mapsTo (Finset.mem_coe.mpr hi)
    have h_card_FK_le : (F_K.card : ℝ) ≤ (μ : ℝ) * (G_K.card : ℝ) := by
      have h1 : F_K.card ≤ μ * G_K.card :=
        h_card_le_image.trans (Nat.mul_le_mul_left μ (Finset.card_le_card h_image_sub_G))
      exact_mod_cast h1
    obtain ⟨par, hpar_in_Q, hpar_ball, h_engine⟩ :=
      hCengine hδ_pos hδr_le_one M hM_pos ρ hρ0_ge_one hρ0_le_4 hρ_M hρ_anti hscale_gap_real
        (κ := κ) (tb := tb) Q proj hproj_mem hproj_le Q_count Q_in_ball Q_ne Δ hΔ_top h_local K'
    have h_engine' : (G_K.card : ℝ) ≤
        Cengine ^ M * ∏ m : Fin M,
          (Δ m).toReal * volume.real
            ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K').carrier
              ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc (par m)).carrier)
          / ((ρ m.succ : ℝ) ^ (Module.finrank ℝ E - 1)) := by
      simpa [hG_K_def] using h_engine
    have hΔ_nn : ∀ m : Fin M, 0 ≤ (Δ m).toReal := fun m => ENNReal.toReal_nonneg
    have hProd_Δ_nn : 0 ≤ (∏ m, Δ m).toReal := ENNReal.toReal_nonneg
    have hProd_Δ_toReal : (∏ m, Δ m).toReal = ∏ m : Fin M, (Δ m).toReal := by
      rw [ENNReal.toReal_prod]
    have hprod_eq : (∏ m : Fin M, (Δ m).toReal * volume.real
        ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K').carrier
          ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc (par m)).carrier)
          / ((ρ m.succ : ℝ) ^ (Module.finrank ℝ E - 1)))
        = (∏ m : Fin M, (Δ m).toReal) *
          ∏ m : Fin M, volume.real
            ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K').carrier
              ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (tb m.castSucc (par m)).carrier)
            / ((ρ m.succ : ℝ) ^ (Module.finrank ℝ E - 1)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intros m _; ring
    have hR4_ge_one : (1 : ℝ) ≤ R + 4 := by linarith
    have hK'_sub_R4 : K'.carrier ⊆ Metric.closedBall (0 : E) (R + 4) := by
      rw [hK'_def]
      change Metric.cthickening (4 * (ρ (Fin.last M) : ℝ)) K_max.carrier
          ⊆ Metric.closedBall (0 : E) (R + 4)
      have hsub : Metric.cthickening (4 * (ρ (Fin.last M) : ℝ)) K_max.carrier
          ⊆ Metric.cthickening (4 * (ρ (Fin.last M) : ℝ)) (Metric.closedBall (0 : E) R) :=
        Metric.cthickening_subset_of_subset _ hKmax_sub_R
      refine hsub.trans ?_
      have h4δ_le : 4 * (ρ (Fin.last M) : ℝ) ≤ 4 := by
        rw [hρ_M]; have : (δ : ℝ) ≤ 1 := hδr_le_one; linarith
      calc Metric.cthickening (4 * (ρ (Fin.last M) : ℝ)) (Metric.closedBall (0 : E) R)
          ⊆ Metric.cthickening 4 (Metric.closedBall (0 : E) R) :=
            Metric.cthickening_mono h4δ_le _
        _ = Metric.closedBall (0 : E) (4 + R) :=
            cthickening_closedBall (by norm_num : (0:ℝ) ≤ 4) (by linarith : (0:ℝ) ≤ R) _
        _ ⊆ Metric.closedBall (0 : E) (R + 4) := by
            rw [show (4 : ℝ) + R = R + 4 by ring]
    have hK'_vol_pos : 0 < volume.real K'.carrier := by
      refine lt_of_lt_of_le hK_max_vol_pos ?_
      apply measureReal_mono ?_ K'.isCompact.measure_lt_top.ne
      rw [hK'_def]
      change K_max.carrier ⊆ Metric.cthickening (4 * (ρ (Fin.last M) : ℝ)) K_max.carrier
      exact Metric.self_subset_cthickening _
    set par_tubes : ∀ m : Fin M, Tube (ρ m.castSucc) E :=
    fun m => tb m.castSucc (par m) with hpar_tubes_def
    have hpar_tubes_ball : ∀ m : Fin M, (par_tubes m).carrier ⊆
              Metric.closedBall (0 : E) ((R + 4) + 3) :=
      fun m => (hpar_ball m).trans (Metric.closedBall_subset_closedBall (by linarith))
    have hδ_le_one_nn : δ ≤ 1 := by exact_mod_cast hδr_le_one
    have h_telescope :
        ∏ m : Fin M, volume.real
            ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K').carrier
              ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (par_tubes m).carrier)
            / ((ρ m.succ : ℝ) ^ (Module.finrank ℝ E - 1))
          ≤ Cdim ^ M * (ρ 0 : ℝ) ^ (Module.finrank ℝ E - 1)
              * volume.real (Metric.cthickening (4 * δr) K'.carrier)
              / (δr ^ (Module.finrank ℝ E - 1)
                  * volume.real (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier)) := by
      have := h_telescope_four (R + 4) hR4_ge_one hδ_pos hδ_le_one_nn M hM_pos ρ
        hρ0_ge_one hρ0_le_4 hρ_M hρ_anti hscale_gap_real K' hK'_sub_R4
          hK'_vol_pos par_tubes hpar_tubes_ball
      simpa [δr, ρr] using this
    have hK'_carrier : K'.carrier = Metric.cthickening (4 * δr) K_max.carrier := by
      rw [hK'_def]
      change Metric.cthickening (4 * (ρ (Fin.last M) : ℝ)) K_max.carrier = _
      rw [show (ρ (Fin.last M) : ℝ) = δr from by rw [hρ_M]]
    have h_cth4_K'_eq : Metric.cthickening (4 * δr) K'.carrier
        = Metric.cthickening (8 * δr) K_max.carrier := by
      rw [hK'_carrier, cthickening_cthickening (by positivity) (by positivity)]
      congr 1; ring
    have h_cth_4δ_le_real :
        volume.real (Metric.cthickening (4 * δr) K'.carrier)
          ≤ ((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier := by
      rw [h_cth4_K'_eq]
      have hball8 := cth_nat_mul_le_pow_of_ball K_max.carrier K_max.convex
        K_max.isCompact (T i₀).x δ.coe_nonneg h_ball_in_Kmax 8
      have hcast8 : ((8 : ℕ) : ℝ) * δr = 8 * δr := by norm_num
      rw [hcast8] at hball8
      have hRHS_fin : (ENNReal.ofReal ((2 : ℝ) ^ n)) ^ 8 * volume K_max.carrier ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hK_max_vol_top
      have hmono := ENNReal.toReal_mono hRHS_fin hball8
      change (volume (Metric.cthickening (8 * δr) K_max.carrier)).toReal ≤ _
      rw [show ((ENNReal.ofReal ((2 : ℝ) ^ n)) ^ 8 * volume K_max.carrier).toReal
            = ((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier by
          rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
          rfl] at hmono
      exact hmono
    have h_cth_1_K'_ge_real :
        vU ≤ volume.real (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier) := by
      have h_ge_unit : volume (Metric.closedBall (0 : E) 1)
          ≤ volume (Metric.cthickening (1 : ℝ) K'.carrier) :=
        Kakeya.convexBody_cthickening_one_volume_ge_unit_ball K'.nonempty
      have h_cth_mono : Metric.cthickening (1 : ℝ) K'.carrier ⊆
              Metric.cthickening ((ρ 0 : ℝ)) K'.carrier :=
        Metric.cthickening_mono (by exact_mod_cast hρ0_ge_one) K'.carrier
      have h_ge_cth : volume (Metric.cthickening (1 : ℝ) K'.carrier)
          ≤ volume (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier) :=
        measure_mono h_cth_mono
      have hfin : volume (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier) ≠ ⊤ :=
        K'.isCompact.cthickening.measure_lt_top.ne
      have h_ge_total : volume (Metric.closedBall (0 : E) 1) ≤
          volume (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier) :=
        h_ge_unit.trans h_ge_cth
      have := ENNReal.toReal_mono hfin h_ge_total
      rw [hvU_def]; exact this
    have h_cth_1_K'_pos :
        0 < volume.real (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier) :=
      lt_of_lt_of_le hvU_pos h_cth_1_K'_ge_real
    have h_ratio_bound :
        volume.real (Metric.cthickening (4 * δr) K'.carrier)
            / (δr ^ (n - 1) * volume.real (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier))
          ≤ ((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier / (δr ^ (n - 1) * vU) := by
      have h_denom1_pos : 0 < δr ^ (n - 1) * volume.real
          (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier) := mul_pos hδ_pow_pos h_cth_1_K'_pos
      have h_denom2_pos : 0 < δr ^ (n - 1) * vU := mul_pos hδ_pow_pos hvU_pos
      rw [div_le_div_iff₀ h_denom1_pos h_denom2_pos]
      have h_num2_nn : (0 : ℝ) ≤ ((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier :=
        mul_nonneg (by positivity) measureReal_nonneg
      have h_left_le : volume.real (Metric.cthickening (4 * δr) K'.carrier) * vU
          ≤ (((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier) * vU :=
        mul_le_mul_of_nonneg_right h_cth_4δ_le_real hvU_pos.le
      have h_right_ge : ((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier * vU
          ≤ ((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier
            * volume.real (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier) :=
        mul_le_mul_of_nonneg_left h_cth_1_K'_ge_real h_num2_nn
      calc volume.real (Metric.cthickening (4 * δr) K'.carrier) * (δr ^ (n - 1) * vU)
          = volume.real (Metric.cthickening (4 * δr) K'.carrier) * vU * δr ^ (n - 1) := by
            ring
        _ ≤ ((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier * vU * δr ^ (n - 1) :=
            mul_le_mul_of_nonneg_right h_left_le hδ_pow_pos.le
        _ ≤ ((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier
            * volume.real (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier) * δr ^ (n - 1) :=
            mul_le_mul_of_nonneg_right h_right_ge hδ_pow_pos.le
        _ = ((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier
            * (δr ^ (n - 1) * volume.real (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier)) := by
            ring
    have hCdim_pow_nn : (0 : ℝ) ≤ Cdim ^ M := pow_nonneg hCdim_pos.le _
    have h_ρ0_pow_le_4_pow : (ρ 0 : ℝ) ^ (n - 1) ≤ (4 : ℝ) ^ (n - 1) := by
      have h_nonneg : 0 ≤ (ρ 0 : ℝ) := by positivity
      have h_le : (ρ 0 : ℝ) ≤ 4 := by exact_mod_cast hρ0_le_4
      exact pow_le_pow_left₀ h_nonneg h_le (n - 1)
    have h_4pow_nn : 0 ≤ (4 : ℝ) ^ (n - 1) := by positivity
    set V := volume.real (Metric.cthickening (4 * δr) K'.carrier) with hV_def
    set D := δr ^ (n - 1) * volume.real (Metric.cthickening ((ρ 0 : ℝ)) K'.carrier) with hD_def
    have hD_pos : 0 < D := by
      rw [hD_def]; exact mul_pos hδ_pow_pos h_cth_1_K'_pos
    have hV_nonneg : 0 ≤ V := measureReal_nonneg
    have h_telescope_clean :
        ∏ m : Fin M, volume.real
            ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K').carrier
              ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (par_tubes m).carrier)
            / ((ρ m.succ : ℝ) ^ (Module.finrank ℝ E - 1))
          ≤ Cdim ^ M * 4 ^ (n - 1) * (((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier
              / (δr ^ (n - 1) * vU)) := by
      calc
        ∏ m : Fin M, volume.real
              ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K').carrier
                ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (par_tubes m).carrier)
              / ((ρ m.succ : ℝ) ^ (Module.finrank ℝ E - 1))
            ≤ Cdim ^ M * (ρ 0 : ℝ) ^ (n - 1) * V / D := h_telescope
        _ = (Cdim ^ M * (ρ 0 : ℝ) ^ (n - 1)) * (V / D) := by
          have hD_ne_zero : D ≠ 0 := by linarith
          field_simp [hD_ne_zero]
        _ ≤ (Cdim ^ M * (4 : ℝ) ^ (n - 1)) * (V / D) := by
          have h_VD_nonneg : 0 ≤ V / D := div_nonneg hV_nonneg (by linarith)
          have h_factor : Cdim ^ M * (ρ 0 : ℝ) ^ (n - 1) ≤ Cdim ^ M * (4 : ℝ) ^ (n - 1) :=
            mul_le_mul_of_nonneg_left h_ρ0_pow_le_4_pow hCdim_pow_nn
          exact mul_le_mul_of_nonneg_right h_factor h_VD_nonneg
        _ = Cdim ^ M * (4 : ℝ) ^ (n - 1) * (V / D) := by ring
        _ ≤ Cdim ^ M * (4 : ℝ) ^ (n - 1) * (((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier
              / (δr ^ (n - 1) * vU)) :=
          mul_le_mul_of_nonneg_left h_ratio_bound (mul_nonneg hCdim_pow_nn (by positivity))
    have hCengine_pow_nn : (0 : ℝ) ≤ Cengine ^ M := pow_nonneg hCengine_pos.le _
    have h_GK_bound : (G_K.card : ℝ) ≤
        Cengine ^ M * ((∏ m, Δ m).toReal *
          (Cdim ^ M * 4 ^ (n - 1) * (((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier
            / (δr ^ (n - 1) * vU)))) := by
      refine h_engine'.trans ?_
      rw [hprod_eq]
      rw [show (∏ m : Fin M, (Δ m).toReal) = (∏ m, Δ m).toReal from hProd_Δ_toReal.symm]
      apply mul_le_mul_of_nonneg_left _ hCengine_pow_nn
      exact mul_le_mul_of_nonneg_left h_telescope_clean hProd_Δ_nn
    have h_FK_bound : (F_K.card : ℝ) ≤
        (μ : ℝ) * (Cengine ^ M * ((∏ m, Δ m).toReal *
          (Cdim ^ M * 4 ^ (n - 1) * (((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier
            / (δr ^ (n - 1) * vU))))) :=
      h_card_FK_le.trans (mul_le_mul_of_nonneg_left h_GK_bound hμR_pos.le)
    have hvol_W : ∀ i : ι, volume.real (W i).carrier ≤ Cvol * δr ^ (n - 1) := fun i => by
      have h := Tube.volume_le (E := E) (δ := δ) hδ_le_one_nn (T i)
      have hRHS_fin : (Tube.volume_le.C n : ENNReal) *
          (δ : ENNReal) ^ (n - 1) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      have hreal := ENNReal.toReal_mono hRHS_fin h
      change volume.real (T i).carrier ≤ Cvol * δr ^ (n - 1)
      simpa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_pow,
        MeasureTheory.Measure.real, hCvol_def, hδr_def] using hreal
    have h_sum_le : ∑ i ∈ F_K, volume.real (W i).carrier
        ≤ (F_K.card : ℝ) * (Cvol * δr ^ (n - 1)) := by
      calc ∑ i ∈ F_K, volume.real (W i).carrier
          ≤ ∑ _ ∈ F_K, (Cvol * δr ^ (n - 1)) := Finset.sum_le_sum (fun i _ => hvol_W i)
        _ = (F_K.card : ℝ) * (Cvol * δr ^ (n - 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hCvolδ_nn : 0 ≤ Cvol * δr ^ (n - 1) := mul_nonneg hCvol_pos.le hδ_pow_pos.le
    have h_sum_le_2 : ∑ i ∈ F_K, volume.real (W i).carrier
        ≤ (μ : ℝ) * (Cengine ^ M * ((∏ m, Δ m).toReal *
            (Cdim ^ M * 4 ^ (n - 1) * (((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier
              / (δr ^ (n - 1) * vU)))))
          * (Cvol * δr ^ (n - 1)) :=
      h_sum_le.trans (mul_le_mul_of_nonneg_right h_FK_bound hCvolδ_nn)
    have hsimp :
        (μ : ℝ) * (Cengine ^ M * ((∏ m, Δ m).toReal *
            (Cdim ^ M * 4 ^ (n - 1) * (((2 : ℝ) ^ n) ^ 8 * volume.real K_max.carrier
              / (δr ^ (n - 1) * vU)))))
          * (Cvol * δr ^ (n - 1))
        = (μ : ℝ) * (Cengine * Cdim) ^ M * 4 ^ (n - 1) * (((2 : ℝ) ^ n) ^ 8 * Cvol / vU)
            * (∏ m, Δ m).toReal * volume.real K_max.carrier := by
      have hδne : δr ^ (n - 1) ≠ 0 := hδ_pow_pos.ne'
      have hvUne : vU ≠ 0 := hvU_pos.ne'
      rw [mul_pow]
      field_simp
    rw [hsimp] at h_sum_le_2
    have h_densityIn_le_sum :
        (densityIn s W K_max).toReal =
          (∑ i ∈ F_K, volume.real (W i).carrier) / volume.real K_max.carrier := by
      change ((∑ i ∈ s with W i ≤ K_max, volume (W i).carrier)
          / volume K_max.carrier).toReal = _
      rw [ENNReal.toReal_div]
      congr 1
      change (∑ i ∈ F_K, volume (W i).carrier).toReal
          = ∑ i ∈ F_K, volume.real (W i).carrier
      exact ENNReal.toReal_sum (fun i _ => (W i).isCompact.measure_lt_top.ne)
    have h_density_le : (densityIn s W K_max).toReal ≤
        (μ : ℝ) * (Cengine * Cdim) ^ M * 4 ^ (n - 1) * (((2 : ℝ) ^ n) ^ 8 * Cvol / vU)
          * (∏ m, Δ m).toReal := by
      rw [h_densityIn_le_sum, div_le_iff₀ hK_max_vol_pos]
      linarith [h_sum_le_2]
    refine h_density_le.trans ?_
    apply mul_le_mul_of_nonneg_right _ hProd_Δ_nn
    have hCC_nn : (0 : ℝ) ≤ Cengine * Cdim := mul_nonneg hCengine_pos.le hCdim_pos.le
    have hCC_pow_nn : (0 : ℝ) ≤ (Cengine * Cdim) ^ M := pow_nonneg hCC_nn _
    have hS_ge_one : (1 : ℝ) ≤ max Kslack 1 := le_max_right _ _
    have hK_le_S : Kslack ≤ max Kslack 1 := le_max_left _ _
    have hS_le_pow : max Kslack 1 ≤ max Kslack 1 ^ M := by
      have hpow : max Kslack 1 ^ 1 ≤ max Kslack 1 ^ M :=
        pow_le_pow_right₀ hS_ge_one hM_pos
      simpa [pow_one] using hpow
    have hKslack_eq : ((2 : ℝ) ^ n) ^ 8 * Cvol / vU = Kslack := by rw [hKslack_def]
    have hμ_pow : (μ : ℝ) ≤ (μ : ℝ) ^ M := by
      have : (μ : ℝ) ^ 1 ≤ (μ : ℝ) ^ M :=
        pow_le_pow_right₀ (by exact_mod_cast hμ_pos) hM_pos
      simpa [pow_one] using this
    rw [hKslack_eq]
    have h_4pow_ge_one : (1 : ℝ) ≤ (4 : ℝ) ^ (n - 1) := by
      calc
        (1 : ℝ) = (4 : ℝ) ^ (0 : ℕ) := by norm_num
        _ ≤ (4 : ℝ) ^ (n - 1) := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (4 : ℝ)) (Nat.zero_le _)
    have h_4pow_pow : (4 : ℝ) ^ (n - 1) ≤ ((4 : ℝ) ^ (n - 1)) ^ M := by
      have hM_ge_one : 1 ≤ M := by omega
      have h_temp : ((4 : ℝ) ^ (n - 1)) ^ (1 : ℕ) ≤ ((4 : ℝ) ^ (n - 1)) ^ M :=
        pow_le_pow_right₀ h_4pow_ge_one hM_ge_one
      simpa [pow_one] using h_temp
    have hB_nonneg : 0 ≤ (μ : ℝ) * Cengine * Cdim * max Kslack 1 := by positivity
    have h_existing_calc : (μ : ℝ) * (Cengine * Cdim) ^ M * Kslack
        ≤ (μ : ℝ) ^ M * (Cengine * Cdim) ^ M * (max Kslack 1 ^ M) := by
      have h1 : (μ : ℝ) * (Cengine * Cdim) ^ M
          ≤ (μ : ℝ) ^ M * (Cengine * Cdim) ^ M :=
        mul_le_mul_of_nonneg_right hμ_pow hCC_pow_nn
      have h2 : Kslack ≤ max Kslack 1 ^ M := hK_le_S.trans hS_le_pow
      calc (μ : ℝ) * (Cengine * Cdim) ^ M * Kslack
          ≤ (μ : ℝ) ^ M * (Cengine * Cdim) ^ M * Kslack :=
            mul_le_mul_of_nonneg_right h1 hKslack_nn
        _ ≤ (μ : ℝ) ^ M * (Cengine * Cdim) ^ M * (max Kslack 1 ^ M) :=
            mul_le_mul_of_nonneg_left h2
              (mul_nonneg (pow_nonneg (by exact_mod_cast hμ_pos.le) _) hCC_pow_nn)
    calc (μ : ℝ) * (Cengine * Cdim) ^ M * ((4 : ℝ) ^ (n - 1)) * Kslack
        = ((μ : ℝ) * (Cengine * Cdim) ^ M * Kslack) * ((4 : ℝ) ^ (n - 1)) := by ring
      _ ≤ ((μ : ℝ) ^ M * (Cengine * Cdim) ^ M * (max Kslack 1 ^ M)) * ((4 : ℝ) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_right h_existing_calc (by positivity)
      _ = ((μ : ℝ) * Cengine * Cdim * max Kslack 1) ^ M * ((4 : ℝ) ^ (n - 1)) := by
        rw [mul_pow, mul_pow, mul_pow]; ring
      _ ≤ ((μ : ℝ) * Cengine * Cdim * max Kslack 1) ^ M * (((4 : ℝ) ^ (n - 1)) ^ M) :=
        mul_le_mul_of_nonneg_left h_4pow_pow (pow_nonneg hB_nonneg M)
      _ = (((μ : ℝ) * Cengine * Cdim * max Kslack 1) * ((4 : ℝ) ^ (n - 1))) ^ M := by
        rw [← mul_pow]
      _ = Cprod ^ M := by rw [hCprod_def]
  · rw [Finset.not_nonempty_iff_eq_empty] at hSmax_ne
    have hmax_zero : maxDensity s W = 0 :=
      maxDensity_eq_zero_of_maximizer_eq_empty hSmax_ne
    have h_eq_zero : densityIn s W K_max = 0 := by
      rw [hKmax_def, hSmax_def, densityIn_self_maximizer_eq, hmax_zero]
    rw [h_eq_zero]
    simp only [ENNReal.toReal_zero]
    have hProd_nn : (0 : ℝ) ≤ (∏ m, Δ m).toReal := ENNReal.toReal_nonneg
    have hC_nn : (0 : ℝ) ≤ Cprod ^ M := pow_nonneg hCprod_pos.le _
    exact mul_nonneg hC_nn hProd_nn

end Tube.ParentBodyDensity
