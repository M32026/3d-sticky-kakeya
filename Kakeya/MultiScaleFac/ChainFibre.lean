/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform.ParentBodyDensity
public import Kakeya.MultiScaleFac.ChainNode

/-!
# The fibre-anchored node chain

`Kakeya.MultiScaleFac.maxDensity_le_prod_of_grid_cuts_nodes` bounds the maximal density of the
*whole* family `𝕋` by a product over all gaps of the grid.  GWZ Lemma 7.7 needs instead the
maximal density of a single fibre `𝕋[i₀; σ₁]`, and it needs it without paying for the coarse
gaps: dividing by the anchor density `Δ(𝕋, T_{i₀}^{(σ₁)})` would otherwise leave the coarse
per-gap factors uncancelled, and those contain the coarse densities, which are not `δ^{-O(ε)}`.

The fix is small and is carried out here.  Run the same chain, but let the leaf family be the
fibre `s₁ = s_{δ∣σ₁}(i₀)` and let each level of the chain retain only the nodes carrying a leaf
of `s₁`.  Then the level-`1` node family consists of `σ₁`-nodes sharing a `δ`-tube with the
`σ₁`-tube `T_{i₀}^{(σ₁)}`, of which the bounded-overlap clause of the bundle allows at most `Cu²`
— the constant of the per-scale reading `ChainUniformTubeSet.uniformAt`.  The coarse gap
therefore carries the *constant* Katz–Tao data `Cu²` rather than a density, which is exactly the
collapse the cancellation needs; every finer gap keeps the node-reading hypothesis of
`maxDensity_le_prod_of_grid_cuts_nodes`.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **The fibre-anchored node-reading chain step of GWZ Lemma 7.7(A).**  Same hypotheses as
`maxDensity_le_prod_of_grid_cuts_nodes`, except that the Katz–Tao data is required only at the gaps
`m ≠ 0`, that the coarsest gap is given the constant datum `Cu² ≤ Δ 0`, and that the conclusion
bounds the maximal density of the *fibre* `𝕋[i₀; σ₁]` rather than of the whole family. -/
theorem maxDensity_fibre_le_prod_of_grid_cuts_nodes_uniform (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : ℕ) {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (σ : ℕ → NNReal), σ 0 = 1 → σ (J + 2) = δ → Antitone σ →
      (∀ m : Fin (J + 2), 16 * σ (m.succ : ℕ) ≤ σ (m.castSucc : ℕ)) →
      ∀ (𝒰 : ChainUniformTubeSet s T (J + 2) σ Cu),
      ∀ (Δ : Fin (J + 2) → ENNReal), (∀ m, Δ m ≠ ⊤) →
        ((Cu ^ 2 : NNReal) : ENNReal) ≤ Δ 0 →
      (∀ m : Fin (J + 2), m ≠ 0 → ∀ i₁ ∈ s,
          ConvexSpaceBody.IsKatzTao (gapNodeIndex 𝒰 (m.succ : ℕ) i₁ (5 * σ (m.castSucc : ℕ)))
            (fun j => (𝒰.cover.tube (m.succ : ℕ) j).toConvexSpaceBody) (Δ m)) →
      ∀ i₀ ∈ s,
      maxDensity (fibreIndex s T δ (σ 1) i₀) (fun i => (T i).toConvexSpaceBody)
        ≤ ENNReal.ofReal C ^ (J + 2)
            * (((Cu ^ 2 : NNReal) : ENNReal) * (𝒰.branchingN (J + 2) : ENNReal))
            * ∏ m, Δ m := by
  have hCu_pos : 0 < Cu := zero_lt_one.trans_le hCu
  obtain ⟨C₀, hC₀, h74⟩ :=
    Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales (E := E) 6
      (by norm_num) ((Cu ^ 2 : NNReal) : ℝ) (NNReal.coe_pos.mpr (pow_pos hCu_pos 2))
  set Kc := katzTaoRescaleConst E with hKc_def
  have hKc_pos : 0 < (Kc : ℝ) := NNReal.coe_pos.mpr katzTaoRescaleConst_pos
  obtain ⟨A, hApos, hleafFibre⟩ := exists_isKatzTao_leaf_fibre (E := E)
  have hApos' : 0 < (A : ℝ) := NNReal.coe_pos.mpr hApos
  let C := C₀ * ((A : ℝ) + 1) * ((Kc : ℝ) + 1)
  have hC_pos : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC_pos, ?_⟩
  intro J
  set M := J + 2 with hM_def
  have hM : 0 < M := by omega
  intro ι δ hδ hδ1 s T hball σ hσ0 hσlast hanti hgap 𝒰 Δ hΔ hCuΔ0 hKT i₀ hi₀
  classical
  let u : ∀ k : Fin (M + 1), Tube.IsUniformAtScale s T (σ (k : ℕ)) (Cu ^ 2) :=
    fun k => 𝒰.uniformAt hCu (Nat.lt_succ_iff.mp k.isLt)
  have hval1 : ((1 : Fin (M + 1)) : ℕ) = 1 := by simp [hM_def]
  set s₁ := fibreIndex s T δ (σ 1) i₀ with hs₁_def
  have hs₁_eq : s₁ = s.filter (fun i =>
      (T i).toConvexSpaceBody ≤ ((T i₀).rescale (σ 1)).toConvexSpaceBody) := by
    rw [hs₁_def, fibreIndex_self s T (σ 1) i₀]
  have hs₁_mem : ∀ i ∈ s₁, i ∈ s ∧
      (T i).toConvexSpaceBody ≤ ((T i₀).rescale (σ 1)).toConvexSpaceBody := by
    rw [hs₁_eq]; exact fun i hi => Finset.mem_filter.mp hi
  have hs₁_sub : s₁ ⊆ s := fun i hi => (hs₁_mem i hi).1
  have hi₀s₁ : i₀ ∈ s₁ := by
    rw [hs₁_eq]
    exact Finset.mem_filter.mpr
      ⟨hi₀, Tube.le_rescale (T i₀) (by rw [← hσlast]; exact hanti (by omega))⟩
  have hs : s.Nonempty := ⟨i₀, hi₀⟩
  have hδσ : ∀ k : Fin (M + 1), (δ : NNReal) ≤ σ (k : ℕ) := fun k => by
    rw [← hσlast]; exact hanti (Nat.lt_succ_iff.mp k.isLt)
  have hσpos : ∀ k : Fin (M + 1), 0 < σ (k : ℕ) := fun k => hδ.trans_le (hδσ k)
  have hσle1 : ∀ k : Fin (M + 1), σ (k : ℕ) ≤ 1 := fun k =>
    (hanti (Nat.zero_le _)).trans hσ0.le
  have hδhalf : (δ : ℝ) ≤ 1/2 := by
    let m₀' : Fin (J + 2) := ⟨J + 1, by omega⟩
    have hm_succ_last : ((m₀'.succ : Fin (M + 1)) : ℕ) = M := by
      simp only [Fin.val_succ, m₀', hM_def]
    have h16 : (16 : NNReal) * δ ≤ 1 := by
      have h := (hgap m₀').trans (hσle1 m₀'.castSucc)
      rwa [hm_succ_last, hσlast] at h
    linarith [show (16 : ℝ) * (δ : ℝ) ≤ 1 by exact_mod_cast h16]
  have hball6 : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 6 := fun i hi =>
    (hball i hi).trans (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 6))
  have hball6_s₁ : ∀ i ∈ s₁, (T i).carrier ⊆ Metric.closedBall (0 : E) 6 :=
    fun i hi => hball6 i (hs₁_sub hi)
  obtain ⟨ρ, hρ0ge, hρ0le, hρlast, hρanti, hρgap, hρle2, hσleρ, hρle2σ, hρle1, hslack⟩ :=
    exists_inflated_scales_node hM hδ (fun k : Fin (M + 1) => σ (k : ℕ))
      (by simpa only [Fin.val_zero] using hσ0) (by simpa only [Fin.val_last] using hσlast)
      (fun a b hab => hanti (Fin.le_def.mp hab)) (fun m => hgap m)
  have hpar_ex : ∀ (k : Fin (M + 1)) (i : ι), ∃ j,
      i ∈ s → (j ∈ (u k).parent ∧
        (T i).toConvexSpaceBody ≤ ((u k).parentTube j).toConvexSpaceBody) := by
    intro k i
    by_cases hi : i ∈ s
    · obtain ⟨j, hj, hle⟩ := (u k).exists_le_rescale hi; exact ⟨j, fun _ => ⟨hj, hle⟩⟩
    · exact ⟨i, fun hi' => (hi hi').elim⟩
  choose par hpar using hpar_ex
  let m₀ : Fin M := ⟨M - 1, by omega⟩
  have hlast_iff : ∀ m : Fin M, m.succ = Fin.last M ↔ m = m₀ := by
    intro m
    simp only [Fin.ext_iff, Fin.val_succ, Fin.val_last, m₀]
    omega
  have hcs_ne : ∀ m : Fin M, m.castSucc ≠ Fin.last M := Fin.castSucc_ne_last
  let tb : ∀ k : Fin (M + 1), ι → Tube (ρ k) E := fun k j =>
    if k = Fin.last M then (T j).rescale (ρ k) else ((u k).parentTube j).rescale (ρ k)
  let Q : ∀ _ : Fin (M + 1), Finset ι := fun k =>
    if k = Fin.last M then s₁
    else (u k).parent.filter
      (fun j => ∃ i ∈ s₁, (T i).toConvexSpaceBody ≤ ((u k).parentTube j).toConvexSpaceBody)
  have hQlast : Q (Fin.last M) = s₁ := by dsimp only [Q]; rw [if_pos rfl]
  have hQcs : ∀ m : Fin M, Q m.castSucc =
      (u m.castSucc).parent.filter (fun j => ∃ i ∈ s₁,
        (T i).toConvexSpaceBody ≤ ((u m.castSucc).parentTube j).toConvexSpaceBody) := by
    intro m
    dsimp only [Q]; rw [if_neg (hcs_ne m)]
  have hleaf_ex : ∀ (k : Fin (M + 1)) (j : ι), ∃ i : ι,
      (∃ i' ∈ s₁, (T i').toConvexSpaceBody ≤ ((u k).parentTube j).toConvexSpaceBody) →
        (i ∈ s₁ ∧ (T i).toConvexSpaceBody ≤ ((u k).parentTube j).toConvexSpaceBody) := by
    intro k j
    by_cases hj : ∃ i' ∈ s₁, (T i').toConvexSpaceBody ≤ ((u k).parentTube j).toConvexSpaceBody
    · obtain ⟨i, hi, hle⟩ := hj; exact ⟨i, fun _ => ⟨hi, hle⟩⟩
    · exact ⟨j, fun hc => absurd hc hj⟩
  choose leaf hleaf using hleaf_ex
  let lf : ∀ k : Fin (M + 1), ι → ι := fun k w =>
    if k = Fin.last M then w else leaf k w
  have hlf_spec : ∀ (k : Fin (M + 1)) (w : ι), w ∈ Q k → lf k w ∈ s₁ ∧
      (k ≠ Fin.last M →
        (T (lf k w)).toConvexSpaceBody ≤ ((u k).parentTube w).toConvexSpaceBody) := by
    intro k w hw
    dsimp only [Q] at hw
    by_cases hk : k = Fin.last M
    · subst hk
      rw [if_pos rfl] at hw
      dsimp only [lf]; rw [if_pos rfl]
      exact ⟨hw, fun h => absurd rfl h⟩
    · rw [if_neg hk, Finset.mem_filter] at hw
      obtain ⟨hi_s, hi_le⟩ := hleaf k w hw.2
      dsimp only [lf]; rw [if_neg hk]
      exact ⟨hi_s, fun _ => hi_le⟩
  let proj : ∀ _ : Fin M, ι → ι := fun m w =>
    par m.castSucc (lf m.succ w)
  let cover : ι → ι := id
  let Δ' : Fin M → ENNReal := fun m =>
    (if m = m₀ then (A : ENNReal) * ((Cu ^ 2 : NNReal) : ENNReal) * (𝒰.branchingN M : ENNReal)
     else (Kc : ENNReal)) * Δ m
  have hproj_mem : ∀ m : Fin M, ∀ w ∈ Q m.succ, proj m w ∈ Q m.castSucc := by
    intro m w hw
    have hlf_w_s₁ : lf m.succ w ∈ s₁ := (hlf_spec m.succ w hw).1
    have hpar_spec := hpar m.castSucc (lf m.succ w) (hs₁_sub hlf_w_s₁)
    rw [hQcs m]
    exact Finset.mem_filter.mpr ⟨hpar_spec.1, lf m.succ w, hlf_w_s₁, hpar_spec.2⟩
  have hchain : ∀ m : Fin M, ∀ w ∈ Q m.succ,
      (tb m.succ w).toConvexSpaceBody ≤ (tb m.castSucc (proj m w)).toConvexSpaceBody := by
    intro m w hw
    have hpar_body : (T (lf m.succ w)).toConvexSpaceBody ≤
        ((u m.castSucc).parentTube (proj m w)).toConvexSpaceBody :=
      (hpar m.castSucc (lf m.succ w) (hs₁_sub (hlf_spec m.succ w hw).1)).2
    have htbcs : tb m.castSucc (proj m w)
        = ((u m.castSucc).parentTube (proj m w)).rescale (ρ m.castSucc) := by
      dsimp only [tb]; rw [if_neg (hcs_ne m)]
    by_cases hk : m.succ = Fin.last M
    · have hlfw : lf m.succ w = w := by dsimp only [lf]; rw [if_pos hk]
      rw [show tb m.succ w = (T (lf m.succ w)).rescale (ρ m.succ) by
        dsimp only [tb]; rw [if_pos hk, hlfw], htbcs]
      exact Tube.rescale_le_rescale_of_body_le (T (lf m.succ w))
        ((u m.castSucc).parentTube (proj m w)) (le_trans (hδσ m.succ) (hσleρ m.succ))
        ((add_le_add_left le_self_add _).trans (hslack m)) hpar_body
    · rw [show tb m.succ w = ((u m.succ).parentTube w).rescale (ρ m.succ) by
        dsimp only [tb]; rw [if_neg hk], htbcs]
      exact node_rescale_le_node_rescale_of_shared_tube ((u m.castSucc).parentTube (proj m w))
        ((u m.succ).parentTube w) (T (lf m.succ w))
        ((hδσ m.succ).trans (le_mul_of_one_le_left' (by norm_num))) (hσleρ m.succ) (hslack m)
        ((hlf_spec m.succ w hw).2 hk) hpar_body
  have hcard0_bound : ((Q 0).card : ℝ)
      ≤ ((Cu ^ 2 : NNReal) : ℝ) * (6 + 3) ^ (2 * Module.finrank ℝ E) := by
    have hQ0 : Q 0 ⊆ (u 0).parent.filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ ((u 0).parentTube j).toConvexSpaceBody) := by
      dsimp only [Q]
      rw [if_neg (show (0 : Fin (M + 1)) ≠ Fin.last M by
        simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega)]
      intro j hj
      obtain ⟨hj_parent, i, hi_s₁, hi_le⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hj_parent, i, hs₁_sub hi_s₁, hi_le⟩
    rw [show (6 + 3 : ℝ) = 9 by norm_num]
    exact le_trans (Nat.cast_le.mpr (Finset.card_le_card hQ0))
      (card_parent_with_leaf_le hδhalf hs hball 𝒰 hCu
        (show ((0 : Fin (M + 1)) : ℕ) ≤ M by simp) (by simpa only [Fin.val_zero] using hσ0))
  have hball_chain : ∀ k : Fin (M + 1), ∀ t ∈ Q k,
      (tb k t).carrier ⊆ Metric.closedBall (0 : E) (6 + 3) := by
    intro k t ht
    rw [show (6 + 3 : ℝ) = 9 by norm_num]
    by_cases hk : k = Fin.last M
    · have ht_s₁ : t ∈ s₁ := by
        rw [hk] at ht; rwa [hQlast] at ht
      rw [show tb k t = (T t).rescale (ρ k) by dsimp only [tb]; rw [if_pos hk]]
      exact leaf_rescale_carrier_subset_closedBall (T t) (hball t (hs₁_sub ht_s₁))
        (le_trans (NNReal.coe_le_coe.mpr (hρle2 k)) (by norm_num))
    · rw [show tb k t = ((u k).parentTube t).rescale (ρ k) by dsimp only [tb]; rw [if_neg hk]]
      exact node_rescale_carrier_subset_closedBall ((u k).parentTube t) (T (lf k t))
        (hball _ (hs₁_sub (hlf_spec k t ht).1)) ((hlf_spec k t ht).2 hk) (hσleρ k)
        (by exact_mod_cast hσle1 k) (by exact_mod_cast hρle2 k)
  have hQnonempty : ∀ m : Fin M, (Q m.castSucc).Nonempty := by
    intro m
    have hpar_spec := hpar m.castSucc i₀ hi₀
    rw [hQcs m]
    exact ⟨par m.castSucc i₀, Finset.mem_filter.mpr ⟨hpar_spec.1, i₀, hi₀s₁, hpar_spec.2⟩⟩
  have hcover_mem : ∀ i ∈ s₁, cover i ∈ Q (Fin.last M) := by
    intro i hi; rw [hQlast]; exact hi
  have hcover_body : ∀ i ∈ s₁, (T i).toConvexSpaceBody ≤
      (tb (Fin.last M) (cover i)).toConvexSpaceBody := by
    intro i hi
    rw [show tb (Fin.last M) (cover i) = (T i).rescale (ρ (Fin.last M)) by
      dsimp only [tb, cover, id_eq]; rw [if_pos rfl]]
    exact Tube.le_rescale (T i) (by rw [hρlast])
  have hcover_inj : Set.InjOn cover (↑s₁ : Set ι) := Set.injOn_id _
  have hΔ'_ne_top : ∀ m : Fin M, Δ' m ≠ ⊤ := fun m => by
    dsimp only [Δ']
    refine ENNReal.mul_ne_top ?_ (hΔ m)
    split
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
        ENNReal.coe_ne_top
    · exact ENNReal.coe_ne_top
  have hvol_pos : 0 < volume ((T i₀).carrier) :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos (Module.finrank ℝ E))
      (pow_pos hδ (Module.finrank ℝ E - 1)))) (by simpa using Tube.le_volume (T i₀))
  have hvol_fin : volume ((T i₀).carrier) ≠ ⊤ := (T i₀).toConvexSpaceBody.3.measure_ne_top
  have hKc_ge_one : (1 : ENNReal) ≤ (Kc : ENNReal) := by
    have h_temp : (1 : ENNReal) * volume ((T i₀).carrier)
        ≤ (Kc : ENNReal) * volume ((T i₀).carrier) := by
      simpa only [one_mul] using
        Kakeya.MultiScaleFac.volume_tube_le_mul_volume_tube hδ1 (T i₀) (T i₀)
    simpa using (ENNReal.mul_le_mul_iff_left hvol_pos.ne' hvol_fin).mp h_temp
  have hKT_chain : ∀ m : Fin M, ∀ p ∈ Q m.castSucc,
      ConvexSpaceBody.IsKatzTao ((Q m.succ).filter (fun w => proj m w = p))
        (fun w => (tb m.succ w).toConvexSpaceBody) (Δ' m) := by
    intro m p hp
    set Fw := (Q m.succ).filter (fun w => proj m w = p)
    have hℓp_s₁ : lf m.castSucc p ∈ s₁ := (hlf_spec m.castSucc p hp).1
    have hℓp_s : lf m.castSucc p ∈ s := hs₁_sub hℓp_s₁
    have hℓp_body : (T (lf m.castSucc p)).toConvexSpaceBody ≤
        ((u m.castSucc).parentTube p).toConvexSpaceBody :=
      (hlf_spec m.castSucc p hp).2 (hcs_ne m)
    have hkey : ∀ w ∈ Fw, (T (lf m.succ w)).toConvexSpaceBody ≤
        ((u m.castSucc).parentTube p).toConvexSpaceBody := by
      intro w hw
      have hlf_ws₁ : lf m.succ w ∈ s₁ := (hlf_spec m.succ w (Finset.mem_filter.mp hw).1).1
      have hres := (hpar m.castSucc (lf m.succ w) (hs₁_sub hlf_ws₁)).2
      rwa [show par m.castSucc (lf m.succ w) = p from (Finset.mem_filter.mp hw).2] at hres
    have h45 : 4 * σ (m.castSucc : ℕ) + 4 * σ (m.succ : ℕ) ≤ 5 * σ (m.castSucc : ℕ) := by
      have h4 : 4 * σ (m.succ : ℕ) ≤ σ (m.castSucc : ℕ) :=
        (mul_le_mul_left (by norm_num : (4 : NNReal) ≤ 16) _).trans (hgap m)
      exact (add_le_add_right h4 _).trans_eq (by ring)
    by_cases hk : m.succ = Fin.last M
    · have hm_eq_m₀ : m = m₀ := (hlast_iff m).mp hk
      have hΔ'eq : Δ' m
          = (A : ENNReal) * ((Cu ^ 2 : NNReal) : ENNReal) * (𝒰.branchingN M : ENNReal) * Δ m := by
        dsimp only [Δ']; rw [if_pos hm_eq_m₀]
      have hm_ne_zero : m ≠ 0 := by
        rw [hm_eq_m₀]; simp only [ne_eq, Fin.ext_iff, Fin.val_zero, m₀]; omega
      have hFws : Fw ⊆ s := fun w hw => by
        have hwQ : w ∈ Q m.succ := (Finset.mem_filter.mp hw).1
        rw [hk, hQlast] at hwQ; exact hs₁_sub hwQ
      have hKT_clean : ConvexSpaceBody.IsKatzTao
          (gapNodeIndex 𝒰 M (lf m.castSucc p) (5 * σ (m.castSucc : ℕ)))
          (fun j => (𝒰.cover.tube M j).toConvexSpaceBody) (Δ m) := by
        have htemp := hKT m hm_ne_zero (lf m.castSucc p) hℓp_s
        rw [hk] at htemp; simpa only [Fin.val_last] using htemp
      have hfib_goal : ∀ w ∈ Fw,
          (T w).toConvexSpaceBody ≤ ((u m.castSucc).parentTube p).toConvexSpaceBody := by
        intro w hw
        have h1 := hkey w hw
        rwa [show lf m.succ w = w by dsimp only [lf]; rw [if_pos hk]] at h1
      have h_body_eq : (fun w => (tb m.succ w).toConvexSpaceBody)
          = (fun w => (T w).toConvexSpaceBody) := by
        have hρ_succ : ρ m.succ = δ := by rw [hk, hρlast]
        funext w
        rw [show tb m.succ w = (T w).rescale (ρ m.succ) by dsimp only [tb]; rw [if_pos hk],
          hρ_succ, Tube.toConvexSpaceBody_rescale_self]
      rw [h_body_eq, hΔ'eq]
      exact hleafFibre (ι := ι) (N := M) (σ := σ) (ka := (m.castSucc : ℕ)) (kl := M) (δ := δ)
        hδ hδ1 le_rfl hσlast (s := s) (T := T) (Cu := Cu) 𝒰 hCu
        (by rw [show σ M = σ (m.succ : ℕ) by rw [hk, Fin.val_last]]; exact h45)
        (Δ := Δ m) (p := p) (ℓp := lf m.castSucc p) hℓp_body
        hKT_clean Fw hFws hfib_goal
    · by_cases hm0 : m = 0
      · subst hm0
        have hΔ'eq : Δ' (0 : Fin M) = (Kc : ENNReal) * Δ (0 : Fin M) := by
          dsimp only [Δ']
          rw [if_neg (show (0 : Fin M) ≠ m₀ by
            simp only [ne_eq, Fin.ext_iff, Fin.val_zero, m₀]; omega)]
        have hsucc_zero_eq_one : (0 : Fin M).succ = (1 : Fin (M + 1)) := by apply Fin.ext; simp
        have hFw_sub_Q1 : Fw ⊆ Q ((0 : Fin M).succ) := Finset.filter_subset _ _
        have hQ1_eq : Q (1 : Fin (M + 1)) =
            (u 1).parent.filter (fun j => ∃ i ∈ s₁,
              (T i).toConvexSpaceBody ≤ ((u 1).parentTube j).toConvexSpaceBody) := by
          dsimp only [Q]
          rw [if_neg (show (1 : Fin (M + 1)) ≠ Fin.last M by
            simp only [ne_eq, Fin.ext_iff, hval1, Fin.val_last]; omega)]
        have hQ1_card_bound_ENNReal : ((Q (1 : Fin (M + 1))).card : ENNReal)
            ≤ ((Cu ^ 2 : NNReal) : ENNReal) := by
          have h_sub : Q (1 : Fin (M + 1)) ⊆ ((u 1).parent).filter (fun j => ∃ i ∈ s,
              (T i).toConvexSpaceBody ≤ ((u 1).parentTube j).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody
                ≤ ((T i₀).rescale (σ (((1 : Fin (M + 1)) : ℕ)))).toConvexSpaceBody) := by
            rw [hQ1_eq]
            intro j hj
            obtain ⟨hj_parent, i, hi_s₁, hi_le⟩ := Finset.mem_filter.mp hj
            obtain ⟨hi_s, hi_body⟩ := hs₁_mem i hi_s₁
            exact Finset.mem_filter.mpr ⟨hj_parent, i, hi_s, hi_le, by rwa [hval1]⟩
          refine le_trans (Nat.cast_le.mpr (Finset.card_le_card h_sub)) ?_
          exact_mod_cast (u 1).boundedOverlap ((T i₀).rescale (σ (((1 : Fin (M + 1)) : ℕ))))
        rw [ConvexSpaceBody.IsKatzTao_def, hΔ'eq]
        calc
          maxDensity Fw (fun w => (tb ((0 : Fin M).succ) w).toConvexSpaceBody)
              ≤ (Fw.card : ENNReal) := maxDensity_le_card _ _
          _ ≤ ((Q (1 : Fin (M + 1))).card : ENNReal) := by
            rw [← hsucc_zero_eq_one]
            exact Nat.cast_le.mpr (Finset.card_le_card hFw_sub_Q1)
          _ ≤ ((Cu ^ 2 : NNReal) : ENNReal) := hQ1_card_bound_ENNReal
          _ ≤ Δ (0 : Fin M) := hCuΔ0
          _ ≤ (Kc : ENNReal) * Δ (0 : Fin M) := le_mul_of_one_le_left' hKc_ge_one
      · have hm_ne_zero : m ≠ 0 := hm0
        have hΔ'eq : Δ' m = (Kc : ENNReal) * Δ m := by
          dsimp only [Δ']
          rw [if_neg (fun h : m = m₀ => hk ((hlast_iff m).mpr h))]
        have hFwsub : Fw ⊆ (u m.succ).parent := fun w hw => by
          have hwQ : w ∈ Q m.succ := (Finset.mem_filter.mp hw).1
          dsimp only [Q] at hwQ
          rw [if_neg hk, Finset.mem_filter] at hwQ
          exact hwQ.1
        have hδb : (δ : NNReal) ≤ 4 * σ (m.succ : ℕ) :=
          (hδσ m.succ).trans (le_mul_of_one_le_left' (by norm_num))
        have hfib : ∀ w ∈ Fw, ∃ i,
            (T i).toConvexSpaceBody ≤ ((u m.succ).parentTube w).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ ((u m.castSucc).parentTube p).toConvexSpaceBody :=
          fun w hw => ⟨lf m.succ w,
            (hlf_spec m.succ w (Finset.mem_filter.mp hw).1).2 hk, hkey w hw⟩
        have hres := isKatzTao_node_fibre 𝒰 (ka := (m.castSucc : ℕ)) (kb := (m.succ : ℕ))
          (hσpos m.succ) (hσleρ m.succ) (hρle2σ m) (hρle1 m) hδb h45 hℓp_body
          (hKT m hm_ne_zero (lf m.castSucc p) hℓp_s) Fw hFwsub hfib
        have htb_simp : (fun w : ι => (tb m.succ w).toConvexSpaceBody) =
            (fun w : ι => (((u m.succ).parentTube w).rescale (ρ m.succ)).toConvexSpaceBody) := by
          funext w; dsimp only [tb]; rw [if_neg hk]
        rw [htb_simp, hΔ'eq]
        exact hres
  have hchain_result : maxDensity s₁ (fun i => (T i).toConvexSpaceBody) ≤
      ENNReal.ofReal C₀ ^ M * (∏ m : Fin M, Δ' m) :=
    h74 hδ hδ1 s₁ T hball6_s₁ M hM ρ hρ0ge hρ0le hρlast hρanti hρgap
      (κ := fun _ => ι) (tb := tb) (Q := Q) (proj := proj)
      hproj_mem hchain hcard0_bound hball_chain hQnonempty cover hcover_mem hcover_body
      hcover_inj Δ' hΔ'_ne_top hKT_chain
  have hRHS_le : ENNReal.ofReal C₀ ^ M * (∏ m : Fin M, Δ' m) ≤
      ENNReal.ofReal C ^ M * (((Cu ^ 2 : NNReal) : ENNReal) * (𝒰.branchingN M : ENNReal))
        * ∏ m : Fin M, Δ m := by
    rw [show (∏ m : Fin M, Δ' m) = ((A : ENNReal) * ((Cu ^ 2 : NNReal) : ENNReal)
        * (𝒰.branchingN M : ENNReal)) * (Kc : ENNReal) ^ (M - 1) * (∏ m : Fin M, Δ m) from
      prod_ite_succ_last_mul m₀ (Kc : ENNReal) _ Δ]
    exact chain_const_arith hM hC₀ A Kc (Cu ^ 2) (𝒰.branchingN M) (∏ m, Δ m)
  exact hchain_result.trans hRHS_le

end MultiScaleFac

end Kakeya
