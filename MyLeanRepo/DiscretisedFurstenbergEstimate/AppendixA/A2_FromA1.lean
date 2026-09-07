module

/-
  A2_FromA1: Construct A2_SquareData from A1_Output.

  Provides two entry points:
  - `a2_square_data_from_a1`: low-level, takes explicit per-square S-set
  - `a2_square_data_from_a1_auto`: convenience wrapper that derives the
    per-square S-set from A1's global P_all using density-aware restriction.

  The auto wrapper consumes `per_square_sset_from_a1` (which uses the heavy-square
  cardinality lower bound `a1.h_points_card_lower`) and `absorb_C_P_times_81`.

  Obtain A + hQTTC + hA_one from `qttc_typed_parentCell`:
  ```
  rcases qttc_typed_parentCell s hs_pos (show s < 2 from by linarith)
    with ⟨A, hA_one, hQTTC⟩
  ```

  `K_pack` must equal `a1.K_pack`; standard value is
  `MainAppendix.affineLine_packing_constant + 1`.

  Whiteprint node: a2_from_a1
  Dependencies: A2_PerSquare, TDeltaGlobalConstruction, Interfaces, SSetRestriction
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_PerSquare
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TDeltaGlobalConstruction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.PerSquareSSetFromA1
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon
open DirecretisedFurstenbergEstimate.AppendixA.A2
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
open DirecretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly
open DirecretisedFurstenbergEstimate.QTTC_Assembly
open DirecretisedFurstenbergEstimate.AppendixA.TDeltaGlobal

/-- Transport `A2_Smallness` across the phantom exponent parameter.

    The `t` (or `u`) parameter in `A2_Smallness` does not appear in any field;
    all numerical conditions depend only on `Δ, δ, s, ε, A, K_pack, M`.
    Therefore a package proved for one exponent can be reused for any other. -/
lemma A2_Smallness.transport {Δ δ s t u ε A K M : ℝ}
    (h : A2_Smallness Δ δ s t ε A K M) :
    A2_Smallness Δ δ s u ε A K M :=
  ⟨h.hΔ_pos, h.hΔ_lt_half, h.hδ_le_Δ, h.hA_pos,
   h.hK_loss, h.hK_loss_strong, h.hC2_loss, h.hstrip_loss,
   h.hKpack_loss, h.hKpack_loss_strong, h.hM_large, h.hM_upper,
   h.hKpack_const_ge1, h.hslope_sset_const, h.hcover_lower_pack⟩

/-- Construct `A2_SquareData` for a square Q from `A1_Output`.

    Takes explicit selected `A`, `hA_one` (1 ≤ A), `hQTTC` (for that A),
    and `h_small` (matching smallness package). Obtain A + hA_one + hQTTC
    from `qttc_typed_parentCell`:
    ```
    rcases qttc_typed_parentCell s hs_pos (show s < 2 from by linarith)
      with ⟨A, hA_one, hQTTC⟩
    ```

    `K_pack` must equal `a1.K_pack`; standard value is
    `MainAppendix.affineLine_packing_constant + 1`.

    `h_small` is accepted for any exponent `u` (the exponent is phantom in
    `A2_Smallness`) and transported to `t` internally via `A2_Smallness.transport`.

    The `h_prove_sub` argument is constructed using
    `qttc_C_sub_T_Delta_global`. -/
def a2_square_data_from_a1
    {Δ δ s t u ε : ℝ}
    {n m0 : ℕ}
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_eq : Δ = dyadicDelta m0)
    (hnm : m0 ≤ n)
    (hm_pos : 1 ≤ m0)
    (a1 : A1_Output Δ δ t s ε)
    (Q : CoarseSquare Δ)
    (hQ : Q ∈ a1.Qset)
    (K_pack : ℝ)
    (hK_pack_eq : a1.K_pack = K_pack)
    (A : ℝ)
    (hA_one : 1 ≤ A)
    (hQTTC : ∀ {n m : ℕ} {δ Δ C₁ : ℝ} {M : ℕ}
      {P : Finset Plane} {T : Plane → Finset AffineLine},
      (hδ_eq : δ = dyadicDelta n) →
      (hΔ_eq : Δ = dyadicDelta m) →
      (hnm : m ≤ n) → (hm_pos : 1 ≤ m) →
      1 ≤ C₁ → P.Nonempty → 0 < M →
      (∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M) →
      (∀ p ∈ P, _root_.BallGrowth δ s C₁ (T p)) →
      (∀ p ∈ P, SeparatedAt (δ / 2) ((T p) : Set AffineLine)) →
      (∀ p ∈ P, ∀ ℓ ∈ T p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3) →
      (R : ℝ) → (hR : R ≤ Real.sqrt 2) →
      (∀ p ∈ P, |p 1| ≤ R) →
      (hδ_le_quarter_Delta : δ ≤ Δ / 4) →
      (∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1) →
      ∃ (P' : Finset Plane) (T' : Plane → Finset AffineLine)
        (C' : Finset AffineLine) (K C₂ : ℝ) (H : ℕ),
        1 ≤ K ∧ K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
        1 ≤ C₂ ∧ 0 < H ∧
        P' ⊆ P ∧
        (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
        (∀ p ∈ P', T' p ⊆ T p) ∧
        (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
        _root_.IsFiniteDeltaSSet Δ s C₂ C' ∧
        IsDeltaSSet Δ s (max 1 (C_PACK * C₂)) (C' : Set AffineLine) ∧
        C₂ ≤ A * Real.rpow K A * C₁ ∧
        (∀ c ∈ C', |tubeSlope c| ≤ 1) ∧
        (∀ c ∈ C', (LemmaE.getDirV c) 1 ≠ 0) ∧
        (∀ c ∈ C', |tubeIntercept c| ≤ 3) ∧
        (∀ c ∈ C', ∃ p ∈ P', |tubeIntercept c - (p 0 - tubeSlope c * p 1)| ≤ 4 * Δ) ∧
        (∀ c ∈ C', ∃ (p : Plane) (hp : p ∈ P') (ell : AffineLine)
          (hell : ell ∈ T' p) (U : DyadicTube m),
          sp hnm (snapTube n ell) = U ∧ c = dyadicTubeToA2 U) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ c ∈ C',
          (H : ℝ) ≤ ∑ p ∈ P', (pointFiber Δ hΔ_pos T' p c).card) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ p ∈ P', ∀ c ∈ C',
          (pointFiber Δ hΔ_pos T' p c).card ≤
            C₁ * (6 : ℝ)^s * (T p).card * Δ^s) ∧
        (M : ℝ) * (P.card : ℝ) ≤ K * (H : ℝ) * (C'.card : ℝ) ∧
        (H : ℝ) * (C'.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ))
    (h_small : A2_Smallness Δ δ s u ε A K_pack a1.M)
    (hs_pos : 0 < s)
    (hs_lt_one : s < 1)
    -- Point S-set for this square
    (C_P : ℝ)
    (hP_sset : IsDeltaSSet δ t C_P (a1.points Q hQ : Set Plane))
    (hC_P_bound : C_P * 81 ≤ Real.rpow Δ (-t - 8 * ε))
    -- Source tube family and inclusion
    (T_source : Finset FineTube)
    (hT_sub_source : ∀ p ∈ a1.points Q hQ, a1.tubes p ⊆ T_source)
    -- Global coarse cover
    (T_Delta_global : Finset CoarseTube)
    (hT_Delta_global_eq : T_Delta_global = TDeltaGlobal.T_Delta_global hnm T_source)
    -- Geometry
    (hδ_le_quarter_Delta : δ ≤ Δ / 4)
    (hδ_pos : 0 < δ) :
    A2_SquareData Δ δ s t ε Q := by
  let P := a1.points Q hQ
  let T := a1.tubes
  let M := a1.M

  -- Transport smallness package from exponent u to t (exponent is phantom)
  let h_small_t : A2_Smallness Δ δ s t ε A K_pack a1.M :=
    A2_Smallness.transport h_small

  have hP_nonempty : P.Nonempty := by
    have h1 : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ) := a1.h_points_card_lower Q hQ
    have h2 : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos h_small_t.hΔ_pos _
    have h3 : 0 < (P.card : ℝ) := by linarith
    have h4 : 0 < P.card := by exact_mod_cast h3
    exact Finset.card_pos.mp h4

  have hP_in_square : (P : Set Plane) ⊆ squareSet Δ Q :=
    fun p hp => a1.h_points_in_square Q hQ p hp

  let R : ℝ := Real.sqrt 2
  have hR : R ≤ Real.sqrt 2 := le_refl R

  have hP_in_ball : (P : Set Plane) ⊆ Metric.closedBall 0 R :=
    a1.h_points_in_ball Q hQ

  have hP_separated : SeparatedAt δ (P : Set Plane) :=
    a1.h_separated Q hQ

  have hP_card_lower : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ) :=
    a1.h_points_card_lower Q hQ

  have hP_card_lower_strong : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ) :=
    a1.h_points_card_lower_strong Q hQ

  have hP_card_upper : (P.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) :=
    a1.h_points_card_upper Q hQ

  have hM_pos : 0 < M := a1.hM_pos
  have hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack := by
    have h1 : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / a1.K_pack := a1.hM_lower
    rw [hK_pack_eq] at h1
    exact h1
  have hM_upper : M ≤ 2 * Real.rpow Δ (-2 * s - ε) := a1.hM_upper

  have h_tubes_card : ∀ p ∈ P, (M / 2 : ℝ) ≤ (T p).card ∧ (T p).card ≤ M :=
    fun p hp => a1.h_tubes_card Q hQ p hp

  have h_tubes_sset : ∀ p ∈ P,
      IsDeltaSSet δ s (max 1 (K_pack * Real.rpow δ (-ε))) (T p : Set FineTube) := by
    intro p hp
    have h1 : IsDeltaSSet δ s (max 1 (a1.K_pack * Real.rpow δ (-ε))) (T p : Set FineTube) :=
      a1.h_tubes_sset Q hQ p hp
    rw [hK_pack_eq] at h1
    exact h1

  have h_tubes_separated : ∀ p ∈ P, SeparatedAt (δ / 2) (T p : Set FineTube) :=
    fun p hp => a1.h_tubes_separated Q hQ p hp

  have h_slope_bound : ∀ p ∈ P, ∀ ℓ ∈ T p,
      (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3 :=
    fun p hp ℓ hℓ => a1.h_slope_bound Q hQ p hp ℓ hℓ

  have h_inc : ∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1 :=
    fun p hp ℓ hℓ => a1.h_inc Q hQ p hp ℓ hℓ

  have hs1 : s < 1 := hs_lt_one

  -- Construct h_prove_sub using TDeltaGlobalConstruction
  let h_prove_sub : ∀ (P' : Finset Plane) (T' : Plane → Finset AffineLine) (C' : Finset AffineLine),
      P' ⊆ P →
      (∀ p ∈ P', T' p ⊆ T p) →
      (∀ c ∈ C', ∃ (p : Plane) (hp : p ∈ P') (ell : AffineLine)
        (hell : ell ∈ T' p) (U : DyadicTube m0),
        sp hnm (snapTube n ell) = U ∧ c = dyadicTubeToA2 U) →
      (C' : Set CoarseTube) ⊆ (T_Delta_global : Set CoarseTube) := by
    intro P' T' C' hP'_sub_P hT'_sub_T h_parent
    have hT'_sub_source : ∀ p ∈ P', T' p ⊆ T_source := by
      intro p hp
      have h1 : T' p ⊆ T p := hT'_sub_T p hp
      have h2 : p ∈ P := hP'_sub_P hp
      have h3 : T p ⊆ T_source := hT_sub_source p h2
      exact Finset.Subset.trans h1 h3
    have h_qttc : ∀ c ∈ C', ∃ p ∈ P', ∃ ℓ ∈ T' p,
        c = dyadicTubeToA2 (sp hnm (snapTube n ℓ)) := by
      intro c hc
      rcases h_parent c hc with ⟨p, hp, ell, hell, U, hU_eq, hc_eq⟩
      refine ⟨p, hp, ell, hell, ?_⟩
      rw [hU_eq, hc_eq]
    rw [hT_Delta_global_eq]
    exact qttc_C_sub_T_Delta_global hT'_sub_source h_qttc

  exact a2_per_square (n := n) (m0 := m0)
    hδ_eq hΔ_eq hnm hm_pos
    (hQTTC := hQTTC)
    (h_small := h_small_t)
    (hP_nonempty := hP_nonempty)
    (hP_in_square := hP_in_square)
    (R := R)
    (hR := hR)
    (hP_in_ball := hP_in_ball)
    (hP_separated := hP_separated)
    (hP_card_lower := hP_card_lower)
    (hP_card_lower_strong := hP_card_lower_strong)
    (hP_card_upper := hP_card_upper)
    (C_P := C_P)
    (hP_sset := hP_sset)
    (hC_P_bound := hC_P_bound)
    (hs_pos := hs_pos)
    (hs1 := hs_lt_one)
    (hM_pos := hM_pos)
    (hM_lower := hM_lower)
    (hM_upper := hM_upper)
    (h_tubes_card := h_tubes_card)
    (h_tubes_sset := h_tubes_sset)
    (h_tubes_separated := h_tubes_separated)
    (h_slope_bound := h_slope_bound)
    (h_inc := h_inc)
    (hδ_le_quarter_Delta := hδ_le_quarter_Delta)
    (T_Delta_global := T_Delta_global)
    (h_prove_sub := h_prove_sub)
    (hδ_pos := hδ_pos)

/-- Convenience wrapper: constructs per-square S-set from A1's global P_all
    using `per_square_sset_from_a1` (density-aware restriction with heavy-square
    cardinality lower bound), then calls `a2_square_data_from_a1`.

    Use this when you don't already have a per-square S-set.

    The S-set constant is `C_P = 9 * Δ^{-t-29ε/4}`, which satisfies
    `C_P * 81 ≤ Δ^{-t-8ε}` when `Δ^{ε/4} ≤ 1/100`.

    The selected A/hQTTC/h_small triple is passed through unchanged
    (no second QTTC selection). -/
def a2_square_data_from_a1_auto
    {Δ δ s t u ε : ℝ}
    {n m0 : ℕ}
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_eq : Δ = dyadicDelta m0)
    (hnm : m0 ≤ n)
    (hm_pos : 1 ≤ m0)
    (a1 : A1_Output Δ δ t s ε)
    (Q : CoarseSquare Δ)
    (hQ : Q ∈ a1.Qset)
    (K_pack : ℝ)
    (hK_pack_eq : a1.K_pack = K_pack)
    (A : ℝ)
    (hA_one : 1 ≤ A)
    (hQTTC : ∀ {n m : ℕ} {δ Δ C₁ : ℝ} {M : ℕ}
      {P : Finset Plane} {T : Plane → Finset AffineLine},
      (hδ_eq : δ = dyadicDelta n) →
      (hΔ_eq : Δ = dyadicDelta m) →
      (hnm : m ≤ n) → (hm_pos : 1 ≤ m) →
      1 ≤ C₁ → P.Nonempty → 0 < M →
      (∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M) →
      (∀ p ∈ P, _root_.BallGrowth δ s C₁ (T p)) →
      (∀ p ∈ P, SeparatedAt (δ / 2) ((T p) : Set AffineLine)) →
      (∀ p ∈ P, ∀ ℓ ∈ T p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3) →
      (R : ℝ) → (hR : R ≤ Real.sqrt 2) →
      (∀ p ∈ P, |p 1| ≤ R) →
      (hδ_le_quarter_Delta : δ ≤ Δ / 4) →
      (∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1) →
      ∃ (P' : Finset Plane) (T' : Plane → Finset AffineLine)
        (C' : Finset AffineLine) (K C₂ : ℝ) (H : ℕ),
        1 ≤ K ∧ K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
        1 ≤ C₂ ∧ 0 < H ∧
        P' ⊆ P ∧
        (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
        (∀ p ∈ P', T' p ⊆ T p) ∧
        (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
        _root_.IsFiniteDeltaSSet Δ s C₂ C' ∧
        IsDeltaSSet Δ s (max 1 (C_PACK * C₂)) (C' : Set AffineLine) ∧
        C₂ ≤ A * Real.rpow K A * C₁ ∧
        (∀ c ∈ C', |tubeSlope c| ≤ 1) ∧
        (∀ c ∈ C', (LemmaE.getDirV c) 1 ≠ 0) ∧
        (∀ c ∈ C', |tubeIntercept c| ≤ 3) ∧
        (∀ c ∈ C', ∃ p ∈ P', |tubeIntercept c - (p 0 - tubeSlope c * p 1)| ≤ 4 * Δ) ∧
        (∀ c ∈ C', ∃ (p : Plane) (hp : p ∈ P') (ell : AffineLine)
          (hell : ell ∈ T' p) (U : DyadicTube m),
          sp hnm (snapTube n ell) = U ∧ c = dyadicTubeToA2 U) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ c ∈ C',
          (H : ℝ) ≤ ∑ p ∈ P', (pointFiber Δ hΔ_pos T' p c).card) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ p ∈ P', ∀ c ∈ C',
          (pointFiber Δ hΔ_pos T' p c).card ≤
            C₁ * (6 : ℝ)^s * (T p).card * Δ^s) ∧
        (M : ℝ) * (P.card : ℝ) ≤ K * (H : ℝ) * (C'.card : ℝ) ∧
        (H : ℝ) * (C'.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ))
    (h_small : A2_Smallness Δ δ s u ε A K_pack a1.M)
    (hs_pos : 0 < s)
    (hs_lt_one : s < 1)
    -- Scale and smallness for S-set restriction
    (hδ_sq : δ = Δ ^ 2)
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hε_pos : 0 < ε)
    (ht_nonneg : 0 ≤ t)
    -- Source tube family and inclusion
    (T_source : Finset FineTube)
    (hT_sub_source : ∀ p ∈ a1.points Q hQ, a1.tubes p ⊆ T_source)
    -- Global coarse cover
    (T_Delta_global : Finset CoarseTube)
    (hT_Delta_global_eq : T_Delta_global = TDeltaGlobal.T_Delta_global hnm T_source)
    -- Geometry
    (hδ_le_quarter_Delta : δ ≤ Δ / 4)
    (hδ_pos : 0 < δ) :
    A2_SquareData Δ δ s t ε Q := by
  let C_P : ℝ := 9 * Real.rpow Δ (-t - 29 * ε / 4)

  have hP_sset : IsDeltaSSet δ t C_P (a1.points Q hQ : Set Plane) :=
    per_square_sset_from_a1
      (u := t)
      h_small.hΔ_pos hδ_pos hδ_sq h_small_eps hε_pos
      ht_nonneg
      a1 Q hQ

  have hC_P_bound : C_P * 81 ≤ Real.rpow Δ (-t - 8 * ε) :=
    absorb_C_P_times_81 (u := t) h_small.hΔ_pos h_small_eps hε_pos

  exact a2_square_data_from_a1
    (t := t) (u := u)
    hδ_eq hΔ_eq hnm hm_pos
    a1 Q hQ
    K_pack hK_pack_eq
    A hA_one hQTTC h_small
    hs_pos hs_lt_one
    C_P hP_sset hC_P_bound
    T_source hT_sub_source
    T_Delta_global hT_Delta_global_eq
    hδ_le_quarter_Delta hδ_pos

/-- Projection theorem: the `T_Delta` field of the per-square A2 data
    equals the global `T_Delta_global` passed in. Holds for both branches
    of the internal `hP_hi_large` case split. -/
lemma a2_square_data_from_a1_auto_T_Delta_eq
    {Δ δ s t u ε : ℝ} {n m0 : ℕ}
    (hδ_eq : δ = dyadicDelta n) (hΔ_eq : Δ = dyadicDelta m0)
    (hnm : m0 ≤ n) (hm_pos : 1 ≤ m0)
    (a1 : A1_Output Δ δ t s ε) (Q : CoarseSquare Δ) (hQ : Q ∈ a1.Qset)
    (K_pack : ℝ) (hK_pack_eq : a1.K_pack = K_pack)
    (A : ℝ) (hA_one : 1 ≤ A)
    (hQTTC : ∀ {n m : ℕ} {δ Δ C₁ : ℝ} {M : ℕ}
      {P : Finset Plane} {T : Plane → Finset AffineLine},
      (hδ_eq : δ = dyadicDelta n) →
      (hΔ_eq : Δ = dyadicDelta m) →
      (hnm : m ≤ n) → (hm_pos : 1 ≤ m) →
      1 ≤ C₁ → P.Nonempty → 0 < M →
      (∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M) →
      (∀ p ∈ P, _root_.BallGrowth δ s C₁ (T p)) →
      (∀ p ∈ P, SeparatedAt (δ / 2) ((T p) : Set AffineLine)) →
      (∀ p ∈ P, ∀ ℓ ∈ T p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3) →
      (R : ℝ) → (hR : R ≤ Real.sqrt 2) →
      (∀ p ∈ P, |p 1| ≤ R) →
      (hδ_le_quarter_Delta : δ ≤ Δ / 4) →
      (∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1) →
      ∃ (P' : Finset Plane) (T' : Plane → Finset AffineLine)
        (C' : Finset AffineLine) (K C₂ : ℝ) (H : ℕ),
        1 ≤ K ∧ K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
        1 ≤ C₂ ∧ 0 < H ∧
        P' ⊆ P ∧
        (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
        (∀ p ∈ P', T' p ⊆ T p) ∧
        (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
        _root_.IsFiniteDeltaSSet Δ s C₂ C' ∧
        IsDeltaSSet Δ s (max 1 (C_PACK * C₂)) (C' : Set AffineLine) ∧
        C₂ ≤ A * Real.rpow K A * C₁ ∧
        (∀ c ∈ C', |tubeSlope c| ≤ 1) ∧
        (∀ c ∈ C', (LemmaE.getDirV c) 1 ≠ 0) ∧
        (∀ c ∈ C', |tubeIntercept c| ≤ 3) ∧
        (∀ c ∈ C', ∃ p ∈ P', |tubeIntercept c - (p 0 - tubeSlope c * p 1)| ≤ 4 * Δ) ∧
        (∀ c ∈ C', ∃ (p : Plane) (hp : p ∈ P') (ell : AffineLine)
          (hell : ell ∈ T' p) (U : DyadicTube m),
          sp hnm (snapTube n ell) = U ∧ c = dyadicTubeToA2 U) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ c ∈ C',
          (H : ℝ) ≤ ∑ p ∈ P', (pointFiber Δ hΔ_pos T' p c).card) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ p ∈ P', ∀ c ∈ C',
          (pointFiber Δ hΔ_pos T' p c).card ≤
            C₁ * (6 : ℝ)^s * (T p).card * Δ^s) ∧
        (M : ℝ) * (P.card : ℝ) ≤ K * (H : ℝ) * (C'.card : ℝ) ∧
        (H : ℝ) * (C'.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ))
    (h_small : A2_Smallness Δ δ s t ε A K_pack a1.M)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hδ_sq : δ = Δ ^ 2) (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hε_pos : 0 < ε) (ht_nonneg : 0 ≤ t)
    (T_source : Finset FineTube)
    (hT_sub_source : ∀ p ∈ a1.points Q hQ, a1.tubes p ⊆ T_source)
    (T_Delta_global : Finset CoarseTube)
    (hT_Delta_global_eq : T_Delta_global = TDeltaGlobal.T_Delta_global hnm T_source)
    (hδ_le_quarter_Delta : δ ≤ Δ / 4) (hδ_pos : 0 < δ) :
    (a2_square_data_from_a1_auto hδ_eq hΔ_eq hnm hm_pos a1 Q hQ K_pack hK_pack_eq
      A hA_one hQTTC h_small hs_pos hs_lt_one
      hδ_sq h_small_eps hε_pos ht_nonneg
      T_source hT_sub_source T_Delta_global hT_Delta_global_eq
      hδ_le_quarter_Delta hδ_pos).T_Delta = T_Delta_global := by
  dsimp only [a2_square_data_from_a1_auto, a2_square_data_from_a1]
  let m_ceil := Nat.ceil a1.M
  let P_hi := (a1.points Q hQ).filter (fun p => (a1.tubes p).card > m_ceil / 2)
  by_cases h : P_hi.card * 2 ≥ (a1.points Q hQ).card
  · delta a2_per_square; rw [dif_pos h] <;> rfl
  · delta a2_per_square; rw [dif_neg h] <;> rfl

/-- Projection theorem: the `T_original` field of the per-square A2 data
    equals `a1.tubes`. Holds for both branches of the internal
    `hP_hi_large` case split. -/
lemma a2_square_data_from_a1_auto_T_original_eq
    {Δ δ s t u ε : ℝ} {n m0 : ℕ}
    (hδ_eq : δ = dyadicDelta n) (hΔ_eq : Δ = dyadicDelta m0)
    (hnm : m0 ≤ n) (hm_pos : 1 ≤ m0)
    (a1 : A1_Output Δ δ t s ε) (Q : CoarseSquare Δ) (hQ : Q ∈ a1.Qset)
    (K_pack : ℝ) (hK_pack_eq : a1.K_pack = K_pack)
    (A : ℝ) (hA_one : 1 ≤ A)
    (hQTTC : ∀ {n m : ℕ} {δ Δ C₁ : ℝ} {M : ℕ}
      {P : Finset Plane} {T : Plane → Finset AffineLine},
      (hδ_eq : δ = dyadicDelta n) →
      (hΔ_eq : Δ = dyadicDelta m) →
      (hnm : m ≤ n) → (hm_pos : 1 ≤ m) →
      1 ≤ C₁ → P.Nonempty → 0 < M →
      (∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M) →
      (∀ p ∈ P, _root_.BallGrowth δ s C₁ (T p)) →
      (∀ p ∈ P, SeparatedAt (δ / 2) ((T p) : Set AffineLine)) →
      (∀ p ∈ P, ∀ ℓ ∈ T p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3) →
      (R : ℝ) → (hR : R ≤ Real.sqrt 2) →
      (∀ p ∈ P, |p 1| ≤ R) →
      (hδ_le_quarter_Delta : δ ≤ Δ / 4) →
      (∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1) →
      ∃ (P' : Finset Plane) (T' : Plane → Finset AffineLine)
        (C' : Finset AffineLine) (K C₂ : ℝ) (H : ℕ),
        1 ≤ K ∧ K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
        1 ≤ C₂ ∧ 0 < H ∧
        P' ⊆ P ∧
        (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
        (∀ p ∈ P', T' p ⊆ T p) ∧
        (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
        _root_.IsFiniteDeltaSSet Δ s C₂ C' ∧
        IsDeltaSSet Δ s (max 1 (C_PACK * C₂)) (C' : Set AffineLine) ∧
        C₂ ≤ A * Real.rpow K A * C₁ ∧
        (∀ c ∈ C', |tubeSlope c| ≤ 1) ∧
        (∀ c ∈ C', (LemmaE.getDirV c) 1 ≠ 0) ∧
        (∀ c ∈ C', |tubeIntercept c| ≤ 3) ∧
        (∀ c ∈ C', ∃ p ∈ P', |tubeIntercept c - (p 0 - tubeSlope c * p 1)| ≤ 4 * Δ) ∧
        (∀ c ∈ C', ∃ (p : Plane) (hp : p ∈ P') (ell : AffineLine)
          (hell : ell ∈ T' p) (U : DyadicTube m),
          sp hnm (snapTube n ell) = U ∧ c = dyadicTubeToA2 U) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ c ∈ C',
          (H : ℝ) ≤ ∑ p ∈ P', (pointFiber Δ hΔ_pos T' p c).card) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ p ∈ P', ∀ c ∈ C',
          (pointFiber Δ hΔ_pos T' p c).card ≤
            C₁ * (6 : ℝ)^s * (T p).card * Δ^s) ∧
        (M : ℝ) * (P.card : ℝ) ≤ K * (H : ℝ) * (C'.card : ℝ) ∧
        (H : ℝ) * (C'.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ))
    (h_small : A2_Smallness Δ δ s t ε A K_pack a1.M)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hδ_sq : δ = Δ ^ 2) (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hε_pos : 0 < ε) (ht_nonneg : 0 ≤ t)
    (T_source : Finset FineTube)
    (hT_sub_source : ∀ p ∈ a1.points Q hQ, a1.tubes p ⊆ T_source)
    (T_Delta_global : Finset CoarseTube)
    (hT_Delta_global_eq : T_Delta_global = TDeltaGlobal.T_Delta_global hnm T_source)
    (hδ_le_quarter_Delta : δ ≤ Δ / 4) (hδ_pos : 0 < δ)
    (p : Plane) :
    (a2_square_data_from_a1_auto hδ_eq hΔ_eq hnm hm_pos a1 Q hQ K_pack hK_pack_eq
      A hA_one hQTTC h_small hs_pos hs_lt_one
      hδ_sq h_small_eps hε_pos ht_nonneg
      T_source hT_sub_source T_Delta_global hT_Delta_global_eq
      hδ_le_quarter_Delta hδ_pos).T_original p = a1.tubes p := by
  dsimp only [a2_square_data_from_a1_auto, a2_square_data_from_a1]
  let m_ceil := Nat.ceil a1.M
  let P_hi := (a1.points Q hQ).filter (fun p => (a1.tubes p).card > m_ceil / 2)
  by_cases h : P_hi.card * 2 ≥ (a1.points Q hQ).card
  · delta a2_per_square; rw [dif_pos h] <;> rfl
  · delta a2_per_square; rw [dif_neg h] <;> rfl

end DirecretisedFurstenbergEstimate.AppendixA
