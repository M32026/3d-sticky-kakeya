module

/-
  Uniform Prop5 Wrapper

  Converts a NiceConfiguration (DyadicSquare/DyadicTube) to the DSquare/DTube
  format expected by uniform_prop5, and transfers the incidence bound back.

  Key difference from prop5_wrapper: uniform_prop5's K depends ONLY on s,t,
  not on δ, C_P, C_T, or M. This enables λ-independent constants in the
  combining theorem.

  Dependencies:
  - uniform_prop5 (UniformProp5.lean)
  - dyadicSquareToDSquare, dyadicTubeToDTube (DyadicConversion.lean)
  - deltaSSet_dyadicToDTube (FormatConversionLemmas.lean)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M1

/-- Wrapper around uniform_prop5 for NiceConfiguration, with explicit K.

    Use this when K has already been extracted from uniform_prop5 at the
    top level (e.g., for lam-independent constant selection). -/
lemma uniform_prop5_wrapper_with_K
    {n : ℕ} {s t C₁ C_P K : ℝ} {M : ℕ}
    (hK_pos : 0 < K)
    (hK_spec : ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ n →
      ∀ (P : Finset (DSquare n)), P.Nonempty →
        IsFinsetDeltaSSet (δ n) t C_P P →
        (∀ (x y : DSquare n), x ∈ P → y ∈ P → dist x y ≤ 3) →
        (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
        ∀ (Tp : TubeFamily n),
          (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
          (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
          (∀ p ∈ P, IsFinsetDeltaSSet (δ n) s C_T (Tp p)) →
          (∀ p ∈ P, M / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
            let T := P.biUnion fun p => Tp p
            (T.card : ℝ) ≥ (1 / K) * Real.log (1 / δ n) ^ (-K) *
              (1 / (C_P * C_T)) * M * (δ n) ^ (-s) *
                (M * (δ n) ^ s) ^ ((t - s) / (1 - s)))
    (config : NiceConfiguration n s C₁ M)
    (hn_ge_2 : 2 ≤ n)
    (hM_pos : 0 < M)
    (hP_nonempty : config.P₀.Nonempty)
    (hCP : 0 < C_P)
    (hCP_ge1 : 1 ≤ C_P)
    (hC₁ : 0 < C₁)
    (hC1_ge1 : 1 ≤ C₁)
    (hs_nonneg : 0 ≤ s)
    (hP_set : IsFinsetDeltaSSet (dyadicDelta n) t C_P
      (finsetDyadicToDSquare config.P₀))
    (h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1)
    (h_diam : ∀ (p q : DSquare n),
      p ∈ finsetDyadicToDSquare config.P₀ →
      q ∈ finsetDyadicToDSquare config.P₀ → dist p q ≤ 3)
    (h_unit : ∀ (p : DSquare n), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) :
    (config.T₀.card : ℝ) ≥
      (1 / K) * Real.log (1 / dyadicDelta n) ^ (-K) *
        (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) *
        (dyadicDelta n) ^ (-s) *
        ((M : ℝ) * (dyadicDelta n) ^ s) ^ ((t - s) / (1 - s)) := by
  classical
  let P' : Finset (DSquare n) := finsetDyadicToDSquare config.P₀
  let C_T : ℝ := 13 * C₁ * Real.rpow 2 s
  have hCT_pos : 0 < C_T := by
    have h1 : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
    exact mul_pos (mul_pos (by norm_num) hC₁) h1
  have hCT_ge1 : 1 ≤ C_T := by
    have h_rpow1 : 1 ≤ Real.rpow 2 s := Real.one_le_rpow (by norm_num) hs_nonneg
    have h2 : C_T ≥ 13 * C₁ := by
      calc C_T = 13 * C₁ * Real.rpow 2 s := by ring
        _ ≥ 13 * C₁ := by nlinarith
    have h3 : 13 * C₁ ≥ 13 := by linarith
    linarith

  have h_mem_iff : ∀ (p' : DSquare n), p' ∈ P' ↔ dSquareToDyadicSquare p' ∈ config.P₀ := by
    intro p'
    simp [P', finsetDyadicToDSquare, Finset.mem_image]
    constructor
    · rintro ⟨p_dy, hpin, rfl⟩
      have h_rt : dSquareToDyadicSquare (dyadicSquareToDSquare p_dy) = p_dy := by
        cases p_dy
        rfl
      rw [h_rt] <;> exact hpin
    · intro hpin
      refine' ⟨dSquareToDyadicSquare p', hpin, _⟩
      cases p'
      rfl

  have h_tube_mem_iff : ∀ (F : Finset (DyadicTube n)) (t' : DTube n),
      t' ∈ finsetDyadicToDTube F ↔ dTubeToDyadicTube t' ∈ F := by
    intro F t'
    simp [finsetDyadicToDTube, Finset.mem_image]
    constructor
    · rintro ⟨T_dy, hT, rfl⟩
      have h_rt : dTubeToDyadicTube (dyadicTubeToDTube T_dy) = T_dy := roundtrip_dyadic T_dy
      rw [h_rt] <;> exact hT
    · intro hT
      refine' ⟨dTubeToDyadicTube t', hT, _⟩
      exact roundtrip_dtube t'

  have h_preimage_eq_image : ∀ (F : Finset (DyadicTube n)),
      (dTubeToDyadicTube ⁻¹' (F : Set (DyadicTube n))) =
      (finsetDyadicToDTube F : Set (DTube n)) := by
    intro F
    ext t'
    simp only [Set.mem_preimage, Finset.mem_coe]
    exact (h_tube_mem_iff F t').symm

  let Tp : DSquare n → Finset (DTube n) := fun p' =>
    let p_dy := dSquareToDyadicSquare p'
    if h : p_dy ∈ config.P₀ then
      finsetDyadicToDTube (config.tubeFamily p_dy h)
    else
      ∅

  have hP'_nonempty : P'.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    refine' ⟨dyadicSquareToDSquare p, _⟩
    simp [P', finsetDyadicToDSquare, Finset.mem_image, hp] <;> exact ⟨p, hp, rfl⟩

  have hTp_set : ∀ p' ∈ P', IsFinsetDeltaSSet (δ n) s C_T (Tp p') := by
    intro p' hp'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    have h1 : Tp p' = finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
      unfold Tp; rw [dif_pos h_p_in]
    rw [h1]
    have h2 : IsDeltaSSet (dyadicDelta n) s C₁
        (config.tubeFamily p_dy h_p_in : Set (DyadicTube n)) :=
      config.h_delta_s_set p_dy h_p_in
    have h3 : IsDeltaSSet (dyadicDelta n) s C_T
        (dTubeToDyadicTube ⁻¹' (config.tubeFamily p_dy h_p_in : Set (DyadicTube n))) :=
      deltaSSet_dyadicToDTube hs_nonneg hC₁ h2
    rw [h_preimage_eq_image (config.tubeFamily p_dy h_p_in)] at h3
    have hδ : (dyadicDelta n) = δ n := scale_eq.symm
    rw [hδ] at h3
    exact h3

  have hTp_int : ∀ p' ∈ P', ∀ t' ∈ Tp p', (t'.toSet ∩ p'.toSet).Nonempty := by
    intro p' hp' t' ht'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    let T_dy := dTubeToDyadicTube t'
    have hT_in : T_dy ∈ config.tubeFamily p_dy h_p_in := by
      have h1 : t' ∈ finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
        unfold Tp at ht'; rw [dif_pos h_p_in] at ht'; exact ht'
      exact (h_tube_mem_iff (config.tubeFamily p_dy h_p_in) t').mp h1
    have h_inc : (T_dy.toSet ∩ p_dy.toSet).Nonempty :=
      config.h_intersect p_dy h_p_in T_dy hT_in
    rcases h_inc with ⟨x, hxT, hxp⟩
    refine' ⟨(x 0, x 1), _⟩
    have h6 : (x 0, x 1) ∈ t'.toSet := by
      rw [←tubeToSet_correspondence t' x] <;> exact hxT
    have h7 : (x 0, x 1) ∈ p'.toSet := by
      rw [←toSet_correspondence p' x] <;> exact hxp
    exact ⟨h6, h7⟩

  have hTp_slope : ∀ p' ∈ P', ∀ t' ∈ Tp p', |t'.slope| ≤ 1 := by
    intro p' hp' t' ht'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    let T_dy := dTubeToDyadicTube t'
    have hT_in_family : T_dy ∈ config.tubeFamily p_dy h_p_in := by
      have h1 : t' ∈ finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
        unfold Tp at ht'; rw [dif_pos h_p_in] at ht'; exact ht'
      exact (h_tube_mem_iff (config.tubeFamily p_dy h_p_in) t').mp h1
    have hT_in_T0 : T_dy ∈ config.T₀ := config.h_subset p_dy h_p_in hT_in_family
    have h3 : |T_dy.slope| ≤ 1 := h_slope T_dy hT_in_T0
    have h4 : t'.slope = T_dy.slope := (slope_eq t').symm
    rw [h4] <;> exact h3

  have hTp_card : ∀ p' ∈ P', (M : ℝ) / 2 < (Tp p').card ∧ (Tp p').card ≤ (M : ℝ) := by
    intro p' hp'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    have h1 : (Tp p').card = (config.tubeFamily p_dy h_p_in).card := by
      unfold Tp; rw [dif_pos h_p_in]; exact card_dyadicToDTube _
    have h2 : (config.tubeFamily p_dy h_p_in).card = M := config.h_size p_dy h_p_in
    rw [h1, h2]
    have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    exact ⟨by linarith, by linarith⟩

  have hδ_eq : δ n = dyadicDelta n := scale_eq

  have h_bound := hK_spec C_P C_T (M : ℝ) hCP hCP_ge1 hCT_pos hCT_ge1
    (by exact_mod_cast (show 1 ≤ M from Nat.succ_le_iff.mpr hM_pos))
    hn_ge_2 P' hP'_nonempty
    (by simpa [IsFinsetDeltaSSet, hδ_eq] using hP_set)
    h_diam h_unit Tp hTp_int hTp_slope hTp_set hTp_card

  let T_dtube : Finset (DTube n) := P'.biUnion Tp
  have h_sub : T_dtube ⊆ finsetDyadicToDTube config.T₀ := by
    intro t' ht'
    rcases Finset.mem_biUnion.mp ht' with ⟨p', hp', ht'⟩
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    have h1 : t' ∈ finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
      unfold Tp at ht'; rw [dif_pos h_p_in] at ht'; exact ht'
    have h2 : dTubeToDyadicTube t' ∈ config.tubeFamily p_dy h_p_in :=
      (h_tube_mem_iff (config.tubeFamily p_dy h_p_in) t').mp h1
    have hT_in_T0 : dTubeToDyadicTube t' ∈ config.T₀ :=
      config.h_subset p_dy h_p_in h2
    exact (h_tube_mem_iff config.T₀ t').mpr hT_in_T0

  have h_card_le : T_dtube.card ≤ (finsetDyadicToDTube config.T₀).card :=
    Finset.card_le_card h_sub
  have h_card_eq : (finsetDyadicToDTube config.T₀).card = config.T₀.card :=
    card_dyadicToDTube config.T₀

  have h_final : (T_dtube.card : ℝ) ≥ (1 / K) * Real.log (1 / δ n) ^ (-K) *
      (1 / (C_P * C_T)) * (M : ℝ) * (δ n) ^ (-s) *
      ((M : ℝ) * (δ n) ^ s) ^ ((t - s) / (1 - s)) := h_bound

  rw [hδ_eq] at h_final
  have h : (config.T₀.card : ℝ) ≥ (T_dtube.card : ℝ) := by
    have h9 : (T_dtube.card : ℝ) ≤ ((finsetDyadicToDTube config.T₀).card : ℝ) := by exact_mod_cast h_card_le
    have h10 : ((finsetDyadicToDTube config.T₀).card : ℝ) = (config.T₀.card : ℝ) := by
      exact_mod_cast h_card_eq
    rw [h10] at h9
    exact h9
  exact le_trans h_final h

/-- Wrapper around uniform_prop5 for NiceConfiguration.

    Returns K depending only on s,t (not δ, C_P, C_T, M).
    Requires t < 1 (uniform_prop5 constraint).
    Requires diameter ≤ 3 and |x.1| ≤ 1 for the point set. -/
lemma uniform_prop5_wrapper
    {n : ℕ} {s t C₁ C_P : ℝ} {M : ℕ}
    (config : NiceConfiguration n s C₁ M)
    (hn_ge_2 : 2 ≤ n)
    (hM_pos : 0 < M)
    (hP_nonempty : config.P₀.Nonempty)
    (h_st : 0 < s ∧ s < 1 ∧ s ≤ t ∧ t ≤ 1)
    (hCP : 0 < C_P)
    (hCP_ge1 : 1 ≤ C_P)
    (hC₁ : 0 < C₁)
    (hC1_ge1 : 1 ≤ C₁)
    -- Point set S-set property at exponent t
    (hP_set : IsFinsetDeltaSSet (dyadicDelta n) t C_P
      (finsetDyadicToDSquare config.P₀))
    -- Slope bound
    (h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1)
    -- Diameter bound for all pairs of squares
    (h_diam : ∀ (p q : DSquare n),
      p ∈ finsetDyadicToDSquare config.P₀ →
      q ∈ finsetDyadicToDSquare config.P₀ → dist p q ≤ 3)
    -- Vertical strip bound
    (h_unit : ∀ (p : DSquare n), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) :
    ∃ (K : ℝ), 0 < K ∧
      (config.T₀.card : ℝ) ≥
        (1 / K) * Real.log (1 / dyadicDelta n) ^ (-K) *
          (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) *
          (dyadicDelta n) ^ (-s) *
          ((M : ℝ) * (dyadicDelta n) ^ s) ^ ((t - s) / (1 - s)) := by
  classical
  let P' : Finset (DSquare n) := finsetDyadicToDSquare config.P₀
  let C_T : ℝ := 13 * C₁ * Real.rpow 2 s
  have hs_nonneg : 0 ≤ s := le_of_lt h_st.1
  have hCT_pos : 0 < C_T := by
    have h1 : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
    exact mul_pos (mul_pos (by norm_num) hC₁) h1
  have hCT_ge1 : 1 ≤ C_T := by
    have h_rpow1 : 1 ≤ Real.rpow 2 s := Real.one_le_rpow (by norm_num) hs_nonneg
    have h2 : C_T ≥ 13 * C₁ := by
      calc C_T = 13 * C₁ * Real.rpow 2 s := by ring
        _ ≥ 13 * C₁ := by nlinarith
    have h3 : 13 * C₁ ≥ 13 := by linarith
    linarith

  have h_mem_iff : ∀ (p' : DSquare n), p' ∈ P' ↔ dSquareToDyadicSquare p' ∈ config.P₀ := by
    intro p'
    simp [P', finsetDyadicToDSquare, Finset.mem_image]
    constructor
    · rintro ⟨p_dy, hpin, rfl⟩
      have h_rt : dSquareToDyadicSquare (dyadicSquareToDSquare p_dy) = p_dy := by
        cases p_dy
        rfl
      rw [h_rt] <;> exact hpin
    · intro hpin
      refine' ⟨dSquareToDyadicSquare p', hpin, _⟩
      cases p'
      rfl

  have h_tube_mem_iff : ∀ (F : Finset (DyadicTube n)) (t' : DTube n),
      t' ∈ finsetDyadicToDTube F ↔ dTubeToDyadicTube t' ∈ F := by
    intro F t'
    simp [finsetDyadicToDTube, Finset.mem_image]
    constructor
    · rintro ⟨T_dy, hT, rfl⟩
      have h_rt : dTubeToDyadicTube (dyadicTubeToDTube T_dy) = T_dy := roundtrip_dyadic T_dy
      rw [h_rt] <;> exact hT
    · intro hT
      refine' ⟨dTubeToDyadicTube t', hT, _⟩
      exact roundtrip_dtube t'

  have h_preimage_eq_image : ∀ (F : Finset (DyadicTube n)),
      (dTubeToDyadicTube ⁻¹' (F : Set (DyadicTube n))) =
      (finsetDyadicToDTube F : Set (DTube n)) := by
    intro F
    ext t'
    simp only [Set.mem_preimage, Finset.mem_coe]
    exact (h_tube_mem_iff F t').symm

  let Tp : DSquare n → Finset (DTube n) := fun p' =>
    let p_dy := dSquareToDyadicSquare p'
    if h : p_dy ∈ config.P₀ then
      finsetDyadicToDTube (config.tubeFamily p_dy h)
    else
      ∅

  have hP'_nonempty : P'.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    refine' ⟨dyadicSquareToDSquare p, _⟩
    simp [P', finsetDyadicToDSquare, Finset.mem_image, hp] <;> exact ⟨p, hp, rfl⟩

  have hTp_set : ∀ p' ∈ P', IsFinsetDeltaSSet (δ n) s C_T (Tp p') := by
    intro p' hp'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    have h1 : Tp p' = finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
      unfold Tp; rw [dif_pos h_p_in]
    rw [h1]
    have h2 : IsDeltaSSet (dyadicDelta n) s C₁
        (config.tubeFamily p_dy h_p_in : Set (DyadicTube n)) :=
      config.h_delta_s_set p_dy h_p_in
    have h3 : IsDeltaSSet (dyadicDelta n) s C_T
        (dTubeToDyadicTube ⁻¹' (config.tubeFamily p_dy h_p_in : Set (DyadicTube n))) :=
      deltaSSet_dyadicToDTube hs_nonneg hC₁ h2
    rw [h_preimage_eq_image (config.tubeFamily p_dy h_p_in)] at h3
    have hδ : (dyadicDelta n) = δ n := scale_eq.symm
    rw [hδ] at h3
    exact h3

  have hTp_int : ∀ p' ∈ P', ∀ t' ∈ Tp p', (t'.toSet ∩ p'.toSet).Nonempty := by
    intro p' hp' t' ht'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    let T_dy := dTubeToDyadicTube t'
    have hT_in : T_dy ∈ config.tubeFamily p_dy h_p_in := by
      have h1 : t' ∈ finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
        unfold Tp at ht'; rw [dif_pos h_p_in] at ht'; exact ht'
      exact (h_tube_mem_iff (config.tubeFamily p_dy h_p_in) t').mp h1
    have h_inc : (T_dy.toSet ∩ p_dy.toSet).Nonempty :=
      config.h_intersect p_dy h_p_in T_dy hT_in
    rcases h_inc with ⟨x, hxT, hxp⟩
    refine' ⟨(x 0, x 1), _⟩
    have h6 : (x 0, x 1) ∈ t'.toSet := by
      rw [←tubeToSet_correspondence t' x] <;> exact hxT
    have h7 : (x 0, x 1) ∈ p'.toSet := by
      rw [←toSet_correspondence p' x] <;> exact hxp
    exact ⟨h6, h7⟩

  have hTp_slope : ∀ p' ∈ P', ∀ t' ∈ Tp p', |t'.slope| ≤ 1 := by
    intro p' hp' t' ht'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    let T_dy := dTubeToDyadicTube t'
    have hT_in_family : T_dy ∈ config.tubeFamily p_dy h_p_in := by
      have h1 : t' ∈ finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
        unfold Tp at ht'; rw [dif_pos h_p_in] at ht'; exact ht'
      exact (h_tube_mem_iff (config.tubeFamily p_dy h_p_in) t').mp h1
    have hT_in_T0 : T_dy ∈ config.T₀ := config.h_subset p_dy h_p_in hT_in_family
    have h3 : |T_dy.slope| ≤ 1 := h_slope T_dy hT_in_T0
    have h4 : t'.slope = T_dy.slope := (slope_eq t').symm
    rw [h4] <;> exact h3

  have hTp_card : ∀ p' ∈ P', (M : ℝ) / 2 < (Tp p').card ∧ (Tp p').card ≤ (M : ℝ) := by
    intro p' hp'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    have h1 : (Tp p').card = (config.tubeFamily p_dy h_p_in).card := by
      unfold Tp; rw [dif_pos h_p_in]; exact card_dyadicToDTube _
    have h2 : (config.tubeFamily p_dy h_p_in).card = M := config.h_size p_dy h_p_in
    rw [h1, h2]
    have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    exact ⟨by linarith, by linarith⟩

  have hδ_eq : δ n = dyadicDelta n := scale_eq

  -- Apply uniform_prop5 (K is chosen before t, so it's uniform in t)
  have hs_pos : 0 < s := h_st.1
  have hs_lt_one : s < 1 := h_st.2.1
  have hst : s ≤ t := h_st.2.2.1
  have ht_le_one : t ≤ 1 := h_st.2.2.2
  rcases uniform_prop5 s hs_pos hs_lt_one with ⟨K, hK_pos, h_main⟩
  have h_bound := h_main t hst ht_le_one C_P C_T (M : ℝ) hCP hCP_ge1 hCT_pos hCT_ge1
    (by exact_mod_cast (show 1 ≤ M from Nat.succ_le_iff.mpr hM_pos))
    hn_ge_2 P' hP'_nonempty
    (by simpa [IsFinsetDeltaSSet, hδ_eq] using hP_set)
    h_diam h_unit Tp hTp_int hTp_slope hTp_set hTp_card

  let T_dtube : Finset (DTube n) := P'.biUnion Tp
  have h_sub : T_dtube ⊆ finsetDyadicToDTube config.T₀ := by
    intro t' ht'
    rcases Finset.mem_biUnion.mp ht' with ⟨p', hp', ht'⟩
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    have h1 : t' ∈ finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
      unfold Tp at ht'; rw [dif_pos h_p_in] at ht'; exact ht'
    have h2 : dTubeToDyadicTube t' ∈ config.tubeFamily p_dy h_p_in :=
      (h_tube_mem_iff (config.tubeFamily p_dy h_p_in) t').mp h1
    have hT_in_T0 : dTubeToDyadicTube t' ∈ config.T₀ :=
      config.h_subset p_dy h_p_in h2
    exact (h_tube_mem_iff config.T₀ t').mpr hT_in_T0

  have h_card_le : T_dtube.card ≤ (finsetDyadicToDTube config.T₀).card :=
    Finset.card_le_card h_sub
  have h_card_eq : (finsetDyadicToDTube config.T₀).card = config.T₀.card :=
    card_dyadicToDTube config.T₀

  have h_final : (T_dtube.card : ℝ) ≥ (1 / K) * Real.log (1 / δ n) ^ (-K) *
      (1 / (C_P * C_T)) * (M : ℝ) * (δ n) ^ (-s) *
      ((M : ℝ) * (δ n) ^ s) ^ ((t - s) / (1 - s)) := h_bound

  rw [hδ_eq] at h_final
  have h : (config.T₀.card : ℝ) ≥ (T_dtube.card : ℝ) := by
    have h9 : (T_dtube.card : ℝ) ≤ ((finsetDyadicToDTube config.T₀).card : ℝ) := by exact_mod_cast h_card_le
    have h10 : ((finsetDyadicToDTube config.T₀).card : ℝ) = (config.T₀.card : ℝ) := by
      exact_mod_cast h_card_eq
    rw [h10] at h9
    exact h9
  exact ⟨K, hK_pos, by simpa [C_T] using le_trans h_final h⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
