module

/-
  B1 Hard Fields — standalone lemmas for the B1BridgeDecomposition.

  Proves the "easy" geometric properties from source-to-nice data:
  1. `b1_hPfin_sset_strong`: IsDeltaSSet δ_n u (δ_n^{-ε}) on square centers
  2. `b1_hPfin_sset`: weakened to δ_n^{-2ε} (for B1BridgeDecomposition)
  3. `b1_hP_ball_growth`: ball growth via strong S-set

  The critical blocker `hM_fine_upper` is NOT proved here.

  Dependencies: PointSSetTransfer, SsetExtractionBounds, DyadicBridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.PointSSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.SsetExtractionBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.DyadicSquareCenterSeparation
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.RegularB1Bounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.DeltasSetTreeExtractionCore
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction
open DirecretisedFurstenbergEstimate.FrontEndLemmas

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.B1HardFields

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ### Helper: subset S-set with Ncover ratio -/

lemma subset_sset_with_ncover_ratio
    {X : Type*} [PseudoMetricSpace X] {δ u C K : ℝ}
    {A B : Set X}
    (hδ_pos : 0 < δ) (hu_nonneg : 0 ≤ u) (hC_pos : 0 < C) (hK_pos : 0 < K)
    (hA_nonempty : A.Nonempty)
    (hA_sub_B : A ⊆ B)
    (hB_sset : IsDeltaSSet δ u C B)
    (h_ratio : (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) ≤
        ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)) :
    IsDeltaSSet δ u (K * C) A := by
  have hKC_pos : 0 < K * C := mul_pos hK_pos hC_pos
  refine' ⟨hA_nonempty, hδ_pos, hKC_pos, hu_nonneg, _⟩
  intro x r hr
  have h_inter_sub : A ∩ Metric.closedBall x r ⊆ B ∩ Metric.closedBall x r := by
    intro z hz; exact ⟨hA_sub_B hz.1, hz.2⟩
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall x r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set h_inter_sub
  have h2 := hB_sset.2.2.2.2 x r hr
  set N_A := (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) with hN_A
  set N_B := (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) with hN_B
  have h3 : N_B ≤ ENNReal.ofReal K * N_A := h_ratio
  have h4 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * N_B ≤
      ENNReal.ofReal (K * C) * (ENNReal.ofReal r) ^ u * N_A := by
    calc ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * N_B
      ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * (ENNReal.ofReal K * N_A) := by gcongr
    _ = ENNReal.ofReal C * ENNReal.ofReal K * (ENNReal.ofReal r) ^ u * N_A := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    _ = ENNReal.ofReal (K * C) * (ENNReal.ofReal r) ^ u * N_A := by
      have h5 : ENNReal.ofReal C * ENNReal.ofReal K = ENNReal.ofReal (K * C) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> ring_nf
      rw [h5] <;> ring
  exact le_trans h1 (le_trans h2 h4)

/-! ### Helper: cardinality bound from disjoint squares -/

lemma b1_card_ge_from_squares
    {n : ℕ}
    {config_P0 : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    {P'_fin : Finset Plane}
    {P_oriented : Set Plane}
    (h_squares_meet : ∀ q ∈ config_P0, ((q.toSet : Set Plane) ∩ P_oriented).Nonempty)
    (hP_oriented_sub_P' : P_oriented ⊆ (P'_fin : Set Plane)) :
    config_P0.card ≤ P'_fin.card := by
  classical
  choose f hf using fun (q : DiscretisedFurstenbergEstimate.DyadicSquare n) (hq : q ∈ config_P0) =>
    h_squares_meet q hq
  let g : DiscretisedFurstenbergEstimate.DyadicSquare n → Plane := fun q =>
    if hq : q ∈ config_P0 then f q hq else (0 : Plane)
  have hg_mem : ∀ q ∈ config_P0, g q ∈ (q.toSet : Set Plane) ∩ P_oriented := by
    intro q hq
    have h_eq : g q = f q hq := by unfold g; rw [dif_pos hq]
    rw [h_eq]; exact hf q hq
  have hg_in_P' : ∀ q ∈ config_P0, g q ∈ P'_fin := by
    intro q hq
    have h5 : g q ∈ P_oriented := (hg_mem q hq).2
    exact hP_oriented_sub_P' h5
  have hg_inj : Set.InjOn g (config_P0 : Set _) := by
    intro q1 hq1 q2 hq2 h_eq
    have h1 : g q1 ∈ (q1.toSet : Set Plane) := (hg_mem q1 hq1).1
    have h2 : g q2 ∈ (q2.toSet : Set Plane) := (hg_mem q2 hq2).1
    rw [h_eq] at h1
    by_cases hne : q1 = q2
    · exact hne
    · have h4 : Disjoint (q1.toSet : Set Plane) (q2.toSet : Set Plane) :=
        dyadicSquare_toSet_disjoint hne
      have h5 : ∀ ⦃x : Plane⦄, x ∈ (q1.toSet : Set Plane) → x ∉ (q2.toSet : Set Plane) :=
        Set.disjoint_left.mp h4
      have h6 : (g q2) ∉ (q2.toSet : Set Plane) := h5 h1
      exact False.elim (h6 h2)
  have h_image_sub : (config_P0.image g) ⊆ P'_fin := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
    exact hg_in_P' q hq
  have h_card_image : (config_P0.image g).card = config_P0.card :=
    Finset.card_image_of_injOn hg_inj
  calc config_P0.card
    = (config_P0.image g).card := h_card_image.symm
  _ ≤ P'_fin.card := Finset.card_le_card h_image_sub

/-! ### 1. Strong point S-set on centers (`hPfin_sset_strong`) -/

/-- Transfer S-set from Pbar to square centers with constant δ_n^{-ε}.

    This is the STRONGER version used for ball growth. Weaken to δ_n^{-2ε}
    using `IsDeltaSSet.weaken_C` for the B1BridgeDecomposition field. -/
lemma b1_hPfin_sset_strong
    {n : ℕ} {δ_n u ε ρ_mass C_Pbar : ℝ}
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hu_nonneg : 0 ≤ u) (hε_pos : 0 < ε)
    (hC_Pbar_pos : 0 < C_Pbar)
    (hρ_mass_nonneg : 0 ≤ ρ_mass)
    {Pbar : Finset Plane}
    {P_oriented : Set Plane}
    {config_P0 : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    (hconfig_P0_nonempty : config_P0.Nonempty)
    (hPbar_sset : IsDeltaSSet δ_n u C_Pbar (Pbar : Set Plane))
    (hPbar_sep : Set.Pairwise (Pbar : Set Plane) (fun p q => δ_n ≤ dist p q))
    (hP_oriented_sub_Pbar : P_oriented ⊆ (Pbar : Set Plane))
    (hP_oriented_sub_pointSet : P_oriented ⊆
        ⋃ p ∈ (config_P0 : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)),
          (p.toSet : Set Plane))
    (h_squares_meet : ∀ q ∈ config_P0,
        ((q.toSet : Set Plane) ∩ P_oriented).Nonempty)
    (h_ncover_lower : (Metric.externalCoveringNumber δ_n.toNNReal
          (⋃ p ∈ (config_P0 : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)),
            (p.toSet : Set Plane)) : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ_n ρ_mass) *
          (Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set Plane)))
    (h_absorb : (25 : ℝ) * 625 * (2 : ℝ)^u * Real.rpow δ_n (-ρ_mass) * C_Pbar ≤
        Real.rpow δ_n (-ε)) :
    IsDeltaSSet δ_n u (Real.rpow δ_n (-ε))
      (config_P0.image dyadicSquareCenter : Set Plane) := by
  set configPointSet : Set Plane :=
    ⋃ p ∈ (config_P0 : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)),
      (p.toSet : Set Plane) with hconfigPointSet
  set P'_fin : Finset Plane := Pbar.filter (fun p => p ∈ configPointSet) with hP'_fin
  set P' : Set Plane := (P'_fin : Set Plane) with hP'
  have hP'_eq : P' = (Pbar : Set Plane) ∩ configPointSet := by
    ext x; simp [hP'_fin, hP', Finset.mem_filter] <;> tauto
  have hP'_sub_Pbar : P' ⊆ (Pbar : Set Plane) := by
    rw [hP'_eq]; intro z hz; exact hz.1
  have hP'_sub_pointSet : P' ⊆ configPointSet := by
    rw [hP'_eq]; intro z hz; exact hz.2
  have hP_oriented_sub_P' : P_oriented ⊆ P' := by
    intro p hp
    have h1 : p ∈ (Pbar : Set Plane) := hP_oriented_sub_Pbar hp
    have h2 : p ∈ configPointSet := hP_oriented_sub_pointSet hp
    rw [hP'_eq]; exact ⟨h1, h2⟩
  have hP'_sep : Set.Pairwise P' (fun p q => δ_n ≤ dist p q) :=
    fun p hp q hq hne => hPbar_sep (hP'_sub_Pbar hp) (hP'_sub_Pbar hq) hne

  have hP'_card_ge : config_P0.card ≤ P'_fin.card :=
    b1_card_ge_from_squares h_squares_meet hP_oriented_sub_P'

  have hP'_nonempty : P'.Nonempty := by
    rcases hconfig_P0_nonempty with ⟨q, hq⟩
    rcases h_squares_meet q hq with ⟨p, _, hp_oriented⟩
    exact ⟨p, hP_oriented_sub_P' hp_oriented⟩

  have h_ncover_cfg : (Metric.externalCoveringNumber δ_n.toNNReal configPointSet : ENNReal) ≤
      (config_P0.card : ENNReal) := by
    have hδ_toNN : δ_n.toNNReal = (DiscretisedFurstenbergEstimate.dyadicDelta n).toNNReal := by
      rw [hδ_n_eq]
    rw [hδ_toNN]
    have h_sub : configPointSet ⊆
        ⋃ p ∈ (config_P0 : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)),
          (p.toSet : Set Plane) := by rfl
    have h := fine_card_lower_ncover (P₀ := config_P0) (pointSet := configPointSet) h_sub
    have h_card_eq : (config_P0.card : ENNReal) = (config_P0.card : ENNReal) := rfl
    exact_mod_cast h

  have h_card_le : (P'_fin.card : ENNReal) ≤
      (25 : ENNReal) * (Metric.externalCoveringNumber δ_n.toNNReal P' : ENNReal) := by
    have h := separated_card_le_25_cover hδ_n_pos (S := P'_fin) hP'_sep
    exact_mod_cast h

  set Nbar := (Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set Plane) : ENNReal) with hNbar
  set Ncfg := (Metric.externalCoveringNumber δ_n.toNNReal configPointSet : ENNReal) with hNcfg
  set Np' := (Metric.externalCoveringNumber δ_n.toNNReal P' : ENNReal) with hNp'
  have h_rpow1_pos : 0 < Real.rpow δ_n (-ρ_mass) := Real.rpow_pos_of_pos hδ_n_pos _
  have h_rpow2_pos : 0 < Real.rpow δ_n ρ_mass := Real.rpow_pos_of_pos hδ_n_pos _
  have h_rpow_mul : Real.rpow δ_n (-ρ_mass) * Real.rpow δ_n ρ_mass = 1 := by
    have h_add : Real.rpow δ_n ((-ρ_mass) + ρ_mass) =
        Real.rpow δ_n (-ρ_mass) * Real.rpow δ_n ρ_mass := Real.rpow_add hδ_n_pos _ _
    have h_zero : (-ρ_mass) + ρ_mass = 0 := by ring
    rw [h_zero] at h_add
    simpa using h_add.symm
  have h_ennreal_mul : ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) *
      ENNReal.ofReal (Real.rpow δ_n ρ_mass) = 1 := by
    rw [← ENNReal.ofReal_mul h_rpow1_pos.le, h_rpow_mul] <;> simp
  have h_step1 : Nbar ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * Ncfg := by
    have h5 : ENNReal.ofReal (Real.rpow δ_n ρ_mass) * Nbar ≤ Ncfg := h_ncover_lower
    have h6 : Nbar = ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) *
        (ENNReal.ofReal (Real.rpow δ_n ρ_mass) * Nbar) := by
      rw [← mul_assoc, h_ennreal_mul, one_mul]
    rw [h6]; gcongr
  have h_step2 : Nbar ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * (config_P0.card : ENNReal) := by
    calc Nbar ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * Ncfg := h_step1
       _ ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * (config_P0.card : ENNReal) := by gcongr
  have h_step3 : Nbar ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * (P'_fin.card : ENNReal) := by
    calc Nbar ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * (config_P0.card : ENNReal) := h_step2
       _ ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * (P'_fin.card : ENNReal) := by
         gcongr
  have h_step4 : Nbar ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * ((25 : ENNReal) * Np') := by
    calc Nbar ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * (P'_fin.card : ENNReal) := h_step3
       _ ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * ((25 : ENNReal) * Np') := by gcongr
  have h_step5 : Nbar ≤ ENNReal.ofReal ((25 : ℝ) * Real.rpow δ_n (-ρ_mass)) * Np' := by
    have h9 : (25 : ENNReal) = ENNReal.ofReal (25 : ℝ) := by simp
    have h10 : ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * ((25 : ENNReal) * Np') =
        ENNReal.ofReal ((25 : ℝ) * Real.rpow δ_n (-ρ_mass)) * Np' := by
      rw [h9]
      have h11 : ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * (ENNReal.ofReal (25 : ℝ) * Np') =
          (ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * ENNReal.ofReal (25 : ℝ)) * Np' := by ring
      rw [h11]
      have h12 : ENNReal.ofReal (Real.rpow δ_n (-ρ_mass)) * ENNReal.ofReal (25 : ℝ) =
          ENNReal.ofReal (Real.rpow δ_n (-ρ_mass) * (25 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
      rw [h12]
      have h13 : Real.rpow δ_n (-ρ_mass) * (25 : ℝ) = (25 : ℝ) * Real.rpow δ_n (-ρ_mass) := by ring
      rw [h13] <;> ring
    exact le_trans h_step4 (le_of_eq h10)

  let C' := (25 : ℝ) * Real.rpow δ_n (-ρ_mass) * C_Pbar
  have hC'_pos : 0 < C' := by positivity
  have hP'_sset : IsDeltaSSet δ_n u C' P' :=
    subset_sset_with_ncover_ratio hδ_n_pos hu_nonneg hC_Pbar_pos
      (by positivity) hP'_nonempty hP'_sub_Pbar hPbar_sset h_step5

  have h_match_forward : ∀ p ∈ P', ∃ q ∈ config_P0,
      dist p (dyadicSquareCenter q) ≤ δ_n := by
    intro p hp
    have h_in : p ∈ configPointSet := hP'_sub_pointSet hp
    rcases Set.mem_iUnion₂.mp h_in with ⟨q, hq, hp_in_square⟩
    refine ⟨q, hq, ?_⟩
    have h9 : (q.toSet : Set Plane) ⊆
        Metric.closedBall (dyadicSquareCenter q)
          (DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2) :=
      dyadicSquare_subset_centerBall q
    have h10 : p ∈ Metric.closedBall (dyadicSquareCenter q)
        (DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2) := h9 hp_in_square
    have h11 : DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2 ≤ δ_n := by
      rw [hδ_n_eq]
      have h12 : Real.sqrt 2 / 2 ≤ 1 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith
    exact (Metric.mem_closedBall.mp h10).trans h11

  have h_match_backward : ∀ q ∈ config_P0, ∃ p ∈ P',
      dist p (dyadicSquareCenter q) ≤ δ_n := by
    intro q hq
    rcases h_squares_meet q hq with ⟨p, hp_in_square, hp_in_Poriented⟩
    have hp_in_P' : p ∈ P' := hP_oriented_sub_P' hp_in_Poriented
    refine ⟨p, hp_in_P', ?_⟩
    have h9 : (q.toSet : Set Plane) ⊆
        Metric.closedBall (dyadicSquareCenter q)
          (DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2) :=
      dyadicSquare_subset_centerBall q
    have h10 : p ∈ Metric.closedBall (dyadicSquareCenter q)
        (DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2) := h9 hp_in_square
    have h11 : DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2 ≤ δ_n := by
      rw [hδ_n_eq]
      have h12 : Real.sqrt 2 / 2 ≤ 1 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith
    exact (Metric.mem_closedBall.mp h10).trans h11

  have h_inj : Set.InjOn dyadicSquareCenter
      (config_P0 : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)) := by
    intro q1 _ q2 _ h
    exact dyadicSquareCenter_injective (n := n) h

  have h_transfer : IsDeltaSSet δ_n u (C' * 625 * (2 : ℝ)^u)
      (config_P0.image dyadicSquareCenter : Set Plane) :=
    sset_transfer_to_centers hδ_n_pos hu_nonneg hC'_pos hP'_sset
      h_match_forward h_match_backward h_inj

  have hC_total_le : C' * 625 * (2 : ℝ)^u ≤ Real.rpow δ_n (-ε) := by
    dsimp only [C']
    have h : (25 : ℝ) * Real.rpow δ_n (-ρ_mass) * C_Pbar * 625 * (2 : ℝ)^u =
        (25 : ℝ) * 625 * (2 : ℝ)^u * Real.rpow δ_n (-ρ_mass) * C_Pbar := by ring
    rw [h]
    exact h_absorb

  rcases h_transfer with ⟨hne, hδ, hC_old_pos, hs, hmain⟩
  have hC_new_pos : 0 < Real.rpow δ_n (-ε) := Real.rpow_pos_of_pos hδ_n_pos _
  refine ⟨hne, hδ, hC_new_pos, hs, fun x r hr => ?_⟩
  have h6 := hmain x r hr
  have h7 : ENNReal.ofReal (C' * 625 * (2 : ℝ)^u) ≤
      ENNReal.ofReal (Real.rpow δ_n (-ε)) := ENNReal.ofReal_le_ofReal hC_total_le
  have h_goal : (Metric.externalCoveringNumber δ_n.toNNReal
        ((config_P0.image dyadicSquareCenter : Set Plane) ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal (Real.rpow δ_n (-ε)) * (ENNReal.ofReal r) ^ u *
        (Metric.externalCoveringNumber δ_n.toNNReal (config_P0.image dyadicSquareCenter : Set Plane) : ENNReal) := by
    calc (Metric.externalCoveringNumber δ_n.toNNReal
          ((config_P0.image dyadicSquareCenter : Set Plane) ∩ Metric.closedBall x r) : ENNReal)
      ≤ ENNReal.ofReal (C' * 625 * (2 : ℝ)^u) * (ENNReal.ofReal r) ^ u *
          (Metric.externalCoveringNumber δ_n.toNNReal (config_P0.image dyadicSquareCenter : Set Plane) : ENNReal) := h6
    _ ≤ ENNReal.ofReal (Real.rpow δ_n (-ε)) * (ENNReal.ofReal r) ^ u *
          (Metric.externalCoveringNumber δ_n.toNNReal (config_P0.image dyadicSquareCenter : Set Plane) : ENNReal) := by
      gcongr
  exact h_goal

/-- Weaken the strong S-set constant δ_n^{-ε} to δ_n^{-2ε} for B1BridgeDecomposition. -/
lemma b1_hPfin_sset
    {n : ℕ} {δ_n u ε ρ_mass C_Pbar : ℝ}
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hu_nonneg : 0 ≤ u) (hε_pos : 0 < ε)
    (hC_Pbar_pos : 0 < C_Pbar)
    (hρ_mass_nonneg : 0 ≤ ρ_mass)
    {Pbar : Finset Plane}
    {P_oriented : Set Plane}
    {config_P0 : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    (hconfig_P0_nonempty : config_P0.Nonempty)
    (hPbar_sset : IsDeltaSSet δ_n u C_Pbar (Pbar : Set Plane))
    (hPbar_sep : Set.Pairwise (Pbar : Set Plane) (fun p q => δ_n ≤ dist p q))
    (hP_oriented_sub_Pbar : P_oriented ⊆ (Pbar : Set Plane))
    (hP_oriented_sub_pointSet : P_oriented ⊆
        ⋃ p ∈ (config_P0 : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)),
          (p.toSet : Set Plane))
    (h_squares_meet : ∀ q ∈ config_P0,
        ((q.toSet : Set Plane) ∩ P_oriented).Nonempty)
    (h_ncover_lower : (Metric.externalCoveringNumber δ_n.toNNReal
          (⋃ p ∈ (config_P0 : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)),
            (p.toSet : Set Plane)) : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ_n ρ_mass) *
          (Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set Plane)))
    (h_absorb : (25 : ℝ) * 625 * (2 : ℝ)^u * Real.rpow δ_n (-ρ_mass) * C_Pbar ≤
        Real.rpow δ_n (-ε)) :
    IsDeltaSSet δ_n u (Real.rpow δ_n (-2 * ε))
      (config_P0.image dyadicSquareCenter : Set Plane) := by
  have h_strong : IsDeltaSSet δ_n u (Real.rpow δ_n (-ε))
      (config_P0.image dyadicSquareCenter : Set Plane) :=
    b1_hPfin_sset_strong hδ_n_pos hδ_n_eq hu_nonneg hε_pos hC_Pbar_pos hρ_mass_nonneg
      hconfig_P0_nonempty hPbar_sset hPbar_sep hP_oriented_sub_Pbar hP_oriented_sub_pointSet
      h_squares_meet h_ncover_lower h_absorb
  have hδ_n_le_one : δ_n ≤ 1 := by
    rw [hδ_n_eq]
    exact dyadicDelta_le_one n
  have h_weaken : Real.rpow δ_n (-ε) ≤ Real.rpow δ_n (-2 * ε) := by
    have h1 : -2 * ε ≤ -ε := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ_n_pos hδ_n_le_one h1
  rcases h_strong with ⟨hne, hδ, hC_pos, hs, hmain⟩
  have hC_new_pos : 0 < Real.rpow δ_n (-2 * ε) := Real.rpow_pos_of_pos hδ_n_pos _
  refine ⟨hne, hδ, hC_new_pos, hs, fun x r hr => ?_⟩
  have h6 := hmain x r hr
  have h7 : ENNReal.ofReal (Real.rpow δ_n (-ε)) ≤
      ENNReal.ofReal (Real.rpow δ_n (-2 * ε)) := ENNReal.ofReal_le_ofReal h_weaken
  calc (Metric.externalCoveringNumber δ_n.toNNReal
        ((config_P0.image dyadicSquareCenter : Set Plane) ∩ Metric.closedBall x r) : ENNReal)
    ≤ ENNReal.ofReal (Real.rpow δ_n (-ε)) * (ENNReal.ofReal r) ^ u *
        (Metric.externalCoveringNumber δ_n.toNNReal (config_P0.image dyadicSquareCenter : Set Plane) : ENNReal) := h6
  _ ≤ ENNReal.ofReal (Real.rpow δ_n (-2 * ε)) * (ENNReal.ofReal r) ^ u *
        (Metric.externalCoveringNumber δ_n.toNNReal (config_P0.image dyadicSquareCenter : Set Plane) : ENNReal) := by
    gcongr

/-! ### 2. Ball growth on centers (`hP_ball_growth`) -/

/-- Ball growth bound on dyadic square centers.

    Uses the STRONG centers S-set (constant δ_n^{-ε}) plus `sset_ball_growth`.
    With δ_n = Δ², we have δ_n^{-ε} = Δ^{-2ε}, and absorption gives:
    25 · Δ^{-2ε} ≤ Δ^{-9ε/4} iff 25 ≤ Δ^{-ε/4}, true for small Δ. -/
lemma b1_hP_ball_growth
    {n : ℕ} {δ_n Δ u ε : ℝ}
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hu_nonneg : 0 ≤ u) (hε_pos : 0 < ε)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_le_Δ : δ_n ≤ Δ)
    {config_P0 : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    (hcenters_sset_strong : IsDeltaSSet δ_n u (Real.rpow δ_n (-ε))
        (config_P0.image dyadicSquareCenter : Set Plane))
    (h_absorb : (25 : ℝ) * Real.rpow δ_n (-ε) ≤ Real.rpow Δ (-9 * ε / 4)) :
    ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((config_P0.image dyadicSquareCenter).filter (fun y => dist c y ≤ r)).card ≤
        Real.rpow Δ (-9 * ε / 4) * r^u * (config_P0.image dyadicSquareCenter).card := by
  let centers : Finset Plane := config_P0.image dyadicSquareCenter
  have h_sep : Set.Pairwise (centers : Set Plane) (fun p q => δ_n ≤ dist p q) := by
    have h := dyadicSquareCenters_separated config_P0
    simpa [centers, SSetBridges.SeparatedAt, hδ_n_eq] using h
  have hC_pos : 0 < Real.rpow δ_n (-ε) := Real.rpow_pos_of_pos hδ_n_pos _
  have h_main : ∀ (c : Plane) (r : ℝ), δ_n ≤ r →
      ((centers.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        (25 : ℝ) * Real.rpow δ_n (-ε) * r^u * (centers.card : ℝ) :=
    sset_ball_growth hδ_n_pos hu_nonneg hC_pos h_sep hcenters_sset_strong
  intro c r hr
  have hδ_n_le_r : δ_n ≤ r := le_trans hδ_n_le_Δ hr
  have h1 := h_main c r hδ_n_le_r
  have h2 : (25 : ℝ) * Real.rpow δ_n (-ε) * r^u * (centers.card : ℝ) ≤
      Real.rpow Δ (-9 * ε / 4) * r^u * (centers.card : ℝ) := by
    have h3 : 0 ≤ r^u := Real.rpow_nonneg (by linarith) u
    have h4 : 0 ≤ (centers.card : ℝ) := by positivity
    nlinarith
  exact_mod_cast (le_trans h1 h2)

end DirecretisedFurstenbergEstimate.FrontEndLemmas.B1HardFields

end
