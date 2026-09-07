module

/-
  Proof skeleton for robust_kaufman_projection.
  Developed in .scratch/marlin/.
-/

public import MyLeanRepo.robust_kaufman_projection.Base
public import MyLeanRepo.robust_kaufman_projection.Packing
public import MyLeanRepo.robust_kaufman_projection.PlaneEnergy
public import MyLeanRepo.robust_kaufman_projection.Refinement
public import MyLeanRepo.robust_kaufman_projection.GoodDirections
public import MyLeanRepo.robust_kaufman_projection.Helpers
public import MyLeanRepo.robust_kaufman_projection.CoveringWitness
public import MyLeanRepo.robust_kaufman_projection.EnergyAveraging
public import MyLeanRepo.robust_kaufman_projection.Arithmetic
public import MyLeanRepo.robust_kaufman_projection.PolynomialAbsorption
public import MyLeanRepo.robust_kaufman_projection.GenericRefinement
public import MyLeanRepo.robust_kaufman_projection.AbsorptionBounds
public import MyLeanRepo.robust_kaufman_projection.HausdorffContentToDeltaSet
public import MyLeanRepo.robust_kaufman_projection.RestrictionFrostman
public import MyLeanRepo.robust_kaufman_projection.PerturbationGeneral
public import MyLeanRepo.robust_kaufman_projection.PolynomialAbsorption
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

namespace RobustKaufmanProjection.Dune

open RobustKaufmanProjection.EnergyAveraging
open RobustKaufmanProjection.RestrictionFrostman
open RobustKaufmanProjection.HausdorffContentToDeltaSet
open RobustKaufmanProjection.PerturbationGeneral

open MeasureTheory Metric Set Finset Classical

abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem IsDeltaSSet.extract_plane {δ t C : ℝ} {P : Set EuclideanPlane}
    (h : IsDeltaSSet δ t C P) (hP_bounded : Bornology.IsBounded P) :
    ∃ (S : Finset EuclideanPlane),
      (S : Set EuclideanPlane) ⊆ P ∧
      S.Nonempty ∧
      IsSeparated δ.toNNReal (S : Set EuclideanPlane) ∧
      (∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ ‖p - q‖) ∧
      IsCover δ.toNNReal P (S : Set EuclideanPlane) ∧
      (Ncover δ P ≤ (S.card : ENNReal)) ∧
      (∀ p ∈ S, ∀ r : ℝ, δ ≤ r →
        (S.filter (fun q => ‖p - q‖ ≤ r)).card ≤ (9 * C) * r ^ t * S.card) := by
  have hδpos : 0 < δ := h.2.1
  have hCpos : 0 < C := h.2.2.1
  have ht_nonneg : 0 ≤ t := h.2.2.2.1
  have hPnonempty : P.Nonempty := h.1
  let δ' : NNReal := ⟨δ, hδpos.le⟩
  have hδ'_co : (δ' : ℝ) = δ := by rfl
  have hP_tb : TotallyBounded P := by
    rcases hP_bounded.subset_closedBall (0 : EuclideanPlane) with ⟨R, hR⟩
    exact (isCompact_closedBall (0 : EuclideanPlane) R).totallyBounded.subset hR
  have hδ'pos : 0 < δ' := by exact_mod_cast hδpos
  have h_ec_ne_top : externalCoveringNumber (δ' / 2) P ≠ ⊤ := by
    have hhalf_pos : 0 < δ' / 2 := by
      have h : (δ' : ℝ) > 0 := by exact_mod_cast hδpos
      have h2 : (δ' / 2 : ℝ) > 0 := by linarith
      exact_mod_cast h2
    rcases exists_finite_isCover_of_totallyBounded hhalf_pos.ne' hP_tb with ⟨N, _, hNfin, hNcover⟩
    have h : externalCoveringNumber (δ' / 2) P ≤ N.encard := IsCover.externalCoveringNumber_le_encard hNcover
    exact ne_top_of_le_ne_top (by exact encard_ne_top_iff.mpr hNfin) h
  have hmul : 2 * (δ' / 2) = δ' := by
    apply NNReal.coe_injective; simp [hδ'_co] <;> ring
  have h_pack_ne_top : packingNumber δ' P ≠ ⊤ := by
    have h : packingNumber (2 * (δ' / 2)) P ≤ externalCoveringNumber (δ' / 2) P :=
      packingNumber_two_mul_le_externalCoveringNumber (δ' / 2) P
    rw [hmul] at h; exact ne_top_of_le_ne_top h_ec_ne_top h
  let S : Set EuclideanPlane := maximalSeparatedSet δ' P
  have hS_subset : S ⊆ P := maximalSeparatedSet_subset
  have hS_sep : IsSeparated δ' S := isSeparated_maximalSeparatedSet
  have hS_encard : S.encard = packingNumber δ' P := encard_maximalSeparatedSet h_pack_ne_top
  have hS_cover : IsCover δ' P S := isCover_maximalSeparatedSet h_pack_ne_top
  have hS_finite : S.Finite := by
    have h : S.encard ≠ ⊤ := by rw [hS_encard] <;> exact h_pack_ne_top
    exact encard_ne_top_iff.mp h
  have hS_nonempty : S.Nonempty := hS_cover.nonempty hPnonempty
  classical
  let Sfin : Finset EuclideanPlane := hS_finite.toFinset
  have hSfin_eq : (Sfin : Set EuclideanPlane) = S := by simp [Sfin]
  have hSfin_card : S.encard = ↑Sfin.card := by rw [← hSfin_eq] <;> simp
  have hSfin_pos : 0 < Sfin.card := by
    have h : 0 < packingNumber δ' P := packingNumber_pos_iff.mpr hPnonempty
    have h2 : 0 < S.encard := by rw [hS_encard]; exact h
    have h3 : S.encard = ↑Sfin.card := hSfin_card
    rw [h3] at h2
    exact_mod_cast h2
  have hδ'_eq : δ' = δ.toNNReal := by ext <;> simp [δ', hδ'_co] <;> linarith
  have hNcover_le : Ncover δ P ≤ (Sfin.card : ENNReal) := by
    have h1 : externalCoveringNumber δ' P ≤ S.encard := IsCover.externalCoveringNumber_le_encard hS_cover
    have hδ'_eq2 : δ' = δ.toNNReal := hδ'_eq
    rw [hδ'_eq2] at h1
    have h2 : (externalCoveringNumber δ.toNNReal P : ENNReal) ≤ (S.encard : ENNReal) := by exact_mod_cast h1
    have h3 : (S.encard : ENNReal) = (Sfin.card : ENNReal) := by rw [hSfin_card] <;> simp
    rw [h3] at h2
    simpa [Ncover] using h2
  have h_sep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ ‖p - q‖ := by
    intro p hp q hq hne
    have h_edist : (δ' : ENNReal) < edist p q := hS_sep hp hq hne
    have h_dist : edist p q = ENNReal.ofReal ‖p - q‖ := by rw [edist_dist] <;> rfl
    rw [h_dist] at h_edist
    have h_coe : (↑δ' : ENNReal) = ENNReal.ofReal (δ' : ℝ) := by simp
    rw [h_coe] at h_edist
    have h_pos : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h' : ENNReal.ofReal (δ' : ℝ) < ENNReal.ofReal ‖p - q‖ := h_edist
    have h'' : (δ' : ℝ) < ‖p - q‖ := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h'
    rw [hδ'_co] at h''; exact le_of_lt h''
  have h_ball_growth : ∀ p ∈ S, ∀ r : ℝ, δ ≤ r →
      (Sfin.filter (fun q => ‖p - q‖ ≤ r)).card ≤ (9 * C) * r ^ t * Sfin.card := by
    intro p hp r hr
    have hrpos : 0 < r := by linarith
    have hrnonneg : 0 ≤ r := by linarith
    let B : Set EuclideanPlane := closedBall p r
    let T : Finset EuclideanPlane := Sfin.filter (fun q => ‖p - q‖ ≤ r)
    have hT_eq : (T : Set EuclideanPlane) = S ∩ B := by
      ext x; have h_xin : x ∈ Sfin ↔ x ∈ S := by rw [← hSfin_eq] <;> simp
      simp only [T, Finset.mem_coe, Finset.mem_filter, h_xin, Set.mem_inter_iff, Set.mem_setOf_eq]
      have hB : x ∈ B ↔ ‖x - p‖ ≤ r := by simp [B, dist_eq_norm]
      have h_comm : ‖x - p‖ = ‖p - x‖ := by exact norm_sub_rev x p
      constructor
      · rintro ⟨h1, h2⟩
        have h3 : ‖x - p‖ ≤ r := by rw [h_comm]; exact h2
        exact ⟨h1, hB.mpr h3⟩
      · rintro ⟨h1, h2⟩
        have h3 : ‖x - p‖ ≤ r := hB.mp h2
        have h4 : ‖p - x‖ ≤ r := by rw [←h_comm]; exact h3
        exact ⟨h1, h4⟩
    have hT_subset_PB : (T : Set EuclideanPlane) ⊆ P ∩ B := by
      rw [hT_eq]; intro y hy; exact ⟨hS_subset hy.1, hy.2⟩
    have hT_sep : IsSeparated δ' (T : Set EuclideanPlane) := by
      rw [hT_eq]; exact IsSeparated.subset (fun y hy => hy.1) hS_sep
    have h1 : (T : Set EuclideanPlane).encard ≤ packingNumber δ' (P ∩ B) :=
      IsSeparated.encard_le_packingNumber hT_subset_PB hT_sep
    have h2 : packingNumber δ' (P ∩ B) ≤ externalCoveringNumber (δ' / 2) (P ∩ B) := by
      have h2' : packingNumber (2 * (δ' / 2)) (P ∩ B) ≤ externalCoveringNumber (δ' / 2) (P ∩ B) :=
        packingNumber_two_mul_le_externalCoveringNumber (δ' / 2) (P ∩ B)
      rw [hmul] at h2'; exact h2'
    have h3 : externalCoveringNumber (δ' / 2) (P ∩ B) ≤ 9 * externalCoveringNumber δ' (P ∩ B) :=
      externalCoveringNumber_half_le_plane (P ∩ B) δ'
    have h4 : (externalCoveringNumber δ' (P ∩ B) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (externalCoveringNumber δ' P : ENNReal) := by
      have h5 := h.2.2.2.2 p r hr; rw [hδ'_eq] at *; exact h5
    have h5 : externalCoveringNumber δ' P ≤ S.encard := IsCover.externalCoveringNumber_le_encard hS_cover
    have h_rpow : (ENNReal.ofReal r) ^ t = ENNReal.ofReal (r ^ t) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hrnonneg ht_nonneg]
    have h9C : (9 : ENNReal) * ENNReal.ofReal C = ENNReal.ofReal (9 * C) := by
      have h11 : 0 ≤ C := by linarith
      have h12 : ENNReal.ofReal (9 * C) = (9 : ENNReal) * ENNReal.ofReal C := by
        simp [ENNReal.ofReal_mul h11] <;> norm_num
      exact h12.symm
    have h6 : (↑T.card : ENNReal) ≤
        ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ t) * (↑Sfin.card : ENNReal) := by
      have h1' : (↑T.card : ENNReal) ≤ ↑(packingNumber δ' (P ∩ B)) := by
        have h_eq : (T : Set EuclideanPlane).encard = ↑T.card := by simp
        rw [h_eq] at h1; exact_mod_cast h1
      have h2' : (↑(packingNumber δ' (P ∩ B)) : ENNReal) ≤ ↑(externalCoveringNumber (δ' / 2) (P ∩ B)) := by exact_mod_cast h2
      have h3' : ↑(externalCoveringNumber (δ' / 2) (P ∩ B)) ≤ (9 : ENNReal) * ↑(externalCoveringNumber δ' (P ∩ B)) := by exact_mod_cast h3
      have h4' : (↑(externalCoveringNumber δ' (P ∩ B)) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal) := by
        calc
          (↑(externalCoveringNumber δ' (P ∩ B)) : ENNReal)
            ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑(externalCoveringNumber δ' P) : ENNReal) := h4
          _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal) := by
            gcongr; exact_mod_cast le_trans h5 (le_of_eq hSfin_card)
      calc
        (↑T.card : ENNReal)
          ≤ ↑(packingNumber δ' (P ∩ B)) := h1'
        _ ≤ ↑(externalCoveringNumber (δ' / 2) (P ∩ B)) := h2'
        _ ≤ (9 : ENNReal) * ↑(externalCoveringNumber δ' (P ∩ B)) := h3'
        _ ≤ (9 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal)) := by gcongr
        _ = ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ t) * (↑Sfin.card : ENNReal) := by
          have h_eq : (9 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal)) =
              ((9 : ENNReal) * ENNReal.ofReal C) * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal) := by ring
          rw [h_eq, h9C, h_rpow] <;> ring
    have h_bound_real : 0 ≤ (9 * C) * r ^ t * (Sfin.card : ℝ) := by positivity
    have h8 : ENNReal.ofReal ((9 * C) * r ^ t * (Sfin.card : ℝ)) =
        ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ t) * (↑Sfin.card : ENNReal) := by
      have h_pos1 : 0 ≤ 9 * C := by positivity
      have h_pos2 : 0 ≤ r ^ t := by positivity
      have h_pos3 : 0 ≤ (Sfin.card : ℝ) := by positivity
      have h_parse : (9 * C) * r ^ t * (Sfin.card : ℝ) = (9 * C) * (r ^ t * (Sfin.card : ℝ)) := by ring
      rw [h_parse, ENNReal.ofReal_mul h_pos1, ENNReal.ofReal_mul h_pos2]
      <;> simp [mul_assoc] <;> ring
    have h9 : (↑T.card : ENNReal) ≤ ENNReal.ofReal ((9 * C) * r ^ t * (Sfin.card : ℝ)) := by
      rw [h8]; exact h6
    have h10 : ENNReal.ofReal (↑T.card : ℝ) ≤ ENNReal.ofReal ((9 * C) * r ^ t * (Sfin.card : ℝ)) := by
      have h11 : (↑T.card : ENNReal) = ENNReal.ofReal (↑T.card : ℝ) := by simp
      rw [h11] at h9; exact h9
    have h_iff : ENNReal.ofReal (↑T.card : ℝ) ≤ ENNReal.ofReal ((9 * C) * r ^ t * (Sfin.card : ℝ)) ↔
        (↑T.card : ℝ) ≤ (9 * C) * r ^ t * (Sfin.card : ℝ) :=
      ENNReal.ofReal_le_ofReal_iff h_bound_real
    exact h_iff.mp h10
  have hSfin_nonempty : Sfin.Nonempty := by
    have h : (Sfin : Set EuclideanPlane).Nonempty := by rw [hSfin_eq]; exact hS_nonempty
    exact (Finite.toFinset_nonempty hS_finite).mpr hS_nonempty
  have h_sep' : ∀ p ∈ Sfin, ∀ q ∈ Sfin, p ≠ q → δ ≤ ‖p - q‖ := by
    intro p hp q hq hne
    have hp' : p ∈ S := by rw [← hSfin_eq]; exact hp
    have hq' : q ∈ S := by rw [← hSfin_eq]; exact hq
    exact h_sep p hp' q hq' hne
  have h_ball_growth' : ∀ p ∈ Sfin, ∀ r : ℝ, δ ≤ r →
      (Sfin.filter (fun q => ‖p - q‖ ≤ r)).card ≤ (9 * C) * r ^ t * Sfin.card := by
    intro p hp r hr
    have hp' : p ∈ S := by rw [← hSfin_eq]; exact hp
    exact h_ball_growth p hp' r hr
  have hS_cover' : IsCover δ.toNNReal P (Sfin : Set EuclideanPlane) := by
    have h : IsCover δ' P S := hS_cover
    have hδ'_eq2 : δ' = δ.toNNReal := hδ'_eq
    rw [hδ'_eq2] at h
    rw [←hSfin_eq] at h
    exact h
  have hS_is_sep : IsSeparated δ.toNNReal (Sfin : Set EuclideanPlane) := by
    have hδ'_eq2 : δ' = δ.toNNReal := hδ'_eq
    rw [hδ'_eq2] at hS_sep
    simpa [hSfin_eq] using hS_sep
  exact ⟨Sfin, by simpa [hSfin_eq] using hS_subset, hSfin_nonempty, hS_is_sep, h_sep', hS_cover', hNcover_le, h_ball_growth'⟩

/-- A δ-separated subset S ⊆ P has cardinality at most 9 * Ncover δ P. -/
lemma card_le_nine_ncover {δ : ℝ} {P : Set EuclideanPlane}
    (S : Finset EuclideanPlane) (hS_subset : (S : Set EuclideanPlane) ⊆ P)
    (hS_sep : IsSeparated δ.toNNReal (S : Set EuclideanPlane))
    (hδ : 0 < δ) :
    (S.card : ENNReal) ≤ 9 * Ncover δ P := by
  let δ' : NNReal := δ.toNNReal
  have hδ'_co : (δ' : ℝ) = δ := by simp [δ'] <;> linarith
  have h1 : (S : Set EuclideanPlane).encard ≤ packingNumber δ' P :=
    IsSeparated.encard_le_packingNumber hS_subset hS_sep
  have hmul : 2 * (δ' / 2) = δ' := by
    apply NNReal.coe_injective; simp [hδ'_co] <;> ring
  have h2 : packingNumber δ' P ≤ externalCoveringNumber (δ' / 2) P := by
    have h2' : packingNumber (2 * (δ' / 2)) P ≤ externalCoveringNumber (δ' / 2) P :=
      packingNumber_two_mul_le_externalCoveringNumber (δ' / 2) P
    rw [hmul] at h2'; exact h2'
  have h3 : externalCoveringNumber (δ' / 2) P ≤ 9 * externalCoveringNumber δ' P :=
    externalCoveringNumber_half_le_plane P δ'
  have hδ'_eq : δ' = δ.toNNReal := by ext <;> simp [δ', hδ'_co] <;> linarith
  calc
    (S.card : ENNReal) = (S : Set EuclideanPlane).encard := by simp
    _ ≤ ↑(packingNumber δ' P) := by exact_mod_cast h1
    _ ≤ ↑(externalCoveringNumber (δ' / 2) P) := by exact_mod_cast h2
    _ ≤ (9 : ENNReal) * ↑(externalCoveringNumber δ' P) := by exact_mod_cast h3
    _ = 9 * Ncover δ P := by
      rw [hδ'_eq]; simp [Ncover] <;> ring

/-! ### Uniform measure -/

/-- Uniform probability measure on a finset. -/
noncomputable def uniformMeasure {X : Type*} [MeasurableSpace X] (S : Finset X) : Measure X :=
  (S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set X)

lemma sfinite_count_restrict_finset' {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (S : Finset X) : SFinite (Measure.count.restrict (S : Set X)) :=
  RobustKaufmanProjection.Refinement.sfinite_count_restrict_finset S

/-- Lintegral over count measure restricted to a finset equals the finite sum. -/
lemma lintegral_count_restrict_finset {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (S : Finset X) (f : X → ENNReal) :
    ∫⁻ x, f x ∂(Measure.count.restrict (S : Set X)) = ∑ x ∈ S, f x := by
  have h_eq : Measure.count.restrict (S : Set X) =
      Finset.sum S (fun x => Measure.dirac x) := by
    ext A hA
    have h1 : Measure.count.restrict (S : Set X) A = Measure.count (A ∩ (S : Set X)) := by
      rw [Measure.restrict_apply hA]
    have h_sum_apply : (Finset.sum S (fun x => Measure.dirac x)) A = ∑ x ∈ S, (Measure.dirac x) A := by
      have h_ind : ∀ (T : Finset X), (Finset.sum T (fun x => Measure.dirac x)) A = ∑ x ∈ T, (Measure.dirac x) A := by
        intro T
        induction T using Finset.induction with
        | empty => simp
        | @insert x T hx ih =>
          rw [Finset.sum_insert hx, Measure.add_apply, ih, Finset.sum_insert hx] <;> ring
      exact h_ind S
    rw [h1, h_sum_apply]
    have h_meas' : MeasurableSet (A ∩ (S : Set X)) := hA.inter (Finset.measurableSet S)
    have h_set : (A ∩ (S : Set X)) = (S.filter (fun x => x ∈ A) : Set X) := by
      ext y; simp [Finset.mem_filter] <;> tauto
    have h3 : Measure.count (A ∩ (S : Set X)) = ↑(S.filter (fun x => x ∈ A)).card := by
      rw [Measure.count_apply h_meas']
      have h4 : (A ∩ (S : Set X)).encard = (S.filter (fun x => x ∈ A)).card := by
        rw [h_set]
        exact Set.encard_coe_eq_coe_finsetCard (S.filter (fun x => x ∈ A))
      exact_mod_cast h4
    have h5 : ∑ x ∈ S, (Measure.dirac x) A = ↑(S.filter (fun x => x ∈ A)).card := by
      have h6 : ∀ x ∈ S, (Measure.dirac x) A = if x ∈ A then (1 : ENNReal) else 0 := by
        intro x _
        simp [Measure.dirac_apply, Set.indicator_apply]
        <;> split_ifs <;> simp
      rw [Finset.sum_congr rfl h6]
      simp [Finset.sum_ite]
      <;> norm_cast
    rw [h3, h5]
  rw [h_eq]
  have h_ind : ∀ (T : Finset X), ∫⁻ x, f x ∂(Finset.sum T (fun x => Measure.dirac x)) = ∑ x ∈ T, f x := by
    intro T
    induction T using Finset.induction with
    | empty => simp
    | @insert x T hx ih =>
      rw [Finset.sum_insert hx, lintegral_add_measure, ih, lintegral_dirac, Finset.sum_insert hx] <;> ring
  exact h_ind S

lemma refinement_cover_density
    {δ ρ : ℝ} {P P' : Set EuclideanPlane}
    {S_P : Finset EuclideanPlane}
    (hS_P_nonempty : S_P.Nonempty)
    (hS_P_sub : (S_P : Set EuclideanPlane) ⊆ P)
    (hS_P_strict_sep : IsSeparated δ.toNNReal (S_P : Set EuclideanPlane))
    (hS_P_cover : IsCover δ.toNNReal P (S_P : Set EuclideanPlane))
    (hP'_sub : P' ⊆ P)
    (hP'_density : ENNReal.ofReal (δ ^ ρ) * Ncover δ P ≤ Ncover δ P')
    (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ (S_P' : Finset EuclideanPlane),
      S_P' ⊆ S_P ∧
      S_P'.Nonempty ∧
      (∀ x ∈ S_P', ∃ p ∈ P', dist x p ≤ δ) ∧
      ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) ≤ (9 : ENNReal) * (S_P'.card : ENNReal) := by
  let S_P' : Finset EuclideanPlane := S_P.filter (fun p => ∃ q ∈ P', ‖p - q‖ ≤ δ)
  have hS_P'_sub : S_P' ⊆ S_P := Finset.filter_subset _ _
  have hS_P'_covers_P' : IsCover δ.toNNReal P' (S_P' : Set EuclideanPlane) := by
    rw [isCover_iff_subset_iUnion_closedBall]
    intro q hq
    have hqP : q ∈ P := hP'_sub hq
    have h1 : q ∈ (⋃ p ∈ (S_P : Set Plane), closedBall p δ.toNNReal) :=
      (isCover_iff_subset_iUnion_closedBall.mp hS_P_cover) hqP
    rcases Set.mem_iUnion₂.mp h1 with ⟨p, hpS, hdist⟩
    have hdist' : ‖p - q‖ ≤ δ := by
      have h : dist q p ≤ (δ.toNNReal : ℝ) := hdist
      have h2 : (δ.toNNReal : ℝ) = δ := by
        simp [hδ.le] <;> linarith
      rw [h2] at h
      have h3 : dist q p = ‖q - p‖ := by simp [dist_eq_norm]
      rw [h3] at h
      rw [norm_sub_rev] at h
      exact h
    have hpS' : p ∈ S_P' := by
      simp only [S_P', Finset.mem_filter]
      refine ⟨hpS, ?_⟩
      exact ⟨q, hq, hdist'⟩
    exact Set.mem_iUnion₂.mpr ⟨p, hpS', hdist⟩
  have hNcover_P'_le : Ncover δ P' ≤ (S_P'.card : ENNReal) := by
    have h1 : externalCoveringNumber δ.toNNReal P' ≤ (S_P' : Set Plane).encard :=
      IsCover.externalCoveringNumber_le_encard hS_P'_covers_P'
    have h2 : (S_P' : Set Plane).encard = ↑S_P'.card := by simp
    rw [h2] at h1
    have h3 : (↑(externalCoveringNumber δ.toNNReal P') : ENNReal) ≤ (↑S_P'.card : ENNReal) := by
      exact_mod_cast h1
    simpa [Ncover] using h3
  have hS_P_le_ncover : (S_P.card : ENNReal) ≤ 9 * Ncover δ P :=
    card_le_nine_ncover S_P hS_P_sub hS_P_strict_sep hδ
  have h_step1 : ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) ≤
      ENNReal.ofReal (δ ^ ρ) * (9 * Ncover δ P) := by gcongr
  have h_step2 : ENNReal.ofReal (δ ^ ρ) * (9 * Ncover δ P) =
      9 * (ENNReal.ofReal (δ ^ ρ) * Ncover δ P) := by ring
  have h_step3 : 9 * (ENNReal.ofReal (δ ^ ρ) * Ncover δ P) ≤ 9 * Ncover δ P' := by
    exact mul_le_mul_of_nonneg_left hP'_density (by simp)
  have h_step4 : 9 * Ncover δ P' ≤ 9 * (S_P'.card : ENNReal) := by
    exact mul_le_mul_of_nonneg_left hNcover_P'_le (by simp)
  have hS_P'_density : ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) ≤
      (9 : ENNReal) * (S_P'.card : ENNReal) :=
    le_trans h_step1 (le_trans (Eq.le h_step2) (le_trans h_step3 h_step4))
  have hδρ_pos : 0 < δ ^ ρ := by positivity
  have hS_P_card_pos : 0 < S_P.card := hS_P_nonempty.card_pos
  have hS_P_card_pos' : 0 < (S_P.card : ENNReal) := by exact_mod_cast hS_P_card_pos
  have h_pos : (0 : ENNReal) < ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) := by
    positivity
  have hS_P'_nonempty : S_P'.Nonempty := by
    by_cases h : S_P'.Nonempty
    · exact h
    · have h4 : S_P'.card = 0 := by simpa [Finset.not_nonempty_iff_eq_empty] using h
      have h5 : (S_P'.card : ENNReal) = 0 := by
        exact_mod_cast h4
      rw [h5] at hS_P'_density
      have h61 : (9 : ENNReal) * (0 : ENNReal) = 0 := by simp
      rw [h61] at hS_P'_density
      have h6 : ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) ≤ 0 := hS_P'_density
      have h7 : ¬ (ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) ≤ 0) := by
        exact Std.not_le.mpr h_pos
      exact False.elim (h7 h6)
  have hS_P'_near : ∀ x ∈ S_P', ∃ p ∈ P', dist x p ≤ δ := by
    intro x hx
    have h1 : x ∈ S_P ∧ ∃ q ∈ P', ‖x - q‖ ≤ δ := by
      simpa [S_P', Finset.mem_filter] using hx
    have h2 : ∃ q ∈ P', ‖x - q‖ ≤ δ := h1.2
    rcases h2 with ⟨p, hp, hnorm⟩
    have hdist : dist x p ≤ δ := by
      have h : dist x p = ‖x - p‖ := by simp [dist_eq_norm]
      rw [h]; exact hnorm
    exact ⟨p, hp, hdist⟩
  exact ⟨S_P', hS_P'_sub, hS_P'_nonempty, hS_P'_near, hS_P'_density⟩

/-- From density bound δ^ρ · |S_P| ≤ 9 · |S_P'|, derive ratio |S_P|/|S_P'| ≤ 9·δ^{-ρ}. -/
lemma refinement_ratio_bound
    {δ ρ : ℝ} {S_P S_P' : Finset EuclideanPlane}
    (hS_P'_nonempty : S_P'.Nonempty)
    (hS_P'_density : ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) ≤ (9 : ENNReal) * (S_P'.card : ENNReal))
    (hδ : 0 < δ) (hρ : 0 < ρ) :
    (S_P.card : ENNReal) / (S_P'.card : ENNReal) ≤ ENNReal.ofReal (9 * δ ^ (-ρ)) := by
  set b : ENNReal := (S_P'.card : ENNReal) with hb_def
  set c : ENNReal := ENNReal.ofReal (9 * δ ^ (-ρ)) with hc_def
  have hb_ne_zero : b ≠ 0 := by
    have h : 0 < S_P'.card := hS_P'_nonempty.card_pos
    have h2 : (0 : ENNReal) < (S_P'.card : ENNReal) := by exact_mod_cast h
    have h' : (0 : ENNReal) < b := by
      rw [hb_def]
      exact h2
    exact h'.ne'
  have hb_ne_top : b ≠ ⊤ := ENNReal.coe_ne_top
  have hδ' : 0 ≤ δ := le_of_lt hδ
  have h_inv_mul : ENNReal.ofReal (δ ^ (-ρ)) * ENNReal.ofReal (δ ^ ρ) = 1 := by
    have h1 : 0 ≤ δ ^ (-ρ) := by positivity
    have h3 : δ ^ (-ρ) * δ ^ ρ = 1 := by
      have h4 : δ ^ ((-ρ) + ρ) = δ ^ (-ρ) * δ ^ ρ := Real.rpow_add hδ (-ρ) ρ
      have h5 : (-ρ) + ρ = 0 := by ring
      rw [h5] at h4
      have h6 : δ ^ (0 : ℝ) = 1 := by simp
      rw [h6] at h4
      exact h4.symm
    rw [← ENNReal.ofReal_mul h1, h3] <;> simp
  have h9mul : ENNReal.ofReal (δ ^ (-ρ)) * (9 : ENNReal) = c := by
    have h1 : 0 ≤ δ ^ (-ρ) := by positivity
    have h2 : ENNReal.ofReal (9 * δ ^ (-ρ)) = ENNReal.ofReal (δ ^ (-ρ)) * (9 : ENNReal) := by
      have hpos : 0 ≤ δ ^ (-ρ) := by positivity
      have h4 : 9 * δ ^ (-ρ) = δ ^ (-ρ) * 9 := by ring
      rw [h4]
      have h5 : ENNReal.ofReal (δ ^ (-ρ) * 9) = ENNReal.ofReal (δ ^ (-ρ)) * ENNReal.ofReal (9 : ℝ) := by
        rw [ENNReal.ofReal_mul hpos]
      rw [h5]
      <;> simp
    rw [hc_def, h2] <;> ring
  have h_goal : (S_P.card : ENNReal) ≤ c * b := by
    have h2 : ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) ≤ (9 : ENNReal) * b := by
      simpa [hb_def] using hS_P'_density
    have h3 : ENNReal.ofReal (δ ^ (-ρ)) * (ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal)) ≤
        ENNReal.ofReal (δ ^ (-ρ)) * ((9 : ENNReal) * b) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : ENNReal.ofReal (δ ^ (-ρ)) * (ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal)) =
        (ENNReal.ofReal (δ ^ (-ρ)) * ENNReal.ofReal (δ ^ ρ)) * (S_P.card : ENNReal) := by ring
    rw [h4] at h3
    rw [h_inv_mul] at h3
    have h5 : (1 : ENNReal) * (S_P.card : ENNReal) = (S_P.card : ENNReal) := by simp
    rw [h5] at h3
    have h6 : ENNReal.ofReal (δ ^ (-ρ)) * ((9 : ENNReal) * b) =
        (ENNReal.ofReal (δ ^ (-ρ)) * (9 : ENNReal)) * b := by ring
    rw [h6] at h3
    rw [h9mul] at h3
    exact h3
  have h7 : (S_P.card : ENNReal) / b ≤ c := by
    have h_def : (S_P.card : ENNReal) / b = (S_P.card : ENNReal) * b⁻¹ := by rfl
    rw [h_def]
    have h : (S_P.card : ENNReal) * b⁻¹ ≤ (c * b) * b⁻¹ := by
      exact mul_le_mul_of_nonneg_right h_goal (by positivity)
    have h2 : (c * b) * b⁻¹ = c * (b * b⁻¹) := by ring
    rw [h2] at h
    rw [ENNReal.mul_inv_cancel hb_ne_zero hb_ne_top] at h
    simpa using h
  exact h7

/-! ### Direction count transfer -/

/-- A finite 2δ-separated subset of a set `A` has cardinality at most `Ncover δ A`. -/
lemma separated_card_le_ncover {δ : ℝ} (hδ : 0 < δ)
    {R : Finset ℝ} {A : Set ℝ}
    (hR_sub : (R : Set ℝ) ⊆ A)
    (hR_sep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 2 * δ < |x - y|) :
    (R.card : ENNReal) ≤ Ncover δ A := by
  let ε : NNReal := δ.toNNReal
  have hε : (ε : ℝ) = δ := by
    rw [Real.coe_toNNReal δ] <;> linarith
  have hR_is_sep : IsSeparated (2 * ε) (R : Set ℝ) := by
    intro x hx y hy hne
    have h : 2 * δ < |x - y| := hR_sep x hx y hy hne
    have h_edist : edist x y = ENNReal.ofReal |x - y| := by
      rw [edist_dist, Real.dist_eq]
    rw [h_edist]
    have h_coe : (2 * (↑ε : ENNReal)) = ENNReal.ofReal (2 * δ) := by
      simp [ε, hε] <;> norm_cast
    rw [h_coe]
    have h_pos' : 0 < |x - y| := by linarith [h]
    exact (ENNReal.ofReal_lt_ofReal_iff h_pos').mpr h
  have h1 : (R : Set ℝ).encard ≤ packingNumber (2 * ε) A :=
    IsSeparated.encard_le_packingNumber hR_sub hR_is_sep
  have h2 : packingNumber (2 * ε) A ≤ externalCoveringNumber ε A :=
    packingNumber_two_mul_le_externalCoveringNumber ε A
  have h3 : (R : Set ℝ).encard ≤ externalCoveringNumber ε A := le_trans h1 h2
  have h4 : (R : Set ℝ).encard = ↑R.card := by simp
  rw [h4] at h3
  have h5 : (↑R.card : ENNReal) ≤ ↑(externalCoveringNumber ε A) := by exact_mod_cast h3
  simpa [Ncover, hε] using h5

/-- Direction count transfer: if `R` is a 2δ-separated subset of an `IsDeltaSSet`
    set `directions` with `|R| = Ncover δ directions`, then `R` satisfies the counting
    bound required by `projected_energy_average_reg`. -/
lemma direction_count_transfer {δ s C : ℝ} {directions : Set ℝ} {R : Finset ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hC : 0 < C)
    (h_dir : IsDeltaSSet δ s C directions)
    (hR_sub : (R : Set ℝ) ⊆ directions)
    (hR_sep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 2 * δ < |x - y|)
    (hR_card : (R.card : ENNReal) = Ncover δ directions) :
    ∀ (σ : ℝ) (r : ℝ), δ ≤ r →
      (R.filter (fun x => dist x σ ≤ r)).card ≤ C * r ^ s * (R.card : ℝ) := by
  intro σ r hr
  let R_ball : Finset ℝ := R.filter (fun x => dist x σ ≤ r)
  let dir_ball : Set ℝ := directions ∩ closedBall σ r
  have hR_ball_sub : (R_ball : Set ℝ) ⊆ dir_ball := by
    intro x hx
    have h1 : x ∈ R := (Finset.mem_filter.mp hx).1
    have h2 : dist x σ ≤ r := (Finset.mem_filter.mp hx).2
    exact ⟨hR_sub h1, h2⟩
  have hR_ball_sep : ∀ x ∈ R_ball, ∀ y ∈ R_ball, x ≠ y → 2 * δ < |x - y| := by
    intro x hx y hy hne
    have hx' : x ∈ R := (Finset.mem_filter.mp hx).1
    have hy' : y ∈ R := (Finset.mem_filter.mp hy).1
    exact hR_sep x hx' y hy' hne
  have h1 : (R_ball.card : ENNReal) ≤ Ncover δ dir_ball :=
    separated_card_le_ncover hδ hR_ball_sub hR_ball_sep
  have h2 : Ncover δ dir_ball ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Ncover δ directions := by
    have h3 := h_dir.2.2.2.2 σ r hr
    simpa [Ncover] using h3
  have h4 : (R_ball.card : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Ncover δ directions :=
    le_trans h1 h2
  rw [hR_card.symm] at h4
  have h5 : (R_ball.card : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (R.card : ENNReal) := h4
  have h6 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s = ENNReal.ofReal (C * r ^ s) := by
    have hr_nonneg : 0 ≤ r := by linarith
    have hC_nonneg : 0 ≤ C := by linarith
    have h61 : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
      ENNReal.ofReal_rpow_of_nonneg hr_nonneg hs
    rw [h61]
    rw [← ENNReal.ofReal_mul hC_nonneg] <;> rfl
  rw [h6] at h5
  have hr_nonneg' : 0 ≤ r := by linarith
  have h_rpow_nonneg : 0 ≤ r ^ s := Real.rpow_nonneg hr_nonneg' s
  have h_pos : 0 ≤ C * r ^ s := mul_nonneg (by linarith) h_rpow_nonneg
  have h_ne_top1 : (R_ball.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h_ne_top2 : (ENNReal.ofReal (C * r ^ s) * (R.card : ENNReal)) ≠ ⊤ := by
    have h1 : ENNReal.ofReal (C * r ^ s) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2 : (R.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    exact ENNReal.mul_ne_top h1 h2
  have h_iff : ((R_ball.card : ENNReal)).toReal ≤ (ENNReal.ofReal (C * r ^ s) * (R.card : ENNReal)).toReal ↔
      (R_ball.card : ENNReal) ≤ ENNReal.ofReal (C * r ^ s) * (R.card : ENNReal) :=
    ENNReal.toReal_le_toReal h_ne_top1 h_ne_top2
  have h8 : ((R_ball.card : ENNReal)).toReal ≤ (ENNReal.ofReal (C * r ^ s) * (R.card : ENNReal)).toReal :=
    h_iff.mpr h5
  have h9 : (ENNReal.ofReal (C * r ^ s) * (R.card : ENNReal)).toReal =
      (C * r ^ s) * (R.card : ℝ) := by
    have h10 : (ENNReal.ofReal (C * r ^ s) * (R.card : ENNReal)).toReal =
        (ENNReal.ofReal (C * r ^ s)).toReal * (R.card : ℝ) := by
      rw [ENNReal.toReal_mul] <;> simp
    rw [h10]
    have h11 : (ENNReal.ofReal (C * r ^ s)).toReal = C * r ^ s := by
      rw [ENNReal.toReal_ofReal h_pos]
    rw [h11] <;> ring
  rw [h9] at h8
  exact h8

/-- Transfer ball-growth from IsDeltaSSet on directions to a 2δ-separated witness R.
    Uses direction_count_transfer. -/
lemma direction_ball_growth_transfer
    {δ s C_dir : ℝ} {directions : Set ℝ} {R : Finset ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hC_dir_pos : 0 < C_dir)
    (hdir_sset : IsDeltaSSet δ s C_dir directions)
    (hR_sub : (R : Set ℝ) ⊆ directions)
    (hR_sep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 2 * δ < |x - y|)
    (hR_card : (R.card : ENNReal) = Ncover δ directions) :
    ∀ (σ : ℝ) (r : ℝ), δ ≤ r →
      (R.filter (fun x => dist x σ ≤ r)).card ≤ C_dir * r ^ s * (R.card : ℝ) := by
  intro σ r hr
  exact direction_count_transfer hδ hs hC_dir_pos hdir_sset hR_sub hR_sep hR_card σ r hr

/-! ### Bridge extraction lemma (measure-based pipeline) -/

/-- Helper: weaken the constant in IsDeltaSSet. -/
private lemma IsDeltaSSet.weaken' {X : Type*} [PseudoMetricSpace X] {δ s C1 C2 : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C1 P) (hC : C1 ≤ C2) (hC2_pos : 0 < C2) :
    IsDeltaSSet δ s C2 P := by
  refine' ⟨h.1, h.2.1, hC2_pos, h.2.2.2.1, _⟩
  intro x r hr
  have h1 := h.2.2.2.2 x r hr
  have h2 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
  calc
    Ncover δ (P ∩ closedBall x r)
      ≤ ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s * Ncover δ P := h1
    _ ≤ ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s * Ncover δ P := by gcongr

/-- Extract a δ-set from the projection of P' given bounded projected energy on S_P'.
    Uses the measure-based pipeline: pushforward → Frostman restriction → CDF extraction →
    near-identity transfer. -/
lemma extract_delta_set_from_projected_energy
    {δ s A ρ : ℝ} (hδ : 0 < δ) (hδ_lt_one : δ < 1) (hs : 0 < s)
    (hA_ge_one : 1 ≤ A) (hρ : 0 < ρ)
    {S_P' : Finset EuclideanPlane} {P' : Set EuclideanPlane} {σ : ℝ}
    (hS_P'_near : ∀ x ∈ S_P', ∃ p ∈ P', dist x p ≤ δ)
    (hP'_unit : P' ⊆ {p | p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1})
    (hσ_range : -1 ≤ σ ∧ σ ≤ 1)
    {E : ℝ} (hE_pos : 0 < E)
    (hE_bound : projectedEnergyReg (uniformMeasure S_P') s δ σ ≤ ENNReal.ofReal E)
    (hS_card : (S_P'.card : ℝ) ≥ δ ^ (A * ρ - s))
    (h_absorb_sset : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (E + δ^(-s)/(S_P'.card : ℝ)) ≤ δ ^ (-A * ρ))
    (h_absorb_ncover : 7 * (E + δ^(-s)/(S_P'.card : ℝ)) ≤ δ ^ (-A * ρ) / ((2 : ℝ)^(2*s+3) * 3^s)) :
    ∃ (X : Set ℝ),
      X ⊆ RobustKaufmanProjection.affineProjection σ P' ∧
      IsDeltaSSet δ s (δ ^ (-A * ρ)) X ∧
      ENNReal.ofReal (δ ^ (A * ρ - s)) ≤ Ncover δ X := by
  set n : ℝ := (S_P'.card : ℝ) with hn_def
  have h_card_pos : 0 < S_P'.card := by
    by_contra h2
    have h3 : S_P'.card = 0 := by omega
    have h4 : (S_P'.card : ℝ) = 0 := by exact_mod_cast h3
    rw [hn_def, h4] at hS_card
    have h5 : δ ^ (A * ρ - s) > 0 := Real.rpow_pos_of_pos hδ (A * ρ - s)
    linarith
  have hn_pos : 0 < n := by
    have h' : (0 : ℝ) < (S_P'.card : ℝ) := by exact_mod_cast h_card_pos
    simpa [hn_def] using h'
  have hS_nonempty : S_P'.Nonempty := Finset.card_pos.mp h_card_pos
  set E' : ℝ := E + δ^(-s) / n with hE'_def
  have hE'_pos : 0 < E' := by positivity
  let proj : EuclideanPlane → ℝ := fun p => p 0 - σ * p 1
  let μ : Measure EuclideanPlane := uniformMeasure S_P'
  let ν : Measure ℝ := Measure.map proj μ
  have hν_prob : ν Set.univ = 1 := by
    have h1 : ν Set.univ = μ Set.univ := by
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] <;> simp
    rw [h1]
    have h2 : μ Set.univ = (S_P'.card : ENNReal)⁻¹ * (S_P'.card : ENNReal) := by
      simp [μ, uniformMeasure] <;> rfl
    rw [h2]
    have h3 : (S_P'.card : ENNReal) ≠ 0 := by exact_mod_cast h_card_pos.ne'
    have h4 : (S_P'.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    exact ENNReal.inv_mul_cancel h3 h4
  have h_energy_eq : regularizedEnergy ν s δ =
      projectedEnergyReg μ s δ σ + ENNReal.ofReal (δ^(-s) / n) :=
    pushforward_projected_energy hδ hs hS_nonempty
  have h_energy_le : regularizedEnergy ν s δ ≤ ENNReal.ofReal E' := by
    rw [h_energy_eq]
    have h1 : projectedEnergyReg μ s δ σ ≤ ENNReal.ofReal E := hE_bound
    have h2 : ENNReal.ofReal E + ENNReal.ofReal (δ^(-s) / n) = ENNReal.ofReal E' := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), hE'_def] <;> rfl
    calc projectedEnergyReg μ s δ σ + ENNReal.ofReal (δ^(-s) / n)
      ≤ ENNReal.ofReal E + ENNReal.ofReal (δ^(-s) / n) := add_le_add h1 (le_refl _)
    _ = ENNReal.ofReal E' := h2
  rcases energy_to_frostman_restriction hδ hs hE'_pos hν_prob h_energy_le
    with ⟨ν', m, hm_ge_half, hν'_mass, h_ball_growth, hν'_support⟩
  have hm_pos : 0 < m := by linarith
  have hμ_support_eq : μ.support = (S_P' : Set EuclideanPlane) := by
    have hS_closed : IsClosed (S_P' : Set EuclideanPlane) := (Finset.finite_toSet S_P').isClosed
    have hS_meas : MeasurableSet (S_P' : Set EuclideanPlane) := Finset.measurableSet S_P'
    have h_null_compl : μ (S_P' : Set EuclideanPlane)ᶜ = 0 := by
      dsimp only [μ, uniformMeasure]
      have h_rest : (Measure.count.restrict (S_P' : Set EuclideanPlane)) ((S_P' : Set EuclideanPlane)ᶜ) = 0 := by
        rw [Measure.restrict_apply hS_meas.compl]
        have h_disj : (S_P' : Set EuclideanPlane)ᶜ ∩ (S_P' : Set EuclideanPlane) = ∅ := by
          ext x; simp [Set.mem_compl_iff] <;> tauto
        rw [h_disj] <;> simp
      simpa [smul_eq_mul] using congr_arg (fun x : ENNReal => (S_P'.card : ENNReal)⁻¹ * x) h_rest
    have h_ae : (S_P' : Set EuclideanPlane) ∈ ae μ := by
      exact mem_ae_iff.mpr h_null_compl
    have h_sub1 : μ.support ⊆ (S_P' : Set EuclideanPlane) :=
      Measure.support_subset_of_isClosed hS_closed h_ae
    have h_sub2 : (S_P' : Set EuclideanPlane) ⊆ μ.support := by
      intro x hx
      have h3 : 0 < μ {x} := by
        simp [μ, uniformMeasure, hx, h_card_pos.ne'] <;> positivity
      rw [Measure.mem_support_iff_forall x]
      intro U hU_nhds
      have h_x_in_U : x ∈ U := by exact mem_of_mem_nhds hU_nhds
      have h4 : {x} ⊆ U := singleton_subset_iff.mpr h_x_in_U
      have h5 : μ {x} ≤ μ U := measure_mono h4
      exact lt_of_lt_of_le h3 h5
    exact Set.Subset.antisymm h_sub1 h_sub2
  have h_image_finite : (proj '' (S_P' : Set EuclideanPlane)).Finite :=
    Set.Finite.image _ (Finset.finite_toSet S_P')
  have h_image_closed : IsClosed (proj '' (S_P' : Set EuclideanPlane)) := h_image_finite.isClosed
  have hν_support_sub : ν.support ⊆ proj '' (S_P' : Set EuclideanPlane) := by
    have hν_null : ν (proj '' (S_P' : Set EuclideanPlane))ᶜ = 0 := by
      have h_compl_meas : MeasurableSet (proj '' (S_P' : Set EuclideanPlane))ᶜ :=
        h_image_closed.isOpen_compl.measurableSet
      rw [Measure.map_apply (by fun_prop) h_compl_meas]
      have h_preimage_sub : proj ⁻¹' ((proj '' (S_P' : Set EuclideanPlane))ᶜ) ⊆ (S_P' : Set EuclideanPlane)ᶜ := by
        intro x hx
        have h3 : proj x ∉ proj '' (S_P' : Set EuclideanPlane) := hx
        by_contra h4
        have h5 : x ∈ (S_P' : Set EuclideanPlane) := by simpa [Set.mem_compl_iff] using h4
        exact h3 ⟨x, h5, rfl⟩
      have h_support_null : μ (μ.supportᶜ) = 0 := by exact Measure.measure_compl_support
      have h_more : (proj ⁻¹' ((proj '' (S_P' : Set EuclideanPlane))ᶜ)) ⊆ μ.supportᶜ := by
        intro x hx
        have h6 : x ∉ μ.support := by
          intro h7
          have h8 : x ∈ (S_P' : Set EuclideanPlane) := by
            rw [←hμ_support_eq]; exact h7
          exact h_preimage_sub hx h8
        exact h6
      exact measure_mono_null h_more h_support_null
    have h_ae2 : (proj '' (S_P' : Set EuclideanPlane)) ∈ ae ν := by
      exact mem_ae_iff.mpr hν_null
    exact Measure.support_subset_of_isClosed h_image_closed h_ae2
  have h_proj_bdd : proj '' (S_P' : Set EuclideanPlane) ⊆ Set.Icc (-100 : ℝ) 100 := by
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    have h_near : ∃ q ∈ P', dist p q ≤ δ := hS_P'_near p hp
    rcases h_near with ⟨q, hqP, hdist⟩
    have hq0 : q 0 ∈ Set.Icc (0 : ℝ) 1 := (hP'_unit hqP).1
    have hq1 : q 1 ∈ Set.Icc (0 : ℝ) 1 := (hP'_unit hqP).2
    have h_p0_near : |p 0 - q 0| ≤ dist p q := PiLp.norm_apply_le (p - q) 0
    have h_p1_near : |p 1 - q 1| ≤ dist p q := PiLp.norm_apply_le (p - q) 1
    have h_p0_ge : p 0 ≥ q 0 - δ := by linarith [abs_le.mp h_p0_near]
    have h_p0_le : p 0 ≤ q 0 + δ := by linarith [abs_le.mp h_p0_near]
    have h_p1_ge : p 1 ≥ q 1 - δ := by linarith [abs_le.mp h_p1_near]
    have h_p1_le : p 1 ≤ q 1 + δ := by linarith [abs_le.mp h_p1_near]
    have h_p0_bdd : -100 ≤ proj p := by
      dsimp only [proj]
      have h1 : p 0 ≥ -1 := by linarith [hq0.1, hδ_lt_one]
      have h2 : p 1 ≤ 2 := by linarith [hq1.2, hδ_lt_one]
      have h3 : p 1 ≥ -1 := by linarith [hq1.1, hδ_lt_one]
      have h4 : σ * p 1 ≤ 2 := by
        have h5 : -1 ≤ σ := hσ_range.1
        have h6 : σ ≤ 1 := hσ_range.2
        nlinarith [abs_nonneg (p 1)]
      linarith
    have h_p1_bdd : proj p ≤ 100 := by
      dsimp only [proj]
      have h1 : p 0 ≤ 2 := by linarith [hq0.2, hδ_lt_one]
      have h2 : p 1 ≥ -1 := by linarith [hq1.1, hδ_lt_one]
      have h3 : p 1 ≤ 2 := by linarith [hq1.2, hδ_lt_one]
      have h4 : σ * p 1 ≥ -2 := by
        have h5 : -1 ≤ σ := hσ_range.1
        have h6 : σ ≤ 1 := hσ_range.2
        nlinarith [abs_nonneg (p 1)]
      linarith
    exact ⟨h_p0_bdd, h_p1_bdd⟩
  have hν_support_bdd : ν.support ⊆ Set.Icc (-100 : ℝ) 100 := hν_support_sub.trans h_proj_bdd
  have hν'_support_bdd : ν'.support ⊆ Set.Icc (-100 : ℝ) 100 := hν'_support.trans hν_support_bdd
  set C_frost : ℝ := 2^(2*s+1) * E' with hC_frost_def
  have hC_frost_pos : 0 < C_frost := by positivity
  have h_ball : ∀ (x : ℝ) (r : ℝ), δ / 2 ≤ r → ν' (closedBall x r) ≤ ENNReal.ofReal (C_frost * r^s) := by
    intro x r hr; have h := h_ball_growth x r hr; simpa [hC_frost_def] using h
  rcases frostman_measure_to_deltaset (hδ := hδ) (hs := hs) (hC := hC_frost_pos) (hm := hm_pos)
    (hX_bdd := hν_support_bdd) (hμ_support := hν'_support) (hμ_mass := hν'_mass) (h_ball := h_ball)
    with ⟨G, hG_sub_support, hG_sset, hG_lower⟩
  have hG_in_proj_S : G ⊆ proj '' (S_P' : Set EuclideanPlane) := hG_sub_support.trans hν_support_sub
  have h_choose : ∀ (x : ℝ), x ∈ G →
      ∃ (y : ℝ), y ∈ RobustKaufmanProjection.affineProjection σ P' ∧ dist y x ≤ 2 * δ := by
    intro x hx
    have h_x_in_proj : x ∈ proj '' (S_P' : Set EuclideanPlane) := hG_in_proj_S hx
    rcases h_x_in_proj with ⟨p, hpS, rfl⟩
    have h_near : ∃ q ∈ P', dist p q ≤ δ := hS_P'_near p hpS
    rcases h_near with ⟨q, hqP, hdist⟩
    let y : ℝ := proj q
    have hy_in : y ∈ RobustKaufmanProjection.affineProjection σ P' := ⟨q, hqP, rfl⟩
    have h_dist_yx : dist y (proj p) ≤ 2 * δ := by
      have hy_def : y = proj q := by rfl
      rw [hy_def]
      have h1 : dist (proj q) (proj p) = |proj q - proj p| := by
        rw [Real.dist_eq] <;> rfl
      rw [h1]
      have h2 : |proj q - proj p| ≤ |q 0 - p 0| + |σ| * |q 1 - p 1| := by
        dsimp only [proj]
        have h3 : |(q 0 - σ * q 1) - (p 0 - σ * p 1)| ≤ |q 0 - p 0| + |σ| * |q 1 - p 1| := by
          calc |(q 0 - σ * q 1) - (p 0 - σ * p 1)|
            = |(q 0 - p 0) - σ * (q 1 - p 1)| := by ring_nf
          _ ≤ |q 0 - p 0| + |σ * (q 1 - p 1)| := by exact abs_sub _ _
          _ = |q 0 - p 0| + |σ| * |q 1 - p 1| := by rw [abs_mul]
        exact h3
      have h6 : |q 0 - p 0| ≤ dist q p := PiLp.norm_apply_le (q - p) 0
      have h7 : |q 1 - p 1| ≤ dist q p := PiLp.norm_apply_le (q - p) 1
      have h8 : |σ| ≤ 1 := by exact abs_le.mpr ⟨hσ_range.1, hσ_range.2⟩
      have h9 : dist q p ≤ δ := by rw [dist_comm]; exact hdist
      calc |proj q - proj p|
        ≤ |q 0 - p 0| + |σ| * |q 1 - p 1| := h2
      _ ≤ dist q p + |σ| * dist q p := by gcongr
      _ = (1 + |σ|) * dist q p := by ring
      _ ≤ (1 + 1) * dist q p := by gcongr
      _ = 2 * dist q p := by ring
      _ ≤ 2 * δ := by
        exact mul_le_mul_of_nonneg_left h9 (by norm_num)
    exact ⟨y, hy_in, h_dist_yx⟩
  classical
  let f : ℝ → ℝ := fun x => if h : x ∈ G then Classical.choose (h_choose x h) else 0
  have hf1 : ∀ x ∈ G, f x ∈ RobustKaufmanProjection.affineProjection σ P' := by
    intro x hx
    dsimp only [f]
    rw [dif_pos hx]
    exact (Classical.choose_spec (h_choose x hx)).1
  have hf2 : ∀ x ∈ G, dist (f x) x ≤ 2 * δ := by
    intro x hx
    dsimp only [f]
    rw [dif_pos hx]
    exact (Classical.choose_spec (h_choose x hx)).2
  let X : Set ℝ := f '' G
  have hX_sub : X ⊆ RobustKaufmanProjection.affineProjection σ P' := by
    intro z hz; rcases hz with ⟨x, hx, rfl⟩; exact hf1 x hx
  have h_perturb : ∀ x ∈ G, dist (f x) x ≤ 2 * δ := by intro x hx; exact hf2 x hx
  have h_transfer := isDeltaSSet_near_identity_transfer (hδ := hδ) (hs := hs.le) (c := (2 : ℝ)) (by norm_num)
    hG_sset h_perturb rfl
  have hC_orig_le : 4 * C_frost * 3^s / m ≤ 2^(2*s+4) * 3^s * E' := by
    have h1 : 1 / m ≤ 2 := by
      have h2 : 0 < m := hm_pos
      have h3 : m ≥ 1 / 2 := hm_ge_half
      have h4 : 1 / m ≤ 1 / (1 / 2 : ℝ) := by gcongr
      have h5 : 1 / (1 / 2 : ℝ) = 2 := by norm_num
      rw [h5] at h4
      exact h4
    calc
      4 * C_frost * 3^s / m
        = (4 * 3^s) * C_frost * (1 / m) := by ring
      _ ≤ (4 * 3^s) * C_frost * 2 := by gcongr
      _ = 8 * C_frost * 3^s := by ring
      _ = 8 * (2^(2*s+1) * E') * 3^s := by rw [hC_frost_def]
      _ = 2^(2*s+4) * 3^s * E' := by
        have h4 : (8 : ℝ) * 2^(2*s+1) = 2^(2*s+4) := by
          have h5 : (8 : ℝ) = (2 : ℝ)^(3 : ℝ) := by norm_num
          have h6 : (2 : ℝ)^(3 : ℝ) * (2 : ℝ)^(2*s+1) = (2 : ℝ)^(3 + (2*s+1)) := by
            rw [← Real.rpow_add (by norm_num)]
          have h7 : 3 + (2*s+1) = 2*s+4 := by ring
          calc (8 : ℝ) * 2^(2*s+1)
            = (2 : ℝ)^(3 : ℝ) * (2 : ℝ)^(2*s+1) := by rw [h5]
          _ = (2 : ℝ)^(3 + (2*s+1)) := h6
          _ = (2 : ℝ)^(2*s+4) := by rw [h7]
        have h_eq : 8 * (2^(2*s+1) * E') * 3^s = (8 * 2^(2*s+1)) * E' * 3^s := by ring
        rw [h_eq, h4] <;> ring
  let C_transfer : ℝ := (4 * C_frost * 3^s / m) * (7 : ℝ)^2 * (1 + (2 : ℝ))^s
  have hC_transfer_le : C_transfer ≤ 49 * 2^(2*s+4) * 3^(2*s) * E' := by
    dsimp only [C_transfer]
    have h1 : (4 * C_frost * 3^s / m) ≤ 2^(2*s+4) * 3^s * E' := hC_orig_le
    have h2 : (1 + (2 : ℝ))^s = (3 : ℝ)^s := by norm_num
    rw [h2]
    calc
      (4 * C_frost * 3^s / m) * (7 : ℝ)^2 * (3 : ℝ)^s
        ≤ (2^(2*s+4) * 3^s * E') * (7 : ℝ)^2 * (3 : ℝ)^s := by gcongr
      _ = 49 * 2^(2*s+4) * 3^(2*s) * E' := by
        have h3s : (3 : ℝ)^s * (3 : ℝ)^s = (3 : ℝ)^(2*s) := by
          rw [← Real.rpow_add (by norm_num)] <;> ring_nf
        calc
          (2^(2*s+4) * 3^s * E') * (7 : ℝ)^2 * (3 : ℝ)^s
            = (7 : ℝ)^2 * 2^(2*s+4) * ((3 : ℝ)^s * (3 : ℝ)^s) * E' := by ring
        _ = (7 : ℝ)^2 * 2^(2*s+4) * (3 : ℝ)^(2*s) * E' := by rw [h3s]
        _ = 49 * 2^(2*s+4) * 3^(2*s) * E' := by norm_num <;> ring
  have hC_target_pos : 0 < δ ^ (-A * ρ) := Real.rpow_pos_of_pos hδ (-A * ρ)
  have hC_absorb : C_transfer ≤ δ ^ (-A * ρ) := by
    calc C_transfer ≤ 49 * 2^(2*s+4) * 3^(2*s) * E' := hC_transfer_le
         _ ≤ δ ^ (-A * ρ) := by simpa [hE'_def] using h_absorb_sset
  have h_ceil : Int.ceil (2 : ℝ) = 2 := by simp
  have h_toNat : (Int.ceil (2 : ℝ)).toNat = 2 := by
    rw [h_ceil] <;> simp
  have hK_simp : (2 * (Int.ceil (2 : ℝ)).toNat + 3 : ℕ) = 7 := by
    rw [h_toNat] <;> norm_num
  have h_transfer1' : IsDeltaSSet δ s ((4 * C_frost * 3^s / m) * (7 : ℝ)^2 * (1 + (2 : ℝ))^s) X := by
    have h_eq1 : ((2 * (Int.ceil (2 : ℝ)).toNat + 3 : ℝ)^2) = (7 : ℝ)^2 := by
      rw [h_toNat] <;> norm_num
    have h : IsDeltaSSet δ s ((4 * C_frost * 3^s / m) * ((2 * (Int.ceil (2 : ℝ)).toNat + 3 : ℝ)^2) * (1 + (2 : ℝ))^s) X := h_transfer.1
    rw [h_eq1] at h
    exact h
  have hC_absorb' : (4 * C_frost * 3 ^ s / m) * (7 : ℝ)^2 * (1 + (2 : ℝ))^s ≤ δ ^ (-A * ρ) := by
    simpa [C_transfer] using hC_absorb
  have hX_sset : IsDeltaSSet δ s (δ ^ (-A * ρ)) X :=
    IsDeltaSSet.weaken' h_transfer1' hC_absorb' hC_target_pos
  have h_lower1 : m / (2 * C_frost * 3^s * δ^s) ≥ 1 / ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s) := by
    have h4 : (4 : ℝ) * (2 : ℝ)^(2*s+1) = (2 : ℝ)^(2*s+3) := by
      rw [show (4 : ℝ) = (2 : ℝ)^(2 : ℝ) by norm_num]
      rw [← Real.rpow_add (by norm_num)] <;> ring_nf
    have h_denom_eq : 4 * C_frost * 3^s * δ^s = (2 : ℝ)^(2*s+3) * 3^s * E' * δ^s := by
      have h : C_frost = (2 : ℝ)^(2*s+1) * E' := hC_frost_def
      calc 4 * C_frost * 3^s * δ^s
        = 4 * ((2 : ℝ)^(2*s+1) * E') * 3^s * δ^s := by rw [h]
      _ = (4 * (2 : ℝ)^(2*s+1)) * E' * 3^s * δ^s := by ring
      _ = (2 : ℝ)^(2*s+3) * E' * 3^s * δ^s := by rw [h4] <;> ring
      _ = (2 : ℝ)^(2*s+3) * 3^s * E' * δ^s := by ring
    have h1 : m ≥ 1 / 2 := hm_ge_half
    have h_pos_denom : 0 < 2 * C_frost * 3^s * δ^s := by positivity
    have h2 : m / (2 * C_frost * 3^s * δ^s) ≥ (1 / 2 : ℝ) / (2 * C_frost * 3^s * δ^s) := by
      exact div_le_div_of_nonneg_right h1 (by positivity)
    have h3 : (1 / 2 : ℝ) / (2 * C_frost * 3^s * δ^s) = 1 / (4 * C_frost * 3^s * δ^s) := by ring_nf
    rw [h3] at h2
    rw [h_denom_eq] at h2
    exact h2
  have h_transfer_lower : Ncover δ G ≤ (7 : ENNReal) * Ncover δ X := by
    have h_tmp := h_transfer.2
    have hK_eq : (2 * (Int.ceil (2 : ℝ)).toNat + 3 : ENNReal) = (7 : ENNReal) := by
      rw [h_toNat] <;> norm_num
    rw [hK_eq] at h_tmp
    exact h_tmp
  have hX_lower1 : ENNReal.ofReal (1 / ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s)) ≤ Ncover δ G := by
    have h_pos1 : 0 ≤ m / (2 * C_frost * 3^s * δ^s) := by positivity
    have h1 : ENNReal.ofReal (1 / ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s)) ≤ ENNReal.ofReal (m / (2 * C_frost * 3^s * δ^s)) :=
      ENNReal.ofReal_le_ofReal h_lower1
    have h2 : ENNReal.ofReal (m / (2 * C_frost * 3^s * δ^s)) ≤ Ncover δ G := hG_lower
    exact le_trans h1 h2
  have hX_lower2 : ENNReal.ofReal (1 / (7 * ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s))) ≤ Ncover δ X := by
    have h_pos2 : 0 ≤ 1 / ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s) := by positivity
    have h3 : ENNReal.ofReal (1 / ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s)) ≤ (7 : ENNReal) * Ncover δ X :=
      le_trans hX_lower1 h_transfer_lower
    have h_inv7 : (1 / 7 : ENNReal) = ENNReal.ofReal (1 / 7 : ℝ) := by
      simp
    have h4 : (1 / 7 : ENNReal) * ENNReal.ofReal (1 / ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s)) ≤ (1 / 7 : ENNReal) * ((7 : ENNReal) * Ncover δ X) := by
      gcongr
    have h5 : (1 / 7 : ENNReal) * ((7 : ENNReal) * Ncover δ X) = Ncover δ X := by
      have h51 : (1 / 7 : ENNReal) * (7 : ENNReal) = 1 := by
        have h : (1 / 7 : ENNReal) = ENNReal.ofReal (1 / 7 : ℝ) := by simp
        have h7 : (7 : ENNReal) = ENNReal.ofReal (7 : ℝ) := by simp
        rw [h, h7]
        rw [← ENNReal.ofReal_mul (by norm_num)]
        have h2 : (1 / 7 : ℝ) * (7 : ℝ) = 1 := by norm_num
        rw [h2] <;> simp
      rw [← mul_assoc, h51, one_mul]
    have h6 : (1 / 7 : ENNReal) * ENNReal.ofReal (1 / ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s)) =
        ENNReal.ofReal (1 / (7 * ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s))) := by
      rw [h_inv7]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      have h7 : (1 / 7 : ℝ) * (1 / ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s)) = 1 / (7 * ((2 : ℝ)^(2*s+3) * 3^s * E' * δ^s)) := by ring_nf
      rw [h7]
    rw [h6] at h4
    rw [h5] at h4
    exact h4
  have hX_lower_final : ENNReal.ofReal (δ ^ (A * ρ - s)) ≤ Ncover δ X := by
    set K : ℝ := (2 : ℝ)^(2*s+3) * (3 : ℝ)^s with hK_def
    have hK_pos : 0 < K := by positivity
    have h9 : δ ^ (A * ρ - s) ≤ 1 / (7 * K * E' * δ^s) := by
      have h1 : 7 * E' * K ≤ δ ^ (-A * ρ) := by
        have h2 : 7 * E' ≤ δ ^ (-A * ρ) / K := by
          simpa [K, hK_def] using h_absorb_ncover
        calc 7 * E' * K
          ≤ (δ ^ (-A * ρ) / K) * K := by gcongr
        _ = δ ^ (-A * ρ) := by
          field_simp [hK_pos.ne'] <;> ring
      have h3 : δ ^ (A * ρ) * (7 * E' * K) ≤ 1 := by
        have h4 : δ ^ (A * ρ) * δ ^ (-A * ρ) = 1 := by
          rw [← Real.rpow_add hδ] <;> ring_nf <;> simp
        calc δ ^ (A * ρ) * (7 * E' * K)
          ≤ δ ^ (A * ρ) * δ ^ (-A * ρ) := by gcongr
        _ = 1 := h4
      have h5 : δ ^ (A * ρ) ≤ 1 / (7 * E' * K) := by
        have h6 : 0 < 7 * E' * K := by positivity
        calc δ ^ (A * ρ)
          = (δ ^ (A * ρ) * (7 * E' * K)) / (7 * E' * K) := by field_simp [h6.ne'] <;> ring
        _ ≤ 1 / (7 * E' * K) := by gcongr
      have h7 : 0 < δ^s := Real.rpow_pos_of_pos hδ s
      have h8 : δ ^ (A * ρ - s) * δ^s = δ ^ (A * ρ) := by
        rw [← Real.rpow_add hδ] <;> ring_nf
      have h9_eq : δ ^ (A * ρ - s) = δ ^ (A * ρ) / δ^s := by
        exact (eq_div_iff h7.ne').mpr h8
      calc δ ^ (A * ρ - s)
        = δ ^ (A * ρ) / δ^s := h9_eq
      _ ≤ (1 / (7 * E' * K)) / δ^s := by gcongr
      _ = 1 / (7 * K * E' * δ^s) := by ring_nf
    have h13 : ENNReal.ofReal (δ ^ (A * ρ - s)) ≤ ENNReal.ofReal (1 / (7 * K * E' * δ^s)) :=
      ENNReal.ofReal_le_ofReal h9
    have h14 : (1 / (7 * K * E' * δ^s)) = (1 / (7 * ((2 : ℝ)^(2*s+3) * (3 : ℝ)^s * E' * δ^s))) := by
      simp [K, hK_def] <;> ring
    rw [h14] at h13
    exact le_trans h13 hX_lower2
  exact ⟨X, hX_sub, hX_sset, hX_lower_final⟩

/-- Absorb E_ref into δ^(-8ρ)/100 for sufficiently small δ. -/
lemma e_ref_absorption (s t ρ : ℝ) (hs : 0 < s) (hst : s < t) (hρ : 0 < ρ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        81 * δ ^ (-2 * ρ) * (4 * ((δ ^ (-ρ) * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s) * Real.log (4 / δ) *
          (1 + (9 * δ ^ (-ρ)) * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t)))))
        ≤ δ ^ (-8 * ρ) / 100 := by
  have h_st_neg : s - t < 0 := by linarith
  have h2_pow_lt_one : (2 : ℝ)^(s-t) < 1 := by
    have h1 : 1 < (2 : ℝ) := by norm_num
    have h2 : (2 : ℝ)^(s-t) < (2 : ℝ)^(0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt h1 h_st_neg
    have h3 : (2 : ℝ)^(0 : ℝ) = 1 := by simp
    rw [h3] at h2
    exact h2
  have h_denom_pos : 0 < 1 - (2 : ℝ)^(s-t) := by linarith

  let C1 : ℝ := (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s
  let C2 : ℝ := 1 + 9 * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t))
  let C_const : ℝ := 324 * C1 * C2

  have hC1_pos : 0 < C1 := by positivity
  have hC2_pos : 0 < C2 := by positivity
  have hC_const_pos : 0 < C_const := by positivity

  have ha : 0 < 4 * ρ := by positivity
  have hε : 0 < 4 * ρ := by positivity

  obtain ⟨δ₀, hδ₀_pos, hδ₀_le_one, h_abs⟩ :=
    RobustKaufmanProjection.PolynomialAbsorption.delta_pow_absorb_log4
      C_const (4 * ρ) (4 * ρ) hC_const_pos ha hε

  refine' ⟨δ₀, hδ₀_pos, hδ₀_le_one, _⟩
  intro δ hδ hδ_le

  have hδ_le_one : δ ≤ 1 := by linarith [hδ₀_le_one]
  have hδ_rpow_ge_one : 1 ≤ δ ^ (-ρ) := by
    have h1 : (-ρ : ℝ) ≤ (0 : ℝ) := by linarith
    have h4 : δ ^ (0 : ℝ) ≤ δ ^ (-ρ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ_le_one h1
    have h5 : δ ^ (0 : ℝ) = 1 := by simp
    rw [h5] at h4
    exact h4

  set C_total : ℝ := δ ^ (-ρ) * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s with hC_total_def
  set M_plane : ℝ := 1 + (9 * δ ^ (-ρ)) * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t)) with hM_plane_def
  set M : ℝ := C_total * Real.log (4 / δ) * M_plane with hM_def

  have hC_total_bound : C_total ≤ C1 * δ ^ (-ρ) := by
    rw [hC_total_def]
    dsimp only [C1]
    have h6 : 1 ≤ δ ^ (-ρ) := hδ_rpow_ge_one
    have h7 : δ ^ (-ρ) * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s ≤
        ((4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s) * δ ^ (-ρ) := by
      have h8 : (4 : ℝ)^s ≤ (4 : ℝ)^s * δ ^ (-ρ) := by
        calc (4 : ℝ)^s
          = (4 : ℝ)^s * 1 := by ring
        _ ≤ (4 : ℝ)^s * δ ^ (-ρ) := by gcongr
      have h9 : δ ^ (-ρ) * (4 : ℝ)^s * 3 / Real.log 2 =
          (4 : ℝ)^s * 3 / Real.log 2 * δ ^ (-ρ) := by ring
      rw [h9]
      ring_nf at * <;> linarith
    exact h7

  have hM_plane_bound : M_plane ≤ C2 * δ ^ (-ρ) := by
    rw [hM_plane_def]
    dsimp only [C2]
    have h7 : 1 ≤ δ ^ (-ρ) := hδ_rpow_ge_one
    have h9 : 1 + 9 * δ ^ (-ρ) * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t)) ≤
        (1 + 9 * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t))) * δ ^ (-ρ) := by
      have h10 : 1 + 9 * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t)) * δ ^ (-ρ) ≤
          δ ^ (-ρ) + 9 * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t)) * δ ^ (-ρ) := by
        linarith [h7]
      ring_nf at * <;> linarith
    exact h9

  have hlog_nonneg : 0 ≤ Real.log (4 / δ) := by
    have h11 : 1 ≤ 4 / δ := by
      have h12 : δ ≤ 4 := by linarith
      have h13 : 0 < δ := hδ
      calc 1 ≤ 4 / 4 := by norm_num
           _ ≤ 4 / δ := by gcongr
    exact Real.log_nonneg h11

  have hM_bound : M ≤ C1 * C2 * δ ^ (-2 * ρ) * Real.log (4 / δ) := by
    rw [hM_def]
    calc
      C_total * Real.log (4 / δ) * M_plane
        ≤ (C1 * δ ^ (-ρ)) * Real.log (4 / δ) * (C2 * δ ^ (-ρ)) := by gcongr <;> linarith
      _ = C1 * C2 * (δ ^ (-ρ) * δ ^ (-ρ)) * Real.log (4 / δ) := by ring
      _ = C1 * C2 * δ ^ (-2 * ρ) * Real.log (4 / δ) := by
        have h12 : δ ^ (-ρ) * δ ^ (-ρ) = δ ^ (-2 * ρ) := by
          rw [← Real.rpow_add hδ] <;> ring_nf
        rw [h12] <;> ring

  have hE_ref_bound : 81 * δ ^ (-2 * ρ) * (4 * M) ≤
      C_const * δ ^ (-4 * ρ) * Real.log (4 / δ) := by
    dsimp only [C_const]
    calc
      81 * δ ^ (-2 * ρ) * (4 * M)
        ≤ 81 * δ ^ (-2 * ρ) * (4 * (C1 * C2 * δ ^ (-2 * ρ) * Real.log (4 / δ))) := by gcongr
      _ = 324 * C1 * C2 * (δ ^ (-2 * ρ) * δ ^ (-2 * ρ)) * Real.log (4 / δ) := by ring
      _ = 324 * C1 * C2 * δ ^ (-4 * ρ) * Real.log (4 / δ) := by
        have h13 : δ ^ (-2 * ρ) * δ ^ (-2 * ρ) = δ ^ (-4 * ρ) := by
          rw [← Real.rpow_add hδ] <;> ring_nf
        rw [h13] <;> ring
      _ = C_const * δ ^ (-4 * ρ) * Real.log (4 / δ) := by ring

  have h_sum : (4 * ρ) + (4 * ρ) = 8 * ρ := by ring
  have h_final : C_const * δ ^ (-4 * ρ) * Real.log (4 / δ) ≤ δ ^ (-8 * ρ) / 100 := by
    have h := h_abs δ hδ hδ_le
    have h_eq1 : δ ^ (-(4 * ρ)) = δ ^ (-4 * ρ) := by ring_nf
    have h_eq2 : δ ^ (-((4 * ρ) + (4 * ρ))) = δ ^ (-8 * ρ) := by rw [h_sum] <;> ring_nf
    rw [h_eq1, h_eq2] at h
    exact h

  exact le_trans hE_ref_bound h_final

end RobustKaufmanProjection.Dune
