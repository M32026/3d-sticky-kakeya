module

/-
  Local regularity transfer theorem — Team-B copy.

  Extracted from SourceToNiceOutput.lean without importing Section9.
  Transfers IsSquareRootRegular from the original point set P to
  config.pointSet at scale δ_n.

  Dependencies beyond Base/CombiningTheorem:
  - Geometry.SSetThickening (plane thickening lemmas)
  - Section6.CommonLemmas (density-aware S-set restriction)
  - PlaneCoveringDoubling (plane covering doubling)
  - CoordinatePartition (swapCoords isometry)

  Whiteprint node: local_regularity_transfer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Geometry.SSetThickening
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.CommonLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.PlaneCoveringDoubling
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open CoordinatePartition
open RegularIncidence

/-- Local Ncover abbreviation matching the original file. -/
abbrev Ncover {X : Type*} [PseudoMetricSpace X] (delta : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber delta.toNNReal E

/-- Distance between two points in the same dyadic square is at most √2·δ_n. -/
lemma local_dyadic_square_dist_le_sqrt2 {n : ℕ} {p : DyadicSquare n}
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ p.toSet) (hy : y ∈ p.toSet) :
    dist x y ≤ Real.sqrt 2 * dyadicDelta n := by
  have h_side := DyadicSquare.side_length hx hy
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have h1 : (x 0 - y 0)^2 ≤ (dyadicDelta n)^2 := by
    have h11 : |x 0 - y 0| ≤ dyadicDelta n := h_side.1
    have h12 : |x 0 - y 0|^2 ≤ (dyadicDelta n)^2 := by gcongr
    simpa [sq_abs] using h12
  have h2 : (x 1 - y 1)^2 ≤ (dyadicDelta n)^2 := by
    have h21 : |x 1 - y 1| ≤ dyadicDelta n := h_side.2
    have h22 : |x 1 - y 1|^2 ≤ (dyadicDelta n)^2 := by gcongr
    simpa [sq_abs] using h22
  have h3 : dist x y = Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) := by
    have h_dist1 : dist x y = ‖x - y‖ := by
      exact dist_eq_norm x y
    rw [h_dist1]
    have h_norm : ‖x - y‖ = Real.sqrt (((x - y) 0)^2 + ((x - y) 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
    rw [h_norm]
    have h4 : (x - y) 0 = x 0 - y 0 := by rfl
    have h5 : (x - y) 1 = x 1 - y 1 := by rfl
    rw [h4, h5]
  rw [h3]
  have h4 : (x 0 - y 0)^2 + (x 1 - y 1)^2 ≤ 2 * (dyadicDelta n)^2 := by linarith
  have h5 : Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) ≤ Real.sqrt (2 * (dyadicDelta n)^2) :=
    Real.sqrt_le_sqrt h4
  have h6 : Real.sqrt (2 * (dyadicDelta n)^2) = Real.sqrt 2 * dyadicDelta n := by
    have h7 : 0 ≤ dyadicDelta n := by linarith
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq h7] <;> ring
  rw [h6] at h5
  exact h5

/-- Scale transfer: (δ,u,C)-set → (δ_n,u,81·C·4^u)-set when δ_n ≤ δ < 4δ_n. -/
lemma local_sset_scale_transfer_finer
    {δ δ_n u C : ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hδn_pos : 0 < δ_n) (hδ_pos : 0 < δ)
    (hδn_leδ : δ_n ≤ δ) (hδ_lt4δn : δ < 4 * δ_n)
    (hu_nonneg : 0 ≤ u) (hC_pos : 0 < C)
    (hP : IsDeltaSSet δ u C P) :
    IsDeltaSSet δ_n u (81 * C * (4 : ℝ)^u) P := by
  rcases hP with ⟨hP_nonempty, _, _, hs_nonneg, hcover⟩
  have h2δn_pos : 0 < 2 * δ_n := by positivity
  have h4δn_pos : 0 < 4 * δ_n := by positivity
  have h_nnreal3 : δ.toNNReal ≤ (4 * δ_n).toNNReal := by
    apply NNReal.coe_le_coe.mp
    have h1 : ((4 * δ_n).toNNReal : ℝ) = 4 * δ_n := by simp [h4δn_pos.le] <;> linarith
    have h2 : (δ.toNNReal : ℝ) = δ := by simp [hδ_pos.le] <;> linarith
    rw [h1, h2] <;> linarith [hδ_lt4δn]
  have h_nnreal5 : δ_n.toNNReal ≤ δ.toNNReal := by
    apply NNReal.coe_le_coe.mp
    have h1 : (δ_n.toNNReal : ℝ) = δ_n := by simp [hδn_pos.le] <;> linarith
    have h2 : (δ.toNNReal : ℝ) = δ := by simp [hδ_pos.le] <;> linarith
    rw [h1, h2] <;> exact hδn_leδ
  have h_main_cover : ∀ (E : Set (EuclideanSpace ℝ (Fin 2))),
      Ncover δ_n E ≤ (81 : ENNReal) * Ncover δ E := by
    intro E
    have h1 : Ncover δ_n E ≤ (9 : ENNReal) * Ncover (2 * δ_n) E :=
      PlaneCoveringDoubling.plane_covering_doubling hδn_pos E
    have h2 : Ncover (2 * δ_n) E ≤ (9 : ENNReal) * Ncover (4 * δ_n) E := by
      have h21 : Ncover (2 * δ_n) E ≤ (9 : ENNReal) * Ncover (2 * (2 * δ_n)) E :=
        PlaneCoveringDoubling.plane_covering_doubling h2δn_pos E
      have h22 : 2 * (2 * δ_n) = 4 * δ_n := by ring
      rw [h22] at h21
      exact h21
    have h3 : Ncover (4 * δ_n) E ≤ Ncover δ E := by
      have h : (Metric.externalCoveringNumber (4 * δ_n).toNNReal E : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_anti h_nnreal3
      exact h
    calc Ncover δ_n E
      ≤ (9 : ENNReal) * Ncover (2 * δ_n) E := h1
    _ ≤ (9 : ENNReal) * ((9 : ENNReal) * Ncover (4 * δ_n) E) := by gcongr
    _ = (81 : ENNReal) * Ncover (4 * δ_n) E := by ring
    _ ≤ (81 : ENNReal) * Ncover δ E := by gcongr
  have h_anti : Ncover δ P ≤ Ncover δ_n P := by
    have h : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
        (Metric.externalCoveringNumber δ_n.toNNReal P : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_anti h_nnreal5
    exact h
  have h4u_one : (1 : ℝ) ≤ (4 : ℝ)^u := by
    have h : (4 : ℝ)^(0 : ℝ) ≤ (4 : ℝ)^u := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using h
  have h_const_le : ENNReal.ofReal (81 * C) ≤ ENNReal.ofReal (81 * C * (4 : ℝ)^u) := by
    apply ENNReal.ofReal_le_ofReal
    have h : 81 * C ≤ 81 * C * (4 : ℝ)^u := by nlinarith
    exact h
  have h_rpow_mul : ∀ (r : ℝ), 0 < r →
      (ENNReal.ofReal (4 * r)) ^ u = (ENNReal.ofReal (4 : ℝ)) ^ u * (ENNReal.ofReal r) ^ u := by
    intro r hr
    have h1 : (ENNReal.ofReal (4 * r)) ^ u = ENNReal.ofReal ((4 * r) ^ u) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hu_nonneg]
    have h2 : (4 * r) ^ u = (4 : ℝ)^u * r^u := by
      rw [Real.mul_rpow] <;> linarith
    have h3 : ENNReal.ofReal ((4 : ℝ)^u * r^u) =
        ENNReal.ofReal ((4 : ℝ)^u) * ENNReal.ofReal (r^u) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    have h4 : ENNReal.ofReal ((4 : ℝ)^u) = (ENNReal.ofReal (4 : ℝ)) ^ u := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num) hu_nonneg]
    have h5 : ENNReal.ofReal (r^u) = (ENNReal.ofReal r) ^ u := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hu_nonneg]
    rw [h1, h2, h3, h4, h5]
  have h_rearrange : ∀ (r : ℝ), 0 < r →
      (81 : ENNReal) * ENNReal.ofReal C * ((ENNReal.ofReal (4 : ℝ)) ^ u * (ENNReal.ofReal r) ^ u) =
      ENNReal.ofReal (81 * C * (4 : ℝ)^u) * (ENNReal.ofReal r) ^ u := by
    intro r hr
    have h11 : (81 : ENNReal) * ENNReal.ofReal C = ENNReal.ofReal (81 * C) := by
      have h9 : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by simp
      rw [h9, ← ENNReal.ofReal_mul (by positivity)] <;> ring
    calc (81 : ENNReal) * ENNReal.ofReal C * ((ENNReal.ofReal (4 : ℝ)) ^ u * (ENNReal.ofReal r) ^ u)
      = ENNReal.ofReal (81 * C) * ((ENNReal.ofReal (4 : ℝ)) ^ u * (ENNReal.ofReal r) ^ u) := by rw [h11]
    _ = ENNReal.ofReal (81 * C) * (ENNReal.ofReal (4 : ℝ)) ^ u * (ENNReal.ofReal r) ^ u := by ring
    _ = ENNReal.ofReal (81 * C * (4 : ℝ)^u) * (ENNReal.ofReal r) ^ u := by
      have h12 : ENNReal.ofReal (81 * C) * (ENNReal.ofReal (4 : ℝ)) ^ u =
          ENNReal.ofReal (81 * C * (4 : ℝ)^u) := by
        have h13 : ENNReal.ofReal (81 * C) * (ENNReal.ofReal (4 : ℝ)) ^ u =
            ENNReal.ofReal (81 * C) * ENNReal.ofReal ((4 : ℝ)^u) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num) hu_nonneg]
        rw [h13, ← ENNReal.ofReal_mul (by positivity)] <;> ring
      rw [h12] <;> ring
  refine' ⟨hP_nonempty, hδn_pos, by positivity, hs_nonneg, _⟩
  intro x r hr
  by_cases h_rs : δ ≤ r
  · -- Case 1: r ≥ δ
    have h1 := h_main_cover (P ∩ Metric.closedBall x r)
    have h2 := hcover x r h_rs
    have h3 : Ncover δ_n (P ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal (81 * C) * (ENNReal.ofReal r) ^ u * Ncover δ_n P := by
      calc Ncover δ_n (P ∩ Metric.closedBall x r)
        ≤ (81 : ENNReal) * Ncover δ (P ∩ Metric.closedBall x r) := h1
      _ ≤ (81 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * Ncover δ P) := by gcongr
      _ = ENNReal.ofReal (81 * C) * (ENNReal.ofReal r) ^ u * Ncover δ P := by
        have h9 : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by simp
        have h_assoc : (81 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * Ncover δ P) =
            ((81 : ENNReal) * ENNReal.ofReal C) * (ENNReal.ofReal r) ^ u * Ncover δ P := by ring
        rw [h_assoc, h9]
        have h10 : ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal C = ENNReal.ofReal (81 * C) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
        rw [h10] <;> ring
      _ ≤ ENNReal.ofReal (81 * C) * (ENNReal.ofReal r) ^ u * Ncover δ_n P := by gcongr
    calc Ncover δ_n (P ∩ Metric.closedBall x r)
      ≤ ENNReal.ofReal (81 * C) * (ENNReal.ofReal r) ^ u * Ncover δ_n P := h3
    _ ≤ ENNReal.ofReal (81 * C * (4 : ℝ)^u) * (ENNReal.ofReal r) ^ u * Ncover δ_n P := by gcongr
  · -- Case 2: δ_n ≤ r < δ
    have h_r_pos : 0 < r := by linarith
    have h4 : P ∩ Metric.closedBall x r ⊆ P ∩ Metric.closedBall x δ := by gcongr <;> linarith
    have h5 : Ncover δ_n (P ∩ Metric.closedBall x r) ≤ Ncover δ_n (P ∩ Metric.closedBall x δ) := by
      have h : Metric.externalCoveringNumber δ_n.toNNReal (P ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber δ_n.toNNReal (P ∩ Metric.closedBall x δ) :=
        Metric.externalCoveringNumber_mono_set h4
      exact_mod_cast h
    have h6 := h_main_cover (P ∩ Metric.closedBall x δ)
    have h7 := hcover x δ (by linarith)
    have hδ_lt : δ < 4 * r := by
      have h : δ_n ≤ r := by linarith
      nlinarith
    have h8 : (ENNReal.ofReal δ) ^ u ≤ (ENNReal.ofReal (4 * r)) ^ u := by gcongr <;> linarith
    have h9 := h_rpow_mul r h_r_pos
    have h10 := h_rearrange r h_r_pos
    calc Ncover δ_n (P ∩ Metric.closedBall x r)
      ≤ Ncover δ_n (P ∩ Metric.closedBall x δ) := h5
    _ ≤ (81 : ENNReal) * Ncover δ (P ∩ Metric.closedBall x δ) := h6
    _ ≤ (81 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal δ) ^ u * Ncover δ P) := by gcongr
    _ ≤ (81 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal (4 * r)) ^ u * Ncover δ_n P := by
      have h_assoc : (81 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal δ) ^ u * Ncover δ P) =
          (81 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal δ) ^ u * Ncover δ P := by ring
      rw [h_assoc]
      gcongr
    _ = (81 : ENNReal) * ENNReal.ofReal C * ((ENNReal.ofReal (4 : ℝ)) ^ u * (ENNReal.ofReal r) ^ u) * Ncover δ_n P := by
      rw [h9] <;> ring
    _ = ENNReal.ofReal (81 * C * (4 : ℝ)^u) * (ENNReal.ofReal r) ^ u * Ncover δ_n P := by
      have h10' := congr_arg (fun x => x * Ncover δ_n P) h10
      exact h10'

/-- Every point of config.pointSet is within √2·δ_n of some point in P_oriented. -/
lemma local_pointSet_close {n : ℕ} {s C : ℝ} {M : ℕ} {config : CTNiceConfiguration n s C M}
    {P_oriented : Set (EuclideanSpace ℝ (Fin 2))}
    (h_occupied : ∀ (q : DyadicSquare n), q ∈ config.P₀ → (q.toSet ∩ P_oriented).Nonempty) :
    ∀ y ∈ config.pointSet, ∃ a ∈ P_oriented, dist y a ≤ Real.sqrt 2 * dyadicDelta n := by
  intro y hy
  rcases Set.mem_iUnion₂.mp hy with ⟨q, hq, hyq⟩
  rcases h_occupied q hq with ⟨a, ha⟩
  exact ⟨a, ha.2, local_dyadic_square_dist_le_sqrt2 hyq ha.1⟩

/-- swapCoords preserves the S-set property on point sets. -/
lemma local_swapCoords_sset {δ s C : ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (h : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ s C (swapCoords '' P) := by
  have h_iso : Isometry swapCoords := swapCoords_isometry
  rcases h with ⟨hne, hδ_pos, hC_pos, hs_nonneg, hmain⟩
  refine ⟨hne.image swapCoords, hδ_pos, hC_pos, hs_nonneg, ?_⟩
  intro y r hr
  set x := swapCoords y with hx_def
  have h_y_eq : y = swapCoords x := by
    simp [hx_def, swapCoords_invol] <;> exact (swapCoords_invol y).symm
  rw [h_y_eq]
  have h_image_ball : (swapCoords '' P) ∩ Metric.closedBall (swapCoords x) r =
      swapCoords '' (P ∩ Metric.closedBall x r) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hz⟩
      refine ⟨w, ⟨hw, ?_⟩, rfl⟩
      have h_dist : dist (swapCoords w) (swapCoords x) ≤ r := hz
      have h_eq : dist (swapCoords w) (swapCoords x) = dist w x := h_iso.dist_eq w x
      rw [h_eq] at h_dist
      exact h_dist
    · rintro ⟨w, ⟨hw, hdist⟩, rfl⟩
      have h_ball : swapCoords w ∈ Metric.closedBall (swapCoords x) r := by
        simpa [Metric.mem_closedBall, h_iso.dist_eq w x] using hdist
      exact ⟨⟨w, hw, rfl⟩, h_ball⟩
  rw [h_image_ball]
  have h1 := externalCoveringNumber_image_of_involutive_isometry h_iso swapCoords_invol δ.toNNReal (P ∩ Metric.closedBall x r)
  have h2 := externalCoveringNumber_image_of_involutive_isometry h_iso swapCoords_invol δ.toNNReal P
  rw [h1, h2]
  exact hmain x r hr

/-- Transfer IsSquareRootRegular from original P at scale δ to config.pointSet at scale δ_n. -/
lemma local_config_pointSet_regular_transfer
    {δ δ_n u C K s C_config : ℝ} {n M : ℕ}
    {P P_oriented : Set (EuclideanSpace ℝ (Fin 2))}
    {config : CTNiceConfiguration n s C_config M}
    {swapped : Bool} {rho_mass : ℝ}
    (hδn_pos : 0 < δ_n) (hδ_pos : 0 < δ)
    (hδn_leδ : δ_n ≤ δ) (hδ_lt4δn : δ < 4 * δ_n)
    (hu_pos : 0 < u) (hC_pos : 0 < C) (hK_pos : 0 < K)
    (hrho_mass_nonneg : 0 ≤ rho_mass)
    (hδn_le_one : δ_n ≤ 1)
    (hδn_eq : δ_n = dyadicDelta n)
    (hP_regular : IsSquareRootRegular δ u C K P)
    (hP_oriented_sub : P_oriented ⊆ config.pointSet)
    (h_occupied : ∀ q ∈ config.P₀, (q.toSet ∩ P_oriented).Nonempty)
    (h_swapped_false : swapped = false → P_oriented ⊆ P)
    (h_swapped_true : swapped = true → P_oriented ⊆ swapCoords '' P)
    (h_mass : Ncover δ_n config.pointSet ≥
      ENNReal.ofReal (δ_n ^ rho_mass) * Ncover δ_n P)
    (hP_oriented_nonempty : P_oriented.Nonempty) :
    IsSquareRootRegular δ_n u
      (81 * C * (4 : ℝ)^u * ((2 * (Real.sqrt 2 + 1) + 4) ^ 2)^2 * (1 + Real.sqrt 2)^u * δ_n^(-rho_mass))
      (K * 9 * (2 * (Real.sqrt 2 + 1) + 4) ^ 2)
      config.pointSet := by
  let C_cover : ℝ := (2 * (Real.sqrt 2 + 1) + 4) ^ 2
  let R : ℝ := Real.sqrt 2 * δ_n
  let K_density : ℝ := C_cover * δ_n ^ (-rho_mass)
  let P' : Set (EuclideanSpace ℝ (Fin 2)) := if swapped then swapCoords '' P else P
  have hC_cover_pos : 0 < C_cover := by positivity
  have hK_density_pos : 0 < K_density := by positivity
  have hR_nonneg : 0 ≤ R := by positivity
  have hR_div : R / δ_n = Real.sqrt 2 := by
    have hR_def : R = Real.sqrt 2 * δ_n := by rfl
    rw [hR_def]
    field_simp [hδn_pos.ne'] <;> ring
  have h_const1 : (2 * (R + δ_n) / δ_n + 4) ^ 2 ≤ C_cover := by
    have h9 : 2 * (R + δ_n) / δ_n + 4 ≤ 2 * (Real.sqrt 2 + 1) + 4 := by
      have h10 : 2 * (R + δ_n) / δ_n = 2 * (R / δ_n + 1) := by
        field_simp [hδn_pos.ne'] <;> ring
      rw [h10, hR_div] <;> ring
    have h11 : 0 ≤ 2 * (R + δ_n) / δ_n + 4 := by positivity
    nlinarith
  -- Facts about P'
  have hP'_sset : IsDeltaSSet δ u C P' := by
    by_cases h : swapped
    · have hP'_eq : P' = swapCoords '' P := by simp [P', h]
      rw [hP'_eq]
      exact local_swapCoords_sset hP_regular.1
    · have hP'_eq : P' = P := by simp [P', h]
      rw [hP'_eq]
      exact hP_regular.1
  have h_sub : P_oriented ⊆ P' := by
    cases h : swapped
    · have hP'_eq : P' = P := by simp [P', h]
      rw [hP'_eq]
      exact h_swapped_false h
    · have hP'_eq : P' = swapCoords '' P := by simp [P', h]
      rw [hP'_eq]
      exact h_swapped_true h
  have h_ncover_eq : Ncover δ_n P' = Ncover δ_n P := by
    by_cases h : swapped
    · simpa [P', h] using externalCoveringNumber_image_of_involutive_isometry
        swapCoords_isometry swapCoords_invol δ_n.toNNReal P
    · simp [P', h]
  have h_sqrt_ncover_eq : Ncover (Real.sqrt δ) P' = Ncover (Real.sqrt δ) P := by
    by_cases h : swapped
    · simpa [P', h] using externalCoveringNumber_image_of_involutive_isometry
        swapCoords_isometry swapCoords_invol (Real.sqrt δ).toNNReal P
    · simp [P', h]
  -- Step 1: scale transfer δ → δ_n
  have hP'_sset_n : IsDeltaSSet δ_n u (81 * C * (4 : ℝ)^u) P' :=
    local_sset_scale_transfer_finer hδn_pos hδ_pos hδn_leδ hδ_lt4δn (by linarith) hC_pos hP'_sset
  -- Step 2: thickening relation
  have h_close : ∀ y ∈ config.pointSet, ∃ a ∈ P_oriented, dist y a ≤ R := by
    have h_close0 := local_pointSet_close h_occupied
    have hR_eq : R = Real.sqrt 2 * dyadicDelta n := by
      simp [R, hδn_eq] <;> ring
    intro y hy
    rcases h_close0 y hy with ⟨a, ha, hdist⟩
    exact ⟨a, ha, by rw [hR_eq]; exact hdist⟩
  -- Step 3: thickening cover at scale δ_n
  have h_thick_cover : Ncover δ_n config.pointSet ≤ ENNReal.ofReal C_cover * Ncover δ_n P_oriented := by
    have h := A10.plane_thickening_cover hδn_pos hR_nonneg h_close
    have h_exact : Ncover δ_n config.pointSet ≤
        ENNReal.ofReal ((2 * (R + δ_n) / δ_n + 4) ^ 2) * Ncover δ_n P_oriented := by
      convert h using 2 <;> simp [Ncover]
    have h_le : ENNReal.ofReal ((2 * (R + δ_n) / δ_n + 4) ^ 2) ≤ ENNReal.ofReal C_cover :=
      ENNReal.ofReal_le_ofReal h_const1
    calc Ncover δ_n config.pointSet
      ≤ ENNReal.ofReal ((2 * (R + δ_n) / δ_n + 4) ^ 2) * Ncover δ_n P_oriented := h_exact
    _ ≤ ENNReal.ofReal C_cover * Ncover δ_n P_oriented := by gcongr
  -- Step 4: density bound for P' relative to P_oriented
  have h_density : Ncover δ_n P' ≤ ENNReal.ofReal K_density * Ncover δ_n P_oriented := by
    have h1 : ENNReal.ofReal (δ_n ^ rho_mass) * Ncover δ_n P ≤ Ncover δ_n config.pointSet := h_mass
    have h2' : ENNReal.ofReal (δ_n ^ rho_mass) * Ncover δ_n P' ≤
        ENNReal.ofReal C_cover * Ncover δ_n P_oriented := by
      have h2 : ENNReal.ofReal (δ_n ^ rho_mass) * Ncover δ_n P ≤
          ENNReal.ofReal C_cover * Ncover δ_n P_oriented := le_trans h1 h_thick_cover
      have h_eq : Ncover δ_n P' = Ncover δ_n P := h_ncover_eq
      rw [h_eq]
      exact h2
    have h3 : 0 < δ_n ^ rho_mass := by positivity
    have h4 : δ_n ^ (-rho_mass) * δ_n ^ rho_mass = 1 := by
      have h43 : δ_n ^ ((-rho_mass) + rho_mass) = δ_n ^ (-rho_mass) * δ_n ^ rho_mass :=
        Real.rpow_add hδn_pos (-rho_mass) rho_mass
      have h44 : (-rho_mass) + rho_mass = 0 := by ring
      have h45 : δ_n ^ ((-rho_mass) + rho_mass) = 1 := by
        rw [h44] <;> simp
      exact h43.symm.trans h45
    have h5 : ENNReal.ofReal (δ_n ^ (-rho_mass)) * (ENNReal.ofReal (δ_n ^ rho_mass) * Ncover δ_n P') ≤
        ENNReal.ofReal (δ_n ^ (-rho_mass)) * (ENNReal.ofReal C_cover * Ncover δ_n P_oriented) := by
      gcongr
    have h6 : ENNReal.ofReal (δ_n ^ (-rho_mass)) * ENNReal.ofReal (δ_n ^ rho_mass) = 1 := by
      have h61 : ENNReal.ofReal (δ_n ^ (-rho_mass)) * ENNReal.ofReal (δ_n ^ rho_mass) =
          ENNReal.ofReal ((δ_n ^ (-rho_mass)) * (δ_n ^ rho_mass)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      rw [h61, h4]
      simp
    have h5' : (ENNReal.ofReal (δ_n ^ (-rho_mass)) * ENNReal.ofReal (δ_n ^ rho_mass)) * Ncover δ_n P' ≤
        ENNReal.ofReal (δ_n ^ (-rho_mass)) * (ENNReal.ofReal C_cover * Ncover δ_n P_oriented) := by
      simpa [mul_assoc] using h5
    rw [h6] at h5'
    have h5_final : Ncover δ_n P' ≤
        ENNReal.ofReal (δ_n ^ (-rho_mass)) * (ENNReal.ofReal C_cover * Ncover δ_n P_oriented) := by
      simpa [one_mul] using h5'
    have h7 : ENNReal.ofReal (δ_n ^ (-rho_mass)) * ENNReal.ofReal C_cover = ENNReal.ofReal K_density := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have h71 : (δ_n ^ (-rho_mass)) * C_cover = K_density := by
        simp [K_density] <;> ring
      rw [h71]
    have h5_final2 : Ncover δ_n P' ≤ ENNReal.ofReal K_density * Ncover δ_n P_oriented := by
      have h_rearr : ENNReal.ofReal (δ_n ^ (-rho_mass)) * (ENNReal.ofReal C_cover * Ncover δ_n P_oriented) =
          (ENNReal.ofReal (δ_n ^ (-rho_mass)) * ENNReal.ofReal C_cover) * Ncover δ_n P_oriented := by ring
      rw [h_rearr] at h5_final
      rw [h7] at h5_final
      exact h5_final
    exact h5_final2
  -- Step 5: subset S-set transfer P' → P_oriented
  have hP_oriented_sset : IsDeltaSSet δ_n u (81 * C * (4 : ℝ)^u * K_density) P_oriented :=
    Section6.thin_preserves_sset_by_density hP'_sset_n h_sub hP_oriented_nonempty hK_density_pos h_density
  -- Step 6: thickening S-set transfer P_oriented → config.pointSet
  have h_const2 : (1 + R / δ_n) ^ u ≤ (1 + Real.sqrt 2) ^ u := by
    rw [hR_div] <;> exact le_refl _
  have h_raw_const : (2 * (R + δ_n) / δ_n + 4) ^ 2 * (1 + R / δ_n) ^ u * (81 * C * (4 : ℝ)^u * K_density) ≤
      C_cover * (1 + Real.sqrt 2)^u * (81 * C * (4 : ℝ)^u * K_density) := by
    gcongr <;> linarith
  have h_config_sset_exact : IsDeltaSSet δ_n u
      ((2 * (R + δ_n) / δ_n + 4) ^ 2 * (1 + R / δ_n) ^ u * (81 * C * (4 : ℝ)^u * K_density))
      config.pointSet :=
    A10.IsDeltaSSet.thickening_plane hP_oriented_sset hP_oriented_sub hR_nonneg h_close
  have h_config_sset_raw : IsDeltaSSet δ_n u
      (C_cover * (1 + Real.sqrt 2)^u * (81 * C * (4 : ℝ)^u * K_density))
      config.pointSet :=
    IsDeltaSSet.weaken_C h_config_sset_exact h_raw_const
  have h_const_eq : C_cover * (1 + Real.sqrt 2)^u * (81 * C * (4 : ℝ)^u * K_density) =
      81 * C * (4 : ℝ)^u * (C_cover ^ 2) * (1 + Real.sqrt 2)^u * δ_n ^ (-rho_mass) := by
    simp [K_density] <;> ring
  rw [h_const_eq] at h_config_sset_raw
  have hC2 : C_cover ^ 2 = ((2 * (Real.sqrt 2 + 1) + 4) ^ 2)^2 := by
    simp [C_cover] <;> ring
  rw [hC2] at h_config_sset_raw
  -- Step 7: sqrt-scale covering bound
  have h_sqrtδn_pos : 0 < Real.sqrt δ_n := Real.sqrt_pos.mpr hδn_pos
  have h_sqrt2_lt_2 : Real.sqrt 2 < (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h_sqrt_lt : Real.sqrt δ < 2 * Real.sqrt δ_n := by
    have h1 : δ < 4 * δ_n := hδ_lt4δn
    have h2 : Real.sqrt δ < Real.sqrt (4 * δ_n) := Real.sqrt_lt_sqrt (by linarith) h1
    have h3 : Real.sqrt (4 * δ_n) = 2 * Real.sqrt δ_n := by
      have h41 : Real.sqrt (4 * δ_n) = Real.sqrt 4 * Real.sqrt δ_n := by
        rw [Real.sqrt_mul] <;> norm_num <;> linarith
      rw [h41]
      have h51 : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h51] <;> ring
    rw [h3] at h2
    have h4 : Real.sqrt 2 * Real.sqrt δ_n < 2 * Real.sqrt δ_n :=
      mul_lt_mul_of_pos_right h_sqrt2_lt_2 h_sqrtδn_pos
    linarith
  have h_step1 : Ncover (Real.sqrt δ_n) config.pointSet ≤
      (9 : ENNReal) * Ncover (2 * Real.sqrt δ_n) config.pointSet :=
    PlaneCoveringDoubling.plane_covering_doubling h_sqrtδn_pos config.pointSet
  have h_nnreal_sqrt : (Real.sqrt δ).toNNReal ≤ (2 * Real.sqrt δ_n).toNNReal := by
    have h3 : ((Real.sqrt δ).toNNReal : ℝ) ≤ ((2 * Real.sqrt δ_n).toNNReal : ℝ) := by
      simp [h_sqrt_lt.le] <;> linarith
    exact NNReal.coe_le_coe.mp h3
  have h_step2 : Ncover (2 * Real.sqrt δ_n) config.pointSet ≤ Ncover (Real.sqrt δ) config.pointSet := by
    have h : Metric.externalCoveringNumber (2 * Real.sqrt δ_n).toNNReal config.pointSet ≤
        Metric.externalCoveringNumber (Real.sqrt δ).toNNReal config.pointSet :=
      Metric.externalCoveringNumber_anti (A := config.pointSet) h_nnreal_sqrt
    exact_mod_cast h
  have h_ratio : R / Real.sqrt δ ≤ Real.sqrt 2 := by
    have h1 : δ_n ^ 2 ≤ δ_n * δ := by nlinarith
    have h51 : 0 ≤ δ_n := by linarith
    have h53 : Real.sqrt (δ_n ^ 2) ≤ Real.sqrt (δ_n * δ) := Real.sqrt_le_sqrt h1
    have h54 : Real.sqrt (δ_n ^ 2) = δ_n := Real.sqrt_sq h51
    have h2 : δ_n ≤ Real.sqrt (δ_n * δ) := by
      have h55 : Real.sqrt (δ_n ^ 2) ≤ Real.sqrt (δ_n * δ) := h53
      have h56 : Real.sqrt (δ_n ^ 2) = δ_n := h54
      rw [h56] at h55
      exact h55
    have h6 : Real.sqrt (δ_n * δ) = Real.sqrt δ_n * Real.sqrt δ := by
      rw [Real.sqrt_mul (by linarith)] <;> ring
    have h7 : δ_n ≤ Real.sqrt δ_n * Real.sqrt δ := by
      rw [h6] at h2 <;> exact h2
    have h9 : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ_pos
    have h8 : δ_n / Real.sqrt δ ≤ Real.sqrt δ_n := by
      calc δ_n / Real.sqrt δ
        ≤ (Real.sqrt δ_n * Real.sqrt δ) / Real.sqrt δ := by gcongr
      _ = Real.sqrt δ_n := by field_simp [h9.ne'] <;> ring
    have h10 : Real.sqrt δ_n ≤ 1 := by
      rw [Real.sqrt_le_left (by linarith)] <;> linarith
    have h11 : R / Real.sqrt δ = Real.sqrt 2 * (δ_n / Real.sqrt δ) := by
      simp [R] <;> ring
    rw [h11]
    have h12 : Real.sqrt 2 * (δ_n / Real.sqrt δ) ≤ Real.sqrt 2 * Real.sqrt δ_n := by gcongr
    have h13 : Real.sqrt 2 * Real.sqrt δ_n ≤ Real.sqrt 2 := by
      calc Real.sqrt 2 * Real.sqrt δ_n
        ≤ Real.sqrt 2 * 1 := by gcongr
      _ = Real.sqrt 2 := by ring
    linarith
  have h_const_le : (2 * (R + Real.sqrt δ) / Real.sqrt δ + 4) ^ 2 ≤ C_cover := by
    have h9 : 2 * (R + Real.sqrt δ) / Real.sqrt δ + 4 ≤ 2 * (Real.sqrt 2 + 1) + 4 := by
      have h10 : 2 * (R + Real.sqrt δ) / Real.sqrt δ = 2 * (R / Real.sqrt δ + 1) := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h10]
      gcongr <;> linarith
    have h11 : 0 ≤ 2 * (R + Real.sqrt δ) / Real.sqrt δ + 4 := by positivity
    nlinarith
  have h_step3 : Ncover (Real.sqrt δ) config.pointSet ≤
      ENNReal.ofReal C_cover * Ncover (Real.sqrt δ) P_oriented := by
    have h_exact := A10.plane_thickening_cover (Real.sqrt_pos.mpr hδ_pos) hR_nonneg h_close
    calc Ncover (Real.sqrt δ) config.pointSet
      ≤ ENNReal.ofReal ((2 * (R + Real.sqrt δ) / Real.sqrt δ + 4) ^ 2) *
          Ncover (Real.sqrt δ) P_oriented := h_exact
    _ ≤ ENNReal.ofReal C_cover * Ncover (Real.sqrt δ) P_oriented := by
      gcongr
  have h_step4 : Ncover (Real.sqrt δ) P_oriented ≤ Ncover (Real.sqrt δ) P' := by
    have h : Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P_oriented ≤
        Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P' :=
      Metric.externalCoveringNumber_mono_set h_sub
    exact_mod_cast h
  have h_step6 : Ncover (Real.sqrt δ) P ≤ ENNReal.ofReal (K * δ ^ (-u / 2)) := hP_regular.2
  have h_v_pos : 0 < u / 2 := by linarith
  have h_exp1 : δ_n ^ (u / 2) ≤ δ ^ (u / 2) := by
    gcongr <;> linarith
  have h_exp2 : 0 < δ_n ^ (u / 2) := Real.rpow_pos_of_pos hδn_pos (u / 2)
  have h_exp3 : 0 < δ ^ (u / 2) := Real.rpow_pos_of_pos hδ_pos (u / 2)
  have h_exp_le : δ ^ (-u / 2) ≤ δ_n ^ (-u / 2) := by
    have h4 : δ ^ (-u / 2) = 1 / δ ^ (u / 2) := by
      have h_eq : (-u / 2) = -(u / 2) := by ring
      have h41 : δ ^ (-u / 2) = (δ ^ (u / 2))⁻¹ := by
        rw [h_eq]
        exact Real.rpow_neg hδ_pos.le (u / 2)
      rw [h41] <;> field_simp
    have h5 : δ_n ^ (-u / 2) = 1 / δ_n ^ (u / 2) := by
      have h_eq : (-u / 2) = -(u / 2) := by ring
      have h51 : δ_n ^ (-u / 2) = (δ_n ^ (u / 2))⁻¹ := by
        rw [h_eq]
        exact Real.rpow_neg hδn_pos.le (u / 2)
      rw [h51] <;> field_simp
    rw [h4, h5]
    apply one_div_le_one_div_of_le
    <;> linarith
  have h_algebra : (9 : ENNReal) * (ENNReal.ofReal C_cover * ENNReal.ofReal (K * δ ^ (-u / 2))) =
      ENNReal.ofReal (K * 9 * C_cover * δ ^ (-u / 2)) := by
    have h1 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by simp
    rw [h1]
    have h2 : ENNReal.ofReal (9 : ℝ) * (ENNReal.ofReal C_cover * ENNReal.ofReal (K * δ ^ (-u / 2))) =
        ENNReal.ofReal ((9 : ℝ) * (C_cover * (K * δ ^ (-u / 2)))) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h2] <;> ring_nf
  have h_sqrt_final : Ncover (Real.sqrt δ_n) config.pointSet ≤
      ENNReal.ofReal ((K * 9 * C_cover) * δ_n ^ (-u / 2)) := by
    calc Ncover (Real.sqrt δ_n) config.pointSet
      ≤ (9 : ENNReal) * Ncover (2 * Real.sqrt δ_n) config.pointSet := h_step1
    _ ≤ (9 : ENNReal) * Ncover (Real.sqrt δ) config.pointSet := by gcongr
    _ ≤ (9 : ENNReal) * (ENNReal.ofReal C_cover * Ncover (Real.sqrt δ) P_oriented) := by gcongr
    _ ≤ (9 : ENNReal) * (ENNReal.ofReal C_cover * Ncover (Real.sqrt δ) P') := by gcongr
    _ = (9 : ENNReal) * (ENNReal.ofReal C_cover * Ncover (Real.sqrt δ) P) := by
      rw [h_sqrt_ncover_eq]
    _ ≤ (9 : ENNReal) * (ENNReal.ofReal C_cover * ENNReal.ofReal (K * δ ^ (-u / 2))) := by gcongr
    _ = ENNReal.ofReal (K * 9 * C_cover * δ ^ (-u / 2)) := h_algebra
    _ ≤ ENNReal.ofReal (K * 9 * C_cover * δ_n ^ (-u / 2)) := by
      gcongr <;> linarith
  have hK'_eq : (K * 9 * C_cover) = K * 9 * (2 * (Real.sqrt 2 + 1) + 4) ^ 2 := by
    simp [C_cover] <;> ring
  rw [hK'_eq] at h_sqrt_final
  exact ⟨h_config_sset_raw, h_sqrt_final⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
