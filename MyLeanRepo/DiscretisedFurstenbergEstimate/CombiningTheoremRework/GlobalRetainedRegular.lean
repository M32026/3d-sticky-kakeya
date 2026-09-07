module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1ToSection6
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.CommonLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.RegularIncidence

/-- Upper bound: Ncover(δ_n, pointSet) ≤ |P₀| via center covering. -/
lemma pointSet_ncover_upper {n : ℕ} {s C₁ : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C₁ M) :
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet ≤
      (config.P₀.card : ENNReal) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let centers : Finset (EuclideanSpace ℝ (Fin 2)) :=
    config.P₀.image (fun p : DyadicSquare n => squareCenter δ p)
  have h1 : config.pointSet ⊆ ⋃ c ∈ (centers : Set (EuclideanSpace ℝ (Fin 2))),
      Metric.closedBall c δ.toNNReal := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨p, hp, hyp⟩
    let c := squareCenter δ p
    have hc_in : c ∈ centers := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hcov : y ∈ Metric.closedBall c δ :=
      dyadicSquare_covered_by_center hδ_pos (by rfl) p hyp
    have hcov' : y ∈ Metric.closedBall c δ.toNNReal := by
      have h5 : ((δ.toNNReal : ℝ)) = δ := by
        simp [NNReal.coe_mk, hδ_pos.le] <;> linarith
      simpa [Metric.mem_closedBall, h5] using hcov
    exact Set.mem_iUnion₂.mpr ⟨c, hc_in, hcov'⟩
  have h_iscover : Metric.IsCover δ.toNNReal config.pointSet (centers : Set _) :=
    Metric.IsCover.of_subset_iUnion_closedBall h1
  have h6_enat : Metric.externalCoveringNumber δ.toNNReal config.pointSet ≤
      (centers : Set (EuclideanSpace ℝ (Fin 2))).encard :=
    h_iscover.externalCoveringNumber_le_encard
  have h7 : (centers : Set (EuclideanSpace ℝ (Fin 2))).encard = ↑centers.card := by simp
  have h8 : Metric.externalCoveringNumber δ.toNNReal config.pointSet ≤ ↑centers.card := by
    rw [h7] at h6_enat
    exact h6_enat
  have h9 : centers.card ≤ config.P₀.card := Finset.card_image_le
  have h10 : (Metric.externalCoveringNumber δ.toNNReal config.pointSet : ENNReal) ≤
      (config.P₀.card : ENNReal) := by
    exact_mod_cast (le_trans h8 (by exact_mod_cast h9))
  exact h10

/-- Global retained point regularity.

    Given original `IsSquareRootRegular` on the full point set, B1-retained
    squares `P`, and a global cardinality retention bound, prove that the
    retained point set is also `IsSquareRootRegular`.

    The S-set constant degrades by `9 * K_global`; the sqrt-scale bound
    is preserved with the same `K` since the retained set is a subset. -/
theorem global_retained_regular
    {n m : ℕ} {hnm : m ≤ n} {s t C K C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (hReg : IsSquareRootRegular (dyadicDelta n) t C K config.pointSet)
    (P : Finset (DyadicSquare n))
    (hP_sub : P ⊆ config.P₀)
    (K_global : ℝ) (hK_global_pos : 0 < K_global)
    (h_global_ret : (config.P₀.card : ℝ) ≤ K_global * (P.card : ℝ))
    (hP_nonempty : P.Nonempty) :
    IsSquareRootRegular (dyadicDelta n) t (C * 9 * K_global) K
      (⋃ p ∈ (P : Set (DyadicSquare n)), (p.toSet : Set (EuclideanSpace ℝ (Fin 2)))) := by
  let δ_n := dyadicDelta n
  let E := config.pointSet
  let E' : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ p ∈ (P : Set (DyadicSquare n)), (p.toSet : Set (EuclideanSpace ℝ (Fin 2)))
  let Ncover_E : ENNReal := Metric.externalCoveringNumber δ_n.toNNReal E
  let Ncover_E' : ENNReal := Metric.externalCoveringNumber δ_n.toNNReal E'
  have hδ_pos : 0 < δ_n := dyadicDelta_pos n

  -- Step 1: E' ⊆ E
  have h_sub : E' ⊆ E := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    have h_p_in_P0 : p ∈ config.P₀ := hP_sub hp
    exact Set.mem_iUnion₂.mpr ⟨p, h_p_in_P0, hxp⟩

  -- Step 2: E' nonempty
  have hE'_nonempty : E'.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    have h_nonempty : (p.toSet : Set (EuclideanSpace ℝ (Fin 2))).Nonempty :=
      DyadicSquare.toSet_nonempty p
    rcases h_nonempty with ⟨x, hx⟩
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨p, hp, hx⟩⟩

  -- Step 3: Upper bound Ncover(δ_n, E) ≤ |config.P₀|
  have h_upper : Ncover_E ≤ (config.P₀.card : ENNReal) :=
    pointSet_ncover_upper config

  -- Step 4: Lower bound |P| ≤ 9 * Ncover(δ_n, E')
  have h_lower : (P.card : ENNReal) ≤ (9 : ENNReal) * Ncover_E' :=
    finset_squares_ncover_lower P

  -- Step 5: Global density bound
  -- Ncover(E) ≤ |P0| ≤ K_global * |P| ≤ K_global * 9 * Ncover(E')
  have h9K_pos : 0 < 9 * K_global := by positivity
  have h_density : Ncover_E ≤ ENNReal.ofReal (9 * K_global) * Ncover_E' := by
    calc Ncover_E
        ≤ (config.P₀.card : ENNReal) := h_upper
      _ ≤ ENNReal.ofReal (K_global * (P.card : ℝ)) := by
        have h_cast : (config.P₀.card : ENNReal) = ENNReal.ofReal (config.P₀.card : ℝ) := by simp
        rw [h_cast]
        exact ENNReal.ofReal_le_ofReal h_global_ret
      _ = ENNReal.ofReal K_global * (P.card : ENNReal) := by
        have hKg_nonneg : 0 ≤ K_global := by linarith
        simp [ENNReal.ofReal_mul hKg_nonneg] <;> norm_cast
      _ ≤ ENNReal.ofReal K_global * ((9 : ENNReal) * Ncover_E') := by gcongr
      _ = ENNReal.ofReal (9 * K_global) * Ncover_E' := by
        have hKg_nonneg : 0 ≤ K_global := by linarith
        have h_step1 : ENNReal.ofReal K_global * ((9 : ENNReal) * Ncover_E') =
            (ENNReal.ofReal K_global * (9 : ENNReal)) * Ncover_E' := by simp [mul_assoc]
        rw [h_step1]
        have h_mul2 : ENNReal.ofReal K_global * (9 : ENNReal) = ENNReal.ofReal (K_global * 9) := by
          rw [ENNReal.ofReal_mul hKg_nonneg] <;> norm_cast
        rw [h_mul2]
        have h_comm : K_global * 9 = 9 * K_global := by ring
        rw [h_comm]

  -- Step 6: S-set transfer via density
  have h_sset : IsDeltaSSet δ_n t (C * 9 * K_global) E' := by
    have h : IsDeltaSSet δ_n t (C * (9 * K_global)) E' :=
      DirecretisedFurstenbergEstimate.Section6.thin_preserves_sset_by_density hReg.1 h_sub hE'_nonempty h9K_pos h_density
    have h_eq : C * (9 * K_global) = C * 9 * K_global := by ring
    rw [h_eq] at h
    exact h

  -- Step 7: Sqrt-scale bound preserved by subset
  have h_sqrt : (Metric.externalCoveringNumber (Real.sqrt δ_n).toNNReal E' : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow δ_n (-t / 2)) := by
    have h_mono : ∀ (s : Set (EuclideanSpace ℝ (Fin 2))) (_ : s ⊆ E),
        (Metric.externalCoveringNumber (Real.sqrt δ_n).toNNReal s : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.sqrt δ_n).toNNReal E : ENNReal) := by
      intro s hs
      exact_mod_cast Metric.externalCoveringNumber_mono_set hs
    have h1 := h_mono E' h_sub
    have hReg2 : (Metric.externalCoveringNumber (Real.sqrt δ_n).toNNReal E : ENNReal) ≤
        ENNReal.ofReal (K * Real.rpow δ_n (-t / 2)) := hReg.2
    exact le_trans h1 hReg2

  exact ⟨h_sset, h_sqrt⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
