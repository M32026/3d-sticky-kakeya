module

/-
  Helper: convert IsSetBetweenScales (at Δ=1) to IsDeltaSSet on the full set.

  When P ⊆ [0,1)² and Δ=1, only the unit square (i,j)=(0,0) intersects P,
  and homothetyS 1 0 0 is the identity. Thus IsSetBetweenScales P δ 1 s C
  directly gives IsDeltaSSet δ s C P.

  Also provides exponent weakening for IsDeltaSSet:
  an S-set at exponent s₂ implies one at exponent s₁ when 0 ≤ s₁ ≤ s₂,
  using the fact that for r ≥ 1 the bound follows from monotonicity
  (C * r^{s₁} ≥ 1), and for r ≤ 1 we have r^{s₂} ≤ r^{s₁}.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem

abbrev Plane' := EuclideanSpace ℝ (Fin 2)

/-- Convert IsSetBetweenScales at Δ=1 to IsDeltaSSet when P ⊆ unit square. -/
lemma isSetBetweenScales_to_isDeltaSSet_unit
    {P : Set Plane'} {δ s C : ℝ}
    (h : IsSetBetweenScales P δ 1 s C)
    (hP_sub : P ⊆ dyadicSquare 1 0 0)
    (hP_nonempty : P.Nonempty) :
    IsDeltaSSet δ s C P := by
  have h1 : (P ∩ dyadicSquare 1 0 0).Nonempty := by
    exact hP_nonempty.mono (fun x hx => ⟨hx, hP_sub hx⟩)
  have h_main : ∀ (i j : ℤ), (P ∩ dyadicSquare 1 i j).Nonempty →
      IsDeltaSSet (δ / 1) s C (homothetyS 1 i j '' (P ∩ dyadicSquare 1 i j)) :=
    h.2.2.2.2.2
  have h2 := h_main 0 0 h1
  have h3 : δ / 1 = δ := by ring
  rw [h3] at h2
  have h4 : homothetyS 1 0 0 = id := by
    funext x
    simp [homothetyS]
    <;> ext i <;> fin_cases i <;> simp <;> ring
  have h5 : P ∩ dyadicSquare 1 0 0 = P := by
    apply Set.inter_eq_left.mpr
    exact hP_sub
  rw [h4, h5] at h2
  simpa using h2

/-- Exponent weakening for IsDeltaSSet.

    If 0 ≤ s₁ ≤ s₂ and C ≥ 1, then an (s₂, C)-set is also an (s₁, C)-set.

    Proof:
    - For r ≤ 1: r^{s₂} ≤ r^{s₁}, so the (s₂)-bound implies the (s₁)-bound.
    - For r ≥ 1: Ncover(P ∩ ball) ≤ Ncover(P) by monotonicity, and
      C * r^{s₁} ≥ 1, so C * r^{s₁} * Ncover(P) ≥ Ncover(P). -/
lemma IsDeltaSSet.weaken_exponent
    {X : Type*} [MetricSpace X] {P : Set X} {δ s₁ s₂ C : ℝ}
    (h : IsDeltaSSet δ s₂ C P)
    (hs1_nonneg : 0 ≤ s₁)
    (hs12 : s₁ ≤ s₂)
    (hC_ge1 : 1 ≤ C) :
    IsDeltaSSet δ s₁ C P := by
  refine' ⟨h.1, h.2.1, h.2.2.1, hs1_nonneg, _⟩
  intro x r hr
  by_cases h_r_le_one : r ≤ 1
  · -- Case r ≤ 1: r^{s₂} ≤ r^{s₁}
    have h6 := h.2.2.2.2 x r hr
    have h_r_nonneg : 0 ≤ r := by linarith [h.2.1]
    have h7 : (ENNReal.ofReal r) ^ s₂ ≤ (ENNReal.ofReal r) ^ s₁ := by
      have h8 : ENNReal.ofReal r ≤ 1 := by
        rw [ENNReal.ofReal_le_one] <;> linarith
      exact ENNReal.rpow_le_rpow_of_exponent_ge h8 hs12
    calc
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ℝ≥0∞)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s₂ *
            (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := h6
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s₁ *
            (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := by gcongr
  · -- Case r > 1: use monotonicity and C * r^{s₁} ≥ 1
    have h_r_gt_one : 1 < r := by linarith
    have h_r_nonneg : 0 ≤ r := by linarith
    have h9 : (P ∩ Metric.closedBall x r) ⊆ P := by simp
    have h10 : Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) ≤
        Metric.externalCoveringNumber δ.toNNReal P :=
      Metric.externalCoveringNumber_mono_set h9
    have h11 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s₁ := by
      have h12 : (1 : ENNReal) ≤ ENNReal.ofReal C := by
        simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hC_ge1
      have h13 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s₁ := by
        have h14 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
          have h15 : (1 : ℝ) ≤ r := by linarith
          simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h15
        by_cases h16 : 0 < s₁
        · exact ENNReal.one_le_rpow h14 h16
        · have h17 : s₁ = 0 := by linarith
          rw [h17]
          simp
      calc
        (1 : ENNReal) = (1 : ENNReal) * (1 : ENNReal) := by simp
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s₁ := by gcongr
    calc
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ℝ≥0∞)
        ≤ (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := by exact_mod_cast h10
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s₁ *
            Metric.externalCoveringNumber δ.toNNReal P := by
      have h15 : (1 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ s₁ * Metric.externalCoveringNumber δ.toNNReal P := by
        gcongr
      simpa using h15

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
