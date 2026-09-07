module

/-
  S0 Regularity Transfer Helpers

  Provides scale_squareRootRegular: transfers IsSquareRootRegular through a
  1/4-scaling + translation map.

  Also documents the fix for Issue 3: use out.hConfig_regular directly
  instead of inventing C_P_reg/K_P_reg.

  Whiteprint node: s0_regularity_transfer
  Status: IMPLEMENTED
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence

/-- Monotonicity of external covering number in radius:
    if 0 ≤ ε₁ ≤ ε₂, then Ncover(ε₂, E) ≤ Ncover(ε₁, E). -/
lemma ncover_antitone {X : Type*} [PseudoMetricSpace X] {ε₁ ε₂ : ℝ}
    (h : ε₁ ≤ ε₂) (hε₁ : 0 ≤ ε₁) {E : Set X} :
    Ncover ε₂ E ≤ Ncover ε₁ E := by
  have hε₂_nonneg : 0 ≤ ε₂ := by linarith
  have h1 : (ε₁.toNNReal : ℝ) ≤ (ε₂.toNNReal : ℝ) := by
    have h1a : (ε₁.toNNReal : ℝ) = ε₁ := by
      exact Real.coe_toNNReal ε₁ hε₁
    have h2a : (ε₂.toNNReal : ℝ) = ε₂ := by exact Real.coe_toNNReal ε₂ hε₂_nonneg
    rw [h1a, h2a] <;> linarith
  have h1' : ε₁.toNNReal ≤ ε₂.toNNReal := NNReal.coe_le_coe.mpr h1
  have h2 : Metric.externalCoveringNumber ε₂.toNNReal E ≤
      Metric.externalCoveringNumber ε₁.toNNReal E :=
    Metric.externalCoveringNumber_anti h1'
  simpa [Ncover] using h2

/-- Transfer IsSquareRootRegular through a 1/4-scaling + translation map S0.

    Given:
    - `hS0_sset`: transfers IsDeltaSSet through S0 (scale factor 4^u)
    - `hS0_ncover`: Ncover(r, S0 '' P) = Ncover(4*r, P) for all r > 0

    Produces IsSquareRootRegular at scale δ/4 with:
    - new S-set constant: C * 4^u
    - new sqrt constant: K (unchanged)

    Proof of sqrt bound:
      Ncover(√(δ/4), S0 '' P) = Ncover(2√δ, P)  (scaling property)
                              ≤ Ncover(√δ, P)     (antitone)
                              ≤ K · δ^{-u/2}
                              ≤ K · (δ/4)^{-u/2}
-/
lemma scale_squareRootRegular
    {δ u C K : ℝ} {P : Set EuclideanPlane} {S0 : EuclideanPlane → EuclideanPlane}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hu_nonneg : 0 ≤ u) (hK_nonneg : 0 ≤ K)
    (hS0_sset : ∀ {t C : ℝ}, IsDeltaSSet δ t C P →
      IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t) (S0 '' P))
    (hS0_ncover : ∀ (r : ℝ), 0 < r →
      Ncover r (S0 '' P) = Ncover (4 * r) P)
    (h : IsSquareRootRegular δ u C K P) :
    IsSquareRootRegular (δ / 4) u (C * (4 : ℝ)^u) K (S0 '' P) := by
  have hδ4_pos : 0 < δ / 4 := by positivity
  have h_sqrt4_pos : 0 < Real.sqrt (δ / 4) := Real.sqrt_pos.mpr hδ4_pos

  -- S-set transfer
  have h_sset : IsDeltaSSet (δ / 4) u (C * (4 : ℝ)^u) (S0 '' P) :=
    hS0_sset h.1

  -- Covering number transfer for sqrt scale
  have h1 : Ncover (Real.sqrt (δ / 4)) (S0 '' P) =
      Ncover (4 * Real.sqrt (δ / 4)) P :=
    hS0_ncover (Real.sqrt (δ / 4)) h_sqrt4_pos

  have h2 : 4 * Real.sqrt (δ / 4) = 2 * Real.sqrt δ := by
    have hδ_nonneg : 0 ≤ δ := by linarith
    have h3 : Real.sqrt (δ / 4) = Real.sqrt δ / 2 := by
      have h4 : Real.sqrt (δ / 4) = Real.sqrt δ / Real.sqrt 4 :=
        (Real.sqrt_div hδ_nonneg) 4
      rw [h4]
      have h5 : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h5] <;> ring
    rw [h3] <;> ring

  have h4 : Real.sqrt δ ≤ 2 * Real.sqrt δ := by
    have h5 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
    linarith

  have h_main1 : Ncover (Real.sqrt (δ / 4)) (S0 '' P) ≤
      Ncover (Real.sqrt δ) P := by
    calc Ncover (Real.sqrt (δ / 4)) (S0 '' P)
      = Ncover (4 * Real.sqrt (δ / 4)) P := hS0_ncover (Real.sqrt (δ / 4)) h_sqrt4_pos
    _ = Ncover (2 * Real.sqrt δ) P := by rw [h2]
    _ ≤ Ncover (Real.sqrt δ) P := ncover_antitone h4 (Real.sqrt_nonneg δ)

  have h6 : Ncover (Real.sqrt δ) P ≤ ENNReal.ofReal (K * Real.rpow δ (-u / 2)) := h.2

  have h7 : K * Real.rpow δ (-u / 2) ≤ K * Real.rpow (δ / 4) (-u / 2) := by
    have h8 : Real.rpow δ (-u / 2) ≤ Real.rpow (δ / 4) (-u / 2) := by
      have h9 : -u / 2 ≤ 0 := by linarith
      exact Real.rpow_le_rpow_of_nonpos hδ4_pos (by linarith) h9
    gcongr

  have h_final : Ncover (Real.sqrt (δ / 4)) (S0 '' P) ≤
      ENNReal.ofReal (K * Real.rpow (δ / 4) (-u / 2)) :=
    le_trans h_main1 (le_trans h6 (ENNReal.ofReal_le_ofReal h7))

  exact ⟨h_sset, h_final⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
