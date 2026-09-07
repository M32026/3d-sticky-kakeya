module

/-
  Between-Scales Transfer for the Genuine Inductive Step

  When the B1 bridge normalizes a coarse square Q (scale Δ₁) to [0,1)²,
  the point set P_Q = S_Q(P ∩ Q) inherits between-scales properties from P.

  Core lemmas (already proved in GoodTransfer.lean):
  - set_between_scales_rescale: IsSetBetweenScales transfer
  - regular_between_scales_rescale: IsRegularBetweenScales transfer

  This module provides a combined wrapper tailored to the CombiningConfig
  context: given h_normal/h_good at scales Δ_{j+1} ⊂ Δ_j, transfer them
  to the normalized set at scales Δ_{j+1}/Δ₁ and Δ_j/Δ₁.

  Whiteprint node: combining_theorem_rework / between_scales_transfer
  References: OS lines 1038-1054, 1066-1072
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GoodTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem

-- Plane is already defined in GoodTransfer.lean (imported above)

/-- Transfer all between-scales properties from P to P_Q = S_Q(P ∩ Q).

    Given P with between-scales properties at scales (Δ_{j+1}, Δ_j) for
    each scale block j, and a coarse square Q at scale Δ₁ with Δ_j ≤ Δ₁,
    the normalized set P_Q inherits the same properties at rescaled
    scales (Δ_{j+1}/Δ₁, Δ_j/Δ₁).

    This is the key lemma used in the inductive step of Proposition 7.3:
    the B1 bridge produces fine configurations inside each coarse square,
    and their between-scales data is obtained by this transfer. -/
lemma between_scales_transfer_all
    {P : Set Plane} {Δ₁ : ℝ} {i₀ j₀ : ℤ}
    (hΔ₁_pos : 0 < Δ₁)
    (hΔ₁_dyadic : Δ₁ ∈ dyadicScales)
    (n : ℕ)
    (Δ : Fin (n + 1) → ℝ)
    (hΔ_dyadic : ∀ i, Δ i ∈ dyadicScales)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (hΔ_decreasing : ∀ j : Fin n, Δ (Fin.succ j) ≤ Δ j.castSucc)
    (hΔ_j_le_Δ₁ : ∀ j : Fin n, Δ j.castSucc ≤ Δ₁)
    (scaleClass : Fin n → ScaleClass)
    (s : ℝ)
    (C_between : Fin n → ℝ)
    (h_normal : ∀ (j : Fin n),
      scaleClass j = ScaleClass.normal →
        IsSetBetweenScales P (Δ (Fin.succ j)) (Δ j.castSucc) s (C_between j))
    (h_good : ∀ (j : Fin n) (t_j : ℝ),
      scaleClass j = ScaleClass.good t_j →
        IsRegularBetweenScales P (Δ (Fin.succ j)) (Δ j.castSucc) t_j
          (C_between j) (C_between j)) :
    let P_Q : Set Plane := homothetyS Δ₁ i₀ j₀ '' (P ∩ dyadicSquare Δ₁ i₀ j₀)
    (∀ (j : Fin n),
      scaleClass j = ScaleClass.normal →
        IsSetBetweenScales P_Q
          (Δ (Fin.succ j) / Δ₁) (Δ j.castSucc / Δ₁) s (C_between j)) ∧
    (∀ (j : Fin n) (t_j : ℝ),
      scaleClass j = ScaleClass.good t_j →
        IsRegularBetweenScales P_Q
          (Δ (Fin.succ j) / Δ₁) (Δ j.castSucc / Δ₁) t_j
          (C_between j) (C_between j)) := by
  let P_Q : Set Plane := homothetyS Δ₁ i₀ j₀ '' (P ∩ dyadicSquare Δ₁ i₀ j₀)
  have h1 : ∀ (j : Fin n),
      scaleClass j = ScaleClass.normal →
        IsSetBetweenScales P_Q
          (Δ (Fin.succ j) / Δ₁) (Δ j.castSucc / Δ₁) s (C_between j) := by
    intro j hj
    have hδ_pos : 0 < Δ (Fin.succ j) := hΔ_pos (Fin.succ j)
    have hΔ_pos' : 0 < Δ j.castSucc := hΔ_pos j.castSucc
    have hΔ_le : Δ (Fin.succ j) ≤ Δ j.castSucc := hΔ_decreasing j
    have hΔj_le_Δ₁ : Δ j.castSucc ≤ Δ₁ := hΔ_j_le_Δ₁ j
    exact set_between_scales_rescale
      hδ_pos hΔ_pos' hΔ₁_pos hΔj_le_Δ₁
      hΔ₁_dyadic (hΔ_dyadic j.castSucc)
      (h_normal j hj) i₀ j₀
  have h2 : ∀ (j : Fin n) (t_j : ℝ),
      scaleClass j = ScaleClass.good t_j →
        IsRegularBetweenScales P_Q
          (Δ (Fin.succ j) / Δ₁) (Δ j.castSucc / Δ₁) t_j
          (C_between j) (C_between j) := by
    intro j t_j hj
    have hδ_pos : 0 < Δ (Fin.succ j) := hΔ_pos (Fin.succ j)
    have hΔ_pos' : 0 < Δ j.castSucc := hΔ_pos j.castSucc
    have hΔ_le : Δ (Fin.succ j) ≤ Δ j.castSucc := hΔ_decreasing j
    have hΔj_le_Δ₁ : Δ j.castSucc ≤ Δ₁ := hΔ_j_le_Δ₁ j
    exact regular_between_scales_rescale
      hδ_pos hΔ_pos' hΔ₁_pos hΔj_le_Δ₁
      hΔ₁_dyadic (hΔ_dyadic j.castSucc)
      (h_good j t_j hj) i₀ j₀
  exact ⟨h1, h2⟩

/-- Transfer a single IsSetBetweenScales property under homothety.

    Convenience wrapper around `set_between_scales_rescale` with named
    arguments matching the CombiningConfig field order. -/
lemma transfer_normal
    {P : Set Plane} {δ Δ Δ₁ s C : ℝ} {i₀ j₀ : ℤ}
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hΔ₁_pos : 0 < Δ₁)
    (hΔ_le_Δ₁ : Δ ≤ Δ₁)
    (hΔ₁_dyadic : Δ₁ ∈ dyadicScales) (hΔ_dyadic : Δ ∈ dyadicScales)
    (h : IsSetBetweenScales P δ Δ s C) :
    IsSetBetweenScales
      (homothetyS Δ₁ i₀ j₀ '' (P ∩ dyadicSquare Δ₁ i₀ j₀))
      (δ / Δ₁) (Δ / Δ₁) s C :=
  set_between_scales_rescale hδ_pos hΔ_pos hΔ₁_pos hΔ_le_Δ₁
    hΔ₁_dyadic hΔ_dyadic h i₀ j₀

/-- Transfer a single IsRegularBetweenScales property under homothety.

    Convenience wrapper around `regular_between_scales_rescale`. -/
lemma transfer_good
    {P : Set Plane} {δ Δ Δ₁ t C K : ℝ} {i₀ j₀ : ℤ}
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hΔ₁_pos : 0 < Δ₁)
    (hΔ_le_Δ₁ : Δ ≤ Δ₁)
    (hΔ₁_dyadic : Δ₁ ∈ dyadicScales) (hΔ_dyadic : Δ ∈ dyadicScales)
    (h : IsRegularBetweenScales P δ Δ t C K) :
    IsRegularBetweenScales
      (homothetyS Δ₁ i₀ j₀ '' (P ∩ dyadicSquare Δ₁ i₀ j₀))
      (δ / Δ₁) (Δ / Δ₁) t C K :=
  regular_between_scales_rescale hδ_pos hΔ_pos hΔ₁_pos hΔ_le_Δ₁
    hΔ₁_dyadic hΔ_dyadic h i₀ j₀

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
