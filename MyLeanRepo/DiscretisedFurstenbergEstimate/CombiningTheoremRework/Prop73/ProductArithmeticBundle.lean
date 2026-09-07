module

/-
  Split 3: Product arithmetic bundle — extracted from InductiveStepCore_v2_Body.lean

  Extracts lines 357-401 (product splitting) plus h_product expansion (398-402)
  into a standalone lemma.

  Inputs: Δ, scaleClass, N, C_between, hcfg, j0, G0, B0, PΔ, and bound constants.
  Outputs: shifted data (Δ', scaleClass', N', C_between'), tail products (G', B', Pb),
           product splitting lemmas, and full h_product expansion.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.ProductSplittingExtra
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.TailSplit
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion

/-- Product arithmetic bundle: shifted scale data, tail product definitions,
    product splitting lemmas, and full combiningLowerBound expansion. -/
lemma product_arithmetic_bundle
    {n_fine k M : ℕ}
    {s t τ ε_G η ε_N C_P lam C C' : ℝ}
    (Δ : Fin (n_fine + 2) → ℝ)
    (scaleClass : Fin (n_fine + 1) → ScaleClass)
    (N : Fin (n_fine + 1) → ℕ)
    (C_between : Fin (n_fine + 1) → ℝ)
    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (hcfg : CombiningConfig s t τ (n_fine + 1) ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (j0 : Fin (n_fine + 1))
    (hj0 : j0.val = 0)
    (G0 B0 : Finset (Fin (n_fine + 1)))
    (hG0 : G0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood))
    (hB0 : B0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad))
    (PΔ : ℝ)
    (hPΔ_pos : 0 < PΔ)
    (hPΔ_def : PΔ = (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
                      (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc)) :
    ∃ (Δ' : Fin (n_fine + 1) → ℝ)
      (scaleClass' : Fin n_fine → ScaleClass)
      (N' : Fin n_fine → ℕ)
      (C_between' : Fin n_fine → ℝ)
      (G' B' : Finset (Fin n_fine))
      (Pb : ℝ),
      (∀ i, Δ' i = Δ (Fin.succ i) / Δ 1) ∧
      (∀ j, scaleClass' j = scaleClass (Fin.succ j)) ∧
      (∀ j, N' j = N (Fin.succ j)) ∧
      (∀ j, C_between' j = C_between (Fin.succ j)) ∧
      (G' = (Finset.univ : Finset (Fin n_fine)).filter (fun j => (scaleClass' j).isGood)) ∧
      (B' = (Finset.univ : Finset (Fin n_fine)).filter (fun j => (scaleClass' j).isBad)) ∧
      (Pb = (∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η) *
               (∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc)) ∧
      0 < Pb ∧
      ((∏ j ∈ (Finset.univ : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood),
          Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) =
        (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
        (∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η)) ∧
      ((∏ j ∈ (Finset.univ : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad),
          Δ (Fin.succ j) / Δ j.castSucc) =
        (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc) *
        (∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc)) ∧
      (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass =
        Real.rpow (Real.log (1 / dyadicDelta k)) (-C) * (M : ℝ) *
        Real.rpow (dyadicDelta k) (C' * lam) * Real.rpow (dyadicDelta k) (-s + ε_N) * (PΔ * Pb)) := by
  let shift : Fin n_fine → Fin (n_fine + 1) := Fin.succ
  let Δ' : Fin (n_fine + 1) → ℝ := fun i =>
    Δ (⟨i.val + 1, by omega⟩ : Fin (n_fine + 2)) / Δ 1
  let scaleClass' : Fin n_fine → ScaleClass := fun j => scaleClass (shift j)
  let N' : Fin n_fine → ℕ := fun j => N (shift j)
  let C_between' : Fin n_fine → ℝ := fun j => C_between (shift j)
  let G' : Finset (Fin n_fine) := Finset.univ.filter (fun j => (scaleClass' j).isGood)
  let B' : Finset (Fin n_fine) := Finset.univ.filter (fun j => (scaleClass' j).isBad)
  let Pb : ℝ := (∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η) *
      (∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc)
  have hPb_pos : 0 < Pb := by
    dsimp only [Pb]
    apply mul_pos <;> apply Finset.prod_pos <;> intro j _
    · have h1 : 0 < Δ' j.castSucc := by exact div_pos (hcfg.hΔ_pos _) (hcfg.hΔ_pos 1)
      have h2 : 0 < Δ' (Fin.succ j) := by exact div_pos (hcfg.hΔ_pos _) (hcfg.hΔ_pos 1)
      exact Real.rpow_pos_of_pos (div_pos h1 h2) _
    · exact div_pos (by exact div_pos (hcfg.hΔ_pos _) (hcfg.hΔ_pos 1)) (by exact div_pos (hcfg.hΔ_pos _) (hcfg.hΔ_pos 1))
  have hG0' : G0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood) := hG0
  have hB0' : B0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad) := hB0
  have hG'_def : G' = (Finset.univ : Finset (Fin n_fine)).filter (fun j => (scaleClass (Fin.succ j)).isGood) := by
    ext j; simp [G', scaleClass'] <;> rfl
  have hB'_def : B' = (Finset.univ : Finset (Fin n_fine)).filter (fun j => (scaleClass (Fin.succ j)).isBad) := by
    ext j; simp [B', scaleClass'] <;> rfl
  have hΔ'_def : ∀ i, Δ' i = Δ (Fin.succ i) / Δ 1 := by
    intro i; rfl
  have h_prod_good : (∏ j ∈ (Finset.univ : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood),
        Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) =
      (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
      (∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η) :=
    good_product_splitting Δ scaleClass hcfg.hΔ_pos j0 hj0 G0 Δ' G' hG0' hG'_def hΔ'_def
  have h_prod_bad : (∏ j ∈ (Finset.univ : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad),
        Δ (Fin.succ j) / Δ j.castSucc) =
      (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc) *
      (∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc) :=
    bad_product_splitting Δ scaleClass hcfg.hΔ_pos j0 hj0 B0 Δ' B' hB0' hB'_def hΔ'_def
  have h_product : combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass =
      Real.rpow (Real.log (1 / dyadicDelta k)) (-C) * (M : ℝ) *
      Real.rpow (dyadicDelta k) (C' * lam) * Real.rpow (dyadicDelta k) (-s + ε_N) * (PΔ * Pb) := by
    simp only [combiningLowerBound, Pb]
    rw [h_prod_good, h_prod_bad, hPΔ_def] <;> ring
  exact ⟨Δ', scaleClass', N', C_between', G', B', Pb,
    hΔ'_def,
    (fun j => by simp [scaleClass', shift] <;> rfl),
    (fun j => by simp [N', shift] <;> rfl),
    (fun j => by simp [C_between', shift] <;> rfl),
    hG'_def, hB'_def, rfl, hPb_pos, h_prod_good, h_prod_bad, h_product⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
