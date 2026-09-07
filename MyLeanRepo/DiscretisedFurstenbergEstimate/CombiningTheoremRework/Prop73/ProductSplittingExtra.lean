module

/-
  Product Splitting Extra — Additional extracted lemmas from InductiveStepCore_v2.

  Extracts the good/bad product splitting and Pb positivity
  from the main inductive proof to reduce proof size and compilation time.

  Whiteprint node: combining_theorem_genuine / inductive_step_core_v2
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.ProductSplitting
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Local helper: (a/c) / (b/c) = a/b for positive b, c. -/
lemma div_div_cancel' {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    (a / c) / (b / c) = a / b := by
  have hc' : c ≠ 0 := hc.ne'
  have hb' : b ≠ 0 := hb.ne'
  field_simp [hc', hb']

/-- Good product splitting: full good product = G0 product * G' product. -/
lemma good_product_splitting
    {n_fine : ℕ} {η : ℝ}
    (Δ : Fin (n_fine + 2) → ℝ)
    (scaleClass : Fin (n_fine + 1) → ScaleClass)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (j0 : Fin (n_fine + 1))
    (hj0 : j0.val = 0)
    (G0 : Finset (Fin (n_fine + 1)))
    (Δ' : Fin (n_fine + 1) → ℝ)
    (G' : Finset (Fin n_fine))
    (hG0 : G0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood))
    (hG' : G' = (Finset.univ : Finset (Fin n_fine)).filter (fun j => (scaleClass (Fin.succ j)).isGood))
    (hΔ'_def : ∀ i, Δ' i = Δ (Fin.succ i) / Δ 1) :
    (∏ j ∈ (Finset.univ : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood),
        Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) =
    (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
    (∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η) := by
  let shift : Fin n_fine → Fin (n_fine + 1) := Fin.succ
  have h_split := finset_product_split_first j0 hj0
    (fun j => (scaleClass j).isGood)
    (fun j => Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η)
  have h_filter_eq : (Finset.univ : Finset (Fin n_fine)).filter (fun i => (scaleClass (shift i)).isGood) = G' := by
    ext x
    simp [hG', shift]
  have h_tail : ∏ i ∈ (Finset.univ : Finset (Fin n_fine)).filter (fun i => (scaleClass (shift i)).isGood),
      Real.rpow (Δ (shift i).castSucc / Δ (Fin.succ (shift i))) η =
      ∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η := by
    rw [h_filter_eq]
    apply Finset.prod_congr rfl
    intro j _
    have h_pos1 : 0 < Δ 1 := hΔ_pos 1
    have h_pos2 : 0 < Δ (Fin.succ (shift j)) := hΔ_pos _
    have h_ratio : Δ (shift j).castSucc / Δ (Fin.succ (shift j)) =
        Δ' j.castSucc / Δ' (Fin.succ j) := by
      have h_eq : Δ (shift j).castSucc / Δ (Fin.succ (shift j)) =
          (Δ (shift j).castSucc / Δ 1) / (Δ (Fin.succ (shift j)) / Δ 1) :=
        (div_div_cancel' h_pos2 h_pos1).symm
      have h1 : Δ' j.castSucc = Δ (shift j).castSucc / Δ 1 := by
        rw [hΔ'_def] <;> congr 1
      have h2 : Δ' (Fin.succ j) = Δ (Fin.succ (shift j)) / Δ 1 := by
        rw [hΔ'_def]
      rw [h_eq, h1, h2]
    rw [h_ratio]
  have h_first : (∏ j ∈ (Finset.univ : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood),
        Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) =
      (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
      (∏ i ∈ (Finset.univ : Finset (Fin n_fine)).filter (fun i => (scaleClass (shift i)).isGood),
        Real.rpow (Δ (shift i).castSucc / Δ (Fin.succ (shift i))) η) := by
    rw [h_split, hG0]
  calc _
    = (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
      (∏ i ∈ (Finset.univ : Finset (Fin n_fine)).filter (fun i => (scaleClass (shift i)).isGood),
        Real.rpow (Δ (shift i).castSucc / Δ (Fin.succ (shift i))) η) := h_first
  _ = (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
      (∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η) := by
    rw [h_tail]

/-- Bad product splitting: full bad product = B0 product * B' product. -/
lemma bad_product_splitting
    {n_fine : ℕ}
    (Δ : Fin (n_fine + 2) → ℝ)
    (scaleClass : Fin (n_fine + 1) → ScaleClass)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (j0 : Fin (n_fine + 1))
    (hj0 : j0.val = 0)
    (B0 : Finset (Fin (n_fine + 1)))
    (Δ' : Fin (n_fine + 1) → ℝ)
    (B' : Finset (Fin n_fine))
    (hB0 : B0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad))
    (hB' : B' = (Finset.univ : Finset (Fin n_fine)).filter (fun j => (scaleClass (Fin.succ j)).isBad))
    (hΔ'_def : ∀ i, Δ' i = Δ (Fin.succ i) / Δ 1) :
    (∏ j ∈ (Finset.univ : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad),
        Δ (Fin.succ j) / Δ j.castSucc) =
    (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc) *
    (∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc) := by
  let shift : Fin n_fine → Fin (n_fine + 1) := Fin.succ
  have h_split := finset_product_split_first j0 hj0
    (fun j => (scaleClass j).isBad)
    (fun j => Δ (Fin.succ j) / Δ j.castSucc)
  have h_filter_eq : (Finset.univ : Finset (Fin n_fine)).filter (fun i => (scaleClass (shift i)).isBad) = B' := by
    ext x
    simp [hB', shift]
  have h_tail : ∏ i ∈ (Finset.univ : Finset (Fin n_fine)).filter (fun i => (scaleClass (shift i)).isBad),
      Δ (Fin.succ (shift i)) / Δ (shift i).castSucc =
      ∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc := by
    rw [h_filter_eq]
    apply Finset.prod_congr rfl
    intro j _
    have h_pos1 : 0 < Δ 1 := hΔ_pos 1
    have h_pos2 : 0 < Δ (shift j).castSucc := hΔ_pos _
    have h_ratio : Δ (Fin.succ (shift j)) / Δ (shift j).castSucc =
        Δ' (Fin.succ j) / Δ' j.castSucc := by
      have h_eq : Δ (Fin.succ (shift j)) / Δ (shift j).castSucc =
          (Δ (Fin.succ (shift j)) / Δ 1) / (Δ (shift j).castSucc / Δ 1) :=
        (div_div_cancel' h_pos2 h_pos1).symm
      have h1 : Δ' (Fin.succ j) = Δ (Fin.succ (shift j)) / Δ 1 := by
        rw [hΔ'_def]
      have h2 : Δ' j.castSucc = Δ (shift j).castSucc / Δ 1 := by
        rw [hΔ'_def] <;> congr 1
      rw [h_eq, h1, h2]
    rw [h_ratio]
  have h_first : (∏ j ∈ (Finset.univ : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad),
        Δ (Fin.succ j) / Δ j.castSucc) =
      (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc) *
      (∏ i ∈ (Finset.univ : Finset (Fin n_fine)).filter (fun i => (scaleClass (shift i)).isBad),
        Δ (Fin.succ (shift i)) / Δ (shift i).castSucc) := by
    rw [h_split, hB0]
  calc _
    = (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc) *
      (∏ i ∈ (Finset.univ : Finset (Fin n_fine)).filter (fun i => (scaleClass (shift i)).isBad),
        Δ (Fin.succ (shift i)) / Δ (shift i).castSucc) := h_first
  _ = (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc) *
      (∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc) := by
    rw [h_tail]

/-- Positivity of Pb (tail product of good rpow factors and bad ratios). -/
lemma Pb_positivity
    {n_fine : ℕ} {η : ℝ}
    (Δ' : Fin (n_fine + 1) → ℝ)
    (G' B' : Finset (Fin n_fine))
    (hΔ'_pos : ∀ i, 0 < Δ' i)
    (Pb : ℝ)
    (hPb_def : Pb = (∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η) *
        (∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc)) :
    0 < Pb := by
  rw [hPb_def]
  apply mul_pos
  · apply Finset.prod_pos
    intro j _
    have h1 : 0 < Δ' j.castSucc := hΔ'_pos _
    have h2 : 0 < Δ' (Fin.succ j) := hΔ'_pos _
    exact Real.rpow_pos_of_pos (div_pos h1 h2) _
  · apply Finset.prod_pos
    intro j _
    have h1 : 0 < Δ' (Fin.succ j) := hΔ'_pos _
    have h2 : 0 < Δ' j.castSucc := hΔ'_pos _
    exact div_pos h1 h2

end Prop73Restructure

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
