import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import MyLeanRepo.Kakeya.Assouad.WZ1.FineMultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.RestoreExtremality
import MyLeanRepo.Kakeya.Assouad.WZ1.ParameterAndExtremal
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.WZ1.CardinalityBound
import Mathlib.Tactic

/-!
# Clean proof of WZ1 Proposition 5 Fiber Refinement

Components:
1. Parent balancing
2. Union of per-parent source shadings (def + 3 lemmas)
3. Log-polynomial conversion for cardinality bound
4. Main theorem assembly
-/

noncomputable section

open MeasureTheory Metric Set Finset

namespace Kakeya.Assouad

/-! ### Helper lemmas -/

/-- `a ≤ b + c` implies `a - c ≤ b` in ENNReal. -/
private lemma ennreal_sub_le_of_le_add {a b c : ENNReal} (h : a ≤ b + c) : a - c ≤ b :=
  (OrderedSub.tsub_le_iff_right a c b).mpr h

/-- `a ≥ b + c` implies `a - c ≥ b` in ENNReal, when `c ≠ ⊤`. -/
private lemma ennreal_sub_ge_of_ge_add {a b c : ENNReal} (hc : c ≠ ⊤) (h : b + c ≤ a) : b ≤ a - c := by
  have h1 : a ≤ (a - c) + c := le_tsub_add
  have h2 : b + c ≤ (a - c) + c := h.trans h1
  have h3 : b ≤ a - c := by
    rwa [ENNReal.add_le_add_iff_right hc] at h2
  exact h3

/-! ### Arithmetic helper lemmas -/

/-- For `a < 0` and `C > 1`, there exists `0 < δ₀ ≤ 1` such that
`δ^a ≥ C` for all `0 < δ ≤ δ₀`. -/
private lemma exists_rpow_ge (a C : ℝ) (ha : a < 0) (hC : 1 < C) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ → Real.rpow δ a ≥ C := by
  let b : ℝ := -a
  have hb_pos : 0 < b := by linarith
  have hC_pos : 0 < C := by linarith
  let δ₀ : ℝ := C ^ (-1 / b)
  have hδ₀_pos : 0 < δ₀ := Real.rpow_pos_of_pos hC_pos _
  have h_pos_inv : 0 < 1 / b := by positivity
  have h2 : 1 < C ^ (1 / b) := Real.one_lt_rpow hC h_pos_inv
  have h3 : C ^ (-1 / b) = (C ^ (1 / b))⁻¹ := by
    have h_neg_eq : -1 / b = -(1 / b) := by ring
    rw [h_neg_eq]
    exact Real.rpow_neg hC_pos.le (1 / b)
  have hδ₀_lt_one : δ₀ < 1 := by
    dsimp only [δ₀]
    rw [h3]
    have h_pos2 : 0 < C ^ (1 / b) := Real.rpow_pos_of_pos hC_pos _
    have h4 : (C ^ (1 / b))⁻¹ < 1 := by
      have h5 : 1 ≤ C ^ (1 / b) := h2.le
      have h6 : (C ^ (1 / b))⁻¹ ≠ 1 := by
        intro h7
        have h8 : C ^ (1 / b) = 1 := by
          field_simp [h_pos2.ne'] at h7 <;> linarith
        linarith [h2]
      exact lt_of_le_of_ne (inv_le_one_of_one_le₀ h5) h6
    exact h4
  have hδ₀_le_one : δ₀ ≤ 1 := hδ₀_lt_one.le
  have h4 : Real.rpow δ₀ b = C⁻¹ := by
    have h51 : δ₀ = C ^ (-1 / b) := by rfl
    rw [h51]
    have h52 : Real.rpow (C ^ (-1 / b)) b = C ^ ((-1 / b) * b) :=
      (Real.rpow_mul hC_pos.le (-1 / b) b).symm
    rw [h52]
    have h53 : (-1 / b) * b = -1 := by
      field_simp [hb_pos.ne'] <;> ring
    rw [h53]
    have h54 : C ^ (-1 : ℝ) = C⁻¹ := by
      have h55 : C ^ (-1 : ℝ) = (C ^ (1 : ℝ))⁻¹ := Real.rpow_neg hC_pos.le 1
      rw [h55]
      have h56 : C ^ (1 : ℝ) = C := by simp
      rw [h56] <;> ring
    rw [h54]
  refine' ⟨δ₀, hδ₀_pos, hδ₀_le_one, _⟩
  intro δ hδ_pos hδ_le
  have h5 : Real.rpow δ b ≤ Real.rpow δ₀ b :=
    Real.rpow_le_rpow hδ_pos.le hδ_le hb_pos.le
  have h6 : Real.rpow δ b ≤ C⁻¹ := by
    rw [h4] at h5; exact h5
  have h7 : 0 < Real.rpow δ b := Real.rpow_pos_of_pos hδ_pos b
  have h8 : (Real.rpow δ b)⁻¹ ≥ C := by
    have h9 : (Real.rpow δ b)⁻¹ ≥ (C⁻¹)⁻¹ := by gcongr
    have h10 : (C⁻¹)⁻¹ = C := by simp
    rw [h10] at h9; exact h9
  have h11 : a = -b := by linarith
  have h12 : Real.rpow δ a = (Real.rpow δ b)⁻¹ := by
    rw [h11]; exact Real.rpow_neg hδ_pos.le b
  rw [h12]; exact h8

/-- For `0 < eta < inputLoss`, there exists `delta₀` such that for
`0 < delta ≤ delta₀`, `δ^inputLoss ≤ (1/2) * δ^eta` in ENNReal. -/
private lemma mass_absorption {eta inputLoss : ℝ}
    (heta : 0 < eta) (h : eta < inputLoss) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
        Kakeya.realRpowENN delta inputLoss ≤
          (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta := by
  have h1 : inputLoss - eta > 0 := by linarith
  have h2 : eta - inputLoss < 0 := by linarith
  rcases exists_rpow_ge (eta - inputLoss) 2 h2 (by norm_num) with
    ⟨δ₀, hδ₀_pos, hδ₀_le_one, hbound⟩
  have h_main : ∀ (delta : ℝ), 0 < delta → delta ≤ δ₀ →
      Kakeya.realRpowENN delta inputLoss ≤
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta := by
    intro delta hdelta_pos hdelta_le
    have h_ge2 : Real.rpow delta (eta - inputLoss) ≥ 2 := hbound delta hdelta_pos hdelta_le
    have h_pos_eta : 0 < Real.rpow delta eta := Real.rpow_pos_of_pos hdelta_pos _
    have h_pos_in : 0 < Real.rpow delta inputLoss := Real.rpow_pos_of_pos hdelta_pos _
    have h_add : (eta - inputLoss) + inputLoss = eta := by ring
    have h_rpow : Real.rpow delta ((eta - inputLoss) + inputLoss) =
        Real.rpow delta (eta - inputLoss) * Real.rpow delta inputLoss :=
      Real.rpow_add hdelta_pos (eta - inputLoss) inputLoss
    have h_eq : Real.rpow delta eta = Real.rpow delta (eta - inputLoss) * Real.rpow delta inputLoss := by
      rw [h_add] at h_rpow; exact h_rpow
    have h_real : Real.rpow delta inputLoss ≤ (1 / 2 : ℝ) * Real.rpow delta eta := by
      rw [h_eq]
      have h : (1 / 2 : ℝ) * (Real.rpow delta (eta - inputLoss) * Real.rpow delta inputLoss) ≥
          Real.rpow delta inputLoss := by
        have h' : Real.rpow delta (eta - inputLoss) ≥ 2 := h_ge2
        have h'' : 0 ≤ Real.rpow delta inputLoss := by positivity
        calc
          (1 / 2 : ℝ) * (Real.rpow delta (eta - inputLoss) * Real.rpow delta inputLoss)
            ≥ (1 / 2 : ℝ) * (2 * Real.rpow delta inputLoss) := by gcongr
          _ = Real.rpow delta inputLoss := by ring
      exact h
    have h_enn : ENNReal.ofReal (Real.rpow delta inputLoss) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta eta) := ENNReal.ofReal_mono h_real
    have h_mul : ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta eta) =
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta := by
      have h_nonneg : 0 ≤ Real.rpow delta eta := by positivity
      simp [Kakeya.realRpowENN, ENNReal.ofReal_mul, h_nonneg] <;> norm_cast
    rw [h_mul] at h_enn
    exact h_enn
  exact ⟨δ₀, hδ₀_pos, hδ₀_le_one, h_main⟩

/-- For `c > 0` and `a < b`, there exists `delta₀` such that for
`0 < delta ≤ delta₀`, `δ^b ≤ c * δ^a` in ENNReal. -/
private lemma constant_absorption {a b c : ℝ}
    (hc : 0 < c) (h : a < b) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
        Kakeya.realRpowENN delta b ≤
          ENNReal.ofReal c * Kakeya.realRpowENN delta a := by
  by_cases hc1 : c ≥ 1
  · have h_main : ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        Kakeya.realRpowENN delta b ≤ ENNReal.ofReal c * Kakeya.realRpowENN delta a := by
      intro delta hdelta_pos hdelta_le
      have h1 : Kakeya.realRpowENN delta b ≤ Kakeya.realRpowENN delta a := by
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le h.le
      have h3 : (1 : ENNReal) ≤ ENNReal.ofReal c := by
        simpa [ENNReal.ofReal_le_ofReal_iff] using hc1
      have h4 : Kakeya.realRpowENN delta a ≤ ENNReal.ofReal c * Kakeya.realRpowENN delta a := by
        calc Kakeya.realRpowENN delta a
          = (1 : ENNReal) * Kakeya.realRpowENN delta a := by rw [one_mul]
        _ ≤ ENNReal.ofReal c * Kakeya.realRpowENN delta a := by gcongr
      exact h1.trans h4
    exact ⟨1, by norm_num, by norm_num, h_main⟩
  · have hc_lt_one : c < 1 := by by_contra h'; exact hc1 (by linarith)
    have hc' : 1 < 1 / c := by apply one_lt_one_div hc; exact hc_lt_one
    have h1 : a - b < 0 := by linarith
    rcases exists_rpow_ge (a - b) (1 / c) h1 hc' with
      ⟨δ₀, hδ₀_pos, hδ₀_le_one, hbound⟩
    have h_main : ∀ (delta : ℝ), 0 < delta → delta ≤ δ₀ →
        Kakeya.realRpowENN delta b ≤ ENNReal.ofReal c * Kakeya.realRpowENN delta a := by
      intro delta hdelta_pos hdelta_le
      have h2 : Real.rpow delta (a - b) ≥ 1 / c := hbound delta hdelta_pos hdelta_le
      have h_pos_a : 0 < Real.rpow delta a := Real.rpow_pos_of_pos hdelta_pos _
      have h_pos_b : 0 < Real.rpow delta b := Real.rpow_pos_of_pos hdelta_pos _
      have h_add : (a - b) + b = a := by ring
      have h_rpow : Real.rpow delta ((a - b) + b) =
          Real.rpow delta (a - b) * Real.rpow delta b :=
        Real.rpow_add hdelta_pos (a - b) b
      have h_eq : Real.rpow delta a = Real.rpow delta (a - b) * Real.rpow delta b := by
        rw [h_add] at h_rpow; exact h_rpow
      have h_real : Real.rpow delta b ≤ c * Real.rpow delta a := by
        rw [h_eq]
        have h : c * (Real.rpow delta (a - b) * Real.rpow delta b) ≥ Real.rpow delta b := by
          have h' : Real.rpow delta (a - b) ≥ 1 / c := h2
          have h'' : 0 ≤ Real.rpow delta b := by positivity
          have h3 : c * Real.rpow delta (a - b) ≥ 1 := by
            calc c * Real.rpow delta (a - b) ≥ c * (1 / c) := by gcongr
            _ = 1 := by field_simp [hc.ne'] <;> ring
          nlinarith
        exact h
      have h_enn : ENNReal.ofReal (Real.rpow delta b) ≤
          ENNReal.ofReal (c * Real.rpow delta a) := ENNReal.ofReal_mono h_real
      have h_mul : ENNReal.ofReal (c * Real.rpow delta a) =
          ENNReal.ofReal c * Kakeya.realRpowENN delta a := by
        have h_nonneg : 0 ≤ Real.rpow delta a := by positivity
        simp [Kakeya.realRpowENN, ENNReal.ofReal_mul, hc.le, h_nonneg] <;> rfl
      rw [h_mul] at h_enn
      exact h_enn
    exact ⟨δ₀, hδ₀_pos, hδ₀_le_one, h_main⟩

/-! ### Parent balancing -/

lemma parent_balancing
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {inputLoss : ℝ} :
    ∃ (retained : Finset (Fin (U.coarse rho).card)),
      (∀ j ∈ retained,
        (U.cover rho).toFactoring.fiberShadedMass Y j ≥
          Kakeya.realRpowENN delta inputLoss *
          (U.cover rho).toFactoring.fiberMass j) ∧
      (∑ j ∈ retained, (U.cover rho).toFactoring.fiberShadedMass Y j ≥
        Y.mass - Kakeya.realRpowENN delta inputLoss * F.toBodyFamily.mass) := by
  let G := U.coarse rho
  let Pcover := U.cover rho
  let threshold := Kakeya.realRpowENN delta inputLoss
  let retained : Finset (Fin G.card) :=
    Finset.univ.filter (fun j => threshold * Pcover.toFactoring.fiberMass j ≤ Pcover.toFactoring.fiberShadedMass Y j)
  let bad := Finset.univ \ retained

  have h_retained_prop : ∀ j ∈ retained, threshold * Pcover.toFactoring.fiberMass j ≤ Pcover.toFactoring.fiberShadedMass Y j := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2

  have h_bad_le : ∀ j ∈ bad, Pcover.toFactoring.fiberShadedMass Y j ≤ threshold * Pcover.toFactoring.fiberMass j := by
    intro j hj
    have h_j_not_retained : j ∉ retained := (Finset.mem_sdiff.mp hj).2
    have h : ¬(threshold * Pcover.toFactoring.fiberMass j ≤ Pcover.toFactoring.fiberShadedMass Y j) := by
      simpa [retained, Finset.mem_filter, Finset.mem_univ j] using h_j_not_retained
    exact (lt_of_not_ge h).le

  have h_disj : ∀ (j1 j2 : Fin G.card), j1 ≠ j2 →
      Disjoint (Pcover.toFactoring.fiberIndices j1) (Pcover.toFactoring.fiberIndices j2) := by
    intro j1 j2 hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : Pcover.toFactoring.parent i = j1 := (Finset.mem_filter.mp hi1).2
    have h2 : Pcover.toFactoring.parent i = j2 := (Finset.mem_filter.mp hi2).2
    have h3 : j1 = j2 := by rw [←h1, h2]
    exact hne h3

  have h_disj' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin G.card)))
      (fun j : Fin G.card => Pcover.toFactoring.fiberIndices j) := by
    intro j1 _ j2 _ hne
    exact h_disj j1 j2 hne

  have h_union : Finset.biUnion (Finset.univ : Finset (Fin G.card))
      (fun j => Pcover.toFactoring.fiberIndices j) = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro _; trivial
    · intro _
      exact ⟨Pcover.toFactoring.parent i, by
        simp only [Kakeya.Streamlined.Factoring.fiberIndices, Finset.mem_filter, Finset.mem_univ, true_and]⟩

  have h_sum_shaded : ∑ j : Fin G.card, Pcover.toFactoring.fiberShadedMass Y j = Y.mass := by
    have h8 : ∑ j : Fin G.card, Pcover.toFactoring.fiberShadedMass Y j =
        ∑ i ∈ (Finset.biUnion (Finset.univ : Finset (Fin G.card))
          (fun j => Pcover.toFactoring.fiberIndices j)), volume (Y.carrier i) := by
      rw [Finset.sum_biUnion h_disj'] <;> rfl
    rw [h8, h_union] <;> rfl

  have h_sum_mass : ∑ j : Fin G.card, Pcover.toFactoring.fiberMass j = F.toBodyFamily.mass := by
    have h8 : ∑ j : Fin G.card, Pcover.toFactoring.fiberMass j =
        ∑ i ∈ (Finset.biUnion (Finset.univ : Finset (Fin G.card))
          (fun j => Pcover.toFactoring.fiberIndices j)), (F.toBodyFamily.body i).volume := by
      rw [Finset.sum_biUnion h_disj'] <;> rfl
    rw [h8, h_union] <;> rfl

  have h_bad_sum : ∑ j ∈ bad, Pcover.toFactoring.fiberShadedMass Y j ≤ threshold * F.toBodyFamily.mass := by
    calc
      ∑ j ∈ bad, Pcover.toFactoring.fiberShadedMass Y j
        ≤ ∑ j ∈ bad, (threshold * Pcover.toFactoring.fiberMass j) := Finset.sum_le_sum h_bad_le
      _ = threshold * ∑ j ∈ bad, Pcover.toFactoring.fiberMass j := by rw [Finset.mul_sum]
      _ ≤ threshold * ∑ j : Fin G.card, Pcover.toFactoring.fiberMass j := by gcongr <;> simp [bad]
      _ = threshold * F.toBodyFamily.mass := by rw [h_sum_mass]

  have h_disj_rb : Disjoint retained bad := by
    simp [retained, bad, Finset.disjoint_left] <;> tauto
  have h_union_rb : retained ∪ bad = Finset.univ := by
    ext j; simp [retained, bad] <;> tauto
  have h_total : ∑ j ∈ retained, Pcover.toFactoring.fiberShadedMass Y j + ∑ j ∈ bad, Pcover.toFactoring.fiberShadedMass Y j = Y.mass := by
    have h_sum : ∑ j ∈ (retained ∪ bad), Pcover.toFactoring.fiberShadedMass Y j =
        ∑ j ∈ retained, Pcover.toFactoring.fiberShadedMass Y j + ∑ j ∈ bad, Pcover.toFactoring.fiberShadedMass Y j :=
      Finset.sum_union h_disj_rb
    have h_eq : ∑ j ∈ (retained ∪ bad), Pcover.toFactoring.fiberShadedMass Y j = ∑ j : Fin G.card, Pcover.toFactoring.fiberShadedMass Y j := by
      have h_u : retained ∪ bad = (Finset.univ : Finset (Fin G.card)) := h_union_rb
      rw [h_u] <;> rfl
    rw [←h_sum, h_eq, h_sum_shaded]

  have h3 : Y.mass ≤ ∑ j ∈ retained, Pcover.toFactoring.fiberShadedMass Y j + threshold * F.toBodyFamily.mass := by
    calc
      Y.mass = ∑ j ∈ retained, Pcover.toFactoring.fiberShadedMass Y j + ∑ j ∈ bad, Pcover.toFactoring.fiberShadedMass Y j := h_total.symm
      _ ≤ ∑ j ∈ retained, Pcover.toFactoring.fiberShadedMass Y j + threshold * F.toBodyFamily.mass := by gcongr <;> exact h_bad_sum

  have h_main : ∑ j ∈ retained, Pcover.toFactoring.fiberShadedMass Y j ≥
      Y.mass - threshold * F.toBodyFamily.mass :=
    ennreal_sub_le_of_le_add h3

  exact ⟨retained, h_retained_prop, h_main⟩

/-! ### Union of per-parent source shadings -/

def unionParentShadings
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (retained : Finset (Fin (U.coarse rho).card))
    (S : Fin (U.coarse rho).card → Kakeya.Streamlined.TubeShading F) :
    Kakeya.Streamlined.TubeShading F :=
  let Pcover := U.cover rho
  {
    carrier := fun i =>
      if Pcover.toFactoring.parent i ∈ retained
      then (S (Pcover.toFactoring.parent i)).carrier i
      else ∅
    measurable_carrier := by
      intro i
      by_cases h : Pcover.toFactoring.parent i ∈ retained
      · simp [h, (S (Pcover.toFactoring.parent i)).measurable_carrier i]
      · simp [h]
    subset_body := by
      intro i
      by_cases h : Pcover.toFactoring.parent i ∈ retained
      · simp [h]
        exact (S (Pcover.toFactoring.parent i)).subset_body i
      · simp [h]
  }

lemma unionParentShadings_carrier_of_mem
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {retained : Finset (Fin (U.coarse rho).card)}
    {S : Fin (U.coarse rho).card → Kakeya.Streamlined.TubeShading F}
    {i : Fin F.card} (h : (U.cover rho).toFactoring.parent i ∈ retained) :
    (unionParentShadings retained S).carrier i =
    (S ((U.cover rho).toFactoring.parent i)).carrier i := by
  simp [unionParentShadings, h]

lemma unionParentShadings_carrier_of_not_mem
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {retained : Finset (Fin (U.coarse rho).card)}
    {S : Fin (U.coarse rho).card → Kakeya.Streamlined.TubeShading F}
    {i : Fin F.card} (h : (U.cover rho).toFactoring.parent i ∉ retained) :
    (unionParentShadings retained S).carrier i = ∅ := by
  simp [unionParentShadings, h]

lemma unionParentShadings_subshading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {retained : Finset (Fin (U.coarse rho).card)}
    {S : Fin (U.coarse rho).card → Kakeya.Streamlined.TubeShading F}
    (h_sub : ∀ j ∈ retained, IsSubshading (S j) Y)
    (h_supported : ∀ j ∈ retained, ∀ i,
      (S j).carrier i ≠ ∅ → (U.cover rho).toFactoring.parent i = j) :
    IsSubshading (unionParentShadings retained S) Y := by
  let Pcover := U.cover rho
  let Z := unionParentShadings retained S
  intro i
  dsimp only [Z, unionParentShadings]
  by_cases h : Pcover.toFactoring.parent i ∈ retained
  · rw [if_pos h]
    exact h_sub (Pcover.toFactoring.parent i) h i
  · rw [if_neg h] <;> simp

lemma unionParentShadings_mass
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {retained : Finset (Fin (U.coarse rho).card)}
    {S : Fin (U.coarse rho).card → Kakeya.Streamlined.TubeShading F}
    (h_sub : ∀ j ∈ retained, IsSubshading (S j) Y)
    (h_supported : ∀ j ∈ retained, ∀ i,
      (S j).carrier i ≠ ∅ → (U.cover rho).toFactoring.parent i = j) :
    (unionParentShadings retained S).mass = ∑ j ∈ retained, (S j).mass := by
  let G := U.coarse rho
  let Pcover := U.cover rho
  let Z := unionParentShadings retained S

  have h_disj : ∀ (j1 j2 : Fin G.card), j1 ≠ j2 →
      Disjoint (Pcover.toFactoring.fiberIndices j1) (Pcover.toFactoring.fiberIndices j2) := by
    intro j1 j2 hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : Pcover.toFactoring.parent i = j1 := (Finset.mem_filter.mp hi1).2
    have h2 : Pcover.toFactoring.parent i = j2 := (Finset.mem_filter.mp hi2).2
    have h3 : j1 = j2 := by rw [←h1, h2]
    exact hne h3

  have h_disj' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin G.card)))
      (fun j : Fin G.card => Pcover.toFactoring.fiberIndices j) := by
    intro j1 _ j2 _ hne
    exact h_disj j1 j2 hne

  have h_union : Finset.biUnion (Finset.univ : Finset (Fin G.card))
      (fun j => Pcover.toFactoring.fiberIndices j) = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro _; trivial
    · intro _
      exact ⟨Pcover.toFactoring.parent i, by
        simp only [Kakeya.Streamlined.Factoring.fiberIndices, Finset.mem_filter, Finset.mem_univ, true_and]⟩

  have h_supported_mass : ∀ j ∈ retained,
      (S j).mass = ∑ i ∈ Pcover.toFactoring.fiberIndices j, volume ((S j).carrier i) := by
    intro j hj
    have h1 : (S j).mass = ∑ i, volume ((S j).carrier i) := rfl
    rw [h1]
    have h_zero : ∀ (i : Fin F.card), i ∉ Pcover.toFactoring.fiberIndices j → volume ((S j).carrier i) = 0 := by
      intro i hni
      have h_parent_ne : Pcover.toFactoring.parent i ≠ j := by
        intro h
        have h2 : i ∈ Pcover.toFactoring.fiberIndices j := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ i, h⟩
        exact hni h2
      have h_empty : (S j).carrier i = ∅ := by
        by_contra hne
        exact h_parent_ne (h_supported j hj i hne)
      rw [h_empty] <;> simp
    have h_eq : ∑ i ∈ Pcover.toFactoring.fiberIndices j, volume ((S j).carrier i) = ∑ i, volume ((S j).carrier i) :=
      Finset.sum_subset (Pcover.toFactoring.fiberIndices j).subset_univ (fun i _ hni => h_zero i hni)
    exact h_eq.symm

  have h_disj_retained : Set.PairwiseDisjoint (retained : Set (Fin G.card))
      (fun j => Pcover.toFactoring.fiberIndices j) := by
    intro j1 _ j2 _ hne
    exact h_disj j1 j2 hne

  have h4 : ∀ i, i ∉ Finset.biUnion retained (fun j => Pcover.toFactoring.fiberIndices j) →
      volume (Z.carrier i) = 0 := by
    intro i hni
    have h5 : Pcover.toFactoring.parent i ∉ retained := by
      intro h
      have h6 : i ∈ Pcover.toFactoring.fiberIndices (Pcover.toFactoring.parent i) := by
        simp only [Kakeya.Streamlined.Factoring.fiberIndices, Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
      have h7 : i ∈ Finset.biUnion retained (fun j => Pcover.toFactoring.fiberIndices j) :=
        Finset.mem_biUnion.mpr ⟨Pcover.toFactoring.parent i, h, h6⟩
      exact hni h7
    have h8 : Z.carrier i = ∅ := by
      dsimp only [Z, unionParentShadings]
      rw [if_neg h5]
    rw [h8] <;> simp

  calc
    Z.mass
      = ∑ i, volume (Z.carrier i) := rfl
    _ = ∑ i ∈ Finset.biUnion retained (fun j => Pcover.toFactoring.fiberIndices j),
          volume (Z.carrier i) := by
      have h_eq : (∑ i, volume (Z.carrier i)) =
          ∑ i ∈ Finset.biUnion retained (fun j => Pcover.toFactoring.fiberIndices j), volume (Z.carrier i) := by
        apply (Finset.sum_subset (Finset.subset_univ _) _).symm
        intro i _ hni
        exact h4 i hni
      exact h_eq
    _ = ∑ j ∈ retained, ∑ i ∈ Pcover.toFactoring.fiberIndices j, volume (Z.carrier i) := by
      have h_sum : ∑ j ∈ retained, ∑ i ∈ Pcover.toFactoring.fiberIndices j, volume (Z.carrier i) =
          ∑ i ∈ Finset.biUnion retained (fun j => Pcover.toFactoring.fiberIndices j), volume (Z.carrier i) := by
        rw [Finset.sum_biUnion h_disj_retained]
      exact h_sum.symm
    _ = ∑ j ∈ retained, ∑ i ∈ Pcover.toFactoring.fiberIndices j, volume ((S j).carrier i) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        have h4 : Pcover.toFactoring.parent i = j := (Finset.mem_filter.mp hi).2
        have h5 : Pcover.toFactoring.parent i ∈ retained := by rw [h4] <;> exact hj
        have hP : Pcover = U.cover rho := rfl
        have h5' : (U.cover rho).toFactoring.parent i ∈ retained := by
          rw [←hP] <;> exact h5
        have h6 : Z.carrier i = (S ((U.cover rho).toFactoring.parent i)).carrier i :=
          unionParentShadings_carrier_of_mem h5'
        have h7 : Z.carrier i = (S j).carrier i := by
          rw [h6, h4]
        exact congr_arg volume h7
    _ = ∑ j ∈ retained, (S j).mass := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (h_supported_mass j hj).symm

lemma unionParentShadings_fiber_cap
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {retained : Finset (Fin (U.coarse rho).card)}
    {S : Fin (U.coarse rho).card → Kakeya.Streamlined.TubeShading F}
    (h_sub : ∀ j ∈ retained, IsSubshading (S j) Y)
    (h_supported : ∀ j ∈ retained, ∀ i,
      (S j).carrier i ≠ ∅ → (U.cover rho).toFactoring.parent i = j)
    {C : ENNReal}
    (h_cap : ∀ j ∈ retained, ∀ p,
      ((U.cover rho).toFactoring.fiberPointMultiplicity (S j) j p : ENNReal) ≤ C) :
    ∀ j p,
      ((U.cover rho).toFactoring.fiberPointMultiplicity
        (unionParentShadings retained S) j p : ENNReal) ≤ C := by
  let Pcover := U.cover rho
  let Z := unionParentShadings retained S
  classical
  intro j p
  by_cases hj : j ∈ retained
  · have h_filter_eq : (Pcover.toFactoring.fiberIndices j).filter (fun i => p ∈ Z.carrier i) =
        (Pcover.toFactoring.fiberIndices j).filter (fun i => p ∈ (S j).carrier i) := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter]
      constructor
      · intro ⟨hi, hmem⟩
        have h2 : Pcover.toFactoring.parent i = j := (Finset.mem_filter.mp hi).2
        have h3 : Pcover.toFactoring.parent i ∈ retained := by rw [h2] <;> exact hj
        have hP : Pcover = U.cover rho := rfl
        have h3' : (U.cover rho).toFactoring.parent i ∈ retained := by
          rw [←hP] <;> exact h3
        have h4 : Z.carrier i = (S ((U.cover rho).toFactoring.parent i)).carrier i :=
          unionParentShadings_carrier_of_mem h3'
        have h5 : Z.carrier i = (S j).carrier i := by
          rw [h4, h2]
        exact ⟨hi, h5 ▸ hmem⟩
      · intro ⟨hi, hmem⟩
        have h2 : Pcover.toFactoring.parent i = j := (Finset.mem_filter.mp hi).2
        have h3 : Pcover.toFactoring.parent i ∈ retained := by rw [h2] <;> exact hj
        have hP : Pcover = U.cover rho := rfl
        have h3' : (U.cover rho).toFactoring.parent i ∈ retained := by
          rw [←hP] <;> exact h3
        have h4 : Z.carrier i = (S ((U.cover rho).toFactoring.parent i)).carrier i :=
          unionParentShadings_carrier_of_mem h3'
        have h5 : Z.carrier i = (S j).carrier i := by
          rw [h4, h2]
        exact ⟨hi, h5.symm ▸ hmem⟩
    have h1 : Pcover.toFactoring.fiberPointMultiplicity Z j p =
        Pcover.toFactoring.fiberPointMultiplicity (S j) j p := by
      simp only [Kakeya.Streamlined.Factoring.fiberPointMultiplicity]
      rw [h_filter_eq]
    rw [h1]
    exact h_cap j hj p
  · have h1 : Pcover.toFactoring.fiberPointMultiplicity Z j p = 0 := by
      simp only [Kakeya.Streamlined.Factoring.fiberPointMultiplicity]
      have h2 : (Pcover.toFactoring.fiberIndices j).filter (fun i => p ∈ Z.carrier i) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i
        intro h3
        have h4 : i ∈ Pcover.toFactoring.fiberIndices j := (Finset.mem_filter.mp h3).1
        have h5 : Pcover.toFactoring.parent i = j := (Finset.mem_filter.mp h4).2
        have h6 : Pcover.toFactoring.parent i ∉ retained := by
          rw [h5] <;> exact hj
        have h7 : Z.carrier i = ∅ := by
          have hP : Pcover = U.cover rho := rfl
          have h6' : (U.cover rho).toFactoring.parent i ∉ retained := by
            rw [←hP] <;> exact h6
          exact unionParentShadings_carrier_of_not_mem h6'
        have h3' : p ∈ Z.carrier i := (Finset.mem_filter.mp h3).2
        rw [h7] at h3'
        simpa using h3'
      rw [h2] <;> simp
    rw [h1]
    simp

/-! ### Main theorem -/

theorem wz1_proposition5_fiber_refinement :
    WZ1Proposition5FiberRefinementStatement := by
  intro h_leaf
  intro sigma hsigma hsigma_one hCriticalFloor
  intro outputLoss massLoss scaleLoss
    houtputLoss_pos hmassLoss_pos hmassLoss_lt_output hscaleLoss_pos

  -- Step 1: Critical floor at outputLoss
  rcases hCriticalFloor outputLoss houtputLoss_pos with
    ⟨eta_floor, delta₀_floor, heta_floor_pos, hdelta₀_floor_pos, hdelta₀_floor_one, hFloor⟩

  -- Step 2: Choose epsilon_ref
  let epsilon_ref : ℝ := min massLoss eta_floor
  have hepsilon_ref_pos : 0 < epsilon_ref := by
    dsimp only [epsilon_ref]
    exact lt_min hmassLoss_pos heta_floor_pos
  have hepsilon_ref_le_mass : epsilon_ref ≤ massLoss := min_le_left _ _
  have hepsilon_ref_le_floor : epsilon_ref ≤ eta_floor := min_le_right _ _

  -- Step 3: Choose retentionLoss
  let retentionLoss : ℝ := epsilon_ref / 8
  have hretentionLoss_pos : 0 < retentionLoss := by positivity
  have hretentionLoss_lt_output : retentionLoss < outputLoss := by
    dsimp only [retentionLoss]
    have h : epsilon_ref ≤ massLoss := hepsilon_ref_le_mass
    linarith

  -- Step 4: Apply one-parent leaf
  rcases h_leaf sigma hsigma hsigma_one hCriticalFloor
      outputLoss retentionLoss scaleLoss
      houtputLoss_pos hretentionLoss_pos
      (by linarith) hscaleLoss_pos with
    ⟨inputLoss, delta₀_leaf, hinputLoss_pos, hinputLoss_lt_retention,
      hdelta₀_leaf_pos, hdelta₀_leaf_one, hLeafInner⟩

  -- Step 5: Choose eta < inputLoss
  let eta : ℝ := min (inputLoss / 2) (massLoss / 4)
  have heta_pos : 0 < eta := by
    dsimp only [eta]
    exact lt_min (by linarith) (by positivity)
  have heta_lt_inputLoss : eta < inputLoss := by
    dsimp only [eta]
    have h : min (inputLoss / 2) (massLoss / 4) ≤ inputLoss / 2 := min_le_left _ _
    linarith
  have heta_lt_massLoss : eta < massLoss := by
    dsimp only [eta]
    have h : min (inputLoss / 2) (massLoss / 4) ≤ massLoss / 4 := min_le_right _ _
    linarith

  -- Step 6: Choose eta_ref
  let eta_ref : ℝ := retentionLoss + eta + epsilon_ref / 8
  have heta_ref_pos : 0 < eta_ref := by positivity
  have heta_ref_gt_retention_plus_eta : retentionLoss + eta < eta_ref := by
    dsimp only [eta_ref] <;> linarith
  have h3eta_ref_lt_epsilon : 3 * eta_ref < epsilon_ref := by
    dsimp only [eta_ref, retentionLoss]
    have h1 : eta ≤ inputLoss / 2 := by
      dsimp only [eta]
      exact min_le_left _ _
    have h2 : inputLoss < epsilon_ref / 8 := by
      dsimp only [retentionLoss] at hinputLoss_lt_retention <;> linarith
    nlinarith
  have heta_le_eta_ref : eta ≤ eta_ref := by
    dsimp only [eta_ref] <;> linarith

  -- Step 7: Choose delta₀ small enough
  -- 7a: Mass absorption: δ^inputLoss ≤ (1/2) * δ^eta
  rcases mass_absorption heta_pos heta_lt_inputLoss with
    ⟨delta₀_abs1, hdelta₀_abs1_pos, hdelta₀_abs1_one, h_abs1⟩

  -- 7b: Constant absorption: δ^eta_ref ≤ (1/2) * δ^(retentionLoss + eta)
  rcases constant_absorption (show (0 : ℝ) < 1 / 2 by norm_num) heta_ref_gt_retention_plus_eta with
    ⟨delta₀_abs2, hdelta₀_abs2_pos, hdelta₀_abs2_one, h_abs2⟩

  -- 7c: Mass inequality: δ^(3*eta_ref - epsilon_ref) ≥ 4
  have h_gap_neg : 3 * eta_ref - epsilon_ref < 0 := by linarith
  rcases exists_rpow_ge (3 * eta_ref - epsilon_ref) 4 h_gap_neg (by norm_num) with
    ⟨delta₀_ineq, hdelta₀_ineq_pos, hdelta₀_ineq_one, h_ineq_bound⟩

  -- 7d: Log bound for cardinality: choose δ₀
  rcases log_bound_from_poly (show (1 : ℝ) ≤ (99 : ℝ)^6 by norm_num)
      (show (0 : ℝ) ≤ 6 + eta_ref by linarith)
      (show (0 : ℝ) < epsilon_ref - eta_ref by linarith) with
    ⟨delta₀_card, hdelta₀_card_pos, hdelta₀_card_one, h_log_bound_thresh⟩

  -- 7e: Smallness for cardinality bound
  let delta₀_small : ℝ := 1 / 17
  have hdelta₀_small_pos : 0 < delta₀_small := by norm_num
  have hdelta₀_small_one : delta₀_small ≤ 1 := by norm_num

  -- Build delta₀ as nested minimums with explicit intermediates
  let d1 := min delta₀_floor delta₀_leaf
  let d2 := min d1 delta₀_abs1
  let d3 := min d2 delta₀_abs2
  let d4 := min d3 delta₀_ineq
  let d5 := min d4 delta₀_card
  let delta₀ : ℝ := min d5 delta₀_small

  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_one : delta₀ ≤ 1 := by
    have h : delta₀ ≤ delta₀_small := min_le_right d5 delta₀_small
    exact h.trans hdelta₀_small_one

  refine' ⟨eta, delta₀, heta_pos, heta_lt_massLoss, hdelta₀_pos, hdelta₀_one, _⟩

  intro delta hdelta hdelta_le
  intro F U Y hExt rho hrho_lower hrho_upper

  have hdelta_one : delta ≤ 1 := le_trans hdelta_le hdelta₀_one

  -- Explicit delta₀ bound helpers
  have h_le_d5 : delta₀ ≤ d5 := min_le_left d5 delta₀_small
  have h_le_d4 : delta₀ ≤ d4 := h_le_d5.trans (min_le_left d4 delta₀_card)
  have h_le_d3 : delta₀ ≤ d3 := h_le_d4.trans (min_le_left d3 delta₀_ineq)
  have h_le_d2 : delta₀ ≤ d2 := h_le_d3.trans (min_le_left d2 delta₀_abs2)
  have h_le_d1 : delta₀ ≤ d1 := h_le_d2.trans (min_le_left d1 delta₀_abs1)

  have hdelta_small : delta < 1 / 16 := by
    have h1 : delta ≤ delta₀_small := by
      calc delta ≤ delta₀ := hdelta_le
           _ ≤ delta₀_small := min_le_right d5 delta₀_small
    have h2 : delta₀_small = 1 / 17 := by rfl
    rw [h2] at h1
    have h3 : delta ≤ 1 / 17 := h1
    have h4 : (1 / 17 : ℝ) < 1 / 16 := by norm_num
    exact h3.trans_lt h4

  -- Weaken hExt from eta to eta_ref
  have hExt_etaRef : WZ1ExtremalPair sigma eta_ref F U Y :=
    WZ1ExtremalPair.mono_epsilon hExt heta_le_eta_ref

  -- Extract components
  have hY_ball : Y.union ⊆ Metric.closedBall (0 : Point3) 1 := hExt_etaRef.2.2.2.1
  have hF_distinct : F.IsEssentiallyDistinct := hExt_etaRef.2.2.2.2.1
  have hF_nonempty : F.Nonempty := hExt_etaRef.2.2.1
  have hU_uniform : U.uniformity ≤ Kakeya.realRpowENN delta (-eta_ref) := hExt_etaRef.2.2.2.2.2.1
  have hU_frostman : U.IsFrostmanAtEveryScale (Kakeya.realRpowENN delta (-eta_ref)) := hExt_etaRef.2.2.2.2.2.2.1
  have hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN delta eta_ref) := hExt_etaRef.2.2.2.2.2.2.2.1
  have hY_vol_upper : MeasureTheory.volume Y.union ≤ Kakeya.realRpowENN delta (sigma - eta_ref) := hExt_etaRef.2.2.2.2.2.2.2.2.1

  -- Parameter bounds
  have hdelta_le_floor : delta ≤ delta₀_floor := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ d1 := h_le_d1
         _ ≤ delta₀_floor := min_le_left delta₀_floor delta₀_leaf
  have hdelta_le_leaf : delta ≤ delta₀_leaf := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ d1 := h_le_d1
         _ ≤ delta₀_leaf := min_le_right delta₀_floor delta₀_leaf
  have hdelta_le_abs1 : delta ≤ delta₀_abs1 := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ d2 := h_le_d2
         _ ≤ delta₀_abs1 := min_le_right d1 delta₀_abs1
  have hdelta_le_abs2 : delta ≤ delta₀_abs2 := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ d3 := h_le_d3
         _ ≤ delta₀_abs2 := min_le_right d2 delta₀_abs2
  have hdelta_le_ineq : delta ≤ delta₀_ineq := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ d4 := h_le_d4
         _ ≤ delta₀_ineq := min_le_right d3 delta₀_ineq
  have hdelta_le_card : delta ≤ delta₀_card := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ d5 := h_le_d5
         _ ≤ delta₀_card := min_le_right d4 delta₀_card

  have h_abs1' : Kakeya.realRpowENN delta inputLoss ≤ (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta :=
    h_abs1 delta hdelta hdelta_le_abs1
  have h_abs2' : Kakeya.realRpowENN delta eta_ref ≤ (1 / 2 : ENNReal) * Kakeya.realRpowENN delta (retentionLoss + eta) := by
    have h := h_abs2 delta hdelta hdelta_le_abs2
    have h1 : ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤ := by simp
    have h2 : (1 / 2 : ENNReal) ≠ ⊤ := by simp
    have h_eq : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
      apply (ENNReal.toReal_eq_toReal_iff' h1 h2).mp
      simp [ENNReal.toReal_div] <;> norm_num
    rw [h_eq] at h
    exact h
  have h_ineq_bound' : Real.rpow delta (3 * eta_ref - epsilon_ref) ≥ 4 :=
    h_ineq_bound delta hdelta hdelta_le_ineq
  have h_log_bound' : 2 * (Real.log ((99 : ℝ)^6 * Real.rpow delta (-(6 + eta_ref))) / Real.log 2 + 1) ≤
      Real.rpow delta (eta_ref - epsilon_ref) := by
    have h := h_log_bound_thresh delta hdelta hdelta_le_card
    have h_exp : -(epsilon_ref - eta_ref) = eta_ref - epsilon_ref := by ring
    rw [h_exp] at h
    exact h

  -- Step 8: Parent balancing
  rcases parent_balancing (inputLoss := inputLoss) with
    ⟨retained, hretained_condition, hretained_mass⟩

  -- Step 9: Apply leaf to each retained parent
  classical
  let hrho : 0 < rho.1 := lt_of_lt_of_le hExt.1 rho.2.1
  have hExt_inputLoss : WZ1ExtremalPair sigma inputLoss F U Y :=
    WZ1ExtremalPair.mono_epsilon hExt (by linarith)

  have h_data : ∀ j ∈ retained,
      Nonempty (WZ1RescaledCoveredParentFiberData
        (sigma := sigma) (outputLoss := outputLoss)
        (retentionLoss := retentionLoss) U Y rho j hrho) := by
    intro j hj
    exact hLeafInner delta hdelta hdelta_le_leaf F U Y hExt_inputLoss rho
      hrho_lower hrho_upper j (hretained_condition j hj)

  let data : ∀ j ∈ retained, WZ1RescaledCoveredParentFiberData
      (sigma := sigma) (outputLoss := outputLoss)
      (retentionLoss := retentionLoss) U Y rho j hrho :=
    fun j hj => (h_data j hj).some

  let S : Fin (U.coarse rho).card → Kakeya.Streamlined.TubeShading F :=
    fun j => if hj : j ∈ retained then (data j hj).sourceShading else Y

  have hS_sub : ∀ j ∈ retained, IsSubshading (S j) Y := by
    intro j hj
    have hS_j : S j = (data j hj).sourceShading := by
      simp [S, hj]
    rw [hS_j]
    exact (data j hj).source_subshading

  have hS_supported : ∀ j ∈ retained, ∀ i,
      (S j).carrier i ≠ ∅ → (U.cover rho).toFactoring.parent i = j := by
    intro j hj i hne
    have hS_j : S j = (data j hj).sourceShading := by
      simp [S, hj]
    rw [hS_j] at hne
    have h_nonempty : ((data j hj).sourceShading.carrier i).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    rcases h_nonempty with ⟨p, hp⟩
    have h : (U.cover rho).parent i = j := (data j hj).source_supported_on_parent i p hp
    exact_mod_cast h

  -- Step 10: Union source shadings
  let Z : Kakeya.Streamlined.TubeShading F :=
    unionParentShadings retained S

  have hZ_subshading : IsSubshading Z Y :=
    unionParentShadings_subshading hS_sub hS_supported

  have hZ_mass_eq : Z.mass = ∑ j ∈ retained, (S j).mass :=
    unionParentShadings_mass hS_sub hS_supported

  have hZ_fiber_cap : ∀ j p,
      ((U.cover rho).toFactoring.fiberPointMultiplicity Z j p : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1) (-sigma - outputLoss) :=
    unionParentShadings_fiber_cap hS_sub hS_supported
      (fun j hj p => by
        have hSj : S j = (data j hj).sourceShading := by simp [S, hj]
        rw [hSj]
        exact (data j hj).source_fiber_cap p)

  -- Step 11: Z density at eta_ref
  have hZ_mass_lower : Z.mass ≥
      Kakeya.realRpowENN delta retentionLoss *
        ∑ j ∈ retained, (U.cover rho).toFactoring.fiberShadedMass Y j := by
    rw [hZ_mass_eq]
    have h2 : ∑ j ∈ retained, (S j).mass ≥
        ∑ j ∈ retained, (Kakeya.realRpowENN delta retentionLoss *
          (U.cover rho).toFactoring.fiberShadedMass Y j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hSj : S j = (data j hj).sourceShading := by simp [S, hj]
      rw [hSj]
      exact (data j hj).retained_source_mass
    rw [Finset.mul_sum] at *
    <;> exact h2

  have hY_dense_eta : Y.IsLambdaDense (Kakeya.realRpowENN delta eta) :=
    hExt.2.2.2.2.2.2.2.1

  let FMass := F.toBodyFamily.mass

  -- Finiteness proofs for the subtraction lemma
  have hY_ball' : Y.union ⊆ Metric.closedBall (0 : Point3) 1 := hExt_etaRef.2.2.2.1
  have h_ball_ne_top : MeasureTheory.volume (Metric.closedBall (0 : Point3) 1) ≠ ⊤ := by
    have h : MeasureTheory.volume (Metric.closedBall (0 : Point3) 1) < ⊤ :=
      MeasureTheory.measure_closedBall_lt_top
    exact h.ne
  have hY_union_ne_top : MeasureTheory.volume Y.union ≠ ⊤ := by
    have h_le : volume Y.union ≤ volume (Metric.closedBall (0 : Point3) 1) := measure_mono hY_ball'
    exact ne_top_of_le_ne_top h_ball_ne_top h_le
  have hY_mass_ne_top : Y.mass ≠ ⊤ := by
    have h1 : Y.mass = ∑ i : Fin F.card, volume (Y.carrier i) := by rfl
    rw [h1]
    exact ENNReal.sum_ne_top.mpr (fun i _ => by
      have h2 : volume (Y.carrier i) ≤ volume Y.union := measure_mono (fun p hp => ⟨i, hp⟩)
      exact ne_top_of_le_ne_top hY_union_ne_top h2)
  have h_rpow_eta_pos : 0 < Kakeya.realRpowENN delta eta := by
    simp [Kakeya.realRpowENN, hdelta] <;> positivity
  have hFMass_ne_top : FMass ≠ ⊤ := by
    by_contra h
    have h3 : Kakeya.realRpowENN delta eta * FMass = ⊤ := by
      rw [h] <;> simp [h_rpow_eta_pos.ne']
    have h4 : Kakeya.realRpowENN delta eta * FMass ≤ Y.mass := hY_dense_eta
    rw [h3] at h4
    have h5 : Y.mass = ⊤ := top_le_iff.mp h4
    exact hY_mass_ne_top h5
  have hc_ne_top : Kakeya.realRpowENN delta inputLoss * FMass ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN]) hFMass_ne_top

  have h_step1 : Kakeya.realRpowENN delta inputLoss * FMass ≤
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass := by
    gcongr <;> exact h_abs1'

  have h_step2 : (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass +
      Kakeya.realRpowENN delta inputLoss * FMass ≤
      Kakeya.realRpowENN delta eta * FMass := by
    let X : ENNReal := Kakeya.realRpowENN delta eta * FMass
    have h_half_add : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
      have h21 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
      rw [h21]
      have h22 : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = ENNReal.ofReal (1 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)] <;> norm_num
      rw [h22] <;> simp
    have h_assoc : (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass = (1 / 2 : ENNReal) * X := by
      rw [mul_assoc]
    have h_sum : (1 / 2 : ENNReal) * X + (1 / 2 : ENNReal) * X = X := by
      calc (1 / 2 : ENNReal) * X + (1 / 2 : ENNReal) * X
          = ((1 / 2 : ENNReal) + (1 / 2 : ENNReal)) * X := by rw [add_mul]
        _ = (1 : ENNReal) * X := by rw [h_half_add]
        _ = X := by simp
    have h' : Kakeya.realRpowENN delta inputLoss * FMass ≤ (1 / 2 : ENNReal) * X := by
      rw [←h_assoc]
      exact h_step1
    calc
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass + Kakeya.realRpowENN delta inputLoss * FMass
        = (1 / 2 : ENNReal) * X + Kakeya.realRpowENN delta inputLoss * FMass := by rw [h_assoc]
      _ ≤ (1 / 2 : ENNReal) * X + (1 / 2 : ENNReal) * X := by gcongr
      _ = X := h_sum
      _ = Kakeya.realRpowENN delta eta * FMass := by rfl

  have h_step3 : Kakeya.realRpowENN delta eta * FMass ≤ Y.mass := hY_dense_eta

  have h_step4 : (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass +
      Kakeya.realRpowENN delta inputLoss * FMass ≤ Y.mass :=
    h_step2.trans h_step3

  have h_step5 : (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass ≤
      Y.mass - Kakeya.realRpowENN delta inputLoss * FMass :=
    ennreal_sub_ge_of_ge_add hc_ne_top h_step4

  have h_step6 : ∑ j ∈ retained, (U.cover rho).toFactoring.fiberShadedMass Y j ≥
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass := by
    exact h_step5.trans hretained_mass

  have h_step7 : Z.mass ≥
      Kakeya.realRpowENN delta retentionLoss *
        ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass) := by
    calc Z.mass
      ≥ Kakeya.realRpowENN delta retentionLoss *
          ∑ j ∈ retained, (U.cover rho).toFactoring.fiberShadedMass Y j := hZ_mass_lower
    _ ≥ Kakeya.realRpowENN delta retentionLoss *
          ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass) := by gcongr

  have h_rpow_add : Kakeya.realRpowENN delta retentionLoss * Kakeya.realRpowENN delta eta =
      Kakeya.realRpowENN delta (retentionLoss + eta) := by
    simp only [Kakeya.realRpowENN]
    have h_nonneg1 : 0 ≤ Real.rpow delta retentionLoss := Real.rpow_nonneg hdelta.le _
    have h_nonneg2 : 0 ≤ Real.rpow delta eta := Real.rpow_nonneg hdelta.le _
    have h_rpow : Real.rpow delta retentionLoss * Real.rpow delta eta =
        Real.rpow delta (retentionLoss + eta) :=
      (Real.rpow_add hdelta retentionLoss eta).symm
    rw [← ENNReal.ofReal_mul h_nonneg1, h_rpow]
    <;> rfl

  have h_step8 : Z.mass ≥
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta (retentionLoss + eta) * FMass := by
    have h : Kakeya.realRpowENN delta retentionLoss *
        ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass) =
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta (retentionLoss + eta) * FMass := by
      have h_assoc : Kakeya.realRpowENN delta retentionLoss *
          ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * FMass) =
          (1 / 2 : ENNReal) * (Kakeya.realRpowENN delta retentionLoss * Kakeya.realRpowENN delta eta) * FMass := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h_assoc, h_rpow_add] <;> simp [mul_assoc]
    rw [h] at h_step7
    exact h_step7

  have h_step9 : Kakeya.realRpowENN delta eta_ref * FMass ≤
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta (retentionLoss + eta) * FMass := by
    gcongr <;> exact h_abs2'

  have hZ_density : Z.IsLambdaDense (Kakeya.realRpowENN delta eta_ref) :=
    h_step9.trans h_step8

  -- Step 12: Cardinality bound
  have h_card_raw : (F.card : ℝ) ≤ (99 : ℝ)^6 * Real.rpow delta (-6 - eta_ref) :=
    wz1_poly_card_bound hdelta hdelta_one hdelta_small hExt_etaRef
  have h_eq : (-6 - eta_ref) = (-(6 + eta_ref)) := by ring
  have h_card : (F.card : ℝ) ≤ (99 : ℝ)^6 * Real.rpow delta (-(6 + eta_ref)) := by
    rw [h_eq] at h_card_raw
    exact h_card_raw
  have h_card_bound : 2 * (Nat.log 2 F.card + 1 : ENNReal) ≤
      Kakeya.realRpowENN delta (eta_ref - epsilon_ref) :=
    cardinality_bound_from_poly hdelta hdelta_one hF_nonempty
      (by norm_num) (by linarith) h_card h_log_bound'

  -- Step 13: Mass inequality
  have h_mass_ineq : Kakeya.realRpowENN delta (2 * eta_ref) ≥
      4 * Kakeya.realRpowENN delta (epsilon_ref - eta_ref) :=
    mass_inequality_from_extremal hdelta hdelta_one heta_ref_pos
      h3eta_ref_lt_epsilon h_ineq_bound'

  -- Step 14: Apply fine multiplicity refinement
  have hZ_union_sub : Z.union ⊆ Y.union := hZ_subshading.union_subset
  have hZ_vol_upper : MeasureTheory.volume Z.union ≤ Kakeya.realRpowENN delta (sigma - eta_ref) :=
    (measure_mono hZ_union_sub).trans hY_vol_upper
  rcases fine_multiplicity_refinement_explicit
      hdelta hdelta_one hsigma hsigma_one hepsilon_ref_pos
      heta_ref_pos h3eta_ref_lt_epsilon
      hF_nonempty hF_distinct hU_uniform hU_frostman
      hZ_density hZ_vol_upper h_card_bound h_mass_ineq with
    ⟨W, m, hW_subshading, hm_pos, hW_const_mult, hm_lower, hW_mass⟩

  -- Step 15: Critical floor for W
  have hW_density_floor : W.IsLambdaDense (Kakeya.realRpowENN delta eta_floor) := by
    have h1 : Kakeya.realRpowENN delta eta_floor * FMass ≤
        Kakeya.realRpowENN delta epsilon_ref * FMass := by
      gcongr
      <;> apply ENNReal.ofReal_mono
        <;> apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
    exact h1.trans hW_mass

  have hW_ball : W.union ⊆ Metric.closedBall (0 : Point3) 1 :=
    hW_subshading.union_subset.trans (hZ_subshading.union_subset.trans hY_ball)

  have hU_uniform_floor : U.uniformity ≤ Kakeya.realRpowENN delta (-eta_floor) := by
    have h1 : Kakeya.realRpowENN delta (-eta_ref) ≤
        Kakeya.realRpowENN delta (-eta_floor) := by
      apply ENNReal.ofReal_mono
      apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
    exact hU_uniform.trans h1

  have hU_frostman_floor : U.IsFrostmanAtEveryScale
        (Kakeya.realRpowENN delta (-eta_floor)) := by
    intro rho' j K hK_convex hK_subset
    have h_old := hU_frostman rho' j K hK_convex hK_subset
    have h_mon : Kakeya.realRpowENN delta (-eta_ref) ≤
        Kakeya.realRpowENN delta (-eta_floor) := by
      apply ENNReal.ofReal_mono
      apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
    exact h_old.trans (by gcongr)

  have hW_vol_lower : Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      MeasureTheory.volume W.union :=
    hFloor delta hdelta hdelta_le_floor F hF_nonempty hF_distinct U
      hU_uniform_floor hU_frostman_floor W hW_ball hW_density_floor

  -- Step 16: Assemble WZ1ExtremalPair for W at outputLoss
  have hW_extremal : WZ1ExtremalPair sigma outputLoss F U W := by
    refine' ⟨hdelta, hdelta_one, hF_nonempty, hW_ball, hF_distinct, _, _, _, _, _⟩
    · -- uniformity
      have h1 : U.uniformity ≤ Kakeya.realRpowENN delta (-eta_ref) := hU_uniform
      have h2 : Kakeya.realRpowENN delta (-eta_ref) ≤
          Kakeya.realRpowENN delta (-outputLoss) := by
        apply ENNReal.ofReal_mono
        apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
      exact h1.trans h2
    · -- Frostman
      intro rho' j K hK_convex hK_subset
      have h_old := hU_frostman rho' j K hK_convex hK_subset
      have h_mon : Kakeya.realRpowENN delta (-eta_ref) ≤
          Kakeya.realRpowENN delta (-outputLoss) := by
        apply ENNReal.ofReal_mono
        apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
      exact h_old.trans (by gcongr)
    · -- density
      have h1 : Kakeya.realRpowENN delta outputLoss * FMass ≤
          Kakeya.realRpowENN delta massLoss * FMass := by
        gcongr <;> apply ENNReal.ofReal_mono
          <;> apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
      have h2 : Kakeya.realRpowENN delta massLoss * FMass ≤
          Kakeya.realRpowENN delta epsilon_ref * FMass := by
        gcongr <;> apply ENNReal.ofReal_mono
          <;> apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
      exact h1.trans (h2.trans hW_mass)
    · -- volume upper
      have h1 : MeasureTheory.volume W.union ≤ MeasureTheory.volume Z.union :=
        measure_mono hW_subshading.union_subset
      have h2 : MeasureTheory.volume Z.union ≤
          Kakeya.realRpowENN delta (sigma - eta_ref) := by
        have h3 : Z.union ⊆ Y.union := hZ_subshading.union_subset
        have h4 : MeasureTheory.volume Z.union ≤ MeasureTheory.volume Y.union := measure_mono h3
        exact h4.trans hY_vol_upper
      have h3 : Kakeya.realRpowENN delta (sigma - eta_ref) ≤
          Kakeya.realRpowENN delta (sigma - outputLoss) := by
        apply ENNReal.ofReal_mono
        apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
      calc
        MeasureTheory.volume W.union
          ≤ MeasureTheory.volume Z.union := h1
        _ ≤ Kakeya.realRpowENN delta (sigma - eta_ref) := h2
        _ ≤ Kakeya.realRpowENN delta (sigma - outputLoss) := h3
    · -- volume lower
      exact hW_vol_lower

  -- Step 17: Final checks
  have h_retained_mass : Kakeya.realRpowENN delta massLoss * FMass ≤ W.mass := by
    have h3 : Kakeya.realRpowENN delta massLoss * FMass ≤
        Kakeya.realRpowENN delta epsilon_ref * FMass := by
      gcongr <;> apply ENNReal.ofReal_mono
        <;> apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
    exact h3.trans hW_mass

  have h_fine_mult_lower : Kakeya.realRpowENN delta (-sigma + outputLoss) ≤ (m : ENNReal) := by
    have h1 : Kakeya.realRpowENN delta (-sigma + outputLoss) ≤
        Kakeya.realRpowENN delta (-sigma + epsilon_ref) := by
      apply ENNReal.ofReal_mono
      apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one <;> linarith
    exact h1.trans hm_lower

  have h_fiber_cap : ∀ j p,
      ((U.cover rho).toFactoring.fiberPointMultiplicity W j p : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1) (-sigma - outputLoss) := by
    intro j p
    have h1 : (U.cover rho).toFactoring.fiberPointMultiplicity W j p ≤
        (U.cover rho).toFactoring.fiberPointMultiplicity Z j p := by
      dsimp only [Kakeya.Streamlined.Factoring.fiberPointMultiplicity]
      apply Finset.card_le_card
      intro i hi
      have h_in_fiber : i ∈ (U.cover rho).toFactoring.fiberIndices j :=
        (Finset.mem_filter.mp hi).1
      have h_in_W : p ∈ W.carrier i := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨h_in_fiber, hW_subshading i h_in_W⟩
    have h2 : ((U.cover rho).toFactoring.fiberPointMultiplicity Z j p : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1) (-sigma - outputLoss) :=
      hZ_fiber_cap j p
    have h3 : ((U.cover rho).toFactoring.fiberPointMultiplicity W j p : ENNReal) ≤
        ((U.cover rho).toFactoring.fiberPointMultiplicity Z j p : ENNReal) := by
      simpa using h1
    exact h3.trans h2

  refine' ⟨W, (fun i => (hW_subshading i).trans (hZ_subshading i)), hW_extremal, m, hm_pos,
    hW_const_mult, h_fine_mult_lower, h_retained_mass, h_fiber_cap⟩

end Kakeya.Assouad
