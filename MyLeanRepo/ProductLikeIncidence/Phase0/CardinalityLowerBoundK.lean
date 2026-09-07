module

/-
# Generalized Cardinality Lower Bound

Generalizes `cardinality_lower_bound` from overlap ≤ 3 to arbitrary overlap K.

For approximate incidence, the overlap bound is 7 (not 3), so the constant
changes from `3·C²` to `K·C²`.

## Main result

`cardinality_lower_bound_K`: |T_y| ≥ δ^{-2s}/(K·C²)
-/

public import MyLeanRepo.ProductLikeIncidence.CoveringLowerBound
public import MyLeanRepo.ProductLikeIncidence.CardinalityLowerBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped ENNReal

namespace ProductLikeIncidence

-- Re-exported helper: finiteness from ENNReal encard bound
lemma finite_of_ennreal_encard_bound' {α : Type*} {S : Set α} {r : ℝ}
    (h : ENat.toENNReal S.encard ≤ ENNReal.ofReal r) : S.Finite := by
  have h1 : ENat.toENNReal S.encard ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have h2 : S.encard ≠ ⊤ := by
    intro h3
    rw [h3] at h1
    simp at h1
  have h3 : S.encard < ⊤ := lt_top_iff_ne_top.mpr h2
  exact Set.encard_lt_top_iff.mp h3

-- Helper: bounded overlap for finsets
lemma bounded_overlap_finset' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (T : α → Finset β) (K : ℕ)
    (h : ∀ b ∈ s.biUnion T, (s.filter (fun i => b ∈ T i)).card ≤ K) :
    ∑ i ∈ s, (T i).card ≤ K * (s.biUnion T).card := by
  let incidences := s.sigma T
  let f : (Σ _ : α, β) → β := fun p => p.2
  have h1 : incidences.card = ∑ i ∈ s, (T i).card := by rw [Finset.card_sigma]
  have h2 : Finset.image f incidences = s.biUnion T := by
    ext b; simp [incidences, f] <;> aesop
  have h3 : ∀ b ∈ Finset.image f incidences,
      (Finset.filter (fun p : Σ _ : α, β => f p = b) incidences).card ≤ K := by
    intro b hb
    rw [h2] at hb
    have h4 : (Finset.filter (fun p : Σ _ : α, β => f p = b) incidences).card =
        (s.filter (fun i => b ∈ T i)).card := by
      let g : α → (Σ _ : α, β) := fun i => ⟨i, b⟩
      have h_inj : Function.Injective g := by intro i j h; simpa [g] using h
      have h_image : Finset.image g (s.filter (fun i => b ∈ T i)) =
          Finset.filter (fun p : Σ _ : α, β => f p = b) incidences := by
        ext p; simp [g, incidences, f] <;> aesop
      rw [←h_image, Finset.card_image_of_injective _ h_inj]
    rw [h4]
    exact h b hb
  have h5 := Finset.card_le_mul_card_image incidences K h3
  rw [h1, h2] at h5
  exact h5

/-- Generalized bounded overlap double counting for arbitrary K. -/
lemma bounded_overlap_set_K {α β : Type*}
    (S : Set α) (T : α → Set β) (K : ℕ)
    (hS : S.Finite)
    (hT : ∀ i ∈ S, (T i).Finite)
    (h : ∀ b ∈ ⋃ i ∈ S, T i,
        {i ∈ S | b ∈ T i}.Finite ∧ {i ∈ S | b ∈ T i}.encard ≤ K) :
    ENat.toENNReal (⋃ i ∈ S, T i).encard * (K : ENNReal) ≥
      ∑ᶠ i ∈ S, ENat.toENNReal (T i).encard := by
  classical
  let sFinset := hS.toFinset
  let TFinset : α → Finset β := fun i =>
    if h : i ∈ S then (hT i h).toFinset else ∅
  have hTFinset_eq : ∀ i ∈ S, (TFinset i : Set β) = T i := by
    intro i hi
    simp [TFinset, hi]
  have h_coe_s : (sFinset : Set α) = S := by exact hS.coe_toFinset
  have h_union : (⋃ i ∈ S, T i) = ↑(sFinset.biUnion TFinset) := by
    ext b
    have h1 : b ∈ (⋃ i ∈ S, T i) ↔ ∃ i ∈ S, b ∈ T i := by
      simp [Set.mem_iUnion]
    have h2 : b ∈ (↑(sFinset.biUnion TFinset) : Set β) ↔ ∃ i ∈ sFinset, b ∈ TFinset i := by
      simpa [Finset.mem_biUnion] using Iff.rfl
    rw [h1, h2]
    constructor
    · rintro ⟨i, hi, hbi⟩
      have h_i_in : i ∈ sFinset := by
        have h20 : i ∈ (sFinset : Set α) := by simpa [h_coe_s] using hi
        exact h20
      have h_b_in : b ∈ TFinset i := by
        have h_eq : (TFinset i : Set β) = T i := hTFinset_eq i hi
        have h20 : b ∈ (TFinset i : Set β) := by
          have h21 : b ∈ T i := hbi
          rw [h_eq] at * <;> tauto
        exact h20
      exact ⟨i, h_i_in, h_b_in⟩
    · rintro ⟨i, hi, hbi⟩
      have hi' : i ∈ S := by
        have h20 : i ∈ (sFinset : Set α) := hi
        simpa [h_coe_s] using h20
      have h_b_in : b ∈ T i := by
        have h_eq : (TFinset i : Set β) = T i := hTFinset_eq i hi'
        have h20 : b ∈ (TFinset i : Set β) := hbi
        have h21 : b ∈ T i := by rw [←h_eq]; exact h20
        exact h21
      exact ⟨i, hi', h_b_in⟩
  have h_encard_T : ∀ i ∈ S, (T i).encard = ↑(TFinset i).card := by
    intro i hi
    have h6 : (T i) = ↑(TFinset i) := (hTFinset_eq i hi).symm
    rw [h6, Set.encard_coe_eq_coe_finsetCard]
  have h_overlap' : ∀ b ∈ sFinset.biUnion TFinset,
      (sFinset.filter (fun i => b ∈ TFinset i)).card ≤ K := by
    intro b hb
    have h7 : b ∈ ⋃ i ∈ S, T i := by rw [h_union] <;> exact hb
    have h8 := (h b h7)
    have h9 : {i ∈ S | b ∈ T i}.Finite := h8.1
    have h10 : {i ∈ S | b ∈ T i}.encard ≤ K := h8.2
    have h11 : (sFinset.filter (fun i => b ∈ TFinset i)) = h9.toFinset := by
      ext i
      simp only [Finset.mem_filter]
      have h_iS : i ∈ sFinset ↔ i ∈ S := by
        constructor
        · intro h
          have h20 : i ∈ (sFinset : Set α) := h
          simpa [h_coe_s] using h20
        · intro h
          have h20 : i ∈ (sFinset : Set α) := by simpa [h_coe_s] using h
          exact h20
      by_cases h13 : i ∈ sFinset
      · have h14 : i ∈ S := h_iS.mp h13
        have h15 : b ∈ TFinset i ↔ b ∈ T i := by
          have h16 : (TFinset i : Set β) = T i := hTFinset_eq i h14
          exact Set.ext_iff.mp h16 b
        simp [h13, h15, h14]
      · have h14 : i ∉ S := by
          intro h
          exact h13 (h_iS.mpr h)
        simp [h13, h14]
    rw [h11]
    have h13 : {i ∈ S | b ∈ T i}.encard = ↑(h9.toFinset.card) := h9.encard_eq_coe_toFinset_card
    rw [h13] at h10
    exact_mod_cast h10
  have h_main := bounded_overlap_finset' sFinset TFinset K h_overlap'
  have h13 : ENat.toENNReal (⋃ i ∈ S, T i).encard = ↑((sFinset.biUnion TFinset).card) := by
    rw [h_union, Set.encard_coe_eq_coe_finsetCard] <;> rfl
  have h14 : (∑ᶠ i ∈ S, ENat.toENNReal (T i).encard) =
      ∑ i ∈ sFinset, ENat.toENNReal (T i).encard := by
    apply finsum_mem_eq_sum_of_subset (f := fun i => ENat.toENNReal (T i).encard)
    · intro x hx; rw [h_coe_s] at *; exact hx.1
    · rw [h_coe_s]
  rw [h14, h13]
  have h15 : ∀ i ∈ sFinset, ENat.toENNReal (T i).encard = ↑((TFinset i).card) := by
    intro i hi
    have h16 : i ∈ S := by rw [←h_coe_s] <;> exact hi
    rw [h_encard_T i h16] <;> rfl
  have h16 : ∑ i ∈ sFinset, ENat.toENNReal (T i).encard =
      ∑ i ∈ sFinset, (↑((TFinset i).card) : ENNReal) := by
    apply Finset.sum_congr rfl; intro i hi; exact h15 i hi
  rw [h16]
  have h17 : (∑ i ∈ sFinset, (↑((TFinset i).card) : ENNReal)) ≤
      (K : ENNReal) * ↑((sFinset.biUnion TFinset).card) := by
    exact_mod_cast h_main
  have h18 : (∑ i ∈ sFinset, (↑((TFinset i).card) : ENNReal)) ≤
      ↑((sFinset.biUnion TFinset).card) * (K : ENNReal) := by
    have h19 : (K : ENNReal) * ↑((sFinset.biUnion TFinset).card) =
        ↑((sFinset.biUnion TFinset).card) * (K : ENNReal) := by ring
    rw [h19] at h17
    exact h17
  exact h18

/-- Generalized cardinality lower bound with arbitrary overlap K.

The union T_y has cardinality at least δ^{-2s}/(K·C²). -/
lemma cardinality_lower_bound_K
    {α : Type*} {δ s C y : ℝ} {K : ℕ}
    {X : Set ℝ} {T_x : ℝ → Set α}
    {cell : α → Set (EuclideanSpace ℝ (Fin 2))}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs : 0 < s) (hC : 1 ≤ C) (hK_pos : 1 ≤ K)
    (hX_regular : IsDeltaSCSet δ s C (realLineCopy X))
    (hX_upper : ENat.toENNReal X.encard ≤ ENNReal.ofReal (δ ^ (-s)))
    (hcell : ∀ x ∈ X, ∀ a ∈ T_x x, cell a ∈ dyadicCubes 2 δ)
    (hcell_inj : Set.InjOn cell (⋃ x ∈ X, T_x x))
    (hTx_regular : ∀ x ∈ X,
      IsDeltaSCSet δ s C (cellRealization cell (T_x x)))
    (hTx_upper : ∀ x ∈ X,
      ENat.toENNReal (T_x x).encard ≤ ENNReal.ofReal (δ ^ (-s)))
    (hoverlap : ∀ a ∈ ⋃ x ∈ X, T_x x,
      {x ∈ X | a ∈ T_x x}.Finite ∧
      {x ∈ X | a ∈ T_x x}.encard ≤ K) :
    ENNReal.ofReal (δ ^ (-2 * s) / ((K : ℝ) * C ^ 2)) ≤
      ENat.toENNReal (⋃ x ∈ X, T_x x).encard := by
  let T_y := ⋃ x ∈ X, T_x x
  let c : ENNReal := ENNReal.ofReal (δ ^ (-s) / C)
  have hC_pos : 0 < C := by linarith
  have hX_finite : X.Finite := finite_of_ennreal_encard_bound' hX_upper
  have hTx_finite : ∀ x ∈ X, (T_x x).Finite := fun x hx =>
    finite_of_ennreal_encard_bound' (hTx_upper x hx)
  have h_c_eq : c = ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
    have h_eq : δ ^ (-s) / C = C⁻¹ * δ ^ (-s) := by
      field_simp [hC_pos.ne'] <;> ring
    exact congr_arg ENNReal.ofReal h_eq
  -- Step 1: c ≤ |X|
  have h1 : c ≤ ENat.toENNReal X.encard := by
    have hcov : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy X)) :=
      covering_lower_bound hX_regular
    rw [←h_c_eq] at hcov
    have hle : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy X)) ≤
        ENat.toENNReal (realLineCopy X).encard := covering_number_le_encard hδ
    have h_encard : (realLineCopy X).encard = X.encard := by
      let mkPoint1 : ℝ → EuclideanSpace ℝ (Fin 1) := fun x =>
        (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun (_ : Fin 1) => x)
      have h_eq1 : realLineCopy X = mkPoint1 '' X := by
        ext p
        simp only [realLineCopy, Set.mem_image, Set.mem_setOf_eq]
        constructor
        · intro hp
          refine ⟨p 0, hp, ?_⟩
          exact PiLp.ext (fun i => by fin_cases i <;> rfl)
        · rintro ⟨x, hx, rfl⟩
          simpa [mkPoint1] using hx
      rw [h_eq1]
      have h_inj : Set.InjOn mkPoint1 X := by
        intro x _ y _ h
        have h' : (mkPoint1 x) 0 = (mkPoint1 y) 0 := by rw [h]
        simpa [mkPoint1] using h'
      exact h_inj.encard_image
    rw [h_encard] at hle
    exact le_trans hcov hle
  -- Step 2: ∀ x ∈ X, c ≤ |T_x x|
  have h2 : ∀ x ∈ X, c ≤ ENat.toENNReal (T_x x).encard := by
    intro x hx
    have hcov : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (cellRealization cell (T_x x))) :=
      covering_lower_bound (hTx_regular x hx)
    rw [←h_c_eq] at hcov
    have heq : dyadicCoveringNumber δ (cellRealization cell (T_x x)) = (T_x x).encard :=
      dyadicCoveringNumber_cellRealization hδ
        (fun a ha => hcell x hx a ha)
        (Set.InjOn.mono (show T_x x ⊆ T_y from fun a ha => Set.mem_iUnion₂.mpr ⟨x, hx, ha⟩) hcell_inj)
    rw [heq] at hcov
    exact hcov
  -- Step 3: Σ |T_x x| ≥ |X| * c
  let Xf := hX_finite.toFinset
  have hXf_coe : (Xf : Set ℝ) = X := hX_finite.coe_toFinset
  have h_finsum_eq : ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard =
      ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard := by
    apply finsum_mem_eq_sum_of_subset (f := fun x => ENat.toENNReal (T_x x).encard)
    · intro x hx; rw [hXf_coe] at *; exact hx.1
    · rw [hXf_coe]
  have h_sum_lower : ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard ≥
      (Xf.card : ENNReal) * c := by
    have h_each : ∀ x ∈ Xf, c ≤ ENat.toENNReal (T_x x).encard := by
      intro x hx
      have h_x_in_X : x ∈ X := by rw [←hXf_coe] <;> exact hx
      exact h2 x h_x_in_X
    have h : ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard ≥ ∑ x ∈ Xf, c :=
      Finset.sum_le_sum h_each
    have h2 : ∑ x ∈ Xf, c = (Xf.card : ENNReal) * c := by
      rw [Finset.sum_const] <;> simp [mul_comm] <;> ring
    rw [h2] at h
    exact h
  have h_card_eq : (Xf.card : ENNReal) = ENat.toENNReal X.encard := by
    have h : X.encard = ↑Xf.card := by
      rw [←hXf_coe, Set.encard_coe_eq_coe_finsetCard] <;> rfl
    rw [h] <;> norm_cast
  -- Step 4: Σ |T_x x| ≥ c * c
  have h4 : ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard ≥ c * c := by
    rw [h_finsum_eq]
    calc
      ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard ≥ (Xf.card : ENNReal) * c := h_sum_lower
      _ = ENat.toENNReal X.encard * c := by rw [h_card_eq]
      _ ≥ c * c := by gcongr <;> exact h1
  -- Step 5: c * c = ENNReal.ofReal (δ^{-2s} / C^2)
  have h5 : c * c = ENNReal.ofReal (δ ^ (-2 * s) / C ^ 2) := by
    have hpos1 : 0 ≤ δ ^ (-s) / C := by positivity
    have hpos2 : 0 ≤ δ ^ (-2 * s) / C ^ 2 := by positivity
    have h_mul : ENNReal.ofReal (δ ^ (-s) / C) * ENNReal.ofReal (δ ^ (-s) / C) =
        ENNReal.ofReal ((δ ^ (-s) / C) * (δ ^ (-s) / C)) := by
      rw [← ENNReal.ofReal_mul hpos1] <;> rfl
    rw [h_mul]
    have h_eq : (δ ^ (-s) / C) * (δ ^ (-s) / C) = δ ^ (-2 * s) / C ^ 2 := by
      have h_exp : δ ^ (-s) * δ ^ (-s) = δ ^ (-2 * s) := by
        have h_sum : (-s) + (-s) = -2 * s := by ring
        have h : δ ^ (-s) * δ ^ (-s) = δ ^ ((-s) + (-s)) := by
          rw [← Real.rpow_add (by linarith)] <;> ring
        rw [h, h_sum]
      calc (δ ^ (-s) / C) * (δ ^ (-s) / C)
        = (δ ^ (-s) * δ ^ (-s)) / (C * C) := by ring
      _ = δ ^ (-2 * s) / (C * C) := by rw [h_exp]
      _ = δ ^ (-2 * s) / C ^ 2 := by ring
    rw [h_eq]
  -- Step 6: K * |T_y| ≥ Σ |T_x x|
  have h6 : ENat.toENNReal T_y.encard * (K : ENNReal) ≥
      ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard :=
    bounded_overlap_set_K X T_x K hX_finite hTx_finite hoverlap
  -- Step 7: |T_y| ≥ c * c / K
  have h7 : ENat.toENNReal T_y.encard * (K : ENNReal) ≥ c * c := by
    calc ENat.toENNReal T_y.encard * (K : ENNReal)
      ≥ ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard := h6
    _ ≥ c * c := h4
  have hK_nat_pos : (K : ENNReal) ≠ 0 := by
    have h : 0 < K := by exact_mod_cast hK_pos
    exact_mod_cast h.ne'
  have h8 : ENat.toENNReal T_y.encard ≥ (c * c) / (K : ENNReal) := by
    have h9 : ENat.toENNReal T_y.encard * (K : ENNReal) ≥ c * c := h7
    have h10 : (ENat.toENNReal T_y.encard * (K : ENNReal)) / (K : ENNReal) ≥ (c * c) / (K : ENNReal) := by gcongr
    have h11 : (ENat.toENNReal T_y.encard * (K : ENNReal)) / (K : ENNReal) = ENat.toENNReal T_y.encard := by
      exact ENNReal.mul_div_cancel_right hK_nat_pos (by simp)
    rw [h11] at h10
    exact h10
  rw [h5] at h8
  have h_final : (ENNReal.ofReal (δ ^ (-2 * s) / C ^ 2)) / (K : ENNReal) =
      ENNReal.ofReal (δ ^ (-2 * s) / ((K : ℝ) * C ^ 2)) := by
    have hpos : 0 ≤ δ ^ (-2 * s) / C ^ 2 := by positivity
    let x : ℝ := δ ^ (-2 * s) / C ^ 2
    have hK_pos' : 0 < (K : ℝ) := by exact_mod_cast hK_pos
    have h_inv_coe : (↑K : ENNReal) = ENNReal.ofReal (K : ℝ) := by
      exact Eq.symm (ENNReal.ofReal_natCast K)
    have h_div : ENNReal.ofReal x / (K : ENNReal) =
        ENNReal.ofReal x * ENNReal.ofReal ((K : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, h_inv_coe]
      have h : (ENNReal.ofReal (K : ℝ))⁻¹ = ENNReal.ofReal ((K : ℝ)⁻¹) := by
        rw [← ENNReal.ofReal_inv_of_pos hK_pos']
      rw [h]
    rw [h_div]
    have h_mul : ENNReal.ofReal x * ENNReal.ofReal ((K : ℝ)⁻¹) =
        ENNReal.ofReal (x * (K : ℝ)⁻¹) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h_mul]
    have h_eq : x * (K : ℝ)⁻¹ = δ ^ (-2 * s) / ((K : ℝ) * C ^ 2) := by
      simp only [x] <;> field_simp [hK_pos] <;> ring
    rw [h_eq]
  rw [h_final] at h8
  exact h8

/-- Variant of `cardinality_lower_bound_K` taking finiteness directly instead
of upper cardinality bounds. -/
lemma cardinality_lower_bound_K_finite
    {α : Type*} {δ s C y : ℝ} {K : ℕ}
    {X : Set ℝ} {T_x : ℝ → Set α}
    {cell : α → Set (EuclideanSpace ℝ (Fin 2))}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs : 0 < s) (hC : 1 ≤ C) (hK_pos : 1 ≤ K)
    (hX_regular : IsDeltaSCSet δ s C (realLineCopy X))
    (hX_finite : X.Finite)
    (hTx_finite : ∀ x ∈ X, (T_x x).Finite)
    (hcell : ∀ x ∈ X, ∀ a ∈ T_x x, cell a ∈ dyadicCubes 2 δ)
    (hcell_inj : Set.InjOn cell (⋃ x ∈ X, T_x x))
    (hTx_regular : ∀ x ∈ X,
      IsDeltaSCSet δ s C (cellRealization cell (T_x x)))
    (hoverlap : ∀ a ∈ ⋃ x ∈ X, T_x x,
      {x ∈ X | a ∈ T_x x}.Finite ∧
      {x ∈ X | a ∈ T_x x}.encard ≤ K) :
    ENNReal.ofReal (δ ^ (-2 * s) / ((K : ℝ) * C ^ 2)) ≤
      ENat.toENNReal (⋃ x ∈ X, T_x x).encard := by
  let T_y := ⋃ x ∈ X, T_x x
  let c : ENNReal := ENNReal.ofReal (δ ^ (-s) / C)
  have hC_pos : 0 < C := by linarith
  have h_c_eq : c = ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
    have h_eq : δ ^ (-s) / C = C⁻¹ * δ ^ (-s) := by
      field_simp [hC_pos.ne'] <;> ring
    exact congr_arg ENNReal.ofReal h_eq
  -- Step 1: c ≤ |X|
  have h1 : c ≤ ENat.toENNReal X.encard := by
    have hcov : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy X)) :=
      covering_lower_bound hX_regular
    rw [←h_c_eq] at hcov
    have hle : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy X)) ≤
        ENat.toENNReal (realLineCopy X).encard := covering_number_le_encard hδ
    have h_encard : (realLineCopy X).encard = X.encard := by
      let mkPoint1 : ℝ → EuclideanSpace ℝ (Fin 1) := fun x =>
        (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun (_ : Fin 1) => x)
      have h_eq1 : realLineCopy X = mkPoint1 '' X := by
        ext p
        simp only [realLineCopy, Set.mem_image, Set.mem_setOf_eq]
        constructor
        · intro hp
          refine ⟨p 0, hp, ?_⟩
          exact PiLp.ext (fun i => by fin_cases i <;> rfl)
        · rintro ⟨x, hx, rfl⟩
          simpa [mkPoint1] using hx
      rw [h_eq1]
      have h_inj : Set.InjOn mkPoint1 X := by
        intro x _ y _ h
        have h' : (mkPoint1 x) 0 = (mkPoint1 y) 0 := by rw [h]
        simpa [mkPoint1] using h'
      exact h_inj.encard_image
    rw [h_encard] at hle
    exact le_trans hcov hle
  -- Step 2: ∀ x ∈ X, c ≤ |T_x x|
  have h2 : ∀ x ∈ X, c ≤ ENat.toENNReal (T_x x).encard := by
    intro x hx
    have hcov : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (cellRealization cell (T_x x))) :=
      covering_lower_bound (hTx_regular x hx)
    rw [←h_c_eq] at hcov
    have heq : dyadicCoveringNumber δ (cellRealization cell (T_x x)) = (T_x x).encard :=
      dyadicCoveringNumber_cellRealization hδ
        (fun a ha => hcell x hx a ha)
        (Set.InjOn.mono (show T_x x ⊆ T_y from fun a ha => Set.mem_iUnion₂.mpr ⟨x, hx, ha⟩) hcell_inj)
    rw [heq] at hcov
    exact hcov
  -- Step 3: Σ |T_x x| ≥ |X| * c
  let Xf := hX_finite.toFinset
  have hXf_coe : (Xf : Set ℝ) = X := hX_finite.coe_toFinset
  have h_finsum_eq : ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard =
      ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard := by
    apply finsum_mem_eq_sum_of_subset (f := fun x => ENat.toENNReal (T_x x).encard)
    · intro x hx; rw [hXf_coe] at *; exact hx.1
    · rw [hXf_coe]
  have h_sum_lower : ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard ≥
      (Xf.card : ENNReal) * c := by
    have h_each : ∀ x ∈ Xf, c ≤ ENat.toENNReal (T_x x).encard := by
      intro x hx
      have h_x_in_X : x ∈ X := by rw [←hXf_coe] <;> exact hx
      exact h2 x h_x_in_X
    have h : ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard ≥ ∑ x ∈ Xf, c :=
      Finset.sum_le_sum h_each
    have h2 : ∑ x ∈ Xf, c = (Xf.card : ENNReal) * c := by
      rw [Finset.sum_const] <;> simp [mul_comm] <;> ring
    rw [h2] at h
    exact h
  have h_card_eq : (Xf.card : ENNReal) = ENat.toENNReal X.encard := by
    have h : X.encard = ↑Xf.card := by
      rw [←hXf_coe, Set.encard_coe_eq_coe_finsetCard] <;> rfl
    rw [h] <;> norm_cast
  -- Step 4: Σ |T_x x| ≥ c * c
  have h4 : ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard ≥ c * c := by
    rw [h_finsum_eq]
    calc
      ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard ≥ (Xf.card : ENNReal) * c := h_sum_lower
      _ = ENat.toENNReal X.encard * c := by rw [h_card_eq]
      _ ≥ c * c := by gcongr <;> exact h1
  -- Step 5: c * c = ENNReal.ofReal (δ^{-2s} / C^2)
  have h5 : c * c = ENNReal.ofReal (δ ^ (-2 * s) / C ^ 2) := by
    have hpos1 : 0 ≤ δ ^ (-s) / C := by positivity
    have hpos2 : 0 ≤ δ ^ (-2 * s) / C ^ 2 := by positivity
    have h_mul : ENNReal.ofReal (δ ^ (-s) / C) * ENNReal.ofReal (δ ^ (-s) / C) =
        ENNReal.ofReal ((δ ^ (-s) / C) * (δ ^ (-s) / C)) := by
      rw [← ENNReal.ofReal_mul hpos1] <;> rfl
    rw [h_mul]
    have h_eq : (δ ^ (-s) / C) * (δ ^ (-s) / C) = δ ^ (-2 * s) / C ^ 2 := by
      have h_exp : δ ^ (-s) * δ ^ (-s) = δ ^ (-2 * s) := by
        have h_sum : (-s) + (-s) = -2 * s := by ring
        have h : δ ^ (-s) * δ ^ (-s) = δ ^ ((-s) + (-s)) := by
          rw [← Real.rpow_add (by linarith)] <;> ring
        rw [h, h_sum]
      calc (δ ^ (-s) / C) * (δ ^ (-s) / C)
        = (δ ^ (-s) * δ ^ (-s)) / (C * C) := by ring
      _ = δ ^ (-2 * s) / (C * C) := by rw [h_exp]
      _ = δ ^ (-2 * s) / C ^ 2 := by ring
    rw [h_eq]
  -- Step 6: K * |T_y| ≥ Σ |T_x x|
  have h6 : ENat.toENNReal T_y.encard * (K : ENNReal) ≥
      ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard :=
    bounded_overlap_set_K X T_x K hX_finite hTx_finite hoverlap
  -- Step 7: |T_y| ≥ c * c / K
  have h7 : ENat.toENNReal T_y.encard * (K : ENNReal) ≥ c * c := by
    calc ENat.toENNReal T_y.encard * (K : ENNReal)
      ≥ ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard := h6
    _ ≥ c * c := h4
  have hK_nat_pos : (K : ENNReal) ≠ 0 := by
    have h : 0 < K := by exact_mod_cast hK_pos
    exact_mod_cast h.ne'
  have h8 : ENat.toENNReal T_y.encard ≥ (c * c) / (K : ENNReal) := by
    have h9 : ENat.toENNReal T_y.encard * (K : ENNReal) ≥ c * c := h7
    have h10 : (ENat.toENNReal T_y.encard * (K : ENNReal)) / (K : ENNReal) ≥ (c * c) / (K : ENNReal) := by gcongr
    have h11 : (ENat.toENNReal T_y.encard * (K : ENNReal)) / (K : ENNReal) = ENat.toENNReal T_y.encard := by
      exact ENNReal.mul_div_cancel_right hK_nat_pos (by simp)
    rw [h11] at h10
    exact h10
  rw [h5] at h8
  have h_final : (ENNReal.ofReal (δ ^ (-2 * s) / C ^ 2)) / (K : ENNReal) =
      ENNReal.ofReal (δ ^ (-2 * s) / ((K : ℝ) * C ^ 2)) := by
    have hpos : 0 ≤ δ ^ (-2 * s) / C ^ 2 := by positivity
    let x : ℝ := δ ^ (-2 * s) / C ^ 2
    have hK_pos' : 0 < (K : ℝ) := by exact_mod_cast hK_pos
    have h_inv_coe : (↑K : ENNReal) = ENNReal.ofReal (K : ℝ) := by exact Eq.symm (ENNReal.ofReal_natCast K)
    have h_div : ENNReal.ofReal x / (K : ENNReal) =
        ENNReal.ofReal x * ENNReal.ofReal ((K : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, h_inv_coe]
      have h : (ENNReal.ofReal (K : ℝ))⁻¹ = ENNReal.ofReal ((K : ℝ)⁻¹) := by
        rw [← ENNReal.ofReal_inv_of_pos hK_pos']
      rw [h]
    rw [h_div]
    have h_mul : ENNReal.ofReal x * ENNReal.ofReal ((K : ℝ)⁻¹) =
        ENNReal.ofReal (x * (K : ℝ)⁻¹) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h_mul]
    have h_eq : x * (K : ℝ)⁻¹ = δ ^ (-2 * s) / ((K : ℝ) * C ^ 2) := by
      simp only [x] <;> field_simp [hK_pos] <;> ring
    rw [h_eq]
  rw [h_final] at h8
  exact h8

end ProductLikeIncidence
