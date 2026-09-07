module

/-
# Product Reduction Helpers

Helper lemmas for the product-like incidence reduction theorem.

Extracted from scratch versions of `ProductReduction.lean`.

## Main results

1. `covering_number_eq_encard` — covering number of tube parameter set = tube encard
   (alias for `DualityBridge.covering_number_eq_tube_card`)
2. `parameter_set_within_2delta` — canonical cube points within 2δ of dual line
3. `parameter_set_bounded` — parameter set P is bounded

## Dependencies

- `MyLeanRepo.CoreDefinitions`
- `MyLeanRepo.ProductLikeBasic`
- `MyLeanRepo.DualityBridge`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.DualityBridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set Bornology ENNReal MeasureTheory

namespace ProductLikeIncidence.ProductReduction

/-! ## Covering number = tube cardinality -/

/-- For a family 𝒯 of dyadic δ-tubes, the δ-covering number of the parameter
set P equals the cardinality of 𝒯. Alias for
`DualityBridge.covering_number_eq_tube_card`. -/
lemma covering_number_eq_encard {δ : ℝ} (hδ : 0 < δ)
    (𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2))))
    (h𝒯 : 𝒯 ⊆ appendixDyadicTubes δ) :
    dyadicCoveringNumber δ
      (productLikeAppendixDyadicTubeParameterSet δ 𝒯) = 𝒯.encard :=
  ProductLikeIncidence.DualityBridge.covering_number_eq_tube_card hδ h𝒯

/-! ## Parameter cube proximity to dual line -/

/-- Every parameter point in the canonical cube of a tube through z lies within
2δ of the dual line through z. -/
lemma parameter_set_within_2delta {δ : ℝ} (hδ : 0 < δ)
    {z : EuclideanSpace ℝ (Fin 2)}
    {T : Set (EuclideanSpace ℝ (Fin 2))}
    (hT_tube : T ∈ appendixDyadicTubes δ)
    (hz_in_T : z ∈ T)
    (hy1 : 0 ≤ z 1) (hy2 : z 1 ≤ 1) :
    ∀ p ∈ productLikeAppendixDyadicTubeCanonicalParameterCube δ T,
      |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ := by
  let Q := productLikeAppendixDyadicTubeCanonicalParameterCube δ T
  have hQ_correct : Q ∈ dyadicCubesMeeting (d := 2) δ appendixParameterStrip ∧
      appendixDualOfParameterSet Q = T :=
    ProductLikeIncidence.DualityBridge.canonical_cube_correct hT_tube
  have hQ_dyadic : Q ∈ dyadicCubes 2 δ := hQ_correct.1.1
  rcases hQ_dyadic with ⟨k, hQ_eq⟩
  have hz_in_dual : z ∈ appendixDualOfParameterSet Q := by
    rw [hQ_correct.2] <;> exact hz_in_T
  rcases hz_in_dual with ⟨p0, hp0Q, hz_line⟩
  have hz_eq : z 0 = p0 0 * z 1 + p0 1 := by
    simpa [appendixDualLineMap, appendixDualLine] using hz_line
  intro p hp
  have hpQ' : p ∈ Q := hp
  have hp0Q' : p0 ∈ Q := hp0Q
  have h_p_in : ∀ (x : EuclideanSpace ℝ (Fin 2)), x ∈ Q →
      x 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) ∧
      x 1 ∈ Set.Ico (δ * (k 1 : ℝ)) (δ * ((k 1 : ℝ) + 1)) := by
    intro x hx
    rw [hQ_eq] at hx
    exact ⟨hx 0, hx 1⟩
  have h_p := h_p_in p hpQ'
  have h_p0 := h_p_in p0 hp0Q'
  have h1 : |p 0 - p0 0| < δ := by
    rw [abs_sub_lt_iff] <;> constructor <;> linarith [h_p.1.1, h_p.1.2, h_p0.1.1, h_p0.1.2]
  have h4 : |p 1 - p0 1| < δ := by
    rw [abs_sub_lt_iff] <;> constructor <;> linarith [h_p.2.1, h_p.2.2, h_p0.2.1, h_p0.2.2]
  have h5 : |p 0 * z 1 + p 1 - z 0| =
      |(p 0 - p0 0) * z 1 + (p 1 - p0 1)| := by
    rw [hz_eq] <;> ring_nf <;> rfl
  rw [h5]
  have h6 : |(p 0 - p0 0) * z 1 + (p 1 - p0 1)| ≤
      |p 0 - p0 0| * |z 1| + |p 1 - p0 1| := by
    have h_tri : |(p 0 - p0 0) * z 1 + (p 1 - p0 1)| ≤
        |(p 0 - p0 0) * z 1| + |p 1 - p0 1| := by
      let a := (p 0 - p0 0) * z 1
      let b := (p 1 - p0 1)
      have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
      have h21 : -|a| ≤ a := by
        have h : -a ≤ |a| := by simpa [abs_neg] using le_abs_self (-a)
        linarith
      have h22 : -|b| ≤ b := by
        have h : -b ≤ |b| := by simpa [abs_neg] using le_abs_self (-b)
        linarith
      have h2 : -(|a| + |b|) ≤ a + b := by linarith
      exact abs_le.mpr ⟨h2, h1⟩
    have h_mul : |(p 0 - p0 0) * z 1| = |p 0 - p0 0| * |z 1| := by
      rw [abs_mul]
    rw [h_mul] at h_tri
    exact h_tri
  have h7 : |z 1| ≤ 1 := by rw [abs_of_nonneg hy1] <;> linarith
  have h9 : |p 0 - p0 0| * |z 1| < δ := by
    have h10 : |p 0 - p0 0| * |z 1| ≤ |p 0 - p0 0| := by
      calc |p 0 - p0 0| * |z 1|
        ≤ |p 0 - p0 0| * 1 := by gcongr <;> exact h7
      _ = |p 0 - p0 0| := by ring
    exact lt_of_le_of_lt h10 h1
  have h8 : |(p 0 - p0 0) * z 1 + (p 1 - p0 1)| < 2 * δ := by
    calc |(p 0 - p0 0) * z 1 + (p 1 - p0 1)|
      ≤ |p 0 - p0 0| * |z 1| + |p 1 - p0 1| := h6
    _ < δ + δ := by linarith
    _ = 2 * δ := by ring
  exact le_of_lt h8

/-! ## Boundedness of parameter set -/

/-- The parameter set P is bounded: slopes lie in [-1-δ, 1+δ] (from the
parameter strip) and intercepts lie in [-1-2δ, 2+2δ] (since tubes pass through
points in [0,1]² with slopes in [-1,1]). -/
lemma parameter_set_bounded {δ s : ℝ} (hδ : 0 < δ)
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {𝒯z : EuclideanSpace ℝ (Fin 2) → Set (Set (EuclideanSpace ℝ (Fin 2)))}
    {η : ℝ}
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hXy_sub : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ)
    (hTubes : ∀ z ∈ productLikeIncidenceSet Y X,
      IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ s (δ ^ (-η)) (𝒯z z) ∧
        ∀ T ∈ 𝒯z z, z ∈ T) :
    Bornology.IsBounded
      (productLikeAppendixDyadicTubeParameterSet δ
        (⋃ z ∈ productLikeIncidenceSet Y X, 𝒯z z)) := by
  let 𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
    ⋃ z ∈ productLikeIncidenceSet Y X, 𝒯z z
  let P := productLikeAppendixDyadicTubeParameterSet δ 𝒯
  have h_main : ∀ p ∈ P,
      p 0 ∈ Set.Icc (-1 - δ) (1 + δ) ∧ p 1 ∈ Set.Icc (-1 - 2 * δ) (2 + 2 * δ) := by
    intro p hp
    simp only [P, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion] at hp
    rcases hp with ⟨Q, hQ, hpQ⟩
    rcases hQ with ⟨T, hT𝒯, rfl⟩
    simp only [𝒯, Set.mem_iUnion] at hT𝒯
    rcases hT𝒯 with ⟨z, hz, hT⟩
    have hz_simp : z 0 ∈ X (z 1) ∧ z 1 ∈ Y := by
      simpa [productLikeIncidenceSet, Set.mem_iUnion] using hz
    have hzY : z 1 ∈ Y := hz_simp.2
    have hzX : z 0 ∈ X (z 1) := hz_simp.1
    have hz1 : 0 ≤ z 1 := (hY_sub hzY).2.1
    have hz2 : z 1 ≤ 1 := (hY_sub hzY).2.2
    have hz0_grid : z 0 ∈ productLikeUnitGrid δ := hXy_sub (z 1) hzY hzX
    have hz01 : 0 ≤ z 0 := hz0_grid.2.1
    have hz02 : z 0 ≤ 1 := hz0_grid.2.2
    let Q := productLikeAppendixDyadicTubeCanonicalParameterCube δ T
    have hT_tube : T ∈ appendixDyadicTubes δ :=
      (hTubes z hz).1.1 hT
    have hzT : z ∈ T := (hTubes z hz).2 T hT
    have hQ_correct := ProductLikeIncidence.DualityBridge.canonical_cube_correct hT_tube
    have hQ_dyadic : Q ∈ dyadicCubes 2 δ := hQ_correct.1.1
    have hQ_strip : (Q ∩ appendixParameterStrip).Nonempty := hQ_correct.1.2
    rcases hQ_strip with ⟨q, hqQ, hq_strip⟩
    have hq0 : q 0 ∈ Set.Icc (-1 : ℝ) 1 := hq_strip
    have hz_in_dual : z ∈ appendixDualOfParameterSet Q := by
      rw [hQ_correct.2] <;> exact hzT
    rcases hz_in_dual with ⟨p0, hp0Q, hline⟩
    have hline' : z 0 = p0 0 * z 1 + p0 1 := by
      simpa [appendixDualLineMap, appendixDualLine] using hline
    rcases hQ_dyadic with ⟨k, hQk⟩
    have h_in_Q : ∀ (x : EuclideanSpace ℝ (Fin 2)), x ∈ Q →
        x 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) ∧
        x 1 ∈ Set.Ico (δ * (k 1 : ℝ)) (δ * ((k 1 : ℝ) + 1)) := by
      intro x hx
      rw [hQk] at hx
      exact ⟨hx 0, hx 1⟩
    have h_p := h_in_Q p hpQ
    have h_p0 := h_in_Q p0 hp0Q
    have h_q := h_in_Q q hqQ
    have h_p0_low : -1 - δ ≤ p 0 := by
      have h1 : δ * (k 0 : ℝ) ≤ p 0 := h_p.1.1
      have h2 : q 0 < δ * ((k 0 : ℝ) + 1) := h_q.1.2
      nlinarith [hq0.1]
    have h_p0_high : p 0 ≤ 1 + δ := by
      have h1 : p 0 < δ * ((k 0 : ℝ) + 1) := h_p.1.2
      have h2 : δ * (k 0 : ℝ) ≤ q 0 := h_q.1.1
      nlinarith [hq0.2]
    have h_p00_low : -1 - δ ≤ p0 0 := by
      have h1 : δ * (k 0 : ℝ) ≤ p0 0 := h_p0.1.1
      have h2 : q 0 < δ * ((k 0 : ℝ) + 1) := h_q.1.2
      nlinarith [hq0.1]
    have h_p00_high : p0 0 ≤ 1 + δ := by
      have h1 : p0 0 < δ * ((k 0 : ℝ) + 1) := h_p0.1.2
      have h2 : δ * (k 0 : ℝ) ≤ q 0 := h_q.1.1
      nlinarith [hq0.2]
    have h_p01_low : -1 - δ ≤ p0 1 := by
      have h_eq : p0 1 = z 0 - p0 0 * z 1 := by linarith [hline']
      rw [h_eq]
      by_cases h : 0 ≤ p0 0
      · nlinarith
      · have h' : p0 0 ≤ 0 := by linarith
        nlinarith [mul_nonpos_of_nonpos_of_nonneg h' hz1]
    have h_p01_high : p0 1 ≤ 2 + δ := by
      have h_eq : p0 1 = z 0 - p0 0 * z 1 := by linarith [hline']
      rw [h_eq]
      nlinarith
    have h_p1_lo : δ * (k 1 : ℝ) ≤ p 1 := h_p.2.1
    have h_p01_hi : p0 1 < δ * ((k 1 : ℝ) + 1) := h_p0.2.2
    have h_p1_low : -1 - 2 * δ ≤ p 1 := by nlinarith
    have h_p_hi : p 1 < δ * ((k 1 : ℝ) + 1) := h_p.2.2
    have h_p01_lo2 : δ * (k 1 : ℝ) ≤ p0 1 := h_p0.2.1
    have h_p1_high : p 1 ≤ 2 + 2 * δ := by nlinarith
    exact ⟨⟨h_p0_low, h_p0_high⟩, ⟨h_p1_low, h_p1_high⟩⟩
  let R : ℝ := Real.sqrt ((1 + δ) ^ 2 + (2 + 2 * δ) ^ 2) + 1
  have hR_nonneg : 0 ≤ R := by positivity
  have h_norm : ∀ p ∈ P, ‖p‖ ≤ R := by
    intro p hp
    have h_coords := h_main p hp
    have h1 : |p 0| ≤ 1 + δ := by
      rw [abs_le] <;> constructor <;> linarith [h_coords.1.1, h_coords.1.2]
    have h2 : |p 1| ≤ 2 + 2 * δ := by
      rw [abs_le] <;> constructor <;> linarith [h_coords.2.1, h_coords.2.2]
    have h3 : ‖p‖ = Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2) := by
      simpa [EuclideanSpace.norm_eq, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] using rfl
    rw [h3]
    have h4 : (p 0) ^ 2 + (p 1) ^ 2 ≤ (1 + δ) ^ 2 + (2 + 2 * δ) ^ 2 := by
      nlinarith [abs_le.mp h1, abs_le.mp h2]
    have h5 : Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2) ≤
        Real.sqrt ((1 + δ) ^ 2 + (2 + 2 * δ) ^ 2) := Real.sqrt_le_sqrt h4
    have h6 : Real.sqrt ((1 + δ) ^ 2 + (2 + 2 * δ) ^ 2) ≤ R := by
      dsimp only [R]; linarith
    exact h5.trans h6
  exact Metric.isBounded_iff.mpr ⟨2 * R, fun x hx y hy => by
    have hx' : ‖x‖ ≤ R := h_norm x hx
    have hy' : ‖y‖ ≤ R := h_norm y hy
    have h : dist x y ≤ ‖x‖ + ‖y‖ := by simpa [dist_eq_norm] using norm_sub_le x y
    linarith⟩

end ProductLikeIncidence.ProductReduction
