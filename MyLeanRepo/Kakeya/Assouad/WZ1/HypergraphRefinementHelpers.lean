import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFinalStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

/-!
# Helper lemmas for applying hypergraph refinement to tripartite graphs

Provides encoding/decoding between `Point2 × Point2 × Point2` and `Fin 3 → Point2`,
and a convenience wrapper around `WZ1TripartiteHypergraphRefinementStatement`.
-/

namespace Kakeya.Assouad

open scoped ENNReal
open Classical

/-- `wz1TripleCoordinate` is injective: distinct triples give distinct functions. -/
lemma wz1TripleCoordinate_injective :
    Function.Injective (wz1TripleCoordinate : (Point2 × Point2 × Point2) → (Fin 3 → Point2)) := by
  intro x y h
  have h0 : x.1 = y.1 := by
    have h0' := congr_fun h 0
    simpa [wz1TripleCoordinate] using h0'
  have h1 : x.2.1 = y.2.1 := by
    have h1' := congr_fun h 1
    simpa [wz1TripleCoordinate] using h1'
  have h2 : x.2.2 = y.2.2 := by
    have h2' := congr_fun h 2
    simpa [wz1TripleCoordinate] using h2'
  simp [Prod.ext_iff] <;> tauto

/-- Encoding triples preserves cardinality. -/
lemma wz1HypergraphEncodeTriples_card (H : Finset (Point2 × Point2 × Point2)) :
    (wz1EncodeTriples H).card = H.card := by
  rw [wz1EncodeTriples, Finset.card_image_of_injective _ wz1TripleCoordinate_injective]

/-- Decode a function edge back to a triple. -/
def wz1HypergraphDecodeTriple (f : Fin 3 → Point2) : Point2 × Point2 × Point2 :=
  (f 0, f 1, f 2)

/-- Decoding is the left inverse of encoding. -/
lemma wz1HypergraphDecodeEncode (t : Point2 × Point2 × Point2) :
    wz1HypergraphDecodeTriple (wz1TripleCoordinate t) = t := by
  simp [wz1HypergraphDecodeTriple, wz1TripleCoordinate, Prod.ext_iff] <;> tauto

/-- Encoding is the left inverse of decoding (for functions in the image). -/
lemma wz1HypergraphEncodeDecode (f : Fin 3 → Point2) :
    wz1TripleCoordinate (wz1HypergraphDecodeTriple f) = f := by
  funext i
  fin_cases i <;> simp [wz1HypergraphDecodeTriple, wz1TripleCoordinate] <;> rfl

/--
Apply the tripartite hypergraph refinement lemma to a graph in triple
representation, and decode the result back to triples.

Given a supported graph `H` and `0 < ε < 1`, produces `H' ⊆ H` with
`(1-ε) * |H| ≤ |H'|` and uniform density
`c = ε/8 * |H| / (|F| * |G₁| * |G₂|)`.
-/
lemma tripartite_refinement_apply
    {hRef : WZ1TripartiteHypergraphRefinementStatement}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hsupport : ∀ h ∈ H, h.1 ∈ F ∧ h.2.1 ∈ G₁ ∧ h.2.2 ∈ G₂)
    (hH_nonempty : H.Nonempty)
    {epsilon : ENNReal} (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1) :
    ∃ (H' : Finset (Point2 × Point2 × Point2)),
      H' ⊆ H ∧
      (1 - epsilon) * (H.card : ENNReal) ≤ (H'.card : ENNReal) ∧
      WZ1UniformTripleDensity
        ((epsilon / (2 : ENNReal) ^ (3 : ℕ)) *
          ((H.card : ENNReal) / (F.enncard * G₁.enncard * G₂.enncard)))
        F G₁ G₂ H' := by
  let A : Fin 3 → DiscreteSet 2 := wz1TripleVertexClasses F G₁ G₂
  let H_enc : Finset (Fin 3 → Point2) := wz1EncodeTriples H
  have h_support_enc : ∀ edge ∈ H_enc, ∀ i : Fin 3, edge i ∈ A i := by
    intro edge hedge i
    rcases Finset.mem_image.mp hedge with ⟨t, ht, rfl⟩
    have h_t_support := hsupport t ht
    fin_cases i <;> simp [A, wz1TripleVertexClasses, h_t_support] <;> tauto
  rcases hRef A H_enc h_support_enc epsilon hepsilon_pos hepsilon_lt_one with
    ⟨H'_enc, h_subset, h_card, h_uniform⟩
  let H' : Finset (Point2 × Point2 × Point2) :=
    H'_enc.image wz1HypergraphDecodeTriple
  have h_H'_subset : H' ⊆ H := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨f, hf, rfl⟩
    have h_f_in_H_enc : f ∈ H_enc := h_subset hf
    rcases Finset.mem_image.mp h_f_in_H_enc with ⟨t', ht', h_eq⟩
    have h_f_eq : f = wz1TripleCoordinate t' := h_eq.symm
    rw [h_f_eq]
    rw [wz1HypergraphDecodeEncode]
    exact ht'
  have h_inj_on : Set.InjOn wz1HypergraphDecodeTriple (H'_enc : Set (Fin 3 → Point2)) := by
    intro f _ g _ h
    have h1 : wz1TripleCoordinate (wz1HypergraphDecodeTriple f) = wz1TripleCoordinate (wz1HypergraphDecodeTriple g) := by
      rw [h]
    simpa [wz1HypergraphEncodeDecode] using h1
  have h_card' : H'.card = H'_enc.card := by
    rw [Finset.card_image_of_injOn h_inj_on]
  have h_enc_eq : wz1EncodeTriples H' = H'_enc := by
    ext f
    simp only [wz1EncodeTriples, Finset.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases Finset.mem_image.mp ht with ⟨g, hg, h_eq⟩
      have h_t : wz1HypergraphDecodeTriple g = t := h_eq
      rw [← h_t, wz1HypergraphEncodeDecode]
      exact hg
    · intro hf
      exact ⟨wz1HypergraphDecodeTriple f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, wz1HypergraphEncodeDecode f⟩
  have h_vertex_product : wz1VertexCardProduct A Finset.univ = F.enncard * G₁.enncard * G₂.enncard := by
    have h_univ : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [h_univ]
    simp [wz1VertexCardProduct, A, wz1TripleVertexClasses, Finset.prod_insert, DiscreteSet.enncard]
    <;> ring
  rcases h_uniform with ⟨h_support_uniform, h_density⟩
  have h_H'_enc_nonempty : H'_enc.Nonempty := by
    have h1 : (0 : ENNReal) < 1 - epsilon :=
      tsub_pos_of_lt hepsilon_lt_one
    have h2 : (0 : ENNReal) < (H_enc.card : ENNReal) := by
      have h21 : 0 < H.card := hH_nonempty.card_pos
      have h22 : H_enc.card = H.card := by exact_mod_cast wz1HypergraphEncodeTriples_card H
      rw [h22]
      exact_mod_cast h21
    have h3 : (0 : ENNReal) < (1 - epsilon) * (H_enc.card : ENNReal) := by
      exact ENNReal.mul_pos (ne_of_gt h1) (ne_of_gt h2)
    have h4 : (0 : ENNReal) < (H'_enc.card : ENNReal) := h3.trans_le h_card
    have h5 : 0 < H'_enc.card := by exact_mod_cast h4
    exact Finset.card_pos.mp h5
  have h_H'_nonempty : H'.Nonempty := by
    rcases h_H'_enc_nonempty with ⟨f, hf⟩
    exact ⟨wz1HypergraphDecodeTriple f, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩
  have h_card_eq : (H_enc.card : ENNReal) = (H.card : ENNReal) := by
    exact_mod_cast wz1HypergraphEncodeTriples_card H
  have h_density2 : WZ1UniformHypergraphDensity
        ((epsilon / (2 : ENNReal) ^ (3 : ℕ)) *
          ((H.card : ENNReal) / (F.enncard * G₁.enncard * G₂.enncard)))
        A H'_enc := by
    have h_rewrite : ((epsilon / (2 : ENNReal) ^ (3 : ℕ)) *
          ((H_enc.card : ENNReal) / wz1VertexCardProduct A Finset.univ)) =
        ((epsilon / (2 : ENNReal) ^ (3 : ℕ)) *
          ((H.card : ENNReal) / (F.enncard * G₁.enncard * G₂.enncard))) := by
      rw [h_card_eq, h_vertex_product]
    have h_density' : ∀ edge ∈ H'_enc, ∀ (I : Finset (Fin 3)),
          ((epsilon / (2 : ENNReal) ^ (3 : ℕ)) *
            ((H.card : ENNReal) / (F.enncard * G₁.enncard * G₂.enncard))) *
          wz1VertexCardProduct A (Finset.univ \ I) ≤
          (↑(wz1HypergraphFiber H'_enc I edge).card) := by
      intro edge hedge I
      have h_old := h_density edge hedge I
      rw [h_rewrite] at *
      exact h_old
    exact ⟨h_support_uniform, h_density'⟩
  have h_density' : WZ1UniformHypergraphDensity
        ((epsilon / (2 : ENNReal) ^ (3 : ℕ)) *
          ((H.card : ENNReal) / (F.enncard * G₁.enncard * G₂.enncard)))
        A (wz1EncodeTriples H') := by
    rw [h_enc_eq]
    exact h_density2
  have h_card_final : (1 - epsilon) * (H.card : ENNReal) ≤ (H'.card : ENNReal) := by
    have h_card_enc : (1 - epsilon) * (H_enc.card : ENNReal) ≤ (H'_enc.card : ENNReal) := h_card
    have h9 : (H'.card : ENNReal) = (H'_enc.card : ENNReal) := by exact_mod_cast h_card'
    rw [h_card_eq] at h_card_enc
    rw [h9]
    exact h_card_enc
  exact ⟨H', h_H'_subset, h_card_final, ⟨h_H'_nonempty, h_density'⟩⟩


/-- Numerical bound: if `δ^η < 1/4`, then `δ^{36η} ≤ 1/(32·82^6)`. -/
lemma delta_36eta_bound
    {delta eta : ℝ} (hdelta : 0 < delta) (heta : 0 < eta)
    (hsmall : Real.rpow delta eta < 1 / 4) :
    Real.rpow delta (36 * eta) ≤ 1 / (32 * (82 : ℝ)^6) := by
  have h21 : Real.rpow delta (eta * (36 : ℝ)) = (Real.rpow delta eta) ^ (36 : ℝ) :=
    Real.rpow_mul hdelta.le eta (36 : ℝ)
  have h22 : eta * (36 : ℝ) = 36 * eta := by ring
  have h1 : Real.rpow delta (36 * eta) = (Real.rpow delta eta) ^ 36 := by
    rw [← h22, h21] <;> norm_cast
  rw [h1]
  have h_nonneg : 0 ≤ Real.rpow delta eta := Real.rpow_nonneg hdelta.le eta
  have h_le : Real.rpow delta eta ≤ 1 / 4 := hsmall.le
  have h2 : (Real.rpow delta eta) ^ 36 ≤ (1 / 4 : ℝ) ^ 36 :=
    pow_le_pow_left₀ h_nonneg h_le 36
  have h3 : (1 / 4 : ℝ) ^ 36 ≤ 1 / (32 * (82 : ℝ)^6) := by norm_num
  exact h2.trans h3

/--
Lower bound on the refined hypergraph density.
-/
lemma refined_density_lower
    {delta eta : ℝ} (hdelta : 0 < delta) (heta : 0 < eta)
    (hdelta_small : Real.rpow delta eta < 1 / 4)
    {H_scaled : Finset (Point2 × Point2 × Point2)}
    {F_norm G1_norm G2_norm : DiscreteSet 2}
    (hH_lower : (H_scaled.card : ENNReal) ≥
        Kakeya.realRpowENN delta (61 * eta - 3) / ((2 : ENNReal) * (82 : ENNReal)^6))
    (hF_upper : F_norm.enncard ≤ Kakeya.realRpowENN delta (-1 - eta))
    (hG1_upper : G1_norm.enncard ≤ Kakeya.realRpowENN delta (-1 - eta))
    (hG2_upper : G2_norm.enncard ≤ Kakeya.realRpowENN delta (-1 - eta)) :
    Kakeya.realRpowENN delta (100 * eta) ≤
      ((1 / 16 : ENNReal) * (H_scaled.card : ENNReal) /
       (F_norm.enncard * G1_norm.enncard * G2_norm.enncard)) := by
  set D : ENNReal := F_norm.enncard * G1_norm.enncard * G2_norm.enncard with hD
  set Y : ENNReal := (2 : ENNReal) * (82 : ENNReal)^6 with hY
  set Z : ENNReal := Kakeya.realRpowENN delta (-3 - 3 * eta) with hZ
  have hD_upper : D ≤ Z := by
    have h11 : F_norm.enncard * G1_norm.enncard ≤
        Kakeya.realRpowENN delta (-1 - eta) * Kakeya.realRpowENN delta (-1 - eta) :=
      mul_le_mul hF_upper hG1_upper (by positivity) (by positivity)
    have h1 : D ≤ Kakeya.realRpowENN delta (-1 - eta) * Kakeya.realRpowENN delta (-1 - eta) *
           Kakeya.realRpowENN delta (-1 - eta) :=
      mul_le_mul h11 hG2_upper (by positivity) (by positivity)
    have h2 : Kakeya.realRpowENN delta (-1 - eta) * Kakeya.realRpowENN delta (-1 - eta) *
           Kakeya.realRpowENN delta (-1 - eta) = Z := by
      simp only [hZ]
      have h21 : Kakeya.realRpowENN delta (-1 - eta) * Kakeya.realRpowENN delta (-1 - eta) =
          Kakeya.realRpowENN delta ((-1 - eta) + (-1 - eta)) :=
        (realRpowENN_add hdelta (-1 - eta) (-1 - eta)).symm
      have h22 : Kakeya.realRpowENN delta ((-1 - eta) + (-1 - eta)) * Kakeya.realRpowENN delta (-1 - eta) =
          Kakeya.realRpowENN delta (((-1 - eta) + (-1 - eta)) + (-1 - eta)) :=
        (realRpowENN_add hdelta ((-1 - eta) + (-1 - eta)) (-1 - eta)).symm
      rw [h21, h22] <;> ring
    exact h1.trans_eq h2
  have h_antitone : (H_scaled.card : ENNReal) / D ≥ (H_scaled.card : ENNReal) / Z := by
    have h_inv : Z⁻¹ ≤ D⁻¹ := ENNReal.inv_le_inv.mpr hD_upper
    have h3 : (H_scaled.card : ENNReal) * Z⁻¹ ≤ (H_scaled.card : ENNReal) * D⁻¹ :=
      mul_le_mul_left' h_inv _
    simpa [div_eq_mul_inv] using h3
  have h_pos : 0 < Real.rpow delta (-3 - 3 * eta) := Real.rpow_pos_of_pos hdelta _
  have hZ_inv : Z⁻¹ = Kakeya.realRpowENN delta (3 + 3 * eta) := by
    simp only [hZ, Kakeya.realRpowENN]
    have h : (ENNReal.ofReal (Real.rpow delta (-3 - 3 * eta)))⁻¹ =
        ENNReal.ofReal ((Real.rpow delta (-3 - 3 * eta))⁻¹) :=
      (ENNReal.ofReal_inv_of_pos h_pos).symm
    rw [h]
    have h_pos2 : 0 < Real.rpow delta (3 + 3 * eta) := Real.rpow_pos_of_pos hdelta _
    have h21 : Real.rpow delta (-3 - 3 * eta) = (Real.rpow delta (3 + 3 * eta))⁻¹ := by
      have h22 : Real.rpow delta (-(3 + 3 * eta)) = (Real.rpow delta (3 + 3 * eta))⁻¹ :=
        Real.rpow_neg hdelta.le (3 + 3 * eta)
      have h23 : -(3 + 3 * eta) = -3 - 3 * eta := by ring
      rw [h23] at h22
      exact h22
    have h2 : (Real.rpow delta (-3 - 3 * eta))⁻¹ = Real.rpow delta (3 + 3 * eta) := by
      rw [h21, inv_inv] <;> positivity
    rw [h2]
  have h_step2 : (H_scaled.card : ENNReal) / Z ≥ Kakeya.realRpowENN delta (64 * eta) / Y := by
    calc
      (H_scaled.card : ENNReal) / Z
        ≥ (Kakeya.realRpowENN delta (61 * eta - 3) / Y) / Z := by gcongr
      _ = (Kakeya.realRpowENN delta (61 * eta - 3)) * Z⁻¹ / Y := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      _ = (Kakeya.realRpowENN delta (61 * eta - 3)) * Kakeya.realRpowENN delta (3 + 3 * eta) / Y := by
        rw [hZ_inv]
      _ = Kakeya.realRpowENN delta (64 * eta) / Y := by
        have h_exp : (61 * eta - 3) + (3 + 3 * eta) = 64 * eta := by ring
        have h_mul2 : Kakeya.realRpowENN delta (61 * eta - 3) * Kakeya.realRpowENN delta (3 + 3 * eta) =
            Kakeya.realRpowENN delta ((61 * eta - 3) + (3 + 3 * eta)) :=
          (realRpowENN_add hdelta (61 * eta - 3) (3 + 3 * eta)).symm
        rw [h_mul2, h_exp] <;> rfl
  have h_real : Real.rpow delta (36 * eta) ≤ 1 / (32 * (82 : ℝ)^6) :=
    delta_36eta_bound hdelta heta hdelta_small
  have h_enn : Kakeya.realRpowENN delta (36 * eta) ≤
      ((32 : ENNReal) * (82 : ENNReal)^6)⁻¹ := by
    have h3 : Kakeya.realRpowENN delta (36 * eta) ≤
        ENNReal.ofReal (1 / (32 * (82 : ℝ)^6)) := by
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_le_ofReal h_real
    have h4 : ENNReal.ofReal (1 / (32 * (82 : ℝ)^6)) =
        ((32 : ENNReal) * (82 : ENNReal)^6)⁻¹ := by
      have h_pos2 : (0 : ℝ) < 32 * (82 : ℝ)^6 := by norm_num
      have h5 : (1 / (32 * (82 : ℝ)^6)) = (32 * (82 : ℝ)^6)⁻¹ := by ring
      rw [h5, ENNReal.ofReal_inv_of_pos h_pos2] <;> simp
    exact h3.trans_eq h4
  have h_exp : 64 * eta + 36 * eta = 100 * eta := by ring
  have h_mul : Kakeya.realRpowENN delta (64 * eta) * Kakeya.realRpowENN delta (36 * eta) =
      Kakeya.realRpowENN delta (100 * eta) := by
    have h_mul2 : Kakeya.realRpowENN delta (64 * eta) * Kakeya.realRpowENN delta (36 * eta) =
        Kakeya.realRpowENN delta (64 * eta + 36 * eta) :=
      (realRpowENN_add hdelta (64 * eta) (36 * eta)).symm
    rw [h_mul2, h_exp]
  have h6 : (16 : ENNReal) * ((32 : ENNReal) * (82 : ENNReal)^6)⁻¹ = Y⁻¹ := by
    have h_pos1 : (0 : ℝ) < 32 * (82 : ℝ)^6 := by norm_num
    have h_pos2 : (0 : ℝ) < 2 * (82 : ℝ)^6 := by norm_num
    have h_real_eq : (16 : ℝ) * (32 * (82 : ℝ)^6)⁻¹ = (2 * (82 : ℝ)^6)⁻¹ := by
      field_simp <;> ring
    have h32 : (32 : ENNReal) * (82 : ENNReal)^6 = ENNReal.ofReal (32 * (82 : ℝ)^6) := by
      simp <;> norm_cast
    have h_left : ((16 : ENNReal) * ((32 : ENNReal) * (82 : ENNReal)^6)⁻¹) =
        ENNReal.ofReal ((16 : ℝ) * (32 * (82 : ℝ)^6)⁻¹) := by
      rw [h32]
      have h41 : (ENNReal.ofReal (32 * (82 : ℝ)^6))⁻¹ =
          ENNReal.ofReal ((32 * (82 : ℝ)^6)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos h_pos1).symm
      rw [h41]
      have h4 : ENNReal.ofReal ((16 : ℝ) * (32 * (82 : ℝ)^6)⁻¹) =
          (16 : ENNReal) * ENNReal.ofReal ((32 * (82 : ℝ)^6)⁻¹) := by
        simpa [ENNReal.ofReal_mul] using rfl
      exact h4.symm
    have hY' : Y = ENNReal.ofReal (2 * (82 : ℝ)^6) := by
      simp [hY] <;> norm_cast
    have h_right : Y⁻¹ = ENNReal.ofReal ((2 * (82 : ℝ)^6)⁻¹) := by
      rw [hY', ENNReal.ofReal_inv_of_pos h_pos2] <;> rfl
    rw [h_left, h_right, h_real_eq]
  have h5 : (16 : ENNReal) * Kakeya.realRpowENN delta (36 * eta) ≤ Y⁻¹ := by
    have h51 : (16 : ENNReal) * Kakeya.realRpowENN delta (36 * eta) ≤
        (16 : ENNReal) * ((32 : ENNReal) * (82 : ENNReal)^6)⁻¹ := by gcongr
    rw [h6] at h51
    exact h51
  have h_step3 : Kakeya.realRpowENN delta (64 * eta) / Y ≥
      (16 : ENNReal) * Kakeya.realRpowENN delta (100 * eta) := by
    rw [div_eq_mul_inv, ← h_mul]
    have h7 : Kakeya.realRpowENN delta (64 * eta) *
          ((16 : ENNReal) * Kakeya.realRpowENN delta (36 * eta)) ≤
        Kakeya.realRpowENN delta (64 * eta) * Y⁻¹ := mul_le_mul_left' h5 _
    have h8 : (16 : ENNReal) * (Kakeya.realRpowENN delta (64 * eta) * Kakeya.realRpowENN delta (36 * eta)) =
        Kakeya.realRpowENN delta (64 * eta) *
          ((16 : ENNReal) * Kakeya.realRpowENN delta (36 * eta)) := by ring
    rw [h8]
    exact h7
  have h_final : (H_scaled.card : ENNReal) / D ≥
      (16 : ENNReal) * Kakeya.realRpowENN delta (100 * eta) := by
    calc
      (H_scaled.card : ENNReal) / D
        ≥ (H_scaled.card : ENNReal) / Z := h_antitone
      _ ≥ Kakeya.realRpowENN delta (64 * eta) / Y := h_step2
      _ ≥ (16 : ENNReal) * Kakeya.realRpowENN delta (100 * eta) := h_step3
  have h9 : (1 / 16 : ENNReal) * (16 : ENNReal) = 1 := by
    have h10 : (1 / 16 : ENNReal) = (16 : ENNReal)⁻¹ := by simp
    rw [h10, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  calc
    ((1 / 16 : ENNReal) * (H_scaled.card : ENNReal)) / D
      = (1 / 16 : ENNReal) * ((H_scaled.card : ENNReal) / D) := by rw [mul_div_assoc]
    _ ≥ (1 / 16 : ENNReal) * ((16 : ENNReal) * Kakeya.realRpowENN delta (100 * eta)) := by gcongr
    _ = ((1 / 16 : ENNReal) * (16 : ENNReal)) * Kakeya.realRpowENN delta (100 * eta) := by rw [mul_assoc]
    _ = Kakeya.realRpowENN delta (100 * eta) := by rw [h9, one_mul]


end Kakeya.Assouad
