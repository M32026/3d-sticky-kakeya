import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanAffineHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

/-!
# Property transfer helpers for WZ1 wide fixed-cell normalization

Standalone lemmas for transferring Frostman, separation, uniform density,
and related properties under scaling and translation.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The constant comparison needed when contracting a Frostman estimate:
`δ^(-3λ/4) / m ≤ (mδ)^(-λ)` follows from `δ^(λ/4) ≤ m^(1-λ)`. -/
lemma frostman_contraction_constant_ok
    {delta m lambda : ℝ}
    (hdelta : 0 < delta) (_hdelta_one : delta ≤ 1)
    (hm : 0 < m) (_hm_le_one : m ≤ 1)
    (_hlambda_pos : 0 < lambda) (_hlambda_le_one : lambda ≤ 1)
    (hsmall : Real.rpow delta (lambda / 4) ≤ Real.rpow m (1 - lambda)) :
    Kakeya.realRpowENN delta (-(3 * lambda / 4)) / ENNReal.ofReal m ≤
    Kakeya.realRpowENN (m * delta) (-lambda) := by
  have h2 : (1 - lambda : ℝ) = (1 : ℝ) + (-lambda) := by ring
  have h_add1 : Real.rpow m ((1 : ℝ) + (-lambda)) =
      Real.rpow m (1 : ℝ) * Real.rpow m (-lambda) :=
    Real.rpow_add hm (1 : ℝ) (-lambda)
  have h1 : Real.rpow m (1 - lambda) = m * Real.rpow m (-lambda) := by
    rw [h2]
    exact h_add1.trans (by simp)
  have h_small' : Real.rpow delta (lambda / 4) ≤ m * Real.rpow m (-lambda) := by
    rw [h1] at hsmall
    exact hsmall
  have h_mul : Real.rpow (m * delta) (-lambda) =
      Real.rpow m (-lambda) * Real.rpow delta (-lambda) := by
    have h : (m * delta) ^ (-lambda) = m ^ (-lambda) * delta ^ (-lambda) :=
      Real.mul_rpow hm.le hdelta.le
    exact h
  have h_exp3 : (-(3 * lambda / 4) : ℝ) = (-lambda) + (lambda / 4) := by ring
  have h_add2 : Real.rpow delta ((-lambda) + (lambda / 4)) =
      Real.rpow delta (-lambda) * Real.rpow delta (lambda / 4) :=
    Real.rpow_add hdelta (-lambda) (lambda / 4)
  have h3 : Real.rpow delta (-(3 * lambda / 4)) =
      Real.rpow delta (-lambda) * Real.rpow delta (lambda / 4) := by
    rw [h_exp3]
    exact h_add2
  have h_pos : 0 ≤ Real.rpow delta (-lambda) := Real.rpow_nonneg hdelta.le _
  have h5 : Real.rpow delta (lambda / 4) / m ≤ Real.rpow m (-lambda) := by
    calc
      Real.rpow delta (lambda / 4) / m
        ≤ (m * Real.rpow m (-lambda)) / m := by gcongr
      _ = Real.rpow m (-lambda) := by
        field_simp [hm.ne']
  have h_real : Real.rpow delta (-(3 * lambda / 4)) / m ≤
      Real.rpow (m * delta) (-lambda) := by
    calc
      Real.rpow delta (-(3 * lambda / 4)) / m
        = (Real.rpow delta (-lambda) * Real.rpow delta (lambda / 4)) / m := by rw [h3]
      _ = Real.rpow delta (-lambda) * (Real.rpow delta (lambda / 4) / m) := by ring
      _ ≤ Real.rpow delta (-lambda) * Real.rpow m (-lambda) := by gcongr
      _ = Real.rpow m (-lambda) * Real.rpow delta (-lambda) := by ring
      _ = Real.rpow (m * delta) (-lambda) := by rw [h_mul]
  have h_div : Kakeya.realRpowENN delta (-(3 * lambda / 4)) / ENNReal.ofReal m =
      ENNReal.ofReal (Real.rpow delta (-(3 * lambda / 4)) / m) := by
    rw [Kakeya.realRpowENN]
    rw [ENNReal.ofReal_div_of_pos hm]
  rw [h_div, Kakeya.realRpowENN]
  exact ENNReal.ofReal_le_ofReal h_real

/-- Weaken the constant in a Frostman estimate. -/
lemma DiscreteSet.IsFrostman.mono_const
    {n : ℕ} {E : DiscreteSet n} {delta s : ℝ} {C C' : ENNReal}
    (h : E.IsFrostman delta s C) (hle : C ≤ C') :
    E.IsFrostman delta s C' := by
  intro x r hδ hr
  have h' := h x r hδ hr
  exact h'.trans (by gcongr)

/-- Frostman transfer for a set under scaling by `scale`, with lower
Lipschitz factor `m ≤ scale`. -/
lemma frostman_transfer_scaling
    {E : DiscreteSet 2} {delta scale m lambda : ℝ}
    (hFrost : E.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-(3 * lambda / 4))))
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hscale_pos : 0 < scale)
    (hm_pos : 0 < m) (hm_le_scale : m ≤ scale) (hm_le_one : m ≤ 1)
    (hlambda_pos : 0 < lambda) (hlambda_le_one : lambda ≤ 1)
    (hsmall : Real.rpow delta (lambda / 4) ≤ Real.rpow m (1 - lambda)) :
    DiscreteSet.IsFrostman (E.image (fun x : Point2 => scale • x)) (m * delta) 1
        (Kakeya.realRpowENN (m * delta) (-lambda)) := by
  let f : Point2 ≃ₗ[ℝ] Point2 :=
    LinearEquiv.smulOfNeZero ℝ Point2 scale hscale_pos.ne'
  have hLower : ∀ (x : Point2), m * ‖x‖ ≤ ‖f x‖ := by
    intro x
    have h_smul : ‖scale • x‖ = |scale| * ‖x‖ := norm_smul scale x
    have h_abs : |scale| = scale := abs_of_pos hscale_pos
    have h : ‖f x‖ = scale * ‖x‖ := by
      simp [f, LinearEquiv.smulOfNeZero_apply, h_smul, h_abs]
    rw [h]
    exact mul_le_mul_of_nonneg_right hm_le_scale (norm_nonneg x)
  have h_exp : (-(3 * lambda / 4) : ℝ) ≤ 0 := by linarith
  have h_rpow : Real.rpow delta 0 ≤ Real.rpow delta (-(3 * lambda / 4)) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one h_exp
  have hconstant_real : 1 ≤ Real.rpow delta (-(3 * lambda / 4)) := by
    simpa using h_rpow
  have hconstant : 1 ≤ Kakeya.realRpowENN delta (-(3 * lambda / 4)) := by
    rw [Kakeya.realRpowENN]
    exact ENNReal.one_le_ofReal.mpr hconstant_real
  have h_ok := frostman_contraction_constant_ok
    hdelta_pos hdelta_one hm_pos hm_le_one hlambda_pos hlambda_le_one hsmall
  have h_main : DiscreteSet.IsFrostman (E.image f) (m * delta) 1
      (Kakeya.realRpowENN delta (-(3 * lambda / 4)) / ENNReal.ofReal m) :=
    DiscreteSet.isFrostman_map_contraction_s1 hFrost hconstant hm_pos hLower
  exact h_main.mono_const h_ok

/-- Translation preserves Frostman estimates. -/
lemma DiscreteSet.isFrostman_translate
    {E : DiscreteSet 2} {t : Point2} {delta exponent : ℝ} {constant : ENNReal}
    (h : E.IsFrostman delta exponent constant) :
    DiscreteSet.IsFrostman (E.image (fun x : Point2 => x + t)) delta exponent constant :=
  let f : Point2 → Point2 := fun x => x + t
  let inverse : Point2 → Point2 := fun x => x - t
  DiscreteSet.isFrostman_map_expansive (f := f) (inverse := inverse) h
    (fun x => by
      have h_eq : (x + t) - t = x := by abel
      exact h_eq)
    (fun x y => by
      have h_dist : dist (x - t) (y - t) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        <;> abel
      exact h_dist.le)

/-- General transfer of `WZ1UniformHypergraphDensity` under injective
coordinate maps. -/
lemma WZ1UniformHypergraphDensity.map_injective
    {k : ℕ} {α β : Type*} [DecidableEq α] [DecidableEq β]
    {c : ENNReal} {A : Fin k → Finset α} {H : Finset (Fin k → α)}
    (h : WZ1UniformHypergraphDensity c A H)
    (f : Fin k → α → β) (hf_inj : ∀ i, Function.Injective (f i)) :
    WZ1UniformHypergraphDensity c
      (fun i => (A i).image (f i))
      (H.image (fun edge i => f i (edge i))) := by
  let φ : (Fin k → α) → (Fin k → β) := fun edge i => f i (edge i)
  have hφ_inj : Function.Injective φ := by
    intro edge1 edge2 h
    ext i
    exact hf_inj i (congr_fun h i)
  have h1 : ∀ edge' ∈ H.image φ, ∀ i, edge' i ∈ (A i).image (f i) := by
    intro edge' hedge' i
    rcases Finset.mem_image.mp hedge' with ⟨edge, hedge, rfl⟩
    exact Finset.mem_image.mpr ⟨edge i, h.1 edge hedge i, rfl⟩
  have h2 : ∀ edge' ∈ H.image φ, ∀ I : Finset (Fin k),
      c * wz1VertexCardProduct (fun i => (A i).image (f i)) (Finset.univ \ I) ≤
        ((wz1HypergraphFiber (H.image φ) I edge').card : ENNReal) := by
    intro edge' hedge' I
    rcases Finset.mem_image.mp hedge' with ⟨edge, hedge, rfl⟩
    have hfiber : wz1HypergraphFiber (H.image φ) I (φ edge) =
        (wz1HypergraphFiber H I edge).image φ := by
      ext other'
      simp only [wz1HypergraphFiber, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨other, hother, rfl⟩, hcond⟩
        refine ⟨other, ⟨hother, ?_⟩, rfl⟩
        intro i hi
        exact hf_inj i (hcond i hi)
      · rintro ⟨other, ⟨hother, hcond⟩, rfl⟩
        refine ⟨⟨other, hother, rfl⟩, ?_⟩
        intro i hi
        exact congr_arg (f i) (hcond i hi)
    rw [hfiber]
    have hcard : ((wz1HypergraphFiber H I edge).image φ).card =
        (wz1HypergraphFiber H I edge).card :=
      Finset.card_image_of_injective _ hφ_inj
    rw [hcard]
    have hprod : wz1VertexCardProduct (fun i => (A i).image (f i)) (Finset.univ \ I) =
        wz1VertexCardProduct A (Finset.univ \ I) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [Finset.card_image_of_injective _ (hf_inj i)]
    rw [hprod]
    exact h.2 edge hedge I
  exact ⟨h1, h2⟩

/-- Transfer of `WZ1UniformTripleDensity` under injective maps on each
vertex class. -/
lemma WZ1UniformTripleDensity.map_injective
    {c : ENNReal} {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (h : WZ1UniformTripleDensity c F G₁ G₂ H)
    (fF fG₁ fG₂ : Point2 → Point2)
    (hfF_inj : Function.Injective fF)
    (hfG₁_inj : Function.Injective fG₁)
    (hfG₂_inj : Function.Injective fG₂) :
    WZ1UniformTripleDensity c
      (F.image fF) (G₁.image fG₁) (G₂.image fG₂)
      (H.image (fun edge => (fF edge.1, fG₁ edge.2.1, fG₂ edge.2.2))) := by
  let fH : Point2 × Point2 × Point2 → Point2 × Point2 × Point2 :=
    fun edge => (fF edge.1, fG₁ edge.2.1, fG₂ edge.2.2)
  let f : Fin 3 → Point2 → Point2 := fun i =>
    if i = 0 then fF else if i = 1 then fG₁ else fG₂
  have hf0 : f 0 = fF := by simp [f]
  have hf1 : f 1 = fG₁ := by simp [f]
  have hf2 : f 2 = fG₂ := by simp [f]
  have hf_inj : ∀ i, Function.Injective (f i) := by
    intro i
    fin_cases i <;> simp [hf0, hf1, hf2] <;> tauto
  let φ : (Fin 3 → Point2) → (Fin 3 → Point2) := fun edge i => f i (edge i)
  have h_comm : φ ∘ wz1TripleCoordinate = wz1TripleCoordinate ∘ fH := by
    funext edge
    ext i
    fin_cases i <;> simp [φ, wz1TripleCoordinate, fH, hf0, hf1, hf2] <;> rfl
  have h_enc : (wz1EncodeTriples H).image φ = wz1EncodeTriples (H.image fH) := by
    have h1 : (wz1EncodeTriples H).image φ = H.image (φ ∘ wz1TripleCoordinate) := by
      rw [wz1EncodeTriples, Finset.image_image] <;> rfl
    have h2 : wz1EncodeTriples (H.image fH) = H.image (wz1TripleCoordinate ∘ fH) := by
      rw [wz1EncodeTriples, Finset.image_image] <;> rfl
    rw [h1, h2, h_comm]
  have h_verts : (fun i : Fin 3 => (wz1TripleVertexClasses F G₁ G₂ i).image (f i)) =
      wz1TripleVertexClasses (F.image fF) (G₁.image fG₁) (G₂.image fG₂) := by
    funext i
    fin_cases i <;> rfl
  have h_main : WZ1UniformHypergraphDensity c
      (wz1TripleVertexClasses (F.image fF) (G₁.image fG₁) (G₂.image fG₂))
      (wz1EncodeTriples (H.image fH)) := by
    have h0 := WZ1UniformHypergraphDensity.map_injective h.2 f hf_inj
    rw [h_verts, h_enc] at h0
    exact h0
  have h_nonempty : (H.image fH).Nonempty := h.1.image _
  exact ⟨h_nonempty, h_main⟩

end Kakeya.Assouad
