module

public import MyLeanRepo.robust_kaufman_projection.Base

@[expose] public section

/-!
# Refinement energy bound

This module proves the key energy inequality used in the Kaufman projection
argument (OS, Lemma "projections", Appendix A).

If μ' is the normalized restriction of μ to a subset of relative mass r,
then the Riesz s-energy satisfies I_s(μ') ≤ r^{-2} · I_s(μ).

For finite sets S' ⊆ S with uniform measures, this becomes:
I_s(μ') ≤ (|S|/|S'|)^2 · I_s(μ).

## Main results
- `energy_bound_of_le_smul`: general measure-theoretic bound
- `refinement_energy_bound`: Finset version
- `refinement_projected_energy_bound`: projected version
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Measure

namespace RobustKaufmanProjection.Refinement

/--
Riesz s-energy of a measure μ on a metric space:
I_s(μ) = ∫∫ edist(x,y)^{-s} dμ(x) dμ(y).
-/
def rieszEnergy {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (s : ℝ) : ENNReal :=
  ∫⁻ (p : X × X), (edist p.1 p.2) ^ (-s) ∂(μ.prod μ)

/-- Riesz s-energy on the Euclidean plane. -/
abbrev planeEnergy (μ : Measure EuclideanPlane) (s : ℝ) : ENNReal :=
  rieszEnergy μ s

/--
Projected Riesz s-energy: the energy of the pushforward of μ under
the affine projection p ↦ p 0 - σ * p 1.
-/
def projectedEnergy (μ : Measure EuclideanPlane) (s σ : ℝ) : ENNReal :=
  rieszEnergy (Measure.map (fun p : EuclideanPlane => p 0 - σ * p 1) μ) s

/--
Product measure scaling lemma: if μ' ≤ c • μ, then
μ'.prod μ' ≤ c^2 • μ.prod μ.
-/
lemma prod_mono_smul {X : Type*} [MeasurableSpace X]
    {μ μ' : Measure X} [SFinite μ] [SFinite μ'] {c : ENNReal}
    (h : μ' ≤ c • μ) :
    μ'.prod μ' ≤ c ^ 2 • μ.prod μ := by
  rw [Measure.le_iff]
  intro A hA
  have hmeas : MeasurableSet A := hA
  have hfn : Measurable fun (x : X) => μ {y : X | (x, y) ∈ A} :=
    measurable_measure_prodMk_left hmeas
  have h1 : ∀ (x : X), μ' {y : X | (x, y) ∈ A} ≤ c * μ {y : X | (x, y) ∈ A} := by
    intro x
    exact h _
  calc
    (μ'.prod μ') A
      = ∫⁻ (x : X), μ' {y : X | (x, y) ∈ A} ∂μ' :=
        Measure.prod_apply hmeas
    _ ≤ ∫⁻ (x : X), c * μ {y : X | (x, y) ∈ A} ∂μ' :=
        lintegral_mono h1
    _ = c * ∫⁻ (x : X), μ {y : X | (x, y) ∈ A} ∂μ' :=
        lintegral_const_mul c hfn
    _ ≤ c * ∫⁻ (x : X), μ {y : X | (x, y) ∈ A} ∂(c • μ) := by
        gcongr
    _ = c * (c * ∫⁻ (x : X), μ {y : X | (x, y) ∈ A} ∂μ) := by
        rw [lintegral_smul_measure] <;> ring
    _ = c ^ 2 * (μ.prod μ) A := by
        have h_eq : (∫⁻ (x : X), μ {y : X | (x, y) ∈ A} ∂μ) =
            (∫⁻ (x : X), μ (Prod.mk x ⁻¹' A) ∂μ) := by
          congr with x <;> rfl
        rw [h_eq, Measure.prod_apply hmeas] <;> ring
    _ = (c ^ 2 • μ.prod μ) A := by
        rw [Measure.smul_apply] <;> rfl

/--
General energy refinement bound.

If μ' ≤ c • μ (as measures), then for any s:
I_s(μ') ≤ c^2 * I_s(μ).
-/
theorem energy_bound_of_le_smul {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ μ' : Measure X} [SFinite μ] [SFinite μ']
    {c : ENNReal} (h : μ' ≤ c • μ) {s : ℝ} :
    rieszEnergy μ' s ≤ c ^ 2 * rieszEnergy μ s := by
  have hprod : μ'.prod μ' ≤ c ^ 2 • μ.prod μ := prod_mono_smul h
  have h3 : ∫⁻ (p : X × X), (edist p.1 p.2) ^ (-s) ∂(μ'.prod μ') ≤
      ∫⁻ (p : X × X), (edist p.1 p.2) ^ (-s) ∂(c ^ 2 • μ.prod μ) :=
    lintegral_mono' hprod le_rfl
  rw [lintegral_smul_measure] at h3
  exact h3

/--
For finite sets S' ⊆ S, the uniform measure on S' is bounded by
(|S|/|S'|) times the uniform measure on S.
-/
lemma refinement_measure_le' {S S' : Finset EuclideanPlane}
    (hS'_sub : S' ⊆ S) (hS'_nonempty : S'.Nonempty) :
    (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set EuclideanPlane) ≤
    ((S.card : ENNReal) / (S'.card : ENNReal)) •
    ((S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane)) := by
  let c : ENNReal := (S.card : ENNReal) / (S'.card : ENNReal)
  have hS'_pos : (S'.card : ENNReal) ≠ 0 := by
    exact_mod_cast hS'_nonempty.card_pos.ne'
  have hS'_top : (S'.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hS_nonempty : S.Nonempty := hS'_nonempty.mono hS'_sub
  have hS_pos : (S.card : ENNReal) ≠ 0 := by
    have h : 0 < S.card := Finset.card_pos.mpr hS_nonempty
    exact_mod_cast h.ne'
  have hS_top : (S.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h1 : Measure.count.restrict (S' : Set EuclideanPlane) ≤
      Measure.count.restrict (S : Set EuclideanPlane) :=
    Measure.restrict_mono hS'_sub le_rfl
  have h21 : (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set EuclideanPlane) ≤
      (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane) :=
    smul_le_smul_left (S'.card : ENNReal)⁻¹ h1
  have h22 : (S'.card : ENNReal)⁻¹ = c * (S.card : ENNReal)⁻¹ := by
    have hdiv : c = (S.card : ENNReal) * (S'.card : ENNReal)⁻¹ := by
      simp [c, div_eq_mul_inv] <;> rfl
    rw [hdiv]
    have h3 : (S.card : ENNReal) * (S'.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ =
        (S'.card : ENNReal)⁻¹ := by
      have h4 : (S.card : ENNReal) * (S.card : ENNReal)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel hS_pos hS_top
      calc
        (S.card : ENNReal) * (S'.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹
          = (S'.card : ENNReal)⁻¹ * ((S.card : ENNReal) * (S.card : ENNReal)⁻¹) := by
            rw [mul_left_comm, ←mul_assoc]
        _ = (S'.card : ENNReal)⁻¹ * 1 := by rw [h4]
        _ = (S'.card : ENNReal)⁻¹ := by rw [mul_one]
    exact h3.symm
  calc
    (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set EuclideanPlane)
      ≤ (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane) := h21
    _ = (c * (S.card : ENNReal)⁻¹) • Measure.count.restrict (S : Set EuclideanPlane) := by
        rw [h22]
    _ = c • ((S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane)) := by
        rw [smul_smul] <;> rfl

/--
Ratio bound from density inequality.

If `a * b ≤ c * d` with `a, d` nonzero and finite, then `b / d ≤ c / a`.
Used to convert a density bound `δ^ρ * |S| ≤ 9 * |S'|` into
`|S| / |S'| ≤ 9 / δ^ρ = 9 * δ^{-ρ}`.
-/
lemma ennreal_ratio_bound {a b c d : ENNReal}
    (ha_pos : a ≠ 0) (ha_top : a ≠ ⊤)
    (hd_pos : d ≠ 0) (hd_top : d ≠ ⊤)
    (h : a * b ≤ c * d) :
    b / d ≤ c / a := by
  have h1 : a⁻¹ * d⁻¹ * (a * b) ≤ a⁻¹ * d⁻¹ * (c * d) := by gcongr
  have h21 : d⁻¹ * (a * b) = a * (d⁻¹ * b) := by rw [mul_left_comm d⁻¹ a]
  have h22 : a⁻¹ * a = 1 := by
    have h : a * a⁻¹ = 1 := ENNReal.mul_inv_cancel ha_pos ha_top
    have h' : a⁻¹ * a = a * a⁻¹ := by rw [mul_comm]
    rw [h']; exact h
  have h2 : a⁻¹ * d⁻¹ * (a * b) = b * d⁻¹ := by
    calc
      a⁻¹ * d⁻¹ * (a * b)
        = a⁻¹ * (d⁻¹ * (a * b)) := by rw [mul_assoc]
      _ = a⁻¹ * (a * (d⁻¹ * b)) := by rw [h21]
      _ = a⁻¹ * a * (d⁻¹ * b) := by rw [mul_assoc]
      _ = 1 * (d⁻¹ * b) := by rw [h22]
      _ = d⁻¹ * b := by simp
      _ = b * d⁻¹ := by rw [mul_comm]
  have h31 : d⁻¹ * (c * d) = c * (d⁻¹ * d) := by rw [mul_left_comm d⁻¹ c]
  have h32 : d⁻¹ * d = 1 := by
    have h : d * d⁻¹ = 1 := ENNReal.mul_inv_cancel hd_pos hd_top
    have h' : d⁻¹ * d = d * d⁻¹ := by rw [mul_comm]
    rw [h']
    exact h
  have h3 : a⁻¹ * d⁻¹ * (c * d) = c * a⁻¹ := by
    calc
      a⁻¹ * d⁻¹ * (c * d)
        = a⁻¹ * (d⁻¹ * (c * d)) := by rw [mul_assoc]
      _ = a⁻¹ * (c * (d⁻¹ * d)) := by rw [h31]
      _ = a⁻¹ * (c * 1) := by rw [h32]
      _ = a⁻¹ * c := by simp
      _ = c * a⁻¹ := by rw [mul_comm]
  rw [h2, h3] at h1
  simpa [div_eq_mul_inv] using h1

/-- Convert `9 / ofReal(δ^ρ)` to `ofReal(9 * δ^{-ρ})`. -/
lemma ennreal_nine_div_ofReal_pow {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    (9 : ENNReal) / ENNReal.ofReal (δ ^ ρ) = ENNReal.ofReal (9 * δ ^ (-ρ)) := by
  have h1 : 0 < δ ^ ρ := by positivity
  have h22 : δ ^ (-ρ) = (δ ^ ρ)⁻¹ :=
    Real.rpow_neg (show 0 ≤ δ from by linarith) ρ
  have h2 : ENNReal.ofReal (δ ^ (-ρ)) = (ENNReal.ofReal (δ ^ ρ))⁻¹ := by
    rw [h22]
    exact ENNReal.ofReal_inv_of_pos h1
  calc
    (9 : ENNReal) / ENNReal.ofReal (δ ^ ρ)
      = (9 : ENNReal) * (ENNReal.ofReal (δ ^ ρ))⁻¹ := by rw [div_eq_mul_inv]
    _ = (9 : ENNReal) * ENNReal.ofReal (δ ^ (-ρ)) := by rw [←h2]
    _ = ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal (δ ^ (-ρ)) := by norm_cast
    _ = ENNReal.ofReal (9 * δ ^ (-ρ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> ring

/-- Any finite measure is s-finite. -/
lemma sfinite_of_isFiniteMeasure {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] : SFinite μ := by
  have h1 : SFinite (Measure.sum (fun (_ : Unit) => μ)) :=
    sfinite_sum_of_countable (fun (_ : Unit) => μ)
  have h2 : Measure.sum (fun (_ : Unit) => μ) = μ := by
    ext s hs
    simp [Measure.sum_apply]
  rw [h2] at h1
  exact h1

/-- SFinite for count measure restricted to a finset. -/
lemma sfinite_count_restrict_finset {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (S : Finset X) :
    SFinite (Measure.count.restrict (S : Set X)) := by
  have hS_meas : MeasurableSet (S : Set X) := S.finite_toSet.measurableSet
  have h : (Measure.count.restrict (S : Set X)) Set.univ = ↑S.card := by
    have h1 : (Measure.count.restrict (S : Set X)) Set.univ = Measure.count (S : Set X) := by
      simp [Measure.restrict_apply]
    rw [h1]
    have h2 : Measure.count (S : Set X) = (S : Set X).encard :=
      Measure.count_apply hS_meas
    rw [h2]
    have h3 : (S : Set X).encard = ↑S.card := Set.encard_coe_eq_coe_finsetCard S
    rw [h3] <;> norm_cast
  have hfin : (Measure.count.restrict (S : Set X)) Set.univ < ⊤ := by
    rw [h]
    exact ENNReal.coe_lt_top
  letI : IsFiniteMeasure (Measure.count.restrict (S : Set X)) := ⟨hfin⟩
  exact sfinite_of_isFiniteMeasure (Measure.count.restrict (S : Set X))

/--
Refinement energy bound for finite sets with uniform counting measures.

If S' ⊆ S are finite nonempty sets and μ, μ' are the uniform probability
measures on S, S' respectively, then:
I_s(μ') ≤ (|S|/|S'|)^2 * I_s(μ).
-/
theorem refinement_energy_bound {S S' : Finset EuclideanPlane} {s : ℝ}
    (hS'_sub : S' ⊆ S) (hS'_nonempty : S'.Nonempty)
    (μ μ' : Measure EuclideanPlane)
    (hμ : μ = (S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane))
    (hμ' : μ' = (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set EuclideanPlane)) :
    planeEnergy μ' s ≤ ((S.card : ENNReal) / (S'.card : ENNReal)) ^ 2 * planeEnergy μ s := by
  subst hμ hμ'
  letI : SFinite (Measure.count.restrict (S : Set EuclideanPlane)) :=
    sfinite_count_restrict_finset S
  letI : SFinite (Measure.count.restrict (S' : Set EuclideanPlane)) :=
    sfinite_count_restrict_finset S'
  exact energy_bound_of_le_smul (refinement_measure_le' hS'_sub hS'_nonempty)

/--
Projected refinement energy bound for finite sets.

The projected energy satisfies the same bound because the pushforward
of a measure inequality is preserved: if μ' ≤ c • μ, then
map f μ' ≤ c • map f μ.
-/
theorem refinement_projected_energy_bound {S S' : Finset EuclideanPlane} {s σ : ℝ}
    (hS'_sub : S' ⊆ S) (hS'_nonempty : S'.Nonempty)
    (μ μ' : Measure EuclideanPlane)
    (hμ : μ = (S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane))
    (hμ' : μ' = (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set EuclideanPlane)) :
    projectedEnergy μ' s σ ≤ ((S.card : ENNReal) / (S'.card : ENNReal)) ^ 2 * projectedEnergy μ s σ := by
  subst hμ hμ'
  let c : ENNReal := (S.card : ENNReal) / (S'.card : ENNReal)
  let f : EuclideanPlane → ℝ := fun p => p 0 - σ * p 1
  have hf : Measurable f := by fun_prop
  have h_main : (S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set EuclideanPlane) ≤
      c • ((S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane)) :=
    refinement_measure_le' hS'_sub hS'_nonempty
  have h_map : Measure.map f ((S'.card : ENNReal)⁻¹ • Measure.count.restrict (S' : Set EuclideanPlane)) ≤
      c • Measure.map f ((S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane)) := by
    calc
      Measure.map f _ ≤ Measure.map f (c • _) := Measure.map_mono h_main hf
      _ = c • Measure.map f _ := by rw [Measure.map_smul c _ f]
  letI : SFinite (Measure.count.restrict (S : Set EuclideanPlane)) :=
    sfinite_count_restrict_finset S
  letI : SFinite (Measure.count.restrict (S' : Set EuclideanPlane)) :=
    sfinite_count_restrict_finset S'
  exact energy_bound_of_le_smul h_map

end RobustKaufmanProjection.Refinement
end
