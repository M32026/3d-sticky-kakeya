import MyLeanRepo.Kakeya.Assouad.WZ1.Inputs

/-!
# Discrete thin-tubes predicate and measure-to-discrete transfer

Defines `HasDiscreteThinTubes` for finite `DiscreteSet`s and proves that
uniform probability measures on finite sets with `HasMeasureThinTubes`
directly yield discrete thin tubes with the same constant.
-/

noncomputable section

open MeasureTheory Set ProbabilityTheory

open scoped ENNReal NNReal

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Uniform probability measure on a nonempty finite set. -/
def DiscreteSet.toProbabilityMeasure {n : ℕ}
    (A : DiscreteSet n) (h : A.Nonempty) : ProbabilityMeasure (Point n) :=
  ⟨uniformOn (A : Set _),
    isProbabilityMeasure_uniformOn (Finset.finite_toSet A) (Finset.coe_nonempty.mpr h)⟩

lemma DiscreteSet.toProbabilityMeasure_apply {n : ℕ}
    (A : DiscreteSet n) (h : A.Nonempty) (S : Set (Point n)) :
    (A.toProbabilityMeasure h : Measure (Point n)) S =
      ((A.filter (fun x => x ∈ S)).card : ENNReal) / (A.card : ENNReal) := by
  have hA_meas : MeasurableSet (A : Set (Point n)) := Finset.measurableSet A
  have h1 : (A.toProbabilityMeasure h : Measure (Point n)) S =
      (Measure.count (A : Set (Point n)))⁻¹ * Measure.count ((A : Set (Point n)) ∩ S) := by
    simp [DiscreteSet.toProbabilityMeasure, uniformOn, cond_apply hA_meas]
  rw [h1]
  have h_inter_fin : ((A : Set (Point n)) ∩ S).Finite :=
    Set.Finite.subset (Finset.finite_toSet A) (by simp)
  have h_toFinset : h_inter_fin.toFinset = A.filter (fun x => x ∈ S) := by
    ext x
    simp [Finset.mem_filter]
  have h_count_inter : Measure.count ((A : Set (Point n)) ∩ S) =
      ((A.filter (fun x => x ∈ S)).card : ENNReal) := by
    rw [Measure.count_apply_finite ((A : Set (Point n)) ∩ S) h_inter_fin, h_toFinset]
  have h_count_A : Measure.count (A : Set (Point n)) = (A.card : ENNReal) := by
    rw [Measure.count_apply_finite (A : Set (Point n)) (Finset.finite_toSet A)] <;> simp
  rw [h_count_inter, h_count_A]
  <;> rw [div_eq_mul_inv, mul_comm]

/-- The uniform measure equals a normalized sum of Dirac masses. -/
lemma DiscreteSet.uniformMeasure_eq_sum_dirac {n : ℕ}
    (A : DiscreteSet n) (h : A.Nonempty) :
    (A.toProbabilityMeasure h : Measure (Point n)) =
      ∑ x ∈ A, ((1 : ENNReal) / (A.card : ENNReal)) • Measure.dirac x := by
  apply Measure.ext
  intro S hS
  rw [A.toProbabilityMeasure_apply h S, Measure.finsetSum_apply]
  let c : ENNReal := (1 : ENNReal) / (A.card : ENNReal)
  have h_dirac : ∀ x ∈ A, ((c • Measure.dirac x) S) =
      c * (if x ∈ S then (1 : ENNReal) else 0) := by
    intro x _
    have h_smul : (c • Measure.dirac x) S = c * (Measure.dirac x) S :=
      MeasureTheory.Measure.smul_apply c (Measure.dirac x) S
    rw [h_smul]
    have h2 : (Measure.dirac x) S = (if x ∈ S then (1 : ENNReal) else 0) := by
      rw [Measure.dirac_apply]
      have h3 : Set.indicator S (1 : Point n → ENNReal) x =
          (if x ∈ S then (1 : ENNReal) else 0) := by
        simp [Set.indicator_apply] <;> split_ifs <;> simp
      exact h3
    rw [h2]
  have h_sum1 : ∑ x ∈ A, (c • Measure.dirac x) S =
      ∑ x ∈ A, c * (if x ∈ S then (1 : ENNReal) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact h_dirac x hx
  rw [h_sum1]
  have h_sum2 : ∑ x ∈ A, c * (if x ∈ S then (1 : ENNReal) else 0) =
      c * ((A.filter (fun x => x ∈ S)).card : ENNReal) := by
    rw [←Finset.mul_sum]
    have h : ∑ x ∈ A, (if x ∈ S then (1 : ENNReal) else 0) =
        ((A.filter (fun x => x ∈ S)).card : ENNReal) := by
      rw [Finset.sum_ite]
      <;> simp
    rw [h]
  rw [h_sum2]
  have h_final : c * ((A.filter (fun x => x ∈ S)).card : ENNReal) =
      ((A.filter (fun x => x ∈ S)).card : ENNReal) / (A.card : ENNReal) := by
    simp only [c, div_eq_mul_inv, mul_comm]
    <;> simp <;> rfl
  exact h_final.symm

-- Helper: support of c • μ when c ≠ 0
private lemma support_smul {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} {c : ENNReal} (hc : c ≠ 0) :
    (c • μ).support = μ.support := by
  ext x
  simp only [Measure.mem_support_iff_forall]
  constructor
  · intro h U hU
    have h4 : 0 < (c • μ) U := h U hU
    have h5 : (c • μ) U = c * μ U := by
      rw [MeasureTheory.Measure.smul_apply c μ U] <;> rfl
    rw [h5] at h4
    have h6 : c * μ U ≠ 0 := h4.ne'
    have h7 : μ U ≠ 0 := by
      by_contra h8
      have h9 : c * μ U = 0 := by rw [h8] <;> simp
      exact h6 h9
    exact Ne.bot_lt h7
  · intro h U hU
    have h4 : 0 < μ U := h U hU
    have h5 : μ U ≠ 0 := h4.ne'
    have h6 : c * μ U ≠ 0 := mul_ne_zero hc h5
    have h7 : 0 < c * μ U := Ne.bot_lt h6
    have h_smul : (c • μ) U = c * μ U := by
      rw [MeasureTheory.Measure.smul_apply c μ U] <;> rfl
    rw [h_smul]
    exact h7

-- Helper: support of finset sum of measures
private lemma support_finset_sum {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {ι : Type*} (s : Finset ι) (μ : ι → Measure X) :
    (∑ i ∈ s, μ i).support = ⋃ i ∈ s, (μ i).support := by
  classical
  induction s using Finset.induction with
  | empty => simp [Measure.support_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Measure.support_add, ih]
    ext y
    simp [Finset.mem_insert]

-- Helper: support of dirac in T1Space
private lemma support_dirac {X : Type*} [TopologicalSpace X] [T1Space X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (x0 : X) :
    (Measure.dirac x0).support = {x0} := by
  ext x
  simp only [Measure.mem_support_iff_forall, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hxa
    have h_compl_open : IsOpen ({x0} : Set X)ᶜ := isOpen_compl_singleton
    have h_nhds : ({x0} : Set X)ᶜ ∈ nhds x := h_compl_open.mem_nhds hxa
    have h_measure : (Measure.dirac x0) (({x0} : Set X)ᶜ) = 0 := by
      rw [Measure.dirac_apply]
      have h3 : Set.indicator (({x0} : Set X)ᶜ) (1 : X → ENNReal) x0 = 0 := by
        simp
      exact h3
    have h4 := h (({x0} : Set X)ᶜ) h_nhds
    rw [h_measure] at h4 <;> simp at h4
  · intro h_eq
    intro U hU
    have h_x0_in_U : x0 ∈ U := by
      rw [←h_eq]
      exact mem_of_mem_nhds hU
    have h_measure : (Measure.dirac x0) U = 1 := by
      rw [Measure.dirac_apply]
      have h3 : Set.indicator U (1 : X → ENNReal) x0 = 1 := by
        simp [h_x0_in_U]
      exact h3
    rw [h_measure] <;> norm_num

lemma DiscreteSet.toProbabilityMeasure_support {n : ℕ}
    (A : DiscreteSet n) (h : A.Nonempty) :
    (A.toProbabilityMeasure h : Measure (Point n)).support = (A : Set (Point n)) := by
  have h_card_pos : 0 < (A.card : ENNReal) := by exact_mod_cast h.card_pos
  have h_card_ne_zero : (A.card : ENNReal) ≠ 0 := h_card_pos.ne'
  have h_card_ne_top : (A.card : ENNReal) ≠ ⊤ := (ENNReal.natCast_lt_top A.card).ne
  let c : ENNReal := (1 : ENNReal) / (A.card : ENNReal)
  have hc_pos : 0 < c := by
    dsimp only [c]
    have h1 : (1 : ENNReal) ≠ 0 := by norm_num
    exact ENNReal.div_pos h1 h_card_ne_top
  have hc : c ≠ 0 := hc_pos.ne'
  have h_eq : (A.toProbabilityMeasure h : Measure (Point n)) =
      ∑ x ∈ A, c • Measure.dirac x :=
    A.uniformMeasure_eq_sum_dirac h
  rw [h_eq, support_finset_sum]
  have h1 : (⋃ x ∈ A, (c • Measure.dirac x).support) =
      (⋃ x ∈ A, (Measure.dirac x).support) := by
    ext y
    simp only [Set.mem_iUnion]
    <;> constructor <;> rintro ⟨x, hx, hy⟩ <;> refine ⟨x, hx, ?_⟩ <;>
      (rw [support_smul hc] at *; tauto)
  rw [h1]
  have h2 : (⋃ x ∈ A, (Measure.dirac x).support) = (⋃ x ∈ A, ({x} : Set (Point n))) := by
    ext y
    simp only [Set.mem_iUnion]
    <;> constructor <;> rintro ⟨x, hx, hy⟩ <;> refine ⟨x, hx, ?_⟩ <;>
      (rw [support_dirac x] at *; tauto)
  rw [h2]
  ext y
  simp <;> tauto

/-- Lintegral with respect to the uniform measure on a finite set. -/
lemma DiscreteSet.lintegral_uniformMeasure {n : ℕ}
    (A : DiscreteSet n) (h : A.Nonempty) (f : Point n → ENNReal) :
    ∫⁻ x, f x ∂(A.toProbabilityMeasure h : Measure _) =
      ∑ x ∈ A, ((1 : ENNReal) / (A.card : ENNReal)) * f x := by
  rw [A.uniformMeasure_eq_sum_dirac h]
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro x _
  have h : ∫⁻ y, f y ∂(((1 : ENNReal) / (A.card : ENNReal)) • Measure.dirac x) =
      ((1 : ENNReal) / (A.card : ENNReal)) * f x := by
    rw [lintegral_smul_measure, lintegral_dirac]
    <;> rw [smul_eq_mul]
  exact h

/-- Product of uniform measures on finite sets. -/
lemma DiscreteSet.toProbabilityMeasure_prod_apply
    {G₁ G₂ : DiscreteSet 2}
    (h1 : G₁.Nonempty) (h2 : G₂.Nonempty)
    (E' : Finset (Point2 × Point2)) (hE' : E' ⊆ G₁ ×ˢ G₂) :
    ((G₁.toProbabilityMeasure h1).prod (G₂.toProbabilityMeasure h2)) (E' : Set _) =
      (E'.card : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) := by
  set ν₁ := G₁.toProbabilityMeasure h1 with hν₁
  set ν₂ := G₂.toProbabilityMeasure h2 with hν₂
  have hE'_meas : MeasurableSet (E' : Set (Point2 × Point2)) :=
    (Finset.finite_toSet E').measurableSet
  have h_fiber_eq : ∀ (x : Point2), Prod.mk x ⁻¹' (E' : Set _) =
      {b₂ | (x, b₂) ∈ E'} := by
    intro x
    ext b₂
    simp
  let c1 : ENNReal := (1 : ENNReal) / (G₁.card : ENNReal)
  let c2 : ENNReal := (1 : ENNReal) / (G₂.card : ENNReal)
  let c12 : ENNReal := (1 : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal))
  have h4 : ∀ x ∈ G₁, (ν₂ : Measure Point2) (Prod.mk x ⁻¹' (E' : Set _)) =
      ((G₂.filter (fun b₂ => (x, b₂) ∈ E')).card : ENNReal) / (G₂.card : ENNReal) := by
    intro x _
    have h_fiber : (ν₂ : Measure Point2) (Prod.mk x ⁻¹' (E' : Set _)) =
        (ν₂ : Measure Point2) {b₂ | (x, b₂) ∈ E'} := by
      rw [h_fiber_eq x]
    rw [h_fiber]
    have h_app := G₂.toProbabilityMeasure_apply h2 {b₂ | (x, b₂) ∈ E'}
    simpa [Finset.mem_filter] using h_app
  have h4' : ∀ x ∈ G₁, c1 * (ν₂ : Measure Point2) (Prod.mk x ⁻¹' (E' : Set _)) =
      c12 * ((G₂.filter (fun b₂ => (x, b₂) ∈ E')).card : ENNReal) := by
    intro x hx
    rw [h4 x hx]
    set A : ENNReal := ((G₂.filter (fun b₂ => (x, b₂) ∈ E')).card : ENNReal) with hA
    have h1pos : (G₁.card : ENNReal) ≠ 0 := by exact_mod_cast h1.card_pos.ne'
    have h2pos : (G₂.card : ENNReal) ≠ 0 := by exact_mod_cast h2.card_pos.ne'
    have h1top : (G₁.card : ENNReal) ≠ ⊤ := (ENNReal.natCast_lt_top G₁.card).ne
    have h2top : (G₂.card : ENNReal) ≠ ⊤ := (ENNReal.natCast_lt_top G₂.card).ne
    calc
      c1 * (A / (G₂.card : ENNReal))
        = (1 / (G₁.card : ENNReal)) * (A / (G₂.card : ENNReal)) := by rfl
      _ = A / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) := by
        have h_step1 : ((1 : ENNReal) / (G₁.card : ENNReal)) * (A / (G₂.card : ENNReal)) =
            (((1 : ENNReal) / (G₁.card : ENNReal)) * A) / (G₂.card : ENNReal) := by
          rw [←mul_div_assoc]
        rw [h_step1]
        have h_step2 : (((1 : ENNReal) / (G₁.card : ENNReal)) * A) / (G₂.card : ENNReal) =
            (A / (G₁.card : ENNReal)) / (G₂.card : ENNReal) := by
          have h_comm : ((1 : ENNReal) / (G₁.card : ENNReal)) * A = A / (G₁.card : ENNReal) := by
            have h : ((1 : ENNReal) / (G₁.card : ENNReal)) * A = A * ((1 : ENNReal) / (G₁.card : ENNReal)) := mul_comm _ _
            rw [h]
            simp [div_eq_mul_inv] <;> rfl
          rw [h_comm]
        rw [h_step2]
        have h_step3 : (A / (G₁.card : ENNReal)) / (G₂.card : ENNReal) =
            A / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) := by
          simp only [div_eq_mul_inv]
          have h_inv : (G₁.card : ENNReal)⁻¹ * (G₂.card : ENNReal)⁻¹ =
              ((G₁.card : ENNReal) * (G₂.card : ENNReal))⁻¹ := by
            have h_mult : ((G₁.card : ENNReal)⁻¹ * (G₂.card : ENNReal)⁻¹) *
                ((G₁.card : ENNReal) * (G₂.card : ENNReal)) = 1 := by
              calc
                ((G₁.card : ENNReal)⁻¹ * (G₂.card : ENNReal)⁻¹) *
                    ((G₁.card : ENNReal) * (G₂.card : ENNReal))
                  = (G₁.card : ENNReal)⁻¹ * ((G₂.card : ENNReal)⁻¹ * (G₂.card : ENNReal)) *
                      (G₁.card : ENNReal) := by
                    simp [mul_assoc, mul_comm, mul_left_comm]
                _ = (G₁.card : ENNReal)⁻¹ * 1 * (G₁.card : ENNReal) := by
                    rw [ENNReal.inv_mul_cancel h2pos h2top] <;> simp
                _ = (G₁.card : ENNReal)⁻¹ * (G₁.card : ENNReal) := by simp
                _ = 1 := ENNReal.inv_mul_cancel h1pos h1top
            exact ENNReal.eq_inv_of_mul_eq_one_left h_mult
          rw [mul_assoc, h_inv]
        exact h_step3
      _ = c12 * A := by
        simp [c12, div_eq_mul_inv, mul_comm] <;> rfl
  have h_lintegral : ∫⁻ (x : Point2), (ν₂ : Measure Point2) (Prod.mk x ⁻¹' (E' : Set _)) ∂(ν₁ : Measure Point2) =
      (E'.card : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) := by
    rw [G₁.lintegral_uniformMeasure h1]
    have h_sum : ∑ x ∈ G₁, c1 * (ν₂ : Measure Point2) (Prod.mk x ⁻¹' (E' : Set _)) =
        c12 * ∑ x ∈ G₁, ((G₂.filter (fun b₂ => (x, b₂) ∈ E')).card : ENNReal) := by
      rw [Finset.sum_congr rfl h4', Finset.mul_sum]
      <;> rfl
    rw [h_sum]
    let F : Point2 → Finset (Point2 × Point2) := fun x =>
      ({x} : Finset Point2) ×ˢ (G₂.filter (fun b₂ => (x, b₂) ∈ E'))
    have h8 : E' = Finset.biUnion G₁ F := by
      ext p
      simp only [Finset.mem_biUnion]
      constructor
      · intro h9
        have h10 : p ∈ G₁ ×ˢ G₂ := hE' h9
        have h11 : p.1 ∈ G₁ := (Finset.mem_product.mp h10).1
        have h12 : p.2 ∈ G₂ := (Finset.mem_product.mp h10).2
        have h13 : p.2 ∈ G₂.filter (fun b₂ => (p.1, b₂) ∈ E') := by
          simp only [Finset.mem_filter] <;> exact ⟨h12, h9⟩
        refine ⟨p.1, h11, ?_⟩
        have h14 : p ∈ F p.1 := by
          simp only [F, Finset.mem_product, Finset.mem_singleton]
          <;> exact ⟨trivial, h13⟩
        exact h14
      · rintro ⟨x', hx', hp⟩
        simp only [F, Finset.mem_product, Finset.mem_singleton] at hp
        have h14 : p.1 = x' := hp.1
        have h15 : p.2 ∈ G₂.filter (fun b₂ => (x', b₂) ∈ E') := hp.2
        have h16 : (x', p.2) ∈ E' := (Finset.mem_filter.mp h15).2
        have h17 : (p.1, p.2) ∈ E' := by
          have h18 : (p.1, p.2) = (x', p.2) := by
            rw [h14]
          rw [h18]
          exact h16
        simpa using h17
    have h_disj : ∀ (x : Point2), x ∈ G₁ → ∀ (y : Point2), y ∈ G₁ → x ≠ y → Disjoint (F x) (F y) := by
      intro x _ y _ hxy
      simp only [Finset.disjoint_left, Finset.mem_product, Finset.mem_singleton, F]
      intro p hp1 hp2
      have hpx : p.1 = x := hp1.1
      have hpy : p.1 = y := hp2.1
      have h_cont : x = y := by rw [←hpx, hpy]
      exact hxy h_cont
    have h9 : (E'.card : ENNReal) = ∑ x ∈ G₁, ((F x).card : ENNReal) := by
      rw [h8, Finset.card_biUnion h_disj]
      rw [Nat.cast_sum]
    rw [h9]
    have h10 : ∑ x ∈ G₁, ((F x).card : ENNReal) =
        ∑ x ∈ G₁, ((G₂.filter (fun b₂ => (x, b₂) ∈ E')).card : ENNReal) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [F, Finset.card_product, Finset.card_singleton, one_mul]
    rw [h10]
    <;> rw [show c12 = ((G₁.card : ENNReal) * (G₂.card : ENNReal))⁻¹ from by
          simp [c12, div_eq_mul_inv]]
    <;> rw [mul_comm, ←div_eq_mul_inv]
  have h_main : (ν₁.prod ν₂) (E' : Set _) =
      ↑((∫⁻ (x : Point2), (ν₂ : Measure Point2) (Prod.mk x ⁻¹' (E' : Set _)) ∂(ν₁ : Measure Point2)).toNNReal) := by
    exact ProbabilityMeasure.prod_apply ν₁ ν₂ (E' : Set _) hE'_meas
  rw [h_main, h_lintegral]
  have h_ne_top : (E'.card : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) ≠ ⊤ := by
    have h9 : E'.card ≤ (G₁ ×ˢ G₂).card := Finset.card_le_card hE'
    have h10 : (G₁ ×ˢ G₂).card = G₁.card * G₂.card := Finset.card_product G₁ G₂
    have h11 : (E'.card : ENNReal) ≤ (G₁.card : ENNReal) * (G₂.card : ENNReal) := by
      rw [h10] at h9
      exact_mod_cast h9
    have h_pos : 0 < (G₁.card : ENNReal) * (G₂.card : ENNReal) := by positivity
    have h_div : (E'.card : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) ≤
        ((G₁.card : ENNReal) * (G₂.card : ENNReal)) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) := by
      gcongr
    set a : ENNReal := (G₁.card : ENNReal) * (G₂.card : ENNReal) with ha
    have ha0 : a ≠ 0 := h_pos.ne'
    have hatop : a ≠ ⊤ := (ENNReal.mul_lt_top (ENNReal.natCast_lt_top G₁.card) (ENNReal.natCast_lt_top G₂.card)).ne
    have h_self : a / a = 1 := by
      rw [div_eq_mul_inv, ENNReal.mul_inv_cancel ha0 hatop] <;> norm_num
    rw [h_self] at h_div
    have h12 : (E'.card : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) ≤ 1 := h_div
    have h13 : (E'.card : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) < ⊤ :=
      lt_of_le_of_lt h12 (by norm_num)
    exact h13.ne
  exact ENNReal.coe_toNNReal h_ne_top

/--
Discrete thin-tubes condition for finite planar sets.

The bound is only required for scales `r ≥ δ`, avoiding the contradiction
that would arise for `r → 0` when `β > 0`.
-/
def HasDiscreteThinTubes (δ β K c : ℝ)
    (G₁ G₂ : DiscreteSet 2) : Prop :=
  0 ≤ β ∧
  1 ≤ K ∧
  c ∈ Set.Ico (0 : ℝ) 1 ∧
  ∃ E : Finset (Point2 × Point2),
    E ⊆ G₁ ×ˢ G₂ ∧
    (1 - ENNReal.ofReal c) * (G₁.card : ENNReal) * (G₂.card : ENNReal)
      ≤ (E.card : ENNReal) ∧
    ∀ b₁ ∈ G₁,
      ∀ ℓ : AffineSubspace ℝ Point2,
        b₁ ∈ (ℓ : Set Point2) →
          Module.finrank ℝ ℓ.direction = 1 →
            ∀ r : ℝ, δ ≤ r →
              ((G₂.filter fun b₂ =>
                b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
                (b₁, b₂) ∈ E).card : ENNReal) ≤
                ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal)

/--
Transfer from measure thin tubes to discrete thin tubes for uniform
probability measures on finite sets.

The measure bound holds for all `r > 0`, so restricting to `r ≥ δ` is trivial.
-/
theorem hasMeasureThinTubes_to_hasDiscreteThinTubes
    {δ β K c : ℝ} (hδ : 0 < δ)
    {G₁ G₂ : DiscreteSet 2}
    (h1 : G₁.Nonempty) (h2 : G₂.Nonempty)
    (h : HasMeasureThinTubes β K c
      (G₁.toProbabilityMeasure h1)
      (G₂.toProbabilityMeasure h2)) :
    HasDiscreteThinTubes δ β K c G₁ G₂ := by
  rcases h with ⟨hβ, hK, hc, E, hE_meas, hE_sub, hE_mass, h_thin⟩
  have h_supp1 : (G₁.toProbabilityMeasure h1 : Measure Point2).support = (G₁ : Set Point2) :=
    G₁.toProbabilityMeasure_support h1
  have h_supp2 : (G₂.toProbabilityMeasure h2 : Measure Point2).support = (G₂ : Set Point2) :=
    G₂.toProbabilityMeasure_support h2
  have hE_sub' : E ⊆ (G₁ : Set Point2) ×ˢ (G₂ : Set Point2) := by
    rw [h_supp1, h_supp2] at hE_sub
    exact hE_sub
  have h_eq_prod : (↑(G₁ ×ˢ G₂) : Set (Point2 × Point2)) =
      (G₁ : Set Point2) ×ˢ (G₂ : Set Point2) := by
    ext ⟨x, y⟩
    simp <;> tauto
  have hE_sub'' : E ⊆ (↑(G₁ ×ˢ G₂) : Set (Point2 × Point2)) := by
    rw [h_eq_prod]
    exact hE_sub'
  have hE_finite : Set.Finite E :=
    Set.Finite.subset (Finset.finite_toSet (G₁ ×ˢ G₂)) hE_sub''
  let E' : Finset (Point2 × Point2) := hE_finite.toFinset
  have hE'_eq : (E' : Set (Point2 × Point2)) = E :=
    Set.Finite.coe_toFinset _
  have hE'_sub : E' ⊆ G₁ ×ˢ G₂ := by
    simpa [E', hE'_eq] using hE_sub''
  have h_card_pos1 : 0 < (G₁.card : ENNReal) := by exact_mod_cast h1.card_pos
  have h_card_pos2 : 0 < (G₂.card : ENNReal) := by exact_mod_cast h2.card_pos
  have h_card_ne_top1 : (G₁.card : ENNReal) ≠ ⊤ := (ENNReal.natCast_lt_top G₁.card).ne
  have h_card_ne_top2 : (G₂.card : ENNReal) ≠ ⊤ := (ENNReal.natCast_lt_top G₂.card).ne
  have h_card_pos12 : 0 < (G₁.card : ENNReal) * (G₂.card : ENNReal) := by positivity
  have h_card_ne_top12 : (G₁.card : ENNReal) * (G₂.card : ENNReal) ≠ ⊤ := by
    have h : (G₁.card : ENNReal) * (G₂.card : ENNReal) < ⊤ := by
      apply ENNReal.mul_lt_top
      <;> exact ENNReal.natCast_lt_top _
    exact h.ne
  have h_prod : ((G₁.toProbabilityMeasure h1).prod
      (G₂.toProbabilityMeasure h2)) E =
      (E'.card : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) := by
    have h9 : ((G₁.toProbabilityMeasure h1).prod (G₂.toProbabilityMeasure h2)) E =
        ((G₁.toProbabilityMeasure h1).prod (G₂.toProbabilityMeasure h2)) (E' : Set _) := by
      rw [hE'_eq]
    rw [h9]
    exact DiscreteSet.toProbabilityMeasure_prod_apply h1 h2 E' hE'_sub
  have h_mass : (1 - ENNReal.ofReal c) * (G₁.card : ENNReal) * (G₂.card : ENNReal)
      ≤ (E'.card : ENNReal) := by
    rw [h_prod] at hE_mass
    have h : (1 - ENNReal.ofReal c) ≤
        (E'.card : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)) := hE_mass
    have h' : (1 - ENNReal.ofReal c) * ((G₁.card : ENNReal) * (G₂.card : ENNReal)) ≤
        (E'.card : ENNReal) := by
      calc
        (1 - ENNReal.ofReal c) * ((G₁.card : ENNReal) * (G₂.card : ENNReal))
          ≤ ((E'.card : ENNReal) / ((G₁.card : ENNReal) * (G₂.card : ENNReal)))
              * ((G₁.card : ENNReal) * (G₂.card : ENNReal)) := by gcongr
        _ = (E'.card : ENNReal) := by
          rw [ENNReal.div_mul_cancel h_card_pos12.ne' h_card_ne_top12]
    simpa [mul_assoc] using h'
  have h_main : ∀ b₁ ∈ G₁, ∀ ℓ : AffineSubspace ℝ Point2,
      b₁ ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ r : ℝ, δ ≤ r →
        ((G₂.filter fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
          (b₁, b₂) ∈ E').card : ENNReal) ≤
          ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal) := by
    intro b₁ hb₁ ℓ hb₁_line hfin r hr
    have hr_pos : 0 < r := hδ.trans_le hr
    have hb₁_supp : b₁ ∈ (G₁.toProbabilityMeasure h1 : Measure Point2).support := by
      rw [h_supp1] <;> exact hb₁
    let S : Set Point2 := {b₂ |
      b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E}
    have h_nonneg : 0 ≤ K * r ^ β := by positivity
    have h_thin' : (G₂.toProbabilityMeasure h2) S ≤ Real.toNNReal (K * r ^ β) := by
      have h_S_def : S = {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E} := by rfl
      rw [h_S_def]
      exact h_thin b₁ hb₁_supp ℓ hb₁_line hfin r hr_pos
    have h_measure : (G₂.toProbabilityMeasure h2 : Measure Point2) S ≤
        ENNReal.ofReal (K * r ^ β) := by
      let ν : ProbabilityMeasure Point2 := G₂.toProbabilityMeasure h2
      have h_univ : (ν : Measure Point2) Set.univ = 1 := by
        simp [ProbabilityMeasure]
      have h_le_one : (ν : Measure Point2) S ≤ 1 := by
        calc (ν : Measure Point2) S
          ≤ (ν : Measure Point2) Set.univ := measure_mono (Set.subset_univ S)
        _ = 1 := h_univ
      have h_ne_top : (ν : Measure Point2) S ≠ ⊤ := ne_top_of_le_ne_top (by simp) h_le_one
      set x : ENNReal := (ν : Measure Point2) S with hx
      have h1 : x ≠ ⊤ := h_ne_top
      have h_toNNReal : x.toNNReal = ν S := by
        rfl
      have h_eq : ENNReal.ofNNReal (x.toNNReal) = x :=
        ENNReal.coe_toNNReal h1
      rw [←h_eq, h_toNNReal]
      have h3 : ENNReal.ofNNReal (ν S) ≤ ENNReal.ofNNReal (Real.toNNReal (K * r ^ β)) :=
        ENNReal.coe_le_coe.mpr h_thin'
      have h4 : ENNReal.ofNNReal (Real.toNNReal (K * r ^ β)) = ENNReal.ofReal (K * r ^ β) :=
        ENNReal.ofNNReal_toNNReal (K * r ^ β)
      rw [h4] at h3
      exact h3
    have h_filter_eq : G₂.filter (fun b₂ =>
        b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E') =
        G₂.filter (fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E) := by
      ext b₂
      simp only [Finset.mem_filter]
      have h_iff : (b₁, b₂) ∈ E' ↔ (b₁, b₂) ∈ E := by
        exact hE'_eq ▸ Iff.rfl
      tauto
    rw [h_filter_eq]
    have h_S_eq : S = {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E} := by
      rfl
    have h_apply : (G₂.toProbabilityMeasure h2 : Measure Point2) S =
        ((G₂.filter (fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E)).card : ENNReal)
          / (G₂.card : ENNReal) := by
      rw [h_S_eq]
      have h_tmp := G₂.toProbabilityMeasure_apply h2 {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E}
      simpa [Finset.mem_filter] using h_tmp
    rw [h_apply] at h_measure
    have h_cancel : (((G₂.filter (fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E)).card : ENNReal)
          / (G₂.card : ENNReal)) * (G₂.card : ENNReal) =
        ((G₂.filter (fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E)).card : ENNReal) := by
      rw [ENNReal.div_mul_cancel h_card_pos2.ne' h_card_ne_top2]
    calc
      ((G₂.filter (fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E)).card : ENNReal)
        = (((G₂.filter (fun b₂ =>
            b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E)).card : ENNReal)
              / (G₂.card : ENNReal)) * (G₂.card : ENNReal) := by
          rw [h_cancel]
      _ ≤ ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal) := by gcongr
  exact ⟨hβ, hK, hc, E', hE'_sub, h_mass, h_main⟩

/-- Subset inheritance for direct tube bounds (the form used by Lemma 40).

If `G₂` satisfies a tube bound with constant `K`, and `G₂'' ⊆ G₂` is nonempty,
then `G₂''` satisfies the same bound with constant `K * |G₂| / |G₂''|`.
-/
lemma thin_tubes_subset
    {δ β K : ℝ} {G₁ G₂ G₂'' : DiscreteSet 2}
    (hK : 1 ≤ K) (hδ : 0 < δ)
    (h_sub : G₂'' ⊆ G₂) (hG2''_ne : G₂''.Nonempty)
    (h_thin : ∀ b₁ ∈ G₁, ∀ ℓ : AffineSubspace ℝ Point2,
      b₁ ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ((G₂.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2))).card : ENNReal) ≤
        ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal)) :
    ∀ b₁ ∈ G₁, ∀ ℓ : AffineSubspace ℝ Point2,
      b₁ ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ((G₂''.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2))).card : ENNReal) ≤
        ENNReal.ofReal ((K * (G₂.card : ℝ) / (G₂''.card : ℝ)) * r ^ β) * (G₂''.card : ENNReal) := by
  intro b₁ hb₁ ℓ hb₁_in hfin r hr hr1
  let S : Set Point2 := Metric.thickening r (ℓ : Set Point2)
  have h1 : (G₂''.filter (fun b₂ => b₂ ∈ S)) ⊆ (G₂.filter (fun b₂ => b₂ ∈ S)) := by
    apply Finset.filter_subset_filter
    exact h_sub
  have h2 : ((G₂''.filter (fun b₂ => b₂ ∈ S)).card : ENNReal) ≤
      ((G₂.filter (fun b₂ => b₂ ∈ S)).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card h1
  have h3 := h_thin b₁ hb₁ ℓ hb₁_in hfin r hr hr1
  have h4 : ((G₂''.filter (fun b₂ => b₂ ∈ S)).card : ENNReal) ≤
      ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal) := le_trans h2 h3
  have hK_nonneg : 0 ≤ K := by linarith
  have hr_nonneg : 0 ≤ r := by linarith
  have hG2_card_pos : 0 < (G₂.card : ℝ) := by
    exact_mod_cast (hG2''_ne.mono h_sub).card_pos
  have hG2''_card_pos : 0 < (G₂''.card : ℝ) := by exact_mod_cast hG2''_ne.card_pos
  have h_pos1 : 0 ≤ K * r ^ β := by positivity
  have h_pos2 : 0 ≤ (K * (G₂.card : ℝ) / (G₂''.card : ℝ)) * r ^ β := by positivity
  have hG2_coe : (G₂.card : ENNReal) = ENNReal.ofReal (G₂.card : ℝ) := by
    simp
  have hG2''_coe : (G₂''.card : ENNReal) = ENNReal.ofReal (G₂''.card : ℝ) := by
    simp
  have h_eq : ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal) =
      ENNReal.ofReal ((K * (G₂.card : ℝ) / (G₂''.card : ℝ)) * r ^ β) * (G₂''.card : ENNReal) := by
    rw [hG2_coe, hG2''_coe]
    have h5 : ENNReal.ofReal (K * r ^ β) * ENNReal.ofReal (G₂.card : ℝ) =
        ENNReal.ofReal (K * r ^ β * (G₂.card : ℝ)) := by
      rw [←ENNReal.ofReal_mul h_pos1]
    have h6 : ENNReal.ofReal ((K * (G₂.card : ℝ) / (G₂''.card : ℝ)) * r ^ β) * ENNReal.ofReal (G₂''.card : ℝ) =
        ENNReal.ofReal (((K * (G₂.card : ℝ) / (G₂''.card : ℝ)) * r ^ β) * (G₂''.card : ℝ)) := by
      rw [←ENNReal.ofReal_mul h_pos2]
    rw [h5, h6]
    have h7 : K * r ^ β * (G₂.card : ℝ) =
        ((K * (G₂.card : ℝ) / (G₂''.card : ℝ)) * r ^ β) * (G₂''.card : ℝ) := by
      field_simp [hG2''_card_pos.ne'] <;> ring
    rw [h7]
  rw [h_eq] at h4
  exact h4

/-- Frostman property transfers to subsets with constant scaled by |A|/|A'|. -/
lemma frostman_subset
    {δ s : ℝ} {C : ENNReal} {A A' : DiscreteSet 2}
    (h_sub : A' ⊆ A) (hA'_ne : A'.Nonempty)
    (hFrost : A.IsFrostman δ s C) :
    A'.IsFrostman δ s (C * (A.enncard / A'.enncard)) := by
  intro x r hr hr1
  have h1 : A'.ballCount x r ≤ A.ballCount x r := by
    let p : Point2 → Prop := fun y => dist y x ≤ r
    have h_filter : A'.filter p ⊆ A.filter p := by
      exact Finset.filter_subset_filter p h_sub
    have h_card : ((A'.filter p).card : ENNReal) ≤ ((A.filter p).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h_filter
    simpa [DiscreteSet.ballCount] using h_card
  have h2 := hFrost x r hr hr1
  have h3 : A'.ballCount x r ≤ C * Kakeya.realRpowENN r s * A.enncard := le_trans h1 h2
  have hA'_pos : A'.enncard ≠ 0 := by
    have h : (A'.card : ENNReal) ≠ 0 := by exact_mod_cast hA'_ne.card_pos.ne'
    simpa [DiscreteSet.enncard] using h
  have hA'_top : A'.enncard ≠ ⊤ := ENNReal.natCast_ne_top _
  have h4 : C * Kakeya.realRpowENN r s * A.enncard =
      (C * (A.enncard / A'.enncard)) * Kakeya.realRpowENN r s * A'.enncard := by
    calc
      C * Kakeya.realRpowENN r s * A.enncard
        = C * Kakeya.realRpowENN r s * (A.enncard / A'.enncard * A'.enncard) := by
          rw [ENNReal.div_mul_cancel hA'_pos hA'_top] <;> ring
      _ = (C * (A.enncard / A'.enncard)) * Kakeya.realRpowENN r s * A'.enncard := by ring
  rw [h4] at h3
  exact h3

end Kakeya.Assouad
