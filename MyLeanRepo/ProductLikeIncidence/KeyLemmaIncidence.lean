module

/-
# Key Lemma — Incidence Counting (Step 1)

Elementary combinatorial step: total incidences between incidence points z
and δ-cubes meeting Pz is ≥ C^{-3} δ^{-(τ+2s)}.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeIncidence.CoveringLowerBound
public import MyLeanRepo.ProductLikeIncidence.CardinalityLowerBound
public import MyLeanRepo.TauMonotonicity
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set Bornology ENNReal MeasureTheory Finset

namespace ProductLikeIncidence.ProductReduction

attribute [local instance] Classical.propDecidable

/-- Construct a 2D point from coordinates. -/
def mkP2 (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i : Fin 2 => if i = 0 then x else y

/-- For a grid subset A ⊆ δℤ ∩ [0,1] that is a (δ,s,C)-set, encard A ≥ C^{-1} δ^{-s}. -/
lemma grid_encard_lower_bound {δ s C : ℝ} {A : Set ℝ}
    (hδ : 0 < δ) (_hA_grid : A ⊆ productLikeUnitGrid δ)
    (hA_delta : IsProductLikeRealDeltaSCSet δ s C A) :
    ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤ ENat.toENNReal A.encard := by
  have h1 : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
      ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) :=
    ProductLikeIncidence.covering_lower_bound hA_delta
  have h2 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) ≤
      ENat.toENNReal (productLikeRealLineCopy A).encard :=
    ProductLikeIncidence.covering_number_le_encard hδ
  let f : ℝ → EuclideanSpace ℝ (Fin 1) := fun x =>
    (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun (_ : Fin 1) => x)
  have h_eq1 : productLikeRealLineCopy A = f '' A := by
    ext p
    simp only [productLikeRealLineCopy, Set.mem_image]
    constructor
    · intro hp
      exact ⟨p 0, hp, PiLp.ext (fun i => by fin_cases i <;> rfl)⟩
    · rintro ⟨x, hx, h_eq⟩
      have h_p0 : p 0 = x := by
        have h' : (f x) 0 = x := by simp [f]
        rw [←h', h_eq]
      have h_goal : p 0 ∈ A := by rw [h_p0] <;> exact hx
      exact h_goal
  have h_inj : Set.InjOn f A := by
    intro x _ y _ h
    have h' : (f x) 0 = (f y) 0 := by rw [h]
    simpa [f] using h'
  have h3 : (productLikeRealLineCopy A).encard = A.encard := by
    rw [h_eq1]
    exact h_inj.encard_image
  rw [h3] at h2
  exact le_trans h1 h2

/-- The incidence set is finite. -/
lemma incidence_set_finite {δ : ℝ} {Y : Set ℝ} {X : ℝ → Set ℝ}
    (hδ : 0 < δ) (hY_grid : Y ⊆ productLikeUnitGrid δ)
    (hX_grid : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ) :
    (productLikeIncidenceSet Y X).Finite := by
  have hY_finite : Y.Finite :=
    Set.Finite.subset (productLikeUnitGrid_finite hδ) hY_grid
  have hX_finite : ∀ y ∈ Y, (X y).Finite := fun y hy =>
    Set.Finite.subset (productLikeUnitGrid_finite hδ) (hX_grid y hy)
  have h_fiber_finite : ∀ y ∈ Y,
      ({z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y}).Finite := by
    intro y hy
    let g : ℝ → EuclideanSpace ℝ (Fin 2) := fun x => mkP2 x y
    have h_eq : {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y} = g '' X y := by
      ext z
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro hz
        refine ⟨z 0, hz.1, ?_⟩
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [g, mkP2, hz.2] <;> rfl
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, by simp [g, mkP2]⟩
    rw [h_eq]
    exact (hX_finite y hy).image g
  exact hY_finite.biUnion h_fiber_finite

/-- **Step 1: Incidence count lower bound.**

Total incidences (z, δ-cube Q meeting Pz) ≥ C^{-3} δ^{-(τ+2s)}. -/
lemma incidence_count_lower_bound
    {δ s τ C : ℝ} {Y : Set ℝ} {X : ℝ → Set ℝ}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (hδ : 0 < δ) (hC_pos : 0 < C)
    (hY_grid : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hX_grid : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ)
    (hX_delta : ∀ y ∈ Y, IsProductLikeRealDeltaSCSet δ s C (X y))
    (hPz_delta : ∀ z ∈ productLikeIncidenceSet Y X,
      IsDeltaSCSet δ s C (Pz z)) :
    ENNReal.ofReal (C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s))) ≤
      ∑ z ∈ (incidence_set_finite hδ hY_grid hX_grid).toFinset,
        ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) := by
  let Z := productLikeIncidenceSet Y X
  have hZ_finite : Z.Finite := incidence_set_finite hδ hY_grid hX_grid
  have hY_finite : Y.Finite :=
    Set.Finite.subset (productLikeUnitGrid_finite hδ) hY_grid
  let Yf := hY_finite.toFinset
  let Zf := hZ_finite.toFinset

  have hY_lower : ENNReal.ofReal (C⁻¹ * δ ^ (-τ)) ≤ ENat.toENNReal Y.encard :=
    grid_encard_lower_bound hδ hY_grid hY_delta

  have hX_lower : ∀ y ∈ Y,
      ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤ ENat.toENNReal (X y).encard :=
    fun y hy => grid_encard_lower_bound hδ (hX_grid y hy) (hX_delta y hy)

  -- Z.encard ≥ C^{-2} δ^{-(τ+s)}
  have hZ_lower : ENNReal.ofReal (C⁻¹ ^ 2 * δ ^ (-(τ + s))) ≤ ENat.toENNReal Z.encard := by
    let fiber (y : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z 0 ∈ X y ∧ z 1 = y}
    have h_disj : ∀ y1 ∈ Y, ∀ y2 ∈ Y, y1 ≠ y2 → Disjoint (fiber y1) (fiber y2) := by
      intro y1 _ y2 _ hne
      simp only [fiber, Set.disjoint_left, Set.mem_setOf_eq]
      intro z hz1 hz2
      have h : z 1 = y1 := hz1.2
      have h' : z 1 = y2 := hz2.2
      rw [h] at h'; exact hne h'
    have h_encard : Z.encard = ∑ᶠ y ∈ Y, (fiber y).encard :=
      hY_finite.encard_biUnion h_disj
    have h_fiber_encard : ∀ y ∈ Y, (fiber y).encard = (X y).encard := by
      intro y _
      let g : ℝ → EuclideanSpace ℝ (Fin 2) := fun x => mkP2 x y
      have h_eq : fiber y = g '' (X y) := by
        ext z
        simp only [fiber, Set.mem_image, Set.mem_setOf_eq]
        constructor
        · intro hz
          refine ⟨z 0, hz.1, ?_⟩
          apply PiLp.ext
          intro i
          fin_cases i <;> simp [g, mkP2, hz.2] <;> rfl
        · rintro ⟨x, hx, rfl⟩
          exact ⟨hx, by simp [g, mkP2]⟩
      rw [h_eq]
      have h_inj : Set.InjOn g (X y) := by
        intro x1 _ x2 _ h
        have h' : (g x1) 0 = (g x2) 0 := by rw [h]
        simpa [g, mkP2] using h'
      exact h_inj.encard_image
    -- Convert finsum to Finset.sum
    have h_finsum_eq : (∑ᶠ y ∈ Y, (fiber y).encard) = ∑ y ∈ Yf, (fiber y).encard := by
      have hY_coe : (Yf : Set ℝ) = Y := hY_finite.coe_toFinset
      rw [←hY_coe]
      exact finsum_mem_finset_eq_sum (fun i => (fiber i).encard) Yf
    have h_encard2 : Z.encard = ∑ y ∈ Yf, (fiber y).encard := by
      rw [h_encard, h_finsum_eq]
    have h_coe_sum : ENat.toENNReal (∑ y ∈ Yf, (fiber y).encard) =
        ∑ y ∈ Yf, ENat.toENNReal (fiber y).encard := by
      have h_main : ∀ (s : Finset ℝ), ENat.toENNReal (∑ y ∈ s, (fiber y).encard) =
          ∑ y ∈ s, ENat.toENNReal (fiber y).encard := by
        intro s
        induction' s using Finset.induction with a s ha ih
        · simp
        · rw [Finset.sum_insert ha, Finset.sum_insert ha]
          have h_add : ENat.toENNReal ((fiber a).encard + ∑ y ∈ s, (fiber y).encard) =
              ENat.toENNReal (fiber a).encard + ENat.toENNReal (∑ y ∈ s, (fiber y).encard) := by
            exact ENat.toENNReal_add (fiber a).encard (∑ y ∈ s, (fiber y).encard)
          rw [h_add, ih]
      exact h_main Yf
    have h_sum_eq : ENat.toENNReal Z.encard = ∑ y ∈ Yf, ENat.toENNReal (X y).encard := by
      rw [h_encard2, h_coe_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have h_y_in_Y : y ∈ Y := by simpa [Yf, Set.Finite.mem_toFinset] using hy
      rw [h_fiber_encard y h_y_in_Y]
    have h_sum_bdd : ∑ y ∈ Yf, ENat.toENNReal (X y).encard ≥
        (Yf.card : ENNReal) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
      have h_each : ∀ y ∈ Yf, ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤ ENat.toENNReal (X y).encard := by
        intro y hy
        have h_y_in_Y : y ∈ Y := by simpa [Yf, Set.Finite.mem_toFinset] using hy
        exact hX_lower y h_y_in_Y
      have h : ∑ y ∈ Yf, ENat.toENNReal (X y).encard ≥ ∑ y ∈ Yf, ENNReal.ofReal (C⁻¹ * δ ^ (-s)) :=
        Finset.sum_le_sum h_each
      have h2 : ∑ y ∈ Yf, ENNReal.ofReal (C⁻¹ * δ ^ (-s)) =
          (Yf.card : ENNReal) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
        rw [Finset.sum_const] <;> simp [mul_comm]
      rw [h2] at h
      exact h
    have h_card : (Yf.card : ENNReal) = ENat.toENNReal Y.encard := by
      have h : Y.encard = ↑Yf.card := by
        rw [←hY_finite.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] <;> rfl
      rw [h] <;> simp
    have h_rpow : δ ^ (-τ) * δ ^ (-s) = δ ^ (-(τ + s)) := by
      have h1 : δ ^ (-τ) * δ ^ (-s) = δ ^ ((-τ) + (-s)) :=
        (Real.rpow_add hδ (-τ) (-s)).symm
      rw [h1]
      have h2 : (-τ) + (-s) = -(τ + s) := by ring
      rw [h2]
    have h_real1 : (C⁻¹ * δ ^ (-τ)) * (C⁻¹ * δ ^ (-s)) = C⁻¹ ^ 2 * δ ^ (-(τ + s)) := by
      have h_group : (C⁻¹ * δ ^ (-τ)) * (C⁻¹ * δ ^ (-s)) =
          (C⁻¹ * C⁻¹) * (δ ^ (-τ) * δ ^ (-s)) := by ring
      rw [h_group, h_rpow] <;> ring
    have h_mul : ENNReal.ofReal (C⁻¹ * δ ^ (-τ)) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) =
        ENNReal.ofReal (C⁻¹ ^ 2 * δ ^ (-(τ + s))) := by
      rw [←ENNReal.ofReal_mul (by positivity)]
      <;> congr 1 <;> exact h_real1
    calc
      ENNReal.ofReal (C⁻¹ ^ 2 * δ ^ (-(τ + s)))
        ≤ ENNReal.ofReal (C⁻¹ * δ ^ (-τ)) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := le_of_eq h_mul.symm
      _ ≤ (ENat.toENNReal Y.encard) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by gcongr
      _ ≤ ∑ y ∈ Yf, ENat.toENNReal (X y).encard := by
        simpa [h_card] using h_sum_bdd
      _ = ENat.toENNReal Z.encard := h_sum_eq.symm

  have hPz_lower : ∀ z ∈ Z,
      ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) :=
    fun z hz => ProductLikeIncidence.covering_lower_bound (hPz_delta z hz)

  have h_rpow2 : δ ^ (-(τ + s)) * δ ^ (-s) = δ ^ (-(τ + 2 * s)) := by
    have h1 : δ ^ (-(τ + s)) * δ ^ (-s) = δ ^ ((-(τ + s)) + (-s)) :=
      (Real.rpow_add hδ (-(τ + s)) (-s)).symm
    rw [h1]
    have h2 : (-(τ + s)) + (-s) = -(τ + 2 * s) := by ring
    rw [h2]
  have h_real2 : (C⁻¹ ^ 2 * δ ^ (-(τ + s))) * (C⁻¹ * δ ^ (-s)) = C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s)) := by
    have h_group : (C⁻¹ ^ 2 * δ ^ (-(τ + s))) * (C⁻¹ * δ ^ (-s)) =
        (C⁻¹ ^ 2 * C⁻¹) * (δ ^ (-(τ + s)) * δ ^ (-s)) := by ring
    rw [h_group, h_rpow2] <;> ring
  have h_mul2 : ENNReal.ofReal (C⁻¹ ^ 2 * δ ^ (-(τ + s))) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) =
      ENNReal.ofReal (C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s))) := by
    rw [←ENNReal.ofReal_mul (by positivity)]
    <;> congr 1 <;> exact h_real2

  calc
    (∑ z ∈ Zf, ENat.toENNReal (dyadicCoveringNumber δ (Pz z)))
      ≥ (Zf.card : ENNReal) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
        have h_each : ∀ z ∈ Zf, ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
            ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) := by
          intro z hz
          have h_z_in_Z : z ∈ Z := by
            simpa [Zf, Set.Finite.mem_toFinset] using hz
          exact hPz_lower z h_z_in_Z
        have h : ∑ z ∈ Zf, ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) ≥
            ∑ z ∈ Zf, ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := Finset.sum_le_sum h_each
        have h2 : ∑ z ∈ Zf, ENNReal.ofReal (C⁻¹ * δ ^ (-s)) =
            (Zf.card : ENNReal) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
          rw [Finset.sum_const] <;> simp [mul_comm]
        rw [h2] at h
        exact h
    _ ≥ ENNReal.ofReal (C⁻¹ ^ 2 * δ ^ (-(τ + s))) *
          ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
        have h_card : (Zf.card : ENNReal) = ENat.toENNReal Z.encard := by
          have h : Z.encard = ↑Zf.card := by
            rw [←hZ_finite.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] <;> rfl
          rw [h] <;> simp
        rw [h_card]
        gcongr
    _ = ENNReal.ofReal (C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s))) := h_mul2

end ProductLikeIncidence.ProductReduction
