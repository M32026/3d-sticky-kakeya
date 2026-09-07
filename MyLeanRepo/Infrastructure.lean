module

/-
# Additional infrastructure for robust projection

Helper lemmas for dyadic cubes, covering numbers, and projections.
These extend the core definitions in `Basic.lean`.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal

namespace bourgain_projection_theorem

/-- Abbrev matching reference code. -/
abbrev productLikeRealLineCopy : Set ℝ → Set (EuclideanSpace ℝ (Fin 1)) := realLineCopy

/-- Abbrev matching reference code. -/
abbrev projectionSet (y : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) → Set ℝ := affineProjection y

/-- Abbrev matching reference code. -/
abbrev projectionSet1D (y : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) → Set (EuclideanSpace ℝ (Fin 1)) := affineProjection1D y

section DyadicScales

lemma dyadicScales_pos {δ : ℝ} (h : δ ∈ dyadicScales) : 0 < δ := by
  rcases h with ⟨n, rfl⟩; positivity

lemma dyadicScales_le_one {δ : ℝ} (h : δ ∈ dyadicScales) : δ ≤ 1 := by
  rcases h with ⟨n, rfl⟩
  have h₂ : (n : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le n
  have h₁ : -(n : ℤ) ≤ 0 := by linarith
  have h₃ : (2 : ℝ) ^ (-(n : ℤ)) ≤ (2 : ℝ) ^ (0 : ℤ) := by
    gcongr <;> norm_num <;> linarith
  simpa using h₃

lemma dyadicScales_pos_and_le_one {δ : ℝ} (h : δ ∈ dyadicScales) :
    0 < δ ∧ δ ≤ 1 :=
  ⟨dyadicScales_pos h, dyadicScales_le_one h⟩

end DyadicScales

section DyadicCubes

lemma dyadicCube_nonempty {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (k : Fin d → ℤ) :
    (dyadicCube δ k).Nonempty := by
  let f : Fin d → ℝ := fun i => δ * (k i : ℝ)
  let e : EuclideanSpace ℝ (Fin d) ≃ (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ
  let x : EuclideanSpace ℝ (Fin d) := e.symm f
  refine ⟨x, ?_⟩
  intro i
  have h₁ : e x = f := by simp [x, e]
  have h₂ : (e x) i = f i := by rw [h₁]
  have h₃ : x i = (e x) i := by rfl
  rw [h₃, h₂]; simp only [f]; exact ⟨by linarith, by linarith⟩

lemma dyadicCube_bounded {d : ℕ} {δ : ℝ} {k : Fin d → ℤ} :
    Bornology.IsBounded (dyadicCube δ k) := by
  let B2 : ℝ := ∑ i : Fin d, (|δ * (k i : ℝ)| + |δ * ((k i : ℝ) + 1)|) ^ 2
  let B : ℝ := Real.sqrt B2 + 1
  have h_main : ∀ x ∈ dyadicCube δ k, ‖x‖ ≤ B := by
    intro x hx
    have h₁ : ‖x‖ = Real.sqrt (∑ i : Fin d, |x i| ^ 2) := EuclideanSpace.norm_eq x
    rw [h₁]
    have h₂ : ∑ i : Fin d, |x i| ^ 2 ≤ B2 := by
      apply Finset.sum_le_sum
      intro i _
      have h₃ : x i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := hx i
      have h₄ : |x i| ≤ |δ * (k i : ℝ)| + |δ * ((k i : ℝ) + 1)| := by
        by_cases h₅ : 0 ≤ x i
        · rw [abs_of_nonneg h₅]
          have h₆ : x i < δ * ((k i : ℝ) + 1) := h₃.2
          have h₇ : 0 ≤ δ * ((k i : ℝ) + 1) := by linarith [h₅, h₆]
          rw [abs_of_nonneg h₇]
          linarith [abs_nonneg (δ * (k i : ℝ))]
        · have h₅' : x i < 0 := by linarith
          rw [abs_of_neg h₅']
          have h₆ : δ * (k i : ℝ) ≤ x i := h₃.1
          have h₇ : δ * (k i : ℝ) ≤ 0 := by linarith
          rw [abs_of_nonpos h₇]
          linarith [abs_nonneg (δ * ((k i : ℝ) + 1))]
      have h₅ : |x i| ^ 2 ≤ (|δ * (k i : ℝ)| + |δ * ((k i : ℝ) + 1)|) ^ 2 := by
        gcongr <;> linarith
      exact h₅
    have h₃ : 0 ≤ B2 := by positivity
    have h₄ : Real.sqrt (∑ i : Fin d, |x i| ^ 2) ≤ Real.sqrt B2 := Real.sqrt_le_sqrt h₂
    have h₅ : Real.sqrt B2 ≤ B := by
      dsimp only [B]; linarith [Real.sqrt_nonneg B2]
    linarith
  exact Metric.isBounded_iff.mpr ⟨2 * B, fun x hx y hy => by
    have hx' : ‖x‖ ≤ B := h_main x hx
    have hy' : ‖y‖ ≤ B := h_main y hy
    have h : dist x y ≤ ‖x‖ + ‖y‖ := by
      simpa [dist_eq_norm] using norm_sub_le x y
    linarith⟩

lemma dyadicCoveringNumber_mono {d : ℕ} {δ : ℝ}
    {A B : Set (EuclideanSpace ℝ (Fin d))} (hAB : A ⊆ B) :
    dyadicCoveringNumber δ A ≤ dyadicCoveringNumber δ B := by
  apply Set.encard_mono
  intro Q hQ
  have hQ1 : Q ∈ dyadicCubes d δ := hQ.1
  have hQ2 : (Q ∩ A).Nonempty := hQ.2
  rcases hQ2 with ⟨x, hxQ, hxA⟩
  exact ⟨hQ1, ⟨x, hxQ, hAB hxA⟩⟩

lemma dyadicCubesMeeting_finite {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : Bornology.IsBounded A) :
    (dyadicCubesMeeting δ A).Finite := by
  by_cases hA_empty : A = ∅
  · rw [hA_empty]
    simp [dyadicCubesMeeting]
  · rcases (Set.nonempty_iff_ne_empty.mpr hA_empty) with ⟨x₀, hx₀⟩
    rcases Metric.isBounded_iff.mp hA with ⟨C, hC⟩
    let R : ℝ := C + ‖x₀‖ + 1
    have hB : ∀ x ∈ A, ∀ i : Fin d, |x i| ≤ R := by
      intro x hx i
      have hdist : dist x x₀ ≤ C := hC hx hx₀
      have h_norm : ‖x - x₀‖ ≤ C := by simpa [dist_eq_norm] using hdist
      have h_eq : x = x₀ + (x - x₀) := by abel
      have h_tri : ‖x₀ + (x - x₀)‖ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
      have h_eq2 : ‖x‖ = ‖x₀ + (x - x₀)‖ := by
        congr 1 <;> exact h_eq
      have h₁ : ‖x‖ ≤ ‖x₀‖ + C := by
        rw [h_eq2]; linarith [h_tri, h_norm]
      have h₂ : |x i| ≤ ‖x‖ := by
        have h₃ : |x i| ^ 2 ≤ ∑ j : Fin d, |x j| ^ 2 := by
          apply Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
        have h₄ : 0 ≤ |x i| := by positivity
        have h₅ : Real.sqrt (|x i| ^ 2) = |x i| := by
          have h₅₁ : |x i| ^ 2 = (x i) ^ 2 := by rw [sq_abs]
          rw [h₅₁, Real.sqrt_sq_eq_abs]
        have h₆ : Real.sqrt (|x i| ^ 2) ≤ Real.sqrt (∑ j : Fin d, |x j| ^ 2) := Real.sqrt_le_sqrt h₃
        have h₇ : ‖x‖ = Real.sqrt (∑ j : Fin d, |x j| ^ 2) := EuclideanSpace.norm_eq x
        rw [h₇]; rw [h₅] at h₆; exact h₆
      linarith
    let K : Set (Fin d → ℤ) := {k | ∀ i, -R / δ - 1 ≤ (k i : ℝ) ∧ (k i : ℝ) ≤ R / δ + 1}
    have hK_finite : K.Finite := by
      let lo (i : Fin d) : ℤ := ⌊-R / δ - 1⌋
      let hi (i : Fin d) : ℤ := ⌈R / δ + 1⌉
      have h₁ : K ⊆ Set.univ.pi (fun i : Fin d => Set.Icc (lo i) (hi i)) := by
        intro k hk; intro i _
        have h_floor : (lo i : ℝ) ≤ -R / δ - 1 := Int.floor_le (-R / δ - 1)
        have h_ceil : R / δ + 1 ≤ (hi i : ℝ) := Int.le_ceil (R / δ + 1)
        have h_lo : (lo i : ℝ) ≤ (k i : ℝ) := by linarith [h_floor, (hk i).1]
        have h_hi : (k i : ℝ) ≤ (hi i : ℝ) := by linarith [h_ceil, (hk i).2]
        exact ⟨Int.cast_le.mp h_lo, Int.cast_le.mp h_hi⟩
      apply Set.Finite.subset _ h₁
      exact Set.Finite.pi (fun i => Set.finite_Icc (lo i) (hi i))
    have h_main : dyadicCubesMeeting δ A ⊆ Set.image (fun k : Fin d → ℤ => dyadicCube δ k) K := by
      intro Q hQ
      rcases hQ with ⟨⟨k, rfl⟩, ⟨x, hxQ, hxA⟩⟩
      have h₂ : k ∈ K := by
        simp only [K, Set.mem_setOf_eq]; intro i
        have h₃ : |x i| ≤ R := hB x hxA i
        have h₄ : -R ≤ x i := (abs_le.mp h₃).1
        have h₅ : x i ≤ R := (abs_le.mp h₃).2
        have h₆ : δ * (k i : ℝ) ≤ x i := (hxQ i).1
        have h₇ : x i < δ * ((k i : ℝ) + 1) := (hxQ i).2
        constructor
        · have h₈ : -R < δ * ((k i : ℝ) + 1) := by linarith
          have h₉ : (-R : ℝ) / δ < (k i : ℝ) + 1 := by
            have h₁₀ : (-R : ℝ) / δ < (δ * ((k i : ℝ) + 1)) / δ := by gcongr
            have h₁₁ : (δ * ((k i : ℝ) + 1)) / δ = (k i : ℝ) + 1 := by
              field_simp [hδ.ne'] <;> ring
            rw [h₁₁] at h₁₀; exact h₁₀
          linarith
        · have h₈ : (k i : ℝ) ≤ R / δ := by
            have h₉ : δ * (k i : ℝ) ≤ R := by linarith
            have h₁₀ : (δ * (k i : ℝ)) / δ ≤ R / δ := by gcongr
            have h₁₁ : (δ * (k i : ℝ)) / δ = (k i : ℝ) := by
              field_simp [hδ.ne'] <;> ring
            rw [h₁₁] at h₁₀; exact h₁₀
          linarith
      exact ⟨k, h₂, rfl⟩
    exact Set.Finite.subset (hK_finite.image _) h_main

lemma dyadicCoveringNumber_lt_top {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : Bornology.IsBounded A) :
    dyadicCoveringNumber δ A < ⊤ := by
  have h := dyadicCubesMeeting_finite hδ hA
  exact Set.Finite.encard_lt_top h

end DyadicCubes

section RealLineCopy

lemma productLikeRealLineCopy_bounded {A : Set ℝ} (hA : Bornology.IsBounded A) :
    Bornology.IsBounded (productLikeRealLineCopy A) := by
  by_cases hA_empty : A = ∅
  · rw [hA_empty]
    simp [productLikeRealLineCopy]
    <;> exact Bornology.isBounded_empty
  · have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
    rcases hA_nonempty with ⟨a₀, ha₀⟩
    rcases Metric.isBounded_iff.mp hA with ⟨C, hC⟩
    let M : ℝ := C + |a₀| + 1
    have h_main : ∀ (x : EuclideanSpace ℝ (Fin 1)), x ∈ productLikeRealLineCopy A → ‖x‖ ≤ M := by
      intro x hx
      have h₁ : x 0 ∈ A := hx
      have h₂ : dist (x 0) a₀ ≤ C := hC h₁ ha₀
      have h₃ : |x 0 - a₀| ≤ C := by simpa [Real.dist_eq] using h₂
      have h₄ : |x 0| ≤ |x 0 - a₀| + |a₀| := by
        calc |x 0| = |(x 0 - a₀) + a₀| := by ring_nf
          _ ≤ |x 0 - a₀| + |a₀| := by exact abs_add_le (x.ofLp 0 - a₀) a₀
      have h₅ : |x 0| ≤ M := by linarith
      have h₆ : ‖x‖ = |x 0| := by
        have h₇ : ‖x‖ = Real.sqrt (∑ i : Fin 1, |x i| ^ 2) := EuclideanSpace.norm_eq x
        rw [h₇]
        have h₈ : (∑ i : Fin 1, |x i| ^ 2) = |x 0| ^ 2 := by
          simp [Finset.sum_singleton] <;> ring
        rw [h₈, Real.sqrt_sq (abs_nonneg (x 0))]
      rw [h₆]; exact h₅
    exact Metric.isBounded_iff.mpr ⟨2 * M, fun x hx y hy => by
      have hx' : ‖x‖ ≤ M := h_main x hx
      have hy' : ‖y‖ ≤ M := h_main y hy
      have h : dist x y ≤ ‖x‖ + ‖y‖ := by simpa [dist_eq_norm] using norm_sub_le x y
      linarith⟩

lemma productLikeRealLineCopy_nonempty {A : Set ℝ} (hA : A.Nonempty) :
    (productLikeRealLineCopy A).Nonempty := by
  rcases hA with ⟨a, ha⟩
  let e : EuclideanSpace ℝ (Fin 1) ≃ (Fin 1 → ℝ) := EuclideanSpace.equiv (Fin 1) ℝ
  let f : Fin 1 → ℝ := fun _ => a
  let x : EuclideanSpace ℝ (Fin 1) := e.symm f
  have h₁ : e x = f := by simp [x, e]
  have h₂ : x 0 = a := by
    have h₃ : x 0 = (e x) 0 := by rfl
    rw [h₃, h₁] <;> rfl
  have h₃ : x ∈ productLikeRealLineCopy A := by
    simpa [productLikeRealLineCopy, realLineCopy] using h₂ ▸ ha
  exact ⟨x, h₃⟩

end RealLineCopy

section IsDeltaSCSet

lemma IsDeltaSCSet.mono {d : ℕ} {δ s C C' : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (h : IsDeltaSCSet δ s C P) (hC : C ≤ C') :
    IsDeltaSCSet δ s C' P := by
  rcases h with ⟨hBdd, hNonempty, hd, hδdyadic, hδpos, hsnonneg, hsdim, hCpos, hMain⟩
  refine ⟨hBdd, hNonempty, hd, hδdyadic, hδpos, hsnonneg, hsdim, by
    have hC'pos : 0 < C' := by linarith
    exact hC'pos, ?_⟩
  intro r Q hr hQ' hδr hr1
  have h₄ := hMain hr hQ' hδr hr1
  have h₅ : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC
  calc
    ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q))
      ≤ ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ P) * ENNReal.ofReal (r ^ s) := h₄
    _ ≤ ENNReal.ofReal C' * ENat.toENNReal (dyadicCoveringNumber δ P) * ENNReal.ofReal (r ^ s) := by
      gcongr

end IsDeltaSCSet

/-- The real grid `δℤ` used in the product-like incidence proposition. -/
def productLikeIntegerGrid (δ : ℝ) : Set ℝ :=
  {x | ∃ k : ℤ, x = δ * (k : ℝ)}

end bourgain_projection_theorem
