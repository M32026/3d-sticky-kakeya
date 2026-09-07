module

/-
# Product-like incidence proof: elementary steps (Proposition A.7)

This file formalizes Steps 1-3 of the proof of `product_like_incidence_sum_product`
from OS Appendix A.7:

1. `T(y) := ⋃_{x ∈ X_y} 𝒯z(x,y)` is a `(δ, 2s)`-set.
2. `π_y(T(x,y)) ⊂ B(x, 2δ)`, hence `π_y(T(y)) ⊂ X_y(2δ)`.
3. A refinement `T̄ ⊂ T` is also a `(δ, 2s)`-set via averaging.

Step 4 (Bourgain projection contradiction) is left for a separate module.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.DualityBridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped BigOperators

namespace ProductLikeIncidence

attribute [local instance] Classical.propDecidable

/-- Construct a 2D Euclidean point from coordinates. -/
def mkPoint2 (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i : Fin 2 =>
    if i = 0 then x else y

@[simp] lemma mkPoint2_fst (x y : ℝ) : (mkPoint2 x y) 0 = x := by simp [mkPoint2]
@[simp] lemma mkPoint2_snd (x y : ℝ) : (mkPoint2 x y) 1 = y := by simp [mkPoint2]

/-- The projection `π_y(a,b) := a*y + b` from the parameter plane to the real line.
This maps tube parameters to the x-coordinate at height y. -/
def piY (y : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  p 0 * y + p 1

/-!
## Step 2: Projection containment

For a tube `T` through the point `(x,y)`, the `π_y`-image of its canonical
parameter cube lies within `2δ` of `x`.
-/

/-- **Step 2, core lemma.** If `T` is an Appendix-A dyadic `δ`-tube containing
the point `z = (x,y)` with `y ∈ [0,1]`, then every parameter point `p` in the
canonical parameter cube of `T` satisfies `|π_y(p) - x| < 2δ`. -/
lemma tube_projection_near_point {δ x y : ℝ}
    {T : Set (EuclideanSpace ℝ (Fin 2))}
    (hδ : 0 < δ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hT : T ∈ appendixDyadicTubes δ)
    (z : EuclideanSpace ℝ (Fin 2))
    (hz0 : z 0 = x) (hz1 : z 1 = y)
    (hpoint : z ∈ T) :
    ∀ p ∈ productLikeAppendixDyadicTubeCanonicalParameterCube δ T,
      |piY y p - x| < 2 * δ := by
  set P := productLikeAppendixDyadicTubeCanonicalParameterCube δ T with hPdef
  have hP_cube : P ∈ dyadicCubesMeeting (d := 2) δ appendixParameterStrip := by
    simp [hPdef, productLikeAppendixDyadicTubeCanonicalParameterCube, hT]
    <;> exact (Classical.choose_spec hT).1
  have hP_image : appendixDualOfParameterSet P = T := by
    simp [hPdef, productLikeAppendixDyadicTubeCanonicalParameterCube, hT]
    <;> exact (Classical.choose_spec hT).2
  have hP_dyadic : P ∈ dyadicCubes 2 δ := hP_cube.1
  rcases hP_dyadic with ⟨k, hk⟩
  have hq : ∃ (q : EuclideanSpace ℝ (Fin 2)),
      q ∈ P ∧ z ∈ appendixDualLineMap q := by
    have h : z ∈ appendixDualOfParameterSet P := hP_image ▸ hpoint
    simpa [appendixDualOfParameterSet] using h
  rcases hq with ⟨q, hqP, hqline⟩
  have h_eq : x = q 0 * y + q 1 := by
    have h : z 0 = q 0 * z 1 + q 1 := by
      simpa [appendixDualLineMap, appendixDualLine] using hqline
    rw [hz0, hz1] at h
    exact h
  intro p hp
  have h_p01 : δ * (k 0 : ℝ) ≤ p 0 := by rw [hk] at hp; exact (hp 0).1
  have h_p02 : p 0 < δ * ((k 0 : ℝ) + 1) := by rw [hk] at hp; exact (hp 0).2
  have h_p11 : δ * (k 1 : ℝ) ≤ p 1 := by rw [hk] at hp; exact (hp 1).1
  have h_p12 : p 1 < δ * ((k 1 : ℝ) + 1) := by rw [hk] at hp; exact (hp 1).2
  have h_q01 : δ * (k 0 : ℝ) ≤ q 0 := by rw [hk] at hqP; exact (hqP 0).1
  have h_q02 : q 0 < δ * ((k 0 : ℝ) + 1) := by rw [hk] at hqP; exact (hqP 0).2
  have h_q11 : δ * (k 1 : ℝ) ≤ q 1 := by rw [hk] at hqP; exact (hqP 1).1
  have h_q12 : q 1 < δ * ((k 1 : ℝ) + 1) := by rw [hk] at hqP; exact (hqP 1).2
  have h1 : |p 0 - q 0| < δ := by
    have h11 : p 0 - q 0 > -δ := by linarith
    have h12 : p 0 - q 0 < δ := by linarith
    rw [abs_lt]; exact ⟨h11, h12⟩
  have h2 : |p 1 - q 1| < δ := by
    have h21 : p 1 - q 1 > -δ := by linarith
    have h22 : p 1 - q 1 < δ := by linarith
    rw [abs_lt]; exact ⟨h21, h22⟩
  have h4 : |(p 0 - q 0) * y + (p 1 - q 1)| ≤
      |p 0 - q 0| * |y| + |p 1 - q 1| := by
    have h41 : |(p 0 - q 0) * y + (p 1 - q 1)| ≤
        |(p 0 - q 0) * y| + |p 1 - q 1| := by exact abs_add_le ((p.ofLp 0 - q.ofLp 0) * y) (p.ofLp 1 - q.ofLp 1)
    have h42 : |(p 0 - q 0) * y| = |p 0 - q 0| * |y| := by rw [abs_mul]
    rw [h42] at h41
    exact h41
  have h5 : |y| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have h6 : |p 0 - q 0| * |y| + |p 1 - q 1| < 2 * δ := by
    calc
      |p 0 - q 0| * |y| + |p 1 - q 1|
        ≤ |p 0 - q 0| * 1 + |p 1 - q 1| := by gcongr <;> linarith
      _ = |p 0 - q 0| + |p 1 - q 1| := by ring
      _ < δ + δ := by linarith
      _ = 2 * δ := by ring
  have h_goal : |piY y p - x| = |(p 0 - q 0) * y + (p 1 - q 1)| := by
    simp only [piY, h_eq] <;> ring_nf
  rw [h_goal]
  exact lt_of_le_of_lt h4 h6

/-- **Step 2, family version.** For the family `T(y) := ⋃_{x ∈ X_y} 𝒯z(x,y)`,
every parameter point `p` in the parameter set of `T(y)` satisfies
`|π_y(p) - x| < 2δ` for some `x ∈ X_y`. Consequently, `π_y(T(y))` is contained
in the `2δ`-neighborhood of `X_y`. -/
lemma family_projection_near_Xy {δ y : ℝ} {X_y : Set ℝ}
    {𝒯z : EuclideanSpace ℝ (Fin 2) → Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hδ : 0 < δ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hX : X_y ⊆ productLikeUnitGrid δ)
    (hTubes : ∀ x ∈ X_y, 𝒯z (mkPoint2 x y) ⊆ appendixDyadicTubes δ)
    (hpoint : ∀ x ∈ X_y, ∀ T ∈ 𝒯z (mkPoint2 x y), (mkPoint2 x y) ∈ T) :
    ∀ p ∈ productLikeAppendixDyadicTubeParameterSet δ
        (⋃ x ∈ X_y, 𝒯z (mkPoint2 x y)),
      ∃ x ∈ X_y, |piY y p - x| < 2 * δ := by
  intro p hp
  have h_main : ∃ (x : ℝ), x ∈ X_y ∧ ∃ (T : Set (EuclideanSpace ℝ (Fin 2))),
      T ∈ 𝒯z (mkPoint2 x y) ∧
      p ∈ productLikeAppendixDyadicTubeCanonicalParameterCube δ T := by
    simpa [productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion,
      Set.mem_image, Set.mem_iUnion] using hp
  rcases h_main with ⟨x, hxX, T, hxT, hpT⟩
  have hT_in : T ∈ appendixDyadicTubes δ := hTubes x hxX hxT
  have hz0 : ((mkPoint2 x y) : EuclideanSpace ℝ (Fin 2)) 0 = x := by simp
  have hz1 : ((mkPoint2 x y) : EuclideanSpace ℝ (Fin 2)) 1 = y := by simp
  have h_main := tube_projection_near_point hδ hy0 hy1 hT_in
    (mkPoint2 x y) hz0 hz1 (hpoint x hxX T hxT)
  exact ⟨x, hxX, h_main p hpT⟩

/-!
## Bounded overlap geometric fact

A single Appendix-A dyadic tube can pass through at most `O(1)` points
`(x,y)` with `x ∈ X_y ⊂ δℤ`, because the set of such `x` lies in an
interval of length at most `2δ`.
-/

/-- The set of `x ∈ X_y` such that `(x,y) ∈ T` is finite and has cardinality
at most `3`, since these `x` lie in an interval of length `≤ 2δ` and are
`δ`-separated. -/
lemma bounded_overlap {δ y : ℝ} {X_y : Set ℝ}
    {T : Set (EuclideanSpace ℝ (Fin 2))}
    (hδ : 0 < δ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hX : X_y ⊆ productLikeUnitGrid δ)
    (hT : T ∈ appendixDyadicTubes δ) :
    let S : Set ℝ := {x ∈ X_y | (mkPoint2 x y) ∈ T}
    S.Finite ∧ S.encard ≤ 3 := by
  let S : Set ℝ := {x ∈ X_y | (mkPoint2 x y) ∈ T}
  have hS_sub : S ⊆ X_y := by intro x hx; exact hx.1
  have hX_grid : ∀ x ∈ X_y, ∃ (k : ℤ), x = δ * (k : ℝ) := by
    intro x hx
    have h1 : x ∈ productLikeUnitGrid δ := hX hx
    rcases h1 with ⟨h2, _⟩
    simpa [productLikeIntegerGrid] using h2
  have h_geom : ∀ (x1 x2 : ℝ), x1 ∈ S → x2 ∈ S → |x1 - x2| < 2 * δ := by
    intro x1 x2 hx1 hx2
    have h1 : (mkPoint2 x1 y) ∈ T := hx1.2
    have h2 : (mkPoint2 x2 y) ∈ T := hx2.2
    set P := productLikeAppendixDyadicTubeCanonicalParameterCube δ T with hPdef
    have hP_cube : P ∈ dyadicCubesMeeting (d := 2) δ appendixParameterStrip := by
      simp [hPdef, productLikeAppendixDyadicTubeCanonicalParameterCube, hT]
      <;> exact (Classical.choose_spec hT).1
    have hP_image : appendixDualOfParameterSet P = T := by
      simp [hPdef, productLikeAppendixDyadicTubeCanonicalParameterCube, hT]
      <;> exact (Classical.choose_spec hT).2
    rcases hP_cube.1 with ⟨k, hk⟩
    have hq1 : ∃ (q1 : EuclideanSpace ℝ (Fin 2)),
        q1 ∈ P ∧ (mkPoint2 x1 y) ∈ appendixDualLineMap q1 := by
      have h : (mkPoint2 x1 y) ∈ appendixDualOfParameterSet P := hP_image ▸ h1
      simpa [appendixDualOfParameterSet] using h
    have hq2 : ∃ (q2 : EuclideanSpace ℝ (Fin 2)),
        q2 ∈ P ∧ (mkPoint2 x2 y) ∈ appendixDualLineMap q2 := by
      have h : (mkPoint2 x2 y) ∈ appendixDualOfParameterSet P := hP_image ▸ h2
      simpa [appendixDualOfParameterSet] using h
    rcases hq1 with ⟨q1, hq1P, hq1line⟩
    rcases hq2 with ⟨q2, hq2P, hq2line⟩
    have h_eq1 : x1 = q1 0 * y + q1 1 := by
      have h : ((mkPoint2 x1 y) : EuclideanSpace ℝ (Fin 2)) 0 =
          q1 0 * ((mkPoint2 x1 y) : EuclideanSpace ℝ (Fin 2)) 1 + q1 1 := by
        simpa [appendixDualLineMap, appendixDualLine] using hq1line
      simpa using h
    have h_eq2 : x2 = q2 0 * y + q2 1 := by
      have h : ((mkPoint2 x2 y) : EuclideanSpace ℝ (Fin 2)) 0 =
          q2 0 * ((mkPoint2 x2 y) : EuclideanSpace ℝ (Fin 2)) 1 + q2 1 := by
        simpa [appendixDualLineMap, appendixDualLine] using hq2line
      simpa using h
    have hq1_cube : q1 ∈ dyadicCube (d := 2) δ k := by rw [hk] at hq1P; exact hq1P
    have hq2_cube : q2 ∈ dyadicCube (d := 2) δ k := by rw [hk] at hq2P; exact hq2P
    have hdiff1 : |q1 0 - q2 0| < δ := by
      let a := δ * (k 0 : ℝ)
      let b := δ * ((k 0 : ℝ) + 1)
      have h11 : a ≤ q1 0 := (hq1_cube 0).1
      have h12 : q1 0 < b := (hq1_cube 0).2
      have h21 : a ≤ q2 0 := (hq2_cube 0).1
      have h22 : q2 0 < b := (hq2_cube 0).2
      have h : |q1 0 - q2 0| < b - a := by
        have h5 : q1 0 - q2 0 < b - a := by linarith
        have h6 : -(b - a) < q1 0 - q2 0 := by linarith
        exact abs_lt.mpr ⟨h6, h5⟩
      have hba : b - a = δ := by simp [a, b] <;> ring
      rw [hba] at h
      exact h
    have hdiff2 : |q1 1 - q2 1| < δ := by
      let a := δ * (k 1 : ℝ)
      let b := δ * ((k 1 : ℝ) + 1)
      have h11 : a ≤ q1 1 := (hq1_cube 1).1
      have h12 : q1 1 < b := (hq1_cube 1).2
      have h21 : a ≤ q2 1 := (hq2_cube 1).1
      have h22 : q2 1 < b := (hq2_cube 1).2
      have h : |q1 1 - q2 1| < b - a := by
        have h5 : q1 1 - q2 1 < b - a := by linarith
        have h6 : -(b - a) < q1 1 - q2 1 := by linarith
        exact abs_lt.mpr ⟨h6, h5⟩
      have hba : b - a = δ := by simp [a, b] <;> ring
      rw [hba] at h
      exact h
    have h_y_abs : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h_bound : |x1 - x2| < 2 * δ := by
      calc
        |x1 - x2|
          = |(q1 0 * y + q1 1) - (q2 0 * y + q2 1)| := by rw [h_eq1, h_eq2]
        _ = |(q1 0 - q2 0) * y + (q1 1 - q2 1)| := by ring_nf
        _ ≤ |q1 0 - q2 0| * |y| + |q1 1 - q2 1| := by
          have h : |(q1 0 - q2 0) * y + (q1 1 - q2 1)| ≤
              |(q1 0 - q2 0) * y| + |q1 1 - q2 1| := by exact abs_add_le ((q1.ofLp 0 - q2.ofLp 0) * y) (q1.ofLp 1 - q2.ofLp 1)
          have h2 : |(q1 0 - q2 0) * y| = |q1 0 - q2 0| * |y| := by rw [abs_mul]
          rw [h2] at h; exact h
        _ ≤ |q1 0 - q2 0| * 1 + |q1 1 - q2 1| := by gcongr <;> linarith
        _ < δ + δ := by linarith
        _ = 2 * δ := by ring
    exact h_bound
  by_cases hS_empty : S = ∅
  · dsimp only
    have h_goal : {x ∈ X_y | (mkPoint2 x y) ∈ T}.Finite ∧
        {x ∈ X_y | (mkPoint2 x y) ∈ T}.encard ≤ 3 := by
      have h_eq : {x ∈ X_y | (mkPoint2 x y) ∈ T} = (∅ : Set ℝ) := hS_empty
      rw [h_eq]
      simp
    exact h_goal
  · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
    rcases hS_nonempty with ⟨x0, hx0⟩
    rcases hX_grid x0 (hS_sub hx0) with ⟨k0, hk0⟩
    let K : Set ℤ := {k : ℤ | δ * (k : ℝ) ∈ S}
    have hk0_in_K : k0 ∈ K := by
      simpa [K, hk0] using hx0
    have hK_bdd : ∀ k ∈ K, |k - k0| ≤ 1 := by
      intro k hk
      have h3 : |δ * (k : ℝ) - δ * (k0 : ℝ)| < 2 * δ :=
        h_geom (δ * (k : ℝ)) (δ * (k0 : ℝ)) hk hk0_in_K
      have h4 : |(k : ℝ) - (k0 : ℝ)| < 2 := by
        have h5 : |δ * ((k : ℝ) - (k0 : ℝ))| < 2 * δ := by simpa [mul_sub] using h3
        have h6 : |δ| * |(k : ℝ) - (k0 : ℝ)| < 2 * δ := by simpa [abs_mul] using h5
        have h7 : |δ| = δ := abs_of_pos hδ
        rw [h7] at h6
        nlinarith
      have h5 : -2 < (k : ℝ) - (k0 : ℝ) := (abs_lt.mp h4).1
      have h6 : (k : ℝ) - (k0 : ℝ) < 2 := (abs_lt.mp h4).2
      have h7 : -2 < k - k0 := by exact_mod_cast h5
      have h8 : k - k0 < 2 := by exact_mod_cast h6
      have h9 : k - k0 ≤ 1 := by omega
      have h10 : -1 ≤ k - k0 := by omega
      have h11 : |k - k0| ≤ 1 := by
        rw [abs_le] <;> omega
      exact h11
    let K' : Finset ℤ := Finset.Icc (k0 - 1) (k0 + 1)
    have hK_sub : K ⊆ (K' : Set ℤ) := by
      intro k hk
      have h : |k - k0| ≤ 1 := hK_bdd k hk
      have h' : k0 - 1 ≤ k ∧ k ≤ k0 + 1 := by
        rw [abs_le] at h
        constructor <;> omega
      simp only [K', Finset.mem_coe, Finset.mem_Icc]
      exact ⟨h'.1, h'.2⟩
    have hK_fin : K.Finite := Set.Finite.subset K'.finite_toSet hK_sub
    have hK_card : K.encard ≤ 3 := by
      calc
        K.encard ≤ (K' : Set ℤ).encard := Set.encard_mono hK_sub
        _ = ↑K'.card := by simp
        _ = 3 := by
          have h_card : K'.card = 3 := by
            have h1 : K' = Finset.Icc (k0 - 1) (k0 + 1) := by rfl
            rw [h1]
            simp [Finset.Icc_eq_empty_of_lt]
            <;> omega
          rw [h_card] <;> norm_num
    have hS_image : S = (fun (k : ℤ) => δ * (k : ℝ)) '' K := by
      ext x
      simp only [Set.mem_image, K]
      constructor
      · intro hx
        rcases hX_grid x (hS_sub hx) with ⟨k, hk⟩
        exact ⟨k, by simpa [hk] using hx, Eq.symm hk⟩
      · rintro ⟨k, hk, rfl⟩; exact hk
    have hS_fin : S.Finite := by rw [hS_image]; exact hK_fin.image _
    have hS_encard : S.encard ≤ K.encard := by rw [hS_image]; exact Set.encard_image_le _ _
    have h_final : S.encard ≤ 3 := le_trans hS_encard hK_card
    dsimp only
    exact ⟨hS_fin, h_final⟩

/-!
## Helper lemmas for Step 1
-/

/-- If two dyadic cubes of the same scale have nonempty intersection,
their grid indices are equal (hence the cubes are equal). -/
lemma dyadicCubesSameScaleEqual {δ : ℝ} (hδ : 0 < δ) {d : ℕ}
    {k j : Fin d → ℤ} (h : (dyadicCube δ k ∩ dyadicCube δ j).Nonempty) :
    k = j := by
  rcases h with ⟨p, hp1, hp2⟩
  ext i
  have h1 : δ * (k i : ℝ) ≤ p i ∧ p i < δ * ((k i : ℝ) + 1) := by
    simpa [Set.mem_Ico] using hp1 i
  have h2 : δ * (j i : ℝ) ≤ p i ∧ p i < δ * ((j i : ℝ) + 1) := by
    simpa [Set.mem_Ico] using hp2 i
  by_cases h3 : k i ≤ j i
  · by_contra h4
    have h5 : j i ≥ k i + 1 := by omega
    have h6 : δ * ((k i : ℝ) + 1) ≤ δ * (j i : ℝ) := by
      gcongr <;> norm_cast <;> linarith
    linarith
  · have h4 : k i > j i := by omega
    have h5 : k i ≥ j i + 1 := by omega
    have h6 : δ * ((j i : ℝ) + 1) ≤ δ * (k i : ℝ) := by
      gcongr <;> norm_cast <;> linarith
    linarith

/-- For a tube family `𝒯`, the dyadic covering number of its parameter
set equals the cardinality of `𝒯`. -/
lemma tubeParamCoveringEqCard {δ : ℝ} (hδ : 0 < δ)
    {𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hsub : 𝒯 ⊆ appendixDyadicTubes δ) :
    dyadicCoveringNumber δ (productLikeAppendixDyadicTubeParameterSet δ 𝒯) = 𝒯.encard := by
  let canon := productLikeAppendixDyadicTubeCanonicalParameterCube δ
  let paramSet := productLikeAppendixDyadicTubeParameterSet δ 𝒯
  have h1 : ∀ T ∈ 𝒯, canon T ∈ dyadicCubes 2 δ ∧
      appendixDualOfParameterSet (canon T) = T := by
    intro T hT
    have hT' : T ∈ appendixDyadicTubes δ := hsub hT
    have hP_cube : canon T ∈ dyadicCubesMeeting (d := 2) δ appendixParameterStrip := by
      simp [canon, productLikeAppendixDyadicTubeCanonicalParameterCube, hT']
      <;> exact (Classical.choose_spec hT').1
    have hP_image : appendixDualOfParameterSet (canon T) = T := by
      simp [canon, productLikeAppendixDyadicTubeCanonicalParameterCube, hT']
      <;> exact (Classical.choose_spec hT').2
    exact ⟨hP_cube.1, hP_image⟩
  have h_canon_cube : ∀ T ∈ 𝒯, canon T ∈ dyadicCubes 2 δ :=
    fun T hT => (h1 T hT).1
  have h_canon_inj : Set.InjOn canon 𝒯 := by
    intro T1 hT1 T2 hT2 h
    have h_eq1 : appendixDualOfParameterSet (canon T1) = T1 := (h1 T1 hT1).2
    have h_eq2 : appendixDualOfParameterSet (canon T2) = T2 := (h1 T2 hT2).2
    rw [h] at h_eq1
    exact h_eq1.symm.trans h_eq2
  have h_main : dyadicCubesMeeting (d := 2) δ paramSet = canon '' 𝒯 := by
    ext D
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hD_cube, ⟨p, hpD, hpP⟩⟩
      simp only [paramSet, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion, Set.mem_image] at hpP
      rcases hpP with ⟨C, ⟨T, hT, rfl⟩, hpC⟩
      rcases hD_cube with ⟨k, rfl⟩
      rcases h_canon_cube T hT with ⟨j, hj⟩
      have hpC' : p ∈ dyadicCube δ j := by
        have h : p ∈ canon T := hpC
        rw [hj] at h
        exact h
      have h_inter : (dyadicCube δ k ∩ dyadicCube δ j).Nonempty := ⟨p, hpD, hpC'⟩
      have h_eq : k = j := dyadicCubesSameScaleEqual hδ h_inter
      have hD_eq : dyadicCube δ k = canon T := by rw [h_eq, hj]
      exact ⟨T, hT, hD_eq.symm⟩
    · rintro ⟨T, hT, rfl⟩
      have hC_cube : canon T ∈ dyadicCubes 2 δ := h_canon_cube T hT
      have hC_nonempty : (canon T).Nonempty := by
        rcases hC_cube with ⟨k, hk⟩
        have h : (dyadicCube δ k).Nonempty := dyadicCube_nonempty hδ k
        exact hk.symm ▸ h
      rcases hC_nonempty with ⟨p, hp⟩
      have hpP : p ∈ paramSet := by
        simp only [paramSet, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion, Set.mem_image]
        exact ⟨canon T, ⟨T, hT, rfl⟩, hp⟩
      exact ⟨hC_cube, ⟨p, hp, hpP⟩⟩
  have h_encard : (canon '' 𝒯).encard = 𝒯.encard := by
    exact Set.InjOn.encard_image h_canon_inj
  rw [dyadicCoveringNumber, h_main, h_encard]

/-- For `A ⊆ δℤ`, the 1D dyadic covering number of its real-line copy
equals the cardinality of `A`. -/
lemma realLineCoveringEqCard {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA : A ⊆ productLikeIntegerGrid δ) :
    dyadicCoveringNumber δ (productLikeRealLineCopy A) = A.encard := by
  classical
  let e : EuclideanSpace ℝ (Fin 1) ≃ (Fin 1 → ℝ) := EuclideanSpace.equiv (Fin 1) ℝ
  let k_of : ℝ → ℤ := fun x =>
    if h : x ∈ A then
      let h_exists : ∃ (k : ℤ), x = δ * (k : ℝ) := by
        simpa [productLikeIntegerGrid] using hA h
      Classical.choose h_exists
    else 0
  let cube_of : ℝ → Set (EuclideanSpace ℝ (Fin 1)) := fun x =>
    dyadicCube δ (fun (_ : Fin 1) => k_of x)
  have hk : ∀ (x : ℝ), x ∈ A → x = δ * ((k_of x : ℝ)) := by
    intro x hx
    let h_exists : ∃ (k : ℤ), x = δ * (k : ℝ) := by
      simpa [productLikeIntegerGrid] using hA hx
    have h_def : k_of x = Classical.choose h_exists := by
      simp [k_of, hx, h_exists] <;> rfl
    rw [h_def]
    exact Classical.choose_spec h_exists
  have h_inj : Set.InjOn cube_of A := by
    intro x1 hx1 x2 hx2 h
    have h1 : x1 = δ * ((k_of x1 : ℝ)) := hk x1 hx1
    have h2 : x2 = δ * ((k_of x2 : ℝ)) := hk x2 hx2
    have h3 : k_of x1 = k_of x2 := by
      have h_set_eq : dyadicCube δ (fun (_ : Fin 1) => k_of x1) = dyadicCube δ (fun (_ : Fin 1) => k_of x2) := by
        simpa [cube_of] using h
      let f : Fin 1 → ℝ := fun _ => δ * (k_of x1 : ℝ)
      let q : EuclideanSpace ℝ (Fin 1) := e.symm f
      have hq : q ∈ dyadicCube δ (fun (_ : Fin 1) => k_of x1) := by
        intro i
        have hqi : q i = f i := by rfl
        rw [hqi]
        fin_cases i
        · simp only [f, Set.mem_Ico]
          constructor
          · exact le_refl _
          · have h_pos : 0 < δ := hδ
            have h : δ * (k_of x1 : ℝ) < δ * ((k_of x1 : ℝ) + 1) := by gcongr <;> linarith
            exact h
      have h4 : (fun (_ : Fin 1) => k_of x1) = (fun (_ : Fin 1) => k_of x2) :=
        dyadicCubesSameScaleEqual hδ ⟨q, hq, by rw [h_set_eq] at *; exact hq⟩
      exact congr_fun h4 0
    rw [h1, h2, h3]
  have h_image : cube_of '' A = dyadicCubesMeeting δ (productLikeRealLineCopy A) := by
    ext D
    simp only [Set.mem_image, dyadicCubesMeeting, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hk' : x = δ * ((k_of x : ℝ)) := hk x hx
      have hD_cube : cube_of x ∈ dyadicCubes 1 δ := by
        exact ⟨(fun _ => k_of x), rfl⟩
      let f : Fin 1 → ℝ := fun _ => x
      let p : EuclideanSpace ℝ (Fin 1) := e.symm f
      have hpD : p ∈ cube_of x := by
        intro i
        have hpi : p i = f i := by rfl
        rw [hpi]
        fin_cases i
        · have h_x_eq : x = δ * (k_of x : ℝ) := hk'
          have h_goal1 : δ * (k_of x : ℝ) ≤ x := le_of_eq h_x_eq.symm
          have h_strict : δ * (k_of x : ℝ) < δ * ((k_of x : ℝ) + 1) := by
            have h' : (k_of x : ℝ) < (k_of x : ℝ) + 1 := by linarith
            exact mul_lt_mul_of_pos_left h' hδ
          have h_goal2 : x < δ * ((k_of x : ℝ) + 1) := lt_of_eq_of_lt h_x_eq h_strict
          simp only [f, Set.mem_Ico]
          exact ⟨h_goal1, h_goal2⟩
      have hp0 : p 0 = x := by
        have h : p 0 = f 0 := by rfl
        rw [h] <;> rfl
      have hpA : p ∈ productLikeRealLineCopy A := by
        dsimp only [productLikeRealLineCopy, realLineCopy]
        have h5 : p 0 ∈ A := by rw [hp0]; exact hx
        exact h5
      exact ⟨hD_cube, ⟨p, hpD, hpA⟩⟩
    · rintro ⟨hD_cube, hne⟩
      rcases hne with ⟨p, hpD, hpA⟩
      let x0 : ℝ := p 0
      have hpa : x0 ∈ A := by
        have h : p ∈ realLineCopy A := by exact_mod_cast hpA
        have h2 : p 0 ∈ A := by simpa [realLineCopy] using h
        simpa [x0] using h2
      rcases hD_cube with ⟨k, hk_eq⟩
      have h1 : x0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) := by
        rw [hk_eq] at hpD; exact hpD 0
      have h_exists : ∃ (m : ℤ), x0 = δ * (m : ℝ) := by
        simpa [productLikeIntegerGrid, x0] using hA hpa
      rcases h_exists with ⟨m, hm⟩
      have h4 : δ * (k 0 : ℝ) ≤ x0 := h1.1
      have h5 : x0 < δ * ((k 0 : ℝ) + 1) := h1.2
      have h6 : (k 0 : ℝ) ≤ (m : ℝ) := by
        have h61 : δ * (k 0 : ℝ) ≤ δ * (m : ℝ) := by rw [hm] at *; exact h4
        nlinarith
      have h7 : (m : ℝ) < (k 0 : ℝ) + 1 := by
        have h71 : δ * (m : ℝ) < δ * ((k 0 : ℝ) + 1) := by rw [hm] at *; exact h5
        nlinarith
      have hkm : k 0 = m := by
        have h8 : k 0 ≤ m := by exact_mod_cast h6
        have h9 : m < k 0 + 1 := by exact_mod_cast h7
        omega
      have h_exists2 : ∃ (k' : ℤ), x0 = δ * (k' : ℝ) := by
        simpa [productLikeIntegerGrid, x0] using hA hpa
      have h_def : k_of x0 = Classical.choose h_exists2 := by
        simp [k_of, hpa, h_exists2] <;> rfl
      have h_choice_spec : x0 = δ * ((Classical.choose h_exists2 : ℤ) : ℝ) :=
        Classical.choose_spec h_exists2
      have h_eq_m : (Classical.choose h_exists2 : ℤ) = m := by
        have h12 : δ * ((Classical.choose h_exists2 : ℤ) : ℝ) = x0 := h_choice_spec.symm
        have h13 : δ * ((Classical.choose h_exists2 : ℤ) : ℝ) = δ * (m : ℝ) := by
          rw [h12, hm]
        have h14 : ((Classical.choose h_exists2 : ℤ) : ℝ) = (m : ℝ) := by
          exact (mul_right_inj' hδ.ne').mp h13
        exact_mod_cast h14
      have h2 : k_of x0 = m := by
        rw [h_def, h_eq_m]
      have h3 : k = (fun (_ : Fin 1) => k_of x0) := by
        ext i
        fin_cases i
        <;> simp [hkm, h2]
      have h_eq : cube_of x0 = D := by
        have h10 : cube_of x0 = dyadicCube δ (fun (_ : Fin 1) => k_of x0) := by rfl
        have h11 : dyadicCube δ (fun (_ : Fin 1) => k_of x0) = dyadicCube δ k := by
          rw [h3.symm]
        have h12 : cube_of x0 = dyadicCube δ k := by
          rw [h10, h11]
        rw [h12]
        exact hk_eq.symm
      exact ⟨x0, hpa, h_eq⟩
  have h_encard : (cube_of '' A).encard = A.encard := by
    exact Set.InjOn.encard_image h_inj
  rw [dyadicCoveringNumber, ← h_image, h_encard]

/-- The ratio of two dyadic scales with δ ≤ r is a natural multiple. -/
lemma dyadicScales_ratio_nat {δ r : ℝ} (hδ : δ ∈ dyadicScales) (hr : r ∈ dyadicScales)
    (hδ_le_r : δ ≤ r) : ∃ (N : ℕ), r = (N : ℝ) * δ := by
  rcases hδ with ⟨n, hn⟩
  rcases hr with ⟨m, hm⟩
  have hnm : n ≥ m := by
    by_contra h
    have h' : n < m := by linarith
    have h'' : (2 : ℝ)^(-(n : ℤ)) > (2 : ℝ)^(-(m : ℤ)) := by
      gcongr <;> norm_num <;> linarith
    rw [hn, hm] at hδ_le_r
    linarith
  let N : ℕ := n - m
  use 2^N
  have h1 : (n : ℤ) = (m : ℤ) + (N : ℤ) := by
    simp [N] <;> omega
  have h_goal : (2 : ℝ)^(-(m : ℤ)) = ((2^N : ℕ) : ℝ) * (2 : ℝ)^(-(n : ℤ)) := by
    have h2 : -(m : ℤ) = (N : ℤ) + (-(n : ℤ)) := by omega
    rw [h2]
    have h3 : (2 : ℝ)^((N : ℤ) + (-(n : ℤ))) = (2 : ℝ)^(N : ℤ) * (2 : ℝ)^(-(n : ℤ)) := by
      exact zpow_add₀ (by norm_num) (N : ℤ) (-(n : ℤ))
    rw [h3]
    have h4 : (2 : ℝ)^(N : ℤ) = ((2^N : ℕ) : ℝ) := by norm_cast
    rw [h4] <;> ring
  rw [hn, hm]
  exact h_goal

/-- A dyadic δ-cube that intersects a dyadic r-cube (δ ≤ r, r = N*δ)
is contained in the r-cube. -/
lemma dyadicCubeContainment {d : ℕ} {δ r : ℝ} {k : Fin d → ℤ} {j : Fin d → ℤ}
    (hδ : 0 < δ) (hN : ∃ (N : ℕ), r = (N : ℝ) * δ)
    (h_inter : (dyadicCube δ k ∩ dyadicCube r j).Nonempty) :
    dyadicCube δ k ⊆ dyadicCube r j := by
  rcases hN with ⟨N, hN⟩
  rcases h_inter with ⟨p, hpδ, hpr⟩
  have hpr' : ∀ i, (N : ℝ) * δ * (j i : ℝ) ≤ p i ∧ p i < (N : ℝ) * δ * ((j i : ℝ) + 1) := by
    intro i
    have h := hpr i
    constructor
    · have h' : r * (j i : ℝ) = (N : ℝ) * δ * (j i : ℝ) := by rw [hN] <;> ring
      rw [h'] at h; exact h.1
    · have h' : r * ((j i : ℝ) + 1) = (N : ℝ) * δ * ((j i : ℝ) + 1) := by rw [hN] <;> ring
      rw [h'] at h; exact h.2
  intro q hq
  intro i
  have h1 : N * (j i) ≤ k i := by
    have h11 : (N : ℝ) * δ * (j i : ℝ) ≤ p i := (hpr' i).1
    have h12 : p i < δ * ((k i : ℝ) + 1) := (hpδ i).2
    have h : (N : ℝ) * (j i : ℝ) < (k i : ℝ) + 1 := by nlinarith
    by_contra h2
    have h3 : N * (j i) ≥ k i + 1 := by omega
    have h4 : (N : ℝ) * (j i : ℝ) ≥ (k i : ℝ) + 1 := by exact_mod_cast h3
    linarith
  have h2 : k i + 1 ≤ N * (j i + 1) := by
    have h21 : δ * (k i : ℝ) ≤ p i := (hpδ i).1
    have h22 : p i < (N : ℝ) * δ * ((j i : ℝ) + 1) := (hpr' i).2
    have h : (k i : ℝ) < (N : ℝ) * ((j i : ℝ) + 1) := by nlinarith
    by_contra h3
    have h4 : k i + 1 > N * (j i + 1) := by omega
    have h5 : k i ≥ N * (j i + 1) := by omega
    have h6 : (k i : ℝ) ≥ (N : ℝ) * ((j i : ℝ) + 1) := by exact_mod_cast h5
    linarith
  have h1' : (N : ℝ) * (j i : ℝ) ≤ (k i : ℝ) := by exact_mod_cast h1
  have h2' : (k i : ℝ) + 1 ≤ (N : ℝ) * ((j i : ℝ) + 1) := by exact_mod_cast h2
  have h3 : r * (j i : ℝ) ≤ q i := by
    calc r * (j i : ℝ) = (N : ℝ) * δ * (j i : ℝ) := by rw [hN] <;> ring
      _ = δ * ((N : ℝ) * (j i : ℝ)) := by ring
      _ ≤ δ * (k i : ℝ) := by
        have h5 : (N : ℝ) * (j i : ℝ) ≤ (k i : ℝ) := h1'
        exact mul_le_mul_of_nonneg_left h5 (by linarith)
      _ ≤ q i := (hq i).1
  have h4 : q i < r * ((j i : ℝ) + 1) := by
    have h5 : δ * ((k i : ℝ) + 1) ≤ (N : ℝ) * δ * ((j i : ℝ) + 1) := by
      have h6 : (k i : ℝ) + 1 ≤ (N : ℝ) * ((j i : ℝ) + 1) := h2'
      have h7 : δ * ((k i : ℝ) + 1) ≤ δ * ((N : ℝ) * ((j i : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h6 (by linarith)
      linarith
    calc q i < δ * ((k i : ℝ) + 1) := (hq i).2
      _ ≤ (N : ℝ) * δ * ((j i : ℝ) + 1) := h5
      _ = r * ((j i : ℝ) + 1) := by rw [hN] <;> ring
  exact ⟨h3, h4⟩

/-- Any (δ,s,C)-set has covering number at least δ^{-s}/C. -/
lemma deltaSCSet_card_lower_bound {d : ℕ} {δ s C : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (hP : IsDeltaSCSet δ s C P) :
    ENat.toENNReal (dyadicCoveringNumber δ P) ≥ ENNReal.ofReal (δ^(-s) / C) := by
  rcases hP with ⟨hBdd, hNonempty, _, hδ_dyadic, hδ, _, _, hC_pos, hMain⟩
  rcases hNonempty with ⟨p, hp⟩
  let k : Fin d → ℤ := fun i => ⌊p i / δ⌋
  let Q : Set (EuclideanSpace ℝ (Fin d)) := dyadicCube δ k
  have hQ_dyadic : Q ∈ dyadicCubes d δ := ⟨k, rfl⟩
  have hpQ : p ∈ Q := by
    intro i
    have h1 : δ * (⌊p i / δ⌋ : ℝ) ≤ p i := by
      have h2 : (⌊p i / δ⌋ : ℝ) ≤ p i / δ := Int.floor_le (p i / δ)
      have h3 : δ * (⌊p i / δ⌋ : ℝ) ≤ δ * (p i / δ) := by gcongr
      have h4 : δ * (p i / δ) = p i := by field_simp [hδ.ne'] <;> ring
      rw [h4] at h3; exact h3
    have h5 : p i < δ * ((⌊p i / δ⌋ : ℝ) + 1) := by
      have h6 : p i / δ < (⌊p i / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (p i / δ)
      have h7 : δ * (p i / δ) < δ * ((⌊p i / δ⌋ : ℝ) + 1) := by gcongr
      have h8 : δ * (p i / δ) = p i := by field_simp [hδ.ne'] <;> ring
      rw [h8] at h7; exact h7
    exact ⟨h1, h5⟩
  have hPQ_nonempty : (P ∩ Q).Nonempty := ⟨p, hp, hpQ⟩
  have hQ_intersect : (Q ∩ (P ∩ Q)).Nonempty := by
    rcases hPQ_nonempty with ⟨p', hpP, hpQ'⟩
    exact ⟨p', hpQ', hpP, hpQ'⟩
  have h9 : (dyadicCubesMeeting δ (P ∩ Q)).Nonempty :=
    ⟨Q, hQ_dyadic, hQ_intersect⟩
  have h10 : dyadicCoveringNumber δ (P ∩ Q) ≠ 0 := by
    have h101 : (dyadicCubesMeeting δ (P ∩ Q)) ≠ ∅ := Set.nonempty_iff_ne_empty.mp h9
    have h102 : (dyadicCubesMeeting δ (P ∩ Q)).encard ≠ 0 := by
      intro h
      have h103 : (dyadicCubesMeeting δ (P ∩ Q)) = ∅ := by
        simpa [dyadicCoveringNumber] using h
      exact h101 h103
    simpa [dyadicCoveringNumber] using h102
  have h11 : 1 ≤ dyadicCoveringNumber δ (P ∩ Q) := by
    have h111 : (dyadicCoveringNumber δ (P ∩ Q)) ≠ 0 := h10
    have : 1 ≤ (dyadicCoveringNumber δ (P ∩ Q)) := by exact Order.one_le_iff_ne_zero.mpr h10
    exact this
  have h_cover_pos : (1 : ENNReal) ≤ ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q)) := by
    exact_mod_cast h11
  have hδ_le_one : δ ≤ 1 := dyadicScales_le_one hδ_dyadic
  have h_main2 := hMain hδ_dyadic hQ_dyadic (by simpa using hδ_dyadic) hδ_le_one
  set X : ENNReal := ENat.toENNReal (dyadicCoveringNumber δ P) with hX
  have h11' : (1 : ENNReal) ≤ ENNReal.ofReal C * X * ENNReal.ofReal (δ ^ s) :=
    le_trans h_cover_pos h_main2
  have h_pos : 0 < C * δ ^ s := by positivity
  set a : ENNReal := ENNReal.ofReal (C * δ ^ s) with ha
  have ha_pos : 0 < a := ENNReal.ofReal_pos.mpr h_pos
  have ha_ne_top : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_mul : ENNReal.ofReal C * X * ENNReal.ofReal (δ ^ s) = a * X := by
    have h : ENNReal.ofReal C * ENNReal.ofReal (δ ^ s) = ENNReal.ofReal (C * δ ^ s) := by
      rw [← ENNReal.ofReal_mul] <;> positivity
    calc
      ENNReal.ofReal C * X * ENNReal.ofReal (δ ^ s)
        = (ENNReal.ofReal C * ENNReal.ofReal (δ ^ s)) * X := by ring
      _ = ENNReal.ofReal (C * δ ^ s) * X := by rw [h]
      _ = a * X := by simp [ha]
  rw [h_mul] at h11'
  have h14 : a * (1 / a) = 1 := ENNReal.mul_div_cancel ha_pos.ne' ha_ne_top
  have h13 : 1 / a ≤ X := by
    have h15 : a * (1 / a) ≤ a * X := by
      rw [h14] <;> exact h11'
    have h16 : (1 / a) * (a * (1 / a)) ≤ (1 / a) * (a * X) := by gcongr
    have h17 : (1 / a) * (a * (1 / a)) = (1 / a) := by
      calc
        (1 / a) * (a * (1 / a)) = ((1 / a) * a) * (1 / a) := by ring
        _ = 1 * (1 / a) := by rw [ENNReal.div_mul_cancel ha_pos.ne' ha_ne_top]
        _ = (1 / a) := by ring
    have h18 : (1 / a) * (a * X) = X := by
      calc
        (1 / a) * (a * X) = ((1 / a) * a) * X := by ring
        _ = 1 * X := by rw [ENNReal.div_mul_cancel ha_pos.ne' ha_ne_top]
        _ = X := by ring
    rw [h17, h18] at h16
    exact h16
  have h16 : 1 / a = ENNReal.ofReal (δ^(-s) / C) := by
    have h171 : a = ENNReal.ofReal (C * δ ^ s) := by simp [ha]
    rw [h171]
    have h_pos2 : 0 < C * δ ^ s := by positivity
    have hnonneg : 0 ≤ C * δ ^ s := by positivity
    have h_mul : ENNReal.ofReal (C * δ ^ s) * ENNReal.ofReal (1 / (C * δ ^ s)) = 1 := by
      have h : ENNReal.ofReal (C * δ ^ s) * ENNReal.ofReal (1 / (C * δ ^ s)) =
          ENNReal.ofReal ((C * δ ^ s) * (1 / (C * δ ^ s))) := by
        rw [ENNReal.ofReal_mul hnonneg]
      rw [h]
      have h2 : (C * δ ^ s) * (1 / (C * δ ^ s)) = 1 := by
        field_simp [h_pos2.ne'] <;> ring
      rw [h2] <;> simp
    have h172 : (1 : ENNReal) / ENNReal.ofReal (C * δ ^ s) = ENNReal.ofReal (1 / (C * δ ^ s)) := by
      set b : ENNReal := ENNReal.ofReal (1 / (C * δ ^ s)) with hb
      have h1 : a * b = 1 := h_mul
      have h_inv : b = 1 / a := by
        calc b
          = 1 * b := by ring
        _ = (a * (1 / a)) * b := by rw [ENNReal.mul_div_cancel ha_pos.ne' ha_ne_top]
        _ = (1 / a) * (a * b) := by ring
        _ = (1 / a) * 1 := by rw [h1]
        _ = 1 / a := by ring
      exact h_inv.symm
    rw [h172]
    have h19 : δ ^ s * δ ^ (-s) = 1 := by
      have hδ' : 0 ≤ δ := by linarith
      have h20 : δ ^ s * δ ^ (-s) = δ ^ (s + (-s)) := by
        rw [← Real.rpow_add hδ] <;> rfl
      rw [h20]
      have h21 : s + (-s) = 0 := by ring
      rw [h21]
      exact Real.rpow_zero δ
    have h18 : 1 / (C * δ ^ s) = δ^(-s) / C := by
      calc 1 / (C * δ ^ s)
        = (δ ^ s * δ ^ (-s)) / (C * δ ^ s) := by rw [h19]
      _ = δ^(-s) / C := by field_simp [h_pos.ne'] <;> ring
    rw [h18]
  rw [h16] at h13
  exact h13

/-- Covering number of a finite union is at most the sum of covering numbers. -/
lemma dyadicCoveringNumber_iUnion_le {d : ℕ} {δ : ℝ} {α : Type*}
    (s : Finset α) (A : α → Set (EuclideanSpace ℝ (Fin d)))
    (hA : ∀ i ∈ s, Bornology.IsBounded (A i)) (hδ : 0 < δ) :
    ENat.toENNReal (dyadicCoveringNumber δ (⋃ i ∈ s, A i)) ≤
      ∑ i ∈ s, ENat.toENNReal (dyadicCoveringNumber δ (A i)) := by
  classical
  let f (i : α) : Finset (Set (EuclideanSpace ℝ (Fin d))) :=
    if h : i ∈ s then (dyadicCubesMeeting_finite hδ (hA i h)).toFinset else ∅
  let BF : Finset (Set (EuclideanSpace ℝ (Fin d))) := s.biUnion f
  have h1 : ∀ i ∈ s, (f i : Set (Set (EuclideanSpace ℝ (Fin d)))) = dyadicCubesMeeting δ (A i) := by
    intro i hi
    have hfi : f i = (dyadicCubesMeeting_finite hδ (hA i hi)).toFinset := by
      simp [f, hi]
    rw [hfi] <;> simp
  have h_main : dyadicCubesMeeting δ (⋃ i ∈ s, A i) ⊆ (BF : Set _) := by
    intro Q hQ
    rcases hQ with ⟨hQ_cube, ⟨p, hpQ, hpU⟩⟩
    rcases Set.mem_iUnion₂.mp hpU with ⟨i, hi, hpA⟩
    have h5 : Q ∈ f i := by
      have hfi : f i = (dyadicCubesMeeting_finite hδ (hA i hi)).toFinset := by
        simp [f, hi]
      rw [hfi]
      simpa using ⟨hQ_cube, ⟨p, hpQ, hpA⟩⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, h5⟩
  let BF_set : Set (Set (EuclideanSpace ℝ (Fin d))) := ↑BF
  have h6 : dyadicCoveringNumber δ (⋃ i ∈ s, A i) ≤ ↑BF.card := by
    have h7 : dyadicCoveringNumber δ (⋃ i ∈ s, A i) = (dyadicCubesMeeting δ (⋃ i ∈ s, A i)).encard := by rfl
    rw [h7]
    have h8 : (dyadicCubesMeeting δ (⋃ i ∈ s, A i)).encard ≤ BF_set.encard := Set.encard_mono h_main
    have h9 : BF_set.encard = ↑BF.card := by
      rw [Set.encard_coe_eq_coe_finsetCard BF]
    rw [h9] at h8
    exact h8
  have h_card_le : BF.card ≤ ∑ i ∈ s, (f i).card := Finset.card_biUnion_le
  have h7 : ENat.toENNReal BF.card ≤ ∑ i ∈ s, ENat.toENNReal ((f i).card) := by
    have h8 : (↑BF.card : ENNReal) ≤ ∑ i ∈ s, (↑(f i).card : ENNReal) := by
      exact_mod_cast h_card_le
    have h9 : ENat.toENNReal BF.card = (↑BF.card : ENNReal) := by simp
    have h10 : ∑ i ∈ s, ENat.toENNReal ((f i).card) = ∑ i ∈ s, (↑(f i).card : ENNReal) := by
      apply Finset.sum_congr rfl
      intro i _
      simp
    rw [h9, h10]
    exact h8
  have h9 : ∀ i ∈ s, ENat.toENNReal ((f i).card) = ENat.toENNReal (dyadicCoveringNumber δ (A i)) := by
    intro i hi
    have h10 : (f i : Set (Set (EuclideanSpace ℝ (Fin d)))) = dyadicCubesMeeting δ (A i) := h1 i hi
    have h11 : (↑(f i).card : ℕ∞) = (dyadicCubesMeeting δ (A i)).encard := by
      have h12 : (↑(f i).card : ℕ∞) = (↑(f i) : Set (Set (EuclideanSpace ℝ (Fin d)))).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard (f i)]
      rw [h12, h10]
    simpa [dyadicCoveringNumber] using congr_arg ENat.toENNReal h11
  have h13 : ∑ i ∈ s, ENat.toENNReal ((f i).card) = ∑ i ∈ s, ENat.toENNReal (dyadicCoveringNumber δ (A i)) :=
    Finset.sum_congr rfl h9
  calc
    ENat.toENNReal (dyadicCoveringNumber δ (⋃ i ∈ s, A i))
      ≤ ENat.toENNReal BF.card := by exact_mod_cast h6
    _ ≤ ∑ i ∈ s, ENat.toENNReal ((f i).card) := h7
    _ = ∑ i ∈ s, ENat.toENNReal (dyadicCoveringNumber δ (A i)) := h13

/-- A bounded subset of the dyadic grid δℤ is finite. -/
lemma finite_bounded_grid_subset {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA1 : A ⊆ productLikeIntegerGrid δ) (hA2 : Bornology.IsBounded A) : A.Finite := by
  by_cases hA_empty : A = ∅
  · rw [hA_empty]; exact Set.finite_empty
  · have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
    rcases hA_nonempty with ⟨x0, hx0⟩
    rcases Metric.isBounded_iff.mp hA2 with ⟨C, hC⟩
    let M : ℝ := C + |x0| + 1
    have h4 : ∀ x ∈ A, |x| ≤ M := by
      intro x hx
      have h5 : dist x x0 ≤ C := hC hx hx0
      have h6 : |x - x0| ≤ C := by simpa [Real.dist_eq] using h5
      have h7 : |x| ≤ |x0| + C := by
        have h_abs : |x0 + (x - x0)| ≤ |x0| + |x - x0| := by exact abs_add_le x0 (x - x0)
        have h_eq : x = x0 + (x - x0) := by ring
        rw [h_eq]
        linarith [h_abs, h6]
      linarith
    let K : Set ℤ := Set.Icc ⌈-M / δ⌉ ⌊M / δ⌋
    have hK_finite : K.Finite := Set.finite_Icc _ _
    have h5 : A ⊆ (fun k : ℤ => δ * (k : ℝ)) '' K := by
      intro x hx
      have h6 : x ∈ productLikeIntegerGrid δ := hA1 hx
      rcases h6 with ⟨k, hk⟩
      have h7 : |x| ≤ M := h4 x hx
      have h8 : -M ≤ x := by linarith [abs_le.mp h7]
      have h9 : x ≤ M := by linarith [abs_le.mp h7]
      have h_eq : δ * (k : ℝ) = x := hk.symm
      have h10 : ⌈-M / δ⌉ ≤ k := by
        have h11 : -M ≤ δ * (k : ℝ) := by rw [h_eq]; exact h8
        have h12 : -M / δ ≤ (k : ℝ) := by
          calc -M / δ = (-M) / δ := by ring
            _ ≤ (δ * (k : ℝ)) / δ := by gcongr
            _ = (k : ℝ) := by field_simp [hδ.ne'] <;> ring
        exact Int.ceil_le.mpr h12
      have h13 : k ≤ ⌊M / δ⌋ := by
        have h14 : δ * (k : ℝ) ≤ M := by rw [h_eq]; exact h9
        have h15 : (k : ℝ) ≤ M / δ := by
          calc (k : ℝ) = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
            _ ≤ M / δ := by gcongr
        exact Int.le_floor.mpr h15
      have h16 : k ∈ K := by
        simp only [K, Set.mem_Icc] <;> exact ⟨h10, h13⟩
      exact ⟨k, h16, h_eq⟩
    exact Set.Finite.subset (hK_finite.image _) h5

/-!
## Step 1: T(y) is a (δ, 2s)-set

For each `y ∈ Y`, the union `T(y) := ⋃_{x ∈ X_y} 𝒯z(x,y)` is a
`(δ, 2s, C')`-set. The proof uses:
- Bounded overlap (each tube belongs to at most 3 of the `𝒯z(x,y)`)
- The `(δ,s)`-set property of `X_y` to count how many `x` can have
  tubes meeting a given `r`-cube
- The `(δ,s)`-set property of each `𝒯z(x,y)` to count tubes in an `r`-cube
-/

/-- **Step 1.** Given that `X_y` is a `(δ,s,C)`-set and each `𝒯z(x,y)` is a
`(δ,s,C)`-set of tubes through `(x,y)`, with bounded overlap and cardinality
upper bounds, the union `T(y) := ⋃_{x ∈ X_y} 𝒯z(x,y)` is a
`(δ, 2s, 9·C⁴)`-set. -/
lemma T_y_is_delta_2s_set {δ s C : ℝ} {y : ℝ} {X_y : Set ℝ}
    {𝒯z : EuclideanSpace ℝ (Fin 2) → Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1) (hC_pos : 0 < C)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hX_grid : X_y ⊆ productLikeIntegerGrid δ)
    (hX_set : IsProductLikeRealDeltaSCSet δ s C X_y)
    (hT_set : ∀ x ∈ X_y,
      IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ s C (𝒯z (mkPoint2 x y)))
    (hpoint : ∀ x ∈ X_y, ∀ T ∈ 𝒯z (mkPoint2 x y), (mkPoint2 x y) ∈ T)
    (h_bounded_overlap : ∀ (T : Set (EuclideanSpace ℝ (Fin 2))),
      T ∈ (⋃ x ∈ X_y, 𝒯z (mkPoint2 x y)) →
      let S := {x ∈ X_y | T ∈ 𝒯z (mkPoint2 x y)}
      S.Finite ∧ S.encard ≤ 3)
    (hT_card : ∀ x ∈ X_y,
      ENat.toENNReal (𝒯z (mkPoint2 x y)).encard ≤ ENNReal.ofReal (C * δ^(-s))) :
    IsDeltaSCSet (d := 2) δ (2 * s) (9 * C^4)
      (productLikeAppendixDyadicTubeParameterSet δ
        (⋃ x ∈ X_y, 𝒯z (mkPoint2 x y))) := by
  classical
  let U : Set (Set (EuclideanSpace ℝ (Fin 2))) := ⋃ x ∈ X_y, 𝒯z (mkPoint2 x y)
  let P_U := productLikeAppendixDyadicTubeParameterSet δ U
  let P_x := fun x => productLikeAppendixDyadicTubeParameterSet δ (𝒯z (mkPoint2 x y))
  have hX_bdd_real : Bornology.IsBounded X_y := by
    have h1 : Bornology.IsBounded (productLikeRealLineCopy X_y) := hX_set.1
    let f_proj : EuclideanSpace ℝ (Fin 1) → ℝ := fun p => p 0
    have h_lip : LipschitzWith 1 f_proj := by
      apply LipschitzWith.mk_one
      intro x y
      have h1 : |(x - y) 0| ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) 0
      have h2 : (x - y) 0 = x 0 - y 0 := by simp
      have h3 : dist (f_proj x) (f_proj y) = |x 0 - y 0| := by
        dsimp only [f_proj]; rw [Real.dist_eq] <;> rfl
      have h4 : dist x y = ‖x - y‖ := dist_eq_norm x y
      rw [h3, h4, ←h2]; exact h1
    have h2 : Bornology.IsBounded (f_proj '' productLikeRealLineCopy X_y) :=
      h_lip.isBounded_image h1
    have h3 : (fun (p : EuclideanSpace ℝ (Fin 1)) => p 0) '' productLikeRealLineCopy X_y = X_y := by
      ext x
      simp only [Set.mem_image, productLikeRealLineCopy, Set.mem_setOf_eq]
      constructor
      · rintro ⟨p, hp, rfl⟩
        simpa [productLikeRealLineCopy, realLineCopy] using hp
      · intro hx
        let f : Fin 1 → ℝ := fun _ => x
        let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm f
        have hp2 : p 0 = x := by
          have h_eq : (WithLp.equiv 2 (Fin 1 → ℝ)) p = f :=
            (WithLp.equiv 2 (Fin 1 → ℝ)).apply_symm_apply f
          have h4 : ((WithLp.equiv 2 (Fin 1 → ℝ)) p) 0 = p 0 := by rfl
          rw [← h4, h_eq] <;> simp [f]
        have hp1 : p ∈ productLikeRealLineCopy X_y := by
          simpa [productLikeRealLineCopy, realLineCopy, hp2] using hx
        exact ⟨p, hp1, hp2⟩
    rw [h3] at h2; exact h2
  have hX_nonempty : X_y.Nonempty := by
    have h1 : (productLikeRealLineCopy X_y).Nonempty := hX_set.2.1
    rcases h1 with ⟨p, hp⟩
    exact ⟨p 0, hp⟩
  have hX_fin : X_y.Finite := finite_bounded_grid_subset hδ hX_grid hX_bdd_real
  have hT_fin : ∀ x ∈ X_y, (𝒯z (mkPoint2 x y)).Finite := by
    intro x hx
    have h3 : dyadicCoveringNumber δ (P_x x) < ⊤ :=
      dyadicCoveringNumber_lt_top hδ (hT_set x hx).2.2.2.1
    have h4 : dyadicCoveringNumber δ (P_x x) = (𝒯z (mkPoint2 x y)).encard :=
      tubeParamCoveringEqCard hδ (hT_set x hx).1
    rw [h4] at h3
    exact Set.encard_lt_top_iff.mp h3
  have hU_fin : U.Finite := Set.Finite.biUnion hX_fin hT_fin
  have hP_U_card : dyadicCoveringNumber δ P_U = U.encard :=
    tubeParamCoveringEqCard hδ (fun T hT => by
      have h1 : ∃ x ∈ X_y, T ∈ 𝒯z (mkPoint2 x y) := by
        simpa [U, Set.mem_iUnion] using hT
      rcases h1 with ⟨x, hx, hTx⟩
      exact (hT_set x hx).1 hTx)
  let X_finset : Finset ℝ := hX_fin.toFinset
  have hP_U_bdd : Bornology.IsBounded P_U := by
    have h1 : P_U = ⋃ x ∈ X_y, P_x x := by
      simp [P_U, P_x, U, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion, Set.mem_image]
    rw [h1]
    have h2 : ∀ (x : ℝ), x ∈ X_y → Bornology.IsBounded (P_x x) := by
      intro x hx
      exact (hT_set x hx).2.2.2.1
    have h3 : Bornology.IsBounded (⋃ x ∈ X_y, P_x x) := by
      let S : Set (Set (EuclideanSpace ℝ (Fin 2))) := P_x '' X_y
      have hS_fin : S.Finite := Set.Finite.image _ hX_fin
      have h_eq : (⋃ x ∈ X_y, P_x x) = ⋃₀ S := by
        ext z; simp [S, Set.mem_iUnion, Set.mem_sUnion] <;> tauto
      rw [h_eq]
      rw [Bornology.isBounded_sUnion hS_fin]
      intro T hT
      rcases hT with ⟨x, hx, rfl⟩
      exact h2 x hx
    exact h3
  have hP_U_nonempty : P_U.Nonempty := by
    rcases hX_nonempty with ⟨x, hx⟩
    have h1 : (P_x x).Nonempty := (hT_set x hx).2.2.2.2.1
    rcases h1 with ⟨p, hp⟩
    have h2 : p ∈ P_U := by
      have h3 : P_U = ⋃ x ∈ X_y, P_x x := by
        simp [P_U, P_x, U, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion, Set.mem_image]
      rw [h3]
      exact Set.mem_iUnion₂.mpr ⟨x, hx, hp⟩
    exact ⟨p, h2⟩
  let T_finset (x : ℝ) : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    if h : x ∈ X_y then (hT_fin x h).toFinset else ∅
  let U_finset : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    X_finset.biUnion T_finset
  have hU_finset_eq : (U_finset : Set _) = U := by
    ext T
    simp only [U_finset, U, T_finset, X_finset, Finset.mem_coe, Finset.mem_biUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hT⟩
      have hx' : x ∈ X_y := by simpa [X_finset] using hx
      have hT' : T ∈ 𝒯z (mkPoint2 x y) := by
        simpa [T_finset, hx'] using hT
      exact ⟨x, hx', hT'⟩
    · rintro ⟨x, hx, hT⟩
      refine ⟨x, by simpa [X_finset] using hx, ?_⟩
      simpa [T_finset, hx] using hT
  have hX_lower : ENat.toENNReal X_y.encard ≥ ENNReal.ofReal (δ^(-s) / C) := by
    have h1 := deltaSCSet_card_lower_bound hX_set
    rw [realLineCoveringEqCard hδ hX_grid] at h1
    exact h1
  have hT_lower : ∀ x ∈ X_y, ENat.toENNReal (𝒯z (mkPoint2 x y)).encard ≥ ENNReal.ofReal (δ^(-s) / C) := by
    intro x hx
    have h1 := deltaSCSet_card_lower_bound (hT_set x hx).2.2.2
    rw [tubeParamCoveringEqCard hδ (hT_set x hx).1] at h1
    exact h1
  let I_inc : Finset (ℝ × Set (EuclideanSpace ℝ (Fin 2))) :=
    X_finset.biUnion (fun x => ({x} : Finset ℝ) ×ˢ T_finset x)
  have hI_card : I_inc.card = ∑ x ∈ X_finset, (T_finset x).card := by
    rw [Finset.card_biUnion]
    · simp [I_inc, Finset.card_product, Finset.card_singleton]
    · intro a _ b _ hab
      apply Finset.disjoint_left.mpr
      intro p hp1 hp2
      have h1 : p.1 ∈ ({a} : Finset ℝ) := (Finset.mem_product.mp hp1).1
      have h1' : p.1 = a := by simpa using h1
      have h2 : p.1 ∈ ({b} : Finset ℝ) := (Finset.mem_product.mp hp2).1
      have h2' : p.1 = b := by simpa using h2
      rw [h1'] at h2'; exact hab h2'
  have h_img : I_inc.image (fun p : ℝ × Set (EuclideanSpace ℝ (Fin 2)) => p.2) = U_finset := by
    ext T
    simp only [Finset.mem_image, I_inc, Finset.mem_biUnion, U_finset]
    constructor
    · rintro ⟨p, ⟨x, hx, hp⟩, rfl⟩
      have hT : p.2 ∈ T_finset x := (Finset.mem_product.mp hp).2
      exact ⟨x, hx, hT⟩
    · rintro ⟨x, hx, hT⟩
      have h_mem : (x, T) ∈ ({x} : Finset ℝ) ×ˢ T_finset x := by
        simp [hT]
      exact ⟨(x, T), ⟨x, hx, h_mem⟩, rfl⟩
  have hI_le : I_inc.card ≤ 3 * U_finset.card := by
    have h_disj : ∀ T1 ∈ U_finset, ∀ T2 ∈ U_finset, T1 ≠ T2 →
        Disjoint (I_inc.filter (fun p => p.2 = T1)) (I_inc.filter (fun p => p.2 = T2)) := by
      intro T1 _ T2 _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : p.2 = T1 := (Finset.mem_filter.mp hp1).2
      have h2 : p.2 = T2 := (Finset.mem_filter.mp hp2).2
      rw [h1] at h2
      exact hne h2
    have h_union : I_inc = U_finset.biUnion (fun T => I_inc.filter (fun p => p.2 = T)) := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hp
        have hT : p.2 ∈ U_finset := by
          rw [← h_img]
          exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
        exact ⟨p.2, hT, hp, rfl⟩
      · rintro ⟨T, hT, hp, _⟩
        exact hp
    have h_sum : I_inc.card = ∑ T ∈ U_finset, (I_inc.filter (fun p => p.2 = T)).card := by
      have h_card : (U_finset.biUnion (fun T => I_inc.filter (fun p => p.2 = T))).card =
          ∑ T ∈ U_finset, (I_inc.filter (fun p => p.2 = T)).card :=
        Finset.card_biUnion h_disj
      exact (congr_arg Finset.card h_union).trans h_card
    rw [h_sum]
    have h_each : ∀ T ∈ U_finset, (I_inc.filter (fun p => p.2 = T)).card ≤ 3 := by
      intro T hT
      let S : Set ℝ := {x ∈ X_y | T ∈ 𝒯z (mkPoint2 x y)}
      have hS_fin : S.Finite := hX_fin.subset (fun x hx => hx.1)
      let S' : Finset ℝ := hS_fin.toFinset
      have hT_in_U : T ∈ U := by
        rw [← hU_finset_eq]; exact hT
      have hS_encard : S.encard ≤ 3 := (h_bounded_overlap T hT_in_U).2
      have hS'_card : S'.card ≤ 3 := by
        have h_eq : (S' : Set ℝ) = S := by simp [S']
        have h : S.encard = ↑S'.card := by
          rw [← h_eq]
          exact Set.encard_coe_eq_coe_finsetCard S'
        rw [h] at hS_encard
        exact_mod_cast hS_encard
      let fiber_img : Finset (ℝ × Set (EuclideanSpace ℝ (Fin 2))) :=
        S'.image (fun x => (x, T))
      have h_fiber_eq : I_inc.filter (fun p => p.2 = T) = fiber_img := by
        ext p
        simp only [Finset.mem_filter, fiber_img, Finset.mem_image]
        constructor
        · rintro ⟨hp, h_eq⟩
          rcases Finset.mem_biUnion.mp hp with ⟨x', hx', h6'⟩
          have h_eq1 : p.1 = x' := by
            have h : p.1 ∈ ({x'} : Finset ℝ) := (Finset.mem_product.mp h6').1
            simpa using h
          have h8 : x' ∈ X_y := by simpa [X_finset] using hx'
          have h9 : p.2 ∈ T_finset x' := (Finset.mem_product.mp h6').2
          have h9' : T ∈ T_finset x' := by rw [← h_eq]; exact h9
          have h10 : x' ∈ S' := by
            have h101 : x' ∈ S := by
              simp only [S, Set.mem_setOf_eq]
              exact ⟨h8, by simpa [T_finset, h8] using h9'⟩
            simpa [S'] using h101
          have h11 : (x', T) = p := by
            ext <;> simp [h_eq1, h_eq]
          exact ⟨x', h10, h11⟩
        · rintro ⟨x, hx, rfl⟩
          have hxS : x ∈ S := by simpa [S'] using hx
          have hxX : x ∈ X_y := hxS.1
          have hT' : T ∈ 𝒯z (mkPoint2 x y) := hxS.2
          have h11 : T ∈ T_finset x := by simpa [T_finset, hxX] using hT'
          have h_prod : (x, T) ∈ ({x} : Finset ℝ) ×ˢ T_finset x := by
            simp [h11]
          have h' : x ∈ X_finset := by simpa [X_finset] using hxX
          have h12 : (x, T) ∈ I_inc := by
            simp only [I_inc, Finset.mem_biUnion]
            exact ⟨x, h', h_prod⟩
          exact ⟨h12, rfl⟩
      rw [h_fiber_eq]
      have h_inj : Function.Injective (fun x : ℝ => (x, T)) := by
        intro x y h; simpa using h
      have h_card : fiber_img.card = S'.card := by
        have h_eq : fiber_img = S'.image (fun x : ℝ => (x, T)) := by rfl
        rw [h_eq]
        exact Finset.card_image_of_injective S' h_inj
      rw [h_card]
      exact hS'_card
    have h_sum3 : ∑ T ∈ U_finset, (I_inc.filter (fun p => p.2 = T)).card ≤ ∑ T ∈ U_finset, 3 :=
      Finset.sum_le_sum h_each
    have h_final : ∑ T ∈ U_finset, (I_inc.filter (fun p => p.2 = T)).card ≤ 3 * U_finset.card := by
      have h : ∑ T ∈ U_finset, (I_inc.filter (fun p => p.2 = T)).card ≤ ∑ T ∈ U_finset, (3 : ℕ) := h_sum3
      have h2 : ∑ T ∈ U_finset, (3 : ℕ) = 3 * U_finset.card := by
        rw [Finset.sum_const] <;> ring
      linarith
    exact h_final
  have h_sum_lower : ((∑ x ∈ X_finset, (T_finset x).card : ℝ)) ≥
      (X_finset.card : ℝ) * (δ^(-s) / C) := by
    have h_each2 : ∀ x ∈ X_finset, ((T_finset x).card : ℝ) ≥ (δ^(-s) / C) := by
      intro x hx
      have hx' : x ∈ X_y := by simpa [X_finset] using hx
      have h_coe : (T_finset x : Set _) = 𝒯z (mkPoint2 x y) := by
        have hif : T_finset x = (hT_fin x hx').toFinset := by
          unfold T_finset
          rw [dif_pos hx']
        rw [hif]
        exact Set.Finite.coe_toFinset (hT_fin x hx')
      have h_encard : (𝒯z (mkPoint2 x y)).encard = ↑(T_finset x).card := by
        have h9 : (𝒯z (mkPoint2 x y)).encard = (↑(T_finset x) : Set (Set (EuclideanSpace ℝ (Fin 2)))).encard := by
          rw [← h_coe]
        rw [h9]
        exact Set.encard_coe_eq_coe_finsetCard (T_finset x)
      have h4 : ENat.toENNReal (𝒯z (mkPoint2 x y)).encard = (↑(T_finset x).card : ENNReal) := by
        rw [h_encard] <;> simp
      have h5 : (↑(T_finset x).card : ENNReal) ≥ ENNReal.ofReal (δ^(-s) / C) := by
        rw [← h4]
        exact hT_lower x hx'
      have h_pos_card : 0 ≤ ((T_finset x).card : ℝ) := Nat.cast_nonneg _
      have h_coe' : (↑(T_finset x).card : ENNReal) = ENNReal.ofReal ((T_finset x).card : ℝ) :=
        (ENNReal.ofReal_natCast (T_finset x).card).symm
      have h6 : ENNReal.ofReal (δ^(-s) / C) ≤ ENNReal.ofReal ((T_finset x).card : ℝ) := by
        have h7 : ENNReal.ofReal ((T_finset x).card : ℝ) = (↑(T_finset x).card : ENNReal) := h_coe'.symm
        rw [h7]
        exact h5
      have h_pos_ds : 0 ≤ δ ^ (-s) := Real.rpow_nonneg (by linarith) _
      have h_pos : 0 ≤ δ ^ (-s) / C := by
        exact div_nonneg h_pos_ds (by linarith)
      exact (ENNReal.ofReal_le_ofReal_iff h_pos_card).mp h6
    have h : ((∑ x ∈ X_finset, (T_finset x).card : ℝ)) ≥ ∑ x ∈ X_finset, (δ^(-s) / C) :=
      Finset.sum_le_sum h_each2
    rw [Finset.sum_const] at h
    simpa using h
  have h_double_count : (3 : ENNReal) * ENat.toENNReal U.encard ≥
      ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s) / C) := by
    have h1 : (I_inc.card : ℝ) ≤ 3 * (U_finset.card : ℝ) := by exact_mod_cast hI_le
    have h2 : (I_inc.card : ℝ) = ∑ x ∈ X_finset, ((T_finset x).card : ℝ) := by
      rw [hI_card, Nat.cast_sum]
    have h_sum_lower2 : (I_inc.card : ℝ) ≥ (X_finset.card : ℝ) * (δ^(-s) / C) := by
      rw [h2]
      exact h_sum_lower
    have h3 : (X_finset.card : ℝ) * (δ^(-s) / C) ≤ 3 * (U_finset.card : ℝ) := by
      linarith [h_sum_lower2, h1]
    have hX_eq : ENat.toENNReal X_y.encard = (↑X_finset.card : ENNReal) := by
      have h' : (↑X_finset : Set ℝ) = X_y := hX_fin.coe_toFinset
      have h : X_y.encard = ↑X_finset.card := by
        rw [← h']
        exact Set.encard_coe_eq_coe_finsetCard X_finset
      exact_mod_cast h
    have hU_eq : ENat.toENNReal U.encard = (↑U_finset.card : ENNReal) := by
      have h' : (↑U_finset : Set _) = U := hU_finset_eq
      have h : U.encard = ↑U_finset.card := by
        rw [← h']
        exact Set.encard_coe_eq_coe_finsetCard U_finset
      exact_mod_cast h
    rw [hX_eq, hU_eq]
    have h_pos3 : 0 ≤ (X_finset.card : ℝ) * (δ^(-s) / C) := by positivity
    have h3' : ENNReal.ofReal ((X_finset.card : ℝ) * (δ^(-s) / C)) ≤
        ENNReal.ofReal (3 * (U_finset.card : ℝ)) := ENNReal.ofReal_le_ofReal h3
    have h5 : ENNReal.ofReal ((X_finset.card : ℝ) * (δ^(-s) / C)) =
        (↑X_finset.card : ENNReal) * ENNReal.ofReal (δ^(-s) / C) := by
      have h_pos1 : 0 ≤ (X_finset.card : ℝ) := by positivity
      have h_pos2 : 0 ≤ δ^(-s) / C := by positivity
      have h_coe : (↑X_finset.card : ENNReal) = ENNReal.ofReal (X_finset.card : ℝ) := by norm_cast
      have h_mul : ENNReal.ofReal ((X_finset.card : ℝ) * (δ^(-s) / C)) =
          ENNReal.ofReal (X_finset.card : ℝ) * ENNReal.ofReal (δ^(-s) / C) :=
        ENNReal.ofReal_mul h_pos1
      calc
        ENNReal.ofReal ((X_finset.card : ℝ) * (δ^(-s) / C))
          = ENNReal.ofReal (X_finset.card : ℝ) * ENNReal.ofReal (δ^(-s) / C) := h_mul
        _ = (↑X_finset.card : ENNReal) * ENNReal.ofReal (δ^(-s) / C) := by rw [h_coe]
    have h6 : ENNReal.ofReal (3 * (U_finset.card : ℝ)) =
        (3 : ENNReal) * (↑U_finset.card : ENNReal) := by
      have h_pos1 : 0 ≤ (3 : ℝ) := by positivity
      have h_pos2 : 0 ≤ (U_finset.card : ℝ) := by positivity
      have h_coe : (↑U_finset.card : ENNReal) = ENNReal.ofReal (U_finset.card : ℝ) := by norm_cast
      have h_mul : ENNReal.ofReal (3 * (U_finset.card : ℝ)) =
          ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal (U_finset.card : ℝ) :=
        ENNReal.ofReal_mul h_pos1
      have h_coe3 : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by norm_cast
      calc
        ENNReal.ofReal (3 * (U_finset.card : ℝ))
          = ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal (U_finset.card : ℝ) := h_mul
        _ = (3 : ENNReal) * (↑U_finset.card : ENNReal) := by
            rw [h_coe3, h_coe] <;> ring
    rw [h5, h6] at h3'
    exact h3'
  have h_main_bound : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 2))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 2 r → δ ≤ r → r ≤ 1 →
      ENat.toENNReal (dyadicCoveringNumber δ (P_U ∩ Q)) ≤
        ENNReal.ofReal (9 * C^4) * ENat.toENNReal (dyadicCoveringNumber δ P_U) *
          ENNReal.ofReal (r ^ (2 * s)) := by
    intro r Q hr_dyadic hQ_dyadic hδ_le_r hr_le_one
    rcases hQ_dyadic with ⟨k, hk⟩
    have hQ_eq : Q = dyadicCube r k := hk
    let lo : ℝ := r * (k 0 : ℝ) * y + r * (k 1 : ℝ)
    let hi : ℝ := r * ((k 0 : ℝ) + 1) * y + r * ((k 1 : ℝ) + 1)
    let I_real : Set ℝ := Set.Icc lo hi
    have hr_pos : 0 < r := dyadicScales_pos hr_dyadic
    have h_len : hi - lo ≤ 2 * r := by
      dsimp only [lo, hi]
      have h_y : y ≤ 1 := hy1
      nlinarith
    have hN : ∃ (N : ℕ), r = (N : ℝ) * δ := dyadicScales_ratio_nat hδ_dyadic hr_dyadic hδ_le_r
    have h_proj : ∀ (x : ℝ), x ∈ X_y → (P_x x ∩ Q).Nonempty → x ∈ I_real := by
      intro x hx hnonempty
      rcases hnonempty with ⟨p, hpP, hpQ⟩
      have h_exists_T : ∃ (T : Set (EuclideanSpace ℝ (Fin 2))), T ∈ 𝒯z (mkPoint2 x y) ∧
          p ∈ productLikeAppendixDyadicTubeCanonicalParameterCube δ T := by
        simpa [P_x, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion, Set.mem_image] using hpP
      rcases h_exists_T with ⟨T, hT_in, hp_in_cube⟩
      let C_T := productLikeAppendixDyadicTubeCanonicalParameterCube δ T
      have hT_in_appendix : T ∈ appendixDyadicTubes δ := (hT_set x hx).1 hT_in
      have hCT_dyadic : C_T ∈ dyadicCubes 2 δ :=
        (DualityBridge.canonical_cube_correct hT_in_appendix).1.1
      rcases hCT_dyadic with ⟨kT, hCT_eq⟩
      have h_inter : (C_T ∩ Q).Nonempty := ⟨p, hp_in_cube, hpQ⟩
      have h_inter2 : (dyadicCube δ kT ∩ dyadicCube r k).Nonempty := by
        rw [← hCT_eq, ← hQ_eq]
        exact h_inter
      have h_contain1 : dyadicCube δ kT ⊆ dyadicCube r k := dyadicCubeContainment hδ hN h_inter2
      have h_contain : C_T ⊆ Q := by
        rw [hCT_eq, hQ_eq]
        exact h_contain1
      have h_dual : appendixDualOfParameterSet C_T = T :=
        (DualityBridge.canonical_cube_correct hT_in_appendix).2
      have h_point_in_T : (mkPoint2 x y) ∈ T := hpoint x hx T hT_in
      rw [← h_dual] at h_point_in_T
      rcases h_point_in_T with ⟨p', hp'_in_CT, h_eq⟩
      have h_p'_in_Q : p' ∈ Q := h_contain hp'_in_CT
      have h_p'_in_cube : p' ∈ dyadicCube r k := by
        rw [← hQ_eq]; exact h_p'_in_Q
      have h_x_eq : x = p' 0 * y + p' 1 := by
        simpa [appendixDualLineMap, appendixDualLine] using h_eq
      have h1 : lo ≤ p' 0 * y + p' 1 := by
        have h11 : r * (k 0 : ℝ) ≤ p' 0 := (h_p'_in_cube 0).1
        have h12 : r * (k 1 : ℝ) ≤ p' 1 := (h_p'_in_cube 1).1
        dsimp only [lo]
        nlinarith [hy0]
      have h2 : p' 0 * y + p' 1 ≤ hi := by
        have h21 : p' 0 < r * ((k 0 : ℝ) + 1) := (h_p'_in_cube 0).2
        have h22 : p' 1 < r * ((k 1 : ℝ) + 1) := (h_p'_in_cube 1).2
        dsimp only [hi]
        nlinarith [hy0, hy1]
      rw [h_x_eq]
      exact ⟨h1, h2⟩
    let k_lo : ℤ := ⌊lo / r⌋
    let k_hi : ℤ := ⌊hi / r⌋
    let K : Finset ℤ := Finset.Icc k_lo k_hi
    have hK_card : K.card ≤ 3 := by
      have h1 : k_hi - k_lo ≤ 2 := by
        by_contra h
        have h' : k_hi - k_lo ≥ 3 := by linarith
        have h2 : (k_hi : ℝ) ≥ (k_lo : ℝ) + 3 := by
          have h21 : (k_hi - k_lo : ℝ) ≥ 3 := by exact_mod_cast h'
          linarith
        have h3 : hi / r ≥ (k_hi : ℝ) := Int.floor_le (hi / r)
        have h4 : lo / r < (k_lo : ℝ) + 1 := Int.lt_floor_add_one (lo / r)
        have h5 : hi / r - lo / r > 2 := by linarith
        have h6 : hi / r - lo / r ≤ 2 := by
          have h7 : hi - lo ≤ 2 * r := h_len
          have h8 : (hi - lo) / r ≤ 2 := by
            have h81 : (hi - lo) / r ≤ (2 * r) / r := by gcongr
            have h82 : (2 * r) / r = 2 := by field_simp [hr_pos.ne'] <;> ring
            rw [h82] at h81
            exact h81
          have h9 : (hi - lo) / r = hi / r - lo / r := by ring
          linarith
        linarith
      simp [K, Finset.Icc_eq_empty_of_lt]
      <;> omega
    let J (k' : ℤ) : Set ℝ := Set.Ico (r * (k' : ℝ)) (r * ((k' : ℝ) + 1))
    have h_cover_I : I_real ⊆ ⋃ k' ∈ K, J k' := by
      intro x hx
      have h_x_in : lo ≤ x ∧ x ≤ hi := hx
      let k' : ℤ := ⌊x / r⌋
      have h_k'_in_K : k' ∈ K := by
        have h1 : k_lo ≤ k' := by
          have h2 : lo ≤ x := h_x_in.1
          have h3 : lo / r ≤ x / r := by gcongr
          have h4 : ⌊lo / r⌋ ≤ ⌊x / r⌋ := Int.floor_mono h3
          exact h4
        have h2 : k' ≤ k_hi := by
          have h3 : x ≤ hi := h_x_in.2
          have h4 : x / r ≤ hi / r := by gcongr
          have h5 : ⌊x / r⌋ ≤ ⌊hi / r⌋ := Int.floor_mono h4
          exact h5
        exact Finset.mem_Icc.mpr ⟨h1, h2⟩
      have h_x_in_J : x ∈ J k' := by
        dsimp only [J]
        have h1 : r * (k' : ℝ) ≤ x := by
          have h2 : (k' : ℝ) ≤ x / r := Int.floor_le (x / r)
          have h3 : r * (k' : ℝ) ≤ r * (x / r) := by gcongr
          have h4 : r * (x / r) = x := by field_simp [hr_pos.ne'] <;> ring
          rw [h4] at h3; exact h3
        have h5 : x < r * ((k' : ℝ) + 1) := by
          have h6 : x / r < (k' : ℝ) + 1 := Int.lt_floor_add_one (x / r)
          have h7 : r * (x / r) < r * ((k' : ℝ) + 1) := by gcongr
          have h8 : r * (x / r) = x := by field_simp [hr_pos.ne'] <;> ring
          rw [h8] at h7; exact h7
        exact ⟨h1, h5⟩
      exact Set.mem_iUnion₂.mpr ⟨k', h_k'_in_K, h_x_in_J⟩
    have h_interval_bound : ∀ k' ∈ K,
        ENat.toENNReal (X_y ∩ J k').encard ≤
          ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s) := by
      intro k' _
      let Q1 : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube r (fun _ => k')
      have hQ1_dyadic : Q1 ∈ dyadicCubes 1 r := ⟨(fun _ => k'), rfl⟩
      have hX_cover : ∀ ⦃r' : ℝ⦄ ⦃Q' : Set (EuclideanSpace ℝ (Fin 1))⦄,
          r' ∈ dyadicScales → Q' ∈ dyadicCubes 1 r' → δ ≤ r' → r' ≤ 1 →
          ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy X_y ∩ Q')) ≤
            ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy X_y)) *
              ENNReal.ofReal (r' ^ s) := hX_set.2.2.2.2.2.2.2.2
      have h_main := hX_cover hr_dyadic hQ1_dyadic hδ_le_r hr_le_one
      have h_eq1 : productLikeRealLineCopy X_y ∩ Q1 = productLikeRealLineCopy (X_y ∩ J k') := by
        ext p
        simp only [productLikeRealLineCopy, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2⟩
          have h3 : p 0 ∈ J k' := by
            simpa [Q1, J] using h2 0
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          have h3 : p ∈ Q1 := by
            simpa [dyadicCube, Q1, J] using h2
          exact ⟨h1, h3⟩
      rw [h_eq1] at h_main
      have h_card : dyadicCoveringNumber δ (productLikeRealLineCopy (X_y ∩ J k')) = (X_y ∩ J k').encard :=
        realLineCoveringEqCard hδ (fun x hx => hX_grid hx.1)
      rw [h_card] at h_main
      have h_X_card : dyadicCoveringNumber δ (productLikeRealLineCopy X_y) = X_y.encard :=
        realLineCoveringEqCard hδ hX_grid
      rw [h_X_card] at h_main
      exact h_main
    let S_set : Set ℝ := X_y ∩ I_real
    have hS_fin : S_set.Finite := hX_fin.subset (fun x hx => hx.1)
    let S_finset : Finset ℝ := hS_fin.toFinset
    have hS_eq : (S_finset : Set ℝ) = S_set := by simp [S_finset, S_set]
    have h_empty : ∀ x ∈ X_y, x ∉ I_real → P_x x ∩ Q = ∅ := by
      intro x hx hnx
      by_contra h
      have h' : (P_x x ∩ Q).Nonempty := Set.nonempty_iff_ne_empty.mpr h
      exact hnx (h_proj x hx h')
    have h_union_eq : P_U ∩ Q = ⋃ x ∈ S_finset, P_x x ∩ Q := by
      have h1 : P_U = ⋃ x ∈ X_y, P_x x := by
        simp [P_U, P_x, U, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion, Set.mem_image]
      rw [h1]
      ext p
      simp only [Set.mem_inter_iff, Set.mem_iUnion]
      constructor
      · rintro ⟨h2, h3⟩
        rcases h2 with ⟨x, hx, hp⟩
        have h4 : x ∈ S_set := by
          have h5 : (P_x x ∩ Q).Nonempty := ⟨p, hp, h3⟩
          exact ⟨hx, h_proj x hx h5⟩
        have h6 : x ∈ S_finset := by
          have h7 : x ∈ (S_finset : Set ℝ) := by rw [hS_eq]; exact h4
          exact_mod_cast h7
        exact ⟨x, h6, hp, h3⟩
      · rintro ⟨x, hx, hp, hQ⟩
        have h7 : x ∈ S_set := by
          have h8 : x ∈ (S_finset : Set ℝ) := hx
          rw [hS_eq] at h8
          exact h8
        have h8 : x ∈ X_y := h7.1
        exact ⟨⟨x, h8, hp⟩, hQ⟩
    have h_bdd : ∀ x ∈ S_finset, Bornology.IsBounded (P_x x ∩ Q) := by
      intro x hx
      have hxS : x ∈ S_set := by
        have h : x ∈ (S_finset : Set ℝ) := hx
        rw [hS_eq] at h
        exact h
      have hx' : x ∈ X_y := hxS.1
      have h_bdd_Px : Bornology.IsBounded (P_x x) := (hT_set x hx').2.2.2.1
      have h_Q_bdd : Bornology.IsBounded Q := by
        rw [hQ_eq]
        exact dyadicCube_bounded
      have h_sub : (P_x x ∩ Q) ⊆ (P_x x) := by
        intro z hz
        exact hz.1
      have h : Bornology.IsBounded (P_x x ∩ Q) :=
        Bornology.IsBounded.subset h_bdd_Px h_sub
      exact h
    have h_cover_union : ENat.toENNReal (dyadicCoveringNumber δ (P_U ∩ Q)) ≤
        ∑ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) := by
      rw [h_union_eq]
      exact dyadicCoveringNumber_iUnion_le S_finset (fun x => P_x x ∩ Q) h_bdd hδ
    have h_per_x : ∀ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) ≤
        ENNReal.ofReal (C^2 * δ^(-s) * r^s) := by
      intro x hx
      have hxS : x ∈ S_set := by
        have h : x ∈ (S_finset : Set ℝ) := hx
        rw [hS_eq] at h
        exact h
      have hx' : x ∈ X_y := hxS.1
      let Q2 : Set (EuclideanSpace ℝ (Fin 2)) := Q
      have hT_delta : IsDeltaSCSet (d := 2) δ s C (P_x x) := (hT_set x hx').2.2.2
      have hT_cover : ∀ ⦃r' : ℝ⦄ ⦃Q' : Set (EuclideanSpace ℝ (Fin 2))⦄,
          r' ∈ dyadicScales → Q' ∈ dyadicCubes 2 r' → δ ≤ r' → r' ≤ 1 →
          ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q')) ≤
            ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ (P_x x)) *
              ENNReal.ofReal (r' ^ s) := hT_delta.2.2.2.2.2.2.2.2
      have hQ_dyadic2 : Q ∈ dyadicCubes 2 r := by
        rw [hQ_eq]
        exact ⟨k, rfl⟩
      have h_main2 := hT_cover hr_dyadic hQ_dyadic2 hδ_le_r hr_le_one
      have h_card1 : dyadicCoveringNumber δ (P_x x) = (𝒯z (mkPoint2 x y)).encard :=
        tubeParamCoveringEqCard hδ (hT_set x hx').1
      rw [h_card1] at h_main2
      have h_upper : ENat.toENNReal (𝒯z (mkPoint2 x y)).encard ≤ ENNReal.ofReal (C * δ^(-s)) := hT_card x hx'
      calc
        ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q2))
          ≤ ENNReal.ofReal C * ENat.toENNReal (𝒯z (mkPoint2 x y)).encard * ENNReal.ofReal (r ^ s) := h_main2
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal (C * δ^(-s)) * ENNReal.ofReal (r ^ s) := by gcongr
        _ = ENNReal.ofReal (C^2 * δ^(-s) * r^s) := by
          have h_posC : 0 ≤ C := by positivity
          have h_posd : 0 ≤ δ^(-s) := by positivity
          have h_posr : 0 ≤ r ^ s := by positivity
          have h1 : ENNReal.ofReal (C * δ^(-s)) = ENNReal.ofReal C * ENNReal.ofReal (δ^(-s)) := by
            rw [ENNReal.ofReal_mul h_posC]
          rw [h1]
          have h2 : ENNReal.ofReal C * (ENNReal.ofReal C * ENNReal.ofReal (δ^(-s))) * ENNReal.ofReal (r ^ s) =
              ENNReal.ofReal (C^2 * δ^(-s) * r^s) := by
            have hpc : 0 ≤ C := by positivity
            have hpd : 0 ≤ δ^(-s) := by positivity
            have hpr : 0 ≤ r ^ s := by positivity
            have h1 : ENNReal.ofReal C * ENNReal.ofReal C = ENNReal.ofReal (C * C) :=
              (ENNReal.ofReal_mul hpc).symm
            have h2 : 0 ≤ C * C := by positivity
            have h3 : ENNReal.ofReal (C * C) * ENNReal.ofReal (δ^(-s)) = ENNReal.ofReal ((C * C) * δ^(-s)) :=
              (ENNReal.ofReal_mul h2).symm
            have h4 : 0 ≤ (C * C) * δ^(-s) := by positivity
            have h5 : ENNReal.ofReal ((C * C) * δ^(-s)) * ENNReal.ofReal (r ^ s) = ENNReal.ofReal (((C * C) * δ^(-s)) * r ^ s) :=
              (ENNReal.ofReal_mul h4).symm
            calc
              ENNReal.ofReal C * (ENNReal.ofReal C * ENNReal.ofReal (δ^(-s))) * ENNReal.ofReal (r ^ s)
                = (ENNReal.ofReal C * ENNReal.ofReal C) * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r ^ s) := by ring
              _ = ENNReal.ofReal (C * C) * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r ^ s) := by rw [h1]
              _ = ENNReal.ofReal ((C * C) * δ^(-s)) * ENNReal.ofReal (r ^ s) := by rw [h3]
              _ = ENNReal.ofReal (((C * C) * δ^(-s)) * r ^ s) := by rw [h5]
              _ = ENNReal.ofReal (C^2 * δ^(-s) * r^s) := by
                exact congr_arg ENNReal.ofReal (by ring)
          exact h2
    have h_sum_bound : ∑ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) ≤
        ENNReal.ofReal (C^2 * δ^(-s) * r^s) * ENat.toENNReal S_finset.card := by
      have h : ∑ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) ≤
          ∑ x ∈ S_finset, ENNReal.ofReal (C^2 * δ^(-s) * r^s) :=
        Finset.sum_le_sum h_per_x
      have h' : ∑ x ∈ S_finset, ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
          ENNReal.ofReal (C^2 * δ^(-s) * r^s) * ENat.toENNReal S_finset.card := by
        have h1 : ∑ x ∈ S_finset, ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
            S_finset.card • ENNReal.ofReal (C^2 * δ^(-s) * r^s) := by
          rw [Finset.sum_const]
        rw [h1]
        have h2 : S_finset.card • ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
            (↑S_finset.card : ENNReal) * ENNReal.ofReal (C^2 * δ^(-s) * r^s) := by
          rw [nsmul_eq_mul] <;> rfl
        have h3 : (↑S_finset.card : ENNReal) = ENat.toENNReal S_finset.card := by
          simp
        rw [h2, h3]
        <;> exact mul_comm _ _
      rw [h'] at h
      exact h
    have hS_card_bound : ENat.toENNReal S_finset.card ≤
        ENNReal.ofReal 3 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s) := by
      have h1 : S_set ⊆ ⋃ k' ∈ K, X_y ∩ J k' := by
        intro x hx
        have h2 : x ∈ I_real := hx.2
        have h3 : x ∈ ⋃ k' ∈ K, J k' := h_cover_I h2
        rcases Set.mem_iUnion₂.mp h3 with ⟨k', hk', hxJ⟩
        exact Set.mem_iUnion₂.mpr ⟨k', hk', ⟨hx.1, hxJ⟩⟩
      let XJ_finset (k' : ℤ) : Finset ℝ := (hX_fin.subset (fun x (hx : x ∈ X_y ∩ J k') => hx.1)).toFinset
      have hXJ_eq : ∀ k', (XJ_finset k' : Set ℝ) = X_y ∩ J k' := by
        intro k'
        simp [XJ_finset]
        <;> rfl
      have h2 : S_finset.card ≤ ∑ k' ∈ K, (XJ_finset k').card := by
        have h4 : S_finset ⊆ K.biUnion XJ_finset := by
          intro x hx
          have h5 : x ∈ S_set := by
            have h51 : x ∈ (S_finset : Set ℝ) := hx
            rw [hS_eq] at h51
            exact h51
          have h6 : x ∈ ⋃ k' ∈ K, X_y ∩ J k' := h1 h5
          rcases Set.mem_iUnion₂.mp h6 with ⟨k', hk', hxJ⟩
          have h7 : x ∈ XJ_finset k' := by
            simpa [XJ_finset] using hxJ
          exact Finset.mem_biUnion.mpr ⟨k', hk', h7⟩
        have h5 : S_finset.card ≤ (K.biUnion XJ_finset).card := Finset.card_le_card h4
        have h6 : (K.biUnion XJ_finset).card ≤ ∑ k' ∈ K, (XJ_finset k').card := Finset.card_biUnion_le
        linarith
      have h3 : ENat.toENNReal S_finset.card ≤ ∑ k' ∈ K, ENat.toENNReal (XJ_finset k').card := by
        have h31 : (S_finset.card : ENNReal) ≤ ∑ k' ∈ K, ((XJ_finset k').card : ENNReal) := by
          exact_mod_cast h2
        simpa using h31
      have h4 : ∑ k' ∈ K, ENat.toENNReal (XJ_finset k').card ≤
          ∑ k' ∈ K, (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) :=
        Finset.sum_le_sum (fun k' hk' => by
          have h_eq : ENat.toENNReal (XJ_finset k').card = ENat.toENNReal (X_y ∩ J k').encard := by
            have h1 : ENat.toENNReal (XJ_finset k').card = ENat.toENNReal ((XJ_finset k' : Set ℝ)).encard := by
              simp
            rw [h1]
            have h2 : (XJ_finset k' : Set ℝ) = X_y ∩ J k' := hXJ_eq k'
            rw [h2]
          rw [h_eq]
          exact h_interval_bound k' hk')
      have h_sum_eq : ∑ k' ∈ K, (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) =
          ENNReal.ofReal (K.card : ℝ) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by
        have h1 : ∑ k' ∈ K, (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) =
            (↑K.card : ENNReal) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          <;> rfl
        have h2 : (↑K.card : ENNReal) = ENNReal.ofReal (K.card : ℝ) := by norm_cast
        rw [h1, h2]
      have h5 : ENat.toENNReal S_finset.card ≤
          ENNReal.ofReal (K.card : ℝ) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by
        calc
          ENat.toENNReal S_finset.card
            ≤ ∑ k' ∈ K, ENat.toENNReal (XJ_finset k').card := h3
          _ ≤ ∑ k' ∈ K, (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := h4
          _ = ENNReal.ofReal (K.card : ℝ) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := h_sum_eq
      have h6 : ENNReal.ofReal (K.card : ℝ) ≤ ENNReal.ofReal 3 := by
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hK_card)
      calc
        ENat.toENNReal S_finset.card
          ≤ ENNReal.ofReal (K.card : ℝ) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := h5
        _ ≤ ENNReal.ofReal 3 * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by gcongr
        _ = ENNReal.ofReal 3 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s) := by ring
    calc
      ENat.toENNReal (dyadicCoveringNumber δ (P_U ∩ Q))
        ≤ ∑ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) := h_cover_union
      _ ≤ ENNReal.ofReal (C^2 * δ^(-s) * r^s) * ENat.toENNReal S_finset.card := h_sum_bound
      _ ≤ ENNReal.ofReal (C^2 * δ^(-s) * r^s) *
            (ENNReal.ofReal 3 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by
          gcongr
      _ = ENNReal.ofReal (3 * C^3) * ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r ^ (2 * s)) := by
          have h_posC : 0 ≤ C := by positivity
          have h_posC2 : 0 ≤ C^2 := by positivity
          have h_posd : 0 ≤ δ^(-s) := by positivity
          have h_posr : 0 ≤ r ^ s := by positivity
          have h_pos3 : 0 ≤ (3 : ℝ) := by positivity
          have h1 : ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
              ENNReal.ofReal (C^2) * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r^s) := by
            have h1a : ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
                ENNReal.ofReal (C^2 * δ^(-s)) * ENNReal.ofReal (r^s) :=
              ENNReal.ofReal_mul (by positivity : 0 ≤ C^2 * δ^(-s))
            have h1b : ENNReal.ofReal (C^2 * δ^(-s)) =
                ENNReal.ofReal (C^2) * ENNReal.ofReal (δ^(-s)) :=
              ENNReal.ofReal_mul h_posC2
            rw [h1a, h1b] <;> ring
          have h2 : ENNReal.ofReal (r ^ s) * ENNReal.ofReal (r ^ s) = ENNReal.ofReal (r ^ (2 * s)) := by
            have h2a : ENNReal.ofReal (r ^ s) * ENNReal.ofReal (r ^ s) = ENNReal.ofReal ((r ^ s) * (r ^ s)) :=
              (ENNReal.ofReal_mul h_posr).symm
            rw [h2a]
            have h2b : (r ^ s) * (r ^ s) = r ^ (2 * s) := by
              have h : (r ^ s) * (r ^ s) = r ^ (s + s) := by
                rw [← Real.rpow_add (by positivity)]
              rw [h]
              have h2 : s + s = 2 * s := by ring
              rw [h2]
            rw [h2b]
          have h3 : ENNReal.ofReal (C^2) * (ENNReal.ofReal 3 * ENNReal.ofReal C) = ENNReal.ofReal (3 * C^3) := by
            have h3a : ENNReal.ofReal 3 * ENNReal.ofReal C = ENNReal.ofReal (3 * C) :=
              (ENNReal.ofReal_mul h_pos3).symm
            have h3b : ENNReal.ofReal (C^2) * ENNReal.ofReal (3 * C) = ENNReal.ofReal (C^2 * (3 * C)) :=
              (ENNReal.ofReal_mul h_posC2).symm
            rw [h3a, h3b]
            have h3c : C^2 * (3 * C) = 3 * C^3 := by ring
            rw [h3c]
          have h4 : ENNReal.ofReal (C^2 * δ^(-s) * r^s) *
                (ENNReal.ofReal 3 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) =
              ENNReal.ofReal (3 * C^3) * ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r ^ (2 * s)) := by
            rw [h1]
            have h5 : (ENNReal.ofReal (C^2) * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r^s)) *
                  (ENNReal.ofReal 3 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) =
                (ENNReal.ofReal (C^2) * (ENNReal.ofReal 3 * ENNReal.ofReal C)) *
                  ENNReal.ofReal (δ^(-s)) * ENat.toENNReal X_y.encard *
                  (ENNReal.ofReal (r ^ s) * ENNReal.ofReal (r ^ s)) := by ring
            rw [h5, h3, h2] <;> ring
          exact h4
      _ ≤ ENNReal.ofReal (9 * C^4) * ENat.toENNReal (dyadicCoveringNumber δ P_U) * ENNReal.ofReal (r ^ (2 * s)) := by
          have h9 : ENNReal.ofReal (δ^(-s)) = ENNReal.ofReal C * ENNReal.ofReal (δ^(-s) / C) := by
            have h_posC : 0 ≤ C := by positivity
            have h9a : C * (δ^(-s) / C) = δ^(-s) := by
              field_simp [hC_pos.ne'] <;> ring
            have h9b : ENNReal.ofReal C * ENNReal.ofReal (δ^(-s) / C) = ENNReal.ofReal (C * (δ^(-s) / C)) :=
              (ENNReal.ofReal_mul h_posC).symm
            rw [h9b, h9a]
          have h7 : ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)) ≤
              (3 : ENNReal) * ENNReal.ofReal C * ENat.toENNReal U.encard := by
            rw [h9]
            have h10 : ENat.toENNReal X_y.encard * (ENNReal.ofReal C * ENNReal.ofReal (δ^(-s) / C)) =
                ENNReal.ofReal C * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s) / C)) := by ring
            rw [h10]
            have h11 : ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s) / C) ≤
                (3 : ENNReal) * ENat.toENNReal U.encard := h_double_count
            have h12 : ENNReal.ofReal C * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s) / C)) ≤
                ENNReal.ofReal C * ((3 : ENNReal) * ENat.toENNReal U.encard) :=
              mul_le_mul_of_nonneg_left h11 (by positivity)
            have h13 : ENNReal.ofReal C * ((3 : ENNReal) * ENat.toENNReal U.encard) =
                (3 : ENNReal) * ENNReal.ofReal C * ENat.toENNReal U.encard := by ring
            rw [h13] at h12
            exact h12
          have h_goal : ENNReal.ofReal (3 * C^3) * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s))) ≤
              ENNReal.ofReal (9 * C^4) * ENat.toENNReal U.encard := by
            have h91 : ENNReal.ofReal (3 * C^3) * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s))) ≤
                ENNReal.ofReal (3 * C^3) * ((3 : ENNReal) * ENNReal.ofReal C * ENat.toENNReal U.encard) :=
              mul_le_mul_of_nonneg_left h7 (by positivity)
            have h10 : ENNReal.ofReal (3 * C^3) * ((3 : ENNReal) * ENNReal.ofReal C * ENat.toENNReal U.encard) =
                ENNReal.ofReal (9 * C^4) * ENat.toENNReal U.encard := by
              have h11 : ENNReal.ofReal (3 * C^3) * ((3 : ENNReal) * ENNReal.ofReal C) = ENNReal.ofReal (9 * C^4) := by
                have h11a : (3 : ENNReal) = ENNReal.ofReal 3 := by norm_cast
                rw [h11a]
                have h11b : ENNReal.ofReal (3 * C^3) * (ENNReal.ofReal 3 * ENNReal.ofReal C) =
                    ENNReal.ofReal ((3 * C^3) * (3 * C)) := by
                  have h : ENNReal.ofReal 3 * ENNReal.ofReal C = ENNReal.ofReal (3 * C) :=
                    (ENNReal.ofReal_mul (by positivity)).symm
                  rw [h]
                  exact (ENNReal.ofReal_mul (by positivity)).symm
                rw [h11b]
                have h : (3 * C^3) * (3 * C) = 9 * C^4 := by ring
                rw [h]
              have h12 : ENNReal.ofReal (3 * C^3) * ((3 : ENNReal) * ENNReal.ofReal C * ENat.toENNReal U.encard) =
                  (ENNReal.ofReal (3 * C^3) * ((3 : ENNReal) * ENNReal.ofReal C)) * ENat.toENNReal U.encard := by ring
              rw [h12, h11] <;> ring
            exact le_trans h91 (le_of_eq h10)
          have h12 : ENNReal.ofReal (3 * C^3) * ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r ^ (2 * s)) =
              (ENNReal.ofReal (3 * C^3) * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)))) * ENNReal.ofReal (r ^ (2 * s)) := by ring
          rw [h12]
          have h13 : ENNReal.ofReal (9 * C^4) * ENat.toENNReal U.encard = ENNReal.ofReal (9 * C^4) * ENat.toENNReal (dyadicCoveringNumber δ P_U) := by
            rw [hP_U_card]
          rw [h13] at h_goal
          exact mul_le_mul_of_nonneg_right h_goal (by positivity)
  have h_s_nonneg2 : 0 ≤ 2 * s := by linarith [hs_nonneg]
  have h_s_le_two : 2 * s ≤ 2 := by linarith [hs_le_one]
  exact ⟨hP_U_bdd, hP_U_nonempty, by norm_num, hδ_dyadic, hδ, h_s_nonneg2, h_s_le_two, by positivity, h_main_bound⟩

/-!
### Helper lemmas for Step 3
-/

/-- If a dyadic cube at scale δ intersects a dyadic cube at scale r, with
δ ≤ r and both scales dyadic, then the smaller cube is contained in the
larger one. -/
lemma dyadicCube_nesting {δ r : ℝ} {d : ℕ}
    (hδ : 0 < δ) (hδ_le_r : δ ≤ r)
    (hδ_dyadic : δ ∈ dyadicScales) (hr_dyadic : r ∈ dyadicScales)
    (k : Fin d → ℤ) (j : Fin d → ℤ)
    (h_inter : (dyadicCube δ k ∩ dyadicCube r j).Nonempty) :
    dyadicCube δ k ⊆ dyadicCube r j := by
  rcases hδ_dyadic with ⟨n, rfl⟩
  rcases hr_dyadic with ⟨m, rfl⟩
  have hnm : m ≤ n := by
    by_contra h
    have h' : n < m := by omega
    have : (2 : ℝ) ^ (-(n : ℤ)) > (2 : ℝ) ^ (-(m : ℤ)) := by
      gcongr <;> norm_cast <;> omega
    linarith
  let q : ℕ := 2 ^ (n - m)
  set δ' : ℝ := (2 : ℝ) ^ (-(n : ℤ)) with hδ'
  set r' : ℝ := (2 : ℝ) ^ (-(m : ℤ)) with hr'
  have hδ'_pos : 0 < δ' := by positivity
  have h_eq_int : (-(m : ℤ)) = ((n - m : ℕ) : ℤ) + (-(n : ℤ)) := by
    simp [hnm] <;> omega
  have hq_eq : r' = (q : ℝ) * δ' := by
    have hq1 : (q : ℝ) = (2 : ℝ) ^ ((n - m : ℕ) : ℤ) := by
      simp [q] <;> norm_cast
    simp only [hr', hδ']
    rw [hq1]
    have h : (2 : ℝ) ^ (((n - m : ℕ) : ℤ) + (-(n : ℤ))) =
        (2 : ℝ) ^ ((n - m : ℕ) : ℤ) * (2 : ℝ) ^ (-(n : ℤ)) := by
      rw [zpow_add₀ (by norm_num)] <;> ring
    rw [← h, h_eq_int]
  rcases h_inter with ⟨p, hp1, hp2⟩
  have h_int1 : ∀ i, (q : ℝ) * (j i : ℝ) ≤ (k i : ℝ) := by
    intro i
    have h1 : r' * (j i : ℝ) ≤ p i := (hp2 i).1
    have h2 : p i < δ' * ((k i : ℝ) + 1) := (hp1 i).2
    have h3 : (q : ℝ) * δ' * (j i : ℝ) < δ' * ((k i : ℝ) + 1) := by
      rw [hq_eq] at h1; linarith
    have h4 : (q : ℝ) * (j i : ℝ) < (k i : ℝ) + 1 := by
      by_contra h5
      have h5' : (q : ℝ) * (j i : ℝ) ≥ (k i : ℝ) + 1 := by linarith
      have h6 : δ' * ((q : ℝ) * (j i : ℝ)) ≥ δ' * ((k i : ℝ) + 1) := by gcongr
      have h7 : δ' * ((q : ℝ) * (j i : ℝ)) = (q : ℝ) * δ' * (j i : ℝ) := by ring
      rw [h7] at h6
      linarith
    have h4' : (q : ℤ) * (j i) < (k i) + 1 := by exact_mod_cast h4
    have h5 : (q : ℤ) * (j i) ≤ (k i) := Int.le_of_lt_add_one h4'
    exact_mod_cast h5
  have h_int2 : ∀ i, (k i : ℝ) + 1 ≤ (q : ℝ) * ((j i : ℝ) + 1) := by
    intro i
    have h1 : δ' * (k i : ℝ) ≤ p i := (hp1 i).1
    have h2 : p i < r' * ((j i : ℤ) + 1) := (hp2 i).2
    have h3 : δ' * (k i : ℝ) < (q : ℝ) * δ' * ((j i : ℝ) + 1) := by
      rw [hq_eq] at h2; linarith
    have h4 : (k i : ℝ) < (q : ℝ) * ((j i : ℝ) + 1) := by
      by_contra h5
      have h5' : (q : ℝ) * ((j i : ℝ) + 1) ≤ (k i : ℝ) := by linarith
      have h6 : δ' * ((q : ℝ) * ((j i : ℝ) + 1)) ≤ δ' * (k i : ℝ) := by gcongr
      have h7 : δ' * ((q : ℝ) * ((j i : ℝ) + 1)) = (q : ℝ) * δ' * ((j i : ℝ) + 1) := by ring
      rw [h7] at h6
      linarith
    have h4_int : (k i) < (q : ℤ) * ((j i) + 1) := by exact_mod_cast h4
    have h5 : (k i) + 1 ≤ (q : ℤ) * ((j i) + 1) := by omega
    exact_mod_cast h5
  intro x hx
  intro i
  have hxi1 : δ' * (k i : ℝ) ≤ x i := (hx i).1
  have hxi2 : x i < δ' * ((k i : ℝ) + 1) := (hx i).2
  have h1 : r' * (j i : ℝ) ≤ x i := by
    calc r' * (j i : ℝ)
      = (q : ℝ) * δ' * (j i : ℝ) := by rw [hq_eq] <;> ring
    _ = δ' * ((q : ℝ) * (j i : ℝ)) := by ring
    _ ≤ δ' * (k i : ℝ) := by gcongr; exact h_int1 i
    _ ≤ x i := hxi1
  have h2 : x i < r' * ((j i : ℤ) + 1) := by
    calc x i
      < δ' * ((k i : ℝ) + 1) := hxi2
    _ ≤ δ' * ((q : ℝ) * ((j i : ℝ) + 1)) := by gcongr; exact h_int2 i
    _ = (q : ℝ) * δ' * ((j i : ℝ) + 1) := by ring
    _ = r' * ((j i : ℤ) + 1) := by rw [hq_eq] <;> ring
  exact ⟨h1, h2⟩

/-- For a tube family `𝒮` and a dyadic cube `Q` at scale r ≥ δ,
`P(𝒮) ∩ Q = P(𝒮_Q)` where `𝒮_Q` is the subfamily of tubes whose canonical
cubes are contained in `Q`. -/
lemma paramSetIntersectCube {δ r : ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hr_dyadic : r ∈ dyadicScales) (hδ_le_r : δ ≤ r)
    {𝒮 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hS_dyadic : 𝒮 ⊆ appendixDyadicTubes δ)
    {Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hQ_cube : Q ∈ dyadicCubes 2 r) :
    productLikeAppendixDyadicTubeParameterSet δ 𝒮 ∩ Q =
      productLikeAppendixDyadicTubeParameterSet δ
        {T ∈ 𝒮 | productLikeAppendixDyadicTubeCanonicalParameterCube δ T ⊆ Q} := by
  let canon := productLikeAppendixDyadicTubeCanonicalParameterCube δ
  let 𝒮_Q : Set (Set (EuclideanSpace ℝ (Fin 2))) := {T ∈ 𝒮 | canon T ⊆ Q}
  ext p
  simp only [Set.mem_inter_iff, productLikeAppendixDyadicTubeParameterSet,
    Set.mem_sUnion, Set.mem_image, 𝒮_Q] at *
  constructor
  · rintro ⟨⟨C, ⟨T, hT, rfl⟩, hpC⟩, hpQ⟩
    have hT' : T ∈ appendixDyadicTubes δ := hS_dyadic hT
    have hC_cube : canon T ∈ dyadicCubes 2 δ := by
      simpa [canon, productLikeAppendixDyadicTubeCanonicalParameterCube, hT'] using
        (Classical.choose_spec hT').1.1
    obtain ⟨k, hk : canon T = dyadicCube δ k⟩ := hC_cube
    rcases hQ_cube with ⟨j, hQ_eq⟩
    have h_inter : (dyadicCube δ k ∩ dyadicCube r j).Nonempty := by
      rw [← hk, ← hQ_eq]; exact ⟨p, hpC, hpQ⟩
    have h_sub : canon T ⊆ Q := by
      rw [hk, hQ_eq]
      exact dyadicCube_nesting hδ hδ_le_r hδ_dyadic hr_dyadic k j h_inter
    exact ⟨canon T, ⟨T, ⟨hT, h_sub⟩, rfl⟩, hpC⟩
  · rintro ⟨C, ⟨T, ⟨hT, h_sub⟩, rfl⟩, hpC⟩
    exact ⟨⟨canon T, ⟨T, hT, rfl⟩, hpC⟩, h_sub hpC⟩

/-- For a single tube family `𝒮` that is a `(δ,2s,C)`-set, the covering
bound at an `r`-cube `Q` translates to an `ENat` cardinality bound on the
subfamily of tubes whose canonical parameter cubes lie in `Q`. -/
lemma single_family_covering_bound {δ s C r : ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hr_dyadic : r ∈ dyadicScales) (hδ_le_r : δ ≤ r) (hr_le_one : r ≤ 1)
    {𝒮 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hS_dyadic : 𝒮 ⊆ appendixDyadicTubes δ)
    (hS_set : IsDeltaSCSet (d := 2) δ (2 * s) C
      (productLikeAppendixDyadicTubeParameterSet δ 𝒮))
    {Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hQ_cube : Q ∈ dyadicCubes 2 r) :
    ENat.toENNReal ({T ∈ 𝒮 | productLikeAppendixDyadicTubeCanonicalParameterCube δ T ⊆ Q}).encard ≤
      ENNReal.ofReal C * ENat.toENNReal 𝒮.encard * ENNReal.ofReal (r ^ (2 * s)) := by
  let canon := productLikeAppendixDyadicTubeCanonicalParameterCube δ
  let S_Q := {T ∈ 𝒮 | canon T ⊆ Q}
  have hS_Q_dyadic : S_Q ⊆ appendixDyadicTubes δ := fun T hT => hS_dyadic hT.1
  have h_eq1 : dyadicCoveringNumber δ (productLikeAppendixDyadicTubeParameterSet δ S_Q) = S_Q.encard :=
    tubeParamCoveringEqCard hδ hS_Q_dyadic
  have h_eq2 : productLikeAppendixDyadicTubeParameterSet δ 𝒮 ∩ Q =
      productLikeAppendixDyadicTubeParameterSet δ S_Q :=
    paramSetIntersectCube hδ hδ_dyadic hr_dyadic hδ_le_r hS_dyadic hQ_cube
  rcases hS_set with ⟨_, _, _, _, _, _, _, _, hMain⟩
  have h := hMain hr_dyadic hQ_cube hδ_le_r hr_le_one
  rw [h_eq2] at h
  rw [h_eq1, tubeParamCoveringEqCard hδ hS_dyadic] at h
  exact h

/-- Convert a real cardinality covering bound to an `ENNReal` inequality. -/
lemma real_covering_bound_to_ennat {a b : ℕ} {C x : ℝ}
    (hC_nonneg : 0 ≤ C) (hx_nonneg : 0 ≤ x)
    (h : (a : ℝ) ≤ C * (b : ℝ) * x) :
    (↑a : ENNReal) ≤ ENNReal.ofReal C * (↑b : ENNReal) * ENNReal.ofReal x := by
  have h_pos : 0 ≤ C * (b : ℝ) * x := by positivity
  have h3 : 0 ≤ C * (b : ℝ) := by positivity
  have h4 : (↑b : ENNReal) = ENNReal.ofReal (b : ℝ) := by simp
  have h5 : ENNReal.ofReal C * ENNReal.ofReal (b : ℝ) = ENNReal.ofReal (C * (b : ℝ)) :=
    (ENNReal.ofReal_mul hC_nonneg).symm
  have h6 : ENNReal.ofReal (C * (b : ℝ)) * ENNReal.ofReal x = ENNReal.ofReal ((C * (b : ℝ)) * x) :=
    (ENNReal.ofReal_mul h3).symm
  have h_eq : ENNReal.ofReal C * (↑b : ENNReal) * ENNReal.ofReal x =
      ENNReal.ofReal (C * (b : ℝ) * x) := by
    calc
      ENNReal.ofReal C * (↑b : ENNReal) * ENNReal.ofReal x
        = ENNReal.ofReal C * ENNReal.ofReal (b : ℝ) * ENNReal.ofReal x := by rw [h4]
      _ = (ENNReal.ofReal C * ENNReal.ofReal (b : ℝ)) * ENNReal.ofReal x := by ring
      _ = ENNReal.ofReal (C * (b : ℝ)) * ENNReal.ofReal x := by rw [h5]
      _ = ENNReal.ofReal ((C * (b : ℝ)) * x) := h6
      _ = ENNReal.ofReal (C * (b : ℝ) * x) := by ring_nf
  have h_pos2 : 0 ≤ C * (b : ℝ) * x := by positivity
  have h1 : (↑a : ENNReal) ≤ ENNReal.ofReal (C * (b : ℝ) * x) := by
    have h5 : ENNReal.ofReal (a : ℝ) = (↑a : ENNReal) := by simp
    rw [← h5]
    have h_iff : ENNReal.ofReal (a : ℝ) ≤ ENNReal.ofReal (C * (b : ℝ) * x) ↔ (a : ℝ) ≤ C * (b : ℝ) * x :=
      ENNReal.ofReal_le_ofReal_iff h_pos2
    exact h_iff.mpr h
  rw [h_eq]
  exact h1

/-!
## Step 3: Refinement T̄

By double-counting incidences between tubes and the families `T(y)`,
we find a large refinement `T̄ ⊂ T` such that each `T ∈ T̄` belongs to
many of the `T(y)`. Averaging the `(δ,2s)`-set property over `y ∈ Y`
shows that `T̄` itself is a `(δ,2s)`-set.
-/

/-- **Step 3 (corrected).** Given a total tube family `𝒯` and subfamilies
`T_y ⊆ 𝒯` for `y ∈ Y`, where each `T_y` is a `(δ,2s,C)`-set, and each
`T_y` has cardinality at least `c * |𝒯|`, there exists a refinement
`T̄ ⊆ 𝒯` that is a `(δ,2s,4C/c²)`-set and has cardinality at least
`(c/2) * |𝒯|`. -/
lemma refinement_is_delta_2s_set {δ s C c : ℝ} {Y : Set ℝ}
    {𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    {T_y : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs_nonneg : 0 ≤ s) (hs_le_two : 2 * s ≤ 2)
    (hC_pos : 0 < C) (hc_pos : 0 < c)
    (hY_fin : Y.Finite) (hY_nonempty : Y.Nonempty)
    (hT_y_set : ∀ y ∈ Y, IsDeltaSCSet (d := 2) δ (2 * s) C
      (productLikeAppendixDyadicTubeParameterSet δ (T_y y)))
    (hT_y_sub : ∀ y ∈ Y, T_y y ⊆ 𝒯)
    (hT_y_dyadic : ∀ y ∈ Y, T_y y ⊆ appendixDyadicTubes δ)
    (h_card : ∀ y ∈ Y, ENat.toENNReal (T_y y).encard ≥
      ENNReal.ofReal c * ENat.toENNReal 𝒯.encard) :
    ∃ (T_bar : Set (Set (EuclideanSpace ℝ (Fin 2)))),
      T_bar ⊆ 𝒯 ∧
      IsDeltaSCSet (d := 2) δ (2 * s) (4 * C / c^2)
        (productLikeAppendixDyadicTubeParameterSet δ T_bar) ∧
      ENat.toENNReal T_bar.encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal 𝒯.encard ∧
      (∀ T ∈ T_bar, ENat.toENNReal ({y ∈ Y | T ∈ T_y y}).encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) := by
  let canon := productLikeAppendixDyadicTubeCanonicalParameterCube δ
  rcases hY_nonempty with ⟨y0, hy0⟩

  -- Finiteness of each T_y y
  have hTy_fin : ∀ y ∈ Y, (T_y y).Finite := by
    intro y hy
    have h1 : Bornology.IsBounded (productLikeAppendixDyadicTubeParameterSet δ (T_y y)) :=
      (hT_y_set y hy).1
    have h2 : dyadicCoveringNumber δ (productLikeAppendixDyadicTubeParameterSet δ (T_y y)) < ⊤ :=
      dyadicCoveringNumber_lt_top hδ h1
    have h3 : dyadicCoveringNumber δ (productLikeAppendixDyadicTubeParameterSet δ (T_y y)) = (T_y y).encard :=
      tubeParamCoveringEqCard hδ (hT_y_dyadic y hy)
    rw [h3] at h2
    exact Set.encard_lt_top_iff.mp h2

  -- Finiteness of 𝒯
  have h𝒯_fin : 𝒯.Finite := by
    by_contra h
    have h_top : 𝒯.encard = ⊤ := by rw [Set.encard_eq_top_iff] <;> exact h
    have h_top' : ENat.toENNReal 𝒯.encard = ⊤ := by rw [h_top] <;> simp
    have h_card0 := h_card y0 hy0
    have h_pos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc_pos
    have h_rhs_top : ENNReal.ofReal c * ENat.toENNReal 𝒯.encard = ⊤ := by
      rw [h_top']
      have h : ENNReal.ofReal c * ⊤ = ⊤ := by simp [h_pos.ne']
      exact h
    rw [h_rhs_top] at h_card0
    have h_eq : ENat.toENNReal (T_y y0).encard = ⊤ := top_le_iff.mp h_card0
    have h_cont : (T_y y0).encard = ⊤ := by exact Eq.symm ((fun {m n} => ENat.toENNReal_inj.mp) (id (Eq.symm h_eq)))
    have h_lt : (T_y y0).encard < ⊤ := Set.Finite.encard_lt_top (hTy_fin y0 hy0)
    rw [h_cont] at h_lt <;> simp at h_lt <;> tauto

  -- Nonemptiness of 𝒯
  have hTy0_nonempty : (T_y y0).Nonempty := by
    have hP_nonempty : (productLikeAppendixDyadicTubeParameterSet δ (T_y y0)).Nonempty :=
      (hT_y_set y0 hy0).2.1
    by_contra h
    have h' : T_y y0 = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h'] at hP_nonempty
    simp [productLikeAppendixDyadicTubeParameterSet] at hP_nonempty <;> tauto
  have h𝒯_nonempty : 𝒯.Nonempty := hTy0_nonempty.mono (hT_y_sub y0 hy0)

  -- Finset conversions
  let Yf : Finset ℝ := hY_fin.toFinset
  let 𝒯f : Finset (Set (EuclideanSpace ℝ (Fin 2))) := h𝒯_fin.toFinset
  let Tyf : ℝ → Finset (Set (EuclideanSpace ℝ (Fin 2))) := fun y =>
    if hy : y ∈ Y then (hTy_fin y hy).toFinset else ∅

  have hYf_eq : (Yf : Set ℝ) = Y := by exact hY_fin.coe_toFinset
  have h𝒯f_eq : (𝒯f : Set _) = 𝒯 := by exact h𝒯_fin.coe_toFinset
  have hTyf_eq : ∀ y ∈ Y, (↑(Tyf y) : Set _) = T_y y := by
    intro y hy; simp [Tyf, hy] <;> rfl
  have hTyf_sub : ∀ y ∈ Y, Tyf y ⊆ 𝒯f := by
    intro y hy
    have h1 : (↑(Tyf y) : Set _) ⊆ 𝒯 := by
      rw [hTyf_eq y hy] <;> exact hT_y_sub y hy
    have h2 : (↑(Tyf y) : Set (Set (EuclideanSpace ℝ (Fin 2)))) ⊆ (↑𝒯f : Set (Set (EuclideanSpace ℝ (Fin 2)))) := by
      rw [h𝒯f_eq] at *
      exact h1
    exact Finset.coe_subset.mp h2
  have hTyf_card : ∀ y ∈ Y, ENat.toENNReal (T_y y).encard = (↑(Tyf y).card : ENNReal) := by
    intro y hy
    have h4 : (T_y y).encard = ↑(Tyf y).card := by rw [← hTyf_eq y hy] <;> simp
    rw [h4] <;> rfl
  have h𝒯_card : ENat.toENNReal 𝒯.encard = (↑𝒯f.card : ENNReal) := by
    have h4 : 𝒯.encard = ↑𝒯f.card := by rw [← h𝒯f_eq] <;> simp
    rw [h4] <;> rfl

  -- Convert h_card to real inequalities
  have h_card_real : ∀ y ∈ Y, ((Tyf y).card : ℝ) ≥ c * (𝒯f.card : ℝ) := by
    intro y hy
    have h5 := h_card y hy
    rw [hTyf_card y hy, h𝒯_card] at h5
    have h_pos2 : 0 ≤ c * (𝒯f.card : ℝ) := by positivity
    have h_card_nonneg : 0 ≤ ((Tyf y).card : ℝ) := Nat.cast_nonneg _
    have h9 : (↑(Tyf y).card : ENNReal) = ENNReal.ofReal ((Tyf y).card : ℝ) := by norm_cast
    rw [h9] at h5
    have h6 : ENNReal.ofReal c * (↑𝒯f.card : ENNReal) = ENNReal.ofReal (c * (𝒯f.card : ℝ)) := by
      have h7 : 0 ≤ c := by linarith
      rw [ENNReal.ofReal_mul h7] <;> simp <;> ring
    rw [h6] at h5
    have h10 : ENNReal.ofReal (c * (𝒯f.card : ℝ)) ≤ ENNReal.ofReal ((Tyf y).card : ℝ) := h5
    have h11 : c * (𝒯f.card : ℝ) ≤ ((Tyf y).card : ℝ) := by exact (ENNReal.ofReal_le_ofReal_iff h_card_nonneg).mp h5
    exact h11

  -- Multiplicity function
  let m : (Set (EuclideanSpace ℝ (Fin 2))) → ℕ := fun T =>
    (Yf.filter (fun y => T ∈ Tyf y)).card
  have h1_m : ∀ T, m T = ∑ y ∈ Yf, if T ∈ Tyf y then 1 else 0 := by
    intro T; simp [m, Finset.filter_eq', Finset.sum_boole] <;> rfl

  -- Double counting
  have h_double_count : ∑ T ∈ 𝒯f, (m T : ℝ) = ∑ y ∈ Yf, ((Tyf y).card : ℝ) := by
    have h2 : ∑ T ∈ 𝒯f, (m T : ℝ) = ∑ T ∈ 𝒯f, ∑ y ∈ Yf, (if T ∈ Tyf y then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro T _; exact_mod_cast h1_m T
    rw [h2, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    have hyY : y ∈ Y := by
      have h : y ∈ (Yf : Set ℝ) := hy
      rw [hYf_eq] at h
      exact h
    have h3 : 𝒯f.filter (fun T => T ∈ Tyf y) = Tyf y := by
      ext T; simp [hTyf_sub y hyY] <;> tauto
    rw [Finset.sum_boole, h3] <;> norm_cast

  -- Lower bound on sum
  have h_sum_lower : ∑ y ∈ Yf, ((Tyf y).card : ℝ) ≥ (Yf.card : ℝ) * c * (𝒯f.card : ℝ) := by
    calc
      ∑ y ∈ Yf, ((Tyf y).card : ℝ)
        ≥ ∑ y ∈ Yf, c * (𝒯f.card : ℝ) := Finset.sum_le_sum (fun y hy => h_card_real y (by
        have h : y ∈ (Yf : Set ℝ) := hy
        rw [hYf_eq] at h
        exact h))
      _ = (Yf.card : ℝ) * c * (𝒯f.card : ℝ) := by simp [Finset.sum_const] <;> ring

  -- Define T_bar
  let threshold : ℝ := c * (Yf.card : ℝ) / 2
  let T_barf : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    𝒯f.filter (fun T => (m T : ℝ) ≥ threshold)
  let T_bar : Set (Set (EuclideanSpace ℝ (Fin 2))) := ↑T_barf

  have h_m_le_ycard : ∀ T ∈ 𝒯f, (m T : ℝ) ≤ (Yf.card : ℝ) := by
    intro T _; have h : m T ≤ Yf.card := Finset.card_filter_le _ _; exact_mod_cast h

  -- Size bound
  have h_sum_upper : ∑ T ∈ 𝒯f, (m T : ℝ) ≤
      (Yf.card : ℝ) * (T_barf.card : ℝ) + threshold * (𝒯f.card : ℝ) := by
    have h1 : ∑ T ∈ 𝒯f, (m T : ℝ) =
        ∑ T ∈ T_barf, (m T : ℝ) + ∑ T ∈ (𝒯f \ T_barf), (m T : ℝ) := by
      have h_disj : Disjoint T_barf (𝒯f \ T_barf) := by exact Finset.disjoint_sdiff
      have h_univ : T_barf ∪ (𝒯f \ T_barf) = 𝒯f := by ext x; simp [T_barf] <;> tauto
      rw [← Finset.sum_union h_disj, h_univ]
    rw [h1]
    have hT_barf_sub : T_barf ⊆ 𝒯f := Finset.filter_subset _ _
    have h2 : ∑ T ∈ T_barf, (m T : ℝ) ≤ (Yf.card : ℝ) * (T_barf.card : ℝ) := by
      calc
        ∑ T ∈ T_barf, (m T : ℝ)
          ≤ ∑ T ∈ T_barf, (Yf.card : ℝ) := Finset.sum_le_sum (fun T hT => h_m_le_ycard T (hT_barf_sub hT))
        _ = (Yf.card : ℝ) * (T_barf.card : ℝ) := by simp [Finset.sum_const] <;> ring
    have h3 : ∑ T ∈ (𝒯f \ T_barf), (m T : ℝ) ≤ threshold * ((𝒯f \ T_barf).card : ℝ) := by
      calc
        ∑ T ∈ (𝒯f \ T_barf), (m T : ℝ)
          ≤ ∑ T ∈ (𝒯f \ T_barf), threshold := Finset.sum_le_sum (fun T hT => by
            have hTin : T ∈ 𝒯f := Finset.mem_sdiff.mp hT |>.1
            have h5' : T ∉ T_barf := Finset.mem_sdiff.mp hT |>.2
            have h6 : ¬((m T : ℝ) ≥ threshold) := by
              by_contra h7
              have h8 : T ∈ T_barf := Finset.mem_filter.mpr ⟨hTin, h7⟩
              exact h5' h8
            linarith)
        _ = threshold * ((𝒯f \ T_barf).card : ℝ) := by simp [Finset.sum_const] <;> ring
    have h41 : (𝒯f \ T_barf) ⊆ 𝒯f := by simp
    have h4 : ((𝒯f \ T_barf).card : ℝ) ≤ (𝒯f.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h41
    have h_thresh_nonneg : 0 ≤ threshold := by positivity
    have h5 : threshold * ((𝒯f \ T_barf).card : ℝ) ≤ threshold * (𝒯f.card : ℝ) := by
      gcongr
    calc
      (∑ T ∈ T_barf, (m T : ℝ)) + (∑ T ∈ (𝒯f \ T_barf), (m T : ℝ))
        ≤ (Yf.card : ℝ) * (T_barf.card : ℝ) + threshold * ((𝒯f \ T_barf).card : ℝ) := by
          exact add_le_add h2 h3
      _ ≤ (Yf.card : ℝ) * (T_barf.card : ℝ) + threshold * (𝒯f.card : ℝ) := by
          exact add_le_add_right h5 _

  have h_ycard_pos : 0 < (Yf.card : ℝ) := by
    have hYf_nonempty : Yf.Nonempty := by
      have h1 : (Yf : Set ℝ) = Y := hYf_eq
      have h2 : (Yf : Set ℝ).Nonempty := by rw [h1]; exact ⟨y0, hy0⟩
      exact_mod_cast h2
    have h3 : 0 < Yf.card := Finset.card_pos.mpr hYf_nonempty
    exact_mod_cast h3
  have h_size : (T_barf.card : ℝ) ≥ (c / 2) * (𝒯f.card : ℝ) := by
    have h6 : (Yf.card : ℝ) * c * (𝒯f.card : ℝ) ≤ (Yf.card : ℝ) * (T_barf.card : ℝ) + threshold * (𝒯f.card : ℝ) := by
      calc
        (Yf.card : ℝ) * c * (𝒯f.card : ℝ)
          ≤ ∑ y ∈ Yf, ((Tyf y).card : ℝ) := h_sum_lower
        _ = ∑ T ∈ 𝒯f, (m T : ℝ) := h_double_count.symm
        _ ≤ (Yf.card : ℝ) * (T_barf.card : ℝ) + threshold * (𝒯f.card : ℝ) := h_sum_upper
    have h7 : threshold = c * (Yf.card : ℝ) / 2 := by rfl
    rw [h7] at h6
    have h9 : (Yf.card : ℝ) * ((c / 2) * (𝒯f.card : ℝ)) ≤ (Yf.card : ℝ) * (T_barf.card : ℝ) := by linarith
    calc
      (c / 2) * (𝒯f.card : ℝ)
        = ((Yf.card : ℝ) * ((c / 2) * (𝒯f.card : ℝ))) / (Yf.card : ℝ) := by
          field_simp [h_ycard_pos.ne'] <;> ring
      _ ≤ ((Yf.card : ℝ) * (T_barf.card : ℝ)) / (Yf.card : ℝ) := by gcongr
      _ = (T_barf.card : ℝ) := by
          field_simp [h_ycard_pos.ne'] <;> ring

  -- T_bar subset properties
  have hT_bar_sub : T_bar ⊆ 𝒯 := by
    have h : T_barf ⊆ 𝒯f := Finset.filter_subset _ _
    have h_coe1 : (↑T_barf : Set _) = T_bar := by simp [T_bar]
    have h_coe2 : (↑𝒯f : Set _) = 𝒯 := by simp [𝒯f]
    intro x hx
    have hx' : x ∈ (↑T_barf : Set _) := by rw [h_coe1] <;> exact hx
    have h4 : x ∈ (↑𝒯f : Set _) := h hx'
    rw [h_coe2] at h4
    exact h4

  have hT_bar_dyadic : T_bar ⊆ appendixDyadicTubes δ := by
    intro T hT
    have hT' : T ∈ T_barf := by exact_mod_cast hT
    have h_above : (m T : ℝ) ≥ threshold := (Finset.mem_filter.mp hT').2
    have h_thresh_pos : 0 < threshold := by positivity
    have h_pos : 0 < (m T : ℝ) := by linarith
    have h_m_pos : 0 < m T := by exact_mod_cast h_pos
    have h_exists : (Yf.filter (fun y => T ∈ Tyf y)).Nonempty := Finset.card_pos.mp h_m_pos
    rcases h_exists with ⟨y, hy⟩
    have hyYf : y ∈ Yf := (Finset.mem_filter.mp hy).1
    have hTin : T ∈ Tyf y := (Finset.mem_filter.mp hy).2
    have hyY : y ∈ Y := by
      have h : y ∈ (Yf : Set ℝ) := hyYf
      rw [hYf_eq] at h
      exact h
    have hT_in_Ty : T ∈ T_y y := by simpa [Tyf, hyY] using hTin
    exact hT_y_dyadic y hyY hT_in_Ty

  -- Nonemptiness
  have hT_bar_nonempty : T_bar.Nonempty := by
    have h9 : (T_barf.card : ℝ) > 0 := by
      have h10 : 0 < 𝒯f.card := Finset.card_pos.mpr (by exact (Set.Finite.toFinset_nonempty h𝒯_fin).mpr h𝒯_nonempty )
      have h11 : (T_barf.card : ℝ) ≥ (c / 2) * (𝒯f.card : ℝ) := h_size
      have h12 : (c / 2) * (𝒯f.card : ℝ) > 0 := by positivity
      linarith
    have h13 : 0 < T_barf.card := by exact_mod_cast h9
    exact Finset.card_pos.mp h13

  let P_bar := productLikeAppendixDyadicTubeParameterSet δ T_bar

  have hP_bar_nonempty : P_bar.Nonempty := by
    rcases hT_bar_nonempty with ⟨T, hT⟩
    have hT' : T ∈ appendixDyadicTubes δ := hT_bar_dyadic hT
    have h_cube : canon T ∈ dyadicCubes 2 δ := by
      simpa [canon, productLikeAppendixDyadicTubeCanonicalParameterCube, hT'] using
        (Classical.choose_spec hT').1.1
    have h_cube_nonempty : (canon T).Nonempty := by
      rcases h_cube with ⟨k, hk⟩
      rw [hk]
      exact dyadicCube_nonempty hδ k
    have h_in_Pbar : canon T ⊆ P_bar := by
      intro p hp
      simp only [P_bar, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion, Set.mem_image]
      exact ⟨canon T, ⟨T, hT, rfl⟩, hp⟩
    exact h_cube_nonempty.mono h_in_Pbar

  -- Boundedness
  have hP_bar_bdd : Bornology.IsBounded P_bar := by
    have h1 : ∀ T ∈ T_bar, Bornology.IsBounded (canon T) := by
      intro T hT
      have hT' : T ∈ appendixDyadicTubes δ := hT_bar_dyadic hT
      have h_cube : canon T ∈ dyadicCubes 2 δ := by
        simpa [canon, productLikeAppendixDyadicTubeCanonicalParameterCube, hT'] using
          (Classical.choose_spec hT').1.1
      rcases h_cube with ⟨k, hk⟩
      rw [hk]
      exact dyadicCube_bounded
    have h2 : Bornology.IsBounded (⋃ T ∈ T_barf, canon T) := by
      have h4 : ∀ T ∈ T_barf, Bornology.IsBounded (canon T) := fun T hT => h1 T (by simpa [T_bar] using hT)
      exact (Bornology.isBounded_biUnion_finset T_barf).mpr h1
    have hP_bar_eq : P_bar = (⋃ T ∈ T_barf, canon T) := by
      simp [P_bar, productLikeAppendixDyadicTubeParameterSet, T_bar]
      <;> rfl
    rw [hP_bar_eq]
    exact h2

  -- Covering bound (core)
  have h_covering_main : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 2))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 2 r → δ ≤ r → r ≤ 1 →
        ENat.toENNReal (dyadicCoveringNumber δ (P_bar ∩ Q)) ≤
          ENNReal.ofReal (4 * C / c^2) * ENat.toENNReal (dyadicCoveringNumber δ P_bar) *
            ENNReal.ofReal (r ^ (2 * s)) := by
    intro r Q hr_dyadic hQ_cube hδ_le_r hr_le_one
    let restrictQ (𝒮 : Finset (Set (EuclideanSpace ℝ (Fin 2)))) : Finset _ :=
      𝒮.filter (fun T => canon T ⊆ Q)
    let T_bar_Q := restrictQ T_barf

    have h_y_cover : ∀ y ∈ Yf, ((restrictQ (Tyf y)).card : ℝ) ≤
        C * ((Tyf y).card : ℝ) * (r ^ (2 * s)) := by
      intro y hy
      have hyY : y ∈ Y := by
        have h : y ∈ (Yf : Set ℝ) := hy
        rw [hYf_eq] at h
        exact h
      let S_y : Set (Set (EuclideanSpace ℝ (Fin 2))) := {T ∈ T_y y | canon T ⊆ Q}
      have hS_y_dyadic : S_y ⊆ appendixDyadicTubes δ := fun T hT => hT_y_dyadic y hyY hT.1
      have h_ennat := single_family_covering_bound hδ hδ_dyadic hr_dyadic hδ_le_r hr_le_one
        (hT_y_dyadic y hyY) (hT_y_set y hyY) hQ_cube
      have h_fin : S_y.Finite := (hTy_fin y hyY).subset (fun _ h => h.1)
      have h_eq1 : S_y.encard = ↑(restrictQ (Tyf y)).card := by
        have h3 : (↑S_y : Set _) = ↑(restrictQ (Tyf y)) := by
          ext T
          simp only [S_y, Set.mem_setOf_eq, restrictQ, Finset.mem_coe, Finset.mem_filter]
          have h4 : T ∈ T_y y ↔ T ∈ Tyf y := by
            rw [← hTyf_eq y hyY] <;> simp
          constructor
          · rintro ⟨h5, h6⟩
            exact ⟨h4.mp h5, h6⟩
          · rintro ⟨h5, h6⟩
            exact ⟨h4.mpr h5, h6⟩
        rw [h3] <;> simp
      have h_eq2 : (T_y y).encard = ↑(Tyf y).card := by
        rw [← hTyf_eq y hyY] <;> simp
      rw [h_eq1, h_eq2] at h_ennat
      set a := (restrictQ (Tyf y)).card with ha
      set b := (Tyf y).card with hb
      set x := r ^ (2 * s) with hx
      have hx_nonneg : 0 ≤ x := Real.rpow_nonneg (by linarith) _
      have hC_nonneg : 0 ≤ C := by linarith
      have h_b_nonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
      have h_rhs_eq : ENNReal.ofReal C * (↑b : ENNReal) * ENNReal.ofReal x =
          ENNReal.ofReal (C * (b : ℝ) * x) := by
        have h1 : (↑b : ENNReal) = ENNReal.ofReal (b : ℝ) := by norm_cast
        rw [h1]
        have h2 : ENNReal.ofReal C * ENNReal.ofReal (b : ℝ) =
            ENNReal.ofReal (C * (b : ℝ)) := by
          exact (ENNReal.ofReal_mul hC_nonneg).symm
        rw [h2]
        have h3 : ENNReal.ofReal (C * (b : ℝ)) * ENNReal.ofReal x =
            ENNReal.ofReal ((C * (b : ℝ)) * x) := by
          exact (ENNReal.ofReal_mul (mul_nonneg hC_nonneg h_b_nonneg)).symm
        rw [h3] <;> rfl
      have h10' : (↑a : ENNReal) ≤ ENNReal.ofReal C * (↑b : ENNReal) * ENNReal.ofReal x := by
        simpa [ha, hb, hx] using h_ennat
      rw [h_rhs_eq] at h10'
      have h4 : (↑a : ENNReal) = ENNReal.ofReal (a : ℝ) := by simp
      rw [h4] at h10'
      have h5 : 0 ≤ C * (b : ℝ) * x := by
        exact mul_nonneg (mul_nonneg hC_nonneg h_b_nonneg) hx_nonneg
      exact (ENNReal.ofReal_le_ofReal_iff h5).mp h10'

    have h_double_restrict : ∑ T ∈ restrictQ 𝒯f, (m T : ℝ) =
        ∑ y ∈ Yf, ((restrictQ (Tyf y)).card : ℝ) := by
      have h2 : ∑ T ∈ restrictQ 𝒯f, (m T : ℝ) =
          ∑ T ∈ restrictQ 𝒯f, ∑ y ∈ Yf, (if T ∈ Tyf y then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro T _
        exact_mod_cast h1_m T
      rw [h2, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      have hyY : y ∈ Y := by
        have h : y ∈ (Yf : Set ℝ) := hy
        rw [hYf_eq] at h
        exact h
      have h3 : (restrictQ 𝒯f).filter (fun T => T ∈ Tyf y) = restrictQ (Tyf y) := by
        ext T
        simp only [restrictQ, Finset.mem_filter]
        have h4 : T ∈ Tyf y → T ∈ 𝒯f := fun hTin => hTyf_sub y hyY hTin
        constructor
        · rintro ⟨⟨h5, h6⟩, h7⟩
          exact ⟨h7, h6⟩
        · rintro ⟨h7, h6⟩
          exact ⟨⟨h4 h7, h6⟩, h7⟩
      rw [Finset.sum_boole, h3] <;> norm_cast

    have h_thresh_pos : 0 < threshold := by positivity

    have h_lower : threshold * (T_bar_Q.card : ℝ) ≤ ∑ T ∈ T_bar_Q, (m T : ℝ) := by
      have h : ∀ T ∈ T_bar_Q, (m T : ℝ) ≥ threshold := by
        intro T hT
        have h8 : T ∈ T_barf ∧ canon T ⊆ Q := by
          simpa [T_bar_Q, restrictQ, Finset.mem_filter] using hT
        have h5 : T ∈ T_barf := h8.1
        exact (Finset.mem_filter.mp h5).2
      calc
        threshold * (T_bar_Q.card : ℝ)
          = ∑ T ∈ T_bar_Q, threshold := by rw [Finset.sum_const] <;> ring
        _ ≤ ∑ T ∈ T_bar_Q, (m T : ℝ) := Finset.sum_le_sum h

    have h_upper1 : ∑ T ∈ T_bar_Q, (m T : ℝ) ≤ ∑ T ∈ restrictQ 𝒯f, (m T : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro T hT
        have h8 : T ∈ T_barf ∧ canon T ⊆ Q := by
          simpa [T_bar_Q, restrictQ, Finset.mem_filter] using hT
        have h5 : T ∈ T_barf := h8.1
        have hTbarf_sub : T_barf ⊆ 𝒯f := Finset.filter_subset _ _
        have h6 : T ∈ 𝒯f := hTbarf_sub h5
        have h7 : canon T ⊆ Q := h8.2
        exact Finset.mem_filter.mpr ⟨h6, h7⟩
      · intro _ _ _; positivity

    have h_upper2 : ∑ T ∈ restrictQ 𝒯f, (m T : ℝ) ≤
        ∑ y ∈ Yf, C * ((Tyf y).card : ℝ) * (r ^ (2 * s)) := by
      rw [h_double_restrict]
      apply Finset.sum_le_sum
      intro y hy
      exact h_y_cover y hy

    have h_upper3 : ∑ y ∈ Yf, C * ((Tyf y).card : ℝ) * (r ^ (2 * s)) ≤
        (Yf.card : ℝ) * C * (𝒯f.card : ℝ) * (r ^ (2 * s)) := by
      have h4 : ∀ y ∈ Yf, ((Tyf y).card : ℝ) ≤ (𝒯f.card : ℝ) := by
        intro y hy
        have hyY : y ∈ Y := by
          have h : y ∈ (Yf : Set ℝ) := hy
          rw [hYf_eq] at h
          exact h
        have h_sub : Tyf y ⊆ 𝒯f := hTyf_sub y hyY
        exact_mod_cast Finset.card_le_card h_sub
      calc
        ∑ y ∈ Yf, C * ((Tyf y).card : ℝ) * (r ^ (2 * s))
          ≤ ∑ y ∈ Yf, C * (𝒯f.card : ℝ) * (r ^ (2 * s)) :=
            Finset.sum_le_sum (fun y hy =>
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (h4 y hy) (by linarith))
                (Real.rpow_nonneg (by linarith) _))
        _ = (Yf.card : ℝ) * C * (𝒯f.card : ℝ) * (r ^ (2 * s)) := by
          simp [Finset.sum_const] <;> ring

    have h_main_ineq : threshold * (T_bar_Q.card : ℝ) ≤
        (Yf.card : ℝ) * C * (𝒯f.card : ℝ) * (r ^ (2 * s)) :=
      le_trans h_lower (le_trans h_upper1 (le_trans h_upper2 h_upper3))

    have h_cover1 : (T_bar_Q.card : ℝ) ≤ (2 * C / c) * (𝒯f.card : ℝ) * (r ^ (2 * s)) := by
      set yc := (Yf.card : ℝ) with hyc
      set tc := (𝒯f.card : ℝ) with htc
      set rp := r ^ (2 * s) with hrp
      have hyc_pos : 0 < yc := h_ycard_pos
      have hc_pos' : 0 < c := hc_pos
      have h_algebra : (yc * C * tc * rp) / threshold = (2 * C / c) * tc * rp := by
        have hthresh : threshold = c * yc / 2 := by rfl
        rw [hthresh]
        have hyc_ne : yc ≠ 0 := hyc_pos.ne'
        have hc_ne : c ≠ 0 := hc_pos'.ne'
        have h1 : (c * yc / 2)⁻¹ = 2 / (c * yc) := by
          rw [inv_div] <;> norm_num
        calc
          (yc * C * tc * rp) / (c * yc / 2)
            = (yc * C * tc * rp) * (c * yc / 2)⁻¹ := by rw [div_eq_mul_inv]
          _ = (yc * C * tc * rp) * (2 / (c * yc)) := by rw [h1]
          _ = (yc * (2 * C * tc * rp)) / (c * yc) := by ring
          _ = (2 * C * tc * rp) / c := by
            have h2 : c * yc = yc * c := by ring
            rw [h2]
            have hyc_ne' : yc ≠ 0 := hyc_pos.ne'
            have hc_ne' : c ≠ 0 := hc_pos'.ne'
            field_simp [hyc_ne', hc_ne'] <;> ring
          _ = (2 * C / c) * tc * rp := by ring
      have h_result : (T_bar_Q.card : ℝ) ≤ (yc * C * tc * rp) / threshold := by
        have h_pos : 0 < threshold := h_thresh_pos
        have h_ne : threshold ≠ 0 := h_pos.ne'
        have h_mul_div : threshold * ((yc * C * tc * rp) / threshold) = yc * C * tc * rp := by
          field_simp [h_ne] <;> ring
        have h : threshold * (T_bar_Q.card : ℝ) ≤ yc * C * tc * rp := h_main_ineq
        rw [← h_mul_div] at h
        nlinarith
      have h_final1 : (T_bar_Q.card : ℝ) ≤ (2 * C / c) * tc * rp := by
        calc
          (T_bar_Q.card : ℝ) ≤ (yc * C * tc * rp) / threshold := h_result
          _ = (2 * C / c) * tc * rp := h_algebra
      exact h_final1

    have h_cover2 : (T_bar_Q.card : ℝ) ≤
        (4 * C / c^2) * (T_barf.card : ℝ) * (r ^ (2 * s)) := by
      set tbc := (T_barf.card : ℝ) with htbc
      set tc := (𝒯f.card : ℝ) with htc
      set rp := r ^ (2 * s) with hrp
      have hc_ne : c ≠ 0 := hc_pos.ne'
      have h_helper : (2 / c) * ((c / 2) * tc) = tc := by
        calc
          (2 / c) * ((c / 2) * tc)
            = ((2 / c) * (c / 2)) * tc := by ring
          _ = 1 * tc := by
            have h9 : (2 / c) * (c / 2) = 1 := by
              have hc_ne' : c ≠ 0 := hc_pos.ne'
              field_simp [hc_ne'] <;> ring
            rw [h9]
          _ = tc := by ring
      have h7 : tc ≤ (2 / c) * tbc := by
        have h8 : (2 / c) * tbc ≥ (2 / c) * ((c / 2) * tc) := by gcongr
        rw [h_helper] at h8
        exact h8
      have hrp_nonneg : 0 ≤ rp := Real.rpow_nonneg (by linarith) _
      have h10 : (2 * C / c) * (2 / c) = 4 * C / c^2 := by
        have hc_ne' : c ≠ 0 := hc_pos.ne'
        field_simp [hc_ne'] <;> ring
      have h_final : (2 * C / c) * ((2 / c) * tbc) * rp =
          (4 * C / c^2) * tbc * rp := by
        calc
          (2 * C / c) * ((2 / c) * tbc) * rp
            = ((2 * C / c) * (2 / c)) * tbc * rp := by ring
          _ = (4 * C / c^2) * tbc * rp := by rw [h10]
      have hC2_nonneg' : 0 ≤ 2 * C / c := by positivity
      have h_cover2_mul : (2 * C / c) * tc * rp ≤ (2 * C / c) * ((2 / c) * tbc) * rp :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 hC2_nonneg') hrp_nonneg
      calc
        (T_bar_Q.card : ℝ)
          ≤ (2 * C / c) * tc * rp := h_cover1
        _ ≤ (2 * C / c) * ((2 / c) * tbc) * rp := h_cover2_mul
        _ = (4 * C / c^2) * tbc * rp := h_final

    -- Convert to ENNReal and relate to covering numbers
    let S_bar_Q : Set (Set (EuclideanSpace ℝ (Fin 2))) := {T ∈ T_bar | canon T ⊆ Q}
    have hS_bar_Q_dyadic : S_bar_Q ⊆ appendixDyadicTubes δ := fun T hT => hT_bar_dyadic hT.1
    have h_eq_inter : P_bar ∩ Q = productLikeAppendixDyadicTubeParameterSet δ S_bar_Q :=
      paramSetIntersectCube hδ hδ_dyadic hr_dyadic hδ_le_r hT_bar_dyadic hQ_cube
    have h_eq_coverQ : dyadicCoveringNumber δ (P_bar ∩ Q) = S_bar_Q.encard := by
      rw [h_eq_inter]
      exact tubeParamCoveringEqCard hδ hS_bar_Q_dyadic
    have h_eq_cover : dyadicCoveringNumber δ P_bar = T_bar.encard :=
      tubeParamCoveringEqCard hδ hT_bar_dyadic
    have h_eq_card1 : S_bar_Q.encard = ↑(T_bar_Q.card) := by
      have h3 : (↑S_bar_Q : Set _) = ↑T_bar_Q := by
        ext T
        simp only [S_bar_Q, T_bar_Q, T_bar, restrictQ, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq]
        <;> aesop
      rw [h3] <;> simp
    have h_eq_card2 : T_bar.encard = ↑T_barf.card := by
      simp [T_bar] <;> rfl
    rw [h_eq_coverQ, h_eq_cover, h_eq_card1, h_eq_card2]
    have hC2_nonneg : 0 ≤ 4 * C / c^2 := by positivity
    have h_rpow_nonneg : 0 ≤ r ^ (2 * s) := Real.rpow_nonneg (by linarith) _
    exact real_covering_bound_to_ennat hC2_nonneg h_rpow_nonneg h_cover2

  -- Assemble conclusion
  have h_s2_nonneg : 0 ≤ 2 * s := by linarith [hs_nonneg]
  have h_s2_le_two : 2 * s ≤ 2 := hs_le_two
  have h_final_set : IsDeltaSCSet (d := 2) δ (2 * s) (4 * C / c^2) P_bar :=
    ⟨hP_bar_bdd, hP_bar_nonempty, by norm_num, hδ_dyadic, hδ, h_s2_nonneg, h_s2_le_two, by positivity,
      h_covering_main⟩

  have h_final_card : ENat.toENNReal T_bar.encard ≥
      ENNReal.ofReal (c / 2) * ENat.toENNReal 𝒯.encard := by
    have h11 : T_bar.encard = ↑T_barf.card := by simp [T_bar] <;> rfl
    have h1 : ENat.toENNReal T_bar.encard = (↑T_barf.card : ENNReal) := by
      rw [h11] <;> rfl
    have h3 : (c / 2) * (𝒯f.card : ℝ) ≤ (T_barf.card : ℝ) := h_size
    have h4 : 0 ≤ (T_barf.card : ℝ) := Nat.cast_nonneg _
    have h_ofReal_card : (↑T_barf.card : ENNReal) = ENNReal.ofReal (T_barf.card : ℝ) := by
      norm_cast
    have h_mul : ENNReal.ofReal ((c / 2) * (𝒯f.card : ℝ)) =
        ENNReal.ofReal (c / 2) * (↑𝒯f.card : ENNReal) := by
      have h7 : 0 ≤ c / 2 := by positivity
      rw [ENNReal.ofReal_mul h7] <;> norm_cast <;> ring
    have h8 : ENNReal.ofReal ((c / 2) * (𝒯f.card : ℝ)) ≤ ENNReal.ofReal (T_barf.card : ℝ) :=
      ENNReal.ofReal_le_ofReal_iff h4 |>.mpr h3
    have h9 : ENNReal.ofReal (c / 2) * (↑𝒯f.card : ENNReal) ≤ ENNReal.ofReal (T_barf.card : ℝ) :=
      h_mul ▸ h8
    have h10 : ENNReal.ofReal (c / 2) * (↑𝒯f.card : ENNReal) ≤ (↑T_barf.card : ENNReal) :=
      h_ofReal_card.symm ▸ h9
    simpa [h1, h𝒯_card] using h10

  -- Multiplicity bound: each T ∈ T_bar belongs to at least (c/2)·|Y| families
  have h_final_mult : ∀ T ∈ T_bar, ENat.toENNReal ({y ∈ Y | T ∈ T_y y}).encard ≥
      ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard := by
    intro T hT
    have hT' : T ∈ T_barf := by exact_mod_cast hT
    have h_above : (m T : ℝ) ≥ threshold := (Finset.mem_filter.mp hT').2
    have h_set_eq : ({y ∈ Y | T ∈ T_y y} : Set ℝ) = ↑(Yf.filter (fun y => T ∈ Tyf y)) := by
      ext y
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
      have h_y_in_Y : y ∈ Y ↔ y ∈ (Yf : Set ℝ) := by
        rw [hYf_eq] <;> rfl
      constructor
      · rintro ⟨hyY, hTin⟩
        have hyf : y ∈ Yf := by
          have h : y ∈ (Yf : Set ℝ) := by rw [hYf_eq] <;> exact hyY
          exact_mod_cast h
        have h_eq : T ∈ Tyf y := by
          have h : (↑(Tyf y) : Set _) = T_y y := hTyf_eq y hyY
          have h6 : T ∈ (↑(Tyf y) : Set _) := by
            rw [h]
            exact hTin
          exact_mod_cast h6
        exact ⟨hyf, h_eq⟩
      · rintro ⟨hyf, h_eq⟩
        have hyY : y ∈ Y := by
          have h : y ∈ (Yf : Set ℝ) := by exact_mod_cast hyf
          rw [hYf_eq] at h
          exact h
        have hTin : T ∈ T_y y := by
          have h : (↑(Tyf y) : Set _) = T_y y := hTyf_eq y hyY
          have h6 : T ∈ (↑(Tyf y) : Set _) := by exact_mod_cast h_eq
          rw [h] at h6
          exact h6
        exact ⟨hyY, hTin⟩
    have h_filter_eq : (Yf.filter (fun y => T ∈ Tyf y)).card = m T := by
      simp [m] <;> rfl
    have h_encard : (↑(Yf.filter (fun y => T ∈ Tyf y)) : Set ℝ).encard = ↑(m T) := by
      rw [Set.encard_coe_eq_coe_finsetCard, h_filter_eq]
    have h_card_eq : ENat.toENNReal ({y ∈ Y | T ∈ T_y y}).encard = ↑(m T) := by
      rw [h_set_eq, h_encard] <;> rfl
    rw [h_card_eq]
    have hY_card_eq : ENat.toENNReal Y.encard = ↑Yf.card := by
      rw [←hYf_eq, Set.encard_coe_eq_coe_finsetCard] <;> rfl
    rw [hY_card_eq]
    have h_thresh_eq : threshold = (c / 2) * (Yf.card : ℝ) := by
      simp [threshold] <;> ring
    rw [h_thresh_eq] at h_above
    have h_mul_eq : ENNReal.ofReal (c / 2) * ↑Yf.card =
        ENNReal.ofReal ((c / 2) * (Yf.card : ℝ)) := by
      have h7 : 0 ≤ c / 2 := by positivity
      have h8 : (↑Yf.card : ENNReal) = ENNReal.ofReal (Yf.card : ℝ) := by norm_cast
      rw [h8]
      rw [← ENNReal.ofReal_mul h7]
      <;> norm_cast
    have h_ennreal : ENNReal.ofReal ((c / 2) * (Yf.card : ℝ)) ≤ ↑(m T) := by
      have h3 : (c / 2) * (Yf.card : ℝ) ≤ (m T : ℝ) := h_above
      have h4 : ENNReal.ofReal ((c / 2) * (Yf.card : ℝ)) ≤ ENNReal.ofReal ((m T : ℝ)) :=
        ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h3
      have h5 : ENNReal.ofReal ((m T : ℝ)) = ↑(m T) := by norm_cast
      rw [h5] at h4
      exact h4
    rw [h_mul_eq]
    exact h_ennreal

  exact ⟨T_bar, hT_bar_sub, h_final_set, h_final_card, h_final_mult⟩

end ProductLikeIncidence
