module

/-
  GridLineDirDist.lean

  Extends tubeFamily_covering_containment with a direction distance bound.
  Given L and x ∈ tube(r,L) ∩ B(0,1), constructs G ∈ tubeFamily r such that:
  1. x ∈ tube(2r, G)
  2. tube(r,L) ∩ B(0,2) ⊆ tube(2r, G)
  3. lineDirDist L G ≤ r/10

  The direction bound follows from angle_rounding: |θ_c - θ'| ≤ π/numAngles ≤ r/10,
  and lineDirDist(L, G) = |sin(θ_c - θ')| ≤ |θ_c - θ'|.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.TubeLine
public import MyLeanRepo.RadialBootstrapping.TubeFamilies
public import MyLeanRepo.RadialBootstrapping.GridGeometryCount
public import MyLeanRepo.RadialBootstrapping.GreedySelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping
namespace B1

/-- Direction distance from L to a grid line with normal angle θ' is ≤ |θ_c - θ'|,
    where θ_c is from L.angle_offset_rep. -/
lemma lineDirDist_to_grid_angle_bound
    (L : Line2) (θ_c : ℝ)
    (h_case : (normalVec θ_c = L.normalVector) ∨ (normalVec θ_c = -L.normalVector))
    (θ' a' : ℝ) :
    lineDirDist L (lineOfAngleOffset θ' a') ≤ |θ_c - θ'| := by
  let G := lineOfAngleOffset θ' a'
  let φ_u : ℝ := if normalVec θ_c = L.normalVector then θ_c + Real.pi / 2 else θ_c - Real.pi / 2
  have hcos : L.unitDirection 0 = Real.cos φ_u := by
    dsimp only [φ_u]
    split_ifs with h
    · -- Case normalVec θ_c = L.normalVector
      have h1 : (normalVec θ_c) 0 = L.unitDirection 1 := by
        rw [h, L.normalVector_component0]
      have h2 : L.unitDirection 1 = Real.cos θ_c := by
        have h21 : (normalVec θ_c) 0 = Real.cos θ_c := normalVec_component0 θ_c
        linarith
      have h3 : (normalVec θ_c) 1 = -L.unitDirection 0 := by
        rw [h, L.normalVector_component1]
      have h4 : L.unitDirection 0 = -Real.sin θ_c := by
        have h41 : (normalVec θ_c) 1 = Real.sin θ_c := normalVec_component1 θ_c
        linarith
      rw [h4]
      have h5 : Real.cos (θ_c + Real.pi / 2) = -Real.sin θ_c := by
        rw [Real.cos_add] <;> norm_num <;> ring
      exact h5.symm
    · -- Case normalVec θ_c ≠ L.normalVector
      have h' : normalVec θ_c = -L.normalVector := h_case.resolve_left h
      have h1 : (normalVec θ_c) 0 = -L.unitDirection 1 := by
        have h11 : (normalVec θ_c) 0 = (-L.normalVector) 0 := by rw [h']
        rw [h11]
        have h12 : (-L.normalVector) 0 = -L.normalVector 0 := by simp
        rw [h12, L.normalVector_component0] <;> ring
      have h2 : L.unitDirection 1 = -Real.cos θ_c := by
        have h21 : (normalVec θ_c) 0 = Real.cos θ_c := normalVec_component0 θ_c
        linarith
      have h3 : (normalVec θ_c) 1 = L.unitDirection 0 := by
        have h31 : (normalVec θ_c) 1 = (-L.normalVector) 1 := by rw [h']
        rw [h31]
        have h32 : (-L.normalVector) 1 = -L.normalVector 1 := by simp
        rw [h32, L.normalVector_component1] <;> ring
      have h4 : L.unitDirection 0 = Real.sin θ_c := by
        have h41 : (normalVec θ_c) 1 = Real.sin θ_c := normalVec_component1 θ_c
        linarith
      rw [h4]
      have h5 : Real.cos (θ_c - Real.pi / 2) = Real.sin θ_c := by
        rw [Real.cos_sub] <;> norm_num <;> ring
      exact h5.symm
  have hsin : L.unitDirection 1 = Real.sin φ_u := by
    dsimp only [φ_u]
    split_ifs with h
    · have h2 : L.unitDirection 1 = Real.cos θ_c := by
        have h1 : (normalVec θ_c) 0 = L.unitDirection 1 := by rw [h, L.normalVector_component0]
        have h21 : (normalVec θ_c) 0 = Real.cos θ_c := normalVec_component0 θ_c
        linarith
      rw [h2]
      have h5 : Real.sin (θ_c + Real.pi / 2) = Real.cos θ_c := by
        rw [Real.sin_add] <;> norm_num <;> ring
      exact h5.symm
    · have h' : normalVec θ_c = -L.normalVector := h_case.resolve_left h
      have h2 : L.unitDirection 1 = -Real.cos θ_c := by
        have h1 : (normalVec θ_c) 0 = -L.unitDirection 1 := by
          have h11 : (normalVec θ_c) 0 = (-L.normalVector) 0 := by rw [h']
          rw [h11]
          have h12 : (-L.normalVector) 0 = -L.normalVector 0 := by simp
          rw [h12, L.normalVector_component0] <;> ring
        have h21 : (normalVec θ_c) 0 = Real.cos θ_c := normalVec_component0 θ_c
        linarith
      rw [h2]
      have h5 : Real.sin (θ_c - Real.pi / 2) = -Real.cos θ_c := by
        rw [Real.sin_sub] <;> norm_num <;> ring
      exact h5.symm
  have h_main : lineDirDist G L = |Real.cos (θ' - φ_u)| :=
    lineDirDist_gridLine_eq_cos θ' a' L φ_u hcos hsin
  have h_perp : Real.cos (φ_u - θ_c) = 0 := by
    dsimp only [φ_u]
    split_ifs with h
    · have h_eq : θ_c + Real.pi / 2 - θ_c = Real.pi / 2 := by ring
      rw [h_eq] <;> norm_num
    · have h_eq : θ_c - Real.pi / 2 - θ_c = -Real.pi / 2 := by ring
      rw [h_eq]
      have h_neg : (-Real.pi / 2) = -(Real.pi / 2) := by ring
      rw [h_neg, Real.cos_neg] <;> norm_num
  have h_sin_sq : Real.sin (φ_u - θ_c) ^ 2 = 1 := by
    have h4 : Real.cos (φ_u - θ_c) ^ 2 + Real.sin (φ_u - θ_c) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    rw [h_perp] at h4 <;> linarith
  have h_abs_sin : |Real.sin (φ_u - θ_c)| = 1 := by
    have h5 : |Real.sin (φ_u - θ_c)| ^ 2 = 1 := by
      rw [sq_abs] <;> exact h_sin_sq
    have h6 : 0 ≤ |Real.sin (φ_u - θ_c)| := abs_nonneg _
    nlinarith
  have h_eq : |Real.cos (θ' - φ_u)| = |Real.sin (θ_c - θ')| := by
    have h1 : Real.cos (θ' - φ_u) = Real.sin (θ' - θ_c) * Real.sin (φ_u - θ_c) := by
      have h2 : θ' - φ_u = (θ' - θ_c) - (φ_u - θ_c) := by ring
      rw [h2, Real.cos_sub, h_perp] <;> ring
    have h_goal : |Real.cos (θ' - φ_u)| = |Real.sin (θ' - θ_c)| * |Real.sin (φ_u - θ_c)| := by
      rw [h1, abs_mul]
    have h7 : |Real.sin (θ' - θ_c)| = |Real.sin (θ_c - θ')| := by
      have h8 : Real.sin (θ' - θ_c) = -Real.sin (θ_c - θ') := by
        rw [show θ' - θ_c = -(θ_c - θ') by ring, Real.sin_neg] <;> ring
      rw [h8, abs_neg]
    rw [h_goal, h7, h_abs_sin] <;> ring
  calc lineDirDist L G
    = submoduleDirDist L.toAffine.direction G.toAffine.direction := by rfl
  _ = submoduleDirDist G.toAffine.direction L.toAffine.direction := submoduleDirDist_comm _ _
  _ = lineDirDist G L := by rfl
  _ = |Real.cos (θ' - φ_u)| := h_main
  _ = |Real.sin (θ_c - θ')| := h_eq
  _ ≤ |θ_c - θ'| := Real.abs_sin_le_abs
end B1
end RadialBootstrapping
