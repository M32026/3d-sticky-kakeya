import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.ShapeSpace
import MyLeanRepo.Kakeya.CV.ShapeNet
import MyLeanRepo.Kakeya.CV.AuerbachEllipsoid
import MyLeanRepo.Kakeya.CV.EllipsoidShapeClose
import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.Tactic

/-!
# Stable finite-colour ellipsoid net

Strengthens the CV Lemma 8 interface with the `α³` same-colour separation
margin consumed by the selection-stability argument.

## Proof outline

1. Choose `β = 2` for the shape net separation parameter.
2. Let `α = √3 * β`. The Auerbach construction gives a `√3`-close ellipsoid
   at 0, and the shape net gives a `β`-close shape, so by transitivity the
   palette ellipsoid is `α`-close to the body.
3. Let `γ = α³` be the conflict parameter. Since `β ≤ γ`, the conflict graph
   on the shape net has bounded degree and admits a finite proper colouring.
4. The net consists of centered ellipsoids `(0, B.symm)` for `B ∈ shapeNet β`.
5. For separation: if two same-colour palette ellipsoids are `α³`-close at 0,
   then `homothetyAt_imp_shapeClose` gives `ShapeClose α³` of their inverse
   shapes, which is a conflict in the graph. A proper colouring then forces
   the shapes to be equal.
-/

noncomputable section

open Kakeya.CV
open Kakeya.CV.ShapeSpace
open Kakeya.CV.ShapeNet

namespace Kakeya.CV

theorem stable_finite_colour_ellipsoid_net :
    StableEllipsoidColouringStatement := by
  classical
  /- Constants -/
  let β : ℝ := 2
  have hβ : 1 < β := by norm_num
  have hβ_pos : 0 < β := by norm_num
  let α : ℝ := Real.sqrt 3 * β
  have h_sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hα_pos : 0 < α := by positivity
  have hα : 1 < α := by
    have h1 : (1 : ℝ) < Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    nlinarith
  let γ : ℝ := α ^ 3
  have hγ_pos : 0 < γ := by positivity
  have hβ_le_γ : β ≤ γ := by
    have h1 : 1 < α := hα
    have h2 : α ^ 3 > α := by
      have h3 : 1 < α := h1
      have h4 : α ^ 2 > 1 := by nlinarith
      nlinarith
    have h5 : α > β := by
      dsimp only [α, β]
      have h6 : Real.sqrt 3 > 1 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      nlinarith
    linarith

  /- Shape colouring -/
  rcases shapeNet_boundedDegree_gen β γ hβ hγ_pos hβ_le_γ with ⟨D, hD⟩
  let shapeCol : (Point 3 ≃ₗ[ℝ] Point 3) → Fin (D + 1) :=
    shapeColour_gen β γ D hD

  /- Net definition: all centered ellipsoids whose inverse shape is in shapeNet -/
  let net : Set EllipsoidParameter :=
    { E | E.1 = 0 ∧ E.2.symm ∈ shapeNet β }

  /- Colouring -/
  let N : ℕ := D + 1
  have hN_pos : 0 < N := by positivity
  let colour : EllipsoidParameter → Fin N := fun E => shapeCol E.2.symm

  /- All net ellipsoids are centered at 0 -/
  have h_center : ∀ E ∈ net, E.1 = 0 := by
    intro E hE
    exact hE.1

  /- Covering property -/
  have h_covering : ∀ (K : Set (Point 3)),
      JohnEllipsoid.IsConvexBody K →
      (∀ x, x ∈ K → -x ∈ K) →
      ∃ E, E ∈ net ∧
        AreHomotheticallyCloseAt 0 α K (ellipsoidCarrier E) := by
    intro K hK h_sym
    rcases symmetric_body_ellipsoid_approx hK (fun x hx => by
      have h : (0 : Point 3) + ((0 : Point 3) - x) = -x := by simp
      rw [h]
      exact h_sym x hx) with ⟨A_J, h_john_incl⟩
    let B_K : Point 3 ≃ₗ[ℝ] Point 3 := A_J.symm
    rcases shapeNet_covering β hβ B_K with ⟨B, hB_net, hShapeClose⟩
    have h1_incl : AreHomotheticallyCloseAt 0 β
        (JohnEllipsoid.ellipsoid 0 A_J)
        (JohnEllipsoid.ellipsoid 0 B.symm) := by
      have h_BK_symm : B_K.symm = A_J := by simp [B_K]
      have h := shapeClose_imp_homothety_at hβ_pos (0 : Point 3) hShapeClose
      rw [h_BK_symm] at h
      exact h
    have h_all : AreHomotheticallyCloseAt 0 α K (JohnEllipsoid.ellipsoid 0 B.symm) := by
      have h_trans : AreHomotheticallyCloseAt 0 (Real.sqrt 3 * β) K (JohnEllipsoid.ellipsoid 0 B.symm) :=
        AreHomotheticallyCloseAt.trans h_john_incl h1_incl
      have h_eq : Real.sqrt 3 * β = α := by
        dsimp only [α, β] <;> ring
      rw [h_eq] at h_trans
      exact h_trans
    let E : EllipsoidParameter := (0, B.symm)
    have hE_in_net : E ∈ net := by
      simp only [net, E, Set.mem_setOf_eq]
      <;> exact ⟨by trivial, hB_net⟩
    have h_goal : AreHomotheticallyCloseAt 0 α K (ellipsoidCarrier E) := by
      have h : ellipsoidCarrier E = JohnEllipsoid.ellipsoid 0 B.symm := by rfl
      rw [h]
      exact h_all
    exact ⟨E, hE_in_net, h_goal⟩

  /- Separation property -/
  have h_separation : ∀ (E₁ E₂ : EllipsoidParameter),
      E₁ ∈ net →
      E₂ ∈ net →
      colour E₁ = colour E₂ →
      AreHomotheticallyCloseAt 0 (α ^ 3)
        (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) →
      E₁ = E₂ := by
    intro E₁ E₂ hE₁ hE₂ hcol hclose
    let B₁ := E₁.2.symm
    let B₂ := E₂.2.symm
    have hB₁_net : B₁ ∈ shapeNet β := hE₁.2
    have hB₂_net : B₂ ∈ shapeNet β := hE₂.2
    have hE1_center : E₁.1 = 0 := hE₁.1
    have hE2_center : E₂.1 = 0 := hE₂.1
    have h_carrier1 : ellipsoidCarrier E₁ = JohnEllipsoid.ellipsoid 0 E₁.2 := by
      simp [ellipsoidCarrier, hE1_center]
    have h_carrier2 : ellipsoidCarrier E₂ = JohnEllipsoid.ellipsoid 0 E₂.2 := by
      simp [ellipsoidCarrier, hE2_center]
    rw [h_carrier1, h_carrier2] at hclose
    have hγ_eq : γ = α ^ 3 := by rfl
    have hclose' : AreHomotheticallyCloseAt 0 γ
        (JohnEllipsoid.ellipsoid 0 E₁.2) (JohnEllipsoid.ellipsoid 0 E₂.2) := by
      rw [hγ_eq]
      exact hclose
    have h_shapeClose : ShapeSpace.ShapeClose γ B₁ B₂ :=
      homothetyAt_imp_shapeClose hγ_pos hclose'
    have h_gc : graphConflictGen β γ B₁ B₂ := ⟨hB₁_net, hB₂_net, h_shapeClose⟩
    by_cases hne : B₁ = B₂
    · -- Shapes equal, so ellipsoid parameters equal
      have hA_eq : E₁.2 = E₂.2 := by
        have h : B₁ = B₂ := hne
        simpa [B₁, B₂] using congr_arg (fun (X : Point 3 ≃ₗ[ℝ] Point 3) => X.symm) h
      have hE_eq : E₁ = E₂ := by
        ext <;> simp [hE1_center, hE2_center, hA_eq]
      exact hE_eq
    · -- Shapes distinct, but same colour + conflict is impossible
      have h_proper : shapeCol B₁ ≠ shapeCol B₂ :=
        shapeColour_gen_isProper β γ D hD B₁ B₂ h_gc hne
      have h_col_eq : shapeCol B₁ = shapeCol B₂ := by
        simpa [colour] using hcol
      exact False.elim (h_proper h_col_eq)

  /- Assemble final statement -/
  refine ⟨α, N, net, colour, hα, hN_pos, h_center, h_covering, h_separation⟩

end Kakeya.CV
