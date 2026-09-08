import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.DilatedTubeBodyGeometry
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Recover tube provenance from a subfamily of dilated tube bodies

A `FactoringRefinement` of a dilated tube factoring returns a body subfamily.
The body indices still point to the original coarse tubes.  This module
recovers exactly those indexed tubes and transports the body shading without
changing any carrier, mass, or union.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- A tube subfamily induces the identically indexed subfamily of bodies at
any fixed common dilation. -/
def TubeSubfamily.toDilatedBodySubfamily
    {rho B : ℝ} {F : TubeFamily rho}
    (S : TubeSubfamily F) :
    Subfamily (dilatedTubeBodyFamily B F) where
  family := dilatedTubeBodyFamily B S.family
  embedding := S.embedding
  carrier_eq i := by
    change dilatedTubeCarrier B (S.family.tube i) =
      dilatedTubeCarrier B (F.tube (S.embedding i))
    rw [S.tube_eq i]

/-- The exact tube subfamily represented by a subfamily of actual dilated
tube bodies.  No new selection or reordering occurs. -/
def dilatedBodySubfamilyToTubeSubfamily
    {rho B : ℝ} {F : TubeFamily rho}
    (S : Subfamily (dilatedTubeBodyFamily B F)) : TubeSubfamily F where
  family :=
    { card := S.family.card
      tube := fun i => F.tube (S.embedding i) }
  embedding := S.embedding
  tube_eq := fun _ => rfl

@[simp]
lemma dilatedBodySubfamilyToTubeSubfamily_card
    {rho B : ℝ} {F : TubeFamily rho}
    (S : Subfamily (dilatedTubeBodyFamily B F)) :
    (dilatedBodySubfamilyToTubeSubfamily S).family.card = S.family.card :=
  rfl

/-- Regard a shading on the selected dilated bodies as a shading on the
dilated bodies of the recovered tube subfamily. -/
def dilatedBodySubfamilyShading
    {rho B : ℝ} {F : TubeFamily rho}
    (S : Subfamily (dilatedTubeBodyFamily B F))
    (Y : Shading S.family) :
    Shading
      (dilatedTubeBodyFamily B
        (dilatedBodySubfamilyToTubeSubfamily S).family) where
  carrier := Y.carrier
  measurable_carrier := Y.measurable_carrier
  subset_body i := by
    have h := Y.subset_body i
    rw [S.carrier_eq i] at h
    exact h

@[simp]
lemma dilatedBodySubfamilyShading_carrier
    {rho B : ℝ} {F : TubeFamily rho}
    (S : Subfamily (dilatedTubeBodyFamily B F))
    (Y : Shading S.family) (i : Fin S.family.card) :
    (dilatedBodySubfamilyShading S Y).carrier i = Y.carrier i :=
  rfl

@[simp]
lemma dilatedBodySubfamilyShading_mass
    {rho B : ℝ} {F : TubeFamily rho}
    (S : Subfamily (dilatedTubeBodyFamily B F))
    (Y : Shading S.family) :
    (dilatedBodySubfamilyShading S Y).mass = Y.mass :=
  rfl

@[simp]
lemma dilatedBodySubfamilyShading_union
    {rho B : ℝ} {F : TubeFamily rho}
    (S : Subfamily (dilatedTubeBodyFamily B F))
    (Y : Shading S.family) :
    (dilatedBodySubfamilyShading S Y).union = Y.union :=
  rfl

end Kakeya.Streamlined
