/-
Bridge from ModuleCat(ZMod 2) to AddCommGrpCat for the transfer sequence.

The forgetful functor forget₂ : ModuleCat R ⥤ AddCommGrpCat is exact.
It is lifted to chain complexes via mapHomologicalComplex.

This file also provides the identification between the singular chain complex
with Z/2 coefficients in ModuleCat(Z2) passed through the forgetful functor,
and the standard singular chain complex in AddCommGrpCat with Z/2 coefficients.
-/
import MyLeanRepo.Kakeya.BorsukUlam.TransferInstantiation
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.TransferSequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

noncomputable section

namespace BorsukUlamBackup

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial
open SeedMathlib.AlgebraicTopology.Degree

/-- The forgetful functor from Z/2-modules to abelian groups. -/
abbrev forgetZ2 : ModuleCat Z2 ⥤ AddCommGrpCat :=
  forget₂ (ModuleCat Z2) AddCommGrpCat

/-- forgetZ2 preserves finite limits. -/
instance forgetZ2PreservesFiniteLimits : PreservesFiniteLimits forgetZ2 :=
  PreservesLimitsOfSize.preservesFiniteLimits forgetZ2

/-- forgetZ2 preserves finite colimits. -/
instance forgetZ2PreservesFiniteColimits : PreservesFiniteColimits forgetZ2 := by
  infer_instance

/-- The forgetful functor lifted to chain complexes. -/
abbrev forgetZ2Chain :
    ChainComplex (ModuleCat Z2) ℕ ⥤ ChainComplex AddCommGrpCat ℕ :=
  forgetZ2.mapHomologicalComplex (ComplexShape.down ℕ)

/-- Applying the forgetful functor to a short exact sequence of chain complexes
    in ModuleCat(Z2) gives a short exact sequence in AddCommGrpCat. -/
lemma sphereTransferShortExactAddGrp (n : ℕ) :
    let S := ttransferShortComplex (pHash2 n) (pHash2_rangePi_eq_ker n)
    (S.map forgetZ2Chain).ShortExact :=
  (sphereTransferShortExact n).map_of_exact forgetZ2Chain

/-- Naturality of (unused, commented out) sigmaComparison w.r.t. Sigma.map'. -/
lemma sigmaComparison_naturality {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {α β : Type} {f : α → C} {g : β → C}
    [HasCoproduct f] [HasCoproduct (fun b => G.obj (f b))]
    [HasCoproduct g] [HasCoproduct (fun b => G.obj (g b))]
    (p : α → β) (q : ∀ a, f a ⟶ g (p a)) :
    sigmaComparison G f ≫ G.map (Sigma.map' p q) =
    Sigma.map' p (fun a : α => G.map (q a)) ≫ sigmaComparison G g := by
  let GF : α → D := fun b => G.obj (f b)
  let GG : β → D := fun b => G.obj (g b)
  let q' : ∀ (a : α), GF a ⟶ GG (p a) := fun a => G.map (q a)
  apply Limits.colimit.hom_ext (J := Discrete α)
  rintro ⟨a⟩
  have h1 : Sigma.ι GF a ≫ sigmaComparison G f = G.map (Sigma.ι f a) :=
    ι_comp_sigmaComparison (G := G) (f := f) a
  have h2 : G.map (Sigma.ι f a) ≫ G.map (Sigma.map' p q) =
      G.map (Sigma.ι f a ≫ Sigma.map' p q) := by
    exact (Functor.map_comp G _ _).symm
  have h3 : Sigma.ι f a ≫ Sigma.map' p q = q a ≫ Sigma.ι g (p a) :=
    Sigma.ι_comp_map' (f := f) (g := g) p q a
  have h4 : G.map (q a ≫ Sigma.ι g (p a)) =
      G.map (q a) ≫ G.map (Sigma.ι g (p a)) :=
    Functor.map_comp G _ _
  have h5 : Sigma.ι GG (p a) ≫ sigmaComparison G g = G.map (Sigma.ι g (p a)) :=
    ι_comp_sigmaComparison (G := G) (f := g) (p a)
  have h6 : Sigma.ι GF a ≫ Sigma.map' p q' = q' a ≫ Sigma.ι GG (p a) :=
    Sigma.ι_comp_map' (f := GF) (g := GG) p q' a
  calc
    Sigma.ι GF a ≫ (sigmaComparison G f ≫ G.map (Sigma.map' p q))
      = (Sigma.ι GF a ≫ sigmaComparison G f) ≫ G.map (Sigma.map' p q) := by
        simp only [Category.assoc]
    _ = G.map (Sigma.ι f a) ≫ G.map (Sigma.map' p q) := by rw [h1]
    _ = G.map (Sigma.ι f a ≫ Sigma.map' p q) := by rw [h2]
    _ = G.map (q a ≫ Sigma.ι g (p a)) := by rw [h3]
    _ = G.map (q a) ≫ G.map (Sigma.ι g (p a)) := by rw [h4]
    _ = G.map (q a) ≫ (Sigma.ι GG (p a) ≫ sigmaComparison G g) := by rw [h5]
    _ = (G.map (q a) ≫ Sigma.ι GG (p a)) ≫ sigmaComparison G g := by
        simp only [Category.assoc]
    _ = (Sigma.ι GF a ≫ Sigma.map' p q') ≫ sigmaComparison G g := by rw [h6]
    _ = Sigma.ι GF a ≫ (Sigma.map' p q' ≫ sigmaComparison G g) := by
        simp only [Category.assoc]

/-- Natural isomorphism: sigmaConst.obj R ⋙ forgetZ2 ≅ sigmaConst.obj (forgetZ2.obj R). -/
noncomputable def sigmaConstForgetIso (R2 : ModuleCat Z2) :
    (sigmaConst.obj R2) ⋙ forgetZ2 ≅ sigmaConst.obj (forgetZ2.obj R2) := by
  refine' NatIso.ofComponents (fun α => by
    exact PreservesCoproduct.iso forgetZ2 (fun (_ : α) => R2)) _
  intro α β f
  let iso_α := PreservesCoproduct.iso forgetZ2 (fun (_ : α) => R2)
  let iso_β := PreservesCoproduct.iso forgetZ2 (fun (_ : β) => R2)
  let fα : α → ModuleCat Z2 := fun (_ : α) => R2
  let fβ : β → ModuleCat Z2 := fun (_ : β) => R2
  let q : ∀ (a : α), fα a ⟶ fβ (f a) := fun (_ : α) => 𝟙 R2
  let F := (sigmaConst.obj R2) ⋙ forgetZ2
  let G' := sigmaConst.obj (forgetZ2.obj R2)
  have h_nat := sigmaComparison_naturality forgetZ2 (f := fα) (g := fβ) f q
  have h7 : iso_α.inv ≫ F.map f = G'.map f ≫ iso_β.inv := by
    exact h_nat
  exact iso_β.eq_comp_inv.mp (iso_α.inv_comp_eq.mp h7)

/-- Coefficient object Z/2 in ModuleCat. -/
abbrev R2 : ModuleCat Z2 := ModuleCat.of (ZMod 2) (ZMod 2)

/-- Natural isomorphism: singular chains with Z/2 coefficients (in ModuleCat),
    passed through the forgetful functor to AddCommGrpCat, is naturally isomorphic
    to the standard singular chain complex with Z/2 coefficients in AddCommGrpCat. -/
noncomputable def singularChainComplexForgetNatIso :
    ((singularChainComplexFunctor (ModuleCat Z2)).obj R2 ⋙ forgetZ2Chain) ≅
    (singularChainComplexFunctor AddCommGrpCat).obj (forgetZ2.obj R2) := by
  let e1 : (sigmaConst.obj R2) ⋙ forgetZ2 ≅ sigmaConst.obj (forgetZ2.obj R2) :=
    sigmaConstForgetIso R2
  let W1 := SimplicialObject.whiskering (Type _) (ModuleCat Z2)
  let W2 := SimplicialObject.whiskering (ModuleCat Z2) AddCommGrpCat
  let W3 := SimplicialObject.whiskering (Type _) AddCommGrpCat
  let A1 := alternatingFaceMapComplex (ModuleCat Z2)
  let A2 := alternatingFaceMapComplex AddCommGrpCat
  let G1 := (SSet.chainComplexFunctor (ModuleCat Z2)).obj R2
  let G2 := (SSet.chainComplexFunctor AddCommGrpCat).obj (forgetZ2.obj R2)

  have hG1 : G1 = W1.obj (sigmaConst.obj R2) ⋙ A1 := by rfl
  have hG2 : G2 = W3.obj (sigmaConst.obj (forgetZ2.obj R2)) ⋙ A2 := by rfl
  have h_comp : W1.obj (sigmaConst.obj R2) ⋙ W2.obj forgetZ2 =
      W3.obj ((sigmaConst.obj R2) ⋙ forgetZ2) := by rfl
  have h_afm : A1 ⋙ forgetZ2Chain = W2.obj forgetZ2 ⋙ A2 :=
    map_alternatingFaceMapComplex (F := forgetZ2)

  let step1 : G1 ⋙ forgetZ2Chain ≅
      (W1.obj (sigmaConst.obj R2) ⋙ A1) ⋙ forgetZ2Chain :=
    eqToIso (by rw [hG1])
  let step2 : (W1.obj (sigmaConst.obj R2) ⋙ A1) ⋙ forgetZ2Chain ≅
      W1.obj (sigmaConst.obj R2) ⋙ (A1 ⋙ forgetZ2Chain) :=
    eqToIso (by rfl)
  let step3 : W1.obj (sigmaConst.obj R2) ⋙ (A1 ⋙ forgetZ2Chain) ≅
      W1.obj (sigmaConst.obj R2) ⋙ (W2.obj forgetZ2 ⋙ A2) :=
    Functor.isoWhiskerLeft (W1.obj (sigmaConst.obj R2)) (eqToIso h_afm)
  let step4 : W1.obj (sigmaConst.obj R2) ⋙ (W2.obj forgetZ2 ⋙ A2) ≅
      (W1.obj (sigmaConst.obj R2) ⋙ W2.obj forgetZ2) ⋙ A2 :=
    eqToIso (by rfl)
  let step5 : (W1.obj (sigmaConst.obj R2) ⋙ W2.obj forgetZ2) ⋙ A2 ≅
      W3.obj ((sigmaConst.obj R2) ⋙ forgetZ2) ⋙ A2 :=
    eqToIso (by rw [h_comp])
  let step6 : W3.obj ((sigmaConst.obj R2) ⋙ forgetZ2) ⋙ A2 ≅
      W3.obj (sigmaConst.obj (forgetZ2.obj R2)) ⋙ A2 :=
    Functor.isoWhiskerRight (W3.mapIso e1) A2
  let step7 : W3.obj (sigmaConst.obj (forgetZ2.obj R2)) ⋙ A2 ≅ G2 :=
    eqToIso (by rw [hG2])

  let inner_iso : G1 ⋙ forgetZ2Chain ≅ G2 :=
    step1 ≪≫ step2 ≪≫ step3 ≪≫ step4 ≪≫ step5 ≪≫ step6 ≪≫ step7

  exact Functor.isoWhiskerLeft TopCat.toSSet inner_iso

/-- Component-wise isomorphism from the natural isomorphism. -/
noncomputable def singularChainComplexForgetIso (X : TopCat) :
    forgetZ2Chain.obj (((singularChainComplexFunctor (ModuleCat Z2)).obj R2).obj X) ≅
    ((singularChainComplexFunctor AddCommGrpCat).obj (forgetZ2.obj R2)).obj X :=
  singularChainComplexForgetNatIso.app X

/-- Naturality of `singularChainComplexForgetIso` with respect to continuous maps. -/
lemma singularChainComplexForgetIso_naturality {X Y : TopCat} (f : X ⟶ Y) :
    forgetZ2Chain.map (((singularChainComplexFunctor (ModuleCat Z2)).obj R2).map f) ≫
      (singularChainComplexForgetIso Y).hom =
    (singularChainComplexForgetIso X).hom ≫
      ((singularChainComplexFunctor AddCommGrpCat).obj (forgetZ2.obj R2)).map f := by
  dsimp only [singularChainComplexForgetIso]
  let e : _ ≅ _ := singularChainComplexForgetNatIso
  exact e.hom.naturality f

/-- The singular chain complex of S^n with Z/2 coefficients, passed through
    the forgetful functor, is isomorphic to the standard one in AddCommGrpCat. -/
noncomputable def chainSphere2ForgetIso (n : ℕ) :
    forgetZ2Chain.obj (ChainSphere2 n) ≅
    ((singularChainComplexFunctor AddCommGrpCat).obj (forgetZ2.obj R2)).obj (TopCat.of (Sphere n)) :=
  singularChainComplexForgetIso (TopCat.of (Sphere n))

end BorsukUlamBackup

end
