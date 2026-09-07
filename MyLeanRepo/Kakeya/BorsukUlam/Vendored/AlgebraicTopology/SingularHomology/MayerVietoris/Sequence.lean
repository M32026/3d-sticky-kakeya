module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.MayerVietoris.BoundaryIso
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.RelativeHomology

@[expose] public section

/-!
# Mayer-Vietoris Long Exact Sequence

From the short exact sequence of chain complexes:
  0 → C(U ∩ V) → C(U) ⊕ C(V) → C_small(X) → 0

we get a long exact sequence in homology. Using the small chain theorem
(quasi-isomorphism C_small(X) → C(X)), we obtain the Mayer-Vietoris sequence:

  ⋯ → Hₙ(U∩V) → Hₙ(U) ⊕ Hₙ(V) → Hₙ(X) → Hₙ₋₁(U∩V) → ⋯

The key consequence we use for computations is the boundary isomorphism:
when Hₙ(U) = Hₙ(V) = Hₙ₊₁(U) = Hₙ₊₁(V) = 0, then Hₙ₊₁(X) ≅ Hₙ(U∩V).
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial
open SSet

universe w v u

namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable (R : C) [HasBinaryBiproducts C] [HasBinaryBiproducts (ChainComplex C ℕ)]
variable [CategoryWithHomology C]

variable (ts : TwoSubspaces.{w})

section mvMapG_Epi

/-!
## Surjectivity of mvMapG

Every small simplex comes from U or from V, so the map
C(U) ⊕ C(V) → C_small(X) is an epimorphism.
-/

/-- Every small n-simplex is in the image of smallFromU or smallFromV. -/
lemma small_simplex_covered {n : ℕ} (τ : (smallSSet ts) _⦋n⦌) :
    (∃ (σ : (TopCat.toSSet.obj ts.U) _⦋n⦌), (smallFromU ts).app _ σ = τ) ∨
    (∃ (σ : (TopCat.toSSet.obj ts.V) _⦋n⦌), (smallFromV ts).app _ σ = τ) := by
  let τ₀ : (TopCat.toSSet.obj ts.X) _⦋n⦌ := (smallι ts).app _ τ
  have h_small : isSmallSimplex ts τ₀ := by
    have h : τ₀ ∈ (smallSubcomplex ts).obj _ := τ.prop
    simpa [isSmallSimplex, smallSubcomplex] using h
  have h_inj : Function.Injective ((smallι ts).app (Opposite.op (SimplexCategory.mk n))) := by
    exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a => a
  rcases h_small with (⟨σ_U, h_U⟩ | ⟨σ_V, h_V⟩)
  · left
    refine' ⟨σ_U, _⟩
    have h1 : (smallι ts).app _ ((smallFromU ts).app _ σ_U) = (TopCat.toSSet.map ts.jU).app _ σ_U := by
      have h_nat : (smallFromU ts).app _ ≫ (smallι ts).app _ = (TopCat.toSSet.map ts.jU).app _ :=
        NatTrans.congr_app (smallFromU_comp_ι ts) (Opposite.op (SimplexCategory.mk n))
      have h41 : ((smallFromU ts).app _ ≫ (smallι ts).app _) σ_U = (TopCat.toSSet.map ts.jU).app _ σ_U := by
        rw [h_nat]
      simpa [Category.assoc] using h41
    have h2 : (smallι ts).app _ ((smallFromU ts).app _ σ_U) = τ₀ := by
      rw [h1, h_U]
    have h3 : (smallι ts).app _ ((smallFromU ts).app _ σ_U) = (smallι ts).app _ τ := by
      exact h2
    exact h_inj h3
  · right
    refine' ⟨σ_V, _⟩
    have h1 : (smallι ts).app _ ((smallFromV ts).app _ σ_V) = (TopCat.toSSet.map ts.jV).app _ σ_V := by
      have h_nat : (smallFromV ts).app _ ≫ (smallι ts).app _ = (TopCat.toSSet.map ts.jV).app _ :=
        NatTrans.congr_app (smallFromV_comp_ι ts) (Opposite.op (SimplexCategory.mk n))
      have h41 : ((smallFromV ts).app _ ≫ (smallι ts).app _) σ_V = (TopCat.toSSet.map ts.jV).app _ σ_V := by
        rw [h_nat]
      simpa [Category.assoc] using h41
    have h2 : (smallι ts).app _ ((smallFromV ts).app _ σ_V) = τ₀ := by
      rw [h1, h_V]
    have h3 : (smallι ts).app _ ((smallFromV ts).app _ σ_V) = (smallι ts).app _ τ := by
      exact h2
    exact h_inj h3

omit [HasBinaryBiproducts C] [HasBinaryBiproducts (ChainComplex C ℕ)] [CategoryWithHomology C] in
/-- Degreewise auxiliary: if z vanishes on both smallChainFromU and smallChainFromV,
    then z = 0 in degree n. -/
lemma mvMapG_epi_degree_aux {n : ℕ} {Z : C}
    (z : (smallChainComplex C R ts).X n ⟶ Z)
    (hU : (smallChainFromU C R ts).f n ≫ z = 0)
    (hV : (smallChainFromV C R ts).f n ≫ z = 0) : z = 0 := by
  have h2 : ∀ (τ : (smallSSet ts) _⦋n⦌),
      (smallSSet ts).ιChainComplex τ ≫ z =
      (smallSSet ts).ιChainComplex τ ≫ (0 : _) := by
    intro τ
    have h3 := small_simplex_covered ts τ
    rcases h3 with (⟨σ_U, h_eq_U⟩ | ⟨σ_V, h_eq_V⟩)
    · -- τ is in image of U
      have h9 : (smallChainFromU C R ts).f n ≫ z = 0 := hU
      have h12 : (TopCat.toSSet.obj ts.U).ιChainComplex σ_U ≫ ((smallChainFromU C R ts).f n ≫ z) = (0 : R ⟶ Z) := by
        have h_zero : (TopCat.toSSet.obj ts.U).ιChainComplex σ_U ≫ (0 : ((TopCat.toSSet.obj ts.U).chainComplex R).X n ⟶ Z) = (0 : R ⟶ Z) := by simp
        exact h9.symm ▸ h_zero
      have h10 : ((TopCat.toSSet.obj ts.U).ιChainComplex σ_U ≫ (smallChainFromU C R ts).f n) ≫ z = 0 := by
        have h11 : ((TopCat.toSSet.obj ts.U).ιChainComplex σ_U ≫ (smallChainFromU C R ts).f n) ≫ z =
            (TopCat.toSSet.obj ts.U).ιChainComplex σ_U ≫ ((smallChainFromU C R ts).f n ≫ z) := Category.assoc _ _ _
        rw [h11]
        exact h12
      have h4 : (TopCat.toSSet.obj ts.U).ιChainComplex σ_U ≫ (smallChainFromU C R ts).f n =
          (smallSSet ts).ιChainComplex τ := by
        have h5 := ι_chainComplexMap_f (f := smallFromU ts) (R := R) (x := σ_U)
        rw [←h_eq_U]
        exact h5
      have h7 : (smallSSet ts).ιChainComplex τ ≫ z = 0 := by
        rw [←h4]
        exact h10
      rw [h7] ; simp
    · -- τ is in image of V
      have h9 : (smallChainFromV C R ts).f n ≫ z = 0 := hV
      have h12 : (TopCat.toSSet.obj ts.V).ιChainComplex σ_V ≫ ((smallChainFromV C R ts).f n ≫ z) = (0 : R ⟶ Z) := by
        have h_zero : (TopCat.toSSet.obj ts.V).ιChainComplex σ_V ≫ (0 : ((TopCat.toSSet.obj ts.V).chainComplex R).X n ⟶ Z) = (0 : R ⟶ Z) := by simp
        exact h9.symm ▸ h_zero
      have h10 : ((TopCat.toSSet.obj ts.V).ιChainComplex σ_V ≫ (smallChainFromV C R ts).f n) ≫ z = 0 := by
        have h11 : ((TopCat.toSSet.obj ts.V).ιChainComplex σ_V ≫ (smallChainFromV C R ts).f n) ≫ z =
            (TopCat.toSSet.obj ts.V).ιChainComplex σ_V ≫ ((smallChainFromV C R ts).f n ≫ z) := Category.assoc _ _ _
        rw [h11]
        exact h12
      have h4 : (TopCat.toSSet.obj ts.V).ιChainComplex σ_V ≫ (smallChainFromV C R ts).f n =
          (smallSSet ts).ιChainComplex τ := by
        have h5 := ι_chainComplexMap_f (f := smallFromV ts) (R := R) (x := σ_V)
        rw [←h_eq_V]
        exact h5
      have h7 : (smallSSet ts).ιChainComplex τ ≫ z = 0 := by
        rw [←h4]
        exact h10
      rw [h7] ; simp
  exact chainComplex_hom_ext (h := h2)

/-- **mvMapG is an epimorphism.**

    Every small simplex factors through U or V (by definition of small chains),
    so the map C(U) ⊕ C(V) → C_small(X) is surjective on chain groups,
    hence an epimorphism of chain complexes. -/
instance mvMapG_epi : Epi (mvMapG C R ts) := by
  have h_main : ∀ (Z : ChainComplex C ℕ) (z : smallChainComplex C R ts ⟶ Z),
      mvMapG C R ts ≫ z = 0 → z = 0 := by
    intro Z z hz
    have hU : smallChainFromU C R ts ≫ z = 0 := by
      have h1 : biprod.inl ≫ mvMapG C R ts = smallChainFromU C R ts :=
        biprod.inl_desc _ _
      calc
        smallChainFromU C R ts ≫ z
          = (biprod.inl ≫ mvMapG C R ts) ≫ z := by rw [h1]
        _ = biprod.inl ≫ (mvMapG C R ts ≫ z) := by rw [Category.assoc]
        _ = biprod.inl ≫ 0 := by rw [hz]
        _ = 0 := by simp
    have hV : smallChainFromV C R ts ≫ z = 0 := by
      have h1 : biprod.inr ≫ mvMapG C R ts = smallChainFromV C R ts :=
        biprod.inr_desc _ _
      calc
        smallChainFromV C R ts ≫ z
          = (biprod.inr ≫ mvMapG C R ts) ≫ z := by rw [h1]
        _ = biprod.inr ≫ (mvMapG C R ts ≫ z) := by rw [Category.assoc]
        _ = biprod.inr ≫ 0 := by rw [hz]
        _ = 0 := by simp
    have h_deg : ∀ n : ℕ, z.f n = 0 := by
      intro n
      exact mvMapG_epi_degree_aux C R ts (z.f n)
        (by rw [←HomologicalComplex.comp_f]; exact congr_arg (fun f : _ ⟶ Z => f.f n) hU)
        (by rw [←HomologicalComplex.comp_f]; exact congr_arg (fun f : _ ⟶ Z => f.f n) hV)
    have hz' : z = 0 := HomologicalComplex.hom_ext z 0 h_deg
    exact hz'
  exact (Preadditive.epi_iff_cancel_zero (mvMapG C R ts)).mpr h_main

end mvMapG_Epi

section mvMapF_Mono

/-!
## Injectivity of mvMapF

The map C(U∩V) → C(U) ⊕ C(V) given by c ↦ (iU* c, -iV* c) is a monomorphism
provided iU* (or iV*) is a monomorphism. This holds when iU is a subspace inclusion.
-/

variable [Mono ts.iU]

/-- **mvMapF is a monomorphism** (assuming iU is mono).

    Since mvMapF(c) = (iU* c, -iV* c), if mvMapF(c) = 0 then iU* c = 0,
    and since iU* is mono (because iU is mono), we have c = 0. -/
instance mvMapF_mono [Mono ((singularChainComplexFunctor C).obj R |>.map ts.iU)] :
    Mono (mvMapF C R ts) := by
  let iU_star := (singularChainComplexFunctor C).obj R |>.map ts.iU
  have h1 : mvMapF C R ts ≫ biprod.fst = iU_star := by
    simp [mvMapF, Preadditive.sub_comp]
    ; abel
  have h_main : ∀ (Z : ChainComplex C ℕ) (g : Z ⟶ singularChainComplex' C R ts.UV),
      g ≫ mvMapF C R ts = 0 → g = 0 := by
    intro Z g hg
    have h2 : g ≫ (mvMapF C R ts ≫ biprod.fst) = 0 := by
      calc
        g ≫ (mvMapF C R ts ≫ biprod.fst)
          = (g ≫ mvMapF C R ts) ≫ biprod.fst := by rw [Category.assoc]
        _ = 0 ≫ biprod.fst := by rw [hg]
        _ = 0 := by simp
    rw [h1] at h2
    have h3 : g = 0 := by
      have h4 := (Preadditive.mono_iff_cancel_zero iU_star).mp inferInstance Z g
      exact h4 h2
    exact h3
  exact Preadditive.mono_of_cancel_zero (mvMapF C R ts) (fun {Z} g hg => h_main Z g hg)

end mvMapF_Mono

/-- Assumption: for each n, the square of n-simplices is a pullback.
    Given simplices x in U and y in V that agree in X,
    there exists a simplex z in UV that restricts to both. -/
def DegreewisePullbackAssumption (ts : TwoSubspaces.{w}) : Prop :=
  ∀ (n : ℕ), ∀ (x : (TopCat.toSSet.obj ts.U) _⦋n⦌) (y : (TopCat.toSSet.obj ts.V) _⦋n⦌),
    (smallFromU ts).app _ x = (smallFromV ts).app _ y →
    ∃ (z : (TopCat.toSSet.obj ts.UV) _⦋n⦌),
      (TopCat.toSSet.map ts.iU).app _ z = x ∧
      (TopCat.toSSet.map ts.iV).app _ z = y

namespace mvExactProof

section Degreewise

variable (n : ℕ)

/-- smallFromU is injective on n-simplices (since jU is mono). -/
lemma sU_inj [Mono ts.jU] :
    Function.Injective ((smallFromU ts).app (Opposite.op (SimplexCategory.mk n))) := by
  intro x₁ x₂ h
  have h1 : (smallι ts).app (Opposite.op (SimplexCategory.mk n))
              (((smallFromU ts).app (Opposite.op (SimplexCategory.mk n))) x₁) =
            (smallι ts).app (Opposite.op (SimplexCategory.mk n))
              (((smallFromU ts).app (Opposite.op (SimplexCategory.mk n))) x₂) := by
    rw [h]
  have h_nat : (smallFromU ts).app (Opposite.op (SimplexCategory.mk n)) ≫ (smallι ts).app (Opposite.op (SimplexCategory.mk n)) =
      (TopCat.toSSet.map ts.jU).app (Opposite.op (SimplexCategory.mk n)) := by
    exact NatTrans.congr_app (smallFromU_comp_ι ts) (Opposite.op (SimplexCategory.mk n))
  have h3 : ∀ (x : (TopCat.toSSet.obj ts.U) _⦋n⦌),
      (smallι ts).app (Opposite.op (SimplexCategory.mk n)) (((smallFromU ts).app (Opposite.op (SimplexCategory.mk n))) x) =
      (TopCat.toSSet.map ts.jU).app (Opposite.op (SimplexCategory.mk n)) x := by
    intro x
    have h4 : ((smallFromU ts).app (Opposite.op (SimplexCategory.mk n)) ≫ (smallι ts).app (Opposite.op (SimplexCategory.mk n))) x =
        (TopCat.toSSet.map ts.jU).app (Opposite.op (SimplexCategory.mk n)) x := by
      rw [h_nat]
    simpa [Category.assoc] using h4
  have h2 : (TopCat.toSSet.map ts.jU).app (Opposite.op (SimplexCategory.mk n)) x₁ =
            (TopCat.toSSet.map ts.jU).app (Opposite.op (SimplexCategory.mk n)) x₂ := by
    rw [←h3 x₁, ←h3 x₂]
    exact h1
  have h_mono : Mono (TopCat.toSSet.map ts.jU) := by
    exact Functor.map_mono (TopCat.toSSet) ts.jU
  have h_inj : Function.Injective ((TopCat.toSSet.map ts.jU).app (Opposite.op (SimplexCategory.mk n))) := by
    have h : ∀ (X Y : TopCat.{w}) (f : X ⟶ Y) [Mono f],
        Function.Injective ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n))) := by
      intro X Y f _
      exact injective_of_mono ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌))
    exact h ts.U ts.X ts.jU
  exact h_inj h2

/-- smallFromV is injective on n-simplices (since jV is mono). -/
lemma sV_inj [Mono ts.jV] :
    Function.Injective ((smallFromV ts).app (Opposite.op (SimplexCategory.mk n))) := by
  intro y₁ y₂ h
  have h1 : (smallι ts).app (Opposite.op (SimplexCategory.mk n))
              (((smallFromV ts).app (Opposite.op (SimplexCategory.mk n))) y₁) =
            (smallι ts).app (Opposite.op (SimplexCategory.mk n))
              (((smallFromV ts).app (Opposite.op (SimplexCategory.mk n))) y₂) := by
    rw [h]
  have h_nat : (smallFromV ts).app (Opposite.op (SimplexCategory.mk n)) ≫ (smallι ts).app (Opposite.op (SimplexCategory.mk n)) =
      (TopCat.toSSet.map ts.jV).app (Opposite.op (SimplexCategory.mk n)) := by
    exact NatTrans.congr_app (smallFromV_comp_ι ts) (Opposite.op (SimplexCategory.mk n))
  have h3 : ∀ (y : (TopCat.toSSet.obj ts.V) _⦋n⦌),
      (smallι ts).app (Opposite.op (SimplexCategory.mk n)) (((smallFromV ts).app (Opposite.op (SimplexCategory.mk n))) y) =
      (TopCat.toSSet.map ts.jV).app (Opposite.op (SimplexCategory.mk n)) y := by
    intro y
    have h4 : ((smallFromV ts).app (Opposite.op (SimplexCategory.mk n)) ≫ (smallι ts).app (Opposite.op (SimplexCategory.mk n))) y =
        (TopCat.toSSet.map ts.jV).app (Opposite.op (SimplexCategory.mk n)) y := by
      rw [h_nat]
    simpa [Category.assoc] using h4
  have h2 : (TopCat.toSSet.map ts.jV).app (Opposite.op (SimplexCategory.mk n)) y₁ =
            (TopCat.toSSet.map ts.jV).app (Opposite.op (SimplexCategory.mk n)) y₂ := by
    rw [←h3 y₁, ←h3 y₂]
    exact h1
  have h_mono : Mono (TopCat.toSSet.map ts.jV) := by
    exact Functor.map_mono (TopCat.toSSet) ts.jV
  have h_inj : Function.Injective ((TopCat.toSSet.map ts.jV).app (Opposite.op (SimplexCategory.mk n))) := by
    have h : ∀ (X Y : TopCat.{w}) (f : X ⟶ Y) [Mono f],
        Function.Injective ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n))) := by
      intro X Y f _
      exact injective_of_mono ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌))
    exact h ts.V ts.X ts.jV
  exact h_inj h2

omit [HasBinaryBiproducts C] [HasBinaryBiproducts (ChainComplex C ℕ)] [CategoryWithHomology C] in
/-- Given a : C_U → Z and b : C_V → Z that agree on C_UV,
    there exists l : C_small → Z such that sU* ≫ l = a and sV* ≫ l = b. -/
theorem exists_lift (h_pullback : DegreewisePullbackAssumption ts)
    [Mono ts.jU] [Mono ts.jV]
    {Z : C}
    (a : (singularChainComplex' C R ts.U).X n ⟶ Z)
    (b : (singularChainComplex' C R ts.V).X n ⟶ Z)
    (h : ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n ≫ a =
         ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n ≫ b) :
    ∃ (l : (smallChainComplex C R ts).X n ⟶ Z),
      (smallChainFromU C R ts).f n ≫ l = a ∧
      (smallChainFromV C R ts).f n ≫ l = b := by
  let sU_map := (smallFromU ts).app (Opposite.op (SimplexCategory.mk n))
  let sV_map := (smallFromV ts).app (Opposite.op (SimplexCategory.mk n))
  let iU_map := (TopCat.toSSet.map ts.iU).app (Opposite.op (SimplexCategory.mk n))
  let iV_map := (TopCat.toSSet.map ts.iV).app (Opposite.op (SimplexCategory.mk n))

  have h_main : ∀ (τ : (smallSSet ts) _⦋n⦌), ∃ (hτ : R ⟶ Z),
      (∀ (x : (TopCat.toSSet.obj ts.U) _⦋n⦌), sU_map x = τ →
        (TopCat.toSSet.obj ts.U).ιChainComplex x ≫ a = hτ) ∧
      (∀ (y : (TopCat.toSSet.obj ts.V) _⦋n⦌), sV_map y = τ →
        (TopCat.toSSet.obj ts.V).ιChainComplex y ≫ b = hτ) := by
    intro τ
    have h_cov := small_simplex_covered ts τ
    rcases h_cov with (⟨x, hx⟩ | ⟨y, hy⟩)
    · -- Case 1: τ comes from U
      refine ⟨(TopCat.toSSet.obj ts.U).ιChainComplex x ≫ a, ?_, ?_⟩
      · -- First conjunct: for any x' with sU(x') = τ, ιU(x') ≫ a = ιU(x) ≫ a
        intro x' hx'
        have h_eq : x' = x := sU_inj ts n (by rwa [hx])
        rw [h_eq]
      · -- Second conjunct: for any y with sV(y) = τ, ιV(y) ≫ b = ιU(x) ≫ a
        intro y hy'
        have h_pb : ∃ (z : (TopCat.toSSet.obj ts.UV) _⦋n⦌),
            iU_map z = x ∧ iV_map z = y :=
          h_pullback n x y (by rw [hx, hy'])
        rcases h_pb with ⟨z, hz1, hz2⟩
        have h3 : ((TopCat.toSSet.obj ts.UV).ιChainComplex z ≫
                     ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n) ≫ a =
                   ((TopCat.toSSet.obj ts.UV).ιChainComplex z ≫
                     ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n) ≫ b := by
          have h_iU : ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n ≫ a =
                      ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n ≫ b := h
          have h_goal : (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫ (((singularChainComplexFunctor C).obj R).map ts.iU).f n ≫ a =
                       (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫ (((singularChainComplexFunctor C).obj R).map ts.iV).f n ≫ b :=
            congr_arg (fun f : _ => (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫ f) h_iU
          simpa [Category.assoc] using h_goal
        have h4 : (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫
                    ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n =
                  (TopCat.toSSet.obj ts.U).ιChainComplex (iU_map z) := by
          exact SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map ts.iU) (R := R) (x := z)
        have h5 : (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫
                    ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n =
                  (TopCat.toSSet.obj ts.V).ιChainComplex (iV_map z) := by
          exact SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map ts.iV) (R := R) (x := z)
        rw [h4, h5] at h3
        rw [hz1, hz2] at h3
        exact h3.symm
    · -- Case 2: τ comes from V
      refine ⟨(TopCat.toSSet.obj ts.V).ιChainComplex y ≫ b, ?_, ?_⟩
      · -- First conjunct: for any x with sU(x) = τ, ιU(x) ≫ a = ιV(y) ≫ b
        intro x hx'
        have h_pb : ∃ (z : (TopCat.toSSet.obj ts.UV) _⦋n⦌),
            iU_map z = x ∧ iV_map z = y :=
          h_pullback n x y (by rw [hx', hy])
        rcases h_pb with ⟨z, hz1, hz2⟩
        have h3 : ((TopCat.toSSet.obj ts.UV).ιChainComplex z ≫
                     ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n) ≫ a =
                   ((TopCat.toSSet.obj ts.UV).ιChainComplex z ≫
                     ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n) ≫ b := by
          have h_iU : ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n ≫ a =
                      ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n ≫ b := h
          have h_goal : (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫ (((singularChainComplexFunctor C).obj R).map ts.iU).f n ≫ a =
                       (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫ (((singularChainComplexFunctor C).obj R).map ts.iV).f n ≫ b :=
            congr_arg (fun f : _ => (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫ f) h_iU
          simpa [Category.assoc] using h_goal
        have h4 : (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫
                    ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n =
                  (TopCat.toSSet.obj ts.U).ιChainComplex (iU_map z) := by
          exact SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map ts.iU) (R := R) (x := z)
        have h5 : (TopCat.toSSet.obj ts.UV).ιChainComplex z ≫
                    ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n =
                  (TopCat.toSSet.obj ts.V).ιChainComplex (iV_map z) := by
          exact SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map ts.iV) (R := R) (x := z)
        rw [h4, h5] at h3
        rw [hz1, hz2] at h3
        exact h3
      · -- Second conjunct: for any y' with sV(y') = τ, ιV(y') ≫ b = ιV(y) ≫ b
        intro y' hy'
        have h_eq : y' = y := sV_inj ts n (by rwa [hy])
        rw [h_eq]

  choose hτ h1 h2 using h_main
  let h_isColimit := (smallSSet ts).isColimitChainComplexXCofan R n
  let h_cocone : Cocone (Discrete.functor (fun (_ : (smallSSet ts) _⦋n⦌) => R)) :=
    { pt := Z
      ι := { app := fun j => hτ j.as
             naturality := fun {X Y} f => by
               have hX : X = Y := by
                 let f' : X.as = Y.as := by exact Discrete.eq_of_hom f
                 apply Discrete.ext
                 exact f'
               subst hX
               simp } }
  let l := h_isColimit.desc h_cocone

  refine ⟨l, ?_, ?_⟩
  · -- Show sU_star ≫ l = a
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj ts.U) (R := R) (n := n)
    intro x
    let τ : (smallSSet ts) _⦋n⦌ := sU_map x
    have h7 : (TopCat.toSSet.obj ts.U).ιChainComplex x ≫ (smallChainFromU C R ts).f n =
              (smallSSet ts).ιChainComplex τ := by
      exact SSet.ι_chainComplexMap_f (f := smallFromU ts) (R := R) (x := x)
    have h_fac : (smallSSet ts).ιChainComplex τ ≫ l = hτ τ := by
      exact h_isColimit.fac h_cocone (Discrete.mk τ)
    calc
      (TopCat.toSSet.obj ts.U).ιChainComplex x ≫ (smallChainFromU C R ts).f n ≫ l
        = ((TopCat.toSSet.obj ts.U).ιChainComplex x ≫ (smallChainFromU C R ts).f n) ≫ l := by rw [Category.assoc]
      _ = (smallSSet ts).ιChainComplex τ ≫ l := by
        exact congr_arg (fun f : _ => f ≫ l) h7
      _ = hτ τ := h_fac
      _ = (TopCat.toSSet.obj ts.U).ιChainComplex x ≫ a := (h1 τ x rfl).symm
  · -- Show sV_star ≫ l = b
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj ts.V) (R := R) (n := n)
    intro y
    let τ : (smallSSet ts) _⦋n⦌ := sV_map y
    have h7 : (TopCat.toSSet.obj ts.V).ιChainComplex y ≫ (smallChainFromV C R ts).f n =
              (smallSSet ts).ιChainComplex τ := by
      exact SSet.ι_chainComplexMap_f (f := smallFromV ts) (R := R) (x := y)
    have h_fac : (smallSSet ts).ιChainComplex τ ≫ l = hτ τ := by
      exact h_isColimit.fac h_cocone (Discrete.mk τ)
    calc
      (TopCat.toSSet.obj ts.V).ιChainComplex y ≫ (smallChainFromV C R ts).f n ≫ l
        = ((TopCat.toSSet.obj ts.V).ιChainComplex y ≫ (smallChainFromV C R ts).f n) ≫ l := by rw [Category.assoc]
      _ = (smallSSet ts).ιChainComplex τ ≫ l := by
        exact congr_arg (fun f : _ => f ≫ l) h7
      _ = hτ τ := h_fac
      _ = (TopCat.toSSet.obj ts.V).ιChainComplex y ≫ b := (h2 τ y rfl).symm

/-- The square of SSet maps commutes: iU* ; smallFromU = iV* ; smallFromV. -/
lemma square_commutes_sset :
    TopCat.toSSet.map ts.iU ≫ smallFromU ts =
    TopCat.toSSet.map ts.iV ≫ smallFromV ts := by
  have h1 : (TopCat.toSSet.map ts.iU ≫ smallFromU ts) ≫ smallι ts =
             (TopCat.toSSet.map ts.iV ≫ smallFromV ts) ≫ smallι ts := by
    calc
      (TopCat.toSSet.map ts.iU ≫ smallFromU ts) ≫ smallι ts
        = TopCat.toSSet.map ts.iU ≫ (smallFromU ts ≫ smallι ts) := by rw [Category.assoc]
      _ = TopCat.toSSet.map ts.iU ≫ TopCat.toSSet.map ts.jU := by rw [smallFromU_comp_ι]
      _ = TopCat.toSSet.map (ts.iU ≫ ts.jU) := by rw [← Functor.map_comp]
      _ = TopCat.toSSet.map (ts.iV ≫ ts.jV) := by rw [ts.comm]
      _ = TopCat.toSSet.map ts.iV ≫ TopCat.toSSet.map ts.jV := by rw [← Functor.map_comp]
      _ = TopCat.toSSet.map ts.iV ≫ (smallFromV ts ≫ smallι ts) := by rw [smallFromV_comp_ι]
      _ = (TopCat.toSSet.map ts.iV ≫ smallFromV ts) ≫ smallι ts := by rw [Category.assoc]
  have h_mono : Mono (smallι ts) := by
    letI : Mono (smallSubcomplex ts).ι := by exact inferInstance
    exact this
  exact h_mono.right_cancellation _ _ h1

omit [HasBinaryBiproducts C] [HasBinaryBiproducts (ChainComplex C ℕ)] [CategoryWithHomology C] in
/-- The square of n-th chain groups is a pushout. -/
theorem degreewise_isPushout [Mono ts.jU] [Mono ts.jV]
    (h_pullback : DegreewisePullbackAssumption ts) :
    IsPushout
      (((singularChainComplexFunctor C).obj R |>.map ts.iU).f n)
      (((singularChainComplexFunctor C).obj R |>.map ts.iV).f n)
      ((smallChainFromU C R ts).f n)
      ((smallChainFromV C R ts).f n) := by
  let iU_star := ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n
  let iV_star := ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n
  let sU_star := (smallChainFromU C R ts).f n
  let sV_star := (smallChainFromV C R ts).f n
  have h_comm : iU_star ≫ sU_star = iV_star ≫ sV_star := by
    let F : SSet.{w} ⥤ ChainComplex C ℕ := (SSet.chainComplexFunctor C).obj R
    have h41 : ((singularChainComplexFunctor C).obj R).map ts.iU = F.map (TopCat.toSSet.map ts.iU) := by rfl
    have h42 : ((singularChainComplexFunctor C).obj R).map ts.iV = F.map (TopCat.toSSet.map ts.iV) := by rfl
    have h43 : smallChainFromU C R ts = F.map (smallFromU ts) := by rfl
    have h44 : smallChainFromV C R ts = F.map (smallFromV ts) := by rfl
    have h_sset : TopCat.toSSet.map ts.iU ≫ smallFromU ts =
                   TopCat.toSSet.map ts.iV ≫ smallFromV ts :=
      square_commutes_sset ts
    have h_chain : ((singularChainComplexFunctor C).obj R).map ts.iU ≫ smallChainFromU C R ts =
                    ((singularChainComplexFunctor C).obj R).map ts.iV ≫ smallChainFromV C R ts := by
      rw [h41, h42, h43, h44]
      have h_comp1 : F.map (TopCat.toSSet.map ts.iU) ≫ F.map (smallFromU ts) =
                       F.map (TopCat.toSSet.map ts.iU ≫ smallFromU ts) := by exact Eq.symm (F.map_comp (TopCat.toSSet.map ts.iU) (smallFromU ts))
      have h_comp2 : F.map (TopCat.toSSet.map ts.iV) ≫ F.map (smallFromV ts) =
                       F.map (TopCat.toSSet.map ts.iV ≫ smallFromV ts) := by exact Eq.symm (F.map_comp (TopCat.toSSet.map ts.iV) (smallFromV ts))
      have h_goal : F.map (TopCat.toSSet.map ts.iU ≫ smallFromU ts) =
                    F.map (TopCat.toSSet.map ts.iV ≫ smallFromV ts) := by rw [h_sset]
      calc
        F.map (TopCat.toSSet.map ts.iU) ≫ F.map (smallFromU ts)
          = F.map (TopCat.toSSet.map ts.iU ≫ smallFromU ts) := h_comp1
        _ = F.map (TopCat.toSSet.map ts.iV ≫ smallFromV ts) := h_goal
        _ = F.map (TopCat.toSSet.map ts.iV) ≫ F.map (smallFromV ts) := h_comp2.symm
    exact congr_arg (fun f : _ => f.f n) h_chain
  apply IsPushout.mk' h_comm
  · -- Uniqueness
    intro Z φ φ' h1 h2
    have hU : sU_star ≫ φ = sU_star ≫ φ' := h1
    have hV : sV_star ≫ φ = sV_star ≫ φ' := h2
    have hU' : sU_star ≫ (φ - φ') = 0 := by
      rw [Preadditive.comp_sub]
      rw [hU]
      ; simp
    have hV' : sV_star ≫ (φ - φ') = 0 := by
      rw [Preadditive.comp_sub]
      rw [hV]
      ; simp
    have h_eq : φ - φ' = 0 := mvMapG_epi_degree_aux C R ts (φ - φ') hU' hV'
    exact sub_eq_zero.mp h_eq
  · -- Existence
    intro Z a b h
    have h_exists : ∃ (l : (smallChainComplex C R ts).X n ⟶ Z),
        (smallChainFromU C R ts).f n ≫ l = a ∧
        (smallChainFromV C R ts).f n ≫ l = b :=
      exists_lift C R ts n h_pullback a b h
    exact h_exists

end Degreewise

end mvExactProof

section Exactness

/-!
## Exactness in the middle

ker(mvMapG) = im(mvMapF)

This requires the square to be a pullback (UV = U ∩ V).
We assume degreewise that the square of n-simplices is a pullback:
given x ∈ U_n, y ∈ V_n with jU_n(x) = jV_n(y) in small_n,
there exists z ∈ UV_n with iU_n(z) = x and iV_n(z) = y.

The inclusion im(mvMapF) ≤ ker(mvMapG) follows from mvMapF ≫ mvMapG = 0,
which is already part of the ShortComplex structure.
The reverse inclusion requires the pullback property.
-/

variable (h_pullback : DegreewisePullbackAssumption ts)
variable [Mono ts.jU] [Mono ts.jV]

omit [HasBinaryBiproducts C] [CategoryWithHomology C] in
/-- The Mayer-Vietoris short complex is exact at the middle term
    (assuming the square is a pullback degreewise).

    Proof: exactness of chain complexes can be checked degreewise.
    In each degree n, the square of chain groups is a pushout,
    so the associated short complex is exact. -/
theorem mvShortComplex_exact (h_pullback : DegreewisePullbackAssumption ts) :
    (mvShortComplex C R ts).Exact := by
  have h_degreewise : ∀ (n : ℕ),
      ((mvShortComplex C R ts).map (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Exact := by
    intro n
    let iU_star := ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n
    let iV_star := ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n
    let sU_star := (smallChainFromU C R ts).f n
    let sV_star := (smallChainFromV C R ts).f n
    have h_push : IsPushout iU_star iV_star sU_star sV_star :=
      mvExactProof.degreewise_isPushout C R ts n h_pullback
    let S_n := (mvShortComplex C R ts).map (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
    have h_main : S_n.Exact := by
      dsimp only [S_n, mvShortComplex, mvMapF, mvMapG]
      let f := (mvMapF C R ts).f n
      let g := (mvMapG C R ts).f n
      let K := singularChainComplex' C R ts.U
      let L := singularChainComplex' C R ts.V
      let Y := (K ⊞ L).X n
      let inl_chain : K ⟶ K ⊞ L := biprod.inl
      let inr_chain : L ⟶ K ⊞ L := biprod.inr
      let inl_deg : K.X n ⟶ Y := inl_chain.f n
      let inr_deg : L.X n ⟶ Y := inr_chain.f n
      have h_inl_g : inl_deg ≫ g = (smallChainFromU C R ts).f n := by
        have h : inl_chain ≫ mvMapG C R ts = smallChainFromU C R ts := by
          exact biprod.inl_desc _ _
        exact congr_arg (fun k : _ => k.f n) h
      have h_inr_g : inr_deg ≫ g = (smallChainFromV C R ts).f n := by
        have h : inr_chain ≫ mvMapG C R ts = smallChainFromV C R ts := by
          exact biprod.inr_desc _ _
        exact congr_arg (fun k : _ => k.f n) h
      have h_zero : f ≫ g = 0 := by
        have h : (mvMapF C R ts) ≫ (mvMapG C R ts) = 0 := mvMapF_comp_mvMapG C R ts
        exact congr_arg (fun k : _ => k.f n) h
      have h_jointly_monic : ∀ {Z : C} (h1 h2 : Y ⟶ Z),
          inl_deg ≫ h1 = inl_deg ≫ h2 → inr_deg ≫ h1 = inr_deg ≫ h2 → h1 = h2 := by
        intro Z h1 h2 h_inl h_inr
        let fst_chain : K ⊞ L ⟶ K := biprod.fst
        let snd_chain : K ⊞ L ⟶ L := biprod.snd
        let fst_deg : Y ⟶ K.X n := fst_chain.f n
        let snd_deg : Y ⟶ L.X n := snd_chain.f n
        have h_total : fst_deg ≫ inl_deg + snd_deg ≫ inr_deg = 𝟙 Y := by
          have h : fst_chain ≫ inl_chain + snd_chain ≫ inr_chain = 𝟙 (K ⊞ L) :=
            biprod.total
          exact congr_arg (fun k : _ => k.f n) h
        calc
          h1 = (𝟙 Y) ≫ h1 := by rw [Category.id_comp]
          _ = (fst_deg ≫ inl_deg + snd_deg ≫ inr_deg) ≫ h1 := by rw [h_total]
          _ = (fst_deg ≫ inl_deg) ≫ h1 + (snd_deg ≫ inr_deg) ≫ h1 := by
            rw [Preadditive.add_comp]
          _ = fst_deg ≫ (inl_deg ≫ h1) + snd_deg ≫ (inr_deg ≫ h1) := by
            rw [Category.assoc, Category.assoc]
          _ = fst_deg ≫ (inl_deg ≫ h2) + snd_deg ≫ (inr_deg ≫ h2) := by
            rw [h_inl, h_inr]
          _ = (fst_deg ≫ inl_deg) ≫ h2 + (snd_deg ≫ inr_deg) ≫ h2 := by
            rw [Category.assoc, Category.assoc]
          _ = (fst_deg ≫ inl_deg + snd_deg ≫ inr_deg) ≫ h2 := by
            rw [Preadditive.add_comp]
          _ = (𝟙 Y) ≫ h2 := by rw [h_total]
          _ = h2 := by rw [Category.id_comp]
      have h_lift : ∀ {Z : C} (k : Y ⟶ Z),
          f ≫ k = 0 → { l : (smallChainComplex C R ts).X n ⟶ Z // g ≫ l = k } := by
        intro Z k hk
        let a := inl_deg ≫ k
        let b := inr_deg ≫ k
        have h_f_def : f = ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n ≫ inl_deg -
                        ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n ≫ inr_deg := by
          simp [mvMapF, f, inl_deg, inr_deg, inl_chain, inr_chain]
          ; rfl
        have h_eq : ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n ≫ a =
                   ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n ≫ b := by
          rw [h_f_def] at hk
          have h2 : (((singularChainComplexFunctor C).obj R |>.map ts.iU).f n ≫ inl_deg -
                     ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n ≫ inr_deg) ≫ k = 0 := hk
          have h3 : ((singularChainComplexFunctor C).obj R |>.map ts.iU).f n ≫ inl_deg ≫ k -
                     ((singularChainComplexFunctor C).obj R |>.map ts.iV).f n ≫ inr_deg ≫ k = 0 := by
            simpa [Preadditive.sub_comp] using h2
          simpa [a, b, sub_eq_zero] using h3
        have h_exists : ∃ (l : (smallChainComplex C R ts).X n ⟶ Z),
            (smallChainFromU C R ts).f n ≫ l = a ∧
            (smallChainFromV C R ts).f n ≫ l = b :=
          mvExactProof.exists_lift C R ts n h_pullback a b h_eq
        let l : (smallChainComplex C R ts).X n ⟶ Z := Classical.choose h_exists
        have hla : (smallChainFromU C R ts).f n ≫ l = a := (Classical.choose_spec h_exists).1
        have hlb : (smallChainFromV C R ts).f n ≫ l = b := (Classical.choose_spec h_exists).2
        have h1 : inl_deg ≫ (g ≫ l) = inl_deg ≫ k := by
          calc
            inl_deg ≫ (g ≫ l) = (inl_deg ≫ g) ≫ l := by rw [Category.assoc]
            _ = (smallChainFromU C R ts).f n ≫ l := by rw [h_inl_g]
            _ = a := hla
            _ = inl_deg ≫ k := by rfl
        have h2 : inr_deg ≫ (g ≫ l) = inr_deg ≫ k := by
          calc
            inr_deg ≫ (g ≫ l) = (inr_deg ≫ g) ≫ l := by rw [Category.assoc]
            _ = (smallChainFromV C R ts).f n ≫ l := by rw [h_inr_g]
            _ = b := hlb
            _ = inr_deg ≫ k := by rfl
        have hgl : g ≫ l = k := h_jointly_monic (g ≫ l) k h1 h2
        exact ⟨l, hgl⟩
      have h_isColim : IsColimit (CokernelCofork.ofπ g h_zero) :=
        CokernelCofork.IsColimit.ofπ' g h_zero (fun {Z} k hk => h_lift k hk)
      exact ShortComplex.exact_of_g_is_cokernel _ h_isColim
    exact h_main
  let S := mvShortComplex C R ts
  have h_main : S.Exact := by
    have h1 : S.Exact ↔ IsZero S.homology := S.exact_iff_isZero_homology
    rw [h1]
    rw [IsZero.iff_id_eq_zero]
    have h_goal : (𝟙 S.homology) = 0 := by
      ext i
      have h_i : (S.map (HomologicalComplex.eval C (ComplexShape.down ℕ) i)).Exact := h_degreewise i
      have h2 : IsZero ((S.map (HomologicalComplex.eval C (ComplexShape.down ℕ) i)).homology) := by
        rwa [ShortComplex.exact_iff_isZero_homology] at h_i
      have h3 : IsZero ((HomologicalComplex.eval C (ComplexShape.down ℕ) i).obj S.homology) :=
        (S.mapHomologyIso (HomologicalComplex.eval C (ComplexShape.down ℕ) i)).isZero_iff.mp h2
      have h4 : (𝟙 ((HomologicalComplex.eval C (ComplexShape.down ℕ) i).obj S.homology)) = 0 := by
        rwa [IsZero.iff_id_eq_zero] at h3
      change (𝟙 ((HomologicalComplex.eval C (ComplexShape.down ℕ) i).obj S.homology)) = 0
      exact h4
    exact h_goal
  exact h_main

end Exactness

section ShortExact

/-!
## The short exact sequence

Assembling the three parts: mono + exact + epi = ShortExact.
-/

variable [Mono ts.iU] [Mono ts.jU] [Mono ts.jV]
variable (h_pullback : DegreewisePullbackAssumption ts)

omit [HasBinaryBiproducts C] [CategoryWithHomology C] in
/-- **Mayer-Vietoris SES is short exact.**

    The sequence 0 → C(U∩V) → C(U)⊕C(V) → C_small(X) → 0 is short exact,
    assuming iU is mono and the square is a pullback. -/
theorem mvSES_shortExact' (h_pullback : DegreewisePullbackAssumption ts) :
    (mvShortComplex C R ts).ShortExact :=
  { exact := mvShortComplex_exact C R ts h_pullback,
    mono_f := mvMapF_mono C R ts,
    epi_g := mvMapG_epi C R ts }


end ShortExact

section BoundaryIsoHelper

/-!
## Helper for the boundary isomorphism

We prove the boundary isomorphism in a minimal context to avoid
type inference performance issues in heavier sections.
-/

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable [CategoryWithHomology C]
variable (R : C)
variable (ts : TwoSubspaces.{w})

/-- **Boundary isomorphism helper (light context).**

    Given any short exact sequence of chain complexes, if the middle
    complex has trivial homology in degrees n+1 and n, then the
    connecting homomorphism gives an isomorphism H_{n+1}(X₃) ≅ H_n(X₁). -/
noncomputable def boundaryIso_helper
    {S : ShortComplex (ChainComplex C ℕ)}
    (hS : S.ShortExact) (n : ℕ)
    (h_succ : IsZero (S.X₂.homology (n + 1)))
    (h_n : IsZero (S.X₂.homology n)) :
    S.X₃.homology (n + 1) ≅ S.X₁.homology n := by
  have hij : (ComplexShape.down ℕ).Rel (n + 1) n := by
    simp [ComplexShape.down_Rel]
  exact Algebra.Homology.shortExact_δIso hS hij h_succ h_n

/-- **Boundary isomorphism for the Mayer-Vietoris small chain complex.**

    Given the short exact sequence 0 → C(UV) → C(U)⊕C(V) → C_small → 0,
    if H_{n+1}(C(U)⊕C(V)) = 0 and H_n(C(U)⊕C(V)) = 0, then the connecting
    homomorphism gives an isomorphism H_{n+1}(small) ≅ H_n(UV).

    Proved in the light `BoundaryIsoHelper` context to avoid the type class
    diamond performance issue that occurs when both `[Preadditive C]` and
    `[Abelian C]` are present as separate variables. -/
noncomputable def mv_boundaryIso_small (n : ℕ)
    (hS : (mvShortComplex C R ts).ShortExact)
    (h_mid_succ : IsZero ((mvShortComplex C R ts).X₂.homology (n + 1)))
    (h_mid_n : IsZero ((mvShortComplex C R ts).X₂.homology n)) :
    (mvShortComplex C R ts).X₃.homology (n + 1) ≅
    (mvShortComplex C R ts).X₁.homology n :=
  boundaryIso_helper hS n h_mid_succ h_mid_n

end BoundaryIsoHelper

section BiprodHomology

/-!
## Homology of biproducts

If both chain complexes have trivial homology in degree n,
then so does their biproduct.
-/

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable [HasBinaryBiproducts C] [HasBinaryBiproducts (ChainComplex C ℕ)]
variable [CategoryWithHomology C]
variable {K L : ChainComplex C ℕ} {n : ℕ}

omit [HasCoproducts C] [HasBinaryBiproducts C] in
/-- If both factors have trivial homology in degree n, then so does their biproduct. -/
lemma isZero_biprod_homology
    (hK : IsZero (K.homology n)) (hL : IsZero (L.homology n)) :
    IsZero ((K ⊞ L).homology n) := by
  let π₁ := homologyMap (biprod.fst : K ⊞ L ⟶ K) n
  let π₂ := homologyMap (biprod.snd : K ⊞ L ⟶ L) n
  let ι₁ := homologyMap (biprod.inl : K ⟶ K ⊞ L) n
  let ι₂ := homologyMap (biprod.inr : L ⟶ K ⊞ L) n
  have hι₁ : ι₁ = 0 := by
    have h : ∀ (f g : K.homology n ⟶ (K ⊞ L).homology n), f = g := hK.eq_of_src
    exact h ι₁ 0
  have hι₂ : ι₂ = 0 := by
    have h : ∀ (f g : L.homology n ⟶ (K ⊞ L).homology n), f = g := hL.eq_of_src
    exact h ι₂ 0
  have hπ₁ : π₁ = 0 := by
    have h : ∀ (f g : (K ⊞ L).homology n ⟶ K.homology n), f = g := hK.eq_of_tgt
    exact h π₁ 0
  have hπ₂ : π₂ = 0 := by
    have h : ∀ (f g : (K ⊞ L).homology n ⟶ L.homology n), f = g := hL.eq_of_tgt
    exact h π₂ 0
  have h_biprod_id :
      (biprod.fst : K ⊞ L ⟶ K) ≫ (biprod.inl : K ⟶ K ⊞ L) +
      (biprod.snd : K ⊞ L ⟶ L) ≫ (biprod.inr : L ⟶ K ⊞ L) = 𝟙 (K ⊞ L) := by
    apply HomologicalComplex.hom_ext
    intro i
    simp
  have h1 : homologyMap ((biprod.fst : K ⊞ L ⟶ K) ≫ (biprod.inl : K ⟶ K ⊞ L) +
      (biprod.snd : K ⊞ L ⟶ L) ≫ (biprod.inr : L ⟶ K ⊞ L)) n =
      homologyMap (𝟙 (K ⊞ L)) n := by
    rw [h_biprod_id]
  have h2 : homologyMap ((biprod.fst : K ⊞ L ⟶ K) ≫ (biprod.inl : K ⟶ K ⊞ L) +
      (biprod.snd : K ⊞ L ⟶ L) ≫ (biprod.inr : L ⟶ K ⊞ L)) n =
      homologyMap ((biprod.fst : K ⊞ L ⟶ K) ≫ (biprod.inl : K ⟶ K ⊞ L)) n +
      homologyMap ((biprod.snd : K ⊞ L ⟶ L) ≫ (biprod.inr : L ⟶ K ⊞ L)) n :=
    HomologicalComplex.homologyMap_add _ _ _
  have h3 : homologyMap ((biprod.fst : K ⊞ L ⟶ K) ≫ (biprod.inl : K ⟶ K ⊞ L)) n =
      π₁ ≫ ι₁ := by
    rw [HomologicalComplex.homologyMap_comp]
  have h4 : homologyMap ((biprod.snd : K ⊞ L ⟶ L) ≫ (biprod.inr : L ⟶ K ⊞ L)) n =
      π₂ ≫ ι₂ := by
    rw [HomologicalComplex.homologyMap_comp]
  have h5 : homologyMap (𝟙 (K ⊞ L)) n = 𝟙 ((K ⊞ L).homology n) := by simp
  rw [h2, h3, h4, h5] at h1
  have h6 : π₁ ≫ ι₁ + π₂ ≫ ι₂ = 𝟙 ((K ⊞ L).homology n) := h1
  have h_term1 : π₁ ≫ ι₁ = 0 := by
    rw [hπ₁, hι₁] ; simp
  have h_term2 : π₂ ≫ ι₂ = 0 := by
    rw [hπ₂, hι₂] ; simp
  have h_id_zero : 𝟙 ((K ⊞ L).homology n) = 0 := by
    rw [←h6, h_term1, h_term2] ; simp
  let X := (K ⊞ L).homology n
  have h_id : 𝟙 X = 0 := h_id_zero
  have h_src : ∀ (Y : C) (f g : X ⟶ Y), f = g := by
    intro Y f g
    have hf : f = 𝟙 X ≫ f := by exact Eq.symm (Category.id_comp f)
    have hg : g = 𝟙 X ≫ g := by exact Eq.symm (Category.id_comp g)
    rw [hf, hg, h_id] ; simp
  have h_tgt : ∀ (Y : C) (f g : Y ⟶ X), f = g := by
    intro Y f g
    have hf : f = f ≫ 𝟙 X := by exact Eq.symm (Category.comp_id f)
    have hg : g = g ≫ 𝟙 X := by exact Eq.symm (Category.comp_id g)
    rw [hf, hg, h_id] ; simp
  exact ⟨fun Y => ⟨⟨⟨0⟩, fun f => h_src Y f 0⟩⟩, fun Y => ⟨⟨⟨0⟩, fun f => h_tgt Y f 0⟩⟩⟩

end BiprodHomology

section PullbackImpliesDegreewise

/-!
## Pullback square implies degreewise pullback

If the square of topological spaces is a pullback (i.e., UV = U ∩ V)
and jU, jV are embeddings, then the degreewise pullback assumption holds
for singular simplices.
-/

open CategoryTheory.Limits

variable (ts : TwoSubspaces.{w})

/-- Generalized factor lemma: if f is an embedding and range(σ) ⊆ range(f),
    then σ factors through the domain of f. -/
lemma factor_of_range_subset_general
    {A X : TopCat.{w}} (f : A ⟶ X) (h_emb : Topology.IsEmbedding f)
    {n : SimplexCategoryᵒᵖ} {σ : (TopCat.toSSet.obj X).obj n}
    (h : Set.range (TopCat.toSSetObjEquiv X n σ) ⊆ Set.range f) :
    ∃ (τ : (TopCat.toSSet.obj A).obj n), (TopCat.toSSet.map f).app n τ = σ := by
  let eX : (TopCat.toSSet.obj X).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), X) :=
    TopCat.toSSetObjEquiv X n
  let eA : (TopCat.toSSet.obj A).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), A) :=
    TopCat.toSSetObjEquiv A n
  let σ' : C(stdSimplex ℝ (Fin (n.unop.len + 1)), X) := eX σ
  have h' : Set.range σ' ⊆ Set.range f := h
  let e_homeo : A ≃ₜ (Set.range f : Set X) := h_emb.toHomeomorph
  let g : stdSimplex ℝ (Fin (n.unop.len + 1)) → (Set.range f : Set X) :=
    fun x => ⟨σ' x, h' (Set.mem_range_self x)⟩
  have hg_cont : Continuous g := σ'.continuous.subtype_mk _
  let τ_val : stdSimplex ℝ (Fin (n.unop.len + 1)) → A := e_homeo.symm ∘ g
  have hτ_cont : Continuous τ_val := (e_homeo.symm).continuous.comp hg_cont
  let τ' : C(stdSimplex ℝ (Fin (n.unop.len + 1)), A) := ⟨τ_val, hτ_cont⟩
  let τ : (TopCat.toSSet.obj A).obj n := eA.symm τ'
  refine ⟨τ, ?_⟩
  have h1 : ∀ (x : _), (TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n τ)) x = f (τ' x) := by
    intro x
    rfl
  have h_key : ∀ (y : Set.range f), f (e_homeo.symm y) = (y : X) := by
    intro y
    have h5 : e_homeo (e_homeo.symm y) = y := e_homeo.apply_symm_apply y
    have h_apply : ∀ (z : A), (e_homeo z : X) = f z := by
      intro z
      rfl
    have h6 : (e_homeo (e_homeo.symm y) : X) = f (e_homeo.symm y) := h_apply (e_homeo.symm y)
    have h7 : (e_homeo (e_homeo.symm y) : X) = (y : X) := by
      rw [h5]
    rw [←h6, h7]
  have h3 : TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n τ) =
            TopCat.toSSetObjEquiv X n σ := by
    apply ContinuousMap.ext
    intro x
    have h4 : (TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n τ)) x = f (τ' x) := h1 x
    rw [h4]
    dsimp only [τ', τ_val, g]
    have h7 : f (e_homeo.symm ⟨σ' x, h' (Set.mem_range_self x)⟩) = σ' x := by
      rw [h_key ⟨σ' x, h' (Set.mem_range_self x)⟩]
    exact h7
  exact eX.injective h3

/-- If jU is an embedding, then `toSSet.map jU` is injective on simplices. -/
lemma toSSet_map_injective_of_embedding
    {A X : TopCat.{w}} (f : A ⟶ X) (h_emb : Topology.IsEmbedding f)
    {n : SimplexCategoryᵒᵖ} :
    Function.Injective ((TopCat.toSSet.map f).app n) := by
  intro σ τ h
  apply (TopCat.toSSetObjEquiv A n).injective
  apply ContinuousMap.ext
  intro x
  have h1 : ∀ y, (TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n σ)) y =
              f ((TopCat.toSSetObjEquiv A n σ) y) := by
    intro y
    rfl
  have h2 : ∀ y, (TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n τ)) y =
              f ((TopCat.toSSetObjEquiv A n τ) y) := by
    intro y
    rfl
  have h3 : (TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n σ)) x =
            (TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n τ)) x := by
    rw [h]
  rw [h1 x, h2 x] at h3
  exact h_emb.injective h3

/-- Helper: if σ is in the image of f*, then range(σ) ⊆ range(f). -/
lemma range_of_factor_map
    {A X : TopCat.{w}} (f : A ⟶ X) {n : SimplexCategoryᵒᵖ}
    {σ : (TopCat.toSSet.obj X).obj n} {τ : (TopCat.toSSet.obj A).obj n}
    (h : (TopCat.toSSet.map f).app n τ = σ) :
    Set.range (TopCat.toSSetObjEquiv X n σ) ⊆ Set.range f := by
  have h1 : ∀ (x : _), (TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n τ)) x =
              f ((TopCat.toSSetObjEquiv A n τ) x) := by
    intro x; rfl
  have h2 : Set.range (TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n τ)) ⊆
            Set.range f := by
    have h3 : Set.range (TopCat.toSSetObjEquiv X n ((TopCat.toSSet.map f).app n τ)) =
              Set.range (f ∘ (TopCat.toSSetObjEquiv A n τ)) := by
      ext z
      simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨x, hx⟩; exact ⟨x, (h1 x).symm ▸ hx⟩
      · rintro ⟨x, hx⟩; exact ⟨x, (h1 x) ▸ hx⟩
    rw [h3, Set.range_comp]
    exact Set.image_subset_range f _
  rw [h] at h2
  exact h2

/-- If the square is a pullback in TopCat and jV is an embedding, then iU is an embedding. -/
lemma iU_isEmbedding_of_isPullback_of_embedding
    (h_pullback : IsPullback ts.iU ts.iV ts.jU ts.jV)
    (h_jV_emb : Topology.IsEmbedding ts.jV) :
    Topology.IsEmbedding ts.iU := by
  have h_can : IsPullback (Limits.pullback.fst ts.jU ts.jV)
      (Limits.pullback.snd ts.jU ts.jV) ts.jU ts.jV := by exact IsPullback.of_hasPullback ts.jU ts.jV
  let e : ts.UV ≅ Limits.pullback ts.jU ts.jV :=
    h_pullback.isoIsPullback ts.U ts.V h_can
  have h_eq1 : e.hom ≫ Limits.pullback.fst ts.jU ts.jV = ts.iU :=
    h_pullback.isoIsPullback_hom_fst ts.U ts.V h_can
  have h_fst_emb : Topology.IsEmbedding (Limits.pullback.fst ts.jU ts.jV) :=
    TopCat.fst_isEmbedding_of_right ts.jU (show Topology.IsEmbedding (↑ts.jV) from h_jV_emb)
  have h_e_emb : Topology.IsEmbedding e.hom :=
    (TopCat.homeoOfIso e).isEmbedding
  have h : Topology.IsEmbedding (e.hom ≫ Limits.pullback.fst ts.jU ts.jV) :=
    h_fst_emb.comp h_e_emb
  rwa [h_eq1] at h

/-- If the square is a pullback in TopCat and jU, jV are embeddings,
    then DegreewisePullbackAssumption holds. -/
theorem degreewisePullback_of_isPullback_of_embeddings
    (h_pullback : IsPullback ts.iU ts.iV ts.jU ts.jV)
    (h_jU_emb : Topology.IsEmbedding ts.jU)
    (h_jV_emb : Topology.IsEmbedding ts.jV) :
    DegreewisePullbackAssumption ts := by
  intro n x y h_eq
  let n_op : SimplexCategoryᵒᵖ := Opposite.op (SimplexCategory.mk n)
  -- Step 1: From equality of small simplices, get jU*(x) = jV*(y) in X
  have h1 : (TopCat.toSSet.map ts.jU).app n_op x = (TopCat.toSSet.map ts.jV).app n_op y := by
    have h2 : (smallFromU ts).app n_op x = (smallFromV ts).app n_op y := h_eq
    have h3 : (smallι ts).app n_op ((smallFromU ts).app n_op x) =
              (smallι ts).app n_op ((smallFromV ts).app n_op y) := by rw [h2]
    have h_natU : (smallFromU ts).app n_op ≫ (smallι ts).app n_op = (TopCat.toSSet.map ts.jU).app n_op :=
      NatTrans.congr_app (smallFromU_comp_ι ts) n_op
    have h_natV : (smallFromV ts).app n_op ≫ (smallι ts).app n_op = (TopCat.toSSet.map ts.jV).app n_op :=
      NatTrans.congr_app (smallFromV_comp_ι ts) n_op
    have h4 : (smallι ts).app n_op ((smallFromU ts).app n_op x) = (TopCat.toSSet.map ts.jU).app n_op x := by
      have h41 : ((smallFromU ts).app n_op ≫ (smallι ts).app n_op) x = (TopCat.toSSet.map ts.jU).app n_op x := by
        rw [h_natU]
      simpa [Category.assoc] using h41
    have h5 : (smallι ts).app n_op ((smallFromV ts).app n_op y) = (TopCat.toSSet.map ts.jV).app n_op y := by
      have h51 : ((smallFromV ts).app n_op ≫ (smallι ts).app n_op) y = (TopCat.toSSet.map ts.jV).app n_op y := by
        rw [h_natV]
      simpa [Category.assoc] using h51
    rw [h4, h5] at h3
    exact h3
  -- Step 2: The common simplex σ := jU*(x) = jV*(y) has range in both U and V
  let σ : (TopCat.toSSet.obj ts.X).obj n_op := (TopCat.toSSet.map ts.jU).app n_op x
  have hσU : Set.range (TopCat.toSSetObjEquiv ts.X n_op σ) ⊆ Set.range ts.jU :=
    range_of_factor_map ts.jU rfl
  have hσV : Set.range (TopCat.toSSetObjEquiv ts.X n_op σ) ⊆ Set.range ts.jV :=
    range_of_factor_map ts.jV (τ := y) h1.symm
  -- Step 3: iU is an embedding (pullback of an embedding)
  have h_iU_emb : Topology.IsEmbedding ts.iU :=
    iU_isEmbedding_of_isPullback_of_embedding ts h_pullback h_jV_emb
  have h_comp_emb : Topology.IsEmbedding (ts.iU ≫ ts.jU) :=
    h_jU_emb.comp h_iU_emb
  -- Step 4: Point-level pullback existence: given u ∈ U, v ∈ V with jU(u) = jV(v),
  -- there exists z ∈ UV with iU(z) = u and iV(z) = v.
  have h_point_lift : ∀ (u : ts.U) (v : ts.V), ts.jU u = ts.jV v →
      ∃ (z : ts.UV), ts.iU z = u ∧ ts.iV z = v := by
    intro u v huv
    let pt : TopCat.{w} := TopCat.of PUnit
    let f_u : pt ⟶ ts.U := TopCat.const u
    let f_v : pt ⟶ ts.V := TopCat.const v
    have h_comm : f_u ≫ ts.jU = f_v ≫ ts.jV := by
      ext ⟨⟩
      exact huv
    let f_z : pt ⟶ ts.UV := h_pullback.lift f_u f_v h_comm
    have hz1 : f_z ≫ ts.iU = f_u := h_pullback.lift_fst f_u f_v h_comm
    have hz2 : f_z ≫ ts.iV = f_v := h_pullback.lift_snd f_u f_v h_comm
    let z : ts.UV := f_z PUnit.unit
    have h_f_u_eq : f_u PUnit.unit = u := by simp [f_u, TopCat.const_apply]
    have h_f_v_eq : f_v PUnit.unit = v := by simp [f_v, TopCat.const_apply]
    have h41 : (f_z ≫ ts.iU) PUnit.unit = f_u PUnit.unit := by rw [hz1]
    have h42 : (f_z ≫ ts.iV) PUnit.unit = f_v PUnit.unit := by rw [hz2]
    have h_iU_z : ts.iU z = u := by
      simpa [z, h_f_u_eq] using h41
    have h_iV_z : ts.iV z = v := by
      simpa [z, h_f_v_eq] using h42
    exact ⟨z, h_iU_z, h_iV_z⟩
  -- Step 5: range(jU) ∩ range(jV) = range(jU ∘ iU)
  have h_inter_eq : Set.range ts.jU ∩ Set.range ts.jV = Set.range (ts.iU ≫ ts.jU) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_range]
    constructor
    · rintro ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
      have h_eq2 : ts.jU u = ts.jV v := hv.symm
      have h_exists : ∃ (z : ts.UV), ts.iU z = u ∧ ts.iV z = v := h_point_lift u v h_eq2
      rcases h_exists with ⟨z, hz1, hz2⟩
      refine ⟨z, ?_⟩
      have h : (ts.iU ≫ ts.jU) z = ts.jU u := by
        simpa using congr_arg ts.jU hz1
      exact h
    · rintro ⟨z, rfl⟩
      constructor
      · exact ⟨ts.iU z, rfl⟩
      · have h : ts.jU (ts.iU z) = ts.jV (ts.iV z) := by
          have h' : (ts.iU ≫ ts.jU) z = (ts.iV ≫ ts.jV) z := by
            rw [ts.comm]
          exact h'
        exact ⟨ts.iV z, h.symm⟩
  -- Step 6: range(σ) ⊆ range(jU ∘ iU)
  have h5 : Set.range (TopCat.toSSetObjEquiv ts.X n_op σ) ⊆ Set.range (ts.iU ≫ ts.jU) := by
    have h6 : Set.range (TopCat.toSSetObjEquiv ts.X n_op σ) ⊆
              Set.range ts.jU ∩ Set.range ts.jV :=
      Set.subset_inter hσU hσV
    rw [h_inter_eq] at h6
    exact h6
  -- Step 7: σ factors through UV via the embedding jU ∘ iU
  have h_lift : ∃ (z : (TopCat.toSSet.obj ts.UV).obj n_op),
      (TopCat.toSSet.map (ts.iU ≫ ts.jU)).app n_op z = σ :=
    factor_of_range_subset_general (ts.iU ≫ ts.jU) h_comp_emb h5
  rcases h_lift with ⟨z, hz⟩
  -- Step 8: iU*(z) = x and iV*(z) = y by injectivity of jU* and jV*
  have h_map_comp1 : (TopCat.toSSet.map (ts.iU ≫ ts.jU)).app n_op z =
      (TopCat.toSSet.map ts.jU).app n_op ((TopCat.toSSet.map ts.iU).app n_op z) := by
    have hmc : TopCat.toSSet.map (ts.iU ≫ ts.jU) =
        TopCat.toSSet.map ts.iU ≫ TopCat.toSSet.map ts.jU := by
      rw [Functor.map_comp]
    rw [hmc]
    rfl
  have h_iU_eq : (TopCat.toSSet.map ts.jU).app n_op ((TopCat.toSSet.map ts.iU).app n_op z) =
                  (TopCat.toSSet.map ts.jU).app n_op x := by
    rw [←h_map_comp1, hz]
  have h_iU_final : (TopCat.toSSet.map ts.iU).app n_op z = x :=
    toSSet_map_injective_of_embedding ts.jU h_jU_emb h_iU_eq
  have h_map_comp2 : (TopCat.toSSet.map (ts.iV ≫ ts.jV)).app n_op z =
      (TopCat.toSSet.map ts.jV).app n_op ((TopCat.toSSet.map ts.iV).app n_op z) := by
    have hmc : TopCat.toSSet.map (ts.iV ≫ ts.jV) =
        TopCat.toSSet.map ts.iV ≫ TopCat.toSSet.map ts.jV := by
      rw [Functor.map_comp]
    rw [hmc]
    rfl
  have h_comm2 : ts.iV ≫ ts.jV = ts.iU ≫ ts.jU := ts.comm.symm
  have h_iV_eq1 : (TopCat.toSSet.map ts.jV).app n_op ((TopCat.toSSet.map ts.iV).app n_op z) =
                   (TopCat.toSSet.map ts.jV).app n_op y := by
    rw [←h_map_comp2, h_comm2, hz]
    ; simpa using h1
  have h_iV_final : (TopCat.toSSet.map ts.iV).app n_op z = y :=
    toSSet_map_injective_of_embedding ts.jV h_jV_emb h_iV_eq1
  exact ⟨z, h_iU_final, h_iV_final⟩

end PullbackImpliesDegreewise

section BoundaryIso

/-!
## The Mayer-Vietoris boundary isomorphism

From the Mayer-Vietoris long exact sequence, when U and V have trivial homology in
degrees n and n+1, the connecting homomorphism gives an isomorphism:
  H_{n+1}(X) ≅ H_n(U ∩ V)

This follows from the long exact sequence in homology associated to the
short exact sequence of chain complexes:
  0 → C(U∩V) → C(U) ⊕ C(V) → C_small(X) → 0

When H_{n+1}(U) ⊕ H_{n+1}(V) = 0 and H_n(U) ⊕ H_n(V) = 0,
the connecting homomorphism δ : H_{n+1}(small) → H_n(U∩V) is an isomorphism.
-/

