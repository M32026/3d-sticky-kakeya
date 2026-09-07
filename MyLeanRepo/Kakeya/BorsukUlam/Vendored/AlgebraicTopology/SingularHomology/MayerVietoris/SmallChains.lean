module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.RelativeHomology

@[expose] public section

/-!
# Small Singular Chains

Given a space X and two subspaces U, V, we define the subcomplex
of "small" singular chains — those whose simplices are entirely contained
in U or entirely in V.

This is the first step toward the Mayer-Vietoris sequence.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial

universe w v u

namespace AlgebraicTopology

section TwoSubspaces

/-!
## Setup: two subspaces of X
-/

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
variable (R : C)

/-- Data for two subspaces of a space (not necessarily open). -/
structure TwoSubspaces where
  /-- The total space. -/
  X : TopCat.{w}
  /-- The first subspace. -/
  U : TopCat.{w}
  /-- The second subspace. -/
  V : TopCat.{w}
  /-- The intersection U ∩ V. -/
  UV : TopCat.{w}
  /-- Inclusion of U into X. -/
  jU : U ⟶ X
  /-- Inclusion of V into X. -/
  jV : V ⟶ X
  /-- Inclusion of UV into U. -/
  iU : UV ⟶ U
  /-- Inclusion of UV into V. -/
  iV : UV ⟶ V
  /-- The square commutes: iU ≫ jU = iV ≫ jV. -/
  comm : iU ≫ jU = iV ≫ jV

variable (ts : TwoSubspaces.{w})

/-!
### Small simplices
-/

/-- A singular simplex is "small" if it factors through U or through V. -/
def isSmallSimplex {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj ts.X).obj n) : Prop :=
  (∃ (τ : (TopCat.toSSet.obj ts.U).obj n), (TopCat.toSSet.map ts.jU).app n τ = σ) ∨
  (∃ (τ : (TopCat.toSSet.obj ts.V).obj n), (TopCat.toSSet.map ts.jV).app n τ = σ)

/-- The subcomplex of small singular simplices. -/
noncomputable def smallSubcomplex : (TopCat.toSSet.obj ts.X).Subcomplex where
  obj n := {σ | isSmallSimplex ts σ}
  map {m n} f σ h := by
    dsimp only [isSmallSimplex] at h ⊢
    rcases h with (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
    · left
      refine ⟨(TopCat.toSSet.obj ts.U).map f τ, ?_⟩
      have hnat : (TopCat.toSSet.obj ts.U).map f ≫ (TopCat.toSSet.map ts.jU).app n =
          (TopCat.toSSet.map ts.jU).app m ≫ (TopCat.toSSet.obj ts.X).map f :=
        (TopCat.toSSet.map ts.jU).naturality f
      have h : ((TopCat.toSSet.obj ts.U).map f ≫ (TopCat.toSSet.map ts.jU).app n) τ =
          ((TopCat.toSSet.map ts.jU).app m ≫ (TopCat.toSSet.obj ts.X).map f) τ := by
        rw [hnat]
      exact h
    · right
      refine ⟨(TopCat.toSSet.obj ts.V).map f τ, ?_⟩
      have hnat : (TopCat.toSSet.obj ts.V).map f ≫ (TopCat.toSSet.map ts.jV).app n =
          (TopCat.toSSet.map ts.jV).app m ≫ (TopCat.toSSet.obj ts.X).map f :=
        (TopCat.toSSet.map ts.jV).naturality f
      have h : ((TopCat.toSSet.obj ts.V).map f ≫ (TopCat.toSSet.map ts.jV).app n) τ =
          ((TopCat.toSSet.map ts.jV).app m ≫ (TopCat.toSSet.obj ts.X).map f) τ := by
        rw [hnat]
      exact h

/-- The small simplicial set (of small simplices). -/
def smallSSet : SSet.{w} := (smallSubcomplex ts).toSSet

/-- The inclusion of the small simplicial set into the full one. -/
def smallι : smallSSet ts ⟶ TopCat.toSSet.obj ts.X :=
  (smallSubcomplex ts).ι

/-!
### Small chain complex
-/

/-- The small singular chain complex C_small(X). -/
noncomputable def smallChainComplex : ChainComplex C ℕ :=
  ((SSet.chainComplexFunctor C).obj R).obj (smallSSet ts)

/-- The inclusion map C_small(X) → C(X) on chain complexes. -/
noncomputable def smallChainInclusion :
    smallChainComplex C R ts ⟶ singularChainComplex' C R ts.X :=
  ((SSet.chainComplexFunctor C).obj R).map (smallι ts)

/-!
### Maps from C(U) and C(V) to C_small(X)
-/

/-- The map from singular simplices of U to small simplices of X. -/
def smallFromU : TopCat.toSSet.obj ts.U ⟶ smallSSet ts where
  app n := TypeCat.ofHom fun τ =>
    (⟨(TopCat.toSSet.map ts.jU).app n τ, Or.inl ⟨τ, rfl⟩⟩ : (smallSSet ts).obj n)
  naturality m n f := by
    have hnat : (TopCat.toSSet.obj ts.U).map f ≫ (TopCat.toSSet.map ts.jU).app n =
        (TopCat.toSSet.map ts.jU).app m ≫ (TopCat.toSSet.obj ts.X).map f :=
      (TopCat.toSSet.map ts.jU).naturality f
    ext x
    apply Subtype.ext
    dsimp only
    have h : ((TopCat.toSSet.obj ts.U).map f ≫ (TopCat.toSSet.map ts.jU).app n) x =
        ((TopCat.toSSet.map ts.jU).app m ≫ (TopCat.toSSet.obj ts.X).map f) x := by
      rw [hnat]
    exact h

/-- The map from singular simplices of V to small simplices of X. -/
def smallFromV : TopCat.toSSet.obj ts.V ⟶ smallSSet ts where
  app n := TypeCat.ofHom fun τ =>
    (⟨(TopCat.toSSet.map ts.jV).app n τ, Or.inr ⟨τ, rfl⟩⟩ : (smallSSet ts).obj n)
  naturality m n f := by
    have hnat : (TopCat.toSSet.obj ts.V).map f ≫ (TopCat.toSSet.map ts.jV).app n =
        (TopCat.toSSet.map ts.jV).app m ≫ (TopCat.toSSet.obj ts.X).map f :=
      (TopCat.toSSet.map ts.jV).naturality f
    ext x
    apply Subtype.ext
    dsimp only
    have h : ((TopCat.toSSet.obj ts.V).map f ≫ (TopCat.toSSet.map ts.jV).app n) x =
        ((TopCat.toSSet.map ts.jV).app m ≫ (TopCat.toSSet.obj ts.X).map f) x := by
      rw [hnat]
    exact h

/-- The chain map C(U) → C_small(X). -/
noncomputable def smallChainFromU :
    singularChainComplex' C R ts.U ⟶ smallChainComplex C R ts :=
  ((SSet.chainComplexFunctor C).obj R).map (smallFromU ts)

/-- The chain map C(V) → C_small(X). -/
noncomputable def smallChainFromV :
    singularChainComplex' C R ts.V ⟶ smallChainComplex C R ts :=
  ((SSet.chainComplexFunctor C).obj R).map (smallFromV ts)

/-- smallFromU ≫ smallι = jU* at the SSet level. -/
lemma smallFromU_comp_ι : smallFromU ts ≫ smallι ts = TopCat.toSSet.map ts.jU := by
  ext n τ
  ; rfl

/-- smallFromV ≫ smallι = jV* at the SSet level. -/
lemma smallFromV_comp_ι : smallFromV ts ≫ smallι ts = TopCat.toSSet.map ts.jV := by
  ext n τ
  ; rfl

/-!
### The Mayer-Vietoris short exact sequence

  0 → C(U ∩ V) → C(U) ⊕ C(V) → C_small(X) → 0
-/

end TwoSubspaces

section MayerVietorisShortComplex

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable (R : C) (ts : TwoSubspaces.{w})
variable [HasBinaryBiproducts (ChainComplex C ℕ)]

/-- The map f : C(U ∩ V) → C(U) ⊕ C(V) given by c ↦ (iU* c, -iV* c). -/
noncomputable def mvMapF :
    singularChainComplex' C R ts.UV ⟶
    (singularChainComplex' C R ts.U) ⊞ (singularChainComplex' C R ts.V) :=
  ((singularChainComplexFunctor C).obj R).map ts.iU ≫ biprod.inl -
  ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr

/-- The map g : C(U) ⊕ C(V) → C_small(X) given by (c₁, c₂) ↦ jU* c₁ + jV* c₂. -/
noncomputable def mvMapG :
    (singularChainComplex' C R ts.U) ⊞ (singularChainComplex' C R ts.V) ⟶
    smallChainComplex C R ts :=
  biprod.desc (smallChainFromU C R ts) (smallChainFromV C R ts)

/-- The composition `mvMapF ≫ mvMapG` is zero. -/
theorem mvMapF_comp_mvMapG : mvMapF C R ts ≫ mvMapG C R ts = 0 := by
  have h1 : biprod.inl ≫ mvMapG C R ts = smallChainFromU C R ts :=
    biprod.inl_desc _ _
  have h2 : biprod.inr ≫ mvMapG C R ts = smallChainFromV C R ts :=
    biprod.inr_desc _ _
  have h3 : TopCat.toSSet.map ts.iU ≫ smallFromU ts =
             TopCat.toSSet.map ts.iV ≫ smallFromV ts := by
    have h1' : (TopCat.toSSet.map ts.iU ≫ smallFromU ts) ≫ smallι ts =
                TopCat.toSSet.map (ts.iU ≫ ts.jU) := by
      calc
        (TopCat.toSSet.map ts.iU ≫ smallFromU ts) ≫ smallι ts
          = TopCat.toSSet.map ts.iU ≫ (smallFromU ts ≫ smallι ts) := by
            rw [Category.assoc]
        _ = TopCat.toSSet.map ts.iU ≫ TopCat.toSSet.map ts.jU := by
            rw [smallFromU_comp_ι]
        _ = TopCat.toSSet.map (ts.iU ≫ ts.jU) := by
            rw [← Functor.map_comp]
    have h2' : (TopCat.toSSet.map ts.iV ≫ smallFromV ts) ≫ smallι ts =
                TopCat.toSSet.map (ts.iV ≫ ts.jV) := by
      calc
        (TopCat.toSSet.map ts.iV ≫ smallFromV ts) ≫ smallι ts
          = TopCat.toSSet.map ts.iV ≫ (smallFromV ts ≫ smallι ts) := by
            rw [Category.assoc]
        _ = TopCat.toSSet.map ts.iV ≫ TopCat.toSSet.map ts.jV := by
            rw [smallFromV_comp_ι]
        _ = TopCat.toSSet.map (ts.iV ≫ ts.jV) := by
            rw [← Functor.map_comp]
    have h_eq : (TopCat.toSSet.map ts.iU ≫ smallFromU ts) ≫ smallι ts =
                (TopCat.toSSet.map ts.iV ≫ smallFromV ts) ≫ smallι ts := by
      rw [h1', h2', ts.comm]
    have h_mono : Mono (smallι ts) := by
      letI : Mono (smallSubcomplex ts).ι := by exact inferInstance
      exact this
    exact h_mono.right_cancellation _ _ h_eq
  let F : SSet.{w} ⥤ ChainComplex C ℕ := (SSet.chainComplexFunctor C).obj R
  have h41 : ((singularChainComplexFunctor C).obj R).map ts.iU = F.map (TopCat.toSSet.map ts.iU) := by rfl
  have h42 : ((singularChainComplexFunctor C).obj R).map ts.iV = F.map (TopCat.toSSet.map ts.iV) := by rfl
  have h43 : smallChainFromU C R ts = F.map (smallFromU ts) := by rfl
  have h44 : smallChainFromV C R ts = F.map (smallFromV ts) := by rfl
  have h4 : ((singularChainComplexFunctor C).obj R).map ts.iU ≫ smallChainFromU C R ts =
             ((singularChainComplexFunctor C).obj R).map ts.iV ≫ smallChainFromV C R ts := by
    rw [h41, h42, h43, h44]
    have h_comp1 : F.map (TopCat.toSSet.map ts.iU) ≫ F.map (smallFromU ts) =
                     F.map (TopCat.toSSet.map ts.iU ≫ smallFromU ts) := by exact Eq.symm (F.map_comp (TopCat.toSSet.map ts.iU) (smallFromU ts))
    have h_comp2 : F.map (TopCat.toSSet.map ts.iV) ≫ F.map (smallFromV ts) =
                     F.map (TopCat.toSSet.map ts.iV ≫ smallFromV ts) := by exact Eq.symm (F.map_comp (TopCat.toSSet.map ts.iV) (smallFromV ts))
    have h_goal : F.map (TopCat.toSSet.map ts.iU ≫ smallFromU ts) =
                  F.map (TopCat.toSSet.map ts.iV ≫ smallFromV ts) := by rw [h3]
    calc
      F.map (TopCat.toSSet.map ts.iU) ≫ F.map (smallFromU ts)
        = F.map (TopCat.toSSet.map ts.iU ≫ smallFromU ts) := h_comp1
      _ = F.map (TopCat.toSSet.map ts.iV ≫ smallFromV ts) := h_goal
      _ = F.map (TopCat.toSSet.map ts.iV) ≫ F.map (smallFromV ts) := h_comp2.symm
  have h5 : ((singularChainComplexFunctor C).obj R).map ts.iU ≫ biprod.inl ≫ mvMapG C R ts =
             ((singularChainComplexFunctor C).obj R).map ts.iU ≫ smallChainFromU C R ts := by
    rw [h1]
  have h6 : ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr ≫ mvMapG C R ts =
             ((singularChainComplexFunctor C).obj R).map ts.iV ≫ smallChainFromV C R ts := by
    rw [h2]
  have h_eq : ((singularChainComplexFunctor C).obj R).map ts.iU ≫ biprod.inl ≫ mvMapG C R ts =
                ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr ≫ mvMapG C R ts := by
    rw [h5, h6, h4]
  have h_sub : ∀ (x y : singularChainComplex' C R ts.UV ⟶
      (singularChainComplex' C R ts.U) ⊞ (singularChainComplex' C R ts.V)),
      (x - y) ≫ mvMapG C R ts = (x ≫ mvMapG C R ts) - (y ≫ mvMapG C R ts) := by
    intro x y
    have h : (x + (-y)) ≫ mvMapG C R ts = x ≫ mvMapG C R ts + (-y) ≫ mvMapG C R ts := by
      exact Preadditive.add_comp (singularChainComplex' C R ts.UV) (singularChainComplex' C R ts.U ⊞ singularChainComplex' C R ts.V) (smallChainComplex C R ts) x (-y) (mvMapG C R ts)
    simp [sub_eq_add_neg]
  have h9 := h_sub (mvMapF C R ts + ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr)
                (((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr)
  have h10 : mvMapF C R ts + (((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr) -
               (((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr) = mvMapF C R ts := by
    abel
  have h11 : (mvMapF C R ts + ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr -
                ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr) ≫
              mvMapG C R ts =
            (mvMapF C R ts) ≫ mvMapG C R ts := by
    rw [h10]
  have h12 : mvMapF C R ts ≫ mvMapG C R ts =
      ((mvMapF C R ts + ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr) ≫ mvMapG C R ts) -
      ((((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr) ≫ mvMapG C R ts) := by
    rw [← h11, h9]
  rw [h12]
  have h13 : (mvMapF C R ts + ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr) ≫ mvMapG C R ts =
             (((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr) ≫ mvMapG C R ts := by
    have h14 : mvMapF C R ts + ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr =
               ((singularChainComplexFunctor C).obj R).map ts.iU ≫ biprod.inl := by
      dsimp only [mvMapF]
      ; abel
    rw [h14]
    have h_assoc : (((singularChainComplexFunctor C).obj R).map ts.iU ≫ biprod.inl) ≫ mvMapG C R ts =
                   ((singularChainComplexFunctor C).obj R).map ts.iU ≫ biprod.inl ≫ mvMapG C R ts := by
      rw [Category.assoc]
    have h_assoc2 : (((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr) ≫ mvMapG C R ts =
                    ((singularChainComplexFunctor C).obj R).map ts.iV ≫ biprod.inr ≫ mvMapG C R ts := by
      rw [Category.assoc]
    rw [h_assoc, h_assoc2]
    exact h_eq
  rw [h13]
  ; simp

/-- The Mayer-Vietoris short complex: 0 → C(U∩V) → C(U)⊕C(V) → C_small(X) → 0 -/
noncomputable def mvShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (mvMapF C R ts) (mvMapG C R ts) (mvMapF_comp_mvMapG C R ts)

end MayerVietorisShortComplex

end AlgebraicTopology
