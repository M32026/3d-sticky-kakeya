module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

@[expose] public section

/-!
# Relative Singular Homology

Relative singular homology `Hₙ(X, A)` for a pair `(X, A)`.

Given a topological pair (X, A), i.e., a space X and a subspace A ⊆ X,
the relative singular homology Hₙ(X, A) is the homology of the quotient
chain complex Cₙ(X) / Cₙ(A).

The inclusion i : A → X induces a map iₙ : Cₙ(A) → Cₙ(X), and we have a
short exact sequence of chain complexes:
  0 → Cₙ(A) → Cₙ(X) → Cₙ(X, A) → 0

From the snake lemma, this induces a long exact sequence in homology.

## Definitions

* `TopologicalPair` — a pair (X, A) with an inclusion A → X
* `relativeSingularChainComplex C R p` — the relative chain complex C(X,A)
* `relativeSingularHomology C R p n` — the relative homology Hₙ(X,A)
* `inclusionHomologyMap C R p n` — Hₙ(A) → Hₙ(X)
* `quotientHomologyMap C R p n` — Hₙ(X) → Hₙ(X,A)
* `connectingHomomorphism C R p n` — ∂ : Hₙ₊₁(X,A) → Hₙ(A)

## Results

* `pairLES_exact_at_A` — exactness at Hₙ(A)
* `pairLES_exact_at_X` — exactness at Hₙ(X)
* `pairLES_exact_at_relative` — exactness at Hₙ(X,A)
* `pairLES_δIso` — when Hₙ(X) = Hₙ₋₁(X) = 0, ∂ is an isomorphism
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex

universe w v u

namespace AlgebraicTopology

/-- A pair of topological spaces (X, A) with an inclusion A → X. -/
structure TopologicalPair where
  /-- The total space. -/
  X : TopCat.{w}
  /-- The subspace. -/
  A : TopCat.{w}
  /-- The inclusion map. -/
  i : A ⟶ X
  [mono_i : Mono i]

attribute [instance] TopologicalPair.mono_i

/-- The singular chain complex of a space, for convenient reference. -/
abbrev singularChainComplex' (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
    [Preadditive C] (R : C) (X : TopCat.{w}) : ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj X

/-- The singular homology of a space, for convenient reference. -/
abbrev singularHomology' (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
    [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ) (X : TopCat.{w}) : C :=
  ((singularHomologyFunctor C n).obj R).obj X

section Preadditive

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
variable (R : C)

/-- The map on singular chain complexes induced by the inclusion A → X. -/
noncomputable def TopologicalPair.inclusionChainMap (p : TopologicalPair.{w}) :
    singularChainComplex' C R p.A ⟶ singularChainComplex' C R p.X :=
  ((singularChainComplexFunctor C).obj R).map p.i

/-- The inclusion map on singular chains is a monomorphism. -/
lemma topologicalPair_inclusionChainMap_mono (p : TopologicalPair.{w})
    [Limits.HasPullbacks C] : Mono (p.inclusionChainMap C R) := by
  let F : TopCat.{w} ⥤ ChainComplex C ℕ := (singularChainComplexFunctor C).obj R
  have hM : F.PreservesMonomorphisms := by
    exact instPreservesMonomorphismsTopCatChainComplexNatObjFunctorSingularChainComplexFunctorOfHasPullbacks C
  exact hM.preserves p.i

end Preadditive

section Abelian

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable (R : C) [CategoryWithHomology C]
variable (p : TopologicalPair.{w}) [Limits.HasPullbacks C]

omit [HasCoproducts C] [CategoryWithHomology C] [Limits.HasPullbacks C] in
/-- For composable monomorphisms `X ⟶ Y ⟶ Z`, the induced sequence
`coker f ⟶ coker (f ≫ g) ⟶ coker g` is short exact. -/
theorem shortExactCokernelOfComposableMono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono f] [Mono g] :
    let S := ShortComplex.mk
      (cokernel.map f (f ≫ g) (𝟙 X) g (by simp))
      (cokernel.map (f ≫ g) g f (𝟙 Z) (by simp))
      (by
        let K := kernelCokernelCompSequence f g
        have hK : K.Exact := kernelCokernelCompSequence_exact f g
        exact hK.toIsComplex.zero' 3 4 5 (by norm_num) (by norm_num) (by norm_num))
    S.ShortExact := by
  dsimp only
  let K := kernelCokernelCompSequence f g
  have hK : K.Exact := kernelCokernelCompSequence_exact f g
  have h_exact_middle : (ShortComplex.mk
      (cokernel.map f (f ≫ g) (𝟙 X) g (by simp))
      (cokernel.map (f ≫ g) g f (𝟙 Z) (by simp))
      (hK.toIsComplex.zero' 3 4 5 (by norm_num) (by norm_num) (by norm_num))).Exact :=
    hK.exact' 3 4 5 (by norm_num) (by norm_num) (by norm_num)
  have h_mono : Mono (cokernel.map f (f ≫ g) (𝟙 X) g (by simp)) := by
    have h_zero_kernel : IsZero (kernel g) := by
      exact isZero_kernel_of_mono g
    have h_exact_prev : (ShortComplex.mk
        (K.map' 2 3 (by norm_num) (by norm_num))
        (K.map' 3 4 (by norm_num) (by norm_num))
        (hK.toIsComplex.zero' 2 3 4 (by norm_num) (by norm_num) (by norm_num))).Exact :=
      hK.exact' 2 3 4 (by norm_num) (by norm_num) (by norm_num)
    exact h_exact_prev.mono_g (IsZero.eq_zero_of_src h_zero_kernel _)
  have h_epi : Epi (cokernel.map (f ≫ g) g f (𝟙 Z) (by simp)) := by
    exact cokernel.desc_epi (f ≫ g) (𝟙 Z ≫ cokernel.π g) (by simp)
  exact ShortComplex.ShortExact.mk' h_exact_middle h_mono h_epi

/-- The relative singular chain complex C(X, A) = C(X) / C(A). -/
noncomputable def relativeSingularChainComplex : ChainComplex C ℕ :=
  (ShortComplex.cokernelSequence (p.inclusionChainMap C R)).X₃

/-- The short exact sequence 0 → C(A) → C(X) → C(X,A) → 0
of singular chain complexes, as a `ShortComplex`. -/
noncomputable def pairChainComplexSES : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.cokernelSequence (p.inclusionChainMap C R)

omit [CategoryWithHomology C] in
/-- The short exact sequence of chain complexes is indeed short exact. -/
theorem pairChainComplexSES_shortExact : (pairChainComplexSES C R p).ShortExact := by
  have hMono : Mono (pairChainComplexSES C R p).f := by
    dsimp only [pairChainComplexSES, ShortComplex.cokernelSequence]
    exact topologicalPair_inclusionChainMap_mono C R p
  have hExact : (pairChainComplexSES C R p).Exact :=
    ShortComplex.exact_cokernel (p.inclusionChainMap C R)
  have hEpi : Epi (pairChainComplexSES C R p).g := by
    dsimp only [pairChainComplexSES]
    infer_instance
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- The n-th relative singular homology group Hₙ(X, A). -/
noncomputable def relativeSingularHomology (n : ℕ) : C :=
  (relativeSingularChainComplex C R p).homology n

/-- The map Hₙ(A) → Hₙ(X) induced by the inclusion. -/
noncomputable def inclusionHomologyMap (n : ℕ) :
    singularHomology' C R n p.A ⟶ singularHomology' C R n p.X :=
  homologyMap (p.inclusionChainMap C R) n

/-- The map Hₙ(X) → Hₙ(X, A) induced by the quotient map. -/
noncomputable def quotientHomologyMap (n : ℕ) :
    singularHomology' C R n p.X ⟶ relativeSingularHomology C R p n :=
  homologyMap (pairChainComplexSES C R p).g n

/-- The connecting homomorphism ∂ : Hₙ₊₁(X, A) → Hₙ(A). -/
noncomputable def connectingHomomorphism (n : ℕ) :
    relativeSingularHomology C R p (n + 1) ⟶ singularHomology' C R n p.A :=
  ShortComplex.ShortExact.δ
    (pairChainComplexSES_shortExact C R p) (n + 1) n
    (by simp [ComplexShape.down_Rel])

/-- Exactness at Hₙ(A): im(∂) = ker(iₙ*). -/
theorem pairLES_exact_at_A (n : ℕ) :
    (ShortComplex.mk (connectingHomomorphism C R p n)
      (inclusionHomologyMap C R p n)
      (show connectingHomomorphism C R p n ≫ inclusionHomologyMap C R p n = 0 from by
        dsimp only [inclusionHomologyMap, connectingHomomorphism]
        exact ShortComplex.ShortExact.δ_comp
          (pairChainComplexSES_shortExact C R p) (n + 1) n
          (by simp [ComplexShape.down_Rel]))).Exact :=
  ShortComplex.ShortExact.homology_exact₁
    (pairChainComplexSES_shortExact C R p) (n + 1) n
    (by simp [ComplexShape.down_Rel])

/-- Exactness at Hₙ(X): im(iₙ*) = ker(πₙ*). -/
theorem pairLES_exact_at_X (n : ℕ) :
    (ShortComplex.mk (inclusionHomologyMap C R p n)
      (quotientHomologyMap C R p n)
      (show inclusionHomologyMap C R p n ≫ quotientHomologyMap C R p n = 0 from by
        dsimp only [inclusionHomologyMap, quotientHomologyMap]
        have h0 : (pairChainComplexSES C R p).f ≫
            (pairChainComplexSES C R p).g = 0 :=
          (pairChainComplexSES C R p).zero
        have h1 : homologyMap ((pairChainComplexSES C R p).f ≫
            (pairChainComplexSES C R p).g) n =
            homologyMap (pairChainComplexSES C R p).f n ≫
            homologyMap (pairChainComplexSES C R p).g n :=
          homologyMap_comp (φ := (pairChainComplexSES C R p).f)
            (ψ := (pairChainComplexSES C R p).g) (i := n)
        rw [h0, homologyMap_zero] at h1
        exact h1.symm)).Exact :=
  ShortComplex.ShortExact.homology_exact₂
    (pairChainComplexSES_shortExact C R p) n

/-- Exactness at Hₙ₊₁(X,A): im(πₙ₊₁*) = ker(∂). -/
theorem pairLES_exact_at_relative (n : ℕ) :
    (ShortComplex.mk (quotientHomologyMap C R p (n + 1))
      (connectingHomomorphism C R p n)
      (show quotientHomologyMap C R p (n + 1) ≫
          connectingHomomorphism C R p n = 0 from by
        dsimp only [quotientHomologyMap, connectingHomomorphism]
        exact ShortComplex.ShortExact.comp_δ
          (pairChainComplexSES_shortExact C R p) (n + 1) n
          (by simp [ComplexShape.down_Rel]))).Exact :=
  ShortComplex.ShortExact.homology_exact₃
    (pairChainComplexSES_shortExact C R p) (n + 1) n
    (by simp [ComplexShape.down_Rel])

/-- If Hₙ₊₁(X) = 0 and Hₙ(X) = 0, then ∂ : Hₙ₊₁(X,A) → Hₙ(A) is an isomorphism. -/
noncomputable def pairLES_δIso (n : ℕ)
    (h1 : IsZero (singularHomology' C R (n + 1) p.X))
    (h2 : IsZero (singularHomology' C R n p.X)) :
    relativeSingularHomology C R p (n + 1) ≅ singularHomology' C R n p.A :=
  ShortComplex.ShortExact.δIso
    (pairChainComplexSES_shortExact C R p) (n + 1) n
    (by simp [ComplexShape.down_Rel]) h1 h2

omit [CategoryWithHomology C] [Limits.HasPullbacks C] in
/-- If the inclusion of a pair is an isomorphism, then the relative chain
complex is zero. -/
theorem relativeSingularChainComplex_isZero_of_isIso_inclusion [IsIso p.i] :
    IsZero (relativeSingularChainComplex C R p) := by
  dsimp only [relativeSingularChainComplex, pairChainComplexSES, ShortComplex.cokernelSequence]
  let F := (singularChainComplexFunctor C).obj R
  haveI : IsIso (F.map p.i) := Functor.map_isIso F p.i
  exact isZero_cokernel_of_epi (F.map p.i)

omit [Limits.HasPullbacks C] in
/-- If the inclusion of a pair is an isomorphism, then its relative homology is
zero in every degree. -/
theorem relativeSingularHomology_isZero_of_isIso_inclusion [IsIso p.i] (n : ℕ) :
    IsZero (relativeSingularHomology C R p n) := by
  let K := relativeSingularChainComplex C R p
  have hK : IsZero K := relativeSingularChainComplex_isZero_of_isIso_inclusion C R p
  have h_id_zero : (𝟙 K : K ⟶ K) = 0 := by
    exact (IsZero.iff_id_eq_zero K).mp hK
  change IsZero (K.homology n)
  rw [IsZero.iff_id_eq_zero (K.homology n)]
  calc
    (𝟙 (K.homology n) : K.homology n ⟶ K.homology n)
        = HomologicalComplex.homologyMap (𝟙 K : K ⟶ K) n := by
          rw [HomologicalComplex.homologyMap_id]
    _ = HomologicalComplex.homologyMap (0 : K ⟶ K) n := by
          rw [h_id_zero]
    _ = 0 := by
          simp

end Abelian

section MapOfPairs

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable (R : C) [CategoryWithHomology C] [Limits.HasPullbacks C]

/-- Given a map of pairs, produce the induced chain map on relative chain complexes. -/
noncomputable def mapOfPairsRelChainMap
    (p p' : TopologicalPair.{w})
    (fX : p.X ⟶ p'.X) (fA : p.A ⟶ p'.A)
    (h : p.i ≫ fX = fA ≫ p'.i) :
    relativeSingularChainComplex C R p ⟶ relativeSingularChainComplex C R p' := by
  let F := (singularChainComplexFunctor C).obj R
  let Ci := p.inclusionChainMap C R
  let Ci' := p'.inclusionChainMap C R
  let fA' := F.map fA
  let fX' := F.map fX
  have h_comm : Ci ≫ fX' = fA' ≫ Ci' := by
    dsimp only [Ci, Ci', fA', fX', TopologicalPair.inclusionChainMap]
    rw [← F.map_comp, ← F.map_comp, h]
  exact cokernel.map Ci Ci' fA' fX' h_comm

/-- The induced map on relative homology from a map of pairs. -/
noncomputable def mapOfPairsRelHomologyMap
    (p p' : TopologicalPair.{w})
    (fX : p.X ⟶ p'.X) (fA : p.A ⟶ p'.A)
    (h : p.i ≫ fX = fA ≫ p'.i) (n : ℕ) :
    relativeSingularHomology C R p n ⟶ relativeSingularHomology C R p' n :=
  HomologicalComplex.homologyMap (mapOfPairsRelChainMap C R p p' fX fA h) n

omit [CategoryWithHomology C] [Limits.HasPullbacks C] in
/-- Naturality of the quotient map at the chain level for a map of pairs. -/
theorem mapOfPairsRelChainMap_naturality
    (p p' : TopologicalPair.{w})
    (fX : p.X ⟶ p'.X) (fA : p.A ⟶ p'.A)
    (h : p.i ≫ fX = fA ≫ p'.i) :
    (pairChainComplexSES C R p).g ≫ mapOfPairsRelChainMap C R p p' fX fA h =
      ((singularChainComplexFunctor C).obj R).map fX ≫ (pairChainComplexSES C R p').g := by
  let F := (singularChainComplexFunctor C).obj R
  let Ci := p.inclusionChainMap C R
  let Ci' := p'.inclusionChainMap C R
  let fA' := F.map fA
  let fX' := F.map fX
  let q := (pairChainComplexSES C R p).g
  let q' := (pairChainComplexSES C R p').g
  let fRel := mapOfPairsRelChainMap C R p p' fX fA h
  have h_comm : Ci ≫ fX' = fA' ≫ Ci' := by
    dsimp only [Ci, Ci', fA', fX', TopologicalPair.inclusionChainMap]
    rw [← F.map_comp, ← F.map_comp, h]
  have h_chain : q ≫ fRel = fX' ≫ q' := by
    dsimp only [fRel, mapOfPairsRelChainMap, q, q', pairChainComplexSES,
      ShortComplex.cokernelSequence]
    have h_w : Ci ≫ (fX' ≫ cokernel.π Ci') = 0 := by
      calc
        Ci ≫ (fX' ≫ cokernel.π Ci')
          = (Ci ≫ fX') ≫ cokernel.π Ci' := by rw [Category.assoc]
        _ = (fA' ≫ Ci') ≫ cokernel.π Ci' := by rw [h_comm]
        _ = fA' ≫ (Ci' ≫ cokernel.π Ci') := by rw [Category.assoc]
        _ = fA' ≫ 0 := by rw [cokernel.condition]
        _ = 0 := by simp
    exact cokernel.π_desc Ci (fX' ≫ cokernel.π Ci') h_w
  exact h_chain

omit [Limits.HasPullbacks C] in
/-- Naturality of the quotient homology map for a map of pairs. -/
theorem quotientHomologyMap_naturality
    (p p' : TopologicalPair.{w})
    (fX : p.X ⟶ p'.X) (fA : p.A ⟶ p'.A)
    (h : p.i ≫ fX = fA ≫ p'.i) (n : ℕ) :
    quotientHomologyMap C R p n ≫ mapOfPairsRelHomologyMap C R p p' fX fA h n =
      ((singularHomologyFunctor C n).obj R).map fX ≫ quotientHomologyMap C R p' n := by
  let F := (singularChainComplexFunctor C).obj R
  have h_chain := mapOfPairsRelChainMap_naturality C R p p' fX fA h
  have h_left :
      HomologicalComplex.homologyMap (pairChainComplexSES C R p).g n ≫
          HomologicalComplex.homologyMap (mapOfPairsRelChainMap C R p p' fX fA h) n =
        HomologicalComplex.homologyMap
          ((pairChainComplexSES C R p).g ≫
            mapOfPairsRelChainMap C R p p' fX fA h) n := by
    exact (HomologicalComplex.homologyMap_comp (pairChainComplexSES C R p).g
      (mapOfPairsRelChainMap C R p p' fX fA h) n).symm
  have h_right :
      HomologicalComplex.homologyMap (F.map fX) n ≫
          HomologicalComplex.homologyMap (pairChainComplexSES C R p').g n =
        HomologicalComplex.homologyMap
          (F.map fX ≫ (pairChainComplexSES C R p').g) n := by
    exact (HomologicalComplex.homologyMap_comp (F.map fX)
      (pairChainComplexSES C R p').g n).symm
  change
    HomologicalComplex.homologyMap (pairChainComplexSES C R p).g n ≫
        HomologicalComplex.homologyMap (mapOfPairsRelChainMap C R p p' fX fA h) n =
      HomologicalComplex.homologyMap (F.map fX) n ≫
        HomologicalComplex.homologyMap (pairChainComplexSES C R p').g n
  rw [h_left, h_right, h_chain]
  rfl

omit [CategoryWithHomology C] in
/-- A map of pairs induces a morphism between the short exact sequences
`C(A) ⟶ C(X) ⟶ C(X,A)` and `C(A') ⟶ C(X') ⟶ C(X',A')`. -/
noncomputable def mapOfPairsSESMap
    (p p' : TopologicalPair.{w})
    (fX : p.X ⟶ p'.X) (fA : p.A ⟶ p'.A)
    (h : p.i ≫ fX = fA ≫ p'.i) :
    pairChainComplexSES C R p ⟶ pairChainComplexSES C R p' := by
  let F := (singularChainComplexFunctor C).obj R
  let fA' := F.map fA
  let fX' := F.map fX
  let fRel := mapOfPairsRelChainMap C R p p' fX fA h
  refine ShortComplex.homMk fA' fX' fRel ?_ ?_
  · dsimp only [pairChainComplexSES, ShortComplex.cokernelSequence,
      TopologicalPair.inclusionChainMap, fA', fX']
    rw [← F.map_comp, ← F.map_comp, h]
  · exact (mapOfPairsRelChainMap_naturality C R p p' fX fA h).symm

/-- Naturality of the connecting homomorphism in the long exact sequence of a
pair, for maps of pairs, stated in the chain-level homology-map form. -/
theorem connectingHomomorphism_naturality_chain
    (p p' : TopologicalPair.{w})
    (fX : p.X ⟶ p'.X) (fA : p.A ⟶ p'.A)
    (h : p.i ≫ fX = fA ≫ p'.i) (n : ℕ) :
    let φ := mapOfPairsSESMap C R p p' fX fA h
    ShortComplex.ShortExact.δ (pairChainComplexSES_shortExact C R p) (n + 1) n
        (by simp [ComplexShape.down_Rel]) ≫
        HomologicalComplex.homologyMap φ.τ₁ n =
      HomologicalComplex.homologyMap φ.τ₃ (n + 1) ≫
        ShortComplex.ShortExact.δ (pairChainComplexSES_shortExact C R p') (n + 1) n
          (by simp [ComplexShape.down_Rel]) := by
  dsimp only
  let φ := mapOfPairsSESMap C R p p' fX fA h
  simpa [φ, mapOfPairsSESMap] using
    (HomologicalComplex.HomologySequence.δ_naturality φ
      (pairChainComplexSES_shortExact C R p)
      (pairChainComplexSES_shortExact C R p') (n + 1) n
      (by simp [ComplexShape.down_Rel]))

omit [CategoryWithHomology C] in
/-- Composition of maps of pairs at the chain level. -/
theorem mapOfPairsRelChainMap_comp
    (p p' p'' : TopologicalPair.{w})
    (fX : p.X ⟶ p'.X) (fA : p.A ⟶ p'.A)
    (hf : p.i ≫ fX = fA ≫ p'.i)
    (gX : p'.X ⟶ p''.X) (gA : p'.A ⟶ p''.A)
    (hg : p'.i ≫ gX = gA ≫ p''.i) :
    mapOfPairsRelChainMap C R p p'' (fX ≫ gX) (fA ≫ gA)
        (by
          calc
            p.i ≫ (fX ≫ gX) = (p.i ≫ fX) ≫ gX := by rw [Category.assoc]
            _ = (fA ≫ p'.i) ≫ gX := by rw [hf]
            _ = fA ≫ (p'.i ≫ gX) := by rw [Category.assoc]
            _ = fA ≫ (gA ≫ p''.i) := by rw [hg]
            _ = (fA ≫ gA) ≫ p''.i := by rw [← Category.assoc]) =
      mapOfPairsRelChainMap C R p p' fX fA hf ≫
        mapOfPairsRelChainMap C R p' p'' gX gA hg := by
  let F := (singularChainComplexFunctor C).obj R
  let q : singularChainComplex' C R p.X ⟶ relativeSingularChainComplex C R p :=
    (pairChainComplexSES C R p).g
  let q' : singularChainComplex' C R p'.X ⟶ relativeSingularChainComplex C R p' :=
    (pairChainComplexSES C R p').g
  let q'' : singularChainComplex' C R p''.X ⟶ relativeSingularChainComplex C R p'' :=
    (pairChainComplexSES C R p'').g
  let fRel := mapOfPairsRelChainMap C R p p' fX fA hf
  let gRel := mapOfPairsRelChainMap C R p' p'' gX gA hg
  let hcomp : p.i ≫ (fX ≫ gX) = (fA ≫ gA) ≫ p''.i := by
    calc
      p.i ≫ (fX ≫ gX) = (p.i ≫ fX) ≫ gX := by rw [Category.assoc]
      _ = (fA ≫ p'.i) ≫ gX := by rw [hf]
      _ = fA ≫ (p'.i ≫ gX) := by rw [Category.assoc]
      _ = fA ≫ (gA ≫ p''.i) := by rw [hg]
      _ = (fA ≫ gA) ≫ p''.i := by rw [← Category.assoc]
  let fgRel := mapOfPairsRelChainMap C R p p'' (fX ≫ gX) (fA ≫ gA) hcomp
  have h1 : q ≫ fRel = F.map fX ≫ q' :=
    mapOfPairsRelChainMap_naturality C R p p' fX fA hf
  have h2 : q' ≫ gRel = F.map gX ≫ q'' :=
    mapOfPairsRelChainMap_naturality C R p' p'' gX gA hg
  have h3 : q ≫ fgRel = F.map (fX ≫ gX) ≫ q'' :=
    mapOfPairsRelChainMap_naturality C R p p'' (fX ≫ gX) (fA ≫ gA) hcomp
  have h4 : q ≫ (fRel ≫ gRel) = F.map (fX ≫ gX) ≫ q'' := by
    calc
      q ≫ (fRel ≫ gRel) = (q ≫ fRel) ≫ gRel := by rw [Category.assoc]
      _ = (F.map fX ≫ q') ≫ gRel := by rw [h1]
      _ = F.map fX ≫ (q' ≫ gRel) := by rw [Category.assoc]
      _ = F.map fX ≫ (F.map gX ≫ q'') := by rw [h2]
      _ = (F.map fX ≫ F.map gX) ≫ q'' := by rw [Category.assoc]
      _ = F.map (fX ≫ gX) ≫ q'' := by
        rw [← F.map_comp]
  have h5 : q ≫ fgRel = q ≫ (fRel ≫ gRel) := by
    rw [h3, h4]
  haveI : Epi q := by
    dsimp only [q]
    exact (pairChainComplexSES_shortExact C R p).epi_g
  exact (cancel_epi q).mp h5

/-- Composition of maps of pairs on relative homology. -/
theorem mapOfPairsRelHomologyMap_comp
    (p p' p'' : TopologicalPair.{w})
    (fX : p.X ⟶ p'.X) (fA : p.A ⟶ p'.A)
    (hf : p.i ≫ fX = fA ≫ p'.i)
    (gX : p'.X ⟶ p''.X) (gA : p'.A ⟶ p''.A)
    (hg : p'.i ≫ gX = gA ≫ p''.i) (n : ℕ) :
    mapOfPairsRelHomologyMap C R p p'' (fX ≫ gX) (fA ≫ gA)
        (by
          calc
            p.i ≫ (fX ≫ gX) = (p.i ≫ fX) ≫ gX := by rw [Category.assoc]
            _ = (fA ≫ p'.i) ≫ gX := by rw [hf]
            _ = fA ≫ (p'.i ≫ gX) := by rw [Category.assoc]
            _ = fA ≫ (gA ≫ p''.i) := by rw [hg]
            _ = (fA ≫ gA) ≫ p''.i := by rw [← Category.assoc]) n =
      mapOfPairsRelHomologyMap C R p p' fX fA hf n ≫
        mapOfPairsRelHomologyMap C R p' p'' gX gA hg n := by
  let hcomp : p.i ≫ (fX ≫ gX) = (fA ≫ gA) ≫ p''.i := by
    calc
      p.i ≫ (fX ≫ gX) = (p.i ≫ fX) ≫ gX := by rw [Category.assoc]
      _ = (fA ≫ p'.i) ≫ gX := by rw [hf]
      _ = fA ≫ (p'.i ≫ gX) := by rw [Category.assoc]
      _ = fA ≫ (gA ≫ p''.i) := by rw [hg]
      _ = (fA ≫ gA) ≫ p''.i := by rw [← Category.assoc]
  have h_chain :
      mapOfPairsRelChainMap C R p p'' (fX ≫ gX) (fA ≫ gA) hcomp =
        mapOfPairsRelChainMap C R p p' fX fA hf ≫
          mapOfPairsRelChainMap C R p' p'' gX gA hg :=
    mapOfPairsRelChainMap_comp C R p p' p'' fX fA hf gX gA hg
  dsimp only [mapOfPairsRelHomologyMap]
  rw [h_chain]
  exact HomologicalComplex.homologyMap_comp
    (mapOfPairsRelChainMap C R p p' fX fA hf)
    (mapOfPairsRelChainMap C R p' p'' gX gA hg) n

omit [CategoryWithHomology C] in
/-- Congruence for maps of pairs at the chain level. -/
theorem mapOfPairsRelChainMap_congr
    (p p' : TopologicalPair.{w})
    {fX₁ fX₂ : p.X ⟶ p'.X} {fA₁ fA₂ : p.A ⟶ p'.A}
    (h₁ : p.i ≫ fX₁ = fA₁ ≫ p'.i)
    (h₂ : p.i ≫ fX₂ = fA₂ ≫ p'.i)
    (hX : fX₁ = fX₂) (_hA : fA₁ = fA₂) :
    mapOfPairsRelChainMap C R p p' fX₁ fA₁ h₁ =
      mapOfPairsRelChainMap C R p p' fX₂ fA₂ h₂ := by
  let F := (singularChainComplexFunctor C).obj R
  let q : singularChainComplex' C R p.X ⟶ relativeSingularChainComplex C R p :=
    (pairChainComplexSES C R p).g
  let q' : singularChainComplex' C R p'.X ⟶ relativeSingularChainComplex C R p' :=
    (pairChainComplexSES C R p').g
  let fRel₁ := mapOfPairsRelChainMap C R p p' fX₁ fA₁ h₁
  let fRel₂ := mapOfPairsRelChainMap C R p p' fX₂ fA₂ h₂
  have hnat₁ : q ≫ fRel₁ = F.map fX₁ ≫ q' :=
    mapOfPairsRelChainMap_naturality C R p p' fX₁ fA₁ h₁
  have hnat₂ : q ≫ fRel₂ = F.map fX₂ ≫ q' :=
    mapOfPairsRelChainMap_naturality C R p p' fX₂ fA₂ h₂
  have hmap : F.map fX₁ = F.map fX₂ := by rw [hX]
  have h_eq : q ≫ fRel₁ = q ≫ fRel₂ := by
    rw [hnat₁, hmap, hnat₂]
  haveI : Epi q := by
    dsimp only [q]
    exact (pairChainComplexSES_shortExact C R p).epi_g
  exact (cancel_epi q).mp h_eq

/-- Congruence for maps of pairs on relative homology. -/
theorem mapOfPairsRelHomologyMap_congr
    (p p' : TopologicalPair.{w})
    {fX₁ fX₂ : p.X ⟶ p'.X} {fA₁ fA₂ : p.A ⟶ p'.A}
    (h₁ : p.i ≫ fX₁ = fA₁ ≫ p'.i)
    (h₂ : p.i ≫ fX₂ = fA₂ ≫ p'.i)
    (hX : fX₁ = fX₂) (hA : fA₁ = fA₂) (n : ℕ) :
    mapOfPairsRelHomologyMap C R p p' fX₁ fA₁ h₁ n =
      mapOfPairsRelHomologyMap C R p p' fX₂ fA₂ h₂ n := by
  have h_chain :
      mapOfPairsRelChainMap C R p p' fX₁ fA₁ h₁ =
        mapOfPairsRelChainMap C R p p' fX₂ fA₂ h₂ :=
    mapOfPairsRelChainMap_congr C R p p' h₁ h₂ hX hA
  dsimp only [mapOfPairsRelHomologyMap]
  rw [h_chain]

omit [CategoryWithHomology C] in
/-- The identity map of a pair induces the identity map on relative chain complexes. -/
theorem mapOfPairsRelChainMap_id (p : TopologicalPair.{w}) :
    mapOfPairsRelChainMap C R p p (𝟙 p.X) (𝟙 p.A) (by simp) = 𝟙 _ := by
  let F := (singularChainComplexFunctor C).obj R
  let q : singularChainComplex' C R p.X ⟶ relativeSingularChainComplex C R p :=
    (pairChainComplexSES C R p).g
  have hnat :
      q ≫ mapOfPairsRelChainMap C R p p (𝟙 p.X) (𝟙 p.A) (by simp) =
        F.map (𝟙 p.X) ≫ q :=
    mapOfPairsRelChainMap_naturality C R p p (𝟙 p.X) (𝟙 p.A) (by simp)
  have h_eq :
      q ≫ mapOfPairsRelChainMap C R p p (𝟙 p.X) (𝟙 p.A) (by simp) =
        q ≫ 𝟙 _ := by
    rw [hnat, F.map_id]
    simp
  haveI : Epi q := by
    dsimp only [q]
    exact (pairChainComplexSES_shortExact C R p).epi_g
  exact (cancel_epi q).mp h_eq

/-- The identity map of a pair induces the identity map on relative homology. -/
theorem mapOfPairsRelHomologyMap_id (p : TopologicalPair.{w}) (n : ℕ) :
    mapOfPairsRelHomologyMap C R p p (𝟙 p.X) (𝟙 p.A) (by simp) n = 𝟙 _ := by
  dsimp only [mapOfPairsRelHomologyMap]
  rw [mapOfPairsRelChainMap_id C R p]
  exact HomologicalComplex.homologyMap_id _ n

end MapOfPairs

end AlgebraicTopology
