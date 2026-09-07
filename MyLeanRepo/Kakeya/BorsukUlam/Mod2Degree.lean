/-
# Bockstein Short Exact Sequence for Singular Homology

Constructs and proves exact the short exact sequence of singular chain complexes:
  0 → C_*(X; ℤ) --2→ C_*(X; ℤ) → C_*(X; Z/2) → 0

Derives:
- coeffChange_surjective: H_n(S^n; ℤ) → H_n(S^n; Z/2) is surjective for n ≥ 1
- topSphereHomologyIsoZ2: H_n(S^n; Z/2) ≅ Z/2 for n ≥ 1
-/

import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.Degree.Homology
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.StdSphereHomology
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.TopSphereHomology
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open Vendored.AlgebraicTopology.Degree

variable {n : ℕ}

/-- Z/2 as AddCommGrpCat object. -/
abbrev R2 : AddCommGrpCat := AddCommGrpCat.of (ZMod 2)

/-- Coefficient reduction ℤ → Z/2. -/
def coeffReductionMap : AddCommGrpCat.of ℤ ⟶ R2 :=
  AddCommGrpCat.ofHom
    { toFun := fun n : ℤ => (n : ZMod 2)
      map_zero' := by simp
      map_add' := by intro a b; simp }

/-- The coefficient short exact sequence 0 → ℤ --2→ ℤ → Z/2 → 0. -/
def coeffShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (2 • 𝟙 (AddCommGrpCat.of ℤ)) coeffReductionMap (by
    ext
    simp [coeffReductionMap]
    <;> decide)

/-- Proof that the coefficient sequence is short exact. -/
lemma coeffShortExact : coeffShortComplex.ShortExact := by
  let f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ := 2 • 𝟙 _
  let g : AddCommGrpCat.of ℤ ⟶ R2 := coeffReductionMap
  have hfg : f ≫ g = 0 := coeffShortComplex.zero
  have h_mono : Mono f := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro (x : ℤ) (y : ℤ) h
    simpa [f] using h
  have h_epi : Epi g := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro (z : ZMod 2)
    refine ⟨z.val, ?_⟩
    simp [g, coeffReductionMap]
    <;> fin_cases z <;> decide
  have h_mod2 : ∀ (n : ℤ), (n : ZMod 2) = 0 → n % 2 = 0 := by
    intro n h
    by_cases h7 : n % 2 = 0
    · exact h7
    · have h8 : n % 2 = 1 := by omega
      have h9 : ∃ (m : ℤ), n = 2 * m + 1 := by
        refine ⟨n / 2, ?_⟩
        omega
      rcases h9 with ⟨m, hm⟩
      rw [hm] at h
      have h10 : ((2 * m + 1 : ℤ) : ZMod 2) = 1 := by
        have h11 : (2 : ZMod 2) = 0 := by decide
        calc
          ((2 * m + 1 : ℤ) : ZMod 2)
            = (2 : ZMod 2) * (m : ZMod 2) + 1 := by simp
          _ = 0 * (m : ZMod 2) + 1 := by rw [h11]
          _ = 1 := by ring
      rw [h10] at h
      <;> norm_num at h
  have h_div2 : ∀ (x y : ℤ), x % 2 = 0 → y % 2 = 0 → (x + y) / 2 = x / 2 + y / 2 := by
    intro x y hx hy
    have hx' : x = 2 * (x / 2) := by omega
    have hy' : y = 2 * (y / 2) := by omega
    have h : x + y = 2 * (x / 2 + y / 2) := by linarith
    omega
  have h_lift : ∀ {A : AddCommGrpCat} (k : A ⟶ AddCommGrpCat.of ℤ)
      (hk : k ≫ g = 0), { l : A ⟶ AddCommGrpCat.of ℤ // l ≫ f = k } := by
    intro A k hk
    let k' : A → ℤ := (k : A → ℤ)
    have h_k'_add : ∀ (a b : A), k' (a + b) = k' a + k' b := by
      intro a b
      exact (k.hom).map_add a b
    have h_even : ∀ (a : A), (k' a : ZMod 2) = 0 := by
      intro a
      have h : (k ≫ g) a = 0 := by rw [hk] <;> simp
      exact h
    have h_even2 : ∀ (a : A), (k' a) % 2 = 0 := by
      intro a
      exact h_mod2 (k' a) (h_even a)
    let l : A → ℤ := fun a => (k' a) / 2
    have l_add : ∀ (a b : A), l (a + b) = l a + l b := by
      intro a b
      have h1 : k' (a + b) = k' a + k' b := h_k'_add a b
      dsimp only [l]
      rw [h1]
      exact h_div2 (k' a) (k' b) (h_even2 a) (h_even2 b)
    have l_zero : l 0 = 0 := by
      dsimp only [l]
      have hz : k' 0 = 0 := (k.hom).map_zero
      rw [hz] <;> norm_num
    let l_hom : A →+ AddCommGrpCat.of ℤ :=
      { toFun := l
        map_zero' := l_zero
        map_add' := l_add }
    let l_mor : A ⟶ AddCommGrpCat.of ℤ := AddCommGrpCat.ofHom l_hom
    have hfac : l_mor ≫ f = k := by
      ext a
      have h4 : k' a = 2 * (k' a / 2) := by
        have h5 : (k' a) % 2 = 0 := h_even2 a
        omega
      simpa [l_mor, l_hom, l, f, k'] using h4.symm
    exact ⟨l_mor, hfac⟩
  have h_kernel : IsLimit (KernelFork.ofι f hfg) :=
    KernelFork.IsLimit.ofι' f hfg (h := fun {A} k hk => h_lift k hk)
  have h_exact : coeffShortComplex.Exact :=
    ShortComplex.exact_of_f_is_kernel coeffShortComplex h_kernel
  letI : Mono coeffShortComplex.f := h_mono
  letI : Epi coeffShortComplex.g := h_epi
  exact ⟨h_exact⟩

/-- Abbreviation for H_n(X; Z/2). -/
abbrev HnZ2 (X : TopCat) (n : ℕ) : AddCommGrpCat :=
  ((singularHomologyFunctor AddCommGrpCat n).obj R2).obj X

/-- Coefficient change map H_n(X; ℤ) → H_n(X; Z/2). -/
noncomputable def coeffChangeHomology (X : TopCat) (n : ℕ) :
    Hn X n ⟶ HnZ2 X n :=
  ((singularHomologyFunctor AddCommGrpCat n).map coeffReductionMap).app X

/-- The singular chain complex with coefficients R. -/
abbrev chainC (R : AddCommGrpCat) (X : TopCat) : ChainComplex AddCommGrpCat ℕ :=
  singularChainComplex' AddCommGrpCat R X

/-- Multiplication by 2 on C_*(X; ℤ). -/
noncomputable def multTwo (X : TopCat) :
    chainC (AddCommGrpCat.of ℤ) X ⟶ chainC (AddCommGrpCat.of ℤ) X :=
  2 • 𝟙 _

/-- Coefficient reduction on chain complexes. -/
noncomputable def coeffReduction (X : TopCat) :
    chainC (AddCommGrpCat.of ℤ) X ⟶ chainC R2 X :=
  ((SSet.chainComplexFunctor AddCommGrpCat).map coeffReductionMap).app (TopCat.toSSet.obj X)

/-- multTwo ≫ coeffReduction = 0. -/
lemma multTwo_comp_coeffReduction (X : TopCat) :
    multTwo X ≫ coeffReduction X = 0 := by
  let F := SSet.chainComplexFunctor AddCommGrpCat
  let f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ := 2 • 𝟙 _
  let g : AddCommGrpCat.of ℤ ⟶ R2 := coeffReductionMap
  have hfg : f ≫ g = 0 := by
    ext
    simp [f, g, coeffReductionMap] <;> decide
  have h1 : F.map f ≫ F.map g = 0 := by
    calc
      F.map f ≫ F.map g = F.map (f ≫ g) := by rw [←F.map_comp]
      _ = F.map 0 := by rw [hfg]
      _ = 0 := by simp
  have h2 : (F.map f ≫ F.map g).app (TopCat.toSSet.obj X) = 0 := by
    rw [h1] <;> simp
  have h31 : F.map f = 2 • 𝟙 (F.obj (AddCommGrpCat.of ℤ)) := by
    dsimp only [f]
    rw [Functor.map_smul, F.map_id] <;> simp
  have h3 : (F.map f).app (TopCat.toSSet.obj X) = multTwo X := by
    rw [h31] <;> simp [multTwo] <;> rfl
  have h4 : (F.map g).app (TopCat.toSSet.obj X) = coeffReduction X := by rfl
  have h5 : (F.map f ≫ F.map g).app (TopCat.toSSet.obj X) =
      (F.map f).app (TopCat.toSSet.obj X) ≫ (F.map g).app (TopCat.toSSet.obj X) := by rfl
  rw [h5, h3, h4] at h2
  exact h2

/-- The Bockstein short complex of chain complexes for X. -/
noncomputable def bocksteinShortComplex (X : TopCat) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (multTwo X) (coeffReduction X) (multTwo_comp_coeffReduction X)

/-- Coproduct functor via sigmaConst - definitionally matches chain groups. -/
def G_I (I : Type) : AddCommGrpCat ⥤ AddCommGrpCat :=
  { obj := fun R => (sigmaConst.obj R).obj I
    map := fun {R R'} f => (sigmaConst.map f).app I }

/-- Coproduct functor via colim - has exactness properties by AB4. -/
def G_I_colim (I : Type) : AddCommGrpCat ⥤ AddCommGrpCat :=
  Functor.const (Discrete I) ⋙ colim (J := Discrete I) (C := AddCommGrpCat)

instance _root_.GIColimInstances (I : Type) :
    (Functor.const (Discrete I) : AddCommGrpCat ⥤ (Discrete I ⥤ AddCommGrpCat)).Additive := by
  exact Functor.additive_of_preserves_binary_products (Functor.const (Discrete I))
instance _root_.GIColimInstances2 (I : Type) :
    (colim (J := Discrete I) (C := AddCommGrpCat)).Additive := by
  exact instAdditiveFunctorColim
instance _root_.GIColimInstances3 (I : Type) : (G_I_colim I).Additive := by delta G_I_colim; infer_instance
instance _root_.GIColimInstances4 (I : Type) : PreservesFiniteLimits (G_I_colim I) := by
  delta G_I_colim
  exact comp_preservesFiniteLimits (Functor.const (Discrete I)) colim
instance _root_.GIColimInstances5 (I : Type) : PreservesFiniteColimits (G_I_colim I) := by
  delta G_I_colim
  exact comp_preservesFiniteColimits (Functor.const (Discrete I)) colim

/-- Natural isomorphism between the two coproduct functors. -/
def G_I_iso (I : Type) : G_I I ≅ G_I_colim I :=
  NatIso.ofComponents (fun R => by exact Iso.refl _) (by
    intro R R' f
    ext i
    simp [G_I, G_I_colim, colimit.ι_desc, Limits.Sigma.ι_map]
    <;> rfl)

/-- G_I preserves finite limits (transferred from G_I_colim via iso). -/
instance (I : Type) : PreservesFiniteLimits (G_I I) :=
  preservesFiniteLimits_of_natIso (G_I_iso I).symm

/-- G_I preserves finite colimits (transferred from G_I_colim via iso). -/
instance (I : Type) : PreservesFiniteColimits (G_I I) :=
  preservesFiniteColimits_of_natIso (G_I_iso I).symm

instance (I : Type) : (G_I I).Additive := by
  refine' ⟨fun {X Y} f g => _⟩
  simp [G_I]
  <;> rfl

/-- G_I preserves short exact sequences (by AB4). -/
lemma G_I_preserves_shortExact (I : Type)
    (S : ShortComplex AddCommGrpCat) (hS : S.ShortExact) :
    (S.map (G_I I)).ShortExact := by
  have h6 : (G_I I).PreservesHomology := Functor.preservesHomologyOfExact (G_I I)
  have h7 := (Functor.exact_tfae (G_I I)).out 2 0 |>.1 h6
  exact h7 S hS

/-- The functor R ↦ C_k(X; R), the degree-k chain group functor. -/
noncomputable def chainDegreeFunctor (X : TopCat) (k : ℕ) :
    AddCommGrpCat ⥤ AddCommGrpCat :=
  { obj := fun R => (chainC R X).X k
    map := fun {R R'} f =>
      ((SSet.chainComplexFunctor AddCommGrpCat).map f).app (TopCat.toSSet.obj X) |>.f k
    map_id := by
      intro R
      simp [chainC, SSet.chainComplexFunctor, alternatingFaceMapComplex_map_f]
      <;> rfl
    map_comp := by
      intro R R' R'' f g
      simp [chainC, SSet.chainComplexFunctor, alternatingFaceMapComplex_map_f]
      <;> rfl }

/-- chainDegreeFunctor is additive. -/
instance (X : TopCat) (k : ℕ) : (chainDegreeFunctor X k).Additive := by
  refine' ⟨fun {R R'} f g => _⟩
  simp [chainDegreeFunctor, SSet.chainComplexFunctor]
  <;> rfl

/-- Natural isomorphism chainDegreeFunctor X k ≅ G_I I. -/
def chainDegreeFunctorIso (X : TopCat) (k : ℕ) :
    chainDegreeFunctor X k ≅ G_I ((TopCat.toSSet.obj X) _⦋k⦌) :=
  NatIso.ofComponents (fun R => by exact Iso.refl _) (by
    intro R R' f
    ext i
    simp [chainDegreeFunctor, G_I, SSet.chainComplexFunctor,
      alternatingFaceMapComplex_map_f, sigmaConst]
    <;> rfl)

/-- chainDegreeFunctor preserves finite limits. -/
instance (X : TopCat) (k : ℕ) : PreservesFiniteLimits (chainDegreeFunctor X k) :=
  preservesFiniteLimits_of_natIso (chainDegreeFunctorIso X k).symm

/-- chainDegreeFunctor preserves finite colimits. -/
instance (X : TopCat) (k : ℕ) : PreservesFiniteColimits (chainDegreeFunctor X k) :=
  preservesFiniteColimits_of_natIso (chainDegreeFunctorIso X k).symm

/-- The degreewise short complex is isomorphic to coeffShortComplex mapped by chainDegreeFunctor. -/
def degreewiseShortComplexIso (X : TopCat) (k : ℕ) :
    coeffShortComplex.map (chainDegreeFunctor X k) ≅
    (bocksteinShortComplex X).map (eval AddCommGrpCat (ComplexShape.down ℕ) k) := by
  let S_eval := (bocksteinShortComplex X).map (eval AddCommGrpCat (ComplexShape.down ℕ) k)
  let S_F := coeffShortComplex.map (chainDegreeFunctor X k)
  have hf : S_eval.f = S_F.f := by
    dsimp only [S_eval, S_F, bocksteinShortComplex, ShortComplex.map,
      coeffShortComplex, chainDegreeFunctor, multTwo]
    simp [SSet.chainComplexFunctor, Functor.map_smul, alternatingFaceMapComplex_map_f]
    <;> rfl
  have hg : S_eval.g = S_F.g := by
    dsimp only [S_eval, S_F, bocksteinShortComplex, ShortComplex.map,
      coeffShortComplex, chainDegreeFunctor, coeffReduction]
    <;> rfl
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) hf hg

/-- The Bockstein short complex is short exact. -/
theorem bocksteinShortExact (X : TopCat) :
    (bocksteinShortComplex X).ShortExact := by
  let S := bocksteinShortComplex X
  have h_deg : ∀ (k : ℕ), (S.map (eval AddCommGrpCat (ComplexShape.down ℕ) k)).ShortExact := by
    intro k
    let F := chainDegreeFunctor X k
    let S_F := coeffShortComplex.map F
    have h_iso := degreewiseShortComplexIso X k
    have h_pres : F.PreservesHomology := Functor.preservesHomologyOfExact F
    have h_main := (Functor.exact_tfae F).out 2 0 |>.1 h_pres
    have hS_F : S_F.ShortExact := h_main coeffShortComplex coeffShortExact
    exact ShortComplex.shortExact_of_iso h_iso hS_F
  exact HomologicalComplex.shortExact_of_degreewise_shortExact S h_deg

/-- Multiplication by 2 on H_0(X; ℤ) is mono for any topological space X. -/
lemma h0_two_smul_mono (X : TopCat) : Mono (2 • 𝟙 (Hn X 0)) := by
  let e := TopCat.singularHomology₀Iso X (AddCommGrpCat.of ℤ)
  let I := ZerothHomotopy X
  let G := G_I I
  let B := G.obj (AddCommGrpCat.of ℤ)
  let hB : B ⟶ B := 2 • 𝟙 B
  have h_main : Mono hB := by
    have h1 : hB = G.map (2 • 𝟙 (AddCommGrpCat.of ℤ)) := by
      rw [G.map_smul, G.map_id] <;> rfl
    rw [h1]
    have h2 : Mono (2 • 𝟙 (AddCommGrpCat.of ℤ)) := by
      rw [AddCommGrpCat.mono_iff_injective]
      intro x y h
      simpa using h
    exact Functor.map_mono G (2 • 𝟙 (AddCommGrpCat.of ℤ))
  let hA : Hn X 0 ⟶ Hn X 0 := 2 • 𝟙 (Hn X 0)
  have h_nat : e.inv ≫ hA = hB ≫ e.inv := by
    have h1 : e.inv ≫ hA = e.inv + e.inv := by
      have h11 : hA = 𝟙 (Hn X 0) + 𝟙 (Hn X 0) := by
        simp [hA, two_smul] <;> abel
      rw [h11, comp_add] <;> simp
    have h2 : hB ≫ e.inv = e.inv + e.inv := by
      have h21 : hB = 𝟙 B + 𝟙 B := by
        simp [hB, two_smul] <;> abel
      rw [h21, add_comp] <;> simp <;> rfl
    rw [h1, h2]
  have h3 : hA = e.hom ≫ hB ≫ e.inv := by
    calc
      hA
        = e.hom ≫ (e.inv ≫ hA) := by simp [Iso.hom_inv_id_assoc]
      _ = e.hom ≫ (hB ≫ e.inv) := by rw [h_nat] <;> rfl
      _ = e.hom ≫ hB ≫ e.inv := by simp [Category.assoc]
  change Mono hA
  rw [h3]
  have h_iff1 : Mono (e.hom ≫ (hB ≫ e.inv)) ↔ Mono (hB ≫ e.inv) := by
    exact mono_comp_iff_of_isIso e.hom (hB ≫ e.inv)
  rw [h_iff1]
  have h_iff2 : Mono (hB ≫ e.inv) ↔ Mono hB := by
    exact mono_comp_iff_of_mono hB e.inv
  rw [h_iff2]
  exact h_main

/-- Coefficient change H_n(S^n; ℤ) → H_n(S^n; Z/2) is surjective for n ≥ 1. -/
theorem coeffChange_surjective (n : ℕ) (hn : 1 ≤ n) :
    Epi (coeffChangeHomology (TopSphere n) n) := by
  let X := TopSphere n
  let S := bocksteinShortComplex X
  have hS : S.ShortExact := bocksteinShortExact X
  let c := ComplexShape.down ℕ
  have h_rel : c.Rel n (n - 1) := by
    cases n with
    | zero => linarith
    | succ n' => simp [c, ComplexShape.down]
  let δ := hS.δ n (n - 1) h_rel
  let S_hom3 := ShortComplex.mk
    (HomologicalComplex.homologyMap S.g n)
    δ
    (hS.comp_δ n (n - 1) h_rel)
  have h_exact3 : S_hom3.Exact := hS.homology_exact₃ n (n - 1) h_rel
  have hδ : δ = 0 := by
    by_cases h_n2 : n ≥ 2
    · have h_vanish : IsZero (Hn X (n - 1)) :=
        AlgebraicTopology.StdSphereHomology.stdSphere_vanishing n (n - 1) (by omega) (by omega)
      exact IsZero.eq_zero_of_tgt h_vanish δ
    · have h_n1 : n = 1 := by omega
      subst h_n1
      let g : S.X₂ ⟶ S.X₂ := S.f
      have hg : g = 𝟙 S.X₂ + 𝟙 S.X₂ := by
        simp [g, S, bocksteinShortComplex, multTwo, two_smul] <;> abel
      have h5 : HomologicalComplex.homologyMap g 0 = 2 • 𝟙 (Hn X 0) := by
        rw [hg]
        have h7 := HomologicalComplex.homologyMap_add (𝟙 S.X₂) (𝟙 S.X₂)
        rw [h7, HomologicalComplex.homologyMap_id]
        show (𝟙 (Hn X 0) + 𝟙 (Hn X 0)) = (2 • 𝟙 (Hn X 0))
        simp [two_smul] <;> abel
      have h6 : HomologicalComplex.homologyMap S.f 0 = HomologicalComplex.homologyMap g 0 := by rfl
      have h_eq : HomologicalComplex.homologyMap S.f 0 = 2 • 𝟙 (Hn X 0) := by
        rw [h6]
        exact h5
      have h_mono : Mono (HomologicalComplex.homologyMap S.f 0) := by
        rw [h_eq]
        exact h0_two_smul_mono X
      let S_hom1 := ShortComplex.mk δ
        (HomologicalComplex.homologyMap S.f 0)
        (hS.δ_comp 1 0 (by simp [ComplexShape.down]))
      have h_exact1 : S_hom1.Exact := hS.homology_exact₁ 1 0 (by simp [ComplexShape.down])
      have h : S_hom1.f = 0 := (h_exact1.mono_g_iff).mp h_mono
      exact h
  have h_epi : Epi S_hom3.f := h_exact3.epi_f hδ
  have h_eq2 : S_hom3.f = coeffChangeHomology X n := by rfl
  rw [h_eq2] at h_epi
  exact h_epi

/-- H_n(S^n; Z/2) ≅ Z/2 for n ≥ 1. -/
noncomputable def topSphereHomologyIsoZ2 (n : ℕ) (hn : 1 ≤ n) :
    HnZ2 (TopSphere n) n ≅ R2 := by
  let X := TopSphere n
  let S := bocksteinShortComplex X
  have hS : S.ShortExact := bocksteinShortExact X
  let A := Hn X n
  let C := HnZ2 X n
  let B := AddCommGrpCat.of ℤ
  let f : A ⟶ A := 2 • 𝟙 A
  let f' : B ⟶ B := 2 • 𝟙 B
  let π1 : A ⟶ C := HomologicalComplex.homologyMap S.g n
  let π2 : B ⟶ R2 := coeffReductionMap

  -- Step 1: homologyMap S.f n = 2 • 𝟙 (Hn X n)
  let g : S.X₂ ⟶ S.X₂ := S.f
  have hg : g = 𝟙 S.X₂ + 𝟙 S.X₂ := by
    simp [g, S, bocksteinShortComplex, multTwo, two_smul] <;> abel
  have h5 : HomologicalComplex.homologyMap g n = 2 • 𝟙 (Hn X n) := by
    rw [hg]
    have h7 := HomologicalComplex.homologyMap_add (𝟙 S.X₂) (𝟙 S.X₂)
    rw [h7, HomologicalComplex.homologyMap_id]
    show (𝟙 (Hn X n) + 𝟙 (Hn X n)) = (2 • 𝟙 (Hn X n))
    simp [two_smul] <;> abel
  have h6 : HomologicalComplex.homologyMap S.f n = HomologicalComplex.homologyMap g n := by rfl
  have h_f_eq : HomologicalComplex.homologyMap S.f n = f := by
    rw [h6]
    exact h5

  -- Step 2: f ≫ π1 = 0
  have h_zero1 : f ≫ π1 = 0 := by
    have h : (HomologicalComplex.homologyMap S.f n) ≫
        (HomologicalComplex.homologyMap S.g n) = 0 := by
      rw [← HomologicalComplex.homologyMap_comp, S.zero,
        HomologicalComplex.homologyMap_zero]
    rw [h_f_eq] at h
    exact h

  -- Step 3: The short complex A --f→ A --π1→ C is exact
  let S_hom2 : ShortComplex AddCommGrpCat := ShortComplex.mk
    (HomologicalComplex.homologyMap S.f n)
    (HomologicalComplex.homologyMap S.g n)
    (by rw [← HomologicalComplex.homologyMap_comp, S.zero,
      HomologicalComplex.homologyMap_zero])
  have h_exact2 : S_hom2.Exact := hS.homology_exact₂ n
  let S_hom2' : ShortComplex AddCommGrpCat := ShortComplex.mk f π1 h_zero1
  have h_exact2' : S_hom2'.Exact := by
    let e_iso : S_hom2 ≅ S_hom2' :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        h_f_eq.symm rfl
    exact ShortComplex.exact_of_iso e_iso h_exact2

  -- Step 4: C is cokernel of f
  have h_epi1 : Epi π1 := coeffChange_surjective n hn
  let h_cok1 : IsColimit (CokernelCofork.ofπ π1 h_zero1) := h_exact2'.gIsCokernel

  -- Step 5: R2 is cokernel of f'
  have h_zero2 : f' ≫ π2 = 0 := coeffShortComplex.zero
  let h_cok2 : IsColimit (CokernelCofork.ofπ π2 h_zero2) := coeffShortExact.gIsCokernel

  -- Step 6: Isomorphism e : A ≅ B commuting with f, f'
  let e : A ≅ B := sphereTopHomologyIso n (by linarith)
  have h_comm : f ≫ e.hom = e.hom ≫ f' := by
    simp [f, f']
  have h_comm2 : f' ≫ e.inv = e.inv ≫ f := by
    calc
      f' ≫ e.inv
        = (e.inv ≫ e.hom) ≫ f' ≫ e.inv := by simp [Iso.inv_hom_id_assoc] <;> rfl
      _ = e.inv ≫ (e.hom ≫ f') ≫ e.inv := by simp [Category.assoc]
      _ = e.inv ≫ (f ≫ e.hom) ≫ e.inv := by rw [←h_comm]
      _ = (e.inv ≫ f) ≫ (e.hom ≫ e.inv) := by simp [Category.assoc]
      _ = (e.inv ≫ f) ≫ 𝟙 A := by rw [e.hom_inv_id]
      _ = e.inv ≫ f := by simp

  -- Step 7: Construct k1 : C → R2
  let h1' : A ⟶ R2 := e.hom ≫ π2
  have hz1 : f ≫ h1' = 0 := by
    calc
      f ≫ h1'
        = f ≫ (e.hom ≫ π2) := by rfl
      _ = (f ≫ e.hom) ≫ π2 := by rw [Category.assoc]
      _ = (e.hom ≫ f') ≫ π2 := by rw [h_comm]
      _ = e.hom ≫ (f' ≫ π2) := by rw [Category.assoc]
      _ = e.hom ≫ 0 := by rw [h_zero2]
      _ = 0 := by simp
  let k1 : C ⟶ R2 := h_cok1.desc (CokernelCofork.ofπ h1' hz1)

  -- Step 8: Construct k2 : R2 → C
  let h2' : B ⟶ C := e.inv ≫ π1
  have hz2 : f' ≫ h2' = 0 := by
    calc
      f' ≫ h2'
        = f' ≫ (e.inv ≫ π1) := by rfl
      _ = (f' ≫ e.inv) ≫ π1 := by rw [Category.assoc]
      _ = (e.inv ≫ f) ≫ π1 := by rw [h_comm2]
      _ = e.inv ≫ (f ≫ π1) := by rw [Category.assoc]
      _ = e.inv ≫ 0 := by rw [h_zero1]
      _ = 0 := by simp
  let k2 : R2 ⟶ C := h_cok2.desc (CokernelCofork.ofπ h2' hz2)

  -- Step 9: Factorization properties
  have hk1 : π1 ≫ k1 = h1' := by
    exact h_cok1.fac (CokernelCofork.ofπ h1' hz1) WalkingParallelPair.one
  have hk2 : π2 ≫ k2 = h2' := by
    exact h_cok2.fac (CokernelCofork.ofπ h2' hz2) WalkingParallelPair.one

  -- Step 10: k1 ≫ k2 = 𝟙 C
  have h_id1 : k1 ≫ k2 = 𝟙 C := by
    haveI : Epi π1 := h_epi1
    have h : π1 ≫ (k1 ≫ k2) = π1 := by
      calc
        π1 ≫ (k1 ≫ k2)
          = (π1 ≫ k1) ≫ k2 := by rw [Category.assoc]
        _ = h1' ≫ k2 := by rw [hk1]
        _ = (e.hom ≫ π2) ≫ k2 := by rfl
        _ = e.hom ≫ (π2 ≫ k2) := by rw [Category.assoc]
        _ = e.hom ≫ h2' := by rw [hk2]
        _ = e.hom ≫ (e.inv ≫ π1) := by rfl
        _ = (e.hom ≫ e.inv) ≫ π1 := by rw [Category.assoc]
        _ = 𝟙 A ≫ π1 := by rw [e.hom_inv_id]
        _ = π1 := by simp
    have h' : π1 ≫ (k1 ≫ k2) = π1 ≫ 𝟙 C := by
      rw [h] <;> simp
    exact Epi.left_cancellation (f := π1) (g := k1 ≫ k2) (h := 𝟙 C) h'

  -- Step 11: k2 ≫ k1 = 𝟙 R2
  have h_id2 : k2 ≫ k1 = 𝟙 R2 := by
    haveI : Epi π2 := coeffShortExact.epi_g
    have h : π2 ≫ (k2 ≫ k1) = π2 := by
      calc
        π2 ≫ (k2 ≫ k1)
          = (π2 ≫ k2) ≫ k1 := by rw [Category.assoc]
        _ = h2' ≫ k1 := by rw [hk2]
        _ = (e.inv ≫ π1) ≫ k1 := by rfl
        _ = e.inv ≫ (π1 ≫ k1) := by rw [Category.assoc]
        _ = e.inv ≫ h1' := by rw [hk1]
        _ = e.inv ≫ (e.hom ≫ π2) := by rfl
        _ = (e.inv ≫ e.hom) ≫ π2 := by rw [Category.assoc]
        _ = 𝟙 B ≫ π2 := by rw [e.inv_hom_id]
        _ = π2 := by simp
    have h' : π2 ≫ (k2 ≫ k1) = π2 ≫ 𝟙 R2 := by
      rw [h] <;> simp
    exact Epi.left_cancellation (f := π2) (g := k2 ≫ k1) (h := 𝟙 R2) h'

  exact Iso.mk k1 k2 h_id1 h_id2

/-- Coefficient change is natural. -/
lemma coeffChange_natural {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map f ≫
      coeffChangeHomology Y n =
    coeffChangeHomology X n ≫
      ((singularHomologyFunctor AddCommGrpCat n).obj R2).map f :=
  ((singularHomologyFunctor AddCommGrpCat n).map coeffReductionMap).naturality f

/-- The induced map on integer homology is multiplication by degree. -/
lemma homologyMap_degree_smul (f : C(Sphere n, Sphere n)) (hn : 0 < n) :
    ∀ (x : Hn (TopSphere n) n),
      (homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x = (degree f hn) • x := by
  let e := sphereTopHomologyIso n hn
  let g : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ := e.inv ≫ homologyMap f ≫ e.hom
  have h1 : ∀ (k : ℤ), (g : ℤ → ℤ) k = k * (degree f hn) := by
    intro k; exact int_hom_mul g k
  intro x
  let e_hom : Hn (TopSphere n) n → AddCommGrpCat.of ℤ := e.hom
  let e_inv : AddCommGrpCat.of ℤ → Hn (TopSphere n) n := e.inv
  have h_e_hom_inv : ∀ (y : Hn (TopSphere n) n), e_inv (e_hom y) = y := by
    intro y
    have h : (e.hom ≫ e.inv : Hn (TopSphere n) n → Hn (TopSphere n) n) y = y := by
      rw [e.hom_inv_id] <;> simp
    exact h
  have h2 : e_hom ((homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x) = (degree f hn) * e_hom x := by
    have h3 : e_hom ((homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x) =
        (g : ℤ → ℤ) (e_hom x) := by
      dsimp only [g]
      have h4 : e_hom ((homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x) =
          e_hom ((homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) (e_inv (e_hom x))) := by
        rw [h_e_hom_inv x]
      rw [h4] <;> rfl
    rw [h3, h1] <;> ring
  have h5 : e_hom ((degree f hn) • x) = (degree f hn) * e_hom x := by
    let e_hom' : Hn (TopSphere n) n →+ AddCommGrpCat.of ℤ := (e.hom).hom
    have h51 : e_hom' ((degree f hn) • x) = (degree f hn) • e_hom' x :=
      e_hom'.map_zsmul (degree f hn) x
    have h52 : (degree f hn) • e_hom x = (degree f hn) * e_hom x := by
      exact Int.zsmul_eq_mul (degree f hn) (e_hom x)
    exact h52 ▸ h51
  have h4 : e_hom ((homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x) = e_hom ((degree f hn) • x) := by
    rw [h2, h5]
  have h_inj : Function.Injective e_hom := by
    have h_mono : Mono e.hom := by infer_instance
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback e.hom).mp h_mono
  exact h_inj h4

/-- Helper: in H_n(S^n; Z/2), every element has order 2. -/
lemma z2_homology_two_smul (n : ℕ) (hn : 1 ≤ n)
    (e_z2 : HnZ2 (TopSphere n) n ≅ R2) :
    ∀ (y : HnZ2 (TopSphere n) n), (2 : ℤ) • y = 0 := by
  intro y
  have h7 : e_z2.hom ((2 : ℤ) • y) = (2 : ℤ) • e_z2.hom y :=
    (e_z2.hom).hom.map_zsmul 2 y
  have h8 : (2 : ℤ) • e_z2.hom y = 0 := by
    have h9 : ∀ (z : R2), (2 : ℤ) • z = 0 := by
      intro z
      exact CharTwo.two_zsmul z
    exact h9 (e_z2.hom y)
  have h10 : e_z2.hom ((2 : ℤ) • y) = e_z2.hom 0 := by
    rw [h7, h8]
    <;> simp
  have h11 : Function.Injective (e_z2.hom : HnZ2 (TopSphere n) n → R2) := by
    have h_mono : Mono e_z2.hom := by infer_instance
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback e_z2.hom).mp h_mono
  exact h11 h10

/-- If degree is odd, the induced map on Z/2 homology is the identity. -/
lemma z2_homologyMap_of_odd_degree (f : C(Sphere n, Sphere n)) (hn : 0 < n)
    (h_surj : Epi (coeffChangeHomology (TopSphere n) n))
    (e_z2 : HnZ2 (TopSphere n) n ≅ R2)
    (h_odd : Odd (degree f hn)) :
    ((singularHomologyFunctor AddCommGrpCat n).obj R2).map (TopCat.ofHom f) = 𝟙 _ := by
  let c := coeffChangeHomology (TopSphere n) n
  let c' : Hn (TopSphere n) n → HnZ2 (TopSphere n) n := (c : Hn (TopSphere n) n → HnZ2 (TopSphere n) n)
  haveI : Epi c := h_surj
  have h_surj' : Function.Surjective c' := AddCommGrpCat.epi_iff_surjective c |>.mp h_surj
  have h_nat : (homologyMap f) ≫ c = c ≫
      ((singularHomologyFunctor AddCommGrpCat n).obj R2).map (TopCat.ofHom f) :=
    coeffChange_natural (TopCat.ofHom f) n
  have h3 : ∀ (x : Hn (TopSphere n) n),
      (homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x = (degree f hn) • x :=
    homologyMap_degree_smul f hn
  have h4 : ∀ (y : HnZ2 (TopSphere n) n),
      ((singularHomologyFunctor AddCommGrpCat n).obj R2).map (TopCat.ofHom f) y =
      (degree f hn) • y := by
    intro y
    rcases h_surj' y with ⟨x, rfl⟩
    have h5 : c' ((homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x) =
        ((singularHomologyFunctor AddCommGrpCat n).obj R2).map (TopCat.ofHom f) (c' x) := by
      calc
        c' ((homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x)
          = (((homologyMap f) ≫ c) : Hn (TopSphere n) n → HnZ2 (TopSphere n) n) x := by rfl
        _ = ((c ≫ ((singularHomologyFunctor AddCommGrpCat n).obj R2).map (TopCat.ofHom f)) : Hn (TopSphere n) n → HnZ2 (TopSphere n) n) x := by rw [h_nat]
        _ = ((singularHomologyFunctor AddCommGrpCat n).obj R2).map (TopCat.ofHom f) (c' x) := by rfl
    have h6 : c' ((homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x) =
        (degree f hn) • c' x := by
      rw [h3 x]
      exact (c).hom.map_zsmul (degree f hn) x
    rw [h5] at *
    exact h6
  have h_two := z2_homology_two_smul n (by linarith) e_z2
  have h5 : ∀ (y : HnZ2 (TopSphere n) n), (degree f hn) • y = y := by
    intro y
    rcases h_odd with ⟨k, hk⟩
    rw [hk]
    have h7 : ((2 * k + 1 : ℤ) • y) = y := by
      calc
        ((2 * k + 1 : ℤ) • y)
          = (2 * k : ℤ) • y + (1 : ℤ) • y := by rw [add_smul]
        _ = (2 : ℤ) • (k • y) + y := by rw [mul_smul, one_smul] <;> rfl
        _ = 0 + y := by rw [h_two (k • y)]
        _ = y := by simp
    exact h7
  ext y
  rw [h4 y, h5 y] <;> simp

/-- If f induces identity on Z/2 homology, degree is odd. -/
theorem degree_odd_of_z2_id (f : C(Sphere n, Sphere n)) (hn : 0 < n)
    (h_z2_id : ((singularHomologyFunctor AddCommGrpCat n).obj R2).map (TopCat.ofHom f) = 𝟙 _)
    (h_surj : Epi (coeffChangeHomology (TopSphere n) n))
    (e_z2 : HnZ2 (TopSphere n) n ≅ R2) :
    Odd (degree f hn) := by
  let k := degree f hn
  let c : Hn (TopSphere n) n ⟶ HnZ2 (TopSphere n) n := coeffChangeHomology (TopSphere n) n
  let c' : Hn (TopSphere n) n → HnZ2 (TopSphere n) n := (c : Hn (TopSphere n) n → HnZ2 (TopSphere n) n)
  haveI : Epi c := h_surj
  have h_surj' : Function.Surjective c' := AddCommGrpCat.epi_iff_surjective c |>.mp h_surj
  have h_nat : (homologyMap f) ≫ c = c ≫
      ((singularHomologyFunctor AddCommGrpCat n).obj R2).map (TopCat.ofHom f) :=
    coeffChange_natural (TopCat.ofHom f) n
  rw [h_z2_id] at h_nat
  have h_eq : (homologyMap f) ≫ c = c := by
    rw [h_nat] <;> simp
  have h3 : ∀ (x : Hn (TopSphere n) n),
      (homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x = k • x :=
    homologyMap_degree_smul f hn
  have h4 : ∀ (x : Hn (TopSphere n) n), k • c' x = c' x := by
    intro x
    have h5 : (((homologyMap f) ≫ c) : Hn (TopSphere n) n → HnZ2 (TopSphere n) n) x = c' x := by
      rw [h_eq] <;> rfl
    have h5' : c' ((homologyMap f : Hn (TopSphere n) n → Hn (TopSphere n) n) x) = c' x := h5
    rw [h3 x] at h5'
    have h7 : c' (k • x) = k • c' x := (c).hom.map_zsmul k x
    rw [h7] at h5'
    exact h5'
  have h5 : ∀ (y : HnZ2 (TopSphere n) n), k • y = y := by
    intro y
    rcases h_surj' y with ⟨x, rfl⟩
    exact h4 x
  have h6 : ∀ (y : HnZ2 (TopSphere n) n), (k - 1 : ℤ) • y = 0 := by
    intro y
    have h7 : k • y = y := h5 y
    have h8 : (k - 1 : ℤ) • y = k • y - y := by
      rw [sub_smul, one_smul]
    rw [h8, h7, sub_self]
  have h9 : (k - 1 : ℤ) • (e_z2.inv (1 : ZMod 2)) = 0 := h6 (e_z2.inv 1)
  have h10 : e_z2.hom ((k - 1 : ℤ) • (e_z2.inv (1 : ZMod 2))) =
      (k - 1 : ℤ) • (e_z2.hom (e_z2.inv (1 : ZMod 2))) :=
    (e_z2.hom).hom.map_zsmul (k - 1) (e_z2.inv 1)
  have h11 : e_z2.hom (e_z2.inv (1 : ZMod 2)) = (1 : ZMod 2) := by
    have h12 : ∀ (z : R2), e_z2.hom (e_z2.inv z) = z := by
      intro z
      have h : e_z2.inv ≫ e_z2.hom = 𝟙 R2 := e_z2.inv_hom_id
      exact congr_arg (fun (f : R2 → R2) => f z) (congr_arg (fun (g : R2 ⟶ R2) => (g : R2 → R2)) h)
    exact h12 (1 : ZMod 2)
  have h13 : e_z2.hom ((k - 1 : ℤ) • (e_z2.inv (1 : ZMod 2))) = 0 := by
    rw [h9]
    exact (e_z2.hom).hom.map_zero
  have h14 : (k - 1 : ℤ) • (1 : ZMod 2) = 0 := by
    calc
      (k - 1 : ℤ) • (1 : ZMod 2)
        = (k - 1 : ℤ) • (e_z2.hom (e_z2.inv (1 : ZMod 2))) := by rw [h11]
      _ = e_z2.hom ((k - 1 : ℤ) • (e_z2.inv (1 : ZMod 2))) := by rw [h10]
      _ = 0 := h13
  have h15 : ((k - 1 : ZMod 2)) = 0 := by
    simpa [smul_eq_mul] using h14
  have h16 : (k : ZMod 2) = 1 := by
    simpa [sub_eq_zero] using h15
  have h17 : k % 2 = 1 := by
    by_cases h : k % 2 = 0
    · have h19 : (k : ZMod 2) = 0 := by
        have h21 : (2 : ℤ) ∣ k := by omega
        rcases h21 with ⟨m, hm⟩
        rw [hm]
        have h24 : (2 : ZMod 2) = 0 := by decide
        simp [h24] <;> ring
      rw [h19] at h16
      norm_num at h16
    · omega
  exact ⟨k / 2, by omega⟩

end
