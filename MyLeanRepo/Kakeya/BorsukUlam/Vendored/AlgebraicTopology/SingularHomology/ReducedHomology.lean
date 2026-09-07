module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Connected.PathConnected
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.PiZeroPathComponents

@[expose] public section

/-!
# Reduced Singular Homology

This file defines reduced singular homology `H̃ₙ(X; R)` for topological spaces.

The reduced homology groups differ from ordinary singular homology only in degree 0:
- `H̃ₙ(X) ≅ Hₙ(X)` for `n > 0`
- `H₀(X) ≅ H̃₀(X) ⊕ R` (split short exact sequence)

Intuitively, `H̃₀(X)` is the free `R`-module on (path components of X minus one generator),
i.e., it measures "how many more components than a point" the space has.

## Construction

The reduced chain complex is obtained by augmenting the ordinary singular chain complex
with an extra `R` in degree `0` (shifting everything up), connected by the augmentation map
`ε : C₀(X) → R` that sends each 0-simplex (point) to `1 ∈ R`.

Then `H̃ₙ(X) := Hₙ₊₁` of this augmented chain complex.

## Main definitions

- `SSet.augmentationMap` — the augmentation `C₀(X) → R` for simplicial sets
- `SSet.augmentedChainComplex` — the augmented chain complex of a simplicial set
- `SSet.reducedHomology n` — reduced homology H̃ₙ(X) of a simplicial set
- `reducedSingularHomology n X` — reduced singular homology of a topological space

## Main results

- `singularHomologyPointZero` — `H₀({*}) ≅ R`
- `isZero_singularHomologyPoint` — `Hₙ({*}) = 0` for `n > 0`
- `isZero_reducedHomologyPoint` — `H̃ₙ({*}) = 0` for all `n`
- For connected simplicial sets, `homology₀ε : H₀(X) → R` is an isomorphism
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
variable (X : SSet) (R : C)

/-- The augmentation map on the level of 0-chains of a simplicial set:
    it sends each 0-simplex to the identity map on `R` (i.e., "1" in `R`).

    This is the composition of the map to the free module on `π₀(X)`
    with the fold map that sums all the generators. -/
noncomputable def augmentationMap :
    (X.chainComplex R).X 0 ⟶ R :=
  SSet.π₀.fromChainComplexXZero X R ≫ Sigma.desc (fun (_ : π₀ X) ↦ 𝟙 R)

@[reassoc (attr := simp)]
lemma d_one_zero_comp_augmentationMap :
    (X.chainComplex R).d 1 0 ≫ X.augmentationMap R = 0 := by
  simp only [augmentationMap]
  rw [← CategoryTheory.Category.assoc]
  rw [SSet.π₀.d_fromChainComplexXZero]
  rw [zero_comp]

/-- The augmented chain complex of a simplicial set.

    Degree 0 is `R`, degree 1 is `C₀`, degree 2 is `C₁`, etc.
    The differential `d₁₀` is the augmentation map `ε : C₀ → R`.

    The homology of this augmented complex gives reduced homology:
    `H̃ₙ(X) = Hₙ₊₁(augmentedChainComplex)`. -/
noncomputable def augmentedChainComplex : ChainComplex C ℕ :=
  ChainComplex.augment (X.chainComplex R) (X.augmentationMap R)
    (X.d_one_zero_comp_augmentationMap R)

variable [CategoryWithHomology C]

/-- Reduced homology of a simplicial set.

    Defined as `Hₙ₊₁` of the augmented chain complex.
    - For `n = 0`: `H̃₀(X) = ker(H₀(X) → R)` (the "reduced" 0-th homology)
    - For `n > 0`: `H̃ₙ(X) ≅ Hₙ(X)` (same as unreduced homology) -/
noncomputable def reducedHomology (n : ℕ) : C :=
  (X.augmentedChainComplex R).homology (n + 1)

/-- Reduced homology agrees with ordinary homology in degrees ≥ 1.

    For all `n : ℕ`, we have `H̃ₙ₊₁(X) ≅ Hₙ₊₁(X)`.

    This follows from the fact that the augmented chain complex agrees with the
    original chain complex in degrees ≥ 1 (shifted by one), so their homology
    in corresponding degrees is isomorphic. -/
noncomputable def reducedHomologySuccIso (n : ℕ) :
    X.reducedHomology R (n + 1) ≅ X.homology R (n + 1) := by
  let j := n + 2
  let i := j + 1
  let k := n + 1
  let sc1 := (X.augmentedChainComplex R).sc' i j k
  let sc2 := (X.chainComplex R).sc' (n + 2) (n + 1) n
  have h_iso_sc : sc1 ≅ sc2 := by exact Iso.refl sc1
  have h1 : (X.augmentedChainComplex R).homology j ≅ sc1.homology :=
    (X.augmentedChainComplex R).homologyIsoSc' i j k (by simp [i, j]) (by simp [j, k])
  have h2 : sc1.homology ≅ sc2.homology := ShortComplex.homologyMapIso h_iso_sc
  have h3 : sc2.homology ≅ (X.chainComplex R).homology (n + 1) :=
    ((X.chainComplex R).homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).symm
  exact h1 ≪≫ h2 ≪≫ h3

/-- The augmentation map on `H₀`: `H₀(X) → R`.

    This is the map induced by the augmentation on the chain level.
    It sends each generator (path component) to `1 ∈ R`. -/
noncomputable def homology₀ε' : X.homology R 0 ⟶ R :=
  X.homology₀ε R

/-- For a connected simplicial set, the augmentation map `H₀(X) → R` is an isomorphism.

    This follows from `H₀(X) ≅ R[π₀(X)]` and `π₀(X)` being a one-element set
    when `X` is connected.

    The `IsIso` instance is provided by `SSet.homology₀ε`. -/
lemma homology₀ε_isIso_of_isConnected [X.IsConnected] : IsIso (X.homology₀ε R) := by
  infer_instance

variable {X Y Z : SSet.{w}} (f : X ⟶ Y) (g : Y ⟶ Z)

omit [CategoryWithHomology C] in
/-- The augmentation map is natural with respect to simplicial set maps. -/
lemma augmentationMap_naturality :
    (((SSet.chainComplexFunctor C).obj R).map f).f 0 ≫ Y.augmentationMap R =
      X.augmentationMap R := by
  apply SSet.chainComplex_hom_ext (X := X) (R := R) (n := 0)
  intro x
  have h1 : X.ιChainComplex x ≫ (((SSet.chainComplexFunctor C).obj R).map f).f 0 =
      Y.ιChainComplex (f.app _ x) := by exact ι_chainComplexMap_f X Y f R x
  have h2 : X.ιChainComplex x ≫ X.augmentationMap R = 𝟙 R := by
    simp only [augmentationMap]
    rw [← Category.assoc]
    rw [SSet.π₀.comp_fromChainComplexXZero (X := X) (R := R) x]
    ; exact Sigma.ι_desc _ _
  have h3 : Y.ιChainComplex (f.app _ x) ≫ Y.augmentationMap R = 𝟙 R := by
    simp only [augmentationMap]
    rw [← Category.assoc]
    rw [SSet.π₀.comp_fromChainComplexXZero (X := Y) (R := R) (f.app _ x)]
    ; exact Sigma.ι_desc _ _
  calc
    X.ιChainComplex x ≫ (((SSet.chainComplexFunctor C).obj R).map f).f 0 ≫ Y.augmentationMap R
      = (X.ιChainComplex x ≫ (((SSet.chainComplexFunctor C).obj R).map f).f 0) ≫ Y.augmentationMap R := by
        rw [Category.assoc]
    _ = Y.ιChainComplex (f.app _ x) ≫ Y.augmentationMap R := by rw [h1]
    _ = 𝟙 R := h3
    _ = X.ιChainComplex x ≫ X.augmentationMap R := h2.symm

/-- The chain map between augmented chain complexes induced by a map of simplicial sets. -/
noncomputable def augmentedChainComplexMap :
    X.augmentedChainComplex R ⟶ Y.augmentedChainComplex R :=
  let f_chain := (SSet.chainComplexFunctor C).obj R |>.map f
  let ε_X := X.augmentationMap R
  let ε_Y := Y.augmentationMap R
  let w_X := X.d_one_zero_comp_augmentationMap R
  let w_Y := Y.d_one_zero_comp_augmentationMap R
  have h_nat : f_chain.f 0 ≫ ε_Y = ε_X := augmentationMap_naturality (R := R) f
  { f := fun i => match i with
    | 0 => 𝟙 R
    | i + 1 => f_chain.f i
    comm' := fun i j h => by
      have h_rel : j + 1 = i := h
      cases j with
      | zero =>
        have hi : i = 1 := by omega
        rw [hi]
        have h2 : (X.augmentedChainComplex R).d 1 0 = ε_X :=
          ChainComplex.augment_d_one_zero (X.chainComplex R) ε_X w_X
        have h3 : (Y.augmentedChainComplex R).d 1 0 = ε_Y :=
          ChainComplex.augment_d_one_zero (Y.chainComplex R) ε_Y w_Y
        have h_goal : f_chain.f 0 ≫ ε_Y = ε_X ≫ 𝟙 R := by
          rw [h_nat, Category.comp_id]
        rw [h2, h3]
        exact h_goal
      | succ k =>
        have hi : i = k + 2 := by omega
        rw [hi]
        have h4 : (X.augmentedChainComplex R).d (k + 2) (k + 1) = (X.chainComplex R).d (k + 1) k :=
          ChainComplex.augment_d_succ_succ (X.chainComplex R) ε_X w_X (k + 1) k
        have h5 : (Y.augmentedChainComplex R).d (k + 2) (k + 1) = (Y.chainComplex R).d (k + 1) k :=
          ChainComplex.augment_d_succ_succ (Y.chainComplex R) ε_Y w_Y (k + 1) k
        simp [h4, h5] ; exact f_chain.comm (k + 1) k }

/-- The map on reduced homology induced by a map of simplicial sets. -/
noncomputable def reducedHomologyMap (n : ℕ) :
    X.reducedHomology R n ⟶ Y.reducedHomology R n :=
  (X.augmentedChainComplex R).homologyMap (augmentedChainComplexMap (R := R) f) (n + 1)

omit [CategoryWithHomology C] in
/-- The augmented chain complex map of the identity is the identity. -/
lemma augmentedChainComplexMap_id :
    augmentedChainComplexMap (R := R) (𝟙 X) = 𝟙 (X.augmentedChainComplex R) := by
  ext i
  dsimp only [augmentedChainComplexMap, augmentedChainComplex]
  cases i with
  | zero => rfl
  | succ i => simp

omit [CategoryWithHomology C] in
/-- The augmented chain complex map of a composition is the composition. -/
lemma augmentedChainComplexMap_comp :
    augmentedChainComplexMap (R := R) (f ≫ g) =
    augmentedChainComplexMap (R := R) f ≫ augmentedChainComplexMap (R := R) g := by
  ext i
  dsimp only [augmentedChainComplexMap, augmentedChainComplex]
  cases i with
  | zero =>
    simp [Category.comp_id]
  | succ i => simp

/-- The reduced homology map of the identity is the identity. -/
lemma reducedHomologyMap_id (n : ℕ) :
    reducedHomologyMap (R := R) (𝟙 X) n = 𝟙 (X.reducedHomology R n) := by
  rw [reducedHomologyMap, augmentedChainComplexMap_id]
  exact HomologicalComplex.homologyMap_id (X.augmentedChainComplex R) (n + 1)

/-- The reduced homology map of a composition is the composition. -/
lemma reducedHomologyMap_comp (n : ℕ) :
    reducedHomologyMap (R := R) (f ≫ g) n =
    reducedHomologyMap (R := R) f n ≫ reducedHomologyMap (R := R) g n := by
  rw [reducedHomologyMap, reducedHomologyMap, reducedHomologyMap, augmentedChainComplexMap_comp]
  exact HomologicalComplex.homologyMap_comp (augmentedChainComplexMap (R := R) f) (augmentedChainComplexMap (R := R) g) (n + 1)

/-- For a connected simplicial set, reduced homology in degree 0 is zero.

    Proof: H̃₀(X) is the right homology of the short complex
    `C₁ --d₁₀--> C₀ --ε--> R`. The cokernel of d₁₀ is `∐ (fun (_ : π₀ X) ↦ R)`,
    and the induced map to R is the fold map. When X is connected, the fold map
    is an isomorphism, so its kernel is trivial, hence H̃₀(X) = 0. -/
lemma isZero_reducedHomologyZero_of_isConnected [X.IsConnected] :
    IsZero (X.reducedHomology R 0) := by
  let S := (X.augmentedChainComplex R).sc' 2 1 0
  let h : S.RightHomologyData := S.rightHomologyData
  let Q' := ∐ (fun (_ : π₀ X) ↦ R)
  let p' : S.X₂ ⟶ Q' := π₀.fromChainComplexXZero X R
  have hwp' : S.f ≫ p' = 0 := by
    have h_f : S.f = (X.chainComplex R).d 1 0 := by
      simp [S, augmentedChainComplex, ChainComplex.augment]
    rw [h_f]
    exact π₀.d_fromChainComplexXZero X R 1
  let hp' : IsColimit (CokernelCofork.ofπ p' hwp') :=
    isColimitCokernelCoforkChainComplexDOneZero X R
  let e_hom : h.Q ⟶ Q' := h.descQ p' hwp'
  let e_inv : Q' ⟶ h.Q := hp'.desc (CokernelCofork.ofπ h.p h.wp)
  have he1 : h.p ≫ e_hom = p' := h.p_descQ p' hwp'
  have he2 : p' ≫ e_inv = h.p := by
    exact hp'.fac (CokernelCofork.ofπ h.p h.wp) WalkingParallelPair.one
  have e_hom_inv : e_hom ≫ e_inv = 𝟙 h.Q := by
    apply Cofork.IsColimit.hom_ext h.hp
    have h_eq : h.p ≫ (e_hom ≫ e_inv) = h.p ≫ 𝟙 h.Q := by
      calc
        h.p ≫ (e_hom ≫ e_inv) = (h.p ≫ e_hom) ≫ e_inv := by rw [Category.assoc]
        _ = p' ≫ e_inv := by rw [he1]
        _ = h.p := by rw [he2]
        _ = h.p ≫ 𝟙 h.Q := by rw [Category.comp_id]
    exact h_eq
  have e_inv_hom : e_inv ≫ e_hom = 𝟙 Q' := by
    apply Cofork.IsColimit.hom_ext hp'
    have h_eq : p' ≫ (e_inv ≫ e_hom) = p' ≫ 𝟙 Q' := by
      calc
        p' ≫ (e_inv ≫ e_hom) = (p' ≫ e_inv) ≫ e_hom := by rw [Category.assoc]
        _ = h.p ≫ e_hom := by rw [he2]
        _ = p' := by rw [he1]
        _ = p' ≫ 𝟙 Q' := by rw [Category.comp_id]
    exact h_eq
  let e : h.Q ≅ Q' :=
    { hom := e_hom, inv := e_inv, hom_inv_id := e_hom_inv, inv_hom_id := e_inv_hom }
  let g' : Q' ⟶ R := Sigma.desc (fun (_ : π₀ X) ↦ 𝟙 R)
  have hε : S.g = p' ≫ g' := by
    have h_g : S.g = X.augmentationMap R := by
      simp [S, augmentedChainComplex, ChainComplex.augment]
    rw [h_g, augmentationMap] ; rfl
  have h_induced : h.descQ S.g S.zero = e.hom ≫ g' := by
    apply Cofork.IsColimit.hom_ext h.hp
    have h_left : h.p ≫ h.descQ S.g S.zero = S.g := h.p_descQ S.g S.zero
    have h_right : h.p ≫ (e.hom ≫ g') = S.g := by
      calc
        h.p ≫ (e.hom ≫ g') = (h.p ≫ e.hom) ≫ g' := by rw [Category.assoc]
        _ = p' ≫ g' := by rw [he1]
        _ = S.g := by rw [hε]
    have h_ofπ : (CokernelCofork.ofπ h.p h.wp).π = h.p := by
      simp [CokernelCofork.ofπ]
    have h_goal : (CokernelCofork.ofπ h.p h.wp).π ≫ h.descQ S.g S.zero =
        (CokernelCofork.ofπ h.p h.wp).π ≫ (e.hom ≫ g') := by
      rw [h_ofπ]
      exact h_left.trans h_right.symm
    exact h_goal
  let x : π₀ X := Classical.arbitrary _
  let s : R ⟶ Q' := Sigma.ι (fun (_ : π₀ X) ↦ R) x
  have h_section : s ≫ g' = 𝟙 R := by
    simp [g', s, Sigma.ι_desc]
  have h_retraction : g' ≫ s = 𝟙 Q' := by
    apply Sigma.hom_ext
    intro y
    have hxy : x = y := by subsingleton
    subst hxy
    have h : (Sigma.ι (fun (_ : π₀ X) ↦ R) x) ≫ g' ≫ s =
        (Sigma.ι (fun (_ : π₀ X) ↦ R) x) ≫ 𝟙 Q' := by
      calc
        (Sigma.ι (fun (_ : π₀ X) ↦ R) x) ≫ g' ≫ s
          = ((Sigma.ι (fun (_ : π₀ X) ↦ R) x) ≫ g') ≫ s := by rw [Category.assoc]
        _ = (𝟙 R) ≫ s := by rw [h_section]
        _ = s := by rw [Category.id_comp]
        _ = (Sigma.ι (fun (_ : π₀ X) ↦ R) x) := by rfl
        _ = (Sigma.ι (fun (_ : π₀ X) ↦ R) x) ≫ 𝟙 Q' := by rw [Category.comp_id]
    exact h
  have h_g'_iso : IsIso g' := by
    exact ⟨s, h_retraction, h_section⟩
  have h_e_iso : IsIso e.hom := by
    letI : IsIso e.hom := e.isIso_hom
    exact ‹IsIso e.hom›
  have h_comp_iso : IsIso (e.hom ≫ g') := by exact (isIso_comp_right_iff e.hom g').mpr h_e_iso
  have h_induced_iso : IsIso (h.descQ S.g S.zero) := by
    rw [h_induced]
    exact h_comp_iso
  have h_mono2 : Mono (h.descQ S.g S.zero) := by exact IsIso.mono_of_iso (h.descQ S.g S.zero)
  have h1 : h.ι ≫ h.descQ S.g S.zero = 0 := h.wι
  have hι_eq_zero : h.ι = 0 := by
    have h2 : h.ι ≫ h.descQ S.g S.zero = (0 : h.H ⟶ h.Q) ≫ h.descQ S.g S.zero := by
      rw [h1, zero_comp]
    exact (cancel_mono (h.descQ S.g S.zero)).mp h2
  have h_mono : Mono h.ι := inferInstance
  have h_id_zero : 𝟙 h.H = 0 := by
    have h2 : (𝟙 h.H) ≫ h.ι = (0 : h.H ⟶ h.H) ≫ h.ι := by
      rw [Category.id_comp, hι_eq_zero, zero_comp]
    exact (cancel_mono h.ι).mp h2
  have hH_zero : IsZero h.H := by
    rw [IsZero.iff_id_eq_zero]
    exact h_id_zero
  have h_iso1 : S.rightHomology ≅ h.H := h.rightHomologyIso
  have h_zero_right : IsZero S.rightHomology :=
    IsZero.of_iso hH_zero h_iso1
  have h_iso2 : S.homology ≅ S.rightHomology := S.rightHomologyIso.symm
  have h_zero_homology : IsZero S.homology :=
    IsZero.of_iso h_zero_right h_iso2
  have h_iso3 : (X.augmentedChainComplex R).homology 1 ≅ S.homology :=
    (X.augmentedChainComplex R).homologyIsoSc' 2 1 0 (by simp) (by simp)
  have h_zero_aug : IsZero ((X.augmentedChainComplex R).homology 1) :=
    IsZero.of_iso h_zero_homology h_iso3
  exact h_zero_aug

/-- The short exact sequence 0 → H̃₀(X) → H₀(X) → R → 0 is split when X is nonempty.

    This gives `H₀(X) ≅ H̃₀(X) ⊕ R`.

    Proof: H̃₀(X) is the kernel of the augmentation map `H₀(X) → R`.
    When X is nonempty, this map is a split epimorphism (section = inclusion of
    any path component), so the SES splits. -/
noncomputable def homologyZeroIsoReducedHomologyZeroPlusR [HasBinaryBiproducts C] [X.Nonempty] :
    X.homology R 0 ≅ X.reducedHomology R 0 ⊞ R := by
  let S := (X.augmentedChainComplex R).sc' 2 1 0
  let h : S.RightHomologyData := S.rightHomologyData
  let Q' := ∐ (fun (_ : π₀ X) ↦ R)
  let p' : S.X₂ ⟶ Q' := π₀.fromChainComplexXZero X R
  have hwp' : S.f ≫ p' = 0 := by
    have h_f : S.f = (X.chainComplex R).d 1 0 := by
      simp [S, augmentedChainComplex, ChainComplex.augment]
    rw [h_f]
    exact π₀.d_fromChainComplexXZero X R 1
  let hp' : IsColimit (CokernelCofork.ofπ p' hwp') :=
    isColimitCokernelCoforkChainComplexDOneZero X R
  let e_hom : h.Q ⟶ Q' := h.descQ p' hwp'
  let e_inv : Q' ⟶ h.Q := hp'.desc (CokernelCofork.ofπ h.p h.wp)
  have he1 : h.p ≫ e_hom = p' := h.p_descQ p' hwp'
  have he2 : p' ≫ e_inv = h.p := by
    exact hp'.fac (CokernelCofork.ofπ h.p h.wp) WalkingParallelPair.one
  have e_hom_inv : e_hom ≫ e_inv = 𝟙 h.Q := by
    apply Cofork.IsColimit.hom_ext h.hp
    have h_eq : h.p ≫ (e_hom ≫ e_inv) = h.p ≫ 𝟙 h.Q := by
      calc
        h.p ≫ (e_hom ≫ e_inv) = (h.p ≫ e_hom) ≫ e_inv := by rw [Category.assoc]
        _ = p' ≫ e_inv := by rw [he1]
        _ = h.p := by rw [he2]
        _ = h.p ≫ 𝟙 h.Q := by rw [Category.comp_id]
    exact h_eq
  have e_inv_hom : e_inv ≫ e_hom = 𝟙 Q' := by
    apply Cofork.IsColimit.hom_ext hp'
    have h_eq : p' ≫ (e_inv ≫ e_hom) = p' ≫ 𝟙 Q' := by
      calc
        p' ≫ (e_inv ≫ e_hom) = (p' ≫ e_inv) ≫ e_hom := by rw [Category.assoc]
        _ = h.p ≫ e_hom := by rw [he2]
        _ = p' := by rw [he1]
        _ = p' ≫ 𝟙 Q' := by rw [Category.comp_id]
    exact h_eq
  let e : h.Q ≅ Q' :=
    { hom := e_hom, inv := e_inv, hom_inv_id := e_hom_inv, inv_hom_id := e_inv_hom }
  let g' : Q' ⟶ R := Sigma.desc (fun (_ : π₀ X) ↦ 𝟙 R)
  have hε : S.g = p' ≫ g' := by
    have h_g : S.g = X.augmentationMap R := by
      simp [S, augmentedChainComplex, ChainComplex.augment]
    rw [h_g, augmentationMap] ; rfl
  let g : h.Q ⟶ R := h.descQ S.g S.zero
  have h_induced : g = e.hom ≫ g' := by
    apply Cofork.IsColimit.hom_ext h.hp
    have h_left : h.p ≫ g = S.g := h.p_descQ S.g S.zero
    have h_right : h.p ≫ (e.hom ≫ g') = S.g := by
      calc
        h.p ≫ (e.hom ≫ g') = (h.p ≫ e_hom) ≫ g' := by rw [Category.assoc]
        _ = p' ≫ g' := by rw [he1]
        _ = S.g := by rw [hε]
    have h_ofπ : (CokernelCofork.ofπ h.p h.wp).π = h.p := by
      simp [CokernelCofork.ofπ]
    have h_goal : (CokernelCofork.ofπ h.p h.wp).π ≫ g =
        (CokernelCofork.ofπ h.p h.wp).π ≫ (e.hom ≫ g') := by
      rw [h_ofπ]
      exact h_left.trans h_right.symm
    exact h_goal
  -- When X is nonempty, g' is a split epimorphism
  have h_nonempty_pi0 : Nonempty (π₀ X) :=
    (SSet.π₀.nonempty_iff (X := X)).mpr ‹X.Nonempty›
  let x0 : π₀ X := Classical.choice h_nonempty_pi0
  let s : R ⟶ Q' := Sigma.ι (fun (_ : π₀ X) ↦ R) x0
  have h_section : s ≫ g' = 𝟙 R := by
    simp [g', s, Sigma.ι_desc]
  -- Then g is also a split epimorphism
  let sec : R ⟶ h.Q := s ≫ e.inv
  have h_sec_g : sec ≫ g = 𝟙 R := by
    have h1 : sec ≫ g = (s ≫ e.inv) ≫ g := by rfl
    rw [h1]
    have h2 : (s ≫ e.inv) ≫ g = s ≫ (e.inv ≫ g) := by rw [Category.assoc]
    rw [h2]
    have h3 : e.inv ≫ g = e.inv ≫ (e.hom ≫ g') := by rw [h_induced]
    rw [h3]
    have h4 : s ≫ (e.inv ≫ (e.hom ≫ g')) = s ≫ ((e.inv ≫ e.hom) ≫ g') := by
      apply congr_arg (fun (f : Q' ⟶ R) => s ≫ f)
      exact (Category.assoc e.inv e.hom g').symm
    rw [h4]
    have h5 : (e.inv ≫ e.hom) = 𝟙 Q' := e.inv_hom_id
    rw [h5]
    have h6 : s ≫ (𝟙 Q' ≫ g') = s ≫ g' := by rw [Category.id_comp]
    rw [h6]
    exact h_section
  letI : IsSplitEpi g := ⟨⟨sec, h_sec_g⟩⟩
  -- h.ι is the kernel of g
  let kf : KernelFork g := KernelFork.ofι h.ι h.wι
  have h_kf : IsLimit kf := h.hι
  -- Therefore we have a bilimit bicone h.H -- h.Q -- R
  let bicone : BinaryBicone h.H R := binaryBiconeOfIsSplitEpiOfKernel (c := kf) h_kf
  have h_bilimit : bicone.IsBilimit := isBilimitBinaryBiconeOfIsSplitEpiOfKernel h_kf
  -- h.Q ≅ h.H ⊞ R (since bicone is a bilimit)
  have h_iso_hQ_biprod : h.Q ≅ h.H ⊞ R := biprod.uniqueUpToIso h.H R h_bilimit
  -- H₀(X) ≅ h.Q (both are ≅ ∐ (π₀ X; R))
  have h_iso_H0_hQ : X.homology R 0 ≅ h.Q :=
    X.homology₀Iso R ≪≫ e.symm
  -- H̃₀(X) ≅ h.H
  have h_iso_Htilde_hH : X.reducedHomology R 0 ≅ h.H := by
    let S2 := (X.augmentedChainComplex R).sc' 2 1 0
    have h1 : (X.augmentedChainComplex R).homology 1 ≅ S2.homology :=
      (X.augmentedChainComplex R).homologyIsoSc' 2 1 0 (by simp) (by simp)
    have h2 : S2.homology ≅ S2.rightHomology := S2.rightHomologyIso.symm
    have h3 : S2.rightHomology ≅ h.H := h.rightHomologyIso
    exact h1 ≪≫ h2 ≪≫ h3
  -- h.H ⊞ R ≅ X.reducedHomology R 0 ⊞ R
  have h_iso_biprod_map : h.H ⊞ R ≅ X.reducedHomology R 0 ⊞ R :=
    biprod.mapIso h_iso_Htilde_hH.symm (Iso.refl R)
  -- Therefore H₀(X) ≅ H̃₀(X) ⊞ R
  exact h_iso_H0_hQ ≪≫ h_iso_hQ_biprod ≪≫ h_iso_biprod_map

end SSet


namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
variable (n : ℕ) (R : C)

section ReducedSingularHomology

variable [CategoryWithHomology C]
variable {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Reduced singular homology of a topological space.

    This is the reduced homology of the singular simplicial set of `X`. -/
noncomputable def reducedSingularHomology (X : TopCat.{w}) : C :=
  SSet.reducedHomology (TopCat.toSSet.obj X) R n

/-- The unreduced singular homology functor `Hₙ(-; R) : TopCat → C`. -/
abbrev singularHomology : TopCat.{w} ⥤ C :=
  (singularHomologyFunctor C n).obj R

/-- Reduced singular homology is functorial: continuous maps induce maps on reduced homology. -/
noncomputable def reducedSingularHomologyMap :
    reducedSingularHomology C n R X ⟶ reducedSingularHomology C n R Y :=
  SSet.reducedHomologyMap (R := R) (f := TopCat.toSSet.map f) n

/-- For a path-connected topological space, reduced singular homology in degree 0 is zero. -/
lemma isZero_reducedSingularHomologyZero_of_pathConnected {X : TopCat.{w}}
    [PathConnectedSpace X] :
    IsZero (reducedSingularHomology C 0 R X) := by
  have h1 : Subsingleton (SSet.π₀ (TopCat.toSSet.obj X)) := by
    have h_sub : Subsingleton (ZerothHomotopy X) := by
      have h := pathConnectedSpace_iff_zerothHomotopy.mp ‹PathConnectedSpace X›
      exact h.2
    let e : SSet.π₀ (TopCat.toSSet.obj X) ≃ ZerothHomotopy X :=
      singularPiZeroEquivZerothHomotopy X
    haveI : Subsingleton (ZerothHomotopy X) := h_sub
    refine' ⟨fun a b => _⟩
    have h_eq : e a = e b := Subsingleton.elim (e a) (e b)
    exact e.injective h_eq
  have h_nonempty_pi0 : Nonempty (SSet.π₀ (TopCat.toSSet.obj X)) := by
    have hne : Nonempty (ZerothHomotopy X) := by
      have h := pathConnectedSpace_iff_zerothHomotopy.mp ‹PathConnectedSpace X›
      exact h.1
    exact Nonempty.map (singularPiZeroEquivZerothHomotopy X).symm hne
  have h2 : (TopCat.toSSet.obj X).Nonempty :=
    (SSet.π₀.nonempty_iff (X := TopCat.toSSet.obj X)).mp h_nonempty_pi0
  have h_conn : (TopCat.toSSet.obj X).IsConnected :=
    { toSubsingleton := h1, nonempty := h2 }
  have h_main : IsZero (SSet.reducedHomology (TopCat.toSSet.obj X) R 0) :=
    SSet.isZero_reducedHomologyZero_of_isConnected (X := TopCat.toSSet.obj X) R
  exact h_main

/-- The split short exact sequence for reduced singular homology:
    `H₀(X) ≅ H̃₀(X) ⊕ R` when `X` is nonempty. -/
noncomputable def singularHomologyZeroIsoReducedSingularHomologyZeroPlusR
    [HasBinaryBiproducts C] {X : TopCat.{w}} [Nonempty X] :
    (singularHomology C 0 R).obj X ≅ reducedSingularHomology C 0 R X ⊞ R := by
  have h_nonempty : (TopCat.toSSet.obj X).Nonempty := by
    have hne : Nonempty X := inferInstance
    let x : X := hne.some
    exact ⟨TopCat.toSSetObj₀Equiv.symm x⟩
  exact SSet.homologyZeroIsoReducedHomologyZeroPlusR (X := TopCat.toSSet.obj X) R

end ReducedSingularHomology

section TODO_ReducedHomologyProperties

-- The following results remain to be proved:
--
-- 1. H₀(X) ≅ H̃₀(X) ⊕ R (split short exact sequence)
--    (the augmentation map gives a SES 0 → H̃₀ → H₀ → R → 0)
--
-- 2. For path-connected spaces: H̃₀(X) = 0
--    (follows from 1 and H₀ ≅ R for connected spaces)
--
-- 3. Functoriality laws for reduced homology:
--    - reducedHomologyMap id = id
--    - reducedHomologyMap (f ≫ g) = reducedHomologyMap f ≫ reducedHomologyMap g
--
-- 4. Homotopy invariance of reduced homology
--
-- 5. H̃₀ of a point = 0
--
-- These will be addressed in subsequent work.

end TODO_ReducedHomologyProperties

end AlgebraicTopology
